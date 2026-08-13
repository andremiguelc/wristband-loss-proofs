"""Figures for fourier_measured.md, drawn from the measured results.

Every number plotted is printed, so the prose can quote what was drawn rather than a value
computed separately. Run after the diagnostics, with the results directory as the first
argument:

   .venv/bin/python docs/posts/fourier/measured_figures.py <results-dir>
"""

import json
import math
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

RES = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
HERE = Path(__file__).resolve().parent

COLOR = {"exact": "#4a4a4a", "spectral": "#e08214", "paired": "#2a5d9f", "phase": "#7fb3e0",
         "proved": "#a83232", "pairwise": "#4a4a4a"}

plt.rcParams.update({
   "figure.dpi": 110, "savefig.dpi": 150, "savefig.bbox": "tight",
   "font.size": 10, "axes.titlesize": 11, "axes.labelsize": 10,
   "axes.grid": True, "grid.alpha": 0.3, "grid.linewidth": 0.6,
   "axes.spines.top": False, "axes.spines.right": False, "axes.axisbelow": True,
   "legend.frameon": False, "legend.fontsize": 9,
   "lines.linewidth": 2.0, "lines.markersize": 6,
   "figure.facecolor": "white", "axes.facecolor": "white",
})


def load(name):
   path = RES / f"{name}.json"
   return json.loads(path.read_text()) if path.exists() else None


########################################################################################################################
# 1. What the harmonic cut cannot see
########################################################################################################################

def FigureBlindness():
   data = load("blindness")
   if data is None:
      return
   names = list(data)
   short = ["uniform\non the sphere", "uniform on a\ngreat circle", "a two-lobed\nbelt",
            "four clusters\nat a square", "one antipodal\npair"]
   x = np.arange(len(names))
   w = 0.27

   fig, ax = plt.subplots(figsize=(9, 4.6))
   ax.bar(x - w, [data[n]["exact"] for n in names], w, label="exact kernel",
          color=COLOR["exact"])
   ax.bar(x, [data[n]["spectral"] for n in names], w, label="harmonic cut at $\\ell \\leq 1$",
          color=COLOR["spectral"])
   ax.bar(x + w, [data[n]["fourier"] for n in names], w,
          yerr=[data[n]["fourier_sd"] for n in names], capsize=3,
          label="random Fourier features", color=COLOR["paired"])

   # The whole argument is that the orange bars do not move. Draw the line they sit on.
   blind = names[1:]
   level = float(np.mean([data[n]["spectral"] for n in blind]))
   ax.plot([0.6, len(names) - 0.6], [level, level], color="#a83232", ls="--", lw=1.4, zorder=5)
   ax.annotate("the cut gives one number for all four of these,\n"
               "so it cannot tell them apart at all",
               xy=(2.6, level), xytext=(1.35, 0.395), color="#a83232", fontsize=9.5,
               arrowprops=dict(arrowstyle="->", color="#a83232", lw=1.2))

   ax.set_xticks(x)
   ax.set_xticklabels(short)
   ax.set_ylim(0., 0.46)
   ax.set_ylabel("repulsion energy")
   ax.set_title("Five arrangements of 1024 directions in 128 dimensions. Only the first is\n"
                "uniform, and a higher bar means further from uniform.")
   ax.legend(loc="upper left")
   fig.savefig(HERE / "measured_blindness.png")
   plt.close(fig)

   spread = lambda k: (max(data[n][k] for n in blind) - min(data[n][k] for n in blind))
   print("FIGURE 1 -- blindness")
   for n in names:
      print(f"   {n:<44} exact {data[n]['exact']:.6f}  cut {data[n]['spectral']:.6f}  "
            f"fourier {data[n]['fourier']:.6f}")
   print(f"   spread over the four non-uniform arrangements: exact {spread('exact'):.6f}, "
         f"cut {spread('spectral'):.6f} ({100 * spread('spectral') / spread('exact'):.1f}%), "
         f"fourier {spread('fourier'):.6f} ({100 * spread('fourier') / spread('exact'):.1f}%)")


########################################################################################################################
# 2. The feature budget, and how far the proved rule sits from the measured one
########################################################################################################################

def FigureBudget():
   data = load("variance")
   if data is None:
      return
   rows = data["rows"]
   feats = sorted({int(k.split("|")[1]) for k in rows})

   fig, axes = plt.subplots(1, 2, figsize=(12, 4.4))

   ax = axes[0]
   for variant in ("paired", "phase"):
      xs = [f for f in feats if f"{variant}|{f}" in rows]
      ys = [rows[f"{variant}|{f}"]["rel_sd"] for f in xs]
      ax.plot(xs, ys, "o-", color=COLOR[variant], label=f"measured, {variant}")
      rho = data[f"rho_{variant}"]
      ax.plot(xs, [math.sqrt(rho / f) for f in xs], "--", color=COLOR[variant], alpha=0.55,
              label=f"$\\sqrt{{\\rho/D}}$, {variant}")
   ax.set_xscale("log", base=2)
   ax.set_yscale("log")
   ax.set_xlabel("features $D$")
   ax.set_ylabel("relative spread of one estimate")
   ax.set_title("(a) the spread falls as $1/\\sqrt{D}$")
   ax.annotate("the paired feature sits above its own\n"
               "population law: that gap is the finite batch",
               xy=(384, math.sqrt(data["rho_paired"] / 384)), xytext=(40, 0.0043),
               fontsize=8.5, color="#4a4a4a",
               arrowprops=dict(arrowstyle="->", color="#4a4a4a", lw=1))
   ax.legend()

   ax = axes[1]
   eps = np.geomspace(0.02, 0.4, 60)
   top = max(feats)
   rho_meas = {v: rows[f"{v}|{top}"]["rho"] for v in ("paired", "phase")}
   for variant in ("paired", "phase"):
      ax.plot(eps, rho_meas[variant] / eps ** 2, color=COLOR[variant],
              label=f"measured, {variant}")
   delta = 0.05
   ax.plot(eps, data["d_rad"] * (0.085 / eps) ** 2, color=COLOR["proved"],
           label="proved, batch-measured")
   ax.plot(eps, data["d_sup"] * (0.085 / eps) ** 2, color=COLOR["proved"], ls="--",
           label="proved, worst case")
   ax.axvline(0.085, color="k", alpha=0.4, lw=1)
   ax.text(0.087, 1.4, "the accuracy in use, 8.5%", fontsize=8.5, alpha=0.8, rotation=90,
           va="bottom")
   ax.set_xscale("log")
   ax.set_yscale("log")
   ticks = [0.02, 0.05, 0.085, 0.1, 0.2, 0.4]
   ax.set_xticks(ticks)
   ax.set_xticklabels([f"{100 * t:g}%" for t in ticks])
   ax.minorticks_off()
   ax.set_ylim(0.3, 1e9)
   ax.set_xlabel("wanted relative accuracy")
   ax.set_ylabel("features $D$ the rule asks for")
   ax.set_title(f"(b) four answers to “how many features” ($\\delta$ = {delta})")
   ax.legend(loc="upper right")

   fig.suptitle("Sizing the feature budget, $d$ = 128, $c$ = 4/3", y=1.02)
   fig.savefig(HERE / "measured_budget.png")
   plt.close(fig)

   print("\nFIGURE 2 -- the feature budget")
   for variant in ("paired", "phase"):
      for f in feats:
         r = rows.get(f"{variant}|{f}")
         if r:
            print(f"   {variant:<7} D={f:>5}  relative spread {r['rel_sd']:.5f}  "
                  f"rho = D x var = {r['rho']:.5f}")
   print(f"   analytic rho: paired {data['rho_paired']:.5f}, phase {data['rho_phase']:.5f}")
   print(f"   proved D at eps=0.085, delta=0.05: batch-measured {data['d_rad']:,.0f}, "
         f"worst case {data['d_sup']:,.0f}")
   for variant in ("paired", "phase"):
      print(f"   measured D at eps=0.085: {variant} {rho_meas[variant] / 0.085 ** 2:,.0f}")


########################################################################################################################
# 3. Cost, and the wall that arrives before the cost does
########################################################################################################################

def FigureCost():
   data = load("timing")
   if data is None:
      return
   sizes = sorted({int(k.split("|")[1]) for k in data})
   paths = [("pairwise", "pairwise, exact"), ("spectral", "harmonic cut"),
            ("fourier paired", "fourier, paired"), ("fourier phase", "fourier, phase")]
   key = {"pairwise": COLOR["pairwise"], "spectral": COLOR["spectral"],
          "fourier paired": COLOR["paired"], "fourier phase": COLOR["phase"]}

   fig, axes = plt.subplots(1, 2, figsize=(12, 4.4))

   ax = axes[0]
   for name, label in paths:
      xs = [n for n in sizes if f"{name}|{n}" in data]
      if not xs:
         continue
      ys = [data[f"{name}|{n}"]["backward_ms"] for n in xs]
      ax.plot(xs, ys, "o-", color=key[name], label=label,
              linewidth=2.6 if name.startswith("fourier paired") else 1.7)
      if name == "pairwise" and max(xs) < max(sizes):
         # The quadratic law, continued past the point where the machine runs out of memory.
         beyond = [n for n in sizes if n > max(xs)]
         base_n, base_y = max(xs), data[f"pairwise|{max(xs)}"]["backward_ms"]
         ax.plot([base_n] + beyond, [base_y] + [base_y * (n / base_n) ** 2 for n in beyond],
                 ":", color=key[name], alpha=0.7, label="pairwise, $N^2$ continued")
   ax.set_xscale("log", base=2)
   ax.set_yscale("log")
   ax.set_xticks(sizes)
   ax.set_xticklabels([str(s) for s in sizes])
   ax.set_xlabel("batch size $N$")
   ax.set_ylabel("milliseconds, forward and backward")
   ax.set_title("(a) time per repulsion term, $d$ = 128, $D$ = 384")
   ax.legend()

   ax = axes[1]
   grid = np.array(sizes, dtype=float)
   pair_gib = 8. * 4. * grid ** 2 / 2. ** 30
   feat_gib = 8. * 4. * grid * 384. / 2. ** 30
   ax.plot(grid, pair_gib, "o-", color=key["pairwise"], label="pairwise, $\\propto N^2$")
   ax.plot(grid, feat_gib, "o-", color=key["fourier paired"], label="fourier, $\\propto N D$")
   ax.axhline(16., color="#a83232", lw=1.4)
   ax.text(grid[0], 20., "this laptop: 16 GiB of unified memory", color="#a83232", fontsize=9)
   n_wall = math.sqrt(16. * 2. ** 30 / 32.)                # where 8 x 4 x N^2 bytes reaches 16 GiB
   ax.axvline(n_wall, color="#a83232", ls="--", lw=1, alpha=0.7)
   ax.annotate(f"pairwise stops fitting\nnear N = {int(n_wall):,}", xy=(n_wall, 3.),
               xytext=(1000, 2.6), color="#a83232", fontsize=8.5,
               arrowprops=dict(arrowstyle="->", color="#a83232", lw=1))
   ax.set_xscale("log", base=2)
   ax.set_yscale("log")
   ax.set_xticks(sizes)
   ax.set_xticklabels([str(s) for s in sizes])
   ax.set_xlabel("batch size $N$")
   ax.set_ylabel("GiB held for the repulsion term")
   ax.set_title("(b) the wall that arrives first")
   ax.legend(loc="lower right")

   fig.savefig(HERE / "measured_cost.png")
   plt.close(fig)

   print("\nFIGURE 3 -- cost")
   for n in sizes:
      cells = [f"{name}={data[f'{name}|{n}']['forward_ms']:.2f}/"
               f"{data[f'{name}|{n}']['backward_ms']:.2f}"
               for name, _ in paths if f"{name}|{n}" in data]
      print(f"   N={n:>6}  " + "  ".join(cells)
            + f"   pairwise memory {8. * 4. * n * n / 2. ** 30:.1f} GiB")


########################################################################################################################
# 4. Training: where each path landed, and how long it took to get there
########################################################################################################################

def FigureTraining(suffix="", out="measured_training.png", mark_epoch=None, scale="floor"):
   """Quality against wall-clock, one panel per latent width.

   ``scale`` picks what divides the angular score. ``floor`` is one draw of the score of a
   genuine Gaussian batch; it is kept only for the 12-epoch figure that was published with it.
   The true value of that statistic is zero, so the draw lands either side of zero and cannot
   divide anything -- ``band`` uses the 95th percentile of the null band instead, which is
   positive, fixed by its own seed, and the same in every run.
   """
   pairs = [(f"training_d8{suffix}", "latent width 8", "input 15"),
            (f"training_d32{suffix}", "latent width 32", "input 128")]
   loaded = [(load(name), label, sub) for name, label, sub in pairs]
   loaded = [row for row in loaded if row[0] is not None]
   if not loaded:
      return
   key = {"pairwise": COLOR["pairwise"], "spectral": COLOR["spectral"],
          "fourier paired": COLOR["paired"], "fourier phase": COLOR["phase"]}
   # The random phase variant tracks the paired one closely enough here that drawing it only
   # thickens the plot. It is still measured, and it is still in the table of section 6.
   shown = {"pairwise": "pairwise", "spectral": "spectral", "fourier paired": "fourier"}
   wide = {"fourier paired": 2.7}

   # Raw energy distances at two latent widths are not comparable numbers, so both panels are
   # divided by a per-width reference and share one axis.
   band = load("null_band")
   panels = []
   for data, label, sub in loaded:
      rows = data["results"]["shared calibration"]
      width = "8" if "width 8" in label else "32"
      floor = data["floor"][0] if scale == "floor" else band[width]["q95"]
      curves = {}
      for path in data["paths"]:
         runs = rows[path]["runs"]
         secs = np.median([[h["seconds"] for h in r["history"]] for r in runs], axis=0)
         ang = np.array([[h["angular"] for h in r["history"]] for r in runs]) / floor
         curves[path] = dict(secs=secs, med=np.median(ang, axis=0), lo=ang.min(axis=0),
                             hi=ang.max(axis=0), best=ang.min(axis=1))
      panels.append((data, label, sub, rows, floor, curves))

   # Bounded by what is drawn: the bands when they are shown, the medians when they are not.
   edge = ("lo", "hi") if scale == "floor" else ("med", "med")
   lo = min(min(p[5][k][edge[0]].min() for k in shown) for p in panels)
   hi = max(max(p[5][k][edge[1]].max() for k in shown) for p in panels)

   fig, axes = plt.subplots(1, len(panels), figsize=(6.3 * len(panels), 5.3),
                            squeeze=False, sharex=True, sharey=True)
   print("\nFIGURE 4 -- training")
   for ax, (data, label, sub, rows, floor, curves) in zip(axes[0], panels):
      for path in shown:
         c = curves[path]
         if scale == "floor":
            ax.fill_between(c["secs"], c["lo"], c["hi"], color=key[path], alpha=0.15, lw=0)
         ax.plot(c["secs"], c["med"], color=key[path], marker="o", ms=4.6,
                 markeredgecolor="white", markeredgewidth=0.7, lw=wide.get(path, 2.), zorder=3)
         if mark_epoch is not None and mark_epoch <= len(c["med"]):
            # Where the earlier, shorter run stopped. It stopped inside the reorganisation.
            ax.plot(c["secs"][mark_epoch - 1], c["med"][mark_epoch - 1], "s", mfc="white",
                    mec=key[path], ms=9, mew=1.8, zorder=5)
         elif scale == "floor":
            # A ring on the best point, for the run that overshoots and comes back.
            j = int(np.argmin(c["med"]))
            ax.plot(c["secs"][j], c["med"][j], "o", mfc="none", mec=key[path], ms=13, mew=1.8,
                    zorder=4)

      if scale == "floor":
         # The best pairwise reached. Grey and dotted, because it is a fact about the grey curve.
         ref = float(curves["pairwise"]["med"].min())
      else:
         # One is the null band: the score a genuine target batch produces. Nothing can go
         # meaningfully below it, because there the test can no longer tell the two apart.
         ref = 1.
      ax.axhline(ref, ls=":", color=key["pairwise"], lw=1.4, zorder=2)

      print(f"   {label} ({sub}): dividing by {floor:.3e} ({scale})")
      # A score every path reached, so the time to reach it is defined for all of them.
      common = max(float(curves[p]["med"].min()) for p in shown)
      when = {}
      for path, c in curves.items():
         hit = c["secs"][c["med"] <= 1.01 * common]
         when[path] = float(hit.min()) if len(hit) else None
         pen = c["best"] / curves["pairwise"]["best"] - 1.
         print(f"      {path:<16} {rows[path]['seconds']:.2f} s/epoch   "
               f"best {np.median(c['best']):.1f} "
               f"[{c['best'].min():.1f}, {c['best'].max():.1f}]   "
               f"final {np.median(c['med'][-1]):.1f}   "
               f"penalty {100 * np.median(pen):+.1f}% "
               f"[{100 * pen.min():+.1f}%, {100 * pen.max():+.1f}%]   "
               f"reached {common:.1f} after "
               + (f"{when[path]:.1f} s" if when[path] else "never")
               + f"   final KS {rows[path]['ks']:.3f}   "
               f"share {100 * data['shares'][path]['share']:.1f}%")

      ax.set_xscale("log")
      ax.set_yscale("log")
      ax.set_xlim(0.75 * min(c["secs"][0] for c in curves.values()),
                  1.5 * max(c["secs"][-1] for c in curves.values()))
      # The reference line must be inside the frame, or the axis promises a line it never draws.
      ax.set_ylim(min(0.85 * lo, 0.75 * ref), 1.5 * hi)
      xt = [0.05, 0.1, 0.5, 1., 5., 10., 25., 100.]
      ax.set_xticks(xt)
      ax.set_xticklabels([f"{t:g} s" for t in xt])
      yt = ([400, 600, 1000, 2000, 4000, 8000] if scale == "floor" else
            [1, 3, 10, 30, 100, 300, 1000])
      ax.set_yticks(yt)
      ax.set_yticklabels([f"{t:,}×" for t in yt])
      ax.tick_params(which="minor", length=2)
      ax.grid(which="minor", alpha=0.12)
      ax.set_xlabel("seconds of training")
      ax.set_title(f"{label}   ·   {sub}", pad=12)

   axes[0][0].set_ylabel("distance from uniform,\nas a multiple of a true $N(0, I)$ batch")
   handles = [plt.Line2D([], [], color=key[p], lw=wide.get(p, 2.), marker="o", ms=4.6,
                         markeredgecolor="white", markeredgewidth=0.7, label=shown[p])
              for p in shown]
   if mark_epoch:
      handles += [plt.Line2D([], [], color="#888888", lw=0, marker="s", mfc="white",
                             mec="#888888", ms=9, mew=1.6,
                             label=f"where the {mark_epoch}-epoch run stopped")]
   elif scale == "floor":
      handles += [plt.Line2D([], [], color="#888888", lw=0, marker="o", mfc="none",
                             mec="#888888", ms=11, mew=1.6, label="best point of the run")]
   if scale == "floor":
      handles += [plt.Rectangle((0, 0), 1, 1, fc="#888888", alpha=0.2, ec="none",
                                label="spread over three seeds")]
   fig.legend(handles=handles, ncol=5, loc="upper center", bbox_to_anchor=(0.5, 0.945),
              frameon=False, fontsize=9, columnspacing=1.8, handlelength=2.4)
   epochs = len(panels[0][5]["pairwise"]["med"])
   fig.suptitle(f"Batch 4096, {epochs} epochs, identical weights and batch order", y=0.99)
   fig.subplots_adjust(top=0.79, wspace=0.06)
   fig.savefig(HERE / out)
   plt.close(fig)


if __name__ == "__main__":
   FigureBlindness()
   FigureBudget()
   FigureCost()
   FigureTraining()
   FigureTraining(suffix="_long", out="measured_training_long.png", scale="band")
   print(f"\nfigures written to {HERE}")
