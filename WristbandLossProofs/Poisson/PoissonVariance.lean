import WristbandLossProofs.Poisson.PoissonEstimator
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic

set_option autoImplicit false

noncomputable section

namespace WristbandLossProofs

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The energy one draw produces. `realizedEnergy_eq_average` says the realized
energy is the mean of `D` of these, one per draw. -/
def drawEnergy (S : AngularSampler d Ω) (β : ℝ) (P : Distribution (Wristband d)) :
    Ω → ℝ :=
  fun z => ∫ q, drawWristbandKernel S β z q.1 q.2
    ∂((P : Measure (Wristband d)).prod (P : Measure (Wristband d)))

/-- The realized energy is, almost everywhere, the sample mean of `D` independent
copies of `drawEnergy`. -/
lemma realizedEnergy_ae_eq_mean (S : AngularSampler d Ω) (β : ℝ) {D : ℕ}
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P) :
    (fun ω : Fin D → Ω => kernelEnergy (realizedWristbandKernel S β ω) P)
      =ᵐ[(drawLaw S D : Measure (Fin D → Ω))]
      fun ω => (D : ℝ)⁻¹ * ∑ j : Fin D, drawEnergy S β P (ω j) := by
  set μ : Measure Ω := (S.law : Measure Ω) with hμ
  set PP : Measure (Wristband d × Wristband d) :=
    (P : Measure (Wristband d)).prod (P : Measure (Wristband d)) with hPP
  have hmp : ∀ j : Fin D,
      MeasurePreserving (Function.eval j) (Measure.pi fun _ : Fin D => μ) μ :=
    fun j => measurePreserving_eval (fun _ : Fin D => μ) j
  have hae : ∀ᵐ z ∂μ, Integrable (fun q : Wristband d × Wristband d =>
      drawWristbandKernel S β z q.1 q.2) PP := Integrable.prod_right_ae hInt
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin D => μ), ∀ j : Fin D,
      Integrable (fun q : Wristband d × Wristband d =>
        drawWristbandKernel S β (ω j) q.1 q.2) PP :=
    ae_all_iff.mpr fun j => (hmp j).quasiMeasurePreserving.tendsto_ae.eventually hae
  have hlaw : (drawLaw S D : Measure (Fin D → Ω))
      = Measure.pi fun _ : Fin D => μ := rfl
  rw [hlaw]
  filter_upwards [hall] with ω h using realizedEnergy_eq_average S β ω P h

/-! ### The variance falls as `1/D`

The draws are independent, so the variance of their mean is the variance of one
draw divided by `D`. Nothing here is specific to this sampler. -/

/-- **The realized energy has variance `Var[one draw] / D`.**

`hL2` is the hypothesis that one draw's energy has a finite second moment; it is
the quantity every feature-count rule is written in. -/
theorem realizedEnergy_variance (S : AngularSampler d Ω) (β : ℝ) {D : ℕ}
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P)
    (hL2 : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω)) :
    Var[fun ω : Fin D → Ω => kernelEnergy (realizedWristbandKernel S β ω) P ;
        (drawLaw S D : Measure (Fin D → Ω))]
      = Var[drawEnergy S β P; (S.law : Measure Ω)] / D := by
  set μ : Measure Ω := (S.law : Measure Ω) with hμ
  set g : Ω → ℝ := drawEnergy S β P with hg
  have hlaw : (drawLaw S D : Measure (Fin D → Ω))
      = Measure.pi fun _ : Fin D => μ := rfl
  have hmp : ∀ j : Fin D,
      MeasurePreserving (Function.eval j) (Measure.pi fun _ : Fin D => μ) μ :=
    fun j => measurePreserving_eval (fun _ : Fin D => μ) j
  -- each coordinate copy is `L²` and has the same variance
  have hL2j : ∀ j : Fin D, MemLp (fun ω : Fin D → Ω => g (ω j)) 2
      (Measure.pi fun _ : Fin D => μ) :=
    fun j => hL2.comp_measurePreserving (hmp j)
  have hvarj : ∀ j : Fin D, Var[fun ω : Fin D → Ω => g (ω j) ;
      Measure.pi fun _ : Fin D => μ] = Var[g; μ] :=
    fun j => (hmp j).variance_fun_comp hL2.aestronglyMeasurable.aemeasurable
  -- the coordinate copies are independent
  have hindep : iIndepFun (fun (j : Fin D) (ω : Fin D → Ω) => g (ω j))
      (Measure.pi fun _ : Fin D => μ) :=
    iIndepFun_pi (fun _ => hL2.aestronglyMeasurable.aemeasurable)
  have hfun : (∑ j : Fin D, (fun ω : Fin D → Ω => g (ω j)))
      = fun ω : Fin D → Ω => ∑ j : Fin D, g (ω j) := by
    funext ω; simp
  have hsum : Var[fun ω : Fin D → Ω => ∑ j : Fin D, g (ω j) ;
      Measure.pi fun _ : Fin D => μ] = ∑ _j : Fin D, Var[g; μ] := by
    rw [← hfun]
    refine (IndepFun.variance_sum (μ := Measure.pi fun _ : Fin D => μ)
      (X := fun (j : Fin D) (ω : Fin D → Ω) => g (ω j)) (s := Finset.univ)
      (fun j _ => hL2j j) (fun i _ j _ hij => hindep.indepFun hij)).trans ?_
    exact Finset.sum_congr rfl fun j _ => hvarj j
  rw [variance_congr (realizedEnergy_ae_eq_mean S β P hInt), hlaw,
    variance_const_mul, ← hg, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos D with hD0 | hD0
  · subst hD0; simp
  · field_simp

/-- The realized energy is square-integrable whenever one draw's energy is. -/
lemma realizedEnergy_memLp_two (S : AngularSampler d Ω) (β : ℝ) {D : ℕ}
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P)
    (hL2 : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω)) :
    MemLp (fun ω : Fin D → Ω => kernelEnergy (realizedWristbandKernel S β ω) P) 2
      (drawLaw S D : Measure (Fin D → Ω)) := by
  set μ : Measure Ω := (S.law : Measure Ω) with hμ
  have hlaw : (drawLaw S D : Measure (Fin D → Ω))
      = Measure.pi fun _ : Fin D => μ := rfl
  have hmp : ∀ j : Fin D,
      MeasurePreserving (Function.eval j) (Measure.pi fun _ : Fin D => μ) μ :=
    fun j => measurePreserving_eval (fun _ : Fin D => μ) j
  have hL2j : ∀ j : Fin D, MemLp (fun ω : Fin D → Ω => drawEnergy S β P (ω j)) 2
      (Measure.pi fun _ : Fin D => μ) :=
    fun j => hL2.comp_measurePreserving (hmp j)
  have hmean : MemLp (fun ω : Fin D → Ω =>
      (D : ℝ)⁻¹ * ∑ j : Fin D, drawEnergy S β P (ω j)) 2
      (Measure.pi fun _ : Fin D => μ) := by
    have hfun : (∑ j : Fin D, (fun ω : Fin D → Ω => drawEnergy S β P (ω j)))
        = fun ω : Fin D → Ω => ∑ j : Fin D, drawEnergy S β P (ω j) := by
      funext ω; simp
    have : MemLp (fun ω : Fin D → Ω => ∑ j : Fin D, drawEnergy S β P (ω j)) 2
        (Measure.pi fun _ : Fin D => μ) :=
      hfun ▸ memLp_finset_sum' (μ := Measure.pi fun _ : Fin D => μ)
        (p := 2) Finset.univ (fun j _ => hL2j j)
    exact this.const_mul _
  rw [hlaw]
  exact hmean.ae_eq (Filter.EventuallyEq.symm
    (by rw [hlaw] at *; exact realizedEnergy_ae_eq_mean S β P hInt))

/-! ### Chebyshev, and the feature count it dictates -/

/-- **Chebyshev for the realized energy.** The chance the estimate misses the true
energy by `ε` is at most `Var[one draw] / (D ε²)`. -/
theorem realizedEnergy_chebyshev (S : AngularSampler d Ω) (β α : ℝ) {D : ℕ}
    (hD : 0 < D) (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P)
    (hL2 : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω)) {ε : ℝ} (hε : 0 < ε) :
    (drawLaw S D : Measure (Fin D → Ω))
        {ω | ε ≤ |kernelEnergy (realizedWristbandKernel S β ω) P
              - kernelEnergy (wristbandKernelNeumann (d := d) β α) P|}
      ≤ ENNReal.ofReal
          (Var[drawEnergy S β P; (S.law : Measure Ω)] / (D * ε ^ 2)) := by
  have hmean : ∫ ω, kernelEnergy (realizedWristbandKernel S β ω) P
      ∂(drawLaw S D : Measure (Fin D → Ω))
      = kernelEnergy (wristbandKernelNeumann (d := d) β α) P :=
    realizedEnergy_unbiased S β α hD hUnbiased P hInt
  have hcheb := meas_ge_le_variance_div_sq
    (μ := (drawLaw S D : Measure (Fin D → Ω)))
    (realizedEnergy_memLp_two (D := D) S β P hInt hL2) hε
  rw [hmean, realizedEnergy_variance S β P hInt hL2] at hcheb
  refine hcheb.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
  field_simp

/-- **The feature-count rule.** To hold the estimate within `ε` of the true energy
with probability at least `1 - δ`, it is enough to take
`D ≥ V / (δ ε²)`, where `V` bounds one draw's variance. -/
theorem featureCount_suffices (S : AngularSampler d Ω) (β α : ℝ) {D : ℕ}
    (hD : 0 < D) (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P)
    (hL2 : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω))
    {V δ ε : ℝ} (hV : Var[drawEnergy S β P; (S.law : Measure Ω)] ≤ V)
    (hδ : 0 < δ) (hε : 0 < ε) (hcount : V / (δ * ε ^ 2) ≤ (D : ℝ)) :
    (drawLaw S D : Measure (Fin D → Ω))
        {ω | ε ≤ |kernelEnergy (realizedWristbandKernel S β ω) P
              - kernelEnergy (wristbandKernelNeumann (d := d) β α) P|}
      ≤ ENNReal.ofReal δ := by
  refine (realizedEnergy_chebyshev S β α hD hUnbiased P hInt hL2 hε).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hden : (0 : ℝ) < (D : ℝ) * ε ^ 2 := by positivity
  rw [div_le_iff₀ hden]
  have hVD : V ≤ (D : ℝ) * (δ * ε ^ 2) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ * ε ^ 2)] at hcount
    linarith
  nlinarith [hV]

/-- The same rule in the form a practitioner uses: to hold the estimate within a
*relative* error `ε` of the true energy, take `D ≥ ϱ / (δ ε²)`, where `ϱ` bounds
one draw's variance in units of the squared energy. `ϱ` carries no `D`, no batch
size and no dimension — it is a property of the kernel alone. -/
theorem featureCount_suffices_relative (S : AngularSampler d Ω) (β α : ℝ) {D : ℕ}
    (hD : 0 < D) (hUnbiased : IsUnbiasedFor S (kernelAngChordal (d := d) β α))
    (P : Distribution (Wristband d)) (hInt : HasIntegrableDrawEnergy S β P)
    (hL2 : MemLp (drawEnergy S β P) 2 (S.law : Measure Ω))
    {ϱ δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hE : 0 < kernelEnergy (wristbandKernelNeumann (d := d) β α) P)
    (hϱ : Var[drawEnergy S β P; (S.law : Measure Ω)]
      ≤ ϱ * kernelEnergy (wristbandKernelNeumann (d := d) β α) P ^ 2)
    (hcount : ϱ / (δ * ε ^ 2) ≤ (D : ℝ)) :
    (drawLaw S D : Measure (Fin D → Ω))
        {ω | ε * kernelEnergy (wristbandKernelNeumann (d := d) β α) P
              ≤ |kernelEnergy (realizedWristbandKernel S β ω) P
                - kernelEnergy (wristbandKernelNeumann (d := d) β α) P|}
      ≤ ENNReal.ofReal δ := by
  set E := kernelEnergy (wristbandKernelNeumann (d := d) β α) P with hEdef
  refine featureCount_suffices S β α hD hUnbiased P hInt hL2 (V := ϱ * E ^ 2)
    hϱ hδ (by positivity) ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ * (ε * E) ^ 2)]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ * ε ^ 2)] at hcount
  nlinarith [sq_nonneg E, hE]

end WristbandLossProofs
