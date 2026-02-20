# AGENTS.md

## Lean Proof Workflow (Scratch + Finalize)

When working on Lean proofs in this repo:

1. Use a temporary scratch file outside the repository for fast probes.
   - Put it under `/tmp` (or `$TMPDIR`), not in the project tree.
   - Use it for `#check`, tiny `example` proofs, and quick tactic experiments.
2. Do not create persistent scratch files like `check.lean` in the repo unless explicitly requested.
3. Once the proof approach works, move only the finalized proof/code into the real `.lean` file in this repo.
4. Remove the temporary scratch file after use.
5. Run `lake build` after integrating changes to confirm the project still typechecks.

