# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1.cone_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3557b7f124/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.rectifiable-a1.cone_density-a1`
- Child key: `cone_cutoff`
- Declaration: `Submission.cbrr_tcd_cone_cutoff_exists`
- Exact Lean type: `∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (δ : ℝ), 0 < δ → ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, (∀ y, 0 ≤ f y) ∧ (∀ y, f y ≤ 1) ∧ (∀ y : Euclid P, 2 * ‖Q.starProjection y‖ < ‖y‖ → ‖y‖ < 1 → f y = 1) ∧ ∀ y ∈ Q, δ < ‖y‖ → f y = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
