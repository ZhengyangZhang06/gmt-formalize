# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1.normalization-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-a44cc12920/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.constant_planes-a1`
- Child key: `normalization`
- Declaration: `Submission.cbr_ci_cp_eval_eq_orthonormal_frame`
- Exact Lean type: `∀ (P d : ℕ) (ζ₀ : MultiVector P (d + 1)) (V : Submodule ℝ (Euclid P)), Module.finrank ℝ V ≤ d + 1 → (∀ β : Covector (Euclid P) (d + 1), |ζ₀ β| ≤ covectorEuclideanNorm β) → (∃ β : Covector (Euclid P) (d + 1), covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = 1) → (∀ β : Covector (Euclid P) (d + 1), ζ₀ β = ζ₀ (β.compContinuousLinearMap V.starProjection)) → Module.finrank ℝ V = d + 1 ∧ ∃ v : Fin (d + 1) → Euclid P, Orthonormal ℝ v ∧ Submodule.span ℝ (Set.range v) = V ∧ ∀ β : Covector (Euclid P) (d + 1), ζ₀ β = β v`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_eval_le-a1`
- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_norming-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
