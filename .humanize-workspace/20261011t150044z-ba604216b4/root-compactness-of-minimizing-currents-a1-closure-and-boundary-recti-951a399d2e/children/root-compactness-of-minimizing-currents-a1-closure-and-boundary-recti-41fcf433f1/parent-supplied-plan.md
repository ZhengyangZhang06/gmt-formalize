# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.covector_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-41fcf433f1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1`
- Child key: `covector_bounds`
- Declaration: `Submission.cbr_ci_pw_orthonormal_covector_bounds`
- Exact Lean type: `∀ (P n : ℕ) (v : Fin n → Euclid P) (pL : Euclid P →L[ℝ] Euclid n), Orthonormal ℝ v → (∀ (x : Euclid P) (i : Fin n), pL x i = inner ℝ (v i) x) → (∀ β : Covector (Euclid P) n, |β v| ≤ covectorEuclideanNorm β) ∧ ∀ (l : ℕ) (γ : Covector (Euclid n) l), covectorEuclideanNorm (γ.compContinuousLinearMap pL) ≤ covectorEuclideanNorm γ`

## Sibling prerequisites

- `root.regular_components_are_minimizing-a1.imrep_mass_formula-a1.covector_sq_sum-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
