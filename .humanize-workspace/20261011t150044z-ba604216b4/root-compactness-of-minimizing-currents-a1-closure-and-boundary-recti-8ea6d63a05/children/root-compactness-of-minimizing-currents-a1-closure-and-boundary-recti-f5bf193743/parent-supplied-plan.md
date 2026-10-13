# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.cycle_const-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f5bf193743/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1`
- Child key: `cycle_const`
- Declaration: `Submission.cbrld_cone_cycle_eval_eq_zero_of_const_on_ball`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (x₀ : Euclid P) (r : ℝ) (α : Covector (Euclid P) (n + 1)) (φ : TestFormOn (univ : Set (Euclid P)) (n + 1)), 0 < r → X.boundary = 0 → X.support ⊆ ball x₀ r → (∀ x ∈ ball x₀ r, (φ : DifferentialForm (Euclid P) (n + 1)) x = α) → X φ = 0`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.affine_primitive-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.lower_density-a1.cone-a1.localize-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
