# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1.cylinder_weight-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-cylinder-monotonicity-a1-73165036b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.cylinder_monotonicity-a1`
- Child key: `cylinder_weight`
- Declaration: `Submission.intcpt_allard_cm_cylinder_weight`
- Exact Lean type: `∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ (N n : ℕ) (P : Grassmannian N n) (y : Euclidean N) (τ : ℝ), 0 < τ → ∃ h : Euclidean N → ℝ, ContDiff ℝ 1 h ∧ (∀ z, 0 ≤ h z ∧ h z ≤ 1) ∧ (∀ z, ‖(z - y) - Grassmannian.project P (z - y)‖ < τ → h z = 1) ∧ (∀ z, 2 * τ ≤ ‖(z - y) - Grassmannian.project P (z - y)‖ → h z = 0) ∧ ∀ (z : Euclidean N) (S : Grassmannian N n), |fderiv ℝ h z (Grassmannian.project S (z - y))| ≤ M₀ / τ * ‖LinearMap.toContinuousLinearMap (Grassmannian.projectionLinearMap S - Grassmannian.projectionLinearMap P)‖ * ‖z - y‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
