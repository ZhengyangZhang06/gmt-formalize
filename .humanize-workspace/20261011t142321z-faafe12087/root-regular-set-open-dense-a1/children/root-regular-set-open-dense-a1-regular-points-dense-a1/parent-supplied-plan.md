# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_set_open_dense-a1.regular_points_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-regular-set-open-dense-a1-regular-points-dense-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_set_open_dense-a1`
- Child key: `regular_points_dense`
- Declaration: `Submission.rsod_regularSet_meets_ball`
- Exact Lean type: `AllardRegularityTheorem → ∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (p : ℝ), (n : ℝ) < p → V.HasGeneralizedMeanCurvature H → V.LocallyLp H p → (∀ᵐ x ∂V.weight, x ∈ V.support → ∃ k : ℕ, 1 ≤ k ∧ V.mult x = k) → ∀ ξ ∈ V.support, ∀ r : ℝ, 0 < r → (V.regularSet ∩ ball ξ r).Nonempty`

## Sibling prerequisites

- `root.regular_set_open_dense-a1.c1_submanifold_open_inter-a1`
- `root.regular_set_open_dense-a1.localized_varifold-a1`
- `root.regular_set_open_dense-a1.density_one_regular_point-a1`
- `root.regular_set_open_dense-a1.ae_approx_tangent_exists-a1`
- `root.regular_set_open_dense-a1.density_of_approx_tangent-a1`
- `root.regular_set_open_dense-a1.least_integer_density_point-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
