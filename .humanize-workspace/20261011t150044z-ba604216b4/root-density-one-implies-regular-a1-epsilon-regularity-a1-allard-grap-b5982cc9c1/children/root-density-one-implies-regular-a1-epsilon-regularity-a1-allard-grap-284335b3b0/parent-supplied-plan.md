# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1.test_field_divergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-284335b3b0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_height-a1`
- Child key: `test_field_divergence`
- Declaration: `Submission.dorag_th_trace_comp_fderiv_test_field`
- Exact Lean type: `∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)) (ζ : Euclid P → ℝ) (ξ x : Euclid P), DifferentiableAt ℝ ζ x → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))) x).toLinearMap) = ζ x ^ 2 * LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) + 2 * ζ x * fderiv ℝ ζ x (T.starProjection ((x - ξ) - S.starProjection (x - ξ)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
