# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1.normal_trace_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-mean-curvature-of-stationary-a1-7a456981d2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.minimizing_implies_stationary-a1.mean_curvature_of_stationary-a1`
- Child key: `normal_trace_identity`
- Declaration: `Submission.mcs_trace_normal_part_eq_neg_inner`
- Exact Lean type: `∀ (P : ℕ) (Q S : Submodule ℝ (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X Y : Euclid P → Euclid P) (x : Euclid P), Q ≤ S → pr x = S.starProjection → DifferentiableAt ℝ pr x → DifferentiableAt ℝ X x → Y =ᶠ[𝓝 x] (fun y => X y - pr y (X y)) → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ Y x).toLinearMap) = -inner ℝ (X x) (∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (Q.starProjection (EuclideanSpace.single j 1))) (Q.starProjection (EuclideanSpace.single j 1)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
