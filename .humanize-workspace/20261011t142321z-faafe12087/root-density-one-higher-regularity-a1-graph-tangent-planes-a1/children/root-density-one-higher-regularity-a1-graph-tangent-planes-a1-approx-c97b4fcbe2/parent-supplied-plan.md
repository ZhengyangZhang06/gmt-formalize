# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1.approx_tangent_isometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1-approx-c97b4fcbe2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.graph_tangent_planes-a1`
- Child key: `approx_tangent_isometry`
- Declaration: `Submission.dohr_tp_approx_tangent_affine_isometry`
- Exact Lean type: `∀ (n ℓ : ℕ) (S : Set (Amb n ℓ)) (z ξ : Amb n ℓ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (P : Submodule ℝ (Amb n ℓ)), Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n S z P → Poincare.SimonGMT.Chapter03.HasApproximateTangentSpaceAt n ((fun w => ξ + Q w) '' S) (ξ + Q z) (Submodule.map Q.toLinearEquiv.toLinearMap P)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
