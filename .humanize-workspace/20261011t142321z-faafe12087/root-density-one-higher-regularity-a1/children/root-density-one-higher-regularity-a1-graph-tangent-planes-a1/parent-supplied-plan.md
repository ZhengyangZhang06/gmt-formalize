# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.graph_tangent_planes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-graph-tangent-planes-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1`
- Child key: `graph_tangent_planes`
- Declaration: `Submission.dohr_graph_tangent_planes`
- Exact Lean type: `∀ n ℓ : ℕ, 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (s R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), 0 < s → s ≤ R → closedBall ξ s ⊆ U → ContDiffOn ℝ 1 u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → AEStronglyMeasurable (fun y => V.tangentProj y) (V.weight.restrict (ball ξ s)) ∧ ∀ᵐ y ∂V.weight, y ∈ ball ξ s → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
