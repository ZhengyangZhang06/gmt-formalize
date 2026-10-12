# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_higher_regularity-a1.local_multiplicity_one-a1.graph_tangent_rank-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-density-one-higher-regularity-a1-local-multiplicity-one-a1-graph-cabb27e079/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_higher_regularity-a1.local_multiplicity_one-a1`
- Child key: `graph_tangent_rank`
- Declaration: `Submission.dohr_lmo_graph_tangent_rank`
- Exact Lean type: `∀ n ℓ : ℕ, ∀ (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (ξ : Amb n ℓ) (R : ℝ) (Q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ), ball ξ R ⊆ U → DifferentiableOn ℝ u (ball 0 R) → Q '' ((fun x => x - ξ) '' V.support) ∩ ball 0 R = graphOver u (ball 0 R) ∩ ball 0 R → (∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∀ x ∈ ball (0 : Rn n) R, Q (y - ξ) = graphPoint x (u x) → V.tangentProj y = (Submodule.map Q.symm.toLinearEquiv.toLinearMap (LinearMap.range (fderiv ℝ (fun z : Rn n => graphPoint z (u z)) x).toLinearMap)).starProjection) → ∀ᵐ y ∂V.weight, y ∈ ball ξ R → ∃ P : Submodule ℝ (Amb n ℓ), Module.finrank ℝ P = n ∧ V.tangentProj y = P.starProjection`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
