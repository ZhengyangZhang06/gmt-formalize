# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_comparison-a1.graph_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1-graph-tangent-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_comparison-a1`
- Child key: `graph_tangent`
- Declaration: `Submission.anyrad_gc_graph_tangentProj_ae`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (Ω : Set (Rn n)), IsOpen Ω → ContDiffOn ℝ 1 u Ω → (∀ P : Amb n ℓ → Prop, (∀ᵐ y ∂V.weight, P y) → ∀ᵐ x ∂(volume.restrict Ω), P (q (graphPoint x (u x)))) → ∀ᵐ x ∂(volume.restrict Ω), V.tangentProj (q (graphPoint x (u x))) = (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u x v)))).starProjection`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.tangent_plane_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
