# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-comparison-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1`
- Child key: `graph_comparison`
- Declaration: `Submission.any_radius_graph_comparison`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δE : ℝ, 0 < δE ∧ ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δE → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (Ω : Set (Rn n)), IsOpen Ω → ContDiffOn ℝ 1 u Ω → q '' graphOver u Ω ⊆ V.support ∩ ball 0 ρ → (∀ A : Set (Rn n), MeasurableSet A → A ⊆ Ω → ∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in A, g (q (graphPoint x (u x))) ≤ ∫⁻ y in q '' graphOver u A, g y ∂V.weight) ∧ (∀ᵐ x ∂(volume.restrict Ω), V.tangentProj (q (graphPoint x (u x))) = (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u x v)))).starProjection) ∧ ∀ᵐ x ∂(volume.restrict Ω), Tendsto (fun s : ℝ => (V.weight (closedBall (q (graphPoint x (u x))) s))⁻¹ * ∫⁻ y in closedBall (q (graphPoint x (u x))) s, ENNReal.ofReal (hsNormSq (V.tangentProj y - V.tangentProj (q (graphPoint x (u x))))) ∂V.weight) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- `root.allard_any_radius-a1.tangent_ae-a1`
- `root.allard_any_radius-a1.monotonicity_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
