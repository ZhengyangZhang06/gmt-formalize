# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_regularity-a1.graph_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-regularity-a1-graph-comparison-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_regularity-a1`
- Child key: `graph_comparison`
- Declaration: `Submission.allard52_graph_comparison`
- Exact Lean type: `∀ (n : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ (ℓ : ℕ) (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ) (δ ρ : ℝ), 0 < δ → δ ≤ δ₂ → V.AllardHypotheses H p δ ρ → ∀ (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (f : Rn n → Rn ℓ) (R : ℝ), 0 < R → R ≤ δ * ρ → f 0 = 0 → LipschitzOnWith 1 f (closedBall 0 R) → V.support ∩ closedBall 0 R = q '' graphOver f (closedBall 0 R) ∩ closedBall 0 R → ∀ Φ : Amb n ℓ → (Amb n ℓ →L[ℝ] Amb n ℓ) → ℝ≥0∞, Measurable (Function.uncurry Φ) → ∀ A : Set (Rn n), MeasurableSet A → A ⊆ ball 0 (R / 2) → ∫⁻ x in A, Φ (q (graphPoint x (f x))) ((Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ f x v))).map q.toLinearEquiv.toLinearMap).starProjection ≤ ∫⁻ y in q '' graphOver f A, Φ y (V.tangentProj y) ∂V.weight`

## Sibling prerequisites

- `root.allard_regularity-a1.tangent_ae-a1`
- `root.allard_regularity-a1.density_bounds-a1`
- `root.allard_regularity-a1.graph_plane_algebra-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
