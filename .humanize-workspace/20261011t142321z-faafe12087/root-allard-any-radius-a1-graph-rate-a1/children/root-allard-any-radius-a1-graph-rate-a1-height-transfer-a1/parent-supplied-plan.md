# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.height_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-height-transfer-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1`
- Child key: `height_transfer`
- Declaration: `Submission.any_radius_gr_height_transfer`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (R ρ : ℝ), ContDiffOn ℝ 1 u (ball 0 R) → u 0 = 0 → (∀ x ∈ ball (0 : Rn n) R, ‖fderiv ℝ u x‖ ≤ 1 / 7) → q '' graphOver u (ball 0 R) ⊆ ball 0 ρ → AEStronglyMeasurable V.tangentProj V.weight → (∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in ball (0 : Rn n) R, g (q (graphPoint x (u x))) ≤ ∫⁻ y in q '' graphOver u (ball 0 R), g y ∂V.weight) → (∀ᵐ x ∂(volume.restrict (ball (0 : Rn n) R)), V.tangentProj (q (graphPoint x (u x))) = (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u x v)))).starProjection) → ∫⁻ x in ball (0 : Rn n) R, ENNReal.ofReal (‖u x - fderiv ℝ u x x‖ ^ 2 / ‖x‖ ^ (n + 2)) ≤ ENNReal.ofReal (2 ^ (n + 4)) * ∫⁻ y in ball (0 : Amb n ℓ) ρ, ENNReal.ofReal (‖y - V.tangentProj y y‖ ^ 2 / ‖y‖ ^ (n + 2)) ∂V.weight`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
