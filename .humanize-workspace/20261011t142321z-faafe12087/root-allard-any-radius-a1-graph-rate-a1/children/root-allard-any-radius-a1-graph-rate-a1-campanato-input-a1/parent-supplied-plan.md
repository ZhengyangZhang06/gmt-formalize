# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.allard_any_radius-a1.graph_rate-a1.campanato_input-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-allard-any-radius-a1-graph-rate-a1-campanato-input-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.allard_any_radius-a1.graph_rate-a1`
- Child key: `campanato_input`
- Declaration: `Submission.any_radius_gr_campanato_input`
- Exact Lean type: `∀ (n ℓ : ℕ) (U : Set (Amb n ℓ)) (V : RectifiableVarifold n ℓ U) (q : Amb n ℓ ≃ₗᵢ[ℝ] Amb n ℓ) (u : Rn n → Rn ℓ) (Ω : Set (Rn n)), AEStronglyMeasurable V.tangentProj V.weight → ContinuousOn u Ω → (∀ A : Set (Rn n), MeasurableSet A → A ⊆ Ω → ∀ g : Amb n ℓ → ℝ≥0∞, Measurable g → ∫⁻ x in A, g (q (graphPoint x (u x))) ≤ ∫⁻ y in q '' graphOver u A, g y ∂V.weight) → (∀ᵐ x ∂(volume.restrict Ω), V.tangentProj (q (graphPoint x (u x))) = (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u x v)))).starProjection) → ∀ (S : Submodule ℝ (Amb n ℓ)) (z : Rn n) (r s : ℝ), 0 < s → closedBall z r ⊆ Ω → (∀ x ∈ closedBall z r, hsNorm (fderiv ℝ u x) ≤ 1 / 4) → (∀ x ∈ closedBall z r, ‖q (graphPoint x (u x)) - q (graphPoint z (u z))‖ ≤ s) → (Submodule.map q.toLinearEquiv.toLinearMap (Submodule.span ℝ (Set.range fun v : Rn n => graphPoint v (fderiv ℝ u z v)))).starProjection = S.starProjection → V.weight (closedBall (q (graphPoint z (u z))) s) < ⊤ → ∫⁻ x in closedBall z r, ENNReal.ofReal (hsNormSq (fderiv ℝ u x - fderiv ℝ u z)) ≤ ENNReal.ofReal (s ^ n * V.tiltExcess (q (graphPoint z (u z))) s S)`

## Sibling prerequisites

- `root.allard_any_radius-a1.graph_rate-a1.la_basics-a1`
- `root.allard_any_radius-a1.graph_rate-a1.plane_projections-a1`
- `root.allard_any_radius-a1.graph_rate-a1.tilt_integrals-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
