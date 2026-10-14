# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.density_gap-a1.allard_graph-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-density-gap-a1-allard-graph-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.density_gap-a1`
- Child key: `allard_graph`
- Declaration: `Submission.dimred_cdg_allard_bounded_curvature_graph`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ ε : ℝ, 0 < ε → ∃ δ₀ γ : ℝ, 0 < δ₀ ∧ 0 < γ ∧ γ ≤ 1 ∧ ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ₀) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ₀ → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ u 0 = 0 ∧ ContDiffOn ℝ 1 u (ball 0 (γ * ρ)) ∧ (∀ v ∈ ball (0 : Euclid n) (γ * ρ), ‖fderiv ℝ u v‖ ≤ ε) ∧ R.measure.support ∩ ball z (γ * ρ) = ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) (γ * ρ)) ∩ ball z (γ * ρ)`

## Sibling prerequisites

- `root.minimizing_implies_stationary-a1.tangent_projection_measurable-a1`
- `root.dimension_reduction_results-a1.density_gap-a1.harmonic_affine-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
