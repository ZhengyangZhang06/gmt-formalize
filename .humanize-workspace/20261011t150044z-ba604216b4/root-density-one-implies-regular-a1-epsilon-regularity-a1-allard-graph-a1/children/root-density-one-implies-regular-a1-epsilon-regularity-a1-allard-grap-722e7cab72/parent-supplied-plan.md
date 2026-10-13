# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_decay-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-722e7cab72/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child key: `tilt_excess_decay`
- Declaration: `Submission.dorag_tilt_excess_decay`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∃ δ₂ C : ℝ, 0 < δ₂ ∧ δ₂ ≤ 1 / 8 ∧ 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ : ℝ) (T : Submodule ℝ (Euclid (n + k))), 0 < σ → σ ≤ δ * ρ → Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ (∀ s : ℝ, 0 < s → s ≤ σ → ∫⁻ x in closedBall ξ s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C * (s / σ) * s ^ n) * max (ENNReal.ofReal (1 / σ ^ n) * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * σ ^ 2 / δ))) ∧ ENNReal.ofReal (∑ i : Fin (n + k), ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal C * max (ENNReal.ofReal (1 / σ ^ n) * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * σ ^ 2 / δ))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tangent_projection_measurable-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tilt_excess_step-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
