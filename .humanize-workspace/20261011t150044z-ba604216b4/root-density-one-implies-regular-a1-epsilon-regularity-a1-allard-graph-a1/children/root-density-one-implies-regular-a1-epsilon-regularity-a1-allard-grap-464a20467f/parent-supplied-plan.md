# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-464a20467f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1`
- Child key: `lipschitz_approximation`
- Declaration: `Submission.dorag_lipschitz_approximation`
- Exact Lean type: `∀ (n k : ℕ), 0 < n → ∀ C₆ : ℝ, 1 ≤ C₆ → ∃ δ₅ β β' C₇ : ℝ, 0 < δ₅ ∧ δ₅ ≤ 1 / 8 ∧ 0 < β' ∧ β' ≤ β ∧ β ≤ 1 / 4 ∧ 0 < C₇ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₅ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ₀ L : ℝ) (T₀ : Submodule ℝ (Euclid (n + k))), 0 < σ₀ → σ₀ ≤ δ * ρ → Module.finrank ℝ T₀ = n → 0 < L → L ≤ 1 → δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ≤ β * L → ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (C₆ * (δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))) ^ 2 * σ₀ ^ n) → (∀ x ∈ R.measure.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ v w, ‖f v - f w‖ ≤ L * ‖v - w‖) ∧ (∀ v, ‖f v‖ ≤ C₇ * δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) * σ₀) ∧ R.measure (closedBall ξ (σ₀ / 2) \ range (fun v => ξ + ι v + ι' (f v))) + μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ (σ₀ / 4)) ≤ ENNReal.ofReal (C₇ / L ^ 2) * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ∧ ((∀ y ∈ R.measure.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y t, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (β' ^ 2 * L ^ 2 * t ^ n)) → R.measure.support ∩ closedBall ξ (σ₀ / 8) = range (fun v => ξ + ι v + ι' (f v)) ∩ closedBall ξ (σ₀ / 8))`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.tangent_projection_measurable-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.monotonicity-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.density_bounds-a1`
- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.affine_approximation-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
