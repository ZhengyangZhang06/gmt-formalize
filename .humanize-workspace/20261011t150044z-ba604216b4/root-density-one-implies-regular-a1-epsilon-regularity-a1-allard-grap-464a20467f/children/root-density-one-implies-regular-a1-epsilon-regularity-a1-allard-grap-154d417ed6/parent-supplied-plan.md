# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.cone_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-154d417ed6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `cone_estimate`
- Declaration: `Submission.dorag_lip_good_set_cone_estimate`
- Exact Lean type: `∀ (n k : ℕ) (C₃ C₆ : ℝ), 1 ≤ C₃ → 1 ≤ C₆ → ∃ C₈ : ℝ, 0 < C₈ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ ε β L : ℝ), AEStronglyMeasurable (fun x => (τ x).starProjection) μ → 0 < σ₀ → 0 ≤ ε → 0 < β → 0 < L → ε ≤ β * L → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∃ S : Submodule ℝ (Euclid (n + k)), (∀ x ∈ μ.support ∩ closedBall y t, ‖(x - y) - S.starProjection (x - y)‖ ≤ C₃ * ε * t) ∧ ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₃ * ε ^ 2 * (t / 2) ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 4 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ x ∈ μ.support ∩ closedBall ξ σ₀, ‖(x - ξ) - T₀.starProjection (x - ξ)‖ ≤ C₆ * ε * σ₀) → ∀ y₁ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), ∀ y₂ ∈ μ.support ∩ closedBall ξ (3 * σ₀ / 4), (∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y₁ (t / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal (β ^ 2 * L ^ 2 * t ^ n)) → ‖(y₂ - y₁) - T₀.starProjection (y₂ - y₁)‖ ≤ C₈ * β * L * ‖y₂ - y₁‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
