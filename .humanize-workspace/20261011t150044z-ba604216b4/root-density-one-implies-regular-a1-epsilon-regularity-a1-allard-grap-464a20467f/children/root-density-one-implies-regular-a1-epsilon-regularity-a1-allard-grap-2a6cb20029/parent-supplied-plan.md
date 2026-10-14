# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.off_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-2a6cb20029/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `off_support`
- Declaration: `Submission.dorag_lip_off_support_estimate`
- Exact Lean type: `∀ (n k : ℕ), ∃ lam₀ C₉ : ℝ, 0 < lam₀ ∧ 0 < C₉ ∧ ∀ (μ : Measure (Euclid (n + k))) (τ : Euclid (n + k) → Submodule ℝ (Euclid (n + k))) (T₀ : Submodule ℝ (Euclid (n + k))) (F : Set (Euclid (n + k))) (ξ : Euclid (n + k)) (σ₀ κ lam : ℝ), 0 < σ₀ → 0 ≤ κ → κ * σ₀ ≤ 1 → 0 ≤ lam → lam ≤ lam₀ → ξ ∈ μ.support → (∀ x ∈ F, ∀ x' ∈ F, ‖(x - x') - T₀.starProjection (x - x')‖ ≤ lam * ‖x - x'‖) → (∀ y ∈ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 8 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → (∀ y ∈ μ.support ∩ closedBall ξ (σ₀ / 2), ∀ t : ℝ, 0 < t → t ≤ σ₀ / 8 → unitBallVolume n * ENNReal.ofReal (t ^ n) ≤ 2 * μ (closedBall y t)) → (∀ (y : Euclid (n + k)) (s t : ℝ), y ∈ closedBall ξ (σ₀ / 4) → 0 < s → s < t → t ≤ 3 * σ₀ / 8 → ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * μ (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * μ (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (τ x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂μ) → ∀ η ∈ (F \ μ.support) ∩ closedBall ξ (σ₀ / 4), ∃ s : ℝ, ∃ y ∈ μ.support, 0 < s ∧ 2 * s ≤ dist η ξ ∧ dist y η = 2 * s ∧ ENNReal.ofReal (s ^ n) ≤ ENNReal.ofReal C₉ * (μ (closedBall η (3 * s) \ F) + ∫⁻ x in closedBall η (3 * s), ENNReal.ofReal (∑ i : Fin (n + k), ‖(τ x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₀.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
