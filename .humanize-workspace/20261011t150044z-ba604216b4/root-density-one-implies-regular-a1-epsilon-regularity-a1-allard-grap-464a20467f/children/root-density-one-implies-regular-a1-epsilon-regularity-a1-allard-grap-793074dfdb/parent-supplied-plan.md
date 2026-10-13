# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.bad_set-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-allard-grap-793074dfdb/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1`
- Child key: `bad_set`
- Declaration: `Submission.dorag_lip_bad_set_measure_bound`
- Exact Lean type: `∀ (n k : ℕ) (μ : Measure (Euclid (n + k))) (e : Euclid (n + k) → ℝ) (ξ : Euclid (n + k)) (σ₀ a : ℝ), 0 < σ₀ → 0 < a → (∀ y ∈ closedBall ξ (3 * σ₀ / 4), ∀ t : ℝ, 0 < t → t ≤ 5 * σ₀ / 4 → μ (closedBall y t) ≤ 2 * unitBallVolume n * ENNReal.ofReal (t ^ n)) → μ (closedBall ξ (3 * σ₀ / 4) \ {y | y ∈ μ.support ∧ ∀ t : ℝ, 0 < t → t ≤ σ₀ / 2 → ∫⁻ x in closedBall y (t / 2), ENNReal.ofReal (e x) ∂μ ≤ ENNReal.ofReal (a * t ^ n)}) ≤ ENNReal.ofReal (2 * (5 / 2) ^ n / a) * unitBallVolume n * ∫⁻ x in closedBall ξ σ₀, ENNReal.ofReal (e x) ∂μ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.allard_graph-a1.lipschitz_approximation-a1.vitali_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
