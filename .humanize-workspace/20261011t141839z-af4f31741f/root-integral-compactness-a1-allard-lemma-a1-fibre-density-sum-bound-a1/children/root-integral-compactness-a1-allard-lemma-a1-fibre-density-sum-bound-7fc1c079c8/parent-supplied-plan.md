# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1.separated_sum_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141839Z-af4f31741f/nodes/root-integral-compactness-a1-allard-lemma-a1-fibre-density-sum-bound-7fc1c079c8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integral_compactness-a1.allard_lemma-a1.fibre_density_sum_bound-a1`
- Child key: `separated_sum_bound`
- Declaration: `Submission.intcpt_allard_fdsb_separated_sum_bound`
- Exact Lean type: `∀ (N n : ℕ) (μ : Measure (Euclidean N)) (P : Grassmannian N n) (x : Euclidean N) (s : Finset (Euclidean N)) (Θ : Euclidean N → ℝ≥0∞) (K c δ ε : ℝ) (M : ℕ), 0 ≤ K → 0 ≤ c → 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε ≤ δ ^ 4 → (2 + 2 * c + 2 * c / (unitBallVolume n).toReal + 2 * (M : ℝ) * K / (unitBallVolume n).toReal) * δ ≤ 1 → 2 ≤ s.card → s.card ≤ M → (∀ y ∈ s, ‖y - x‖ < ε ∧ ∀ τ σ : ℝ, 0 < τ → τ ≤ 1 / 4 → 0 < σ → σ < 1 → Θ y ≤ (ENNReal.ofReal (Real.exp ε) * (μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < 4 * τ}) / ENNReal.ofReal σ ^ n) + ENNReal.ofReal (K * ε * σ / τ)) / unitBallVolume n) → (∀ σ τ : ℝ, 0 < σ → σ ≤ δ ^ 2 → 2 * δ ^ 2 * σ ≤ τ → (∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → 4 * τ ≤ ‖y - y'‖) → ∑ y ∈ s, μ (closedBall y σ ∩ {z | ‖(z - y) - Grassmannian.project P (z - y)‖ < τ}) / ENNReal.ofReal σ ^ n ≤ ENNReal.ofReal (1 + c * δ ^ 2) * μ (closedBall x 1) + ENNReal.ofReal (c * δ ^ 2)) → ∑ y ∈ s, Θ y ≤ ENNReal.ofReal (1 + δ) * μ (closedBall x 1) / unitBallVolume n + ENNReal.ofReal δ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
