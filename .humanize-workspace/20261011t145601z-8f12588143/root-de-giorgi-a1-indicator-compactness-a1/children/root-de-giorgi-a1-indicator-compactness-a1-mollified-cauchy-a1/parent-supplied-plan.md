# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.mollified_cauchy-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-mollified-cauchy-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child key: `mollified_cauchy`
- Declaration: `Submission.indCompact_local_cauchy_of_mollified_cauchy`
- Exact Lean type: `∀ (N : ℕ) (F : ℕ → Set (Rn N)) (ρ : ℕ → Rn N → ℝ), (∀ k, NullMeasurableSet (F k) volume) → (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) → (∀ m y, 0 ≤ ρ m y) → (∀ m, ∫ y, ρ m y = 1) → (∀ m, Function.support (ρ m) ⊆ Metric.closedBall (0 : Rn N) (1 / ((m : ℝ) + 1))) → (∀ R : ℕ, ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ h : Rn N, ‖h‖ ≤ 1 → volume (Metric.ball (0 : Rn N) R ∩ symmDiff ((fun y ↦ y + h) ⁻¹' F k) (F k)) ≤ ENNReal.ofReal (C * ‖h‖)) → (∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, ∀ y ∈ Metric.closedBall (0 : Rn N) m, |(∫ z in F k, ρ m (y - z)) - ∫ z in F l, ρ m (y - z)| ≤ ε) → ∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
