# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.local_cauchy_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-local-cauchy-limit-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child key: `local_cauchy_limit`
- Declaration: `Submission.indCompact_limit_of_local_cauchy`
- Exact Lean type: `∀ (N : ℕ) (F : ℕ → Set (Rn N)), (∀ k, NullMeasurableSet (F k) volume) → (∀ (R : ℕ) (ε : ℝ≥0∞), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, volume (Metric.ball (0 : Rn N) R ∩ symmDiff (F k) (F l)) ≤ ε) → ∃ G : Set (Rn N), MeasurableSet G ∧ ∀ K : Set (Rn N), IsCompact K → Tendsto (fun k ↦ volume (K ∩ symmDiff (F k) G)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
