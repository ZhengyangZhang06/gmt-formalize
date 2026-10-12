# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.diagonal_arzela_ascoli-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-diagonal-arzela-ascoli-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1`
- Child key: `diagonal_arzela_ascoli`
- Declaration: `Submission.indCompact_diagonal_mollified_uniform_cauchy`
- Exact Lean type: `∀ (N : ℕ) (ρ : ℕ → Rn N → ℝ) (F : ℕ → Set (Rn N)), (∀ m, Continuous (ρ m)) → (∀ m, HasCompactSupport (ρ m)) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ (m : ℕ) (ε : ℝ), 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ l ≥ k₀, ∀ y ∈ Metric.closedBall (0 : Rn N) m, |(∫ z in F (φ k), ρ m (y - z)) - ∫ z in F (φ l), ρ m (y - z)| ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
