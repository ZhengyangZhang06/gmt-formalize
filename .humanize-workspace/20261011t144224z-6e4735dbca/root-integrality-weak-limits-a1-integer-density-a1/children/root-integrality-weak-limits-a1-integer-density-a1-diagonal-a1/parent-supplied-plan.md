# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.integrality_weak_limits-a1.integer_density-a1.diagonal-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-integrality-weak-limits-a1-integer-density-a1-diagonal-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.integrality_weak_limits-a1.integer_density-a1`
- Child key: `diagonal`
- Declaration: `Submission.ind_diagonal_weak_limit`
- Exact Lean type: `∀ (P n : ℕ) (U W : Set (Eucl P)) (X : ℕ → ℕ → GeometricCurrentOn U n) (Z : ℕ → TestFormOn U n → ℝ) (L : TestFormOn U n → ℝ) (C : ℝ), IsCompact (closure W) → (∀ (k : ℕ) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun j => X k j ω) atTop (𝓝 (Z k ω))) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => Z k ω) atTop (𝓝 (L ω))) → (∀ k, ∀ᶠ j in atTop, (X k j).massOn W ≤ ENNReal.ofReal C) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ k, (X k (φ k)).massOn W ≤ ENNReal.ofReal C) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ W → Tendsto (fun k => X k (φ k) ω) atTop (𝓝 (L ω))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
