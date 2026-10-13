# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.besicovitch_federer-a1.infinite_fibres-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-besicovitch-federer-a1-infinite-fibres-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.besicovitch_federer-a1`
- Child key: `infinite_fibres`
- Declaration: `Submission.bf_infiniteFibre_projection_null`
- Exact Lean type: `(∀ (N m k : ℕ), ∃ C : ℝ≥0, ∀ (A : Set (Rn N)) (f : Rn N → Rn m) (L : ℝ≥0), LipschitzWith L f → ∃ g : Rn m → ℝ≥0∞, Measurable g ∧ (∀ y, μHE[k] (A ∩ f ⁻¹' {y}) ≤ g y) ∧ ∫⁻ y, g y ≤ ((C * L ^ m : ℝ≥0) : ℝ≥0∞) * μHE[m + k] A) → ∀ (n ℓ : ℕ) (W : Submodule ℝ (Rn (n + ℓ))), finrank ℝ W = n → ∀ A : Set (Rn (n + ℓ)), μHE[n] A < ∞ → μHE[n] (W.starProjection '' {a | a ∈ A ∧ {b | b ∈ A ∧ W.starProjection b = W.starProjection a}.Infinite}) = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
