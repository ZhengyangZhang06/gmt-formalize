# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.shift_change_of_variables-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1-sh-117fddf760/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child key: `shift_change_of_variables`
- Declaration: `Submission.indCompact_transEst_integral_indicator_shift_mul`
- Exact Lean type: `∀ (N : ℕ) (F : Set (Rn N)) (ψ : Rn N → ℝ) (h : Rn N), NullMeasurableSet F volume → Integrable ψ volume → ∫ y, (F.indicator (1 : Rn N → ℝ) (y + h) - F.indicator (1 : Rn N → ℝ) y) * ψ y = ∫ z in F, (ψ (z - h) - ψ z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
