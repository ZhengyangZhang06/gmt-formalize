# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1.symmdiff_l1_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/nodes/root-de-giorgi-a1-indicator-compactness-a1-translation-estimate-a1-sy-097b589f33/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.de_giorgi-a1.indicator_compactness-a1.translation_estimate-a1`
- Child key: `symmdiff_l1_identity`
- Declaration: `Submission.indCompact_transEst_volume_symmDiff_eq_integral`
- Exact Lean type: `∀ (N : ℕ) (A F : Set (Rn N)) (R : ℝ), NullMeasurableSet A volume → NullMeasurableSet F volume → volume (Metric.ball (0 : Rn N) R ∩ symmDiff A F) = ENNReal.ofReal (∫ y in Metric.ball (0 : Rn N) R, |A.indicator (1 : Rn N → ℝ) y - F.indicator (1 : Rn N → ℝ) y|)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
