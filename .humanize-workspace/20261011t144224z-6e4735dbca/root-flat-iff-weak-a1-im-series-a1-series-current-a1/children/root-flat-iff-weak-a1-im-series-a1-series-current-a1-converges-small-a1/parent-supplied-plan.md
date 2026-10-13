# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.series_current-a1.converges_small-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-converges-small-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1`
- Child key: `converges_small`
- Declaration: `Submission.fiw_ims_sc_converges_zero_small`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (ω : ℕ → TestFormOn U n), TestFormOnConverges ω 0 → ∃ K : Set (Eucl P), IsCompact K ∧ K ⊆ U ∧ (∀ q, tsupport ((ω q : DifferentialForm (Eucl P) n)) ⊆ K) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q in atTop, ∀ x, covectorEuclideanNorm ((ω q : DifferentialForm (Eucl P) n) x) ≤ ε`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.series_current-a1.covector_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
