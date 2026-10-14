# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.im_series-a1.series_current-a1.series_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-series-current-a1-series-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.im_series-a1.series_current-a1`
- Child key: `series_bound`
- Declaration: `Submission.fiw_ims_sc_series_bound`
- Exact Lean type: `∀ (a : ℕ → ℝ) (c : ℕ → ℤ) (m : ℕ → ℝ≥0∞) (C : ℝ), (∀ r, ENNReal.ofReal |a r| ≤ m r * ENNReal.ofReal C) → (∑' r, ((c r).natAbs : ℝ≥0∞) * m r) < ∞ → Summable (fun r => (c r : ℝ) * a r) ∧ ENNReal.ofReal |∑' r, (c r : ℝ) * a r| ≤ ENNReal.ofReal C * ∑' r, ((c r).natAbs : ℝ≥0∞) * m r`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
