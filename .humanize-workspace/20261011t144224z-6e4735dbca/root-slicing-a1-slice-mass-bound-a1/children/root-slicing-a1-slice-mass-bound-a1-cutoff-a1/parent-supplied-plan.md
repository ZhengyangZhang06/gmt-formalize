# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-cutoff-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1`
- Child key: `cutoff`
- Declaration: `Submission.slicing_mb_cutoff`
- Exact Lean type: `∀ (t h ε : ℝ), 0 < h → 0 < ε → ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ (∀ s, 0 ≤ χ s ∧ χ s ≤ 1) ∧ (∀ s, s ≤ t - h → χ s = 1) ∧ (∀ s, t ≤ s → χ s = 0) ∧ (∀ s, |deriv χ s| ≤ (1 + ε) / h) ∧ (∀ s, s ∉ Ioo (t - h) t → deriv χ s = 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
