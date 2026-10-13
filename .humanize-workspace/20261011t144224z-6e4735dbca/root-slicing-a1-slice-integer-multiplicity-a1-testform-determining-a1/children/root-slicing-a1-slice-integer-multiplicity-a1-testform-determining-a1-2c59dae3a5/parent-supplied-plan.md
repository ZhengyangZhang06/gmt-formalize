# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1.seq_dense-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-testform-determining-a1-2c59dae3a5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.testform_determining-a1`
- Child key: `seq_dense`
- Declaration: `Submission.slicing_im_td_countable_seq_dense`
- Exact Lean type: `∀ (P k : ℕ) (U K : Set (Eucl P)), IsCompact K → K ⊆ U → ∃ E : Set (TestFormOn U k), E.Countable ∧ ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ K → ∃ e : ℕ → TestFormOn U k, (∀ l, e l ∈ E) ∧ TestFormOnConverges e ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
