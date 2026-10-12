# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.constancy-a1.globalize-a1.pou_decomposition-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-constancy-a1-globalize-a1-pou-decomposition-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.constancy-a1.globalize-a1`
- Child key: `pou_decomposition`
- Declaration: `Submission.constancy_testFormOn_eq_finset_sum_subordinate`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Eucl P)) (ι : Type) (V : ι → Set (Eucl P)), (∀ i, IsOpen (V i)) → ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Eucl P) n) ⊆ ⋃ i, V i → ∃ (s : Finset ι) (η : ι → TestFormOn U n), (∀ i ∈ s, tsupport (η i : DifferentialForm (Eucl P) n) ⊆ V i) ∧ ω = ∑ i ∈ s, η i`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
