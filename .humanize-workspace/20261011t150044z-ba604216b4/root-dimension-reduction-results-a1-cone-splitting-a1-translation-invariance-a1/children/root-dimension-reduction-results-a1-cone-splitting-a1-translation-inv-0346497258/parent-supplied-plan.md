# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1.const_contraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-translation-inv-0346497258/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.translation_invariance-a1`
- Child key: `const_contraction`
- Declaration: `Submission.dimred_cs_ti_const_contraction_isTestForm`
- Exact Lean type: `∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)) (v : Euclid P), IsTestForm β → IsTestForm (fun z => ContinuousAlternatingMap.curryLeft (β z) v)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
