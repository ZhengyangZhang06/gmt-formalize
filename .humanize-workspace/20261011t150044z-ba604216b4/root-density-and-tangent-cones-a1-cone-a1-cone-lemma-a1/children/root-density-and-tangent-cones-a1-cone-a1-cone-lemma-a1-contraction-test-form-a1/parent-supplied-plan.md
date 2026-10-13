# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1.contraction_test_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-cone-lemma-a1-contraction-test-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1.cone_lemma-a1`
- Child key: `contraction_test_form`
- Declaration: `Submission.dtc_cwv_euler_contraction_isTestForm`
- Exact Lean type: `∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), IsTestForm β → IsTestForm (fun z => ContinuousAlternatingMap.curryLeft (β z) z)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
