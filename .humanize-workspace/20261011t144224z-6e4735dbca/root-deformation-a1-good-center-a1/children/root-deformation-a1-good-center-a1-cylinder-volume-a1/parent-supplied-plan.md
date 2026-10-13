# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.good_center-a1.cylinder_volume-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-good-center-a1-cylinder-volume-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.good_center-a1`
- Child key: `cylinder_volume`
- Declaration: `Submission.dgc_cylinder_volume`
- Exact Lean type: `∀ (ι : Type) [Fintype ι] (J : Finset ι) (B : Set (EuclideanSpace ℝ J)), volume {a : EuclideanSpace ℝ ι | (∀ i, 0 ≤ a i ∧ a i ≤ 1) ∧ WithLp.toLp 2 (fun i : J => a i) ∈ B} ≤ volume B`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
