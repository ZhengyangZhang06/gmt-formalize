# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1.product_support-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-1649cb1ddf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1`
- Child key: `product_support`
- Declaration: `Submission.dimred_cs_sos_mt_cc_product_support`
- Exact Lean type: `∀ (P k m' n' : ℕ) (E : Set (Euclid P)) (A : GeometricCurrentOn (univ : Set (Euclid P)) m') (RA : IMRep (univ : Set (Euclid P)) m') (B : GeometricCurrentOn (univ : Set (Euclid P)) n') (RB : IMRep (univ : Set (Euclid P)) n'), IsCompact E → IsCompact A.support → RA.Represents A → RB.Represents B → (∀ C : Set (Euclid P), MeasurableSet C → RB.measure C = ∫⁻ t in E, RA.measure ((fun y => t + y) ⁻¹' C) ∂μHE[k]) → B.support ⊆ Set.image2 (fun t y => t + y) E A.support`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1.support_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
