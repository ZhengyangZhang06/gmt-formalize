# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.tangent_projection_measurable-a1.opspace_aemeasurable_of_aesm-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-tangent-projection-measurab-364c5c8a71/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1.tangent_projection_measurable-a1`
- Child key: `opspace_aemeasurable_of_aesm`
- Declaration: `Submission.dtc_cone_opEuclid_aemeasurable_of_aesm`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable f μ → AEMeasurable f μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
