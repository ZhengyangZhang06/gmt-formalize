# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.cone-a1.euler_cartan-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-cone-a1-euler-cartan-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.cone-a1`
- Child key: `euler_cartan`
- Declaration: `Submission.dtc_cone_euler_cartan`
- Exact Lean type: `∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)) (y : Euclid P), DifferentiableAt ℝ β y → exteriorDerivative (fun z => ContinuousAlternatingMap.curryLeft (β z) z) y + ContinuousAlternatingMap.curryLeft (exteriorDerivative β y) y = ((m : ℝ) + 1) • β y + fderiv ℝ β y y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
