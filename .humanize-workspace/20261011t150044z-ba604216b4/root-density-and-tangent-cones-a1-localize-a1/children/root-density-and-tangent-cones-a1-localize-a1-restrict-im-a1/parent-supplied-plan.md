# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.localize-a1.restrict_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-restrict-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.localize-a1`
- Child key: `restrict_im`
- Declaration: `Submission.dtc_restrictDomain_isIntegerMultiplicity`
- Exact Lean type: `∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n), IsOpen V → IsIntegerMultiplicity T → IsIntegerMultiplicity (T.restrictDomain hVU)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.approx_tangent_local-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
