# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.localize-a1.extend_by_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-localize-a1-extend-by-zero-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.localize-a1`
- Child key: `extend_by_zero`
- Declaration: `Submission.dtc_extend_by_zero`
- Exact Lean type: `∀ (P n : ℕ) (U V K : Set (Euclid P)) (hVU : V ⊆ U) (X : GeometricCurrentOn V n) (R : IMRep V n), IsOpen U → IsOpen V → IsCompact K → K ⊆ V → R.Represents X → μHE[n] (R.carrier \ K) = 0 → ∃ Y : GeometricCurrentOn U n, Y.restrictDomain hVU = X ∧ Y.support ⊆ K ∧ IsCompact Y.support ∧ (BoundaryVanishes X → BoundaryVanishes Y) ∧ IsIntegerMultiplicity Y`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.localize-a1.imrep_transfer-a1`
- `root.density_and_tangent_cones-a1.localize-a1.imrep_current-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
