# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1.measure_subadditive-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-local-compari-9a7649a7ed/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.local_comparison-a1`
- Child key: `measure_subadditive`
- Declaration: `Submission.dtc_bc_lc_measure_le_add`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (X Y Z : GeometricCurrentOn U n) (RX RY RZ : IMRep U n) (c : ℝ), IsOpen U → |c| ≤ 1 → RX.Represents X → RY.Represents Y → RZ.Represents Z → (∀ ω : TestFormOn U n, Z ω = X ω + c * Y ω) → RZ.measure ≤ RX.measure + RY.measure`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
