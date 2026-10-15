# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.unit_current-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-1e9a471351/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1`
- Child key: `unit_current`
- Declaration: `Submission.dtc_bc_cz_unit_current`
- Exact Lean type: `∀ (n : ℕ) (c : ℤ), 0 < n → ∃ C : GeometricCurrentOn (univ : Set (Euclid n)) n, IsIntegerMultiplicity C ∧ ∀ ω : TestFormOn (univ : Set (Euclid n)) n, C ω = (c : ℝ) * ∫ y, (ω : DifferentialForm (Euclid n) n) y ⇑(EuclideanSpace.basisFun (Fin n) ℝ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
