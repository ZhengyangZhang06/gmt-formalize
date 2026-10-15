# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1.top_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-blowup-compactness-a1-codim-zero-a1-e6c9223733/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1.blowup_compactness-a1.codim_zero-a1`
- Child key: `top_density`
- Declaration: `Submission.dtc_bc_cz_top_density`
- Exact Lean type: `∀ (n : ℕ) (V : Set (Euclid n)) (X : GeometricCurrentOn V n), 0 < n → IsOpen V → IsIntegerMultiplicity X → ∃ g : Euclid n → ℤ, LocallyIntegrableOn (fun y => (g y : ℝ)) V volume ∧ ∀ ω : TestFormOn V n, X ω = ∫ y, (g y : ℝ) * (ω : DifferentialForm (Euclid n) n) y ⇑(EuclideanSpace.basisFun (Fin n) ℝ)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
