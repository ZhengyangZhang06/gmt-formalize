# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_and_tangent_cones-a1.density_usc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-and-tangent-cones-a1-density-usc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_and_tangent_cones-a1`
- Child key: `density_usc`
- Declaration: `Submission.dtc_density_usc`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → 0 < n → R.Represents T → R.HasLocallyBoundedMeanCurvature → ∃ Θ : Euclid P → ℝ, (∀ x ∈ U, HasMassDensity T x (Θ x)) ∧ UpperSemicontinuousOn Θ U`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.mass_eq_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
