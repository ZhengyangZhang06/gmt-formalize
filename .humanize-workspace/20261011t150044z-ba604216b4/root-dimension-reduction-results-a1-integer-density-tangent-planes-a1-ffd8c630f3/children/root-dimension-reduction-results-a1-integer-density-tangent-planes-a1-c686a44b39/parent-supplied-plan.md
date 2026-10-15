# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1.mult_const-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-c686a44b39/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.sheet_first_variation-a1`
- Child key: `mult_const`
- Declaration: `Submission.idtp_ccd_sfv_mult_ae_eq_density`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (p : Euclid P) (ρ : ℝ) (k : ℕ), IsOpen U → R.Represents T → (∀ y ∈ T.support, y ∈ ball p ρ → HasMassDensity T y k) → (∀ᵐ x ∂R.measure, x ∈ ball p ρ → R.mult x = k) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ ball p ρ)), R.mult x = k`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
