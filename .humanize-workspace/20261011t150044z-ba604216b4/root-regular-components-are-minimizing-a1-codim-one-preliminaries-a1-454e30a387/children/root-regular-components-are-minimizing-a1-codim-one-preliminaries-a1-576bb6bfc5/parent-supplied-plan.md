# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.isolated_carrier_point-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-codim-one-preliminaries-a1-576bb6bfc5/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1`
- Child key: `isolated_carrier_point`
- Declaration: `Submission.regcomp_cop_zdr_isolated_carrier_point`
- Exact Lean type: `∀ (P : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U 0) (R : IMRep U 0) (y : Euclid P) (r c : ℝ), R.Represents T → 0 < r → ball y r ⊆ U → c ≠ 0 → (∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ ball y r → T ω = c * (ω : DifferentialForm (Euclid P) 0) y (fun i => i.elim0)) → y ∈ R.carrier ∧ R.carrier ∩ ball y r ⊆ {y}`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.zero_dim_minimizing_trivial-a1.imrep_zero_structure-a1`
- `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.unit_orientation_zero-a1`
- `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.isolated_point_integral-a1`
- `root.regular_components_are_minimizing-a1.codim_one_preliminaries-a1.zero_dim_regular_empty-a1.bump_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
