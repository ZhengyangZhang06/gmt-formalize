# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.isoperimetric-a1.lattice_mass_lower_bound-a1.isolating_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-isoperimetric-a1-lattice-mass-lower-bound-a1-isolating-form-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.isoperimetric-a1.lattice_mass_lower_bound-a1`
- Child key: `isolating_form`
- Declaration: `Submission.isoperimetric_lattice_face_isolating_form`
- Exact Lean type: `∀ (n N : ℕ) (ρ δ : ℝ) (F₀ : LatticeFaceIndex n N), 0 < ρ → 0 < δ → δ < 1 / 4 → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, ω ∈ massAdmissibleOn (univ : Set (Eucl N)) n univ ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ (ρ * (1 - 2 * δ)) ^ n ≤ latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n)`

## Sibling prerequisites

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1`
- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.box_measure-a1`
- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.face_cutoff-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
