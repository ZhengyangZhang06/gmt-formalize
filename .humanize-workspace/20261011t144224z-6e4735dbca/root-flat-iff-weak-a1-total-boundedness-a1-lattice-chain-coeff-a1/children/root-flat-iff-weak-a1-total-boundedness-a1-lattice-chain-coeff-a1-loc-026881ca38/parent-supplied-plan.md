# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.local_isolating_form-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1-loc-026881ca38/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- Child key: `local_isolating_form`
- Declaration: `Submission.fiw_tb_lcc_local_isolating_form`
- Exact Lean type: `∀ (n N : ℕ) (ρ : ℝ) (F₀ : LatticeFaceIndex n N) (x : Eucl N) (W : Set (Eucl N)), 0 < ρ → x ∈ latticeFace ρ F₀ → IsOpen W → x ∈ W → ∃ ω : TestFormOn (univ : Set (Eucl N)) n, tsupport (ω : DifferentialForm (Eucl N) n) ⊆ W ∧ (∀ F : LatticeFaceIndex n N, F ≠ F₀ → latticeFaceAction ρ F (ω : DifferentialForm (Eucl N) n) = 0) ∧ 0 < latticeFaceAction ρ F₀ (ω : DifferentialForm (Eucl N) n)`

## Sibling prerequisites

- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.coord_covector-a1`
- `root.isoperimetric-a1.lattice_mass_lower_bound-a1.face_cutoff-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.face_integral_pos-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
