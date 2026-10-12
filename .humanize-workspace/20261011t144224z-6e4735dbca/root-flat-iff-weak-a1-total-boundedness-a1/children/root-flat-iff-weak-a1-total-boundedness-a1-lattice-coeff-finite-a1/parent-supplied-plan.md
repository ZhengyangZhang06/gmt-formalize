# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.lattice_coeff_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-coeff-finite-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1`
- Child key: `lattice_coeff_finite`
- Declaration: `Submission.fiw_tb_lattice_coeff_finite`
- Exact Lean type: `∀ (n N : ℕ) (ρ : ℝ), 0 < ρ → ∀ (Y : Set (Eucl N)), Bornology.IsBounded Y → ∀ A : ℝ, {β : LatticeFaceIndex n N → ℝ | (∀ F, ∃ k : ℤ, β F = k) ∧ ∀ F, β F ≠ 0 → latticeFace ρ F ⊆ Y ∧ |β F| ≤ A}.Finite`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
