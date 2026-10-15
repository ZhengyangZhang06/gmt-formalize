# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_chain-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-lattice-chain-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child key: `lattice_chain`
- Declaration: `Submission.fiw_tb_tda_lattice_chain`
- Exact Lean type: `∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ∀ β : LatticeFaceIndex (m + 1) (m + 1) → ℝ, (∀ F, ∃ k : ℤ, β F = k) → (∑' F, ENNReal.ofReal (|β F| * ρ ^ (m + 1))) < ∞ → ∃ (Pc : GeometricCurrentOn (univ : Set (Eucl (m + 1))) (m + 1)) (v : Eucl (m + 1) → ℝ), IsLatticeChain ρ β Pc ∧ IsIntegerMultiplicity Pc ∧ Integrable v ∧ (∀ F, ∀ᵐ x ∂((volume : Measure (Eucl (m + 1))).restrict (latticeFace ρ F)), v x = β F) ∧ ∀ ω : TestFormOn (univ : Set (Eucl (m + 1))) (m + 1), Pc ω = ∫ x, v x * (ω : DifferentialForm (Eucl (m + 1)) (m + 1)) x (fun i => EuclideanSpace.single i (1 : ℝ))`

## Sibling prerequisites

- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_cubes-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.density_current-a1`
- `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.locally_constant_im-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
