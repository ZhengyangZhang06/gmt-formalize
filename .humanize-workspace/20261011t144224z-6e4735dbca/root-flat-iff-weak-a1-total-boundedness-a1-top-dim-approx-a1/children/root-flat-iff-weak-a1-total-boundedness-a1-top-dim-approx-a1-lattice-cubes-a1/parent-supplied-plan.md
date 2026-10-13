# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1.lattice_cubes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-top-dim-approx-a1-lattice-cubes-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.top_dim_approx-a1`
- Child key: `lattice_cubes`
- Declaration: `Submission.fiw_tb_tda_lattice_cubes`
- Exact Lean type: `∀ (m : ℕ) (ρ : ℝ), 0 < ρ → (∀ (F : LatticeFaceIndex (m + 1) (m + 1)) (j : Fin (m + 1)), F.2 j = j) ∧ (∀ F : LatticeFaceIndex (m + 1) (m + 1), latticeFace ρ F = {x : Eucl (m + 1) | ∀ i, ρ * (F.1 i : ℝ) ≤ x i ∧ x i ≤ ρ * ((F.1 i : ℝ) + 1)}) ∧ (∀ F : LatticeFaceIndex (m + 1) (m + 1), MeasurableSet (latticeFace ρ F)) ∧ (∀ F : LatticeFaceIndex (m + 1) (m + 1), volume (latticeFace ρ F) = ENNReal.ofReal (ρ ^ (m + 1))) ∧ (∀ F : LatticeFaceIndex (m + 1) (m + 1), ∀ x ∈ latticeFace ρ F, ∀ y ∈ latticeFace ρ F, dist x y ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * ρ) ∧ (∀ᵐ x ∂(volume : Measure (Eucl (m + 1))), ∀ (i : Fin (m + 1)) (k : ℤ), x i ≠ ρ * k) ∧ (∀ g : Eucl (m + 1) → ℝ≥0∞, ∫⁻ x, g x = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫⁻ x in latticeFace ρ F, g x) ∧ ∀ f : Eucl (m + 1) → ℝ, Integrable f → ∫ x, f x = ∑' F : LatticeFaceIndex (m + 1) (m + 1), ∫ x in latticeFace ρ F, f x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
