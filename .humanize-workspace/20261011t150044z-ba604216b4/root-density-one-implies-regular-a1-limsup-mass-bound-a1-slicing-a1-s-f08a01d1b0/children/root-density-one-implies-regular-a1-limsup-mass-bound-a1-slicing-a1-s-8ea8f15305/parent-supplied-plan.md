# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1.slice_plane_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-8ea8f15305/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.piece_slice_tangent-a1`
- Child key: `slice_plane_algebra`
- Declaration: `Submission.dor_lmbsf_pst_slice_plane_algebra`
- Exact Lean type: `∀ (m P : ℕ) (L : Euclid m →L[ℝ] Euclid P) (ℓ : Euclid m →L[ℝ] ℝ) (g : Euclid P), g ∈ LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P) → (∀ e : Euclid m, inner ℝ g (L e) = ℓ e) → (g = 0 ↔ ℓ = 0) ∧ LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ g)ᗮ = Submodule.map (L : Euclid m →ₗ[ℝ] Euclid P) (LinearMap.ker (ℓ : Euclid m →ₗ[ℝ] ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
