# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.lattice_chain_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-def4bb7ee6/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `lattice_chain_im`
- Declaration: `Submission.dor_lmb_fcd_fr_lattice_chain_im`
- Exact Lean type: `∀ (P m : ℕ) (s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P))) (β : (Fin P → ℤ) × (Fin (m + 1) → Fin P) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.2) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (β p : ℝ) * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (fun k => EuclideanSpace.single (p.2 k) (1 : ℝ))) → IsIntegerMultiplicity T`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.face_geometry-a1`
- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.local_plane_tangent-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
