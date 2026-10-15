# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.skeleton_cells-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-2535f2ddf8/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `skeleton_cells`
- Declaration: `Submission.dor_lmb_fcd_fr_skeleton_cells`
- Exact Lean type: `∀ (P m : ℕ) (K : Set (Euclid P)), m + 1 < P → IsCompact K → ∃ s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ⊆ cthickening (Real.sqrt P) K) ∧ IsClosed {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∧ ∀ᵐ x ∂(μHE[m + 1].restrict ({x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∩ K)), ∃ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.face_geometry-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
