# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1.face_integral_pos-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-total-boundedness-a1-lattice-chain-coeff-a1-fac-f1c15dad9e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.flat_iff_weak-a1.total_boundedness-a1.lattice_chain_coeff-a1`
- Child key: `face_integral_pos`
- Declaration: `Submission.fiw_tb_lcc_face_integral_pos`
- Exact Lean type: `∀ (n N : ℕ) (ρ : ℝ) (F : LatticeFaceIndex n N) (g : Eucl N → ℝ) (p : Eucl N), 0 < ρ → Continuous g → (∀ x, 0 ≤ g x) → 0 < g p → (∀ i : Fin N, (i ∈ range F.2 → ρ * (F.1 i : ℝ) < p i ∧ p i < ρ * ((F.1 i : ℝ) + 1)) ∧ (i ∉ range F.2 → p i = ρ * (F.1 i : ℝ))) → 0 < ∫ x in latticeFace ρ F, g x ∂(μHE[n] : Measure (Eucl N))`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1.lattice_face_param-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
