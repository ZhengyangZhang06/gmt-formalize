# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_boundary_im-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-boundary-im-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1`
- Child key: `lattice_boundary_im`
- Declaration: `Submission.br_lattice_chain_boundary_isIntegerMultiplicity`
- Exact Lean type: `∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (β : LatticeFaceIndex (m + 1) P → ℤ) (Pc : GeometricCurrentOn (univ : Set (Eucl P)) (m + 1)), IsLatticeChain ρ (fun F => (β F : ℝ)) Pc → IsIntegerMultiplicity Pc.boundary`

## Sibling prerequisites

- `root.boundary_rectifiability-a1.lattice_face_stokes-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
