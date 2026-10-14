# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_face_stokes-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-face-stokes-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1`
- Child key: `lattice_face_stokes`
- Declaration: `Submission.br_lattice_face_stokes`
- Exact Lean type: `∀ (P m : ℕ) (ρ : ℝ), 0 < ρ → ∀ (F : LatticeFaceIndex (m + 1) P) (ω : DifferentialForm (Eucl P) m), IsSmoothForm ω → latticeFaceAction ρ F (exteriorDerivative ω) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (latticeFaceAction ρ (F.1 + Pi.single (F.2 i) 1, (Fin.succAboveOrderEmb i).trans F.2) ω - latticeFaceAction ρ (F.1, (Fin.succAboveOrderEmb i).trans F.2) ω)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
