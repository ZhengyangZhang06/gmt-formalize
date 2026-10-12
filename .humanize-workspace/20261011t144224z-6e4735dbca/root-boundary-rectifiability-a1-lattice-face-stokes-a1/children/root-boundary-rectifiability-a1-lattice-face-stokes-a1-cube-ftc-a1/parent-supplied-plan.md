# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_face_stokes-a1.cube_ftc-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-face-stokes-a1-cube-ftc-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.lattice_face_stokes-a1`
- Child key: `cube_ftc`
- Declaration: `Submission.br_cube_integral_fderiv_eq_faces`
- Exact Lean type: `∀ (n : ℕ) (ρ : ℝ), 0 ≤ ρ → ∀ (φ : (Fin (n + 1) → ℝ) → ℝ), ContDiff ℝ 1 φ → ∀ (i : Fin (n + 1)), ∫ s in Set.Icc (0 : Fin (n + 1) → ℝ) (fun _ => ρ), fderiv ℝ φ s (Pi.single i 1) = ∫ s in Set.Icc (0 : Fin n → ℝ) (fun _ => ρ), (φ (Fin.insertNth i ρ s) - φ (Fin.insertNth i 0 s))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
