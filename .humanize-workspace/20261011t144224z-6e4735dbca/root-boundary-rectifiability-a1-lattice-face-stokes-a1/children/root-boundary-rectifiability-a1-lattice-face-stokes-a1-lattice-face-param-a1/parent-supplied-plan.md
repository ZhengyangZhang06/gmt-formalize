# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.boundary_rectifiability-a1.lattice_face_stokes-a1.lattice_face_param-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-lattice-face-stokes-a1-lattice-face-param-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.boundary_rectifiability-a1.lattice_face_stokes-a1`
- Child key: `lattice_face_param`
- Declaration: `Submission.br_latticeFace_setIntegral_eq_cube`
- Exact Lean type: `∀ (P d : ℕ) (ρ : ℝ) (G : LatticeFaceIndex d P) (g : Eucl P → ℝ), ∫ x in latticeFace ρ G, g x ∂(μHE[d] : Measure (Eucl P)) = ∫ s in Set.Icc (0 : Fin d → ℝ) (fun _ => ρ), g (∑ l, (ρ * (G.1 l : ℝ)) • EuclideanSpace.single l (1 : ℝ) + ∑ j, s j • EuclideanSpace.single (G.2 j) (1 : ℝ))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
