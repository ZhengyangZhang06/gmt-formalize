# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1.coord_plane_orientation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-24aa912e6a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.polyhedral_im-a1`
- Child key: `coord_plane_orientation`
- Declaration: `Submission.dimred_mbl_dtfrpi_coord_plane_orientation`
- Exact Lean type: `∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
