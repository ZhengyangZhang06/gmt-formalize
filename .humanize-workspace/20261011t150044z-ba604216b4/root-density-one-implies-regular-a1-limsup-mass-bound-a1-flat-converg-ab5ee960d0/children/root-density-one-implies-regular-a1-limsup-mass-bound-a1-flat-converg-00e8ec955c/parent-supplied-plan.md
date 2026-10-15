# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1.local_plane_tangent-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-flat-converg-00e8ec955c/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.flat_convergence-a1.deformation-a1.face_replacement-a1`
- Child key: `local_plane_tangent`
- Declaration: `Submission.dor_lmb_fcd_fr_local_plane_tangent`
- Exact Lean type: `∀ (P n : ℕ) (N : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (r : ℝ), Module.finrank ℝ V = n → 0 < r → (∀ y ∈ Metric.ball x r, y ∈ N ↔ y - x ∈ V) → HasApproximateTangentSpaceAt n N x V`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
