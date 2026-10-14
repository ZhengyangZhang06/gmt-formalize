# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1.frame_sign-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-slicing-a1-s-855be436ec/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.density_one_implies_regular-a1.limsup_mass_bound-a1.slicing-a1.slice_family-a1.wedge_orientation-a1`
- Child key: `frame_sign`
- Declaration: `Submission.dor_lmbsf_io_orientation_frame_sign`
- Exact Lean type: `∀ (P m : ℕ) (ζ : MultiVector P m) (Q : Submodule ℝ (Euclid P)) (ρ : Fin m → Euclid P), IsUnitOrientationOf ζ Q → Orthonormal ℝ ρ → (∀ j, ρ j ∈ Q) → (∀ β : Covector (Euclid P) m, ζ β = β ρ) ∨ ∀ β : Covector (Euclid P) m, ζ β = -β ρ`

## Sibling prerequisites

- `root.density_one_implies_regular-a1.epsilon_regularity-a1.graph_cycle_regular-a1.graph_orientation_jacobian-a1.covector_frame_det-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
