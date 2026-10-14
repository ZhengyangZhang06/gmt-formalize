# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.faces_meeting_compact_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-fac-f3d25200d4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Child key: `faces_meeting_compact_finite`
- Declaration: `Submission.cmcdtfrsd_faces_meeting_compact_finite`
- Exact Lean type: `∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
