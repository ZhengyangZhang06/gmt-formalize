# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1.skeleton_point_on_open_face-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-15d4796914/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.face_replacement-a1.skeleton_decomposition-a1`
- Child key: `skeleton_point_on_open_face`
- Declaration: `Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face`
- Exact Lean type: `∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
