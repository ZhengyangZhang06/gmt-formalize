# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1.local_inverse-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-90cc8d121d/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.stationary_cone_sheet_planar-a1`
- Child key: `local_inverse`
- Declaration: `Submission.idtp_ccd_scsp_local_inverse`
- Exact Lean type: `∀ (P : ℕ) (M : Set (Euclid P)) (p : Euclid P) (U : Set (Euclid P)) (F : Euclid P → Euclid 2), IsEmbeddedSubmanifold 1 2 M → p ∈ M → IsOpen U → p ∈ U → ContDiffOn ℝ 1 F U → (∀ v ∈ Submodule.span ℝ (tangentSpace M p), fderiv ℝ F p v = 0 → v = 0) → ∃ (O : Set (Euclid 2)) (N : Set (Euclid P)) (G : Euclid 2 → Euclid P), IsOpen O ∧ IsOpen N ∧ F p ∈ O ∧ p ∈ N ∧ N ⊆ U ∧ ContDiffOn ℝ 1 G O ∧ G '' O = M ∩ N ∧ (∀ w ∈ O, F (G w) = w) ∧ ∀ w ∈ O, tangentSpace M (G w) = Set.range (fderiv ℝ G w)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
