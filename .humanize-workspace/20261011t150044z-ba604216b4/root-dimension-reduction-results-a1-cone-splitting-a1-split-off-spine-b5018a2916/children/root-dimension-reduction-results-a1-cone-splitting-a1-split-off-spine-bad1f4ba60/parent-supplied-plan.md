# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1.cube_geometry-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-bad1f4ba60/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1`
- Child key: `cube_geometry`
- Declaration: `Submission.dimred_cs_sos_mt_cc_cube_sum_geometry`
- Exact Lean type: `∀ (P k : ℕ) (g : Fin k → Euclid P) (r : ℝ) (K : Set (Euclid P)), Orthonormal ℝ g → IsCompact K → K ⊆ ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P)) → IsCompact {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} ∧ IsCompact (Set.image2 (fun t y => t + y) {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} K) ∧ Set.image2 (fun t y => t + y) {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} K ⊆ {x | ∀ i, |inner ℝ (g i) x| ≤ r} ∩ (Submodule.span ℝ (Set.range g))ᗮ.starProjection ⁻¹' K`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
