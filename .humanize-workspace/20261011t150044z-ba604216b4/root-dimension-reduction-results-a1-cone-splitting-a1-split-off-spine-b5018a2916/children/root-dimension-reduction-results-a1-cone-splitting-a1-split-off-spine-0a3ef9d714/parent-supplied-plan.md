# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1.cycle_algebra-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-0a3ef9d714/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1`
- Child key: `cycle_algebra`
- Declaration: `Submission.dimred_cs_sos_mt_cc_cycle_of_boundary_eq`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (B : GeometricCurrentOn U (n + 1 + 1)) (T₁ T₂ : GeometricCurrentOn U (n + 1)) (p : ℕ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U (n + 1), B.boundary ω = T₂ ω + (-1 : ℝ) ^ p * T₁ ω) → ∃ Z E' : GeometricCurrentOn U (n + 1), IsIntegerMultiplicity Z ∧ BoundaryVanishes Z ∧ Z.support ⊆ B.support ∧ E'.mass ≤ T₂.mass ∧ ∀ ω : TestFormOn U (n + 1), Z ω = T₁ ω + E' ω`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.cube_cycle-a1.support_smul_boundary-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
