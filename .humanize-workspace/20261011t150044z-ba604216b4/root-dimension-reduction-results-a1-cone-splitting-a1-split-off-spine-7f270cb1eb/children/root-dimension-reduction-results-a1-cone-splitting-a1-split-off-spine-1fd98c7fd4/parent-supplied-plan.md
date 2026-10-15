# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.measure_comparison-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-1fd98c7fd4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1`
- Child key: `measure_comparison`
- Declaration: `Submission.dimred_cs_sos_mt_measure_comparison`
- Exact Lean type: `∀ (P j : ℕ) (S₁ S₂ : GeometricCurrentOn (univ : Set (Euclid P)) j) (R₁ R₂ : IMRep (univ : Set (Euclid P)) j) (W₀ B : Set (Euclid P)), R₁.Represents S₁ → R₂.Represents S₂ → IsOpen W₀ → IsOpen B → (S₁ - S₂).support ⊆ W₀ → W₀ ⊆ B → R₁.measure B + R₂.measure W₀ = R₂.measure B + R₁.measure W₀`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
