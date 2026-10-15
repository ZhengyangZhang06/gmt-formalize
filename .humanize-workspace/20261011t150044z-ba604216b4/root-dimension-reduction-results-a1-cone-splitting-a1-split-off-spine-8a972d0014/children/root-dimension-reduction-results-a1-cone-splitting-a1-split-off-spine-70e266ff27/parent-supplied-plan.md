# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.carried_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-70e266ff27/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child key: `carried_transfer`
- Declaration: `Submission.dimred_cs_sos_mt_cm_carried_transfer`
- Exact Lean type: `∀ (P j : ℕ) (S₁ S₂ : GeometricCurrentOn (univ : Set (Euclid P)) j) (R₁ R₂ : IMRep (univ : Set (Euclid P)) j) (F : Set (Euclid P)), R₁.Represents S₁ → R₂.Represents S₂ → IsClosed F → R₂.measure Fᶜ = 0 → (S₁ - S₂).support ⊆ F → R₁.measure Fᶜ = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
