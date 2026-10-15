# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1.box_cancellation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-cone-splitting-a1-split-off-spine-cfd4771394/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.cone_splitting-a1.split_off_spine-a1.minimality_transfer-a1.competitor_mass-a1`
- Child key: `box_cancellation`
- Declaration: `Submission.dimred_cs_sos_mt_cm_box_cancellation`
- Exact Lean type: `∀ (P m : ℕ) (S₀ S₀' : GeometricCurrentOn (univ : Set (Euclid P)) m) (R₀ R₀' : IMRep (univ : Set (Euclid P)) m) (W₀ B : Set (Euclid P)) (a b e : ℝ≥0∞), R₀.Represents S₀ → R₀'.Represents S₀' → IsOpen W₀ → IsOpen B → Bornology.IsBounded B → (S₀' - S₀).support ⊆ W₀ → W₀ ⊆ B → b ≤ a → a ≠ ∞ → a * R₀.measure B ≤ (a - b) * R₀.measure B + b * R₀'.measure B + e → b * S₀.massOn W₀ ≤ b * S₀'.massOn W₀ + e`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
