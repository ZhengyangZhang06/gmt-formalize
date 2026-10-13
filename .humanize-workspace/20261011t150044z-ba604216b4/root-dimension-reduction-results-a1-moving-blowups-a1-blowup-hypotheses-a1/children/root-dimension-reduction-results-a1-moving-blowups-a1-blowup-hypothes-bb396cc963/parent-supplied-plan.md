# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1.local_retraction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-blowup-hypothes-bb396cc963/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.blowup_hypotheses-a1`
- Child key: `local_retraction`
- Declaration: `Submission.dimred_mbl_bh_local_retraction`
- Exact Lean type: `∀ (P d : ℕ) (N : Set (Euclid P)) (x : Euclid P), IsEmbeddedSubmanifold 2 d N → x ∈ N → ∃ (δ : ℝ) (π : Euclid P → Euclid P), 0 < δ ∧ ContDiffOn ℝ 1 π (ball x δ) ∧ MapsTo π (ball x δ) N ∧ (∀ y ∈ N ∩ ball x δ, π y = y) ∧ ∀ η : ℝ, 0 < η → ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ ∀ y ∈ ball x s, ∀ z ∈ ball x s, ‖π y - π z‖ ≤ (1 + η) * ‖y - z‖`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
