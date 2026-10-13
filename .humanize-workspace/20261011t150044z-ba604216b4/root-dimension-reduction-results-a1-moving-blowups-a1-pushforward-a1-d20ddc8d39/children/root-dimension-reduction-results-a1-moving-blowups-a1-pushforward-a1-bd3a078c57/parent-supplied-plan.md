# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_boundary-a1.c1_perturbation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-bd3a078c57/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_boundary-a1`
- Child key: `c1_perturbation`
- Declaration: `Submission.dimred_mbl_pfb_c1_compact_perturbation`
- Exact Lean type: `∀ (P : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → IsCompact K → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (φ : Euclid P → Euclid P) (V K' : Set (Euclid P)), IsOpen V ∧ K ⊆ V ∧ IsCompact K' ∧ K' ⊆ O ∧ ContDiff ℝ 1 φ ∧ (∀ x ∈ V, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x) ∧ ∀ x, x ∉ K' → φ x = x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
