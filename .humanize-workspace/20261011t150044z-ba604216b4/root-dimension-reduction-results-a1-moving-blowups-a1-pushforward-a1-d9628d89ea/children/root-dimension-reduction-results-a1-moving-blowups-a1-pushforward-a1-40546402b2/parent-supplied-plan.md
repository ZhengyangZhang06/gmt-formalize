# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1.cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-40546402b2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.pf_integer-a1`
- Child key: `cutoff`
- Declaration: `Submission.dimred_mbl_pfi_c1_lipschitz_cutoff`
- Exact Lean type: `∀ (P : ℕ) (K O : Set (Euclid P)) (f : Euclid P → Euclid P), IsCompact K → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (g : Euclid P → Euclid P) (L : NNReal), ContDiff ℝ 1 g ∧ LipschitzWith L g ∧ ∀ x ∈ K, g x = f x ∧ fderiv ℝ g x = fderiv ℝ f x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
