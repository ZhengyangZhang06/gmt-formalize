# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1.pullback_cutoff-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-8e008058fe/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.extension-a1`
- Child key: `pullback_cutoff`
- Declaration: `Submission.dimred_mbl_pf_ext_pullback_cutoff`
- Exact Lean type: `∀ (P n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) n), Continuous ω → IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → ∃ h : Euclid P → Covector (Euclid P) n, Continuous h ∧ HasCompactSupport h ∧ ∀ x ∈ K, h x = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
