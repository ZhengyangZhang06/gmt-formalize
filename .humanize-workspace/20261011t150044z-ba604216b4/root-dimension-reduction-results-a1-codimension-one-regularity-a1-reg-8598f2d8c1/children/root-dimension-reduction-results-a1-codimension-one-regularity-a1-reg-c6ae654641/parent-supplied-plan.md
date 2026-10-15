# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1.smooth_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-c6ae654641/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.tangent_measure_ae-a1`
- Child key: `smooth_approx`
- Declaration: `Submission.codim1_rdo_dg_tma_smooth_approx`
- Exact Lean type: `∀ (P : ℕ) (f : Euclid P → ℝ) (R θ : ℝ), Continuous f → tsupport f ⊆ closedBall (0 : Euclid P) R → 0 < θ → ∃ g : Euclid P → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ closedBall (0 : Euclid P) (R + 1) ∧ ∀ x, |f x - g x| ≤ θ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
