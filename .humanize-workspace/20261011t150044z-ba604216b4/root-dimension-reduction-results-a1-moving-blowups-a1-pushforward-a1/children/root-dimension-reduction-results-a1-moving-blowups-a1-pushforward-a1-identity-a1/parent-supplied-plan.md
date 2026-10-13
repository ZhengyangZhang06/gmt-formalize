# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-pushforward-a1-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1`
- Child key: `identity`
- Declaration: `Submission.dimred_mbl_pf_pushforward_eq_self_of_fix`
- Exact Lean type: `∀ (P n : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P) (Y Z : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsOpen O → ContDiffOn ℝ 1 f O → R.Represents Y → Y.support ⊆ O → (∀ y ∈ Y.support, f y = y) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → Z = Y`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.carrier_facts-a1`
- `root.dimension_reduction_results-a1.moving_blowups-a1.pushforward-a1.orient_comp-a1`
- `root.density_one_implies_regular-a1.mean_curvature_monotonicity-a1.approx_tangent_in_tangent_space-a1.blowup_points-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
