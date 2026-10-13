# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1.ball_cone_measurable-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-cdbbfaed48/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.rectifiable_criterion-a1`
- Child key: `ball_cone_measurable`
- Declaration: `Submission.codim1_rdo_dg_rc_ball_cone_measurable`
- Exact Lean type: `∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (α q : ℝ), SFinite μ → Measurable ν → Measurable (fun x : Euclid (m + 1) => μ (closedBall x q)) ∧ Measurable (fun x : Euclid (m + 1) => μ ({z | α * ‖z - x‖ ≤ |inner ℝ (z - x) (ν x)|} ∩ closedBall x q))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
