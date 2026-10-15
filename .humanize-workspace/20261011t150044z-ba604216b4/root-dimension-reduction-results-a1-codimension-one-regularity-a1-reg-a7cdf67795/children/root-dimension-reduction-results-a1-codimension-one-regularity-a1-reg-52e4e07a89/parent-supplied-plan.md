# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.smooth_indicator_approx-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-52e4e07a89/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `smooth_indicator_approx`
- Declaration: `Submission.codim1_rdo_dg_bvc_smooth_indicator_approx`
- Exact Lean type: `∀ (n : ℕ) (P : Set (Euclid n)) (R η : ℝ), MeasurableSet P → P ⊆ ball (0 : Euclid n) R → 0 < η → ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ ball (0 : Euclid n) R ∧ (∀ z, 0 ≤ ψ z ∧ ψ z ≤ 1) ∧ ∫ z, |ψ z - P.indicator (fun _ => (1 : ℝ)) z| < η`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
