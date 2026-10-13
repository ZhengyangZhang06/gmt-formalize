# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.l1_duality-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-01aba3754f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `l1_duality`
- Declaration: `Submission.codim1_rdo_dg_bvc_l1_le_of_tests`
- Exact Lean type: `∀ (n : ℕ) (f : Euclid n → ℝ) (R A M : ℝ), Measurable f → (∀ z, |f z| ≤ M) → (∀ φ : Euclid n → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid n) R → (∀ z, |φ z| ≤ 1) → ∫ z, f z * φ z ≤ A) → ∫ z in ball (0 : Euclid n) R, |f z| ≤ A`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.smooth_indicator_approx-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
