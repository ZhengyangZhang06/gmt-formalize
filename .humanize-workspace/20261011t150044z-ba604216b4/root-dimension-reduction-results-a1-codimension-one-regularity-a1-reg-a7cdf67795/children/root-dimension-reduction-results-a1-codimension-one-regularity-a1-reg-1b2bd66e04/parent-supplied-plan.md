# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1.fast_cauchy_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-reg-1b2bd66e04/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.region_density_one-a1.de_giorgi-a1.bv_compactness-a1`
- Child key: `fast_cauchy_limit`
- Declaration: `Submission.codim1_rdo_dg_bvc_limit_of_fast_cauchy`
- Exact Lean type: `∀ (n : ℕ) (Gs : ℕ → Set (Euclid n)), (∀ j, MeasurableSet (Gs j)) → (∀ i : ℕ, volume (symmDiff (Gs (i + 1)) (Gs i) ∩ ball (0 : Euclid n) ((i : ℝ) + 1)) ≤ (2⁻¹ : ℝ≥0∞) ^ i) → ∃ F₀ : Set (Euclid n), MeasurableSet F₀ ∧ ∀ R : ℝ, Tendsto (fun j => volume (symmDiff (Gs j) F₀ ∩ ball (0 : Euclid n) R)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
