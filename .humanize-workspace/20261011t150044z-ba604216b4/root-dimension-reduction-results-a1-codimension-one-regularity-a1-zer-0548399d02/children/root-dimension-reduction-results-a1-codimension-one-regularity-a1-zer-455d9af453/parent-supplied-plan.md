# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1.cauchy_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-codimension-one-regularity-a1-zer-455d9af453/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.codimension_one_regularity-a1.zero_scale_limit_plane-a1.bv_compactness-a1`
- Child key: `cauchy_limit`
- Declaration: `Submission.codim1_zsl_pc_cauchy_limit_set`
- Exact Lean type: `∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
