# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1.lower_bound_transfer-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-79e916e4c9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1`
- Child key: `lower_bound_transfer`
- Declaration: `Submission.dimred_tr_mcr_tl_lower_bound_transfer`
- Exact Lean type: `∀ (P : ℕ) (μ : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (ws : ℕ → Euclid P) (w : Euclid P) (s : ℝ) (h : ℝ → ℝ≥0∞), (∀ K : Set (Euclid P), IsCompact K → limsup (fun j => μs j K) atTop ≤ μ K) → Tendsto ws atTop (𝓝 w) → Continuous h → (∀ᶠ j in atTop, ∀ ρ ∈ Ioo 0 s, h ρ ≤ μs j (ball (ws j) ρ)) → ∀ t ∈ Ioo 0 s, h t ≤ μ (ball w t)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
