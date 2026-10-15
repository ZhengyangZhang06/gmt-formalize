# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-flat-convergenc-b377ee2e50/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.good_slice-a1`
- Child key: `ae_quotient_finite`
- Declaration: `Submission.dimred_mbl_fc_gs_ae_quotient_finite`
- Exact Lean type: `∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo a b → liminf (fun j => liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ j (Ioo (t - h) t)) (𝓝[>] 0)) atTop ≠ ∞`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
