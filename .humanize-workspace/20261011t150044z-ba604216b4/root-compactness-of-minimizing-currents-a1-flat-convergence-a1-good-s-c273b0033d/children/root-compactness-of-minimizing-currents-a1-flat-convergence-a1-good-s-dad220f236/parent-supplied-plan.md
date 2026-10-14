# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1.liminf_le_seq-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-dad220f236/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1`
- Child key: `liminf_le_seq`
- Declaration: `Submission.cmc_fc_gs_aqf_liminf_le_seq`
- Exact Lean type: `∀ (μ : Measure ℝ) (a b t : ℝ), t ∈ Ioo a b → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (Ioo (t - h) t)) (𝓝[>] 0) ≤ liminf (fun n : ℕ => ((n : ℝ≥0∞) + 1) * (μ.restrict (Icc a b)) (Ioo (t - 1 / ((n : ℝ) + 1)) t)) atTop`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
