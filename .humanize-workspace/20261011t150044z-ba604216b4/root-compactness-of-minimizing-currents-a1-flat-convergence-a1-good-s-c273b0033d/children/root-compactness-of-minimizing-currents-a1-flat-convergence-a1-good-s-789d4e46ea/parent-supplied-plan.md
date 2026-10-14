# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1.ae_seq_liminf_finite-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-789d4e46ea/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1`
- Child key: `ae_seq_liminf_finite`
- Declaration: `Submission.cmc_fc_gs_aqf_ae_seq_liminf_finite`
- Exact Lean type: `∀ (ν : ℕ → Measure ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, ν j univ ≤ Λ) → ∀ᵐ t ∂(volume : Measure ℝ), liminf (fun j => liminf (fun n : ℕ => ((n : ℝ≥0∞) + 1) * ν j (Ioo (t - 1 / ((n : ℝ) + 1)) t)) atTop) atTop ≠ ∞`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.ae_quotient_finite-a1.window_lintegral-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
