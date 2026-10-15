# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1.good_slice-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-flat-convergenc-8eb68d73ac/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.moving_blowups-a1.flat_convergence-a1`
- Child key: `good_slice`
- Declaration: `Submission.dimred_mbl_fc_good_slice`
- Exact Lean type: `∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), a < b → Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∃ (s : ℝ) (φ : ℕ → ℕ) (C : ℝ≥0∞), a < s ∧ s < b ∧ StrictMono φ ∧ C ≠ ∞ ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (φ j) (Ioo (s - h) s)) (𝓝[>] 0) ≤ C) ∧ ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μ (φ j) (Icc (s - δ) s) ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
