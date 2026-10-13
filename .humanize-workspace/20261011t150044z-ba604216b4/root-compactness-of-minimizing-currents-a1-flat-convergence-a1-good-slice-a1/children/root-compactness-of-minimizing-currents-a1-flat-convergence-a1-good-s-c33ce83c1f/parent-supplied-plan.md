# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1.helly_no_concentration-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-good-s-c33ce83c1f/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.flat_convergence-a1.good_slice-a1`
- Child key: `helly_no_concentration`
- Declaration: `Submission.cmc_fc_gs_helly_no_concentration`
- Exact Lean type: `∀ (μ : ℕ → Measure ℝ) (a b : ℝ) (Λ : ℝ≥0∞), Λ ≠ ∞ → (∀ j, μ j (Icc a b) ≤ Λ) → ∃ (φ : ℕ → ℕ) (N : Set ℝ), StrictMono φ ∧ N.Countable ∧ ∀ s ∈ Ioo a b, s ∉ N → ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, μ (φ j) (Icc (s - δ) s) ≤ ε`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
