# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.top_density-a1.finite_ac_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-dad2ea0971/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.weight_ge_one-a1.top_density-a1`
- Child key: `finite_ac_density`
- Declaration: `Submission.cbr_ci_pw_td_finite_ac_density`
- Exact Lean type: `∀ (n : ℕ) (μ : Measure (Euclid n)) (h : Euclid n → ℝ), μ univ < ∞ → μ ≪ volume → AEStronglyMeasurable h μ → (∀ᵐ y ∂μ, |h y| ≤ 1) → ∃ u : Euclid n → ℝ, Integrable u ∧ ∫ y, |u y| ≤ (μ univ).toReal ∧ ∀ g : Euclid n → ℝ, ∫ y, g y * h y ∂μ = ∫ y, u y * g y`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
