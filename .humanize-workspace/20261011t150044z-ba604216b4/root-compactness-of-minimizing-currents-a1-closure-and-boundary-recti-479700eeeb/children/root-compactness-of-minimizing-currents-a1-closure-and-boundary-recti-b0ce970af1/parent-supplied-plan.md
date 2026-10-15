# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1.lebesgue_error-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-b0ce970af1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.good_points-a1`
- Child key: `lebesgue_error`
- Declaration: `Submission.cbr_ci_gp_lebesgue_error_tendsto`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (τ : Euclid P → MultiVector P n), MeasurableSet M → μHE[n] M < ∞ → StronglyMeasurable τ → ∫⁻ x in M, ‖τ x‖ₑ ∂μHE[n] < ∞ → ∀ᵐ a ∂(μHE[n].restrict M), limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) < ∞ → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖τ x - τ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
