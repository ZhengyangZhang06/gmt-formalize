# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1.eventual_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-25ca54fba0/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1`
- Child key: `eventual_bounds`
- Declaration: `Submission.cbr_ci_bl_db_eventual_bounds`
- Exact Lean type: `∀ (n : ℕ) (m h H o : ℝ → ℝ≥0∞) (θ₀ η₁ : ℝ) (K : ℝ≥0∞), 0 < θ₀ → 0 < η₁ → K ≠ ∞ → (∀ r : ℝ, 0 < r → m r ≤ ENNReal.ofReal θ₀ * h r + K * o r) → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => m r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) → limsup (fun r : ℝ => H r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => o r / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ENNReal.ofReal (η₁ / (4 * θ₀)) * (unitBallVolume n * ENNReal.ofReal (r ^ n)) ≤ h r ∧ H r ≤ 2 * (unitBallVolume n * ENNReal.ofReal (r ^ n))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
