# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1.threshold_limit-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-measure-cl-64c33e67d4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.measure_class_reduction-a1`
- Child key: `threshold_limit`
- Declaration: `Submission.dimred_tr_mcr_threshold_limit`
- Exact Lean type: `∀ (P n : ℕ) (Λ c : ℝ) (μ : Measure (Euclid P)) (μs : ℕ → Measure (Euclid P)) (ws : ℕ → Euclid P) (w : Euclid P), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ (j : ℕ) (K : Set (Euclid P)), IsCompact K → μs j K ≠ ∞) → (∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ closedBall 0 2 → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * μ (ball y ρ)) (Ioo 0 R)) → (∀ (j : ℕ) (y : Euclid P) (R : ℝ), closedBall y R ⊆ closedBall 0 2 → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * μs j (ball y ρ)) (Ioo 0 R)) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(μs j)) atTop (𝓝 (∫ x, f x ∂μ))) → Tendsto ws atTop (𝓝 w) → ‖w‖ < 2 → (∀ j, c ≤ (limsup (fun ρ : ℝ => μs j (ball (ws j) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → c ≤ (limsup (fun ρ : ℝ => μ (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.convergence_tools-a1.portmanteau-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
