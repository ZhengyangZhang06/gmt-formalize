# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.rescaled_integral_tendsto-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-weighted-tangent-on-c1-chart-a1-char-8b5bd63a08/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1`
- Child key: `rescaled_integral_tendsto`
- Declaration: `Submission.lpf_wtc_cat_rescaled_integral_tendsto`
- Exact Lean type: `∀ (Q n : ℕ) (Φ : Eucl n → Eucl Q) (Ω : Set (Eucl n)) (J : Eucl n → ℝ) (φ : Eucl Q → ℝ) (w : Eucl n), IsOpen Ω → w ∈ Ω → Continuous Φ → DifferentiableAt ℝ Φ w → (∃ c : ℝ, 0 < c ∧ ∀ v ∈ Ω, ∀ v' ∈ Ω, c * ‖v - v'‖ ≤ ‖Φ v - Φ v'‖) → Continuous J → Continuous φ → HasCompactSupport φ → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ v in Ω, J v * φ (r⁻¹ • (Φ v - Φ w))) (𝓝[>] 0) (𝓝 (∫ s, J w * φ (fderiv ℝ Φ w s)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
