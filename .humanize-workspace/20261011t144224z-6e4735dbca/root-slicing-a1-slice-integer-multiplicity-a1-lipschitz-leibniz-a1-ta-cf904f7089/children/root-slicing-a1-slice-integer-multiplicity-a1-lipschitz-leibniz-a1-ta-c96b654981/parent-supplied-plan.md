# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.coefficient_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-c96b654981/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1`
- Child key: `coefficient_field`
- Declaration: `Submission.slicing_im_ll_twl_coefficient_field`
- Exact Lean type: `∀ (P n : ℕ) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (A : Set (Eucl P)) (Y : Eucl P → Eucl P), IsOpen Ω → ContDiff ℝ 1 Φ → (∃ K : ℝ≥0, LipschitzOnWith K Φ Ω) → (∃ κ : ℝ, 0 < κ ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, κ * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → A ⊆ Φ '' Ω → NullMeasurableSet A (μHE[n] : Measure (Eucl P)) → IntegrableOn Y A (μHE[n] : Measure (Eucl P)) → (∀ᵐ x ∂((μHE[n] : Measure (Eucl P)).restrict A), ∀ w ∈ Ω, Φ w = x → Y x ∈ LinearMap.range (fderiv ℝ Φ w).toLinearMap) → ∃ c : Eucl n → Eucl n, IntegrableOn c Ω (volume : Measure (Eucl n)) ∧ (∀ w, w ∉ Ω ∩ Φ ⁻¹' A → c w = 0) ∧ ∀ᵐ w ∂((volume : Measure (Eucl n)).restrict (Ω ∩ Φ ⁻¹' A)), fderiv ℝ Φ w (c w) = Real.sqrt (Matrix.of fun i j => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i 1)) (fderiv ℝ Φ w (EuclideanSpace.single j 1))).det • Y (Φ w)`

## Sibling prerequisites

- `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangential_weak_limit-a1.chart_integral_eq-a1`
- `root.lipschitz_pushforward_im-a1.chart_chain_rule-a1.ae_pullback-a1`
- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.continuous_left_inverse-a1`
- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
