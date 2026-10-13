# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1.single_chart-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-f939a87b7a/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1`
- Child key: `single_chart`
- Declaration: `Submission.lpf_tde_mcd_single_chart`
- Exact Lean type: `∀ (P Q n : ℕ) (Λ : (Eucl n →L[ℝ] Eucl P) → (Eucl P →L[ℝ] Eucl n)) (Φ : Eucl n → Eucl P) (Ω : Set (Eucl n)) (f : Eucl P → Eucl Q), ContinuousOn Λ {A : Eucl n →L[ℝ] Eucl P | Function.Injective A} → (∀ A : Eucl n →L[ℝ] Eucl P, Function.Injective A → (Λ A).comp A = ContinuousLinearMap.id ℝ (Eucl n) ∧ ∀ v : Eucl P, ‖A (Λ A v)‖ ≤ ‖v‖) → IsOpen Ω → ContDiff ℝ 1 Φ → (∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω, ∀ w' ∈ Ω, c * ‖w - w'‖ ≤ ‖Φ w - Φ w'‖) → ∃ G : Eucl P → (Eucl P →L[ℝ] Eucl Q), Measurable G ∧ MeasurableSet (Φ '' Ω) ∧ ∀ x ∈ Φ '' Ω, ∃ w ∈ Ω, Φ w = x ∧ (∀ s : Eucl n, G x (fderiv ℝ Φ w s) = fderiv ℝ (f ∘ Φ) w s) ∧ ∀ v : Eucl P, ∃ s : Eucl n, ‖fderiv ℝ Φ w s‖ ≤ ‖v‖ ∧ G x v = fderiv ℝ (f ∘ Φ) w s`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.weighted_tangent_on_c1_chart-a1.chart_approximate_tangent-a1.fderiv_lower_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
