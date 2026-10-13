# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.measurable_chart_differential-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-tangential-differential-exists-a1-me-70f87b0655/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1`
- Child key: `measurable_chart_differential`
- Declaration: `Submission.lpf_tde_measurable_chart_differential`
- Exact Lean type: `∀ (P Q n : ℕ) (Φ : ℕ → Eucl n → Eucl P) (Ω : ℕ → Set (Eucl n)) (f : Eucl P → Eucl Q), (∀ j, IsOpen (Ω j)) → (∀ j, ContDiff ℝ 1 (Φ j)) → (∀ j, ∃ c : ℝ, 0 < c ∧ ∀ w ∈ Ω j, ∀ w' ∈ Ω j, c * ‖w - w'‖ ≤ ‖Φ j w - Φ j w'‖) → ∃ L : Eucl P → (Eucl P →L[ℝ] Eucl Q), StronglyMeasurable L ∧ (∀ x, x ∉ (⋃ j, Φ j '' Ω j) → L x = 0) ∧ ∀ x ∈ (⋃ j, Φ j '' Ω j), ∃ j, ∃ w ∈ Ω j, Φ j w = x ∧ (∀ s : Eucl n, L x (fderiv ℝ (Φ j) w s) = fderiv ℝ (f ∘ Φ j) w s) ∧ ∀ v : Eucl P, ∃ s : Eucl n, ‖fderiv ℝ (Φ j) w s‖ ≤ ‖v‖ ∧ L x v = fderiv ℝ (f ∘ Φ j) w s`

## Sibling prerequisites

- `root.lipschitz_pushforward_im-a1.tangential_differential_exists-a1.continuous_left_inverse-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
