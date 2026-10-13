# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.tilt_excess_decay-a1.lp_monotonicity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142321Z-faafe12087/nodes/root-tilt-excess-decay-a1-lp-monotonicity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.tilt_excess_decay-a1`
- Child key: `lp_monotonicity`
- Declaration: `Submission.ted_lp_monotonicity`
- Exact Lean type: `∀ (n ℓ : ℕ), 1 ≤ n → ∀ p : ℝ, (n : ℝ) < p → ∀ (U : Set (Amb n ℓ)), IsOpen U → ∀ (V : RectifiableVarifold n ℓ U) (H : Amb n ℓ → Amb n ℓ), V.HasGeneralizedMeanCurvature H → ∀ (y : Amb n ℓ) (R S Λ : ℝ), 0 < R → R < S → 0 < Λ → closedBall y S ⊆ U → ∫⁻ x in closedBall y S, ‖H x‖ₑ ^ p ∂V.weight < ⊤ → V.scaledLpNorm H p y R ≤ ENNReal.ofReal ((p - n) / (4 * p) * Λ) → ∃ F : ℝ → ℝ, (∀ r : ℝ, 0 < r → r ≤ R → Real.exp (-Λ) ≤ F r ∧ F r ≤ Real.exp Λ ∧ |F r - 1| ≤ Real.exp (Λ / 2) / 2 * Λ * (r / R) ^ (1 - (n : ℝ) / p) ∧ (Λ ≤ 1 → |F r - 1| ≤ Λ * (r / R) ^ (1 - (n : ℝ) / p))) ∧ ∀ s r : ℝ, 0 < s → s ≤ r → r ≤ R → F s * ((V.weight (closedBall y s)).toReal / s ^ n) + (F s - 1) ≤ F r * ((V.weight (closedBall y r)).toReal / r ^ n) + (F r - 1)`

## Sibling prerequisites

- `root.tilt_excess_decay-a1.tangent_plane_facts-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
