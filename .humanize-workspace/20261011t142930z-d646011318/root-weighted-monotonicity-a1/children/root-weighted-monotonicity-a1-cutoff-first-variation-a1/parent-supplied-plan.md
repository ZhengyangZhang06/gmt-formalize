# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.weighted_monotonicity-a1.cutoff_first_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-weighted-monotonicity-a1-cutoff-first-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.weighted_monotonicity-a1`
- Child key: `cutoff_first_variation`
- Declaration: `Submission.weighted_mono_cutoff_first_variation`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (ξ : Ambient n ℓ) (ρ : ℝ), IsFiniteMeasureOnCompacts V.weight → AEStronglyMeasurable (fun x ↦ (V.tangentSpace x).starProjection) V.weight → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → tsupport h ∩ closedBall ξ ρ ⊆ U → 0 < ρ → (∀ γ : ℝ → ℝ, ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight) → ∃ R A : ℝ, ρ < R ∧ AEStronglyMeasurable h (V.weight.restrict (closedBall ξ R)) ∧ AEStronglyMeasurable (V.normalRadialSq ξ) (V.weight.restrict (closedBall ξ R)) ∧ (∀ x ∈ closedBall ξ R, |h x| ≤ A ∧ |V.normalRadialSq ξ x| ≤ 1) ∧ IntegrableOn (fun x ↦ inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x)) (closedBall ξ R) V.weight ∧ ∀ (ε : ℝ) (φ : ℝ → ℝ), 0 < ε → (1 + ε) * ρ < R → ContDiff ℝ 1 φ → (∀ t, t ≤ 1 → φ t = 1) → (∀ t, 1 + ε ≤ t → φ t = 0) → ∀ τ, 0 < τ → τ ≤ ρ → (n : ℝ) * ∫ x, h x * φ (‖x - ξ‖ / τ) ∂V.weight + ∫ x, h x * (1 - V.normalRadialSq ξ x) * (‖x - ξ‖ / τ * deriv φ (‖x - ξ‖ / τ)) ∂V.weight + ∫ x, φ (‖x - ξ‖ / τ) * inner ℝ (x - ξ) (V.tangentialGradient h x + h x • H x) ∂V.weight = 0`

## Sibling prerequisites

- `root.weighted_monotonicity-a1.radial_test_field-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
