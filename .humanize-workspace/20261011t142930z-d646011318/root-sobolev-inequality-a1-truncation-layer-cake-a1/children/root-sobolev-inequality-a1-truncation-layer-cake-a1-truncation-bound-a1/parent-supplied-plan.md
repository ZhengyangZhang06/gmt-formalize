# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.sobolev_inequality-a1.truncation_layer_cake-a1.truncation_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-sobolev-inequality-a1-truncation-layer-cake-a1-truncation-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.sobolev_inequality-a1.truncation_layer_cake-a1`
- Child key: `truncation_bound`
- Declaration: `Submission.sobolev_truncation_superlevel_bound`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (C ε t : ℝ), IsFiniteMeasureOnCompacts V.weight → LocallyIntegrableOn H U V.weight → 0 ≤ C → (∀ g : Ambient n ℓ → ℝ, ContDiffOn ℝ 1 g U → HasCompactSupport g → tsupport g ⊆ U → (∀ x, 0 ≤ g x) → ∫ x in {x | 1 ≤ g x}, g x ∂V.weight ≤ C * (∫ x, g x ∂V.weight) ^ (n : ℝ)⁻¹ * ∫ x, (‖V.tangentialGradient g x‖ + g x * ‖H x‖) ∂V.weight) → ContDiff ℝ 1 h → HasCompactSupport h → tsupport h ⊆ U → (∀ x, 0 ≤ h x) → Integrable (fun x ↦ ‖V.tangentialGradient h x‖) V.weight → ContDiff ℝ 1 γ → Monotone γ → (∀ s, 0 ≤ γ s ∧ γ s ≤ 1) → (∀ s, s ≤ 0 → γ s = 0) → 0 < ε → (∀ s, ε ≤ s → γ s = 1) → 0 ≤ t → V.weight.real {x | t + ε < h x} ≤ C * (V.weight.real {x | t < h x}) ^ (n : ℝ)⁻¹ * ((∫ x, deriv γ (h x - t) * ‖V.tangentialGradient h x‖ ∂V.weight) + ∫ x in {x | t < h x}, ‖H x‖ ∂V.weight)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
