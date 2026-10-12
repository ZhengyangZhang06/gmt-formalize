# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.radial_first_variation-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T142930Z-d646011318/nodes/root-radial-first-variation-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root`
- Child key: `radial_first_variation`
- Declaration: `Submission.radial_first_variation`
- Exact Lean type: `∀ (n ℓ : ℕ) (V : RectifiableVarifold n ℓ) (U : Set (Ambient n ℓ)) (H : Ambient n ℓ → Ambient n ℓ) (h : Ambient n ℓ → ℝ) (γ : ℝ → ℝ) (ξ : Ambient n ℓ), (∀ᵐ x ∂V.weight, Module.finrank ℝ (V.tangentSpace x) = n) → IsOpen U → V.HasMeanCurvatureIn U H → ContDiffOn ℝ 1 h U → ContDiff ℝ 1 γ → IsTestField U (fun x ↦ (h x * γ ‖x - ξ‖) • (x - ξ)) → ∫ x in U, (h x * ((n : ℝ) * γ ‖x - ξ‖ + ‖x - ξ‖ * deriv γ ‖x - ξ‖ * (1 - V.normalRadialSq ξ x)) + γ ‖x - ξ‖ * inner ℝ (x - ξ) (V.tangentialGradient h x)) ∂V.weight = -∫ x in U, h x * γ ‖x - ξ‖ * inner ℝ (x - ξ) (H x) ∂V.weight`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
