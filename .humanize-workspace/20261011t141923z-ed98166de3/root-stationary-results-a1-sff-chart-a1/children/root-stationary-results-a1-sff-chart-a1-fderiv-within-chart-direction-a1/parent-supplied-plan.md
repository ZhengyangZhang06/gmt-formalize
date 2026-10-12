# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.sff_chart-a1.fderiv_within_chart_direction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-chart-a1-fderiv-within-chart-direction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.sff_chart-a1`
- Child key: `fderiv_within_chart_direction`
- Declaration: `Submission.sff_fderivWithin_chart_direction`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)) (V : Set (Rn n)) (ψ : Rn n → Rn N) (f g : Rn N → (Rn N →L[ℝ] Rn N)) (x₀ : Rn n), V ∈ 𝓝 x₀ → ψ '' V ⊆ M → DifferentiableAt ℝ ψ x₀ → DifferentiableAt ℝ g (ψ x₀) → f =ᶠ[𝓝[M] ψ x₀] g → ∀ a : Rn n, fderivWithin ℝ f M (ψ x₀) (fderiv ℝ ψ x₀ a) = fderiv ℝ g (ψ x₀) (fderiv ℝ ψ x₀ a)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
