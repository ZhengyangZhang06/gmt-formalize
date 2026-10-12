# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.variation_formulas-a1.param_integral_deriv-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-variation-formulas-a1-param-integral-deriv-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.variation_formulas-a1`
- Child key: `param_integral_deriv`
- Declaration: `Submission.variation_param_integral_deriv`
- Exact Lean type: `∀ (α X : Type) [MeasurableSpace α] [NormedAddCommGroup X] [NormedSpace ℝ X] (μ : Measure α) (S : Set α) (C : Set X) (e : α → X) (g : ℝ × X → ℝ), MeasurableSet S → μ S < ⊤ → IsCompact C → (∀ z ∈ S, e z ∈ C) → AEStronglyMeasurable e (μ.restrict S) → ((∀ x ∈ C, ContDiffAt ℝ 1 g (0, x)) → (∀ᶠ t in 𝓝 0, Integrable (fun z ↦ g (t, e z)) (μ.restrict S)) ∧ HasDerivAt (fun t ↦ ∫ z in S, g (t, e z) ∂μ) (∫ z in S, deriv (fun t ↦ g (t, e z)) 0 ∂μ) 0) ∧ ((∀ x ∈ C, ContDiffAt ℝ 2 g (0, x)) → (∀ᶠ t in 𝓝 0, HasDerivAt (fun s ↦ ∫ z in S, g (s, e z) ∂μ) (∫ z in S, deriv (fun s ↦ g (s, e z)) t ∂μ) t) ∧ HasDerivAt (fun t ↦ ∫ z in S, deriv (fun s ↦ g (s, e z)) t ∂μ) (∫ z in S, deriv (fun t ↦ deriv (fun s ↦ g (s, e z)) t) 0 ∂μ) 0)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
