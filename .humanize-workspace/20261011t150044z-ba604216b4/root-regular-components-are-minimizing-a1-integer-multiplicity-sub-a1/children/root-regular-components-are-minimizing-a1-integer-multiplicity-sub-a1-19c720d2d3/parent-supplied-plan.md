# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1.difference_data-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1-19c720d2d3/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1`
- Child key: `difference_data`
- Declaration: `Submission.regcomp_ims_difference_data`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), (∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x) → ∃ (C : Set (Euclid P)) (θ : Euclid P → ℕ) (ξ : Euclid P → MultiVector P n), MeasurableSet C ∧ C ⊆ R₁.carrier ∪ R₂.carrier ∧ Measurable θ ∧ (∀ x ∈ C, 0 < θ x) ∧ (∀ x ∈ C, θ x ≤ R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) ∧ AEStronglyMeasurable ξ (μHE[n].restrict C) ∧ (∀ᵐ x ∂(μHE[n].restrict (C ∩ R₁.carrier)), ξ x = R₁.orient x ∨ ξ x = -R₁.orient x) ∧ (∀ᵐ x ∂(μHE[n].restrict (C \ R₁.carrier)), ξ x = R₂.orient x ∨ ξ x = -R₂.orient x) ∧ ∀ᵐ x ∂μHE[n], C.indicator (fun y => (θ y : ℝ) • ξ y) x = R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x - R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
