# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1.glue_imrep-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1-940d0d04c2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.integer_multiplicity_sub-a1`
- Child key: `glue_imrep`
- Declaration: `Submission.regcomp_ims_imrep_of_signed_pieces`
- Exact Lean type: `∀ (P n : ℕ) (U C : Set (Euclid P)) (R₁ R₂ : IMRep U n) (θ : Euclid P → ℕ) (ξ : Euclid P → MultiVector P n), MeasurableSet C → C ⊆ R₁.carrier ∪ R₂.carrier → Measurable θ → (∀ x ∈ C, 0 < θ x) → (∀ x ∈ C, θ x ≤ R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) → AEStronglyMeasurable ξ (μHE[n].restrict C) → (∀ᵐ x ∂(μHE[n].restrict (C ∩ R₁.carrier)), ξ x = R₁.orient x ∨ ξ x = -R₁.orient x) → (∀ᵐ x ∂(μHE[n].restrict (C \ R₁.carrier)), ξ x = R₂.orient x ∨ ξ x = -R₂.orient x) → (∀ᵐ x ∂(μHE[n].restrict (C ∩ R₁.carrier)), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R₁.carrier x Q → HasApproximateTangentSpaceAt n C x Q) → (∀ᵐ x ∂(μHE[n].restrict (C \ R₁.carrier)), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R₂.carrier x Q → HasApproximateTangentSpaceAt n C x Q) → ∃ R : IMRep U n, R.carrier = C ∧ R.mult = θ ∧ R.orient = ξ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
