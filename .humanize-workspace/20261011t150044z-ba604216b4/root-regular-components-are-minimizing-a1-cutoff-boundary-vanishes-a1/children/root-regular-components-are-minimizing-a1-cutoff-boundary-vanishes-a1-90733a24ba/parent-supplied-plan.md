# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1.localized_boundary_zero-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1-90733a24ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Child key: `localized_boundary_zero`
- Declaration: `Submission.regcomp_localized_boundary_zero`
- Exact Lean type: `∀ (P m : ℕ) (U M₁ : Set (Euclid P)) (T T₁ : GeometricCurrentOn U (m + 1)) (ξ : Euclid P → MultiVector P (m + 1)), T.boundary = 0 → (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in M₁, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → (∀ z ∈ M₁, ∃ G : Set (Euclid P), IsOpen G ∧ z ∈ G ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ G → T₁ ω = c * T ω) → ∀ η : TestFormOn U m, closure M₁ ∩ tsupport (η : DifferentialForm (Euclid P) m) ⊆ M₁ → T₁.boundary η = 0`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
