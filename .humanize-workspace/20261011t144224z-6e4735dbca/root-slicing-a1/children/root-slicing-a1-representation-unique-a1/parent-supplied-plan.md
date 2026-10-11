# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.representation_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-representation-unique-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1`
- Child key: `representation_unique`
- Declaration: `Submission.slicing_representation_unique`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ (μ₁ μ₂ : Measure (Eucl P)) (v₁ v₂ : Eucl P → NVector (Eucl P) k), (∀ ω : TestFormOn U k, Integrable (fun x => v₁ x ((ω : DifferentialForm (Eucl P) k) x)) μ₁) → (∀ ω : TestFormOn U k, Integrable (fun x => v₂ x ((ω : DifferentialForm (Eucl P) k) x)) μ₂) → ∀ W : Set (Eucl P), IsOpen W → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → ∫ x, v₁ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₁ = ∫ x, v₂ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₂) → ∀ A : Set (Eucl P), MeasurableSet A → ∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Eucl P) k) ⊆ W → ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₁ = ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl P) k) x) ∂μ₂`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
