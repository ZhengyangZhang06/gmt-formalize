# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.mass_restriction-a1.representation_unique-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1-representation-unique-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1.mass_restriction-a1`
- Child key: `representation_unique`
- Declaration: `Submission.dmr_measureRepresentation_unique`
- Exact Lean type: `∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k) (μ₁ μ₂ : Measure (Eucl N)) (v₁ v₂ : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ₁ v₁ → IsMeasureRepresentation X μ₂ v₂ → (∀ A : Set (Eucl N), MeasurableSet A → ∀ ω : TestFormOn (univ : Set (Eucl N)) k, ∫ x in A, v₁ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₁ = ∫ x in A, v₂ x ((ω : DifferentialForm (Eucl N) k) x) ∂μ₂) ∧ (∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v₁ x α ∂μ₁ = ∫ x in A, v₂ x α ∂μ₂)`

## Sibling prerequisites

- `root.slicing-a1.representation_unique-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
