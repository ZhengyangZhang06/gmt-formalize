# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.deformation-a1.mass_restriction-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-deformation-a1-mass-restriction-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.deformation-a1`
- Child key: `mass_restriction`
- Declaration: `Submission.deformation_mass_restriction`
- Exact Lean type: `∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Eucl N)) k), X.mass < ∞ → ∃ (μ : Measure (Eucl N)) (v : Eucl N → NVector (Eucl N) k), IsFiniteMeasure μ ∧ IsMeasureRepresentation X μ v ∧ μ X.supportᶜ = 0 ∧ (∀ (μ' : Measure (Eucl N)) (v' : Eucl N → NVector (Eucl N) k), IsMeasureRepresentation X μ' v' → ∀ A : Set (Eucl N), MeasurableSet A → Bornology.IsBounded A → ∀ α : Covector (Eucl N) k, ∫ x in A, v' x α ∂μ' = ∫ x in A, v x α ∂μ) ∧ ∀ A : Set (Eucl N), MeasurableSet A → ∃ Y : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y ∧ (∀ ω : TestFormOn (univ : Set (Eucl N)) k, Y ω = ∫ x in A, v x ((ω : DifferentialForm (Eucl N) k) x) ∂μ) ∧ (∀ W : Set (Eucl N), IsOpen W → Y.massOn W = μ (W ∩ A)) ∧ (∀ Y' : GeometricCurrentOn (univ : Set (Eucl N)) k, IsRestriction X A Y' → Y' = Y) ∧ (IsIntegerMultiplicity X → IsIntegerMultiplicity Y)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
