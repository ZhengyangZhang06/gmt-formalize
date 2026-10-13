# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.unit_form_density-a1.unit_coord_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-unit-form-density-a1-unit-coord-field-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1.unit_form_density-a1`
- Child key: `unit_coord_field`
- Declaration: `Submission.smr_ufd_unit_coord_field`
- Exact Lean type: `∀ (P k N : ℕ) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k) (J : Covector (Eucl P) k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)), (∀ α : Covector (Eucl P) k, covectorEuclideanNorm α = ‖J α‖) → (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) → (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) → (∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1) → ∃ u : Eucl P → EuclideanSpace ℝ (Fin N), Measurable u ∧ (∀ x, ‖u x‖ ≤ 1) ∧ (∀ᵐ x ∂μ, ‖u x‖ = 1) ∧ ∀ (x : Eucl P) (α : Covector (Eucl P) k), v x α = inner ℝ (J α) (u x)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
