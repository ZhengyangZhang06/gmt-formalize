# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.stationary_results-a1.sff_properties-a1.normal_field_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-stationary-results-a1-sff-properties-a1-normal-field-identity-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.stationary_results-a1.sff_properties-a1`
- Child key: `normal_field_identity`
- Declaration: `Submission.inner_fderiv_normal_field_eq_neg_second_fundamental_form`
- Exact Lean type: `∀ (n N : ℕ) (M : Set (Rn N)), Chapter02.IsSimonSubmanifold (E := Rn n) 2 M → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, tangentSpace M (ψ x) = LinearMap.range (fderiv ℝ ψ x).toLinearMap) → (∀ (V : Set (Rn n)) (W : Set (Rn N)) (ψ : Rn n → Rn N), Chapter02.IsSimonLocalRepresentation 2 M V W ψ → ∀ x ∈ V, ∀ a b : Rn n, secondFundamentalForm M (ψ x) (fderiv ℝ ψ x a) (fderiv ℝ ψ x b) = normalPart M (ψ x) (fderiv ℝ (fderiv ℝ ψ) x a b)) → ∀ (Y : Rn N → Rn N) (y : Rn N), y ∈ M → DifferentiableAt ℝ Y y → (∀ z ∈ M, ∀ v ∈ tangentSpace M z, inner ℝ (Y z) v = 0) → ∀ τ ∈ tangentSpace M y, ∀ η ∈ tangentSpace M y, inner ℝ η (fderiv ℝ Y y τ) = -inner ℝ (Y y) (secondFundamentalForm M y τ η)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
