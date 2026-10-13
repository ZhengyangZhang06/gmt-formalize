# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.mass_representation-a1.riesz_forms-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-mass-representation-a1-riesz-forms-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.mass_representation-a1`
- Child key: `riesz_forms`
- Declaration: `Submission.smr_riesz_continuous_forms`
- Exact Lean type: `∀ (P k : ℕ) (U : Set (Eucl P)), IsOpen U → ∀ L : (Eucl P → Covector (Eucl P) k) → ℝ, (∀ φ ψ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ U → L (φ + ψ) = L φ + L ψ) → (∀ (c : ℝ) (φ : Eucl P → Covector (Eucl P) k), Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → L (c • φ) = c * L φ) → (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → ∃ B : ℝ, ∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → tsupport φ ⊆ K → (∀ x, covectorEuclideanNorm (φ x) ≤ 1) → |L φ| ≤ B) → ∃ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) k), (∀ φ : Eucl P → Covector (Eucl P) k, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → Integrable (fun x => v x (φ x)) μ ∧ L φ = ∫ x, v x (φ x) ∂μ) ∧ μ Uᶜ = 0 ∧ (∀ K : Set (Eucl P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ (x : Eucl P) (α : Covector (Eucl P) k), |v x α| ≤ covectorEuclideanNorm α) ∧ (∀ α : Covector (Eucl P) k, Measurable (fun x => v x α)) ∧ ∀ᵐ x ∂μ, ∃ α : Covector (Eucl P) k, covectorEuclideanNorm α ≤ 1 ∧ v x α = 1`

## Sibling prerequisites

- `root.slicing-a1.mass_representation-a1.covector_isometry-a1`
- `root.slicing-a1.mass_representation-a1.riesz_borel-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
