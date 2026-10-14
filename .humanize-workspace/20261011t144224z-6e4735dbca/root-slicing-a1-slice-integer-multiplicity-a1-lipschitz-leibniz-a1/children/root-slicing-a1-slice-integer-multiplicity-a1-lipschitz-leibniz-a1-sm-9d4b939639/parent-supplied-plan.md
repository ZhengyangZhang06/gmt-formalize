# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.smooth_identity-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-sm-9d4b939639/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`
- Child key: `smooth_identity`
- Declaration: `Submission.slicing_im_ll_smooth_leibniz`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)), (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)) (μ' : Measure (Eucl P)) (v' : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T μ v → IsMeasureRepresentation T.boundary μ' v' → ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ ψ x).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ∂(μHE[m + 1] : Measure (Eucl P)) = (∫ x, ψ x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') - (∫ x, ψ x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ)`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.extderiv_leibniz-a1`
- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.smul_test_form-a1`
- `root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1.wedge_test_form-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
