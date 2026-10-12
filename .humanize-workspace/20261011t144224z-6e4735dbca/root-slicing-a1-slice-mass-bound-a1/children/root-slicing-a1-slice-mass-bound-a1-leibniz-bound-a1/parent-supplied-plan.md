# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_mass_bound-a1.leibniz_bound-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-leibniz-bound-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_mass_bound-a1`
- Child key: `leibniz_bound`
- Declaration: `Submission.slicing_mb_leibniz_bound`
- Exact Lean type: `∀ (P m : ℕ) (U : Set (Eucl P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)), IsMeasureRepresentation T μ v → (∀ (x : Eucl P) (α : Covector (Eucl P) (m + 1)), |v x α| ≤ covectorEuclideanNorm α) → ∀ (ω : TestFormOn U m) (ψ : Eucl P → ℝ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ∃ (η₁ : TestFormOn U m) (η₂ : TestFormOn U (m + 1)), (∀ x, (η₁ : DifferentialForm (Eucl P) m) x = ψ x • (ω : DifferentialForm (Eucl P) m) x) ∧ (∀ x, (η₂ : DifferentialForm (Eucl P) (m + 1)) x = ψ x • exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∧ ENNReal.ofReal |T.boundary η₁ - T η₂| ≤ ∫⁻ x, (‖fderiv ℝ ψ x‖₊ : ℝ≥0∞) * ENNReal.ofReal (covectorEuclideanNorm ((ω : DifferentialForm (Eucl P) m) x)) ∂μ`

## Sibling prerequisites

- `root.slicing-a1.slice_mass_bound-a1.wedge_norm-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
