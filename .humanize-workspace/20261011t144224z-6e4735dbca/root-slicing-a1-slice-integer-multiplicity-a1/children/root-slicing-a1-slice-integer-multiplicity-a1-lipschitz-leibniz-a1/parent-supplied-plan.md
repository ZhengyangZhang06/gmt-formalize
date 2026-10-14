# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1`
- Child key: `lipschitz_leibniz`
- Declaration: `Submission.slicing_im_lipschitz_leibniz`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (T : GeometricCurrentOn U (m + 1)), IsOpen U → IsRectifiableTriple U (m + 1) M θ ξ → (∀ η : TestFormOn U (m + 1), T η = tauAction (m + 1) M θ ξ η) → ∀ (μ : Measure (Eucl P)) (v : Eucl P → NVector (Eucl P) (m + 1)) (μ' : Measure (Eucl P)) (v' : Eucl P → NVector (Eucl P) m), IsMeasureRepresentation T μ v → IsMeasureRepresentation T.boundary μ' v' → ∀ (h : Eucl P → ℝ) (Lh : ℝ≥0) (Gh : Eucl P → Eucl P), LipschitzWith Lh h → Measurable Gh → (∀ x, ‖Gh x‖ ≤ Lh) → (∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → Gh x ∈ Q ∧ ∀ u ∈ Q, HasDerivAt (fun s : ℝ => h (x + s • u)) (inner ℝ (Gh x) u) 0) → ∀ ω : TestFormOn U m, (∫ x, h x * v' x ((ω : DifferentialForm (Eucl P) m) x) ∂μ') - (∫ x, h x * v x (exteriorDerivative (ω : DifferentialForm (Eucl P) m) x) ∂μ) = ∫ x in M, θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (Gh x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) ∂(μHE[m + 1] : Measure (Eucl P))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
