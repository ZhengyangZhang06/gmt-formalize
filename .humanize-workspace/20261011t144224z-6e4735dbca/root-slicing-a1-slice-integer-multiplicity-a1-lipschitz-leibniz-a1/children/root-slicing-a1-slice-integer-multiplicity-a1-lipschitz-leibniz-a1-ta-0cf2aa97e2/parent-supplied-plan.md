# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1.tangent_field-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-lipschitz-leibniz-a1-ta-0cf2aa97e2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.lipschitz_leibniz-a1`
- Child key: `tangent_field`
- Declaration: `Submission.slicing_im_ll_tangent_dual_field`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)), IsRectifiableTriple U (m + 1) M θ ξ → ∀ ω : TestFormOn U m, ∃ Y : Eucl P → Eucl P, Integrable Y ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧ (∀ (x : Eucl P) (φ : Eucl P →L[ℝ] ℝ), φ (Y x) = θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin (φ.smulRight ((ω : DifferentialForm (Eucl P) m) x)))) ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), ∀ Q : Submodule ℝ (Eucl P), HasWeightedApproximateTangentSpaceAt (m + 1) M θ x Q → Y x ∈ Q`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
