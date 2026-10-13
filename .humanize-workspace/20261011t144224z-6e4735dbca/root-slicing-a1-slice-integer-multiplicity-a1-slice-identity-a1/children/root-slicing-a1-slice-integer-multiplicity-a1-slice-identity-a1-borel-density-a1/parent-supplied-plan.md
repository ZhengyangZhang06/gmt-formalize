# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.borel_density-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1-borel-density-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child key: `borel_density`
- Declaration: `Submission.slicing_im_si_borel_density`
- Exact Lean type: `∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (G : Eucl P → Eucl P) (ω : TestFormOn U m), IsRectifiableTriple U (m + 1) M θ ξ → Measurable G → ∃ g : Eucl P → ℝ, Measurable g ∧ Integrable g ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧ (∀ x, G x = 0 → g x = 0) ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), (G x ≠ 0 → g x = θ x * (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x)))) ((ω : DifferentialForm (Eucl P) m) x)) ∧ θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) = ‖G x‖ * g x`

## Sibling prerequisites

- `root.flat_iff_weak-a1.im_series-a1.tsum_tau-a1.unit_bound-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
