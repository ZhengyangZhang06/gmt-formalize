# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.im_criterion-a1.im_assembly-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-4f1d720f00/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.im_criterion-a1`
- Child key: `im_assembly`
- Declaration: `Submission.cbr_ci_imc_isIntegerMultiplicity_of_rectifiable`
- Exact Lean type: `∀ (P n : ℕ) (Γ : GeometricCurrentOn (univ : Set (Euclid P)) n) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n), MeasurableSet M → CountablyRectifiable n M → Measurable θ → StronglyMeasurable ζ → (∀ x ∈ M, 0 < θ x) → ∫⁻ x in M, ENNReal.ofReal (θ x) ∂μHE[n] < ∞ → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q ∧ ∃ m : ℕ, θ x = m) → IsIntegerMultiplicity Γ`

## Sibling prerequisites

- `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.tangent_null_invariance-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
