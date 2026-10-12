# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1.boundary_smul_estimate-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-cutoff-boundary-vanishes-a1-1af7183163/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.regular_components_are_minimizing-a1.cutoff_boundary_vanishes-a1`
- Child key: `boundary_smul_estimate`
- Declaration: `Submission.regcomp_boundary_smul_estimate`
- Exact Lean type: `∀ (P m : ℕ) (U M₁ : Set (Euclid P)) (T₁ : GeometricCurrentOn U (m + 1)) (ξ : Euclid P → MultiVector P (m + 1)), (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in M₁, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → (∀ᵐ x ∂(μHE[m + 1].restrict M₁), ∀ α : Covector (Euclid P) (m + 1), |ξ x α| ≤ ‖α‖) → ∀ (f : Euclid P → ℝ) (ω F : TestFormOn U m), Differentiable ℝ f → (∀ x, (F : DifferentialForm (Euclid P) m) x = f x • (ω : DifferentialForm (Euclid P) m) x) → ENNReal.ofReal |T₁.boundary F| ≤ ∫⁻ x in M₁, ENNReal.ofReal (((m : ℝ) + 1) * (|f x| * ‖fderiv ℝ (ω : DifferentialForm (Euclid P) m) x‖ + ‖fderiv ℝ f x‖ * ‖(ω : DifferentialForm (Euclid P) m) x‖)) ∂μHE[m + 1]`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
