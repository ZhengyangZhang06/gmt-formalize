# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_calculus-a1.dilation_blowup-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-61322d5395/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_calculus-a1`
- Child key: `dilation_blowup`
- Declaration: `Submission.cbr_cidc_dilation_exists_eq_blowUp`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ ∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ (ω : TestFormOn (univ : Set (Euclid P)) m) (ω₁ : TestFormOn (dilation a lam '' (univ : Set (Euclid P))) m), (ω₁ : DifferentialForm (Euclid P) m) = (ω : DifferentialForm (Euclid P) m) → X' ω = blowUp X a lam hlam.ne' ω₁`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.testform_correspondence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
