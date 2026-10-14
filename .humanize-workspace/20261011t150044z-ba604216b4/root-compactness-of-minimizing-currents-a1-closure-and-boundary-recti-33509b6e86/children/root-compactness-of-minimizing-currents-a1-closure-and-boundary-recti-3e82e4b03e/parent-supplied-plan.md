# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-3e82e4b03e/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1`
- Child key: `dilation_calculus`
- Declaration: `Submission.cbr_ci_dilation_calculus`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P) (lam : ℝ), 0 < lam → (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) m, ∃ X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω')) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) (m + 1), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) (m + 1)) y = (ω : DifferentialForm (Euclid P) (m + 1)) (dilation a lam y)) → X' ω = lam⁻¹ ^ (m + 1) * X ω') → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X'.boundary ω = lam⁻¹ ^ m * X.boundary ω') ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → IsIntegerMultiplicity X → IsIntegerMultiplicity X') ∧ (∀ (X X' : GeometricCurrentOn (univ : Set (Euclid P)) m) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) m) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) m, X' ω = ∫ y, ξ (a + lam • y) ((ω : DifferentialForm (Euclid P) m) y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ)) ∧ (∀ X X' : GeometricCurrentOn (univ : Set (Euclid P)) m, (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) m, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) m) y = (ω : DifferentialForm (Euclid P) m) (dilation a lam y)) → X' ω = lam⁻¹ ^ m * X ω') → ∀ W : Set (Euclid P), X'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ m) * X.massOn W) ∧ (∀ A : Set (Euclid P), μHE[m] (dilation a lam '' A) = ENNReal.ofReal (lam⁻¹ ^ m) * μHE[m] A)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
