# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.blowup_scale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6da3570ebf/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `blowup_scale`
- Declaration: `Submission.cbr_ci_bl_blowup_scale`
- Exact Lean type: `∀ (P d : ℕ) (Γ Γ' : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P (d + 1)) (a : Euclid P) (lam : ℝ), 0 < lam → Γ.boundary = 0 → μ univ < ∞ → (∀ W : Set (Euclid P), IsOpen W → Γ.massOn W = μ W) → MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[(d + 1)].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x in M, θ x * ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μHE[(d + 1)]) → (∀ ω ω' : TestFormOn (univ : Set (Euclid P)) d, (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) d) y = (ω : DifferentialForm (Euclid P) d) (dilation a lam y)) → Γ'.boundary ω = lam⁻¹ ^ d * Γ.boundary ω') → ((∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → ∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) → (∀ W : Set (Euclid P), Γ'.massOn (dilation a lam '' W) = ENNReal.ofReal (lam⁻¹ ^ (d + 1)) * Γ.massOn W) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ ω = ∫ x, ζ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ Γ'.boundary = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → Γ'.massOn W = (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) W) ∧ AEStronglyMeasurable (fun y => ζ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, ζ (a + lam • y) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ)) ∧ (ENNReal.ofReal (lam⁻¹ ^ (d + 1)) • Measure.map (dilation a lam) μ) (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)ᶜ = 0 ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), Γ' ω = ∫ y, (θ (a + lam • y) • ζ (a + lam • y)) ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂(μHE[(d + 1)].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.blowup_measure-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
