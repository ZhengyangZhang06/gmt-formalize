# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-6264bc6f37/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `rescaled_bounds`
- Declaration: `Submission.cbr_ci_bl_rescaled_bounds`
- Exact Lean type: `∀ (P n : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n) (a : Euclid P) (η₁ : ℝ) (lams : ℕ → ℝ), μHE[n] M < ∞ → MeasurableSet M → Measurable θ → StronglyMeasurable ζ → μ = (μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x)) → (∀ x ∈ M, 0 < θ x) → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ζ x α| ≤ covectorEuclideanNorm α) → (∀ x ∈ M, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ζ x β = 1) → a ∈ M → 0 < η₁ → ENNReal.ofReal η₁ ≤ liminf (fun r : ℝ => μ (ball a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) → limsup (fun r : ℝ => μHE[n] (M ∩ closedBall a r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) ≤ 1 → Tendsto (fun r : ℝ => (∫⁻ x in M ∩ closedBall a r, ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) → (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → (∀ K : Set (Euclid P), IsCompact K → ⨆ i, (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M)) K < ∞) ∧ (∀ R : ℝ, 0 < R → limsup (fun i => (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M)) (closedBall 0 R)) atTop ≤ unitBallVolume n * ENNReal.ofReal (R ^ n)) ∧ (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ENNReal.ofReal (η₁ / (4 * θ a)) * (unitBallVolume n * ENNReal.ofReal (R ^ n)) ≤ (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M)) (closedBall 0 R)) ∧ (∀ R : ℝ, 0 < R → Tendsto (fun i => ∫⁻ y in closedBall (0 : Euclid P) R, ‖θ (a + lams i • y) • ζ (a + lams i • y) - θ a • ζ a‖ₑ ∂(μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a (lams i) '' M))) atTop (𝓝 0))`

## Sibling prerequisites

- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.blowup_measure-a1`
- `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.density_bounds-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
