# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1.pushforward_pair-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-36d85accd9/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.dilation_isp-a1`
- Child key: `pushforward_pair`
- Declaration: `Submission.cbr_ci_dsp_pushforward_pair`
- Exact Lean type: `∀ (P m : ℕ) (a : Euclid P) (lam : ℝ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m), 0 < lam → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ K : Set (Euclid P), IsCompact K → (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) K < ∞) ∧ AEStronglyMeasurable (fun y => ξ (a + lam • y)) (ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) ∧ (∀ᵐ y ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ), ∀ α : Covector (Euclid P) m, |ξ (a + lam • y) α| ≤ covectorEuclideanNorm α) ∧ ∀ (S : Set (Euclid P)) (ω : DifferentialForm (Euclid P) m), ∫ y in S, ξ (a + lam • y) (ω y) ∂(ENNReal.ofReal (lam⁻¹ ^ m) • Measure.map (dilation a lam) μ) = lam⁻¹ ^ m * ∫ x in dilation a lam ⁻¹' S, ξ x (ω (dilation a lam x)) ∂μ`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
