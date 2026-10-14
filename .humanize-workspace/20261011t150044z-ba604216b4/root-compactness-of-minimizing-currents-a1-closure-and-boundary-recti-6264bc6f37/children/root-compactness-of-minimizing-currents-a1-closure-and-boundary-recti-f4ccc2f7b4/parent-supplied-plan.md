# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1.scale_identities-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f4ccc2f7b4/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.rescaled_bounds-a1`
- Child key: `scale_identities`
- Declaration: `Submission.cbr_ci_bl_rb_scale_identities`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (ζ : Euclid P → MultiVector P n) (a : Euclid P) (lam : ℝ), 0 < lam → μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) = ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) → (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) univ = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] M ∧ ∀ R : ℝ, 0 < R → (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) (closedBall 0 R) = unitBallVolume n * ENNReal.ofReal (R ^ n) * (μHE[n] (M ∩ closedBall a (lam * R)) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) ∧ (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) (ball 0 R) = unitBallVolume n * ENNReal.ofReal (R ^ n) * (μHE[n] (M ∩ ball a (lam * R)) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n))) ∧ ∫⁻ y in closedBall (0 : Euclid P) R, ‖θ (a + lam • y) • ζ (a + lam • y) - θ a • ζ a‖ₑ ∂(μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)) = unitBallVolume n * ENNReal.ofReal (R ^ n) * ((∫⁻ x in M ∩ closedBall a (lam * R), ‖θ x • ζ x - θ a • ζ a‖ₑ ∂μHE[n]) / (unitBallVolume n * ENNReal.ofReal ((lam * R) ^ n)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
