# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1.blowup_measure-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-92df5214ba/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.cycle_im-a1.blowup_limit-a1`
- Child key: `blowup_measure`
- Declaration: `Submission.cbr_ci_bl_blowUp_restrict_scaling`
- Exact Lean type: `∀ (P n : ℕ) (M : Set (Euclid P)) (θ : Euclid P → ℝ) (a : Euclid P) (lam : ℝ), MeasurableSet M → Measurable θ → 0 < lam → MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) ∧ μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M) = ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) (μHE[n].restrict M) ∧ ENNReal.ofReal (lam⁻¹ ^ n) • Measure.map (dilation a lam) ((μHE[n].restrict M).withDensity (fun x => ENNReal.ofReal (θ x))) = (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap a lam '' M)).withDensity (fun y => ENNReal.ofReal (θ (a + lam • y)))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
