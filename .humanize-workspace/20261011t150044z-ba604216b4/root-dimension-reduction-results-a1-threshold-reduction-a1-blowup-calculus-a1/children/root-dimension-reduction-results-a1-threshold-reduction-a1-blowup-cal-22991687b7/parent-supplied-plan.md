# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_calculus-a1.currenteval_pullback-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cal-22991687b7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_calculus-a1`
- Child key: `currenteval_pullback`
- Declaration: `Submission.dimred_tr_bc_currentEval_blowUp`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)`

## Sibling prerequisites

- `root.density_and_tangent_cones-a1.blowup_scaling-a1.testform_correspondence-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
