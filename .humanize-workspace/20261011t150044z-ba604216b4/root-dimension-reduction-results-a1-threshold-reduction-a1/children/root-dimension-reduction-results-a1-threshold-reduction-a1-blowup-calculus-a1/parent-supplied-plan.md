# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_calculus-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-calculus-a1/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1`
- Child key: `blowup_calculus`
- Declaration: `Submission.dimred_tr_blowup_calculus`
- Exact Lean type: `∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
