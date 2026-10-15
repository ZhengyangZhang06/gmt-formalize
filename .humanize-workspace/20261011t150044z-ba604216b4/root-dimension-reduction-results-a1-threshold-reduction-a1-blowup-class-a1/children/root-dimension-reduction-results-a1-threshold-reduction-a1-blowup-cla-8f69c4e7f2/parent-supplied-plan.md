# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.zero_limit_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-8f69c4e7f2/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`
- Child key: `zero_limit_rescale`
- Declaration: `Submission.dimred_tr_bc_zero_limit_rescale`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (cs : ℕ → Euclid P) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (lam : ℝ) (hlam : 0 < lam), ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S → ∃ S' : GeometricCurrentOn (univ : Set (Euclid P)) n, ConvergesWeakly (fun i => blowUp T (cs i + ts i • y) (ts i * lam) (mul_pos (hts i) hlam).ne') S' ∧ ∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents S → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.Represents S' ∧ R'.measure = ENNReal.ofReal (lam⁻¹ ^ n) • R.measure.map (dilation y lam)`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
