# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1.weight_convergence-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-b1a0f97aa7/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_tangent-a1`
- Child key: `weight_convergence`
- Declaration: `Submission.dimred_tr_bc_ct_weight_convergence`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (P n : ℕ) (V : Set (Euclid P)) (A : GeometricCurrentOn V n) (R : IMRep V n) (a : Euclid P) (ss : ℕ → ℝ) (hss : ∀ j, 0 < ss j) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (RC : IMRep (univ : Set (Euclid P)) n), R.Represents A → RC.Represents C → MassMeasuresConverge (fun j => blowUp A a (ss j) (hss j).ne') C → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((ss j)⁻¹ ^ n) • R.measure.map (dilation a (ss j)))) atTop (𝓝 (∫ x, f x ∂RC.measure))`

## Sibling prerequisites

- None.

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
