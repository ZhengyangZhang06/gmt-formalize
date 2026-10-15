# Parent-supplied child implementation contract

This scaffold was created deterministically by the controller. DAG child
`root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.class_rescale-a1` must not run plan generation or natural-language proof generation.
Use the independently reviewed proof at `.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-threshold-reduction-a1-blowup-cla-caa850f858/parent-supplied-natural-proof.md` directly.

## Frozen theorem

- Parent node: `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1`
- Child key: `class_rescale`
- Declaration: `Submission.dimred_tr_bc_class_rescale`
- Exact Lean type: `(∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜)`

## Sibling prerequisites

- `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.flat_off_null_set-a1.cone_class-a1.ambient_calculus-a1`
- `root.dimension_reduction_results-a1.threshold_reduction-a1.blowup_class-a1.zero_limit_rescale-a1`

## Implementation steps

1. Read the complete parent-supplied natural-language proof.
2. Formalize exactly the frozen theorem without weakening or replacing it.
3. Use only the listed accepted sibling prerequisites and ordinary frozen proof-base helpers.
4. Run the configured author-side child comparator and return a committed candidate. The outer
   controller, not this nested implementation loop, owns the independent reviewer comparator.
