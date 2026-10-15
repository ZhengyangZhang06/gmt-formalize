# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1.convex_poincare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 2 and 5 of the parent proof (finiteness; integrating the segment estimate over Q × Q with Tonelli; the final estimate), for a general convex measurable Q with ‖x − y‖ ≤ d on Q.
- Step 1 of the parent proof is the sibling segment_bound (Submission.dimred_mbl_dt_cbm_sp_segment_bound).
- Steps 3–4 of the parent proof are the sibling convex_slice_bound (Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound).

The bound keeps the factors d and Lⁿ(Q) separate; the parent later uses d = √n and Lⁿ(Q) ≤ 1. The structure is that of the accepted Lean proof of Submission.dorag_ha_pb_double_integral_bound (commit cba007e5f), without the square.

Notation. ℝⁿ := Euclid n and Lⁿ := volume. F(z) := ‖Dv(z)‖ = ‖fderiv ℝ v z‖ and g(z) := ofReal(F(z)) ∈ [0, ∞). ∫⁻ are lower Lebesgue integrals; ∫ are Bochner integrals.

1. Regularity and finiteness.
   - v is continuous, and F is continuous because v is C¹ (so Dv is continuous).
   - Q is bounded, since dist(x, y) = ‖x − y‖ ≤ d for x, y ∈ Q (Metric.isBounded_iff). Hence Lⁿ(Q) < ∞ (Bornology.IsBounded.measure_lt_top) and closure(Q) is compact.
   - So there is C with F(z) ≤ C for z ∈ closure(Q) ⊇ Q (IsCompact.exists_bound_of_continuousOn).
   - g is measurable, and ∫⁻_Q g ≤ ∫⁻_Q ofReal(C) = ofReal(C)·Lⁿ(Q) < ∞.
2. Pointwise bound. Fix x, y ∈ Q and let G := ∫_0^1 F((1 − t)y + tx) dt ≥ 0 (interval integral).
   - By segment_bound, |v(x) − v(y)| ≤ ‖x − y‖·G ≤ d·G, using ‖x − y‖ ≤ d and G ≥ 0.
   - Since 0 ≤ 1, G = ∫_{(0,1]} F((1 − t)y + tx) dt (intervalIntegral.integral_of_le). The integrand is nonnegative and continuous, so G = toReal(∫⁻_{t∈(0,1]} g((1 − t)y + tx) dt) (integral_eq_lintegral_of_nonneg_ae). Hence ofReal(G) ≤ ∫⁻_{t∈(0,1]} g((1 − t)y + tx) dt, because ofReal(toReal a) ≤ a.
   - As d ≥ 0, ofReal|v(x) − v(y)| ≤ ofReal(d·G) = ofReal(d)·ofReal(G) ≤ ofReal(d)·∫⁻_{t∈(0,1]} g((1 − t)y + tx) dt.
3. Tonelli.
   - For fixed x, (y, t) ↦ g((1 − t)y + tx) is measurable: it is g composed with a continuous map.
   - (x, t) ↦ ∫⁻_{y∈Q} g((1 − t)y + tx) dy is measurable: it is a parametric lower integral of the jointly measurable function ((x, t), y) ↦ g((1 − t)y + tx) (Measurable.lintegral_prod_right').
   - Two applications of Tonelli (lintegral_lintegral_swap) give
     ∫⁻_{x∈Q} ∫⁻_{y∈Q} ∫⁻_{t∈(0,1]} g((1 − t)y + tx) = ∫⁻_{t∈(0,1]} ∫⁻_{x∈Q} ∫⁻_{y∈Q} g((1 − t)y + tx).
4. Lower-integral estimate. Integrate step 2 over y ∈ Q and then over x ∈ Q (setLIntegral_mono'). Pull out the finite constant ofReal(d) (lintegral_const_mul') and use step 3. Then bound each t-slice by convex_slice_bound, applied to Q, g and t ∈ (0, 1] ⊆ [0, 1]. Since L¹((0, 1]) = 1, this gives
   ∫⁻_{x∈Q} ∫⁻_{y∈Q} ofReal|v(x) − v(y)| ≤ ofReal(d)·∫⁻_{t∈(0,1]} 2ⁿ·Lⁿ(Q)·∫⁻_Q g dt = ofReal(d)·(2ⁿ·Lⁿ(Q)·∫⁻_Q g) =: K.
   By step 1, K < ∞.
5. Back to Bochner integrals.
   (a) For every x, ∫_{y∈Q} |v(x) − v(y)| dy = toReal(h(x)), where h(x) := ∫⁻_{y∈Q} ofReal|v(x) − v(y)| dy (nonnegative continuous integrand; integral_eq_lintegral_of_nonneg_ae).
   (b) h is measurable (Measurable.lintegral_prod_right', applied to the continuous map (x, y) ↦ |v(x) − v(y)|). So ∫_{x∈Q} toReal(h(x)) dx = toReal(∫⁻_{x∈Q} ofReal(toReal(h(x))) dx).
   (c) Since ofReal(toReal(h(x))) ≤ h(x), the last lower integral is ≤ ∫⁻_{x∈Q} h(x) dx ≤ K < ∞ by step 4. Monotonicity of toReal on finite values (ENNReal.toReal_mono) gives ∫_{x∈Q} ∫_{y∈Q} |v(x) − v(y)| dy dx ≤ toReal(K).
   (d) toReal(K) = d·2ⁿ·toReal(Lⁿ(Q))·toReal(∫⁻_Q g), because toReal is multiplicative and toReal(ofReal d) = d for d ≥ 0. Also toReal(∫⁻_Q g) = ∫_Q F, since F ≥ 0 is continuous.
   Therefore ∫_{x∈Q} ∫_{y∈Q} |v(x) − v(y)| dy dx ≤ 2ⁿ·d·Lⁿ(Q)·∫_Q ‖Dv‖. ∎

Lean reference (informative, not part of the mathematical argument above). The following proof of exactly this frozen statement, under exactly this declaration name, was kernel-checked in this decomposition session: it was compiled with `lake env lean` after `import GMT.Ch07.Submission` in the frozen contract scope (project b4d606d, Mathlib 25730c7c), and it was also compiled when inserted into a copy of GMT/Ch07/Submission.lean between the closing `end` of the noncomputable section and main_theorem. #print axioms: propext, Classical.choice, Quot.sound. It uses the sibling theorems Submission.dimred_mbl_dt_cbm_sp_segment_bound and Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound, and needs no import beyond the frozen Submission header.

theorem Submission.dimred_mbl_dt_cbm_sp_convex_poincare : ∀ (n : ℕ) (Q : Set (Euclid n)) (v : Euclid n → ℝ) (d : ℝ), Convex ℝ Q → MeasurableSet Q → 0 ≤ d → (∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ d) → ContDiff ℝ 1 v → ∫ x in Q, ∫ y in Q, |v x - v y| ≤ 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
  intro n Q v d hQc hQm hd hdiam hv
  have hseg := Submission.dimred_mbl_dt_cbm_sp_segment_bound n v
  have hslice := Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound n Q
  have hcont : Continuous v := hv.continuous
  have hFc : Continuous fun z => ‖fderiv ℝ v z‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hQb : Bornology.IsBounded Q :=
    Metric.isBounded_iff.2 ⟨d, fun x hx y hy => by rw [dist_eq_norm]; exact hdiam x hx y hy⟩
  have hQfin : volume Q < ∞ := hQb.measure_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ closure Q, ‖‖fderiv ℝ v z‖‖ ≤ C :=
    hQb.isCompact_closure.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal ‖fderiv ℝ v z‖ :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal ‖fderiv ℝ v z‖ := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hFc.measurable.ennreal_ofReal
  have hJ : ∫⁻ z in Q, g z ≠ ∞ := by
    have h1 : ∫⁻ z in Q, g z ≤ ∫⁻ _ in Q, ENNReal.ofReal C :=
      setLIntegral_mono' hQm fun z hz => by
        rw [hgx]
        exact ENNReal.ofReal_le_ofReal (by simpa using hC z (subset_closure hz))
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin)).ne
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    intro x hx y hy
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => norm_nonneg _
    have h1 : |v x - v y| ≤ d * G :=
      (hseg x y hv).trans (mul_le_mul_of_nonneg_right (hdiam x hx y hy) hG)
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ v ((1 - t) • y + t • x)‖)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hFc.comp h).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => norm_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal |v x - v y| ≤ ENNReal.ofReal (d * G) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal d * ENNReal.ofReal G := ENNReal.ofReal_mul hd
      _ ≤ _ := by gcongr
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in Q, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in Q, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in Q, g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  have hI : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y|
        ≤ ∫⁻ x in Q, ∫⁻ y in Q,
            ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => hpt x hx y hy
      _ = ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q,
            g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [hswap]
      _ ≤ ENNReal.ofReal d * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hQc hQm hg t (Ioc_subset_Icc_self ht)) _
      _ = ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  have hK : Measurable fun x : Euclid n => ∫⁻ y in Q, ENNReal.ofReal |v x - v y| := by
    have h : Continuous fun p : Euclid n × Euclid n => |v p.1 - v p.2| := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal |v p.1 - v p.2|)
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in Q, |v x - v y| =
      (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
      (by fun_prop : Continuous fun y => |v x - v y|).aestronglyMeasurable
  have hrhs : ∫ z in Q, ‖fderiv ℝ v z‖ = (∫⁻ z in Q, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => norm_nonneg _)
      hFc.aestronglyMeasurable]
    simp only [hgx]
  have hfin : ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hQfin.ne) hJ)
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      = ∫ x in Q, (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := by simp only [hinner]
    _ = (∫⁻ x in Q, ENNReal.ofReal (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z)).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hd]
        ring

## Key steps

1. F = ‖Dv‖ is continuous; Q is bounded, so Lⁿ(Q) < ∞ and F ≤ C on Q; g = ofReal ∘ F has finite lower integral over Q.
2. segment_bound and ‖x − y‖ ≤ d: ofReal|v(x) − v(y)| ≤ ofReal(d)·∫⁻_{(0,1]} g((1 − t)y + tx) dt for x, y ∈ Q.
3. Tonelli moves the t-integral outside; convex_slice_bound bounds each t-slice by 2ⁿ Lⁿ(Q) ∫⁻_Q g.
4. Hence ∫⁻_Q∫⁻_Q ofReal|v(x) − v(y)| ≤ ofReal(d)·2ⁿ Lⁿ(Q) ∫⁻_Q g < ∞.
5. Convert to Bochner integrals (integral_eq_lintegral_of_nonneg_ae, toReal monotonicity) to get ≤ 2ⁿ d Lⁿ(Q) ∫_Q ‖Dv‖.

## Reference use

### local-project

Queries:
- `cat RUN/local-references/123e8435b4a2469b/manifest.json (project_commit b4d606db1da5…, mathlib_commit 25730c7c759d…); git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD (both match the manifest)`
- `cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean (both identical)`
- `rg -n -i 'poincar' SNAPSHOT/project/GMT -g '*.lean' (only Poincare.SimonGMT import/open lines)`
- `rg -n -i 'poincar[eé] inequality|poincare_inequality|poincareInequality' SNAPSHOT/mathlib/Mathlib -g '*.lean' (no match); rg -n -i -l 'poincar' SNAPSHOT/mathlib/Mathlib (only CurveIntegral/Poincare.lean = Poincaré lemma for closed 1-forms, Geometry/Manifold/PoincareConjecture.lean, recurrence/other unrelated files)`
- `rg -n -i 'poincar[eé] inequality|poincare_ineq|PoincareIneq' lake-packages-25730c7c/simongmt -g '*.lean' (only Chapter04/Poincare.lean: Simon (5.6) varifold inequality HasGeneralizedMeanCurvatureIn.poincare_inequality, not applicable)`
- `rg -n 'theorem map_addHaar_smul|lintegral_mul_left_eq_self|theorem lintegral_lintegral_swap|theorem Measurable.lintegral_prod_right.|theorem integral_eq_lintegral_of_nonneg_ae|theorem integral_eq_sub_of_hasDerivAt |theorem integral_mono_on |theorem PiLp.volume_preserving_ofLp|theorem volume_pi_Ioo|theorem EuclideanSpace.norm_eq|theorem setLIntegral_mono.|theorem setLIntegral_const|theorem lintegral_indicator |theorem lintegral_smul_measure|theorem setLIntegral_le_lintegral|theorem convex_iff_forall_pos|theorem finrank_euclideanSpace_fin|Bornology.IsBounded.measure_lt_top' SNAPSHOT/mathlib/Mathlib -g '*.lean' (all found)`
- `python3 scans of RUN/dag.json (2092 nodes): selected node status decomposing, depth 5, children []; nodes with identical lean_statement: twin cmcdt_cbm_smooth_poincare (waiting-children) whose children cmcdt_cbm_sp_{segment_bound,convex_slice_bound,cube_geometry} are decomposing and cmcdt_cbm_sp_convex_poincare speculative-lean (none accepted); no accepted node carries any of the four child types; accepted ball analogues dorag_ha_pb_slice_bound (candidate 7ad779ea2) and dorag_ha_pb_double_integral_bound (candidate cba007e5f) have different types`
- `exact lean_name and substring scans for dimred_mbl_dt_cbm_sp_ in dag.json; rg -n 'dimred_mbl_dt_cbm_sp' SNAPSHOT GMT lake-packages-25730c7c/simongmt; git for-each-ref | xargs git grep -l -F 'dimred_mbl_dt_cbm_sp_' -- GMT/Ch07/Submission.lean over 3711 ref tips (no match anywhere)`
- `grep -n 'def _existing_lean_name_problem' -A40 /runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py (unaccepted names owned by another parent cannot be shared)`
- `python3 cat of twin node files decomposition-v1.json, decomposition-audit-v1.json, decomposition-review-receipt-v1.json, decomposition-scope-v1.json, parent-child-handoff.json; diff of the twin's and this node's supplied natural proofs (same steps 0–5, wording only)`
- `python3 -I importing verifier/gmt-compare.py contract_scope/child_modules (contract mode) and validate_lean_statement from verifier/lean_contract.py and runtime lean_contract.py for the four child types and the parent type`
- `lake env lean /tmp/dimred_sp_audit_9426/lean/Proofs.lean; lake env lean /tmp/dimred_sp_audit_9426/lean/Solutions.lean; lake env lean /tmp/dimred_sp_audit_9426/lean/SubmissionInserted.lean; lake env lean /tmp/dimred_sp_audit_9426/chal/Challenge_{segment_bound,convex_slice_bound,convex_poincare,cube_geometry,parent}.lean`
- `sed -n 645,660p book/chapter-02.txt (Simon Ch. 2, 2.7: 'usual Poincaré inequality for smooth functions (see e.g. [GT01])')`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter04/Poincare.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9426bce89d/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-deformation-the-9426bce89d/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/decomposition-audit-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/decomposition-review-receipt-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/decomposition-scope-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/dimred_sp_audit_9426/lean/Proofs.lean`
- `/tmp/dimred_sp_audit_9426/lean/Proofs.log`
- `/tmp/dimred_sp_audit_9426/lean/Solutions.lean`
- `/tmp/dimred_sp_audit_9426/lean/Solutions.lean.log`
- `/tmp/dimred_sp_audit_9426/lean/SubmissionInserted.lean`
- `/tmp/dimred_sp_audit_9426/lean/SubmissionInserted.log`
- `/tmp/dimred_sp_audit_9426/chal/Challenge_segment_bound.lean`
- `/tmp/dimred_sp_audit_9426/chal/Challenge_convex_slice_bound.lean`
- `/tmp/dimred_sp_audit_9426/chal/Challenge_convex_poincare.lean`
- `/tmp/dimred_sp_audit_9426/chal/Challenge_cube_geometry.lean`
- `/tmp/dimred_sp_audit_9426/chal/Challenge_parent.lean`

The pins match: workspace HEAD b4d606db and Mathlib 25730c7c. The workspace Submission.lean and Contract.lean are byte-identical to the snapshot contract.

No usable Poincaré inequality exists locally:
- The snapshot project has none.
- Mathlib has none. Its only 'Poincare' file is the Poincaré lemma for closed 1-forms.
- SimonGMT has only the varifold inequality of Simon (5.6), which does not apply to this Euclidean C¹ double-integral statement.

Every Mathlib lemma the split uses exists at the pinned revision and is available under the bare Submission imports. These are map_addHaar_smul, lintegral_add_left_eq_self (to_additive of lintegral_mul_left_eq_self), lintegral_lintegral_swap, Measurable.lintegral_prod_right', integral_eq_lintegral_of_nonneg_ae, intervalIntegral.integral_eq_sub_of_hasDerivAt, PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, EuclideanSpace.norm_eq and the setLIntegral lemmas.

The four child types are byte-identical to the audited, unaccepted split of the identical-type twin cmcdt_cbm_smooth_poincare. That twin belongs to another parent, so the fresh names dimred_mbl_dt_cbm_sp_* are required. They collide with nothing in the DAG, the snapshot, the GMT workspace, SimonGMT, or any git ref.

All five types, the four children and the parent, elaborate in the exact comparator challenge form and pass both statement validators. The four child proofs and the parent composition compile together, as standalone files and when inserted into a copy of Submission.lean. The only axioms are propext, Classical.choice and Quot.sound.
