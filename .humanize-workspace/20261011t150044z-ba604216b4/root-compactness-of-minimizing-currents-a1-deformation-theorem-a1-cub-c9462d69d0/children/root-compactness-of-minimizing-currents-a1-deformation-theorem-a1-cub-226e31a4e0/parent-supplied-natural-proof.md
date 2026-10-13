# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.cube_bv_median-a1.smooth_poincare-a1.convex_poincare-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 0, 2 and 5 of the parent proof (finiteness; integrating the segment estimate over Q × Q with Tonelli; the final estimate), for a general convex measurable Q with ‖x − y‖ ≤ d on Q.
- Step 1 of the parent proof is the sibling segment_bound (Submission.cmcdt_cbm_sp_segment_bound).
- Steps 3–4 of the parent proof are the sibling convex_slice_bound (Submission.cmcdt_cbm_sp_convex_slice_bound).

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

Lean reference (informative, not part of the mathematical argument above). The following proof of exactly this frozen statement was kernel-checked during decomposition: it was compiled with `lake env lean` after `import GMT.Ch07.Submission` in the frozen contract scope (project b4d606d, Mathlib 25730c7c), and it was also compiled when inserted into GMT/Ch07/Submission.lean before main_theorem. #print axioms: propext, Classical.choice, Quot.sound. It uses the sibling theorems Submission.cmcdt_cbm_sp_segment_bound and Submission.cmcdt_cbm_sp_convex_slice_bound, and needs no import beyond the frozen Submission header.

theorem Submission.cmcdt_cbm_sp_convex_poincare : ∀ (n : ℕ) (Q : Set (Euclid n)) (v : Euclid n → ℝ) (d : ℝ), Convex ℝ Q → MeasurableSet Q → 0 ≤ d → (∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ d) → ContDiff ℝ 1 v → ∫ x in Q, ∫ y in Q, |v x - v y| ≤ 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
  intro n Q v d hQc hQm hd hdiam hv
  have hseg := Submission.cmcdt_cbm_sp_segment_bound n v
  have hslice := Submission.cmcdt_cbm_sp_convex_slice_bound n Q
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
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest.json)`
- `rg -n 'cmcdt_cbm_sp' local-references/123e8435b4a2469b/project local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean' (no match)`
- `python3 scan of runs/20261011T150044Z-ba604216b4/dag.json lean_name fields (1594 names) for cmcdt_cbm_sp_segment_bound, cmcdt_cbm_sp_convex_slice_bound, cmcdt_cbm_sp_convex_poincare, cmcdt_cbm_sp_cube_geometry (no collision)`
- `python3 scan of dag.json lean_statement/statement fields for '(1 - t) •', 'fderiv ℝ v', 'Poincar', '∫ t in (0', 'segment' (hits: accepted unit-ball nodes dorag_ha_pb_slice_bound, dorag_ha_pb_double_integral_bound, dorag_ha_pb_segment_ftc, dorag_ha_pb_pair_sq_bound)`
- `git show 7ad779ea2 -- GMT/Ch07/Submission.lean; git show cba007e5f -- GMT/Ch07/Submission.lean (accepted Lean proofs of dorag_ha_pb_slice_bound and dorag_ha_pb_double_integral_bound)`
- `rg -n -i 'poincar[eé] inequality|poincare_ineq|BVPoincare|double.integral|segment' local-references/123e8435b4a2469b/project/GMT -g '*.lean'`
- `rg -n 'theorem map_addHaar_smul|theorem lintegral_lintegral_swap|theorem lintegral_indicator\b|theorem setLIntegral_le_lintegral|theorem setLIntegral_mono'|theorem setLIntegral_const\b|theorem integral_eq_lintegral_of_nonneg_ae|theorem Measurable.lintegral_prod_right'|theorem integral_eq_sub_of_hasDerivAt\b|theorem norm_integral_le_integral_norm|theorem integral_mono_on\b|theorem volume_pi_Ioo|theorem convex_iff_forall_pos|theorem finrank_euclideanSpace_fin|theorem lintegral_map\b' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `rg -n 'lintegral_mul_left_eq_self|theorem PiLp.volume_preserving_ofLp|theorem EuclideanSpace.norm_eq|Bornology.IsBounded.measure_lt_top|theorem lintegral_smul_measure|theorem ContDiff.continuous_fderiv|theorem HasFDerivAt.comp_hasDerivAt|theorem lintegral_const_mul'|theorem mul_le_mul_right' local-references/123e8435b4a2469b/mathlib/Mathlib -g '*.lean'`
- `sed -n 540,640p verifier/gmt-compare.py (child scope = contract scope commands replayed up to main_theorem; solution module proves the frozen type by exact Submission.<lean_name>)`
- `lake env lean /tmp/sp-decomp-c946/Types1.lean (candidate child types elaborate after import GMT.Ch07.Submission in the contract scope; the parent type pretty-prints as the intended iterated set integrals with √(↑m + 1))`
- `lake env lean /tmp/sp-decomp-c946/All.lean (complete proofs of the four children and of the frozen parent type from them, no sorry; comparator-style theorem _root_.HumanizeNodeComparator.target : (type) := by exact Submission.X for all five types; #print axioms: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/sp-decomp-c946/SubmissionTest.lean (GMT/Ch07/Submission.lean with the five theorems inserted before main_theorem; only warning is main_theorem's contract sorry)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch04/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Group/LIntegral.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Prod.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Map.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Convex/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/Deriv/Comp.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-cub-c9462d69d0/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/tmp/sp-decomp-c946/Types1.lean`
- `/tmp/sp-decomp-c946/All.lean`
- `/tmp/sp-decomp-c946/SubmissionTest.lean`

The snapshot (project b4d606d, Mathlib 25730c7c) has the same contract as the workspace: Contract.lean and Submission.lean are both byte-identical to it.

No declaration can be reused as-is:
- The snapshot project has Poincaré-type results only as unsolved contract Props: Ch02 BVPoincare and Ch04 PoincareInequality.
- No cmcdt_cbm_sp_* name exists in the snapshot, Mathlib, or the 1594 DAG lean names.
- The DAG's accepted unit-ball nodes dorag_ha_pb_slice_bound, dorag_ha_pb_double_integral_bound and dorag_ha_pb_segment_ftc have different frozen types: a ball instead of a convex set, a Lipschitz u with a.e. differentiability, and squared differences. Their accepted proofs (commits 7ad779ea2 and cba007e5f) were adapted for the convex slice bound and the convex Poincaré child.

Mathlib 25730c7c supplies every tool, all inside the import closure of the frozen Submission header:
- Measure.map_addHaar_smul, lintegral_map, lintegral_smul_measure, lintegral_add_left_eq_self, lintegral_indicator, setLIntegral_le_lintegral;
- lintegral_lintegral_swap, Measurable.lintegral_prod_right', setLIntegral_mono', setLIntegral_const, lintegral_const_mul', integral_eq_lintegral_of_nonneg_ae, mul_le_mul_right;
- intervalIntegral.integral_eq_sub_of_hasDerivAt, intervalIntegral.norm_integral_le_integral_norm, intervalIntegral.integral_mono_on, HasFDerivAt.comp_hasDerivAt, ContDiff.continuous_fderiv;
- PiLp.volume_preserving_ofLp, Real.volume_pi_Ioo, EuclideanSpace.norm_eq, convex_iff_forall_pos, Bornology.IsBounded.measure_lt_top.

Verification:
- All four child types elaborate in the contract scope.
- Complete Lean proofs of every child, and of the frozen parent type from cube_geometry and convex_poincare, compile with only propext, Classical.choice and Quot.sound.
- They compile both in a scratch module and when inserted into Submission.lean.
