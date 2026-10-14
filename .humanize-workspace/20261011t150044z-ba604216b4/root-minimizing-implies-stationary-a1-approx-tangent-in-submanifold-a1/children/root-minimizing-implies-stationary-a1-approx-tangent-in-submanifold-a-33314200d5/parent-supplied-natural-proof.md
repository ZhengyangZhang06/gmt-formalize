# Parent-supplied natural-language proof

- Parent DAG node: `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1`
- Child DAG node: `root.minimizing_implies_stationary-a1.approx_tangent_in_submanifold-a1.approx_tangent_le_flat-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 3–6 of the parent-supplied proof of approxTangent_le_submanifold_tangentSpace. The flatness established in its step 2 is now a hypothesis, T is an arbitrary linear subspace, and x need not lie in N. Book: Simon, Introduction to GMT, Ch. 3, Definition 1.4 and Remark 1.5(1) (local book/chapter-03.txt lines 77–86). The resulting inclusion T_xM ⊆ T_xN is used in Ch. 4, 2.6–2.7 (book/chapter-04.txt lines 175–209).
Notation: H^n := μHE[n]. η_r(y) := r⁻¹(y − x), which is Poincare.SimonGMT.Chapter03.blowUpMap x r y. |·| is the Euclidean norm. B(a, s) and B̄(a, s) are the open and closed balls. dist(q, T) := inf over t ∈ T of |q − t| (Metric.infDist q T).
1. Set-up for contradiction. Let q ∈ Q; we show q ∈ T. Suppose q ∉ T. T is a finite-dimensional linear subspace of ℝ^P, hence closed (Submodule.closed_of_finiteDimensional), and it is nonempty since 0 ∈ T. Therefore δ := dist(q, T) > 0 (IsClosed.notMem_iff_infDist_pos).
2. Test function. Let g(y) := max(0, δ/2 − |y − q|).
- g is continuous and g ≥ 0.
- If g(y) ≠ 0 then |y − q| < δ/2; otherwise δ/2 − |y − q| ≤ 0 and g(y) = 0. Conversely, |y − q| < δ/2 implies g(y) > 0.
- Hence g vanishes outside the compact ball B̄(q, δ/2), so g has compact support (HasCompactSupport.intro).
- So g defines f ∈ C_c(ℝ^P, ℝ), the CompactlySupportedContinuousMap ⟨⟨g, continuity⟩, compact support⟩, with f(y) = g(y) for all y.
The parent normalizes |q| = 1 and uses ε = δ/8 and r < ρ/2. Here no normalization is made and the constants of step 4 are used instead; the mathematics is the same.
3. ∫_Q g dH^n > 0. By hypothesis finrank Q = n.
(a) The measure H^n⌞Q is regular (SimonGMT Chapter03 regular_euclideanHausdorffMeasure_restrict_submodule), in particular finite on compact sets. So the continuous, compactly supported g is H^n⌞Q-integrable (Continuous.integrable_of_hasCompactSupport).
(b) The support of the measure H^n⌞Q is exactly Q (SimonGMT support_euclideanHausdorffMeasure_restrict_submodule). Since q ∈ Q and B(q, δ/2) is a neighbourhood of q, (H^n⌞Q)(B(q, δ/2)) > 0 (Measure.mem_support_iff_forall, whose explicit argument is the point q).
(c) B(q, δ/2) ⊆ {g ≠ 0}, so (H^n⌞Q)({g ≠ 0}) > 0. Since g ≥ 0 is integrable, ∫_Q g dH^n > 0 (integral_pos_iff_support_of_nonneg).
4. Constants. |q| + δ > 0. Put ε := δ/(2(|q| + δ)) > 0, so that ε(|q| + δ) = δ/2. Let ρ > 0 be given by the flatness hypothesis for this ε: every z ∈ N with |z − x| < ρ admits t ∈ T with |z − x − t| ≤ ε|z − x|.
5. Vanishing of the blow-up integrals. Fix r with 0 < r < ρ/(|q| + δ). We show ∫_{η_r(M)} g dH^n = 0.
(a) H^n(η_r(M ∖ N)) = 0.
- η_r(M ∖ N) = r⁻¹·A, where A := {y − x : y ∈ M ∖ N} (Set.image_smul, Set.image_image).
- The translation y ↦ y − x is an isometry (dist_sub_right), so H^n(A) = H^n(M ∖ N) = 0 (Isometry.euclideanHausdorffMeasure_image).
- Since r⁻¹ ≠ 0, H^n(r⁻¹·A) = |r⁻¹|^n·H^n(A) = 0 (Measure.euclideanHausdorffMeasure_smul₀).
(b) {g ≠ 0} ∩ η_r(M) ⊆ η_r(M ∖ N). Let y = η_r(z) with z ∈ M and g(y) ≠ 0; it suffices to show z ∉ N. Suppose z ∈ N.
- By step 2, |y − q| < δ/2, so |y| ≤ |y − q| + |q| < |q| + δ/2.
- Since r ≠ 0, z − x = r·y. Hence |z − x| = r|y| ≤ r(|q| + δ) < ρ.
- By step 4 there is t ∈ T with |z − x − t| ≤ ε|z − x|.
- Then r⁻¹t ∈ T and y − r⁻¹t = r⁻¹(z − x − t). So |y − r⁻¹t| ≤ r⁻¹ε|z − x| = ε|y| ≤ ε(|q| + δ) = δ/2.
- Consequently δ = dist(q, T) ≤ |q − r⁻¹t| ≤ |q − y| + |y − r⁻¹t| < δ/2 + δ/2 = δ (infDist_le_dist_of_mem), a contradiction.
(c) {g ≠ 0} is open because g is continuous, hence Borel.
- By Measure.restrict_apply, which needs measurability only of {g ≠ 0} and not of η_r(M): (H^n⌞η_r(M))({g ≠ 0}) = H^n({g ≠ 0} ∩ η_r(M)).
- By (b) and (a), this is ≤ H^n(η_r(M ∖ N)) = 0 (measure_mono_null).
- So g = 0 almost everywhere for H^n⌞η_r(M) (ae_iff), and ∫_{η_r(M)} g dH^n = 0 (integral_eq_zero_of_ae).
6. Conclusion.
- Apply the hypothesis HasApproximateTangentSpaceAt n M x Q to f: the function r ↦ ∫_{η_r(M)} g dH^n tends to ∫_Q g dH^n along 𝓝[>] 0.
- The interval (0, ρ/(|q| + δ)) belongs to 𝓝[>] 0 (Ioo_mem_nhdsGT). So by step 5 this function is eventually 0 along 𝓝[>] 0, and therefore also tends to 0 (Tendsto.congr').
- Since 𝓝[>] 0 is a nontrivial filter on ℝ, limits are unique (tendsto_nhds_unique). Hence ∫_Q g dH^n = 0, contradicting step 3.
- Therefore q ∈ T. As q ∈ Q was arbitrary, Q ≤ T.
Appendix: a verified Lean script for exactly this frozen statement. It compiled in scratch: in /tmp/atsm-v3-q8w/B.lean after import GMT.Ch07.Submission, and inside a byte copy of GMT/Ch07/Submission.lean at proof base c36d11c. Environment: Lean v4.35.0-rc3, Mathlib 25730c7c, SimonGMT 2b366308. #print axioms reports [propext, Classical.choice, Quot.sound]. Place it inside namespace GMT.Ch07, after the contract's noncomputable section and before main_theorem. The contract does not open the scoped notations C_c(·,·) or pointwise set smul, so the script begins with 'open scoped CompactlySupported Pointwise in'. This leaves the elaborated type unchanged.
```lean
open scoped CompactlySupported Pointwise in
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump function
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : C_c(Euclid P, ℝ) := ⟨⟨g, hgc⟩, hgcs⟩
  have hf : ∀ y, f y = g y := fun y => rfl
  -- the plane integral is positive
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- the blow-up integrals vanish for small r
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          r⁻¹ • ((fun y => y - x) '' (M \ N)) := by
        rw [← Set.image_smul, Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- conclusion
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith
```

## Key steps

1. If q ∈ Q ∖ T, then δ = dist(q, T) > 0 because T is closed. The bump g = max(0, δ/2 − |· − q|) lies in C_c and has ∫_Q g dH^n > 0, because spt(H^n⌞Q) = Q and H^n⌞Q is finite on compact sets (finrank Q = n).
2. The blow-up η_{x,r}(M ∖ N) is H^n-null: H^n is translation invariant and scales by |r⁻¹|^n.
3. Take ε = δ/(2(|q| + δ)) and 0 < r < ρ/(|q| + δ). Flatness of N at x along T makes g vanish on η_{x,r}(M ∩ N). So g = 0 H^n-a.e. on η_{x,r}(M) (restriction evaluated on the open set {g ≠ 0}), and ∫_{η_{x,r}(M)} g dH^n = 0.
4. The defining limit along 𝓝[>] 0 then forces ∫_Q g dH^n = 0, a contradiction. Hence Q ≤ T.

## Reference use

### local-project

Queries:
- `cat .humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json (project b4d606db, mathlib 25730c7c)`
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/{Contract,Submission}.lean against workspace GMT/Ch07 (identical); git show c36d11c:GMT/Ch07/Submission.lean | diff - GMT/Ch07/Submission.lean (identical)`
- `python3 -I: read nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/{parent-child-handoff.json,parent-supplied-plan.md,decomposition-v2.json,decomposition-audit-v1.json,decomposition-audit-v2.json,decomposition-review-receipt-v1.json,decomposition-review-receipt-v2.json,decomposition-scope-v1.json,decomposition-scope-v2.json}`
- `python3 -I: dag.json (451 nodes): entries for this node, chart_tangent_space-a1, dsmc_approxTangentPlane_subset_tangentSpace and its four children, dgcr_atg_* nodes; lean_name scan for 'atsm' and 'flat'; issue-workers.json records for issue 998`
- `grep -rl 'atsm_chart_image_flat\|atsm_approxTangent_le_of_flat' nodes dag.json DAG.md issue-workers.json; grep -rn atsm_ GMT/; grep -rln atsm_ simongmt/Poincare`
- `grep -n 'def HasApproximateTangentSpaceAt\|def blowUpMap\|support_euclideanHausdorffMeasure_restrict_submodule\|regular_euclideanHausdorffMeasure_restrict_submodule' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; sed -n 80,200p of that file`
- `grep -n exists_antilipschitzWith mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean; grep -n 'euclideanHausdorffMeasure_smul₀\|Isometry.euclideanHausdorffMeasure_image' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean; grep for ContDiffOn.differentiableOn (Calculus/ContDiff/Defs.lean), bound_of_antilipschitz (Normed/Operator/ContinuousLinearMap.lean), integral_pos_iff_support_of_nonneg (Integral/Bochner/Basic.lean)`
- `sed -n 1,320p GMT/Ch07/Contract.lean (Euclid, IsEmbeddedSubmanifold, tangentSpace, dilation); sed -n 845,875p book/chapter-02.txt; sed -n 60,100p book/chapter-03.txt; sed -n 175,212p book/chapter-04.txt`
- `lake env lean /tmp/atsm-v3-q8w/Types.lean; lake env lean /tmp/atsm-v3-q8w/Assembly.lean; lake env lean /tmp/atsm-v3-q8w/A.lean; lake env lean /tmp/atsm-v3-q8w/B.lean; lake env lean /tmp/atsm-v3-q8w/Inlined.lean (toolchain lean-4.35.0-rc3-linux)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/issue-workers.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-minimizing-implies-stationary-a1-approx-tangent-in-submanifold-a1/decomposition-review-receipt-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-epsilon-regularity-a1-graph-cycle-b5ecd87c13/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-04.txt`
- `/tmp/atsm-v3-q8w/Types.lean`
- `/tmp/atsm-v3-q8w/Assembly.lean`
- `/tmp/atsm-v3-q8w/A.lean`
- `/tmp/atsm-v3-q8w/B.lean`
- `/tmp/atsm-v3-q8w/Inlined.lean`

Snapshot compatibility verified. Project b4d606db and proof base c36d11c: GMT/Ch07/Submission.lean and Contract.lean are byte-identical to the snapshot copies. Mathlib is 25730c7c and SimonGMT is 2b366308. SimonGMT HasApproximateTangentSpaceAt is (finrank P = n) ∧ ∀ f : C_c(E, ℝ), the integrals ∫ y in blowUpMap x r '' M, f y ∂μHE[n] tend to ∫ y in P, f y ∂μHE[n] along 𝓝[>] 0. That is Simon Ch. 3, Definition 1.4. All cited Mathlib and SimonGMT lemmas exist with the signatures used: support and regularity of μHE[n] restricted to Q, antilipschitz coercivity, invariance of μHE under isometries, scaling by smul₀, and restrict_apply on an open set. No project or SimonGMT declaration proves either child; there is no atsm_ match in GMT/ or SimonGMT. The accepted dsmc_approxTangentPlane_subset_tangentSpace (general r) and its children sit on an unintegrated branch with different frozen types. dgcr_atg_approxTangent_le_of_flat has a different, localized type. So nothing is reused. Both child types elaborate. A sorry-free conditional assembly with the exact sibling contract proves the exact frozen parent. Complete scratch proofs of both children compile using only propext, Classical.choice and Quot.sound, including when inlined into a byte copy of Submission.lean. Both names are unreserved by any other branch. No inline square-matrix or typeclass-sensitive construction occurs; Q ≤ T is the Submodule order, and the norms are Euclidean (PiLp 2).
