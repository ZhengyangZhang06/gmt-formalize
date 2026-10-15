# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1`
- Child DAG node: `root.dimension_reduction_results-a1.integer_density_tangent_planes-a1.cone_constant_density_planar-a1.regular_point_support-a1.submanifold_subset_support-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 5 of the supplied proof of the selected node (M ∩ B_ρ(y) ⊆ spt T, the bump-form argument (a)–(g)). Here it is stated for an arbitrary open set G ⊆ U on which T = m[[M]], with both B_ρ(y) and B_{ρ₀}(y) of the supplied proof replaced by G. The supplied proof takes some facts from its steps 2–3; here they are obtained as follows. M is Borel by the sibling embedded_locally_closed. Hⁿ(M ∩ K) < ∞ for the compact ball K ⊆ G is a hypothesis. The integrand is integrable because it is bounded by ‖α‖ on a set of finite measure, so compactness of M ∩ K is not needed.
Conventions. Hⁿ := μHE[n], ω_n := unitBallVolume n, B_r(x) := ball x r. For T ∈ 𝒟_n(U), "T vanishes on W" means T(ω) = 0 for each ω ∈ 𝒟ⁿ(U) (TestFormOn U n) with tsupport ω ⊆ W. zeroRegion T is the union of the open sets W with closure(W) compact and closure(W) ⊆ U on which T vanishes, and spt T = T.support = U ∖ zeroRegion T (Simon 6.2.11). Λⁿ = Covector (Euclid P) n carries the operator norm of continuous alternating maps, and Λ_n = MultiVector P n = (Λⁿ →L[ℝ] ℝ) its operator norm, so |ξ(z)(β)| ≤ ‖ξ(z)‖·‖β‖.
0. (Facts about M and ξ.)
 (i) By the sibling embedded_locally_closed (Submission.dimred_rpd_embedded_locally_closed with r = 1, d = n), M is a measurable set.
 (ii) By IsOrientation n M ξ, ξ is continuous on M, and for every z ∈ M there is a subspace Q_z with IsUnitOrientationOf (ξ(z)) Q_z. So by the sibling unit_orientation_bounds (Submission.imsupp_unit_orientation_ne_zero_norm_le_one), ξ(z) ≠ 0 and ‖ξ(z)‖ ≤ 1 for every z ∈ M.
1. (Setting up the contradiction.) Let x ∈ M ∩ G. Then x ∈ U because G ⊆ U, so it remains to show x ∉ zeroRegion T. Suppose instead that x ∈ zeroRegion T. Then x ∈ W for some open set W (with closure(W) compact and contained in U) on which T vanishes.
2. (A covector α with ξ(x)(α) = 1.) By step 0(ii), ξ(x) ≠ 0, so there is α₀ ∈ Λⁿ with ξ(x)(α₀) ≠ 0; otherwise ξ(x) would be the zero functional. Put α := ξ(x)(α₀)⁻¹·α₀. By linearity, ξ(x)(α) = ξ(x)(α₀)⁻¹·ξ(x)(α₀) = 1.
3. (Continuity.) The function z ↦ ξ(z)(α) is continuous on M: ξ is continuous on M, and evaluating a continuous linear map at the fixed covector α is continuous (ContinuousOn.clm_apply with a constant). Since ξ(x)(α) = 1, there is ε₁ > 0 such that |ξ(z)(α) − 1| < 1/2, hence ξ(z)(α) > 1/2, for every z ∈ M with |z − x| < ε₁.
4. (Radius.) W ∩ G is open and contains x, so there is r > 0 with B_r(x) ⊆ W ∩ G. Put ε := min(r, ε₁) > 0. Then ε ≤ ε₁ and closedBall(x, ε/2) ⊆ B_ε(x) ⊆ B_r(x) ⊆ W ∩ G.
5. (The bump form.) Let g be Mathlib's smooth bump function centred at x with inner radius ε/4 and outer radius ε/2 (a ContDiffBump x with rIn = ε/4 and rOut = ε/2; note 0 < ε/4 < ε/2). It has these properties:
 - g is C^∞ and 0 ≤ g ≤ 1;
 - g = 1 on closedBall(x, ε/4) (one_of_mem_closedBall);
 - tsupport g = closedBall(x, ε/2) (tsupport_eq), so g(z) = 0 for z ∉ closedBall(x, ε/2);
 - g has compact support.
 Define the n-form ω(z) := g(z)·α. It is C^∞ as the product of the smooth function g and the constant α. It has compact support (HasCompactSupport.smul_right), and tsupport ω ⊆ tsupport g = closedBall(x, ε/2) (tsupport_smul_subset_left). Since closedBall(x, ε/2) ⊆ W ∩ G ⊆ U, we get ω ∈ 𝒟ⁿ(U), i.e. ω is a TestFormOn U n.
6. (T(ω) = 0.) tsupport ω ⊆ closedBall(x, ε/2) ⊆ W and T vanishes on W, so T(ω) = 0.
7. (T(ω) as an integral.) tsupport ω ⊆ closedBall(x, ε/2) ⊆ G, so the representation hypothesis gives T(ω) = m·∫_M h dHⁿ with h(z) := ξ(z)(ω(z)). By linearity of ξ(z), h(z) = ξ(z)(g(z)·α) = g(z)·ξ(z)(α).
8. (Properties of h.) Let μ := Hⁿ⌞M (μHE[n].restrict M) and K := closedBall(x, ε/2).
 (a) h is continuous on M, as the product of the continuous g and the function of step 3. Since M is measurable (step 0(i)), h is a.e.-strongly measurable for μ (ContinuousOn.aestronglyMeasurable).
 (b) h(z) = 0 for z ∉ K, because g(z) = 0 there.
 (c) For z ∈ M, |h(z)| = |g(z)|·|ξ(z)(α)| ≤ 1·‖ξ(z)‖·‖α‖ ≤ ‖α‖, using 0 ≤ g ≤ 1 and step 0(ii). Since μ-almost every point lies in M, |h| ≤ ‖α‖ μ-a.e.
 (d) K is compact and K ⊆ G, so Hⁿ(M ∩ K) < ∞ by hypothesis. Since K is measurable, μ(K) = Hⁿ(K ∩ M) < ∞.
 (e) (Integrability.) By (a), (c) and (d), h is integrable on K with respect to μ, being a bounded a.e.-strongly measurable function on a set of finite measure (Measure.integrableOn_of_bounded). By (b), h vanishes off K, so h is μ-integrable (IntegrableOn.integrable_of_forall_notMem_eq_zero).
 (f) (Nonnegativity.) h ≥ 0 μ-a.e. Let z ∈ M. If z ∈ K, then |z − x| ≤ ε/2 < ε ≤ ε₁, so ξ(z)(α) > 1/2 > 0 by step 3; with g(z) ≥ 0 this gives h(z) ≥ 0. If z ∉ K, then h(z) = 0 by (b).
 (g) (Where h is positive.) Let z ∈ M ∩ B_{ε/4}(x). Then z ∈ closedBall(x, ε/4), so g(z) = 1. Also |z − x| < ε/4 < ε₁, so h(z) = ξ(z)(α) > 1/2 > 0. Hence M ∩ B_{ε/4}(x) ⊆ {h ≠ 0} ∩ M.
9. (M has positive measure near x.) We claim Hⁿ(M ∩ B_{ε/4}(x)) > 0. Suppose instead that Hⁿ(M ∩ B_{ε/4}(x)) = 0. For every s ∈ (0, ε/4), monotonicity gives Hⁿ(M ∩ B_s(x)) = 0, so Hⁿ(M ∩ B_s(x))/(ω_n sⁿ) = 0, since in [0, ∞] zero divided by anything is zero. So this ratio is eventually 0 as s ↓ 0, and it tends to 0. But M is an embedded C¹ n-submanifold and x ∈ M, so by the sibling submanifold_density_one (Submission.dimred_rpd_submanifold_density_one) the same ratio tends to 1 as s ↓ 0. The filter s ↓ 0 (𝓝[>] 0) is nontrivial and limits in [0, ∞] are unique, so 1 = 0, which is absurd.
10. (The integral is positive.) For a μ-integrable function that is ≥ 0 μ-a.e., ∫ h dμ > 0 if and only if μ({h ≠ 0}) > 0 (integral_pos_iff_support_of_nonneg_ae, applicable by 8(e) and 8(f)). By 8(g), step 9 and Measure.le_restrict_apply, μ({h ≠ 0}) ≥ Hⁿ({h ≠ 0} ∩ M) ≥ Hⁿ(M ∩ B_{ε/4}(x)) > 0. Hence ∫_M h dHⁿ = ∫ h dμ > 0. This is the supplied proof's bound ∫_M h dHⁿ ≥ ∫_{M ∩ B_{ε/4}(x)} h dHⁿ ≥ ½·Hⁿ(M ∩ B_{ε/4}(x)) > 0, stated as a positivity criterion.
11. (Contradiction.) By steps 6 and 7, 0 = T(ω) = m·∫_M h dHⁿ. But m ≠ 0, so (m : ℝ) ≠ 0, and ∫_M h dHⁿ > 0 by step 10, so the product is nonzero. This contradiction shows x ∉ zeroRegion T, hence x ∈ U ∖ zeroRegion T = spt T. Since x ∈ M ∩ G was arbitrary, M ∩ G ⊆ spt T. ∎

Formalization notes:
- In the contract, IsTestForm ω is ContDiff ℝ ∞ ω ∧ HasCompactSupport ω, where ∞ is ((⊤ : ℕ∞) : WithTop ℕ∞). Write that exponent explicitly: under the contract's `open scoped ENNReal`, a bare ∞ elaborates as an element of ℝ≥0∞.
- x ∈ zeroRegion T unfolds by Set.mem_sUnion.1 to ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩.
- When naming the measure with set/let, ascribe its type, `set μ : Measure (Euclid P) := μHE[n]`; otherwise the BorelSpace instance problem is stuck.

Lean reference proof (verified). The declaration below was compiled with `lake env lean` (Lean v4.35.0-rc3, Mathlib 25730c7c) after `import GMT.Ch07.Submission`, inside `namespace GMT.Ch07` with the contract `open`s (Filter Function Set MeasureTheory Metric; scoped ENNReal Topology; Poincare.SimonGMT.Chapter06; Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)), with the three sibling declarations above it. `#print axioms` reports only propext, Classical.choice and Quot.sound. It follows the numbered proof step by step.

```lean
theorem Submission.idtp_ccd_rps_submanifold_subset_support : ∀ (P n : ℕ) (U G M : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : ℤ) (ξ : Euclid P → MultiVector P n), IsOpen G → G ⊆ U → m ≠ 0 → IsEmbeddedSubmanifold 1 n M → IsOrientation n M ξ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ G → μHE[n] (M ∩ K) ≠ ∞) → (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ G → T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) → M ∩ G ⊆ T.support := by
  intro P n U G M T m ξ hG hGU hm hM hξ hfin hrep x hx
  obtain ⟨hxM, hxG⟩ := hx
  refine ⟨hGU hxG, fun hxZ => ?_⟩
  obtain ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩ := Set.mem_sUnion.1 hxZ
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 n M hM).1
  -- (a) a covector α with ξ(x)(α) = 1, and the bound ‖ξ(z)‖ ≤ 1 on M
  obtain ⟨Qx, -, hQx⟩ := hξ.2 x hxM
  have hξx := (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n (ξ x) Qx hQx).1
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : Covector (Euclid P) n, ξ x α₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hξx (ContinuousLinearMap.ext fun a => by simpa using h a)
  obtain ⟨α, hα⟩ : ∃ α : Covector (Euclid P) n, ξ x α = 1 :=
    ⟨(ξ x α₀)⁻¹ • α₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hα₀]⟩
  have hnorm : ∀ z ∈ M, ‖ξ z‖ ≤ 1 := by
    intro z hz
    obtain ⟨Q, -, hQ⟩ := hξ.2 z hz
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n (ξ z) Q hQ).2
  -- (b) continuity of z ↦ ξ(z)(α) on M at x
  have hcont : ContinuousOn (fun z => ξ z α) M := hξ.1.clm_apply continuousOn_const
  obtain ⟨ε₁, hε₁, hε₁'⟩ := Metric.continuousWithinAt_iff.1 (hcont x hxM) (1 / 2) (by norm_num)
  have hhalf : ∀ z ∈ M, dist z x < ε₁ → 1 / 2 < ξ z α := by
    intro z hz hzx
    have h := hε₁' hz hzx
    rw [Real.dist_eq, hα] at h
    linarith [(abs_lt.1 h).1]
  -- (c) the radius ε
  obtain ⟨r, hr, hrWG⟩ := Metric.isOpen_iff.1 (hWo.inter hG) x ⟨hxW, hxG⟩
  set ε := min r ε₁ with hεdef
  have hε : 0 < ε := lt_min hr hε₁
  have hεr : ε ≤ r := min_le_left _ _
  have hεε₁ : ε ≤ ε₁ := min_le_right _ _
  have hcb : closedBall x (ε / 2) ⊆ W ∩ G :=
    (closedBall_subset_ball (by linarith)).trans ((ball_subset_ball hεr).trans hrWG)
  -- (d) the bump form ω = g·α
  let g : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let ω : DifferentialForm (Euclid P) n := fun z => g z • α
  have hωsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := g.contDiff.smul contDiff_const
  have hωcpt : HasCompactSupport ω := g.hasCompactSupport.smul_right
  have hωts : tsupport ω ⊆ closedBall x (ε / 2) :=
    (tsupport_smul_subset_left (fun z => g z) (fun _ => α)).trans g.tsupport_eq.subset
  let ωU : TestFormOn U n :=
    ⟨ω, ⟨hωsmooth, hωcpt⟩, hωts.trans (hcb.trans fun z hz => hGU hz.2)⟩
  have hT0 : T ωU = 0 := hWv ωU (hωts.trans (hcb.trans inter_subset_left))
  have hTrep := hrep ωU (hωts.trans (hcb.trans inter_subset_right))
  -- (e) the integrand h(z) = g(z)·ξ(z)(α)
  have hval : ∀ z, ξ z ((ωU : DifferentialForm (Euclid P) n) z) = g z * ξ z α := by
    intro z
    show ξ z (g z • α) = g z * ξ z α
    rw [map_smul, smul_eq_mul]
  have hzero : ∀ z, z ∉ closedBall x (ε / 2) → g z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (by rw [g.tsupport_eq]; exact hz)
  set μ : Measure (Euclid P) := μHE[n] with hμdef
  set h : Euclid P → ℝ := fun z => ξ z ((ωU : DifferentialForm (Euclid P) n) z) with hhdef
  have hcontOn : ContinuousOn h M := by
    have : ContinuousOn (fun z => g z * ξ z α) M := g.continuous.continuousOn.mul hcont
    exact this.congr fun z _ => hval z
  have hmeas : AEStronglyMeasurable h (μ.restrict M) := hcontOn.aestronglyMeasurable hMmeas
  have hfinK : μ (M ∩ closedBall x (ε / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall _ _) (hcb.trans inter_subset_right)
  have hintK : IntegrableOn h (closedBall x (ε / 2)) (μ.restrict M) := by
    refine Measure.integrableOn_of_bounded (M := ‖α‖) ?_ hmeas ?_
    · rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
      exact hfinK
    · have hM' : ∀ᵐ z ∂(μ.restrict M), z ∈ M := ae_restrict_mem hMmeas
      refine ae_restrict_of_ae ?_
      filter_upwards [hM'] with z hz
      rw [hhdef]
      dsimp only
      rw [hval z, norm_mul]
      have h1 : ‖g z‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (g.nonneg)]
        exact g.le_one
      have h2 : ‖ξ z α‖ ≤ ‖α‖ :=
        ((ξ z).le_opNorm α).trans (by nlinarith [hnorm z hz, norm_nonneg α])
      nlinarith [norm_nonneg (g z), norm_nonneg (ξ z α)]
  have hint : Integrable h (μ.restrict M) :=
    hintK.integrable_of_forall_notMem_eq_zero fun z hz => by
      rw [hhdef]; dsimp only; rw [hval z, hzero z hz, zero_mul]
  have hnonneg : 0 ≤ᵐ[μ.restrict M] h := by
    filter_upwards [ae_restrict_mem hMmeas] with z hz
    show (0 : ℝ) ≤ h z
    rw [hhdef]; dsimp only; rw [hval z]
    by_cases hzb : z ∈ closedBall x (ε / 2)
    · have : 1 / 2 < ξ z α := hhalf z hz (by
        rw [mem_closedBall] at hzb; linarith)
      exact mul_nonneg g.nonneg (by linarith)
    · rw [hzero z hzb, zero_mul]
  -- (f) positive measure of M near x
  have hpos : 0 < μ (M ∩ ball x (ε / 4)) := by
    rw [pos_iff_ne_zero]
    intro h0
    have hlim := Submission.dimred_rpd_submanifold_density_one P n M x hM hxM
    have hev : (fun s : ℝ => μHE[n] (M ∩ ball x s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)))
        =ᶠ[𝓝[>] 0] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 4 by positivity)] with s hs
      have : μHE[n] (M ∩ ball x s) = 0 :=
        measure_mono_null (inter_subset_inter_right _ (ball_subset_ball hs.2.le)) h0
      rw [this, ENNReal.zero_div]
    exact one_ne_zero (tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds)
  have hsupp : μ (M ∩ ball x (ε / 4)) ≤ (μ.restrict M) (support h) := by
    refine le_trans (measure_mono ?_) (Measure.le_restrict_apply _ _)
    rintro z ⟨hzM, hzb⟩
    refine ⟨?_, hzM⟩
    rw [mem_support, hhdef]; dsimp only; rw [hval z]
    have hg1 : g z = 1 := g.one_of_mem_closedBall (ball_subset_closedBall hzb)
    have : 1 / 2 < ξ z α := hhalf z hzM (by rw [mem_ball] at hzb; linarith)
    rw [hg1, one_mul]
    linarith
  have hIpos : 0 < ∫ z in M, h z ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hnonneg hint).2 (hpos.trans_le hsupp)
  -- (g) contradiction
  rw [hTrep] at hT0
  exact mul_ne_zero (Int.cast_ne_zero.2 hm) hIpos.ne' hT0
```

## Key steps

1. M is Borel (embedded_locally_closed), and ξ(z) ≠ 0 with ‖ξ(z)‖ ≤ 1 on M (unit_orientation_bounds). Pick α with ξ(x)(α) = 1, and ε₁ > 0 with ξ(z)(α) > 1/2 on M ∩ B_{ε₁}(x), by continuity of ξ on M.
2. If x ∈ zeroRegion T through an open W, take ε ≤ ε₁ with B_ε(x) ⊆ W ∩ G. The bump form ω = g·α, with g = 1 on closedBall(x, ε/4) and tsupport g = closedBall(x, ε/2), is a test form supported in W, so T(ω) = 0.
3. T(ω) = m·∫_M g·ξ(α) dHⁿ. The integrand is bounded by ‖α‖, measurable on M, vanishes off closedBall(x, ε/2), which has finite Hⁿ⌞M measure, is ≥ 0 on M, and is > 1/2 on M ∩ B_{ε/4}(x).
4. Hⁿ(M ∩ B_{ε/4}(x)) > 0 because the density ratio of M at x tends to 1 (submanifold_density_one). So ∫_M g·ξ(α) dHⁿ > 0 and T(ω) ≠ 0, since m ≠ 0, a contradiction. Hence x ∈ spt T.

## Reference use

### local-project

Queries:
- `cmp <snapshot>/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean; git rev-parse HEAD; git -C .lake/packages/mathlib rev-parse HEAD; git -C .lake/packages/simongmt rev-parse HEAD (checked against manifest.json)`
- `grep -n 'def zeroRegion|def support|def VanishesOn|theorem|lemma' SimonGMT Chapter06/CurrentLocalEquality.lean; sed -n 80,200p Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn); sed -n 20,80p Chapter06/Forms.lean (Covector, DifferentialForm, IsTestForm); sed -n 1,100p Chapter06/Mass.lean (massAdmissibleOn, massOn)`
- `python3 -I scans of dag.json: nodes under cone_constant_density_planar-a1; lean_statements with IsEmbeddedSubmanifold plus MeasurableSet/IsCompact/closure; accepted lemmas whose statements mention support together with VanishesOn/zeroRegion/massOn; statements with IsOrientation or 'closure M' together with .support; local representations 'T ω = _ * ∫ x in M'; records (status, candidate, depends_on) of dimred_rpd_embedded_locally_closed, dimred_rpd_submanifold_density_one, imsupp_unit_orientation_ne_zero_norm_le_one, dimred_rpd_massOn_eq_mult_measure, dimred_regular_point_density`
- `git show 1d91497901e9a040bb92dab7cea2968379e0e3a2:GMT/Ch07/Submission.lean (parent proof base = bare contract); git show {6da66b1e,e8842d90,2e5d20d4,5fcaddaa}:GMT/Ch07/Submission.lean | grep '^theorem Submission.' (accepted candidates contain only their declared dependencies)`
- `scan of nodes/*/parent-child-handoff.json resolved_dependencies (385 non-empty, including cross-branch); nodes/root-dimension-reduction-results-a1-regular-point-density-a1/decomposition-v1.json and nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json (precedent for reusing accepted declarations, with 'Reuse note' natural proofs)`
- `grep -c idtp_ccd_rps dag.json; grep -rl idtp_ccd_rps nodes/ ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission.lean ../.swarm-worktrees/*/gmt-ch07/GMT/Ch07/Submission/ (no match)`
- `grep -rn 'theorem integral_pos_iff_support_of_nonneg_ae|setIntegral_eq_zero_of_forall_eq_zero|integrableOn_of_bounded|integrable_of_forall_notMem_eq_zero|ContinuousOn.aestronglyMeasurable|le_restrict_apply|IsOpen.inter_closure|tsupport_smul_subset_left|ContinuousOn.clm_apply' <snapshot>/mathlib/Mathlib; grep -n 'tsupport_eq|one_of_mem_closedBall|nonneg|le_one|hasCompactSupport|contDiff' <snapshot>/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `sed -n 290,310p book/chapter-06.txt (Simon 6.2.11-2.12); sed -n 586,600p book/chapter-07.txt (Simon 7.4.1)`
- `lake env lean /tmp/rps-decomp-4RlzzQ/{Probe,Assembly,C1,C2,Full,FromJson}.lean with #print axioms`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b656aa468/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-integer-density-tangent-planes-a1-7b656aa468/parent-supplied-plan.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-locally-closed-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1-density-one-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-support-eq-measure-sup-2d6f974584/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-regular-point-density-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-density-one-implies-regular-a1-limsup-mass-bound-a1-projected-comparison-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-components-are-minimizing-a1-integer-multiplicity-sub-a1-f90e8352bc/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Neighborhoods.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Support.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-07.txt`
- `/tmp/rps-decomp-4RlzzQ/Assembly.lean`
- `/tmp/rps-decomp-4RlzzQ/C1.lean`
- `/tmp/rps-decomp-4RlzzQ/C2.lean`
- `/tmp/rps-decomp-4RlzzQ/Full.lean`
- `/tmp/rps-decomp-4RlzzQ/FromJson.lean`

Pins match the manifest. The snapshot project commit equals workspace HEAD b4d606d, Mathlib is 25730c7c and SimonGMT is 2b36630. The snapshot Contract.lean is byte-identical to the workspace Contract.lean and Submission.lean.

SimonGMT definitions match the supplied proof: T.support = U ∖ zeroRegion T, where zeroRegion T is the union of the open W with compact closure inside U on which T.VanishesOn W holds. TestFormOn U n is {ω | ContDiff ℝ ∞ ω ∧ HasCompactSupport ω ∧ tsupport ω ⊆ U}.

The selected node cannot reach the lemmas its proof cites. Its proof cites the accepted Submission.imsupp_unit_orientation_ne_zero_norm_le_one (candidate 2e5d20d4) and Submission.dimred_rpd_submanifold_density_one (e8842d90). Its step 2 is the accepted Submission.dimred_rpd_embedded_locally_closed (6da66b1e). Yet the node has no declared dependencies, and its proof base 1d91497 is the bare contract. Accepted candidates contain only their declared dependencies, and the DAG precedent reuses accepted declarations as children at identical frozen types. Hence the three reuse children; their lean_statements are byte-identical to dag.json.

No accepted or pending lemma states either support inclusion. The names idtp_ccd_rps_* have no match in dag.json, nodes/ or any worktree Submission.

Mathlib 25730c7c provides every lemma used by the new children's proofs: ContDiffBump (tsupport_eq, one_of_mem_closedBall, nonneg, le_one, contDiff, hasCompactSupport), setIntegral_eq_zero_of_forall_eq_zero, Measure.integrableOn_of_bounded, IntegrableOn.integrable_of_forall_notMem_eq_zero, ContinuousOn.aestronglyMeasurable, integral_pos_iff_support_of_nonneg_ae, Measure.le_restrict_apply, IsOpen.inter_closure and ContinuousOn.clm_apply.

Lean check: all child types elaborate. The assembly proves the frozen parent type from the children. Both new children are fully proved. FromJson.lean, built from this JSON plus the accepted reused proofs, proves Submission.idtp_ccd_regular_point_support with no sorry and axioms propext, Classical.choice and Quot.sound.
