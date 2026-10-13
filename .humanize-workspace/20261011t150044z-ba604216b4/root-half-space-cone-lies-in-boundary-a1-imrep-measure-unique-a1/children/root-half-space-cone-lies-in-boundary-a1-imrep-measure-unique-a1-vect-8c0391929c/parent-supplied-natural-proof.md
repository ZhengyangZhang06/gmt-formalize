# Parent-supplied natural-language proof

- Parent DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1`
- Child DAG node: `root.half_space_cone_lies_in_boundary-a1.imrep_measure_unique-a1.vector_density_ae_eq-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: step 2 of the parent proof of representation independence of θH^n⌞M (Simon Ch. 6, 3.2(3)), with its preliminaries 1(a), 1(c), 1(d): test T on the forms ω = gα for all n-covectors α and apply the Banach-valued fundamental lemma of the calculus of variations on the open set U (Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, which needs no local finiteness of the measure).

Notation. M_k = R_k.carrier (Borel, M_k ⊆ U), θ_k = R_k.mult (measurable, ℕ-valued, θ_k ≥ 1 on M_k), ξ_k = R_k.orient (k = 1, 2); H = μHE[n]; ν := H⌞(M_1 ∪ M_2), so ν ≤ H; Λ := MultiVector P n with the operator norm (a real Banach space); F_k(x) := 1_{M_k}(x)·θ_k(x)·ξ_k(x) ∈ Λ; Θ_k(x) := 1_{M_k}(x)·θ_k(x) ∈ [0, ∞); f := F_1 − F_2. The claim is F_1(x) = F_2(x) for ν-a.e. x.
1. (Measurability.) θ_k is measurable and ξ_k is a.e.-strongly measurable for H⌞M_k (R_k.aestronglyMeasurable_orient), so x ↦ θ_k(x)ξ_k(x) is a.e.-strongly measurable for H⌞M_k; as M_k is measurable, its indicator F_k is a.e.-strongly measurable for H (Mathlib aestronglyMeasurable_indicator_iff), hence for ν ≤ H and every restriction of ν. Consequently f, g·f (g continuous) and x ↦ g(x)·F_k(x)(α) (evaluation at a covector α is continuous on Λ) are a.e.-strongly measurable for ν.
2. (Pointwise bound; parent 1(c), 1(d).) By R_k.orients, for H-a.e. x ∈ M_k there is a subspace Q with IsUnitOrientationOf (ξ_k(x)) Q, hence ‖ξ_k(x)‖ ≤ 1 by the sibling lemma unit_orientation_norm_le_one. So for H-a.e. x: if x ∈ M_k then ‖F_k(x)‖ ≤ θ_k(x)·‖ξ_k(x)‖ ≤ θ_k(x) = Θ_k(x) (‖c·L‖ ≤ |c|·‖L‖); if x ∉ M_k then F_k(x) = 0 = Θ_k(x). Thus ‖F_k‖ ≤ Θ_k H-a.e., hence ν-a.e.
3. (Θ_k is integrable on compact subsets of U; parent 1(a).) For compact K ⊆ U, ∫_K Θ_k dH = ∫_{M_k ∩ K} θ_k dH < ∞ by R_k.locallyIntegrable_mult. So Θ_k is H-integrable on K, and ν-integrable on K because ν ≤ H.
4. (f is locally integrable on U with respect to ν.) Let x ∈ U and choose r > 0 with B_r(x) ⊆ U. Then K := closedBall(x, r/2) is a compact neighbourhood of x contained in U. On K, f is ν-a.e.-strongly measurable (step 1) and ‖f‖ ≤ ‖F_1‖ + ‖F_2‖ ≤ Θ_1 + Θ_2 ν-a.e. (step 2), where Θ_1 + Θ_2 is ν-integrable on K (step 3); hence f is ν-integrable on K. Since K ∈ 𝓝[U] x, f is locally integrable on U with respect to ν.
5. (Vanishing moments.) Let g : ℝ^P → ℝ be C^∞ with compact support and tsupport g ⊆ U, and let C ≥ 0 with |g| ≤ C everywhere (g is continuous with compact support).
 (a) For every n-covector α, ω_α(x) := g(x)·α is a test form in U: it is C^∞ (a smooth scalar function times a constant covector), it has compact support (its support is contained in the support of g), and tsupport ω_α ⊆ tsupport g ⊆ U. So ω_α ∈ TestFormOn U n, and by R_k.Represents T, T(ω_α) = R_k.action(ω_α) = ∫_{M_k} θ_k(x)·ξ_k(x)(g(x)α) dH(x) for k = 1, 2.
 (b) For every α and k the real function h_k(x) := g(x)·F_k(x)(α) is ν-integrable: it is a.e.-strongly measurable (step 1), vanishes off tsupport g, and |h_k(x)| ≤ |g(x)|·‖F_k(x)‖·‖α‖ ≤ C‖α‖·1_{tsupport g}(x)·Θ_k(x) ν-a.e. (step 2), the bound being ν-integrable by step 3 with K = tsupport g (compact, ⊆ U).
 (c) ∫ h_k dν = T(ω_α): by linearity of ξ_k(x), h_k(x) = 1_{M_k}(x)·θ_k(x)·ξ_k(x)(g(x)α); the integral of the indicator of the measurable set M_k equals the integral over M_k (Mathlib integral_indicator), and ν⌞M_k = H⌞(M_k ∩ (M_1 ∪ M_2)) = H⌞M_k; hence ∫ h_k dν = ∫_{M_k} θ_k ξ_k(gα) dH = R_k.action(ω_α) = T(ω_α) by (a).
 (d) The Λ-valued function g·f is ν-integrable: it is a.e.-strongly measurable (step 1) and ‖g(x)f(x)‖ ≤ C·1_{tsupport g}(x)·(Θ_1(x) + Θ_2(x)) ν-a.e. Let I := ∫ g·f dν ∈ Λ. Evaluation at α commutes with the Bochner integral (Mathlib ContinuousLinearMap.integral_apply), and (g(x)f(x))(α) = h_1(x) − h_2(x); by (b) and (c), I(α) = ∫ h_1 dν − ∫ h_2 dν = T(ω_α) − T(ω_α) = 0. As α is arbitrary, I = 0.
6. (Fundamental lemma.) ℝ^P is a finite-dimensional real normed space with its Borel σ-algebra, Λ is a real Banach space, U is open, f is locally integrable on U with respect to ν (step 4), and ∫ g·f dν = 0 for every C^∞ function g with compact support and tsupport g ⊆ U (step 5). By Mathlib IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero, for ν-a.e. x, x ∈ U implies f(x) = 0.
7. (Conclusion.) ν = H⌞(M_1 ∪ M_2) is carried by the measurable set M_1 ∪ M_2 ⊆ U (Mathlib ae_restrict_mem; R_k.carrier_subset), so ν-a.e. x lies in U and therefore f(x) = 0, i.e. 1_{M_1}(x)θ_1(x)ξ_1(x) = 1_{M_2}(x)θ_2(x)ξ_2(x) for ν-a.e. x. ∎

Lean implementation notes (all verified by the reference implementation below). At this Mathlib pin, instance search does NOT synthesize ContinuousENorm, NormSMulClass ℝ or TopologicalSpace.PseudoMetrizableSpace for MultiVector P n = Covector (Euclid P) n →L[ℝ] ℝ: the strong topology of a CLM space over a ContinuousAlternatingMap domain is not reducibly the norm topology (the two topologies are equal by rfl). Hence: (i) never state Integrable / LocallyIntegrableOn for Λ-valued functions as fresh terms; obtain those goals from `hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν) (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom` and from `rw [ContinuousLinearMap.integral_apply ?hint α]`, and close them with Integrable.mono' (real dominating functions) and AEStronglyMeasurable terms built from the IMRep fields (accepted by exact up to defeq); (ii) prove LocallyIntegrableOn directly from its definition with closed balls (locallyIntegrableOn_iff needs the missing PseudoMetrizableSpace instance); (iii) use ContinuousLinearMap.opNorm_smul_le instead of norm_smul (NormSMulClass is missing); norm_sub_le works (the explicit (E := MultiVector P n) in the reference code is optional). The real-valued integrals of steps 5(b),(c) have no instance problems.

Lean reference implementation (kernel-checked during this decomposition against GMT.Ch07.Submission, Lean v4.35.0-rc3, Mathlib 25730c7c; place inside `namespace GMT.Ch07` / `namespace Submission` with the contract's opens; #print axioms gives propext, Classical.choice, Quot.sound):
open scoped ContDiff Pointwise in
theorem imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- pointwise bound ‖F R‖ ≤ θ R, a.e.
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- θ R is integrable on compact subsets of U
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier, Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · have h1 := (hFbound R₁)
      have h2 := (hFbound R₂)
      filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous h1),
        ae_restrict_of_ae (hνle.absolutelyContinuous h2)] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := by
            exact norm_sub_le (E := MultiVector P n) (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test form `ω = g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    -- `θ R` restricted to `tsupport g` is integrable
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure hνle
    -- the scalar identity `∫ g F_R(α) dν = T(gα)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, ContinuousLinearMap.smul_apply, smul_eq_mul,
            map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    -- integrability of the scalar integrands
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact ((hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle)
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · calc ‖F R₁ x - F R₂ x‖ ≤ ‖F R₁ x‖ + ‖F R₂ x‖ := by
                        exact norm_sub_le (E := MultiVector P n) (F R₁ x) (F R₂ x)
                    _ ≤ θ R₁ x + θ R₂ x := add_le_add hx1 hx2
        · have : g x = 0 := image_eq_zero_of_notMem_tsupport hx'
          rw [this, zero_smul, Pi.add_apply, indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

## Key steps

1. F_k = 1_{M_k}θ_kξ_k is a.e.-strongly measurable and ‖F_k‖ ≤ 1_{M_k}θ_k H^n-a.e., using ‖ξ_k‖ ≤ 1 (sibling unit_orientation_norm_le_one).
2. R_k.locallyIntegrable_mult makes F_1 − F_2 locally integrable on U for ν = H^n⌞(M_1 ∪ M_2).
3. For smooth compactly supported g in U and every covector α, ω = gα is a test form in U and (∫ g(F_1 − F_2) dν)(α) = R_1.action(ω) − R_2.action(ω) = T(ω) − T(ω) = 0.
4. The Banach-valued fundamental lemma on the open set U gives F_1 = F_2 ν-a.e. on U, hence ν-a.e., since ν is carried by M_1 ∪ M_2 ⊆ U.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); cat local-references/123e8435b4a2469b/manifest.json`
- `sed -n 1,280p simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean (blowUpMap, HasApproximateTangentSpaceAt, HasApproximateTangentSpaceAt.unique)`
- `grep -n Covector simongmt/Poincare/SimonGMT/Chapter06/Forms.lean; sed -n 100,200p simongmt/Poincare/SimonGMT/Chapter06/Currents.lean (testFormOnSubmodule, TestFormOn, GeometricCurrentOn)`
- `grep -rn wedgeCovectors_apply_det simongmt/Poincare/SimonGMT (Chapter06/FormsDuality.lean; Unknown identifier after import GMT.Ch07.Submission)`
- `grep -n theorem mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean; sed -n 118,240p (IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero)`
- `sed -n 60,185p mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean (euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image)`
- `grep -rn det_to_matrix_orthonormalBasis_real mathlib/Mathlib; grep -rn eq_smul_basis_det mathlib/Mathlib; sed -n 150,300p mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean (volumeForm_robust', abs_volumeForm_apply_le, abs_volumeForm_apply_of_orthonormal)`
- `grep -rn continuous_of_finiteDimensional mathlib/Mathlib (no multilinear version); grep -n mkContinuous mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `grep -n integral_apply mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean; grep -n locallyIntegrableOn_iff mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean; grep -n subset_image_sdiff mathlib/Mathlib/Data/Set/Image.lean`
- `python3 census of lean_name fields in dag.json; grep -rhoE lean_name nodes dag.json problem.json | sort -u; grep -rl for each proposed name in nodes, dag.json, problem.json, local-references project, simongmt/Poincare (no match)`
- `lake env lean /tmp/imrep-unique-decomp/{Stmts,Assembly,Small,Frame,Inst,Inst2,Inst3,Inst4,Inst5,Fin,Vec4,All,StmtsExact,Final}.lean (#synth probes, conditional parent assembly, child trial proofs, #print axioms)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/Orientation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/LinearAlgebra/Determinant.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/LocallyIntegrable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Data/Set/Image.lean`
- `/tmp/imrep-unique-decomp/Final.lean`
- `/tmp/imrep-unique-decomp/Assembly.lean`
- `/tmp/imrep-unique-decomp/StmtsExact.lean`
- `/tmp/imrep-unique-review/Cond.lean`

The snapshot contract (project b4d606d, mathlib 25730c7c) is byte-identical to the workspace Contract.lean and Submission.lean.

Library support:
- SimonGMT Chapter03/Rectifiable.lean defines blowUpMap and HasApproximateTangentSpaceAt (Simon 3.1.4) and proves HasApproximateTangentSpaceAt.unique, which the parent uses.
- Mathlib (snapshot) supplies IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (Banach-valued, no local finiteness), ContinuousLinearMap.integral_apply, Measure.euclideanHausdorffMeasure_smul₀, Isometry.euclideanHausdorffMeasure_image, Set.subset_image_sdiff and setIntegral_congr_set.
- It also supplies the volume-form lemmas Orientation.volumeForm_robust', Orientation.abs_volumeForm_apply_le (Hadamard) and Orientation.abs_volumeForm_apply_of_orthonormal, plus OrthonormalBasis.det_to_matrix_orthonormalBasis_real.

Gaps:
- There is no continuity theorem for multilinear maps on finite-dimensional spaces, so the frame determinant is made continuous with AlternatingMap.mkContinuous.
- SimonGMT wedgeCovectors_apply_det is not reachable from Submission's imports.
- Instance search fails for ContinuousENorm, NormSMulClass ℝ and PseudoMetrizableSpace on MultiVector P n; the vector-density child's proof records the workaround that was tested.

Checks:
- All four child types and the parent type elaborate in namespace GMT.Ch07 with the contract's opens.
- The parent compiles from the four children with sorry'd proofs.
- Full trial proofs of all four children and of the parent assembly print axioms propext, Classical.choice, Quot.sound only.
- None of the four proposed names occurs in the DAG, the nodes, the project snapshot or SimonGMT.
