# Parent-supplied natural-language proof

- Parent DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1`
- Child DAG node: `root.compactness_of_minimizing_currents-a1.deformation_theorem-a1.im_series-a1.series_current-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: steps 1–4 of the supplied proof (evaluation bound, definition and continuity of S, mass, support), written for an arbitrary open U and degree n. The selected statement uses U = ℝ^P (univ) and n = k + 1. This is Simon Ch. 6, 2.4, and the M-absolutely convergent series in the proof of 7.2.

Notation. |α| := covectorEuclideanNorm α (Euclidean coefficient norm); ‖α‖ is the operator norm. For Z ∈ 𝒟_n(U), M(Z) = Z.mass = M_U(Z) = sup{ofReal(Z(ω)) : ω admissible}. Here ω ∈ 𝒟ⁿ(U) is admissible if |ω(x)| ≤ 1 for every x; tsupport ω ⊆ U holds for every test form in U. Write M(Z)^ℝ := M(Z).toReal.

1. (Norm facts; sibling norm_props.) |tα| = |t||α| for t ∈ ℝ; there is C ≥ 0 with |α| ≤ C‖α‖ for every covector α; and α ↦ |α| is continuous.
2. (Bounded coefficient norm.) Let ω ∈ 𝒟ⁿ(U). The function x ↦ |ω(x)| is continuous: ω is C^∞, hence continuous, and step 1 applies. It vanishes outside the compact set tsupport ω, since |0| = 0. So it is bounded; choose c_ω > 0 with |ω(x)| ≤ c_ω for all x.
3. (Evaluation bound.) Let Z ∈ 𝒟_n(U) with M(Z) < ∞, ω ∈ 𝒟ⁿ(U), and c > 0 with |ω(x)| ≤ c for all x. Then |Z(ω)| ≤ c·M(Z)^ℝ. Indeed, for s = c⁻¹ and s = −c⁻¹ the form sω lies in 𝒟ⁿ(U), and |sω(x)| = c⁻¹|ω(x)| ≤ 1 by step 1. So sω is admissible and ofReal(Z(sω)) ≤ M(Z) (GeometricCurrentOn.le_massOn). Since M(Z) < ∞, this means s·Z(ω) = Z(sω) ≤ M(Z)^ℝ. Multiplying the two inequalities by c > 0 gives ±Z(ω) ≤ c·M(Z)^ℝ.
4. (Absolute summability.) Put A := Σ_r M(X_r) < ∞. Every M(X_r) is finite (ENNReal.ne_top_of_tsum_ne_top). The real sequence (M(X_r)^ℝ) is summable (ENNReal.summable_toReal) with Σ_r M(X_r)^ℝ = A^ℝ (ENNReal.tsum_toReal_eq). For ω ∈ 𝒟ⁿ(U), steps 2–3 give |X_r(ω)| ≤ c_ω·M(X_r)^ℝ for every r. So Σ_r |X_r(ω)| < ∞, and the real series Σ_r X_r(ω) is summable (Summable.of_norm_bounded).
5. (Linear functional.) Put L(ω) := Σ_r X_r(ω). Since each X_r is linear and the series are summable, L(ω + ω') = L(ω) + L(ω') (Summable.tsum_add) and L(tω) = t·L(ω) (tsum_mul_left).
6. (Uniform bound.) If c > 0 and |ω(x)| ≤ c for all x, then |L(ω)| ≤ Σ_r |X_r(ω)| ≤ Σ_r c·M(X_r)^ℝ = c·A^ℝ. This uses norm_tsum_le_tsum_norm, Summable.tsum_le_tsum and step 3.
7. (Continuity.) First, A^ℝ ≥ 0: apply step 6 to ω = 0 and c = 1, using L(0) = 0. Let ω_j → 0 in 𝒟ⁿ(U), i.e. TestFormOnConverges ω_j 0. Let η > 0 and put ε := η/(2(C + 1)(A^ℝ + 1)) > 0. By sibling uniform_small, for all large j, ‖ω_j(x)‖ ≤ ε for every x. Then |ω_j(x)| ≤ C‖ω_j(x)‖ ≤ Cε ≤ (C + 1)ε. Step 6 with c := (C + 1)ε gives |L(ω_j)| ≤ (C + 1)ε·A^ℝ ≤ (C + 1)ε(A^ℝ + 1) = η/2 < η. Hence L(ω_j) → 0. This is the continuity condition of GeometricCurrentOn, so there is Y ∈ 𝒟_n(U) with Y(ω) = L(ω) for every ω. By step 4, HasSum (r ↦ X_r(ω)) (Y(ω)) for every ω ∈ 𝒟ⁿ(U); this is conclusion (i).
8. (Mass.) Let ω be admissible. The terms max(X_r(ω), 0) are nonnegative and bounded by |X_r(ω)|, so they are summable; also X_r(ω) ≤ max(X_r(ω), 0). Hence Y(ω) = Σ_r X_r(ω) ≤ Σ_r max(X_r(ω), 0). Therefore ofReal(Y(ω)) ≤ ofReal(Σ_r max(X_r(ω), 0)) = Σ_r ofReal(max(X_r(ω), 0)) (ENNReal.ofReal_tsum_of_nonneg) = Σ_r ofReal(X_r(ω)). This is ≤ Σ_r M(X_r), because ω is admissible for every M(X_r) (le_massOn). Taking the supremum over admissible ω gives M(Y) ≤ Σ_r M(X_r); this is conclusion (ii).
9. (Support, using (VO).) Let E := closure(⋃_r spt X_r), a closed set, and let x ∈ spt Y; then x ∈ U, since spt Y ⊆ U. Suppose x ∉ E. As U is open, U ∖ E is open and contains x. Choose ε > 0 with B_ε(x) ⊆ U ∖ E and put W := B_{ε/2}(x). Then W is open, and closure W ⊆ B̄_{ε/2}(x) ⊆ B_ε(x) ⊆ U ∖ E ⊆ U. Also closure W is compact, being closed and bounded in ℝ^P. Let ω ∈ 𝒟ⁿ(U) with tsupport ω ⊆ W. For each r, spt X_r ⊆ E, while tsupport ω ⊆ closure W ⊆ U ∖ E. So tsupport ω and spt X_r are disjoint, and (VO) gives X_r(ω) = 0. Hence HasSum (r ↦ X_r(ω)) 0. By uniqueness of sums in the Hausdorff space ℝ and (i), Y(ω) = 0. So Y vanishes on W, and W is one of the sets whose union is zeroRegion Y. Then x ∈ W ⊆ zeroRegion Y, contradicting x ∈ spt Y = U ∖ zeroRegion Y. Therefore spt Y ⊆ E; this is conclusion (iii). ∎

Lean reference implementation. It was kernel-checked in the decomposition session after import GMT.Ch07.Submission, inside namespace GMT.Ch07 with the contract's opens (open Filter Function Set MeasureTheory Metric; open scoped ENNReal Topology; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)). #print axioms gives propext, Classical.choice, Quot.sound and the two sibling declarations only. An identical copy is in /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.lean.

theorem Submission.cmcdt_ims_series_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (U : Set (Euclid P)) (X : ℕ → GeometricCurrentOn U n), IsOpen U → ∑' r, (X r).mass ≠ ∞ → ∃ Y : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, HasSum (fun r => X r ω) (Y ω)) ∧ Y.mass ≤ ∑' r, (X r).mass ∧ Y.support ⊆ closure (⋃ r, (X r).support) := by
  intro hVO P n U X hU hX
  -- Step 1 (reused rsd_mw_tfa_norm_props): `|t α| = |t| |α|`, `|α| ≤ C ‖α‖`, `|·|` continuous
  have hhom := (Submission.rsd_mw_tfa_norm_props P n).2.1
  -- Step 3: `|Z(ω)| ≤ c M(Z)` whenever `|ω(x)| ≤ c` for all `x`
  have h3 : ∀ (Z : GeometricCurrentOn U n) (ω : TestFormOn U n) (c : ℝ), 0 < c → Z.mass ≠ ∞ →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      |Z ω| ≤ c * Z.mass.toReal := by
    intro Z ω c hc hZ hω
    have key : ∀ s : ℝ, |s| = c⁻¹ → s * Z ω ≤ Z.mass.toReal := by
      intro s hs
      have hadm : s • ω ∈ massAdmissibleOn U n U := by
        refine ⟨(s • ω).property.2, fun x => ?_⟩
        have hx : ((s • ω : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
            s • ((ω : DifferentialForm (Euclid P) n) x) := rfl
        rw [hx, hhom, hs]
        calc c⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
            ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left (hω x) (inv_nonneg.mpr hc.le)
          _ = 1 := inv_mul_cancel₀ hc.ne'
      have h1 : ENNReal.ofReal (Z (s • ω)) ≤ Z.mass := Z.le_massOn hadm
      rw [ENNReal.ofReal_le_iff_le_toReal hZ] at h1
      have hlin : Z (s • ω) = s * Z ω := by
        rw [map_smul, smul_eq_mul]
      rwa [hlin] at h1
    have hp := key c⁻¹ (abs_of_pos (inv_pos.mpr hc))
    have hn := key (-c⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.mpr hc)])
    rw [abs_le]
    constructor
    · have h' : c * (-c⁻¹ * Z ω) ≤ c * Z.mass.toReal := mul_le_mul_of_nonneg_left hn hc.le
      have : c * (-c⁻¹ * Z ω) = -(Z ω) := by field_simp
      linarith
    · have h' : c * (c⁻¹ * Z ω) ≤ c * Z.mass.toReal := mul_le_mul_of_nonneg_left hp hc.le
      have : c * (c⁻¹ * Z ω) = Z ω := by field_simp
      linarith
  -- Step 2: every test form has bounded coefficient norm
  have h4 : ∀ ω : TestFormOn U n, ∃ c : ℝ, 0 < c ∧
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c := by
    intro ω
    have hsmooth : IsSmoothForm (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
    have hcont : Continuous (fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)) :=
      (Submission.rsd_mw_tfa_norm_props P n).2.2.2.comp (ContDiff.continuous hsmooth)
    have hcs : HasCompactSupport (fun x => covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)) :=
      HasCompactSupport.comp_left (g := covectorEuclideanNorm) ω.property.1.2 (covectorEuclideanNorm_zero P n)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
    refine ⟨max C 0 + 1, by positivity, fun x => ?_⟩
    have h := hC x
    rw [Real.norm_eq_abs] at h
    linarith [le_abs_self (covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)), le_max_left C 0]
  -- Step 7: a linear functional with `|L(ω)| ≤ c A` whenever `|ω| ≤ c` is a current
  have h5 : ∀ (L : TestFormOn U n →ₗ[ℝ] ℝ) (A : ℝ), (∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |L ω| ≤ c * A) →
      ∃ Y : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, Y ω = L ω := by
    intro L A hL
    obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P n).2.2.1
    have hA : 0 ≤ A := by
      have h0 := hL 0 1 one_pos (fun x => by simp)
      simpa using h0
    refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    obtain ⟨K, -, -, -, hunif⟩ := Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
    rw [Metric.tendsto_atTop]
    intro η hη
    set ε : ℝ := η / (2 * (C + 1) * (A + 1)) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)
    refine ⟨N, fun j hj => ?_⟩
    have hb : ∀ x, covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x) ≤ (C + 1) * ε := by
      intro x
      calc covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x)
          ≤ C * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := hC _
        _ ≤ C * ε := mul_le_mul_of_nonneg_left (hN j hj x) hC0
        _ ≤ (C + 1) * ε := by nlinarith
    have hLj := hL (ωs j) ((C + 1) * ε) (by positivity) hb
    rw [Real.dist_eq, sub_zero]
    have hkey : (C + 1) * ε * A < η := by
      have h1 : (C + 1) * ε * (A + 1) = η / 2 := by
        rw [hε]; field_simp
      nlinarith
    exact lt_of_le_of_lt hLj hkey
  -- Steps 4-6: absolute summability, the linear functional `L = Σ X_r`, its bound
  have hXr : ∀ r, (X r).mass ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hX
  have hm : Summable (fun r => (X r).mass.toReal) := ENNReal.summable_toReal hX
  have hms : (∑' r, (X r).mass).toReal = ∑' r, (X r).mass.toReal := ENNReal.tsum_toReal_eq hXr
  have hbound : ∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      ∀ r, |X r ω| ≤ c * (X r).mass.toReal :=
    fun ω c hc hω r => h3 (X r) ω c hc (hXr r) hω
  have hsumm_abs : ∀ ω : TestFormOn U n, Summable (fun r => |X r ω|) := by
    intro ω
    obtain ⟨c, hc, hω⟩ := h4 ω
    exact Summable.of_nonneg_of_le (fun r => abs_nonneg _) (hbound ω c hc hω) (hm.mul_left c)
  have hsumm : ∀ ω : TestFormOn U n, Summable (fun r => X r ω) := fun ω =>
    Summable.of_norm_bounded (hsumm_abs ω) (fun r => by rw [Real.norm_eq_abs])
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑' r, X r ω
      map_add' := fun ω ω' => by
        simp only [map_add]
        exact (hsumm ω).tsum_add (hsumm ω')
      map_smul' := fun t ω => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  have hLbound : ∀ (ω : TestFormOn U n) (c : ℝ), 0 < c →
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) →
      |L ω| ≤ c * (∑' r, (X r).mass).toReal := by
    intro ω c hc hω
    show |∑' r, X r ω| ≤ _
    rw [hms]
    calc |∑' r, X r ω| ≤ ∑' r, |X r ω| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (f := fun r => X r ω) (by simpa [Real.norm_eq_abs] using hsumm_abs ω)
      _ ≤ ∑' r, c * (X r).mass.toReal :=
          Summable.tsum_le_tsum (hbound ω c hc hω) (hsumm_abs ω) (hm.mul_left c)
      _ = c * ∑' r, (X r).mass.toReal := tsum_mul_left
  obtain ⟨Y, hY⟩ := h5 L _ hLbound
  have hYsum : ∀ ω : TestFormOn U n, HasSum (fun r => X r ω) (Y ω) := by
    intro ω
    rw [hY ω]
    exact (hsumm ω).hasSum
  refine ⟨Y, hYsum, ?_, ?_⟩
  · -- Step 8: the mass bound
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have hpos_summ : Summable (fun r => max (X r ω) 0) :=
      Summable.of_nonneg_of_le (fun r => le_max_right _ _)
        (fun r => max_le (le_abs_self _) (abs_nonneg _)) (hsumm_abs ω)
    calc ENNReal.ofReal (Y ω) = ENNReal.ofReal (∑' r, X r ω) := by rw [(hYsum ω).tsum_eq]
      _ ≤ ENNReal.ofReal (∑' r, max (X r ω) 0) :=
          ENNReal.ofReal_le_ofReal
            (Summable.tsum_le_tsum (fun r => le_max_left _ _) (hsumm ω) hpos_summ)
      _ = ∑' r, ENNReal.ofReal (max (X r ω) 0) :=
          ENNReal.ofReal_tsum_of_nonneg (fun r => le_max_right _ _) hpos_summ
      _ = ∑' r, ENNReal.ofReal (X r ω) := by
          congr 1
          funext r
          rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le]
      _ ≤ ∑' r, (X r).mass := ENNReal.tsum_le_tsum (fun r => (X r).le_massOn hω)
  · -- Step 9: the support bound, from (VO)
    intro x hx
    by_contra hxE
    set E := closure (⋃ r, (X r).support) with hEdef
    have hxU : x ∈ U := Y.support_subset_domain hx
    have hopen : IsOpen (U \ E) := hU.sdiff isClosed_closure
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x ⟨hxU, hxE⟩
    set W := ball x (ε / 2) with hWdef
    have hclW : closure W ⊆ ball x ε :=
      (closure_ball_subset_closedBall).trans (closedBall_subset_ball (by linarith))
    have hWzero : W ⊆ Y.zeroRegion := by
      refine subset_sUnion_of_mem ⟨isOpen_ball, ?_, ?_, ?_⟩
      · exact isBounded_ball.isCompact_closure
      · exact hclW.trans (hball.trans diff_subset)
      · intro ω hω
        have hX0 : ∀ r, X r ω = 0 := by
          intro r
          apply hVO
          rw [Set.disjoint_iff]
          intro y ⟨hy1, hy2⟩
          have hyE : y ∈ E := subset_closure (mem_iUnion.mpr ⟨r, hy2⟩)
          have hyW : y ∈ U \ E := hball (hclW (subset_closure (hω hy1)))
          exact hyW.2 hyE
        have h0 : HasSum (fun r => X r ω) 0 := by
          simp only [hX0]; exact hasSum_zero
        exact (hYsum ω).unique h0
    exact hx.2 (hWzero (mem_ball_self (by linarith)))

## Key steps

1. Admissibility of ±c⁻¹ω gives |Z(ω)| ≤ c·M(Z) whenever |ω(x)| ≤ c; test forms have bounded coefficient norm.
2. Σ_r M(X_r) < ∞ makes Σ_r X_r(ω) absolutely summable; L(ω) := Σ_r X_r(ω) is linear with |L(ω)| ≤ c·Σ_r M(X_r) when |ω| ≤ c.
3. Uniform smallness of test forms converging to 0 and |α| ≤ C‖α‖ make L sequentially continuous, so L is a current Y with HasSum (X_r(ω)) (Y(ω)).
4. For admissible ω, ofReal(Y(ω)) ≤ Σ_r ofReal(X_r(ω)) ≤ Σ_r M(X_r), so M(Y) ≤ Σ_r M(X_r).
5. For x ∉ closure ⋃ spt X_r, a small ball W around x has compact closure inside U ∖ closure ⋃ spt X_r; (VO) kills every X_r(ω) with tsupport ω ⊆ W, so Y vanishes on W and x ∉ spt Y.

## Reference use

### local-project

Queries:
- `cmp local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean workspaces/gmt-ch07/GMT/Ch07/Contract.lean (identical); cmp GMT/Ch07/Contract.lean GMT/Ch07/Submission.lean (identical); git -C local-references/123e8435b4a2469b/mathlib rev-parse HEAD (25730c7c759d108ef87ab70af2342a196760f79d, matches manifest)`
- `rg -n "theorem hasSum_integral_of_dominated_convergence|theorem Measurable.tsum|theorem enorm_tsum_le_tsum_enorm|theorem stronglyMeasurable_of_tendsto|theorem iUnion_disjointed|theorem disjoint_disjointed|theorem setIntegral_indicator|theorem HasCompactSupport.exists_bound_of_continuous|theorem ae_lt_top|theorem ENNReal.summable_toReal|theorem StronglyMeasurable.measurableSet_eq_fun|theorem Monotone.measurable|theorem Int.abs_lt_one_iff|lemma Int.abs_lt_one_iff|theorem lintegral_tsum|theorem measure_iUnion_le" mathlib/Mathlib -g '*.lean'`
- `rg -n "Measurable.tsum|stronglyMeasurable_of_tendsto\b|measurableSet_eq_fun|exists_bound_of_continuous\b|isBoundedBilinearMap_apply\b|theorem tsum_eq_sum\b|theorem lintegral_indicator\b|theorem withDensity_apply\b" mathlib/Mathlib -g '*.lean'; rg -n tprod mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean; rg -n ennreal_tsum mathlib/Mathlib -g '*.lean'; rg -n abs_lt_one_iff mathlib/Mathlib -g '*.lean'`
- `rg -n -i "countable sum|series of currents|integer multiplicity" project/GMT -g '*.lean'; rg -n "IMRep|imrep" project/GMT -g '*.lean'; rg -n cmcdt_ims project mathlib/Mathlib (no match)`
- `grep -n 'theorem countablyRectifiable_iUnion|theorem CountablyRectifiable.mono|theorem HasApproximateTangentSpaceAt.unique' lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean; reading Chapter06/{Currents,Mass,CurrentLocalEquality,Forms,FormSupNorm}.lean`
- `python3 -I scans of runs/20261011T150044Z-ba604216b4/dag.json (902 then about 980 nodes): statuses, candidate commits and frozen types of rsd_mw_tfa_norm_props, dpf_pfc_testFormOnConverges_zero_uniform, rsdic_imrep_ae_tangent_orient_of_subset, rsdic_unitOrientation_eq_or_eq_neg, rsdic_ae_tangent_iff_of_subset, unit_orientation_norm_le_one (all accepted, byte-identical); exact-type and name search for the four new children (none); comparison with cmc_fc_series_current, dor_lmb_fc_im_series, rsdic_exists_imrep_int_combination`
- `git show a02fee1b89|fe95347baa|a157a5f4f6|0325970d8b:GMT/Ch07/Submission.lean | grep 'theorem Submission.<name>'; git show 2af75d6921:GMT/Ch07/Submission.lean (hand-built MetrizableSpace (MultiVector P n) instance)`
- `sed of /runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py (_existing_lean_name_problem, _solve_children node bound, _overlay_accepted_children, _accepted_checkpoint, _install_parent_supplied_child_handoff) and store.py ensure; max_nodes in .humanize/swarm-configs (newest: 5000)`
- `python3 -I /tmp/cmcdt_ims/scripts/gen_challenges.py /runtime/flows/gmt-claude-1e66f8f4bfb6 (gmt-compare.py child_modules + contract_scope + lean_contract.validate_lean_statement on all ten statements); lake env lean Challenge_*.lean (10 files, only the expected sorry)`
- `lake env lean Types.lean, Assembly.lean, C.lean, D.lean, IM1.lean, Support.lean, SeriesCurrentFull.lean (copy of GMT/Scratch/cmc_fc_series_current_decomposition/Full.lean), Reference.lean; #print axioms = propext, Classical.choice, Quot.sound plus only the declared reused siblings`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/InfiniteSum.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Disjointed.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Markov.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Algebra/Order/Group/Unbundled/Int.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Measure/WithDensity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1-im-series-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-deformation-theorem-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-flat-convergence-a1-series-current-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-imrep-tangent-transfer-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-orientation-sign-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-locality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-regular-set-dense-a1-integer-combination-a1-tangent-growth-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-half-space-cone-lies-in-boundary-a1-imrep-measure-unique-a1-orie-c3a822a8f5/parent-supplied-natural-proof.md`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/runtime.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/store.py`
- `/runtime/flows/gmt-claude-1e66f8f4bfb6/_recursive_lean/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmc_fc_series_current_decomposition/Full.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Scratch/cmcdt_im_series_decomposition/Reference.out`

The snapshot (project b4d606d, Mathlib 25730c7c) has a Ch07 contract byte-identical to the workspace Contract.lean and Submission.lean. The snapshot project has no lemma on series of currents, countable sums of IMReps or integer densities: its Ch06 statements are sorry-frozen, use different types and are not imported by Ch07; cmcdt_ims gives no match. Mathlib supplies every tool the new children cite: hasSum_integral_of_dominated_convergence (MeasureTheory/Integral/DominatedConvergence.lean:77), Measurable.tsum (additive form of Measurable.tprod, Constructions/Polish/Basic.lean:1035), enorm_tsum_le_tsum_enorm (Analysis/Normed/Group/InfiniteSum.lean:133), stronglyMeasurable_of_tendsto and StronglyMeasurable.measurableSet_eq_fun (Function/StronglyMeasurable/Basic.lean:789,1028), disjointed/iUnion_disjointed/disjoint_disjointed (Order/Disjointed.lean), setIntegral_indicator (Integral/Bochner/Set.lean:194), ae_lt_top, lintegral_tsum, ENNReal.summable_toReal, Int.abs_lt_one_iff, Monotone.measurable, isBoundedBilinearMap_apply, withDensity_apply and HasCompactSupport.exists_bound_of_continuous. SimonGMT supplies countablyRectifiable_iUnion, CountablyRectifiable.mono and HasApproximateTangentSpaceAt.unique. The six reused DAG declarations are accepted with byte-identical frozen types and candidate commits. The four new names and types are fresh. All ten child types compile as exact comparator challenges. The assembly of the exact selected type and the proofs of the four new children compile, depending only on standard axioms and the declared reused siblings.
