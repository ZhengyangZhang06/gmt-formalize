# Parent-supplied natural-language proof

- Parent DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1`
- Child DAG node: `root.slicing-a1.slice_integer_multiplicity-a1.slice_identity-a1.borel_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof, Step 3 (the density g_ω for Simon's 4.2 with g = θ⟨ξ⌞ν, ω⟩), together with the pointwise part of Step 5 and Fact U. One simplification: θ is only needed on M ∩ tsupport ω, so U need not be exhausted by compacts.

Notation. μ := H^{m+1} = μHE[m+1]. K := tsupport ω. ν(x) := |G(x)|⁻¹G(x), so ν(x) = 0 when G(x) = 0. For w ∈ ℝ^P and an m-covector α, w♭∧α := alternatizeUncurryFin((innerSL ℝ w).smulRight α), an (m+1)-covector. This map is bilinear in (w, α). ξ_t(x) := ξ(x) ∘ alternatizeUncurryFinCLM ∘ smulRightL(innerSL ν(x)); by definition (rfl), ξ_t(x)(α) = ξ(x)(ν(x)♭∧α). All "a.e." statements are for μ⌞M.

1. (Facts about ω.) ω ∈ D^m(U) is smooth, has compact support and tsupport ω ⊆ U. So ω is continuous, K is compact, K ⊆ U, and K is closed, hence Borel. ω(x) = 0 for x ∉ K. Since ω is continuous with compact support, there is C_ω ≥ 0 with ‖ω(x)‖ ≤ C_ω for all x.
2. (Borel version of θ on M ∩ K.) By IsRectifiableTriple.integrableOn applied to the compact K ⊆ U, θ is μ-integrable on M ∩ K. In particular θ is a.e.-strongly measurable for μ⌞(M ∩ K), so there is a Borel θ' with θ = θ' μ⌞(M∩K)-a.e. As K is Borel, μ⌞(M∩K) = (μ⌞M)⌞K. Hence for μ⌞M-a.e. x: x ∈ K ⟹ θ(x) = θ'(x).
3. (Borel version of ξ.) By IsRectifiableTriple.aestronglyMeasurable there is a strongly measurable ξ' with ξ = ξ' μ⌞M-a.e.
4. (Unit bound, Fact U.) By IsRectifiableTriple.orients, for μ⌞M-a.e. x there is an orthonormal τ : Fin (m+1) → ℝ^P with ξ(x) = simpleNVector τ or ξ(x) = −simpleNVector τ. By the sibling unit_bound (fiw_ims_tt_unit_bound), |ξ(x)(α)| ≤ ‖α‖ for every (m+1)-covector α, for μ⌞M-a.e. x.
5. (The field β := ν♭∧ω.) ν is Borel, since G and x ↦ |G(x)|⁻¹ are, and |ν(x)| ≤ 1 (it is 1 if G(x) ≠ 0 and 0 otherwise). The map (w, α) ↦ w♭∧α is continuous: it is the bounded bilinear map (λ, α) ↦ λ.smulRight α, precomposed with innerSL in the first argument and followed by the continuous linear map alternatizeUncurryFinCLM. So β(x) := ν(x)♭∧ω(x) is strongly measurable, as a continuous image of the strongly measurable pair (ν, ω). Moreover ‖β(x)‖ ≤ (m+1)·‖(innerSL ν(x)).smulRight ω(x)‖ = (m+1)|ν(x)|‖ω(x)‖ ≤ (m+1)C_ω. Evaluation (Λ, α) ↦ Λ(α) is continuous, so x ↦ ξ'(x)(β(x)) is strongly measurable.
6. (Definition of g.) Let S := {x : x ∈ K, G(x) ≠ 0}, a Borel set, and g := 1_S·θ'·ξ'(β). Thus g(x) = θ'(x)·ξ'(x)(β(x)) if x ∈ K and G(x) ≠ 0, and g(x) = 0 otherwise. g is Borel and g(x) = 0 whenever G(x) = 0.
7. (Integrability.) 1_K θ' is μ⌞M-integrable. Indeed, for Borel K, 1_Kθ' is μ⌞M-integrable iff θ' is integrable for (μ⌞M)⌞K = μ⌞(M∩K), and θ' = θ a.e. there with θ integrable on M ∩ K (step 2). For μ⌞M-a.e. x (steps 3 and 4):
 - if x ∈ S, then |g(x)| = |θ'(x)|·|ξ(x)(β(x))| ≤ |θ'(x)|·‖β(x)‖ ≤ (m+1)C_ω·|1_Kθ'(x)|;
 - if x ∉ S, then |g(x)| = 0 ≤ (m+1)C_ω·|1_Kθ'(x)|.
 g is measurable and a.e. dominated by an integrable function, so g is μ⌞M-integrable.
8. (Identity (a).) Let x lie in the μ⌞M-conull set where ξ(x) = ξ'(x) and (x ∈ K ⟹ θ(x) = θ'(x)). Suppose G(x) ≠ 0. Then ξ_t(x)(ω(x)) = ξ(x)(ν(x)♭∧ω(x)) = ξ(x)(β(x)).
 - If x ∈ K, then g(x) = θ'(x)ξ'(x)(β(x)) = θ(x)ξ(x)(β(x)).
 - If x ∉ K, then ω(x) = 0, so β(x) = 0 and θ(x)ξ(x)(β(x)) = 0 = g(x).
 In both cases g(x) = θ(x)·ξ_t(x)(ω(x)).
9. (Identity (b).) For the same x:
 - If G(x) = 0, then G(x)♭∧ω(x) = 0 (innerSL 0 = 0, 0.smulRight α = 0, and alternatizeUncurryFin is linear). So θ(x)ξ(x)(G(x)♭∧ω(x)) = θ(x)ξ(x)(0) = 0 = |G(x)|·g(x).
 - If G(x) ≠ 0, then G(x) = |G(x)|·ν(x). Linearity of w ↦ w♭∧α gives G(x)♭∧ω(x) = |G(x)|·β(x). So θ(x)ξ(x)(G(x)♭∧ω(x)) = |G(x)|·θ(x)ξ(x)(β(x)) = |G(x)|·g(x), by step 8.
 Hence (a) and (b) hold for μ⌞M-a.e. x. ∎

Formalization notes (a complete Lean proof of exactly this statement was checked in a scratch build of the frozen commit d8d46c9: written as `theorem Submission.<lean_name>` inside `namespace GMT.Ch06` of a file importing GMT.Ch06.Submission, with the comparator-form restatement `theorem _root_.X : (<lean_statement>) := by exact Submission.<lean_name>` also checked; axioms propext, Classical.choice, Quot.sound; the verified proof is appended at the end):
- Avoid `set` on large terms: it causes slow elaboration. Introduce K, β, g with `obtain ⟨β, hβ⟩ : ∃ β, β = … := ⟨_, rfl⟩`. Get the Borel versions by `obtain ⟨θ', hθ'm, hθθ'⟩ := hθK.aestronglyMeasurable` and likewise for ξ.
- Test-form facts: `ω.2.1.1.continuous`, `ω.2.1.2` (compactness of the tsupport), `ω.2.2`, `isClosed_tsupport`, `image_eq_zero_of_notMem_tsupport`, `Continuous.bounded_above_of_compact_support`.
- Step 2: `Measure.restrict_restrict hKm`, `inter_comm`, `ae_restrict_iff' hKm`.
- Continuity of (w, α) ↦ w♭∧α: `(isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Eucl P) (F := Covector (Eucl P) m)).continuous.comp (((innerSL ℝ).continuous.comp continuous_fst).prodMk continuous_snd)`, then `(ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp`. Do NOT go through continuity of `smulRightL`: instance synthesis for the iterated CLM topology fails.
- Strong measurability: `hBc.comp_stronglyMeasurable (hνm.stronglyMeasurable.prodMk hwc.stronglyMeasurable)`, then `beta_reduce at h` before `exact`. Without `beta_reduce`, the defeq check hits a deterministic whnf timeout. Evaluation: `(continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hξ'm.prodMk hβm)`, again with `beta_reduce`.
- Define g with `Set.indicator` on {x | x ∈ K ∧ G x ≠ 0}: an `if` needs a Decidable instance.
- Norm bound: `ContinuousAlternatingMap.norm_alternatizeUncurryFin_le`, `ContinuousLinearMap.norm_smulRight_apply`, `innerSL_apply_norm`.
- Integrability: `integrable_indicator_iff hKm`, `IntegrableOn.congr_fun_ae`, `Integrable.mono'` with `(hind.norm).const_mul`.
- Linearity: prove `∀ c v α, (innerSL ℝ (c • v)).smulRight α = c • (innerSL ℝ v).smulRight α` by `ext y; simp [smul_smul]`, then use `ContinuousAlternatingMap.alternatizeUncurryFin_smul`, `map_smul`, `smul_eq_mul`. Zero: `map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)` gives `alternatizeUncurryFin 0 = 0`; `(innerSL ℝ v).smulRight 0 = 0` by `ext y; simp`. The ξ_t-evaluation identity is `rfl` after `rw [hβ]`.

Verified Lean proof (scratch build of d8d46c9; place it in GMT/Ch06/Submission.lean after the contract's closing `end` of the noncomputable section and before `theorem main_theorem`, inside `namespace GMT.Ch06`; it uses only the frozen imports, and `Submission.fiw_ims_tt_unit_bound` from the sibling unit_bound):
```lean
theorem Submission.slicing_im_si_borel_density :
    ∀ (P m : ℕ) (U M : Set (Eucl P)) (θ : Eucl P → ℝ) (ξ : Eucl P → NVector (Eucl P) (m + 1)) (G : Eucl P → Eucl P) (ω : TestFormOn U m), IsRectifiableTriple U (m + 1) M θ ξ → Measurable G → ∃ g : Eucl P → ℝ, Measurable g ∧ Integrable g ((μHE[m + 1] : Measure (Eucl P)).restrict M) ∧ (∀ x, G x = 0 → g x = 0) ∧ ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), (G x ≠ 0 → g x = θ x * (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x)))) ((ω : DifferentialForm (Eucl P) m) x)) ∧ θ x * ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))) = ‖G x‖ * g x := by
  have unit_bound := Submission.fiw_ims_tt_unit_bound
  intro P m U M θ ξ G ω hM hG
  have hwc : Continuous (ω : DifferentialForm (Eucl P) m) := ω.2.1.1.continuous
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Eucl P) m)) := ω.2.1.2
  have hKU : tsupport (ω : DifferentialForm (Eucl P) m) ⊆ U := ω.2.2
  obtain ⟨K, hK⟩ : ∃ K : Set (Eucl P), K = tsupport (ω : DifferentialForm (Eucl P) m) := ⟨_, rfl⟩
  rw [← hK] at hKc hKU
  have hKm : MeasurableSet K := hK ▸ (isClosed_tsupport _).measurableSet
  have hw0 : ∀ x, x ∉ K → (ω : DifferentialForm (Eucl P) m) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hK ▸ hx)
  obtain ⟨Cw, hCw⟩ := hwc.bounded_above_of_compact_support ω.2.1.2
  -- Borel versions of θ (on M ∩ K) and ξ (on M)
  have hθK : IntegrableOn θ (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hM.integrableOn K hKc hKU
  obtain ⟨θ', hθ'm, hθθ'⟩ := hθK.aestronglyMeasurable
  obtain ⟨ξ', hξ'm, hξξ'⟩ := hM.aestronglyMeasurable
  -- the covector field β = ν♭ ∧ ω with ν = G/|G|
  have hνm : Measurable (fun x => ‖G x‖⁻¹ • G x) := (hG.norm.inv).smul hG
  have hνle : ∀ x, ‖‖G x‖⁻¹ • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, norm_inv, norm_norm]
    by_cases h : ‖G x‖ = 0
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  obtain ⟨β, hβ⟩ : ∃ β : Eucl P → Covector (Eucl P) (m + 1), β = fun x =>
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := ⟨_, rfl⟩
  have hBc : Continuous (fun p : Eucl P × Covector (Eucl P) m =>
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ p.1).smulRight p.2)) := by
    have h2 : Continuous (fun p : Eucl P × Covector (Eucl P) m => (innerSL ℝ p.1).smulRight p.2) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Eucl P) (F := Covector (Eucl P) m)).continuous.comp
        (((innerSL ℝ).continuous.comp continuous_fst).prodMk continuous_snd)
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).continuous.comp h2
  have hβm : StronglyMeasurable β := by
    have h3 : StronglyMeasurable (fun x => ((‖G x‖⁻¹ • G x : Eucl P), (ω : DifferentialForm (Eucl P) m) x)) :=
      hνm.stronglyMeasurable.prodMk hwc.stronglyMeasurable
    have h4 := hBc.comp_stronglyMeasurable h3
    beta_reduce at h4
    rw [hβ]; exact h4
  have hβle : ∀ x, ‖β x‖ ≤ (m + 1) * Cw := by
    intro x
    rw [hβ]
    calc ‖ContinuousAlternatingMap.alternatizeUncurryFin
            ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x))‖
        ≤ ((m : ℝ) + 1) * ‖(innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)‖ :=
          ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _
      _ = ((m : ℝ) + 1) * (‖‖G x‖⁻¹ • G x‖ * ‖(ω : DifferentialForm (Eucl P) m) x‖) := by
          rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
      _ ≤ ((m : ℝ) + 1) * (1 * Cw) := by
          gcongr
          · exact hνle x
          · exact hCw x
      _ = (m + 1) * Cw := by ring
  have hξβm : StronglyMeasurable (fun x => ξ' x (β x)) := by
    have h4 := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hξ'm.prodMk hβm)
    beta_reduce at h4
    exact h4
  -- the density
  have hSm : MeasurableSet {x | x ∈ K ∧ G x ≠ 0} :=
    hKm.inter (hG (measurableSet_singleton (0 : Eucl P))).compl
  obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
      g = {x | x ∈ K ∧ G x ≠ 0}.indicator (fun x => θ' x * ξ' x (β x)) := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (hθ'm.measurable.mul hξβm.measurable).indicator hSm
  -- a.e. facts on M
  have hθae : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M), x ∈ K → θ x = θ' x := by
    have : ∀ᵐ x ∂(((μHE[m + 1] : Measure (Eucl P)).restrict M).restrict K), θ x = θ' x := by
      rw [Measure.restrict_restrict hKm, inter_comm]; exact hθθ'
    exact (ae_restrict_iff' hKm).1 this
  have hunit : ∀ᵐ x ∂((μHE[m + 1] : Measure (Eucl P)).restrict M),
      ∀ α : Covector (Eucl P) (m + 1), |ξ x α| ≤ ‖α‖ := by
    filter_upwards [hM.orients] with x hx
    obtain ⟨τ, hτ, -, hξx⟩ := hx
    exact unit_bound P (m + 1) τ (ξ x) hτ hξx
  refine ⟨g, hgm, ?_, ?_, ?_⟩
  · -- integrability
    have hθ'K : IntegrableOn θ' (M ∩ K) (μHE[m + 1] : Measure (Eucl P)) := hθK.congr_fun_ae hθθ'
    have hind : Integrable (K.indicator θ') ((μHE[m + 1] : Measure (Eucl P)).restrict M) := by
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
      exact hθ'K
    refine Integrable.mono' ((hind.norm).const_mul ((m + 1) * Cw)) hgm.aestronglyMeasurable ?_
    filter_upwards [hξξ', hunit] with x hξx hux
    by_cases hS : x ∈ K ∧ G x ≠ 0
    · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from hS), indicator_of_mem hS.1, norm_mul]
      have : ‖ξ' x (β x)‖ ≤ (m + 1) * Cw := by
        rw [← hξx, Real.norm_eq_abs]; exact (hux (β x)).trans (hβle x)
      calc ‖θ' x‖ * ‖ξ' x (β x)‖ ≤ ‖θ' x‖ * ((m + 1) * Cw) := by gcongr
        _ = (m + 1) * Cw * ‖θ' x‖ := by ring
    · rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from hS), norm_zero]
      have hCw0 : 0 ≤ Cw := (norm_nonneg _).trans (hCw x)
      positivity
  · intro x hx
    rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => h.2 hx)]
  · filter_upwards [hξξ', hθae] with x hξx hθx
    have hcomp : (ξ x).comp ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ).comp
        (ContinuousLinearMap.smulRightL ℝ (Eucl P) (Covector (Eucl P) m) (innerSL ℝ (‖G x‖⁻¹ • G x))))
          ((ω : DifferentialForm (Eucl P) m) x) = ξ x (β x) := by
      rw [hβ]; rfl
    have part1 : G x ≠ 0 → g x = θ x * ξ x (β x) := by
      intro hG0
      by_cases hxK : x ∈ K
      · rw [hg, indicator_of_mem (show x ∈ {x | x ∈ K ∧ G x ≠ 0} from ⟨hxK, hG0⟩), hθx hxK, hξx]
      · have hβ0 : β x = 0 := by
          have hsr : (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight (0 : Covector (Eucl P) m) = 0 := by
            ext y; simp
          rw [hβ]
          simp only [hw0 x hxK, hsr]
          exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
        rw [hg, indicator_of_notMem (show x ∉ {x | x ∈ K ∧ G x ≠ 0} from fun h => hxK h.1), hβ0,
          map_zero, mul_zero]
    refine ⟨fun hG0 => by rw [hcomp]; exact part1 hG0, ?_⟩
    by_cases hG0 : G x = 0
    · have h0 : ContinuousAlternatingMap.alternatizeUncurryFin (0 : Eucl P →L[ℝ] Covector (Eucl P) m) = 0 :=
        map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Eucl P) ℝ)
      simp [hG0, h0]
    · have hGν : G x = ‖G x‖ • (‖G x‖⁻¹ • G x) := by
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hG0), one_smul]
      have hlin : ∀ (c : ℝ) (v : Eucl P) (α : Covector (Eucl P) m),
          (innerSL ℝ (c • v)).smulRight α = c • (innerSL ℝ v).smulRight α := by
        intro c v α
        ext y; simp [smul_smul]
      have hsm : (innerSL ℝ (G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) =
          ‖G x‖ • (innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x) := by
        rw [← hlin]
        congr 2
      have hβx : β x = ContinuousAlternatingMap.alternatizeUncurryFin
          ((innerSL ℝ (‖G x‖⁻¹ • G x)).smulRight ((ω : DifferentialForm (Eucl P) m) x)) := by rw [hβ]
      rw [hsm, ContinuousAlternatingMap.alternatizeUncurryFin_smul, map_smul, smul_eq_mul, ← hβx,
        part1 hG0]
      ring
```

## Key steps

1. K = tsupport ω is compact ⊆ U, Borel, ω = 0 off K and |ω| ≤ C_ω; θ is integrable on M ∩ K, so it has a Borel version θ' there; ξ has a strongly measurable version ξ' on M
2. Fact U (reused unit_bound + orients): |ξ(x)(α)| ≤ ‖α‖ for H^{m+1}⌞M-a.e. x
3. β = ν♭∧ω is strongly measurable with ‖β‖ ≤ (m+1)C_ω; g := 1_{K∩{G≠0}} θ' ξ'(β) is Borel, vanishes where G = 0, and |g| ≤ (m+1)C_ω|1_Kθ'| a.e. on M, hence integrable
4. where G ≠ 0: g = θ ξ(β) = θ ξ_t(ω) a.e. (using θ = θ' on K, ξ = ξ', and β = 0 off K)
5. G♭∧ω = |G|·β by linearity (and = 0 where G = 0), so θ ξ(G♭∧ω) = |G| g a.e. on M

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp GMT/Ch06/Contract.lean GMT/Ch06/Submission.lean (byte-identical); read Contract.lean: IsRectifiableTriple, tauAction, IsMeasureRepresentation, IsRestriction, IsSlice`
- `grep -n 'def testFormOnSubmodule|def exteriorDerivativeTestOn|tsupport_exteriorDerivative_subset|boundary_apply' simongmt/Poincare/SimonGMT/Chapter06/{Forms,Currents}.lean`
- `python3 scan of dag.json: decomposition of root.slicing-a1.slice_integer_multiplicity-a1 (sibling types slicing_im_coarea, slicing_im_lipschitz_leibniz, statuses decomposing); accepted nodes matching 'f ⁻¹' {t}|HasDerivAt (fun s|max 0|𝓝[>] 0|toMeasurable|simpleNVector|innerSL|alternatizeUncurryFin|IsSlice' -> reusable slicing_mb_pointwise_cutoff_tendsto (012eb78d) and fiw_ims_tt_unit_bound (27af9b19)`
- `git show 012eb78d57e01b1e54de6b8f0e5cf786950b91c0:GMT/Ch06/Submission.lean; git show 27af9b191b732eae73e3d693d8903e52f89962ce:GMT/Ch06/Submission.lean (accepted proofs, isolated-comparator-result.json passed)`
- `grep -rn 'theorem ae_tendsto_average|ae_hasDerivAt_integral|tendsto_Icc_vitaliFamily_left' mathlib/Mathlib; read MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `lake env lean Avail*.lean: availability under `import GMT.Ch06.Submission` of LocallyIntegrable.ae_hasDerivAt_integral (unknown constant), VitaliFamily.ae_tendsto_average, Real.tendsto_Icc_vitaliFamily_left, NullMeasurableSet.exists_measurable_subset_ae_eq, Measure.restrict_congr_set, Measure.le_restrict_apply, lintegral_eq_zero_iff', integral_eq_lintegral_pos_part_sub_lintegral_neg_part, integrable_toReal_of_lintegral_ne_top, integral_toReal, ae_lt_top', ContinuousAlternatingMap.norm_alternatizeUncurryFin_le, isBoundedBilinearMap_smulRight, Integrable.bdd_mul`
- `lake env lean /tmp/sid_split_scratch/Stmts.lean (eight child types in the exact comparator scope; #print checked)`
- `lake env lean /tmp/sid_split_scratch/Assembly.lean (parent type from child and sibling types; #print axioms)`
- `lake env lean /tmp/sid_split_scratch/Full.lean (#print axioms ParentFromUncles: propext, Classical.choice, Quot.sound)`
- `lake env lean /tmp/sid_split_scratch/E2Echildren.lean (embedded child proofs verbatim + comparator-form exact; no errors, no warnings)`
- `rg 'slicing_im_si_' /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project (no match); grep -rn 'slicing_im_si_' simongmt/Poincare (no match); dag.json lean_name scan for slicing_im_si_* (no match among 464 nodes)`
- `sed -n 1150,1345p book/chapter-06.txt (Simon Ch. 6, 4.1, Remark 4.2, 4.4, Lemma 4.5 and its proof)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/LebesgueDifferentiationThm.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/Differentiation.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/OneDim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Covering/DensityTheorem.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Module/Alternating/Uncurry/Fin.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Analysis/InnerProductSpace/LinearMap.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/Restrict.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Measure/NullMeasurable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-identity-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-coarea-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-integer-multiplicity-a1-slice-triple-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-boundary-rectifiability-a1-localization-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-slicing-a1-slice-mass-bound-a1-pointwise-a1-cutoff-tendsto-a1/isolated-comparator-result.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-flat-iff-weak-a1-im-series-a1-tsum-tau-a1-unit-bound-a1/isolated-comparator-result.json`
- `/tmp/sid_split_scratch/Stmts.lean`
- `/tmp/sid_split_scratch/Assembly.lean`
- `/tmp/sid_split_scratch/Full.lean`
- `/tmp/sid_split_scratch/E2Echildren.lean`

The pinned snapshot (project d8d46c95, Mathlib 25730c7c) holds the frozen Ch06 contract; Submission is byte-identical, so child types may use only contract, SimonGMT and Mathlib names in the comparator scope. SimonGMT provides TestFormOn (smooth, compact support, tsupport ⊆ U), exteriorDerivativeTestOn, tsupport_exteriorDerivative_subset and GeometricCurrentOn.boundary_apply. Neither SimonGMT nor Mathlib has co-area, slicing or cut-off tangential-gradient results; the six new children isolate exactly those steps of the supplied proof (Simon Ch. 6, Remark 4.2 and proof of 4.5(2)). Mathlib's interval Lebesgue differentiation lemma is not importable from Submission, but VitaliFamily.ae_tendsto_average and Real.tendsto_Icc_vitaliFamily_left are, so the one-sided version is proved from them. Two accepted DAG declarations are reused with byte-identical types: slicing_mb_pointwise_cutoff_tendsto (Step 9) and fiw_ims_tt_unit_bound (Fact U). All eight child types elaborate in the exact comparator scope. In scratch Lean the six new children are fully proved, and the parent's frozen type follows from the children plus the two declared sibling types slicing_im_coarea and slicing_im_lipschitz_leibniz, using only propext, Classical.choice and Quot.sound. No new name collides with the snapshot, SimonGMT or the 464 DAG nodes. These checks do not cover the proofs of the two sibling dependencies, which remain their own nodes.
