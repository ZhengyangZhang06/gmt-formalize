# Parent-supplied natural-language proof

- Parent DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1`
- Child DAG node: `root.lipschitz_pushforward_im-a1.pushforward_integrality-a1.image_density-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Conventions: ℝ^P = EuclideanSpace ℝ (Fin P) (Lean `Eucl P`) with inner product ⟨·,·⟩ and norm |·|; Hⁿ = μHE[n], Mathlib's Euclidean-normalised n-dimensional Hausdorff measure, which equals Lebesgue measure Lⁿ = volume on ℝⁿ. An n-covector on E is a continuous alternating n-linear map α : Eⁿ → ℝ with the operator norm. An n-vector is a continuous linear functional on n-covectors (`NVector E n`), also with the operator norm. simpleNVector v is the n-vector α ↦ α(v₁,…,vₙ). For a continuous linear map A, A_#u := nVectorPushforward n A u = u ∘ A^#, where A^#α = α(A·,…,A·). Thus A_# is linear in u, and A_#(simpleNVector v) = simpleNVector(A∘v) (`nVectorPushforward_simple`). `HasWeightedApproximateTangentSpaceAt n M θ x T` is Simon's weighted approximate tangent space (Ch. 3, 1.7). By SimonGMT `HasWeightedApproximateTangentSpaceAt.unique` it is unique when θ(x) ≠ 0, and its first component says dim T = n. The derivative clause for (M, θ, f, L) means: for Hⁿ⌞M-a.e. x, for every subspace T with HasWeightedApproximateTangentSpaceAt n M θ x T and every v ∈ T, the map t ↦ f(x + t v) has derivative L(x)v at t = 0. Φ is c-antilipschitz on Ω if c|w − w′| ≤ |Φ(w) − Φ(w′)| for all w, w′ ∈ Ω.

This is Steps 4(b), 5, 8 and 9 of the parent proof, stated for an abstract n-vector field Ξ. The parent applies it with Ξ(x) = L(x)_#ξ(x). Two changes from the parent's write-up. First, the image set is taken as Y := {y ∈ V : 1 ≤ N(y) < ∞}, defined by the fibre counting function N; the parent used f(M₊) minus a null set. Second, the density c(y)ζ(y) of the parent is built directly as the fibre sum Ψ(y) = Σ_{x ∈ F_y} θ(x)η_x. Its measurability comes from the fibre-sum measurability in (AF), which the parent's Step 9 also uses, instead of from inverse charts. Throughout, Hⁿ = μHE[n] on ℝ^P and on ℝ^Q, and Σ' is the unordered (tsum) sum.

1. (Positive part.) Put M₊ := {x ∈ M : Ξ(x) ≠ 0} = M ∩ {‖Ξ‖ ≠ 0}. It is Hⁿ-null-measurable. The real function ‖Ξ‖ is Hⁿ⌞M-a.e. measurable, so it agrees with a measurable φ off a set N₀ with Hⁿ⌞M(N₀) = 0; then Hⁿ(N₀ ∩ M) ≤ Hⁿ⌞M(N₀) = 0 (`Measure.le_restrict_apply`). M ∩ {φ ≠ 0} is null-measurable, and its symmetric difference with M₊ lies in the Hⁿ-null set N₀ ∩ M. Since θ(x) ∈ ℕ and θ(x) > 0, θ ≥ 1 on M. For x ∈ M₊ put η(x) := ‖Ξ(x)‖⁻¹ • Ξ(x) and ϑ(x) := θ(x) • η(x) = (θ(x)‖Ξ(x)‖⁻¹) • Ξ(x). Then ‖η(x)‖ = 1 and ‖ϑ(x)‖ = θ(x). For y ∈ ℝ^Q let F_y := {x ∈ M₊ : f(x) = y}.
2. (Counting function.) N(y) := Σ'_{x ∈ F_y} ofReal(θ(x)) ∈ [0, ∞]. By (AF) with A := M₊ and h := ofReal∘θ (Hⁿ⌞M₊-a.e. measurable), N is Hⁿ-a.e. measurable.
3. (Local finiteness.) Let K ⊆ V be compact. f is continuous on M, so M ∩ f⁻¹(K) = M ∩ C for some closed C ⊆ ℝ^P (`continuousOn_iff_isClosed`). Apply (AF) with A := M₊ and h := ofReal(θ)·1_C, which is a.e. measurable on M₊. For x ∈ F_y, 1_C(x) = 1_K(f(x)) = 1_K(y), so the fibre sum of h is 1_K(y)·N(y). Hence ∫⁻ 1_K N dHⁿ = ∫⁻_{M₊} h‖Ξ‖ₑ ≤ ∫⁻_M 1_C ofReal(θ)‖Ξ‖ₑ = ∫⁻_{M ∩ C} ofReal(θ)‖Ξ‖ₑ = ∫⁻_{M ∩ f⁻¹(K)} ofReal(θ)‖Ξ‖ₑ < ∞, using (LF).
4. (N < ∞ a.e.) For y ∉ V, F_y = ∅ because f(M) ⊆ V, so N(y) = 0. The open set V is a countable union of compact sets K_i ⊆ V (V is σ-compact: the subtype V is locally compact by `IsOpen.locallyCompactSpace`, so `SigmaCompactSpace.exists_compact_covering` applies to it; take the images of its compact sets in ℝ^Q). By Step 3 and `ae_lt_top'`, 1_{K_i}N < ∞ Hⁿ-a.e. for each i. Hence Hⁿ({y : N(y) = ∞}) = 0.
5. (The set Y.) Y := {y : y ∈ V, N(y) ≠ 0, N(y) ≠ ∞}. Clearly Y ⊆ V, and Y is Hⁿ-null-measurable (V open, N a.e. measurable). Let y ∈ Y. Then F_y ≠ ∅, since an empty sum is 0. F_y is finite: each term ofReal(θ(x)) is ≥ 1, so any m distinct points of F_y contribute ≥ m to N(y) < ∞ (`ENNReal.sum_le_tsum`). Moreover N(y) ≥ 1. For compact K ⊆ V, Y ∩ K ⊆ {y : 1 ≤ 1_K(y)N(y)}, so Markov's inequality (`meas_ge_le_lintegral_div` or `mul_meas_ge_le_lintegral₀`) gives Hⁿ(Y ∩ K) ≤ ∫⁻ 1_K N < ∞ (Step 3).
6. (The density.) Ψ(y) := Σ'_{x ∈ F_y} ϑ(x), a tsum in the finite-dimensional normed space NVector(ℝ^Q, n); in Lean the sum runs over the subtype {x // x ∈ M₊ ∧ f x = y}. For y ∈ Y the fibre is finite, so Ψ(y) = Σ_{x ∈ F_y} ϑ(x) (`tsum_fintype`) and ‖Ψ(y)‖ ≤ Σ_{x ∈ F_y} θ(x) = N(y).toReal.
7. (Measurability of Ψ on Y.) Let β be an n-covector on ℝ^Q and g_β(x) := ϑ(x)(β), a real function that is Hⁿ⌞M₊-a.e. strongly measurable (θ, Ξ are, and ζ ↦ ζ(β) is continuous). Let N^±_β be the fibre sums over M₊ of ofReal(±g_β). By (AF) both are Hⁿ-a.e. measurable. For y ∈ Y (finite fibre), Ψ(y)(β) = Σ_{x ∈ F_y} g_β(x) = N⁺_β(y).toReal − N⁻_β(y).toReal. So y ↦ Ψ(y)(β) is Hⁿ⌞Y-a.e. measurable for every β. The space Covector(ℝ^Q, n) of n-covectors is finite-dimensional by the sibling lemma lpf_pi_covector_finiteDimensional (in Lean: `haveI := Submission.lpf_pi_covector_finiteDimensional Q n`). Do not use the instance `Module.Finite.multilinearMap`: its module Mathlib.LinearAlgebra.Multilinear.FiniteDimensional is not imported by GMT.Ch06.Submission, and a child may not add imports. Choose a basis b_1,…,b_D of Covector(ℝ^Q, n) (e.g. `Module.finBasis`) and put b*_i := the i-th coordinate functional of this basis, a continuous linear functional on Covector(ℝ^Q, n) (every linear functional on a finite-dimensional space is continuous, `LinearMap.toContinuousLinearMap`). Then b*_i is an n-vector with b*_i(b_l) = δ_il. Every n-vector ζ equals Σ_i ζ(b_i) • b*_i: evaluate at α = Σ_l (coord_l α) b_l (`Module.Basis.sum_repr`) and use linearity of ζ. Hence Ψ = Σ_i Ψ(·)(b_i) • b*_i on Y, a finite sum of (a.e. measurable real function) • (constant n-vector). So Ψ is Hⁿ⌞Y-a.e. strongly measurable (`AEStronglyMeasurable.smul_const`, `Finset.aestronglyMeasurable_fun_sum`; see the Lean note below for the needed `ContinuousAdd` instance).
8. (Integrability.) Let K ⊆ V be compact. ‖Ψ‖ is Hⁿ⌞(Y ∩ K)-a.e. strongly measurable by Step 7, and ∫⁻_{Y∩K} ‖Ψ‖ₑ ≤ ∫⁻_{Y∩K} N ≤ ∫⁻ 1_K N < ∞ by Steps 3 and 6. So ‖Ψ‖ is integrable on Y ∩ K.
9. (Chart family.) Let B := {x ∈ M : Ξ(x) ≠ 0 and the conclusion of (CH) fails at x}. By (CH) and null-measurability of M, Hⁿ(B) = 0, so E := f(B) is Hⁿ-null by the null-image hypothesis (B ⊆ M). Let y ∈ Y ∖ E. Every x ∈ F_y lies in M₊ ∖ B (else y = f(x) ∈ E). So (CH) gives k_x, w_x ∈ O_{k_x} with G_{k_x}(w_x) = f(x) = y, and an orthonormal σ_x with span(range σ_x) = range DG_{k_x}(w_x) and Ξ(x) = ε_x‖Ξ(x)‖ • simpleNVector σ_x, ε_x ∈ {1, −1}. Then ϑ(x) = (ε_x θ(x)) • simpleNVector σ_x, and a_x := ε_x·θ(x) ∈ ℤ because θ(x) ∈ ℕ. Enumerate the finite set F_y as x_1,…,x_m via an equivalence with Fin m (`Fintype.equivFin`). Set a_i := a_{x_i}, k_i := k_{x_i}, w_i := w_{x_i}, σ_i := σ_{x_i}. Reindexing the finite sum of Step 6 gives Ψ(y) = Σ_i a_i • simpleNVector σ_i. Hⁿ⌞Y-a.e. y lies in Y ∖ E (Y null-measurable, E null), so this is the asserted a.e. family.
10. (Representation.) Fix ω ∈ Dⁿ(V). K_ω := tsupport ω is compact with K_ω ⊆ V, ω is continuous, and C_ω := sup_y |ω(y)| < ∞.
 (a) On M ∖ M₊, Ξ = 0, so the integrand of (S) vanishes. With M null-measurable and M₊ ⊆ M, `setIntegral_eq_of_subset_of_ae_sdiff_eq_zero` gives S(ω) = ∫_{M₊} θ(x)Ξ(x)(ω(f(x))) dHⁿ.
 (b) Let g(x) := ϑ(x)(ω(f(x))). It is Hⁿ⌞M₊-a.e. strongly measurable, because ω∘f is continuous on M and evaluation (ζ, α) ↦ ζ(α) is continuous. Since M is only null-measurable, pick a measurable M₀ ⊆ M with Hⁿ(M ∖ M₀) = 0 (`NullMeasurableSet.exists_measurable_subset_ae_eq`). Then Hⁿ⌞M = Hⁿ⌞M₀ and `ContinuousOn.aestronglyMeasurable` applies on M₀ ⊆ M. On M₊, g(x)·‖Ξ(x)‖ = θ(x)Ξ(x)(ω(f(x))). Also |g(x)|·‖Ξ(x)‖ = θ(x)|Ξ(x)(ω(f(x)))| ≤ C_ω θ(x)‖Ξ(x)‖ 1_{K_ω}(f(x)). So ∫⁻_{M₊} ‖g‖ₑ‖Ξ‖ₑ ≤ C_ω ∫⁻_{M ∩ f⁻¹(K_ω)} ofReal(θ)‖Ξ‖ₑ < ∞, by (LF) and the closed-set argument of Step 3.
 (c) Apply the sibling lemma lpf_pi_signed_fibre_sum with (X, μ) := (ℝ^P, Hⁿ), (Y, ν) := (ℝ^Q, Hⁿ), the map f, A := M₊, J := ‖Ξ‖ₑ (a.e. measurable), and g. Its area-identity hypothesis is (AF) for A = M₊. Since ‖Ξ(x)‖ₑ.toReal = ‖Ξ(x)‖, it gives ∫_{M₊} g‖Ξ‖ dHⁿ = ∫ Σ'_{x ∈ F_y} g(x) dHⁿ(y). By (b) the left side is the integral in (a).
 (d) For y ∈ Y: Σ'_{x ∈ F_y} g(x) = Σ_{x ∈ F_y} ϑ(x)(ω(y)) = (Σ_{x ∈ F_y} ϑ(x))(ω(y)) = Ψ(y)(ω(y)). Here f(x) = y on F_y, and a finite sum of linear maps is evaluated termwise. For y ∉ Y with N(y) ≠ ∞: either y ∉ V or N(y) = 0, and in both cases F_y = ∅, so the sum is 0. Since Hⁿ({N = ∞}) = 0 (Step 4), Σ'_{x ∈ F_y} g(x) = 1_Y(y)·Ψ(y)(ω(y)) for Hⁿ-a.e. y.
 (e) By (a)–(d) and null-measurability of Y (`integral_indicator₀`), S(ω) = ∫ 1_Y·Ψ(ω) dHⁿ = ∫_Y Ψ(y)(ω(y)) dHⁿ(y). ∎

Lean note (verified in this environment; engineering advice, not part of the mathematics). For maps into `NVector (Eucl Q) n`, instance search fails for `ContinuousAdd`, `TopologicalSpace.PseudoMetrizableSpace`, `ContinuousENorm` and `ContinuousEval`. So `AEStronglyMeasurable.add/.norm/.enorm`, `Finset.aestronglyMeasurable_fun_sum` and `continuous_eval` do not apply out of the box. Working replacements: (1) `have : ContinuousAdd (NVector (Eucl Q) n) := ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩`, after which finite sums and `.add` of a.e.-strongly-measurable n-vector fields work; (2) `(@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable h` for y ↦ ‖Ψ y‖, then `ofReal_norm` to pass to ‖·‖ₑ; (3) `continuous_fst.clm_apply continuous_snd` for continuity of (ζ, α) ↦ ζ α; (4) express sets such as {Ψ ≠ 0} as {‖Ψ‖ ≠ 0}, so null-measurability comes from the real-valued a.e.-measurable function ‖Ψ‖.

Verified Lean script (engineering aid; the mathematics is the numbered proof above). On 2026-10-12 the script below was compiled as the complete proof of `theorem Submission.lpf_pi_image_density : <the frozen Lean statement> := by` in the child context: `import GMT.Ch06.Submission`, inside `namespace GMT.Ch06` with the contract's `open` commands. It was compiled in one file together with the other ten children's proofs, which were real proofs, not stubs. `#print axioms` gives exactly propext, Classical.choice, Quot.sound. The script adds no helper declarations; all auxiliary facts are local `have`s. It uses the declared siblings `Submission.lpf_pi_signed_fibre_sum`, `Submission.lpf_pi_covector_finiteDimensional`. The remaining compiler output consists only of style-linter and deprecation warnings.
```
  intro P Q n V M θ Ξ f G O S hV hM hθpos hθnat hθm hΞm hfc hfV hnull hAF hLF hCH hS
  classical
  generalize hμdef : (μHE[n] : Measure (Eucl P)) = μ at *
  generalize hνdef : (μHE[n] : Measure (Eucl Q)) = ν at *
  have hCA : ContinuousAdd (NVector (Eucl Q) n) :=
    ⟨(inferInstance : IsTopologicalAddGroup (NVector (Eucl Q) n)).toContinuousAdd.continuous_add⟩
  -- Step 1: positive part
  have hθ1 : ∀ x ∈ M, 1 ≤ θ x := by
    intro x hx
    obtain ⟨k, hk⟩ := hθnat x hx
    have h0 := hθpos x hx
    rw [hk] at h0 ⊢
    have hk0 : 0 < k := by exact_mod_cast h0
    exact_mod_cast hk0
  obtain ⟨Mp, hMp⟩ : ∃ Mp : Set (Eucl P), Mp = {x | x ∈ M ∧ Ξ x ≠ 0} := ⟨_, rfl⟩
  have hMp_mem : ∀ x, x ∈ Mp ↔ x ∈ M ∧ Ξ x ≠ 0 := by intro x; rw [hMp]; rfl
  have hMpM : Mp ⊆ M := fun x hx => ((hMp_mem x).1 hx).1
  obtain ⟨M₀, hM₀M, hM₀m, hM₀ae⟩ := hM.exists_measurable_subset_ae_eq
  have hrestr : μ.restrict M₀ = μ.restrict M := Measure.restrict_congr_set hM₀ae
  have hnΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M₀) := by
    rw [hrestr]
    exact (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hMpnm : NullMeasurableSet Mp μ := by
    obtain ⟨φ, hφm, hφeq⟩ : ∃ φ : Eucl P → ℝ, Measurable φ ∧
        (fun x => ‖Ξ x‖) =ᵐ[μ.restrict M₀] φ :=
      ⟨hnΞ.mk _, hnΞ.stronglyMeasurable_mk.measurable, hnΞ.ae_eq_mk⟩
    have h1 : ∀ᵐ x ∂μ, x ∈ M₀ → ‖Ξ x‖ = φ x :=
      (ae_restrict_iff' hM₀m).1 hφeq
    have h2 : ∀ᵐ x ∂μ, x ∈ M₀ ↔ x ∈ M := eventuallyEqSet_iff.1 hM₀ae
    have hmeas : MeasurableSet (M₀ ∩ {x | φ x ≠ 0}) :=
      hM₀m.inter (hφm (measurableSet_singleton 0).compl)
    refine hmeas.nullMeasurableSet.congr (eventuallyEqSet_iff.2 ?_)
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hMp_mem]
    constructor
    · rintro ⟨hxM₀, hφx⟩
      refine ⟨hx2.1 hxM₀, ?_⟩
      intro hΞx
      apply hφx
      rw [← hx1 hxM₀, hΞx]
      exact ContinuousLinearMap.opNorm_zero
    · rintro ⟨hxM, hΞx⟩
      have hxM₀ : x ∈ M₀ := hx2.2 hxM
      refine ⟨hxM₀, ?_⟩
      show φ x ≠ 0
      rw [← hx1 hxM₀]
      exact fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
  have hAFp : ∀ h : Eucl P → ℝ≥0∞, AEMeasurable h (μ.restrict Mp) →
      AEMeasurable (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x) ν ∧
      ∫⁻ x in Mp, h x * ‖Ξ x‖ₑ ∂μ = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, h x ∂ν :=
    fun h hh => hAF Mp h hMpM hMpnm hh
  -- Step 2: counting function
  obtain ⟨N, hN⟩ : ∃ N : Eucl Q → ℝ≥0∞,
      N = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := ⟨_, rfl⟩
  have hθmp : AEMeasurable (fun x => ENNReal.ofReal (θ x)) (μ.restrict Mp) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hθm).mono_set hMpM
  have hNm : AEMeasurable N ν := by rw [hN]; exact (hAFp _ hθmp).1
  -- Step 3: closed-set argument and local finiteness
  have hclosed : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      ∃ C : Set (Eucl P), IsClosed C ∧ (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) ∧
        ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCeq⟩ := (continuousOn_iff_isClosed.mp hfc) K hK.isClosed
    refine ⟨C, hCc, ?_, ?_⟩
    · intro x hx
      constructor
      · intro hxC
        have : x ∈ C ∩ M := ⟨hxC, hx⟩
        rw [← hCeq] at this
        exact this.1
      · intro hfx
        have : x ∈ f ⁻¹' K ∩ M := ⟨hfx, hx⟩
        rw [hCeq] at this
        exact this.1
    · calc ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ
          ≤ ∫⁻ x in M, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_mono_set hMpM
        _ = ∫⁻ x in C ∩ M, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [lintegral_indicator hCc.measurableSet, Measure.restrict_restrict hCc.measurableSet]
        _ = ∫⁻ x in M ∩ f ⁻¹' K, ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ ∂μ := by
            rw [← hCeq, Set.inter_comm]
        _ < ∞ := hLF K hK hKV
  have hfib_ind : ∀ (K : Set (Eucl Q)) (C : Set (Eucl P)), (∀ x ∈ M, (x ∈ C ↔ f x ∈ K)) →
      ∀ (u : Eucl P → ℝ≥0∞) (y : Eucl Q),
        ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x =
          K.indicator (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, u x) y := by
    intro K C hC u y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      refine tsum_congr fun x => ?_
      have hxC : (x : Eucl P) ∈ C := (hC x (hMpM x.2.1)).2 (by rw [x.2.2]; exact hy)
      rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hy]
      have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, C.indicator u x = 0 := by
        intro x
        have hxC : (x : Eucl P) ∉ C := fun h => hy (by rw [← x.2.2]; exact (hC x (hMpM x.2.1)).1 h)
        rw [Set.indicator_of_notMem hxC]
      simp only [this, tsum_zero]
  have hNK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ∫⁻ y, K.indicator N y ∂ν < ∞ := by
    intro K hK hKV
    obtain ⟨C, hCc, hCK, hCfin⟩ := hclosed K hK hKV
    have hh : AEMeasurable (C.indicator (fun x => ENNReal.ofReal (θ x))) (μ.restrict Mp) :=
      hθmp.indicator hCc.measurableSet
    have key := (hAFp _ hh).2
    calc ∫⁻ y, K.indicator N y ∂ν
        = ∫⁻ y, ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y},
            C.indicator (fun x => ENNReal.ofReal (θ x)) x ∂ν := by
          refine lintegral_congr fun y => ?_
          rw [hfib_ind K C hCK, hN]
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x)) x * ‖Ξ x‖ₑ ∂μ := key.symm
      _ = ∫⁻ x in Mp, C.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
          refine lintegral_congr fun x => ?_
          by_cases hx : x ∈ C <;> simp [hx]
      _ < ∞ := hCfin
  -- Step 4/5: fibre facts
  have hNy : ∀ y, N y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
    intro y; rw [hN]
  have hfin : ∀ y, N y ≠ ∞ → Finite {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    apply hy
    rw [hNy, ← top_le_iff]
    calc (∞ : ℝ≥0∞) = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, (1 : ℝ≥0∞) :=
          (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
  have hempty : ∀ y, N y = 0 → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    rw [hNy, ENNReal.tsum_eq_zero] at hy
    refine ⟨fun x => ?_⟩
    have h1 := hy x
    rw [ENNReal.ofReal_eq_zero] at h1
    linarith [hθ1 x (hMpM x.2.1)]
  have hNge1 : ∀ y, N y ≠ 0 → 1 ≤ N y := by
    intro y hy
    rw [hNy] at hy ⊢
    obtain ⟨x, hx⟩ : ∃ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (ENNReal.tsum_eq_zero.2 h)
    calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (θ x) := by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hθ1 x (hMpM x.2.1))
      _ ≤ ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ENNReal.ofReal (θ x) :=
          ENNReal.le_tsum (f := fun x : {x : Eucl P // x ∈ Mp ∧ f x = y} => ENNReal.ofReal (θ x)) x
  have hnotV : ∀ y, y ∉ V → IsEmpty {x : Eucl P // x ∈ Mp ∧ f x = y} := by
    intro y hy
    refine ⟨fun x => hy ?_⟩
    rw [← x.2.2]
    exact hfV (hMpM x.2.1)
  -- Step 5: the set Y
  obtain ⟨Y, hY⟩ : ∃ Y : Set (Eucl Q), Y = {y | y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞} := ⟨_, rfl⟩
  have hY_mem : ∀ y, y ∈ Y ↔ y ∈ V ∧ N y ≠ 0 ∧ N y ≠ ∞ := by intro y; rw [hY]; rfl
  have hYV : Y ⊆ V := fun y hy => ((hY_mem y).1 hy).1
  have hYnm : NullMeasurableSet Y ν := by
    have h1 : NullMeasurableSet (N ⁻¹' {0}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton 0).compl
    have h2 : NullMeasurableSet (N ⁻¹' {∞}ᶜ) ν :=
      hNm.nullMeasurable (measurableSet_singleton ∞).compl
    have : Y = V ∩ (N ⁻¹' {0}ᶜ ∩ N ⁻¹' {∞}ᶜ) := by
      ext y; rw [hY_mem]; simp
    rw [this]
    exact hV.measurableSet.nullMeasurableSet.inter (h1.inter h2)
  have hYK : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V → ν (Y ∩ K) < ∞ := by
    intro K hK hKV
    have hsub : Y ∩ K ⊆ {y | 1 ≤ K.indicator N y} := by
      rintro y ⟨hyY, hyK⟩
      rw [Set.mem_ofPred_eq, Set.indicator_of_mem hyK]
      exact hNge1 y ((hY_mem y).1 hyY).2.1
    have hmk := mul_meas_ge_le_lintegral₀ (hNm.indicator hK.measurableSet) 1
    rw [one_mul] at hmk
    exact lt_of_le_of_lt (measure_mono hsub) (lt_of_le_of_lt hmk (hNK K hK hKV))
  -- Step 6: the density
  obtain ⟨ϑ, hϑ⟩ : ∃ ϑ : Eucl P → NVector (Eucl Q) n,
      ϑ = fun x => (θ x * ‖Ξ x‖⁻¹) • Ξ x := ⟨_, rfl⟩
  have hϑx : ∀ x, ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := fun x => by rw [hϑ]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Eucl Q → NVector (Eucl Q) n,
      Ψ = fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := ⟨_, rfl⟩
  have hΨy : ∀ y, Ψ y = ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := fun y => by rw [hΨ]
  have hnormΞ : AEStronglyMeasurable (fun x => ‖Ξ x‖) (μ.restrict M) :=
    (@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΞm
  have hϑm : AEStronglyMeasurable ϑ (μ.restrict Mp) := by
    rw [hϑ]
    have h1 : AEStronglyMeasurable (fun x => θ x * ‖Ξ x‖⁻¹) (μ.restrict M) :=
      (hθm.mul hnormΞ.aemeasurable.inv).aestronglyMeasurable
    exact (h1.smul hΞm).mono_set hMpM
  have hgβ : ∀ β : Covector (Eucl Q) n,
      AEStronglyMeasurable (fun x => ϑ x β) (μ.restrict Mp) :=
    fun β => (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hϑm
  -- Step 7: measurability of Ψ on Y
  have hΨβ : ∀ β : Covector (Eucl Q) n, AEMeasurable (fun y => Ψ y β) (ν.restrict Y) := by
    intro β
    have hp := (hAFp (fun x => ENNReal.ofReal (ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable)).1
    have hm := (hAFp (fun x => ENNReal.ofReal (-ϑ x β))
      (ENNReal.measurable_ofReal.comp_aemeasurable (hgβ β).aemeasurable.neg)).1
    refine ((hp.ennreal_toReal.sub hm.ennreal_toReal).mono_measure
      Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem₀ hYnm] with y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    simp only [Pi.sub_apply]
    rw [hΨy, tsum_fintype, tsum_fintype, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top),
      ENNReal.toReal_sum (fun x _ => ENNReal.ofReal_ne_top), ← Finset.sum_sub_distrib,
      sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    exact max_zero_sub_eq_self _
  have := Submission.lpf_pi_covector_finiteDimensional Q n
  obtain ⟨D, b, bs, hexp⟩ : ∃ (D : ℕ) (b : Fin D → Covector (Eucl Q) n)
      (bs : Fin D → NVector (Eucl Q) n), ∀ ζ : NVector (Eucl Q) n, ζ = ∑ i, ζ (b i) • bs i := by
    let bb := Module.finBasis ℝ (Covector (Eucl Q) n)
    refine ⟨_, bb, fun i => LinearMap.toContinuousLinearMap (bb.coord i), fun ζ => ?_⟩
    ext α
    have hα : α = ∑ i, bb.repr α i • bb i := (bb.sum_repr α).symm
    calc ζ α = ζ (∑ i, bb.repr α i • bb i) := by rw [← hα]
      _ = ∑ i, bb.repr α i * ζ (bb i) := by simp only [map_sum, map_smul, smul_eq_mul]
      _ = (∑ i, ζ (bb i) • LinearMap.toContinuousLinearMap (bb.coord i)) α := by
          rw [sum_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
  have hΨm : AEStronglyMeasurable Ψ (ν.restrict Y) := by
    have h1 : AEStronglyMeasurable (fun y => ∑ i, Ψ y (b i) • bs i) (ν.restrict Y) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (hΨβ (b i)).aestronglyMeasurable.smul_const (bs i)
    exact h1.congr (Eventually.of_forall fun y => (hexp (Ψ y)).symm)
  -- Step 8: integrability
  have hϑnorm : ∀ x ∈ Mp, ‖ϑ x‖ ≤ θ x := by
    intro x hx
    obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
    have hpos : 0 < ‖Ξ x‖ := lt_of_le_of_ne (norm_nonneg (Ξ x))
      (Ne.symm fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h))
    rw [hϑx]
    calc ‖(θ x * ‖Ξ x‖⁻¹) • Ξ x‖ ≤ ‖θ x * ‖Ξ x‖⁻¹‖ * ‖Ξ x‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = θ x := by
          rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hθpos x hxM) (inv_pos.2 hpos)),
            inv_mul_cancel_right₀ hpos.ne']
  have hΨnorm : ∀ y ∈ Y, ENNReal.ofReal ‖Ψ y‖ ≤ N y := by
    intro y hy
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hy).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    rw [hΨy, hNy, tsum_fintype, tsum_fintype,
      ← ENNReal.ofReal_sum_of_nonneg (fun (x : {x : Eucl P // x ∈ Mp ∧ f x = y}) _ =>
        zero_le_one.trans (hθ1 x (hMpM x.2.1)))]
    refine ENNReal.ofReal_le_ofReal ?_
    refine ContinuousLinearMap.opNorm_le_bound _
      (Finset.sum_nonneg fun x _ => zero_le_one.trans (hθ1 x (hMpM x.2.1))) fun α => ?_
    rw [sum_apply, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hϑnorm x x.2.1) (norm_nonneg α))
  have hint : ∀ K : Set (Eucl Q), IsCompact K → K ⊆ V →
      IntegrableOn (fun y => ‖Ψ y‖) (Y ∩ K) ν := by
    intro K hK hKV
    refine ⟨((@continuous_norm (NVector (Eucl Q) n) _).comp_aestronglyMeasurable hΨm).mono_set
      Set.inter_subset_left, ?_⟩
    show ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν < ∞
    calc ∫⁻ y in Y ∩ K, ‖‖Ψ y‖‖ₑ ∂ν ≤ ∫⁻ y in Y ∩ K, K.indicator N y ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem₀ (hYnm.inter hK.measurableSet.nullMeasurableSet)]
            with y hy
          rw [Real.enorm_eq_ofReal (norm_nonneg (Ψ y)), Set.indicator_of_mem hy.2]
          exact hΨnorm y hy.1
      _ ≤ ∫⁻ y, K.indicator N y ∂ν := setLIntegral_le_lintegral _ _
      _ < ∞ := hNK K hK hKV
  -- Step 9: chart family
  have hCH' := (ae_restrict_iff'₀ hM).1 hCH
  obtain ⟨Gd, hGd_ae, hGd⟩ := hCH'.exists_mem
  have hGdc : μ Gdᶜ = 0 := mem_ae_iff.1 hGd_ae
  have hBnull : μ (Gdᶜ ∩ M) = 0 := measure_mono_null Set.inter_subset_left hGdc
  have hE : ν (f '' (Gdᶜ ∩ M)) = 0 := hnull _ Set.inter_subset_right hBnull
  have hchart : ∀ᵐ y ∂(ν.restrict Y), ∃ (m : ℕ) (a : Fin m → ℤ) (k : Fin m → ℕ)
      (w : Fin m → Eucl n) (σ : Fin m → Fin n → Eucl Q),
      (∀ i, w i ∈ O (k i) ∧ G (k i) (w i) = y ∧ Orthonormal ℝ (σ i) ∧
        Submodule.span ℝ (range (σ i)) = LinearMap.range (fderiv ℝ (G (k i)) (w i)).toLinearMap) ∧
      Ψ y = ∑ i, (a i : ℝ) • simpleNVector (σ i) := by
    have hE' : ∀ᵐ y ∂ν, y ∉ f '' (Gdᶜ ∩ M) := measure_eq_zero_iff_ae_notMem.1 hE
    filter_upwards [ae_restrict_mem₀ hYnm, ae_restrict_of_ae hE'] with y hyY hyE
    have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
    have := hfin y hyN
    have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
    have hdata : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ∃ k, ∃ w ∈ O k, G k w = y ∧
        ∃ σ : Fin n → Eucl Q, Orthonormal ℝ σ ∧
          Submodule.span ℝ (range σ) = LinearMap.range (fderiv ℝ (G k) w).toLinearMap ∧
          ∃ a : ℤ, ϑ x = (a : ℝ) • simpleNVector σ := by
      intro x
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 x.2.1
      have hxGd : (x : Eucl P) ∈ Gd := by
        by_contra hc
        exact hyE ⟨x, ⟨hc, hxM⟩, x.2.2⟩
      obtain ⟨k, w, hw, hGw, σ, hσ, hspan, hsign⟩ := hGd x hxGd hxM hΞx
      obtain ⟨j, hj⟩ := hθnat x hxM
      refine ⟨k, w, hw, hGw.trans x.2.2, σ, hσ, hspan, ?_⟩
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rcases hsign with h | h
      · refine ⟨j, ?_⟩
        calc ϑ x = (θ x * ‖Ξ x‖⁻¹) • Ξ x := hϑx x
          _ = (θ x * ‖Ξ x‖⁻¹) • (‖Ξ x‖ • simpleNVector σ) := by rw [← h]
          _ = (θ x * ‖Ξ x‖⁻¹ * ‖Ξ x‖) • simpleNVector σ := smul_smul _ _ _
          _ = ((j : ℤ) : ℝ) • simpleNVector σ := by
              rw [inv_mul_cancel_right₀ hpos, hj, Int.cast_natCast]
      · refine ⟨-(j : ℤ), ?_⟩
        have hα : ∀ α : Covector (Eucl Q) n, Ξ x α = -(‖Ξ x‖ * α σ) := fun α =>
          congrArg (fun z : NVector (Eucl Q) n => z α) h
        rw [hϑx]
        ext α
        show (θ x * ‖Ξ x‖⁻¹) * Ξ x α = ((-(j : ℤ) : ℤ) : ℝ) * α σ
        rw [hα α, hj]
        have hr : ‖Ξ x‖⁻¹ * ‖Ξ x‖ = 1 := inv_mul_cancel₀ hpos
        calc (j : ℝ) * ‖Ξ x‖⁻¹ * -(‖Ξ x‖ * α σ) = -((j : ℝ) * (‖Ξ x‖⁻¹ * ‖Ξ x‖) * α σ) := by
              ring
          _ = ((-(j : ℤ) : ℤ) : ℝ) * α σ := by rw [hr]; push_cast; ring
    choose k w hw hGw σ hσ hspan a ha using hdata
    let e := Fintype.equivFin {x : Eucl P // x ∈ Mp ∧ f x = y}
    refine ⟨Fintype.card {x : Eucl P // x ∈ Mp ∧ f x = y}, fun i => a (e.symm i),
      fun i => k (e.symm i), fun i => w (e.symm i), fun i => σ (e.symm i),
      fun i => ⟨hw _, hGw _, hσ _, hspan _⟩, ?_⟩
    calc Ψ y = ∑ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, ϑ x := by rw [hΨy, tsum_fintype]
      _ = ∑ i, ϑ (e.symm i) := (e.symm.sum_comp (fun x => ϑ x)).symm
      _ = ∑ i, (a (e.symm i) : ℝ) • simpleNVector (σ (e.symm i)) :=
          Finset.sum_congr rfl fun i _ => ha (e.symm i)
  -- Step 10: representation
  have hrep : ∀ ω : TestFormOn V n,
      S ω = ∫ y in Y, Ψ y ((ω : DifferentialForm (Eucl Q) n) y) ∂ν := by
    intro ω
    obtain ⟨⟨hωs, hωc⟩, hωV⟩ := ω.2
    obtain ⟨Cω, hCω⟩ := hωc.exists_bound_of_continuous hωs.continuous
    have hCω0 : 0 ≤ Cω := (norm_nonneg _).trans (hCω 0)
    obtain ⟨Cl, hCl_closed, hCl_iff, hCl_fin⟩ := hclosed _ hωc.isCompact hωV
    obtain ⟨g, hg⟩ : ∃ g : Eucl P → ℝ,
        g = fun x => ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := ⟨_, rfl⟩
    have hgx : ∀ x, g x = ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x)) := fun x => by rw [hg]
    -- (a)
    have ha : S ω = ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ := by
      rw [hS ω]
      refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hM hMpM
        (Eventually.of_forall fun x hx => ?_)
      have : Ξ x = 0 := by
        by_contra hne
        exact hx.2 ((hMp_mem x).2 ⟨hx.1, hne⟩)
      rw [this, zero_apply, mul_zero]
    -- (b)
    have hb : ∫ x in Mp, θ x * Ξ x ((ω : DifferentialForm (Eucl Q) n) (f x)) ∂μ =
        ∫ x in Mp, g x * (‖Ξ x‖ₑ).toReal ∂μ := by
      refine setIntegral_congr_fun₀ hMpnm fun x hx => ?_
      obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
      have hpos : ‖Ξ x‖ ≠ 0 := fun h => hΞx ((norm_eq_zero (E := NVector (Eucl Q) n)).1 h)
      rw [hgx, hϑx, toReal_enorm, smul_apply, smul_eq_mul]
      field_simp
    have hωf : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
        (μ.restrict Mp) := by
      have h0 : AEStronglyMeasurable (fun x => (ω : DifferentialForm (Eucl Q) n) (f x))
          (μ.restrict M₀) :=
        (hωs.continuous.comp_continuousOn (hfc.mono hM₀M)).aestronglyMeasurable hM₀m
      rw [hrestr] at h0
      exact h0.mono_set hMpM
    have hgm : AEStronglyMeasurable g (μ.restrict Mp) := by
      rw [hg]
      exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hϑm.prodMk hωf)
    have hgfin : ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ < ∞ := by
      calc ∫⁻ x in Mp, ‖g x‖ₑ * ‖Ξ x‖ₑ ∂μ
          ≤ ∫⁻ x in Mp, ENNReal.ofReal Cω *
              Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem₀ hMpnm] with x hx
            obtain ⟨hxM, hΞx⟩ := (hMp_mem x).1 hx
            by_cases hxC : x ∈ Cl
            · rw [Set.indicator_of_mem hxC]
              have hgle : ‖g x‖ₑ ≤ ENNReal.ofReal Cω * ENNReal.ofReal (θ x) := by
                rw [← ENNReal.ofReal_mul hCω0, hgx, Real.enorm_eq_ofReal_abs]
                refine ENNReal.ofReal_le_ofReal ?_
                rw [← Real.norm_eq_abs]
                calc ‖ϑ x ((ω : DifferentialForm (Eucl Q) n) (f x))‖
                    ≤ ‖ϑ x‖ * ‖(ω : DifferentialForm (Eucl Q) n) (f x)‖ :=
                      ContinuousLinearMap.le_opNorm _ _
                  _ ≤ θ x * Cω := mul_le_mul (hϑnorm x hx) (hCω _) (norm_nonneg _)
                      (zero_le_one.trans (hθ1 x hxM))
                  _ = Cω * θ x := mul_comm _ _
              calc ‖g x‖ₑ * ‖Ξ x‖ₑ ≤ (ENNReal.ofReal Cω * ENNReal.ofReal (θ x)) * ‖Ξ x‖ₑ := by
                    gcongr
                _ = ENNReal.ofReal Cω * (ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) := mul_assoc _ _ _
            · have hfx : f x ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
                fun h => hxC ((hCl_iff x hxM).2 h)
              have : g x = 0 := by rw [hgx, image_eq_zero_of_notMem_tsupport hfx, map_zero]
              rw [this, enorm_zero, zero_mul]
              exact zero_le
        _ = ENNReal.ofReal Cω *
              ∫⁻ x in Mp, Cl.indicator (fun x => ENNReal.ofReal (θ x) * ‖Ξ x‖ₑ) x ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCl_fin
    have hJm : AEMeasurable (fun x => ‖Ξ x‖ₑ) (μ.restrict Mp) := by
      have h0 := (hnormΞ.aemeasurable.ennreal_ofReal).mono_set hMpM
      exact h0.congr (Eventually.of_forall fun x => ofReal_norm (Ξ x))
    obtain ⟨-, -, heq⟩ := Submission.lpf_pi_signed_fibre_sum (Eucl P) (Eucl Q) μ ν f Mp
      (fun x => ‖Ξ x‖ₑ) hJm hAFp g hgm hgfin
    -- (d)
    have hNfin : ∀ᵐ y ∂ν, y ∈ tsupport (ω : DifferentialForm (Eucl Q) n) → N y < ∞ := by
      have h1 := ae_lt_top' (hNm.indicator hωc.isCompact.measurableSet)
        (hNK _ hωc.isCompact hωV).ne
      filter_upwards [h1] with y hy hyK
      rwa [Set.indicator_of_mem hyK] at hy
    have hd : (fun y => ∑' x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x) =ᵐ[ν]
        Y.indicator (fun y => Ψ y ((ω : DifferentialForm (Eucl Q) n) y)) := by
      filter_upwards [hNfin] with y hy
      by_cases hyY : y ∈ Y
      · rw [Set.indicator_of_mem hyY]
        have hyN : N y ≠ ∞ := ((hY_mem y).1 hyY).2.2
        have := hfin y hyN
        have := Fintype.ofFinite {x : Eucl P // x ∈ Mp ∧ f x = y}
        rw [tsum_fintype, hΨy, tsum_fintype, sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hgx, x.2.2]
      · rw [Set.indicator_of_notMem hyY]
        by_cases hyV : y ∈ V
        · by_cases hN0 : N y = 0
          · have := hempty y hN0
            exact tsum_empty
          · have hNinf : N y = ∞ := by
              by_contra h
              exact hyY ((hY_mem y).2 ⟨hyV, hN0, h⟩)
            have hyK : y ∉ tsupport (ω : DifferentialForm (Eucl Q) n) :=
              fun hyK => (hy hyK).ne hNinf
            have : ∀ x : {x : Eucl P // x ∈ Mp ∧ f x = y}, g x = 0 := by
              intro x
              rw [hgx, x.2.2, image_eq_zero_of_notMem_tsupport hyK, map_zero]
            simp only [this, tsum_zero]
        · have := hnotV y hyV
          exact tsum_empty
    rw [ha, hb]
    refine heq.trans ?_
    rw [integral_congr_ae hd, integral_indicator₀ hYnm]
  exact ⟨Y, Ψ, hYV, hYnm, hYK, hΨm, hint, hchart, hrep⟩
```

## Key steps

1. M₊ = {Ξ ≠ 0} null-measurable; θ ≥ 1; normalised η = Ξ/‖Ξ‖ and ϑ = θη on M₊
2. Counting function N(y) = Σ_{F_y} θ is a.e. measurable; ∫_K N ≤ ∫_{M∩f⁻¹K} θ‖Ξ‖ < ∞ via (AF) and (LF)
3. N < ∞ a.e.; Y := {y ∈ V : 1 ≤ N < ∞} null-measurable with finite fibres and Hⁿ(Y ∩ K) < ∞
4. Ψ(y) = Σ_{F_y} ϑ: measurable via coordinate fibre sums N^±_β and a basis of the finite-dimensional covector space (sibling), locally integrable via ‖Ψ‖ ≤ N
5. Outside the null set f(B), every fibre point carries chart data from (CH), giving the integer chart family
6. Representation: restrict to M₊, apply lpf_pi_signed_fibre_sum to g = ϑ(ω∘f), identify fibre sums with Ψ(ω) a.e.

## Reference use

### local-project

Queries:
- `cat /mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json (mode local-project; project_commit d8d46c9587747dee0751a1f780fcafdba16a3886; mathlib_commit 25730c7c759d108ef87ab70af2342a196760f79d)`
- `cmp snapshot project/GMT/Ch06/{Contract,Submission}.lean against workspace GMT/Ch06/{Contract,Submission}.lean (identical)`
- `python3 over dag.json: frozen lean_statement/status of the 8 uncle nodes; all lean_name fields (226 unique); grep -c 'lpf_pi_' dag.json (0 matches)`
- `contract_scope(Contract.lean, 'GMT.Ch06.main_theorem') from verifier/gmt-compare.py (replay: open MeasureTheory Filter Set Metric; open scoped ENNReal NNReal Topology; namespace GMT.Ch06; open Poincare.SimonGMT.Chapter06; open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasWeightedApproximateTangentSpaceAt); open Poincare.SimonGMT.Chapter01 (dimensionalUpperDensity); noncomputable section; end)`
- `lean_contract.validate_lean_statement on all 11 child statements`
- `grep -n 'def CountablyRectifiable|theorem CountablyRectifiable.mono|theorem countablyRectifiable_range|theorem countablyRectifiable_iUnion|def HasWeightedApproximateTangentSpaceAt|theorem HasWeightedApproximateTangentSpaceAt.unique' simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `grep -n 'abbrev NVector|def covectorPullback|def nVectorPushforward|def simpleNVector|theorem nVectorPushforward_simple' simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean; 'abbrev Covector|abbrev DifferentialForm|def IsTestForm' Chapter06/Forms.lean; 'abbrev TestFormOn|structure GeometricCurrentOn' Chapter06/Currents.lean; 'def GeometricCurrentOn.support|theorem GeometricCurrentOn.support_subset_domain' Chapter06/CurrentLocalEquality.lean`
- `grep -n 'theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn' simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean (line 216)`
- `grep -n 'LocallyLipschitzOn.comp|protected lemma comp' mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean (only LocallyLipschitz.comp exists)`
- `lake build GMT.Ch06.Submission in /tmp/lpi3_scratch (scratch copy, .lake/packages linked to the pinned package tree)`
- `lake env lean Scratch/Stmts.lean (11 statements in comparator scope, only sorry warnings)`
- `lake env lean Scratch/Names.lean (#check of ~90 cited Mathlib/SimonGMT names; #synth Norm (NVector (Eucl 3) 2) = ContinuousLinearMap.hasOpNorm, ENorm via SeminormedAddGroup.toContinuousENorm, MeasureSpace (Eucl 3) = measureSpaceOfInnerProductSpace, Norm (Covector ..) = ContinuousAlternatingMap.instNormedAddCommGroup.toNorm)`
- `lake env lean Scratch/Inst.lean (#synth ContinuousAdd / PseudoMetrizableSpace / ContinuousENorm (NVector (Eucl 3) 2) fail; documented workarounds compile)`
- `lake env lean Scratch/Assembly.lean (parent from 19 stubs; #print axioms propext, sorryAx, Classical.choice, Quot.sound)`
- `lake env lean Scratch/AllChildren.lean and Scratch/E2E.lean (all 11 children proved in dependency order + parent assembly; per-child #print axioms = propext, Classical.choice, Quot.sound)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/project/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/local-references/197bdd4b88278494/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/GMT/Ch06/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/parent-supplied-natural-proof.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-pushforward-integrality-a1/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch06/.humanize/github-theorem-prover/runs/20261011T144224Z-6e4735dbca/nodes/root-lipschitz-pushforward-im-a1-locally-lipschitz-image-a1-inner-com-6be04fd41f/rlcr-plan-v1.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/FormsDuality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/mathlib/Mathlib/Topology/EMetricSpace/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/tmp/lpi3_scratch/Scratch/Stmts.lean`
- `/tmp/lpi3_scratch/Scratch/Names.lean`
- `/tmp/lpi3_scratch/Scratch/Inst.lean`
- `/tmp/lpi3_scratch/Scratch/Assembly.lean`
- `/tmp/lpi3_scratch/Scratch/AllChildren.lean`
- `/tmp/lpi3_scratch/Scratch/E2E.lean`

The snapshot (project d8d46c95, Mathlib 25730c7c) is byte-identical to the workspace Contract and Submission. The child scope is import GMT.Ch06.Submission plus the replayed namespace and opens. It provides the contract notions (IsRectifiableTriple, tauAction, IsIntegerMultiplicity) and SimonGMT Ch03 Rectifiable (CountablyRectifiable with mono/range/iUnion, HasWeightedApproximateTangentSpaceAt, .unique for θ x ≠ 0). It also provides Ch06 n-vectors (NVector = Covector →L[ℝ] ℝ with the operator norm, simpleNVector, nVectorPushforward_simple), test forms, currents and support_subset_domain, plus Ch02 euclideanHausdorffMeasure_image_le_of_lipschitzOn.

It does not provide:
- SimonGMT SubmanifoldCover (countablyRectifiable_image_contDiffOn_open) or Mathlib's Multilinear.FiniteDimensional; both facts are therefore separate import-free leaves.
- LocallyLipschitzOn.comp.
- Instance search on NVector for ContinuousAdd, PseudoMetrizableSpace, ContinuousENorm and NormSMulClass; the verified workarounds are recorded in the child texts.

No lpf_pi_* name is reserved in dag.json, and leaf plans forbid helper declarations, so every child script is a single theorem. All 11 frozen statements validate and elaborate in the comparator scope. All 11 children are fully proved in Lean with only propext, Classical.choice and Quot.sound, using only their declared siblings. The frozen parent type follows from them and the eight uncles by the stated assembly; its only sorryAx comes from the uncle stubs.
