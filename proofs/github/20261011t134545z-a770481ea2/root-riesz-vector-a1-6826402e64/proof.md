# Parent-supplied natural-language proof

- Parent DAG node: `root`
- Child DAG node: `root.riesz_vector-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

PROOF OF `RieszVector` (Simon, Ch. 1, Lemma 4.7, Theorem 4.10, Theorem 4.14; printed proofs, transcribed and completed; the L¹-duality step is localized to compact sets because a Radon measure on a general locally compact Hausdorff space need not be σ-finite).

Statement. Let X be a locally compact Hausdorff space, H a finite-dimensional real inner product space, and L : C_c(X; H) → ℝ linear such that for every compact K ⊆ X the set {L(f) : f ∈ C_c(X; H), |f(x)| ≤ 1 for all x, spt f ⊆ K} is bounded above. Then there are a Radon outer measure μ on X (Def. 4.6) and a μ-measurable ν : X → H (preimages of Borel sets are μ-measurable) with |ν| = 1 μ-a.e. and L(f) = ∫_X ⟨f, ν⟩ dμ for all f ∈ C_c(X; H) (integrals with respect to μ on the μ-measurable sets; Lean `caratheodoryMeasure μ`).

Dependency. Theorem 4.12 = sibling `riesz_positive` (Lean `Submission.riesz_positive : RieszPositive`).
Standard facts: Lemma 1.6 / Remark 1.7 (Carathéodory); Urysohn's lemma for locally compact Hausdorff spaces (Simon 4.4: for K compact ⊆ V open there is f ∈ C_c(X, [0, 1]) with f ≡ 1 near K and spt f ⊆ V); disjoint compact sets have disjoint open neighbourhoods (Simon 4.1); every compact set has an open neighbourhood with compact closure; simple functions are dense in L¹; for a finite measure space, every bounded linear functional on L¹ is given by a bounded measurable function (L¹–L^∞ duality); Zorn's lemma.

STEP 0 (reductions). Let n := dim H. If n = 0 then H = {0}, C_c(X; H) = {0}, L = 0, and μ := 0 (the zero outer measure, which satisfies (R1)–(R3)) with ν := 0 works: L(f) = 0 = ∫⟨f, ν⟩ dμ, ν is measurable, and “|ν| = 1 μ-a.e.” holds because μ = 0. Assume n ≥ 1. An orthonormal basis e₁, …, e_n of H gives a linear isometry H ≅ ℝⁿ preserving inner products; transporting L, the hypothesis and the conclusion along it, we may assume H = ℝⁿ (printed: “By using an orthonormal basis for H, it suffices to prove the theorem with H = ℝⁿ”). |·| is the Euclidean norm. K₊ := C_c(X, [0, ∞)).

STEP 1 (the positive functional; printed). For f ∈ K₊ let λ(f) := sup{L(ω) : ω ∈ C_c(X; ℝⁿ), |ω| ≤ f}.
 • 0 ≤ λ(f) < ∞: ω = 0 is admissible; if |ω| ≤ f then spt ω ⊆ spt f =: K, and if s := sup f > 0 then ω/s is admissible in the hypothesis for K, so L(ω) ≤ s·M_K with M_K an upper bound (if s = 0 then ω = 0).
 • λ(cf) = cλ(f) for c ≥ 0 (c = 0: only ω = 0; c > 0: ω ↦ cω is a bijection between the admissible sets).
 • λ(f + g) ≤ λ(f) + λ(g): given ω with |ω| ≤ f + g let ω₁ := fω/(f + g), ω₂ := gω/(f + g) where f + g > 0, and ω₁ = ω₂ := 0 where f + g = 0. Then ω₁ + ω₂ = ω, |ω₁| ≤ f, |ω₂| ≤ g, and ω₁, ω₂ ∈ C_c(X; ℝⁿ): they are continuous where f + g > 0, and at a point x₀ with f(x₀) + g(x₀) = 0 we have |ω_i(x)| ≤ |ω(x)| ≤ f(x) + g(x) → 0 as x → x₀; their supports lie in spt ω. So L(ω) = L(ω₁) + L(ω₂) ≤ λ(f) + λ(g).
 • λ(f + g) ≥ λ(f) + λ(g): if |ω₁| ≤ f and |ω₂| ≤ g then |ω₁ + ω₂| ≤ f + g, so L(ω₁) + L(ω₂) ≤ λ(f + g).
 Thus λ is an ℝ≥0-linear map K₊ → [0, ∞), and Theorem 4.12 (sibling `riesz_positive`) gives a Radon outer measure μ on X with
  (**) sup{L(ω) : |ω| ≤ f} = λ(f) = ∫_X f dμ for all f ∈ K₊.
 Consequently, for ω ∈ C_c(X; ℝⁿ): |ω| ∈ K₊ and L(ω) ≤ λ(|ω|), L(−ω) ≤ λ(|ω|), i.e.
  (†) |L(ω)| ≤ ∫_X |ω| dμ.

STEP 2 (Lemma 4.7; printed). If A is μ-measurable with μ(A) < ∞ then μ(A) = sup{μ(K) : K ⊆ A compact}. [Given ε > 0 choose open U ⊇ A with μ(U ∖ A) < ε (R2), compact K ⊆ U with μ(U ∖ K) < ε (R3), and open W ⊇ U ∖ A with μ(W) < 2ε (R2). Then K ∖ W is compact, K ∖ W ⊆ U ∖ W ⊆ A, and μ(A ∖ (K ∖ W)) ≤ μ(U ∖ K) + μ(W) < 3ε.]

STEP 3 (Theorem 4.10 for p = 1; printed). C_c(X) is dense in L¹(μ), and hence (componentwise) C_c(X; ℝⁿ) is dense in L¹(μ; ℝⁿ). [Let f ∈ L¹(μ), ε > 0. Choose a simple φ = Σ_{j=1}^N a_j1_{A_j} with distinct a_j ≠ 0 and pairwise disjoint μ-measurable A_j with ‖f − φ‖₁ < ε; then μ(A_j) < ∞. Let M > max|a_j| and η := ε/(2MN). By Step 2 choose compact K_j ⊆ A_j with μ(A_j ∖ K_j) < η and by (R2) open U_j ⊇ K_j with μ(U_j ∖ K_j) < η; replacing U_j by U_j ∩ U'_j with pairwise disjoint open U'_j ⊇ K_j (Simon 4.1), the U_j are pairwise disjoint. By Urysohn choose g_j ∈ C_c(X) with g_j = a_j on K_j, |g_j| ≤ |a_j|, spt g_j ⊆ U_j, and put g := Σ_jg_j. Then g = φ on ⋃K_j, |φ − g| ≤ 2M, and φ − g vanishes off ⋃_j((U_j ∖ K_j) ∪ (A_j ∖ K_j)), so ‖φ − g‖₁ ≤ 2M·Σ_j2η = 2ε and ‖f − g‖₁ < 3ε.]

STEP 4 (extension of L to L¹). Each ω ∈ C_c(X; ℝⁿ) is μ-integrable (bounded, μ(spt ω) < ∞). By (†), L(ω) depends only on the class of ω in L¹(μ; ℝⁿ) and |L(ω) − L(ω')| ≤ ‖ω − ω'‖₁. By Step 3, L extends uniquely to a linear functional L̄ on L¹(μ; ℝⁿ) with |L̄(F)| ≤ ‖F‖₁ (printed: “L_j(f) := L(fe_j) extends to a bounded linear functional on L¹(μ)”).

STEP 5 (local duality; printed “by the Riesz representation theorem for L¹(μ)”, applied on sets of finite measure). Let E be μ-measurable with μ(E) < ∞. For i = 1, …, n the map h ↦ L̄(1_E h e_i) is a linear functional on L¹(μ⌞E) of norm ≤ 1; since μ⌞E is finite, L¹–L^∞ duality gives a bounded μ-measurable ν_{E,i} (zero off E) with L̄(1_E h e_i) = ∫_E h ν_{E,i} dμ. Put ν_E := (ν_{E,1}, …, ν_{E,n}); then L̄(1_E G) = ∫_E ⟨G, ν_E⟩ dμ for all G ∈ L¹(μ; ℝⁿ).
 • |ν_E| ≤ 1 μ-a.e. on E: for η > 0 let S := {x ∈ E : |ν_E(x)| > 1 + η} and G := 1_S ν_E/|ν_E|; then (1 + η)μ(S) ≤ ∫_S|ν_E| dμ = L̄(1_E G) ≤ ‖G‖₁ = μ(S), so μ(S) = 0.
 • Consistency: if E ⊆ E' both have finite measure, then for bounded measurable G vanishing off E, ∫_E⟨G, ν_E⟩ dμ = L̄(1_E G) = L̄(1_{E'}G) = ∫_E⟨G, ν_{E'}⟩ dμ; with G := 1_E(ν_E − ν_{E'}) this gives ν_E = ν_{E'} μ-a.e. on E. Consequently, for any two compact F, F', ν_F = ν_{F∪F'} = ν_{F'} μ-a.e. on F ∩ F'.

STEP 6 (decomposition of a Radon measure into compact pieces).
 6.1 For compact F let S_F := {x ∈ F : μ(F ∩ O) > 0 for every open O ∋ x} (the support of μ⌞F). S_F is closed (if x ∈ F ∖ S_F, some open O ∋ x has μ(F ∩ O) = 0, and then O ∩ S_F = ∅), hence compact, and μ(F ∖ S_F) = 0: F ∖ S_F is μ-measurable with finite measure, every compact C ⊆ F ∖ S_F is covered by finitely many open O with μ(F ∩ O) = 0, so μ(C) = 0, and Step 2 gives μ(F ∖ S_F) = 0.
 6.2 By Zorn's lemma there is a family 𝓕 of compact sets, maximal among families with μ(F) > 0 for F ∈ 𝓕 and μ(F ∩ F') = 0 for distinct F, F' ∈ 𝓕 (the union of a chain of such families is such a family).
 6.3 For compact K, 𝓕_K := {F ∈ 𝓕 : μ(K ∩ F) > 0} is countable: for distinct F₁, …, F_N ∈ 𝓕 the sets F_i' := F_i ∖ ⋃_{l≠i}F_l are disjoint and μ(F_i ∖ F_i') = 0, so Σ_iμ(K ∩ F_i) = μ(K ∩ ⋃F_i') ≤ μ(K) < ∞; hence at most m·μ(K) members have μ(K ∩ F) > 1/m.
 6.4 For compact K, μ(K ∖ ⋃_{F∈𝓕_K}F) = 0: otherwise K' := K ∖ ⋃_{𝓕_K}F (μ-measurable, a countable union being removed) has 0 < μ(K') < ∞, and Step 2 gives a compact C ⊆ K' with μ(C) > 0; C is disjoint from every F ∈ 𝓕_K and μ(C ∩ F) ≤ μ(K ∩ F) = 0 for F ∈ 𝓕 ∖ 𝓕_K; C ∉ 𝓕 (else C ∈ 𝓕_K, but C ∩ C = C ≠ ∅); so 𝓕 ∪ {C} contradicts maximality.
 6.5 For compact K, 𝓕'_K := {F ∈ 𝓕 : S_F ∩ K ≠ ∅} is countable: choose an open O ⊇ K with Ō compact; if x ∈ S_F ∩ K then μ(F ∩ O) > 0, so μ(F ∩ Ō) > 0 and F ∈ 𝓕_{Ō}, which is countable by 6.3.
 6.6 For F ∈ 𝓕 let P_F := S_F ∖ ⋃_{F'∈𝓕, F'≠F}S_{F'}. The P_F are pairwise disjoint; for compact K, P_F ∩ K = ∅ unless F ∈ 𝓕'_K, and P_F ∩ K = (S_F ∩ K) ∖ ⋃_{F'∈𝓕'_K, F'≠F}S_{F'} is a Borel set (6.5). Moreover μ(K ∖ ⋃_{F∈𝓕'_K}P_F) = 0: a point x ∈ K in no P_F either lies outside ⋃_{F∈𝓕_K}F (a null set by 6.4), or lies in some F ∈ 𝓕_K but not in S_F (a subset of the null set F ∖ S_F, 6.1), or lies in S_F ∩ S_{F'} ⊆ F ∩ F' for some distinct F, F' ∈ 𝓕'_K (then F, F' ∈ 𝓕'_K since x ∈ K, and μ(F ∩ F') = 0); these are countably many null sets.

STEP 7 (gluing the local fields). Define ν : X → ℝⁿ by ν := ν_F on P_F (F ∈ 𝓕) and ν := e₁ on X ∖ ⋃_{F∈𝓕}P_F.
 7.1 (Localization principle.) A set T ⊆ X is μ-measurable if T ∩ K is μ-measurable for every compact K. [Let Y ⊆ X with μ(Y) < ∞ and ε > 0; by (R2) take open U ⊇ Y with μ(U) < ∞, and by (R3) (U is μ-measurable) a compact K ⊆ U with μ(U ∖ K) < ε. Since T ∩ K is μ-measurable, μ(Y ∩ T) + μ(Y ∖ T) ≤ μ(Y ∩ K ∩ T) + μ((Y ∩ K) ∖ T) + 2μ(Y ∖ K) ≤ μ(Y ∩ K) + 2ε ≤ μ(Y) + 2ε; conclude by Remark 1.3.]
 7.2 ν is μ-measurable: for a Borel G ⊆ ℝⁿ and compact K, ν^{−1}(G) ∩ K = ⋃_{F∈𝓕'_K}(ν_F^{−1}(G) ∩ P_F ∩ K) ∪ (either K ∖ ⋃_{F∈𝓕'_K}P_F or ∅, according as e₁ ∈ G or not), a countable union of μ-measurable sets; apply 7.1.
 7.3 For compact K, ν = ν_K μ-a.e. on K: on K ∩ P_F (F ∈ 𝓕'_K), ν = ν_F = ν_K μ-a.e. (Step 5, consistency on K ∩ F), and K ∖ ⋃_{F∈𝓕'_K}P_F is null (6.6). In particular |ν| ≤ 1 μ-a.e. on each compact set.

STEP 8 (representation; printed (*)). For ω ∈ C_c(X; ℝⁿ) let K := spt ω. Then ω = 1_Kω and, by Steps 4, 5 and 7.3,
  L(ω) = L̄(1_Kω) = ∫_K⟨ω, ν_K⟩ dμ = ∫_K⟨ω, ν⟩ dμ = ∫_X⟨ω, ν⟩ dμ.

STEP 9 (|ν| = 1 locally a.e.; printed argument). Let f ∈ K₊ and K := spt f.
 (i) For ω with |ω| ≤ f, Cauchy–Schwarz gives L(ω) = ∫⟨ω, ν⟩ dμ ≤ ∫ f|ν| dμ; by (**), ∫f dμ ≤ ∫f|ν| dμ.
 (ii) Let ν̂ := ν/|ν| where ν ≠ 0 and ν̂ := 0 elsewhere. 1_Kν̂ ∈ L¹(μ; ℝⁿ), so by Step 3 there are g_k ∈ C_c(X; ℝⁿ) with ∫|g_k − 1_Kν̂| dμ → 0. Let R be the nearest-point retraction of ℝⁿ onto the closed unit ball (R(y) = y for |y| ≤ 1, y/|y| otherwise); it is continuous, R(0) = 0, and |R(y) − v| ≤ |y − v| whenever |v| ≤ 1. So ĝ_k := R ∘ g_k ∈ C_c(X; ℝⁿ), |fĝ_k| ≤ f, and |ĝ_k − ν̂| ≤ |g_k − ν̂| on K. Hence, using |ν| ≤ 1 a.e. on K,
  |L(fĝ_k) − ∫f|ν| dμ| = |∫_K f⟨ĝ_k − ν̂, ν⟩ dμ| ≤ (sup f)∫|g_k − 1_Kν̂| dμ → 0,
 and L(fĝ_k) ≤ λ(f) = ∫f dμ by (**). So ∫f|ν| dμ ≤ ∫f dμ.
 Thus ∫f(1 − |ν|) dμ = 0 for every f ∈ K₊, with f(1 − |ν|) ≥ 0 a.e. For compact K choose (Urysohn) f ∈ K₊ with f ≡ 1 on K; then 1 − |ν| = 0 μ-a.e. on K. So |ν| = 1 μ-a.e. on every compact set.

STEP 10 (a field of norm exactly one). Let ν' := ν on {|ν| = 1} and ν' := e₁ on {|ν| ≠ 1}. Then ν' is μ-measurable ({|ν| = 1} is μ-measurable by 7.2), |ν'(x)| = 1 for every x ∈ X — so in particular |ν'| = 1 μ-a.e., i.e. μ({|ν'| ≠ 1}) = μ(∅) = 0 — and ν' = ν μ-a.e. on each compact set (Step 9), so Step 8 gives L(ω) = ∫_{spt ω}⟨ω, ν'⟩ dμ = ∫_X⟨ω, ν'⟩ dμ for all ω ∈ C_c(X; ℝⁿ). (Replacing ν by ν' avoids asserting that a set which is null on every compact set is globally null, which may fail for non-σ-finite Radon measures.)

Conclusion. μ (Step 1) is a Radon outer measure and ν' : X → ℝⁿ ≅ H is μ-measurable with |ν'| = 1 μ-a.e. and L(f) = ∫_X⟨f, ν'⟩ dμ for every f ∈ C_c(X; H). ∎

Formalization note (non-binding): `Poincare.SimonGMT.Chapter01.simon_theorem_4_14` (Chapter01/RadonPolarRepresentation.lean) proves exactly this statement: its hypothesis `IsLocallyBoundedCcFunctional L` unfolds to the contract's bounded-above hypothesis, its measure `hμ.toCaratheodoryMeasure` is by definition `@OuterMeasure.toMeasure X μ.caratheodory μ le_rfl` (= `caratheodoryMeasure μ`), and its a.e. statement for `hμ.toCaratheodoryMeasure` transfers to μ because both agree on all sets (`IsRadonOuterMeasure.toCaratheodoryMeasure_apply_all`).

## Key steps

1. Reduce to H = ℝⁿ by an orthonormal basis; n = 0 is handled by μ = 0.
2. λ(f) := sup{L(ω) : |ω| ≤ f} is additive and positively homogeneous; Theorem 4.12 gives a Radon μ with λ(f) = ∫f dμ, hence |L(ω)| ≤ ∫|ω| dμ.
3. Lemma 4.7 and Theorem 4.10 (C_c dense in L¹); extend L to L̄ on L¹(μ; ℝⁿ) with norm ≤ 1.
4. Local L¹–L^∞ duality on each set of finite measure gives consistent fields ν_E with |ν_E| ≤ 1.
5. A maximal almost-disjoint family of compacts, with supports S_F and cores P_F, glues the ν_F into one ν, measurable by the compact localization principle.
6. Representation L(ω) = ∫⟨ω, ν⟩ dμ; |ν| = 1 locally a.e. via Cauchy–Schwarz and approximants composed with the radial retraction.
7. Replace non-unit values by e₁: |ν'| = 1 everywhere, with the same representation and measurability.

## Reference use

### local-project

Queries:
- `cat manifest.json (snapshot root e8e26216f05cbb4e)`
- `rg -n '^def (CaratheodoryCriterion|BorelRegularApproximation|LusinTheorem|LebesgueEqHausdorff|IsodiametricInequality|UpperDensityComparison|UpperDensityTheorem|BesicovitchCovering|GeneralDensityTheorem|LebesgueDifferentiation|RadonNikodymTheorem|HausdorffDensityBounds|RieszPositive|RieszVector|RadonCompactness)|^theorem main_theorem|^universe|^open|^namespace' project/GMT/Ch01/Contract.lean`
- `cmp project/GMT/Ch01/Contract.lean project/GMT/Ch01/Submission.lean`
- `rg -n -c Poincare.SimonGMT project mathlib/Mathlib`
- `rg -n 'theorem simon_theorem' . (no match: SimonGMT is not in the snapshot)`
- `rg -n 'theorem borel_le_caratheodory|def IsMetric' mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `rg -n '^theorem exist_disjoint_covering_families|^theorem isEmpty_satelliteConfig_multiplicity|def multiplicity' mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `rg -n 'theorem integral_rieszMeasure|instance rieszMeasure_regular|instance regular_rieszMeasure' mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `rg -n 'theorem volume_ball|theorem volume_closedBall' mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `rg -n 'def IsCaratheodory|def caratheodory |theorem isCaratheodory_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `rg -n 'theorem toMeasure_apply|theorem le_toMeasure_apply' mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean; rg -n 'theorem ae_iff' mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `rg -n 'theorem setLIntegral_trim_ae|theorem lintegral_trim_ae' mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean; rg -n 'theorem integral_trim_ae|theorem integral_trim ' mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean; rg -n 'theorem restrict_trim' mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `rg -n 'sigmaCompactSpace_of_locallyCompact_secondCountable|noncomputable def choice|theorem exists_superset_of_isCompact' mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `rg -n '^instance|^theorem' mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean; rg -n 'metrizableSpace_of_t3_secondCountable' mathlib/Mathlib/Topology/Metrizable/Urysohn.lean; rg -n 'theorem exists_compact_superset' mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `rg -n 'theorem exists_continuous_one_zero_of_isCompact' mathlib/Mathlib/Topology/UrysohnsLemma.lean; rg -n 'theorem IsCompact.tendsto_subseq' mathlib/Mathlib/Topology/Sequences.lean`
- `rg -n 'theorem tendsto_iff_forall_integral_tendsto' mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean; rg -n -F 'CompactSpace (ProbabilityMeasure' mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean; rg -n 'theorem measure_iUnion_le|theorem measure_mono_null' mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `test -f on every cited snapshot file (all present); cmp of cited Mathlib files against lake-packages-25730c7c/mathlib (identical)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/GMT/Ch01/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/PROBLEM.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lakefile.toml`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/project/lake-manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/Besicovitch.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Caratheodory.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/OuterMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/AE.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/OuterMeasure/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Trim.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/SigmaCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Sequences.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/UrysohnsLemma.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/ContinuousMap/SecondCountableSpace.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Metrizable/Urysohn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/FiniteMeasure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch01/.humanize/github-theorem-prover/runs/20261011T134545Z-a770481ea2/local-references/e8e26216f05cbb4e/mathlib/Mathlib/MeasureTheory/Measure/Prokhorov.lean`

The manifest pins project ec1c322 and Mathlib 25730c7c. In the snapshot, project/GMT/Ch01/Contract.lean is byte-identical to Submission.lean. It defines exactly the fifteen Props CaratheodoryCriterion … RadonCompactness (lines 88–303), with main_theorem at line 313, inside namespace GMT.Ch01 with `universe u v` (line 69) and the opens at lines 63–65. Each child lean_statement is one of these Props or a conjunction of two of them; the two merged children with universe parameters share the declared universe u, which the comparator replays from that scope. README.md maps the conjuncts to SimonGMT theorems and documents the 4.16 erratum (second countability). That erratum is applied in radon_compactness. The snapshot contains no SimonGMT declarations: rg finds 'Poincare.SimonGMT' only as imports and opens in the project files, and 'theorem simon_theorem' has no match. The package is pinned in project/lake-manifest.json and lives outside the snapshot, so the children cite it only in non-binding formalization notes. The snapshot's Mathlib contains the facts those notes rely on:
- OuterMeasure.IsMetric and borel_le_caratheodory: Measure/Hausdorff.lean:137,161.
- Besicovitch.exist_disjoint_covering_families (Covering/Besicovitch.lean:455), multiplicity and isEmpty_satelliteConfig_multiplicity (BesicovitchVectorSpace.lean:98,488).
- NNRealRMK.integral_rieszMeasure and rieszMeasure_regular (RieszMarkovKakutani/NNReal.lean:47,66); the real RMK (Real.lean:345,357).
- EuclideanSpace.volume_ball and volume_closedBall: Lebesgue/VolumeOfBalls.lean:307,324.
- IsCaratheodory and the caratheodory σ-algebra: OuterMeasure/Caratheodory.lean:55,176,181.
- toMeasure_apply and le_toMeasure_apply (Measure/OuterMeasure.lean:46,50); ae_iff (OuterMeasure/AE.lean:134).
- setLIntegral_trim_ae (Integral/Lebesgue/Add.lean:490); integral_trim and integral_trim_ae (Bochner/Basic.lean:1301,1332); restrict_trim (Measure/Trim.lean:108).
- σ-compactness and compact exhaustions: SigmaCompact.lean:187,376,418.
- Urysohn's lemma: UrysohnsLemma.lean:404.
- Separability of C(X,Y): ContinuousMap/SecondCountableSpace.lean:108. Metrizability: Metrizable/Urysohn.lean:127.
- Compact supersets: LocallyCompact.lean:58. IsCompact.tendsto_subseq: Sequences.lean:298.
- Weak convergence and Prokhorov: FiniteMeasure.lean:727; Prokhorov.lean:176.
The cited Mathlib files are byte-identical to the packages used by the build. The mathematical arguments of the children are the printed proofs of the source and do not depend on these declarations.
