# Parent-supplied natural-language proof

- Parent DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1`
- Child DAG node: `root.dimension_reduction_results-a1.moving_blowups-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1.cutoff_extension-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent-supplied proof of dmcbr_closure_succ, step 8 (extension to ℝ^P: X̂(ω) := X(ζω) with a cutoff ζ ∈ C^∞_c(U) equal to 1 near K), together with the facts about the extension used in its steps 9–11 (integer multiplicity, support, mass and boundary-mass bounds, weak convergence, agreement with the original current on forms supported in K). This is the transfer to U = ℝ^P in Simon Ch. 6, Remark 8.3(1) (book/chapter-06.txt lines 2311–2318, printed p. 176). The vanishing hypothesis in (iv) replaces the appeal to (VO) in step 8: it is exactly what (VO) yields from spt X ⊆ K, and the sibling localize supplies it directly. Sibling dependency: SMC = dmcbrcs_testFormOnConverges_smul (key smul_continuity): if ζ : ℝ^P → ℝ is C^∞ with compact support and tsupport ζ ⊆ U, ω_j → 0 in 𝒟^k(ℝ^P) and η_j ∈ 𝒟^k(U) satisfy η_j(x) = ζ(x)•ω_j(x), then η_j → 0 in 𝒟^k(U). Notation: for a covector α, |α| is the Euclidean coefficient norm covectorEuclideanNorm α; 𝒟^k(V) = TestFormOn V k (C^∞ k-forms on ℝ^P with compact support and tsupport ⊆ V); ι := testFormOnInclusion (subset_univ U) (m+1) : 𝒟^{m+1}(U) → 𝒟^{m+1}(ℝ^P), which does not change the underlying form.
1. (Cutoff.) ℝ^P is locally compact and regular, so (Mathlib exists_open_between_and_isCompact_closure) there is an open V₁ with K ⊆ V₁, closure V₁ ⊆ U and closure V₁ compact; applying the same lemma to the compact set closure V₁ ⊆ U gives an open V₂ with closure V₁ ⊆ V₂, closure V₂ ⊆ U and closure V₂ compact. By the smooth Urysohn lemma for finite-dimensional real normed spaces (Mathlib exists_contDiff_support_eq_eq_one_iff, Mathlib/Geometry/Manifold/PartitionOfUnity.lean, available after `import GMT.Ch07.Submission`; smoothness order ⊤ : ℕ∞, s := V₂ open, t := closure V₁ closed, t ⊆ s) there is ζ : ℝ^P → ℝ with ContDiff ℝ ⊤ ζ, range ζ ⊆ [0, 1], support ζ = V₂, and ζ(x) = 1 for every x ∈ closure V₁. Put K₂ := tsupport ζ = closure (support ζ) = closure V₂, a compact subset of U (so ζ has compact support), and N := V₁, an open set with K ⊆ N on which ζ = 1.
2. (Multiplication by ζ.) For a k-form ω on ℝ^P let ζω be x ↦ ζ(x)•ω(x). If ω ∈ 𝒟^k(ℝ^P), then ζω is C^∞ (ContDiff.smul), tsupport(ζω) ⊆ tsupport ω (tsupport_smul_subset_right), which is compact, so ζω has compact support (a closed subset of a compact set), and tsupport(ζω) ⊆ tsupport ζ = K₂ ⊆ U (tsupport_smul_subset_left). So ζω ∈ 𝒟^k(U). The map M_k : 𝒟^k(ℝ^P) → 𝒟^k(U), ω ↦ ζω, is ℝ-linear, because pointwise ζ(x)•(ω + η)(x) = ζ(x)•ω(x) + ζ(x)•η(x) and ζ(x)•(cω(x)) = c(ζ(x)•ω(x)).
3. (Norm homogeneity.) For c ∈ ℝ and a k-covector α, |cα| = |c|·|α|: each coefficient α(e_{I_1}, …, e_{I_k}) with I strictly increasing is multiplied by c, so the sum of squares is multiplied by c², and √(c²s) = |c|√s (Real.sqrt_mul, Real.sqrt_sq_eq_abs). Hence, as 0 ≤ ζ ≤ 1, |ω(x)| ≤ 1 for all x implies |(ζω)(x)| = ζ(x)|ω(x)| ≤ 1 for all x.
4. (Sequential continuity of M_k.) If ω_j → 0 in 𝒟^k(ℝ^P) (TestFormOnConverges), then M_k ω_j → 0 in 𝒟^k(U): this is SMC applied to ζ (C^∞, compact support, tsupport ζ = K₂ ⊆ U), the sequence (ω_j) and η_j := M_k ω_j, for which η_j(x) = ζ(x)•ω_j(x) holds by definition.
5. (Definition of E.) For X ∈ 𝒟_{m+1}(U) let E X have underlying linear map X ∘ M_{m+1}, i.e. (E X)(ω) := X(ζω) for ω ∈ 𝒟^{m+1}(ℝ^P). If ω_j → 0 in 𝒟^{m+1}(ℝ^P), then M_{m+1}ω_j → 0 in 𝒟^{m+1}(U) by step 4, so (E X)(ω_j) = X(M_{m+1}ω_j) → 0 by the continuity field of X. Thus E X ∈ 𝒟_{m+1}(ℝ^P) (a GeometricCurrentOn univ (m+1)).
6. (Proof of (i).) Let ω ∈ 𝒟^{m+1}(U) with tsupport ω ⊆ K. For x ∈ K ⊆ N, ζ(x) = 1 and ζ(x)•ω(x) = ω(x); for x ∉ K, x ∉ tsupport ω, so ω(x) = 0 = ζ(x)•ω(x). Hence ζ·(ιω) = ω pointwise, so M_{m+1}(ιω) = ω in 𝒟^{m+1}(U) (Subtype.ext and funext), and (E X)(ιω) = X(ω).
7. (Proof of (ii).) If X_j ⇀ X in U then, for every ω ∈ 𝒟^{m+1}(ℝ^P), (E X_j)(ω) = X_j(M_{m+1}ω) → X(M_{m+1}ω) = (E X)(ω), since M_{m+1}ω is one fixed element of 𝒟^{m+1}(U). So E X_j ⇀ E X in ℝ^P.
8. (Proof of (iii).) M(E X) = M_{ℝ^P}(E X) is the supremum of ofReal((E X)(ω)) over ω ∈ 𝒟^{m+1}(ℝ^P) with |ω(x)| ≤ 1 for all x (tsupport ω ⊆ ℝ^P holds trivially). For such ω, M_{m+1}ω ∈ 𝒟^{m+1}(U) has tsupport ⊆ U and |ζω| ≤ 1 (step 3), so it is admissible for M_U(X), and ofReal((E X)(ω)) = ofReal(X(M_{m+1}ω)) ≤ M_U(X) = M(X) (GeometricCurrentOn.le_massOn). Taking the supremum (sSup_le) gives M(E X) ≤ M(X).
9. (Proof of (iv), support.) Assume X(ω) = 0 for every ω ∈ 𝒟^{m+1}(U) whose topological support is disjoint from K. Let x ∈ ℝ^P ∖ K. K is compact, hence closed, so (Metric.isOpen_iff for the open set ℝ^P ∖ K) there is ε > 0 with ball(x, ε) ∩ K = ∅; let W := ball(x, ε/2). W is open, x ∈ W, closure W ⊆ closedBall(x, ε/2) (closure_ball_subset_closedBall), so closure W is compact, and closure W ⊆ ℝ^P. For ω ∈ 𝒟^{m+1}(ℝ^P) with tsupport ω ⊆ W: tsupport(ζω) ⊆ tsupport ω ⊆ W ⊆ ball(x, ε) (step 2), which is disjoint from K, so (E X)(ω) = X(M_{m+1}ω) = 0. Thus E X vanishes on W, W belongs to the family whose union is the zero region of E X, x lies in that zero region, and x ∉ spt(E X) = ℝ^P ∖ zeroRegion(E X). Therefore spt(E X) ⊆ K.
10. (Proof of (iv), boundary mass.) Under the same assumption let η ∈ 𝒟^m(ℝ^P) with |η(x)| ≤ 1 for all x. By the definition of the boundary (∂Y(η) = Y(dη), through exteriorDerivativeTestOn), ∂(E X)(η) = (E X)(dη) = X(ζ·dη) and ∂X(ζη) = X(d(ζη)); here d is SimonGMT's exteriorDerivative, an abbreviation of Mathlib's extDeriv (Chapter06/Forms.lean). Let δ := d(ζη) − ζ·dη, the difference of the two elements exteriorDerivativeTestOn U m (M_m η) and M_{m+1}(exteriorDerivativeTestOn univ m η) of 𝒟^{m+1}(U). For y ∈ N the forms ζη and η agree on the open neighbourhood N of y (ζ = 1 on N), i.e. ζη =ᶠ[𝓝 y] η, so d(ζη)(y) = dη(y) (Mathlib Filter.EventuallyEq.extDeriv_eq), and ζ(y)·dη(y) = dη(y). Hence δ = 0 on N, so support δ ⊆ ℝ^P ∖ N; this set is closed, so tsupport δ ⊆ ℝ^P ∖ N (closure_minimal), which is disjoint from K ⊆ N. The hypothesis gives X(δ) = 0, and by linearity X(δ) = X(d(ζη)) − X(ζ·dη), so ∂(E X)(η) = X(ζ·dη) = X(d(ζη)) = ∂X(ζη). Since ζη ∈ 𝒟^m(U) satisfies |ζη| ≤ 1 (step 3) and tsupport(ζη) ⊆ U, it is admissible for M_U(∂X), so ofReal(∂(E X)(η)) ≤ M_U(∂X) = M(∂X). Taking the supremum over η gives M(∂(E X)) ≤ M(∂X).
11. (Proof of (v).) Let R = (M, θ, ξ) be an IMRep in U representing X with M ⊆ K. Let R̂ have the same carrier, multiplicity and orientation, regarded in ℝ^P. The fields measurableSet_carrier, rectifiable, measurable_mult, mult_pos, aestronglyMeasurable_orient and orients do not mention the domain and are inherited (HasApproximateTangentSpaceAt n M x Q depends only on M, x and Q), and carrier_subset holds because M ⊆ ℝ^P. For locallyIntegrable_mult let K′ ⊆ ℝ^P be compact: as M ⊆ K, M ∩ K′ ⊆ M ∩ K, so ∫_{M∩K′} θ dH^{m+1} ≤ ∫_{M∩K} θ dH^{m+1} (lintegral_mono_set) < ∞ by R's own locallyIntegrable_mult field applied to the compact set K ⊆ U. So R̂ is an IMRep in ℝ^P. For ω ∈ 𝒟^{m+1}(ℝ^P), (E X)(ω) = X(ζω) = R.action(ζω) = ∫_M θ(x)·ξ(x)(ζ(x)•ω(x)) dH^{m+1}(x); for x ∈ M ⊆ K ⊆ N we have ζ(x) = 1, so the integrand equals θ(x)·ξ(x)(ω(x)) on M (setIntegral_congr_fun on the measurable set M), and (E X)(ω) = ∫_M θ(x)·ξ(x)(ω(x)) dH^{m+1}(x) = R̂.action(ω). Hence R̂ represents E X, and E X is integer multiplicity.
12. (Conclusion.) The map E of step 5 satisfies (i) (step 6), (ii) (step 7), (iii) (step 8), (iv) (steps 9–10) and (v) (step 11). ∎

Appendix (verified Lean realization of the numbered proof above; not part of the proof). The declaration below was compiled in the decomposition session of dmcbr_closure_succ with Lean v4.35.0-rc3, Mathlib 25730c7c and SimonGMT 2b366308 inside a copy of GMT/Ch07/Contract.lean (namespace GMT.Ch07, after the `noncomputable section ... end` block, before `main_theorem`), i.e. under the frozen imports only, with default options (no `set_option`), as one theorem with local `have`s and no helper declaration. Its only dependency, Submission.dmcbrcs_testFormOnConverges_smul, was present with the proof of the sibling smul_continuity (itself proved from smul_leibniz). `#print axioms` reports propext, Classical.choice and Quot.sound. The runtime's leaf source-delta checker (_recursive_lean/leaf_verification.check_source_delta) accepts the insertion.

```lean
theorem Submission.dmcbrcs_cutoff_extension : ∀ (P m : ℕ) (U K : Set (Euclid P)), IsOpen U → IsCompact K → K ⊆ U → ∃ E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn U (m + 1)), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ K → E X (testFormOnInclusion (subset_univ U) (m + 1) ω) = X ω) ∧ (∀ (Xs : ℕ → GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn U (m + 1)), WeaklyConvergesOn Xs X → WeaklyConvergesOn (fun j => E (Xs j)) (E X)) ∧ (∀ X : GeometricCurrentOn U (m + 1), (E X).mass ≤ X.mass) ∧ (∀ X : GeometricCurrentOn U (m + 1), (∀ ω : TestFormOn U (m + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (m + 1))) K → X ω = 0) → (E X).support ⊆ K ∧ (E X).boundary.mass ≤ X.boundary.mass) ∧ (∀ (X : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)), R.Represents X → R.carrier ⊆ K → IsIntegerMultiplicity (E X)) := by
  have hC := Submission.dmcbrcs_testFormOnConverges_smul
  intro P m U K hU hK hKU
  -- Step 1: the cutoff ζ
  obtain ⟨V₁, hV₁o, hKV₁, hV₁U, hV₁c⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨V₂, hV₂o, hV₁V₂, hV₂U, hV₂c⟩ := exists_open_between_and_isCompact_closure hV₁c hU hV₁U
  obtain ⟨ζ, hζs, hζr, hζsupp, hζone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₂o isClosed_closure hV₁V₂
  have htsζ : tsupport ζ = closure V₂ := by rw [tsupport, hζsupp]
  have hζc : HasCompactSupport ζ := by
    rw [HasCompactSupport, htsζ]; exact hV₂c
  have hζU : tsupport ζ ⊆ U := htsζ ▸ hV₂U
  have hζ1 : ∀ x ∈ V₁, ζ x = 1 := fun x hx => (hζone x).1 (subset_closure hx)
  have hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1 := fun x => hζr (mem_range_self x)
  -- Step 3: absolute homogeneity of the Euclidean coefficient norm
  have hnorm : ∀ (k : ℕ) (c : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro k c α
    unfold covectorEuclideanNorm
    have hsum : (∑ I : Fin k → Fin P, if StrictMono I then
          ((c • α) (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
        = c ^ 2 * ∑ I : Fin k → Fin P, if StrictMono I then
          (α (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
      · rw [mul_zero]
    rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hadm : ∀ (k : ℕ) (ω : DifferentialForm (Euclid P) k), (∀ x, covectorEuclideanNorm (ω x) ≤ 1) →
      ∀ x, covectorEuclideanNorm (ζ x • ω x) ≤ 1 := by
    intro k ω hω x
    rw [hnorm, abs_of_nonneg (hζ01 x).1]
    exact (mul_le_mul (hζ01 x).2 (hω x) (covectorEuclideanNorm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  -- Step 2: multiplication by ζ
  have hmem : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ∈ TestFormOn U k := by
    intro k ω
    have hω : IsTestForm (ω : DifferentialForm (Euclid P) k) ∧
        tsupport (ω : DifferentialForm (Euclid P) k) ⊆ univ := ω.property
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) k) := hω.1.1
    have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k)) := hω.1.2
    have hsub : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆
        tsupport (ω : DifferentialForm (Euclid P) k) :=
      tsupport_smul_subset_right (fun x => ζ x) _
    have hsubζ : tsupport (fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) ⊆ tsupport ζ :=
      tsupport_smul_subset_left (fun x => ζ x) _
    have hcpt : IsCompact (tsupport fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x) :=
      hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
    exact ⟨⟨hζs.smul hsmooth, hcpt⟩, hsubζ.trans hζU⟩
  let Mk : (k : ℕ) → TestFormOn (univ : Set (Euclid P)) k →ₗ[ℝ] TestFormOn U k := fun k =>
    { toFun := fun ω => ⟨fun x => ζ x • (ω : DifferentialForm (Euclid P) k) x, hmem k ω⟩
      map_add' := fun ω η => by
        apply Subtype.ext; funext x
        change ζ x • ((ω : DifferentialForm (Euclid P) k) x + (η : DifferentialForm (Euclid P) k) x) =
          ζ x • (ω : DifferentialForm (Euclid P) k) x + ζ x • (η : DifferentialForm (Euclid P) k) x
        rw [smul_add]
      map_smul' := fun c ω => by
        apply Subtype.ext; funext x
        change ζ x • (c • (ω : DifferentialForm (Euclid P) k) x) =
          c • (ζ x • (ω : DifferentialForm (Euclid P) k) x)
        rw [smul_comm] }
  have hMk : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k) (x : Euclid P),
      ((Mk k ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
        ζ x • (ω : DifferentialForm (Euclid P) k) x := fun _ _ _ => rfl
  -- Step 5: the extension
  let E : GeometricCurrentOn U (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) :=
    fun X =>
      { toCurrent := X.toCurrent.comp (Mk (m + 1))
        continuous' := fun ωs hω => by
          have h1 := hC P (m + 1) U ζ ωs (fun j => Mk (m + 1) (ωs j)) hζs hζc hζU hω
            (fun j x => rfl)
          have h2 := X.continuous' _ h1
          have h3 : (fun j => X.toCurrent ((fun j => Mk (m + 1) (ωs j)) j)) =
              (fun j => (X.toCurrent.comp (Mk (m + 1))) (ωs j)) := rfl
          rw [h3] at h2
          exact h2 }
  have hE : ∀ (X : GeometricCurrentOn U (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)),
      E X ω = X (Mk (m + 1) ω) := fun _ _ => rfl
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · -- (i) agreement on forms supported in K
    intro X ω hω
    rw [hE]
    congr 1
    apply Subtype.ext; funext x
    change ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x = (ω : DifferentialForm (Euclid P) (m + 1)) x
    by_cases hx : x ∈ K
    · rw [hζ1 x (hKV₁ hx), one_smul]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hω h)), smul_zero]
  · -- (ii) weak convergence
    intro Xs X hX ω
    exact hX (Mk (m + 1) ω)
  · -- (iii) mass
    intro X
    apply sSup_le
    rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
    exact X.le_massOn ⟨(Mk (m + 1) ω).property.2, hadm (m + 1) _ hω⟩
  · -- (iv) support and boundary mass
    intro X hvan
    constructor
    · intro x hx
      by_contra hxK
      obtain ⟨ε, hε, hεK⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hxK
      apply hx.2
      refine ⟨ball x (ε / 2), ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self (half_pos hε)⟩
      · exact (isCompact_closedBall x (ε / 2)).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall
      · intro ω hω
        rw [hE]
        apply hvan
        rw [Set.disjoint_left]
        intro y hy hyK
        have hy' : y ∈ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) :=
          tsupport_smul_subset_right _ _ hy
        exact hεK (ball_subset_ball (half_le_self hε.le) (hω hy')) hyK
    · apply sSup_le
      rintro _ ⟨η, ⟨-, hη⟩, rfl⟩
      have hδ : X (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 := by
        apply hvan
        have hzero : ∀ y ∈ V₁, ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) y = 0 := by
          intro y hy
          change extDeriv (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) y -
            ζ y • extDeriv (η : DifferentialForm (Euclid P) m) y = 0
          have hev : (fun x => ζ x • (η : DifferentialForm (Euclid P) m) x) =ᶠ[𝓝 y]
              (η : DifferentialForm (Euclid P) m) := by
            filter_upwards [hV₁o.mem_nhds hy] with z hz
            rw [hζ1 z hz, one_smul]
          rw [hev.extDeriv_eq, hζ1 y hy, one_smul, sub_self]
        have hts : tsupport ((exteriorDerivativeTestOn U m (Mk m η) -
            Mk (m + 1) (exteriorDerivativeTestOn univ m η) : TestFormOn U (m + 1)) :
              DifferentialForm (Euclid P) (m + 1)) ⊆ V₁ᶜ := by
          apply closure_minimal _ hV₁o.isClosed_compl
          intro y hy hyV
          exact hy (hzero y hyV)
        exact Set.disjoint_of_subset_left hts (Set.disjoint_compl_left_iff_subset.2 hKV₁)
      have heq : (E X).boundary η = X.boundary (Mk m η) := by
        rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hE]
        have hsub := X.toCurrent.map_sub (exteriorDerivativeTestOn U m (Mk m η))
          (Mk (m + 1) (exteriorDerivativeTestOn univ m η))
        change X.toCurrent (exteriorDerivativeTestOn U m (Mk m η) -
          Mk (m + 1) (exteriorDerivativeTestOn univ m η)) = 0 at hδ
        rw [hsub, sub_eq_zero] at hδ
        exact hδ.symm
      change ENNReal.ofReal ((E X).boundary η) ≤ X.boundary.mass
      rw [heq]
      exact X.boundary.le_massOn ⟨(Mk m η).property.2, hadm m _ hη⟩
  · -- (v) integer multiplicity
    intro X R hR hRK
    refine ⟨{ carrier := R.carrier
              mult := R.mult
              orient := R.orient
              measurableSet_carrier := R.measurableSet_carrier
              carrier_subset := subset_univ _
              rectifiable := R.rectifiable
              measurable_mult := R.measurable_mult
              mult_pos := R.mult_pos
              locallyIntegrable_mult := fun K' _ _ => ?_
              aestronglyMeasurable_orient := R.aestronglyMeasurable_orient
              orients := R.orients }, ?_⟩
    · refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) (lintegral_mono_set ?_)
      exact fun x hx => ⟨hx.1, hRK hx.1⟩
    · intro ω
      rw [hE, hR (Mk (m + 1) ω)]
      unfold IMRep.action
      apply setIntegral_congr_fun R.measurableSet_carrier
      intro x hx
      change (R.mult x : ℝ) * R.orient x (ζ x • (ω : DifferentialForm (Euclid P) (m + 1)) x) =
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x)
      rw [hζ1 x (hKV₁ (hRK hx)), one_smul]
```

## Key steps

1. Smooth cutoff ζ: ℝ^P → [0, 1] with compact tsupport ζ ⊆ U and ζ = 1 on an open N ⊇ K (exists_open_between_and_isCompact_closure twice, then exists_contDiff_support_eq_eq_one_iff).
2. ω ↦ ζω maps 𝒟^k(ℝ^P) linearly into 𝒟^k(U), shrinks tsupport, and keeps |ω| ≤ 1 (the Euclidean coefficient norm is absolutely homogeneous).
3. ω ↦ ζω is sequentially continuous (sibling smul_continuity), so E X := X(ζ·) is a current in ℝ^P; weak convergence passes through E.
4. ζω = ω when tsupport ω ⊆ K, so E X agrees with X there; admissible forms map to admissible forms, so M(E X) ≤ M(X).
5. If X vanishes on forms supported off K: E X vanishes on small balls missing K, so spt E X ⊆ K; d(ζη) − ζdη vanishes on N (EventuallyEq.extDeriv_eq), so ∂(E X)(η) = ∂X(ζη) and M(∂E X) ≤ M(∂X).
6. An IMRep in U with carrier in K, regarded in ℝ^P, is an IMRep there (compact local integrability) and represents E X because ζ = 1 on the carrier.

## Reference use

### local-project

Queries:
- `python3 over RUN/dag.json: selected node, siblings convergence_tools/im_local/closure_compact (types byte-identical to the twin cbr_* nodes), twin node root.compactness_of_minimizing_currents-a1.closure_and_boundary_rectifiability-a1.closure_succ-a1 (type byte-identical), its decomposition-v2/audit-v2, status and candidate commits of the six reused declarations, and absence of the names dmcbrcs_norm_iteratedFDeriv_smul_le, dmcbrcs_testFormOnConverges_smul, dmcbrcs_cutoff_extension, dmcbrcs_localize_at_point`
- `rg -c dmcbrcs SNAPSHOT (no match, exit 1); grep -c dmcbrcs GMT/Ch07/Submission.lean (0); cmp SNAPSHOT/project/GMT/Ch07/Contract.lean GMT/Ch07/Contract.lean; cmp GMT/Ch07/Submission.lean GMT/Ch07/Contract.lean; git rev-parse HEAD (b4d606d), mathlib 25730c7c, simongmt 2b366308`
- `rg -n -F in SNAPSHOT/mathlib/Mathlib: exists_contDiff_support_eq_eq_one_iff, norm_iteratedFDeriv_smul_le, Filter.EventuallyEq.extDeriv_eq, exists_open_between_and_isCompact_closure, support_iteratedFDeriv_subset, tsupport_iteratedFDeriv_subset, HasCompactSupport.iteratedFDeriv, iteratedFDeriv_fun_zero, bounded_above_of_compact_support, eventually_all_finset, tendstoUniformlyOn_iff, setIntegral_congr_fun, lintegral_mono_set, tsupport_smul_subset_left/right, ContDiff.smul, extraction_of_frequently_atTop, frequently_lt_of_liminf_lt, limsup_comp, setIntegral_eq_integral_of_forall_compl_eq_zero, enorm_integral_le_lintegral_enorm, LipschitzWith.dist_left; sed of Mathlib/Analysis/Calculus/ContDiff/Bounds.lean lines 36-260 (Leibniz proofs and imports)`
- `lake env lean availability probe after `import GMT.Ch07.Submission`: #check norm_iteratedFDeriv_smul_le and ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear (unknown), exists_contDiff_support_eq_eq_one_iff, EventuallyEq.extDeriv_eq, ContinuousLinearMap.precompR/precompL, norm_precompR_le, fderivWithin_of_bilinear, norm_iteratedFDerivWithin_fderivWithin, Finset.sum_choose_succ_mul (available); Norm instance on three-level CLM spaces needs maxSynthPendingDepth 3 when written explicitly`
- `git log --all -G '^import ' -- GMT/Ch07/Submission.lean and -S 'set_option maxHeartbeats' (import additions and set_option reverted by the leaf gate: fa0865963, d5ba41d68, fe5f15468, 410955ec1); grep set_option in _recursive_lean/*.py (leaf_verification.check_source_delta forbidden-token rule)`
- `sed of SimonGMT Chapter06 Currents.lean (TestFormOnConverges, GeometricCurrentOn, WeaklyConvergesOn, boundary), Mass.lean (covectorEuclideanNorm, massAdmissibleOn, massOn, le_massOn, massOn_le_liminf), CurrentLocalEquality.lean (testFormOnInclusion, restrictDomain, zeroRegion, support), Forms.lean (exteriorDerivative = extDeriv); book/chapter-06.txt lines 2280-2345 (Simon 8.2, Remark 8.3(1), printed p. 176)`
- `lake env lean on /tmp/dmcbr-succ-dec/lean/{Types,Assembly,Localize,LocalizeHyp,LocalizeFinal,Challenges}.lean, /tmp/dmcbr-succ-dec/proto/{Leibniz3,Cont3,Cutoff}.lean and /tmp/dmcbr-succ-dec/final/FromJSON.lean; leaf_verification.check_source_delta on each appendix insertion; lean_contract.validate_lean_statement on all child types`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/project/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/Bounds.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Geometry/Manifold/PartitionOfUnity.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/Separation/Regular.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Order/Filter/Finite.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/Analysis/Normed/Group/Bounded.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/local-references/123e8435b4a2469b/mathlib/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/GMT/Ch07/Submission.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Currents.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Mass.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/CurrentLocalEquality.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.lake/packages/simongmt/Poincare/SimonGMT/Chapter06/Forms.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-dimension-reduction-results-a1-moving-blowups-a1-closure-and-bou-79c745d596/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-932152a15b/decomposition-audit-v2.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch07/.humanize/github-theorem-prover/runs/20261011T150044Z-ba604216b4/nodes/root-compactness-of-minimizing-currents-a1-closure-and-boundary-recti-f9e8023a0d/decomposition-v1.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-06.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/leaf_verification.py`
- `/runtime/flows/gmt-claude-b888e19cffb1/_recursive_lean/runtime.py`
- `/tmp/dmcbr-succ-dec/lean/Assembly.lean`
- `/tmp/dmcbr-succ-dec/lean/LocalizeHyp.lean`
- `/tmp/dmcbr-succ-dec/final/FromJSON.lean`

Pins match: HEAD b4d606d is the snapshot project commit, with Mathlib 25730c7c and SimonGMT 2b366308, and Submission.lean is byte-identical to the frozen contract. The snapshot has no dmcbrcs declaration and no closure or extension theorem; its Chapter 6 matches are definitions only. Every Mathlib name cited by the child proofs exists in the pinned sources. One cited name, norm_iteratedFDeriv_smul_le from Mathlib.Analysis.Calculus.ContDiff.Bounds, is outside the frozen import closure, so the Leibniz bound becomes the child smul_leibniz, transcribed from that file and verified. The six reused declarations are accepted, with byte-identical declarations in their candidate commits. All child types elaborate, and the hypothesis-only assembly proves the exact parent type with propext, Classical.choice and Quot.sound. Every new child's appendix compiles under default options and passes the leaf source-delta gate.
