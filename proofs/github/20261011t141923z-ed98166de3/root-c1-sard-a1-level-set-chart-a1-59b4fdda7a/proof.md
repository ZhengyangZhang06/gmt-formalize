# Parent-supplied natural-language proof

- Parent DAG node: `root.c1_sard-a1`
- Child DAG node: `root.c1_sard-a1.level_set_chart-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: parent proof of root.c1_sard-a1, PART II steps 7-10 (the inverse/implicit function theorem construction behind Simon's "the implicit function theorem implies that f⁻¹(y) \ C ... is a k-dimensional C¹ submanifold", p. 66-67), carried out in the parameter space for an arbitrary C¹ map G (in the parent G = f ∘ ψ). This lemma says that a level set of a C¹ map whose derivative is onto at x₀ has a C¹ Simon local representation near x₀ (Simon 4.1), inside any prescribed open V.

Notation. n := m + k, ℝᵖ = EuclideanSpace ℝ (Fin p), y₀ := G(x₀), A := fderiv ℝ G x₀ (surjective). ℝᵐ × ℝᵏ carries its product (sup) norm; it is a finite-dimensional normed space of dimension m + k.

1. (Kernel and complementary coordinate.) K := ker A ⊆ ℝⁿ. By rank-nullity, dim(range A) + dim K = n; range A = ℝᵐ by surjectivity, so dim K = n − m = k = dim ℝᵏ. Choose a linear isomorphism e : K → ℝᵏ (equal finite dimensions), let P_K : ℝⁿ → K be the orthogonal projection, and put π := e ∘ P_K : ℝⁿ → ℝᵏ (continuous linear). For v ∈ K, P_K v = v, hence π v = e v.
2. (The map Φ.) Φ : ℝⁿ → ℝᵐ × ℝᵏ, Φ(x) := (G(x), π(x − x₀)). Φ is C¹ on V (first component by hypothesis, second affine), Φ(x₀) = (y₀, 0), and for x ∈ V (V open) Φ has derivative DΦ(x) = (DG(x), π).
3. (DΦ(x₀) is invertible.) (A, π) is injective: if A v = A w and π v = π w, then v − w ∈ K and e(v − w) = π(v − w) = 0, so v = w. As dim ℝⁿ = m + k = dim(ℝᵐ × ℝᵏ), the injective linear map (A, π) is bijective; let Φ' : ℝⁿ ≃L ℝᵐ × ℝᵏ be the resulting continuous linear equivalence, so Φ has derivative Φ' at x₀.
4. (Inverse function theorem.) Φ is C¹ at x₀ with invertible derivative Φ'. By the C¹ inverse function theorem there is a local homeomorphism h (an open partial homeomorphism ℝⁿ ⇀ ℝᵐ × ℝᵏ) with h = Φ as functions, x₀ ∈ source(h), source and target open, h mapping source(h) bijectively onto target(h) with continuous inverse h⁻¹ (h⁻¹(h x) = x on the source, h(h⁻¹ ω) = ω on the target, h(source) ⊆ target, h⁻¹(target) ⊆ source).
5. (Restrict to invertible derivative.) V_inv := {x ∈ V : DΦ(x) is invertible} is open: x ↦ DΦ(x) is continuous on the open set V (Φ is C¹ on V) and the invertible continuous linear maps ℝⁿ → ℝᵐ × ℝᵏ form an open set. x₀ ∈ V_inv by step 3. Let h' be h restricted to V_inv: source(h') = source(h) ∩ V_inv ⊆ V, h' = Φ and h'⁻¹ = h⁻¹ as functions, and x₀ ∈ source(h').
6. (Regularity of the inverse.) Let ω ∈ target(h') and x := h'⁻¹(ω) ∈ source(h') ⊆ V_inv. Then DΦ(x) is (the underlying map of) a continuous linear equivalence E_ω and Φ is C¹ at x (x ∈ V). By the inverse-function regularity lemmas for local homeomorphisms, h'⁻¹ has derivative E_ω⁻¹ at ω and is C¹ at ω.
7. (Box and chart.) target(h') is open and contains Φ(x₀) = (y₀, 0). Choose ε > 0 with B((y₀,0), ε) ⊆ target(h'); in the product norm B((y₀,0), ε) = B(y₀, ε) × B(0, ε) =: O. Define D := B(0, ε) ⊆ ℝᵏ (open ball), V₁ := source(h') ∩ Φ⁻¹(O) (open, since source(h') is open and Φ = h' is continuous on it), j(z) := (y₀, z), and l(z) := h'⁻¹(y₀, z) for z ∈ ℝᵏ. For z ∈ D, j(z) ∈ O ⊆ target(h').
8. (x₀ ∈ V₁ ⊆ V.) x₀ ∈ source(h') and Φ(x₀) = (y₀, 0) ∈ O; V₁ ⊆ source(h') ⊆ V.
9. (Openness.) D and V₁ are open (step 7).
10. (C¹ on D.) For z ∈ D, l = h'⁻¹ ∘ j, j is affine (C^∞) and h'⁻¹ is C¹ at j(z) ∈ target(h') (step 6); so l is C¹ at z. Hence l is C¹ on D.
11. (Injective on D.) If z, z' ∈ D and l(z) = l(z'), applying h' and h'(h'⁻¹ ω) = ω gives (y₀, z) = (y₀, z'), so z = z'.
12. (Image.) l(D) = V₁ ∩ G⁻¹{y₀}. (⊆) For z ∈ D, ω := (y₀, z) ∈ target(h'), so x := l(z) = h'⁻¹(ω) ∈ source(h') and Φ(x) = h'(h'⁻¹ ω) = ω ∈ O; thus x ∈ V₁, and G(x) = (first component of Φ(x)) = y₀. (⊇) If x ∈ V₁ and G(x) = y₀, then Φ(x) = (y₀, π(x − x₀)) ∈ O, so z := π(x − x₀) ∈ B(0, ε) = D, and l(z) = h'⁻¹(Φ(x)) = h'⁻¹(h'(x)) = x since x ∈ source(h').
13. (Properness relative to (D, V₁).) Let Q ⊆ V₁ be compact. Φ is continuous on V₁ ⊆ V, so Φ(Q) is compact. Claim: D ∩ l⁻¹(Q) = j⁻¹(Φ(Q)) = {z : (y₀, z) ∈ Φ(Q)}. (⊆) If z ∈ D and l(z) ∈ Q then (y₀, z) = h'(h'⁻¹(y₀, z)) = Φ(l(z)) ∈ Φ(Q). (⊇) If (y₀, z) = Φ(q) with q ∈ Q ⊆ V₁, then Φ(q) ∈ O gives z ∈ B(0, ε) = D, and l(z) = h'⁻¹(Φ(q)) = h'⁻¹(h'(q)) = q ∈ Q because q ∈ source(h'). Now j⁻¹(Φ(Q)) is closed (Φ(Q) is compact hence closed, j continuous) and contained in the compact set pr₂(Φ(Q)); a closed subset of a compact set is compact. Hence D ∩ l⁻¹(Q) is compact.
14. (Injective derivative.) For z ∈ D, by the chain rule Dl(z) = D(h'⁻¹)(j(z)) ∘ Dj(z) = E⁻¹ ∘ (h ↦ (0, h)), with E the equivalence from step 6 at ω = j(z). Both factors are injective, so Dl(z) is injective.
15. Steps 8-14 give x₀ ∈ V₁, V₁ ⊆ V and IsSimonLocalRepresentation 1 (G⁻¹{G x₀}) D V₁ l: IsOpen D, IsOpen V₁, ContDiffOn ℝ 1 l D, InjOn l D, l '' D = V₁ ∩ G⁻¹{G x₀}, IsProperOnInto l D V₁, and Dl(z) injective for z ∈ D. ∎
(Edge cases: k = 0 gives ℝᵏ = {0}, K = {0}, D = {0}; m = 0 gives A trivially onto, K = ℝⁿ. No step assumes m > 0 or k > 0.)

Formalization reference (machine-checked by the decomposer: extra import `Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff`; inside `namespace GMT.Ch02` with the contract's opens; axioms propext, Classical.choice, Quot.sound only). Library: LinearMap.finrank_range_add_finrank_ker, LinearEquiv.ofFinrankEq, Submodule.orthogonalProjectionOnto, LinearMap.injective_iff_surjective_of_finrank_eq_finrank, Module.finrank_prod, ContDiffAt.toOpenPartialHomeomorph / mem_toOpenPartialHomeomorph_source, ContinuousLinearEquiv.isOpen, OpenPartialHomeomorph.restrOpen (coercions are rfl), OpenPartialHomeomorph.hasFDerivAt_symm, OpenPartialHomeomorph.contDiffAt_symm, ball_prod_same, IsCompact.of_isClosed_subset.

```lean
theorem c1_sard_submersion_level_set_chart : ∀ (m k : ℕ) (V : Set (Rn (m + k))) (G : Rn (m + k) → Rn m) (x₀ : Rn (m + k)), IsOpen V → x₀ ∈ V → ContDiffOn ℝ 1 G V → Function.Surjective (fderiv ℝ G x₀) → ∃ (D : Set (Rn k)) (V₁ : Set (Rn (m + k))) (l : Rn k → Rn (m + k)), x₀ ∈ V₁ ∧ V₁ ⊆ V ∧ Chapter02.IsSimonLocalRepresentation 1 (G ⁻¹' {G x₀}) D V₁ l := by
  intro m k V G x₀ hV hx₀ hG hsurj
  -- kernel of A and a complementary map π
  set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G x₀ with hA
  set K : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK
  have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hKdim : Module.finrank ℝ K = Module.finrank ℝ (Rn k) := by
    have h := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
    rw [hrange, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin, ← hK] at h
    rw [finrank_euclideanSpace_fin]
    omega
  let e : K ≃ₗ[ℝ] Rn k := LinearEquiv.ofFinrankEq K (Rn k) hKdim
  let π : Rn (m + k) →L[ℝ] Rn k :=
    (e.toContinuousLinearEquiv : K →L[ℝ] Rn k) ∘L K.orthogonalProjectionOnto
  have hπK : ∀ v : K, π v = e v := by
    intro v
    simp [π]
  -- the map Φ
  let Φ : Rn (m + k) → Rn m × Rn k := fun x => (G x, π (x - x₀))
  have hπaff : ContDiff ℝ 1 (fun x : Rn (m + k) => π (x - x₀)) :=
    π.contDiff.comp (contDiff_id.sub contDiff_const)
  have hΦC : ContDiffOn ℝ 1 Φ V := hG.prodMk hπaff.contDiffOn
  have hΦCA : ∀ x ∈ V, ContDiffAt ℝ 1 Φ x := fun x hx => hΦC.contDiffAt (hV.mem_nhds hx)
  have hπd : ∀ x, HasFDerivAt (fun x : Rn (m + k) => π (x - x₀)) π x := by
    intro x
    have h1 : HasFDerivAt (fun x : Rn (m + k) => x - x₀) (ContinuousLinearMap.id ℝ (Rn (m + k))) x :=
      (hasFDerivAt_id x).sub_const x₀
    have h2 := (π.hasFDerivAt (x := x - x₀)).comp x h1
    rw [ContinuousLinearMap.comp_id] at h2
    exact h2
  have hΦd : ∀ x ∈ V, HasFDerivAt Φ ((fderiv ℝ G x).prod π) x := by
    intro x hx
    have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
      ((hG.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hx)).hasFDerivAt
    exact hGx.prodMk (hπd x)
  -- invertibility of DΦ(x₀)
  have hinj : Function.Injective (A.prod π) := by
    intro v w hvw
    have h1 : A v = A w := congrArg Prod.fst hvw
    have h2 : π v = π w := congrArg Prod.snd hvw
    have hmem : v - w ∈ K := by
      show A (v - w) = 0
      rw [map_sub, h1, sub_self]
    have h3 : e ⟨v - w, hmem⟩ = e 0 := by
      rw [← hπK, map_zero]
      show π (v - w) = 0
      rw [map_sub, h2, sub_self]
    have := congrArg Subtype.val (e.injective h3)
    simpa [sub_eq_zero] using this
  have hdim : Module.finrank ℝ (Rn (m + k)) = Module.finrank ℝ (Rn m × Rn k) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      finrank_euclideanSpace_fin]
  have hsurjΦ : Function.Surjective (A.prod π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj
  let Φ' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
    (LinearEquiv.ofBijective ((A.prod π : Rn (m + k) →L[ℝ] Rn m × Rn k) :
      Rn (m + k) →ₗ[ℝ] Rn m × Rn k) ⟨hinj, hsurjΦ⟩).toContinuousLinearEquiv
  have hΦ'd : HasFDerivAt Φ (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) x₀ := by
    have : (Φ' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    rw [this]; exact hΦd x₀ hx₀
  -- local homeomorphism (inverse function theorem)
  let h := (hΦCA x₀ hx₀).toOpenPartialHomeomorph Φ hΦ'd one_ne_zero
  have hh : (h : Rn (m + k) → Rn m × Rn k) = Φ := rfl
  -- the open set where DΦ is invertible
  set Vinv : Set (Rn (m + k)) := V ∩ (fderiv ℝ Φ) ⁻¹'
    (range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k)) with hVinv
  have hVinvo : IsOpen Vinv :=
    (hΦC.continuousOn_fderiv_of_isOpen hV le_rfl).isOpen_inter_preimage hV
      ContinuousLinearEquiv.isOpen
  have hx₀inv : x₀ ∈ Vinv := ⟨hx₀, Φ', (hΦ'd.fderiv).symm⟩
  let h' := h.restrOpen Vinv hVinvo
  have hh' : (h' : Rn (m + k) → Rn m × Rn k) = Φ := rfl
  have hx₀src : x₀ ∈ h'.source :=
    ⟨(hΦCA x₀ hx₀).mem_toOpenPartialHomeomorph_source hΦ'd one_ne_zero, hx₀inv⟩
  have hsrcV : h'.source ⊆ V := fun x hx => hx.2.1
  have hΦx₀ : Φ x₀ = (G x₀, 0) := by simp [Φ]
  have htgt : (G x₀, (0 : Rn k)) ∈ h'.target := by
    rw [← hΦx₀, ← hh']; exact h'.map_source hx₀src
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp h'.open_target _ htgt
  set O : Set (Rn m × Rn k) := ball (G x₀) ε ×ˢ ball (0 : Rn k) ε with hO
  have hOt : O ⊆ h'.target := by rw [hO, ball_prod_same]; exact hball
  have hjO : ∀ z ∈ ball (0 : Rn k) ε, ((G x₀, z) : Rn m × Rn k) ∈ O :=
    fun z hz => ⟨mem_ball_self hε, hz⟩
  have hsymm : ∀ ω ∈ h'.target, ∃ eqv : Rn (m + k) ≃L[ℝ] Rn m × Rn k,
      HasFDerivAt h'.symm (eqv.symm : Rn m × Rn k →L[ℝ] Rn (m + k)) ω ∧
        ContDiffAt ℝ 1 h'.symm ω := by
    intro ω hω
    have hxs : h'.symm ω ∈ h'.source := h'.map_target hω
    obtain ⟨eqv, heqv⟩ := hxs.2.2
    have hxV : h'.symm ω ∈ V := hxs.2.1
    have hd : HasFDerivAt h' (eqv : Rn (m + k) →L[ℝ] Rn m × Rn k) (h'.symm ω) := by
      rw [heqv]; exact ((hΦCA _ hxV).differentiableAt one_ne_zero).hasFDerivAt
    exact ⟨eqv, h'.hasFDerivAt_symm hω hd, h'.contDiffAt_symm hω hd (hΦCA _ hxV)⟩
  refine ⟨ball (0 : Rn k) ε, h'.source ∩ Φ ⁻¹' O, fun z => h'.symm (G x₀, z),
    ⟨hx₀src, ?_⟩, fun x hx => hsrcV hx.1, ?_⟩
  · rw [Set.mem_preimage, hΦx₀]; exact ⟨mem_ball_self hε, mem_ball_self hε⟩
  refine ⟨isOpen_ball, h'.isOpen_inter_preimage (isOpen_ball.prod isOpen_ball), ?_, ?_, ?_, ?_, ?_⟩
  · -- C¹
    intro z hz
    obtain ⟨eqv, -, hcd⟩ := hsymm _ (hOt (hjO z hz))
    exact (hcd.comp z (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  · -- injective
    intro z hz z' hz' hzz
    have h1 := h'.right_inv (hOt (hjO z hz))
    have h2 := h'.right_inv (hOt (hjO z' hz'))
    have := congrArg h' hzz
    simp only at this
    rw [h1, h2] at this
    exact (Prod.mk.inj this).2
  · -- image
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hω := hOt (hjO z hz)
      refine ⟨⟨h'.map_target hω, ?_⟩, ?_⟩
      · show Φ (h'.symm (G x₀, z)) ∈ O
        rw [← hh', h'.right_inv hω]; exact hjO z hz
      · show G (h'.symm (G x₀, z)) = G x₀
        exact congrArg Prod.fst (h'.right_inv hω)
    · rintro ⟨⟨hxs, hxO⟩, hxG⟩
      have hxG' : G x = G x₀ := hxG
      refine ⟨π (x - x₀), hxO.2, ?_⟩
      show h'.symm (G x₀, π (x - x₀)) = x
      have : ((G x₀, π (x - x₀)) : Rn m × Rn k) = h' x := by rw [hh']; simp [Φ, hxG']
      rw [this, h'.left_inv hxs]
  · -- proper
    intro Q hQ hQV₁
    have hΦQ : IsCompact (Φ '' Q) :=
      hQ.image_of_continuousOn (hΦC.continuousOn.mono (fun x hx => hsrcV (hQV₁ hx).1))
    have heq : ball (0 : Rn k) ε ∩ (fun z => h'.symm (G x₀, z)) ⁻¹' Q =
        (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) ⁻¹' (Φ '' Q) := by
      ext z
      constructor
      · rintro ⟨hz, hzQ⟩
        refine ⟨_, hzQ, ?_⟩
        rw [← hh', h'.right_inv (hOt (hjO z hz))]
      · rintro ⟨q, hq, hqz⟩
        have hqz' : Φ q = (G x₀, z) := hqz
        have hqO : Φ q ∈ O := (hQV₁ hq).2
        rw [hqz'] at hqO
        refine ⟨hqO.2, ?_⟩
        show h'.symm (G x₀, z) ∈ Q
        rw [← hqz', ← hh', h'.left_inv (hQV₁ hq).1]; exact hq
    rw [heq]
    refine (hΦQ.image continuous_snd).of_isClosed_subset
      (hΦQ.isClosed.preimage (continuous_const.prodMk continuous_id)) ?_
    intro z hz
    exact ⟨_, hz, rfl⟩
  · -- injective derivative
    intro z hz
    obtain ⟨eqv, hd, -⟩ := hsymm _ (hOt (hjO z hz))
    have hj : HasFDerivAt (fun z : Rn k => ((G x₀, z) : Rn m × Rn k))
        ((0 : Rn k →L[ℝ] Rn m).prod (ContinuousLinearMap.id ℝ (Rn k))) z :=
      (hasFDerivAt_const (G x₀) z).prodMk (hasFDerivAt_id z)
    have hcomp := hd.comp z hj
    rw [show (fun z => h'.symm (G x₀, z)) =
      h'.symm ∘ (fun z : Rn k => ((G x₀, z) : Rn m × Rn k)) from rfl, hcomp.fderiv,
      ContinuousLinearMap.coe_comp]
    refine eqv.symm.injective.comp ?_
    intro a b hab
    have := congrArg Prod.snd hab
    simpa using this
```

## Key steps

1. K = ker DG(x₀) has dimension k; set π := e ∘ P_K with e : K ≅ ℝᵏ.
2. Φ(x) = (G(x), π(x − x₀)) is C¹ on V and DΦ(x₀) = (DG(x₀), π) is injective, hence an isomorphism.
3. Inverse function theorem: a local homeomorphism h = Φ near x₀, restricted to the open set where DΦ is invertible, so h⁻¹ is C¹ with invertible derivative on its target.
4. Choose a box B(G x₀, ε) × B(0, ε) in the target; D := B(0, ε), V₁ := source ∩ Φ⁻¹(box), l(z) := h⁻¹(G x₀, z).
5. Check the clauses: l is C¹ and injective, l(D) = V₁ ∩ G⁻¹{G x₀}, properness (D ∩ l⁻¹Q is a closed slice of the compact Φ(Q)), and Dl(z) = (DΦ)⁻¹ ∘ (0, ·) is injective.

## Reference use

### local-project

Queries:
- `rg -n "^def C1Sard|^def CoareaFormula|^def coareaJacobian|^def tangentSpace|^def tangentProjection" project/GMT/Ch02/Contract.lean`
- `rg -n "C1Sard|6.4" project/GMT/Ch02/README.md`
- `rg -n "theorem toOpenPartialHomeomorph|def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm" mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean; rg -n "theorem OpenPartialHomeomorph.hasFDerivAt_symm" mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "protected def restrOpen|theorem coe_restrOpen" mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `rg -n "theorem _root_.Submodule.adjoint_subtypeL|theorem adjoint_comp|theorem _root_.ContinuousLinearMap.adjoint_toLinearMap" mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean; rg -n "^def starProjection|theorem orthogonalProjectionOnto_mem_subspace_eq_self" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -n "theorem ContinuousOn.clm_comp" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean; rg -n "theorem ContDiffOn.continuousOn_fderiv_of_isOpen" mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean; rg -n "theorem continuousOn_iff_isClosed|theorem ContinuousOn.isOpen_inter_preimage" mathlib/Mathlib/Topology/ContinuousOn.lean`
- `rg -n "theorem lintegral_eq_zero_iff'|theorem lintegral_indicator_one" mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/*.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|theorem injective_iff_surjective_of_finrank_eq_finrank" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean; rg -n "lemma ball_prod_same" mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean; rg -n "theorem fderiv_comp " mathlib/Mathlib/Analysis/Calculus/FDeriv/Comp.lean; rg -n "theorem finrank_euclideanSpace_fin" mathlib/Mathlib/Analysis/InnerProductSpace/PiL2.lean`
- `rg -n "def implicitToOpenPartialHomeomorph|def implicitFunction|theorem map_implicitFunction_eq" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -il "sard" mathlib/Mathlib; rg -n "Submission\." project --glob '*.lean'; rg -il "sard|regular value|implicit" lake-packages-25730c7c/simongmt/Poincare/SimonGMT/`
- `full reads of simongmt Poincare/SimonGMT/Chapter02/{Submanifold,SubmanifoldTopology,SubmanifoldCalculus,CoareaLinearAlgebra,CoareaProjection}.lean; git rev-parse HEAD of the simongmt and mathlib package checkouts`
- `python3 -I gen_checks.py / gen_solutions.py (replay verifier gmt-compare.py contract_scope + child_modules for the six lean_statements); lean NodeChallenge/NodeSolution modules against scratch oleans of GMT.Ch02.Submission`
- `lean Assembly.lean, GCheck.lean, Combined.lean with #print axioms (six child proofs + parent assembly, uncle types as stand-ins)`
- `read dag.json lean_name list for collisions with the six proposed names`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/project/GMT/Ch02/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/FDeriv/OfCompLeft.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/OpenPartialHomeomorph/IsImage.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Adjoint.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/ContDiff/Defs.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/ContinuousOn.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Topology/MetricSpace/Pseudo/Constructions.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/local-references/ff09f3909baeeae7/mathlib/Mathlib/MeasureTheory/Function/Jacobian.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Submanifold.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldTopology.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaLinearAlgebra.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/SubmanifoldCalculus.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/CoareaProjection.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch02/.humanize/github-theorem-prover/runs/20261011T141923Z-ed98166de3/nodes/root-c1-sard-a1/parent-child-handoff.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/tmp/c1sard-decomp-Z3BOJI/Combined.lean`

Frozen contract: Contract.lean:349-374 fixes CoareaFormula and C1Sard. Conjunct (2) uses μHE[k] and volume on Rn m, and conjunct (3b) uses IsSimonSubmanifold (E := Rn k) 1. coareaJacobian (line 123) is defined with ContinuousLinearMap.adjoint and the det of L ∘L L†. README row 16 and line 103 confirm the relatively-closed reading and the rank conjunct.

Snapshot Mathlib supplies everything the six children use:
- the C¹ inverse function theorem, ContDiffAt.toOpenPartialHomeomorph (InverseFunctionTheorem/ContDiff.lean:31);
- OpenPartialHomeomorph.contDiffAt_symm (ContDiff/Operations.lean:881) and OpenPartialHomeomorph.hasFDerivAt_symm (FDeriv/OfCompLeft.lean:214);
- ContinuousLinearEquiv.isOpen (BoundedLinearMaps.lean:543) and restrOpen (OpenPartialHomeomorph/IsImage.lean:216; its coercions are rfl);
- Submodule.adjoint_subtypeL (Adjoint.lean:177), adjoint_comp (Adjoint.lean:136) and starProjection (Projection/Basic.lean:131);
- ContinuousOn.clm_comp (BoundedLinearMaps.lean:453), ContDiffOn.continuousOn_fderiv_of_isOpen (ContDiff/Defs.lean:916) and continuousOn_iff_isClosed (Topology/ContinuousOn.lean:149);
- lintegral_eq_zero_iff' and lintegral_indicator_one (Lebesgue/Basic.lean:322, 572);
- rank-nullity (FiniteDimensional/Lemmas.lean:173, 204), ball_prod_same, fderiv_comp and finrank_euclideanSpace_fin.

No existing result proves C1Sard or any child. Implicit.lean offers an alternative implicit-function route. The 'Sard' matches (MeasureTheory/Function/Jacobian.lean) are the equal-dimension critical-value lemma, not the coarea-based C¹ Sard theorem. The SimonGMT 'implicit' matches are unrelated comments.

Pinned SimonGMT is at rev 2b3663083f3f, which matches the lakefile, and its oleans are built. It provides:
- coareaLinearJacobian_eq_sqrt_det and coareaLinearJacobian_eq_zero_iff (CoareaLinearAlgebra.lean:35-48);
- IsSimonLocalRepresentation.exists_open_image_eq_inter (SubmanifoldTopology.lean:100, Simon 4.2).
All of these depend only on propext, Classical.choice and Quot.sound.

The project snapshot has no Submission.* declarations, and dag.json has no c1_sard_* children, so the six names are free.

Verifier replay results:
- all six statements elaborate after import GMT.Ch02.Submission in the contract scope;
- the assembly proves C1Sard from the children and the two uncle types;
- complete Lean proofs of all six children compile, and the verifier-generated NodeSolution modules check against them using standard axioms only.
