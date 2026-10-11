# Parent-supplied natural-language proof

- Parent DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1`
- Child DAG node: `root.coarea_and_slices-a1.c1_level_slices_rectifiable-a1.regular_slices-a1`
- Review gate: accepted as part of the parent's decomposition audit

## Proof

Source: the parent's supplied proof, step 2 (regular part). This is the implicit-function-theorem half of Simon's C¹ Sard-type Theorem 6.4 (Ch. 2 §6, chapter-02.txt lines 1476-1497): "since J_f(x) ≠ 0 precisely when df_x has rank m, the implicit function theorem implies that either f⁻¹(y) \ C is empty or else it is a k-dimensional C¹ submanifold". Here it is specialized to the image under ψ, with every detail written out. Standard background: the inverse function theorem, and the regular level set theorem (Lee, Introduction to Smooth Manifolds, 2nd ed., Cor. 5.14).

Notation: n := m + k; ℝ^d = Rn d = EuclideanSpace ℝ (Fin d); DG(u) = fderiv ℝ G u; S := {u ∈ ℝⁿ : DG(u) is surjective}. Fix y ∈ ℝᵐ. We prove that ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable. The argument is uniform in m and k and needs neither k > 0 nor m > 0. For m = 0, every DG(u) is surjective. For k = 0, the parameter space ℝ⁰ is a single point.

1. (C¹ images of open subsets of ℝᵏ.) Claim: if W ⊆ ℝᵏ is open and h : ℝᵏ → ℝᴺ is C¹ on W, then h(W) is countably k-rectifiable.
   Proof. W is an open subset of ℝᵏ, so it is locally compact and σ-compact. Write W = ⋃_{j∈ℕ} C_j with each C_j ⊆ W compact. Every x ∈ W has a neighbourhood on which h is Lipschitz: h is C¹ at x because W is open, and the mean value inequality applies. So h is locally Lipschitz on the compact set C_j, and therefore Lipschitz on C_j with some constant L_j. By the Lipschitz extension theorem for maps into a finite-dimensional normed space (Mathlib LipschitzOnWith.extend_finite_dimension), there is a Lipschitz map g_j : ℝᵏ → ℝᴺ with g_j = h on C_j. Then h(W) ⊆ ⋃_j g_j(ℝᵏ), a countable union of ranges of Lipschitz maps ℝᵏ → ℝᴺ. By Definition 1.1 (countablyRectifiable_range, countablyRectifiable_iUnion, CountablyRectifiable.mono), h(W) is countably k-rectifiable. (This is SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open.)

2. (Linear algebra at a regular point.) Let u₀ ∈ D ∩ S, and let A := DG(u₀) : ℝⁿ → ℝᵐ, a surjective linear map. Put K₀ := ker A. By rank–nullity, m + dim K₀ = dim ℝⁿ = m + k, so dim K₀ = k.
   Fix a linear isomorphism ι : K₀ → ℝᵏ, and let P₀ : ℝⁿ → K₀ be the orthogonal projection onto K₀, so P₀v = v for v ∈ K₀. Set π := ι ∘ P₀ : ℝⁿ → ℝᵏ (continuous and linear) and L := (A, π) : ℝⁿ → ℝᵐ × ℝᵏ.
   L is injective: if Av = 0 and πv = 0, then v ∈ K₀, so P₀v = v and ι(v) = 0, hence v = 0. Since dim(ℝᵐ × ℝᵏ) = m + k = dim ℝⁿ, L is a linear isomorphism. In finite dimensions it is automatically a continuous linear equivalence.

3. (Chart map and inverse function theorem.) Let Φ : ℝⁿ → ℝᵐ × ℝᵏ, Φ(u) := (G(u), π(u)). Φ is C¹ on ℝⁿ with DΦ(u) = (DG(u), π) for every u. In particular DΦ(u₀) = L is invertible.
   Let V := {u ∈ ℝⁿ : DΦ(u) is a linear isomorphism ℝⁿ → ℝᵐ × ℝᵏ}. V is open: u ↦ DΦ(u) is continuous because Φ is C¹, and the invertible continuous linear maps between the Banach spaces ℝⁿ and ℝᵐ × ℝᵏ form an open set. Also u₀ ∈ V.
   Φ is C¹ with invertible derivative at u₀, so it is strictly differentiable there. The inverse function theorem gives open sets U₀ ∋ u₀ and Ω₀ ⊆ ℝᵐ × ℝᵏ such that Φ maps U₀ homeomorphically onto Ω₀. Write Θ : Ω₀ → U₀ for the inverse. Then Θ(Φ(u)) = u for u ∈ U₀, and Φ(Θ(p)) = p with Θ(p) ∈ U₀ for p ∈ Ω₀. Extend Θ arbitrarily to a map ℝᵐ × ℝᵏ → ℝⁿ. Only its values on Ω₀ are ever used; Mathlib's OpenPartialHomeomorph.symm is such a total extension.
   Moreover, Θ is C¹ at every p ∈ Ω₀ with Θ(p) ∈ V. Indeed, Φ is C¹ at Θ(p) with invertible derivative DΦ(Θ(p)). The inverse of a local homeomorphism that is C¹ with invertible derivative at the preimage point is C¹ at the image point (Mathlib OpenPartialHomeomorph.contDiffAt_symm).
   Set O := U₀ ∩ D ∩ V. Then O is open and u₀ ∈ O.

4. (The slice in the chart is a C¹ image.) Let W := {z ∈ ℝᵏ : (y, z) ∈ Ω₀ and Θ(y, z) ∈ D ∩ V}. The set Ω₀ ∩ Θ⁻¹(D ∩ V) is open, since Θ is continuous on the open set Ω₀ and D ∩ V is open. W is its preimage under the continuous map z ↦ (y, z), so W is open.
   Define h : ℝᵏ → ℝᴺ by h(z) := ψ(Θ(y, z)), using the total extension of Θ from step 3. Only z ∈ W matters, and there (y, z) ∈ Ω₀. Let z ∈ W. The map z ↦ (y, z) is C^∞. Θ is C¹ at (y, z) by step 3, since Θ(y, z) ∈ V. ψ is C¹ at Θ(y, z), because Θ(y, z) ∈ D, D is open and ψ is C¹ on D. By the chain rule, h is C¹ at z. Hence h is C¹ on W, and by step 1, h(W) is countably k-rectifiable.

5. (The chart's piece of the slice lies in h(W).) Let u ∈ O with G(u) = y. Then u ∈ U₀, so Φ(u) = (y, π(u)) ∈ Ω₀ and Θ(y, π(u)) = Θ(Φ(u)) = u ∈ D ∩ V. Thus z := π(u) ∈ W and h(z) = ψ(u). Hence ψ(O ∩ G⁻¹{y}) ⊆ h(W), and ψ(O ∩ G⁻¹{y}) is countably k-rectifiable (CountablyRectifiable.mono).

6. (Countably many charts, by Lindelöf.) By steps 2–5, every u₀ ∈ D ∩ S has an open set O_{u₀} ∋ u₀ with ψ(O_{u₀} ∩ G⁻¹{y}) countably k-rectifiable. Since ℝⁿ is second countable, there is a countable T ⊆ D ∩ S with ⋃_{u∈T} O_u = ⋃_{u∈D∩S} O_u (TopologicalSpace.isOpen_iUnion_countable). This uses only the second countability of ℝⁿ and does not use the openness of D ∩ S. (S is in fact open, since DG is continuous and surjective linear maps form an open set, but this is not needed.) Hence D ∩ S ⊆ ⋃_{u∈T} O_u, and so ψ(D ∩ S ∩ G⁻¹{y}) ⊆ ⋃_{u∈T} ψ(O_u ∩ G⁻¹{y}).

7. (Conclusion.) A countable union of countably k-rectifiable sets is countably k-rectifiable (countablyRectifiable_sUnion / countablyRectifiable_iUnion; for T = ∅ the union is the empty set, which is Hᵏ-null). A subset of a countably k-rectifiable set is countably k-rectifiable (CountablyRectifiable.mono). By steps 5–6, ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable. Since y was arbitrary, the statement holds for every y ∈ ℝᵐ. ∎

Implementation notes (checked on the pinned toolchain lean 4.35.0-rc3 / Mathlib 25730c7c against `import GMT.Ch03.Submission` in the comparator's replayed Contract scope):
- `ContDiffAt.toOpenPartialHomeomorph` is not imported by Submission. Use `HasStrictFDerivAt.toOpenPartialHomeomorph Φ (ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero)`.
- Generalized field notation on a `ContDiffAt ℝ 1 …` hypothesis can fail, because the literal `1` makes the type unfold. Call those lemmas by their full names.
- `Poincare.SimonGMT.Chapter03.countablyRectifiable_image_contDiffOn_open` is in `Poincare.SimonGMT.Chapter03.SubmanifoldCover`, which Submission does not import. The proof below therefore inlines step 1, so no new import is needed.

Appendix: a complete Lean proof of exactly this statement. It type-checks with no warnings and depends only on [propext, Classical.choice, Quot.sound]. Place it in GMT/Ch03/Submission.lean inside `namespace GMT.Ch03`, after the frozen definitions; this is the same scope the comparator replays.

```lean
theorem Submission.c1_regular_level_slice_image_countablyRectifiable : ∀ (m k N : ℕ) (D : Set (Rn (m + k))) (ψ : Rn (m + k) → Rn N) (G : Rn (m + k) → Rn m) (y : Rn m), IsOpen D → ContDiffOn ℝ 1 ψ D → ContDiff ℝ 1 G → CountablyRectifiable k (ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y})) := by
  intro m k N D ψ G y hD hψ hG
  -- C¹ images of open subsets of ℝᵏ are countably k-rectifiable
  -- (inline copy of SimonGMT `countablyRectifiable_image_contDiffOn_open`).
  have himage : ∀ (W : Set (Rn k)) (h : Rn k → Rn N), IsOpen W → ContDiffOn ℝ 1 h W →
      CountablyRectifiable k (h '' W) := by
    intro W h hW hh
    let _ : LocallyCompactSpace W := hW.locallyCompactSpace
    obtain ⟨Kc, hKc, hKcover⟩ := SigmaCompactSpace.exists_compact_covering (X := W)
    let C : ℕ → Set (Rn k) := fun j => ((↑) : W → Rn k) '' Kc j
    have hCc : ∀ j, IsCompact (C j) := fun j => (hKc j).image continuous_subtype_val
    have hCW : ∀ j, C j ⊆ W := by
      rintro j _ ⟨x, -, rfl⟩
      exact x.2
    have hLip : ∀ j, ∃ L : ℝ≥0, LipschitzOnWith L h (C j) := by
      intro j
      apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hCc j)
      intro x hx
      obtain ⟨L, t, ht, hht⟩ := (hh.contDiffAt (hW.mem_nhds (hCW j hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hht⟩
    choose L hL using hLip
    choose g hgL hgeq using fun j => (hL j).extend_finite_dimension
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun j => range (g j))
      (fun j => Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hgL j))).mono ?_
    rintro _ ⟨x, hxW, rfl⟩
    have hx : (⟨x, hxW⟩ : W) ∈ ⋃ j, Kc j := by rw [hKcover]; trivial
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨j, x, (hgeq j ⟨⟨x, hxW⟩, hj, rfl⟩).symm⟩
  -- Local charts at regular points (implicit function theorem via Φ = (G, π)).
  have hloc : ∀ u₀ : ↥(D ∩ {u | Function.Surjective (fderiv ℝ G u)}),
      ∃ O : Set (Rn (m + k)), IsOpen O ∧ (u₀ : Rn (m + k)) ∈ O ∧
        CountablyRectifiable k (ψ '' (O ∩ G ⁻¹' {y})) := by
    rintro ⟨u₀, hu₀D, hu₀S⟩
    set A : Rn (m + k) →L[ℝ] Rn m := fderiv ℝ G u₀ with hA
    have hrange : LinearMap.range (A : Rn (m + k) →ₗ[ℝ] Rn m) = ⊤ := LinearMap.range_eq_top.2 hu₀S
    set K₀ : Submodule ℝ (Rn (m + k)) := LinearMap.ker (A : Rn (m + k) →ₗ[ℝ] Rn m) with hK₀
    have hker : finrank ℝ K₀ = k := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (A : Rn (m + k) →ₗ[ℝ] Rn m)
      rw [hrange, finrank_top] at h1
      simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
      change m + finrank ℝ K₀ = m + k at h1
      omega
    obtain ⟨ι⟩ : Nonempty (K₀ ≃L[ℝ] Rn k) :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [hker])
    let π : Rn (m + k) →L[ℝ] Rn k := (ι : K₀ →L[ℝ] Rn k).comp K₀.orthogonalProjectionOnto
    let Φ : Rn (m + k) → Rn m × Rn k := fun u => (G u, π u)
    have hΦ : ContDiff ℝ 1 Φ := hG.prodMk π.contDiff
    have hΦd : ∀ u, HasFDerivAt Φ ((fderiv ℝ G u).prod π) u := fun u =>
      ((hG.differentiable one_ne_zero u).hasFDerivAt).prodMk π.hasFDerivAt
    have hinj : Function.Injective (A.prod π) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hAv : A v = 0 := congrArg Prod.fst hv
      have hπv : π v = 0 := congrArg Prod.snd hv
      have hvK : v ∈ K₀ := hAv
      have hP : K₀.orthogonalProjectionOnto v = ⟨v, hvK⟩ :=
        Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨v, hvK⟩
      have : ι ⟨v, hvK⟩ = 0 := by simpa [π, hP] using hπv
      have h0 : (⟨v, hvK⟩ : K₀) = 0 := by simpa using this
      simpa using congrArg Subtype.val h0
    have hdim : finrank ℝ (Rn (m + k)) = finrank ℝ (Rn m × Rn k) := by
      simp [Module.finrank_prod]
    let e' : Rn (m + k) ≃L[ℝ] Rn m × Rn k :=
      ((A.prod π : Rn (m + k) →ₗ[ℝ] Rn m × Rn k).linearEquivOfInjective hinj hdim).toContinuousLinearEquiv
    have he' : (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) = A.prod π := by ext1 v; rfl
    -- `V`: the open set where `DΦ` is invertible.
    let V : Set (Rn (m + k)) := (fderiv ℝ Φ) ⁻¹'
      range ((↑) : (Rn (m + k) ≃L[ℝ] Rn m × Rn k) → Rn (m + k) →L[ℝ] Rn m × Rn k)
    have hVo : IsOpen V := ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv one_ne_zero)
    have hu₀V : u₀ ∈ V := ⟨e', by rw [he', (hΦd u₀).fderiv]⟩
    have hΦa : ContDiffAt ℝ 1 Φ u₀ := hΦ.contDiffAt
    have hΦ'a : HasFDerivAt Φ (e' : Rn (m + k) →L[ℝ] Rn m × Rn k) u₀ := by
      rw [he']; exact hΦd u₀
    have hstrict := ContDiffAt.hasStrictFDerivAt' hΦa hΦ'a one_ne_zero
    let e := HasStrictFDerivAt.toOpenPartialHomeomorph Φ hstrict
    have hecoe : (e : Rn (m + k) → Rn m × Rn k) = Φ := rfl
    refine ⟨e.source ∩ D ∩ V, (e.open_source.inter hD).inter hVo,
      ⟨⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hstrict, hu₀D⟩, hu₀V⟩, ?_⟩
    -- The slice through the chart is the image of the open set `W` under `h`.
    let W : Set (Rn k) := (fun z => (y, z)) ⁻¹' (e.target ∩ e.symm ⁻¹' (D ∩ V))
    have hWo : IsOpen W :=
      (e.isOpen_inter_preimage_symm (hD.inter hVo)).preimage (continuous_const.prodMk continuous_id)
    let h : Rn k → Rn N := fun z => ψ (e.symm (y, z))
    have hh : ContDiffOn ℝ 1 h W := by
      intro z hz
      apply ContDiffAt.contDiffWithinAt
      obtain ⟨hzt, hzD, ⟨L, hL⟩⟩ := hz
      have h1 : ContDiffAt ℝ 1 e.symm (y, z) := by
        refine e.contDiffAt_symm hzt (f₀' := L) ?_ ?_
        · rw [hL, hecoe]
          exact (hΦ.differentiable one_ne_zero _).hasFDerivAt
        · rw [hecoe]; exact hΦ.contDiffAt
      have h2 : ContDiffAt ℝ 1 ψ (e.symm (y, z)) := hψ.contDiffAt (hD.mem_nhds hzD)
      exact h2.comp z (h1.comp z (contDiffAt_const.prodMk contDiffAt_id))
    apply (himage W h hWo hh).mono
    rintro _ ⟨u, ⟨⟨⟨hus, huD⟩, huV⟩, huy⟩, rfl⟩
    have hey : e u = (y, π u) := by
      rw [hecoe]; simp only [Φ]; rw [show G u = y from huy]
    refine ⟨π u, ?_, ?_⟩
    · show (y, π u) ∈ e.target ∩ e.symm ⁻¹' (D ∩ V)
      rw [← hey]
      exact ⟨e.map_source hus, by rw [mem_preimage, e.left_inv hus]; exact ⟨huD, huV⟩⟩
    · show ψ (e.symm (y, π u)) = ψ u
      rw [← hey, e.left_inv hus]
  -- Lindelöf: countably many charts cover the regular part.
  choose O hOo hmem hrect using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hsub : ψ '' (D ∩ {u | Function.Surjective (fderiv ℝ G u)} ∩ G ⁻¹' {y}) ⊆
      ⋃₀ ((fun i => ψ '' (O i ∩ G ⁻¹' {y})) '' T) := by
    rintro _ ⟨u, ⟨huDS, huy⟩, rfl⟩
    have hu : u ∈ ⋃ i ∈ T, O i := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨u, huDS⟩, hmem _⟩
    obtain ⟨i, hiT, hui⟩ := mem_iUnion₂.1 hu
    exact ⟨_, ⟨i, hiT, rfl⟩, ⟨u, ⟨hui, huy⟩, rfl⟩⟩
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (hTc.image _) ?_).mono hsub
  rintro _ ⟨i, -, rfl⟩
  exact hrect i
```

## Key steps

1. C¹ images of open subsets of ℝᵏ are countably k-rectifiable: σ-compact exhaustion, Lipschitz on each compact piece, finite-dimensional Lipschitz extension, countable union of Lipschitz ranges.
2. At u₀ ∈ D ∩ S: K₀ = ker DG(u₀) has dimension k (rank–nullity); π := ι ∘ (orthogonal projection onto K₀) with ι : K₀ ≅ ℝᵏ; L = (DG(u₀), π) is an injective map between spaces of equal dimension, so a linear isomorphism.
3. Φ = (G, π) is C¹ with DΦ(u₀) = L invertible; V = {u : DΦ(u) invertible} is open; the inverse function theorem gives a local inverse Θ : Ω₀ → U₀, which is C¹ at points p with Θ(p) ∈ V; take the chart O := U₀ ∩ D ∩ V.
4. W := {z : (y,z) ∈ Ω₀, Θ(y,z) ∈ D ∩ V} is open, h(z) = ψ(Θ(y,z)) is C¹ on W, and ψ(O ∩ G⁻¹{y}) ⊆ h(W), so it is countably k-rectifiable.
5. Lindelöf (second countability of ℝⁿ): countably many charts O_u cover D ∩ S; a countable union plus monotonicity gives that ψ(D ∩ S ∩ G⁻¹{y}) is countably k-rectifiable.

## Reference use

### local-project

Queries:
- `rg -n "theorem isOpen_iUnion_countable" mathlib/Mathlib/Topology/Bases.lean`
- `rg -n "theorem ContDiffAt.exists_lipschitzOnWith |lemma ContDiffOn.locallyLipschitzOn" mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `rg -n "theorem OpenPartialHomeomorph.contDiffAt_symm " mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `rg -n "protected theorem ContinuousLinearEquiv.isOpen" mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `rg -n "def toOpenPartialHomeomorph|theorem mem_toOpenPartialHomeomorph_source|theorem toOpenPartialHomeomorph_coe" mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `grep -n "theorem\|def \|lemma" mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `rg -n "theorem finrank_range_add_finrank_ker|noncomputable def linearEquivOfInjective" mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `rg -n "theorem FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq" mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `rg -n "theorem orthogonalProjectionOnto_mem_subspace_eq_self|def orthogonalProjectionOnto" mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `rg -l -i "countablyRectifiable" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Geometry mathlib/Mathlib/Analysis/Calculus  (no match)`
- `rg -n "hausdorffMeasure_image_null|image_null_of_locallyLipschitz|LocallyLipschitzOn.hausdorffMeasure" mathlib/Mathlib/MeasureTheory mathlib/Mathlib/Topology/MetricSpace  (no match)`
- `rg -n "theorem hausdorffMeasure_image_le \(h : LipschitzOnWith" mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean; rg -n 'notation "μHE\["' mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `rg -n "^open|^namespace|^abbrev Rn|^def SlicesAreRectifiable" project/GMT/Ch03/Contract.lean; rg -n "^import" project/GMT/Ch03/Contract.lean`
- `rg -n "^theorem countablyRectifiable_image_contDiffOn_open|^theorem countablyRectifiable_sUnion|^theorem countablyRectifiable_iUnion|^theorem countablyRectifiable_of_measure_zero|^theorem CountablyRectifiable.mono|^theorem euclideanHausdorffMeasure_image_le_of_lipschitzOn" <pinned simongmt>/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean Chapter03/Rectifiable.lean Chapter02/Lipschitz.lean`
- `cmp GMT/Ch03/Submission.lean GMT/Ch03/Contract.lean; cmp GMT/Ch03/Contract.lean <snapshot>/project/GMT/Ch03/Contract.lean (both identical)`
- `lean Avail.lean / Avail2.lean: #check of the IFT, Lipschitz, Lindelöf and SimonGMT lemmas after only `import GMT.Ch03.Submission``
- `python3 -I: gmt-compare.py child_modules(contract mode) + lean_contract.validate_lean_statement on both child types, then `lean` on the generated NodeChallenge files`
- `lean /tmp/c1slices-decomp/Integration.lean (full child proofs + sibling stub + parent assembly + `exact Submission.X` comparator checks; #print axioms)`
- `python3 -I dag.json lean_name uniqueness (113 nodes) + grep of both names in all branches' GMT/Ch03/Submission.lean, simongmt and Mathlib (no match)`
- `sed -n 1440,1500p book/chapter-02.txt (Simon 6.2-6.4); sed -n 425,445p book/chapter-03.txt (Remark 2.10(2)); sed -n 268,290p book/chapter-02.txt (Thm 1.8)`

Files inspected:
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/manifest.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/Contract.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/project/GMT/Ch03/README.md`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Bases.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/RCLike.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/ContDiff/Operations.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/FDeriv.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/Calculus/Implicit.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Topology/Algebra/Module/FiniteDimension.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory/Measure/Hausdorff.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/Geometry/Euclidean/Volume/Measure.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/local-references/d498d77b74ea2063/mathlib/Mathlib/MeasureTheory`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/Rectifiable.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter03/SubmanifoldCover.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/lake-packages-25730c7c/simongmt/Poincare/SimonGMT/Chapter02/Lipschitz.lean`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/gmt-compare.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/verifier/lean_contract.py`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/workspaces/gmt-ch03/.humanize/github-theorem-prover/runs/20261011T145601Z-8f12588143/dag.json`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-02.txt`
- `/mnt/data/zhengyang-workspace/gmt-formalize-claude-opus55-max-20261011/book/chapter-03.txt`

Snapshot: project d09bc8a, Mathlib 25730c7c, plus the pinned simongmt package. The workspace Submission.lean and Contract.lean are byte-identical to the snapshot Contract.

No-match results:
- Mathlib has no countable-rectifiability notion; rg 'countablyRectifiable' finds nothing in MeasureTheory, Geometry or Analysis/Calculus.
- Mathlib has no lemma 'locally Lipschitz images of Hausdorff-null sets are null'.
- Mathlib has no regular-level-set rectifiability result.

Available after only `import GMT.Ch03.Submission`, verified by #check:
- Inverse function theorem: HasStrictFDerivAt.toOpenPartialHomeomorph (+ mem_toOpenPartialHomeomorph_source), ContDiffAt.hasStrictFDerivAt', OpenPartialHomeomorph.contDiffAt_symm, ContinuousLinearEquiv.isOpen.
- Lindelöf: TopologicalSpace.isOpen_iUnion_countable.
- Lipschitz: ContDiffAt.exists_lipschitzOnWith, LipschitzOnWith.extend_finite_dimension, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact.
- Linear algebra: LinearMap.finrank_range_add_finrank_ker, LinearMap.linearEquivOfInjective, FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self.
- SimonGMT: countablyRectifiable_range / _iUnion / _sUnion / _of_measure_zero, CountablyRectifiable.mono, Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn.

Not reachable without a new import:
- ContDiffAt.toOpenPartialHomeomorph.
- HasStrictFDerivAt.implicitToOpenPartialHomeomorph.
- SimonGMT Chapter03.countablyRectifiable_image_contDiffOn_open, which is in SubmanifoldCover. Child A therefore inlines its 25-line proof.

Both child types elaborate in the comparator's replayed Contract scope. Both have complete, warning-free Lean proofs using only standard axioms. The selected frozen type follows from them plus a stub of the frozen sibling type, which is the only sorryAx.

Simon Ch. 2 6.3–6.4 (chapter-02.txt lines 1476–1497) and Ch. 3 Remark 2.10(2) (chapter-03.txt lines 439–442) give exactly the regular-part / critical-part structure used.
