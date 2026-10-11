module

public import Poincare.SimonGMT.Chapter08.DeformationFamily

@[expose] public section

/-!
# Simon GMT, Chapter 8, (2.2)--(2.3): arbitrary-family first variation

Let `F(t,x)` be jointly `C²` on `(-1,1) × U`, initially the identity,
and equal to the identity outside a fixed compact `K ⊆ U`. If its slices
are injective maps of `U` into itself, the real mass of the pushed-forward
varifold on `K × G(N,n)` has derivative `∫ div_S X dV`, where `X` is
the initial velocity. Thus the source's diffeomorphism families are covered,
and the result is independent of the chosen family and compact support set.

Properness on the weight support and finite pushed-forward compact mass are
derived from compact support. All measurability and domination conditions
are derived from the local regularity hypotheses, not assumed.

Source: Simon, Chapter 8, (2.1)--(2.3), printed pp. 207--209; the deformation
family hypotheses are those of Chapter 2, (5.6), printed pp. 62--63.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology ENNReal Matrix.Norms.Elementwise

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
variable {N n : ℕ} {U : Set (Euclidean N)}

theorem contDiffAt_deformation
    {F : ℝ × Euclidean N → Euclidean N}
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1)
    {x : Euclidean N} (hx : x ∈ U) : ContDiffAt ℝ 2 F (t, x) :=
  hF.contDiffAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht, hx⟩)

theorem contDiffOn_deformation_slice
    {F : ℝ × Euclidean N → Euclidean N}
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ContDiffOn ℝ 1 (fun x ↦ F (t, x)) U :=
  (hF.of_le (by norm_num)).comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun _ hx ↦ ⟨ht, hx⟩)

theorem familySpatialDerivative_zero
    {F : ℝ × Euclidean N → Euclidean N}
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hU : IsOpen U) (hzero : ∀ x ∈ U, F (0, x) = x)
    {x : Euclidean N} (hx : x ∈ U) :
    familySpatialDerivative F (0, x) = ContinuousLinearMap.id ℝ (Euclidean N) := by
  rw [familySpatialDerivative_eq_fderiv F 0 x
    ((contDiffAt_deformation hF hU (by norm_num) hx).differentiableAt (by norm_num))]
  have he : (fun y ↦ F (0, y)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hzero y hy
  rw [he.fderiv_eq, fderiv_id]

theorem familyJacobian_eq_tangentialJacobianReal
    (F : ℝ × Euclidean N → Euclidean N) (t : ℝ) (x : Euclidean N)
    (S : Grassmannian N n) (hF : DifferentiableAt ℝ F (t, x)) :
    familyJacobian F (t, (x, S.1)) = tangentialJacobianReal (fun y ↦ F (t, y)) x S := by
  change linearTangentialJacobian S (familySpatialDerivative F (t, x)) = _
  rw [familySpatialDerivative_eq_fderiv F t x hF, linearTangentialJacobian_fderiv]

/-- Simon (8.2.3): differentiate the actual tangential-Jacobian integral for
a family that is jointly `C²` only on `(-1,1) × U`. Compactness derives
the required measurability, integrability and uniform derivative bound. -/
theorem hasDerivAt_integral_tangentialJacobianReal_family
    (V : Varifold N n U) (F : ℝ × Euclidean N → Euclidean N)
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hzero : ∀ x ∈ U, F (0, x) = x)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
        tangentialJacobianReal (fun y ↦ F (t, y)) z.1 z.2 ∂V.measure)
      (∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
        tangentialDivergence (initialVelocity F) z.1 z.2 ∂V.measure) 0 := by
  let C := K ×ˢ (univ : Set (Grassmannian N n))
  let e : Euclidean N × Grassmannian N n →
      Euclidean N × Matrix (Fin N) (Fin N) ℝ := fun z ↦ (z.1, z.2.1)
  have he : Continuous e := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hC : IsCompact C := hK.prod isCompact_univ
  have hg (z : Euclidean N × Grassmannian N n) (hz : z ∈ C) :
      ContDiffAt ℝ 1 (familyJacobian F) (0, e z) :=
    contDiffAt_familyJacobian F z.1 z.2
      (contDiffAt_deformation hF V.isOpen_domain (by norm_num) (hKU hz.1))
      (familySpatialDerivative_zero hF V.isOpen_domain hzero (hKU hz.1))
  have hd := hasDerivAt_integral_of_contDiffAt_on_compact
    V.measure C hC (V.finite_on_compact K hK hKU) e he (familyJacobian F) hg
  have hcoeff : (∫ z in C, fderiv ℝ (familyJacobian F) (0, e z) (1, 0) ∂V.measure) =
      ∫ z in C, tangentialDivergence (initialVelocity F) z.1 z.2 ∂V.measure := by
    apply setIntegral_congr_fun hC.measurableSet
    intro z hz
    have hh := ((hg z hz).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 (e z)))
    exact hh.unique (hasDerivAt_linearTangentialJacobian_family F z.1 z.2
      (contDiffAt_deformation hF V.isOpen_domain (by norm_num) (hKU hz.1))
      (familySpatialDerivative_zero hF V.isOpen_domain hzero (hKU hz.1)))
  apply (hd.congr_deriv hcoeff).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
  apply setIntegral_congr_fun hC.measurableSet
  intro z hz
  exact (familyJacobian_eq_tangentialJacobianReal F t z.1 z.2
    ((contDiffAt_deformation hF V.isOpen_domain ht (hKU hz.1)).differentiableAt
      (by norm_num))).symm

theorem initialVelocity_eq_zero_of_fixed
    {F : ℝ × Euclidean N → Euclidean N}
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hU : IsOpen U) {K : Set (Euclidean N)}
    (hfix : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → F (t, x) = x)
    {x : Euclidean N} (hx : x ∈ U) (hxK : x ∉ K) : initialVelocity F x = 0 := by
  rw [initialVelocity_eq_deriv F x
    ((contDiffAt_deformation hF hU (by norm_num) hx).differentiableAt (by norm_num))]
  have he : (fun t ↦ F (t, x)) =ᶠ[𝓝 (0 : ℝ)] (fun _ ↦ x) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hfix t ht x hx hxK
  rw [he.deriv_eq, deriv_const]

theorem tangentialDivergence_initialVelocity_eq_zero_of_fixed
    {F : ℝ × Euclidean N → Euclidean N}
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hU : IsOpen U) {K : Set (Euclidean N)} (hK : IsClosed K)
    (hfix : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → F (t, x) = x)
    {x : Euclidean N} (hx : x ∈ U) (hxK : x ∉ K) (S : Grassmannian N n) :
    tangentialDivergence (initialVelocity F) x S = 0 := by
  have he : initialVelocity F =ᶠ[𝓝 x] (fun _ ↦ (0 : Euclidean N)) := by
    filter_upwards [(hU.sdiff hK).mem_nhds ⟨hx, hxK⟩] with y hy
    exact initialVelocity_eq_zero_of_fixed hF hU hfix hy.1 hy.2
  have hd : fderiv ℝ (fun _ : Euclidean N ↦ (0 : Euclidean N)) x = 0 := fderiv_const_apply (0 : Euclidean N)
  simp only [tangentialDivergence, jacobian, he.fderiv_eq, hd, map_zero,
    Matrix.mul_zero, Matrix.trace_zero]

theorem setIntegral_tangentialDivergence_initialVelocity_eq_firstVariation
    (V : Varifold N n U) (F : ℝ × Euclidean N → Euclidean N)
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (K : Set (Euclidean N)) (hK : IsClosed K)
    (hfix : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → F (t, x) = x) :
    ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
      tangentialDivergence (initialVelocity F) z.1 z.2 ∂V.measure =
      V.firstVariation (initialVelocity F) := by
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [V.ae_mem_domain] with z hz hnot
  exact tangentialDivergence_initialVelocity_eq_zero_of_fixed hF V.isOpen_domain hK hfix
    hz.1 (fun h ↦ hnot ⟨h, mem_univ _⟩) z.2

theorem imageMap_preimage_cylinder_ae_of_fixed
    (V : Varifold N n U) {f : Euclidean N → Euclidean N}
    {K : Set (Euclidean N)} (hfU : MapsTo f U U) (hinj : InjOn f U)
    (hfix : ∀ x ∈ U, x ∉ K → f x = x) :
    imageMap (n := n) f ⁻¹' (K ×ˢ (univ : Set (Grassmannian N n))) =ᵐ[V.measure]
      K ×ˢ (univ : Set (Grassmannian N n)) := by
  filter_upwards [V.ae_mem_domain] with z hz
  apply propext
  change (f z.1 ∈ K ∧ True) ↔ (z.1 ∈ K ∧ True)
  simp only [and_true]
  constructor
  · intro hf
    by_contra hx
    exact hx ((hfix z.1 hz.1 hx) ▸ hf)
  · intro hx
    by_contra hf
    have heq : z.1 = f z.1 :=
      hinj hz.1 (hfU hz.1) (hfix (f z.1) (hfU hz.1) hf).symm
    exact hf (heq ▸ hx)

theorem pushforwardMeasure_cylinder_toReal_eq_integral_of_fixed
    (V : Varifold N n U) {f : Euclidean N → Euclidean N}
    (hf : ContDiffOn ℝ 1 f U) {K : Set (Euclidean N)} (hK : MeasurableSet K)
    (hfU : MapsTo f U U) (hinj : InjOn f U)
    (hfix : ∀ x ∈ U, x ∉ K → f x = x) :
    (V.pushforwardMeasure f (K ×ˢ (univ : Set (Grassmannian N n)))).toReal =
      ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
        tangentialJacobianReal f z.1 z.2 ∂V.measure := by
  rw [V.pushforwardMeasure_apply_of_contDiffOn hf (hK.prod MeasurableSet.univ),
    setLIntegral_congr (V.imageMap_preimage_cylinder_ae_of_fixed hfU hinj hfix)]
  exact (integral_eq_lintegral_of_nonneg_ae
    (f := fun z : Euclidean N × Grassmannian N n ↦ tangentialJacobianReal f z.1 z.2)
    (Eventually.of_forall fun z ↦ tangentialJacobianReal_nonneg f z.1 z.2)
    (V.aestronglyMeasurable_tangentialJacobianReal hf).restrict).symm

/-- A continuous domain map equal to the identity off a compact subset of
`U` is proper on the weight support inside `U`. This derives the
properness hypothesis of Simon (8.2.1) for deformation slices. -/
theorem isProperMap_on_support_of_fixed
    (V : Varifold N n U) {f : Euclidean N → Euclidean N}
    (hf : ContinuousOn f U) {K : Set (Euclidean N)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hfU : MapsTo f U U) (hfix : ∀ x ∈ U, x ∉ K → f x = x) :
    IsProperMap (fun x : ↥(V.weight.support ∩ U) ↦ (⟨f x, hfU x.2.2⟩ : U)) := by
  let g : ↥(V.weight.support ∩ U) → U := fun x ↦ ⟨f x, hfU x.2.2⟩
  have hc : Continuous g :=
    ((continuousOn_iff_continuous_domRestrict.mp hf).comp
      (continuous_subtype_val.subtype_mk (fun x ↦ x.2.2))).subtype_mk _
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hc, ?_⟩
  intro A hA
  let B := (K ∪ (Subtype.val : U → Euclidean N) '' A) ∩ V.weight.support
  have hB : IsCompact B := (hK.union (hA.image continuous_subtype_val)).inter_right
    V.weight.isClosed_support
  have hBU : B ⊆ V.weight.support ∩ U := by
    rintro x ⟨hx, hs⟩
    refine ⟨hs, ?_⟩
    rcases hx with hx | ⟨y, _, rfl⟩
    · exact hKU hx
    · exact y.2
  have hB' : IsCompact ((Subtype.val : ↥(V.weight.support ∩ U) → Euclidean N) ⁻¹' B) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hB (by simpa using hBU)
  apply hB'.of_isClosed_subset (hA.isClosed.preimage hc)
  intro x hx
  refine ⟨?_, x.2.1⟩
  by_cases hxK : x.1 ∈ K
  · exact Or.inl hxK
  · exact Or.inr ⟨g x, hx, hfix x x.2.2 hxK⟩

/-- Finiteness of the localized pushed-forward mass follows from the checked
proper open-domain pushforward, with no extra integrability hypothesis. -/
theorem pushforwardMeasure_cylinder_ne_top_of_fixed
    (V : Varifold N n U) {f : Euclidean N → Euclidean N}
    (hf : ContDiffOn ℝ 1 f U) {K : Set (Euclidean N)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hfU : MapsTo f U U) (hfix : ∀ x ∈ U, x ∉ K → f x = x) :
    V.pushforwardMeasure f (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ :=
  V.pushforwardMeasure_finite_on_compact hf hfU
    (V.isProperMap_on_support_of_fixed hf.continuousOn hK hKU hfU hfix) K hK hKU

/-- Simon (8.2.2)--(8.2.3) for arbitrary jointly `C²` deformation families.
The source assumes diffeomorphisms of `U`; only their injectivity and
domain-preservation are needed here. No assumption is imposed outside `U`. -/
theorem hasDerivAt_pushforwardMeasure_cylinder_family
    (V : Varifold N n U) (F : ℝ × Euclidean N → Euclidean N)
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hzero : ∀ x ∈ U, F (0, x) = x)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hfU : ∀ t ∈ Ioo (-1 : ℝ) 1, MapsTo (fun x ↦ F (t, x)) U U)
    (hinj : ∀ t ∈ Ioo (-1 : ℝ) 1, InjOn (fun x ↦ F (t, x)) U)
    (hfix : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → F (t, x) = x) :
    HasDerivAt
      (fun t : ℝ ↦ (V.pushforwardMeasure (fun x ↦ F (t, x))
        (K ×ˢ (univ : Set (Grassmannian N n)))).toReal)
      (V.firstVariation (initialVelocity F)) 0 := by
  have hd := V.hasDerivAt_integral_tangentialJacobianReal_family F hF hzero K hK hKU
  rw [V.setIntegral_tangentialDivergence_initialVelocity_eq_firstVariation F hF K hK.isClosed hfix] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)] with t ht
  exact V.pushforwardMeasure_cylinder_toReal_eq_integral_of_fixed
    (contDiffOn_deformation_slice hF ht) hK.measurableSet (hfU t ht) (hinj t ht) (hfix t ht)

/-- First variation is intrinsic to the open domain, regardless of how the
vector field is extended outside it. -/
theorem firstVariation_congr_on
    (V : Varifold N n U) {X Y : Euclidean N → Euclidean N}
    (hXY : EqOn X Y U) : V.firstVariation X = V.firstVariation Y := by
  apply integral_congr_ae
  filter_upwards [V.ae_mem_domain] with z hz
  have he : X =ᶠ[𝓝 z.1] Y := by
    filter_upwards [V.isOpen_domain.mem_nhds hz.1] with x hx
    exact hXY hx
  simp only [tangentialDivergence, jacobian, he.fderiv_eq]

/-- Family and localization-set independence in Simon (8.2.2): every
admissible family with initial velocity `X` has mass derivative `δV(X)`.
The displayed derivative formula is Simon (8.2.3), since `firstVariation`
is the integral of the tangential divergence. -/
theorem hasDerivAt_pushforwardMeasure_cylinder_family_of_velocity
    (V : Varifold N n U) (F : ℝ × Euclidean N → Euclidean N)
    (hF : ContDiffOn ℝ 2 F (Ioo (-1 : ℝ) 1 ×ˢ U))
    (hzero : ∀ x ∈ U, F (0, x) = x)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hfU : ∀ t ∈ Ioo (-1 : ℝ) 1, MapsTo (fun x ↦ F (t, x)) U U)
    (hinj : ∀ t ∈ Ioo (-1 : ℝ) 1, InjOn (fun x ↦ F (t, x)) U)
    (hfix : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ x ∈ U, x ∉ K → F (t, x) = x)
    (X : Euclidean N → Euclidean N)
    (hvelocity : ∀ x ∈ U, deriv (fun t ↦ F (t, x)) 0 = X x) :
    HasDerivAt
      (fun t : ℝ ↦ (V.pushforwardMeasure (fun x ↦ F (t, x))
        (K ×ˢ (univ : Set (Grassmannian N n)))).toReal)
      (V.firstVariation X) 0 := by
  have hX : V.firstVariation (initialVelocity F) = V.firstVariation X := by
    apply V.firstVariation_congr_on
    intro x hx
    rw [initialVelocity_eq_deriv F x
      ((contDiffAt_deformation hF V.isOpen_domain (by norm_num) hx).differentiableAt
        (by norm_num))]
    exact hvelocity x hx
  rw [← hX]
  exact V.hasDerivAt_pushforwardMeasure_cylinder_family F hF hzero K hK hKU hfU hinj hfix

end
end Poincare.SimonGMT.Chapter08.Varifold
