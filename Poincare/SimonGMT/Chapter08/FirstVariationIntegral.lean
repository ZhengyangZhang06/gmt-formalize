module

public import Poincare.SimonGMT.Chapter08.JacobianBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-!
# Differentiation of the varifold Jacobian integral

For the compactly supported `C¹` variation `φₜ = id + t X`, the Jacobian
integral has derivative `δV(X)`.  Pointwise differentiation and the uniform
domination estimate are proved in the preceding modules.  Measurability of
the tangential Jacobian and the transported image plane follows from their
explicit ambient projection-matrix formulas; no measurability hypotheses
are imposed on the first-variation theorem.

Source: `Simon-gmt new.pdf`, (8.2.2)--(8.2.3), printed pp. 208--209.
-/

open Set Filter MeasureTheory Function Metric
open scoped Topology NNReal ENNReal

namespace Poincare.SimonGMT.Chapter08.Varifold

noncomputable section

variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Localizing to any cylinder containing the support of the variation does
not change its first-variation integral. -/
theorem setIntegral_tangentialDivergence_eq_firstVariation
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (K : Set (Euclidean N)) (hsupport : tsupport X ⊆ K) :
    ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
      tangentialDivergence X z.1 z.2 ∂V.measure = V.firstVariation X := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  by_contra hne
  have hmem : z ∈ support
      (fun z : Euclidean N × Grassmannian N n ↦ tangentialDivergence X z.1 z.2) := hne
  have hsup := support_tangentialDivergence_subset X hmem
  exact hz ⟨hsupport hsup.1, mem_univ _⟩

/-- The differentiation-under-the-integral step in Simon (8.2.3) for
`φₜ = id + t X`.  Differentiation, domination and measurability all follow
from the compactly supported `C¹` field. -/
theorem hasDerivAt_integral_tangentialJacobianReal_id_add_smul
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (hX : ContDiff ℝ 1 X) (hXcompact : HasCompactSupport X)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupport : tsupport X ⊆ K) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
        tangentialJacobianReal (fun y ↦ y + t • X y) z.1 z.2 ∂V.measure)
      (V.firstVariation X) 0 := by
  obtain ⟨ε, C, hε, hC⟩ :=
    exists_uniform_lipschitzOnWith_tangentialJacobianReal (n := n) X hX hXcompact
  have hfinite := V.finite_on_compact K hK hKU
  have hzero : IntegrableOn
      (fun z : Euclidean N × Grassmannian N n ↦
        tangentialJacobianReal (fun y ↦ y + (0 : ℝ) • X y) z.1 z.2)
      (K ×ˢ (univ : Set (Grassmannian N n))) V.measure := by
    simpa only [zero_smul, add_zero, tangentialJacobianReal_id] using
      (integrableOn_const hfinite : IntegrableOn
        (fun _ : Euclidean N × Grassmannian N n ↦ (1 : ℝ))
        (K ×ˢ (univ : Set (Grassmannian N n))) V.measure)
  have hlip : ∀ᵐ z ∂(V.measure.restrict (K ×ˢ (univ : Set (Grassmannian N n)))),
      LipschitzOnWith (Real.nnabs (C : ℝ))
        (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) z.1 z.2)
        (ball 0 ε) := by
    filter_upwards with z
    simpa only [Real.nnabs_coe] using hC z.1 z.2
  have hdiff : ∀ᵐ z ∂(V.measure.restrict (K ×ˢ (univ : Set (Grassmannian N n)))),
      HasDerivAt
        (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) z.1 z.2)
        (tangentialDivergence X z.1 z.2) 0 := by
    filter_upwards with z
    exact hasDerivAt_tangentialJacobianReal_id_add_smul X z.1 z.2
      hX.differentiable_one.differentiableAt
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := fun _ : Euclidean N × Grassmannian N n ↦ (C : ℝ))
    (Metric.ball_mem_nhds 0 hε)
    (Eventually.of_forall fun t ↦
      (continuous_tangentialJacobianReal (contDiff_id.add (hX.const_smul t))).aestronglyMeasurable)
    hzero
    (continuous_tangentialDivergence hX).aestronglyMeasurable hlip
    (integrableOn_const hfinite) hdiff
  rwa [setIntegral_tangentialDivergence_eq_firstVariation V X K hsupport] at hderiv

/-- The Jacobian integral on a compact cylinder is finite near zero; this
ensures that taking real mass below does not use the value of `toReal` at
infinity. -/
theorem eventually_integrableOn_tangentialJacobianReal_id_add_smul
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (hX : ContDiff ℝ 1 X) (hXcompact : HasCompactSupport X)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᶠ t : ℝ in 𝓝 0, IntegrableOn
      (fun z : Euclidean N × Grassmannian N n ↦
        tangentialJacobianReal (fun y ↦ y + t • X y) z.1 z.2)
      (K ×ˢ (univ : Set (Grassmannian N n))) V.measure := by
  obtain ⟨ε, C, hε, hC⟩ :=
    exists_uniform_lipschitzOnWith_tangentialJacobianReal (n := n) X hX hXcompact
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  have hflow : ContDiff ℝ 1 (fun x ↦ x + t • X x) := contDiff_id.add (hX.const_smul t)
  apply Integrable.mono' (integrableOn_const (V.finite_on_compact K hK hKU)
    (C := (C : ℝ) * ε + 1))
    (continuous_tangentialJacobianReal hflow).aestronglyMeasurable
  filter_upwards with z
  have hlip := (hC z.1 z.2).dist_le_mul t ht 0 (mem_ball_self hε)
  simp only [zero_smul, add_zero, tangentialJacobianReal_id, Real.dist_eq, sub_zero] at hlip
  have hupper := (le_abs_self
    (tangentialJacobianReal (fun y ↦ y + t • X y) z.1 z.2 - 1)).trans hlip
  have habs : |t| < ε := by simpa only [mem_ball, Real.dist_eq, sub_zero] using ht
  rw [Real.norm_eq_abs, abs_of_nonneg (tangentialJacobianReal_nonneg _ _ _)]
  nlinarith [C.coe_nonneg]

/-- A Lipschitz perturbation of the identity is injective when its Lipschitz
constant is strictly less than one. -/
theorem injective_id_add_smul_of_lipschitzWith
    (X : Euclidean N → Euclidean N) {L : ℝ≥0} (hX : LipschitzWith L X)
    {t : ℝ} (ht : |t| * (L : ℝ) < 1) :
    Injective (fun x ↦ x + t • X x) := by
  intro x y hxy
  have hsub : x - y + t • (X x - X y) = 0 := by
    calc
      _ = (x + t • X x) - (y + t • X y) := by module
      _ = 0 := sub_eq_zero.mpr hxy
  have heq : ‖x - y‖ = |t| * ‖X x - X y‖ := by
    rw [eq_neg_of_add_eq_zero_left hsub, norm_neg, norm_smul, Real.norm_eq_abs]
  have hLip : ‖X x - X y‖ ≤ (L : ℝ) * ‖x - y‖ := by
    simpa only [dist_eq_norm] using hX.dist_le_mul x y
  have hle : ‖x - y‖ ≤ (|t| * (L : ℝ)) * ‖x - y‖ := by
    rw [heq]
    calc
      |t| * ‖X x - X y‖ ≤ |t| * ((L : ℝ) * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left hLip (abs_nonneg t)
      _ = (|t| * (L : ℝ)) * (|t| * ‖X x - X y‖) := by rw [← heq]; ring
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- The affine variation of a compactly supported `C¹` field is injective for
all sufficiently small times. -/
theorem eventually_injective_id_add_smul
    (X : Euclidean N → Euclidean N) (hX : ContDiff ℝ 1 X)
    (hXcompact : HasCompactSupport X) :
    ∀ᶠ t : ℝ in 𝓝 0, Injective (fun x ↦ x + t • X x) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXcompact hX one_ne_zero
  have hc : Continuous (fun t : ℝ ↦ |t| * (L : ℝ)) := by fun_prop
  have ht : ∀ᶠ t : ℝ in 𝓝 0, |t| * (L : ℝ) < 1 :=
    hc.continuousAt.eventually_lt continuousAt_const (by simp)
  exact ht.mono fun _ ht ↦ injective_id_add_smul_of_lipschitzWith X hL ht

/-- An injective variation that is the identity outside `K` preserves exactly
the cylinder `K × G(N,n)` occurring in Simon (8.2.2). -/
theorem imageMap_preimage_cylinder_id_add_smul
    (X : Euclidean N → Euclidean N) (K : Set (Euclidean N))
    (hsupport : tsupport X ⊆ K) (t : ℝ)
    (hinj : Injective (fun x ↦ x + t • X x)) :
    imageMap (n := n) (fun x ↦ x + t • X x) ⁻¹'
        (K ×ˢ (univ : Set (Grassmannian N n))) =
      K ×ˢ (univ : Set (Grassmannian N n)) := by
  let f : Euclidean N → Euclidean N := fun x ↦ x + t • X x
  have hfix : ∀ x, x ∉ K → f x = x := by
    intro x hx
    have hzero : X x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hsupport h))
    simp [f, hzero]
  ext z
  change (f z.1 ∈ K ∧ True) ↔ (z.1 ∈ K ∧ True)
  simp only [and_true]
  constructor
  · intro hz
    by_contra hx
    exact hx ((hfix z.1 hx) ▸ hz)
  · intro hz
    by_contra hx
    have heq : f z.1 = z.1 := hinj (hfix (f z.1) hx)
    exact hx (heq.symm ▸ hz)

/-- Real mass of the pushed-forward varifold on the fixed compact cylinder,
evaluated using the exact pushforward formula (8.2.1). -/
theorem pushforwardMeasure_cylinder_toReal_eq_integral
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (K : Set (Euclidean N)) (hK : MeasurableSet K) (hsupport : tsupport X ⊆ K)
    (t : ℝ) (hinj : Injective (fun x ↦ x + t • X x))
    (hF : Measurable (imageMap (n := n) (fun x ↦ x + t • X x)))
    (hJ : AEStronglyMeasurable
      (fun z : Euclidean N × Grassmannian N n ↦
        tangentialJacobianReal (fun x ↦ x + t • X x) z.1 z.2)
      (V.measure.restrict (K ×ˢ (univ : Set (Grassmannian N n))))) :
    (V.pushforwardMeasure (fun x ↦ x + t • X x)
      (K ×ˢ (univ : Set (Grassmannian N n)))).toReal =
      ∫ z in K ×ˢ (univ : Set (Grassmannian N n)),
        tangentialJacobianReal (fun x ↦ x + t • X x) z.1 z.2 ∂V.measure := by
  rw [V.pushforwardMeasure_apply _ hF (hK.prod MeasurableSet.univ),
    imageMap_preimage_cylinder_id_add_smul X K hsupport t hinj]
  simp only [tangentialJacobian]
  exact (integral_eq_lintegral_of_nonneg_ae
    (f := fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobianReal (fun x ↦ x + t • X x) z.1 z.2)
    (Eventually.of_forall fun z ↦ tangentialJacobianReal_nonneg _ z.1 z.2) hJ).symm

/-- The pushed-forward mass on the fixed cylinder is finite for small times. -/
theorem eventually_pushforwardMeasure_cylinder_ne_top
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (hX : ContDiff ℝ 1 X) (hXcompact : HasCompactSupport X)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupport : tsupport X ⊆ K) :
    ∀ᶠ t : ℝ in 𝓝 0, V.pushforwardMeasure (fun x ↦ x + t • X x)
      (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ := by
  filter_upwards [eventually_injective_id_add_smul X hX hXcompact,
    V.eventually_integrableOn_tangentialJacobianReal_id_add_smul X hX hXcompact K hK hKU]
      with t hinj hJint
  have hF : Measurable (imageMap (n := n) (fun x ↦ x + t • X x)) :=
    measurable_imageMap (contDiff_id.add (hX.const_smul t))
  rw [V.pushforwardMeasure_apply _ hF (hK.measurableSet.prod MeasurableSet.univ),
    imageMap_preimage_cylinder_id_add_smul X K hsupport t hinj]
  simp only [tangentialJacobian]
  exact (lintegral_ofReal_ne_top_iff_integrable hJint.aestronglyMeasurable
    (Eventually.of_forall fun z ↦ tangentialJacobianReal_nonneg _ z.1 z.2)).mpr hJint

/-- Simon (8.2.2)--(8.2.3) for the affine variation `φₜ = id + t X`.
Jacobian differentiation, domination, localization, image-map measurability
and small-time injectivity are all derived from the compactly supported
`C¹` vector field.  The extension to arbitrary jointly `C²` families on
the open domain is proved in `DeformationIntegral`. -/
theorem hasDerivAt_pushforwardMeasure_cylinder_id_add_smul
    (V : Varifold N n U) (X : Euclidean N → Euclidean N)
    (hX : ContDiff ℝ 1 X) (hXcompact : HasCompactSupport X)
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKU : K ⊆ U)
    (hsupport : tsupport X ⊆ K) :
    HasDerivAt
      (fun t : ℝ ↦ (V.pushforwardMeasure (fun x ↦ x + t • X x)
        (K ×ˢ (univ : Set (Grassmannian N n)))).toReal)
      (V.firstVariation X) 0 := by
  apply (V.hasDerivAt_integral_tangentialJacobianReal_id_add_smul
    X hX hXcompact K hK hKU hsupport).congr_of_eventuallyEq
  filter_upwards [eventually_injective_id_add_smul X hX hXcompact] with t hinj
  have hflow : ContDiff ℝ 1 (fun x ↦ x + t • X x) := contDiff_id.add (hX.const_smul t)
  exact V.pushforwardMeasure_cylinder_toReal_eq_integral X K hK.measurableSet
    hsupport t hinj (measurable_imageMap hflow)
    (continuous_tangentialJacobianReal hflow).aestronglyMeasurable

end

end Poincare.SimonGMT.Chapter08.Varifold
