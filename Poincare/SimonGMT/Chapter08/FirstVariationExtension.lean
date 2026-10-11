module

public import Poincare.SimonGMT.Chapter08.FirstVariationBounds
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

@[expose] public section

/-!
# Extending first variation to continuous test vector fields

The local boundedness hypothesis preceding Simon (8.2.5) constructs a
unique linear extension of first variation to continuous compactly
supported vector fields. The extension preserves all local uniform-norm
bounds. This is the extension step needed before applying the vector
Riesz representation theorem in (8.2.5)--(8.2.6); measure and polar-field
existence are not assumed here.

Source: `Simon-gmt new.pdf`, printed p. 209, PDF object 215.
-/

open Set Filter MeasureTheory Function
open scoped Topology ENNReal CompactlySupported BoundedContinuousFunction

namespace Poincare.SimonGMT.Chapter08.Varifold
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {N n : ℕ} {U : Set (Euclidean N)}

/-- Continuous compactly supported ambient vector fields with support in
`W`, with the uniform norm inherited from bounded continuous functions. -/
def continuousFields (W : Set (Euclidean N)) :
    Submodule ℝ (Euclidean N →ᵇ Euclidean N) where
  carrier := {f | HasCompactSupport f ∧ tsupport f ⊆ W}
  zero_mem' := ⟨HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    exact (tsupport_add _ _).trans (union_subset hf.2 hg.2)
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.smul_left, ?_⟩
    exact (closure_mono (support_const_smul_subset c (f : Euclidean N → Euclidean N))).trans hf.2

instance (W : Set (Euclidean N)) : NormedAddCommGroup (continuousFields W) :=
  (continuousFields W).normedAddCommGroup

instance (W : Set (Euclidean N)) : NormedSpace ℝ (continuousFields W) :=
  (continuousFields W).normedSpace

/-- The `C¹` subspace of continuous compactly supported vector fields. -/
def smoothFields (W : Set (Euclidean N)) : Submodule ℝ (continuousFields W) where
  carrier := {f | ContDiff ℝ 1 (f.1 : Euclidean N → Euclidean N)}
  zero_mem' := by
    change ContDiff ℝ 1 (fun _ : Euclidean N ↦ (0 : Euclidean N))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ 1 (f.1 : Euclidean N → Euclidean N) at hf
    change ContDiff ℝ 1 (g.1 : Euclidean N → Euclidean N) at hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ 1 (f.1 : Euclidean N → Euclidean N) at hf
    exact hf.const_smul c

instance (W : Set (Euclidean N)) : AddCommGroup (smoothFields W) :=
  (smoothFields W).addCommGroup

/-- Put a source test vector field into its continuous uniform-norm space. -/
def TestVectorField.toContinuousField (X : TestVectorField (N := N) U) : continuousFields U :=
  ⟨(⟨⟨X.toFun, X.contDiff.continuous⟩, X.compactSupport⟩ :
    C_c(Euclidean N, Euclidean N)).toBoundedContinuousFunction,
      X.compactSupport, X.support_subset⟩

/-- Put a source test vector field into the smooth subspace. -/
def TestVectorField.toSmoothField (X : TestVectorField (N := N) U) : smoothFields U :=
  ⟨X.toContinuousField, X.contDiff⟩

/-- Recover the original test-field structure from the smooth subspace. -/
def smoothFieldToTest {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (f : smoothFields W) : TestVectorField (N := N) U where
  toFun := f.1.1
  contDiff := f.2
  compactSupport := f.1.2.1
  support_subset := f.1.2.2.trans hWU

/-- Support-preserving smooth approximation makes the `C¹` subspace
dense in the uniform norm, for every support set `W`. -/
theorem dense_smoothFields (W : Set (Euclidean N)) :
    DenseRange (smoothFields W).subtype := by
  rw [Metric.denseRange_iff]
  intro f ε hε
  obtain ⟨X, hXs, hXe⟩ := exists_testVectorField_uniform_approx
    (U := W) f.1 f.1.continuous f.2.1 f.2.2 (half_pos hε)
  refine ⟨X.toSmoothField, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
  change dist f.1 X.toContinuousField.1 ≤ ε / 2
  rw [dist_eq_norm]
  apply BoundedContinuousFunction.norm_le (half_pos hε).le |>.mpr
  intro x
  change ‖f.1 x - X x‖ ≤ ε / 2
  rw [norm_sub_rev]
  exact (hXe x).le

/-- First variation as a real linear functional on smooth fields with a
fixed support set. -/
def smoothFirstVariation (V : Varifold N n U) {W : Set (Euclidean N)}
    (hWU : W ⊆ U) : smoothFields W →ₗ[ℝ] ℝ where
  toFun f := V.firstVariation f.1.1
  map_add' f g := V.firstVariation_add f.2 g.2 f.1.2.1 g.1.2.1
    (f.1.2.2.trans hWU) (g.1.2.2.trans hWU)
  map_smul' c f := V.firstVariation_const_smul c f.2 f.1.2.1

/-- The local extension as a continuous linear map. The meaningful
extension and bound properties are proved below from finiteness of the
source's actual supremum. -/
def localContinuousFirstVariation (V : Varifold N n U) {W : Set (Euclidean N)}
    (hWU : W ⊆ U) : continuousFields W →L[ℝ] ℝ :=
  LinearMap.extendOfNorm (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := smoothFields W) (Eₗ := continuousFields W) (F := ℝ)
    (V.smoothFirstVariation hWU) (smoothFields W).subtype

theorem smoothFirstVariation_norm_bound (V : Varifold N n U)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) (f : smoothFields W) :
    ‖V.smoothFirstVariation hWU f‖ ≤
      (V.firstVariationNormOn W).toReal * ‖(smoothFields W).subtype f‖ := by
  have hbound : ∀ X : TestVectorField (N := N) U, X.UnitSupportedIn W →
      |V.firstVariation X| ≤ (V.firstVariationNormOn W).toReal := by
    intro X hX
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp (V.le_firstVariationNormOn W X hX)
  exact V.firstVariation_bound_of_unit_bound W _ ENNReal.toReal_nonneg hbound
    (smoothFieldToTest hWU f) f.1.2.2 (norm_nonneg f.1)
    (fun x ↦ BoundedContinuousFunction.norm_coe_le_norm f.1.1 x)

theorem localContinuousFirstVariation_eq (V : Varifold N n U)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) (f : smoothFields W) :
    V.localContinuousFirstVariation hWU f.1 = V.firstVariation f.1.1 :=
  LinearMap.extendOfNorm_eq (dense_smoothFields W)
    ⟨_, V.smoothFirstVariation_norm_bound hWU hfin⟩ f

theorem localContinuousFirstVariation_norm_bound (V : Varifold N n U)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) (f : continuousFields W) :
    ‖V.localContinuousFirstVariation hWU f‖ ≤
      (V.firstVariationNormOn W).toReal * ‖f‖ :=
  LinearMap.norm_extendOfNorm_apply_le (dense_smoothFields W) _
    (V.smoothFirstVariation_norm_bound hWU hfin) f

theorem continuousFields_mono {W Z : Set (Euclidean N)} (hWZ : W ⊆ Z) :
    continuousFields W ≤ continuousFields Z :=
  fun _ hf ↦ ⟨hf.1, hf.2.trans hWZ⟩

/-- Inclusion of support spaces is an isometry for the uniform norm. -/
def continuousFieldInclusion {W Z : Set (Euclidean N)} (hWZ : W ⊆ Z) :
    continuousFields W →L[ℝ] continuousFields Z where
  toLinearMap := Submodule.inclusion (continuousFields_mono hWZ)
  cont := continuous_subtype_val.subtype_mk _

theorem firstVariationNormOn_mono (V : Varifold N n U)
    {W Z : Set (Euclidean N)} (hWZ : W ⊆ Z) :
    V.firstVariationNormOn W ≤ V.firstVariationNormOn Z := by
  classical
  unfold firstVariationNormOn
  refine iSup_le fun X ↦ ?_
  split_ifs with hX
  · apply le_iSup_of_le X
    rw [ite_eq_left ⟨hX.1.trans hWZ, hX.2⟩]
  · exact zero_le

/-- Local extensions agree when the support set is enlarged. This is
the compatibility needed to construct a functional on all of `C_c(U)`. -/
theorem localContinuousFirstVariation_inclusion (V : Varifold N n U)
    {W Z : Set (Euclidean N)} (hWZ : W ⊆ Z) (hZU : Z ⊆ U)
    (hfin : V.firstVariationNormOn Z ≠ ∞) (f : continuousFields W) :
    V.localContinuousFirstVariation hZU (continuousFieldInclusion hWZ f) =
      V.localContinuousFirstVariation (hWZ.trans hZU) f := by
  have hWfin : V.firstVariationNormOn W ≠ ∞ :=
    ne_top_of_le_ne_top hfin (V.firstVariationNormOn_mono hWZ)
  have heq :
      (V.localContinuousFirstVariation hZU).comp (continuousFieldInclusion hWZ) =
        V.localContinuousFirstVariation (hWZ.trans hZU) := by
    apply DFunLike.ext'
    apply (dense_smoothFields W).equalizer
      ((V.localContinuousFirstVariation hZU).comp (continuousFieldInclusion hWZ)).continuous
      (V.localContinuousFirstVariation (hWZ.trans hZU)).continuous
    funext g
    let gZ : smoothFields Z := ⟨continuousFieldInclusion hWZ g.1, g.2⟩
    change V.localContinuousFirstVariation hZU gZ.1 =
      V.localContinuousFirstVariation (hWZ.trans hZU) g.1
    rw [V.localContinuousFirstVariation_eq hZU hfin gZ,
      V.localContinuousFirstVariation_eq (hWZ.trans hZU) hWfin g]
    rfl
  exact DFunLike.congr_fun heq f

/-- Compact subsets of the domain inherit a finite first-variation norm
from the source's relatively compact open neighborhoods. -/
theorem HasLocallyBoundedFirstVariation.finite_on_compact
    {V : Varifold N n U} (hV : V.HasLocallyBoundedFirstVariation)
    {K : Set (Euclidean N)} (hK : IsCompact K) (hKU : K ⊆ U) :
    V.firstVariationNormOn K ≠ ∞ := by
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK V.isOpen_domain hKU
  exact ne_top_of_le_ne_top (hV W hWo ⟨hWc, hWU⟩)
    (V.firstVariationNormOn_mono hKW)

/-- Evaluate the local extension on the field's own compact support.
Compatibility makes this independent of any larger support neighborhood. -/
def continuousFirstVariationValue (V : Varifold N n U) (f : continuousFields U) : ℝ :=
  V.localContinuousFirstVariation f.2.2 ⟨f.1, f.2.1, subset_rfl⟩

theorem continuousFirstVariationValue_eq_local (V : Varifold N n U)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) (f : continuousFields U)
    (hfW : tsupport f.1 ⊆ W) :
    V.continuousFirstVariationValue f =
      V.localContinuousFirstVariation hWU ⟨f.1, f.2.1, hfW⟩ := by
  exact (V.localContinuousFirstVariation_inclusion hfW hWU hfin
    ⟨f.1, f.2.1, subset_rfl⟩).symm

/-- First variation extends to a real-linear functional on all continuous
compactly supported fields in the domain, using only local boundedness. -/
def continuousFirstVariation (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : continuousFields U →ₗ[ℝ] ℝ where
  toFun := V.continuousFirstVariationValue
  map_add' f g := by
    let K := tsupport f.1 ∪ tsupport g.1
    have hKU : K ⊆ U := union_subset f.2.2 g.2.2
    have hKfin := hV.finite_on_compact (f.2.1.union g.2.1) hKU
    have hfK : tsupport f.1 ⊆ K := subset_union_left
    have hgK : tsupport g.1 ⊆ K := subset_union_right
    have hfgK : tsupport (f + g).1 ⊆ K := tsupport_add f.1 g.1
    rw [V.continuousFirstVariationValue_eq_local hKU hKfin (f + g) hfgK,
      V.continuousFirstVariationValue_eq_local hKU hKfin f hfK,
      V.continuousFirstVariationValue_eq_local hKU hKfin g hgK]
    exact (V.localContinuousFirstVariation hKU).map_add
      ⟨f.1, f.2.1, hfK⟩ ⟨g.1, g.2.1, hgK⟩
  map_smul' c f := by
    have hKfin := hV.finite_on_compact f.2.1 f.2.2
    have hcf : tsupport (c • f).1 ⊆ tsupport f.1 :=
      closure_mono (support_const_smul_subset c (f.1 : Euclidean N → Euclidean N))
    rw [V.continuousFirstVariationValue_eq_local f.2.2 hKfin (c • f) hcf,
      V.continuousFirstVariationValue_eq_local f.2.2 hKfin f subset_rfl]
    exact (V.localContinuousFirstVariation f.2.2).map_smul c
      ⟨f.1, f.2.1, subset_rfl⟩

theorem continuousFirstVariation_eq_test (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (X : TestVectorField (N := N) U) :
    V.continuousFirstVariation hV X.toContinuousField = V.firstVariation X := by
  let g : smoothFields (tsupport X.toFun) :=
    ⟨⟨X.toContinuousField.1, X.compactSupport, subset_rfl⟩, X.contDiff⟩
  exact V.localContinuousFirstVariation_eq X.support_subset
    (hV.finite_on_compact X.compactSupport X.support_subset) g

/-- Every original local uniform-norm bound survives the extension. -/
theorem continuousFirstVariation_norm_bound (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) (f : continuousFields U)
    (hfW : tsupport f.1 ⊆ W) :
    ‖V.continuousFirstVariation hV f‖ ≤
      (V.firstVariationNormOn W).toReal * ‖f‖ := by
  change ‖V.continuousFirstVariationValue f‖ ≤ _
  rw [V.continuousFirstVariationValue_eq_local hWU hfin f hfW]
  exact V.localContinuousFirstVariation_norm_bound hWU hfin ⟨f.1, f.2.1, hfW⟩

/-- The local operator norm is exactly the supremum in Simon (8.2.5).
Thus completing the test class introduces no loss in the variation norm. -/
theorem localContinuousFirstVariation_norm_eq (V : Varifold N n U)
    {W : Set (Euclidean N)} (hWU : W ⊆ U)
    (hfin : V.firstVariationNormOn W ≠ ∞) :
    ENNReal.ofReal ‖V.localContinuousFirstVariation hWU‖ = V.firstVariationNormOn W := by
  classical
  apply le_antisymm
  · rw [← ENNReal.ofReal_toReal hfin]
    apply ENNReal.ofReal_le_ofReal
    exact (V.localContinuousFirstVariation hWU).opNorm_le_bound
      ENNReal.toReal_nonneg (V.localContinuousFirstVariation_norm_bound hWU hfin)
  · unfold firstVariationNormOn
    refine iSup_le fun X ↦ ?_
    split_ifs with hX
    · let f : smoothFields W :=
        ⟨⟨X.toContinuousField.1, X.compactSupport, hX.1⟩, X.contDiff⟩
      have hf : ‖f.1‖ ≤ 1 := BoundedContinuousFunction.norm_le zero_le_one |>.mpr hX.2
      apply ENNReal.ofReal_le_ofReal
      change ‖V.firstVariation X‖ ≤ _
      change ‖V.firstVariation f.1.1‖ ≤ _
      rw [← V.localContinuousFirstVariation_eq hWU hfin f]
      exact ((V.localContinuousFirstVariation hWU).le_opNorm f.1).trans
        (by simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg _))
    · exact zero_le

/-- The extension is continuous on every fixed compact-support space. -/
theorem continuousFirstVariation_continuous_on_support (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation)
    {K : Set (Euclidean N)} (hK : IsCompact K) (hKU : K ⊆ U) :
    Continuous (fun f : continuousFields K ↦
      V.continuousFirstVariation hV (continuousFieldInclusion hKU f)) := by
  have heq : (fun f : continuousFields K ↦
      V.continuousFirstVariation hV (continuousFieldInclusion hKU f)) =
      V.localContinuousFirstVariation hKU := by
    funext f
    exact V.continuousFirstVariationValue_eq_local hKU
      (hV.finite_on_compact hK hKU) (continuousFieldInclusion hKU f) f.2.2
  rw [heq]
  exact (V.localContinuousFirstVariation hKU).continuous

/-- Uniqueness of the extension among functionals continuous on each
compact-support space. No measure-representation assumption is used. -/
theorem continuousFirstVariation_unique (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (L : continuousFields U →ₗ[ℝ] ℝ)
    (hLtest : ∀ X : TestVectorField (N := N) U,
      L X.toContinuousField = V.firstVariation X)
    (hLcont : ∀ (K : Set (Euclidean N)) (_hK : IsCompact K) (hKU : K ⊆ U),
      Continuous (fun f : continuousFields K ↦ L (continuousFieldInclusion hKU f))) :
    L = V.continuousFirstVariation hV := by
  ext f
  let K := tsupport f.1
  have hK : IsCompact K := f.2.1
  have hKU : K ⊆ U := f.2.2
  have heq :
      (fun g : continuousFields K ↦ L (continuousFieldInclusion hKU g)) =
      fun g : continuousFields K ↦
        V.continuousFirstVariation hV (continuousFieldInclusion hKU g) := by
    apply (dense_smoothFields K).equalizer (hLcont K hK hKU)
      (V.continuousFirstVariation_continuous_on_support hV hK hKU)
    funext g
    let X := smoothFieldToTest hKU g
    change L X.toContinuousField = V.continuousFirstVariation hV X.toContinuousField
    rw [hLtest, V.continuousFirstVariation_eq_test hV]
  exact congrFun heq ⟨f.1, f.2.1, subset_rfl⟩

/-- The full existence-and-uniqueness extension statement obtained from
the hypothesis printed immediately before Simon (8.2.5). -/
theorem existsUnique_continuousFirstVariation (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) :
    ∃! L : continuousFields U →ₗ[ℝ] ℝ,
      (∀ X : TestVectorField (N := N) U,
        L X.toContinuousField = V.firstVariation X) ∧
      (∀ (K : Set (Euclidean N)) (_hK : IsCompact K) (hKU : K ⊆ U),
        Continuous (fun f : continuousFields K ↦ L (continuousFieldInclusion hKU f))) := by
  refine ⟨V.continuousFirstVariation hV, ⟨V.continuousFirstVariation_eq_test hV, ?_⟩, ?_⟩
  · intro K hK hKU
    exact V.continuousFirstVariation_continuous_on_support hV hK hKU
  · intro L hL
    exact V.continuousFirstVariation_unique hV L hL.1 hL.2

/-- Zero extension identifies continuous compactly supported fields on
the actual open domain with ambient fields supported inside that domain. -/
def zeroExtendContinuousField (hU : IsOpen U) (f : C_c(U, Euclidean N)) :
    continuousFields U :=
  ⟨(⟨⟨Subtype.val.extend f 0,
      HasCompactSupport.continuous_extend_zero hU f.continuous f.hasCompactSupport⟩,
      f.hasCompactSupport.extend_zero continuous_subtype_val⟩ :
      C_c(Euclidean N, Euclidean N)).toBoundedContinuousFunction,
    f.hasCompactSupport.extend_zero continuous_subtype_val,
    (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)⟩

@[simp] theorem zeroExtendContinuousField_apply (hU : IsOpen U)
    (f : C_c(U, Euclidean N)) (x : U) :
    (zeroExtendContinuousField hU f).1 x = f x :=
  Subtype.val_injective.extend_apply f 0 x

theorem zeroExtendContinuousField_apply_of_notMem (hU : IsOpen U)
    (f : C_c(U, Euclidean N)) {x : Euclidean N} (hx : x ∉ U) :
    (zeroExtendContinuousField hU f).1 x = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, rfl⟩
  exact hx y.property

/-- Zero extension preserves the uniform norm, including for the empty
domain. -/
theorem zeroExtendContinuousField_norm (hU : IsOpen U)
    (f : C_c(U, Euclidean N)) :
    ‖zeroExtendContinuousField hU f‖ = ‖f.toBoundedContinuousFunction‖ := by
  apply le_antisymm
  · apply BoundedContinuousFunction.norm_le (norm_nonneg _) |>.mpr
    intro x
    by_cases hx : x ∈ U
    · change ‖(zeroExtendContinuousField hU f).1 (⟨x, hx⟩ : U)‖ ≤ _
      rw [zeroExtendContinuousField_apply]
      exact f.toBoundedContinuousFunction.norm_coe_le_norm ⟨x, hx⟩
    · change ‖(zeroExtendContinuousField hU f).1 x‖ ≤ _
      rw [zeroExtendContinuousField_apply_of_notMem hU f hx, norm_zero]
      exact norm_nonneg _
  · apply BoundedContinuousFunction.norm_le (norm_nonneg _) |>.mpr
    intro x
    change ‖f x‖ ≤ _
    rw [← zeroExtendContinuousField_apply hU f x]
    exact (zeroExtendContinuousField hU f).1.norm_coe_le_norm x

/-- Restriction to the domain preserves compact support because the
ambient support is a compact subset of that domain. -/
def restrictContinuousField (f : continuousFields U) : C_c(U, Euclidean N) where
  toFun x := f.1 x
  continuous_toFun := f.1.continuous.comp continuous_subtype_val
  hasCompactSupport' := by
    have hK : IsCompact ((Subtype.val : U → Euclidean N) ⁻¹' tsupport f.1) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' f.2.1 (by simpa using f.2.2)
    exact hK.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset_preimage f.1 continuous_subtype_val)

/-- The linear identification with the literal space `C_c(U; ℝᴺ)` used
by the Riesz representation theorem. -/
def domainContinuousFieldEquiv (hU : IsOpen U) :
    C_c(U, Euclidean N) ≃ₗ[ℝ] continuousFields U where
  toFun := zeroExtendContinuousField hU
  invFun := restrictContinuousField
  left_inv f := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    exact zeroExtendContinuousField_apply hU f x
  right_inv f := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    by_cases hx : x ∈ U
    · exact zeroExtendContinuousField_apply hU (restrictContinuousField f) ⟨x, hx⟩
    · rw [zeroExtendContinuousField_apply_of_notMem hU _ hx]
      exact (image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (f.2.2 hs))).symm
  map_add' f g := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    by_cases hx : x ∈ U
    · change (zeroExtendContinuousField hU (f + g)).1 (⟨x, hx⟩ : U) =
      (zeroExtendContinuousField hU f).1 (⟨x, hx⟩ : U) +
          (zeroExtendContinuousField hU g).1 (⟨x, hx⟩ : U)
      rw [zeroExtendContinuousField_apply hU (f + g) ⟨x, hx⟩,
        zeroExtendContinuousField_apply hU f ⟨x, hx⟩,
        zeroExtendContinuousField_apply hU g ⟨x, hx⟩]
      rfl
    · change (zeroExtendContinuousField hU (f + g)).1 x =
        (zeroExtendContinuousField hU f).1 x + (zeroExtendContinuousField hU g).1 x
      simp only [zeroExtendContinuousField_apply_of_notMem hU _ hx, add_zero]
  map_smul' c f := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro x
    by_cases hx : x ∈ U
    · change (zeroExtendContinuousField hU (c • f)).1 (⟨x, hx⟩ : U) =
        c • (zeroExtendContinuousField hU f).1 (⟨x, hx⟩ : U)
      rw [zeroExtendContinuousField_apply hU (c • f) ⟨x, hx⟩,
        zeroExtendContinuousField_apply hU f ⟨x, hx⟩]
      rfl
    · change (zeroExtendContinuousField hU (c • f)).1 x =
        c • (zeroExtendContinuousField hU f).1 x
      simp only [zeroExtendContinuousField_apply_of_notMem hU _ hx, smul_zero]

/-- The actual real-linear functional on `C_c(U; ℝᴺ)` constructed from
locally bounded first variation. The domain is `U` itself, so no behavior
at its boundary or finite global variation is imposed. -/
def domainContinuousFirstVariation (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) : C_c(U, Euclidean N) →ₗ[ℝ] ℝ :=
  (V.continuousFirstVariation hV).comp
    (domainContinuousFieldEquiv V.isOpen_domain).toLinearMap

theorem domainContinuousFirstVariation_eq_test (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (X : TestVectorField (N := N) U) :
    V.domainContinuousFirstVariation hV (restrictContinuousField X.toContinuousField) =
      V.firstVariation X := by
  change V.continuousFirstVariation hV
    (domainContinuousFieldEquiv V.isOpen_domain
      ((domainContinuousFieldEquiv V.isOpen_domain).symm X.toContinuousField)) = _
  rw [LinearEquiv.apply_symm_apply, V.continuousFirstVariation_eq_test hV]

/-- On the literal domain space `C_c(U; ℝᴺ)`, the constructed functional
has the local uniform-norm bounds required by vector Riesz representation.
This conclusion follows directly from the source hypothesis on `δV`. -/
theorem domainContinuousFirstVariation_local_bound (V : Varifold N n U)
    (hV : V.HasLocallyBoundedFirstVariation) (K : Set U) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : C_c(U, Euclidean N), tsupport f ⊆ K →
      |V.domainContinuousFirstVariation hV f| ≤ C * ‖f.toBoundedContinuousFunction‖ := by
  let W : Set (Euclidean N) := Subtype.val '' K
  have hWU : W ⊆ U := Subtype.coe_image_subset _ _
  have hfin := hV.finite_on_compact (hK.image continuous_subtype_val) hWU
  refine ⟨(V.firstVariationNormOn W).toReal, ENNReal.toReal_nonneg, fun f hf ↦ ?_⟩
  have hsupport : tsupport (zeroExtendContinuousField V.isOpen_domain f).1 ⊆ W :=
    (f.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans (image_mono hf)
  have hb := V.continuousFirstVariation_norm_bound hV hWU hfin
    (zeroExtendContinuousField V.isOpen_domain f) hsupport
  rw [zeroExtendContinuousField_norm] at hb
  exact hb

end
end Poincare.SimonGMT.Chapter08.Varifold
