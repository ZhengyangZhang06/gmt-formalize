module

public import Poincare.SimonGMT.Chapter08.ConstancyChartLocalIntegrability
public import Poincare.SimonGMT.Chapter08.ConstancyNormalCharts
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# Regularity and cutoff infrastructure for tangent coordinate tests

The actual metric Jacobian of a regular `C²` chart is `C¹`. A scalar
cutoff supported in a smoothness domain globalizes vector-valued `C¹`
fields without any regularity outside that domain. These are prerequisites
for constructing arbitrary supported tangent coordinate tests.

The normalization is not used or altered here. The coordinate test-field
extension and the Jacobian-weighted tangential-divergence identity are not
asserted here.
-/

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Poincare.SimonGMT.Chapter08
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {N n : ℕ}

/-- The actual metric Jacobian is `C¹` on a regular `C²` chart. The
Gram determinant is differentiated as a finite polynomial and its square
root is smooth because injectivity makes it strictly positive. -/
theorem contDiffOn_areaJacobianAt_simonChart
    {M W : Set (Euclidean N)} {D : Set (Euclidean n)}
    {φ : Euclidean n → Euclidean N}
    (hφ : Chapter02.IsSimonLocalRepresentation 2 M D W φ) :
    ContDiffOn ℝ 1 (Chapter02.areaJacobianAt φ) D := by
  classical
  let b : OrthonormalBasis (Fin n) ℝ (Euclidean n) :=
    (stdOrthonormalBasis ℝ (Euclidean n)).reindex (finCongr (by simp))
  let G : Euclidean n → Matrix (Fin n) (Fin n) ℝ :=
    fun u ↦ Matrix.gram ℝ (fun i ↦ fderiv ℝ φ u (b i))
  have hd : ContDiffOn ℝ 1 (fderiv ℝ φ) D :=
    hφ.contDiffOn.fderiv_of_isOpen hφ.isOpen_source (by norm_num)
  have hg : ∀ i j, ContDiffOn ℝ 1 (fun u ↦ G u i j) D := by
    intro i j
    exact (hd.clm_apply contDiffOn_const).inner ℝ (hd.clm_apply contDiffOn_const)
  have hdet : ContDiffOn ℝ 1 (fun u ↦ (G u).det) D := by
    simp only [Matrix.det_apply]
    apply ContDiffOn.sum
    intro σ hσ
    apply ContDiffOn.const_smul
    apply contDiffOn_prod
    intro i hi
    exact hg (σ i) i
  have hsquare (u : Euclidean n) : Chapter02.areaJacobianAt φ u ^ 2 = (G u).det := by
    rw [Chapter02.areaJacobianAt_eq_normDet]
    simpa [G] using (fderiv ℝ φ u).toLinearMap.normDet_sq_eq_det_gram b
  have heq : Chapter02.areaJacobianAt φ = fun u ↦ Real.sqrt ((G u).det) := by
    funext u
    rw [← hsquare, Real.sqrt_sq (Chapter02.areaJacobianAt_nonneg φ u)]
  rw [heq]
  apply hdet.sqrt
  intro u hu
  rw [← hsquare]
  exact pow_ne_zero _ (areaJacobianAt_pos_simonChart hφ hu).ne'

/-- A scalar cutoff supported inside a smoothness domain globalizes a
vector-valued `C¹` field. No regularity outside that domain is assumed. -/
theorem contDiff_cutoff_smul_of_contDiffOn
    {B : Set (Euclidean N)} {F : Euclidean N → Euclidean N} {γ : Euclidean N → ℝ}
    (hB : IsOpen B) (hF : ContDiffOn ℝ 1 F B) (hγ : ContDiff ℝ 1 γ)
    (hγB : tsupport γ ⊆ B) : ContDiff ℝ 1 (fun y ↦ γ y • F y) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ B
  · exact hγ.contDiffAt.smul ((hF y hy).contDiffAt (hB.mem_nhds hy))
  · have hyγ : y ∉ tsupport γ := fun ht ↦ hy (hγB ht)
    apply (show ContDiffAt ℝ 1 (fun _ : Euclidean N ↦ (0 : Euclidean N)) y from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hyγ] with z hz
    simp only [Pi.zero_apply] at hz
    simp only [hz, zero_smul]

end
end Poincare.SimonGMT.Chapter08
