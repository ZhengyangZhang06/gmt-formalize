module

public import Poincare.SimonGMT.Chapter08.FirstVariation
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Uniform bounds for the tangential-Jacobian calculation

These are the local domination estimates used in differentiating the integral
in Simon (8.2.2)--(8.2.3), printed pp. 208--209.
-/

open Set Filter Metric
open scoped Topology NNReal Matrix.Norms.Elementwise

namespace Poincare.SimonGMT.Chapter08

noncomputable section

/-- Determinant of the quadratic matrix occurring in the Gram expansion. -/
def quadraticMatrixDeterminant (n : ℕ)
    (z : ℝ × (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)) : ℝ :=
  (1 + z.1 • z.2.1 + z.1 ^ 2 • z.2.2).det

theorem contDiff_quadraticMatrixDeterminant (n : ℕ) :
    ContDiff ℝ 1 (quadraticMatrixDeterminant n) := by
  classical
  change ContDiff ℝ 1 (fun z : ℝ ×
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) ↦
      (1 + z.1 • z.2.1 + z.1 ^ 2 • z.2.2).det)
  simp_rw [Matrix.det_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  fun_prop

@[simp] theorem quadraticMatrixDeterminant_zero (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    quadraticMatrixDeterminant n (0, A, B) = 1 := by
  simp [quadraticMatrixDeterminant]

/-- A single neighborhood and Lipschitz constant control all the square-root
Gram determinants with bounded linear and quadratic coefficients.  The
constants are obtained by compactness, without any choice of a continuous
orthonormal basis on the Grassmannian. -/
theorem exists_uniform_lipschitzOnWith_sqrt_quadraticMatrixDeterminant
    (n : ℕ) (M : ℝ) :
    ∃ (ε : ℝ) (C : ℝ≥0), 0 < ε ∧
      ∀ A B : Matrix (Fin n) (Fin n) ℝ, ‖A‖ ≤ M → ‖B‖ ≤ M →
        LipschitzOnWith C
          (fun t ↦ Real.sqrt (quadraticMatrixDeterminant n (t, A, B)))
          (ball 0 ε) := by
  let K : Set (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) :=
    closedBall 0 M ×ˢ closedBall 0 M
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ p ∈ K,
      quadraticMatrixDeterminant n (t, p) ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro p hp
    exact (contDiff_quadraticMatrixDeterminant n).continuous.continuousAt.eventually_ne
      (by simp [quadraticMatrixDeterminant])
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnear
  let T : Set (ℝ × (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ)) :=
    closedBall 0 (ε / 2) ×ˢ K
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hK
  have hTconv : Convex ℝ T :=
    (convex_closedBall (0 : ℝ) (ε / 2)).prod
      ((convex_closedBall _ M).prod (convex_closedBall _ M))
  have hsqrt : ContDiffOn ℝ 1
      (fun z ↦ Real.sqrt (quadraticMatrixDeterminant n z)) T := by
    apply (contDiff_quadraticMatrixDeterminant n).contDiffOn.sqrt
    intro z hz
    apply hεsub ?_ z.2 hz.2
    exact (mem_closedBall.mp hz.1).trans_lt (by linarith)
  obtain ⟨C, hC⟩ := hsqrt.exists_lipschitzOnWith one_ne_zero hTconv hT
  refine ⟨ε / 2, C, by positivity, ?_⟩
  intro A B hA hB
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  have hp : (A, B) ∈ K := by
    simpa [K, mem_closedBall, dist_zero_right] using And.intro hA hB
  have hdist := hC.dist_le_mul
    (t, A, B) ⟨mem_closedBall.mpr (le_of_lt ht), hp⟩
    (s, A, B) ⟨mem_closedBall.mpr (le_of_lt hs), hp⟩
  simpa only [dist_prod_same_right] using hdist

namespace Varifold

variable {N n : ℕ}

/-- Linear term in the Gram matrix of `D(id + t X)|S`, in the basis `b`. -/
def linearDeformationGram (X : Euclidean N → Euclidean N) (x : Euclidean N)
    (S : Grassmannian N n) (b : OrthonormalBasis (Fin n) ℝ S.plane) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦
  inner ℝ ((fderiv ℝ X x) (b i : Euclidean N)) (b j : Euclidean N) +
    inner ℝ (b i : Euclidean N) ((fderiv ℝ X x) (b j : Euclidean N))

/-- Quadratic term in the Gram matrix of `D(id + t X)|S`, in the basis `b`. -/
def quadraticDeformationGram (X : Euclidean N → Euclidean N) (x : Euclidean N)
    (S : Grassmannian N n) (b : OrthonormalBasis (Fin n) ℝ S.plane) :
    Matrix (Fin n) (Fin n) ℝ := fun i j ↦
  inner ℝ ((fderiv ℝ X x) (b i : Euclidean N))
    ((fderiv ℝ X x) (b j : Euclidean N))

/-- Exact square-root Gram formula for the affine variation in Simon (8.2.3).
It holds for every orthonormal basis of the plane. -/
theorem tangentialJacobianReal_id_add_smul_eq_sqrt_quadraticMatrixDeterminant
    (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
    (b : OrthonormalBasis (Fin n) ℝ S.plane) (hX : DifferentiableAt ℝ X x) (t : ℝ) :
    tangentialJacobianReal (fun y ↦ y + t • X y) x S =
      Real.sqrt (quadraticMatrixDeterminant n
        (t, linearDeformationGram X x S b, quadraticDeformationGram X x S b)) := by
  have hflow : tangentialDerivative (fun y ↦ y + t • X y) x S =
      S.plane.subtype + t • (fderiv ℝ X x).toLinearMap.domRestrict S.plane := by
    apply LinearMap.ext
    intro v
    change (fderiv ℝ (id + t • X) x) (v : Euclidean N) = _
    rw [((hasFDerivAt_id x).add (hX.hasFDerivAt.const_smul t)).fderiv]
    rfl
  have hsquare : tangentialJacobianReal (fun y ↦ y + t • X y) x S ^ 2 =
      quadraticMatrixDeterminant n
        (t, linearDeformationGram X x S b, quadraticDeformationGram X x S b) := by
    have hg : tangentialJacobianReal (fun y ↦ y + t • X y) x S ^ 2 =
        (Matrix.gram ℝ
          (fun i ↦ tangentialDerivative (fun y ↦ y + t • X y) x S (b i))).det := by
      simpa [tangentialJacobianReal] using LinearMap.normDet_sq_eq_det_gram
        (tangentialDerivative (fun y ↦ y + t • X y) x S) b
    rw [hg, quadraticMatrixDeterminant]
    congr 1
    ext i j
    rw [hflow]
    have hb : inner ℝ (b i : Euclidean N) (b j : Euclidean N) =
        if i = j then 1 else 0 := b.inner_eq_ite i j
    change inner ℝ
        ((b i : Euclidean N) + t • (fderiv ℝ X x) (b i : Euclidean N))
        ((b j : Euclidean N) + t • (fderiv ℝ X x) (b j : Euclidean N)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) i j +
        t * linearDeformationGram X x S b i j +
        t ^ 2 * quadraticDeformationGram X x S b i j
    simp [Matrix.one_apply, linearDeformationGram, quadraticDeformationGram,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb]
    ring
  rw [← hsquare, Real.sqrt_sq (tangentialJacobianReal_nonneg _ _ _)]

/-- A bound on `DX` bounds every linear Gram coefficient uniformly over all
planes and all their orthonormal bases. -/
theorem norm_linearDeformationGram_le
    (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
    (b : OrthonormalBasis (Fin n) ℝ S.plane) {M : ℝ}
    (hM : 0 ≤ M) (hDX : ‖fderiv ℝ X x‖ ≤ M) :
    ‖linearDeformationGram X x S b‖ ≤ 2 * M := by
  have hb (i : Fin n) : ‖(b i : Euclidean N)‖ = 1 := b.norm_eq_one i
  have hDb (i : Fin n) : ‖(fderiv ℝ X x) (b i : Euclidean N)‖ ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ X x‖ * ‖(b i : Euclidean N)‖ := (fderiv ℝ X x).le_opNorm _
      _ ≤ M := by simpa [hb] using hDX
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  calc
    _ ≤ ‖inner ℝ ((fderiv ℝ X x) (b i : Euclidean N)) (b j : Euclidean N)‖ +
        ‖inner ℝ (b i : Euclidean N) ((fderiv ℝ X x) (b j : Euclidean N))‖ :=
      norm_add_le _ _
    _ ≤ M + M := by
      apply add_le_add
      · exact (norm_inner_le_norm _ _).trans (by simpa [hb] using hDb i)
      · exact (norm_inner_le_norm _ _).trans (by simpa [hb] using hDb j)
    _ = 2 * M := by ring

/-- The quadratic Gram coefficient has the corresponding square bound. -/
theorem norm_quadraticDeformationGram_le
    (X : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n)
    (b : OrthonormalBasis (Fin n) ℝ S.plane) {M : ℝ}
    (hM : 0 ≤ M) (hDX : ‖fderiv ℝ X x‖ ≤ M) :
    ‖quadraticDeformationGram X x S b‖ ≤ M * M := by
  have hb (i : Fin n) : ‖(b i : Euclidean N)‖ = 1 := b.norm_eq_one i
  have hDb (i : Fin n) : ‖(fderiv ℝ X x) (b i : Euclidean N)‖ ≤ M := by
    calc
      _ ≤ ‖fderiv ℝ X x‖ * ‖(b i : Euclidean N)‖ := (fderiv ℝ X x).le_opNorm _
      _ ≤ M := by simpa [hb] using hDX
  apply (Matrix.norm_le_iff (mul_nonneg hM hM)).mpr
  intro i j
  exact (norm_inner_le_norm _ _).trans (mul_le_mul (hDb i) (hDb j) (norm_nonneg _) hM)

/-- The domination needed in Simon's differentiation-under-the-integral
argument follows from a uniform bound on the derivative of the field. -/
theorem exists_uniform_lipschitzOnWith_tangentialJacobianReal_of_fderiv_le
    (X : Euclidean N → Euclidean N) (hX : Differentiable ℝ X)
    {M : ℝ} (hM : 0 ≤ M) (hDX : ∀ x, ‖fderiv ℝ X x‖ ≤ M) :
    ∃ (ε : ℝ) (C : ℝ≥0), 0 < ε ∧
      ∀ (x : Euclidean N) (S : Grassmannian N n), LipschitzOnWith C
        (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) x S) (ball 0 ε) := by
  obtain ⟨ε, C, hε, hC⟩ :=
    exists_uniform_lipschitzOnWith_sqrt_quadraticMatrixDeterminant n (max (2 * M) (M * M))
  refine ⟨ε, C, hε, ?_⟩
  intro x S
  let b : OrthonormalBasis (Fin n) ℝ S.plane :=
    (stdOrthonormalBasis ℝ S.plane).reindex (finCongr S.finrank_plane)
  have heq :
      (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) x S) =
      fun t ↦ Real.sqrt (quadraticMatrixDeterminant n
        (t, linearDeformationGram X x S b, quadraticDeformationGram X x S b)) := by
    funext t
    exact tangentialJacobianReal_id_add_smul_eq_sqrt_quadraticMatrixDeterminant
      X x S b (hX x) t
  rw [heq]
  exact hC _ _ ((norm_linearDeformationGram_le X x S b hM (hDX x)).trans (le_max_left _ _))
    ((norm_quadraticDeformationGram_le X x S b hM (hDX x)).trans (le_max_right _ _))

/-- Compact support and `C¹` regularity provide all the uniform Lipschitz
domination hypotheses for the affine variation, simultaneously for every
point and every plane. -/
theorem exists_uniform_lipschitzOnWith_tangentialJacobianReal
    (X : Euclidean N → Euclidean N) (hX : ContDiff ℝ 1 X)
    (hXcompact : HasCompactSupport X) :
    ∃ (ε : ℝ) (C : ℝ≥0), 0 < ε ∧
      ∀ (x : Euclidean N) (S : Grassmannian N n), LipschitzOnWith C
        (fun t : ℝ ↦ tangentialJacobianReal (fun y ↦ y + t • X y) x S) (ball 0 ε) := by
  obtain ⟨M, hM⟩ := (hXcompact.fderiv ℝ).exists_bound_of_continuous
    (hX.continuous_fderiv (by norm_num))
  exact exists_uniform_lipschitzOnWith_tangentialJacobianReal_of_fderiv_le X
    hX.differentiable_one (le_max_right M 0) (fun x ↦ (hM x).trans (le_max_left M 0))

end Varifold

end

end Poincare.SimonGMT.Chapter08
