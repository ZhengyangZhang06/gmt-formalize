module

public import Poincare.SimonGMT.Chapter06.Forms
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Order.Hom.PowersetCard

@[expose] public section

open Function

namespace Poincare.SimonGMT.Chapter06

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Simon (6.1.2): the strictly increasing multi-indices of length `n` with
values among `p` coordinate indices. -/
abbrev SimonMultiIndex (n p : ℕ) := Fin n ↪o Fin p

/-- Simon (6.1.2): there are `p.choose n` increasing multi-indices. -/
theorem card_simonMultiIndex (n p : ℕ) :
    Nat.card (SimonMultiIndex n p) = Nat.choose p n := by
  rw [Nat.card_congr Set.powersetCard.ofFinEmbEquiv,
    Set.powersetCard.card, Nat.card_fin]

/-- The finite-dimensional dual realization of Simon's space of `n`-vectors. -/
abbrev NVector (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :=
  Covector E n →L[ℝ] ℝ

/-- Simon (6.1.7): the canonical pairing of an `n`-covector and an `n`-vector. -/
def covectorNVectorPairing {n : ℕ} (omega : Covector E n) (w : NVector E n) : ℝ :=
  w omega

/-- Simon (6.1.8): pullback of an `n`-covector by a linear map. -/
def covectorPullback {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (L : E →L[ℝ] F) : Covector F n →L[ℝ] Covector E n :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM L

@[simp] theorem covectorPullback_apply
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (L : E →L[ℝ] F) (omega : Covector F n) (w : Fin n → E) :
    covectorPullback n L omega w = omega (L ∘ w) :=
  rfl

@[simp] theorem covectorPullback_id (n : ℕ) :
    covectorPullback n (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ (Covector E n) := by
  ext omega v
  rfl

theorem covectorPullback_comp
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (L : E →L[ℝ] F) (K : F →L[ℝ] G) :
    covectorPullback n (K.comp L) =
      (covectorPullback n L).comp (covectorPullback n K) := by
  ext omega v
  rfl

/-- Simon (6.1.9): pushforward of an `n`-vector, defined by duality. -/
def nVectorPushforward {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (L : E →L[ℝ] F) (w : NVector E n) : NVector F n :=
  w.comp (covectorPullback n L)

@[simp] theorem nVectorPushforward_id (n : ℕ) (w : NVector E n) :
    nVectorPushforward n (ContinuousLinearMap.id ℝ E) w = w := by
  ext omega
  rfl

theorem nVectorPushforward_comp
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (L : E →L[ℝ] F) (K : F →L[ℝ] G) (w : NVector E n) :
    nVectorPushforward n (K.comp L) w =
      nVectorPushforward n K (nVectorPushforward n L w) := by
  ext omega
  rfl

/-- The defining duality identity (6.1.9). -/
@[simp] theorem pairing_pullback_eq_pairing_pushforward
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (L : E →L[ℝ] F) (omega : Covector F n) (w : NVector E n) :
    covectorNVectorPairing (covectorPullback n L omega) w =
      covectorNVectorPairing omega (nVectorPushforward n L w) :=
  rfl

/-- The simple `n`-vector `v₁ ∧ ⋯ ∧ vₙ`, represented by evaluation on
`n`-covectors. -/
def simpleNVector {n : ℕ} (v : Fin n → E) : NVector E n :=
  (({
    toFun := fun omega : Covector E n ↦ omega v
    map_add' := by intro; simp
    map_smul' := by intro; simp
  } : Covector E n →ₗ[ℝ] ℝ).mkContinuous (∏ i, ‖v i‖) (fun omega ↦ by
    simpa [mul_comm] using ContinuousAlternatingMap.le_opNorm omega v))

@[simp] theorem simpleNVector_apply {n : ℕ} (v : Fin n → E) (omega : Covector E n) :
    simpleNVector v omega = omega v :=
  rfl

/-- Simon (6.1.10), vector half: pushforward sends a decomposable vector to
the wedge of the pushed-forward factors. -/
theorem nVectorPushforward_simple
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (L : E →L[ℝ] F) (v : Fin n → E) :
    nVectorPushforward n L (simpleNVector v) = simpleNVector (L ∘ v) := by
  ext omega
  rfl

/-- Exterior product of a finite family of continuous one-covectors. -/
def wedgeCovectors : ∀ n : ℕ, (Fin n → (E →L[ℝ] ℝ)) → Covector E n
  | 0, _ => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1
  | n + 1, alpha =>
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((alpha 0).smulRight (wedgeCovectors n (Fin.tail alpha)))

@[simp] theorem wedgeCovectors_zero (alpha : Fin 0 → (E →L[ℝ] ℝ)) :
    wedgeCovectors 0 alpha = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1 :=
  rfl

/-- Simon (6.1.1): the exterior product of one-covectors evaluates as the
determinant of their value matrix. -/
theorem wedgeCovectors_apply_det (n : ℕ) (alpha : Fin n → (E →L[ℝ] ℝ))
    (v : Fin n → E) :
    wedgeCovectors n alpha v =
      Matrix.det (Matrix.of fun i j ↦ alpha i (v j)) := by
  induction n with
  | zero =>
      simp [wedgeCovectors, Matrix.det_fin_zero]
  | succ n ih =>
      rw [Matrix.det_succ_row_zero]
      simp only [wedgeCovectors,
        ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        ContinuousLinearMap.smulRight_apply, zsmul_eq_mul,
        ContinuousAlternatingMap.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [ih]
      have hdet :
          Matrix.det (Matrix.of fun i k ↦ (Fin.tail alpha i) ((j.removeNth v) k)) =
            Matrix.det ((Matrix.of fun i k ↦ alpha i (v k)).submatrix
              Fin.succ j.succAbove) := by
        congr 1
      rw [hdet]
      simp [mul_assoc]

/-- Coefficient of an `n`-covector in the standard coordinate wedge basis. -/
def euclideanCovectorCoordinate {n p : ℕ}
    (omega : Covector (EuclideanSpace ℝ (Fin p)) n) (alpha : SimonMultiIndex n p) : ℝ :=
  omega (fun j ↦ EuclideanSpace.single (alpha j) 1)

/-- Simon (6.1.5): the coordinate inner product on Euclidean `n`-covectors. -/
def euclideanCovectorInner {n p : ℕ}
    (omega eta : Covector (EuclideanSpace ℝ (Fin p)) n) : ℝ :=
  ∑ alpha : SimonMultiIndex n p,
    euclideanCovectorCoordinate omega alpha * euclideanCovectorCoordinate eta alpha

@[simp] theorem euclideanCovectorInner_apply {n p : ℕ}
    (omega eta : Covector (EuclideanSpace ℝ (Fin p)) n) :
    euclideanCovectorInner omega eta =
      ∑ alpha : SimonMultiIndex n p,
        euclideanCovectorCoordinate omega alpha *
          euclideanCovectorCoordinate eta alpha :=
  rfl

/-- Coefficient of an `n`-vector in the standard coordinate wedge basis. -/
def euclideanNVectorCoordinate {n p : ℕ}
    (w : NVector (EuclideanSpace ℝ (Fin p)) n) (alpha : SimonMultiIndex n p) : ℝ :=
  w (wedgeCovectors n (fun j ↦ EuclideanSpace.proj (alpha j)))

/-- Simon (6.1.6): the coordinate inner product on Euclidean `n`-vectors. -/
def euclideanNVectorInner {n p : ℕ}
    (u w : NVector (EuclideanSpace ℝ (Fin p)) n) : ℝ :=
  ∑ alpha : SimonMultiIndex n p,
    euclideanNVectorCoordinate u alpha * euclideanNVectorCoordinate w alpha

@[simp] theorem euclideanNVectorInner_apply {n p : ℕ}
    (u w : NVector (EuclideanSpace ℝ (Fin p)) n) :
    euclideanNVectorInner u w =
      ∑ alpha : SimonMultiIndex n p,
        euclideanNVectorCoordinate u alpha *
          euclideanNVectorCoordinate w alpha :=
  rfl

/-- Simon (6.1.10), covector half: pullback commutes with the exterior product
of a finite family of one-covectors. -/
theorem covectorPullback_wedgeCovectors
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (L : E →L[ℝ] F) (alpha : Fin n → (F →L[ℝ] ℝ)) :
    covectorPullback n L (wedgeCovectors n alpha) =
      wedgeCovectors n (fun i ↦ (alpha i).comp L) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      ext w
      have htail :
          wedgeCovectors n (Fin.tail fun i => (alpha i).comp L) =
            covectorPullback n L (wedgeCovectors n (Fin.tail alpha)) := by
        rw [ih (Fin.tail alpha)]
        rfl
      simp only [wedgeCovectors]
      rw [htail]
      simp +unfoldPartialApp [covectorPullback_apply,
        ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
        Fin.removeNth, Function.comp_def]

section InnerProduct

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Simon (6.1.4): the covector dual to a vector under the real inner product. -/
def vectorCovector (v : H) : Covector H 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ H ℝ 0 (innerSL ℝ v)

@[simp] theorem vectorCovector_apply (v : H) (w : Fin 1 → H) :
    vectorCovector v w = inner ℝ v (w 0) :=
  rfl

end InnerProduct

end

end Poincare.SimonGMT.Chapter06
