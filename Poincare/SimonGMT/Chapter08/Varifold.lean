module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-!
# Simon GMT, Chapter 8: general varifolds

We realize an unoriented plane by its orthogonal projection matrix.  Thus the
Grassmannian is a concrete closed-condition subtype of a finite-dimensional
matrix space, and an `n`-varifold is genuinely a measure on the product of
Euclidean space with that Grassmannian.  Finiteness is required only on
compact cylinders contained in the open domain `U`.  The ambient measure is
the zero extension of the genuine Radon measure `domainMeasure` on
`U × G(N,n)`; infinite mass accumulating at the boundary of `U` is allowed.

The file also defines weight, mass, tangential divergence, first variation,
and stationarity (printed pp. 208--210).
-/

open scoped ENNReal Topology Matrix.Norms.Elementwise
open Set MeasureTheory Matrix Function

namespace Poincare.SimonGMT.Chapter08

/-- Ambient Euclidean coordinate space `ℝ^N`, carrying its Euclidean norm and
inner product rather than the sup norm on an unbundled function space. -/
abbrev Euclidean (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The projection-matrix realization of `G(N,n)`.

A real matrix is the orthogonal projection onto an `n`-plane exactly when it
is symmetric, idempotent, and has trace `n`. -/
abbrev Grassmannian (N n : ℕ) :=
  {P : Matrix (Fin N) (Fin N) ℝ //
    P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)}

namespace Grassmannian

variable {N n : ℕ}

@[simp] theorem symmetric (S : Grassmannian N n) : S.1.IsSymm := S.2.1

@[simp] theorem idempotent (S : Grassmannian N n) : S.1 * S.1 = S.1 := S.2.2.1

@[simp] theorem trace_eq (S : Grassmannian N n) : S.1.trace = (n : ℝ) := S.2.2.2

/-- The standard orthonormal coordinate basis of the ambient Euclidean
space. -/
noncomputable abbrev coordinateBasis :
    OrthonormalBasis (Fin N) ℝ (Euclidean N) :=
  EuclideanSpace.basisFun (Fin N) ℝ

/-- The orthogonal-projection endomorphism represented by a point of the
Grassmannian. -/
noncomputable def projectionLinearMap (S : Grassmannian N n) :
    Euclidean N →ₗ[ℝ] Euclidean N :=
  (LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis).symm S.1

@[simp] theorem toMatrix_projectionLinearMap (S : Grassmannian N n) :
    LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis
      S.projectionLinearMap = S.1 := by
  simp [projectionLinearMap]

theorem projectionLinearMap_comp_self (S : Grassmannian N n) :
    S.projectionLinearMap.comp S.projectionLinearMap = S.projectionLinearMap := by
  apply (LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis).injective
  rw [LinearMap.toMatrix_comp coordinateBasis.toBasis coordinateBasis.toBasis
    coordinateBasis.toBasis]
  simpa using S.idempotent

theorem projectionLinearMap_isSymmetric (S : Grassmannian N n) :
    S.projectionLinearMap.IsSymmetric := by
  apply (LinearMap.isHermitian_toMatrix_iff coordinateBasis).mp
  rw [Matrix.isHermitian_iff_isSymm]
  simpa using S.symmetric

/-- Orthogonal projection of a vector onto the represented plane. -/
noncomputable def project (S : Grassmannian N n) (x : Euclidean N) : Euclidean N :=
  S.projectionLinearMap x

@[simp] theorem project_project (S : Grassmannian N n) (x : Euclidean N) :
    S.project (S.project x) = S.project x := by
  exact LinearMap.congr_fun S.projectionLinearMap_comp_self x

/-- The `n`-plane represented by an orthogonal projection matrix. -/
noncomputable def plane (S : Grassmannian N n) : Submodule ℝ (Euclidean N) :=
  LinearMap.range S.projectionLinearMap

theorem projectionLinearMap_apply_of_mem (S : Grassmannian N n)
    {x : Euclidean N} (hx : x ∈ S.plane) : S.projectionLinearMap x = x := by
  obtain ⟨y, rfl⟩ := hx
  exact LinearMap.congr_fun S.projectionLinearMap_comp_self y

/-- Orthogonal projection with codomain restricted to the represented plane. -/
noncomputable def planeProjection (S : Grassmannian N n) :
    Euclidean N →ₗ[ℝ] S.plane :=
  S.projectionLinearMap.rangeRestrict

theorem finrank_plane (S : Grassmannian N n) :
    Module.finrank ℝ S.plane = n := by
  have hidem : IsIdempotentElem S.projectionLinearMap := by
    change S.projectionLinearMap * S.projectionLinearMap = S.projectionLinearMap
    apply (LinearMap.toMatrix coordinateBasis.toBasis
      coordinateBasis.toBasis).injective
    rw [LinearMap.toMatrix_mul]
    simpa using S.idempotent
  have htrace : LinearMap.trace ℝ (Euclidean N) S.projectionLinearMap = (n : ℝ) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ coordinateBasis.toBasis]
    simpa using S.trace_eq
  have hrank := (LinearMap.IsIdempotentElem.isProj_range _ hidem).trace
  rw [htrace] at hrank
  exact_mod_cast hrank.symm

/-- The projection-matrix point corresponding to an `n`-dimensional linear
subspace. -/
noncomputable def ofSubmodule (L : Submodule ℝ (Euclidean N))
    (hL : Module.finrank ℝ L = n) : Grassmannian N n := by
  let p : Euclidean N →ₗ[ℝ] Euclidean N := L.starProjection
  let P := LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis p
  refine ⟨P, ?_, ?_, ?_⟩
  · exact ((LinearMap.isHermitian_toMatrix_iff coordinateBasis).2
      L.starProjection_isSymmetric).isSymm
  · rw [← LinearMap.toMatrix_comp]
    apply congrArg (LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis)
    apply LinearMap.ext
    intro x
    exact Submodule.starProjection_eq_self_iff.mpr <| by
      change (L.orthogonalProjectionOnto x : Euclidean N) ∈ L
      exact Submodule.coe_mem _
  · rw [← LinearMap.trace_eq_matrix_trace ℝ coordinateBasis.toBasis]
    have hidem : IsIdempotentElem p := by
      change p * p = p
      apply LinearMap.ext
      intro x
      exact Submodule.starProjection_eq_self_iff.mpr <| by
        change (L.orthogonalProjectionOnto x : Euclidean N) ∈ L
        exact Submodule.coe_mem _
    rw [(LinearMap.IsIdempotentElem.isProj_range _ hidem).trace]
    have hrange : LinearMap.range p = L := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        change L.starProjection y ∈ L
        change (L.orthogonalProjectionOnto y : Euclidean N) ∈ L
        exact Submodule.coe_mem _
      · intro hx
        refine ⟨x, ?_⟩
        exact Submodule.starProjection_eq_self_iff.mpr hx
    rw [hrange, hL]

@[simp] theorem plane_ofSubmodule (L : Submodule ℝ (Euclidean N))
    (hL : Module.finrank ℝ L = n) : (ofSubmodule L hL).plane = L := by
  let p : Euclidean N →ₗ[ℝ] Euclidean N := L.starProjection
  have hrange : LinearMap.range p = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change L.starProjection y ∈ L
      change (L.orthogonalProjectionOnto y : Euclidean N) ∈ L
      exact Submodule.coe_mem _
    · intro hx
      refine ⟨x, ?_⟩
      exact Submodule.starProjection_eq_self_iff.mpr hx
  change LinearMap.range
    ((LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis).symm
      (LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis p)) = L
  rw [LinearEquiv.symm_apply_apply, hrange]

@[simp] theorem ofSubmodule_plane (S : Grassmannian N n) :
    ofSubmodule S.plane S.finrank_plane = S := by
  have hidem : IsIdempotentElem S.projectionLinearMap := by
    change S.projectionLinearMap.comp S.projectionLinearMap = S.projectionLinearMap
    exact S.projectionLinearMap_comp_self
  have hsymmetricProjection : S.projectionLinearMap.IsSymmetricProjection :=
    ⟨hidem, S.projectionLinearMap_isSymmetric⟩
  obtain ⟨_, hp⟩ :=
    (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp
      hsymmetricProjection
  apply Subtype.ext
  change LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis
      (S.plane.starProjection : Euclidean N →ₗ[ℝ] Euclidean N) = S.1
  rw [← S.toMatrix_projectionLinearMap]
  apply congrArg (LinearMap.toMatrix coordinateBasis.toBasis coordinateBasis.toBasis)
  exact hp.symm

/-- The squared Frobenius norm of an orthogonal projection is its rank. -/
theorem sum_sq_eq_rank (S : Grassmannian N n) :
    (∑ i, ∑ j, (S.1 i j) ^ 2) = (n : ℝ) := by
  calc
    (∑ i, ∑ j, (S.1 i j) ^ 2) = ∑ i, ∑ j, S.1 i j * S.1 j i := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [S.symmetric.apply i j]
      ring
    _ = Matrix.trace (S.1 * S.1) := by
      rfl
    _ = (n : ℝ) := by rw [S.idempotent, S.trace_eq]

theorem entry_sq_le_rank (S : Grassmannian N n) (i j : Fin N) :
    (S.1 i j) ^ 2 ≤ (n : ℝ) := by
  calc
    (S.1 i j) ^ 2 ≤ ∑ j', (S.1 i j') ^ 2 :=
      Finset.single_le_sum (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', (S.1 i' j') ^ 2 :=
      Finset.single_le_sum
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i)
    _ = (n : ℝ) := S.sum_sq_eq_rank

theorem entry_norm_le_sqrt_rank (S : Grassmannian N n) (i j : Fin N) :
    ‖S.1 i j‖ ≤ Real.sqrt n := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  simpa [Real.norm_eq_abs, sq_abs] using S.entry_sq_le_rank i j

theorem norm_le_sqrt_rank (S : Grassmannian N n) : ‖S.1‖ ≤ Real.sqrt n := by
  apply (Matrix.norm_le_iff (Real.sqrt_nonneg _)).2
  exact S.entry_norm_le_sqrt_rank

theorem isClosed_projectionSet : IsClosed
    {P : Matrix (Fin N) (Fin N) ℝ |
      P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)} := by
  have hs : IsClosed {P : Matrix (Fin N) (Fin N) ℝ | P.IsSymm} := by
    change IsClosed {P : Matrix (Fin N) (Fin N) ℝ | P.transpose = P}
    exact isClosed_eq continuous_id.matrix_transpose continuous_id
  have hi : IsClosed {P : Matrix (Fin N) (Fin N) ℝ | P * P = P} :=
    isClosed_eq (continuous_id.mul continuous_id) continuous_id
  have ht : IsClosed {P : Matrix (Fin N) (Fin N) ℝ | P.trace = (n : ℝ)} :=
    isClosed_eq continuous_id.matrix_trace continuous_const
  exact hs.inter (hi.inter ht)

theorem isBounded_projectionSet : Bornology.IsBounded
    {P : Matrix (Fin N) (Fin N) ℝ |
      P.IsSymm ∧ P * P = P ∧ P.trace = (n : ℝ)} := by
  let _ : NormedAddCommGroup (Matrix (Fin N) (Fin N) ℝ) :=
    Matrix.normedAddCommGroup
  apply (isBounded_iff_forall_norm_le
    (E := Matrix (Fin N) (Fin N) ℝ)).2
  refine ⟨Real.sqrt n, ?_⟩
  intro P hP
  exact norm_le_sqrt_rank ⟨P, hP⟩

noncomputable instance instCompactSpace : CompactSpace (Grassmannian N n) :=
  isCompact_iff_compactSpace.mp <|
    Metric.isCompact_of_isClosed_isBounded isClosed_projectionSet isBounded_projectionSet

instance instSecondCountableTopology : SecondCountableTopology (Grassmannian N n) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

end Grassmannian

/-- The rectangular determinant identity used to express a plane Jacobian
without making any basis choice depend on the plane. -/
theorem det_id_add_comp {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (A : F →ₗ[ℝ] E) (B : E →ₗ[ℝ] F) :
    (LinearMap.id + A.comp B).det = (LinearMap.id + B.comp A).det := by
  classical
  let bE := Module.finBasis ℝ E
  let bF := Module.finBasis ℝ F
  rw [← LinearMap.det_toMatrix bE, ← LinearMap.det_toMatrix bF]
  simp only [map_add, LinearMap.toMatrix_id,
    LinearMap.toMatrix_comp bE bF bE, LinearMap.toMatrix_comp bF bE bF]
  exact Matrix.det_one_add_mul_comm _ _

/-- Algebraic orthogonal-projection formula for the image of a plane under
a linear map that is nondegenerate on that plane. -/
theorem imageProjectionMatrix_properties (P L : Matrix (Fin N) (Fin N) ℝ)
    (hPs : P.IsSymm) (hPi : P * P = P)
    (hd : (1 - P + P * L.transpose * L * P).det ≠ 0) :
    let H := 1 - P + P * L.transpose * L * P
    let Q := L * P * H⁻¹ * P * L.transpose
    Q.IsSymm ∧ Q * Q = Q ∧ Q * (L * P) = L * P := by
  dsimp only
  let H := 1 - P + P * L.transpose * L * P
  let Q := L * P * H⁻¹ * P * L.transpose
  change Q.IsSymm ∧ Q * Q = Q ∧ Q * (L * P) = L * P
  have hH : H.IsSymm := by
    change H.transpose = H
    simp only [H, transpose_add, transpose_sub, transpose_one, transpose_mul,
      transpose_transpose, hPs.eq, Matrix.mul_assoc]
  have hQ : Q.IsSymm := by
    change Q.transpose = Q
    simp only [Q, transpose_mul, transpose_transpose, hPs.eq, hH.inv.eq,
      Matrix.mul_assoc]
  have hHP : H * P = P * L.transpose * L * P := by
    simp [H, sub_mul, add_mul, Matrix.mul_assoc, hPi]
  have hIH : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  have hQLP : Q * (L * P) = L * P := by
    calc
      Q * (L * P) = L * P * H⁻¹ * (P * L.transpose * L * P) := by
        simp only [Q, Matrix.mul_assoc]
      _ = L * P * H⁻¹ * (H * P) := by rw [hHP]
      _ = L * P * (H⁻¹ * H) * P := by simp only [Matrix.mul_assoc]
      _ = L * P := by rw [hIH, mul_one, Matrix.mul_assoc, hPi]
  refine ⟨hQ, ?_, hQLP⟩
  calc
    Q * Q = (Q * (L * P)) * (H⁻¹ * P * L.transpose) := by
      simp only [Q, Matrix.mul_assoc]
    _ = Q := by rw [hQLP]; simp only [Q, Matrix.mul_assoc]

/-- An `n`-varifold on the open domain `U` (Simon 8.1), represented by its
zero extension to the ambient product.  Only compact subsets of `U` are
required to have finite mass; no local finiteness at `∂U` is imposed. -/
structure Varifold (N n : ℕ) (U : Set (Euclidean N)) where
  isOpen_domain : IsOpen U
  measure : Measure (Euclidean N × Grassmannian N n)
  supported : measure (Uᶜ ×ˢ (Set.univ : Set (Grassmannian N n))) = 0
  finite_on_compact : ∀ K : Set (Euclidean N), IsCompact K → K ⊆ U →
    measure (K ×ˢ (Set.univ : Set (Grassmannian N n))) ≠ ∞

namespace Varifold

variable {N n : ℕ} {U W : Set (Euclidean N)}

/-- The measure on Simon's actual open product `Gₙ(U)`. -/
noncomputable def domainMeasure (V : Varifold N n U) :
    Measure (U ×ˢ (univ : Set (Grassmannian N n))) :=
  V.measure.comap Subtype.val

theorem domainMeasure_apply (V : Varifold N n U)
    (A : Set (U ×ˢ (univ : Set (Grassmannian N n)))) :
    V.domainMeasure A = V.measure (Subtype.val '' A) :=
  (MeasurableEmbedding.subtype_coe
    (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)).comap_apply _ _

/-- Local finiteness is on the open product, not on its ambient closure. -/
instance domainMeasure.instIsLocallyFiniteMeasure (V : Varifold N n U) :
    IsLocallyFiniteMeasure V.domainMeasure := by
  letI : LocallyCompactSpace (U ×ˢ (univ : Set (Grassmannian N n))) :=
    (V.isOpen_domain.prod isOpen_univ).locallyCompactSpace
  constructor
  intro z
  obtain ⟨C, hCcompact, hCnhds⟩ := exists_compact_mem_nhds z
  let K : Set (Euclidean N) := (fun w : U ×ˢ (univ : Set (Grassmannian N n)) ↦
    w.1.1) '' C
  have hKcompact : IsCompact K :=
    hCcompact.image (continuous_fst.comp continuous_subtype_val)
  have hKU : K ⊆ U := by rintro _ ⟨w, _, rfl⟩; exact w.2.1
  refine ⟨C, hCnhds, ?_⟩
  rw [V.domainMeasure_apply]
  apply (measure_mono ?_).trans_lt
    (lt_top_iff_ne_top.2 (V.finite_on_compact K hKcompact hKU))
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw, rfl⟩, Set.mem_univ _⟩

/-- The open-product measure is Radon: it is regular as well as locally
finite.  This follows from the metrizable, second-countable local model. -/
instance domainMeasure.instRegular (V : Varifold N n U) :
    Measure.Regular V.domainMeasure := by
  letI : LocallyCompactSpace (U ×ˢ (univ : Set (Grassmannian N n))) :=
    (V.isOpen_domain.prod isOpen_univ).locallyCompactSpace
  letI := domainMeasure.instIsLocallyFiniteMeasure V
  infer_instance

/-- Recovering the ambient zero extension from the source-domain measure. -/
theorem map_domainMeasure (V : Varifold N n U) :
    V.domainMeasure.map Subtype.val = V.measure := by
  rw [domainMeasure, map_comap_subtype_coe
    (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  have hcomp : {z : Euclidean N × Grassmannian N n | ¬z ∈ U ×ˢ univ} =
      Uᶜ ×ˢ univ := by ext z; simp
  rw [hcomp]
  exact V.supported

instance measure.instSigmaFinite (V : Varifold N n U) : SigmaFinite V.measure := by
  letI : LocallyCompactSpace (U ×ˢ (univ : Set (Grassmannian N n))) :=
    (V.isOpen_domain.prod isOpen_univ).locallyCompactSpace
  letI := domainMeasure.instIsLocallyFiniteMeasure V
  rw [← V.map_domainMeasure]
  exact (MeasurableEmbedding.subtype_coe
    (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)).sigmaFinite_map

/-- Every Radon measure on Simon's open product gives a varifold.  Together
with `map_domainMeasure` and `domainMeasure_ofDomainMeasure`, this proves
that the ambient representation excludes no source-domain measures. -/
noncomputable def ofDomainMeasure (hU : IsOpen U)
    (μ : Measure (U ×ˢ (univ : Set (Grassmannian N n))))
    [IsLocallyFiniteMeasure μ] : Varifold N n U where
  isOpen_domain := hU
  measure := μ.map Subtype.val
  supported := by
    rw [Measure.map_apply measurable_subtype_coe
      (hU.measurableSet.compl.prod MeasurableSet.univ)]
    have hempty : Subtype.val ⁻¹' (Uᶜ ×ˢ (univ : Set (Grassmannian N n))) =
        (∅ : Set (U ×ˢ (univ : Set (Grassmannian N n)))) := by
      ext z
      simp [z.2.1]
    rw [hempty, measure_empty]
  finite_on_compact := by
    intro K hK hKU
    rw [Measure.map_apply measurable_subtype_coe
      (hK.measurableSet.prod MeasurableSet.univ)]
    apply IsCompact.measure_ne_top
    apply Topology.IsInducing.subtypeVal.isCompact_preimage'
      (hK.prod isCompact_univ)
    rw [Subtype.range_val]
    exact prod_mono hKU Subset.rfl

@[simp] theorem domainMeasure_ofDomainMeasure (hU : IsOpen U)
    (μ : Measure (U ×ˢ (univ : Set (Grassmannian N n))))
    [IsLocallyFiniteMeasure μ] :
    (ofDomainMeasure hU μ).domainMeasure = μ := by
  exact (MeasurableEmbedding.subtype_coe
    (hU.measurableSet.prod MeasurableSet.univ)).comap_map _

/-- The derivative of `f` restricted to the plane `S`.  This is the linear
map denoted `dfₓ|S` in Simon 8.2.1. -/
noncomputable def tangentialDerivative (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) :
    S.plane →ₗ[ℝ] Euclidean N :=
  (fderiv ℝ f x).toLinearMap.domRestrict S.plane

/-- The tangential Jacobian `J_S f(x)` from Simon 8.2.1.  Mathlib's
`LinearMap.normDet` is precisely the square root of the Gram determinant of
`dfₓ|S`. -/
noncomputable def tangentialJacobianReal (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) : ℝ :=
  (tangentialDerivative f x S).normDet

noncomputable def tangentialJacobian (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) : ℝ≥0∞ :=
  ENNReal.ofReal (tangentialJacobianReal f x S)

@[simp] theorem tangentialDerivative_id (x : Euclidean N)
    (S : Grassmannian N n) :
    tangentialDerivative (fun y : Euclidean N ↦ y) x S = S.plane.subtype := by
  apply LinearMap.ext
  intro v
  simp [tangentialDerivative]

@[simp] theorem tangentialJacobianReal_id (x : Euclidean N)
    (S : Grassmannian N n) :
    tangentialJacobianReal (fun y : Euclidean N ↦ y) x S = 1 := by
  simp [tangentialJacobianReal]

@[simp] theorem tangentialJacobian_id (x : Euclidean N)
    (S : Grassmannian N n) :
    tangentialJacobian (fun y : Euclidean N ↦ y) x S = 1 := by
  simp [tangentialJacobian]

theorem tangentialJacobianReal_nonneg (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) :
    0 ≤ tangentialJacobianReal f x S :=
  LinearMap.normDet_nonneg _

theorem tangentialJacobian_ne_zero_iff (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) :
    tangentialJacobian f x S ≠ 0 ↔ tangentialJacobianReal f x S ≠ 0 := by
  rw [tangentialJacobian, Ne, ENNReal.ofReal_eq_zero, not_le]
  constructor
  · exact ne_of_gt
  · intro h
    exact lt_of_le_of_ne (tangentialJacobianReal_nonneg f x S) h.symm

/-- The image plane `dfₓ(S)` on the nondegenerate locus `J_S f(x) ≠ 0`.
Outside that locus its value is immaterial for pushforward measure because the
Jacobian density is zero, so we use `S` itself as a total extension. -/
noncomputable def transportedPlane (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) : Grassmannian N n :=
  if hJ : tangentialJacobianReal f x S ≠ 0 then
    Grassmannian.ofSubmodule (LinearMap.range (tangentialDerivative f x S)) <| by
      have hrank := ((tangentialDerivative f x S).normDet_ne_zero_tfae.out 1 3).mp hJ
      rw [Grassmannian.finrank_plane] at hrank
      exact hrank
  else S

@[simp] theorem transportedPlane_id (x : Euclidean N) (S : Grassmannian N n) :
    transportedPlane (fun y : Euclidean N ↦ y) x S = S := by
  simp [transportedPlane]

theorem transportedPlane_eq_image (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n)
    (hJ : tangentialJacobianReal f x S ≠ 0) :
    (transportedPlane f x S).plane =
      LinearMap.range (tangentialDerivative f x S) := by
  rw [transportedPlane, dif_pos hJ]
  exact Grassmannian.plane_ofSubmodule _ _

/-- The map `F(x,S) = (f(x), dfₓ(S))` in Simon 8.2.1, totalized on the
zero-Jacobian locus as explained in `transportedPlane`. -/
noncomputable def imageMap (f : Euclidean N → Euclidean N) :
    Euclidean N × Grassmannian N n → Euclidean N × Grassmannian N n :=
  fun z ↦ (f z.1, transportedPlane f z.1 z.2)

@[simp] theorem imageMap_id :
    imageMap (n := n) (fun y : Euclidean N ↦ y) = id := by
  funext z
  simp [imageMap]

/-- The weighted mapped measure in Simon (8.2.1).  The theorems below derive
image-map measurability from `C¹` regularity on `U` and compact finiteness
from properness on `spt μ_V ∩ U`, producing the varifold `pushforward`. -/
noncomputable def pushforwardMeasure (V : Varifold N n U)
    (f : Euclidean N → Euclidean N) :
    Measure (Euclidean N × Grassmannian N n) :=
  Measure.map (imageMap f)
    (V.measure.withDensity fun z ↦ tangentialJacobian f z.1 z.2)

/-- Exact evaluation formula (8.2.1) for the pushforward measure. -/
theorem pushforwardMeasure_apply (V : Varifold N n U)
    (f : Euclidean N → Euclidean N)
    (hF : Measurable (imageMap (n := n) f))
    {A : Set (Euclidean N × Grassmannian N n)} (hA : MeasurableSet A) :
    V.pushforwardMeasure f A =
      ∫⁻ z in imageMap (n := n) f ⁻¹' A,
        tangentialJacobian f z.1 z.2 ∂V.measure := by
  rw [pushforwardMeasure, Measure.map_apply hF hA,
    withDensity_apply _ (hA.preimage hF)]

/-- Total mass of the measure in (8.2.1). -/
theorem pushforwardMeasure_univ (V : Varifold N n U)
    (f : Euclidean N → Euclidean N)
    (hF : Measurable (imageMap (n := n) f)) :
    V.pushforwardMeasure f univ =
      ∫⁻ z, tangentialJacobian f z.1 z.2 ∂V.measure := by
  rw [V.pushforwardMeasure_apply f hF MeasurableSet.univ, preimage_univ,
    setLIntegral_univ]

@[simp] theorem pushforwardMeasure_id (V : Varifold N n U) :
    V.pushforwardMeasure (fun y : Euclidean N ↦ y) = V.measure := by
  simp [pushforwardMeasure]

/-- The weight measure `μ_V = π_# V`. -/
noncomputable def weight (V : Varifold N n U) : Measure (Euclidean N) :=
  V.measure.map Prod.fst

/-- The mass of `V` in a set `A`. -/
noncomputable def massOn (V : Varifold N n U) (A : Set (Euclidean N)) : ℝ≥0∞ :=
  V.weight A

/-- Evaluation of the weight measure on Borel sets. -/
theorem weight_apply (V : Varifold N n U) {A : Set (Euclidean N)} (hA : MeasurableSet A) :
    V.weight A = V.measure (A ×ˢ (Set.univ : Set (Grassmannian N n))) := by
  rw [weight, MeasureTheory.Measure.map_apply measurable_fst hA]
  congr 1
  ext z
  simp

theorem massOn_eq (V : Varifold N n U) {A : Set (Euclidean N)} (hA : MeasurableSet A) :
    V.massOn A = V.measure (A ×ˢ (Set.univ : Set (Grassmannian N n))) :=
  V.weight_apply hA

theorem weight_finite_on_compact (V : Varifold N n U) (K : Set (Euclidean N))
    (hK : IsCompact K) (hKU : K ⊆ U) : V.weight K ≠ ∞ := by
  rw [V.weight_apply hK.measurableSet]
  exact V.finite_on_compact K hK hKU

/-- Simon's weight measure on the open domain itself. -/
noncomputable def domainWeight (V : Varifold N n U) : Measure U :=
  V.weight.comap Subtype.val

theorem domainWeight_apply (V : Varifold N n U) (A : Set U) :
    V.domainWeight A = V.weight (Subtype.val '' A) :=
  (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).comap_apply _ _

instance domainWeight.instIsLocallyFiniteMeasure (V : Varifold N n U) :
    IsLocallyFiniteMeasure V.domainWeight := by
  letI : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  constructor
  intro x
  obtain ⟨K, hKcompact, hKnhds⟩ := exists_compact_mem_nhds x
  refine ⟨K, hKnhds, ?_⟩
  rw [V.domainWeight_apply]
  exact lt_top_iff_ne_top.2 (V.weight_finite_on_compact _
    (hKcompact.image continuous_subtype_val) (by rintro _ ⟨y, _, rfl⟩; exact y.2))

instance domainWeight.instRegular (V : Varifold N n U) :
    Measure.Regular V.domainWeight := by
  letI : LocallyCompactSpace U := V.isOpen_domain.locallyCompactSpace
  letI := domainWeight.instIsLocallyFiniteMeasure V
  infer_instance

theorem map_domainWeight (V : Varifold N n U) :
    V.domainWeight.map Subtype.val = V.weight := by
  rw [domainWeight, map_comap_subtype_coe V.isOpen_domain.measurableSet]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change V.weight Uᶜ = 0
  rw [V.weight_apply V.isOpen_domain.measurableSet.compl]
  exact V.supported

instance weight.instSigmaFinite (V : Varifold N n U) : SigmaFinite V.weight := by
  letI := domainWeight.instIsLocallyFiniteMeasure V
  rw [← V.map_domainWeight]
  exact (MeasurableEmbedding.subtype_coe V.isOpen_domain.measurableSet).sigmaFinite_map

/-- The source-domain projection, weight formula, and total mass from the
preamble to Simon Chapter 8. -/
def domainProjection : (U ×ˢ (univ : Set (Grassmannian N n))) → U :=
  fun z ↦ ⟨z.1.1, z.2.1⟩

theorem domainWeight_eq_map_domainMeasure (V : Varifold N n U) :
    V.domainWeight = V.domainMeasure.map domainProjection := by
  apply Measure.ext
  intro A hA
  have hp : Measurable (domainProjection (n := n) (U := U)) :=
    (measurable_fst.comp measurable_subtype_coe).subtype_mk
  rw [Measure.map_apply hp hA, V.domainMeasure_apply, V.domainWeight_apply,
    V.weight_apply ((MeasurableEmbedding.subtype_coe
      V.isOpen_domain.measurableSet).measurableSet_image.mpr hA)]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨x, hx, hxz⟩, _⟩
    exact ⟨⟨(x.1, z.2), x.2, mem_univ _⟩, hx, Prod.ext hxz rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨domainProjection y, hy, rfl⟩, mem_univ _⟩

theorem massOn_domain_eq (V : Varifold N n U) :
    V.massOn U = V.domainMeasure univ := by
  rw [V.massOn_eq V.isOpen_domain.measurableSet, V.domainMeasure_apply]
  rw [image_univ, Subtype.range_val]

/-- Coordinate Jacobian of a vector field. -/
noncomputable def clmToMatrix :
    ((Euclidean N →L[ℝ] Euclidean N) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ) :=
  (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin N) ℝ).toBasis).toLinearMap.comp
      (ContinuousLinearMap.coeLM ℝ)

noncomputable def jacobian (X : Euclidean N → Euclidean N) (x : Euclidean N) :
    Matrix (Fin N) (Fin N) ℝ :=
  clmToMatrix (fderiv ℝ X x)

theorem jacobian_eq_toMatrix (X : Euclidean N → Euclidean N) (x : Euclidean N) :
    jacobian X x =
      LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis (fderiv ℝ X x).toLinearMap := by
  rfl

theorem continuous_jacobian {X : Euclidean N → Euclidean N}
    (hX : ContDiff ℝ 1 X) : Continuous (jacobian X) := by
  exact (clmToMatrix.continuous_of_finiteDimensional).comp
    (hX.continuous_fderiv (by norm_num))

/-- The square of Simon's tangential Jacobian is an ambient determinant.
On the orthogonal complement of `S`, the displayed operator is the identity.
This formula also applies on the degenerate locus. -/
theorem tangentialJacobianReal_sq_eq_det_ambientGram
    (f : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n) :
    tangentialJacobianReal f x S ^ 2 =
      (1 - S.1 + S.1 * (jacobian f x).transpose * jacobian f x * S.1).det := by
  let L : Euclidean N →ₗ[ℝ] Euclidean N := (fderiv ℝ f x).toLinearMap
  let P := S.projectionLinearMap
  let i := S.plane.subtype
  let q := i.adjoint
  have hqi : q.comp i = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro w
    change inner ℝ w (i.adjoint (i v)) = inner ℝ w v
    rw [LinearMap.adjoint_inner_right]
    rfl
  have hiq : i.comp q = P := by
    apply LinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro w
    have hs := S.projectionLinearMap_isSymmetric
    have hproj := S.projectionLinearMap_apply_of_mem (q v).property
    calc
      inner ℝ w ((i.comp q) v) = inner ℝ w (P (q v)) :=
        congrArg (inner ℝ w) hproj.symm
      _ = inner ℝ (P w) ((i.comp q) v) := (hs w (q v)).symm
      _ = inner ℝ (⟨P w, ⟨w, rfl⟩⟩ : S.plane) (q v) := rfl
      _ = inner ℝ (P w) v := LinearMap.adjoint_inner_right i _ v
      _ = inner ℝ w (P v) := hs w v
  let B : Euclidean N →ₗ[ℝ] S.plane :=
    q.comp (L.adjoint.comp (L.comp P)) - q
  have hBi : LinearMap.id + B.comp i =
      (L.comp i).adjoint.comp (L.comp i) := by
    have hPi : P.comp i = i := by
      apply LinearMap.ext
      intro v
      exact S.projectionLinearMap_apply_of_mem v.property
    simp only [B, LinearMap.sub_comp, LinearMap.comp_assoc, hPi, hqi,
      LinearMap.adjoint_comp]
    module
  have hiB : LinearMap.id + i.comp B =
      LinearMap.id - P + P.comp (L.adjoint.comp (L.comp P)) := by
    simp only [B, LinearMap.comp_sub, ← LinearMap.comp_assoc, hiq]
    module
  calc
    tangentialJacobianReal f x S ^ 2 = ((L.comp i).adjoint.comp (L.comp i)).det := by
      change (L.comp i).normDet ^ 2 = _
      simpa using (L.comp i).normDet_sq
    _ = (LinearMap.id + B.comp i).det := by rw [hBi]
    _ = (LinearMap.id + i.comp B).det := (det_id_add_comp i B).symm
    _ = (LinearMap.id - P + P.comp (L.adjoint.comp (L.comp P))).det := by rw [hiB]
    _ = _ := by
      rw [← LinearMap.det_toMatrix Grassmannian.coordinateBasis.toBasis]
      simp only [map_add, map_sub,
        LinearMap.toMatrix_id, LinearMap.toMatrix_comp Grassmannian.coordinateBasis.toBasis
          Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis,
        LinearMap.toMatrix_adjoint Grassmannian.coordinateBasis Grassmannian.coordinateBasis,
        Grassmannian.toMatrix_projectionLinearMap, P, L, ← jacobian_eq_toMatrix]
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]

theorem tangentialJacobianReal_eq_sqrt_det_ambientGram
    (f : Euclidean N → Euclidean N) (x : Euclidean N) (S : Grassmannian N n) :
    tangentialJacobianReal f x S =
      Real.sqrt (1 - S.1 + S.1 * (jacobian f x).transpose * jacobian f x * S.1).det := by
  rw [← tangentialJacobianReal_sq_eq_det_ambientGram, Real.sqrt_sq
    (tangentialJacobianReal_nonneg f x S)]

theorem continuous_tangentialJacobianReal {f : Euclidean N → Euclidean N}
    (hf : ContDiff ℝ 1 f) :
    Continuous (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobianReal f z.1 z.2) := by
  simp_rw [tangentialJacobianReal_eq_sqrt_det_ambientGram]
  have hP : Continuous (fun z : Euclidean N × Grassmannian N n ↦ z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hL := (continuous_jacobian hf).comp
    (continuous_fst : Continuous (Prod.fst : Euclidean N × Grassmannian N n → Euclidean N))
  exact Real.continuous_sqrt.comp
    (((continuous_const.sub hP).add (((hP.mul hL.matrix_transpose).mul hL).mul hP)).matrix_det)

theorem continuousOn_tangentialJacobianReal {f : Euclidean N → Euclidean N}
    {U : Set (Euclidean N)} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (fun z : Euclidean N × Grassmannian N n ↦
      tangentialJacobianReal f z.1 z.2) (U ×ˢ univ) := by
  simp_rw [tangentialJacobianReal_eq_sqrt_det_ambientGram]
  have hP : ContinuousOn (fun z : Euclidean N × Grassmannian N n ↦ z.2.1)
      (U ×ˢ univ) := (continuous_subtype_val.comp continuous_snd).continuousOn
  have hL : ContinuousOn (fun z : Euclidean N × Grassmannian N n ↦ jacobian f z.1)
      (U ×ˢ univ) :=
    (clmToMatrix.continuous_of_finiteDimensional.comp_continuousOn
      (hf.continuousOn_fderiv_of_isOpen hU le_rfl)).comp
        continuous_fst.continuousOn (fun _ hz ↦ hz.1)
  have hLt := continuous_id.matrix_transpose.comp_continuousOn hL
  have hGram := ((continuousOn_const (c := (1 : Matrix (Fin N) (Fin N) ℝ))).sub hP).add
    (((hP.mul hLt).mul hL).mul hP)
  exact Real.continuous_sqrt.comp_continuousOn
    (continuous_id.matrix_det.comp_continuousOn hGram)

/-- The explicit projection-matrix formula for `df(S)` proves measurability
without choosing a measurable orthonormal frame. -/
theorem ofSubmodule_image_eq_imageProjectionMatrix
    (L : Euclidean N →ₗ[ℝ] Euclidean N) (S : Grassmannian N n)
    (hrank : Module.finrank ℝ (LinearMap.range (L.domRestrict S.plane)) = n)
    (hd : (1 - S.1 + S.1 * (LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
      Grassmannian.coordinateBasis.toBasis L).transpose *
      LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis L * S.1).det ≠ 0) :
    (Grassmannian.ofSubmodule (LinearMap.range (L.domRestrict S.plane)) hrank).1 =
      let A := LinearMap.toMatrix Grassmannian.coordinateBasis.toBasis
        Grassmannian.coordinateBasis.toBasis L
      A * S.1 * (1 - S.1 + S.1 * A.transpose * A * S.1)⁻¹ * S.1 * A.transpose := by
  let b := Grassmannian.coordinateBasis (N := N)
  let A := LinearMap.toMatrix b.toBasis b.toBasis L
  let H := 1 - S.1 + S.1 * A.transpose * A * S.1
  let Q := A * S.1 * H⁻¹ * S.1 * A.transpose
  let q := (LinearMap.toMatrix b.toBasis b.toBasis).symm Q
  let F := L.comp S.projectionLinearMap
  have hqmat : LinearMap.toMatrix b.toBasis b.toBasis q = Q := by simp [q]
  have hFmat : LinearMap.toMatrix b.toBasis b.toBasis F = A * S.1 := by
    simp only [F, LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis,
      Grassmannian.toMatrix_projectionLinearMap, A, b]
  obtain ⟨hQs, hQi, hQF⟩ := imageProjectionMatrix_properties S.1 A S.symmetric S.idempotent hd
  have hqF : q.comp F = F := by
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    rw [LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis, hqmat, hFmat]
    exact hQF
  have hqfactor : q = F.comp
      ((LinearMap.toMatrix b.toBasis b.toBasis).symm (H⁻¹ * S.1 * A.transpose)) := by
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    rw [LinearMap.toMatrix_comp b.toBasis b.toBasis b.toBasis, hqmat, hFmat]
    simp only [LinearEquiv.apply_symm_apply, Q, Matrix.mul_assoc]
  have hrangeF : LinearMap.range F = LinearMap.range (L.domRestrict S.plane) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨S.projectionLinearMap w, ⟨w, rfl⟩⟩, rfl⟩
    · rintro ⟨w, rfl⟩
      refine ⟨w.1, ?_⟩
      change L (S.projectionLinearMap w) = L w
      rw [S.projectionLinearMap_apply_of_mem w.2]
  have hrangeq : LinearMap.range q = LinearMap.range F := by
    apply le_antisymm
    · rw [hqfactor]
      exact LinearMap.range_comp_le_range _ _
    · rintro v ⟨w, rfl⟩
      exact ⟨F w, LinearMap.congr_fun hqF w⟩
  have hqid : IsIdempotentElem q := by
    apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    rw [LinearMap.toMatrix_mul, hqmat]
    exact hQi
  have hqsym : q.IsSymmetric := by
    apply (LinearMap.isHermitian_toMatrix_iff b).mp
    rw [hqmat, Matrix.isHermitian_iff_isSymm]
    exact hQs
  obtain ⟨_, hqproj⟩ :=
    (LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range).mp ⟨hqid, hqsym⟩
  change LinearMap.toMatrix b.toBasis b.toBasis
    ((LinearMap.range (L.domRestrict S.plane)).starProjection :
      Euclidean N →ₗ[ℝ] Euclidean N) = Q
  have hqproj' : q = ((LinearMap.range (L.domRestrict S.plane)).starProjection :
      Euclidean N →ₗ[ℝ] Euclidean N) := by
    simpa only [hrangeq, hrangeF] using hqproj
  rw [← hqproj', hqmat]

theorem transportedPlane_val_eq (f : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) :
    (transportedPlane f x S).1 =
      if tangentialJacobianReal f x S ≠ 0 then
        jacobian f x * S.1 *
          (1 - S.1 + S.1 * (jacobian f x).transpose * jacobian f x * S.1)⁻¹ *
            S.1 * (jacobian f x).transpose
      else S.1 := by
  classical
  by_cases h : tangentialJacobianReal f x S ≠ 0
  · rw [transportedPlane, dif_pos h, if_pos h]
    apply ofSubmodule_image_eq_imageProjectionMatrix (fderiv ℝ f x).toLinearMap S
    change (1 - S.1 + S.1 * (jacobian f x).transpose * jacobian f x * S.1).det ≠ 0
    rw [← tangentialJacobianReal_sq_eq_det_ambientGram]
    exact pow_ne_zero 2 h
  · simp [transportedPlane, h]

theorem measurable_matrix_nonsing_inv :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A⁻¹) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact continuous_id.matrix_det.measurable.inv.mul
    (continuous_id.matrix_adjugate.measurable.eval_matrix)

theorem measurable_transportedPlane {f : Euclidean N → Euclidean N}
    (hf : ContDiff ℝ 1 f) :
    Measurable (fun z : Euclidean N × Grassmannian N n ↦ transportedPlane f z.1 z.2) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  have hP : Continuous (fun z : Euclidean N × Grassmannian N n ↦ z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hL := (continuous_jacobian hf).comp
    (continuous_fst : Continuous (Prod.fst : Euclidean N × Grassmannian N n → Euclidean N))
  have hH : Continuous (fun z : Euclidean N × Grassmannian N n ↦
      1 - z.2.1 + z.2.1 * (jacobian f z.1).transpose * jacobian f z.1 * z.2.1) :=
    (continuous_const.sub hP).add (((hP.mul hL.matrix_transpose).mul hL).mul hP)
  have hQ := (((hL.measurable.mul hP.measurable).mul
    (measurable_matrix_nonsing_inv.comp hH.measurable)).mul hP.measurable).mul
      hL.matrix_transpose.measurable
  have hset : MeasurableSet {z : Euclidean N × Grassmannian N n |
      tangentialJacobianReal f z.1 z.2 ≠ 0} :=
    (isClosed_eq (continuous_tangentialJacobianReal hf) continuous_const).measurableSet.compl
  have hval : Measurable (fun z : Euclidean N × Grassmannian N n ↦
      (transportedPlane f z.1 z.2).1) := by
    simp_rw [transportedPlane_val_eq]
    exact hQ.ite hset hP.measurable
  exact hval.subtype_mk

theorem measurable_imageMap {f : Euclidean N → Euclidean N}
    (hf : ContDiff ℝ 1 f) : Measurable (imageMap (n := n) f) :=
  (hf.continuous.measurable.comp measurable_fst).prodMk (measurable_transportedPlane hf)

/-- Domain-local measurability and proper pushforward in Simon (8.2.1).
Only regularity on `U` and properness on the weight support inside `U` are
used.  The Jacobian-weighted measure is concentrated on Simon's `Gₙ⁺(U)`,
so the total extension of the image-plane map does not add mass. -/
theorem ae_mem_domain (V : Varifold N n U) :
    ∀ᵐ z ∂V.measure, z ∈ U ×ˢ (univ : Set (Grassmannian N n)) := by
  rw [ae_iff]
  have hcomp : {z : Euclidean N × Grassmannian N n | ¬z ∈ U ×ˢ univ} =
      Uᶜ ×ˢ univ := by ext z; simp
  rw [hcomp]
  exact V.supported

theorem measurable_imageMap_domain {f : Euclidean N → Euclidean N}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    Measurable (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦ imageMap f z.1) := by
  letI : SecondCountableTopology (Matrix (Fin N) (Fin N) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → ℝ))
  have hx : Continuous (domainProjection (U := U) (n := n)) :=
    (continuous_fst.comp continuous_subtype_val).subtype_mk _
  have hP : Continuous (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦ z.1.2.1) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
  have hL : Continuous (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦ jacobian f z.1.1) :=
    clmToMatrix.continuous_of_finiteDimensional.comp
      ((continuousOn_iff_continuous_domRestrict.mp
        (hf.continuousOn_fderiv_of_isOpen hU le_rfl)).comp hx)
  have hH : Continuous (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦
      1 - z.1.2.1 + z.1.2.1 * (jacobian f z.1.1).transpose * jacobian f z.1.1 * z.1.2.1) :=
    (continuous_const.sub hP).add (((hP.mul hL.matrix_transpose).mul hL).mul hP)
  have hQ := (((hL.measurable.mul hP.measurable).mul
    (measurable_matrix_nonsing_inv.comp hH.measurable)).mul hP.measurable).mul
      hL.matrix_transpose.measurable
  have hJ : Continuous (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦
      tangentialJacobianReal f z.1.1 z.1.2) :=
    continuousOn_iff_continuous_domRestrict.mp (continuousOn_tangentialJacobianReal hU hf)
  have hset : MeasurableSet {z : U ×ˢ (univ : Set (Grassmannian N n)) |
      tangentialJacobianReal f z.1.1 z.1.2 ≠ 0} :=
    (isClosed_eq hJ continuous_const).measurableSet.compl
  have hval : Measurable (fun z : U ×ˢ (univ : Set (Grassmannian N n)) ↦
      (transportedPlane f z.1.1 z.1.2).1) := by
    simp_rw [transportedPlane_val_eq]
    exact hQ.ite hset hP.measurable
  exact ((continuousOn_iff_continuous_domRestrict.mp hf.continuousOn).comp hx).measurable.prodMk
    hval.subtype_mk

theorem aemeasurable_imageMap (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U) :
    AEMeasurable (imageMap (n := n) f) V.measure := by
  have h := aemeasurable_restrict_of_measurable_subtype
    (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)
    (measurable_imageMap_domain V.isOpen_domain hf)
    (μ := V.measure)
  rwa [Measure.restrict_eq_self_of_ae_mem V.ae_mem_domain] at h

theorem aestronglyMeasurable_tangentialJacobianReal (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U) :
    AEStronglyMeasurable
      (fun z : Euclidean N × Grassmannian N n ↦ tangentialJacobianReal f z.1 z.2)
      V.measure := by
  have h := aemeasurable_restrict_of_measurable_subtype
    (f := fun z : Euclidean N × Grassmannian N n ↦ tangentialJacobianReal f z.1 z.2)
    (V.isOpen_domain.measurableSet.prod MeasurableSet.univ)
    (continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_tangentialJacobianReal V.isOpen_domain hf)).measurable
    (μ := V.measure)
  rw [Measure.restrict_eq_self_of_ae_mem V.ae_mem_domain] at h
  exact h.aestronglyMeasurable

theorem jacobianDensity_ae_mem_positiveDomain (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U) :
    ∀ᵐ z ∂V.measure.withDensity (fun z ↦ tangentialJacobian f z.1 z.2),
      z ∈ U ×ˢ (univ : Set (Grassmannian N n)) ∧ tangentialJacobianReal f z.1 z.2 ≠ 0 := by
  apply (ae_withDensity_iff'
    (V.aestronglyMeasurable_tangentialJacobianReal hf).aemeasurable.ennreal_ofReal).mpr
  filter_upwards [V.ae_mem_domain] with z hz hJ
  exact ⟨hz, (tangentialJacobian_ne_zero_iff f z.1 z.2).mp hJ⟩

theorem pushforwardMeasure_apply_of_contDiffOn (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U)
    {A : Set (Euclidean N × Grassmannian N n)} (hA : MeasurableSet A) :
    V.pushforwardMeasure f A =
      ∫⁻ z in imageMap (n := n) f ⁻¹' A, tangentialJacobian f z.1 z.2 ∂V.measure := by
  rw [pushforwardMeasure, Measure.map_apply_of_aemeasurable
    ((V.aemeasurable_imageMap hf).mono_ac (withDensity_absolutelyContinuous _ _)) hA]
  exact withDensity_apply₀ _ ((V.aemeasurable_imageMap hf).nullMeasurable hA)

theorem exists_compact_preimage_on_support (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hfW : MapsTo f U W)
    (hproper : IsProperMap
      (fun x : ↥(V.weight.support ∩ U) ↦ (⟨f x, hfW x.2.2⟩ : W)))
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKW : K ⊆ W) :
    ∃ L : Set (Euclidean N), IsCompact L ∧ L ⊆ U ∧
      V.weight.support ∩ U ∩ f ⁻¹' K ⊆ L := by
  let g : ↥(V.weight.support ∩ U) → W := fun x ↦ ⟨f x, hfW x.2.2⟩
  have hK' : IsCompact ((Subtype.val : W → Euclidean N) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKW)
  let C := g ⁻¹' (Subtype.val ⁻¹' K)
  have hC : IsCompact C := hproper.isCompact_preimage hK'
  refine ⟨Subtype.val '' C, hC.image continuous_subtype_val, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2.2
  · intro x hx
    exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩

theorem pushforwardMeasure_finite_on_compact (V : Varifold N n U)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U)
    (hfW : MapsTo f U W)
    (hproper : IsProperMap
      (fun x : ↥(V.weight.support ∩ U) ↦ (⟨f x, hfW x.2.2⟩ : W)))
    (K : Set (Euclidean N)) (hK : IsCompact K) (hKW : K ⊆ W) :
    V.pushforwardMeasure f (K ×ˢ (univ : Set (Grassmannian N n))) ≠ ∞ := by
  obtain ⟨L, hL, hLU, hpre⟩ := V.exists_compact_preimage_on_support hfW hproper K hK hKW
  have hsupp : ∀ᵐ z ∂V.measure, z.1 ∈ V.weight.support :=
    ae_of_ae_map measurable_fst.aemeasurable V.weight.support_mem_ae
  have hsubset : imageMap f ⁻¹' (K ×ˢ (univ : Set (Grassmannian N n))) ≤ᵐ[V.measure]
      L ×ˢ (univ : Set (Grassmannian N n)) := by
    filter_upwards [hsupp, V.ae_mem_domain] with z hz hU hKz
    exact ⟨hpre ⟨⟨hz, hU.1⟩, hKz.1⟩, mem_univ _⟩
  have hJcont := (continuousOn_tangentialJacobianReal V.isOpen_domain hf).mono
    (prod_mono hLU (Subset.rfl : (univ : Set (Grassmannian N n)) ⊆ univ))
  obtain ⟨C, hC⟩ := (hL.prod (isCompact_univ : IsCompact (univ : Set (Grassmannian N n))))
    |>.exists_bound_of_continuousOn hJcont
  have hJint : IntegrableOn
      (fun z : Euclidean N × Grassmannian N n ↦ tangentialJacobianReal f z.1 z.2)
      (L ×ˢ univ) V.measure := by
    apply V.measure.integrableOn_of_bounded (V.finite_on_compact L hL hLU)
      (V.aestronglyMeasurable_tangentialJacobianReal hf)
    filter_upwards [ae_restrict_mem (hL.measurableSet.prod MeasurableSet.univ)] with z hz
    exact hC z hz
  rw [V.pushforwardMeasure_apply_of_contDiffOn hf (hK.measurableSet.prod MeasurableSet.univ)]
  apply ne_top_of_le_ne_top ?_ (lintegral_mono_set' hsubset)
  exact (lintegral_ofReal_ne_top_iff_integrable hJint.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ tangentialJacobianReal_nonneg f z.1 z.2)).mpr hJint

noncomputable def pushforward (V : Varifold N n U) (hW : IsOpen W)
    {f : Euclidean N → Euclidean N} (hf : ContDiffOn ℝ 1 f U)
    (hfW : MapsTo f U W)
    (hproper : IsProperMap
      (fun x : ↥(V.weight.support ∩ U) ↦ (⟨f x, hfW x.2.2⟩ : W))) : Varifold N n W where
  isOpen_domain := hW
  measure := V.pushforwardMeasure f
  supported := by
    rw [pushforwardMeasure, Measure.map_apply_of_aemeasurable
      ((V.aemeasurable_imageMap hf).mono_ac (withDensity_absolutelyContinuous _ _))
      (hW.measurableSet.compl.prod MeasurableSet.univ)]
    apply (withDensity_absolutelyContinuous _ _)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [V.ae_mem_domain] with z hz
    intro hnot
    exact hnot.1 (hfW hz.1)
  finite_on_compact := V.pushforwardMeasure_finite_on_compact hf hfW hproper

/-- `div_S X = trace(P_S DX)`, Simon 8.2.3. -/
noncomputable def tangentialDivergence (X : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n) : ℝ :=
  Matrix.trace (S.1 * jacobian X x)

/-- The projection-matrix trace formula is exactly Simon's displayed
orthonormal-basis formula (8.2.4). -/
theorem tangentialDivergence_eq_sum_inner (X : Euclidean N → Euclidean N)
    (x : Euclidean N) (S : Grassmannian N n)
    (b : OrthonormalBasis (Fin n) ℝ S.plane) :
    tangentialDivergence X x S =
      ∑ i, inner ℝ (b i : Euclidean N)
        ((fderiv ℝ X x) (b i : Euclidean N)) := by
  let D : Euclidean N →ₗ[ℝ] Euclidean N := (fderiv ℝ X x).toLinearMap
  let q : Euclidean N →ₗ[ℝ] S.plane := S.planeProjection
  let i : S.plane →ₗ[ℝ] Euclidean N := S.plane.subtype
  have hp : i.comp q = S.projectionLinearMap := by
    rfl
  calc
    tangentialDivergence X x S =
        LinearMap.trace ℝ (Euclidean N) (S.projectionLinearMap.comp D) := by
      rw [tangentialDivergence, LinearMap.trace_eq_matrix_trace ℝ
        Grassmannian.coordinateBasis.toBasis,
        LinearMap.toMatrix_comp Grassmannian.coordinateBasis.toBasis
          Grassmannian.coordinateBasis.toBasis Grassmannian.coordinateBasis.toBasis]
      simp [D, jacobian_eq_toMatrix]
    _ = LinearMap.trace ℝ (Euclidean N) (i.comp (q.comp D)) := by
      rw [← LinearMap.comp_assoc, hp]
    _ = LinearMap.trace ℝ S.plane ((q.comp D).comp i) :=
      LinearMap.trace_comp_comm' (q.comp D) i
    _ = ∑ j, inner ℝ (b j) (((q.comp D).comp i) (b j)) :=
      LinearMap.trace_eq_sum_inner _ b
    _ = ∑ j, inner ℝ (b j : Euclidean N) (D (b j : Euclidean N)) := by
      apply Finset.sum_congr rfl
      intro j _
      change inner ℝ (b j : Euclidean N)
          (S.projectionLinearMap (D (b j : Euclidean N))) = _
      rw [← S.projectionLinearMap_isSymmetric]
      rw [S.projectionLinearMap_apply_of_mem (b j).property]
    _ = ∑ j, inner ℝ (b j : Euclidean N)
        ((fderiv ℝ X x) (b j : Euclidean N)) := rfl

theorem tangentialDivergence_add {X Y : Euclidean N → Euclidean N}
    {x : Euclidean N} (S : Grassmannian N n)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x) :
    tangentialDivergence (X + Y) x S =
      tangentialDivergence X x S + tangentialDivergence Y x S := by
  rw [tangentialDivergence, tangentialDivergence, tangentialDivergence,
    jacobian, jacobian, jacobian, fderiv_add hX hY]
  simp only [map_add, Matrix.mul_add, Matrix.trace_add]

theorem tangentialDivergence_const_smul (c : ℝ)
    {X : Euclidean N → Euclidean N} {x : Euclidean N}
    (S : Grassmannian N n) (hX : DifferentiableAt ℝ X x) :
    tangentialDivergence (c • X) x S = c * tangentialDivergence X x S := by
  rw [tangentialDivergence, tangentialDivergence, jacobian, jacobian,
    fderiv_const_smul hX c]
  simp only [map_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

theorem continuous_tangentialDivergence {X : Euclidean N → Euclidean N}
    (hX : ContDiff ℝ 1 X) :
    Continuous (fun z : Euclidean N × Grassmannian N n ↦
      tangentialDivergence X z.1 z.2) := by
  apply Continuous.matrix_trace
  exact (continuous_subtype_val.comp continuous_snd).mul
    ((continuous_jacobian hX).comp continuous_fst)

theorem support_tangentialDivergence_subset (X : Euclidean N → Euclidean N) :
    support (fun z : Euclidean N × Grassmannian N n ↦
      tangentialDivergence X z.1 z.2) ⊆
      tsupport X ×ˢ (Set.univ : Set (Grassmannian N n)) := by
  intro z hz
  refine ⟨?_, Set.mem_univ _⟩
  contrapose! hz
  simp [tangentialDivergence, jacobian, fderiv_of_notMem_tsupport ℝ hz, clmToMatrix]

theorem hasCompactSupport_tangentialDivergence (X : Euclidean N → Euclidean N)
    (hX : HasCompactSupport X) :
    HasCompactSupport (fun z : Euclidean N × Grassmannian N n ↦
      tangentialDivergence X z.1 z.2) := by
  apply (hX.prod isCompact_univ).of_isClosed_subset (isClosed_tsupport _)
  exact closure_minimal (support_tangentialDivergence_subset X)
    ((isClosed_tsupport X).prod isClosed_univ)

/-- The first-variation integrand is genuinely Bochner integrable for the
compactly supported `C¹` fields used by Simon. -/
theorem integrable_tangentialDivergence (V : Varifold N n U)
    (X : Euclidean N → Euclidean N) (hX_c1 : ContDiff ℝ 1 X)
    (hXcompact : HasCompactSupport X) (hXU : tsupport X ⊆ U) :
    Integrable (fun z : Euclidean N × Grassmannian N n ↦
      tangentialDivergence X z.1 z.2) V.measure := by
  let F := fun z : Euclidean N × Grassmannian N n ↦
    tangentialDivergence X z.1 z.2
  have hFcont : Continuous F := continuous_tangentialDivergence hX_c1
  have hFcompact : HasCompactSupport F := hasCompactSupport_tangentialDivergence X hXcompact
  obtain ⟨C, hC⟩ := hFcompact.exists_bound_of_continuous hFcont
  have hfinite : V.measure
      (tsupport X ×ˢ (Set.univ : Set (Grassmannian N n))) ≠ ∞ :=
    V.finite_on_compact (tsupport X) hXcompact hXU
  have hOn : IntegrableOn F
      (tsupport X ×ˢ (Set.univ : Set (Grassmannian N n))) V.measure :=
    V.measure.integrableOn_of_bounded hfinite hFcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ hC z)
  exact (integrableOn_iff_integrable_of_support_subset
    (support_tangentialDivergence_subset X)).mp hOn

/-- First variation `δV(X) = ∫ div_S X dV`, Simon 8.2.3. -/
noncomputable def firstVariation (V : Varifold N n U)
    (X : Euclidean N → Euclidean N) : ℝ :=
  ∫ z : Euclidean N × Grassmannian N n, tangentialDivergence X z.1 z.2 ∂V.measure

/-- The integral formula (8.2.3) is additive on Simon's test fields. -/
theorem firstVariation_add (V : Varifold N n U)
    {X Y : Euclidean N → Euclidean N}
    (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y)
    (hXcompact : HasCompactSupport X) (hYcompact : HasCompactSupport Y)
    (hXU : tsupport X ⊆ U) (hYU : tsupport Y ⊆ U) :
    V.firstVariation (X + Y) = V.firstVariation X + V.firstVariation Y := by
  have hXint := V.integrable_tangentialDivergence X hX hXcompact hXU
  have hYint := V.integrable_tangentialDivergence Y hY hYcompact hYU
  rw [firstVariation, firstVariation, firstVariation, ← integral_add hXint hYint]
  apply integral_congr_ae
  filter_upwards with z
  exact tangentialDivergence_add z.2 hX.differentiable_one.differentiableAt
    hY.differentiable_one.differentiableAt

/-- The integral formula (8.2.3) is homogeneous on Simon's test fields. -/
theorem firstVariation_const_smul (V : Varifold N n U) (c : ℝ)
    {X : Euclidean N → Euclidean N} (hX : ContDiff ℝ 1 X)
    (hXcompact : HasCompactSupport X) :
    V.firstVariation (c • X) = c * V.firstVariation X := by
  rw [firstVariation, firstVariation, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  exact tangentialDivergence_const_smul c z.2 hX.differentiable_one.differentiableAt

/-- The test space `K(U; ℝᴺ)` used in Simon §8.2: compactly supported
`C¹` vector fields whose topological support is contained in `U`. -/
structure TestVectorField (U : Set (Euclidean N)) where
  toFun : Euclidean N → Euclidean N
  contDiff : ContDiff ℝ 1 toFun
  compactSupport : HasCompactSupport toFun
  support_subset : tsupport toFun ⊆ U

instance : CoeFun (TestVectorField (N := N) U)
    (fun _ ↦ Euclidean N → Euclidean N) :=
  ⟨TestVectorField.toFun⟩

/-- Test fields of norm at most one supported in `W`, the class occurring in
the supremum in (8.2.5). -/
def TestVectorField.UnitSupportedIn (X : TestVectorField (N := N) U)
    (W : Set (Euclidean N)) : Prop :=
  tsupport X.toFun ⊆ W ∧ ∀ x, ‖X x‖ ≤ 1

/-- The supremum in Simon (8.2.5).  It is `ℝ≥0∞`-valued so the definition is
meaningful before local boundedness has been proved. -/
noncomputable def firstVariationNormOn (V : Varifold N n U)
    (W : Set (Euclidean N)) : ℝ≥0∞ := by
  classical
  exact ⨆ X : TestVectorField (N := N) U,
    if X.UnitSupportedIn W then ENNReal.ofReal |V.firstVariation X| else 0

/-- Simon's condition of locally bounded first variation, expressed by
finiteness of the exact supremum in (8.2.5) on every `W ⋐ U`. -/
def HasLocallyBoundedFirstVariation (V : Varifold N n U) : Prop :=
  ∀ W : Set (Euclidean N), IsOpen W →
    (IsCompact (closure W) ∧ closure W ⊆ U) →
      V.firstVariationNormOn W ≠ ∞

/-- The ambient zero extension of a measure satisfying (8.2.5). Local
finiteness is required on the actual domain `U`, not at its boundary.
This predicate does not assert existence of the Riesz-representation
measure; that theorem remains an explicit obligation. -/
def IsFirstVariationMeasure (V : Varifold N n U)
    (mu : Measure (Euclidean N)) : Prop :=
  IsLocallyFiniteMeasure (mu.comap (Subtype.val : U → Euclidean N)) ∧
    mu Uᶜ = 0 ∧
    ∀ W : Set (Euclidean N), IsOpen W →
      (IsCompact (closure W) ∧ closure W ⊆ U) →
        mu W = V.firstVariationNormOn W

/-- The signed polar representation in (8.2.6),
`δV(X) = -∫ ν · X d‖δV‖`.  Existence from the vector-valued Riesz
representation theorem is deliberately not asserted here. -/
def IsFirstVariationPolarRepresentation (V : Varifold N n U)
    (mu : Measure (Euclidean N)) (nu : Euclidean N → Euclidean N) : Prop :=
  AEStronglyMeasurable nu mu ∧
    (∀ᵐ x ∂mu, ‖nu x‖ = 1) ∧
    ∀ X : TestVectorField (N := N) U,
      Integrable (fun x ↦ inner ℝ (nu x) (X x)) mu ∧
      V.firstVariation X = -(∫ x, inner ℝ (nu x) (X x) ∂mu)

/-- `D_{μ_V} ‖δV‖`, represented by Mathlib's Radon--Nikodym derivative. -/
noncomputable def firstVariationDensity (V : Varifold N n U)
    (mu : Measure (Euclidean N)) (x : Euclidean N) : ℝ≥0∞ :=
  mu.rnDeriv V.weight x

/-- The finite, real-valued density used in the generalized mean curvature.
It agrees with `firstVariationDensity` at the `μ_V`-almost every point where
that derivative is finite. -/
noncomputable def firstVariationDensityReal (V : Varifold N n U)
    (mu : Measure (Euclidean N)) (x : Euclidean N) : ℝ :=
  (V.firstVariationDensity mu x).toReal

/-- `H = D_{μ_V} ‖δV‖ ν` from (8.2.7)--(8.2.8). -/
noncomputable def generalizedMeanCurvature (V : Varifold N n U)
    (mu : Measure (Euclidean N)) (nu : Euclidean N → Euclidean N)
    (x : Euclidean N) : Euclidean N :=
  V.firstVariationDensityReal mu x • nu x

/-- Simon's generalized-boundary set `Z` in (8.2.9). -/
noncomputable def generalizedBoundarySet (V : Varifold N n U)
    (mu : Measure (Euclidean N)) : Set (Euclidean N) :=
  U ∩ {x | V.firstVariationDensity mu x = ∞}

/-- Simon's generalized-boundary measure `σ = ‖δV‖ ⌞ Z`. -/
noncomputable def generalizedBoundaryMeasure (V : Varifold N n U)
    (mu : Measure (Euclidean N)) : Measure (Euclidean N) :=
  mu.restrict (V.generalizedBoundarySet mu)

/-- The source assertion `μ_V(Z)=0` follows from finiteness of the
Radon--Nikodym derivative almost everywhere. -/
theorem weight_generalizedBoundarySet (V : Varifold N n U)
    (mu : Measure (Euclidean N)) [SigmaFinite mu] :
    V.weight (V.generalizedBoundarySet mu) = 0 := by
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [Measure.rnDeriv_ne_top mu V.weight] with x hx
  intro hmem
  exact hx hmem.2

/-- The canonical Lebesgue decomposition underlying (8.2.8).  Identifying
Mathlib's singular part with Simon's restriction to the density-infinity set
uses the differentiation theorem and remains separate. -/
theorem firstVariationMeasure_lebesgueDecomposition (V : Varifold N n U)
    (mu : Measure (Euclidean N)) [SigmaFinite mu] :
    mu = mu.singularPart V.weight +
      V.weight.withDensity (mu.rnDeriv V.weight) := by
  exact mu.haveLebesgueDecomposition_add V.weight

/-- Stationarity in `U`: first variation vanishes on every compactly supported
`C¹` vector field supported in `U`. -/
def Stationary (V : Varifold N n U) : Prop :=
  ∀ X : TestVectorField (N := N) U, V.firstVariation X = 0

theorem stationary_iff (V : Varifold N n U) : V.Stationary ↔
    ∀ X : Euclidean N → Euclidean N,
      ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
        V.firstVariation X = 0 := by
  constructor
  · intro h X hC1 hcompact hsupp
    exact h ⟨X, hC1, hcompact, hsupp⟩
  · intro h X
    exact h X X.contDiff X.compactSupport X.support_subset

theorem Stationary.firstVariationNormOn_eq_zero {V : Varifold N n U}
    (hV : V.Stationary) (W : Set (Euclidean N)) :
    V.firstVariationNormOn W = 0 := by
  classical
  unfold firstVariationNormOn
  apply le_antisymm
  · refine iSup_le fun X ↦ ?_
    by_cases hX : X.UnitSupportedIn W
    · rw [if_pos hX, hV X]
      simp
    · rw [if_neg hX]
  · exact bot_le

theorem Stationary.hasLocallyBoundedFirstVariation {V : Varifold N n U}
    (hV : V.Stationary) : V.HasLocallyBoundedFirstVariation := by
  intro W _ _
  rw [hV.firstVariationNormOn_eq_zero W]
  exact ENNReal.zero_ne_top

@[simp] theorem jacobian_zero (x : Euclidean N) :
    jacobian (fun _ : Euclidean N ↦ 0) x = 0 := by
  rw [jacobian, (hasFDerivAt_const (x := x) (0 : Euclidean N)).fderiv]
  rfl

@[simp] theorem tangentialDivergence_zero (x : Euclidean N) (S : Grassmannian N n) :
    tangentialDivergence (fun _ : Euclidean N ↦ 0) x S = 0 := by
  simp [tangentialDivergence]

@[simp] theorem firstVariation_zero (V : Varifold N n U) :
    V.firstVariation (fun _ : Euclidean N ↦ 0) = 0 := by
  simp [firstVariation]

end Varifold

end Poincare.SimonGMT.Chapter08
