import Std
import Poincare.SimonGMT.Chapter01.Basic
import Poincare.SimonGMT.Chapter01.MetricCriterion
import Poincare.SimonGMT.Chapter01.Hausdorff
import Poincare.SimonGMT.Chapter01.HausdorffOpenCovers
import Poincare.SimonGMT.Chapter01.LebesgueOuterUniqueness
import Poincare.SimonGMT.Chapter01.LebesgueBoxCovers
import Poincare.SimonGMT.Chapter01.EuclideanHausdorffUpper
import Poincare.SimonGMT.Chapter01.IsodiametricBounds
import Poincare.SimonGMT.Chapter01.SteinerSliceBounds
import Poincare.SimonGMT.Chapter01.SteinerDiameter
import Poincare.SimonGMT.Chapter01.SteinerVolume
import Poincare.SimonGMT.Chapter01.SteinerSymmetry
import Poincare.SimonGMT.Chapter01.EuclideanNormalization
import Poincare.SimonGMT.Chapter01.Densities
import Poincare.SimonGMT.Chapter01.DensityComparison
import Poincare.SimonGMT.Chapter01.DensityCovering
import Poincare.SimonGMT.Chapter01.Radon
import Poincare.SimonGMT.Chapter01.RadonOuterMeasure
import Poincare.SimonGMT.Chapter01.RadonTopology
import Poincare.SimonGMT.Chapter01.RadonDensity
import Poincare.SimonGMT.Chapter01.RadonRepresentation
import Poincare.SimonGMT.Chapter01.RadonLocalMeasurability
import Poincare.SimonGMT.Chapter01.RadonCompactDecomposition
import Poincare.SimonGMT.Chapter01.RadonFieldGluing
import Poincare.SimonGMT.Chapter01.Regularity
import Poincare.SimonGMT.Chapter01.RegularityCompletion
import Poincare.SimonGMT.Chapter01.ExactRegularity
import Poincare.SimonGMT.Chapter01.Lusin
import Poincare.SimonGMT.Chapter01.SymmetricVitali
import Poincare.SimonGMT.Chapter01.RelativeDensityComparison
import Poincare.SimonGMT.Chapter01.GeneralDensity
import Poincare.SimonGMT.Chapter01.GeneralDifferentiation
import Poincare.SimonGMT.Chapter01.SingularDecomposition
import Poincare.SimonGMT.Chapter01.LowerDensityComparison
import Poincare.SimonGMT.Chapter01.RadonNikodymDensity
import Poincare.SimonGMT.Chapter01.RadonNikodymTheorem
import Poincare.SimonGMT.Chapter01.InfiniteDensitySet
import Poincare.SimonGMT.Chapter01.SingularPartRemarks
import Poincare.SimonGMT.Chapter01.HausdorffDensityBounds
import Poincare.SimonGMT.Chapter01.HausdorffContentDensity
import Poincare.SimonGMT.Chapter01.VectorFunctionalEnvelope
import Poincare.SimonGMT.Chapter01.VectorFunctionalL1
import Poincare.SimonGMT.Chapter01.SequentialCompactnessCounterexample
import Poincare.SimonGMT.Chapter01.FiniteL1Dual
import Poincare.SimonGMT.Chapter01.LocalFiniteL1Dual
import Poincare.SimonGMT.Chapter01.RadonLocalDualField
import Poincare.SimonGMT.Chapter01.RadonCaratheodoryIntegral
import Poincare.SimonGMT.Chapter01.RadonPolarRepresentation
import Poincare.SimonGMT.Chapter01.PolarFieldNorm
import Poincare.SimonGMT.Chapter01.FinitePolarRepresentation
import Poincare.SimonGMT.Chapter01.CompactMetrizableCompactness
import Poincare.SimonGMT.Chapter02.Lipschitz
import Poincare.SimonGMT.Chapter02.LipschitzDomain
import Poincare.SimonGMT.Chapter02.LipschitzMeasurability
import Poincare.SimonGMT.Chapter02.Area
import Poincare.SimonGMT.Chapter02.AreaWeighted
import Poincare.SimonGMT.Chapter02.AreaLinearWeighted
import Poincare.SimonGMT.Chapter02.AreaMultiplicity
import Poincare.SimonGMT.Chapter02.AreaCurve
import Poincare.SimonGMT.Chapter02.AreaParametrization
import Poincare.SimonGMT.Chapter02.AreaApproximation
import Poincare.SimonGMT.Chapter02.AreaDerivative
import Poincare.SimonGMT.Chapter02.AreaFormula
import Poincare.SimonGMT.Chapter02.WeightedArea
import Poincare.SimonGMT.Chapter02.AreaNormalization
import Poincare.SimonGMT.Chapter02.AreaCritical
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Poincare.SimonGMT.Chapter02.AreaBranches
import Poincare.SimonGMT.Chapter02.AreaNoninjective
import Poincare.SimonGMT.Chapter02.AreaCompletion
import Poincare.SimonGMT.Chapter02.AreaDomain
import Poincare.SimonGMT.Chapter02.AreaLiteral
import Poincare.SimonGMT.Chapter02.AreaCurveExample
import Poincare.SimonGMT.Chapter02.AreaGraphExample
import Poincare.SimonGMT.Chapter02.AreaSubmanifoldExample
import Poincare.SimonGMT.Chapter02.CoareaProjection
import Poincare.SimonGMT.Chapter02.CoareaLinearAlgebra
import Poincare.SimonGMT.Chapter02.CoareaLinear
import Poincare.SimonGMT.Chapter02.Submanifold
import Poincare.SimonGMT.Chapter02.SubmanifoldTopology
import Poincare.SimonGMT.Chapter02.SubmanifoldCalculus
import Poincare.SimonGMT.Chapter02.SecondFundamentalForm
import Poincare.SimonGMT.Chapter02.SecondFundamentalFormCalculus
import Poincare.SimonGMT.Chapter02.SubmanifoldIntegral
import Poincare.SimonGMT.Chapter02.BV
import Poincare.SimonGMT.Chapter02.UpperIntegral
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter03.SubmanifoldCover
import Poincare.SimonGMT.Chapter03.DisjointCover
import Poincare.SimonGMT.Chapter03.Differential
import Poincare.SimonGMT.Chapter03.FinitePerimeter
import Poincare.SimonGMT.Chapter04.Basic
import Poincare.SimonGMT.Chapter04.FirstVariation
import Poincare.SimonGMT.Chapter04.Density
import Poincare.SimonGMT.Chapter04.MeanCurvature
import Poincare.SimonGMT.Chapter04.LogarithmicError
import Poincare.SimonGMT.Chapter04.LpMeanCurvature
import Poincare.SimonGMT.Chapter04.LpDensity
import Poincare.SimonGMT.Chapter04.LpCancellation
import Poincare.SimonGMT.Chapter04.LpAnnular
import Poincare.SimonGMT.Chapter04.LayerCake
import Poincare.SimonGMT.Chapter04.LpRemarks
import Poincare.SimonGMT.Chapter04.WeightedFirstVariation
import Poincare.SimonGMT.Chapter04.WeightedCutoff
import Poincare.SimonGMT.Chapter04.WeightedEstimates
import Poincare.SimonGMT.Chapter04.WeightedRadiusIntegration
import Poincare.SimonGMT.Chapter04.WeightedBallIntegration
import Poincare.SimonGMT.Chapter04.RadialPotential
import Poincare.SimonGMT.Chapter04.WeightedBoundedIntegration
import Poincare.SimonGMT.Chapter04.WeightedBallInequalities
import Poincare.SimonGMT.Chapter04.MultiplicityBridge
import Poincare.SimonGMT.Chapter04.WeightedDensity
import Poincare.SimonGMT.Chapter04.TangentDensity
import Poincare.SimonGMT.Chapter04.LowerDensityTangents
import Poincare.SimonGMT.Chapter04.PositiveMultiplicityScale
import Poincare.SimonGMT.Chapter04.CanonicalDensitySupport
import Poincare.SimonGMT.Chapter04.PoincareKernel
import Poincare.SimonGMT.Chapter04.PoincareTruncation
import Poincare.SimonGMT.Chapter04.Poincare
import Poincare.SimonGMT.Chapter04.SobolevCovering
import Poincare.SimonGMT.Chapter04.GoodRadiusSource
import Poincare.SimonGMT.Chapter04.GoodRadius
import Poincare.SimonGMT.Chapter04.CompactWeighted
import Poincare.SimonGMT.Chapter04.CompactRadius
import Poincare.SimonGMT.Chapter04.SobolevGoodRadius
import Poincare.SimonGMT.Chapter04.SobolevTruncation
import Poincare.SimonGMT.Chapter04.SobolevLayerCake
import Poincare.SimonGMT.Chapter04.Sobolev
import Poincare.SimonGMT.Chapter04.CompactSupportMaximum
import Poincare.SimonGMT.Chapter04.CompactConvexHull
import Poincare.SimonGMT.Chapter04.ConvexHullProperty
import Poincare.SimonGMT.Chapter04.LpLowerDensity
import Poincare.SimonGMT.Chapter04.WeightedBlowUp
import Poincare.SimonGMT.Chapter04.ClassicalTangent
import Poincare.SimonGMT.Chapter05.Basic
import Poincare.SimonGMT.Chapter05.GraphAreaExpansion
import Poincare.SimonGMT.Chapter05.ScalarAreaRemainder
import Poincare.SimonGMT.Chapter05.HarmonicEnergy
import Poincare.SimonGMT.Chapter05.CurveAreaRemainder
import Poincare.SimonGMT.Chapter05.ScalarCodimensionRemainder
import Poincare.SimonGMT.Chapter06.Forms
import Poincare.SimonGMT.Chapter06.FormsDuality
import Poincare.SimonGMT.Chapter06.Currents
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.FormSupNorm
import Poincare.SimonGMT.Chapter06.Representation
import Poincare.SimonGMT.Chapter06.Product
import Poincare.SimonGMT.Chapter06.WedgeForms
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter06.GeometricPointProduct
import Poincare.SimonGMT.Chapter06.FixedSupportCurrentTopology
import Poincare.SimonGMT.Chapter06.CurrentDistributionEquivalence
import Poincare.SimonGMT.Chapter06.ParametricCurrentContinuity
import Poincare.SimonGMT.Chapter07.Basic
import Poincare.SimonGMT.Chapter08.Varifold
import Poincare.SimonGMT.Chapter08.JacobianBounds
import Poincare.SimonGMT.Chapter08.FirstVariation
import Poincare.SimonGMT.Chapter08.FirstVariationIntegral
import Poincare.SimonGMT.Chapter08.DeformationFamily
import Poincare.SimonGMT.Chapter08.DeformationIntegral
import Poincare.SimonGMT.Chapter08.FirstVariationBounds
import Poincare.SimonGMT.Chapter08.FirstVariationExtension
import Poincare.SimonGMT.Chapter08.FirstVariationDensity
import Poincare.SimonGMT.Chapter08.FirstVariationDecomposition
import Poincare.SimonGMT.Chapter08.ScalarRiesz
import Poincare.SimonGMT.Chapter08.VectorRiesz
import Poincare.SimonGMT.Chapter08.PolarNorm
import Poincare.SimonGMT.Chapter08.FirstVariationRiesz
import Poincare.SimonGMT.Chapter08.RadialFirstVariation
import Poincare.SimonGMT.Chapter08.RadialCutoffDifferentiation
import Poincare.SimonGMT.Chapter08.WeightedRadialIdentity
import Poincare.SimonGMT.Chapter08.StationaryCutoff
import Poincare.SimonGMT.Chapter08.StationaryMonotonicity
import Poincare.SimonGMT.Chapter08.BallVariationBound
import Poincare.SimonGMT.Chapter08.VarifoldConvergence
import Poincare.SimonGMT.Chapter08.ConstancySupport
import Poincare.SimonGMT.Chapter08.ConstancyTangent
import Poincare.SimonGMT.Chapter08.ConstancyProjection
import Poincare.SimonGMT.Chapter08.DistributionalConstancy
import Poincare.SimonGMT.Chapter08.StationaryHausdorff
import Poincare.SimonGMT.Chapter08.ConstancyHausdorffDensity
import Poincare.SimonGMT.Chapter08.ConstancyLocalDefining
import Poincare.SimonGMT.Chapter08.ConstancyNormalCharts
import Poincare.SimonGMT.Chapter08.ConstancyTangentGraph
import Poincare.SimonGMT.Chapter08.ConstancyChartTransport
import Poincare.SimonGMT.Chapter08.ConstancyChartDensity
import Poincare.SimonGMT.Chapter08.ConstancyChartVariation
import Poincare.SimonGMT.Chapter08.ConstancyDomainCounterexample
import Poincare.SimonGMT.Chapter08.ConstancyFullDimension
import Poincare.SimonGMT.Chapter08.ConstancyChartLocalIntegrability
import Poincare.SimonGMT.Chapter08.ConstancyCoordinateTests
import Poincare.SimonGMT.Chapter08.ConstancyTangentTests
import Poincare.SimonGMT.Chapter08.ConstancyPiola
import Poincare.SimonGMT.Chapter08.ConstancyChartWeakDerivatives
import Poincare.SimonGMT.Chapter08.ConstancyManifoldGluing
import Poincare.SimonGMT.Chapter08.ConstancyCorrected
import Poincare.SimonGMT.Chapter08.ConstancyRemarks
import Poincare.SimonGMT.Chapter08.TangentRescaling
import Poincare.SimonGMT.Chapter08.TangentRadialRigidity
import Poincare.SimonGMT.Chapter08.TangentScalingCounterexample
import Poincare.SimonGMT.AppendixA.Foundations
import Poincare.SimonGMT.AppendixB.SimonsInequalities
import Poincare.SimonGMT.AppendixB.LagrangeIdentity
import Poincare.SimonGMT.AppendixB.ConeDefect

/-!
# Simon's *Introduction to GMT*

This is the compatibility and aggregate entry point for the ongoing full-book
formalization. The `Poincare.SimonGMT.*` modules use Mathlib's genuine analysis
and measure-theory foundations. The older `SimonGMT` namespace retained below
is an initial abstract experiment and does not count toward source coverage.

In that legacy experiment, the range `[0, infinity]` is represented by the
`MeasureValue` contract:
an ordered additive commutative monoid equipped with a countable-series
operation.  Every theorem below is proved uniformly for every implementation
of that contract.  The contract deliberately has no order-continuity law for
`series`, so the finite part of Lemma 1.6 and Remark 1.7 is proved below while
the countable limiting step is left outside the claimed scope.
-/

namespace SimonGMT

universe u v

/-! ## Sets and sigma-algebras -/

/-- A set is represented by its membership predicate. -/
abbrev Subset (X : Type u) := X -> Prop

namespace Subset

/-- The empty subset. -/
def empty : Subset X := fun _ => False

/-- The full subset. -/
def univ : Subset X := fun _ => True

/-- Set-theoretic inclusion. -/
def Included (A B : Subset X) : Prop := forall x, A x -> B x

/-- Set union. -/
def union (A B : Subset X) : Subset X := fun x => A x \/ B x

/-- Set intersection. -/
def inter (A B : Subset X) : Subset X := fun x => A x /\ B x

/-- Set difference. -/
def diff (A B : Subset X) : Subset X := fun x => A x /\ Not (B x)

/-- Set complement relative to the ambient type. -/
def compl (A : Subset X) : Subset X := fun x => Not (A x)

/-- Countable union. -/
def iUnion (A : Nat -> Subset X) : Subset X := fun x => exists n, A n x

/-- Countable intersection. -/
def iInter (A : Nat -> Subset X) : Subset X := fun x => forall n, A n x

/-- Union of the first `n` members of a family. -/
def prefixUnion (A : Nat -> Subset X) : Nat -> Subset X
  | 0 => empty
  | n + 1 => union (prefixUnion A n) (A n)

infix:50 " ⊆ₛ " => Included
infixl:65 " ∪ₛ " => union
infixl:70 " ∩ₛ " => inter
infixl:70 " ∖ₛ " => diff
postfix:max "ᶜₛ" => compl
notation "∅ₛ" => empty
notation "Uₛ" => univ
notation "⋃ₛ" => iUnion
notation "⋂ₛ" => iInter

/-- Predicate extensionality for the set representation. -/
theorem ext {A B : Subset X} (h : forall x, A x <-> B x) : A = B := by
  funext x
  exact propext (h x)

theorem included_refl (A : Subset X) : A ⊆ₛ A := by
  intro _ hx
  exact hx

theorem included_trans {A B C : Subset X} (hAB : A ⊆ₛ B) (hBC : B ⊆ₛ C) : A ⊆ₛ C := by
  intro x hx
  exact hBC x (hAB x hx)

@[simp] theorem compl_compl (A : Subset X) : (Aᶜₛ)ᶜₛ = A := by
  apply ext
  intro x
  classical
  by_cases hx : A x <;> simp [compl, hx]

@[simp] theorem diff_empty (A : Subset X) : A ∖ₛ ∅ₛ = A := by
  apply ext
  intro x
  simp [diff, empty]

@[simp] theorem inter_empty (A : Subset X) : A ∩ₛ ∅ₛ = ∅ₛ := by
  apply ext
  intro x
  simp [inter, empty]

@[simp] theorem empty_inter (A : Subset X) : ∅ₛ ∩ₛ A = ∅ₛ := by
  apply ext
  intro x
  simp [inter, empty]

@[simp] theorem inter_univ (A : Subset X) : A ∩ₛ Uₛ = A := by
  apply ext
  intro x
  simp [inter, univ]

@[simp] theorem univ_inter (A : Subset X) : Uₛ ∩ₛ A = A := by
  apply ext
  intro x
  simp [inter, univ]

@[simp] theorem diff_univ (A : Subset X) : A ∖ₛ Uₛ = ∅ₛ := by
  apply ext
  intro x
  simp [diff, univ, empty]

@[simp] theorem diff_compl (A B : Subset X) : A ∖ₛ (Bᶜₛ) = A ∩ₛ B := by
  apply ext
  intro x
  classical
  by_cases hx : B x <;> simp [diff, compl, inter, hx]

@[simp] theorem inter_compl (A B : Subset X) : A ∩ₛ (Bᶜₛ) = A ∖ₛ B := by
  apply ext
  intro x
  simp [diff, compl, inter]

@[simp] theorem diff_self (A : Subset X) : A ∖ₛ A = ∅ₛ := by
  apply ext
  intro x
  simp [diff, empty]

@[simp] theorem inter_self (A : Subset X) : A ∩ₛ A = A := by
  apply ext
  intro x
  simp [inter]

@[simp] theorem union_empty (A : Subset X) : A ∪ₛ ∅ₛ = A := by
  apply ext
  intro x
  simp [union, empty]

@[simp] theorem empty_union (A : Subset X) : ∅ₛ ∪ₛ A = A := by
  apply ext
  intro x
  simp [union, empty]

theorem diff_included (S A : Subset X) : S ∖ₛ A ⊆ₛ S := by
  intro _ hx
  exact hx.1

theorem inter_included_left (S A : Subset X) : S ∩ₛ A ⊆ₛ S := by
  intro _ hx
  exact hx.1

theorem inter_included_right (S A : Subset X) : S ∩ₛ A ⊆ₛ A := by
  intro _ hx
  exact hx.2

theorem inter_mono_left {A B : Subset X} (h : A ⊆ₛ B) (S : Subset X) : S ∩ₛ A ⊆ₛ S ∩ₛ B := by
  intro x hx
  exact And.intro hx.1 (h x hx.2)

theorem cut_union (S A : Subset X) : (S ∖ₛ A) ∪ₛ (S ∩ₛ A) = S := by
  apply ext
  intro x
  classical
  by_cases hx : A x <;> simp [union, diff, inter, hx]

theorem diff_union (S A B : Subset X) : S ∖ₛ (A ∪ₛ B) = (S ∖ₛ A) ∖ₛ B := by
  apply ext
  intro x
  constructor
  · intro hx
    exact ⟨⟨hx.1, fun ha => hx.2 (Or.inl ha)⟩, fun hb => hx.2 (Or.inr hb)⟩
  · intro hx
    exact ⟨hx.1.1, fun hab => hab.elim hx.1.2 hx.2⟩

theorem union_cut_diff (S A B : Subset X) :
    (S ∩ₛ (A ∪ₛ B)) ∖ₛ A = (S ∖ₛ A) ∩ₛ B := by
  apply ext
  intro x
  classical
  by_cases ha : A x <;> simp [diff, inter, union, ha]

theorem union_cut_inter (S A B : Subset X) :
    (S ∩ₛ (A ∪ₛ B)) ∩ₛ A = S ∩ₛ A := by
  apply ext
  intro x
  constructor
  · intro hx
    exact ⟨hx.1.1, hx.2⟩
  · intro hx
    exact ⟨⟨hx.1, Or.inl hx.2⟩, hx.2⟩

theorem inter_diff_assoc (Y S A : Subset X) : Y ∩ₛ (S ∖ₛ A) = (Y ∩ₛ S) ∖ₛ A := by
  apply ext
  intro x
  simp [inter, diff, and_assoc]

theorem inter_assoc (Y S A : Subset X) : Y ∩ₛ (S ∩ₛ A) = (Y ∩ₛ S) ∩ₛ A := by
  apply ext
  intro x
  simp [inter, and_assoc]

theorem inter_iUnion_cover {A : Subset X} {C : Nat -> Subset X}
    (h : A ⊆ₛ ⋃ₛ C) (Y : Subset X) :
    Y ∩ₛ A ⊆ₛ ⋃ₛ (fun n => Y ∩ₛ C n) := by
  intro x hx
  obtain ⟨n, hn⟩ := h x hx.2
  exact ⟨n, hx.1, hn⟩

/-- Membership in a finite prefix union, stated without a finite-set library. -/
theorem mem_prefixUnion_iff (A : Nat -> Subset X) (n : Nat) (x : X) :
    prefixUnion A n x ↔ ∃ i, i < n ∧ A i x := by
  induction n with
  | zero => simp [prefixUnion, empty]
  | succ n ih =>
      constructor
      · intro hx
        cases hx with
        | inl hx =>
            obtain ⟨i, hi, hAi⟩ := ih.mp hx
            exact ⟨i, Nat.lt_succ_of_lt hi, hAi⟩
        | inr hx => exact ⟨n, Nat.lt_succ_self n, hx⟩
      · rintro ⟨i, hi, hAi⟩
        by_cases hin : i = n
        · exact Or.inr (hin ▸ hAi)
        · exact Or.inl (ih.mpr ⟨i, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hin, hAi⟩)

end Subset

open Subset

/-
Simon, Chapter 1, Definition 1.4 and Remark 1.5 (printed page 2): a
sigma-algebra contains the empty set and is closed under complement and
countable union.
-/
/-- A sigma-algebra on an abstract space, matching Simon Definition 1.4. -/
structure SigmaAlgebra (X : Type u) where
  sets : Subset (Subset X)
  empty_mem : sets ∅ₛ
  compl_mem : forall {A}, sets A -> sets (Aᶜₛ)
  iUnion_mem : forall A : Nat -> Subset X, (forall n, sets (A n)) -> sets (⋃ₛ A)

namespace SigmaAlgebra

/-- The whole space belongs to every sigma-algebra (Simon 1.4(1)). -/
theorem univ_mem (S : SigmaAlgebra X) : S.sets Uₛ := by
  have h := S.compl_mem S.empty_mem
  have heq : (∅ₛ : Subset X)ᶜₛ = Uₛ := by
    apply Subset.ext
    intro x
    simp [Subset.compl, Subset.empty, Subset.univ]
  rw [heq] at h
  exact h

/-- Sigma-algebras are closed under countable intersection (Simon Remark 1.5(1)). -/
theorem iInter_mem (S : SigmaAlgebra X) (A : Nat -> Subset X)
    (hA : forall n, S.sets (A n)) : S.sets (⋂ₛ A) := by
  have hc : S.sets (⋃ₛ (fun n => (A n)ᶜₛ)) :=
    S.iUnion_mem (fun n => (A n)ᶜₛ) (fun n => S.compl_mem (hA n))
  have hcc := S.compl_mem hc
  have heq : (⋃ₛ (fun n => (A n)ᶜₛ))ᶜₛ = ⋂ₛ A := by
    apply Subset.ext
    intro x
    change (Not (Exists fun n => Not (A n x))) <-> (forall n, A n x)
    classical
    constructor
    · intro hn n
      apply Classical.byContradiction
      intro han
      exact hn ⟨n, han⟩
    · intro hall hex
      obtain ⟨n, hn⟩ := hex
      exact hn (hall n)
  rw [heq] at hcc
  exact hcc

/-- Intersection construction: the smallest sigma-algebra containing `G`.

This is Simon Remark 1.5(2), made impredicative so it needs no choice of an
enumeration of generated sets.
-/
def generated (G : Subset (Subset X)) : SigmaAlgebra X where
  sets A := forall S : SigmaAlgebra X, (forall B, G B -> S.sets B) -> S.sets A
  empty_mem := by
    intro S _
    exact S.empty_mem
  compl_mem := by
    intro A hA S hG
    exact S.compl_mem (hA S hG)
  iUnion_mem := by
    intro A hA S hG
    exact S.iUnion_mem A (fun n => hA n S hG)

/-- Every generator belongs to the sigma-algebra it generates. -/
theorem subset_generated (G : Subset (Subset X)) {A : Subset X} (hA : G A) :
    (generated G).sets A := by
  intro S hG
  exact hG A hA

/-- Minimality of the generated sigma-algebra. -/
theorem generated_minimal (G : Subset (Subset X)) (S : SigmaAlgebra X)
    (hG : forall A, G A -> S.sets A) {A : Subset X}
    (hA : (generated G).sets A) : S.sets A :=
  hA S hG

end SigmaAlgebra

/-! ## Outer measures and Caratheodory measurability -/

/-- Algebraic interface for the extended nonnegative values used by an outer
measure.  `series` supplies the countable sum in Simon equation (1.1).

`series_pair` records the only evaluation law needed for the finite consequences
proved in this file.  Concrete implementations may use extended reals, extended
rationals, or any other ordered additive model.
-/
class MeasureValue (V : Type v) extends LE V, Zero V, Add V where
  le_refl : forall a : V, a <= a
  le_trans : forall {a b c : V}, a <= b -> b <= c -> a <= c
  le_antisymm : forall {a b : V}, a <= b -> b <= a -> a = b
  zero_le : forall a : V, 0 <= a
  add_zero : forall a : V, a + 0 = a
  zero_add : forall a : V, 0 + a = a
  add_comm : forall a b : V, a + b = b + a
  add_assoc : forall a b c : V, a + b + c = a + (b + c)
  series : (Nat -> V) -> V
  series_pair : forall a b : V,
    series (fun n => match n with | 0 => a | 1 => b | _ => 0) = a + b

/-- The countable series operation of a measure-value system. -/
def measureSeries [MeasureValue V] (f : Nat -> V) : V := MeasureValue.series f

/-- Left-associated sum of the first `n` values of a sequence. -/
def measurePrefixSum [MeasureValue V] (f : Nat -> V) : Nat -> V
  | 0 => 0
  | n + 1 => measurePrefixSum f n + f n

/-
Simon, Chapter 1, Section 1, equation (1.1), printed pages 1--2: an outer
measure is zero on the empty set, monotone, and countably subadditive.
-/
/-- An outer measure on an abstract space, with its codomain made explicit. -/
structure OuterMeasure (X : Type u) (V : Type v) [MeasureValue V] where
  toFun : Subset X -> V
  empty : toFun ∅ₛ = 0
  mono : forall {A B}, A ⊆ₛ B -> toFun A <= toFun B
  countable_subadditive : forall (A : Subset X) (C : Nat -> Subset X),
    A ⊆ₛ ⋃ₛ C -> toFun A <= measureSeries (fun n => toFun (C n))

instance [MeasureValue V] : CoeFun (OuterMeasure X V) (fun _ => Subset X -> V) where
  coe mu := mu.toFun

namespace OuterMeasure

/-- Finite subadditivity, proved from Simon equation (1.1). -/
theorem union_le [MeasureValue V] (mu : OuterMeasure X V) (A B : Subset X) :
    mu (A ∪ₛ B) <= mu A + mu B := by
  let C : Nat -> Subset X := fun n => match n with
    | 0 => A
    | 1 => B
    | _ => ∅ₛ
  have hcover : A ∪ₛ B ⊆ₛ ⋃ₛ C := by
    intro x hx
    cases hx with
    | inl ha => exact ⟨0, ha⟩
    | inr hb => exact ⟨1, hb⟩
  have h := mu.countable_subadditive (A ∪ₛ B) C hcover
  have hseries : measureSeries (fun n => mu (C n)) = mu A + mu B := by
    rw [show (fun n => mu (C n)) =
        (fun n => match n with | 0 => mu A | 1 => mu B | _ => 0) by
      funext n
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n => simp [C, mu.empty]]
    exact MeasureValue.series_pair (mu A) (mu B)
  rw [hseries] at h
  exact h

/-
Simon, Chapter 1, Definition 1.2, printed page 2: `A` is measurable when it
cuts every test set additively.
-/
/-- Caratheodory measurability for an outer measure. -/
def IsMeasurable [MeasureValue V] (mu : OuterMeasure X V) (A : Subset X) : Prop :=
  forall S, mu S = mu (S ∖ₛ A) + mu (S ∩ₛ A)

/-- Measurability is invariant under complement, as observed after Simon
Definition 1.2 (printed page 2). -/
theorem measurable_compl [MeasureValue V] (mu : OuterMeasure X V) {A : Subset X}
    (hA : mu.IsMeasurable A) : mu.IsMeasurable (Aᶜₛ) := by
  intro S
  rw [Subset.diff_compl, Subset.inter_compl]
  rw [MeasureValue.add_comm]
  exact hA S

/-- The empty set is Caratheodory measurable. -/
theorem measurable_empty [MeasureValue V] (mu : OuterMeasure X V) :
    mu.IsMeasurable ∅ₛ := by
  intro S
  rw [Subset.diff_empty, Subset.inter_empty, mu.empty, MeasureValue.add_zero]

/-- The full set is Caratheodory measurable. -/
theorem measurable_univ [MeasureValue V] (mu : OuterMeasure X V) :
    mu.IsMeasurable Uₛ := by
  have h := mu.measurable_compl mu.measurable_empty
  have heq : (∅ₛ : Subset X)ᶜₛ = Uₛ := by
    apply Subset.ext
    intro x
    simp [Subset.compl, Subset.empty, Subset.univ]
  rw [heq] at h
  exact h

/-- The finite-union part of Caratheodory's Lemma 1.6, proved by cutting first
with `A` and then with `B`. -/
theorem measurable_union [MeasureValue V] (mu : OuterMeasure X V) {A B : Subset X}
    (hA : mu.IsMeasurable A) (hB : mu.IsMeasurable B) :
    mu.IsMeasurable (A ∪ₛ B) := by
  intro S
  have hcutB := hB (S ∖ₛ A)
  have hcutA := hA (S ∩ₛ (A ∪ₛ B))
  rw [Subset.union_cut_diff, Subset.union_cut_inter] at hcutA
  rw [Subset.diff_union, hcutA]
  calc
    mu S = mu (S ∖ₛ A) + mu (S ∩ₛ A) := hA S
    _ = (mu ((S ∖ₛ A) ∖ₛ B) + mu ((S ∖ₛ A) ∩ₛ B)) + mu (S ∩ₛ A) := by
      rw [hcutB]
    _ = mu ((S ∖ₛ A) ∖ₛ B) +
        (mu ((S ∖ₛ A) ∩ₛ B) + mu (S ∩ₛ A)) := by
      rw [MeasureValue.add_assoc]

/-- Caratheodory measurable sets are closed under intersection. -/
theorem measurable_inter [MeasureValue V] (mu : OuterMeasure X V) {A B : Subset X}
    (hA : mu.IsMeasurable A) (hB : mu.IsMeasurable B) :
    mu.IsMeasurable (A ∩ₛ B) := by
  have hc := mu.measurable_union (mu.measurable_compl hA) (mu.measurable_compl hB)
  have hcc := mu.measurable_compl hc
  have heq : ((Aᶜₛ) ∪ₛ (Bᶜₛ))ᶜₛ = A ∩ₛ B := by
    apply Subset.ext
    intro x
    classical
    by_cases ha : A x <;> by_cases hb : B x <;>
      simp [Subset.compl, Subset.union, Subset.inter, ha, hb]
  rw [heq] at hcc
  exact hcc

/-- Caratheodory measurable sets are closed under set difference. -/
theorem measurable_diff [MeasureValue V] (mu : OuterMeasure X V) {A B : Subset X}
    (hA : mu.IsMeasurable A) (hB : mu.IsMeasurable B) :
    mu.IsMeasurable (A ∖ₛ B) := by
  have h := mu.measurable_inter hA (mu.measurable_compl hB)
  rw [Subset.inter_compl] at h
  exact h

/-
Simon, immediately before Lemma 1.6 (printed page 2): every subset of outer
measure zero is measurable.
-/
/-- Every null set is Caratheodory measurable. -/
theorem null_measurable [MeasureValue V] (mu : OuterMeasure X V) {A : Subset X}
    (hzero : mu A = 0) : mu.IsMeasurable A := by
  intro S
  have hInterLe : mu (S ∩ₛ A) <= mu A :=
    mu.mono (Subset.inter_included_right S A)
  have hInterZero : mu (S ∩ₛ A) = 0 := by
    apply MeasureValue.le_antisymm
    · simpa [hzero] using hInterLe
    · exact MeasureValue.zero_le _
  have hForward : mu S <= mu (S ∖ₛ A) + mu (S ∩ₛ A) := by
    have h := mu.union_le (S ∖ₛ A) (S ∩ₛ A)
    rw [Subset.cut_union] at h
    exact h
  apply MeasureValue.le_antisymm hForward
  rw [hInterZero, MeasureValue.add_zero]
  exact mu.mono (Subset.diff_included S A)

/-- Additivity on two disjoint measurable sets, the finite case of Simon
Remark 1.7 (printed pages 2--4). -/
theorem add_of_disjoint [MeasureValue V] (mu : OuterMeasure X V) {A B : Subset X}
    (hA : mu.IsMeasurable A) (hDisjoint : forall x, A x -> B x -> False) :
    mu (A ∪ₛ B) = mu A + mu B := by
  have h := hA (A ∪ₛ B)
  have hdiff : (A ∪ₛ B) ∖ₛ A = B := by
    apply Subset.ext
    intro x
    constructor
    · intro hx
      cases hx.1 with
      | inl ha => exact False.elim (hx.2 ha)
      | inr hb => exact hb
    · intro hb
      exact ⟨Or.inr hb, fun ha => hDisjoint x ha hb⟩
  have hinter : (A ∪ₛ B) ∩ₛ A = A := by
    apply Subset.ext
    intro x
    constructor
    · exact fun hx => hx.2
    · exact fun ha => ⟨Or.inl ha, ha⟩
  rw [hdiff, hinter, MeasureValue.add_comm] at h
  exact h

/-- Every finite prefix of measurable sets is measurable.  This packages the
induction in Step 3 of Simon's proof of Lemma 1.6 (printed page 4). -/
theorem measurable_prefixUnion [MeasureValue V] (mu : OuterMeasure X V)
    (A : Nat -> Subset X) (hA : ∀ i, mu.IsMeasurable (A i)) :
    ∀ n, mu.IsMeasurable (Subset.prefixUnion A n)
  | 0 => mu.measurable_empty
  | n + 1 => mu.measurable_union (mu.measurable_prefixUnion A hA n) (hA n)

/-- Finite additivity for every prefix of a pairwise-disjoint measurable
family.  This is the exact finite identity used before the countable limiting
argument in Simon Lemma 1.6 and Remark 1.7. -/
theorem measure_prefixUnion_of_pairwise_disjoint [MeasureValue V]
    (mu : OuterMeasure X V) (A : Nat -> Subset X)
    (hA : ∀ i, mu.IsMeasurable (A i))
    (hDisjoint : ∀ i j, i ≠ j → ∀ x, A i x → A j x → False) :
    ∀ n, mu (Subset.prefixUnion A n) = measurePrefixSum (fun i => mu (A i)) n
  | 0 => mu.empty
  | n + 1 => by
      have hPrefix : mu.IsMeasurable (Subset.prefixUnion A n) :=
        mu.measurable_prefixUnion A hA n
      have hSep : ∀ x, Subset.prefixUnion A n x → A n x → False := by
        intro x hx hAn
        obtain ⟨i, hi, hAi⟩ := (Subset.mem_prefixUnion_iff A n x).mp hx
        exact hDisjoint i n (Nat.ne_of_lt hi) x hAi hAn
      rw [measurePrefixSum]
      rw [Subset.prefixUnion]
      rw [mu.add_of_disjoint hPrefix hSep]
      rw [mu.measure_prefixUnion_of_pairwise_disjoint A hA hDisjoint n]

/-
Simon equation (1.12), printed page 5: restriction to `Y` is defined by
`(mu | Y)(Z) = mu(Y intersection Z)`.
-/
/-- Restriction of an outer measure to an arbitrary subset. -/
def restrict [MeasureValue V] (mu : OuterMeasure X V) (Y : Subset X) : OuterMeasure X V where
  toFun Z := mu (Y ∩ₛ Z)
  empty := by
    rw [Subset.inter_empty, mu.empty]
  mono := by
    intro A B hAB
    exact mu.mono (Subset.inter_mono_left hAB Y)
  countable_subadditive := by
    intro A C hcover
    exact mu.countable_subadditive (Y ∩ₛ A) (fun n => Y ∩ₛ C n)
      (Subset.inter_iUnion_cover hcover Y)

/-- Evaluation rule for restriction (Simon equation 1.12). -/
@[simp] theorem restrict_apply [MeasureValue V] (mu : OuterMeasure X V)
    (Y Z : Subset X) : mu.restrict Y Z = mu (Y ∩ₛ Z) := rfl

/-- Every `mu`-measurable set stays measurable for `mu` restricted to an
arbitrary `Y`, as noted immediately after Simon equation (1.12). -/
theorem measurable_restrict [MeasureValue V] (mu : OuterMeasure X V)
    (Y : Subset X) {A : Subset X} (hA : mu.IsMeasurable A) :
    (mu.restrict Y).IsMeasurable A := by
  intro S
  change mu (Y ∩ₛ S) = mu (Y ∩ₛ (S ∖ₛ A)) + mu (Y ∩ₛ (S ∩ₛ A))
  rw [Subset.inter_diff_assoc, Subset.inter_assoc]
  exact hA (Y ∩ₛ S)

/-
Simon, Chapter 1, Definition following equation (1.9), printed page 4.
-/
/-- Regularity of an outer measure: every set has a measurable hull of the
same outer measure (Simon, printed page 4). -/
def IsRegular [MeasureValue V] (mu : OuterMeasure X V) : Prop :=
  forall A : Subset X, exists B : Subset X,
    A ⊆ₛ B /\ mu.IsMeasurable B /\ mu B = mu A

end OuterMeasure

end SimonGMT
