import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Simon, *Introduction to Geometric Measure Theory*, Chapter 7 "Area Minimizing Currents"
(printed pp. 181–204)

Frozen contract.  Currents, boundary, mass, support and weak convergence are the clean SimonGMT
objects of `Poincare.SimonGMT.Chapter06`: `GeometricCurrentOn U n` (Simon 6.2.1), `T.boundary`
(6.2.3), `T.massOn W` = `M_W(T)` (6.2.5, Euclidean coefficient norm), `T.mass` (6.2.4),
`T.support` (6.2.11), `WeaklyConvergesOn` (6.2.13), and the proper affine push-forward
`GeometricCurrentOn.affinePushforward` (6.2.23).  Everything else (integer multiplicity currents,
minimizing currents, densities, blow-ups, tangent cones, `reg T`, `sing T`, the associated
varifold) is defined below from primitive data.  `Hⁿ` is Mathlib's normalized `μHE[n]`; null-set
statements use Mathlib's `μH[s]` (same null sets as Simon's `Hˢ`).

**Conventions.**  The ambient space is `ℝ^{n+k}` (`Euclid (n + k)`); when a submanifold `N` is
present it has dimension `n + ℓ`, `ℓ ≤ k` (Simon writes `N^{n+ℓ} ⊂ ℝ^{n+ℓ}`, `ℓ ≤ k`, a
misprint for `ℝ^{n+k}`; `N = ℝ^{n+k}` is the case `ℓ = k`).  For an `n`-current, `∂T = 0`,
`∂S = ∂T`, `spt ∂T`, `M_W(∂T)` are read with Simon's convention `∂T = 0` if `n = 0` (6.2.3).
-/

open Filter Function Set MeasureTheory Metric
open scoped ENNReal Topology

namespace GMT.Ch07

open Poincare.SimonGMT.Chapter06
open Poincare.SimonGMT.Chapter03 (CountablyRectifiable HasApproximateTangentSpaceAt)

noncomputable section

/-- Euclidean space `ℝᴾ`. -/
abbrev Euclid (P : ℕ) := EuclideanSpace ℝ (Fin P)

variable {P : ℕ}

/-! ## Multivectors and integer multiplicity currents (Simon Ch. 6, §1 and 3.1) -/

/-- `n`-vectors `Λₙ(ℝᴾ)`, realized as the dual of `n`-covectors (Simon 6.1, `Λₙ ≅ (Λⁿ)*`);
`ξ α` is the pairing `⟨α, ξ⟩` of Simon (6.1.7). -/
abbrev MultiVector (P n : ℕ) := Covector (Euclid P) n →L[ℝ] ℝ

/-- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of the subspace `Q`, i.e.
`⟨α, ξ⟩ = ±α(τ₁, …, τₙ)` (Simon 6.1.1, 6.1.7; 6.2.2).  The sign matters only for `n = 0`. -/
def IsUnitOrientationOf {n : ℕ} (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) : Prop :=
  ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (range τ) = Q ∧
    ((∀ α : Covector (Euclid P) n, ξ α = α τ) ∨ ∀ α : Covector (Euclid P) n, ξ α = -α τ)

/-- Simon Ch. 6, Definition 3.1 (p. 146): a triple `(M, θ, ξ)` in `U`.  `M ⊆ U` is
`Hⁿ`-measurable (taken Borel; this loses nothing, `Hⁿ⌞M` being σ-finite) and countably
`n`-rectifiable; `θ` is positive integer-valued on `M` and locally `Hⁿ`-integrable in `U`; `ξ` is
`Hⁿ`-measurable and, `Hⁿ`-a.e. on `M`, orients the approximate tangent space `TₓM`
(Ch. 3, 1.4). -/
structure IMRep (U : Set (Euclid P)) (n : ℕ) where
  carrier : Set (Euclid P)
  mult : Euclid P → ℕ
  orient : Euclid P → MultiVector P n
  measurableSet_carrier : MeasurableSet carrier
  carrier_subset : carrier ⊆ U
  rectifiable : CountablyRectifiable n carrier
  measurable_mult : Measurable mult
  mult_pos : ∀ x ∈ carrier, 0 < mult x
  locallyIntegrable_mult : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
    ∫⁻ x in carrier ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞
  aestronglyMeasurable_orient : AEStronglyMeasurable orient (μHE[n].restrict carrier)
  orients : ∀ᵐ x ∂(μHE[n].restrict carrier), ∃ Q : Submodule ℝ (Euclid P),
    HasApproximateTangentSpaceAt n carrier x Q ∧ IsUnitOrientationOf (orient x) Q

variable {U : Set (Euclid P)} {n : ℕ}

/-- `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)` (Simon 6.3.1 (‡)). -/
def IMRep.action (R : IMRep U n) (ω : DifferentialForm (Euclid P) n) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]

/-- `T = τ(M, θ, ξ)` in `U`. -/
def IMRep.Represents (R : IMRep U n) (T : GeometricCurrentOn U n) : Prop :=
  ∀ ω : TestFormOn U n, T ω = R.action (ω : DifferentialForm (Euclid P) n)

/-- The weight `μ_V = θ Hⁿ⌞M` of the associated varifold `V = v(M, θ)`; it equals the mass
measure `μ_T` of `T = τ(M, θ, ξ)` (Simon 6.3.2(3), 4.1.1). -/
def IMRep.measure (R : IMRep U n) : Measure (Euclid P) :=
  (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞)

/-- Simon 6.3.1: `T` is an integer multiplicity (rectifiable) current. -/
def IsIntegerMultiplicity (T : GeometricCurrentOn U n) : Prop :=
  ∃ R : IMRep U n, R.Represents T

/-- Difference of currents (needed for `spt(S − T)` in 7.1.1). -/
instance : Sub (GeometricCurrentOn U n) where
  sub S T :=
    { toCurrent := S.toCurrent - T.toCurrent
      continuous' := fun ωs h => by
        simpa using (S.continuous' ωs h).sub (T.continuous' ωs h) }

/-! ## Boundary conventions in arbitrary degree -/

/-- `∂S = ∂T` in `U` (vacuous for `n = 0`, where `∂ = 0`). -/
def SameBoundary : {n : ℕ} → GeometricCurrentOn U n → GeometricCurrentOn U n → Prop
  | 0, _, _ => True
  | _ + 1, S, T => S.boundary = T.boundary

/-- `∂T = 0` in `U`. -/
def BoundaryVanishes : {n : ℕ} → GeometricCurrentOn U n → Prop
  | 0, _ => True
  | _ + 1, T => T.boundary = 0

/-- `spt ∂T` (empty for `n = 0`). -/
def boundarySupport : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P)
  | 0, _ => ∅
  | _ + 1, T => T.boundary.support

/-- `M_W(∂T)` (zero for `n = 0`). -/
def boundaryMassOn : {n : ℕ} → GeometricCurrentOn U n → Set (Euclid P) → ℝ≥0∞
  | 0, _, _ => 0
  | _ + 1, T, W => T.boundary.massOn W

/-! ## Minimizing currents (Simon 7.1.1) -/

/-- `W ⊂⊂ U`: `closure W` is a compact subset of `U`. -/
def CompactlyContained (W U : Set (Euclid P)) : Prop :=
  IsCompact (closure W) ∧ closure W ⊆ U

/-- **Simon 7.1.1 (p. 181).**  The integer multiplicity `T ∈ 𝒟ₙ(U)` is *minimizing in `A`*
(`A ⊆ U`): `M_W(T) ≤ M_W(S)` whenever `W ⊂⊂ U` is open, `S ∈ 𝒟ₙ(U)` is integer multiplicity,
`∂S = ∂T` in `U` and `spt(S − T)` is a compact subset of `A ∩ W`.  Competitors are integer
multiplicity, as required by Remark 7.2.2(1) and the proofs of 7.1.4 and 7.2.4. -/
def IsMinimizingIn (T : GeometricCurrentOn U n) (A : Set (Euclid P)) : Prop :=
  IsIntegerMultiplicity T ∧
    ∀ (W : Set (Euclid P)) (S : GeometricCurrentOn U n), IsOpen W → CompactlyContained W U →
      IsIntegerMultiplicity S → SameBoundary S T → IsCompact (S - T).support →
        (S - T).support ⊆ A ∩ W → T.massOn W ≤ S.massOn W

/-! ## Densities, blow-ups, tangent cones (Simon 7.3) -/

/-- `ωₙ`, the Lebesgue measure of the unit ball of `ℝⁿ`. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ := volume (ball (0 : Euclid n) 1)

/-- `Θⁿ(μ_T, x) = θ`: `(ωₙρⁿ)⁻¹ μ_T(B_ρ(x)) → θ` as `ρ ↓ 0`, with `μ_T(B_ρ(x)) = M_{B_ρ(x)}(T)`
for small `ρ` (Simon 6.2.8; open and closed balls give the same limit). -/
def HasMassDensity (T : GeometricCurrentOn U n) (x : Euclid P) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ Tendsto (fun ρ : ℝ => T.massOn (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
    (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ))

/-- Value of a current in `U` on an ambient form: `T(ω)` if `ω ∈ 𝒟ⁿ(U)`, else `0`.  Used for
convergence of currents on varying domains (Simon: "`η_{x,λⱼ#}T ⇀ C` in `ℝ^{n+ℓ}`"). -/
def currentEval (T : GeometricCurrentOn U n) (ω : DifferentialForm (Euclid P) n) : ℝ := by
  classical
  exact if h : IsTestForm ω ∧ tsupport ω ⊆ U then T ⟨ω, h⟩ else 0

/-- `Tⱼ ⇀ T` in `V`, for currents `Tⱼ ∈ 𝒟ₙ(Uⱼ)` whose domains eventually contain every compact
subset of `V` (as for blow-ups): `Tⱼ(ω) → T(ω)` for every `ω ∈ 𝒟ⁿ(V)` (Simon 6.2.13). -/
def ConvergesWeakly {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ ω : TestFormOn V n,
    Tendsto (fun j => currentEval (Ts j) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (T ω))

/-- `μ_{Tⱼ} → μ_T` as Radon measures in `V` (Simon 7.2.4, Remark 7.2.5(1)): for all integer
multiplicity representations of the `Tⱼ` and of `T`, `∫ f dμ_{Tⱼ} → ∫ f dμ_T` for every
continuous `f` with compact support in `V`. -/
def MassMeasuresConverge {Us : ℕ → Set (Euclid P)} (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n)
    {V : Set (Euclid P)} (T : GeometricCurrentOn V n) : Prop :=
  ∀ Rs : (j : ℕ) → IMRep (Us j) n, (∀ j, (Rs j).Represents (Ts j)) →
    ∀ R : IMRep V n, R.Represents T →
      ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ V →
        Tendsto (fun j => ∫ x, f x ∂(Rs j).measure) atTop (𝓝 (∫ x, f x ∂R.measure))

/-- The linear part `y ↦ λ⁻¹y` of the dilation `η_{x,λ}`. -/
def dilationCLM (P : ℕ) (lam : ℝ) : Euclid P →L[ℝ] Euclid P :=
  lam⁻¹ • ContinuousLinearMap.id ℝ (Euclid P)

/-- Simon's dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, written `y ↦ −λ⁻¹x + λ⁻¹y`. -/
def dilation (x : Euclid P) (lam : ℝ) : Euclid P → Euclid P :=
  fun y => -(lam⁻¹ • x) + dilationCLM P lam y

/-- The blow-up `η_{x,λ#}T ∈ 𝒟ₙ(η_{x,λ}(U))`, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` (Simon 6.2.23 for
the proper affine diffeomorphism `η_{x,λ}`, `λ ≠ 0`). -/
def blowUp (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : lam ≠ 0) :
    GeometricCurrentOn (dilation x lam '' U) n :=
  (T.restrictDomain (show (fun y => -(lam⁻¹ • x) + dilationCLM P lam y) ⁻¹'
      (dilation x lam '' U) ⊆ U by
    rintro y ⟨z, hz, hzy⟩
    have hzy' : lam⁻¹ • z = lam⁻¹ • y := by
      simpa [dilation, dilationCLM] using hzy
    rwa [← smul_right_injective (Euclid P) (inv_ne_zero hlam) hzy'])).affinePushforward
    (dilationCLM P lam) (-(lam⁻¹ • x)) (by
      convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • x)))).isProperMap using 1
      funext y
      simp [dilationCLM])

/-- `C ∈ 𝒟ₙ(ℝᴾ)` is a cone: `η_{0,λ#}C = C` for every `λ > 0` (Simon 7.3.1(2)). -/
def IsConeCurrent (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∀ (lam : ℝ) (hlam : 0 < lam) (ω : TestFormOn (univ : Set (Euclid P)) n),
    currentEval (blowUp C 0 lam hlam.ne') (ω : DifferentialForm (Euclid P) n) = C ω

/-- Simon 7.3.2(1): `C` is a tangent cone of `T` at `x`, i.e. `η_{x,λⱼ#}T ⇀ C` in `ℝᴾ` for some
sequence `λⱼ > 0`, `λⱼ → 0`. -/
def IsTangentConeAt (T : GeometricCurrentOn U n) (x : Euclid P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) n) : Prop :=
  ∃ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) ∧
    ConvergesWeakly (fun j => blowUp T x (lams j) (hlams j).ne') C

/-- Simon 7.3.2(1): `T` has a (multiplicity `m`) tangent plane at `x`: some tangent cone has
support an `n`-dimensional subspace. -/
def HasTangentPlaneAt (T : GeometricCurrentOn U n) (x : Euclid P) : Prop :=
  ∃ C : GeometricCurrentOn (univ : Set (Euclid P)) n, IsTangentConeAt T x C ∧
    ∃ Q : Submodule ℝ (Euclid P), Module.finrank ℝ Q = n ∧ C.support = (Q : Set (Euclid P))

/-! ## Submanifolds, `reg T`, `sing T` (Simon Ch. 2, §4 and 7.4.1) -/

/-- Simon Ch. 2, §4, (4.1) (p. 55): `M ⊂ ℝᴾ` is a `d`-dimensional (embedded) `Cʳ` submanifold:
each `y ∈ M` has an open `W ∋ y` and a 1:1 `Cʳ` map `ψ : V → W`, `V ⊆ ℝᵈ` open, with
`ψ(V) = W ∩ M`, `ψ` proper, and `Dψ` of rank `d` on `V`. -/
def IsEmbeddedSubmanifold (r d : ℕ) (M : Set (Euclid P)) : Prop :=
  ∀ y ∈ M, ∃ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P),
    IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ r ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
      ∀ z ∈ V, Injective (fderiv ℝ ψ z)

/-- Simon Ch. 2, §4 (p. 55): `T_yM = {γ'(0) : γ ∈ C¹((−1,1); ℝᴾ), γ((−1,1)) ⊆ M, γ(0) = y}`. -/
def tangentSpace (M : Set (Euclid P)) (y : Euclid P) : Set (Euclid P) :=
  {v | ∃ γ : ℝ → Euclid P, ContDiffOn ℝ 1 γ (Ioo (-1) 1) ∧ MapsTo γ (Ioo (-1) 1) M ∧
    γ 0 = y ∧ HasDerivAt γ v 0}

/-- An orientation of the `d`-dimensional submanifold `M` (Simon 6.2.2): `ξ` is continuous on
`M` and `ξ(y) = ±τ₁ ∧ ⋯ ∧ τ_d` for an orthonormal basis `τ` of `T_yM`, for every `y ∈ M`. -/
def IsOrientation (d : ℕ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P d) : Prop :=
  ContinuousOn ξ M ∧ ∀ y ∈ M, ∃ Q : Submodule ℝ (Euclid P),
    (Q : Set (Euclid P)) = tangentSpace M y ∧ IsUnitOrientationOf (ξ y) Q

/-- **Simon 7.4.1 (p. 193)**: `reg T` is the set of `y ∈ spt T` such that, for some `ρ > 0`
(with `B_ρ(y) ⊆ U`), `m ∈ ℤ \ {0}` and embedded `n`-dimensional oriented `C¹` submanifold `M`
(of locally finite `Hⁿ`-measure in `B_ρ(y)`, as `[[M]]` requires, 6.2.2), `T = m[[M]]` in
`B_ρ(y)` (6.2.16), i.e. `T(ω) = m ∫_M ⟨ω, ξ_M⟩ dHⁿ` whenever `spt ω ⊆ B_ρ(y)`.
The point `y` itself must lie on `M` (as in 4.4(8) and the proof of 5.8): otherwise a singular
point could be declared regular by deleting it from `M`, e.g. the vertex of the Simons cone. -/
def regularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  {y | y ∈ T.support ∧ ∃ ρ : ℝ, 0 < ρ ∧ ball y ρ ⊆ U ∧
    ∃ (m : ℤ) (M : Set (Euclid P)) (ξ : Euclid P → MultiVector P n), m ≠ 0 ∧ y ∈ M ∧
      IsEmbeddedSubmanifold 1 n M ∧ IsOrientation n M ξ ∧
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ ball y ρ → μHE[n] (M ∩ K) ≠ ∞) ∧
      ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ ball y ρ →
        T ω = m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]}

/-- **Simon 7.4.1**: `sing T = spt T \ reg T`. -/
def singularSet (T : GeometricCurrentOn U n) : Set (Euclid P) :=
  T.support \ regularSet T

/-! ## The associated varifold `V = v(M, θ)` (Simon Ch. 4, 2.3–2.7 and 3.14) -/

/-- The approximate tangent plane `TₓM` (Ch. 3, 1.4; unique when it exists), `⊥` otherwise. -/
def approxTangentPlane (n : ℕ) (M : Set (Euclid P)) (x : Euclid P) :
    Submodule ℝ (Euclid P) := by
  classical
  exact if h : ∃ Q, HasApproximateTangentSpaceAt n M x Q then h.choose else ⊥

/-- `div_M X(x) = Σⱼ eⱼ · ∇^M Xʲ = trace(p_{TₓM} ∘ DX(x))` (Simon Ch. 4, 2.3). -/
def tangentialDivergence (n : ℕ) (M : Set (Euclid P)) (X : Euclid P → Euclid P)
    (x : Euclid P) : ℝ :=
  LinearMap.trace ℝ (Euclid P)
    ((approxTangentPlane n M x).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)

/-- First variation `δV(X) = ∫_M div_M X dμ_V` of `V = v(M, θ)` (Simon Ch. 4, 2.2). -/
def IMRep.firstVariation (R : IMRep U n) (X : Euclid P → Euclid P) : ℝ :=
  ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x ∂μHE[n]

/-- Simon Ch. 4, 2.6 (computed form, p. 88): `V` is stationary in `U ∩ N`: `δV(X) = 0` for all
`X ∈ C¹_c(U; ℝᴾ)` with `X(x) ∈ TₓN` for every `x ∈ N ∩ U`. -/
def IMRep.IsStationaryAlong (R : IMRep U n) (N : Set (Euclid P)) : Prop :=
  ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
    (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → R.firstVariation X = 0

/-- Simon Ch. 4, 3.14: `V` has generalized mean curvature `H` in `U`
(`∫ div_M X dμ_V = −∫ X · H dμ_V`, `X ∈ C¹_c(U; ℝᴾ)`), with `H` bounded on compact subsets. -/
def IMRep.HasLocallyBoundedMeanCurvature (R : IMRep U n) : Prop :=
  ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧
    (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ᵐ x ∂R.measure, x ∈ K → ‖H x‖ ≤ Λ) ∧
    ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
      R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure

/-! ## Codimension one (Simon 7.5) -/

/-- Simon 7.5 (p. 197): `N ∈ 𝒪`, an oriented embedded `C²` submanifold of dimension `n + 1` with
`(N̄ \ N) ∩ U = ∅` and `N ∩ U ≠ ∅`, with chosen orientation `ξN`. -/
def InClassO (n : ℕ) (U N : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  IsEmbeddedSubmanifold 2 (n + 1) N ∧ IsOrientation (n + 1) N ξN ∧ (closure N \ N) ∩ U = ∅ ∧
    (N ∩ U).Nonempty

/-- Simon 7.5.1: `T = ∂[[E]]` in `U`, where `[[E]](ω) = ∫_E ⟨ω, ξ_N⟩ dH^{n+1}`. -/
def IsBoundaryOfRegion (T : GeometricCurrentOn U n) (E : Set (Euclid P))
    (ξN : Euclid P → MultiVector P (n + 1)) : Prop :=
  ∀ ω : TestFormOn U n,
    T ω = ∫ x in E, ξN x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]

/-! ## Headline results -/

/-- **Simon 7.1.2 (Lemma, pp. 181–182).**  Let `N` be an embedded `C²` `(n+ℓ)`-dimensional
submanifold of `ℝ^{n+k}`, `(N̄ \ N) ∩ U = ∅`.  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`,
`spt T ⊆ N` and `∂T = 0` in `U`, then the associated varifold `V = v(M, θ)` (for any
representation `T = τ(M, θ, ξ)`) is stationary in `N ∩ U` (Ch. 4, 2.6) and has locally bounded
generalized mean curvature in `U` (Ch. 4, 3.14).
*Correction*: `spt T ⊆ N` and `(N̄ \ N) ∩ U = ∅` are implicit in the book (they are part of the
setting of Ch. 4, 2.5–2.6 and of §3); without `spt T ⊆ N` the lemma is false. -/
def MinimizingImpliesStationary : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    T.support ⊆ N → IsMinimizingIn T (N ∩ U) → BoundaryVanishes T →
    ∀ R : IMRep U n, R.Represents T → R.IsStationaryAlong N ∧ R.HasLocallyBoundedMeanCurvature

/-- **Simon 7.2.1 (Lemma, p. 183).**  Let `S ∈ 𝒟_{n−1}(ℝ^{n+ℓ})` be integer multiplicity with
`spt S` compact and `∂S = 0`.  Then there is an integer multiplicity `T ∈ 𝒟ₙ(ℝ^{n+ℓ})` with
`spt T` compact, `∂T = S`, and `M(T) ≤ M(R)` for every integer multiplicity `R` with `spt R`
compact and `∂R = S`.  Here `n = m + 2`: integer multiplicity currents have dimension `≥ 1`
(Ch. 6, §3).  *Correction*: the printed statement omits the conclusion `∂T = S` (proved: `T ∈ 𝓘_S`);
without it `T = 0` would do. -/
def ExistenceOfMinimizingFilling : Prop :=
  ∀ (m ℓ : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 1)),
    IsIntegerMultiplicity S → IsCompact S.support → S.boundary = 0 →
    ∃ T : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsIntegerMultiplicity T ∧ IsCompact T.support ∧ T.boundary = S ∧
      ∀ R : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
        IsIntegerMultiplicity R → IsCompact R.support → R.boundary = S → T.mass ≤ R.mass

/-- **Simon 7.2.4 (Theorem, p. 184).**  If `Tⱼ` are minimizing in `U`,
`supⱼ (M_W(Tⱼ) + M_W(∂Tⱼ)) < ∞` for each open `W ⊂⊂ U`, and `Tⱼ ⇀ T ∈ 𝒟ₙ(U)`, then `T` is
(integer multiplicity, Remark 7.2.5(1), and) minimizing in `U`, and `μ_{Tⱼ} → μ_T` as Radon
measures in `U`. -/
def CompactnessOfMinimizingCurrents : Prop :=
  ∀ (n k : ℕ) (U : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n),
    IsOpen U → (∀ j, IsMinimizingIn (Ts j) U) →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U →
      ⨆ j, ((Ts j).massOn W + boundaryMassOn (Ts j) W) < ∞) →
    WeaklyConvergesOn Ts T → IsMinimizingIn T U ∧ MassMeasuresConverge (Us := fun _ => U) Ts T

/-- **Simon 7.3.1 (Theorem, p. 187).**  `N` as in 7.1.2 (`C²`).  If `T ∈ 𝒟ₙ(U)` is minimizing in
`U ∩ N` and `spt T ⊆ U ∩ N`, then (1) `Θⁿ(μ_T, x)` exists at every `x ∈ U \ spt ∂T` and is upper
semicontinuous there; (2) for `x ∈ spt T \ spt ∂T` and `λⱼ ↓ 0` (any `λⱼ > 0`, `λⱼ → 0`) there
are a subsequence `λⱼ'` and an integer multiplicity `C ∈ 𝒟ₙ(ℝ^{n+k})`, minimizing in `ℝ^{n+k}`,
with `η_{x,λⱼ'#}T ⇀ C`, `μ_{η_{x,λⱼ'#}T} → μ_C`, `η_{0,λ#}C = C` (`λ > 0`) and
`Θⁿ(μ_C, 0) = Θⁿ(μ_T, x)`.
*Correction*: the printed hypothesis "`x ∈ spt T \ spt ∂T`" and "(1) … everywhere in `U`" are
garbled; the monotonicity proof gives (1) on `U \ spt ∂T`, which is what is stated. -/
def DensityAndTangentCones : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N →
    (∃ Θ : Euclid (n + k) → ℝ, (∀ x ∈ U \ boundarySupport T, HasMassDensity T x (Θ x)) ∧
        UpperSemicontinuousOn Θ (U \ boundarySupport T)) ∧
    ∀ x ∈ T.support \ boundarySupport T, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j),
      Tendsto lams atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧
        ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧
        IsMinimizingIn C univ ∧ IsConeCurrent C ∧
        ∃ θ : ℝ, HasMassDensity T x θ ∧ HasMassDensity C 0 θ

/-- **Simon 7.3.3 (Theorem, p. 189).**  `N` as in 7.3.1.  If `T` is minimizing in `U ∩ N`,
`spt T ⊆ U ∩ N` and `∂T = 0` in `U`, then (1) `Θⁿ(μ_T, x) ∈ ℤ` for all `x ∈ U \ E`, where
`H^{n−3+α}(E) = 0` for all `α > 0`; (2) there is `F ⊇ E` with `H^{n−2+α}(F) = 0` for all `α > 0`
such that `T` has a tangent plane at each `x ∈ spt T \ F`.
*Correction*: printed "`F ⊂ E`" must read `F ⊃ E` (non-integer density excludes tangent planes). -/
def IntegerDensityAndTangentPlanes : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∃ E F : Set (Euclid (n + k)), E ⊆ F ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 3 + α] E = 0) ∧
      (∀ x ∈ U \ E, ∃ m : ℤ, HasMassDensity T x m) ∧
      (∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] F = 0) ∧
      ∀ x ∈ T.support \ F, HasTangentPlaneAt T x

/-- **Simon 7.4.2 (Theorem, p. 194).**  If `T ∈ 𝒟ₙ(U)` is integer multiplicity and minimizing in
`U ∩ N` (`N` an embedded `C²` `(n+ℓ)`-submanifold, `(N̄ \ N) ∩ U = ∅`), `spt T ⊆ U ∩ N` and
`∂T = 0` in `U`, then `reg T` is dense in `spt T`. -/
def RegularSetDense : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    T.support ⊆ closure (regularSet T)

/-- **Simon 7.4.3 (Theorem, p. 194)**, for a fixed `N` (`Nᵢ = N`).  Let `Tᵢ, T` be minimizing in
`U ∩ N`, `spt Tᵢ, spt T ⊆ N`, `∂Tᵢ = ∂T = 0` in `U`, `Tᵢ ⇀ T`, with
`supᵢ M_W(Tᵢ) < ∞` for `W ⊂⊂ U`.  If `y ∈ N ∩ U`, `Θⁿ(μ_T, y) = 1`, `y = lim yⱼ`, `yⱼ ∈ spt Tⱼ`,
then `y ∈ reg T` and `yⱼ ∈ reg Tⱼ` for all large `j`.
*Deviations*: the book allows `Nᵢ → N` "in the `C²` sense" (not defined at this point of the
book); we take `Nᵢ = N`.  The local mass bound is the hypothesis of 7.2.4, which the proof uses
for `μ_{Tⱼ} → μ_T`; it is added explicitly. -/
def DensityOneImpliesRegular : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (Ts : ℕ → GeometricCurrentOn U n)
      (T : GeometricCurrentOn U n) (ys : ℕ → Euclid (n + k)) (y : Euclid (n + k)),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    (∀ j, IsMinimizingIn (Ts j) (U ∩ N)) → IsMinimizingIn T (U ∩ N) →
    (∀ j, (Ts j).support ⊆ N) → T.support ⊆ N →
    (∀ j, BoundaryVanishes (Ts j)) → BoundaryVanishes T →
    (∀ W : Set (Euclid (n + k)), IsOpen W → CompactlyContained W U → ⨆ j, (Ts j).massOn W < ∞) →
    WeaklyConvergesOn Ts T → y ∈ N ∩ U → HasMassDensity T y 1 →
    Tendsto ys atTop (𝓝 y) → (∀ j, ys j ∈ (Ts j).support) →
    y ∈ regularSet T ∧ ∀ᶠ j in atTop, ys j ∈ regularSet (Ts j)

/-- **Simon 7.4.4 (Theorem, p. 194).**  If `T` is as in 7.4.2 and `ξ ∈ spt T` has
`Θⁿ(μ_T, ξ) < 2`, then there is `ρ > 0` with `H^{n−2+α}(sing T ∩ B_ρ(ξ)) = 0` for all `α > 0`. -/
def SingularSetSmallWhereDensityBelowTwo : Prop :=
  ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n),
    IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ →
    IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T →
    ∀ ξ ∈ T.support, ∀ θ : ℝ, HasMassDensity T ξ θ → θ < 2 →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 2 + α] (singularSet T ∩ ball ξ ρ) = 0

/-- **Simon 7.4.5 (Theorem, p. 195).**  If `C ∈ 𝒟ₙ(ℝ^{n+k})` is minimizing in `ℝ^{n+k}`, `∂C = 0`,
`C` is a cone, and `spt C ⊆ H̄` for an open half-space `H = {x : v · x > 0}` (`v ≠ 0`, so
`0 ∈ ∂H`), then `spt C ⊆ ∂H`. -/
def HalfSpaceConeLiesInBoundary : Prop :=
  ∀ (n k : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (v : Euclid (n + k)),
    IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → v ≠ 0 →
    C.support ⊆ closure {x | 0 < inner ℝ v x} → C.support ⊆ frontier {x | 0 < inner ℝ v x}

/-- **Simon 7.5.8 (Theorem, p. 200).**  Let `N ∈ 𝒪` (oriented by `ξN`), `E ⊆ N ∩ U`
`H^{n+1}`-measurable, `T = ∂[[E]] ∈ 𝒟ₙ(U)` integer multiplicity and minimizing in `N ∩ U`.  Then
`sing T = ∅` if `n ≤ 6`; `sing T` is locally finite in `U` (finite on compact subsets of `U`) if
`n = 7`; `H^{n−7+α}(sing T) = 0` for all `α > 0` if `n > 7`.  (`N = ℝ^{n+1}` is the case `k = 1`.)
-/
def CodimensionOneRegularity : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    (n ≤ 6 → singularSet T = ∅) ∧
    (n = 7 → ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ U → (singularSet T ∩ K).Finite) ∧
    (7 < n → ∀ α : ℝ, 0 < α → μH[(n : ℝ) - 7 + α] (singularSet T) = 0)

/-- **Simon 7.5.11 (Corollary, p. 202).**  If `T` is as in 7.5.8, `T = τ(M, θ, ξ)`, and
`T₁ ∈ 𝒟ₙ(U)` is obtained by equipping a connected component `M₁` of `reg T` with multiplicity
`1` and the orientation `ξ` of `T`, then `∂T₁ = 0` in `U` and `T₁` is minimizing in `U ∩ N`. -/
def RegularComponentsAreMinimizing : Prop :=
  ∀ (n k : ℕ) (U N E : Set (Euclid (n + k))) (ξN : Euclid (n + k) → MultiVector (n + k) (n + 1))
      (T : GeometricCurrentOn U n),
    IsOpen U → InClassO n U N ξN → MeasurableSet E → E ⊆ N ∩ U → IsBoundaryOfRegion T E ξN →
    IsMinimizingIn T (N ∩ U) →
    ∀ R : IMRep U n, R.Represents T → ∀ y ∈ regularSet T, ∀ T₁ : GeometricCurrentOn U n,
      (∀ ω : TestFormOn U n, T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
        R.orient x ((ω : DifferentialForm (Euclid (n + k)) n) x) ∂μHE[n]) →
      BoundaryVanishes T₁ ∧ IsMinimizingIn T₁ (U ∩ N)

end

/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2

set_option maxHeartbeats 2000000 in
/-- **Simon 7.2.1 (Lemma, p. 183): existence of a minimizing filling.**  Let `P = m + 2 + ℓ` and
let `S ∈ 𝒟_{m+1}(ℝᴾ)` be integer multiplicity with `spt S` compact and `∂S = 0`.  Then some integer
multiplicity `T ∈ 𝒟_{m+2}(ℝᴾ)` with `spt T` compact and `∂T = S` has `M(T) ≤ M(R)` for every
integer multiplicity `R` with `spt R` compact and `∂R = S`.

The class `𝓘_S` of such `R` is nonempty by the cone filling `0 ⨯ S`
(`Submission.emf_exists_cone_filling`).  If `m₀ = inf_{𝓘_S} M` is infinite the cone itself works;
otherwise choose `R_q ∈ 𝓘_S` with `M(R_q) < m₀ + 1/(q+1)`.  The coordinatewise map
`f(x)ᵢ = ∫₀^{xᵢ} h` (`h` a bump equal to `1` on `[-a, a]`) is `C^∞`, `1`-Lipschitz, the identity on
`B_a(0) ⊇ spt S`, and has bounded image.  Its push-forwards `f_# R_q`
(`Submission.dtc_bc_lc_pushforward`) are integer multiplicity, supported in a fixed ball, and
satisfy `M(f_# R_q) ≤ M(R_q)`.  Moreover `∂ f_# R_q = S`, by the push-forward integral formula,
`d ∘ f^# = f^# ∘ d`, a cut-off, and the vanishing a.e. of the orientation of `R_q` off `spt R_q`
(from `Submission.dtc_vanish_off_support`).  Uniform mass and support bounds give a weakly
convergent subsequence, by a diagonal argument over test forms dense in `C(K, Λⁿ)`.  Federer–Fleming
closure (`Submission.cmc_closure_and_boundary_rectifiability`, using `M(S) < ∞`) makes the limit
`T` integer multiplicity.  `spt T` stays in the ball, `∂T = S` because `∂` is weakly continuous,
and lower semicontinuity of mass gives `M(T) ≤ m₀ ≤ M(R)`. -/
theorem Submission.existence_of_minimizing_filling : ExistenceOfMinimizingFilling := by
  -- (A) coordinates of covectors: `α v = Σ_J (∏ᵢ vᵢ(Jᵢ)) α(e_{J₁}, …, e_{Jₙ})`
  have emfA_expand : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (v : Fin n → Euclid P), α v = ∑ J : Fin n → Fin P, (∏ i, v i (J i)) * α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) := by
    intro P n α v
    have hv : v = fun i => ∑ k, v i k • EuclideanSpace.basisFun (Fin P) ℝ k := by
      funext i
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (v i)]
      simp only [EuclideanSpace.basisFun_repr]
    conv_lhs => rw [hv]
    rw [α.map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [α.map_smul_univ (fun i => v i (J i)) (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))]
    rfl
  -- (A) `|α(e_J)| ≤ |α|` for the Euclidean coefficient norm (sort `J` by a permutation)
  have emfA_basis_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (J : Fin n → Fin P), |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))| ≤ covectorEuclideanNorm α := by
    intro P n α J
    classical
    by_cases hJ : Function.Injective J
    · set σ := Tuple.sort J with hσ
      have hmono : Monotone (J ∘ σ) := Tuple.monotone_sort J
      have hsm : StrictMono (J ∘ σ) := hmono.strictMono_of_injective (hJ.comp σ.injective)
      have hperm : α (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((J ∘ σ) i)) =
          Equiv.Perm.sign σ • α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) :=
        α.toAlternatingMap.map_perm (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) σ
      have habs : |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))| =
          |α (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((J ∘ σ) i))| := by
        rw [hperm]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      rw [habs]
      have hterm : (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ ((J ∘ σ) i))) ^ 2 ≤
          ∑ I : Fin n → Fin P, (if StrictMono I then
            (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) := by
        have := Finset.single_le_sum (f := fun I : Fin n → Fin P =>
          if StrictMono I then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)
          (fun I _ => by split_ifs <;> positivity) (Finset.mem_univ (J ∘ σ))
        simpa [hsm] using this
      unfold covectorEuclideanNorm
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hterm
    · have h0 : α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) = 0 :=
        α.map_eq_zero_of_not_injective _ (fun h => hJ (fun i j hij => h (by simp only [hij])))
      rw [h0, abs_zero]
      exact covectorEuclideanNorm_nonneg α
  -- (A) `|α v| ≤ Pⁿ |α| ∏ᵢ ‖vᵢ‖`
  have emfA_abs_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ (Fintype.card (Fin n → Fin P) : ℝ) * covectorEuclideanNorm α * ∏ i, ‖v i‖ := by
    intro P n α v
    rw [emfA_expand P n α v]
    calc |∑ J : Fin n → Fin P,
            (∏ i, v i (J i)) * α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))|
        ≤ ∑ J : Fin n → Fin P,
            |(∏ i, v i (J i)) * α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _J : Fin n → Fin P, (covectorEuclideanNorm α * ∏ i, ‖v i‖) := by
          refine Finset.sum_le_sum fun J _ => ?_
          rw [abs_mul, Finset.abs_prod, mul_comm]
          refine mul_le_mul (emfA_basis_le P n α J) ?_
            (Finset.prod_nonneg fun i _ => abs_nonneg _) (covectorEuclideanNorm_nonneg α)
          exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by
            have := PiLp.norm_apply_le (v i) (J i)
            simpa [Real.norm_eq_abs] using this)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  -- (A) a covector vanishing on all coordinate tuples is zero
  have emfA_eq_zero : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (h : ∀ J : Fin n → Fin P, α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) = 0), α = 0 := by
    intro P n α h
    ext v
    rw [emfA_expand P n α v]
    exact (Finset.sum_eq_zero fun J _ => by rw [h J, mul_zero]).trans rfl
  -- (A) `Λⁿ` is finite dimensional (paired with `True`, so it is not a local instance)
  have emfA_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) ∧ True := by
    intro P n
    refine ⟨?_, trivial⟩
    let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
      { toFun := fun α J => α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))
        map_add' := fun α β => by funext J; simp
        map_smul' := fun c α => by funext J; simp }
    refine Module.Finite.of_injective Φ ?_
    intro α β hαβ
    have : α - β = 0 := emfA_eq_zero P n (α - β) (fun J => by
      have := congrFun hαβ J
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
      rw [ContinuousAlternatingMap.sub_apply, this, sub_self])
    exact sub_eq_zero.mp this
  -- (A) homogeneity of the Euclidean coefficient norm
  have emfA_euclid_smul : ∀ (P n : ℕ) (c : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro P n c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- (A) the Euclidean coefficient norm is at most `Pⁿ` times the operator norm
  have emfA_euclid_le_opNorm : ∀ (P n : ℕ) (α : Covector (Euclid P) n), covectorEuclideanNorm α ≤ (Fintype.card (Fin n → Fin P) : ℝ) * ‖α‖ := by
    intro P n α
    set N : ℝ := (Fintype.card (Fin n → Fin P) : ℝ) with hN
    have hterm : ∀ I : Fin n → Fin P, (if StrictMono I then
        (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0) ≤ ‖α‖ ^ 2 := by
      intro I
      split_ifs
      · have h1 := α.le_opNorm (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))
        simp only [OrthonormalBasis.norm_eq_one, Finset.prod_const_one, mul_one,
          Real.norm_eq_abs] at h1
        have h0 : 0 ≤ ‖α‖ := norm_nonneg _
        nlinarith [abs_nonneg (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))),
          sq_abs (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)))]
      · positivity
    have hsum : (∑ I : Fin n → Fin P, (if StrictMono I then
        (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i))) ^ 2 else 0)) ≤ (N * ‖α‖) ^ 2 := by
      calc _ ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 := Finset.sum_le_sum fun I _ => hterm I
        _ = N * ‖α‖ ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ ≤ (N * ‖α‖) ^ 2 := by
            have hN1 : N ≤ N ^ 2 := by
              rcases Nat.eq_zero_or_pos (Fintype.card (Fin n → Fin P)) with h | h
              · simp [hN, h]
              · have : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast h
                nlinarith
            have : 0 ≤ ‖α‖ ^ 2 := by positivity
            nlinarith
    unfold covectorEuclideanNorm
    calc Real.sqrt _ ≤ Real.sqrt ((N * ‖α‖) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = N * ‖α‖ := Real.sqrt_sq (by positivity)
  -- (B) `x ↦ g(x)(L(x)·, …, L(x)·)` is `C^∞` (coordinates and a linear left inverse)
  have emfB_pullback_contDiff : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n) (L : Euclid P → (Euclid P →L[ℝ] Euclid P)) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hL : ContDiff ℝ (⊤ : ℕ∞) L), ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x).compContinuousLinearMap (L x)) := by
    intro P n g L hg hL
    classical
    let Ev : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclid P) ℝ →L[ℝ]
        ((Fin n → Fin P) → ℝ) :=
      ContinuousLinearMap.pi fun J => ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euclid P) ℝ
        (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))
    let ι : Covector (Euclid P) n →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => Euclid P) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    let Φ : Covector (Euclid P) n →L[ℝ] ((Fin n → Fin P) → ℝ) := Ev.comp ι
    have hΦapp : ∀ α J, Φ α J = α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i)) :=
      fun α J => rfl
    have hΦ : Function.Injective Φ := by
      intro α β h
      have : α - β = 0 := emfA_eq_zero P n (α - β) (fun J => by
        have := congrFun h J
        rw [hΦapp, hΦapp] at this
        rw [ContinuousAlternatingMap.sub_apply, this, sub_self])
      exact sub_eq_zero.mp this
    obtain ⟨Ψl, hΨl⟩ :=
      LinearMap.exists_leftInverse_of_injective Φ.toLinearMap (LinearMap.ker_eq_bot.mpr hΦ)
    let Ψ : ((Fin n → Fin P) → ℝ) →L[ℝ] Covector (Euclid P) n :=
      ⟨Ψl, Ψl.continuous_of_finiteDimensional⟩
    have hΨ : ∀ α, Ψ (Φ α) = α := fun α => LinearMap.congr_fun hΨl α
    have hmult : ContDiff ℝ (⊤ : ℕ∞) (fun x => ι ((g x).compContinuousLinearMap (L x))) := by
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
          ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
            (fun _ : Fin n => Euclid P) (fun _ : Fin n => Euclid P) ℝ (fun _ => L x)) :=
        (ContinuousMultilinearMap.contDiff _).comp (contDiff_pi.2 fun _ => hL)
      have h2 := h1.clm_apply (ι.contDiff.comp hg)
      convert h2 using 1
      funext x
      ext v
      rfl
    have heq : (fun x => (g x).compContinuousLinearMap (L x)) =
        fun x => Ψ (Ev (ι ((g x).compContinuousLinearMap (L x)))) := by
      funext x
      exact (hΨ _).symm
    rw [heq]
    exact Ψ.contDiff.comp (Ev.contDiff.comp hmult)
  -- (C) a `C^∞` map `f` with `‖Df‖ ≤ 1`, `f = id` on `B_a(0)` and bounded image
  have emfC_retraction : ∀ (P : ℕ) (a : ℝ) (ha : 0 < a), ∃ f : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) f ∧ (∀ x, ‖fderiv ℝ f x‖ ≤ 1) ∧ (∀ x ∈ ball (0 : Euclid P) a, f x = x) ∧ ∃ R : ℝ, ∀ x, ‖f x‖ ≤ R := by
    intro P a ha
    let h : ContDiffBump (0 : ℝ) := ⟨a, a + 1, ha, by linarith⟩
    let φ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, h s
    have hderiv : ∀ t, HasDerivAt φ (h t) t := fun t =>
      intervalIntegral.integral_hasDerivAt_right (h.continuous.intervalIntegrable _ _)
        (h.continuous.stronglyMeasurableAtFilter _ _) h.continuous.continuousAt
    have hdiff : Differentiable ℝ φ := fun t => (hderiv t).differentiableAt
    have hderiv_eq : deriv φ = h := funext fun t => (hderiv t).deriv
    have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ :=
      contDiff_infty_iff_deriv.2 ⟨hdiff, by rw [hderiv_eq]; exact h.contDiff⟩
    have hφ_lip : LipschitzWith 1 φ := by
      refine lipschitzWith_of_nnnorm_deriv_le hdiff fun t => ?_
      rw [hderiv_eq, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_eq_abs,
        abs_of_nonneg (h.nonneg' t)]
      exact h.le_one
    have hφ_id : ∀ t, |t| < a → φ t = t := by
      intro t ht
      have h1 : EqOn (fun s => h s) (fun _ => (1 : ℝ)) (Set.uIcc (0 : ℝ) t) := by
        intro s hs
        apply h.one_of_mem_closedBall
        rw [mem_closedBall, Real.dist_eq, sub_zero]
        show |s| ≤ a
        have := abs_le.1 ht.le
        rcases Set.mem_uIcc.1 hs with ⟨h0, h2⟩ | ⟨h0, h2⟩
        · rw [abs_le]; constructor <;> linarith [le_abs_self t]
        · rw [abs_le]; constructor <;> linarith [neg_abs_le t]
      calc φ t = ∫ s in (0 : ℝ)..t, (1 : ℝ) := intervalIntegral.integral_congr h1
        _ = t := by simp
    have hint : Integrable (fun s => h s) :=
      h.continuous.integrable_of_hasCompactSupport h.hasCompactSupport
    have hφ_bdd : ∀ t, |φ t| ≤ ∫ s, h s := by
      intro t
      calc |φ t| = ‖∫ s in (0 : ℝ)..t, h s‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∫ s in Set.uIoc (0 : ℝ) t, ‖h s‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
        _ ≤ ∫ s, ‖h s‖ :=
            setIntegral_le_integral hint.norm (Eventually.of_forall fun _ => norm_nonneg _)
        _ = ∫ s, h s := by
            congr 1; funext s; rw [Real.norm_eq_abs, abs_of_nonneg (h.nonneg' s)]
    let f : Euclid P → Euclid P := fun x => WithLp.toLp 2 (fun i => φ (x i))
    have hf_apply : ∀ x i, f x i = φ (x i) := fun x i => rfl
    have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f :=
      contDiff_piLp' 2 fun i => hφ_smooth.comp (contDiff_piLp_apply 2)
    have hf_lip : LipschitzWith 1 f := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, NNReal.coe_one, one_mul]
      apply Real.sqrt_le_sqrt
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 := hφ_lip.dist_le_mul (x i) (y i)
      rw [NNReal.coe_one, one_mul] at h1
      rw [hf_apply, hf_apply]
      exact pow_le_pow_left₀ dist_nonneg h1 2
    refine ⟨f, hf_smooth, fun x => ?_, fun x hx => ?_, ?_⟩
    · simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hf_lip
    · refine PiLp.ext fun i => ?_
      rw [hf_apply]
      apply hφ_id
      calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x‖ := PiLp.norm_apply_le x i
        _ < a := by simpa [mem_ball, dist_zero_right] using hx
    · refine ⟨Real.sqrt (P * (∫ s, h s) ^ 2), fun x => ?_⟩
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖f x i‖ ^ 2 ≤ ∑ _i : Fin P, (∫ s, h s) ^ 2 := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs, hf_apply]
            have := hφ_bdd (x i)
            exact sq_le_sq' (by linarith [neg_abs_le (φ (x i))]) (le_trans (le_abs_self _) this)
        _ = P * (∫ s, h s) ^ 2 := by simp
  -- (E) the orientation of a representation of `Y` vanishes a.e. off `spt Y`
  have emfE_orient_null : ∀ (P n : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (hR : R.Represents Y), ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∉ Y.support → R.orient x = 0 := by
    intro P n Y R hR
    classical
    have := (emfA_finiteDimensional P n).1
    set ν := μHE[n].restrict R.carrier with hν
    have hmult_meas : Measurable fun x => (R.mult x : ℝ) :=
      (measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp R.measurable_mult
    have hmultE : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp R.measurable_mult
    have hVopen : IsOpen (Y.support)ᶜ := by
      have : (Y.support)ᶜ = Y.zeroRegion := by
        ext x; simp [GeometricCurrentOn.support]
      rw [this]; exact Y.isOpen_zeroRegion
    have key : ∀ α : Covector (Euclid P) n,
        ∀ᵐ x ∂ν, x ∈ (Y.support)ᶜ → (R.mult x : ℝ) * R.orient x α = 0 := by
      intro α
      have horient_le : ∀ᵐ x ∂ν, |R.orient x α| ≤ ‖α‖ := by
        filter_upwards [R.orients] with x hx
        obtain ⟨Q, -, τ, hτ, -, hsign⟩ := hx
        have hτn : ∏ i, ‖τ i‖ = 1 := Finset.prod_eq_one fun i _ => hτ.1 i
        have hαle := α.le_opNorm τ
        rw [hτn, mul_one, Real.norm_eq_abs] at hαle
        rcases hsign with h | h
        · rw [h α]; exact hαle
        · rw [h α, abs_neg]; exact hαle
      have hmeas_o : AEStronglyMeasurable (fun x => R.orient x α) ν :=
        (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
          R.aestronglyMeasurable_orient
      have hF_loc : LocallyIntegrable (fun x => (R.mult x : ℝ) * R.orient x α) ν := by
        rw [locallyIntegrable_iff]
        intro K hK
        have hKm : MeasurableSet K := hK.isClosed.measurableSet
        refine ⟨(hmult_meas.aestronglyMeasurable.mul hmeas_o).restrict, ?_⟩
        have hfin := R.locallyIntegrable_mult K hK (subset_univ K)
        have hbound : ∀ᵐ x ∂(ν.restrict K), ‖(R.mult x : ℝ) * R.orient x α‖ₑ ≤
            ENNReal.ofReal ‖α‖ * (R.mult x : ℝ≥0∞) := by
          filter_upwards [ae_restrict_of_ae horient_le] with x hx
          rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _))
        calc ∫⁻ x, ‖(R.mult x : ℝ) * R.orient x α‖ₑ ∂(ν.restrict K)
            ≤ ∫⁻ x, ENNReal.ofReal ‖α‖ * (R.mult x : ℝ≥0∞) ∂(ν.restrict K) :=
              lintegral_mono_ae hbound
          _ = ENNReal.ofReal ‖α‖ * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
              rw [lintegral_const_mul _ hmultE, hν, Measure.restrict_restrict hKm, Set.inter_comm]
          _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top
      refine hVopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF_loc.locallyIntegrableOn _) ?_
      intro g hg hgc hgU
      have hmem : (fun x => g x • α) ∈ TestFormOn (univ : Set (Euclid P)) n :=
        ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, subset_univ _⟩
      have hdisj : Disjoint (tsupport (fun x => g x • α)) Y.support :=
        Set.subset_compl_iff_disjoint_right.1
          ((tsupport_smul_subset_left (fun x => g x) (fun _ => α)).trans hgU)
      have hY0 := Submission.dtc_vanish_off_support P n univ Y ⟨_, hmem⟩ hdisj
      rw [hR] at hY0
      simp only [IMRep.action] at hY0
      rw [← hY0]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, map_smul]
      ring
    let b := Module.finBasis ℝ (Covector (Euclid P) n)
    have hall : ∀ᵐ x ∂ν, ∀ i, x ∈ (Y.support)ᶜ → (R.mult x : ℝ) * R.orient x (b i) = 0 :=
      ae_all_iff.2 fun i => key (b i)
    filter_upwards [hall, ae_restrict_mem R.measurableSet_carrier] with x hx hxM hxS
    have hpos : (R.mult x : ℝ) ≠ 0 := by exact_mod_cast (R.mult_pos x hxM).ne'
    apply ContinuousLinearMap.coe_injective
    refine b.ext fun i => ?_
    have := hx i hxS
    simpa using (mul_eq_zero.1 this).resolve_left hpos
  -- (F) Simon 6.3.2(3): compactly supported integer multiplicity currents have finite mass
  have emfF_mass_lt_top : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (hS : IsIntegerMultiplicity S) (hc : IsCompact S.support), S.mass < ∞ := by
    intro P n S hS hc
    obtain ⟨R, hR⟩ := hS
    obtain ⟨r, hr, hKr⟩ := hc.isBounded.subset_ball_lt 0 (0 : Euclid P)
    let ψ : ContDiffBump (0 : Euclid P) := ⟨r, r + 1, hr, by linarith⟩
    set K := closedBall (0 : Euclid P) (r + 1) with hK
    have hKm : MeasurableSet K := measurableSet_closedBall
    set C : ℝ := (Fintype.card (Fin n → Fin P) : ℝ) with hC
    have hC0 : 0 ≤ C := by positivity
    have hfin : ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ :=
      R.locallyIntegrable_mult K (isCompact_closedBall _ _) (subset_univ _)
    have horient : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
        |R.orient x α| ≤ C * covectorEuclideanNorm α := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, -, τ, hτ, -, hsign⟩ := hx
      intro α
      have hτn : ∏ i, ‖τ i‖ = 1 := Finset.prod_eq_one fun i _ => hτ.1 i
      have h1 := emfA_abs_le P n α τ
      rw [hτn, mul_one] at h1
      rcases hsign with h | h
      · rw [h α]; exact h1
      · rw [h α, abs_neg]; exact h1
    have hψ1 : ∀ x ∈ ball (0 : Euclid P) r, ψ x = 1 := fun x hx =>
      ψ.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hψ0 : ∀ x, x ∉ K → ψ x = 0 := fun x hx => ψ.zero_of_le_dist (by
      rw [hK, mem_closedBall, not_le] at hx; exact hx.le)
    refine lt_of_le_of_lt (b := ENNReal.ofReal C * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n])
      ?_ (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top)
    unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have hmem : (fun x => ψ x • (ω : DifferentialForm (Euclid P) n) x) ∈
        TestFormOn (univ : Set (Euclid P)) n :=
      ⟨⟨ψ.contDiff.smul ω.property.1.1, ψ.hasCompactSupport.smul_right⟩, subset_univ _⟩
    let ψω : TestFormOn (univ : Set (Euclid P)) n := ⟨_, hmem⟩
    have hSeq : S ω = S ψω := by
      have hdisj : Disjoint (tsupport ((ω - ψω : TestFormOn (univ : Set (Euclid P)) n) :
          DifferentialForm (Euclid P) n)) S.support := by
        refine Set.subset_compl_iff_disjoint_right.1 (Subset.trans ?_ (compl_subset_compl.2 hKr))
        refine closure_minimal ?_ isOpen_ball.isClosed_compl
        intro x hx
        by_contra hxb
        apply hx
        have : ψ x = 1 := hψ1 x (by simpa using hxb)
        show (ω : DifferentialForm (Euclid P) n) x - ψ x • (ω : DifferentialForm (Euclid P) n) x = 0
        rw [this, one_smul, sub_self]
      have := Submission.dtc_vanish_off_support P n univ S (ω - ψω) hdisj
      rw [show S (ω - ψω) = S ω - S ψω from S.toCurrent.map_sub ω ψω] at this
      exact sub_eq_zero.1 this
    show ENNReal.ofReal (S ω) ≤ _
    rw [hSeq, hR ψω]
    simp only [IMRep.action]
    calc ENNReal.ofReal (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])
        ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in R.carrier, ‖(R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in R.carrier, K.indicator (fun x => ENNReal.ofReal C * (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
          refine lintegral_mono_ae ?_
          filter_upwards [horient] with x hx
          by_cases hxK : x ∈ K
          · rw [Set.indicator_of_mem hxK]
            have hle : |(R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x)| ≤
                C * (R.mult x : ℝ) := by
              rw [map_smul, smul_eq_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
                abs_of_nonneg (ψ.nonneg' x)]
              have h2 := hx ((ω : DifferentialForm (Euclid P) n) x)
              have h3 := hω.2 x
              have h4 : ψ x ≤ 1 := ψ.le_one
              have h5 : 0 ≤ ψ x := ψ.nonneg' x
              have h6 : 0 ≤ |R.orient x ((ω : DifferentialForm (Euclid P) n) x)| := abs_nonneg _
              have h7 : 0 ≤ (R.mult x : ℝ) := Nat.cast_nonneg _
              calc (R.mult x : ℝ) * (ψ x * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|)
                  ≤ (R.mult x : ℝ) * (1 * (C * 1)) := by
                    gcongr
                    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC0)
                _ = C * (R.mult x : ℝ) := by ring
            calc ‖(R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x)‖ₑ
                = ENNReal.ofReal |(R.mult x : ℝ) * R.orient x (ψ x • (ω : DifferentialForm (Euclid P) n) x)| :=
                  Real.enorm_eq_ofReal_abs _
              _ ≤ ENNReal.ofReal (C * (R.mult x : ℝ)) := ENNReal.ofReal_le_ofReal hle
              _ = ENNReal.ofReal C * (R.mult x : ℝ≥0∞) := by
                  rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
          · rw [Set.indicator_of_notMem hxK, hψ0 x hxK, zero_smul, map_zero, mul_zero]
            simp
      _ = ENNReal.ofReal C * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          have hmultE : Measurable fun x => (R.mult x : ℝ≥0∞) :=
            (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp R.measurable_mult
          rw [lintegral_indicator hKm, Measure.restrict_restrict hKm, Set.inter_comm,
            lintegral_const_mul _ hmultE]
  -- (G) `∂(f_# Y) = S` if `∂Y = S` and `f = id` near `spt S` (`d ∘ f^# = f^# ∘ d`)
  have emfG_boundary_push : ∀ (P m : ℕ) (f : Euclid P → Euclid P) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) (hfid : ∀ x ∈ ball (0 : Euclid P) a, f x = x) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (hSa : S.support ⊆ ball 0 a) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (R : IMRep (univ : Set (Euclid P)) (m + 2)) (hR : R.Represents Y) (hYc : IsCompact Y.support) (hYb : Y.boundary = S) (Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (hZ : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 2), Z ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 2)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 2]), Z.boundary = S := by
    intro P m f hf a hfid S hSa Y R hR hYc hYb Z hZ
    apply GeometricCurrentOn.ext
    intro ω
    set ω' : DifferentialForm (Euclid P) (m + 1) := (ω : DifferentialForm (Euclid P) (m + 1)) with hω'
    have hωs : ContDiff ℝ (⊤ : ℕ∞) ω' := ω.property.1.1
    let β : DifferentialForm (Euclid P) (m + 1) :=
      fun x => (ω' (f x)).compContinuousLinearMap (fderiv ℝ f x)
    have hDf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
    have hβs : ContDiff ℝ (⊤ : ℕ∞) β :=
      emfB_pullback_contDiff P (m + 1) (fun x => ω' (f x)) (fderiv ℝ f) (hωs.comp hf) hDf
    have hnat : ∀ x, exteriorDerivative β x =
        ((exteriorDerivative ω') (f x)).compContinuousLinearMap (fderiv ℝ f x) :=
      fun x => extDeriv_pullback (hωs.differentiable (by simp) (f x)) hf.contDiffAt (by simp)
    obtain ⟨r, hr, hKr⟩ :=
      (hYc.union (isCompact_closedBall (0 : Euclid P) a)).isBounded.subset_ball_lt 0 0
    let ψ : ContDiffBump (0 : Euclid P) := ⟨r, r + 1, hr, by linarith⟩
    have hψ1 : ∀ x ∈ ball (0 : Euclid P) r, ψ x = 1 := fun x hx =>
      ψ.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hmem : (fun x => ψ x • β x) ∈ TestFormOn (univ : Set (Euclid P)) (m + 1) :=
      ⟨⟨ψ.contDiff.smul hβs, ψ.hasCompactSupport.smul_right⟩, subset_univ _⟩
    let η : TestFormOn (univ : Set (Euclid P)) (m + 1) := ⟨_, hmem⟩
    have hstep1 : Z.boundary ω = Y.boundary η := by
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hZ, hR]
      simp only [IMRep.action]
      refine integral_congr_ae ?_
      filter_upwards [emfE_orient_null P (m + 2) Y R hR] with x hx
      by_cases hxr : x ∈ ball (0 : Euclid P) r
      · have hloc : (fun y => ψ y • β y) =ᶠ[𝓝 x] β := by
          filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
          rw [hψ1 y hy, one_smul]
        show (R.mult x : ℝ) * R.orient x ((exteriorDerivative ω' (f x)).compContinuousLinearMap
            (fderiv ℝ f x)) = (R.mult x : ℝ) * R.orient x (exteriorDerivative (fun y => ψ y • β y) x)
        rw [show exteriorDerivative (fun y => ψ y • β y) x = exteriorDerivative β x from
          hloc.extDeriv_eq, hnat x]
      · have hxY : x ∉ Y.support := fun h => hxr (hKr (Or.inl h))
        rw [hx hxY]
        simp
    rw [hstep1, hYb]
    have hdisj : Disjoint (tsupport ((η - ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) :
        DifferentialForm (Euclid P) (m + 1))) S.support := by
      refine Set.subset_compl_iff_disjoint_right.1 (Subset.trans ?_ (compl_subset_compl.2 hSa))
      refine closure_minimal ?_ isOpen_ball.isClosed_compl
      intro x hx
      by_contra hxb
      apply hx
      have hxa : x ∈ ball (0 : Euclid P) a := by simpa using hxb
      have hxr : x ∈ ball (0 : Euclid P) r := hKr (Or.inr (ball_subset_closedBall hxa))
      have hfx : f x = x := hfid x hxa
      have hDfx : fderiv ℝ f x = ContinuousLinearMap.id ℝ (Euclid P) := by
        have : f =ᶠ[𝓝 x] id := by
          filter_upwards [isOpen_ball.mem_nhds hxa] with y hy using hfid y hy
        rw [this.fderiv_eq, fderiv_id]
      show ψ x • β x - ω' x = 0
      rw [hψ1 x hxr, one_smul]
      show (ω' (f x)).compContinuousLinearMap (fderiv ℝ f x) - ω' x = 0
      rw [hfx, hDfx, sub_eq_zero]
      ext v
      rfl
    have := Submission.dtc_vanish_off_support P (m + 1) univ S (η - ω) hdisj
    rw [show S (η - ω) = S η - S ω from S.toCurrent.map_sub η ω] at this
    exact sub_eq_zero.1 this
  -- (H) weak sequential compactness under uniform support and mass bounds
  have emfH_compactness : ∀ (P n : ℕ) (Ys : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) n) (r₀ : ℝ) (hr₀ : 0 < r₀) (hsupp : ∀ i, (Ys i).support ⊆ closedBall 0 r₀) (C : ℝ) (hC : 0 ≤ C) (hmass : ∀ i, (Ys i).mass ≤ ENNReal.ofReal C), ∃ (φ : ℕ → ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) n), StrictMono φ ∧ WeaklyConvergesOn (fun i => Ys (φ i)) T := by
    intro P n Ys r₀ hr₀ hsupp C hC hmass
    classical
    have hfd := (emfA_finiteDimensional P n).1
    set N : ℝ := (Fintype.card (Fin n → Fin P) : ℝ) with hN
    have hN0 : 0 ≤ N := by positivity
    let ψ : ContDiffBump (0 : Euclid P) := ⟨r₀ + 1, r₀ + 2, by linarith, by linarith⟩
    set K₁ := closedBall (0 : Euclid P) (r₀ + 2) with hK₁
    have hψ1 : ∀ x ∈ ball (0 : Euclid P) (r₀ + 1), ψ x = 1 := fun x hx =>
      ψ.one_of_mem_closedBall (ball_subset_closedBall hx)
    have hψ0 : ∀ x, x ∉ K₁ → ψ x = 0 := fun x hx => ψ.zero_of_le_dist (by
      rw [hK₁, mem_closedBall, not_le] at hx; exact hx.le)
    -- the basic bound `|Yᵢ(ω)| ≤ C N sup_{K₁} ‖ω‖`
    have hbound : ∀ i (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), 0 ≤ s →
        (∀ x ∈ K₁, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |Ys i ω| ≤ C * N * s := by
      intro i ω s hs hωs
      have hmem : (fun x => ψ x • (ω : DifferentialForm (Euclid P) n) x) ∈
          TestFormOn (univ : Set (Euclid P)) n :=
        ⟨⟨ψ.contDiff.smul ω.property.1.1, ψ.hasCompactSupport.smul_right⟩, subset_univ _⟩
      let ψω : TestFormOn (univ : Set (Euclid P)) n := ⟨_, hmem⟩
      have hYeq : Ys i ω = Ys i ψω := by
        have hdisj : Disjoint (tsupport ((ω - ψω : TestFormOn (univ : Set (Euclid P)) n) :
            DifferentialForm (Euclid P) n)) (Ys i).support := by
          refine Set.subset_compl_iff_disjoint_right.1 (Subset.trans ?_ (compl_subset_compl.2
            ((hsupp i).trans (closedBall_subset_ball (show r₀ < r₀ + 1 by linarith)))))
          refine closure_minimal ?_ isOpen_ball.isClosed_compl
          intro x hx
          by_contra hxb
          apply hx
          have : ψ x = 1 := hψ1 x (by simpa using hxb)
          show (ω : DifferentialForm (Euclid P) n) x - ψ x • (ω : DifferentialForm (Euclid P) n) x = 0
          rw [this, one_smul, sub_self]
        have := Submission.dtc_vanish_off_support P n univ (Ys i) (ω - ψω) hdisj
        rw [show Ys i (ω - ψω) = Ys i ω - Ys i ψω from (Ys i).toCurrent.map_sub ω ψω] at this
        exact sub_eq_zero.1 this
      rw [hYeq]
      have key : ∀ t : ℝ, N * s < t → |Ys i ψω| ≤ C * t := by
        intro t ht
        have ht0 : 0 < t := lt_of_le_of_lt (by positivity) ht
        have hadm : ∀ c : ℝ, |c| = t⁻¹ → (c • ψω) ∈ massAdmissibleOn univ n univ := by
          intro c hc
          refine ⟨subset_univ _, fun x => ?_⟩
          show covectorEuclideanNorm (c • (ψ x • (ω : DifferentialForm (Euclid P) n) x)) ≤ 1
          rw [emfA_euclid_smul, emfA_euclid_smul, hc]
          have hpsi : |ψ x| ≤ 1 := by rw [abs_of_nonneg (ψ.nonneg' x)]; exact ψ.le_one
          by_cases hxK : x ∈ K₁
          · have h1 := emfA_euclid_le_opNorm P n ((ω : DifferentialForm (Euclid P) n) x)
            have h2 := hωs x hxK
            have h3 : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ N * s :=
              h1.trans (mul_le_mul_of_nonneg_left h2 hN0)
            calc t⁻¹ * (|ψ x| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x))
                ≤ t⁻¹ * (1 * (N * s)) := by
                  gcongr
                  · exact covectorEuclideanNorm_nonneg _
              _ ≤ 1 := by
                  rw [one_mul, inv_mul_le_iff₀ ht0]; linarith
          · rw [hψ0 x hxK, abs_zero, zero_mul, mul_zero]; exact zero_le_one
        have hm := hmass i
        have hle1 := (Ys i).le_massOn (hadm t⁻¹ (abs_of_pos (inv_pos.2 ht0)))
        have hle2 := (Ys i).le_massOn (hadm (-t⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 ht0)]))
        have e1 : Ys i (t⁻¹ • ψω) = t⁻¹ * Ys i ψω := (Ys i).toCurrent.map_smul t⁻¹ ψω
        have e2 : Ys i ((-t⁻¹) • ψω) = -t⁻¹ * Ys i ψω := (Ys i).toCurrent.map_smul (-t⁻¹) ψω
        rw [e1] at hle1
        rw [e2] at hle2
        have hmass' : (Ys i).massOn univ ≤ ENNReal.ofReal C := hm
        have i1 : t⁻¹ * Ys i ψω ≤ C :=
          (ENNReal.ofReal_le_ofReal_iff hC).1 (hle1.trans hmass')
        have i2 : -t⁻¹ * Ys i ψω ≤ C :=
          (ENNReal.ofReal_le_ofReal_iff hC).1 (hle2.trans hmass')
        have i1' : Ys i ψω ≤ C * t := by
          have := mul_le_mul_of_nonneg_left i1 ht0.le
          rw [← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul] at this; linarith
        have i2' : -(Ys i ψω) ≤ C * t := by
          have := mul_le_mul_of_nonneg_left i2 ht0.le
          rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul] at this; linarith
        exact abs_le.2 ⟨by linarith, i1'⟩
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hεC : 0 < ε / (C + 1) := by positivity
      have h1 := key (N * s + ε / (C + 1)) (by linarith)
      have h2 : C * (ε / (C + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
      nlinarith
    -- a countable family of test forms dense in `C(K₁, Λⁿ)`
    have : CompactSpace K₁ := isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
    have : LocallyCompactSpace K₁ := isClosed_closedBall.locallyCompactSpace
    let res : TestFormOn (univ : Set (Euclid P)) n → C(K₁, Covector (Euclid P) n) := fun ω =>
      ⟨fun x => (ω : DifferentialForm (Euclid P) n) x,
        (ω.property.1.1.continuous).comp continuous_subtype_val⟩
    have : SecondCountableTopology C(K₁, Covector (Euclid P) n) :=
      ContinuousMap.instSecondCountableTopology
    set A := Set.range res with hA
    have : Nonempty A := ⟨⟨res 0, Set.mem_range_self 0⟩⟩
    have hdense : DenseRange (TopologicalSpace.denseSeq A) := TopologicalSpace.denseRange_denseSeq A
    choose d hd using fun k => (TopologicalSpace.denseSeq A k).2
    have happrox : ∀ (ω : TestFormOn (univ : Set (Euclid P)) n) (ε : ℝ), 0 < ε → ∃ k,
        ∀ x ∈ K₁, ‖(ω : DifferentialForm (Euclid P) n) x - (d k : DifferentialForm (Euclid P) n) x‖ < ε := by
      intro ω ε hε
      have hV : {g : C(K₁, Covector (Euclid P) n) | ∀ x, dist (res ω x) (g x) < ε} ∈ 𝓝 (res ω) := by
        have := ContinuousMap.tendsto_iff_tendstoUniformly.1 (tendsto_id (x := 𝓝 (res ω)))
        exact (Metric.tendstoUniformly_iff.1 this) ε hε
      have hmem : (⟨res ω, Set.mem_range_self ω⟩ : A) ∈
          closure (Set.range (TopologicalSpace.denseSeq A)) := hdense _
      obtain ⟨_, hy1, k, rfl⟩ := mem_closure_iff_nhds.1 hmem _
        (continuous_subtype_val.continuousAt.preimage_mem_nhds hV)
      refine ⟨k, fun x hx => ?_⟩
      have h1 := hy1 ⟨x, hx⟩
      rw [← hd k] at h1
      rw [← dist_eq_norm]
      exact h1
    have hsk : ∀ k, ∃ s : ℝ, 0 ≤ s ∧ ∀ x, ‖(d k : DifferentialForm (Euclid P) n) x‖ ≤ s := by
      intro k
      obtain ⟨s, hs⟩ := (d k).property.1.1.continuous.bounded_above_of_compact_support
        (d k).property.1.2
      exact ⟨max s 0, le_max_right _ _, fun x => (hs x).trans (le_max_left _ _)⟩
    choose sk hsk0 hsk using hsk
    let B : ℕ → ℝ := fun k => C * N * sk k
    have hBk : ∀ i k, |Ys i (d k)| ≤ B k := fun i k =>
      hbound i (d k) (sk k) (hsk0 k) (fun x _ => hsk k x)
    have hbox : IsCompact (Set.pi univ fun k => Icc (-B k) (B k)) :=
      isCompact_univ_pi fun k => isCompact_Icc
    have ha : ∀ i, (fun k => Ys i (d k)) ∈ Set.pi univ fun k => Icc (-B k) (B k) :=
      fun i k _ => abs_le.1 (hBk i k)
    obtain ⟨v, -, φ, hφ, hlim⟩ := hbox.tendsto_subseq ha
    have hlimk : ∀ k, Tendsto (fun i => Ys (φ i) (d k)) atTop (𝓝 (v k)) := fun k =>
      ((continuous_apply k).tendsto v).comp hlim
    -- every `Y_{φ i}(ω)` is Cauchy
    have hcauchy : ∀ ω : TestFormOn (univ : Set (Euclid P)) n, CauchySeq (fun i => Ys (φ i) ω) := by
      intro ω
      rw [Metric.cauchySeq_iff']
      intro ε hε
      set δ := ε / (4 * (C * N + 1)) with hδ
      have hCN : 0 ≤ C * N := mul_nonneg hC hN0
      have hδ0 : 0 < δ := by positivity
      obtain ⟨k, hk⟩ := happrox ω δ hδ0
      have hcs := (hlimk k).cauchySeq
      rw [Metric.cauchySeq_iff'] at hcs
      obtain ⟨M, hM⟩ := hcs (ε / 2) (by positivity)
      refine ⟨M, fun i hi => ?_⟩
      have hdk : ∀ x ∈ K₁, ‖((ω - d k : TestFormOn (univ : Set (Euclid P)) n) :
          DifferentialForm (Euclid P) n) x‖ ≤ δ := fun x hx => (hk x hx).le
      have hb1 := hbound (φ i) (ω - d k) δ hδ0.le hdk
      have hb2 := hbound (φ M) (ω - d k) δ hδ0.le hdk
      rw [show Ys (φ i) (ω - d k) = Ys (φ i) ω - Ys (φ i) (d k) from
        (Ys (φ i)).toCurrent.map_sub ω (d k)] at hb1
      rw [show Ys (φ M) (ω - d k) = Ys (φ M) ω - Ys (φ M) (d k) from
        (Ys (φ M)).toCurrent.map_sub ω (d k)] at hb2
      have h3 := hM i hi
      rw [Real.dist_eq] at h3 ⊢
      have hCNδ : C * N * δ ≤ ε / 4 := by
        rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith
      calc |Ys (φ i) ω - Ys (φ M) ω|
          ≤ |Ys (φ i) ω - Ys (φ i) (d k)| + |Ys (φ i) (d k) - Ys (φ M) (d k)| +
              |Ys (φ M) ω - Ys (φ M) (d k)| := by
            have := abs_sub_le (Ys (φ i) ω) (Ys (φ i) (d k)) (Ys (φ M) ω)
            have := abs_sub_le (Ys (φ i) (d k)) (Ys (φ M) (d k)) (Ys (φ M) ω)
            rw [abs_sub_comm (Ys (φ M) (d k)) (Ys (φ M) ω)] at this
            linarith
        _ < ε := by linarith
    have hconv : ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        ∃ L, Tendsto (fun i => Ys (φ i) ω) atTop (𝓝 L) :=
      fun ω => cauchySeq_tendsto_of_complete (hcauchy ω)
    choose L hL using hconv
    have hLbound : ∀ (ω : TestFormOn (univ : Set (Euclid P)) n) (s : ℝ), 0 ≤ s →
        (∀ x ∈ K₁, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ s) → |L ω| ≤ C * N * s :=
      fun ω s hs hω => le_of_tendsto' ((hL ω).abs) (fun i => hbound (φ i) ω s hs hω)
    let Tlin : TestFormOn (univ : Set (Euclid P)) n →ₗ[ℝ] ℝ :=
      { toFun := L
        map_add' := fun ω η => tendsto_nhds_unique (hL (ω + η)) (by
          simpa [map_add] using (hL ω).add (hL η))
        map_smul' := fun c ω => tendsto_nhds_unique (hL (c • ω)) (by
          simpa [map_smul] using (hL ω).const_mul c) }
    let T : GeometricCurrentOn (univ : Set (Euclid P)) n :=
      { toCurrent := Tlin
        continuous' := by
          intro ωs hωs
          obtain ⟨K, -, -, hsuppK, -, hderiv⟩ := hωs
          have h0 := hderiv 0
          rw [Metric.tendstoUniformlyOn_iff] at h0
          rw [Metric.tendsto_nhds]
          intro ε hε
          set δ := ε / (2 * (C * N + 1)) with hδ
          have hCN : 0 ≤ C * N := mul_nonneg hC hN0
          have hδ0 : 0 < δ := by positivity
          filter_upwards [h0 δ hδ0] with j hj
          have hb : ∀ x ∈ K₁, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ := by
            intro x _
            by_cases hxK : x ∈ K
            · have h1 := hj x hxK
              have h2 : iteratedFDeriv ℝ 0
                  (((0 : TestFormOn (univ : Set (Euclid P)) n)) : DifferentialForm (Euclid P) n) x = 0 := by
                rw [← norm_eq_zero, norm_iteratedFDeriv_zero]; simp
              rw [h2, dist_zero_left, norm_iteratedFDeriv_zero] at h1
              exact h1.le
            · have : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
                image_eq_zero_of_notMem_tsupport (fun h => hxK (hsuppK j h))
              rw [this, norm_zero]; exact hδ0.le
          have := hLbound (ωs j) δ hδ0.le hb
          rw [Real.dist_eq, sub_zero]
          show |L (ωs j)| < ε
          calc |L (ωs j)| ≤ C * N * δ := this
            _ < ε := by
                rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
                nlinarith }
    exact ⟨φ, T, hφ, fun ω => hL ω⟩
  -- the cone filling (child), the C¹ push-forward and Federer–Fleming closure (DAG nodes)
  have hcone := Submission.emf_exists_cone_filling
  have hpush := Submission.dtc_bc_lc_pushforward
  have hclosure := Submission.cmc_closure_and_boundary_rectifiability.1
  intro m ℓ S hSim hSc hSb
  -- the admissible class `𝓘_S` and its infimum mass `m₀` (Step 1: `𝓘_S ≠ ∅` by the cone child)
  obtain ⟨R₀, hR₀im, hR₀c, hR₀b⟩ := hcone m (m + 2 + ℓ) S hSim hSc hSb
  let I : Set (GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2)) :=
    {R | IsIntegerMultiplicity R ∧ IsCompact R.support ∧ R.boundary = S}
  set m₀ : ℝ≥0∞ := ⨅ R ∈ I, R.mass with hm₀
  have hm₀le : ∀ R ∈ I, m₀ ≤ R.mass := fun R hR => biInf_le _ hR
  by_cases hinf : m₀ = ∞
  · refine ⟨R₀, hR₀im, hR₀c, hR₀b, fun R hRim hRc hRb => ?_⟩
    have h := hm₀le R ⟨hRim, hRc, hRb⟩
    rw [hinf, top_le_iff] at h
    rw [h]
    exact le_top
  -- Step 2: a minimizing sequence `R_q ∈ 𝓘_S`, `M(R_q) < m₀ + 1/(q+1)`
  have hseq : ∀ q : ℕ, ∃ R ∈ I, R.mass < m₀ + ((q : ℝ≥0∞) + 1)⁻¹ := by
    intro q
    have hlt : m₀ < m₀ + ((q : ℝ≥0∞) + 1)⁻¹ := ENNReal.lt_add_right hinf (by simp)
    obtain ⟨R, hR⟩ := iInf_lt_iff.1 (lt_of_eq_of_lt hm₀.symm hlt)
    obtain ⟨hRI, hR'⟩ := iInf_lt_iff.1 hR
    exact ⟨R, hRI, hR'⟩
  choose Rs hRsI hRsm using hseq
  choose Reps hReps using fun q => (hRsI q).1
  -- Step 3: a `C^∞` retraction `f`, `‖Df‖ ≤ 1`, `f = id` on `B_a(0) ⊇ spt S`, bounded image
  obtain ⟨a, ha0, hSa⟩ := hSc.isBounded.subset_ball_lt 0 (0 : Euclid (m + 2 + ℓ))
  obtain ⟨f, hfs, hfd, hfid, Rf, hRf⟩ := emfC_retraction (m + 2 + ℓ) a ha0
  obtain ⟨push, hpush1, -⟩ := hpush (m + 2 + ℓ) (m + 1) univ f isOpen_univ
    ((hfs.of_le (by simp)).contDiffOn)
  set r₀ : ℝ := max Rf 1 with hr₀
  have hr₀0 : 0 < r₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp_closed : ∀ Y : GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2),
      IsClosed Y.support := fun Y => isClosed_univ.sdiff Y.isOpen_zeroRegion
  have hpushq : ∀ q, (∀ ω : TestFormOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2), push (Rs q) ω =
      ∫ x in (Reps q).carrier, ((Reps q).mult x : ℝ) * (Reps q).orient x
        (((ω : DifferentialForm (Euclid (m + 2 + ℓ)) (m + 2)) (f x)).compContinuousLinearMap
          (fderiv ℝ f x)) ∂μHE[m + 2]) ∧
      IsIntegerMultiplicity (push (Rs q)) ∧ (push (Rs q)).support ⊆ f '' (Rs q).support ∧
      (∀ L : ℝ, (∀ y ∈ univ, ‖fderiv ℝ f y‖ ≤ L) →
        (push (Rs q)).mass ≤ ENNReal.ofReal (L ^ (m + 2)) * (Rs q).mass) := fun q => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hpush1 (Rs q) (Reps q) (hReps q) (hRsI q).2.1 (subset_univ _)
    exact ⟨h1, h2, h3, h4⟩
  let Ys : ℕ → GeometricCurrentOn (univ : Set (Euclid (m + 2 + ℓ))) (m + 2) := fun q => push (Rs q)
  have hYim : ∀ q, IsIntegerMultiplicity (Ys q) := fun q => (hpushq q).2.1
  have hYsupp : ∀ q, (Ys q).support ⊆ closedBall 0 r₀ := fun q => by
    refine (hpushq q).2.2.1.trans ?_
    rintro _ ⟨x, -, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    exact (hRf x).trans (le_max_left _ _)
  have hYmass : ∀ q, (Ys q).mass ≤ (Rs q).mass := fun q => by
    have := (hpushq q).2.2.2 1 (fun y _ => hfd y)
    rwa [one_pow, ENNReal.ofReal_one, one_mul] at this
  have hYb : ∀ q, (Ys q).boundary = S := fun q =>
    emfG_boundary_push (m + 2 + ℓ) m f hfs a hfid S hSa (Rs q) (Reps q) (hReps q) (hRsI q).2.1
      (hRsI q).2.2 (Ys q) (hpushq q).1
  -- uniform mass bound
  have hm₀1 : m₀ + 1 ≠ ∞ := ENNReal.add_ne_top.2 ⟨hinf, ENNReal.one_ne_top⟩
  set C : ℝ := (m₀ + 1).toReal with hC
  have hC0 : 0 ≤ C := ENNReal.toReal_nonneg
  have hRsle : ∀ q, (Rs q).mass ≤ m₀ + 1 := fun q => by
    refine (hRsm q).le.trans (add_le_add le_rfl ?_)
    exact ENNReal.inv_le_one.2 (by simp)
  have hYC : ∀ q, (Ys q).mass ≤ ENNReal.ofReal C := fun q => by
    rw [hC, ENNReal.ofReal_toReal hm₀1]
    exact (hYmass q).trans (hRsle q)
  -- Step 4: a weakly convergent subsequence `f_# R_{φ i} ⇀ T` (uniform mass and support bounds)
  obtain ⟨φ, T, hφ, hconv⟩ := emfH_compactness (m + 2 + ℓ) (m + 2) Ys r₀ hr₀0 hYsupp C hC0 hYC
  -- Federer–Fleming closure: `T` is integer multiplicity
  have hSmass : S.mass < ∞ := emfF_mass_lt_top (m + 2 + ℓ) (m + 1) S hSim hSc
  have hTim : IsIntegerMultiplicity T := by
    refine hclosure (m + 2 + ℓ) (m + 2) univ (fun i => Ys (φ i)) T isOpen_univ
      (fun j => hYim (φ j)) (fun W _ _ => ?_) hconv
    refine lt_of_le_of_lt (b := ENNReal.ofReal C + S.mass) (iSup_le fun j => ?_)
      (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, hSmass⟩)
    have h1 : (Ys (φ j)).massOn W ≤ ENNReal.ofReal C :=
      ((Ys (φ j)).massOn_mono (subset_univ W)).trans (hYC (φ j))
    have h2 : boundaryMassOn (Ys (φ j)) W ≤ S.mass := by
      show (Ys (φ j)).boundary.massOn W ≤ S.mass
      rw [hYb (φ j)]
      exact S.massOn_mono (subset_univ W)
    exact add_le_add h1 h2
  -- Step 5: `spt T ⊆ B̄_{r₀}(0)` is compact and `∂T = S`
  have hTsupp : T.support ⊆ closedBall 0 r₀ := by
    intro x hx
    by_contra hxr
    rw [mem_closedBall, dist_zero_right, not_le] at hxr
    set ρ := (‖x‖ - r₀) / 2 with hρ
    have hρ0 : 0 < ρ := by rw [hρ]; linarith
    have hdisjB : ∀ y ∈ ball x ρ, y ∉ closedBall (0 : Euclid (m + 2 + ℓ)) r₀ := by
      intro y hy hy0
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right] at hy0
      have := norm_sub_norm_le x y
      rw [← norm_neg (x - y), neg_sub] at this
      linarith
    have hvan : T.VanishesOn (ball x ρ) := by
      intro ω hω
      have h0 : ∀ i, Ys (φ i) ω = 0 := fun i =>
        Submission.dtc_vanish_off_support (m + 2 + ℓ) (m + 2) univ (Ys (φ i)) ω
          (Set.disjoint_left.2 fun y hy hyY => hdisjB y (hω hy) (hYsupp (φ i) hyY))
      exact tendsto_nhds_unique (hconv ω) (by simp only [h0]; exact tendsto_const_nhds)
    apply hx.2
    refine ⟨ball x ρ, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, mem_ball_self hρ0⟩
    rw [closure_ball x hρ0.ne']
    exact isCompact_closedBall _ _
  have hTc : IsCompact T.support :=
    (isCompact_closedBall (0 : Euclid (m + 2 + ℓ)) r₀).of_isClosed_subset (hsupp_closed T) hTsupp
  have hTb : T.boundary = S := by
    apply GeometricCurrentOn.ext
    intro ω
    rw [GeometricCurrentOn.boundary_apply]
    refine tendsto_nhds_unique (hconv (exteriorDerivativeTestOn univ (m + 1) ω)) ?_
    have : ∀ i, Ys (φ i) (exteriorDerivativeTestOn univ (m + 1) ω) = S ω := fun i => by
      rw [← GeometricCurrentOn.boundary_apply, hYb (φ i)]
    simp only [this]
    exact tendsto_const_nhds
  -- Step 6: lower semicontinuity of mass, `M(T) ≤ m₀ ≤ M(R)`
  have hTm : T.mass ≤ m₀ := by
    have hlsc := WeaklyConvergesOn.massOn_le_liminf hconv univ
    have hv : Tendsto (fun i : ℕ => m₀ + ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 m₀) := by
      have h1 : Tendsto (fun i : ℕ => ((i : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
        simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using this
      simpa using (tendsto_const_nhds (x := m₀)).add h1
    calc T.mass = T.massOn univ := rfl
      _ ≤ liminf (fun i => (Ys (φ i)).massOn univ) atTop := hlsc
      _ ≤ liminf (fun i : ℕ => m₀ + ((i : ℝ≥0∞) + 1)⁻¹) atTop := by
          refine liminf_le_liminf (Eventually.of_forall fun i => ?_)
          refine ((hYmass (φ i)).trans (hRsm (φ i)).le).trans (add_le_add le_rfl ?_)
          refine ENNReal.inv_le_inv.2 (add_le_add ?_ le_rfl)
          exact_mod_cast hφ.id_le i
      _ = m₀ := hv.liminf_eq
  exact ⟨T, hTim, hTc, hTb, fun R hRim hRc hRb => hTm.trans (hm₀le R ⟨hRim, hRc, hRb⟩)⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
