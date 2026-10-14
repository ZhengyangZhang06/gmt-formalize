import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.AreaLipschitz
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Poincare.SimonGMT.Chapter01.DensityComparison

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

/-- **Degenerate case `P < n` of the cone splitting** (step 0 of the parent proof of Simon 7.3.5;
the book assumes `n ≤ P`).  An alternating `n`-form on `ℝᴾ` vanishes when `n > P`, so every test
`n`-form is `0` and `S = 0`; hence `S` and all its blow-ups vanish, giving the cone property and the
invariance under translations along `L`.  For the splitting take `S₀ := 0`: the zero current is
integer multiplicity (empty carrier), has zero mass, so it is minimizing, it is a cone with
`∂S₀ = 0` and empty support, and it has density `θ` at a point iff `θ = 0`, in every degree. -/
theorem Submission.dimred_cs_high_degree_case : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), P < n → IsConeCurrent S ∧ (∀ v ∈ L, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω) ∧ ∃ S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L), IsMinimizingIn S₀ univ ∧ BoundaryVanishes S₀ ∧ IsConeCurrent S₀ ∧ S₀.support ⊆ (Lᗮ : Set (Euclid P)) ∧ (∀ t ∈ L, ∀ y ∈ Lᗮ, (t + y ∈ S.support ↔ y ∈ S₀.support)) ∧ ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ θ : ℝ, (HasMassDensity S (t + y) θ ↔ HasMassDensity S₀ y θ) := by
  intro P n S L hPn
  -- an alternating `k`-form on `ℝᴾ`, `k > P`, vanishes: `k` vectors in `ℝᴾ` are dependent
  have covector_eq_zero : ∀ {k : ℕ}, P < k → ∀ α : Covector (Euclid P) k, α = 0 := by
    intro k hk α
    ext v
    have hdep : ¬ LinearIndependent ℝ v := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_fin, finrank_euclideanSpace] at this
      omega
    exact α.toAlternatingMap.map_linearDependent v hdep
  -- hence every test `k`-form is `0`, and so is every `k`-current
  have current_eq_zero : ∀ {k : ℕ} {U : Set (Euclid P)} (T : GeometricCurrentOn U k), P < k →
      T = 0 := by
    intro k U T hk
    ext ω
    have hω : ω = 0 := by
      apply Subtype.ext
      funext x
      exact covector_eq_zero hk _
    rw [hω, GeometricCurrentOn.zero_apply]
    exact T.toCurrent.map_zero
  -- the zero current in an arbitrary degree `j`: zero mass
  have zero_mass : ∀ {j : ℕ} (W : Set (Euclid P)),
      (0 : GeometricCurrentOn (univ : Set (Euclid P)) j).massOn W = 0 := by
    intro j W
    apply le_antisymm _ zero_le
    apply sSup_le
    rintro _ ⟨ω, _, rfl⟩
    simp
  -- integer multiplicity, represented by the empty carrier
  have zero_im : ∀ {j : ℕ},
      IsIntegerMultiplicity (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) := by
    intro j
    refine ⟨{ carrier := ∅
              mult := fun _ => 0
              orient := fun _ => 0
              measurableSet_carrier := MeasurableSet.empty
              carrier_subset := empty_subset _
              rectifiable :=
                Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
              measurable_mult := measurable_const
              mult_pos := fun x hx => absurd hx (notMem_empty x)
              locallyIntegrable_mult := fun K _ _ => by simp
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := by simp }, ?_⟩
    intro ω
    simp [IMRep.action]
  -- minimizing: its mass `0` is below that of every competitor
  have zero_min : ∀ {j : ℕ},
      IsMinimizingIn (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) univ := by
    intro j
    refine ⟨zero_im, fun W S' _ _ _ _ _ _ => ?_⟩
    rw [zero_mass]
    exact zero_le
  -- `∂0 = 0`
  have zero_bdry : ∀ {j : ℕ},
      BoundaryVanishes (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) := by
    intro j
    cases j with
    | zero => trivial
    | succ j => exact GeometricCurrentOn.ext fun ω => rfl
  -- every blow-up of `0` evaluates to `0`, so `0` is a cone
  have eval_blowUp_zero : ∀ {j : ℕ} (x : Euclid P) (lam : ℝ) (h : lam ≠ 0)
      (ω : DifferentialForm (Euclid P) j),
      currentEval (blowUp (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) x lam h) ω = 0 := by
    intro j x lam h ω
    unfold currentEval
    split_ifs <;> rfl
  have zero_cone : ∀ {j : ℕ}, IsConeCurrent (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) := by
    intro j lam hlam ω
    rw [eval_blowUp_zero]
    rfl
  -- empty support: `0` vanishes on the relatively compact ball `B₁(x)`
  have zero_support : ∀ {j : ℕ},
      (0 : GeometricCurrentOn (univ : Set (Euclid P)) j).support = ∅ := by
    intro j
    apply eq_empty_of_forall_notMem
    intro x hx
    apply hx.2
    refine mem_sUnion.2 ⟨ball x 1, ⟨isOpen_ball, ?_, subset_univ _, fun ω _ => rfl⟩,
      mem_ball_self one_pos⟩
    exact (isCompact_closedBall x 1).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  -- density: the ratios are all `0`, and `𝓝[>] 0` is nontrivial
  have zero_density : ∀ {j : ℕ} (x : Euclid P) (θ : ℝ),
      HasMassDensity (0 : GeometricCurrentOn (univ : Set (Euclid P)) j) x θ ↔ θ = 0 := by
    intro j x θ
    simp only [HasMassDensity, zero_mass, ENNReal.zero_div]
    rw [tendsto_const_nhds_iff]
    constructor
    · rintro ⟨h0, h⟩
      have := ENNReal.ofReal_eq_zero.1 h.symm
      linarith
    · rintro rfl
      exact ⟨le_rfl, by simp⟩
  -- assembly with `S = 0` and `S₀ := 0`
  obtain rfl : S = 0 := current_eq_zero S hPn
  refine ⟨zero_cone, ?_, 0, zero_min, zero_bdry, zero_cone, ?_, ?_, ?_⟩
  · intro v _ ω
    rw [eval_blowUp_zero]
    rfl
  · rw [zero_support]
    exact empty_subset _
  · intro t _ y _
    rw [zero_support, zero_support]
    simp
  · intro t _ y _ θ
    rw [zero_density, zero_density]
/-- **Mass densities are unique** (Simon Ch. 1, 3.1, chapter-01.txt lines 562–598: `Θⁿ(μ, x)` is
the common value of the upper and lower densities, i.e. the limit of `(ωₙρⁿ)⁻¹μ(B_ρ(x))` as
`ρ ↓ 0`; used for `Θⁿ(μ_T, x)` in Ch. 7, 3.1, chapter-07.txt lines 302–310).  If
`HasMassDensity T x θ` and `HasMassDensity T x θ'`, the ratio `M_{B_ρ(x)}(T)/(ωₙρⁿ)` tends to both
`ofReal θ` and `ofReal θ'` along the nontrivial filter `𝓝[>] 0` in the Hausdorff space `[0, ∞]`,
so `ofReal θ = ofReal θ'`, and `θ, θ' ≥ 0` give `θ = θ'`. -/
theorem Submission.dimred_cs_mi_hasMassDensity_unique : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (θ θ' : ℝ), HasMassDensity T x θ → HasMassDensity T x θ' → θ = θ' := by
  intro P n U T x θ θ' hθ hθ'
  -- Steps 1–2: `𝓝[>] 0` is nontrivial (`nhdsGT_neBot`) and `ℝ≥0∞` is Hausdorff, so the two
  -- limits of the density ratio coincide.
  have h : ENNReal.ofReal θ = ENNReal.ofReal θ' := tendsto_nhds_unique hθ.2 hθ'.2
  -- Step 3: `ENNReal.ofReal` is injective on `[0, ∞)`.
  exact (ENNReal.ofReal_eq_ofReal_iff hθ.1 hθ'.1).1 h
/-- An approximate tangent plane forces unit `Hⁿ`-density on closed balls (Simon Ch. 3,
Remark 1.5(3), with Definition 1.4).  If `Hⁿ(M ∩ B̄_s(x)) < ∞` and `Q` is an approximate tangent
space of `M` at `x`, then `Hⁿ(M ∩ B̄_ρ(x)) / (ωₙρⁿ) → 1` as `ρ ↓ 0`.  Since
`Hⁿ(η_{x,r}(M) ∩ B̄_1(0)) = r⁻ⁿHⁿ(M ∩ B̄_r(x))` and `Hⁿ(Q ∩ B̄_t(0)) = ωₙtⁿ`, the radial cut-offs
`g_{1-ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}` in `C_c` squeeze `r⁻ⁿHⁿ(M ∩ B̄_r(x))` between blow-up integrals
whose limits lie within `ωₙ(1 ∓ ε)ⁿ`. -/
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
        (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
      rw [image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b →
      ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
        (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: back to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
/-- **Simon Ch. 1, 3.16–3.17 with 3.11(3)**, localized to an open `U`: if `μ` and
`ν = μ.withDensity θ` (`θ` Borel) are finite on compact subsets of `U`, then
`ν(B̄_ρ(x))/μ(B̄_ρ(x)) → θ(x)` as `ρ ↓ 0` for `μ`-a.e. `x ∈ U`.  Besicovitch differentiation
(`Besicovitch.ae_tendsto_rnDeriv`, `Measure.rnDeriv_withDensity`) is applied to `μ⌞Kⱼ` and
`ν⌞Kⱼ = (μ⌞Kⱼ).withDensity θ` for the compact exhaustion
`Kⱼ = B̄_{j+1}(0) ∩ {y : dist(y, z) ≥ 1/(j+1) for all z ∉ U}` of `U`; each `x ∈ U` has
`B_{1/(j+1)}(x) ⊆ Kⱼ` for some `j`, and there the localized ball ratios are the global ones. -/
theorem Submission.rsd_ae_tendsto_withDensity_div_closedBall : ∀ (P : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (θ : Euclid P → ℝ≥0∞), IsOpen U → Measurable θ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞) → ∀ᵐ x ∂μ, x ∈ U → Tendsto (fun ρ : ℝ => μ.withDensity θ (closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (θ x)) := by
  intro P U μ θ hU hθ hμK hνK
  -- the compact exhaustion `K j`
  set K : ℕ → Set (Euclid P) := fun j =>
    closedBall 0 ((j : ℝ) + 1) ∩ {y | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} with hKdef
  have hKclosed' : ∀ j : ℕ, IsClosed {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} := by
    intro j
    have : {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} =
        ⋂ z ∈ Uᶜ, {y | 1 / ((j : ℝ) + 1) ≤ dist y z} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKclosed : ∀ j, IsClosed (K j) := fun j => isClosed_closedBall.inter (hKclosed' j)
  have hKcpt : ∀ j, IsCompact (K j) := fun j =>
    (isCompact_closedBall (0 : Euclid P) _).inter_right (hKclosed' j)
  have hKU : ∀ j, K j ⊆ U := by
    intro j y hy
    by_contra hyU
    have h := hy.2 y hyU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hcover : ∀ x ∈ U, ∃ j : ℕ, ball x (1 / ((j : ℝ) + 1)) ⊆ K j := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (max (2 / δ) ‖x‖)
    have hj1 : 2 / δ < (j : ℝ) + 1 := by
      have := le_max_left (2 / δ) ‖x‖; linarith
    have hj2 : ‖x‖ < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hsmall : 2 / ((j : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hjpos]
      rw [div_lt_iff₀ hδ] at hj1
      linarith
    refine ⟨j, fun y hy => ⟨?_, ?_⟩⟩
    · rw [mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ ‖x‖ + dist y x := by
        have := norm_le_norm_add_norm_sub' y x
        rw [dist_eq_norm]; linarith [norm_sub_rev y x]
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have h3 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hjpos]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      linarith
    · intro z hz
      have hxz : δ ≤ dist x z := by
        by_contra h
        exact hz (hball (by rw [mem_ball, dist_comm]; linarith))
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have htri := dist_triangle x y z
      have h4 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
      rw [dist_comm] at h2
      linarith
  -- Besicovitch on each `K j`
  have hj : ∀ j : ℕ, ∀ᵐ x ∂μ, x ∈ K j → Tendsto (fun ρ : ℝ =>
      ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
      (𝓝[>] 0) (𝓝 (θ x)) := by
    intro j
    have hKm : MeasurableSet (K j) := (hKclosed j).measurableSet
    have : IsFiniteMeasure (μ.restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hμK _ (hKcpt j) (hKU j)).lt_top⟩
    have : IsFiniteMeasure ((μ.withDensity θ).restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hνK _ (hKcpt j) (hKU j)).lt_top⟩
    have h1 := Besicovitch.ae_tendsto_rnDeriv ((μ.withDensity θ).restrict (K j)) (μ.restrict (K j))
    have h2 := Measure.rnDeriv_withDensity (μ.restrict (K j)) hθ
    rw [← restrict_withDensity hKm] at h2
    have h3 : ∀ᵐ x ∂(μ.restrict (K j)), Tendsto (fun ρ : ℝ =>
        ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (θ x)) := by
      filter_upwards [h1, h2] with x hx1 hx2
      rwa [hx2] at hx1
    exact (ae_restrict_iff' hKm).1 h3
  filter_upwards [ae_all_iff.2 hj] with x hx hxU
  obtain ⟨j, hjK⟩ := hcover x hxU
  have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hxK : x ∈ K j := hjK (mem_ball_self hr)
  refine (hx j hxK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ
  have hsub : closedBall x ρ ⊆ K j := (closedBall_subset_ball hρ.2).trans hjK
  rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hsub]
/-- **Simon Ch. 1, 3.1–3.2** (densities may be computed with closed or open balls; cf. 6.2.8 and
`HasMassDensity`): if `ν(B̄_ρ(x)) / (ωₙρⁿ) → θ ∈ [0, ∞]` as `ρ ↓ 0`, then also
`ν(B_ρ(x)) / (ωₙρⁿ) → θ`.  The upper bound follows from `B_ρ(x) ⊆ B̄_ρ(x)`.  For the lower
bound, given `a < θ` pick `t ∈ (0, 1)` with `a < tⁿθ`; then `B̄_{tρ}(x) ⊆ B_ρ(x)` and
`ωₙ(tρ)ⁿ = tⁿ ωₙρⁿ` give `ν(B_ρ(x)) / (ωₙρⁿ) ≥ tⁿ · ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) > a` for small
`ρ`. -/
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
      exact hta
    -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
    filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]

/-- Hadamard's inequality for Gram determinants: `det(⟨vᵢ, vⱼ⟩) ≤ ∏ᵢ |vᵢ|²`.  If `v` is
linearly dependent, a nonzero `c` with `∑ⱼ cⱼ vⱼ = 0` lies in the kernel of the Gram matrix, so
its determinant vanishes; if `v` is independent, the Gram–Schmidt frame of
`dpf_exists_orthonormal_frame_det_gram` gives `det(⟨vᵢ, vⱼ⟩) = (det A)²` with
`|det A| ≤ ∏ᵢ |vᵢ|`. -/
theorem Submission.dtc_bc_lc_pf_gram_det_le_prod_norm_sq : ∀ (P n : ℕ) (v : Fin n → Euclid P), Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) ≤ ∏ i, ‖v i‖ ^ 2 := by
  intro P n v
  by_cases hv : LinearIndependent ℝ v
  · -- independent: square `|det A| ≤ ∏ᵢ |vᵢ|`
    obtain ⟨σ, -, -, hG, -, hA⟩ := Submission.dpf_exists_orthonormal_frame_det_gram P n v hv
    rw [hG, Finset.prod_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  · -- dependent: a nonzero kernel vector `c` of the Gram matrix
    obtain ⟨c, hc, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hv
    have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨c, fun h => hi₀ (congrFun h i₀), funext fun i => ?_⟩
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      have : ∑ j, inner ℝ (v i) (v j) * c j = inner ℝ (v i) (∑ j, c j • v j) := by
        rw [inner_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_right, mul_comm]
      rw [this, hc, inner_zero_right]
    rw [hdet]
    exact Finset.prod_nonneg fun i _ => sq_nonneg _
/-- **Simon Ch. 3, Lemma 1.2 and Remark 1.3**, with bi-Lipschitz Borel pieces in place of `C¹`
submanifolds: a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null set, the disjoint
union of Borel sets `Fᵢ(Bᵢ) ⊆ M`, where `Fᵢ : ℝⁿ → ℝᴾ` is Lipschitz, `Bᵢ` is Borel,
`mᵢ|a − a'| ≤ |Fᵢ(a) − Fᵢ(a')|` on `Bᵢ` for some `mᵢ > 0`, and `DFᵢ` exists and is injective on
`Bᵢ`.  Each Lipschitz `Fⱼ` of the cover maps its non-differentiability points (Rademacher) and
its critical points (the image of `{JFⱼ = 0}`) to `Hⁿ`-null sets.  Mathlib's partition lemma cuts
the regular points into pieces on which `Fⱼ` is close to an injective linear map, hence
bi-Lipschitz; the images of the pieces are Borel (Lusin–Souslin) and are made disjoint as in
Remark 1.3. -/
theorem Submission.dpf_rectifiable_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0 := by
  intro P n M hM hrect
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F₀, hF₀, hcover⟩ := hrect
  choose K hK using hF₀
  -- Step 2: the regular sets `Gⱼ` are Borel and `Hⁿ(Fⱼ(ℝⁿ ∖ Gⱼ)) = 0`
  have hGmeas : ∀ f : Euclid n → Euclid P,
      MeasurableSet {a | DifferentiableAt ℝ f a ∧ Injective (fderiv ℝ f a)} := fun f =>
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet)
  -- Step 2(a): nondifferentiability points have null image (Rademacher)
  have hrad : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 := by
    intro f L hf
    have hz : volume {a : Euclid n | ¬ DifferentiableAt ℝ f a} = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hf.lipschitzOnWith (s := {a | ¬ DifferentiableAt ℝ f a}))
    rw [hvol, hz, mul_zero] at hle
    exact le_antisymm hle bot_le
  -- Step 2(b): critical points have null image.  On a piece where `f` is `ε`-close to a
  -- rank-deficient `A` (`Av = 0`, `‖v‖ = 1`), `|f a - f a'| ≤ (L + 1)|D a - D a'|` for
  -- `D = id - (1 - ε) v ⊗ v`, and `det D = ε`.
  have hsard : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}) = 0 := by
    intro f L hf
    set S := {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}
    have hSmeas : MeasurableSet S :=
      (measurableSet_of_differentiableAt ℝ f).inter
        (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet).compl
    have hR : ∀ R : ℕ, μHE[n] (f '' (S ∩ ball (0 : Euclid n) R)) = 0 := by
      intro R
      set s := S ∩ ball (0 : Euclid n) R
      have hsmeas : MeasurableSet s := hSmeas.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (f '' s) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
        intro ε hε hε1
        rcases s.eq_empty_or_nonempty with hse | hsne
        · rw [hse, image_empty, measure_empty]; exact bot_le
        obtain ⟨t, A, htdisj, htmeas, hst, hA, hAy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
            (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (f '' (s ∩ t k)) ≤
            ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
          intro k
          obtain ⟨y, hy, hAk⟩ := hAy hsne k
          have hAnorm : ‖A k‖ ≤ L := hAk ▸ norm_fderiv_le_of_lipschitz ℝ hf
          have hAni : ¬ Injective (A k) := hAk ▸ hy.1.2
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ A k v = 0 := by
            simp only [Injective, not_forall] at hAni
            obtain ⟨a, b, hab, hne⟩ := hAni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c : ℝ := 1 - (ε : ℝ) with hc
          have hc0 : 0 ≤ c := by
            rw [hc]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hAD : ∀ h, A k (D h) = A k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc]; ring
          have hfD : ∀ a ∈ s ∩ t k, ∀ a' ∈ s ∩ t k,
              ‖f a - f a'‖ ≤ ((L : ℝ) + 1) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hA k a ha a' ha'
            have h2 : ‖A k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hAD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (f a - f a') (A k (a - a'))
            linarith
          have himg : μHE[n] (f '' (s ∩ t k)) ≤
              ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := by
            set X := s ∩ t k
            set g := Function.invFunOn D X
            have hg : ∀ y ∈ D '' X, g y ∈ X ∧ D (g y) = y :=
              fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
            have hLip : LipschitzOnWith (L + 1) (f ∘ g) (D '' X) := by
              refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
              obtain ⟨hgy, hDy⟩ := hg y hy
              obtain ⟨hgy', hDy'⟩ := hg y' hy'
              simp only [comp_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
              calc ‖f (g y) - f (g y')‖ ≤ ((L : ℝ) + 1) * ‖D (g y) - D (g y')‖ :=
                    hfD _ hgy _ hgy'
                _ = _ := by rw [hDy, hDy']
            have hsub : f '' X ⊆ (f ∘ g) '' (D '' X) := by
              rintro _ ⟨a, ha, rfl⟩
              refine ⟨D a, mem_image_of_mem D ha, ?_⟩
              obtain ⟨hga, hDa⟩ := hg (D a) (mem_image_of_mem D ha)
              have := hfD _ hga _ ha
              rw [hDa, sub_self, norm_zero, mul_zero] at this
              exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
            exact (measure_mono hsub).trans
              (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c * v i) = 1 - c * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc]; ring
          calc μHE[n] (f '' (s ∩ t k)) ≤
                ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := himg
            _ = ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
              rw [hvol, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
                NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
              push_cast
              ring
        calc μHE[n] (f '' s) ≤ μHE[n] (⋃ k, f '' (s ∩ t k)) := by
              apply measure_mono
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨k, hk⟩ := mem_iUnion.mp (hst ha)
              exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
          _ ≤ ∑' k, μHE[n] (f '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := ENNReal.tsum_le_tsum hpiece
          _ = ((L : ℝ≥0∞) + 1) ^ n * volume (⋃ k, s ∩ t k) * ε := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right
              · exact fun k => hsmeas.inter (htmeas k)
          _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left.trans inter_subset_right
      have hfin : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have htend : Tendsto (fun ε : NNReal =>
          ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * (ε : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.coe_zero]
          exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      refine le_antisymm (ge_of_tendsto htend ?_) bot_le
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
      exact hbound ε hε.1 hε.2
    refine measure_mono_null ?_ (measure_iUnion_null hR)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
  set G : ℕ → Set (Euclid n) := fun j =>
    {a | DifferentiableAt ℝ (F₀ j) a ∧ Injective (fderiv ℝ (F₀ j) a)}
  have hGnull : ∀ j, μHE[n] (F₀ j '' (G j)ᶜ) = 0 := by
    intro j
    refine measure_mono_null ?_ (measure_union_null (hrad _ _ (hK j)) (hsard _ _ (hK j)))
    rintro _ ⟨a, ha, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F₀ j) a
    · exact Or.inr ⟨a, ⟨hd, fun hi => ha ⟨hd, hi⟩⟩, rfl⟩
    · exact Or.inl ⟨a, hd, rfl⟩
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Step 4: Mathlib's partition of `Gⱼ` into pieces on which `Fⱼ` is close to linear
  have hpart : ∀ j, ∃ (t : ℕ → Set (Euclid n)) (A : ℕ → Euclid n →L[ℝ] Euclid P),
      Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G j ⊆ ⋃ k, t k ∧
      (∀ k, ApproximatesLinearOn (F₀ j) (A k) (G j ∩ t k) (c (A k) / 2)) ∧
      ((G j).Nonempty → ∀ k, ∃ y ∈ G j, A k = fderiv ℝ (F₀ j) y) := fun j =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F₀ j) (G j) (fderiv ℝ (F₀ j))
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun A => c A / 2)
      (fun A => (div_pos (hcpos A) two_pos).ne')
  choose t A htdisj htmeas hGt hAapprox hAy using hpart
  -- Step 5: `Fⱼ` is bi-Lipschitz on `Gⱼ ∩ tⱼₖ` with lower constant `c(Aⱼₖ)/2`
  have hlow : ∀ j k, ∀ a ∈ G j ∩ t j k, ∀ a' ∈ G j ∩ t j k,
      ((c (A j k) / 2 : NNReal) : ℝ) * ‖a - a'‖ ≤ ‖F₀ j a - F₀ j a'‖ := by
    intro j k a ha a' ha'
    obtain ⟨y, hy, hAk⟩ := hAy j ⟨a, ha.1⟩ k
    have hinj : Injective (A j k) := hAk ▸ hy.2
    have h1 := hc (A j k) hinj (a - a')
    have h2 := hAapprox j k a ha a' ha'
    have h3 := norm_sub_norm_le (A j k (a - a')) (F₀ j a - F₀ j a')
    rw [norm_sub_rev (A j k (a - a'))] at h3
    push_cast at h2 ⊢
    linarith
  -- Step 6: enumerate the pieces by `i ↦ (unpair i)`; their images are Borel (Lusin–Souslin)
  set Fi : ℕ → Euclid n → Euclid P := fun i => F₀ (Nat.unpair i).1 with hFi
  set Di : ℕ → Set (Euclid n) := fun i =>
    G (Nat.unpair i).1 ∩ t (Nat.unpair i).1 (Nat.unpair i).2 with hDi
  set mi : ℕ → ℝ := fun i =>
    ((c (A (Nat.unpair i).1 (Nat.unpair i).2) / 2 : NNReal) : ℝ) with hmi
  have hDmeas : ∀ i, MeasurableSet (Di i) := fun i =>
    (hGmeas _).inter (htmeas _ _)
  have hmipos : ∀ i, 0 < mi i := fun i => by
    simp only [hmi, NNReal.coe_div, NNReal.coe_ofNat]
    exact div_pos (hcpos _) two_pos
  have hlowi : ∀ i, ∀ a ∈ Di i, ∀ a' ∈ Di i, mi i * ‖a - a'‖ ≤ ‖Fi i a - Fi i a'‖ :=
    fun i => hlow _ _
  have hNmeas : ∀ i, MeasurableSet (Fi i '' Di i) := by
    intro i
    refine (hDmeas i).image_of_continuousOn_injOn (hK _).continuous.continuousOn ?_
    intro a ha a' ha' h
    have := hlowi i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmipos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 7: disjointify the images inside `M`
  set Ñ : ℕ → Set (Euclid P) := fun i => Fi i '' Di i ∩ M
  have hÑmeas : ∀ i, MeasurableSet (Ñ i) := fun i => (hNmeas i).inter hM
  set B : ℕ → Set (Euclid n) := fun i => Di i ∩ Fi i ⁻¹' disjointed Ñ i with hB
  have himg : ∀ i, Fi i '' B i = disjointed Ñ i := by
    intro i
    rw [hB, image_inter_preimage]
    exact inter_eq_right.mpr ((disjointed_subset Ñ i).trans inter_subset_left)
  refine ⟨Fi, B, mi, fun i => ⟨K _, hK _⟩,
    fun i => (hDmeas i).inter ((hK _).continuous.measurable (MeasurableSet.disjointed hÑmeas i)),
    hmipos, fun i a ha a' ha' => hlowi i a ha.1 a' ha'.1, fun i a ha => ha.1.1,
    fun i => himg i ▸ MeasurableSet.disjointed hÑmeas i,
    fun i => himg i ▸ ((disjointed_subset Ñ i).trans inter_subset_right), ?_, ?_⟩
  · intro i j hij
    rw [himg i, himg j]
    exact disjoint_disjointed Ñ hij
  -- Step 8: the remainder lies in `M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ ∖ Gⱼ)`
  · have hU : (⋃ i, Fi i '' B i) = ⋃ i, Ñ i := by
      simp_rw [himg]
      exact iUnion_disjointed
    rw [hU]
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hGnull))
    rintro x ⟨hxM, hxN⟩
    rcases hcover hxM with hx0 | hx
    · exact Or.inl hx0
    · obtain ⟨j, a, rfl⟩ := mem_iUnion.mp hx
      by_cases ha : a ∈ G j
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt j ha)
        apply hxN
        refine mem_iUnion.mpr ⟨Nat.pair j k, ⟨a, ?_, ?_⟩, hxM⟩
        · simp only [hDi, Nat.unpair_pair]
          exact ⟨ha, hk⟩
        · simp only [hFi, Nat.unpair_pair]
      · exact Or.inr (mem_iUnion.mpr ⟨j, a, ha, rfl⟩)
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.ptd_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]
/-- **Algebra of unit orientations** (Simon 6.1.1, 6.1.7, 6.2.2): for `n`-vectors on `ℝᴾ`,
(a) two unit orientations `ξ`, `ξ'` of the same subspace `T` agree up to sign, `ξ' = ±ξ`;
(b) a unit orientation `ξ` satisfies `|ξ(β)| ≤ ‖β‖` for every `n`-covector `β`;
(c) if `A : ℝⁿ → ℝᴾ` is injective, then `J_A = det(⟨Aeₖ, Aeₗ⟩)^{1/2} > 0` and
`J_A⁻¹ A_#e : β ↦ J_A⁻¹ β(Ae₁, …, Aeₙ)` is a unit orientation of `range A`;
(d) if `A` is not injective, then `β(Ae₁, …, Aeₙ) = 0` for every `n`-covector `β`.
For an orthonormal `τ` and `bⱼ ∈ span τ`, with `M = (⟨τᵢ, bⱼ⟩)`, `α(b) = det M · α(τ)` (expand
`α` in the basis `τ` of `span τ`) and `det(⟨bₖ, bₗ⟩) = (det M)²` (Parseval).  Two orthonormal
frames of `T` therefore differ by `det M = ±1`; for injective `A`, a Gram–Schmidt frame `τ` of
`range A` gives an invertible `M` and `J_A = |det M|`; a non-injective `A` makes `(Aeₖ)` linearly
dependent. -/
theorem Submission.dtc_bc_lc_pfi_unitOrientation_algebra : ∀ (P n : ℕ), (∀ (ξ ξ' : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → IsUnitOrientationOf ξ' T → ξ' = ξ ∨ ξ' = -ξ) ∧ (∀ (ξ : MultiVector P n) (T : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ T → ∀ β : Covector (Euclid P) n, |ξ β| ≤ ‖β‖) ∧ (∀ A : Euclid n →L[ℝ] Euclid P, Injective A → 0 < Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) ∧ IsUnitOrientationOf ((Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))))⁻¹ • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun k : Fin n => A (EuclideanSpace.single k 1))) (LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P))) ∧ ∀ A : Euclid n →L[ℝ] Euclid P, ¬ Injective A → ∀ β : Covector (Euclid P) n, β (fun k : Fin n => A (EuclideanSpace.single k 1)) = 0 := by
  intro P n
  -- Step 1 (expansion): for orthonormal `τ` and `bⱼ ∈ span τ`, `α(b) = det(⟨τᵢ, bⱼ⟩) α(τ)`
  have hE : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n,
        α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
    intro τ b hτ hb α
    set L := Submodule.span ℝ (Set.range τ)
    -- `τ` is a basis `e` of `L`
    let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
    have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
      rw [Module.Basis.span_apply hτ.linearIndependent i]
    -- the restriction `α_L` of `α` to `L`
    let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
    let b' : Fin n → L := fun j => ⟨b j, hb j⟩
    have h1 : α b = αL b' := rfl
    have h2 : α τ = αL e := by
      show α τ = α (fun i => (e i : Euclid P))
      congr 1
      funext i
      exact (he i).symm
    -- coordinates of `b'` in `e` are the inner products with `τ`
    have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
      intro i j
      have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
        have := congrArg (Subtype.val) (e.sum_repr (b' j))
        simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
        exact this.symm
      rw [hs, hτ.inner_right_fintype]
    have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
      ext i j
      rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
    -- `α_L = α_L(e) • det_e`
    have h3 : αL b' = αL e * e.det b' := by
      conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
      rfl
    rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
  -- Step 2 (coordinates): for orthonormal `τ` and `bⱼ ∈ span τ`, `bⱼ = Σᵢ ⟨τᵢ, bⱼ⟩ τᵢ`
  have hcoord : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ j, b j = ∑ i, inner ℝ (τ i) (b j) • τ i := by
    intro τ b hτ hb j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hb j)
    have hci : ∀ i, inner ℝ (τ i) (b j) = c i := fun i => by rw [← hc, hτ.inner_right_fintype]
    calc b j = ∑ i, c i • τ i := hc.symm
      _ = ∑ i, inner ℝ (τ i) (b j) • τ i := Finset.sum_congr rfl fun i _ => by rw [hci i]
  -- Step 3 (Parseval): `(⟨bₖ, bₗ⟩) = MᵀM` for `M = (⟨τᵢ, bⱼ⟩)`, so `det(⟨bₖ, bₗ⟩) = (det M)²`
  have hG : ∀ (τ b : Fin n → Euclid P), Orthonormal ℝ τ →
      (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) →
        (Matrix.of fun k l => inner ℝ (b k) (b l)).det =
          (Matrix.of fun i j => inner ℝ (τ i) (b j)).det ^ 2 := by
    intro τ b hτ hb
    have hmat : (Matrix.of fun k l => inner ℝ (b k) (b l)) =
        (Matrix.of fun i j => inner ℝ (τ i) (b j)).transpose *
          Matrix.of fun i j => inner ℝ (τ i) (b j) := by
      ext k l
      rw [Matrix.mul_apply, Matrix.of_apply]
      conv_lhs => rw [hcoord τ b hτ hb k]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
    rw [hmat, Matrix.det_mul, Matrix.det_transpose, sq]
  -- Step 4: the standard basis `eₖ = single k 1` of `ℝⁿ` is independent and spanning
  have he_fun : ⇑(EuclideanSpace.basisFun (Fin n) ℝ).toBasis =
      fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n) := by
    rw [OrthonormalBasis.coe_toBasis]
    funext k
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ k
  have he_li : LinearIndependent ℝ (fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n)) := by
    have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent
    rwa [he_fun] at this
  have he_span :
      Submodule.span ℝ (Set.range fun k : Fin n => (EuclideanSpace.single k 1 : Euclid n)) = ⊤ := by
    have := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.span_eq
    rwa [he_fun] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a) `τ'` lies in `span τ`, so `α(τ') = det O · α(τ)` with `(det O)² = det 1 = 1`
    rintro ξ ξ' T ⟨τ, hτ, hτT, hξ⟩ ⟨τ', hτ', hτ'T, hξ'⟩
    have hmem : ∀ j, τ' j ∈ Submodule.span ℝ (Set.range τ) := fun j => by
      rw [hτT, ← hτ'T]
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨d, hexp, hd⟩ : ∃ d : ℝ, (∀ α : Covector (Euclid P) n, α τ' = d * α τ) ∧ d ^ 2 = 1 := by
      refine ⟨_, hE τ τ' hτ hmem, ?_⟩
      rw [← hG τ τ' hτ hmem]
      have h1 : (Matrix.of fun k l => inner ℝ (τ' k) (τ' l)) = 1 := by
        ext k l
        rw [Matrix.of_apply, Matrix.one_apply]
        exact orthonormal_iff_ite.mp hτ' k l
      rw [h1, Matrix.det_one]
    -- the signs `s, s' = ±1` of `ξ = s τ` and `ξ' = s' τ'`
    obtain ⟨s, hs, hξs⟩ : ∃ s : ℝ, s * s = 1 ∧ ∀ α, ξ α = s * α τ := by
      rcases hξ with h | h
      · exact ⟨1, one_mul 1, fun α => by rw [h, one_mul]⟩
      · exact ⟨-1, by norm_num, fun α => by rw [h, neg_one_mul]⟩
    obtain ⟨s', hs', hξs'⟩ : ∃ s : ℝ, s * s = 1 ∧ ∀ α, ξ' α = s * α τ' := by
      rcases hξ' with h | h
      · exact ⟨1, one_mul 1, fun α => by rw [h, one_mul]⟩
      · exact ⟨-1, by norm_num, fun α => by rw [h, neg_one_mul]⟩
    -- `ξ' = c ξ` with `c = s' · det O · s` and `c² = 1`
    have hc : ∀ α : Covector (Euclid P) n, ξ' α = (s' * d * s) * ξ α := by
      intro α
      rw [hξs' α, hexp α, hξs α]
      linear_combination (-(s' * d * α τ)) * hs
    have hc1 : (s' * d * s) * (s' * d * s) = 1 := by
      linear_combination (s' * s' * d ^ 2) * hs + (s' * s') * hd + hs'
    rcases mul_self_eq_one_iff.mp hc1 with h | h
    · left
      exact ContinuousLinearMap.ext fun α => by rw [hc α, h, one_mul]
    · right
      exact ContinuousLinearMap.ext fun α => by rw [hc α, h, neg_apply, neg_one_mul]
  · -- (b) `|ξ(β)| = |β(τ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖`
    rintro ξ T ⟨τ, hτ, -, hξ⟩ β
    have h1 : |β τ| ≤ ‖β‖ := by
      have h := β.le_opNorm τ
      rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h β]
      exact h1
    · rw [h β, abs_neg]
      exact h1
  · -- (c) a Gram–Schmidt frame `τ` of `range A = span (Aeₖ)`, and `M = (⟨τᵢ, Aeⱼ⟩)`
    intro A hA
    set v : Fin n → Euclid P := fun k => A (EuclideanSpace.single k 1) with hv_def
    have hv : LinearIndependent ℝ v :=
      he_li.map' (A : Euclid n →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.mpr hA)
    have hspan_v :
        Submodule.span ℝ (Set.range v) = LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P) := by
      rw [LinearMap.range_eq_map, ← he_span, Submodule.map_span, ← Set.range_comp]
      rfl
    obtain ⟨τ, hτ, hτspan⟩ : ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
        Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range v) :=
      ⟨InnerProductSpace.gramSchmidtNormed ℝ v, InnerProductSpace.gramSchmidtNormed_orthonormal hv,
        by rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt]⟩
    have hvmem : ∀ j, v j ∈ Submodule.span ℝ (Set.range τ) := fun j => by
      rw [hτspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    -- `M` is invertible: `M c = 0` gives `Σⱼ cⱼ vⱼ = Σᵢ (M c)ᵢ τᵢ = 0`, so `c = 0`
    have hMne : (Matrix.of fun i j => inner ℝ (τ i) (v j)).det ≠ 0 := by
      intro h0
      obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hc0
      funext j
      refine Fintype.linearIndependent_iff.mp hv c ?_ j
      calc ∑ j, c j • v j = ∑ j, c j • ∑ i, inner ℝ (τ i) (v j) • τ i :=
            Finset.sum_congr rfl fun j _ => by rw [← hcoord τ v hτ hvmem j]
        _ = ∑ i, (∑ j, inner ℝ (τ i) (v j) * c j) • τ i := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [mul_comm]
        _ = 0 := by
            refine Finset.sum_eq_zero fun i _ => ?_
            have := congrFun hc i
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
            rw [this, zero_smul]
    obtain ⟨d, hd0, hexp, hgram⟩ : ∃ d : ℝ, d ≠ 0 ∧ (∀ α : Covector (Euclid P) n, α v = d * α τ) ∧
        (Matrix.of fun k l => inner ℝ (v k) (v l)).det = d ^ 2 :=
      ⟨_, hMne, hE τ v hτ hvmem, hG τ v hτ hvmem⟩
    -- `J_A = ((det M)²)^{1/2} = |det M| > 0` and `J_A⁻¹ β(Ae) = sign(det M) β(τ)`
    have hJ : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n =>
        inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1)))) = |d| := by
      rw [← Real.sqrt_sq_eq_abs, ← hgram]
    rw [hJ]
    refine ⟨abs_pos.mpr hd0, τ, hτ, hτspan.trans hspan_v, ?_⟩
    have hval : ∀ α : Covector (Euclid P) n,
        (|d|⁻¹ • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ v) α = (|d|⁻¹ * d) * α τ := by
      intro α
      rw [smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul, hexp α, mul_assoc]
    rcases lt_or_gt_of_ne hd0 with hneg | hpos
    · right
      intro α
      rw [hval, abs_of_neg hneg, inv_neg, neg_mul, inv_mul_cancel₀ hd0, neg_one_mul]
    · left
      intro α
      rw [hval, abs_of_pos hpos, inv_mul_cancel₀ hd0, one_mul]
  · -- (d) if `(Aeₖ)` were independent, `A` would be injective (`e` spans `ℝⁿ`)
    intro A hA β
    have hdep : ¬ LinearIndependent ℝ (fun k : Fin n => A (EuclideanSpace.single k 1)) := fun hli =>
      hA (LinearMap.injective_of_linearIndependent (f := (A : Euclid n →ₗ[ℝ] Euclid P)) he_span hli)
    exact β.toAlternatingMap.map_linearDependent _ hdep
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1

/-- Localized Besicovitch density (Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6, with
Simon Ch. 1, Theorem 3.16 = Mathlib's `Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be
open, `A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e.
`x` and every `ε > 0`, `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`; the
exceptional set does not depend on `ε`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `a/β`, where
  `a = Hⁿ(A ∩ B̄_ρ(x))` and `β = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `a/β > 1 − ε`, which forces `0 < β < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = β − a ≤ εβ`. -/
theorem Submission.ptd_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many open balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2–3: Besicovitch density for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`, off one
  -- `Hⁿ⌞A`-null set for all `y ∈ D` at once
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  -- Step 4: `x ∈ B(y, r y)` for some `y ∈ D`, so `B̄_ρ(x) ⊆ B̄(y, r y)` for `ρ < δ`
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- (i)–(ii): for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  -- (iii): `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄(y, r y)) < ∞` for `ρ < δ`
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- (iv): `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 5: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- (a) `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- (b) `ε < 1`: eventually `a / β > 1 − ε`, with `β ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set β := μHE[n] (B ∩ closedBall x ρ)
    set a := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hβtop : β ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + a = β := hsplit ρ
    -- `β ≠ 0`, since otherwise `a / β = 0 / 0 = 0 ≤ 1 − ε`
    have hβ0 : β ≠ 0 := by
      intro h0
      have ha0 : a = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : a / β = 0 := by rw [ha0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * β < a :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hβ0) (Or.inl hβtop)).1 hρq
    -- `e + (1 − ε)β ≤ e + a = β = εβ + (1 − ε)β`, and `(1 − ε)β ≠ ∞`
    have h1 : e + (1 - ε) * β ≤ ε * β + (1 - ε) * β := by
      calc e + (1 - ε) * β ≤ e + a := by gcongr
        _ = β := hsplitρ
        _ = (ε + (1 - ε)) * β := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * β + (1 - ε) * β := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hβtop) h1

/-- **Simon Ch. 3, Remark 1.5(3)** (the upper bound, with `ε = 1`): if `D` has approximate
tangent space `Q` at `x` and `Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all
small `ρ > 0`.

* Test Definition 1.4 with `φ = max(0, min(1, 2 − |w|)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`:
  `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`, so for `0 < ρ < r₁` it is `< C := |Λ| + 1`, and
  `2ρ < r₀`.
* By the blow-up scaling, `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, so `φ` is
  integrable on `η_{x,ρ}(D)` and `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} φ dHⁿ < C`.
* Scaling back, `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ Cρⁿ`. -/
theorem Submission.ptd_tl_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1: the cutoff `φ = max(0, min(1, 2 − ‖w‖)) ∈ C_c`, `1_{B̄₁(0)} ≤ φ ≤ 1_{B̄₂(0)}`
  have hout : ∀ w : Euclid P, w ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖w‖)) = 0 := by
    intro w hw
    rw [mem_closedBall_zero_iff, not_le] at hw
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let φ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun w => max 0 (min 1 (2 - ‖w‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hφ0 : ∀ w, 0 ≤ φ w := fun w => le_max_left _ _
  have hφ1 : ∀ w, φ w ≤ 1 := fun w => max_le zero_le_one (min_le_left _ _)
  have hφB : ∀ w ∈ closedBall (0 : Euclid P) 1, φ w = 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    show max 0 (min 1 (2 - ‖w‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 2: `∫_{η_{x,ρ}(D)} φ dHⁿ → Λ := ∫_Q φ dHⁿ`; choose `r₁` such that
  -- `∫_{η_{x,ρ}(D)} φ dHⁿ < |Λ| + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set Λ := ∫ w in (Q : Set (Euclid P)), φ w ∂μHE[n]
  have hC : (0 : ℝ) ≤ |Λ| + 1 := by positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ w in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, φ w ∂μHE[n]) < |Λ| + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 φ).eventually_lt_const ((le_abs_self Λ).trans_lt (lt_add_one _))).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨|Λ| + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hI, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := (ENNReal.ofReal_pos.2 hρ).ne'
  -- the blow-up scaling with `R = 2` and `R = 1`
  have h2 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 2 D hρ
  have h1 := Submission.ptd_tl_blowUp_measure_scaling P n x ρ 1 D hρ
  rw [mul_one ρ] at h1
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  -- Step 3: `Hⁿ(T ∩ B̄₂(0)) = ρ⁻ⁿHⁿ(D ∩ B̄_{2ρ}(x)) < ∞`, as `2ρ < r₀`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    rw [h2]
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 hρ0)) ?_
    refine ne_top_of_le_ne_top hfin (measure_mono (Set.inter_subset_inter_right _ ?_))
    exact closedBall_subset_closedBall (by linarith)
  -- Step 4: `|φ| ≤ 1_{B̄₂(0)}`, which is integrable for `Hⁿ⌞T`; hence so is `φ`
  have hint : Integrable (fun w => φ w) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      φ.continuous.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hw : w ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hw, Real.norm_of_nonneg (hφ0 w)]
        exact hφ1 w
      · rw [Set.indicator_of_notMem hw, norm_le_zero_iff]
        exact hout w hw
  -- Step 5: `Hⁿ(T ∩ B̄₁(0)) = ∫⁻ 1_{B̄₁(0)} d(Hⁿ⌞T) ≤ ∫⁻ φ d(Hⁿ⌞T) = ∫_T φ dHⁿ < |Λ| + 1`
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (|Λ| + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ w, (closedBall (0 : Euclid P) 1).indicator 1 w ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ w, ENNReal.ofReal (φ w) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun w => ?_
          by_cases hw : w ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hw, Pi.one_apply, hφB w hw, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hw]
            exact zero_le
      _ = ENNReal.ofReal (∫ w, φ w ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hφ0)).symm
      _ ≤ ENNReal.ofReal (|Λ| + 1) := ENNReal.ofReal_le_ofReal hI.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) = ρⁿHⁿ(T ∩ B̄₁(0)) ≤ (|Λ| + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      = ENNReal.ofReal ρ ^ n * ((ENNReal.ofReal ρ)⁻¹ ^ n * μHE[n] (D ∩ closedBall x ρ)) := by
        rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel hρ0 ENNReal.ofReal_ne_top, one_pow,
          one_mul]
    _ = ENNReal.ofReal ρ ^ n * μHE[n] (T ∩ closedBall 0 1) := by rw [h1]
    _ ≤ ENNReal.ofReal ρ ^ n * ENNReal.ofReal (|Λ| + 1) := by gcongr
    _ = ENNReal.ofReal ((|Λ| + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow hρ.le, mul_comm (ENNReal.ofReal ρ ^ n)]
/-- Zero `n`-density of the excess `B ∖ A` (step 6 of the tangent-locality argument for a piece):
if `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0` as
`ρ ↓ 0`.  With `ε = 1/2`, subadditivity and cancellation of the finite half give
`Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ`; then `ε = δ/(2C + 1)` gives
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.ptd_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hG hE
  -- Step 1: for `ρ > 0`, `ofReal (Cρⁿ) = ofReal C · (ofReal ρ)ⁿ`
  have hA : ∀ ρ : ℝ, 0 < ρ → ρ < r₁ →
      μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal C * ENNReal.ofReal ρ ^ n := by
    intro ρ hρ hρ₁
    rw [← ENNReal.ofReal_pow hρ.le, ← ENNReal.ofReal_mul' (pow_nonneg hρ.le n)]
    exact hG ρ hρ hρ₁
  -- Step 2: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ κ (ofReal ρ)ⁿ` with `κ = 2 ofReal C`
  set κ : ℝ≥0∞ := 2 * ENNReal.ofReal C with hκ
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ κ * ENNReal.ofReal ρ ^ n := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hE 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := hρ.2.le.trans (min_le_left _ _)
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hβ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hρ₀)))
    -- `B ∩ B̄_ρ(x) ⊆ (A ∩ B̄_ρ(x)) ∪ ((B ∖ A) ∩ B̄_ρ(x))`, so subadditivity applies
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- `β/2 + β/2 = β ≤ a + e ≤ a + β/2`; cancelling the finite `β/2` gives `β/2 ≤ a`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hβ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add le_rfl he)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * (ENNReal.ofReal C * ENNReal.ofReal ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = κ * ENNReal.ofReal ρ ^ n := by rw [hκ, mul_assoc]
  -- Step 3: for `δ > 0`, `ε = δ/(κ + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δ (ofReal ρ)ⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hκ₁ : κ + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hκ₀ : κ + 1 ≠ 0 := by positivity
  filter_upwards [hB, hE (δ / (κ + 1)) (ENNReal.div_pos hδ.ne' hκ₁)] with ρ hρB hρe
  -- Step 4: hence `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / (ofReal ρ)ⁿ ≤ δ`
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ)
      ≤ δ / (κ + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (κ + 1) * ((κ + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hκ₀ hκ₁]
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value
(by `Submission.ptd_tl_blowUp_measure_scaling`), and this tends to `0`. -/
theorem Submission.ptd_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)` is Borel
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Step 2: for every `f ∈ C_c`, `Δ_f(ρ) = ∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- (a): `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- (b): `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- (c)–(e) give `|Δ_f(ρ)| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for `0 < ρ < r₀/R`; (f) sends the
    -- bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- (c): for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- (d): `Δ_f(ρ) = ∫_{η_{x,ρ}(B ∖ A)} f`, as `η_{x,ρ}(B ∖ A) = η_{x,ρ}(B) ∖ η_{x,ρ}(A)`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- (e): `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- (f): `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.ptd_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Steps 3–4: transfer the limits of Definition 1.4 in both directions; `finrank Q = n` is shared
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _

/-- **Simon Ch. 3, Remarks 1.5(2)–(3) and the proof of Theorem 1.6 "⇒"**: let `U` be open,
`A ⊆ B ⊆ U` Borel, and `Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x`,
simultaneously for every subspace `Q`, `B` has approximate tangent space `Q` at `x` iff `A` does.

* Off one `Hⁿ⌞A`-null set, independent of `Q`, `x ∈ A` and for every `ε > 0`,
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0` (Besicovitch).
* `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`.
* A tangent plane of `B` or of `A` at `x` gives `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for small `ρ` (via
  `A ⊆ B` in the first case), hence `Hⁿ((B \ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals
  of `B` and `A` have the same limits. -/
theorem Submission.ptd_ae_approxTangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 2–4: off one `Hⁿ⌞A`-null set, chosen before `Q`, `x ∈ A` and the excess of `B` over
  -- `A` near `x` is eventually small relative to `Hⁿ(B ∩ B̄_ρ(x))`
  filter_upwards [Submission.ptd_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB_le : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 6–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` makes the excess `o(ρⁿ)`, which forces
  -- the same approximate tangent spaces
  have hiff : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.ptd_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.ptd_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth
          hexc) Q
  -- Step 8: step 5 turns the assumed tangent plane into the growth bound
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (hiff C r₁ hr₁ fun ρ hρ hρr₁ => (hAB_le ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.ptd_tl_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB_le (s / 2))) hTA
    exact (hiff C r₁ hr₁ hgrowth).2 hTA
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
/-- Borel image and null-set pullback along a bi-Lipschitz piece: if `F : ℝⁿ → ℝᴾ` is Lipschitz,
`B ⊆ ℝⁿ` is Borel and `m‖a − a'‖ ≤ ‖F a − F a'‖` on `B` (`m > 0`), then `F(B)` is Borel
(Lusin–Souslin), and a property holding `Hⁿ⌞F(B)`-a.e. holds at `F b` for Lebesgue-a.e. `b ∈ B`:
`invFunOn F B` is `m⁻¹`-Lipschitz on `F(B)` (Simon Ch. 2, 1.8(i)) and maps the `Hⁿ`-null bad
image set onto a superset of the bad parameters, and `Hⁿ` is Lebesgue measure on `ℝⁿ`. -/
theorem Submission.ptd_piece_image_measurable_ae_pullback : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → MeasurableSet (F '' B) ∧ ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ b ∂(volume.restrict B), p (F b) := by
  intro P n F B L m hF hB hm hlow
  -- Step 1: the lower bound makes `F` injective on `B`
  have hinj : InjOn F B := fun a ha a' ha' h => by
    have hle := hlow a ha a' ha'
    rw [h, sub_self, norm_zero] at hle
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hle hm))
  -- Step 2: Lusin–Souslin
  have hFB : MeasurableSet (F '' B) := hB.image_of_continuousOn_injOn hF.continuous.continuousOn hinj
  refine ⟨hFB, fun p hp => ?_⟩
  -- Step 3: `G = invFunOn F B` is `m⁻¹`-Lipschitz on `F '' B`
  have hG : LipschitzOnWith (Real.toNNReal m⁻¹) (invFunOn F B) (F '' B) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩
    rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn ha', dist_eq_norm, dist_eq_norm,
      inv_mul_eq_div, le_div_iff₀' hm]
    exact hlow a ha a' ha'
  -- Step 4: the bad parameters lie in the `G`-image of the `Hⁿ`-null bad image set
  rw [ae_restrict_iff' hFB, ae_iff] at hp
  rw [ae_restrict_iff' hB, ae_iff, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hnull : μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)}) = 0 := by
    refine le_zero_iff.1 ?_
    calc μHE[n] (invFunOn F B '' {y | ¬(y ∈ F '' B → p y)})
        ≤ (Real.toNNReal m⁻¹ : ℝ≥0∞) ^ n * μHE[n] {y | ¬(y ∈ F '' B → p y)} :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hG.mono fun y hy => (not_imp.1 hy).1)
      _ = 0 := by rw [hp, mul_zero]
  refine measure_mono_null (fun b hb => ?_) hnull
  obtain ⟨hbB, hpb⟩ := not_imp.1 (show ¬(b ∈ B → p (F b)) from hb)
  exact ⟨F b, show ¬(F b ∈ F '' B → p (F b)) from not_imp.2 ⟨mem_image_of_mem F hbB, hpb⟩,
    hinj.leftInvOn_invFunOn hbB⟩
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.pit_setIntegral_blowUpMap_image : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
  intro P n M x r hr f
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
      ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
    ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
  -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
  have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
    intro S
    have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
      rw [image_image, he]
      rfl
    rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
  have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
      Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
      e.image_preimage]
  -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
  rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]

/-- **Rescaled area formula** (Jacobian kept abstract): if `F` is continuous, `B` and `J ≥ 0` are
Borel and `∫⁻_{F(B)} g dHⁿ = ∫⁻_B J(x) g(F(x)) dλ(x)` for every `g ≥ 0`, then for `r > 0` and
continuous `f`,
`∫_{η_{F(b),r}(F(B))} f dHⁿ = ∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dλ(c)`.
The area hypothesis says `Hⁿ⌞F(B) = F_#ν` with `ν = J λ⌞B`, which transports every integral;
the substitution `a = b + rc` produces the factor `rⁿ` that cancels the `r⁻ⁿ` of the blow-up. -/
theorem Submission.pit_blowUp_image_setIntegral_eq_rescaled : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (b : Euclid n) (r : ℝ) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) → 0 < r → Continuous f → ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap (F b) r '' (F '' B), f z ∂μHE[n] = ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume := by
  intro P n F B J b r f hF hB hJ hJ0 harea hr hf
  -- blow-up scaling: `∫_{η(F(B))} f dHⁿ = r⁻ⁿ ∫_{F(B)} f ∘ η dHⁿ`, `η = η_{F(b),r}`
  rw [Submission.pit_setIntegral_blowUpMap_image P n (F '' B) (F b) r hr f]
  -- `Hⁿ⌞F(B) = F_#ν`: the area hypothesis with `g = 1_T` for every Borel `T`
  have hmeas : μHE[n].restrict (F '' B) =
      Measure.map F ((volume.restrict B).withDensity fun x => ENNReal.ofReal (J x)) := by
    ext T hT
    have h := harea (T.indicator 1)
    rw [lintegral_indicator_one hT] at h
    rw [h, Measure.map_apply hF.measurable hT, withDensity_apply _ (hT.preimage hF.measurable),
      ← lintegral_indicator (hT.preimage hF.measurable)]
    congr 1
    funext x
    by_cases hx : F x ∈ T <;> simp [hx]
  -- `∫_{F(B)} f ∘ η dHⁿ = ∫ 1_B J (f ∘ η ∘ F) dλ`, with no integrability needed
  have hη : Continuous fun z => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r z) := by
    unfold Poincare.SimonGMT.Chapter03.blowUpMap
    fun_prop
  have hpull : ∫ y in F '' B, f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r y) ∂μHE[n] =
      ∫ x, B.indicator J x * f (r⁻¹ • (F x - F b)) ∂volume := by
    rw [hmeas, integral_map hF.aemeasurable hη.aestronglyMeasurable]
    have h := integral_withDensity_eq_integral_smul (μ := volume.restrict B) hJ.real_toNNReal
      (fun x => f (Poincare.SimonGMT.Chapter03.blowUpMap (F b) r (F x)))
    simp only [ENNReal.ofReal]
    rw [h, ← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B
    · simp [hx, NNReal.smul_def, hJ0 x, Poincare.SimonGMT.Chapter03.blowUpMap]
    · simp [hx]
  rw [hpull]
  -- substitution `a = b + rc`: `∫ G(b + rc) dλ(c) = r⁻ⁿ ∫ G dλ`
  set G : Euclid n → ℝ := fun x => B.indicator J x * f (r⁻¹ • (F x - F b))
  have hsubst : ∫ c, G (b + r • c) ∂volume = r⁻¹ ^ n * ∫ a, G a ∂volume := by
    rw [Measure.integral_comp_smul volume (fun x => G (b + x)) r,
      integral_add_left_eq_self (fun x => G x) b, finrank_euclideanSpace_fin, smul_eq_mul,
      ← inv_pow, abs_of_pos (pow_pos (inv_pos.2 hr) n)]
  exact hsubst.symm
/-- Co-Lipschitz bounds pass to the derivative at density points: if `m > 0`,
`m‖a − b‖ ≤ ‖F(a) − F(b)‖` for every `a ∈ B` (`B` arbitrary), `F` is differentiable at `b` and
`λ(B ∩ B̄_ρ(b)) / λ(B̄_ρ(b)) → 1` as `ρ ↓ 0`, then `m‖c‖ ≤ ‖DF(b)c‖` for every `c`.
For small `r > 0` the ball `B_{rδ}(b + rc)`, a fixed fraction `(δ / (‖c‖ + δ))ⁿ` of
`B̄_{r(‖c‖+δ)}(b)`, must meet `B`; the bound at such a point and differentiability give
`m‖c‖ ≤ ‖DF(b)c‖ + δ(m + ‖DF(b)‖ + ‖c‖ + δ)`, and `δ ↓ 0`. -/
theorem Submission.pit_fderiv_lower_bound_of_density : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (m : ℝ) (b : Euclid n), 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → ∀ c : Euclid n, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ := by
  intro P n F B m b hm hB hF hdens c
  set L := fderiv ℝ F b with hL
  have hFL : HasFDerivAt F L b := hF.hasFDerivAt
  -- main estimate: for every `δ > 0`, `m‖c‖ ≤ ‖Lc‖ + δ (m + ‖L‖ + ‖c‖ + δ)`
  have key : ∀ δ : ℝ, 0 < δ → m * ‖c‖ ≤ ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ) := by
    intro δ hδ
    have hK : 0 < ‖c‖ + δ := by positivity
    -- differentiability: `‖F a - F b - L (a - b)‖ ≤ δ ‖a - b‖` near `b`
    obtain ⟨ε, hε, hεF⟩ := Metric.eventually_nhds_iff.1 (hFL.isLittleO.bound hδ)
    -- density: the ratio exceeds `1 - q`, `q = (δ / (‖c‖ + δ)) ^ n`, on some `(0, ρ₀)`
    obtain ⟨q, hq_def⟩ : ∃ q : ℝ≥0∞, q = ENNReal.ofReal ((δ / (‖c‖ + δ)) ^ n) := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq_def, Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hlt : 1 - q < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq
    obtain ⟨ρ₀, hρ₀, hρ₀sub⟩ :=
      mem_nhdsGT_iff_exists_Ioo_subset.1 (hdens.eventually_const_lt hlt)
    have hρ₀' : 0 < ρ₀ := hρ₀
    -- the radius `ρ = r (‖c‖ + δ)`
    obtain ⟨ρ, hρ, hρε, hρρ₀⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ε ∧ ρ < ρ₀ :=
      ⟨min ε ρ₀ / 2, by positivity, by linarith [min_le_left ε ρ₀, lt_min hε hρ₀'],
        by linarith [min_le_right ε ρ₀, lt_min hε hρ₀']⟩
    obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / (‖c‖ + δ) := ⟨_, rfl⟩
    have hr : 0 < r := by rw [hr_def]; positivity
    have hrK : r * (‖c‖ + δ) = ρ := by rw [hr_def]; field_simp
    -- some point of `B` lies in `B_{rδ}(b + r c)`, else the ratio at `ρ` is `≤ 1 - q`
    obtain ⟨a, haB, ha⟩ : ∃ a ∈ B, ‖a - (b + r • c)‖ < r * δ := by
      by_contra! hcon
      have hsub : ball (b + r • c) (r * δ) ⊆ closedBall b ρ := by
        intro x hx
        rw [mem_ball, dist_eq_norm] at hx
        rw [mem_closedBall, dist_eq_norm]
        calc ‖x - b‖ = ‖(x - (b + r • c)) + r • c‖ := by congr 1; abel
          _ ≤ ‖x - (b + r • c)‖ + ‖r • c‖ := norm_add_le _ _
          _ = ‖x - (b + r • c)‖ + r * ‖c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
          _ ≤ ρ := by rw [← hrK]; linarith
      have hBsub : B ∩ closedBall b ρ ⊆ closedBall b ρ \ ball (b + r • c) (r * δ) := by
        rintro x ⟨hxB, hx⟩
        refine ⟨hx, fun hxW => ?_⟩
        rw [mem_ball, dist_eq_norm] at hxW
        exact (hcon x hxB).not_gt hxW
      have hVfin : volume (closedBall b ρ) ≠ ∞ := measure_closedBall_lt_top.ne
      have hball : volume (ball (b + r • c) (r * δ)) = q * volume (closedBall b ρ) := by
        rw [Measure.addHaar_ball_of_pos volume _ (mul_pos hr hδ),
          Measure.addHaar_closedBall volume _ hρ.le, finrank_euclideanSpace_fin, ← mul_assoc,
          hq_def, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (δ / (‖c‖ + δ)) ^ n), ← mul_pow,
          ← hrK]
        congr 3
        field_simp
      have hle : volume (B ∩ closedBall b ρ) ≤ (1 - q) * volume (closedBall b ρ) := by
        calc volume (B ∩ closedBall b ρ)
            ≤ volume (closedBall b ρ \ ball (b + r • c) (r * δ)) := measure_mono hBsub
          _ = volume (closedBall b ρ) - volume (ball (b + r • c) (r * δ)) :=
            measure_sdiff hsub measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
          _ = (1 - q) * volume (closedBall b ρ) := by
            rw [hball, ENNReal.sub_mul (fun _ _ => hVfin), one_mul]
      have hgt : 1 - q < volume (B ∩ closedBall b ρ) / volume (closedBall b ρ) :=
        hρ₀sub ⟨hρ, hρρ₀⟩
      exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
    -- the estimate at `a`, with `a - b = r c + e`, `‖e‖ < r δ`
    obtain ⟨e, he_def⟩ : ∃ e : Euclid n, e = a - (b + r • c) := ⟨_, rfl⟩
    rw [← he_def] at ha
    have hab : a - b = r • c + e := by rw [he_def]; abel
    have hab_le : ‖a - b‖ ≤ r * ‖c‖ + ‖e‖ := by
      rw [hab]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
    have hab_lt : ‖a - b‖ < r * (‖c‖ + δ) := by rw [mul_add]; linarith
    have hdist : dist a b < ε := by rw [dist_eq_norm]; linarith
    have h1 : m * ‖a - b‖ ≤ ‖F a - F b‖ := hB a haB
    have h2 : ‖F a - F b‖ ≤ ‖L (a - b)‖ + δ * ‖a - b‖ := by
      have h := hεF hdist
      have h' := norm_sub_norm_le (F a - F b) (L (a - b))
      linarith
    have h3 : ‖L (a - b)‖ ≤ r * ‖L c‖ + ‖L‖ * ‖e‖ := by
      rw [hab, map_add, map_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hr.le]
      linarith [L.le_opNorm e]
    have h4 : r * ‖c‖ ≤ ‖a - b‖ + ‖e‖ := by
      have : r • c = (a - b) - e := by rw [hab]; abel
      calc r * ‖c‖ = ‖r • c‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
        _ = ‖(a - b) - e‖ := by rw [this]
        _ ≤ ‖a - b‖ + ‖e‖ := norm_sub_le _ _
    have h5 : ‖L‖ * ‖e‖ ≤ ‖L‖ * (r * δ) := mul_le_mul_of_nonneg_left ha.le (norm_nonneg _)
    have h6 : m * ‖e‖ ≤ m * (r * δ) := mul_le_mul_of_nonneg_left ha.le hm.le
    have h7 : δ * ‖a - b‖ ≤ δ * (r * (‖c‖ + δ)) := mul_le_mul_of_nonneg_left hab_lt.le hδ.le
    have h8 : m * (r * ‖c‖) ≤ m * (‖a - b‖ + ‖e‖) := mul_le_mul_of_nonneg_left h4 hm.le
    have hfin : r * (m * ‖c‖) ≤ r * (‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by
      linarith
    exact le_of_mul_le_mul_left hfin hr
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) (𝓝[>] 0) (𝓝 ‖L c‖) := by
    have hcont : Continuous (fun δ : ℝ => ‖L c‖ + δ * (m + ‖L‖ + ‖c‖ + δ)) := by fun_prop
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
/-- If `F` has derivative `L` at `b` and `f` is continuous with compact support, then
`∫_{B̄_R(0)} |f(r⁻¹(F(b + rc) − F(b))) − f(Lc)| dc → 0` as `r ↓ 0` (the error term `T₃` in the
limit of rescaled integrals over the image of a `C¹` piece; cf. the tangent-plane limit in Simon
Ch. 3, proof of 1.6 "⇒").  With `V = |B̄_R(0)|` and `S = |R| + 1`, take `η` from the uniform
continuity of `f` for `ε / (V + 1)`, then `δ₀` with `‖F(b + k) − F(b) − Lk‖ ≤ (η / 2S)‖k‖` for
`‖k‖ < δ₀`; for `0 < r < δ₀ / S` the integrand is `≤ ε / (V + 1)` on the ball. -/
theorem Submission.pit_ril_diffQuot_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (b : Euclid n) (f : Euclid P → ℝ) (R : ℝ), HasFDerivAt F L b → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro P n F L b f R hF hfc hfs
  -- `D = B̄_R(0)` has finite measure `V`, and `‖c‖ < S = |R| + 1` on `D`
  have hDfin : (volume : Measure (Euclid n)) (closedBall 0 R) < ∞ := measure_closedBall_lt_top
  set V : ℝ := (volume : Measure (Euclid n)).real (closedBall 0 R)
  have hV : 0 ≤ V := measureReal_nonneg
  set S : ℝ := |R| + 1
  have hS : 0 < S := by positivity
  have hcS : ∀ c ∈ closedBall (0 : Euclid n) R, ‖c‖ < S := fun c hc =>
    ((mem_closedBall_zero_iff.1 hc).trans (le_abs_self R)).trans_lt (lt_add_one _)
  -- uniform continuity of `f` and the little-o form of `HasFDerivAt`
  have huc := Metric.uniformContinuous_iff.1 (hfs.uniformContinuous_of_continuous hfc)
  have hlo := hasFDerivAt_iff_isLittleO_nhds_zero.1 hF
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hV1 : 0 < V + 1 := by linarith
  set ε₁ : ℝ := ε / (V + 1) with hε₁_def
  have hε₁ : 0 < ε₁ := div_pos hε hV1
  obtain ⟨η, hη, hηf⟩ := huc ε₁ hε₁
  set θ : ℝ := η / (2 * S) with hθ_def
  have hθ : 0 < θ := div_pos hη (by linarith)
  obtain ⟨δ₀, hδ₀, hδ₀F⟩ := Metric.eventually_nhds_iff.1 (hlo.bound hθ)
  refine ⟨δ₀ / S, div_pos hδ₀ hS, fun r hr hrδ => ?_⟩
  rw [mem_Ioi] at hr
  rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hrδ
  have hrS : r * S < δ₀ := (lt_div_iff₀ hS).1 hrδ
  -- pointwise bound on the integrand
  have hpt : ∀ c ∈ closedBall (0 : Euclid n) R,
      ‖‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖ ≤ ε₁ := by
    intro c hc
    have hc' := hcS c hc
    have hnorm : ‖r • c‖ = r * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hrc : dist (r • c) 0 < δ₀ := by
      rw [dist_zero_right, hnorm]
      calc r * ‖c‖ ≤ r * S := mul_le_mul_of_nonneg_left hc'.le hr.le
        _ < δ₀ := hrS
    have hbound := hδ₀F hrc
    have heq : r⁻¹ • (F (b + r • c) - F b) - L c
        = r⁻¹ • (F (b + r • c) - F b - L (r • c)) := by
      rw [map_smul, smul_sub _ (F (b + r • c) - F b), inv_smul_smul₀ hr.ne']
    have hclose : dist (r⁻¹ • (F (b + r • c) - F b)) (L c) < η := by
      rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
      calc r⁻¹ * ‖F (b + r • c) - F b - L (r • c)‖
          ≤ r⁻¹ * (θ * ‖r • c‖) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr.le)
        _ = θ * ‖c‖ := by rw [hnorm]; field_simp
        _ ≤ θ * S := mul_le_mul_of_nonneg_left hc'.le hθ.le
        _ = η / 2 := by rw [hθ_def]; field_simp
        _ < η := half_lt_self hη
    have := hηf hclose
    rw [Real.dist_eq] at this
    rw [norm_norm, Real.norm_eq_abs]
    exact this.le
  -- integral bound
  have hint := norm_setIntegral_le_of_norm_le_const hDfin hpt
  rw [dist_zero_right]
  calc ‖∫ c in closedBall (0 : Euclid n) R, ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖‖
      ≤ ε₁ * V := hint
    _ < ε := by
      rw [hε₁_def, div_mul_eq_mul_div, div_lt_iff₀ hV1]
      nlinarith
/-- At a point `b` of Lebesgue density one of the Borel set `B` (`λ(B ∩ B̄_ρ(b))/λ(B̄_ρ(b)) → 1`
as `ρ ↓ 0`, the quotient taken in `[0, ∞]`), the averages `⨍_{B̄_s(b)} 1_{ℝⁿ∖B} dλ` tend to `0`
as `s ↓ 0`.  For `s > 0`, `0 < λ(B̄_s(b)) < ∞` and, by additivity, the average equals
`1 − (λ(B ∩ B̄_s(b))/λ(B̄_s(b))).toReal`; `toReal` is continuous at `1`. -/
theorem Submission.pit_ril_compl_average_tendsto : ∀ (n : ℕ) (B : Set (Euclid n)) (b : Euclid n), MeasurableSet B → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, Bᶜ.indicator (fun _ => (1 : ℝ)) a ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n B b hB hlim
  -- `q(ρ).toReal → 1` (`toReal` is continuous at `1 ≠ ∞`), so `1 - q(ρ).toReal → 0`
  have h1 : Tendsto (fun ρ : ℝ =>
      1 - (volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub
      ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim)
    rwa [ENNReal.toReal_one, sub_self] at h
  refine h1.congr' ?_
  -- for `s > 0`, `0 < λ(C_s) < ∞` and the average equals `1 - q(s).toReal`
  filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
  have hfin : volume (closedBall b s) ≠ ∞ := measure_closedBall_lt_top.ne
  have hC : volume.real (closedBall b s) ≠ 0 :=
    (ENNReal.toReal_pos (measure_closedBall_pos volume b hs).ne' hfin).ne'
  -- `λ_ℝ(C_s ∩ B) + λ_ℝ(C_s \ B) = λ_ℝ(C_s)`
  have hsplit := measureReal_inter_add_sdiff (μ := volume) (s := closedBall b s) hB hfin
  rw [setAverage_eq, setIntegral_indicator hB.compl, setIntegral_const, smul_eq_mul, smul_eq_mul,
    mul_one, ENNReal.toReal_div, ← measureReal_def, ← measureReal_def, inter_comm B,
    ← Set.sdiff_eq, ← hsplit]
  rw [← hsplit] at hC
  field_simp
  ring
/-- Localised three-term estimate for the rescaled area integrals (one fixed `r > 0`).  With
`Φ_r(c) = r⁻¹(F(b + rc) − F(b))` and `D = B̄_{R/m}(0)`, the integrands
`X(c) = 1_B(b + rc) J(b + rc) f(Φ_r(c))` and `Y(c) = J(b) f(Lc)` vanish off `D` (by the lower
bounds for `F` on `B` and for `L`, as `f = 0` off the open `R`-ball), and pointwise
`|X − Y| ≤ KM·1_{Bᶜ}(b + rc) + M|J(b + rc) − J(b)| + J(b)|f(Φ_r(c)) − f(Lc)|`, by cases on
`b + rc ∈ B`; all are bounded Borel functions, so integrate over `D`. -/
theorem Submission.pit_ril_three_term_bound : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (L : Euclid n →L[ℝ] Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ) (R M r : ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → (∀ c, m * ‖c‖ ≤ ‖L c‖) → Continuous f → (∀ w, R ≤ ‖w‖ → f w = 0) → (∀ w, ‖f w‖ ≤ M) → 0 < r → ‖(∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) - J b * (∫ c, f (L c) ∂volume)‖ ≤ K * M * (∫ c in closedBall (0 : Euclid n) (R / m), Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) ∂volume) + M * (∫ c in closedBall (0 : Euclid n) (R / m), ‖J (b + r • c) - J b‖ ∂volume) + J b * (∫ c in closedBall (0 : Euclid n) (R / m), ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ ∂volume) := by
  intro P n F L B J K m b f R M r hF hB hJ hJK hm hFB hL hf hfR hfM hr
  -- constants: `0 ≤ M`, `0 ≤ J b ≤ K`, `0 ≤ K`, and `λ(D) < ∞` for `D = B̄_{R/m}(0)`
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hfM 0)
  have hJb0 : 0 ≤ J b := (hJK b).1
  have hJbK : J b ≤ K := (hJK b).2
  have hK0 : 0 ≤ K := hJb0.trans hJbK
  have hDfin : volume (closedBall (0 : Euclid n) (R / m)) ≠ ∞ := measure_closedBall_lt_top.ne
  -- measurability of the integrands
  have hshift : Continuous fun c : Euclid n => b + r • c :=
    continuous_const.add (continuous_id.const_smul r)
  have hΦ : Continuous fun c : Euclid n => f (r⁻¹ • (F (b + r • c) - F b)) :=
    hf.comp (((hF.comp hshift).sub continuous_const).const_smul r⁻¹)
  have hfL : Continuous fun c : Euclid n => f (L c) := hf.comp L.continuous
  have hIJ : Measurable fun c : Euclid n => B.indicator J (b + r • c) :=
    (hJ.indicator hB).comp hshift.measurable
  have hg₁ : Measurable fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) :=
    (measurable_const.indicator hB.compl).comp hshift.measurable
  have hg₂ : Measurable fun c : Euclid n => ‖J (b + r • c) - J b‖ :=
    ((hJ.comp hshift.measurable).sub measurable_const).norm
  have hg₃ : Continuous fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
    (hΦ.sub hfL).norm
  -- bounded measurable functions are integrable on `D`
  have hIJb : ∀ c : Euclid n, ‖B.indicator J (b + r • c)‖ ≤ K := by
    intro c
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Real.norm_of_nonneg (hJK _).1]
      exact (hJK _).2
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact hK0
  have hXint : IntegrableOn
      (fun c : Euclid n => B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (hIJ.mul hΦ.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul]
    exact mul_le_mul (hIJb c) (hfM _) (norm_nonneg _) hK0
  have hYint : IntegrableOn (fun c : Euclid n => J b * f (L c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K * M) hDfin
      (measurable_const.mul hfL.measurable).aestronglyMeasurable (Eventually.of_forall fun c => ?_)
    rw [norm_mul, Real.norm_of_nonneg hJb0]
    exact mul_le_mul hJbK (hfM _) (norm_nonneg _) hK0
  have hg₁int : IntegrableOn (fun c : Euclid n => Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c))
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := 1) hDfin hg₁.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    by_cases h : b + r • c ∈ Bᶜ
    · rw [Set.indicator_of_mem h, norm_one]
    · rw [Set.indicator_of_notMem h, norm_zero]
      exact zero_le_one
  have hg₂int : IntegrableOn (fun c : Euclid n => ‖J (b + r • c) - J b‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := K) hDfin hg₂.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm, Real.norm_eq_abs, abs_sub_le_iff]
    constructor <;> linarith [hJK (b + r • c), hJK b]
  have hg₃int : IntegrableOn
      (fun c : Euclid n => ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume := by
    refine Measure.integrableOn_of_bounded (M := M + M) hDfin hg₃.aestronglyMeasurable
      (Eventually.of_forall fun c => ?_)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hfM _) (hfM _))
  -- localisation: both integrands vanish off `D`
  have hloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → R < m * ‖c‖ := by
    intro c hc
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hc
    rwa [mul_comm] at hc
  have hXloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) →
      B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) = 0 := by
    intro c hc
    by_cases h : b + r • c ∈ B
    · have h1 := hFB _ h
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h2 : R ≤ ‖r⁻¹ • (F (b + r • c) - F b)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc R ≤ m * ‖c‖ := (hloc c hc).le
          _ = r⁻¹ * (m * (r * ‖c‖)) := by rw [mul_left_comm m r, inv_mul_cancel_left₀ hr.ne']
          _ ≤ r⁻¹ * ‖F (b + r • c) - F b‖ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hr.le)
      rw [hfR _ h2, mul_zero]
    · rw [Set.indicator_of_notMem h, zero_mul]
  have hYloc : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) (R / m) → J b * f (L c) = 0 := by
    intro c hc
    rw [hfR _ ((hloc c hc).le.trans (hL c)), mul_zero]
  -- pointwise three-term estimate, by cases on `b + r • c ∈ B`
  have hpt : ∀ c : Euclid n,
      ‖B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖ ≤
        K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) + M * ‖J (b + r • c) - J b‖ +
          J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
    intro c
    have hu := hfM (r⁻¹ • (F (b + r • c) - F b))
    have hv := hfM (L c)
    have hA : 0 ≤ M * ‖J (b + r • c) - J b‖ := mul_nonneg hM0 (norm_nonneg _)
    have hB' : 0 ≤ J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ :=
      mul_nonneg hJb0 (norm_nonneg _)
    by_cases h : b + r • c ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h), mul_zero,
        zero_add]
      have hJu := mul_le_mul_of_nonneg_left hu (norm_nonneg (J (b + r • c) - J b))
      calc ‖J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (L c)‖
          = ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b)) +
              J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := by
            congr 1
            ring
        _ ≤ ‖(J (b + r • c) - J b) * f (r⁻¹ • (F (b + r • c) - F b))‖ +
              ‖J b * (f (r⁻¹ • (F (b + r • c) - F b)) - f (L c))‖ := norm_add_le _ _
        _ = ‖J (b + r • c) - J b‖ * ‖f (r⁻¹ • (F (b + r • c) - F b))‖ +
              J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            rw [norm_mul, norm_mul, Real.norm_of_nonneg hJb0]
        _ ≤ M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖ := by
            linarith [mul_comm M ‖J (b + r • c) - J b‖]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_mul, zero_sub,
        norm_neg, norm_mul, Real.norm_of_nonneg hJb0, mul_one]
      have hJv : J b * ‖f (L c)‖ ≤ K * M := mul_le_mul hJbK hv (norm_nonneg _) hK0
      linarith
  -- integrate the pointwise estimate over `D`
  have h1 : (∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m),
        B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hXloc).symm
  have h2 : J b * (∫ c, f (L c) ∂volume) =
      ∫ c in closedBall (0 : Euclid n) (R / m), J b * f (L c) ∂volume := by
    rw [← integral_const_mul]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hYloc).symm
  have hG₁₂ : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖) (closedBall (0 : Euclid n) (R / m)) volume :=
    (hg₁int.const_mul _).add (hg₂int.const_mul _)
  have hG : IntegrableOn (fun c : Euclid n => K * M * Bᶜ.indicator (fun _ => (1 : ℝ)) (b + r • c) +
      M * ‖J (b + r • c) - J b‖ + J b * ‖f (r⁻¹ • (F (b + r • c) - F b)) - f (L c)‖)
      (closedBall (0 : Euclid n) (R / m)) volume :=
    hG₁₂.add (hg₃int.const_mul _)
  rw [h1, h2, ← integral_sub hXint hYint]
  refine (norm_integral_le_of_norm_le hG (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_add hG₁₂ (hg₃int.const_mul _), integral_add (hg₁int.const_mul _) (hg₂int.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul]
/-- **Rescaled integrals at a point of vanishing ball averages**: for `R > 0`, if
`⨍_{B̄_s(b)} h → 0` as `s → 0⁺`, then `∫_{B̄_R(0)} h(b + rc) dc → 0` as `r → 0⁺`.
For `r > 0`, dilation by `r` and translation by `b` give
`∫_{B̄_R(0)} h(b + rc) dc = r⁻ⁿ ∫_{B̄_{rR}(b)} h = ω Rⁿ ⨍_{B̄_{rR}(b)} h`, `ω = λ(B̄₁(0))`. -/
theorem Submission.pit_integral_closedBall_rescale_tendsto : ∀ (n : ℕ) (h : Euclid n → ℝ) (b : Euclid n) (R : ℝ), 0 < R → Tendsto (fun s : ℝ => ⨍ a in closedBall b s, h a ∂volume) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume) (𝓝[>] 0) (𝓝 0) := by
  intro n h b R hR hlim
  -- `ω = λ(B̄₁(0)) ∈ (0, ∞)` and `λ(B̄_s(z)) = sⁿ ω` for `s ≥ 0`
  set ω : ℝ := volume.real (closedBall (0 : Euclid n) 1) with hω_def
  have hω : 0 < ω := by
    rw [hω_def, measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  have hvol : ∀ (z : Euclid n) {s : ℝ}, 0 ≤ s → volume.real (closedBall z s) = s ^ n * ω := by
    intro z s hs
    rw [Measure.addHaar_real_closedBall' volume z hs, finrank_euclideanSpace_fin]
  -- for `r > 0`: `∫_{B̄_R(0)} h(b + rc) dc = Rⁿ ω ⨍_{B̄_{rR}(b)} h`
  have key : ∀ r : ℝ, 0 < r → ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
      R ^ n * ω * ⨍ a in closedBall b (r * R), h a ∂volume := by
    intro r hr
    set H : Euclid n → ℝ := (closedBall b (r * R)).indicator h with hH
    have hmem : ∀ c : Euclid n, b + r • c ∈ closedBall b (r * R) ↔ c ∈ closedBall (0 : Euclid n) R := by
      intro c
      rw [mem_closedBall, mem_closedBall, dist_self_add_left, dist_zero_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, mul_le_mul_iff_of_pos_left hr]
    -- `1_{B̄_R(0)}(c) h(b + rc) = H(b + rc)`
    have h1 : ∫ c in closedBall (0 : Euclid n) R, h (b + r • c) ∂volume =
        ∫ c, H (b + r • c) ∂volume := by
      rw [← integral_indicator measurableSet_closedBall]
      congr 1
      ext c
      by_cases hc : c ∈ closedBall (0 : Euclid n) R
      · rw [indicator_of_mem hc, hH, indicator_of_mem ((hmem c).2 hc)]
      · rw [indicator_of_notMem hc, hH, indicator_of_notMem (mt (hmem c).1 hc)]
    -- dilation by `r` and translation by `b`
    have h2 : ∫ c, H (b + r • c) ∂volume = (r ^ n)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [Measure.integral_comp_smul volume (fun x => H (b + x)) r, integral_add_left_eq_self H b,
        hH, integral_indicator measurableSet_closedBall, finrank_euclideanSpace_fin, smul_eq_mul,
        abs_of_pos (inv_pos.2 (pow_pos hr n))]
    have h3 : ⨍ a in closedBall b (r * R), h a ∂volume =
        ((r * R) ^ n * ω)⁻¹ * ∫ a in closedBall b (r * R), h a ∂volume := by
      rw [setAverage_eq, hvol b (mul_pos hr hR).le, smul_eq_mul]
    rw [h1, h2, h3, mul_pow]
    field_simp
  -- `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR
  have hlim' := (hlim.comp hmap).const_mul (R ^ n * ω)
  rw [mul_zero] at hlim'
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (key r hr).symm

/-- **Rescaled integrals at a density point of `B` and a Lebesgue point of `J`**: let
`m|a − b| ≤ |F(a) − F(b)|` on `B`, `m|c| ≤ |Lc|` for `L = DF(b)`, `0 ≤ J ≤ K`, let `B` have
density `1` at `b` and `⨍_{B̄_ρ(b)} |J − J(b)| → 0`.  Then for `f ∈ C_c(ℝᴾ)`,
`∫ 1_B(b + rc) J(b + rc) f(r⁻¹(F(b + rc) − F(b))) dc → J(b) ∫ f(Lc) dc` as `r → 0⁺`.
With `f = 0` off `B_R(0)` and `|f| ≤ M`, the error is at most `K M T₁ + M T₂ + J(b) T₃`, where
`T₁, T₂, T₃` integrate `1_{Bᶜ}(b + rc)`, `|J(b + rc) − J(b)|` and
`|f(r⁻¹(F(b + rc) − F(b))) − f(Lc)|` over `B̄_{R/m}(0)`; each tends to `0`. -/
theorem Submission.pit_rescaled_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → (∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖) → Tendsto (fun ρ : ℝ => volume (B ∩ closedBall b ρ) / volume (closedBall b ρ)) (𝓝[>] 0) (𝓝 1) → Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) (𝓝[>] 0) (𝓝 (J b * ∫ c, f (fderiv ℝ F b c) ∂volume)) := by
  intro P n F B J K m b f hF hB hJ hJK hm hFB hdiff hL hdens hLeb hf hfc
  -- `f = 0` off `B_R(0)` and `|f| ≤ M`; the integrals live on `B̄_{R/m}(0)`
  obtain ⟨R, hR, hRf⟩ := hfc.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hRm : 0 < R / m := div_pos hR hm
  -- `T₁ → 0`: `B` has density `1` at `b`
  have hT₁ := Submission.pit_integral_closedBall_rescale_tendsto n
    (Bᶜ.indicator fun _ => (1 : ℝ)) b (R / m) hRm
    (Submission.pit_ril_compl_average_tendsto n B b hB hdens)
  -- `T₂ → 0`: `b` is a Lebesgue point of `J`
  have hT₂ := Submission.pit_integral_closedBall_rescale_tendsto n (fun a => ‖J a - J b‖) b
    (R / m) hRm hLeb
  -- `T₃ → 0`: `r⁻¹(F(b + rc) − F(b)) → Lc` uniformly on `B̄_{R/m}(0)`
  have hT₃ := Submission.pit_ril_diffQuot_integral_tendsto P n F (fderiv ℝ F b) b f (R / m)
    hdiff.hasFDerivAt hf hfc
  have hlim := ((hT₁.const_mul (K * M)).add (hT₂.const_mul M)).add (hT₃.const_mul (J b))
  simp only [mul_zero, add_zero] at hlim
  -- squeeze `|I(r) − J(b) ∫ f(Lc) dc| ≤ K M T₁(r) + M T₂(r) + J(b) T₃(r)` for `r > 0`
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact Submission.pit_ril_three_term_bound P n F (fderiv ℝ F b) B J K m b f R M r hF hB hJ hJK
    hm hFB hL hf hRf hM hr
/-- Integral over the range of a linear map with constant Jacobian: if `T : ℝⁿ → ℝᴾ` is linear
and `Hⁿ(T(S)) = j λ(S)` for every `S ⊆ ℝⁿ` (`j ≥ 0`, `λ` Lebesgue measure), then for continuous
`f`, `∫_{T(ℝⁿ)} f dHⁿ = j ∫ f(T(c)) dλ(c)`.  On Borel `A`, `A ∩ T(ℝⁿ) = T(T⁻¹(A))`, so
`Hⁿ⌞T(ℝⁿ) = j T_#λ`. -/
theorem Submission.pit_setIntegral_range_linear : ∀ (P n : ℕ) (T : Euclid n →L[ℝ] Euclid P) (j : ℝ) (f : Euclid P → ℝ), 0 ≤ j → (∀ S : Set (Euclid n), μHE[n] (T '' S) = ENNReal.ofReal j * volume S) → Continuous f → ∫ y in (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = j * ∫ c, f (T c) ∂volume := by
  intro P n T j f hj hT hf
  -- the carrier of the submodule `range T` is the set `T(ℝⁿ)`
  have hrange : (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) = range T := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
  -- `Hⁿ⌞T(ℝⁿ) = ofReal(j) • T_#λ`, checked on Borel sets
  have hmeas : μHE[n].restrict (range T) = ENNReal.ofReal j • volume.map T := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply T.measurable hA,
      ← image_preimage_eq_inter_range, hT, smul_eq_mul]
  -- change of variables, with `(ofReal j).toReal = j` since `j ≥ 0`
  rw [hrange, hmeas, integral_smul_measure,
    integral_map T.measurable.aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hj, smul_eq_mul]
/-- **Simon Ch. 3, 1.4** (approximate tangent spaces of a bi-Lipschitz piece): let `F : ℝⁿ → ℝᴾ`
be `L`-Lipschitz, `B ⊆ ℝⁿ` Borel and `m > 0` with `m|a − a'| ≤ |F a − F a'|` on `B`, and let `F`
be differentiable at every point of `B` with injective derivative.  Then for a.e. `b ∈ B`,
`F(B)` has approximate tangent space `range DF(b)` at `F b`.
With `J := normDet DF` (Borel, `0 ≤ J ≤ Lⁿ`) the injective area formula holds on `B`.  A.e.
`b ∈ B` is a density point of `B` and a Lebesgue point of `J`; there
`∫_{η_{F b,r}(F(B))} f dHⁿ = ∫ 1_B J(b + rc) f(r⁻¹(F(b + rc) − F b)) dc` tends to
`J(b) ∫ f(DF(b)c) dc = ∫_{range DF(b)} f dHⁿ` as `r ↓ 0`. -/
theorem Submission.ptd_piece_image_approxTangent_ae : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n (F '' B) (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F B L m hF hB hm hcolip hreg
  have hfin : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  -- the area Jacobian `J = normDet DF`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid n → ℝ, J = Poincare.SimonGMT.Chapter02.areaJacobianAt F :=
    ⟨_, rfl⟩
  have hJmeas : Measurable J := hJ ▸ Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt F
  have hJnonneg : ∀ a, 0 ≤ J a := hJ ▸ Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg F
  -- `Hⁿ(T(S)) = normDet T · λ(S)` for every linear `T`
  have hlin : ∀ (T : Euclid n →L[ℝ] Euclid P) (S : Set (Euclid n)),
      μHE[n] (T '' S) = ENNReal.ofReal (T : Euclid n →ₗ[ℝ] Euclid P).normDet * volume S := by
    intro T S
    have h := LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume
      (T : Euclid n →ₗ[ℝ] Euclid P) S
    rw [hfin] at h
    simpa using h
  have hJlin : ∀ a (S : Set (Euclid n)),
      μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S := by
    intro a S
    rw [hlin, hJ, Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet]
  -- `J ≤ Lⁿ`: compare `Hⁿ(DF(a)(B̄₁(0)))` with the Lipschitz bound `‖DF(a)‖ ≤ L`
  have hJle : ∀ a, J a ≤ (L : ℝ) ^ n := by
    intro a
    have hTL : ‖fderiv ℝ F a‖₊ ≤ L := by
      have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := a) hF
      exact_mod_cast h
    have hpos : volume (closedBall (0 : Euclid n) 1) ≠ 0 :=
      (measure_closedBall_pos volume (0 : Euclid n) one_pos).ne'
    have hfin' : volume (closedBall (0 : Euclid n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
    have hle : ENNReal.ofReal (J a) * volume (closedBall (0 : Euclid n) 1) ≤
        (L : ℝ≥0∞) ^ n * volume (closedBall (0 : Euclid n) 1) := by
      rw [← hJlin a, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
      calc μHE[n] (fderiv ℝ F a '' closedBall 0 1)
          ≤ (‖fderiv ℝ F a‖₊ : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
              (fderiv ℝ F a).lipschitzWith.lipschitzOnWith
        _ ≤ (L : ℝ≥0∞) ^ n * μHE[n] (closedBall (0 : Euclid n) 1) := by gcongr
    have h2 : ENNReal.ofReal (J a) ≤ (L : ℝ≥0∞) ^ n :=
      (ENNReal.mul_le_mul_iff_left hpos hfin').1 hle
    rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ENNReal.ofReal_pow L.coe_nonneg,
      ENNReal.ofReal_coe_nnreal]
    exact h2
  -- `F` is injective on `B`, so the area formula holds on `B` with weight `J`
  have hinjOn : InjOn F B := by
    intro a ha a' ha' hFa
    have h := hcolip a ha a' ha'
    rw [hFa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hm
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  have harea : ∀ g : Euclid P → ℝ≥0∞,
      ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume := by
    intro g
    have h := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hB hinjOn g
    rw [hfin] at h
    rw [h, hJ]
  -- `J` is bounded and Borel, hence locally integrable
  have hJloc : LocallyIntegrable J volume := by
    rw [locallyIntegrable_iff]
    intro k hk
    refine Measure.integrableOn_of_bounded hk.measure_lt_top.ne hJmeas.aestronglyMeasurable
      (M := (L : ℝ) ^ n) (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hJnonneg a)]
    exact hJle a
  -- a.e. `b ∈ B` is a density point of `B` and a Lebesgue point of `J`
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub (volume : Measure (Euclid n))
    hJloc 1
  filter_upwards [ae_restrict_mem hB, Besicovitch.ae_tendsto_measure_inter_div volume B,
    ae_restrict_of_ae hleb] with b hbB hα hβ
  have hβ' : Tendsto (fun ρ : ℝ => ⨍ a in closedBall b ρ, ‖J a - J b‖ ∂volume) (𝓝[>] 0) (𝓝 0) :=
    hβ (fun _ => b) id tendsto_id (eventually_nhdsWithin_of_forall fun ρ (hρ : 0 < ρ) =>
      mem_closedBall_self (by simpa using hρ.le))
  obtain ⟨hdb, hinj⟩ := hreg b hbB
  have hcolb : ∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖ := fun a ha => hcolip a ha b hbB
  have hγ : ∀ c, m * ‖c‖ ≤ ‖fderiv ℝ F b c‖ :=
    Submission.pit_fderiv_lower_bound_of_density P n F B m b hm hcolb hdb hα
  refine ⟨?_, fun f => ?_⟩
  · rw [LinearMap.finrank_range_of_inj (by simpa using hinj), hfin]
  · rw [Submission.pit_setIntegral_range_linear P n (fderiv ℝ F b) (J b) f (hJnonneg b)
      (hJlin b) f.continuous]
    refine (Submission.pit_rescaled_integral_tendsto P n F B J ((L : ℝ) ^ n) m b f hF.continuous
      hB hJmeas (fun a => ⟨hJnonneg a, hJle a⟩) hm hcolb hdb hγ hα hβ' f.continuous
      f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (Submission.pit_blowUp_image_setIntegral_eq_rescaled P n F B J b r f hF.continuous hB
      hJmeas hJnonneg harea hr f.continuous).symm

/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"**, for a bi-Lipschitz piece: let `U` be open,
`Y ⊆ U` Borel with `Hⁿ(Y ∩ C) < ∞` for compact `C ⊆ U`, `F` Lipschitz, `B` Borel with
`m|a − a'| ≤ |F(a) − F(a')|` on `B`, `DF(a)` injective for `a ∈ B`, and `F(B) ⊆ Y`.  Then for
a.e. `b ∈ B`, `Y` has approximate tangent space `range DF(b)` at `F(b)`.  The image `F(B)` itself
has this tangent space at `F(b)` for a.e. `b`; `Y` and its Borel subset `F(B)` have the same
approximate tangent spaces `Hⁿ`-a.e. on `F(B)`; and `Hⁿ⌞F(B)`-null sets pull back along `F` to
Lebesgue-null subsets of `B`. -/
theorem Submission.dpf_approxTangent_ae_bilipschitz_piece : ∀ (P n : ℕ) (U Y : Set (Euclid P)) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal) (m : ℝ), IsOpen U → MeasurableSet Y → Y ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (Y ∩ C) ≠ ∞) → LipschitzWith L F → MeasurableSet B → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → F '' B ⊆ Y → ∀ᵐ b ∂(volume.restrict B), HasApproximateTangentSpaceAt n Y (F b) (LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n U Y F B L m hU hY hYU hfin hF hB hm hbi hdiff hFBY
  -- Step 0(a)–(b): `F(B)` is Borel; `Hⁿ⌞F(B)`-a.e. properties hold at `F(b)` for a.e. `b ∈ B`
  obtain ⟨hA, hpull⟩ := Submission.ptd_piece_image_measurable_ae_pullback P n F B L m hF hB hm hbi
  -- Steps 1–3 and 6: `Hⁿ`-a.e. on `F(B)`, `Y` and `F(B)` have the same approximate tangent spaces
  have hloc := Submission.ptd_ae_approxTangent_iff_of_subset P n U (F '' B) Y hU hA hY hFBY hYU hfin
  -- Steps 4, 5 and 7: `F(B)` has approximate tangent space `range DF(b)` at `F(b)` for a.e. `b ∈ B`
  filter_upwards [hpull _ hloc,
    Submission.ptd_piece_image_approxTangent_ae P n F B L m hF hB hm hbi hdiff] with b hYA hA'
  exact (hYA _).2 hA'
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable

/-- **Simon Ch. 6, Definition 3.1, from an integer density**: let `N ⊆ U` be Borel and countably
`n`-rectifiable with `Hⁿ(N ∩ K) < ∞` for compact `K ⊆ U`, let `η` orient the approximate tangent
spaces of `N` `Hⁿ`-a.e. on `N`, and let `m` be integer-valued with `∫_{N ∩ K} |m| dHⁿ < ∞` for
compact `K ⊆ U`.  Then `(N', |m|, sign(m) η)`, `N' = N ∩ {m ≠ 0}`, is an `IMRep` in `U` acting by
`ω ↦ ∫_N m ⟨ω, η⟩ dHⁿ`.

Proof sketch:
* `N' ⊆ N` is Borel and countably `n`-rectifiable; `⌊|m|⌋₊ = |m|` is measurable, positive on `N'`
  and locally integrable; `sign(m) η` is strongly measurable.
* By locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2), 1.8(1)), for `Hⁿ`-a.e.
  `x ∈ N'` a tangent space `Q` of `N` at `x` is one of `N'`, and `±η(x)` still orients `Q`.
* Pointwise on `N`, `1_{N'} |m| ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩`, so the two integrals agree. -/
theorem Submission.cmcdt_ims_imrep_of_int_density : ∀ (P n : ℕ) (U N : Set (Euclid P)) (η : Euclid P → MultiVector P n) (m : Euclid P → ℝ), IsOpen U → MeasurableSet N → N ⊆ U → CountablyRectifiable n N → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (N ∩ K) ≠ ∞) → StronglyMeasurable η → Measurable m → (∀ x, ∃ z : ℤ, m x = z) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict N), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R : IMRep U n, ∀ ω : DifferentialForm (Euclid P) n, R.action ω = ∫ x in N, m x * η x (ω x) ∂μHE[n] := by
  intro P n U N η m hU hN hNU hrect hfin hη hm hint hloc hor
  classical
  -- Step 1: the carrier `N' = N ∩ {m ≠ 0}`
  set N' : Set (Euclid P) := N ∩ {x | m x ≠ 0}
  have hN'meas : MeasurableSet N' :=
    hN.inter ((measurableSet_singleton (0 : ℝ)).preimage hm).compl
  have hN'N : N' ⊆ N := inter_subset_left
  -- Steps 2–3: the multiplicity `⌊|m|⌋₊ = |m|` and the orientation `sign(m) η`
  set mult : Euclid P → ℕ := fun x => ⌊|m x|⌋₊ with hmultdef
  set orient : Euclid P → MultiVector P n := fun x => if m x < 0 then -η x else η x with horientdef
  have hmult_cast : ∀ x, ((mult x : ℕ) : ℝ) = |m x| := by
    intro x
    obtain ⟨z, hz⟩ := hint x
    simp only [hmultdef, hz]
    rw [show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs]]
    rw [Nat.floor_natCast]
  have hmult_meas : Measurable mult :=
    (Nat.floor_mono.measurable).comp (continuous_abs.measurable.comp hm)
  have hmult_pos : ∀ x ∈ N', 0 < mult x := by
    intro x hx
    have hx0 : m x ≠ 0 := hx.2
    have h1 : (0 : ℝ) < ((mult x : ℕ) : ℝ) := by
      rw [hmult_cast]; exact abs_pos.mpr hx0
    exact_mod_cast h1
  have horient_sm : StronglyMeasurable orient := by
    have hset : MeasurableSet {x | m x < 0} := measurableSet_lt hm measurable_const
    have hneg : StronglyMeasurable (fun x => -η x) := by
      have := hη.const_smul (-1 : ℝ)
      convert this using 1
      funext x
      exact (neg_one_smul ℝ (η x)).symm
    exact StronglyMeasurable.ite hset hneg hη
  -- Step 4: local integrability, `∫_{N' ∩ K} ⌊|m|⌋₊ ≤ ∫_{N ∩ K} |m| < ∞`
  have hloc' : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (hloc K hK hKU) ?_
    calc ∫⁻ x in N' ∩ K, (mult x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in N ∩ K, (mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left _ hN'N)
      _ ≤ ∫⁻ x in N ∩ K, ‖m x‖ₑ ∂μHE[n] := by
          refine lintegral_mono fun x => ?_
          rw [Real.enorm_eq_ofReal_abs, ← hmult_cast x, ENNReal.ofReal_natCast]
  -- Step 5: tangent spaces of `N` are tangent spaces of `N'` a.e. on `N'`, and `±η` orients them
  have hor' : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n N' x Q ∧ IsUnitOrientationOf (orient x) Q := by
    have h1 := Submission.rsdic_ae_tangent_iff_of_subset P n U N' N hU hN'meas hN hN'N hNU hfin
    have h2 : ∀ᵐ x ∂(μHE[n].restrict N'), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n N x Q ∧ IsUnitOrientationOf (η x) Q :=
      ae_restrict_of_ae_restrict_of_subset hN'N hor
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨Q, hQ1, hQ2⟩ := hx2
    refine ⟨Q, (hx1 Q).1 hQ1, ?_⟩
    simp only [horientdef]
    split_ifs
    · obtain ⟨τ, hτ, hspan, hξ⟩ := hQ2
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hξ with h | h
      · right; intro α; simp [h]
      · left; intro α; simp [h]
    · exact hQ2
  -- Step 6: the `IMRep`
  let R : IMRep U n :=
    { carrier := N'
      mult := mult
      orient := orient
      measurableSet_carrier := hN'meas
      carrier_subset := hN'N.trans hNU
      rectifiable := hrect.mono hN'N
      measurable_mult := hmult_meas
      mult_pos := hmult_pos
      locallyIntegrable_mult := hloc'
      aestronglyMeasurable_orient := horient_sm.aestronglyMeasurable
      orients := hor' }
  refine ⟨R, ?_⟩
  -- Step 7: the action, from `1_{N'} ⌊|m|⌋₊ ⟨ω, sign(m) η⟩ = m ⟨ω, η⟩` pointwise on `N`
  intro ω
  show ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] = ∫ x in N, m x * η x (ω x) ∂μHE[n]
  have hpt : ∀ x ∈ N,
      N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x = m x * η x (ω x) := by
    intro x hx
    by_cases hx0 : m x = 0
    · have : x ∉ N' := fun h => h.2 hx0
      simp [this, hx0]
    · have hxN' : x ∈ N' := ⟨hx, hx0⟩
      rw [indicator_of_mem hxN', hmult_cast]
      simp only [horientdef]
      split_ifs with hneg
      · rw [abs_of_neg hneg]; simp
      · rw [abs_of_nonneg (not_lt.mp hneg)]
  calc ∫ x in N', (mult x : ℝ) * orient x (ω x) ∂μHE[n]
      = ∫ x in N ∩ N', (mult x : ℝ) * orient x (ω x) ∂μHE[n] := by
        rw [inter_eq_right.mpr hN'N]
    _ = ∫ x in N, N'.indicator (fun x => (mult x : ℝ) * orient x (ω x)) x ∂μHE[n] :=
        (setIntegral_indicator hN'meas).symm
    _ = ∫ x in N, m x * η x (ω x) ∂μHE[n] := setIntegral_congr_fun hN hpt
/-- **`C¹` cut-off with a global Lipschitz bound** (step 1(b) of the integer multiplicity
push-forward).  If `f` is `C¹` on an open `O ⊇ K`, `K` compact, then `φ = id + χ (f − id)` is `C¹`
on `ℝᴾ`, globally Lipschitz, and agrees with `f` to first order on `K`; here `χ ∈ [0, 1]` is a
smooth cut-off with `χ = 1` exactly on `cthickening δ K` and `support χ = thickening (2δ) K`, where
`cthickening (3δ) K ⊆ O`.  `Dφ` is continuous and equals `id` off the compact set `spt χ`, so it
is bounded, and the mean value inequality makes `φ` Lipschitz. -/
theorem Submission.dtc_bc_lc_pfi_c1_cutoff_lipschitz : ∀ (P : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → IsCompact K → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (φ : Euclid P → Euclid P) (Λ : NNReal), ContDiff ℝ 1 φ ∧ LipschitzWith Λ φ ∧ ∀ x ∈ K, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x := by
  intro P O K f hO hK hKO hf
  -- Step 1: a margin `cthickening (3δ) K ⊆ O`
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ 3 * δ = ε := ⟨ε / 3, by positivity, by ring⟩
  -- Step 2: the cut-off `χ`, equal to `1` exactly on `cthickening δ K`, with
  -- `support χ = thickening (2δ) K`
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
    (isOpen_thickening (δ := 2 * δ) (E := K)) (isClosed_cthickening (δ := δ) (E := K))
    (cthickening_subset_thickening' (by positivity) (by linarith) K)
  have hχ' : ContDiff ℝ 1 χ := hχ
  have htsupp : tsupport χ ⊆ cthickening (2 * δ) K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  have htO : tsupport χ ⊆ O := htsupp.trans ((cthickening_mono (by linarith) K).trans hεO)
  have htcpt : IsCompact (tsupport χ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) htsupp
  have hχK : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, χ y = 1 := fun x hx =>
    Filter.mem_of_superset (isOpen_thickening.mem_nhds (self_subset_thickening hδ K hx))
      fun y hy => (hχ1 y).1 (thickening_subset_cthickening δ K hy)
  -- Step 3: `φ = id + χ (f − id)`; it is the identity near every point off `spt χ`
  set φ : Euclid P → Euclid P := fun x => x + χ x • (f x - x) with hφdef
  have hφid : ∀ x, x ∉ tsupport χ → φ =ᶠ[𝓝 x] id := by
    intro x hx
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    have hy' : χ y = 0 := hy
    simp [hφdef, hy']
  -- Step 4: `φ` is `C¹`
  have hφ : ContDiff ℝ 1 φ := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · exact contDiffAt_id.add
        (hχ'.contDiffAt.smul ((hf.contDiffAt (hO.mem_nhds hx)).sub contDiffAt_id))
    · exact contDiffAt_id.congr_of_eventuallyEq (hφid x fun h => hx (htO h))
  -- Step 6: `‖Dφ‖ ≤ max 1 C`, so `φ` is Lipschitz
  obtain ⟨C, hC⟩ :=
    htcpt.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨φ, (max 1 C).toNNReal, hφ, ?_, ?_⟩
  · refine lipschitzWith_of_nnnorm_fderiv_le (hφ.differentiable one_ne_zero) fun x => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal _ (zero_le_one.trans (le_max_left _ _))]
    by_cases hx : x ∈ tsupport χ
    · exact (hC x hx).trans (le_max_right _ _)
    · rw [(hφid x hx).fderiv_eq, fderiv_id]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
  -- Step 5: `φ = f` near each point of `K`
  · intro x hx
    have heq : φ =ᶠ[𝓝 x] f := by
      filter_upwards [hχK x hx] with y hy
      simp [hφdef, hy]
    exact ⟨heq.eq_of_nhds, heq.fderiv_eq⟩
/-- **Area change of variables for injective maps.**  Write `J_T = √det(⟨T eₖ, T eₗ⟩)` for linear
`T : ℝⁿ → ℝᴾ`.  (I) For injective `T` the area formula gives `Hⁿ(T(S)) = J_T |S|`; on the unit
ball the Lipschitz bound `Hⁿ(L(X)) ≤ ‖L‖ⁿ Hⁿ(X)` gives `J_{L∘A} ≤ ‖L‖ⁿ J_A`.  (II) Let `F` be
differentiable with injective `DF` at every point of the Borel set `B` and injective on `B`, and
`J(x) = J_{DF(x)}`.  `F(B)` is Borel (Lusin–Souslin).  For Borel `S`, `(invFunOn F B)⁻¹(S)` is
`F(B ∩ S)` together with `F(B)ᶜ` if `S` contains the default value, so `invFunOn F B` is Borel.
A Borel `Hⁿ⌞F(B)`-null `Z` has `∫_B J · 1_Z ∘ F = Hⁿ(Z ∩ F(B)) = 0`, and `J > 0` on `B`, so
`F⁻¹(Z)` is null in `B`.  The area formula for `‖h‖ₑ`, `h⁺` and `h⁻` gives the integrability
criterion and the integral identity; if `h` is not integrable both integrals vanish. -/
theorem Submission.dtc_bc_lc_pfi_area_change_of_variables : ∀ (P n : ℕ), (∀ (A : Euclid n →L[ℝ] Euclid P) (L : Euclid P →L[ℝ] Euclid P), Injective (L.comp A) → Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ ((L.comp A) (EuclideanSpace.single k 1)) ((L.comp A) (EuclideanSpace.single l 1)))) ≤ ‖L‖ ^ n * Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (A (EuclideanSpace.single k 1)) (A (EuclideanSpace.single l 1))))) ∧ ∀ (F : Euclid n → Euclid P) (B : Set (Euclid n)), MeasurableSet B → (∀ x ∈ B, DifferentiableAt ℝ F x ∧ Injective (fderiv ℝ F x)) → InjOn F B → MeasurableSet (F '' B) ∧ Measurable (Function.invFunOn F B) ∧ (∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) → ∀ᵐ x ∂(volume.restrict B), p (F x)) ∧ ∀ h : Euclid P → ℝ, AEStronglyMeasurable h (μHE[n].restrict (F '' B)) → (IntegrableOn h (F '' B) μHE[n] ↔ IntegrableOn (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x)) B) ∧ ∫ y in F '' B, h y ∂μHE[n] = ∫ x in B, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ F x (EuclideanSpace.single k 1)) (fderiv ℝ F x (EuclideanSpace.single l 1)))) * h (F x) := by
  intro P n
  -- `G T = √det(⟨T eₖ, T eₗ⟩)`, the Gram-determinant Jacobian of a linear `T : ℝⁿ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid n →L[ℝ] Euclid P) → ℝ, ∀ T, G T = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin n => inner ℝ (T (EuclideanSpace.single k 1)) (T (EuclideanSpace.single l 1)))) :=
    ⟨_, fun T => rfl⟩
  have harea := Submission.codim1_lura_gram_area_formula n P
  simp only [← hG] at harea ⊢
  have hG0 : ∀ T, 0 ≤ G T := fun T => by rw [hG]; exact Real.sqrt_nonneg _
  -- `J_T > 0` for injective `T` (orient_algebra (c))
  have hGpos : ∀ T : Euclid n →L[ℝ] Euclid P, Injective T → 0 < G T := fun T hT => by
    rw [hG]
    exact ((Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n).2.2.1 T hT).1
  -- linear area identity: `Hⁿ(T(S)) = J_T |S|` for injective `T` and Borel `S`
  have hlin : ∀ T : Euclid n →L[ℝ] Euclid P, Injective T → ∀ S : Set (Euclid n),
      MeasurableSet S → μHE[n] (T '' S) = ENNReal.ofReal (G T) * volume S := by
    intro T hT S hS
    simpa only [ContinuousLinearMap.fderiv, mul_one, setLIntegral_one, setLIntegral_const] using
      (harea T).2 S hS (fun x _ => T.differentiableAt) (fun x _ => by rwa [T.fderiv]) hT.injOn
        fun _ => 1
  refine ⟨fun A L hLA => ?_, fun F B hB hF hinj => ?_⟩
  · -- (I): compare the images of the unit ball under `L ∘ A` and `A`
    have hA : Injective A := fun x y hxy => hLA (by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hxy])
    have hle : μHE[n] ((L.comp A) '' ball 0 1) ≤ (‖L‖₊ : ℝ≥0∞) ^ n * μHE[n] (A '' ball 0 1) := by
      rw [ContinuousLinearMap.coe_comp, image_comp]
      exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        L.lipschitzWith.lipschitzOnWith
    rw [hlin _ hLA _ measurableSet_ball, hlin _ hA _ measurableSet_ball, ← mul_assoc,
      ENNReal.mul_le_mul_iff_left (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
        measure_ball_lt_top.ne] at hle
    refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (pow_nonneg (norm_nonneg L) n) (hG0 A))).1 ?_
    rw [ENNReal.ofReal_mul (pow_nonneg (norm_nonneg L) n), ENNReal.ofReal_pow (norm_nonneg L),
      ofReal_norm, enorm_eq_nnnorm]
    exact hle
  have hcont : ContinuousOn F B := fun x hx => (hF x hx).1.continuousAt.continuousWithinAt
  have hFae : AEMeasurable F (volume.restrict B) := hcont.aemeasurable hB
  have hJ : Measurable fun x => G (fderiv ℝ F x) := (harea F).1
  have hAF := (harea F).2 B hB (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2) hinj
  -- (i) Lusin–Souslin: images of Borel subsets of `B` are Borel
  have himage : ∀ S, MeasurableSet S → S ⊆ B → MeasurableSet (F '' S) :=
    fun S hS hSB => hS.image_of_continuousOn_injOn (hcont.mono hSB) (hinj.mono hSB)
  -- (ii) `(invFunOn F B)⁻¹(S) = F(B ∩ S) ∪ (F(B)ᶜ ∩ {_ | c ∈ S})`, `c` the default value
  have hψ : Measurable (Function.invFunOn F B) := by
    intro S hS
    obtain ⟨c, hc⟩ : ∃ c, ∀ y, y ∉ F '' B → Function.invFunOn F B y = c :=
      ⟨_, fun y hy => Function.invFunOn_neg hy⟩
    have heq : Function.invFunOn F B ⁻¹' S = F '' (B ∩ S) ∪ (F '' B)ᶜ ∩ {_y | c ∈ S} := by
      ext y
      by_cases hy : y ∈ F '' B
      · obtain ⟨x, hx, rfl⟩ := hy
        rw [mem_preimage, hinj.leftInvOn_invFunOn hx]
        constructor
        · exact fun hxS => Or.inl ⟨x, ⟨hx, hxS⟩, rfl⟩
        · rintro (⟨x', ⟨hx', hx'S⟩, hx'x⟩ | ⟨hFx, -⟩)
          · rwa [← hinj hx' hx hx'x]
          · exact absurd (mem_image_of_mem F hx) hFx
      · rw [mem_preimage, hc y hy]
        constructor
        · exact fun hcS => Or.inr ⟨hy, hcS⟩
        · rintro (⟨x', ⟨hx', -⟩, rfl⟩ | ⟨-, hcS⟩)
          · exact absurd (mem_image_of_mem F hx') hy
          · exact hcS
    rw [heq]
    exact (himage _ (hB.inter hS) inter_subset_left).union
      ((himage B hB Subset.rfl).compl.inter (MeasurableSet.const _))
  -- (iii) `Hⁿ⌞F(B)`-null sets pull back to null subsets of `B`, since `J > 0` on `B`
  have hnull : ∀ p : Euclid P → Prop, (∀ᵐ y ∂(μHE[n].restrict (F '' B)), p y) →
      ∀ᵐ x ∂(volume.restrict B), p (F x) := by
    intro p hp
    obtain ⟨Z, hpZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hp)
    have h0 : ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ F x)) * Z.indicator 1 (F x) = 0 := by
      rw [← hAF (Z.indicator 1), lintegral_indicator_one hZ, hZ0]
    have h1 := (lintegral_eq_zero_iff' (hJ.ennreal_ofReal.aemeasurable.mul
      ((measurable_one.indicator hZ).comp_aemeasurable hFae))).1 h0
    filter_upwards [h1, ae_restrict_mem hB] with x hx hxB
    by_contra hpx
    have hZx : Z.indicator (1 : Euclid P → ℝ≥0∞) (F x) = 1 := indicator_of_mem (hpZ hpx) _
    simp only [Pi.mul_apply, Pi.zero_apply, comp_apply, hZx, mul_one, ENNReal.ofReal_eq_zero] at hx
    exact absurd hx (not_le.2 (hGpos _ (hF x hxB).2))
  refine ⟨himage B hB Subset.rfl, hψ, hnull, fun h hh => ?_⟩
  -- `x ↦ J(x) h(F(x))` is a.e. strongly measurable on `B`: replace `h` by a Borel version
  have hmeas : AEStronglyMeasurable (fun x => G (fderiv ℝ F x) * h (F x)) (volume.restrict B) := by
    refine (hJ.aemeasurable.mul (hh.stronglyMeasurable_mk.measurable.comp_aemeasurable
      hFae)).aestronglyMeasurable.congr ?_
    filter_upwards [hnull (fun y => hh.mk h y = h y) hh.ae_eq_mk.symm] with x hx
    simp only [Pi.mul_apply, comp_apply, hx]
  -- `∫⁻_{F(B)} ‖h‖ₑ dHⁿ = ∫⁻_B ‖J · h ∘ F‖ₑ`
  have hnorm : ∫⁻ y in F '' B, ‖h y‖ₑ ∂μHE[n] = ∫⁻ x in B, ‖G (fderiv ℝ F x) * h (F x)‖ₑ := by
    rw [hAF]
    refine lintegral_congr fun x => ?_
    rw [enorm_mul, Real.enorm_of_nonneg (hG0 _)]
  have hint : IntegrableOn h (F '' B) μHE[n] ↔
      IntegrableOn (fun x => G (fderiv ℝ F x) * h (F x)) B := by
    refine ⟨fun hi => ⟨hmeas, ?_⟩, fun hi => ⟨hh, ?_⟩⟩
    · rw [hasFiniteIntegral_iff_enorm, ← hnorm]
      exact hi.2
    · rw [hasFiniteIntegral_iff_enorm, hnorm]
      exact hi.2
  refine ⟨hint, ?_⟩
  by_cases hi : IntegrableOn h (F '' B) μHE[n]
  · -- area formula for `h⁺` and `h⁻`
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi.integrable,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint.1 hi).integrable, hAF, hAF]
    have e1 : ∀ x, ENNReal.ofReal (G (fderiv ℝ F x)) * ENNReal.ofReal (h (F x)) =
        ENNReal.ofReal (G (fderiv ℝ F x) * h (F x)) := fun x =>
      (ENNReal.ofReal_mul (hG0 _)).symm
    have e2 : ∀ x, ENNReal.ofReal (G (fderiv ℝ F x)) * ENNReal.ofReal (-h (F x)) =
        ENNReal.ofReal (-(G (fderiv ℝ F x) * h (F x))) := fun x => by
      rw [← ENNReal.ofReal_mul (hG0 _), mul_neg]
    simp only [e1, e2]
  · rw [integral_undef hi, integral_undef fun h' => hi (hint.2 h')]

/-- **Simon Ch. 3, Lemma 1.2, refined for the push-forward of Ch. 6, 3.4–3.6**: for a
differentiable `φ : ℝᴾ → ℝᴾ`, a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null
set, the disjoint union of Borel pieces `Gⱼ(Aⱼ) ⊆ M` as in `dpf_rectifiable_bilipschitz_pieces`
such that on each piece either `φ ∘ Gⱼ` is bi-Lipschitz with injective derivative (Simon's `M₊`,
where `J^M φ > 0`) or `D(φ ∘ Gⱼ)` is nowhere injective (where `J^M φ = 0`, 3.4).  Each piece
`Fᵢ(Bᵢ)` of `dpf_rectifiable_bilipschitz_pieces` is split into the Borel critical set
`{a ∈ Bᵢ : D(φ ∘ Fᵢ)(a) not injective}` and Mathlib's partition of the rest into sets on which
`φ ∘ Fᵢ` is close to an injective linear map, hence bi-Lipschitz. -/
theorem Submission.dtc_bc_lc_pfi_refined_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)) (φ : Euclid P → Euclid P), MeasurableSet M → CountablyRectifiable n M → Differentiable ℝ φ → ∃ (G : ℕ → Euclid n → Euclid P) (A : ℕ → Set (Euclid n)) (κ : ℕ → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (G j)) ∧ (∀ j, MeasurableSet (A j)) ∧ (∀ j, 0 < κ j) ∧ (∀ j, ∀ a ∈ A j, ∀ a' ∈ A j, κ j * ‖a - a'‖ ≤ ‖G j a - G j a'‖) ∧ (∀ j, ∀ a ∈ A j, DifferentiableAt ℝ (G j) a ∧ Injective (fderiv ℝ (G j) a)) ∧ (∀ j, MeasurableSet (G j '' A j)) ∧ (∀ j, G j '' A j ⊆ M) ∧ Pairwise (fun i j => Disjoint (G i '' A i) (G j '' A j)) ∧ μHE[n] (M \ ⋃ j, G j '' A j) = 0 ∧ ∀ j, ((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ A j, ∀ a' ∈ A j, κ' * ‖a - a'‖ ≤ ‖φ (G j a) - φ (G j a')‖) ∧ ∀ a ∈ A j, Injective (fderiv ℝ (φ ∘ G j) a)) ∨ ∀ a ∈ A j, ¬ Injective (fderiv ℝ (φ ∘ G j) a) := by
  intro P n M φ hM hrect hφ
  -- Step 1: the bi-Lipschitz parametrization `Fᵢ(Bᵢ)` of `M`
  obtain ⟨F, B, m, hFL, hBmeas, hmpos, hmlow, hFdiff, -, hFBM, hFBdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P n M hM hrect
  have hFcont : ∀ i, Continuous (F i) := fun i => by
    obtain ⟨L, hL⟩ := hFL i
    exact hL.continuous
  have hinjB : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have := hmlow i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmpos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Steps 2 and 4: split `Bᵢ` into the critical set `Cᵢ = {D(φ ∘ Fᵢ) not injective}` and the
  -- pieces `Bᵢ⁺ ∩ tᵢₗ` of `Bᵢ⁺ = Bᵢ ∖ Cᵢ` on which `φ ∘ Fᵢ` is bi-Lipschitz
  have hsplit : ∀ i, ∃ D : ℕ → Set (Euclid n), (∀ k, D k ⊆ B i) ∧ (∀ k, MeasurableSet (D k)) ∧
      Pairwise (Disjoint on D) ∧ B i ⊆ ⋃ k, D k ∧
      ∀ k, ((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ D k, ∀ a' ∈ D k,
          κ' * ‖a - a'‖ ≤ ‖φ (F i a) - φ (F i a')‖) ∧
        ∀ a ∈ D k, Injective (fderiv ℝ (φ ∘ F i) a)) ∨
        ∀ a ∈ D k, ¬ Injective (fderiv ℝ (φ ∘ F i) a) := by
    intro i
    set S := {a | Injective (fderiv ℝ (φ ∘ F i) a)} with hS
    have hSmeas : MeasurableSet S :=
      measurable_fderiv ℝ (φ ∘ F i) ContinuousLinearMap.isOpen_injective.measurableSet
    obtain ⟨t, T, htdisj, htmeas, hRt, hTapprox, hTy⟩ :=
      exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (φ ∘ F i) (B i ∩ S)
        (fderiv ℝ (φ ∘ F i))
        (fun x hx => ((hφ (F i x)).comp x (hFdiff i x hx.1).1).hasFDerivAt.hasFDerivWithinAt)
        (fun T => c T / 2) (fun T => (div_pos (hcpos T) two_pos).ne')
    refine ⟨fun k => if k = 0 then B i ∩ Sᶜ else B i ∩ S ∩ t (k - 1), ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      dsimp only
      split_ifs
      · exact inter_subset_left
      · exact inter_subset_left.trans inter_subset_left
    · intro k
      dsimp only
      split_ifs
      · exact (hBmeas i).inter hSmeas.compl
      · exact ((hBmeas i).inter hSmeas).inter (htmeas _)
    · intro k k' hkk'
      dsimp only [Function.onFun]
      split_ifs with hk hk'
      · exact absurd (hk.trans hk'.symm) hkk'
      · exact disjoint_left.mpr fun a ha ha' => ha.2 ha'.1.2
      · exact disjoint_left.mpr fun a ha ha' => ha'.2 ha.1.2
      · exact (htdisj fun h => hkk' (by omega)).mono inter_subset_right inter_subset_right
    · intro a ha
      by_cases haS : a ∈ S
      · obtain ⟨l, hl⟩ := mem_iUnion.mp (hRt ⟨ha, haS⟩)
        refine mem_iUnion.mpr ⟨l + 1, ?_⟩
        simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        exact ⟨⟨ha, haS⟩, hl⟩
      · refine mem_iUnion.mpr ⟨0, ?_⟩
        simp only [↓reduceIte]
        exact ⟨ha, haS⟩
    · intro k
      dsimp only
      split_ifs with hk
      · exact Or.inr fun a ha => ha.2
      · refine Or.inl ⟨⟨((c (T (k - 1)) / 2 : NNReal) : ℝ),
          NNReal.coe_pos.mpr (div_pos (hcpos _) two_pos), ?_⟩, fun a ha => ha.1.2⟩
        intro a ha a' ha'
        obtain ⟨y, hy, hTk⟩ := hTy ⟨a, ha.1⟩ (k - 1)
        have hinj : Injective (T (k - 1)) := by
          rw [hTk]
          exact hy.2
        have h1 := hc (T (k - 1)) hinj (a - a')
        have h2 := hTapprox (k - 1) a ha a' ha'
        have h3 := norm_sub_norm_le (T (k - 1) (a - a')) (φ (F i a) - φ (F i a'))
        rw [norm_sub_rev (T (k - 1) (a - a'))] at h3
        simp only [comp_apply] at h2
        push_cast at h2 ⊢
        linarith
  choose D hDB hDmeas hDdisj hBD hDdich using hsplit
  -- Step 5: enumerate the pieces `(i, k) ↦ Fᵢ(Dᵢₖ)` by `j ↦ unpair j`
  refine ⟨fun j => F (Nat.unpair j).1, fun j => D (Nat.unpair j).1 (Nat.unpair j).2,
    fun j => m (Nat.unpair j).1, fun j => hFL _, fun j => hDmeas _ _, fun j => hmpos _,
    fun j a ha a' ha' => hmlow _ a (hDB _ _ ha) a' (hDB _ _ ha'),
    fun j a ha => hFdiff _ a (hDB _ _ ha), fun j => ?_, fun j => ?_, ?_, ?_,
    fun j => hDdich _ _⟩
  -- Step 6: the images are Borel (Lusin–Souslin) and lie in `M`
  · exact (hDmeas _ _).image_of_continuousOn_injOn (hFcont _).continuousOn
      ((hinjB _).mono (hDB _ _))
  · exact (image_mono (hDB _ _)).trans (hFBM _)
  -- Step 7: disjointness
  · intro j j' hjj'
    dsimp only
    rcases eq_or_ne (Nat.unpair j).1 (Nat.unpair j').1 with hi | hi
    · have hk : (Nat.unpair j).2 ≠ (Nat.unpair j').2 := fun hk => hjj' (by
        rw [← Nat.pair_unpair j, ← Nat.pair_unpair j', hi, hk])
      rw [hi]
      rw [disjoint_left]
      rintro _ ⟨a, ha, rfl⟩ ⟨a', ha', heq⟩
      have := hinjB _ (hDB _ _ ha') (hDB _ _ ha) heq
      subst this
      exact disjoint_left.mp (hDdisj _ hk) ha ha'
    · exact (hFBdisj hi).mono (image_mono (hDB _ _)) (image_mono (hDB _ _))
  -- Step 8: the remainder is the null remainder of the parametrization
  · refine measure_mono_null (sdiff_subset_sdiff_right ?_) hnull
    refine iUnion_subset fun i => ?_
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hBD i ha)
    refine mem_iUnion.mpr ⟨Nat.pair i k, a, ?_, ?_⟩
    · simp only [Nat.unpair_pair]
      exact hk
    · simp only [Nat.unpair_pair]
/-- **Simon Ch. 6, (3.4)–(3.5)** (orientation along a bi-Lipschitz piece): let `R = (M, θ, ξ)` be
an integer multiplicity triple in the open set `U`, `G : ℝⁿ → ℝᴾ` `L`-Lipschitz, `A ⊆ ℝⁿ` Borel
and `κ > 0` with `κ|a − a'| ≤ |G a − G a'|` on `A`, `G` differentiable with injective derivative
at every point of `A`, and `G(A) ⊆ M`.  Then for a.e. `a ∈ A` there is `σ = ±1` with
`J_G(a) ⟨β, ξ(G a)⟩ = σ β(DG(a)e₁, …, DG(a)eₙ)` for every `n`-covector `β`, where
`J_G(a) = (det[DG(a)eₖ · DG(a)eₗ])^{1/2}`.
`M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` is locally integrable, so `M` has approximate
tangent space `range DG(a)` at `G a` for a.e. `a ∈ A`; the `Hⁿ`-a.e. orientation condition of `R`
pulls back along `G` to a.e. `a ∈ A`; uniqueness of approximate tangent spaces identifies the
oriented plane with `range DG(a)`, which `J_G(a)⁻¹ DG(a)_# e` orients, so
`ξ(G a) = ±J_G(a)⁻¹ DG(a)_# e`. -/
theorem Submission.dtc_bc_lc_pfi_piece_orientation_sign : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (κ : ℝ), IsOpen U → LipschitzWith L G → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∀ᵐ a ∂(volume.restrict A), ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ β : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ G a (EuclideanSpace.single k 1)) (fderiv ℝ G a (EuclideanSpace.single l 1)))) * R.orient (G a) β = σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1)) := by
  intro P n U R G A L κ hU hG hA hκ hbi hdiff hGA
  -- Step 1: `Hⁿ(M ∩ C) ≤ ∫_{M ∩ C} θ dHⁿ < ∞` for compact `C ⊆ U`, as `θ ≥ 1` on `M`
  have hfin : ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (R.carrier ∩ C) ≠ ∞ := by
    intro C hC hCU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult C hC hCU) ?_
    calc μHE[n] (R.carrier ∩ C) = ∫⁻ _ in R.carrier ∩ C, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hC.isClosed.measurableSet)
          fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1)
  -- Step 2: `M` has approximate tangent space `range DG(a)` at `G a` for a.e. `a ∈ A`
  have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n U R.carrier G A L κ hU
    R.measurableSet_carrier R.carrier_subset hfin hG hA hκ hbi hdiff hGA
  -- Step 3: `G` is injective on `A`, so the `Hⁿ`-a.e. orientation condition of `R`, which holds
  -- `Hⁿ`-a.e. on `G(A) ⊆ M`, pulls back along `G` to a.e. `a ∈ A`
  have hinj : InjOn G A := by
    intro a ha a' ha' hGa
    have h := hbi a ha a' ha'
    rw [hGa, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := le_of_mul_le_mul_left (by simpa using h) hκ
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h')
  obtain ⟨-, -, hpull, -⟩ :=
    (Submission.dtc_bc_lc_pfi_area_change_of_variables P n).2 G A hA hdiff hinj
  have horient := hpull _ (ae_restrict_of_ae_restrict_of_subset hGA R.orients)
  obtain ⟨hsign, -, hunit, -⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  filter_upwards [htan, horient, ae_restrict_mem hA] with a hta hor ha
  -- Step 4: by uniqueness of approximate tangent spaces, `ξ(G a)` orients `range DG(a)`
  obtain ⟨Q, hQ, hξ⟩ := hor
  rw [hQ.unique hta] at hξ
  -- Step 5: `J_G(a) > 0` and `ζ := J_G(a)⁻¹ DG(a)_# e` also orients `range DG(a)`, so
  -- `ξ(G a) = ±ζ`, whence `J_G(a) ξ(G a)(β) = ±β(DG(a)e)`
  obtain ⟨hJ, hζ⟩ := hunit (fderiv ℝ G a) (hdiff a ha).2
  rcases hsign _ _ _ hζ hξ with h | h
  · refine ⟨1, Or.inl rfl, fun β => ?_⟩
    rw [h, smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul,
      mul_inv_cancel_left₀ hJ.ne', one_mul]
  · refine ⟨-1, Or.inr rfl, fun β => ?_⟩
    rw [h, neg_apply, smul_apply, ContinuousAlternatingMap.apply_apply, smul_eq_mul, mul_neg,
      mul_inv_cancel_left₀ hJ.ne', neg_one_mul]
/-- **Push-forward of one bi-Lipschitz piece** (Simon Ch. 6, 3.4–3.7, for one piece `G(A)` of
`M`).  `G` is Lipschitz, bi-Lipschitz on the Borel set `A` with injective `DG` there, `G(A) ⊆ M`,
`∫_{G(A)} θ dHⁿ < ∞`, and `J_G(a) ξ(G(a)) = ±DG(a)_# e` for a.e. `a ∈ A`; `φ` is differentiable
and `Λ`-Lipschitz, and `H = φ ∘ G`.  If `DH` is nowhere injective on `A`, then `DH(a)_# e = 0`,
the integrand `θ ξ(β(φ) ∘ Dφ)` vanishes `Hⁿ`-a.e. on `G(A)`, and `N = ∅`.  If `H` is bi-Lipschitz
on `A` with injective `DH`, take `N = H(A)`, `g = θ ∘ G ∘ H⁻¹` and
`η = (J_G / J_H) ξ̃(G)(· ∘ Dφ(G)) ∘ H⁻¹`: `η(H(a)) = ±J_H(a)⁻¹ DH(a)_# e` orients `range DH(a)`,
the approximate tangent space of `N` at `H(a)`; `J_H ≤ Λⁿ J_G` bounds the mass; and the area
formula along `G` and along `H` turns both integrals into one integral over `A`. -/
theorem Submission.dtc_bc_lc_pfi_piece_pushforward_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (G : Euclid n → Euclid P) (A : Set (Euclid n)) (L : NNReal) (κ : ℝ) (φ : Euclid P → Euclid P) (Λ : NNReal), LipschitzWith L G → MeasurableSet A → 0 < κ → (∀ a ∈ A, ∀ a' ∈ A, κ * ‖a - a'‖ ≤ ‖G a - G a'‖) → (∀ a ∈ A, DifferentiableAt ℝ G a ∧ Injective (fderiv ℝ G a)) → G '' A ⊆ R.carrier → ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ → (∀ᵐ a ∂(volume.restrict A), ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ β : Covector (Euclid P) n, Real.sqrt (Matrix.det (Matrix.of fun k l : Fin n => inner ℝ (fderiv ℝ G a (EuclideanSpace.single k 1)) (fderiv ℝ G a (EuclideanSpace.single l 1)))) * R.orient (G a) β = σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1))) → Differentiable ℝ φ → LipschitzWith Λ φ → (((∃ κ' : ℝ, 0 < κ' ∧ ∀ a ∈ A, ∀ a' ∈ A, κ' * ‖a - a'‖ ≤ ‖φ (G a) - φ (G a')‖) ∧ ∀ a ∈ A, Injective (fderiv ℝ (φ ∘ G) a)) ∨ ∀ a ∈ A, ¬ Injective (fderiv ℝ (φ ∘ G) a)) → ∃ (N : Set (Euclid P)) (g : Euclid P → ℤ) (η : Euclid P → MultiVector P n), MeasurableSet N ∧ N ⊆ φ '' (G '' A) ∧ CountablyRectifiable n N ∧ Measurable g ∧ (∀ y ∈ N, g y ≠ 0) ∧ StronglyMeasurable η ∧ (∀ᵐ y ∂(μHE[n].restrict N), ∃ T : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n N y T ∧ IsUnitOrientationOf (η y) T) ∧ ∫⁻ y in N, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] ≤ (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] ∧ ∀ β : Euclid P → Covector (Euclid P) n, StronglyMeasurable β → ∫ x in G '' A, (R.mult x : ℝ) * R.orient x ((β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] = ∫ y in N, (g y : ℝ) * η y (β y) ∂μHE[n] := by
  intro P n U R G A L κ φ Λ hG hA hκ hbi hdiff hGA hfin hor hφd hφ hcase
  obtain ⟨hJacI, hcov⟩ := Submission.dtc_bc_lc_pfi_area_change_of_variables P n
  obtain ⟨-, -, horientInj, horientCrit⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  -- Gram Jacobians `J_G` of `G` and `J_H` of `H = φ ∘ G`
  obtain ⟨JG, hJG⟩ : ∃ JG : Euclid n → ℝ, ∀ x, JG x = Real.sqrt (Matrix.det (Matrix.of
      fun k l : Fin n => inner ℝ (fderiv ℝ G x (EuclideanSpace.single k 1))
        (fderiv ℝ G x (EuclideanSpace.single l 1)))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨JH, hJH⟩ : ∃ JH : Euclid n → ℝ, ∀ x, JH x = Real.sqrt (Matrix.det (Matrix.of
      fun k l : Fin n => inner ℝ (fderiv ℝ (φ ∘ G) x (EuclideanSpace.single k 1))
        (fderiv ℝ (φ ∘ G) x (EuclideanSpace.single l 1)))) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hJG] at hor
  -- Step 1(a): `G` is injective on `A`; change of variables along `G`
  have hinjOn : ∀ (F : Euclid n → Euclid P) (m : ℝ), 0 < m →
      (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → InjOn F A := by
    intro F m hm hF a ha a' ha' heq
    have h := hF a ha a' ha'
    rw [heq, sub_self, norm_zero] at h
    have h' : ‖a - a'‖ ≤ 0 := by nlinarith [norm_nonneg (a - a')]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h')
  have hGinj : InjOn G A := hinjOn G κ hκ hbi
  obtain ⟨-, -, hGpull, hGint⟩ := hcov G A hA hdiff hGinj
  simp only [← hJG] at hGint
  -- Step 1(b): the integrand `θ ξ(β(φ) ∘ Dφ)` is a.e. strongly measurable on `G(A)`
  have hDφ : StronglyMeasurable (fderiv ℝ φ) := (measurable_fderiv ℝ φ).stronglyMeasurable
  have hLHSm : ∀ β : Euclid P → Covector (Euclid P) n, StronglyMeasurable β →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) *
        R.orient x ((β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)))
        (μHE[n].restrict (G '' A)) := by
    intro β hβ
    have hβφ : StronglyMeasurable (fun x => (β (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) := by
      have hev : Continuous fun p : (Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n) ×
          Covector (Euclid P) n => p.1 p.2 := continuous_fst.clm_apply continuous_snd
      exact hev.comp_stronglyMeasurable
        ((ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable
          hDφ).prodMk (hβ.comp_measurable hφd.continuous.measurable))
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        ((R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hGA le_rfl)).prodMk
          hβφ.aestronglyMeasurable))
  -- Step 1(d): a strongly measurable `ξ̃ = ξ` a.e. on `M`, hence `ξ̃(G(a)) = ξ(G(a))` a.e. on `A`
  set ξ' := R.aestronglyMeasurable_orient.mk R.orient
  have hξ'm : StronglyMeasurable ξ' := R.aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξG : ∀ᵐ a ∂(volume.restrict A), R.orient (G a) = ξ' (G a) :=
    hGpull (fun x => R.orient x = ξ' x)
      (ae_restrict_of_ae_restrict_of_subset hGA R.aestronglyMeasurable_orient.ae_eq_mk)
  rcases hcase with ⟨⟨κ', hκ', hbi'⟩, hinjH⟩ | hcrit
  · -- Step 3: regular case, `N = H(A)`
    have hdiffH : ∀ a ∈ A, DifferentiableAt ℝ (φ ∘ G) a ∧ Injective (fderiv ℝ (φ ∘ G) a) :=
      fun a ha => ⟨(hφd (G a)).comp a (hdiff a ha).1, hinjH a ha⟩
    have hHinj : InjOn (φ ∘ G) A := hinjOn (φ ∘ G) κ' hκ' hbi'
    obtain ⟨hNm, hψm, -, hHint⟩ := hcov (φ ∘ G) A hA hdiffH hHinj
    simp only [← hJH] at hHint
    set ψ := Function.invFunOn (φ ∘ G) A
    have hψH : ∀ a ∈ A, ψ ((φ ∘ G) a) = a := fun a ha => hHinj.leftInvOn_invFunOn ha
    have hGψ : Measurable (fun y => G (ψ y)) := hG.continuous.measurable.comp hψm
    -- Step 3(b): `g = θ ∘ G ∘ ψ` and `η = (J_G/J_H) ∘ ψ · ξ̃(G ∘ ψ)(· ∘ Dφ(G ∘ ψ))`
    obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℤ, ∀ y, g y = (R.mult (G (ψ y)) : ℤ) := ⟨_, fun _ => rfl⟩
    obtain ⟨η, hη⟩ : ∃ η : Euclid P → MultiVector P n, ∀ y, η y = (JG (ψ y) / JH (ψ y)) •
        (ξ' (G (ψ y))).comp (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (fderiv ℝ φ (G (ψ y)))) := ⟨_, fun _ => rfl⟩
    have hgm : Measurable g := by
      rw [show g = fun y => ((R.mult (G (ψ y)) : ℕ) : ℤ) from funext hg]
      exact measurable_from_nat.comp (R.measurable_mult.comp hGψ)
    have hg0 : ∀ y ∈ (φ ∘ G) '' A, g y ≠ 0 := by
      rintro y ⟨a, ha, rfl⟩
      rw [hg, hψH a ha]
      exact Nat.cast_ne_zero.2 (R.mult_pos (G a) (hGA (mem_image_of_mem G ha))).ne'
    have hηm : StronglyMeasurable η := by
      have hJGm : Measurable JG := by
        have h := (Submission.codim1_lura_gram_area_formula n P G).1
        simp only [← hJG] at h
        exact h
      have hJHm : Measurable JH := by
        have h := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).1
        simp only [← hJH] at h
        exact h
      rw [show η = fun y => (JG (ψ y) / JH (ψ y)) •
          (ξ' (G (ψ y))).comp (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (fderiv ℝ φ (G (ψ y)))) from funext hη]
      exact ((hJGm.comp hψm).div (hJHm.comp hψm)).stronglyMeasurable.smul
        ((continuous_fst.clm_comp continuous_snd).comp_stronglyMeasurable
          ((hξ'm.comp_measurable hGψ).prodMk
            (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_stronglyMeasurable
              (hDφ.comp_measurable hGψ))))
    -- Step 3(c): `J_H ≤ ‖Dφ(G a)‖ⁿ J_G ≤ Λⁿ J_G` and `0 < J_H` on `A`
    have hJpos : ∀ a ∈ A, 0 < JH a := fun a ha => by
      rw [hJH]; exact (horientInj _ (hinjH a ha)).1
    have hJle : ∀ a ∈ A, JH a ≤ (Λ : ℝ) ^ n * JG a := by
      intro a ha
      have hcomp := fderiv_comp a (hφd (G a)) (hdiff a ha).1
      have h1 := hJacI (fderiv ℝ G a) (fderiv ℝ φ (G a)) (by rw [← hcomp]; exact hinjH a ha)
      rw [hJH, hJG, hcomp]
      refine h1.trans ?_
      gcongr
      exact norm_fderiv_le_of_lipschitz ℝ hφ
    -- Step 3(d): mass bound
    have hmass : ∫⁻ y in (φ ∘ G) '' A, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] ≤
        (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G '' A, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      have hareaH := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).2 A hA
        (fun a ha => (hdiffH a ha).1) (fun a ha => (hdiffH a ha).2) hHinj
      have hareaG := (Submission.codim1_lura_gram_area_formula n P G).2 A hA
        (fun a ha => (hdiff a ha).1) (fun a ha => (hdiff a ha).2) hGinj
      simp only [← hJG] at hareaG
      simp only [← hJH] at hareaH
      rw [hareaH, hareaG, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
      refine setLIntegral_mono' hA fun a ha => ?_
      rw [hg, hψH a ha, Int.natAbs_natCast, ← mul_assoc]
      gcongr
      calc ENNReal.ofReal (JH a) ≤ ENNReal.ofReal ((Λ : ℝ) ^ n * JG a) :=
            ENNReal.ofReal_le_ofReal (hJle a ha)
        _ = (Λ : ℝ≥0∞) ^ n * ENNReal.ofReal (JG a) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow NNReal.zero_le_coe,
            ENNReal.ofReal_coe_nnreal]
    have hNfin : μHE[n] ((φ ∘ G) '' A) ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfin)
        (le_trans ?_ hmass)
      calc μHE[n] ((φ ∘ G) '' A) = ∫⁻ _ in (φ ∘ G) '' A, 1 ∂μHE[n] := (setLIntegral_one _).symm
        _ ≤ ∫⁻ y in (φ ∘ G) '' A, ((g y).natAbs : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' hNm fun y hy => Nat.one_le_cast.2 (Int.natAbs_pos.2 (hg0 y hy))
    -- Step 3(e): `Hⁿ⌞N`-a.e. properties come from a.e. properties on `A` (`Hⁿ(H(A₀)) = 0`)
    have hpush : ∀ p : Euclid P → Prop, (∀ᵐ a ∂(volume.restrict A), p ((φ ∘ G) a)) →
        ∀ᵐ y ∂(μHE[n].restrict ((φ ∘ G) '' A)), p y := by
      intro p hp
      have hTm := measurableSet_toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)}
      have hT0 : volume (toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)} ∩ A) = 0 := by
        rw [← Measure.restrict_apply hTm, measure_toMeasurable]
        exact ae_iff.1 hp
      have hHT : μHE[n] ((φ ∘ G) '' (toMeasurable (volume.restrict A) {a | ¬ p ((φ ∘ G) a)} ∩ A))
          = 0 := by
        have h := (Submission.codim1_lura_gram_area_formula n P (φ ∘ G)).2 _ (hTm.inter hA)
          (fun a ha => (hdiffH a ha.2).1) (fun a ha => (hdiffH a ha.2).2)
          (hHinj.mono inter_subset_right) (fun _ => 1)
        rw [setLIntegral_one, setLIntegral_measure_zero _ _ hT0] at h
        exact h
      rw [ae_iff, Measure.restrict_apply' hNm]
      refine measure_mono_null ?_ hHT
      rintro y ⟨hy, a, ha, rfl⟩
      refine ⟨a, ⟨?_, ha⟩, rfl⟩
      by_contra haT
      exact hy (not_not.1 fun h => haT (subset_toMeasurable _ _ h))
    -- `H(A)` has approximate tangent space `range DH(a)` at `H(a)` for a.e. `a ∈ A`
    have htan := Submission.dpf_approxTangent_ae_bilipschitz_piece P n univ ((φ ∘ G) '' A) (φ ∘ G)
      A (Λ * L) κ' isOpen_univ hNm (subset_univ _)
      (fun C _ _ => ne_top_of_le_ne_top hNfin (measure_mono inter_subset_left)) (hφ.comp hG) hA
      hκ' hbi' hdiffH subset_rfl
    -- `η(H(a)) = ±J_H(a)⁻¹ DH(a)_# e` orients `range DH(a)`
    have hηor : ∀ a ∈ A, R.orient (G a) = ξ' (G a) → (∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∀ β : Covector (Euclid P) n, JG a * R.orient (G a) β =
          σ * β (fun k => fderiv ℝ G a (EuclideanSpace.single k 1))) →
        IsUnitOrientationOf (η ((φ ∘ G) a))
          (LinearMap.range (fderiv ℝ (φ ∘ G) a : Euclid n →ₗ[ℝ] Euclid P)) := by
      rintro a ha hξa ⟨σ, hσ, hσβ⟩
      obtain ⟨-, τ, hτ, hspan, hτor⟩ := horientInj _ (hinjH a ha)
      rw [← hJH a] at hτor
      have hcomp := fderiv_comp a (hφd (G a)) (hdiff a ha).1
      have key : ∀ α : Covector (Euclid P) n, η ((φ ∘ G) a) α =
          σ * ((JH a)⁻¹ * α (fun k => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1))) := by
        intro α
        rw [hη, hψH a ha, smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hξa, smul_eq_mul,
          div_eq_inv_mul, mul_assoc, hσβ, ContinuousAlternatingMap.compContinuousLinearMap_apply,
          hcomp]
        exact mul_left_comm _ _ _
      have hζ : ∀ α : Covector (Euclid P) n, ((JH a)⁻¹ •
          ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
            (fun k : Fin n => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1))) α =
          (JH a)⁻¹ * α (fun k => fderiv ℝ (φ ∘ G) a (EuclideanSpace.single k 1)) := fun α => rfl
      refine ⟨τ, hτ, hspan, ?_⟩
      rcases hσ with rfl | rfl <;> rcases hτor with h | h
      · exact Or.inl fun α => by rw [key, ← hζ, h, one_mul]
      · exact Or.inr fun α => by rw [key, ← hζ, h, one_mul]
      · exact Or.inr fun α => by rw [key, ← hζ, h, neg_one_mul]
      · exact Or.inl fun α => by rw [key, ← hζ, h, neg_one_mul, neg_neg]
    refine ⟨(φ ∘ G) '' A, g, η, hNm, (image_comp φ G A).subset,
      (Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hφ.comp hG)).mono
        (image_subset_range _ _), hgm, hg0, hηm, ?_, hmass, ?_⟩
    · refine hpush _ ?_
      filter_upwards [ae_restrict_mem hA, htan, hξG, hor] with a ha hta hξa hora
      exact ⟨_, hta, hηor a ha hξa hora⟩
    · -- Step 3(f): both sides are the same integral over `A`
      intro β hβ
      have hRHSm : AEStronglyMeasurable (fun y => (g y : ℝ) * η y (β y))
          (μHE[n].restrict ((φ ∘ G) '' A)) :=
        ((measurable_of_countable (Int.cast : ℤ → ℝ)).comp hgm).aestronglyMeasurable.mul
          ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
            (hηm.prodMk hβ)).aestronglyMeasurable
      rw [(hGint _ (hLHSm β hβ)).2, (hHint _ hRHSm).2]
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem hA, hξG] with a ha hξa
      rw [hg, hη, hψH a ha, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply, ← hξa, smul_eq_mul,
        Int.cast_natCast, Function.comp_apply]
      field_simp [(hJpos a ha).ne']
  · -- Step 2: critical case, `N = ∅`
    refine ⟨∅, fun _ => 0, fun _ => 0, MeasurableSet.empty, empty_subset _,
      Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty,
      measurable_const, fun y hy => hy.elim, stronglyMeasurable_const, by simp, by simp,
      fun β hβ => ?_⟩
    rw [(hGint _ (hLHSm β hβ)).2, Measure.restrict_empty, integral_zero_measure]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hA, hor] with a ha hora
    obtain ⟨σ, -, hσβ⟩ := hora
    have h0 : ((β (φ (G a))).compContinuousLinearMap (fderiv ℝ φ (G a)))
        (fun k => fderiv ℝ G a (EuclideanSpace.single k 1)) = 0 := by
      have h := horientCrit (fderiv ℝ (φ ∘ G) a) (hcrit a ha) (β (φ (G a)))
      rw [fderiv_comp a (hφd (G a)) (hdiff a ha).1] at h
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact h
    rw [Pi.zero_apply, mul_left_comm, hσβ, h0, mul_zero, mul_zero]
/-- **Integer density of a summable family** (step 10 of the push-forward proof, Simon
6.3.3–3.9).  If `fⱼ : ℝᴾ → ℤ` are measurable with `Σⱼ ∫ |fⱼ| dHⁿ < ∞`, then `m = Σⱼ fⱼ` (the real
`tsum`, `0` where the family is not summable) is measurable, integer valued everywhere and bounded
by `Σⱼ |fⱼ|`, and `Hⁿ`-a.e. the family `(fⱼ(y))ⱼ` is summable with sum `m(y)`. -/
theorem Submission.dtc_bc_lc_pfi_integer_density_of_summable : ∀ (P n : ℕ) (f : ℕ → Euclid P → ℤ), (∀ j, Measurable (f j)) → ∑' j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → ∃ m : Euclid P → ℝ, Measurable m ∧ (∀ y, ∃ z : ℤ, m y = z) ∧ (∀ y, ENNReal.ofReal |m y| ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞)) ∧ ∀ᵐ y ∂μHE[n], Summable (fun j => (f j y : ℝ)) ∧ m y = ∑' j, (f j y : ℝ) := by
  intro P n f hf hfin
  -- Step 3: a summable family of integers has finite support, so its tsum is a finite sum
  have hsum : ∀ y, Summable (fun j => (f j y : ℝ)) → ∃ s : Finset ℕ,
      ∑' j, (f j y : ℝ) = ∑ j ∈ s, (f j y : ℝ) := by
    intro y hs
    have hfs : {j | f j y ≠ 0}.Finite := by
      refine eventually_cofinite.1 ?_
      filter_upwards [hs.tendsto_cofinite_zero.eventually (ball_mem_nhds (0 : ℝ) one_pos)]
        with j hj
      rw [dist_zero_right, Real.norm_eq_abs] at hj
      exact Int.abs_lt_one_iff.1 (by exact_mod_cast hj)
    exact ⟨hfs.toFinset, tsum_eq_sum fun j hj => by simpa using hj⟩
  have hm : ∀ j, Measurable fun y => ((f j y).natAbs : ℝ≥0∞) := fun j =>
    (Measurable.of_discrete (f := fun z : ℤ => (z.natAbs : ℝ≥0∞))).comp (hf j)
  refine ⟨fun y => ∑' j, (f j y : ℝ), Measurable.tsum fun j => Measurable.of_discrete.comp (hf j),
    fun y => ?_, fun y => ?_, ?_⟩
  · -- Step 3: integrality (the tsum is `0` if the family is not summable)
    show ∃ z : ℤ, ∑' j, (f j y : ℝ) = z
    by_cases hs : Summable (fun j => (f j y : ℝ))
    · obtain ⟨s, hs⟩ := hsum y hs
      exact ⟨∑ j ∈ s, f j y, by rw [hs, Int.cast_sum]⟩
    · exact ⟨0, by rw [tsum_eq_zero_of_not_summable hs, Int.cast_zero]⟩
  · -- Step 4: pointwise bound `|m| ≤ S`
    show ENNReal.ofReal |∑' j, (f j y : ℝ)| ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞)
    by_cases hs : Summable (fun j => (f j y : ℝ))
    · obtain ⟨s, hs⟩ := hsum y hs
      calc ENNReal.ofReal |∑' j, (f j y : ℝ)| ≤ ENNReal.ofReal (∑ j ∈ s, |(f j y : ℝ)|) := by
            rw [hs]; exact ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)
        _ = ∑ j ∈ s, ((f j y).natAbs : ℝ≥0∞) := by
            rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
        _ ≤ ∑' j, ((f j y).natAbs : ℝ≥0∞) := ENNReal.sum_le_tsum s
    · rw [tsum_eq_zero_of_not_summable hs, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  · -- Step 5: `S = Σ_j |f_j|` has finite integral, so it is finite a.e.
    filter_upwards [ae_lt_top (Measurable.tsum hm)
      ((lintegral_tsum fun j => (hm j).aemeasurable).trans_ne hfin)] with y hy
    refine ⟨summable_abs_iff.1 ?_, rfl⟩
    have h1 : Summable fun j => ((f j y).natAbs : NNReal) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa using hy.ne
    simpa [Nat.cast_natAbs] using NNReal.summable_coe.2 h1

/-- **Simon Ch. 6, 3.7–3.9 (gluing integer pieces)**: let `U` be open, `N_j ⊆ U` Borel and
countably `n`-rectifiable, `g_j` integer-valued and nonzero on `N_j`, and `η_j` a unit orientation
of an approximate tangent space of `N_j` at `Hⁿ`-a.e. point of `N_j`, with
`Σ_j ∫_{N_j} |g_j| dHⁿ < ∞`.  If `Q(ω) = Σ_j ∫_{N_j} g_j ⟨ω, η_j⟩ dHⁿ` for `ω ∈ 𝒟ⁿ(U)`, then `Q` is
integer multiplicity.  The locality of approximate tangent spaces (Ch. 3, Remarks 1.5(2),
1.8(1)) is the first hypothesis.

Proof sketch:
* `N = ⋃_j N_j` is Borel and countably `n`-rectifiable, and `Hⁿ(N) ≤ Σ_j ∫_{N_j} |g_j| < ∞`
  since `|g_j| ≥ 1` on `N_j`.
* By locality, for `Hⁿ`-a.e. `y` and every `j` with `y ∈ N_j`, `η_j(y)` orients an approximate
  tangent space of `N` at `y`.
* `ξ(y) = η_{j₀(y)}(y)`, `j₀(y)` the first `j` with `y ∈ N_j`, is strongly measurable and orients
  the (unique) approximate tangent space of `N` a.e. on `N`, so `η_j = ±ξ` a.e. on `N_j` (3.7).
* With `f_j = 1_{N_j} (±g_j)` (so that `g_j η_j = f_j ξ` a.e. on `N_j`), the integer density
  `m = Σ_j f_j` (3.8) is measurable and `Hⁿ`-integrable.
* Dominated convergence (`|⟨ω, ξ⟩| ≤ sup ‖ω‖` a.e. on `N`) gives `Q(ω) = ∫_N m ⟨ω, ξ⟩ dHⁿ`, and
  `(N, m, ξ)` yields an `IMRep` (3.9) by `cmcdt_ims_imrep_of_int_density`. -/
theorem Submission.dtc_bc_lc_pfi_isIntegerMultiplicity_of_pieces : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (N : ℕ → Set (Euclid P)) (g : ℕ → Euclid P → ℤ) (η : ℕ → Euclid P → MultiVector P n) (Q : GeometricCurrentOn U n), IsOpen U → (∀ j, MeasurableSet (N j)) → (∀ j, N j ⊆ U) → (∀ j, CountablyRectifiable n (N j)) → (∀ j, Measurable (g j)) → (∀ j, ∀ y ∈ N j, g j y ≠ 0) → (∀ j, StronglyMeasurable (η j)) → (∀ j, ∀ᵐ y ∂(μHE[n].restrict (N j)), ∃ T : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (N j) y T ∧ IsUnitOrientationOf (η j y) T) → ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ → (∀ ω : TestFormOn U n, Q ω = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y ((ω : DifferentialForm (Euclid P) n) y) ∂μHE[n]) → IsIntegerMultiplicity Q := by
  intro hTL P n U N g η Q hU hNmeas hNU hNrect hg hg0 hη hηor hsum hQ
  classical
  -- `MultiVector P n` is (pseudo)metrizable; instance search does not find it
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace (MultiVector P n) inferInstance
  obtain ⟨horient_pm, horient_le, -, -⟩ := Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n
  -- Step 1: the union `NN = ⋃_j N_j`, of finite measure since `|g_j| ≥ 1` on `N_j`
  set NN : Set (Euclid P) := ⋃ j, N j
  have hNNmeas : MeasurableSet NN := MeasurableSet.iUnion hNmeas
  have hNNU : NN ⊆ U := iUnion_subset hNU
  have hNNrect : CountablyRectifiable n NN :=
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion N hNrect
  have hNjle : ∀ j, μHE[n] (N j) ≤ ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] := by
    intro j
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (hNmeas j) fun y hy => ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (hg0 j y hy))
  have hNNfin : μHE[n] NN ≠ ∞ :=
    ne_top_of_le_ne_top hsum ((measure_iUnion_le N).trans (ENNReal.tsum_le_tsum hNjle))
  have hNNK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (NN ∩ K) ≠ ∞ :=
    fun K _ _ => ne_top_of_le_ne_top hNNfin (measure_mono inter_subset_left)
  -- Step 2: by locality (`hTL`), a.e. on `N_j`, `η_j` orients a tangent space of `NN`
  have hgood : ∀ᵐ y ∂μHE[n], ∀ j, y ∈ N j → ∃ T : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n NN y T ∧ IsUnitOrientationOf (η j y) T := by
    refine ae_all_iff.2 fun j => (ae_restrict_iff' (hNmeas j)).1 ?_
    filter_upwards [hTL P n U (N j) NN hU (hNmeas j) hNNmeas (subset_iUnion N j) hNNU hNNK,
      hηor j] with y hy hyη
    obtain ⟨T, hT, hTη⟩ := hyη
    exact ⟨T, (hy T).2 hT, hTη⟩
  -- Step 3: the common orientation `ξ(y) = η_{j₀(y)}(y)`, `j₀(y)` the first `j` with `y ∈ N_j`
  have hex : ∀ y, ∃ j, y ∈ N j ∨ y ∉ NN := fun y => by
    by_cases hy : y ∈ NN
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hy
      exact ⟨j, Or.inl hj⟩
    · exact ⟨0, Or.inr hy⟩
  set j₀ : Euclid P → ℕ := fun y => Nat.find (hex y)
  have hj₀meas : Measurable j₀ := measurable_find hex fun j => (hNmeas j).union hNNmeas.compl
  have hj₀mem : ∀ y ∈ NN, y ∈ N (j₀ y) := fun y hy =>
    (Nat.find_spec (hex y)).resolve_right (not_not.2 hy)
  set ξ : Euclid P → MultiVector P n := fun y => η (j₀ y) y
  have hξsm : StronglyMeasurable ξ :=
    (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun _ => continuous_of_discreteTopology) hη).comp_measurable (hj₀meas.prodMk measurable_id)
  have hξor : ∀ᵐ y ∂(μHE[n].restrict NN), ∃ T : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n NN y T ∧ IsUnitOrientationOf (ξ y) T := by
    filter_upwards [ae_restrict_of_ae hgood, ae_restrict_mem hNNmeas] with y hy hyNN
    exact hy (j₀ y) (hj₀mem y hyNN)
  -- Step 4: `η_j = ±ξ` a.e. on `N_j`, by uniqueness of approximate tangent spaces
  have hsign : ∀ᵐ y ∂μHE[n], ∀ j, y ∈ N j → η j y = ξ y ∨ η j y = -ξ y := by
    filter_upwards [hgood] with y hy j hyj
    obtain ⟨T, hT, hTη⟩ := hy j hyj
    obtain ⟨T', hT', hT'ξ⟩ := hy (j₀ y) (hj₀mem y (mem_iUnion.2 ⟨j, hyj⟩))
    rw [hT'.unique hT] at hT'ξ
    exact horient_pm (ξ y) (η j y) T hT'ξ hTη
  -- Step 5: the integer density `m = Σ_j f_j`, `f_j = 1_{N_j} (±g_j)` with `g_j η_j = f_j ξ`
  set f : ℕ → Euclid P → ℤ := fun j y =>
    if y ∈ N j then (if η j y = ξ y then g j y else -g j y) else 0 with hfdef
  have hf_meas : ∀ j, Measurable (f j) := fun j =>
    Measurable.ite (hNmeas j)
      (Measurable.ite ((hη j).measurableSet_eq_fun hξsm) (hg j)
        ((measurable_of_countable fun z : ℤ => -z).comp (hg j)))
      measurable_const
  have hf_natAbs_meas : ∀ j, Measurable fun y => ((f j y).natAbs : ℝ≥0∞) := fun j =>
    (measurable_of_countable fun z : ℤ => ((z.natAbs : ℕ) : ℝ≥0∞)).comp (hf_meas j)
  have hf_abs : ∀ j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] =
      ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] := by
    intro j
    rw [← lintegral_indicator (hNmeas j)]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ N j
    · rw [indicator_of_mem hy]
      simp only [hfdef, ite_eq_left hy]
      split_ifs <;> simp
    · rw [indicator_of_notMem hy]
      simp [hfdef, hy]
  have hf_sum : ∑' j, ∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    rwa [tsum_congr hf_abs]
  obtain ⟨m, hm_meas, hm_int, hm_le, hm_ae⟩ :=
    Submission.dtc_bc_lc_pfi_integer_density_of_summable P n f hf_meas hf_sum
  have hm_loc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in NN ∩ K, ‖m x‖ₑ ∂μHE[n] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top hf_sum ((setLIntegral_le_lintegral _ _).trans ?_)
    calc ∫⁻ x, ‖m x‖ₑ ∂μHE[n]
        ≤ ∫⁻ x, ∑' j, ((f j x).natAbs : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono fun x => (Real.enorm_eq_ofReal_abs (m x)).trans_le (hm_le x)
      _ = ∑' j, ∫⁻ x, ((f j x).natAbs : ℝ≥0∞) ∂μHE[n] :=
          lintegral_tsum fun j => (hf_natAbs_meas j).aemeasurable
  -- Step 6: the triple `(NN, m, ξ)` gives an `IMRep` acting by `ω ↦ ∫_NN m ⟨ω, ξ⟩ dHⁿ`
  obtain ⟨R, hR⟩ := Submission.cmcdt_ims_imrep_of_int_density P n U NN ξ m hU hNNmeas hNNU
    hNNrect hNNK hξsm hm_meas hm_int hm_loc hξor
  refine ⟨R, fun ω => ?_⟩
  -- Step 7: `Q(ω) = Σ_j ∫_NN f_j ⟨ω, ξ⟩ dHⁿ = ∫_NN m ⟨ω, ξ⟩ dHⁿ` by dominated convergence
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hwc : Continuous w := ω.property.1.1.continuous
  obtain ⟨C, hC⟩ := hwc.bounded_above_of_compact_support ω.property.1.2
  have hpiece : ∀ j, ∫ y in N j, (g j y : ℝ) * η j y (w y) ∂μHE[n] =
      ∫ y in NN, (f j y : ℝ) * ξ y (w y) ∂μHE[n] := by
    intro j
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hNNmeas (subset_iUnion N j)
      fun y hy => by simp [hfdef, hy.2]]
    refine setIntegral_congr_ae (hNmeas j) ?_
    filter_upwards [hsign] with y hy hyj
    simp only [hfdef, ite_eq_left hyj]
    split_ifs with he
    · rw [he]
    · rcases hy j hyj with h | h
      · exact absurd h he
      · rw [h, neg_apply, Int.cast_neg, mul_neg, neg_mul]
  have hξbd : ∀ᵐ y ∂(μHE[n].restrict NN), ‖ξ y (w y)‖ₑ ≤ ENNReal.ofReal C := by
    filter_upwards [hξor] with y hy
    obtain ⟨T, -, hT⟩ := hy
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal ((horient_le (ξ y) T hT (w y)).trans (hC y))
  have hcont : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hterm_meas : ∀ j, AEStronglyMeasurable (fun y => (f j y : ℝ) * ξ y (w y))
      (μHE[n].restrict NN) := fun j =>
    ((measurable_of_countable fun z : ℤ => (z : ℝ)).comp (hf_meas j)).aestronglyMeasurable.mul
      (hcont.comp_aestronglyMeasurable (hξsm.aestronglyMeasurable.prodMk hwc.aestronglyMeasurable))
  have hzabs : ∀ z : ℤ, ‖(z : ℝ)‖ₑ = ((z.natAbs : ℕ) : ℝ≥0∞) := fun z => by
    rw [Real.enorm_eq_ofReal_abs, show |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) by simp [Nat.cast_natAbs],
      ENNReal.ofReal_natCast]
  have hterm_bd : ∑' j, ∫⁻ y in NN, ‖(f j y : ℝ) * ξ y (w y)‖ₑ ∂μHE[n] ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hf_sum (ENNReal.ofReal_ne_top (r := C))) ?_
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun j => ?_
    calc ∫⁻ y in NN, ‖(f j y : ℝ) * ξ y (w y)‖ₑ ∂μHE[n]
        ≤ ∫⁻ y in NN, ((f j y).natAbs : ℝ≥0∞) * ENNReal.ofReal C ∂μHE[n] := by
          refine lintegral_mono_ae ?_
          filter_upwards [hξbd] with y hy
          rw [enorm_mul, hzabs]
          exact mul_le_mul_right hy _
      _ = (∫⁻ y in NN, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n]) * ENNReal.ofReal C :=
          lintegral_mul_const _ (hf_natAbs_meas j)
      _ ≤ (∫⁻ y, ((f j y).natAbs : ℝ≥0∞) ∂μHE[n]) * ENNReal.ofReal C :=
          mul_le_mul_left (setLIntegral_le_lintegral _ _) _
  have hsum_eq : ∀ᵐ y ∂(μHE[n].restrict NN),
      ∑' j, (f j y : ℝ) * ξ y (w y) = m y * ξ y (w y) := by
    filter_upwards [ae_restrict_of_ae hm_ae] with y hy
    rw [tsum_mul_right, ← hy.2]
  calc Q ω = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y (w y) ∂μHE[n] := hQ ω
    _ = ∑' j, ∫ y in NN, (f j y : ℝ) * ξ y (w y) ∂μHE[n] := tsum_congr hpiece
    _ = ∫ y in NN, ∑' j, (f j y : ℝ) * ξ y (w y) ∂μHE[n] :=
        (integral_tsum hterm_meas hterm_bd).symm
    _ = ∫ y in NN, m y * ξ y (w y) ∂μHE[n] := integral_congr_ae hsum_eq
    _ = R.action w := (hR w).symm
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- A unit orientation has operator norm at most `1` (step 1(c) of the proof that the weight of
`T = τ(M, θ, ξ)` is at most its mass).  If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`,
then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖` for every `n`-covector `α`, so `‖ξ‖ ≤ 1`. -/
theorem Submission.rsd_mw_wlm_orient_opNorm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **A unit-scale blow-up is a translation** (Simon 6.2.23 for `η_{−v,1}(y) = v + y`; the
translation `τ_{v#}` of Lemma 7.3.5).  For `S ∈ 𝒟ₙ(ℝᴾ)`, `v ∈ ℝᴾ` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, the translate
`ω' = ω(v + ·)` is a test form and `currentEval (η_{−v,1#}S) ω = S(ω')`: `η_{−v,1}(ℝᴾ) = ℝᴾ`, and
unfolding `blowUp` (linear part `dilationCLM P 1 = id`, translation `−(1⁻¹ • −v) = v`) the affine
pullback of `ω` is `y ↦ ω(v + y) ∘ id = ω'(y)`. -/
theorem Submission.dimred_cs_ti_blowUp_translate_eval : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (v : Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) n), ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (v + y)) ∧ currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω' := by
  intro P n S v ω
  -- Step 1: the translate `y ↦ ω(v + y)` is a test form.
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) :=
    ω.property.1.1.comp (contDiff_const.add contDiff_id)
  have hcs : HasCompactSupport (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) :=
    ω.property.1.2.comp_homeomorph (Homeomorph.addLeft v)
  let ω' : TestFormOn (univ : Set (Euclid P)) n :=
    ⟨fun y => (ω : DifferentialForm (Euclid P) n) (v + y), ⟨hsm, hcs⟩, subset_univ _⟩
  refine ⟨ω', fun y => rfl, ?_⟩
  -- Steps 2–3: `η_{−v,1}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (-v) (1 : ℝ) '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨x - v, mem_univ _, ?_⟩
    simp [dilation, dilationCLM]
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (-v) (1 : ℝ) '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h]
  -- Steps 4–5: unfolding `blowUp`, the affine pullback of `ω` by `y ↦ v + 1⁻¹ y` is `ω'`.
  change S _ = S ω'
  congr 1
  apply Subtype.ext
  funext y
  ext w
  change (ω : DifferentialForm (Euclid P) n) (-((1 : ℝ)⁻¹ • -v) + dilationCLM P 1 y)
      (fun i => dilationCLM P 1 (w i)) = (ω : DifferentialForm (Euclid P) n) (v + y) w
  simp [dilationCLM]
/-- `v ∧ ξ(x) = 0` a.e. when `v` lies in the approximate tangent plane a.e. (the translation part of
the proof of Simon Lemma 7.3.5): `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`, and
`y ↦ β(y, τ₁, …, τₙ)` is linear and vanishes on each `τᵢ` (repeated entry), hence on `TₓM ∋ v`. -/
theorem Submission.dimred_cs_ti_wedge_vanishes : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (v : Euclid P), (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection v = v) → ∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β v) = 0 := by
  intro P n U R v hproj
  -- `μ = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so `ξ` orients an approximate tangent plane `μ`-a.e.
  filter_upwards [hproj, (withDensity_absolutelyContinuous _ _).ae_le R.orients]
    with x hx hor β
  obtain ⟨Q, hQ, τ, -, hspan, hξ⟩ := hor
  -- `TₓM = Q` by uniqueness of approximate tangent planes, so `v ∈ Q`
  have hT : approxTangentPlane n R.carrier x = Q := by
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.unique hQ
  have hvQ : v ∈ Q := hT ▸ Submodule.starProjection_eq_self_iff.mp hx
  -- `y ↦ β(y, τ)` vanishes on `Q = span(range τ)`
  have hβ : ∀ y ∈ Q, ContinuousAlternatingMap.curryLeft β y τ = 0 := by
    intro y hy
    rw [← hspan] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      exact β.map_eq_zero_of_eq _ (i := 0) (j := b.succ) (by simp) (Fin.succ_ne_zero b).symm
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, ContinuousAlternatingMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy =>
      rw [map_smul, ContinuousAlternatingMap.smul_apply, hy, smul_zero]
  rcases hξ with hξ | hξ
  · rw [hξ, hβ v hvQ]
  · rw [hξ, hβ v hvQ, neg_zero]
/-- **Cartan's formula for a constant field** `X ≡ v` (Simon Ch. 6, 2.25–2.26, the infinitesimal
form of the homotopy `h(t, x) = x + tv`).  For an `(m+1)`-form `β` differentiable at `y`,
`d(ι_v β)(y) + ι_v dβ(y) = Dβ(y)[v]`.  With `B = Dβ(y)`, `D(ι_v β)(y) u = (B u).curryLeft v`, and every
term of `d(ι_v β)(y)(w)` cancels a term of `dβ(y)(v, w)`, leaving its `k = 0` term `B v w`. -/
theorem Submission.dimred_cs_ti_const_cartan : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)) (v y : Euclid P), DifferentiableAt ℝ β y → exteriorDerivative (fun z => ContinuousAlternatingMap.curryLeft (β z) v) y + ContinuousAlternatingMap.curryLeft (exteriorDerivative β y) v = fderiv ℝ β y v := by
  intro P m β v y hβ
  -- `ι_v β = Φ ∘ β` for the continuous linear map `Φ α = α.curryLeft v`
  let Φ : Covector (Euclid P) (m + 1) →L[ℝ] Covector (Euclid P) m :=
    (ContinuousLinearMap.apply ℝ (Covector (Euclid P) m) v).comp
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
        (n := m)).toContinuousLinearMap
  have hD : fderiv ℝ (fun z => Φ (β z)) y = Φ.comp (fderiv ℝ β y) :=
    (Φ.hasFDerivAt.comp y hβ.hasFDerivAt).fderiv
  have h1 : exteriorDerivative (fun z => ContinuousAlternatingMap.curryLeft (β z) v) y =
      ContinuousAlternatingMap.alternatizeUncurryFin (Φ.comp (fderiv ℝ β y)) := by
    rw [← hD]
    rfl
  -- removing entry `i + 1` of `(v, w)` leaves `(v, w without wᵢ)`
  have hrm : ∀ (i : Fin (m + 1)) (w : Fin (m + 1) → Euclid P),
      Fin.removeNth i.succ (Matrix.vecCons v w) = Matrix.vecCons v (Fin.removeNth i w) := by
    intro i w
    funext j
    cases j using Fin.cases with
    | zero => simp [Fin.removeNth_apply]
    | succ j => simp [Fin.removeNth_apply]
  rw [h1]
  ext w
  simp only [ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply, exteriorDerivative, extDeriv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply,
    LinearIsometry.coe_toContinuousLinearMap, ContinuousAlternatingMap.curryLeftLI_apply, Φ]
  -- split off the `k = 0` term `B v w` of `dβ(y)(v, w)`; the other terms cancel the first sum
  rw [Fin.sum_univ_succ (n := m + 1)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.removeNth_zero, Fin.tail_vecCons,
    hrm, Fin.val_zero, Fin.val_succ, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul,
    Finset.sum_neg_distrib]
  abel
/-- **Contraction with a constant vector preserves test forms** (Simon Ch. 6, 2.25–2.26, the
constant-field counterpart of the Euler-field contraction used for 7.3.1).  If `β` is a test
`(m+1)`-form and `v ∈ ℝᴾ`, then `ι_v β : z ↦ β(z).curryLeft v` is a test `m`-form: it is the
continuous linear map `α ↦ α.curryLeft v` applied to the smooth `β`, and it vanishes wherever `β`
does, so its support lies in the compact `tsupport β`. -/
theorem Submission.dimred_cs_ti_const_contraction_isTestForm : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)) (v : Euclid P), IsTestForm β → IsTestForm (fun z => ContinuousAlternatingMap.curryLeft (β z) v) := by
  intro P m β v hβ
  obtain ⟨hs, hc⟩ := hβ
  refine ⟨?_, ?_⟩
  · -- `z ↦ (curryLeftLI (β z)) v` is a smooth family of continuous linear maps applied to `v`
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
      (E := Euclid P) (F := ℝ) (n := m)).toContinuousLinearMap (β z) v)
    exact (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
      (n := m)).toContinuousLinearMap.contDiff).comp hs).clm_apply contDiff_const
  · -- `β z = 0` forces `β(z).curryLeft v = 0`, so the support stays inside `supp β`
    refine hc.mono ?_
    intro z hz
    simp only [mem_support] at hz ⊢
    intro h0
    apply hz
    rw [h0]
    rfl

/-- **`∂S = 0` and `v ∧ S⃗ = 0` kill directional derivatives** (`L_v S = 0`, the homotopy term of
Simon Ch. 6, 2.25 and 2.33 for `h(t, x) = x + tv`; the translation counterpart of the Euler-field
annihilation in the proof of 7.3.1).  Let `S = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)`, `n ≥ 1`, with `∂S = 0` and
`ξ(x)(ι_v α) = 0` for `μ_S`-a.e. `x` and every `(n+1)`-covector `α`.  Then `S(γ) = 0` whenever
`γ(y) = Dβ(y)[v]` for a test form `β`: by Cartan's formula `Dβ[v] = d(ι_v β) + ι_v dβ` with
`ι_v β`, `ι_v dβ` test forms, `S(d ι_v β) = ∂S(ι_v β) = 0`, and
`S(ι_v dβ) = ∫_M θ ξ(ι_v dβ(y)) dHⁿ = 0` since `θ > 0` on `M`. -/
theorem Submission.dimred_cs_ti_directional_annihilated : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), 0 < n → R.Represents S → BoundaryVanishes S → (∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β v) = 0) → ∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = fderiv ℝ (β : DifferentialForm (Euclid P) n) y v) → S γ = 0 := by
  intro P n S R v hn hR hb hw β γ hγ
  -- Step 1: `n = m + 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Step 2: `ψ = ι_v β` is a test `m`-form and `χ = ι_v dβ` is a test `(m + 1)`-form
  have hψ : IsTestForm (fun z => ContinuousAlternatingMap.curryLeft
      ((β : DifferentialForm (Euclid P) (m + 1)) z) v) :=
    Submission.dimred_cs_ti_const_contraction_isTestForm P m _ v β.property.1
  let ψ : TestFormOn (univ : Set (Euclid P)) m := ⟨_, hψ, subset_univ _⟩
  have hdβ : IsTestForm (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1))) :=
    exteriorDerivative_isTestForm β.property.1
  have hχ := Submission.dimred_cs_ti_const_contraction_isTestForm P (m + 1) _ v hdβ
  let χ : TestFormOn (univ : Set (Euclid P)) (m + 1) := ⟨_, hχ, subset_univ _⟩
  -- Step 3 (Cartan's formula): `γ = Dβ[v] = dψ + χ`
  have hsplit : γ = exteriorDerivativeTestOn univ m ψ + χ := by
    apply Subtype.ext
    funext y
    have hdiff : DifferentiableAt ℝ (β : DifferentialForm (Euclid P) (m + 1)) y :=
      (β.property.1.1.differentiable (by simp)).differentiableAt
    have hc := Submission.dimred_cs_ti_const_cartan P m β v y hdiff
    rw [hγ y]
    push_cast
    exact hc.symm
  -- Step 4 (boundary term): `S(dψ) = ∂S(ψ) = 0`
  have hbd : S.boundary = 0 := hb
  have h1 : S (exteriorDerivativeTestOn univ m ψ) = 0 := by
    have := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) m => T ψ) hbd
    simpa [GeometricCurrentOn.boundary_apply] using this
  -- Step 5 (wedge term): `S(χ) = ∫_M θ ξ(ι_v dβ(x)) dHⁿ = 0`, as `θ > 0` on `M`
  have h2 : S χ = 0 := by
    rw [hR χ]
    unfold IMRep.action
    apply integral_eq_zero_of_ae
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      measurable_from_nat.comp R.measurable_mult
    have h' := (ae_withDensity_iff hθ).1 hw
    have hmem : ∀ᵐ x ∂(μHE[m + 1].restrict R.carrier), x ∈ R.carrier :=
      ae_restrict_mem R.measurableSet_carrier
    filter_upwards [h', hmem] with x hx hxM
    have hpos : (R.mult x : ℝ≥0∞) ≠ 0 := by
      have := R.mult_pos x hxM
      exact_mod_cast this.ne'
    have := hx hpos (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x)
    simp only [Pi.zero_apply]
    change (R.mult x : ℝ) * R.orient x (ContinuousAlternatingMap.curryLeft
      (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x) v) = 0
    rw [this, mul_zero]
  -- Step 6 (linearity): `S(γ) = S(dψ) + S(χ) = 0`
  rw [hsplit]
  change S.toCurrent (exteriorDerivativeTestOn univ m ψ + χ) = 0
  rw [map_add]
  exact (congrArg₂ (· + ·) h1 h2).trans (add_zero 0)
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
/-- **Simon Ch. 3, Definition 1.4 and Remark 1.5(1)**: an approximate tangent space of `M` at `x`
lies in every subspace `T` along which a set `N` carrying `Hⁿ`-almost all of `M` is flat at `x`
(for each `ε > 0` there is `ρ > 0` such that every `z ∈ N` with `|z − x| < ρ` has some `t ∈ T`
with `|z − x − t| ≤ ε|z − x|`).  If `q ∈ Q \ T`, put `δ = dist(q, T) > 0` and
`g = max(0, δ/2 − |· − q|) ∈ C_c(ℝᴾ)`; `∫_Q g dHⁿ > 0` because `spt(Hⁿ⌞Q) = Q`.  With
`ε = δ / (2(|q| + δ))` and `0 < r < ρ / (|q| + δ)`, flatness makes `g` vanish on `η_{x,r}(M ∩ N)`,
and `Hⁿ(η_{x,r}(M \ N)) = 0`; so `∫_{η_{x,r}(M)} g dHⁿ = 0` for all small `r`, contradicting
the defining limit. -/
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  -- `T` is closed, so `δ = dist(q, T) > 0`
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
  -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants: `ε (|q| + δ) = δ / 2`
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- `∫_{η_{x,r}(M)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    -- `η_{x,r}(M \ N) = r⁻¹ (M \ N − x)` is `Hⁿ`-null
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (M \ N)) := by
        rw [Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    -- flatness: `g` vanishes on `η_{x,r}(M ∩ N)`
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(M)`, evaluated on the open set `{g ≠ 0}`
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith

/-- **Simon 7.3.1, footnote 2** (`spt C ⊆ TₓN`): if the weight `θ Hᵐ⌞M` of the triple
`R = (M, θ, ξ)` gives no mass to `ℝᴾ \ V`, the orthogonal projection `q` onto `V` fixes
`τ(M, θ, ξ)`: `τ(M, θ, ξ)(q^#ω) = τ(M, θ, ξ)(ω)`.  As `θ ≥ 1` on `M`, `Hᵐ(M \ V) = 0`; so for
`Hᵐ`-a.e. `x ∈ M`, `x ∈ V` and the approximate tangent plane oriented by `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₘ`
lies in `V` (along which `V` is flat at `x`).  Then `qx = x`, `qτᵢ = τᵢ` and
`⟨(q^#ω)(x), ξ(x)⟩ = ⟨ω(x), ξ(x)⟩`. -/
theorem Submission.idtp_fons_cs_sp_action_starProjection_eq : ∀ (P m : ℕ) (R : IMRep (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)), R.measure ((V : Set (Euclid P))ᶜ) = 0 → ∀ ω : DifferentialForm (Euclid P) m, R.action (affinePullbackForm V.starProjection 0 ω) = R.action ω := by
  intro P m R V hV ω
  -- `Hᵐ(M \ V) = 0`, since `θ ≥ 1` on `M`
  have hnull : μHE[m] (R.carrier \ (V : Set (Euclid P))) = 0 := by
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
    rw [IMRep.measure, withDensity_apply_eq_zero hθ,
      Measure.restrict_apply' R.measurableSet_carrier] at hV
    refine measure_mono_null ?_ hV
    intro x hx
    exact ⟨⟨Nat.cast_ne_zero.2 (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
  -- so `Hᵐ⌞M`-a.e. `x` lies in `V`
  have hVae : ∀ᵐ x ∂(μHE[m].restrict R.carrier), x ∈ (V : Set (Euclid P)) := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hxM
    by_contra hxV
    exact hx ⟨hxM, hxV⟩
  -- the integrands agree `Hᵐ⌞M`-a.e.
  unfold IMRep.action
  refine integral_congr_ae ?_
  filter_upwards [hVae, R.orients] with x hxV hQ
  obtain ⟨Q, hQ, τ, -, hspan, hor⟩ := hQ
  -- `TₓM = Q ≤ V`: `V` is flat at `x ∈ V` along `V` (take `t = z - x`)
  have hQV : Q ≤ V :=
    Submission.atsm_approxTangent_le_of_flat P m (V : Set (Euclid P)) R.carrier x Q V hnull
      (fun ε hε => ⟨1, one_pos, fun z hz _ => ⟨z - x, V.sub_mem hz hxV, by
        rw [sub_self, norm_zero]
        positivity⟩⟩) hQ
  have hτ : V.starProjection ∘ τ = τ := by
    funext i
    exact Submodule.starProjection_eq_self_iff.2
      (hQV (hspan ▸ Submodule.subset_span (mem_range_self i)))
  have hx : V.starProjection x = x := Submodule.starProjection_eq_self_iff.2 hxV
  congr 1
  rcases hor with hor | hor <;>
    simp only [hor, affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      zero_add, hx, hτ]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- **Simon 6.3.2(3)** (with 6.2.4–6.2.8): for `T = τ(M, θ, ξ)` in `U` and open `W ⊆ U`,
`M_W(T) = μ_T(W) = ∫_{M ∩ W} θ dHⁿ`.  Upper bound: for admissible `ω`, `|⟨ω, ξ⟩| ≤ |ω| ≤ 1_W`
`Hⁿ`-a.e. on `M`, so `T(ω) ≤ μ_T(W)`.  Lower bound on a compact `K ⊆ W`, then exhaust `W`: with
`L` the dual of `dor_ims_unitOrientation_dual` (`|L(ξ)| ≤ 1`, `⟨L(ξ), ξ⟩ = 1`), approximate
`f = 1_K L(ξ)` in `L¹(μ_T⌞K_δ)` by a continuous compactly supported `g`, truncate to
`β = g / max(1, |g|)` (so `|β - f| ≤ 2|g - f|`), smooth to `h` with `‖h - β‖ < δ`, and take
`ω = χ h / (1 + Cδ)`, `χ ∈ C^∞`, `χ = 1` on `K`, `spt χ ⊆ K_δ`: `ω` is admissible and
`T(ω) ≥ μ_T(K) - ε`. -/
theorem Submission.dtc_mass_eq_measure : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → W ⊆ U → R.Represents T → T.massOn W = R.measure W := by
  intro P n U W T R _ hW hWU hRT
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `L` is bounded on the unit ball (continuity at `0`)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ξ : MultiVector P n, ‖ξ‖ ≤ 1 → ‖L ξ‖ ≤ B := by
    have hcont : ∀ ε > 0, ∃ δ > 0, ∀ {x : MultiVector P n}, dist x 0 < δ →
        dist (L x) (L 0) < ε :=
      Metric.continuousAt_iff.1 (L.continuous.continuousAt (x := 0))
    obtain ⟨δ, hδ, hδL⟩ := hcont 1 one_pos
    refine ⟨2 / δ, fun ξ hξ => ?_⟩
    have hsm : ‖(δ / 2) • ξ‖ ≤ δ / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
      rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
      gcongr
      calc ‖ξ α‖ ≤ ‖ξ‖ * ‖α‖ := ξ.le_opNorm α
        _ ≤ 1 * ‖α‖ := by gcongr
        _ = ‖α‖ := one_mul _
    have h1 : dist ((δ / 2) • ξ) 0 < δ := by
      rw [dist_zero_right (E := MultiVector P n) _]
      linarith
    have h3 : dist (L ((δ / 2) • ξ)) (L 0) < 1 := hδL h1
    rw [map_smul, map_zero, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity)] at h3
    rw [le_div_iff₀ hδ]
    nlinarith [norm_nonneg (L ξ)]
  -- `|α| = ‖c α‖` for the linear coefficient map `c α = (α(e_I))_I` (`I` strictly increasing)
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : Covector (Euclid P) n →ₗ[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    { toFun := fun α => WithLp.toLp 2 fun I => if StrictMono I then α (fun i => e (I i)) else 0
      map_add' := fun α β => by
        ext I
        simp only [ContinuousAlternatingMap.add_apply, PiLp.add_apply]
        split_ifs <;> simp
      map_smul' := fun a α => by
        ext I
        simp only [ContinuousAlternatingMap.smul_apply, PiLp.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  have hc : ∀ α, covectorEuclideanNorm α = ‖c α‖ := by
    intro α
    rw [← Real.sqrt_sq (norm_nonneg (c α)), EuclideanSpace.real_norm_sq_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [c, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> simp [e]
  -- `|α| ≤ C ‖α‖`, since each coefficient is bounded by the operator norm
  set C : ℝ := √(Fintype.card (Fin n → Fin P)) + 1
  have hCpos : 0 < C := by positivity
  have hN3 : ∀ α, ‖c α‖ ≤ C * ‖α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    calc √(∑ I, ‖(c α) I‖ ^ 2) ≤ √(∑ _I : Fin n → Fin P, ‖α‖ ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun I _ => ?_)
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          simp only [c, LinearMap.coe_mk, AddHom.coe_mk]
          split_ifs
          · calc ‖α (fun i => e (I i))‖ ≤ ‖α‖ * ∏ i, ‖e (I i)‖ := α.le_opNorm _
              _ = ‖α‖ := by
                rw [Finset.prod_eq_one (fun i _ => e.orthonormal.norm_eq_one (I i)), mul_one]
          · simp
      _ = √(Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
            Real.sqrt_sq (norm_nonneg _)]
      _ ≤ C * ‖α‖ := by
          gcongr
          linarith
  have hcc : Continuous c := AddMonoidHomClass.continuous_of_bound c C hN3
  have hNc : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simp only [hc]
    exact hcc.norm
  have hNtri : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_add]
    exact norm_add_le _ _
  have hNsmul : ∀ (r : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (r • α) = |r| * covectorEuclideanNorm α := by
    intro r α
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- truncation `v ↦ v / max(1, |v|)` moves `v` by at most `|v - w|` towards any `|w| ≤ 1`
  have htrunc : ∀ v w : Covector (Euclid P) n, covectorEuclideanNorm w ≤ 1 →
      covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v - w) ≤
        2 * covectorEuclideanNorm (v - w) := by
    intro v w hw
    rcases le_total (covectorEuclideanNorm v) 1 with hv | hv
    · rw [max_eq_left hv, inv_one, one_smul]
      linarith [covectorEuclideanNorm_nonneg (v - w)]
    · rw [max_eq_right hv]
      have hvpos : 0 < covectorEuclideanNorm v := one_pos.trans_le hv
      have e1 : covectorEuclideanNorm ((covectorEuclideanNorm v)⁻¹ • v - v) =
          covectorEuclideanNorm v - 1 := by
        rw [show (covectorEuclideanNorm v)⁻¹ • v - v = ((covectorEuclideanNorm v)⁻¹ - 1) • v by
          module, hNsmul,
          abs_of_nonpos (sub_nonpos.2 (inv_le_one_of_one_le₀ hv)), neg_sub, sub_mul, one_mul,
          inv_mul_cancel₀ hvpos.ne']
      have e2 : covectorEuclideanNorm v ≤
          covectorEuclideanNorm (v - w) + covectorEuclideanNorm w := by
        calc covectorEuclideanNorm v = covectorEuclideanNorm ((v - w) + w) := by
              rw [sub_add_cancel]
          _ ≤ _ := hNtri _ _
      calc covectorEuclideanNorm ((covectorEuclideanNorm v)⁻¹ • v - w)
          = covectorEuclideanNorm (((covectorEuclideanNorm v)⁻¹ • v - v) + (v - w)) := by
            rw [sub_add_sub_cancel]
        _ ≤ _ := hNtri _ _
        _ ≤ 2 * covectorEuclideanNorm (v - w) := by rw [e1]; linarith
  -- good points: `ξ(x)` is a unit orientation of the approximate tangent plane
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      (∀ α, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
      covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 ∧
      ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    obtain ⟨h1, h2, h3⟩ := hL _ Q hQ
    exact ⟨h1, h2, h3, (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2⟩
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgoodμ := hac.ae_le hgood
  -- `T(ω) = ∫ ⟨ω, ξ⟩ dμ` for `μ = θ Hⁿ⌞M`
  have hθ : Measurable fun x => (R.mult x : NNReal) :=
    measurable_from_nat.comp R.measurable_mult
  have hT : ∀ ω : TestFormOn U n,
      T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
    intro ω
    rw [hRT ω, IMRep.action, IMRep.measure]
    have : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    rw [this, integral_withDensity_eq_integral_smul hθ]
    congr 1
  apply le_antisymm
  · -- upper bound: `T(ω) ≤ ∫ |ω| dμ ≤ μ(W)` for admissible `ω`
    apply sSup_le
    rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    dsimp only
    rw [hT ω]
    calc ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure)
        ≤ ‖∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂R.measure :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, W.indicator 1 x ∂R.measure := by
          apply lintegral_mono_ae
          filter_upwards [hgoodμ] with x hx
          by_cases hxW : x ∈ W
          · rw [indicator_of_mem hxW, Pi.one_apply, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.2 ((hx.1 _).trans (hω1 x))
          · have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
              image_eq_zero_of_notMem_tsupport fun h => hxW (hωW h)
            rw [this, map_zero, enorm_zero]
            exact zero_le
      _ = R.measure W := lintegral_indicator_one hW.measurableSet
  · -- lower bound on a compact `K ⊆ W`: an admissible `ω ≈ 1_K L(ξ)` with `T(ω) ≥ μ(K) - ε`
    have hcompact : ∀ K : Set (Euclid P), IsCompact K → K ⊆ W → R.measure K ≤ T.massOn W := by
      intro K hK hKW
      obtain ⟨δ₀, hδ₀, hδ₀W⟩ := hK.exists_cthickening_subset_open hW hKW
      have hKV : K ⊆ thickening δ₀ K := self_subset_thickening hδ₀ K
      have hμC : R.measure (cthickening δ₀ K) < ∞ := by
        rw [IMRep.measure, withDensity_apply _ isClosed_cthickening.measurableSet,
          Measure.restrict_restrict isClosed_cthickening.measurableSet, inter_comm]
        exact lt_top_iff_ne_top.2
          (R.locallyIntegrable_mult _ hK.cthickening (hδ₀W.trans hWU))
      have hμV : R.measure (thickening δ₀ K) < ∞ :=
        (measure_mono (thickening_subset_cthickening δ₀ K)).trans_lt hμC
      have hμK : R.measure K < ∞ := (measure_mono hKV).trans_lt hμV
      -- `ν = μ⌞V`, `V = K_{δ₀}`, is finite
      set V := thickening δ₀ K
      set ν := R.measure.restrict V with hν
      have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμV.ne
      have hgoodν := ae_restrict_of_ae (s := V) hgoodμ
      have hacν : ν ≪ μHE[n].restrict R.carrier :=
        (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).trans hac
      have hξν : AEStronglyMeasurable R.orient ν := R.aestronglyMeasurable_orient.mono_ac hacν
      have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
        isBoundedBilinearMap_apply.continuous
      have hevalm : ∀ v : Euclid P → Covector (Euclid P) n, AEStronglyMeasurable v ν →
          AEStronglyMeasurable (fun x => R.orient x (v x)) ν := fun v hv =>
        (hev.comp_aestronglyMeasurable (hξν.prodMk hv) :)
      -- the target `f = 1_K L(ξ)`: `|f| ≤ 1` and `ξ(f) = 1_K` a.e.
      set f : Euclid P → Covector (Euclid P) n := K.indicator fun x => L (R.orient x) with hf
      have hfm : AEStronglyMeasurable f ν :=
        (L.continuous.comp_aestronglyMeasurable hξν).indicator hK.measurableSet
      have hfi : Integrable f ν := by
        refine Integrable.of_bound hfm (max B 0) ?_
        filter_upwards [hgoodν] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK]
          exact (hB _ hx.2.2.2).trans (le_max_left _ _)
        · rw [hf, indicator_of_notMem hxK, norm_zero]
          exact le_max_right _ _
      have hf1 : ∀ᵐ x ∂ν, covectorEuclideanNorm (f x) ≤ 1 := by
        filter_upwards [hgoodν] with x hx
        by_cases hxK : x ∈ K
        · rw [hf, indicator_of_mem hxK]
          exact hx.2.1
        · rw [hf, indicator_of_notMem hxK, covectorEuclideanNorm_zero]
          exact zero_le_one
      have hfξi : Integrable (fun x => R.orient x (f x)) ν := by
        refine Integrable.of_bound (hevalm _ hfm) 1 ?_
        filter_upwards [hgoodν, hf1] with x hx hx1
        rw [Real.norm_eq_abs]
        exact (hx.1 _).trans hx1
      have hμKf : (R.measure K).toReal = ∫ x, R.orient x (f x) ∂ν := by
        have : (fun x => R.orient x (f x)) =ᵐ[ν] K.indicator 1 := by
          filter_upwards [hgoodν] with x hx
          by_cases hxK : x ∈ K
          · rw [hf, indicator_of_mem hxK, indicator_of_mem hxK, Pi.one_apply, hx.2.2.1]
          · rw [hf, indicator_of_notMem hxK, indicator_of_notMem hxK, map_zero]
        rw [integral_congr_ae this, integral_indicator_one hK.measurableSet, Measure.real, hν,
          Measure.restrict_apply hK.measurableSet, inter_eq_left.2 hKV]
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      -- tolerance `δ`
      set δ : ℝ := (ε : ℝ) / (4 * C * (ν.real univ + 1)) with hδ
      have hδpos : 0 < δ := by
        have : (0 : ℝ) < ε := hε
        positivity
      -- `g` continuous with compact support, `∫ ‖f - g‖ dν ≤ δ`
      obtain ⟨g, hgcs, hgf, hgc, hgi⟩ := hfi.exists_hasCompactSupport_integral_sub_le hδpos
      -- truncation `β = g / max(1, |g|)`, so `|β| ≤ 1`
      set β : Euclid P → Covector (Euclid P) n :=
        fun x => (max 1 (covectorEuclideanNorm (g x)))⁻¹ • g x with hβ
      have hmax : ∀ x, 0 < max 1 (covectorEuclideanNorm (g x)) :=
        fun x => one_pos.trans_le (le_max_left _ _)
      have hβc : Continuous β :=
        ((continuous_const.max (hNc.comp hgc)).inv₀ fun x => (hmax x).ne').smul hgc
      have hβs : HasCompactSupport β := hgcs.mono fun x hx hgx => hx (by
        rw [hβ]
        dsimp only
        rw [hgx, smul_zero])
      have hβ1 : ∀ x, covectorEuclideanNorm (β x) ≤ 1 := by
        intro x
        rw [hβ]
        dsimp only
        rw [hNsmul, abs_of_pos (inv_pos.2 (hmax x)), inv_mul_le_iff₀ (hmax x), mul_one]
        exact le_max_right _ _
      have hβg : ∀ x, covectorEuclideanNorm (β x) ≤ covectorEuclideanNorm (g x) := by
        intro x
        rw [hβ]
        dsimp only
        rw [hNsmul, abs_of_pos (inv_pos.2 (hmax x)), inv_mul_le_iff₀ (hmax x)]
        exact le_mul_of_one_le_left (covectorEuclideanNorm_nonneg _) (le_max_left _ _)
      -- smoothing: `h` smooth, `‖h - β‖ < δ`
      obtain ⟨h, hhs, hhβ⟩ :=
        (hβs.uniformContinuous_of_continuous hβc).exists_contDiff_dist_le hδpos
      have hhβE : ∀ x, covectorEuclideanNorm (h x - β x) ≤ C * δ := by
        intro x
        rw [hc]
        refine (hN3 _).trans (mul_le_mul_of_nonneg_left ?_ hCpos.le)
        rw [← dist_eq_norm]
        exact (hhβ x).le
      -- cutoff `χ ∈ C^∞`, `0 ≤ χ ≤ 1`, `support χ = V`, `χ = 1` on `K`
      obtain ⟨χ, hχs, hχr, hχsupp, hχ1⟩ :=
        exists_contDiff_support_eq_eq_one_iff (n := ⊤) isOpen_thickening hK.isClosed hKV
      have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x => hχr (mem_range_self x)
      have hχ0 : ∀ x, x ∉ V → χ x = 0 := fun x hx => by
        rw [← Function.notMem_support, hχsupp]
        exact hx
      -- the form `ω = a χ h`, `a = (1 + Cδ)⁻¹`
      set a : ℝ := (1 + C * δ)⁻¹ with ha
      have hCδ : 0 < C * δ := mul_pos hCpos hδpos
      have haC : a * (1 + C * δ) = 1 := inv_mul_cancel₀ (by positivity)
      have hapos : 0 < a := inv_pos.2 (by positivity)
      have ha1 : a ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      set ω₀ : DifferentialForm (Euclid P) n := fun x => (a * χ x) • h x with hω₀
      have hω₀0 : ∀ x, x ∉ V → ω₀ x = 0 := fun x hx => by
        rw [hω₀]
        dsimp only
        rw [hχ0 x hx, mul_zero, zero_smul]
      have hω₀s : IsSmoothForm ω₀ := (contDiff_const.mul hχs).smul hhs
      have hω₀c : HasCompactSupport ω₀ :=
        HasCompactSupport.intro hK.cthickening fun x hx =>
          hω₀0 x fun hxV => hx (thickening_subset_cthickening δ₀ K hxV)
      have hω₀W : tsupport ω₀ ⊆ W := by
        refine (closure_minimal (fun x hx => ?_) isClosed_cthickening).trans hδ₀W
        by_contra hxC
        exact hx (hω₀0 x fun hxV => hxC (thickening_subset_cthickening δ₀ K hxV))
      have hω₀1 : ∀ x, covectorEuclideanNorm (ω₀ x) ≤ 1 := by
        intro x
        rw [hω₀]
        dsimp only
        rw [hNsmul, abs_of_nonneg (mul_nonneg hapos.le (hχ01 x).1)]
        have hhx : covectorEuclideanNorm (h x) ≤ 1 + C * δ := by
          calc covectorEuclideanNorm (h x) = covectorEuclideanNorm (β x + (h x - β x)) := by
                rw [add_sub_cancel]
            _ ≤ _ := hNtri _ _
            _ ≤ 1 + C * δ := add_le_add (hβ1 x) (hhβE x)
        calc a * χ x * covectorEuclideanNorm (h x) ≤ a * 1 * (1 + C * δ) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hχ01 x).2 hapos.le) hhx
                (covectorEuclideanNorm_nonneg _) (by rw [mul_one]; exact hapos.le)
          _ = 1 := by rw [mul_one, haC]
      let ω : TestFormOn U n := ⟨ω₀, ⟨hω₀s, hω₀c⟩, hω₀W.trans hWU⟩
      have hωadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀W, hω₀1⟩
      -- `T(ω) = ∫ ξ(ω) dν`
      have hTω : T ω = ∫ x, R.orient x (ω₀ x) ∂ν := by
        rw [hT ω, hν, setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro x hx
        change R.orient x (ω₀ x) = 0
        rw [hω₀0 x hx, map_zero]
      have hω₀i : Integrable (fun x => R.orient x (ω₀ x)) ν := by
        refine Integrable.of_bound (hevalm _ hω₀s.continuous.aestronglyMeasurable) 1 ?_
        filter_upwards [hgoodν] with x hx
        rw [Real.norm_eq_abs]
        exact (hx.1 _).trans (hω₀1 x)
      -- pointwise: `|ξ(ω - f)| ≤ |ω - f| ≤ 2Cδ + 2C‖f - g‖`
      have hpt : ∀ᵐ x ∂ν, ‖R.orient x (ω₀ x) - R.orient x (f x)‖ ≤
          2 * C * δ + 2 * C * ‖f x - g x‖ := by
        filter_upwards [hgoodν, hf1] with x hx hx1
        rw [← map_sub, Real.norm_eq_abs]
        refine (hx.1 _).trans ?_
        have h1 : covectorEuclideanNorm (ω₀ x - χ x • β x) ≤ 2 * C * δ := by
          have e : ω₀ x - χ x • β x = χ x • (a • (h x - β x) + (-(1 - a)) • β x) := by
            rw [hω₀]
            dsimp only
            module
          rw [e, hNsmul, abs_of_nonneg (hχ01 x).1]
          have e2 : covectorEuclideanNorm (a • (h x - β x) + (-(1 - a)) • β x) ≤
              a * (C * δ) + (1 - a) * 1 := by
            refine (hNtri _ _).trans ?_
            rw [hNsmul, hNsmul, abs_of_pos hapos, abs_neg, abs_of_nonneg (sub_nonneg.2 ha1)]
            exact add_le_add (mul_le_mul_of_nonneg_left (hhβE x) hapos.le)
              (mul_le_mul_of_nonneg_left (hβ1 x) (sub_nonneg.2 ha1))
          calc χ x * covectorEuclideanNorm (a • (h x - β x) + (-(1 - a)) • β x)
              ≤ 1 * (a * (C * δ) + (1 - a) * 1) :=
                mul_le_mul (hχ01 x).2 e2 (covectorEuclideanNorm_nonneg _) zero_le_one
            _ ≤ 2 * C * δ := by
                have h1a : 1 - a = a * (C * δ) := by
                  rw [mul_add, mul_one] at haC
                  linarith
                have h2a : a * (C * δ) ≤ C * δ := mul_le_of_le_one_left hCδ.le ha1
                rw [h1a]
                linarith
        have h2 : covectorEuclideanNorm (χ x • β x - f x) ≤ 2 * C * ‖f x - g x‖ := by
          have hgfE : covectorEuclideanNorm (g x - f x) ≤ C * ‖f x - g x‖ := by
            rw [hc, norm_sub_rev (f x)]
            exact hN3 _
          by_cases hxK : x ∈ K
          · rw [(hχ1 x).1 hxK, one_smul]
            refine (htrunc (g x) (f x) hx1).trans ?_
            linarith
          · have hfx : f x = 0 := by rw [hf, indicator_of_notMem hxK]
            rw [show χ x • β x - f x = χ x • β x by rw [hfx, sub_zero], hNsmul,
              abs_of_nonneg (hχ01 x).1]
            have hgf0 : covectorEuclideanNorm (g x) ≤ C * ‖f x - g x‖ := by
              rw [hfx, zero_sub, norm_neg, hc]
              exact hN3 _
            have hn : 0 ≤ C * ‖f x - g x‖ := by positivity
            calc χ x * covectorEuclideanNorm (β x) ≤ 1 * covectorEuclideanNorm (g x) := by
                  gcongr
                  · exact covectorEuclideanNorm_nonneg _
                  · exact (hχ01 x).2
                  · exact hβg x
              _ ≤ 2 * C * ‖f x - g x‖ := by linarith
        calc covectorEuclideanNorm (ω₀ x - f x)
            = covectorEuclideanNorm ((ω₀ x - χ x • β x) + (χ x • β x - f x)) := by
              rw [sub_add_sub_cancel]
          _ ≤ _ := hNtri _ _
          _ ≤ 2 * C * δ + 2 * C * ‖f x - g x‖ := add_le_add h1 h2
      -- integrate: `|T(ω) - μ(K)| ≤ 2Cδ ν(V) + 2Cδ = ε/2`
      have hfgi : Integrable (fun x => ‖f x - g x‖) ν := (hfi.sub hgi).norm
      have hbi : Integrable (fun x => 2 * C * δ + 2 * C * ‖f x - g x‖) ν :=
        (integrable_const _).add (hfgi.const_mul _)
      have hest : |T ω - (R.measure K).toReal| ≤ ε / 2 := by
        rw [hTω, hμKf, ← integral_sub hω₀i hfξi, ← Real.norm_eq_abs]
        refine (norm_integral_le_of_norm_le hbi hpt).trans ?_
        rw [integral_add (integrable_const _) (hfgi.const_mul _), integral_const,
          integral_const_mul, smul_eq_mul]
        have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
        calc ν.real univ * (2 * C * δ) + 2 * C * ∫ x, ‖f x - g x‖ ∂ν
            ≤ ν.real univ * (2 * C * δ) + 2 * C * δ := by gcongr
          _ = 2 * C * δ * (ν.real univ + 1) := by ring
          _ = ε / 2 := by
            rw [hδ]
            field_simp
            ring
      have hTω' : (R.measure K).toReal ≤ T ω + ε := by
        have := (abs_le.1 hest).1
        have : (0 : ℝ) ≤ ε := ε.coe_nonneg
        linarith
      calc R.measure K = ENNReal.ofReal (R.measure K).toReal :=
            (ENNReal.ofReal_toReal hμK.ne).symm
        _ ≤ ENNReal.ofReal (T ω + ε) := ENNReal.ofReal_le_ofReal hTω'
        _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ = ENNReal.ofReal (T ω) + ε := by rw [ENNReal.ofReal_coe_nnreal]
        _ ≤ T.massOn W + ε := by gcongr; exact T.le_massOn hωadm
    -- exhaust `W` by the increasing compact sets `F m ∩ B̄_m(0)`
    obtain ⟨F, hFc, hFW, hFU, hFm⟩ := hW.exists_iUnion_isClosed
    have hKm : Monotone fun m : ℕ => F m ∩ closedBall (0 : Euclid P) m := fun a b hab =>
      inter_subset_inter (hFm hab) (closedBall_subset_closedBall (Nat.cast_le.2 hab))
    have hKU : ⋃ m : ℕ, F m ∩ closedBall (0 : Euclid P) m = W := by
      refine Subset.antisymm (iUnion_subset fun m => inter_subset_left.trans (hFW m))
        fun x hx => ?_
      rw [← hFU] at hx
      obtain ⟨a, ha⟩ := mem_iUnion.1 hx
      obtain ⟨b, hb⟩ := exists_nat_ge (dist x 0)
      exact mem_iUnion.2 ⟨max a b, hFm (le_max_left a b) ha,
        mem_closedBall.2 (hb.trans (Nat.cast_le.2 (le_max_right a b)))⟩
    calc R.measure W = R.measure (⋃ m : ℕ, F m ∩ closedBall (0 : Euclid P) m) := by rw [hKU]
      _ = ⨆ m : ℕ, R.measure (F m ∩ closedBall (0 : Euclid P) m) := hKm.measure_iUnion
      _ ≤ T.massOn W := iSup_le fun m => hcompact _
          ((isCompact_closedBall 0 m).inter_left (hFc m)) (inter_subset_left.trans (hFW m))
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
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion

/-- **Compactly supported C¹ perturbation of the identity** (the cut-off `ζ` of Simon Ch. 6, 2.23,
applied to `f − id`).  Let `O ⊆ ℝᴾ` be open, `K ⊆ O` compact and `f` of class C¹ on `O`.  Choose
`ρ > 0` with `cthickening ρ K ⊆ O` and, by the smooth Urysohn lemma, a smooth `χ : ℝᴾ → [0, 1]`
with `support χ = thickening ρ K` and `χ = 1` on `cthickening (ρ/2) K`.  Then
`φ = id + χ • (f − id)` is C¹ (it is C¹ at points of `O`, and equals `id` near points off
`K' = tsupport χ ⊆ cthickening ρ K ⊆ O`), `K'` is compact, `φ = id` off `K'`, and `φ = f` on the
open `V = thickening (ρ/2) K ⊇ K`, so `φ x = f x` and `Dφ(x) = Df(x)` for `x ∈ V`. -/
theorem Submission.dtc_bc_lc_pf_c1_compact_perturbation : ∀ (P : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → IsCompact K → K ⊆ O → ContDiffOn ℝ 1 f O → ∃ (φ : Euclid P → Euclid P) (V K' : Set (Euclid P)), IsOpen V ∧ K ⊆ V ∧ IsCompact K' ∧ ContDiff ℝ 1 φ ∧ (∀ x ∈ V, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x) ∧ ∀ x, x ∉ K' → φ x = x := by
  intro P O K f hO hK hKO hf
  -- Step 1: a margin `ρ > 0` with `cthickening ρ K ⊆ O`
  obtain ⟨ρ, hρ, hρO⟩ := hK.exists_cthickening_subset_open hO hKO
  -- Step 2: a smooth cut-off `χ` with `support χ = thickening ρ K`, `χ = 1` on `cthickening (ρ/2) K`
  obtain ⟨χ, hχ, -, hχs, hχt⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
    (isOpen_thickening : IsOpen (thickening ρ K))
    (isClosed_cthickening : IsClosed (cthickening (ρ / 2) K))
    (cthickening_subset_thickening' hρ (half_lt_self hρ) K)
  have hχ1 : ContDiff ℝ 1 χ := by exact_mod_cast hχ
  -- `K' := tsupport χ ⊆ cthickening ρ K ⊆ O` is compact
  have hK'sub : tsupport χ ⊆ cthickening ρ K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening ρ K
  have hK'O : tsupport χ ⊆ O := hK'sub.trans hρO
  have hK'cpt : IsCompact (tsupport χ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport χ) hK'sub
  -- Step 3: the perturbation `φ = id + χ • (f - id)`, with `V = thickening (ρ/2) K`
  refine ⟨fun x => x + χ x • (f x - x), thickening (ρ / 2) K, tsupport χ, isOpen_thickening,
    self_subset_thickening (half_pos hρ) K, hK'cpt, ?_, ?_, ?_⟩
  · -- Step 4: `φ` is C¹ at points of `O` (as `f` is) and near points off `tsupport χ` (`φ = id`)
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ O
    · have hfx : ContDiffAt ℝ 1 f x := hf.contDiffAt (hO.mem_nhds hx)
      exact contDiffAt_id.add (hχ1.contDiffAt.smul (hfx.sub contDiffAt_id))
    · have hx' : x ∉ tsupport χ := fun h => hx (hK'O h)
      have hev : (fun y => y + χ y • (f y - y)) =ᶠ[𝓝 x] id := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
        simp [hy]
      exact contDiffAt_id.congr_of_eventuallyEq hev
  · -- Step 5: `χ = 1` on the open set `V`, so `φ = f` near each `x ∈ V`
    intro x hx
    have hev : (fun y => y + χ y • (f y - y)) =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_thickening.mem_nhds hx] with y hy
      have hy1 : χ y = 1 := (hχt y).1 (thickening_subset_cthickening _ _ hy)
      simp [hy1]
    exact ⟨hev.eq_of_nhds, hev.fderiv_eq⟩
  · -- Step 6: `χ = 0` off `tsupport χ`, so `φ = id` there
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
/-- The derivative bound behind Simon 6.2.24(2)–(3) (push-forward by a `C¹` map): if `φ` is `C¹`
on `ℝᴾ` and `φ(x) = x` off a compact set `K`, then `‖Dφ(x)‖ ≤ Λ` for some `Λ ≥ 0` and all `x`.
`Dφ` is continuous, hence bounded by some `c` on `K`; off the closed set `K`, `φ = id` near `x`,
so `Dφ(x) = id` has norm `≤ 1`.  Take `Λ = max(1, c)`. -/
theorem Submission.dpf_pfc_fderiv_norm_le_of_eq_id_off_compact : ∀ (P : ℕ) (K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsCompact K → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x, ‖fderiv ℝ φ x‖ ≤ Λ := by
  intro P K φ hK hφ hid
  -- `Dφ` is continuous, so it is bounded by some `c` on the compact set `K`
  obtain ⟨c, hc⟩ := hK.exists_bound_of_continuousOn (hφ.continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max 1 c, zero_le_one.trans (le_max_left _ _), fun x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hc x hx).trans (le_max_right _ _)
  · -- off the closed set `K`, `φ = id` near `x`, so `Dφ(x) = id` has norm `≤ 1`
    have h : φ =ᶠ[𝓝 x] id := eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hx) hid
    rw [h.fderiv_eq, fderiv_id]
    exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
/-- Simon 6.3.1: `Hⁿ`-a.e. on `M` the orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` of an integer
multiplicity triple is a unit simple `n`-vector (`τ` orthonormal), so every `n`-covector `β`
satisfies `|⟨β, ξ(x)⟩| = |β(τ₁, …, τₙ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖` (operator norm). -/
theorem Submission.dpf_pfc_imrep_orient_abs_apply_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ β : Covector (Euclid P) n, |R.orient x β| ≤ ‖β‖ := by
  intro P n U R
  filter_upwards [R.orients] with x hx β
  -- `ξ(x)` is `±` evaluation at an orthonormal frame `τ`
  obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
  have hβ : |β τ| ≤ ‖β‖ :=
    calc |β τ| = ‖β τ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖β‖ * ∏ i, ‖τ i‖ := β.le_opNorm τ
      _ = ‖β‖ := by rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one]
  rcases hξ with h | h
  · rw [h β]
    exact hβ
  · rw [h β, abs_neg]
    exact hβ

/-- **Pairing bound for `τ(M, θ, ξ)`** (the estimate behind Simon 6.2.24(2)).  If `F` is
`Hⁿ⌞M`-a.e. strongly measurable, vanishes off the compact `C ⊆ U` and `‖F‖ ≤ B`, then
`θ ⟨F, ξ⟩` is `Hⁿ⌞M`-integrable and `|∫_M θ ⟨F, ξ⟩ dHⁿ| ≤ B ∫_{M ∩ C} θ dHⁿ`.  By
`dpf_pfc_imrep_orient_abs_apply_le`, `|θ ⟨F, ξ⟩| ≤ B θ 1_C` a.e., and `θ 1_C` is integrable by
the local integrability of `θ`. -/
theorem Submission.dpf_pfc_imrep_pairing_integrable_abs_le : ∀ (P n : ℕ) (U C : Set (Euclid P)) (R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact C → C ⊆ U → AEStronglyMeasurable F (μHE[n].restrict R.carrier) → (∀ x, x ∉ C → F x = 0) → (∀ x, ‖F x‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x (F x)) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n]| ≤ B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U C R F B hC hCU hF hF0 hFB
  -- Step 1: `C` is measurable; step 2: `θ` is measurable
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
  -- Step 3: `μ.restrict C = Hⁿ⌞(M ∩ C)`
  have hres : (μHE[n].restrict R.carrier).restrict C = μHE[n].restrict (R.carrier ∩ C) := by
    rw [Measure.restrict_restrict hCm, inter_comm]
  -- Step 4: `θ` is integrable on `C`, so `g = B · 1_C θ` is integrable
  have hθC : IntegrableOn (fun x => (R.mult x : ℝ)) C (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hres]
    simpa using (R.locallyIntegrable_mult C hC hCU).lt_top
  have hg : Integrable (fun x => B * C.indicator (fun y => (R.mult y : ℝ)) x)
      (μHE[n].restrict R.carrier) :=
    ((integrable_indicator_iff hCm).2 hθC).const_mul B
  -- Step 5: `h = θ · ξ(F)` is a.e. strongly measurable
  have hh : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (F x))
      (μHE[n].restrict R.carrier) :=
    hθm.aestronglyMeasurable.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      R.aestronglyMeasurable_orient hF)
  -- Step 6: `|h| ≤ g` a.e., by `orient_bound`
  have hdom : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (F x)‖ ≤ B * C.indicator (fun y => (R.mult y : ℝ)) x := by
    filter_upwards [Submission.dpf_pfc_imrep_orient_abs_apply_le P n U R] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (F x)).trans (hFB x)) (Nat.cast_nonneg _)
    · simp [indicator_of_notMem hxC, hF0 x hxC]
  -- Step 7: integrability
  refine ⟨hg.mono' hh hdom, ?_⟩
  -- Step 8: `∫ g dμ = B · (∫⁻_{M ∩ C} θ dHⁿ).toReal`
  have hgval : ∫ x, B * C.indicator (fun y => (R.mult y : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_const_mul, integral_indicator hCm, hres,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Nat.cast_nonneg _)
        hθm.aestronglyMeasurable]
    simp
  -- Step 9: `|∫ h dμ| ≤ ∫ g dμ`
  rw [← Real.norm_eq_abs, ← hgval]
  exact norm_integral_le_of_norm_le hg hdom
/-- **Simon §6.1** (the test-form topology, the case `β = 0`): if `ωⱼ → 0` in `𝒟ⁿ(U)`, the
`ωⱼ` vanish outside one compact `C ⊆ U`, and `supₓ ‖ωⱼ(x)‖ → 0`.  The compact set is the one in
`TestFormOnConverges`; uniform convergence of the `0`-th iterated derivatives on `C` gives the
bound on `C`, and `ωⱼ = 0` off `C`. -/
theorem Submission.dpf_pfc_testFormOnConverges_zero_uniform : ∀ (P n : ℕ) (U : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), TestFormOnConverges ωs 0 → ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ U ∧ (∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε := by
  intro P n U ωs h
  obtain ⟨C, hC, hCU, hsupp, -, hderiv⟩ := h
  have hzero : ∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')
  refine ⟨C, hC, hCU, hzero, fun ε hε => ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ C
  · have hjx := hj x hx
    simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
      norm_iteratedFDeriv_zero] at hjx
    exact hjx.le
  · rw [hzero j x hx, norm_zero]
    exact hε.le

/-- **Simon 6.2.23–2.24 (2)–(3)** (chapter-06.txt lines 403–440): for a triple `R = (M, θ, ξ)` in
`U` and a `C¹` map `φ` equal to the identity off a compact `K ⊆ U`, the push-forward formula
`ω ↦ ∫_M θ(x) ⟨ω(φ(x)) ∘ Dφ(x), ξ(x)⟩ dHⁿ(x)` defines a current in `U`.  With `‖Dφ‖ ≤ Λ`, the
covector field `F_ω(x) = ω(φ(x)) ∘ Dφ(x)` is continuous, vanishes off the compact set
`tsupport ω ∪ K ⊆ U` and has `‖F_ω‖ ≤ sup ‖ω‖ · Λⁿ`; this gives integrability, hence linearity.
If `ωⱼ → 0`, then `F_{ωⱼ}` vanishes off a fixed compact `C ∪ K` and is eventually bounded by
`η Λⁿ`, which gives sequential continuity. -/
theorem Submission.dpf_pushforward_formula_current_exists : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (φ : Euclid P → Euclid P), IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] := by
  intro P n U K R φ hK hKU hφ hid
  -- step 1: `‖Dφ(x)‖ ≤ Λ` for every `x`
  obtain ⟨Λ, hΛ0, hΛ⟩ := Submission.dpf_pfc_fderiv_norm_le_of_eq_id_off_compact P K φ hK hφ hid
  -- the pulled-back covector field `F ω x = ω(φ(x)) ∘ Dφ(x)`
  set F : DifferentialForm (Euclid P) n → Euclid P → Covector (Euclid P) n :=
    fun ω x => (ω (φ x)).compContinuousLinearMap (fderiv ℝ φ x) with hFdef
  have hFcont : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω → Continuous (F ω) := by
    intro ω hω
    have h := (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM (𝕜 := ℝ)
      (ι := Fin n) (G := ℝ) |>.comp (hφ.continuous_fderiv one_ne_zero)).clm_apply
      (hω.comp hφ.continuous)
    simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
      using h
  -- step 2: `‖F ω‖ ≤ B Λⁿ` when `‖ω‖ ≤ B`
  have hFnorm : ∀ (ω : DifferentialForm (Euclid P) n) (B : ℝ), (∀ y, ‖ω y‖ ≤ B) →
      ∀ x, ‖F ω x‖ ≤ B * Λ ^ n := by
    intro ω B hB x
    calc ‖F ω x‖ ≤ ‖ω (φ x)‖ * ‖fderiv ℝ φ x‖ ^ n := by
          simpa only [Fintype.card_fin] using
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le (ω (φ x)) (fderiv ℝ φ x)
      _ ≤ B * Λ ^ n := mul_le_mul (hB _) (pow_le_pow_left₀ (norm_nonneg _) (hΛ x) n)
          (pow_nonneg (norm_nonneg _) n) ((norm_nonneg _).trans (hB (φ x)))
  -- step 3: `F ω` vanishes off `C ∪ K` when `ω` vanishes off `C`
  have hFzero : ∀ (ω : DifferentialForm (Euclid P) n) (C : Set (Euclid P)),
      (∀ y, y ∉ C → ω y = 0) → ∀ x, x ∉ C ∪ K → F ω x = 0 := by
    intro ω C hC x hx
    rw [mem_union, not_or] at hx
    ext v
    simp [hFdef, hid x hx.2, hC x hx.1]
  -- `F ω x` is linear in `ω`
  have hFadd : ∀ (ω₁ ω₂ : DifferentialForm (Euclid P) n) x, F (ω₁ + ω₂) x = F ω₁ x + F ω₂ x := by
    intro ω₁ ω₂ x
    ext v
    simp [hFdef]
  have hFsmul : ∀ (c : ℝ) (ω : DifferentialForm (Euclid P) n) x, F (c • ω) x = c • F ω x := by
    intro c ω x
    ext v
    simp [hFdef]
  -- step 4: the integrand of a test form is integrable
  have hint : ∀ ω : TestFormOn U n, Integrable
      (fun x => (R.mult x : ℝ) * R.orient x (F (ω : DifferentialForm (Euclid P) n) x))
      (μHE[n].restrict R.carrier) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous ω.property.1.1
    obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
    exact (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U
      (tsupport (ω : DifferentialForm (Euclid P) n) ∪ K) R (F ω) (B * Λ ^ n)
      (ω.property.1.2.isCompact.union hK) (union_subset ω.property.2 hKU)
      (hFcont _ hωc).aestronglyMeasurable
      (hFzero _ _ fun y hy => image_eq_zero_of_notMem_tsupport hy) (hFnorm _ _ hB)).1
  -- step 5: the action is linear
  let S₀ : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω =>
        ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F (ω : DifferentialForm (Euclid P) n) x)
          ∂μHE[n]
      map_add' := fun ω₁ ω₂ => by
        rw [← integral_add (hint ω₁) (hint ω₂)]
        congr 1
        ext x
        rw [Submodule.coe_add, hFadd, map_add, mul_add]
      map_smul' := fun c ω => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        ext x
        rw [Submodule.coe_smul, hFsmul, map_smul, smul_eq_mul, mul_left_comm] }
  -- steps 6–7: sequential continuity, and the action is the push-forward formula by definition
  refine ⟨⟨S₀, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  obtain ⟨C, hC, hCU, hCzero, hsmall⟩ :=
    Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
  set I : ℝ := (∫⁻ x in R.carrier ∩ (C ∪ K), (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal
  have hI : 0 ≤ Λ ^ n * I := mul_nonneg (pow_nonneg hΛ0 n) ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη : 0 < ε / (Λ ^ n * I + 1) := div_pos hε (by linarith)
  filter_upwards [hsmall _ hη] with j hj
  have hb := (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n U (C ∪ K) R
    (F (ωs j : DifferentialForm (Euclid P) n)) (ε / (Λ ^ n * I + 1) * Λ ^ n) (hC.union hK)
    (union_subset hCU hKU)
    (hFcont _ (ContDiff.continuous (ωs j).property.1.1)).aestronglyMeasurable
    (hFzero _ _ (hCzero j)) (hFnorm _ _ hj)).2
  rw [Real.dist_eq, sub_zero]
  calc |S₀ (ωs j)| ≤ ε / (Λ ^ n * I + 1) * Λ ^ n * I := hb
    _ = ε * (Λ ^ n * I / (Λ ^ n * I + 1)) := by ring
    _ < ε := mul_lt_of_lt_one_right hε ((div_lt_one (by linarith)).2 (lt_add_one _))
/-- **Pull-back of a test form by a compactly supported perturbation of the identity**
(Simon 6.2.23–6.2.24).  Let `K'` be compact and `ψ` a `C^∞` map with `ψ = id` off `K'`.  For a
test form `α ∈ 𝒟ᵈ`, the pull-back `ψ^#α(x) = α(ψ(x)) ∘ Dψ(x)` is a test form with
`spt ψ^#α ⊆ spt α ∪ K'`.  It is `C^∞` as `ψ^#α(x) = Φ(Dψ(x))(α(ψ(x)))`, where the precomposition
`Φ(L) = (γ ↦ γ ∘ L)` is analytic in `L`.  Off the closed compact set `spt α ∪ K'` we have
`ψ(z) = z` and `α(z) = 0`, so `ψ^#α(z) = 0`. -/
theorem Submission.dpf_pb_smooth_pullback_isTestForm : ∀ (P d : ℕ) (K' : Set (Euclid P)) (ψ : Euclid P → Euclid P) (α : DifferentialForm (Euclid P) d), IsCompact K' → ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ x, x ∉ K' → ψ x = x) → IsTestForm α → IsTestForm (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ∧ tsupport (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ⊆ tsupport α ∪ K' := by
  intro P d K' ψ α hK hψ hfix hα
  -- `α` is `C^∞` with compact support
  obtain ⟨hαs, hαc⟩ := hα
  -- the precomposition `Φ(L) = (γ ↦ γ ∘ L)` on `d`-covectors is analytic, hence `C^∞`
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (Euclid P →L[ℝ] Euclid P) →
        (Euclid P [⋀^Fin d]→L[ℝ] ℝ) →L[ℝ] (Euclid P [⋀^Fin d]→L[ℝ] ℝ)) :=
    (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
  -- `Dψ` and `α ∘ ψ` are `C^∞`, so `ψ^#α = Φ(Dψ)(α ∘ ψ)` is `C^∞`
  have hDψ : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ ψ) := (contDiff_infty_iff_fderiv.mp hψ).2
  have hαψ : ContDiff ℝ (⊤ : ℕ∞) (fun x => α (ψ x)) := hαs.comp hψ
  have hsmooth : IsSmoothForm (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) :=
    (hΦ.comp hDψ).clm_apply hαψ
  -- off the closed set `spt α ∪ K'`, `ψ(z) = z` and `α(z) = 0`, so `ψ^#α(z) = 0`
  have hsupp : tsupport (fun x => (α (ψ x)).compContinuousLinearMap (fderiv ℝ ψ x)) ⊆
      tsupport α ∪ K' := by
    refine closure_minimal ?_ ((isClosed_tsupport α).union hK.isClosed)
    intro z hz
    by_contra hzF
    rw [mem_union, not_or] at hzF
    refine Function.mem_support.mp hz ?_
    show (α (ψ z)).compContinuousLinearMap (fderiv ℝ ψ z) = 0
    rw [hfix z hzF.2, image_eq_zero_of_notMem_tsupport hzF.1]
    ext v
    simp
  -- `spt ψ^#α` is a closed subset of the compact set `spt α ∪ K'`
  exact ⟨⟨hsmooth, (IsCompact.union hαc hK).of_isClosed_subset (isClosed_tsupport _) hsupp⟩,
    hsupp⟩
/-- **Dominated convergence for pulled-back integrals** (Simon 6.2.23–6.2.24, the limit step in the
push-forward by a `C¹` map).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in `U`, `α` a
continuous `n`-form with compact support in `U`, and `ψₖ` `C¹` maps equal to the identity off the
compact `K' ⊆ U`, with `‖Dψₖ‖ ≤ C`, `ψₖ → φ` and `Dψₖ → Dφ` pointwise.  Then
`∫_M θ ⟨α(ψₖ)∘Dψₖ, ξ⟩ dHⁿ → ∫_M θ ⟨α(φ)∘Dφ, ξ⟩ dHⁿ`: the integrands are dominated by
`A Cⁿ θ 1_{spt α ∪ K'}` (`‖α‖ ≤ A`, `|ξ(γ)| ≤ ‖γ‖` a.e.), which is integrable since `θ` is locally
`Hⁿ⌞M`-integrable in `U`. -/
theorem Submission.dpf_pb_imrep_pullback_integral_tendsto : ∀ (P n : ℕ) (U K' : Set (Euclid P)) (R : IMRep U n) (α : DifferentialForm (Euclid P) n) (ψ : ℕ → Euclid P → Euclid P) (φ : Euclid P → Euclid P) (C : ℝ), IsCompact K' → K' ⊆ U → Continuous α → HasCompactSupport α → tsupport α ⊆ U → (∀ k, ContDiff ℝ 1 (ψ k)) → (∀ k x, x ∉ K' → ψ k x = x) → (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) → (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) → (∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((α (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n])) := by
  intro P n U K' R α ψ φ C hK' hK'U hα hαc hαU hψ hψid hψC hψφ hDψ
  -- `C₀ = spt α ∪ K'` is compact, closed (hence measurable) and contained in `U`
  have hC₀ : IsCompact (tsupport α ∪ K') := hαc.isCompact.union hK'
  have hC₀m : MeasurableSet (tsupport α ∪ K') := hC₀.isClosed.measurableSet
  -- `‖α‖ ≤ A` everywhere, so `0 ≤ A`
  obtain ⟨A, hA⟩ := hα.bounded_above_of_compact_support hαc
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- `θ` is measurable
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- orientation bound: `|ξ(x)(γ)| = |γ(τ)| ≤ ‖γ‖ ∏ ‖τᵢ‖ = ‖γ‖` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂μHE[n].restrict R.carrier, ∀ γ : Covector (Euclid P) n,
      |R.orient x γ| ≤ ‖γ‖ := by
    filter_upwards [R.orients] with x ⟨Q, _, τ, hτ, _, hor⟩ γ
    have hγ : |γ τ| ≤ ‖γ‖ := by
      have h := γ.le_opNorm τ
      simp only [hτ.1, Finset.prod_const_one, mul_one] at h
      rwa [Real.norm_eq_abs] at h
    rcases hor with h | h
    · rw [h γ]; exact hγ
    · rw [h γ, abs_neg]; exact hγ
  -- `x ↦ α(ψₖ(x))∘Dψₖ(x)` is continuous
  have hβ : ∀ k, Continuous fun x =>
      (α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x) := by
    intro k
    have h1 : Continuous fun x => (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ (ψ k) x) : Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n) :=
      ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
        ((hψ k).continuous_fderiv one_ne_zero)
    exact h1.clm_apply (hα.comp (hψ k).continuous)
  refine tendsto_integral_of_dominated_convergence
    ((tsupport α ∪ K').indicator fun x => A * C ^ n * (R.mult x : ℝ)) ?_ ?_ ?_ ?_
  · -- each integrand is a.e. strongly measurable
    intro k
    refine hθm.aestronglyMeasurable.mul ?_
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      isBoundedBilinearMap_apply.continuous
    exact Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P n) (v : Covector (Euclid P) n) => L v) hev
      R.aestronglyMeasurable_orient (hβ k).aestronglyMeasurable
  · -- the bound `A Cⁿ θ 1_{C₀}` is integrable, as `θ` is integrable on `M ∩ C₀`
    refine IntegrableOn.integrable_indicator ?_ hC₀m
    refine Integrable.const_mul ?_ _
    show Integrable _ ((μHE[n].restrict R.carrier).restrict (tsupport α ∪ K'))
    rw [Measure.restrict_restrict hC₀m, inter_comm]
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in R.carrier ∩ (tsupport α ∪ K'), ‖(R.mult x : ℝ)‖ₑ ∂μHE[n] < ∞
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult _ hC₀ (union_subset hαU hK'U))
  · -- domination `|hₖ| ≤ A Cⁿ θ 1_{C₀}` a.e.
    intro k
    filter_upwards [hξ] with x hx
    by_cases hxC : x ∈ tsupport α ∪ K'
    · rw [indicator_of_mem hxC]
      have hβle : ‖(α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)‖ ≤ A * C ^ n := by
        refine (ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _).trans ?_
        rw [Fintype.card_fin]
        exact mul_le_mul (hA _) (pow_le_pow_left₀ (norm_nonneg _) (hψC k x) n)
          (pow_nonneg (norm_nonneg _) n) hA0
      rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x))|
          ≤ (R.mult x : ℝ) * (A * C ^ n) :=
            mul_le_mul_of_nonneg_left ((hx _).trans hβle) (Nat.cast_nonneg _)
        _ = A * C ^ n * (R.mult x : ℝ) := mul_comm _ _
    · -- off `C₀`: `ψₖ(x) = x` and `α(x) = 0`, so the integrand vanishes
      rw [indicator_of_notMem hxC]
      have hxK : x ∉ K' := fun h => hxC (Or.inr h)
      have hxα : x ∉ tsupport α := fun h => hxC (Or.inl h)
      have h0 : (0 : Covector (Euclid P) n).compContinuousLinearMap (fderiv ℝ (ψ k) x) = 0 :=
        map_zero (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ (ψ k) x))
      rw [hψid k x hxK, image_eq_zero_of_notMem_tsupport hxα, h0, map_zero, mul_zero, norm_zero]
  · -- pointwise convergence, by continuity of `α`, of `L ↦ (· ∘ L)` and of evaluation
    refine Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.mul (((R.orient x).continuous.tendsto _).comp ?_)
    have h1 : Tendsto (fun k => (ContinuousAlternatingMap.compContinuousLinearMapCLM
        (fderiv ℝ (ψ k) x) : Covector (Euclid P) n →L[ℝ] Covector (Euclid P) n)) atTop
        (𝓝 (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ φ x))) :=
      (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.tendsto _).comp (hDψ x)
    have h2 : Tendsto (fun k => α (ψ k x)) atTop (𝓝 (α (φ x))) := (hα.tendsto _).comp (hψφ x)
    exact (isBoundedBilinearMap_apply.continuous.tendsto _).comp (h1.prodMk_nhds h2)
/-- Simon 6.2.24(1), reduction from `C¹` to smooth maps (step 3 of the push-forward proof): a `C¹`
map `φ` of `ℝᴾ` with `φ = id` off the compact set `K ⊆ U` is the pointwise `C¹` limit of `C^∞`
maps `ψₖ` that equal `id` off one compact `K' ⊆ U` and have uniformly bounded differentials.
`K' = cthickening δ K ⊆ U` and `ψₖ = id + ρₖ ⋆ (φ − id)`, `ρₖ` a normalized smooth bump supported
in `B_{δ/(k+2)}(0)`; then `Dψₖ = I + ρₖ ⋆ D(φ − id)`, so `‖Dψₖ‖ ≤ 1 + sup ‖D(φ − id)‖`, and the
mollifications of the continuous `φ − id` and `D(φ − id)` converge pointwise. -/
theorem Submission.dpf_smooth_approx_compact_perturbation : ∀ (P : ℕ) (U K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ (ψ : ℕ → Euclid P → Euclid P) (K' : Set (Euclid P)) (C : ℝ), IsCompact K' ∧ K' ⊆ U ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧ (∀ k x, x ∉ K' → ψ k x = x) ∧ (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) ∧ (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) ∧ ∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x)) := by
  intro P U K φ hU hK hKU hφ hfix
  -- Step 1: a margin `δ > 0` with `K' = cthickening δ K ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: the perturbation `g = φ - id` is `C¹` and vanishes off `K`; `‖Dg‖ ≤ A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → Euclid P, ∀ x, g x = φ x - x := ⟨fun x => φ x - x, fun _ => rfl⟩
  have hgφ : g = fun x => φ x - x := funext hg
  have hg1 : ContDiff ℝ 1 g := by
    rw [hgφ]
    exact hφ.sub contDiff_id
  have hgK : ∀ x, x ∉ K → g x = 0 := fun x hx => by rw [hg, hfix x hx, sub_self]
  have hgcs : HasCompactSupport g := HasCompactSupport.intro hK hgK
  have hgc : Continuous g := hg1.continuous
  have hDgc : Continuous (fderiv ℝ g) := hg1.continuous_fderiv one_ne_zero
  have hDg : ∀ x, fderiv ℝ g x = fderiv ℝ φ x - ContinuousLinearMap.id ℝ (Euclid P) := by
    intro x
    rw [hgφ]
    exact (((hφ.differentiable one_ne_zero) x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  obtain ⟨A, hA⟩ := hDgc.bounded_above_of_compact_support (hgcs.fderiv ℝ)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 3: nonnegative smooth `ρ k` with `∫ ρ k = 1`, supported in `ball 0 (r k)`, where
  -- `r k = δ / (k + 2)`: the bump `β k` with `rOut = r k`, divided by its integral
  obtain ⟨r, hr0, hrδ, hrlim⟩ : ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ (∀ k, r k ≤ δ) ∧
      Tendsto r atTop (𝓝 0) := by
    refine ⟨fun k => δ / ((k : ℝ) + 2), fun k => by positivity, fun k => ?_, ?_⟩
    · exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨ρ, hρs, hρn, hρi, hρsupp⟩ : ∃ ρ : ℕ → Euclid P → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k)) ∧ (∀ k x, 0 ≤ ρ k x) ∧ (∀ k, ∫ x, ρ k x = 1) ∧
      (∀ k, support (ρ k) ⊆ ball 0 (r k)) := by
    let β : ∀ k, ContDiffBump (0 : Euclid P) := fun k =>
      ⟨r k / 2, r k, half_pos (hr0 k), half_lt_self (hr0 k)⟩
    have hβi : ∀ k, 0 < ∫ x, β k x := fun k => by
      rw [integral_pos_iff_support_of_nonneg (fun x => (β k).nonneg)
        ((β k).continuous.integrable_of_hasCompactSupport (β k).hasCompactSupport),
        (β k).support_eq]
      exact measure_ball_pos _ _ (hr0 k)
    refine ⟨fun k x => (∫ y, β k y)⁻¹ * β k x, fun k => contDiff_const.mul (β k).contDiff,
      fun k x => mul_nonneg (inv_nonneg.2 (hβi k).le) (β k).nonneg, fun k => ?_,
      fun k x hx => ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ (hβi k).ne']
    · have hx' : x ∈ support (β k) := right_ne_zero_of_mul hx
      rwa [(β k).support_eq] at hx'
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall 0 (r k)) fun x hx =>
      notMem_support.1 fun h => hx (ball_subset_closedBall (hρsupp k h))
  have hρloc : ∀ k, LocallyIntegrable (ρ k) volume := fun k => (hρs k).continuous.locallyIntegrable
  have hsmall : Tendsto (fun k => support (ρ k)) atTop (𝓝 (0 : Euclid P)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [(tendsto_order.1 hrlim).2 ε hε] with k hk
    exact (hρsupp k).trans ((ball_subset_ball hk.le).trans hεt)
  -- Steps 4 and 6: `ψ k = id + ρ k ⋆ g` has derivative `I + ρ k ⋆ Dg` (the `precompR`
  -- convolution of `hasFDerivAt_convolution_right` is the scalar one)
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P).precompR (Euclid P) =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (Euclid P →L[ℝ] Euclid P) →L[ℝ] (Euclid P →L[ℝ] Euclid P)) := by
    ext a f v
    simp [ContinuousLinearMap.precompR]
  have hderiv : ∀ k x, HasFDerivAt
      (fun y => y + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume y)
      (ContinuousLinearMap.id ℝ (Euclid P) +
        convolution (ρ k) (fderiv ℝ g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) x := by
    intro k x
    have h := hgcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hρloc k) hg1 x
    rw [hL] at h
    exact (hasFDerivAt_id x).add h
  -- Step 5: off `K'`, `g = 0` on `ball x (r k)`, so `(ρ k ⋆ g) x = 0`
  have hsupp : ∀ k x, x ∉ cthickening δ K →
      convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro k x hx
    have hgy : ∀ y ∈ ball x (r k), g y = 0 := fun y hy => hgK y fun hyK =>
      hx (mem_cthickening_of_dist_le x y δ K hyK ((mem_ball'.1 hy).le.trans (hrδ k)))
    rw [convolution_eq_right' _ (hρsupp k) fun y hy =>
      (hgy y hy).trans (hgy x (mem_ball_self (hr0 k))).symm, hgy x (mem_ball_self (hr0 k))]
    simp
  refine ⟨fun k x => x + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x,
    cthickening δ K, 1 + A, hK.cthickening, hδU, fun k => ?_, fun k x hx => ?_, fun k x => ?_,
    fun x => ?_, fun x => ?_⟩
  · exact contDiff_id.add
      ((hρc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs k)
        hgc.locallyIntegrable)
  · simp only [hsupp k x hx, add_zero]
  · -- Step 6: `‖Dψ k‖ ≤ ‖I‖ + sup ‖Dg‖ ≤ 1 + A`
    rw [(hderiv k x).fderiv]
    refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
    have h := dist_convolution_le (x₀ := x) (z₀ := 0) (μ := volume) hA0 (hρsupp k) (hρn k) (hρi k)
      hDgc.aestronglyMeasurable fun y _ => by rw [dist_zero_right]; exact hA y
    rwa [dist_zero_right] at h
  · -- Step 7: `ψ k x → x + g x = φ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hgc.aestronglyMeasurable) ((hgc.tendsto x).comp tendsto_snd)
      tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add h
    rwa [hg x, add_sub_cancel] at h2
  · -- Step 7: `Dψ k x → I + Dg x = Dφ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => fderiv ℝ g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hDgc.aestronglyMeasurable)
      ((hDgc.tendsto x).comp tendsto_snd) tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ContinuousLinearMap.id ℝ (Euclid P))
      atTop (𝓝 (ContinuousLinearMap.id ℝ (Euclid P)))).add h
    rw [hDg x, add_sub_cancel] at h2
    exact h2.congr fun k => ((hderiv k x).fderiv).symm

/-- Simon 6.2.24(1), `∂f_#T = f_#∂T`, for the `C¹` push-forward formula of 6.2.24(2) (step 3
of the push-forward proof): if `T = τ(M, θ, ξ)` has `∂T = 0` in `U` and
`S(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ`, where the `C¹` map `φ` is the identity off a compact
`K ⊆ U`, then `∂S = 0` in `U`.  Take `C^∞` maps `ψₖ`, equal to the identity off one compact
`K' ⊆ U`, with `‖Dψₖ‖ ≤ C`, `ψₖ → φ` and `Dψₖ → Dφ` pointwise.  For `η ∈ 𝒟ⁿ⁻¹(U)`,
`ψₖ^#η ∈ 𝒟ⁿ⁻¹(U)` and `d(ψₖ^#η) = ψₖ^#(dη)`, so `0 = ∂T(ψₖ^#η) = ∫_M θ ⟨ψₖ^#(dη), ξ⟩ dHⁿ`;
by dominated convergence these integrals tend to `S(dη) = ∂S(η)`. -/
theorem Submission.dpf_pushforward_formula_boundaryVanishes : ∀ (P n : ℕ) (U K : Set (Euclid P)) (T S : GeometricCurrentOn U n) (R : IMRep U n) (φ : Euclid P → Euclid P), IsOpen U → R.Represents T → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → (∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]) → BoundaryVanishes T → BoundaryVanishes S := by
  intro P n U K T S R φ hU hRT hK hKU hφ hφK hS hT
  -- Step 1: `∂ = 0` in degree `0`; for `n = m + 1` show `∂S(η) = S(dη) = 0` for every `η`
  rcases n with _ | m
  · trivial
  change T.boundary = 0 at hT
  change S.boundary = 0
  -- Step 2: `C^∞` maps `ψₖ = id` off a compact `K' ⊆ U`, `‖Dψₖ‖ ≤ C`, `ψₖ → φ`, `Dψₖ → Dφ`
  obtain ⟨ψ, K', C, hK', hK'U, hψ, hψK', hψC, hψφ, hDψφ⟩ :=
    Submission.dpf_smooth_approx_compact_perturbation P U K φ hU hK hKU hφ hφK
  ext η
  rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply, hS]
  -- the test form `α = dη ∈ 𝒟ⁿ(U)`
  set α : DifferentialForm (Euclid P) (m + 1) :=
    (exteriorDerivativeTestOn U m η : DifferentialForm (Euclid P) (m + 1))
  have hα : IsTestForm α ∧ tsupport α ⊆ U := (exteriorDerivativeTestOn U m η).property
  -- Steps 3–5: `∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ = ∂T(ψₖ^#η) = 0` for every `k`
  have hI : ∀ k, ∫ x in R.carrier, (R.mult x : ℝ) *
      R.orient x ((α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x)) ∂μHE[m + 1] = 0 := by
    intro k
    -- Step 3: `ψₖ^#η` is a test form supported in `tsupport η ∪ K' ⊆ U`
    obtain ⟨hηk, hηkK⟩ := Submission.dpf_pb_smooth_pullback_isTestForm P m K' (ψ k)
      (η : DifferentialForm (Euclid P) m) hK' (hψ k) (hψK' k) η.property.1
    let ηk : TestFormOn U m :=
      ⟨fun x => ((η : DifferentialForm (Euclid P) m) (ψ k x)).compContinuousLinearMap
        (fderiv ℝ (ψ k) x), hηk, hηkK.trans (union_subset η.property.2 hK'U)⟩
    -- Step 4: `d(ψₖ^#η) = ψₖ^#(dη)` (Simon 6.1.14; Mathlib `extDeriv_pullback`)
    have hnat : (exteriorDerivativeTestOn U m ηk : DifferentialForm (Euclid P) (m + 1)) =
        fun x => (α (ψ k x)).compContinuousLinearMap (fderiv ℝ (ψ k) x) := by
      funext x
      exact extDeriv_pullback (η.property.1.1.differentiable (by simp)).differentiableAt
        (hψ k).contDiffAt (by simp)
    -- Step 5: `0 = ∂T(ψₖ^#η) = T(d(ψₖ^#η)) = ∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ`
    have h0 : T (exteriorDerivativeTestOn U m ηk) = 0 := by
      rw [← GeometricCurrentOn.boundary_apply, hT, GeometricCurrentOn.zero_apply]
    rw [hRT, IMRep.action, hnat] at h0
    exact h0
  -- Step 6: dominated convergence, `∫_M θ ⟨ψₖ^#α, ξ⟩ dHⁿ → ∫_M θ ⟨φ^#α, ξ⟩ dHⁿ = S(dη)`
  have hlim := Submission.dpf_pb_imrep_pullback_integral_tendsto P (m + 1) U K' R α ψ φ C hK'
    hK'U hα.1.1.continuous hα.1.2 hα.2 (fun k => (hψ k).of_le (by exact_mod_cast le_top)) hψK'
    hψC hψφ hDψφ
  -- Step 7: the limit of the vanishing integrals is `0`
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun k => (hI k).symm)

/-- **Carrier, mass and support of integer multiplicity currents in `ℝᴾ`** (Simon Ch. 6, 2.11 and
Remark 3.2(3)).  (1) If `Y = τ(M, θ, ξ)` in `ℝᴾ`, then `Hⁿ(M \ spt Y) = 0`, `M(Y) = μ_R(ℝᴾ)`, and
`μ_R(ℝᴾ) < ∞` if `spt Y` is compact.  (2) `spt Y₁` is closed and `spt(Y₁ - Y₂) ⊆ spt Y₁ ∪ spt Y₂`.
`Y` kills every form supported in the open set `W = ℝᴾ \ spt Y` (`dtc_vanish_off_support`), so
`μ_R(W) = M_W(Y) = 0` (`dtc_mass_eq_measure`) and, as `θ ≥ 1` on `M`, `Hⁿ(M ∩ W) = 0`; for compact
`spt Y`, `μ_R(ℝᴾ) ≤ μ_R(spt Y) + μ_R(W) = ∫_{M ∩ spt Y} θ dHⁿ < ∞`.  A common relatively compact
neighbourhood on which `Y₁` and `Y₂` vanish lies in the zero region of `Y₁ - Y₂`. -/
theorem Submission.dtc_bc_lc_pf_imrep_carrier_mass_support : ∀ (P n : ℕ), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → μHE[n] (R.carrier \ Y.support) = 0 ∧ Y.mass = R.measure univ ∧ (IsCompact Y.support → R.measure univ ≠ ∞)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y₁.support ∧ (Y₁ - Y₂).support ⊆ Y₁.support ∪ Y₂.support := by
  intro P n
  -- Step 1: `spt Y = ℝᴾ \ Z(Y)` is closed, the zero region `Z(Y)` being open
  have hclosed : ∀ Y : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed Y.support := by
    intro Y
    rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
    exact Y.isOpen_zeroRegion.isClosed_compl
  refine ⟨fun Y R hRY => ?_, fun Y₁ Y₂ => ⟨hclosed Y₁, ?_⟩⟩
  · -- Step 2: `M_W(Y) = 0` on the open set `W = ℝᴾ \ spt Y` (`dtc_vanish_off_support`)
    have hWo : IsOpen (Y.support)ᶜ := (hclosed Y).isOpen_compl
    have hmass : Y.massOn (Y.support)ᶜ = 0 := by
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      dsimp only
      rw [Submission.dtc_vanish_off_support P n univ Y ω
        (subset_compl_iff_disjoint_right.mp hω.1), ENNReal.ofReal_zero]
    -- Step 3: `μ_R(W) = M_W(Y) = 0` (`dtc_mass_eq_measure`); as `θ ≥ 1` on `M`, `Hⁿ(M ∩ W) = 0`
    have hμW : R.measure (Y.support)ᶜ = 0 := by
      rw [← Submission.dtc_mass_eq_measure P n univ _ Y R isOpen_univ hWo (subset_univ _) hRY]
      exact hmass
    have hnull : μHE[n] (R.carrier \ Y.support) = 0 := by
      have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
        measurable_from_nat.comp R.measurable_mult
      have h := (withDensity_apply_eq_zero' (μ := μHE[n].restrict R.carrier)
        hθ.aemeasurable).1 hμW
      rw [Measure.restrict_apply' R.measurableSet_carrier] at h
      refine measure_mono_null ?_ h
      intro x hx
      exact ⟨⟨Nat.cast_ne_zero.2 (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    -- Step 4: `M(Y) = M_{ℝᴾ}(Y) = μ_R(ℝᴾ)`
    refine ⟨hnull, Submission.dtc_mass_eq_measure P n univ univ Y R isOpen_univ isOpen_univ
      subset_rfl hRY, fun hK => ?_⟩
    -- Step 5: `μ_R(ℝᴾ) ≤ μ_R(spt Y) + μ_R(W) = ∫_{M ∩ spt Y} θ dHⁿ < ∞`
    have hKm : R.measure Y.support =
        ∫⁻ x in R.carrier ∩ Y.support, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
        Measure.restrict_restrict hK.measurableSet, inter_comm]
    refine ne_top_of_le_ne_top ?_ ((measure_mono (union_compl_self Y.support).ge).trans
      ((measure_union_le _ _).trans_eq (by rw [hμW, add_zero])))
    rw [hKm]
    exact R.locallyIntegrable_mult _ hK (subset_univ _)
  · -- Step 6: `x ∉ spt Y₁ ∪ spt Y₂` lies in open `W₁`, `W₂` with compact closures on which
    -- `Y₁`, `Y₂` vanish; then `W₁ ∩ W₂` witnesses `x ∈ Z(Y₁ - Y₂)`
    intro x hx
    by_contra hxs
    rw [mem_union, not_or] at hxs
    have hZ : ∀ Y : GeometricCurrentOn (univ : Set (Euclid P)) n, x ∉ Y.support →
        x ∈ Y.zeroRegion := fun Y h => not_not.mp fun h' => h ⟨mem_univ x, h'⟩
    obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁v⟩, hxW₁⟩ := mem_sUnion.mp (hZ Y₁ hxs.1)
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ := mem_sUnion.mp (hZ Y₂ hxs.2)
    -- `closure (W₁ ∩ W₂) ⊆ closure W₁` is compact, and `(Y₁ - Y₂)(ω) = Y₁(ω) - Y₂(ω) = 0`
    refine hx.2 ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o, hW₁c.of_isClosed_subset isClosed_closure
      (closure_mono inter_subset_left), subset_univ _, fun ω hω => ?_⟩, hxW₁, hxW₂⟩
    show Y₁ ω - Y₂ ω = 0
    rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]

/-- **Simon Ch. 6, 2.27 and 2.29** (pointwise estimate behind the push-forward; step 1(a) of the
local comparison in the proof of 7.3.1): let `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` be a unit orientation of `Q`
(`τ` orthonormal, `span τ = Q`) and `L` a continuous linear map.  (a) `⟨α ∘ ΛⁿL, ξ⟩ = ±α(L ∘ τ)`,
and `|α(v)| ≤ |α|_E det(⟨vᵢ, vⱼ⟩)^{1/2}` (Cauchy–Binet and Cauchy–Schwarz,
`covectorEuclideanNorm_gram_bounds`), `det(⟨vᵢ, vⱼ⟩) ≤ ∏ᵢ |vᵢ|²` (Hadamard) and
`|Lτᵢ| ≤ ‖L‖ |τᵢ| = ‖L‖` give `|⟨α ∘ ΛⁿL, ξ⟩| ≤ |α|_E ‖L‖ⁿ`.  (b) If `L` fixes `Q` pointwise,
then `L ∘ τ = τ` since each `τᵢ ∈ Q`, so `⟨α ∘ ΛⁿL, ξ⟩ = ±α(τ) = ⟨α, ξ⟩`. -/
theorem Submission.dtc_bc_lc_pf_unitOrientation_comp : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ (α.compContinuousLinearMap L)| ≤ covectorEuclideanNorm α * ‖L‖ ^ n) ∧ ((∀ v ∈ Q, L v = v) → ∀ α : Covector (Euclid P) n, ξ (α.compContinuousLinearMap L) = ξ α) := by
  rintro P n ξ Q L ⟨τ, hτ, hspan, hsign⟩
  -- `(α ∘ ΛⁿL)(τ) = α(L ∘ τ)`
  have hcomp : ∀ α : Covector (Euclid P) n, α.compContinuousLinearMap L τ = α (⇑L ∘ τ) :=
    fun α => ContinuousAlternatingMap.compContinuousLinearMap_apply α L τ
  refine ⟨fun α => ?_, fun hL α => ?_⟩
  · -- (a) `|⟨α ∘ ΛⁿL, ξ⟩| = |α(L ∘ τ)|` for either sign
    have habs : |ξ (α.compContinuousLinearMap L)| = |α (⇑L ∘ τ)| := by
      rcases hsign with h | h
      · rw [h, hcomp]
      · rw [h, hcomp, abs_neg]
    -- `|Lτᵢ| ≤ ‖L‖ |τᵢ| = ‖L‖`
    have hLτ : ∀ i, ‖(⇑L ∘ τ) i‖ ≤ ‖L‖ := fun i => by
      simpa only [Function.comp_apply, hτ.norm_eq_one i, mul_one] using L.le_opNorm (τ i)
    have hα := covectorEuclideanNorm_nonneg α
    rw [habs]
    calc |α (⇑L ∘ τ)|
        ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j =>
            inner ℝ ((⇑L ∘ τ) i) ((⇑L ∘ τ) j))) :=
          (Submission.covectorEuclideanNorm_gram_bounds P n).1 α (⇑L ∘ τ)
      _ ≤ covectorEuclideanNorm α * Real.sqrt (∏ i, ‖(⇑L ∘ τ) i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (Submission.dtc_bc_lc_pf_gram_det_le_prod_norm_sq P n (⇑L ∘ τ))) hα
      _ = covectorEuclideanNorm α * ∏ i, ‖(⇑L ∘ τ) i‖ := by
          rw [Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _)]
      _ ≤ covectorEuclideanNorm α * ‖L‖ ^ n := by
          rw [← Fin.prod_const]
          exact mul_le_mul_of_nonneg_left
            (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => hLτ i) hα
  · -- (b) each `τᵢ` lies in `Q = span (range τ)`, so `L ∘ τ = τ`
    have hLτ : ⇑L ∘ τ = τ := by
      funext i
      exact hL (τ i) (hspan ▸ Submodule.subset_span (mem_range_self i))
    rcases hsign with h | h <;> rw [h, h, hcomp, hLτ]

/-- **Cut-off of the pulled-back form** (Simon Ch. 6, 2.23 and Remark 2.24(2)).  Let `O ⊆ ℝᴾ` be
open, `K ⊆ O` compact, `f : ℝᴾ → ℝ^Q` of class `C¹` on `O` and `ω` a continuous `n`-form on `ℝ^Q`.
Some continuous, compactly supported `h : ℝᴾ → Λⁿ(ℝᴾ)` equals `ω(f(x)) ∘ Df(x)` on `K`.

Proof sketch:
* `f` and `Df` are continuous on `O`, and `(β, A) ↦ β ∘ A` is continuous (it has a strict
  derivative everywhere), so `γ(x) = ω(f(x)) ∘ Df(x)` is continuous on `O`.
* Take `ρ > 0` with `cthickening ρ K ⊆ O`, and a Urysohn cut-off `χ` with
  `support χ = thickening ρ K` and `χ = 1` on `cthickening (ρ/2) K ⊇ K`.
* `h = χ • γ` has `tsupport h ⊆ tsupport χ ⊆ cthickening ρ K`, a compact subset of `O`: so `h` has
  compact support, is continuous (being continuous on the open `O ⊇ tsupport h`), and `h = γ`
  on `K`. -/
theorem Submission.dtc_bc_lc_pf_ext_pullback_cutoff : ∀ (P Q n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid Q) (ω : DifferentialForm (Euclid Q) n), IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → Continuous ω → ∃ h : Euclid P → Covector (Euclid P) n, Continuous h ∧ HasCompactSupport h ∧ ∀ x ∈ K, h x = (ω (f x)).compContinuousLinearMap (fderiv ℝ f x) := by
  intro P Q n O K f ω hO hf hK hKO hω
  -- `f` and `Df` are continuous on `O`
  have hfc : ContinuousOn f O := hf.continuousOn
  have hDf : ContinuousOn (fderiv ℝ f) O := hf.continuousOn_fderiv_of_isOpen hO le_rfl
  -- `(β, A) ↦ β ∘ A` is continuous, having a strict derivative everywhere
  have hΦ : Continuous fun βA : Covector (Euclid Q) n × (Euclid P →L[ℝ] Euclid Q) =>
      βA.1.compContinuousLinearMap βA.2 :=
    continuous_iff_continuousAt.2 fun βA =>
      (ContinuousAlternatingMap.hasStrictFDerivAt_compContinuousLinearMap βA).continuousAt
  -- `γ(x) = ω(f(x)) ∘ Df(x)` is continuous on `O`
  have hγ : ContinuousOn (fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)) O :=
    hΦ.comp_continuousOn ((hω.comp_continuousOn hfc).prodMk hDf)
  -- a margin `cthickening ρ K ⊆ O`, a compact set
  obtain ⟨ρ, hρ, hρO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hρK : IsCompact (cthickening ρ K) := hK.cthickening
  -- a cut-off `χ` with `support χ = thickening ρ K` and `χ = 1` on `cthickening (ρ/2) K`
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 0)
    (isOpen_thickening (δ := ρ) (E := K)) (isClosed_cthickening (δ := ρ / 2) (E := K))
    (cthickening_subset_thickening' hρ (half_lt_self hρ) K)
  have hχK : ∀ x ∈ K, χ x = 1 := fun x hx => (hχ1 x).1 (self_subset_cthickening K hx)
  have hχt : tsupport χ ⊆ cthickening ρ K := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening ρ K
  -- `h = χ • γ`, whose support lies in `tsupport χ`
  have hts := tsupport_smul_subset_left χ
    fun x => (ω (f x)).compContinuousLinearMap (fderiv ℝ f x)
  refine ⟨fun x => χ x • (ω (f x)).compContinuousLinearMap (fderiv ℝ f x), ?_, ?_, ?_⟩
  · -- continuous on the open `O ⊇ tsupport h`, hence continuous
    exact (hχ.continuous.continuousOn.smul hγ).continuous_of_tsupport_subset hO
      (hts.trans (hχt.trans hρO))
  · -- `tsupport h ⊆ tsupport χ ⊆ cthickening ρ K`, a compact set
    exact hρK.of_isClosed_subset (isClosed_tsupport _) (hts.trans hχt)
  · -- `χ = 1` on `K`
    intro x hx
    simp only [hχK x hx, one_smul]
/-- **Mollification** (behind Simon Ch. 6, Remark 2.24(2)): a continuous, compactly supported
`n`-covector field `h` on `ℝᴾ` is the uniform limit of test forms `ωⱼ ∈ 𝒟ⁿ(ℝᴾ)`.

Let `ψⱼ = φⱼ / ∫ φⱼ`, where `φⱼ ≥ 0` is a smooth bump with `support φⱼ = B_{1/(j+1)}(0)`, so
`ψⱼ ≥ 0` and `∫ ψⱼ = 1`.  Then `ωⱼ = ψⱼ ⋆ h` is `C^∞` with compact support, and
`‖ωⱼ(x) − h(x)‖ ≤ sup_{‖t‖ < 1/(j+1)} ‖h(x − t) − h(x)‖`, which tends to `0` uniformly in `x`
because `h` is uniformly continuous. -/
theorem Submission.dtc_bc_lc_pf_ext_mollify_tendstoUniformly : ∀ (P n : ℕ) (h : Euclid P → Covector (Euclid P) n), Continuous h → HasCompactSupport h → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, TendstoUniformly (fun j x => (ωs j : DifferentialForm (Euclid P) n) x) h atTop := by
  intro P n h hhc hhs
  -- (1) `h` is locally integrable
  have hhi : LocallyIntegrable h volume := hhc.locallyIntegrable
  -- (2) smooth bumps `φ j ≥ 0` with `support (φ j) = B_{1/(j+1)}(0)`, and the normalized kernels
  -- `ψ j = φ j / ∫ φ j`: `ψ j ≥ 0`, `∫ ψ j = 1`
  have hr : ∀ j : ℕ, 0 < 1 / ((j : ℝ) + 1) := fun j => Nat.one_div_pos_of_nat
  let φ : ℕ → ContDiffBump (0 : Euclid P) := fun j =>
    ⟨1 / ((j : ℝ) + 1) / 2, 1 / ((j : ℝ) + 1), half_pos (hr j), half_lt_self (hr j)⟩
  have hφ : ∀ j, 0 < ∫ y, φ j y := fun j => by
    refine (integral_pos_iff_support_of_nonneg (φ j).nonneg'
      ((φ j).continuous.integrable_of_hasCompactSupport (φ j).hasCompactSupport)).mpr ?_
    rw [(φ j).support_eq]
    exact measure_ball_pos volume 0 (hr j)
  let ψ : ℕ → Euclid P → ℝ := fun j y => φ j y / ∫ y, φ j y
  have hψφ : ∀ j, support (ψ j) ⊆ support (φ j) := fun j y hy h0 => hy (by simp [ψ, h0])
  have hψs : ∀ j, support (ψ j) ⊆ ball 0 (1 / ((j : ℝ) + 1)) := fun j =>
    (hψφ j).trans (φ j).support_eq.subset
  have hψc : ∀ j, HasCompactSupport (ψ j) := fun j => (φ j).hasCompactSupport.mono (hψφ j)
  have hψ0 : ∀ j y, 0 ≤ ψ j y := fun j y => div_nonneg (φ j).nonneg (hφ j).le
  have hψ1 : ∀ j, ∫ y, ψ j y = 1 := fun j => by rw [integral_div, div_self (hφ j).ne']
  -- (3) `ω j = ψ j ⋆ h`
  let ω : ℕ → DifferentialForm (Euclid P) n := fun j =>
    convolution (ψ j) h (ContinuousLinearMap.lsmul ℝ ℝ) volume
  -- (4) `ω j` is `C^∞` with compact support, so it is a test form on `ℝᴾ`
  have hω : ∀ j, ω j ∈ TestFormOn (univ : Set (Euclid P)) n := fun j =>
    ⟨⟨(hψc j).contDiff_convolution_left _ ((φ j).contDiff.div_const _) hhi,
      (hψc j).convolution _ hhs⟩, subset_univ _⟩
  refine ⟨fun j => ⟨ω j, hω j⟩, Metric.tendstoUniformly_iff.mpr fun ε hε => ?_⟩
  -- (6) uniform continuity of `h` gives `δ` for `ε/2`; take `J` with `1/(J+1) < δ`
  obtain ⟨δ, hδ, hhδ⟩ := Metric.uniformContinuous_iff.mp
    (hhs.uniformContinuous_of_continuous hhc) (ε / 2) (half_pos hε)
  obtain ⟨J, hJ⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.mpr ⟨J, fun j hj x => ?_⟩
  -- (5) for `j ≥ J`, `‖h(y) − h(x)‖ < ε/2` on `B_{1/(j+1)}(x)`, so `‖ω j x − h x‖ ≤ ε/2 < ε`
  rw [dist_comm]
  refine lt_of_le_of_lt ?_ (half_lt_self hε)
  exact dist_convolution_le (half_pos hε).le (hψs j) (hψ0 j) (hψ1 j) hhc.aestronglyMeasurable
    fun y hy => (hhδ ((mem_ball.mp hy).trans_le ((Nat.one_div_le_one_div hj).trans hJ.le))).le
/-- **Limit of `IMRep` integrals under uniform convergence on a compact carrier set** (Simon
Ch. 6, 2.24(2) with the integral representation 6.3.1 (‡); chapter-06.txt lines 415–424, 271).
Let `R = (M, θ, ξ)` be an `IMRep` in `U`, `K ⊆ U` compact with `Hⁿ(M \ K) = 0`, and `gⱼ`, `g`
continuous `n`-covector fields with `gⱼ → g` uniformly on `K`.  Then
`∫_M θ ⟨gⱼ, ξ⟩ dHⁿ → ∫_M θ ⟨g, ξ⟩ dHⁿ`.

Write `μ = Hⁿ⌞M`.  `μ`-a.e. `x` lies in `K`, and `M =ᵐ M ∩ K`, so `θ` is `μ`-integrable by the
local integrability of `θ` on `K`.  A unit orientation has `|ξ(x)(β)| = |β(τ)| ≤ ‖β‖` (`τ`
orthonormal), so for continuous `G` the integrand `θ ξ(G)` is a.e. strongly measurable and
dominated by `(sup_K ‖G‖) θ`, hence integrable.  Finally
`|∫ θ ξ(gⱼ) dμ − ∫ θ ξ(g) dμ| ≤ ∫ θ ‖gⱼ − g‖ dμ ≤ Θ ε/(Θ + 1) < ε` for large `j`,
where `Θ = ∫ θ dμ`. -/
theorem Submission.dtc_bc_lc_pf_ext_imrep_integral_tendsto : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n) (gs : ℕ → Euclid P → Covector (Euclid P) n) (g : Euclid P → Covector (Euclid P) n), IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → (∀ j, Continuous (gs j)) → Continuous g → TendstoUniformlyOn gs g atTop K → Tendsto (fun j => ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (gs j x) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x) ∂μHE[n])) := by
  intro P n U K R gs g hK hKU hnull hgs hg hunif
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) `μ`-a.e. point lies in `K`, as `Hⁿ(M \ K) = 0`
  have hae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [hμ, ae_restrict_iff' R.measurableSet_carrier, ae_iff]
    refine measure_mono_null (fun x hx => ?_) hnull
    simp only [mem_ofPred_eq, not_imp] at hx
    exact hx
  -- (2) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  -- (3) `θ` is `μ`-integrable: `μ = Hⁿ⌞(M ∩ K)` and `∫_{M ∩ K} θ dHⁿ < ∞`
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  have hμK : μ = μHE[n].restrict (R.carrier ∩ K) := by
    rw [hμ]
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [sdiff_self_inter]
      exact hnull
    · rw [sdiff_eq_empty.2 inter_subset_left]
      exact measure_empty
  have hθint : Integrable (fun x => (R.mult x : ℝ)) μ := by
    refine ⟨hθmeas, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂μ < ∞
    rw [hμK]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) measurability of the integrand for continuous `G`
  have hmeas : ∀ G : Euclid P → Covector (Euclid P) n, Continuous G →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (G x)) μ := by
    intro G hG
    have h2 : AEStronglyMeasurable (fun x => R.orient x (G x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hG.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (5) integrability of the integrand for continuous `G`: it is dominated by `(sup_K ‖G‖) θ`
  have hint : ∀ G : Euclid P → Covector (Euclid P) n, Continuous G →
      Integrable (fun x => (R.mult x : ℝ) * R.orient x (G x)) μ := by
    intro G hG
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuousOn
    refine Integrable.mono' (hθint.const_mul C) (hmeas G hG) ?_
    filter_upwards [hbound, hae] with x hx hxK
    rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    calc (R.mult x : ℝ) * |R.orient x (G x)| ≤ (R.mult x : ℝ) * ‖G x‖ := by
          gcongr; exact hx _
      _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x hxK
      _ = C * (R.mult x : ℝ) := mul_comm _ _
  -- (6) the estimate `|∫ θ ξ(gⱼ) dμ − ∫ θ ξ(g) dμ| ≤ Θ ε/(Θ + 1) < ε` for large `j`
  set Θ := ∫ x, (R.mult x : ℝ) ∂μ with hΘdef
  have hΘ : 0 ≤ Θ := integral_nonneg fun x => Nat.cast_nonneg _
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (Θ + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (ε / (Θ + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  rw [Real.dist_eq, ← integral_sub (hint _ (hgs j)) (hint _ hg), ← Real.norm_eq_abs]
  have hle : ‖∫ x, ((R.mult x : ℝ) * R.orient x (gs j x) - (R.mult x : ℝ) * R.orient x (g x)) ∂μ‖
      ≤ ∫ x, ε / (Θ + 1) * (R.mult x : ℝ) ∂μ := by
    refine norm_integral_le_of_norm_le (hθint.const_mul _) ?_
    filter_upwards [hbound, hae] with x hx hxK
    rw [← mul_sub, ← (R.orient x).map_sub, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    calc (R.mult x : ℝ) * |R.orient x (gs j x - g x)| ≤ (R.mult x : ℝ) * ‖gs j x - g x‖ := by
          gcongr; exact hx _
      _ ≤ (R.mult x : ℝ) * (ε / (Θ + 1)) := by
          gcongr
          have h := hN j hj x hxK
          rw [dist_comm, dist_eq_norm] at h
          exact h.le
      _ = ε / (Θ + 1) * (R.mult x : ℝ) := mul_comm _ _
  rw [integral_const_mul, ← hΘdef] at hle
  refine hle.trans_lt ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

/-- **Integral form of the push-forward along one fixed sequence of test forms** (Simon Ch. 6,
2.23–2.24(2)).  For `f` of class `C¹` on an open `O ⊇ K` (`K` compact) and `ω ∈ 𝒟ⁿ(ℝᴾ)` there
are `ω_j ∈ 𝒟ⁿ(ℝᴾ)`, chosen before any current, with `Y(ω_j) → ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ⟩ dHⁿ`
for every `Y = τ(M, θ, ξ)` with `spt Y ⊆ K`.  A cut-off of `ω(f(·)) ∘ Df(·)` is a continuous,
compactly supported `h` equal to it on `K` (`dtc_bc_lc_pf_ext_pullback_cutoff`), and mollified
test forms converge to `h` uniformly (`dtc_bc_lc_pf_ext_mollify_tendstoUniformly`).  As
`Hⁿ(M \ K) ≤ Hⁿ(M \ spt Y) = 0` (`dtc_bc_lc_pf_imrep_carrier_mass_support`),
`Y(ω_j) = ∫_M θ ξ(ω_j) → ∫_M θ ξ(h)` (`dtc_bc_lc_pf_ext_imrep_integral_tendsto`), and
`∫_M θ ξ(h)` is the stated integral because `h = ω(f) ∘ Df` on `K`. -/
theorem Submission.dtc_bc_lc_pf_pullback_integral_extension : ∀ (P n : ℕ) (O K : Set (Euclid P)) (f : Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) n), IsOpen O → ContDiffOn ℝ 1 f O → IsCompact K → K ⊆ O → ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, ∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents Y → Y.support ⊆ K → Tendsto (fun j => Y (ωs j)) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n])) := by
  intro P n O K f ω hO hf hK hKO
  -- Steps 1–2: a continuous, compactly supported `h` with `h = ω(f(·)) ∘ Df(·)` on `K`
  obtain ⟨h, hhc, hhs, hhK⟩ := Submission.dtc_bc_lc_pf_ext_pullback_cutoff P P n O K f
    (ω : DifferentialForm (Euclid P) n) hO hf hK hKO ω.property.1.1.continuous
  -- Step 3: test forms `ω_j → h` uniformly; they depend only on `f`, `ω`, `O` and `K`
  obtain ⟨ωs, hωs⟩ := Submission.dtc_bc_lc_pf_ext_mollify_tendstoUniformly P n h hhc hhs
  refine ⟨ωs, fun Y R hRY hYK => ?_⟩
  -- Step 4(a): `Hⁿ(M \ K) ≤ Hⁿ(M \ spt Y) = 0`
  have hnull : μHE[n] (R.carrier \ K) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_right hYK)
      ((Submission.dtc_bc_lc_pf_imrep_carrier_mass_support P n).1 Y R hRY).1
  -- Step 5: `h = ω(f) ∘ Df` on `K`, which contains `Hⁿ`-a.e. point of `M`, so the limits agree
  have hae : (fun x => (R.mult x : ℝ) * R.orient x (h x)) =ᵐ[μHE[n].restrict R.carrier]
      fun x => (R.mult x : ℝ) * R.orient x
        (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) := by
    have hMK : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ K := by
      rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
      refine measure_mono_null (fun x hx => ?_) hnull
      exact ⟨hx.2, hx.1⟩
    filter_upwards [hMK] with x hx
    rw [hhK x hx]
  rw [← integral_congr_ae hae]
  -- Step 6: `Y(ω_j) = ∫_M θ ξ(ω_j) → ∫_M θ ξ(h)`
  exact (Submission.dtc_bc_lc_pf_ext_imrep_integral_tendsto P n univ K R
    (fun j x => (ωs j : DifferentialForm (Euclid P) n) x) h hK (subset_univ K) hnull
    (fun j => (ωs j).property.1.1.continuous) hhc hωs.tendstoUniformlyOn).congr
    fun j => (hRY (ωs j)).symm
/-- **Mass bound for the push-forward formula** (Simon Ch. 6, 2.27 and 2.29:
`M(f_#T) ≤ (ess sup |Df|)ⁿ M(T)`).  Let `‖Df‖ ≤ L` on `O`, let `R = (M, θ, ξ)` represent `Y` with
`spt Y ⊆ O`, and let `Z(ω) = ∫_M θ ⟨ω(f(x)) ∘ ΛⁿDf(x), ξ(x)⟩ dHⁿ`.  Then `M(Z) ≤ Lⁿ M(Y)`.
* `Hⁿ(M ∖ spt Y) = 0` and `M(Y) = μ_R(ℝᴾ) = ∫_M θ dHⁿ`.
* For `|ω| ≤ 1` and `Hⁿ`-a.e. `x ∈ M`: `x ∈ spt Y ⊆ O`, so `0 ≤ ‖Df(x)‖ ≤ L` (in particular
  `L ≥ 0` whenever `M` is not `Hⁿ`-null), and `ξ(x)` is a unit orientation of a plane, so
  `|⟨ω(f(x)) ∘ ΛⁿDf(x), ξ(x)⟩| ≤ |ω(f(x))| ‖Df(x)‖ⁿ ≤ Lⁿ`.
* Hence `Z(ω) ≤ ∫_M |θ ⟨ω(f(x)) ∘ ΛⁿDf(x), ξ(x)⟩| dHⁿ ≤ Lⁿ ∫_M θ dHⁿ = Lⁿ M(Y)`; take the
  supremum over `ω`. -/
theorem Submission.dtc_bc_lc_pf_pushforward_mass_le : ∀ (P n : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P) (L : ℝ) (Y Z : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ L) → R.Represents Y → IsCompact Y.support → Y.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Z ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → Z.mass ≤ ENNReal.ofReal (L ^ n) * Y.mass := by
  intro P n O f L Y Z R hL hRY _ hKO hZ
  -- Step 1: `Hⁿ(M ∖ spt Y) = 0` and `M(Y) = μ_R(ℝᴾ) = ∫_M θ dHⁿ`
  obtain ⟨hnull, hmass, -⟩ := (Submission.dtc_bc_lc_pf_imrep_carrier_mass_support P n).1 Y R hRY
  have hspt : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ Y.support := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null (fun x hx => ?_) hnull
    exact ⟨hx.2, hx.1⟩
  have hθ : ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] = Y.mass := by
    rw [hmass, IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- Step 2: fix an admissible `ω`, i.e. `|ω(z)| ≤ 1` for every `z`
  apply sSup_le
  rintro _ ⟨ω, ⟨-, hω⟩, rfl⟩
  dsimp only
  -- Step 3: `|θ ⟨ω(f(x)) ∘ ΛⁿDf(x), ξ(x)⟩| ≤ Lⁿ θ` at `Hⁿ`-a.e. `x ∈ M`
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x
        (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x))‖ₑ ≤
          ENNReal.ofReal (L ^ n) * (R.mult x : ℝ≥0∞) := by
    filter_upwards [hspt, R.orients] with x hx hor
    obtain ⟨Q, -, hQ⟩ := hor
    have hDf : ‖fderiv ℝ f x‖ ≤ L := hL x (hKO hx)
    have hLn : 0 ≤ L ^ n := pow_nonneg ((norm_nonneg _).trans hDf) n
    have hξ : |R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap
        (fderiv ℝ f x))| ≤ L ^ n :=
      calc _ ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) (f x)) *
            ‖fderiv ℝ f x‖ ^ n :=
          (Submission.dtc_bc_lc_pf_unitOrientation_comp P n (R.orient x) Q (fderiv ℝ f x) hQ).1 _
        _ ≤ 1 * L ^ n := mul_le_mul (hω (f x)) (pow_le_pow_left₀ (norm_nonneg _) hDf n)
            (pow_nonneg (norm_nonneg _) n) zero_le_one
        _ = L ^ n := one_mul _
    rw [Real.enorm_eq_ofReal_abs, abs_mul, Nat.abs_cast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul hLn, mul_comm (L ^ n)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hξ (Nat.cast_nonneg _))
  -- Step 4: `Z(ω) ≤ ∫_M |θ ⟨ω(f(x)) ∘ ΛⁿDf(x), ξ(x)⟩| dHⁿ ≤ Lⁿ ∫_M θ dHⁿ = Lⁿ M(Y)`
  rw [hZ ω]
  refine (Real.ofReal_le_enorm _).trans ((enorm_integral_le_lintegral_enorm _).trans
    ((lintegral_mono_ae hbound).trans_eq ?_))
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hθ]

/-- **Push-forward of an integer multiplicity current by a `C¹` map** (Simon Ch. 6, 3.3–3.9, with
the area formula of Ch. 3, 2.4–2.6).  Let `R = (M, θ, ξ)` be an integer multiplicity triple in the
open `U` with `Hⁿ(M ∖ K) = 0` for a compact `K ⊆ U`, let `f` be `C¹` on an open `O ⊇ K` with
`f(K) ⊆ U`, and let `Q(ω) = ∫_M θ ⟨ω(f(x)) ∘ Df(x), ξ(x)⟩ dHⁿ(x)` for `ω ∈ 𝒟ⁿ(U)`.  Replace `f`
by a globally `Λ`-Lipschitz `C¹` map `φ` with `φ = f` and `Dφ = Df` on `K`, and cut
`M₁ = M ∩ K` (with `∫_{M₁} θ < ∞`), up to an `Hⁿ`-null set, into disjoint bi-Lipschitz pieces
`Gⱼ(Aⱼ)` on which `φ ∘ Gⱼ` either is bi-Lipschitz with injective derivative or has nowhere
injective derivative.  On each piece `ξ ∘ Gⱼ = ±DGⱼ#e / J_{Gⱼ}` a.e., and the area formula turns
the contribution of `Gⱼ(Aⱼ)` to `Q(ω)` into `∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩ dHⁿ`, with
`Nⱼ ⊆ φ(Gⱼ(Aⱼ)) ⊆ f(K) ⊆ U`, an integer `gⱼ ≠ 0` on `Nⱼ`, an orientation `ηⱼ` of `TNⱼ`, and
`∫_{Nⱼ} |gⱼ| ≤ Λⁿ ∫_{Gⱼ(Aⱼ)} θ`.  As `|⟨β, ξ⟩| ≤ ‖β‖` a.e. on `M` and `‖Dφ‖ ≤ Λ`, the integrand
`θ ⟨ω(φ) ∘ Dφ, ξ⟩` is `Hⁿ⌞M₁`-integrable, so `Q(ω) = Σⱼ ∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩ dHⁿ` with
`Σⱼ ∫_{Nⱼ} |gⱼ| ≤ Λⁿ ∫_{M₁} θ < ∞`; gluing the pieces gives an integer multiplicity triple
representing `Q`. -/
theorem Submission.dtc_bc_lc_pf_pushforward_isIntegerMultiplicity : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U K O : Set (Euclid P)) (R : IMRep U n) (f : Euclid P → Euclid P) (Q : GeometricCurrentOn U n), IsOpen U → 0 < n → IsCompact K → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → IsOpen O → K ⊆ O → ContDiffOn ℝ 1 f O → f '' K ⊆ U → (∀ ω : TestFormOn U n, Q ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[n]) → IsIntegerMultiplicity Q := by
  intro hTL P n U K O R f Q hU _hn hK hKU hMK hO hKO hf hfK hQ
  -- Step 1(b): a globally Lipschitz `C¹` map `φ` with `φ = f` and `Dφ = Df` on `K`
  obtain ⟨φ, Λ, hφ, hφL, hφK⟩ :=
    Submission.dtc_bc_lc_pfi_c1_cutoff_lipschitz P O K f hO hK hKO hf
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- Step 1(a): `M₁ = M ∩ K` is Borel with `∫_{M₁} θ dHⁿ < ∞`
  have hM₁ : MeasurableSet (R.carrier ∩ K) :=
    R.measurableSet_carrier.inter hK.isClosed.measurableSet
  have hθM₁ : ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ :=
    R.locallyIntegrable_mult K hK hKU
  -- Step 2: disjoint bi-Lipschitz pieces `Gⱼ(Aⱼ)` covering `M₁` up to a null set, on which
  -- `φ ∘ Gⱼ` is bi-Lipschitz with injective derivative or has nowhere injective derivative
  obtain ⟨G, A, κ, hGL, hA, hκ, hGκ, hGd, hGA, hGAM, hdisj, hnull, hφG⟩ :=
    Submission.dtc_bc_lc_pfi_refined_bilipschitz_pieces P n (R.carrier ∩ K) φ hM₁
      (R.rectifiable.mono inter_subset_left) hφd
  choose L hL using hGL
  have hGAR : ∀ j, G j '' A j ⊆ R.carrier := fun j => (hGAM j).trans inter_subset_left
  -- Step 4: `ξ ∘ Gⱼ = ±DGⱼ#e / J_{Gⱼ}` a.e. on `Aⱼ`; Steps 5–8: the image pieces
  -- `Nⱼ ⊆ φ(Gⱼ(Aⱼ))` with integer multiplicities `gⱼ` and orientations `ηⱼ`
  have hpiece := fun j =>
    Submission.dtc_bc_lc_pfi_piece_pushforward_image P n U R (G j) (A j) (L j) (κ j) φ Λ
      (hL j) (hA j) (hκ j) (hGκ j) (hGd j) (hGAR j)
      (ne_top_of_le_ne_top hθM₁ (lintegral_mono_set (hGAM j)))
      (Submission.dtc_bc_lc_pfi_piece_orientation_sign P n U R (G j) (A j) (L j) (κ j) hU
        (hL j) (hA j) (hκ j) (hGκ j) (hGd j) (hGAR j))
      hφd hφL (hφG j)
  choose N g η hN hNφ hNr hg hg0 hη hηT hgθ hNint using hpiece
  -- Steps 9–11: glue the image pieces into one integer multiplicity triple in `U`
  refine Submission.dtc_bc_lc_pfi_isIntegerMultiplicity_of_pieces hTL P n U N g η Q hU hN ?_
    hNr hg hg0 hη hηT ?_ ?_
  · -- `Nⱼ ⊆ φ(Gⱼ(Aⱼ)) ⊆ φ(K) = f(K) ⊆ U`
    intro j y hy
    obtain ⟨x, hx, rfl⟩ := hNφ j hy
    have hxK : x ∈ K := (hGAM j hx).2
    rw [(hφK x hxK).1]
    exact hfK (mem_image_of_mem f hxK)
  · -- `Σⱼ ∫_{Nⱼ} |gⱼ| ≤ Λⁿ Σⱼ ∫_{Gⱼ(Aⱼ)} θ = Λⁿ ∫_{⋃ⱼ Gⱼ(Aⱼ)} θ ≤ Λⁿ ∫_{M₁} θ < ∞`
    have hle : ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n] ≤
        (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
      calc ∑' j, ∫⁻ y in N j, ((g j y).natAbs : ℝ≥0∞) ∂μHE[n]
          ≤ ∑' j, (Λ : ℝ≥0∞) ^ n * ∫⁻ x in G j '' A j, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
            ENNReal.tsum_le_tsum hgθ
        _ = (Λ : ℝ≥0∞) ^ n * ∫⁻ x in ⋃ j, G j '' A j, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            rw [ENNReal.tsum_mul_left, lintegral_iUnion hGA hdisj]
        _ ≤ (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            gcongr
            exact iUnion_subset hGAM
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hθM₁) hle
  · -- `Q(ω) = ∫_{M₁} θ ⟨ω(φ) ∘ Dφ, ξ⟩ = Σⱼ ∫_{Gⱼ(Aⱼ)} θ ⟨ω(φ) ∘ Dφ, ξ⟩ = Σⱼ ∫_{Nⱼ} gⱼ ⟨ω, ηⱼ⟩`
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- Step 1(c): `x ↦ θ(x) ⟨ω(φ(x)) ∘ Dφ(x), ξ(x)⟩` is `Hⁿ⌞M₁`-integrable, being bounded by
    -- `C Λⁿ θ` (`|⟨β, ξ⟩| ≤ ‖β‖` a.e. on `M`, `‖β ∘ Dφ‖ ≤ ‖β‖ ‖Dφ‖ⁿ`, `‖Dφ‖ ≤ Λ`)
    have hβ : Continuous fun x =>
        ((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x) := by
      have h := (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp
        (hφ.continuous_fderiv one_ne_zero)).clm_apply (hωc.comp hφ.continuous)
      simpa only [Function.comp_apply,
        ContinuousAlternatingMap.compContinuousLinearMapCLM_apply] using h
    have hθ : Measurable fun x => (R.mult x : ℝ) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
    have hθi : Integrable (fun x => (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
      refine ⟨hθ.aestronglyMeasurable, ?_⟩
      show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μHE[n].restrict (R.carrier ∩ K)) < ∞
      simp only [Real.enorm_natCast]
      exact lt_top_iff_ne_top.mpr hθM₁
    have hint : IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x
        (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)))
        (R.carrier ∩ K) μHE[n] := by
      refine Integrable.mono' (hθi.const_mul (C * (Λ : ℝ) ^ n))
        (hθ.aestronglyMeasurable.mul ?_) ?_
      · exact Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
          (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
          (R.aestronglyMeasurable_orient.mono_set inter_subset_left) hβ.aestronglyMeasurable
      · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients]
          with x hx
        obtain ⟨T, -, hT⟩ := hx
        have h1 := (Submission.dtc_bc_lc_pfi_unitOrientation_algebra P n).2.1 _ T hT
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x))
        have h2 := ContinuousAlternatingMap.norm_compContinuousLinearMap_le
          ((ω : DifferentialForm (Euclid P) n) (φ x)) (fderiv ℝ φ x)
        rw [Fintype.card_fin] at h2
        have h3 : ‖fderiv ℝ φ x‖ ^ n ≤ (Λ : ℝ) ^ n :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hφL) n
        rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs, mul_comm (C * (Λ : ℝ) ^ n)]
        gcongr
        exact h1.trans (h2.trans (mul_le_mul (hC _) h3 (by positivity) hC0))
    calc Q ω = ∫ x in R.carrier ∩ K, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] := by
          -- `Hⁿ(M ∖ K) = 0`, and `φ = f`, `Dφ = Df` on `M₁ ⊆ K`
          rw [hQ ω, setIntegral_congr_set (ae_eq_set.mpr
            ⟨by rw [sdiff_self_inter]; exact hMK,
              by rw [sdiff_eq_empty.mpr inter_subset_left, measure_empty]⟩)]
          refine setIntegral_congr_fun hM₁ fun x hx => ?_
          simp only [(hφK x hx.2).1, (hφK x hx.2).2]
      _ = ∫ x in ⋃ j, G j '' A j, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] :=
          -- the pieces cover `M₁` up to an `Hⁿ`-null set
          setIntegral_congr_set (ae_eq_set.mpr ⟨hnull,
            by rw [sdiff_eq_empty.mpr (iUnion_subset hGAM), measure_empty]⟩)
      _ = ∑' j, ∫ x in G j '' A j, (R.mult x : ℝ) * R.orient x
          (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap
            (fderiv ℝ φ x)) ∂μHE[n] :=
          integral_iUnion hGA hdisj (hint.mono_set (iUnion_subset hGAM))
      _ = ∑' j, ∫ y in N j, (g j y : ℝ) * η j y ((ω : DifferentialForm (Euclid P) n) y)
          ∂μHE[n] :=
          tsum_congr fun j => hNint j _ hωc.stronglyMeasurable

/-- **Push-forward by a map that is `C¹` near the support** (Simon Ch. 6, 2.23–2.24(2), 2.29 and
3.3–3.9).  Let `O` be open, `f` be `C¹` on `O` and `n = m + 1`.  For integer multiplicity
`Y ∈ 𝒟ₙ(ℝᴾ)` with `spt Y` compact and `⊆ O`, choose a representation `(M₀, θ₀, ξ₀)` and a `C¹` map
`φ`, the identity off a compact set, with `φ = f` and `Dφ = Df` on an open `V ⊇ spt Y`; put
`push Y(ω) = ∫_{M₀} θ₀ ⟨ω(φ(x)) ∘ ΛⁿDφ(x), ξ₀⟩ dHⁿ`, a current.  For every other `Y`,
`push Y = 0`.  As `Hⁿ(M₀ ∖ spt Y) = 0`, `f` may replace `φ` in the integrand.
(i) Every representation `(M, θ, ξ)` of `Y` gives the same integral: it is the limit of `Y(ωⱼ)`
for one sequence of test forms `ωⱼ`, chosen before the representation.
(ii) `push Y` is integer multiplicity by the area formula (Simon 3.5–3.9).
(iii) If `spt ω` misses the compact set `f(spt Y)`, the integrand vanishes `Hⁿ`-a.e. on `M`.
(iv) `|⟨ω(f(x)) ∘ ΛⁿDf(x), ξ⟩| ≤ |ω(f(x))|·‖Df(x)‖ⁿ` gives `M(push Y) ≤ Lⁿ M(Y)`.
(v) The formula with `φ` sends cycles to cycles (Simon 2.24(1)).
(B) `Y₁ − Y₂` is integer multiplicity with compact support in `spt Y₁ ∪ spt Y₂ ⊆ O`, and the three
integrals are the limits of `(Y₁ − Y₂)(ωⱼ) = Y₁(ωⱼ) − Y₂(ωⱼ)`, `Y₁(ωⱼ)` and `Y₂(ωⱼ)`. -/
theorem Submission.dtc_bc_lc_pushforward : ∀ (P m : ℕ) (O : Set (Euclid P)) (f : Euclid P → Euclid P), IsOpen O → ContDiffOn ℝ 1 f O → ∃ push : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1) → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents Y → IsCompact Y.support → Y.support ⊆ O → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push Y ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1]) ∧ IsIntegerMultiplicity (push Y) ∧ (push Y).support ⊆ f '' Y.support ∧ (∀ L : ℝ, (∀ y ∈ O, ‖fderiv ℝ f y‖ ≤ L) → (push Y).mass ≤ ENNReal.ofReal (L ^ (m + 1)) * Y.mass) ∧ (Y.boundary = 0 → (push Y).boundary = 0)) ∧ ∀ Y₁ Y₂ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Y₁ → IsIntegerMultiplicity Y₂ → IsCompact Y₁.support → Y₁.support ⊆ O → IsCompact Y₂.support → Y₂.support ⊆ O → push (Y₁ - Y₂) = push Y₁ - push Y₂ := by
  intro P m O f hO hf
  -- Step 1: `Hⁿ(M ∖ spt Y) = 0`, so `Hⁿ`-a.e. point of the carrier lies in `spt Y`
  have hcf := Submission.dtc_bc_lc_pf_imrep_carrier_mass_support P (m + 1)
  have hspt : ∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1))
      (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents Y →
      ∀ᵐ x ∂(μHE[m + 1].restrict R.carrier), x ∈ Y.support := by
    intro Y R hR
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null (fun x hx => ?_) (hcf.1 Y R hR).1
    exact ⟨hx.2, hx.1⟩
  -- Step 2: for `Y ∈ 𝒴`, a representation `R₀` and a cut-off `φ` of `f` near `spt Y` define
  -- `push Y` by the formula with `φ` (a current); `push Y = 0` otherwise
  have key : ∀ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
        IsIntegerMultiplicity Y → IsCompact Y.support → Y.support ⊆ O →
          ∃ (R₀ : IMRep (univ : Set (Euclid P)) (m + 1)) (φ : Euclid P → Euclid P)
            (V K' : Set (Euclid P)), R₀.Represents Y ∧ Y.support ⊆ V ∧ IsCompact K' ∧
            ContDiff ℝ 1 φ ∧ (∀ x ∈ V, φ x = f x ∧ fderiv ℝ φ x = fderiv ℝ f x) ∧
            (∀ x, x ∉ K' → φ x = x) ∧
            ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), S ω = ∫ x in R₀.carrier,
              (R₀.mult x : ℝ) * R₀.orient x (((ω : DifferentialForm (Euclid P) (m + 1))
                (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[m + 1] := by
    intro Y
    by_cases hY : IsIntegerMultiplicity Y ∧ IsCompact Y.support ∧ Y.support ⊆ O
    · obtain ⟨⟨R₀, hR₀⟩, hK, hKO⟩ := hY
      obtain ⟨φ, V, K', -, hKV, hK', hφ, hφf, hφK'⟩ :=
        Submission.dtc_bc_lc_pf_c1_compact_perturbation P O Y.support f hO hK hKO hf
      obtain ⟨S, hS⟩ := Submission.dpf_pushforward_formula_current_exists P (m + 1) univ K' R₀ φ
        hK' (subset_univ _) hφ hφK'
      exact ⟨S, fun _ _ _ => ⟨R₀, φ, V, K', hR₀, hKV, hK', hφ, hφf, hφK', hS⟩⟩
    · exact ⟨0, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ hY⟩
  choose push hpush using key
  -- Step 3 (i): the formula with `f`, for every representation of `Y`
  have hform : ∀ (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1))
      (R : IMRep (univ : Set (Euclid P)) (m + 1)), R.Represents Y → IsCompact Y.support →
      Y.support ⊆ O → ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), push Y ω =
        ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) (m + 1))
          (f x)).compContinuousLinearMap (fderiv ℝ f x)) ∂μHE[m + 1] := by
    intro Y R hR hK hKO ω
    obtain ⟨R₀, φ, V, K', hR₀, hKV, -, -, hφf, -, hS⟩ := hpush Y ⟨R, hR⟩ hK hKO
    -- `φ = f` and `Dφ = Df` on `V ⊇ spt Y`, which contains `Hⁿ`-a.e. point of `M₀`
    have h₀ : push Y ω = ∫ x in R₀.carrier, (R₀.mult x : ℝ) * R₀.orient x
        (((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap
          (fderiv ℝ f x)) ∂μHE[m + 1] := by
      rw [hS ω]
      refine integral_congr_ae ?_
      filter_upwards [hspt Y R₀ hR₀] with x hx
      rw [(hφf x (hKV hx)).1, (hφf x (hKV hx)).2]
    -- both integrals are limits of `Y(ωⱼ)` for one sequence `ωⱼ`
    obtain ⟨ωs, hωs⟩ := Submission.dtc_bc_lc_pf_pullback_integral_extension P (m + 1) O Y.support
      f ω hO hf hK hKO
    rw [h₀]
    exact tendsto_nhds_unique (hωs Y R₀ hR₀ subset_rfl) (hωs Y R hR subset_rfl)
  refine ⟨push, fun Y R hR hK hKO => ⟨hform Y R hR hK hKO, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- Step 4 (ii): integer multiplicity by the area formula, with tangent locality from the
    -- integer multiplicity calculus (`↔` reversed)
    exact Submission.dtc_bc_lc_pf_pushforward_isIntegerMultiplicity
      (fun P n U A B hU hA hB hAB hBU hfin =>
        (Submission.cmc_imRep_locality_restrict_sub.1 P n U A B hU hA hB hAB hBU hfin).mono
          fun x hx Q => (hx Q).symm)
      P (m + 1) univ Y.support O R f (push Y) isOpen_univ (Nat.succ_pos m) hK (subset_univ _)
      (hcf.1 Y R hR).1 hO hKO hf (subset_univ _) (hform Y R hR hK hKO)
  · -- Step 5 (iii): if `spt ω` misses the compact set `f(spt Y)`, then `ω(f(x)) = 0` for
    -- `Hⁿ`-a.e. `x ∈ M`, so `push Y(ω) = 0`
    have hfK : IsCompact (f '' Y.support) := hK.image_of_continuousOn (hf.continuousOn.mono hKO)
    refine (Submission.rsd_cmr_support_subset_of_vanish P (m + 1) univ (f '' Y.support) (push Y)
      isOpen_univ hfK (subset_univ _) fun ω hω => ?_).1
    rw [hform Y R hR hK hKO ω]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hspt Y R hR] with x hx
    have h0 : (ω : DifferentialForm (Euclid P) (m + 1)) (f x) = 0 :=
      image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hω (mem_image_of_mem f hx))
    have h0' : ((ω : DifferentialForm (Euclid P) (m + 1)) (f x)).compContinuousLinearMap
        (fderiv ℝ f x) = 0 := by
      ext v
      simp [h0]
    simp [h0']
  · -- Step 6 (iv): the mass bound
    intro L hL
    exact Submission.dtc_bc_lc_pf_pushforward_mass_le P (m + 1) O f L Y (push Y) R hL hR hK hKO
      (hform Y R hR hK hKO)
  · -- Step 7 (v): `push Y` is given by the formula with `φ`, which preserves cycles
    intro hYb
    obtain ⟨R₀, φ, V, K', hR₀, -, hK', hφ, -, hφK', hS⟩ := hpush Y ⟨R, hR⟩ hK hKO
    exact Submission.dpf_pushforward_formula_boundaryVanishes P (m + 1) univ K' Y (push Y) R₀ φ
      isOpen_univ hR₀ hK' (subset_univ _) hφ hφK' hS hYb
  · -- Step 8 (B): `Y₁ − Y₂ ∈ 𝒴`, and all three formulas are limits along one sequence `ωⱼ`
    intro Y₁ Y₂ hY₁ hY₂ hK₁ hKO₁ hK₂ hKO₂
    obtain ⟨R₁₂, hR₁₂⟩ := Submission.cmc_imRep_locality_restrict_sub.2.2.1 P (m + 1) univ Y₁ Y₂
      isOpen_univ hY₁ hY₂
    obtain ⟨R₁, hR₁⟩ := hY₁
    obtain ⟨R₂, hR₂⟩ := hY₂
    have hsub : (Y₁ - Y₂).support ⊆ Y₁.support ∪ Y₂.support := (hcf.2 Y₁ Y₂).2
    have hK₁₂ : IsCompact (Y₁ - Y₂).support :=
      (hK₁.union hK₂).of_isClosed_subset (hcf.2 (Y₁ - Y₂) Y₂).1 hsub
    have hKO₁₂ : (Y₁ - Y₂).support ⊆ O := hsub.trans (union_subset hKO₁ hKO₂)
    ext ω
    obtain ⟨ωs, hωs⟩ := Submission.dtc_bc_lc_pf_pullback_integral_extension P (m + 1) O
      (Y₁.support ∪ Y₂.support) f ω hO hf (hK₁.union hK₂) (union_subset hKO₁ hKO₂)
    have h₁ := hωs Y₁ R₁ hR₁ subset_union_left
    have h₂ := hωs Y₂ R₂ hR₂ subset_union_right
    have h₁₂ := hωs (Y₁ - Y₂) R₁₂ hR₁₂ hsub
    rw [← hform Y₁ R₁ hR₁ hK₁ hKO₁ ω] at h₁
    rw [← hform Y₂ R₂ hR₂ hK₂ hKO₂ ω] at h₂
    rw [← hform (Y₁ - Y₂) R₁₂ hR₁₂ hK₁₂ hKO₁₂ ω] at h₁₂
    exact tendsto_nhds_unique h₁₂ (h₁.sub h₂)
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0

/-- **Simon Ch. 6, 3.2(3) and 2.11–2.12**: if `T = τ(M, θ, ξ)` in the open set `U`, then
(i) `M_W(T) = μ_R(W)` for every open `W`, where `μ_R = θ Hⁿ⌞M`, and (ii) `spt T = U ∩ spt μ_R`.
`M_W(T) ≤ μ_R(W)` because admissible forms pair with `ξ` to at most `1`; `μ_R(W) ≤ M_W(T)` by
smoothing the dual covector field of `ξ` (Lusin); (ii) follows from (i) alone. -/
theorem Submission.dor_imrep_massOn_eq_measure_and_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support := by
  intro P n U T R hU hR
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  exact ⟨hmass, Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass⟩
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]

/-- **Simon Ch. 6, Remark 3.2(1)**: the difference of two integer multiplicity currents in the
open set `U` is integer multiplicity.  Let `S = τ(M₁, θ₁, ξ₁)`, `T = τ(M₂, θ₂, ξ₂)`.  By the Upper
Density Theorem (Ch. 1, 3.6) the carriers have density zero at `Hⁿ`-a.e. point outside them, and
approximate tangent spaces ignore sets of density zero (Ch. 3, 1.4–1.5), so `T_yM₁ = T_yM₂` and
`ξ₂(y) = σ(y) ξ₁(y)` with a Borel sign `σ = ±1` for `Hⁿ`-a.e. `y ∈ M₁ ∩ M₂`.  Then
`S − T = τ(M, m, ζ)` with `M = (M₁ \ M₂) ∪ (M₂ \ M₁) ∪ {y ∈ M₁ ∩ M₂ : θ₁ ≠ σθ₂}` and
`(m, ζ) = (θ₁, ξ₁)`, `(θ₂, −ξ₂)`, `(|θ₁ − σθ₂|, ±ξ₁)` on the three pieces. -/
theorem Submission.dtc_isIntegerMultiplicity_sub : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n), IsOpen U → 0 < n → IsIntegerMultiplicity S → IsIntegerMultiplicity T → IsIntegerMultiplicity (S - T) := by
  classical
  intro P n U S T hU _hn hS hT
  obtain ⟨R₁, hR₁⟩ := hS
  obtain ⟨R₂, hR₂⟩ := hT
  -- Step 1: carriers are locally `Hⁿ`-finite in `U` (multiplicities are `≥ 1`)
  have hfin : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    apply setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
    intro x hx
    have := R.mult_pos x hx.1
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 this)
  -- Step 2 (F1): Upper Density Theorem (Simon 1.3.6), localized to `U`
  have F1 : ∀ A : Set (Euclid P), MeasurableSet A →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (A ∩ K) ≠ ∞) →
      ∀ᵐ y ∂(μHE[n] : Measure (Euclid P)), y ∈ U → y ∉ A →
        Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) := by
    intro A hA hAfin
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hzero : ∀ y : Euclid P,
        Poincare.SimonGMT.Chapter01.dimensionalUpperDensity
          ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) A y = 0 →
        Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) := by
      intro y h
      have hq : Tendsto (Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
          ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) A y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        apply tendsto_of_le_liminf_of_limsup_le (zero_le)
        exact h.le
      have hω0 : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) ≠ 0 :=
        (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos hn0).ne'
      have hωt : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) ≠ ∞ :=
        Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
      have h2 := ENNReal.Tendsto.const_mul hq (Or.inr hωt)
        (a := Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ))
      rw [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      simp only [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient,
        Measure.toOuterMeasure_apply]
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (le_of_lt hρ), ← mul_div_assoc,
        ENNReal.mul_div_mul_left _ _ hω0 hωt]
    -- null sets of Simon's `Hⁿ` are `μHE[n]`-null
    have bridge : ∀ Z : Set (Euclid P),
        Poincare.SimonGMT.Chapter01.simonHausdorffOuterMeasureReal (n : ℝ) Z = 0 →
          (μHE[n] : Measure (Euclid P)) Z = 0 := by
      intro Z hZ
      rw [Poincare.SimonGMT.Chapter01.simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure
        hn0] at hZ
      rw [smul_apply, smul_eq_mul] at hZ
      have hc : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) / (2 : ℝ≥0∞) ^ (n : ℝ)
          ≠ 0 :=
        ENNReal.div_ne_zero.mpr
          ⟨(Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos hn0).ne', by simp⟩
      have hH : (μH[(n : ℝ)] : Measure (Euclid P)) Z = 0 := by
        simpa using (mul_eq_zero.mp hZ).resolve_left hc
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
    -- countable cover of `U` by balls whose closures are compact subsets of `U`
    let ι := {p : Euclid P × ℝ // 0 < p.2 ∧ closedBall p.1 p.2 ⊆ U}
    obtain ⟨J, hJc, hJU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : ι => ball i.1.1 i.1.2) (fun _ => isOpen_ball)
    have hcover : U ⊆ ⋃ i : ι, ball i.1.1 i.1.2 := by
      intro x hx
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
      exact mem_iUnion.mpr ⟨⟨(x, ε / 2), half_pos hε,
        (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩, mem_ball_self (half_pos hε)⟩
    let N : ι → Set (Euclid P) := fun i => {x | x ∉ A ∩ ball i.1.1 i.1.2 ∧
      Poincare.SimonGMT.Chapter01.dimensionalUpperDensity
        ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) (A ∩ ball i.1.1 i.1.2) x ≠ 0}
    have hN : ∀ i, (μHE[n] : Measure (Euclid P)) (N i) = 0 := by
      intro i
      apply bridge
      apply Poincare.SimonGMT.Chapter01.simon_theorem_3_6 _
        (Poincare.SimonGMT.Chapter01.measure_toOuterMeasure_isBorelRegular _) hn0
      · exact le_toOuterMeasure_caratheodory _ _ (hA.inter measurableSet_ball)
      · have := hAfin (closedBall i.1.1 i.1.2) (isCompact_closedBall _ _) i.2.2
        exact lt_of_le_of_lt (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
          this.lt_top
    rw [ae_iff]
    apply measure_mono_null (t := ⋃ i ∈ J, N i)
    · intro y hy
      simp only [mem_ofPred_eq, not_imp] at hy
      obtain ⟨hyU, hyA, hnot⟩ := hy
      have hy' := hcover hyU
      rw [← hJU] at hy'
      obtain ⟨i, hiJ, hyi⟩ := mem_iUnion₂.mp hy'
      refine mem_iUnion₂.mpr ⟨i, hiJ, fun h => hyA h.1, fun hden => hnot ?_⟩
      rw [Poincare.SimonGMT.Chapter01.dimensionalUpperDensity_inter_of_mem_nhds _ _ _ _ _
        (isOpen_ball.mem_nhds hyi)] at hden
      exact hzero y hden
    · exact (measure_biUnion_null_iff hJc).mpr fun i _ => hN i
  -- Step 3 (F2): approximate tangent spaces ignore sets of zero `n`-density
  have F2 : ∀ (A A' : Set (Euclid P)) (y : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ),
      MeasurableSet A → MeasurableSet A' → 0 < s →
      μHE[n] (A ∩ closedBall y s) ≠ ∞ → μHE[n] (A' ∩ closedBall y s) ≠ ∞ →
      Tendsto (fun ρ : ℝ => μHE[n] (((A \ A') ∪ (A' \ A)) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      HasApproximateTangentSpaceAt n A y Q → HasApproximateTangentSpaceAt n A' y Q := by
    intro A A' y Q s hA hA' hs hAfin hA'fin hD hTA
    refine ⟨hTA.1, fun f => ?_⟩
    set D := (A \ A') ∪ (A' \ A) with hDdef
    have hfc : Continuous f := map_continuous f
    have hfcs : HasCompactSupport f := f.hasCompactSupport
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfcs
    obtain ⟨L₀, hL₀⟩ := hfcs.isCompact.isBounded.subset_closedBall (0 : Euclid P)
    set L := max L₀ 1 with hLdef
    have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hfL : ∀ z, z ∉ closedBall (0 : Euclid P) L → f z = 0 := by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro hzt
      exact hz (closedBall_subset_closedBall (le_max_left _ _) (hL₀ hzt))
    have hDm : MeasurableSet D := (hA.diff hA').union (hA'.diff hA)
    have hinj : ∀ r : ℝ, 0 < r → Injective (Poincare.SimonGMT.Chapter03.blowUpMap y r) := by
      intro r hr a b hab
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap] at hab
      have := smul_right_injective (Euclid P) (inv_ne_zero hr.ne') hab
      simpa using this
    have hmeasIm : ∀ r : ℝ, 0 < r → ∀ Z : Set (Euclid P), MeasurableSet Z →
        MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z) := by
      intro r hr Z hZ
      have : Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z = (fun w => r • w + y) ⁻¹' Z := by
        ext w
        simp only [mem_image, mem_preimage, Poincare.SimonGMT.Chapter03.blowUpMap]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rwa [smul_inv_smul₀ hr.ne', sub_add_cancel]
        · intro hw
          exact ⟨r • w + y, hw, by rw [add_sub_cancel_right, inv_smul_smul₀ hr.ne']⟩
      rw [this]
      exact hZ.preimage (by fun_prop)
    have hintOn : ∀ Z : Set (Euclid P), MeasurableSet Z →
        μHE[n] (Z ∩ closedBall 0 L) ≠ ∞ → IntegrableOn f Z μHE[n] := by
      intro Z hZ hZfin
      have h1 : IntegrableOn f (Z ∩ closedBall 0 L) μHE[n] :=
        Measure.integrableOn_of_bounded hZfin hfc.aestronglyMeasurable (M := C)
          (Eventually.of_forall hC)
      exact h1.of_forall_sdiff_eq_zero hZ (fun z hz => hfL z (fun h => hz.2 ⟨hz.1, h⟩))
    have hnormle : ∀ Z : Set (Euclid P), MeasurableSet Z →
        μHE[n] (Z ∩ closedBall 0 L) ≠ ∞ →
        ‖∫ z in Z, f z ∂μHE[n]‖ ≤ C * (μHE[n] : Measure (Euclid P)).real (Z ∩ closedBall 0 L) := by
      intro Z hZ hZfin
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hZ inter_subset_left
        (fun z hz => hfL z (fun h => hz.2 ⟨hz.1, h⟩))]
      exact norm_setIntegral_le_of_norm_le_const hZfin.lt_top (fun z _ => hC z)
    -- the scaling identity: reused child `regcomp_atl_blowUp_measure_scaling`
    have hscale : ∀ r : ℝ, 0 < r → ∀ Z : Set (Euclid P),
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z ∩ closedBall 0 L) =
          (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (Z ∩ closedBall y (r * L)) :=
      fun r hr Z => Submission.regcomp_atl_blowUp_measure_scaling P n y r L Z hr
    have hfinS : ∀ Z ⊆ A ∪ A', ∀ r, 0 < r → r * L ≤ s →
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z ∩ closedBall 0 L) ≠ ∞ := by
      intro Z hZ r hr hrs
      rw [hscale r hr]
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')) ?_
      apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAfin, hA'fin⟩)
      calc μHE[n] (Z ∩ closedBall y (r * L))
          ≤ μHE[n] ((A ∩ closedBall y s) ∪ (A' ∩ closedBall y s)) := by
            apply measure_mono
            rintro z ⟨hzZ, hzB⟩
            have hzB' : z ∈ closedBall y s := closedBall_subset_closedBall hrs hzB
            rcases hZ hzZ with h | h
            · exact Or.inl ⟨h, hzB'⟩
            · exact Or.inr ⟨h, hzB'⟩
        _ ≤ _ := measure_union_le _ _
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖(∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' A', f z ∂μHE[n]) -
            ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' A, f z ∂μHE[n]‖ ≤
          2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
            ENNReal.ofReal ((r * L) ^ n)).toReal) := by
      have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r * L ≤ s := by
        filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
        refine ⟨hr.1, ?_⟩
        have := hr.2
        rw [lt_div_iff₀ hL] at this
        linarith
      filter_upwards [hpos] with r ⟨hr, hrs⟩
      set η := Poincare.SimonGMT.Chapter03.blowUpMap y r with hη
      have hinjr : Injective η := hinj r hr
      have hsub1 : A' ∩ A ⊆ A ∪ A' := fun z hz => Or.inl hz.2
      have hsub2 : A' \ A ⊆ A ∪ A' := fun z hz => Or.inr hz.1
      have hsub3 : A \ A' ⊆ A ∪ A' := fun z hz => Or.inl hz.1
      have hsubD : D ⊆ A ∪ A' := union_subset hsub3 hsub2
      have hI1 := hintOn _ (hmeasIm r hr _ (hA'.inter hA)) (hfinS _ hsub1 r hr hrs)
      have hI2 := hintOn _ (hmeasIm r hr _ (hA'.diff hA)) (hfinS _ hsub2 r hr hrs)
      have hI3 := hintOn _ (hmeasIm r hr _ (hA.diff hA')) (hfinS _ hsub3 r hr hrs)
      have hsplitA' : η '' A' = η '' (A' ∩ A) ∪ η '' (A' \ A) := by
        rw [← image_union, inter_union_sdiff]
      have hsplitA : η '' A = η '' (A' ∩ A) ∪ η '' (A \ A') := by
        rw [← image_union, inter_comm, inter_union_sdiff]
      have hdisj1 : Disjoint (η '' (A' ∩ A)) (η '' (A' \ A)) :=
        (disjoint_image_iff hinjr).mpr (disjoint_sdiff_inter.symm)
      have hdisj2 : Disjoint (η '' (A' ∩ A)) (η '' (A \ A')) := by
        rw [disjoint_image_iff hinjr, inter_comm]
        exact disjoint_sdiff_inter.symm
      rw [hsplitA', hsplitA, setIntegral_union hdisj1 (hmeasIm r hr _ (hA'.diff hA)) hI1 hI2,
        setIntegral_union hdisj2 (hmeasIm r hr _ (hA.diff hA')) hI1 hI3]
      have hfinD := hfinS D hsubD r hr hrs
      have hmono2 : (μHE[n] : Measure (Euclid P)).real (η '' (A' \ A) ∩ closedBall 0 L) ≤
          (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
        measureReal_mono (inter_subset_inter_left _ (image_mono subset_union_right)) hfinD
      have hmono3 : (μHE[n] : Measure (Euclid P)).real (η '' (A \ A') ∩ closedBall 0 L) ≤
          (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
        measureReal_mono (inter_subset_inter_left _ (image_mono subset_union_left)) hfinD
      have hn2 := hnormle _ (hmeasIm r hr _ (hA'.diff hA)) (hfinS _ hsub2 r hr hrs)
      have hn3 := hnormle _ (hmeasIm r hr _ (hA.diff hA')) (hfinS _ hsub3 r hr hrs)
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      have hkey : (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) =
          L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) / ENNReal.ofReal ((r * L) ^ n)).toReal := by
        have hfin' : μHE[n] (D ∩ closedBall y (r * L)) ≠ ∞ := by
          have h0 := hfinD
          rw [hscale r hr] at h0
          have ha0 : (ENNReal.ofReal r)⁻¹ ^ n ≠ 0 :=
            pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
          exact fun hb => h0 (ENNReal.mul_eq_top.mpr (Or.inl ⟨ha0, hb⟩))
        rw [measureReal_def, hscale r hr, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal hr.le, mul_pow]
        have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
        have hLn : L ^ n ≠ 0 := pow_ne_zero n hL.ne'
        rw [inv_pow, mul_div_assoc', mul_comm (L ^ n), mul_div_mul_right _ _ hLn, div_eq_inv_mul]
      calc ‖(∫ z in η '' (A' ∩ A), f z ∂μHE[n]) + (∫ z in η '' (A' \ A), f z ∂μHE[n]) -
            ((∫ z in η '' (A' ∩ A), f z ∂μHE[n]) + ∫ z in η '' (A \ A'), f z ∂μHE[n])‖
          = ‖(∫ z in η '' (A' \ A), f z ∂μHE[n]) - ∫ z in η '' (A \ A'), f z ∂μHE[n]‖ := by
            congr 1; ring
        _ ≤ ‖∫ z in η '' (A' \ A), f z ∂μHE[n]‖ + ‖∫ z in η '' (A \ A'), f z ∂μHE[n]‖ :=
            norm_sub_le _ _
        _ ≤ C * (μHE[n] : Measure (Euclid P)).real (η '' (A' \ A) ∩ closedBall 0 L) +
            C * (μHE[n] : Measure (Euclid P)).real (η '' (A \ A') ∩ closedBall 0 L) :=
            add_le_add hn2 hn3
        _ ≤ C * (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) +
            C * (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
            add_le_add (mul_le_mul_of_nonneg_left hmono2 hC0)
              (mul_le_mul_of_nonneg_left hmono3 hC0)
        _ = 2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
              ENNReal.ofReal ((r * L) ^ n)).toReal) := by
            rw [hkey]; ring
    have hlim : Tendsto (fun r : ℝ => 2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
        ENNReal.ofReal ((r * L) ^ n)).toReal)) (𝓝[>] 0) (𝓝 0) := by
      have hmap : Tendsto (fun r : ℝ => r * L) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have h0 : Tendsto (fun r : ℝ => r * L) (𝓝 0) (𝓝 (0 * L)) :=
            (continuous_id.mul continuous_const).tendsto 0
          rw [zero_mul] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hr hL
      have h1 := hD.comp hmap
      have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      have h3 := (h2.const_mul (L ^ n)).const_mul (2 * C)
      simpa [Function.comp_def] using h3
    have hdiff := squeeze_zero_norm' hbound hlim
    have h3 := (hTA.2 f).add hdiff
    simp only [add_zero, add_sub_cancel] at h3
    exact h3
  -- Steps 2–3 combined: a.e. on `A ∩ B` the tangent spaces of `A` and `B` coincide
  have F3 : ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → A ⊆ U → B ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (A ∩ K) ≠ ∞) →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) →
      ∀ᵐ y ∂(μHE[n].restrict (A ∩ B)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n A y Q ↔ HasApproximateTangentSpaceAt n B y Q := by
    intro A B hA hB hAU hBU hAfin hBfin
    set D : Set (Euclid P) := (A \ B) ∪ (B \ A) with hD
    have hDmeas : MeasurableSet D := (hA.diff hB).union (hB.diff hA)
    have hDfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (D ∩ K) ≠ ∞ := by
      intro K hK hKU
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hAfin K hK hKU, hBfin K hK hKU⟩) ?_
      calc μHE[n] (D ∩ K) ≤ μHE[n] ((A ∩ K) ∪ (B ∩ K)) := by
            apply measure_mono
            rintro x ⟨hx | hx, hxK⟩
            · exact Or.inl ⟨hx.1, hxK⟩
            · exact Or.inr ⟨hx.1, hxK⟩
        _ ≤ μHE[n] (A ∩ K) + μHE[n] (B ∩ K) := measure_union_le _ _
    have h1 := F1 D hDmeas hDfin
    have h1' : ∀ᵐ y ∂(μHE[n].restrict (A ∩ B)), y ∈ U → y ∉ D →
        Tendsto (fun ρ : ℝ => μHE[n] (D ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) :=
      ae_restrict_of_ae h1
    filter_upwards [h1', ae_restrict_mem (hA.inter hB)] with y hy hyAB
    have hyU : y ∈ U := hAU hyAB.1
    have hyD : y ∉ D := by
      rintro (h | h)
      · exact h.2 hyAB.2
      · exact h.2 hyAB.1
    have hdens := hy hyU hyD
    obtain ⟨s, hs, hsU⟩ : ∃ s > 0, closedBall y s ⊆ U := by
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hyU
      exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
    have hK : IsCompact (closedBall y s) := isCompact_closedBall y s
    have hAs := hAfin _ hK hsU
    have hBs := hBfin _ hK hsU
    intro Q
    constructor
    · intro hQ
      exact F2 A B y Q s hA hB hs hAs hBs hdens hQ
    · intro hQ
      have hdens' : Tendsto (fun ρ : ℝ => μHE[n] (((B \ A) ∪ (A \ B)) ∩ closedBall y ρ) /
          ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
        simpa only [hD, Set.union_comm] using hdens
      exact F2 B A y Q s hB hA hs hBs hAs hdens' hQ
  -- Step 6 with Step 4 (reused child `rsdic_unitOrientation_eq_or_eq_neg`):
  -- `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hov : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)),
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    have hL := F3 R₁.carrier R₂.carrier R₁.measurableSet_carrier R₂.measurableSet_carrier
      R₁.carrier_subset R₂.carrier_subset (hfin R₁) (hfin R₂)
    have ho₁ : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R₁.carrier x Q ∧ IsUnitOrientationOf (R₁.orient x) Q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left R₁.orients
    have ho₂ : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R₂.carrier x Q ∧ IsUnitOrientationOf (R₂.orient x) Q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right R₂.orients
    filter_upwards [hL, ho₁, ho₂] with x hx h₁ h₂
    obtain ⟨Q₁, hT₁, hO₁⟩ := h₁
    obtain ⟨Q₂, hT₂, hO₂⟩ := h₂
    have hT₁' : HasApproximateTangentSpaceAt n R₂.carrier x Q₁ := (hx Q₁).1 hT₁
    have hQ : Q₁ = Q₂ := hT₁'.unique hT₂
    subst hQ
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₁ hO₁ hO₂
  -- Step 8: IMRep fields for sub-data of `R₁`, `R₂`
  have recombine : ∀ (M : Set (Euclid P)) (m : Euclid P → ℕ) (ζ : Euclid P → MultiVector P n),
      MeasurableSet M → M ⊆ R₁.carrier ∪ R₂.carrier → Measurable m → (∀ x ∈ M, 0 < m x) →
      (∀ x ∈ M, m x ≤ R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) →
      AEStronglyMeasurable ζ (μHE[n].restrict M) →
      (∀ᵐ x ∂(μHE[n].restrict (M ∩ R₁.carrier)), ζ x = R₁.orient x ∨ ζ x = -R₁.orient x) →
      (∀ᵐ x ∂(μHE[n].restrict (M \ R₁.carrier)), ζ x = R₂.orient x ∨ ζ x = -R₂.orient x) →
      ∃ R : IMRep U n, R.carrier = M ∧ R.mult = m ∧ R.orient = ζ := by
    intro M m ζ hM hMsub hm hmpos hmle hζ h₁ h₂
    have hMU : M ⊆ U := hMsub.trans (union_subset R₁.carrier_subset R₂.carrier_subset)
    have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M ∩ K) ≠ ∞ := by
      intro K hK hKU
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin R₁ K hK hKU, hfin R₂ K hK hKU⟩) ?_
      calc μHE[n] (M ∩ K) ≤ μHE[n] ((R₁.carrier ∩ K) ∪ (R₂.carrier ∩ K)) := by
            apply measure_mono
            rintro x ⟨hx, hxK⟩
            rcases hMsub hx with h | h
            · exact Or.inl ⟨h, hxK⟩
            · exact Or.inr ⟨h, hxK⟩
        _ ≤ _ := measure_union_le _ _
    have hneg : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ξ Q → IsUnitOrientationOf (-ξ) Q := by
      rintro ξ Q ⟨τ, hτ, hspan, h | h⟩
      · exact ⟨τ, hτ, hspan, Or.inr fun α => by simp [h α]⟩
      · exact ⟨τ, hτ, hspan, Or.inl fun α => by simp [h α]⟩
    have hpm : ∀ (ξ ξ' : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ξ' Q → (ξ = ξ' ∨ ξ = -ξ') → IsUnitOrientationOf ξ Q := by
      rintro ξ ξ' Q hO (h | h)
      · rw [h]; exact hO
      · rw [h]; exact hneg _ _ hO
    have horient : ∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q := by
      have key : ∀ᵐ x ∂(μHE[n].restrict ((M ∩ R₁.carrier) ∪ (M \ R₁.carrier))),
          ∃ Q : Submodule ℝ (Euclid P),
            HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q := by
        rw [ae_restrict_union_iff]
        constructor
        · have hL := F3 M R₁.carrier hM R₁.measurableSet_carrier hMU R₁.carrier_subset hMfin
            (hfin R₁)
          have ho := ae_restrict_of_ae_restrict_of_subset (inter_subset_right (s := M))
            R₁.orients
          filter_upwards [hL, ho, h₁] with x hx hox hζx
          obtain ⟨Q, hTQ, hO⟩ := hox
          exact ⟨Q, (hx Q).2 hTQ, hpm _ _ _ hO hζx⟩
        · have hL := F3 M R₂.carrier hM R₂.measurableSet_carrier hMU R₂.carrier_subset hMfin
            (hfin R₂)
          have hsub : M \ R₁.carrier ⊆ M ∩ R₂.carrier :=
            fun x hx => ⟨hx.1, (hMsub hx.1).resolve_left hx.2⟩
          have hL' := ae_restrict_of_ae_restrict_of_subset hsub hL
          have ho := ae_restrict_of_ae_restrict_of_subset (hsub.trans inter_subset_right)
            R₂.orients
          filter_upwards [hL', ho, h₂] with x hx hox hζx
          obtain ⟨Q, hTQ, hO⟩ := hox
          exact ⟨Q, (hx Q).2 hTQ, hpm _ _ _ hO hζx⟩
      rwa [inter_union_sdiff] at key
    have hrect : CountablyRectifiable n M := by
      have hU12 : CountablyRectifiable n
          (⋃ i : ℕ, (if i = 0 then R₁.carrier else R₂.carrier)) := by
        apply Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
        intro i
        split_ifs
        · exact R₁.rectifiable
        · exact R₂.rectifiable
      apply hU12.mono
      intro x hx
      rcases hMsub hx with h | h
      · exact mem_iUnion.2 ⟨0, by simpa using h⟩
      · exact mem_iUnion.2 ⟨1, by simpa using h⟩
    have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
        ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
      intro K hK hKU
      have hm1 : Measurable fun x => (R₁.mult x : ℝ≥0∞) :=
        measurable_from_nat.comp R₁.measurable_mult
      have hS1 : MeasurableSet (R₁.carrier ∩ K) :=
        R₁.measurableSet_carrier.inter hK.measurableSet
      have hS2 : MeasurableSet (R₂.carrier ∩ K) :=
        R₂.measurableSet_carrier.inter hK.measurableSet
      have hbound : ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n] ≤
          ∫⁻ x in R₁.carrier ∩ K, (R₁.mult x : ℝ≥0∞) ∂μHE[n] +
            ∫⁻ x in R₂.carrier ∩ K, (R₂.mult x : ℝ≥0∞) ∂μHE[n] := by
        calc ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n]
            ≤ ∫⁻ x in M ∩ K, ((R₁.carrier ∩ K).indicator (fun x => (R₁.mult x : ℝ≥0∞)) x +
                (R₂.carrier ∩ K).indicator (fun x => (R₂.mult x : ℝ≥0∞)) x) ∂μHE[n] := by
              apply setLIntegral_mono' (hM.inter hK.measurableSet)
              intro x hx
              have h := hmle x hx.1
              have hxK := hx.2
              by_cases h1 : x ∈ R₁.carrier <;> by_cases h2 : x ∈ R₂.carrier <;>
                simp [h1, h2, hxK] at h ⊢ <;> exact_mod_cast h
          _ ≤ ∫⁻ x, ((R₁.carrier ∩ K).indicator (fun x => (R₁.mult x : ℝ≥0∞)) x +
                (R₂.carrier ∩ K).indicator (fun x => (R₂.mult x : ℝ≥0∞)) x) ∂μHE[n] :=
              setLIntegral_le_lintegral _ _
          _ = _ := by
              rw [lintegral_add_left (hm1.indicator hS1), lintegral_indicator hS1,
                lintegral_indicator hS2]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨R₁.locallyIntegrable_mult K hK hKU,
        R₂.locallyIntegrable_mult K hK hKU⟩) hbound
    exact ⟨⟨M, m, ζ, hM, hMU, hrect, hm, hmpos, hint, hζ, horient⟩, rfl, rfl, rfl⟩
  -- Steps 5–7: Borel orientations, Borel sign, the new data `(M, m, ζ)`
  obtain ⟨R, hR⟩ : ∃ R : IMRep U n, ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      ∀ α : Covector (Euclid P) n,
        R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y α) x =
          R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) * R₁.orient y α) x -
            R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) * R₂.orient y α) x := by
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) := by
      let M : MetricSpace (MultiVector P n) := inferInstance
      have h1 : @TopologicalSpace.PseudoMetrizableSpace (MultiVector P n)
          (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) :=
        @UniformSpace.pseudoMetrizableSpace (MultiVector P n) PseudoMetricSpace.toUniformSpace
          inferInstance
      have h2 : @T0Space (MultiVector P n)
          (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) := inferInstance
      exact @TopologicalSpace.MetrizableSpace.mk _ _ h1 h2
    have : ContinuousNeg (MultiVector P n) := by
      exact @IsTopologicalAddGroup.toContinuousNeg _ _ _ ContinuousLinearMap.isTopologicalAddGroup
    set M₁ := R₁.carrier with hM₁def
    set M₂ := R₂.carrier with hM₂def
    have hM₁ : MeasurableSet M₁ := R₁.measurableSet_carrier
    have hM₂ : MeasurableSet M₂ := R₂.measurableSet_carrier
    set ξt₁ := R₁.aestronglyMeasurable_orient.mk R₁.orient with hξt₁def
    set ξt₂ := R₂.aestronglyMeasurable_orient.mk R₂.orient with hξt₂def
    have hs₁ : StronglyMeasurable ξt₁ := R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk
    have hs₂ : StronglyMeasurable ξt₂ := R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk
    have he₁ : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₁ → R₁.orient x = ξt₁ x :=
      (ae_restrict_iff' hM₁).1 R₁.aestronglyMeasurable_orient.ae_eq_mk
    have he₂ : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₂ → R₂.orient x = ξt₂ x :=
      (ae_restrict_iff' hM₂).1 R₂.aestronglyMeasurable_orient.ae_eq_mk
    have hov' : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₁ ∩ M₂ →
        R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x :=
      (ae_restrict_iff' (hM₁.inter hM₂)).1 hov
    set σ : Euclid P → ℤ := fun x => if ξt₂ x = ξt₁ x then 1 else -1 with hσdef
    have hσmeas : Measurable σ :=
      Measurable.ite (hs₂.measurableSet_eq_fun hs₁) measurable_const measurable_const
    set d : Euclid P → ℤ := fun x => (R₁.mult x : ℤ) - σ x * (R₂.mult x : ℤ) with hddef
    have hdmeas : Measurable d := by
      have h1 : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
      have h2 : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
      exact h1.sub (hσmeas.mul h2)
    set G : Set (Euclid P) := {x | x ∈ M₁ ∩ M₂ ∧ d x ≠ 0} with hGdef
    have hG : MeasurableSet G :=
      (hM₁.inter hM₂).inter (hdmeas (measurableSet_singleton 0).compl)
    set M : Set (Euclid P) := (M₁ \ M₂) ∪ (M₂ \ M₁) ∪ G with hMdef
    have hM : MeasurableSet M := ((hM₁.diff hM₂).union (hM₂.diff hM₁)).union hG
    set m : Euclid P → ℕ := fun x => if x ∈ M₁ \ M₂ then R₁.mult x
      else if x ∈ M₂ \ M₁ then R₂.mult x else if x ∈ M₁ ∩ M₂ then (d x).natAbs else 0
      with hmdef
    set ζ : Euclid P → MultiVector P n := fun x => if x ∈ M₁ \ M₂ then ξt₁ x
      else if x ∈ M₂ \ M₁ then -ξt₂ x else if 0 < d x then ξt₁ x else -ξt₁ x with hζdef
    have hmmeas : Measurable m := by
      refine Measurable.ite (hM₁.diff hM₂) R₁.measurable_mult
        (Measurable.ite (hM₂.diff hM₁) R₂.measurable_mult
          (Measurable.ite (hM₁.inter hM₂)
            ((Measurable.of_discrete (f := Int.natAbs)).comp hdmeas) measurable_const))
    have hζmeas : StronglyMeasurable ζ := by
      refine StronglyMeasurable.ite (hM₁.diff hM₂) hs₁
        (StronglyMeasurable.ite (hM₂.diff hM₁) hs₂.neg (StronglyMeasurable.ite ?_ hs₁ hs₁.neg))
      exact hdmeas (measurableSet_Ioi (a := (0 : ℤ)))
    have hMsub : M ⊆ M₁ ∪ M₂ := by
      rintro x ((h | h) | h)
      · exact Or.inl h.1
      · exact Or.inr h.1
      · exact Or.inl h.1.1
    have hmpos : ∀ x ∈ M, 0 < m x := by
      rintro x ((h | h) | h)
      · simp only [hmdef, ite_eq_left h]; exact R₁.mult_pos x h.1
      · have hn : x ∉ M₁ \ M₂ := fun h' => h.2 h'.1
        simp only [hmdef, ite_eq_right hn, ite_eq_left h]; exact R₂.mult_pos x h.1
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hmdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left h.1]
        exact Int.natAbs_pos.2 h.2
    have hσpm : ∀ x, σ x = 1 ∨ σ x = -1 := by
      intro x; simp only [hσdef]; split_ifs <;> simp
    have hmle : ∀ x ∈ M, m x ≤ M₁.indicator R₁.mult x + M₂.indicator R₂.mult x := by
      rintro x ((h | h) | h)
      · simp only [hmdef, ite_eq_left h, indicator_of_mem h.1, indicator_of_notMem h.2]; omega
      · have hn : x ∉ M₁ \ M₂ := fun h' => h.2 h'.1
        simp only [hmdef, ite_eq_right hn, ite_eq_left h, indicator_of_mem h.1, indicator_of_notMem h.2]
        omega
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hmdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left h.1, indicator_of_mem h.1.1,
          indicator_of_mem h.1.2]
        simp only [hddef]
        rcases hσpm x with hs | hs <;> rw [hs] <;> omega
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M ∩ M₁)), ζ x = R₁.orient x ∨ ζ x = -R₁.orient x := by
      rw [ae_restrict_iff' (hM.inter hM₁)]
      filter_upwards [he₁] with x hx hxM
      have hxe := hx hxM.2
      rcases hxM.1 with (h | h) | h
      · left; simp only [hζdef, ite_eq_left h]; exact hxe.symm
      · exact absurd hxM.2 h.2
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hζdef, ite_eq_right hn1, ite_eq_right hn2]
        split_ifs
        · left; exact hxe.symm
        · right; rw [hxe]
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M \ M₁)), ζ x = R₂.orient x ∨ ζ x = -R₂.orient x := by
      rw [ae_restrict_iff' (hM.diff hM₁)]
      filter_upwards [he₂] with x hx hxM
      have hx2 : x ∈ M₂ \ M₁ := ⟨(hMsub hxM.1).resolve_left hxM.2, hxM.2⟩
      have hn1 : x ∉ M₁ \ M₂ := fun h' => hxM.2 h'.1
      right; simp only [hζdef, ite_eq_right hn1, ite_eq_left hx2]; rw [hx hx2.1]
    obtain ⟨R, hRc, hRm, hRo⟩ := recombine M m ζ hM hMsub hmmeas hmpos hmle
      hζmeas.aestronglyMeasurable h₁ h₂
    refine ⟨R, ?_⟩
    rw [hRc, hRm, hRo]
    filter_upwards [he₁, he₂, hov'] with x hx₁ hx₂ hx₃
    intro α
    by_cases hA : x ∈ M₁ <;> by_cases hB : x ∈ M₂
    · -- overlap
      have hAB : x ∈ M₁ ∩ M₂ := ⟨hA, hB⟩
      have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 hB
      have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 hA
      have e₁ := hx₁ hA
      have e₂ := hx₂ hB
      have hsig : R₂.orient x α = ((σ x : ℤ) : ℝ) * R₁.orient x α := by
        rcases hx₃ hAB with h | h
        · have : ξt₂ x = ξt₁ x := by rw [← e₁, ← e₂, h]
          simp only [hσdef, ite_eq_left this]; simp [h]
        · by_cases hq : ξt₂ x = ξt₁ x
          · have : R₂.orient x = R₁.orient x := by rw [e₁, e₂, hq]
            simp only [hσdef, ite_eq_left hq]; simp [this]
          · simp only [hσdef, ite_eq_right hq]; simp [h]
      rw [indicator_of_mem hA, indicator_of_mem hB, hsig]
      have hcoef : (R₁.mult x : ℝ) * R₁.orient x α -
          (R₂.mult x : ℝ) * (((σ x : ℤ) : ℝ) * R₁.orient x α) =
          ((d x : ℤ) : ℝ) * R₁.orient x α := by
        simp only [hddef]; push_cast; ring
      rw [hcoef]
      rcases lt_trichotomy (d x) 0 with hd | hd | hd
      · have hxM : x ∈ M := Or.inr ⟨hAB, hd.ne⟩
        rw [indicator_of_mem hxM]
        simp only [hmdef, hζdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left hAB, ite_eq_right (not_lt.2 hd.le)]
        have hc : (((d x).natAbs : ℕ) : ℝ) = -((d x : ℤ) : ℝ) := by
          have h1 : ((d x).natAbs : ℤ) = -(d x) := Int.ofNat_natAbs_of_nonpos hd.le
          have h2 : ((((d x).natAbs : ℕ) : ℤ) : ℝ) = ((-(d x) : ℤ) : ℝ) := by rw [h1]
          simpa using h2
        rw [hc, neg_apply, e₁]; ring
      · have hxM : x ∉ M := by
          rintro ((h | h) | h)
          · exact hn1 h
          · exact hn2 h
          · exact h.2 hd
        rw [indicator_of_notMem hxM, hd]; simp
      · have hxM : x ∈ M := Or.inr ⟨hAB, hd.ne'⟩
        rw [indicator_of_mem hxM]
        simp only [hmdef, hζdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left hAB, ite_eq_left hd]
        have hc : (((d x).natAbs : ℕ) : ℝ) = ((d x : ℤ) : ℝ) := by
          have h1 : ((d x).natAbs : ℤ) = d x := Int.natAbs_of_nonneg hd.le
          have h2 : ((((d x).natAbs : ℕ) : ℤ) : ℝ) = ((d x : ℤ) : ℝ) := by rw [h1]
          simpa using h2
        rw [hc, e₁]
    · -- only in `M₁`
      have h : x ∈ M₁ \ M₂ := ⟨hA, hB⟩
      have hxM : x ∈ M := Or.inl (Or.inl h)
      rw [indicator_of_mem hxM, indicator_of_mem hA, indicator_of_notMem hB, sub_zero]
      simp only [hmdef, hζdef, ite_eq_left h]
      rw [hx₁ hA]
    · -- only in `M₂`
      have h : x ∈ M₂ \ M₁ := ⟨hB, hA⟩
      have hn : x ∉ M₁ \ M₂ := fun h' => hA h'.1
      have hxM : x ∈ M := Or.inl (Or.inr h)
      rw [indicator_of_mem hxM, indicator_of_notMem hA, indicator_of_mem hB, zero_sub]
      simp only [hmdef, hζdef, ite_eq_right hn, ite_eq_left h]
      rw [hx₂ hB, neg_apply]; ring
    · -- outside both
      have hxM : x ∉ M := fun h => (hMsub h).elim hA hB
      rw [indicator_of_notMem hxM, indicator_of_notMem hA, indicator_of_notMem hB, sub_zero]
  -- Step 9 (reused child `rsdic_imrep_action_int_combination` with `p₁ = 1`, `p₂ = -1`)
  have hRv : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
        ((1 : ℤ) : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x +
          ((-1 : ℤ) : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
    filter_upwards [hR] with x hx
    ext α
    have h := hx α
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases h0 : x ∈ R.carrier <;> by_cases h1 : x ∈ R₁.carrier <;>
      by_cases h2 : x ∈ R₂.carrier <;>
      simp only [indicator_of_mem, indicator_of_notMem, h0, h1, h2, not_false_eq_true,
        smul_apply, smul_eq_mul, zero_apply] at h ⊢ <;> push_cast <;> linarith
  refine ⟨R, fun ω => ?_⟩
  rw [Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R 1 (-1) hRv ω, ← hR₁ ω,
    ← hR₂ ω]
  have hsub : (S - T) ω = S ω - T ω := rfl
  rw [hsub]
  push_cast
  ring
/-- **Simon Ch. 6, 3.2(3)**, localized: if `S = τ(RS)` and `T = τ(RT)` in `ℝᴾ` agree on every test
form supported in the open set `O`, then `μ_S⌞O = μ_T⌞O`.  Admissible forms for `M_W` with
`W ⊆ O` are supported in `O`, so `μ_S(W) = M_W(S) = M_W(T) = μ_T(W)` for open `W ⊆ O`; both
measures are finite on balls, and open sets form a generating π-system. -/
theorem Submission.idtp_fons_cs_sp_measure_restrict_eq_of_agree : ∀ (P m : ℕ) (S T : GeometricCurrentOn (univ : Set (Euclid P)) m) (RS RT : IMRep (univ : Set (Euclid P)) m) (O : Set (Euclid P)), IsOpen O → RS.Represents S → RT.Represents T → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, tsupport (ω : DifferentialForm (Euclid P) m) ⊆ O → S ω = T ω) → RS.measure.restrict O = RT.measure.restrict O := by
  intro P m S T RS RT O hO hRS hRT hST
  -- Step 1: `M_W(S) = M_W(T)` for `W ⊆ O`, the admissible forms being supported in `O`
  have hmass : ∀ W : Set (Euclid P), W ⊆ O → S.massOn W = T.massOn W := fun W hW =>
    congrArg sSup (Set.image_congr fun ω hω => by rw [hST ω (hω.1.trans hW)])
  -- Step 2: `μ_S(W) = M_W(S) = M_W(T) = μ_T(W)` for open `W ⊆ O`
  have hopen : ∀ W : Set (Euclid P), IsOpen W → W ⊆ O → RS.measure W = RT.measure W := by
    intro W hWo hWO
    rw [← (Submission.dor_imrep_massOn_eq_measure_and_support P m univ S RS isOpen_univ hRS).1 W hWo,
      ← (Submission.dor_imrep_massOn_eq_measure_and_support P m univ T RT isOpen_univ hRT).1 W hWo]
    exact hmass W hWO
  -- Step 3: `μ_R` is finite on closed balls (`θ` is locally `Hᵐ`-integrable)
  have hfin : ∀ (R : IMRep (univ : Set (Euclid P)) m) (r : ℝ), R.measure (closedBall 0 r) ≠ ∞ := by
    intro R r
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall 0 r) (subset_univ _)
  -- Step 4: the open sets form a generating π-system covered by the balls `B(0, i + 1)`
  refine Measure.ext_of_generateFrom_of_iUnion {s : Set (Euclid P) | IsOpen s}
    (fun i : ℕ => ball (0 : Euclid P) (i + 1)) BorelSpace.measurable_eq isPiSystem_isOpen
    (iUnion_ball_nat_succ 0) (fun _ => isOpen_ball (x := (0 : Euclid P))) (fun i => ?_)
    (fun G (hG : IsOpen G) => ?_)
  · rw [Measure.restrict_apply measurableSet_ball]
    exact ne_top_of_le_ne_top (hfin RS (i + 1))
      (measure_mono (inter_subset_left.trans ball_subset_closedBall))
  · rw [Measure.restrict_apply hG.measurableSet, Measure.restrict_apply hG.measurableSet]
    exact hopen _ (hG.inter hO) inter_subset_right
/-- **Orthogonal projection does not increase mass** (Simon 7.3.1, footnote 2; the push-forward
`f_# T(ω) = ∫ ⟨ω(f(x)), dfₓ# ξ(x)⟩ dμ_T(x)` of Ch. 6, 2.24(2); dimension reduction for 7.3.3).
Let `q` be the orthogonal projection onto `V`, `T = τ(M_T, θ_T, ξ_T)` with `μ_T(ℝᴾ \ V) = 0`,
`X = τ(M_X, θ_X, ξ_X)` with `μ_X(ℝᴾ \ K) = 0` for a compact `K`, and `S' = T + q_# X`, i.e.
`S'(ω) = T(ω) + τ(M_X, θ_X, ξ_X)(q^# ω)`.  The integer combination `R = (M, θ, ξ)` with
`1_M θ ξ = 1_{M_T} θ_T ξ_T + 1_{M_X} θ_X ξ_X` `Hᵐ`-a.e. has
`τ(R)(β) = τ(M_T, θ_T, ξ_T)(β) + τ(M_X, θ_X, ξ_X)(β)` whenever both pairings are integrable
(pairing bound).  This holds for test forms, so `R` represents `T + X`, and for `q^# ω`: `M_T`
lies a.e. in `V`, where `q^# ω` vanishes off `spt ω`, and `M_X` lies a.e. in `K`.  As
`μ_T(ℝᴾ \ V) = 0`, `τ(M_T, θ_T, ξ_T)(q^# ω) = T(ω)`, hence `S'(ω) = τ(R)(q^# ω)`.  A unit
orientation satisfies `|⟨α ∘ Λᵐq, ξ⟩| ≤ |α|_E ‖q‖ᵐ ≤ |α|_E` (Hadamard, `‖q‖ ≤ 1`), so for `ω`
with `spt ω ⊆ O` and `|ω|_E ≤ 1`, `S'(ω) ≤ ∫_{M ∩ q⁻¹(spt ω)} θ dHᵐ ≤ μ_R(q⁻¹(O))`. -/
theorem Submission.idtp_fons_cs_sp_projected_massOn_le : ∀ (P m : ℕ) (T X S' : GeometricCurrentOn (univ : Set (Euclid P)) m) (RT RX : IMRep (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)) (K : Set (Euclid P)), RT.Represents T → RX.Represents X → RT.measure ((V : Set (Euclid P))ᶜ) = 0 → IsCompact K → RX.measure Kᶜ = 0 → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, S' ω = T ω + RX.action (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m))) → ∃ R : IMRep (univ : Set (Euclid P)) m, (∀ ω : TestFormOn (univ : Set (Euclid P)) m, R.action (ω : DifferentialForm (Euclid P) m) = T ω + X ω) ∧ ∀ O : Set (Euclid P), S'.massOn O ≤ R.measure (V.starProjection ⁻¹' O) := by
  intro P m T X S' RT RX V K hRT hRX hTV hK hXK hS'
  -- Step 1: if `μ_{R'}(ℝᴾ \ C) = 0`, then `Hᵐ⌞M'`-a.e. point lies in `C`, as `θ' ≥ 1` on `M'`
  have hlive : ∀ (R' : IMRep (univ : Set (Euclid P)) m) (C : Set (Euclid P)), R'.measure Cᶜ = 0 →
      ∀ᵐ x ∂(μHE[m].restrict R'.carrier), x ∈ C := by
    intro R' C hC
    have hac : μHE[m].restrict R'.carrier ≪ R'.measure :=
      withDensity_absolutelyContinuous' (f := fun x => (R'.mult x : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by
          filter_upwards [ae_restrict_mem R'.measurableSet_carrier] with x hx
          exact Nat.cast_ne_zero.2 (R'.mult_pos x hx).ne')
    exact ae_iff.2 (hac hC)
  -- Step 2: integrability of `θ' ⟨β, ξ'⟩` on `M'` for a continuous bounded `β` that vanishes
  -- `Hᵐ⌞M'`-a.e. off a compact `C`: apply the pairing bound to `1_C β`, which equals `β` a.e.
  have hint_of : ∀ (R' : IMRep (univ : Set (Euclid P)) m) (β : DifferentialForm (Euclid P) m)
      (C : Set (Euclid P)) (B : ℝ), Continuous β → (∀ x, ‖β x‖ ≤ B) → IsCompact C →
      (∀ᵐ x ∂(μHE[m].restrict R'.carrier), x ∉ C → β x = 0) →
      Integrable (fun x => (R'.mult x : ℝ) * R'.orient x (β x)) (μHE[m].restrict R'.carrier) := by
    intro R' β C B hβ hB hC h0
    refine (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P m univ C R' (C.indicator β) B hC
      (subset_univ C) (hβ.aestronglyMeasurable.indicator hC.isClosed.measurableSet)
      (fun x hx => indicator_of_notMem hx β)
      (fun x => (norm_indicator_le_norm_self β x).trans (hB x))).1.congr ?_
    filter_upwards [h0] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC]
    · rw [indicator_of_notMem hxC, hx hxC]
  -- Step 3: the integer combination `R` with `1_M θ ξ = 1_{M_T} θ_T ξ_T + 1_{M_X} θ_X ξ_X` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P m univ RT RX 1 1 isOpen_univ
  -- Step 4: `τ(R)(β) = τ(RT)(β) + τ(RX)(β)` when both pairings are integrable, since
  -- `τ(R')(β) = ∫ ⟨β, 1_{M'} θ' ξ'⟩ dHᵐ` for every `R'`
  have hadd : ∀ β : DifferentialForm (Euclid P) m,
      Integrable (fun x => (RT.mult x : ℝ) * RT.orient x (β x)) (μHE[m].restrict RT.carrier) →
      Integrable (fun x => (RX.mult x : ℝ) * RX.orient x (β x)) (μHE[m].restrict RX.carrier) →
      R.action β = RT.action β + RX.action β := by
    intro β hT hX
    have hfun : ∀ R' : IMRep (univ : Set (Euclid P)) m,
        (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (β x)) =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) * R'.orient y (β y)) := by
      intro R'
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    have hact : ∀ R' : IMRep (univ : Set (Euclid P)) m, R'.action β =
        ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x (β x) ∂μHE[m] := by
      intro R'
      rw [hfun R', integral_indicator R'.measurableSet_carrier]
      rfl
    have hint : ∀ R' : IMRep (univ : Set (Euclid P)) m,
        Integrable (fun x => (R'.mult x : ℝ) * R'.orient x (β x)) (μHE[m].restrict R'.carrier) →
        Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
          (β x)) μHE[m] := by
      intro R' h
      rw [hfun R', integrable_indicator_iff R'.measurableSet_carrier]
      exact h
    rw [hact R, hact RT, hact RX, ← integral_add (hint RT hT) (hint RX hX)]
    refine integral_congr_ae ?_
    filter_upwards [hR] with x hx
    rw [hx]
    simp
  -- Step 5: a test form is continuous, bounded and vanishes off its compact support, so `R`
  -- represents `T + X`
  have htest : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
      R.action (ω : DifferentialForm (Euclid P) m) =
        RT.action (ω : DifferentialForm (Euclid P) m) +
          RX.action (ω : DifferentialForm (Euclid P) m) := by
    intro ω
    obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
    have hωc : Continuous (ω : DifferentialForm (Euclid P) m) := ContDiff.continuous hsmooth
    obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support hcpt
    have h0 : ∀ R' : IMRep (univ : Set (Euclid P)) m, ∀ᵐ x ∂(μHE[m].restrict R'.carrier),
        x ∉ tsupport (ω : DifferentialForm (Euclid P) m) →
          (ω : DifferentialForm (Euclid P) m) x = 0 :=
      fun R' => Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx
    exact hadd _ (hint_of RT _ _ B hωc hB hcpt (h0 RT)) (hint_of RX _ _ B hωc hB hcpt (h0 RX))
  -- Step 6: `q^# ω`, `(q^# ω)(x) = ω(q x) ∘ Λᵐq`, is continuous with `‖q^# ω‖ ≤ sup ‖ω‖`
  -- (`‖q‖ ≤ 1`); it vanishes on `V \ spt ω` (`q x = x` there), so `S'(ω) = τ(R)(q^# ω)`
  have hq1 : ‖V.starProjection‖ ≤ 1 := V.starProjection_norm_le
  have hpull : ∀ ω : TestFormOn (univ : Set (Euclid P)) m,
      S' ω =
        R.action (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m)) := by
    intro ω
    obtain ⟨⟨hsmooth, hcpt⟩, -⟩ := ω.2
    have hωc : Continuous (ω : DifferentialForm (Euclid P) m) := ContDiff.continuous hsmooth
    obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support hcpt
    have hβc : Continuous
        (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m)) :=
      ContDiff.continuous (affinePullbackForm_isSmoothForm V.starProjection 0 hsmooth)
    have hβB : ∀ x,
        ‖affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x‖ ≤ B := by
      intro x
      calc ‖affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x‖
          ≤ ‖(ω : DifferentialForm (Euclid P) m) (0 + V.starProjection x)‖ *
              ‖V.starProjection‖ ^ Fintype.card (Fin m) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖(ω : DifferentialForm (Euclid P) m) (0 + V.starProjection x)‖ :=
            mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq1)
        _ ≤ B := hB _
    have hT0 : ∀ᵐ x ∂(μHE[m].restrict RT.carrier),
        x ∉ tsupport (ω : DifferentialForm (Euclid P) m) →
          affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x = 0 := by
      filter_upwards [hlive RT _ hTV] with x hxV hx
      have hqx : V.starProjection x = x :=
        Submodule.starProjection_eq_self_iff.2 (SetLike.mem_coe.1 hxV)
      ext v
      simp [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hqx,
        image_eq_zero_of_notMem_tsupport hx]
    have hX0 : ∀ᵐ x ∂(μHE[m].restrict RX.carrier), x ∉ K →
        affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x = 0 := by
      filter_upwards [hlive RX K hXK] with x hxK hx
      exact absurd hxK hx
    rw [hS' ω, hRT ω, ← Submission.idtp_fons_cs_sp_action_starProjection_eq P m RT V hTV
      (ω : DifferentialForm (Euclid P) m), hadd _ (hint_of RT _ _ B hβc hβB hcpt hT0)
      (hint_of RX _ K B hβc hβB hK hX0)]
  refine ⟨R, fun ω => by rw [htest ω, ← hRT ω, ← hRX ω], fun O => ?_⟩
  -- Step 7: a unit orientation has `|⟨α ∘ Λᵐq, ξ⟩| ≤ |α|_E ‖q‖ᵐ ≤ |α|_E` (Hadamard)
  have hproj : ∀ᵐ x ∂(μHE[m].restrict R.carrier), ∀ α : Covector (Euclid P) m,
      |R.orient x (α.compContinuousLinearMap V.starProjection)| ≤ covectorEuclideanNorm α := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, hQ⟩ := hx
    exact ((Submission.dtc_bc_lc_pf_unitOrientation_comp P m (R.orient x) Q V.starProjection
      hQ).1 α).trans (mul_le_of_le_one_right (covectorEuclideanNorm_nonneg α)
        (pow_le_one₀ (norm_nonneg _) hq1))
  -- Step 8: for admissible `ω` with `spt ω ⊆ O`, `|θ ⟨q^# ω, ξ⟩| ≤ θ 1_{q⁻¹(spt ω)}` a.e. on `M`,
  -- so `S'(ω) = τ(R)(q^# ω) ≤ μ_R(q⁻¹(spt ω)) ≤ μ_R(q⁻¹(O))`
  apply sSup_le
  rintro r ⟨ω, ⟨hωO, hω1⟩, rfl⟩
  have hs : MeasurableSet (V.starProjection ⁻¹' tsupport (ω : DifferentialForm (Euclid P) m)) :=
    ((isClosed_tsupport _).preimage V.starProjection.continuous).measurableSet
  have hpt : ∀ᵐ x ∂(μHE[m].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x
          (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x)‖ₑ ≤
        (V.starProjection ⁻¹' tsupport (ω : DifferentialForm (Euclid P) m)).indicator
          (fun y => (R.mult y : ℝ≥0∞)) x := by
    filter_upwards [hproj] with x hx
    by_cases hxs : x ∈ V.starProjection ⁻¹' tsupport (ω : DifferentialForm (Euclid P) m)
    · rw [indicator_of_mem hxs, ← ofReal_norm, ← ENNReal.ofReal_natCast]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _)
        ((hx ((ω : DifferentialForm (Euclid P) m) (0 + V.starProjection x))).trans (hω1 _))
    · have hxs' : V.starProjection x ∉ tsupport (ω : DifferentialForm (Euclid P) m) := hxs
      have h0 :
          affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x = 0 := by
        ext v
        simp [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
          image_eq_zero_of_notMem_tsupport hxs']
      rw [indicator_of_notMem hxs, h0]
      simp
  calc ENNReal.ofReal (S' ω)
      = ENNReal.ofReal (R.action
          (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m))) := by
        rw [hpull ω]
    _ ≤ ‖R.action (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m))‖ₑ :=
        (ENNReal.ofReal_le_ofReal (Real.le_norm_self _)).trans_eq (ofReal_norm _)
    _ ≤ ∫⁻ x in R.carrier, ‖(R.mult x : ℝ) * R.orient x
          (affinePullbackForm V.starProjection 0 (ω : DifferentialForm (Euclid P) m) x)‖ₑ ∂μHE[m] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in R.carrier,
          (V.starProjection ⁻¹' tsupport (ω : DifferentialForm (Euclid P) m)).indicator
            (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[m] :=
        lintegral_mono_ae hpt
    _ = R.measure (V.starProjection ⁻¹' tsupport (ω : DifferentialForm (Euclid P) m)) := by
        rw [lintegral_indicator hs, IMRep.measure, withDensity_apply _ hs]
    _ ≤ R.measure (V.starProjection ⁻¹' O) := measure_mono (preimage_mono hωO)
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- An open `W ⊆ U` with `c < μ(W)`, `μ = θ Hⁿ⌞M`, contains an open `V` with `c < μ(V) < ∞`
(step 3 of the proof that the weight of `T = τ(M, θ, ξ)` is at most its mass).  Inner regularity
gives a compact `K ⊆ W` with `c < μ(K)`; an open `V ⊇ K` with compact `closure V ⊆ W` has
`μ(V) ≥ μ(K) > c` and `μ(V) ≤ μ(closure V) = ∫⁻_{M ∩ closure V} θ dHⁿ < ∞`. -/
theorem Submission.rsd_mw_wlm_exists_open_measure_between : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (W : Set (Euclid P)), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < R.measure W → ∃ V : Set (Euclid P), IsOpen V ∧ V ⊆ W ∧ c < R.measure V ∧ R.measure V < ∞ := by
  intro P n U R W hW hWU c hc
  -- open sets are inner regular for closed sets, and closed sets for compact sets
  obtain ⟨K, hKW, hK, hcK⟩ := ((Measure.InnerRegularWRT.isCompact_isClosed R.measure).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace R.measure)) hW c hc
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  refine ⟨V, hVo, subset_closure.trans hVW, hcK.trans_le (measure_mono hKV), ?_⟩
  -- `μ(closure V) = ∫⁻_{M ∩ closure V} θ dHⁿ`, finite as `closure V` is a compact subset of `U`
  have hcl : R.measure (closure V) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ isClosed_closure.measurableSet,
      Measure.restrict_restrict isClosed_closure.measurableSet, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hVc (hVW.trans hWU)
  exact (measure_mono subset_closure).trans_lt hcl.lt_top
/-- A continuous linear image of an a.e. unit-bounded measurable `n`-vector field is integrable:
if `ν` is finite, `ξ` is `ν`-a.e. strongly measurable with `‖ξ x‖ ≤ 1` for `ν`-a.e. `x`, and
`J : MultiVector P n →L[ℝ] Covector (Euclid P) n`, then `x ↦ J (ξ x)` is `ν`-integrable.
Continuity of `J` at `0` gives `δ > 0` with `‖J w‖ < 1` whenever `‖w‖ < δ`; applied to
`(δ / 2) • w`, homogeneity gives `‖J w‖ ≤ 2 / δ` on the closed unit ball.  Hence `J ∘ ξ` is
a.e. strongly measurable and a.e. dominated by the constant `2 / δ`, which is `ν`-integrable as
`ν` is finite. -/
theorem Submission.rsd_mw_wlm_integrable_clm_comp : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (J : MultiVector P n →L[ℝ] Covector (Euclid P) n), IsFiniteMeasure ν → AEStronglyMeasurable ξ ν → (∀ᵐ x ∂ν, ‖ξ x‖ ≤ 1) → Integrable (fun x => J (ξ x)) ν := by
  intro P n ν ξ J hν hξ hξ1
  obtain ⟨δ, hδ, hJδ⟩ : ∃ δ > 0, ∀ w : MultiVector P n, ‖w‖ < δ → ‖J w‖ < 1 := by
    have hJc : @Continuous (MultiVector P n) (Covector (Euclid P) n)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace J := J.continuous
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hJc 0 1 one_pos
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have h' := h w (by convert hw using 1; exact dist_zero_right w)
    convert h' using 1
    rw [map_zero]
    exact (dist_zero_right _).symm
  have hbound : ∀ w : MultiVector P n, ‖w‖ ≤ 1 → ‖J w‖ ≤ 2 / δ := by
    intro w hw
    have h2 : ‖(δ / 2) • w‖ < δ := by
      calc ‖(δ / 2) • w‖ ≤ ‖δ / 2‖ * ‖w‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ δ / 2 * 1 := by
          rw [Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left hw (by positivity)
        _ < δ := by linarith
    have := hJδ _ h2
    rw [map_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at this
    rw [le_div_iff₀ hδ]
    nlinarith
  refine Integrable.mono' (integrable_const (2 / δ)) (J.continuous.comp_aestronglyMeasurable hξ) ?_
  filter_upwards [hξ1] with x hx using hbound _ hx
/-- If `T = τ(M, θ, ξ)` and `spt ω ⊆ V`, then `T(ω) = ∫ ⟨ω, ξ⟩ d(μ⌞V)` with `μ = θ Hⁿ⌞M`
(step 7 of the proof that the weight of `T = τ(M, θ, ξ)` is at most its mass).  The integrand
vanishes off `spt ω ⊆ V`, so restricting `μ` to `V` changes nothing; writing the density `θ` as
a measurable `ℝ≥0`-valued function turns `∫ ⟨ω, ξ⟩ dμ` into `∫_M θ ⟨ω, ξ⟩ dHⁿ = T(ω)`. -/
theorem Submission.rsd_mw_wlm_eval_eq_integral_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ (V : Set (Euclid P)) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ V → T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂(R.measure.restrict V) := by
  intro P n U T R hR V ω hωV
  rw [hR ω, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · -- `μ = (Hⁿ⌞M).withDensity θ` with `θ` read as a measurable `ℝ≥0`-valued density
    have hμ : R.measure = (μHE[n].restrict R.carrier).withDensity
        (fun x => ((R.mult x : NNReal) : ℝ≥0∞)) := by
      simp [IMRep.measure]
    have hmeas : Measurable fun x => (R.mult x : NNReal) :=
      measurable_from_nat.comp R.measurable_mult
    rw [hμ, integral_withDensity_eq_integral_smul hmeas]
    simp [IMRep.action, NNReal.smul_def]
  · -- off `V`, hence off `spt ω`, the form vanishes and so does `⟨ω, ξ⟩`
    intro x hx
    have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (hωV h)
    simp [h0]
/-- Integral lower bound for `⟨ω, ξ⟩` from an `L¹`-close dual field.  Write
`N = covectorEuclideanNorm`.  Let `ν` be finite, `ξ` `ν`-a.e. strongly measurable and `ω`
continuous with `N (ω x) ≤ 1`; suppose that, for `ν`-a.e. `x`, `|ξ x α| ≤ N α` for every `α` and
`ξ x (β x) = 1`.  If `∫⁻ N (ω − β) dν < ε`, then `ν(ℝᴾ) − ε < ∫ ξ(ω) dν`.
The function `h = ξ(ω)` is a.e. strongly measurable (continuous bilinear evaluation) and a.e.
bounded by `N ∘ ω ≤ 1`, hence integrable.  A.e., `h ≤ 1` and
`h = ξ(β) + ξ(ω − β) ≥ 1 − N (ω − β)`, so `0 ≤ 1 − h ≤ N (ω − β)`.  Therefore
`ofReal (∫ (1 − h) dν) = ∫⁻ ofReal (1 − h) dν ≤ ∫⁻ ofReal (N (ω − β)) dν < ofReal ε`, whence
`ν(ℝᴾ) − ∫ h dν = ∫ (1 − h) dν < ε`.  No measurability of `β` is needed: the comparison is made
only between lower integrals. -/
theorem Submission.rsd_mw_wlm_sub_lt_integral : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β ω : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsFiniteMeasure ν → AEStronglyMeasurable ξ ν → Continuous ω → (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → (∀ᵐ x ∂ν, (∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ξ x (β x) = 1) → ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε → (ν univ).toReal - ε < ∫ x, ξ x (ω x) ∂ν := by
  intro P n ν ξ β ω ε hν hξ hω hωN hG hlt
  have hhm : AEStronglyMeasurable (fun x => ξ x (ω x)) ν :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξ.prodMk hω.aestronglyMeasurable)
  have hh_int : Integrable (fun x => ξ x (ω x)) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hhm ?_
    filter_upwards [hG] with x hx
    rw [Real.norm_eq_abs]
    exact (hx.1 (ω x)).trans (hωN x)
  have hpt : ∀ᵐ x ∂ν, 0 ≤ 1 - ξ x (ω x) ∧
      1 - ξ x (ω x) ≤ covectorEuclideanNorm (ω x - β x) := by
    filter_upwards [hG] with x hx
    have hsplit : ξ x (ω x) = ξ x (β x) + ξ x (ω x - β x) := by
      rw [← map_add, add_sub_cancel]
    have h1 := (abs_le.1 ((hx.1 (ω x)).trans (hωN x))).2
    have h2 := (abs_le.1 (hx.1 (ω x - β x))).1
    constructor
    · linarith
    · rw [hsplit, hx.2]
      linarith
  have h1h_int : Integrable (fun x => 1 - ξ x (ω x)) ν := (integrable_const 1).sub hh_int
  have hint_eq : ∫ x, (1 - ξ x (ω x)) ∂ν = (ν univ).toReal - ∫ x, ξ x (ω x) ∂ν := by
    rw [integral_sub (integrable_const 1) hh_int, integral_const, smul_eq_mul, mul_one,
      measureReal_def]
  have hofreal : ENNReal.ofReal (∫ x, (1 - ξ x (ω x)) ∂ν) < ENNReal.ofReal ε := by
    rw [ofReal_integral_eq_lintegral_ofReal h1h_int (hpt.mono fun x hx => hx.1)]
    calc ∫⁻ x, ENNReal.ofReal (1 - ξ x (ω x)) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν :=
          lintegral_mono_ae (hpt.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)
      _ < ENNReal.ofReal ε := hlt
  have hlt' := (ENNReal.ofReal_lt_ofReal_iff'.1 hofreal).1
  linarith
/-- **Simon Ch. 6, Remark 2.6(a)–(b)** for the Euclidean coefficient norm: a unit orientation
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal) has `|ξ(α)| ≤ |α|`, and the single continuous linear map
`J(w) = Σ_I w(e^I) e^I` (`I` strictly increasing) has `|J(ξ)| = 1` and `ξ(J(ξ)) = 1`.  Here
`e^I(v) = det(⟨e_{I(k)}, vⱼ⟩)`, every covector expands as `α = Σ_I α(e_I) e^I`, and
`e^I(e_K) = δ_IK`.  Expanding `γ(v) = det(⟨τₖ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet identity
`Σ_I e^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.rsd_mw_unit_orientation_dual : ∀ (P n : ℕ), ∃ J : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (J ξ) = 1 ∧ ξ (J ξ) = 1 := by
  intro P n
  -- `D u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`, a continuous alternating map as an
  -- alternatization; `e^I = D (e ∘ I)` and `γ = D τ`
  let D : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hD : ∀ u v, D u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [D, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `D u v = D v u` (determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hDsymm : ∀ u v, D u v = D v u := by
    intro u v
    rw [hD, hD]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `D u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hD1 : ∀ u, Orthonormal ℝ u → D u u = 1 := by
    intro u hu
    rw [hD, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- step 2: `e^I(e_K) = δ_IK` for strictly increasing `I`, `K`; a nonzero term forces
  -- `K ∘ σ = I`, so `range I = range K` and `I = K`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I K : Fin n → Fin P, StrictMono I → StrictMono K →
      D (fun k => e (I k)) (fun k => e (K k)) = if I = K then 1 else 0 := by
    intro I K hI hK
    split_ifs with hIK
    · subst hIK
      exact hD1 _ (e.orthonormal.comp I hI.injective)
    · rw [hD]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIK
      have hKσ : K ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← StrictMono.range_inj_of_wellFoundedLT hI hK, ← hKσ, EquivLike.range_comp]
  -- step 1: `α = Σ_{I ∈ S} α(e_I) e^I`; both sides are alternating, so compare them on `e ∘ f`
  -- for injective `f`, and write `f = (f ∘ σ) ∘ σ⁻¹` with `f ∘ σ` strictly increasing
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • D (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hfσ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hfσ hfσ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIf
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hfσ,
        ite_eq_right hIf, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfσ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- step 3 (Cauchy–Binet): `Σ_{I ∈ S} e^I(τ)² = 1` for orthonormal `τ`; evaluate the expansion
  -- of `γ = D τ` at `τ`, using `γ(τ) = 1` and `γ(e_I) = e^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (D τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hD1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hDsymm τ, sq]
  -- step 4: `J w = Σ_{I ∈ S} w(e^I) e^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (D fun k => e (I k))).smulRight
    (D fun k => e (I k)), ?_⟩
  have hJ : ∀ w : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (D fun k => e (I k))).smulRight (D fun k => e (I k))) w =
      ∑ I ∈ S, w (D fun k => e (I k)) • D fun k => e (I k) := by
    intro w
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.apply_apply]
  -- step 5: `ξ(α) = s α(τ)` with `s = ±1`
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (i) `|ξ(α)| = |Σ_I α(e_I) e^I(τ)| ≤ |α| (Σ_I e^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * D (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (ii) `J(ξ)(e_K) = ξ(e^K)`, so `|J(ξ)|² = Σ_K ξ(e^K)² = Σ_K e^K(τ)² = 1`
    rw [hnorm, hJ]
    have : ∑ K ∈ S, (∑ I ∈ S, ξ (D fun k => e (I k)) • D fun k => e (I k))
        (fun k => e (K k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun K hK' => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single K]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hK').2
          (Finset.mem_filter.mp hK').2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIK
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hK').2, ite_eq_right hIK, smul_zero]
      · exact fun h => absurd hK' h
    rw [this, Real.sqrt_one]
  · -- (iii) `ξ(J(ξ)) = Σ_I ξ(e^I)² = Σ_I e^I(τ)² = 1`
    rw [hJ, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]

/-- **Simon Ch. 6, Remark 3.2(3), `≤` half** (with 2.5 and Remark 2.6(a)): `M_W(T) ≤ μ_T(W)` for
`T = τ(M, θ, ξ)` and every `W ⊆ ℝᴾ`.  Let `ω` be admissible: `spt ω ⊆ W`, `|ω| ≤ 1`.  At `Hⁿ`-a.e.
`x ∈ M`, `ξ(x)` is a unit simple `n`-vector, so `|⟨ω(x), ξ(x)⟩| ≤ |ω(x)| ≤ 1`; and `ω(x) = 0` off
`spt ω`.  Hence `T(ω) ≤ ∫_M θ|⟨ω, ξ⟩| dHⁿ ≤ ∫_{M ∩ spt ω} θ dHⁿ = μ_T(spt ω) ≤ μ_T(W)`.  Openness of
`U` and `W` and the local integrability of `θ` are not used. -/
theorem Submission.rsd_mw_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hT W
  obtain ⟨J, hJ⟩ := Submission.rsd_mw_unit_orientation_dual P n
  -- `|⟨α, ξ(x)⟩| ≤ |α|` at `Hⁿ`-a.e. `x ∈ M`, where `ξ(x)` is a unit simple `n`-vector
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hJ (R.orient x) Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  show ENNReal.ofReal (T ω) ≤ R.measure W
  set S := tsupport (ω : DifferentialForm (Euclid P) n)
  have hS : MeasurableSet S := (isClosed_tsupport _).measurableSet
  rw [hT ω, IMRep.action]
  calc _ ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
          ∂μHE[n]‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in R.carrier,
          ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in R.carrier, S.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
        refine lintegral_mono_ae ?_
        filter_upwards [hξ] with x hx
        by_cases hxS : x ∈ S
        · -- `|θ⟨ω, ξ⟩| ≤ θ|ω| ≤ θ` on `spt ω`
          rw [indicator_of_mem hxS, enorm_mul, Real.enorm_natCast, Real.enorm_eq_ofReal_abs]
          exact mul_le_of_le_one_right zero_le
            (ENNReal.ofReal_le_one.2 ((hx _).trans (hω1 x)))
        · -- `ω = 0` off `spt ω`
          rw [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport hxS, map_zero, mul_zero,
            enorm_zero]
    _ = R.measure S := by rw [lintegral_indicator hS, IMRep.measure, withDensity_apply _ hS]
    _ ≤ R.measure W := measure_mono hωW
/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Radial retraction onto the unit ball of `N = covectorEuclideanNorm`** (step 4 of the
approximation of a unit covector field by admissible test forms, used for Simon Ch. 6,
Remark 3.2(3)).  `ρ(a) = max(1, N(a))⁻¹ a` is continuous, `ρ(0) = 0`, `N(ρ(a)) ≤ 1`, and
`N(ρ(a) − b) ≤ 2 N(a − b)` whenever `N(b) ≤ 1`: if `N(a) > 1` then
`N(a − ρ(a)) = N(a) − 1 ≤ N(a − b)`, and the triangle inequality gives the factor `2`. -/
theorem Submission.rsd_mw_tfa_retraction : ∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b) := by
  intro P n
  obtain ⟨htri, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- the rescaling factor `max 1 (N a) ≥ 1` never vanishes
  have hpos : ∀ a : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm a) :=
    fun a => one_pos.trans_le (le_max_left _ _)
  refine ⟨fun a => (max 1 (covectorEuclideanNorm a))⁻¹ • a,
    ((continuous_const.max hcont).inv₀ fun a => (hpos a).ne').smul continuous_id, by simp,
    fun a => ?_, fun a b hb => ?_⟩
  · -- `N (ρ a) = N a / max 1 (N a) ≤ 1`
    dsimp only
    rw [hsmul, abs_of_pos (inv_pos.mpr (hpos a)), inv_mul_le_iff₀ (hpos a), mul_one]
    exact le_max_right _ _
  dsimp only
  rcases le_or_gt (covectorEuclideanNorm a) 1 with ha | ha
  · -- `N a ≤ 1`: `ρ a = a`
    rw [max_eq_left ha, inv_one, one_smul]
    linarith [covectorEuclideanNorm_nonneg (a - b)]
  -- `r := N a > 1`: `ρ a = r⁻¹ a`
  set r := covectorEuclideanNorm a with hr
  rw [max_eq_right ha.le]
  -- `N (a - ρ a) = (1 - r⁻¹) r = r - 1`
  have h₁ : covectorEuclideanNorm (a - r⁻¹ • a) = r - 1 := by
    rw [show a - r⁻¹ • a = (1 - r⁻¹) • a by module, hsmul,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ ha.le)), sub_mul, one_mul, ← hr,
      inv_mul_cancel₀ (one_pos.trans ha).ne']
  -- `r ≤ N (a - b) + N b ≤ N (a - b) + 1`
  have h₂ : r ≤ covectorEuclideanNorm (a - b) + 1 :=
    calc r = covectorEuclideanNorm (a - b + b) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (a - b) + covectorEuclideanNorm b := htri _ _
      _ ≤ covectorEuclideanNorm (a - b) + 1 := by linarith
  calc covectorEuclideanNorm (r⁻¹ • a - b)
      = covectorEuclideanNorm (-(a - r⁻¹ • a) + (a - b)) := by congr 1; abel
    _ ≤ covectorEuclideanNorm (-(a - r⁻¹ • a)) + covectorEuclideanNorm (a - b) := htri _ _
    _ = r - 1 + covectorEuclideanNorm (a - b) := by rw [covectorEuclideanNorm_neg, h₁]
    _ ≤ 2 * covectorEuclideanNorm (a - b) := by linarith

/-- **`L¹(ν)` approximation of a unit covector field by continuous compactly supported unit
fields** (steps 3–4 of the `L¹(ν)` approximation of a unit covector field by admissible test
forms).  Let `ν` be a finite Borel measure on `ℝᴾ` and `β` a `ν`-integrable `n`-covector field
with `N(β) ≤ 1` `ν`-a.e., `N = covectorEuclideanNorm`.  Continuous compactly supported maps are
dense in `L¹(ν)` (`ν` is regular), so one of them, `g₀`, has `∫ ‖β − g₀‖ dν ≤ η`.  With `ρ` the
retraction onto `{N ≤ 1}`, `g = ρ ∘ g₀` is continuous, compactly supported (`ρ 0 = 0`), has
`N(g) ≤ 1`, and `N(g − β) ≤ 2 N(g₀ − β) ≤ 2C ‖β − g₀‖` a.e., so `∫ N(g − β) dν ≤ 2Cη < δ`. -/
theorem Submission.rsd_mw_tfa_continuous_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g x - β x)) ∂ν < ENNReal.ofReal δ := by
  intro P n ν β hν hβ hβ1 δ hδ
  -- Step 1: the constant `C` of `norm_props` (iii), the retraction `ρ`, and the tolerance `η`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨ρ, hρc, hρ0, hρ1, hρ2⟩ := Submission.rsd_mw_tfa_retraction P n
  set η : ℝ := δ / (2 * (2 * C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: continuous compactly supported maps are dense in `L¹(ν)` (`ν` is finite, hence
  -- regular).  The contract does not import `Integrable.exists_hasCompactSupport_lintegral_sub_le`,
  -- so this goes through `MemLp.induction_dense`: `c • 1_s` is approximated by `φ • c`, with `φ`
  -- a Urysohn function for compact `K ⊆ s ⊆ U` open, `ν (U \ K)` small.
  have hind : ∀ (c : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : Euclid P → Covector (Euclid P) n,
        eLpNorm (g - s.indicator fun _ => c) 1 ν ≤ ε ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro c s hs hsν ε hε
    obtain ⟨t, ht0, htε⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hε
    have ht : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht0.ne'
    -- compact `K ⊆ s ⊆ U` open with `ν (s \ K) < t` and `ν (U \ s) < t`
    obtain ⟨K, hKs, hK, hsK⟩ := hs.exists_isCompact_sdiff_lt hsν.ne ht
    obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hsν.ne ht
    -- Urysohn: `φ = 1` on `K`, `φ = 0` off `U`, `0 ≤ φ ≤ 1`, compact support
    obtain ⟨φ, hφK, hφU, hφs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hgc : Continuous fun x => φ x • c := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • c, ?_, hgc, hφs.smul_right⟩
    -- pointwise `‖φ x • c - 1_s(x) c‖ₑ ≤ 1_{U \ K}(x) ‖c‖ₑ`
    have hle : ∀ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ≤
        (U \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      rw [← ofReal_norm]
      by_cases hxK : x ∈ K
      · simp [hφK hxK, hKs hxK]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxK), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [Pi.sub_apply, indicator_of_mem hxs, show φ x • c - c = (φ x - 1) • c by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          nlinarith [norm_nonneg c]
        · rw [Pi.sub_apply, indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg h0]
          nlinarith [norm_nonneg c]
      · simp [hφU hxU, show x ∉ s from fun h => hxU (hsU h), hxU]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (stronglyMeasurable_const.indicator hs).aestronglyMeasurable)]
    calc ∫⁻ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ∂ν
        ≤ ∫⁻ x, (U \ K).indicator (fun _ => ‖c‖ₑ) x ∂ν := lintegral_mono hle
      _ = ‖c‖ₑ * ν (U \ K) := lintegral_indicator_const (hU.measurableSet.diff hK.measurableSet) _
      _ ≤ ‖c‖ₑ * (ν (U \ s) + ν (s \ K)) := by
          gcongr
          refine (measure_mono fun x hx => ?_).trans (measure_union_le (U \ s) (s \ K))
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩
      _ ≤ ‖c‖ₑ * (t + t) := by gcongr
      _ = t * (2 * ‖c‖ₑ) := by ring
      _ ≤ ε := htε.le
  -- the density statement for `β`, with tolerance `η`
  obtain ⟨g₀, hg₀, hg₀c, hg₀s⟩ := (memLp_one_iff_integrable.2 hβ).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.mpr hη0).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hβ.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)] at hg₀
  -- Step 3: `g := ρ ∘ g₀`
  refine ⟨ρ ∘ g₀, hρc.comp hg₀c, hg₀s.comp_left hρ0, fun x => hρ1 _, ?_⟩
  -- Step 4: pointwise a.e. estimate
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x))
      ≤ ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ := by
    filter_upwards [hβ1] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc covectorEuclideanNorm ((ρ ∘ g₀) x - β x)
        ≤ 2 * covectorEuclideanNorm (g₀ x - β x) := hρ2 _ _ hx
      _ ≤ 2 * (C * ‖g₀ x - β x‖) := by gcongr; exact hC _
      _ = 2 * C * ‖β x - g₀ x‖ := by rw [norm_sub_rev]; ring
  -- Step 5: integration
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * C) * ∫⁻ x, ‖β x - g₀ x‖ₑ ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * C) * ENNReal.ofReal η := by gcongr; exact hg₀
    _ = ENNReal.ofReal (2 * C * η) := (ENNReal.ofReal_mul (by positivity)).symm
    -- Step 6: arithmetic
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ, hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smooth uniform approximation keeping the unit bound** (smoothing step in the proof of
`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is `covectorEuclideanNorm`).  Let
`η := δ/(2C + 1)`, where `|·|_E ≤ C‖·‖` (`Submission.rsd_mw_tfa_norm_props`).  A continuous
compactly supported covector field `g` with `|g|_E ≤ 1` is uniformly continuous, so
`‖g y − g x‖ < η` when `dist y x < r`.  Mollifying, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth
bump `φ ≥ 0` with `support φ = B_r(0)` is a `C^∞` field with `‖h' − g‖ ≤ η`; then
`|h' − g|_E ≤ Cη` and `|h'|_E ≤ 1 + Cη`.  The rescaled field `h = (1 + Cη)⁻¹h'` has `|h|_E ≤ 1`
and `|h − h'|_E = Cη(1 + Cη)⁻¹|h'|_E ≤ Cη`, hence `|h − g|_E ≤ 2Cη ≤ δ`. -/
theorem Submission.rsd_mw_tfa_smooth_uniform_approx : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n), Continuous g → HasCompactSupport g → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ h : Euclid P → Covector (Euclid P) n, ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ x, covectorEuclideanNorm (h x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (h x - g x) ≤ δ := by
  intro P n g hgc hgs hg1 δ hδ
  -- `N := covectorEuclideanNorm` is subadditive, absolutely homogeneous and `N ≤ C ‖·‖`
  obtain ⟨htri, hsmul, ⟨C, hC0, hCle⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: the tolerance `η = δ / (2C + 1)`
  set η : ℝ := δ / (2 * C + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hCη : 0 ≤ C * η := mul_nonneg hC0 hη0.le
  -- Step 2: `g` is uniformly continuous: `‖g y - g x‖ < η` whenever `dist y x < r`
  obtain ⟨r, hr, hgr⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη0
  -- Step 3: mollify, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ`, `support φ = B_r(0)`
  let φ : ContDiffBump (0 : Euclid P) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hr
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 r := hψφ.trans φ.support_eq.subset
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  obtain ⟨h', hh's, hh'g⟩ : ∃ h' : Euclid P → Covector (Euclid P) n,
      ContDiff ℝ (⊤ : ℕ∞) h' ∧ ∀ x, dist (h' x) (g x) ≤ η :=
    ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      (φ.hasCompactSupport.mono hψφ).contDiff_convolution_left _ (φ.contDiff.div_const _)
        hgc.locallyIntegrable,
      fun x => dist_convolution_le hη0.le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgr (mem_ball.mp hy)).le⟩
  -- Step 4: `N(h' - g) ≤ Cη` and `N(h') ≤ 1 + Cη`
  have hdiff : ∀ x, covectorEuclideanNorm (h' x - g x) ≤ C * η := fun x =>
    (hCle _).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hh'g x) hC0)
  have hh'1 : ∀ x, covectorEuclideanNorm (h' x) ≤ 1 + C * η := fun x =>
    calc covectorEuclideanNorm (h' x) = covectorEuclideanNorm ((h' x - g x) + g x) := by
          rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (h' x - g x) + covectorEuclideanNorm (g x) := htri _ _
      _ ≤ C * η + 1 := add_le_add (hdiff x) (hg1 x)
      _ = 1 + C * η := add_comm _ _
  -- Step 5: rescale by `s = (1 + Cη)⁻¹ ∈ (0, 1]`
  have hpos : 0 < 1 + C * η := by linarith
  have hne : 1 + C * η ≠ 0 := hpos.ne'
  set s : ℝ := (1 + C * η)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hpos
  refine ⟨fun x => s • h' x, hh's.const_smul s, fun x => ?_, fun x => ?_⟩
  · show covectorEuclideanNorm (s • h' x) ≤ 1
    rw [hsmul, abs_of_pos hs0, hs, inv_mul_le_iff₀ hpos, mul_one]
    exact hh'1 x
  · show covectorEuclideanNorm (s • h' x - g x) ≤ δ
    -- Step 6: `N(s h' - h') = |s - 1| N(h') = Cη s N(h') ≤ Cη`
    have hsh : s • h' x - h' x = (s - 1) • h' x := by module
    have hs1 : |s - 1| = C * η * s := by
      have hle : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      rw [abs_of_nonpos (by linarith), hs]
      field_simp
      ring
    have h6 : covectorEuclideanNorm (s • h' x - h' x) ≤ C * η := by
      rw [hsh, hsmul, hs1]
      calc C * η * s * covectorEuclideanNorm (h' x) ≤ C * η * s * (1 + C * η) :=
            mul_le_mul_of_nonneg_left (hh'1 x) (mul_nonneg hCη hs0.le)
        _ = C * η := by rw [hs]; field_simp
    -- Step 7: `N(s h' - g) ≤ N(s h' - h') + N(h' - g) ≤ 2Cη ≤ δ`
    calc covectorEuclideanNorm (s • h' x - g x)
        = covectorEuclideanNorm ((s • h' x - h' x) + (h' x - g x)) := by
          rw [sub_add_sub_cancel]
      _ ≤ covectorEuclideanNorm (s • h' x - h' x) + covectorEuclideanNorm (h' x - g x) :=
          htri _ _
      _ ≤ C * η + C * η := add_le_add h6 (hdiff x)
      _ ≤ δ := by
          have h2 : 0 < 2 * C + 1 := by linarith
          have h2C : C * η + C * η = 2 * C * δ / (2 * C + 1) := by rw [hη]; ring
          rw [h2C, div_le_iff₀ h2]
          nlinarith

/-- **Test forms approximating a unit-bounded integrable covector field in `L¹(ν)`** (the
approximation behind `M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is
`covectorEuclideanNorm`).  Let `m = ν(ℝᴾ)` and `δ = ε/(4(m + 1))`.  The smooth cut-off `χ` of
`Submission.rsd_mw_tfa_smooth_cutoff` satisfies `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`.  The
continuous field `g₁` of `Submission.rsd_mw_tfa_continuous_approx` satisfies `|g₁|_E ≤ 1` and
`∫ |g₁ − β|_E dν < ε/4`.  Its smoothing `g₂` (`Submission.rsd_mw_tfa_smooth_uniform_approx`)
satisfies `|g₂|_E ≤ 1` and `|g₂ − g₁|_E ≤ δ`.  Then `ω = χ g₂` is a test form, `tsupport ω ⊆ V`
and `|ω|_E ≤ 1`.  For a.e. `x`, `|ω − β|_E ≤ δ + |g₁ − β|_E` where `χ = 1`, and
`|ω − β|_E ≤ 2` where `χ ≠ 1`.  Integrating,
`∫ |ω − β|_E dν ≤ δm + ∫ |g₁ − β|_E dν + 2ν{χ ≠ 1} < ε/4 + ε/4 + ε/4 < ε`. -/
theorem Submission.rsd_mw_exists_testForm_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ ε : ℝ, 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν V β hν hV hVc hβ hβ1 ε hε
  -- `N := covectorEuclideanNorm` is subadditive and absolutely homogeneous
  obtain ⟨htri, hsmul, -, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: a smooth cut-off `χ` with `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`
  obtain ⟨χ, hχs, hχc, hχV, hχ01, hχν⟩ :=
    Submission.rsd_mw_tfa_smooth_cutoff P ν V hν hV hVc (ε / 8) (by positivity)
  -- Step 2: a continuous compactly supported `g₁` with `N(g₁) ≤ 1` and `∫ N(g₁ - β) dν < ε/4`
  obtain ⟨g₁, hg₁c, hg₁s, hg₁1, hg₁β⟩ :=
    Submission.rsd_mw_tfa_continuous_approx P n ν β hν hβ hβ1 (ε / 4) (by positivity)
  -- Step 3: a smooth `g₂` with `N(g₂) ≤ 1` and `N(g₂ - g₁) ≤ δ = ε/(4(m + 1))`, `m = ν(ℝᴾ)`
  set m : ℝ := (ν univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (4 * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g₂, hg₂s, hg₂1, hg₂g₁⟩ :=
    Submission.rsd_mw_tfa_smooth_uniform_approx P n g₁ hg₁c hg₁s hg₁1 δ hδ0
  -- Step 4: `ω = χ g₂` is a test form with `tsupport ω ⊆ V` and `N(ω) ≤ 1`
  have hω1 : ∀ x, covectorEuclideanNorm (χ x • g₂ x) ≤ 1 := fun x => by
    rw [hsmul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hg₂1 x)
  refine ⟨fun x => χ x • g₂ x, ⟨hχs.smul hg₂s, hχc.smul_right⟩,
    (tsupport_smul_subset_left χ g₂).trans hχV, hω1, ?_⟩
  -- Step 5: a.e., `N(ω - β) ≤ δ + N(g₁ - β)` where `χ = 1` and `N(ω - β) ≤ 2` on `S = {χ ≠ 1}`
  set S : Set (Euclid P) := {x | χ x ≠ 1}
  have hSm : MeasurableSet S := (isOpen_ne_fun hχs.continuous continuous_const).measurableSet
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ≤
      ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
        S.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    filter_upwards [hβ1] with x hx
    by_cases h1 : χ x = 1
    · rw [indicator_of_notMem (not_not.mpr h1), add_zero,
        ← ENNReal.ofReal_add hδ0.le (covectorEuclideanNorm_nonneg _), h1, one_smul]
      refine ENNReal.ofReal_le_ofReal ?_
      calc covectorEuclideanNorm (g₂ x - β x)
          = covectorEuclideanNorm ((g₂ x - g₁ x) + (g₁ x - β x)) := by rw [sub_add_sub_cancel]
        _ ≤ covectorEuclideanNorm (g₂ x - g₁ x) + covectorEuclideanNorm (g₁ x - β x) :=
          htri _ _
        _ ≤ δ + covectorEuclideanNorm (g₁ x - β x) := by linarith [hg₂g₁ x]
    · rw [indicator_of_mem h1]
      refine le_add_left (le_of_le_of_eq (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_ofNat 2))
      calc covectorEuclideanNorm (χ x • g₂ x - β x)
          = covectorEuclideanNorm (χ x • g₂ x + -β x) := by rw [sub_eq_add_neg]
        _ ≤ covectorEuclideanNorm (χ x • g₂ x) + covectorEuclideanNorm (-β x) := htri _ _
        _ ≤ 2 := by rw [covectorEuclideanNorm_neg]; linarith [hω1 x]
  -- Step 6: integrate, `∫ N(ω - β) dν ≤ δm + ∫ N(g₁ - β) dν + 2ν(S) < 3ε/4`
  have hδm : ENNReal.ofReal δ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← hm, ← ENNReal.ofReal_mul hδ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc δ * m ≤ δ * (m + 1) := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hS2 : 2 * ν S < ENNReal.ofReal (ε / 4) := by
    calc 2 * ν S = ν S + ν S := two_mul _
      _ < ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := ENNReal.add_lt_add hχν hχν
      _ = ENNReal.ofReal (ε / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
          S.indicator (fun _ => (2 : ℝ≥0∞)) x) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal δ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) ∂ν + 2 * ν S := by
        rw [lintegral_add_right _ (measurable_const.indicator hSm),
          lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hSm]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_le_of_lt
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hδm hg₁β) hS2
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Simon Ch. 6, Remark 3.2(3), `≥` half** (with 2.5 and Remark 2.6(a)–(b)): `μ_T(W) ≤ M_W(T)`
for `T = τ(M, θ, ξ)` and open `W ⊆ U`.  Given `c < μ_T(W)`, take an open `V ⊆ W` with
`c < μ_T(V) < ∞` and put `ν = μ_T⌞V`.  With `J` as in `Submission.rsd_mw_unit_orientation_dual`,
`β = J ∘ ξ` is `ν`-integrable, and `ν`-a.e. `|β| = 1`, `⟨β, ξ⟩ = 1` and `|⟨α, ξ⟩| ≤ |α|`.  A test
form `ω` with `spt ω ⊆ V`, `|ω| ≤ 1` and `∫ |ω − β| dν < ε = (μ_T(V) − c)/2` is admissible for
`M_W(T)`, and `T(ω) = ∫ ⟨ω, ξ⟩ dν > ν(ℝᴾ) − ε = (μ_T(V) + c)/2 > c`. -/
theorem Submission.rsd_mw_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), IsOpen W → W ⊆ U → R.measure W ≤ T.massOn W := by
  intro P n U T R hT W hW hWU
  obtain ⟨J, hJ⟩ := Submission.rsd_mw_unit_orientation_dual P n
  -- it suffices to show `c < M_W(T)` for every `c < μ_T(W)`
  refine le_of_forall_lt fun c hcW => ?_
  -- an open `V ⊆ W` with `c < μ_T(V) < ∞`
  obtain ⟨V, hV, hVW, hcV, hVfin⟩ :=
    Submission.rsd_mw_wlm_exists_open_measure_between P n U R W hW hWU c hcW
  -- `ν = μ_T⌞V` is finite, vanishes off `V`, and `ν ≪ μ_T ≪ Hⁿ⌞M`
  set ν := R.measure.restrict V with hν
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hVfin.ne
  have hνVc : ν Vᶜ = 0 := by
    rw [hν, Measure.restrict_apply' hV.measurableSet, compl_inter_self, measure_empty]
  have hμac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hνac : ν ≪ μHE[n].restrict R.carrier :=
    Measure.restrict_le_self.absolutelyContinuous.trans hμac
  -- `ν`-a.e. `ξ(x)` is a unit orientation
  have hG : ∀ᵐ x ∂ν, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [hνac.ae_le R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact ⟨Q, hQ⟩
  have hξ : AEStronglyMeasurable R.orient ν := R.aestronglyMeasurable_orient.mono_ac hνac
  -- `β = J ∘ ξ` is `ν`-integrable, as `‖ξ‖ ≤ 1` `ν`-a.e., and `|β| ≤ 1` `ν`-a.e.
  have hβ : Integrable (fun x => J (R.orient x)) ν := by
    refine Submission.rsd_mw_wlm_integrable_clm_comp P n ν R.orient J hνfin hξ ?_
    filter_upwards [hG] with x hx
    obtain ⟨Q, hQ⟩ := hx
    exact Submission.rsd_mw_wlm_orient_opNorm_le_one P n Q (R.orient x) hQ
  have hβ1 : ∀ᵐ x ∂ν, covectorEuclideanNorm (J (R.orient x)) ≤ 1 := by
    filter_upwards [hG] with x hx
    obtain ⟨Q, hQ⟩ := hx
    exact (hJ _ Q hQ).2.1.le
  -- `c < ∞`, and `ε = (μ_T(V) − c)/2 > 0` in `ℝ`
  have hctop : c ≠ ∞ := ne_top_of_lt hcV
  have hcV' : c.toReal < (R.measure V).toReal := (ENNReal.toReal_lt_toReal hctop hVfin.ne).2 hcV
  set ε := ((R.measure V).toReal - c.toReal) / 2 with hε
  have hε0 : 0 < ε := by linarith
  -- a test form `ω` with `spt ω ⊆ V`, `|ω| ≤ 1` and `∫ |ω − β| dν < ε`
  obtain ⟨ω, hωt, hωV, hω1, hωβ⟩ := Submission.rsd_mw_exists_testForm_approx P n ν V
    (fun x => J (R.orient x)) hνfin hV hνVc hβ hβ1 ε hε0
  -- `ω` is admissible for `M_W(T)`
  let ω' : TestFormOn U n := ⟨ω, hωt, hωV.trans (hVW.trans hWU)⟩
  have hadm : ω' ∈ massAdmissibleOn U n W := ⟨hωV.trans hVW, hω1⟩
  -- `T(ω) = ∫ ⟨ω, ξ⟩ dν > ν(ℝᴾ) − ε`, where `ν(ℝᴾ) = μ_T(V)`
  have hTω : T ω' = ∫ x, R.orient x (ω x) ∂ν :=
    Submission.rsd_mw_wlm_eval_eq_integral_restrict P n U T R hT V ω' hωV
  have hest := Submission.rsd_mw_wlm_sub_lt_integral P n ν R.orient (fun x => J (R.orient x)) ω
    ε hνfin hξ (ContDiff.continuous hωt.1) hω1 (by
      filter_upwards [hG] with x hx
      obtain ⟨Q, hQ⟩ := hx
      exact ⟨(hJ _ Q hQ).1, (hJ _ Q hQ).2.2⟩) hωβ
  have hνuniv : ν univ = R.measure V := Measure.restrict_apply_univ V
  rw [hνuniv] at hest
  have hlt : c.toReal < T ω' := by
    rw [hTω]
    linarith
  -- `c = ofReal c.toReal < ofReal T(ω) ≤ M_W(T)`
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    _ < ENNReal.ofReal (T ω') :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hlt
    _ ≤ T.massOn W := T.le_massOn hadm

/-- **Simon Ch. 6, Remark 3.2(3)** (with 2.7–2.8): for `T = τ(M, θ, ξ)` integer multiplicity,
`M_W(T) = μ_T(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W ⊆ U`.  The bound `M_W(T) ≤ μ_T(W)` holds for
every `W` (`Submission.rsd_mw_massOn_le_measure`); the reverse bound tests `T` against smooth
admissible forms approximating the unit covector field dual to `ξ`
(`Submission.rsd_mw_measure_le_massOn`). -/
theorem Submission.rsd_massOn_eq_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W := by
  intro P n U T R _ hT W hW hWU
  exact le_antisymm (Submission.rsd_mw_massOn_le_measure P n U T R hT W)
    (Submission.rsd_mw_measure_le_massOn P n U T R hT W hW hWU)
/-- **Simon Ch. 1, Theorem 3.3** (comparison theorem, p. 14), with a non-sharp constant and
`Hⁿ = μHE[n]` on `ℝᴺ`: if `ν(B̄_t(x)) ≥ c tⁿ` for all small `t > 0` at every point `x` of a subset
`A` of an open set `O`, then `Hⁿ(A) ≤ C ν(O)` with `C = C(n, c) < ∞`.  At each scale `δ` the
5-times covering lemma (Simon 3.4) selects, among the balls `B̄_r(x) ⊆ O` with `x ∈ A`, `10r ≤ δ`
and `ν(B̄_r(x)) ≥ c rⁿ`, a disjoint, hence countable, subfamily whose 5-times enlargements cover
`A`.  This `δ`-cover costs `Σ (10rⱼ)ⁿ ≤ (10ⁿ/c) Σ ν(B̄_{rⱼ}(xⱼ)) ≤ (10ⁿ/c) ν(O)`, and `μHE[n]` is
a finite multiple of `μH[n]`. -/
theorem Submission.dorag_sn_hausdorff_le_mul_of_lower_density : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
  intro N n c hc
  -- `μHE[n] = k • μH[n]` with a finite factor `k`; take `C = k · 10ⁿ / c`
  set k : NNReal :=
    Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)]
  refine ⟨(k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro ν A O hO hAO hA
  have hdiam : ∀ (y : Euclid N) (ρ : ℝ), ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
    intro y ρ
    apply ediam_le_of_forall_dist_le
    intro z hz w hw
    rw [mem_closedBall] at hz hw
    linarith [dist_triangle_right z w y]
  -- scale `δ = 1 / (m + 1)`: a countable disjoint family of admissible balls whose 5-times
  -- enlargements cover `A`, of total cost at most `(10ⁿ/c) ν(O)`
  have step : ∀ m : ℕ, ∃ u : Set (Euclid N × ℝ), u.Countable ∧
      (∀ p ∈ u, ediam (closedBall p.1 (5 * p.2)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1))) ∧
      A ⊆ ⋃ p : u, closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2) ∧
      ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) ≤
        ENNReal.ofReal (10 ^ n / c) * ν O := by
    intro m
    set δ : ℝ := 1 / ((m : ℝ) + 1)
    have hδpos : 0 < δ := by positivity
    -- the admissible balls, as (center, radius) pairs
    set T : Set (Euclid N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧
      closedBall p.1 p.2 ⊆ O ∧ ENNReal.ofReal (c * p.2 ^ n) ≤ ν (closedBall p.1 p.2)}
    obtain ⟨u, huT, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun p => p.1)
        (fun p => p.2) δ (fun p hp => by linarith [hp.2.2.1, hp.2.1]) 5 (by norm_num)
    -- disjoint balls with nonempty interiors in the separable space `ℝᴺ`
    have hucount : u.Countable := by
      refine hudisj.countable_of_nonempty_interior fun p hp => ?_
      exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huT hp).2.1)⟩
    refine ⟨u, hucount, fun p hp => ?_, ?_, ?_⟩
    · obtain ⟨-, -, hpδ, -, -⟩ := huT hp
      refine (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    · -- each `x ∈ A` is the center of a small admissible ball
      intro x hx
      obtain ⟨t₀, ht₀, hbound⟩ := hA x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
      set r : ℝ := min (t₀ / 2) (min (ε / 2) (δ / 10))
      have hrpos : 0 < r := by positivity
      have hr₁ := min_le_left (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₂ := min_le_right (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₃ := min_le_left (ε / 2) (δ / 10)
      have hr₄ := min_le_right (ε / 2) (δ / 10)
      have hmem : (x, r) ∈ T :=
        ⟨hx, hrpos, by linarith, (closedBall_subset_ball (by linarith)).trans hball,
          hbound r hrpos (by linarith)⟩
      obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hmem
      exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_closedBall_self hrpos.le)⟩
    · calc ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
          ≤ ∑' p : u, ENNReal.ofReal (10 ^ n / c) *
              ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            obtain ⟨-, hp0, -, -, hpν⟩ := huT p.2
            calc ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (2 * (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) :=
                  ENNReal.rpow_le_rpow (hdiam _ _) (Nat.cast_nonneg n)
              _ = ENNReal.ofReal (10 ^ n / c) * ENNReal.ofReal (c * (p : Euclid N × ℝ).2 ^ n) := by
                  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
                    ← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  field_simp
                  ring
              _ ≤ ENNReal.ofReal (10 ^ n / c) *
                    ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
                  gcongr
        _ = ENNReal.ofReal (10 ^ n / c) * ν (⋃ p ∈ u, closedBall p.1 p.2) := by
            rw [ENNReal.tsum_mul_left,
              measure_biUnion hucount hudisj fun p _ => measurableSet_closedBall]
        _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
            gcongr
            exact iUnion₂_subset fun p hp => (huT hp).2.2.2.1
  choose u hucount hudiam hucov husum using step
  have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
  -- covers of mesh `1 / (m + 1) → 0`
  have main : μH[(n : ℝ)] A ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
    calc μH[(n : ℝ)] A
        ≤ liminf (fun m => ∑' p : u m,
            ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)) atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) A
            (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) ?_
            (fun m p => closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2))
            (Eventually.of_forall fun m p => hudiam m p p.2) (Eventually.of_forall hucov)
          simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O :=
          liminf_le_of_frequently_le' (Frequently.of_forall husum)
  calc μHE[n] A = (k : ℝ≥0∞) * μH[(n : ℝ)] A := by
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul]
    _ ≤ (k : ℝ≥0∞) * (ENNReal.ofReal (10 ^ n / c) * ν O) := by gcongr
    _ = (k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c) * ν O := by rw [mul_assoc]
/-- **A null set at whose points the measure is locally finite has open neighbourhoods of
arbitrarily small measure** (localized outer regularity).  The balls `B(x, r(x))` of finite
measure, `x ∈ A`, have a countable subfamily `B(i, r(i))`, `i ∈ T ⊆ A`, still covering `A`
(Lindelöf).  With budgets `δᵢ > 0`, `∑ᵢ δᵢ < ε`, outer regularity of the finite measure
`μ ⌞ B(i, r(i))` at `A` gives an open `Uᵢ ⊇ A` with `μ (Uᵢ ∩ B(i, r(i))) < δᵢ`; take
`O = ⋃ᵢ Uᵢ ∩ B(i, r(i))`. -/
theorem Submission.dorag_sn_open_superset_measure_lt : ∀ (N : ℕ) (μ : Measure (Euclid N)) (A : Set (Euclid N)), μ A = 0 → (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ μ (ball x r) ≠ ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ O : Set (Euclid N), IsOpen O ∧ A ⊆ O ∧ μ O < ε := by
  intro N μ A hA hloc ε hε
  choose! r hr hfin using hloc
  -- Lindelöf: countably many of the balls `B(x, r(x))`, `x ∈ A`, still cover `A`
  obtain ⟨T, hTA, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable A
    (fun x => ball x (r x)) fun x _ => isOpen_ball
  have : Countable T := hTc.to_subtype
  -- budgets `δᵢ > 0` with `∑ᵢ δᵢ < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' T
  -- outer regularity of the finite measure `μ ⌞ B(i, r(i))` at the null set `A`
  have hU : ∀ i : T, ∃ U : Set (Euclid N), A ⊆ U ∧ IsOpen U ∧
      μ (U ∩ ball (i : Euclid N) (r i)) < δ i := by
    intro i
    have : IsFiniteMeasure (μ.restrict (ball (i : Euclid N) (r i))) :=
      isFiniteMeasure_restrict.2 (hfin i (hTA i.2))
    obtain ⟨U, hAU, hUo, hUδ⟩ := A.exists_isOpen_lt_of_lt
      (μ := μ.restrict (ball (i : Euclid N) (r i))) (δ i)
      ((Measure.restrict_apply_le _ A).trans_lt (by rw [hA]; exact hδ i))
    exact ⟨U, hAU, hUo, by rwa [Measure.restrict_apply hUo.measurableSet] at hUδ⟩
  choose U hAU hUo hUδ using hU
  refine ⟨⋃ i : T, U i ∩ ball (i : Euclid N) (r i),
    isOpen_iUnion fun i => (hUo i).inter isOpen_ball, fun x hx => ?_, ?_⟩
  · obtain ⟨i, hiT, hxi⟩ :=
      mem_iUnion₂.1 (hTU.superset (mem_biUnion hx (mem_ball_self (hr x hx))))
    exact mem_iUnion.2 ⟨⟨i, hiT⟩, hAU _ hx, hxi⟩
  · calc μ (⋃ i : T, U i ∩ ball (i : Euclid N) (r i))
        ≤ ∑' i : T, μ (U i ∩ ball (i : Euclid N) (r i)) := measure_iUnion_le _
      _ ≤ ∑' i : T, δ i := ENNReal.tsum_le_tsum fun i => (hUδ i).le
      _ < ε := hδε

/-- **Simon Ch. 1, Theorem 3.6 and Remark 3.7(2)** (upper density theorem) for the mass measure
`μ_T = θ Hⁿ⌞M` of `T = τ(M, θ, ξ)` in `ℝᴾ`: if `Θⁿ(μ_T, x) = Θ(x)` at every `x`, then `Θ = 0`
at `Hⁿ`-a.e. `x ∉ M`.  Let `t > 0` and `A = {x ∉ M : Θ(x) > t}`.  As
`M_{B_s(x)}(T) = μ_T(B_s(x))`, the density gives `μ_T(B̄_s(x)) ≥ t ωₙ sⁿ` for small `s > 0` at
each `x ∈ A`, so the comparison theorem bounds `Hⁿ(A) ≤ C μ_T(O)` for every open `O ⊇ A`.  But
`μ_T` vanishes off `M` and is locally finite, so there are open `O ⊇ A` of arbitrarily small
`μ_T`-measure, and `Hⁿ(A) = 0`.  Take the union over `t = 1/(k+1)`. -/
theorem Submission.dimred_cs_mi_density_null_off_carrier : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (Θ : Euclid P → ℝ), R.Represents S → (∀ x : Euclid P, HasMassDensity S x (Θ x)) → (μHE[n] : Measure (Euclid P)) {x | x ∉ R.carrier ∧ 0 < Θ x} = 0 := by
  intro P n S R Θ hRS hΘ
  -- `0 < ωₙ < ∞`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_ne_top
  -- `μ_R = θ Hⁿ⌞M` vanishes off `M`
  have hoff : ∀ A ⊆ R.carrierᶜ, R.measure A = 0 := by
    intro A hA
    refine withDensity_absolutelyContinuous (μHE[n].restrict R.carrier)
      (fun x => (R.mult x : ℝ≥0∞)) ?_
    rw [Measure.restrict_apply' R.measurableSet_carrier]
    exact measure_mono_null (fun x hx => hA hx.1 hx.2) measure_empty
  -- `μ_R` is locally finite: `μ_R(B̄₁(x)) = ∫_{M ∩ B̄₁(x)} θ dHⁿ < ∞`
  have hloc : ∀ x : Euclid P, R.measure (ball x 1) ≠ ∞ := by
    intro x
    refine ne_top_of_le_ne_top ?_ (measure_mono ball_subset_closedBall)
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall x 1) (subset_univ _)
  -- each `{x ∉ M : Θ(x) > 1/(k+1)}` is `Hⁿ`-null
  have hk : ∀ k : ℕ,
      (μHE[n] : Measure (Euclid P)) {x | x ∉ R.carrier ∧ 1 / ((k : ℝ) + 1) < Θ x} = 0 := by
    intro k
    set t : ℝ := 1 / ((k : ℝ) + 1)
    have ht : 0 < t := Nat.one_div_pos_of_nat
    set A : Set (Euclid P) := {x | x ∉ R.carrier ∧ t < Θ x}
    have hc : 0 < t * (unitBallVolume n).toReal := mul_pos ht (ENNReal.toReal_pos hω0 hωtop)
    obtain ⟨C, hC, hcomp⟩ := Submission.dorag_sn_hausdorff_le_mul_of_lower_density P n _ hc
    -- lower density bound `μ_R(B̄_s(x)) ≥ t ωₙ sⁿ` for small `s > 0` on `A`
    have hdens : ∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ s : ℝ, 0 < s → s < t₀ →
        ENNReal.ofReal (t * (unitBallVolume n).toReal * s ^ n) ≤ R.measure (closedBall x s) := by
      rintro x ⟨-, hx⟩
      obtain ⟨-, hlim⟩ := hΘ x
      have hlt : ENNReal.ofReal t < ENNReal.ofReal (Θ x) :=
        (ENNReal.ofReal_lt_ofReal_iff (ht.trans hx)).2 hx
      -- the density ratio exceeds `t` on some interval `(0, t₀)`
      obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hlim (Ioi_mem_nhds hlt))
      refine ⟨t₀, ht₀, fun s hs hst => ?_⟩
      have hfs : ENNReal.ofReal t <
          S.massOn (ball x s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) := hsub ⟨hs, hst⟩
      have hd0 : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hs n)).ne'
      have hdtop : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ ∞ :=
        ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
      calc ENNReal.ofReal (t * (unitBallVolume n).toReal * s ^ n)
          = ENNReal.ofReal t * (unitBallVolume n * ENNReal.ofReal (s ^ n)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg ht.le ENNReal.toReal_nonneg),
              ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal hωtop, mul_assoc]
        _ ≤ S.massOn (ball x s) :=
            (ENNReal.le_div_iff_mul_le (Or.inl hd0) (Or.inl hdtop)).1 hfs.le
        _ = R.measure (ball x s) :=
            Submission.rsd_massOn_eq_measure P n univ S R isOpen_univ hRS _ isOpen_ball
              (subset_univ _)
        _ ≤ R.measure (closedBall x s) := measure_mono ball_subset_closedBall
    -- `μ_R(A) = 0`, so for every `ε > 0` some open `O ⊇ A` has `Hⁿ(A) ≤ C μ_R(O) ≤ C ε`
    have hA0 : R.measure A = 0 := hoff A fun x hx => hx.1
    have hCε : ∀ ε : ℝ≥0∞, 0 < ε → (μHE[n] : Measure (Euclid P)) A ≤ C * ε := by
      intro ε hε
      obtain ⟨O, hO, hAO, hOε⟩ := Submission.dorag_sn_open_superset_measure_lt P R.measure A hA0
        (fun x _ => ⟨1, one_pos, hloc x⟩) ε hε
      exact (hcomp R.measure A O hO hAO hdens).trans (mul_le_mul_right hOε.le C)
    -- let `ε = 1/j → 0`, using `C < ∞`
    have hlim : Tendsto (fun j : ℕ => C * (j : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hC)
    exact le_antisymm (ge_of_tendsto' hlim fun j =>
      hCε _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j))) zero_le
  -- `{x ∉ M : Θ(x) > 0} ⊆ ⋃ₖ {x ∉ M : Θ(x) > 1/(k+1)}`
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hk)
  obtain ⟨k, hkx⟩ := exists_nat_one_div_lt hx.2
  exact mem_iUnion.2 ⟨k, hx.1, hkx⟩

/-- **Simon Ch. 4, p. 91** (Ch. 3, Remark 1.8(1)–(2) and Theorem 1.9): for an integer multiplicity
`T = τ(M, θ, ξ)` in open `U`, `Θⁿ(μ_T, x) = θ(x)` for `μ_T`-a.e. `x`.  Write `μ = Hⁿ⌞M`, so
`μ_T = θμ`, and let `x ∈ M` be a `μ`-generic point, with `B̄_s(x) ⊆ U`.
* `R.orients` gives an approximate tangent plane at `x`, so `μ(B̄_ρ(x))/(ωₙρⁿ) → 1`
  (`Submission.rsd_tendsto_closedBall_density_of_approxTangent`).  The required local finiteness
  of `μ` and `μ_T` is `Submission.rsd_imrep_compact_measure_ne_top`.
* Localized Besicovitch differentiation gives `μ_T(B̄_ρ(x))/μ(B̄_ρ(x)) → θ(x)`
  (`Submission.rsd_ae_tendsto_withDensity_div_closedBall`).
* For small `ρ`, `0 < μ(B̄_ρ(x)) < ∞`, so the product of the two ratios is
  `μ_T(B̄_ρ(x))/(ωₙρⁿ)`, which tends to `θ(x)`.
* Open balls give the same limit (`Submission.rsd_tendsto_ball_density_of_closedBall`), and
  `M_{B_ρ(x)}(T) = μ_T(B_ρ(x))` once `B_ρ(x) ⊆ U` (`Submission.rsd_massOn_eq_measure`).

Since `μ_T ≪ μ`, the `μ`-a.e. statement holds `μ_T`-a.e. -/
theorem Submission.rsd_ae_hasMassDensity_mult : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ᵐ x ∂R.measure, HasMassDensity T x (R.mult x) := by
  intro P n U T R hU hR
  -- `μ = Hⁿ⌞M` and `θ = R.mult`; by definition `μ_T = R.measure = θμ`
  set μ : Measure (Euclid P) := μHE[n].restrict R.carrier with hμ
  set θ : Euclid P → ℝ≥0∞ := fun x => (R.mult x : ℝ≥0∞)
  have hθm : Measurable θ := measurable_from_nat.comp R.measurable_mult
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞ := fun K hK hKU => by
    rw [hμ, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
    exact (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1
  have hνK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞ :=
    fun K hK hKU => (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).2
  -- Besicovitch differentiation of `θμ` with respect to `μ`, at `μ`-a.e. `x ∈ U`
  have hbes := Submission.rsd_ae_tendsto_withDensity_div_closedBall P U μ θ hU hθm hμK hνK
  have key : ∀ᵐ x ∂μ, HasMassDensity T x (R.mult x) := by
    filter_upwards [ae_restrict_mem R.measurableSet_carrier, R.orients, hbes]
      with x hxM hQ hx
    obtain ⟨Q, hxQ, -⟩ := hQ
    have hxU : x ∈ U := R.carrier_subset hxM
    -- a closed ball `B̄_s(x) ⊆ U`; every `B̄_ρ(x)`, `ρ ≤ s`, is a compact subset of `U`
    obtain ⟨s, hs, hsU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
    have hsub : ∀ ρ : ℝ, ρ ≤ s → closedBall x ρ ⊆ U := fun ρ hρ =>
      (closedBall_subset_closedBall hρ).trans hsU
    -- `μ(B̄_ρ(x))/(ωₙρⁿ) → 1` (approximate tangent plane at `x`)
    have hden := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n R.carrier x Q s hs
      (Submission.rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x s) hsU).1 hxQ
    -- `μ_T(B̄_ρ(x))/(ωₙρⁿ) = [μ_T(B̄_ρ(x))/μ(B̄_ρ(x))] · [μ(B̄_ρ(x))/(ωₙρⁿ)] → θ(x) · 1`
    have hclosed : Tendsto (fun ρ : ℝ => R.measure (closedBall x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (θ x)) := by
      have hprod := ENNReal.Tendsto.mul (hx hxU) (Or.inr ENNReal.one_ne_top) hden
        (Or.inl one_ne_zero)
      rw [mul_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hs, hden.eventually_ne one_ne_zero] with ρ hρ hne
      -- `0 < μ(B̄_ρ(x)) < ∞` for small `ρ`
      have hfin : μHE[n] (R.carrier ∩ closedBall x ρ) ≠ ∞ :=
        (Submission.rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x ρ)
          (hsub ρ hρ.2.le)).1
      have hpos : μHE[n] (R.carrier ∩ closedBall x ρ) ≠ 0 := fun h0 =>
        hne (by rw [h0, ENNReal.zero_div])
      have hμρ : μ (closedBall x ρ) = μHE[n] (R.carrier ∩ closedBall x ρ) := by
        rw [hμ, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
      rw [hμρ]
      exact ENNReal.div_mul_div_cancel hpos hfin
    -- open balls, then `M_{B_ρ(x)}(T) = μ_T(B_ρ(x))` for `ρ < s`
    have hopen := Submission.rsd_tendsto_ball_density_of_closedBall P n R.measure x (θ x) hclosed
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rw [ENNReal.ofReal_natCast]
    refine hopen.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    rw [Submission.rsd_massOn_eq_measure P n U T R hU hR (ball x ρ) isOpen_ball
      (ball_subset_closedBall.trans (hsub ρ hρ.2.le))]
  -- `μ_T = θμ ≪ μ`
  exact (withDensity_absolutelyContinuous μ θ).ae_le key

/-- **Simon Ch. 3, Remark 1.8(2) with Theorem 1.9** (as used in Ch. 4, 3.12): if `S = τ(M, θ, ξ)`
in `ℝᴾ` and `Θ(x) = Θⁿ(μ_S, x)` at every `x`, then `Θ = θ` for `Hⁿ`-a.e. `x ∈ M`.
`Θⁿ(μ_S, x) = θ(x)` for `μ_S`-a.e. `x` (`Submission.rsd_ae_hasMassDensity_mult`), so densities
being unique (`Submission.dimred_cs_mi_hasMassDensity_unique`) gives `Θ = θ` `μ_S`-a.e.  Since
`θ ≥ 1` on `M`, `Hⁿ⌞M ≪ θHⁿ⌞M = μ_S`, which transfers the equality to `Hⁿ⌞M`-a.e. -/
theorem Submission.dimred_cs_mi_density_eq_mult_ae : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (Θ : Euclid P → ℝ), R.Represents S → (∀ x : Euclid P, HasMassDensity S x (Θ x)) → ∀ᵐ x ∂((μHE[n] : Measure (Euclid P)).restrict R.carrier), Θ x = (R.mult x : ℝ) := by
  intro P n S R Θ hR hΘ
  -- `Θ = θ` `μ_S`-a.e., by uniqueness of densities
  have hμ : ∀ᵐ x ∂R.measure, Θ x = (R.mult x : ℝ) := by
    filter_upwards [Submission.rsd_ae_hasMassDensity_mult P n univ S R isOpen_univ hR] with x hx
    exact Submission.dimred_cs_mi_hasMassDensity_unique P n univ S x (Θ x) (R.mult x) (hΘ x) hx
  -- `Hⁿ⌞M ≪ μ_S = θHⁿ⌞M`, as `θ ≠ 0` on `M`
  have hθ : ∀ᵐ x ∂((μHE[n] : Measure (Euclid P)).restrict R.carrier),
      (R.mult x : ℝ≥0∞) ≠ 0 := by
    filter_upwards [ae_restrict_mem R.measurableSet_carrier] with x hx
    exact Nat.cast_ne_zero.2 (R.mult_pos x hx).ne'
  exact (withDensity_absolutelyContinuous'
    (measurable_from_nat.comp R.measurable_mult).aemeasurable hθ).ae_le hμ

/-- **`μ_R = Θ Hⁿ`** (step 5 of the measure invariance of a cone with invariant density, in the
cone splitting of the dimension reduction argument; Simon Ch. 4, 3.12, chapter-04.txt
lines 350–354, the canonical representative `θ_V(x) = Θⁿ(V, x)` of `V = v(M, θ)`).  Let
`S = τ(M, θ, ξ)` in `ℝᴾ`, and let `Θⁿ(μ_S, x) = Θ(x)` at every `x`.  Then `θ Hⁿ⌞M = Θ Hⁿ`, i.e.
`μ_R(A) = ∫⁻_A Θ dHⁿ` for every Borel `A`.  Split `∫⁻_A Θ dHⁿ` along the Borel carrier `M`:
* on `A ∩ M`, `Θ = θ` `Hⁿ`-a.e. (`Submission.dimred_cs_mi_density_eq_mult_ae`), so this part is
  `∫⁻_{A∩M} θ dHⁿ = μ_R(A)`;
* on `A \ M`, `Θ ≤ 0` off the `Hⁿ`-null set `{x ∉ M, Θ(x) > 0}`
  (`Submission.dimred_cs_mi_density_null_off_carrier`), so `ofReal Θ = 0` there `Hⁿ`-a.e.

No measurability of `Θ` is needed: a.e.-equal functions have equal lower integrals. -/
theorem Submission.dimred_cs_mi_measure_eq_withDensity : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (Θ : Euclid P → ℝ), R.Represents S → (∀ x : Euclid P, HasMassDensity S x (Θ x)) → R.measure = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (Θ x)) := by
  intro P n S R Θ hR hΘ
  -- Step 1: compare both measures on a Borel set `A`
  ext A hA
  -- Steps 2–3: `μ_R(A) = ∫⁻_{A∩M} θ dHⁿ`, and split `∫⁻_A Θ dHⁿ` along `M`
  rw [IMRep.measure, withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA,
    ← lintegral_inter_add_sdiff _ A R.measurableSet_carrier]
  -- Step 4: on `A ∩ M`, `ofReal Θ = θ` `Hⁿ`-a.e.
  have hM : ∫⁻ x in A ∩ R.carrier, ENNReal.ofReal (Θ x) ∂μHE[n] =
      ∫⁻ x in A ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    have hae := ae_restrict_of_ae_restrict_of_subset
      (inter_subset_right : A ∩ R.carrier ⊆ R.carrier)
      (Submission.dimred_cs_mi_density_eq_mult_ae P n S R Θ hR hΘ)
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx, ENNReal.ofReal_natCast]
  -- Step 5: on `A \ M`, `ofReal Θ = 0` `Hⁿ`-a.e., since `{x ∉ M, Θ(x) > 0}` is `Hⁿ`-null
  have hMc : ∫⁻ x in A \ R.carrier, ENNReal.ofReal (Θ x) ∂μHE[n] = 0 := by
    have hnull := Submission.dimred_cs_mi_density_null_off_carrier P n S R Θ hR hΘ
    have hae : ∀ᵐ x ∂μHE[n], x ∈ A \ R.carrier → ENNReal.ofReal (Θ x) = 0 := by
      refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hnull)
      obtain ⟨hxAM, hx0⟩ := not_imp.1 hx
      exact ⟨hxAM.2, ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 hx0)⟩
    rw [lintegral_congr_ae ((ae_restrict_iff' (hA.diff R.measurableSet_carrier)).2 hae)]
    exact lintegral_zero
  -- Step 6: `∫⁻_A Θ dHⁿ = ∫⁻_{A∩M} θ dHⁿ + 0 = μ_R(A)`
  rw [hM, hMc, add_zero]
/-- **Translation invariance of `ν = Hⁿ.withDensity f` for a translation-invariant density `f`**
(step 6 of the measure invariance proof in the cone splitting argument, with `ofReal ∘ Θ` replaced
by an arbitrary `f`): if `f(y + x) = f(x)` for every `x`, then `ν((y + ·)⁻¹(A)) = ν(A)`, i.e.
`ν(A − y) = ν(A)`, for every Borel `A ⊆ ℝᴾ`.  The translation `τ(x) = y + x` is a bijective
isometry, hence a measurable embedding preserving `Hⁿ`, so
`∫⁻_{τ⁻¹(A)} f(τ(a)) dHⁿ(a) = ∫⁻_A f dHⁿ`; and `f ∘ τ = f` by hypothesis. -/
theorem Submission.dimred_cs_mi_withDensity_translate : ∀ (P n : ℕ) (f : Euclid P → ℝ≥0∞) (y : Euclid P), (∀ x : Euclid P, f (y + x) = f x) → ∀ A : Set (Euclid P), MeasurableSet A → (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => y + x) ⁻¹' A) = (μHE[n] : Measure (Euclid P)).withDensity f A := by
  intro P n f y hf A hA
  -- Step 1: `τ(x) = y + x` is a homeomorphism, hence a measurable embedding; `τ⁻¹(A)` is Borel.
  have hτ : MeasurableEmbedding (fun x : Euclid P => y + x) :=
    (Homeomorph.addLeft y).measurableEmbedding
  -- Step 2: `τ` is a bijective isometry, so it preserves `Hⁿ`.
  have hmp : MeasurePreserving (fun x : Euclid P => y + x) μHE[n] μHE[n] :=
    (IsometryEquiv.addLeft y).measurePreserving_euclideanHausdorffMeasure n
  -- Steps 3–5: `ν(τ⁻¹(A)) = ∫⁻_{τ⁻¹(A)} f(y + a) dHⁿ(a) = ∫⁻_A f dHⁿ = ν(A)`.
  calc (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => y + x) ⁻¹' A)
      = ∫⁻ a in (fun x => y + x) ⁻¹' A, f (y + a) ∂μHE[n] := by
        rw [withDensity_apply _ (hτ.measurable hA)]
        simp only [hf]
    _ = ∫⁻ b in A, f b ∂μHE[n] := hmp.setLIntegral_comp_preimage_emb hτ f A
    _ = (μHE[n] : Measure (Euclid P)).withDensity f A := (withDensity_apply _ hA).symm
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm

/-- **`n`-homogeneity of `f Hⁿ` for a dilation-invariant density `f`** (Simon Lemma 7.3.5,
chapter-07.txt lines 407–420, whose proof is "left to the reader": part (ii) of the invariance of
the mass measure `μ = Θ Hⁿ` of `S` when its density `Θ` is invariant under `w ↦ λw`, with an
arbitrary `f : ℝᴾ → [0, ∞]` in place of `ofReal ∘ Θ`).  If `λ > 0` and `f(λx) = f(x)` for all `x`,
then `(f Hⁿ)(λA) = λⁿ (f Hⁿ)(A)` for every Borel `A ⊆ ℝᴾ`.  `δ(x) = λx` is a homeomorphism, so
`λA = δ(A)` is Borel and `δ⁻¹(λA) = A`; the change of variables (ii) of
`Submission.euclid_hausdorff_dilation_change_of_variables` with `g = f` and `f ∘ δ = f` gives
`(f Hⁿ)(A) = λ⁻ⁿ (f Hⁿ)(λA)`, and `λⁿ λ⁻ⁿ = 1`. -/
theorem Submission.dimred_cs_mi_withDensity_dilate : ∀ (P n : ℕ) (f : Euclid P → ℝ≥0∞) (lam : ℝ), 0 < lam → (∀ x : Euclid P, f (lam • x) = f x) → ∀ A : Set (Euclid P), MeasurableSet A → (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * (μHE[n] : Measure (Euclid P)).withDensity f A := by
  intro P n f lam hlam hf A hA
  -- Step 1: `δ(x) = λx` is a homeomorphism, hence a measurable embedding: `D = δ(A)` is Borel and
  -- `δ⁻¹(D) = A` by injectivity.
  have hδ : MeasurableEmbedding (fun x : Euclid P => lam • x) :=
    (Homeomorph.smulOfNeZero lam hlam.ne').measurableEmbedding
  have hD : MeasurableSet ((fun x : Euclid P => lam • x) '' A) := hδ.measurableSet_image.2 hA
  have hpre : (fun x : Euclid P => lam • x) ⁻¹' ((fun x : Euclid P => lam • x) '' A) = A :=
    Set.preimage_image_eq A hδ.injective
  -- Steps 2–3: change of variables (ii) with `c = λ`, `M = D`, `g = f`; with `δ⁻¹(D) = A` and
  -- `f(λz) = f(z)` it reads `∫⁻_A f dHⁿ = λ⁻ⁿ ∫⁻_D f dHⁿ`.
  have h := (Submission.euclid_hausdorff_dilation_change_of_variables P n lam hlam
    ((fun x : Euclid P => lam • x) '' A)).2.1 f
  rw [hpre] at h
  simp only [hf] at h
  -- Steps 4–5: `ν(A) = λ⁻ⁿ ν(D)` by `withDensity_apply` (`A`, `D` Borel), and
  -- `ofReal(λⁿ) ofReal(λ⁻ⁿ) = ofReal((λλ⁻¹)ⁿ) = 1`.
  rw [withDensity_apply _ hD, withDensity_apply _ hA, h, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
    ENNReal.ofReal_one, one_mul]

/-- **Density invariance gives invariance of the mass measure** (the measure step of the cone
splitting in the dimension-reducing argument, Simon 7.3.4–7.3.5, chapter-07.txt lines 380–417).
Let `S = τ(M, θ, ξ)` in `ℝᴾ` have a density `Θ(x)` at every `x`, and let
`HasMassDensity S w θ → HasMassDensity S (y + λw) θ` for `y ∈ L`, `λ > 0`.  Then `μ = θHⁿ⌞M`
satisfies (i) `μ(A − y) = μ(A)` for `y ∈ L` and (ii) `μ(λA) = λⁿμ(A)` for `λ > 0`, `A` Borel.
Densities are unique, so `Θ(y + λw) = Θ(w)`; `μ = Θ·Hⁿ` (Simon Ch. 3, Remark 1.8(2); Ch. 1,
Theorem 3.6); and `Θ·Hⁿ` inherits translation invariance and `n`-homogeneity from `Hⁿ`. -/
theorem Submission.dimred_cs_measure_invariant_of_density_invariant : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), 0 < n → R.Represents S → (∀ x : Euclid P, ∃ θ : ℝ, HasMassDensity S x θ) → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ (w : Euclid P) (θ : ℝ), HasMassDensity S w θ → HasMassDensity S (y + lam • w) θ) → (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => y + x) ⁻¹' A) = R.measure A) ∧ ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n S R L _hn hRS hdens hinv
  -- Step 1: choose the density `Θ(x)` of `S` at every `x`.
  choose Θ hΘ using hdens
  -- Step 2: `μ = Θ·Hⁿ`.
  have hμ : R.measure = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (Θ x)) :=
    Submission.dimred_cs_mi_measure_eq_withDensity P n S R Θ hRS hΘ
  -- Step 3: densities are unique, so `Θ(y + λw) = Θ(w)` for `y ∈ L`, `λ > 0`.
  have hΘinv : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ w : Euclid P, Θ (y + lam • w) = Θ w :=
    fun y hy lam hlam w => Submission.dimred_cs_mi_hasMassDensity_unique P n univ S (y + lam • w)
      _ _ (hΘ (y + lam • w)) (hinv y hy lam hlam w (Θ w) (hΘ w))
  refine ⟨fun y hy A hA => ?_, fun lam hlam A hA => ?_⟩
  -- Step 4, (i): `Θ(y + x) = Θ(x)` (`λ = 1`), and `Θ·Hⁿ` is invariant under such translations.
  · rw [hμ]
    refine Submission.dimred_cs_mi_withDensity_translate P n _ y (fun x => ?_) A hA
    have h := hΘinv y hy 1 one_pos x
    rw [one_smul] at h
    exact congrArg ENNReal.ofReal h
  -- Step 5, (ii): `Θ(λx) = Θ(x)` (`y = 0 ∈ L`), and `Θ·Hⁿ` is `n`-homogeneous under such dilations.
  · rw [hμ]
    refine Submission.dimred_cs_mi_withDensity_dilate P n _ lam hlam (fun x => ?_) A hA
    have h := hΘinv 0 L.zero_mem lam hlam x
    rw [zero_add] at h
    exact congrArg ENNReal.ofReal h
/-- **Cut-off quadratic moments over `n`-planes** (the constant `cₙ` of the measurability proof
for the approximate tangent planes of Simon Ch. 3, 1.4).  For `n ≥ 1` one constant `c > 0`,
depending only on `n`, gives `∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|²` for every `P`,
every `n`-dimensional subspace `Q ⊆ ℝᴾ` and every `u ∈ ℝᴾ`.  On `ℝⁿ` put
`q(w) = ∫ max(1 − |z|², 0)⟨w, z⟩² dHⁿ(z)` and `c = q(e)`, `|e| = 1`: linear isometries preserve
`Hⁿ`, so `q` is invariant under them, `q(tw) = t²q(w)`, and a reflection maps `|w|e` to `w`,
whence `q(w) = c|w|²`; `c > 0` since the integrand is continuous, `≥ 0`, compactly supported and
`3/16` at `e/2`.  An isometry `ι = L⁻¹ : ℝⁿ → Q ⊆ ℝᴾ` carries `Hⁿ` to `Hⁿ⌞Q`, and
`⟨u, ι z⟩ = ⟨L(p_Q u), z⟩`, so the integral is `q(L(p_Q u)) = c|p_Q u|²`. -/
theorem Submission.exists_plane_cutoff_quadratic_moment_eq : ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ u : Euclid P, ∫ y in (Q : Set (Euclid P)), max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 ∂μHE[n] = c * ‖Q.starProjection u‖ ^ 2 := by
  intro n hn
  -- The moment `q(w)` on the model plane `ℝⁿ`; the constant is `c = q(e)` for a unit vector `e`.
  obtain ⟨q, hq_def⟩ : ∃ q : Euclid n → ℝ,
      ∀ w, q w = ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ w z ^ 2 ∂μHE[n] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Euclid n, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  -- `q(Rw) = q(w)` for a linear isometry `R`: substitute `z = Rz'`, `R` preserves `Hⁿ`.
  have hq_iso : ∀ (R : Euclid n ≃ₗᵢ[ℝ] Euclid n) (w : Euclid n), q (R w) = q w := by
    intro R w
    have key : ∫ z, max (1 - ‖R z‖ ^ 2) 0 * inner ℝ (R w) (R z) ^ 2 ∂μHE[n] =
        ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ (R w) z ^ 2 ∂μHE[n] :=
      (R.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n).integral_comp
        R.toHomeomorph.measurableEmbedding (fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ (R w) y ^ 2)
    simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map] at key
    rw [hq_def, hq_def, ← key]
  have hq_smul : ∀ (t : ℝ) (w : Euclid n), q (t • w) = t ^ 2 * q w := by
    intro t w
    rw [hq_def, hq_def, ← integral_const_mul]
    congr 1
    funext z
    rw [real_inner_smul_left]
    ring
  -- `q(w) = c|w|²`: the reflection in `(|w|e − w)ᗮ` maps `|w|e` to `w`.
  have hq : ∀ w : Euclid n, q w = q e * ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖‖w‖ • e‖ = ‖w‖ := by rw [norm_smul, he, mul_one, norm_norm]
    obtain ⟨R, hR⟩ : ∃ R : Euclid n ≃ₗᵢ[ℝ] Euclid n, R (‖w‖ • e) = w :=
      ⟨_, Submodule.reflection_sub h1⟩
    calc q w = q (R (‖w‖ • e)) := by rw [hR]
      _ = q (‖w‖ • e) := hq_iso R _
      _ = q e * ‖w‖ ^ 2 := by rw [hq_smul, mul_comm]
  -- `c > 0`: on `ℝⁿ`, `Hⁿ` is Lebesgue measure, and the integrand is `3/16` at `e/2`.
  have hc : 0 < q e := by
    have hcont : Continuous fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      fun_prop
    have hsupp : HasCompactSupport fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz => ?_
      have h1 : 1 < ‖z‖ := by simpa using hz
      have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right h2]
    have hnonneg : 0 ≤ fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 :=
      fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)
    have hx : (fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2) ((1 / 2 : ℝ) • e) ≠ 0 := by
      simp only [norm_smul, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      norm_num
    rw [hq_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg hx
  refine ⟨q e, hc, fun P Q hQ u => ?_⟩
  -- An orthonormal basis of `Q` indexed by `Fin n` gives `L : Q ≃ ℝⁿ`; `ι = L⁻¹` is an isometry
  -- of `ℝⁿ` onto `Q ⊆ ℝᴾ`, so `ι_# Hⁿ = Hⁿ⌞Q`.
  obtain ⟨L, -⟩ : ∃ L : Q ≃ₗᵢ[ℝ] Euclid n, True :=
    ⟨((stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)).repr, trivial⟩
  have hι : Isometry fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    isometry_subtype_coe.comp L.symm.isometry
  have hrange : Set.range (fun z : Euclid n => ((L.symm z : Q) : Euclid P)) =
      (Q : Set (Euclid P)) := by
    ext y
    refine ⟨?_, fun hy => ⟨L ⟨y, hy⟩, by simp⟩⟩
    rintro ⟨z, rfl⟩
    exact (L.symm z).2
  have hemb : MeasurableEmbedding fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    hι.isClosedEmbedding.measurableEmbedding
  have hnorm : ∀ z : Euclid n, ‖((L.symm z : Q) : Euclid P)‖ = ‖z‖ := fun z => L.symm.norm_map z
  -- `⟨u, ι z⟩ = ⟨p_Q u, ι z⟩ = ⟨L(p_Q u), z⟩`.
  have hinner : ∀ z : Euclid n, inner ℝ u ((L.symm z : Q) : Euclid P) =
      inner ℝ (L (Q.orthogonalProjectionOnto u)) z := by
    intro z
    rw [LinearIsometryEquiv.inner_map_eq_flip,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← hrange, ← hι.map_euclideanHausdorffMeasure, hemb.integral_map]
  simp only [hnorm, hinner]
  rw [← hq_def, hq, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
  rfl
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
  intro P n M x r hr f
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` is a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P,
      ⇑e = Poincare.SimonGMT.Chapter03.blowUpMap x r :=
    ⟨(Homeomorph.subRight x).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr.ne')), rfl⟩
  -- `Hⁿ(η_{x,r}(S)) = ‖r⁻¹‖₊ⁿ Hⁿ(S)` for every set `S`
  have hscale : ∀ S : Set (Euclid P), μHE[n] (e '' S) = ‖r⁻¹‖₊ ^ n • μHE[n] S := by
    intro S
    have hS : e '' S = (fun y => r⁻¹ • y) '' ((IsometryEquiv.subRight x) '' S) := by
      rw [image_image, he]
      rfl
    rw [hS, image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_{x,r}(M) = ‖r⁻¹‖₊ⁿ η_{x,r#}(Hⁿ⌞M)`, checked on Borel sets
  have hmeas : μHE[n].restrict (e '' M) = (‖r⁻¹‖₊ ^ n) • (μHE[n].restrict M).map e := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.smul_apply, Measure.map_apply e.measurable hA,
      Measure.restrict_apply (hA.preimage e.measurable), ← hscale, image_inter e.injective,
      e.image_preimage]
  -- change of variables, with `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n`
  rw [← he, hmeas, integral_smul_nnreal_measure, e.measurableEmbedding.integral_map,
    NNReal.smul_def, smul_eq_mul, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hr)]
/-- Continuity in the centre of the blow-up integrals of Simon Ch. 3, 1.4: for `f` continuous with
compact support, `r > 0` and `μ` finite on compact sets, `x ↦ ∫ f(η_{x,r}(y)) dμ(y)` is continuous,
`η_{x,r}(y) = r⁻¹(y − x)`.  With `‖f‖ ≤ C` and `tsupport f ⊆ B̄_R(0)`, the integrand vanishes for
`x ∈ B_1(x₀)` and `y ∉ B = B̄_{1+rR}(x₀)`; so near `x₀` it is dominated by `C·1_B`, integrable as
`μ(B) < ∞`, and dominated convergence gives continuity at `x₀`. -/
theorem Submission.continuous_integral_comp_blowUpMap : ∀ (P : ℕ) (μ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μ) := by
  intro P μ hμ f hf hfs r hr
  -- `‖f‖ ≤ C` and `tsupport f ⊆ closedBall 0 R`
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  obtain ⟨R, hR⟩ := hfs.isCompact.isBounded.subset_closedBall 0
  -- `(x, y) ↦ f (r⁻¹ • (y - x))` is jointly continuous
  have hF : Continuous fun p : Euclid P × Euclid P =>
      f (Poincare.SimonGMT.Chapter03.blowUpMap p.1 r p.2) :=
    hf.comp ((continuous_snd.sub continuous_fst).const_smul r⁻¹)
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  -- dominated convergence with the bound `C · 1_B`, `B = closedBall x₀ (1 + r R)`
  refine continuousAt_of_dominated (bound := (closedBall x₀ (1 + r * R)).indicator fun _ => C)
    (Eventually.of_forall fun x => (hF.comp (Continuous.prodMk_right x)).aestronglyMeasurable)
    ?_ ?_ (Eventually.of_forall fun y => (hF.comp (Continuous.prodMk_left y)).continuousAt)
  · -- for `x ∈ ball x₀ 1`, `f (r⁻¹ • (y - x)) ≠ 0` forces `‖y - x‖ ≤ r R`, so `y ∈ B`
    filter_upwards [ball_mem_nhds x₀ one_pos] with x hx
    refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ closedBall x₀ (1 + r * R)
    · rw [indicator_of_mem hy]
      exact hC _
    · rw [indicator_of_notMem hy]
      refine le_of_eq (norm_eq_zero.2 (by_contra fun h => hy ?_))
      have h1 := hR (subset_tsupport f h)
      rw [mem_closedBall, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_le_iff₀ hr, ← dist_eq_norm] at h1
      rw [mem_ball] at hx
      rw [mem_closedBall]
      linarith [dist_triangle y x x₀]
  · -- `C · 1_B` is integrable: `B` is compact, so `μ B < ∞`
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact integrableOn_const (hμ _ (isCompact_closedBall _ _))

/-- **Simon Ch. 3, 1.4**: if `Hⁿ(M ∩ K) < ∞` for every compact `K`, `f` is continuous with
compact support and `r > 0`, then the blow-up integral `x ↦ ∫_{η_{x,r}(M)} f dHⁿ` is continuous.
It equals `r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`, continuous in `x` because `Hⁿ⌞M` is finite on compact
sets. -/
theorem Submission.continuous_blowUp_image_setIntegral : ∀ (P n : ℕ) (M : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∀ r : ℝ, 0 < r → Continuous (fun x : Euclid P => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) := by
  intro P n M hM f hf hfs r hr
  -- `Hⁿ⌞M` is finite on compact sets: `(Hⁿ⌞M)(K) = Hⁿ(M ∩ K)`, `K` being closed
  have hμ : ∀ K : Set (Euclid P), IsCompact K → (μHE[n].restrict M) K ≠ ∞ := fun K hK => by
    rw [Measure.restrict_apply hK.isClosed.measurableSet, inter_comm]
    exact hM K hK
  -- change of variables, then continuity of `x ↦ r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`
  exact (continuous_const.mul
    (Submission.continuous_integral_comp_blowUpMap P _ hμ f hf hfs r hr)).congr fun x =>
      (Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul P n M x r hr f).symm
/-- A field of orthogonal projections `p_x = (K x).starProjection` is a.e.-measurable (Borel
σ-algebra of the operator-norm topology) when each quadratic form `x ↦ |p_x u|²` is.  As `p_x` is
self-adjoint and idempotent, `⟪p_x u, w⟫ = (|p_x(u + w)|² − |p_x(u − w)|²)/4`, so the matrix
coefficients `⟪p_x e_a, e_b⟫` are a.e.-measurable, and `p_x = Σ_{a,b} ⟪p_x e_a, e_b⟫ ⟪e_a, ·⟫ e_b`
is a continuous linear function of them. -/
theorem Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K : Euclid P → Submodule ℝ (Euclid P)), (∀ u : Euclid P, AEMeasurable (fun x => ‖(K x).starProjection u‖ ^ 2) μ) → AEMeasurable (fun x => (K x).starProjection) μ := by
  intro P μ K h
  -- by polarization every coefficient `x ↦ ⟪p_x u, w⟫` is a.e.-measurable
  have hcoef : ∀ u w : Euclid P,
      AEMeasurable (fun x => inner ℝ ((K x).starProjection u) w) μ := by
    intro u w
    have key : ∀ x, inner ℝ ((K x).starProjection u) w =
        (‖(K x).starProjection (u + w)‖ ^ 2 - ‖(K x).starProjection (u - w)‖ ^ 2) / 4 := by
      intro x
      have hsym : inner ℝ ((K x).starProjection u) w =
          inner ℝ ((K x).starProjection u) ((K x).starProjection w) := by
        rw [Submodule.inner_starProjection_left_eq_right,
          Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 ((K x).starProjection_apply_mem w)]
      rw [hsym, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
      ring
    simp_rw [key]
    exact ((h (u + w)).sub (h (u - w))).div_const 4
  -- `p_x = Λ (g x)`, `Λ m = ∑ m_{ab} ⟪e_a, ·⟫ e_b`, `g x = (⟪p_x e_a, e_b⟫)_{ab}`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Λ : (Fin P × Fin P → ℝ) → (Euclid P →L[ℝ] Euclid P) := fun m =>
    ∑ ab, m ab • (innerSL ℝ (e ab.1)).smulRight (e ab.2)
  have heq : (fun x => (K x).starProjection) =
      fun x => Λ fun ab => inner ℝ ((K x).starProjection (e ab.1)) (e ab.2) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Λ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Fintype.sum_prod_type]
    calc (K x).starProjection v = (K x).starProjection (∑ a, inner ℝ (e a) v • e a) := by
          rw [e.sum_repr']
      _ = ∑ a, inner ℝ (e a) v • (K x).starProjection (e a) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, inner ℝ (e a) v • ∑ b, inner ℝ (e b) ((K x).starProjection (e a)) • e b := by
          simp only [e.sum_repr']
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [real_inner_comm (e b), smul_smul, smul_smul, mul_comm]
  -- `Λ` is continuous and `g` is a.e.-measurable coordinatewise
  have hΛ : Continuous Λ :=
    continuous_finsetSum _ fun ab _ => (continuous_apply ab).smul continuous_const
  rw [heq]
  exact hΛ.measurable.comp_aemeasurable (AEMeasurable.of_eval fun ab => hcoef _ _)

/-- **Simon Ch. 3, 1.4; Ch. 4**: the approximate tangent planes `TₓM` of an integer multiplicity
representation `R = (M, θ, ξ)` in `ℝᴾ` form an `R.measure`-a.e.-measurable field of orthogonal
projections `x ↦ p_{TₓM}` (Borel σ-algebra of the operator-norm topology).  For `n = 0` every
`TₓM` is `⊥`.  For `n ≥ 1` let `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`: as `θ ≥ 1` on `M`,
`Hⁿ⌞M` is finite on compact sets, so `x ↦ ∫_{η_{x,r}(M)} f_u dHⁿ` is continuous; at `μ`-a.e. `x`
(`R.orients`, `μ = θHⁿ⌞M ≪ Hⁿ⌞M`) `TₓM` exists and these integrals tend, along `r = 1/(k+1)`, to
`∫_{TₓM} f_u dHⁿ = cₙ|p_{TₓM} u|²`, `cₙ > 0`.  So each `x ↦ |p_{TₓM} u|²` is a.e.-measurable,
hence so is `x ↦ p_{TₓM}`. -/
theorem Submission.imrep_univ_tangent_starProjection_aemeasurable : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n R
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: a `0`-dimensional approximate tangent plane is `⊥`, so `p_{TₓM} = 0` for every `x`
    have h0 : ∀ x, (approxTangentPlane 0 R.carrier x).starProjection = 0 := by
      intro x
      have hx : approxTangentPlane 0 R.carrier x = ⊥ := by
        unfold approxTangentPlane
        split_ifs with h
        · exact Submodule.finrank_eq_zero.1 h.choose_spec.1
        · rfl
      rw [hx, Submodule.starProjection_bot]
    simp_rw [h0]
    exact aemeasurable_const
  obtain ⟨c, hc, hcQ⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
  -- `Hⁿ(M ∩ K) ≤ ∫_{M ∩ K} θ dHⁿ < ∞` for compact `K`, as `θ ≥ 1` on `M`
  have hM : ∀ K : Set (Euclid P), IsCompact K → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK (subset_univ K)) ?_
    calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hK.isClosed.measurableSet)
          fun x hx => by exact_mod_cast R.mult_pos x hx.1
  -- `TₓM` is an approximate tangent plane at `μ`-a.e. `x`, since `μ ≪ Hⁿ⌞M`
  have hT : ∀ᵐ x ∂R.measure,
      HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
    have h : ∀ᵐ x ∂μHE[n].restrict R.carrier,
        HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, hQ, -⟩ := hx
      have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
      unfold approxTangentPlane
      rw [dite_eq_left h]
      exact h.choose_spec
    exact (withDensity_absolutelyContinuous _ _).ae_le h
  refine Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq P R.measure
    (approxTangentPlane n R.carrier) fun u => ?_
  -- the test function `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²`, continuous with support in `B̄₁(0)`
  obtain ⟨φ, hφ_def⟩ : ∃ φ : Euclid P → ℝ, φ = fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 :=
    ⟨_, rfl⟩
  have hφ : Continuous φ := by
    rw [hφ_def]
    fun_prop
  have hφs : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1) fun z hz => ?_
    have h1 : 1 < ‖z‖ := by simpa using hz
    have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
    simp [hφ_def, max_eq_right h2]
  -- `|p_x u|² = lim_k c⁻¹ ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` at `μ`-a.e. `x`
  refine aemeasurable_of_tendsto_metrizable_ae' (f := fun (k : ℕ) x => c⁻¹ *
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (1 / ((k : ℝ) + 1)) '' R.carrier, φ y ∂μHE[n])
    (fun k => (continuous_const.mul (Submission.continuous_blowUp_image_setIntegral P n R.carrier
      hM φ hφ hφs (1 / ((k : ℝ) + 1)) (by positivity))).aemeasurable) ?_
  filter_upwards [hT] with x hx
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
  have hval : ‖(approxTangentPlane n R.carrier x).starProjection u‖ ^ 2 =
      c⁻¹ * ∫ y in (approxTangentPlane n R.carrier x : Set (Euclid P)), φ y ∂μHE[n] := by
    rw [hφ_def, hcQ P _ hx.1 u, inv_mul_cancel_left₀ hc.ne']
  rw [hval]
  exact ((hx.2 ⟨⟨φ, hφ⟩, hφs⟩).comp hr).const_mul c⁻¹
/-- **The approximate tangent projection of an integer multiplicity triple is measurable**
(Simon Ch. 3, 1.4 and 1.5(1); Ch. 6, 3.1).  For `R = (M, θ, ξ)`, `x ↦ p_{TₓM}` is
`Hⁿ⌞M`-a.e. strongly measurable.  By uniqueness of approximate tangent planes, `TₓM` is a.e. the
plane oriented by `ξ(x)`.  A unit simple `n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if
also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and `y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is
`τ` with `τᵢ` replaced by `y`, gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.
Hence `p_{TₓM} = G(ξ(x))` a.e., where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there
is none).  `G` is Borel: `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of
orthonormal frames and signs, and `G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.imrep_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) := by
  intro P n U R
  classical
  -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
  let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
    (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
    fun τ α => rfl
  -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
  let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
  have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
  let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
  have hΩ : IsCompact Ω := by
    refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
    · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
          ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
        ext τ
        simp [orthonormal_iff_ite]
      rw [hset]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
    · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
  -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
  have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
    intro ζ Q
    constructor
    · rintro ⟨τ, hτ, hQ, h | h⟩
      · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
      · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
    · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
      refine ⟨τ, hτ, hQ, ?_⟩
      rcases hs with rfl | rfl
      · left
        intro α
        simp [Φ, hev]
      · right
        intro α
        simp [Φ, hev]
  -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
  have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
    intro c
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
    let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro u
      rw [← Matrix.det_transpose]
      rfl
    have hAc : Continuous fun u : Fin n → Euclid P => A u := by
      simp only [hA]
      exact Continuous.matrix_det (continuous_matrix fun k j => by
        simp only [Matrix.of_apply]
        exact continuous_const.inner (continuous_apply j))
    exact ⟨{ A with cont := hAc }, hA⟩
  -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
  -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
  have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
    rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
      Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
    -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
    have h1 : α τ = inner ℝ y (τ i) := by
      rw [hα]
      have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
        ext k j
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
      rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
        ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
    have h2 : α τ' = 0 := by
      rw [hα]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [Matrix.of_apply, Function.update_self]
      rw [real_inner_comm]
      exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
    have h3 : ζ α = 0 := by
      rcases hζ' with h | h <;> simp [h, h2]
    rcases hζ with h | h
    · rw [← h1, ← h, h3]
    · have h4 := h α
      rw [h3] at h4
      rw [← h1]
      linarith
  have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
    fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
  -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in `τ`
  let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
    fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
  have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
    intro ω v
    simp [F]
  have hFc : Continuous F := by
    refine continuous_clm_apply.mpr fun v => ?_
    simp only [hFapply]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
    rintro ⟨τ, s⟩ ⟨hτ, -⟩
    refine ContinuousLinearMap.ext fun v => ?_
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hFapply]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨j, rfl⟩
        rw [hFapply, inner_sub_left, sum_inner]
        simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
  -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
  let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
    if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
  have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
    intro ζ Q hQ
    have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
    simp only [G, dite_eq_left hex]
    rw [huniq _ _ _ hex.choose_spec hQ]
  have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
    rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is a compact set `Φ(Ω ∩ F⁻¹(t))` together with the
  -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
  have hG : Measurable G := by
    refine measurable_of_isClosed fun t ht => ?_
    have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
        ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
      ext ζ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
      · obtain ⟨Q, hQ⟩ := h
        obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
        have hGζ : G ζ = F ω := by
          rw [← hΦω]
          exact hGΦ ω hω
        constructor
        · intro hζt
          exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
        · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
          · rw [← hΦω', hGΦ ω' hω']
            exact hω't
          · exact absurd ⟨ω, hω, hΦω⟩ hn
      · have hGζ : G ζ = 0 := dite_eq_right h
        have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
          h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
        rw [hGζ]
        constructor
        · intro h0
          exact Or.inr ⟨hn, h0⟩
        · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
          · exact absurd ⟨ω', hω', hΦω'⟩ hn
          · exact h0
    rw [hset]
    exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
      ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
  -- a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes), so
  -- `p_{TₓM} = G(ξ(x))`
  have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
      =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
    filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have h1 : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    rw [Function.comp_apply, hGQ _ _ hor, h1]
  -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
    ).congr hae.symm
/-- **A.e. strongly measurable maps into `L(ℝᴾ, ℝᴾ)` are a.e. measurable.**  With the operator
norm, `Euclid P →L[ℝ] Euclid P` is a metric space whose measurable structure is its Borel
σ-algebra (`ContinuousLinearMap.instBorelSpace`).  A strongly measurable representative `g` of `f`
is a pointwise limit of simple functions `gₖ`; for open `O ≠ L`, `dist(gₖ, Oᶜ) → dist(g, Oᶜ)`, so
`g⁻¹(O) = {dist(g, Oᶜ) > 0}` is measurable.  Hence `g` is Borel measurable and `f = g` a.e. -/
theorem Submission.dtc_cone_opEuclid_aemeasurable_of_aesm : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable f μ → AEMeasurable f μ := by
  intro P μ f hf
  exact hf.aemeasurable

/-- **The approximate tangent projection of an integer multiplicity triple is a.e. measurable**
(Simon Ch. 3, 1.4 and 1.5(1); Ch. 6, 3.1).  For `R = (M, θ, ξ)`, `x ↦ p_{TₓM}` is
`Hⁿ⌞M`-a.e. strongly measurable, since a.e. `TₓM` is the plane oriented by `ξ(x)`.  A.e. strongly
measurable maps into the finite-dimensional normed space `L(ℝᴾ, ℝᴾ)` are a.e. measurable for its
Borel σ-algebra. -/
theorem Submission.dtc_cone_tangentProjection_aemeasurable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) := by
  intro P n U R
  exact Submission.dtc_cone_opEuclid_aemeasurable_of_aesm P _ _
    (Submission.imrep_approxTangent_starProjection_aesm P n U R)
/-- **Simon 4.3.6, the stationary monotonicity identity** (Ch. 4, 3.1–3.6, chapter-04.txt
lines 215–307, applied with `U = ℝᴾ`; used in the proof of 7.3.1, chapter-07.txt line 356).
Let `R = (M, θ, ξ)` be an integer multiplicity triple in `ℝᴾ` with `V = v(M, θ)` stationary:
`δV(X) = 0` for every `X ∈ C¹_c(ℝᴾ; ℝᴾ)`.  Then for `z ∈ ℝᴾ` and `0 < σ ≤ ρ`, with closed balls,
`μ_V = θHⁿ⌞M` and `p_x` the orthogonal projection onto `TₓM`,
`σ⁻ⁿμ_V(B_σ(z)) + ∫_{B_ρ(z) \ B_σ(z)} |(x − z) − p_x(x − z)|² / |x − z|ⁿ⁺² dμ_V = ρ⁻ⁿμ_V(B_ρ(z))`.
`δV(X) = ∫ div_M X dμ_V`, and for `X(x) = η(|x − z|²)(x − z)` (3.2), `μ_V`-a.e.
`div_M X = nη + 2η'|p_x(x − z)|²`, since `dim TₓM = n` and `x ↦ p_x` is `μ_V`-measurable
(`dtc_cone_tangentProjection_aemeasurable`, `μ_V ≪ Hⁿ⌞M`).  Simon integrates (3.3) for the
cutoffs `φ(r/t)` against `t⁻ⁿ⁻¹ dt` over `[σ, ρ]` (3.4–3.5); here this is done in the field:
`η = F ∘ m_σ − F ∘ m_ρ` with `F(u) = u^{-n/2}` and `m_c` a `C¹` smoothing of `max(·, c²)` on
`[c², c² + ε]`, so `η → max(·, σ²)^{-n/2} − max(·, ρ²)^{-n/2}` as `ε ↓ 0`.  The divergences
converge pointwise and are uniformly bounded on `B_{ρ+1}(z)`, so dominated convergence (3.6)
gives `n(σ⁻ⁿμ_V(B_σ) − ρ⁻ⁿμ_V(B_ρ) + ∫_{B_ρ \ B_σ} |D^⊥r|²r⁻ⁿ dμ_V) = 0`, with `D^⊥r` the normal
part of `(x − z)/|x − z|`.  For `n = 0`, `TₓM = 0` a.e. and the identity is additivity of
`μ_V`. -/
theorem Submission.dtc_cone_monotonicity_identity : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → ∀ (z : Euclid P) (σ ρ : ℝ), 0 < σ → σ ≤ ρ → R.measure (closedBall z σ) / ENNReal.ofReal (σ ^ n) + ∫⁻ x in closedBall z ρ \ closedBall z σ, ENNReal.ofReal (‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 / ‖x - z‖ ^ (n + 2)) ∂R.measure = R.measure (closedBall z ρ) / ENNReal.ofReal (ρ ^ n) := by
  intro P n R hstat z σ ρ hσ hσρ
  classical
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- `μ_V = θHⁿ⌞M` is finite on compact sets
  have : IsFiniteMeasureOnCompacts R.measure := ⟨fun K hK => by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK (subset_univ K)).lt_top⟩
  -- `x ↦ p_x` is `μ_V`-measurable, since `μ_V ≪ Hⁿ⌞M`
  have hp : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure :=
    (Submission.dtc_cone_tangentProjection_aemeasurable P n univ R).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hpv : AEMeasurable
      (fun x => ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2) R.measure :=
    (ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
      (hp.prodMk (measurable_id.sub_const z).aemeasurable)).norm.pow_const 2
  -- `μ_V`-a.e., `TₓM` is an `n`-dimensional approximate tangent plane
  have hrank : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.finrank_eq
  -- Pythagoras: `|(x - z) - p_x(x - z)|² = |x - z|² - |p_x(x - z)|²`
  have hpyth : ∀ x : Euclid P,
      ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 =
        ‖x - z‖ ^ 2 - ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
    intro x
    have h := Submodule.norm_sq_eq_add_norm_sq_starProjection (x - z)
      (approxTangentPlane n R.carrier x)
    rw [Submodule.starProjection_orthogonal] at h
    simp only [sub_apply, ContinuousLinearMap.id_apply] at h
    linarith
  -- the first variation is the `μ_V`-integral of `div_M X`
  have hfv : ∀ Y : Euclid P → Euclid P,
      R.firstVariation Y = ∫ x, tangentialDivergence n R.carrier Y x ∂R.measure := by
    intro Y
    have hd : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    have hm : Measurable fun x => (R.mult x : NNReal) :=
      (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R.measurable_mult
    rw [IMRep.measure, IMRep.firstVariation, hd, integral_withDensity_eq_integral_smul hm]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [NNReal.smul_def])
  -- Simon 4.3.2–4.3.3 for radial fields `X(x) = η(|x - z|²)(x - z)`:
  -- `div_M X = n η(|x - z|²) + 2η'(|x - z|²)|p_x(x - z)|²` `μ_V`-a.e.
  have hrad : ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → ∀ R0 : ℝ, (∀ s, R0 ^ 2 ≤ s → η s = 0) →
      ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2) + 2 * deriv η (‖x - z‖ ^ 2) *
        ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2) ∂R.measure = 0 := by
    intro η hη R0 hcut
    have hsub : ContDiff ℝ 1 (fun x : Euclid P => x - z) := contDiff_id.sub contDiff_const
    have hX : ContDiff ℝ 1 (fun x : Euclid P => η (‖x - z‖ ^ 2) • (x - z)) :=
      (hη.comp (hsub.norm_sq ℝ)).smul hsub
    have hXc : HasCompactSupport (fun x : Euclid P => η (‖x - z‖ ^ 2) • (x - z)) := by
      refine (isCompact_closedBall z |R0|).of_isClosed_subset (isClosed_tsupport _) ?_
      refine closure_minimal (fun x hx => ?_) isClosed_closedBall
      by_contra hball
      have hnorm : |R0| < ‖x - z‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hball
      have hR0 : R0 ^ 2 ≤ ‖x - z‖ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hnorm.le 2
      exact hx (by simp [hcut _ hR0])
    have hD : ∀ x : Euclid P, HasFDerivAt (fun y : Euclid P => η (‖y - z‖ ^ 2) • (y - z))
        (η (‖x - z‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
          (2 * deriv η (‖x - z‖ ^ 2)) • (innerSL ℝ (x - z)).smulRight (x - z)) x := by
      intro x
      have hs : HasFDerivAt (fun y : Euclid P => y - z) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
        hasFDerivAt_sub_const z
      have hηx := ((hη.differentiable (by simp)) (‖x - z‖ ^ 2)).hasDerivAt
      refine ((hηx.comp_hasFDerivAt x hs.norm_sq).smul hs).congr_fderiv
        (ContinuousLinearMap.ext fun w => ?_)
      simp only [Function.comp_apply, add_apply, smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      module
    have htr : ∀ x : Euclid P,
        tangentialDivergence n R.carrier (fun y : Euclid P => η (‖y - z‖ ^ 2) • (y - z)) x =
          η (‖x - z‖ ^ 2) * (Module.finrank ℝ (approxTangentPlane n R.carrier x) : ℝ) +
            2 * deriv η (‖x - z‖ ^ 2) *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
      intro x
      rw [tangentialDivergence, (hD x).fderiv]
      set K := approxTangentPlane n R.carrier x
      have hlin : K.starProjection.toLinearMap ∘ₗ
          (η (‖x - z‖ ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
            (2 * deriv η (‖x - z‖ ^ 2)) • (innerSL ℝ (x - z)).smulRight (x - z)).toLinearMap =
          η (‖x - z‖ ^ 2) • K.starProjection.toLinearMap +
            (2 * deriv η (‖x - z‖ ^ 2)) •
              (innerSL ℝ (x - z)).toLinearMap.smulRight (K.starProjection (x - z)) := by
        ext w
        simp [map_smul, smul_smul]
      have htrK : LinearMap.trace ℝ (Euclid P) K.starProjection.toLinearMap =
          (Module.finrank ℝ K : ℝ) := by
        rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp,
          LinearMap.trace_comp_comm']
        have hcomp : K.orthogonalProjectionOnto.toLinearMap.comp K.subtypeL.toLinearMap =
            LinearMap.id := by
          ext y
          simp
        rw [hcomp, LinearMap.trace_id]
      have hinner :
          inner ℝ (x - z) (K.starProjection (x - z)) = ‖K.starProjection (x - z)‖ ^ 2 := by
        rw [← K.inner_starProjection_left_eq_right (x - z) (x - z)]
        simpa using K.re_inner_starProjection_eq_normSq (x - z)
      rw [hlin, map_add, map_smul, map_smul, LinearMap.trace_smulRight, htrK]
      simp only [smul_eq_mul, ContinuousLinearMap.coe_coe, innerSL_apply_apply, hinner]
      ring
    have h0 := hstat _ hX hXc
    rw [hfv] at h0
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hrank] with x hx
    rw [htr x, hx]
    ring
  -- the smooth transition `τ` (`0` on `(-∞, 0]`, `1` on `[1, ∞)`) and a bound for `τ'`
  have hτc : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hτd : ∀ u, HasDerivAt Real.smoothTransition (deriv Real.smoothTransition u) u :=
    fun u => ((hτc.differentiable (by simp)) u).hasDerivAt
  have hτ0 : ∀ u : ℝ, u < 0 → deriv Real.smoothTransition u = 0 := by
    intro u hu
    have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hu] with w hw
      exact Real.smoothTransition.zero_of_nonpos hw.le
    rw [h.deriv_eq, deriv_const]
  have hτ1 : ∀ u : ℝ, 1 < u → deriv Real.smoothTransition u = 0 := by
    intro u hu
    have h : Real.smoothTransition =ᶠ[𝓝 u] fun _ => 1 := by
      filter_upwards [lt_mem_nhds hu] with w hw
      exact Real.smoothTransition.one_of_one_le hw.le
    rw [h.deriv_eq, deriv_const]
  obtain ⟨Cτ, hCτ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hτc.continuous_deriv le_rfl).continuousOn (s := Icc (0 : ℝ) 1))
  have hCτ0 : 0 ≤ Cτ := (norm_nonneg _).trans (hCτ 0 ⟨le_rfl, zero_le_one⟩)
  -- `m c ε` is `C¹`, equals `c` on `(-∞, c]` and the identity on `(c + ε, ∞)`; `dm c ε = (m c ε)'`
  obtain ⟨m, hm⟩ : ∃ m : ℝ → ℝ → ℝ → ℝ,
      ∀ c ε s, m c ε s = c + (s - c) * Real.smoothTransition ((s - c) / ε) :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨dm, hdm⟩ : ∃ dm : ℝ → ℝ → ℝ → ℝ, ∀ c ε s, dm c ε s = Real.smoothTransition ((s - c) / ε) +
      (s - c) / ε * deriv Real.smoothTransition ((s - c) / ε) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hm_deriv : ∀ c ε s, ε ≠ 0 → HasDerivAt (m c ε) (dm c ε s) s := by
    intro c ε s hε
    rw [show m c ε = fun t => c + (t - c) * Real.smoothTransition ((t - c) / ε) from
      funext (hm c ε), hdm]
    have h1 : HasDerivAt (fun t : ℝ => t - c) 1 s := (hasDerivAt_id s).sub_const c
    have h3 := (hτd ((s - c) / ε)).comp s (h1.div_const ε)
    refine ((h1.mul h3).const_add c).congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
  have hm_cd : ∀ c ε, ContDiff ℝ 1 (m c ε) := by
    intro c ε
    rw [show m c ε = fun t => c + (t - c) * Real.smoothTransition ((t - c) / ε) from
      funext (hm c ε)]
    exact contDiff_const.add ((contDiff_id.sub contDiff_const).mul
      (hτc.comp ((contDiff_id.sub contDiff_const).div_const ε)))
  have hm_lo : ∀ c ε s, 0 < ε → s ≤ c → m c ε s = c ∧ dm c ε s = 0 := by
    intro c ε s hε hs
    have hu : (s - c) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
    refine ⟨by rw [hm, Real.smoothTransition.zero_of_nonpos hu, mul_zero, add_zero], ?_⟩
    rw [hdm, Real.smoothTransition.zero_of_nonpos hu, zero_add]
    rcases hu.lt_or_eq with hu' | hu'
    · rw [hτ0 _ hu', mul_zero]
    · rw [hu', zero_mul]
  have hm_hi : ∀ c ε s, 0 < ε → c + ε < s → m c ε s = s ∧ dm c ε s = 1 := by
    intro c ε s hε hs
    have hu : 1 < (s - c) / ε := (one_lt_div hε).mpr (by linarith)
    refine ⟨by rw [hm, Real.smoothTransition.one_of_one_le hu.le, mul_one]; ring, ?_⟩
    rw [hdm, Real.smoothTransition.one_of_one_le hu.le, hτ1 _ hu, mul_zero, add_zero]
  have hm_ge : ∀ c ε s, 0 < ε → c ≤ m c ε s := by
    intro c ε s hε
    rw [hm]
    rcases le_or_gt s c with hs | hs
    · rw [Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le), mul_zero, add_zero]
    · have := Real.smoothTransition.nonneg ((s - c) / ε)
      nlinarith
  have hdm_le : ∀ c ε s, |dm c ε s| ≤ 1 + Cτ := by
    intro c ε s
    rw [hdm]
    rcases lt_or_ge ((s - c) / ε) 0 with hu | hu
    · rw [Real.smoothTransition.zero_of_nonpos hu.le, hτ0 _ hu, mul_zero, add_zero, abs_zero]
      linarith
    rcases le_or_gt ((s - c) / ε) 1 with hu1 | hu1
    · have h1 := hCτ _ ⟨hu, hu1⟩
      rw [Real.norm_eq_abs] at h1
      calc |Real.smoothTransition ((s - c) / ε) +
            (s - c) / ε * deriv Real.smoothTransition ((s - c) / ε)|
          ≤ |Real.smoothTransition ((s - c) / ε)| +
            |(s - c) / ε * deriv Real.smoothTransition ((s - c) / ε)| := abs_add_le _ _
        _ ≤ 1 + 1 * Cτ := by
          gcongr
          · rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
            exact Real.smoothTransition.le_one _
          · rw [abs_mul, abs_of_nonneg hu]
            exact mul_le_mul hu1 h1 (abs_nonneg _) zero_le_one
        _ = 1 + Cτ := by ring
    · rw [Real.smoothTransition.one_of_one_le hu1.le, hτ1 _ hu1, mul_zero, add_zero, abs_one]
      linarith
  -- the profile `F(u) = u^{-n/2}`, so that `F(|x - z|²) = |x - z|⁻ⁿ`, and its derivative
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, ∀ u, F u = u ^ (-(n : ℝ) / 2) := ⟨_, fun _ => rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : ℝ → ℝ, ∀ u, F' u = -(n : ℝ) / 2 * u ^ (-(n : ℝ) / 2 - 1) :=
    ⟨_, fun _ => rfl⟩
  have hF_deriv : ∀ u, 0 < u → HasDerivAt F (F' u) u := by
    intro u hu
    rw [show F = fun u => u ^ (-(n : ℝ) / 2) from funext hF, hF']
    exact Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  have hF_cd : ∀ u, 0 < u → ContDiffAt ℝ 1 F u := by
    intro u hu
    rw [show F = fun u => u ^ (-(n : ℝ) / 2) from funext hF]
    exact Real.contDiffAt_rpow_const_of_ne hu.ne'
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hρ2 : σ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hσ.le hσρ 2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hF_le : ∀ u, σ ^ 2 ≤ u → |F u| ≤ F (σ ^ 2) := by
    intro u hu
    rw [hF, hF, abs_of_pos (Real.rpow_pos_of_pos (hσ2.trans_le hu) _)]
    exact Real.rpow_le_rpow_of_nonpos hσ2 hu (by linarith)
  have hF'_le : ∀ u, σ ^ 2 ≤ u → |F' u| ≤ (n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) := by
    intro u hu
    rw [hF', abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hσ2.trans_le hu) _),
      abs_of_nonpos (by linarith : -(n : ℝ) / 2 ≤ 0), show -(-(n : ℝ) / 2) = (n : ℝ) / 2 by ring]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hσ2 hu (by linarith))
      (by positivity)
  have hFsq : ∀ t : ℝ, 0 < t → F (t ^ 2) = (t ^ n)⁻¹ := by
    intro t ht
    rw [hF, show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul ht.le,
      show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring, Real.rpow_neg ht.le, Real.rpow_natCast]
  have hF'sq : ∀ t : ℝ, 0 < t → F' (t ^ 2) = -(n : ℝ) / 2 * (t ^ (n + 2))⁻¹ := by
    intro t ht
    rw [hF', show t ^ 2 = t ^ (2 : ℝ) by norm_cast, ← Real.rpow_mul ht.le,
      show (2 : ℝ) * (-(n : ℝ) / 2 - 1) = -((n + 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_neg ht.le, Real.rpow_natCast]
  -- the test profiles `η ε ≈ max(·, σ²)^{-n/2} - max(·, ρ²)^{-n/2}` and their derivatives
  obtain ⟨η, hη⟩ : ∃ η : ℝ → ℝ → ℝ, ∀ ε s, η ε s = F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨dη, hdη⟩ : ∃ dη : ℝ → ℝ → ℝ, ∀ ε s, dη ε s =
      F' (m (σ ^ 2) ε s) * dm (σ ^ 2) ε s - F' (m (ρ ^ 2) ε s) * dm (ρ ^ 2) ε s :=
    ⟨_, fun _ _ => rfl⟩
  have hmpos : ∀ c ε s, 0 < ε → σ ^ 2 ≤ c → 0 < m c ε s :=
    fun c ε s hε hc => hσ2.trans_le (hc.trans (hm_ge c ε s hε))
  have hη_deriv : ∀ ε s, 0 < ε → HasDerivAt (η ε) (dη ε s) s := by
    intro ε s hε
    rw [show η ε = fun s => F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) from funext (hη ε), hdη]
    exact ((hF_deriv _ (hmpos _ ε s hε le_rfl)).comp s (hm_deriv _ ε s hε.ne')).sub
      ((hF_deriv _ (hmpos _ ε s hε hρ2)).comp s (hm_deriv _ ε s hε.ne'))
  have hη_cd : ∀ ε, 0 < ε → ContDiff ℝ 1 (η ε) := by
    intro ε hε
    rw [show η ε = fun s => F (m (σ ^ 2) ε s) - F (m (ρ ^ 2) ε s) from funext (hη ε)]
    refine contDiff_iff_contDiffAt.2 fun s => ?_
    exact ((hF_cd _ (hmpos _ ε s hε le_rfl)).comp s (hm_cd _ ε).contDiffAt).sub
      ((hF_cd _ (hmpos _ ε s hε hρ2)).comp s (hm_cd _ ε).contDiffAt)
  have hη_cut : ∀ ε s, 0 < ε → ε ≤ 1 → (ρ + 1) ^ 2 ≤ s → η ε s = 0 ∧ dη ε s = 0 := by
    intro ε s hε hε1 hs
    have hs' : ρ ^ 2 + ε < s := by nlinarith
    obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) ε s hε (by linarith)
    obtain ⟨h3, h4⟩ := hm_hi (ρ ^ 2) ε s hε hs'
    rw [hη, hdη, h1, h2, h3, h4]
    constructor <;> ring
  -- the widths `εₖ = 1/(k + 1)` and the divergences `Gₖ` of the corresponding radial fields
  have hεpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hεle : ∀ k : ℕ, 1 / ((k : ℝ) + 1) ≤ 1 := fun k => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Euclid P → ℝ, ∀ k x, G k x =
      (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) + 2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
        ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  have hG0 : ∀ k, ∫ x, G k x ∂R.measure = 0 := by
    intro k
    have h := hrad (η (1 / ((k : ℝ) + 1))) (hη_cd _ (hεpos k)) (ρ + 1)
      (fun s hs => (hη_cut _ s (hεpos k) (hεle k) hs).1)
    have hder : ∀ s, deriv (η (1 / ((k : ℝ) + 1))) s = dη (1 / ((k : ℝ) + 1)) s :=
      fun s => (hη_deriv _ s (hεpos k)).deriv
    simp only [hder] at h
    simpa only [hG] using h
  -- the defect `Ψ = |D^⊥r|²/rⁿ` and the pointwise limit `L` of the `Gₖ`
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid P → ℝ, ∀ x, Ψ x =
      ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Euclid P → ℝ, ∀ x, L x =
      (n : ℝ) * ((closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x +
          (closedBall z ρ \ closedBall z σ).indicator Ψ x) :=
    ⟨_, fun _ => rfl⟩
  have hεmono : ∀ k k0 : ℕ, k0 ≤ k → 1 / ((k : ℝ) + 1) ≤ 1 / ((k0 : ℝ) + 1) := fun k k0 hk =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
  have hlim : ∀ x, Tendsto (fun k : ℕ => G k x) atTop (𝓝 (L x)) := by
    intro x
    by_cases hxσ : x ∈ closedBall z σ
    · -- inside `B_σ(z)` every `Gₖ(x)` is `n(σ⁻ⁿ - ρ⁻ⁿ)`
      have hs : ‖x - z‖ ^ 2 ≤ σ ^ 2 := by
        rw [mem_closedBall, dist_eq_norm] at hxσ
        exact pow_le_pow_left₀ (norm_nonneg _) hxσ 2
      refine tendsto_atTop_of_eventually_const (i₀ := 0) fun k _ => ?_
      obtain ⟨h1, h2⟩ := hm_lo (σ ^ 2) _ _ (hεpos k) hs
      obtain ⟨h3, h4⟩ := hm_lo (ρ ^ 2) _ _ (hεpos k) (hs.trans hρ2)
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_mem hxσ,
        indicator_of_mem (closedBall_subset_closedBall hσρ hxσ),
        indicator_of_notMem (fun h => h.2 hxσ), hFsq σ hσ, hFsq ρ hρ]
      ring
    have hxσ' : σ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hxσ
    have hr : 0 < ‖x - z‖ := hσ.trans hxσ'
    have hs1 : σ ^ 2 < ‖x - z‖ ^ 2 := pow_lt_pow_left₀ hxσ' hσ.le two_ne_zero
    by_cases hxρ : x ∈ closedBall z ρ
    · -- on the annulus, eventually `Gₖ(x) = n(|x - z|⁻ⁿ - ρ⁻ⁿ) - n|p_x(x - z)|²/|x - z|ⁿ⁺²`
      have hs2 : ‖x - z‖ ^ 2 ≤ ρ ^ 2 := by
        rw [mem_closedBall, dist_eq_norm] at hxρ
        exact pow_le_pow_left₀ (norm_nonneg _) hxρ 2
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (sub_pos.mpr hs1)
      refine tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_
      have hεk := hεmono k k0 hk
      obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      obtain ⟨h3, h4⟩ := hm_lo (ρ ^ 2) _ _ (hεpos k) hs2
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_notMem hxσ, indicator_of_mem hxρ,
        indicator_of_mem (show x ∈ closedBall z ρ \ closedBall z σ from ⟨hxρ, hxσ⟩), hΨ, hpyth,
        hFsq _ hr, hFsq ρ hρ, hF'sq _ hr]
      field_simp
      ring
    · -- outside `B_ρ(z)`, eventually `Gₖ(x) = 0`
      have hxρ' : ρ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hxρ
      have hs2 : ρ ^ 2 < ‖x - z‖ ^ 2 := pow_lt_pow_left₀ hxρ' hρ.le two_ne_zero
      obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt (sub_pos.mpr hs2)
      refine tendsto_atTop_of_eventually_const (i₀ := k0) fun k hk => ?_
      have hεk := hεmono k k0 hk
      obtain ⟨h1, h2⟩ := hm_hi (σ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      obtain ⟨h3, h4⟩ := hm_hi (ρ ^ 2) _ (‖x - z‖ ^ 2) (hεpos k) (by linarith)
      rw [hG, hL, hη, hdη, h1, h2, h3, h4, indicator_of_notMem hxσ, indicator_of_notMem hxρ,
        indicator_of_notMem (fun h => hxρ h.1)]
      ring
  -- uniform domination of the `Gₖ` on `B_{ρ+1}(z)`
  have hGbound : ∀ k x, ‖G k x‖ ≤ (closedBall z (ρ + 1)).indicator (fun _ =>
      (n : ℝ) * (2 * F (σ ^ 2)) +
        2 * (2 * ((n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) * (1 + Cτ))) * (ρ + 1) ^ 2) x := by
    intro k x
    have hε := hεpos k
    by_cases hx : x ∈ closedBall z (ρ + 1)
    · rw [indicator_of_mem hx, hG, Real.norm_eq_abs]
      have hxr : ‖x - z‖ ≤ ρ + 1 := by rwa [mem_closedBall, dist_eq_norm] at hx
      have hηb : |η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| ≤ 2 * F (σ ^ 2) := by
        rw [hη]
        refine (abs_sub _ _).trans ?_
        linarith [hF_le _ (hm_ge (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε),
          hF_le _ (hρ2.trans (hm_ge (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε))]
      have hdηb : |dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| ≤
          2 * ((n : ℝ) / 2 * (σ ^ 2) ^ (-(n : ℝ) / 2 - 1) * (1 + Cτ)) := by
        rw [hdη]
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 := hF'_le _ (hm_ge (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε)
        have h2 := hF'_le _ (hρ2.trans (hm_ge (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) hε))
        have h3 := hdm_le (σ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)
        have h4 := hdm_le (ρ ^ 2) (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)
        have h5 := mul_le_mul h1 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
        have h6 := mul_le_mul h2 h4 (abs_nonneg _) (le_trans (abs_nonneg _) h2)
        linarith
      have hpvb : ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 ≤ (ρ + 1) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _)
          (((approxTangentPlane n R.carrier x).norm_starProjection_apply_le (x - z)).trans hxr) 2
      calc |(n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) +
            2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2|
          ≤ (n : ℝ) * |η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| +
            2 * |dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2)| *
              ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 := by
            refine (abs_add_le _ _).trans (le_of_eq ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hn0, abs_two,
              abs_of_nonneg (by positivity :
                (0 : ℝ) ≤ ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2)]
        _ ≤ _ := by gcongr
    · rw [indicator_of_notMem hx, hG, norm_le_zero_iff]
      have hxr : ρ + 1 < ‖x - z‖ := by
        simpa only [mem_closedBall, dist_eq_norm, not_le] using hx
      obtain ⟨h1, h2⟩ := hη_cut _ _ hε (hεle k)
        (pow_le_pow_left₀ (by linarith) hxr.le 2)
      rw [h1, h2]
      ring
  -- measurability of the `Gₖ` and of `Ψ`
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) R.measure := by
    intro k
    have hε := hεpos k
    have hdη_cont : Continuous (dη (1 / ((k : ℝ) + 1))) := by
      rw [show dη (1 / ((k : ℝ) + 1)) = deriv (η (1 / ((k : ℝ) + 1))) from
        funext fun s => ((hη_deriv _ s hε).deriv).symm]
      exact (hη_cd _ hε).continuous_deriv le_rfl
    have hc1 : Continuous fun x : Euclid P => (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) :=
      continuous_const.mul ((hη_cd _ hε).continuous.comp (by fun_prop))
    have hc2 : Continuous fun x : Euclid P => 2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) :=
      continuous_const.mul (hdη_cont.comp (by fun_prop))
    rw [show G k = fun x => (n : ℝ) * η (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) +
        2 * dη (1 / ((k : ℝ) + 1)) (‖x - z‖ ^ 2) *
          ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 from funext (hG k)]
    exact (hc1.aemeasurable.add (hc2.aemeasurable.mul hpv)).aestronglyMeasurable
  have hΨmeas : AEMeasurable Ψ R.measure := by
    rw [show Ψ = fun x =>
        ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
          ‖x - z‖ ^ (n + 2) from funext hΨ]
    have h1 : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection (x - z))
        R.measure :=
      ContinuousLinearMap.measurable_apply₂.comp_aemeasurable
        (hp.prodMk (measurable_id.sub_const z).aemeasurable)
    exact (((measurable_id.sub_const z).aemeasurable.sub h1).norm.pow_const 2).div
      ((measurable_id.sub_const z).norm.pow_const _).aemeasurable
  have hΨnn : ∀ x, 0 ≤ Ψ x := fun x => by
    rw [hΨ]
    positivity
  -- `Ψ ≤ σ⁻ⁿ` on the annulus, so `Ψ` is integrable there
  have hann : MeasurableSet (closedBall z ρ \ closedBall z σ) :=
    measurableSet_closedBall.diff measurableSet_closedBall
  have hΨint : IntegrableOn Ψ (closedBall z ρ \ closedBall z σ) R.measure := by
    refine Measure.integrableOn_of_bounded (M := (σ ^ n)⁻¹)
      ((measure_mono sdiff_subset).trans_lt (isCompact_closedBall z ρ).measure_lt_top).ne
      hΨmeas.aestronglyMeasurable (ae_restrict_of_forall_mem hann fun x hx => ?_)
    have hxσ' : σ < ‖x - z‖ := by simpa only [mem_closedBall, dist_eq_norm, not_le] using hx.2
    have hr : 0 < ‖x - z‖ := hσ.trans hxσ'
    rw [Real.norm_eq_abs, abs_of_nonneg (hΨnn x), hΨ, hpyth, div_le_iff₀ (by positivity),
      pow_add, ← mul_assoc, inv_mul_eq_div]
    have h1 : 1 ≤ ‖x - z‖ ^ n / σ ^ n := by
      rw [one_le_div (by positivity)]
      exact pow_le_pow_left₀ hσ.le hxσ'.le n
    nlinarith [sq_nonneg ‖(approxTangentPlane n R.carrier x).starProjection (x - z)‖,
      sq_nonneg ‖x - z‖]
  -- dominated convergence: `∫ L dμ = lim ∫ Gₖ dμ = 0`
  have hL0 : ∫ x, L x ∂R.measure = 0 := by
    have hconv := tendsto_integral_of_dominated_convergence _ hGmeas
      ((integrableOn_const (isCompact_closedBall z (ρ + 1)).measure_lt_top.ne).integrable_indicator
        measurableSet_closedBall)
      (fun k => Eventually.of_forall (hGbound k)) (Eventually.of_forall hlim)
    simp only [hG0] at hconv
    exact tendsto_nhds_unique hconv tendsto_const_nhds
  -- `∫ L dμ = n (σ⁻ⁿ μ(B_σ) - ρ⁻ⁿ μ(B_ρ) + ∫_{B_ρ \ B_σ} Ψ dμ)`
  have hint_σ : Integrable ((closedBall z σ).indicator fun _ : Euclid P => (σ ^ n)⁻¹) R.measure :=
    (integrableOn_const (isCompact_closedBall z σ).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hint_ρ : Integrable ((closedBall z ρ).indicator fun _ : Euclid P => (ρ ^ n)⁻¹) R.measure :=
    (integrableOn_const (isCompact_closedBall z ρ).measure_lt_top.ne).integrable_indicator
      measurableSet_closedBall
  have hLexp : ∫ x, L x ∂R.measure = (n : ℝ) * (R.measure.real (closedBall z σ) * (σ ^ n)⁻¹ -
      R.measure.real (closedBall z ρ) * (ρ ^ n)⁻¹ +
        ∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure) := by
    have hdiff : Integrable (fun x => (closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x) R.measure := hint_σ.sub hint_ρ
    rw [show L = fun x => (n : ℝ) * ((closedBall z σ).indicator (fun _ => (σ ^ n)⁻¹) x -
        (closedBall z ρ).indicator (fun _ => (ρ ^ n)⁻¹) x +
          (closedBall z ρ \ closedBall z σ).indicator Ψ x) from funext hL,
      integral_const_mul, integral_add hdiff (hΨint.integrable_indicator hann),
      integral_sub hint_σ hint_ρ, integral_indicator_const _ measurableSet_closedBall,
      integral_indicator_const _ measurableSet_closedBall, integral_indicator hann, smul_eq_mul,
      smul_eq_mul]
  -- the real form of Simon 4.3.6
  have hreal : R.measure.real (closedBall z σ) * (σ ^ n)⁻¹ -
      R.measure.real (closedBall z ρ) * (ρ ^ n)⁻¹ +
        ∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure = 0 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- `n = 0`: a.e. `TₓM = 0`, so `Ψ = 1` on the annulus
      have hΨ1 : ∀ᵐ x ∂(R.measure.restrict (closedBall z ρ \ closedBall z σ)), Ψ x = 1 := by
        rw [ae_restrict_iff' hann]
        filter_upwards [hrank] with x hx hxA
        have hxσ' : σ < ‖x - z‖ := by
          simpa only [mem_closedBall, dist_eq_norm, not_le] using hxA.2
        have hbot : approxTangentPlane n R.carrier x = ⊥ :=
          Submodule.finrank_eq_zero.mp (hx.trans hn)
        rw [hΨ, hbot, Submodule.starProjection_bot, zero_apply, sub_zero, hn, zero_add,
          div_self (pow_pos (hσ.trans hxσ') 2).ne']
      have h1 : (σ ^ n)⁻¹ = 1 := by rw [hn, pow_zero, inv_one]
      have h2 : (ρ ^ n)⁻¹ = 1 := by rw [hn, pow_zero, inv_one]
      rw [integral_congr_ae hΨ1, setIntegral_const, smul_eq_mul, mul_one,
        measureReal_sdiff (closedBall_subset_closedBall hσρ) measurableSet_closedBall
          (isCompact_closedBall z ρ).measure_lt_top.ne, h1, h2]
      ring
    · have h := hLexp ▸ hL0
      exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn.ne')
  -- back to `[0, ∞]`
  have hlint : ∫⁻ x in closedBall z ρ \ closedBall z σ, ENNReal.ofReal
      (‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2)) ∂R.measure =
      ENNReal.ofReal (∫ x in closedBall z ρ \ closedBall z σ, Ψ x ∂R.measure) := by
    rw [ofReal_integral_eq_lintegral_ofReal hΨint (Eventually.of_forall hΨnn)]
    simp only [hΨ]
  have hball : ∀ t : ℝ, 0 < t → R.measure (closedBall z t) / ENNReal.ofReal (t ^ n) =
      ENNReal.ofReal (R.measure.real (closedBall z t) * (t ^ n)⁻¹) := by
    intro t ht
    rw [← div_eq_mul_inv, ENNReal.ofReal_div_of_pos (pow_pos ht n), measureReal_def,
      ENNReal.ofReal_toReal (isCompact_closedBall z t).measure_lt_top.ne]
  rw [hlint, hball σ hσ, hball ρ hρ, ← ENNReal.ofReal_add
    (mul_nonneg measureReal_nonneg (inv_nonneg.mpr (pow_nonneg hσ.le n)))
    (integral_nonneg hΨnn)]
  congr 1
  linarith
/-- **Closed-ball masses at points of the spine** (step 1 of the parent proof: the scaling
`(ωₙρⁿ)⁻¹μ_C(B_ρ(0)) = Θⁿ(T, x)` for each `ρ > 0` in Simon's proof of 7.3.1, moved to centres `z`
in the subspace `L` of Lemma 7.3.5).  Let `μ` be invariant under translations by vectors of `L`
and satisfy `μ(λA) = λⁿμ(A)` for `λ > 0`, both on Borel sets.  Then `μ(B̄_ρ(z)) = ρⁿμ(B̄_1(z))`
for `z ∈ L` and `ρ > 0`.  Translation by `-z ∈ L` maps `B̄_r(z)` onto `B̄_r(0)`, and
`B̄_ρ(0) = ρB̄_1(0)`. -/
theorem Submission.dimred_cs_st_closedBall_measure_scaling : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (L : Submodule ℝ (Euclid P)), (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => y + x) ⁻¹' A) = μ A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → μ ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * μ A) → ∀ z ∈ L, ∀ ρ : ℝ, 0 < ρ → μ (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * μ (closedBall z 1) := by
  intro P n μ L htrans hhom z hz ρ hρ
  -- translation by `-z ∈ L`: `B̄_r(z) = (x ↦ -z + x)⁻¹' B̄_r(0)`
  have htr : ∀ r : ℝ, μ (closedBall z r) = μ (closedBall 0 r) := by
    intro r
    rw [← htrans (-z) (L.neg_mem hz) (closedBall 0 r) measurableSet_closedBall]
    congr 1
    ext x
    simp only [mem_closedBall, mem_preimage, dist_eq_norm, sub_zero, neg_add_eq_sub]
  -- dilation by `ρ`: `B̄_ρ(0) = (x ↦ ρ • x) '' B̄_1(0)`
  have hsc : (fun x => ρ • x) '' closedBall (0 : Euclid P) 1 = closedBall 0 ρ := by
    rw [Set.image_smul, smul_unitClosedBall_of_nonneg hρ.le]
  rw [htr ρ, htr 1, ← hsc, hhom ρ hρ _ measurableSet_closedBall]

/-- **Simon, proof of 7.3.1 (chapter-07.txt lines 352–360), at a centre `z`.**  Let
`R = (M, θ, ξ)` be an integer multiplicity triple in `ℝᴾ` with `V = v(M, θ)` stationary:
`δV(X) = 0` for every `X ∈ C¹_c(ℝᴾ; ℝᴾ)`.  If `μ_V(B_ρ(z)) = ρⁿμ_V(B_1(z))` for every `ρ > 0`
(closed balls, `μ_V = θHⁿ⌞M`), then `x − z ∈ TₓM`, i.e. `p_x(x − z) = x − z`, for `μ_V`-a.e. `x`.
The ratio `ρ⁻ⁿμ_V(B_ρ(z)) = μ_V(B_1(z))` is constant and finite (`θ` is locally integrable), so
the monotonicity identity 4.3.6 (`dtc_cone_monotonicity_identity`) gives
`∫_{B_ρ(z) \ B_σ(z)} |(x − z) − p_x(x − z)|² / |x − z|ⁿ⁺² dμ_V = 0` for `0 < σ ≤ ρ`.  The
integrand is `μ_V`-a.e.-measurable (`imrep_univ_tangent_starProjection_aemeasurable`), so it
vanishes a.e. on each annulus, where `|x − z| > σ > 0`; the annuli
`B_{k+1}(z) \ B_{1/(k+1)}(z)` exhaust `ℝᴾ \ {z}`, and `p_z(0) = 0`. -/
theorem Submission.dimred_cs_st_tangent_sub_of_ball_ratio : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (z : Euclid P), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ ρ : ℝ, 0 < ρ → R.measure (closedBall z ρ) = ENNReal.ofReal (ρ ^ n) * R.measure (closedBall z 1)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection (x - z) = x - z := by
  intro P n R z hstat hball
  -- Step 1: `a := μ(B̄_1(z)) < ∞`
  have ha : R.measure (closedBall z 1) ≠ ∞ := by
    have h := R.locallyIntegrable_mult (closedBall z 1) (isCompact_closedBall z 1) (subset_univ _)
    rwa [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
  -- Step 2: the normalized ratio is constantly `a`
  have hratio : ∀ ρ : ℝ, 0 < ρ →
      R.measure (closedBall z ρ) / ENNReal.ofReal (ρ ^ n) = R.measure (closedBall z 1) := by
    intro ρ hρ
    rw [hball ρ hρ, mul_comm, ENNReal.mul_div_cancel_right
      (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne' ENNReal.ofReal_ne_top]
  -- Step 3: measurability of the defect integrand
  have hp : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection (x - z))
      R.measure :=
    (continuous_fst.clm_apply continuous_snd).aemeasurable2
      (Submission.imrep_univ_tangent_starProjection_aemeasurable P n R)
      (aemeasurable_id.sub_const z)
  have hf : AEMeasurable (fun x => ENNReal.ofReal
      (‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2))) R.measure :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((aemeasurable_id.sub_const z).sub hp).norm.pow_const 2).div
        ((measurable_id.sub_const z).norm.pow_const (n + 2)).aemeasurable)
  -- Step 4: the defect over each annulus vanishes
  have hann : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ∀ᵐ x ∂R.measure,
      x ∈ closedBall z ρ \ closedBall z σ →
      (approxTangentPlane n R.carrier x).starProjection (x - z) = x - z := by
    intro σ ρ hσ hσρ
    have h := Submission.dtc_cone_monotonicity_identity P n R hstat z σ ρ hσ hσρ
    rw [hratio σ hσ, hratio ρ (hσ.trans_le hσρ)] at h
    have hD := (lintegral_eq_zero_iff' (hf.mono_measure Measure.restrict_le_self)).1
      ((ENNReal.add_right_inj ha).1 (h.trans (add_zero _).symm))
    have hA : MeasurableSet (closedBall z ρ \ closedBall z σ) :=
      measurableSet_closedBall.diff measurableSet_closedBall
    filter_upwards [(ae_restrict_iff' hA).1 hD] with x hx hxA
    have hxσ : σ < ‖x - z‖ := by
      have h2 := hxA.2
      rw [mem_closedBall, dist_eq_norm, not_le] at h2
      exact h2
    have h0 : ‖(x - z) - (approxTangentPlane n R.carrier x).starProjection (x - z)‖ ^ 2 /
        ‖x - z‖ ^ (n + 2) ≤ 0 :=
      ENNReal.ofReal_eq_zero.1 (hx hxA)
    rw [div_le_iff₀ (pow_pos (hσ.trans hxσ) _), zero_mul] at h0
    have hnorm := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h0 (sq_nonneg _))
    exact (sub_eq_zero.1 (norm_eq_zero.1 hnorm)).symm
  -- Step 5: the annuli `B̄_{k+1}(z) \ B̄_{1/(k+1)}(z)` exhaust `ℝᴾ \ {z}`
  have hk1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => le_add_of_nonneg_left k.cast_nonneg
  have hall := ae_all_iff.2 fun k : ℕ => hann (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) (by positivity)
    (((div_le_one (by positivity)).2 (hk1 k)).trans (hk1 k))
  filter_upwards [hall] with x hx
  rcases eq_or_ne x z with rfl | hxz
  · simp
  have hxpos : 0 < ‖x - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hxz)
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x - z‖ ‖x - z‖⁻¹)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine hx k (Set.mem_sdiff_of_mem ?_ ?_)
  · rw [mem_closedBall, dist_eq_norm]
    linarith [le_max_left ‖x - z‖ ‖x - z‖⁻¹]
  · rw [mem_closedBall, dist_eq_norm, not_le, one_div_lt hk0 hxpos, one_div]
    linarith [le_max_right ‖x - z‖ ‖x - z‖⁻¹]

/-- **Spine tangency** (a step of Simon 7.3.5, whose proof is left to the reader, chapter-07.txt
lines 407–418; argued as in the proof of 7.3.1, lines 355–360).  Let `R = (M, θ, ξ)` be an integer
multiplicity triple in `ℝᴾ` with `V = v(M, θ)` stationary and `L ⊆ ℝᴾ` a subspace such that
`μ_V = θHⁿ⌞M` is invariant under translation by every `y ∈ L` and `μ_V(λA) = λⁿμ_V(A)` for
`λ > 0`.  Then `x ∈ TₓM` and `L ⊆ TₓM` for `μ_V`-a.e. `x`.  For `z ∈ L`,
`μ_V(B̄_ρ(z)) = ρⁿμ_V(B̄_1(z))` (`dimred_cs_st_closedBall_measure_scaling`), so the monotonicity
identity (Ch. 4, 3.6) forces `x − z ∈ TₓM` for `μ_V`-a.e. `x`
(`dimred_cs_st_tangent_sub_of_ball_ratio`).  Apply this to `z = 0` and to every `z` in a finite
set `S` spanning `L` (in place of a countable dense subset of `L`): for `μ_V`-a.e. `x`, `x ∈ TₓM`
and `z = x − (x − z) ∈ TₓM` for `z ∈ S`, so the subspace `TₓM` contains `span S = L`. -/
theorem Submission.dimred_cs_spine_tangent_of_invariant_measure : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)), 0 < n → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ y ∈ L, ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => y + x) ⁻¹' A) = R.measure A) → (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x ∧ ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v := by
  intro P n R L _hn hstat htrans hhom
  -- for each `z ∈ L` the ball ratios at `z` are constant, so `x - z ∈ TₓM` for `μ_V`-a.e. `x`
  have htan : ∀ z ∈ L, ∀ᵐ x ∂R.measure,
      (approxTangentPlane n R.carrier x).starProjection (x - z) = x - z := fun z hz =>
    Submission.dimred_cs_st_tangent_sub_of_ball_ratio P n R z hstat
      (Submission.dimred_cs_st_closedBall_measure_scaling P n R.measure L htrans hhom z hz)
  -- a finite set `S ⊆ L` spanning `L`
  obtain ⟨S, hS⟩ : L.FG := IsNoetherian.noetherian L
  have hSL : ∀ z ∈ S, z ∈ L := fun z hz => hS ▸ Submodule.subset_span (Finset.mem_coe.2 hz)
  filter_upwards [htan 0 L.zero_mem, (eventually_all_finset S).2 fun z hz => htan z (hSL z hz)]
    with x hx0 hxS
  rw [sub_zero] at hx0
  have hxT : x ∈ approxTangentPlane n R.carrier x := Submodule.starProjection_eq_self_iff.1 hx0
  -- `z = x - (x - z) ∈ TₓM` for `z ∈ S`, so `L = span S ≤ TₓM`
  have hLT : L ≤ approxTangentPlane n R.carrier x := by
    rw [← hS, Submodule.span_le]
    intro z hz
    have h := (approxTangentPlane n R.carrier x).sub_mem hxT
      (Submodule.starProjection_eq_self_iff.1 (hxS z (Finset.mem_coe.1 hz)))
    rwa [sub_sub_cancel] at h
  exact ⟨hx0, fun v hv => Submodule.starProjection_eq_self_iff.2 (hLT hv)⟩
/-- `x ∧ ξ(x) = 0` a.e. when `x` lies in its approximate tangent plane a.e. (Simon 7.3.1, proof):
`ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM`, and `y ↦ β(y, τ₁, …, τₙ)` is linear
and vanishes on each `τᵢ` (repeated entry), hence on `TₓM ∋ x`. -/
theorem Submission.dtc_cone_wedge_vanishes : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x) → ∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β x) = 0 := by
  intro P n U R hproj
  -- `μ = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so `ξ` orients an approximate tangent plane `μ`-a.e.
  filter_upwards [hproj, (withDensity_absolutelyContinuous _ _).ae_le R.orients]
    with x hx hor β
  obtain ⟨Q, hQ, τ, -, hspan, hξ⟩ := hor
  -- `TₓM = Q` by uniqueness of approximate tangent planes, so `x ∈ Q`
  have hT : approxTangentPlane n R.carrier x = Q := by
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.unique hQ
  have hxQ : x ∈ Q := hT ▸ Submodule.starProjection_eq_self_iff.mp hx
  -- `y ↦ β(y, τ)` vanishes on `Q = span(range τ)`
  have hβ : ∀ y ∈ Q, ContinuousAlternatingMap.curryLeft β y τ = 0 := by
    intro y hy
    rw [← hspan] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      exact β.map_eq_zero_of_eq _ (i := 0) (j := b.succ) (by simp) (Fin.succ_ne_zero b).symm
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add, ContinuousAlternatingMap.add_apply, hy, hz, add_zero]
    | smul a y _ hy =>
      rw [map_smul, ContinuousAlternatingMap.smul_apply, hy, smul_zero]
  rcases hξ with hξ | hξ
  · rw [hξ, hβ x hxQ]
  · rw [hξ, hβ x hxQ, neg_zero]
/-- **Cartan's formula for the Euler field** `X(z) = z` (Simon Ch. 6, 2.25–2.26 and 2.33, as used
in the proof of 7.3.1).  For an `(m+1)`-form `β` differentiable at `y`,
`d(ι_X β)(y) + ι_y dβ(y) = (m + 1) β(y) + Dβ(y)[y]`, i.e. `L_X β = d ι_X β + ι_X dβ`.  With
`B = Dβ(y)`, the product rule gives `D(ι_X β)(y) u = (B u).curryLeft y + β(y).curryLeft u`; the
second term alternates to `(m + 1) β(y)` (`alternatizeUncurryFin_curryLeft`), and the first one
cancels against every term of `dβ(y)(y, v₀, …, vₘ)` except the `k = 0` term `B y (v₀, …, vₘ)`. -/
theorem Submission.dtc_cone_euler_cartan : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)) (y : Euclid P), DifferentiableAt ℝ β y → exteriorDerivative (fun z => ContinuousAlternatingMap.curryLeft (β z) z) y + ContinuousAlternatingMap.curryLeft (exteriorDerivative β y) y = ((m : ℝ) + 1) • β y + fderiv ℝ β y y := by
  intro P m β y hβ
  -- product rule for `z ↦ Φ (β z) z`, where `Φ f x = f.curryLeft x` is continuous bilinear
  have hψ := (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
    (n := m)).toContinuousLinearMap.hasFDerivAt_of_bilinear hβ.hasFDerivAt (hasFDerivAt_id y)
  have h1 : exteriorDerivative (fun z => ContinuousAlternatingMap.curryLeft (β z) z) y =
      ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun z =>
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
          (n := m)).toContinuousLinearMap (β z) (id z)) y) := rfl
  have h2 : (ContinuousLinearMap.precompR (Euclid P)
      (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
        (n := m)).toContinuousLinearMap) (β y) (ContinuousLinearMap.id ℝ (Euclid P)) =
      ContinuousAlternatingMap.curryLeft (β y) := by
    ext u v
    rfl
  -- `d(ι_X β)(y) = alt(u ↦ (B u).curryLeft y) + (m + 1) β(y)`
  rw [h1, hψ.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_add, h2,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft, add_assoc]
  congr 1
  · rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one]
  · -- removing entry `i + 1` of `(y, v)` leaves `(y, v without vᵢ)`
    have hrm : ∀ (i : Fin (m + 1)) (v : Fin (m + 1) → Euclid P),
        Fin.removeNth i.succ (Matrix.vecCons y v) = Matrix.vecCons y (Fin.removeNth i v) := by
      intro i v
      funext j
      cases j using Fin.cases with
      | zero => simp [Fin.removeNth_apply]
      | succ j => simp [Fin.removeNth_apply]
    ext v
    simp only [ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.alternatizeUncurryFin_apply, exteriorDerivative, extDeriv,
      ContinuousLinearMap.precompL_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap, ContinuousAlternatingMap.curryLeftLI_apply, id_eq]
    -- split off the `k = 0` term `B y v` of `dβ(y)(y, v)`; the other terms cancel the first sum
    rw [Fin.sum_univ_succ (n := m + 1)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.removeNth_zero, Fin.tail_vecCons,
      hrm, Fin.val_zero, Fin.val_succ, pow_zero, one_smul, pow_succ, mul_neg_one, neg_smul,
      Finset.sum_neg_distrib]
    abel
/-- **Cone criterion** (Simon 7.3.1(2), via 6.2.23).  If `C ∈ 𝒟ₙ(ℝᴾ)` satisfies `C(ω') = C(ω)`
whenever `λ > 0` and the test forms `ω, ω'` satisfy `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)`, then `C` is a cone.
As `η_{0,λ}(ℝᴾ) = ℝᴾ`, `η_{0,λ#}C(ω) = C(η_{0,λ}^# ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.dtc_cwv_isConeCurrent_of_pullback_invariant : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ lam : ℝ, 0 < lam → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) → C ω' = C ω) → IsConeCurrent C := by
  intro P n C hC lam hlam ω
  -- Step 1: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h]
  -- Steps 2–3: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω'')` for the affine pullback `ω''` of `ω`,
  -- and `C(ω'') = C(ω)` by the hypothesis.
  refine hC lam hlam ω _ fun y => ?_
  -- Step 4: `ω''(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
/-- **Contraction with the Euler field preserves test forms** (Simon Ch. 6, 2.25–2.26 and 2.33,
as used in the proof of 7.3.1).  If `β` is a test `(m+1)`-form, then so is
`ι_X β : z ↦ β(z).curryLeft z` for `X(z) = z`: it is the smooth family of continuous linear maps
`z ↦ curryLeftLI (β z)` applied to the smooth vector `z`, and it vanishes wherever `β` does, so
its support lies in the compact `tsupport β`. -/
theorem Submission.dtc_cwv_euler_contraction_isTestForm : ∀ (P m : ℕ) (β : DifferentialForm (Euclid P) (m + 1)), IsTestForm β → IsTestForm (fun z => ContinuousAlternatingMap.curryLeft (β z) z) := by
  intro P m β hβ
  obtain ⟨hs, hc⟩ := hβ
  refine ⟨?_, ?_⟩
  · -- `z ↦ (curryLeftLI (β z)) z` is a smooth family of continuous linear maps applied to `z`
    change ContDiff ℝ (⊤ : ℕ∞) (fun z => (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ)
      (E := Euclid P) (F := ℝ) (n := m)).toContinuousLinearMap (β z) z)
    exact (((ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid P) (F := ℝ)
      (n := m)).toContinuousLinearMap.contDiff).comp hs).clm_apply contDiff_id
  · -- `β z = 0` forces `β(z).curryLeft z = 0`, so the support stays inside `supp β`
    refine hc.mono ?_
    intro z hz
    simp only [mem_support] at hz ⊢
    intro h0
    apply hz
    rw [h0]
    rfl

/-- Differentiation under the integral sign for the dilations `y ↦ s y` (steps 0(a), 0(b), 2 and 3
of the proof of Simon Ch. 6, Lemma 2.33, with `c(s) = s`): for `t > 0`, `s ↦ τ(M, θ, ξ)(sⁿ ω(s ·))`
has derivative `τ(M, θ, ξ)(n tⁿ⁻¹ ω(t ·) + tⁿ Dω(t ·)[·])` at `t`.  For `s ∈ (t/2, 2t)` the
integrands vanish off `B = B̄_{2r/t}(0)`, where `spt ω ⊆ B̄_r(0)`, and are dominated by `K θ 1_B`,
`K` bounding the continuous integrand on `[t/2, 2t] × B` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is
integrable since `θ` is locally `Hⁿ`-integrable. -/
theorem Submission.dtc_cwv_scaled_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (t : ℝ), 0 < t → HasDerivAt (fun s : ℝ => R.action (fun y => (s ^ n) • (ω : DifferentialForm (Euclid P) n) (s • y))) (R.action (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) + (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y)) t := by
  intro P n R ω t ht
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: ‖ξ(x)‖ ≤ 1 for Hⁿ⌞M-a.e. x (sibling `orientation_norm`).
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius, a bound for ω; ω and Dω vanish off spt ω.
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 5: measurability of the integrands (Φ jointly continuous).
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y)) (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => (s ^ n) • w (s • y)) := by
    intro s
    have h1 : Continuous (fun y : Euclid P => w (s • y)) := hwcont.comp (continuous_const_smul s)
    exact h1.const_smul (s ^ n)
  have hΦ : Continuous (fun p : ℝ × Euclid P => ((n : ℝ) * p.1 ^ (n - 1)) • w (p.1 • p.2) +
      (p.1 ^ n) • fderiv ℝ w (p.1 • p.2) p.2) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • p.2) := continuous_fst.smul continuous_snd
    exact (((continuous_const.mul (continuous_fst.pow _))).smul (hwcont.comp hsy)).add
      ((continuous_fst.pow _).smul ((hDw.comp hsy).clm_apply continuous_snd))
  have hcF' : ∀ s : ℝ, Continuous (fun y => ((n : ℝ) * s ^ (n - 1)) • w (s • y) +
      (s ^ n) • fderiv ℝ w (s • y) y) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Steps 6–8: localization in B = B̄_ρ(0), the bound K for Φ on [t/2, 2t] × B, integrability.
  set ρ : ℝ := 2 * r / t with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t / 2) (b := 2 * t)).prod (isCompact_closedBall (0 : Euclid P) ρ)
    |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- membership: if s • y ∈ spt ω with s > t/2 then y ∈ B
  have hmemB : ∀ s : ℝ, t / 2 < s → ∀ y : Euclid P, s • y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • y‖ ≤ r := by simpa using hr hy
    have hs0 : 0 < s := by linarith
    rw [norm_smul, Real.norm_of_nonneg hs0.le] at h1
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    rw [le_div_iff₀ ht]
    nlinarith [norm_nonneg y]
  -- Steps 7–9: hypotheses of the dominated differentiation theorem (step 4 is `h_diff`).
  have hs : Ioo (t / 2) (2 * t) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y ((s ^ n) • w (s • y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (((n : ℝ) * t ^ (n - 1)) • w (t • y) + (t ^ n) • fderiv ℝ w (t • y) y))
      (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y ((t ^ n) • w (t • y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul (t ^ n * K0)).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • y ∈ tsupport w
    · have hyB := hmemB t (by linarith) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y ((t ^ n) • w (t • y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖(t ^ n) • w (t • y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * (t ^ n * K0)) := by
            gcongr
            rw [norm_smul, Real.norm_of_nonneg (by positivity)]
            gcongr
            exact hK0 _
        _ = t ^ n * K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, smul_zero, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t / 2) (2 * t),
      ‖(R.mult y : ℝ) * R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
        (s ^ n) • fderiv ℝ w (s • y) y)‖ ≤ K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    obtain ⟨hs1, hs2⟩ := hs
    by_cases hsy : s • y ∈ tsupport w
    · have hyB := hmemB s hs1 y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨⟨hs1.le, hs2.le⟩, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
            (s ^ n) • fderiv ℝ w (s • y) y)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖((n : ℝ) * s ^ (n - 1)) • w (s • y) +
            (s ^ n) • fderiv ℝ w (s • y) y‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).1, (hvan _ hsy).2, smul_zero, zero_apply, smul_zero,
        add_zero, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t / 2) (2 * t),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y ((s ^ n) • w (s • y)))
        ((R.mult y : ℝ) * R.orient y (((n : ℝ) * s ^ (n - 1)) • w (s • y) +
          (s ^ n) • fderiv ℝ w (s • y) y)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • y) y s := by
      simpa using (hasDerivAt_id s).smul_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • y)) (fderiv ℝ w (s • y) y) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • y)).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : HasDerivAt (fun s : ℝ => (s ^ n) • w (s • y))
        ((s ^ n) • fderiv ℝ w (s • y) y + ((n : ℝ) * s ^ (n - 1)) • w (s • y)) s :=
      (hasDerivAt_pow n s).smul h2
    have h4 := ((R.orient y).hasFDerivAt.comp_hasDerivAt s h3).const_mul (R.mult y : ℝ)
    rw [add_comm] at h4
    exact h4
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2
/-- **`∂C = 0` and `x ∧ C⃗ = 0` kill Euler–Lie derivatives** (the homotopy term in the proof of
Simon Ch. 6, Lemma 2.33, as applied in 7.3.1).  Let `C = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)`, `n ≥ 1`, with
`∂C = 0` and `ξ(x)(ι_x α) = 0` for `μ_C`-a.e. `x` and every `(n+1)`-covector `α`.  Then
`C(L_X β) = 0` for the Euler field `X(y) = y`, where `L_X β(y) = n β(y) + Dβ(y)[y]`.  By Cartan's
formula `L_X β = d(ι_X β) + ι_X dβ` (`dtc_cone_euler_cartan`), with `ι_X β` and `ι_X dβ` test forms
(`dtc_cwv_euler_contraction_isTestForm`): `C(d ι_X β) = ∂C(ι_X β) = 0`, and
`C(ι_X dβ) = ∫_M θ ξ(ι_y dβ(y)) dHⁿ = 0` since `θ > 0` on `M`. -/
theorem Submission.dtc_cwv_euler_lie_annihilated : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), 0 < n → R.Represents C → BoundaryVanishes C → (∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β x) = 0) → ∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = (n : ℝ) • (β : DifferentialForm (Euclid P) n) y + fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) → C γ = 0 := by
  intro P n C R hn hR hb hw β γ hγ
  -- write `n = m + 1`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- `ψ = ι_X β` is a test `m`-form
  have hψ : IsTestForm (fun z => ContinuousAlternatingMap.curryLeft
      ((β : DifferentialForm (Euclid P) (m + 1)) z) z) :=
    Submission.dtc_cwv_euler_contraction_isTestForm P m _ β.property.1
  let ψ : TestFormOn (univ : Set (Euclid P)) m := ⟨_, hψ, subset_univ _⟩
  -- `χ = ι_X dβ` is a test `(m + 1)`-form
  have hdβ : IsTestForm (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1))) :=
    exteriorDerivative_isTestForm β.property.1
  have hχ := Submission.dtc_cwv_euler_contraction_isTestForm P (m + 1) _ hdβ
  let χ : TestFormOn (univ : Set (Euclid P)) (m + 1) := ⟨_, hχ, subset_univ _⟩
  -- Cartan's formula: `γ = L_X β = dψ + χ`
  have hsplit : γ = exteriorDerivativeTestOn univ m ψ + χ := by
    apply Subtype.ext
    funext y
    have hdiff : DifferentiableAt ℝ (β : DifferentialForm (Euclid P) (m + 1)) y :=
      (β.property.1.1.differentiable (by simp)).differentiableAt
    have hc := Submission.dtc_cone_euler_cartan P m β y hdiff
    rw [hγ y]
    push_cast
    exact hc.symm
  -- `C(dψ) = ∂C(ψ) = 0`
  have hbd : C.boundary = 0 := hb
  have h1 : C (exteriorDerivativeTestOn univ m ψ) = 0 := by
    have := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) m => T ψ) hbd
    simpa [GeometricCurrentOn.boundary_apply] using this
  -- `C(χ) = ∫_M θ ξ(ι_y dβ(y)) dHⁿ = 0`: the wedge hypothesis passes from `θHⁿ⌞M` to `Hⁿ⌞M`
  have h2 : C χ = 0 := by
    rw [hR χ]
    unfold IMRep.action
    apply integral_eq_zero_of_ae
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      measurable_from_nat.comp R.measurable_mult
    have h' := (ae_withDensity_iff hθ).1 hw
    have hmem : ∀ᵐ x ∂(μHE[m + 1].restrict R.carrier), x ∈ R.carrier :=
      ae_restrict_mem R.measurableSet_carrier
    filter_upwards [h', hmem] with x hx hxM
    have hpos : (R.mult x : ℝ≥0∞) ≠ 0 := by
      have := R.mult_pos x hxM
      exact_mod_cast this.ne'
    have := hx hpos (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x)
    simp only [Pi.zero_apply]
    change (R.mult x : ℝ) * R.orient x (ContinuousAlternatingMap.curryLeft
      (exteriorDerivative (β : DifferentialForm (Euclid P) (m + 1)) x) x) = 0
    rw [this, mul_zero]
  -- linearity: `C(γ) = C(dψ) + C(χ) = 0`
  rw [hsplit]
  change C.toCurrent (exteriorDerivativeTestOn univ m ψ + χ) = 0
  rw [map_add]
  exact (congrArg₂ (· + ·) h1 h2).trans (add_zero 0)

/-- Dilation invariance of `R.action` (Simon Ch. 6, Lemma 2.33 for the dilations `y ↦ sy`; the
step "`C` is a cone" in the proof of 7.3.1).  Suppose `R.action` annihilates every `L_X β`, where
`L_X β(y) = nβ(y) + Dβ(y)[y]` is the Lie derivative of `β` along the Euler field `X(y) = y`.
Put `β_s(y) = sⁿω(sy)` and `G(s) = R.action β_s`.  For `t > 0`, the derivative
`G'(t) = R.action(y ↦ nt^{n−1}ω(ty) + tⁿDω(ty)[y])` (`Submission.dtc_cwv_scaled_action_hasDerivAt`)
is `t⁻¹ R.action(L_X β_t) = 0`.  So `G` is constant on `(0, ∞)`, and
`R.action ω' = G(λ⁻¹) = G(1) = R.action ω`. -/
theorem Submission.dtc_cwv_action_dilation_invariant : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = (n : ℝ) • (β : DifferentialForm (Euclid P) n) y + fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ lam : ℝ, 0 < lam → ∀ ω ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) → R.action (ω' : DifferentialForm (Euclid P) n) = R.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n R hL lam hlam ω ω' hω'
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  -- `R.action` is homogeneous under constant rescaling of the form
  have hsmul : ∀ (c : ℝ) (φ : DifferentialForm (Euclid P) n),
      R.action (fun y => c • φ y) = c * R.action φ := by
    intro c φ
    unfold IMRep.action
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [map_smul, smul_eq_mul]
    ring
  -- `β_t(y) = tⁿ ω(t y)` is a test form for `t ≠ 0`
  have hβs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) := fun t =>
    (hws.comp (contDiff_const_smul t)).const_smul (t ^ n)
  have hβc : ∀ t : ℝ, t ≠ 0 → HasCompactSupport
      (fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) := by
    intro t ht
    refine (hwc.comp_smul ht).mono ?_
    intro y hy
    simp only [mem_support] at hy ⊢
    intro h0
    apply hy
    rw [h0, smul_zero]
  -- chain rule: `Dβ_t(y)[y] = tⁿ⁺¹ Dω(t y)[y]`
  have hfd : ∀ (t : ℝ) (y : Euclid P),
      fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y =
        (t ^ n * t) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y := by
    intro t y
    have h1 : HasFDerivAt (fun z : Euclid P => t • z) (t • ContinuousLinearMap.id ℝ (Euclid P)) y :=
      (hasFDerivAt_id y).const_smul t
    have h2 : HasFDerivAt (fun z : Euclid P => (ω : DifferentialForm (Euclid P) n) (t • z))
        ((fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y)).comp
          (t • ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hws.differentiable (by simp)).differentiableAt (x := t • y)).hasFDerivAt.comp y h1
    have h3 : HasFDerivAt (fun z : Euclid P => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z))
        ((t ^ n) • (fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y)).comp
          (t • ContinuousLinearMap.id ℝ (Euclid P))) y :=
      h2.const_smul (t ^ n)
    rw [h3.fderiv]
    simp [smul_smul]
  -- `γ_t(y) = nβ_t(y) + Dβ_t(y)[y]` is a test form for `t ≠ 0`
  have hγs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
    intro t
    have hd : ContDiff ℝ (⊤ : ℕ∞)
        (fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z))) :=
      (hβs t).fderiv_right (by simp)
    exact ((hβs t).const_smul (n : ℝ)).add (hd.clm_apply contDiff_id)
  have hγc : ∀ t : ℝ, t ≠ 0 → HasCompactSupport
      (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
    intro t ht
    have h1 : HasCompactSupport
        (fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y))) := by
      refine (hβc t ht).mono ?_
      intro y hy
      simp only [mem_support] at hy ⊢
      intro h0
      apply hy
      rw [h0, smul_zero]
    have h2 : HasCompactSupport
        (fun y => fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y) := by
      refine ((hβc t ht).fderiv ℝ).mono ?_
      intro y hy
      simp only [mem_support] at hy ⊢
      intro h0
      apply hy
      rw [h0]
      rfl
    exact h1.add h2
  -- `G(s) = R.action β_s` has derivative `t⁻¹ R.action γ_t = 0` at every `t > 0`
  let G : ℝ → ℝ := fun s => R.action (fun y => (s ^ n) • (ω : DifferentialForm (Euclid P) n) (s • y))
  have hG : ∀ t : ℝ, 0 < t → HasDerivAt G 0 t := by
    intro t ht
    have hD := Submission.dtc_cwv_scaled_action_hasDerivAt P n R ω t ht
    let β : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y), ⟨hβs t, hβc t ht.ne'⟩,
        subset_univ _⟩
    let γ : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y,
        ⟨hγs t, hγc t ht.ne'⟩, subset_univ _⟩
    have hγ0 : R.action (γ : DifferentialForm (Euclid P) n) = 0 := hL β γ (fun y => rfl)
    have heq : (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) +
        (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y) =
        fun y => t⁻¹ • (γ : DifferentialForm (Euclid P) n) y := by
      funext y
      change _ = t⁻¹ • ((n : ℝ) • ((t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • y)) +
        fderiv ℝ (fun z => (t ^ n) • (ω : DifferentialForm (Euclid P) n) (t • z)) y y)
      rw [hfd t y, smul_add, smul_smul, smul_smul, smul_smul]
      congr 2
      · rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          field_simp
          simp [pow_succ]
      · field_simp
    have h0 : R.action (fun y => ((n : ℝ) * t ^ (n - 1)) • (ω : DifferentialForm (Euclid P) n) (t • y) +
        (t ^ n) • fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • y) y) = 0 := by
      rw [heq, hsmul, hγ0, mul_zero]
    rw [h0] at hD
    exact hD
  -- `G` is constant on the connected open set `(0, ∞)`
  have hconst : G lam⁻¹ = G 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun t ht => (hG t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hG t ht).deriv) (inv_pos.2 hlam) (show (0 : ℝ) < 1 from one_pos)
  have hG1 : G 1 = R.action (ω : DifferentialForm (Euclid P) n) := by
    simp [G]
  have hGl : G lam⁻¹ = R.action (ω' : DifferentialForm (Euclid P) n) := by
    simp only [G]
    congr 1
    funext y
    rw [hω' y]
  rw [← hGl, hconst, hG1]

/-- **Radial tangency makes a boundaryless current a cone** (step 4 of the cone-splitting proof:
Simon 7.3.1(2) proof, Ch. 6, 2.25–2.27 and 2.33).  Let `S = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)`, `n ≥ 1`,
`∂S = 0`, with `x ∈ TₓM` for `μ`-a.e. `x`.  Then `x ∧ ξ(x) = 0` `μ`-a.e.
(`dtc_cone_wedge_vanishes`), so `S` annihilates `L_X β = nβ + Dβ[·]` for the Euler field
(`dtc_cwv_euler_lie_annihilated`), hence `G(s) = S(sⁿ ω(s ·))` is constant on `(0, ∞)`
(`dtc_cwv_action_dilation_invariant`), i.e. `S(λ⁻ⁿ ω(λ⁻¹ ·)) = S(ω)`, and `S` is a cone by the
cone criterion `dtc_cwv_isConeCurrent_of_pullback_invariant`. -/
theorem Submission.dimred_cs_cone_of_radial_tangency : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), 0 < n → R.Represents S → BoundaryVanishes S → (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x) → IsConeCurrent S := by
  intro P n S R hn hR hb hrad
  -- step 2: `ξ(x)(ι_x β) = 0` for `μ`-a.e. `x` and every `(n + 1)`-covector `β`
  have hw := Submission.dtc_cone_wedge_vanishes P n univ R hrad
  -- step 4: `R.action (L_X β) = S(L_X β) = 0`
  have hL : ∀ β γ : TestFormOn (univ : Set (Euclid P)) n,
      (∀ y, (γ : DifferentialForm (Euclid P) n) y =
        (n : ℝ) • (β : DifferentialForm (Euclid P) n) y +
          fderiv ℝ (β : DifferentialForm (Euclid P) n) y y) →
      R.action (γ : DifferentialForm (Euclid P) n) = 0 := fun β γ hγ =>
    (hR γ).symm.trans (Submission.dtc_cwv_euler_lie_annihilated P n S R hn hR hb hw β γ hγ)
  -- steps 1, 3 and 5: by the cone criterion, `S(ω') = R.action ω' = R.action ω = S(ω)`
  refine Submission.dtc_cwv_isConeCurrent_of_pullback_invariant P n S fun lam hlam ω ω' hω' => ?_
  rw [hR ω', hR ω]
  exact Submission.dtc_cwv_action_dilation_invariant P n R hL lam hlam ω ω' hω'

/-- Differentiation under the integral sign for the translations `y ↦ sv + y`: for every `t`,
`s ↦ τ(M, θ, ξ)(ω(sv + ·))` has derivative `τ(M, θ, ξ)(Dω(tv + ·)[v])` at `t`.  For
`s ∈ (t − 1, t + 1)` the integrands vanish off `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖` where
`spt ω ⊆ B̄_r(0)`, and are dominated by `K θ 1_B`, `K` bounding the continuous map
`(s, y) ↦ Dω(sv + y)[v]` on `[t − 1, t + 1] × B` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is integrable since
`θ` is locally `Hⁿ`-integrable. -/
theorem Submission.dimred_cs_ti_translate_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (v : Euclid P) (t : ℝ), HasDerivAt (fun s : ℝ => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))) (R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v)) t := by
  intro P n R ω v t
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: `‖ξ(x)‖ ≤ 1` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius `r` and a bound `K0` for `ω`; `ω` and `Dω` vanish off `spt ω`
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 3: measurability of the integrands
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y))
        (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => w (s • v + y)) := fun s =>
    hwcont.comp (continuous_const.add continuous_id)
  have hΦ : Continuous (fun p : ℝ × Euclid P => fderiv ℝ w (p.1 • v + p.2) v) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • v + p.2) :=
      (continuous_fst.smul continuous_const).add continuous_snd
    exact (hDw.comp hsy).clm_apply continuous_const
  have hcF' : ∀ s : ℝ, Continuous (fun y => fderiv ℝ w (s • v + y) v) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Step 4: localization in `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖`; the bound `K` of `Dω(sv+y)[v]`
  set ρ : ℝ := r + (|t| + 1) * ‖v‖ with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod
    (isCompact_closedBall (0 : Euclid P) ρ) |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- if `|s| ≤ |t| + 1` and `s v + y ∈ spt ω` then `y ∈ B`
  have hmemB : ∀ s : ℝ, |s| ≤ |t| + 1 → ∀ y : Euclid P, s • v + y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • v + y‖ ≤ r := by simpa using hr hy
    have h2 := norm_sub_le (s • v + y) (s • v)
    rw [add_sub_cancel_left] at h2
    have h3 : ‖s • v‖ ≤ (|t| + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    linarith
  have habs : ∀ s ∈ Icc (t - 1) (t + 1), |s| ≤ |t| + 1 := by
    intro s hs
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, neg_abs_le t, le_abs_self t]
  -- Step 5: hypotheses of the dominated differentiation theorem
  have hs : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y (w (s • v + y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (fderiv ℝ w (t • v + y) v)) (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y (w (t • v + y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul K0).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • v + y ∈ tsupport w
    · have hyB := hmemB t (by linarith [abs_nonneg t]) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y (w (t • v + y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖w (t • v + y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K0) := by
            gcongr
            exact hK0 _
        _ = K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      ‖(R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)‖ ≤
        K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    by_cases hsy : s • v + y ∈ tsupport w
    · have hyB := hmemB s (habs s (Ioo_subset_Icc_self hs)) y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨Ioo_subset_Icc_self hs, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (fderiv ℝ w (s • v + y) v)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖fderiv ℝ w (s • v + y) v‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).2, zero_apply, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y (w (s • v + y)))
        ((R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • v + y) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).add_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • v + y)) (fderiv ℝ w (s • v + y) v) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • v + y)).hasFDerivAt.comp_hasDerivAt
        s h1
    exact ((R.orient y).hasFDerivAt.comp_hasDerivAt s h2).const_mul (R.mult y : ℝ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2

/-- Translation invariance of `R.action` (the integrated form of `L_v S = 0`; Simon Ch. 6, 2.25
for the homotopy `h(t, x) = x + tv`, the translation counterpart of Lemma 2.33).  Suppose
`R.action` annihilates every directional derivative `y ↦ Dβ(y)[v]` of a test form `β`.  Put
`β_s(y) = ω(sv + y)` and `G(s) = R.action β_s`.  Its derivative
`G'(t) = R.action(Dω(tv + ·)[v]) = R.action(Dβ_t(·)[v])`
(`Submission.dimred_cs_ti_translate_action_hasDerivAt`) vanishes for every `t`, so `G` is constant
and `R.action(ω(v + ·)) = G(1) = G(0) = R.action ω`. -/
theorem Submission.dimred_cs_ti_action_translation_invariant : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), (∀ β γ : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (γ : DifferentialForm (Euclid P) n) y = fderiv ℝ (β : DifferentialForm (Euclid P) n) y v) → R.action (γ : DifferentialForm (Euclid P) n) = 0) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, R.action (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) = R.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n R v hL ω
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  -- Step 1: `β_t(y) = ω(tv + y)` is a test form
  have hβs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
    fun t => hws.comp (contDiff_const.add contDiff_id)
  have hβc : ∀ t : ℝ, HasCompactSupport
      (fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
    fun t => hwc.comp_homeomorph (Homeomorph.addLeft (t • v))
  -- Step 2: chain rule, `Dβ_t(y) = Dω(tv + y)`
  have hfd : ∀ (t : ℝ) (y : Euclid P),
      fderiv ℝ (fun z => (ω : DifferentialForm (Euclid P) n) (t • v + z)) y =
        fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) :=
    fun t y => fderiv_comp_add_left (t • v)
  -- Step 3: `γ_t(y) = Dω(tv + y)[v]` is a test form
  have hγs : ∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) := by
    intro t
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (ω : DifferentialForm (Euclid P) n)) :=
      hws.fderiv_right (by simp)
    exact (hd.comp (contDiff_const.add contDiff_id)).clm_apply contDiff_const
  have hγc : ∀ t : ℝ, HasCompactSupport
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) := by
    intro t
    have h1 : HasCompactSupport
        (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y)) :=
      (hwc.fderiv ℝ).comp_homeomorph (Homeomorph.addLeft (t • v))
    refine h1.mono ?_
    intro y hy
    simp only [mem_support] at hy ⊢
    intro h0
    apply hy
    rw [h0]
    rfl
  -- Steps 4–5: `G(s) = R.action β_s` has derivative `R.action γ_t = 0` at every `t`
  let G : ℝ → ℝ := fun s => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))
  have hG : ∀ t : ℝ, HasDerivAt G 0 t := by
    intro t
    have hD := Submission.dimred_cs_ti_translate_action_hasDerivAt P n R ω v t
    let β : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => (ω : DifferentialForm (Euclid P) n) (t • v + y), ⟨hβs t, hβc t⟩, subset_univ _⟩
    let γ : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v, ⟨hγs t, hγc t⟩,
        subset_univ _⟩
    have hγ0 : R.action (γ : DifferentialForm (Euclid P) n) = 0 :=
      hL β γ (fun y => by
        change fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v =
          fderiv ℝ (fun z => (ω : DifferentialForm (Euclid P) n) (t • v + z)) y v
        rw [hfd t y])
    have h0 : R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v) = 0 :=
      hγ0
    rw [h0] at hD
    exact hD
  -- Step 6: `G` is constant on `ℝ`
  have hconst : G 1 = G 0 :=
    is_const_of_deriv_eq_zero (fun t => (hG t).differentiableAt) (fun t => (hG t).deriv) 1 0
  -- Step 7: `G(1) = R.action(ω(v + ·))` and `G(0) = R.action ω`
  have hG1 : G 1 = R.action (fun y => (ω : DifferentialForm (Euclid P) n) (v + y)) := by
    simp [G]
  have hG0 : G 0 = R.action (ω : DifferentialForm (Euclid P) n) := by
    simp [G]
  rw [← hG1, hconst, hG0]

/-- **Translation invariance from tangency** (the translation counterpart of Simon Ch. 6,
Lemma 2.33; the translation invariance `η_{x,1#}S = S` of the cone splitting in 7.3.3, 7.3.5).
Let `S = τ(M, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)`, `n ≥ 1`, with `∂S = 0` and `v ∈ TₓM` for `μ_S`-a.e. `x`.  Then
`η_{−v,1#}S = S`.  Since `η_{−v,1}(y) = v + y`, `η_{−v,1#}S(ω) = S(ω(v + ·))`, so it suffices that
`s ↦ S(β_s)`, `β_s = ω(sv + ·)`, is constant.  Its derivative is `S(Dβ_s[v])`, and
`S(Dβ[v]) = S(d ι_v β) + S(ι_v dβ) = ∂S(ι_v β) + 0 = 0` by Cartan's formula for the constant
field `v`, `∂S = 0` and `v ∧ ξ = 0` `μ_S`-a.e. -/
theorem Submission.dimred_cs_translation_invariant_of_tangency : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (v : Euclid P), 0 < n → R.Represents S → BoundaryVanishes S → (∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection v = v) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω := by
  intro P n S R v hn hR hb htan ω
  -- `η_{−v,1#}S(ω) = S(ω')` with `ω'(y) = ω(v + y)`, so it suffices that `S(ω') = S(ω)`
  obtain ⟨ω', hω', heval⟩ := Submission.dimred_cs_ti_blowUp_translate_eval P n S v ω
  rw [heval, hR ω', hR ω]
  have hfun : (ω' : DifferentialForm (Euclid P) n) =
      fun y => (ω : DifferentialForm (Euclid P) n) (v + y) := funext hω'
  rw [hfun]
  -- `s ↦ τ(M, θ, ξ)(ω(sv + ·))` is constant once `τ(M, θ, ξ)` kills every `Dβ[v]`
  refine Submission.dimred_cs_ti_action_translation_invariant P n R v ?_ ω
  intro β γ hγ
  -- `S(Dβ[v]) = S(d ι_v β) + S(ι_v dβ) = 0`, as `v ∧ ξ = 0` `μ_S`-a.e.
  rw [← hR γ]
  exact Submission.dimred_cs_ti_directional_annihilated P n S R v hn hR hb
    (Submission.dimred_cs_ti_wedge_vanishes P n univ R v htan) β γ hγ
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
/-- Balls of a product measure `μ = Hᵈ⌞L ⊗ μ₀` (`d = dim L`, `μ₀` concentrated on `L^⊥`):
`μ(B_ρ(t + y)) = ∫_{ℝᵈ} μ₀(B_{√(ρ² − |σ|²)}(y)) dLᵈ(σ)` for `t ∈ L`, `y ∈ L^⊥` and `ρ > 0`.  For
`s ∈ L` and `y' ∈ L^⊥`, Pythagoras gives `s + y' ∈ B_ρ(t + y)` iff `y' ∈ B_{√(ρ² − |t − s|²)}(y)`;
an isometric parametrization of `L` by `ℝᵈ` carries `Lᵈ` to `Hᵈ⌞L`, and a translation centres the
integral at `t`. -/
theorem Submission.dimred_cs_psd_ball_formula : ∀ (P : ℕ) (L : Submodule ℝ (Euclid P)) (μ μ₀ : Measure (Euclid P)), μ₀ (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → μ A = ∫⁻ t in (L : Set (Euclid P)), μ₀ ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) → ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ ρ : ℝ, 0 < ρ → μ (ball (t + y) ρ) = ∫⁻ σ : Euclid (Module.finrank ℝ L), μ₀ (ball y (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2))) := by
  intro P L μ μ₀ hconc hprod t ht y hy ρ hρ
  -- concentration of `μ₀` on `Lᗮ`
  have hconc' : ∀ X : Set (Euclid P), μ₀ X = μ₀ (X ∩ (Lᗮ : Set (Euclid P))) := by
    intro X
    refine le_antisymm ?_ (measure_mono inter_subset_left)
    calc μ₀ X ≤ μ₀ (X ∩ (Lᗮ : Set (Euclid P))) + μ₀ (X \ (Lᗮ : Set (Euclid P))) :=
          measure_le_inter_add_sdiff μ₀ X _
      _ ≤ μ₀ (X ∩ (Lᗮ : Set (Euclid P))) + μ₀ (Lᗮ : Set (Euclid P))ᶜ := by
          gcongr
          exact fun z hz => hz.2
      _ = μ₀ (X ∩ (Lᗮ : Set (Euclid P))) := by rw [hconc, add_zero]
  -- slicing the ball over a point `s ∈ L`
  have hslice : ∀ s ∈ L, μ₀ ((fun y' => s + y') ⁻¹' ball (t + y) ρ) =
      μ₀ (ball y (Real.sqrt (ρ ^ 2 - ‖t - s‖ ^ 2))) := by
    intro s hs
    rw [hconc' ((fun y' => s + y') ⁻¹' ball (t + y) ρ), hconc' (ball y _)]
    congr 1
    ext y'
    simp only [mem_inter_iff, mem_preimage, mem_ball, SetLike.mem_coe]
    refine and_congr_left fun hy' => ?_
    have horth : inner ℝ (s - t) (y' - y) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (L.sub_mem hs ht) (Lᗮ.sub_mem hy' hy)
    have hpyth : ‖s + y' - (t + y)‖ ^ 2 = ‖t - s‖ ^ 2 + ‖y' - y‖ ^ 2 := by
      have h1 : s + y' - (t + y) = (s - t) + (y' - y) := by abel
      rw [h1, ← norm_neg (t - s), neg_sub]
      have := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      nlinarith [this]
    rw [dist_eq_norm, dist_eq_norm, Real.lt_sqrt (norm_nonneg _)]
    rw [← sq_lt_sq₀ (norm_nonneg _) hρ.le, hpyth]
    constructor <;> intro h <;> linarith
  rw [hprod _ measurableSet_ball,
    setLIntegral_congr_fun (Submodule.closed_of_finiteDimensional L).measurableSet hslice]
  -- an isometric parametrization of `L` by `ℝᵈ`
  set d := Module.finrank ℝ L
  let b := stdOrthonormalBasis ℝ L
  let ι : Euclid d → Euclid P := fun σ => ((b.repr.symm σ : L) : Euclid P)
  have hι : Isometry ι := L.subtypeₗᵢ.isometry.comp b.repr.symm.isometry
  have hrange : range ι = (L : Set (Euclid P)) := by
    ext z
    constructor
    · rintro ⟨σ, rfl⟩
      exact (b.repr.symm σ).2
    · intro hz
      exact ⟨b.repr ⟨z, hz⟩, by simp [ι]⟩
  have hmap : (volume : Measure (Euclid d)).map ι = μHE[d].restrict (L : Set (Euclid P)) := by
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hι.map_euclideanHausdorffMeasure,
      hrange]
  rw [← hmap, hι.isClosedEmbedding.measurableEmbedding.lintegral_map]
  -- translate
  set σt : Euclid d := b.repr ⟨t, ht⟩
  have hnorm : ∀ σ : Euclid d, ‖t - ι σ‖ = ‖σ - σt‖ := by
    intro σ
    have ht' : t = ι σt := by simp [ι, σt]
    rw [ht', ← dist_eq_norm, hι.dist_eq, dist_eq_norm, norm_sub_rev]
  simp_rw [hnorm]
  exact lintegral_sub_right_eq_self (fun σ => μ₀ (ball y (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)))) σt
/-- **Cavalieri slicing of Euclidean balls**: for `ρ ≥ 0`,
`L^{d+m}(B_ρ(0)) = ∫_{ℝᵈ} Lᵐ(B_{√(ρ² − ‖σ‖²)}(0)) dLᵈ(σ)`.  Reindexing along
`Fin d ⊕ Fin m ≃ Fin (d + m)` and splitting the blocks is a linear isometry
`ℝ^{d+m} ≃ ℝᵈ × ℝᵐ` (L² product norm), hence carries `L^{d+m}` to `Lᵈ ⊗ Lᵐ`; it maps `B_ρ(0)`
onto `Q = {(u, v) : ‖u‖² + ‖v‖² < ρ²}`, whose slice over `σ` is `B_{√(ρ² − ‖σ‖²)}(0)`, and Tonelli
gives the formula. -/
theorem Submission.dimred_cs_psd_ball_volume_slice : ∀ (d m : ℕ) (ρ : ℝ), 0 ≤ ρ → volume (ball (0 : Euclid (d + m)) ρ) = ∫⁻ σ : Euclid d, volume (ball (0 : Euclid m) (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2))) := by
  intro d m ρ hρ
  -- `Φ = ofLp ∘ e : ℝ^{d+m} → ℝᵈ × ℝᵐ` is volume preserving onto `Lᵈ ⊗ Lᵐ`
  let e : Euclid (d + m) ≃ₗᵢ[ℝ] WithLp 2 (Euclid d × Euclid m) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm).trans
      (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ => ℝ))
  have hΦ : MeasurePreserving (fun x => WithLp.ofLp (e x)) volume
      ((volume : Measure (Euclid d)).prod (volume : Measure (Euclid m))) := by
    have h := (WithLp.volume_preserving_ofLp (Euclid d) (Euclid m)).comp e.measurePreserving
    rw [← Measure.volume_eq_prod]
    exact h
  -- `B_ρ(0) = Φ⁻¹(Q)`, since `‖x‖² = ‖Φ(x).1‖² + ‖Φ(x).2‖²`
  set Q : Set (Euclid d × Euclid m) := {p | ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 < ρ ^ 2}
  have hQ : MeasurableSet Q :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hpre : (fun x => WithLp.ofLp (e x)) ⁻¹' Q = ball (0 : Euclid (d + m)) ρ := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_ball_zero_iff, Q]
    have hn : ‖x‖ ^ 2 = ‖(WithLp.ofLp (e x)).1‖ ^ 2 + ‖(WithLp.ofLp (e x)).2‖ ^ 2 := by
      rw [← e.norm_map x, WithLp.prod_norm_sq_eq_of_L2]
      rfl
    rw [← hn]
    exact sq_lt_sq₀ (norm_nonneg x) hρ
  -- Tonelli, and the slice of `Q` over `σ` is `B_{√(ρ² − ‖σ‖²)}(0)`
  rw [← hpre, hΦ.measure_preimage hQ.nullMeasurableSet, Measure.prod_apply hQ]
  refine lintegral_congr fun σ => ?_
  congr 1
  ext v
  simp only [mem_preimage, mem_ofPred_eq, mem_ball_zero_iff, Q]
  rw [Real.lt_sqrt (norm_nonneg v)]
  constructor <;> intro h <;> linarith

/-- **Simon 7.3.5** (chapter-07.txt lines 407–417, proof left to the reader): the density step
for a product `[[L]] × S₀`, with `d = dim L`.  If `f(0) = 0` and `f(r)/(ωₘrᵐ) → θ` as `r ↓ 0`, then
`(ω_{d+m}ρ^{d+m})⁻¹ ∫_{ℝᵈ} f(√(ρ² − |σ|²)) dσ → θ` as `ρ ↓ 0`.  Every radius `√(ρ² − |σ|²)`
lies in `[0, ρ]`, so for `a' < θ < b'` the hypothesis gives `a'·Lᵐ(B_r) ≤ f(r) ≤ b'·Lᵐ(B_r)` for
all small `r ≥ 0`.  Integrating in `σ` and using the slice identity
`∫_{ℝᵈ} Lᵐ(B_{√(ρ² − |σ|²)}) dσ = L^{d+m}(B_ρ) = ω_{d+m}ρ^{d+m}` bounds the ratio between `a'`
and `b'` for all small `ρ > 0`; no measurability of `f` is needed. -/
theorem Submission.dimred_cs_psd_radial_density : ∀ (d m : ℕ) (f : ℝ → ℝ≥0∞) (θ : ℝ≥0∞), f 0 = 0 → Tendsto (fun r : ℝ => f r / (unitBallVolume m * ENNReal.ofReal (r ^ m))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => (∫⁻ σ : Euclid d, f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2))) / (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m)))) (𝓝[>] 0) (𝓝 θ) := by
  intro d m f θ hf0 hlim
  -- `Lᵏ(B_r(0)) = ωₖrᵏ` for `r > 0`, with `0 < ωₖ < ∞`
  have hvol : ∀ (k : ℕ) (r : ℝ), 0 < r →
      volume (ball (0 : Euclid k) r) = unitBallVolume k * ENNReal.ofReal (r ^ k) := by
    intro k r hr
    rw [Measure.addHaar_ball_of_pos volume (0 : Euclid k) hr, finrank_euclideanSpace_fin, mul_comm]
    rfl
  have hω0 : ∀ k : ℕ, unitBallVolume k ≠ 0 := fun k =>
    (measure_ball_pos volume (0 : Euclid k) one_pos).ne'
  have hωt : ∀ k : ℕ, unitBallVolume k ≠ ⊤ := fun k => measure_ball_lt_top.ne
  have hc0 : ∀ (k : ℕ) (r : ℝ), 0 < r → unitBallVolume k * ENNReal.ofReal (r ^ k) ≠ 0 := by
    intro k r hr
    exact mul_ne_zero (hω0 k) (ENNReal.ofReal_pos.2 (pow_pos hr k)).ne'
  have hct : ∀ (k : ℕ) (r : ℝ), unitBallVolume k * ENNReal.ofReal (r ^ k) ≠ ⊤ := fun k r =>
    ENNReal.mul_ne_top (hωt k) ENNReal.ofReal_ne_top
  -- the comparison profile `v(r) = Lᵐ(B_r(0))`, with `v(0) = 0 = f(0)`
  set v : ℝ → ℝ≥0∞ := fun r => volume (ball (0 : Euclid m) r) with hv
  have hv0 : v 0 = 0 := by simp [hv]
  -- slice identity: `∫_{ℝᵈ} v(√(ρ² − |σ|²)) dσ = ω_{d+m}ρ^{d+m}`
  have hslice : ∀ ρ : ℝ, 0 < ρ → ∫⁻ σ : Euclid d, v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) =
      unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m)) := by
    intro ρ hρ
    rw [← hvol _ _ hρ, Submission.dimred_cs_psd_ball_volume_slice d m ρ hρ.le]
  -- every radius `√(ρ² − |σ|²)` lies in `[0, ρ]`
  have hsq_le : ∀ ρ : ℝ, 0 < ρ → ∀ σ : Euclid d, Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ≤ ρ := by
    intro ρ hρ σ
    calc Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ≤ Real.sqrt (ρ ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [norm_nonneg σ])
      _ = ρ := Real.sqrt_sq hρ.le
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower bound: `a'·v ≤ f` on `[0, s)` integrates to `a' ≤` the ratio for `ρ ∈ (0, s)`
    obtain ⟨a', haa', ha'θ⟩ := exists_between ha
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), a' < f r / (unitBallVolume m * ENNReal.ofReal (r ^ m)) :=
      (tendsto_order.1 hlim).1 a' ha'θ
    obtain ⟨s, hs, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    have hbound : ∀ σ : Euclid d, a' * v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) ≤
        f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      rcases (Real.sqrt_nonneg (ρ ^ 2 - ‖σ‖ ^ 2)).eq_or_lt with h | h
      · rw [← h, hv0, mul_zero]
        exact zero_le
      · have hr : Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ∈ Ioo 0 s :=
          ⟨h, lt_of_le_of_lt (hsq_le ρ hρ.1 σ) hρ.2⟩
        have h2 := hsub hr
        simp only [mem_ofPred_eq] at h2
        rw [ENNReal.lt_div_iff_mul_lt (Or.inl (hc0 m _ h)) (Or.inl (hct m _))] at h2
        rw [hv]
        simp only
        rw [hvol m _ h]
        exact h2.le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hbound
    rw [lintegral_const_mul' _ _ (ne_top_of_lt ha'θ), hslice ρ hρ.1] at hint
    calc a < a' := haa'
      _ = a' * (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) /
            (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) :=
          (ENNReal.mul_div_cancel_right (hc0 _ _ hρ.1) (hct _ _)).symm
      _ ≤ _ := ENNReal.div_le_div_right hint _
  · -- upper bound: `f ≤ b'·v` on `[0, s)` integrates to the ratio `≤ b'` for `ρ ∈ (0, s)`
    obtain ⟨b', hθb', hb'b⟩ := exists_between hb
    have h1 : ∀ᶠ r in 𝓝[>] (0 : ℝ), f r / (unitBallVolume m * ENNReal.ofReal (r ^ m)) < b' :=
      (tendsto_order.1 hlim).2 b' hθb'
    obtain ⟨s, hs, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    have hbound : ∀ σ : Euclid d, f (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) ≤
        b' * v (Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      rcases (Real.sqrt_nonneg (ρ ^ 2 - ‖σ‖ ^ 2)).eq_or_lt with h | h
      · rw [← h, hf0]
        exact zero_le
      · have hr : Real.sqrt (ρ ^ 2 - ‖σ‖ ^ 2) ∈ Ioo 0 s :=
          ⟨h, lt_of_le_of_lt (hsq_le ρ hρ.1 σ) hρ.2⟩
        have h2 := hsub hr
        simp only [mem_ofPred_eq] at h2
        rw [ENNReal.div_lt_iff (Or.inl (hc0 m _ h)) (Or.inl (hct m _))] at h2
        rw [hv]
        simp only
        rw [hvol m _ h]
        exact h2.le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hbound
    rw [lintegral_const_mul' _ _ (ne_top_of_lt hb'b), hslice ρ hρ.1] at hint
    calc _ ≤ b' * (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) /
            (unitBallVolume (d + m) * ENNReal.ofReal (ρ ^ (d + m))) :=
          ENNReal.div_le_div_right hint _
      _ = b' := ENNReal.mul_div_cancel_right (hc0 _ _ hρ.1) (hct _ _)
      _ < b := hb'b
/-- For a nondecreasing `f : ℝ → [0, ∞]`, `∫_{ℝᵈ} f(√(ε² − |σ|²)) dσ ≠ 0` for every `ε > 0` iff
`f(ε) ≠ 0` for every `ε > 0`.  Every radius `√(ε² − |σ|²)` lies in `[0, ε]`, so `f(ε) = 0` kills
the integrand; conversely the integrand is `≥ f(ε/2)` on `B_{ε/2}(0)`, a ball of positive
Lebesgue measure. -/
theorem Submission.dimred_cs_psd_radial_support : ∀ (d : ℕ) (f : ℝ → ℝ≥0∞), Monotone f → ((∀ ε : ℝ, 0 < ε → (∫⁻ σ : Euclid d, f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2))) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → f ε ≠ 0) := by
  intro d f hf
  constructor
  · -- (⇒) if `f(ε) = 0`, then `0 ≤ f(√(ε² − |σ|²)) ≤ f(ε) = 0` for every `σ`
    intro h ε hε hfε
    apply h ε hε
    have hz : ∀ σ : Euclid d, f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) = 0 := by
      intro σ
      refine le_antisymm ?_ zero_le
      calc f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) ≤ f ε := by
            apply hf
            calc Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2) ≤ Real.sqrt (ε ^ 2) :=
                  Real.sqrt_le_sqrt (by nlinarith [norm_nonneg σ])
              _ = ε := Real.sqrt_sq hε.le
        _ = 0 := hfε
    simp [hz]
  · -- (⇐) the integral is `≥ f(ε/2) · Lᵈ(B_{ε/2}(0))`, a product of nonzero factors
    intro h ε hε h0
    have hε2 : 0 < ε / 2 := by linarith
    have hle : ∀ σ : Euclid d, (ball (0 : Euclid d) (ε / 2)).indicator (fun _ => f (ε / 2)) σ ≤
        f (Real.sqrt (ε ^ 2 - ‖σ‖ ^ 2)) := by
      intro σ
      by_cases hσ : σ ∈ ball (0 : Euclid d) (ε / 2)
      · rw [indicator_of_mem hσ]
        apply hf
        rw [mem_ball_zero_iff] at hσ
        rw [Real.le_sqrt hε2.le (by nlinarith [norm_nonneg σ])]
        nlinarith [norm_nonneg σ]
      · rw [indicator_of_notMem hσ]
        exact zero_le
    have hint := lintegral_mono (μ := (volume : Measure (Euclid d))) hle
    rw [h0, lintegral_indicator_const measurableSet_ball] at hint
    have hprod : f (ε / 2) * volume (ball (0 : Euclid d) (ε / 2)) = 0 := le_antisymm hint zero_le
    rcases mul_eq_zero.1 hprod with hf0 | hv0
    · exact h _ hε2 hf0
    · exact (measure_ball_pos volume (0 : Euclid d) hε2).ne' hv0

/-- Supports and densities of `[[L]] × S₀` (in the proof of **Simon 7.3.5**, chapter-07.txt
lines 410–418, which the book leaves to the reader): let `d = dim L < n`, let `R`, `R₀` represent
`S`, `S₀` in `ℝᴾ`, and put `μ = μ_R`, `μ₀ = μ_{R₀}`.  If `μ₀(ℝᴾ ∖ L^⊥) = 0` and
`μ(A) = ∫_L μ₀(A − t) dHᵈ(t)` for Borel `A`, then for `t ∈ L`, `y ∈ L^⊥` and `ρ > 0`,
`μ(B_ρ(t + y)) = ∫_{ℝᵈ} f(√(ρ² − |σ|²)) dσ` with `f(r) = μ₀(B_r(y))`.  As `f` is nondecreasing,
`μ` charges every ball about `t + y` iff `μ₀` charges every ball about `y`, i.e.
`t + y ∈ spt S ⟺ y ∈ spt S₀`.  If `(ω_{n−d} r^{n−d})⁻¹ f(r) → θ` as `r ↓ 0`, then
`(ωₙρⁿ)⁻¹ μ(B_ρ(t + y)) → θ`, as `d + (n − d) = n`; so a density of `S₀` at `y` is one of `S`
at `t + y`, and, densities being unique, `S₀` having a density at `y` gives the converse. -/
theorem Submission.dimred_cs_product_support_density : ∀ (P n : ℕ) (L : Submodule ℝ (Euclid P)) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R : IMRep (univ : Set (Euclid P)) n) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)), Module.finrank ℝ L < n → R.Represents S → R₀.Represents S₀ → R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 → (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) → (∀ y ∈ Lᗮ, ∃ θ : ℝ, HasMassDensity S₀ y θ) → (∀ t ∈ L, ∀ y ∈ Lᗮ, (t + y ∈ S.support ↔ y ∈ S₀.support)) ∧ ∀ t ∈ L, ∀ y ∈ Lᗮ, ∀ θ : ℝ, (HasMassDensity S (t + y) θ ↔ HasMassDensity S₀ y θ) := by
  intro P n L S S₀ R R₀ hdn hR hR₀ hconc hprod hdens
  -- `M_W(S) = μ(W)` and `M_W(S₀) = μ₀(W)` for open `W`; supports are read off from balls
  obtain ⟨hmS, hsS, -⟩ := Submission.dimred_im_mass_measure P n univ S R isOpen_univ hR
  obtain ⟨hmS₀, hsS₀, -⟩ :=
    Submission.dimred_im_mass_measure P (n - Module.finrank ℝ L) univ S₀ R₀ isOpen_univ hR₀
  -- slicing: `μ(B_ρ(t + y)) = ∫_{ℝᵈ} μ₀(B_{√(ρ² − |σ|²)}(y)) dσ`
  have hball := Submission.dimred_cs_psd_ball_formula P L R.measure R₀.measure hconc hprod
  refine ⟨fun t ht y hy => ?_, fun t ht y hy θ => ?_⟩
  · -- supports, via the nondecreasing profile `r ↦ μ₀(B_r(y))`
    have hmono : Monotone fun r : ℝ => R₀.measure (ball y r) :=
      fun a b hab => measure_mono (ball_subset_ball hab)
    rw [hsS _ (mem_univ _), hsS₀ _ (mem_univ _),
      ← Submission.dimred_cs_psd_radial_support (Module.finrank ℝ L) _ hmono]
    exact forall₂_congr fun ε hε => by rw [hball t ht y hy ε hε]
  · -- a density `a` of `S₀` at `y` is a density of `S` at `t + y`
    have key : ∀ a : ℝ, HasMassDensity S₀ y a → HasMassDensity S (t + y) a := by
      rintro a ⟨ha, hlim⟩
      refine ⟨ha, ?_⟩
      have h0 : Tendsto (fun r : ℝ => R₀.measure (ball y r) /
          (unitBallVolume (n - Module.finrank ℝ L) *
            ENNReal.ofReal (r ^ (n - Module.finrank ℝ L)))) (𝓝[>] 0) (𝓝 (ENNReal.ofReal a)) :=
        hlim.congr fun r => by rw [hmS₀ _ isOpen_ball (subset_univ _)]
      have h1 := Submission.dimred_cs_psd_radial_density (Module.finrank ℝ L)
        (n - Module.finrank ℝ L) (fun r => R₀.measure (ball y r)) _ (by simp) h0
      rw [Nat.add_sub_of_le hdn.le] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      rw [hmS _ isOpen_ball (subset_univ _), hball t ht y hy ρ hρ]
    refine ⟨fun h => ?_, key θ⟩
    -- `S₀` has a density `Θ₀` at `y`, which is also one of `S` at `t + y`; densities are unique,
    -- as limits along `𝓝[>] 0` are unique and `ofReal` is injective on `[0, ∞)`
    obtain ⟨Θ₀, hΘ₀⟩ := hdens y hy
    have hS := key Θ₀ hΘ₀
    rwa [(ENNReal.ofReal_eq_ofReal_iff h.1 hS.1).1 (tendsto_nhds_unique h.2 hS.2)]

/-- **Simon 7.3.1, footnote 2** (orthogonal projection onto a subspace does not increase area).
If `T ∈ 𝒟ₘ(ℝᴾ)`, `m ≥ 1`, is minimizing in the subspace `V` and `spt T ⊆ V`, then `T` is
minimizing in `ℝᴾ`.  Let `q` be the orthogonal projection onto `V`, so `μ_T` lives on `V`.  For a
competitor `S` with `K' = spt(S − T) ⊆ W` compact, `S'' := T + q_#(S − T)` is integer
multiplicity, `∂S'' = ∂T` and `spt(S'' − T) ⊆ q(K') ⊆ V ∩ W*` for the window
`W* = q⁻¹(q(W)) ∩ {x : |x − qx| < 1}`, which is open with compact closure.  Minimality in `V` and
`|Λₘq ξ| ≤ 1` give `μ_T(W*) ≤ M_{W*}(S'') ≤ μ_S(q⁻¹(q(W)))`.  As `μ_S = μ_T` off `K'`, `μ_T` lives
on `V` and `W ⊆ q⁻¹(q(W))`, cancelling the finite term `μ_T(q⁻¹(q(W)) ∖ W)` leaves
`M_W(T) = μ_T(W) ≤ μ_S(W) = M_W(S)`. -/
theorem Submission.idtp_fons_cs_minimizing_of_minimizing_in_subspace : ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) m) (V : Submodule ℝ (Euclid P)), 0 < m → IsMinimizingIn T (V : Set (Euclid P)) → T.support ⊆ (V : Set (Euclid P)) → IsMinimizingIn T univ := by
  intro P m T V hm hTV hTsptV
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  set q : Euclid P →L[ℝ] Euclid P := V.starProjection with hq
  -- `q ∘ q = q`, as `q` takes values in `V` and fixes `V`
  have hqq : ∀ x, q (q x) = q x := fun x =>
    V.starProjection_eq_self_iff.2 (V.starProjection_apply_mem x)
  -- Step 1: `μ_T(ℝᴾ ∖ V) = 0`, since `spt μ_T = spt T ⊆ V`
  obtain ⟨RT, hRT⟩ := hTV.1
  have hmsT :=
    Submission.dor_imrep_massOn_eq_measure_and_support P (k + 1) univ T RT isOpen_univ hRT
  have hTV0 : RT.measure ((V : Set (Euclid P))ᶜ) = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hx => hTsptV ?_)
      (Measure.measure_compl_support (μ := RT.measure))
    rw [hmsT.2]
    exact ⟨mem_univ x, hx⟩
  refine ⟨⟨RT, hRT⟩, ?_⟩
  intro W S hW hWc hS hbd hKc hKW
  -- Step 2: `X := S − T` is integer multiplicity, with compact support `K' ⊆ W` carrying `μ_X`
  set X : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1) := S - T with hX
  obtain ⟨RX, hRX⟩ := Submission.dtc_isIntegerMultiplicity_sub P (k + 1) univ S T isOpen_univ
    (Nat.succ_pos k) hS ⟨RT, hRT⟩
  set K' : Set (Euclid P) := X.support with hK'
  have hX0 : RX.measure K'ᶜ = 0 := by
    rw [hK', (Submission.dor_imrep_massOn_eq_measure_and_support P (k + 1) univ X RX isOpen_univ
      hRX).2, univ_inter]
    exact Measure.measure_compl_support
  have hK'W : K' ⊆ W := fun x hx => (hKW hx).2
  have hXbd : X.boundary = 0 := by
    have hbd' : S.boundary = T.boundary := hbd
    ext ω
    have h1 := congrArg (fun Z : GeometricCurrentOn (univ : Set (Euclid P)) k => Z ω) hbd'
    simp only [GeometricCurrentOn.boundary_apply] at h1
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply]
    show S _ - T _ = 0
    rw [h1, sub_self]
  -- the push-forward `Y := q_#X`, with `Y(ω) = ∫ ⟨q^#ω, ξ_X⟩ dμ_X`
  obtain ⟨push, hpush, -⟩ := Submission.dtc_bc_lc_pushforward P k univ (q : Euclid P → Euclid P)
    isOpen_univ q.contDiff.contDiffOn
  obtain ⟨hYform, hYim, hYspt, -, hYbd⟩ := hpush X RX hRX hKc (subset_univ _)
  set Y : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1) := push X with hY
  have hYact : ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1),
      Y ω = RX.action (affinePullbackForm q 0 (ω : DifferentialForm (Euclid P) (k + 1))) := by
    intro ω
    rw [hYform ω, IMRep.action]
    simp only [affinePullbackForm, zero_add, ContinuousLinearMap.fderiv]
  -- the competitor `S'' := T − ((Y − Y) − Y) = T + q_#(S − T)`
  set S'' : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1) := T - ((Y - Y) - Y) with hS''
  have hS''app : ∀ ω, S'' ω = T ω + Y ω := by
    intro ω
    show T ω - ((Y ω - Y ω) - Y ω) = T ω + Y ω
    ring
  have hS''im : IsIntegerMultiplicity S'' := by
    have h1 := Submission.dtc_isIntegerMultiplicity_sub P (k + 1) univ Y Y isOpen_univ
      (Nat.succ_pos k) hYim hYim
    have h2 := Submission.dtc_isIntegerMultiplicity_sub P (k + 1) univ (Y - Y) Y isOpen_univ
      (Nat.succ_pos k) h1 hYim
    exact Submission.dtc_isIntegerMultiplicity_sub P (k + 1) univ T ((Y - Y) - Y) isOpen_univ
      (Nat.succ_pos k) ⟨RT, hRT⟩ h2
  have hS''bd : SameBoundary S'' T := by
    show S''.boundary = T.boundary
    ext ω
    have hY0 := congrArg (fun Z : GeometricCurrentOn (univ : Set (Euclid P)) k => Z ω) (hYbd hXbd)
    simp only [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply] at hY0
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hS''app, hY0,
      add_zero]
  have hS''T : S'' - T = Y := by
    ext ω
    show S'' ω - T ω = Y ω
    rw [hS''app]
    ring
  have hS''Tc : IsCompact (S'' - T).support := by
    rw [hS''T]
    exact (hKc.image q.continuous).of_isClosed_subset (isClosed_univ.sdiff Y.isOpen_zeroRegion)
      hYspt
  -- Step 3: the window `W* := q⁻¹(q(W)) ∩ {x : |x − q x| < 1}`
  set A' : Set (Euclid P) := q ⁻¹' (q '' W) with hA'
  have hA'open : IsOpen A' := by
    have hA'eq : A' = ⋃ v ∈ {v : Euclid P | q v = 0}, (fun x => x + v) ⁻¹' W := by
      ext x
      simp only [hA', mem_preimage, mem_image, mem_iUnion, mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨w, hw, hwx⟩
        exact ⟨w - x, by rw [map_sub, hwx, sub_self], by simpa using hw⟩
      · rintro ⟨v, hv, hxv⟩
        exact ⟨x + v, hxv, by rw [map_add, hv, add_zero]⟩
    rw [hA'eq]
    exact isOpen_biUnion fun v _ => hW.preimage (continuous_id.add continuous_const)
  have hWA' : W ⊆ A' := fun w hw => ⟨w, hw, rfl⟩
  set Wst : Set (Euclid P) := A' ∩ {x | ‖x - q x‖ < 1} with hWst
  have hWst_open : IsOpen Wst :=
    hA'open.inter (isOpen_lt (continuous_id.sub q.continuous).norm continuous_const)
  obtain ⟨R₀, hR₀⟩ := (hWc.1.isBounded.subset subset_closure).subset_closedBall (0 : Euclid P)
  have hWst_ball : Wst ⊆ closedBall (0 : Euclid P) (R₀ + 1) := by
    rintro x ⟨⟨w, hw, hwx⟩, hx1⟩
    have hx1' : ‖x - q x‖ < 1 := hx1
    have hqx : ‖q x‖ ≤ R₀ := by
      rw [← hwx]
      exact (V.norm_starProjection_apply_le w).trans (mem_closedBall_zero_iff.1 (hR₀ hw))
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖(x - q x) + q x‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - q x‖ + ‖q x‖ := norm_add_le _ _
      _ ≤ R₀ + 1 := by linarith
  have hWst_cc : CompactlyContained Wst univ :=
    ⟨(isCompact_closedBall (0 : Euclid P) (R₀ + 1)).of_isClosed_subset isClosed_closure
      (closure_minimal hWst_ball isClosed_closedBall), subset_univ _⟩
  have hS''Tsub : (S'' - T).support ⊆ (V : Set (Euclid P)) ∩ Wst := by
    rw [hS''T]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hYspt hx
    refine ⟨V.starProjection_apply_mem y, ⟨y, hK'W hy, (hqq y).symm⟩, ?_⟩
    show ‖q y - q (q y)‖ < 1
    rw [hqq, sub_self, norm_zero]
    exact one_pos
  -- minimality of `T` in `V`: `M_{W*}(T) ≤ M_{W*}(S'')`
  have hmin := hTV.2 Wst S'' hWst_open hWst_cc hS''im hS''bd hS''Tc hS''Tsub
  -- Step 4: projection does not increase mass, `M_{W*}(S'') ≤ μ_S(q⁻¹(W*))`
  obtain ⟨R, hRact, hRmass⟩ := Submission.idtp_fons_cs_sp_projected_massOn_le P (k + 1) T X S''
    RT RX V K' hRT hRX hTV0 hKc hX0 (fun ω => by rw [hS''app, hYact])
  have hRS : R.Represents S := by
    intro ω
    rw [hRact ω]
    show S ω = T ω + (S ω - T ω)
    ring
  have hpre : q ⁻¹' Wst = A' := by
    ext x
    constructor
    · rintro ⟨hx, -⟩
      show q x ∈ q '' W
      rw [← hqq x]
      exact hx
    · intro hx
      refine ⟨?_, ?_⟩
      · show q (q x) ∈ q '' W
        rw [hqq x]
        exact hx
      · show ‖q x - q (q x)‖ < 1
        rw [hqq, sub_self, norm_zero]
        exact one_pos
  -- Step 5: `μ_S = μ_T` off `K'`, `μ_T` lives on `V`, and the common finite term cancels
  have hloc := Submission.idtp_fons_cs_sp_measure_restrict_eq_of_agree P (k + 1) S T R RT K'ᶜ
    hKc.isClosed.isOpen_compl hRS hRT (fun ω hω => by
      have h0 := Submission.dtc_vanish_off_support P (k + 1) univ X ω
        ((disjoint_compl_left (a := K')).mono_left hω)
      have hXω : X ω = S ω - T ω := rfl
      linarith)
  have hmsS := Submission.dor_imrep_massOn_eq_measure_and_support P (k + 1) univ S R isOpen_univ hRS
  have hA'V : A' ∩ (V : Set (Euclid P)) = Wst ∩ V := by
    ext x
    constructor
    · rintro ⟨hxA, hxV⟩
      refine ⟨⟨hxA, ?_⟩, hxV⟩
      show ‖x - q x‖ < 1
      rw [V.starProjection_eq_self_iff.2 hxV, sub_self, norm_zero]
      exact one_pos
    · rintro ⟨⟨hxA, -⟩, hxV⟩
      exact ⟨hxA, hxV⟩
  have hTA' : RT.measure A' = RT.measure Wst := by
    rw [← measure_inter_conull (s := A') hTV0, hA'V, measure_inter_conull hTV0]
  have hsub' : A' \ W ⊆ K'ᶜ := fun x hx hxK => hx.2 (hK'W hxK)
  have hSA'W : R.measure (A' \ W) = RT.measure (A' \ W) := by
    rw [← Measure.restrict_eq_self (μ := R.measure) hsub', hloc,
      Measure.restrict_eq_self (μ := RT.measure) hsub']
  have hfin : RT.measure (A' \ W) ≠ ∞ := by
    have hC : RT.measure (closure Wst) ≠ ∞ := by
      rw [IMRep.measure, withDensity_apply _ isClosed_closure.measurableSet,
        Measure.restrict_restrict isClosed_closure.measurableSet, inter_comm]
      exact RT.locallyIntegrable_mult _ hWst_cc.1 (subset_univ _)
    refine ne_top_of_le_ne_top hC ?_
    calc RT.measure (A' \ W) ≤ RT.measure A' := measure_mono sdiff_subset
      _ = RT.measure Wst := hTA'
      _ ≤ RT.measure (closure Wst) := measure_mono subset_closure
  rw [hmsT.1 W hW, hmsS.1 W hW]
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc RT.measure W + RT.measure (A' \ W) = RT.measure A' := by
        rw [measure_add_sdiff hW.measurableSet.nullMeasurableSet,
          union_eq_self_of_subset_left hWA']
    _ = RT.measure Wst := hTA'
    _ = T.massOn Wst := (hmsT.1 Wst hWst_open).symm
    _ ≤ S''.massOn Wst := hmin
    _ ≤ R.measure (q ⁻¹' Wst) := hRmass Wst
    _ = R.measure A' := by rw [hpre]
    _ ≤ R.measure (W ∪ (A' \ W)) := measure_mono fun x hx => by
        by_cases hxW : x ∈ W
        · exact Or.inl hxW
        · exact Or.inr ⟨hx, hxW⟩
    _ ≤ R.measure W + R.measure (A' \ W) := measure_union_le _ _
    _ = R.measure W + RT.measure (A' \ W) := by rw [hSA'W]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
