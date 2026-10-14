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
/-- **Triangle inequality for local mass** (Simon 6.2.5).  If `|c| ≤ 1` and
`Z(ω) = X(ω) + c Y(ω)` for every `ω ∈ 𝒟ᵏ(U)` with `spt ω ⊆ G`, then
`M_G(Z) ≤ M_G(X) + M_G(Y)`.  For `ω` admissible for `M_G`, `−ω` is admissible too, so
`|Y(ω)| ≤ M_G(Y)`; since `c Y(ω) ≤ |Y(ω)|`, `Z(ω) ≤ X(ω) + |Y(ω)| ≤ M_G(X) + M_G(Y)`.  Taking the
supremum over admissible `ω` gives the claim (`c = ±1`: sum and difference). -/
theorem Submission.lcmp_massOn_le_add_of_eval_eq : ∀ (P k : ℕ) (U G : Set (Euclid P)) (X Y Z : GeometricCurrentOn U k) (c : ℝ), |c| ≤ 1 → (∀ ω : TestFormOn U k, tsupport (ω : DifferentialForm (Euclid P) k) ⊆ G → Z ω = X ω + c * Y ω) → Z.massOn G ≤ X.massOn G + Y.massOn G := by
  intro P k U G X Y Z c hc hZ
  -- Step 4: `M_G(Z)` is a supremum, so bound each admissible value `ofReal (Z ω)`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- Step 1: `−ω` is admissible (same support, same Euclidean coefficient norm)
  have hneg : -ω ∈ massAdmissibleOn U k G := by
    refine ⟨?_, fun x => ?_⟩
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) =
          -(ω : DifferentialForm (Euclid P) k) := rfl
      rw [hco, tsupport_neg]
      exact hω.1
    · have hco : ((-ω : TestFormOn U k) : DifferentialForm (Euclid P) k) x =
          -((ω : DifferentialForm (Euclid P) k) x) := rfl
      rw [hco, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 2: `ofReal (X ω) ≤ M_G(X)` and, as `Y(−ω) = −Y(ω)`, `ofReal |Y(ω)| ≤ M_G(Y)`
  have hXle : ENNReal.ofReal (X ω) ≤ X.massOn G := X.le_massOn hω
  have hYle : ENNReal.ofReal (Y ω) ≤ Y.massOn G := Y.le_massOn hω
  have hYle' : ENNReal.ofReal (Y (-ω)) ≤ Y.massOn G := Y.le_massOn hneg
  have hYneg : Y (-ω) = -Y ω := map_neg Y.toCurrent ω
  rw [hYneg] at hYle'
  have habs : ENNReal.ofReal |Y ω| ≤ Y.massOn G := by
    rcases abs_cases (Y ω) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hYle
    · rw [h]; exact hYle'
  -- Step 3: `c Y(ω) ≤ |c| |Y(ω)| ≤ |Y(ω)|`; `ofReal` is monotone and subadditive
  have hcy : c * Y ω ≤ |Y ω| :=
    calc c * Y ω ≤ |c * Y ω| := le_abs_self _
      _ = |c| * |Y ω| := abs_mul _ _
      _ ≤ 1 * |Y ω| := by gcongr
      _ = |Y ω| := one_mul _
  show ENNReal.ofReal (Z ω) ≤ X.massOn G + Y.massOn G
  calc ENNReal.ofReal (Z ω) = ENNReal.ofReal (X ω + c * Y ω) := by rw [hZ ω hω.1]
    _ ≤ ENNReal.ofReal (X ω + |Y ω|) := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (X ω) + ENNReal.ofReal |Y ω| := ENNReal.ofReal_add_le
    _ ≤ X.massOn G + Y.massOn G := add_le_add hXle habs
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
/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors
(alternating maps agreeing on distinct basis vectors are equal), so
`Φ α = (α(e ∘ I))_{I : Fin n → Fin P}` is an injective linear map into the finite-dimensional
space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.lcn_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `Φ α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `Φ α = Φ β` makes `α` and `β` agree on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective Φ fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then for every
`n`-covector `α`, `⟨α, ξ⟩ = 0` `Hⁿ`-a.e. on `M ∩ W`.  Let `ν = Hⁿ⌞(M ∩ closure W)`; then
`f = θ ⟨α, ξ⟩` is `ν`-integrable (`lcn_mult_mul_orient_apply_integrableOn`, `closure W` being a
compact subset of `U`).  For smooth `g` with compact support in `W`, `ω = g α` is a test form in
`U` supported in `W`, so `0 = T(ω) = ∫_M θ ⟨g α, ξ⟩ dHⁿ = ∫ g f dν` (`g = 0` off `W`).  The
fundamental lemma of the calculus of variations on `W` gives `f = 0` `ν`-a.e. on `W`; as
`Hⁿ⌞(M ∩ W) ≤ ν` and `θ > 0` on `M`, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. -/
theorem Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW α
  -- `f = θ ⟨α, ξ⟩` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
  have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ closure W)) :=
    Submission.lcn_mult_mul_orient_apply_integrableOn P n U (closure W) R hWc hWU α
  -- fundamental lemma on the open set `W`: `f = 0` `ν`-a.e. on `W`
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ closure W)), x ∈ W →
      (R.mult x : ℝ) * R.orient x α = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
    -- `ω = g α` is a test form in `U` supported in `W`, so `T(ω) = 0`
    have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
    have hω : (fun x => g x • α) ∈ TestFormOn U n :=
      ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
    calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[n].restrict (R.carrier ∩ closure W))
        = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          congr 1
          funext x
          rw [map_smul, smul_eq_mul, smul_eq_mul]
          ring
      -- `g = 0` off `closure W`, so the integral over `M` is the integral over `M ∩ closure W`
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
            inter_subset_left fun x hx => ?_).symm
          have hgx : g x = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩
          rw [hgx, zero_smul, map_zero, mul_zero]
      _ = T ⟨_, hω⟩ := (hRT ⟨_, hω⟩).symm
      _ = 0 := hTW ⟨_, hω⟩ hωW
  -- pass to `Hⁿ⌞(M ∩ W) ≤ ν` and cancel `θ > 0` on `M`
  have hle : μHE[n].restrict (R.carrier ∩ W) ≤ μHE[n].restrict (R.carrier ∩ closure W) :=
    Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
  filter_upwards [ae_mono hle hae,
    ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)] with x hx hxMW
  have hθ : (R.mult x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne'
  exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left hθ

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then
`Hⁿ(M ∩ W) = 0`.  `Λⁿ` is finite-dimensional (`lcn_covector_finiteDimensional`); for each `α` of
a basis, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. (`lcn_orient_apply_ae_eq_zero_of_vanishesOn`), so
`ξ = 0` `Hⁿ⌞(M ∩ W)`-a.e.  But `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, hence nonzero
(`imsupp_unit_orientation_ne_zero_norm_le_one`), so `Hⁿ⌞(M ∩ W) = 0`. -/
theorem Submission.imrep_carrier_inter_null_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μHE[n] (R.carrier ∩ W) = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ`
  have := Submission.lcn_covector_finiteDimensional P n
  let b := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `⟨αₖ, ξ⟩ = 0` for every `k`, `Hⁿ⌞(M ∩ W)`-a.e.
  have h0 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ k, R.orient x (b k) = 0 :=
    ae_all_iff.mpr fun k =>
      Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWc hWU hTW (b k)
  -- `ξ ≠ 0` `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ W)`-a.e.
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x ≠ 0 := by
    refine ae_mono (Measure.restrict_mono inter_subset_left le_rfl) ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a functional on `Λⁿ` vanishing on a basis is zero, so `Hⁿ⌞(M ∩ W)`-a.e. `x` is impossible
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), False := by
    filter_upwards [h0, h1] with x hx hne
    exact hne (ContinuousLinearMap.coe_injective (b.ext fun k => hx k))
  exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` in `U`, then `Hⁿ(M ∖ spt T) = 0`, i.e.
`μ_T(U ∖ spt T) = 0`.  As `M ⊆ U` and `spt T = U ∖ Z`, `M ∖ spt T ⊆ M ∩ Z`, where the zero region
`Z = ⋃ 𝒲` is the union of the open `W ⊂⊂ U` on which `T` vanishes.  `ℝᴾ` is second countable, so
`Z = ⋃_{W ∈ 𝒮} W` for a countable `𝒮 ⊆ 𝒲`; each `Hⁿ(M ∩ W) = 0`
(`imrep_carrier_inter_null_of_vanishesOn`), and countable subadditivity concludes. -/
theorem Submission.imrep_carrier_sdiff_support_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
  intro P n U T R _ hRT
  -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
  obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- `M ∖ spt T ⊆ ⋃_{W ∈ 𝒮} M ∩ W`: a point of `M ⊆ U` outside `spt T = U ∖ Z` lies in `Z`
  have hsub : R.carrier \ T.support ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
    rintro x ⟨hxM, hxS⟩
    have hxZ : x ∈ ⋃₀ 𝒮 := by
      rw [h𝒮]
      by_contra hxZ
      exact hxS (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
    exact mem_biUnion hW ⟨hxM, hxW⟩
  -- `Hⁿ(M ∩ W) = 0` for each of the countably many `W ∈ 𝒮`
  refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
  obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
  exact Submission.imrep_carrier_inter_null_of_vanishesOn P n U W T R hRT hWo hWc hWU hTW
/-- **Simon Ch. 3, 1.4**: approximate tangent planes are local and do not see `Hⁿ`-null
modifications.  If `M' ⊆ M`, `V` is open, `x ∈ V` and `Hⁿ((M \ M') ∩ V) = 0`, then an
approximate tangent plane of `M` at `x` is one of `M'`.  Given `f ∈ C_c(ℝᴾ)`, take
`B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`.  For `0 < r < s / L` the parts of `η_{x,r}(M)` and
`η_{x,r}(M')` in `B_L(0)` differ inside `η_{x,r}((M \ M') ∩ V)`, which is `Hⁿ`-null because
`η_{x,r}` is Lipschitz.  So the blow-up integrals agree for small `r` and have the same limit. -/
theorem Submission.dtc_approxTangent_of_null_diff : ∀ (P n : ℕ) (M M' V : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), M' ⊆ M → IsOpen V → x ∈ V → μHE[n] ((M \ M') ∩ V) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' V x Q hMM' hV hxV hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `B_s(x) ⊆ V` and `spt f ⊆ B_L(0)`
  obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.mp hV x hxV
  obtain ⟨L, hL, hfL⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 0
  -- the blow-up integrals of `M` and `M'` agree for `0 < r < s / L`, so they have the same limit
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
  have hr0 : 0 < r := hr.1
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη]
  -- `f` vanishes off `B_L(0)`, so every set integral may be cut to `B_L(0)`
  have hfB : ∀ y, y ∉ ball (0 : Euclid P) L → f y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hfL h)
  have hcut : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) L ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hfB).symm
  -- `η_{x,r}` is `r⁻¹`-Lipschitz, so it maps the `Hⁿ`-null set `(M \ M') ∩ V` to a null set
  have hnullimg : μHE[n] ((fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V)) = 0 := by
    have hlip : LipschitzWith ‖r⁻¹‖₊ (fun y : Euclid P => r⁻¹ • (y - x)) :=
      LipschitzWith.of_dist_le_mul fun a b =>
        le_of_eq (by rw [dist_smul₀, dist_sub_right, coe_nnnorm])
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul] at hnull ⊢
    have hH : μH[(n : ℝ)] ((M \ M') ∩ V) = 0 := by
      simpa [Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n] using hnull
    have hle := hlip.hausdorffMeasure_image_le (Nat.cast_nonneg n) ((M \ M') ∩ V)
    rw [hH, mul_zero, nonpos_iff_eq_zero] at hle
    rw [hle, mul_zero]
  -- in `B_L(0)`, `η_{x,r}(M)` and `η_{x,r}(M')` differ inside `η_{x,r}((M \ M') ∩ V)`
  have hsub : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) \
      (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M') ⊆
      (fun y : Euclid P => r⁻¹ • (y - x)) '' ((M \ M') ∩ V) := by
    rintro y ⟨⟨hyB, ⟨z, hz, rfl⟩⟩, hy'⟩
    refine ⟨z, ⟨⟨hz, fun hz' => hy' ⟨hyB, z, hz', rfl⟩⟩, hsV ?_⟩, rfl⟩
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le,
      inv_mul_lt_iff₀ hr0] at hyB
    have hrL := (lt_div_iff₀ hL).mp hr.2
    rw [mem_ball, dist_eq_norm]
    linarith
  -- hence the two parts are `Hⁿ`-a.e. equal (`M' ⊆ M` gives the other inclusion)
  have hae : (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M' : Set (Euclid P))
      =ᵐ[μHE[n]] (ball (0 : Euclid P) L ∩ (fun y : Euclid P => r⁻¹ • (y - x)) '' M) := by
    rw [ae_eq_set]
    constructor
    · rw [sdiff_eq_empty.mpr (inter_subset_inter_right _ (image_mono hMM'))]
      exact measure_empty
    · exact measure_mono_null hsub hnullimg
  rw [hcut, hcut ((fun y : Euclid P => r⁻¹ • (y - x)) '' M'), Measure.restrict_congr_set hae]
/-- **`∫_Q g dHⁿ > 0` for a nonnegative `C_c` function `g` with `g(w) > 0` at a point `w` of an
`n`-plane `Q`** (step 4 of the proof that approximate tangent planes of a submanifold lie in its
tangent spaces; Simon Ch. 3, 1.4).  `Hⁿ⌞Q` is regular with support `Q` (SimonGMT Ch. 3), so `g` is
`Hⁿ⌞Q`-integrable and the open set `{g ≠ 0} ∋ w` has positive `Hⁿ⌞Q`-measure. -/
theorem Submission.dsmc_att_setIntegral_submodule_pos : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (g : Euclid P → ℝ) (w : Euclid P), Module.finrank ℝ Q = n → Continuous g → HasCompactSupport g → (∀ y, 0 ≤ g y) → w ∈ Q → 0 < g w → 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
  intro P n Q g w hQ hg hgc hg0 hw hgw
  -- `Hⁿ⌞Q` is regular, hence finite on compact sets, so the `C_c` function `g` is integrable.
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ
  rw [integral_pos_iff_support_of_nonneg hg0 (hg.integrable_of_hasCompactSupport hgc)]
  -- `w ∈ Q = spt(Hⁿ⌞Q)` and `{g ≠ 0}` is an open neighbourhood of `w`.
  have hwμ : w ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
    rwa [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ]
  exact (Measure.mem_support_iff_forall _).1 hwμ _ (hg.isOpen_support.mem_nhds hgw.ne')
/-- Blow-up maps preserve `Hⁿ`-null sets: if `λ ≠ 0` and `Hⁿ(E) = 0`, then `Hⁿ(η_{x,λ}(E)) = 0`.
Since `η_{x,λ}(E) = λ⁻¹ · (E − x)`, the translation `y ↦ y − x` is an isometry (so
`Hⁿ(E − x) = Hⁿ(E) = 0`) and the dilation by `λ⁻¹ ≠ 0` multiplies `Hⁿ` by `|λ⁻¹|ⁿ`. -/
theorem Submission.dsmc_att_blowUpMap_image_null : ∀ (P n : ℕ) (E : Set (Euclid P)) (x : Euclid P) (lam : ℝ), lam ≠ 0 → μHE[n] E = 0 → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E) = 0 := by
  intro P n E x lam hlam hE
  -- Step 1: `η_{x,λ}(E) = λ⁻¹ · τ(E)`, where `τ y = y − x`
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E =
      (fun z : Euclid P => lam⁻¹ • z) '' ((fun y : Euclid P => y - x) '' E) := by
    rw [Set.image_image]
    rfl
  -- Step 2: `τ` is an isometry, so `Hⁿ(τ(E)) = Hⁿ(E) = 0`
  have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
  have htrans : μHE[n] ((fun y : Euclid P => y - x) '' E) = 0 := by
    rw [hτ.euclideanHausdorffMeasure_image, hE]
  -- Steps 3–4: `Hⁿ(λ⁻¹ · τ(E)) = ‖λ⁻¹‖₊ⁿ • Hⁿ(τ(E)) = 0`
  rw [himage, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam), htrans,
    smul_zero]

/-- **Blow-ups of `M ∩ N` approach every vector of an approximate tangent space** (Simon Ch. 3,
Definition 1.4, chapter-03.txt lines 77–83, tested as in Remark 1.5(3), lines 90–92).  If
`Hⁿ(M \ N) = 0`, `Q` is an approximate tangent space of `M` at `x`, `w ∈ Q` and `s > 0`, then for
all small `λ > 0` some `y ∈ M ∩ N` has `|λ⁻¹(y − x) − w| < s`.  The tent `f = max(0, s − |· − w|)`
lies in `C_c`, vanishes off `B_s(w)` and has `∫_Q f dHⁿ > 0`, so `∫_{η_{x,λ}(M)} f dHⁿ > 0` for
small `λ`; hence `Hⁿ(η_{x,λ}(M) ∩ B_s(w)) ≠ 0`, and since `η_{x,λ}(M \ N)` is `Hⁿ`-null,
`η_{x,λ}(M ∩ N)` meets `B_s(w)`. -/
theorem Submission.dsmc_att_blowUp_points_of_approxTangent : ∀ (P n : ℕ) (M N : Set (Euclid P)) (x w : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → w ∈ Q → ∀ s : ℝ, 0 < s → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ y ∈ M ∩ N, ‖lam⁻¹ • (y - x) - w‖ < s := by
  intro P n M N x w Q hMN hQ hw s hs
  -- the tent `g = max(0, s − |· − w|)`: continuous, `g ≥ 0`, `g(w) = s` and `{g ≠ 0} ⊆ B_s(w)`
  set g : Euclid P → ℝ := fun y => max 0 (s - ‖y - w‖)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y => le_max_left _ _
  have hg_ball : ∀ y, g y ≠ 0 → y ∈ ball w s := by
    intro y hy
    rw [mem_ball, dist_eq_norm]
    by_contra h
    exact hy (max_eq_left (by linarith [not_lt.mp h]))
  have hg_supp : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall w s) fun y hy =>
      not_not.mp fun h => hy (ball_subset_closedBall (hg_ball y h))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_supp⟩
  -- `∫_Q f dHⁿ > 0`, hence `∫_{η_{x,λ}(M)} f dHⁿ > 0` for every `λ ∈ (0, λ₀)`
  have hI : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] :=
    Submission.dsmc_att_setIntegral_submodule_pos P n Q g w hQ.1 hg_cont hg_supp hg_nonneg hw
      (by simp [g, hs])
  obtain ⟨lam₀, hlam₀, hpos⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp ((hQ.2 f).eventually (lt_mem_nhds hI))
  refine ⟨lam₀, hlam₀, fun lam hlam hlam₀' => ?_⟩
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x lam with hη
  -- a positive integral of `f` over `η(M)` forces `Hⁿ(η(M) ∩ B_s(w)) ≠ 0`
  have hball : μHE[n] (η '' M ∩ ball w s) ≠ 0 := by
    intro h0
    have hF : 0 < ∫ y in η '' M, f y ∂μHE[n] := hpos ⟨hlam, hlam₀'⟩
    have hF0 : ∫ y in η '' M, f y ∂μHE[n] = 0 := by
      apply integral_eq_zero_of_ae
      rw [EventuallyEq, ae_iff]
      refine measure_mono_null (fun y hy => hg_ball y hy) ?_
      rw [Measure.restrict_apply measurableSet_ball, inter_comm]
      exact h0
    exact hF.ne' hF0
  -- `η(M \ N)` is `Hⁿ`-null and `η(M) ∩ B_s(w) ⊆ (η(M ∩ N) ∩ B_s(w)) ∪ η(M \ N)`
  have hnull : μHE[n] (η '' (M \ N)) = 0 :=
    Submission.dsmc_att_blowUpMap_image_null P n (M \ N) x lam hlam.ne' hMN
  have hcov : η '' M ∩ ball w s ⊆ (η '' (M ∩ N) ∩ ball w s) ∪ η '' (M \ N) := by
    rintro z ⟨⟨y, hyM, rfl⟩, hz⟩
    by_cases hyN : y ∈ N
    · exact Or.inl ⟨⟨y, ⟨hyM, hyN⟩, rfl⟩, hz⟩
    · exact Or.inr ⟨y, ⟨hyM, hyN⟩, rfl⟩
  have hne : μHE[n] (η '' (M ∩ N) ∩ ball w s) ≠ 0 := fun h0 =>
    hball (measure_mono_null hcov (measure_union_null h0 hnull))
  -- so `η(M ∩ N)` meets `B_s(w)`
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := nonempty_of_measure_ne_zero hne
  refine ⟨y, hy, ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  simpa [hη, Poincare.SimonGMT.Chapter03.blowUpMap] using hz

/-- **`Df(x)` fixes the approximate tangent space of a pointwise fixed set** (steps 5–6 of the proof
that a map fixing `spt T` preserves the orientation of `T`; approximate tangent spaces as in Simon
Ch. 3, Definition 1.4).  If `f` is differentiable at `x`, `f(x) = x`, `f` fixes every point of `A`
and `Q` is an approximate tangent space of `A` at `x`, then `Df(x)v = v` for every `v ∈ Q`.  The
blow-up points `u = λ⁻¹(y − x)`, `y ∈ A`, approach `v` as `λ ↓ 0`; since `f(y) − f(x) = y − x`,
differentiability gives `|u − Df(x)u| ≤ η|u|`, so `|Df(x)v − v| ≤ ε` for every `ε > 0`. -/
theorem Submission.dtc_bc_lc_fderiv_apply_eq_of_approxTangent : ∀ (P n : ℕ) (A : Set (Euclid P)) (f : Euclid P → Euclid P) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), HasApproximateTangentSpaceAt n A x Q → DifferentiableAt ℝ f x → f x = x → (∀ y ∈ A, f y = y) → ∀ v ∈ Q, fderiv ℝ f x v = v := by
  intro P n A f x Q hQ hf hfx hA v hv
  set L := fderiv ℝ f x
  have hfL : HasFDerivAt f L x := hf.hasFDerivAt
  -- Step 1: it suffices to show `|Lv − v| ≤ ε` for every `ε > 0`; fix the constants
  refine eq_of_forall_dist_le fun ε hε => ?_
  rw [dist_eq_norm]
  set C : ℝ := ‖v‖ + 1 with hC
  set K : ℝ := ‖L‖ + 1 with hK
  have hCpos : 0 < C := by rw [hC]; positivity
  have hKpos : 0 < K := by rw [hK]; positivity
  set η : ℝ := ε / (2 * C) with hη
  set s : ℝ := min 1 (ε / (2 * K))
  have hηpos : 0 < η := div_pos hε (mul_pos two_pos hCpos)
  have hspos : 0 < s := lt_min one_pos (div_pos hε (mul_pos two_pos hKpos))
  have hKs : K * s ≤ ε / 2 := by
    calc K * s ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hKpos.le
      _ = ε / 2 := by field_simp
  have hηC : η * C = ε / 2 := by rw [hη]; field_simp
  -- Step 2: differentiability gives `δ > 0` with `|f(y) − f(x) − L(y − x)| ≤ η|y − x|` near `x`
  obtain ⟨δ, hδ, hδf⟩ := Metric.eventually_nhds_iff.mp (hfL.isLittleO.bound hηpos)
  -- Step 3: blow-up points of `A ∩ A = A` approach `v`
  obtain ⟨lam₀, hlam₀, hpts⟩ :=
    Submission.dsmc_att_blowUp_points_of_approxTangent P n A A x v Q (by simp) hQ hv s hspos
  -- Step 4: the scale `λ = min(λ₀/2, δ/(2C))` and the point `u = λ⁻¹(y − x)`
  set lam : ℝ := min (lam₀ / 2) (δ / (2 * C))
  have hlampos : 0 < lam := lt_min (half_pos hlam₀) (div_pos hδ (mul_pos two_pos hCpos))
  obtain ⟨y, ⟨hyA, -⟩, hy⟩ := hpts lam hlampos ((min_le_left _ _).trans_lt (half_lt_self hlam₀))
  set u : Euclid P := lam⁻¹ • (y - x) with hu
  have hyx : y - x = lam • u := by rw [hu, smul_inv_smul₀ hlampos.ne']
  have huv : ‖u - v‖ < s := hy
  have huC : ‖u‖ ≤ C := by
    have h1 := norm_le_norm_sub_add u v
    have h2 := huv.trans_le (min_le_left _ _)
    rw [hC]; linarith
  have hyδ : dist y x < δ := by
    rw [dist_eq_norm, hyx, norm_smul, Real.norm_of_nonneg hlampos.le]
    calc lam * ‖u‖ ≤ δ / (2 * C) * C :=
          mul_le_mul (min_le_right _ _) huC (norm_nonneg _) (div_pos hδ (mul_pos two_pos hCpos)).le
      _ = δ / 2 := by field_simp
      _ < δ := half_lt_self hδ
  -- Step 5: `f(y) = y` and `f(x) = x` turn the estimate into `|u − Lu| ≤ η|u| ≤ ε/2`
  have hkey : ‖u - L u‖ ≤ ε / 2 := by
    have h := hδf hyδ
    rw [hA y hyA, hfx, hyx, map_smul, ← smul_sub, norm_smul, norm_smul,
      Real.norm_of_nonneg hlampos.le, mul_left_comm] at h
    calc ‖u - L u‖ ≤ η * ‖u‖ := le_of_mul_le_mul_left h hlampos
      _ ≤ η * C := mul_le_mul_of_nonneg_left huC hηpos.le
      _ = ε / 2 := hηC
  -- Step 6: `|Lv − v| ≤ |L(v − u)| + |Lu − u| + |u − v| ≤ Ks + ε/2 ≤ ε`
  have hLvu : ‖L v - L u‖ ≤ ‖L‖ * ‖u - v‖ := by
    calc ‖L v - L u‖ = ‖L (v - u)‖ := by rw [map_sub]
      _ ≤ ‖L‖ * ‖v - u‖ := L.le_opNorm _
      _ = ‖L‖ * ‖u - v‖ := by rw [norm_sub_rev]
  calc ‖L v - v‖ = ‖(L v - L u) + (L u - u) + (u - v)‖ := by congr 1; abel
    _ ≤ ‖L v - L u‖ + ‖L u - u‖ + ‖u - v‖ := norm_add₃_le
    _ ≤ ‖L‖ * ‖u - v‖ + ε / 2 + ‖u - v‖ := by rw [norm_sub_rev (L u) u]; linarith
    _ = K * ‖u - v‖ + ε / 2 := by rw [hK]; ring
    _ ≤ K * s + ε / 2 := by linarith [mul_le_mul_of_nonneg_left huv.le hKpos.le]
    _ ≤ ε := by linarith
/-- **Simon 6.1.1, 6.1.7** (step 7 of the local comparison in the proof of 7.3.1): if `ξ` is a unit
orientation of `Q` and the continuous linear map `L` fixes `Q` pointwise, then
`⟨α ∘ ΛⁿL, ξ⟩ = ⟨α, ξ⟩` for every `n`-covector `α`.  Write `⟨β, ξ⟩ = ±β(τ₁, …, τₙ)` with `τ`
spanning `Q`; each `τᵢ ∈ Q`, so `L ∘ τ = τ` and `(α ∘ ΛⁿL)(τ) = α(L ∘ τ) = α(τ)`. -/
theorem Submission.dtc_bc_lc_unitOrientation_comp_eq : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), IsUnitOrientationOf ξ Q → (∀ v ∈ Q, L v = v) → ∀ α : Covector (Euclid P) n, ξ (α.compContinuousLinearMap L) = ξ α := by
  intro P n ξ Q L hξ hL α
  obtain ⟨τ, -, hspan, hsign⟩ := hξ
  -- each `τᵢ` lies in `Q = span (range τ)`, so `L ∘ τ = τ`
  have hLτ : ⇑L ∘ τ = τ := by
    funext i
    exact hL (τ i) (hspan ▸ Submodule.subset_span (mem_range_self i))
  -- `(α ∘ ΛⁿL)(τ) = α(L ∘ τ) = α(τ)`
  have hτ : α.compContinuousLinearMap L τ = α τ := by
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hLτ]
  rcases hsign with h | h <;> rw [h, h, hτ]

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
/-- **Simon Ch. 6, 3.1 and 2.16** (with Ch. 3, 1.4): if `T = τ(M, θ, ξ)` is integer multiplicity
in `U` and `V ⊆ U` is open, then `T⌞V = τ(M ∩ V, θ, ξ)` is integer multiplicity in `V`.  The
restricted triple inherits measurability, rectifiability, positivity and local integrability from
`(M, θ, ξ)`.  At `Hⁿ`-a.e. `x ∈ M ∩ V` the approximate tangent space of `M` is also that of
`M ∩ V`, as the removed set `M ∖ (M ∩ V)` misses the open set `V ∋ x`
(`dtc_approxTangent_of_null_diff`).  A test form supported in `V` vanishes on `M ∖ V`, so its
integrals over `M` and over `M ∩ V` agree.  Openness of `U` is not used. -/
theorem Submission.dtc_restrictDomain_isIntegerMultiplicity : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n), IsOpen V → IsIntegerMultiplicity T → IsIntegerMultiplicity (T.restrictDomain hVU) := by
  rintro P n U V hVU T hV ⟨R, hR⟩
  -- Step 1: `M ∩ V` is Borel
  have hMV : MeasurableSet (R.carrier ∩ V) := R.measurableSet_carrier.inter hV.measurableSet
  -- the restricted triple `R' = (M ∩ V, θ, ξ)` in `V`
  let R' : IMRep V n :=
    { carrier := R.carrier ∩ V
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := hMV
      -- Step 2: `M ∩ V ⊆ V`
      carrier_subset := inter_subset_right
      -- Step 3: a subset of a countably `n`-rectifiable set is countably `n`-rectifiable
      rectifiable := R.rectifiable.mono inter_subset_left
      -- Step 4: `θ` is measurable, and positive on `M ∩ V ⊆ M`
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- Step 5: for compact `K ⊆ V`, `(M ∩ V) ∩ K = M ∩ K` and `K ⊆ V ⊆ U`
      locallyIntegrable_mult := fun K hK hKV => by
        rw [inter_assoc, inter_eq_right.2 hKV]
        exact R.locallyIntegrable_mult K hK (hKV.trans hVU)
      -- Step 6: `Hⁿ⌞(M ∩ V) ≤ Hⁿ⌞M`
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
      -- Step 7: at `Hⁿ⌞(M ∩ V)`-a.e. `x`, the plane `Q` oriented by `ξ(x)` stays the approximate
      -- tangent space, since `(M ∖ (M ∩ V)) ∩ V = ∅`
      orients := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset
          (inter_subset_left : R.carrier ∩ V ⊆ R.carrier) R.orients, ae_restrict_mem hMV]
          with x hx hxMV
        obtain ⟨Q, hQ, hξQ⟩ := hx
        have hnull : μHE[n] ((R.carrier \ (R.carrier ∩ V)) ∩ V) = 0 := by
          rw [sdiff_self_inter, sdiff_inter_self, measure_empty]
        exact ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier (R.carrier ∩ V) V x Q
          inter_subset_left hV hxMV.2 hnull hQ, hξQ⟩ }
  -- Step 8: `T⌞V(ω) = T(ιω) = ∫_M θ⟨ω, ξ⟩ dHⁿ = ∫_{M ∩ V} θ⟨ω, ξ⟩ dHⁿ`, as `ω = 0` off `V`
  refine ⟨R', fun ω => ?_⟩
  rw [GeometricCurrentOn.restrictDomain_apply, hR, testFormOnInclusion_coe]
  change ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n] =
    ∫ x in R.carrier ∩ V, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
    inter_subset_left fun x hx => ?_
  have hxω : x ∉ tsupport (ω : DifferentialForm (Euclid P) n) :=
    fun h => hx.2 ⟨hx.1, ω.property.2 h⟩
  rw [image_eq_zero_of_notMem_tsupport hxω, map_zero, mul_zero]

/-- **`S⌞W` as an integer multiplicity current in `ℝᴾ`** (Simon Ch. 6, 3.1 and 2.11; the
restriction device of step 2 in the proof of 7.2.4 for minimizers in a submanifold).  Let `U` be
open, `W ⊂⊂ U` open and `S = τ(M, θ, ξ)` in `U`.  Then `Q = τ(M ∩ W, θ, ξ) ∈ 𝒟ₙ(ℝᴾ)` satisfies
`Q(ω) = S(ω)` for `ω ∈ 𝒟ⁿ(U)` with `spt ω ⊆ W`, and `spt Q ⊆ W̄ ∩ spt S` is compact.
* `(M ∩ W, θ, ξ)` is a triple in `U` (restriction to the Borel set `W`), and it is locally
  integrable in all of `ℝᴾ` because `M ∩ W` lies in the compact set `W̄ ⊆ U`.
* A form supported in `W` vanishes on `M \ W`, so its integrals over `M` and `M ∩ W` agree.
* `S` vanishes off its support, so `M_{U \ spt S}(S) = 0`; hence `θHⁿ⌞M(U \ spt S) = 0`, and as
  `θ ≥ 1` on `M ⊆ U`, `Hⁿ(M \ spt S) = 0`.
* So `Q` kills every form whose support misses the compact set `W̄ ∩ spt S`. -/
theorem Submission.dtc_bc_lc_rc_ambient_restriction : ∀ (P n : ℕ) (U W : Set (Euclid P)) (S : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → IsOpen W → CompactlyContained W U → R.Represents S → ∃ (Q : GeometricCurrentOn (univ : Set (Euclid P)) n) (RQ : IMRep (univ : Set (Euclid P)) n), RQ.Represents Q ∧ RQ.carrier = R.carrier ∩ W ∧ RQ.mult = R.mult ∧ RQ.orient = R.orient ∧ (∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → Q (testFormOnInclusion (subset_univ U) n ω) = S ω) ∧ Q.support ⊆ closure W ∩ S.support ∧ IsCompact Q.support := by
  have hIM := Submission.cmc_imRep_locality_restrict_sub
  have hM := Submission.dtc_mass_eq_measure
  have hV := Submission.dtc_vanish_off_support
  have hSV := Submission.rsd_cmr_support_subset_of_vanish
  intro P n U W S R hU hW hWU hR
  -- Step 1: the triple `(M ∩ W, θ, ξ)` in `U`
  obtain ⟨A₀, R', -, hR'c, hR'm, hR'o⟩ := hIM.2.1 P n U R W hU hW.measurableSet
  have hrect : CountablyRectifiable n (R.carrier ∩ W) := hR'c ▸ R'.rectifiable
  have hasm : AEStronglyMeasurable R.orient (μHE[n].restrict (R.carrier ∩ W)) := by
    rw [← hR'c, ← hR'o]; exact R'.aestronglyMeasurable_orient
  have hor : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (R.carrier ∩ W) x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    rw [← hR'c, ← hR'o]; exact R'.orients
  -- Step 2: the same triple in `ℝᴾ`; for compact `K`, `(M ∩ W) ∩ K ⊆ M ∩ W̄` with `W̄ ⊆ U` compact
  let R₀ : IMRep (univ : Set (Euclid P)) n :=
    { carrier := R.carrier ∩ W
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hW.measurableSet
      carrier_subset := subset_univ _
      rectifiable := hrect
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      locallyIntegrable_mult := fun K _ _ => by
        apply ne_top_of_le_ne_top (R.locallyIntegrable_mult (closure W) hWU.1 hWU.2)
        apply lintegral_mono_set
        intro x hx
        exact ⟨hx.1.1, subset_closure hx.1.2⟩
      aestronglyMeasurable_orient := hasm
      orients := hor }
  -- Step 3: the current `Q = τ(M ∩ W, θ, ξ)` in `ℝᴾ`
  obtain ⟨Q, RQ, hRQ, hRQc, hRQm, hRQo⟩ := hIM.2.1 P n univ R₀ univ isOpen_univ MeasurableSet.univ
  have hRQc' : RQ.carrier = R.carrier ∩ W := by rw [hRQc]; exact inter_univ _
  -- Step 5: `Hⁿ(M \ spt S) = 0`
  have hnull : μHE[n] (R.carrier \ S.support) = 0 := by
    -- `O = U \ spt S = U ∩ Z(S)` is open
    have hopen : IsOpen (U \ S.support) := by
      have : U \ S.support = U ∩ S.zeroRegion := by
        ext x
        simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_inter_iff, not_and, not_not]
        constructor
        · intro h; exact ⟨h.1, h.2 h.1⟩
        · intro h; exact ⟨h.1, fun _ => h.2⟩
      rw [this]
      exact hU.inter S.isOpen_zeroRegion
    -- `M_O(S) = 0`: every admissible form is supported off `spt S`
    have hmass : S.massOn (U \ S.support) = 0 := by
      apply le_zero_iff.mp
      apply sSup_le
      rintro r ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (S ω) ≤ 0
      rw [hV P n U S ω (by
        rw [← Set.subset_compl_iff_disjoint_right]
        exact hω.1.trans (fun x hx => hx.2)), ENNReal.ofReal_zero]
    -- `∫_{O ∩ M} θ dHⁿ = M_O(S) = 0`
    have hmeas : R.measure (U \ S.support) = 0 := by
      rw [← hM P n U (U \ S.support) S R hU hopen sdiff_subset hR, hmass]
    unfold IMRep.measure at hmeas
    rw [withDensity_apply _ hopen.measurableSet, Measure.restrict_restrict hopen.measurableSet] at hmeas
    -- `θ ≥ 1` on `M`
    have hle : μHE[n] ((U \ S.support) ∩ R.carrier) ≤
        ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      calc μHE[n] ((U \ S.support) ∩ R.carrier)
          = ∫⁻ x in (U \ S.support) ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
            rw [setLIntegral_const, one_mul]
        _ ≤ ∫⁻ x in (U \ S.support) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            apply setLIntegral_mono' (hopen.measurableSet.inter R.measurableSet_carrier)
            intro x hx
            have := R.mult_pos x hx.2
            exact_mod_cast this
    have h0 : μHE[n] ((U \ S.support) ∩ R.carrier) = 0 := le_zero_iff.mp (hmeas ▸ hle)
    -- `M ⊆ U`, so `M \ spt S ⊆ O ∩ M`
    apply measure_mono_null _ h0
    intro x hx
    exact ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩
  refine ⟨Q, RQ, hRQ, hRQc', hRQm, hRQo, ?_, ?_⟩
  · -- Step 4 (Q1): `ω = 0` on `M \ W`, so the integrals over `M` and `M ∩ W` agree
    intro ω hω
    rw [hRQ, hR ω]
    unfold IMRep.action
    rw [hRQc', hRQm, hRQo, testFormOnInclusion_coe]
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier inter_subset_left
    intro x hx
    have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx.2 ⟨hx.1, hω h⟩)
    simp [this]
  · -- Step 6 (Q2): `K = W̄ ∩ spt S = W̄ ∩ Z(S)ᶜ` is compact
    have hKcpt : IsCompact (closure W ∩ S.support) := by
      have : closure W ∩ S.support = closure W ∩ (S.zeroRegion)ᶜ := by
        ext x
        simp only [GeometricCurrentOn.support, mem_inter_iff, Set.mem_sdiff, mem_compl_iff]
        constructor
        · intro h; exact ⟨h.1, h.2.2⟩
        · intro h; exact ⟨h.1, hWU.2 h.1, h.2⟩
      rw [this]
      exact hWU.1.inter_right S.isOpen_zeroRegion.isClosed_compl
    -- `Hⁿ`-a.e. point of `M ∩ W` lies in `K`, where a form supported off `K` vanishes
    exact hSV P n univ (closure W ∩ S.support) Q isOpen_univ hKcpt (subset_univ _) (fun ω hω => by
      rw [hRQ ω]
      unfold IMRep.action
      rw [hRQc', hRQm, hRQo]
      apply integral_eq_zero_of_ae
      have hn' : μHE[n] ((R.carrier ∩ W) \ S.support) = 0 :=
        measure_mono_null (sdiff_subset_sdiff_left inter_subset_left) hnull
      have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), x ∈ S.support := by
        rw [ae_restrict_iff' (R.measurableSet_carrier.inter hW.measurableSet)]
        rw [ae_iff]
        apply measure_mono_null _ hn'
        intro x hx
        simp only [Set.mem_ofPred_eq, not_imp] at hx
        exact ⟨hx.1, hx.2⟩
      filter_upwards [hae, ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)]
        with x hx hxM
      have : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h =>
          hω.ne_of_mem h ⟨subset_closure hxM.2, hx⟩ rfl)
      simp [this])
/-- **Simon 7.2.4 (9)** (adding a cycle does not lower the mass of a minimizing current).  Let
`S ∈ 𝒟ₙ(U)` be minimizing in `A`, `W ⊂⊂ U` open, and `X ∈ 𝒟ₙ(ℝᴾ)` integer multiplicity with
`∂X = 0` and `spt X ⊆ K`, `K ⊆ A ∩ W` compact.  Then `M_W(S) ≤ M_W(Z)` for
`Z = S − (0 − X|_U) = S + X|_U`, an admissible competitor: `Z` is integer multiplicity
(`0 = X|_U − X|_U` and closure under differences), `∂Z = ∂S` since `X|_U(dω) = ∂X(ω) = 0`, and
`Z − S = X|_U` vanishes on forms supported off `K ⊇ spt X`, so `spt(Z − S)` is a compact subset
of `K ⊆ A ∩ W`. -/
theorem Submission.dtc_bc_lc_rc_cycle_competitor : ∀ (P m : ℕ) (U A W K : Set (Euclid P)) (S : GeometricCurrentOn U (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsOpen U → IsMinimizingIn S A → IsOpen W → CompactlyContained W U → IsIntegerMultiplicity X → X.boundary = 0 → IsCompact K → X.support ⊆ K → K ⊆ A ∩ W → S.massOn W ≤ (S - (0 - X.restrictDomain (subset_univ U))).massOn W := by
  intro P m U A W K S X hU hmin hW hWU hXim hXbd hK hXK hKAW
  have hsub := Submission.cmc_imRep_locality_restrict_sub.2.2.1 P (m + 1) U
  set XU := X.restrictDomain (subset_univ U)
  -- `X|_U`, `0 = X|_U − X|_U` and `Z = S − (0 − X|_U)` are integer multiplicity
  have hXUim : IsIntegerMultiplicity XU :=
    Submission.dtc_restrictDomain_isIntegerMultiplicity P (m + 1) univ U (subset_univ U) X hU hXim
  have h0im : IsIntegerMultiplicity (0 : GeometricCurrentOn U (m + 1)) := by
    have h0 : XU - XU = 0 := by
      ext ω
      exact sub_self (XU ω)
    have h := hsub XU XU hU hXUim hXUim
    rwa [h0] at h
  have hZim : IsIntegerMultiplicity (S - (0 - XU)) := hsub S _ hU hmin.1 (hsub 0 XU hU h0im hXUim)
  -- `∂Z = ∂S`, since `X|_U(dω) = X(d(ιω)) = ∂X(ιω) = 0`
  have hbd : SameBoundary (S - (0 - XU)) S := by
    show (S - (0 - XU)).boundary = S.boundary
    ext ω
    have hdX : XU (exteriorDerivativeTestOn U m ω) = 0 :=
      congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) m =>
        T (testFormOnInclusion (subset_univ U) m ω)) hXbd
    show S (exteriorDerivativeTestOn U m ω) - (0 - XU (exteriorDerivativeTestOn U m ω)) =
      S (exteriorDerivativeTestOn U m ω)
    rw [hdX, sub_zero, sub_zero]
  -- `Z − S = X|_U` vanishes on forms supported off `K ⊇ spt X`, so `spt (Z − S) ⊆ K`
  have hKU : K ⊆ U := fun x hx => hWU.2 (subset_closure (hKAW hx).2)
  have hspt := Submission.rsd_cmr_support_subset_of_vanish P (m + 1) U K (S - (0 - XU) - S) hU hK
    hKU fun ω hω => by
      have hX0 : XU ω = 0 := Submission.dtc_vanish_off_support P (m + 1) univ X
        (testFormOnInclusion (subset_univ U) (m + 1) ω) (hω.mono_right hXK)
      show S ω - (0 - XU ω) - S ω = 0
      rw [hX0, sub_zero, sub_zero, sub_self]
  exact hmin.2 W _ hW hWU hZim hbd hspt.2 (hspt.1.trans hKAW)
/-- **Simon 6.2.5, 6.2.16** (mass across a change of domain).  If `W ⊆ V ⊆ U`, and
`S ∈ 𝒟ₙ(U)`, `S' ∈ 𝒟ₙ(V)` agree on every `ω ∈ 𝒟ⁿ(V)` with `spt ω ⊆ W`, then
`M_W(S) = M_W(S')`.  A form admissible for `M_W` has `spt ω ⊆ W ⊆ V`, so the admissible forms in
`U` and in `V` are the same underlying forms, related by `testFormOnInclusion`; the two suprema
therefore range over the same values. -/
theorem Submission.dtc_massOn_eq_of_agreeOn : ∀ (P n : ℕ) (U V W : Set (Euclid P)) (hVU : V ⊆ U) (S : GeometricCurrentOn U n) (S' : GeometricCurrentOn V n), W ⊆ V → (∀ ω : TestFormOn V n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → S (testFormOnInclusion hVU n ω) = S' ω) → S.massOn W = S'.massOn W := by
  intro P n U V W hVU S S' hWV hagree
  -- both masses are suprema of `ofReal (T ω)` over admissible forms: compare the value sets
  unfold GeometricCurrentOn.massOn
  congr 1
  ext r
  constructor
  · -- an admissible `ω ∈ 𝒟ⁿ(U)` has `spt ω ⊆ W ⊆ V`, so it is an admissible `ω' ∈ 𝒟ⁿ(V)`
    rintro ⟨ω, hω, rfl⟩
    let ω' : TestFormOn V n := ⟨ω, ω.property.1, hω.1.trans hWV⟩
    have hincl : testFormOnInclusion hVU n ω' = ω := Subtype.ext rfl
    refine ⟨ω', hω, ?_⟩
    dsimp only
    rw [← hagree ω' hω.1, hincl]
  · -- an admissible `ω' ∈ 𝒟ⁿ(V)` is admissible in `U` after inclusion
    rintro ⟨ω', hω', rfl⟩
    refine ⟨testFormOnInclusion hVU n ω', hω', ?_⟩
    dsimp only
    rw [hagree ω' hω'.1]

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

/-- **Simon 7.2.4, local comparison: `f` fixes `T` near `spt T`.**  Let `T = τ(M, θ, ξ)` in `U`,
`O` open and `f` differentiable on `O` with `f = id` on `spt T ∩ O`.  Then for `Hⁿ`-a.e.
`x ∈ M ∩ O`, `f(x) = x` and `⟨α ∘ ΛⁿDf(x), ξ(x)⟩ = ⟨α, ξ(x)⟩` for every `n`-covector `α`.
Since `Hⁿ(M ∖ spt T) = 0`, a.e. `x ∈ M ∩ O` lies in `A = M ∩ (spt T ∩ O)`, and `ξ(x)` orients an
approximate tangent plane `Q` of `M` at `x` (Simon 6.3.1).  As `(M ∖ A) ∩ O` is `Hⁿ`-null and
`x ∈ O`, `Q` is also one of `A` (Ch. 3, 1.4).  `f` fixes `A` and is differentiable at `x`, so
`Df(x)` fixes `Q`, and hence `ΛⁿDf(x)` fixes `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ`. -/
theorem Submission.dtc_bc_lc_orient_fixed : ∀ (P n : ℕ) (U O : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (f : Euclid P → Euclid P), IsOpen U → IsOpen O → R.Represents T → DifferentiableOn ℝ f O → (∀ y ∈ T.support ∩ O, f y = y) → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), f x = x ∧ ∀ α : Covector (Euclid P) n, R.orient x (α.compContinuousLinearMap (fderiv ℝ f x)) = R.orient x α := by
  intro P n U O T R f hU hO hRT hf hfix
  -- `Hⁿ(M ∖ spt T) = 0`, so the good set `A = M ∩ (spt T ∩ O)` has `Hⁿ((M ∖ A) ∩ O) = 0`
  have hnull : μHE[n] (R.carrier \ T.support) = 0 :=
    Submission.imrep_carrier_sdiff_support_null P n U T R hU hRT
  have hAnull : μHE[n] ((R.carrier \ (R.carrier ∩ (T.support ∩ O))) ∩ O) = 0 := by
    refine measure_mono_null (fun y hy => ?_) hnull
    exact ⟨hy.1.1, fun hyS => hy.1.2 ⟨hy.1.1, hyS, hy.2⟩⟩
  have hMO : MeasurableSet (R.carrier ∩ O) := R.measurableSet_carrier.inter hO.measurableSet
  -- `Hⁿ`-a.e. `x ∈ M ∩ O` lies in `spt T`, and `ξ(x)` orients an approximate tangent plane of `M`
  have hS : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), x ∈ T.support := by
    rw [ae_iff, Measure.restrict_apply' hMO]
    refine measure_mono_null (fun y hy => ?_) hnull
    exact ⟨hy.2.1, hy.1⟩
  have hor : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ O)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients
  filter_upwards [ae_restrict_mem hMO, hS, hor] with x hx hxS ⟨Q, hQ, hξ⟩
  have hfx : f x = x := hfix x ⟨hxS, hx.2⟩
  -- `Q` is an approximate tangent plane of `A` at `x ∈ O`, and `Df(x)` fixes it
  have hQA : HasApproximateTangentSpaceAt n (R.carrier ∩ (T.support ∩ O)) x Q :=
    Submission.dtc_approxTangent_of_null_diff P n R.carrier _ O x Q inter_subset_left hO hx.2
      hAnull hQ
  have hDf : ∀ v ∈ Q, fderiv ℝ f x v = v :=
    Submission.dtc_bc_lc_fderiv_apply_eq_of_approxTangent P n _ f x Q hQA
      (hf.differentiableAt (hO.mem_nhds hx.2)) hfx fun y hy => hfix y hy.2
  -- so `ΛⁿDf(x)` fixes the unit orientation `ξ(x)` of `Q`
  exact ⟨hfx, Submission.dtc_bc_lc_unitOrientation_comp_eq P n (R.orient x) Q (fderiv ℝ f x) hξ hDf⟩
/-- **Simon Ch. 6, 3.1–3.2** (the weight `θHᵏ⌞M`): for an integer multiplicity triple
`R = (M, θ, ξ)` in `W`, `R.measure = (Hᵏ⌞M).withDensity θ` has the same null sets as `Hᵏ⌞M`
(`θ` is measurable and `θ ≥ 1` on `M`).  For Borel `A`, `R.measure(A) = ∫_{M ∩ A} θ dHᵏ`; hence
`R.measure(ℝᴾ \ M) = 0`, and `R.measure(K) < ∞` for compact `K ⊆ W` by local integrability of
`θ`.  Absolute continuity makes `ξ` a.e. strongly measurable for `R.measure`, and
`R.action ω = ∫_M θ⟨ω, ξ⟩ dHᵏ = ∫ ⟨ω, ξ⟩ dR.measure` for every form `ω`. -/
theorem Submission.cbr_imRep_measure_basic : ∀ (P k : ℕ) (W : Set (Euclid P)) (R : IMRep W k), R.measure ≪ μHE[k].restrict R.carrier ∧ μHE[k].restrict R.carrier ≪ R.measure ∧ (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ x in R.carrier ∩ A, (R.mult x : ℝ≥0∞) ∂μHE[k]) ∧ R.measure R.carrierᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → R.measure K < ∞) ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ ω : DifferentialForm (Euclid P) k, R.action ω = ∫ x, R.orient x (ω x) ∂R.measure := by
  intro P k W R
  -- the density `θ`, as an `ℝ≥0`-valued measurable function
  have hθ : Measurable fun x => (R.mult x : NNReal) := measurable_from_nat.comp R.measurable_mult
  -- (a) a measure with density is absolutely continuous w.r.t. its base measure
  have hac : R.measure ≪ μHE[k].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- (c) `μ(A) = ∫_A θ d(Hᵏ⌞M) = ∫_{M ∩ A} θ dHᵏ` for Borel `A`
  have happly : ∀ A : Set (Euclid P), MeasurableSet A →
      R.measure A = ∫⁻ x in R.carrier ∩ A, (R.mult x : ℝ≥0∞) ∂μHE[k] := fun A hA => by
    rw [IMRep.measure, withDensity_apply _ hA, Measure.restrict_restrict hA, inter_comm A]
  refine ⟨hac, ?_, happly, ?_, fun K hK hKW => ?_, R.aestronglyMeasurable_orient.mono_ac hac,
    fun ω => ?_⟩
  -- (b) `θ ≠ 0` on `M`, hence `Hᵏ⌞M`-a.e.
  · refine withDensity_absolutelyContinuous'
      (measurable_from_nat.comp R.measurable_mult).aemeasurable ?_
    filter_upwards [ae_restrict_mem R.measurableSet_carrier] with x hx
    exact Nat.cast_ne_zero.2 (R.mult_pos x hx).ne'
  -- (d) `M ∩ Mᶜ = ∅`
  · rw [happly _ R.measurableSet_carrier.compl, inter_compl_self, Measure.restrict_empty,
      lintegral_zero_measure]
  -- (e) local integrability of `θ`
  · rw [happly K hK.measurableSet]
    exact lt_top_iff_ne_top.2 (R.locallyIntegrable_mult K hK hKW)
  -- (g) `∫ ⟨ω, ξ⟩ d(θ Hᵏ⌞M) = ∫_M θ ⟨ω, ξ⟩ dHᵏ`
  · have h := integral_withDensity_eq_integral_smul (μ := μHE[k].restrict R.carrier) hθ
      fun x => R.orient x (ω x)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.action]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [NNReal.smul_def]
/-- Comparison of measures from open subsets, by outer regularity (Simon 1.15(1)): if
`μ(ℝᴾ \ U) = 0`, `ν` is finite on compact subsets of the open set `U`, and `μ(V) ≤ ν(V)` for every
open `V ⊆ U`, then `μ ≤ ν`.  `U` is exhausted by the open sets
`V_k = {‖x‖ < k, 1/k < d(x, ℝᴾ \ U)}`, each inside the compact `K_k ⊆ U`; `ν⌞V_k` is finite,
hence outer regular, which gives `μ(E ∩ V_k) ≤ ν(E ∩ V_k)`; continuity from below finishes. -/
theorem Submission.dtc_bc_lc_measure_le_of_le_on_open : ∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K < ∞) → (∀ V : Set (Euclid P), IsOpen V → V ⊆ U → μ V ≤ ν V) → μ ≤ ν := by
  intro P U μ ν hU hμU hν hle
  -- Steps 1–3: the exhaustion `V k ⊆ K k ⊆ U`, `V` increasing with union `U`
  set V : ℕ → Set (Euclid P) :=
    fun k => {x | ‖x‖ < k ∧ (k : ℝ≥0∞)⁻¹ < infEDist x Uᶜ}
  set K : ℕ → Set (Euclid P) :=
    fun k => {x | ‖x‖ ≤ k ∧ (k : ℝ≥0∞)⁻¹ ≤ infEDist x Uᶜ}
  have hVopen : ∀ k, IsOpen (V k) := fun k =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const continuous_infEDist)
  have hKcpt : ∀ k, IsCompact (K k) := fun k => by
    refine isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le continuous_const continuous_infEDist)
    · refine (isBounded_closedBall (x := (0 : Euclid P)) (r := (k : ℝ))).subset ?_
      intro x hx
      simpa [mem_closedBall, dist_zero_right] using hx.1
  have hKU : ∀ k, K k ⊆ U := fun k x hx => by
    by_contra hxU
    have h0 : infEDist x Uᶜ = 0 := infEDist_zero_of_mem hxU
    have h1 : (k : ℝ≥0∞)⁻¹ ≤ 0 := h0 ▸ hx.2
    exact (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top k)) (nonpos_iff_eq_zero.mp h1)
  have hVK : ∀ k, V k ⊆ K k := fun k x hx => ⟨hx.1.le, hx.2.le⟩
  have hVmono : Monotone V := fun k m hkm x hx =>
    ⟨lt_of_lt_of_le hx.1 (by exact_mod_cast hkm),
      lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast hkm)) hx.2⟩
  have hVU : ⋃ k, V k = U := by
    apply subset_antisymm
    · exact iUnion_subset fun k => (hVK k).trans (hKU k)
    · intro x hx
      have hpos : 0 < infEDist x Uᶜ := by
        rw [infEDist_pos_iff_notMem_closure, hU.isClosed_compl.closure_eq]
        exact fun h => h hx
      obtain ⟨a, ha⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
      obtain ⟨b, hb⟩ := exists_nat_gt ‖x‖
      refine mem_iUnion.mpr ⟨max a b, ?_, ?_⟩
      · exact lt_of_lt_of_le hb (by exact_mod_cast le_max_right a b)
      · exact lt_of_le_of_lt (ENNReal.inv_le_inv.mpr (by exact_mod_cast le_max_left a b)) ha
  -- Step 4: `ν (V k) < ∞`
  have hνV : ∀ k, ν (V k) ≠ ∞ := fun k =>
    ne_of_lt (lt_of_le_of_lt (measure_mono (hVK k)) (hν _ (hKcpt k) (hKU k)))
  -- Step 5: comparison inside `V k`, by outer regularity of the finite measure `ν⌞V k`
  have hcomp : ∀ k (E : Set (Euclid P)), μ (E ∩ V k) ≤ ν (E ∩ V k) := by
    intro k E
    have : IsFiniteMeasure (ν.restrict (V k)) := isFiniteMeasure_restrict.mpr (hνV k)
    refine le_of_forall_gt fun r hr => ?_
    rw [← Measure.restrict_apply' (hVopen k).measurableSet] at hr
    obtain ⟨O, hEO, hO, hOr⟩ := Set.exists_isOpen_lt_of_lt E r hr
    rw [Measure.restrict_apply' (hVopen k).measurableSet] at hOr
    calc μ (E ∩ V k) ≤ μ (O ∩ V k) := measure_mono (inter_subset_inter_left _ hEO)
      _ ≤ ν (O ∩ V k) := hle _ (hO.inter (hVopen k))
          (inter_subset_right.trans ((hVK k).trans (hKU k)))
      _ < r := hOr
  -- Steps 6–8: concentration on `U`, continuity from below, `Measure.le_iff`
  rw [Measure.le_iff]
  intro E hE
  calc μ E = μ (E ∩ U) := by
        have h := measure_inter_add_sdiff E hU.measurableSet (μ := μ)
        have h2 : μ (E \ U) = 0 := measure_mono_null (fun x hx => hx.2) hμU
        rw [h2, add_zero] at h
        exact h.symm
    _ = ⨆ k, μ (E ∩ V k) := by
        rw [← hVU, inter_iUnion]
        exact Monotone.measure_iUnion fun k m hkm => inter_subset_inter_right E (hVmono hkm)
    _ ≤ ν E := iSup_le fun k => (hcomp k E).trans (measure_mono inter_subset_left)

/-- **Subadditivity of weights** (Simon 6.2.5 and 6.3.2(3), as used in the proof of 7.2.4).  If
`|c| ≤ 1` and `Z(ω) = X(ω) + c Y(ω)` for every `ω ∈ 𝒟ⁿ(U)`, then `μ_Z ≤ μ_X + μ_Y`.  For open
`V ⊆ U`, `μ_Z(V) = M_V(Z) ≤ M_V(X) + M_V(Y) = μ_X(V) + μ_Y(V)` by the mass triangle inequality
and `M_V = μ(V)`.  As `M_Z ⊆ U`, `μ_Z` is concentrated on `U`, and `μ_X + μ_Y` is finite on
compact subsets of `U`; so the inequality extends from open subsets of `U` to all sets. -/
theorem Submission.dtc_bc_lc_measure_le_add : ∀ (P n : ℕ) (U : Set (Euclid P)) (X Y Z : GeometricCurrentOn U n) (RX RY RZ : IMRep U n) (c : ℝ), IsOpen U → |c| ≤ 1 → RX.Represents X → RY.Represents Y → RZ.Represents Z → (∀ ω : TestFormOn U n, Z ω = X ω + c * Y ω) → RZ.measure ≤ RX.measure + RY.measure := by
  intro P n U X Y Z RX RY RZ c hU hc hRX hRY hRZ hZ
  obtain ⟨-, -, -, -, hXK, -, -⟩ := Submission.cbr_imRep_measure_basic P n U RX
  obtain ⟨-, -, -, -, hYK, -, -⟩ := Submission.cbr_imRep_measure_basic P n U RY
  obtain ⟨-, -, -, hZM, -, -, -⟩ := Submission.cbr_imRep_measure_basic P n U RZ
  refine Submission.dtc_bc_lc_measure_le_of_le_on_open P U RZ.measure (RX.measure + RY.measure)
    hU ?_ ?_ ?_
  -- Step 3: `μ_Z(ℝᴾ \ U) ≤ μ_Z(ℝᴾ \ M_Z) = 0`, as `M_Z ⊆ U`
  · exact measure_mono_null (compl_subset_compl.2 RZ.carrier_subset) hZM
  -- Step 4: `μ_X(K) + μ_Y(K) < ∞` for compact `K ⊆ U`
  · intro K hK hKU
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨hXK K hK hKU, hYK K hK hKU⟩
  -- Steps 1–2: `μ_Z(V) = M_V(Z) ≤ M_V(X) + M_V(Y) = μ_X(V) + μ_Y(V)` for open `V ⊆ U`
  · intro V hV hVU
    calc RZ.measure V = Z.massOn V :=
          (Submission.dtc_mass_eq_measure P n U V Z RZ hU hV hVU hRZ).symm
      _ ≤ X.massOn V + Y.massOn V :=
          Submission.lcmp_massOn_le_add_of_eval_eq P n U V X Y Z c hc fun ω _ => hZ ω
      _ = (RX.measure + RY.measure) V := by
          rw [Measure.add_apply, Submission.dtc_mass_eq_measure P n U V X RX hU hV hVU hRX,
            Submission.dtc_mass_eq_measure P n U V Y RY hU hV hVU hRY]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
