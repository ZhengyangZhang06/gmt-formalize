import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
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

/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith

/-- **Simon Ch. 3, Lemma 1.2, "only if" part, final paragraph** (chapter-03.txt lines 61–65),
for one `C¹` map `G : ℝⁿ → ℝᴾ`: up to an `Hⁿ`-null set, `G(ℝⁿ)` is covered by the images
`G(B_{r_k}(c_k))` of countably many open balls (empty when `r_k ≤ 0`) carrying lower Lipschitz
bounds `m_k|a − b| ≤ |G a − G b|`, `m_k > 0`.
The critical image `G(C)`, `C = {x : DG(x) not injective}`, is `Hⁿ`-null.  Mathlib's partition
of `C ∩ B̄_R(0)` into pieces `T` on which `G` is `η`-close to some non-injective `A = DG(y)`
reduces this to `Hⁿ(G(T)) ≤ (‖A‖ + 1)ⁿ η Lⁿ(T)`: for a unit `u ∈ ker A`, the compression
`D w = w + (η − 1)⟨u, w⟩u` has `det D = η`, and `|G a − G b| ≤ (‖A‖ + 1)|D a − D b|` on `T`.
For a dense sequence `e` and `(q, p) = Nat.unpair k`, the candidate ball `B_{1/(p+1)}(e_q)` is
kept, with a witness `m_k`, when it carries a lower Lipschitz bound, and replaced by `B_0 = ∅`
otherwise.  At a regular point `x`, `codim1_rdo_c1cov_local_lower_lipschitz` gives a bound on
some `B_δ(x)`; a candidate ball with `2/(p+1) < δ` and `|x − e_q| < 1/(p+1)` contains `x`, lies
in `B_δ(x)` and is kept. -/
theorem Submission.codim1_rdo_c1cov_regular_ball_cover : ∀ (P n : ℕ) (G : Euclid n → Euclid P), ContDiff ℝ 1 G → ∃ (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖G a - G b‖) ∧ μHE[n] (range G \ ⋃ k, G '' ball (c k) (r k)) = 0 := by
  intro P n G hG
  -- the critical image `G({x : DG(x) not injective})` is `Hⁿ`-null
  have hcrit : μHE[n] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    -- near a non-injective `A`, `G` shrinks `Hⁿ` by the factor `ε`
    have hloc : ∀ ε : NNReal, 0 < ε → ε ≤ 1 → ∀ A : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal,
        0 < δ ∧ (¬ Injective A → ∀ T : Set (Euclid n), ApproximatesLinearOn G A T δ →
          μHE[n] (G '' T) ≤ ε * volume T) := by
      intro ε hε hε1 A
      by_cases hA : Injective A
      · exact ⟨1, one_pos, fun h => absurd hA h⟩
      -- a unit vector `u` in the kernel of `A`
      obtain ⟨u, hu1, hAu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ A u = 0 := by
        rw [injective_iff_map_eq_zero] at hA
        push Not at hA
        obtain ⟨w, hw, hw0⟩ := hA
        refine ⟨‖w‖⁻¹ • w, ?_, ?_⟩
        · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw0)]
        · rw [map_smul, hw, smul_zero]
      set K : NNReal := ‖A‖₊ + 1 with hK
      have hK1 : 1 ≤ K := le_add_self
      have hKn : (0 : NNReal) < K ^ n := pow_pos (zero_lt_one.trans_le hK1) n
      set η : NNReal := ε / K ^ n with hη
      have hη0 : 0 < η := div_pos hε hKn
      have hη1 : (η : ℝ) ≤ 1 := by
        have : η ≤ ε := div_le_self (by positivity) (one_le_pow₀ hK1)
        exact_mod_cast this.trans hε1
      refine ⟨η, hη0, fun _ T hT => ?_⟩
      -- the compression `D w = w + (η - 1) ⟪u, w⟫ u` along `u`
      let D : Euclid n →ₗ[ℝ] Euclid n := LinearMap.id + ((η : ℝ) - 1) • (innerₛₗ ℝ u).smulRight u
      have hD : ∀ w, D w = w + (((η : ℝ) - 1) * inner ℝ u w) • u := by
        intro w
        simp [D, mul_smul]
      -- `det D = 1 + (η - 1) ‖u‖² = η` (matrix determinant lemma in the standard basis)
      have hdet : LinearMap.det D = η := by
        set b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis with hb
        have hM : LinearMap.toMatrix b b D =
            1 + Matrix.vecMulVec (fun i => u i) (fun j => ((η : ℝ) - 1) * u j) := by
          ext i j
          rw [LinearMap.toMatrix_apply, hD]
          simp [hb, Matrix.one_apply, Matrix.vecMulVec_apply, EuclideanSpace.inner_single_right]
          ring
        have hsum : ∑ j, u j * u j = 1 := by
          have h := real_inner_self_eq_norm_sq u
          rw [hu1, PiLp.inner_apply] at h
          simpa [sq] using h
        rw [← LinearMap.det_toMatrix b, hM, Matrix.vecMulVec_eq Unit,
          Matrix.det_one_add_replicateCol_mul_replicateRow]
        simp only [dotProduct, mul_assoc]
        rw [← Finset.mul_sum, hsum]
        ring
      -- `‖G y₁ - G y₂‖ ≤ ‖A (y₁ - y₂)‖ + η ‖y₁ - y₂‖ ≤ K ‖D (y₁ - y₂)‖` on `T`
      have hkey : ∀ y₁ ∈ T, ∀ y₂ ∈ T, ‖G y₁ - G y₂‖ ≤ K * ‖D y₁ - D y₂‖ := by
        intro y₁ h₁ y₂ h₂
        have happ : ‖G y₁ - G y₂ - A (y₁ - y₂)‖ ≤ η * ‖y₁ - y₂‖ := hT y₁ h₁ y₂ h₂
        rw [← map_sub]
        set w := y₁ - y₂
        have hAw : A w = A (D w) := by rw [hD, map_add, map_smul, hAu, smul_zero, add_zero]
        -- `‖D w‖² = ‖w‖² - (1 - η²) ⟪u, w⟫² ≥ η² ‖w‖²`
        have hnorm : (η : ℝ) * ‖w‖ ≤ ‖D w‖ := by
          have h1 : ‖D w‖ ^ 2 = ‖w‖ ^ 2 + ((η : ℝ) ^ 2 - 1) * inner ℝ u w ^ 2 := by
            rw [hD, norm_add_sq_real, inner_smul_right, norm_smul, real_inner_comm,
              Real.norm_eq_abs, hu1, mul_one, sq_abs]
            ring
          have h2 : inner ℝ u w ^ 2 ≤ ‖w‖ ^ 2 := by
            have h := abs_real_inner_le_norm u w
            rw [hu1, one_mul] at h
            exact sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
          have h3 : ((η : ℝ) * ‖w‖) ^ 2 ≤ ‖D w‖ ^ 2 := by
            rw [h1, mul_pow]
            have h4 : (η : ℝ) ^ 2 ≤ 1 := by nlinarith [η.coe_nonneg]
            nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
          exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h3
        have hAD : ‖A (D w)‖ ≤ ‖A‖ * ‖D w‖ := A.le_opNorm _
        calc ‖G y₁ - G y₂‖ ≤ ‖A w‖ + ‖G y₁ - G y₂ - A w‖ := norm_le_insert' _ _
          _ ≤ ‖A‖ * ‖D w‖ + ‖D w‖ := by rw [hAw] at happ ⊢; linarith
          _ = K * ‖D w‖ := by simp [K]; ring
      -- `φ = G ∘ D⁻¹` is `K`-Lipschitz on `D '' T` and `G '' T ⊆ φ '' (D '' T)`
      let φ : Euclid n → Euclid P := fun z => G (Function.invFunOn D T z)
      have hφ : ∀ y ∈ T, Function.invFunOn D T (D y) ∈ T ∧ D (Function.invFunOn D T (D y)) = D y :=
        fun y hy => Function.invFunOn_pos ⟨y, hy, rfl⟩
      have hlip : LipschitzOnWith K φ (D '' T) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨y₁, h₁, rfl⟩ _ ⟨y₂, h₂, rfl⟩
        obtain ⟨h₁', e₁⟩ := hφ y₁ h₁
        obtain ⟨h₂', e₂⟩ := hφ y₂ h₂
        have h := hkey _ h₁' _ h₂'
        rw [e₁, e₂] at h
        simpa only [dist_eq_norm] using h
      have hsub : G '' T ⊆ φ '' (D '' T) := by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨D y, ⟨y, hy, rfl⟩, ?_⟩
        obtain ⟨h', e⟩ := hφ y hy
        have h := hkey _ h' _ hy
        rw [e, sub_self, norm_zero, mul_zero] at h
        exact sub_eq_zero.1 (norm_le_zero_iff.1 h)
      -- `Hⁿ(G(T)) ≤ Kⁿ Hⁿ(D(T)) = Kⁿ |det D| Lⁿ(T) = ε Lⁿ(T)`
      calc μHE[n] (G '' T) ≤ μHE[n] (φ '' (D '' T)) := measure_mono hsub
        _ ≤ (K : ℝ≥0∞) ^ n * μHE[n] (D '' T) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hlip
        _ = (K : ℝ≥0∞) ^ n * (ENNReal.ofReal |LinearMap.det D| * volume T) := by
            rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
        _ = ε * volume T := by
            rw [hdet, abs_of_nonneg η.coe_nonneg, ENNReal.ofReal_coe_nnreal, ← mul_assoc,
              ← ENNReal.coe_pow, ← ENNReal.coe_mul, hη, mul_div_cancel₀ _ hKn.ne']
    -- on `C ∩ B̄_R(0)`: partition into pieces where `G` is close to some `DG(y)`, `y ∈ C`
    have hR : ∀ R : ℝ, μHE[n] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall 0 R)) = 0 := by
      intro R
      set s := {x | ¬ Injective (fderiv ℝ G x)} ∩ closedBall (0 : Euclid n) R with hs
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' s) ≤ ε * volume (closedBall (0 : Euclid n) R) := by
        intro ε hε hε1
        rcases eq_empty_or_nonempty s with h | h
        · rw [h, image_empty, measure_empty]
          exact bot_le
        choose δ hδ using hloc ε hε hε1
        obtain ⟨t, A, t_disj, t_meas, t_cover, ht, Af'⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G s (fderiv ℝ G)
            (fun x _ => (hG.differentiable one_ne_zero x).hasFDerivAt.hasFDerivWithinAt) δ
            (fun A => (hδ A).1.ne')
        calc μHE[n] (G '' s) ≤ μHE[n] (⋃ k, G '' (s ∩ t k)) := by
              rw [← image_iUnion, ← inter_iUnion]
              exact measure_mono (image_mono (subset_inter Subset.rfl t_cover))
          _ ≤ ∑' k, μHE[n] (G '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R ∩ t k) := by
              refine ENNReal.tsum_le_tsum fun k => ?_
              obtain ⟨y, hy, hAy⟩ := Af' h k
              calc μHE[n] (G '' (s ∩ t k)) ≤ ε * volume (s ∩ t k) :=
                    (hδ (A k)).2 (by rw [hAy]; exact hy.1) _ (ht k)
                _ ≤ ε * volume (closedBall (0 : Euclid n) R ∩ t k) := by
                    gcongr
                    exact inter_subset_right
          _ = ε * volume (⋃ k, closedBall (0 : Euclid n) R ∩ t k) := by
              rw [ENNReal.tsum_mul_left, measure_iUnion]
              · exact pairwise_disjoint_mono t_disj fun k => inter_subset_right
              · exact fun k => measurableSet_closedBall.inter (t_meas k)
          _ ≤ ε * volume (closedBall (0 : Euclid n) R) := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left
      -- let `ε → 0`
      have B : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
          (𝓝[>] 0) (𝓝 0) := by
        have h : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))
            (𝓝 0) (𝓝 (((0 : NNReal) : ℝ≥0∞) * volume (closedBall (0 : Euclid n) R))) :=
          ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 tendsto_id)
            (Or.inr measure_closedBall_lt_top.ne)
        simp only [zero_mul, ENNReal.coe_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      rw [← nonpos_iff_eq_zero]
      apply ge_of_tendsto B
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with ε hε
      exact hbound ε hε.1 hε.2
    have h := measure_iUnion_null (μ := μHE[n]) fun k : ℕ => hR k
    rwa [← image_iUnion, iUnion_inter_closedBall_nat] at h
  classical
  -- candidate balls `B_{1/(p+1)}(e_q)`, `(q, p) = Nat.unpair k`, for a dense sequence `e`
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq (Euclid n)
  let ctr : ℕ → Euclid n := fun k => e (Nat.unpair k).1
  let rad : ℕ → ℝ := fun k => 1 / ((Nat.unpair k).2 + 1 : ℝ)
  -- a candidate ball is good if `G` has a lower Lipschitz bound on it
  let good : ℕ → Prop := fun k => ∃ μ : ℝ, 0 < μ ∧
    ∀ a ∈ ball (ctr k) (rad k), ∀ b ∈ ball (ctr k) (rad k), μ * ‖a - b‖ ≤ ‖G a - G b‖
  refine ⟨ctr, fun k => if good k then rad k else 0,
    fun k => if h : good k then Exists.choose h else 1, fun k => ?_, fun k => ?_, ?_⟩
  · -- `m_k > 0`
    show 0 < if h : good k then Exists.choose h else 1
    split_ifs with h
    exacts [(Exists.choose_spec h).1, one_pos]
  · -- (i): the witness on a good ball; otherwise `B_0(c_k) = ∅`
    intro a ha b hb
    dsimp only at ha hb ⊢
    by_cases h : good k
    · rw [ite_eq_left h] at ha hb
      rw [dite_eq_left h]
      exact (Exists.choose_spec h).2 a ha b hb
    · rw [ite_eq_right h, ball_zero] at ha
      exact absurd ha (notMem_empty a)
  · -- (ii): each regular point lies in a good ball, so the remainder is in the critical image
    refine measure_mono_null ?_ hcrit
    rintro y ⟨⟨x, rfl⟩, hy⟩
    refine ⟨x, fun hinj => hy ?_, rfl⟩
    obtain ⟨δ, μ, hδ, hμ, hlip⟩ :=
      Submission.codim1_rdo_c1cov_local_lower_lipschitz P n G x hG hinj
    obtain ⟨p, hp⟩ := exists_nat_one_div_lt (half_pos hδ)
    obtain ⟨q, hq⟩ := he.exists_dist_lt x (Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((p : ℝ) + 1))
    have hk : Nat.unpair (Nat.pair q p) = (q, p) := Nat.unpair_pair q p
    -- `B_{1/(p+1)}(e_q) ⊆ B_δ(x)`, so this candidate ball is good
    have hsub : ball (ctr (Nat.pair q p)) (rad (Nat.pair q p)) ⊆ ball x δ := by
      intro a ha
      simp only [ctr, rad, hk, mem_ball] at ha ⊢
      calc dist a x ≤ dist a (e q) + dist (e q) x := dist_triangle _ _ _
        _ < 1 / ((p : ℝ) + 1) + 1 / ((p : ℝ) + 1) := add_lt_add ha (by rwa [dist_comm])
        _ < δ := by linarith
    have hgood : good (Nat.pair q p) :=
      ⟨μ, hμ, fun a ha b hb => hlip a (hsub ha) b (hsub hb)⟩
    refine mem_iUnion.2 ⟨Nat.pair q p, x, ?_, rfl⟩
    show x ∈ ball (ctr (Nat.pair q p)) (if good (Nat.pair q p) then rad (Nat.pair q p) else 0)
    rw [ite_eq_left hgood]
    simpa only [ctr, rad, hk, mem_ball] using hq
/-- **Simon Ch. 3, proof of Lemma 1.2** (properties (ii), (iii) of the pieces `g(B_r(c))`): the
image of an open ball under a `C¹` map `g : ℝⁿ → ℝᴾ` is Borel and has finite `Hⁿ`-measure.
`B_r(c) = ⋃ₜ closedBall(c, r − 1/(t+1))`, so `g(B_r(c))` is a countable union of compact sets;
`g` is Lipschitz on the compact convex `closedBall(c, r)`, so by Simon Ch. 2, 1.8(i)
`Hⁿ(g(B_r(c))) ≤ Λⁿ Lⁿ(B_r(c)) < ∞`. -/
theorem Submission.codim1_rdo_c1cov_image_ball_borel_finite : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r : ℝ), ContDiff ℝ 1 g → MeasurableSet (g '' ball c r) ∧ μHE[n] (g '' ball c r) ≠ ∞ := by
  intro P n g c r hg
  refine ⟨?_, ?_⟩
  · -- `B_r(c)` is the union of the compact balls `closedBall(c, r − 1/(t+1))`
    have hball : ball c r = ⋃ t : ℕ, closedBall c (r - 1 / ((t : ℝ) + 1)) := by
      ext y
      simp only [mem_ball, mem_iUnion, mem_closedBall]
      constructor
      · intro hy
        obtain ⟨t, ht⟩ := exists_nat_one_div_lt (sub_pos.mpr hy)
        exact ⟨t, by linarith⟩
      · rintro ⟨t, ht⟩
        have : (0 : ℝ) < 1 / ((t : ℝ) + 1) := by positivity
        linarith
    rw [hball, image_iUnion]
    exact MeasurableSet.iUnion fun t =>
      ((isCompact_closedBall c _).image hg.continuous).isClosed.measurableSet
  · -- `g` is Lipschitz on the compact convex `closedBall c r`, hence on `ball c r`
    obtain ⟨K, hK⟩ := (hg.contDiffOn (s := closedBall c r)).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall c r) (isCompact_closedBall c r)
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (hK.mono ball_subset_closedBall))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_ball_lt_top.ne
/-- Simon Ch. 3, Lemma 1.2, display (1) (corrected: `F(ℝⁿ) ⊆ E ∪ ⋃ᵢ Gᵢ(ℝⁿ)`, `Gᵢ : ℝⁿ → ℝᴾ`),
for one Lipschitz map `F : ℝⁿ → ℝᴾ`, given the scalar `C¹` approximation theorem (Simon Ch. 2,
Theorem 1.5) on `ℝⁿ` as the hypothesis.  Each coordinate `Fˡ` is `K`-Lipschitz; approximating it
with error `((i + 1)(P + 1))⁻¹` gives `C¹` maps `Gᵢ = (g_{i,l})ₗ` with `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`, so
`Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null, `Hⁿ(F(Z)) ≤ Kⁿ Lⁿ(Z) = 0` (Simon 2.1.8(i), `Hⁿ = Lⁿ` on `ℝⁿ`) and
`F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`. -/
theorem Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover : ∀ (P n : ℕ), (∀ (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε) → ∀ (F : Euclid n → Euclid P) (K : NNReal), LipschitzWith K F → ∃ G : ℕ → Euclid n → Euclid P, (∀ i, ContDiff ℝ 1 (G i)) ∧ μHE[n] (range F \ ⋃ i, range (G i)) = 0 := by
  intro P n hH F K hF
  -- Step 1: the coordinates `Fˡ` of `F` are `K`-Lipschitz
  have hFl : ∀ l : Fin P, LipschitzWith K fun x => F x l := fun l =>
    LipschitzWith.of_dist_le_mul fun x y =>
      (PiLp.dist_apply_le (F x) (F y) l).trans (hF.dist_le_mul x y)
  -- Step 2: `C¹` approximation of every coordinate with error `δᵢ = ((i + 1)(P + 1))⁻¹`
  have hδ : ∀ i : ℕ, (0 : ℝ≥0∞) < (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := fun i =>
    ENNReal.inv_pos.2 (ENNReal.mul_ne_top (by simp) (by simp))
  choose g hg hgvol using fun (i : ℕ) (l : Fin P) => hH (fun x => F x l) K (hFl l) _ (hδ i)
  -- Step 3: `Gᵢ = (g_{i,1}, …, g_{i,P})` is `C¹`
  let G : ℕ → Euclid n → Euclid P := fun i x => WithLp.toLp 2 fun l => g i l x
  have hG : ∀ i, ContDiff ℝ 1 (G i) := fun i => (contDiff_piLp 2).2 fun l => hg i l
  -- Step 4: `{F ≠ Gᵢ} ⊆ ⋃ₗ {Fˡ ≠ g_{i,l} ∨ DFˡ ≠ Dg_{i,l}}`, so `Lⁿ{F ≠ Gᵢ} ≤ (i + 1)⁻¹`
  have hsub : ∀ i, {x | F x ≠ G i x} ⊆
      ⋃ l, {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} := by
    intro i x hx
    obtain ⟨l, hl⟩ : ∃ l, F x l ≠ g i l x := by
      by_contra! h
      exact hx (PiLp.ext h)
    exact mem_iUnion.2 ⟨l, Or.inl hl⟩
  have hvol : ∀ i : ℕ, volume {x | F x ≠ G i x} ≤ ((i : ℝ≥0∞) + 1)⁻¹ := by
    intro i
    calc volume {x | F x ≠ G i x}
        ≤ ∑ l, volume {x | F x l ≠ g i l x ∨ fderiv ℝ (fun x => F x l) x ≠ fderiv ℝ (g i l) x} :=
          (measure_mono (hsub i)).trans (measure_iUnion_fintype_le _ _)
      _ ≤ ∑ _l : Fin P, (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ :=
          Finset.sum_le_sum fun l _ => (hgvol i l).le
      _ = (P : ℝ≥0∞) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by simp
      _ ≤ ((P : ℝ≥0∞) + 1) * (((i : ℝ≥0∞) + 1) * ((P : ℝ≥0∞) + 1))⁻¹ := by gcongr; exact le_self_add
      _ = ((i : ℝ≥0∞) + 1)⁻¹ := by
          rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), mul_left_comm,
            ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]
  -- Step 5: `Z = ⋂ᵢ {F ≠ Gᵢ}` is `Lⁿ`-null
  have hZ : volume (⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm (le_of_forall_gt fun ε hε => ?_) bot_le
    obtain ⟨i, hi⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    calc volume (⋂ i, {x | F x ≠ G i x}) ≤ volume {x | F x ≠ G i x} := measure_mono (iInter_subset _ i)
      _ ≤ ((i : ℝ≥0∞) + 1)⁻¹ := hvol i
      _ ≤ (i : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hi
  -- Step 6: `Hⁿ(F(Z)) ≤ Kⁿ Hⁿ(Z) = Kⁿ Lⁿ(Z) = 0`
  have hFZ : μHE[n] (F '' ⋂ i, {x | F x ≠ G i x}) = 0 := by
    refine le_antisymm ?_ bot_le
    calc μHE[n] (F '' ⋂ i, {x | F x ≠ G i x})
        ≤ (K : ℝ≥0∞) ^ n * μHE[n] (⋂ i, {x | F x ≠ G i x}) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hF.lipschitzOnWith
      _ = 0 := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hZ, mul_zero]
  -- Step 7: `F(ℝⁿ) \ ⋃ᵢ Gᵢ(ℝⁿ) ⊆ F(Z)`
  refine ⟨G, hG, measure_mono_null ?_ hFZ⟩
  rintro _ ⟨⟨x, rfl⟩, hy⟩
  exact ⟨x, mem_iInter.2 fun i h => hy (mem_iUnion.2 ⟨i, x, h.symm⟩), rfl⟩
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

/-- **Lusin's theorem** for `Lⁿ` with a closed set, `Lⁿ(B) = ∞` allowed (Simon Ch. 2, proof of
1.5, step 2, glued as in the infinite-measure case of Simon 1.15(2)).  On the bounded Borel shells
`S_j = {j ≤ ‖x‖ < j + 1}`, the compact form `dor_ims_lusin_measurable_continuousOn` gives compact
`K_j ⊆ B ∩ S_j` with `Lⁿ((B ∩ S_j) \ K_j) < δ_j` on which `g` is continuous, where `∑ δ_j < ε`.
As `K_j ⊆ S_j`, the family `(K_j)` is locally finite, so `C = ⋃ⱼ K_j` is closed and `g` is
continuous on `C`; and `B \ C ⊆ ⋃ⱼ (B ∩ S_j) \ K_j` has measure `< ε`. -/
theorem Submission.codim1_rdo_c1a_lusin_isClosed : ∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε := by
  intro n Y _ _ _ _ g B hg hB ε hε
  -- bounded Borel shells `S_j = {j ≤ ‖x‖ < j + 1}`, each of finite measure; `x ∈ S_⌊‖x‖⌋`
  set S : ℕ → Set (Euclid n) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSμ : ∀ j, volume (S j) ≠ ∞ := fun j =>
    ((measure_mono fun x hx => mem_closedBall_zero_iff.mpr hx.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hxS : ∀ x : Euclid n, x ∈ S ⌊‖x‖⌋₊ := fun x =>
    ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- weights `δ_j > 0` with `∑ δ_j < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- Lusin on each shell: compact `K_j ⊆ B ∩ S_j`, defect `< δ_j`, `g` continuous on `K_j`
  choose K hK hKB hKμ hKg using fun j =>
    Submission.dor_ims_lusin_measurable_continuousOn n volume (B ∩ S j) g (δ j) hg
      (hB.inter (hSm j)) (ne_top_of_le_ne_top (hSμ j) (measure_mono inter_subset_right))
      (hδ j).ne'
  -- `K_j ⊆ S_j`, so `ball x 1` meets `K_j` only for the finitely many `j < ‖x‖ + 1`
  have hlf : LocallyFinite K := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyK, hyx⟩
    refine Nat.lt_ceil.mpr ((hKB j hyK).2.1.trans_lt ?_)
    calc ‖y‖ ≤ ‖x‖ + dist y x := norm_le_norm_add_const_of_dist_le le_rfl
      _ < ‖x‖ + 1 := by linarith [mem_ball.mp hyx]
  -- hence `C = ⋃ⱼ K_j` is closed and `g` is continuous on `C`
  refine ⟨⋃ j, K j, iUnion_subset fun j => (hKB j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j => (hK j).isClosed,
    hlf.continuousOn_iUnion (fun j => (hK j).isClosed) hKg, ?_⟩
  -- `x ∈ B \ C` lies in `(B ∩ S_j) \ K_j` for `j = ⌊‖x‖⌋`
  calc volume (B \ ⋃ j, K j) ≤ volume (⋃ j, (B ∩ S j) \ K j) :=
        measure_mono fun x hx => mem_iUnion.mpr
          ⟨⌊‖x‖⌋₊, ⟨hx.1, hxS x⟩, fun hxK => hx.2 (mem_iUnion_of_mem _ hxK)⟩
    _ ≤ ∑' j, volume ((B ∩ S j) \ K j) := measure_iUnion_le _
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (hKμ j).le
    _ < ε := hδε
/-- **Egoroff's theorem** on `ℝⁿ` with a closed good set (steps 5–6 of Simon's proof of Ch. 2,
1.5).  If `C` is measurable (possibly `|C| = ∞`), `η_k` and `g` are measurable and `η_k → g`
pointwise on `C`, then for every `ε > 0` there is a closed `A ⊆ C` with `|C \ A| < ε` such that
`η_k → g` uniformly on every compact `Q ⊆ A`.  For weights `δ_j > 0` with `∑ δ_j < ε`, Egoroff on
the finite-measure sets `C ∩ B_{j+1}(0)` gives `t_j` with `|t_j| ≤ δ_j / 2`; put
`A₀ = C \ ⋃ t_j`.  Outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with excess `< δ_j / 2`,
so `A = (⋃ U_j)ᶜ ⊆ A₀` is closed and `C \ A ⊆ ⋃ (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`.  A compact
`Q ⊆ A` is bounded, so `Q ⊆ (C ∩ B_{j+1}(0)) \ t_j` for large `j`. -/
theorem Submission.codim1_rdo_c1a_egorov_isClosed : ∀ (n : ℕ) (C : Set (Euclid n)) (η : ℕ → Euclid n → ℝ) (g : Euclid n → ℝ), MeasurableSet C → (∀ k, Measurable (η k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n C η g hC hη hg hconv ε hε
  -- weights `δ_j > 0` with `∑ δ_j < ε`; every `s ∩ B_{j+1}(0)` has finite measure
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hB : ∀ (j : ℕ) (s : Set (Euclid n)), volume (s ∩ ball 0 (j + 1)) ≠ ∞ := fun j s =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Egoroff on `C_j = C ∩ B_{j+1}(0)`: `η_k → g` uniformly on `C_j \ t_j`, `|t_j| ≤ δ_j / 2`
  choose t htC htm htμ htu using fun j : ℕ =>
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hC.inter measurableSet_ball) (hB j C)
      (ae_of_all _ fun x hx => hconv x hx.1) (ENNReal.half_pos (hδ j).ne')
  -- `A₀ = C \ ⋃ t_j`; outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with small excess
  have hA₀ : MeasurableSet (C \ ⋃ j, t j) := hC.diff (MeasurableSet.iUnion htm)
  choose U hUD hUo hUf hUμ using fun j : ℕ =>
    (hA₀.compl.inter measurableSet_ball).exists_isOpen_sdiff_lt (hB j _)
      (ENNReal.half_pos (hδ j).ne').ne'
  -- the balls cover `A₀ᶜ`, so the closed set `A = (⋃ U_j)ᶜ` lies in `A₀`
  have hAA₀ : (⋃ j, U j)ᶜ ⊆ C \ ⋃ j, t j := by
    refine compl_subset_comm.1 fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨j, hUD j ⟨hx, mem_ball.2 (by linarith)⟩⟩
  refine ⟨(⋃ j, U j)ᶜ, hAA₀.trans sdiff_subset, (isOpen_iUnion hUo).isClosed_compl, ?_, ?_⟩
  -- `C \ A ⊆ ⋃_j (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`, and each piece has measure `≤ δ_j`
  · calc volume (C \ (⋃ j, U j)ᶜ)
        ≤ volume (⋃ j, (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1))))) := by
          refine measure_mono fun x ⟨hxC, hxU⟩ => ?_
          obtain ⟨j, hj⟩ := mem_iUnion.1 (not_not.1 hxU)
          by_cases hxt : x ∈ ⋃ i, t i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hxt
            exact mem_iUnion.2 ⟨i, Or.inl hi⟩
          · exact mem_iUnion.2 ⟨j, Or.inr ⟨hj, fun h => h.1 ⟨hxC, hxt⟩⟩⟩
      _ ≤ ∑' j, volume (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1)))) :=
          measure_iUnion_le _
      _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (measure_union_le _ _).trans <|
          (add_le_add (htμ j) (hUμ j).le).trans (ENNReal.add_halves _).le
      _ < ε := hδε
  -- a compact `Q ⊆ A` is bounded, so `Q ⊆ C_j \ t_j` for large `j`
  · intro Q hQ hQA
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball 0
    obtain ⟨j, hj⟩ := exists_nat_ge R
    refine (htu j).mono fun x hx => ⟨⟨(hAA₀ (hQA hx)).1, ?_⟩, fun hxt => ?_⟩
    · exact ball_subset_ball (by linarith) (hR hx)
    · exact (hAA₀ (hQA hx)).2 (mem_iUnion.2 ⟨j, hxt⟩)
/-- **Whitney's hypothesis 1.6(∗) on a large closed set** (Simon Ch. 2, proof of Theorem 1.5).
Let `f : ℝⁿ → ℝ` be `L`-Lipschitz and differentiable at every point of the closed set `C`, with
`Df` continuous on `C`.  The remainder quotient `R(x, y) = |f(y) − f(x) − Df(x)(y − x)| / |y − x|`
is at most `2L`, and `η_k(x) = sup {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}` (`0` off `C`)
tends to `0` on `C`.  Each `{η_k > t}`, `t ≥ 0`, is relatively open in `C`, so `η_k` is Borel,
and Egorov's theorem in closed form gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that
`η_k → 0` uniformly on every compact `Q ⊆ A`.  Then `R(x, y) ≤ η_k(x) < ε'` for `x ∈ Q`,
`y ∈ A`, `0 < |x − y| < 1/(k + 1)`. -/
theorem Submission.codim1_rdo_c1a_whitney_remainder : ∀ (n : ℕ) (f : Euclid n → ℝ) (L : NNReal) (C : Set (Euclid n)), LipschitzWith L f → IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ContinuousOn (fderiv ℝ f) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f L C hf hC hdiff hDf ε hε
  classical
  -- the remainder quotient `R(x, y)`, bounded by `2L` since `‖Df(x)‖ ≤ L`
  let R : Euclid n → Euclid n → ℝ := fun x y => ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖
  have hR_le : ∀ x y, R x y ≤ 2 * L := by
    intro x y
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖y - x‖ + L * ‖y - x‖ := by
          refine add_le_add ?_ ?_
          · rw [← dist_eq_norm, ← dist_eq_norm]
            exact hf.dist_le_mul y x
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      _ = 2 * L * ‖y - x‖ := by ring
  -- `η_k(x) = sup E_k(x)`, `E_k(x) = {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}`, on `C`
  let E : ℕ → Euclid n → Set ℝ := fun k x =>
    R x '' {y | y ∈ C ∧ 0 < dist y x ∧ dist y x < 1 / ((k : ℝ) + 1)}
  let η : ℕ → Euclid n → ℝ := fun k x => if x ∈ C then sSup (E k x) else 0
  have hη_nonneg : ∀ k x, 0 ≤ η k x := by
    intro k x
    by_cases hx : x ∈ C
    · simp only [η, ite_eq_left hx]
      exact Real.sSup_nonneg (by
        rintro _ ⟨y, -, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [η, ite_eq_right hx, le_refl]
  have hR_le_η : ∀ (k : ℕ) x y, x ∈ C → y ∈ C → 0 < dist y x → dist y x < 1 / ((k : ℝ) + 1) →
      R x y ≤ η k x := by
    intro k x y hx hy h0 h1
    simp only [η, ite_eq_left hx]
    exact le_csSup ⟨2 * L, by rintro _ ⟨z, -, rfl⟩; exact hR_le x z⟩ ⟨y, ⟨hy, h0, h1⟩, rfl⟩
  -- `η_k(x) → 0` for `x ∈ C`, by differentiability of `f` at `x`
  have hη_tendsto : ∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hρx⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      simp only [η, ite_eq_left hx]
      refine Real.sSup_le ?_ (half_pos he).le
      rintro _ ⟨y, ⟨-, -, h1⟩, rfl⟩
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos he).le
        (hρx (h1.trans_le ((Nat.one_div_le_one_div hk).trans hN.le)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη_nonneg k x)]
    exact hle.trans_lt (half_lt_self he)
  -- `{η_k > t}` is relatively open in the closed set `C` for `t ≥ 0`, so `η_k` is Borel
  have hη_meas : ∀ k, Measurable (η k) := by
    intro k
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · convert MeasurableSet.univ
      exact eq_univ_of_forall fun x => ht.trans_le (hη_nonneg k x)
    have hUC : η k ⁻¹' Ioi t ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : t < η k x := hx
      simp only [η, ite_eq_right hxC] at hx'
      exact absurd hx' (not_lt.mpr ht)
    have hnhds : ∀ x ∈ η k ⁻¹' Ioi t, η k ⁻¹' Ioi t ∪ Cᶜ ∈ 𝓝 x := by
      intro x hx
      have hxC := hUC hx
      have hxt : t < sSup (E k x) := by
        have hx' : t < η k x := hx
        simpa only [η, ite_eq_left hxC] using hx'
      have hne : (E k x).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Real.sSup_empty] at hxt
        exact absurd hxt (not_lt.mpr ht)
      obtain ⟨_, ⟨y, ⟨hy, h0, h1⟩, rfl⟩, hty⟩ := exists_lt_of_lt_csSup hne hxt
      -- `z ↦ R(z, y)` is continuous within `C` at `x`, as `f` and `Df|_C` are continuous
      have hsub : ContinuousWithinAt (fun z => y - z) C x :=
        continuousWithinAt_const.sub continuousWithinAt_id
      have hnum : ContinuousWithinAt (fun z => ‖f y - f z - fderiv ℝ f z (y - z)‖) C x :=
        ((continuousWithinAt_const.sub hf.continuous.continuousWithinAt).sub
          ((hDf x hxC).clm_apply hsub)).norm
      have hRy : ContinuousWithinAt (fun z => R z y) C x :=
        hnum.div hsub.norm (norm_sub_pos_iff.mpr (dist_pos.mp h0)).ne'
      have hdist : Tendsto (fun z => dist y z) (𝓝 x) (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist tendsto_id
      -- near `x`, every `z ∈ C` has `η_k(z) ≥ R(z, y) > t`
      filter_upwards [eventually_nhdsWithin_iff.mp (Filter.Tendsto.eventually_const_lt hty hRy),
        hdist.eventually_const_lt h0, hdist.eventually_lt_const h1] with z hz hz0 hz1
      by_cases hzC : z ∈ C
      · exact Or.inl ((hz hzC).trans_le (hR_le_η k z y hzC hy hz0 hz1))
      · exact Or.inr hzC
    have heq : η k ⁻¹' Ioi t = C ∩ interior (η k ⁻¹' Ioi t ∪ Cᶜ) := by
      refine Subset.antisymm
        (fun x hx => ⟨hUC hx, mem_interior_iff_mem_nhds.mpr (hnhds x hx)⟩) ?_
      rintro x ⟨hxC, hxI⟩
      rcases interior_subset hxI with hx | hx
      · exact hx
      · exact absurd hxC hx
    rw [heq]
    exact hC.measurableSet.inter isOpen_interior.measurableSet
  -- Egorov on `C`: a closed `A ⊆ C`, `Lⁿ(C \ A) < ε`, with `η_k → 0` uniformly on compact `Q ⊆ A`
  obtain ⟨A, hAC, hA, hCA, hunif⟩ := Submission.codim1_rdo_c1a_egorov_isClosed n C η
    (fun _ => 0) hC.measurableSet hη_meas measurable_const hη_tendsto ε hε
  refine ⟨A, hAC, hA, hCA, fun Q hQ hQA ε' hε' => ?_⟩
  -- `η_k < ε'` on `Q` for some `k`; take `δ = 1/(k + 1)`
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp (hunif Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx y hy hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have h0 : 0 < dist y x := dist_pos.mpr hyx
  have hηx : η k x < ε' := by
    have hkx := hk x hx
    rw [dist_comm, Real.dist_eq, sub_zero] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hR : R x y ≤ ε' :=
    (hR_le_η k x y (hAC (hQA hx)) (hAC hy) h0 (by rwa [dist_comm])).trans hηx.le
  exact (div_le_iff₀ (norm_sub_pos_iff.mpr hyx)).mp hR
/-- **Whitney's `C¹` extension theorem** (Simon Ch. 2, 1.6; proof of Evans–Gariepy §6.5).  If
`A ⊆ ℝⁿ` is closed, `h` and `D` are continuous on `A`, and the remainder
`h y - h x - D x (y - x)` is `o(|y - x|)` uniformly for `x` in compact subsets of `A`, then some
`g ∈ C¹(ℝⁿ)` has `g = h` and `Dg = D` on `A`.  With `r x = min(1, dist(x, A)) / 100`, Vitali's
lemma selects disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `ℝⁿ \ A`;
nearby radii are comparable, so the overlap is uniformly bounded.  Rescaled bumps divided by
their locally finite sum give a partition of unity `w c` on `ℝⁿ \ A` with
`∑ ‖D(w c)(x)‖ ≤ M / r x`.  Put `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`, where
`P b x = h b + D b (x - b)` and `pr c ∈ A` is a nearest point. -/
theorem Submission.codim1_rdo_c1a_whitney_extension : ∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
  intro n A h D hA hh hD hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  -- the Whitney radius `r x = min 1 (dist x A) / 100`
  obtain ⟨r, hr⟩ : ∃ r : Euclid n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := fun x y => by
    have h₁ := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h₁
    have h₂ := (abs_sub_le_iff.mp h₁).1
    rw [hr, hr]; linarith
  -- radii of nearby centres are comparable
  have hnear : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := hrlip x c
    have h₂ := hrlip c x
    rw [dist_comm c x] at h₂
    have := hr0 x
    have := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `Aᶜ`
  obtain ⟨Z, hZA, hZdisj, hZcov⟩ : ∃ Z ⊆ Aᶜ, Z.PairwiseDisjoint (fun c => ball c (r c)) ∧
      ∀ x ∉ A, ∃ c ∈ Z, dist x c < 4 * r c := by
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      simpa only [mem_ball, dist_comm] using lt_of_not_ge hlt
    exact Set.disjoint_left.mp (hZdisj hc hd hcd) hdc (mem_ball_self (hrpos d (hZA hd)))
  -- a `1/2`-separated subset of `B̄(0, 21)` has at most `N` points
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Euclid n), s ⊆ closedBall (0 : Euclid n) 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Euclid n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hssep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Euclid n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Euclid n) ≠ (y : Euclid n) := fun e => hxy' (Subtype.ext e)
      have hd := hssep x.property y.property hne'
      have htri := dist_triangle (x : Euclid n) (c x : Euclid n) (y : Euclid n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Euclid n) (c x : Euclid n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- bounded overlap: at most `N` centres are near any `x ∉ A`
  have hover : ∀ x ∉ A, {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := hrpos x hx
    let f : Euclid n → Euclid n := fun c => (r x)⁻¹ • (c - x)
    have hf : Injective f := by
      intro c d hcd
      have e := congrArg (fun z : Euclid n => r x • z) hcd
      simpa [f, smul_smul, hrx.ne'] using e
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖f c‖ ≤ 21 := by
      intro c hc
      have hd := (hnear x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      simp only [f]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep' : (f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun e => hcd (congrArg f e)
      have hdist := hsep c hc.1 d hd.1 hcd'
      have hrad := (hnear x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        simpa only [dist_eq_norm] using hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      simp only [f]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Euclid n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep'
    exact ⟨hfin.of_finite_image hf.injOn, by rwa [Set.ncard_image_of_injective _ hf] at hcard⟩
  -- the finite set `F x` of centres near `x ∉ A`
  have hfin : ∀ x ∉ A, {c : Z | dist x c ≤ r x + 10 * r c}.Finite := by
    intro x hx
    apply ((hover x hx).1.preimage (Subtype.val_injective (p := (· ∈ Z))).injOn).subset
    intro c hc
    exact ⟨c.property, hc⟩
  have hFex : ∀ x, ∃ s : Finset Z, x ∉ A → ∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun hx' => absurd hx hx'⟩
    · exact ⟨(hfin x hx).toFinset, fun _ c => by simp⟩
  choose F hF using hFex
  have hFcard : ∀ x ∉ A, (F x).card ≤ N := by
    intro x hx
    have hsub : (F x).map (Embedding.subtype _) ⊆ (hover x hx).1.toFinset := by
      intro c hc
      simp only [Finset.mem_map, Embedding.coe_subtype] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Set.Finite.mem_toFinset]
      exact ⟨c'.property, (hF x hx c').mp hc'⟩
    calc (F x).card = ((F x).map (Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (hover x hx).1.toFinset.card := Finset.card_le_card hsub
      _ = {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard :=
          (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ N := (hover x hx).2
  -- a smooth bump `ψ = 1` on `B̄(0, 4)`, `ψ = 0` off `B(0, 8)`
  obtain ⟨ψ, hψc, hψ0, hψ1, hψin, hψout, L, hL⟩ : ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 4 → ψ x = 1) ∧
      (∀ x, 8 ≤ ‖x‖ → ψ x = 0) ∧ ∃ L : NNReal, LipschitzWith L ψ := by
    let b : ContDiffBump (0 : Euclid n) := ⟨4, 8, by norm_num, by norm_num⟩
    have hb : ContDiff ℝ 1 b := b.contDiff
    obtain ⟨L, hL⟩ := hb.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
    refine ⟨b, hb, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_, fun x hx => ?_, L, hL⟩
    · exact b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    · apply notMem_support.mp
      rw [b.support_eq]
      exact fun hxb => absurd (mem_ball_zero_iff.mp hxb) (not_lt.mpr hx)
  -- the rescaled bumps `φ c x = ψ ((x - c) / r c)`
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid n → Euclid n → ℝ, ∀ c x, φ c x = ψ ((r c)⁻¹ • (x - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφfun : ∀ c, φ c = fun x => ψ ((r c)⁻¹ • (x - c)) := fun c => funext (hφ c)
  have hφc : ∀ c, ContDiff ℝ 1 (φ c) := by
    intro c
    rw [hφfun c]
    exact hψc.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hφ0 : ∀ c x, 0 ≤ φ c x := fun c x => by rw [hφ]; exact hψ0 _
  have hφin : ∀ c x, 0 < r c → dist x c ≤ 4 * r c → φ c x = 1 := by
    intro c x hc hx
    rw [hφ]
    apply hψin
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (r c)⁻¹ * dist x c ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have hφout : ∀ c x, 0 < r c → 8 * r c ≤ dist x c → φ c x = 0 := by
    intro c x hc hx
    rw [hφ]
    apply hψout
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * dist x c := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, hBb⟩ : ∃ B : ℝ, 0 < B ∧ ∀ c, 0 < r c → ∀ x, ‖fderiv ℝ (φ c) x‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c hc x => ?_⟩
    let ρ : NNReal := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Euclid n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (φ c) := by
      rw [hφfun c]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (φ c) x‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- near `x ∉ A`, only the bumps indexed by `F x` are active
  have hφzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc
    apply hφout c y (hrpos c (hZA c.property))
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun e => hc ((hF x hx c).mpr e)
    have ht := dist_triangle x y (c : Euclid n)
    rw [dist_comm x y] at ht
    have := hr0 (c : Euclid n)
    linarith
  have hyA : ∀ x ∉ A, ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA'
    have hi := infDist_le_dist_of_mem (x := x) hyA'
    have hr' := hrd x
    rw [dist_comm x y] at hi
    linarith [hr0 x]
  -- the locally finite sum `S = ∑ φ c`
  obtain ⟨S, hS⟩ : ∃ S : Euclid n → ℝ, ∀ x, S x = ∑ᶠ c : Z, φ c x := ⟨_, fun _ => rfl⟩
  have hSnear : ∀ x ∉ A, ∀ y, dist y x < r x → S y = ∑ c ∈ F x, φ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hcF
    exact hc (hφzero x hx y hy c hcF)
  have hSev : ∀ x ∉ A, S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSnear x hx y hy
  have hSc : ∀ x ∉ A, ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (c : Z) y => φ c y) (s := F x) fun c _ => hφc c).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hSfd : ∀ x ∉ A, fderiv ℝ S x = ∑ c ∈ F x, fderiv ℝ (φ c) x := by
    intro x hx
    rw [(hSev x hx).fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (hφc c).differentiable one_ne_zero x)
  have hS1 : ∀ x ∉ A, 1 ≤ S x := by
    intro x hx
    have hrx := hrpos x hx
    rw [hSnear x hx x (by simpa using hrx)]
    obtain ⟨c, hc, hxc⟩ := hZcov x hx
    have hi : (⟨c, hc⟩ : Z) ∈ F x := by
      rw [hF x hx]
      have := hr0 c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = φ c x := (hφin c x (hrpos c (hZA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, φ c x :=
          Finset.single_le_sum (f := fun c : Z => φ c x) (fun c _ => hφ0 c x) hi
  -- the partition of unity `w c = φ c / S` on `Aᶜ`
  obtain ⟨w, hw⟩ : ∃ w : Z → Euclid n → ℝ, ∀ c x, w c x = φ c x / S x := ⟨_, fun _ _ => rfl⟩
  have hwfun : ∀ c, w c = fun x => φ c x / S x := fun c => funext (hw c)
  have hwc : ∀ c : Z, ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    rw [hwfun c]
    exact (hφc c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hw0 : ∀ c : Z, ∀ x ∉ A, 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (hφ0 c x) (le_trans zero_le_one (hS1 x hx))
  have hwzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, hφzero x hx y hy c hc, zero_div]
  have hwsum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ F x, w c y = 1 := by
    intro x hx y hy
    simp only [hw, ← Finset.sum_div, ← hSnear x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hyA x hx y hy))))
  have hwdsum : ∀ x ∉ A, ∑ c ∈ F x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hwsum x hx y hy
    have hh' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh'
    rw [fderiv_fun_sum (fun c _ => (hwc c x hx).differentiableAt one_ne_zero)] at hh'
    exact hh'
  have hwd_le : ∀ x ∉ A, ∀ c : Z,
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro x hx c
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hSi : (S x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1x
    have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ S x ^ 2 by nlinarith)
    have hb := ((hφc c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x := by
      simpa only [hwfun, div_eq_mul_inv, Function.comp_def] using hprod.fderiv
    rw [hder]
    have hb0 := hφ0 c x
    have hb1 : φ c x ≤ 1 := by rw [hφ]; exact hψ1 _
    calc ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x‖
        ≤ ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (φ c) x‖ :=
          norm_add_le _ _
      _ = φ c x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (φ c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (φ c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
  -- `∑_{c ∈ F x} ‖D w_c(x)‖ ≤ M / r x`
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∉ A, ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * B / r x := ⟨_, rfl⟩
    have hT : 0 ≤ T := by rw [hT_def]; positivity
    have hb' : ∀ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ T := by
      intro c hc
      have hcr := hrpos c (hZA c.property)
      have hlow := (hnear x c ((hF x hx c).mp hc)).1
      refine (hBb c hcr x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = T := by rw [hT_def]; ring
    have hcard : ((F x).card : ℝ) ≤ N := by exact_mod_cast hFcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSfd x hx]
      calc ‖∑ c ∈ F x, fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ F x, T := Finset.sum_le_sum hb'
        _ = ((F x).card : ℝ) * T := by simp
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ T + (N : ℝ) * T := fun c hc =>
      (hwd_le x hx c).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ F x, (T + (N : ℝ) * T) := Finset.sum_le_sum hw'
      _ = ((F x).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
  -- the affine jets `P b x = h b + D b (x - b)`
  obtain ⟨P, hP⟩ : ∃ P : Euclid n → Euclid n → ℝ, ∀ b x, P b x = h b + D b (x - b) :=
    ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ b, P b = fun x => h b + D b (x - b) := fun b => funext (hP b)
  have hPc : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    rw [hPfun b]
    exact contDiff_const.add ((D b).contDiff.comp (contDiff_id.sub contDiff_const))
  have hPd : ∀ b x, HasFDerivAt (P b) (D b) x := by
    intro b x
    have e := (((D b).hasFDerivAt (x := x)).sub_const (D b b)).const_add (h b)
    have hfun : (fun y => h b + D b (y - b)) = fun y => h b + (D b y - D b b) := by
      funext y
      rw [map_sub]
    rw [hPfun b, hfun]
    exact e
  have hPsub : ∀ a b x,
      ‖P b x - P a x‖ ≤ ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
    intro a b x
    have heq : P b x - P a x = (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
      have hx : x - a = (x - b) + (b - a) := by abel
      simp only [hP, hx, map_add, sub_apply]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))
  -- nearest points `pr x ∈ A`
  choose pr hprA hprd using fun x => hA.exists_infDist_eq_dist hne x
  have hprle : ∀ x, ∀ a ∈ A, dist x (pr x) ≤ dist x a := by
    intro x a ha
    rw [← hprd x]
    exact infDist_le_dist_of_mem ha
  have hpr2 : ∀ x, ∀ a ∈ A, dist (pr x) a ≤ 2 * dist x a := by
    intro x a ha
    have ht := dist_triangle (pr x) x a
    rw [dist_comm (pr x) x] at ht
    linarith [hprle x a ha]
  have hanc1 : ∀ x ∉ A, ∀ c : Z, c ∈ F x → dist x (pr c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hd := (hnear x c ((hF x hx c).mp hc)).2.2
    have hr' := hrd x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Euclid n)) (y := x)
    have ht := dist_triangle x (c : Euclid n) (pr c)
    rw [dist_comm (c : Euclid n) x] at hi
    rw [← hprd (c : Euclid n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have hanc2 : ∀ x ∉ A, ∀ a ∈ A, ∀ c : Z, c ∈ F x → dist (pr c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := hanc1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (pr c) x a
    rw [dist_comm (pr c) x] at ht
    linarith
  -- uniform estimates near a point of `A`
  have hloc : ∀ a ∈ A, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ η) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ η * ‖c - b‖ := by
    intro a ha η hη
    obtain ⟨r₀, hr₀, hrem₀⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left η hη
    obtain ⟨η₀, hη₀, hD₀⟩ := Metric.continuousWithinAt_iff.mp (hD a ha) η hη
    have hδ1 : min 1 (min η₀ (r₀ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η₀ (r₀ / 3)) ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hδr : min 1 (min η₀ (r₀ / 3)) ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η₀ (r₀ / 3)), lt_min one_pos (lt_min hη₀ (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      simpa only [dist_eq_norm] using (hD₀ hb (hba.trans_le hδη)).le
    · intro b hb hba c hc hca
      apply hrem₀ b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- convex combinations
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : Finset Z)
      (a : Z → ℝ) (v : Z → G) (b : ℝ), (∀ i ∈ s, 0 ≤ a i) → ∑ i ∈ s, a i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, a i • v i‖ ≤ b := by
    intro G _ _ s a v b ha hs hv
    calc ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, a i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (ha i hi)]
      _ ≤ ∑ i ∈ s, a i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (ha i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- the extension: `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid n → ℝ, ∀ x,
      g x = if x ∈ A then h x else ∑ᶠ c : Z, w c x * P (pr c) x := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgnear : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hyA x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (pr c) y = 0
    rw [hwzero x hx y hy c hc', zero_mul]
  have hgev : ∀ x ∉ A, g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgnear x hx y hy
  have hgc : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ F x, w c y * P (pr c) y) x :=
      ContDiffAt.sum (fun c _ => (hwc c x hx).mul (hPc _).contDiffAt)
    exact hs.congr_of_eventuallyEq (hgev x hx)
  have hgfd : ∀ x ∉ A, fderiv ℝ g x =
      ∑ c ∈ F x, (w c x • D (pr c) + P (pr c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(hgev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((hwc c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hPd _ x)
  -- `Dg = D` on `A`
  have hgd : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, -, hDδ, hremδ⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by simpa using hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA]
      have hr' := hremδ a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hxx : dist x x < r x := by simpa using hrpos x hxA
      have hid : g x - h a - D a (x - a) = ∑ c ∈ F x, w c x • (P (pr c) x - P a x) := by
        rw [hgnear x hxA x hxx]
        simp only [smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum x hxA x hxx, one_mul, hP a x]
        ring
      rw [hid]
      apply hconv (F x) (fun c => w c x) (fun c => P (pr c) x - P a x) _
        (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx)
      intro c hc
      have hbA := hprA (c : Euclid n)
      have hba := hanc2 x hxA a ha c hc
      have hxb : dist x (pr c) ≤ 2 * dist x a :=
        (hanc1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr c) hbA hbaδ
      have hr' := hremδ a ha haa (pr c) hbA hbaδ
      have hba' : ‖pr c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
      have hxb' : ‖x - pr c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
      calc ‖P (pr c) x - P a x‖
          ≤ ‖h (pr c) - h a - D a (pr c - a)‖ + ‖D (pr c) - D a‖ * ‖x - pr c‖ :=
            hPsub a (pr c) x
        _ ≤ (ε / 5) * ‖pr c - a‖ + (ε / 5) * ‖x - pr c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  -- `Dg` is continuous at the points of `A`
  have hgcont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by rw [hη_def]; field_simp
    have hηε : η ≤ ε / 2 := by nlinarith [mul_pos hη hM]
    obtain ⟨δ, hδ, hδ1, hDδ, hremδ⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [(hgd a ha).fderiv, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [(hgd x hxA).fderiv]
      exact (hDδ x hxA (by linarith)).trans hηε
    · have hrx := hrpos x hxA
      have hxx : dist x x < r x := by simpa using hrx
      have hbA := hprA x
      have hbaδ : dist (pr x) a < δ := by
        linarith [hpr2 x a ha, dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := by
        rw [hr x, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ F x, ‖D (pr c) - D a‖ ≤ η := by
        intro c hc
        apply hDδ _ (hprA c)
        have hi := hanc2 x hxA a ha c hc
        linarith [dist_nonneg (x := x) (y := a)]
      have hP' : ∀ c ∈ F x, ‖P (pr c) x - P (pr x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA := hprA (c : Euclid n)
        have hda := hanc2 x hxA a ha c hc
        have hdaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
        have hxd := hanc1 x hxA c hc
        have hxb : dist x (pr x) = infDist x A := (hprd x).symm
        have hdb : dist (pr c) (pr x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (pr c) x (pr x)
          rw [dist_comm (pr c) x, hxb] at ht
          linarith
        have hDd : ‖D (pr c) - D (pr x)‖ ≤ 2 * η := by
          calc ‖D (pr c) - D (pr x)‖ = ‖(D (pr c) - D a) - (D (pr x) - D a)‖ := by
                congr 1; abel
            _ ≤ ‖D (pr c) - D a‖ + ‖D (pr x) - D a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hremδ (pr x) hbA hbaδ (pr c) hdA hdaδ
        have hdb' : ‖pr c - pr x‖ ≤ 3 * infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - pr c‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
        calc ‖P (pr c) x - P (pr x) x‖
            ≤ ‖h (pr c) - h (pr x) - D (pr x) (pr c - pr x)‖ +
                ‖D (pr c) - D (pr x)‖ * ‖x - pr c‖ := hPsub (pr x) (pr c) x
          _ ≤ η * ‖pr c - pr x‖ + (2 * η) * ‖x - pr c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hsplit : fderiv ℝ g x - D a = (∑ c ∈ F x, w c x • (D (pr c) - D a)) +
          ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x := by
        rw [hgfd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hwsum x hxA x hxx, hwdsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hsplit]
      calc ‖(∑ c ∈ F x, w c x • (D (pr c) - D a)) +
            ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ F x, w c x • (D (pr c) - D a)‖ +
              ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact hconv (F x) (fun c => w c x) (fun c => D (pr c) - D a) η
                (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx) hD'
            · calc ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ F x, ‖(P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ c ∈ F x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ :=
                    (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = ε / 2 := heq
  refine ⟨g, ?_, fun a ha => hgA a ha, hgd⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (hgd x hx).differentiableAt
    · exact (hgc x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact hgcont x hx
    · exact (hgc x hx).continuousAt_fderiv one_ne_zero
/-- **`C¹` approximation** (Simon Ch. 2, Theorem 1.5).  If `f : ℝⁿ → ℝ` is `K`-Lipschitz and
`ε > 0`, there is `g ∈ C¹(ℝⁿ)` with `Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) < ε`.  By Rademacher (1.4) `f` is
differentiable on a Borel set `B` of full measure.  Lusin gives a closed `C ⊆ B` with `Df|C`
continuous and `Lⁿ(B \ C) < ε/2`; the remainder estimate gives a closed `A ⊆ C` with
`Lⁿ(C \ A) < ε/2` on which `f, Df` satisfy Whitney's condition 1.6(∗); Whitney's extension
theorem (1.6) gives `g ∈ C¹` with `g = f` and `Dg = Df` on `A`.  The exceptional set lies in
`Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.codim1_rdo_c1_approximation : ∀ (n : ℕ) (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n f K hf ε hε
  -- Rademacher: `f` is differentiable on the Borel set `B`, whose complement is null
  set B : Set (Euclid n) := {x | DifferentiableAt ℝ f x}
  have hBm : MeasurableSet B := measurableSet_of_differentiableAt ℝ f
  have hBc : volume Bᶜ = 0 := ae_iff.mp hf.ae_differentiableAt
  -- Lusin: a closed `C ⊆ B` with `Df` continuous on `C` and `Lⁿ(B \ C) < ε/2`
  obtain ⟨C, hCB, hC, hDC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed n (fderiv ℝ f) B
    (measurable_fderiv ℝ f) hBm (ε / 2) (ENNReal.half_pos hε.ne')
  -- a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2` on which Whitney's condition 1.6(∗) holds
  obtain ⟨A, hAC, hA, hCA, hR⟩ := Submission.codim1_rdo_c1a_whitney_remainder n f K C hf hC
    (fun x hx => hCB hx) hDC (ε / 2) (ENNReal.half_pos hε.ne')
  -- Whitney: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`
  obtain ⟨g, hg, hgf, hDg⟩ := Submission.codim1_rdo_c1a_whitney_extension n A f (fderiv ℝ f) hA
    hf.continuous.continuousOn (hDC.mono hAC) hR
  refine ⟨g, hg, ?_⟩
  -- the exceptional set misses `A`, and `Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume (Bᶜ ∪ (B \ C) ∪ (C \ A)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · rcases hx with hfg | hfg
          · exact absurd (hgf hxA).symm hfg
          · exact absurd (hDg x hxA).fderiv.symm hfg
        by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
    _ ≤ volume (Bᶜ ∪ (B \ C)) + volume (C \ A) := measure_union_le _ _
    _ ≤ volume Bᶜ + volume (B \ C) + volume (C \ A) := by gcongr; exact measure_union_le _ _
    _ < ε / 2 + ε / 2 := by
        rw [hBc, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε
/-- **`C¹` approximation of Lipschitz functions** (Simon Ch. 2, Theorem 1.5).  If `f : ℝⁿ → ℝ` is
Lipschitz and `ε > 0`, some `g ∈ C¹(ℝⁿ)` has `Lⁿ({f ≠ g} ∪ {Df ≠ Dg}) < ε`.  By Rademacher, `f`
is differentiable off the null Borel set `Bᶜ`, and `Df` is Borel.  Lusin gives a closed `C ⊆ B`
with `Lⁿ(B \ C) < ε/2` on which `Df` is continuous; the remainder suprema and Egorov give a closed
`A ⊆ C` with `Lⁿ(C \ A) < ε/2` satisfying Whitney's hypothesis 1.6(∗) for `h = f`, `D = Df`; and
Whitney's extension gives `g ∈ C¹` with `g = f`, `Dg = Df` on `A`, so the bad set lies in
`Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.dtc_bc_lc_sl_c1_approx : ∀ (n : ℕ) (f : Euclid n → ℝ) (K : NNReal), LipschitzWith K f → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x} < ε := by
  intro n f K hf ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- Rademacher: `f` is differentiable on the Borel set `B` with `Lⁿ(Bᶜ) = 0`, and `Df` is Borel
  set B : Set (Euclid n) := {x | DifferentiableAt ℝ f x}
  have hBc : volume Bᶜ = 0 := ae_iff.mp (hf.ae_differentiableAt (μ := volume))
  -- Lusin: a closed `C ⊆ B` with `Lⁿ(B \ C) < ε/2` on which `Df` is continuous
  obtain ⟨C, hCB, hC, hDfC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed n (fderiv ℝ f) B
    (measurable_fderiv ℝ f) (measurableSet_of_differentiableAt ℝ f) (ε / 2) hε2
  -- Whitney's hypothesis 1.6(∗) for `h = f`, `D = Df` on a closed `A ⊆ C` with `Lⁿ(C \ A) < ε/2`
  obtain ⟨A, hAC, hA, hCA, hrem⟩ :=
    Submission.codim1_rdo_c1a_whitney_remainder n f K C hf hC (fun x hx => hCB hx) hDfC (ε / 2) hε2
  -- Whitney's extension: `g ∈ C¹` with `g = f` and `Dg = Df` on `A`
  obtain ⟨g, hg, hgf, hgD⟩ := Submission.codim1_rdo_c1a_whitney_extension n A f (fderiv ℝ f) hA
    hf.continuous.continuousOn (hDfC.mono hAC) hrem
  refine ⟨g, hg, ?_⟩
  -- the bad set lies in `Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {x | f x ≠ g x ∨ fderiv ℝ f x ≠ fderiv ℝ g x}
      ≤ volume (Bᶜ ∪ (B \ C) ∪ (C \ A)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ A
        · rcases hx with hx | hx
          · exact absurd (hgf hxA).symm hx
          · exact absurd (hgD x hxA).fderiv.symm hx
        by_cases hxC : x ∈ C
        · exact Or.inr ⟨hxC, hxA⟩
        by_cases hxB : x ∈ B
        · exact Or.inl (Or.inr ⟨hxB, hxC⟩)
        · exact Or.inl (Or.inl hxB)
    _ ≤ volume Bᶜ + volume (B \ C) + volume (C \ A) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = volume (B \ C) + volume (C \ A) := by rw [hBc, zero_add]
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε
/-- **Flat Fubini in product coordinates** (step 3(a) of the chart co-area argument).  Put
`S = Ω ∩ Θ⁻¹(Y')` and `H = 𝟙_S |det DΘ| f ∘ Θ`, where `Θ` is `C¹` and injective on the open set
`Ω` and `Y' ⊆ Θ(Ω)` is Borel.  `S` is Borel (`Θ` is continuous on `Ω`) and `Θ(S) = Y'`, so the
injective change of variables gives `∫_{Y'} f = ∫ H`.  The map `(t, w) ↦ c(t, w) = (t, w₀, …)`
is a measure-preserving equivalence `ℝ × ℝⁿ ≅ ℝⁿ⁺¹`, so by Tonelli `t ↦ ∫ H(c(t, w)) dw` is Borel
and `∫∫ H(c(t, w)) dw dt = ∫ H`. -/
theorem Submission.dtc_bc_lc_sl_cc_flat_fubini : ∀ (n : ℕ) (c : ℝ → Euclid n → Euclid (n + 1)) (Ω Y' : Set (Euclid (n + 1))) (Θ : Euclid (n + 1) → Euclid (n + 1)) (f : Euclid (n + 1) → ℝ≥0∞), (∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i) → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → Measurable f → MeasurableSet Y' → Y' ⊆ Θ '' Ω → Measurable (fun t => ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w)) ∧ ∫⁻ t, ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w) = ∫⁻ y in Y', f y := by
  intro n c Ω Y' Θ f hc hΩ hΘ hinj hf hY hYΩ
  classical
  -- the extension of `Θ` by `0` off `Ω` is Borel and agrees with `Θ` on `Ω`
  have hΘ' : Measurable (Ω.piecewise Θ 0) :=
    hΘ.continuousOn.measurable_piecewise continuousOn_const hΩ.measurableSet
  -- `S = Ω ∩ Θ⁻¹(Y')` is Borel
  have hS : MeasurableSet (Ω ∩ Θ ⁻¹' Y') := by
    have : Ω ∩ Θ ⁻¹' Y' = Ω ∩ Ω.piecewise Θ 0 ⁻¹' Y' := by
      ext z
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_right fun hz => by rw [piecewise_eq_of_mem _ _ _ hz]
    rw [this]
    exact hΩ.measurableSet.inter (hΘ' hY)
  -- `Θ(S) = Y'`, since `Y' ⊆ Θ(Ω)`
  have himage : Θ '' (Ω ∩ Θ ⁻¹' Y') = Y' := by
    refine Subset.antisymm (by rintro _ ⟨z, ⟨-, hz⟩, rfl⟩; exact hz) fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := hYΩ hy
    exact ⟨z, ⟨hz, hy⟩, rfl⟩
  -- injective change of variables: `∫_{Y'} f = ∫_S |det DΘ| f ∘ Θ`
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (fun z hz => ((hΘ.differentiableOn one_ne_zero z hz.1).differentiableAt
      (hΩ.mem_nhds hz.1)).hasFDerivAt.hasFDerivWithinAt) (hinj.mono inter_subset_left) f
  rw [himage] at hcov
  -- `H` is Borel: on `S`, `Θ` agrees with its Borel extension, and `DΘ` is Borel
  have hH : Measurable ((Ω ∩ Θ ⁻¹' Y').indicator
      fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) := by
    rw [indicator_congr (g := fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| *
      f (Ω.piecewise Θ 0 z)) fun z hz => by simp only [piecewise_eq_of_mem _ _ _ hz.1]]
    exact ((ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ Θ)))).mul
        (hf.comp hΘ')).indicator hS
  -- `(t, w) ↦ c(t, w)` is measure preserving, as the composite of the coordinate equivalences
  -- `ℝ × ℝⁿ ≅ ℝ × (Fin n → ℝ) ≅ (Fin (n + 1) → ℝ) ≅ ℝⁿ⁺¹`
  have hcoord : MeasurePreserving (fun p : ℝ × Euclid n => c p.1 p.2)
      (volume.prod volume) volume := by
    convert (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.comp
        ((MeasurePreserving.id volume).prod
          (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)))) using 1
    funext ⟨t, w⟩
    ext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [(hc t w).1]
    · simp [(hc t w).2 i]
  -- Tonelli on `ℝ × ℝⁿ`, then the change of coordinates and the change of variables
  have hG : Measurable fun p : ℝ × Euclid n => (Ω ∩ Θ ⁻¹' Y').indicator
      (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c p.1 p.2) :=
    hH.comp hcoord.measurable
  refine ⟨hG.lintegral_prod_right', ?_⟩
  rw [← lintegral_prod _ hG.aemeasurable, hcoord.lintegral_comp hH, lintegral_indicator hS,
    hcov]
/-- **Eilenberg's covering estimate at one scale** (Simon Ch. 2, proof of Theorem 1.9: (1), `gᵢ`
and (2), case `m = 1`).  Choose a `δ`-cover `(Cᵢ)` of `A` with `∑ᵢ (diam Cᵢ)^(d+1)` below
`μH[d+1] A + ε`.  Then `ψ = ∑ᵢ (diam Cᵢ)ᵈ 𝟙_{f (closure Cᵢ)}` is Borel (the images are
σ-compact), the sets `closure Cᵢ ∩ A ∩ f⁻¹{t}` form a `δ`-cover of `A ∩ f⁻¹{t}` whose sum is at
most `ψ t`, and `L¹ (f (closure Cᵢ)) ≤ diam f (closure Cᵢ) ≤ L diam Cᵢ` bounds `∫ ψ`. -/
theorem Submission.dtc_bc_lc_sl_eil_scale : ∀ (P d : ℕ) (A : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (δ ε : ℝ≥0∞), LipschitzWith L f → 0 < δ → 0 < ε → μH[((d + 1 : ℕ) : ℝ)] A ≠ ∞ → ∃ ψ : ℝ → ℝ≥0∞, Measurable ψ ∧ (∀ t : ℝ, (⨅ (c : ℕ → Set (Euclid P)) (_ : A ∩ f ⁻¹' {t} ⊆ ⋃ i, c i) (_ : ∀ i, Metric.ediam (c i) ≤ δ), ∑' i, ⨆ _ : (c i).Nonempty, Metric.ediam (c i) ^ (d : ℝ)) ≤ ψ t) ∧ ∫⁻ t, ψ t ≤ (L : ℝ≥0∞) * (μH[((d + 1 : ℕ) : ℝ)] A + ε) := by
  intro P d A f L δ ε hf hδ hε hA
  -- Simon's (1): a `δ`-cover `C` of `A` whose `(d + 1)`-sum is below `μH[d + 1] A + ε`
  have hcover : (⨅ (C : ℕ → Set (Euclid P)) (_ : A ⊆ ⋃ i, C i) (_ : ∀ i, ediam (C i) ≤ δ),
      ∑' i, ⨆ _ : (C i).Nonempty, ediam (C i) ^ (((d + 1 : ℕ) : ℝ))) <
        μH[((d + 1 : ℕ) : ℝ)] A + ε := by
    refine lt_of_le_of_lt ?_ (ENNReal.lt_add_right hA hε.ne')
    rw [Measure.hausdorffMeasure_apply]
    exact le_iSup₂_of_le δ hδ le_rfl
  obtain ⟨C, hcover⟩ := iInf_lt_iff.1 hcover
  obtain ⟨hAC, hcover⟩ := iInf_lt_iff.1 hcover
  obtain ⟨hCδ, hsum⟩ := iInf_lt_iff.1 hcover
  -- the images `f (closure (C i))` are σ-compact, hence Borel
  have hK : ∀ i, MeasurableSet (f '' closure (C i)) := fun i => by
    obtain ⟨K, hKc, hKu⟩ := (isSigmaCompact_univ.of_isClosed_subset isClosed_closure
      (subset_univ (closure (C i)))).image hf.continuous
    rw [← hKu]
    exact MeasurableSet.iUnion fun j => (hKc j).measurableSet
  -- Simon's `gᵢ`: `ψ = ∑ᵢ (diam Cᵢ)ᵈ 𝟙_{f (closure Cᵢ)}`
  refine ⟨fun t => ∑' i, (f '' closure (C i)).indicator (fun _ => ediam (C i) ^ (d : ℝ)) t,
    Measurable.tsum fun i => measurable_const.indicator (hK i), fun t => ?_, ?_⟩
  · -- Simon's (2): `(closure Cᵢ ∩ A ∩ f⁻¹{t})ᵢ` is an admissible `δ`-cover of `A ∩ f⁻¹{t}`
    refine iInf_le_of_le (fun i => closure (C i) ∩ (A ∩ f ⁻¹' {t})) <|
      iInf_le_of_le (fun x hx => ?_) <| iInf_le_of_le (fun i => ?_) <|
        ENNReal.tsum_le_tsum fun i => iSup_le fun ⟨x, hxC, _, hxt⟩ => ?_
    · obtain ⟨i, hi⟩ := mem_iUnion.1 (hAC hx.1)
      exact mem_iUnion.2 ⟨i, subset_closure hi, hx⟩
    · exact (ediam_mono inter_subset_left).trans ((ediam_closure _).trans_le (hCδ i))
    · rw [indicator_of_mem (show t ∈ f '' closure (C i) from ⟨x, hxC, hxt⟩)]
      exact ENNReal.rpow_le_rpow ((ediam_mono inter_subset_left).trans (ediam_closure _).le)
        (Nat.cast_nonneg d)
  · -- integrate term by term: `L¹ (f (closure Cᵢ)) ≤ diam f (closure Cᵢ) ≤ L diam Cᵢ`
    rw [lintegral_tsum fun i => (measurable_const.indicator (hK i)).aemeasurable]
    calc ∑' i, ∫⁻ t, (f '' closure (C i)).indicator (fun _ => ediam (C i) ^ (d : ℝ)) t
        ≤ ∑' i, (L : ℝ≥0∞) * ⨆ _ : (C i).Nonempty, ediam (C i) ^ (((d + 1 : ℕ) : ℝ)) := by
          refine ENNReal.tsum_le_tsum fun i => ?_
          rw [lintegral_indicator_const (hK i)]
          rcases (C i).eq_empty_or_nonempty with hC | hC
          · simp [hC]
          rw [iSup_pos hC, ENNReal.rpow_natCast, ENNReal.rpow_natCast, pow_succ]
          calc ediam (C i) ^ d * volume (f '' closure (C i))
              ≤ ediam (C i) ^ d * (L * ediam (C i)) := by
                gcongr
                exact (Real.volume_le_diam _).trans
                  ((hf.ediam_image_le _).trans_eq (by rw [ediam_closure]))
            _ = L * (ediam (C i) ^ d * ediam (C i)) := by ring
      _ = L * ∑' i, ⨆ _ : (C i).Nonempty, ediam (C i) ^ (((d + 1 : ℕ) : ℝ)) :=
          ENNReal.tsum_mul_left
      _ ≤ L * (μH[((d + 1 : ℕ) : ℝ)] A + ε) := mul_le_mul_right hsum.le _
/-- **Passage to the limit** (Simon Ch. 2, proof of Theorem 1.9, "letting `i → ∞`").  If the
`δ_k`-scale Hausdorff contents of `S t` are majorized by Borel functions `ψ_k` with
`∫ ψ_k ≤ B + ε_k`, where `δ_k → 0` and `ε_k → 0`, then `φ = liminf_k ψ_k` is a Borel majorant
of `t ↦ μH[d] (S t)` with `∫ φ ≤ B`: at a scale `r > 0` the content is eventually below
`ψ_k t` (coarser scales have smaller content), and Fatou's lemma bounds `∫ φ`. -/
theorem Submission.dtc_bc_lc_sl_eil_limit : ∀ (P : ℕ) (d : ℝ) (S : ℝ → Set (Euclid P)) (ψ : ℕ → ℝ → ℝ≥0∞) (δ ε : ℕ → ℝ≥0∞) (B : ℝ≥0∞), (∀ k, Measurable (ψ k)) → Tendsto δ atTop (𝓝 0) → Tendsto ε atTop (𝓝 0) → (∀ k t, (⨅ (c : ℕ → Set (Euclid P)) (_ : S t ⊆ ⋃ i, c i) (_ : ∀ i, Metric.ediam (c i) ≤ δ k), ∑' i, ⨆ _ : (c i).Nonempty, Metric.ediam (c i) ^ d) ≤ ψ k t) → (∀ k, ∫⁻ t, ψ k t ≤ B + ε k) → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t, μH[d] (S t) ≤ φ t) ∧ ∫⁻ t, φ t ≤ B := by
  intro P d S ψ δ ε B hψ hδ hε hcontent hint
  refine ⟨fun t => liminf (fun k => ψ k t) atTop, Measurable.liminf hψ, fun t => ?_, ?_⟩
  · -- `μH[d] (S t)` is the supremum over scales `r > 0` of the content at scale `r`
    rw [Measure.hausdorffMeasure_apply]
    refine iSup₂_le fun r hr => le_liminf_of_le (h := ?_)
    -- eventually `δ_k ≤ r`, and a cover with diameters `≤ δ_k` is admissible at scale `r`
    filter_upwards [hδ.eventually_le_const hr] with k hk
    refine le_trans ?_ (hcontent k t)
    exact le_iInf fun c => le_iInf fun hc => le_iInf fun hcδ =>
      iInf_le_of_le c <| iInf_le_of_le hc <| iInf_le_of_le (fun i => (hcδ i).trans hk) le_rfl
  · -- Fatou's lemma, then `B + ε_k → B`
    calc ∫⁻ t, liminf (fun k => ψ k t) atTop ≤ liminf (fun k => ∫⁻ t, ψ k t) atTop :=
          lintegral_liminf_le hψ
      _ ≤ liminf (fun k => B + ε k) atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = B := by rw [(tendsto_const_nhds.add hε).liminf_eq, add_zero]
/-- A uniform lower Lipschitz bound for an injective `C¹` immersion on a compact set (step 2,
"Lower", of the `C¹`-tangent argument): if `U` is open, `K ⊆ U` is compact, `g` is `C¹` on `U`,
injective on `K`, and `Dg(z)` is injective for every `z ∈ K`, then `m|a − b| ≤ |g(a) − g(b)|` on
`K` for some `m > 0`.  Otherwise `|g(a_k) − g(b_k)| < (k + 1)⁻¹|a_k − b_k|` for some `a_k ≠ b_k`
in `K`; along a subsequence `a_k → a`, `b_k → b` and the unit vectors `e_k ∥ a_k − b_k` converge
to some `e`.  If `a ≠ b` then `g(a) = g(b)`; if `a = b` then strict differentiability of `g` at `a`
gives `Dg(a)e = 0` with `|e| = 1`. -/
theorem Submission.dtc_bc_lc_sl_c1t_lower_lipschitz : ∀ (P d : ℕ) (g : Euclid d → Euclid P) (U K : Set (Euclid d)), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → InjOn g K → (∀ z ∈ K, Injective (fderiv ℝ g z)) → ∃ m : ℝ, 0 < m ∧ ∀ a ∈ K, ∀ b ∈ K, m * ‖a - b‖ ≤ ‖g a - g b‖ := by
  intro P d g U K hU hK hKU hg hinj hDinj
  by_contra hcon
  push Not at hcon
  -- for each `k` there are `a_k, b_k ∈ K` with `|g a_k - g b_k| < (k + 1)⁻¹ |a_k - b_k|`
  choose a ha b hb hab using fun k : ℕ => hcon (1 / ((k : ℝ) + 1)) (by positivity)
  -- so `a_k ≠ b_k`
  have hpos : ∀ k, 0 < ‖a k - b k‖ := by
    intro k
    have h1 := hab k
    have h2 := norm_nonneg (g (a k) - g (b k))
    by_contra hle
    push Not at hle
    have h0 : ‖a k - b k‖ = 0 := le_antisymm hle (norm_nonneg _)
    rw [h0, mul_zero] at h1
    linarith
  -- the unit vectors `e_k = |a_k - b_k|⁻¹ (a_k - b_k)`
  set e : ℕ → Euclid d := fun k => ‖a k - b k‖⁻¹ • (a k - b k) with he_def
  have he : ∀ k, e k ∈ sphere (0 : Euclid d) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, he_def]
    simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hpos k).ne'
  -- a subsequence of `(a_k, b_k, e_k)` converges in the compact set `K × K × S`
  obtain ⟨⟨a0, b0, e0⟩, ⟨ha0, hb0, he0⟩, φ, hφ, hlim⟩ :=
    (hK.prod (hK.prod (isCompact_sphere (0 : Euclid d) 1))).tendsto_subseq
      (x := fun k => (a k, b k, e k)) (fun k => ⟨ha k, hb k, he k⟩)
  have hla : Tendsto (fun k => a (φ k)) atTop (𝓝 a0) := (continuous_fst.tendsto _).comp hlim
  have hlb : Tendsto (fun k => b (φ k)) atTop (𝓝 b0) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hle : Tendsto (fun k => e (φ k)) atTop (𝓝 e0) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hinvk : Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  by_cases hab0 : a0 = b0
  · -- `a = b`: strict differentiability of `g` at `a` forces `Dg(a) e = 0`
    subst hab0
    have hstrict : HasStrictFDerivAt g (fderiv ℝ g a0) a0 :=
      (hg.contDiffAt (hU.mem_nhds (hKU ha0))).hasStrictFDerivAt one_ne_zero
    have hpair : Tendsto (fun k => (a (φ k), b (φ k))) atTop (𝓝 (a0, a0)) := hla.prodMk_nhds hlb
    have ho := (hstrict.isLittleO.comp_tendsto hpair).norm_norm.tendsto_div_nhds_zero
    -- `|Dg(a) e_k| ≤ |g a_k - g b_k| / |a_k - b_k| + o(1) → 0`
    have hbound : ∀ k, ‖fderiv ℝ g a0 (e (φ k))‖ ≤ 1 / ((φ k : ℝ) + 1) +
        ‖g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))‖ / ‖a (φ k) - b (φ k)‖ := by
      intro k
      have hk := hpos (φ k)
      have hdec : fderiv ℝ g a0 (e (φ k)) = ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k))) -
          ‖a (φ k) - b (φ k)‖⁻¹ • (g (a (φ k)) - g (b (φ k)) - fderiv ℝ g a0 (a (φ k) - b (φ k))) := by
        rw [he_def, map_smul, ← smul_sub, sub_sub_cancel]
      rw [hdec]
      refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hk]
        have := (hab (φ k)).le
        linarith [mul_comm (1 / ((φ k : ℝ) + 1)) ‖a (φ k) - b (φ k)‖]
      · rw [norm_smul, norm_inv, norm_norm, div_eq_inv_mul]
    have htend : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => norm_nonneg _) hbound ?_
      simpa using hinvk.add ho
    have hL : Tendsto (fun k => ‖fderiv ℝ g a0 (e (φ k))‖) atTop (𝓝 ‖fderiv ℝ g a0 e0‖) :=
      (((fderiv ℝ g a0).continuous.tendsto _).comp hle).norm
    have hL0 : fderiv ℝ g a0 e0 = 0 := norm_eq_zero.1 (tendsto_nhds_unique hL htend)
    have he00 : e0 = 0 := hDinj a0 ha0 (by rw [hL0, map_zero])
    rw [he00, mem_sphere_zero_iff_norm, norm_zero] at he0
    exact zero_ne_one he0
  · -- `a ≠ b`: continuity of `g` at `a` and `b` forces `g a = g b`
    have hcont : ∀ x ∈ K, ContinuousAt g x := fun x hx =>
      (hg.contDiffAt (hU.mem_nhds (hKU hx))).continuousAt
    have hga : Tendsto (fun k => g (a (φ k))) atTop (𝓝 (g a0)) := (hcont a0 ha0).tendsto.comp hla
    have hgb : Tendsto (fun k => g (b (φ k))) atTop (𝓝 (g b0)) := (hcont b0 hb0).tendsto.comp hlb
    have hdiff : Tendsto (fun k => g (a (φ k)) - g (b (φ k))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hbd : Tendsto (fun k => 1 / ((φ k : ℝ) + 1) * ‖a (φ k) - b (φ k)‖) atTop (𝓝 0) := by
        simpa using hinvk.mul (hla.sub hlb).norm
      exact squeeze_zero (fun k => norm_nonneg _) (fun k => (hab (φ k)).le) hbd
    have hzero : g a0 - g b0 = 0 := tendsto_nhds_unique (hga.sub hgb) hdiff
    exact hab0 (hinj ha0 hb0 (sub_eq_zero.1 hzero))
/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"** (approximate tangent plane of an embedded `C¹`
disk, the rescaling step).  With `L = Dg(z)`, `G_s(b) = s⁻¹(g(z + sb) - g(z))` and
`B_s = {b : z + sb ∈ B}`, `∫_{B_s} h(z + sb) f(G_s(b)) db → h(z) ∫ f(Lb) db` as `s ↓ 0`.  Take
`spt f ⊆ B̄_R(0)` and `B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R` the ball `K = B̄_{R/m}(0)` lies in `B_s`,
and off `K` the bound `m|a - z| ≤ |g(a) - g(z)|` gives `|G_s(b)| ≥ m|b| > R`; so the integral is
over `K`.  There the integrand is bounded by `sup_B |h| · sup |f|` and tends to `h(z) f(Lb)`
(continuity of `h` at `z`; `HasFDerivAt.lim`), so dominated convergence applies.  Finally
`f(Lb) = 0` off `K`, since `m|b| ≤ |Lb|`. -/
theorem Submission.dtc_bc_lc_sl_c1t_rescaled_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), IsCompact B → B ∈ 𝓝 z → ContinuousOn g B → DifferentiableAt ℝ g z → ContinuousOn h B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hBc hBz hg hgz hh hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.1 hBz
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Steps 3–4: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`; the integrand vanishes on `B_s \ K`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ B := by
    intro s hs hss b hb
    apply hρB
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 5: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hBc.isClosed.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hKB s hs.1 hs.2.le b hb
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 6: uniform bounds
  obtain ⟨Λ, hΛ⟩ := hBc.exists_bound_of_continuousOn hh
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 7–9: measurability, pointwise limit and dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      have hmaps : MapsTo (fun b : Euclid n => z + s • b) (closedBall (0 : Euclid n) (R / m)) B :=
        fun b hb => hKB s hs.1 hs.2.le b hb
      have hcont : ContinuousOn (fun b : Euclid n => h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)))
          (closedBall (0 : Euclid n) (R / m)) :=
        (hh.comp hz.continuousOn hmaps).mul (hf.comp_continuousOn
          (((hg.comp hz.continuousOn hmaps).sub continuousOn_const).const_smul s⁻¹))
      exact hcont.aestronglyMeasurable measurableSet_closedBall
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.continuousAt hBz).tendsto.comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 10: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
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

/-- **`C¹` pieces along one chart** (Simon Ch. 3, proof of 2.4; Ch. 2, Theorem 1.5).  Let
`M ⊆ ℝᴾ` be Borel, `f : ℝᴾ → ℝ` Lipschitz, `ψ : ℝᴺ → ℝᴾ` of class `C¹` and `V ⊆ ℝᴺ` open.  Borel
sets `Y k` with compact closure in `V` and `ψ(Y k) ⊆ M`, and `F k ∈ C¹` with `f ∘ ψ = F k` on
`Y k`, cover `M ∩ ψ(V)` up to an `Hᴺ`-null set.  Cover `V` by compact sets `K m`; `ψ` is Lipschitz
on `K m`, so `f ∘ ψ` restricted to `K m` has a Lipschitz extension `u m` (McShane), and 1.5 gives
`g m k ∈ C¹` with `Lᴺ{u m ≠ g m k} < 1/k`.  The pieces are `K m ∩ {u m = g m k} ∩ ψ⁻¹(M)`; the
rest of `M ∩ ψ(V)` lies in `⋃ₘ ψ(Z m)`, `Z m = K m ∩ ⋂ₖ {u m ≠ g m k}`, and `Lᴺ(Z m) = 0`. -/
theorem Submission.dtc_bc_lc_sl_cp_chart_refinement : ∀ (P N : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal) (ψ : Euclid N → Euclid P) (V : Set (Euclid N)), MeasurableSet M → LipschitzWith L f → IsOpen V → ContDiff ℝ 1 ψ → ∃ (Y : ℕ → Set (Euclid N)) (F : ℕ → Euclid N → ℝ), (∀ k, ContDiff ℝ 1 (F k) ∧ MeasurableSet (Y k) ∧ IsCompact (closure (Y k)) ∧ closure (Y k) ⊆ V ∧ ψ '' Y k ⊆ M ∧ ∀ y ∈ Y k, f (ψ y) = F k y) ∧ μHE[N] ((M ∩ ψ '' V) \ ⋃ k, ψ '' Y k) = 0 := by
  intro P N M f L ψ V hM hf hV hψ
  -- Step 1: compact sets `K m ⊆ V` covering `V` (the open `V` is σ-compact)
  obtain ⟨K, hKc, hKV, hKU⟩ : ∃ K : ℕ → Set (Euclid N), (∀ m, IsCompact (K m)) ∧
      (∀ m, K m ⊆ V) ∧ ⋃ m, K m = V := by
    have : LocallyCompactSpace V := hV.locallyCompactSpace
    obtain ⟨K', hK'c, hK'U⟩ := SigmaCompactSpace.exists_compact_covering (X := V)
    refine ⟨fun m => Subtype.val '' K' m, fun m => (hK'c m).image continuous_subtype_val,
      fun m => image_subset_iff.2 fun y _ => y.2, ?_⟩
    ext y
    simp only [mem_iUnion, mem_image]
    constructor
    · rintro ⟨m, z, -, rfl⟩
      exact z.2
    · intro hy
      obtain ⟨m, hm⟩ := mem_iUnion.1 (hK'U.symm ▸ mem_univ (⟨y, hy⟩ : V))
      exact ⟨m, ⟨y, hy⟩, hm, rfl⟩
  -- Step 2: `ψ` is `C m`-Lipschitz on the compact `K m`
  choose C hC using fun m => LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hKc m)
    hψ.locallyLipschitz.locallyLipschitzOn
  -- Step 3: a Lipschitz (McShane) extension `u m` of `f ∘ ψ` from `K m`
  choose u hu hfu using fun m => (hf.comp_lipschitzOnWith (hC m)).extend_real
  -- Step 4: `C¹` functions `g m k` with `Lᴺ({u m ≠ g m k}) < 1 / k`
  choose g hg hgvol using fun m (k : ℕ) => Submission.codim1_rdo_c1_approximation N (u m)
    (L * C m) (hu m) (k : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top k))
  -- Step 5: `Z m = K m ∩ ⋂ k, {u m ≠ g m k}` is null, and so is `ψ(Z m)`
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → Set (Euclid N), ∀ m, Z m = K m ∩ ⋂ k, {y | u m y ≠ g m k y} :=
    ⟨_, fun _ => rfl⟩
  have hZnull : ∀ m, μHE[N] (ψ '' Z m) = 0 := by
    intro m
    have hvol : volume (Z m) = 0 := by
      refine le_antisymm (ge_of_tendsto' ENNReal.tendsto_inv_nat_nhds_zero fun k => ?_) zero_le
      refine (measure_mono fun y hy => ?_).trans (hgvol m k).le
      rw [hZ] at hy
      exact Or.inl (mem_iInter.1 hy.2 k)
    have hH : μH[(N : ℝ)] (Z m) = 0 := by
      have h0 : μHE[N] (Z m) = 0 := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
        exact hvol
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
        mul_eq_zero, ENNReal.coe_eq_zero] at h0
      exact h0.resolve_left (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero N)
    have hZK : Z m ⊆ K m := by
      rw [hZ]
      exact inter_subset_left
    have hH' : μH[(N : ℝ)] (ψ '' Z m) = 0 := by
      refine le_antisymm ?_ zero_le
      calc μH[(N : ℝ)] (ψ '' Z m) ≤ (C m : ℝ≥0∞) ^ (N : ℝ) * μH[(N : ℝ)] (Z m) :=
            ((hC m).mono hZK).hausdorffMeasure_image_le (Nat.cast_nonneg N)
        _ = 0 := by rw [hH, mul_zero]
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH', smul_zero]
  -- Step 6: the pieces `Y' m k = K m ∩ {u m = g m k} ∩ ψ⁻¹(M)`
  obtain ⟨Y', hY'⟩ : ∃ Y' : ℕ → ℕ → Set (Euclid N), ∀ m k,
      Y' m k = K m ∩ {y | u m y = g m k y} ∩ ψ ⁻¹' M := ⟨_, fun _ _ => rfl⟩
  have hpiece : ∀ m k, ContDiff ℝ 1 (g m k) ∧ MeasurableSet (Y' m k) ∧
      IsCompact (closure (Y' m k)) ∧ closure (Y' m k) ⊆ V ∧ ψ '' Y' m k ⊆ M ∧
      ∀ y ∈ Y' m k, f (ψ y) = g m k y := by
    intro m k
    have hYK : closure (Y' m k) ⊆ K m := by
      refine closure_minimal ?_ (hKc m).isClosed
      rw [hY']
      exact inter_subset_left.trans inter_subset_left
    refine ⟨hg m k, ?_, (hKc m).of_isClosed_subset isClosed_closure hYK, hYK.trans (hKV m), ?_, ?_⟩
    · rw [hY']
      exact ((hKc m).isClosed.measurableSet.inter
        (isClosed_eq (hu m).continuous (hg m k).continuous).measurableSet).inter
        (hM.preimage hψ.continuous.measurable)
    · rintro _ ⟨y, hy, rfl⟩
      rw [hY'] at hy
      exact hy.2
    · intro y hy
      rw [hY'] at hy
      exact (hfu m hy.1.1).trans hy.1.2
  refine ⟨fun b => Y' (Nat.unpair b).1 (Nat.unpair b).2,
    fun b => g (Nat.unpair b).1 (Nat.unpair b).2, fun b => hpiece _ _, ?_⟩
  -- Step 7: the uncovered part of `M ∩ ψ(V)` lies in `⋃ m, ψ(Z m)`
  refine measure_mono_null ?_ (measure_iUnion_null hZnull)
  rintro x ⟨⟨hxM, y, hyV, rfl⟩, hx⟩
  rw [← hKU] at hyV
  obtain ⟨m, hym⟩ := mem_iUnion.1 hyV
  refine mem_iUnion.2 ⟨m, y, ?_, rfl⟩
  rw [hZ]
  refine ⟨hym, mem_iInter.2 fun k => ?_⟩
  intro hk
  refine hx (mem_iUnion.2 ⟨Nat.pair m k, y, ?_, rfl⟩)
  simp only [Nat.unpair_pair]
  rw [hY']
  exact ⟨⟨hym, hk⟩, hxM⟩

/-- **Simon Ch. 3, Lemma 1.2, "only if"** (chapter-03.txt lines 39–65, in the lemma at lines
25–66), in quantitative form: a countably `n`-rectifiable `M ⊆ ℝᴾ` is covered, up to an
`Hⁿ`-null set, by countably many images `Nₖ = gₖ(B_{rₖ}(cₖ))` of open balls under C¹ maps
`gₖ : ℝⁿ → ℝᴾ` with lower Lipschitz bounds `mₖ|a − b| ≤ |gₖ(a) − gₖ(b)|` on the balls, each `Nₖ`
Borel with `Hⁿ(Nₖ) < ∞`.  By Definition 1.1, `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ`
Lipschitz.  The C¹ approximation theorem (Simon Ch. 2, 1.5) covers `Fⱼ(ℝⁿ)` by C¹ images
`Gⱼᵢ(ℝⁿ)` up to a null set, and `Gⱼᵢ(ℝⁿ)` is covered, up to its null critical image, by images of
balls carrying lower Lipschitz bounds.  The triples `(j, i, q)` are enumerated by applying
`Nat.unpair` twice. -/
theorem Submission.codim1_rdo_rectifiable_c1_cover : ∀ (P n : ℕ) (M : Set (Euclid P)), CountablyRectifiable n M → ∃ (g : ℕ → Euclid n → Euclid P) (c : ℕ → Euclid n) (r m : ℕ → ℝ), (∀ k, ContDiff ℝ 1 (g k)) ∧ (∀ k, 0 < m k) ∧ (∀ k, ∀ a ∈ ball (c k) (r k), ∀ b ∈ ball (c k) (r k), m k * ‖a - b‖ ≤ ‖g k a - g k b‖) ∧ (∀ k, MeasurableSet (g k '' ball (c k) (r k))) ∧ (∀ k, μHE[n] (g k '' ball (c k) (r k)) ≠ ∞) ∧ μHE[n] (M \ ⋃ k, g k '' ball (c k) (r k)) = 0 := by
  intro P n M hM
  -- Step 1 (Definition 1.1): `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and `Fⱼ` `Kⱼ`-Lipschitz.
  obtain ⟨M₀, hM₀, F, hF, hcover⟩ := hM
  choose K hK using hF
  -- Steps 2–3: C¹ maps `Gⱼᵢ` with `Hⁿ(Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) = 0`, by the C¹ approximation theorem.
  choose G hG hFG using fun j => Submission.codim1_rdo_c1cov_lipschitz_range_c1_cover P n
    (Submission.codim1_rdo_c1_approximation n) (F j) (K j) (hK j)
  -- Steps 4–6: balls `B_{rⱼᵢq}(cⱼᵢq)` on which `Gⱼᵢ` has lower Lipschitz constant `mⱼᵢq > 0`,
  -- whose images cover `Gⱼᵢ(ℝⁿ)` up to an `Hⁿ`-null set.
  choose c r m hm hlow hGB using fun j i => Submission.codim1_rdo_c1cov_regular_ball_cover P n
    (G j i) (hG j i)
  -- Step 7: `k ↦ (J k, I k, Q k)` maps `ℕ` onto `ℕ³` (`Nat.unpair` applied twice).
  obtain ⟨J, I, Q, hJIQ⟩ : ∃ J I Q : ℕ → ℕ, ∀ j i q, ∃ k, J k = j ∧ I k = i ∧ Q k = q :=
    ⟨fun k => k.unpair.1, fun k => k.unpair.2.unpair.1, fun k => k.unpair.2.unpair.2,
      fun j i q => ⟨Nat.pair j (Nat.pair i q), by simp⟩⟩
  -- Step 8: the pieces `Nₖ` are Borel with finite `Hⁿ`-measure.
  have hN k := Submission.codim1_rdo_c1cov_image_ball_borel_finite P n (G (J k) (I k))
    (c (J k) (I k) (Q k)) (r (J k) (I k) (Q k)) (hG (J k) (I k))
  refine ⟨fun k => G (J k) (I k), fun k => c (J k) (I k) (Q k), fun k => r (J k) (I k) (Q k),
    fun k => m (J k) (I k) (Q k), fun k => hG _ _, fun k => hm _ _ _, fun k => hlow _ _ _,
    fun k => (hN k).1, fun k => (hN k).2, ?_⟩
  -- Step 9: `M ∖ ⋃ₖ Nₖ` lies in the countable union of `Hⁿ`-null sets
  -- `M₀ ∪ ⋃ⱼ (Fⱼ(ℝⁿ) ∖ ⋃ᵢ Gⱼᵢ(ℝⁿ)) ∪ ⋃ⱼ ⋃ᵢ (Gⱼᵢ(ℝⁿ) ∖ ⋃_q Gⱼᵢ(B_{rⱼᵢq}(cⱼᵢq)))`.
  refine measure_mono_null ?_ (measure_union_null hM₀ (measure_union_null (measure_iUnion_null hFG)
    (measure_iUnion_null fun j => measure_iUnion_null (hGB j))))
  rintro y ⟨hyM, hyN⟩
  rcases hcover hyM with hy₀ | hyF
  · exact Or.inl hy₀
  obtain ⟨j, hyj⟩ := mem_iUnion.1 hyF
  by_cases hyG : y ∈ ⋃ i, range (G j i)
  · obtain ⟨i, hyi⟩ := mem_iUnion.1 hyG
    by_cases hyB : y ∈ ⋃ q, G j i '' ball (c j i q) (r j i q)
    · obtain ⟨q, hyq⟩ := mem_iUnion.1 hyB
      obtain ⟨k, rfl, rfl, rfl⟩ := hJIQ j i q
      exact absurd (mem_iUnion.2 ⟨k, hyq⟩) hyN
    · exact Or.inr (Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨i, hyi, hyB⟩⟩))
  · exact Or.inr (Or.inl (mem_iUnion.2 ⟨j, hyj, hyG⟩))
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

/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in an open set**
(Simon Ch. 1, 3.6 and Remark 3.7(2); chapter-01.txt lines 700–711).  If `U ⊆ ℝᴾ` is open and
`S ⊆ ℝᴾ` is Borel with `Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e.
`x ∈ U \ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B(y, r_y)` with
`B̄(y, r_y) ⊆ U` cover `U` (Lindelöf); the upper density theorem applies to each piece
`S ∩ B(y, r_y)`, of finite measure, and the piece agrees with `S` on small balls about
`x ∈ B(y, r_y)`. -/
theorem Submission.doraggt_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U` (Lindelöf).
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hrad
  obtain ⟨D, hDU, hDc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hr0 y hy)))
  -- Steps 2 and 3, the upper density theorem for each finite-measure piece `S ∩ B(y, r y)`,
  -- simultaneously for the countably many `y ∈ D`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] ((S ∩ ball y (r y)) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    refine Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball) ?_
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
  -- Step 4, near `x ∈ B(y, r y)` the piece and `S` agree.
  filter_upwards [hae] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcover hxU)
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεball)]
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
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
/-- Changing a set by parts of vanishing `n`-density at `x` does not change its approximate
tangent spaces at `x` (Simon Ch. 3, Definition 1.4 and Remark 1.5(2); proof of 3.1.6).  For
`f ∈ C_c(ℝᴾ)` with `|f| ≤ C`, `f = 0` off `B̄_R(0)` and `0 < r < r₀/R`, comparing both blow-up
integrals with the one over `η_{x,r}(A ∩ B)` gives `|∫_{η_{x,r}(A)} f dHⁿ − ∫_{η_{x,r}(B)} f dHⁿ| ≤
C Hⁿ(η_{x,r}(A \ B) ∩ B̄_R(0)) + C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`, and
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`. -/
theorem Submission.doraggt_approxTangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → 0 < r₀ → μHE[n] (A ∩ closedBall x r₀) ≠ ∞ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((A \ B) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n A B x r₀ hA hB hr₀ hAfin hBfin hAB hBA
  -- Step 1: it suffices that `∫_{η_r(A)} f − ∫_{η_r(B)} f → 0` for every `f ∈ C_c`
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n A B x fun f => ?_
  -- Step 2: `|f| ≤ C`, and `f = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hzero⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
      f.hasCompactSupport.isCompact.isBounded
    exact ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))⟩
  -- Step 3: for `0 < r < r₀ / R`, `Hⁿ(η_r(S) ∩ B̄_R(0)) ≤ r⁻ⁿ Hⁿ(S ∩ B̄_{r₀}(x)) < ∞`
  have hfin : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall x r₀) ≠ ∞ → ∀ r ∈ Ioo 0 (r₀ / R),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) ≠ ∞ := by
    intro S hS r hr
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr.1).ne'))
      (ne_top_of_le_ne_top hS (measure_mono (inter_subset_inter_right _
        (closedBall_subset_closedBall ((lt_div_iff₀ hR).mp hr.2).le))))
  -- Step 4: `C Hⁿ(η_r(S) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`
  have herr : ∀ S : Set (Euclid P),
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => C *
        (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
        (𝓝[>] 0) (𝓝 0) := by
    intro S hS
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ => μHE[n] (S ∩ closedBall x ρ)) R hR hS)).const_mul C
    rw [ENNReal.toReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Function.comp_apply, Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr]
  -- Step 5: for `0 < r < r₀ / R`, compare both integrals with the one over `η_r(A ∩ B)`
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]‖ ≤
        C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A \ B) ∩
            closedBall 0 R)).toReal +
          C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩
            closedBall 0 R)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
    have hA' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) A x r R C f
      f.continuous (hA.inter hB) hA inter_subset_left hr.1 (hfin A hAfin r hr) hC hzero
    have hB' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) B x r R C f
      f.continuous (hA.inter hB) hB inter_subset_right hr.1 (hfin B hBfin r hr) hC hzero
    rw [Set.sdiff_self_inter] at hA'
    rw [Set.sdiff_inter_self_eq_sdiff] at hB'
    rw [← sub_sub_sub_cancel_right _ _
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ B), f y ∂μHE[n])]
    exact (norm_sub_le _ _).trans (add_le_add hA' hB')
  -- Step 6: squeeze
  have hlim := (herr _ hAB).add (herr _ hBA)
  rw [add_zero] at hlim
  exact squeeze_zero_norm' hle hlim

/-- **Approximate tangent planes of two locally finite sets agree a.e. on their overlap** (Simon
Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and 113–146,
stated symmetrically for two sets).  Let `W ⊆ ℝᴾ` be open and `A`, `B` Borel with `Hⁿ(A ∩ K)` and
`Hⁿ(B ∩ K)` finite for every compact `K ⊆ W`.  By the upper density theorem the densities of
`A ∖ B` and `B ∖ A` vanish at `Hⁿ`-a.e. `x ∈ W ∩ A ∩ B`; a closed ball about such `x` inside `W`
has finite measure in `A` and in `B`, so `A` and `B` have the same approximate tangent planes at
`x`. -/
theorem Submission.doraggt_ae_approxTangent_transfer : ∀ (P n : ℕ) (W A B : Set (Euclid P)), IsOpen W → MeasurableSet A → MeasurableSet B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (A ∩ K) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ W → x ∈ A → x ∈ B → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n W A B hW hA hB hAfin hBfin
  -- Step 1, the densities of `A ∖ B` and `B ∖ A` vanish `Hⁿ`-a.e. on `W` off these sets.
  have hAB := Submission.doraggt_local_density_zero P n W (A \ B) hW (hA.diff hB)
    fun K hK hKW => ne_top_of_le_ne_top (hAfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  have hBA := Submission.doraggt_local_density_zero P n W (B \ A) hW (hB.diff hA)
    fun K hK hKW => ne_top_of_le_ne_top (hBfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2, at such `x ∈ W ∩ A ∩ B`, `x ∉ A ∖ B` and `x ∉ B ∖ A`, so both densities vanish.
  filter_upwards [hAB, hBA] with x hxAB hxBA hxW hxA hxB
  -- Step 3, `B̄(x, ε/2) ⊆ B(x, ε) ⊆ W` is compact, so `A` and `B` have finite measure in it.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hsub : closedBall x (ε / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4, the approximate tangent planes of `A` and `B` at `x` agree.
  exact Submission.doraggt_approxTangent_iff_of_density_zero P n A B x (ε / 2) hA hB
    (half_pos hε) (hAfin _ (isCompact_closedBall x (ε / 2)) hsub)
    (hBfin _ (isCompact_closedBall x (ε / 2)) hsub) (hxAB hxW fun h => h.2 hxB)
    (hxBA hxW fun h => h.2 hxA)

/-- **Approximate tangent planes of `M` along one bi-Lipschitz `C¹` chart, off a Borel null set**
(Simon Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and
113–146: `TₓM = TₓNⱼ` for `Hⁿ`-a.e. `x ∈ Mⱼ`).  Let `M ⊆ ℝᴾ` be Borel with `Hᴺ(M ∩ K) < ∞` for
compact `K`, let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on `B = B_r(c)`, `m > 0`, and let
`S = g(B)` be Borel with `Hᴺ(S) < ∞`.  Tangent locality with `W = ℝᴾ` gives, for `Hᴺ`-a.e.
`x ∈ S ∩ M`, the same approximate tangent spaces for `S` and `M` at `x`; the exceptional set lies
in a Borel `Hᴺ`-null set `E`.  For `y ∈ B` with `g(y) ∈ M ∖ E`, `S` has approximate tangent space
`Dg(y)(ℝᴺ)` at `g(y)` (the `C¹` piece), hence so does `M`. -/
theorem Submission.dtc_bc_lc_sl_cp_chart_tangent : ∀ (P N : ℕ) (M : Set (Euclid P)) (g : Euclid N → Euclid P) (c : Euclid N) (r m : ℝ), MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[N] (M ∩ K) ≠ ∞) → ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → MeasurableSet (g '' ball c r) → μHE[N] (g '' ball c r) ≠ ∞ → ∃ E : Set (Euclid P), MeasurableSet E ∧ μHE[N] E = 0 ∧ ∀ y ∈ ball c r, g y ∈ M → g y ∉ E → HasApproximateTangentSpaceAt N M (g y) (LinearMap.range (fderiv ℝ g y : Euclid N →ₗ[ℝ] Euclid P)) := by
  intro P N M g c r m hM hMfin hg hm hlip hS hSfin
  -- Steps 1–2, `S = g(B)` and `M` are locally `Hᴺ`-finite, so tangent locality with `W = ℝᴾ`
  -- gives `TₓS = TₓM` for `Hᴺ`-a.e. `x ∈ S ∩ M`.
  have htr := Submission.doraggt_ae_approxTangent_transfer P N univ (g '' ball c r) M isOpen_univ
    hS hM (fun K _ _ => ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
    fun K hK _ => hMfin K hK
  -- Step 3, the exceptional set of the transfer lies in a Borel `Hᴺ`-null set `E`.
  obtain ⟨E, hE₀E, hE, hE0⟩ := exists_measurable_superset_of_null (ae_iff.1 htr)
  refine ⟨E, hE, hE0, fun y hy hyM hyE => ?_⟩
  -- Step 4, at `x = g(y) ∉ E` the transfer holds, and `S` has tangent space `Dg(y)(ℝᴺ)` at `x`.
  by_contra hfail
  refine hyE (hE₀E fun hx => hfail ?_)
  exact (hx (mem_univ _) (mem_image_of_mem g hy) hyM _).1
    (Submission.codim1_rdo_c1_piece_approxTangent P N g c r m hg hm hlip y hy)
/-- **Disjointification of injectively parametrised Borel pieces** (Simon Ch. 3, Remark 1.3).
For continuous `ψⱼ : ℝᴺ → ℝᴾ` injective on Borel `Yⱼ`, the images `Aⱼ = ψⱼ(Yⱼ)` are Borel
(Lusin–Souslin), so `Dⱼ = Aⱼ \ ⋃_{i<j} Aᵢ` (`disjointed`) are Borel, pairwise disjoint and have
the same union as the `Aⱼ`.  The Borel pieces `Y'ⱼ = Yⱼ ∩ ψⱼ⁻¹(Dⱼ) ⊆ Yⱼ` have
`ψⱼ(Y'ⱼ) = Aⱼ ∩ Dⱼ = Dⱼ`. -/
theorem Submission.dtc_bc_lc_sl_cp_disjointify : ∀ (P N : ℕ) (ψ : ℕ → Euclid N → Euclid P) (Y : ℕ → Set (Euclid N)), (∀ j, Continuous (ψ j)) → (∀ j, MeasurableSet (Y j)) → (∀ j, InjOn (ψ j) (Y j)) → ∃ Y' : ℕ → Set (Euclid N), (∀ j, MeasurableSet (Y' j) ∧ Y' j ⊆ Y j) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y' i) (ψ j '' Y' j)) ∧ ⋃ j, ψ j '' Y' j = ⋃ j, ψ j '' Y j := by
  intro P N ψ Y hψ hY hinj
  -- the images `Aⱼ = ψⱼ(Yⱼ)` are Borel (Lusin–Souslin)
  have hA : ∀ j, MeasurableSet (ψ j '' Y j) := fun j =>
    (hY j).image_of_continuousOn_injOn (hψ j).continuousOn (hinj j)
  -- `Y'ⱼ = Yⱼ ∩ ψⱼ⁻¹(Dⱼ)` with `Dⱼ = Aⱼ \ ⋃_{i<j} Aᵢ`, so that `ψⱼ(Y'ⱼ) = Dⱼ`
  have himage : ∀ j, ψ j '' (Y j ∩ ψ j ⁻¹' disjointed (fun i => ψ i '' Y i) j) =
      disjointed (fun i => ψ i '' Y i) j := fun j => by
    rw [image_inter_preimage]
    exact inter_eq_right.2 (disjointed_subset _ j)
  refine ⟨fun j => Y j ∩ ψ j ⁻¹' disjointed (fun i => ψ i '' Y i) j,
    fun j => ⟨(hY j).inter ((hψ j).measurable (MeasurableSet.disjointed hA j)),
      inter_subset_left⟩, fun i j hij => ?_, ?_⟩
  · -- the `Dⱼ` are pairwise disjoint
    dsimp only
    rw [himage i, himage j]
    exact disjoint_disjointed _ hij
  · -- `⋃ⱼ Dⱼ = ⋃ⱼ Aⱼ`
    simp only [himage]
    exact iUnion_disjointed
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

/-- **Simon 2.1.9 and Remark 2.1.10** (Eilenberg's inequality, case `m = 1`): if `f` is
`L`-Lipschitz on an arbitrary `A ⊆ ℝᴾ`, the upper integral of `t ↦ Hⁿ(A ∩ f⁻¹(t))` is at most
`C L Hⁿ⁺¹(A)`, with `C` depending only on `n`; the upper integral is made explicit by a Borel
majorant `φ`.

Proof sketch:
* `μHE[d] = c_d μH[d]` with `0 < c_d < ∞` independent of `P`; take `C = c_n / c_{n+1}`.
* Extend `f` to an `L`-Lipschitz `g` on `ℝᴾ` (McShane); the fibres in `A` do not change.
* If `L = 0`, `g` is constant `= g(0)`, so `φ = ∞ · 1_{g(0)}` works (`∫ φ = 0`).
* If `L > 0` and `μH[n+1](A) = ∞`, the bound is `∞` and `φ ≡ ∞` works.
* Otherwise `dtc_bc_lc_sl_eil_scale` at the scale and slack `δ_k = 2⁻ᵏ` gives Borel `ψ_k`
  dominating the `δ_k`-contents of the fibres `A ∩ g⁻¹(t)`, with
  `∫ ψ_k ≤ L μH[n+1](A) + L 2⁻ᵏ`.
* `dtc_bc_lc_sl_eil_limit` (Fatou) gives a Borel `φ⁰ ≥ μH[n](A ∩ g⁻¹(t))` with
  `∫ φ⁰ ≤ L μH[n+1](A)`; then `φ = c_n φ⁰`. -/
theorem Submission.dtc_bc_lc_sl_eilenberg : ∀ n : ℕ, ∃ C : NNReal, ∀ (P : ℕ) (A : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), LipschitzOnWith L f A → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t, μHE[n] (A ∩ f ⁻¹' {t}) ≤ φ t) ∧ ∫⁻ t, φ t ≤ (C : ℝ≥0∞) * (L : ℝ≥0∞) * μHE[n + 1] A := by
  -- the normalising constants `μHE[d] = c_d • μH[d]`, `c_d ≠ 0`, do not depend on `P`
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℕ → NNReal, (∀ d, c d ≠ 0) ∧
      ∀ (P d : ℕ) (s : Set (Euclid P)), μHE[d] s = (c d : ℝ≥0∞) * μH[d] s :=
    ⟨fun d => Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin d))) μH[d],
      Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero, fun P d s => by
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul]⟩
  intro n
  refine ⟨c n / c (n + 1), fun P A f L hf => ?_⟩
  have hC : ((c n / c (n + 1) : NNReal) : ℝ≥0∞) * c (n + 1) = c n := by
    rw [← ENNReal.coe_mul, div_mul_cancel₀ _ (hc0 (n + 1))]
  -- McShane extension: `g` is `L`-Lipschitz on `ℝᴾ` and has the same fibres in `A`
  obtain ⟨g, hg, hfg⟩ := hf.extend_real
  have hfib : ∀ t, A ∩ f ⁻¹' {t} = A ∩ g ⁻¹' {t} := fun t => by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨h.1, (hfg h.1).symm.trans h.2⟩, fun h => ⟨h.1, (hfg h.1).trans h.2⟩⟩
  -- `L = 0`: `g` is constant, so every fibre but one is empty
  by_cases hL : L = 0
  · subst hL
    have hconst : ∀ x, g x = g 0 := fun x =>
      dist_le_zero.1 ((hg.dist_le_mul x 0).trans (by simp))
    refine ⟨({g 0} : Set ℝ).indicator fun _ => ∞,
      measurable_const.indicator (measurableSet_singleton _), fun t => ?_, ?_⟩
    · by_cases ht : t = g 0
      · rw [ht, indicator_of_mem (mem_singleton _)]
        exact le_top
      · have hempty : A ∩ g ⁻¹' {t} = ∅ := by
          ext x
          simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
            iff_false, not_and]
          exact fun _ hx => ht (hx.symm.trans (hconst x))
        rw [hfib, hempty, measure_empty]
        exact zero_le
    · rw [lintegral_indicator_const (measurableSet_singleton _), Real.volume_singleton, mul_zero]
      exact zero_le
  -- `L > 0` and `μH[n+1](A) = ∞`: the right-hand side is `∞`
  by_cases hA : μH[((n + 1 : ℕ) : ℝ)] A = ∞
  · refine ⟨fun _ => ∞, measurable_const, fun _ => le_top, le_of_le_of_eq le_top ?_⟩
    rw [hc P (n + 1) A, hA, ENNReal.mul_top (ENNReal.coe_ne_zero.2 (hc0 (n + 1))),
      ENNReal.mul_top (mul_ne_zero (ENNReal.coe_ne_zero.2 (div_ne_zero (hc0 n) (hc0 (n + 1))))
        (ENNReal.coe_ne_zero.2 hL))]
  -- main case: one scale `δ_k = 2⁻ᵏ` at a time, then the limit `k → ∞`
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℕ → ℝ≥0∞, (∀ k, 0 < δ k) ∧ Tendsto δ atTop (𝓝 0) :=
    ⟨fun k => 2⁻¹ ^ k, ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top),
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.2 ENNReal.one_lt_two)⟩
  choose ψ hψm hψle hψint using fun k =>
    Submission.dtc_bc_lc_sl_eil_scale P n A g L (δ k) (δ k) hg (hδ0 k) (hδ0 k) hA
  obtain ⟨φ, hφm, hφle, hφint⟩ := Submission.dtc_bc_lc_sl_eil_limit P n
    (fun t => A ∩ g ⁻¹' {t}) ψ δ (fun k => (L : ℝ≥0∞) * δ k)
    ((L : ℝ≥0∞) * μH[((n + 1 : ℕ) : ℝ)] A) hψm hδ
    (by simpa using ENNReal.Tendsto.const_mul (a := (L : ℝ≥0∞)) hδ (Or.inr ENNReal.coe_ne_top))
    hψle (fun k => (hψint k).trans_eq (mul_add _ _ _))
  refine ⟨fun t => (c n : ℝ≥0∞) * φ t, hφm.const_mul _, fun t => ?_, ?_⟩
  · rw [hc, hfib]
    exact mul_le_mul_right (hφle t) _
  · rw [lintegral_const_mul _ hφm, hc P (n + 1) A]
    calc (c n : ℝ≥0∞) * ∫⁻ t, φ t ≤ c n * (L * μH[((n + 1 : ℕ) : ℝ)] A) :=
          mul_le_mul_right hφint _
      _ = ((c n / c (n + 1) : NNReal) : ℝ≥0∞) * c (n + 1) * (L * μH[((n + 1 : ℕ) : ℝ)] A) := by
          rw [hC]
      _ = _ := by ring
/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"** (a `C¹` embedded disk has its tangent plane as
approximate tangent space): if `B = B̄(c, r) ⊆ U` with `U` open, `g` is `C¹` on `U`, injective on
`B`, and `Dg(a)` is injective for `a ∈ B`, then at each `z ∈ B(c, r)` the set `S = g(B)` has
approximate tangent space `Q = Dg(z)(ℝᵈ)` at `g(z)`.  First `dim Q = d`.  A compactness
argument gives `m > 0` with `m|a − b| ≤ |g(a) − g(b)|` on `B`; at the interior point `z` this
passes to `m|v| ≤ |Dg(z)v|`.  For `s > 0` the area formula for the rescaled map
`b ↦ s⁻¹(g(z + s b) − g(z))` gives `∫_{η_{g(z),s}(S)} f dHᵈ = ∫_{B_s} J(z + s b) f(…) db`, with
`B_s = {b | z + s b ∈ B}` and `J = √det(Dg* ∘ Dg)` continuous on `B`.  Dominated convergence
(the lower bound confines the integrands to a fixed ball) sends this to
`J(z) ∫ f(Dg(z)b) db`, which is `∫_Q f dHᵈ` by the linear area formula. -/
theorem Submission.dtc_bc_lc_sl_c1_tangent : ∀ (P d : ℕ) (g : Euclid d → Euclid P) (U : Set (Euclid d)) (c : Euclid d) (r : ℝ), IsOpen U → closedBall c r ⊆ U → ContDiffOn ℝ 1 g U → InjOn g (closedBall c r) → (∀ z ∈ closedBall c r, Injective (fderiv ℝ g z)) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt d (g '' closedBall c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid d →ₗ[ℝ] Euclid P)) := by
  intro P d g U c r hU hBU hg hinj hreg z hz
  have hzB : z ∈ closedBall c r := ball_subset_closedBall hz
  -- `g` is differentiable on the open set `U`, and `Dg` is continuous there
  have hdiff : ∀ a ∈ U, DifferentiableAt ℝ g a := fun a ha =>
    (hg.differentiableOn one_ne_zero a ha).differentiableAt (hU.mem_nhds ha)
  have hDg : ContinuousOn (fderiv ℝ g) U := hg.continuousOn_fderiv_of_isOpen hU le_rfl
  -- the lower Lipschitz bound `m|a − b| ≤ |g(a) − g(b)|` on the compact ball `B`
  obtain ⟨m, hm, hmB⟩ := Submission.dtc_bc_lc_sl_c1t_lower_lipschitz P d g U (closedBall c r)
    hU (isCompact_closedBall c r) hBU hg hinj hreg
  have hmz : ∀ a ∈ closedBall c r, m * ‖a - z‖ ≤ ‖g a - g z‖ := fun a ha => hmB a ha z hzB
  -- at the interior point `z` it passes to the derivative: `m|v| ≤ |Dg(z)v|`
  have hmD : ∀ v : Euclid d, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖ :=
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P d g (ball c r) z m isOpen_ball hz
      (hdiff z (hBU hzB)) fun a ha => hmz a (ball_subset_closedBall ha)
  -- the Jacobian `J(a) = √det(Dg(a)* ∘ Dg(a))` is continuous on `B`
  have hJ : ContinuousOn (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det))
      (closedBall c r) :=
    (Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))).comp_continuousOn
      (hDg.mono hBU)
  -- `dim Dg(z)(ℝᵈ) = d`, since `Dg(z)` is injective
  refine ⟨by rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid d →ₗ[ℝ] Euclid P))
    (hreg z hzB), finrank_euclideanSpace_fin], fun f => ?_⟩
  -- linear area formula: `∫_{Dg(z)(ℝᵈ)} f dHᵈ = J(z) ∫ f(Dg(z)b) db`
  rw [Submission.codim1_rdo_c1pt_linear_range_integral P d (fderiv ℝ g z) f (hreg z hzB)]
  -- for `s > 0` the area formula for the rescaled map turns `∫_{η_{g(z),s}(S)} f dHᵈ` into the
  -- integral over `B_s`, whose limit as `s ↓ 0` is `J(z) ∫ f(Dg(z)b) db`
  refine (Submission.dtc_bc_lc_sl_c1t_rescaled_tendsto P d g _ (closedBall c r) z m f
    (isCompact_closedBall c r) (closedBall_mem_nhds_of_mem hz) (hg.continuousOn.mono hBU)
    (hdiff z (hBU hzB)) hJ hm hmz hmD f.continuous f.hasCompactSupport).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P d g (closedBall c r) z s f
    measurableSet_closedBall (fun a ha => hdiff a (hBU ha)) hinj hreg hs).symm
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Simon Ch. 3, Lemma 1.2 ("only if"), Remarks 1.3 and 1.5(2), proof of 2.4** (chart pieces of
a countably `(n+1)`-rectifiable set).  Let `M ⊆ ℝᴾ` be Borel, countably `(n+1)`-rectifiable and
locally `H^{n+1}`-finite, and `f : ℝᴾ → ℝ` Lipschitz.  Up to an `H^{n+1}`-null set, `M` is the
disjoint union of pieces `ψⱼ(Yⱼ)`: `Yⱼ` is Borel with compact closure in an open `Vⱼ` on which the
`C¹` map `ψⱼ` is injective with injective derivative, `f ∘ ψⱼ` agrees on `Yⱼ` with a `C¹`
function `Fⱼ`, and `T_{ψⱼ(y)}M = Dψⱼ(y)(ℝ^{n+1})` for `y ∈ Yⱼ`.  Lemma 1.2 covers `M`, up to a
null set, by `C¹` ball charts `gₖ` with lower Lipschitz bounds.  Along each chart the `C¹`
approximation theorem (Ch. 2, 1.5) gives pieces `Yₖᵢ` with `f ∘ gₖ = Fₖᵢ` on `Yₖᵢ`, and the
locality of approximate tangent spaces gives a Borel null set `Eₖ` off which
`T_{gₖ(y)}M = Dgₖ(y)(ℝ^{n+1})`.  The pieces `Yₖᵢ ∖ gₖ⁻¹(Eₖ)`, indexed by `Nat.pair k i`, are
disjointified as in Remark 1.3. -/
theorem Submission.dtc_bc_lc_sl_chart_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet M → CountablyRectifiable (n + 1) M → (∀ K : Set (Euclid P), IsCompact K → μHE[n + 1] (M ∩ K) ≠ ∞) → LipschitzWith L f → ∃ (ψ : ℕ → Euclid (n + 1) → Euclid P) (V Y : ℕ → Set (Euclid (n + 1))) (F : ℕ → Euclid (n + 1) → ℝ), (∀ j, IsOpen (V j) ∧ ContDiff ℝ 1 (ψ j) ∧ InjOn (ψ j) (V j) ∧ (∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) ∧ ContDiff ℝ 1 (F j) ∧ MeasurableSet (Y j) ∧ IsCompact (closure (Y j)) ∧ closure (Y j) ⊆ V j ∧ ψ j '' Y j ⊆ M ∧ (∀ y ∈ Y j, f (ψ j y) = F j y) ∧ ∀ y ∈ Y j, HasApproximateTangentSpaceAt (n + 1) M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P))) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μHE[n + 1] (M \ ⋃ j, ψ j '' Y j) = 0 := by
  intro P n M f L hM hrect hfin hf
  -- Steps 1–3 (Lemma 1.2, "only if"): `C¹` charts `gₖ` on `Bₖ = B_{rₖ}(cₖ)` with
  -- `mₖ|a − b| ≤ |gₖ(a) − gₖ(b)|` on `Bₖ`, Borel images `Sₖ = gₖ(Bₖ)` of finite measure,
  -- and `H^{n+1}(M ∖ ⋃ₖ Sₖ) = 0`
  obtain ⟨g, c, r, m, hg, hm, hlow, hSmeas, hSfin, hcover⟩ :=
    Submission.codim1_rdo_rectifiable_c1_cover P (n + 1) M hrect
  -- `gₖ` is injective on `Bₖ`: `gₖ(a) = gₖ(b)` forces `mₖ|a − b| ≤ 0`
  have hinj : ∀ k, InjOn (g k) (ball (c k) (r k)) := by
    intro k a ha b hb hab
    have h := hlow k a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (by nlinarith [norm_nonneg (a - b), hm k]))
  -- `Dgₖ(y)` is injective for `y ∈ Bₖ`: `mₖ|v| ≤ |Dgₖ(y)v|`
  have hDinj : ∀ k, ∀ y ∈ ball (c k) (r k), Injective (fderiv ℝ (g k) y) := by
    intro k y hy v w hvw
    have h := Submission.codim1_rdo_c1pt_fderiv_lower_bound P (n + 1) (g k) (ball (c k) (r k)) y
      (m k) isOpen_ball hy ((hg k).differentiable one_ne_zero y) (fun x hx => hlow k x hx y hy)
      (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 (by nlinarith [norm_nonneg (v - w), hm k]))
  -- Steps 4–6 (proof of 2.4): Borel pieces `Yₖᵢ` with compact closure in `Bₖ`, `gₖ(Yₖᵢ) ⊆ M`
  -- and `f ∘ gₖ = Fₖᵢ ∈ C¹` on `Yₖᵢ`, covering `M ∩ Sₖ` up to a null set
  choose Y₀ F₀ hY₀ hY₀null using fun k =>
    Submission.dtc_bc_lc_sl_cp_chart_refinement P (n + 1) M f L (g k) (ball (c k) (r k)) hM hf
      isOpen_ball (hg k)
  -- Step 8 (Remark 1.5(2)): off a Borel null set `Eₖ`, `M` has approximate tangent space
  -- `Dgₖ(y)(ℝ^{n+1})` at every point `gₖ(y) ∈ M` with `y ∈ Bₖ`
  choose E hEmeas hEnull hEtan using fun k =>
    Submission.dtc_bc_lc_sl_cp_chart_tangent P (n + 1) M (g k) (c k) (r k) (m k) hM hfin (hg k)
      (hm k) (hlow k) (hSmeas k) (hSfin k)
  have hY₀B : ∀ k i, Y₀ k i ⊆ ball (c k) (r k) := fun k i =>
    subset_closure.trans (hY₀ k i).2.2.2.1
  -- Step 7 (Remark 1.3): index the pieces `Yₖᵢ ∖ gₖ⁻¹(Eₖ)` by `b = pair k i`; disjointify
  obtain ⟨Y, hY, hdisj, hunion⟩ := Submission.dtc_bc_lc_sl_cp_disjointify P (n + 1)
    (fun b => g b.unpair.1) (fun b => Y₀ b.unpair.1 b.unpair.2 \ g b.unpair.1 ⁻¹' E b.unpair.1)
    (fun b => (hg _).continuous)
    (fun b => (hY₀ _ _).2.1.diff ((hg _).continuous.measurable (hEmeas _)))
    (fun b => (hinj _).mono (sdiff_subset.trans (hY₀B _ _)))
  refine ⟨fun b => g b.unpair.1, fun b => ball (c b.unpair.1) (r b.unpair.1), Y,
    fun b => F₀ b.unpair.1 b.unpair.2, fun j => ?_, hdisj, ?_⟩
  · -- Step 9: the properties of the `j`-th piece `Yⱼ ⊆ Yₖᵢ ∖ gₖ⁻¹(Eₖ)`, `(k, i) = unpair j`
    obtain ⟨hYj, hYsub⟩ := hY j
    obtain ⟨hFC1, -, hcpt, hclB, himM, hfF⟩ := hY₀ j.unpair.1 j.unpair.2
    have hYY₀ : Y j ⊆ Y₀ j.unpair.1 j.unpair.2 := hYsub.trans sdiff_subset
    refine ⟨isOpen_ball, hg _, hinj _, hDinj _, hFC1, hYj,
      hcpt.of_isClosed_subset isClosed_closure (closure_mono hYY₀),
      (closure_mono hYY₀).trans hclB, (image_mono hYY₀).trans himM, fun y hy => hfF y (hYY₀ hy),
      fun y hy => ?_⟩
    obtain ⟨hy₀, hyE⟩ := hYsub hy
    exact hEtan _ y (hY₀B _ _ hy₀) (himM (mem_image_of_mem _ hy₀)) hyE
  · -- `M ∖ ⋃ⱼ ψⱼ(Yⱼ) ⊆ (M ∖ ⋃ₖ Sₖ) ∪ ⋃ₖ ((M ∩ Sₖ) ∖ ⋃ᵢ gₖ(Yₖᵢ)) ∪ ⋃ₖ Eₖ`, which is null
    rw [hunion]
    refine measure_mono_null ?_ (measure_union_null (measure_union_null hcover
      (measure_iUnion_null hY₀null)) (measure_iUnion_null hEnull))
    rintro x ⟨hxM, hxU⟩
    by_cases hxS : x ∈ ⋃ k, g k '' ball (c k) (r k)
    · obtain ⟨k, hk⟩ := mem_iUnion.1 hxS
      by_cases hxY : x ∈ ⋃ i, g k '' Y₀ k i
      · obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.1 hxY
        by_cases hxE : g k y ∈ E k
        · exact Or.inr (mem_iUnion.2 ⟨k, hxE⟩)
        · refine (hxU (mem_iUnion.2 ⟨Nat.pair k i, y, ?_, ?_⟩)).elim
          · simp only [Nat.unpair_pair]
            exact ⟨hy, hxE⟩
          · simp only [Nat.unpair_pair]
      · exact Or.inl (Or.inr (mem_iUnion.2 ⟨k, ⟨hxM, hk⟩, hxY⟩))
    · exact Or.inl (Or.inl ⟨hxM, hxS⟩)

/-- **Flattening atlas of the regular part of a `C¹` function** (local straightening of `F` by the
inverse function theorem, and a countable choice of charts by second countability).  Fix `y₀ ∈ V`
with `DF(y₀) ≠ 0` and a coordinate direction `e_j` with `DF(y₀)e_j ≠ 0`.  Let `Q` be the
coordinate map of the orthonormal basis obtained from the standard one by swapping `e₀` and `e_j`.
Then `Φ(y) = Q y + (F(y) − (Q y)₀) e₀` is `C¹` with `Φ(y)₀ = F(y)`, and `DΦ(y₀)` is injective:
`DΦ(y₀)h = 0` forces `DF(y₀)h = 0` and `Q h ∈ ℝe₀`, so `h ∈ ℝe_j` and hence `h = 0`.  The inverse
function theorem makes `Φ` a local homeomorphism `e` near `y₀`; on
`W = source ∩ V ∩ {DΦ invertible}` put `Ω = Φ(W)` and `Θ = Φ⁻¹`, which is `C¹` on `Ω` with
derivative `DΦ(Θz)⁻¹`, satisfies `Θ(Ω) = W`, and `F(Θz) = Φ(Θz)₀ = z₀`.  Away from the regular
points take the empty chart; the open sets `Θ(Ω)` cover `{y ∈ V | DF(y) ≠ 0}`, and countably many
of them suffice. -/
theorem Submission.dtc_bc_lc_sl_cc_flattening_atlas : ∀ (n : ℕ) (F : Euclid (n + 1) → ℝ) (V : Set (Euclid (n + 1))), IsOpen V → ContDiff ℝ 1 F → ∃ (Ω : ℕ → Set (Euclid (n + 1))) (Θ : ℕ → Euclid (n + 1) → Euclid (n + 1)), (∀ k, IsOpen (Ω k) ∧ ContDiffOn ℝ 1 (Θ k) (Ω k) ∧ InjOn (Θ k) (Ω k) ∧ (∀ z ∈ Ω k, Injective (fderiv ℝ (Θ k) z)) ∧ IsOpen (Θ k '' Ω k) ∧ Θ k '' Ω k ⊆ V ∧ ∀ z ∈ Ω k, F (Θ k z) = z 0) ∧ {y | y ∈ V ∧ fderiv ℝ F y ≠ 0} ⊆ ⋃ k, Θ k '' Ω k := by
  intro n F V hV hF
  -- a flattening chart `(Ω, Θ)` around every regular point `y₀` (the empty chart elsewhere)
  have hchart : ∀ y₀ : Euclid (n + 1), ∃ (Ω : Set (Euclid (n + 1)))
      (Θ : Euclid (n + 1) → Euclid (n + 1)), (IsOpen Ω ∧ ContDiffOn ℝ 1 Θ Ω ∧ InjOn Θ Ω ∧
        (∀ z ∈ Ω, Injective (fderiv ℝ Θ z)) ∧ IsOpen (Θ '' Ω) ∧ Θ '' Ω ⊆ V ∧
        ∀ z ∈ Ω, F (Θ z) = z 0) ∧ (y₀ ∈ V → fderiv ℝ F y₀ ≠ 0 → y₀ ∈ Θ '' Ω) := by
    intro y₀
    by_cases hy₀ : y₀ ∈ V ∧ fderiv ℝ F y₀ ≠ 0
    swap
    · refine ⟨∅, id, ⟨isOpen_empty, contDiffOn_empty, injOn_empty _, fun z hz => hz.elim,
        by rw [image_empty]; exact isOpen_empty, by rw [image_empty]; exact empty_subset _,
        fun z hz => hz.elim⟩, fun h₁ h₂ => (hy₀ ⟨h₁, h₂⟩).elim⟩
    obtain ⟨hy₀V, hL₀⟩ := hy₀
    -- a coordinate direction `e_j` with `DF(y₀) e_j ≠ 0`
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), fderiv ℝ F y₀ (EuclideanSpace.single j 1) ≠ 0 := by
      by_contra! h
      exact hL₀ (ContinuousLinearMap.coe_injective
        ((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.ext fun i => by simpa using h i))
    -- the orthonormal basis `b` with `b 0 = e_j`, and its coordinate map `Q = b.repr`
    let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).reindex (Equiv.swap 0 j)
    have hb0 : b 0 = EuclideanSpace.single j 1 := by
      simp [b, OrthonormalBasis.reindex_apply]
    let Q : Euclid (n + 1) →L[ℝ] Euclid (n + 1) := b.repr.toContinuousLinearEquiv
    let p : Euclid (n + 1) →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp Q
    let e₀ : Euclid (n + 1) := EuclideanSpace.single 0 1
    -- the flattening map `Φ(y) = Q y + (F y - (Q y)₀) e₀`, so that `Φ(y)₀ = F(y)`
    let Φ : Euclid (n + 1) → Euclid (n + 1) := fun y => Q y + (F y - p y) • e₀
    have hΦ0 : ∀ y, Φ y 0 = F y := fun y => by
      simp [Φ, p, e₀]
    have hΦ : ContDiff ℝ 1 Φ := Q.contDiff.add ((hF.sub p.contDiff).smul contDiff_const)
    have hΦd : ∀ y, HasFDerivAt Φ (Q + (fderiv ℝ F y - p).smulRight e₀) y := fun y =>
      Q.hasFDerivAt.add
        (((hF.differentiable one_ne_zero y).hasFDerivAt.sub p.hasFDerivAt).smul_const e₀)
    -- `DΦ(y₀)` is injective: `DΦ(y₀)h = 0` gives `DF(y₀)h = 0` and `Q h ∈ ℝe₀`, so `h ∈ ℝe_j`
    have hinj : Injective (fderiv ℝ Φ y₀) := by
      rw [(hΦd y₀).fderiv, injective_iff_map_eq_zero]
      intro h hh
      simp only [add_apply, ContinuousLinearMap.smulRight_apply, sub_apply] at hh
      have hL : fderiv ℝ F y₀ h = 0 := by
        have := congrArg (fun z : Euclid (n + 1) => z 0) hh
        simpa [p, e₀] using this
      have hQh : Q h = Q h 0 • e₀ := by
        rw [hL, zero_sub, add_eq_zero_iff_eq_neg, ← neg_smul, neg_neg] at hh
        simpa [p] using hh
      have hhb : h = Q h 0 • b 0 := by
        apply b.repr.injective
        rw [map_smul, b.repr_self]
        exact hQh
      have hc : Q h 0 = 0 := by
        have := congrArg (fderiv ℝ F y₀) hhb
        rw [map_smul, hL, hb0, smul_eq_mul] at this
        exact (mul_eq_zero.1 this.symm).resolve_right hj
      rw [hhb, hc, zero_smul]
    -- hence `DΦ(y₀)` is invertible and `Φ` is strictly differentiable at `y₀`
    let A₀ : Euclid (n + 1) ≃L[ℝ] Euclid (n + 1) :=
      (LinearEquiv.ofInjectiveEndo (fderiv ℝ Φ y₀ : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))
        hinj).toContinuousLinearEquiv
    have hA₀ : (A₀ : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) = fderiv ℝ Φ y₀ := by
      ext1 h
      rfl
    have hstrict : HasStrictFDerivAt Φ (A₀ : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) y₀ := by
      rw [hA₀]
      exact hΦ.contDiffAt.hasStrictFDerivAt one_ne_zero
    -- the inverse function theorem: a local homeomorphism `e` with `e = Φ` and `y₀ ∈ e.source`
    let e := hstrict.toOpenPartialHomeomorph Φ
    have he : (e : Euclid (n + 1) → Euclid (n + 1)) = Φ := hstrict.toOpenPartialHomeomorph_coe
    -- shrink the source to `W = source ∩ V ∩ {DΦ invertible}`; `Ω = Φ(W)`, `Θ = Φ⁻¹`
    let W := e.source ∩ V ∩ {y | ∃ A : Euclid (n + 1) ≃L[ℝ] Euclid (n + 1),
      (A : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) = fderiv ℝ Φ y}
    have hWo : IsOpen W := (e.open_source.inter hV).inter
      (ContinuousLinearEquiv.isOpen.preimage (hΦ.continuous_fderiv one_ne_zero))
    have hWs : W ⊆ e.source := fun y hy => hy.1.1
    have hΘΩ : e.symm '' (e '' W) = W := by
      rw [image_image, image_congr fun y hy => e.left_inv (hWs hy), image_id']
    -- at `y ∈ W`, `e` has an invertible derivative `A`
    have hderiv : ∀ y ∈ W, ∃ A : Euclid (n + 1) ≃L[ℝ] Euclid (n + 1),
        HasFDerivAt e (A : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) (e.symm (e y)) := by
      intro y hy
      obtain ⟨A, hA⟩ := hy.2
      refine ⟨A, ?_⟩
      rw [e.left_inv (hWs hy), he, hA]
      exact (hΦ.differentiable one_ne_zero y).hasFDerivAt
    refine ⟨e '' W, e.symm, ⟨e.isOpen_image_of_subset_source hWo hWs, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      fun _ _ => ?_⟩
    · -- `Θ` is `C¹` at `z = Φ(y)`, since `Φ` is `C¹` at `y` with invertible derivative
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨A, hA⟩ := hderiv y hy
      refine (e.contDiffAt_symm (e.map_source (hWs hy)) hA ?_).contDiffWithinAt
      rw [he]
      exact hΦ.contDiffAt
    · exact e.symm.injOn.mono (by rintro _ ⟨y, hy, rfl⟩; exact e.map_source (hWs hy))
    · -- `DΘ(z) = DΦ(Θz)⁻¹` is injective
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨A, hA⟩ := hderiv y hy
      rw [(e.hasFDerivAt_symm (e.map_source (hWs hy)) hA).fderiv]
      exact A.symm.injective
    · rw [hΘΩ]
      exact hWo
    · rw [hΘΩ]
      exact fun y hy => hy.1.2
    · -- `F(Θz) = Φ(Θz)₀ = z₀`
      rintro _ ⟨y, hy, rfl⟩
      rw [e.left_inv (hWs hy), he, hΦ0]
    · rw [hΘΩ]
      exact ⟨⟨hstrict.mem_toOpenPartialHomeomorph_source, hy₀V⟩, A₀, hA₀⟩
  -- countably many charts suffice (second countability); enumerate them
  choose Ωf Θf hΩf hmem using hchart
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun y => Θf y '' Ωf y)
    fun y => (hΩf y).2.2.2.2.1
  obtain ⟨f, hf⟩ := (hTc.insert (0 : Euclid (n + 1))).exists_eq_range (insert_nonempty _ _)
  refine ⟨fun k => Ωf (f k), fun k => Θf (f k), fun k => hΩf (f k), ?_⟩
  rintro y ⟨hyV, hy⟩
  have hyU : y ∈ ⋃ i ∈ T, Θf i '' Ωf i := hTU ▸ mem_iUnion.2 ⟨y, hmem y hyV hy⟩
  obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 hyU
  obtain ⟨k, rfl⟩ : i ∈ range f := hf ▸ mem_insert_of_mem _ hiT
  exact mem_iUnion.2 ⟨k, hyi⟩
/-- **Gradient of `F` along a `C¹` parametrisation** (step 0(b) of the chart co-area formula).
Let `ψ : ℝᴺ → ℝᴾ` and `F : ℝᴺ → ℝ` be `C¹`, with `Dψ(y)` injective on the open set `V`.  With
`M(y) = Dψ(y)* Dψ(y)` and `∇F(y)` the Riesz representative of `DF(y)`, put
`Ĝ(y) = Dψ(y) M(y)⁻¹ ∇F(y)` on `V` and `Ĝ = 0` off `V`.  On `V`, `M(y)` is injective
(`⟪M(y)a, a⟫ = |Dψ(y)a|²`), hence invertible; inversion is continuous at invertible operators, so
`Ĝ` is continuous on `V`, and Borel as a piecewise map over the open set `V`.  Then
`⟪Ĝ(y), Dψ(y)e⟫ = ⟪M(y)M(y)⁻¹∇F(y), e⟫ = DF(y)e`; if `v = Dψ(y)u` also represents `DF(y)`, then
`v - Ĝ(y)` lies in the range of `Dψ(y)` and is orthogonal to it, so `v = Ĝ(y)`; and `Ĝ(y) = 0`
iff `DF(y) = 0`.  Nothing is claimed about `ψ(V)`: `Ĝ` is a field along the parameter `y`. -/
theorem Submission.dtc_bc_lc_sl_cc_chart_gradient : ∀ (P N : ℕ) (ψ : Euclid N → Euclid P) (V : Set (Euclid N)) (F : Euclid N → ℝ), IsOpen V → ContDiff ℝ 1 ψ → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ Gh : Euclid N → Euclid P, Measurable Gh ∧ ContinuousOn Gh V ∧ ∀ y ∈ V, Gh y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid N →ₗ[ℝ] Euclid P) ∧ (∀ e, inner ℝ (Gh y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) ∧ (∀ v ∈ LinearMap.range (fderiv ℝ ψ y : Euclid N →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ y e) = fderiv ℝ F y e) → v = Gh y) ∧ (Gh y = 0 ↔ fderiv ℝ F y = 0) := by
  intro P N ψ V F hV hψ hinj hF
  classical
  -- `M(y) = Dψ(y)* ∘ Dψ(y)` and the gradient `∇F(y)`, the Riesz representative of `DF(y)`
  obtain ⟨M, hM⟩ : ∃ M : Euclid N → (Euclid N →L[ℝ] Euclid N),
      ∀ y, M y = (fderiv ℝ ψ y).adjoint ∘L fderiv ℝ ψ y := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Euclid N → Euclid N,
      ∀ y, g y = (InnerProductSpace.toDual ℝ (Euclid N)).symm (fderiv ℝ F y) := ⟨_, fun _ => rfl⟩
  -- `y ↦ Dψ(y)`, `y ↦ M(y)` and `y ↦ ∇F(y)` are continuous
  have hDψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv one_ne_zero
  have hMc : Continuous M :=
    ((ContinuousLinearMap.adjoint.continuous.comp hDψ).clm_comp hDψ).congr fun y => (hM y).symm
  have hgc : Continuous g :=
    ((InnerProductSpace.toDual ℝ (Euclid N)).symm.continuous.comp
      (hF.continuous_fderiv one_ne_zero)).congr fun y => (hg y).symm
  -- `⟪M(y)a, b⟫ = ⟪Dψ(y)a, Dψ(y)b⟫` and `⟪∇F(y), e⟫ = DF(y)e`
  have hMinner : ∀ y a b, inner ℝ (M y a) b = inner ℝ (fderiv ℝ ψ y a) (fderiv ℝ ψ y b) :=
    fun y a b => by
      rw [hM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
  have hginner : ∀ y e, inner ℝ (g y) e = fderiv ℝ F y e := fun y e => by
    rw [hg, InnerProductSpace.toDual_symm_apply]
  -- on `V`, `M(y)` is injective (`⟪M(y)a, a⟫ = |Dψ(y)a|²`), hence invertible
  have hMunit : ∀ y ∈ V, IsUnit (M y) := by
    intro y hy
    have hMinj : Injective (M y) := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      apply hinj y hy
      rw [map_zero, ← inner_self_eq_zero (𝕜 := ℝ), ← hMinner, ha, inner_zero_left]
    exact ContinuousLinearMap.isUnit_iff_bijective.2
      ⟨hMinj, LinearMap.injective_iff_surjective (f := (M y : Euclid N →ₗ[ℝ] Euclid N)).1 hMinj⟩
  -- `Ĝ₀(y) = Dψ(y) M(y)⁻¹ ∇F(y)`, with `Ring.inverse` continuous at the units `M(y)`, `y ∈ V`
  obtain ⟨G₀, hG₀⟩ : ∃ G₀ : Euclid N → Euclid P,
      ∀ y, G₀ y = fderiv ℝ ψ y (Ring.inverse (M y) (g y)) := ⟨_, fun _ => rfl⟩
  have hG₀c : ContinuousOn G₀ V := by
    intro y hy
    have hinv : ContinuousAt (fun z => Ring.inverse (M z)) y := by
      have h := NormedRing.inverse_continuousAt (hMunit y hy).unit
      rw [IsUnit.unit_spec] at h
      exact h.comp hMc.continuousAt
    rw [funext hG₀]
    exact (hDψ.continuousAt.clm_apply (hinv.clm_apply hgc.continuousAt)).continuousWithinAt
  -- (b) on `V`: `⟪Ĝ₀(y), Dψ(y)e⟫ = ⟪M(y)M(y)⁻¹∇F(y), e⟫ = ⟪∇F(y), e⟫ = DF(y)e`
  have hgrad : ∀ y ∈ V, ∀ e, inner ℝ (G₀ y) (fderiv ℝ ψ y e) = fderiv ℝ F y e := by
    intro y hy e
    rw [hG₀, ← hMinner, ← mul_apply_eq_comp, Ring.mul_inverse_cancel _ (hMunit y hy),
      one_apply_eq_self, hginner]
  -- `Ĝ = Ĝ₀` on `V` and `0` off `V`: Borel, since `V` is open and `Ĝ₀` is continuous on `V`
  refine ⟨V.piecewise G₀ fun _ => 0, hG₀c.measurable_piecewise continuousOn_const hV.measurableSet,
    hG₀c.congr fun y hy => piecewise_eq_of_mem _ _ _ hy, fun y hy => ?_⟩
  rw [piecewise_eq_of_mem _ _ _ hy]
  refine ⟨?_, hgrad y hy, ?_, ?_⟩
  · -- (a) `Ĝ₀(y) = Dψ(y)(M(y)⁻¹∇F(y))`
    rw [hG₀]
    exact LinearMap.mem_range.2 ⟨_, rfl⟩
  · -- (c) `v - Ĝ₀(y) = Dψ(y)(u - M(y)⁻¹∇F(y))` is orthogonal to the range of `Dψ(y)`
    intro v hv hve
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hv
    rw [ContinuousLinearMap.coe_coe] at hve ⊢
    have h0 : inner ℝ (fderiv ℝ ψ y u - G₀ y)
        (fderiv ℝ ψ y (u - Ring.inverse (M y) (g y))) = 0 := by
      rw [inner_sub_left, hve, hgrad y hy, sub_self]
    rwa [map_sub, ← hG₀, inner_self_eq_zero, sub_eq_zero] at h0
  · -- (d) by (b), and since `∇F(y) = 0` when `DF(y) = 0`
    constructor
    · intro h0
      refine ContinuousLinearMap.ext fun e => ?_
      rw [← hgrad y hy e, h0, inner_zero_left, zero_apply]
    · intro h0
      rw [hG₀, hg, h0, map_zero, map_zero, map_zero]
/-- **The Jacobian identity of the chart co-area argument.**  Let `A : ℝⁿ⁺¹ → ℝᴾ` be injective,
`v ∈ A(ℝⁿ⁺¹)` with `⟨v, A e⟩ = ℓ(e)`, `D` an injective endomorphism of `ℝⁿ⁺¹` with
`ℓ(D z) = z₀`, and `ι w = (0, w)`.  Then `C = A D ι` is injective, `C(ℝⁿ) = A(ℝⁿ⁺¹) ∩ v^⊥`,
and `J(C) = |v| J(A) |det D|`, where `J(X) = √det(X* X)`.

Proof sketch:
* `⟨v, A D z⟩ = z₀`.  So `⟨v, C w⟩ = 0`; and `A D z ⊥ v` forces `z₀ = 0`, i.e. `z = ι w`.
* `D` is onto, so `v = A D z⋆` with `z⋆₀ = |v|²`.  The shear `T z = z + z₀ (z⋆ − e₀)` has
  `det T = z⋆₀ = |v|²` (first row `(z⋆₀, 0, …, 0)`, lower-right block `1`).
* `N = A D T` sends `e₀ ↦ v` and `e_{j+1} ↦ C e'ⱼ ⊥ v`.  In the standard bases the Gram matrix
  of `N` has first row `(|v|², 0, …, 0)` and lower-right block the Gram matrix of `C`, so
  `det(N* N) = |v|² det(C* C)`.
* `det((X S)* (X S)) = (det S)² det(X* X)` gives `det(N* N) = |v|⁴ (det D)² det(A* A)`.  Cancel
  `|v|² ≠ 0` (`⟨v, A D e₀⟩ = 1`) and take square roots. -/
theorem Submission.dtc_bc_lc_sl_cc_jacobian_identity : ∀ (n P : ℕ) (A : Euclid (n + 1) →L[ℝ] Euclid P) (ℓ : Euclid (n + 1) →L[ℝ] ℝ) (v : Euclid P) (D : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) (ι : Euclid n →L[ℝ] Euclid (n + 1)), Injective A → v ∈ LinearMap.range (A : Euclid (n + 1) →ₗ[ℝ] Euclid P) → (∀ e, inner ℝ v (A e) = ℓ e) → Injective D → (∀ z, ℓ (D z) = z 0) → (∀ w, ι w 0 = 0 ∧ ∀ i : Fin n, ι w i.succ = w i) → Injective (A ∘L D ∘L ι) ∧ LinearMap.range ((A ∘L D ∘L ι : Euclid n →L[ℝ] Euclid P) : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (A : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ ∧ Real.sqrt (((A ∘L D ∘L ι).adjoint ∘L (A ∘L D ∘L ι)).det) = ‖v‖ * Real.sqrt ((A.adjoint ∘L A).det) * |D.det| := by
  intro n P A ℓ v D ι hA hv hℓ hD hDℓ hι
  -- `⟨v, A D z⟩ = ℓ (D z) = z₀`
  have hvAD : ∀ z, inner ℝ v (A (D z)) = z 0 := fun z => (hℓ (D z)).trans (hDℓ z)
  -- `ι` is injective: `(ι w)_{i+1} = w_i`
  have hιinj : Injective ι := fun w w' h => by
    ext i
    rw [← (hι w).2 i, ← (hι w').2 i, h]
  -- `D` is an injective endomorphism of `ℝⁿ⁺¹`, hence surjective
  have hDsurj : Surjective D :=
    (LinearMap.injective_iff_surjective (f := (D : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1)))).mp hD
  refine ⟨hA.comp (hD.comp hιinj), ?_, ?_⟩
  · -- the range: `C(ℝⁿ) = A(ℝⁿ⁺¹) ∩ (ℝ v)ᗮ`
    ext x
    simp only [Submodule.mem_inf, LinearMap.mem_range, ContinuousLinearMap.coe_coe,
      Submodule.mem_orthogonal_singleton_iff_inner_right]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨D (ι w), rfl⟩, (hvAD (ι w)).trans (hι w).1⟩
    · -- `x = A D z ⊥ v` forces `z₀ = 0`, so `z = ι w` with `wᵢ = z_{i+1}`
      rintro ⟨⟨y, rfl⟩, hy⟩
      obtain ⟨z, rfl⟩ := hDsurj y
      have hz : z 0 = 0 := (hvAD z).symm.trans hy
      have hιz : ι (WithLp.toLp 2 fun i : Fin n => z i.succ) = z := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rw [(hι _).1, hz]
        · rw [(hι _).2 j]
      exact ⟨WithLp.toLp 2 fun i : Fin n => z i.succ, by simp [hιz]⟩
  · -- the Jacobian identity, via Gram matrices in the standard orthonormal bases `e`, `e'`
    let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
    let b' := EuclideanSpace.basisFun (Fin n) ℝ
    -- `det (X* X) = det [⟨X eᵢ, X eⱼ⟩]` for an orthonormal basis `e`
    have hgram : ∀ (m : ℕ) (X : Euclid m →L[ℝ] Euclid P) (e : OrthonormalBasis (Fin m) ℝ (Euclid m)),
        (X.adjoint ∘L X).det = (Matrix.of fun i j => inner ℝ (X (e i)) (X (e j))).det := by
      intro m X e
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e.toBasis]
      congr 1
      ext i j
      simp only [Matrix.of_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
        OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    -- `det S* = det S`, hence `det ((X S)* (X S)) = (det S)² det (X* X)`
    have hadj : ∀ S : Euclid (n + 1) →L[ℝ] Euclid (n + 1), S.adjoint.det = S.det := by
      intro S
      rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ← ContinuousLinearMap.adjoint_toLinearMap,
        ← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b, Matrix.det_conjTranspose,
        LinearMap.det_toMatrix, star_trivial]
    have hcomp : ∀ (X : Euclid (n + 1) →L[ℝ] Euclid P) (S : Euclid (n + 1) →L[ℝ] Euclid (n + 1)),
        ((X ∘L S).adjoint ∘L (X ∘L S)).det = S.det ^ 2 * (X.adjoint ∘L X).det := by
      intro X S
      have h : (X ∘L S).adjoint ∘L (X ∘L S) = S.adjoint ∘L ((X.adjoint ∘L X) ∘L S) := by
        rw [ContinuousLinearMap.adjoint_comp]
        rfl
      have h2 : (S.adjoint ∘L ((X.adjoint ∘L X) ∘L S)).det =
          S.adjoint.det * ((X.adjoint ∘L X).det * S.det) := by
        simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
      rw [h, h2, hadj]
      ring
    -- `ι e'ⱼ = e_{j+1}`
    have hιb : ∀ j : Fin n, ι (b' j) = b j.succ := by
      intro j
      ext i
      refine Fin.cases ?_ (fun k => ?_) i
      · rw [(hι _).1]
        simp [b, EuclideanSpace.basisFun_apply]
      · rw [(hι _).2 k]
        simp [b, b', EuclideanSpace.basisFun_apply]
    -- `v = A D z⋆`, and `z⋆₀ = ⟨v, A D z⋆⟩ = |v|²`
    obtain ⟨y, hy⟩ := hv
    obtain ⟨zs, rfl⟩ := hDsurj y
    have hy' : A (D zs) = v := hy
    have hzs : zs 0 = ‖v‖ ^ 2 := by rw [← hvAD zs, hy', real_inner_self_eq_norm_sq]
    -- the shear `T z = z + z₀ (z⋆ - e₀)`: `T e₀ = z⋆`, `T e_{j+1} = e_{j+1}`, so `det T = z⋆₀`
    -- (its matrix has first row `(z⋆₀, 0, …, 0)` and lower-right block `1`)
    let T : Euclid (n + 1) →L[ℝ] Euclid (n + 1) :=
      ContinuousLinearMap.id ℝ _ + (EuclideanSpace.proj 0).smulRight (zs - b 0)
    have hT0 : T (b 0) = zs := by
      simp [T, b, EuclideanSpace.basisFun_apply]
    have hTs : ∀ j : Fin n, T (b j.succ) = b j.succ := by
      intro j
      simp [T, b, EuclideanSpace.basisFun_apply]
    have hdetT : T.det = ‖v‖ ^ 2 := by
      have hM : ∀ i j, LinearMap.toMatrix b.toBasis b.toBasis T i j = T (b j) i := by
        intro i j
        simp [b, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_repr]
      have hsub : (LinearMap.toMatrix b.toBasis b.toBasis T).submatrix Fin.succ Fin.succ = 1 := by
        ext i j
        rw [Matrix.submatrix_apply, hM, hTs, Matrix.one_apply]
        simp [b, EuclideanSpace.basisFun_apply]
      rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b.toBasis, Matrix.det_succ_row_zero,
        Fin.sum_univ_succ, Fin.succAbove_zero, hsub]
      simp only [hM, hT0, hTs, ← hzs]
      simp [b, EuclideanSpace.basisFun_apply]
    -- `N = A D T` has `N e₀ = v ⊥ C(ℝⁿ)` and `N e_{j+1} = C e'ⱼ`: its Gram matrix has first row
    -- `(|v|², 0, …, 0)` and lower-right block the Gram matrix of `C`
    have hdetN : (((A ∘L D) ∘L T).adjoint ∘L ((A ∘L D) ∘L T)).det =
        ‖v‖ ^ 2 * ((A ∘L D ∘L ι).adjoint ∘L (A ∘L D ∘L ι)).det := by
      have hN0 : ((A ∘L D) ∘L T) (b 0) = v := by
        simp only [ContinuousLinearMap.comp_apply, hT0, hy']
      have hNs : ∀ j : Fin n, ((A ∘L D) ∘L T) (b j.succ) = (A ∘L D ∘L ι) (b' j) := by
        intro j
        simp only [ContinuousLinearMap.comp_apply, hTs, hιb]
      have hrow : ∀ j : Fin n, inner ℝ v (((A ∘L D) ∘L T) (b j.succ)) = 0 := by
        intro j
        rw [hNs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvAD, (hι _).1]
      have hsub : (Matrix.of fun i j => inner ℝ (((A ∘L D) ∘L T) (b i))
          (((A ∘L D) ∘L T) (b j))).submatrix Fin.succ Fin.succ =
          Matrix.of fun i j => inner ℝ ((A ∘L D ∘L ι) (b' i)) ((A ∘L D ∘L ι) (b' j)) := by
        ext i j
        simp only [Matrix.submatrix_apply, Matrix.of_apply, hNs]
      rw [hgram _ _ b, hgram _ _ b', Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove_zero,
        hsub]
      simp only [Matrix.of_apply, hN0, hrow, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        real_inner_self_eq_norm_sq]
      simp
    -- `det (N* N) = (det T)² (det D)² det (A* A)`; cancel `|v|² ≠ 0`
    have hv0 : ‖v‖ ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 (norm_ne_zero_iff.mpr fun h0 => ?_)
      have h1 := hvAD (b 0)
      rw [h0, inner_zero_left] at h1
      simp [b, EuclideanSpace.basisFun_apply] at h1
    have hkey : ‖v‖ ^ 2 * ((A ∘L D ∘L ι).adjoint ∘L (A ∘L D ∘L ι)).det =
        ‖v‖ ^ 2 * (‖v‖ ^ 2 * D.det ^ 2 * (A.adjoint ∘L A).det) := by
      rw [← hdetN, hcomp, hcomp, hdetT]
      ring
    rw [mul_left_cancel₀ hv0 hkey, show ‖v‖ ^ 2 * D.det ^ 2 * (A.adjoint ∘L A).det =
      (‖v‖ * |D.det|) ^ 2 * (A.adjoint ∘L A).det by rw [mul_pow, sq_abs],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring
/-- **Simon Ch. 2, Theorem 6.4** (`C¹` Sard type), its critical part, with Eilenberg's inequality
(Simon Ch. 2, 1.9) in place of the co-area formula: if Eilenberg's inequality holds on `ℝⁿ⁺¹`
with constant `C`, `F` is `C¹` and `DF = 0` on `Z`, then `Hⁿ(Z ∩ F⁻¹{t}) = 0` for a.e. `t`.
It suffices to treat `Z ⊆ B̄(0, R)`.  For `ε > 0`, uniform continuity of `DF` on `B̄(0, R + 1)`
gives `δ`; the disjointed balls `D m ⊆ B(x m, r)`, `2r = min δ 1`, around a dense sequence are
Borel, pairwise disjoint and cover `ℝⁿ⁺¹`.  If `p ∈ Z ∩ D m`, then `‖DF‖ = ‖DF − DF(p)‖ < ε`
on the convex ball `B(x m, r)`, so `F` is `ε`-Lipschitz on `Z ∩ D m` (mean value inequality).
The sum `Φ_ε` of the Eilenberg majorants dominates `Hⁿ(Z ∩ F⁻¹{t})` and
`∫ Φ_ε ≤ C ε Hⁿ⁺¹(B̄(0, R))`, so `inf_k Φ_{1/(k+1)}` is a Borel majorant with zero integral. -/
theorem Submission.dtc_bc_lc_sl_cc_critical_null : ∀ (n : ℕ) (C : NNReal), (∀ (A : Set (Euclid (n + 1))) (f : Euclid (n + 1) → ℝ) (L : NNReal), LipschitzOnWith L f A → ∃ φ : ℝ → ℝ≥0∞, Measurable φ ∧ (∀ t, μHE[n] (A ∩ f ⁻¹' {t}) ≤ φ t) ∧ ∫⁻ t, φ t ≤ (C : ℝ≥0∞) * (L : ℝ≥0∞) * μHE[n + 1] A) → ∀ (F : Euclid (n + 1) → ℝ) (Z : Set (Euclid (n + 1))), ContDiff ℝ 1 F → (∀ y ∈ Z, fderiv ℝ F y = 0) → ∀ᵐ t, μHE[n] (Z ∩ F ⁻¹' {t}) = 0 := by
  intro n C hEil F Z hF hZ
  -- Step 1: it suffices to treat the bounded pieces `Z ∩ B̄(0, R)`
  suffices key : ∀ R : ℝ, ∀ᵐ t, μHE[n] ((Z ∩ closedBall 0 R) ∩ F ⁻¹' {t}) = 0 by
    filter_upwards [ae_all_iff.2 fun m : ℕ => key m] with t ht
    refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null ht)
    obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨m, ⟨hx.1, mem_closedBall_zero_iff.2 hm⟩, hx.2⟩
  intro R
  -- Step 2: `DF` is uniformly continuous on `K₁ = B̄(0, R + 1)`
  have hdiff : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hDF : UniformContinuousOn (fderiv ℝ F) (closedBall 0 (R + 1)) :=
    (isCompact_closedBall _ _).uniformContinuousOn_of_continuous
      (hF.continuous_fderiv one_ne_zero).continuousOn
  -- `μHE[n + 1]` is Lebesgue measure on `ℝⁿ⁺¹`, so `μHE[n + 1] (B̄(0, R)) < ∞`
  have hK : μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R) ≠ ∞ := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_closedBall_lt_top.ne
  -- Steps 3-5: for every `ε > 0` a Borel majorant `Φ` with `∫ Φ ≤ C ε μHE[n + 1] (B̄(0, R))`
  have main : ∀ ε : NNReal, 0 < ε → ∃ Φ : ℝ → ℝ≥0∞, Measurable Φ ∧
      (∀ t, μHE[n] ((Z ∩ closedBall 0 R) ∩ F ⁻¹' {t}) ≤ Φ t) ∧
      ∫⁻ t, Φ t ≤ (C : ℝ≥0∞) * ε * μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 hDF ε (NNReal.coe_pos.2 hε)
    -- the disjointed balls `D m ⊆ B(x m, r)`, `2 r = min δ 1`, partition `ℝⁿ⁺¹`
    obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ 2 * r = min δ 1 :=
      ⟨min δ 1 / 2, by positivity, by ring⟩
    set x := TopologicalSpace.denseSeq (Euclid (n + 1))
    set D := disjointed fun m => ball (x m) r
    have hDcov : ∀ y, ∃ m, y ∈ D m := by
      intro y
      obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq _) y r hr0
      have hy : y ∈ ⋃ m, D m := by
        rw [iUnion_disjointed]
        exact mem_iUnion.2 ⟨m, mem_ball.2 hm⟩
      exact mem_iUnion.1 hy
    -- `F` is `ε`-Lipschitz on each piece `Z ∩ B̄(0, R) ∩ D m`: if `p` lies in it, then
    -- `|w - p| < min δ 1` on `B(x m, r)`, so `‖DF(w)‖ = ‖DF(w) - DF(p)‖ < ε` there
    have hlip : ∀ m, LipschitzOnWith ε F ((Z ∩ closedBall 0 R) ∩ D m) := by
      intro m
      rcases ((Z ∩ closedBall 0 R) ∩ D m).eq_empty_or_nonempty with he | ⟨p, ⟨hpZ, hpR⟩, hpD⟩
      · rw [he]
        exact lipschitzOnWith_empty _ _
      refine (Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun w _ => hdiff w) (fun w hw => ?_)
        (convex_ball (x m) r)).mono (inter_subset_right.trans (disjointed_subset _ m))
      have hpB : p ∈ ball (x m) r := disjointed_subset _ m hpD
      have hwp : dist w p < min δ 1 := by
        rw [mem_ball] at hw hpB
        linarith [dist_triangle_right w p (x m)]
      have hpR' : ‖p‖ ≤ R := mem_closedBall_zero_iff.1 hpR
      have hwK : w ∈ closedBall (0 : Euclid (n + 1)) (R + 1) := by
        rw [mem_closedBall_zero_iff]
        have h1 : ‖w‖ ≤ ‖p‖ + ‖w - p‖ := norm_le_norm_add_norm_sub' w p
        rw [← dist_eq_norm] at h1
        linarith [min_le_right δ 1]
      have hpK : p ∈ closedBall (0 : Euclid (n + 1)) (R + 1) :=
        mem_closedBall_zero_iff.2 (by linarith)
      have h := hδε w hwK p hpK (hwp.trans_le (min_le_left δ 1))
      rw [hZ p hpZ, dist_zero_right] at h
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact h.le
    -- Eilenberg's inequality on each piece
    choose φ hφm hφle hφint using fun m => hEil _ F ε (hlip m)
    refine ⟨fun t => ∑' m, φ m t, Measurable.tsum hφm, fun t => ?_, ?_⟩
    · -- countable subadditivity: the pieces cover `Z ∩ B̄(0, R)`
      calc μHE[n] ((Z ∩ closedBall 0 R) ∩ F ⁻¹' {t})
          ≤ μHE[n] (⋃ m, ((Z ∩ closedBall 0 R) ∩ D m) ∩ F ⁻¹' {t}) := by
            refine measure_mono fun y hy => ?_
            obtain ⟨m, hm⟩ := hDcov y
            exact mem_iUnion.2 ⟨m, ⟨hy.1, hm⟩, hy.2⟩
        _ ≤ ∑' m, μHE[n] (((Z ∩ closedBall 0 R) ∩ D m) ∩ F ⁻¹' {t}) := measure_iUnion_le _
        _ ≤ ∑' m, φ m t := ENNReal.tsum_le_tsum fun m => hφle m t
    · -- integrate term by term; the pieces lie in the disjoint Borel sets `B̄(0, R) ∩ D m`
      rw [lintegral_tsum fun m => (hφm m).aemeasurable]
      calc ∑' m, ∫⁻ t, φ m t
          ≤ ∑' m, (C : ℝ≥0∞) * ε * μHE[n + 1] ((Z ∩ closedBall 0 R) ∩ D m) :=
            ENNReal.tsum_le_tsum hφint
        _ = (C : ℝ≥0∞) * ε * ∑' m, μHE[n + 1] ((Z ∩ closedBall 0 R) ∩ D m) :=
            ENNReal.tsum_mul_left
        _ ≤ (C : ℝ≥0∞) * ε * μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R) := by
            gcongr
            calc ∑' m, μHE[n + 1] ((Z ∩ closedBall 0 R) ∩ D m)
                ≤ ∑' m, μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R ∩ D m) :=
                  ENNReal.tsum_le_tsum fun m =>
                    measure_mono (inter_subset_inter_left _ inter_subset_right)
              _ ≤ μHE[n + 1] (⋃ m, closedBall (0 : Euclid (n + 1)) R ∩ D m) :=
                  tsum_meas_le_meas_iUnion_of_disjoint _
                    (fun m => measurableSet_closedBall.inter
                      (MeasurableSet.disjointed (fun i => measurableSet_ball) m))
                    (fun i j hij => (disjoint_disjointed _ hij).mono inter_subset_right
                      inter_subset_right)
              _ ≤ μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R) :=
                  measure_mono (iUnion_subset fun m => inter_subset_left)
  -- Step 6: the infimum `Ψ` of the majorants for `ε = (k + 1)⁻¹` has zero integral
  choose Φ hΦm hΦle hΦint using fun k : ℕ => main ((k + 1 : ℕ) : NNReal)⁻¹ (by positivity)
  have hlim : Tendsto (fun k : ℕ => (C : ℝ≥0∞) * ((((k + 1 : ℕ) : NNReal)⁻¹ : NNReal) : ℝ≥0∞) *
      μHE[n + 1] (closedBall (0 : Euclid (n + 1)) R)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞))
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (Or.inr ENNReal.coe_ne_top)) (Or.inr hK)
    simpa [ENNReal.coe_inv, Function.comp_def] using h
  have hΨ : ∫⁻ t, ⨅ k, Φ k t = 0 :=
    le_antisymm (ge_of_tendsto' hlim fun k =>
      (lintegral_mono fun t => iInf_le _ k).trans (hΦint k)) zero_le
  filter_upwards [(lintegral_eq_zero_iff (Measurable.iInf hΦm)).1 hΨ] with t ht
  exact le_antisymm ((le_iInf fun k => hΦle k t).trans_eq ht) zero_le

/-- Level parametrisations of a straightened chart (Simon Ch. 2, §6, co-area formula 6.3/6.6;
step 2 of the chart co-area argument).  Let `c(s, w) = (s, w₀, …, wₙ₋₁)`, let `ψ : ℝⁿ⁺¹ → ℝᴾ` be
`C¹` and injective with injective derivative on `V`, `F : ℝⁿ⁺¹ → ℝ` be `C¹`, and `Θ` be `C¹` and
injective with injective derivative on the open `Ω`, with `Θ(Ω) ⊆ V` and `F ∘ Θ = (·)₀` on `Ω`.
Fix `t`.  Then `Ωᵗ = {w | c(t, w) ∈ Ω}` is open and `χ = ψ ∘ Θ ∘ c(t, ·)` is `C¹` and injective
on `Ωᵗ`.  At `w ∈ Ωᵗ`, with `z = c(t, w)` and `y = Θ(z)`: `DF(y) ≠ 0`, `Dχ(w)` is injective,
and for every `v ∈ Dψ(y)(ℝⁿ⁺¹)` with `⟨v, Dψ(y)e⟩ = DF(y)e` for all `e`,
`Dχ(w)(ℝⁿ) = Dψ(y)(ℝⁿ⁺¹) ∩ (ℝv)^⊥` and `J(Dχ(w)) = |v| J(Dψ(y)) |det DΘ(z)|`, where
`J(X) = √det(X*X)`.

Proof sketch:
* `ι w := c(t, w) − c(t, 0)` is linear with `(ι w)₀ = 0`, `(ι w)ᵢ₊₁ = wᵢ` (compare coordinates),
  so `c(t, ·) = c(t, 0) + ι` is a `C¹` affine injection; hence `Ωᵗ` is open and `χ` is `C¹` on it.
* `χ` is injective on `Ωᵗ`: `ψ` is injective on `V ⊇ Θ(Ω)`, `Θ` on `Ω`, and `c(t, ·)` everywhere.
* Chain rule: `Dχ(w) = Dψ(y) ∘ DΘ(z) ∘ ι`.  As `F ∘ Θ = (·)₀` on the neighbourhood `Ω` of `z`,
  `DF(y)(DΘ(z) z') = z'₀` for all `z'`; at `z' = e₀` this gives `DF(y) ≠ 0`.
* `Dχ(w)` is injective as a composite of injective maps; the range and the Jacobian identity are
  `dtc_bc_lc_sl_cc_jacobian_identity` for `Dψ(y)`, `DF(y)`, `v`, `DΘ(z)` and `ι`. -/
theorem Submission.dtc_bc_lc_sl_cc_slice_param : ∀ (P n : ℕ) (c : ℝ → Euclid n → Euclid (n + 1)) (ψ : Euclid (n + 1) → Euclid P) (V Ω : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (Θ : Euclid (n + 1) → Euclid (n + 1)) (t : ℝ), (∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i) → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → (∀ z ∈ Ω, Injective (fderiv ℝ Θ z)) → Θ '' Ω ⊆ V → (∀ z ∈ Ω, F (Θ z) = z 0) → IsOpen {w | c t w ∈ Ω} ∧ ContDiffOn ℝ 1 (fun w => ψ (Θ (c t w))) {w | c t w ∈ Ω} ∧ InjOn (fun w => ψ (Θ (c t w))) {w | c t w ∈ Ω} ∧ ∀ w, c t w ∈ Ω → fderiv ℝ F (Θ (c t w)) ≠ 0 ∧ Injective (fderiv ℝ (fun w' => ψ (Θ (c t w'))) w) ∧ ∀ v ∈ LinearMap.range (fderiv ℝ ψ (Θ (c t w)) : Euclid (n + 1) →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ (Θ (c t w)) e) = fderiv ℝ F (Θ (c t w)) e) → LinearMap.range (fderiv ℝ (fun w' => ψ (Θ (c t w'))) w : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (fderiv ℝ ψ (Θ (c t w)) : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ ∧ Real.sqrt (((fderiv ℝ (fun w' => ψ (Θ (c t w'))) w).adjoint ∘L fderiv ℝ (fun w' => ψ (Θ (c t w'))) w).det) = ‖v‖ * Real.sqrt (((fderiv ℝ ψ (Θ (c t w))).adjoint ∘L fderiv ℝ ψ (Θ (c t w))).det) * |(fderiv ℝ Θ (c t w)).det| := by
  intro P n c ψ V Ω F Θ t hc hψ hψinj hψd hF hΩ hΘ hΘinj hΘd hΘV hFΘ
  have hc0 : ∀ s w, c s w 0 = s := fun s w => (hc s w).1
  have hcs : ∀ s w (i : Fin n), c s w i.succ = w i := fun s w => (hc s w).2
  -- Step 1: `ι w := c(t, w) − c(t, 0)` is linear, `(ι w)₀ = 0`, `(ι w)ᵢ₊₁ = wᵢ`
  let ιₗ : Euclid n →ₗ[ℝ] Euclid (n + 1) :=
    { toFun := fun w => c t w - c t 0
      map_add' := fun w w' => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hc0]
        · simp [hcs]
      map_smul' := fun a w => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hc0]
        · simp [hcs] }
  let ι : Euclid n →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap ιₗ
  have hιapp : ∀ w, ι w = c t w - c t 0 := fun w => rfl
  have hιcoord : ∀ w, ι w 0 = 0 ∧ ∀ i : Fin n, ι w i.succ = w i := fun w =>
    ⟨by simp [hιapp, hc0], fun i => by simp [hιapp, hcs]⟩
  have hιinj : Injective ι := fun w w' h => by
    ext i
    rw [← (hιcoord w).2 i, ← (hιcoord w').2 i, h]
  -- `c(t, ·) = c(t, 0) + ι` is a `C¹` affine map with derivative `ι`
  have hcfun : (fun w => c t w) = fun w => c t 0 + ι w := by
    funext w
    rw [hιapp, add_sub_cancel]
  have hcd : ∀ w, HasFDerivAt (fun w => c t w) ι w := fun w => by
    rw [hcfun]
    exact ι.hasFDerivAt.const_add (c t 0)
  have hccd : ContDiff ℝ 1 (fun w => c t w) := by
    rw [hcfun]
    exact contDiff_const.add ι.contDiff
  -- Step 2: `Ωᵗ` is open
  have hopen : IsOpen {w | c t w ∈ Ω} := hccd.continuous.isOpen_preimage Ω hΩ
  -- Step 3: `χ` is `C¹` on `Ωᵗ`
  have hcda : ∀ w, c t w ∈ Ω → ContDiffAt ℝ 1 (fun w' => ψ (Θ (c t w'))) w := fun w hw =>
    hψ.contDiffAt.comp w ((hΘ.contDiffAt (hΩ.mem_nhds hw)).comp w hccd.contDiffAt)
  refine ⟨hopen, fun w hw => (hcda w hw).contDiffWithinAt, ?_, ?_⟩
  · -- Step 4: `χ` is injective on `Ωᵗ`
    intro w hw w' hw' h
    have h₁ : Θ (c t w) = Θ (c t w') :=
      hψinj (hΘV (mem_image_of_mem Θ hw)) (hΘV (mem_image_of_mem Θ hw')) h
    apply hιinj
    rw [hιapp, hιapp, hΘinj hw hw' h₁]
  -- Step 5: derivatives at `w ∈ Ωᵗ`, with `z = c(t, w)` and `y = Θ(z)`
  intro w hw
  have hΘz : HasFDerivAt Θ (fderiv ℝ Θ (c t w)) (c t w) :=
    (hΘ.contDiffAt (hΩ.mem_nhds hw)).differentiableAt_one.hasFDerivAt
  have hψy : HasFDerivAt ψ (fderiv ℝ ψ (Θ (c t w))) (Θ (c t w)) :=
    hψ.contDiffAt.differentiableAt_one.hasFDerivAt
  have hFy : HasFDerivAt F (fderiv ℝ F (Θ (c t w))) (Θ (c t w)) :=
    hF.contDiffAt.differentiableAt_one.hasFDerivAt
  -- chain rule: `Dχ(w) = Dψ(y) ∘ DΘ(z) ∘ ι`
  have hχ : HasFDerivAt (fun w' => ψ (Θ (c t w')))
      (fderiv ℝ ψ (Θ (c t w)) ∘L fderiv ℝ Θ (c t w) ∘L ι) w :=
    hψy.comp w (hΘz.comp w (hcd w))
  rw [hχ.fderiv]
  -- `F ∘ Θ = (·)₀` on the neighbourhood `Ω` of `z`, so `DF(y) ∘ DΘ(z) = (·)₀`
  have hproj : HasFDerivAt (fun z' : Euclid (n + 1) => z' 0)
      (EuclideanSpace.proj (0 : Fin (n + 1)) : Euclid (n + 1) →L[ℝ] ℝ) (c t w) :=
    (EuclideanSpace.proj (0 : Fin (n + 1)) : Euclid (n + 1) →L[ℝ] ℝ).hasFDerivAt
  have hℓD : fderiv ℝ F (Θ (c t w)) ∘L fderiv ℝ Θ (c t w) = EuclideanSpace.proj 0 :=
    ((hFy.comp (c t w) hΘz).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hΩ.mem_nhds hw) fun z' hz' => (hFΘ z' hz').symm)).unique hproj
  have hℓDz : ∀ z', fderiv ℝ F (Θ (c t w)) (fderiv ℝ Θ (c t w) z') = z' 0 := fun z' =>
    congrArg (fun L : Euclid (n + 1) →L[ℝ] ℝ => L z') hℓD
  -- Step 6: `DF(y) ≠ 0`, since `DF(y)(DΘ(z) e₀) = 1`
  have hFne : fderiv ℝ F (Θ (c t w)) ≠ 0 := by
    intro h0
    have h₁ := hℓDz (EuclideanSpace.single 0 1)
    rw [h0] at h₁
    simp at h₁
  -- Step 7: `Dχ(w)` is injective as a composite of injective maps
  have hAinj : Injective (fderiv ℝ ψ (Θ (c t w))) := hψd _ (hΘV (mem_image_of_mem Θ hw))
  have hDinj : Injective (fderiv ℝ Θ (c t w)) := hΘd _ hw
  refine ⟨hFne, hAinj.comp (hDinj.comp hιinj), fun v hv hvℓ => ?_⟩
  -- Step 8: the range and the Jacobian identity, from `jacobian_identity`
  exact (Submission.dtc_bc_lc_sl_cc_jacobian_identity n P (fderiv ℝ ψ (Θ (c t w)))
    (fderiv ℝ F (Θ (c t w))) v (fderiv ℝ Θ (c t w)) ι hAinj hv hvℓ hDinj hℓDz hιcoord).2

/-- Co-area formula on one chart piece (Simon Ch. 2, §6, (6.6)).  `ψ` is an injective `C¹`
immersion of the open `V ⊆ ℝ^{n+1}` into `ℝᴾ`, `F` is `C¹`, the `C¹` chart `Θ` of `Ω`
straightens `F` (`F(Θ z) = z₀`) and `G ∘ ψ` is the tangential gradient of `F` on the Borel
`Y' ⊆ Θ(Ω)`.  Then `t ↦ ∫_{ψ(Y' ∩ F⁻¹(t))} g dHⁿ` is Borel and
`∫_ℝ ∫_{ψ(Y' ∩ F⁻¹(t))} g dHⁿ dt = ∫_{ψ(Y')} |G| g dH^{n+1}`.

Proof sketch:
* Area formula (Simon Ch. 2, (3.1)–(3.5)), proved inline: for an injective `C¹` immersion `χ`
  of an open `U ⊆ ℝᵐ` and Borel `S ⊆ U`, `∫_{χ(S)} h dHᵐ = ∫_S J_χ · h ∘ χ dLᵐ`, where
  `J_χ = √det(Dχ* Dχ)`.  For linear injective `L = ι ∘ B` (`ι` an isometry onto `L(ℝᵐ)`),
  `Hᵐ(L A) = |det B| Lᵐ(A)` and `√det(L* L) = |det B|`.  Near `w₀`, `χ` and `L = Dχ(w₀)` are
  `a`-bi-Lipschitz equivalent and `J_χ ≈ J_χ(w₀)`, so `Hᵐ(χ B)` and `∫_B J_χ` agree up to
  `a^{m+1}`; a countable disjoint cover globalizes this, and `a ↓ 1` gives
  `Hᵐ(χ B) = ∫_B J_χ`.  Finally `χ` pushes `J_χ Lᵐ⌞S` forward to `Hᵐ⌞χ(S)`.
* `chart_gradient` gives a Borel `Ĝ` with `G ∘ ψ = Ĝ` on `Y'` (uniqueness); put
  `f = J_ψ · |Ĝ| · g ∘ ψ`, and `flat_fubini` gives `∫_ℝ I = ∫_{Y'} f` with `I` Borel.
* For each `t`, with `c(t, w) = (t, w)` and `χ = ψ ∘ Θ ∘ c(t, ·)`,
  `ψ(Y' ∩ F⁻¹(t)) = χ(Sᵗ)`, `Sᵗ = c(t, ·)⁻¹(Ω ∩ Θ⁻¹(Y'))`; the area formula for `χ` and the
  Jacobian identity `J_χ = |Ĝ| · J_ψ · |det DΘ|` of `slice_param` give
  `∫_{ψ(Y' ∩ F⁻¹(t))} g dHⁿ = I(t)`.
* The area formula for `ψ` on `Y'` turns `∫_{Y'} f` into `∫_{ψ(Y')} |G| g dH^{n+1}`. -/
theorem Submission.dtc_bc_lc_sl_cc_piece_coarea : ∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Ω Y' : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (Θ : Euclid (n + 1) → Euclid (n + 1)) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen Ω → ContDiffOn ℝ 1 Θ Ω → InjOn Θ Ω → (∀ z ∈ Ω, Injective (fderiv ℝ Θ z)) → Θ '' Ω ⊆ V → (∀ z ∈ Ω, F (Θ z) = z 0) → MeasurableSet Y' → Y' ⊆ Θ '' Ω → (∀ y ∈ Y', G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ g : Euclid P → ℝ≥0∞, Measurable g → Measurable (fun t => ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y', ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] := by
  intro P n ψ V Ω Y' F Θ G hV hψ hψinj hDψ hF hΩ hΘ hΘinj hDΘ hΘV hFΘ hY' hY'Θ hG g hg
  -- the injective area formula for `C¹` immersions (Simon Ch. 2, (3.5)), any weight `h`
  have harea : ∀ (m : ℕ) (χ : Euclid m → Euclid P) (U : Set (Euclid m)), IsOpen U →
      ContDiffOn ℝ 1 χ U → InjOn χ U → (∀ w ∈ U, Injective (fderiv ℝ χ w)) →
      ∀ S ⊆ U, MeasurableSet S → ∀ h : Euclid P → ℝ≥0∞,
        ∫⁻ x in χ '' S, h x ∂μHE[m] =
          ∫⁻ w in S, ENNReal.ofReal (Real.sqrt (((fderiv ℝ χ w).adjoint ∘L fderiv ℝ χ w).det)) *
            h (χ w) := by
    intro m χ U hU hχ hinj hreg
    -- (a) the linear area formula
    have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L →
        0 < Real.sqrt ((L.adjoint ∘L L).det) ∧ ∀ A : Set (Euclid m),
          μHE[m] (L '' A) = ENNReal.ofReal (Real.sqrt ((L.adjoint ∘L L).det)) * volume A := by
      intro L hL
      set T : Submodule ℝ (Euclid P) := LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)
      have hTdim : Module.finrank ℝ T = m := by
        rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
      let b : OrthonormalBasis (Fin m) ℝ T := (stdOrthonormalBasis ℝ T).reindex (finCongr hTdim)
      let ι : Euclid m →ₗᵢ[ℝ] Euclid P := T.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
      let B : Euclid m →ₗ[ℝ] Euclid m :=
        b.repr.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
      have hLB : ∀ v, L v = ι (B v) := by
        intro v
        simp [ι, B]
      have hBinj : Injective B := by
        intro u v huv
        apply hL
        rw [hLB u, hLB v, huv]
      have hL' : L = ι.toContinuousLinearMap ∘L LinearMap.toContinuousLinearMap B := by
        ext1 v
        exact hLB v
      have hLLBB : L.adjoint ∘L L =
          (LinearMap.toContinuousLinearMap B).adjoint ∘L LinearMap.toContinuousLinearMap B := by
        rw [hL', ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ ι.toContinuousLinearMap,
          LinearIsometry.adjoint_comp_self]
        rfl
      have hdetadj : ((LinearMap.toContinuousLinearMap B).adjoint).det = LinearMap.det B := by
        let e := EuclideanSpace.basisFun (Fin m) ℝ
        rw [← LinearMap.adjoint_toContinuousLinearMap, ContinuousLinearMap.det,
          LinearMap.coe_toContinuousLinearMap, ← LinearMap.det_toMatrix e.toBasis,
          ← LinearMap.det_toMatrix e.toBasis, LinearMap.toMatrix_adjoint e e,
          Matrix.det_conjTranspose, star_trivial]
      have hdet : (L.adjoint ∘L L).det = LinearMap.det B ^ 2 := by
        rw [hLLBB, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
          LinearMap.det_comp, ← ContinuousLinearMap.det, hdetadj,
          LinearMap.coe_toContinuousLinearMap, sq]
      have hJ : Real.sqrt ((L.adjoint ∘L L).det) = |LinearMap.det B| := by
        rw [hdet, Real.sqrt_sq_eq_abs]
      have hdetB : LinearMap.det B ≠ 0 :=
        (LinearMap.isUnit_det B ((LinearMap.isUnit_iff_ker_eq_bot B).mpr
          (LinearMap.ker_eq_bot.mpr hBinj))).ne_zero
      refine ⟨by rw [hJ]; exact abs_pos.mpr hdetB, fun A => ?_⟩
      rw [hJ]
      have himg : L '' A = ι '' (B '' A) := by
        rw [image_image]
        exact image_congr fun v _ => hLB v
      rw [himg, ι.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap]
    -- the metric Jacobian `J(w) = √det(Dχ(w)* Dχ(w))`
    set J : Euclid m → ℝ := fun w => Real.sqrt (((fderiv ℝ χ w).adjoint ∘L fderiv ℝ χ w).det)
    have hΦ : Continuous fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt ((L.adjoint ∘L L).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
        (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
    have hJcont : ContinuousOn J U :=
      hΦ.comp_continuousOn (hχ.continuousOn_fderiv_of_isOpen hU le_rfl)
    have hJmeas : Measurable J := hΦ.measurable.comp (measurable_fderiv ℝ χ)
    -- (b) near `w₀`, `χ` is `a`-bi-Lipschitz to `L = Dχ(w₀)` and `J ≈ J(w₀)`
    have hloc : ∀ a : ℝ, 1 < a → ∀ w₀ ∈ U, ∃ r > 0, ∀ B ⊆ ball w₀ r, MeasurableSet B →
        μHE[m] (χ '' B) ≤ ENNReal.ofReal a ^ (m + 1) * ∫⁻ w in B, ENNReal.ofReal (J w) ∧
        ∫⁻ w in B, ENNReal.ofReal (J w) ≤ ENNReal.ofReal a ^ (m + 1) * μHE[m] (χ '' B) := by
      intro a ha w₀ hw₀
      have ha0 : 0 < a := by linarith
      have hainv : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ ha
      have h2a : 2 - a⁻¹ ≤ a := by
        have : a + a⁻¹ - 2 = (a - 1) ^ 2 * a⁻¹ := by field_simp; ring
        nlinarith [sq_nonneg (a - 1), inv_pos.mpr ha0]
      set L := fderiv ℝ χ w₀
      have hLinj : Injective L := hreg w₀ hw₀
      obtain ⟨hJ0, hLA⟩ := hlin L hLinj
      obtain ⟨K, hK0, hK⟩ := LinearMap.exists_antilipschitzWith (L : Euclid m →ₗ[ℝ] Euclid P)
        (LinearMap.ker_eq_bot.mpr hLinj)
      have hK0' : (0 : ℝ) < K := hK0
      obtain ⟨Linv, hLinv⟩ :=
        LinearMap.exists_leftInverse_of_injective (L : Euclid m →ₗ[ℝ] Euclid P)
          (LinearMap.ker_eq_bot.mpr hLinj)
      have hLinv' : ∀ v, Linv (L v) = v := fun v => LinearMap.congr_fun hLinv v
      -- `‖χ u - χ v - L (u - v)‖ ≤ δ ‖u - v‖` near `w₀`, with `δ K = 1 - a⁻¹`
      set δ : ℝ := (1 - a⁻¹) / K with hδdef
      have hδ0 : 0 < δ := div_pos (by linarith) hK0'
      have hδK : δ * K = 1 - a⁻¹ := by rw [hδdef]; field_simp
      obtain ⟨s, hs, happrox⟩ :=
        ((hχ.contDiffAt (hU.mem_nhds hw₀)).hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
          (c := Real.toNNReal δ) (Or.inr (Real.toNNReal_pos.mpr hδ0))
      have hJat : Tendsto J (𝓝 w₀) (𝓝 (J w₀)) := hJcont.continuousAt (hU.mem_nhds hw₀)
      have hJw₀ : J w₀ = Real.sqrt ((L.adjoint ∘L L).det) := rfl
      rw [← hJw₀] at hJ0 hLA
      have hevU : ∀ᶠ w in 𝓝 w₀, w ∈ U := hU.mem_nhds hw₀
      have hevs : ∀ᶠ w in 𝓝 w₀, w ∈ s := hs
      have hev : ∀ᶠ w in 𝓝 w₀, w ∈ U ∧ w ∈ s ∧ J w < a * J w₀ ∧ J w₀ / a < J w :=
        hevU.and (hevs.and ((hJat.eventually (gt_mem_nhds (by nlinarith))).and
          (hJat.eventually (lt_mem_nhds (div_lt_self hJ0 ha)))))
      obtain ⟨r, hr, hrb⟩ := Metric.eventually_nhds_iff_ball.mp hev
      refine ⟨r, hr, fun B hBr hB => ?_⟩
      have hBU : B ⊆ U := fun w hw => (hrb w (hBr hw)).1
      have hBs : B ⊆ s := fun w hw => (hrb w (hBr hw)).2.1
      -- the two basic estimates
      have hest : ∀ u ∈ B, ∀ v ∈ B, ‖χ u - χ v - L (u - v)‖ ≤ (1 - a⁻¹) * ‖L u - L v‖ := by
        intro u hu v hv
        have h1 := happrox u (hBs hu) v (hBs hv)
        rw [Real.coe_toNNReal _ hδ0.le] at h1
        have h2 : ‖u - v‖ ≤ K * ‖L u - L v‖ := by
          simpa [dist_eq_norm] using hK.le_mul_dist u v
        calc ‖χ u - χ v - L (u - v)‖ ≤ δ * ‖u - v‖ := h1
          _ ≤ δ * (K * ‖L u - L v‖) := mul_le_mul_of_nonneg_left h2 hδ0.le
          _ = (1 - a⁻¹) * ‖L u - L v‖ := by rw [← mul_assoc, hδK]
      -- (i) `Hᵐ(χ B) ≤ aᵐ Hᵐ(L B)`
      have hN1 : μHE[m] (χ '' B) ≤ ENNReal.ofReal a ^ m * μHE[m] (L '' B) := by
        have himg : χ '' B = (fun x => χ (Linv x)) '' (L '' B) := by
          rw [image_image]
          simp only [hLinv']
        have hlip : LipschitzOnWith (Real.toNNReal a) (fun x => χ (Linv x)) (L '' B) := by
          apply LipschitzOnWith.of_dist_le_mul
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
          simp only [hLinv']
          rw [Real.coe_toNNReal _ ha0.le, dist_eq_norm, dist_eq_norm]
          have h3 := hest u hu v hv
          have h4 : ‖χ u - χ v‖ ≤ ‖χ u - χ v - L (u - v)‖ + ‖L u - L v‖ := by
            rw [map_sub]
            calc ‖χ u - χ v‖ = ‖(χ u - χ v - (L u - L v)) + (L u - L v)‖ := by rw [sub_add_cancel]
              _ ≤ _ := norm_add_le _ _
          nlinarith [norm_nonneg (L u - L v)]
        have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hlip
        rwa [← himg] at this
      -- (ii) `Hᵐ(L B) ≤ aᵐ Hᵐ(χ B)`
      have hN2 : μHE[m] (L '' B) ≤ ENNReal.ofReal a ^ m * μHE[m] (χ '' B) := by
        have himg : L '' B = (fun x => L (invFunOn χ U x)) '' (χ '' B) := by
          rw [image_image]
          exact image_congr fun u hu => by rw [hinj.leftInvOn_invFunOn (hBU hu)]
        have hlip : LipschitzOnWith (Real.toNNReal a) (fun x => L (invFunOn χ U x)) (χ '' B) := by
          apply LipschitzOnWith.of_dist_le_mul
          rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
          simp only [hinj.leftInvOn_invFunOn (hBU hu), hinj.leftInvOn_invFunOn (hBU hv)]
          rw [Real.coe_toNNReal _ ha0.le, dist_eq_norm, dist_eq_norm]
          have h3 := hest u hu v hv
          have h4 : ‖L u - L v‖ ≤ ‖χ u - χ v - L (u - v)‖ + ‖χ u - χ v‖ := by
            rw [map_sub]
            calc ‖L u - L v‖ = ‖(χ u - χ v) - (χ u - χ v - (L u - L v))‖ := by rw [sub_sub_cancel]
              _ ≤ ‖χ u - χ v‖ + ‖χ u - χ v - (L u - L v)‖ := norm_sub_le _ _
              _ = _ := add_comm _ _
          have h5 : a⁻¹ * ‖L u - L v‖ ≤ ‖χ u - χ v‖ := by nlinarith
          calc ‖L u - L v‖ = a * (a⁻¹ * ‖L u - L v‖) := by field_simp
            _ ≤ a * ‖χ u - χ v‖ := mul_le_mul_of_nonneg_left h5 ha0.le
        have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hlip
        rwa [← himg] at this
      -- (iii) `J ≤ a J(w₀)` and `J(w₀) ≤ a J` on `B`
      have hI1 : ∫⁻ w in B, ENNReal.ofReal (J w) ≤
          ENNReal.ofReal a * (ENNReal.ofReal (J w₀) * volume B) := by
        calc ∫⁻ w in B, ENNReal.ofReal (J w) ≤ ∫⁻ _ in B, ENNReal.ofReal (a * J w₀) :=
              setLIntegral_mono' hB fun w hw =>
                ENNReal.ofReal_le_ofReal (hrb w (hBr hw)).2.2.1.le
          _ = ENNReal.ofReal a * (ENNReal.ofReal (J w₀) * volume B) := by
            rw [setLIntegral_const, ENNReal.ofReal_mul ha0.le, mul_assoc]
      have hI2 : ENNReal.ofReal (J w₀) * volume B ≤
          ENNReal.ofReal a * ∫⁻ w in B, ENNReal.ofReal (J w) := by
        calc ENNReal.ofReal (J w₀) * volume B = ∫⁻ _ in B, ENNReal.ofReal (J w₀) :=
              (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ w in B, ENNReal.ofReal a * ENNReal.ofReal (J w) :=
              setLIntegral_mono' hB fun w hw => by
                rw [← ENNReal.ofReal_mul ha0.le]
                apply ENNReal.ofReal_le_ofReal
                have := (hrb w (hBr hw)).2.2.2
                rw [div_lt_iff₀ ha0] at this
                linarith
          _ = ENNReal.ofReal a * ∫⁻ w in B, ENNReal.ofReal (J w) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      constructor
      · calc μHE[m] (χ '' B) ≤ ENNReal.ofReal a ^ m * μHE[m] (L '' B) := hN1
          _ = ENNReal.ofReal a ^ m * (ENNReal.ofReal (J w₀) * volume B) := by rw [hLA B]
          _ ≤ ENNReal.ofReal a ^ m * (ENNReal.ofReal a * ∫⁻ w in B, ENNReal.ofReal (J w)) :=
              mul_le_mul_right hI2 _
          _ = ENNReal.ofReal a ^ (m + 1) * ∫⁻ w in B, ENNReal.ofReal (J w) := by
              rw [pow_succ, mul_assoc]
      · calc ∫⁻ w in B, ENNReal.ofReal (J w) ≤
              ENNReal.ofReal a * (ENNReal.ofReal (J w₀) * volume B) := hI1
          _ = ENNReal.ofReal a * μHE[m] (L '' B) := by rw [hLA B]
          _ ≤ ENNReal.ofReal a * (ENNReal.ofReal a ^ m * μHE[m] (χ '' B)) :=
              mul_le_mul_right hN2 _
          _ = ENNReal.ofReal a ^ (m + 1) * μHE[m] (χ '' B) := by
              rw [pow_succ', mul_assoc]
    -- (c) a countable disjoint cover of `U` by such balls globalizes (b)
    have hglob : ∀ a : ℝ, 1 < a → ∀ B ⊆ U, MeasurableSet B →
        μHE[m] (χ '' B) ≤ ENNReal.ofReal a ^ (m + 1) * ∫⁻ w in B, ENNReal.ofReal (J w) ∧
        ∫⁻ w in B, ENNReal.ofReal (J w) ≤ ENNReal.ofReal a ^ (m + 1) * μHE[m] (χ '' B) := by
      intro a ha B hBU hB
      choose! r hr hrB using hloc a ha
      obtain ⟨T, hTU, hTc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
        (f := fun w => ball w (r w)) (s := U)
        fun w hw => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds w (hr w hw))
      rcases T.eq_empty_or_nonempty with hT | hT
      · have hB0 : B = ∅ := by
          apply eq_empty_of_subset_empty
          intro x hx
          simpa [hT] using hcov (hBU hx)
        subst hB0
        simp
      obtain ⟨e, rfl⟩ := hTc.exists_eq_range hT
      set W : ℕ → Set (Euclid m) := fun k => ball (e k) (r (e k)) with hW
      set D : ℕ → Set (Euclid m) := fun k => B ∩ disjointed W k with hD
      have hDm : ∀ k, MeasurableSet (D k) := fun k =>
        hB.inter (MeasurableSet.disjointed (fun _ => measurableSet_ball) k)
      have hDd : Pairwise (Disjoint on D) := fun i j hij =>
        (disjoint_disjointed W hij).mono inter_subset_right inter_subset_right
      have hDB : ⋃ k, D k = B := by
        rw [hD, ← inter_iUnion, iUnion_disjointed, inter_eq_left]
        intro x hx
        simpa [hW] using hcov (hBU hx)
      have hDW : ∀ k, D k ⊆ ball (e k) (r (e k)) := fun k =>
        inter_subset_right.trans (disjointed_subset W k)
      have heU : ∀ k, e k ∈ U := fun k => hTU (mem_range_self k)
      have hDU : ∀ k, D k ⊆ U := fun k => inter_subset_left.trans hBU
      have hν : μHE[m] (χ '' B) = ∑' k, μHE[m] (χ '' D k) := by
        conv_lhs => rw [← hDB, image_iUnion]
        refine measure_iUnion (fun i j hij => ?_) fun k =>
          (hDm k).image_of_continuousOn_injOn (hχ.continuousOn.mono (hDU k)) (hinj.mono (hDU k))
        show Disjoint (χ '' D i) (χ '' D j)
        rw [Set.disjoint_left]
        rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
        have := hinj (hDU j hv) (hDU i hu) hvu
        subst this
        exact Set.disjoint_left.mp (hDd hij) hu hv
      have hμ : ∫⁻ w in B, ENNReal.ofReal (J w) = ∑' k, ∫⁻ w in D k, ENNReal.ofReal (J w) := by
        conv_lhs => rw [← hDB]
        exact lintegral_iUnion hDm hDd _
      constructor
      · rw [hν, hμ, ← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum fun k => (hrB (e k) (heU k) (D k) (hDW k) (hDm k)).1
      · rw [hν, hμ, ← ENNReal.tsum_mul_left]
        exact ENNReal.tsum_le_tsum fun k => (hrB (e k) (heU k) (D k) (hDW k) (hDm k)).2
    -- (d) letting `a ↓ 1`: `Hᵐ(χ B) = ∫_B J`
    have hlim : ∀ x y : ℝ≥0∞, (∀ a : ℝ, 1 < a → x ≤ ENNReal.ofReal a ^ (m + 1) * y) → x ≤ y := by
      intro x y hxy
      have h1 : Tendsto (fun a : ℝ => ENNReal.ofReal a ^ (m + 1)) (𝓝[>] 1) (𝓝 1) := by
        have := ((ENNReal.continuous_pow (m + 1)).comp ENNReal.continuous_ofReal).tendsto (1 : ℝ)
        simp only [comp_apply, ENNReal.ofReal_one, one_pow] at this
        exact this.mono_left nhdsWithin_le_nhds
      have h2 := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero) (b := y)
      rw [one_mul] at h2
      exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun a ha => hxy a ha)
    have hset : ∀ B ⊆ U, MeasurableSet B → μHE[m] (χ '' B) = ∫⁻ w in B, ENNReal.ofReal (J w) :=
      fun B hBU hB => le_antisymm (hlim _ _ fun a ha => (hglob a ha B hBU hB).1)
        (hlim _ _ fun a ha => (hglob a ha B hBU hB).2)
    -- (e) the weighted formula: `χ` pushes `J Lᵐ⌞S` forward to `Hᵐ⌞χ(S)`
    intro S hSU hS h
    have hemb : MeasurableEmbedding (S.domRestrict χ) :=
      (hχ.continuousOn.mono hSU).measurableEmbedding hS (hinj.mono hSU)
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hmap : Measure.map (S.domRestrict χ)
        ((volume.withDensity fun w => ENNReal.ofReal (J w)).comap (Subtype.val : S → Euclid m)) =
          μHE[m].restrict (χ '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hB : MeasurableSet (Subtype.val '' ((S.domRestrict χ) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict χ) ⁻¹' t) ⊆ S := by
        rintro _ ⟨u, -, rfl⟩
        exact u.2
      rw [withDensity_apply _ hB, ← hset _ (hBS.trans hSU) hB, Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
        exact ⟨hu, u, u.2, rfl⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.lintegral_map]
    change ∫⁻ x : S, (fun w => h (χ w)) x ∂((volume.withDensity
      fun w => ENNReal.ofReal (J w)).comap (Subtype.val : S → Euclid m)) = _
    rw [lintegral_subtype_comap (μ := volume.withDensity fun w => ENNReal.ofReal (J w)) hS
        (fun w => h (χ w)),
      setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _
        hJmeas.ennreal_ofReal.aemeasurable _ hS
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    rfl
  -- the coordinates `c(s, w) = (s, w₀, …, w_{n-1})` of `ℝ^{n+1} = ℝ × ℝⁿ`
  let c : ℝ → Euclid n → Euclid (n + 1) := fun s w => WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))
  have hc : ∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i := fun s w => ⟨rfl, fun i => rfl⟩
  have hccont : ∀ s, Continuous (c s) := fun s =>
    (PiLp.continuous_toLp 2 _).comp (continuous_const.finCons (PiLp.continuous_ofLp 2 _))
  -- Step 1: the Borel tangential gradient `Ĝ`, with `G ∘ ψ = Ĝ` on `Y'`
  have hY'V : Y' ⊆ V := hY'Θ.trans hΘV
  obtain ⟨Gh, hGhm, -, hGh⟩ :=
    Submission.dtc_bc_lc_sl_cc_chart_gradient P (n + 1) ψ V F hV hψ hDψ hF
  have hGG : ∀ y ∈ Y', G (ψ y) = Gh y := fun y hy =>
    (hGh y (hY'V hy)).2.2.1 (G (ψ y)) (hG y hy).1 (hG y hy).2
  -- Step 2: the Borel density `f = J_ψ · |Ĝ| · g ∘ ψ`
  have hΦ : Continuous fun L : Euclid (n + 1) →L[ℝ] Euclid P => Real.sqrt ((L.adjoint ∘L L).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  set f : Euclid (n + 1) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.sqrt (((fderiv ℝ ψ y).adjoint ∘L fderiv ℝ ψ y).det)) *
      (ENNReal.ofReal ‖Gh y‖ * g (ψ y)) with hfdef
  have hfm : Measurable f :=
    (hΦ.measurable.comp (measurable_fderiv ℝ ψ)).ennreal_ofReal.mul
      (hGhm.norm.ennreal_ofReal.mul (hg.comp hψ.continuous.measurable))
  -- Step 3: Fubini in the straightened coordinates
  obtain ⟨hIm, hIeq⟩ :=
    Submission.dtc_bc_lc_sl_cc_flat_fubini n c Ω Y' Θ f hc hΩ hΘ hΘinj hfm hY' hY'Θ
  have hSm : MeasurableSet (Ω ∩ Θ ⁻¹' Y') := by
    classical
    have hpw : Measurable (Ω.piecewise Θ fun _ => 0) :=
      hΘ.continuousOn.measurable_piecewise continuousOn_const hΩ.measurableSet
    have hS : Ω ∩ Θ ⁻¹' Y' = Ω ∩ (Ω.piecewise Θ fun _ => 0) ⁻¹' Y' := by
      ext z
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hz, hzY⟩
        exact ⟨hz, by rwa [piecewise_eq_of_mem _ _ _ hz]⟩
      · rintro ⟨hz, hzY⟩
        exact ⟨hz, by rwa [piecewise_eq_of_mem _ _ _ hz] at hzY⟩
    rw [hS]
    exact hΩ.measurableSet.inter (hpw hY')
  -- Steps 4–7: on each level, the slice integral is the Fubini integrand `I(t)`
  have hkey : ∀ t : ℝ, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] =
      ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator
        (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w) := by
    intro t
    obtain ⟨hΩt, hχ1, hχinj, hχ⟩ := Submission.dtc_bc_lc_sl_cc_slice_param P n c ψ V Ω F Θ t hc
      hψ hψinj hDψ hF hΩ hΘ hΘinj hDΘ hΘV hFΘ
    have hStm : MeasurableSet (c t ⁻¹' (Ω ∩ Θ ⁻¹' Y')) := (hccont t).measurable hSm
    have hStU : c t ⁻¹' (Ω ∩ Θ ⁻¹' Y') ⊆ {w | c t w ∈ Ω} := fun w hw => hw.1
    -- Step 5: `ψ(Y' ∩ F⁻¹(t)) = χ(Sᵗ)`
    have himg : ψ '' (Y' ∩ F ⁻¹' {t}) =
        (fun w => ψ (Θ (c t w))) '' (c t ⁻¹' (Ω ∩ Θ ⁻¹' Y')) := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyY, hyF⟩, rfl⟩
        obtain ⟨z, hzΩ, rfl⟩ := hY'Θ hyY
        have hz0 : z 0 = t := by
          rw [← hFΘ z hzΩ]
          exact hyF
        have hcz : c t (WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))) = z := by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · rw [(hc _ _).1, hz0]
          · rw [(hc _ _).2 j]
            rfl
        refine ⟨WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)), ?_, ?_⟩
        · show c t _ ∈ Ω ∩ Θ ⁻¹' Y'
          rw [hcz]
          exact ⟨hzΩ, hyY⟩
        · show ψ (Θ (c t _)) = ψ (Θ z)
          rw [hcz]
      · rintro ⟨w, ⟨hwΩ, hwY⟩, rfl⟩
        refine ⟨Θ (c t w), ⟨hwY, ?_⟩, rfl⟩
        show F (Θ (c t w)) = t
        rw [hFΘ _ hwΩ]
        exact (hc t w).1
    -- Step 6: the area formula for `χ = ψ ∘ Θ ∘ c(t, ·)` on `Sᵗ`
    rw [himg, harea n (fun w => ψ (Θ (c t w))) {w | c t w ∈ Ω} hΩt hχ1 hχinj
      (fun w hw => (hχ w hw).2.1) _ hStU hStm g, ← lintegral_indicator hStm]
    -- Step 7: the integrands agree, by the Jacobian identity of `slice_param`
    refine lintegral_congr fun w => ?_
    by_cases hw : w ∈ c t ⁻¹' (Ω ∩ Θ ⁻¹' Y')
    · rw [indicator_of_mem hw, indicator_of_mem (show c t w ∈ Ω ∩ Θ ⁻¹' Y' from hw)]
      obtain ⟨hwΩ, -⟩ := hw
      have hGy := hGh _ (hΘV ⟨c t w, hwΩ, rfl⟩)
      have hJac := ((hχ w hwΩ).2.2 (Gh (Θ (c t w))) hGy.1 hGy.2.1).2
      simp only [hfdef]
      rw [hJac, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _)]
      ring
    · rw [indicator_of_notMem hw, indicator_of_notMem (show c t w ∉ Ω ∩ Θ ⁻¹' Y' from hw)]
  -- Steps 8–9: measurability, and the area formula for `ψ` on `Y'`
  have hfun : (fun t => ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n]) = fun t =>
      ∫⁻ w, (Ω ∩ Θ ⁻¹' Y').indicator
        (fun z => ENNReal.ofReal |(fderiv ℝ Θ z).det| * f (Θ z)) (c t w) := funext hkey
  refine ⟨by rw [hfun]; exact hIm, ?_⟩
  rw [hfun, hIeq, harea (n + 1) ψ V hV hψ.contDiffOn hψinj hDψ Y' hY'V hY' _]
  refine setLIntegral_congr_fun hY' fun y hy => ?_
  simp only [hfdef, hGG y hy]

/-- Co-area formula on the regular part of an embedded `C¹` chart (Simon Ch. 2, 6.3 and 6.6, for
`F ∘ ψ⁻¹` on `ψ(V)`, where `DF ≠ 0`).  Let `ψ` be `C¹`, injective on the open `V ⊆ ℝ^{n+1}` with
injective derivative, `F` be `C¹`, `Y' ⊆ V` be Borel with `DF ≠ 0` on `Y'`, and on `Y'` let
`G(ψ(y)) ∈ Dψ(y)(ℝ^{n+1})` with `⟨G(ψ(y)), Dψ(y)e⟩ = DF(y)e`.  Then for Borel `g ≥ 0`,
`t ↦ ∫_{ψ(Y' ∩ F⁻¹(t))} g dHⁿ` is Borel and
`∫_ℝ ∫_{ψ(Y' ∩ F⁻¹(t))} g dHⁿ dt = ∫_{ψ(Y')} |G| g dHⁿ⁺¹`.

Proof sketch:
* Flattening charts `Wₖ = Θₖ(Ωₖ)` (open, `⊆ V`, `F(Θₖ(z)) = z₀`) cover `{y ∈ V : DF(y) ≠ 0}`,
  hence `Y'`.
* `Yₖ = disjointed (Y' ∩ Wₖ)` are Borel, pairwise disjoint, `Yₖ ⊆ Wₖ`, and `⋃ₖ Yₖ = Y'`.
* The one-chart formula holds on each `Yₖ`.
* `ψ` is continuous and injective on `V ⊇ Y'`, so it maps Borel subsets of the `Yₖ` to pairwise
  disjoint Borel sets (Lusin–Souslin).  Hence the slice integral over `ψ(Y' ∩ F⁻¹(t))` is the sum
  of those over `ψ(Yₖ ∩ F⁻¹(t))`, a Borel function of `t`.
* Integrate the sum termwise (`lintegral_tsum`) and reassemble the disjoint union
  `ψ(Y') = ⋃ₖ ψ(Yₖ)` (`lintegral_iUnion`). -/
theorem Submission.dtc_bc_lc_sl_cc_regular_coarea : ∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y' : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y' → Y' ⊆ V → (∀ y ∈ Y', fderiv ℝ F y ≠ 0) → (∀ y ∈ Y', G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ g : Euclid P → ℝ≥0∞, Measurable g → Measurable (fun t => ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y', ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] := by
  intro P n ψ V Y' F G hV hψ hψV hDψ hF hY' hY'V hDF hG g hg
  -- flattening charts `Wₖ = Θₖ(Ωₖ)` covering `{y ∈ V : DF(y) ≠ 0} ⊇ Y'`
  obtain ⟨Ω, Θ, hΘ, hcover⟩ := Submission.dtc_bc_lc_sl_cc_flattening_atlas n F V hV hF
  have hY'W : Y' ⊆ ⋃ k, Θ k '' Ω k := fun y hy => hcover ⟨hY'V hy, hDF y hy⟩
  -- disjoint Borel pieces `Yₖ = disjointed (Y' ∩ Wₖ)` with union `Y'`
  obtain ⟨Y, hYm, hYsub, hYdisj, hYunion⟩ : ∃ Y : ℕ → Set (Euclid (n + 1)),
      (∀ k, MeasurableSet (Y k)) ∧ (∀ k, Y k ⊆ Y' ∩ Θ k '' Ω k) ∧ Pairwise (Disjoint on Y) ∧
        ⋃ k, Y k = Y' :=
    ⟨disjointed fun k => Y' ∩ Θ k '' Ω k,
      MeasurableSet.disjointed fun k => hY'.inter (hΘ k).2.2.2.2.1.measurableSet,
      disjointed_subset _, disjoint_disjointed _,
      by rw [iUnion_disjointed, ← inter_iUnion, inter_eq_left.mpr hY'W]⟩
  have hYY' : ∀ k, Y k ⊆ Y' := fun k => hYunion ▸ subset_iUnion Y k
  -- the one-chart formula on each piece
  have hpiece : ∀ k, Measurable (fun t => ∫⁻ x in ψ '' (Y k ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧
      ∫⁻ t, ∫⁻ x in ψ '' (Y k ∩ F ⁻¹' {t}), g x ∂μHE[n] =
        ∫⁻ x in ψ '' Y k, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] := by
    intro k
    obtain ⟨hΩ, hΘc, hΘi, hDΘ, -, hWV, hFΘ⟩ := hΘ k
    exact Submission.dtc_bc_lc_sl_cc_piece_coarea P n ψ V (Ω k) (Y k) F (Θ k) G
      hV hψ hψV hDψ hF hΩ hΘc hΘi hDΘ hWV hFΘ (hYm k) (fun y hy => (hYsub k hy).2)
      (fun y hy => hG y (hYsub k hy).1) g hg
  -- `ψ` maps Borel subsets of `Y'` to Borel sets (Lusin–Souslin) ...
  have himg : ∀ A ⊆ Y', MeasurableSet A → MeasurableSet (ψ '' A) := fun A hA hAm =>
    hAm.image_of_continuousOn_injOn hψ.continuous.continuousOn (hψV.mono (hA.trans hY'V))
  -- ... and subsets of the disjoint pieces to disjoint sets
  have hdisj : ∀ A : ℕ → Set (Euclid (n + 1)), (∀ k, A k ⊆ Y k) →
      Pairwise (Disjoint on fun k => ψ '' A k) := by
    intro A hA i j hij
    refine disjoint_image_image fun a ha b hb hab => ?_
    obtain rfl := hψV (hY'V (hYY' i (hA i ha))) (hY'V (hYY' j (hA j hb))) hab
    exact disjoint_left.1 (hYdisj hij) (hA i ha) (hA j hb)
  -- the slice integral over `ψ(Y' ∩ F⁻¹(t))` is the sum of the piece slice integrals
  have hslice : ∀ t, ∫⁻ x in ψ '' (Y' ∩ F ⁻¹' {t}), g x ∂μHE[n] =
      ∑' k, ∫⁻ x in ψ '' (Y k ∩ F ⁻¹' {t}), g x ∂μHE[n] := by
    intro t
    have hFt : MeasurableSet (F ⁻¹' {t}) :=
      (isClosed_singleton.preimage hF.continuous).measurableSet
    rw [← hYunion, iUnion_inter, image_iUnion]
    exact lintegral_iUnion
      (fun k => himg _ (inter_subset_left.trans (hYY' k)) ((hYm k).inter hFt))
      (hdisj _ fun k => inter_subset_left) g
  refine ⟨?_, ?_⟩
  · simp only [hslice]
    exact Measurable.tsum fun k => (hpiece k).1
  · simp only [hslice]
    rw [lintegral_tsum fun k => (hpiece k).1.aemeasurable, tsum_congr fun k => (hpiece k).2,
      ← lintegral_iUnion (fun k => himg _ (hYY' k) (hYm k)) (hdisj Y fun k => subset_rfl),
      ← image_iUnion, hYunion]
/-- Countably many slice disks (Simon Ch. 2, 6.4, in local parametrised form).  Let `ψ` be `C¹`,
injective with injective derivative on the open `V ⊆ ℝ^{n+1}`, and `F` be `C¹`.  Then the image
`ψ({y ∈ V : F(y) = t, DF(y) ≠ 0})` is covered by the balls `χ_j(B_{r_j}(a_j))` of countably many
injective `C¹` disks `χ_j : U_j → ℝᴾ` with injective derivative, countably `n`-rectifiable images,
`Hⁿ(χ_j(B̄_{r_j}(a_j))) < ∞`, and `Dχ_j(w)(ℝⁿ) = Dψ(y)(ℝ^{n+1}) ∩ (ℝv)^⊥` at a point `y` of the
level set with `ψ(y) = χ_j(w)`, `v` the gradient of `F` along `ψ`.

Proof sketch:
* `flattening_atlas` gives charts `Θ_k : Ω_k → V` with `F(Θ_k(z)) = z₀` covering `{DF ≠ 0}`;
  `slice_param` makes `χ^k = ψ ∘ Θ_k ∘ c(t, ·)`, `c(t, w) = (t, w)`, an injective `C¹` disk on the
  open `U^k = {w : c(t, w) ∈ Ω_k}`, with `DF ≠ 0`, injective derivative and the range identity.
* Index `j = ⟨k, ⟨m, l⟩⟩`: `U_j = U^k`, `χ_j = χ^k`, `a_j = d_m` for a dense sequence `d`, and
  `r_j = 1/(l+1)` if `B̄_{1/(l+1)}(d_m) ⊆ U^k`, `r_j = -1` (empty balls) otherwise.
* `χ^k` is Lipschitz on the convex compact `B̄_{r_j}(a_j) ⊆ U^k`, so `Hⁿ(χ_j(B̄_{r_j}(a_j))) < ∞`.
* Every `w ∈ U^k` lies in some `B_{r_j}(a_j)` with `j = ⟨k, ⟨m, l⟩⟩`; hence `χ^k(U^k)` is covered by
  the ranges of Lipschitz extensions of the `χ_j` from these balls (countably rectifiable), and
  `ψ(Θ_k(z)) = χ_j(w)` for `z = c(t, w) ∈ Ω_k` with `z₀ = t`. -/
theorem Submission.dtc_bc_lc_sl_cc_slice_disks : ∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (t : ℝ), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ (U : ℕ → Set (Euclid n)) (a : ℕ → Euclid n) (r : ℕ → ℝ) (χ : ℕ → Euclid n → Euclid P), (∀ j, IsOpen (U j) ∧ closedBall (a j) (r j) ⊆ U j ∧ ContDiffOn ℝ 1 (χ j) (U j) ∧ InjOn (χ j) (U j) ∧ CountablyRectifiable n (χ j '' U j) ∧ μHE[n] (χ j '' closedBall (a j) (r j)) ≠ ∞ ∧ ∀ w ∈ U j, Injective (fderiv ℝ (χ j) w) ∧ ∃ y ∈ V, ψ y = χ j w ∧ F y = t ∧ fderiv ℝ F y ≠ 0 ∧ ∀ v ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P), (∀ e, inner ℝ v (fderiv ℝ ψ y e) = fderiv ℝ F y e) → LinearMap.range (fderiv ℝ (χ j) w : Euclid n →ₗ[ℝ] Euclid P) = LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ v)ᗮ) ∧ ψ '' {y | y ∈ V ∧ F y = t ∧ fderiv ℝ F y ≠ 0} ⊆ ⋃ j, χ j '' ball (a j) (r j) := by
  intro P n ψ V F t hV hψ hψinj hDψ hF
  classical
  -- Step 1: charts `Θ_k : Ω_k → V` flattening `F`, and the slices `χ^k = ψ ∘ Θ_k ∘ c(t, ·)`
  obtain ⟨Ω, Θ, hΩ, hcover⟩ := Submission.dtc_bc_lc_sl_cc_flattening_atlas n F V hV hF
  let c : ℝ → Euclid n → Euclid (n + 1) := fun s w =>
    WithLp.toLp 2 (Fin.cons s fun i => w i : Fin (n + 1) → ℝ)
  have hc : ∀ s w, c s w 0 = s ∧ ∀ i : Fin n, c s w i.succ = w i := fun s w => by
    simp [c]
  have hsl := fun k => Submission.dtc_bc_lc_sl_cc_slice_param P n c ψ V (Ω k) F (Θ k) t hc hψ
    hψinj hDψ hF (hΩ k).1 (hΩ k).2.1 (hΩ k).2.2.1 (hΩ k).2.2.2.1 (hΩ k).2.2.2.2.2.1
    (hΩ k).2.2.2.2.2.2
  let U : ℕ → Set (Euclid n) := fun k => {w | c t w ∈ Ω k}
  let χ : ℕ → Euclid n → Euclid P := fun k w => ψ (Θ k (c t w))
  -- Step 2: `j = ⟨k, ⟨m, l⟩⟩`, `a_j = d_m` and `r_j = 1/(l+1)` if `B̄_{1/(l+1)}(d_m) ⊆ U^k`
  let d := TopologicalSpace.denseSeq (Euclid n)
  let ρ : ℕ → ℝ := fun l => 1 / ((l : ℝ) + 1)
  let a : ℕ → Euclid n := fun j => d (Nat.unpair (Nat.unpair j).2).1
  let r : ℕ → ℝ := fun j =>
    if closedBall (a j) (ρ (Nat.unpair (Nat.unpair j).2).2) ⊆ U (Nat.unpair j).1 then
      ρ (Nat.unpair (Nat.unpair j).2).2 else -1
  have hball : ∀ j, closedBall (a j) (r j) ⊆ U (Nat.unpair j).1 := by
    intro j
    simp only [r]
    split_ifs with h
    · exact h
    · rw [closedBall_eq_empty.2 (by norm_num)]
      exact empty_subset _
  -- every `w ∈ U^k` lies in a ball `B_{r_j}(a_j)` with `j = ⟨k, ⟨m, l⟩⟩`
  have hcov : ∀ k, ∀ w ∈ U k, ∃ j, (Nat.unpair j).1 = k ∧ w ∈ ball (a j) (r j) := by
    intro k w hw
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 (hsl k).1 w hw
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt (half_pos hε)
    have hl' : ρ l < ε / 2 := hl
    have hρ : 0 < ρ l := Nat.one_div_pos_of_nat
    obtain ⟨m, hm⟩ := (TopologicalSpace.denseRange_denseSeq (Euclid n)).exists_dist_lt w hρ
    have hsub : closedBall (d m) (ρ l) ⊆ U k := by
      intro u hu
      apply hεU
      rw [mem_closedBall] at hu
      rw [mem_ball]
      calc dist u w ≤ dist u (d m) + dist (d m) w := dist_triangle _ _ _
        _ < ε := by rw [dist_comm] at hm; linarith
    have ha : a (Nat.pair k (Nat.pair m l)) = d m := by simp only [a, Nat.unpair_pair]
    have hr : r (Nat.pair k (Nat.pair m l)) = ρ l := by
      simp only [r, ha, Nat.unpair_pair]
      exact ite_eq_left hsub
    refine ⟨Nat.pair k (Nat.pair m l), by simp only [Nat.unpair_pair], ?_⟩
    rw [ha, hr, mem_ball]
    exact hm
  -- Step 3: `χ^k` is Lipschitz on each `B̄_{r_j}(a_j) ⊆ U^k`; Lipschitz extensions `g_j`
  have hlip : ∀ j, ∃ K, LipschitzOnWith K (χ (Nat.unpair j).1) (closedBall (a j) (r j)) :=
    fun j => ((hsl _).2.1.mono (hball j)).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose K hK using hlip
  choose g hg hgeq using fun j => (hK j).extend_finite_dimension
  have hR : CountablyRectifiable n (⋃ j, range (g j)) :=
    Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion _ fun j =>
      Poincare.SimonGMT.Chapter03.countablyRectifiable_range (hg j)
  refine ⟨fun j => U (Nat.unpair j).1, a, r, fun j => χ (Nat.unpair j).1, fun j =>
    ⟨(hsl _).1, hball j, (hsl _).2.1, (hsl _).2.2.1, ?_, ?_, ?_⟩, ?_⟩
  · -- `χ^k(U^k) ⊆ ⋃_i g_i(ℝⁿ)` by the ball cover of `U^k`
    refine hR.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨i, hik, hwi⟩ := hcov _ w hw
    refine mem_iUnion.2 ⟨i, w, ?_⟩
    rw [← hgeq i (ball_subset_closedBall hwi), hik]
  · -- `Hⁿ(χ_j(B̄_{r_j}(a_j))) ≤ Kⁿ Lⁿ(B̄_{r_j}(a_j)) < ∞`
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n (hK j))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_closedBall_lt_top.ne
  · -- the level-set point `y = Θ_k(c(t, w))`
    intro w hw
    have hw' : c t w ∈ Ω (Nat.unpair j).1 := hw
    obtain ⟨hDF, hinj, hrange⟩ := (hsl (Nat.unpair j).1).2.2.2 w hw'
    refine ⟨hinj, Θ (Nat.unpair j).1 (c t w), (hΩ _).2.2.2.2.2.1 ⟨c t w, hw', rfl⟩, rfl, ?_, hDF,
      fun v hv he => (hrange v hv he).1⟩
    rw [(hΩ _).2.2.2.2.2.2 _ hw']
    exact (hc t w).1
  · -- Step 4: `y = Θ_k(z)` with `z = c(t, w)`, `w ∈ U^k`, so `ψ(y) = χ_j(w)` for some `j`
    rintro _ ⟨y, ⟨hyV, hFy, hDF⟩, rfl⟩
    obtain ⟨k, z, hz, rfl⟩ : ∃ k, ∃ z ∈ Ω k, Θ k z = y := by
      simpa only [mem_iUnion, mem_image] using hcover ⟨hyV, hDF⟩
    have hz0 : z 0 = t := by
      rw [← (hΩ k).2.2.2.2.2.2 z hz]
      exact hFy
    let w : Euclid n := WithLp.toLp 2 fun i => z i.succ
    have hcw : c t w = z := by
      ext i
      induction i using Fin.cases with
      | zero => simp [c, hz0]
      | succ i => simp [c, w]
    obtain ⟨j, hjk, hwj⟩ := hcov k w (show c t w ∈ Ω k by rw [hcw]; exact hz)
    refine mem_iUnion.2 ⟨j, w, hwj, ?_⟩
    show ψ (Θ (Nat.unpair j).1 (c t w)) = ψ (Θ k z)
    rw [hjk, hcw]

/-- **Co-area formula on a `C¹` chart** (Simon Ch. 2, 6.3, 6.4 and 6.6, in the parametrised form).
Let `ψ : ℝ^{n+1} → ℝᴾ` be `C¹`, injective with injective derivative on the open `V`, `F` `C¹`, and
`Y` Borel with `closure Y` a compact subset of `V`.  Let `G ∘ ψ` represent `DF` along `ψ` on `Y`.
Then (i) for Borel `g ≥ 0`, `t ↦ ∫_{ψ(Y ∩ F⁻¹t)} g dHⁿ` is a.e.-measurable with
`∫_ℝ ∫_{ψ(Y ∩ F⁻¹t)} g dHⁿ dt = ∫_{ψ(Y)} |G| g dH^{n+1}`, and (ii) for a.e. `t` the slice
`S_t = ψ(Y ∩ F⁻¹t)` is countably `n`-rectifiable, and `Hⁿ`-a.e. on `S_t`, `G ≠ 0` and
`T_x S_t = Dψ(y)(ℝ^{n+1}) ∩ G(x)^⊥` for `ψ(y) = x`.

Proof sketch:
* Split `Y = Y_r ⊔ Y_c` by `DF ≠ 0` and `DF = 0`; `G ∘ ψ = 0` on `Y_c`, `G ∘ ψ ≠ 0` on `Y_r`.
* `ψ` is Lipschitz on `closure Y`, so Eilenberg's inequality (via `critical_null`) gives
  `Hⁿ(ψ(Y_c ∩ F⁻¹t)) = 0` for a.e. `t`.
* (i): `regular_coarea` on `Y_r`; the slices of `Y` and `Y_r` agree up to the null critical slice,
  and `∫_{ψ(Y_c)} |G| g = 0`.
* `|G| ≤ Γ` on `ψ(Y)` (`chart_gradient`, continuity on the compact `closure Y`) and
  `H^{n+1}(ψ(Y)) < ∞`, so (i) with `g = 1` gives `Hⁿ(S_t) < ∞` for a.e. `t`.
* For such `t`, `slice_disks` covers the regular part of `S_t` by `C¹` disks `χⱼ(Bⱼ)`: this gives
  rectifiability, and `c1_tangent` with tangent locality (`cmc_imRep_locality_restrict_sub` (a))
  on `S_t ∩ χⱼ(Bⱼ)` gives the tangent planes. -/
theorem Submission.dtc_bc_lc_sl_chart_coarea : ∀ (P n : ℕ) (ψ : Euclid (n + 1) → Euclid P) (V Y : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiff ℝ 1 ψ → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → MeasurableSet Y → IsCompact (closure Y) → closure Y ⊆ V → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e, inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → (∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧ ∫⁻ t, ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n] = ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1]) ∧ ∀ᵐ t, CountablyRectifiable n (ψ '' (Y ∩ F ⁻¹' {t})) ∧ ∀ᵐ x ∂(μHE[n].restrict (ψ '' (Y ∩ F ⁻¹' {t}))), G x ≠ 0 ∧ ∀ y ∈ Y, ψ y = x → HasApproximateTangentSpaceAt n (ψ '' (Y ∩ F ⁻¹' {t})) x (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ G x)ᗮ) := by
  intro P n ψ V Y F G hV hψ hψV hDψ hF hY hYcpt hYV hG
  have hYsV : Y ⊆ V := subset_closure.trans hYV
  -- `ψ` maps Borel subsets of `V` onto Borel sets (Lusin–Souslin)
  have himg : ∀ s ⊆ V, MeasurableSet s → MeasurableSet (ψ '' s) := fun s hsV hs =>
    hs.image_of_continuousOn_injOn hψ.continuous.continuousOn (hψV.mono hsV)
  -- `G ∘ ψ` represents `DF` along `ψ` on `Y`, so it vanishes exactly at the critical points
  have hG0 : ∀ y ∈ Y, fderiv ℝ F y = 0 → G (ψ y) = 0 := by
    intro y hy hy0
    obtain ⟨w, hw⟩ := (hG y hy).1
    have h1 := (hG y hy).2 w
    rw [ContinuousLinearMap.coe_coe] at hw
    rw [hy0, zero_apply, hw] at h1
    exact inner_self_eq_zero.1 h1
  have hGne : ∀ y ∈ Y, fderiv ℝ F y ≠ 0 → G (ψ y) ≠ 0 := by
    intro y hy hy0 h0
    refine hy0 (ContinuousLinearMap.ext fun e => ?_)
    rw [zero_apply, ← (hG y hy).2 e, h0, inner_zero_left]
  -- the regular part `Y_r` and the critical part `Y_c` of `Y`
  have hZ : MeasurableSet {y : Euclid (n + 1) | fderiv ℝ F y = 0} :=
    (isClosed_eq (hF.continuous_fderiv one_ne_zero) continuous_const).measurableSet
  set Yr : Set (Euclid (n + 1)) := Y ∩ {y | fderiv ℝ F y ≠ 0}
  set Yc : Set (Euclid (n + 1)) := Y ∩ {y | fderiv ℝ F y = 0}
  have hYrm : MeasurableSet Yr := hY.inter hZ.compl
  have hYcm : MeasurableSet Yc := hY.inter hZ
  have hYrV : Yr ⊆ V := inter_subset_left.trans hYsV
  have hYcV : Yc ⊆ V := inter_subset_left.trans hYsV
  have hYrc : Yr ∪ Yc = Y := by
    ext y
    constructor
    · rintro (⟨hy, -⟩ | ⟨hy, -⟩) <;> exact hy
    · intro hy
      by_cases hy0 : fderiv ℝ F y = 0
      exacts [Or.inr ⟨hy, hy0⟩, Or.inl ⟨hy, hy0⟩]
  -- `ψ` is Lipschitz on `closure Y`
  obtain ⟨R, hR⟩ := hYcpt.isBounded.subset_closedBall (0 : Euclid (n + 1))
  obtain ⟨K, hK⟩ := (hψ.contDiffOn (s := closedBall (0 : Euclid (n + 1)) R)).exists_lipschitzOnWith
    one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hKY : LipschitzOnWith K ψ (closure Y) := hK.mono hR
  -- Step 1 (Sard-type 6.4): the critical slices are `Hⁿ`-null for a.e. `t`
  obtain ⟨C, hC⟩ := Submission.dtc_bc_lc_sl_eilenberg n
  have hcrit : ∀ᵐ t, μHE[n] (ψ '' (Yc ∩ F ⁻¹' {t})) = 0 := by
    filter_upwards [Submission.dtc_bc_lc_sl_cc_critical_null n C
      (fun A f L hL => hC (n + 1) A f L hL) F Yc hF fun y hy => hy.2] with t ht
    refine le_antisymm ?_ zero_le
    calc μHE[n] (ψ '' (Yc ∩ F ⁻¹' {t})) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (Yc ∩ F ⁻¹' {t}) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            (hKY.mono fun y hy => subset_closure hy.1.1)
      _ = 0 := by rw [ht, mul_zero]
  -- Step 4: the slices of `Y` and of `Y_r` agree up to the null critical slice
  have hslice : ∀ t, ψ '' (Y ∩ F ⁻¹' {t}) = ψ '' (Yr ∩ F ⁻¹' {t}) ∪ ψ '' (Yc ∩ F ⁻¹' {t}) := by
    intro t
    rw [← image_union, ← union_inter_distrib_right, hYrc]
  have hslice_ae : ∀ g : Euclid P → ℝ≥0∞,
      (fun t => ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n]) =ᵐ[volume]
        fun t => ∫⁻ x in ψ '' (Yr ∩ F ⁻¹' {t}), g x ∂μHE[n] := by
    intro g
    filter_upwards [hcrit] with t ht
    rw [hslice t]
    refine le_antisymm ?_ (lintegral_mono_set subset_union_left)
    calc ∫⁻ x in ψ '' (Yr ∩ F ⁻¹' {t}) ∪ ψ '' (Yc ∩ F ⁻¹' {t}), g x ∂μHE[n]
        ≤ ∫⁻ x in ψ '' (Yr ∩ F ⁻¹' {t}), g x ∂μHE[n] +
            ∫⁻ x in ψ '' (Yc ∩ F ⁻¹' {t}), g x ∂μHE[n] := lintegral_union_le _ _ _
      _ = ∫⁻ x in ψ '' (Yr ∩ F ⁻¹' {t}), g x ∂μHE[n] := by
          rw [setLIntegral_measure_zero _ _ ht, add_zero]
  -- `G = 0` on `ψ(Y_c)`, so only `ψ(Y_r)` contributes to the right side
  have hrhs : ∀ g : Euclid P → ℝ≥0∞,
      ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] =
        ∫⁻ x in ψ '' Yr, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] := by
    intro g
    have hzero : ∫⁻ x in ψ '' Yc, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] = 0 := by
      rw [setLIntegral_congr_fun (himg Yc hYcV hYcm)
        (show EqOn (fun x => ENNReal.ofReal ‖G x‖ * g x) (fun _ => 0) (ψ '' Yc) from ?_),
        lintegral_zero]
      rintro x ⟨y, hy, rfl⟩
      simp [hG0 y hy.1 hy.2]
    conv_lhs => rw [← hYrc, image_union]
    refine le_antisymm ?_ (lintegral_mono_set subset_union_left)
    calc _ ≤ _ := lintegral_union_le _ _ _
      _ = _ := by rw [hzero, add_zero]
  -- (i): `regular_coarea` on `Y_r`
  have hi : ∀ g : Euclid P → ℝ≥0∞, Measurable g →
      AEMeasurable (fun t => ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n]) ∧
        ∫⁻ t, ∫⁻ x in ψ '' (Y ∩ F ⁻¹' {t}), g x ∂μHE[n] =
          ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ * g x ∂μHE[n + 1] := by
    intro g hg
    obtain ⟨hmeas, hint⟩ := Submission.dtc_bc_lc_sl_cc_regular_coarea P n ψ V Yr F G hV hψ hψV hDψ
      hF hYrm hYrV (fun y hy => hy.2) (fun y hy => hG y hy.1) g hg
    exact ⟨hmeas.aemeasurable.congr (hslice_ae g).symm, by
      rw [lintegral_congr_ae (hslice_ae g), hint, hrhs g]⟩
  refine ⟨hi, ?_⟩
  -- Step 5: `|G| ≤ Γ` on `ψ(Y)` and `H^{n+1}(ψ(Y)) < ∞`, so a.e. slice has finite `Hⁿ`-measure
  obtain ⟨Gh, -, hGhc, hGh⟩ :=
    Submission.dtc_bc_lc_sl_cc_chart_gradient P (n + 1) ψ V F hV hψ hDψ hF
  obtain ⟨Γ, hΓ⟩ := hYcpt.exists_bound_of_continuousOn (hGhc.mono hYV)
  have hGΓ : ∀ x ∈ ψ '' Y, ENNReal.ofReal ‖G x‖ ≤ ENNReal.ofReal Γ := by
    rintro x ⟨y, hy, rfl⟩
    rw [(hGh y (hYsV hy)).2.2.1 (G (ψ y)) (hG y hy).1 (hG y hy).2]
    exact ENNReal.ofReal_le_ofReal (hΓ y (subset_closure hy))
  have hψY : μHE[n + 1] (ψ '' Y) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (n + 1)
        (hKY.mono subset_closure))
    refine ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ?_
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ne_top_of_le_ne_top hYcpt.measure_lt_top.ne (measure_mono subset_closure)
  have hfin : ∀ᵐ t, μHE[n] (ψ '' (Y ∩ F ⁻¹' {t})) < ∞ := by
    obtain ⟨h1m, h1⟩ := hi (fun _ => 1) measurable_const
    simp only [setLIntegral_one, mul_one] at h1m h1
    have hle : ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ ∂μHE[n + 1] ≤
        ENNReal.ofReal Γ * μHE[n + 1] (ψ '' Y) :=
      calc ∫⁻ x in ψ '' Y, ENNReal.ofReal ‖G x‖ ∂μHE[n + 1]
          ≤ ∫⁻ x in ψ '' Y, ENNReal.ofReal Γ ∂μHE[n + 1] :=
            setLIntegral_mono measurable_const hGΓ
        _ = ENNReal.ofReal Γ * μHE[n + 1] (ψ '' Y) := setLIntegral_const _ _
    refine ae_lt_top' h1m ?_
    rw [h1]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hψY) hle
  -- (ii) for every `t` with a finite slice and a null critical slice
  filter_upwards [hfin, hcrit] with t hSfin hNt
  obtain ⟨U, a, r, χ, hχ, hcover⟩ :=
    Submission.dtc_bc_lc_sl_cc_slice_disks P n ψ V F t hV hψ hψV hDψ hF
  have hSm : MeasurableSet (ψ '' (Y ∩ F ⁻¹' {t})) :=
    himg _ (inter_subset_left.trans hYsV)
      (hY.inter (hF.continuous.measurable (measurableSet_singleton t)))
  -- every point of `S_t` is critical or lies on one of the disks `χⱼ(Bⱼ)`
  have hScover : ψ '' (Y ∩ F ⁻¹' {t}) ⊆
      ψ '' (Yc ∩ F ⁻¹' {t}) ∪ ⋃ j, (ψ '' (Y ∩ F ⁻¹' {t}) ∩ χ j '' ball (a j) (r j)) := by
    rintro x ⟨y, ⟨hyY, hyt⟩, rfl⟩
    by_cases hy0 : fderiv ℝ F y = 0
    · exact Or.inl ⟨y, ⟨⟨hyY, hy0⟩, hyt⟩, rfl⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover ⟨y, ⟨hYsV hyY, hyt, hy0⟩, rfl⟩)
      exact Or.inr (mem_iUnion.2 ⟨j, ⟨y, ⟨hyY, hyt⟩, rfl⟩, hj⟩)
  refine ⟨?_, ?_⟩
  · -- Step 6: rectifiability, from the countably rectifiable disks and the null critical slice
    obtain ⟨M₀, hM₀, f, hf, hM⟩ := Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun j => χ j '' U j) fun j => (hχ j).2.2.2.2.1
    refine ⟨M₀ ∪ ψ '' (Yc ∩ F ⁻¹' {t}), measure_union_null hM₀ hNt, f, hf, fun x hx => ?_⟩
    rcases hScover hx with hx | hx
    · exact Or.inl (Or.inr hx)
    · obtain ⟨j, -, hj⟩ := mem_iUnion.1 hx
      rcases hM (mem_iUnion.2 ⟨j, image_mono (ball_subset_closedBall.trans (hχ j).2.1) hj⟩)
        with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  · -- Step 7: tangent planes on each piece `S_t ∩ χⱼ(Bⱼ)`
    have hSloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ →
        μHE[n] (ψ '' (Y ∩ F ⁻¹' {t}) ∩ K) ≠ ∞ := fun K _ _ =>
      ((measure_mono inter_subset_left).trans_lt hSfin).ne
    refine ae_restrict_of_ae_restrict_of_subset hScover ?_
    rw [ae_restrict_union_iff, ae_restrict_iUnion_iff]
    refine ⟨?_, fun j => ?_⟩
    · rw [ae_restrict_eq_bot.2 hNt]
      exact Filter.eventually_bot
    obtain ⟨hUo, hBU, hχC, hχinj, -, hχfin, hχw⟩ := hχ j
    have hbU : ball (a j) (r j) ⊆ U j := ball_subset_closedBall.trans hBU
    have hAm : MeasurableSet (ψ '' (Y ∩ F ⁻¹' {t}) ∩ χ j '' ball (a j) (r j)) :=
      hSm.inter (measurableSet_ball.image_of_continuousOn_injOn (hχC.continuousOn.mono hbU)
        (hχinj.mono hbU))
    have hDm : MeasurableSet (χ j '' closedBall (a j) (r j)) :=
      measurableSet_closedBall.image_of_continuousOn_injOn (hχC.continuousOn.mono hBU)
        (hχinj.mono hBU)
    -- tangent locality for `S_t ∩ χⱼ(Bⱼ) ⊆ χⱼ(B̄ⱼ)` and for `S_t ∩ χⱼ(Bⱼ) ⊆ S_t`
    have hTL1 := Submission.cmc_imRep_locality_restrict_sub.1 P n univ _ _ isOpen_univ hAm hDm
      (inter_subset_right.trans (image_mono ball_subset_closedBall)) (subset_univ _)
      fun K _ _ => ((measure_mono inter_subset_left).trans_lt hχfin.lt_top).ne
    have hTL2 := Submission.cmc_imRep_locality_restrict_sub.1 P n univ _ _ isOpen_univ hAm hSm
      inter_subset_left (subset_univ _) hSloc
    have htan := Submission.dtc_bc_lc_sl_c1_tangent P n (χ j) (U j) (a j) (r j) hUo hBU hχC
      (hχinj.mono hBU) fun z hz => (hχw z (hBU hz)).1
    filter_upwards [hTL1, hTL2, ae_restrict_mem hAm] with x h1 h2 hx
    obtain ⟨⟨y₀, ⟨hy₀Y, -⟩, rfl⟩, w, hw, hwx⟩ := hx
    obtain ⟨-, y, hyV, hyw, -, hdy, hrange⟩ := hχw w (hbU hw)
    have hyy : y = y₀ := hψV hyV (hYsV hy₀Y) (hyw.trans hwx)
    rw [hyy] at hdy hrange
    refine ⟨hGne y₀ hy₀Y hdy, fun y' hy'Y hy' => ?_⟩
    have hy'y : y' = y₀ := hψV (hYsV hy'Y) (hYsV hy₀Y) hy'
    rw [hy'y, ← hrange (G (ψ y₀)) (hG y₀ hy₀Y).1 (hG y₀ hy₀Y).2]
    have h3 := htan w hw
    rw [hwx] at h3
    exact (h2 _).1 ((h1 _).2 h3)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
