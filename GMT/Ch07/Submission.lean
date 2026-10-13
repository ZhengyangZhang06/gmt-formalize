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

/-- **Simon, proof of 7.3.1 (p. 188): radial tangency at constant density ratio.**  If
`V = v(M, θ)` (`R = (M, θ, ξ)` in `ℝᴾ`) is stationary and `μ_V(B_ρ(0)) = aρⁿ` for every `ρ > 0`,
then `x ∈ TₓM`, i.e. `p_{TₓM}(x) = x`, for `μ_V`-a.e. `x` ("by the monotonicity formula 3.6 of
Ch. 4 … `D^⊥r = 0` `μ_C`-a.e. … That is `x ∈ Tₓ spt C` for `μ_C`-a.e. `x`").  Local
finiteness of `μ_V` forces `a < ∞`, and squeezing between open balls gives
`μ_V(B̄_ρ(0)) = aρⁿ`, so the normalized ratio is constantly `a`.  The monotonicity identity
`dtc_cone_monotonicity_identity` at `z = 0` then makes the defect
`∫_{B̄_ρ(0) \ B̄_σ(0)} |x − p_x x|² |x|^{−n−2} dμ_V` vanish; its integrand is a.e. measurable by
`dtc_cone_tangentProjection_aemeasurable`, so `p_x x = x` a.e. on every annulus, and the annuli
`B̄_{k+1}(0) \ B̄_{1/(k+1)}(0)` exhaust `ℝᴾ \ {0}`, while `p_0 0 = 0`. -/
theorem Submission.dtc_cone_radial_tangency : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (a : ℝ≥0∞), (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ ρ : ℝ, 0 < ρ → R.measure (ball 0 ρ) = a * ENNReal.ofReal (ρ ^ n)) → ∀ᵐ x ∂R.measure, (approxTangentPlane n R.carrier x).starProjection x = x := by
  intro P n R a hstat hball
  -- Step 1: `μ_V` is finite on closed balls (`θ` is locally `Hⁿ`-integrable)
  have hfin : ∀ r : ℝ, R.measure (closedBall 0 r) ≠ ∞ := fun r => by
    have h := R.locallyIntegrable_mult (closedBall 0 r) (isCompact_closedBall 0 r) (subset_univ _)
    rwa [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
  -- Step 2: `a = μ_V(B₁(0)) < ∞`
  have ha : a ≠ ∞ := by
    have h1 := hball 1 one_pos
    rw [one_pow, ENNReal.ofReal_one, mul_one] at h1
    rw [← h1]
    exact ne_top_of_le_ne_top (hfin 1) (measure_mono ball_subset_closedBall)
  -- Step 3: `μ_V(B̄_ρ(0)) = aρⁿ`, so the normalized ratio on closed balls is constantly `a`
  have hratio : ∀ ρ : ℝ, 0 < ρ → R.measure (closedBall 0 ρ) / ENNReal.ofReal (ρ ^ n) = a := by
    intro ρ hρ
    suffices h : R.measure (closedBall 0 ρ) = a * ENNReal.ofReal (ρ ^ n) by
      rw [h, ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne'
        ENNReal.ofReal_ne_top]
    refine le_antisymm ?_ ((hball ρ hρ).ge.trans (measure_mono ball_subset_closedBall))
    have hlim : Tendsto (fun t : ℝ => a * ENNReal.ofReal (t ^ n)) (𝓝[>] ρ)
        (𝓝 (a * ENNReal.ofReal (ρ ^ n))) :=
      (ENNReal.Tendsto.const_mul ((ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto ρ)
        (Or.inr ha)).mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun t (ht : ρ < t) =>
      (measure_mono (closedBall_subset_ball ht)).trans (hball t (hρ.trans ht)).le)
  -- Measurability (step 5): `x ↦ p_x x` and the defect integrand are `μ_V`-a.e. measurable,
  -- as `μ_V ≪ Hⁿ⌞M`
  have hp : AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection x)
      R.measure :=
    (continuous_fst.clm_apply continuous_snd).aemeasurable2
      ((Submission.dtc_cone_tangentProjection_aemeasurable P n univ R).mono_ac
        (withDensity_absolutelyContinuous _ _)) aemeasurable_id
  have hf : AEMeasurable (fun x => ENNReal.ofReal
      (‖x - (approxTangentPlane n R.carrier x).starProjection x‖ ^ 2 / ‖x‖ ^ (n + 2)))
      R.measure :=
    ENNReal.measurable_ofReal.comp_aemeasurable (((aemeasurable_id.sub hp).norm.pow_const 2).div
      (measurable_norm.pow_const (n + 2)).aemeasurable)
  -- Steps 4–5: the defect over each annulus `B̄_ρ(0) \ B̄_σ(0)` vanishes, so `p_x x = x` a.e. there
  have hann : ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ∀ᵐ x ∂R.measure, x ∈ closedBall 0 ρ \ closedBall 0 σ →
      (approxTangentPlane n R.carrier x).starProjection x = x := by
    intro σ ρ hσ hσρ
    have h := Submission.dtc_cone_monotonicity_identity P n R hstat 0 σ ρ hσ hσρ
    rw [hratio σ hσ, hratio ρ (hσ.trans_le hσρ)] at h
    simp only [sub_zero] at h
    have hD := (lintegral_eq_zero_iff' (hf.mono_measure Measure.restrict_le_self)).1
      ((ENNReal.add_right_inj ha).1 (h.trans (add_zero a).symm))
    have hA : MeasurableSet (closedBall (0 : Euclid P) ρ \ closedBall 0 σ) :=
      measurableSet_closedBall.diff measurableSet_closedBall
    filter_upwards [(ae_restrict_iff' hA).1 hD] with x hx hxA
    have hxσ : σ < ‖x‖ := not_le.1 fun hle => hxA.2 (mem_closedBall_zero_iff.2 hle)
    have h0 : ‖x - (approxTangentPlane n R.carrier x).starProjection x‖ ^ 2 / ‖x‖ ^ (n + 2) ≤ 0 :=
      ENNReal.ofReal_eq_zero.1 (hx hxA)
    rw [div_le_iff₀ (pow_pos (hσ.trans hxσ) _), zero_mul] at h0
    have hnorm := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm h0 (sq_nonneg _))
    exact (sub_eq_zero.1 (norm_eq_zero.1 hnorm)).symm
  -- Step 6: the annuli `B̄_{k+1}(0) \ B̄_{1/(k+1)}(0)` exhaust `ℝᴾ \ {0}`, and `p_0 0 = 0`
  have hk1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => le_add_of_nonneg_left k.cast_nonneg
  have hall := ae_all_iff.2 fun k : ℕ => hann (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) (by positivity)
    (((div_le_one (by positivity)).2 (hk1 k)).trans (hk1 k))
  filter_upwards [hall] with x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · exact map_zero _
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x‖ ‖x‖⁻¹)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine hx k (Set.mem_sdiff_of_mem ?_ ?_)
  · rw [mem_closedBall_zero_iff]
    linarith [le_max_left ‖x‖ ‖x‖⁻¹]
  · rw [mem_closedBall_zero_iff, not_le, one_div_lt hk0 hxpos, one_div]
    linarith [le_max_right ‖x‖ ‖x‖⁻¹]
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

/-- **Simon Ch. 6, Lemma 2.33, as applied in the proof of 7.3.1.**  Let `C = τ(M, θ, ξ)` be an
`n`-current in `ℝᴾ`, `n ≥ 1`, with `∂C = 0` and `x ∧ C⃗ = 0` `μ_C`-a.e.  Then `C` is a cone:
`η_{0,λ#}C = C` for every `λ > 0`.  Since `η_{0,λ#}C(ω) = C(λ⁻ⁿ ω(λ⁻¹ ·))`, it suffices that
`s ↦ C(β_s)`, `β_s(y) = sⁿ ω(s y)`, is constant on `(0, ∞)`.  Its derivative is `s⁻¹ C(L_X β_s)`,
where `(L_X β)(y) = n β(y) + Dβ(y)[y]` is the Lie derivative along the Euler field `X(y) = y`,
and `C(L_X β) = C(d ι_X β) + C(ι_X dβ) = ∂C(ι_X β) + 0 = 0` by Cartan's formula, `∂C = 0` and
`x ∧ ξ = 0`. -/
theorem Submission.dtc_cone_of_wedge_vanishing : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), 0 < n → R.Represents C → BoundaryVanishes C → (∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) (n + 1), R.orient x (ContinuousAlternatingMap.curryLeft β x) = 0) → IsConeCurrent C := by
  intro P n C R hn hR hb hw
  -- `η_{0,λ#}C(ω) = C(ω')` with `ω'(y) = λ⁻ⁿ ω(λ⁻¹ y)`, so it suffices that `C(ω') = C(ω)`
  apply Submission.dtc_cwv_isConeCurrent_of_pullback_invariant P n C
  intro lam hlam ω ω' hω'
  rw [hR ω', hR ω]
  -- `s ↦ τ(M, θ, ξ)(sⁿ ω(s ·))` is constant on `(0, ∞)` once `τ(M, θ, ξ)` kills every `L_X β`
  refine Submission.dtc_cwv_action_dilation_invariant P n R ?_ lam hlam ω ω' hω'
  intro β γ hγ
  -- `C(L_X β) = C(d ι_X β) + C(ι_X dβ) = 0`
  rw [← hR γ]
  exact Submission.dtc_cwv_euler_lie_annihilated P n C R hn hR hb hw β γ hγ
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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
