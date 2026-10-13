import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

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

/-- **Discrete growth** (Simon Ch. 3, 4.3, (10), integrated in discrete steps).  If `V > 0` on
`(0, ρ₁)` and `V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`, then
`(ρ/(2K(m+1)))^{m+1} ≤ V(ρ)` for `0 < ρ < ρ₁`.  With `W = V^{1/(m+1)}` and the Bernoulli bound
`xⁿ(x + n(y − x)) ≤ x yⁿ` (`x, y ≥ 0`), one step of length `δ` gives
`δw ≤ (W(r+δ) − W(r))(K(m+1)w + mδ)` for `0 ≤ w ≤ W(r)`.  Summing `N` such steps with
`δ = ρ/(2N)` from `ρ/2`, `w = W(ρ/2)` and `N > mρ²/(4K²(m+1)²W(ρ/2)²)` gives
`W(ρ) ≥ ρ/(2K(m+1))`. -/
theorem Submission.codim1_rdo_dg_vdl_discrete_growth : ∀ (m : ℕ) (K ρ₁ : ℝ) (V : ℝ → ℝ), 0 < K → (∀ r : ℝ, 0 < r → r < ρ₁ → 0 < V r) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → V ρ ^ ((m : ℝ) / (m + 1)) ≤ K / δ * (V (ρ + δ) - V ρ)) → ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ V ρ := by
  intro m K ρ₁ V hK hV hdiff ρ hρ hρ₁
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hKm : 0 < K * (m + 1) := by positivity
  -- Bernoulli's inequality `xⁿ (x + n (y − x)) ≤ x yⁿ` for `x, y ≥ 0`
  have bern : ∀ n : ℕ, ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ^ n * (x + n * (y - x)) ≤ x * y ^ n := by
    intro n
    induction n with
    | zero => intro x y _ _; simp
    | succ n ih =>
      intro x y hx hy
      have h1 := mul_le_mul_of_nonneg_left (ih x y hx hy) hy
      have h2 : 0 ≤ x ^ n * (n * (y - x) ^ 2) :=
        mul_nonneg (pow_nonneg hx n) (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg (y - x)))
      rw [pow_succ, pow_succ]
      push_cast
      linarith
  -- Step 2: `W = V^{1/(m+1)}`, so `W > 0`, `W^{m+1} = V` and `W^m = V^{m/(m+1)}`
  obtain ⟨W, hWpos, hWpow, hWpowm⟩ : ∃ W : ℝ → ℝ, (∀ r, 0 < r → r < ρ₁ → 0 < W r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ (m + 1) = V r) ∧
      (∀ r, 0 < r → r < ρ₁ → W r ^ m = V r ^ ((m : ℝ) / (m + 1))) := by
    refine ⟨fun r => V r ^ ((1 : ℝ) / (m + 1)), fun r h1 h2 => Real.rpow_pos_of_pos (hV r h1 h2) _,
      fun r h1 h2 => ?_, fun r h1 h2 => ?_⟩
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = V r
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, Nat.cast_add_one,
        one_div_mul_cancel hm1, Real.rpow_one]
    · show (V r ^ ((1 : ℝ) / (m + 1))) ^ m = V r ^ ((m : ℝ) / (m + 1))
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hV r h1 h2).le, one_div_mul_eq_div]
  -- Step 3, algebra: `δ bᵐ ≤ K (a^{m+1} − b^{m+1})` and `0 ≤ w ≤ b` give
  -- `δ w ≤ (a − b) (K (m+1) w + m δ)`
  have alg : ∀ a b δ w : ℝ, 0 < a → 0 < b → 0 < δ → 0 ≤ w → w ≤ b →
      δ * b ^ m ≤ K * (a ^ (m + 1) - b ^ (m + 1)) →
      δ * w ≤ (a - b) * (K * (m + 1) * w + m * δ) := by
    intro a b δ w ha hb hδ hw0 hwb hd
    rw [pow_succ, pow_succ] at hd
    have hP : 0 < a ^ m := pow_pos ha m
    have hQ : 0 < b ^ m := pow_pos hb m
    have hB1 := bern (m + 1) a b ha.le hb.le
    rw [pow_succ, pow_succ] at hB1
    push_cast at hB1
    have hB0 := bern m a b ha.le hb.le
    -- `a^{m+1} − b^{m+1} ≤ (m+1) aᵐ (a − b)`
    have h1 : a ^ m * a - b ^ m * b ≤ (m + 1) * a ^ m * (a - b) := by
      have h : a * (a ^ m * a - b ^ m * b) ≤ a * ((m + 1) * a ^ m * (a - b)) := by linarith
      exact le_of_mul_le_mul_left h ha
    have h2 : δ * b ^ m ≤ K * (m + 1) * a ^ m * (a - b) := by
      have := mul_le_mul_of_nonneg_left h1 hK.le
      linarith
    have hab : 0 ≤ a - b := by
      by_contra hcon
      have : K * (m + 1) * a ^ m * (a - b) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hKm.le hP.le) (not_le.mp hcon).le
      have : 0 < δ * b ^ m := mul_pos hδ hQ
      linarith
    -- `δ (a − m (a − b)) ≤ K (m+1) a (a − b)`
    have h3 : δ * (a + m * (b - a)) ≤ K * (m + 1) * a * (a - b) := by
      have e1 := mul_le_mul_of_nonneg_left hB0 hδ.le
      have e2 := mul_le_mul_of_nonneg_left h2 ha.le
      have h4 : a ^ m * (δ * (a + m * (b - a))) ≤ a ^ m * (K * (m + 1) * a * (a - b)) := by
        linarith
      exact le_of_mul_le_mul_left h4 hP
    have h5 : a * (δ * w) ≤ a * ((a - b) * (K * (m + 1) * w + m * δ)) := by
      have e1 := mul_le_mul_of_nonneg_left h3 hw0
      have e2 : 0 ≤ (a - b) * m * δ * (a - w) :=
        mul_nonneg (mul_nonneg (mul_nonneg hab hm0) hδ.le) (by linarith)
      linarith
    exact le_of_mul_le_mul_left h5 ha
  -- Step 3: one step of length `δ`
  have step : ∀ r δ w : ℝ, 0 < r → 0 < δ → r + δ < ρ₁ → 0 ≤ w → w ≤ W r →
      δ * w ≤ (W (r + δ) - W r) * (K * (m + 1) * w + m * δ) := by
    intro r δ w hr hδ hrδ hw0 hwb
    have hr1 : r < ρ₁ := by linarith
    have hrδ0 : 0 < r + δ := by linarith
    have hd := hdiff r δ hr hδ hrδ
    rw [← hWpowm r hr hr1, ← hWpow r hr hr1, ← hWpow (r + δ) hrδ0 hrδ] at hd
    refine alg _ _ δ w (hWpos _ hrδ0 hrδ) (hWpos r hr hr1) hδ hw0 hwb ?_
    have hδne : δ ≠ 0 := hδ.ne'
    calc δ * W r ^ m ≤ δ * (K / δ * (W (r + δ) ^ (m + 1) - W r ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hd hδ.le
      _ = K * (W (r + δ) ^ (m + 1) - W r ^ (m + 1)) := by field_simp
  -- Step 4′: `N` steps of length `δ = ρ/(2N)` from `ρ/2`
  have hρ2 : 0 < ρ / 2 := by linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ = W (ρ / 2) := ⟨_, rfl⟩
  have hw₀pos : 0 < w₀ := by rw [hw₀]; exact hWpos _ hρ2 (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt ((m : ℝ) * ρ ^ 2 / (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ρ / (2 * N) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hNδ : (N : ℝ) * δ = ρ / 2 := by
    rw [hδ]
    field_simp
  have ind : ∀ j : ℕ, j ≤ N →
      (j : ℝ) * δ * w₀ ≤ (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) := by
    intro j
    induction j with
    | zero => intro _; simp [hw₀]
    | succ j ih =>
      intro hj
      have ih' := ih (Nat.le_of_succ_le hj)
      have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
      have hr : 0 < ρ / 2 + j * δ := by positivity
      have hrδ : ρ / 2 + j * δ + δ < ρ₁ := by
        have := mul_le_mul_of_nonneg_right hjN hδpos.le
        linarith
      have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
      have hwb : w₀ ≤ W (ρ / 2 + j * δ) := by
        by_contra hcon
        have h1 : (K * (m + 1) * w₀ + m * δ) * (W (ρ / 2 + j * δ) - w₀) < 0 :=
          mul_neg_of_pos_of_neg hcoef (by linarith [not_le.mp hcon])
        have h2 : 0 ≤ (j : ℝ) * δ * w₀ := by positivity
        linarith
      have hs := step (ρ / 2 + j * δ) δ w₀ hr hδpos hrδ hw₀pos.le hwb
      have heq : ρ / 2 + ((j + 1 : ℕ) : ℝ) * δ = ρ / 2 + j * δ + δ := by push_cast; ring
      rw [heq]
      push_cast
      linarith
  have hfin := ind N le_rfl
  have hρN : ρ / 2 + (N : ℝ) * δ = ρ := by rw [hNδ]; ring
  rw [hρN, hNδ] at hfin
  -- `N` is large: `m δ ρ < 2 (K (m+1))² w₀²`
  have hmδ : (m : ℝ) * δ * ρ < 2 * (K * (m + 1)) ^ 2 * w₀ ^ 2 := by
    have h1 : (m : ℝ) * ρ ^ 2 < N * (4 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rwa [div_lt_iff₀ (by positivity)] at hN
    have h2 : (2 * N) * ((m : ℝ) * δ * ρ) = m * ρ ^ 2 := by
      have : (2 * N) * ((m : ℝ) * δ * ρ) = 2 * m * ρ * (N * δ) := by ring
      rw [this, hNδ]; ring
    have h3 : (2 * N) * ((m : ℝ) * δ * ρ) < (2 * N) * (2 * (K * (m + 1)) ^ 2 * w₀ ^ 2) := by
      rw [h2]; linarith
    exact lt_of_mul_lt_mul_left h3 (by positivity)
  -- Steps 4′(c) and 6: `ρ/(2K(m+1)) ≤ W(ρ)`, so `(ρ/(2K(m+1)))^{m+1} ≤ W(ρ)^{m+1} = V(ρ)`
  have hA : ρ / (2 * K * (m + 1)) ≤ W ρ := by
    rw [div_le_iff₀ (by positivity)]
    by_contra hcon
    have hcoef : 0 < K * (m + 1) * w₀ + m * δ := by positivity
    have e1 := mul_lt_mul_of_pos_left (not_le.mp hcon) hcoef
    have e2 := mul_le_mul_of_nonneg_left hfin hKm.le
    have e3 : 0 ≤ K * (m + 1) * m * δ * w₀ := by positivity
    linarith
  calc (ρ / (2 * K * (m + 1))) ^ (m + 1) ≤ W ρ ^ (m + 1) :=
        pow_le_pow_left₀ (by positivity) hA (m + 1)
    _ = V ρ := hWpow ρ hρ hρ₁
/-- **Annular cut-off** (step 3 of the lower volume-density bound in De Giorgi's theorem, Simon
Ch. 3, 4.3, proof of (10)–(11)).  There is `C₀ > 0` such that for all `ρ, δ > 0` some `C¹`
function `ζ` on `ℝᴾ` has compact support in `B̄_{ρ+δ}(y)`, `0 ≤ ζ ≤ 1`, `ζ = 1` on `B̄_ρ(y)`,
`‖Dζ‖ ≤ C₀/δ`, and `Dζ = 0` off the open annulus `B_{ρ+δ}(y) \ B̄_ρ(y)`.  Take `C₀ = 3/2` and
`ζ(z) = h((‖z − y‖ − ρ)/δ)` with `h(t) = 1 − ∫₀ᵗ 6 max(0, s(1 − s)) ds` (`= 1 − 3t² + 2t³` on
`[0, 1]`): `h` is `C¹`, `1` on `(−∞, 0]`, `0` on `[1, ∞)`, `h' = 0` there and `|h'| ≤ 3/2`.  Then
`ζ` is constant near `y`, `h ∘ u` with `u` smooth away from `y`, and `(3/(2δ))`-Lipschitz by the
reverse triangle inequality. -/
theorem Submission.codim1_rdo_dg_vdl_annular_cutoff : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ C₀ / δ) ∧ ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
  -- Step 1: the profile `h(t) = 1 − ∫₀ᵗ g`, `g(s) = 6 max(0, s(1 − s))`
  obtain ⟨h, hh_C1, hh_flat, hh_bounds, hh_one, hh_zero, hh_lip⟩ : ∃ h : ℝ → ℝ,
      ContDiff ℝ 1 h ∧ (∀ t, t ≤ 0 ∨ 1 ≤ t → HasDerivAt h 0 t) ∧ (∀ t, 0 ≤ h t ∧ h t ≤ 1) ∧
      (∀ t, t ≤ 0 → h t = 1) ∧ (∀ t, 1 ≤ t → h t = 0) ∧
      ∀ a b, ‖h b - h a‖ ≤ 3 / 2 * ‖b - a‖ := by
    set g : ℝ → ℝ := fun s => 6 * max 0 (s * (1 - s)) with hg_eq
    have hg_cont : Continuous g := by fun_prop
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ s, 0 ≤ g s := fun s => mul_nonneg (by norm_num) (le_max_left _ _)
    have hg_le : ∀ s, g s ≤ 3 / 2 := fun s => by
      have h : max 0 (s * (1 - s)) ≤ 1 / 4 :=
        max_le (by norm_num) (by nlinarith [sq_nonneg (s - 1 / 2)])
      simp only [hg_eq]
      linarith
    have hg_left : ∀ s, s ≤ 0 → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonpos_of_nonneg hs (by linarith)), mul_zero]
    have hg_right : ∀ s, 1 ≤ s → g s = 0 := fun s hs => by
      simp only [hg_eq]
      rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)), mul_zero]
    -- `∫₀¹ g = 1`: on `[0, 1]`, `g(s) = 6s(1 − s)` is the derivative of `3s² − 2s³`
    have hg_one : ∫ s in (0 : ℝ)..1, g s = 1 := by
      have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 3 * s ^ 2 - 2 * s ^ 3)
          (6 * (s * (1 - s))) s := fun s => by
        convert ((hasDerivAt_pow 2 s).const_mul 3).sub ((hasDerivAt_pow 3 s).const_mul 2) using 1
        norm_num
        ring
      rw [intervalIntegral.integral_congr (g := fun s => 6 * (s * (1 - s))) ?_,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hderiv s)
          ((by fun_prop : Continuous fun s : ℝ => 6 * (s * (1 - s))).intervalIntegrable _ _)]
      · norm_num
      · intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        simp only [hg_eq]
        rw [max_eq_right (mul_nonneg hs.1 (by linarith [hs.2]))]
    -- the primitive `F(t) = ∫₀ᵗ g`, with `F' = g`
    set F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, g s with hF_eq
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hF_left : ∀ t, t ≤ 0 → F t = 0 := fun t ht => by
      simp only [hF_eq]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = 1 := fun t ht => by
      simp only [hF_eq]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int 0 1) (hg_int 1 t), hg_one]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ 1 := fun t => by
      rcases le_total t 0 with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, zero_le_one⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨zero_le_one, le_rfl⟩
      refine ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u, ?_⟩
      rw [← hg_one]
      exact intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg)
        (hg_int _ _)
    -- `h = 1 − F`, with `h' = −g`
    have hh_deriv : ∀ t, HasDerivAt (fun t => 1 - F t) (-g t) t := fun t =>
      (hF_deriv t).const_sub 1
    refine ⟨fun t => 1 - F t, ?_, fun t ht => ?_, fun t => ?_, fun t ht => ?_, fun t ht => ?_,
      fun a b => ?_⟩
    · rw [contDiff_one_iff_deriv]
      refine ⟨fun t => (hh_deriv t).differentiableAt, ?_⟩
      rw [show deriv (fun t => 1 - F t) = fun t => -g t from funext fun t => (hh_deriv t).deriv]
      exact hg_cont.neg
    · have hg0 : g t = 0 := ht.elim (hg_left t) (hg_right t)
      simpa [hg0] using hh_deriv t
    · obtain ⟨h₀, h₁⟩ := hF_bounds t
      exact ⟨by linarith, by linarith⟩
    · simp only [hF_left t ht, sub_zero]
    · simp only [hF_right t ht, sub_self]
    · refine convex_univ.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t _ => (hh_deriv t).hasDerivWithinAt) (fun t _ => ?_) (mem_univ a) (mem_univ b)
      rw [norm_neg, Real.norm_of_nonneg (hg_nonneg t)]
      exact hg_le t
  -- Step 2: `C₀ = 3/2` and `ζ(z) = h(u(z))`, `u(z) = (‖z − y‖ − ρ)/δ`
  refine ⟨3 / 2, by norm_num, fun P y ρ δ hρ hδ => ?_⟩
  -- Step 3: `ζ ≡ 1` on `B_ρ(y)`, a neighbourhood of `y`
  have hζ_near : (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) =ᶠ[𝓝 y] fun _ => 1 := by
    filter_upwards [Metric.ball_mem_nhds y hρ] with z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- `u` is smooth away from `y`
  have hu : ∀ z : Euclid P, z ≠ y → ContDiffAt ℝ 1 (fun w : Euclid P => (‖w - y‖ - ρ) / δ) z :=
    fun z hz => (((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hz)).sub
      contDiffAt_const).div_const δ
  -- Step 4: `ζ = 0` off `B_{ρ+δ}(y)`, so `tsupport ζ ⊆ closure B_{ρ+δ}(y) ⊆ B̄_{ρ+δ}(y)`
  have htsupp : tsupport (fun z : Euclid P => h ((‖z - y‖ - ρ) / δ)) ⊆ closedBall y (ρ + δ) := by
    refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro z hz
    by_contra hzb
    apply hz
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hzb
    exact hh_zero _ ((le_div_iff₀ hδ).2 (by linarith))
  refine ⟨fun z => h ((‖z - y‖ - ρ) / δ), ?_,
    (isCompact_closedBall y (ρ + δ)).of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp,
    fun z => hh_bounds _, fun z hz => ?_, fun z => ?_, fun z hz => ?_⟩
  -- Step 5: `ζ` is `C¹` — constant near `y`, and `h ∘ u` with `u` smooth away from `y`
  · rw [contDiff_iff_contDiffAt]
    intro z
    rcases eq_or_ne z y with rfl | hz
    · exact contDiffAt_const.congr_of_eventuallyEq hζ_near
    · exact hh_C1.contDiffAt.comp z (hu z hz)
  -- Step 3: `ζ = 1` on `B̄_ρ(y)`
  · rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact hh_one _ ((div_le_iff₀ hδ).2 (by linarith))
  -- Step 6: `ζ` is `(3/(2δ))`-Lipschitz (reverse triangle inequality), so `‖Dζ(z)‖ ≤ 3/(2δ)`
  · refine norm_fderiv_le_of_lip' ℝ (by positivity) (Eventually.of_forall fun w => ?_)
    calc ‖h ((‖w - y‖ - ρ) / δ) - h ((‖z - y‖ - ρ) / δ)‖
        ≤ 3 / 2 * ‖(‖w - y‖ - ρ) / δ - (‖z - y‖ - ρ) / δ‖ := hh_lip _ _
      _ = 3 / 2 / δ * |‖w - y‖ - ‖z - y‖| := by
          rw [Real.norm_eq_abs, ← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hδ]
          ring
      _ ≤ 3 / 2 / δ * ‖(w - y) - (z - y)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = 3 / 2 / δ * ‖w - z‖ := by rw [sub_sub_sub_cancel_right]
  -- Step 7: `Dζ(z) = 0` off the open annulus
  · rcases eq_or_ne z y with rfl | hzy
    · rw [hζ_near.fderiv_eq, fderiv_const_apply]
    · -- `u(z) ≤ 0` or `u(z) ≥ 1`, where `h' = 0`; chain rule
      have hu_out : (‖z - y‖ - ρ) / δ ≤ 0 ∨ 1 ≤ (‖z - y‖ - ρ) / δ := by
        rcases le_or_gt ‖z - y‖ ρ with h₁ | h₁
        · exact Or.inl ((div_le_iff₀ hδ).2 (by linarith))
        · refine Or.inr ((le_div_iff₀ hδ).2 ?_)
          have h₂ : z ∉ ball y (ρ + δ) := fun hb => hz ⟨hb, by
            rw [Metric.mem_closedBall, dist_eq_norm, not_le]
            exact h₁⟩
          rw [Metric.mem_ball, dist_eq_norm, not_lt] at h₂
          linarith
      have hD := (hh_flat _ hu_out).comp_hasFDerivAt z
        ((hu z hzy).differentiableAt one_ne_zero).hasFDerivAt
      rw [zero_smul] at hD
      exact hD.fderiv

/-- **Finite-difference form of De Giorgi's volume estimate** (Simon Ch. 3, 4.3, the first
displays of (10); used for 7.5.8).  Let `G ⊆ ℝ^{m+1}` (`m ≥ 1`) be Borel and
`V(r) = L^{m+1}(G ∩ B̄_r(y))`.  Suppose `(∫_G ζ^{(m+1)/m})^{m/(m+1)} ≤ c (∫ ζ dμ + ∫_G |Dζ|)`
for every `C¹` function `ζ ≥ 0` with compact support in `D ⊇ B̄_{ρ₁}(y)` (`μ(B̄_{ρ₁}(y)) < ∞`), and
`δ μ(B̄_ρ(y)) ≤ C₁ L^{m+1}(G ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0`, `ρ + δ < ρ₁`.  Then
`V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ+δ) − V(ρ))` for such `ρ, δ`, with `K = 2c(C₁ + C₀)`, `C₀` the constant
of `Submission.codim1_rdo_dg_vdl_annular_cutoff`.  Test the Sobolev inequality with that cut-off
`ζ` for the radii `ρ` and `η = δ/2`: the left side is at least `V(ρ)^{m/(m+1)}`, since `ζ = 1` on
`B̄_ρ(y)`; `∫ ζ dμ ≤ μ(B̄_{ρ+η}(y)) ≤ (C₁/η) L^{m+1}(G ∩ A₂)`, `A₂ = B_{ρ+δ}(y) \ B̄_{ρ+η}(y)`, by
the second hypothesis at radius `ρ + η`; and `∫_G |Dζ| ≤ (C₀/η) L^{m+1}(G ∩ A₁)`,
`A₁ = B_{ρ+η}(y) \ B̄_ρ(y)`.  The sets `G ∩ B̄_ρ(y)`, `G ∩ A₁` and `G ∩ A₂` are disjoint subsets of
`G ∩ B̄_{ρ+δ}(y)`. -/
theorem Submission.codim1_rdo_dg_vdl_finite_difference : ∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ K : ℝ, 0 < K ∧ ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤ K / δ * ((volume (G ∩ closedBall y (ρ + δ))).toReal - (volume (G ∩ closedBall y ρ)).toReal) := by
  intro m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ hS hA
  obtain ⟨C₀, hC₀, hcut⟩ := Submission.codim1_rdo_dg_vdl_annular_cutoff
  refine ⟨2 * c * (C₁ + C₀), mul_pos (mul_pos two_pos hc) (by linarith), ?_⟩
  intro ρ δ hρ hδ hρδ
  -- Step 0: the exponents, the half width `η = δ/2` and the two annuli `A₁`, `A₂`.
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hp : (0 : ℝ) < (m + 1 : ℝ) / m := div_pos (by positivity) hm0
  have hq : (0 : ℝ) ≤ (m : ℝ) / (m + 1) := by positivity
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = δ / 2 := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact half_pos hδ
  set A₁ := ball y (ρ + η) \ closedBall y ρ
  set A₂ := ball y (ρ + δ) \ closedBall y (ρ + η)
  have hA₁m : MeasurableSet A₁ := measurableSet_ball.diff measurableSet_closedBall
  have hA₂m : MeasurableSet A₂ := measurableSet_ball.diff measurableSet_closedBall
  have hA₁fin : volume A₁ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hA₂fin : volume A₂ ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hGA₁fin : volume (G ∩ A₁) ≠ ∞ := ne_top_of_le_ne_top hA₁fin (measure_mono inter_subset_right)
  have hGA₂fin : volume (G ∩ A₂) ≠ ∞ := ne_top_of_le_ne_top hA₂fin (measure_mono inter_subset_right)
  have hGB : ∀ r : ℝ, volume (G ∩ closedBall y r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono inter_subset_right)
  -- `∫_G 𝟙_s a dL^{m+1} = a L^{m+1}(G ∩ s)`
  have hind : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → ∀ a : ℝ,
      ∫ z in G, s.indicator (fun _ => a) z = a * (volume (G ∩ s)).toReal := by
    intro s hs a
    rw [integral_indicator_const a hs, measureReal_restrict_apply hs, smul_eq_mul, mul_comm,
      inter_comm s G, measureReal_def]
  -- Step 1: the cut-off `ζ` for the radii `ρ` and `η`; it is admissible in the Sobolev inequality.
  obtain ⟨ζ, hζC, hζc, hζsupp, hζ01, hζ1, hζgrad, hζzero⟩ := hcut (m + 1) y ρ η hρ hη
  have hsub : closedBall y (ρ + η) ⊆ closedBall y ρ₁ := closedBall_subset_closedBall (by linarith)
  have hSob := hS ζ hζC hζc (hζsupp.trans (hsub.trans hD)) fun z => (hζ01 z).1
  -- Step 2: `V(ρ) ≤ ∫_G ζ^{(m+1)/m}`, as `ζ^{(m+1)/m} ≥ 𝟙_{B̄_ρ}`.
  have hleft : (volume (G ∩ closedBall y ρ)).toReal ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
    have hcont : Continuous fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζC.continuous.rpow_const fun _ => Or.inr hp.le
    have hcpt : HasCompactSupport fun z => ζ z ^ ((m + 1 : ℝ) / m) :=
      hζc.comp_left (g := fun t : ℝ => t ^ ((m + 1 : ℝ) / m)) (Real.zero_rpow hp.ne')
    have hint : Integrable (fun z => ζ z ^ ((m + 1 : ℝ) / m)) (volume.restrict G) :=
      (hcont.integrable_of_hasCompactSupport hcpt).integrableOn
    calc (volume (G ∩ closedBall y ρ)).toReal
        = ∫ z in G, (closedBall y ρ).indicator (fun _ => (1 : ℝ)) z := by
          rw [hind _ measurableSet_closedBall, one_mul]
      _ ≤ ∫ z in G, ζ z ^ ((m + 1 : ℝ) / m) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hint
            (Eventually.of_forall fun z => ?_)
          · exact indicator_nonneg (fun _ _ => zero_le_one) z
          · dsimp only
            by_cases hz : z ∈ closedBall y ρ
            · rw [indicator_of_mem hz, hζ1 z hz, Real.one_rpow]
            · rw [indicator_of_notMem hz]
              exact Real.rpow_nonneg (hζ01 z).1 _
  -- Step 3: `η ∫ ζ dμ ≤ η μ(B̄_{ρ+η}) ≤ C₁ L^{m+1}(G ∩ A₂)`, by the annular bound at `ρ + η`.
  have hμfin : μ (closedBall y (ρ + η)) ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono hsub)
  have hIμ : ∫ z, ζ z ∂μ ≤ (μ (closedBall y (ρ + η))).toReal := by
    have hint : Integrable ((closedBall y (ρ + η)).indicator fun _ => (1 : ℝ)) μ :=
      (integrableOn_const hμfin).integrable_indicator measurableSet_closedBall
    calc ∫ z, ζ z ∂μ ≤ ∫ z, (closedBall y (ρ + η)).indicator (fun _ => (1 : ℝ)) z ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => (hζ01 z).1) hint
            (Eventually.of_forall fun z => ?_)
          by_cases hz : z ∈ closedBall y (ρ + η)
          · rw [indicator_of_mem hz]
            exact (hζ01 z).2
          · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport fun h => hz (hζsupp h)]
      _ = (μ (closedBall y (ρ + η))).toReal := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_one,
            measureReal_def]
  have hAη : ENNReal.ofReal η * μ (closedBall y (ρ + η)) ≤
      ENNReal.ofReal C₁ * volume (G ∩ A₂) := by
    have h := hA (ρ + η) η (by linarith) hη (by linarith)
    rwa [show ρ + η + η = ρ + δ by linarith] at h
  have hμterm : η * ∫ z, ζ z ∂μ ≤ C₁ * (volume (G ∩ A₂)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGA₂fin) hAη
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
      ENNReal.toReal_ofReal hC₁] at h
    exact (mul_le_mul_of_nonneg_left hIμ hη.le).trans h
  -- Step 4: `η ∫_G |Dζ| ≤ C₀ L^{m+1}(G ∩ A₁)`, as `|Dζ| ≤ (C₀/η) 𝟙_{A₁}`.
  have hgrad : ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ / η * (volume (G ∩ A₁)).toReal := by
    have hint : Integrable (A₁.indicator fun _ => C₀ / η) (volume.restrict G) :=
      ((integrableOn_const hA₁fin).integrable_indicator hA₁m).integrableOn
    calc ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ ∫ z in G, A₁.indicator (fun _ => C₀ / η) z := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun z => norm_nonneg _) hint
            (Eventually.of_forall fun z => ?_)
          dsimp only
          by_cases hz : z ∈ A₁
          · rw [indicator_of_mem hz]
            exact hζgrad z
          · rw [indicator_of_notMem hz, hζzero z hz, norm_zero]
      _ = C₀ / η * (volume (G ∩ A₁)).toReal := hind A₁ hA₁m _
  have hgradterm : η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ C₀ * (volume (G ∩ A₁)).toReal := by
    calc η * ∫ z in G, ‖fderiv ℝ ζ z‖ ≤ η * (C₀ / η * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left hgrad hη.le
      _ = C₀ * (volume (G ∩ A₁)).toReal := by field_simp
  -- Step 5: `G ∩ B̄_ρ`, `G ∩ A₁`, `G ∩ A₂` are disjoint subsets of `G ∩ B̄_{ρ+δ}`.
  have hpieces : (volume (G ∩ closedBall y ρ)).toReal + (volume (G ∩ A₁)).toReal +
      (volume (G ∩ A₂)).toReal ≤ (volume (G ∩ closedBall y (ρ + δ))).toReal := by
    have hd₁ : Disjoint (G ∩ closedBall y ρ) (G ∩ A₁) := by
      rw [Set.disjoint_left]
      rintro z ⟨-, hz⟩ ⟨-, -, hz'⟩
      exact hz' hz
    have hd₂ : Disjoint (G ∩ closedBall y ρ ∪ G ∩ A₁) (G ∩ A₂) := by
      rw [Set.disjoint_left]
      rintro z hz ⟨-, -, hz'⟩
      apply hz'
      rcases hz with ⟨-, hz⟩ | ⟨-, hz, -⟩
      · exact closedBall_subset_closedBall (by linarith) hz
      · exact ball_subset_closedBall hz
    have hsub' : G ∩ closedBall y ρ ∪ G ∩ A₁ ∪ G ∩ A₂ ⊆ G ∩ closedBall y (ρ + δ) := by
      rintro z ((⟨hzG, hz⟩ | ⟨hzG, hz, -⟩) | ⟨hzG, hz, -⟩)
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) hz⟩
      · exact ⟨hzG, closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz)⟩
      · exact ⟨hzG, ball_subset_closedBall hz⟩
    have hle : volume (G ∩ closedBall y ρ) + volume (G ∩ A₁) + volume (G ∩ A₂) ≤
        volume (G ∩ closedBall y (ρ + δ)) := by
      rw [← measure_union hd₁ (hG.inter hA₁m), ← measure_union hd₂ (hG.inter hA₂m)]
      exact measure_mono hsub'
    rw [← ENNReal.toReal_add (hGB ρ) hGA₁fin,
      ← ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hGB ρ, hGA₁fin⟩) hGA₂fin]
    exact ENNReal.toReal_mono (hGB (ρ + δ)) hle
  -- Step 6: combine, with `δ = 2η` and `K = 2c(C₁ + C₀)`.
  have ha₁ : 0 ≤ (volume (G ∩ A₁)).toReal := ENNReal.toReal_nonneg
  have ha₂ : 0 ≤ (volume (G ∩ A₂)).toReal := ENNReal.toReal_nonneg
  have hlhs : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖) :=
    (Real.rpow_le_rpow ENNReal.toReal_nonneg hleft hq).trans hSob
  have hann : C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal ≤
      (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    nlinarith [mul_nonneg hC₁ ha₁, mul_nonneg hC₀.le ha₂]
  have key : η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) ≤
      c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
        (volume (G ∩ closedBall y ρ)).toReal) := by
    calc η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))
        ≤ η * (c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) :=
          mul_le_mul_of_nonneg_left hlhs hη.le
      _ = c * (η * ∫ z, ζ z ∂μ + η * ∫ z in G, ‖fderiv ℝ ζ z‖) := by ring
      _ ≤ c * (C₁ * (volume (G ∩ A₂)).toReal + C₀ * (volume (G ∩ A₁)).toReal) :=
          mul_le_mul_of_nonneg_left (add_le_add hμterm hgradterm) hc.le
      _ ≤ c * ((C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal)) :=
          mul_le_mul_of_nonneg_left hann hc.le
      _ = c * (C₁ + C₀) * ((volume (G ∩ closedBall y (ρ + δ))).toReal -
            (volume (G ∩ closedBall y ρ)).toReal) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  have hδη : (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1)) * δ =
      2 * (η * (volume (G ∩ closedBall y ρ)).toReal ^ ((m : ℝ) / (m + 1))) := by
    rw [hη_def]
    ring
  rw [hδη]
  linarith

/-- **One-sided volume density bound** (the lower bound (10) of Simon Ch. 3, 4.3, for a general
Borel `G`).  Under the Sobolev inequality (S) on `D ⊇ B̄_{ρ₁}(y)` and the annular bound (A), with
`μ(B̄_r(y)) ≠ 0` for `r > 0`, there is `c' > 0` with `c'ρ^{m+1} ≤ L(G ∩ B_ρ(y))` for
`0 < ρ < ρ₁`.  With `V(r) = L(G ∩ B̄_r(y))`, `finite_difference` gives
`V(ρ)^{m/(m+1)} ≤ (K/δ)(V(ρ + δ) − V(ρ))`; (A) at `ρ = δ = r/2` and `μ(B̄_{r/2}(y)) ≠ 0` give
`V(r) > 0` on `(0, ρ₁)`; `discrete_growth` then gives `V(r) ≥ (r/(2K(m+1)))^{m+1}`, and
`B̄_{ρ/2}(y) ⊆ B_ρ(y)` gives the bound with `c' = (1/(4K(m+1)))^{m+1}`. -/
theorem Submission.codim1_rdo_dg_vdl_one_sided_density : ∀ (m : ℕ) (D G : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (y : Euclid (m + 1)) (ρ₁ C₁ c : ℝ), 1 ≤ m → MeasurableSet G → 0 < c → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → μ (closedBall y ρ₁) ≠ ∞ → (∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0) → (∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in G, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in G, ‖fderiv ℝ ζ z‖)) → (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C₁ * volume (G ∩ (ball y (ρ + δ) \ closedBall y ρ))) → ∃ c' : ℝ, 0 < c' ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ENNReal.ofReal (c' * ρ ^ (m + 1)) ≤ volume (G ∩ ball y ρ) := by
  intro m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ_fin hμ_pos hS hA
  -- Step 1: the finite-difference inequality for `V(r) = L(G ∩ B̄_r(y))`
  obtain ⟨K, hK, hdiff⟩ :=
    Submission.codim1_rdo_dg_vdl_finite_difference m D G μ y ρ₁ C₁ c hm hG hc hC₁ hD hμ_fin hS hA
  -- Step 2: `L(G ∩ B̄_r(y)) ≤ L(B̄_r(y)) < ∞`
  have hfin : ∀ r : ℝ, volume (G ∩ closedBall y r) ≠ ∞ := fun r =>
    ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
  -- Step 3: `V > 0` on `(0, ρ₁)`, from (A) at `ρ = δ = r/2`
  have hV_pos : ∀ r : ℝ, 0 < r → r < ρ₁ → 0 < (volume (G ∩ closedBall y r)).toReal := by
    intro r hr hrρ₁
    have hA' := hA (r / 2) (r / 2) (half_pos hr) (half_pos hr) (by linarith)
    have hlhs : ENNReal.ofReal (r / 2) * μ (closedBall y (r / 2)) ≠ 0 :=
      mul_ne_zero (ENNReal.ofReal_ne_zero_iff.2 (half_pos hr)) (hμ_pos _ (half_pos hr))
    have hann : volume (G ∩ (ball y (r / 2 + r / 2) \ closedBall y (r / 2))) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hA'
      exact hlhs (le_zero_iff.1 hA')
    have hsub : G ∩ (ball y (r / 2 + r / 2) \ closedBall y (r / 2)) ⊆ G ∩ closedBall y r := by
      rw [add_halves]
      exact inter_subset_inter_right _ (sdiff_subset.trans ball_subset_closedBall)
    exact ENNReal.toReal_pos (fun h0 => hann (measure_mono_null hsub h0)) (hfin r)
  -- Step 4: discrete growth, `V(r) ≥ (r/(2K(m+1)))^{m+1}` on `(0, ρ₁)`
  have hgrowth := Submission.codim1_rdo_dg_vdl_discrete_growth m K ρ₁
    (fun r => (volume (G ∩ closedBall y r)).toReal) hK hV_pos hdiff
  -- Step 5: evaluate at `ρ/2`, with `c' = (1/(4K(m+1)))^{m+1}` and `B̄_{ρ/2}(y) ⊆ B_ρ(y)`
  refine ⟨(1 / (4 * K * (m + 1))) ^ (m + 1), by positivity, fun ρ hρ hρρ₁ => ?_⟩
  have hc' : (1 / (4 * K * (m + 1))) ^ (m + 1) * ρ ^ (m + 1) =
      (ρ / 2 / (2 * K * (m + 1))) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  calc ENNReal.ofReal ((1 / (4 * K * (m + 1))) ^ (m + 1) * ρ ^ (m + 1))
      ≤ ENNReal.ofReal (volume (G ∩ closedBall y (ρ / 2))).toReal := by
        rw [hc']
        exact ENNReal.ofReal_le_ofReal (hgrowth (ρ / 2) (half_pos hρ) (by linarith))
    _ = volume (G ∩ closedBall y (ρ / 2)) := ENNReal.ofReal_toReal (hfin _)
    _ ≤ volume (G ∩ ball y ρ) :=
        measure_mono (inter_subset_inter_right _ (closedBall_subset_ball (half_lt_self hρ)))
/-- **The divergence of a compactly supported `C¹` vector field integrates to zero** (used for the
complement in Simon Ch. 3, 4.3 (11)): `∫ trace Dφ(z) dLᴾ(z) = 0` for `φ ∈ C¹_c(ℝᴾ; ℝᴾ)`.
For fixed `w`, the difference quotients `g_t = t⁻¹(φ(· + tw) − φ)` have integral `0` by
translation invariance of `Lᴾ`, tend to `Dφ(·)w` pointwise as `t → 0`, and for `0 < |t| ≤ 1` are
bounded by `M‖w‖ 1_{K'}`, where `M = sup ‖Dφ‖` (mean value inequality) and
`K' = cthickening ‖w‖ (spt φ)` is compact; dominated convergence gives `∫ Dφ(z)w dz = 0`.
Finally `trace Dφ(z) = Σᵢ ⟨eᵢ, Dφ(z)eᵢ⟩`, and the integral commutes with the sum and `⟨eᵢ, ·⟩`. -/
theorem Submission.codim1_rdo_dg_vdl_integral_divergence_eq_zero : ∀ (P : ℕ) (φ : Euclid P → Euclid P), ContDiff ℝ 1 φ → HasCompactSupport φ → ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 := by
  intro P φ hφ hsupp
  -- step 1: `Dφ` is continuous with compact support, `φ` is `M`-Lipschitz and integrable
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφc : Continuous φ := hφ.continuous
  have hDc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖fderiv ℝ φ z‖ ≤ M :=
    hDc.bounded_above_of_compact_support (hsupp.fderiv ℝ)
  have hlip : ∀ x y : Euclid P, ‖φ y - φ x‖ ≤ M * ‖y - x‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) (fun z _ => hM z)
      (mem_univ x) (mem_univ y)
  have hint : Integrable φ := hφc.integrable_of_hasCompactSupport hsupp
  -- step 2: `∫ Dφ(z) w dz = 0` for every `w`
  have key : ∀ w : Euclid P, ∫ z, fderiv ℝ φ z w = 0 := by
    intro w
    -- (a) the difference quotients `g_t` have integral zero, by translation invariance
    have ha : ∀ t : ℝ, ∫ z, t⁻¹ • (φ (z + t • w) - φ z) = 0 := fun t => by
      rw [integral_smul, integral_sub (hint.comp_add_right (t • w)) hint,
        integral_add_right_eq_self, sub_self, smul_zero]
    -- (b) `g_t(z) → Dφ(z) w` as `t → 0`, `t ≠ 0`
    have hb : ∀ z, Tendsto (fun t : ℝ => t⁻¹ • (φ (z + t • w) - φ z)) (𝓝[≠] 0)
        (𝓝 (fderiv ℝ φ z w)) := fun z => by
      have h : HasDerivAt (fun t : ℝ => φ (z + t • w)) (fderiv ℝ φ z w) 0 :=
        (hdiff z).hasFDerivAt.hasLineDerivAt w
      simpa only [zero_add, zero_smul, add_zero] using hasDerivAt_iff_tendsto_slope_zero.mp h
    -- (c) for `0 < |t| ≤ 1`, `‖g_t‖ ≤ M‖w‖ 1_{K'}` with `K' = cthickening ‖w‖ (tsupport φ)`
    have hK' : IsCompact (cthickening ‖w‖ (tsupport φ)) := hsupp.cthickening
    have h1 : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [closedBall_mem_nhds (0 : ℝ) one_pos] with t ht
      simpa using ht
    have hbound : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∀ᵐ z, ‖t⁻¹ • (φ (z + t • w) - φ z)‖ ≤
        (cthickening ‖w‖ (tsupport φ)).indicator (fun _ => M * ‖w‖) z := by
      filter_upwards [h1, self_mem_nhdsWithin] with t ht ht0
      have ht0' : t ≠ 0 := ht0
      refine ae_of_all _ fun z => ?_
      by_cases hz : z ∈ cthickening ‖w‖ (tsupport φ)
      · rw [indicator_of_mem hz, norm_smul, norm_inv, Real.norm_eq_abs]
        calc |t|⁻¹ * ‖φ (z + t • w) - φ z‖ ≤ |t|⁻¹ * (M * ‖z + t • w - z‖) :=
              mul_le_mul_of_nonneg_left (hlip z (z + t • w)) (inv_nonneg.mpr (abs_nonneg t))
          _ = M * ‖w‖ := by
              rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_left_comm,
                inv_mul_cancel_left₀ (abs_ne_zero.mpr ht0')]
      · -- outside `K'`, both `z` and `z + t • w` lie outside `tsupport φ`, so `g_t(z) = 0`
        have hz1 : z ∉ tsupport φ := fun h => hz (self_subset_cthickening _ h)
        have hz2 : z + t • w ∉ tsupport φ := fun h => hz <|
          mem_cthickening_of_dist_le z (z + t • w) ‖w‖ _ h <| by
            rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
            exact mul_le_of_le_one_left (norm_nonneg w) ht
        rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz1,
          image_eq_zero_of_notMem_tsupport hz2, sub_self, smul_zero, norm_zero]
    have hbound_int : Integrable ((cthickening ‖w‖ (tsupport φ)).indicator fun _ => M * ‖w‖) :=
      (integrableOn_const hK'.measure_lt_top.ne).integrable_indicator hK'.measurableSet
    -- (d) dominated convergence along `t → 0`, `t ≠ 0`; all the integrals vanish by (a)
    have hd := tendsto_integral_filter_of_dominated_convergence
      (F := fun (t : ℝ) (z : Euclid P) => t⁻¹ • (φ (z + t • w) - φ z)) _
      (Eventually.of_forall fun t =>
        (show Continuous fun z => t⁻¹ • (φ (z + t • w) - φ z) by fun_prop).aestronglyMeasurable)
      hbound hbound_int (ae_of_all _ hb)
    simp only [ha] at hd
    exact tendsto_nhds_unique hd tendsto_const_nhds
  -- step 3: `trace Dφ(z) = Σᵢ ⟨eᵢ, Dφ(z) eᵢ⟩`; integrate termwise
  have htr : ∀ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) =
      ∑ i, inner ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)
        (fderiv ℝ φ z (EuclideanSpace.basisFun (Fin P) ℝ i)) := fun z => by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    rfl
  have hcomp : ∀ v : Euclid P, Integrable (fun z => fderiv ℝ φ z v) := fun v =>
    (hDc.clm_apply continuous_const).integrable_of_hasCompactSupport (hsupp.fderiv_apply ℝ v)
  simp_rw [htr]
  rw [integral_finsetSum _ fun i _ => by
    simpa only [innerSL_apply_apply] using
      (innerSL ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)).integrable_comp (hcomp _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h := (innerSL ℝ (EuclideanSpace.basisFun (Fin P) ℝ i)).integral_comp_comm
    (hcomp (EuclideanSpace.basisFun (Fin P) ℝ i))
  simp only [innerSL_apply_apply] at h
  rw [h, key, inner_zero_right]

/-- **Simon Ch. 3, proof of 4.3, (11)** ("repeating the same argument with `U ∖ E` in place of
`E`", l. 729–732 of the chapter text): the Gauss–Green identity for `F` with normal `ν` gives the
one for `Fᶜ` with normal `−ν`.  The divergence `trace Dφ` of a `C¹` field with compact support is
continuous with compact support, hence integrable, and has integral `0`
(`codim1_rdo_dg_vdl_integral_divergence_eq_zero`).  So
`∫_{Fᶜ} trace Dφ = −∫_F trace Dφ = ∫ ⟨φ, ν⟩ dμ = −∫ ⟨φ, −ν⟩ dμ`. -/
theorem Submission.codim1_rdo_dg_vdl_gauss_green_compl : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P), MeasurableSet F → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in Fᶜ, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (-ν z) ∂μ := by
  intro P D F μ ν hF hGG φ hφ hφc hφD
  -- Step 2: `z ↦ trace Dφ(z)` is continuous with compact support, hence integrable
  have hf_int : Integrable fun z =>
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) := by
    -- `A ↦ trace A` is linear on the finite-dimensional space `ℝᴾ →L[ℝ] ℝᴾ`, hence continuous
    have htr : Continuous fun A : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) :=
      (LinearMap.trace ℝ (Euclid P) ∘ₗ
        ContinuousLinearMap.coeLM ℝ).continuous_of_finiteDimensional
    exact (htr.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hφc.fderiv ℝ).comp_left (by simp))
  -- Step 3: `∫_F trace Dφ + ∫_{Fᶜ} trace Dφ = ∫ trace Dφ = 0`
  have hsplit := integral_add_compl hF hf_int
  have hdiv : ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 :=
    Submission.codim1_rdo_dg_vdl_integral_divergence_eq_zero P φ hφ hφc
  have hF_GG := hGG φ hφ hφc hφD
  -- Step 4: `⟨φ, −ν⟩ = −⟨φ, ν⟩` and `∫ −g dμ = −∫ g dμ`
  simp only [inner_neg_right, integral_neg, neg_neg]
  linarith
/-- **Converging normal averages force positive mass on every ball** (step 2 of the lower volume
density bound in De Giorgi's argument for 7.5.8).  Let `A(ρ) = μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ`
(with `0⁻¹ = 0`).  If `A(ρ) → v ≠ 0` as `ρ ↓ 0`, then `μ(B̄_r(y)) ≠ 0` for every `r > 0`: some
`ρ ∈ (0, r)` has `A(ρ) ≠ 0`, while `μ(B̄_r(y)) = 0` would give `μ(B̄_ρ(y)) = 0` and so `A(ρ) = 0`. -/
theorem Submission.codim1_rdo_dg_vdl_measure_closedBall_ne_zero : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P), v ≠ 0 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0 := by
  intro P μ ν y v hv hlim r hr hμr
  -- Step 1: `A(ρ) → v ≠ 0`, so `A(ρ) ≠ 0` for all small `ρ > 0`
  have hA : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ ≠ 0 :=
    hlim.eventually_ne hv
  -- Step 2: pick `ρ ∈ (0, r)` with `A(ρ) ≠ 0`
  obtain ⟨ρ, hAρ, hρ⟩ := (hA.and (Ioo_mem_nhdsGT hr)).exists
  -- Step 3: `μ(B̄_ρ(y)) ≤ μ(B̄_r(y)) = 0` would force `A(ρ) = 0`
  have hμρ : μ (closedBall y ρ) = 0 := measure_mono_null (closedBall_subset_closedBall hρ.2.le) hμr
  rw [hμρ, ENNReal.toReal_zero, inv_zero, zero_smul] at hAρ
  exact hAρ rfl
/-- The `C¹` radial cut-off between `B̄_ρ(y)` and `B̄_{ρ+δ}(y)` (it replaces Simon's Lipschitz
cut-offs in Ch. 3, 4.3 (3)–(4)): `ζ = h ∘ a` with `a(z) = (|z - y| - ρ)/δ` and the clamped
smoothstep `h = p ∘ clamp_{[0,1]}`, `p(s) = 1 - 3s² + 2s³`.  As `p'(0) = p'(1) = 0`, `h` is `C¹`,
nonincreasing and `3/2`-Lipschitz, so `ζ` is `C¹`, `ζ = 1` on `B̄_ρ`, `tsupport ζ ⊆ B̄_{ρ+δ}`,
`‖Dζ‖ ≤ 3/(2δ)`, `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0, 1`), and
`{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = max {s ∈ [0, 1] | t ≤ h s} < 1`. -/
theorem Submission.codim1_rdo_dg_ce_radial_cutoff : ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ)) ∧ (∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
  intro P y ρ δ hρ hδ
  -- Steps 1–3: the profile `h = p ∘ cl`, `p(s) = 1 - 3s² + 2s³`, `cl(s) = max 0 (min s 1)`
  have profile : ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Antitone h ∧ (∀ s, 0 ≤ h s ∧ h s ≤ 1) ∧
      (∀ s, s ≤ 0 → h s = 1) ∧ (∀ s, 1 ≤ s → h s = 0) ∧ LipschitzWith (3 / 2 : NNReal) h := by
    set p : ℝ → ℝ := fun s => 1 - 3 * s ^ 2 + 2 * s ^ 3 with hp_def
    set cl : ℝ → ℝ := fun s => max 0 (min s 1) with hcl_def
    set h : ℝ → ℝ := fun s => p (cl s) with hh_def
    set q : ℝ → ℝ := fun s => -6 * cl s + 6 * cl s ^ 2 with hq_def
    have hp : ∀ s, HasDerivAt p (-6 * s + 6 * s ^ 2) s := by
      intro s
      have h1 := ((hasDerivAt_pow 2 s).const_mul 3).const_sub 1
      have h2 := (hasDerivAt_pow 3 s).const_mul 2
      convert h1.add h2 using 1
      push_cast
      ring
    have hcl0 : ∀ s, s ≤ 0 → cl s = 0 := fun s hs => by
      simp only [hcl_def]; exact max_eq_left (min_le_of_left_le hs)
    have hcl1 : ∀ s, 1 ≤ s → cl s = 1 := fun s hs => by
      simp only [hcl_def]; rw [min_eq_right hs]; exact max_eq_right zero_le_one
    have hclmid : ∀ s, 0 ≤ s → s ≤ 1 → cl s = s := fun s h0 h1 => by
      simp only [hcl_def]; rw [min_eq_left h1]; exact max_eq_right h0
    have hcl01 : ∀ s, 0 ≤ cl s ∧ cl s ≤ 1 := fun s =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    -- Step 2: `h' = q = p' ∘ cl` everywhere; at `0` and `1` the one-sided derivatives agree
    have hderiv : ∀ s, HasDerivAt h (q s) s := by
      intro s
      rcases lt_trichotomy s 0 with hs | hs | hs
      · have heq : h =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
          filter_upwards [Iio_mem_nhds hs] with u hu
          simp only [hh_def, hcl0 u (le_of_lt hu), hp_def]; norm_num
        have hq0 : q s = 0 := by simp only [hq_def, hcl0 s hs.le]; norm_num
        rw [hq0]; exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq heq
      · subst hs
        have hq0 : q 0 = 0 := by simp only [hq_def, hcl0 0 le_rfl]; norm_num
        rw [hq0]
        have hL : HasDerivWithinAt h 0 (Iic 0) 0 := by
          refine (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr (fun u hu => ?_) ?_
          · simp only [hh_def, hcl0 u hu, hp_def]; norm_num
          · simp only [hh_def, hcl0 0 le_rfl, hp_def]; norm_num
        have hR : HasDerivWithinAt h 0 (Ici 0) 0 := by
          have := (hp 0).hasDerivWithinAt (s := Ici 0)
          simp only [mul_zero, zero_pow two_ne_zero, add_zero] at this
          refine this.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ))
                (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
            simp only [hh_def, hclmid u hu.1 (le_of_lt hu.2)]
          · simp only [hh_def, hclmid 0 le_rfl zero_le_one]
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
        · have heq : h =ᶠ[𝓝 s] p := by
            filter_upwards [Ioo_mem_nhds hs hs1] with u hu
            simp only [hh_def, hclmid u hu.1.le hu.2.le]
          have hqs : q s = -6 * s + 6 * s ^ 2 := by simp only [hq_def, hclmid s hs.le hs1.le]
          rw [hqs]; exact (hp s).congr_of_eventuallyEq heq
        · subst hs1
          have hq0 : q 1 = 0 := by simp only [hq_def, hcl1 1 le_rfl]; norm_num
          rw [hq0]
          have hR : HasDerivWithinAt h 0 (Ici 1) 1 := by
            refine (hasDerivWithinAt_const (1 : ℝ) (Ici 1) (0 : ℝ)).congr (fun u hu => ?_) ?_
            · simp only [hh_def, hcl1 u hu, hp_def]; norm_num
            · simp only [hh_def, hcl1 1 le_rfl, hp_def]; norm_num
          have hL : HasDerivWithinAt h 0 (Iic 1) 1 := by
            have := (hp 1).hasDerivWithinAt (s := Iic 1)
            norm_num at this
            refine this.congr_of_eventuallyEq ?_ ?_
            · filter_upwards [inter_mem_nhdsWithin (Iic (1 : ℝ))
                  (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
              simp only [hh_def, hclmid u (le_of_lt hu.2) hu.1]
            · simp only [hh_def, hclmid 1 zero_le_one le_rfl]
          have := hL.union hR
          rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
        · have heq : h =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hs1] with u hu
            simp only [hh_def, hcl1 u (le_of_lt hu), hp_def]; norm_num
          have hq0 : q s = 0 := by simp only [hq_def, hcl1 s hs1.le]; norm_num
          rw [hq0]; exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
    -- Step 3: `h ∈ C¹`, `-3/2 ≤ h' ≤ 0`, so `h` is antitone and `3/2`-Lipschitz; `0 ≤ h ≤ 1`
    have hdiff : Differentiable ℝ h := fun s => (hderiv s).differentiableAt
    have hderiv_eq : deriv h = q := funext fun s => (hderiv s).deriv
    have hclcont : Continuous cl := by
      simp only [hcl_def]; fun_prop
    have hqcont : Continuous q := by
      simp only [hq_def]; fun_prop
    have hC1 : ContDiff ℝ 1 h := contDiff_one_iff_deriv.2 ⟨hdiff, hderiv_eq ▸ hqcont⟩
    have hq_nonpos : ∀ s, q s ≤ 0 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s; simp only [hq_def]; nlinarith
    have hq_abs : ∀ s, |q s| ≤ 3 / 2 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s
      rw [abs_of_nonpos (hq_nonpos s)]; simp only [hq_def]; nlinarith [sq_nonneg (cl s - 1 / 2)]
    have hanti : Antitone h := antitone_of_deriv_nonpos hdiff fun s => hderiv_eq ▸ hq_nonpos s
    refine ⟨h, hC1, hanti, ?_, ?_, ?_, ?_⟩
    · intro s; obtain ⟨h0, h1⟩ := hcl01 s
      simp only [hh_def, hp_def]
      have e1 : 1 - 3 * cl s ^ 2 + 2 * cl s ^ 3 = (1 - cl s) ^ 2 * (1 + 2 * cl s) := by ring
      constructor
      · rw [e1]; exact mul_nonneg (sq_nonneg _) (by linarith)
      · nlinarith [mul_nonneg (sq_nonneg (cl s)) (by linarith : (0 : ℝ) ≤ 3 - 2 * cl s)]
    · intro s hs; simp only [hh_def, hcl0 s hs, hp_def]; norm_num
    · intro s hs; simp only [hh_def, hcl1 s hs, hp_def]; norm_num
    · refine lipschitzWith_of_nnnorm_deriv_le hdiff fun s => ?_
      rw [hderiv_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
      simpa using hq_abs s
  obtain ⟨h, hC1, hanti, h01, h0, h1, hlip⟩ := profile
  -- Step 4: `ζ = h ∘ a`, `a(z) = (|z - y| - ρ)/δ`; `ζ = 1` on `B̄_ρ` and `ζ = 0` off `B_{ρ+δ}`
  set a : Euclid P → ℝ := fun z => (‖z - y‖ - ρ) / δ with ha_def
  set ζ : Euclid P → ℝ := fun z => h (a z) with hζ_def
  have hζ1 : ∀ z ∈ closedBall y ρ, ζ z = 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact h0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hζ0 : ∀ z, ρ + δ ≤ ‖z - y‖ → ζ z = 0 := by
    intro z hz
    refine h1 _ ?_
    rw [ha_def, le_div_iff₀ hδ]; linarith
  have hsupp : support ζ ⊆ ball y (ρ + δ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    by_contra hcon
    exact hz (hζ0 z (not_lt.1 hcon))
  have htsupp : tsupport ζ ⊆ closedBall y (ρ + δ) :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  have hcomp : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall y (ρ + δ)) fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (htsupp h'))
  -- Step 5: `ζ` is `C¹`: constant near points of `B_ρ`, a `C¹` composite where `z ≠ y`
  have hC1ζ : ContDiff ℝ 1 ζ := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : ‖z - y‖ < ρ
    · have heq : ζ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        have hmem : ball y ρ ∈ 𝓝 z :=
          isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; exact hz)
        filter_upwards [hmem] with u hu
        exact hζ1 u (ball_subset_closedBall hu)
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hzy : z - y ≠ 0 := by
        intro h0'; rw [h0', norm_zero] at hz; exact hz hρ
      have hn : ContDiffAt ℝ 1 (fun u : Euclid P => ‖u - y‖) z :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ hzy
      have ha' : ContDiffAt ℝ 1 a z := (hn.sub contDiffAt_const).div_const δ
      exact hC1.contDiffAt.comp z ha'
  -- Step 6: `ζ` is `3/(2δ)`-Lipschitz, hence `‖Dζ‖ ≤ 3/(2δ)`
  have hlipζ : LipschitzWith (Real.toNNReal (3 / (2 * δ))) ζ := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    have h1' := hlip.dist_le_mul (a z) (a w)
    have h2' : dist (a z) (a w) ≤ dist z w / δ := by
      rw [Real.dist_eq, ha_def]
      simp only
      rw [← sub_div, abs_div, abs_of_pos hδ, dist_eq_norm]
      gcongr
      calc |‖z - y‖ - ρ - (‖w - y‖ - ρ)| = |‖z - y‖ - ‖w - y‖| := by ring_nf
        _ ≤ ‖(z - y) - (w - y)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - w‖ := by abel_nf
    rw [Real.coe_toNNReal _ (by positivity)]
    calc dist (ζ z) (ζ w) ≤ (3 / 2 : NNReal) * dist (a z) (a w) := h1'
      _ ≤ (3 / 2 : ℝ) * (dist z w / δ) := by
          push_cast; gcongr
      _ = 3 / (2 * δ) * dist z w := by field_simp
  have hgrad : ∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ) := by
    intro z
    have := norm_fderiv_le_of_lipschitz ℝ hlipζ (x₀ := z)
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  -- Step 7: `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0` and `ζ = 1`)
  have hζle : ∀ z, ζ z ≤ 1 := fun z => (h01 _).2
  have hζge : ∀ z, 0 ≤ ζ z := fun z => (h01 _).1
  have hzero : ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
    intro z hz
    rw [Set.mem_sdiff, not_and_or, not_not] at hz
    rcases hz with hz | hz
    · rw [mem_ball, dist_eq_norm, not_lt] at hz
      have hmin : IsLocalMin ζ z := Eventually.of_forall fun u => by rw [hζ0 z hz]; exact hζge u
      exact hmin.fderiv_eq_zero
    · have hmax : IsLocalMax ζ z := Eventually.of_forall fun u => by rw [hζ1 z hz]; exact hζle u
      exact hmax.fderiv_eq_zero
  -- Step 8: `{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = sup M`, `M = {s ∈ [0, 1] | t ≤ h s}` compact
  have hlevel : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
    intro t ht0 ht1
    set M : Set ℝ := Icc 0 1 ∩ h ⁻¹' Ici t with hM
    have hMc : IsCompact M :=
      isCompact_Icc.inter_right (isClosed_Ici.preimage hC1.continuous)
    have hM0 : (0 : ℝ) ∈ M := ⟨⟨le_rfl, zero_le_one⟩, by simp [h0 0 le_rfl, ht1]⟩
    set st := sSup M with hst
    have hstM : st ∈ M := hMc.sSup_mem ⟨0, hM0⟩
    have hst0 : 0 ≤ st := hstM.1.1
    have hst1 : st < 1 := by
      rcases hstM.1.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have := hstM.2; rw [heq, mem_preimage, mem_Ici, h1 1 le_rfl] at this; linarith
    have hiff : ∀ u : ℝ, t ≤ h u ↔ u ≤ st := by
      intro u
      constructor
      · intro hu
        by_contra hcon
        push Not at hcon
        rcases le_or_gt u 1 with hu1 | hu1
        · have huM : u ∈ M := ⟨⟨hst0.trans hcon.le, hu1⟩, hu⟩
          exact absurd (le_csSup hMc.bddAbove huM) (not_le.2 hcon)
        · rw [h1 u hu1.le] at hu; linarith
      · intro hu
        exact le_trans hstM.2 (hanti hu)
    refine ⟨ρ + δ * st, by nlinarith, by nlinarith, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_eq_norm, hζ_def]
    rw [hiff, ha_def, div_le_iff₀ hδ]
    constructor <;> intro hh <;> linarith
  exact ⟨ζ, hC1ζ, hcomp, fun z => h01 _, hζ1, htsupp, hgrad, hzero, hlevel⟩
/-- **Signed layer cake** (Simon Ch. 3, 4.3 (4)–(5), the limit procedure of the De Giorgi cut-off
estimates): let `0 ≤ ζ ≤ 1` vanish off `S`, `μ(S) < ∞`, `ζ = 1` on `B`, `|g| ≤ 1` and `c ≥ 0`.  If
`c μ({ζ ≥ t}) ≤ ∫_{ζ ≥ t} g dμ` for every `t ∈ (0, 1]`, then `c μ(B) ≤ ∫ ζ g dμ`.

Proof sketch:
* `ζ(x) g(x) = ∫_{(0,1]} H(x, t) dt` with `H(x, t) = 1{t ≤ ζ(x)} g(x)`; `H` is bounded and
  measurable on the finite product `μ⌞S ⊗ λ⌞(0, 1]`, so Fubini swaps the two integrals.
* For `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`, so `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`;
  integrating over `(0, 1]` concludes. -/
theorem Submission.codim1_rdo_dg_ce_signed_layer_cake : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (ζ g : X → ℝ) (S B : Set X) (c : ℝ), Measurable ζ → Measurable g → (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) → (∀ x, |g x| ≤ 1) → MeasurableSet S → μ S ≠ ∞ → (∀ x, x ∉ S → ζ x = 0) → (∀ x ∈ B, ζ x = 1) → 0 ≤ c → (∀ t : ℝ, 0 < t → t ≤ 1 → c * (μ {x | t ≤ ζ x}).toReal ≤ ∫ x in {x | t ≤ ζ x}, g x ∂μ) → c * (μ B).toReal ≤ ∫ x, ζ x * g x ∂μ := by
  intro X _ μ ζ g S B c hζ hg hζ01 hg1 hS hSfin hζS hζB hc hlev
  -- the finite measures `μ⌞S` and `λ⌞(0, 1]`
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp)
  -- for `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`
  have hLS : ∀ t : ℝ, 0 < t → {x | t ≤ ζ x} ⊆ S := fun t ht x hx => by
    by_contra hxS
    have hx' : t ≤ ζ x := hx
    rw [hζS x hxS] at hx'
    linarith
  have hBL : ∀ t : ℝ, t ≤ 1 → B ⊆ {x | t ≤ ζ x} := fun t ht x hx => by
    show t ≤ ζ x
    rw [hζB x hx]
    exact ht
  -- the layer-cake integrand `H(x, t) = 1{t ≤ ζ(x)} g(x)` is integrable on `μ⌞S ⊗ λ⌞(0, 1]`
  set H : X → ℝ → ℝ := fun x t => if t ≤ ζ x then g x else 0 with hH
  have hHmeas : Measurable (uncurry H) :=
    Measurable.ite (measurableSet_le measurable_snd (hζ.comp measurable_fst))
      (hg.comp measurable_fst) measurable_const
  have hHint : Integrable (uncurry H) ((μ.restrict S).prod ν) := by
    refine Integrable.of_bound hHmeas.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hH]
    split_ifs
    · simpa [Real.norm_eq_abs] using hg1 p.1
    · simp
  -- inner integral in `t`: `∫_{(0,1]} H(x, t) dt = λ((0, ζ(x)]) g(x) = ζ(x) g(x)`
  have hinner : ∀ x, ∫ t, H x t ∂ν = ζ x * g x := by
    intro x
    have : (fun t => H x t) = (Iic (ζ x)).indicator (fun _ => g x) := by
      funext t; simp [hH, indicator_apply, mem_Iic]
    rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, hν, Measure.real,
      Measure.restrict_apply measurableSet_Iic]
    have hset : Iic (ζ x) ∩ Ioc (0 : ℝ) 1 = Ioc 0 (ζ x) := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans (hζ01 x).2⟩
    rw [hset, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (hζ01 x).1]
  -- `ζ g` vanishes off `S`, so `∫ ζ g dμ = ∫∫ H dt dμ⌞S`
  have hleft : ∫ x, ζ x * g x ∂μ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := by
    simp_rw [hinner]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hζS x hx]
  -- for `t ∈ (0, 1]`: `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`
  have hlow : ∀ t ∈ Ioc (0 : ℝ) 1, c * (μ B).toReal ≤ ∫ x, H x t ∂(μ.restrict S) := by
    intro t ht
    have hLmeas : MeasurableSet {x | t ≤ ζ x} := measurableSet_le measurable_const hζ
    have : (fun x => H x t) = {x | t ≤ ζ x}.indicator g := by
      funext x; simp [hH, indicator_apply]
    rw [this, integral_indicator hLmeas, Measure.restrict_restrict hLmeas,
      inter_eq_left.2 (hLS t ht.1)]
    refine le_trans ?_ (hlev t ht.1 ht.2)
    have hLfin : μ {x | t ≤ ζ x} ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono (hLS t ht.1))
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hLfin (measure_mono (hBL t ht.2))) hc
  have hint_t : Integrable (fun t => ∫ x, H x t ∂(μ.restrict S)) ν := hHint.integral_prod_right
  calc c * (μ B).toReal = ∫ t, c * (μ B).toReal ∂ν := by
        simp [hν, Measure.real]
    _ ≤ ∫ t, ∫ x, H x t ∂(μ.restrict S) ∂ν := by
        refine integral_mono_ae (integrable_const _) hint_t ?_
        rw [hν, EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall hlow
    _ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := (integral_integral_swap hHint).symm
    _ = ∫ x, ζ x * g x ∂μ := hleft.symm
/-- The divergence theorem for compactly supported fields (step 6 of the cut-off estimates in the
De Giorgi argument, cf. Simon Ch. 3, 4.3): if `φ : ℝᴾ → ℝᴾ` is `C¹` with compact support, then
`div φ = trace Dφ = ∑ᵢ ∂ᵢφⁱ` is integrable and `∫ div φ dLᴾ = ∑ᵢ ∫ ∂ᵢφⁱ dLᴾ = 0`. -/
theorem Submission.codim1_rdo_dg_ce_integral_div_eq_zero : ∀ (P : ℕ) (φ : Euclid P → Euclid P), ContDiff ℝ 1 φ → HasCompactSupport φ → Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) ∧ ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 := by
  intro P φ hφ hφc
  set b := EuclideanSpace.basisFun (Fin P) ℝ with hb
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- the coordinate functions `φⁱ = ⟪bᵢ, φ⟫` are `C¹` with compact support
  set f : Fin P → Euclid P → ℝ := fun i w => innerSL ℝ (b i) (φ w) with hf
  have hfC : ∀ i, ContDiff ℝ 1 (f i) := fun i => (innerSL ℝ (b i)).contDiff.comp hφ
  have hfcs : ∀ i, HasCompactSupport (f i) := fun i => hφc.comp_left (map_zero _)
  have hfder : ∀ i z, fderiv ℝ (f i) z = (innerSL ℝ (b i)).comp (fderiv ℝ φ z) := by
    intro i z
    exact ((innerSL ℝ (b i)).hasFDerivAt.comp z (hdiff z).hasFDerivAt).fderiv
  -- `trace Dφ(z) = ∑ᵢ ⟪bᵢ, Dφ(z) bᵢ⟫ = ∑ᵢ ∂ᵢφⁱ(z)`
  have hcoord : ∀ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) =
      ∑ i, fderiv ℝ (f i) z (b i) := by
    intro z
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfder]
    simp [innerSL_apply_apply]
  -- each `∂ᵢφⁱ` is continuous and vanishes off `tsupport φⁱ`, hence integrable
  have hint_i : ∀ i, Integrable (fun z => fderiv ℝ (f i) z (b i)) := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hfC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    · refine (hfcs i).mono' ?_
      intro z hz
      refine support_fderiv_subset ℝ ?_
      intro h0
      exact hz (by simp [h0])
  -- `∫ ∂ᵢφⁱ = 0`: integrate by parts against the constant function `1`
  have hzero_i : ∀ i, ∫ z, fderiv ℝ (f i) z (b i) = 0 := by
    intro i
    obtain ⟨C, hC⟩ := (hfC i).lipschitzWith_of_hasCompactSupport (hfcs i) one_ne_zero
    have h1 := (LipschitzWith.const (1 : ℝ) : LipschitzWith 0 (fun _ : Euclid P => (1 : ℝ))).integral_lineDeriv_mul_eq
      (μ := (volume : Measure (Euclid P))) hC (hfcs i) (b i)
    have hl : ∀ x, lineDeriv ℝ (f i) x (-b i) = -fderiv ℝ (f i) x (b i) := by
      intro x
      rw [(((hfC i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
    have hc : ∀ x, lineDeriv ℝ (fun _ : Euclid P => (1 : ℝ)) x (b i) = 0 := by
      intro x
      simp [lineDeriv]
    simp only [hc, zero_mul, integral_zero, mul_one, hl, integral_neg] at h1
    linarith
  have hint : Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) := by
    simp_rw [hcoord]
    exact integrable_finsetSum _ fun i _ => hint_i i
  refine ⟨hint, ?_⟩
  simp_rw [hcoord]
  rw [integral_finsetSum _ fun i _ => hint_i i]
  exact Finset.sum_eq_zero fun i _ => hzero_i i
/-- **Normal averages close to a unit vector** (quantitative form of Simon Ch. 3, 4.3 (1)).  Let
`μ(B̄_{ρ₀}(y)) < ∞`, `ν` be measurable with `|ν| ≤ 1`, `|v| = 1`, and
`A(ρ) := μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ → v` as `ρ ↓ 0`.  Then for some `ρ₂ ∈ (0, ρ₀]`,
`∫_{B̄_r(y)} ⟨ν, v⟩ dμ ≥ ½ μ(B̄_r(y))` whenever `0 < r < ρ₂`.  Since `⟨A(r), v⟩ → |v|² = 1`, we have
`⟨A(r), v⟩ > ½` for `r ∈ (0, ε)`; take `ρ₂ = min ε ρ₀`.  For `0 < r < ρ₂`, `ν` is integrable on
`B̄_r(y)` (bounded, finite measure), so `∫⟨ν, v⟩ = ⟨∫ν, v⟩`.  Either `μ(B̄_r(y)) = 0` and both sides
vanish, or `∫ν = μ(B̄_r(y)) A(r)` and `∫⟨ν, v⟩ = μ(B̄_r(y)) ⟨A(r), v⟩ ≥ ½ μ(B̄_r(y))`. -/
theorem Submission.codim1_rdo_dg_ce_normal_average_lower : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₀ : ℝ), 0 < ρ₀ → μ (closedBall y ρ₀) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ ρ₀ ∧ ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ := by
  intro P μ ν y v ρ₀ hρ₀ hfin hν hν1 hv hT
  -- step 1: `⟨A(ρ), v⟩ → ⟨v, v⟩ = 1`, so `⟨A(ρ), v⟩ > ½` for `ρ ∈ (0, ε)`
  have hT' : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 (inner ℝ v v)) :=
    hT.inner tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq, hv, one_pow] at hT'
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hT'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  -- step 2: `ρ₂ = min ε ρ₀`; for `r < ρ₂`, `μ(B̄_r(y)) ≤ μ(B̄_{ρ₀}(y)) < ∞`
  refine ⟨min ε ρ₀, lt_min hε hρ₀, min_le_right _ _, fun r hr hr₂ => ?_⟩
  have hkey : (1 / 2 : ℝ) < inner ℝ ((μ (closedBall y r)).toReal⁻¹ •
      ∫ z in closedBall y r, ν z ∂μ) v :=
    hεsub ⟨hr, hr₂.trans_le (min_le_left _ _)⟩
  have hBfin : μ (closedBall y r) ≠ ∞ := ne_top_of_le_ne_top hfin
    (measure_mono (closedBall_subset_closedBall (hr₂.trans_le (min_le_right _ _)).le))
  -- step 3: `ν` is integrable on `B̄_r(y)`, and `∫⟨ν, v⟩ = ⟨∫ν, v⟩`
  have hint : IntegrableOn ν (closedBall y r) μ :=
    Measure.integrableOn_of_bounded hBfin hν.aestronglyMeasurable (Eventually.of_forall hν1)
  have hcomm : ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ =
      inner ℝ (∫ z in closedBall y r, ν z ∂μ) v := by
    simpa only [innerSL_apply_apply, real_inner_comm v] using
      (innerSL ℝ v).integral_comp_comm hint
  -- step 4: if `μ(B̄_r(y)) = 0`, both sides vanish
  by_cases hμ0 : μ (closedBall y r) = 0
  · rw [hμ0, ENNReal.toReal_zero, mul_zero, setIntegral_measure_zero _ hμ0]
  -- step 5: otherwise `∫ν = a A(r)` with `a = μ(B̄_r(y)) > 0`, so `∫⟨ν, v⟩ = a ⟨A(r), v⟩ ≥ a / 2`
  have hpos : 0 < (μ (closedBall y r)).toReal := ENNReal.toReal_pos hμ0 hBfin
  have hI : ∫ z in closedBall y r, ν z ∂μ = (μ (closedBall y r)).toReal •
      ((μ (closedBall y r)).toReal⁻¹ • ∫ z in closedBall y r, ν z ∂μ) := by
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [hcomm, hI, real_inner_smul_left]
  nlinarith

/-- Annular bound behind De Giorgi's cut-off estimates (Simon Ch. 3, 4.3 (3)–(6), in
finite-difference form, as used for 7.5.8).  Suppose `F` satisfies the Gauss–Green identity
`∫_F div φ dLᴾ = -∫ ⟨φ, ν⟩ dμ` for `C¹` fields `φ` with compact support in `D ⊇ B̄_{ρ₂}(y)`
(`|ν| ≤ 1`, `μ(B̄_{ρ₂}(y)) < ∞`), and `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂`
(`|v| ≤ 1`).  Then `δ μ(B̄_ρ(y)) ≤ 3 Lᴾ(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0` and
`ρ + δ < ρ₂`.  Test the identity with `φ = ζ v`, `ζ` the radial cut-off
`Submission.codim1_rdo_dg_ce_radial_cutoff`: `div φ = Dζ v` vanishes off the annulus and is
bounded by `3/(2δ)`, while the signed layer-cake formula
`Submission.codim1_rdo_dg_ce_signed_layer_cake` over the superlevel balls `{ζ ≥ t} = B̄_r(y)`
gives `∫ ζ ⟨v, ν⟩ dμ ≥ ½ μ(B̄_ρ(y))`. -/
theorem Submission.codim1_rdo_dg_ce_annular_bound : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₂ : ℝ), MeasurableSet F → closedBall y ρ₂ ⊆ D → μ (closedBall y ρ₂) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ ≤ 1 → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → (∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ) → ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₂ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) := by
  intro P D F μ ν y v ρ₂ _hF hD hfin hν hν1 hv hGG h1' ρ δ hρ hδ hρδ
  set A := ball y (ρ + δ) \ closedBall y ρ
  -- Step 1: `μ(B̄_ρ) ≤ μ(B̄_{ρ+δ}) ≤ μ(B̄_{ρ₂}) < ∞` and `Lᴾ(F ∩ A) ≤ Lᴾ(B_{ρ+δ}) < ∞`.
  have hSsub : closedBall y (ρ + δ) ⊆ closedBall y ρ₂ := closedBall_subset_closedBall hρδ.le
  have hSfin : μ (closedBall y (ρ + δ)) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hSsub)
  have hBfin : μ (closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hSfin (measure_mono (closedBall_subset_closedBall (by linarith)))
  have hAmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hAfin : volume A ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hFAfin : volume (F ∩ A) ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_right)
  -- Step 2: the radial cut-off `ζ`, `= 1` on `B̄_ρ`, supported in `B̄_{ρ+δ}`, `|Dζ| ≤ 3/(2δ)`.
  obtain ⟨ζ, hζC, hζc, hζ01, hζ1, hζsupp, hζgrad, hζzero, hζlevel⟩ :=
    Submission.codim1_rdo_dg_ce_radial_cutoff P y ρ δ hρ hδ
  -- Step 3: Gauss–Green for `φ = ζ v`, whose divergence is the trace `Dζ v` of the rank-one
  -- map `Dφ = Dζ ⊗ v`: `∫ ζ ⟨v, ν⟩ dμ = -∫_F Dζ v dLᴾ`.
  have hφD : tsupport (fun z => ζ z • v) ⊆ D :=
    (tsupport_smul_subset_left _ _).trans (hζsupp.trans (hSsub.trans hD))
  have htrace : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • v) z : Euclid P →ₗ[ℝ] Euclid P) = fderiv ℝ ζ z v := by
    intro z
    rw [fderiv_smul_const ((hζC.differentiable one_ne_zero) z) v]
    exact LinearMap.trace_smulRight _ _
  have hGGζ : ∫ z, ζ z * inner ℝ v (ν z) ∂μ = -∫ z in F, fderiv ℝ ζ z v := by
    have h := hGG (fun z => ζ z • v) (hζC.smul contDiff_const) hζc.smul_right hφD
    simp only [htrace, real_inner_smul_left] at h
    rw [h, neg_neg]
  -- Step 4: `|Dζ v| ≤ (3/(2δ)) 𝟙_A`, so `-∫_F Dζ v dLᴾ ≤ (3/(2δ)) Lᴾ(F ∩ A)`.
  have hpt : ∀ z, ‖fderiv ℝ ζ z v‖ ≤ A.indicator (fun _ => 3 / (2 * δ)) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      calc ‖fderiv ℝ ζ z v‖ ≤ ‖fderiv ℝ ζ z‖ * ‖v‖ := (fderiv ℝ ζ z).le_opNorm v
        _ ≤ 3 / (2 * δ) * 1 := mul_le_mul (hζgrad z) hv (norm_nonneg _) (by positivity)
        _ = 3 / (2 * δ) := mul_one _
    · rw [indicator_of_notMem hz, hζzero z hz]
      simp
  have hup : -∫ z in F, fderiv ℝ ζ z v ≤ 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
    have hint : Integrable (A.indicator (fun _ => 3 / (2 * δ))) (volume.restrict F) :=
      ((integrableOn_const hAfin).integrable_indicator hAmeas).restrict
    have heq : ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z =
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      rw [integral_indicator_const _ hAmeas, smul_eq_mul, mul_comm]
      congr 1
      simp only [Measure.real, Measure.restrict_apply hAmeas, inter_comm]
    calc -∫ z in F, fderiv ℝ ζ z v ≤ ‖∫ z in F, fderiv ℝ ζ z v‖ := by
          rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = 3 / (2 * δ) * (volume (F ∩ A)).toReal := heq
  -- Step 5: the signed layer-cake formula with `g = ⟨v, ν⟩`, `S = B̄_{ρ+δ}`, `B = B̄_ρ`, `c = ½`;
  -- each `{ζ ≥ t} = B̄_r` has `0 < ρ ≤ r < ρ + δ < ρ₂`, where `(1′)` applies.
  have hg : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hν
  have hlow : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤ ∫ z, ζ z * inner ℝ v (ν z) ∂μ := by
    refine Submission.codim1_rdo_dg_ce_signed_layer_cake (Euclid P) μ ζ (fun z => inner ℝ v (ν z))
      (closedBall y (ρ + δ)) (closedBall y ρ) (1 / 2) hζC.continuous.measurable hg hζ01 ?_
      measurableSet_closedBall hSfin ?_ hζ1 (by norm_num) ?_
    · intro z
      calc |inner ℝ v (ν z)| ≤ ‖v‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul hv (hν1 z) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · intro z hz
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hζsupp h))
    · intro t ht0 ht1
      obtain ⟨r, hr1, hr2, hrset⟩ := hζlevel t ht0 ht1
      rw [hrset]
      simpa only [real_inner_comm] using h1' r (by linarith) (by linarith)
  -- Step 6: `½ μ(B̄_ρ) ≤ (3/(2δ)) Lᴾ(F ∩ A)`; multiply by `2δ > 0`.
  have hreal : δ * (μ (closedBall y ρ)).toReal ≤ 3 * (volume (F ∩ A)).toReal := by
    have key : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      linarith
    have h3 : 3 / (2 * δ) * (volume (F ∩ A)).toReal * (2 * δ) = 3 * (volume (F ∩ A)).toReal := by
      field_simp
    nlinarith [key, hδ]
  -- Step 7: back to `[0, ∞]`, both measures being finite by step 1.
  calc ENNReal.ofReal δ * μ (closedBall y ρ)
      = ENNReal.ofReal (δ * (μ (closedBall y ρ)).toReal) := by
        rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hBfin]
    _ ≤ ENNReal.ofReal (3 * (volume (F ∩ A)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 3 * volume (F ∩ A) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hFAfin]

/-- **Cut-off estimates** of Simon Ch. 3, proof of Theorem 4.3, (1) and (3)–(6), in
finite-difference form, at a point `y` where the normal averages of the Gauss–Green measure `μ`
tend to a unit vector `v`.  `codim1_rdo_dg_ce_normal_average_lower` gives `0 < ρ₂ ≤ ρ₀`, with
`B̄_{ρ₀}(y) ⊆ D`, such that `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂` (printed (1)).
`codim1_rdo_dg_ce_annular_bound` (the cut-off and layer-cake argument of (3)–(5)) then gives
`δ μ(B̄_ρ(y)) ≤ 3 L(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` for `ρ + δ < ρ₂`.  Since `∫ div φ = 0`
(`codim1_rdo_dg_ce_integral_div_eq_zero`), `Fᶜ` satisfies the Gauss–Green identity with `−ν`, and
`(−ν, −v)` satisfies the same lower bound, so the annular bound also holds for `Fᶜ`.  Taking
`δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}` gives `μ(B̄_ρ(y)) ≤ 3·2^{m+1} ω_{m+1} ρ^m`
(printed (6)).  Finally `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`. -/
theorem Submission.codim1_rdo_dg_cutoff_estimates : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ 0 ≤ C ∧ closedBall y ρ₁ ⊆ D ∧ (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) ∧ ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume ((ball y (ρ + δ) \ closedBall y ρ) \ F)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ m) := by
  intro m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 1: a radius `ρ₀` with `B̄_{ρ₀}(y) ⊆ D`, and `ρ₂ ≤ ρ₀` below which (1′) holds
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD y hy
  have hρ₀D : closedBall y (ε / 2) ⊆ D := (closedBall_subset_ball (half_lt_self hε)).trans hεD
  have hρ₀fin : μ (closedBall y (ε / 2)) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₀D
  obtain ⟨ρ₂, hρ₂pos, hρ₂le, h1'⟩ := Submission.codim1_rdo_dg_ce_normal_average_lower (m + 1) μ ν
    y v (ε / 2) (half_pos hε) hρ₀fin hν (fun z => (hν1 z).le) hv hT
  have hρ₂D : closedBall y ρ₂ ⊆ D := (closedBall_subset_closedBall hρ₂le).trans hρ₀D
  have hρ₂fin : μ (closedBall y ρ₂) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₂D
  -- steps 2–5: the annular bound for `F`
  have hA1 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D F μ ν y v ρ₂ hF hρ₂D hρ₂fin hν
    (fun z => (hν1 z).le) hv.le hGG h1'
  -- step 6: `Fᶜ` satisfies (GG) with `−ν` because `∫ div φ = 0`, and (1′) holds for `(−ν, −v)`,
  -- so the annular bound also holds for `Fᶜ`
  have hGGc : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ D → ∫ z in Fᶜ, LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (-ν z) ∂μ := by
    intro φ hφ hφc hφD
    obtain ⟨hint, hzero⟩ := Submission.codim1_rdo_dg_ce_integral_div_eq_zero (m + 1) φ hφ hφc
    have hsplit := integral_add_compl hF hint
    rw [hzero, hGG φ hφ hφc hφD] at hsplit
    simp only [inner_neg_right, integral_neg, neg_neg]
    linarith
  have h1'c : ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤
      ∫ z in closedBall y r, inner ℝ (-ν z) (-v) ∂μ := by
    intro r hr hr2
    simpa only [inner_neg_neg] using h1' r hr hr2
  have hA2 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D Fᶜ μ (fun z => -ν z) y (-v) ρ₂
    hF.compl hρ₂D hρ₂fin hν.neg (fun z => by simpa using (hν1 z).le) (by simpa using hv.le) hGGc
    h1'c
  -- step 8: `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`, where `ω_{m+1} = L(B₁(0))`
  set ω : ℝ := (volume (ball (0 : Euclid (m + 1)) 1)).toReal with hω
  have hωeq : volume (ball (0 : Euclid (m + 1)) 1) = ENNReal.ofReal ω := by
    rw [hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  refine ⟨ρ₂ / 2, max 3 (3 * 2 ^ (m + 1) * ω), half_pos hρ₂pos, le_max_of_le_left (by norm_num),
    (closedBall_subset_closedBall (half_le_self hρ₂pos.le)).trans hρ₂D, ?_, ?_⟩
  -- the annular bounds of steps 5–6 hold below `ρ₁ < ρ₂`, and `3 ≤ C`
  · intro ρ δ hρ hδ hρδ
    have hlt : ρ + δ < ρ₂ := by linarith
    have hC : ENNReal.ofReal 3 ≤ ENNReal.ofReal (max 3 (3 * 2 ^ (m + 1) * ω)) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hset : Fᶜ ∩ (ball y (ρ + δ) \ closedBall y ρ) = (ball y (ρ + δ) \ closedBall y ρ) \ F := by
      ext z; simp [and_comm]
    have h2 := hA2 ρ δ hρ hδ hlt
    rw [hset] at h2
    exact ⟨(hA1 ρ δ hρ hδ hlt).trans (mul_le_mul_left hC _), h2.trans (mul_le_mul_left hC _)⟩
  -- step 7: `δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}`
  · intro ρ hρ hρ1
    have hvol : volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤
        ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
      calc volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤ volume (ball y (ρ + ρ)) :=
            measure_mono (inter_subset_right.trans sdiff_subset)
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1)) * volume (ball (0 : Euclid (m + 1)) 1) := by
            rw [Measure.addHaar_ball _ _ (by linarith), finrank_euclideanSpace_fin]
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
            rw [hωeq, ENNReal.ofReal_mul (by positivity)]
    have key : ENNReal.ofReal ρ * μ (closedBall y ρ) ≤
        ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
      calc ENNReal.ofReal ρ * μ (closedBall y ρ)
          ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) :=
            hA1 ρ ρ hρ hρ (by linarith)
        _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := mul_le_mul_right hvol _
        _ = ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hρ.le]
            congr 1
            ring
    have hρne : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
    refine ((ENNReal.mul_le_mul_iff_right hρne ENNReal.ofReal_ne_top).mp key).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
/-- **Real-integral form of a lower-integral Gagliardo–Nirenberg–Sobolev inequality** (Simon
Ch. 3, proof of Theorem 4.3 (De Giorgi), Sobolev step, chapter-03.txt lines 689–712; the bound
`(H)` below has the shape of Mathlib's `lintegral_pow_le_pow_lintegral_fderiv`).  If every `C¹`
compactly supported `w : ℝᴾ → ℝ` satisfies `∫⁻ ‖w‖ₑ^p ≤ C (∫⁻ ‖Dw‖ₑ)^p`, then with
`c = C^{1/p} + 1 > 0` every such `w` satisfies `(∫ |w|^p)^{1/p} ≤ c ∫ |Dw|`: `Dw` is continuous
with compact support, so `∫⁻ ‖Dw‖ₑ < ∞`; both Bochner integrals are the `toReal` of the lower
integrals, `(H)` passes to `toReal`, and `t ↦ t^{1/p}` is monotone on `[0, ∞)`. -/
theorem Submission.codim1_rdo_dg_sp_gns_real_of_lintegral : ∀ (P : ℕ) (p : ℝ) (C : NNReal), 0 < p → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → ∫⁻ x, ‖w x‖ₑ ^ p ≤ (C : ℝ≥0∞) * (∫⁻ x, ‖fderiv ℝ w x‖ₑ) ^ p) → ∃ c : ℝ, 0 < c ∧ ∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖ := by
  intro P p C hp hH
  -- Step 1: `c = C^{1/p} + 1 > 0`
  refine ⟨(C : ℝ) ^ p⁻¹ + 1, by positivity, ?_⟩
  intro w hw hcs
  -- Step 2: `Dw` is continuous with compact support, so `∫⁻ ‖Dw‖ₑ < ∞` and
  -- `∫ |Dw| = (∫⁻ ‖Dw‖ₑ).toReal`
  have hDcont : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hDint : Integrable (fderiv ℝ w) := hDcont.integrable_of_hasCompactSupport (hcs.fderiv ℝ)
  have hAfin : (∫⁻ x, ‖fderiv ℝ w x‖ₑ) ≠ ∞ := hDint.hasFiniteIntegral.ne
  have hA : ∫ z, ‖fderiv ℝ w z‖ = (∫⁻ x, ‖fderiv ℝ w x‖ₑ).toReal :=
    integral_norm_eq_lintegral_enorm hDcont.aestronglyMeasurable
  -- Step 3: `|w|^p` is continuous and nonnegative, and `ofReal (|w x|^p) = ‖w x‖ₑ^p`, so
  -- `∫ |w|^p = (∫⁻ ‖w‖ₑ^p).toReal`
  have hF : ∫ z, |w z| ^ p = (∫⁻ x, ‖w x‖ₑ ^ p).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (w z)) p)
      ((hw.continuous.abs.rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  -- Step 4: take `toReal` in `(H)`, whose right side `C · (∫⁻ ‖Dw‖ₑ)^p` is finite
  have h4 : ∫ z, |w z| ^ p ≤ (C : ℝ) * (∫ z, ‖fderiv ℝ w z‖) ^ p := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.rpow_ne_top_of_nonneg hp.le hAfin))
      (hH w hw hcs)
    rwa [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal, ← hF, ← hA] at h
  -- Step 5: take the `1/p` power: `(C I^p)^{1/p} = C^{1/p} I ≤ c I`
  have hI : 0 ≤ ∫ z, ‖fderiv ℝ w z‖ := integral_nonneg fun z => norm_nonneg _
  have hL : 0 ≤ ∫ z, |w z| ^ p := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg (w z)) p
  calc (∫ z, |w z| ^ p) ^ p⁻¹ ≤ ((C : ℝ) * (∫ z, ‖fderiv ℝ w z‖) ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow hL h4 (inv_nonneg.2 hp.le)
    _ = (C : ℝ) ^ p⁻¹ * ∫ z, ‖fderiv ℝ w z‖ := by
        rw [Real.mul_rpow C.coe_nonneg (Real.rpow_nonneg hI p), Real.rpow_rpow_inv hI hp.ne']
    _ ≤ ((C : ℝ) ^ p⁻¹ + 1) * ∫ z, ‖fderiv ℝ w z‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hI
/-- **Variation of `1_F ζ` from the Gauss–Green identity** (Simon Ch. 3, proof of Theorem 4.3
(De Giorgi), chapter-03.txt lines 689–712: `|D(ζ 1_F)| ≤ ζ |D1_F| + 1_F |Dζ|`, in dual form).  If
`∫_F div φ = -∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly supported `φ` with `tsupport φ ⊆ D`, `|ν| = 1`
and `μ` is finite on compact subsets of `D`, then for `ζ ≥ 0` `C¹` with compact support in `D` and
`g` `C¹` compactly supported with `|g| ≤ 1`, `|∫ 1_F ζ div g| ≤ ∫ ζ dμ + ∫_F |Dζ|`.  Apply (GG) to
`φ = ζ g`: `div (ζ g) = ζ div g + Dζ(g)` (the trace of `v ↦ Dζ(v) g` is `Dζ(g)`), and bound
`|⟨ζ g, ν⟩| ≤ ζ` and `|Dζ(g)| ≤ |Dζ|`. -/
theorem Submission.codim1_rdo_dg_sp_gauss_green_variation : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → ∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, F.indicator ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ ∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖ := by
  intro P D F μ ν _ hF _ hμK _ hν1 hGG ζ hζ hζc hζD hζ0 g hg _ hg1
  -- Step 1: the test field `φ = ζ g` satisfies the hypotheses of (GG)
  have hsupp : support (fun z => ζ z • g z) ⊆ support ζ := fun z hz h0 => hz (by simp [h0])
  have hGGφ := hGG (fun z => ζ z • g z) (hζ.smul hg) (hζc.mono hsupp)
    ((closure_mono hsupp).trans hζD)
  -- Step 2: `div (ζ g) = ζ div g + Dζ(g)`
  have hdiv : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • g z) z : Euclid P →ₗ[ℝ] Euclid P) =
      ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) +
        fderiv ℝ ζ z (g z) := by
    intro z
    rw [fderiv_fun_smul ((hζ.differentiable one_ne_zero) z) ((hg.differentiable one_ne_zero) z),
      ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul,
      smul_eq_mul]
    congr 1
    exact LinearMap.trace_smulRight (fderiv ℝ ζ z : Euclid P →ₗ[ℝ] ℝ) (g z)
  -- Step 3: integrability with respect to Lebesgue measure
  have hdivg : Continuous fun z =>
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) :=
    ((LinearMap.trace ℝ (Euclid P)).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
      (hg.continuous_fderiv one_ne_zero)
  have hI1 : Integrable (fun z =>
      ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)) :=
    (hζ.continuous.mul hdivg).integrable_of_hasCompactSupport hζc.mul_right
  have hI2 : Integrable (fun z => fderiv ℝ ζ z (g z)) :=
    ((hζ.continuous_fderiv one_ne_zero).clm_apply hg.continuous).integrable_of_hasCompactSupport
      ((hζc.fderiv ℝ).mono fun z hz h0 => hz (by simp [h0]))
  have hI3 : Integrable (fun z => ‖fderiv ℝ ζ z‖) :=
    (hζ.continuous_fderiv one_ne_zero).norm.integrable_of_hasCompactSupport (hζc.fderiv ℝ).norm
  -- Step 4: rewriting the left side
  have hkey : ∫ z, F.indicator ζ z *
      LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) =
      -∫ z, inner ℝ (ζ z • g z) (ν z) ∂μ - ∫ z in F, fderiv ℝ ζ z (g z) := by
    have h1 : ∫ z, F.indicator ζ z *
        LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) =
        ∫ z in F, ζ z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_indicator hF]
      congr 1
      ext z
      by_cases hz : z ∈ F <;> simp [hz]
    have h2 := hGGφ
    simp only [hdiv] at h2
    rw [integral_add hI1.integrableOn hI2.integrableOn] at h2
    rw [h1]
    linarith
  -- Step 5: `ζ` is `μ`-integrable
  have hζμ : Integrable ζ μ := by
    have : IsFiniteMeasure (μ.restrict (tsupport ζ)) := isFiniteMeasure_restrict.2 (hμK _ hζc hζD)
    exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport ζ)).1
      (hζ.continuous.integrable_of_hasCompactSupport hζc)
  -- Step 6: pointwise bounds
  have hb1 : ∀ z, ‖inner ℝ (ζ z • g z) (ν z)‖ ≤ ζ z := by
    intro z
    calc ‖inner ℝ (ζ z • g z) (ν z)‖ ≤ ‖ζ z • g z‖ * ‖ν z‖ := norm_inner_le_norm _ _
      _ = ζ z * ‖g z‖ := by rw [hν1, mul_one, norm_smul, Real.norm_of_nonneg (hζ0 z)]
      _ ≤ ζ z * 1 := mul_le_mul_of_nonneg_left (hg1 z) (hζ0 z)
      _ = ζ z := mul_one _
  have hb2 : ∀ z, ‖fderiv ℝ ζ z (g z)‖ ≤ ‖fderiv ℝ ζ z‖ := fun z =>
    ((fderiv ℝ ζ z).le_opNorm (g z)).trans (mul_le_of_le_one_right (norm_nonneg _) (hg1 z))
  -- Step 7: conclusion
  have hA : |∫ z, inner ℝ (ζ z • g z) (ν z) ∂μ| ≤ ∫ z, ζ z ∂μ :=
    norm_integral_le_of_norm_le hζμ (Eventually.of_forall hb1)
  have hB : |∫ z in F, fderiv ℝ ζ z (g z)| ≤ ∫ z in F, ‖fderiv ℝ ζ z‖ :=
    norm_integral_le_of_norm_le hI3.integrableOn (Eventually.of_forall hb2)
  rw [hkey, show ∀ a b : ℝ, -a - b = -(a + b) from fun a b => by ring, abs_neg]
  exact (abs_add_le _ _).trans (add_le_add hA hB)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Mollification by an even `C¹` kernel `η` with compact support commutes with `D` and is
self-adjoint: `∫ D(η * u)(x)(s x) dx = −∫ u div(η * s)` for integrable `u`, `s` (Simon Ch. 2,
Lemma 2.5).  Both derivatives are convolutions with the odd, bounded `Dη`, and Fubini applies to
`Dη(x − z)(s x) u(z)`, which is dominated by `C ‖s x‖ |u z|`. -/
theorem codim1_rdo_dg_sp_mollifier_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, η (-z) = η z) → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc heven hu hs
  -- Step 0: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 1: `η` is even, so `Dη` is odd (chain rule for `η = η ∘ (−id)`).
  have hodd : ∀ y, fderiv ℝ η (-y) = -fderiv ℝ η y := by
    intro y
    have h1 : HasFDerivAt (η ∘ fun z => -z)
        ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [show (η ∘ fun z => -z) = η from funext heven] at h1
    ext v
    rw [h1.fderiv]
    simp
  -- Step 2: `D(η * u)(x) = (Dη * u)(x)`, so `D(η * u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 3: `div(η * s)(z) = trace D(η * s)(z) = ∫ Dη(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ η (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηc.hasFDerivAt_convolution_left _ hη hs.locallyIntegrable z).fderiv, convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 4: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 5: combine, using `Dη(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [← neg_sub x z, hodd, neg_apply]
      ring
/-- Mollification does not increase the variation (Simon Ch. 2, Lemma 2.5, formula (4)): if
`|∫ u div g| ≤ M` for every `g ∈ C¹_c(ℝᴾ; ℝᴾ)` with `|g| ≤ 1`, then `∫ |D(η * u)| ≤ M` for an even
mollifier `η ≥ 0` with `∫ η = 1`.  With `w = η * u`, the field `s = 1_{spt w} |∇w|⁻¹ ∇w`
(`0⁻¹ = 0`) is Borel, bounded by `1`, compactly supported and has `Dw(s) = |Dw|`;
`codim1_rdo_dg_sp_mollifier_adjoint` moves `η` onto `s`, and `g = η * s` is admissible. -/
theorem codim1_rdo_dg_sp_mollify_variation : ∀ (P : ℕ) (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : Euclid P → ℝ, ContDiff ℝ 1 η → HasCompactSupport η → (∀ z, 0 ≤ η z) → (∀ z, η (-z) = η z) → ∫ z, η z = 1 → ∫ z, ‖fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) z‖ ≤ M := by
  intro P u M hu huc hM η hη hηc hη0 heven hη1
  -- Step 1: `w = η * u` is `C¹` with compact support `S = spt w`.
  set w := convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwc : HasCompactSupport w := hηc.convolution _ huc
  have hDw : Continuous (fderiv ℝ w) :=
    (hηc.contDiff_convolution_left _ hη hu.locallyIntegrable).continuous_fderiv one_ne_zero
  set S := tsupport w
  have hSm : MeasurableSet S := (isClosed_tsupport w).measurableSet
  -- Step 2: the gradient `∇w = (toDual)⁻¹ Dw` is continuous, `|∇w| = |Dw|`, `Dw(∇w) = |∇w|²`.
  set grad : Euclid P → Euclid P :=
    fun x => (InnerProductSpace.toDual ℝ (Euclid P)).symm (fderiv ℝ w x)
  have hgc : Continuous grad := (InnerProductSpace.toDual ℝ (Euclid P)).symm.continuous.comp hDw
  have hgn : ∀ x, ‖grad x‖ = ‖fderiv ℝ w x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hgg : ∀ x, fderiv ℝ w x (grad x) = ‖grad x‖ ^ 2 := by
    intro x
    rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := grad x) (y := fderiv ℝ w x)]
    exact real_inner_self_eq_norm_sq _
  -- Step 3: the unit field `f = |∇w|⁻¹ ∇w` (`0⁻¹ = 0`) and `s = 1_S f`.
  set f : Euclid P → Euclid P := fun x => ‖grad x‖⁻¹ • grad x with hf
  have hfm : Measurable f := hgc.norm.measurable.inv.smul hgc.measurable
  have hf1 : ∀ x, ‖f x‖ ≤ 1 := by
    intro x
    simp only [hf, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖grad x‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  set s : Euclid P → Euclid P := S.indicator f with hs
  have hs1 : ∀ x, ‖s x‖ ≤ 1 := fun x => (norm_indicator_le_norm_self f x).trans (hf1 x)
  have hsc : HasCompactSupport s :=
    HasCompactSupport.intro hwc.isCompact fun x hx => indicator_of_notMem hx f
  have hsi : Integrable s := by
    rw [hs, integrable_indicator_iff hSm]
    exact Measure.integrableOn_of_bounded hwc.isCompact.measure_lt_top.ne
      hfm.aestronglyMeasurable (Eventually.of_forall hf1)
  -- Step 4: `Dw(x)(s x) = |Dw(x)|` for all `x`.
  have hDs : ∀ x, fderiv ℝ w x (s x) = ‖fderiv ℝ w x‖ := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hs, indicator_of_mem hx, hf, map_smul, hgg, smul_eq_mul, ← hgn]
      rcases eq_or_ne ‖grad x‖ 0 with h | h
      · simp [h]
      · field_simp
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  -- Step 5: `g = η * s` is admissible: `C¹`, compact support, `|g| ≤ ∫ η = 1`.
  set g := convolution η s (ContinuousLinearMap.lsmul ℝ ℝ) volume with hg
  have hgC1 : ContDiff ℝ 1 g := hηc.contDiff_convolution_left _ hη hsi.locallyIntegrable
  have hgcs : HasCompactSupport g := hηc.convolution _ hsc
  have hηi : Integrable η := hη.continuous.integrable_of_hasCompactSupport hηc
  have hg1 : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    rw [hg, convolution_def]
    refine (norm_integral_le_of_norm_le hηi (Eventually.of_forall fun t => ?_)).trans hη1.le
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hη0 t)]
    exact mul_le_of_le_one_right (hη0 t) (hs1 _)
  -- Steps 6–7: the adjoint identity, then the hypothesis for `g`.
  calc ∫ z, ‖fderiv ℝ w z‖ = ∫ z, fderiv ℝ w z (s z) :=
        integral_congr_ae (Eventually.of_forall fun z => (hDs z).symm)
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P) :=
        Submission.codim1_rdo_dg_sp_mollifier_adjoint P η u s hη hηc heven hu hsi
    _ ≤ |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| :=
        neg_le_abs _
    _ ≤ M := hM g hgC1 hgcs hg1

/-- **Sobolev inequality in the limit of symmetric mollifications** (Simon Ch. 3, proof of
Theorem 4.3 (De Giorgi), Sobolev step, chapter-03.txt lines 689–712, with the mollification
Lemma Ch. 2, 2.5, chapter-02.txt lines 543–596).  Assume the Sobolev inequality
`(∫ |w|^p)^{1/p} ≤ c ∫ |Dw|` for `C¹` compactly supported `w`, let `u` be integrable with compact
support and `|∫ u div g| ≤ M` for `C¹_c` fields `|g| ≤ 1`, and let `η_k` be even, nonnegative,
`C¹`, compactly supported with `∫ η_k = 1` and `η_k * u → u` a.e.  Then `(∫ |u|^p)^{1/p} ≤ c M`:
`g = 0` gives `M ≥ 0`; each `w_k = η_k * u` is `C¹` with compact support and
`∫ |Dw_k| ≤ M` (`codim1_rdo_dg_sp_mollify_variation`), so `∫⁻ ‖w_k‖ₑ^p ≤ (cM)^p` by the Sobolev
inequality; Fatou's lemma along `w_k → u` a.e. gives `∫⁻ ‖u‖ₑ^p ≤ (cM)^p`, and taking `toReal`
and the `1/p` power concludes. -/
theorem codim1_rdo_dg_sp_sobolev_limit : ∀ (P : ℕ) (p c : ℝ), 0 < p → 0 ≤ c → (∀ w : Euclid P → ℝ, ContDiff ℝ 1 w → HasCompactSupport w → (∫ z, |w z| ^ p) ^ p⁻¹ ≤ c * ∫ z, ‖fderiv ℝ w z‖) → ∀ (u : Euclid P → ℝ) (M : ℝ), Integrable u → HasCompactSupport u → (∀ g : Euclid P → Euclid P, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, ‖g z‖ ≤ 1) → |∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ g z : Euclid P →ₗ[ℝ] Euclid P)| ≤ M) → ∀ η : ℕ → Euclid P → ℝ, (∀ k, ContDiff ℝ 1 (η k)) → (∀ k, HasCompactSupport (η k)) → (∀ k z, 0 ≤ η k z) → (∀ k z, η k (-z) = η k z) → (∀ k, ∫ z, η k z = 1) → (∀ᵐ x, Tendsto (fun k => convolution (η k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x) atTop (𝓝 (u x))) → (∫ z, |u z| ^ p) ^ p⁻¹ ≤ c * M := by
  intro P p c hp hc hS u M hu hcu hM η hη hηc hη0 hηs hη1 hae
  -- Step 1: testing the variation bound with `g = 0` gives `M ≥ 0`, hence `c M ≥ 0`
  have hM0 : 0 ≤ M := by
    simpa using hM (fun _ => 0) contDiff_const HasCompactSupport.zero fun _ => by simp
  have hcM : 0 ≤ c * M := mul_nonneg hc hM0
  -- Step 2: the mollifications `w_k = η_k * u` are `C¹` with compact support
  set w : ℕ → Euclid P → ℝ :=
    fun k => convolution (η k) u (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hwC : ∀ k, ContDiff ℝ 1 (w k) := fun k =>
    (hηc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hη k) hu.locallyIntegrable
  have hwcs : ∀ k, HasCompactSupport (w k) := fun k =>
    (hηc k).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcu
  -- `ofReal (|t|^p) = ‖t‖ₑ^p`
  have henorm : ∀ t : ℝ, ENNReal.ofReal (|t| ^ p) = ‖t‖ₑ ^ p := fun t => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg t) hp.le]
  -- Step 3: `∫ |Dw_k| ≤ M` and the Sobolev inequality give `∫ |w_k|^p ≤ (c M)^p`
  have hbound : ∀ k, ∫ z, |w k z| ^ p ≤ (c * M) ^ p := by
    intro k
    have hvar : ∫ z, ‖fderiv ℝ (w k) z‖ ≤ M :=
      Submission.codim1_rdo_dg_sp_mollify_variation P u M hu hcu hM (η k) (hη k) (hηc k)
        (hη0 k) (hηs k) (hη1 k)
    have h1 : (∫ z, |w k z| ^ p) ^ p⁻¹ ≤ c * M :=
      (hS (w k) (hwC k) (hwcs k)).trans (mul_le_mul_of_nonneg_left hvar hc)
    have ha : 0 ≤ ∫ z, |w k z| ^ p :=
      integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) p
    calc ∫ z, |w k z| ^ p = ((∫ z, |w k z| ^ p) ^ p⁻¹) ^ p :=
          (Real.rpow_inv_rpow ha hp.ne').symm
      _ ≤ (c * M) ^ p := Real.rpow_le_rpow (Real.rpow_nonneg ha _) h1 hp.le
  -- Step 4: `|w_k|^p` is continuous with compact support, so `∫⁻ ‖w_k‖ₑ^p ≤ ofReal ((c M)^p)`
  have hlow : ∀ k, ∫⁻ x, ‖w k x‖ₑ ^ p ≤ ENNReal.ofReal ((c * M) ^ p) := by
    intro k
    have hint : Integrable fun z => |w k z| ^ p :=
      ((hwC k).continuous.abs.rpow_const fun _ => Or.inr hp.le).integrable_of_hasCompactSupport
        ((hwcs k).abs.rpow_const hp.ne')
    calc ∫⁻ x, ‖w k x‖ₑ ^ p = ∫⁻ x, ENNReal.ofReal (|w k x| ^ p) :=
          lintegral_congr fun x => (henorm (w k x)).symm
      _ = ENNReal.ofReal (∫ z, |w k z| ^ p) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg _) p)).symm
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := ENNReal.ofReal_le_ofReal (hbound k)
  -- Step 5: Fatou's lemma along `w_k → u` a.e.
  have hfatou : ∫⁻ x, ‖u x‖ₑ ^ p ≤ ENNReal.ofReal ((c * M) ^ p) :=
    calc ∫⁻ x, ‖u x‖ₑ ^ p = ∫⁻ x, liminf (fun k => ‖w k x‖ₑ ^ p) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          exact ((hx.enorm.ennrpow_const p).liminf_eq).symm
      _ ≤ liminf (fun k => ∫⁻ x, ‖w k x‖ₑ ^ p) atTop :=
          lintegral_liminf_le fun k => (hwC k).continuous.measurable.enorm.pow_const p
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := liminf_le_of_frequently_le' (Frequently.of_forall hlow)
  -- Step 6: `∫ |u|^p = (∫⁻ ‖u‖ₑ^p).toReal ≤ (c M)^p`; take the `1/p` power
  have hup : 0 ≤ ∫ z, |u z| ^ p := integral_nonneg fun z => Real.rpow_nonneg (abs_nonneg _) p
  have hU : ∫ z, |u z| ^ p ≤ (c * M) ^ p := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun z => Real.rpow_nonneg (abs_nonneg (u z)) p)
      ((continuous_abs.rpow_const fun _ => Or.inr hp.le).comp_aestronglyMeasurable
        hu.aestronglyMeasurable)]
    refine ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg hcM p) ?_
    calc ∫⁻ x, ENNReal.ofReal (|u x| ^ p) = ∫⁻ x, ‖u x‖ₑ ^ p :=
          lintegral_congr fun x => henorm (u x)
      _ ≤ ENNReal.ofReal ((c * M) ^ p) := hfatou
  calc (∫ z, |u z| ^ p) ^ p⁻¹ ≤ ((c * M) ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow hup hU (inv_nonneg.2 hp.le)
    _ = c * M := Real.rpow_rpow_inv hcM hp.ne'

/-- **The Sobolev inequality for `ζ 1_F`** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi),
chapter-03.txt lines 689–712: `(∫ (ζ 1_F)^{(n+1)/n})^{n/(n+1)} ≤ c ∫ |D(ζ 1_F)| ≤
c (∫ ζ dμ + ∫_F |Dζ|)`, with the mollification Lemma Ch. 2, 2.5).  For `m ≥ 1` the exponent
`p = (m+1)/m` is the Hölder conjugate of `dim ℝ^{m+1} = m+1`, so Mathlib's Gagliardo–Nirenberg–
Sobolev inequality gives the constant `c`.  Given the Gauss–Green identity, `u = 1_F ζ` has
variation at most `M = ∫ ζ dμ + ∫_F |Dζ|`; the normalized bump functions of radius `1/(k+1)` are
even, nonnegative, unit-mass `C¹` kernels whose mollifications converge to `u` a.e. (Lebesgue
differentiation), and the Sobolev bound passes from the mollifications to `u`. -/
theorem codim1_rdo_dg_sobolev_perimeter : ∀ (m : ℕ), 1 ≤ m → ∃ c : ℝ, 0 < c ∧ ∀ (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ D → (∀ z, 0 ≤ ζ z) → (∫ z in F, ζ z ^ ((m + 1 : ℝ) / m)) ^ ((m : ℝ) / (m + 1)) ≤ c * (∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖) := by
  intro m hm
  -- Step 0: `p = (m+1)/m` is the Hölder conjugate of `m + 1`; GNS gives the constant `c`
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < (m + 1 : ℝ) / m := by positivity
  have hHC : Real.HolderConjugate (Module.finrank ℝ (Euclid (m + 1)) : ℝ) ((m + 1 : ℝ) / m) := by
    rw [finrank_euclideanSpace_fin]
    refine ⟨?_, by positivity, hp⟩
    push_cast
    field_simp
    ring
  obtain ⟨c, hc, hS⟩ := Submission.codim1_rdo_dg_sp_gns_real_of_lintegral (m + 1)
    ((m + 1 : ℝ) / m) (lintegralPowLePowLIntegralFDerivConst volume ((m + 1 : ℝ) / m)) hp
    fun w hw hwc => lintegral_pow_le_pow_lintegral_fderiv volume hw hwc hHC
  refine ⟨c, hc, ?_⟩
  intro D F μ ν hD hF hμD hμK hν hν1 hGG ζ hζ hζc hζD hζ0
  -- Step 1: `u = 1_F ζ` is integrable with compact support; its variation bound `M` is
  -- `gauss_green_variation` (used below)
  have hu : Integrable (F.indicator ζ) :=
    (hζ.continuous.integrable_of_hasCompactSupport hζc).indicator hF
  have huc : HasCompactSupport (F.indicator ζ) :=
    hζc.mono fun z hz h0 => hz (by simp [h0])
  -- Step 2: even, nonnegative, unit-mass `C¹` kernels of radius `1/(k+1)`
  let φ : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    { rIn := 1 / ((k : ℝ) + 1) / 2
      rOut := 1 / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith }
  have hφ0 : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hφK : ∀ᶠ k in atTop, (φ k).rOut ≤ 2 * (φ k).rIn :=
    Eventually.of_forall fun k => by
      change 1 / ((k : ℝ) + 1) ≤ 2 * (1 / ((k : ℝ) + 1) / 2)
      linarith
  -- Lebesgue differentiation: the mollifications converge to `u` almost everywhere
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    hφ0 hφK hu.locallyIntegrable
  -- Steps 3–4: GNS for the mollifications and passage to the limit
  have key := Submission.codim1_rdo_dg_sp_sobolev_limit (m + 1) ((m + 1 : ℝ) / m) c hp hc.le hS
    (F.indicator ζ) (∫ z, ζ z ∂μ + ∫ z in F, ‖fderiv ℝ ζ z‖) hu huc
    (fun g hg hgc hg1 => Submission.codim1_rdo_dg_sp_gauss_green_variation (m + 1) D F μ ν hD hF
      hμD hμK hν hν1 hGG ζ hζ hζc hζD hζ0 g hg hgc hg1)
    (fun k => (φ k).normed volume) (fun k => (φ k).contDiff_normed)
    (fun k => (φ k).hasCompactSupport_normed) (fun k => (φ k).nonneg_normed)
    (fun k => (φ k).normed_neg) (fun k => (φ k).integral_normed) hae
  -- Conclusion: `∫ |1_F ζ|^p = ∫_F ζ^p` and `p⁻¹ = m/(m+1)`
  have hint : ∫ z, |F.indicator ζ z| ^ ((m + 1 : ℝ) / m) = ∫ z in F, ζ z ^ ((m + 1 : ℝ) / m) := by
    rw [← integral_indicator hF]
    congr 1
    ext z
    by_cases hz : z ∈ F
    · simp [hz, abs_of_nonneg (hζ0 z)]
    · simp [hz, Real.zero_rpow hp.ne']
  rwa [hint, inv_div] at key

/-- **Lower volume density** of `F` and of its complement (Simon Ch. 3, proof of Theorem 4.3,
(10)–(11)) at a point `y` where the normal averages of the Gauss–Green measure `μ` tend to a unit
vector `v`.  `codim1_rdo_dg_cutoff_estimates` gives `ρ₁ > 0` and `C₁ ≥ 0` with `B̄_{ρ₁}(y) ⊆ D` and
the annular bounds `δ μ(B̄_ρ(y)) ≤ C₁ L(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` and
`δ μ(B̄_ρ(y)) ≤ C₁ L((B_{ρ+δ}(y) \ B̄_ρ(y)) \ F)` for `ρ + δ < ρ₁`, and
`codim1_rdo_dg_sobolev_perimeter` gives `c_S > 0` with
`(∫_F ζ^{(m+1)/m})^{m/(m+1)} ≤ c_S (∫ ζ dμ + ∫_F |Dζ|)`.  Since `v ≠ 0`, every closed ball about
`y` has positive `μ`-measure, and `μ(B̄_{ρ₁}(y)) < ∞` by local finiteness.  The finite-difference
isoperimetric inequality and its discrete integration (`codim1_rdo_dg_vdl_one_sided_density`)
give `L(F ∩ B_ρ(y)) ≥ c₁ ρ^{m+1}` for `ρ < ρ₁` (printed (10)).  Since `∫ div φ = 0`, `Fᶜ`
satisfies the Gauss–Green identity with normal `−ν`, so the Sobolev inequality and the annular
bound hold for `Fᶜ` as well, and the same argument gives `L(B_ρ(y) \ F) ≥ c₂ ρ^{m+1}`
(printed (11)).  Take `c = min c₁ c₂` and `ρ₂ = ρ₁`. -/
theorem codim1_rdo_dg_volume_density_lower : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), 1 ≤ m → IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ c ρ₂ : ℝ, 0 < c ∧ 0 < ρ₂ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ENNReal.ofReal (c * ρ ^ (m + 1)) ≤ volume (F ∩ ball y ρ) ∧ ENNReal.ofReal (c * ρ ^ (m + 1)) ≤ volume (ball y ρ \ F) := by
  intro m D F μ ν y v hm hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 1: `ρ₁`, `C₁` and the annular bounds (a) for `F` and (b) for its complement
  obtain ⟨ρ₁, C₁, hρ₁, hC₁, hρ₁D, hann, -⟩ :=
    Submission.codim1_rdo_dg_cutoff_estimates m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 2: the Sobolev inequality, with a constant `c_S` independent of `(D, F, μ, ν)`
  obtain ⟨cS, hcS, hS⟩ := Submission.codim1_rdo_dg_sobolev_perimeter m hm
  -- step 3: every closed ball about `y` has positive mass, and `μ(B̄_{ρ₁}(y)) < ∞`
  have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (by rw [hv]; exact one_ne_zero)
  have hpos : ∀ r : ℝ, 0 < r → μ (closedBall y r) ≠ 0 :=
    Submission.codim1_rdo_dg_vdl_measure_closedBall_ne_zero (m + 1) μ ν y v hv0 hT
  have hfin : μ (closedBall y ρ₁) ≠ ∞ := hμK _ (isCompact_closedBall y ρ₁) hρ₁D
  -- step 4: the lower bound for `F` (printed (10))
  obtain ⟨c₁, hc₁, h₁⟩ := Submission.codim1_rdo_dg_vdl_one_sided_density m D F μ y ρ₁ C₁ cS hm
    hF hcS hC₁ hρ₁D hfin hpos (hS D F μ ν hD hF hμD hμK hν hν1 hGG)
    fun ρ δ hρ hδ hρδ => (hann ρ δ hρ hδ hρδ).1
  -- step 5: `Fᶜ` satisfies the Gauss–Green identity with normal `−ν`, so the Sobolev inequality
  -- holds for `Fᶜ`; with (b) this gives the lower bound for `Fᶜ` (printed (11))
  have hGGc := Submission.codim1_rdo_dg_vdl_gauss_green_compl (m + 1) D F μ ν hF hGG
  obtain ⟨c₂, hc₂, h₂⟩ := Submission.codim1_rdo_dg_vdl_one_sided_density m D Fᶜ μ y ρ₁ C₁ cS hm
    hF.compl hcS hC₁ hρ₁D hfin hpos
    (hS D Fᶜ μ (fun z => -ν z) hD hF.compl hμD hμK hν.neg
      (fun z => (norm_neg (ν z)).trans (hν1 z)) hGGc)
    fun ρ δ hρ hδ hρδ => by
      rw [← Set.sdiff_eq_compl_inter]
      exact (hann ρ δ hρ hδ hρδ).2
  -- step 6: `c = min c₁ c₂` and `ρ₂ = ρ₁`, using `B_ρ(y) \ F = Fᶜ ∩ B_ρ(y)`
  refine ⟨min c₁ c₂, ρ₁, lt_min hc₁ hc₂, hρ₁, fun ρ hρ hρρ₁ => ⟨?_, ?_⟩⟩
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_left c₁ c₂)
      (pow_nonneg hρ.le _))).trans (h₁ ρ hρ hρρ₁)
  · rw [Set.sdiff_eq_compl_inter]
    exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (min_le_right c₁ c₂)
      (pow_nonneg hρ.le _))).trans (h₂ ρ hρ hρρ₁)

end Submission

end GMT.Ch07
