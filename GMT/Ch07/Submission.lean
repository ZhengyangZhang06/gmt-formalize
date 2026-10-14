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

/-- **Gauss–Green measure** (Simon Ch. 2, 2.1–2.2 and Ch. 3, 4.1, with the Riesz representation
Ch. 1, 4.14): if `φ ↦ ∫_F div φ` is bounded on smooth fields with `|φ| ≤ 1` supported in each
compact `K ⊆ D`, it is `φ ↦ -∫ ⟨φ, ν⟩ dμ` on `C¹` fields compactly supported in `D`, for a measure
`μ` carried by `D`, finite on its compact subsets, and a Borel unit field `ν`.  For each coordinate
`i`, `g ↦ ±∫_F div (g eᵢ)` has positive part `f ↦ sup {±∫_F div (g eᵢ) : g smooth, 0 ≤ g ≤ f}` on
`C_c(D, ℝ≥0)` (additive by smooth approximation under a continuous ceiling), represented by
Riesz–Markov–Kakutani on the open subspace `D`; the `2(m + 1)` measures are densities against their
sum (Lebesgue decomposition), the density field is normalized and the measure pushed forward to
`ℝ^{m+1}`; `C¹` fields are reached by mollification. -/
theorem Submission.codim1_rdo_dg_gauss_green_measure : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))), IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
  intro m D F hD hF hbound
  classical
  -- the trace as a continuous linear functional and the functional `T φ = ∫_F div φ`
  obtain ⟨trc, htrc⟩ : ∃ trc : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ, ∀ A,
      trc A = LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ)), fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Euclid (m + 1) → Euclid (m + 1)) → ℝ,
      ∀ φ, T φ = ∫ y in F, trc (fderiv ℝ φ y) := ⟨_, fun _ => rfl⟩
  have hTeq : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = T φ := by
    intro φ
    rw [hT]
    simp only [htrc]
  have hbound' : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ,
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → T φ ≤ C := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound K hK hKD
    refine ⟨C, fun φ h1 h2 h3 h4 => ?_⟩
    rw [← hTeq φ]
    exact hC φ h1 h2 h3 h4
  suffices H : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ by
    obtain ⟨μ, ν, h1, h2, h3, h4, h5⟩ := H
    exact ⟨μ, ν, h1, h2, h3, h4, fun φ hφ hφc hφD => (hTeq φ).trans (h5 φ hφ hφc hφD)⟩
  -- Step 1: `T` is linear on `C¹` compactly supported fields, and locally bounded
  have hdiv_int : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun y => trc (fderiv ℝ φ y)) (volume.restrict F) := fun φ hφ hc =>
    ((trc.continuous.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_left trc.map_zero)).restrict
  have hT_add : ∀ φ ψ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → T (φ + ψ) = T φ + T ψ := by
    intro φ ψ hφ hφc hψ hψc
    simp only [hT]
    rw [← integral_add (hdiv_int φ hφ hφc) (hdiv_int ψ hψ hψc)]
    congr 1; ext y
    rw [fderiv_add (hφ.differentiable one_ne_zero y) (hψ.differentiable one_ne_zero y), map_add]
  have hT_smul : ∀ (c : ℝ) (φ : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 φ →
      T (c • φ) = c * T φ := by
    intro c φ hφ
    simp only [hT]
    rw [← integral_const_mul]
    congr 1; ext y
    rw [fderiv_const_smul (hφ.differentiable one_ne_zero y),
      map_smul, smul_eq_mul]
  have hT0 : T 0 = 0 := by simp [hT]
  have hbd : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → ∀ M : ℝ, 0 ≤ M → (∀ y, ‖φ y‖ ≤ M) → |T φ| ≤ C * M := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound' K hK hKD
    have hC0 : 0 ≤ C := by
      simpa [hT0] using hC 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
    refine ⟨C, hC0, fun φ hφ hφc hφK M hM hφM => ?_⟩
    rcases hM.eq_or_lt with rfl | hMpos
    · have : φ = 0 := funext fun y => norm_le_zero_iff.1 (hφM y)
      simp [this, hT0]
    · have hsm : ContDiff ℝ (⊤ : ℕ∞) (M⁻¹ • φ) := contDiff_const.smul hφ
      have hsK : tsupport (M⁻¹ • φ) ⊆ K :=
        (tsupport_smul_subset_right (fun _ => M⁻¹) φ).trans hφK
      have hsn : ∀ y, ‖(M⁻¹ • φ) y‖ ≤ 1 := fun y => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM)]
        calc M⁻¹ * ‖φ y‖ ≤ M⁻¹ * M := by gcongr; exact hφM y
          _ = 1 := inv_mul_cancel₀ hMpos.ne'
      have h1 := hC _ hsm (hφc.smul_left) hsK hsn
      have h2 := hC (-(M⁻¹ • φ)) hsm.neg (hφc.smul_left).neg (by rwa [tsupport_neg]) (fun y => by
        rw [Pi.neg_apply, norm_neg]; exact hsn y)
      rw [hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h1
      rw [show -(M⁻¹ • φ) = (-M⁻¹) • φ by rw [neg_smul],
        hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h2
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left h2 hM
        rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h1 hM
        rw [← mul_assoc, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
  -- compact subsets of `D` and compact supports on the subtype `D`
  have hsubK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D →
      IsCompact (Subtype.val ⁻¹' K : Set D) := fun K hK hKD =>
    Subtype.isCompact_iff.2 (by rwa [Subtype.image_preimage_coe, inter_eq_right.2 hKD])
  have hcs : ∀ (h : Euclid (m + 1) → ℝ) (K : Set (Euclid (m + 1))), IsCompact K →
      support h ⊆ K → HasCompactSupport h ∧ tsupport h ⊆ K := fun h K hK hhK =>
    ⟨hK.of_isClosed_subset (isClosed_tsupport h) (closure_minimal hhK hK.isClosed),
      closure_minimal hhK hK.isClosed⟩
  -- smooth approximation of `a` under a continuous ceiling `u` (smooth partitions of unity)
  have happrox : ∀ (u a : Euclid (m + 1) → ℝ), Continuous u → Continuous a →
      (∀ z, 0 ≤ a z ∧ a z ≤ u z) → ∀ ε : ℝ, 0 < ε →
      ∃ a' : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a' ∧
        ∀ z, 0 ≤ a' z ∧ a' z ≤ u z ∧ |a' z - a z| < ε := by
    intro u a hu ha hau ε hε
    have hloc : ∀ y : Euclid (m + 1), ∃ c : ℝ, ∀ᶠ z in 𝓝 y, c ∈ Icc 0 (u z) ∩ ball (a z) ε := by
      intro y
      refine ⟨max 0 (a y - ε / 2), ?_⟩
      have h1 : ∀ᶠ z in 𝓝 y, |a z - a y| < ε / 2 := by
        have := (ha.tendsto y).eventually (ball_mem_nhds (a y) (half_pos hε))
        filter_upwards [this] with z hz
        simpa [Real.dist_eq] using hz
      have h2 : ∀ᶠ z in 𝓝 y, max 0 (a y - ε / 2) ≤ u z := by
        by_cases hay : a y - ε / 2 ≤ 0
        · exact Eventually.of_forall fun z => by
            rw [max_eq_left hay]; exact (hau z).1.trans (hau z).2
        · rw [not_le] at hay
          have hlt : a y - ε / 2 < u y := by linarith [(hau y).2]
          have := (hu.tendsto y).eventually (lt_mem_nhds hlt)
          filter_upwards [this] with z hz
          rw [max_eq_right hay.le]; exact hz.le
      filter_upwards [h1, h2] with z hz1 hz2
      refine ⟨⟨le_max_left _ _, hz2⟩, ?_⟩
      rw [mem_ball, Real.dist_eq]
      have : |max 0 (a y - ε / 2) - a y| ≤ ε / 2 := by
        rcases le_total (a y - ε / 2) 0 with h | h
        · rw [max_eq_left h, zero_sub, abs_neg, abs_of_nonneg (hau y).1]; linarith
        · rw [max_eq_right h]; rw [show a y - ε / 2 - a y = -(ε / 2) by ring, abs_neg,
            abs_of_pos (half_pos hε)]
      calc |max 0 (a y - ε / 2) - a z| ≤ |max 0 (a y - ε / 2) - a y| + |a y - a z| :=
            abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by
          have : |a y - a z| < ε / 2 := by rw [abs_sub_comm]; exact hz1
          linarith
        _ = ε := by ring
    obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
      (modelWithCornersSelf ℝ (Euclid (m + 1))) (n := ⊤)
      (t := fun z => Icc 0 (u z) ∩ ball (a z) ε)
      (fun z => (convex_Icc _ _).inter (convex_ball _ _)) hloc
    refine ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z => ?_⟩
    have := hg z
    simp only [mem_inter_iff, mem_Icc, mem_ball, Real.dist_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- Step 2: the positive part of a locally bounded functional, via Riesz–Markov–Kakutani on `D`
  have hpos : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ : Measure D, IsFiniteMeasureOnCompacts μ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → (∀ y, 0 ≤ g y) →
          BddAbove (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) ∧
          ∫ x : D, g x ∂μ = sSup (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) := by
    intro S hSadd hSsmul hSbd
    have hS0 : S 0 = 0 := by simpa using hSsmul 0 0 contDiff_const
    -- `A u`: smooth `h`, `0 ≤ h ≤ u`, compactly supported in `D`; the functional is `sup S(A u)`
    obtain ⟨A, hA⟩ : ∃ A : (Euclid (m + 1) → ℝ) → Set (Euclid (m + 1) → ℝ), ∀ u h, h ∈ A u ↔
        (ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
          ∀ y, 0 ≤ h y ∧ h y ≤ u y) :=
      ⟨fun u => {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ u y}, fun _ _ => Iff.rfl⟩
    have hA0 : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → (0 : Euclid (m + 1) → ℝ) ∈ A u :=
      fun u hu => (hA u 0).2 ⟨contDiff_const, HasCompactSupport.zero, by simp,
        fun y => ⟨le_rfl, hu y⟩⟩
    have hAsupp : ∀ u h, h ∈ A u → support h ⊆ support u := by
      intro u h hh y hy huy
      obtain ⟨-, -, -, h4⟩ := (hA u h).1 hh
      have := h4 y
      rw [huy] at this
      exact hy (le_antisymm this.2 this.1)
    have hbddA : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → BddAbove (S '' A u) := by
      intro u hu hu0 K hK hKD huK
      obtain ⟨C, hC⟩ := hSbd K hK hKD
      obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support (hcs u K hK huK).1
      refine ⟨C * M, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨h1, h2, -, h4⟩ := (hA u h).1 hh
      refine hC h h1 h2 (hcs h K hK ((hAsupp u h hh).trans huK)).2 M
        ((norm_nonneg _).trans (hM 0)) fun y => ?_
      rw [abs_of_nonneg (h4 y).1]
      exact (h4 y).2.trans ((le_abs_self _).trans (hM y))
    have hle_sup : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ h ∈ A u, S h ≤ sSup (S '' A u) :=
      fun u hu hu0 K hK hKD huK h hh => le_csSup (hbddA u hu hu0 K hK hKD huK) ⟨h, hh, rfl⟩
    have hsup_le : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → ∀ c : ℝ,
        (∀ h ∈ A u, S h ≤ c) → sSup (S '' A u) ≤ c := fun u hu c hc =>
      csSup_le ⟨S 0, 0, hA0 u hu, rfl⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
    -- additivity
    have hadd : ∀ u₁ u₂ : Euclid (m + 1) → ℝ, Continuous u₁ → (∀ y, 0 ≤ u₁ y) →
        Continuous u₂ → (∀ y, 0 ≤ u₂ y) → ∀ K₁ K₂, IsCompact K₁ → K₁ ⊆ D → support u₁ ⊆ K₁ →
        IsCompact K₂ → K₂ ⊆ D → support u₂ ⊆ K₂ →
        sSup (S '' A (u₁ + u₂)) = sSup (S '' A u₁) + sSup (S '' A u₂) := by
      intro u₁ u₂ hu₁ hu₁0 hu₂ hu₂0 K₁ K₂ hK₁ hK₁D hu₁K hK₂ hK₂D hu₂K
      have hu0 : ∀ y, 0 ≤ (u₁ + u₂) y := fun y => add_nonneg (hu₁0 y) (hu₂0 y)
      have huK : support (u₁ + u₂) ⊆ K₁ ∪ K₂ := fun y hy => by
        by_contra hy'
        apply hy
        have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
        have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
        rw [Pi.add_apply, notMem_support.1 (fun h => hy1 (hu₁K h)),
          notMem_support.1 (fun h => hy2 (hu₂K h)), add_zero]
      have hKK : IsCompact (K₁ ∪ K₂) := hK₁.union hK₂
      have hKKD : K₁ ∪ K₂ ⊆ D := union_subset hK₁D hK₂D
      apply le_antisymm
      · apply hsup_le (u₁ + u₂) hu0
        intro g hg
        obtain ⟨hg1, hg2, hg3, hg4⟩ := (hA (u₁ + u₂) g).1 hg
        obtain ⟨C, hC⟩ := hSbd (K₁ ∪ K₂) hKK hKKD
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨δ, hδ0, hCδ⟩ : ∃ δ : ℝ, 0 < δ ∧ C * (2 * δ) ≤ ε := by
          refine ⟨ε / (2 * (|C| + 1)), div_pos hε (by positivity), ?_⟩
          have hpos' : (0 : ℝ) < |C| + 1 := by positivity
          have : C * (2 * (ε / (2 * (|C| + 1)))) = C * ε / (|C| + 1) := by
            field_simp
          rw [this, div_le_iff₀ hpos', mul_comm ε]
          exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right
            zero_le_one)) hε.le
        have ha : Continuous fun y => min (g y) (u₁ y) := hg1.continuous.min hu₁
        obtain ⟨a', ha'1, ha'2⟩ := happrox u₁ (fun y => min (g y) (u₁ y)) hu₁ ha
          (fun z => ⟨le_min (hg4 z).1 (hu₁0 z), min_le_right _ _⟩) δ hδ0
        have hb : ∀ z, 0 ≤ g z - min (g z) (u₁ z) ∧ g z - min (g z) (u₁ z) ≤ u₂ z := by
          intro z
          refine ⟨sub_nonneg.2 (min_le_left _ _), ?_⟩
          have h' : g z ≤ u₁ z + u₂ z := (hg4 z).2
          rcases le_total (g z) (u₁ z) with h | h
          · rw [min_eq_left h, sub_self]; exact hu₂0 z
          · rw [min_eq_right h]; linarith
        obtain ⟨b', hb'1, hb'2⟩ := happrox u₂ (fun y => g y - min (g y) (u₁ y)) hu₂
          (hg1.continuous.sub ha) hb δ hδ0
        have ha'K : support a' ⊆ K₁ := fun y hy => hu₁K fun h => hy (by
          have := ha'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hb'K : support b' ⊆ K₂ := fun y hy => hu₂K fun h => hy (by
          have := hb'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hcsa' := hcs a' K₁ hK₁ ha'K
        have hcsb' := hcs b' K₂ hK₂ hb'K
        have ha'A : a' ∈ A u₁ := (hA u₁ a').2 ⟨ha'1, hcsa'.1, hcsa'.2.trans hK₁D,
          fun z => ⟨(ha'2 z).1, (ha'2 z).2.1⟩⟩
        have hb'A : b' ∈ A u₂ := (hA u₂ b').2 ⟨hb'1, hcsb'.1, hcsb'.2.trans hK₂D,
          fun z => ⟨(hb'2 z).1, (hb'2 z).2.1⟩⟩
        have hgK : support g ⊆ K₁ ∪ K₂ := (hAsupp (u₁ + u₂) g hg).trans huK
        have hrK : support (g - a' - b') ⊆ K₁ ∪ K₂ := fun y hy => by
          by_contra hy'
          apply hy
          have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
          have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
          rw [Pi.sub_apply, Pi.sub_apply, notMem_support.1 (fun h => hy' (hgK h)),
            notMem_support.1 (fun h => hy1 (ha'K h)), notMem_support.1 (fun h => hy2 (hb'K h)),
            sub_zero, sub_zero]
        have hrcs := hcs (g - a' - b') (K₁ ∪ K₂) hKK hrK
        have hr1 : ContDiff ℝ (⊤ : ℕ∞) (g - a' - b') := (hg1.sub ha'1).sub hb'1
        have hrb : ∀ y, |(g - a' - b') y| ≤ 2 * δ := fun y => by
          have h1 := (ha'2 y).2.2
          have h2 := (hb'2 y).2.2
          rw [Pi.sub_apply, Pi.sub_apply]
          have e : g y - a' y - b' y =
              -((a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))) := by ring
          rw [e, abs_neg]
          calc |(a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))|
              ≤ |a' y - min (g y) (u₁ y)| + |b' y - (g y - min (g y) (u₁ y))| :=
                abs_add_le _ _
            _ ≤ 2 * δ := by linarith
        have hSr := hC (g - a' - b') hr1 hrcs.1 hrcs.2 (2 * δ) (by positivity) hrb
        have hdec : S ((a' + b') + (g - a' - b')) = S a' + S b' + S (g - a' - b') := by
          rw [hSadd (a' + b') (g - a' - b') (ha'1.add hb'1) (hcsa'.1.add hcsb'.1) hr1 hrcs.1,
            hSadd a' b' ha'1 hcsa'.1 hb'1 hcsb'.1]
        rw [show (a' + b') + (g - a' - b') = g by abel] at hdec
        have h1 := hle_sup u₁ hu₁ hu₁0 K₁ hK₁ hK₁D hu₁K a' ha'A
        have h2 := hle_sup u₂ hu₂ hu₂0 K₂ hK₂ hK₂D hu₂K b' hb'A
        linarith
      · have key : ∀ h₁ ∈ A u₁, ∀ h₂ ∈ A u₂, S h₁ + S h₂ ≤ sSup (S '' A (u₁ + u₂)) := by
          intro h₁ hh₁ h₂ hh₂
          obtain ⟨a1, a2, a3, a4⟩ := (hA u₁ h₁).1 hh₁
          obtain ⟨b1, b2, b3, b4⟩ := (hA u₂ h₂).1 hh₂
          rw [← hSadd h₁ h₂ a1 a2 b1 b2]
          have hmem : h₁ + h₂ ∈ A (u₁ + u₂) := (hA (u₁ + u₂) (h₁ + h₂)).2 ⟨a1.add b1,
            a2.add b2, (tsupport_add h₁ h₂).trans (union_subset a3 b3),
            fun y => ⟨add_nonneg (a4 y).1 (b4 y).1, add_le_add (a4 y).2 (b4 y).2⟩⟩
          exact hle_sup (u₁ + u₂) (hu₁.add hu₂) hu0 (K₁ ∪ K₂) hKK hKKD huK (h₁ + h₂) hmem
        have : sSup (S '' A u₁) ≤ sSup (S '' A (u₁ + u₂)) - sSup (S '' A u₂) := by
          apply hsup_le u₁ hu₁0
          intro h₁ hh₁
          have : sSup (S '' A u₂) ≤ sSup (S '' A (u₁ + u₂)) - S h₁ := by
            apply hsup_le u₂ hu₂0
            intro h₂ hh₂
            have := key h₁ hh₁ h₂ hh₂
            linarith
          linarith
        linarith
    -- homogeneity
    have hsmul : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ c : ℝ, 0 ≤ c →
        sSup (S '' A (c • u)) = c * sSup (S '' A u) := by
      intro u hu hu0 K hK hKD huK c hc
      have hcu0 : ∀ y, 0 ≤ (c • u) y := fun y => mul_nonneg hc (hu0 y)
      have hcuK : support (c • u) ⊆ K := (support_const_smul_subset c u).trans huK
      have hcuc : Continuous (c • u) := hu.const_smul c
      rcases hc.eq_or_lt with hc0 | hcpos
      · subst hc0
        rw [zero_mul]
        apply le_antisymm
        · apply hsup_le ((0 : ℝ) • u) hcu0
          intro h hh
          obtain ⟨-, -, -, h4⟩ := (hA ((0 : ℝ) • u) h).1 hh
          have : h = 0 := funext fun y => le_antisymm (by
            have := (h4 y).2
            rwa [Pi.smul_apply, zero_smul] at this) (h4 y).1
          rw [this, hS0]
        · have h0 := hle_sup ((0 : ℝ) • u) hcuc hcu0 K hK hKD hcuK 0 (hA0 ((0 : ℝ) • u) hcu0)
          rwa [hS0] at h0
      · apply le_antisymm
        · apply hsup_le (c • u) hcu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA (c • u) h).1 hh
          have hmem : c⁻¹ • h ∈ A u := (hA u (c⁻¹ • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c⁻¹) h2,
            (tsupport_smul_subset_right (fun _ => c⁻¹) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg (inv_nonneg.2 hc) (h4 y).1, by
                rw [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hcpos]
                have := (h4 y).2
                rwa [Pi.smul_apply, smul_eq_mul] at this⟩⟩
          have := hle_sup u hu hu0 K hK hKD huK (c⁻¹ • h) hmem
          have e : S h = c * S (c⁻¹ • h) := by
            rw [hSsmul c⁻¹ h h1, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc
        · rw [← le_div_iff₀' hcpos]
          apply hsup_le u hu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA u h).1 hh
          have hmem : c • h ∈ A (c • u) := (hA (c • u) (c • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c) h2,
            (tsupport_smul_subset_right (fun _ => c) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg hc (h4 y).1, by
                rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
                exact mul_le_mul_of_nonneg_left (h4 y).2 hc⟩⟩
          have := hle_sup (c • u) hcuc hcu0 K hK hKD hcuK (c • h) hmem
          rw [hSsmul c h h1] at this
          rw [le_div_iff₀' hcpos]
          exact this
    -- extension by zero of `f ∈ C_c(D, ℝ≥0)`; `f ↦ sup S(A (ext f))` is `ℝ≥0`-linear
    obtain ⟨ext, hext⟩ : ∃ ext : CompactlySupportedContinuousMap D NNReal →
        Euclid (m + 1) → ℝ, ∀ f y, ext f y = if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0 :=
      ⟨fun f y => if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0, fun _ _ => rfl⟩
    have hextK : ∀ f : CompactlySupportedContinuousMap D NNReal,
        IsCompact (Subtype.val '' tsupport f) ∧ Subtype.val '' tsupport f ⊆ D := fun f =>
      ⟨f.hasCompactSupport.image continuous_subtype_val, by rintro _ ⟨x, -, rfl⟩; exact x.2⟩
    have hext_supp : ∀ f : CompactlySupportedContinuousMap D NNReal,
        support (ext f) ⊆ Subtype.val '' tsupport f := by
      intro f y hy
      rw [mem_support, hext] at hy
      by_cases h : y ∈ D
      · rw [dite_eq_left h] at hy
        refine ⟨⟨y, h⟩, subset_tsupport _ ?_, rfl⟩
        intro h0
        apply hy
        rw [h0]
        rfl
      · rw [dite_eq_right h] at hy
        exact absurd rfl hy
    have hext_nonneg : ∀ f y, 0 ≤ ext f y := by
      intro f y
      rw [hext]
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl
    have hext_cont : ∀ f : CompactlySupportedContinuousMap D NNReal, Continuous (ext f) := by
      intro f
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ Subtype.val '' tsupport f
      · have hyD : y ∈ D := (hextK f).2 hy
        have hcont : ContinuousOn (ext f) D := by
          rw [continuousOn_iff_continuous_domRestrict]
          have : D.domRestrict (ext f) = fun x : D => ((f x : NNReal) : ℝ) := by
            funext x
            rw [Set.domRestrict_apply, hext, dite_eq_left x.2]
          rw [this]
          exact NNReal.continuous_coe.comp f.continuous
        exact hcont.continuousAt (hD.mem_nhds hyD)
      · have : ext f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [(hextK f).1.isClosed.isOpen_compl.mem_nhds hy] with z hz
          by_contra hne
          exact hz (hext_supp f hne)
        exact continuousAt_const.congr this.symm
    have hext_add : ∀ f g : CompactlySupportedContinuousMap D NNReal,
        ext (f + g) = ext f + ext g := by
      intro f g
      funext y
      simp only [hext, Pi.add_apply]
      split_ifs
      · simp
      · simp
    have hext_smul : ∀ (c : NNReal) (f : CompactlySupportedContinuousMap D NNReal),
        ext (c • f) = (c : ℝ) • ext f := by
      intro c f
      funext y
      simp only [hext, Pi.smul_apply]
      split_ifs
      · simp
      · simp
    have hΛ0 : ∀ f : CompactlySupportedContinuousMap D NNReal, 0 ≤ sSup (S '' A (ext f)) :=
      fun f => by
        have := hle_sup (ext f) (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2
          (hext_supp f) 0 (hA0 _ (hext_nonneg f))
        rwa [hS0] at this
    let Λn : CompactlySupportedContinuousMap D NNReal →ₗ[NNReal] NNReal :=
      { toFun := fun f => ⟨sSup (S '' A (ext f)), hΛ0 f⟩
        map_add' := fun f g => by
          apply NNReal.eq
          change sSup (S '' A (ext (f + g))) = sSup (S '' A (ext f)) + sSup (S '' A (ext g))
          rw [hext_add]
          exact hadd _ _ (hext_cont f) (hext_nonneg f) (hext_cont g) (hext_nonneg g) _ _
            (hextK f).1 (hextK f).2 (hext_supp f) (hextK g).1 (hextK g).2 (hext_supp g)
        map_smul' := fun c f => by
          apply NNReal.eq
          change sSup (S '' A (ext (c • f))) = (c : ℝ) * sSup (S '' A (ext f))
          rw [hext_smul]
          exact hsmul _ (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2 (hext_supp f)
            c c.2 }
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    refine ⟨RealRMK.rieszMeasure (CompactlySupportedContinuousMap.toRealPositiveLinear Λn),
      inferInstance, ?_⟩
    intro g hg hgc hgD hg0
    have hAg : A g = {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ g y} := by
      ext h
      exact hA g h
    rw [← hAg]
    refine ⟨hbddA g hg.continuous hg0 (tsupport g) hgc hgD (subset_tsupport g), ?_⟩
    have hgcs : HasCompactSupport (fun x : D => Real.toNNReal (g x)) := by
      refine (hsubK _ hgc hgD).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal ?_ ((isClosed_tsupport g).preimage continuous_subtype_val))
      intro x hx
      apply subset_tsupport g
      intro h0
      apply hx
      simp [h0]
    let fg : CompactlySupportedContinuousMap D NNReal :=
      ⟨⟨fun x => Real.toNNReal (g x),
        continuous_real_toNNReal.comp (hg.continuous.comp continuous_subtype_val)⟩, hgcs⟩
    have hfg : ext fg = g := by
      funext y
      rw [hext]
      by_cases h : y ∈ D
      · rw [dite_eq_left h]
        exact Real.coe_toNNReal _ (hg0 y)
      · rw [dite_eq_right h]
        exact (image_eq_zero_of_notMem_tsupport (fun h' => h (hgD h'))).symm
    calc ∫ x : D, g x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn))
        = ∫ x : D, (CompactlySupportedContinuousMap.toReal fg) x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn)) := by
          congr 1
          funext x
          rw [CompactlySupportedContinuousMap.toReal_apply]
          exact (Real.coe_toNNReal _ (hg0 x)).symm
      _ = CompactlySupportedContinuousMap.toRealPositiveLinear Λn
          (CompactlySupportedContinuousMap.toReal fg) := RealRMK.integral_rieszMeasure _ _
      _ = (Λn fg : ℝ) := by rw [CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
      _ = sSup (S '' A (ext fg)) := rfl
      _ = sSup (S '' A g) := by rw [hfg]
  -- Step 3: Jordan decomposition of a locally bounded functional on smooth functions
  have hcsD : ∀ f : Euclid (m + 1) → ℝ, HasCompactSupport f → tsupport f ⊆ D →
      HasCompactSupport (fun x : D => f x) := by
    intro f hfc hfD
    refine (hsubK _ hfc hfD).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ?_ ((isClosed_tsupport f).preimage continuous_subtype_val))
    intro x hx
    exact subset_tsupport f hx
  have hintD : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ → ∀ f : Euclid (m + 1) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ D → Integrable (fun x : D => f x) μ := by
    intro μ hμ f hf hfc hfD
    exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport (hcsD f hfc hfD)
  have hjordan : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧ IsFiniteMeasureOnCompacts μ₂ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
    intro S hSadd hSsmul hSbd
    obtain ⟨μ₁, hμ₁, h₁⟩ := hpos S hSadd hSsmul hSbd
    have hSneg : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → S (-g) = -S g :=
      fun g hg => by
        rw [show -g = (-1 : ℝ) • g by rw [neg_one_smul], hSsmul (-1) g hg, neg_one_mul]
    obtain ⟨μ₂, hμ₂, h₂⟩ := hpos (fun g => -S g)
      (fun g h hg hgc hh hhc => by rw [hSadd g h hg hgc hh hhc, neg_add])
      (fun c g hg => by rw [hSsmul c g hg, mul_neg])
      (fun K hK hKD => by
        obtain ⟨C, hC⟩ := hSbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (-g) hg.neg hgc.neg (by rwa [tsupport_neg]) M hM
          (fun y => by rw [Pi.neg_apply, abs_neg]; exact hgM y)
        rwa [hSneg g hg] at this)
    refine ⟨μ₁, μ₂, hμ₁, hμ₂, ?_⟩
    have hnn : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ D → (∀ y, 0 ≤ g y) → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro g hg hgc hgD hg0
      obtain ⟨hb₁, he₁⟩ := h₁ g hg hgc hgD hg0
      obtain ⟨hb₂, he₂⟩ := h₂ g hg hgc hgD hg0
      rw [he₁, he₂]
      set Ag := {h : Euclid (m + 1) → ℝ | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y} with hAg
      have hgA : g ∈ Ag := ⟨hg, hgc, hgD, fun y => ⟨hg0 y, le_rfl⟩⟩
      have hsubA : ∀ h ∈ Ag, g - h ∈ Ag := fun h hh =>
        ⟨hg.sub hh.1, hgc.sub hh.2.1, (tsupport_sub g h).trans (union_subset hgD hh.2.2.1),
          fun y => ⟨sub_nonneg.2 (hh.2.2.2 y).2, sub_le_self _ (hh.2.2.2 y).1⟩⟩
      have hdec : ∀ h ∈ Ag, S g = S (g - h) + S h := fun h hh => by
        rw [← hSadd (g - h) h (hg.sub hh.1) (hgc.sub hh.2.1) hh.1 hh.2.1, sub_add_cancel]
      have hne : Ag.Nonempty := ⟨g, hgA⟩
      have i1 : sSup ((fun g => -S g) '' Ag) ≤ sSup (S '' Ag) - S g := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₁ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      have i2 : sSup (S '' Ag) ≤ S g + sSup ((fun g => -S g) '' Ag) := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₂ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      linarith
    -- a general `g`: add `M χ`, with `|g| ≤ M` and a smooth cutoff `χ = 1` on `tsupport g`
    intro g hg hgc hgD
    obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hgc hD hgD
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := tsupport g)) (isClosed_tsupport g)
      (self_subset_thickening hδ _)
    have hχK : support χ ⊆ cthickening δ (tsupport g) :=
      hχs ▸ thickening_subset_cthickening δ _
    have hχcs := hcs χ (cthickening δ (tsupport g)) (IsCompact.cthickening hgc) hχK
    obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (M • χ) := contDiff_const.smul hχ
    have hψcs : HasCompactSupport (M • χ) := HasCompactSupport.smul_left (f := fun _ => M) hχcs.1
    have hψD : tsupport (M • χ) ⊆ D :=
      (tsupport_smul_subset_right (fun _ => M) χ).trans (hχcs.2.trans hδD)
    have hψ0 : ∀ y, 0 ≤ (M • χ) y := fun y => by
      rw [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hM0 (hχ01 y).1
    have hgψ0 : ∀ y, 0 ≤ (g + M • χ) y := fun y => by
      by_cases hy : y ∈ tsupport g
      · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hχ1 y).1 hy, mul_one]
        have := hM y
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (g y)]
      · rw [Pi.add_apply, image_eq_zero_of_notMem_tsupport hy, zero_add]; exact hψ0 y
    have e1 := hnn (g + M • χ) (hg.add hψ) (hgc.add hψcs)
      ((tsupport_add g (M • χ)).trans (union_subset hgD hψD)) hgψ0
    have e2 := hnn (M • χ) hψ hψcs hψD hψ0
    rw [hSadd g (M • χ) hg hgc hψ hψcs] at e1
    have i1 : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ →
        ∫ x : D, (g + M • χ) x ∂μ = ∫ x : D, g x ∂μ + ∫ x : D, (M • χ) x ∂μ := by
      intro μ hμ
      simp only [Pi.add_apply]
      exact integral_add (hintD μ hμ g hg.continuous hgc hgD)
        (hintD μ hμ (M • χ) hψ.continuous hψcs hψD)
    rw [i1 μ₁ hμ₁, i1 μ₂ hμ₂] at e1
    linarith
  -- Step 4: representation of `T` on smooth fields
  have hsm_rep : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
    -- the standard basis
    obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)),
        b = EuclideanSpace.basisFun (Fin (m + 1)) ℝ := ⟨_, rfl⟩
    have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.norm_eq_one i
    have hbinner : ∀ (x : Euclid (m + 1)) (i : Fin (m + 1)), inner ℝ x (b i) = x i := by
      intro x i; rw [hb]; exact EuclideanSpace.inner_basisFun_real _ x i
    have hbsum : ∀ x : Euclid (m + 1), ∑ i, x i • b i = x := by
      intro x; rw [hb]; exact (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x
    -- coordinate functionals
    have hcomp : ∀ i : Fin (m + 1), ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧
        IsFiniteMeasureOnCompacts μ₂ ∧ ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          HasCompactSupport g → tsupport g ⊆ D →
          T (fun y => g y • b i) = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro i
      have hsm : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ContDiff ℝ (⊤ : ℕ∞) (fun y => g y • b i) := fun g hg => hg.smul contDiff_const
      have hcs1 : ∀ g : Euclid (m + 1) → ℝ, HasCompactSupport g →
          HasCompactSupport (fun y => g y • b i) := fun g hg =>
        hg.comp_left (g := fun r : ℝ => r • b i) (zero_smul ℝ (b i))
      apply hjordan (fun g => T (fun y => g y • b i))
      · intro g h hg hgc hh hhc
        have e : (fun y => (g + h) y • b i) = (fun y => g y • b i) + (fun y => h y • b i) := by
          funext y; rw [Pi.add_apply, Pi.add_apply, add_smul]
        change T (fun y => (g + h) y • b i) = T (fun y => g y • b i) + T (fun y => h y • b i)
        rw [e, hT_add _ _ ((hsm g hg).of_le (by exact_mod_cast le_top)) (hcs1 g hgc)
          ((hsm h hh).of_le (by exact_mod_cast le_top)) (hcs1 h hhc)]
      · intro c g hg
        have e : (fun y => (c • g) y • b i) = c • (fun y => g y • b i) := by
          funext y; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]
        change T (fun y => (c • g) y • b i) = c * T (fun y => g y • b i)
        rw [e, hT_smul c _ ((hsm g hg).of_le (by exact_mod_cast le_top))]
      · intro K hK hKD
        obtain ⟨C, -, hC⟩ := hbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (fun y => g y • b i) (hsm g hg) (hcs1 g hgc)
          ((tsupport_smul_subset_left g (fun _ => b i)).trans hgK) M hM (fun y => by
            rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs]; exact hgM y)
        exact (le_abs_self _).trans this
    choose μ₁ μ₂ hμ₁ hμ₂ hrep using hcomp
    -- coordinates of a field
    have hcoord_sm : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y i) := fun φ i hφ =>
      (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hφ
    have hcoord_cs : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        HasCompactSupport φ → HasCompactSupport (fun y => φ y i) := fun φ i hφ =>
      hφ.comp_left (g := fun v : Euclid (m + 1) => v i) rfl
    have hcoord_ts : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        tsupport (fun y => φ y i) ⊆ tsupport φ := fun φ i =>
      tsupport_comp_subset (g := fun v : Euclid (m + 1) => v i) rfl φ
    have hTdecomp : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → T φ = ∑ i, T (fun y => φ y i • b i) := by
      intro φ hφ hφc
      have key : ∀ s : Finset (Fin (m + 1)),
          ContDiff ℝ 1 (∑ i ∈ s, fun y => φ y i • b i) ∧
          HasCompactSupport (∑ i ∈ s, fun y => φ y i • b i) ∧
          T (∑ i ∈ s, fun y => φ y i • b i) = ∑ i ∈ s, T (fun y => φ y i • b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          exact ⟨contDiff_const, HasCompactSupport.zero, hT0⟩
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          have h1 : ContDiff ℝ 1 (fun y => φ y j • b j) :=
            ((hcoord_sm φ j hφ).smul contDiff_const).of_le (by exact_mod_cast le_top)
          have h2 : HasCompactSupport (fun y => φ y j • b j) :=
            (hcoord_cs φ j hφc).comp_left (g := fun r : ℝ => r • b j) (zero_smul ℝ _)
          exact ⟨h1.add ih.1, h2.add ih.2.1, by rw [hT_add _ _ h1 h2 ih.1 ih.2.1, ih.2.2]⟩
      have hφeq : φ = ∑ i, fun y => φ y i • b i := by
        funext y
        rw [Finset.sum_apply]
        exact (hbsum (φ y)).symm
      conv_lhs => rw [hφeq]
      exact (key Finset.univ).2.2
    -- the dominating measure on `D`
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    obtain ⟨μD, hμD⟩ : ∃ μD : Measure D, μD = ∑ i, (μ₁ i + μ₂ i) := ⟨_, rfl⟩
    have hμDK : ∀ K : Set D, IsCompact K → μD K < ∞ := by
      intro K hK
      rw [hμD, Measure.finsetSum_apply]
      refine ENNReal.sum_lt_top.2 fun i _ => ?_
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨(hμ₁ i).lt_top_of_isCompact hK, (hμ₂ i).lt_top_of_isCompact hK⟩
    have : IsFiniteMeasureOnCompacts μD := ⟨hμDK⟩
    have hRN : ∀ ν : Measure D, IsFiniteMeasureOnCompacts ν → ν ≤ μD →
        ∃ r : D → ℝ≥0∞, Measurable r ∧ (∀ᵐ x ∂μD, r x < ∞) ∧ ν = μD.withDensity r := by
      intro ν hν hle
      have := hν
      refine ⟨ν.rnDeriv μD, Measure.measurable_rnDeriv _ _, Measure.rnDeriv_lt_top _ _, ?_⟩
      have := Measure.haveLebesgueDecomposition_add ν μD
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        zero_add] at this
    have hle₁ : ∀ i, μ₁ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_self_add
    have hle₂ : ∀ i, μ₂ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_add_self
    choose r₁ hr₁m hr₁lt hr₁ using fun i => hRN (μ₁ i) (hμ₁ i) (hle₁ i)
    choose r₂ hr₂m hr₂lt hr₂ using fun i => hRN (μ₂ i) (hμ₂ i) (hle₂ i)
    -- the density field `H`
    obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → D → ℝ, ∀ i x, c i x = (r₁ i x).toReal - (r₂ i x).toReal :=
      ⟨fun i x => (r₁ i x).toReal - (r₂ i x).toReal, fun _ _ => rfl⟩
    have hcm : ∀ i, Measurable (c i) := fun i => by
      have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
      rw [this]
      exact (hr₁m i).ennreal_toReal.sub (hr₂m i).ennreal_toReal
    obtain ⟨H, hH⟩ : ∃ H : D → Euclid (m + 1), ∀ x, H x = ∑ i, c i x • b i :=
      ⟨fun x => ∑ i, c i x • b i, fun _ => rfl⟩
    have hHm : Measurable H := by
      have : H = fun x => ∑ i, c i x • b i := funext hH
      rw [this]
      exact Finset.measurable_sum _ fun i _ => (hcm i).smul_const (b i)
    have hrepD : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = ∫ x : D, inner ℝ (φ x) (H x) ∂μD := by
      intro φ hφ hφc hφD
      rw [hTdecomp φ hφ hφc]
      have hterm : ∀ i, Integrable (fun x : D => c i x * φ x i) μD ∧
          T (fun y => φ y i • b i) = ∫ x : D, c i x * φ x i ∂μD := by
        intro i
        have hgi := hcoord_sm φ i hφ
        have hgc := hcoord_cs φ i hφc
        have hgD := (hcoord_ts φ i).trans hφD
        have I₁ := hintD (μ₁ i) (hμ₁ i) (fun y => φ y i) hgi.continuous hgc hgD
        have I₂ := hintD (μ₂ i) (hμ₂ i) (fun y => φ y i) hgi.continuous hgc hgD
        rw [hrep i (fun y => φ y i) hgi hgc hgD]
        rw [hr₁ i] at I₁ ⊢
        rw [hr₂ i] at I₂ ⊢
        have J₁ := (integrable_withDensity_iff_integrable_smul' (hr₁m i) (hr₁lt i)).1 I₁
        have J₂ := (integrable_withDensity_iff_integrable_smul' (hr₂m i) (hr₂lt i)).1 I₂
        rw [integral_withDensity_eq_integral_toReal_smul (hr₁m i) (hr₁lt i),
          integral_withDensity_eq_integral_toReal_smul (hr₂m i) (hr₂lt i), ← integral_sub J₁ J₂]
        have e : (fun x : D => c i x * φ x i) =
            fun x : D => (r₁ i x).toReal • φ x i - (r₂ i x).toReal • φ x i := by
          funext x
          rw [hc, smul_eq_mul, smul_eq_mul, sub_mul]
        rw [e]
        exact ⟨J₁.sub J₂, rfl⟩
      rw [Finset.sum_congr rfl fun i _ => (hterm i).2,
        ← integral_finsetSum _ fun i _ => (hterm i).1]
      congr 1
      funext x
      rw [hH, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, hbinner]
    -- normalization to a unit field
    obtain ⟨ν', hν'⟩ : ∃ ν' : D → Euclid (m + 1), ∀ x,
        ν' x = if H x = 0 then b 0 else ‖H x‖⁻¹ • H x :=
      ⟨fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x, fun _ => rfl⟩
    have hν'm : Measurable ν' := by
      have : ν' = fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x := funext hν'
      rw [this]
      exact Measurable.ite (measurableSet_eq_fun hHm measurable_const) measurable_const
        (hHm.norm.inv.smul hHm)
    have hν'1 : ∀ x, ‖ν' x‖ = 1 := by
      intro x
      rw [hν']
      split_ifs with h
      · exact hb1 0
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    have hHν : ∀ (v : Euclid (m + 1)) (x : D),
        (‖H x‖₊ : ℝ) • inner ℝ v (ν' x) = inner ℝ v (H x) := by
      intro v x
      rw [hν', coe_nnnorm, smul_eq_mul]
      split_ifs with h
      · rw [h, norm_zero, zero_mul, inner_zero_right]
      · rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_mul]
    obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure D,
        μ' = μD.withDensity (fun x => ((‖H x‖₊ : NNReal) : ℝ≥0∞)) := ⟨_, rfl⟩
    have hμ'K : ∀ K : Set D, IsCompact K → μ' K < ∞ := by
      intro K hK
      have hKm : MeasurableSet K := hK.measurableSet
      have hlt : ∀ (r : D → ℝ≥0∞) (ν : Measure D), Measurable r → IsFiniteMeasureOnCompacts ν →
          ν = μD.withDensity r → IntegrableOn (fun x => (r x).toReal) K μD := by
        intro r ν hr hν hνr
        apply integrable_toReal_of_lintegral_ne_top hr.aemeasurable
        rw [← withDensity_apply _ hKm, ← hνr]
        exact (hν.lt_top_of_isCompact hK).ne
      have hci : ∀ i, IntegrableOn (c i) K μD := by
        intro i
        have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
        rw [this]
        exact (hlt _ _ (hr₁m i) (hμ₁ i) (hr₁ i)).sub (hlt _ _ (hr₂m i) (hμ₂ i) (hr₂ i))
      have hHK : IntegrableOn H K μD := by
        have : H = fun x => ∑ i, c i x • b i := funext hH
        rw [this]
        exact integrable_finsetSum _ fun i _ => (hci i).smul_const (b i)
      rw [hμ', withDensity_apply _ hKm]
      exact hHK.hasFiniteIntegral
    -- push forward to `ℝ^{m+1}`
    refine ⟨Measure.map Subtype.val μ', fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.map_apply measurable_subtype_coe hD.measurableSet.compl]
      have : (Subtype.val ⁻¹' Dᶜ : Set D) = ∅ := by
        ext x
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
        exact x.2
      rw [this, measure_empty]
    · intro K hK hKD
      rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
      exact (hμ'K _ (hsubK K hK hKD)).ne
    · exact Measurable.dite hν'm.neg measurable_const hD.measurableSet
    · intro y
      by_cases hy : y ∈ D
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_left hy, norm_neg, hν'1]
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_right hy, hb1]
    · intro φ hφ hφc hφD
      rw [(MeasurableEmbedding.subtype_coe hD.measurableSet).integral_map]
      have e : (fun x : D => inner ℝ (φ x) ((fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0) x))
          = fun x : D => -inner ℝ (φ x) (ν' x) := by
        funext x
        show inner ℝ (φ x) (if hy : (x : Euclid (m + 1)) ∈ D then -ν' ⟨x, hy⟩ else b 0) =
          -inner ℝ (φ x) (ν' x)
        rw [dite_eq_left x.2, Subtype.coe_eta, inner_neg_right]
      rw [e, integral_neg, neg_neg, hrepD φ hφ hφc hφD, hμ',
        integral_withDensity_eq_integral_smul hHm.nnnorm]
      congr 1
      funext x
      rw [NNReal.smul_def]
      exact (hHν (φ x) x).symm
  obtain ⟨μ, ν, hμD, hμK, hνm, hν1, hsmooth⟩ := hsm_rep
  refine ⟨μ, ν, hμD, hμK, hνm, hν1, ?_⟩
  -- Step 5: `C¹` fields, by mollification
  -- normalized mollifiers
  have hmoll : ∀ r : ℝ, 0 < r → ∃ ρ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball 0 r := by
    intro r hr
    let B : ContDiffBump (0 : Euclid (m + 1)) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hBs : HasCompactSupport B := B.hasCompactSupport
    have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
    have hI : 0 < ∫ x, B x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
      exact measure_ball_pos volume 0 hr
    refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
      fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
    · exact (support_mul_subset_right _ _).trans B.support_eq.subset
  have hprec : ContinuousLinearMap.precompR (Euclid (m + 1))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1)) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ]
        (Euclid (m + 1) →L[ℝ] Euclid (m + 1))) := by
    ext x A v
    simp [ContinuousLinearMap.precompR]
  intro φ hφ hφc hφD
  obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hφc hD hφD
  set K' := cthickening δ (tsupport φ) with hK'
  have hK'c : IsCompact K' := IsCompact.cthickening hφc
  have hK'm : MeasurableSet K' := isClosed_cthickening.measurableSet
  -- radii
  obtain ⟨rr, hrr0, hrrδ, hrrlim⟩ : ∃ rr : ℕ → ℝ, (∀ n, 0 < rr n) ∧ (∀ n, rr n ≤ δ) ∧
      Tendsto rr atTop (𝓝 0) := by
    refine ⟨fun n => δ / ((n : ℝ) + 1), fun n => div_pos hδ (by positivity), fun n => ?_, ?_⟩
    · exact div_le_self hδ.le (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose ρ hρs hρc hρ0 hρ1 hρsupp using fun n => hmoll (rr n) (hrr0 n)
  -- mollified fields
  obtain ⟨φn, hφn⟩ : ∃ φn : ℕ → Euclid (m + 1) → Euclid (m + 1),
      ∀ n, φn n = convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨fun n => convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun _ => rfl⟩
  have hφn_sm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φn n) := fun n => by
    rw [hφn]
    exact (hρc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs n)
      hφ.continuous.locallyIntegrable
  have hφn_supp : ∀ n, support (φn n) ⊆ K' := fun n => by
    rw [hφn]
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add (hρsupp n) (subset_tsupport φ)).trans ?_
    rw [ball_add_zero]
    exact (thickening_subset_cthickening _ _).trans (cthickening_mono (hrrδ n) _)
  have hφn_cs : ∀ n, HasCompactSupport (φn n) ∧ tsupport (φn n) ⊆ K' := fun n =>
    ⟨hK'c.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hφn_supp n) hK'c.isClosed),
      closure_minimal (hφn_supp n) hK'c.isClosed⟩
  -- bounds
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M', hM'⟩ := hdφc.bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hφn_bd : ∀ n y, ‖φn n y‖ ≤ Mφ := fun n y => by
    rw [hφn, ← dist_zero_right]
    exact dist_convolution_le hMφ0 (hρsupp n) (hρ0 n) (hρ1 n)
      hφ.continuous.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hMφ x)
  have hsmall : Tendsto (fun n => support (ρ n)) atTop (𝓝 (0 : Euclid (m + 1))).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [hrrlim.eventually (gt_mem_nhds hε)] with n hn
    exact (hρsupp n).trans ((ball_subset_ball hn.le).trans hεt)
  have hφn_lim : ∀ y, Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) := fun y => by
    simp only [hφn]
    exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1) hsmall
      (Eventually.of_forall fun _ => hφ.continuous.aestronglyMeasurable)
      ((hφ.continuous.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- derivatives
  have hdφn : ∀ n y, fderiv ℝ (φn n) y =
      convolution (ρ n) (fderiv ℝ φ) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := fun n y => by
    rw [hφn, ← hprec]
    exact (hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρs n).continuous.locallyIntegrable hφ y).fderiv
  have hdφn_bd : ∀ n y, ‖fderiv ℝ (φn n) y‖ ≤ M' := fun n y => by
    rw [hdφn, ← dist_zero_right]
    exact dist_convolution_le hM'0 (hρsupp n) (hρ0 n) (hρ1 n)
      hdφc.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hM' x)
  have hdφn_lim : ∀ y, Tendsto (fun n => fderiv ℝ (φn n) y) atTop (𝓝 (fderiv ℝ φ y)) :=
    fun y => by
      simp only [hdφn]
      exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1)
        hsmall (Eventually.of_forall fun _ => hdφc.aestronglyMeasurable)
        ((hdφc.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- convergence of the left side
  have hL : Tendsto (fun n => T (φn n)) atTop (𝓝 (T φ)) := by
    simp only [hT]
    refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ => ‖trc‖ * M')
      (fun n => (trc.continuous.comp ((hφn_sm n).continuous_fderiv (by simp))).aestronglyMeasurable)
      ?_ (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · exact ((integrable_indicator_iff hK'm).2
        (integrableOn_const hK'c.measure_lt_top.ne)).restrict
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        exact (trc.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hdφn_bd n y) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        have : fderiv ℝ (φn n) y = 0 :=
          notMem_support.1 fun h => hy ((hφn_cs n).2 (support_fderiv_subset ℝ h))
        rw [this, map_zero, norm_zero]
    · exact (trc.continuous.tendsto _).comp (hdφn_lim y)
  -- convergence of the right side
  have hR : Tendsto (fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ) atTop
      (𝓝 (-∫ y, inner ℝ (φ y) (ν y) ∂μ)) := by
    refine Tendsto.neg (tendsto_integral_of_dominated_convergence (K'.indicator fun _ => Mφ)
      (fun n => (Continuous.measurable2 continuous_inner (hφn_sm n).continuous.measurable
        hνm).aestronglyMeasurable) ?_ (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_))
    · exact (integrable_indicator_iff hK'm).2
        (integrableOn_const (hμK K' hK'c hδD))
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hν1, mul_one]
        exact hφn_bd n y
      · rw [indicator_of_notMem hy]
        have : φn n y = 0 := notMem_support.1 fun h => hy (hφn_supp n h)
        rw [this, inner_zero_left, norm_zero]
    · exact (hφn_lim y).inner tendsto_const_nhds
  have hLR : (fun n => T (φn n)) = fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ := by
    funext n
    exact hsmooth (φn n) (hφn_sm n) (hφn_cs n).1 ((hφn_cs n).2.trans hδD)
  rw [hLR] at hL
  exact tendsto_nhds_unique hL hR
/-- **Differentiation of the unit normal** (Simon Ch. 3, (4.2); Ch. 1, 3.23): if `μ` is carried
by the open set `D` and is finite on compact subsets of `D`, then for `μ`-a.e. `y` the averages of
the bounded Borel field `ν` over `B̄_ρ(y)` tend to `ν(y)` as `ρ ↓ 0`.  Exhaust `D` by the compact
sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ)`; for the finite measure `μ⌞K a b` this is Mathlib's
Lebesgue–Besicovitch differentiation theorem along closed balls (`ae_tendsto_average` for
`Besicovitch.vitaliFamily`, with `Besicovitch.tendsto_filterAt`), and near a point of `D` the
averages for `μ` and for `μ⌞K a b` coincide. -/
theorem Submission.codim1_rdo_dg_normal_average_ae : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → ∀ᵐ y ∂μ, y ∈ D ∧ Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 (ν y)) := by
  intro m D μ ν hD hDc hK hν hν1
  -- the compact sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ) ⊆ D`
  let K : ℕ → ℕ → Set (Euclid (m + 1)) := fun a b =>
    closedBall 0 a \ thickening (1 / ((b : ℝ) + 1)) Dᶜ
  have hKc : ∀ a b, IsCompact (K a b) := fun a b =>
    (isCompact_closedBall _ _).diff isOpen_thickening
  have hKD : ∀ a b, K a b ⊆ D := fun a b x hx => by
    by_contra hxD
    exact hx.2 (self_subset_thickening (by positivity) _ hxD)
  -- Besicovitch differentiation of `ν` for the finite measures `μ⌞K a b`
  have hdiff : ∀ a b, ∀ᵐ y ∂μ, y ∈ K a b → Tendsto
      (fun ρ : ℝ => ⨍ z in closedBall y ρ, ν z ∂(μ.restrict (K a b))) (𝓝[>] 0) (𝓝 (ν y)) := by
    intro a b
    have : IsFiniteMeasure (μ.restrict (K a b)) :=
      isFiniteMeasure_restrict.2 (hK _ (hKc a b) (hKD a b))
    have hint : Integrable ν (μ.restrict (K a b)) :=
      Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun y => (hν1 y).le)
    have h := (Besicovitch.vitaliFamily (μ.restrict (K a b))).ae_tendsto_average
      hint.locallyIntegrable
    rw [ae_restrict_iff' (hKc a b).isClosed.measurableSet] at h
    filter_upwards [h] with y hy hyK
    exact (hy hyK).comp (Besicovitch.tendsto_filterAt _ y)
  -- `μ`-a.e. point lies in `D`
  have hDae : ∀ᵐ y ∂μ, y ∈ D := by
    have h := compl_mem_ae_iff.2 hDc
    rwa [compl_compl] at h
  filter_upwards [hDae, ae_all_iff.2 fun a => ae_all_iff.2 (hdiff a)] with y hyD hy
  refine ⟨hyD, ?_⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD y hyD
  obtain ⟨a, ha⟩ := exists_nat_ge (‖y‖ + 1)
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hε)
  -- `B̄_ρ(y) ⊆ K a b` for `ρ < min 1 (ε / 2)`
  have hsub : ∀ ρ : ℝ, ρ < 1 → ρ < ε / 2 → closedBall y ρ ⊆ K a b := by
    intro ρ hρ1 hρε z hz
    refine ⟨?_, fun hzt => ?_⟩
    · rw [mem_closedBall_zero_iff]
      have := norm_le_of_mem_closedBall hz
      linarith
    · obtain ⟨w, hwD, hzw⟩ := mem_thickening_iff.1 hzt
      apply hwD
      apply hεD
      rw [mem_ball]
      have hzy := mem_closedBall.1 hz
      rw [dist_comm] at hzw
      calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ < ε := by linarith
  have hyK : y ∈ K a b := hsub 0 one_pos (half_pos hε) (mem_closedBall_self le_rfl)
  -- for small `ρ` the averages for `μ⌞K a b` and for `μ` over `B̄_ρ(y)` coincide
  refine (hy a b hyK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (half_pos hε))] with ρ hρ
  have hρK := hsub ρ (hρ.2.trans_le (min_le_left _ _)) (hρ.2.trans_le (min_le_right _ _))
  rw [setAverage_eq, measureReal_def, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hρK, Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hρK]
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

end Submission

end GMT.Ch07
