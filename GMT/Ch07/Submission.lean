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

/-- A `0`-dimensional integer multiplicity carrier is finite on compact `K ⊆ U` (Simon 6.3.1,
`n = 0`): `H⁰ = μHE[0]` gives every point mass `1` and `θ ≥ 1` on `M`, so
`H⁰(M ∩ K) ≤ ∫_{M ∩ K} θ dH⁰ < ∞`, while an infinite `M ∩ K` has `N`-point subsets of
`H⁰`-measure `N` for every `N`. -/
theorem Submission.dtc_dim_zero_carrier_finite : ∀ (P : ℕ) (U K : Set (Euclid P)) (R : IMRep U 0), IsCompact K → K ⊆ U → (R.carrier ∩ K).Finite := by
  intro P U K R hK hKU
  -- `H⁰(M ∩ K) ≤ ∫_{M ∩ K} θ dH⁰ < ∞`, as `θ ≥ 1` on `M`
  have hfin : μHE[0] (R.carrier ∩ K) ≠ ∞ := by
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R.measurableSet_carrier.inter hK.isClosed.measurableSet)
      fun x hx => by exact_mod_cast R.mult_pos x hx.1
  -- an infinite `M ∩ K` contains `N` points, of `H⁰`-measure `N > H⁰(M ∩ K)`
  by_contra hinf
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin
  obtain ⟨F, hF, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf N
  refine hN.not_ge ?_
  calc (N : ℝ≥0∞) = ∑ x ∈ F, μHE[0] ({x} : Set (Euclid P)) := by
        simp [Measure.euclideanHausdorffMeasure_zero, hcard]
    _ = μHE[0] (F : Set (Euclid P)) := sum_measure_singleton
    _ ≤ μHE[0] (R.carrier ∩ K) := measure_mono hF
/-- Deleting a point `p ≠ x` from `M` keeps the approximate tangent space of `M` at `x`
(Simon Ch. 3, 1.4).  Choose `a > 0` with `spt f ⊆ B̄_a(0)`.  For `0 < r < |p − x|/a` the point
`η_{x,r}(p)` has norm `|p − x|/r > a`, so `f` vanishes there; the Borel set `η_{x,r}(M)` and its
subset `η_{x,r}(M ∖ {p})` differ at most by `η_{x,r}(p)`, hence carry the same integral of `f`. -/
theorem Submission.dtc_approxTangent_sdiff_singleton : ∀ (P n : ℕ) (M : Set (Euclid P)) (x p : Euclid P) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → x ≠ p → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n (M \ {p}) x Q := by
  intro P n M x p Q hM hxp hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `spt f ⊆ B̄_a(0)` with `a > 0`, and `|p − x| > 0`
  obtain ⟨a, ha, hfa⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  have hd : 0 < ‖p - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp.symm)
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hd ha)] with r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  -- `η_{x,r}(y) = r⁻¹ • (y − x)`
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη]
  -- `f` vanishes at `η_{x,r}(p)`, whose norm `r⁻¹|p − x|` exceeds `a`
  have hfp : f (r⁻¹ • (p - x)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    have h1 := mem_closedBall_zero_iff.mp (hfa hp)
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.1.le, inv_mul_le_iff₀ hr.1] at h1
    have h2 := (lt_div_iff₀ ha).mp hr.2
    linarith
  -- `η_{x,r}(M)` is Borel: it is the preimage of `M` under `y ↦ x + r • y`
  have hmeas : MeasurableSet ((fun y => r⁻¹ • (y - x)) '' M) := by
    have himg : (fun y => r⁻¹ • (y - x)) '' M = (fun y => x + r • y) ⁻¹' M := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [smul_smul, mul_inv_cancel₀ hr0] using hz
      · intro hy
        exact ⟨x + r • y, hy, by simp [smul_smul, inv_mul_cancel₀ hr0]⟩
    rw [himg]
    exact hM.preimage (by fun_prop)
  -- `η_{x,r}(M) ∖ η_{x,r}(M ∖ {p}) ⊆ {η_{x,r}(p)}`, where `f` vanishes
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas (image_mono Set.sdiff_subset) ?_
  rintro _ ⟨⟨z, hz, rfl⟩, hy⟩
  by_cases hzp : z = p
  · subst hzp
    exact hfp
  · exact absurd ⟨z, ⟨hz, hzp⟩, rfl⟩ hy

/-- Deleting a point `p ∈ M` from a `0`-dimensional triple `R = (M, θ, ξ)` (Simon 6.3.1 with
`n = 0`).  `R' = (M ∖ {p}, θ, ξ)` is again a triple in `U`; off `p` its approximate tangent spaces
are those of `M`.  As `H⁰{p} = 1`, `H⁰⌞M = H⁰⌞(M ∖ {p}) + δ_p`, so `μ_R = μ_{R'} + θ(p) δ_p`.
The integrand `θ ⟨ω, ξ⟩` vanishes off `spt ω` and `M ∩ spt ω` is finite, so it is integrable on
`M` and splitting `∫_M = ∫_{M ∖ {p}} + ∫_{{p}}` gives `τ_R(ω) = τ_{R'}(ω) + θ(p) ⟨ω(p), ξ(p)⟩`. -/
theorem Submission.dtc_dim_zero_erase_point : ∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0) (p : Euclid P), p ∈ R.carrier → ∃ R' : IMRep U 0, R'.carrier = R.carrier \ {p} ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ R.measure = R'.measure + (R.mult p : ℝ≥0∞) • Measure.dirac p ∧ ∀ ω : TestFormOn U 0, R.action (ω : DifferentialForm (Euclid P) 0) = R'.action (ω : DifferentialForm (Euclid P) 0) + (R.mult p : ℝ) * R.orient p ((ω : DifferentialForm (Euclid P) 0) p) := by
  intro P U R p hp
  -- `H⁰{y} = 1`, as `μHE[0] = μH[0]`
  have hH : ∀ y : Euclid P, μHE[0] ({y} : Set (Euclid P)) = 1 := fun y => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  -- `M = (M ∖ {p}) ∪ {p}`, a disjoint union of Borel sets
  have hMp : MeasurableSet (R.carrier \ {p}) :=
    R.measurableSet_carrier.diff (measurableSet_singleton p)
  have hsplit : R.carrier \ {p} ∪ {p} = R.carrier :=
    Set.sdiff_union_of_subset (Set.singleton_subset_iff.mpr hp)
  have hdisj : Disjoint (R.carrier \ {p}) {p} := Set.disjoint_sdiff_left
  -- orientation: `H⁰`-a.e. `x ∈ M ∖ {p}` has `x ≠ p`, so `TₓM = Tₓ(M ∖ {p})`
  have horients : ∀ᵐ x ∂(μHE[0].restrict (R.carrier \ {p})), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt 0 (R.carrier \ {p}) x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.sdiff_subset R.orients,
      ae_restrict_mem hMp] with x hx hxM
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, Submission.dtc_approxTangent_sdiff_singleton P 0 R.carrier x p Q
      R.measurableSet_carrier hxM.2 hQ, hξ⟩
  refine ⟨{ carrier := R.carrier \ {p}
            mult := R.mult
            orient := R.orient
            measurableSet_carrier := hMp
            carrier_subset := Set.sdiff_subset.trans R.carrier_subset
            rectifiable := R.rectifiable.mono Set.sdiff_subset
            measurable_mult := R.measurable_mult
            mult_pos := fun x hx => R.mult_pos x hx.1
            locallyIntegrable_mult := fun K hK hKU =>
              ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU)
                (lintegral_mono_set (Set.inter_subset_inter_left K Set.sdiff_subset))
            aestronglyMeasurable_orient := R.aestronglyMeasurable_orient.mono_measure
              (Measure.restrict_mono Set.sdiff_subset le_rfl)
            orients := horients }, rfl, rfl, rfl, ?_, fun ω => ?_⟩
  · -- `H⁰⌞M = H⁰⌞(M ∖ {p}) + δ_p` and `δ_p.withDensity θ = θ(p) δ_p`
    have hres : μHE[0].restrict R.carrier =
        μHE[0].restrict (R.carrier \ {p}) + Measure.dirac p := by
      conv_lhs => rw [← hsplit]
      rw [Measure.restrict_union hdisj (measurableSet_singleton p), Measure.restrict_singleton,
        hH p, one_smul]
    show (μHE[0].restrict R.carrier).withDensity (fun x => (R.mult x : ℝ≥0∞)) =
      (μHE[0].restrict (R.carrier \ {p})).withDensity (fun x => (R.mult x : ℝ≥0∞)) +
        (R.mult p : ℝ≥0∞) • Measure.dirac p
    rw [hres, withDensity_add_measure, dirac_withDensity]
  · -- `g = θ ξ(ω)` vanishes off `spt ω`, and `M ∩ spt ω` is finite, so `g` is integrable on `M`
    have hfin : (R.carrier ∩ tsupport (ω : DifferentialForm (Euclid P) 0)).Finite :=
      Submission.dtc_dim_zero_carrier_finite P U _ R ω.property.1.2 ω.property.2
    have hint : IntegrableOn (fun x => (R.mult x : ℝ) *
        R.orient x ((ω : DifferentialForm (Euclid P) 0) x)) R.carrier μHE[0] := by
      refine IntegrableOn.of_forall_sdiff_eq_zero
        (s := R.carrier ∩ tsupport (ω : DifferentialForm (Euclid P) 0)) ?_
        R.measurableSet_carrier ?_
      · rw [← Set.biUnion_of_singleton (R.carrier ∩ tsupport (ω : DifferentialForm (Euclid P) 0))]
        exact (integrableOn_finite_biUnion hfin).mpr fun y _ =>
          integrableOn_singleton (hx := by rw [hH y]; exact ENNReal.one_lt_top)
      · rintro x ⟨hxM, hxK⟩
        rw [image_eq_zero_of_notMem_tsupport fun h => hxK ⟨hxM, h⟩, map_zero, mul_zero]
    -- split `∫_M = ∫_{M ∖ {p}} + ∫_{{p}}` and evaluate `∫_{{p}} g dH⁰ = H⁰{p} g(p) = g(p)`
    have hsum := setIntegral_union hdisj (measurableSet_singleton p)
      (hint.mono_set Set.sdiff_subset)
      (integrableOn_singleton (hx := by rw [hH p]; exact ENNReal.one_lt_top))
    rw [hsplit, integral_singleton, measureReal_def, hH p, ENNReal.toReal_one, one_smul] at hsum
    exact hsum
/-- The point current `X(ω) = ⟨ω(p), ζ⟩` in `U` (Simon 6.2.1, 6.2.11): test-form convergence to `0`
forces `ω_j(p) → 0`, and every `q ∈ U \ {p}` has a ball `V ∌ p` with `closure V` compact in `U` on
which `X` vanishes, so `spt X ⊆ {p}`. -/
theorem Submission.dtc_point_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (p : Euclid P) (ζ : MultiVector P n), IsOpen U → ∃ X : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, X ω = ζ ((ω : DifferentialForm (Euclid P) n) p)) ∧ X.support ⊆ {p} := by
  intro P n U p ζ hU
  -- test-form convergence to `0` forces `ω_j(p) → 0`
  have heval : ∀ ωs : ℕ → TestFormOn U n, TestFormOnConverges ωs 0 →
      Tendsto (fun j => ((ωs j : TestFormOn U n) : DifferentialForm (Euclid P) n) p) atTop
        (𝓝 0) := by
    rintro ωs ⟨K, -, -, hsupp, -, hderiv⟩
    by_cases hpK : p ∈ K
    · -- the `0`-th derivatives converge uniformly on `K ∋ p`; undo `iteratedFDeriv ℝ 0`
      have h0 := ((continuousMultilinearCurryFin0 ℝ (Euclid P)
        (Covector (Euclid P) n)).continuous.tendsto _).comp ((hderiv 0).tendsto_at hpK)
      simpa [Function.comp_def, iteratedFDeriv_zero_eq_comp] using h0
    · -- `p ∉ K ⊇ tsupport ω_j`, so `ω_j(p) = 0` for every `j`
      have hz : ∀ j, ((ωs j : TestFormOn U n) : DifferentialForm (Euclid P) n) p = 0 := fun j =>
        image_eq_zero_of_notMem_tsupport fun hp => hpK (hsupp j hp)
      simp only [hz]
      exact tendsto_const_nhds
  -- the linear functional `ω ↦ ζ(ω(p))`, continuous by `heval`
  refine ⟨⟨{ toFun := fun ω => ζ ((ω : DifferentialForm (Euclid P) n) p)
             map_add' := fun ω η => by simp
             map_smul' := fun c ω => by simp }, fun ωs h => ?_⟩, fun ω => rfl, ?_⟩
  · simpa [Function.comp_def] using (ζ.continuous.tendsto 0).comp (heval ωs h)
  -- support: each `q ∈ U \ {p}` lies in `ball q (min ε (dist q p) / 2)`, where `X` vanishes
  · intro q hq
    by_contra hqp
    obtain ⟨hqU, hqZ⟩ := hq
    apply hqZ
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU q hqU
    have hm : 0 < min ε (dist q p) := lt_min hε (dist_pos.2 hqp)
    have hr : 0 < min ε (dist q p) / 2 := half_pos hm
    have hrε : min ε (dist q p) / 2 < ε := (half_lt_self hm).trans_le (min_le_left _ _)
    have hrd : min ε (dist q p) / 2 < dist q p := (half_lt_self hm).trans_le (min_le_right _ _)
    refine Set.mem_sUnion_of_mem (mem_ball_self hr) ⟨isOpen_ball, ?_, ?_, ?_⟩
    · exact (isCompact_closedBall q _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrε).trans hεU)
    · intro ω hω
      have hp : p ∉ tsupport (ω : DifferentialForm (Euclid P) n) := fun hp => by
        have h := mem_ball.1 (hω hp)
        rw [dist_comm] at h
        linarith
      show ζ _ = 0
      rw [image_eq_zero_of_notMem_tsupport hp, map_zero]
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
/-- **An integer multiplicity triple essentially carried by a compact set moves to any domain
containing it** (step 6.6 of the localization in the proof of Simon 7.3.1; Simon 6.3.1,
chapter-06.txt lines 733–753).  If `R = (M, θ, ξ)` is an `IMRep` in `V`, `K ⊆ V ∩ U` is compact
and `Hⁿ(M \ K) = 0`, then `(M ∩ K, θ, ξ)` is an `IMRep` in `U` with the same action: `M ∩ K` and
`M` differ by the `Hⁿ`-null set `M \ K`, so `Hⁿ⌞(M ∩ K) = Hⁿ⌞M`; `∫_{M ∩ K} θ dHⁿ < ∞` since
`K ⊆ V` is compact; and `M ∩ K` has the approximate tangent planes of `M`
(`dtc_approxTangent_of_null_diff` with the open set `ℝᴾ`). -/
theorem Submission.dtc_imrep_of_null_off_compact : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (R : IMRep V n), IsCompact K → K ⊆ V → K ⊆ U → μHE[n] (R.carrier \ K) = 0 → ∃ R' : IMRep U n, R'.carrier ⊆ K ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action ω := by
  intro P n U V K R hK hKV hKU hnull
  have hsub : R.carrier ∩ K ⊆ R.carrier := inter_subset_left
  have hdiff : R.carrier \ (R.carrier ∩ K) = R.carrier \ K := Set.sdiff_self_inter
  -- `M ∩ K =ᵐ M`: `(M ∩ K) \ M = ∅` and `M \ (M ∩ K) = M \ K` is `Hⁿ`-null.
  have hrestr : μHE[n].restrict (R.carrier ∩ K) = μHE[n].restrict R.carrier := by
    refine Measure.restrict_congr_set (ae_eq_set.2 ⟨?_, hdiff ▸ hnull⟩)
    rw [Set.sdiff_eq_empty.2 hsub]
    exact measure_empty
  refine ⟨
    { carrier := R.carrier ∩ K
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := R.measurableSet_carrier.inter hK.isClosed.measurableSet
      carrier_subset := inter_subset_right.trans hKU
      rectifiable := R.rectifiable.mono hsub
      measurable_mult := R.measurable_mult
      mult_pos := fun x hx => R.mult_pos x hx.1
      -- `∫_{(M ∩ K) ∩ C} θ ≤ ∫_{M ∩ K} θ < ∞`, using only that `K ⊆ V` is compact.
      locallyIntegrable_mult := fun _ _ _ => ne_top_of_le_ne_top
        (R.locallyIntegrable_mult K hK hKV) (lintegral_mono_set inter_subset_left)
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hsub le_rfl)
      -- a.e. on `M ∩ K`, the plane `Q` oriented by `ξ(x)` is also `Tₓ(M ∩ K)`.
      orients := (ae_restrict_of_ae_restrict_of_subset hsub R.orients).mono
        fun x ⟨Q, hQ, hξ⟩ => ⟨Q, Submission.dtc_approxTangent_of_null_diff P n R.carrier
          (R.carrier ∩ K) univ x Q hsub isOpen_univ (mem_univ x)
          (by rw [inter_univ, hdiff]; exact hnull) hQ, hξ⟩ },
    inter_subset_right, fun ω => ?_⟩
  -- the actions are integrals of the same function against the same measure
  change ∫ x in R.carrier ∩ K, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n] =
    ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (ω x) ∂μHE[n]
  rw [hrestr]
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

/-- **Extension by zero** (steps 6.2–6.6 of the localization in the proof of Simon 7.3.1).  Let
`V ⊆ U` be open, `K ⊆ V` compact and `X = τ(M, θ, ξ) ∈ 𝒟ₙ(V)` with `Hⁿ(M \ K) = 0`.  Move the
representation to `U` with carrier in `K` and let `Y ∈ 𝒟ₙ(U)` be the current it defines.  Then
`Y⌞V = X`; `Y` kills every form whose support misses `K`, so `spt Y = K \ Z_Y` is a compact subset
of `K`; and if `∂X = 0`, then for a cutoff `χ ∈ C^∞_c(V)` equal to `1` near `K` we get
`∂Y(ω) = Y(dω) = X(d(χω)) = ∂X(χω) = 0`, since `d(χω) = dω` near the carrier. -/
theorem Submission.dtc_extend_by_zero : ∀ (P n : ℕ) (U V K : Set (Euclid P)) (hVU : V ⊆ U) (X : GeometricCurrentOn V n) (R : IMRep V n), IsOpen U → IsOpen V → IsCompact K → K ⊆ V → R.Represents X → μHE[n] (R.carrier \ K) = 0 → ∃ Y : GeometricCurrentOn U n, Y.restrictDomain hVU = X ∧ Y.support ⊆ K ∧ IsCompact Y.support ∧ (BoundaryVanishes X → BoundaryVanishes Y) ∧ IsIntegerMultiplicity Y := by
  intro P n U V K hVU X R hU hV hK hKV hRX hnull
  -- Step 1: move `R` to `U`, with carrier in `K` and the same action
  obtain ⟨R', hR'K, hR'R⟩ :=
    Submission.dtc_imrep_of_null_off_compact P n U V K R hK hKV (hKV.trans hVU) hnull
  -- Step 2: `Y = τ(R')`, which is integer multiplicity
  obtain ⟨Y, hY⟩ := Submission.dtc_imrep_current P n U R'
  -- Step 4: `Y` vanishes on forms whose support misses `K`
  have hvan : ∀ ω : TestFormOn U n,
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → Y ω = 0 := by
    intro ω hω
    rw [hY ω, IMRep.action]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.mp hω (hR'K hx)), map_zero,
      mul_zero]
  -- Step 5: `spt Y ⊆ K`; a point of `U \ K` has a ball `W ⊂⊂ U \ K` on which `Y` vanishes
  have hspt : Y.support ⊆ K := by
    rintro q ⟨hqU, hqZ⟩
    by_contra hqK
    obtain ⟨r, hr, hrUK⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) q ⟨hqU, hqK⟩
    have hcl : closure (ball q (r / 2)) ⊆ ball q r :=
      closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hr))
    refine hqZ (mem_sUnion.mpr ⟨ball q (r / 2), ⟨isOpen_ball,
      (isCompact_closedBall q (r / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall,
      hcl.trans (hrUK.trans sdiff_subset), fun ω hω => hvan ω ?_⟩, mem_ball_self (half_pos hr)⟩)
    exact disjoint_sdiff_left.mono_left (hω.trans (subset_closure.trans (hcl.trans hrUK)))
  -- Step 6: `spt Y = K \ Z_Y` is compact
  have hcpt : IsCompact Y.support := by
    have heq : Y.support = K \ Y.zeroRegion :=
      Subset.antisymm (fun x hx => ⟨hspt hx, hx.2⟩) fun x hx => ⟨hVU (hKV hx.1), hx.2⟩
    rw [heq]
    exact hK.diff Y.isOpen_zeroRegion
  -- Step 3: `Y⌞V = X`, since `R'` and `R` have the same action
  have hres : Y.restrictDomain hVU = X := by
    ext ω
    rw [GeometricCurrentOn.restrictDomain_apply, hY (testFormOnInclusion hVU n ω),
      testFormOnInclusion_coe, hR'R, hRX ω]
  refine ⟨Y, hres, hspt, hcpt, ?_, ⟨R', hY⟩⟩
  -- Step 7: `∂X = 0 → ∂Y = 0` (trivial in degree `0`)
  rcases n with _ | m
  · exact fun _ => trivial
  intro hX
  change X.boundary = 0 at hX
  change Y.boundary = 0
  -- Step 7.1: a cutoff `χ ∈ C^∞_c(V)` equal to `1` on an open set `O ⊇ K`
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
  obtain ⟨χ, hχ1, hχ0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Euclid P)) (n := ⊤) hK.isClosed
    ((self_subset_thickening hδ K).trans (thickening_subset_interior_cthickening δ K))
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := contMDiff_iff_contDiff.mp χ.contMDiff
  have hχsupp : tsupport χ ⊆ cthickening δ K :=
    closure_minimal (fun x hx => by_contra fun h => hx (hχ0 x h)) isClosed_cthickening
  have hχc : HasCompactSupport χ :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) hχsupp
  obtain ⟨O, hO, hKO, hOχ⟩ := mem_nhdsSet_iff_exists.mp hχ1
  -- Step 7.2: `χω ∈ 𝒟^m(V)` for `ω ∈ 𝒟^m(U)`
  have hcut : ∀ ω : TestFormOn U m,
      (fun x => χ x • (ω : DifferentialForm (Euclid P) m) x) ∈ testFormOnSubmodule V m :=
    fun ω => ⟨⟨hχs.smul ω.property.1.1, hχc.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans (hχsupp.trans hδV)⟩
  -- Step 7.4: `∂Y(ω) = R'(dω) = R'(d(χω)) = R(d(χω)) = X(d(χω)) = ∂X(χω) = 0`
  ext ω
  rw [GeometricCurrentOn.zero_apply, GeometricCurrentOn.boundary_apply,
    hY (exteriorDerivativeTestOn U m ω)]
  have hd : R'.action (exteriorDerivativeTestOn U m ω : DifferentialForm (Euclid P) (m + 1)) =
      R'.action (exteriorDerivativeTestOn V m ⟨_, hcut ω⟩ :
        DifferentialForm (Euclid P) (m + 1)) := by
    unfold IMRep.action
    refine setIntegral_congr_fun R'.measurableSet_carrier fun x hx => ?_
    -- Step 7.3: `χω = ω` near `x ∈ M' ⊆ K ⊆ O`, so `d(χω)(x) = dω(x)`
    have hloc : (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) =ᶠ[𝓝 x]
        (ω : DifferentialForm (Euclid P) m) :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds (hKO (hR'K hx))) fun y hy => by
        rw [show χ y = 1 from hOχ hy, one_smul]
    show (R'.mult x : ℝ) * R'.orient x (extDeriv (ω : DifferentialForm (Euclid P) m) x) =
      (R'.mult x : ℝ) * R'.orient x
        (extDeriv (fun y => χ y • (ω : DifferentialForm (Euclid P) m) y) x)
    rw [hloc.extDeriv_eq]
  rw [hd, hR'R, ← hRX, ← GeometricCurrentOn.boundary_apply, hX, GeometricCurrentOn.zero_apply]
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
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl
/-- **Every current in `η(U)` is a blow-up**, `η = η_{x,λ}`, `λ > 0` (Simon Ch. 6, 2.23 and 3.9
for `η⁻¹`; used for the minimality of `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt
lines 326–338): every `S' ∈ 𝒟ₙ(η(U))` is `η_{x,λ#}S''` for some `S'' ∈ 𝒟ₙ(U)`, integer
multiplicity whenever `S'` is.  `κ = η_{−λ⁻¹x,λ⁻¹}` inverts `η`, so `κ(η(U)) = U`, and `S''` is
`κ_#S'` restricted to `U`: `dtc_blowUp_testForm_corr` for `η` and for `κ` gives
`η_#S''(ω) = λ⁻ⁿ κ_#S'(ω ∘ η) = λ⁻ⁿ λⁿ S'(ω)`, and a representation of `κ_#S'` in
`κ(η(U)) = U` (`dtc_blowUp_imrep`) represents `S''`. -/
theorem Submission.dtc_blowUp_preimage : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (S' : GeometricCurrentOn (dilation x lam '' U) n), ∃ S'' : GeometricCurrentOn U n, blowUp S'' x lam hlam.ne' = S' ∧ (IsIntegerMultiplicity S' → IsIntegerMultiplicity S'') := by
  intro P n U x lam hlam S'
  have hlam' : 0 < lam⁻¹ := inv_pos.mpr hlam
  -- `κ = η_{−λ⁻¹x,λ⁻¹}`, `κ(z) = x + λz`, is a two-sided inverse of `η = η_{x,λ}`
  have hκη : ∀ y, dilation (-(lam⁻¹ • x)) lam⁻¹ (dilation x lam y) = y := fun y => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hηκ : ∀ z, dilation x lam (dilation (-(lam⁻¹ • x)) lam⁻¹ z) = z := fun z => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hdom : dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) = U := by
    rw [image_image]
    simp only [hκη, image_id']
  have hUV : U ⊆ dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) := hdom.superset
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hblow' := (Submission.dtc_blowUp_testForm_corr P n (dilation x lam '' U)
    (-(lam⁻¹ • x)) lam⁻¹ hlam').2.2
  -- `S'' := κ_#S'`, restricted from `κ(η(U)) = U` to `U`
  refine ⟨(blowUp S' (-(lam⁻¹ • x)) lam⁻¹ hlam'.ne').restrictDomain hUV, ?_, ?_⟩
  · -- `η_#S''(ω) = λ⁻ⁿ S''(ω ∘ η)` and `κ_#S'(ω ∘ η) = λⁿ S'(ω)`, as `ω ∘ η ∘ κ = ω`
    ext ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow _ ω ω' hω', GeometricCurrentOn.restrictDomain_apply,
      hblow' S' (testFormOnInclusion hUV n ω') ω fun z => by
        rw [testFormOnInclusion_coe, hω', hηκ],
      ← mul_assoc, ← mul_pow, inv_inv, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]
  · -- a representation of `κ_#S'` in `κ(η(U)) = U` is one in `U`, and it represents `S''`
    rintro ⟨R₁, hR₁⟩
    obtain ⟨R₂, hR₂, -⟩ := Submission.dtc_blowUp_imrep P n (dilation x lam '' U) S'
      (-(lam⁻¹ • x)) lam⁻¹ hlam' R₁ hR₁
    exact ⟨{ R₂ with
        carrier_subset := R₂.carrier_subset.trans hdom.subset
        locallyIntegrable_mult := fun K hK hKU =>
          R₂.locallyIntegrable_mult K hK (hKU.trans hUV) },
      fun ω => hR₂ (testFormOnInclusion hUV n ω)⟩

/-- **Blow-ups preserve minimality** (Simon 7.1.1, chapter-07.txt lines 12–18, for `η = η_{x,λ}`,
`λ > 0`; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337): if `T` is
minimizing in `A`, then `η_#T` is minimizing in `η(A)`.

`η_#T` is integer multiplicity (`dtc_blowUp_imrep`).  A competitor `S'` for `η_#T` on
`W' ⊂⊂ η(U)` is `η_#S''` with `S''` integer multiplicity (`dtc_blowUp_preimage`), and `S''` is a
competitor for `T` on `W = η⁻¹(W') ⊂⊂ U`: `∂S'' = ∂T` and
`spt(S'' − T) = η⁻¹(spt(S' − η_#T)) ⊆ A ∩ W` (`dtc_blowUp_algebra`).  So
`M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')` (`dtc_blowUp_massOn_image`). -/
theorem Submission.dtc_blowUp_isMinimizingIn : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A) := by
  intro P n U A T x lam hlam hT
  obtain ⟨⟨R, hR⟩, hmin⟩ := hT
  obtain ⟨hsub, hinj, hspt, hbdry⟩ := Submission.dtc_blowUp_algebra P U x lam hlam
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨?_, fun W' S' hW'o hW'c hS'im hS'bd hS'c hS'A => ?_⟩
  · -- `η_#T` is integer multiplicity
    obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P n U T x lam hlam R hR
    exact ⟨R', hR'⟩
  -- `S' = η_#S''` with `S''` integer multiplicity
  obtain ⟨S'', rfl, hS''im⟩ := Submission.dtc_blowUp_preimage P n U x lam hlam S'
  -- `W = η⁻¹(W')` is open and `W ⊂⊂ U`, since `closure W = η⁻¹(closure W')` and `η⁻¹(η(U)) = U`
  have hWo : IsOpen (dilation x lam ⁻¹' W') := by
    rw [← he]
    exact hW'o.preimage e.continuous
  have hWc : CompactlyContained (dilation x lam ⁻¹' W') U := by
    obtain ⟨hc, hsub'⟩ := hW'c
    rw [← he] at hsub' ⊢
    refine ⟨?_, ?_⟩ <;> rw [← e.preimage_closure]
    · exact e.isCompact_preimage.2 hc
    · exact (preimage_mono hsub').trans (e.preimage_image U).subset
  -- `∂S'' = ∂T`: `η_#(∂S'') = ∂S' = ∂(η_#T) = η_#(∂T)` and `η_#` is injective
  have hbd : SameBoundary S'' T := by
    cases n with
    | zero => trivial
    | succ m =>
      show S''.boundary = T.boundary
      apply hinj
      rw [← hbdry, ← hbdry]
      exact hS'bd
  -- `spt(S' − η_#T) = η(spt(S'' − T))`, so `spt(S'' − T)` is compact and lies in `A ∩ W`
  have hspt' : (blowUp S'' x lam hlam.ne' - blowUp T x lam hlam.ne').support =
      dilation x lam '' (S'' - T).support := by
    rw [← hsub, hspt]
  rw [hspt', ← he] at hS'c hS'A
  have hc : IsCompact (S'' - T).support := e.isCompact_image.1 hS'c
  have hA : (S'' - T).support ⊆ A ∩ dilation x lam ⁻¹' W' := by
    intro y hy
    obtain ⟨⟨a, ha, hay⟩, hyW'⟩ := hS'A (mem_image_of_mem e hy)
    rw [← he]
    exact ⟨e.injective hay ▸ ha, hyW'⟩
  -- `M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')`, as `η(W) = W'`
  have hle := hmin _ S'' hWo hWc (hS''im hS'im) hbd hc hA
  have hW' : dilation x lam '' (dilation x lam ⁻¹' W') = W' := by
    rw [← he]
    exact e.image_preimage W'
  have hmT := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W')
  have hmS := Submission.dtc_blowUp_massOn_image P n U S'' x lam hlam (dilation x lam ⁻¹' W')
  rw [hW'] at hmT hmS
  rw [hmT, hmS]
  gcongr

/-- **Scaling of blow-ups** `η_{x,λ#}T`, `η = η_{x,λ}`, `λ > 0` (proof of Simon 7.3.1,
chapter-07.txt lines 326–338; push-forward 6.2.23 and 6.3.3–6.3.9): (1) the mass scaling
`M_{η(W)}(η_#T) = λ⁻ⁿ M_W(T)` of (1) there (`dtc_blowUp_massOn_image`); (2) a representation
`(M, θ, ξ)` of `T` pushes forward to one of `η_#T` with `μ_{η_#T}(B) = λ⁻ⁿ μ_T(η⁻¹(B))`
(`dtc_blowUp_imrep`); (3) `η_#T` is minimizing in `η(A)` if `T` is minimizing in `A`
(`dtc_blowUp_isMinimizingIn`).  The hypotheses `U` open and `n > 0` are not needed. -/
theorem Submission.dtc_blowUp_scaling : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsOpen U → 0 < n → (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W) ∧ (∀ R : IMRep U n, R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) ∧ (IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)) := by
  intro P n U A T x lam hlam _ _
  exact ⟨Submission.dtc_blowUp_massOn_image P n U T x lam hlam,
    Submission.dtc_blowUp_imrep P n U T x lam hlam,
    Submission.dtc_blowUp_isMinimizingIn P n U A T x lam hlam⟩

/-- **Zero-dimensional minimizing currents vanish** (step 1 of the proof of Simon 7.3.1).  If
`T ∈ 𝒟₀(U)` is minimizing in `A` and `spt T ⊆ A`, then `T = 0`, `spt T = ∅` and `M_W(T) = 0` for
every `W`.  Let `T = τ(M, θ, ξ)`, suppose `p ∈ M` and put `R' = (M \ {p}, θ, ξ)`.  For every open
`V ⊆ U` containing `p`, `M_V(T) = μ_{R'}(V) + θ(p) ≥ 1`, so `p ∈ spt T ⊆ A`.  Deleting `p` gives
the integer multiplicity competitor `S = T − θ(p)ξ(p)δ_p = τ(R')` with `spt(S − T) ⊆ {p}`.  On a
small ball `W ⊂⊂ U` about `p`, `μ_{R'}(W) < ∞` gives
`M_W(S) = μ_{R'}(W) < μ_{R'}(W) + θ(p) = M_W(T)`, contradicting minimality.  Hence `M = ∅` and
`T = 0`. -/
theorem Submission.dtc_dim_zero_eq_zero : ∀ (P : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U 0), IsOpen U → IsMinimizingIn T A → T.support ⊆ A → T = 0 ∧ T.support = ∅ ∧ ∀ W : Set (Euclid P), T.massOn W = 0 := by
  intro P U A T hU hmin hsptA
  obtain ⟨⟨R, hR⟩, hminT⟩ := hmin
  -- a current vanishing on every admissible form of `W` has no mass in `W`
  have hmass_zero : ∀ (S : GeometricCurrentOn U 0) (W : Set (Euclid P)),
      (∀ ω ∈ massAdmissibleOn U 0 W, S ω = 0) → S.massOn W = 0 := by
    intro S W hS
    refine le_antisymm (sSup_le ?_) zero_le
    rintro r ⟨ω, hω, rfl⟩
    show ENNReal.ofReal (S ω) ≤ 0
    rw [hS ω hω, ENNReal.ofReal_zero]
  -- every `y ∈ U` is the centre of a ball `W` with `W ⊂⊂ U`
  have hball : ∀ y ∈ U, ∃ ε > 0, CompactlyContained (ball y ε) U := by
    intro y hy
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU y hy
    have hcl : closure (ball y (ε / 2)) ⊆ closedBall y (ε / 2) := closure_ball_subset_closedBall
    exact ⟨ε / 2, half_pos hε,
      (isCompact_closedBall y (ε / 2)).of_isClosed_subset isClosed_closure hcl,
      hcl.trans ((closedBall_subset_ball (half_lt_self hε)).trans hεU)⟩
  -- the carrier `M` is empty
  have hM : R.carrier = ∅ := by
    by_contra hne
    obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr hne
    have hpU : p ∈ U := R.carrier_subset hp
    have hθ : (R.mult p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (R.mult_pos p hp).ne'
    obtain ⟨R', -, -, -, hmeas, hact⟩ := Submission.dtc_dim_zero_erase_point P U R p hp
    -- `M_V(T) = μ_{R'}(V) + θ(p)` for every open `V ⊆ U` containing `p`
    have hmassV : ∀ V : Set (Euclid P), IsOpen V → V ⊆ U → p ∈ V →
        T.massOn V = R'.measure V + (R.mult p : ℝ≥0∞) := by
      intro V hV hVU hpV
      rw [Submission.dtc_mass_eq_measure P 0 U V T R hU hV hVU hR, hmeas, Measure.add_apply,
        Measure.smul_apply, Measure.dirac_apply_of_mem hpV, smul_eq_mul, mul_one]
    -- `p ∈ spt T ⊆ A`: on an open `V ∋ p` where `T` vanishes, `M_V(T) = 0 < θ(p)`
    have hpA : p ∈ A := by
      refine hsptA ⟨hpU, fun hpZ => ?_⟩
      obtain ⟨V, ⟨hVo, -, hVU, hvan⟩, hpV⟩ := mem_sUnion.mp hpZ
      have h0 := hmass_zero T V fun ω hω => hvan ω hω.1
      rw [hmassV V hVo (subset_closure.trans hVU) hpV] at h0
      exact hθ (add_eq_zero.mp h0).2
    -- the competitor `S = T − θ(p)ξ(p)δ_p` is represented by `R'`, and `S − T = −θ(p)ξ(p)δ_p`
    obtain ⟨X, hX, -⟩ := Submission.dtc_point_current P 0 U p ((R.mult p : ℝ) • R.orient p) hU
    obtain ⟨Y, hY, hYspt⟩ :=
      Submission.dtc_point_current P 0 U p (-((R.mult p : ℝ) • R.orient p)) hU
    have hS : R'.Represents (T - X) := by
      intro ω
      change T ω - X ω = _
      rw [hR ω, hX ω, hact ω, smul_apply, smul_eq_mul, add_sub_cancel_right]
    have hSTY : T - X - T = Y := by
      ext ω
      change T ω - X ω - T ω = Y ω
      rw [hX ω, hY ω, neg_apply, sub_sub_cancel_left]
    have hspt : (T - X - T).support ⊆ {p} := by
      rw [hSTY]
      exact hYspt
    -- minimality on a ball `W ∋ p` with `W ⊂⊂ U`
    obtain ⟨ε, hε, hWcc⟩ := hball p hpU
    have hWU : ball p ε ⊆ U := subset_closure.trans hWcc.2
    have hpW : p ∈ ball p ε := mem_ball_self hε
    have hle := hminT (ball p ε) (T - X) isOpen_ball hWcc ⟨R', hS⟩ trivial
      ((finite_singleton p).subset hspt).isCompact
      (hspt.trans (singleton_subset_iff.mpr ⟨hpA, hpW⟩))
    rw [hmassV _ isOpen_ball hWU hpW,
      Submission.dtc_mass_eq_measure P 0 U _ (T - X) R' hU isOpen_ball hWU hS] at hle
    -- `μ_{R'}(W) < ∞`, since `θ` is locally integrable and `closure W` is compact in `U`
    have hfin : R'.measure (ball p ε) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono (subset_closure (s := ball p ε)))
      rw [IMRep.measure, withDensity_apply _ isClosed_closure.measurableSet,
        Measure.restrict_restrict isClosed_closure.measurableSet, Set.inter_comm]
      exact R'.locallyIntegrable_mult _ hWcc.1 hWcc.2
    exact absurd hle (not_le.mpr (ENNReal.lt_add_right hfin hθ))
  -- with `M = ∅`, `T(ω) = ∫_∅ ⋯ = 0` for every `ω`
  have hT0 : T = 0 := by
    ext ω
    rw [hR ω, GeometricCurrentOn.zero_apply, IMRep.action, hM, Measure.restrict_empty,
      integral_zero_measure]
  subst hT0
  refine ⟨rfl, ?_, fun W => hmass_zero 0 W fun ω _ => rfl⟩
  -- `spt 0 = ∅`: `0` vanishes on a ball `W ⊂⊂ U` about every `y ∈ U`
  refine eq_empty_iff_forall_notMem.mpr fun y hy => hy.2 ?_
  obtain ⟨ε, hε, hWcc⟩ := hball y hy.1
  exact mem_sUnion.mpr ⟨ball y ε, ⟨isOpen_ball, hWcc.1, hWcc.2, fun ω _ => rfl⟩,
    mem_ball_self hε⟩

/-- **Localization away from `spt ∂T`** (proof of Simon 7.3.1, chapter-07.txt lines 335–337:
`∂η_{x,λⱼ #} T = 0` in `B_R(0)` because `x ∉ spt ∂T`).  Let `T ∈ 𝒟ₙ(U)`, `n ≥ 1`, be minimizing in
`A`, `U' = U \ spt ∂T` and `T' = T⌞U'`.  `U' = U ∩ Z_∂` with `Z_∂` the open zero region of `∂T`.
`T'` and `T` agree on forms supported in `U'`, so `M_W(T') = M_W(T)` for `W ⊆ U'`, `spt T' ⊆ spt T`,
and `∂T'(ω) = ∂T(ω) = 0` since `spt ω` misses `spt ∂T` (`dtc_vanish_off_support`).  `T'` is integer
multiplicity.  Given a competitor `S'` for `T'` in `W ⊂⊂ U'`, `X = S' − T'` is integer multiplicity
with `∂X = 0`, and `M_{U' \ K}(X) = 0` for the compact `K = spt X`, so by `dtc_mass_eq_measure` the
carrier of `X` is `Hⁿ`-null off `K`.  Hence `X` extends by zero to `Y ∈ 𝒟ₙ(U)` with `spt Y ⊆ K` and
`∂Y = 0`, and `S = T − ((T − T) − Y) = T + Y` is an integer multiplicity competitor for `T` that
agrees with `S'` on forms supported in `W`: `M_W(T') = M_W(T) ≤ M_W(S) = M_W(S')`. -/
theorem Submission.dtc_localize : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → 0 < n → IsMinimizingIn T A → IsOpen (U \ boundarySupport T) ∧ IsMinimizingIn (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)) A ∧ BoundaryVanishes (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)) ∧ (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)).support ⊆ T.support ∧ ∀ W : Set (Euclid P), W ⊆ U \ boundarySupport T → (T.restrictDomain (Set.sdiff_subset : U \ boundarySupport T ⊆ U)).massOn W = T.massOn W := by
  intro P n U A T hU hn hT
  -- `n = m + 1`, so `spt ∂T = spt (T.boundary)` and `∂T' = 0` means `T'.boundary = 0`
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set U' := U \ boundarySupport T
  have hU'U : U' ⊆ U := Set.sdiff_subset
  set T' := T.restrictDomain hU'U
  -- Step 1 (a): `U' = U \ (U \ Z_∂) = U ∩ Z_∂` is open
  have hU'o : IsOpen U' := by
    show IsOpen (U \ (U \ T.boundary.zeroRegion))
    rw [Set.sdiff_sdiff_right_self]
    exact hU.inter T.boundary.isOpen_zeroRegion
  -- `T'(ω) = T(ω)` for `ω ∈ 𝒟ⁿ(U')`
  have hagree : ∀ ω : TestFormOn U' (m + 1), T (testFormOnInclusion hU'U (m + 1) ω) = T' ω :=
    fun ω => rfl
  -- Step 2 (e): `M_W(T') = M_W(T)` for `W ⊆ U'`
  have hmass : ∀ W : Set (Euclid P), W ⊆ U' → T'.massOn W = T.massOn W := fun W hW =>
    (Submission.dtc_massOn_eq_of_agreeOn P (m + 1) U U' W hU'U T T' hW fun ω _ => hagree ω).symm
  -- Step 5: `T' = τ(M ∩ U', θ, ξ)` is integer multiplicity
  have hT'IM : IsIntegerMultiplicity T' :=
    Submission.dtc_restrictDomain_isIntegerMultiplicity P (m + 1) U U' hU'U T hU'o hT.1
  refine ⟨hU'o, ⟨hT'IM, ?_⟩, ?_, ?_, hmass⟩
  · -- Step 6 (b): a competitor `S'` for `T'` yields a competitor `S` for `T`
    intro W S' hWo hWcc hS' hSB hKc hKAW
    have hWU' : W ⊆ U' := subset_closure.trans hWcc.2
    set X := S' - T'
    set K := X.support
    have hKU' : K ⊆ U' := X.support_subset_domain
    -- Step 6.1: `X` is integer multiplicity, with `∂X = ∂S' − ∂T' = 0`
    obtain ⟨R, hR⟩ :=
      Submission.dtc_isIntegerMultiplicity_sub P (m + 1) U' S' T' hU'o hn hS' hT'IM
    have hXb : BoundaryVanishes X := by
      have hSB' : S'.boundary = T'.boundary := hSB
      show X.boundary = 0
      ext ω
      show S'.boundary ω - T'.boundary ω = 0
      rw [hSB', sub_self]
    -- Step 6.6: `M_{U' \ K}(X) = 0`, as `X` kills every form supported off `K = spt X`
    have hUKo : IsOpen (U' \ K) := hU'o.sdiff hKc.isClosed
    have hX0 : X.massOn (U' \ K) = 0 := by
      unfold GeometricCurrentOn.massOn
      refine le_antisymm (sSup_le ?_) zero_le
      rintro r ⟨ω, hω, rfl⟩
      have h0 : X ω = 0 := Submission.dtc_vanish_off_support P (m + 1) U' X ω
        (Set.disjoint_left.mpr fun x hx hxK => (hω.1 hx).2 hxK)
      simp [h0]
    -- so `∫_{M_X \ K} θ_X dHⁿ = μ_X(U' \ K) = M_{U' \ K}(X) = 0`, and `θ_X ≥ 1` gives
    -- `Hⁿ(M_X \ K) = 0`
    have hμ := Submission.dtc_mass_eq_measure P (m + 1) U' (U' \ K) X R hU'o hUKo
      Set.sdiff_subset hR
    rw [hX0, IMRep.measure, withDensity_apply _ hUKo.measurableSet,
      Measure.restrict_restrict hUKo.measurableSet] at hμ
    have hnull : μHE[m + 1] (R.carrier \ K) = 0 := by
      have hset : R.carrier \ K = (U' \ K) ∩ R.carrier := by
        ext x
        exact ⟨fun hx => ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩, fun hx => ⟨hx.2, hx.1.2⟩⟩
      have hle : ∫⁻ _ in (U' \ K) ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[m + 1] ≤
          ∫⁻ x in (U' \ K) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[m + 1] :=
        setLIntegral_mono' (hUKo.measurableSet.inter R.measurableSet_carrier) fun x hx => by
          exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (R.mult_pos x hx.2))
      rw [hset, ← setLIntegral_one]
      exact le_antisymm (hle.trans hμ.symm.le) zero_le
    -- Steps 6.2–6.6: extend `X` by zero to `Y ∈ 𝒟ₙ(U)` with `spt Y ⊆ K` and `∂Y = 0`
    obtain ⟨Y, hYX, hYK, hYc, hYb, hYIM⟩ :=
      Submission.dtc_extend_by_zero P (m + 1) U U' K hU'U X R hU hU'o hKc hKU' hR hnull
    have hYb' : Y.boundary = 0 := hYb hXb
    -- Step 6.7: `T − T`, `(T − T) − Y` and `S = T − ((T − T) − Y) = T + Y` are integer
    -- multiplicity (`T − T` replaces the zero current of the text)
    set S := T - ((T - T) - Y)
    have hSIM : IsIntegerMultiplicity S :=
      Submission.dtc_isIntegerMultiplicity_sub P (m + 1) U T _ hU hn hT.1
        (Submission.dtc_isIntegerMultiplicity_sub P (m + 1) U (T - T) Y hU hn
          (Submission.dtc_isIntegerMultiplicity_sub P (m + 1) U T T hU hn hT.1 hT.1) hYIM)
    have hSapp : ∀ ω : TestFormOn U (m + 1), S ω = T ω + Y ω := fun ω => by
      show T ω - ((T ω - T ω) - Y ω) = T ω + Y ω
      ring
    -- Step 6.8: `∂S = ∂T` and `S − T = Y`, so `spt(S − T) = spt Y ⊆ K ⊆ A ∩ W` is compact
    have hSB2 : SameBoundary S T := by
      show S.boundary = T.boundary
      ext ω
      rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, hSapp,
        ← GeometricCurrentOn.boundary_apply Y, hYb', GeometricCurrentOn.zero_apply, add_zero]
    have hST : S - T = Y := by
      ext ω
      show S ω - T ω = Y ω
      rw [hSapp]
      ring
    have hmin := hT.2 W S hWo ⟨hWcc.1, hWcc.2.trans hU'U⟩ hSIM hSB2
      (by rw [hST]; exact hYc) (by rw [hST]; exact hYK.trans hKAW)
    -- Step 6.9: `S = T + X = S'` on forms supported in `W ⊆ U'`, so
    -- `M_W(T') = M_W(T) ≤ M_W(S) = M_W(S')`
    have hSW : S.massOn W = S'.massOn W :=
      Submission.dtc_massOn_eq_of_agreeOn P (m + 1) U U' W hU'U S S' hWU' fun ω _ => by
        have hY : Y (testFormOnInclusion hU'U (m + 1) ω) = X ω :=
          congrArg (fun Z : GeometricCurrentOn U' (m + 1) => Z ω) hYX
        rw [hSapp, hY, hagree]
        show T' ω + (S' ω - T' ω) = S' ω
        ring
    rw [hmass W hWU', ← hSW]
    exact hmin
  · -- Step 4 (c): `∂T'(ω) = ∂T(ω) = 0`, as `spt ω ⊆ U'` misses `spt ∂T`
    show T'.boundary = 0
    ext ω
    rw [GeometricCurrentOn.zero_apply, GeometricCurrentOn.boundary_apply, ← hagree]
    have hd : testFormOnInclusion hU'U (m + 1) (exteriorDerivativeTestOn U' m ω) =
        exteriorDerivativeTestOn U m (testFormOnInclusion hU'U m ω) := Subtype.ext rfl
    rw [hd, ← GeometricCurrentOn.boundary_apply]
    exact Submission.dtc_vanish_off_support P m U T.boundary _
      (Set.disjoint_left.mpr fun x hx hxb => (ω.property.2 hx).2 hxb)
  · -- Step 3 (d): a point of `U' \ spt T` has a neighbourhood `V ∩ B_{r/2}(y) ⊂⊂ U'` on which
    -- `T'` vanishes
    rintro y ⟨hyU', hyZ'⟩
    refine ⟨hU'U hyU', fun hyZ => hyZ' ?_⟩
    obtain ⟨V, ⟨hVo, -, -, hTV⟩, hyV⟩ := Set.mem_sUnion.mp hyZ
    obtain ⟨r, hr, hrU'⟩ := Metric.isOpen_iff.mp hU'o y hyU'
    have hcl : closure (V ∩ ball y (r / 2)) ⊆ closedBall y (r / 2) :=
      (closure_mono Set.inter_subset_right).trans closure_ball_subset_closedBall
    exact Set.mem_sUnion.mpr ⟨V ∩ ball y (r / 2), ⟨hVo.inter isOpen_ball,
      (isCompact_closedBall y (r / 2)).of_isClosed_subset isClosed_closure hcl,
      hcl.trans ((closedBall_subset_ball (half_lt_self hr)).trans hrU'),
      fun ω hω => hTV (testFormOnInclusion hU'U (m + 1) ω) (hω.trans Set.inter_subset_left)⟩,
      hyV, mem_ball_self (half_pos hr)⟩

/-- **Existence and upper semicontinuity of the density** (Simon 7.3.1(1), first sentence of its
proof; Ch. 4, 3.16–3.17 and 3.11).  Let `n ≥ 1`, `U` open and `T = τ(M, θ, ξ)` in `U`, where
`V = v(M, θ)` has locally bounded generalized mean curvature in `U`, `μ = θHⁿ⌞M`.  Then
`Θⁿ(μ_T, x)` exists at every `x ∈ U` and is upper semicontinuous on `U`.

Step 0: `TᵧM` is read off the orientation `ξ(y) = ±τ₁ ∧ ⋯ ∧ τₙ`.  For the coordinate covectors
`e^K` (`K : Fin n → Fin P`), Hadamard's inequality and an orthonormal completion give
`|p_{TᵧM} w| = max_{|vᵢ| ≤ 1} |∑_K (∏ᵢ (w, v)ᵢ^{Kᵢ}) ⟨e^K, ξ(y)⟩|`, a continuous function of
`(⟨e^K, ξ(y)⟩)_K` and `w`; so `div_M X` is `μ`-measurable and the first variation is a genuine
integral.  Steps 1–2: testing with `X = Φ_a(|y - x|²/t²)(y - x)`, where `Φ_a` is a `C¹`
nonincreasing profile equal to `1` on `(-∞, 1]` and `0` on `[a, ∞)`, gives
`n I - t I' ≤ Λ t I` for `I(t) = ∫ Φ_a(|y - x|²/t²) dμ` (`div_M X = nΦ + 2Φ'|p(y - x)|²/t²`,
`|X · H| ≤ 2tΛ₀Φ`), so `e^{Λt} t⁻ⁿ I(t)` is nondecreasing; letting `a ↓ 1`, so is
`e^{Λt} t⁻ⁿ μ(B_t(x))`, with the same `Λ` for all `x` near a given point.  Steps 3–5: the density
is the limit (infimum) of these monotone quantities; `M_{B_ρ(x)}(T) = μ(B_ρ(x))`
(`dtc_mass_eq_measure`) gives `HasMassDensity`, and comparing balls at nearby centres gives upper
semicontinuity. -/
theorem Submission.dtc_density_usc : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → 0 < n → R.Represents T → R.HasLocallyBoundedMeanCurvature → ∃ Θ : Euclid P → ℝ, (∀ x ∈ U, HasMassDensity T x (Θ x)) ∧ UpperSemicontinuousOn Θ U := by
  intro P n U T R hU hn hrep hH
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  obtain ⟨H, -, hHb, hfv⟩ := hH
  -- Step 0: `y ↦ |p_y w|` is `Hⁿ⌞M`-measurable, read off the orientation `ξ`
  have hpm : ∀ x : Euclid P, AEStronglyMeasurable
      (fun y => ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖) R.measure := by
    obtain ⟨F, hF, c, hc, hFc⟩ : ∃ F : ((Fin (m + 1) → Fin P) → ℝ) × Euclid P → ℝ, Continuous F ∧
        ∃ c : Euclid P → ((Fin (m + 1) → Fin P) → ℝ),
          AEStronglyMeasurable c (μHE[m + 1].restrict R.carrier) ∧
          ∀ᵐ y ∂(μHE[m + 1].restrict R.carrier), ∀ w,
            ‖(approxTangentPlane (m + 1) R.carrier y).starProjection w‖ = F (c y, w) := by
      -- coordinate `n`-covectors `e K`, `e K w = det (w j (K i))`
      have hfact : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨finrank_euclideanSpace_fin⟩
      let b₀ := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
      let o₀ : Orientation ℝ (Euclid (m + 1)) (Fin (m + 1)) := b₀.toBasis.orientation
      let L : (Fin (m + 1) → Fin P) → (Euclid P →L[ℝ] Euclid (m + 1)) := fun K =>
        (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.pi fun j => EuclideanSpace.proj (K j))
      let e : (Fin (m + 1) → Fin P) → Covector (Euclid P) (m + 1) := fun K =>
        (b₀.toBasis.det.compLinearMap (L K).toLinearMap).mkContinuous (‖L K‖ ^ (m + 1)) fun w => by
          rw [Real.norm_eq_abs]
          calc |b₀.toBasis.det.compLinearMap (L K).toLinearMap w|
              = |o₀.volumeForm fun i => L K (w i)| := (o₀.volumeForm_robust' b₀ _).symm
            _ ≤ ∏ i, ‖L K (w i)‖ := o₀.abs_volumeForm_apply_le _
            _ ≤ ∏ i, (‖L K‖ * ‖w i‖) :=
                Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => (L K).le_opNorm _
            _ = ‖L K‖ ^ (m + 1) * ∏ i, ‖w i‖ := by
                rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have he : ∀ K (w : Fin (m + 1) → Euclid P), e K w = Matrix.det (Matrix.of fun i j => w j (K i)) := by
        intro K w
        show b₀.toBasis.det (fun i => L K (w i)) = _
        rw [Module.Basis.det_apply]
        rfl
      -- expansion of `det ⟪aᵢ, τⱼ⟫` in the coordinate covectors
      have hexp : ∀ a τ : Fin (m + 1) → Euclid P,
          Matrix.det (Matrix.of fun i j => inner ℝ (a i) (τ j)) =
            ∑ K : Fin (m + 1) → Fin P, (∏ i, a i (K i)) * e K τ := by
        intro a τ
        have hrow : (Matrix.of fun i j => inner ℝ (a i) (τ j)) =
            fun i => ∑ k, a i k • fun j => τ j k := by
          ext i j
          simp [PiLp.inner_apply, Finset.sum_apply, mul_comm]
        rw [hrow]
        have h1 := (Matrix.detRowAlternating (n := Fin (m + 1)) (R := ℝ)).toMultilinearMap.map_sum
          (fun i k => a i k • fun j => τ j k)
        simp only [AlternatingMap.coe_multilinearMap] at h1
        refine h1.trans (Finset.sum_congr rfl fun K _ => ?_)
        rw [he, ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ]
        rfl
      -- the sup formula
      let f : (((Fin (m + 1) → Fin P) → ℝ) × Euclid P) → (Fin m → Euclid P) → ℝ := fun p v =>
        |∑ K : Fin (m + 1) → Fin P, (∏ i, (Fin.cons p.2 v : Fin (m + 1) → Euclid P) i (K i)) * p.1 K|
      refine ⟨fun p => sSup (f p '' closedBall 0 1),
        IsCompact.continuous_sSup (isCompact_closedBall _ _) (by fun_prop),
        fun y K => R.orient y (e K),
        (continuous_pi fun K => (ContinuousLinearMap.apply ℝ ℝ (e K)).continuous).comp_aestronglyMeasurable
          R.aestronglyMeasurable_orient, ?_⟩
      filter_upwards [R.orients] with y hy
      obtain ⟨Q, hQ, τ, hτ, hspan, hsign⟩ := hy
      have hT : approxTangentPlane (m + 1) R.carrier y = Q := by
        have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier y Q := ⟨Q, hQ⟩
        rw [approxTangentPlane, dite_eq_left h]
        exact h.choose_spec.unique hQ
      rw [hT]
      -- an orthonormal basis of `Q` from the frame `τ`
      have hmem : ∀ i, τ i ∈ Q := fun i => hspan ▸ Submodule.subset_span (mem_range_self i)
      let w₀ : Fin (m + 1) → Q := fun i => ⟨τ i, hmem i⟩
      have hw₀ : Orthonormal ℝ w₀ := by
        rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w₀)]
        exact hτ
      have hw₀span : ⊤ ≤ Submodule.span ℝ (range w₀) := by
        rintro ⟨z, hz⟩ -
        rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hz
        obtain ⟨c, hc⟩ := hz
        rw [Submodule.mem_span_range_iff_exists_fun]
        exact ⟨c, Subtype.ext (by simp only [Submodule.coe_sum, Submodule.coe_smul]; exact hc)⟩
      let b := OrthonormalBasis.mk hw₀ hw₀span
      have hb : ∀ i, (b i : Euclid P) = τ i := fun i =>
        congrArg Subtype.val (congrFun (OrthonormalBasis.coe_mk hw₀ hw₀span) i)
      have hQdim : Module.finrank ℝ Q = m + 1 :=
        (Module.finrank_eq_card_basis b.toBasis).trans (Fintype.card_fin _)
      have : Fact (Module.finrank ℝ Q = m + 1) := ⟨hQdim⟩
      let o : Orientation ℝ Q (Fin (m + 1)) := b.toBasis.orientation
      let π := Q.orthogonalProjectionOnto
      have hbdet : ∀ a : Fin (m + 1) → Euclid P,
          b.toBasis.det (fun j => π (a j)) = Matrix.det (Matrix.of fun i j => inner ℝ (a i) (τ j)) := by
        intro a
        rw [Module.Basis.det_apply, ← Matrix.det_transpose]
        congr 1
        ext i j
        rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.repr_apply_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, hb,
          real_inner_comm]
        rfl
      have hD : ∀ a : Fin (m + 1) → Euclid P,
          |∑ K : Fin (m + 1) → Fin P, (∏ i, a i (K i)) * R.orient y (e K)| =
            |b.toBasis.det (fun j => π (a j))| := by
        intro a
        rw [hbdet, hexp]
        rcases hsign with h | h
        · simp only [h]
        · simp only [h, mul_neg, Finset.sum_neg_distrib, abs_neg]
      have hHad : ∀ a : Fin (m + 1) → Euclid P, |b.toBasis.det (fun j => π (a j))| ≤ ∏ j, ‖π (a j)‖ :=
        fun a => by rw [← o.volumeForm_robust' b]; exact o.abs_volumeForm_apply_le _
      have hnorm : ∀ w, ‖Q.starProjection w‖ = ‖π w‖ := fun w => by
        rw [Submodule.starProjection_apply]; rfl
      have hup : ∀ w (v : Fin m → Euclid P), ‖v‖ ≤ 1 →
          |b.toBasis.det (fun j => π ((Fin.cons w v : Fin (m + 1) → Euclid P) j))| ≤ ‖π w‖ := by
        intro w v hv
        refine (hHad _).trans ?_
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        refine mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
          fun i _ => ?_)
        rw [Fin.cons_succ]
        exact (Q.norm_orthogonalProjectionOnto_apply_le _).trans ((norm_le_pi_norm v i).trans hv)
      intro w
      refine (IsGreatest.csSup_eq ⟨?_, ?_⟩).symm
      · by_cases h0 : π w = 0
        · refine ⟨0, mem_closedBall_self zero_le_one, ?_⟩
          show |_| = _
          rw [hD, hnorm, h0, norm_zero]
          exact le_antisymm ((hup w 0 (by rw [norm_zero]; exact zero_le_one)).trans_eq
            (by rw [h0, norm_zero])) (abs_nonneg _)
        · have hu : ‖(‖π w‖⁻¹ • π w)‖ = 1 := by
            rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
          obtain ⟨c', hc'⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := Q)
            (ι := Fin (m + 1)) (hQdim.trans (Fintype.card_fin _).symm)
            (v := fun _ => ‖π w‖⁻¹ • π w) (s := {0})
            ⟨fun i => hu, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
          have hc0 : c' 0 = ‖π w‖⁻¹ • π w := hc' 0 rfl
          refine ⟨fun i => (c' i.succ : Euclid P), ?_, ?_⟩
          · rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
            intro i
            exact le_of_eq (c'.orthonormal.1 i.succ)
          · show |_| = _
            rw [hD, hnorm]
            have hcomp : (fun j => π ((Fin.cons w (fun i => (c' i.succ : Euclid P)) :
                Fin (m + 1) → Euclid P) j)) =
                fun j => (Fin.cons ‖π w‖ (fun _ => 1) : Fin (m + 1) → ℝ) j • c' j := by
              funext j
              refine Fin.cases ?_ (fun i => ?_) j
              · simp only [Fin.cons_zero, hc0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
              · simp only [Fin.cons_succ, one_smul]
                exact Q.orthogonalProjectionOnto_mem_subspace_eq_self _
            rw [hcomp, ← AlternatingMap.coe_multilinearMap, MultilinearMap.map_smul_univ,
              AlternatingMap.coe_multilinearMap, Fin.prod_univ_succ, Fin.cons_zero, smul_eq_mul, abs_mul,
              ← o.volumeForm_robust' b, o.abs_volumeForm_apply_of_orthonormal]
            simp only [Fin.cons_succ, Finset.prod_const_one, mul_one, abs_norm]
      · rintro _ ⟨v, hv, rfl⟩
        show |_| ≤ _
        rw [hD, hnorm]
        exact hup w v (by simpa using hv)
    intro x
    exact ((hF.comp_aestronglyMeasurable (hc.prodMk
      (continuous_id.sub continuous_const).aestronglyMeasurable)).congr
        (hFc.mono fun y hy => (hy (y - x)).symm)).mono_ac (withDensity_absolutelyContinuous _ _)
  set μ := R.measure with hμ
  -- `μ = θHⁿ⌞M` is finite on compact subsets of `U`
  have hfin : ∀ K, IsCompact K → K ⊆ U → μ K ≠ ∞ := by
    intro K hK hKU
    rw [hμ, IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Steps 1–2: locally uniform monotonicity of `e^{Λt} t⁻ⁿ μ(B_t(x))` (Simon 4.3.16–3.17)
  have hmono : ∀ x₀ ∈ U, ∃ R₀ > 0, ∃ Λ : ℝ, closedBall x₀ (4 * R₀) ⊆ U ∧
      ∀ x ∈ ball x₀ R₀, MonotoneOn
        (fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) (Ioo 0 R₀) := by
    -- cutoff profiles `Φ a`: `1` on `(-∞, 1]`, `0` on `[a, ∞)`, `C¹`, nonincreasing
    obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℝ → ℝ → ℝ, Φ = fun a s => Real.smoothTransition ((a - s) / (a - 1)) :=
      ⟨_, rfl⟩
    have hΦ1 : ∀ a s, 1 < a → s ≤ 1 → Φ a s = 1 := fun a s ha hs => by
      rw [hΦdef]
      exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (by linarith)]; linarith)
    have hΦ0 : ∀ a s, 1 < a → a ≤ s → Φ a s = 0 := fun a s ha hs => by
      rw [hΦdef]
      exact Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    have hΦnn : ∀ a s, 0 ≤ Φ a s := fun a s => by rw [hΦdef]; exact Real.smoothTransition.nonneg _
    have hΦle : ∀ a s, Φ a s ≤ 1 := fun a s => by rw [hΦdef]; exact Real.smoothTransition.le_one _
    have hΦC1 : ∀ a, ContDiff ℝ 1 (Φ a) := fun a => by
      rw [hΦdef]
      exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
    have hΦc : ∀ a, Continuous (Φ a) := fun a => (hΦC1 a).continuous
    have hΦd : ∀ a s, HasDerivAt (Φ a) (deriv (Φ a) s) s := fun a s =>
      ((hΦC1 a).differentiable one_ne_zero s).hasDerivAt
    have hΦdc : ∀ a, Continuous (deriv (Φ a)) := fun a => (hΦC1 a).continuous_deriv le_rfl
    have hΦdnp : ∀ a s, 1 < a → deriv (Φ a) s ≤ 0 := fun a s ha => by
      refine Antitone.deriv_nonpos fun s₁ s₂ h => ?_
      rw [hΦdef]
      exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))
    have hΦd0 : ∀ a s, 1 < a → (s < 1 ∨ a < s) → deriv (Φ a) s = 0 := fun a s ha hs => by
      rcases hs with hs | hs
      · rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (1 : ℝ))
          ((eventually_lt_nhds hs).mono fun s' hs' => hΦ1 a s' ha hs'.le), deriv_const]
      · rw [Filter.EventuallyEq.deriv_eq (f := fun _ => (0 : ℝ))
          ((eventually_gt_nhds hs).mono fun s' hs' => hΦ0 a s' ha hs'.le), deriv_const]
    have hΦbd : ∀ a, 1 < a → ∃ C, ∀ s, |s * deriv (Φ a) s| ≤ C := fun a ha =>
      Continuous.bounded_above_of_compact_support (continuous_id.mul (hΦdc a))
        (HasCompactSupport.intro (isCompact_Icc (a := 1) (b := a)) fun s hs => by
          show s * deriv (Φ a) s = 0
          rw [hΦd0 a s ha (by simp only [mem_Icc, not_and_or, not_le] at hs; exact hs), mul_zero])
    have hdt : ∀ a r2 t : ℝ, t ≠ 0 → HasDerivAt (fun t => Φ a (r2 / t ^ 2))
        (deriv (Φ a) (r2 / t ^ 2) * (-2 * (r2 / t ^ 2) / t)) t := by
      intro a r2 t ht
      have h1 : HasDerivAt (fun t : ℝ => r2 / t ^ 2) (-2 * (r2 / t ^ 2) / t) t := by
        convert (hasDerivAt_const t r2).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht) using 1
        norm_num
        field_simp
      exact (hΦd a _).comp t h1
    have hcancel : ∀ D q t : ℝ, t ≠ 0 → -t * (D * (-2 * q / t)) = 2 * (q * D) := by
      intro D q t ht
      field_simp
    have hr1 : ∀ D q r2 N u : ℝ, D ≤ 0 → 0 ≤ u → 0 ≤ N → N ≤ r2 → q = r2 * u →
        q * D ≤ D * u * N ∧ D * u * N ≤ 0 := by
      intro D q r2 N u hD hu hN hNr hq
      have h1 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD hu) (sub_nonneg.2 hNr)
      have h2 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hD hu) hN
      have e : q * D - D * u * N = D * u * (r2 - N) := by rw [hq]; ring
      exact ⟨by linarith, h2⟩
    have hr2 : ∀ k φ D q N u C : ℝ, 0 ≤ k → 0 ≤ φ → φ ≤ 1 → |q * D| ≤ C → q * D ≤ D * u * N →
        D * u * N ≤ 0 → |k * φ + 2 * (D * u) * N| ≤ k + 2 * C := by
      intro k φ D q N u C hk hφ hφ1 hC h1 h2
      have h3 := abs_le.1 hC
      have h4 := mul_nonneg hk hφ
      have h5 := mul_le_of_le_one_right hk hφ1
      have e : 2 * (D * u) * N = 2 * (D * u * N) := by ring
      exact abs_le.2 ⟨by linarith, by linarith⟩
    intro x₀ hx₀
    -- `dim Tᵧ = n` for `μ`-a.e. `y`
    have hrank : ∀ᵐ y ∂μ, Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier y) = m + 1 := by
      refine (withDensity_absolutelyContinuous _ _).ae_le ?_
      filter_upwards [R.orients] with y hy
      obtain ⟨Q, hQ, -⟩ := hy
      have h : ∃ Q, HasApproximateTangentSpaceAt (m + 1) R.carrier y Q := ⟨Q, hQ⟩
      rw [approxTangentPlane, dite_eq_left h]
      exact h.choose_spec.finrank_eq
    -- Simon 4.3.2: `div_M X = n η(|y - x|²) + 2 η'(|y - x|²) |p_y(y - x)|²`
    have hdiv : ∀ (η η' : ℝ → ℝ) (x y : Euclid P), (∀ s, HasDerivAt η (η' s) s) →
        Module.finrank ℝ (approxTangentPlane (m + 1) R.carrier y) = m + 1 →
        tangentialDivergence (m + 1) R.carrier (fun z => η (‖z - x‖ ^ 2) • (z - x)) y =
          ((m : ℝ) + 1) * η (‖y - x‖ ^ 2) + 2 * η' (‖y - x‖ ^ 2) *
            ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 := by
      intro η η' x y hη hy
      set T := approxTangentPlane (m + 1) R.carrier y
      have hsub : HasFDerivAt (fun z : Euclid P => z - x) (ContinuousLinearMap.id ℝ (Euclid P)) y :=
        (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
      have hc : HasFDerivAt (fun z : Euclid P => η (‖z - x‖ ^ 2))
          (η' (‖y - x‖ ^ 2) • (2 • (innerSL ℝ (y - x)).comp (ContinuousLinearMap.id ℝ (Euclid P)))) y :=
        (hη _).comp_hasFDerivAt y hsub.norm_sq
      have htr : LinearMap.trace ℝ (Euclid P) T.starProjection.toLinearMap = (m : ℝ) + 1 := by
        rw [LinearMap.IsProj.trace (p := T) ⟨fun z => T.starProjection_apply_mem z,
          fun z hz => Submodule.starProjection_eq_self_iff.2 hz⟩, hy, Nat.cast_succ]
      have hinner : inner ℝ (y - x) (T.starProjection (y - x)) = ‖T.starProjection (y - x)‖ ^ 2 := by
        have h := T.re_inner_starProjection_eq_normSq (y - x)
        rw [RCLike.re_to_real, real_inner_comm] at h
        exact h
      have hcomp : T.starProjection.toLinearMap ∘ₗ
          (fderiv ℝ (fun z : Euclid P => η (‖z - x‖ ^ 2) • (z - x)) y).toLinearMap =
          η (‖y - x‖ ^ 2) • T.starProjection.toLinearMap +
            (η' (‖y - x‖ ^ 2) • (2 • (innerSL ℝ (y - x)).comp
              (ContinuousLinearMap.id ℝ (Euclid P)))).toLinearMap.smulRight (T.starProjection (y - x)) := by
        rw [show fderiv ℝ (fun z : Euclid P => η (‖z - x‖ ^ 2) • (z - x)) y = _ from
          (hc.smul hsub).fderiv]
        refine LinearMap.ext fun w => ?_
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, add_apply,
          smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
          map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]
      rw [tangentialDivergence, hcomp, map_add, map_smul, LinearMap.trace_smulRight, htr]
      simp only [ContinuousLinearMap.coe_coe, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, innerSL_apply_apply, hinner, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat]
      ring
    -- the first-variation hypothesis as an identity of `μ`-integrals
    have hfvμ : ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
        ∫ y, tangentialDivergence (m + 1) R.carrier X y ∂μ = -∫ y, inner ℝ (X y) (H y) ∂μ := by
      intro X h1 h2 h3
      have hden : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
        funext x
        simp
      have hmeas : Measurable fun x => (R.mult x : NNReal) := measurable_from_nat.comp R.measurable_mult
      rw [← hfv X h1 h2 h3, hμ, IMRep.measure, hden, integral_withDensity_eq_integral_smul hmeas,
        IMRep.firstVariation]
      congr 1
    -- localization
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
    have hR₀ : 0 < δ / 5 := by positivity
    have hK₀U : closedBall x₀ (4 * (δ / 5)) ⊆ U := (closedBall_subset_ball (by linarith)).trans hδU
    have hK₀fin : μ (closedBall x₀ (4 * (δ / 5))) ≠ ∞ := hfin _ (isCompact_closedBall _ _) hK₀U
    obtain ⟨Λ₀, hΛ₀⟩ := hHb _ (isCompact_closedBall _ _) hK₀U
    refine ⟨δ / 5, hR₀, 2 * max Λ₀ 0, hK₀U, fun x hx => ?_⟩
    set R₀ := δ / 5 with hR₀def
    set K₀ := closedBall x₀ (4 * R₀) with hK₀def
    set Λ := 2 * max Λ₀ 0 with hΛdef
    have hxx₀ : ‖x - x₀‖ < R₀ := by rwa [mem_ball, dist_eq_norm] at hx
    have hfar : ∀ y, y ∉ K₀ → 3 * R₀ < ‖y - x‖ := by
      intro y hy
      rw [hK₀def, mem_closedBall, dist_eq_norm, not_le] at hy
      linarith [norm_sub_le_norm_sub_add_norm_sub y x x₀]
    have hnear : ∀ y, ‖y - x‖ < 3 * R₀ → y ∈ K₀ := by
      intro y hy
      rw [hK₀def, mem_closedBall, dist_eq_norm]
      linarith [norm_sub_le_norm_sub_add_norm_sub y x x₀]
    have hout : ∀ a t, a ≤ 2 → 0 < t → t < R₀ → ∀ y, y ∉ K₀ → a < ‖y - x‖ ^ 2 / t ^ 2 := by
      intro a t ha ht htR y hy
      rw [lt_div_iff₀ (pow_pos ht 2)]
      have h1 := pow_lt_pow_left₀ (hfar y hy) (by positivity) two_ne_zero
      have h2 := pow_lt_pow_left₀ htR ht.le two_ne_zero
      have h3 := mul_le_mul_of_nonneg_right ha (sq_nonneg t)
      have h4 : (3 * R₀) ^ 2 = 9 * R₀ ^ 2 := by ring
      linarith [sq_nonneg R₀]
    -- bounded functions vanishing off `K₀` are integrable
    have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f μ → ∀ C : ℝ, (∀ y, |f y| ≤ C) →
        (∀ y, y ∉ K₀ → f y = 0) → Integrable f μ := by
      intro f hf C hC h0
      refine Integrable.mono'
        ((integrableOn_const (C := C) hK₀fin).integrable_indicator measurableSet_closedBall)
        hf (ae_of_all _ fun y => ?_)
      by_cases hy : y ∈ K₀
      · rw [indicator_of_mem hy, Real.norm_eq_abs]
        exact hC y
      · rw [indicator_of_notMem hy, h0 y hy, norm_zero]
    have hΦint : ∀ a, 1 < a → a ≤ 2 → ∀ t, 0 < t → t < R₀ →
        Integrable (fun y => Φ a (‖y - x‖ ^ 2 / t ^ 2)) μ := fun a ha1 ha2 t ht htR =>
      hint _ ((hΦc a).comp (by fun_prop)).aestronglyMeasurable 1
        (fun y => by rw [abs_of_nonneg (hΦnn _ _)]; exact hΦle _ _)
        fun y hy => hΦ0 a _ ha1 (hout a t ha2 ht htR y hy).le
    -- monotonicity of `e^{Λt} t⁻ⁿ ∫ Φ_a(|y - x|²/t²) dμ` (Simon 4.3.16–3.17)
    have hGmono : ∀ a, 1 < a → a ≤ 2 → MonotoneOn
        (fun t => Real.exp (Λ * t) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) / t ^ (m + 1))
          (Ioo 0 R₀) := by
      intro a ha1 ha2
      obtain ⟨C, hC⟩ := hΦbd a ha1
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
      have hstep : ∀ t ∈ Ioo 0 R₀,
          HasDerivAt (fun t => ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ)
            (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) t ∧
          ((m : ℝ) + 1) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) -
              t * (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) ≤
            Λ * t * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) := by
        rintro t ⟨ht0, htR⟩
        have hq : Continuous fun y : Euclid P => ‖y - x‖ ^ 2 / t ^ 2 := by fun_prop
        have hI_int := hΦint a ha1 ha2 t ht0 htR
        -- `|Φ'(q) · (-2q/s)| = (2/s) |q Φ'(q)| ≤ 2C/s`
        have hF' : ∀ q s : ℝ, 0 < s → |deriv (Φ a) q * (-2 * q / s)| ≤ 2 / s * C := by
          intro q s hs
          rw [show deriv (Φ a) q * (-2 * q / s) = -(2 / s * (q * deriv (Φ a) q)) by ring, abs_neg,
            abs_mul, abs_of_pos (div_pos two_pos hs)]
          exact mul_le_mul_of_nonneg_left (hC q) (div_pos two_pos hs).le
        have hJ_int : Integrable
            (fun y => deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t)) μ :=
          hint _ (((hΦdc a).comp hq).mul (by fun_prop)).aestronglyMeasurable (2 / t * C)
            (fun y => hF' _ t ht0) fun y hy => by
              rw [hΦd0 a _ ha1 (Or.inr (hout a t ha2 ht0 htR y hy)), zero_mul]
        refine ⟨?_, ?_⟩
        · -- differentiation under the integral sign
          refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Ioo (t / 2) R₀)
            (F := fun t y => Φ a (‖y - x‖ ^ 2 / t ^ 2))
            (F' := fun t y => deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))
            (bound := K₀.indicator fun _ => 2 / (t / 2) * C) (Ioo_mem_nhds (by linarith) htR)
            (Eventually.of_forall fun t' => ((hΦc a).comp (by fun_prop)).aestronglyMeasurable)
            hI_int hJ_int.aestronglyMeasurable (ae_of_all _ fun y t' ht' => ?_)
            ((integrableOn_const (C := 2 / (t / 2) * C) hK₀fin).integrable_indicator
              measurableSet_closedBall)
            (ae_of_all _ fun y t' ht' => hdt a _ t' (by linarith [ht'.1]))).2
          have ht'0 : 0 < t' := by linarith [ht'.1]
          by_cases hy : y ∈ K₀
          · rw [indicator_of_mem hy, Real.norm_eq_abs]
            exact (hF' _ t' ht'0).trans (mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_left zero_le_two (by linarith) ht'.1.le) hC0)
          · rw [indicator_of_notMem hy, hΦd0 a _ ha1 (Or.inr (hout a t' ha2 ht'0 ht'.2 y hy)),
              zero_mul, norm_zero]
        · -- the first variation of the radial field `X = Φ_a(|y - x|²/t²)(y - x)`
          have hη : ∀ s, HasDerivAt (fun s => Φ a (s / t ^ 2))
              (deriv (Φ a) (s / t ^ 2) * (1 / t ^ 2)) s := fun s =>
            (hΦd a (s / t ^ 2)).comp s ((hasDerivAt_id s).div_const (t ^ 2))
          have hXsupp : ∀ z : Euclid P, 2 * t ≤ ‖z - x‖ →
              Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x) = 0 := by
            intro z hz
            refine (congrArg (· • (z - x)) (hΦ0 a _ ha1 ?_)).trans (zero_smul ℝ _)
            rw [le_div_iff₀ (pow_pos ht0 2)]
            have h1 := pow_le_pow_left₀ (by positivity) hz 2
            have h3 := mul_le_mul_of_nonneg_right ha2 (sq_nonneg t)
            have h4 : (2 * t) ^ 2 = 4 * t ^ 2 := by ring
            linarith [sq_nonneg t]
          have hXts : tsupport (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) ⊆
              closedBall x (2 * t) := by
            refine closure_minimal (fun z hz => ?_) isClosed_closedBall
            by_contra h
            rw [mem_closedBall, dist_eq_norm, not_le] at h
            exact hz (hXsupp z h.le)
          have hfvX := hfvμ (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x))
            (((hΦC1 a).comp (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const
              _)).smul (contDiff_id.sub contDiff_const))
            ((isCompact_closedBall x (2 * t)).of_isClosed_subset (isClosed_tsupport _) hXts)
            (hXts.trans fun z hz => hK₀U (hnear z (by
              rw [mem_closedBall, dist_eq_norm] at hz
              linarith)))
          have hdivX : ∀ᵐ y ∂μ, tangentialDivergence (m + 1) R.carrier
              (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) y =
              ((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                2 * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 :=
            hrank.mono fun y hy => hdiv (fun s => Φ a (s / t ^ 2)) _ x y hη hy
          -- pointwise: `q Φ'(q) ≤ Φ'(q) t⁻² |p_y(y - x)|² ≤ 0`
          have hpt : ∀ y : Euclid P,
              (‖y - x‖ ^ 2 / t ^ 2) * deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) ≤
                deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 ∧
              deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2) *
                  ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2 ≤ 0 := fun y =>
            hr1 _ _ _ _ _ (hΦdnp a _ ha1) (one_div_nonneg.2 (sq_nonneg t)) (sq_nonneg _)
              (pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2)
              (div_eq_mul_one_div _ _)
          have hB_int : Integrable (fun y => ((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
              2 * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (1 / t ^ 2)) *
                ‖(approxTangentPlane (m + 1) R.carrier y).starProjection (y - x)‖ ^ 2) μ := by
            refine hint _ ((((hΦc a).comp hq).aestronglyMeasurable.const_mul _).add
              ((((hΦdc a).comp hq).aestronglyMeasurable.mul_const _).const_mul _ |>.mul
                ((continuous_pow 2).comp_aestronglyMeasurable (hpm x))))
              ((m : ℝ) + 1 + 2 * C) (fun y => ?_) fun y hy => ?_
            · exact hr2 _ _ _ _ _ _ _ (by positivity) (hΦnn _ _) (hΦle _ _) (hC _) (hpt y).1 (hpt y).2
            · rw [hΦ0 a _ ha1 (hout a t ha2 ht0 htR y hy).le,
                hΦd0 a _ ha1 (Or.inr (hout a t ha2 ht0 htR y hy))]
              ring
          have hA_int := (hI_int.const_mul ((m : ℝ) + 1)).add (hJ_int.const_mul (-t))
          have h1 : ((m : ℝ) + 1) * (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) -
              t * (∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ) =
              ∫ y, (((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                -t * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))) ∂μ := by
            rw [integral_add (hI_int.const_mul _) (hJ_int.const_mul _), integral_const_mul,
              integral_const_mul]
            ring
          have h2 : ∫ y, (((m : ℝ) + 1) * Φ a (‖y - x‖ ^ 2 / t ^ 2) +
                -t * (deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t))) ∂μ ≤
              ∫ y, tangentialDivergence (m + 1) R.carrier
                (fun z : Euclid P => Φ a (‖z - x‖ ^ 2 / t ^ 2) • (z - x)) y ∂μ := by
            rw [integral_congr_ae hdivX]
            refine integral_mono hA_int hB_int fun y => (add_le_add_iff_left _).2 ?_
            rw [hcancel _ _ t ht0.ne', mul_assoc]
            exact mul_le_mul_of_nonneg_left (hpt y).1 zero_le_two
          have h3 : -∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ ≤
              Λ * t * ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ := by
            have hbd : ∀ᵐ y ∂μ, |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)| ≤
                Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) := by
              filter_upwards [hΛ₀] with y hy
              by_cases hyx : ‖y - x‖ < 2 * t
              · have hH := (hy (hnear y (by linarith))).trans (le_max_left Λ₀ 0)
                calc |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)|
                    ≤ ‖Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)‖ * ‖H y‖ := abs_real_inner_le_norm _ _
                  _ = Φ a (‖y - x‖ ^ 2 / t ^ 2) * ‖y - x‖ * ‖H y‖ := by
                    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦnn _ _)]
                  _ ≤ Φ a (‖y - x‖ ^ 2 / t ^ 2) * (2 * t) * max Λ₀ 0 :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hyx.le (hΦnn _ _)) hH (norm_nonneg _)
                      (mul_nonneg (hΦnn _ _) (by linarith))
                  _ = Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) := by rw [hΛdef]; ring
              · rw [hXsupp y (not_lt.1 hyx), inner_zero_left, abs_zero]
                exact mul_nonneg (mul_nonneg (by positivity) ht0.le) (hΦnn _ _)
            calc -∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ
                ≤ |∫ y, inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y) ∂μ| := neg_le_abs _
              _ ≤ ∫ y, |inner ℝ (Φ a (‖y - x‖ ^ 2 / t ^ 2) • (y - x)) (H y)| ∂μ :=
                abs_integral_le_integral_abs
              _ ≤ ∫ y, Λ * t * Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ :=
                integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (hI_int.const_mul _) hbd
              _ = Λ * t * ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ := integral_const_mul _ _
          linarith
      have hG : ∀ t ∈ Ioo 0 R₀, ∃ d, 0 ≤ d ∧ HasDerivAt (fun t => Real.exp (Λ * t) *
          (∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ) / t ^ (m + 1)) d t := by
        intro t ht
        obtain ⟨hI, hineq⟩ := hstep t ht
        set I := ∫ y, Φ a (‖y - x‖ ^ 2 / t ^ 2) ∂μ
        set J := ∫ y, deriv (Φ a) (‖y - x‖ ^ 2 / t ^ 2) * (-2 * (‖y - x‖ ^ 2 / t ^ 2) / t) ∂μ
        have he : HasDerivAt (fun t => Real.exp (Λ * t)) (Real.exp (Λ * t) * Λ) t := by
          simpa using ((hasDerivAt_id t).const_mul Λ).exp
        refine ⟨Real.exp (Λ * t) * t ^ m * (Λ * t * I - (((m : ℝ) + 1) * I - t * J)) /
            (t ^ (m + 1)) ^ 2, div_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le
              (pow_nonneg ht.1.le _)) (by linarith)) (sq_nonneg _),
          ((he.mul hI).div (hasDerivAt_pow (m + 1) t) (pow_ne_zero _ ht.1.ne')).congr_deriv ?_⟩
        have alg : ∀ e I J : ℝ, (e * Λ * I + e * J) * t ^ (m + 1) -
            e * I * (((m + 1 : ℕ) : ℝ) * t ^ (m + 1 - 1)) =
            e * t ^ m * (Λ * t * I - (((m : ℝ) + 1) * I - t * J)) := by
          intro e I J
          rw [Nat.add_sub_cancel]
          push_cast
          ring
        simp only [Pi.mul_apply]
        rw [alg]
      refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 R₀)
        (fun t ht => (hG t ht).choose_spec.2.continuousAt.continuousWithinAt) ?_ ?_
      · rw [interior_Ioo]
        exact fun t ht => (hG t ht).choose_spec.2.differentiableAt.differentiableWithinAt
      · rw [interior_Ioo]
        exact fun t ht => (hG t ht).choose_spec.2.deriv ▸ (hG t ht).choose_spec.1
    -- let `ρ ↑ ρ₁` with `a = (ρ₁/ρ)²`: `e^{Λt} t⁻ⁿ μ(B_t(x))` is nondecreasing (Simon 4.3.17)
    intro σ hσ ρ₁ hρ₁ hσρ₁
    obtain ⟨hσ0, hσR⟩ := hσ
    obtain ⟨hρ₁0, hρ₁R⟩ := hρ₁
    have hind : ∀ r, r < R₀ → Integrable ((ball x r).indicator (1 : Euclid P → ℝ)) μ := fun r hr =>
      (integrableOn_const (C := (1 : ℝ)) (ne_top_of_le_ne_top hK₀fin (measure_mono fun z hz =>
        hnear z (by rw [mem_ball, dist_eq_norm] at hz; linarith)))).integrable_indicator
        measurableSet_ball
    have hkey : ∀ ρ ∈ Ioo (max σ (3 * ρ₁ / 4)) ρ₁,
        Real.exp (Λ * σ) * (μ (ball x σ)).toReal / σ ^ (m + 1) ≤
          Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal / ρ ^ (m + 1) := by
      rintro ρ ⟨hρ1, hρ2⟩
      have hσρ : σ < ρ := (le_max_left _ _).trans_lt hρ1
      have hρ0 : 0 < ρ := hσ0.trans hσρ
      have ha1 : 1 < (ρ₁ / ρ) ^ 2 := one_lt_pow₀ ((one_lt_div hρ0).2 hρ2) two_ne_zero
      have ha2 : (ρ₁ / ρ) ^ 2 ≤ 2 := by
        have h43 : ρ₁ / ρ ≤ 4 / 3 := by
          rw [div_le_iff₀ hρ0]
          linarith [(le_max_right σ (3 * ρ₁ / 4)).trans_lt hρ1]
        calc (ρ₁ / ρ) ^ 2 ≤ (4 / 3) ^ 2 := pow_le_pow_left₀ (by positivity) h43 2
          _ ≤ 2 := by norm_num
      have hlow : (μ (ball x σ)).toReal ≤ ∫ y, Φ ((ρ₁ / ρ) ^ 2) (‖y - x‖ ^ 2 / σ ^ 2) ∂μ := by
        refine (integral_indicator_one measurableSet_ball).symm.trans_le
          (integral_mono (hind σ hσR) (hΦint _ ha1 ha2 σ hσ0 hσR) fun y => ?_)
        by_cases hy : y ∈ ball x σ
        · rw [indicator_of_mem hy, Pi.one_apply, hΦ1 _ _ ha1]
          rw [mem_ball, dist_eq_norm] at hy
          exact (div_le_one (pow_pos hσ0 2)).2 (pow_le_pow_left₀ (norm_nonneg _) hy.le 2)
        · rw [indicator_of_notMem hy]
          exact hΦnn _ _
      have hup : ∫ y, Φ ((ρ₁ / ρ) ^ 2) (‖y - x‖ ^ 2 / ρ ^ 2) ∂μ ≤ (μ (ball x ρ₁)).toReal := by
        refine (integral_mono (hΦint _ ha1 ha2 ρ hρ0 (hρ2.trans hρ₁R)) (hind ρ₁ hρ₁R)
          fun y => ?_).trans_eq (integral_indicator_one measurableSet_ball)
        by_cases hy : y ∈ ball x ρ₁
        · rw [indicator_of_mem hy, Pi.one_apply]
          exact hΦle _ _
        · rw [indicator_of_notMem hy, hΦ0 _ _ ha1]
          rw [mem_ball, dist_eq_norm, not_lt] at hy
          rw [div_pow]
          exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hρ₁0.le hy 2) (sq_nonneg ρ)
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le)
        (pow_nonneg hσ0.le _)).trans ((hGmono _ ha1 ha2 ⟨hσ0, hσR⟩ ⟨hρ0, hρ2.trans hρ₁R⟩ hσρ.le).trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hup (Real.exp_pos _).le)
            (pow_nonneg hρ0.le _)))
    have hlim : Tendsto (fun ρ => Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal / ρ ^ (m + 1)) (𝓝[<] ρ₁)
        (𝓝 (Real.exp (Λ * ρ₁) * (μ (ball x ρ₁)).toReal / ρ₁ ^ (m + 1))) :=
      (((by fun_prop : Continuous fun ρ => Real.exp (Λ * ρ) * (μ (ball x ρ₁)).toReal).continuousAt).div
        (continuous_pow (m + 1)).continuousAt (pow_ne_zero _ hρ₁0.ne')).tendsto.mono_left
        nhdsWithin_le_nhds
    rcases hσρ₁.lt_or_eq with hlt | heq
    · exact ge_of_tendsto hlim (Filter.mem_of_superset (Ioo_mem_nhdsLT (max_lt hlt (by linarith)))
        fun ρ hρ => hkey ρ hρ)
    · rw [heq]
  -- `M_W(T) = μ(W)` for open `W ⊆ U`
  have hmass : ∀ W, IsOpen W → W ⊆ U → T.massOn W = μ W := fun W hW hWU =>
    Submission.dtc_mass_eq_measure P (m + 1) U W T R hU hW hWU hrep
  -- Steps 3–5: existence of the density, `HasMassDensity`, upper semicontinuity (Simon 4.3.11)
  have hω0 : unitBallVolume (m + 1) ≠ 0 := (measure_ball_pos volume (0 : Euclid (m + 1)) one_pos).ne'
  have hωtop : unitBallVolume (m + 1) ≠ ∞ := measure_ball_lt_top.ne
  -- the density quotient converges to `L/ωₙ`, `L = inf_{0<t<R₀} e^{Λt} t⁻ⁿ μ(B_t(x))`
  have hlim : ∀ (x : Euclid P) (Λ R₀ : ℝ), 0 < R₀ → (∀ t ∈ Ioo 0 R₀, μ (ball x t) ≠ ∞) →
      MonotoneOn (fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) (Ioo 0 R₀) →
      Tendsto (fun ρ => μ (ball x ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1))))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal (sInf ((fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal /
          t ^ (m + 1)) '' Ioo 0 R₀)) / unitBallVolume (m + 1))) := by
    intro x Λ R₀ hR₀ hfinx hmon
    have h1 := hmon.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.2 hR₀) ⟨0, by
      rintro _ ⟨t, ht, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (pow_nonneg ht.1.le _)⟩
    have h2 := ((((by fun_prop : Continuous fun t : ℝ => Real.exp (-(Λ * t))).tendsto 0).mono_left
      nhdsWithin_le_nhds).mul h1)
    rw [mul_zero, neg_zero, Real.exp_zero, one_mul] at h2
    refine (ENNReal.Tendsto.div_const (ENNReal.tendsto_ofReal h2) (Or.inr hω0)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR₀] with t ht
    rw [mul_div_assoc', ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul,
      ENNReal.ofReal_div_of_pos (pow_pos ht.1 _), ENNReal.ofReal_toReal (hfinx t ht),
      div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop)]
    ring
  -- the chosen density
  refine ⟨fun x => (limUnder (𝓝[>] (0 : ℝ)) fun ρ =>
    μ (ball x ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1)))).toReal, ?_, ?_⟩
  · intro x hx
    dsimp only
    obtain ⟨R₀, hR₀, Λ, hK, hmon⟩ := hmono x hx
    have hfinx : ∀ t ∈ Ioo 0 R₀, μ (ball x t) ≠ ∞ := fun t ht =>
      ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
        (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [ht.2]))))
    have hl := hlim x Λ R₀ hR₀ hfinx (hmon x (mem_ball_self hR₀))
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    rw [hl.limUnder_eq, ENNReal.ofReal_toReal (ENNReal.div_ne_top ENNReal.ofReal_ne_top hω0)]
    refine hl.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hR₀] with ρ hρ
    rw [hmass _ isOpen_ball ((ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith [hρ.2]))).trans hK)]
  · intro x hx c hc
    obtain ⟨R₀, hR₀, Λ, hK, hmon⟩ := hmono x hx
    have hω : 0 < (unitBallVolume (m + 1)).toReal := ENNReal.toReal_pos hω0 hωtop
    -- `Θ(x') = L(x')/ωₙ` near `x`
    have hΘ : ∀ x' ∈ ball x R₀, (limUnder (𝓝[>] (0 : ℝ)) fun ρ =>
        μ (ball x' ρ) / (unitBallVolume (m + 1) * ENNReal.ofReal (ρ ^ (m + 1)))).toReal =
        sInf ((fun t => Real.exp (Λ * t) * (μ (ball x' t)).toReal / t ^ (m + 1)) '' Ioo 0 R₀) /
          (unitBallVolume (m + 1)).toReal := by
      intro x' hx'
      have hfinx : ∀ t ∈ Ioo 0 R₀, μ (ball x' t) ≠ ∞ := fun t ht =>
        ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
          (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall' (by
            rw [mem_ball] at hx'
            linarith [ht.2]))))
      rw [(hlim x' Λ R₀ hR₀ hfinx (hmon x' hx')).limUnder_eq, ENNReal.toReal_div,
        ENNReal.toReal_ofReal (Real.sInf_nonneg (by
          rintro _ ⟨t, ht, rfl⟩
          exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
            (pow_nonneg ht.1.le _)))]
    have hc' : sInf ((fun t => Real.exp (Λ * t) * (μ (ball x t)).toReal / t ^ (m + 1)) '' Ioo 0 R₀) <
        c * (unitBallVolume (m + 1)).toReal := by
      rw [← div_lt_iff₀ hω, ← hΘ x (mem_ball_self hR₀)]
      exact hc
    obtain ⟨_, ⟨t₁, ht₁, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((nonempty_Ioo.2 hR₀).image _) hc'
    -- shrink the radius slightly: `e^{Λt} t⁻ⁿ μ(B_{t₁}(x)) < cωₙ` for some `t < t₁`
    have hcont : ContinuousAt (fun t => Real.exp (Λ * t) * (μ (ball x t₁)).toReal / t ^ (m + 1)) t₁ :=
      ((by fun_prop : Continuous fun t => Real.exp (Λ * t) * (μ (ball x t₁)).toReal).continuousAt).div
        (continuous_pow (m + 1)).continuousAt (pow_ne_zero _ ht₁.1.ne')
    obtain ⟨t₂, ht₂lt, ht₂⟩ := ((hcont.eventually (gt_mem_nhds hlt)).filter_mono nhdsWithin_le_nhds |>.and
      (Ioo_mem_nhdsLT ht₁.1)).exists (f := 𝓝[<] t₁)
    have hfin₁ : μ (ball x t₁) ≠ ∞ := ne_top_of_le_ne_top (hfin _ (isCompact_closedBall _ _) hK)
      (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [ht₁.2]))))
    refine eventually_nhdsWithin_of_eventually_nhds (Filter.mem_of_superset
      (ball_mem_nhds x (lt_min hR₀ (sub_pos.2 ht₂.2))) fun x' hx' => ?_)
    have hx'1 : x' ∈ ball x R₀ := ball_subset_ball (min_le_left _ _) hx'
    simp only [Set.mem_ofPred_eq]
    rw [hΘ x' hx'1, div_lt_iff₀ hω]
    have hbdd : BddBelow ((fun t => Real.exp (Λ * t) * (μ (ball x' t)).toReal / t ^ (m + 1)) ''
        Ioo 0 R₀) := ⟨0, by
      rintro _ ⟨t, ht, rfl⟩
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) (pow_nonneg ht.1.le _)⟩
    refine (csInf_le hbdd ⟨t₂, ⟨ht₂.1, ht₂.2.trans ht₁.2⟩, rfl⟩).trans_lt (lt_of_le_of_lt ?_ ht₂lt)
    · refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ((ENNReal.toReal_le_toReal
        (ne_top_of_le_ne_top hfin₁ (measure_mono ?_)) hfin₁).2 (measure_mono ?_)) (Real.exp_pos _).le)
        (pow_nonneg ht₂.1.le _) <;>
      · intro z hz
        rw [mem_ball] at hz hx' ⊢
        have := dist_triangle z x' x
        have := min_le_right R₀ (t₁ - t₂)
        linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
