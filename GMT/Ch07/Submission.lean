import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Mathlib.Analysis.Calculus.BumpFunction.Normed

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

/-- **Simon, proof of Ch. 6, 5.1** (step 0 of the cube estimate: subtracting a constant multiple
of `[[F]]` does not change the boundary inside the cube): if `g` is `C¹` with compact support in
the open unit cube `Q₁ ⊆ ℝⁿ`, then `∫_{Q₁} div g = 0`.  Translation does not change `∫ g`, so
differentiating `v ↦ ∫ g (x + v) dx` at `0` under the integral sign (dominated by `sup ‖Dg‖` on
the `1`-thickening of `tsupport g`) gives `∫ Dg = 0`; the trace is a continuous linear functional,
so `∫ div g = trace ∫ Dg = 0`; and `div g` vanishes off `tsupport g ⊆ Q₁`. -/
theorem Submission.dimred_mbl_dt_cbm_integral_div_eq_zero : ∀ (m : ℕ) (g : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) = 0 := by
  intro m g hg hgc hsub
  -- `Dg` is continuous, compactly supported and bounded
  have hDc : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hDs : HasCompactSupport (fderiv ℝ g) := hgc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDs
  -- `∫ Dg = 0`: differentiate the constant map `v ↦ ∫ g (x + v) dx` at `v = 0`
  have hD0 : ∫ x, fderiv ℝ g x = 0 := by
    have hK : IsCompact (cthickening 1 (tsupport g)) := hgc.isCompact.cthickening
    have h1 : HasFDerivAt (fun v : Euclid (m + 1) => ∫ x, g (x + v))
        (∫ x, fderiv ℝ g (x + 0)) 0 := by
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun v x => g (x + v))
        (F' := fun v x => fderiv ℝ g (x + v))
        (bound := (cthickening 1 (tsupport g)).indicator fun _ => C)
        (ball_mem_nhds 0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
      · exact Eventually.of_forall fun v =>
          (hg.continuous.comp (continuous_add_const v)).aestronglyMeasurable
      · simpa using hg.continuous.integrable_of_hasCompactSupport hgc
      · exact (hDc.comp (continuous_add_const 0)).aestronglyMeasurable
      · refine ae_of_all _ fun x v hv => ?_
        by_cases hx : x + v ∈ tsupport g
        · rw [indicator_of_mem (mem_cthickening_of_dist_le x (x + v) 1 _ hx ?_)]
          · exact hC _
          · rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
            exact (mem_ball_zero_iff.mp hv).le
        · rw [fderiv_of_notMem_tsupport ℝ hx, norm_zero]
          exact indicator_nonneg (fun _ _ => (norm_nonneg _).trans (hC 0)) x
      · exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
      · refine ae_of_all _ fun x v _ => ?_
        have h := (hg.differentiable one_ne_zero (x + v)).hasFDerivAt.comp v
          ((hasFDerivAt_id v).const_add x)
        rwa [ContinuousLinearMap.comp_id] at h
    have h2 : HasFDerivAt (fun v : Euclid (m + 1) => ∫ x, g (x + v))
        (0 : Euclid (m + 1) →L[ℝ] Euclid (m + 1)) 0 := by
      simp_rw [integral_add_right_eq_self]
      exact hasFDerivAt_const _ _
    simpa using h1.unique h2
  -- the trace, as a continuous linear functional on `L(ℝⁿ, ℝⁿ)`
  let T : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · calc ∫ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) = ∫ y, T (fderiv ℝ g y) := rfl
      _ = T (∫ y, fderiv ℝ g y) := T.integral_comp_comm (hDc.integrable_of_hasCompactSupport hDs)
      _ = 0 := by rw [hD0, map_zero]
  · intro y hy
    rw [fderiv_of_notMem_tsupport ℝ fun h => hy (hsub h)]
    simp

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
/-- Smoothing a unit field `s` supported in `Q_δ` by a nonnegative normalized `C^∞` kernel `ρ` of
radius `σ < δ` gives an admissible test field for `Q₁` (Simon Ch. 2, proof of Lemma 2.5): `ρ ⋆ s`
is `C^∞` (differentiation under the integral), `|ρ ⋆ s| ≤ ∫ ρ = 1`, and
`spt (ρ ⋆ s) ⊆ Q_δ + B_σ(0)` lies in the compact box `{δ − σ ≤ yᵢ ≤ 1 − δ + σ} ⊆ Q₁`. -/
theorem dimred_mbl_dt_cbm_sa_smoothed_field : ∀ (m : ℕ) (δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ) (s : Euclid (m + 1) → Euclid (m + 1)), 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → AEStronglyMeasurable s volume → (∀ x, ‖s x‖ ≤ 1) → (∀ x, x ∉ {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} → s x = 0) → ContDiff ℝ (⊤ : ℕ∞) (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ HasCompactSupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ tsupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∧ ∀ y, ‖convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume y‖ ≤ 1 := by
  intro m δ σ ρ s hσ hσδ hρs hρnn hρint hρsupp hs hs1 hs0
  set G : Euclid (m + 1) → Euclid (m + 1) := convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hG_def
  -- Step 1: `ρ` vanishes off `B̄_σ(0)`, so it has compact support; `∫ ρ = 1 ≠ 0`, so it is
  -- integrable.
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => ?_
    by_contra h
    exact hx (ball_subset_closedBall (hρsupp h))
  have hρi : Integrable ρ := integrable_of_integral_eq_one hρint
  -- Step 2: `s` is a.e.-strongly measurable and bounded by `1`, hence locally integrable.
  have hsloc : LocallyIntegrable s volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hs
      (Eventually.of_forall hs1) (M := 1)
  -- Step 3: `G = ρ ⋆ s` is `C^∞` by differentiation under the integral sign.
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := hρc.contDiff_convolution_left _ hρs hsloc
  -- Step 4: `|G y| ≤ ∫ ρ(t) |s(y − t)| dt ≤ ∫ ρ = 1`.
  have hGle : ∀ y, ‖G y‖ ≤ 1 := by
    intro y
    rw [hG_def, convolution_def, ← hρint]
    refine norm_integral_le_of_norm_le hρi (Eventually.of_forall fun t => ?_)
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hρnn t)]
    exact mul_le_of_le_one_right (hρnn t) (hs1 _)
  -- Step 5: `support G ⊆ support s + support ρ ⊆ Q_δ + B_σ(0) ⊆ P`, using `|tᵢ| ≤ |t|`.
  set P : Set (Euclid (m + 1)) := {y | ∀ i, δ - σ ≤ y i ∧ y i ≤ 1 - δ + σ}
  have hsuppG : support G ⊆ P := by
    intro y hy
    obtain ⟨a, ha, t, ht, rfl⟩ := support_convolution_subset_swap _ hy
    have haQ : ∀ i, δ < a i ∧ a i < 1 - δ := by
      by_contra h
      exact ha (hs0 a h)
    have htn : ‖t‖ < σ := by simpa using hρsupp ht
    intro i
    have hti : |t i| < σ := by
      have := PiLp.norm_apply_le t i
      rw [Real.norm_eq_abs] at this
      linarith
    obtain ⟨ha1, ha2⟩ := haQ i
    obtain ⟨ht1, ht2⟩ := abs_lt.1 hti
    simp only [PiLp.add_apply]
    constructor <;> linarith
  -- Step 6: `P` is closed and, as `0 < σ < δ`, lies in `Q₁ ⊆ B̄_{√(m+1)}(0)`; so it is compact.
  have hPclosed : IsClosed P := by
    have : P = ⋂ i, ({y : Euclid (m + 1) | δ - σ ≤ y i} ∩
        {y : Euclid (m + 1) | y i ≤ 1 - δ + σ}) := by
      ext y; simp [P]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (by fun_prop)).inter
      (isClosed_le (by fun_prop) continuous_const)
  have hPQ1 : P ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    exact ⟨by linarith, by linarith⟩
  have hQ1bdd : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ⊆
      closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1)) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            obtain ⟨h0, h1⟩ := hy i
            rw [Real.norm_eq_abs, sq_abs]; nlinarith
      _ = m + 1 := by simp
  have hPcompact : IsCompact P :=
    isCompact_of_isClosed_isBounded hPclosed (isBounded_closedBall.subset (hPQ1.trans hQ1bdd))
  -- Step 7: `tsupport G = closure (support G) ⊆ P`, so it is compact and lies in `Q₁`.
  have htsupp : tsupport G ⊆ P := closure_minimal hsuppG hPclosed
  exact ⟨hG, hPcompact.of_isClosed_subset (isClosed_tsupport G) htsupp, htsupp.trans hPQ1, hGle⟩

/-- Gradient bound for the mollified function (Simon Ch. 2, Lemma 2.5, duality argument): if
`∫_{Q₁} u div g ≤ V` for every smooth `g` with `|g| ≤ 1` and compact support in `Q₁`, then
`f = ρ * 1_{Q₁}u` satisfies `∫_{Q_δ} ‖Df‖ ≤ V` for an even mollifier `ρ` supported in `B_σ(0)`,
`σ < δ`.  Test with `g = −ρ * s`, `s = 1_{Q_δ} ∇f/|∇f|`, and use the adjoint identity
`∫ Df(s) = −∫ 1_{Q₁}u div(ρ * s)`. -/
theorem dimred_mbl_dt_cbm_sa_grad_bound : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ρ (-z) = ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (convolution ρ ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  have smoothed_field := Submission.dimred_mbl_dt_cbm_sa_smoothed_field
  have adjoint := codim1_rdo_dg_sp_mollifier_adjoint
  intro m u V δ σ ρ hu hyp hσ hσδ hρs hρnn hρeven hρint hρsupp
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qd : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 0: `Q₁`, `Q_δ` are measurable, `Q_δ ⊆ Q₁ ⊆ B̄_{√(m+1)}(0)` has finite measure,
  -- `1_{Q₁}u` is integrable and `ρ` is `C¹` with compact support.
  have hQ1m : MeasurableSet Q1 := by
    have : Q1 = ⋂ i, ({y : Euclid (m + 1) | 0 < y i} ∩ {y : Euclid (m + 1) | y i < 1}) := by
      ext y; simp [Q1]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hQdm : MeasurableSet Qd := by
    have : Qd = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y : Euclid (m + 1) | y i < 1 - δ}) := by
      ext y; simp [Qd]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hδ : 0 < δ := hσ.trans hσδ
  have hQdQ1 : Qd ⊆ Q1 := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    exact ⟨by linarith, by linarith⟩
  have hQ1bdd : Q1 ⊆ closedBall (0 : Euclid (m + 1)) (Real.sqrt (m + 1)) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
            obtain ⟨h0, h1⟩ := hy i
            rw [Real.norm_eq_abs, sq_abs]; nlinarith
      _ = m + 1 := by simp
  have hQdfin : volume Qd < ∞ :=
    (measure_mono (hQdQ1.trans hQ1bdd)).trans_lt measure_closedBall_lt_top
  set ubar : Euclid (m + 1) → ℝ := Q1.indicator u
  have hubar : Integrable ubar := (integrable_indicator_iff hQ1m).2 hu
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => ?_
    by_contra h
    exact hx (ball_subset_closedBall (hρsupp h))
  have hρ1 : ContDiff ℝ 1 ρ := hρs.of_le (by exact_mod_cast le_top)
  -- Step 1: `f = ρ * 1_{Q₁}u` is `C^∞`, so `Df` is continuous.
  set f : Euclid (m + 1) → ℝ := convolution ρ ubar (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hρc.contDiff_convolution_left _ hρs hubar.locallyIntegrable
  have hDf : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  -- Step 2: the gradient `w` (Riesz representative of `Df`) and the unit field
  -- `s = 1_{Q_δ} w/|w|`, with `Df(x)(s x) = 1_{Q_δ}(x) ‖Df(x)‖`.
  set w : Euclid (m + 1) → Euclid (m + 1) := fun x =>
    (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm (fderiv ℝ f x)
  have hw : Continuous w := (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm.continuous.comp hDf
  have hwn : ∀ x, ‖w x‖ = ‖fderiv ℝ f x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hwapp : ∀ x h, fderiv ℝ f x h = inner ℝ (w x) h := fun x h =>
    (InnerProductSpace.toDual_symm_apply).symm
  set s : Euclid (m + 1) → Euclid (m + 1) := Qd.indicator (fun x => ‖w x‖⁻¹ • w x)
  have hs_meas : Measurable s :=
    ((hw.measurable.norm.inv).smul hw.measurable).indicator hQdm
  have hs_le : ∀ x, ‖s x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ Qd
    · simp only [s, indicator_of_mem hx, norm_smul, norm_inv, norm_norm]
      by_cases hw0 : ‖w x‖ = 0
      · simp [hw0]
      · rw [inv_mul_cancel₀ hw0]
    · simp [s, indicator_of_notMem hx]
  have hs_zero : ∀ x, x ∉ Qd → s x = 0 := fun x hx => indicator_of_notMem hx _
  have hs_int : Integrable s := by
    have : IntegrableOn (fun x => ‖w x‖⁻¹ • w x) Qd :=
      Measure.integrableOn_of_bounded hQdfin.ne
        ((hw.measurable.norm.inv).smul hw.measurable).aestronglyMeasurable
        (Eventually.of_forall fun x => by
          simp only [norm_smul, norm_inv, norm_norm]
          by_cases hw0 : ‖w x‖ = 0
          · simp [hw0]
          · rw [inv_mul_cancel₀ hw0]) (M := 1)
    exact (integrable_indicator_iff hQdm).2 this
  have hDfs : ∀ x, fderiv ℝ f x (s x) = Qd.indicator (fun x => ‖fderiv ℝ f x‖) x := by
    intro x
    by_cases hx : x ∈ Qd
    · simp only [s, indicator_of_mem hx, map_smul, smul_eq_mul, hwapp x (w x),
        real_inner_self_eq_norm_sq]
      rw [← hwn x]
      by_cases hw0 : ‖w x‖ = 0
      · simp [hw0]
      · field_simp
    · simp [s, indicator_of_notMem hx]
  -- Step 3: the smoothed field `G = ρ * s` is admissible (`smoothed_field`), so testing the
  -- hypothesis with `−G` gives `−∫_{Q₁} u div G ≤ V`.
  set G : Euclid (m + 1) → Euclid (m + 1) := convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume
  obtain ⟨hG, hGc, hGsupp, hGle⟩ := smoothed_field m δ σ ρ s hσ hσδ hρs hρnn hρint hρsupp
    hs_meas.aestronglyMeasurable hs_le hs_zero
  have h1 := hyp (-G) hG.neg hGc.neg (by rw [tsupport_neg]; exact hGsupp)
    (fun y => by simpa using hGle y)
  have h1' : -∫ y in Q1, u y * LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ G y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ V := by
    rw [← integral_neg]
    convert h1 using 3 with y
    rw [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg]
  -- Step 4: the adjoint identity `∫ Df(s) = −∫ 1_{Q₁}u div G = −∫_{Q₁} u div G`.
  have h2 := adjoint (m + 1) ρ ubar s hρ1 hρc hρeven hubar hs_int
  have h3 : ∫ z, ubar z * LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ G z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
      ∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ G z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
    rw [← integral_indicator hQ1m]
    congr 1
    funext z
    by_cases hz : z ∈ Q1
    · simp [ubar, indicator_of_mem hz]
    · simp [ubar, indicator_of_notMem hz]
  -- Step 5: `∫_{Q_δ} ‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V`.
  calc ∫ x in Qd, ‖fderiv ℝ f x‖ = ∫ x, Qd.indicator (fun x => ‖fderiv ℝ f x‖) x :=
        (integral_indicator hQdm).symm
    _ = ∫ x, fderiv ℝ f x (s x) := by
        congr 1; funext x; rw [hDfs]
    _ = -∫ z, ubar z * LinearMap.trace ℝ (Euclid (m + 1))
          (fderiv ℝ G z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := h2
    _ = -∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1))
          (fderiv ℝ G z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by rw [h3]
    _ ≤ V := h1'
/-- Mollifications converge in `L¹`, uniformly over normalized kernels: for integrable `f` and
`ε > 0` there is `r > 0` with `∫ |ρ * f − f| ≤ ε` for every continuous `ρ ≥ 0` with `∫ ρ = 1`
and `spt ρ ⊆ B_r(0)` (Simon Ch. 2, proof of Lemma 2.5).  Approximate `f` in `L¹` by a continuous
compactly supported `h`; then `ρ * f − f = ρ * (f − h) + (ρ * h − h) + (h − f)`, where
convolution with `ρ` does not increase the `L¹` norm and `ρ * h − h` is uniformly small and
vanishes off a fixed ball. -/
theorem dimred_mbl_dt_cbm_sa_mollify_l1 : ∀ (n : ℕ) (f : Euclid n → ℝ), Integrable f → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n f hf ε hε
  -- Step 2: continuous compactly supported functions are dense in `L¹`.  It suffices to
  -- approximate `c 1_s` (`MemLp.induction_dense`): take compact `K ⊆ s` and open `V ⊇ K` with
  -- `vol(s \ K), vol(V \ K) < θ` (regularity) and an Urysohn function `φ`, `1` on `K`, `0` off `V`;
  -- then `|φ c − c 1_s| ≤ |c| (1_{V \ K} + 1_{s \ K})`.
  obtain ⟨h, hfh₀, hhc, hhcont⟩ : ∃ h : Euclid n → ℝ,
      eLpNorm (f - h) 1 volume ≤ ENNReal.ofReal (ε / 4) ∧ HasCompactSupport h ∧ Continuous h := by
    have hf1 : MemLp f 1 volume := memLp_one_iff_integrable.2 hf
    have hε4 : ENNReal.ofReal (ε / 4) ≠ 0 := by simp; positivity
    have hadd : ∀ g₁ g₂ : Euclid n → ℝ, HasCompactSupport g₁ ∧ Continuous g₁ →
        HasCompactSupport g₂ ∧ Continuous g₂ → HasCompactSupport (g₁ + g₂) ∧ Continuous (g₁ + g₂) :=
      fun g₁ g₂ h₁ h₂ => ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩
    refine hf1.induction_dense ENNReal.one_ne_top (fun g => HasCompactSupport g ∧ Continuous g) ?_
      hadd hε4
    intro c s hs hsμ δ hδ
    obtain ⟨θ, hθ, hθδ⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hδ
    have hθ0 : (θ : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hθ.ne'
    obtain ⟨K, hKs, hK, hKcl, hsK⟩ := hs.exists_isCompact_isClosed_sdiff_lt hsμ.ne hθ0
    obtain ⟨V, hKV, hV, -, hVK⟩ :=
      hKcl.measurableSet.exists_isOpen_sdiff_lt ((measure_mono hKs).trans_lt hsμ).ne hθ0
    obtain ⟨φ, hφK, hφV, hφc, hφ01⟩ :=
      exists_continuous_one_zero_of_isCompact hK hV.isClosed_compl
        (disjoint_compl_right_iff_subset.2 hKV)
    have hgc : Continuous fun x => φ x * c := φ.continuous.mul continuous_const
    have hgs : HasCompactSupport fun x => φ x * c := hφc.mul_right (f' := fun _ => c)
    refine ⟨fun x => φ x * c, ?_, hgs, hgc⟩
    have hpt : ∀ x, ‖φ x * c - s.indicator (fun _ => c) x‖ₑ ≤
        (V \ K).indicator (fun _ => ‖c‖ₑ) x + (s \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      by_cases hxK : x ∈ K
      · have h1 : φ x = 1 := hφK hxK
        simp [h1, hKs hxK]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (mem_sdiff_of_mem hxV hxK)]
        refine le_trans ?_ le_self_add
        rw [enorm_le_iff_norm_le, Real.norm_eq_abs, Real.norm_eq_abs]
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs, show φ x * c - c = (φ x - 1) * c by ring, abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (abs_le.2 ⟨by linarith, by linarith⟩)
        · rw [indicator_of_notMem hxs, sub_zero, abs_mul, abs_of_nonneg h0]
          exact mul_le_of_le_one_left (abs_nonneg _) h1
      · have h0 : φ x = 0 := hφV hxV
        rw [indicator_of_notMem (s := V \ K) fun hx => hxV hx.1, zero_add]
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs, indicator_of_mem (mem_sdiff_of_mem hxs hxK), h0]
          simp
        · simp [hxs, h0]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (aestronglyMeasurable_const.indicator hs))]
    calc ∫⁻ x, ‖φ x * c - s.indicator (fun _ => c) x‖ₑ
        ≤ ∫⁻ x, ((V \ K).indicator (fun _ => ‖c‖ₑ) x + (s \ K).indicator (fun _ => ‖c‖ₑ) x) :=
          lintegral_mono hpt
      _ = ‖c‖ₑ * volume (V \ K) + ‖c‖ₑ * volume (s \ K) := by
          rw [lintegral_add_left
              (measurable_const.indicator (hV.measurableSet.diff hKcl.measurableSet)),
            lintegral_indicator_const (hV.measurableSet.diff hKcl.measurableSet),
            lintegral_indicator_const (hs.diff hKcl.measurableSet)]
      _ ≤ ‖c‖ₑ * θ + ‖c‖ₑ * θ := by gcongr
      _ = θ * (2 * ‖c‖ₑ) := by ring
      _ ≤ δ := hθδ.le
  have hhi : Integrable h := hhcont.integrable_of_hasCompactSupport hhc
  have hfh : ∫⁻ x, ‖f x - h x‖ₑ ≤ ENNReal.ofReal (ε / 4) := by
    rwa [eLpNorm_one_eq_lintegral_enorm (hf.sub hhi).aestronglyMeasurable] at hfh₀
  -- Step 3: `S` is a closed ball containing `spt h` and its `1`-neighbourhood, and `r ≤ 1` is
  -- such that `|h(a) − h(b)| < η` whenever `|a − b| < r`.
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euclid n)
  set S : Set (Euclid n) := closedBall (0 : Euclid n) (R + 1)
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S < ∞ := measure_closedBall_lt_top
  set η : ℝ := ε / (4 * ((volume S).toReal + 1)) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨r₀, hr₀, hr₀h⟩ :=
    Metric.uniformContinuous_iff.1 (hhc.uniformContinuous_of_continuous hhcont) η hη
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, ?_⟩
  intro ρ hρc hρnn hρint hρsupp
  have hρcs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) (min r₀ 1)) fun x hx => ?_
    by_contra hne
    exact hx (ball_subset_closedBall (hρsupp hne))
  have hρi : Integrable ρ := integrable_of_integral_eq_one hρint
  have hρ1 : ∫⁻ t, ‖ρ t‖ₑ = 1 := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρnn)
    rw [hρint, ENNReal.ofReal_one] at h1
    rw [h1]
    congr 1; funext t
    rw [Real.enorm_eq_ofReal (hρnn t)]
  -- Step 1: `L¹` contraction, `∫ |ρ * g| ≤ ∫ |g|` (Tonelli and translation invariance).
  have contraction : ∀ g : Euclid n → ℝ, AEStronglyMeasurable g volume →
      ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ := by
    intro g hg
    have hmeas : AEMeasurable (uncurry fun x t =>
        ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ)
        ((volume : Measure (Euclid n)).prod volume) :=
      (hρc.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg).enorm
    calc ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
        ≤ ∫⁻ x, ∫⁻ t, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ :=
          lintegral_mono fun x => by
            rw [convolution_def]
            exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ x, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (ρ t) (g (x - t))‖ₑ :=
          lintegral_lintegral_swap hmeas
      _ = ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, ‖g x‖ₑ := by
          congr 1; funext t
          simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top,
            lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
      _ = ∫⁻ x, ‖g x‖ₑ := by
          rw [lintegral_mul_const _ hρc.measurable.enorm, hρ1, one_mul]
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ)
  have hhloc : LocallyIntegrable h volume := hhi.locallyIntegrable
  have hfhloc : LocallyIntegrable (f - h) volume := (hf.sub hhi).locallyIntegrable
  -- Step 5: linearity, `ρ * f − ρ * h = ρ * (f − h)`.
  have hlin : ∀ x, convolution ρ f L volume x - convolution ρ h L volume x =
      convolution ρ (f - h) L volume x := by
    intro x
    have e1 := hρcs.convolutionExists_left L hρc hhloc x
    have e2 := hρcs.convolutionExists_left L hρc hfhloc x
    have e3 := e1.distrib_add e2
    rw [show h + (f - h) = f by funext y; simp] at e3
    rw [e3]; ring
  -- Step 4: `|ρ * h − h| ≤ η` everywhere (`dist_convolution_le`), and `ρ * h − h = 0` off `S`.
  have hRle : min r₀ 1 ≤ r₀ := min_le_left _ _
  have hpt : ∀ x, ‖convolution ρ h L volume x - h x‖ₑ ≤
      S.indicator (fun _ => ENNReal.ofReal η) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have hd := dist_convolution_le (μ := volume) (f := ρ) (g := h) (x₀ := x) (R := min r₀ 1)
        (ε := η) (z₀ := h x) hη.le hρsupp hρnn hρint hhcont.aestronglyMeasurable
        (fun y hy => (hr₀h (lt_of_lt_of_le (mem_ball.1 hy) hRle)).le)
      rw [dist_eq_norm] at hd
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hd
    · rw [indicator_of_notMem hx]
      have h1 : h x = 0 := by
        by_contra hne
        exact hx (closedBall_subset_closedBall (by linarith) (hR (subset_tsupport _ hne)))
      have h2 : convolution ρ h L volume x = 0 := by
        by_contra hne
        obtain ⟨a, ha, t, ht, rfl⟩ := support_convolution_subset_swap L hne
        have ha' : ‖a‖ ≤ R := mem_closedBall_zero_iff.1 (hR (subset_tsupport _ ha))
        have ht' : ‖t‖ < min r₀ 1 := mem_ball_zero_iff.1 (hρsupp ht)
        exact hx (mem_closedBall_zero_iff.2
          ((norm_add_le a t).trans (by linarith [min_le_right r₀ 1])))
      simp [h1, h2]
  have hstep4 : ∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ ≤ ENNReal.ofReal (ε / 4) := by
    calc ∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ
        ≤ ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal η) x := lintegral_mono hpt
      _ = ENNReal.ofReal η * volume S := lintegral_indicator_const hSm _
      _ = ENNReal.ofReal (η * (volume S).toReal) := by
          rw [ENNReal.ofReal_mul hη.le, ENNReal.ofReal_toReal hSfin.ne]
      _ ≤ ENNReal.ofReal (ε / 4) := by
          apply ENNReal.ofReal_le_ofReal
          have hV : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
          rw [hη_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  -- Step 6: `ρ * f − f = ρ * (f − h) + (ρ * h − h) − (f − h)`; each term is at most `ε / 4`.
  have hpt2 : ∀ x, ‖convolution ρ f L volume x - f x‖ₑ ≤
      ‖convolution ρ (f - h) L volume x‖ₑ + ‖convolution ρ h L volume x - h x‖ₑ +
        ‖f x - h x‖ₑ := by
    intro x
    have e : convolution ρ f L volume x - f x = convolution ρ (f - h) L volume x +
        (convolution ρ h L volume x - h x) - (f x - h x) := by
      rw [← hlin x]; ring
    rw [e]
    exact (enorm_sub_le).trans (add_le_add_left (enorm_add_le _ _) _)
  have hc1 : Continuous (convolution ρ (f - h) L volume) :=
    hρcs.continuous_convolution_left L hρc hfhloc
  have hc2 : Continuous (convolution ρ h L volume) :=
    hρcs.continuous_convolution_left L hρc hhloc
  have hm1 : AEMeasurable (fun x => ‖convolution ρ (f - h) L volume x‖ₑ) volume :=
    hc1.measurable.enorm.aemeasurable
  have hm2 : AEMeasurable (fun x => ‖convolution ρ h L volume x - h x‖ₑ) volume :=
    (hc2.sub hhcont).measurable.enorm.aemeasurable
  calc ∫⁻ x, ‖convolution ρ f L volume x - f x‖ₑ
      ≤ ∫⁻ x, (‖convolution ρ (f - h) L volume x‖ₑ + ‖convolution ρ h L volume x - h x‖ₑ +
          ‖f x - h x‖ₑ) := lintegral_mono hpt2
    _ = (∫⁻ x, ‖convolution ρ (f - h) L volume x‖ₑ) +
          (∫⁻ x, ‖convolution ρ h L volume x - h x‖ₑ) + ∫⁻ x, ‖f x - h x‖ₑ := by
        have h12 : AEMeasurable (fun x => ‖convolution ρ (f - h) L volume x‖ₑ +
            ‖convolution ρ h L volume x - h x‖ₑ) volume := hm1.add hm2
        rw [lintegral_add_left' h12, lintegral_add_left' hm1]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
        refine add_le_add (add_le_add ?_ hstep4) hfh
        exact (contraction (f - h) (hf.sub hhi).aestronglyMeasurable).trans hfh
    _ = ENNReal.ofReal (3 * ε / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        ring_nf
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

/-- `C¹` approximation on `Q_δ` with total variation at most `V` (Simon Ch. 2, 2.5 as used in
2.7): the mollifications `v_k = φ_k * 1_{Q₁} u` by the even normalized bumps `φ_k` of radius
`σ_k = δ / (k + 2) < δ` satisfy `∫_{Q_δ} ‖Dv_k‖ ≤ V` (duality with smoothed unit fields, which are
admissible test fields since `σ_k < δ`), and `v_k → 1_{Q₁} u` in `L¹`, where `1_{Q₁} u = u` on
`Q_δ`. -/
theorem dimred_mbl_dt_cbm_smooth_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ∃ v : ℕ → Euclid (m + 1) → ℝ, (∀ k, ContDiff ℝ 1 (v k)) ∧ (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (v k) x‖ ≤ V) ∧ Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) := by
  have grad_bound := Submission.dimred_mbl_dt_cbm_sa_grad_bound
  have mollify_l1 := Submission.dimred_mbl_dt_cbm_sa_mollify_l1
  intro m u V δ hu hyp hδ
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qd : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 1: `Q₁` and `Q_δ ⊆ Q₁` are measurable, and `ū = 1_{Q₁} u` is integrable.
  have hQ1m : MeasurableSet Q1 := by
    have : Q1 = ⋂ i, ({y : Euclid (m + 1) | 0 < y i} ∩ {y : Euclid (m + 1) | y i < 1}) := by
      ext y; simp [Q1]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hQdm : MeasurableSet Qd := by
    have : Qd = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y : Euclid (m + 1) | y i < 1 - δ}) := by
      ext y; simp [Qd]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) measurable_const)
  have hQdQ1 : Qd ⊆ Q1 := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    exact ⟨by linarith, by linarith⟩
  set ubar : Euclid (m + 1) → ℝ := Q1.indicator u
  have hubar : Integrable ubar := (integrable_indicator_iff hQ1m).2 hu
  -- The radii `σ_k = δ / (k + 2) ∈ (0, δ)` and the even normalized bumps `φ_k ≥ 0`, `∫ φ_k = 1`,
  -- with support `B_{σ_k}(0)`.
  set σ : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2)
  have hσpos : ∀ k, 0 < σ k := fun k => by
    simp only [σ]; positivity
  have hσlt : ∀ k, σ k < δ := fun k => by
    simp only [σ]
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  let φ : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    ⟨σ k / 2, σ k, by linarith [hσpos k], by linarith [hσpos k]⟩
  set ρ : ℕ → Euclid (m + 1) → ℝ := fun k => (φ k).normed volume
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k => (φ k).hasCompactSupport_normed (μ := volume)
  have hρs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => (φ k).contDiff_normed (μ := volume)
  have hρ1 : ∀ k, ContDiff ℝ (1 : ℕ∞) (ρ k) := fun k => (φ k).contDiff_normed (μ := volume)
  have hρcont : ∀ k, Continuous (ρ k) := fun k => (φ k).continuous_normed (μ := volume)
  have hρnn : ∀ k z, 0 ≤ ρ k z := fun k z => (φ k).nonneg_normed (μ := volume) z
  have hρeven : ∀ k z, ρ k (-z) = ρ k z := fun k z => (φ k).normed_neg (μ := volume) z
  have hρint : ∀ k, ∫ z, ρ k z = 1 := fun k => (φ k).integral_normed (μ := volume)
  have hρsupp : ∀ k, support (ρ k) = ball (0 : Euclid (m + 1)) (σ k) := fun k =>
    (φ k).support_normed_eq (μ := volume)
  -- Step 5: `v_k = φ_k * ū`.
  refine ⟨fun k => convolution (ρ k) ubar (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
  · -- Step 2: `v_k` is `C¹` (differentiation under the integral sign).
    intro k
    have h := (hρc k).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (hρ1 k) hubar.locallyIntegrable (μ := volume)
    simpa using h
  · -- Step 3: the gradient bound on `Q_δ`, since `σ_k < δ`.
    intro k
    exact grad_bound m u V δ (σ k) (ρ k) hu hyp (hσpos k) (hσlt k) (hρs k)
      (hρnn k) (hρeven k) (hρint k) (hρsupp k).le
  · -- Step 4: `∫_{Q_δ} |v_k − u| = ∫_{Q_δ} |v_k − ū| ≤ ∫ |v_k − ū| ≤ ε / 2` once `σ_k < r`.
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r, hr, hρr⟩ := mollify_l1 (m + 1) ubar hubar (ε / 2) (by positivity)
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / r)
    refine ⟨N, fun k hk => ?_⟩
    have hσr : σ k < r := by
      simp only [σ]
      rw [div_lt_iff₀ (by positivity)]
      have hkN : (N : ℝ) ≤ k := by exact_mod_cast hk
      have : δ < r * N := by
        rw [div_lt_iff₀ hr] at hN; linarith
      nlinarith
    have hl := hρr (ρ k) (hρcont k) (hρnn k) (hρint k)
      (by rw [hρsupp k]; exact ball_subset_ball hσr.le)
    set w : Euclid (m + 1) → ℝ := convolution (ρ k) ubar (ContinuousLinearMap.lsmul ℝ ℝ) volume
    have hwc : Continuous w :=
      (hρc k).continuous_convolution_left _ (hρcont k) hubar.locallyIntegrable
    have heq : ∫ x in Qd, |w x - u x| = ∫ x in Qd, |w x - ubar x| := by
      refine setIntegral_congr_fun hQdm fun x hx => ?_
      simp only [ubar, indicator_of_mem (hQdQ1 hx)]
    have hmeas : AEStronglyMeasurable (fun x => |w x - ubar x|) (volume.restrict Qd) :=
      ((hwc.aestronglyMeasurable.sub hubar.aestronglyMeasurable).norm).restrict
    have hlin : ∫ x in Qd, |w x - ubar x| =
        (∫⁻ x in Qd, ENNReal.ofReal |w x - ubar x|).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => abs_nonneg _) hmeas
    have hle : (∫⁻ x in Qd, ENNReal.ofReal |w x - ubar x|) ≤ ENNReal.ofReal (ε / 2) := by
      refine le_trans (setLIntegral_le_lintegral _ _) ?_
      refine le_trans (le_of_eq ?_) hl
      congr 1; funext x; rw [Real.enorm_eq_ofReal_abs]
    have hnn : 0 ≤ ∫ x in Qd, |w x - u x| := integral_nonneg fun x => abs_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn, heq, hlin]
    calc (∫⁻ x in Qd, ENNReal.ofReal |w x - ubar x|).toReal ≤ ε / 2 :=
          ENNReal.toReal_le_of_le_ofReal (by positivity) hle
      _ < ε := by linarith

end Submission

end GMT.Ch07
