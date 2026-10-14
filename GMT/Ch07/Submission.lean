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

/-- **Simon Ch. 6, proof of 5.1, step 4** (with `n = m + 1`): a point `x ∈ ℝᴾ` of the lattice
`(m + 1)`-skeleton `L_{m+1}` (at least `P − (m + 1)` integer coordinates) that is not in the
`m`-skeleton `L_m` (fewer than `P − m` integer coordinates) lies on an open unit lattice
`(m + 1)`-face.  The set `J` of integer coordinates of `x` has `P = m + 1 + |J|`, so its
complement is the range of a strictly increasing `ι : Fin (m + 1) → Fin P`.  With `b = ⌊x⌋`
and `y_j = fract(x_{ι(j)})`, which lies in `(0, 1)` as `x_{ι(j)} ∉ ℤ`, coordinatewise
`b + Σⱼ yⱼ e_{ι(j)} = x`: `⌊xᵢ⌋ = xᵢ` for `i ∈ J`, `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j₀)`. -/
theorem Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x := by
  classical
  rintro P m x ⟨s, hsP, hs⟩ hnot
  -- Step 1: the set `J` of integer coordinates of `x`
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin P), ∀ i, i ∈ J ↔ ∃ z : ℤ, x i = z :=
    ⟨Finset.univ.filter fun i => ∃ z : ℤ, x i = z, fun i => by simp⟩
  -- Steps 2–4: `s ⊆ J` gives `P ≤ m + 1 + |J|`, and `J` itself is not admissible in (ii), so
  -- `m + |J| < P`; hence `|Jᶜ| = P − |J| = m + 1`
  have hcard : Jᶜ.card = m + 1 := by
    have h1 : s.card ≤ J.card := Finset.card_le_card fun i hi => (hJ i).2 (hs i hi)
    have h2 : ¬ P ≤ m + J.card := fun h => hnot ⟨J, h, fun i hi => (hJ i).1 hi⟩
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  -- Step 5: the increasing enumeration `ι` of `Jᶜ`
  obtain ⟨ι, hιmono, hιJ, hιrange⟩ : ∃ ι : Fin (m + 1) → Fin P,
      StrictMono ι ∧ (∀ j, ι j ∉ J) ∧ ∀ i, i ∉ J → ∃ j, ι j = i := by
    refine ⟨Jᶜ.orderEmbOfFin hcard, (Jᶜ.orderEmbOfFin hcard).strictMono,
      fun j => Finset.mem_compl.1 (Jᶜ.orderEmbOfFin_mem hcard j), fun i hi => ?_⟩
    have hrange : i ∈ Set.range (Jᶜ.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.2 hi
    exact hrange
  -- Steps 6–7: `p = (ι, ⌊x⌋)` and `y_j = fract(x_{ι(j)}) ∈ (0, 1)`, since `x_{ι(j)} ∉ ℤ`
  refine ⟨(ι, fun i => ⌊x i⌋), WithLp.toLp 2 fun j => Int.fract (x (ι j)), hιmono,
    fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [PiLp.toLp_apply]
    exact Int.fract_pos.2 fun h => hιJ j ((hJ (ι j)).2 ⟨_, h⟩)
  · rw [PiLp.toLp_apply]
    exact Int.fract_lt_one _
  -- Step 8: the `i`-th coordinate is `⌊xᵢ⌋ + Σⱼ [i = ι(j)] fract(x_{ι(j)}) = xᵢ`
  refine PiLp.ext fun i => ?_
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ J
  · -- (a) `i ∈ J`: no `ι(j)` equals `i`, and `⌊xᵢ⌋ = xᵢ` as `xᵢ ∈ ℤ`
    obtain ⟨z, hz⟩ := (hJ i).1 hi
    rw [Finset.sum_eq_zero, add_zero, hz, Int.floor_intCast]
    exact fun j _ => ite_eq_right fun h : i = ι j => hιJ j (h ▸ hi)
  · -- (b) `i = ι(j₀)`: only the `j₀` summand survives, and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ`
    obtain ⟨j₀, rfl⟩ := hιrange i hi
    rw [Finset.sum_eq_single j₀, ite_eq_left rfl, Int.floor_add_fract]
    · exact fun j _ hj => ite_eq_right fun h => hj (hιmono.injective h.symm)
    · exact fun h => absurd (Finset.mem_univ j₀) h
/-- Only finitely many unit lattice faces `b + Σⱼ [0, 1] e_{ι(j)}` (`b ∈ ℤᴾ`, `ι : Fin k → Fin P`
arbitrary) meet a compact `K ⊆ ℝᴾ` (Simon Ch. 6, §5).  If `‖x‖ ≤ ρ` on `K` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` with `y ∈ [0, 1]ᵏ`, then `Φ(y)ᵢ = bᵢ + Sᵢ` with `0 ≤ Sᵢ ≤ k`
and `|Φ(y)ᵢ| ≤ ρ`, so `|bᵢ| ≤ ⌈ρ⌉ + k`: the set lies in the finite set `(all ι) × [-N, N]ᴾ`. -/
theorem Submission.dimred_mbl_dtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite := by
  intro P k K hK
  -- `K` is bounded: `‖x‖ ≤ ρ` for `x ∈ K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- the set lies in `(Fin k → Fin P) × [-N, N]ᴾ`, `N = ⌈ρ⌉ + k`, which is finite
  refine (Set.finite_univ.prod (Set.Finite.pi fun _ =>
    Set.finite_Icc (-(⌈ρ⌉ + k)) (⌈ρ⌉ + k))).subset ?_
  rintro ⟨ι, b⟩ ⟨y, hy, hxK⟩
  refine ⟨Set.mem_univ _, fun i _ => ?_⟩
  -- coordinate formula `Φ(y)ᵢ = bᵢ + Sᵢ`, `Sᵢ = Σⱼ [i = ι j] yⱼ`
  have hcoord : (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) i =
      (b i : ℝ) + ∑ j, if i = ι j then y j else 0 := by
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  -- `|bᵢ + Sᵢ| = |Φ(y)ᵢ| ≤ ‖Φ(y)‖ ≤ ρ`
  have hxi : |(b i : ℝ) + ∑ j, if i = ι j then y j else 0| ≤ ρ := by
    rw [← hcoord, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (hρ _ hxK)
  -- `0 ≤ Sᵢ ≤ k`: each of the `k` summands lies in `[0, 1]`
  have hS0 : 0 ≤ ∑ j, if i = ι j then y j else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> linarith [(hy j).1]
  have hS1 : (∑ j, if i = ι j then y j else 0) ≤ k :=
    calc (∑ j, if i = ι j then y j else 0) ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [(hy j).2]
      _ = k := by simp
  -- hence `-(⌈ρ⌉ + k) ≤ bᵢ ≤ ⌈ρ⌉ + k`
  obtain ⟨h1, h2⟩ := abs_le.mp hxi
  have hc := Int.le_ceil ρ
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have : ((-(⌈ρ⌉ + k) : ℤ) : ℝ) ≤ b i := by push_cast; linarith
    exact_mod_cast this
  · have : (b i : ℝ) ≤ ((⌈ρ⌉ + k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
/-- **Simon Ch. 6, 1.1, 3.1 and Ch. 3, 1.4**: on a Borel set `E` lying in the coordinate `n`-plane
`{a : aᵢ = cᵢ for i ∉ range ι}`, the orientation `ξ` of an integer multiplicity triple
`(M, θ, ξ)` in an open `U` is `Hⁿ`-a.e. on `M ∩ E` a Borel sign `σ ∈ {−1, 0, 1}` times the
coordinate `n`-vector `e_ι = e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`, `⟨α, e_ι⟩ = α(e_{ι(1)}, …, e_{ι(n)})`.
This is assumed: (IMC-b) the restriction of `(M, θ, ξ)` to `M ∩ E` is a triple with the same
`ξ`; (PO) a unit orientation of an approximate tangent plane at `x` of a set whose points agree
with `x` off `range ι` is `±e_ι`.  By (IMC-b), `ξ(x)` orients an approximate tangent plane of
`M ∩ E` at `Hⁿ`-a.e. `x ∈ M ∩ E`; points of `E` agree with `x` off `range ι`, so (PO) gives
`ξ(x) = ±e_ι`.  For a strongly measurable version `ξ̃` of `ξ`, `σ = 1` on `{ξ̃ = e_ι}`,
`σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}` and `σ = 0` elsewhere is Borel (the operator-norm topology
on `n`-vectors is metrizable), and `ξ = ξ̃ = σ e_ι` `Hⁿ`-a.e. on `M ∩ E`. -/
theorem Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  classical
  intro hIMC hPO P n U R ι c E hU hι hE hEc
  have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
  -- (IMC-b): the restriction `R'` of `R` to `M ∩ E` keeps `ξ`, so `Hⁿ`-a.e. on `M ∩ E`, `ξ(x)`
  -- orients an approximate tangent plane of `M ∩ E` at `x`
  obtain ⟨_, R', _, hR'c, _, hR'o⟩ := hIMC P n U R E hU hE
  have h1 := R'.orients
  rw [hR'c, hR'o] at h1
  -- (PO): `ξ(x) = ±e_ι` a.e. on `M ∩ E`, as all points of `E` agree with `x` off `range ι`
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)),
      (∀ α : Covector (Euclid P) n,
        R.orient x α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨
      ∀ α : Covector (Euclid P) n,
        R.orient x α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    filter_upwards [h1, ae_restrict_mem hME] with x hxQ hx
    obtain ⟨Q, hQ, hξQ⟩ := hxQ
    refine hPO P n ι (R.carrier ∩ E) x Q (R.orient x) hι (fun a ha i hi => ?_) hQ hξQ
    rw [hEc a ha.2 i hi, hEc x hx.2 i hi]
  -- a strongly measurable version `ξ̃` of `ξ`; `ξ = ξ̃` a.e. on `M`, hence on `M ∩ E`
  obtain ⟨ξt, hξt, h3⟩ : ∃ ξt : Euclid P → MultiVector P n, StronglyMeasurable ξt ∧
      R.orient =ᵐ[μHE[n].restrict R.carrier] ξt :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  have h3' : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), R.orient x = ξt x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left h3
  -- the coordinate `n`-vector `e_ι`
  obtain ⟨e, he⟩ : ∃ e : MultiVector P n, ∀ α : Covector (Euclid P) n,
      e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) :=
    ⟨ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _, fun α => rfl⟩
  -- the operator-norm topology on `n`-vectors is metrizable, so `{ξ̃ = ±e_ι}` are Borel
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    ⟨⟨(inferInstance : PseudoMetricSpace (MultiVector P n)).toUniformSpace, rfl,
      @EMetric.instIsCountablyGeneratedUniformity _
        (inferInstance : PseudoMetricSpace (MultiVector P n)).toPseudoEMetricSpace⟩⟩
  have hm1 : MeasurableSet {x | ξt x = e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  have hm2 : MeasurableSet {x | ξt x = -e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  -- `σ = 1` on `{ξ̃ = e_ι}`, `σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}`, `σ = 0` elsewhere
  refine ⟨fun x => if ξt x = e then 1 else if ξt x = -e then -1 else 0,
    Measurable.ite hm1 measurable_const (Measurable.ite hm2 measurable_const measurable_const),
    fun x => ?_, ?_⟩
  · dsimp only
    split_ifs <;> simp
  · filter_upwards [h2, h3'] with x hx hxt α
    rcases hx with h | h
    · -- `ξ(x) = e_ι`, so `ξ̃(x) = e_ι` and `σ(x) = 1`
      have hte : ξt x = e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => (h β).trans (he β).symm)
      rw [ite_eq_left hte, h α, Int.cast_one, one_mul]
    · -- `ξ(x) = −e_ι`, so `ξ̃(x) = −e_ι`; `σ(x) = 1` only if also `ξ̃(x) = e_ι`
      have hte : ξt x = -e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => by rw [h β, neg_apply, he β])
      by_cases hte' : ξt x = e
      · rw [ite_eq_left hte', Int.cast_one, one_mul, hxt, hte', he α]
      · rw [ite_eq_right hte', ite_eq_left hte, Int.cast_neg, Int.cast_one, neg_one_mul, h α]

/-- **Simon Ch. 6, proof of 5.1, (27)–(28) (p. 167)**, on one open face of the unit lattice: let
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` be an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  Then
`τ(M, θ, ξ)⌞F̆`, pulled back to `Q₁`, is `u(y) ⟨ω(Φ_p(y)), e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}⟩ dy` for an
integer-valued `u ∈ L¹(Q₁)` with `∫_{Q₁} |u| ≤ μ_V(F̆)`.  `F̆` is Borel and lies in the coordinate
plane through `b`, so `coordinate_plane_orientation_sign` gives `ξ = σ e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}`
`Hⁿ`-a.e. on `M ∩ F̆`, with `σ` integer-valued and `|σ| ≤ 1`.  Take `u = (1_M θ σ) ∘ Φ_p`: isometry
invariance of `μHE` and `μHE = Lⁿ` on `ℝⁿ` give `Hⁿ⌞F̆ = Φ_p#(Lⁿ⌞Q₁)`, and `μ_V(F̆) < ∞` because
`F̆` lies in the compact set `Φ_p([0, 1]ⁿ)`. -/
theorem Submission.dimred_mbl_dtfrsd_face_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro hIMC hPO P n R p hι hiso
  -- name the parametrization `Φ = Φ_p`, the open cube `Q₁` and the frame `Ep = E_p`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid n → Euclid P, Φ = fun y : Euclid n =>
      WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Set (Euclid n), Q₁ = {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} :=
    ⟨_, rfl⟩
  obtain ⟨Ep, hEp⟩ : ∃ Ep : Fin n → Euclid P,
      Ep = fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hΦiso : Isometry Φ := by rw [hΦ]; exact hiso
  suffices H : ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u Q₁ ∧
      ENNReal.ofReal (∫ y in Q₁, |u y|) ≤ R.measure (Φ '' Q₁) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        ∫ x in R.carrier ∩ Φ '' Q₁,
            (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
          ∫ y in Q₁, u y * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep by
    subst hΦ hQ₁ hEp
    exact H
  -- `Q₁` is open, `Φ` is a measurable embedding (an isometry), so `F̆ = Φ(Q₁)` is Borel
  have hQ₁meas : MeasurableSet Q₁ := by
    have hopen : IsOpen Q₁ := by
      have : Q₁ = ⋂ i, {y : Euclid n | 0 < y i ∧ y i < 1} := by
        rw [hQ₁]; ext y; simp
      rw [this]
      refine isOpen_iInter_of_finite fun i => ?_
      have hc : Continuous fun y : Euclid n => y i := by fun_prop
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    exact hopen.measurableSet
  have hΦme : MeasurableEmbedding Φ := hΦiso.isClosedEmbedding.measurableEmbedding
  have hFmeas : MeasurableSet (Φ '' Q₁) := hΦme.measurableSet_image.2 hQ₁meas
  have hMmeas : MeasurableSet R.carrier := R.measurableSet_carrier
  -- `F̆` lies in the coordinate plane through `b`: `aᵢ = bᵢ` for `a ∈ F̆` and `i ∉ range ι`
  have hplane : ∀ a ∈ Φ '' Q₁, ∀ i, (∀ j, p.1 j ≠ i) →
      a i = (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) : Euclid P) i := by
    rintro a ⟨y, -, rfl⟩ i hi
    rw [hΦ]
    simp [Ne.symm (hi _)]
  -- `ξ = σ E_p`, `|σ| ≤ 1`, `Hⁿ`-a.e. on `M ∩ F̆`
  obtain ⟨σ, hσmeas, hσle, hσae⟩ :=
    Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign hIMC hPO P n univ R p.1
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (Φ '' Q₁) isOpen_univ hι hFmeas hplane
  rw [← hEp] at hσae
  -- change of variables: `Hⁿ⌞F̆ = Φ#(Lⁿ⌞Q₁)`
  have hrestr : μHE[n].restrict (Φ '' Q₁) =
      Measure.map Φ ((volume : Measure (Euclid n)).restrict Q₁) := by
    rw [← Measure.restrict_restrict_of_subset (image_subset_range Φ Q₁),
      ← hΦiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hΦme.restrict_map, hΦme.injective.preimage_image]
  have hcov : ∀ f : Euclid P → ℝ, ∫ x in Φ '' Q₁, f x ∂μHE[n] = ∫ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.integral_map]
  have hlcov : ∀ f : Euclid P → ℝ≥0∞, ∫⁻ x in Φ '' Q₁, f x ∂μHE[n] = ∫⁻ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.lintegral_map]
  -- the density `g = 1_M θ σ` (so `u = g ∘ Φ`) and the weight `θ' = 1_M θ`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℝ,
      g = R.carrier.indicator (fun x => (R.mult x : ℝ) * (σ x : ℝ)) := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : Euclid P → ℝ≥0∞,
      θ' = R.carrier.indicator (fun x => (R.mult x : ℝ≥0∞)) := ⟨_, rfl⟩
  have hgM : ∀ x ∈ R.carrier, g x = (R.mult x : ℝ) * (σ x : ℝ) := fun x hx => by
    rw [hg]; exact indicator_of_mem hx _
  have hg0 : ∀ x ∉ R.carrier, g x = 0 := fun x hx => by
    rw [hg]; exact indicator_of_notMem hx _
  have hgmeas : Measurable g := by
    rw [hg]
    refine Measurable.indicator ?_ hMmeas
    exact ((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).mul
      ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp hσmeas)
  have hgint : ∀ x, ∃ z : ℤ, g x = z := by
    intro x
    by_cases hx : x ∈ R.carrier
    · exact ⟨(R.mult x : ℤ) * σ x, by rw [hgM x hx]; push_cast; ring⟩
    · exact ⟨0, by rw [hg0 x hx]; simp⟩
  have hgle : ∀ x, ENNReal.ofReal |g x| ≤ θ' x := by
    intro x
    by_cases hx : x ∈ R.carrier
    · rw [hgM x hx, hθ', indicator_of_mem hx, abs_mul, Nat.abs_cast]
      have h1 : |(σ x : ℝ)| ≤ 1 := by exact_mod_cast hσle x
      calc ENNReal.ofReal ((R.mult x : ℝ) * |(σ x : ℝ)|) ≤ ENNReal.ofReal (R.mult x : ℝ) :=
            ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (Nat.cast_nonneg _) h1)
        _ = (R.mult x : ℝ≥0∞) := ENNReal.ofReal_natCast _
    · rw [hg0 x hx, hθ', indicator_of_notMem hx]; simp
  -- `μ_V(F̆) = ∫_{F̆} 1_M θ dHⁿ = ∫_{Q₁} θ' ∘ Φ`
  have hmass : R.measure (Φ '' Q₁) = ∫⁻ y in Q₁, θ' (Φ y) := by
    rw [← hlcov θ', hθ', IMRep.measure, ← withDensity_indicator hMmeas,
      withDensity_apply _ hFmeas]
  -- `μ_V(F̆) ≤ μ_V(Φ([0, 1]ⁿ)) < ∞` by local integrability of `θ`
  have hfin : R.measure (Φ '' Q₁) < ∞ := by
    obtain ⟨C, hCc, hQC⟩ : ∃ C : Set (Euclid n), IsCompact C ∧ Q₁ ⊆ C := by
      refine ⟨WithLp.toLp 2 '' (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1),
        (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _), ?_⟩
      intro y hy
      rw [hQ₁] at hy
      exact ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
    have hKc : IsCompact (Φ '' C) := hCc.image hΦiso.continuous
    have hKfin : R.measure (Φ '' C) ≠ ∞ := by
      rw [IMRep.measure, withDensity_apply _ hKc.measurableSet,
        Measure.restrict_restrict hKc.measurableSet, inter_comm]
      exact R.locallyIntegrable_mult _ hKc (subset_univ _)
    exact lt_of_le_of_lt (measure_mono (image_mono hQC)) hKfin.lt_top
  -- integrability of `u = g ∘ Φ` on `Q₁` and `∫_{Q₁} |u| ≤ μ_V(F̆)`
  have hlint : ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| ≤ R.measure (Φ '' Q₁) := by
    rw [hmass]
    exact lintegral_mono fun y => hgle (Φ y)
  have huint : Integrable (fun y => g (Φ y)) ((volume : Measure (Euclid n)).restrict Q₁) := by
    refine ⟨(hgmeas.comp hΦiso.continuous.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hlint hfin
  refine ⟨fun y => g (Φ y), fun y => hgint (Φ y), huint, ?_, fun ω => ?_⟩
  · exact (ofReal_integral_eq_lintegral_ofReal huint.abs
      (Eventually.of_forall fun y => abs_nonneg _)).trans_le hlint
  -- `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{F̆} g ω(E_p) dHⁿ = ∫_{Q₁} u ω(Φ ·)(E_p)`
  calc ∫ x in R.carrier ∩ Φ '' Q₁,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
      = ∫ x in R.carrier ∩ Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine integral_congr_ae ?_
        filter_upwards [hσae, ae_restrict_mem (hMmeas.inter hFmeas)] with x hx hxm
        rw [hx, hgM x hxm.1]
        ring
    _ = ∫ x in Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hFmeas inter_subset_right
          ?_).symm
        intro x hx
        rw [hg0 x (fun h => hx.2 ⟨h, hx.1⟩), zero_mul]
    _ = ∫ y in Q₁, g (Φ y) * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep :=
        hcov (fun x => g x * (ω : DifferentialForm (Euclid P) n) x Ep)
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
/-- **Integrability of the action integrand** (Simon Ch. 6, 3.1 (‡)).  For an integer
multiplicity triple `R = (C, θ, ξ)` in `U` and `ω ∈ 𝒟ⁿ(U)`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is
`Hⁿ⌞C`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal `Hⁿ`-a.e. on `C`, so
`|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by `B θ 1_{spt ω}` (`B` a bound for `‖ω‖`),
which is integrable because `spt ω` is a compact subset of `U` and `∫_{C ∩ K} θ dHⁿ < ∞` for
such `K`. -/
theorem Submission.regcomp_rim_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  set K : Set (Euclid P) := tsupport f
  /- Step 1: `ω` is continuous, bounded by some `B`, and vanishes off the compact set
  `K = spt ω ⊆ U`. -/
  have hcont : Continuous f := hsmooth.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  /- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ C`. -/
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hor⟩ := hx
    have hατ : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hor with h | h
    · rw [h]
      exact hατ
    · rw [h, norm_neg]
      exact hατ
  /- Step 3: the integrand is a.e. strongly measurable (evaluation is continuous). -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hev : AEStronglyMeasurable (fun x => R.orient x (f x)) (μHE[n].restrict R.carrier) :=
    happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable)
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (f x))
      (μHE[n].restrict R.carrier) := hθm.aestronglyMeasurable.mul hev
  /- Step 4: `B θ 1_K` is integrable, since `∫_{C ∩ K} θ dHⁿ < ∞`. -/
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => B * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul B
  /- Step 5: `|θ ⟨ω, ξ⟩| ≤ B θ 1_K` a.e. on `C`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (f x)‖ ≤ B * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (f x)).trans (hB x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound
/-- **Disjoint neighbourhoods of the open unit faces** (Simon Ch. 6, §5, proof of 5.1, step 1: the
interiors `F̆` of the faces get pairwise disjoint neighbourhoods).  For `p = (ι, b)` with `ι`
strictly increasing let `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, and for `t ∈ (0,1)ᵏ` let `B_p(t)` be the set
of `x` with `2|x − Φ_p(t)| < 1` and `2|x − Φ_p(t)| < min(tⱼ, 1 − tⱼ)` for all `j`.  Then
`N_p = ⋃_{t ∈ (0,1)ᵏ} B_p(t)` is a union of finite intersections of open sets, hence open, and it
contains `Φ_p((0,1)ᵏ)` (take `t = y`).  The separation hypothesis gives
`2|x − Φ_p(t)| < |Φ_p(t) − Φ_q(y')|` for `x ∈ B_p(t)`, `q ≠ p` and `y' ∈ [0,1]ᵏ`.  For
`x = Φ_q(y')` this reads `2|x − Φ_p(t)| < |x − Φ_p(t)|`, so `Φ_q([0,1]ᵏ)` misses `N_p`; for
`x ∈ B_p(t) ∩ B_q(t')` the bounds for `(p, q, t, t')` and `(q, p, t', t)` contradict the triangle
inequality. -/
theorem Submission.dimred_mbl_dtfrbv_face_neighbourhoods : ∀ (P k : ℕ), (∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) → ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → IsOpen (N p) ∧ (∀ y : Euclid k, (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N p) ∧ ∀ q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono q.1 → q ≠ p → (∀ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∉ N p) ∧ Disjoint (N p) (N q) := by
  intro P k hS
  -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P, ∀ p y,
      Φ p y = WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hΦ] at hS ⊢
  -- step 1: `B_p(t) = {x : 2|x − Φ_p t| < 1, 2|x − Φ_p t| < min(tⱼ, 1 − tⱼ) ∀ j}` and
  -- `N_p = ⋃_{t ∈ (0,1)ᵏ} B_p(t)`
  obtain ⟨B, hB⟩ : ∃ B : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Set (Euclid P), ∀ p t,
      B p t = {x | 2 * dist x (Φ p t) < 1} ∩
        ⋂ j, {x | 2 * dist x (Φ p t) < min (t j) (1 - t j)} := ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p,
      N p = ⋃ t ∈ {t : Euclid k | ∀ j, 0 < t j ∧ t j < 1}, B p t := ⟨_, fun _ => rfl⟩
  -- step 4: `2|x − Φ_p t| < |Φ_p t − Φ_q y'|` for `x ∈ B_p(t)`, `q ≠ p` and `y' ∈ [0,1]ᵏ`
  have hkey : ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q →
      ∀ t : Euclid k, (∀ j, 0 < t j ∧ t j < 1) → ∀ y' : Euclid k, (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) →
        ∀ x ∈ B p t, 2 * dist x (Φ p t) < dist (Φ p t) (Φ q y') := by
    intro p q hp hq hpq t ht y' hy' x hx
    simp only [hB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx
    rcases hS p q hp hq hpq t y' ht hy' with h | ⟨j, h⟩
    · exact lt_of_lt_of_le hx.1 h
    · exact lt_of_lt_of_le (hx.2 j) h
  refine ⟨N, fun p hp => ⟨?_, fun y hy => ?_, fun q hq hqp => ⟨fun y hy hx => ?_, ?_⟩⟩⟩
  · -- step 2: each `B_p(t)` is a finite intersection of open sets `{x : 2|x − Φ_p t| < c}`
    rw [hN]
    refine isOpen_biUnion fun t _ => ?_
    have hd : Continuous fun x : Euclid P => 2 * dist x (Φ p t) :=
      continuous_const.mul (continuous_id.dist continuous_const)
    rw [hB]
    exact (isOpen_lt hd continuous_const).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt hd continuous_const)
  · -- step 3: `Φ_p(y) ∈ B_p(y)`, as `|Φ_p y − Φ_p y| = 0 < min(yⱼ, 1 − yⱼ)`
    rw [hN]
    refine Set.mem_biUnion (show y ∈ {t : Euclid k | ∀ j, 0 < t j ∧ t j < 1} from hy) ?_
    simp only [hB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, dist_self, mul_zero]
    exact ⟨one_pos, fun j => lt_min (hy j).1 (sub_pos.mpr (hy j).2)⟩
  · -- step 5: for `x = Φ_q(y) ∈ B_p(t)`, step 4 with `y' = y` gives `2|x − Φ_p t| < |x − Φ_p t|`
    rw [hN] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    rw [Set.mem_ofPred_eq] at ht
    have h := hkey p q hp hq hqp.symm t ht y hy (Φ q y) hxt
    rw [dist_comm (Φ p t)] at h
    linarith [dist_nonneg (x := Φ q y) (y := Φ p t)]
  · -- step 6: step 4 for `(p, q, t, t')` and `(q, p, t', t)` contradicts the triangle inequality
    rw [Set.disjoint_left]
    intro x hxp hxq
    rw [hN] at hxp hxq
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxp
    obtain ⟨t', ht', hxt'⟩ := Set.mem_iUnion₂.mp hxq
    rw [Set.mem_ofPred_eq] at ht ht'
    have h₁ := hkey p q hp hq hqp.symm t ht t' (fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩) x hxt
    have h₂ := hkey q p hq hp hqp t' ht' t (fun i => ⟨(ht i).1.le, (ht i).2.le⟩) x hxt'
    have h₃ := dist_triangle (Φ p t) x (Φ q t')
    linarith [dist_comm (Φ p t) x, dist_comm (Φ q t') (Φ p t)]
/-- Local mass is superadditive over a finite pairwise disjoint family (Simon 6.2.5; the summation
over faces in the proof of 6.5.1): `∑_{i ∈ s} M_{N_i}(S) ≤ M_W(S)` for `W = ⋃_{i ∈ s} N_i`.
Forms `ω_i` admissible for the pairwise disjoint `N_i` have at most one nonzero value at each
point, so `∑_{i ∈ s} ω_i` is admissible for `W`, and `S(∑ ω_i) = ∑ S(ω_i)`.  Choosing `ω_i` with
`S(ω_i) ≥ 0` and `M_{N_i}(S) ≤ S(ω_i) + ε / #s`, and letting `ε → 0`, gives the inequality. -/
theorem Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ι : Type) (s : Finset ι) (N : ι → Set (Euclid P)), (↑s : Set ι).PairwiseDisjoint N → ∑ i ∈ s, S.massOn (N i) ≤ S.massOn (⋃ i ∈ s, N i) := by
  classical
  intro P n U S ι s N hN
  -- gluing: forms admissible for the pairwise disjoint `N i` sum to a form admissible for `W`
  have hglue : ∀ ω : ι → TestFormOn U n, (∀ i ∈ s, ω i ∈ massAdmissibleOn U n (N i)) →
      (∑ i ∈ s, ω i) ∈ massAdmissibleOn U n (⋃ i ∈ s, N i) := by
    intro ω hω
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_sum, Finset.sum_fn]
      have hsupp : support (fun x => ∑ i ∈ s, (ω i : DifferentialForm (Euclid P) n) x) ⊆
          ⋃ i ∈ s, tsupport (ω i : DifferentialForm (Euclid P) n) :=
        (Finset.support_sum s fun i => (ω i : DifferentialForm (Euclid P) n)).trans
          (iUnion₂_mono fun i _ => subset_tsupport _)
      exact (closure_minimal hsupp (isClosed_biUnion_finset fun i _ => isClosed_tsupport _)).trans
        (iUnion₂_mono fun i hi => (hω i hi).1)
    · rw [Submodule.coe_sum, Finset.sum_apply]
      by_cases hx : ∃ i ∈ s, x ∈ tsupport (ω i : DifferentialForm (Euclid P) n)
      · -- `x` lies in at most one `N i`, so at most one summand is nonzero at `x`
        obtain ⟨i, hi, hxi⟩ := hx
        rw [Finset.sum_eq_single i (fun j hj hji => image_eq_zero_of_notMem_tsupport fun hxj =>
          Set.disjoint_left.1 (hN hj hi hji) ((hω j hj).1 hxj) ((hω i hi).1 hxi))
          (fun h => absurd hi h)]
        exact (hω i hi).2 x
      · rw [Finset.sum_eq_zero fun i hi =>
          image_eq_zero_of_notMem_tsupport fun hxi => hx ⟨i, hi, hxi⟩, covectorEuclideanNorm_zero]
        exact zero_le_one
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hW => ?_
  have hδ : (ε : ℝ≥0∞) / s.card ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨ENNReal.coe_ne_zero.2 hε.ne', ENNReal.natCast_ne_top _⟩
  -- near-optimal forms: `S(ω_i) ≥ 0` and `M_{N_i}(S) ≤ S(ω_i) + ε / #s`
  have happrox : ∀ i ∈ s, ∃ ω ∈ massAdmissibleOn U n (N i), 0 ≤ S ω ∧
      S.massOn (N i) ≤ ENNReal.ofReal (S ω) + (ε : ℝ≥0∞) / s.card := by
    intro i hi
    by_cases h0 : S.massOn (N i) = 0
    · exact ⟨0, ⟨by simp, fun x => by simp⟩, by simp, by simp [h0]⟩
    have hfin : S.massOn (N i) ≠ ∞ :=
      ((S.massOn_mono (Finset.subset_set_biUnion_of_mem (f := N) hi)).trans_lt hW).ne
    obtain ⟨_, ⟨ω, hω, rfl⟩, hlt⟩ := lt_sSup_iff.1 (ENNReal.sub_lt_self hfin h0 hδ)
    exact ⟨ω, hω, (ENNReal.ofReal_pos.1 (zero_le.trans_lt hlt)).le,
      tsub_le_iff_right.1 hlt.le⟩
  choose! ω hω hpos happ using happrox
  calc ∑ i ∈ s, S.massOn (N i)
      ≤ ∑ i ∈ s, (ENNReal.ofReal (S (ω i)) + (ε : ℝ≥0∞) / s.card) := Finset.sum_le_sum happ
    _ = ENNReal.ofReal (S (∑ i ∈ s, ω i)) + s.card * ((ε : ℝ≥0∞) / s.card) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, map_sum,
        ENNReal.ofReal_sum_of_nonneg hpos]
    _ ≤ S.massOn (⋃ i ∈ s, N i) + ε := add_le_add (S.le_massOn (hglue ω hω)) ENNReal.mul_div_le
/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
/-- **Kronecker property of the determinant covectors** (Simon 6.1, chapter-06.txt lines 22–47:
`dxʲ(v) = vⱼ`, `dx^{i₁} ∧ ⋯ ∧ dx^{iₙ}(v₁, …, vₙ) = det(dx^{iₖ}(vⱼ))` (1.1), and
`ω_α = ω(e_{i₁}, …, e_{iₙ})` for the basis `{dx^α : α ∈ I_{n,P}}` (1.2)): if `I`, `J` are strictly
increasing and `θ(v) = det (v_j(I k))_{k,j}`, then `θ(e_{J 1}, …, e_{J n}) = δ_{IJ}`.  The matrix
of `θ(e_J)` has entries `[I k = J j]`.  It is the identity if `I = J`.  Otherwise some `I k₀` is
not a value of `J` (else `range I ⊆ range J`, both have `n` elements, so the ranges agree and the
strictly increasing maps agree), and row `k₀` vanishes. -/
theorem Submission.cmr_cc_det_covector_basis_kronecker : ∀ (P n : ℕ) (I J : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → StrictMono J → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → θ (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 := by
  intro P n I J θ hI hJ hθ
  -- Step 1: `θ(e_J) = det M` with `M k j = e_{J j}(I k)`
  rw [hθ]
  -- Step 2: `M k j = e_{J j}(I k) = if I k = J j then 1 else 0`
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hIJ : I = J
  · -- Step 3: if `I = J`, injectivity of `J` gives `M = 1`, so `det M = 1`
    rw [ite_eq_left hIJ]
    subst hIJ
    refine (congrArg Matrix.det ?_).trans Matrix.det_one
    ext k j
    simp only [Matrix.of_apply, Matrix.one_apply, hI.injective.eq_iff]
  · -- Step 4: if `I ≠ J`, some `I k₀` is not a value of `J`: otherwise `range I ⊆ range J`,
    -- both ranges have `n` elements, so they are equal and `I = J`
    rw [ite_eq_right hIJ]
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, I k₀ ∉ Set.range J := by
      by_contra hcon
      have hsub : Set.range I ⊆ Set.range J := by
        rintro _ ⟨k, rfl⟩
        by_contra hk
        exact hcon ⟨k, hk⟩
      have hcard : (Set.range J).ncard ≤ (Set.range I).ncard :=
        ((Set.ncard_range_of_injective hJ.injective).trans
          (Set.ncard_range_of_injective hI.injective).symm).le
      exact hIJ ((hI.range_inj_of_wellFoundedLT hJ).1 (Set.eq_of_subset_of_ncard_le hsub hcard))
    -- Step 5: row `k₀` of `M` vanishes, so `det M = 0`
    refine Matrix.det_eq_zero_of_row_eq_zero k₀ fun j => ?_
    simp only [Matrix.of_apply]
    exact ite_eq_right fun hEq => hk₀ ⟨j, hEq.symm⟩

/-- **Face covectors of a coordinate `(m+1)`-plane** (Simon Ch. 6, (1.1), (1.2), (1.15)): for
strictly increasing `ι : Fin (m + 1) → Fin P` put `J_j = ι ∘ j.succAbove` (the `j`-th index
dropped) and `ε_j = (-1)^j dx^{J_j}`, with `dx^{J_j}` from `Submission.cmr_cc_det_covector_exists`.
The `J_j` are strictly increasing and pairwise distinct (for `j ≠ j'`, `ι j` is a value of `J_{j'}`
but not of `J_j`), so by `Submission.cmr_cc_det_covector_basis_kronecker` the coefficient
`α_c(e_I)` of `α_c = Σ_j c_j ε_j` is `(-1)^j c_j` if `I = J_j` and `0` for every other strictly
increasing `I`.  This gives `α_c(e_{J_j}) = (-1)^j c_j` and `|α_c| = √(Σ_j c_j²)`. -/
theorem Submission.cmcdtfrbv_face_covectors : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P), StrictMono ι → ∃ ε : Fin (m + 1) → Covector (Euclid P) m, (∀ c : Fin (m + 1) → ℝ, covectorEuclideanNorm (∑ j, c j • ε j) = Real.sqrt (∑ j, c j ^ 2)) ∧ ∀ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)), (∑ j', c j' • ε j') (fun k => EuclideanSpace.single (ι (j.succAbove k)) (1 : ℝ)) = (-1) ^ (j : ℕ) * c j := by
  intro P m ι hι
  -- Step 1: the face indices `J_j = ι ∘ j.succAbove` are strictly increasing
  obtain ⟨J, hJ⟩ : ∃ J : Fin (m + 1) → Fin m → Fin P, ∀ j k, J j k = ι (j.succAbove k) :=
    ⟨fun j k => ι (j.succAbove k), fun _ _ => rfl⟩
  have hJmono : ∀ j, StrictMono (J j) := by
    intro j a b hab
    rw [hJ, hJ]
    exact hι (Fin.strictMono_succAbove j hab)
  -- Step 2: `j ↦ J_j` is injective: for `j ≠ j'`, `ι j` is a value of `J_{j'}` but not of `J_j`
  have hJinj : Injective J := by
    intro j j' h
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    have h1 : J j z = ι j := by rw [h, hJ, hz]
    rw [hJ] at h1
    exact Fin.succAbove_ne j z (hι.injective h1)
  -- Step 3: `θ_j = dx^{J_j}` by `det_covector_exists`, and `ε_j = (-1)^j θ_j`
  choose θ hθ using fun j => Submission.cmr_cc_det_covector_exists P m (J j)
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (m + 1) → Covector (Euclid P) m,
      ∀ j, ε j = ((-1 : ℝ) ^ (j : ℕ)) • θ j :=
    ⟨fun j => ((-1 : ℝ) ^ (j : ℕ)) • θ j, fun _ => rfl⟩
  -- Steps 4–5: by `det_covector_kronecker`, on a strictly increasing `I`
  -- `α_c(e_I) = Σ_{j'} [J_{j'} = I] (-1)^{j'} c_{j'}`
  have hval : ∀ (c : Fin (m + 1) → ℝ) (I : Fin m → Fin P), StrictMono I →
      (∑ j', c j' • ε j') (fun k => EuclideanSpace.basisFun (Fin P) ℝ (I k)) =
        ∑ j', if J j' = I then (-1) ^ (j' : ℕ) * c j' else 0 := by
    intro c I hI
    rw [ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, hε, ContinuousAlternatingMap.smul_apply,
      Submission.cmr_cc_det_covector_basis_kronecker P m (J j') I (θ j') (hJmono j') hI (hθ j')]
    split_ifs
    · rw [smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · rw [smul_zero, smul_zero]
  -- Step 6: `α_c(e_{J_j}) = (-1)^j c_j`, since only `j' = j` has `J_{j'} = J_j`
  have hface : ∀ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)),
      (∑ j', c j' • ε j') (fun k => EuclideanSpace.basisFun (Fin P) ℝ (J j k)) =
        (-1) ^ (j : ℕ) * c j := by
    intro c j
    rw [hval c (J j) (hJmono j), Finset.sum_eq_single j]
    · exact ite_eq_left rfl
    · intro j' _ hj'
      exact ite_eq_right fun h => hj' (hJinj h)
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  refine ⟨ε, fun c => ?_, fun c j => ?_⟩
  · -- Step 7: the squared coefficient of `α_c` on a strictly increasing `I` is `c_j²` if
    -- `I = J_j` and `0` otherwise, so the squared coefficients sum to `Σ_j c_j²`
    rw [covectorEuclideanNorm]
    congr 1
    symm
    refine Fintype.sum_of_injective J hJinj _ _ (fun I hI => ?_) (fun j => ?_)
    · split_ifs with hmono
      · have h0 : (∑ j', if J j' = I then (-1 : ℝ) ^ (j' : ℕ) * c j' else 0) = 0 :=
          Finset.sum_eq_zero fun j' _ => ite_eq_right fun h => hI ⟨j', h⟩
        rw [hval c I hmono, h0]
        ring
      · rfl
    · rw [ite_eq_left (hJmono j), hface c j]
      rcases neg_one_pow_eq_or ℝ (j : ℕ) with h | h <;> rw [h] <;> ring
  · -- Step 6 with `e_l = EuclideanSpace.single l 1`
    have hv : (fun k => EuclideanSpace.single (ι (j.succAbove k)) (1 : ℝ)) =
        fun k => EuclideanSpace.basisFun (Fin P) ℝ (J j k) := by
      funext k
      rw [EuclideanSpace.basisFun_apply, hJ]
    rw [hv]
    exact hface c j

/-- **Admissible test form with prescribed values on a face** (Simon Ch. 6, proof of the
deformation theorem 5.1, displays (26)–(28), with the test forms of 2.35).  Let
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` be the chart of the face `p = (ι, b)` and
`π(x) = (x_{ι(j)} − b_{ι(j)})ⱼ` its affine left inverse.  The compact set `K = Φ_p(spt g) ⊆ N`
has `cthickening δ K ⊆ N` for some `δ > 0`, and a smooth `χ : ℝᴾ → [0, 1]` with support
`thickening δ K` equals `1` exactly on `K`.  So `G = χ · (g ∘ π)` is smooth, compactly supported
in `N`, bounded by `1`, and `G ∘ Φ_p = g`.  With the face covectors `εⱼ` of `ι`
(`Submission.cmcdtfrbv_face_covectors`), `γ(x) = Σⱼ Gⱼ(x) εⱼ` is a test form with
`tsupport γ ⊆ N` and `|γ(x)| = ‖G x‖ ≤ 1`, and `γ(Φ_p y)(e_{ι ∘ i.succAbove}) = (-1)ⁱ gᵢ(y)`. -/
theorem Submission.dimred_mbl_dtfrbv_face_test_form : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ γ : TestFormOn (univ : Set (Euclid P)) m, tsupport (γ : DifferentialForm (Euclid P) m) ⊆ N ∧ (∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ ∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), g y i = (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)) := by
  intro P m p N g hι hN hΦN hg hgc hgQ hg1
  -- Step 1: the face chart `Φ_p`, its affine left inverse `π = L - c₀`, and `π ∘ Φ_p = id`
  -- (the `ι(j)`-th coordinate of `Φ_p y` is `b_{ι(j)} + yⱼ`, as `ι` is injective)
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let L : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (p.1 j))
      map_add' := fun x x' => by ext j; simp
      map_smul' := fun c x => by ext j; simp }
  have hL : ∀ x, L x = WithLp.toLp 2 (fun j => x (p.1 j)) := fun x => rfl
  let c₀ : Euclid (m + 1) := WithLp.toLp 2 (fun j => (p.2 (p.1 j) : ℝ))
  let π : Euclid P → Euclid (m + 1) := fun x => L x - c₀
  have hπΦ : ∀ y, π (Φ y) = y := by
    intro y
    ext j
    simp [π, hL, c₀, Φ, Pi.single_apply, hι.injective.eq_iff]
  have hΦc : Continuous Φ := by fun_prop
  have hπc : ContDiff ℝ (⊤ : ℕ∞) π := L.contDiff.sub contDiff_const
  -- Step 2: `K = Φ_p(spt g)` is a compact subset of `N`, so `cthickening δ K ⊆ N` for some `δ > 0`
  have hKc : IsCompact (Φ '' tsupport g) := hgc.isCompact.image hΦc
  have hKN : Φ '' tsupport g ⊆ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΦN y (hgQ hy)
  obtain ⟨δ, hδ, hδN⟩ := hKc.exists_cthickening_subset_open hN hKN
  -- Step 3: smooth `χ` with values in `[0, 1]`, support `thickening δ K` and `χ = 1` exactly on
  -- `K`; so `tsupport χ ⊆ cthickening δ K ⊆ N`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := Φ '' tsupport g)) hKc.isClosed
    (self_subset_thickening hδ _)
  have hχK : tsupport χ ⊆ cthickening δ (Φ '' tsupport g) := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  -- Step 4: `G = χ · (g ∘ π)` is smooth, compactly supported in `N` and bounded by `1`, and
  -- `G ∘ Φ_p = g`, since `χ = 1` on `K` and `g = 0` off `spt g`
  obtain ⟨G, hG, hGc, hGN, hG1, hGΦ⟩ : ∃ G : Euclid P → Euclid (m + 1),
      ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ tsupport G ⊆ N ∧ (∀ x, ‖G x‖ ≤ 1) ∧
        ∀ y, G (Φ y) = g y := by
    refine ⟨fun x => χ x • g (π x), hχ.smul (hg.comp hπc), ?_, ?_, ?_, fun y => ?_⟩
    · exact hKc.cthickening.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_smul_subset_left _ _).trans hχK)
    · exact (tsupport_smul_subset_left _ _).trans (hχK.trans hδN)
    · intro x
      have hx := hχr (mem_range_self x)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans (hg1 _)
    · show χ (Φ y) • g (π (Φ y)) = g y
      rw [hπΦ]
      by_cases hyg : y ∈ tsupport g
      · rw [(hχ1 (Φ y)).1 (mem_image_of_mem Φ hyg), one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hyg, smul_zero]
  -- Step 5: the face covectors `εⱼ` of `ι = p.1`
  obtain ⟨ε, hεn, hεf⟩ := Submission.cmcdtfrbv_face_covectors P m p.1 hι
  -- Step 6: `γ(x) = Σⱼ Gⱼ(x) εⱼ` is smooth and `supp γ ⊆ supp G`, so `γ` is a test form on `ℝᴾ`
  -- with `tsupport γ ⊆ tsupport G ⊆ N`
  set γ : DifferentialForm (Euclid P) m := fun x => ∑ j, G x j • ε j with hγ
  have hGj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun x => G x j := fun j =>
    (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hγs : ContDiff ℝ (⊤ : ℕ∞) γ :=
    ContDiff.sum fun j _ => (hGj j).smul contDiff_const
  have hγG : support γ ⊆ support G := by
    intro x hx
    rw [mem_support] at hx ⊢
    contrapose! hx
    simp [hγ, hx]
  have hγT : IsTestForm γ ∧ tsupport γ ⊆ (univ : Set (Euclid P)) :=
    ⟨⟨hγs, hGc.mono hγG⟩, subset_univ _⟩
  refine ⟨⟨γ, hγT⟩, (closure_mono hγG).trans hGN, fun x => ?_, fun y i => ?_⟩
  · -- Step 7: `|γ(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`
    calc covectorEuclideanNorm (γ x) = Real.sqrt (∑ j, G x j ^ 2) := hεn fun j => G x j
      _ = ‖G x‖ := by rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ 1 := hG1 x
  · -- Step 8: `γ(Φ_p y)(e_{ι ∘ i.succAbove}) = (-1)ⁱ Gᵢ(Φ_p y) = (-1)ⁱ gᵢ(y)`, and `((-1)ⁱ)² = 1`
    have hface : γ (Φ y) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)) =
        (-1 : ℝ) ^ (i : ℕ) * G (Φ y) i :=
      hεf (fun j => G (Φ y) j) i
    show g y i = (-1 : ℝ) ^ (i : ℕ) *
      γ (Φ y) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ))
    rw [hface, hGΦ y]
    rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> rw [h] <;> ring
/-- **Isometric images: Borel, `Hᵏ`-measure and change of variables** (for the lattice faces
`F̆_p = Φ_p(Q₁)` in the deformation theorem, Simon Ch. 6 §5).  If `Φ : ℝᵏ → ℝᴾ` is an isometry and
`A ⊆ ℝᵏ` is Borel, then `Φ(A)` is Borel, `Hᵏ(Φ(A)) = Lᵏ(A)`, and
`∫_{Φ(A)} h dHᵏ = ∫_A h(Φ(y)) dy` for every `h : ℝᴾ → ℝ` (Bochner integrals: no integrability of
`h` is needed).  `Φ` is a closed, hence measurable, embedding; `Hᵏ` is isometry invariant and equals
`Lᵏ` on `ℝᵏ`; and `Φ_#Hᵏ = Hᵏ⌞range Φ` restricts to `Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A)`. -/
theorem Submission.dimred_mbl_dtfrpi_isometry_image_integral : ∀ (P k : ℕ) (Φ : Euclid k → Euclid P) (A : Set (Euclid k)), Isometry Φ → MeasurableSet A → MeasurableSet (Φ '' A) ∧ μHE[k] (Φ '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in Φ '' A, h x ∂μHE[k] = ∫ y in A, h (Φ y) := by
  intro P k Φ A hΦ hA
  -- step 1: `ℝᵏ` is complete, so `Φ` is a closed, hence measurable, embedding and `Φ(A)` is Borel
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  have hΦA : MeasurableSet (Φ '' A) := hemb.measurableSet_image.mpr hA
  -- step 4: `Hᵏ⌞Φ(A) = (Φ_#Hᵏ)⌞Φ(A) = Φ_#(Hᵏ⌞Φ⁻¹(Φ(A))) = Φ_#(Lᵏ⌞A)`, as `Φ_#Hᵏ = Hᵏ⌞range Φ`
  have hpush : μHE[k].restrict (Φ '' A) = (volume.restrict A).map Φ := by
    have h := hemb.restrict_map μHE[k] (Φ '' A)
    rwa [hΦ.map_euclideanHausdorffMeasure, Measure.restrict_restrict hΦA,
      Set.inter_eq_left.mpr (Set.image_subset_range Φ A), Set.preimage_image_eq A hemb.injective,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume k] at h
  refine ⟨hΦA, ?_, fun h => ?_⟩
  -- steps 2-3: `Hᵏ(Φ(A)) = Hᵏ(A) = Lᵏ(A)`, by isometry invariance and `Hᵏ = Lᵏ` on `ℝᵏ`
  · rw [hΦ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume k]
  -- step 5: change of variables along the measurable embedding `Φ`, valid for every `h`
  · rw [hpush, hemb.integral_map]
/-- **Simon Ch. 3, 1.4, flat case** (step 4(iii) of the proof of `dimred_mbl_dtfr_polyhedral_im`):
if `M` agrees with the affine plane `x + V` on `B_δ(x)`, i.e. `z ∈ M ⇔ z − x ∈ V` whenever
`|z − x| < δ`, then `V` is the approximate tangent space of `M` at `x`.  If `f ∈ C_c(ℝᴾ)` vanishes
off `B_R(0)`, then for `0 < r < δ/R` the blow-up `η_{x,r}(M)` agrees with `V` on `B_R(0)`, so
`∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ`: the integrals are eventually constant as `r ↓ 0`.  No
measurability of `M` is needed. -/
theorem Submission.dimred_mbl_dtfrpi_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (δ : ℝ), Module.finrank ℝ V = n → 0 < δ → (∀ z : Euclid P, dist z x < δ → (z ∈ M ↔ z - x ∈ V)) → HasApproximateTangentSpaceAt n M x V := by
  intro P n M x V δ hV hδ hM
  refine ⟨hV, fun f => ?_⟩
  -- `f` vanishes outside some ball `B(0, R)`
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
  obtain ⟨R, hRpos, hfz⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y ∉ ball (0 : Euclid P) R, f y = 0 := by
    refine ⟨max R₀ 0 + 1, by positivity,
      fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => hy ?_⟩
    have hy'' := hR₀ hy'
    rw [mem_closedBall, dist_zero_right] at hy''
    rw [mem_ball, dist_zero_right]
    linarith [le_max_left R₀ 0]
  -- restricting to the Borel ball `B(0, R)` does not change `∫ f`
  have hloc : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) R ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfz]
  -- for `0 < r < δ / R`, `η_{x,r}(M)` agrees with `V` on `B(0, R)`
  apply (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hRpos)] with r ⟨hr0, hrR⟩
  rw [lt_div_iff₀ hRpos] at hrR
  have hset : ball (0 : Euclid P) R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
      ball (0 : Euclid P) R ∩ (V : Set (Euclid P)) := by
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      refine ⟨hyB, V.smul_mem _ ((hM z ?_).1 hzM)⟩
      rw [mem_ball, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        norm_inv, Real.norm_of_nonneg hr0.le, inv_mul_lt_iff₀ hr0] at hyB
      rw [dist_eq_norm]
      linarith
    · rintro ⟨hyB, hyV⟩
      refine ⟨hyB, x + r • y, (hM _ ?_).2 ?_, ?_⟩
      · rw [mem_ball, dist_zero_right] at hyB
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
        calc r * ‖y‖ ≤ r * R := by gcongr
          _ < δ := hrR
      · rw [add_sub_cancel_left]
        exact V.smul_mem r hyV
      · rw [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, inv_smul_smul₀ hr0.ne']
  rw [hloc (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M), hset, ← hloc]
/-- **Coordinate `k`-planes and their unit orientations** (Simon Ch. 6, (1.2), (1.7): the simple
`k`-vector `e_{i₁} ∧ ⋯ ∧ e_{iₖ}` pairs with a `k`-covector `ω` as `ω(e_{i₁}, …, e_{iₖ})`; §5: a face
`F ∈ 𝓛ₖ` of the Deformation Theorem lies in such a coordinate plane, oriented by
`±e_{i₁} ∧ ⋯ ∧ e_{iₖ}`).  Let `ι : Fin k → Fin P` be strictly increasing, `τⱼ = e_{ι(j)}` and
`V = span{τⱼ}`.  The standard orthonormal basis composed with the injective `ι` is orthonormal,
hence linearly independent, so `dim V = k`.  Evaluation `α ↦ α(τ)` is linear with
`|α(τ)| ≤ ‖α‖ ∏ⱼ ‖τⱼ‖ = ‖α‖`, which gives the `k`-vector `e` with `e(α) = α(τ)`; the frame `τ`
witnesses that both `e` and `-e` are unit orientations of `V`. -/
theorem Submission.dimred_mbl_dtfrpi_coord_plane_orientation : ∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro P k ι hι
  -- step 1: `τ` is the orthonormal standard basis of `ℝᴾ` composed with the injective `ι`
  have hτ : Orthonormal ℝ (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P) :=
    EuclideanSpace.orthonormal_single.comp ι hι.injective
  -- step 2: an orthonormal family is linearly independent, so `dim V = #(Fin k) = k`
  have hV : Module.finrank ℝ (Submodule.span ℝ
      (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k := by
    rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- step 3: `α ↦ α(τ)` is linear (covector operations are pointwise) and bounded by `‖α‖`
  let e : MultiVector P k :=
    LinearMap.mkContinuous
      { toFun := fun α : Covector (Euclid P) k => α fun j => EuclideanSpace.single (ι j) (1 : ℝ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } 1
      fun α => by
        calc ‖α fun j => EuclideanSpace.single (ι j) (1 : ℝ)‖
            ≤ ‖α‖ * ∏ j, ‖(EuclideanSpace.single (ι j) (1 : ℝ) : Euclid P)‖ := α.le_opNorm _
          _ = 1 * ‖α‖ := by simp [hτ.1]
  refine ⟨hV, e, fun _ => rfl, ?_, ?_⟩
  -- step 4: the frame `τ` orients `V` with sign `+` for `e`
  · exact ⟨_, hτ, rfl, Or.inl fun _ => rfl⟩
  -- step 5: and with sign `-` for `-e`, as `(-e)(α) = -e(α)`
  · exact ⟨_, hτ, rfl, Or.inr fun _ => rfl⟩
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
/-- **Simon 6.5.1** (proof, (31): `Lⁿ` of the interior of a unit face is `1`): the open unit cube
`{y : 0 < yᵢ < 1}` of `ℝᵏ` has volume `1`.  It is the preimage of the box `∏ᵢ (0, 1)` under the
volume-preserving `ofLp : ℝᵏ → (Fin k → ℝ)`, and the box has volume `∏ᵢ (1 - 0) = 1` (the empty
product if `k = 0`). -/
theorem Submission.cmcdtfrfg_cube_volume : ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro k
  -- the box `∏ᵢ (0, 1)` in `Fin k → ℝ`
  have hB : MeasurableSet (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- the cube is `ofLp⁻¹` of the box
  have hpre : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp
/-- **Coordinates of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face of the
cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P`, `b ∈ ℤᴾ`, `y ∈ ℝᵏ` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)}`: coordinates are additive and linear and `(eᵢ)ₗ = [l = i]`, so
`Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`.  At `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`,
giving `b_{ι(m)} + yₘ`; for `l` outside the range of `ι` every summand vanishes, giving `bₗ`. -/
theorem Submission.cmcdtfrfg_face_coord : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ) (y : Euclid k), Function.Injective ι → (∀ m, (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (ι m) = (b (ι m) : ℝ) + y m) ∧ (∀ l, (∀ m, ι m ≠ l) → (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l = (b l : ℝ)) := by
  intro P k ι b y hι
  -- steps 1-2: `Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`
  have hcoord : ∀ l : Fin P, (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l =
      (b l : ℝ) + ∑ j, if ι j = l then y j else 0 := by
    intro l
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact if_congr eq_comm rfl rfl
  refine ⟨fun m => ?_, fun l hl => ?_⟩
  -- step 3: at `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`
  · rw [hcoord, Fintype.sum_eq_single m fun j hj => ite_eq_right (hι.ne hj), ite_eq_left rfl]
  -- step 4: for `l` outside the range of `ι` every summand vanishes
  · rw [hcoord, Finset.sum_eq_zero fun j _ => ite_eq_right (hl j), add_zero]

/-- **Isometry and diameter of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face
of the cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P` and `b ∈ ℤᴾ`, the
map `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry `ℝᵏ → ℝᴾ`: by `face_coord` the coordinate gap of
`Φ(y)` and `Φ(y')` is `yₘ - y'ₘ` at `ι(m)` and `0` off the range of `ι`, so reindexing the sum of
squared gaps along `ι` gives `|Φ(y) - Φ(y')| = |y - y'|`.  On the closed unit cube every squared gap
is at most `1`, so `|y - y'| ≤ √k ≤ √P`, as `k ≤ P` by injectivity of `ι`. -/
theorem Submission.cmcdtfrfg_face_isometry_diam : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ), Function.Injective ι → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) ≤ Real.sqrt P) := by
  intro P k ι b hι
  -- (a), steps 1-5: `|Φ(y) - Φ(y')|² = Σₗ |Φ(y)ₗ - Φ(y')ₗ|² = Σₘ |yₘ - y'ₘ|² = |y - y'|²`
  have hiso : ∀ y y' : Euclid k,
      dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) =
      dist y y' := by
    intro y y'
    -- step 2: the coordinates of `Φ(y)` and `Φ(y')`
    obtain ⟨hy, hyc⟩ := Submission.cmcdtfrfg_face_coord P k ι b y hι
    obtain ⟨hy', hy'c⟩ := Submission.cmcdtfrfg_face_coord P k ι b y' hι
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    -- steps 3-4: reindex the sum of squared gaps along the injective `ι`
    symm
    refine Fintype.sum_of_injective ι hι _ _ (fun l hl => ?_) fun m => ?_
    -- off the range of `ι` the gap is `bₗ - bₗ = 0`
    · have hl' : ∀ m, ι m ≠ l := fun m hm => hl ⟨m, hm⟩
      rw [hyc l hl', hy'c l hl', dist_self, sq, mul_zero]
    -- at `ι(m)` the gap is `(b_{ι(m)} + yₘ) - (b_{ι(m)} + y'ₘ) = yₘ - y'ₘ`
    · rw [hy m, hy' m, dist_add_left]
  refine ⟨hiso, fun y y' hy hy' => ?_⟩
  -- (b), step 6: on the unit cube `-1 ≤ yₘ - y'ₘ ≤ 1`, so every squared gap is at most `1`
  have hgap : ∀ m, dist (y m) (y' m) ^ 2 ≤ 1 := by
    intro m
    obtain ⟨hy₀, hy₁⟩ := hy m
    obtain ⟨hy'₀, hy'₁⟩ := hy' m
    rw [Real.dist_eq, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  -- step 7: `k = #(Fin k) ≤ #(Fin P) = P`, as `ι` is injective
  have hkP : k ≤ P := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ι hι
  -- step 8: `|Φ(y) - Φ(y')| = |y - y'| = √(Σₘ |yₘ - y'ₘ|²) ≤ √k ≤ √P`
  rw [hiso, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ m, dist (y m) (y' m) ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := Finset.sum_le_sum fun m _ => hgap m
    _ = k := by simp
    _ ≤ P := by exact_mod_cast hkP
/-- **Separation of distinct unit lattice faces** (Simon Ch. 6, §5, chapter-06.txt lines 1841–1918:
the faces `F ∈ 𝓛ₖ` and their interiors `F̆`).  For `p = (ι, b) ≠ q = (ι', b')` with `ι, ι'`
strictly increasing, `x = Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` with `y ∈ (0,1)ᵏ` and `z = Φ_q(y')` with
`y' ∈ [0,1]ᵏ`, either `1 ≤ |x − z|` or `min(yⱼ, 1 − yⱼ) ≤ |x − z|` for some `j`.  If some
`z_{ι(j)}` lies outside `(b_{ι(j)}, b_{ι(j)} + 1) ∋ x_{ι(j)} = b_{ι(j)} + yⱼ`, the coordinate `ι(j)`
gives the second alternative.  Otherwise no `z_{ι(j)}` is an integer, so `range ι ⊆ range ι'` and
`ι = ι'` (both enumerate the same `k`-element set increasingly), `b = b'` on `range ι`, and a
coordinate `l ∉ range ι` with `b_l ≠ b'_l` gives `|x_l − z_l| = |b_l − b'_l| ≥ 1`.  The coordinates
of `x` and `z` are `cmcdtfrfg_face_coord`. -/
theorem Submission.cmcdtfrfg_face_separation : ∀ (P k : ℕ) (p q : (Fin k → Fin P) × (Fin P → ℤ)), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) := by
  intro P k p q hp hq hpq y y' hy hy'
  -- step 1: the coordinates of `x = Φ_p(y)` and `z = Φ_q(y')`
  obtain ⟨hx₁, hx₂⟩ := Submission.cmcdtfrfg_face_coord P k p.1 p.2 y hp.injective
  obtain ⟨hz₁, hz₂⟩ := Submission.cmcdtfrfg_face_coord P k q.1 q.2 y' hq.injective
  set x := WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  set z := WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)
  -- step 2: `|x_l − z_l| ≤ |x − z|`
  have hcoord : ∀ l, |x l - z l| ≤ dist x z := fun l => by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x z l
  by_cases hA : ∃ j, ¬((p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1)
  · -- step 3 (Case A): `z_{ι(j)} ∉ (b_{ι(j)}, b_{ι(j)} + 1)` while `x_{ι(j)} = b_{ι(j)} + y_j`
    obtain ⟨j, hj⟩ := hA
    obtain ⟨hy₀, hy₁⟩ := hy j
    refine Or.inr ⟨j, le_trans ?_ (hcoord (p.1 j))⟩
    rw [hx₁ j]
    rcases not_and_or.mp hj with h | h
    · calc min (y j) (1 - y j) ≤ y j := min_le_left _ _
        _ ≤ (p.2 (p.1 j) : ℝ) + y j - z (p.1 j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := le_abs_self _
    · calc min (y j) (1 - y j) ≤ 1 - y j := min_le_right _ _
        _ ≤ z (p.1 j) - ((p.2 (p.1 j) : ℝ) + y j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := by rw [abs_sub_comm]; exact le_abs_self _
  -- step 4 (Case B): `b_{ι(j)} < z_{ι(j)} < b_{ι(j)} + 1` for every `j`
  have hB : ∀ j, (p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1 :=
    fun j => not_not.mp fun h => hA ⟨j, h⟩
  refine Or.inl ?_
  -- step 5: `range ι ⊆ range ι'`, since `z_l = b'_l ∈ ℤ` for `l ∉ range ι'`
  have hsub : ∀ j, ∃ m, q.1 m = p.1 j := by
    intro j
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hB j
    rw [hz₂ (p.1 j) fun m hm => hne ⟨m, hm⟩] at h₁ h₂
    have h₁' : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) := h₁
    have h₂' : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := h₂
    have : p.2 (p.1 j) < q.2 (p.1 j) := by exact_mod_cast h₁'
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₂'
    omega
  -- step 6: `ι = ι'`, both being the increasing enumeration of the `k`-element set `range ι'`
  have hι : p.1 = q.1 := by
    have hcard : (Finset.univ.image q.1).card = k := by
      rw [Finset.card_image_of_injective _ hq.injective, Finset.card_univ, Fintype.card_fin]
    refine (Finset.orderEmbOfFin_unique hcard (fun j => ?_) hp).trans
      (Finset.orderEmbOfFin_unique hcard
        (fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j)) hq).symm
    obtain ⟨m, hm⟩ := hsub j
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩
  -- step 7: `b = b'` on `range ι`, since `b_{ι(j)} = ⌊z_{ι(j)}⌋ = b'_{ι(j)}`
  have hb : ∀ j, p.2 (p.1 j) = q.2 (p.1 j) := by
    intro j
    obtain ⟨h₁, h₂⟩ := hB j
    obtain ⟨h₃, h₄⟩ := hy' j
    have hzj := hz₁ j
    rw [← hι] at hzj
    rw [hzj] at h₁ h₂
    have h₅ : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) + 1 := by linarith
    have h₆ : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := by linarith
    have : p.2 (p.1 j) < q.2 (p.1 j) + 1 := by exact_mod_cast h₅
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₆
    omega
  -- step 8: as `p ≠ q`, some `l ∉ range ι` has `b_l ≠ b'_l`, and there `x_l = b_l`, `z_l = b'_l`
  obtain ⟨l, hl⟩ := Function.ne_iff.mp fun h : p.2 = q.2 => hpq (Prod.ext hι h)
  have hlι : ∀ m, p.1 m ≠ l := by
    rintro m rfl
    exact hl (hb m)
  calc (1 : ℝ) ≤ |(p.2 l : ℝ) - q.2 l| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hl)
    _ = |x l - z l| := by rw [hx₂ l hlι, hz₂ l (hι ▸ hlι)]
    _ ≤ dist x z := hcoord l

/-- **Geometry of unit lattice faces** (Simon Ch. 6, §5, deformation theorem: the faces `F ∈ 𝓛ₖ`,
`Hᵏ(F̆) = 1`, `diam F ≤ √P` and Lemma 2.1, for faces of any common dimension `k`).  The open unit
cube of `ℝᵏ` has volume `1` (`cmcdtfrfg_cube_volume`).  For `p = (ι, b)` with `ι` strictly
increasing, hence injective, the face map `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry and
`|Φ_p(y) − Φ_p(y')| ≤ √P` on the closed unit cube (`cmcdtfrfg_face_isometry_diam`).  For
`p ≠ q`, `y ∈ (0,1)ᵏ` and `y' ∈ [0,1]ᵏ`, either `1 ≤ |Φ_p(y) − Φ_q(y')|` or
`min(yⱼ, 1 − yⱼ) ≤ |Φ_p(y) − Φ_q(y')|` for some `j` (`cmcdtfrfg_face_separation`). -/
theorem Submission.dimred_mbl_dtfr_face_geometry : ∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) := by
  intro P k
  -- step 1: the open unit cube has volume `1`
  refine ⟨Submission.cmcdtfrfg_cube_volume k, fun p q hp hq => ?_⟩
  -- steps 2-4: `ι` is injective, so `Φ_p` is an isometry and the closed face has diameter `≤ √P`
  obtain ⟨hiso, hdiam⟩ := Submission.cmcdtfrfg_face_isometry_diam P k p.1 p.2 hp.injective
  -- steps 5-8: distinct faces are separated
  exact ⟨hiso, hdiam, Submission.cmcdtfrfg_face_separation P k p q hp hq⟩
/-- **The `(n − 1)`-skeleton of the unit cubical lattice is `Hⁿ`-null** (Simon Ch. 6, proof of the
deformation theorem 5.1, where `spt Q ⊆ Lₙ` (22) is split over the open `n`-faces (26)–(28):
`Hⁿ(L_{n−1}) = 0`, here `n = m + 1`).  The points of `ℝᴾ` with at least `P − m` integer
coordinates lie in the countably many coordinate planes `A(s, z) = {x : xᵢ = zᵢ for i ∈ s}`,
`P ≤ m + |s|`, `z ∈ ℤᴾ`.  Each `A(s, z)` is the image of an isometry `ψ : ℝʳ → ℝᴾ`,
`r = P − |s| ≤ m`, and `ℝʳ` is `μHE[m + 1]`-null: it is a countable union of balls of finite
`μHE[r]` (= Lebesgue) measure, and `r < m + 1`. -/
theorem Submission.dimred_mbl_dtfr_skeleton_null : ∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
  intro P m
  -- (3) `ℝʳ`, `r ≤ m`, is a countable union of closed balls of finite `μHE[r]` = Lebesgue measure,
  -- so each ball, and hence `ℝʳ`, is `μHE[m + 1]`-null
  have hnull : ∀ r : ℕ, r ≤ m → (μHE[m + 1] : Measure (Euclid r)) univ = 0 := by
    intro r hr
    rw [← Metric.iUnion_closedBall_nat (0 : Euclid r)]
    refine measure_iUnion_null fun k => ?_
    refine (Measure.euclideanHausdorffMeasure_zero_or_top (d₁ := r) (d₂ := m + 1) (by omega)
      _).resolve_right ?_
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_closedBall_lt_top.ne
  -- (2), (4) each plane `A(s, z)` with `P ≤ m + |s|` is the image of an isometry `ψ : ℝʳ → ℝᴾ`,
  -- `r = P − |s| ≤ m`, hence `μHE[m + 1]`-null
  have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
      μHE[m + 1] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
    intro s hs z
    obtain ⟨r, hr⟩ : ∃ r, sᶜ.card = r := ⟨_, rfl⟩
    have hrm : r ≤ m := by
      rw [← hr, Finset.card_compl, Fintype.card_fin]
      omega
    -- `κ : Fin r ↪ Fin P` enumerates the coordinates outside `s`
    obtain ⟨κ, hκs, hκ⟩ : ∃ κ : Fin r ↪ Fin P, (∀ l, κ l ∉ s) ∧ Finset.univ.map κ = sᶜ :=
      ⟨(sᶜ.orderEmbOfFin hr).toEmbedding,
        fun l => Finset.mem_compl.1 (sᶜ.orderEmbOfFin_mem hr l), sᶜ.map_orderEmbOfFin_univ hr⟩
    -- `ψ t = (zᵢ on s, 0 off s) + Σₗ tₗ e_{κ l}` has `ψ t = z` on `s` and `ψ t (κ l) = t l`
    obtain ⟨ψ, hψs, hψκ⟩ : ∃ ψ : Euclid r → Euclid P,
        (∀ t, ∀ i ∈ s, ψ t i = z i) ∧ ∀ t l, ψ t (κ l) = t l := by
      refine ⟨fun t => WithLp.toLp 2 (fun i => if i ∈ s then (z i : ℝ) else 0) +
        ∑ l, t l • EuclideanSpace.single (κ l) (1 : ℝ), fun t i hi => ?_, fun t l => ?_⟩
      · have h0 : ∀ l, i ≠ κ l := fun l h => hκs l (h ▸ hi)
        simp [hi, h0]
      · simp [Pi.single_apply, hκs l]
    -- `ψ` is an isometry: `ψ t − ψ t'` has coordinate `tₗ − t'ₗ` at `κ l` and `0` on `s`
    have hiso : Isometry ψ := by
      refine Isometry.of_dist_eq fun t t' => ?_
      rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
      congr 1
      rw [← Finset.sum_subset (Finset.subset_univ sᶜ), ← hκ, Finset.sum_map]
      · simp only [hψκ]
      · intro i _ hi
        have hi' : i ∈ s := by simpa using hi
        simp [hψs t i hi', hψs t' i hi']
    -- `A(s, z) ⊆ ψ '' univ`: `x = ψ (x ∘ κ)` for `x ∈ A(s, z)`
    have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ ψ '' univ := by
      intro x hx
      refine ⟨WithLp.toLp 2 fun l => x (κ l), mem_univ _, ?_⟩
      ext i
      by_cases hi : i ∈ s
      · rw [hψs _ i hi, hx i hi]
      · have hi' : i ∈ Finset.univ.map κ := by
          rw [hκ]
          exact Finset.mem_compl.2 hi
        obtain ⟨l, -, rfl⟩ := Finset.mem_map.1 hi'
        rw [hψκ, PiLp.toLp_apply]
    exact measure_mono_null hsub (by rw [hiso.euclideanHausdorffMeasure_image]; exact hnull r hrm)
  -- (1) `L_m ⊆ ⋃ A(s, z)` over the countably many `s` with `P ≤ m + |s|` and `z ∈ ℤᴾ`
  -- (`zᵢ = ⌊xᵢ⌋`)
  have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆
      ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card}) (z : Fin P → ℤ),
        {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
    rintro x ⟨s, hs, hx⟩
    refine mem_iUnion₂.2 ⟨⟨s, hs⟩, fun i => ⌊x i⌋, fun i hi => ?_⟩
    obtain ⟨w, hw⟩ := hx i hi
    simp [hw]
  -- (5) countable subadditivity
  exact measure_mono_null hcover
    (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
/-- **Simon Ch. 3, Definition 1.4** (the test-function argument of Remark 1.5(3)): if
`a − x ∈ V` for every `a ∈ A`, where `V` is a linear subspace, then every approximate tangent
space `Q` of `A` at `x` is contained in `V`.  Every blow-up `η_{x,r}(A) = r⁻¹(A − x)` lies in
`V`.  For `q ∈ Q \ V` let `d = dist(q, V) > 0` (`V` is closed); the bump
`g = max(0, d/2 − |· − q|) ∈ C_c` vanishes on `V`, so all blow-up integrals of `g` vanish and
in the limit `∫_Q g dHⁿ = 0`.  Since `dim Q = n`, `Hⁿ⌞Q` is regular with support `Q ∋ q`, and
`g ≥ 0` has support `B_{d/2}(q)`, so `∫_Q g dHⁿ > 0`, a contradiction. -/
theorem Submission.dimred_mbl_dtfrpo_approxTangent_le_of_sub_mem : ∀ (P n : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q V : Submodule ℝ (Euclid P)), (∀ a ∈ A, a - x ∈ V) → HasApproximateTangentSpaceAt n A x Q → Q ≤ V := by
  intro P n A x Q V hAV hQ q hqQ
  by_contra hqV
  -- `d = dist(q, V) > 0`: `V` is closed (finite dimension) and contains `0`
  have hd : 0 < infDist q (V : Set (Euclid P)) :=
    (V.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, V.zero_mem⟩).mp hqV
  set d := infDist q (V : Set (Euclid P))
  -- the bump `g = max(0, d/2 − dist(·, q))`
  set g : Euclid P → ℝ := fun y => max 0 (d / 2 - dist y q)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hg_nonneg : 0 ≤ g := fun y => le_max_left 0 _
  have hg_far : ∀ y, d / 2 ≤ dist y q → g y = 0 := fun y hy =>
    max_eq_left (sub_nonpos.mpr hy)
  have hg_supp : Function.support g = ball q (d / 2) := by
    ext y
    rw [Function.mem_support, mem_ball]
    constructor
    · intro hy
      by_contra hy'
      exact hy (hg_far y (not_lt.mp hy'))
    · intro hy
      exact (lt_max_of_lt_right (sub_pos.mpr hy)).ne'
  have hg_cpt : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall q (d / 2)) fun y hy => hg_far y ?_
    rw [mem_closedBall, not_le] at hy
    exact hy.le
  -- `g` vanishes on `V`, as `dist(v, q) ≥ dist(q, V) = d` there
  have hg_V : ∀ v ∈ V, g v = 0 := by
    intro v hv
    refine hg_far v ?_
    have h : d ≤ dist q v := infDist_le_dist_of_mem (SetLike.mem_coe.mpr hv)
    rw [dist_comm] at h
    linarith
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_cpt⟩
  -- the blow-up `η_{x,r}(A)` lies in `V`, so its integral of `f` is `0` (no measurability)
  have hblow : ∀ r : ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] = 0 := by
    intro r
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hg_V _ (V.smul_mem r⁻¹ (hAV a ha))
  -- uniqueness of limits along `𝓝[>] 0`: `∫_Q g dHⁿ = 0`
  have hQ_zero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := by
    refine tendsto_nhds_unique (hQ.2 f) ?_
    simp only [hblow]
    exact tendsto_const_nhds
  -- `dim Q = n`: `Hⁿ⌞Q` is regular with support `Q ∋ q`, so `∫_Q g dHⁿ > 0`
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Euclid P) hQ.1
  have hg_int : Integrable g (μHE[n].restrict (Q : Set (Euclid P))) :=
    hg_cont.integrable_of_hasCompactSupport hg_cpt
  have hq_supp : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
    rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
    exact hqQ
  have hball : 0 < μHE[n].restrict (Q : Set (Euclid P)) (ball q (d / 2)) :=
    (Measure.mem_support_iff_forall q).mp hq_supp _ (ball_mem_nhds q (half_pos hd))
  have hQ_pos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg_nonneg hg_int, hg_supp]
    exact hball
  exact hQ_pos.ne' hQ_zero
/-- **Two orthonormal frames of one plane evaluate covectors equally up to one sign** (Simon
Ch. 6, §1 and §3: an `n`-plane is oriented by `±τ₁ ∧ ⋯ ∧ τₙ` for any orthonormal basis `τ` of
it).  If the orthonormal `n`-frames `τ` and `e` of `ℝᴾ` span the same subspace `W`, then
`α(τ) = α(e) · c` for every `n`-covector `α`, where `c = det_e(τ)` is the determinant of `τ` in
the basis `e` of `W` (`AlternatingMap.eq_smul_basis_det` for `α` restricted to `W`).  As the
change-of-basis determinant between two orthonormal bases of `W`, `c = ±1`. -/
theorem Submission.dimred_mbl_dtfrpo_orthonormal_frame_sign : ∀ (P n : ℕ) (τ e : Fin n → Euclid P), Orthonormal ℝ τ → Orthonormal ℝ e → Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range e) → (∀ α : Covector (Euclid P) n, α τ = α e) ∨ (∀ α : Covector (Euclid P) n, α τ = -α e) := by
  intro P n τ e hτ he hspan
  -- Step 1: `W = span (range e)` has the basis `b = Basis.span` with `b j = e j`, so `finrank W = n`
  let W : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e)
  have he_li : LinearIndependent ℝ e := he.linearIndependent
  let b : Module.Basis (Fin n) ℝ W := Module.Basis.span he_li
  have hb : ∀ j, (b j : Euclid P) = e j := Module.Basis.coe_span_apply he_li
  have hrank : Module.finrank ℝ W = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  -- Step 2: each `τ j` lies in `span (range τ) = W`, giving the family `τW` in `W`
  have hτW : ∀ j, τ j ∈ W := fun j => hspan.le (Submodule.subset_span (Set.mem_range_self j))
  let τW : Fin n → W := Set.codRestrict τ W hτW
  -- Step 3: restricting `α` to `W`, `eq_smul_basis_det` gives `α(τ) = α(e) · det_b(τW)`
  have hdet : ∀ α : Covector (Euclid P) n, α τ = α e * b.det τW := by
    intro α
    have h := congrArg (fun f : W [⋀^Fin n]→ₗ[ℝ] ℝ => f τW)
      ((α.toAlternatingMap.compLinearMap W.subtype).eq_smul_basis_det b)
    have hτ' : (fun j => W.subtype (τW j)) = τ := rfl
    have he' : (fun j => W.subtype (b j)) = e := funext hb
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h
    rw [hτ', he'] at h
    exact h
  -- Step 4: `b` and `τW` are orthonormal bases of `W`, so `det_b(τW) = ±1`
  have hb_on : Orthonormal ℝ b := by
    have h := orthonormal_span he
    convert h using 1
    funext j
    exact Module.Basis.span_apply he_li j
  have hτW_on : Orthonormal ℝ τW := hτ.codRestrict W hτW
  have hτW_sp : ⊤ ≤ Submodule.span ℝ (Set.range τW) :=
    (hτW_on.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, hrank])).ge
  have hc : b.det τW = 1 ∨ b.det τW = -1 := by
    have h := (b.toOrthonormalBasis hb_on).det_to_matrix_orthonormalBasis_real
      (OrthonormalBasis.mk hτW_on hτW_sp)
    rwa [Module.Basis.toBasis_toOrthonormalBasis, OrthonormalBasis.coe_mk] at h
  -- Step 5: the sign `det_b(τW)` does not depend on `α`
  rcases hc with hc | hc
  · exact Or.inl fun α => by rw [hdet α, hc, mul_one]
  · exact Or.inr fun α => by rw [hdet α, hc, mul_neg_one]

/-- **Orientation of a set lying in a coordinate plane** (Simon Ch. 6, §5, (26)–(27): on a face
of the lattice the orientation is `±e₁ ∧ ⋯ ∧ eₙ`; Ch. 3, Definition 1.4).  If `a_i = x_i` for
every `a ∈ A` and every `i ∉ range ι`, and `ξ` is a unit orientation of an approximate tangent
space `Q` of `A` at `x`, then `ξ = ±e_{ι 0} ∧ ⋯ ∧ e_{ι (n−1)}`.  Every `a − x` lies in
`V = span {e_{ι j}}`, so `Q ≤ V`; as `dim Q = n = dim V`, `Q = V`.  Then `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for
an orthonormal basis `τ` of `V`, and `α(τ) = ±α(e_ι)` with one sign for all `n`-covectors `α`. -/
theorem Submission.dimred_mbl_dtfr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  -- Step 1: the coordinate frame `e j = e_{ι j}` is orthonormal (`ι` is injective)
  set e : Fin n → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have he : Orthonormal ℝ e :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp ι hι.injective
  -- Step 2: `v = ∑ i, v i • e_i` lies in `V = span (range e)` if `v i = 0` for `i ∉ range ι`
  have hmem : ∀ v : Euclid P, (∀ i, (∀ j, ι j ≠ i) → v i = 0) →
      v ∈ Submodule.span ℝ (Set.range e) := by
    intro v hv
    rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := h
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
      rw [EuclideanSpace.basisFun_apply]
    · rw [EuclideanSpace.basisFun_repr, hv i (fun j hj => h ⟨j, hj⟩), zero_smul]
      exact Submodule.zero_mem _
  -- Step 3: `a − x ∈ V` for `a ∈ A`, so `Q ≤ V`; `dim Q = n = dim V` gives `Q = V`
  have hAV : ∀ a ∈ A, a - x ∈ Submodule.span ℝ (Set.range e) := fun a ha =>
    hmem _ fun i hi => by rw [PiLp.sub_apply, hA a ha i hi, sub_self]
  have hQV := Submission.dimred_mbl_dtfrpo_approxTangent_le_of_sub_mem P n A x Q _ hAV hQ
  have hQeq : Q = Submodule.span ℝ (Set.range e) := Submodule.eq_of_le_of_finrank_eq hQV (by
    rw [hQ.1, finrank_span_eq_card he.linearIndependent, Fintype.card_fin])
  -- Step 4: `ξ = ±τ` for an orthonormal frame `τ` of `Q = V`, and `α(τ) = ±α(e)` uniformly
  obtain ⟨τ, hτ, hτQ, hσ⟩ := hξ
  rcases Submission.dimred_mbl_dtfrpo_orthonormal_frame_sign P n τ e hτ he (hτQ.trans hQeq)
    with hc | hc <;> rcases hσ with hσ | hσ
  · exact Or.inl fun α => by rw [hσ α, hc α]
  · exact Or.inr fun α => by rw [hσ α, hc α]
  · exact Or.inr fun α => by rw [hσ α, hc α]
  · exact Or.inl fun α => by rw [hσ α, hc α, neg_neg]
/-- **Integrable densities on finitely many unit faces define a current** (Simon Ch. 6, proof of
Theorem 5.1, displays (27)–(30)).  Let `Q₁ ⊆ ℝ^{m+1}` be the open unit cube and, for
`p = (ι, b) ∈ s`, `Φₚ(y) = b + Σⱼ yⱼ e_{ι j}`, `Eₚ = (e_{ι j})ⱼ`, with `wₚ` integrable on `Q₁`.
(I) For every test form `ω`, `y ↦ wₚ(y) ω(Φₚ y)(Eₚ)` is integrable on `Q₁`: it is `wₚ` times a
continuous function bounded by `supₓ ‖ω(x)‖`, as `|α(Eₚ)| ≤ ‖α‖` (the `e_l` are unit vectors).
(II) `L(ω) = Σₚ ∫_{Q₁} wₚ(y) ω(Φₚ y)(Eₚ) dy` is linear with `|L(ω)| ≤ (Σₚ ∫_{Q₁} |wₚ|) · δ`
whenever `‖ω(x)‖ ≤ δ` for all `x`; order-0 uniform convergence on a common compact set then
gives `L(ωⱼ) → 0` for `ωⱼ → 0`, so `L` is a current. -/
theorem Submission.dimred_mbl_dtfric_current_exists : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s w hint
  -- Step 1: the face map `Φₚ` is continuous
  have hΦcont : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), Continuous (fun y : Euclid (m + 1) =>
      WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro p
    exact continuous_const.add
      (continuous_finsetSum _ fun j _ => (PiLp.continuous_apply 2 _ j).smul continuous_const)
  -- Step 2: `y ↦ ω(Φₚ y)(Eₚ)` is continuous (evaluation at `Eₚ` is continuous linear)
  have hhcont : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1))
      (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)),
      Continuous (fun y : Euclid (m + 1) => (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) := by
    intro ω p
    have hω : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ω.property.1.1.continuous
    exact (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
      (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))).continuous.comp (hω.comp (hΦcont p))
  -- Step 3: `|α(Eₚ)| ≤ ‖α‖`, since `‖e_l‖ = 1`
  have hop : ∀ (α : Covector (Euclid P) (m + 1)) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)),
      ‖α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ ‖α‖ := by
    intro α p
    have := α.le_opNorm (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
    simpa [PiLp.norm_single] using this
  -- Step 4: a test form is bounded (continuous with compact support)
  have hbdd : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∃ C : ℝ,
      ∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ C := by
    intro ω
    exact ω.property.1.2.exists_bound_of_continuous ω.property.1.1.continuous
  -- Step 5: (I), integrable times bounded measurable
  have hI : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s,
      IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro ω p hp
    obtain ⟨C, hC⟩ := hbdd ω
    exact (hint p hp).mul_bdd (hhcont ω p).aestronglyMeasurable
      (Eventually.of_forall fun y => (hop _ p).trans (hC _))
  -- Step 6: the functional `L` is linear, by (I)
  let L : TestFormOn (univ : Set (Euclid P)) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * (ω : DifferentialForm (Euclid P) (m + 1))
            (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
      map_add' := by
        intro ω η
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← integral_add (hI ω p hp) (hI η p hp)]
        apply integral_congr_ae
        filter_upwards with y
        simp [mul_add]
      map_smul' := by
        intro c ω
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        ring }
  -- Step 7: `|L(ω)| ≤ A δ` whenever `‖ω(x)‖ ≤ δ` for all `x`, `A = Σₚ ∫_{Q₁} |wₚ|`
  set A : ℝ := ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
  have hest : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (δ : ℝ),
      (∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ δ) → |L ω| ≤ A * δ := by
    intro ω δ hδ
    calc |L ω| ≤ ∑ p ∈ s, |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * (ω : DifferentialForm (Euclid P) (m + 1))
            (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) * δ := by
          apply Finset.sum_le_sum
          intro p hp
          have hpt : ∀ y : Euclid (m + 1), ‖w p y * (ω : DifferentialForm (Euclid P) (m + 1))
              (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ |w p y| * δ := by
            intro y
            rw [norm_mul, Real.norm_eq_abs (w p y)]
            exact mul_le_mul_of_nonneg_left ((hop _ p).trans (hδ _)) (abs_nonneg _)
          have h := norm_integral_le_of_norm_le ((hint p hp).abs.mul_const δ)
            (Eventually.of_forall hpt)
          rw [integral_mul_const, Real.norm_eq_abs] at h
          exact h
      _ = A * δ := by rw [hA, Finset.sum_mul]
  -- Step 8: sequential continuity at `0`, from order-0 uniform convergence on the compact `K`
  -- and `ωⱼ = 0` off `K`
  have hcont : ∀ ωseq : ℕ → TestFormOn (univ : Set (Euclid P)) (m + 1),
      TestFormOnConverges ωseq 0 → Tendsto (fun j => L (ωseq j)) atTop (𝓝 0) := by
    intro ωseq hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (A + 1)) hδ)
    refine ⟨N, fun j hj => ?_⟩
    have hsmall : ∀ x, ‖(ωseq j : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ ε / (A + 1) := by
      intro x
      by_cases hx : x ∈ K
      · have h := hN j hj x hx
        have hz : iteratedFDeriv ℝ 0
            ((0 : TestFormOn (univ : Set (Euclid P)) (m + 1)) : DifferentialForm (Euclid P) (m + 1))
              x = 0 := by
          simp
        rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
        exact h.le
      · have hx' : x ∉ tsupport (ωseq j : DifferentialForm (Euclid P) (m + 1)) :=
          fun h => hx (hsupp j h)
        rw [image_eq_zero_of_notMem_tsupport hx', norm_zero]
        exact hδ.le
    rw [Real.dist_eq, sub_zero]
    calc |L (ωseq j)| ≤ A * (ε / (A + 1)) := hest _ _ hsmall
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  -- Step 9: `D = ⟨L, Step 8⟩` satisfies the formula by definition
  exact ⟨hI, ⟨⟨L, hcont⟩, fun ω => rfl⟩⟩
/-- **Mass bound for a current given by integrable densities on coordinate unit faces** (Simon
Ch. 6, proof of Theorem 5.1, (28) and the first line of (30)).  Let `n = m + 1`, `Q₁ = (0, 1)ⁿ`,
and for `p = (ι, b)` let `Φ_p(y) = b + Σ_j y_j e_{ι(j)}` and `E_p = (e_{ι(0)}, …, e_{ι(m)})`.  If
every `ι` is strictly increasing, every `w_p` is integrable on `Q₁` and
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy` for every test form `ω`, then
`M(D) ≤ Σ_{p ∈ s} ∫_{Q₁} |w_p|`.  For strictly increasing `I`, `α(e_I)²` is one nonnegative
summand of `|α|² = Σ_{J strictly increasing} α(e_J)²`, so `|α(e_I)| ≤ |α|`.  Hence for an
admissible `ω` (`|ω(x)| ≤ 1`) the integrand of each face term is bounded by `|w_p|`, an integrable
majorant. -/
theorem Submission.dimred_mbl_dtfric_mass_le : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) := by
  intro P m s w D hmono hint hD
  -- Step 1 (F1): for strictly increasing `I`, `α(e_I)²` is one nonnegative summand of `|α|²`,
  -- so `|α(e_I)| ≤ |α|`
  have hcoef : ∀ (α : Covector (Euclid P) (m + 1)) (I : Fin (m + 1) → Fin P), StrictMono I →
      |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α := by
    intro α I hI
    unfold covectorEuclideanNorm
    apply Real.abs_le_sqrt
    have hnn : ∀ J ∈ (Finset.univ : Finset (Fin (m + 1) → Fin P)), 0 ≤
        (if StrictMono J then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))) ^ 2
          else 0) := by
      intro J _
      split_ifs <;> positivity
    have hI' := Finset.single_le_sum hnn (Finset.mem_univ I)
    simpa [hI, EuclideanSpace.basisFun_apply] using hI'
  -- Step 2: `M(D)` is the supremum of `D ω` over admissible `ω`; bound each `D ω`
  change D.massOn univ ≤ _
  unfold GeometricCurrentOn.massOn
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hD ω]
  -- Step 5: compare the two sums term by term
  apply Finset.sum_le_sum
  intro p hp
  -- Step 3: `|w_p(y) ω(Φ_p y)(E_p)| ≤ |w_p(y)| |ω(Φ_p y)| ≤ |w_p(y)|` by Step 1 with `I = p.1`
  have hbound : ∀ y : Euclid (m + 1),
      ‖w p y * (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ |w p y| := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := (hcoef _ p.1 (hmono p hp)).trans (hω.2
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
    calc _ ≤ |w p y| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |w p y| := mul_one _
  -- Step 4: `∫ w_p h ≤ |∫ w_p h| ≤ ∫ |w_p|`, with the integrable majorant `|w_p|`
  have hint' := norm_integral_le_of_norm_le (hint p hp).abs (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hint'
  exact (le_abs_self _).trans hint'
/-- **Support of a face current** (Simon Ch. 6, proof of Theorem 5.1, the face currents of (27)).
Let `D ∈ 𝒟_{m+1}(ℝᴾ)` act by `D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p y)(E_p) dy`, where `Q₁` is the
open unit cube, each `w_p` is integrable on `Q₁`, `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and
`E_p = (e_{ι_p(j)})_j`.  Then every `x ∈ spt D` is `Φ_p(y)` for some `p ∈ s` with
`∫_{Q₁} |w_p| ≠ 0` and some `y` in the closed unit cube.  Otherwise `x` lies outside the compact
union `Z` of the closed faces `Φ_p([0,1]^{m+1})` with `∫_{Q₁} |w_p| ≠ 0`, so some ball `B` about
`x` misses `Z`.  Each face integral of a test form supported in `B` vanishes: either `w_p = 0`
a.e. on `Q₁`, or the form vanishes on `Φ_p(Q₁) ⊆ Z`.  So `D` vanishes on `B`, and `x` lies in the
zero region of `D`, contradicting `x ∈ spt D`. -/
theorem Submission.dimred_mbl_dtfric_support_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x := by
  intro P m s w D hint hD x hx
  -- Step 1: otherwise `x` misses every closed face `Φ_p(Cⁿ)` with `∫_{Q₁} |w_p| ≠ 0`
  by_contra hcon
  push Not at hcon
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set C : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  set Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P :=
    fun p y => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
    with hΦ
  set s' := s.filter (fun p => (∫ y in Q, |w p y|) ≠ 0) with hs'
  set Z : Set (Euclid P) := ⋃ p ∈ s', Φ p '' C with hZ
  -- Step 2: `Z` is compact, so some ball about `x` misses it
  have hCcomp : IsCompact C := by
    have hpi : IsCompact (Set.pi univ (fun _ : Fin (m + 1) => Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have himg := hpi.image (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ))
    convert himg using 1
    ext y
    constructor
    · intro hy
      refine ⟨WithLp.ofLp y, ?_, by simp⟩
      intro i _
      exact ⟨(hy i).1, (hy i).2⟩
    · rintro ⟨z, hz, rfl⟩ i
      exact ⟨(hz i (mem_univ i)).1, (hz i (mem_univ i)).2⟩
  have hΦcont : ∀ p, Continuous (Φ p) := by
    intro p
    exact continuous_const.add
      (continuous_finsetSum _ fun j _ => (PiLp.continuous_apply 2 _ j).smul continuous_const)
  have hZcomp : IsCompact Z := s'.isCompact_biUnion (fun p _ => hCcomp.image (hΦcont p))
  have hxZ : x ∉ Z := by
    intro hxZ
    simp only [hZ, mem_iUnion, mem_image] at hxZ
    obtain ⟨p, hp, y, hy, hyx⟩ := hxZ
    rw [hs', Finset.mem_filter] at hp
    exact hcon p hp.1 hp.2 y hy hyx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hZcomp.isClosed.isOpen_compl x hxZ
  -- Step 3: `D` vanishes on `ball x r`, face by face
  have hvan : D.VanishesOn (ball x r) := by
    intro ω hω
    rw [hD ω]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hp0 : (∫ y in Q, |w p y|) = 0
    · -- (a) `w_p = 0` a.e. on `Q₁`
      have habs : (fun y => |w p y|) =ᵐ[volume.restrict Q] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (w p y)) (hint p hp).abs).mp hp0
      apply integral_eq_zero_of_ae
      filter_upwards [habs] with y hy
      have : w p y = 0 := abs_eq_zero.mp hy
      simp [this]
    · -- (b) `ω` vanishes on `Φ_p(Q₁) ⊆ Z`
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      have hyC : y ∈ C := fun i => ⟨(hy i).1.le, (hy i).2.le⟩
      have hps' : p ∈ s' := by rw [hs', Finset.mem_filter]; exact ⟨hp, hp0⟩
      have hmemZ : Φ p y ∈ Z := mem_biUnion hps' (mem_image_of_mem _ hyC)
      have hnot : Φ p y ∉ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) := by
        intro hin
        exact hball (hω hin) hmemZ
      have h0 := image_eq_zero_of_notMem_tsupport hnot
      simp only [hΦ] at h0
      simp [h0]
  -- Step 4: `ball x r` is open with compact closure, so `x` lies in the zero region of `D`
  have hxzero : x ∈ D.zeroRegion := by
    refine mem_sUnion.mpr ⟨ball x r, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, mem_ball_self hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  -- Step 5: this contradicts `x ∈ spt D`
  exact hx.2 hxzero
/-- **One partial derivative integrated over the open unit cube** (Fubini and the one-variable
fundamental theorem of calculus).  For `G ∈ C¹(ℝ^{k+1})` and a coordinate `i`, the partial
derivative `DG(·)eᵢ` is integrable on `Q^{k+1} = (0, 1)^{k+1}` and
`∫_{Q^{k+1}} DG(y)eᵢ dy = ∫_{Q^k} G(y', yᵢ = 1) dy' − ∫_{Q^k} G(y', yᵢ = 0) dy'`. -/
theorem Submission.dimred_mbl_dtfrcb_cube_partial_ftc : ∀ (k : ℕ) (i : Fin (k + 1)) (G : Euclid (k + 1) → ℝ), ContDiff ℝ 1 G → IntegrableOn (fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1} ∧ ∫ y in {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1}, fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = (∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) (WithLp.ofLp y)))) - ∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) (WithLp.ofLp y))) := by
  intro k i G hG
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hg : Continuous fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- The open cube `Q^d` lies in the compact image of the closed box `[0, 1]^d` under `toLp`.
  have hcpt : ∀ d : ℕ,
      IsCompact (WithLp.toLp 2 '' Set.pi univ fun _ : Fin d => Icc (0 : ℝ) 1 : Set (Euclid d)) :=
    fun d => (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hsub : ∀ d : ℕ, {y : Euclid d | ∀ j, 0 < y j ∧ y j < 1} ⊆
      WithLp.toLp 2 '' Set.pi univ fun _ : Fin d => Icc (0 : ℝ) 1 :=
    fun d y hy => ⟨WithLp.ofLp y, fun j _ => ⟨(hy j).1.le, (hy j).2.le⟩, rfl⟩
  refine ⟨(hg.continuousOn.integrableOn_compact (hcpt (k + 1))).mono_set (hsub (k + 1)), ?_⟩
  -- Transport the cube integrals to the open boxes of `Fin d → ℝ`.
  have htrans : ∀ (d : ℕ) (f : Euclid d → ℝ),
      ∫ y in {y : Euclid d | ∀ j, 0 < y j ∧ y j < 1}, f y =
        ∫ x in Set.pi univ fun _ : Fin d => Ioo (0 : ℝ) 1, f (WithLp.toLp 2 x) := by
    intro d f
    have hpre : WithLp.toLp 2 ⁻¹' {y : Euclid d | ∀ j, 0 < y j ∧ y j < 1} =
        Set.pi univ fun _ : Fin d => Ioo (0 : ℝ) 1 := by
      ext x
      simp
    rw [← hpre, (PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding f]
  rw [htrans, htrans, htrans]
  dsimp only
  -- Split off the `i`-th coordinate: `(t, z) ↦ insertNth i t z` is measure preserving.
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm
      (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm _
  have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm ⁻¹'
      (Set.pi univ fun _ : Fin (k + 1) => Ioo (0 : ℝ) 1) =
        Ioo (0 : ℝ) 1 ×ˢ Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1 := by
    ext ⟨t, z⟩
    simp only [Set.mem_preimage, MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv_apply, Set.mem_univ_pi, Set.mem_prod]
    rw [Fin.forall_iff_succAbove i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  -- The integrand in the coordinates `(t, z)` is continuous, hence integrable on the box.
  have hFc : Continuous fun p : ℝ × (Fin k → ℝ) =>
      fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2)) (EuclideanSpace.single i (1 : ℝ)) :=
    hg.comp ((PiLp.continuous_toLp 2 _).comp
      (Continuous.finInsertNth (A := fun _ => ℝ) i continuous_fst continuous_snd))
  have hFint : Integrable (fun p : ℝ × (Fin k → ℝ) =>
      fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2)) (EuclideanSpace.single i (1 : ℝ)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    exact (hFc.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc))).mono_set
      (Set.prod_mono Ioo_subset_Icc_self (Set.pi_mono fun _ _ => Ioo_subset_Icc_self))
  -- Along each line `t ↦ insertNth i t z` (direction `eᵢ`), the fundamental theorem of calculus.
  have hline : ∀ (z : Fin k → ℝ) (t : ℝ), WithLp.toLp 2 (Fin.insertNth i t z) =
      WithLp.toLp 2 (Fin.insertNth i 0 z) + t • EuclideanSpace.single i (1 : ℝ) := by
    intro z t
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨l, rfl⟩
    · simp
    · simp [Fin.succAbove_ne]
  have hftc : ∀ z : Fin k → ℝ,
      ∫ t in Ioo (0 : ℝ) 1,
          fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ)) =
        G (WithLp.toLp 2 (Fin.insertNth i 1 z)) - G (WithLp.toLp 2 (Fin.insertNth i 0 z)) := by
    intro z
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => G (WithLp.toLp 2 (Fin.insertNth i s z)))
        (fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ))) t := by
      intro t
      have hcurve : HasDerivAt
          (fun s : ℝ => WithLp.toLp 2 (Fin.insertNth i 0 z) + s • EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) t := by
        simpa only [one_smul] using
          ((hasDerivAt_id' t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
            (WithLp.toLp 2 (Fin.insertNth i 0 z))
      have h := (hGd (WithLp.toLp 2 (Fin.insertNth i 0 z) +
        t • EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp_hasDerivAt t hcurve
      simpa only [Function.comp_def, ← hline] using h
    have hcont : Continuous fun t : ℝ =>
        fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ)) :=
      hg.comp ((PiLp.continuous_toLp 2 _).comp
        (Continuous.finInsertNth (A := fun _ => ℝ) i continuous_id continuous_const))
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)
  have hface : ∀ c : ℝ, IntegrableOn (fun z : Fin k → ℝ => G (WithLp.toLp 2 (Fin.insertNth i c z)))
      (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    intro c
    have hc : Continuous fun z : Fin k → ℝ => G (WithLp.toLp 2 (Fin.insertNth i c z)) :=
      hG.continuous.comp ((PiLp.continuous_toLp 2 _).comp
        (Continuous.finInsertNth (A := fun _ => ℝ) i continuous_const continuous_id))
    exact (hc.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
      (Set.pi_mono fun _ _ => Ioo_subset_Icc_self)
  calc ∫ x in Set.pi univ (fun _ : Fin (k + 1) => Ioo (0 : ℝ) 1),
        fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ))
      = ∫ p in Ioo (0 : ℝ) 1 ×ˢ Set.pi univ (fun _ : Fin k => Ioo (0 : ℝ) 1),
          fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2)) (EuclideanSpace.single i (1 : ℝ))
          ∂(volume.prod volume) := by
        have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)
          (fun x => fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ)))
          (Set.pi univ fun _ : Fin (k + 1) => Ioo (0 : ℝ) 1)
        rw [hpre] at h
        exact h.symm
    _ = ∫ z in Set.pi univ (fun _ : Fin k => Ioo (0 : ℝ) 1), ∫ t in Ioo (0 : ℝ) 1,
          fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [← Measure.prod_restrict]
        exact integral_prod_symm _ hFint
    _ = ∫ z in Set.pi univ (fun _ : Fin k => Ioo (0 : ℝ) 1),
          (G (WithLp.toLp 2 (Fin.insertNth i 1 z)) - G (WithLp.toLp 2 (Fin.insertNth i 0 z))) :=
        integral_congr_ae (Eventually.of_forall hftc)
    _ = _ := integral_sub (hface 1) (hface 0)

/-- **Stokes' formula for one oriented lattice unit cube, from a divergence representation of
`dγ`** (the cubes `z + C`, `z ∈ ℤᴾ`, of the lattice of Simon Ch. 6, §5, p. 159).  Let
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` on the open unit cube `Q^{m+1}` (`b ∈ ℤᴾ`, `ι` arbitrary),
`E = (e_{ι(0)}, …, e_{ι(m)})`, `E'ᵢ = (e_{ι(succAbove i l)})ₗ`, and let `G` be a `C¹` field with
`Gᵢ(y) = (−1)ⁱ γ(Φ y)(E'ᵢ)` and `dγ(Φ y)(E) = tr DG(y)` (no regularity of `γ` is needed).  Then
`∫_{Q^{m+1}} dγ(Φ y)(E) = Σᵢ (−1)ⁱ (∫_{Q^m} γ(Φ¹ᵢ)(E'ᵢ) − ∫_{Q^m} γ(Φ⁰ᵢ)(E'ᵢ))`, where
`Φᶜᵢ(y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}`.
By the orthonormal trace formula and the chain rule for `Gᵢ = projᵢ ∘ G`, `tr DG = Σᵢ ∂ᵢGᵢ`;
`dimred_mbl_dtfrcb_cube_partial_ftc` integrates each `∂ᵢGᵢ` to the difference of the integrals of
`Gᵢ` over the faces `yᵢ = 1` and `yᵢ = 0`, and `Φ(insertNth i c y') = Φᶜᵢ(y')`. -/
theorem Submission.dimred_mbl_dtfrcb_cube_stokes : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m) (G : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 G → (∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), G y i = (-1 : ℝ) ^ (i : ℕ) * γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun l => EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ))) → (∀ y : Euclid (m + 1), exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * ((∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) - ∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) := by
  intro P m ι b γ G hG hGi hdγ
  -- each coordinate `Gᵢ = projᵢ ∘ G` is `C¹`
  have hC1 : ∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y => G y i) := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  -- `tr DG(y) = Σᵢ ⟪eᵢ, DG(y) eᵢ⟫ = Σᵢ ∂ᵢGᵢ(y)`
  have htr : ∀ y : Euclid (m + 1), LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
      ∑ i, fderiv ℝ (fun z => G z i) y (EuclideanSpace.single i (1 : ℝ)) := by
    intro y
    have hd : HasFDerivAt G (fderiv ℝ G y) y :=
      ((hG.differentiable one_ne_zero) y).hasFDerivAt
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : HasFDerivAt (fun z => G z i)
        ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G y)) y :=
      (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp y hd
    rw [hi.fderiv]
    simp [EuclideanSpace.inner_single_left]
  -- so `dγ(Φ y)(E) = Σᵢ ∂ᵢGᵢ(y)`, and each `∂ᵢGᵢ` is integrable on the cube
  simp only [hdγ, htr]
  rw [integral_finsetSum _ fun i _ =>
    (Submission.dimred_mbl_dtfrcb_cube_partial_ftc m i _ (hC1 i)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `∫ ∂ᵢGᵢ` is the difference of the integrals of `Gᵢ` over the faces `yᵢ = 1` and `yᵢ = 0`
  rw [(Submission.dimred_mbl_dtfrcb_cube_partial_ftc m i _ (hC1 i)).2]
  simp only [hGi]
  -- `Φ(insertNth i c y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}`
  have hface : ∀ (c : ℝ) (y : Euclid m),
      WithLp.toLp 2 (fun k => (b k : ℝ)) +
          ∑ j, (WithLp.toLp 2 (Fin.insertNth i c (WithLp.ofLp y)) : Euclid (m + 1)) j •
            EuclideanSpace.single (ι j) (1 : ℝ) =
        WithLp.toLp 2 (fun k => (b k : ℝ)) + c • EuclideanSpace.single (ι i) (1 : ℝ) +
          ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ) := by
    intro c y
    rw [Fin.sum_univ_succAbove _ i, add_assoc]
    simp
  -- the front face is based at `b + e_{ι(i)}`
  have hbase : WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) =
      WithLp.toLp 2 (fun k => (b k : ℝ)) + EuclideanSpace.single (ι i) (1 : ℝ) := by
    ext k
    by_cases hk : k = ι i
    · subst hk
      simp
    · simp [hk]
  simp only [hface, one_smul, zero_smul, add_zero, ← hbase]
  -- `(−1)ⁱ` leaves both integrals; `ι (succAbove i l) = (ι ∘ succAbove i) l` by definition
  rw [integral_const_mul, integral_const_mul, mul_sub]
  rfl
/-- Regrouping the signed faces of a lattice chain into a lattice chain of one dimension less.
Index an oriented lattice `(m+1)`-cube by `p = (ι, b)`, `ι` strictly increasing, and its `i`-th
front and back faces by `(ι ∘ succAbove i, b + 𝟙_{ι i})` and `(ι ∘ succAbove i, b)`.  Then
`∑_p β_p ∑_i (-1)ⁱ (I(front) - I(back)) = ∑_{q ∈ s'} β'_q I(q)` for integers `β'_q` and lattice
`m`-cube indices `q ∈ s'` not depending on `I`: `s'` is the set of all faces and
`β'_q = ∑_{p,i} β_p (-1)ⁱ ([front = q] - [back = q])`. -/
theorem Submission.dimred_mbl_dtfrcb_face_regroup : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ q ∈ s', StrictMono q.1) ∧ ∀ I : (Fin m → Fin P) × (Fin P → ℤ) → ℝ, ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2)) = ∑ q ∈ s', (β' q : ℝ) * I q := by
  classical
  intro P m s β hs
  -- `front p i` and `back p i`: the two copies of the `i`-th face of the cube indexed by `p`
  let front : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → (Fin m → Fin P) × (Fin P → ℤ) :=
    fun p i => (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1)
  let back : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → (Fin m → Fin P) × (Fin P → ℤ) :=
    fun p i => (p.1 ∘ Fin.succAbove i, p.2)
  -- `s'` collects all faces; `β' q` is the signed sum of the coefficients of the faces equal to `q`
  let S : Finset ((Fin m → Fin P) × (Fin P → ℤ)) :=
    s.biUnion fun p => Finset.univ.biUnion fun i => {front p i, back p i}
  let c : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → (Fin m → Fin P) × (Fin P → ℤ) → ℤ :=
    fun p i q => β p * (-1) ^ (i : ℕ) * ((if front p i = q then 1 else 0) - (if back p i = q then 1 else 0))
  have hfront : ∀ p ∈ s, ∀ i, front p i ∈ S := fun p hp i =>
    Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩⟩
  have hback : ∀ p ∈ s, ∀ i, back p i ∈ S := fun p hp i =>
    Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩⟩
  refine ⟨S, fun q => ∑ p ∈ s, ∑ i : Fin (m + 1), c p i q, ?_, fun I => ?_⟩
  · intro q hq
    obtain ⟨p, hp, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨i, -, hq⟩ := Finset.mem_biUnion.1 hq
    rcases Finset.mem_insert.1 hq with rfl | hq
    · exact (hs p hp).comp (Fin.strictMono_succAbove i)
    · rw [Finset.mem_singleton.1 hq]
      exact (hs p hp).comp (Fin.strictMono_succAbove i)
  · -- for each `(p, i)` the `q`-sum over `S` picks out the two faces of `p`
    have key : ∀ p ∈ s, ∀ i : Fin (m + 1), ∑ q ∈ S, (c p i q : ℝ) * I q =
        (β p : ℝ) * ((-1 : ℝ) ^ (i : ℕ) * (I (front p i) - I (back p i))) := by
      intro p hp i
      simp only [c, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sub,
        Int.cast_ite, Int.cast_zero, mul_sub, sub_mul, mul_ite, ite_mul, mul_one, mul_zero,
        zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq, hfront p hp i, hback p hp i,
        ite_true]
      ring
    calc ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2))
        = ∑ p ∈ s, ∑ i : Fin (m + 1), ∑ q ∈ S, (c p i q : ℝ) * I q := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (key p hp i).symm
      _ = ∑ p ∈ s, ∑ q ∈ S, ∑ i : Fin (m + 1), (c p i q : ℝ) * I q :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ q ∈ S, ∑ p ∈ s, ∑ i : Fin (m + 1), (c p i q : ℝ) * I q := Finset.sum_comm
      _ = ∑ q ∈ S, ((∑ p ∈ s, ∑ i : Fin (m + 1), c p i q : ℤ) : ℝ) * I q := by
          simp only [Int.cast_sum, Finset.sum_mul]
/-- Deformation theorem, face replacement: divergence form of `dγ` on a coordinate face.  For
`Φ(y) = b + ∑ⱼ yⱼ e_{ι j}` and `G(y)ᵢ = (−1)ⁱ γ(Φ y)(e_{ι ∘ succAbove i})` (`γ(Φ y)` on the
frame `E = (e_{ι 0}, …, e_{ι m})` with its `i`-th vector removed), `G` is smooth,
`‖G(y)‖ ≤ |γ(Φ y)|` and `dγ(Φ y)(E) = div G(y) = trace DG(y)`. -/
theorem Submission.dimred_mbl_dtfr_face_divergence : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m) (G : Euclid (m + 1) → Euclid (m + 1)), StrictMono ι → ContDiff ℝ (⊤ : ℕ∞) γ → (∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), G y i = (-1 : ℝ) ^ (i : ℕ) * γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun l => EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ))) → ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y : Euclid (m + 1), ‖G y‖ ≤ covectorEuclideanNorm (γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y : Euclid (m + 1), exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) := by
  intro P m ι b γ G hι hγ hG
  classical
  -- `Φ y = c + L y` parametrizes the face; `L y = ∑ j, y j • e_{ι j}`
  let L : Euclid (m + 1) →L[ℝ] Euclid P :=
    ∑ j, (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single (ι j) (1 : ℝ))
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)
  have hL : ∀ y, L y = ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) := by
    intro y
    simp [L]
  have hΦL : Φ = fun y => WithLp.toLp 2 (fun k => (b k : ℝ)) + L y := by
    funext y
    simp only [Φ, hL]
  have hΦd : ∀ y, HasFDerivAt Φ L y := by
    intro y
    rw [hΦL]
    exact L.hasFDerivAt.const_add _
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [hΦL]
    exact contDiff_const.add L.contDiff
  -- `ev i α = α (w i)`, `w i` the frame with its `i`-th vector removed
  let w : Fin (m + 1) → Fin m → Euclid P := fun i l =>
    EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ)
  let ev : Fin (m + 1) → Covector (Euclid P) m →L[ℝ] ℝ := fun i =>
    ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (w i)
  have hGi : ∀ y i, G y i = (-1 : ℝ) ^ (i : ℕ) * ev i (γ (Φ y)) := fun y i => hG y i
  have hGc : ∀ i, (fun y => G y i) = fun y => (-1 : ℝ) ^ (i : ℕ) * ev i (γ (Φ y)) := by
    intro i
    funext y
    exact hGi y i
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_euclidean]
    intro i
    rw [hGc i]
    exact contDiff_const.mul ((ev i).contDiff.comp (hγ.comp hΦs))
  refine ⟨hGs, ?_, ?_⟩
  · -- `‖G y‖² = ∑ i, γ(Φ y)(w i)²` is a sub-sum of `|γ(Φ y)|²`
    intro y
    show ‖G y‖ ≤ covectorEuclideanNorm (γ (Φ y))
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    apply Real.sqrt_le_sqrt
    let g : (Fin m → Fin P) → ℝ := fun I => if StrictMono I then
      (γ (Φ y) (fun l => EuclideanSpace.basisFun (Fin P) ℝ (I l))) ^ 2 else 0
    have hinj : Function.Injective fun i : Fin (m + 1) => ι ∘ Fin.succAbove i :=
      hι.injective.comp_left.comp Fin.succAbove_left_injective
    have hterm : ∀ i, ‖G y i‖ ^ 2 = g (ι ∘ Fin.succAbove i) := by
      intro i
      have hmono : StrictMono (ι ∘ Fin.succAbove i) := hι.comp (Fin.strictMono_succAbove i)
      simp only [g, hmono, ↓reduceIte, Real.norm_eq_abs, sq_abs, hGi, mul_pow]
      rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> simp [h, ev, w]
    calc ∑ i, ‖G y i‖ ^ 2 = ∑ i, g (ι ∘ Fin.succAbove i) := Finset.sum_congr rfl fun i _ => hterm i
      _ = ∑ I ∈ Finset.univ.image fun i : Fin (m + 1) => ι ∘ Fin.succAbove i, g I :=
        (Finset.sum_image hinj.injOn).symm
      _ ≤ ∑ I, g I :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun I _ _ => by
          simp only [g]
          split_ifs <;> positivity
  · -- both sides are `∑ i, (-1)^i Dγ(Φ y)(e_{ι i})(w i)`
    intro y
    show exteriorDerivative γ (Φ y) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) =
      LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)
    have hcoord : ∀ i (v : Euclid (m + 1)),
        fderiv ℝ G y v i = (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ γ (Φ y) (L v)) (w i) := by
      intro i v
      have h1 : HasFDerivAt (fun y => G y i)
          ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G y)) y :=
        (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp y
          ((hGs.differentiable (by simp)) y).hasFDerivAt
      have h2 : HasFDerivAt (fun y => G y i)
          ((-1 : ℝ) ^ (i : ℕ) • (ev i).comp ((fderiv ℝ γ (Φ y)).comp L)) y := by
        rw [hGc i]
        exact ((ev i).hasFDerivAt.comp y ((hγd (Φ y)).hasFDerivAt.comp y (hΦd y))).const_mul _
      have h3 := congrArg (fun f : Euclid (m + 1) →L[ℝ] ℝ => f v) (h1.unique h2)
      simpa [ev] using h3
    have hfd : ∀ (i : Fin (m + 1)) (x : Euclid P),
        fderiv ℝ (fun x => γ x (Fin.removeNth i fun j => EuclideanSpace.single (ι j) (1 : ℝ))) x =
          (ev i).comp (fderiv ℝ γ x) := fun i x =>
      ((ev i).hasFDerivAt.comp x (hγd x).hasFDerivAt).fderiv
    rw [exteriorDerivative_apply (hγd _),
      LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis,
      Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd]
    simp [Matrix.diag, LinearMap.toMatrix_apply, hcoord, hL, ev, w, zsmul_eq_mul]
/-- `spt(A − B) ⊆ spt A ∪ spt B`, `M_W(A − B) ≤ M_W(A) + M_W(B)`, `spt ∂A ⊆ spt A` and
`∂(A − B) = ∂A − ∂B`.  A point of `U` in zero-region sets `W₁` of `A` and `W₂` of `B` lies in
`W₁ ∩ W₂`, an open set with compact closure in `U` on which `A − B` vanishes.  For a `W`-admissible
`ω`, `−ω` is `W`-admissible and `(A − B)(ω) = A(ω) + B(−ω)`.  A zero-region set of `A` is one of
`∂A`, since `tsupport dγ ⊆ tsupport γ`.  Finally `∂(A − B)(γ) = A(dγ) − B(dγ) = (∂A − ∂B)(γ)`. -/
theorem Submission.dimred_mbl_dtfr_current_calculus : (∀ (P n : ℕ) (U W : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).support ⊆ A.support ∪ B.support ∧ (A - B).massOn W ≤ A.massOn W + B.massOn W) ∧ ∀ (P m : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U (m + 1)), A.boundary.support ⊆ A.support ∧ (A - B).boundary = A.boundary - B.boundary := by
  refine ⟨fun P n U W A B => ⟨?_, ?_⟩, fun P m U A B => ⟨?_, ?_⟩⟩
  · -- `spt(A − B) ⊆ spt A ∪ spt B`
    rintro y ⟨hyU, hyZ⟩
    by_contra hAB
    have hA : y ∈ A.zeroRegion := not_not.mp fun h => hAB (Or.inl ⟨hyU, h⟩)
    have hB : y ∈ B.zeroRegion := not_not.mp fun h => hAB (Or.inr ⟨hyU, h⟩)
    obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hA
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hyW₂⟩ := mem_sUnion.mp hB
    -- `W₁ ∩ W₂` belongs to the family whose union is the zero region of `A − B`
    have hcl : closure (W₁ ∩ W₂) ⊆ closure W₁ := closure_mono inter_subset_left
    refine hyZ (mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
      hW₁c.of_isClosed_subset isClosed_closure hcl, hcl.trans hW₁U, fun ω hω => ?_⟩, hyW₁, hyW₂⟩)
    change A ω - B ω = 0
    rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
  · -- `M_W(A − B) ≤ M_W(A) + M_W(B)`
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    -- `−ω` is `W`-admissible
    have hneg : -ω ∈ massAdmissibleOn U n W := by
      refine ⟨?_, fun x => ?_⟩
      · show tsupport (-(ω : DifferentialForm (Euclid P) n)) ⊆ W
        rw [tsupport_neg]
        exact hω.1
      · show covectorEuclideanNorm (-(ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [covectorEuclideanNorm_neg]
        exact hω.2 x
    -- `(A − B)(ω) = A(ω) + B(−ω)`
    have heq : (A - B) ω = A ω + B (-ω) := by
      rw [show B (-ω) = -B ω from map_neg B.toCurrent ω]
      exact sub_eq_add_neg (A ω) (B ω)
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [heq]
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.massOn W + B.massOn W := add_le_add (A.le_massOn hω) (B.le_massOn hneg)
  · -- `spt ∂A ⊆ spt A`: a zero-region set of `A` is one of `∂A`
    rintro y ⟨hyU, hyZ⟩
    refine ⟨hyU, fun hA => hyZ ?_⟩
    obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hA
    refine mem_sUnion.mpr ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, fun γ hγ => ?_⟩, hyW₁⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hW₁v _ ((tsupport_exteriorDerivative_subset (γ : DifferentialForm (Euclid P) m)).trans hγ)
  · -- `∂(A − B)(γ) = (A − B)(dγ) = A(dγ) − B(dγ) = (∂A − ∂B)(γ)`
    ext γ
    rfl

/-- **Simon Ch. 6, proof of 5.1, (26)–(28) and (33)** (with `n = m + 1`): an integer
multiplicity `Q₀ ∈ 𝒟ₙ(ℝᴾ)` with `spt Q₀` in a compact `K` and in the lattice `n`-skeleton `L_n`
is a finite sum of integer `L¹` densities on open unit lattice `n`-faces
`F̆_p = Φ_p((0, 1)ⁿ)`, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` (`p = (ι, b)`, `ι` increasing):
`Q₀(ω) = Σ_p ∫_{(0,1)ⁿ} u_p(y) ⟨ω(Φ_p(y)), e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}⟩ dy`, `Σ_p ∫ |u_p| ≤ M(Q₀)`.
Write `Q₀ = τ(M, θ, ξ)`.  The faces whose open face meets `spt Q₀ ⊆ K` are finitely many, and
distinct open faces are disjoint (face_geometry).  `M` lies in their union up to
`(M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null (`imrep_carrier_sdiff_support_null`, skeleton_null), as
a point of `L_n ∖ L_m` lies on an open face.  On each face `Q₀⌞F̆_p` is an integer density `u_p`
with `∫ |u_p| ≤ μ_{Q₀}(F̆_p)` (face_density; `Φ_p` is an isometry).  Summing over the disjoint
faces gives the representation and, by (MR), `Σ_p ∫ |u_p| ≤ μ_{Q₀}(ℝᴾ) = M(Q₀)`. -/
theorem Submission.dimred_mbl_dtfr_skeleton_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ) (K : Set (Euclid P)) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → ∃ (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q₀.mass ∧ (∀ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.support) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  classical
  intro _ hMR hIMC P m K Q₀ hK hQ₀ hQ₀K hQ₀L
  obtain ⟨-, hIMCb, -, -⟩ := hIMC
  -- Step 1: an integer multiplicity representation `R = (M, θ, ξ)` of `Q₀`
  obtain ⟨R, hR⟩ := hQ₀
  -- the open unit cube `Q₁ = (0, 1)ⁿ` and the open faces `F̆_p = Φ_p(Q₁)`
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  set F : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Set (Euclid P) := fun p =>
    (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' Q₁
  -- Step 8: for increasing `ι`, `Φ_p` is an isometry (face_geometry (a)), hence a measurable
  -- embedding, so the open faces are Borel
  have hiso : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      Isometry (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) := fun p hp =>
    Isometry.of_dist_eq ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p p hp hp).1
  have hQ₁o : IsOpen Q₁ := by
    rw [hQ₁, ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hFm : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → MeasurableSet (F p) :=
    fun p hp => (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image'
      hQ₁o.measurableSet
  -- Step 6: distinct open faces are disjoint (face_geometry (c))
  have hdisj : ∀ p q : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 →
      p ≠ q → Disjoint (F p) (F q) := by
    intro p q hp hq hpq
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h0 : dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
          ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = 0 :=
      dist_eq_zero.2 hyy'.symm
    rcases ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p q hp hq).2.2 hpq y y' hy
      (fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩) with h | ⟨j, hj⟩
    · linarith [h.trans_eq h0]
    · linarith [hj.trans_eq h0, lt_min (hy j).1 (sub_pos.2 (hy j).2)]
  -- Step 5: the faces `p` (with `ι` increasing) whose open face meets `spt Q₀` form a finite set,
  -- since `spt Q₀ ⊆ K` is compact
  have hSfin : {p : (Fin (m + 1) → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧
      ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Q₀.support}.Finite :=
    (Submission.dimred_mbl_dtfrsd_faces_meeting_compact_finite P (m + 1) K hK).subset
      fun p ⟨_, y, hy, hyS⟩ => ⟨y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hQ₀K hyS⟩
  set s := hSfin.toFinset
  have hsS : ∀ p ∈ s, StrictMono p.1 ∧
      ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Q₀.support :=
    fun p hp => hSfin.mem_toFinset.1 hp
  have hpd : Set.Pairwise (↑s) (Disjoint on F) := by
    intro p hp q hq hpq
    exact hdisj p q (hsS p hp).1 (hsS q hq).1 hpq
  -- Steps 8 and 10–12 for one face (face_density): an integer density `u_p` on `Q₁`
  have hfd : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), ∃ v : Euclid (m + 1) → ℝ,
      StrictMono p.1 → (∀ y, ∃ z : ℤ, v y = z) ∧ IntegrableOn v Q₁ ∧
        ENNReal.ofReal (∫ y in Q₁, |v y|) ≤ R.measure (F p) ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
          ∫ x in R.carrier ∩ F p, (R.mult x : ℝ) *
              R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
            ∫ y in Q₁, v y * (ω : DifferentialForm (Euclid P) (m + 1))
              (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
                ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro p
    by_cases hp : StrictMono p.1
    · obtain ⟨v, hv⟩ := Submission.dimred_mbl_dtfrsd_face_density hIMCb
        Submission.dimred_mbl_dtfr_plane_orientation P (m + 1) R p hp (hiso p hp)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose u hu using hfd
  refine ⟨s, u, fun p hp => (hsS p hp).1, fun p hp => (hu p (hsS p hp).1).1,
    fun p hp => (hu p (hsS p hp).1).2.1, ?_, ?_, ?_⟩
  · -- Step 11: `Σ_p ∫_{Q₁} |u_p| ≤ Σ_p μ(F̆_p) = μ(⋃_p F̆_p) ≤ μ(ℝᴾ) = M(Q₀)`, by (MR)
    calc ENNReal.ofReal (∑ p ∈ s, ∫ y in Q₁, |u p y|)
        = ∑ p ∈ s, ENNReal.ofReal (∫ y in Q₁, |u p y|) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
      _ ≤ ∑ p ∈ s, R.measure (F p) :=
          Finset.sum_le_sum fun p hp => (hu p (hsS p hp).1).2.2.1
      _ = R.measure (⋃ p ∈ s, F p) :=
          (measure_biUnion_finset hpd fun p hp => hFm p (hsS p hp).1).symm
      _ ≤ R.measure univ := measure_mono (subset_univ _)
      _ = Q₀.mass := (hMR P (m + 1) univ Q₀ R isOpen_univ hR univ isOpen_univ).symm
  · -- each closed face of `s` meets `spt Q₀`
    intro p hp
    obtain ⟨-, y, hy, hyS⟩ := hsS p hp
    exact ⟨y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hyS⟩
  · -- Step 12: the representation of `Q₀(ω)`
    intro ω
    -- Step 7: `M ∖ ⋃_p (M ∩ F̆_p) ⊆ (M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null by Steps 2 and 3
    have hnull : μHE[m + 1] (R.carrier \ ⋃ p ∈ s, R.carrier ∩ F p) = 0 := by
      refine measure_mono_null ?_ (measure_union_null
        (Submission.imrep_carrier_sdiff_support_null P (m + 1) univ Q₀ R isOpen_univ hR)
        (Submission.dimred_mbl_dtfr_skeleton_null P m))
      rintro x ⟨hxM, hxU⟩
      by_cases hxS : x ∈ Q₀.support
      · refine mem_union_right _ ?_
        by_contra hxL
        -- Step 4: `x ∈ L_n ∖ L_m` lies on an open face `F̆_p`, and `p ∈ s` as `x ∈ spt Q₀`
        obtain ⟨p, y, hp, hy, hpy⟩ :=
          Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face P m x (hQ₀L hxS) hxL
        refine hxU (mem_iUnion₂.2 ⟨p, hSfin.mem_toFinset.2 ⟨hp, y, hy, ?_⟩, hxM, y, hy, hpy⟩)
        rw [hpy]
        exact hxS
      · exact mem_union_left _ ⟨hxM, hxS⟩
    have hae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, R.carrier ∩ F p := by
      refine ae_eq_set.2 ⟨hnull, ?_⟩
      rw [sdiff_eq_empty.2 (iUnion₂_subset fun p _ => inter_subset_left)]
      exact measure_empty
    have hint := Submission.regcomp_rim_action_integrable P (m + 1) univ R ω
    have hpd' : Set.Pairwise (↑s) (Disjoint on fun p => R.carrier ∩ F p) := by
      intro p hp q hq hpq
      exact Disjoint.mono inter_subset_right inter_subset_right (hpd hp hq hpq)
    rw [hR ω]
    show ∫ x in R.carrier, (R.mult x : ℝ) *
      R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] = _
    rw [setIntegral_congr_set hae, integral_biUnion_finset s
      (fun p hp => R.measurableSet_carrier.inter (hFm p (hsS p hp).1)) hpd'
      (fun p _ => IntegrableOn.mono_set hint inter_subset_left)]
    exact Finset.sum_congr rfl fun p hp => (hu p (hsS p hp).1).2.2.2 ω

/-- **Currents given by integrable densities on finitely many unit faces** (Simon Ch. 6, proof of
Theorem 5.1, displays (27)–(30) and (34)).  Let `Q₁ ⊆ ℝ^{m+1}` be the open unit cube and, for
`p = (ι, b) ∈ s` with `ι` strictly increasing, `Φₚ(y) = b + Σⱼ yⱼ e_{ι j}`, `Eₚ = (e_{ι j})ⱼ`,
with `wₚ` integrable on `Q₁`.  Then (I) each `y ↦ wₚ(y) ω(Φₚ y)(Eₚ)` is integrable on `Q₁`;
(II) `D(ω) = Σₚ ∫_{Q₁} wₚ(y) ω(Φₚ y)(Eₚ) dy` defines a current; and every such `D` has
(a) `M(D) ≤ Σₚ ∫_{Q₁} |wₚ|`, (b) `M(∂D) ≤ Σₚ Bₚ` whenever `|∫_{Q₁} wₚ div G| ≤ Bₚ` for every
smooth `G` with `|G| ≤ 1`, and (c) `spt D` in the closed faces `Φₚ([0,1]^{m+1})` with
`∫_{Q₁} |wₚ| ≠ 0`.  For (b), an admissible `γ` gives on each face the smooth field
`Gₚ(y)ᵢ = (−1)ⁱ γ(Φₚ y)(Eₚ ∘ succAbove i)`, with `|Gₚ| ≤ |γ ∘ Φₚ| ≤ 1` and
`dγ(Φₚ y)(Eₚ) = div Gₚ(y)`; so `∂D(γ) = D(dγ) = Σₚ ∫_{Q₁} wₚ div Gₚ ≤ Σₚ Bₚ`. -/
theorem Submission.dimred_mbl_dtfr_face_integral_current : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ∧ (∀ B : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ B p) → D.boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, B p)) ∧ (∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x) := by
  intro P m s w hmono hint
  -- Step 1: (I) and (II), by `dimred_mbl_dtfric_current_exists`
  obtain ⟨hI, D₀, hD₀⟩ := Submission.dimred_mbl_dtfric_current_exists P m s w hint
  refine ⟨hI, ⟨D₀, hD₀⟩, fun D hD => ⟨?_, ?_, ?_⟩⟩
  -- Step 2: (III)(a), by `dimred_mbl_dtfric_mass_le`
  · exact Submission.dimred_mbl_dtfric_mass_le P m s w D hmono hint hD
  -- Step 3: (III)(b).  `M(∂D)` is the supremum of `∂D(γ)` over admissible `γ`; bound each
  -- `∂D(γ) = D(dγ)` face by face
  · intro B hB
    change D.boundary.massOn univ ≤ _
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro r ⟨γ, hγ, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    rw [GeometricCurrentOn.boundary_apply, hD]
    apply Finset.sum_le_sum
    intro p hp
    -- the field `Gₚ(y)ᵢ = (−1)ⁱ γ(Φₚ y)(Eₚ ∘ succAbove i)` of `dimred_mbl_dtfr_face_divergence`
    -- is smooth, with `‖Gₚ(y)‖ ≤ |γ(Φₚ y)|` and `dγ(Φₚ y)(Eₚ) = div Gₚ(y)`
    set G : Euclid (m + 1) → Euclid (m + 1) := fun y => WithLp.toLp 2 (fun i : Fin (m + 1) =>
      (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m)
        (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)))
    obtain ⟨hGsmooth, hGnorm, hGdiv⟩ := Submission.dimred_mbl_dtfr_face_divergence P m p.1 p.2
      (γ : DifferentialForm (Euclid P) m) G (hmono p hp) γ.property.1.1 (fun y i => rfl)
    -- `‖Gₚ‖ ≤ 1`, since `γ` is admissible
    have hG1 : ∀ y, ‖G y‖ ≤ 1 := fun y => (hGnorm y).trans (hγ.2 _)
    -- the form underlying the test form `dγ` is `exteriorDerivative γ`
    have hdiv : ∀ y, w p y * ((exteriorDerivativeTestOn (univ : Set (Euclid P)) m γ :
        TestFormOn (univ : Set (Euclid P)) (m + 1)) : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) =
        w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) := by
      intro y
      rw [← hGdiv y]
      rfl
    -- the `p`-th face term is `∫_{Q₁} wₚ div Gₚ ≤ |∫_{Q₁} wₚ div Gₚ| ≤ Bₚ`
    calc _ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
          integral_congr_ae (Eventually.of_forall hdiv)
      _ ≤ |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| := le_abs_self _
      _ ≤ B p := hB p hp G hGsmooth hG1
  -- Step 4: (III)(c), by `dimred_mbl_dtfric_support_faces`
  · exact Submission.dimred_mbl_dtfric_support_faces P m s w D hint hD
/-- **Boundary variation on the open faces of a lattice chain** (Simon Ch. 6, proof of 5.1,
displays (27)–(28) and (32): `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|` by the reasoning of 2.35).  Let
`Q₀(ω) = Σ_{p ∈ s} ∫_{Q₁} u_p(y) ω(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) dy` with `M(∂Q₀) < ∞`.  The
separation `(c)` of `Submission.dimred_mbl_dtfr_face_geometry` and
`Submission.dimred_mbl_dtfrbv_face_neighbourhoods` give open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint
and missing every other closed face; put `V_p = M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`.  Then
`Σ_p V_p ≤ M(∂Q₀)` by `Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le`.  `(i)` The test form
`γ` of `Submission.dimred_mbl_dtfrbv_face_test_form` is admissible for `N_p` and has
`gᵢ(y) = (-1)ⁱ γ(Φ_p y)(e_{ι ∘ i.succAbove})`, so `Submission.dimred_mbl_dtfr_face_divergence`
(with `G := g`) gives `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = div g(y)`.  `dγ` vanishes on the other
faces, so `∫ u_p div g = Q₀(dγ) = ∂Q₀(γ) ≤ V_p`.  `(ii)` If `V_p ≠ 0`, some admissible `γ` for
`N_p` has `∂Q₀(γ) > 0`; by (VO) `tsupport γ ⊆ N_p` meets `spt ∂Q₀ ⊆ spt Q₀`
(`Submission.dimred_mbl_dtfr_current_calculus`).  By
`Submission.dimred_mbl_dtfr_face_integral_current`, `spt Q₀` lies on the closed faces, and of
these only the face of `p` meets `N_p`. -/
theorem Submission.dimred_mbl_dtfr_boundary_variation : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → Q₀.boundary.mass < ∞ → ∃ V : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q₀.boundary.mass ∧ (∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p) ∧ (∀ p ∈ s, V p ≠ 0 → ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.boundary.support) := by
  intro hVO P m s u Q₀ hs hu hQ₀ hmass
  -- step 1: open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing the other closed faces, from the
  -- separation `(c)` of `face_geometry`
  obtain ⟨N, hN⟩ := Submission.dimred_mbl_dtfrbv_face_neighbourhoods P (m + 1)
    fun p q hp hq => ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p q hp hq).2.2
  -- step 3: `M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`, so `V_p := M_{N_p}(∂Q₀)` is a real number
  have hfin : ∀ p, Q₀.boundary.massOn (N p) ≠ ∞ := fun p =>
    ne_top_of_le_ne_top hmass.ne (Q₀.boundary.massOn_mono (subset_univ (N p)))
  refine ⟨fun p => (Q₀.boundary.massOn (N p)).toReal, fun p _ => ENNReal.toReal_nonneg, ?_, ?_,
    ?_⟩
  · -- step 9: the `N_p`, `p ∈ s`, are pairwise disjoint, so `Σ_p M_{N_p}(∂Q₀) ≤ M(∂Q₀)`
    have hdisj : (s : Set ((Fin (m + 1) → Fin P) × (Fin P → ℤ))).PairwiseDisjoint N := by
      intro p hp q hq hpq
      exact ((hN p (hs p hp)).2.2 q (hs q hq) hpq.symm).2
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => ENNReal.toReal_nonneg]
    calc ∑ p ∈ s, ENNReal.ofReal (Q₀.boundary.massOn (N p)).toReal
        = ∑ p ∈ s, Q₀.boundary.massOn (N p) :=
          Finset.sum_congr rfl fun p _ => ENNReal.ofReal_toReal (hfin p)
      _ ≤ Q₀.boundary.massOn (⋃ p ∈ s, N p) :=
          Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le P m univ Q₀.boundary _ s N hdisj
      _ ≤ Q₀.boundary.mass := Q₀.boundary.massOn_mono (subset_univ _)
  · intro p hp g hg hgc hgs hgb
    obtain ⟨hNo, hNF, hNq⟩ := hN p (hs p hp)
    -- step 5: the test form `γ` for `g` is admissible for `N_p`, so `∂Q₀(γ) ≤ V_p`
    obtain ⟨γ, hγs, hγn, hγg⟩ := Submission.dimred_mbl_dtfrbv_face_test_form P m p (N p) g
      (hs p hp) hNo hNF hg hgc hgs hgb
    have hle : Q₀.boundary γ ≤ (Q₀.boundary.massOn (N p)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin p)).1 (Q₀.boundary.le_massOn ⟨hγs, hγn⟩)
    -- step 6: `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = trace Dg(y)`, by `face_divergence` with `G := g`
    have hdiv := (Submission.dimred_mbl_dtfr_face_divergence P m p.1 p.2
      (γ : DifferentialForm (Euclid P) m) g (hs p hp) γ.property.1.1 hγg).2.2
    -- steps 7–8: `∂Q₀(γ) = Q₀(dγ) = Σ_q ∫_{Q₁} u_q(y) dγ(Φ_q y)(E_q) dy = ∫_{Q₁} u_p div g`
    have hval : Q₀.boundary γ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
      rw [GeometricCurrentOn.boundary_apply, hQ₀, Finset.sum_eq_single_of_mem p hp]
      · congr 1
        funext y
        change u p y * exteriorDerivative (γ : DifferentialForm (Euclid P) m) _ _ = _
        rw [hdiv y]
      · -- step 7: for `q ≠ p`, `Φ_q(Q₁)` misses `N_p ⊇ tsupport γ ⊇ tsupport dγ`
        intro q hq hqp
        refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
        have hz : exteriorDerivative (γ : DifferentialForm (Euclid P) m)
            (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
              ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => (hNq q (hs q hq) hqp).1 y
            (fun i => ⟨(hy i).1.le, (hy i).2.le⟩) (hγs (tsupport_exteriorDerivative_subset _ h))
        change u q y * exteriorDerivative (γ : DifferentialForm (Euclid P) m) _ _ = 0
        rw [hz]
        simp
    rw [← hval]
    exact hle
  · intro p hp hV
    -- step 10: `V_p ≠ 0` gives `M_{N_p}(∂Q₀) > 0`, so some admissible `γ` for `N_p` has
    -- `∂Q₀(γ) > 0`
    have hpos : 0 < Q₀.boundary.massOn (N p) := by
      refine pos_iff_ne_zero.2 fun h => hV ?_
      simp only [h, ENNReal.toReal_zero]
    unfold GeometricCurrentOn.massOn at hpos
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγpos⟩ := lt_sSup_iff.1 hpos
    -- by (VO), `tsupport γ ⊆ N_p` meets `spt ∂Q₀` at some `x`
    obtain ⟨x, hxγ, hx⟩ := Set.not_disjoint_iff.1 fun hd =>
      (ENNReal.ofReal_pos.1 hγpos).ne' (hVO P m univ Q₀.boundary γ hd)
    -- step 2: `spt ∂Q₀ ⊆ spt Q₀` (`current_calculus`), so `face_integral_current` gives
    -- `x = Φ_q(y)` with `q ∈ s` and `y ∈ [0,1]ⁿ`; step 1: `q = p`, since `x ∈ N_p`
    obtain ⟨q, hq, -, y, hy, rfl⟩ :=
      ((Submission.dimred_mbl_dtfr_face_integral_current P m s u hs hu).2.2 Q₀ hQ₀).2.2 x
        ((Submission.dimred_mbl_dtfr_current_calculus.2 P m univ Q₀ Q₀).1 hx)
    by_cases hqp : q = p
    · subst hqp
      exact ⟨y, hy, hx⟩
    · exact absurd (hγ.1 hxγ) (((hN p (hs p hp)).2.2 q (hs q hq) hqp).1 y hy)

/-- **Open lattice faces are disjoint, and their union is flat near each of its points** (Simon
Ch. 6, §5, chapter-06.txt lines 1841–1844 and 1899–1911: the interiors `F̆` of the faces
`F ∈ 𝓛ₙ`, and `P = Σ_F β_F [[F]]` with `M(P) = Σ_F |β_F|`).  Assume (FG), the type of
`dimred_mbl_dtfr_face_geometry`.  Let `S` be a finite set of pairs `p = (ι, b)` with `ι` strictly
increasing, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, `F̆_p = Φ_p((0,1)ᵏ)` and `C = ⋃_{q ∈ S} F̆_q`.
(a) A common point `Φ_p(t) = Φ_q(t')` of `F̆_p` and `F̆_q`, `p ≠ q`, is at distance `0` from itself,
while by the separation in (FG) that distance is at least `1` or some `min(tⱼ, 1 − tⱼ) > 0`.
(b) For `x = Φ_p(t)`, `t ∈ (0,1)ᵏ`, take `δ = min({1} ∪ {min(tⱼ, 1 − tⱼ)})` and let `|z − x| < δ`.
If `z = Φ_q(t') ∈ C`, separation forces `q = p`, so `z − x = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}` lies in
`V_p = span{e_{ι(j)}}`.  Conversely, if `z − x = Σⱼ cⱼ e_{ι(j)}`, then `z = Φ_p(t + c)` and, `Φ_p`
being an isometry, `|cⱼ| ≤ |c| = |z − x| < δ`, so `t + c ∈ (0,1)ᵏ` and `z ∈ F̆_p ⊆ C`. -/
theorem Submission.dimred_mbl_dtfrpi_face_union_local_plane : (∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)))) → ∀ (P k : ℕ) (S : Finset ((Fin k → Fin P) × (Fin P → ℤ))), (∀ p ∈ S, StrictMono p.1) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}) ((fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})) ∧ ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euclid P, dist z (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) < δ → (z ∈ ⋃ q ∈ S, (fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ↔ z - (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro FG P k S hS
  -- step 0: the isometry and separation facts of (FG) at `(P, k)`
  obtain ⟨-, FGpq⟩ := FG P k
  refine ⟨fun p hp q hq hpq => ?_, fun p hp t ht => ?_⟩
  -- step 1 (a): a common point `w = Φ_p(t) = Φ_q(t')` is at distance `0` from itself, against the
  -- separation of the open face `F̆_p` from the closed face of `q`
  · rw [Set.disjoint_left]
    rintro w ⟨t, ht, rfl⟩ ⟨t', ht', hw⟩
    beta_reduce at hw
    obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
    rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
    · rw [hw, dist_self] at h
      linarith
    · rw [hw, dist_self] at hj
      linarith [lt_min (ht j).1 (sub_pos.mpr (ht j).2)]
  -- step 2 (b): `δ := min ({1} ∪ {min(tⱼ, 1 − tⱼ)})`, so `0 < δ ≤ 1` and `δ ≤ min(tⱼ, 1 − tⱼ)`
  obtain ⟨δ, hδ, hδ1, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, δ ≤ min (t j) (1 - t j) := by
    let D : Finset ℝ := insert 1 (Finset.univ.image fun j => min (t j) (1 - t j))
    refine ⟨D.min' (Finset.insert_nonempty _ _), (Finset.lt_min'_iff _ _).mpr fun d hd => ?_,
      Finset.min'_le _ _ (Finset.mem_insert_self _ _), fun j => Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
      exact lt_min (ht j).1 (sub_pos.mpr (ht j).2)
  refine ⟨δ, hδ, fun z hz => ⟨fun hzC => ?_, fun hzV => ?_⟩⟩
  -- step 3 (⇒): `z = Φ_q(t')` with `q ∈ S` and `t' ∈ (0,1)ᵏ`
  · rw [Set.mem_iUnion₂] at hzC
    obtain ⟨q, hq, t', ht', hzq⟩ := hzC
    beta_reduce at hzq
    by_cases hpq : p = q
    -- for `q = p`, `z − x = Φ_p(t') − Φ_p(t) = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}`
    · subst hpq
      rw [← hzq, Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun j => t' j - t j, by simp only [sub_smul, Finset.sum_sub_distrib]; abel⟩
    -- for `q ≠ p`, separation gives `1 ≤ |z − x|` or `min(tⱼ, 1 − tⱼ) ≤ |z − x|`, both `≥ δ`
    · obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
      rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
      · rw [hzq, dist_comm] at h
        linarith
      · rw [hzq, dist_comm] at hj
        linarith [hδt j]
  -- step 4 (⇐): `z − x = Σⱼ cⱼ e_{ι(j)}`
  · rw [Submodule.mem_span_range_iff_exists_fun] at hzV
    obtain ⟨c, hc⟩ := hzV
    obtain ⟨hiso, -, -⟩ := FGpq p p (hS p hp) (hS p hp)
    -- `t' := t + c` has coordinates `tⱼ + cⱼ`, and `Φ_p(t') = x + (z − x) = z`
    have hcoord : ∀ j, (t + WithLp.toLp 2 c) j = t j + c j := fun j => by
      rw [PiLp.add_apply, PiLp.toLp_apply]
    have hz' : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, (t + WithLp.toLp 2 c) j • EuclideanSpace.single (p.1 j) (1 : ℝ) = z := by
      simp only [hcoord, add_smul, Finset.sum_add_distrib, hc]
      abel
    -- `|cⱼ| = |t'ⱼ − tⱼ| ≤ |t' − t| = |Φ_p(t') − Φ_p(t)| = |z − x| < δ`, as `Φ_p` is an isometry
    have hc' : ∀ j, |c j| < δ := fun j => by
      have h := PiLp.dist_apply_le (t + WithLp.toLp 2 c) t j
      rw [← hiso, hz', hcoord, Real.dist_eq, add_sub_cancel_left] at h
      exact h.trans_lt hz
    -- hence `0 < tⱼ + cⱼ < 1`, and `z = Φ_p(t') ∈ F̆_p ⊆ C`
    rw [Set.mem_iUnion₂]
    refine ⟨p, hp, t + WithLp.toLp 2 c, fun j => ?_, hz'⟩
    obtain ⟨hc₁, hc₂⟩ := abs_lt.mp (hc' j)
    rw [hcoord]
    constructor <;> linarith [hδt j, min_le_left (t j) (1 - t j), min_le_right (t j) (1 - t j)]
/-- **Finitely many disjoint oriented rectifiable pieces form an integer multiplicity current**
(Simon Ch. 6, Definition 3.1 and 6.3.1 (‡); used in the deformation theorem 6.5.1 for the
polyhedral currents, whose pieces are the open faces).  Let `S` be finite and, for `p ∈ S`, let
the pieces `F_p ⊆ U` be pairwise disjoint Borel sets with `Hᵏ(F_p) < ∞` and `F_p ⊆ G_p(ℝᵏ)` for
a Lipschitz `G_p`, let `m_p > 0`, and let `ξ_p` orient an approximate tangent space of
`C = ⋃_{q ∈ S} F_q` at each point of `F_p`.  Then `(C, θ, ξ)`, with `θ = Σ_q m_q 1_{F_q}` and
`ξ = ξ_p` on `F_p` (`0` off `C`), is an `IMRep`.  As `θ = m_p` and `ξ = ξ_p` on `F_p`, its action
is `Σ_p m_p ∫_{F_p} ⟨ω, ξ_p⟩ dHᵏ` and its mass measure of `ℝᴾ` is `Σ_p m_p Hᵏ(F_p)`. -/
theorem Submission.dimred_mbl_dtfrpi_finite_piece_imrep : ∀ (P k : ℕ) (I : Type) (U : Set (Euclid P)) (S : Finset I) (F : I → Set (Euclid P)) (m : I → ℕ) (ξ : I → MultiVector P k) (G : I → Euclid k → Euclid P), (∀ p ∈ S, MeasurableSet (F p)) → (∀ p ∈ S, F p ⊆ U) → (∀ p ∈ S, μHE[k] (F p) ≠ ∞) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (F p) (F q)) → (∀ p ∈ S, 0 < m p) → (∀ p ∈ S, ∃ K : NNReal, LipschitzWith K (G p)) → (∀ p ∈ S, F p ⊆ range (G p)) → (∀ p ∈ S, ∀ x ∈ F p, ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξ p) Q) → ∃ R : IMRep U k, (∀ ω : TestFormOn U k, R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, (m p : ℝ) * ∫ x in F p, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ R.measure univ = ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
  intro P k I U S F m ξ G hFm hFU hFfin hdisj hmpos hGlip hFG htan
  classical
  -- step 1: the carrier `C = ⋃_{q ∈ S} F_q` is Borel and lies in `U`
  have hCm : MeasurableSet (⋃ q ∈ S, F q) := Finset.measurableSet_biUnion S hFm
  have hCU : (⋃ q ∈ S, F q) ⊆ U := Set.iUnion₂_subset hFU
  -- step 2: a point of `F_p` lies in no other piece
  have hone : ∀ p ∈ S, ∀ q ∈ S, ∀ x ∈ F p, x ∈ F q → q = p := by
    intro p hp q hq x hxp hxq
    by_contra hqp
    exact Set.disjoint_left.mp (hdisj q hq p hp hqp) hxq hxp
  -- step 3: the multiplicity `θ = Σ_q m_q 1_{F_q}` is measurable and `θ = m_p > 0` on `F_p`
  let θ : Euclid P → ℕ := fun x => ∑ q ∈ S, (F q).indicator (fun _ => m q) x
  have hθm : Measurable θ :=
    Finset.measurable_sum S fun q hq => measurable_const.indicator (hFm q hq)
  have hθ : ∀ p ∈ S, ∀ x ∈ F p, θ x = m p := by
    intro p hp x hx
    show ∑ q ∈ S, (F q).indicator (fun _ => m q) x = m p
    rw [Finset.sum_eq_single_of_mem p hp]
    · exact Set.indicator_of_mem hx _
    · intro q hq hqp
      exact Set.indicator_of_notMem (fun hxq => hqp (hone p hp q hq x hx hxq)) _
  have hθpos : ∀ x ∈ ⋃ q ∈ S, F q, 0 < θ x := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    rw [hθ p hp x hxp]
    exact hmpos p hp
  -- step 4: the orientation, `ξ_p` on `F_p` and `0` off `C`: the right fold over a list of `S`
  -- of `(q, acc) ↦ if x ∈ F_q then ξ_q else acc`, starting from `0`
  let orient : List I → Euclid P → MultiVector P k := fun L x =>
    L.foldr (fun q acc => if x ∈ F q then ξ q else acc) 0
  have horient_sm : ∀ L : List I, (∀ q ∈ L, q ∈ S) → StronglyMeasurable (orient L) := by
    intro L
    induction L with
    | nil => exact fun _ => stronglyMeasurable_const
    | cons a L ih =>
      intro hL
      show StronglyMeasurable fun x => if x ∈ F a then ξ a else orient L x
      exact StronglyMeasurable.ite (hFm a (hL a List.mem_cons_self)) stronglyMeasurable_const
        (ih fun q hq => hL q (List.mem_cons_of_mem a hq))
  have horient : ∀ L : List I, (∀ q ∈ L, q ∈ S) → ∀ p ∈ L, ∀ x ∈ F p, orient L x = ξ p := by
    intro L
    induction L with
    | nil => intro _ p hp; simp at hp
    | cons a L ih =>
      intro hL p hpL x hx
      have hp : p ∈ S := hL p hpL
      show (if x ∈ F a then ξ a else orient L x) = ξ p
      by_cases hxa : x ∈ F a
      · rw [ite_eq_left hxa, hone p hp a (hL a List.mem_cons_self) x hx hxa]
      · rw [ite_eq_right hxa]
        refine ih (fun q hq => hL q (List.mem_cons_of_mem a hq)) p ?_ x hx
        rcases List.mem_cons.mp hpL with rfl | hpL'
        · exact absurd hx hxa
        · exact hpL'
  let ξC : Euclid P → MultiVector P k := orient S.toList
  have hSL : ∀ q ∈ S.toList, q ∈ S := fun q hq => Finset.mem_toList.mp hq
  have hξCm : StronglyMeasurable ξC := horient_sm S.toList hSL
  have hξC : ∀ p ∈ S, ∀ x ∈ F p, ξC x = ξ p := fun p hp =>
    horient S.toList hSL p (Finset.mem_toList.mpr hp)
  -- step 5: `C` is countably `k`-rectifiable, with `M₀ = ∅` and the Lipschitz maps `G_p` listed
  -- along `S.toList`, padded with constant maps
  have hrect : CountablyRectifiable k (⋃ q ∈ S, F q) := by
    refine ⟨∅, measure_empty, fun j => if h : j < S.toList.length then G (S.toList.get ⟨j, h⟩)
      else fun _ => 0, fun j => ?_, fun x hx => ?_⟩
    · by_cases h : j < S.toList.length
      · simp only [h, ↓reduceDIte]
        exact hGlip _ (hSL _ (List.get_mem _ _))
      · simp only [h, ↓reduceDIte]
        exact ⟨0, LipschitzWith.const 0⟩
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨y, rfl⟩ := hFG p hp hxp
      obtain ⟨⟨j, hj⟩, hjp⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hp)
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, y, ?_⟩)
      simp only [hj, ↓reduceDIte, hjp]
  -- step 6: `∫_C θ dHᵏ = Σ_p m_p Hᵏ(F_p) < ∞`, as the `F_p` are disjoint and `θ = m_p` on `F_p`
  have hpd : Set.PairwiseDisjoint (S : Set I) F := fun p hp q hq hpq => hdisj p hp q hq hpq
  have hθint : ∫⁻ x in ⋃ q ∈ S, F q, (θ x : ℝ≥0∞) ∂μHE[k] =
      ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
    rw [lintegral_biUnion_finset hpd hFm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hon : EqOn (fun x => (θ x : ℝ≥0∞)) (fun _ => (m p : ℝ≥0∞)) (F p) := by
      intro x hx
      simp only [hθ p hp x hx]
    rw [setLIntegral_congr_fun (hFm p hp) hon, setLIntegral_const]
  have hθfin : ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun p hp => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hFfin p hp)
  -- step 7: `∫_{C ∩ K} θ dHᵏ ≤ ∫_C θ dHᵏ < ∞`
  have hθloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ q ∈ S, F q) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := fun K _ _ =>
    ne_top_of_le_ne_top (by rw [hθint]; exact hθfin) (lintegral_mono_set Set.inter_subset_left)
  -- step 8: `ξ` orients an approximate tangent space at every point of `C`, hence `Hᵏ⌞C`-a.e.
  have horients : ∀ᵐ x ∂(μHE[k].restrict (⋃ q ∈ S, F q)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξC x) Q := by
    refine ae_restrict_of_forall_mem hCm fun x hx => ?_
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨Q, hQ, hξQ⟩ := htan p hp x hxp
    exact ⟨Q, hQ, by rw [hξC p hp x hxp]; exact hξQ⟩
  -- step 9: the triple `(C, θ, ξ)`
  let R : IMRep U k :=
    { carrier := ⋃ q ∈ S, F q
      mult := θ
      orient := ξC
      measurableSet_carrier := hCm
      carrier_subset := hCU
      rectifiable := hrect
      measurable_mult := hθm
      mult_pos := hθpos
      locallyIntegrable_mult := hθloc
      aestronglyMeasurable_orient := hξCm.aestronglyMeasurable
      orients := horients }
  refine ⟨R, fun ω => ?_, ?_⟩
  -- step 10: on `F_p` the integrand is `m_p ⟨ω, ξ_p⟩`, continuous with compact support and so
  -- integrable for the finite measure `Hᵏ⌞F_p`; the action splits over the disjoint pieces
  · have hωc : Continuous (ω : DifferentialForm (Euclid P) k) := ω.2.1.1.continuous
    have hωs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.2.1.2
    have hon : ∀ p ∈ S, EqOn (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x))
        (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x)) (F p) := by
      intro p hp x hx
      simp only [hθ p hp x hx, hξC p hp x hx]
    have hint : ∀ p ∈ S, IntegrableOn
        (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x)) (F p) μHE[k] := by
      intro p hp
      have : IsFiniteMeasure (μHE[k].restrict (F p)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hFfin p hp).lt_top⟩
      have hg : Integrable (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x))
          (μHE[k].restrict (F p)) :=
        (continuous_const.mul ((ξ p).continuous.comp hωc)).integrable_of_hasCompactSupport
          (hωs.comp_left (map_zero (ξ p))).mul_left
      exact IntegrableOn.congr_fun hg (hon p hp).symm (hFm p hp)
    show ∫ x in ⋃ q ∈ S, F q, (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] = _
    rw [integral_biUnion_finset S hFm hpd hint]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [setIntegral_congr_fun (hFm p hp) (hon p hp), integral_const_mul]
  -- step 11: `μ_T(ℝᴾ) = ∫ θ d(Hᵏ⌞C) = Σ_p m_p Hᵏ(F_p)`, by step 6
  · show ((μHE[k].restrict (⋃ q ∈ S, F q)).withDensity fun x => (θ x : ℝ≥0∞)) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hθint]

/-- **Lattice polyhedral chains are integer multiplicity, with mass `Σ_F |β_F|`** (Simon Ch. 6,
§5, in the proof of the deformation theorem 6.5.1: `P = Σ_F β_F [[F]]` is integer multiplicity
and `M(P) = Σ_F |β_F|`).  Here `T(ω) = Σ_{p ∈ s} β_p ∫_{(0,1)ᵏ} ⟨ω(Φ_p y), e_{ι(0)} ∧ ⋯ ∧
e_{ι(k-1)}⟩ dy`, where `Φ_p(y) = b + Σ_j y_j e_{ι(j)}` maps `(0,1)ᵏ` isometrically onto the open
lattice face `F̆_p` of `p = (ι, b)`.  The open faces with `β_p ≠ 0` are disjoint, and near each of
its points their union `C` agrees with the plane of that face, which is therefore its approximate
tangent space.  So `C`, with multiplicity `|β_p|` and orientation
`sign(β_p) e_{ι(0)} ∧ ⋯ ∧ e_{ι(k-1)}` on `F̆_p`, represents `T`.  The hypothesis (MR)
(`M_W(T) = μ_R(W)` for open `W` whenever the `IMRep` `R` represents `T`) then gives
`M(T) = Σ_p |β_p| Hᵏ(F̆_p) = Σ_p |β_p|`, which is at least `1` unless every `β_p` vanishes, and
then `T = 0`. -/
theorem Submission.dimred_mbl_dtfr_polyhedral_im : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P k : ℕ) (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → IsIntegerMultiplicity T ∧ T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) ∧ (T = 0 ∨ 1 ≤ T.mass) := by
  intro MR P k s β T hmono hT
  -- step 1: the open cube `Q₁ = (0,1)ᵏ` is Borel with volume `1`, and each `Φ_p` is an isometry
  let Q₁ : Set (Euclid k) := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}
  let Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  obtain ⟨hvol, hFG⟩ := Submission.dimred_mbl_dtfr_face_geometry P k
  have hQm : MeasurableSet Q₁ := by
    have hQ : Q₁ = ⋂ i, ({y : Euclid k | 0 < y i} ∩ {y | y i < 1}) := by
      ext y
      exact ⟨fun h => mem_iInter.2 h, fun h => mem_iInter.1 h⟩
    rw [hQ]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
        (measurableSet_lt (PiLp.continuous_apply 2 _ i).measurable measurable_const)
  have hiso : ∀ p ∈ s, Isometry (Φ p) := fun p hp =>
    Isometry.of_dist_eq (hFG p p (hmono p hp) (hmono p hp)).1
  -- step 2: the open face `F̆_p = Φ_p(Q₁)` is Borel, `Hᵏ(F̆_p) = 1`, and
  -- `∫_{F̆_p} h dHᵏ = ∫_{Q₁} h ∘ Φ_p`
  have hface : ∀ p ∈ s, MeasurableSet (Φ p '' Q₁) ∧ μHE[k] (Φ p '' Q₁) = 1 ∧
      ∀ h : Euclid P → ℝ, ∫ x in Φ p '' Q₁, h x ∂μHE[k] = ∫ y in Q₁, h (Φ p y) := by
    intro p hp
    obtain ⟨h₁, h₂, h₃⟩ :=
      Submission.dimred_mbl_dtfrpi_isometry_image_integral P k (Φ p) Q₁ (hiso p hp) hQm
    exact ⟨h₁, h₂.trans hvol, h₃⟩
  -- step 3: the faces `S` with `β_p ≠ 0`, the `k`-vectors `e_p = e_{ι(0)} ∧ ⋯ ∧ e_{ι(k-1)}` and the
  -- orientations `ξ_p = sign(β_p) e_p`
  obtain ⟨S, hS⟩ : ∃ S, S = s.filter fun p => β p ≠ 0 := ⟨_, rfl⟩
  have hSs : ∀ p ∈ S, p ∈ s ∧ β p ≠ 0 := fun p hp => Finset.mem_filter.mp (hS ▸ hp)
  have hSmono : ∀ p ∈ S, StrictMono p.1 := fun p hp => hmono p (hSs p hp).1
  have hE : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), ∃ e : MultiVector P k, StrictMono p.1 →
      Module.finrank ℝ (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) = k ∧
      (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧
      IsUnitOrientationOf e (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) ∧
      IsUnitOrientationOf (-e) (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
    intro p
    by_cases hp : StrictMono p.1
    · obtain ⟨hrank, e, he⟩ := Submission.dimred_mbl_dtfrpi_coord_plane_orientation P k p.1 hp
      exact ⟨e, fun _ => ⟨hrank, he⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose e he using hE
  let ξ : (Fin k → Fin P) × (Fin P → ℤ) → MultiVector P k := fun p =>
    if 0 < β p then e p else -e p
  -- step 4: the open faces in `S` are disjoint, and near `x = Φ_p(t)` their union
  -- `C = ⋃_{q ∈ S} F̆_q` is the plane `x + V_p`; so `V_p` is the approximate tangent space of `C`
  -- at `x`, and `ξ_p` orients it
  obtain ⟨hdisj, hflat⟩ := Submission.dimred_mbl_dtfrpi_face_union_local_plane
    Submission.dimred_mbl_dtfr_face_geometry P k S hSmono
  have htan : ∀ p ∈ S, ∀ x ∈ Φ p '' Q₁, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, Φ q '' Q₁) x Q ∧ IsUnitOrientationOf (ξ p) Q := by
    rintro p hp x ⟨t, ht, rfl⟩
    obtain ⟨δ, hδ, hloc⟩ := hflat p hp t ht
    obtain ⟨hrank, -, hep, hen⟩ := he p (hSmono p hp)
    refine ⟨_, Submission.dimred_mbl_dtfrpi_local_plane_tangent P k _ _ _ δ hrank hδ hloc, ?_⟩
    by_cases hβ : 0 < β p
    · rw [show ξ p = e p from ite_eq_left hβ]
      exact hep
    · rw [show ξ p = -e p from ite_eq_right hβ]
      exact hen
  -- step 5: the `IMRep` `R = (C, θ, ξ)`, with `θ = |β_p|` and `ξ = ξ_p` on `F̆_p`
  have hfin : ∀ p ∈ S, μHE[k] (Φ p '' Q₁) ≠ ∞ := fun p hp => by
    rw [(hface p (hSs p hp).1).2.1]
    exact ENNReal.one_ne_top
  obtain ⟨R, hRact, hRmass⟩ := Submission.dimred_mbl_dtfrpi_finite_piece_imrep P k _ univ S
    (fun p => Φ p '' Q₁) (fun p => (β p).natAbs) ξ Φ (fun p hp => (hface p (hSs p hp).1).1)
    (fun _ _ => subset_univ _) hfin hdisj (fun p hp => Int.natAbs_pos.mpr (hSs p hp).2)
    (fun p hp => ⟨1, (hiso p (hSs p hp).1).lipschitzWith⟩) (fun p _ => image_subset_range _ _)
    htan
  have hRact' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, ((β p).natAbs : ℝ) *
        ∫ x in Φ p '' Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] := hRact
  have hRmass' : R.measure univ = ∑ p ∈ S, ((β p).natAbs : ℝ≥0∞) * μHE[k] (Φ p '' Q₁) := hRmass
  -- step 6: `R` represents `T`: the change of variables `Φ_p` gives
  -- `|β_p| ∫_{F̆_p} ⟨ω, ξ_p⟩ dHᵏ = β_p ∫_{Q₁} ⟨ω ∘ Φ_p, e_p⟩`, and the faces with `β_p = 0`
  -- contribute `0`
  have hRep : R.Represents T := by
    intro ω
    rw [hT ω, hRact' ω, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    split_ifs with hβ
    · obtain ⟨-, he₁, -, -⟩ := he p (hmono p hp)
      have hcv : ∫ x in Φ p '' Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] =
          ∫ y in Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) (Φ p y)) :=
        (hface p hp).2.2 fun x => ξ p ((ω : DifferentialForm (Euclid P) k) x)
      show (β p : ℝ) * ∫ y in Q₁, (ω : DifferentialForm (Euclid P) k) (Φ p y)
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) = _
      rw [hcv]
      by_cases hpos : 0 < β p
      · have habs : ((β p).natAbs : ℝ) = β p := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (Int.cast_pos.mpr hpos)]
        rw [show ξ p = e p from ite_eq_left hpos, habs]
        simp only [he₁]
      · have habs : ((β p).natAbs : ℝ) = -β p := by
          rw [Nat.cast_natAbs, Int.cast_abs,
            abs_of_neg (Int.cast_lt_zero.mpr (lt_of_le_of_ne (not_lt.mp hpos) hβ))]
        rw [show ξ p = -e p from ite_eq_right hpos, habs]
        simp only [neg_apply, he₁, integral_neg, neg_mul_neg]
    · rw [not_not.mp hβ, Int.cast_zero, zero_mul]
  -- step 7: by (MR), `M(T) = μ_R(ℝᴾ) = Σ_{p ∈ S} |β_p| Hᵏ(F̆_p) = Σ_{p ∈ s} |β_p|`
  have hmass : T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := by
    have hTR : T.mass = R.measure univ := MR P k univ T R isOpen_univ hRep univ isOpen_univ
    rw [hTR, hRmass', ENNReal.ofReal_sum_of_nonneg fun p _ => abs_nonneg _, hS,
      Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [(hface p hp).2.1, mul_one, ← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs]
    · intro p _ h hβ
      exact h (by simp [hβ])
  -- step 8: `T = 0` if every `β_p` vanishes; otherwise `M(T) ≥ |β_p| ≥ 1` for some `p ∈ s`
  refine ⟨⟨R, hRep⟩, hmass, ?_⟩
  by_cases h0 : ∃ p ∈ s, β p ≠ 0
  · right
    obtain ⟨p, hp, hβ⟩ := h0
    rw [hmass, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) ≤ |(β p : ℝ)| := by exact_mod_cast Int.one_le_abs hβ
      _ ≤ ∑ q ∈ s, |(β q : ℝ)| :=
        Finset.single_le_sum (f := fun q => |(β q : ℝ)|) (fun q _ => abs_nonneg _) hp
  · left
    ext ω
    rw [hT ω, GeometricCurrentOn.zero_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hβ : β p = 0 := by
      by_contra hβ
      exact h0 ⟨p, hp, hβ⟩
    rw [hβ, Int.cast_zero, zero_mul]

/-- **The boundary of an integer lattice chain is an integer lattice chain** (cubical Stokes).
Let `T(ω) = Σ_{p ∈ s} β_p ∫_{Q^{m+1}} ω(Φ_p y)(e_{p.1(0)}, …, e_{p.1(m)}) dy`, where
`Φ_p(y) = p.2 + Σⱼ yⱼ e_{p.1(j)}` and each `p.1` is strictly increasing.  Then
`∂T(γ) = Σ_{q ∈ s'} β'_q ∫_{Q^m} γ(Φ_q y)(e_{q.1(0)}, …, e_{q.1(m-1)}) dy` for integers `β'_q` and
lattice `m`-cube indices `q ∈ s'` that do not depend on `γ`.
Indeed `∂T(γ) = T(dγ)`.  On the cube `p`, `dγ(Φ_p y)(E_p) = tr DG(y)` for the smooth field
`Gᵢ(y) = (-1)ⁱ γ(Φ_p y)(E_p ∘ succAbove i)` (`dimred_mbl_dtfr_face_divergence`), and
`dimred_mbl_dtfrcb_cube_stokes` integrates this to the signed sum of the integrals over the front
and back faces of `p`.  `dimred_mbl_dtfrcb_face_regroup` collects these faces with integer
coefficients. -/
theorem Submission.dimred_mbl_dtfr_chain_boundary : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s', StrictMono p.1) ∧ ∀ γ : TestFormOn (univ : Set (Euclid P)) m, T.boundary γ = ∑ p ∈ s', (β' p : ℝ) * ∫ y in {y : Euclid m | ∀ i, 0 < y i ∧ y i < 1}, (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s β T hs hT
  -- the faces of the cubes of `s`, regrouped with integer coefficients independent of `γ`
  obtain ⟨s', β', hs', hI⟩ := Submission.dimred_mbl_dtfrcb_face_regroup P m s β hs
  refine ⟨s', β', hs', fun γ => ?_⟩
  -- `∂T(γ) = T(dγ) = Σ_p β_p ∫_{Q^{m+1}} dγ(Φ_p y)(E_p) dy`
  rw [GeometricCurrentOn.boundary_apply, hT, ← hI fun q =>
    ∫ y in {y : Euclid m | ∀ i, 0 < y i ∧ y i < 1}, (γ : DifferentialForm (Euclid P) m)
      (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ))
      (fun j => EuclideanSpace.single (q.1 j) (1 : ℝ))]
  refine Finset.sum_congr rfl fun p hp => ?_
  congr 1
  -- Stokes on the cube `p`, with `dγ(Φ_p y)(E_p) = tr DG(y)` for `Gᵢ(y) = (-1)ⁱ γ(Φ_p y)(E'ᵢ)`
  obtain ⟨hG, -, htr⟩ := Submission.dimred_mbl_dtfr_face_divergence P m p.1 p.2
    (γ : DifferentialForm (Euclid P) m)
    (fun y => WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m)
      (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
      (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)))
    (hs p hp) γ.property.1.1 fun _ _ => rfl
  exact Submission.dimred_mbl_dtfrcb_cube_stokes P m p.1 p.2 _ _
    (hG.of_le (by exact_mod_cast le_top)) (fun _ _ => rfl) htr
/-- Finite family in the proof of the deformation theorem (Simon 6.5.1): for compact `K ⊆ ℝᴾ` and
`Λ ∈ ℝ` there are only finitely many currents `T = Σ_{p ∈ s} β_p [[F_p]]` whose unit `k`-faces
`F_p = b + {Σⱼ yⱼ e_{ι(j)} : y ∈ [0,1]ᵏ}` (`p = (ι, b)`, `ι` increasing, `b ∈ ℤᴾ`) all meet `K`
and whose integer coefficients have `Σ_p |β_p| ≤ Λ`.  If `‖x‖ ≤ ρ` on `K`, a face meeting `K`
has `|bᵢ| ≤ ρ + 1`, so these faces form a finite set `S_K`; padding `β` by zero gives a
coefficient vector `S_K → {z ∈ ℤ : |z| ≤ Λ}`, which determines `T` (`GeometricCurrentOn.ext`). -/
theorem Submission.dimred_mbl_dtfr_finite_family : ∀ (P k : ℕ) (K : Set (Euclid P)) (Λ : ℝ), IsCompact K → {T : GeometricCurrentOn (univ : Set (Euclid P)) k | ∃ (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ K) ∧ ∑ p ∈ s, |(β p : ℝ)| ≤ Λ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))}.Finite := by
  intro P k K Λ hK
  -- `{z ∈ ℤ : |z| ≤ r}` is finite
  have hZ : ∀ r : ℝ, {z : ℤ | |(z : ℝ)| ≤ r}.Finite := fun r =>
    (Set.finite_Icc (-⌊r⌋) ⌊r⌋).subset fun z hz => by
      obtain ⟨h₁, h₂⟩ := abs_le.mp (Set.mem_ofPred.mp hz)
      have h₃ : -z ≤ ⌊r⌋ := Int.le_floor.mpr (by push_cast; linarith)
      exact ⟨by linarith, Int.le_floor.mpr h₂⟩
  -- step 1: `K` is bounded, `|x i| ≤ ‖x‖ ≤ ρ` on `K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- step 2: the faces `p = (ι, b)` meeting `K` form a finite set `S_K`, since `|b i| ≤ ρ + 1`
  have hSK : {p : (Fin k → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧ ∃ y : Euclid k,
      (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ K}.Finite := by
    refine (Set.finite_univ.prod (Set.Finite.pi fun _ : Fin P => hZ (ρ + 1))).subset ?_
    rintro p ⟨hι, y, hy, hyK⟩
    refine Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ_pi.mpr fun i => ?_⟩
    -- `Φ_p(y) i - b i` is `y j` if `i = ι j` (`ι` is injective), and `0` if `i ∉ range ι`
    have hv : 0 ≤ (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i ∧
        (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i ≤ 1 := by
      simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply,
        PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : ∃ j₀, p.1 j₀ = i
      · obtain ⟨j₀, rfl⟩ := hi
        rw [Finset.sum_eq_single j₀]
        · rw [ite_eq_left rfl]
          exact hy j₀
        · intro j _ hj
          exact ite_eq_right (hι.injective.ne hj).symm
        · intro h
          exact absurd (Finset.mem_univ j₀) h
      · rw [Finset.sum_eq_zero]
        · exact ⟨le_rfl, zero_le_one⟩
        · intro j _
          exact ite_eq_right fun h => hi ⟨j, h.symm⟩
    have hx := (PiLp.norm_apply_le _ i).trans (hρ _ hyK)
    simp only [PiLp.add_apply, Real.norm_eq_abs, abs_le] at hx
    exact Set.mem_ofPred.mpr (abs_le.mpr ⟨by linarith [hx.1, hv.2], by linarith [hx.2, hv.1]⟩)
  let S := hSK.toFinset
  -- step 3: if `Λ < 0` the set is empty, as `0 ≤ Σ_{p ∈ s} |β p|`
  rcases lt_or_ge Λ 0 with hΛ | hΛ
  · refine Set.finite_empty.subset ?_
    rintro T ⟨s, β, -, -, hs, -⟩
    exact absurd ((Finset.sum_nonneg fun p _ => abs_nonneg _).trans hs) (not_le.mpr hΛ)
  -- otherwise the coefficient vectors `𝔅 = (S_K → {z ∈ ℤ : |z| ≤ Λ})` form a finite set
  have h𝔅 : (Set.pi Set.univ fun _ : S => {z : ℤ | |(z : ℝ)| ≤ Λ}).Finite :=
    Set.Finite.pi fun _ => hZ Λ
  -- the face integral `[[p]](ω)`
  let I : (Fin k → Fin P) × (Fin P → ℤ) → TestFormOn (univ : Set (Euclid P)) k → ℝ :=
    fun p ω => ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k)
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
      (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
  -- step 4: pad the witness `β` of `T` by zero to `β̄_T ∈ 𝔅`; then `T = Σ_{p ∈ S_K} β̄_T(p) [[p]]`
  have step4 : ∀ T ∈ {T : GeometricCurrentOn (univ : Set (Euclid P)) k |
      ∃ (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ),
        (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
            ∈ K) ∧ ∑ p ∈ s, |(β p : ℝ)| ≤ Λ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
          T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1},
            (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
              ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))},
      ∃ c ∈ Set.pi Set.univ (fun _ : S => {z : ℤ | |(z : ℝ)| ≤ Λ}),
        ∀ ω, T ω = ∑ p : S, (c p : ℝ) * I p ω := by
    rintro T ⟨s, β, hmono, hsK, hs, hT⟩
    have hsS : s ⊆ S := fun p hp => hSK.mem_toFinset.mpr ⟨hmono p hp, hsK p hp⟩
    refine ⟨fun p => if (p : (Fin k → Fin P) × (Fin P → ℤ)) ∈ s then β p else 0,
      Set.mem_univ_pi.mpr fun p => ?_, fun ω => ?_⟩
    · -- `|β p| ≤ Σ_{q ∈ s} |β q| ≤ Λ` for `p ∈ s`, and `|0| ≤ Λ`
      show |((if (p : (Fin k → Fin P) × (Fin P → ℤ)) ∈ s then β p else 0 : ℤ) : ℝ)| ≤ Λ
      split_ifs with hp
      · exact (Finset.single_le_sum (fun q _ => abs_nonneg (β q : ℝ)) hp).trans hs
      · simpa using hΛ
    · -- the added terms vanish
      rw [hT ω, Finset.sum_coe_sort S fun p => ((if p ∈ s then β p else 0 : ℤ) : ℝ) * I p ω,
        ← Finset.sum_subset hsS]
      · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left hp]
      · intro p _ hp
        rw [ite_eq_right hp, Int.cast_zero, zero_mul]
  -- step 5: currents are determined by their values, so `T ↦ β̄_T` is injective
  choose! c hc hcT using step4
  exact Set.Finite.of_injOn hc (fun T₁ h₁ T₂ h₂ h => GeometricCurrentOn.ext fun ω => by
    rw [hcT T₁ h₁ ω, hcT T₂ h₂ ω, h]) h𝔅
/-- **Simon Ch. 2, 2.7** (proof, the final limit `σ ↓ 0`): on the cube
`Q_δ = {z : δ < zᵢ < 1 - δ}` (`0 ≤ δ`) the double-integral oscillation
`∫_{Q_δ} ∫_{Q_δ} |u(x) - u(y)| dy dx` passes to `L¹(Q_δ)` limits of continuous functions: if `u` is
integrable on the unit cube, every `v_k` has oscillation `≤ K` and `∫_{Q_δ} |v_k - u| → 0`, then
`u` has oscillation `≤ K`.  Integrating
`|u(x) - u(y)| ≤ |v_k(x) - v_k(y)| + |u(x) - v_k(x)| + |v_k(y) - u(y)|` over `Q_δ × Q_δ` gives
`D(u) ≤ K + 2 |Q_δ| ∫_{Q_δ} |v_k - u|` (Fubini for `v_k`, continuous on the bounded `Q_δ`). -/
theorem Submission.dimred_mbl_dt_cbm_bvp_osc_le_of_l1_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (v : ℕ → Euclid (m + 1) → ℝ) (δ K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → 0 ≤ δ → (∀ k, Continuous (v k)) → (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - v k y| ≤ K) → Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K := by
  intro m u v δ K hu hδ hv hK hlim
  set S : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- 1. `S ⊆ Q₁`, since `0 ≤ δ`
  have hSQ : S ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- 2. `Q₁ ⊆ B̄(0, √(m + 1))`, so `S` has finite volume
  have hSB : S ⊆ closedBall (0 : Euclid (m + 1)) √(m + 1 : ℕ) := by
    intro z hz
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖z.ofLp i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := Finset.sum_le_sum fun i _ => by
          have h0 := (hSQ hz i).1
          have h1 := (hSQ hz i).2
          rw [Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = (m + 1 : ℕ) := by simp
  have hS_fin : volume S < ∞ := (measure_mono hSB).trans_lt measure_closedBall_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hS_fin.ne
  -- 3. `u, v k ∈ L¹(S)`
  have huS : Integrable u (volume.restrict S) := hu.mono_set hSQ
  have hvS : ∀ k, Integrable (v k) (volume.restrict S) := fun k =>
    ((hv k).continuousOn.integrableOn_compact (isCompact_closedBall _ _)).mono_set hSB
  -- 4. Fubini: `d_k x = ∫_S |v k x - v k y| dy` is integrable on `S`
  have hd : ∀ k, Integrable (fun x => ∫ y in S, |v k x - v k y|) (volume.restrict S) := fun k =>
    (((hvS k).comp_fst (volume.restrict S)).sub
      ((hvS k).comp_snd (volume.restrict S))).abs.integral_prod_left
  -- 5–6. the inner integral
  have hinner : ∀ k x, ∫ y in S, |u x - u y| ≤ (∫ y in S, |v k x - v k y|) +
      (volume.restrict S).real univ * |u x - v k x| + ∫ y in S, |v k y - u y| := by
    intro k x
    have h1 : Integrable (fun y => |v k x - v k y|) (volume.restrict S) :=
      ((integrable_const (v k x)).sub (hvS k)).abs
    have h2 : Integrable (fun _ : Euclid (m + 1) => |u x - v k x|) (volume.restrict S) :=
      integrable_const _
    have h3 : Integrable (fun y => |v k y - u y|) (volume.restrict S) := ((hvS k).sub huS).abs
    have h12 : Integrable (fun y => |v k x - v k y| + |u x - v k x|) (volume.restrict S) :=
      h1.add h2
    calc ∫ y in S, |u x - u y|
        ≤ ∫ y in S, (|v k x - v k y| + |u x - v k x| + |v k y - u y|) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
            (h12.add h3) (Eventually.of_forall fun y => ?_)
          calc |u x - u y| = |(v k x - v k y) + (u x - v k x) + (v k y - u y)| := by
                congr 1; ring
            _ ≤ _ := abs_add_three _ _ _
      _ = _ := by
          rw [integral_add h12 h3, integral_add h1 h2, integral_const, smul_eq_mul]
  -- 7. the outer integral: `D(u) ≤ K + 2 a ε_k`
  have hbound : ∀ k, ∫ x in S, ∫ y in S, |u x - u y| ≤
      K + (volume.restrict S).real univ * (∫ x in S, |v k x - u x|) +
        (volume.restrict S).real univ * ∫ x in S, |v k x - u x| := by
    intro k
    have h2 : Integrable (fun x => (volume.restrict S).real univ * |u x - v k x|)
        (volume.restrict S) := ((huS.sub (hvS k)).abs).const_mul _
    have h3 : Integrable (fun _ : Euclid (m + 1) => ∫ y in S, |v k y - u y|) (volume.restrict S) :=
      integrable_const _
    have h12 : Integrable (fun x => (∫ y in S, |v k x - v k y|) +
        (volume.restrict S).real univ * |u x - v k x|) (volume.restrict S) := (hd k).add h2
    have hsymm : ∫ x in S, |u x - v k x| = ∫ x in S, |v k x - u x| := by
      simp_rw [abs_sub_comm (u _)]
    calc ∫ x in S, ∫ y in S, |u x - u y|
        ≤ ∫ x in S, ((∫ y in S, |v k x - v k y|) + (volume.restrict S).real univ * |u x - v k x| +
            ∫ y in S, |v k y - u y|) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _)
            (h12.add h3) (Eventually.of_forall fun x => hinner k x)
      _ = (∫ x in S, ∫ y in S, |v k x - v k y|) +
            (volume.restrict S).real univ * (∫ x in S, |u x - v k x|) +
            (volume.restrict S).real univ * ∫ y in S, |v k y - u y| := by
          rw [integral_add h12 h3, integral_add (hd k) h2, integral_const_mul,
            integral_const, smul_eq_mul]
      _ ≤ _ := by
          rw [hsymm]
          linarith [hK k]
  -- 8. let `k → ∞`
  have hlim' := (tendsto_const_nhds (x := K)).add (hlim.const_mul ((volume.restrict S).real univ))
    |>.add (hlim.const_mul ((volume.restrict S).real univ))
  rw [mul_zero, add_zero, add_zero] at hlim'
  exact ge_of_tendsto' hlim' hbound

/-- **Simon 2.7** (BV Poincaré inequality, as used for (32) in the proof of 6.5.1): the passage
`δ ↓ 0` from the inner cubes `Q_δ = {z : δ < zᵢ < 1 - δ}` to the open unit cube
`Q₁ = {y : 0 < yᵢ < 1}` of `ℝ^{m+1}`.  If `u` is integrable on `Q₁` and
`∫_{Q_δ} ∫_{Q_δ} |u(x) - u(y)| dy dx ≤ K` for all `0 < δ < 1/2`, then the same bound holds on
`Q₁`: for `δⱼ = 1/(j + 3) ↓ 0` the products `Q_{δⱼ} × Q_{δⱼ}` increase to `Q₁ × Q₁`, on which
`|u(x) - u(y)|` is integrable (`vol(Q₁) = 1`), so the set integrals converge, and Fubini
identifies them with the double integrals. -/
theorem Submission.dimred_mbl_dt_cbm_bvp_osc_le_of_inner_cubes : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K) → ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| ≤ K := by
  intro m u K hu hK
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  -- `δⱼ = 1/(j + 3)` lies in `(0, 1/2)` and decreases to `0`
  set δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 3) with hδ
  have hδpos : ∀ j, 0 < δ j := fun j => by positivity
  have hδlt : ∀ j, δ j < 1 / 2 := fun j =>
    one_div_lt_one_div_of_lt two_pos (by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
  have hδanti : Antitone δ := fun i j hij =>
    one_div_le_one_div_of_le (by positivity)
      (by have := (Nat.cast_le (α := ℝ)).2 hij; linarith)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have h := (tendsto_atTop_add_const_right atTop (3 : ℝ)
      tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    refine h.congr fun j => ?_
    simp [hδ, one_div]
  -- the inner cubes `Qⱼ = Q_{δⱼ}` are measurable, increasing, and exhaust `Q₁`
  set Q : ℕ → Set (Euclid (m + 1)) := fun j => {z | ∀ i, δ j < z i ∧ z i < 1 - δ j}
    with hQ
  have hcoord : ∀ i : Fin (m + 1), Measurable fun z : Euclid (m + 1) => z i := fun _ => by
    fun_prop
  have hQmeas : ∀ j, MeasurableSet (Q j) := fun j => by
    have : Q j = ⋂ i, ({z : Euclid (m + 1) | δ j < z i} ∩ {z | z i < 1 - δ j}) := by
      ext z
      simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i => (measurableSet_lt measurable_const (hcoord i)).inter
      (measurableSet_lt (hcoord i) measurable_const)
  have hQmono : Monotone Q := fun j j' hjj' z hz i =>
    ⟨(hδanti hjj').trans_lt (hz i).1, (hz i).2.trans_le (by linarith [hδanti hjj'])⟩
  have hQsub : ∀ j, Q j ⊆ Q₁ := fun j z hz i =>
    ⟨(hδpos j).trans (hz i).1, (hz i).2.trans (by linarith [hδpos j])⟩
  have hQunion : ⋃ j, Q j = Q₁ := by
    refine Subset.antisymm (iUnion_subset hQsub) fun z hz => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < z i ∧ z i < 1 - δ j := by
      rw [eventually_all]
      intro i
      have h1 : ∀ᶠ j in atTop, δ j < z i := hδlim.eventually (gt_mem_nhds (hz i).1)
      have h2 : ∀ᶠ j in atTop, δ j < 1 - z i :=
        hδlim.eventually (gt_mem_nhds (by linarith [(hz i).2]))
      filter_upwards [h1, h2] with j hj1 hj2
      exact ⟨hj1, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact mem_iUnion.2 ⟨j, hj⟩
  -- `vol(Q₁) = 1`, so `|u(x) - u(y)|` is integrable on `Q₁ × Q₁`
  have : IsFiniteMeasure (volume.restrict Q₁) := by
    refine isFiniteMeasure_restrict.2 ?_
    rw [hQ₁, Submission.cmcdtfrfg_cube_volume (m + 1)]
    exact ENNReal.one_ne_top
  have hF : IntegrableOn (fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|)
      (Q₁ ×ˢ Q₁) (volume.prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ((Integrable.comp_fst hu _).sub (Integrable.comp_snd hu _)).abs
  -- the products `Qⱼ × Qⱼ` increase to `Q₁ × Q₁`; pass to the limit and apply Fubini
  have hunion : ⋃ j, Q j ×ˢ Q j = Q₁ ×ˢ Q₁ := by
    rw [iUnion_prod_of_monotone hQmono hQmono, hQunion]
  have hlim : Tendsto (fun j => ∫ x in Q j, ∫ y in Q j, |u x - u y|) atTop
      (𝓝 (∫ x in Q₁, ∫ y in Q₁, |u x - u y|)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume.prod volume)
      (f := fun p : Euclid (m + 1) × Euclid (m + 1) => |u p.1 - u p.2|)
      (fun j => (hQmeas j).prod (hQmeas j)) (fun j j' h => prod_mono (hQmono h) (hQmono h))
      (by rw [hunion]; exact hF)
    rw [hunion, setIntegral_prod _ hF] at h
    refine h.congr fun j => ?_
    exact setIntegral_prod _ (hF.mono_set (prod_mono (hQsub j) (hQsub j)))
  exact le_of_tendsto' hlim fun j => hK (δ j) (hδpos j) (hδlt j)
/-- **Simon Ch. 2, 2.7** (BV Poincaré inequality, applied to the unit faces of 6.5.1 at (32)):
the mean deviation over a set `S` with `vol(S) = 1` is at most the double-integral oscillation.
As `vol⌞S` is a probability measure, `u x - ∫_S u = ∫_S (u x - u y) dy`, so
`|u x - ∫_S u| ≤ ∫_S |u x - u y| dy`; the right side is integrable in `x` by Fubini, and
integrating over `S` gives the claim. -/
theorem Submission.dimred_mbl_dt_cbm_bvp_mean_dev_le_osc : ∀ (m : ℕ) (S : Set (Euclid (m + 1))) (u : Euclid (m + 1) → ℝ), volume S = 1 → IntegrableOn u S → ∫ x in S, |u x - ∫ y in S, u y| ≤ ∫ x in S, ∫ y in S, |u x - u y| := by
  intro m S u hS hu
  -- `vol⌞S` is a probability measure
  have : IsProbabilityMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ, hS]⟩
  -- Fubini: `|u x - u y|` is integrable on `S × S`, so `x ↦ ∫_S |u x - u y| dy` is integrable
  have hosc : Integrable (fun x => ∫ y in S, |u x - u y|) (volume.restrict S) :=
    ((hu.integrable.comp_fst (volume.restrict S)).sub
      (hu.integrable.comp_snd (volume.restrict S))).abs.integral_prod_left
  -- pointwise bound: `u x - ∫_S u = ∫_S (u x - u y) dy` since `vol(S) = 1`
  have hpt : ∀ x, |u x - ∫ y in S, u y| ≤ ∫ y in S, |u x - u y| := by
    intro x
    have hmean : ∫ y in S, (u x - u y) = u x - ∫ y in S, u y := by
      rw [integral_sub (integrable_const (u x)) hu.integrable, integral_const, probReal_univ,
        one_smul]
    rw [← hmean]
    exact abs_integral_le_integral_abs
  exact integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hosc
    (Eventually.of_forall hpt)
/-- **Segment estimate.**  For `v ∈ C¹(ℝⁿ)` and `x, y ∈ ℝⁿ`,
`|v(x) − v(y)| ≤ ‖x − y‖ ∫₀¹ ‖Dv((1 − t)y + tx)‖ dt`.  Along `p(t) = (1 − t)y + tx` the chain
rule gives `(v ∘ p)'(t) = Dv(p(t))(x − y)`, which is continuous in `t`; the fundamental theorem
of calculus writes `v(x) − v(y)` as its integral over `[0, 1]`, and the operator-norm bound
`|Dv(p(t))(x − y)| ≤ ‖x − y‖ ‖Dv(p(t))‖` with monotonicity of the integral finishes the proof. -/
theorem Submission.dimred_mbl_dt_cbm_sp_segment_bound : ∀ (n : ℕ) (v : Euclid n → ℝ) (x y : Euclid n), ContDiff ℝ 1 v → |v x - v y| ≤ ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ := by
  intro n v x y hv
  have hdiff : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- the segment `p(t) = (1 - t) • y + t • x`, with `p 0 = y`, `p 1 = x` and `p' = x - y`
  obtain ⟨p, hp⟩ : ∃ p : ℝ → Euclid n, p = fun t => (1 - t) • y + t • x := ⟨_, rfl⟩
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hpd : ∀ t, HasDerivAt p (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) • y) ((-1 : ℝ) • y) t :=
      ((hasDerivAt_id t).const_sub 1).smul_const y
    have h2 : HasDerivAt (fun t : ℝ => t • x) ((1 : ℝ) • x) t := (hasDerivAt_id t).smul_const x
    have h3 := h1.add h2
    rw [hp]
    convert h3 using 1
    simp only [neg_smul, one_smul]
    abel
  -- chain rule: `(v ∘ p)'(t) = Dv(p(t))(x - y)`, continuous in `t`
  have hγ : ∀ t, HasDerivAt (fun t => v (p t)) (fderiv ℝ v (p t) (x - y)) t := fun t =>
    (hdiff (p t)).hasFDerivAt.comp_hasDerivAt t (hpd t)
  have hγc : Continuous fun t => fderiv ℝ v (p t) (x - y) :=
    (hcont.comp hpc).clm_apply continuous_const
  -- fundamental theorem of calculus
  have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y) = v x - v y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ t)
      (hγc.intervalIntegrable 0 1)]
    simp [hp]
  have hpt : ∀ t, (1 - t) • y + t • x = p t := fun t => by rw [hp]
  simp only [hpt]
  rw [← hftc, ← Real.norm_eq_abs]
  calc ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t) (x - y)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, ‖x - y‖ * ‖fderiv ℝ v (p t)‖ := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact hγc.norm.intervalIntegrable 0 1
        · exact (continuous_const.mul (hcont.comp hpc).norm).intervalIntegrable 0 1
        · intro t _
          rw [mul_comm]
          exact (fderiv ℝ v (p t)).le_opNorm (x - y)
    _ = ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t)‖ :=
        intervalIntegral.integral_const_mul _ _
/-- **Slice bound on a convex set.**  For convex measurable `Q ⊆ ℝⁿ`, measurable `g ≥ 0` and
`t ∈ [0, 1]`, `∫_Q ∫_Q g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(Q) ∫_Q g`.  If `s ≥ 1/2` and `c + sQ ⊆ Q`,
the Haar scaling `v ↦ sv` and translation invariance give
`∫_Q g(c + sv) dv ≤ ∫ (1_Q g)(c + sv) dv = s⁻ⁿ ∫_Q g ≤ 2ⁿ ∫_Q g`.  By convexity of `Q`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `Q` gives the claim. -/
theorem Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound : ∀ (n : ℕ) (Q : Set (Euclid n)) (g : Euclid n → ℝ≥0∞), Convex ℝ Q → MeasurableSet Q → Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
  intro n Q g hQc hQm hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • Q ⊆ Q`, then `∫_Q g(c + s v) dv ≤ 2ⁿ ∫_Q g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ Q, c + s • v ∈ Q) →
      ∫⁻ v in Q, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in Q, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = Q.indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator hQm
    -- change of variables `v ↦ s • v` (Haar scaling) followed by translation invariance
    have hcv : ∫⁻ v, F (c + s • v) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
      have h1 : ∫⁻ w, F (c + w) ∂(Measure.map (fun v : Euclid n => s • v) volume)
          = ∫⁻ v, F (c + s • v) :=
        lintegral_map (hF.comp (measurable_const_add c)) (measurable_const_smul s)
      rw [← h1, Measure.map_addHaar_smul volume hs0.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self F c, finrank_euclideanSpace_fin, smul_eq_mul]
    have hs2 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 two_pos]
      linarith
    calc ∫⁻ v in Q, g (c + s • v)
        = ∫⁻ v in Q, F (c + s • v) := by
          refine setLIntegral_congr_fun hQm fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in Q, g z := by
          rw [hcv, hFdef, lintegral_indicator hQm]
      _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
          gcongr
          calc ENNReal.ofReal |(s ^ n)⁻¹| = ENNReal.ofReal s⁻¹ ^ n := by
                rw [abs_of_pos (by positivity), ← inv_pow, ENNReal.ofReal_pow (by positivity)]
            _ ≤ ENNReal.ofReal 2 ^ n := by gcongr
            _ = 2 ^ n := by rw [ENNReal.ofReal_ofNat]
  -- the integrand is jointly measurable
  have hmeas : Measurable (fun p : Euclid n × Euclid n => g ((1 - t) • p.2 + t • p.1)) :=
    hg.comp (by fun_prop)
  rcases le_total (1 / 2 : ℝ) t with h | h
  · -- `t ≥ 1/2`: Tonelli, then change variables in `x` with `c = (1 - t) • y`, `s = t`
    rw [lintegral_lintegral_swap (f := fun x y => g ((1 - t) • y + t • x)) hmeas.aemeasurable]
    calc ∫⁻ y in Q, ∫⁻ x in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact hQc hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun x hx => ?_
          calc ∫⁻ y in Q, g ((1 - t) • y + t • x)
              = ∫⁻ y in Q, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact hQc hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality on a convex set, double-integral form** (the "usual Poincaré inequality
for smooth functions" of Gilbarg–Trudinger, Lemma 7.16, invoked in Simon's proof of Ch. 2, 2.7).
For `v ∈ C¹(ℝⁿ)` and convex measurable `Q ⊆ ℝⁿ` with `‖x - y‖ ≤ d` on `Q`,
`∫_Q ∫_Q |v(x) - v(y)| ≤ 2ⁿ d Lⁿ(Q) ∫_Q ‖Dv‖`.  For `x, y ∈ Q`,
`dimred_mbl_dt_cbm_sp_segment_bound` gives `|v(x) - v(y)| ≤ d ∫₀¹ ‖Dv((1 - t)y + tx)‖ dt`.
Integrate over `Q × Q` and move the `t`-integral outside (Tonelli); then
`dimred_mbl_dt_cbm_sp_convex_slice_bound` bounds each slice by `2ⁿ Lⁿ(Q) ∫_Q ‖Dv‖`.  As `Q` is
bounded and `‖Dv‖` is continuous, the bound is finite, so it passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.dimred_mbl_dt_cbm_sp_convex_poincare : ∀ (n : ℕ) (Q : Set (Euclid n)) (v : Euclid n → ℝ) (d : ℝ), Convex ℝ Q → MeasurableSet Q → 0 ≤ d → (∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ d) → ContDiff ℝ 1 v → ∫ x in Q, ∫ y in Q, |v x - v y| ≤ 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
  intro n Q v d hQc hQm hd hdiam hv
  have hseg := Submission.dimred_mbl_dt_cbm_sp_segment_bound n v
  have hslice := Submission.dimred_mbl_dt_cbm_sp_convex_slice_bound n Q
  have hcont : Continuous v := hv.continuous
  -- Step 1: `F = ‖Dv‖` is continuous and `Q` is bounded, so `Lⁿ(Q) < ∞`, `F ≤ C` on `Q`, and
  -- `g = ofReal ∘ F` has finite integral over `Q`
  have hFc : Continuous fun z => ‖fderiv ℝ v z‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hQb : Bornology.IsBounded Q :=
    Metric.isBounded_iff.2 ⟨d, fun x hx y hy => by rw [dist_eq_norm]; exact hdiam x hx y hy⟩
  have hQfin : volume Q < ∞ := hQb.measure_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ closure Q, ‖‖fderiv ℝ v z‖‖ ≤ C :=
    hQb.isCompact_closure.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal ‖fderiv ℝ v z‖ :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal ‖fderiv ℝ v z‖ := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hFc.measurable.ennreal_ofReal
  have hJ : ∫⁻ z in Q, g z ≠ ∞ := by
    have h1 : ∫⁻ z in Q, g z ≤ ∫⁻ _ in Q, ENNReal.ofReal C :=
      setLIntegral_mono' hQm fun z hz => by
        rw [hgx]
        exact ENNReal.ofReal_le_ofReal (by simpa using hC z (subset_closure hz))
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin)).ne
  -- Step 2: for `x, y ∈ Q`, `|v x - v y| ≤ d ∫_(0,1] ‖Dv((1 - t) y + t x)‖ dt`
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    intro x hx y hy
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => norm_nonneg _
    have h1 : |v x - v y| ≤ d * G :=
      (hseg x y hv).trans (mul_le_mul_of_nonneg_right (hdiam x hx y hy) hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative continuous function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ v ((1 - t) • y + t • x)‖)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hFc.comp h).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => norm_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal |v x - v y| ≤ ENNReal.ofReal (d * G) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal d * ENNReal.ofReal G := ENNReal.ofReal_mul hd
      _ ≤ _ := by gcongr
  -- Step 3: move the `t`-integral outside (Tonelli, twice)
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in Q, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in Q, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in Q, g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  -- Step 4: integrate step 2 over `Q × Q`; the convex slice bound controls each `t`-slice
  have hI : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y|
        ≤ ∫⁻ x in Q, ∫⁻ y in Q,
            ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => hpt x hx y hy
      _ = ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q,
            g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [hswap]
      _ ≤ ENNReal.ofReal d * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          gcongr ENNReal.ofReal d * ?_
          exact setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hQc hQm hg t (Ioc_subset_Icc_self ht)
      _ = ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  -- Step 5: back to Bochner integrals; the bound is finite by step 1
  have hK : Measurable fun x : Euclid n => ∫⁻ y in Q, ENNReal.ofReal |v x - v y| := by
    have h : Continuous fun p : Euclid n × Euclid n => |v p.1 - v p.2| := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal |v p.1 - v p.2|)
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in Q, |v x - v y| =
      (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
      (by fun_prop : Continuous fun y => |v x - v y|).aestronglyMeasurable
  have hrhs : ∫ z in Q, ‖fderiv ℝ v z‖ = (∫⁻ z in Q, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => norm_nonneg _)
      hFc.aestronglyMeasurable]
    simp only [hgx]
  have hfin : ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hQfin.ne) hJ)
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      = ∫ x in Q, (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := by simp only [hinner]
    _ = (∫⁻ x in Q, ENNReal.ofReal (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z)).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hd]
        ring
/-- **Geometry of the cube `Q_δ`.**  For `δ ≥ 0`, the open cube
`Q_δ = {z ∈ ℝⁿ : δ < zᵢ < 1 − δ for all i}` is convex and measurable, `‖x − y‖ ≤ √n` for
`x, y ∈ Q_δ`, and `Lⁿ(Q_δ) ≤ 1`.  Convexity is coordinatewise; `Q_δ` is a finite intersection of
the measurable sets `{δ < zᵢ}` and `{zᵢ < 1 − δ}`; `|xᵢ − yᵢ| < 1 − 2δ ≤ 1` gives
`‖x − y‖ = √(∑ᵢ (xᵢ − yᵢ)²) ≤ √n`; and `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))`, where the coordinate map
`ofLp` is measure preserving and the box `∏ᵢ (0, 1)` has volume `1`. -/
theorem Submission.dimred_mbl_dt_cbm_sp_cube_geometry : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → Convex ℝ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ MeasurableSet {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ (∀ x ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ∀ y ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖x - y‖ ≤ Real.sqrt n) ∧ volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ≤ 1 := by
  intro n δ hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- convexity: `a (xᵢ − δ) + b (yᵢ − δ) > 0` and `a (1 − δ − xᵢ) + b (1 − δ − yᵢ) > 0`
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab i => ?_
    have hxi := hx i
    have hyi := hy i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    constructor
    · nlinarith [mul_pos ha (sub_pos.2 hxi.1), mul_pos hb (sub_pos.2 hyi.1)]
    · nlinarith [mul_pos ha (sub_pos.2 hxi.2), mul_pos hb (sub_pos.2 hyi.2)]
  · -- measurability: a finite intersection of sets defined by continuous coordinates
    have hc : ∀ i : Fin n, Continuous fun z : Euclid n => z i := fun i => by fun_prop
    have : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} =
        ⋂ i, ({z : Euclid n | δ < z i} ∩ {z : Euclid n | z i < 1 - δ}) := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i).measurable).inter
        (measurableSet_lt (hc i).measurable measurable_const)
  · -- diameter: `(xᵢ − yᵢ)² ≤ 1` for each coordinate
    intro x hx y hy
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hxi := hx i
          have hyi := hy i
          simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = n := by simp
  · -- volume: `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))` and `ofLp` is measure preserving
    have hsub : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
        WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) := by
      intro z hz
      simp only [mem_preimage, mem_univ_pi, mem_Ioo]
      intro i
      exact ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩
    calc volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}
        ≤ volume (WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) : Set (Euclid n)) :=
          measure_mono hsub
      _ = volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) :=
          (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
            (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet
      _ = 1 := by rw [Real.volume_pi_Ioo]; simp

/-- **Smooth Poincaré inequality on the cube `Q_δ`** (the "usual Poincaré inequality for smooth
functions" of Simon Ch. 2, 2.7).  For `n = m + 1`, `δ ≥ 0`, `Q_δ = {z : δ < zᵢ < 1 − δ ∀ i}` and
`v ∈ C¹(ℝⁿ)`, `∫_{Q_δ} ∫_{Q_δ} |v(x) − v(y)| dy dx ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`.  The cube `Q_δ` is convex
and measurable, has diameter `≤ √n` and `Lⁿ(Q_δ) ≤ 1`, so the convex Poincaré bound with `d = √n`
gives `∫∫ |v(x) − v(y)| ≤ 2ⁿ √n Lⁿ(Q_δ) ∫_{Q_δ} ‖Dv‖ ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`. -/
theorem Submission.dimred_mbl_dt_cbm_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x - v y| ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ
  -- `Q_δ` is convex and measurable, with diameter `≤ √n` and volume `≤ 1` (`n = m + 1`).
  obtain ⟨hconv, hmeas, hdiam, hvol⟩ := Submission.dimred_mbl_dt_cbm_sp_cube_geometry (m + 1) δ hδ
  -- Convex Poincaré bound with `d = √n`: `∫∫ |v x − v y| ≤ 2ⁿ √n Lⁿ(Q_δ) ∫ ‖Dv‖`.
  have hP := Submission.dimred_mbl_dt_cbm_sp_convex_poincare (m + 1) _ v
    (Real.sqrt ((m + 1 : ℕ) : ℝ)) hconv hmeas (Real.sqrt_nonneg _) hdiam hv
  have hvol' : (volume {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  calc _ ≤ _ := hP
    _ ≤ 2 ^ (m + 1) * Real.sqrt ((m + 1 : ℕ) : ℝ) * 1 *
          ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖ := by
        gcongr
    _ = _ := by push_cast; ring
/-- **Simon 6.5.1** (proof, (31): the integer median `β`): if `μ` is a probability measure and `u`
is `μ`-a.e. measurable and integer-valued, then some `β ∈ ℤ` has `μ{u ≥ β} ≥ 1/2` and
`μ{u ≤ β} ≥ 1/2`.  Take the least integer `β` with `F(β) ≥ 1/2`, `F(t) = μ{u ≤ t}`; it exists
because `F(n) → 1` and `F(-n) → 0` (continuity of `μ` from below and above).  Then
`F(β - 1) < 1/2`, and `{u ≥ β} = {u ≤ β - 1}ᶜ` since `u` is integer-valued. -/
theorem Submission.dimred_mbl_dt_cbm_im_integer_median_exists : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ), IsProbabilityMeasure μ → AEMeasurable u μ → (∀ x, ∃ z : ℤ, u x = z) → ∃ β : ℤ, 1 / 2 ≤ μ.real {x | (β : ℝ) ≤ u x} ∧ 1 / 2 ≤ μ.real {x | u x ≤ (β : ℝ)} := by
  intro X _ μ u _ hu hint
  -- each `{u ≤ t}` is null-measurable
  have hnm : ∀ t : ℝ, NullMeasurableSet {x | u x ≤ t} μ := fun t =>
    hu.nullMeasurableSet_preimage measurableSet_Iic
  -- `F(t) = μ.real {u ≤ t}` is nondecreasing
  have hmono : ∀ s t : ℝ, s ≤ t → μ.real {x | u x ≤ s} ≤ μ.real {x | u x ≤ t} := fun s t hst =>
    measureReal_mono fun x hx => le_trans (show u x ≤ s from hx) hst
  -- upper tail: `F(n) → 1`, so `F(n₁) > 1/2` for some `n₁ : ℕ`
  obtain ⟨n₁, hn₁⟩ : ∃ n₁ : ℕ, 1 / 2 < μ.real {x | u x ≤ (n₁ : ℝ)} := by
    have hA : Monotone fun n : ℕ => {x | u x ≤ (n : ℝ)} := fun a b hab x hx =>
      le_trans (show u x ≤ (a : ℝ) from hx) (Nat.cast_le.mpr hab)
    have hU : (⋃ n : ℕ, {x | u x ≤ (n : ℝ)}) = univ :=
      eq_univ_of_forall fun x => mem_iUnion.mpr (exists_nat_ge (u x))
    have h1 := tendsto_measure_iUnion_atTop (μ := μ) hA
    rw [hU, measure_univ] at h1
    have h2 : Tendsto (fun n : ℕ => μ.real {x | u x ≤ (n : ℝ)}) atTop (𝓝 1) := by
      simpa [Function.comp_def, Measure.real] using (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
    exact (h2.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  -- lower tail: `F(-n) → 0`, so `F(-n₀) < 1/2` for some `n₀ : ℕ`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, μ.real {x | u x ≤ -(n₀ : ℝ)} < 1 / 2 := by
    have hB : Antitone fun n : ℕ => {x | u x ≤ -(n : ℝ)} := fun a b hab x hx =>
      le_trans (show u x ≤ -(b : ℝ) from hx) (neg_le_neg (Nat.cast_le.mpr hab))
    have hI : (⋂ n : ℕ, {x | u x ≤ -(n : ℝ)}) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (-u x)
      have : u x ≤ -(n : ℝ) := mem_iInter.mp hx n
      linarith
    have h1 := tendsto_measure_iInter_atTop (μ := μ) (fun n : ℕ => hnm (-(n : ℝ))) hB
      ⟨0, measure_ne_top μ _⟩
    rw [hI, measure_empty] at h1
    have h2 : Tendsto (fun n : ℕ => μ.real {x | u x ≤ -(n : ℝ)}) atTop (𝓝 0) := by
      simpa [Function.comp_def, Measure.real] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    exact (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  -- `β` is the least integer with `F(β) ≥ 1/2`; the set is nonempty and bounded below by `-n₀`
  obtain ⟨β, hβ, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z : ℤ => 1 / 2 ≤ μ.real {x | u x ≤ (z : ℝ)})
    ⟨-(n₀ : ℤ), fun z hz => by
      by_contra hlt
      have hz' : (z : ℝ) ≤ -(n₀ : ℝ) := by exact_mod_cast (not_le.mp hlt).le
      linarith [hmono _ _ hz']⟩
    ⟨n₁, by simpa using hn₁.le⟩
  refine ⟨β, ?_, hβ⟩
  -- minimality: `F(β - 1) < 1/2`
  have hβ1 : μ.real {x | u x ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 :=
    lt_of_not_ge fun h => by linarith [hmin (β - 1) h]
  -- `u` is integer-valued, so `{β ≤ u} = {u ≤ β - 1}ᶜ`
  have hset : {x | (β : ℝ) ≤ u x} = {x | u x ≤ ((β - 1 : ℤ) : ℝ)}ᶜ := by
    ext x
    obtain ⟨z, hz⟩ := hint x
    simp only [mem_ofPred_eq, mem_compl_iff, hz, Int.cast_le, not_le]
    omega
  rw [hset, probReal_compl_eq_one_sub₀ (hnm _)]
  linarith
/-- **Simon 6.5.1** (proof, (31)–(32): the median `β` minimizes the `L¹` deviation, which replaces
the median hypothesis 2.7(‡) of Ch. 2): if `μ` is a probability measure, `u` is `μ`-integrable
and `β` is a median of `u` (`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`), then
`∫ |u - β| dμ ≤ ∫ |u - c| dμ` for every `c`.  If `β ≤ c`, then
`|u - c| - |u - β| ≥ (c - β)(2 · 1_{u ≤ β} - 1)` pointwise (equality on `{u ≤ β}`, the triangle
inequality off it), and integrating gives `∫ |u - c| - ∫ |u - β| ≥ (c - β)(2μ{u ≤ β} - 1) ≥ 0`.
The case `c < β` is symmetric, with `{β ≤ u}` and `β - c`. -/
theorem Submission.dimred_mbl_dt_cbm_im_median_minimizes : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → ∀ c : ℝ, ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
  intro X _ μ u β hμ hu hge hle c
  -- every `|u - a|` is integrable
  have habs : ∀ a : ℝ, Integrable (fun x => |u x - a|) μ := fun a =>
    (hu.sub (integrable_const a)).abs
  -- key lemma: integrate `d (2 · 1_s - 1) ≤ |u - c| - |u - β|`, using `∫ 1_s = μ(s)`, `∫ 1 = 1`
  have key : ∀ (s : Set X) (d : ℝ), NullMeasurableSet s μ → 1 / 2 ≤ μ.real s → 0 ≤ d →
      (∀ x, d * (2 * s.indicator (fun _ => (1 : ℝ)) x - 1) ≤ |u x - c| - |u x - β|) →
      ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
    intro s d hs hs2 hd hpt
    have hind : Integrable (s.indicator fun _ => (1 : ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator₀ hs
    have hI : ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ = μ.real s := by
      rw [integral_indicator₀ hs, setIntegral_const, smul_eq_mul, mul_one]
    have hL : ∫ x, d * (2 * s.indicator (fun _ => (1 : ℝ)) x - 1) ∂μ = d * (2 * μ.real s - 1) := by
      rw [integral_const_mul, integral_sub (hind.const_mul 2) (integrable_const 1),
        integral_const_mul, hI, integral_const, probReal_univ, smul_eq_mul, mul_one]
    have hR : ∫ x, (|u x - c| - |u x - β|) ∂μ = ∫ x, |u x - c| ∂μ - ∫ x, |u x - β| ∂μ :=
      integral_sub (habs c) (habs β)
    have hmono : ∫ x, d * (2 * s.indicator (fun _ => (1 : ℝ)) x - 1) ∂μ ≤
        ∫ x, (|u x - c| - |u x - β|) ∂μ :=
      integral_mono (((hind.const_mul 2).sub (integrable_const 1)).const_mul d)
        ((habs c).sub (habs β)) hpt
    have hnn : 0 ≤ d * (2 * μ.real s - 1) := mul_nonneg hd (by linarith)
    linarith
  -- `u` is a.e.-measurable, so `{u ≤ β}` and `{β ≤ u}` are null-measurable
  have hmeas : AEMeasurable u μ := hu.aemeasurable
  rcases le_or_gt β c with hc | hc
  · -- `β ≤ c`: `s = {u ≤ β}`, `d = c - β`
    refine key {x | u x ≤ β} (c - β) (hmeas.nullMeasurableSet_preimage measurableSet_Iic) hle
      (sub_nonneg.mpr hc) fun x => ?_
    by_cases hx : u x ≤ β
    · rw [Set.indicator_of_mem (show x ∈ {x | u x ≤ β} from hx),
        abs_of_nonpos (by linarith : u x - c ≤ 0), abs_of_nonpos (by linarith : u x - β ≤ 0)]
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | u x ≤ β} from hx)]
      have h1 := abs_sub_le (u x) c β
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - β)] at h1
      linarith
  · -- `c < β`: `s = {β ≤ u}`, `d = β - c`
    refine key {x | β ≤ u x} (β - c) (hmeas.nullMeasurableSet_preimage measurableSet_Ici) hge
      (sub_nonneg.mpr hc.le) fun x => ?_
    by_cases hx : β ≤ u x
    · rw [Set.indicator_of_mem (show x ∈ {x | β ≤ u x} from hx),
        abs_of_nonneg (by linarith : 0 ≤ u x - c), abs_of_nonneg (by linarith : 0 ≤ u x - β)]
      linarith
    · rw [Set.indicator_of_notMem (show x ∉ {x | β ≤ u x} from hx)]
      have h1 := abs_sub_le (u x) c β
      rw [abs_of_nonpos (by linarith : c - β ≤ 0)] at h1
      linarith
/-- **Simon 6.5.1** (proof, (35): `|β_F| ≤ 2 ∫_{F̊} |F| dLⁿ` from the median choice (31)): if
`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2` for an integrable `u` on a probability space, then
`|β| ≤ 2 ∫ |u| dμ`.  By Markov's inequality `|β| μ{|β| ≤ |u|} ≤ ∫ |u| dμ`, and `{|β| ≤ |u|}`
contains `{β ≤ u}` if `β ≥ 0` and `{u ≤ β}` if `β < 0`, so it has measure `≥ 1/2`. -/
theorem Submission.dimred_mbl_dt_cbm_im_median_abs_le : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → |β| ≤ 2 * ∫ x, |u x| ∂μ := by
  intro X _ μ u β _ hu hge hle
  -- Markov's inequality for `|u|` at level `|β|`
  have hmarkov : |β| * μ.real {x | |β| ≤ |u x|} ≤ ∫ x, |u x| ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg (u x)) hu.abs |β|
  -- `{|β| ≤ |u|}` contains `{β ≤ u}` if `β ≥ 0` and `{u ≤ β}` if `β < 0`
  have hhalf : 1 / 2 ≤ μ.real {x | |β| ≤ |u x|} := by
    rcases le_or_gt 0 β with hβ | hβ
    · refine hge.trans (measureReal_mono fun x (hx : β ≤ u x) => ?_)
      rw [abs_of_nonneg hβ]
      exact hx.trans (le_abs_self (u x))
    · refine hle.trans (measureReal_mono fun x (hx : u x ≤ β) => ?_)
      rw [abs_of_neg hβ]
      exact (neg_le_neg hx).trans (neg_le_abs (u x))
  calc |β| = 2 * (|β| * (1 / 2)) := by ring
    _ ≤ 2 * (|β| * μ.real {x | |β| ≤ |u x|}) := by gcongr
    _ ≤ 2 * ∫ x, |u x| ∂μ := by gcongr

/-- **Simon 6.5.1** (proof, (31) and (35): the integer median `β_F` and `|β_F| ≤ 2∫_{F̊}|F|`):
if `u` is integer-valued and integrable on the open unit cube `Q₁ = (0, 1)ⁿ`, some `β ∈ ℤ`
minimizes `c ↦ ∫_{Q₁} |u - c|` and satisfies `|β| ≤ 2 ∫_{Q₁} |u|`.  Since `vol(Q₁) = 1`, Lebesgue
measure restricted to `Q₁` is a probability measure; an integer median `β` of `u` for it exists,
minimizes the `L¹` deviation, and is bounded by twice the `L¹` norm. -/
theorem Submission.dimred_mbl_dt_cbm_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, (∀ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c|) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hu hint
  -- `μ := volume.restrict Q₁` is a probability measure, as `vol(Q₁) = 1`
  have hμ : IsProbabilityMeasure
      (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact Submission.cmcdtfrfg_cube_volume (m + 1)⟩
  -- an integer median `β` of `u` for `μ` (`IntegrableOn u Q₁` is `Integrable u μ`)
  obtain ⟨β, hβu, huβ⟩ := Submission.dimred_mbl_dt_cbm_im_integer_median_exists _ _ u hμ
    hint.integrable.aemeasurable hu
  exact ⟨β, Submission.dimred_mbl_dt_cbm_im_median_minimizes _ _ u β hμ hint.integrable hβu huβ,
    Submission.dimred_mbl_dt_cbm_im_median_abs_le _ _ u β hμ hint.integrable hβu huβ⟩
/-- **Simon, proof of the deformation theorem** (the `BV`-trace step): a continuous
`f : ℝᵏ → ℝ` is bounded and integrable on the open unit cube `Q₁ = {y : 0 < yᵢ < 1}`.  The closed
cube `K = {0 ≤ yᵢ ≤ 1}` is the preimage of the compact box `∏ᵢ [0, 1]` under the coordinate
homeomorphism `PiLp.homeomorph`, hence compact; `f` is bounded and (for the Haar measure `volume`)
integrable on `K`, hence on `Q₁ ⊆ K`. -/
theorem Submission.dimred_mbl_dt_cbm_bvt_cube_cont_bound : ∀ (k : ℕ) (f : Euclid k → ℝ), Continuous f → (∃ M : ℝ, ∀ y ∈ {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ M) ∧ IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
  intro k f hf
  -- the closed unit cube is compact
  have hK : IsCompact {y : Euclid k | ∀ i, 0 ≤ y i ∧ y i ≤ 1} := by
    have hpre : {y : Euclid k | ∀ i, 0 ≤ y i ∧ y i ≤ 1} =
        (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)) ⁻¹' (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1) := by
      ext y
      simp [PiLp.homeomorph, Pi.le_def, forall_and]
    rw [hpre]
    exact (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.2
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hsub : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ⊆ {y : Euclid k | ∀ i, 0 ≤ y i ∧ y i ≤ 1} :=
    fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨⟨C, fun y hy => ?_⟩, (hf.continuousOn.integrableOn_compact hK).mono_set hsub⟩
  simpa [Real.norm_eq_abs] using hC y (hsub hy)
/-- **Trace estimate on cubes, the limit `k → ∞`** (for the appeal to Simon Ch. 2, 2.8–2.9 in
(32) of the proof of Ch. 6, 5.1): an affine bound `|∫_S v_k h| ≤ A + B ∫_S |v_k|` (`B ≥ 0`) passes
to an `L¹(S)` limit `w` of the `v_k`, for a multiplier `h` with `|h| ≤ M` on the measurable set
`S`.  With `ε_k = ∫_S |v_k - w| → 0` one has `|∫_S w h - ∫_S v_k h| ≤ M ε_k` and
`∫_S |v_k| ≤ ∫_S |w| + ε_k`, so `|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k` for every `k`. -/
theorem Submission.dimred_mbl_dt_cbm_bvt_l1_limit : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (v : ℕ → α → ℝ) (w h : α → ℝ) (A B M : ℝ), MeasurableSet S → 0 ≤ B → (∀ k, IntegrableOn (v k) S μ) → IntegrableOn w S μ → AEStronglyMeasurable h (μ.restrict S) → (∀ x ∈ S, |h x| ≤ M) → Tendsto (fun k => ∫ x in S, |v k x - w x| ∂μ) atTop (𝓝 0) → (∀ k, |∫ x in S, v k x * h x ∂μ| ≤ A + B * ∫ x in S, |v k x| ∂μ) → |∫ x in S, w x * h x ∂μ| ≤ A + B * ∫ x in S, |w x| ∂μ := by
  intro α _ μ S v w h A B M hS hB hv hw hh hM hlim hbound
  -- 1. `|h| ≤ M` a.e. on `S`, so `w h` and every `v_k h` are integrable on `S`
  have hae : ∀ᵐ x ∂(μ.restrict S), ‖h x‖ ≤ M := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simpa [Real.norm_eq_abs] using hM x hx
  have hwh : Integrable (fun x => w x * h x) (μ.restrict S) := Integrable.mul_bdd hw hh hae
  have hvh : ∀ k, Integrable (fun x => v k x * h x) (μ.restrict S) :=
    fun k => Integrable.mul_bdd (hv k) hh hae
  -- 2–4. for every `k`, `|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k` with `ε_k = ∫_S |v_k - w|`
  have key : ∀ k, |∫ x in S, w x * h x ∂μ| ≤
      A + B * ∫ x in S, |w x| ∂μ + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by
    intro k
    have hdiff : Integrable (fun x => |v k x - w x|) (μ.restrict S) := ((hv k).sub hw).abs
    -- 2. `|∫_S w h - ∫_S v_k h| ≤ ∫_S |v_k - w| |h| ≤ M ε_k`
    have h1 : |∫ x in S, w x * h x ∂μ - ∫ x in S, v k x * h x ∂μ| ≤
        M * ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_sub hwh (hvh k), ← integral_const_mul]
      refine abs_integral_le_integral_abs.trans (integral_mono_ae (hwh.sub (hvh k)).abs
        (hdiff.const_mul M) ?_)
      filter_upwards [ae_restrict_mem hS] with x hx
      calc |w x * h x - v k x * h x| = |v k x - w x| * |h x| := by
            rw [← sub_mul, abs_mul, abs_sub_comm]
        _ ≤ |v k x - w x| * M := mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg _)
        _ = M * |v k x - w x| := mul_comm _ _
    -- 3. `∫_S |v_k| ≤ ∫_S |w| + ε_k`, from `|v_k| ≤ |w| + |v_k - w|`
    have h2 : ∫ x in S, |v k x| ∂μ ≤ ∫ x in S, |w x| ∂μ + ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_add hw.abs hdiff]
      refine integral_mono (hv k).abs (hw.abs.add hdiff) fun x => ?_
      have := abs_add_le (w x) (v k x - w x)
      rwa [add_sub_cancel] at this
    -- 4. `|∫_S w h| ≤ |∫_S v_k h| + M ε_k ≤ A + B (∫_S |w| + ε_k) + M ε_k`, as `B ≥ 0`
    calc |∫ x in S, w x * h x ∂μ|
        ≤ |∫ x in S, v k x * h x ∂μ| + |∫ x in S, w x * h x ∂μ - ∫ x in S, v k x * h x ∂μ| := by
          linarith [abs_sub_abs_le_abs_sub (∫ x in S, w x * h x ∂μ) (∫ x in S, v k x * h x ∂μ)]
      _ ≤ (A + B * ∫ x in S, |v k x| ∂μ) + M * ∫ x in S, |v k x - w x| ∂μ :=
          add_le_add (hbound k) h1
      _ ≤ (A + B * (∫ x in S, |w x| ∂μ + ∫ x in S, |v k x - w x| ∂μ)) +
            M * ∫ x in S, |v k x - w x| ∂μ := by gcongr
      _ = A + B * ∫ x in S, |w x| ∂μ + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by ring
  -- 5. let `k → ∞`: `ε_k → 0`
  have hlim' : Tendsto (fun k => A + B * ∫ x in S, |w x| ∂μ +
      (B + M) * ∫ x in S, |v k x - w x| ∂μ) atTop (𝓝 (A + B * ∫ x in S, |w x| ∂μ + (B + M) * 0)) :=
    tendsto_const_nhds.add (hlim.const_mul _)
  have := ge_of_tendsto' hlim' key
  rwa [mul_zero, add_zero] at this
/-- **Simon, proof of Ch. 6, 5.1, display (32)** (the limit `δ ↓ 0` of the trace estimate on the
unit cube that replaces Ch. 2, 2.9): if `f` is integrable on `Q₁ = {0 < yᵢ < 1}`, then
`∫_{Q_δ} f → ∫_{Q₁} f` as `δ ↓ 0`, where `Q_δ = {δ < zᵢ < 1 − δ}`.  For `δ > 0`, `Q_δ ⊆ Q₁` gives
`∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f`; every point of `Q₁` lies in `Q_δ` for all small `δ`, so dominated
convergence with the bound `|f|` applies. -/
theorem Submission.dimred_mbl_dt_cbm_bvt_cube_exhaust : ∀ (k : ℕ) (f : Euclid k → ℝ), IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} → Tendsto (fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y) (𝓝[>] 0) (𝓝 (∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, f y)) := by
  intro k f hf
  -- the boxes `{a < zᵢ < b ∀ i}` are open, hence measurable
  have hcoord : ∀ i : Fin k, Continuous fun z : Euclid k => z i := fun i =>
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin k => ℝ))
  have hopen : ∀ a b : ℝ, IsOpen {z : Euclid k | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    have : {z : Euclid k | ∀ i, a < z i ∧ z i < b} =
        ⋂ i, ({z : Euclid k | a < z i} ∩ {z : Euclid k | z i < b}) := by
      ext z; simp
    rw [this]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (hcoord i)).inter (isOpen_lt (hcoord i) continuous_const)
  set Q₁ : Set (Euclid k) := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}
  have hQ₁m : MeasurableSet Q₁ := (hopen 0 1).measurableSet
  have hQm : ∀ δ : ℝ, MeasurableSet {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} :=
    fun δ => (hopen δ (1 - δ)).measurableSet
  -- `Q_δ ⊆ Q₁` for `δ ≥ 0`
  have hsub : ∀ δ : ℝ, 0 ≤ δ → {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆ Q₁ :=
    fun δ hδ z hz i => ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- dominated convergence on `Q₁` for `1_{Q_δ} f → f`, with the bound `|f|`
  have hF : Tendsto (fun δ : ℝ =>
        ∫ y in Q₁, {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}.indicator f y)
      (𝓝[>] 0) (𝓝 (∫ y in Q₁, f y)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
      (Eventually.of_forall fun δ => hf.aestronglyMeasurable.indicator (hQm δ))
      (Eventually.of_forall fun δ => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _)
      hf.norm ?_
    filter_upwards [ae_restrict_mem hQ₁m] with y hy
    -- each `y ∈ Q₁` lies in `Q_δ` for all small `δ` (finitely many coordinates)
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), y ∈ {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} := by
      have h0 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ i, δ < y i ∧ y i < 1 - δ := by
        rw [Filter.eventually_all]
        intro i
        have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < y i := eventually_lt_nhds (hy i).1
        have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 1 - y i := eventually_lt_nhds (by linarith [(hy i).2])
        filter_upwards [h1, h2] with δ hδ1 hδ2
        exact ⟨hδ1, by linarith⟩
      exact h0.filter_mono nhdsWithin_le_nhds
    exact tendsto_const_nhds.congr' (hev.mono fun δ hδ => (indicator_of_mem hδ f).symm)
  -- for `δ > 0`, `∫_{Q₁} 1_{Q_δ} f = ∫_{Q₁ ∩ Q_δ} f = ∫_{Q_δ} f`
  refine hF.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  rw [setIntegral_indicator (hQm δ), Set.inter_eq_right.2 (hsub δ (le_of_lt hδ))]
/-- The integrands of the smooth trace estimate are integrable on an open cube (fact (F3) of its
proof): a continuous `h : ℝⁿ → ℝ` is integrable on the open box `{z : a < z_j < b for all j}`,
which lies in the compact closed box `toLp '' Icc (fun _ => a) (fun _ => b)`. -/
theorem Submission.dimred_mbl_dt_cbm_st_box_integrableOn : ∀ (n : ℕ) (h : Euclid n → ℝ) (a b : ℝ), Continuous h → IntegrableOn h {z : Euclid n | ∀ j, a < z j ∧ z j < b} := by
  intro n h a b hh
  have hsub : {z : Euclid n | ∀ j, a < z j ∧ z j < b} ⊆
      (WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hz j).1.le, fun j => (hz j).2.le⟩, rfl⟩
  have hKc : IsCompact ((WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  exact (hh.continuousOn.integrableOn_compact hKc).mono_set hsub
/-- Coordinate slicing (Fubini in the `i`-th coordinate) on the open cube `Q = (a, b)^{m+1}` of
`ℝ^{m+1}`: with `ι(t, y) = toLp 2 (Fin.insertNth i t y)` and `Q' = (a, b)^m ⊆ ℝ^m`, the slice
integral `y ↦ ∫_a^b h(ι(t, y)) dt` is integrable on `Q'` and `∫_Q h = ∫_{Q'} ∫_a^b h(ι(t, y)) dt dy`.
The map `E(t, y) = ι(t, y)` is the measure-preserving equivalence
`(MeasurableEquiv.piFinSuccAbove _ i).symm` followed by `MeasurableEquiv.toLp 2`, and
`E⁻¹(Q) = (a, b) ×ˢ Q'`; then change variables, apply Fubini with outer variable `y`, and replace
`∫_{(a, b)}` by `∫_a^b` (`a ≤ b`, `{b}` is null). -/
theorem Submission.dimred_mbl_dt_cbm_st_slice_integral : ∀ (m : ℕ) (i : Fin (m + 1)) (a b : ℝ) (h : Euclid (m + 1) → ℝ), a ≤ b → IntegrableOn h {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b} → IntegrableOn (fun y : Fin m → ℝ => ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y))) {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b} ∧ ∫ x in {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b}, h x = ∫ y in {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b}, ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
  intro m i a b h hab hint
  set Q : Set (Euclid (m + 1)) := {z | ∀ j, a < z j ∧ z j < b} with hQ
  set Q' : Set (Fin m → ℝ) := {y | ∀ j, a < y j ∧ y j < b} with hQ'
  -- `E (t, y) = toLp 2 (insertNth i t y)`: a measure-preserving equivalence `ℝ × ℝ^m ≃ ℝ^{m+1}`
  let E : ℝ × (Fin m → ℝ) ≃ᵐ Euclid (m + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ))
  have hE : MeasurePreserving E (volume.prod volume) volume :=
    (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have hEapply : ∀ p : ℝ × (Fin m → ℝ), E p = WithLp.toLp 2 (Fin.insertNth i p.1 p.2) :=
    fun p => rfl
  -- `E⁻¹(Q) = (a, b) ×ˢ Q'`
  have hpre : E ⁻¹' Q = Ioo a b ×ˢ Q' := by
    ext ⟨t, y⟩
    simp only [Set.mem_preimage, hEapply, Q, Q', Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
    rw [Fin.forall_iff_succAbove i]
    simp
  have hint' : Integrable (fun p => h (E p))
      ((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
    rw [Measure.prod_restrict, ← hpre]
    exact (hE.integrableOn_comp_preimage E.measurableEmbedding).2 hint
  -- since `a ≤ b`, the inner integral over `(a, b)` is the interval integral `∫_a^b`
  have hinner : ∀ y : Fin m → ℝ, ∫ t in Ioo a b, h (E (t, y)) =
      ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
    intro y
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    rfl
  refine ⟨?_, ?_⟩
  · have := hint'.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ x in Q, h x = ∫ p in E ⁻¹' Q, h (E p) ∂(volume.prod volume) :=
          (hE.setIntegral_preimage_emb E.measurableEmbedding h Q).symm
      _ = ∫ p, h (E p) ∂((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
          rw [hpre, Measure.prod_restrict]
      _ = ∫ y in Q', ∫ t in Ioo a b, h (E (t, y)) := integral_prod_symm _ hint'
      _ = ∫ y in Q', ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
          simp only [hinner]
/-- **One-dimensional boundary-term and trace estimate.**  For `a < b`, `C¹` functions `φ, γ` on
`ℝ` with `|γ| ≤ 1`, `|∫_a^b (φγ)'| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|`.  By the fundamental
theorem of calculus the left side is `|φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(b)| + |φ(a)|`.  For `c, t ∈ [a, b]`,
`|φ(c)| ≤ |φ(t)| + |∫_t^c φ'| ≤ |φ(t)| + ∫_a^b |φ'|`; averaging over `t ∈ [a, b]` gives
`|φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + ∫_a^b |φ'|`, applied at `c = a` and `c = b`. -/
theorem Submission.dimred_mbl_dt_cbm_st_interval_bound : ∀ (φ γ : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 γ → (∀ t, |γ t| ≤ 1) → a < b → |∫ t in a..b, deriv (fun s => φ s * γ s) t| ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
  intro φ γ a b hφ hγ hγb hab
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpc : ContDiff ℝ 1 (fun s => φ s * γ s) := hφ.mul hγ
  -- fundamental theorem of calculus for the product
  have hftc : ∫ t in a..b, deriv (fun s => φ s * γ s) t = φ b * γ b - φ a * γ a :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => (hpc.differentiable one_ne_zero) t)
      ((hpc.continuous_deriv le_rfl).intervalIntegrable _ _)
  -- the one-dimensional trace inequality at a point `c ∈ [a, b]`
  have htrace : ∀ c ∈ Icc a b,
      |φ c| ≤ (b - a)⁻¹ * (∫ t in a..b, |φ t|) + ∫ t in a..b, |deriv φ t| := by
    intro c hc
    set D := ∫ t in a..b, |deriv φ t| with hD
    have hpt : ∀ t ∈ Icc a b, |φ c| ≤ |φ t| + D := by
      intro t ht
      have hsub : φ c - φ t = ∫ s in t..c, deriv φ s :=
        (intervalIntegral.integral_deriv_eq_sub (fun s _ => hφd s)
          (hφ'c.intervalIntegrable _ _)).symm
      have hle : |∫ s in t..c, deriv φ s| ≤ D := by
        have habs : |∫ s in t..c, deriv φ s| ≤ |∫ s in t..c, (|deriv φ s|)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_abs_integral_norm (f := deriv φ) (a := t) (b := c)
              (μ := volume))
        refine habs.trans ?_
        rcases le_total t c with htc | hct
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg htc fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval ht.1 htc hc.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
        · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hct fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hc.1 hct ht.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
      calc |φ c| = |φ t + (φ c - φ t)| := by ring_nf
        _ ≤ |φ t| + |φ c - φ t| := abs_add_le _ _
        _ ≤ |φ t| + D := by rw [hsub]; gcongr
    have hint : ∫ t in a..b, |φ c| ≤ ∫ t in a..b, (|φ t| + D) :=
      intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        ((hφd.continuous.abs.add continuous_const).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (hφd.continuous.abs.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hint
    have hba : 0 < b - a := sub_pos.mpr hab
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hba]
    nlinarith
  have hA := htrace a ⟨le_rfl, hab.le⟩
  have hB := htrace b ⟨hab.le, le_rfl⟩
  rw [hftc]
  have hγa := hγb a
  have hγb' := hγb b
  calc |φ b * γ b - φ a * γ a| ≤ |φ b * γ b| + |φ a * γ a| := abs_sub _ _
    _ = |φ b| * |γ b| + |φ a| * |γ a| := by rw [abs_mul, abs_mul]
    _ ≤ |φ b| * 1 + |φ a| * 1 := by gcongr
    _ = |φ b| + |φ a| := by ring
    _ ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
        have : 2 / (b - a) = (b - a)⁻¹ + (b - a)⁻¹ := by ring
        rw [this]; linarith

/-- **One-coordinate divergence estimate on the cube** `Q_δ = {z : δ < z_j < 1 − δ ∀ j}` (the
`i`-th term of the smooth trace estimate behind Simon Ch. 2, 2.8–2.9, on a cube of side
`1 − 2δ ≥ 1/2`): for `C¹` functions `v, g` with `|g| ≤ 1`,
`|∫_{Q_δ} D(vg)(x)eᵢ dx| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖`.  Slice `Q_δ` into the lines
`t ↦ ι(t, y) = toLp 2 (insertNth i t y)`, `y ∈ Q'`, whose velocity is `eᵢ`.  On each line,
`(vg)∘ι` has derivative `D(vg)(ι)eᵢ`, so the one-dimensional estimate, `2/(1 − 2δ) ≤ 4` and
`|Dv(x)eᵢ| ≤ ‖Dv(x)‖` give `|∫_δ^{1−δ} D(vg)(ι)eᵢ| ≤ ∫_δ^{1−δ} (4|v| + 2‖Dv‖)(ι)`; then
integrate over `y ∈ Q'`. -/
theorem Submission.dimred_mbl_dt_cbm_st_coord_bound : ∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v g i δ hv hg hgb _ hδ
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}
  set Q' : Set (Fin m → ℝ) := {y : Fin m → ℝ | ∀ j, δ < y j ∧ y j < 1 - δ}
  have hab : δ < 1 - δ := by linarith
  -- the line `t ↦ ι t y` through the slice point `y` in direction `eᵢ`
  set ι : ℝ → (Fin m → ℝ) → Euclid (m + 1) := fun t y => WithLp.toLp 2 (Fin.insertNth i t y)
  have hι_affine : ∀ y,
      (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
    intro y
    funext s
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [ι]
    | p j => simp [ι, Fin.succAbove_ne]
  have hι_deriv : ∀ t y, HasDerivAt (fun s => ι s y) (EuclideanSpace.single i 1) t := by
    intro t y
    rw [hι_affine y]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (ι 0 y)
  have hι_cd : ∀ y, ContDiff ℝ 1 (fun s => ι s y) := by
    intro y
    rw [hι_affine y]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hvg : ContDiff ℝ 1 (fun y => v y * g y) := hv.mul hg
  -- `F = D(vg)(·)eᵢ` and the majorant `H = 4|v| + 2‖Dv‖`, both continuous
  set F : Euclid (m + 1) → ℝ := fun x => fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)
  set H : Euclid (m + 1) → ℝ := fun x => 4 * |v x| + 2 * ‖fderiv ℝ v x‖
  have hFc : Continuous F := (hvg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : Continuous fun x => |v x| := hv.continuous.abs
  have hDvc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hHc : Continuous H := (continuous_const.mul hvc).add (continuous_const.mul hDvc)
  -- slice `Q` along the `i`-th coordinate
  obtain ⟨-, hFslice⟩ := Submission.dimred_mbl_dt_cbm_st_slice_integral m i δ (1 - δ) F hab.le
    (Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hFc)
  obtain ⟨hHint, hHslice⟩ := Submission.dimred_mbl_dt_cbm_st_slice_integral m i δ (1 - δ) H hab.le
    (Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hHc)
  have hHsplit : ∫ x in Q, H x = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [integral_add ((Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hvc).const_mul 4)
      ((Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _ hDvc).const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the one-dimensional estimate on each line
  have hline : ∀ y, |∫ t in δ..(1 - δ), F (ι t y)| ≤ ∫ t in δ..(1 - δ), H (ι t y) := by
    intro y
    have hφ : ContDiff ℝ 1 (fun s => v (ι s y)) := hv.comp (hι_cd y)
    have hγ : ContDiff ℝ 1 (fun s => g (ι s y)) := hg.comp (hι_cd y)
    -- chain rule along the line: `((vg)∘ι)' = D(vg)(ι)eᵢ` and `(v∘ι)' = Dv(ι)eᵢ`
    have hderiv_prod : ∀ t, deriv (fun s => v (ι s y) * g (ι s y)) t = F (ι t y) := by
      intro t
      have := (hvg.differentiable one_ne_zero (ι t y)).hasFDerivAt.comp_hasDerivAt t (hι_deriv t y)
      exact this.deriv
    have hderiv_v : ∀ t, deriv (fun s => v (ι s y)) t =
        fderiv ℝ v (ι t y) (EuclideanSpace.single i 1) := by
      intro t
      have := (hv.differentiable one_ne_zero (ι t y)).hasFDerivAt.comp_hasDerivAt t (hι_deriv t y)
      exact this.deriv
    have h1 := Submission.dimred_mbl_dt_cbm_st_interval_bound (fun s => v (ι s y))
      (fun s => g (ι s y)) δ (1 - δ) hφ hγ (fun t => hgb _) hab
    simp only [hderiv_prod, hderiv_v] at h1
    have hcoef : 2 / (1 - δ - δ) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hint_nonneg : 0 ≤ ∫ t in δ..(1 - δ), |v (ι t y)| :=
      intervalIntegral.integral_nonneg hab.le fun t _ => abs_nonneg _
    have hcont_v : Continuous fun t => |v (ι t y)| := hφ.continuous.abs
    have hcont_Dv : Continuous fun t => ‖fderiv ℝ v (ι t y)‖ := hDvc.comp (hι_cd y).continuous
    have hcont_dv : Continuous fun t => |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| :=
      (((hv.continuous_fderiv one_ne_zero).comp (hι_cd y).continuous).clm_apply
        continuous_const).abs
    -- `|Dv(x)eᵢ| ≤ ‖Dv(x)‖ ‖eᵢ‖ = ‖Dv(x)‖`
    have hmono : ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| ≤
        ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      refine intervalIntegral.integral_mono_on hab.le (hcont_dv.intervalIntegrable _ _)
        (hcont_Dv.intervalIntegrable _ _) fun t _ => ?_
      have := (fderiv ℝ v (ι t y)).le_opNorm (EuclideanSpace.single i 1)
      rwa [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] at this
    have hHline : ∫ t in δ..(1 - δ), H (ι t y) =
        4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      simp only [H]
      rw [intervalIntegral.integral_add ((hcont_v.intervalIntegrable _ _).const_mul 4)
        ((hcont_Dv.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hHline]
    calc |∫ t in δ..(1 - δ), F (ι t y)|
        ≤ 2 / (1 - δ - δ) * (∫ t in δ..(1 - δ), |v (ι t y)|) +
            2 * ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| := h1
      _ ≤ 4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
        gcongr
  -- integrate the line estimate over the face variable `y ∈ Q'`
  calc |∫ x in Q, F x|
      = |∫ y in Q', ∫ t in δ..(1 - δ), F (ι t y)| := by rw [hFslice]
    _ ≤ ∫ y in Q', |∫ t in δ..(1 - δ), F (ι t y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q', ∫ t in δ..(1 - δ), H (ι t y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hHint
          (Eventually.of_forall hline)
    _ = ∫ x in Q, H x := hHslice.symm
    _ = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := hHsplit
/-- Pointwise product rule for the divergence: if `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` are
differentiable at `x`, then `v(x) · trace DG(x) = Σᵢ D(v Gᵢ)(x) eᵢ − Dv(x)(G(x))`, where
`eᵢ = EuclideanSpace.single i 1` and `Gᵢ = (G ·)ᵢ`.  The product rule gives
`D(v Gᵢ)(x) eᵢ = v(x) (DG(x) eᵢ)ᵢ + Gᵢ(x) Dv(x) eᵢ`.  In the standard orthonormal basis,
`trace DG(x) = Σᵢ ⟪eᵢ, DG(x) eᵢ⟫ = Σᵢ (DG(x) eᵢ)ᵢ`, and `Dv(x)(G(x)) = Σᵢ Gᵢ(x) Dv(x) eᵢ` because
`G(x) = Σᵢ Gᵢ(x) eᵢ`.  Summing over `i` and rearranging gives the claim. -/
theorem Submission.dimred_mbl_dt_cbm_st_div_product : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (x : Euclid (m + 1)), DifferentiableAt ℝ v x → DifferentiableAt ℝ G x → v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = ∑ i, fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) - fderiv ℝ v x (G x) := by
  intro m v G x hv hG
  -- the coordinate `Gᵢ = projᵢ ∘ G` has derivative `projᵢ ∘ DG(x)`
  have hGi : ∀ i : Fin (m + 1), HasFDerivAt (fun y => G y i)
      ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x)) x := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x hG.hasFDerivAt
  -- product rule, evaluated at `eᵢ`
  have hprod : ∀ i : Fin (m + 1),
      fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) =
        v x * (fderiv ℝ G x (EuclideanSpace.single i 1)) i +
          G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    intro i
    have h : HasFDerivAt (fun y => v y * G y i)
        (v x • (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x) +
          G x i • fderiv ℝ v x) x := hv.hasFDerivAt.mul (hGi i)
    rw [h.fderiv]
    simp
  -- the trace in the standard orthonormal basis
  have htrace : LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      ∑ i, (fderiv ℝ G x (EuclideanSpace.single i 1)) i := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp
  -- `G(x) = Σᵢ Gᵢ(x) eᵢ`, hence `Dv(x)(G(x)) = Σᵢ Gᵢ(x) Dv(x) eᵢ`
  have hexp : G x = ∑ i, G x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hDvG : fderiv ℝ v x (G x) = ∑ i, G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hexp]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [htrace, hDvG, Finset.mul_sum]
  simp only [hprod, Finset.sum_add_distrib]
  ring
/-- **Simon Ch. 2, 2.8–2.9, smooth case on the cube** (step 5 of the proof of
`dimred_mbl_dt_cube_bv_median`).  Let `n = m + 1`, `0 ≤ δ ≤ 1/4` and `Q_δ = (δ, 1 − δ)ⁿ`.  For `C¹`
maps `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` with `|G| ≤ 1`,
`|∫_{Q_δ} v div G| ≤ (2n + 1)∫_{Q_δ}‖Dv‖ + 4n∫_{Q_δ}|v|`.  By the product rule
`v div G = Σᵢ ∂ᵢ(vGᵢ) − Dv(G)`.  The divergence theorem on the box and the face estimate bound each
`|∫_{Q_δ} ∂ᵢ(vGᵢ)|` by `4∫_{Q_δ}|v| + 2∫_{Q_δ}‖Dv‖`, and `|∫_{Q_δ} Dv(G)| ≤ ∫_{Q_δ}‖Dv‖` since
`|G| ≤ 1`.  Summing over the `n` coordinates gives the bound. -/
theorem Submission.dimred_mbl_dt_cbm_smooth_trace : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x)| ≤ (2 * (m + 1) + 1) * (∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x| := by
  intro m v G δ hv hG hGb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- the coordinates `Gᵢ = projᵢ ∘ G` are `C¹`, with `|Gᵢ| ≤ |G| ≤ 1`
  have hGi : ∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y => G y i) := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hGib : ∀ (i : Fin (m + 1)) (y : Euclid (m + 1)), |G y i| ≤ 1 := by
    intro i y
    have h := PiLp.norm_apply_le (G y) i
    rw [Real.norm_eq_abs] at h
    exact h.trans (hGb y)
  -- the integrands `Fᵢ = ∂ᵢ(vGᵢ)`, `D = Dv(G)` and `‖Dv‖` are continuous, hence integrable on `Q`
  set F : Fin (m + 1) → Euclid (m + 1) → ℝ :=
    fun i x => fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1)
  set D : Euclid (m + 1) → ℝ := fun x => fderiv ℝ v x (G x)
  have hFint : ∀ i, IntegrableOn (F i) Q := fun i =>
    Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _
      (((hv.mul (hGi i)).continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hDint : IntegrableOn D Q :=
    Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _
      ((hv.continuous_fderiv one_ne_zero).clm_apply hG.continuous)
  have hDvint : IntegrableOn (fun x => ‖fderiv ℝ v x‖) Q :=
    Submission.dimred_mbl_dt_cbm_st_box_integrableOn _ _ _ _
      (hv.continuous_fderiv one_ne_zero).norm
  -- step 1: `v div G = Σᵢ Fᵢ - D` pointwise, so `∫_Q v div G = Σᵢ ∫_Q Fᵢ - ∫_Q D`
  have hpt : ∀ x, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = (∑ i, F i x) - D x :=
    fun x => Submission.dimred_mbl_dt_cbm_st_div_product m v G x
      (hv.differentiable one_ne_zero x) (hG.differentiable one_ne_zero x)
  have hsplit : ∫ x in Q, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      (∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x := by
    simp_rw [hpt]
    rw [integral_sub (integrable_finsetSum _ fun i _ => hFint i) hDint,
      integral_finsetSum _ fun i _ => hFint i]
  -- steps 2 and 4, one coordinate at a time: `|∫_Q Fᵢ| ≤ 4∫_Q|v| + 2∫_Q‖Dv‖`
  have hFb : ∀ i, |∫ x in Q, F i x| ≤ 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ :=
    fun i => Submission.dimred_mbl_dt_cbm_st_coord_bound m v (fun y => G y i) i δ hv (hGi i)
      (hGib i) hδ0 hδ1
  -- `|∫_Q D| ≤ ∫_Q ‖Dv‖`, since `|Dv(x)(G x)| ≤ ‖Dv(x)‖ |G x| ≤ ‖Dv(x)‖`
  have hDb : |∫ x in Q, D x| ≤ ∫ x in Q, ‖fderiv ℝ v x‖ := by
    refine abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
      (Eventually.of_forall fun x => abs_nonneg _) hDvint (Eventually.of_forall fun x => ?_))
    calc |D x| = ‖fderiv ℝ v x (G x)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ v x‖ * ‖G x‖ := (fderiv ℝ v x).le_opNorm (G x)
      _ ≤ ‖fderiv ℝ v x‖ * 1 := mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
      _ = ‖fderiv ℝ v x‖ := mul_one _
  -- steps 3 and 5: sum over the `m + 1` coordinates
  rw [hsplit]
  calc |(∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x|
      ≤ |∑ i, ∫ x in Q, F i x| + |∫ x in Q, D x| := abs_sub _ _
    _ ≤ (∑ i, |∫ x in Q, F i x|) + ∫ x in Q, ‖fderiv ℝ v x‖ :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) hDb
    _ ≤ (∑ _i : Fin (m + 1), (4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖)) +
          ∫ x in Q, ‖fderiv ℝ v x‖ :=
        add_le_add (Finset.sum_le_sum fun i _ => hFb i) le_rfl
    _ = (2 * (m + 1) + 1) * (∫ x in Q, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in Q, |v x| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

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

/-- **BV Poincaré inequality on the unit cube** (Simon Ch. 2, 2.7, in the form used for the first
line of display (32) in the proof of Ch. 6, 5.1): if `u ∈ L¹(Q₁)` has `∫_{Q₁} u div g ≤ V` for all
smooth `g` with `spt g ⊆ Q₁` and `|g| ≤ 1`, then `∫_{Q₁} |u - c| ≤ 2ⁿ⁺¹ √n V` with `c = ∫_{Q₁} u`.
Testing with `g ≡ 0` gives `V ≥ 0`.  On every inner cube `Q_δ`, `0 < δ < 1/2`, the `C¹`
approximations `v_k` of `u` satisfy `∫_{Q_δ}∫_{Q_δ} |v_k x - v_k y| ≤ 2ⁿ √n V` by the smooth
Poincaré inequality, and the bound passes to the `L¹` limit `u`; exhausting `Q₁` by the `Q_δ` and
using `|Q₁| = 1` bounds the mean deviation of `u` by the same `2ⁿ √n V ≤ 2ⁿ⁺¹ √n V`. -/
theorem Submission.dimred_mbl_dt_cbm_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c| ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := by
  intro m u V hu hV
  -- `V ≥ 0`: test the hypothesis with `g ≡ 0`
  have hV0 : 0 ≤ V := by
    simpa using hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) fun _ => by simp
  have hK : (0 : ℝ) ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) := by positivity
  -- on each inner cube `Q_δ`, `0 < δ < 1/2`, the oscillation of `u` is at most `2ⁿ √n V`
  have hinner : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
        ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤
        2 ^ (m + 1) * Real.sqrt (m + 1) * V := by
    intro δ hδ _
    obtain ⟨v, hv, hvV, hvu⟩ := Submission.dimred_mbl_dt_cbm_smooth_approx m u V δ hu hV hδ
    refine Submission.dimred_mbl_dt_cbm_bvp_osc_le_of_l1_approx m u v δ _ hu hδ.le
      (fun k => (hv k).continuous) (fun k => ?_) hvu
    exact (Submission.dimred_mbl_dt_cbm_smooth_poincare m (v k) δ (hv k) hδ.le).trans
      (mul_le_mul_of_nonneg_left (hvV k) hK)
  -- exhaust `Q₁` by the inner cubes
  have hosc := Submission.dimred_mbl_dt_cbm_bvp_osc_le_of_inner_cubes m u _ hu hinner
  -- `c = ∫_{Q₁} u`; the mean deviation is at most the oscillation since `|Q₁| = 1`
  refine ⟨∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y,
    ((Submission.dimred_mbl_dt_cbm_bvp_mean_dev_le_osc m _ u
      (Submission.cmcdtfrfg_cube_volume (m + 1)) hu).trans hosc).trans ?_⟩
  have h2 : (2 : ℝ) ^ (m + 1) ≤ 2 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)) hV0
/-- **Simon, proof of Ch. 6, 5.1** (second line of display (32), in place of the appeal to Ch. 2,
2.8–2.9): if `w` is integrable on the open unit cube `Q₁ ⊆ ℝⁿ` and `∫_{Q₁} w div g ≤ V` for every
smooth `g` with compact support in `Q₁` and `|g| ≤ 1`, then
`|∫_{Q₁} w div G| ≤ (2n + 1)V + 4n∫_{Q₁}|w|` for every `C¹` field `G` with `|G| ≤ 1`.  On
`Q_δ = {δ < yᵢ < 1 - δ}`, `0 < δ ≤ 1/4`, the smooth estimate for the approximations `v_k` of `w`
passes to the `L¹(Q_δ)` limit `w` (`div G` is continuous, hence bounded on `Q₁`); letting `δ ↓ 0`
gives the estimate on `Q₁`. -/
theorem Submission.dimred_mbl_dt_cbm_bv_trace : ∀ (m : ℕ) (w : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn w {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
  intro m w V hw hV G hG hGb
  -- the cubes `{a < yᵢ < b}` are open, and `Q_δ ⊆ Q₁` for `δ ≥ 0`
  have hopen : ∀ a b : ℝ, IsOpen {z : Euclid (m + 1) | ∀ i, a < z i ∧ z i < b} := fun a b => by
    rw [show {z : Euclid (m + 1) | ∀ i, a < z i ∧ z i < b} = ⋂ i, {z | a < z i ∧ z i < b} by
      ext; simp]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hsub : ∀ δ : ℝ, 0 ≤ δ → {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun δ hδ z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- `div G = trace ∘ DG` is continuous, hence bounded by `M` on `Q₁`, so `w div G ∈ L¹(Q₁)`
  have hdiv : Continuous fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
    (LinearMap.continuous_of_finiteDimensional
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ))).comp
      (hG.continuous_fderiv one_ne_zero)
  obtain ⟨⟨M, hM⟩, -⟩ := Submission.dimred_mbl_dt_cbm_bvt_cube_cont_bound (m + 1) _ hdiv
  have hwdiv : IntegrableOn (fun y => w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    Integrable.mul_bdd hw hdiv.aestronglyMeasurable
      (ae_restrict_of_forall_mem (hopen 0 1).measurableSet fun y hy =>
        (Real.norm_eq_abs _).trans_le (hM y hy))
  -- the estimate on `Q_δ`, `0 < δ ≤ 1/4`: the `L¹(Q_δ)` limit of the smooth estimate
  have hQδ : ∀ δ ∈ Ioc (0 : ℝ) (1 / 4),
      |∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
          w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (2 * (m + 1) + 1) * V +
          4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
    rintro δ ⟨hδ0, hδ⟩
    have hs := hsub δ hδ0.le
    obtain ⟨v, hvC, hvD, hvw⟩ := Submission.dimred_mbl_dt_cbm_smooth_approx m w V δ hw hV hδ0
    have hl1 := Submission.dimred_mbl_dt_cbm_bvt_l1_limit volume _ v w _
      ((2 * (m + 1) + 1) * V) (4 * (m + 1)) M (hopen δ (1 - δ)).measurableSet (by positivity)
      (fun k => (Submission.dimred_mbl_dt_cbm_bvt_cube_cont_bound (m + 1) (v k)
        (hvC k).continuous).2.mono_set hs)
      (hw.mono_set hs) hdiv.aestronglyMeasurable (fun y hy => hM y (hs hy)) hvw fun k =>
        (Submission.dimred_mbl_dt_cbm_smooth_trace m (v k) G δ (hvC k) hG hGb hδ0.le hδ).trans
          (by gcongr; exact hvD k)
    refine hl1.trans ?_
    gcongr _ + _ * ?_
    exact setIntegral_mono_set (Integrable.abs hw) (ae_of_all _ fun y => abs_nonneg (w y))
      (ae_of_all _ hs)
  -- `δ ↓ 0`
  exact le_of_tendsto (Submission.dimred_mbl_dt_cbm_bvt_cube_exhaust (m + 1) _ hwdiv).abs
    (eventually_of_mem (Ioc_mem_nhdsGT (by norm_num)) hQδ)

/-- **Simon, proof of Ch. 6, 5.1** (displays (26)–(35), the cube estimate: Poincaré inequality,
integer median and boundary mass of `(u − β)[[Q₁]]`).  For `n = m + 1` there is `c > 0` such that
if `u` is integer-valued and integrable on the open unit cube `Q₁ ⊆ ℝⁿ` and `∫_{Q₁} u div g ≤ V`
for every smooth `g` with compact support in `Q₁` and `|g| ≤ 1`, then some `β ∈ ℤ` has
`∫_{Q₁} |u − β| ≤ cV`, `|β| ≤ 2 ∫_{Q₁} |u|` and `|∫_{Q₁} (u − β) div G| ≤ cV` for every smooth `G`
with `|G| ≤ 1`.  Take `c = A + (2n + 1) + 4nA` with `A = 2ⁿ⁺¹ √n`.  Testing with `g = 0` gives
`V ≥ 0`.  The integer median `β` minimizes `c' ↦ ∫_{Q₁} |u − c'|`, so the BV Poincaré inequality
gives `∫_{Q₁} |u − β| ≤ AV`.  As `∫_{Q₁} div g = 0`, `u − β` satisfies the hypothesis with the
same `V`, and the BV trace inequality gives `|∫_{Q₁} (u − β) div G| ≤ (2n + 1)V + 4nAV`. -/
theorem Submission.dimred_mbl_dt_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  -- `A = 2ⁿ⁺¹ √n ≥ 0` (`n = m + 1`) and `c = A + (2n + 1) + 4nA > 0`
  have hA : (0 : ℝ) ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) := by positivity
  have hAc : (2 : ℝ) ^ (m + 2) * Real.sqrt (m + 1) ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) +
      (2 * (m + 1) + 1) + 4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1)) := by
    have : (0 : ℝ) ≤ 4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1)) := by positivity
    linarith
  refine ⟨2 ^ (m + 2) * Real.sqrt (m + 1) + (2 * (m + 1) + 1) +
    4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1)), by positivity, ?_⟩
  intro u V hu hint hV
  -- `V ≥ 0`: test the hypothesis with `g = 0`
  have hV0 : 0 ≤ V := by
    simpa using hV 0 contDiff_zero_fun HasCompactSupport.zero (by simp) (by simp)
  -- the integer median `β` and the Poincaré constant `c₀`: `∫ |u − β| ≤ ∫ |u − c₀| ≤ AV`
  obtain ⟨β, hβmin, hβabs⟩ := Submission.dimred_mbl_dt_cbm_integer_median m u hu hint
  obtain ⟨c₀, hc₀⟩ := Submission.dimred_mbl_dt_cbm_bv_poincare m u V hint hV
  have h1 := (hβmin c₀).trans hc₀
  refine ⟨β, h1.trans (mul_le_mul_of_nonneg_right hAc hV0), hβabs, fun G hG hG1 => ?_⟩
  -- `u − β` is integrable on `Q₁`, whose volume is finite: `Q₁` is the preimage of the box
  -- `∏ᵢ (0, 1)` under the volume-preserving `ofLp`
  have hQ : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ≠ ∞ := by
    have hpre : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Set.mem_pi]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hwint : IntegrableOn (fun y => u y - (β : ℝ))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    hint.fun_sub (integrableOn_const hQ)
  -- `u − β` satisfies the hypothesis with the same `V`, since `∫_{Q₁} div g = 0`
  have hwV : ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} →
      (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V := by
    intro g hg hgc hgs hg1
    have hg' : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
    -- `div g` is continuous with compact support, hence bounded and integrable
    let T : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ))
    have hdc : Continuous fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) :=
      T.continuous.comp (hg'.continuous_fderiv one_ne_zero)
    have hds : HasCompactSupport fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) :=
      (hgc.fderiv ℝ).comp_left (g := T) (map_zero T)
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support hds
    have hdi : IntegrableOn (fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
      (hdc.integrable_of_hasCompactSupport hds).integrableOn
    have hui : IntegrableOn (fun y => u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
      hint.integrable.mul_bdd hdc.aestronglyMeasurable (ae_of_all _ hC)
    calc ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)
        = (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)) -
          β * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
          simp_rw [sub_mul]
          rw [integral_sub hui (hdi.const_mul (β : ℝ)), integral_const_mul]
      _ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
          rw [Submission.dimred_mbl_dt_cbm_integral_div_eq_zero m g hg' hgc hgs, mul_zero,
            sub_zero]
      _ ≤ V := hV g hg hgc hgs hg1
  -- the BV trace inequality for `u − β`, with `∫_{Q₁} |u − β| ≤ AV`
  have h3 := Submission.dimred_mbl_dt_cbm_bv_trace m (fun y => u y - β) V hwint hwV G
    (hG.of_le (by exact_mod_cast le_top)) hG1
  have hAV : (0 : ℝ) ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := mul_nonneg hA hV0
  calc _ ≤ _ := h3
    _ ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1) * V) := by
      gcongr
    _ ≤ _ := by linarith

/-- **Face replacement in the deformation theorem** (Simon Ch. 6, proof of 5.1, (26)–(37), in the
unit grid).  Let `c_B` be the constant of the cube median estimate (`dimred_mbl_dt_cube_bv_median`)
and `c := max 2 (1 + c_B)`; `𝒬₀` is the finite family of integer chains `Σ_p β_p [[F_p]]` on unit
`n`-faces meeting `K` with `Σ_p |β_p| ≤ 2Λ` (`dimred_mbl_dtfr_finite_family`).  Write
`Q₀ = Σ_p u_p [[F_p]]` with integer densities `u_p` on the faces meeting `spt Q₀`
(`dimred_mbl_dtfr_skeleton_decomposition`), whose variations `V_p` satisfy `Σ_p V_p ≤ M(∂Q₀)`
(`dimred_mbl_dtfr_boundary_variation`), and let `β_p` be the integer medians of the `u_p`; then
`Pc := Σ_p β_p [[F_p]] ∈ 𝒬₀`.  The face currents with densities `β_p` and `u_p - β_p`
(`dimred_mbl_dtfr_face_integral_current`) give `M(Q₀ - Pc), M(∂(Q₀ - Pc)) ≤ c_B M(∂Q₀)` and the
supports; integer polyhedral chains (`dimred_mbl_dtfr_polyhedral_im`,
`dimred_mbl_dtfr_chain_boundary`) give the integrality of `Pc` and `∂Pc` and
`M(Pc) = Σ_p |β_p| ≤ 2 M(Q₀)`; and `∂Pc = ∂Q₀ - ∂(Q₀ - Pc)` (`dimred_mbl_dtfr_current_calculus`)
gives `M(∂Pc) ≤ (1 + c_B) M(∂Q₀)`.  A face meeting a set `X` lies in `cthickening √P X`
(`dimred_mbl_dtfr_face_geometry`). -/
theorem Submission.dimred_mbl_dt_face_replacement : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (K : Set (Euclid P)) (Λ : NNReal), IsCompact K → ∃ 𝒬₀ : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬₀.Finite ∧ ∀ Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → Q₀.mass ≤ Λ → Q₀.boundary.mass < ∞ → ∃ Pc ∈ 𝒬₀, IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity Pc.boundary ∧ (Pc = 0 ∨ 1 ≤ Pc.mass) ∧ Pc.mass ≤ c * Q₀.mass ∧ Pc.boundary.mass ≤ c * Q₀.boundary.mass ∧ (Q₀ - Pc).mass ≤ c * Q₀.boundary.mass ∧ Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support ∧ (Q₀ - Pc).support ∪ Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
  intro hVO hMR hIMC P m
  -- step 1: CB's constant `c_B > 0` and `c := max 2 (1 + c_B) ≥ 1`; the case `n > P` needs no
  -- separate treatment (there are no faces)
  obtain ⟨cB, hcB, hCB⟩ := Submission.dimred_mbl_dt_cube_bv_median m
  have hc2 : ENNReal.ofReal 2 ≤ (Real.toNNReal (max 2 (1 + cB)) : ℝ≥0∞) :=
    ENNReal.ofReal_le_ofReal (le_max_left 2 (1 + cB))
  have hc1B : ENNReal.ofReal (1 + cB) ≤ (Real.toNNReal (max 2 (1 + cB)) : ℝ≥0∞) :=
    ENNReal.ofReal_le_ofReal (le_max_right 2 (1 + cB))
  have hcB1 : ENNReal.ofReal cB ≤ ENNReal.ofReal (1 + cB) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨Real.toNNReal (max 2 (1 + cB)), ?_, fun K Λ hK => ?_⟩
  · calc (1 : NNReal) = Real.toNNReal 1 := Real.toNNReal_one.symm
      _ ≤ Real.toNNReal (max 2 (1 + cB)) :=
        Real.toNNReal_le_toNNReal ((by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _))
  -- step 2: `𝒬₀` is the finite family of integer chains on faces meeting `K`, `Σ|β| ≤ 2Λ`
  refine ⟨_, Submission.dimred_mbl_dtfr_finite_family P (m + 1) K (2 * (Λ : ℝ)) hK, ?_⟩
  intro Q₀ hQ₀ hQ₀K hQ₀L hQ₀Λ hQ₀bd
  -- steps 3-4: `Q₀ = Σ_p u_p [[F_p]]`, integer densities `u_p` on the faces meeting `spt Q₀`
  obtain ⟨s, u, hs, hu, huint, humass, hsmeet, hQ₀rep⟩ :=
    Submission.dimred_mbl_dtfr_skeleton_decomposition hVO hMR hIMC P m K Q₀ hK hQ₀ hQ₀K hQ₀L
  -- step 5: the variations `V_p` of the `u_p`, with `Σ_p V_p ≤ M(∂Q₀)`
  obtain ⟨V, -, hVsum, hVvar, hVspt⟩ :=
    Submission.dimred_mbl_dtfr_boundary_variation hVO P m s u Q₀ hs huint hQ₀rep hQ₀bd
  -- step 6: CB gives the integer medians `β_p`
  have hβ := fun p (hp : p ∈ s) => hCB (u p) (V p) (hu p hp) (huint p hp) (hVvar p hp)
  choose! β hβ1 hβ2 hβ3 using hβ
  -- step 7: the polyhedral current `Pc = Σ_p β_p [[F_p]]` and the face formula for `Q₀ - Pc`
  have hvol : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ≠ ∞ := by
    rw [(Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).1]
    exact ENNReal.one_ne_top
  have hβint : ∀ p ∈ s, IntegrableOn (fun _ : Euclid (m + 1) => (β p : ℝ))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun p _ => integrableOn_const hvol
  obtain ⟨hIu, -, -⟩ := Submission.dimred_mbl_dtfr_face_integral_current P m s u hs huint
  obtain ⟨hIβ, ⟨Pc, hPc⟩, hIIIβ⟩ :=
    Submission.dimred_mbl_dtfr_face_integral_current P m s (fun p _ => (β p : ℝ)) hs hβint
  have hPc' : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω =
      ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
            ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro ω
    rw [hPc ω]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  have hdiff : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (Q₀ - Pc) ω =
      ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u p y - (β p : ℝ)) * (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
            ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro ω
    change Q₀ ω - Pc ω = _
    rw [hQ₀rep ω, hPc ω, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← integral_sub (hIu ω p hp) (hIβ ω p hp)]
    simp only [sub_mul]
  have hwint : ∀ p ∈ s, IntegrableOn (fun y => u p y - (β p : ℝ))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun p hp =>
    (huint p hp).sub (hβint p hp)
  obtain ⟨-, -, hIIIw⟩ := Submission.dimred_mbl_dtfr_face_integral_current P m s
    (fun p y => u p y - (β p : ℝ)) hs hwint
  obtain ⟨hmassD, hbdD, hsptD⟩ := hIIIw (Q₀ - Pc) hdiff
  -- the mass bounds `Σ_p |β_p| ≤ 2 Σ_p ∫|u_p| ≤ 2Λ` and `M(∂(Q₀ - Pc)) ≤ c_B M(∂Q₀)`
  have hsumΛ :
      ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| ≤ (Λ : ℝ) := by
    rw [← ENNReal.ofReal_le_ofReal_iff Λ.coe_nonneg, ENNReal.ofReal_coe_nnreal]
    exact humass.trans hQ₀Λ
  have hβsum : ∑ p ∈ s, |(β p : ℝ)| ≤
      2 * ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => hβ2 p hp
  have hVsum' :
      ENNReal.ofReal (∑ p ∈ s, cB * V p) ≤ ENNReal.ofReal cB * Q₀.boundary.mass := by
    rw [← Finset.mul_sum, ENNReal.ofReal_mul hcB.le]
    exact mul_le_mul' le_rfl hVsum
  have hdiffbd : (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal cB * Q₀.boundary.mass :=
    (hbdD (fun p => cB * V p) fun p hp G hG hG1 => hβ3 p hp G hG hG1).trans hVsum'
  -- step 8: `Pc`, `∂Pc` are integer multiplicity, `M(Pc) = Σ_p |β_p|`, `∂Pc = ∂Q₀ - ∂(Q₀ - Pc)`
  obtain ⟨hPcIM, hPcmass, hPc01⟩ :=
    Submission.dimred_mbl_dtfr_polyhedral_im hMR P (m + 1) s β Pc hs hPc'
  obtain ⟨s', β', hs', hPcbd⟩ := Submission.dimred_mbl_dtfr_chain_boundary P m s β Pc hs hPc'
  obtain ⟨hPcbdIM, -, -⟩ :=
    Submission.dimred_mbl_dtfr_polyhedral_im hMR P m s' β' Pc.boundary hs' hPcbd
  obtain ⟨hcc1, hcc2⟩ := Submission.dimred_mbl_dtfr_current_calculus
  have hPcbdeq : Pc.boundary = Q₀.boundary - (Q₀ - Pc).boundary := by
    have hPceq : Pc = Q₀ - (Q₀ - Pc) := by
      ext ω
      change Pc ω = Q₀ ω - (Q₀ ω - Pc ω)
      ring
    have h := (hcc2 P m univ Q₀ (Q₀ - Pc)).2
    rwa [← hPceq] at h
  -- step 9: the supports; a face meeting `X` lies in `cthickening √P X`
  have hdiam : ∀ p ∈ s, ∀ y y' : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) →
      (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) →
      dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
          ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
          ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P := fun p hp =>
    ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p p (hs p hp) (hs p hp)).2.1
  have hdiffspt : (Q₀ - Pc).support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
    intro x hx
    obtain ⟨p, hp, hne, y, hy, rfl⟩ := hsptD x hx
    -- `∫|u_p - β_p| ≠ 0` forces `V_p ≠ 0`, so the face meets `spt ∂Q₀`
    have hVp : V p ≠ 0 := by
      intro hV
      apply hne
      have h := hβ1 p hp
      rw [hV, mul_zero] at h
      exact le_antisymm h (integral_nonneg fun y => abs_nonneg _)
    obtain ⟨y', hy', hy'Q⟩ := hVspt p hp hVp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  -- step 10: `Pc ∈ 𝒬₀` and the conclusions
  refine ⟨Pc, ⟨s, β, hs, fun p hp => ?_, ?_, hPc'⟩, hPcIM, hPcbdIM, hPc01, ?_, ?_, ?_, ?_,
    union_subset hdiffspt ?_⟩
  · obtain ⟨y, hy, hyQ⟩ := hsmeet p hp
    exact ⟨y, hy, hQ₀K hyQ⟩
  · linarith
  · -- `M(Pc) = Σ_p |β_p| ≤ 2 Σ_p ∫|u_p| ≤ 2 M(Q₀)`
    rw [hPcmass]
    calc ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|)
        ≤ ENNReal.ofReal
            (2 * ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) :=
          ENNReal.ofReal_le_ofReal hβsum
      _ = ENNReal.ofReal 2 * ENNReal.ofReal
            (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) :=
          ENNReal.ofReal_mul (by norm_num)
      _ ≤ _ := mul_le_mul' hc2 humass
  · -- `M(∂Pc) ≤ M(∂Q₀) + M(∂(Q₀ - Pc)) ≤ (1 + c_B) M(∂Q₀)`
    rw [hPcbdeq]
    calc (Q₀.boundary - (Q₀ - Pc).boundary).mass
        ≤ Q₀.boundary.mass + (Q₀ - Pc).boundary.mass :=
          (hcc1 P m univ univ Q₀.boundary (Q₀ - Pc).boundary).2
      _ ≤ Q₀.boundary.mass + ENNReal.ofReal cB * Q₀.boundary.mass := by gcongr
      _ = ENNReal.ofReal (1 + cB) * Q₀.boundary.mass := by
          rw [ENNReal.ofReal_add zero_le_one hcB.le, ENNReal.ofReal_one, add_mul, one_mul]
      _ ≤ _ := mul_le_mul' hc1B le_rfl
  · -- `M(Q₀ - Pc) ≤ Σ_p ∫|u_p - β_p| ≤ c_B Σ_p V_p ≤ c_B M(∂Q₀)`
    calc (Q₀ - Pc).mass
        ≤ ENNReal.ofReal (∑ p ∈ s,
            ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y - (β p : ℝ)|) :=
          hmassD
      _ ≤ ENNReal.ofReal (∑ p ∈ s, cB * V p) :=
          ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun p hp => hβ1 p hp)
      _ ≤ ENNReal.ofReal cB * Q₀.boundary.mass := hVsum'
      _ ≤ _ := mul_le_mul' (hcB1.trans hc1B) le_rfl
  · -- the faces of `Pc` meet `spt Q₀`
    intro x hx
    obtain ⟨p, hp, -, y, hy, rfl⟩ := (hIIIβ Pc hPc).2.2 x hx
    obtain ⟨y', hy', hy'Q⟩ := hsmeet p hp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  · -- `spt ∂Pc ⊆ spt ∂Q₀ ∪ spt ∂(Q₀ - Pc) ⊆ spt ∂Q₀ ∪ spt (Q₀ - Pc)`
    rw [hPcbdeq]
    intro x hx
    rcases (hcc1 P m univ univ Q₀.boundary (Q₀ - Pc).boundary).1 hx with hx | hx
    · exact self_subset_cthickening _ hx
    · exact hdiffspt ((hcc2 P m univ (Q₀ - Pc) Q₀).1 hx)

end GMT.Ch07
