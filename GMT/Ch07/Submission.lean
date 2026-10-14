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

/-- **Simon Ch. 6, proof of Lemma 5.4, step 5** (local finiteness of the unit cubical grid): every
`y` near `x` lies in one of the finitely many closed unit cubes `z + [0, 1]ᴾ`, `z ∈ ℤᴾ`, that
contain `x`.  In one dimension the intervals `[k, k + 1] ∋ t` with `k ∈ {⌊t⌋ − 1, ⌊t⌋}` cover the
neighbourhood `(⌊t⌋, ⌊t⌋ + 1)` of `t` if `t ∉ ℤ`, and `(t − 1, t + 1)` if `t ∈ ℤ`.  `Z` is the set
of corners in the finite product `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`; for `y` in the
intersection of the finitely many coordinate neighbourhoods the corner is chosen coordinate by
coordinate. -/
theorem Submission.dimred_mbl_dtsr_cube_cover : ∀ (P : ℕ) (x : Euclid P), ∃ Z : Finset (Fin P → ℤ), (∀ z ∈ Z, ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1) ∧ ∀ᶠ y : Euclid P in 𝓝 x, ∃ z ∈ Z, ∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1 := by
  intro P x
  classical
  -- step 1: for `t ∈ ℝ`, the intervals `[k, k + 1] ∋ t` with `k ∈ {⌊t⌋ − 1, ⌊t⌋}` cover a
  -- neighbourhood of `t`
  have h1 : ∀ t : ℝ, ∀ᶠ s in 𝓝 t, ∃ k ∈ ({⌊t⌋ - 1, ⌊t⌋} : Finset ℤ),
      ((k : ℝ) ≤ t ∧ t ≤ k + 1) ∧ (k : ℝ) ≤ s ∧ s ≤ k + 1 := by
    intro t
    have hfl : (⌊t⌋ : ℝ) ≤ t := Int.floor_le t
    have hfl' : t < ⌊t⌋ + 1 := Int.lt_floor_add_one t
    rcases hfl.lt_or_eq with hlt | heq
    · -- `t ∉ ℤ`: `[⌊t⌋, ⌊t⌋ + 1]` contains the neighbourhood `(⌊t⌋, ⌊t⌋ + 1)` of `t`
      filter_upwards [Ioo_mem_nhds hlt hfl'] with s hs
      exact ⟨⌊t⌋, by simp, ⟨hfl, hfl'.le⟩, hs.1.le, hs.2.le⟩
    · -- `t ∈ ℤ`: `[t − 1, t] ∪ [t, t + 1]` contains the neighbourhood `(t − 1, t + 1)` of `t`
      filter_upwards [Ioo_mem_nhds (sub_one_lt t) (lt_add_one t)] with s hs
      rcases le_total s t with hst | hts
      · refine ⟨⌊t⌋ - 1, by simp, ?_⟩
        push_cast
        exact ⟨⟨by linarith, by linarith⟩, by linarith [hs.1], by linarith⟩
      · exact ⟨⌊t⌋, by simp, ⟨hfl, hfl'.le⟩, by linarith, by linarith [hs.2]⟩
  -- step 2: `Z` is the set of corners in `∏ᵢ {⌊xᵢ⌋ − 1, ⌊xᵢ⌋}` whose cube contains `x`
  let T : Fin P → Finset ℤ := fun i => {⌊x i⌋ - 1, ⌊x i⌋}
  refine ⟨(Fintype.piFinset T).filter fun z => ∀ i, (z i : ℝ) ≤ x i ∧ x i ≤ z i + 1,
    fun z hz => (Finset.mem_filter.mp hz).2, ?_⟩
  -- step 3: pull the neighbourhoods back along the continuous coordinates `y ↦ yᵢ` and intersect
  -- the finitely many of them
  have h3 : ∀ᶠ y : Euclid P in 𝓝 x, ∀ i, ∃ k ∈ T i,
      ((k : ℝ) ≤ x i ∧ x i ≤ k + 1) ∧ (k : ℝ) ≤ y i ∧ y i ≤ k + 1 :=
    eventually_all.mpr fun i => ((PiLp.continuous_apply 2 _ i).tendsto x).eventually (h1 (x i))
  -- step 4: choose the corner coordinate by coordinate
  filter_upwards [h3] with y hy
  choose k hkT hk using hy
  exact ⟨k, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hkT, fun i => (hk i).1⟩,
    fun i => (hk i).2⟩
/-- **At most `m + 1` coordinates lie near a cube centre** (Simon Ch. 6, Lemma 5.4, closing
Remark: the cone `K_G` through the centre `b + a` of the cube `b + C` lies in `L*(a)`).  Let
`d = dist(x, L*(a))`, where `L*(a) = {w : w_i − a_i ∈ ℤ for at least m + 2 indices i}`.  If
`m + 2` coordinates had `|x_i − b_i − a_i| < d/√(m + 2)`, moving exactly those coordinates to
`b_i + a_i` would give a point `w ∈ L*(a)` with `|x − w|² < (m + 2) · d²/(m + 2) = d²`.  This
contradicts `d ≤ |x − w|`. -/
theorem Submission.dimred_mbl_dtsr_dual_dist_count : ∀ (P m : ℕ) (a x : Euclid P) (b : Fin P → ℤ), (Finset.univ.filter (fun i => |x i - b i - a i| < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} / Real.sqrt (m + 2))).card ≤ m + 1 := by
  intro P m a x b
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- Step 1: otherwise keep exactly `m + 2` coordinates within `d/√(m + 2)` of `b i + a i`
  by_contra hcon
  obtain ⟨s, hsS, hs⟩ := Finset.exists_subset_card_eq (show m + 2 ≤ _ from not_le.mp hcon)
  -- Step 2: moving them to `b i + a i` gives a point of `K_G ⊆ L*(a)`, so `d ≤ |x - w|`
  let w : Euclid P := WithLp.toLp 2 (fun i => if i ∈ s then (b i : ℝ) + a i else x i)
  have hw : ∀ i, w i = if i ∈ s then (b i : ℝ) + a i else x i := fun i => rfl
  have hwL : w ∈ L := ⟨s, hs.ge, fun i hi => ⟨b i, by rw [hw, ite_eq_left hi]; ring⟩⟩
  have hdw : infDist x L ≤ dist x w := infDist_le_dist_of_mem hwL
  -- Step 3: `|x - w|² = ∑_{i ∈ s} (x i - b i - a i)² < (m + 2) · d² / (m + 2) = d²`
  have hm : (0 : ℝ) < m + 2 := by positivity
  have hsum : ∑ i, dist (x i) (w i) ^ 2 = ∑ i ∈ s, (x i - b i - a i) ^ 2 := by
    rw [← Finset.sum_subset (Finset.subset_univ s) fun i _ hi => by rw [hw, ite_eq_right hi, dist_self]; ring]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hw, ite_eq_left hi, Real.dist_eq, sq_abs]
    ring
  have hlt : ∑ i ∈ s, (x i - b i - a i) ^ 2 < ∑ i ∈ s, infDist x L ^ 2 / (m + 2) := by
    refine Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) fun i hi => ?_
    have hi' := (Finset.mem_filter.mp (hsS hi)).2
    rw [← sq_abs, ← Real.sq_sqrt hm.le, ← div_pow]
    exact pow_lt_pow_left₀ hi' (abs_nonneg _) two_ne_zero
  rw [Finset.sum_const, hs, nsmul_eq_mul, Nat.cast_add, Nat.cast_two, mul_div_cancel₀ _ hm.ne'] at hlt
  -- Step 4: `d ≤ |x - w| < d`
  have hxw : dist x w < infDist x L := by
    rw [EuclideanSpace.dist_eq, hsum]
    exact (Real.sqrt_lt (Finset.sum_nonneg fun i _ => sq_nonneg _) infDist_nonneg).mpr hlt
  exact hxw.not_ge hdw
/-- **Simon Ch. 6, Lemma 5.4** (proof: the radial retraction of a face from its centre).  Let
`F = {y : b_k ≤ y_k ≤ b_k + 1 (k ∈ J), y_k = b_k (k ∉ J)}` have centre `a_F` (`b_k + a_k` on `J`,
`b_k` off `J`), and let `N(y) = max_{k ∈ J} max ((y_k − b_k − a_k)/(1 − a_k), (b_k + a_k − y_k)/a_k)`
be the gauge of `F − a_F` at `y − a_F`.  As `1/4 < a_k < 3/4`, `|y_k − b_k − a_k| ≤ N(y)` (`k ∈ J`),
`N ≤ 1` on `F` and `N` is `4`-Lipschitz.  So for `x ∈ F \ {a_F}`, `0 < N(x) ≤ 1`,
`ψ_F(x) = a_F + (x − a_F)/N(x)` lies on `∂F` (a coordinate attaining the maximum goes to `b_i` or
`b_i + 1`), `ψ_F = id` on `∂F` (there `N = 1`), and, with `w = y − a_F`, `|w| ≤ √|J|·N(y)` gives
`|ψ_F(y) − ψ_F(x)| ≤ |y − x|/N(x) + (|w|/N(y))·|N(x) − N(y)|/N(x) ≤ (1 + 4√|J|)/N(x)·|y − x|`. -/
theorem Submission.dimred_mbl_dtsr_face_radial : ∀ (P : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (ψF : Euclid P → Euclid P), (∀ y : Euclid P, ∀ i, ψF y i = if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / J.sup' hJ (fun k => max ((y k - b k - a k) / (1 - a k)) ((b k + a k - y k) / a k)) else y i) → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → (∃ i ∈ J, x i ≠ b i + a i) → (∀ k ∈ J, |x k - b k - a k| ≤ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))) ∧ 0 < J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ∧ J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) ≤ 1 ∧ (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧ (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧ ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧ ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) → (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) * dist y x := by
  intro P a ha b J hJ ψF hψ x hx hne
  -- the gauge `N(u)` of `F − a_F` at `u − a_F`
  let N : Euclid P → ℝ := fun u =>
    J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
  have hψN : ∀ y : Euclid P, ∀ i, ψF y i =
      if i ∈ J then (b i : ℝ) + a i + (y i - b i - a i) / N y else y i := hψ
  -- `1/4 < a_k < 3/4`
  have ha' : ∀ k, 1 / 4 < a k ∧ a k < 3 / 4 := fun k => by
    obtain ⟨h1, h2⟩ := abs_lt.mp (ha k)
    constructor <;> linarith
  -- each term of the gauge is at most `N(u)` and dominates `|u_k − b_k − a_k|`
  have hterm : ∀ u : Euclid P, ∀ k ∈ J,
      max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k) ≤ N u := fun u k hk =>
    Finset.le_sup' (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) hk
  have habs : ∀ u : Euclid P, ∀ k ∈ J, |u k - b k - a k| ≤ N u := by
    intro u k hk
    refine le_trans ?_ (hterm u k hk)
    obtain ⟨h1, h2⟩ := ha' k
    rcases le_or_gt 0 (u k - b k - a k) with ht | ht
    · rw [abs_of_nonneg ht]
      refine le_max_of_le_left ?_
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    · rw [abs_of_neg ht]
      refine le_max_of_le_right ?_
      rw [le_div_iff₀ (by linarith)]
      nlinarith
  -- `N ≤ 1` on `F`, and `N > 0` on `F` off the centre `a_F`
  have hle : ∀ u : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧
      (i ∉ J → u i = b i)) → N u ≤ 1 := by
    intro u hu
    refine Finset.sup'_le hJ _ fun k hk => ?_
    obtain ⟨h1, h2⟩ := ha' k
    obtain ⟨hu1, hu2⟩ := (hu k).1 hk
    refine max_le ?_ ?_
    · rw [div_le_one (by linarith)]; linarith
    · rw [div_le_one (by linarith)]; linarith
  have hpos : ∀ u : Euclid P, (∃ i ∈ J, u i ≠ b i + a i) → 0 < N u := by
    rintro u ⟨i, hi, hui⟩
    have h0 : u i - b i - a i ≠ 0 := fun h => hui (by linarith)
    exact (abs_pos.mpr h0).trans_le (habs u i hi)
  -- `N` is `4`-Lipschitz, as `1/(1 − a_k) < 4` and `1/a_k < 4`
  have hlip : ∀ u v : Euclid P, N u ≤ N v + 4 * dist u v := by
    intro u v
    refine Finset.sup'_le hJ _ fun k hk => ?_
    obtain ⟨h1, h2⟩ := ha' k
    have hd : |u k - v k| ≤ dist u v := by
      simpa only [Real.dist_eq] using PiLp.dist_apply_le u v k
    have hd0 : 0 ≤ dist u v := dist_nonneg
    refine max_le ?_ ?_
    · have h : (u k - b k - a k) / (1 - a k) - (v k - b k - a k) / (1 - a k) ≤ 4 * dist u v := by
        rw [← sub_div, div_le_iff₀ (by linarith)]
        nlinarith [le_abs_self (u k - v k)]
      linarith [(le_max_left _ _).trans (hterm v k hk)]
    · have h : (b k + a k - u k) / a k - (b k + a k - v k) / a k ≤ 4 * dist u v := by
        rw [← sub_div, div_le_iff₀ (by linarith)]
        nlinarith [neg_abs_le (u k - v k)]
      linarith [(le_max_right _ _).trans (hterm v k hk)]
  have hNx := hpos x hne
  show (∀ k ∈ J, |x k - b k - a k| ≤ N x) ∧ 0 < N x ∧ N x ≤ 1 ∧
    (∀ i, (i ∈ J → (b i : ℝ) ≤ ψF x i ∧ ψF x i ≤ b i + 1) ∧ (i ∉ J → ψF x i = b i)) ∧
    (∃ i ∈ J, ψF x i = b i ∨ ψF x i = b i + 1) ∧
    ((∃ i ∈ J, x i = b i ∨ x i = b i + 1) → ψF x = x) ∧
    ∀ y : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ y i ∧ y i ≤ b i + 1) ∧ (i ∉ J → y i = b i)) →
      (∃ i ∈ J, y i ≠ b i + a i) → dist (ψF y) (ψF x) ≤ (1 + 4 * Real.sqrt J.card) / N x * dist y x
  refine ⟨habs x, hNx, hle x hx, fun i => ⟨fun hi => ?_, fun hi => ?_⟩, ?_, ?_, ?_⟩
  · -- `ψ_F(x) ∈ F`: `−a_i ≤ (x_i − b_i − a_i)/N(x) ≤ 1 − a_i`
    obtain ⟨h1, h2⟩ := ha' i
    have hp := (le_max_left _ _).trans (hterm x i hi)
    have hq := (le_max_right _ _).trans (hterm x i hi)
    rw [div_le_iff₀ (by linarith)] at hp hq
    have hlo : -a i ≤ (x i - b i - a i) / N x := by rw [le_div_iff₀ hNx]; linarith
    have hhi : (x i - b i - a i) / N x ≤ 1 - a i := by rw [div_le_iff₀ hNx]; linarith
    rw [hψN x i, ite_eq_left hi]
    constructor <;> linarith
  · rw [hψN x i, ite_eq_right hi]
    exact (hx i).2 hi
  · -- a coordinate attaining the maximum is sent to `b_i` or `b_i + 1`
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hJ
      (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k))
    change N x = max ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) at heq
    obtain ⟨h1, h2⟩ := ha' i
    refine ⟨i, hi, ?_⟩
    rw [hψN x i, ite_eq_left hi]
    rcases max_choice ((x i - b i - a i) / (1 - a i)) ((b i + a i - x i) / a i) with hm | hm
    · rw [hm, eq_div_iff (by linarith)] at heq
      have h : (x i - b i - a i) / N x = 1 - a i := by rw [div_eq_iff hNx.ne']; linarith
      right
      rw [h]
      ring
    · rw [hm, eq_div_iff (by linarith)] at heq
      have h : (x i - b i - a i) / N x = -a i := by rw [div_eq_iff hNx.ne']; linarith
      left
      rw [h]
      ring
  · -- on `∂F`, `N(x) = 1` and `ψ_F(x) = x`
    rintro ⟨i, hi, hbi⟩
    obtain ⟨h1, h2⟩ := ha' i
    have hN1 : N x = 1 := by
      refine le_antisymm (hle x hx) ?_
      rcases hbi with h | h
      · have h' : (b i + a i - x i) / a i = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]
          ring
        exact h'.symm.le.trans ((le_max_right _ _).trans (hterm x i hi))
      · have h' : (x i - b i - a i) / (1 - a i) = 1 := by
          rw [h, div_eq_one_iff_eq (by linarith)]
          ring
        exact h'.symm.le.trans ((le_max_left _ _).trans (hterm x i hi))
    ext k
    rw [hψN x k, hN1]
    split_ifs <;> ring
  · -- the radial estimate
    intro y hy hney
    have hNy := hpos y hney
    -- `w = y − a_F` is supported on `J`, so `|w| ≤ √|J|·N(y)`
    let w : Euclid P := WithLp.toLp 2 fun k => if k ∈ J then y k - b k - a k else 0
    have hwk : ∀ k, w k = if k ∈ J then y k - b k - a k else 0 := fun k => rfl
    have hw : ‖w‖ ≤ Real.sqrt J.card * N y := by
      have hsum : ∑ k, ‖w k‖ ^ 2 ≤ J.card * N y ^ 2 :=
        calc ∑ k, ‖w k‖ ^ 2 = ∑ k ∈ J, ‖w k‖ ^ 2 :=
              (Finset.sum_subset (Finset.subset_univ J) fun k _ hk => by
                rw [hwk k, ite_eq_right hk, norm_zero]; ring).symm
          _ ≤ ∑ _k ∈ J, N y ^ 2 := Finset.sum_le_sum fun k hk => by
              rw [hwk k, ite_eq_left hk, Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (habs y k hk) 2
          _ = J.card * N y ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      rw [EuclideanSpace.norm_eq]
      calc Real.sqrt (∑ k, ‖w k‖ ^ 2) ≤ Real.sqrt (J.card * N y ^ 2) := Real.sqrt_le_sqrt hsum
        _ = Real.sqrt J.card * N y := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hNy.le]
    -- `ψ_F(y) − ψ_F(x) = (y − x)/N(x) + (1/N(y) − 1/N(x))·w`
    have hdecomp : ψF y - ψF x = (1 / N x) • (y - x) + (1 / N y - 1 / N x) • w := by
      ext k
      rw [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, PiLp.sub_apply,
        hψN x k, hψN y k, hwk k, smul_eq_mul, smul_eq_mul]
      by_cases hk : k ∈ J
      · rw [ite_eq_left hk, ite_eq_left hk, ite_eq_left hk]
        ring
      · rw [ite_eq_right hk, ite_eq_right hk, ite_eq_right hk, (hx k).2 hk, (hy k).2 hk]
        ring
    have hlipxy : |N x - N y| ≤ 4 * dist y x := by
      rw [abs_le]
      constructor <;> linarith [hlip x y, hlip y x, dist_comm x y]
    have hfrac : |1 / N y - 1 / N x| * N y = |N x - N y| / N x := by
      rw [div_sub_div _ _ hNy.ne' hNx.ne', abs_div, abs_of_pos (mul_pos hNy hNx)]
      field_simp
    rw [dist_eq_norm, hdecomp]
    calc ‖(1 / N x) • (y - x) + (1 / N y - 1 / N x) • w‖
        ≤ ‖(1 / N x) • (y - x)‖ + ‖(1 / N y - 1 / N x) • w‖ := norm_add_le _ _
      _ = 1 / N x * dist y x + |1 / N y - 1 / N x| * ‖w‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (one_div_pos.mpr hNx), dist_eq_norm]
      _ ≤ 1 / N x * dist y x + |1 / N y - 1 / N x| * (Real.sqrt J.card * N y) := by gcongr
      _ = 1 / N x * dist y x + |N x - N y| / N x * Real.sqrt J.card := by rw [← hfrac]; ring
      _ ≤ 1 / N x * dist y x + 4 * dist y x / N x * Real.sqrt J.card := by gcongr
      _ = (1 + 4 * Real.sqrt J.card) / N x * dist y x := by ring

/-- **Simon Ch. 6, proof of Lemma 5.4: the composite of the face retractions** (chapter-06.txt,
lines 1508–1546).  For `a` with `|aᵢ − 1/2| < 1/4` there are maps `Ψ_k : ℝᴾ → ℝᴾ` with
`Ψ_{m+1} = id` and `Ψ_j(x) = Ψ_{j−1}(ψ_F(x))` for every `j`-face `F = F(b, J)`, `m + 2 ≤ j ≤ P`,
and `x ∈ F`, where `ψ_F` is the radial retraction of `F` from its centre `a_F` onto `∂F` (Simon's
`ψ^{(j)} := ⋃ ψ_F` and `ψ^{(m+2)} ∘ ⋯ ∘ ψ^{(j)}`; at `x = a_F` the gauge vanishes and, with
`t / 0 = 0`, `ψ_F(a_F) = a_F`).  Two distinct `j`-faces through `u` meet where `u` has a coordinate
`uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, in each of them, and there both retractions are the identity
(`dimred_mbl_dtsr_face_radial`); so the step map `φ_j` retracting along any `j`-face through `u`
is well defined, and `Ψ_k := Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`. -/
theorem Submission.dimred_mbl_dtsr_face_retraction_family : ∀ (P m : ℕ) (a : Euclid P), (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) ∧ ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y := by
  classical
  intro P m a ha
  -- `u ∈ F(b, J)`
  let InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop := fun b J u =>
    ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i)
  -- the radial retraction `R_{b,J}` of `F(b, J)` from its centre onto `∂F(b, J)` (`id` if `J = ∅`)
  let R : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Euclid P := fun b J u =>
    if hJ : J.Nonempty then
      WithLp.toLp 2 fun i => if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i
    else u
  have hR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (u : Euclid P) (i : Fin P),
      R b J u i = if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) /
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k))
        else u i := by
    intro b J hJ u i
    simp only [R, dite_eq_left hJ, PiLp.toLp_apply]
  -- Step 1: if two distinct faces of the same dimension contain `u`, then `u` has a coordinate
  -- `uᵢ ∈ {bᵢ, bᵢ + 1}`, `i ∈ J`, on the boundary of the first one
  have hbd : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → (b, J) ≠ (b', J') → ∃ i ∈ J, u i = b i ∨ u i = b i + 1 := by
    intro b b' J J' u hcard hu hu' hne
    by_cases hJJ : J = J'
    · -- same free coordinates: `bᵢ ≠ b'ᵢ` for some `i ∈ J` and `uᵢ ∈ [bᵢ, bᵢ + 1] ∩ [b'ᵢ, b'ᵢ + 1]`
      subst hJJ
      obtain ⟨i, hi⟩ := Function.ne_iff.mp fun h : b = b' => hne (by rw [h])
      by_cases hiJ : i ∈ J
      · refine ⟨i, hiJ, ?_⟩
        obtain ⟨h1, h2⟩ := (hu i).1 hiJ
        obtain ⟨h3, h4⟩ := (hu' i).1 hiJ
        rcases lt_or_gt_of_ne hi with hlt | hlt
        · have : (b i : ℝ) + 1 ≤ b' i := by exact_mod_cast hlt
          right; linarith
        · have : (b' i : ℝ) + 1 ≤ b i := by exact_mod_cast hlt
          left; linarith
      · exact absurd (Int.cast_injective (((hu i).2 hiJ).symm.trans ((hu' i).2 hiJ))) hi
    · -- `J ⊄ J'`: for `i ∈ J \ J'` the coordinate `uᵢ = b'ᵢ ∈ [bᵢ, bᵢ + 1]` is an integer
      obtain ⟨i, hiJ, hiJ'⟩ := Finset.not_subset.mp fun hsub =>
        hJJ (Finset.eq_of_subset_of_card_le hsub hcard.ge)
      refine ⟨i, hiJ, ?_⟩
      obtain ⟨h1, h2⟩ := (hu i).1 hiJ
      rw [(hu' i).2 hiJ'] at h1 h2 ⊢
      have h1' : b i ≤ b' i := Int.cast_le.mp h1
      have h2' : b' i ≤ b i + 1 := by
        rw [← Int.cast_le (R := ℝ), Int.cast_add, Int.cast_one]
        exact h2
      rcases h1'.eq_or_lt with h | h
      · left; rw [← h]
      · right; rw [le_antisymm h2' (Int.add_one_le_of_lt h), Int.cast_add, Int.cast_one]
  -- Step 2: at such points `R_{b,J}` is the identity (`dimred_mbl_dtsr_face_radial`;
  -- `1/4 < aᵢ < 3/4` keeps `u` off the centre), so all faces of the same dimension through `u`
  -- agree
  have hfix : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P), InF b J u →
      (∃ i ∈ J, u i = b i ∨ u i = b i + 1) → R b J u = u := by
    rintro b J u hu ⟨i, hiJ, hbi⟩
    have hJ : J.Nonempty := ⟨i, hiJ⟩
    have hai := abs_lt.mp (ha i)
    have hne : ∃ i ∈ J, u i ≠ b i + a i := ⟨i, hiJ, by
      rcases hbi with h | h <;> rw [h] <;> intro h' <;> linarith [hai.1, hai.2]⟩
    exact (Submission.dimred_mbl_dtsr_face_radial P a ha b J hJ (R b J) (hR b J hJ) u hu
      hne).2.2.2.2.2.1 ⟨i, hiJ, hbi⟩
  have hcons : ∀ (b b' : Fin P → ℤ) (J J' : Finset (Fin P)) (u : Euclid P), J.card = J'.card →
      InF b J u → InF b' J' u → R b J u = R b' J' u := by
    intro b b' J J' u hcard hu hu'
    by_cases h : (b, J) = (b', J')
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    · rw [hfix b J u hu (hbd b b' J J' u hcard hu hu' h),
        hfix b' J' u hu' (hbd b' b J' J u hcard.symm hu' hu (Ne.symm h))]
  -- Step 3: the step map `φ_j` applies the retraction of a chosen `j`-face through `u`
  let φ : ℕ → Euclid P → Euclid P := fun j u =>
    if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = j ∧ InF p.1 p.2 u then
      R h.choose.1 h.choose.2 u
    else u
  -- Step 4: `Ψ_k = id` for `k ≤ m + 1` and `Ψ_k = Ψ_{k−1} ∘ φ_k` for `k ≥ m + 2`
  let Ψ : ℕ → Euclid P → Euclid P := fun k =>
    Nat.rec (motive := fun _ => Euclid P → Euclid P) id
      (fun k Ψk => if k + 1 ≤ m + 1 then id else Ψk ∘ φ (k + 1)) k
  refine ⟨Ψ, fun x => ?_, ?_⟩
  · show (if m + 1 ≤ m + 1 then id else Ψ m ∘ φ (m + 1)) x = x
    rw [ite_eq_left le_rfl]
    rfl
  -- Step 5: for `x ∈ F(b, J)` the chosen face gives `φ_j(x) = R_{b,J}(x) = y`
  · intro j hj _ b J hJ hcard x hx y hy
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr ((Nat.zero_lt_succ _).trans_le hj)
    have hk : ¬k + 1 ≤ m + 1 := Nat.not_le.mpr hj
    show (if k + 1 ≤ m + 1 then id else Ψ k ∘ φ (k + 1)) x = Ψ (k + 1 - 1) y
    rw [ite_eq_right hk, Nat.add_sub_cancel]
    have hex : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x :=
      ⟨(b, J), hcard, hx⟩
    show Ψ k (if h : ∃ p : (Fin P → ℤ) × Finset (Fin P), p.2.card = k + 1 ∧ InF p.1 p.2 x then
      R h.choose.1 h.choose.2 x else x) = Ψ k y
    rw [dite_eq_left hex, hcons _ b _ J x (hex.choose_spec.1.trans hcard.symm) hex.choose_spec.2 hx]
    congr 1
    ext i
    rw [hR b J hJ x i, hy i]
/-- **Face-by-face Lipschitz bound for the skeleton retraction** (Simon Ch. 6, Lemma 5.4, proof
of (3), chapter-06.txt lines 1563–1640: induction over the faces, radial retractions and the chain
rule).  `F = F(b, J)` is the face `{b_i ≤ x_i ≤ b_i + 1 (i ∈ J), x_i = b_i (i ∉ J)}`, `N = N_{b,J}`
its gauge about the centre `a_F`, and `ψ_F(u) = a_F + (u − a_F)/N(u)` on `J`, `u` off `J`; the
recursion says `Ψ_j = Ψ_{j−1} ∘ ψ_F` on `F`.  With `K = 1 + 4√P` and `c = K^P`, induction on
`j ∈ [m + 2, P]` shows: if `x ∈ F` and at most `m + 1` indices `i ∈ J` have
`|x_i − b_i − a_i| < ρ` (the coordinate form of "`x` is `ρ`-far from the planes through `a_F`
fixing `m + 2` coordinates of `J`"), then `Ψ_j(x) ∈ F`, `P − m − 1` coordinates of `Ψ_j(x)` are
integers, and `|Ψ_j(y) − Ψ_j(x)| ≤ (K^{j−m−1}/ρ)|y − x|` for `y ∈ F` near `x`.  The counting
condition gives `N(x) ≥ ρ`, and it holds at `y` with radius `ρ/2` if `|y − x| < ρ/2`.  For
`j = m + 2`, `Ψ_j = ψ_F` on `F` and `Submission.dimred_mbl_dtsr_face_radial` gives the constant
`(1 + 4√j)/N(x)`.  For `j > m + 2`, `y₀ = ψ_F(x)` lies on the `(j − 1)`-faces
`F(b[i ↦ β], J ∖ {i})` with `y₀_i = β ∈ {b_i, b_i + 1}`; as `y₀ − a_F = (x − a_F)/N(x)` on `J`,
the counting condition holds at `y₀` with radius `ρ/N(x)` (the similarity after (7)), and
`ψ_F(y)` lies on one of these faces for `y` near `x`.  The chain rule cancels `N(x)`, so the bound `|y − a| ≥ 3/4` behind (6)
(an erratum for `1/4`) is not needed. -/
theorem Submission.dimred_mbl_dtsr_face_count_induction : ∀ (P m : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∀ Ψ : ℕ → Euclid P → Euclid P, (∀ x, Ψ (m + 1) x = x) → (∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ y : Euclid P, (∀ i, y i = if i ∈ J then (b i : ℝ) + a i + (x i - b i - a i) / J.sup' hJ (fun k => max ((x k - b k - a k) / (1 - a k)) ((b k + a k - x k) / a k)) else x i) → Ψ j x = Ψ (j - 1) y) → ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j → ∀ x : Euclid P, (∀ i, (i ∈ J → (b i : ℝ) ≤ x i ∧ x i ≤ b i + 1) ∧ (i ∉ J → x i = b i)) → ∀ ρ : ℝ, 0 < ρ → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 → (∀ i, (i ∈ J → (b i : ℝ) ≤ Ψ j x i ∧ Ψ j x i ≤ b i + 1) ∧ (i ∉ J → Ψ j x i = b i)) ∧ (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧ ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ J → (b i : ℝ) ≤ w i ∧ w i ≤ b i + 1) ∧ (i ∉ J → w i = b i)}] x, dist (Ψ j y) (Ψ j x) ≤ c / ρ * dist y x := by
  intro P m
  -- Step 0: `K = 1 + 4√P ≥ 1` and `c = K ^ P`
  have hK1 : (1 : ℝ) ≤ 1 + 4 * Real.sqrt P := by
    have := Real.sqrt_nonneg (P : ℝ); linarith
  refine ⟨(1 + 4 * Real.sqrt P) ^ P, by positivity, ?_⟩
  intro a ha Ψ hΨ0 hrec
  -- the face `F(b, J)`, the gauge `N_{b,J}` and the radial map `ψ_{b,J}`
  obtain ⟨InF, hInF⟩ : ∃ InF : (Fin P → ℤ) → Finset (Fin P) → Euclid P → Prop, ∀ b J u,
      InF b J u ↔ ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i) :=
    ⟨fun b J u => ∀ i, (i ∈ J → (b i : ℝ) ≤ u i ∧ u i ≤ b i + 1) ∧ (i ∉ J → u i = b i),
      fun _ _ _ => Iff.rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin P → ℤ) → (J : Finset (Fin P)) → J.Nonempty → Euclid P → ℝ,
      ∀ b J hJ u, N b J hJ u =
        J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)) :=
    ⟨fun b J hJ u =>
      J.sup' hJ (fun k => max ((u k - b k - a k) / (1 - a k)) ((b k + a k - u k) / a k)),
      fun _ _ _ _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : (Fin P → ℤ) → (J : Finset (Fin P)) → J.Nonempty → Euclid P → Euclid P,
      ∀ b J hJ u i, R b J hJ u i =
        if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i :=
    ⟨fun b J hJ u => WithLp.toLp 2 fun i =>
      if i ∈ J then (b i : ℝ) + a i + (u i - b i - a i) / N b J hJ u else u i,
      fun _ _ _ _ _ => rfl⟩
  -- Step 1(c), the recursion: `Ψ_j = Ψ_{j−1} ∘ ψ_{b,J}` on `F(b, J)`
  have hrec' : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P))
      (hJ : J.Nonempty), J.card = j → ∀ u, InF b J u → Ψ j u = Ψ (j - 1) (R b J hJ u) :=
    fun j hj hjP b J hJ hc u hu =>
      hrec j hj hjP b J hJ hc u ((hInF b J u).1 hu) (R b J hJ u) (fun i => by rw [hR, hN])
  -- Step 1(d), face_radial for `ψ_{b,J}`
  have FR : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (hJ : J.Nonempty) (x : Euclid P), InF b J x →
      (∃ i ∈ J, x i ≠ b i + a i) →
      (∀ k ∈ J, |x k - b k - a k| ≤ N b J hJ x) ∧ 0 < N b J hJ x ∧ InF b J (R b J hJ x) ∧
      (∃ i ∈ J, R b J hJ x i = b i ∨ R b J hJ x i = b i + 1) ∧
      ∀ y, InF b J y → (∃ i ∈ J, y i ≠ b i + a i) →
        dist (R b J hJ y) (R b J hJ x) ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := by
    intro b J hJ x hx hne
    obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := Submission.dimred_mbl_dtsr_face_radial P a ha b J hJ
      (R b J hJ) (fun y i => by rw [hR, hN]) x ((hInF b J x).1 hx) hne
    rw [← hN b J hJ x] at h1 h2 h7
    exact ⟨h1, h2, (hInF b J _).2 h4, h5, fun y hy hney => h7 y ((hInF b J y).1 hy) hney⟩
  -- Step 1(a), the counting condition leaves a coordinate with `|u_i − b_i − a_i| ≥ ρ`
  have hfar : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), m + 2 ≤ J.card → ∀ (u : Euclid P) (ρ : ℝ),
      (J.filter (fun i => |u i - b i - a i| < ρ)).card ≤ m + 1 →
      ∃ i ∈ J, ρ ≤ |u i - b i - a i| := by
    intro b J hJc u ρ hcount
    by_contra h
    have h' : ∀ i ∈ J, |u i - b i - a i| < ρ := fun i hi => not_le.mp fun hle => h ⟨i, hi, hle⟩
    rw [Finset.filter_true_of_mem h'] at hcount
    omega
  have hcentre : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (u : Euclid P) (ρ : ℝ), 0 < ρ →
      (∃ i ∈ J, ρ ≤ |u i - b i - a i|) → ∃ i ∈ J, u i ≠ b i + a i := by
    rintro b J u ρ hρ ⟨i, hi, hf⟩
    refine ⟨i, hi, fun he => ?_⟩
    have h0 : u i - b i - a i = 0 := by rw [he]; ring
    rw [h0, abs_zero] at hf
    linarith
  -- Step 1(b), the counting condition passes to `y` with `|y − x| < ρ/2`, with radius `ρ/2`
  have hnear : ∀ (b : Fin P → ℤ) (J : Finset (Fin P)) (x y : Euclid P) (ρ : ℝ),
      dist y x < ρ / 2 → (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      (J.filter (fun i => |y i - b i - a i| < ρ / 2)).card ≤ m + 1 := by
    intro b J x y ρ hyx hcount
    refine le_trans (Finset.card_le_card fun i hi => ?_) hcount
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, ?_⟩
    have hd : |x i - y i| ≤ dist y x := by
      rw [dist_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le x y i
    calc |x i - b i - a i| = |(x i - y i) + (y i - b i - a i)| := by ring_nf
      _ ≤ |x i - y i| + |y i - b i - a i| := abs_add_le _ _
      _ < ρ := by linarith [hi.2]
  -- Claim(j), by induction on `j ≥ m + 2`
  have hclaim : ∀ j, m + 2 ≤ j → j ≤ P → ∀ (b : Fin P → ℤ) (J : Finset (Fin P)), J.card = j →
      ∀ x : Euclid P, InF b J x → ∀ ρ : ℝ, 0 < ρ →
      (J.filter (fun i => |x i - b i - a i| < ρ)).card ≤ m + 1 →
      InF b J (Ψ j x) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j x i = z) ∧
      ∃ δ > 0, ∀ y : Euclid P, InF b J y → dist y x < δ →
        dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      -- Step 2: `j = m + 2`, where `Ψ_j = ψ_F` on `F`
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hΨ : ∀ u, InF b J u → Ψ (m + 2) u = R b J hJ u := fun u hu => by
        rw [hrec' (m + 2) le_rfl hP b J hJ hcard u hu, show m + 2 - 1 = m + 1 by omega, hΨ0]
      obtain ⟨i, hi, hfx⟩ := hfar b J (by omega) x ρ hcount
      obtain ⟨F1, -, F3, F4, F6⟩ := FR b J hJ x hx (hcentre b J x ρ hρ ⟨i, hi, hfx⟩)
      have hNρ : ρ ≤ N b J hJ x := hfx.trans (F1 i hi)
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨ x hx]; exact F3
      · -- (B): the coordinates off `J` and one boundary coordinate in `J`
        obtain ⟨i₀, hi₀, hbd⟩ := F4
        have F3' := (hInF b J _).1 F3
        refine ⟨insert i₀ (Finset.univ \ J), ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hi₀]),
            Finset.card_sdiff_of_subset (Finset.subset_univ J), Finset.card_univ,
            Fintype.card_fin, hcard]
          omega
        · intro k hk
          rw [hΨ x hx]
          rcases Finset.mem_insert.mp hk with rfl | hk'
          · rcases hbd with h | h
            · exact ⟨b k, h⟩
            · exact ⟨b k + 1, by rw [h, Int.cast_add, Int.cast_one]⟩
          · exact ⟨b k, (F3' k).2 (Finset.mem_sdiff.mp hk').2⟩
      · -- (C) with `δ = ρ/2` and constant `(1 + 4√(m + 2))/N(x) ≤ K/ρ`
        refine ⟨ρ / 2, by positivity, fun y hy hyx => ?_⟩
        have hney := hcentre b J y (ρ / 2) (by positivity)
          (hfar b J (by omega) y (ρ / 2) (hnear b J x y ρ hyx hcount))
        rw [hΨ y hy, hΨ x hx]
        have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
          Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
        calc dist (R b J hJ y) (R b J hJ x)
            ≤ (1 + 4 * Real.sqrt J.card) / N b J hJ x * dist y x := F6 y hy hney
          _ ≤ (1 + 4 * Real.sqrt P) ^ (m + 2 - m - 1) / ρ * dist y x := by
            rw [show m + 2 - m - 1 = 1 by omega, pow_one]
            apply mul_le_mul_of_nonneg_right _ dist_nonneg
            exact div_le_div₀ (by positivity) (by linarith) hρ hNρ
    | succ j hj ih =>
      -- Step 3: `m + 3 ≤ j + 1 ≤ P`, assuming Claim(j)
      intro hP b J hcard x hx ρ hρ hcount
      have hJ : J.Nonempty := Finset.card_pos.mp (by omega)
      have hrecj : ∀ u, InF b J u → Ψ (j + 1) u = Ψ j (R b J hJ u) := fun u hu => by
        rw [hrec' (j + 1) (by omega) hP b J hJ hcard u hu, show j + 1 - 1 = j by omega]
      obtain ⟨-, Fpos, F3, F4, F6⟩ :=
        FR b J hJ x hx (hcentre b J x ρ hρ (hfar b J (by omega) x ρ hcount))
      -- `y₀ = ψ_F(x)` satisfies `y₀ − a_F = (x − a_F)/N(x)` on `J`
      have hy₀k : ∀ k ∈ J, R b J hJ x k - b k - a k = (x k - b k - a k) / N b J hJ x := by
        intro k hk
        rw [hR, ite_eq_left hk]; ring
      have hΨx : Ψ (j + 1) x = Ψ j (R b J hJ x) := hrecj x hx
      obtain ⟨Nx, hNx⟩ : ∃ t, N b J hJ x = t := ⟨_, rfl⟩
      obtain ⟨y₀, hy₀⟩ : ∃ y, R b J hJ x = y := ⟨_, rfl⟩
      rw [hNx] at Fpos hy₀k F6
      rw [hy₀] at F3 F4 hy₀k hΨx F6
      have hsq : Real.sqrt J.card ≤ Real.sqrt P :=
        Real.sqrt_le_sqrt (by rw [hcard]; exact_mod_cast hP)
      -- (i) the faces `G_{i,β} = F(b[i ↦ β], J ∖ {i})` lie in `F` and contain the points of `F`
      -- with `i`-th coordinate `β`
      have hGsub : ∀ i' ∈ J, ∀ β : ℤ, b i' ≤ β → β ≤ b i' + 1 → ∀ u,
          InF (Function.update b i' β) (J.erase i') u → InF b J u := by
        intro i' hi' β hβ1 hβ2 u hu
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          have hu2 := (hu k).2 (Finset.notMem_erase k J)
          rw [Function.update_self] at hu2
          refine ⟨fun _ => ⟨?_, ?_⟩, fun h => absurd hi' h⟩
          · rw [hu2]; exact_mod_cast hβ1
          · have h2 : (β : ℝ) ≤ ((b k + 1 : ℤ) : ℝ) := Int.cast_le.mpr hβ2
            rw [hu2]; push_cast at h2; exact h2
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          obtain ⟨h1, h2⟩ := hu k
          rw [hupd, hmem] at h1 h2
          exact ⟨h1, h2⟩
      have hGmem : ∀ i' ∈ J, ∀ u, InF b J u → ∀ β : ℤ, u i' = β →
          InF (Function.update b i' β) (J.erase i') u := by
        intro i' hi' u hu β hβ
        rw [hInF] at hu ⊢
        intro k
        by_cases hk : k = i'
        · subst hk
          refine ⟨fun h => absurd h (Finset.notMem_erase k J), fun _ => ?_⟩
          rw [Function.update_self]; exact hβ
        · have hupd : Function.update b i' β k = b k := Function.update_of_ne hk _ _
          have hmem : k ∈ J.erase i' ↔ k ∈ J := by simp [Finset.mem_erase, hk]
          rw [hupd, hmem]
          exact hu k
      -- (ii) scaling: the counting condition holds at `y₀` on `G_{i,β}` with radius `ρ/N(x)`
      have hρN : 0 < ρ / Nx := div_pos hρ Fpos
      have hGcount : ∀ i' ∈ J, ∀ β : ℤ,
          ((J.erase i').filter (fun k => |y₀ k - Function.update b i' β k - a k| < ρ / Nx)).card
            ≤ m + 1 := by
        intro i' hi' β
        refine le_trans (Finset.card_le_card fun k hk => ?_) hcount
        rw [Finset.mem_filter] at hk ⊢
        obtain ⟨hki, hkJ⟩ := Finset.mem_erase.mp hk.1
        refine ⟨hkJ, ?_⟩
        have h' := hk.2
        rw [Function.update_of_ne hki, hy₀k k hkJ, abs_div, abs_of_pos Fpos] at h'
        exact (div_lt_div_iff_of_pos_right Fpos).mp h'
      have hGcard : ∀ i' ∈ J, (J.erase i').card = j := by
        intro i' hi'
        rw [Finset.card_erase_of_mem hi']; omega
      -- (iii) Claim(j) at `y₀` on every face `G_{i,β}` through `y₀`
      have hIH : ∀ i' ∈ J, ∀ β : ℤ, y₀ i' = β →
          InF (Function.update b i' β) (J.erase i') (Ψ j y₀) ∧
          (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ j y₀ i = z) ∧
          ∃ δ > 0, ∀ y' : Euclid P, InF (Function.update b i' β) (J.erase i') y' →
            dist y' y₀ < δ →
            dist (Ψ j y') (Ψ j y₀) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀ :=
        fun i' hi' β hβ => ih (by omega) (Function.update b i' β) (J.erase i') (hGcard i' hi') y₀
          (hGmem i' hi' y₀ F3 β hβ) (ρ / Nx) hρN (hGcount i' hi' β)
      -- (A) and (B) from a face through `y₀`
      obtain ⟨i₁, hi₁, hbd₁⟩ := F4
      obtain ⟨β₁, hβ₁a, hβ₁b, hβ₁e⟩ : ∃ β : ℤ, b i₁ ≤ β ∧ β ≤ b i₁ + 1 ∧ y₀ i₁ = β := by
        rcases hbd₁ with h | h
        · exact ⟨b i₁, le_refl _, by omega, h⟩
        · exact ⟨b i₁ + 1, by omega, le_refl _, by rw [h, Int.cast_add, Int.cast_one]⟩
      obtain ⟨hA₁, hB₁, -⟩ := hIH i₁ hi₁ β₁ hβ₁e
      refine ⟨?_, ?_, ?_⟩
      · rw [hΨx]; exact hGsub i₁ hi₁ β₁ hβ₁a hβ₁b _ hA₁
      · rw [hΨx]; exact hB₁
      -- (iv) near `y₀`: the bounds of (iii), and `y'_i ≠ β` whenever `y₀_i ≠ β`
      have hev : ∀ᶠ y' in 𝓝 y₀, ∀ i' ∈ J, ∀ e : Bool,
          (y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            InF (Function.update b i' (if e then b i' + 1 else b i')) (J.erase i') y' →
            dist (Ψ j y') (Ψ j y₀) ≤
              (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist y' y₀) ∧
          (y₀ i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ) →
            y' i' ≠ ((if e then b i' + 1 else b i' : ℤ) : ℝ)) := by
        rw [Filter.eventually_all_finset]
        intro i' hi'
        rw [Filter.eventually_all]
        intro e
        by_cases hβ : y₀ i' = ((if e then b i' + 1 else b i' : ℤ) : ℝ)
        · obtain ⟨-, -, δ', hδ', hbd⟩ := hIH i' hi' _ hβ
          filter_upwards [Metric.ball_mem_nhds y₀ hδ'] with y' hy'
          exact ⟨fun _ hG => hbd y' hG (Metric.mem_ball.mp hy'), fun h => absurd hβ h⟩
        · have hpos : 0 < |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| :=
            abs_pos.mpr (sub_ne_zero.mpr hβ)
          filter_upwards [Metric.ball_mem_nhds y₀ hpos] with y' hy'
          refine ⟨fun h => absurd h hβ, fun _ heq => ?_⟩
          have h1 : |y₀ i' - ((if e then b i' + 1 else b i' : ℤ) : ℝ)| ≤ dist y' y₀ := by
            rw [← heq, abs_sub_comm, ← Real.dist_eq]; exact PiLp.dist_apply_le _ _ _
          exact absurd (Metric.mem_ball.mp hy') (not_lt.mpr h1)
      obtain ⟨η, hη, hηQ⟩ := Metric.eventually_nhds_iff.mp hev
      -- (v) `δ = min(ρ/2, η N(x)/(1 + 4√(j + 1)))`, so that `|ψ_F(y) − y₀| < η`
      refine ⟨min (ρ / 2) (η * Nx / (1 + 4 * Real.sqrt J.card)), by positivity, ?_⟩
      intro y hy hyx
      have hyx1 : dist y x < ρ / 2 := lt_of_lt_of_le hyx (min_le_left _ _)
      have hyx2 : dist y x < η * Nx / (1 + 4 * Real.sqrt J.card) :=
        lt_of_lt_of_le hyx (min_le_right _ _)
      have hney := hcentre b J y (ρ / 2) (by positivity)
        (hfar b J (by omega) y (ρ / 2) (hnear b J x y ρ hyx1 hcount))
      obtain ⟨-, -, F3y, F4y, -⟩ := FR b J hJ y hy hney
      have hd := F6 y hy hney
      have hdη : dist (R b J hJ y) y₀ < η := by
        calc dist (R b J hJ y) y₀ ≤ (1 + 4 * Real.sqrt J.card) / Nx * dist y x := hd
          _ < (1 + 4 * Real.sqrt J.card) / Nx * (η * Nx / (1 + 4 * Real.sqrt J.card)) := by
            gcongr
          _ = η := by field_simp
      -- (vi) `ψ_F(y)` lies on a face `G_{i,β}` through `y₀`; the chain rule
      obtain ⟨i₂, hi₂, hbd₂⟩ := F4y
      obtain ⟨e, he⟩ : ∃ e : Bool,
          R b J hJ y i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        rcases hbd₂ with h | h
        · exact ⟨false, by simp [h]⟩
        · exact ⟨true, by simp [h]⟩
      obtain ⟨hQ1, hQ2⟩ := hηQ hdη i₂ hi₂ e
      have hy₀β : y₀ i₂ = ((if e then b i₂ + 1 else b i₂ : ℤ) : ℝ) := by
        by_contra hc
        exact hQ2 hc he
      have hbound := hQ1 hy₀β (hGmem i₂ hi₂ _ F3y _ he)
      rw [hrecj y hy, hΨx]
      calc dist (Ψ j (R b J hJ y)) (Ψ j y₀)
          ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) * dist (R b J hJ y) y₀ := hbound
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / (ρ / Nx) *
              ((1 + 4 * Real.sqrt J.card) / Nx * dist y x) := by gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt J.card) / ρ * dist y x := by
            field_simp
        _ ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) * (1 + 4 * Real.sqrt P) / ρ * dist y x := by
            gcongr
        _ = (1 + 4 * Real.sqrt P) ^ (j + 1 - m - 1) / ρ * dist y x := by
            rw [show j + 1 - m - 1 = (j - m - 1) + 1 by omega, pow_succ]
  -- Step 0: Claim(j) gives the theorem, since `K ^ (j − m − 1) ≤ K ^ P = c`
  intro j hj hjP b J hcard x hx ρ hρ hcount
  obtain ⟨hA, hB, δ, hδ, hC⟩ := hclaim j hj hjP b J hcard x ((hInF b J x).2 hx) ρ hρ hcount
  refine ⟨(hInF b J _).1 hA, hB, ?_⟩
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy hyF
  calc dist (Ψ j y) (Ψ j x) ≤ (1 + 4 * Real.sqrt P) ^ (j - m - 1) / ρ * dist y x :=
        hC y ((hInF b J y).2 hyF) (Metric.mem_ball.mp hy)
    _ ≤ (1 + 4 * Real.sqrt P) ^ P / ρ * dist y x := by
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      apply div_le_div_of_nonneg_right _ hρ.le
      exact pow_le_pow_right₀ hK1 (by omega)
/-- **Simon Ch. 6, proof of 5.1** (tube cover of the shifted dual skeleton; the inclusion `⊆` in
the identity before display (6)).  Let `L*(a)` be the set of `w ∈ ℝᴾ` with `wᵢ - aᵢ ∈ ℤ` for at
least `m + 2` indices `i`.  If `dist(x, L*(a)) < r`, then for some injective
`e : Fin (m + 2) → Fin P` and `z ∈ ℤ^{m+2}`, `Σₖ (x_{e k} - a_{e k} - z_k)² < r²`.  Take
`w ∈ L*(a)` (nonempty, as `a ∈ L*(a)`) with `dist(x, w) < r`, let `e` enumerate `m + 2` of its
integral indices and put `z_k = w_{e k} - a_{e k}`; the sum is then
`Σₖ (x_{e k} - w_{e k})² ≤ dist(x, w)² < r²`. -/
theorem Submission.dimred_mbl_dt_gc_tube_cover : ∀ (P m : ℕ), m + 1 < P → ∀ (a x : Euclid P) (r : ℝ), infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r → ∃ e : Fin (m + 2) → Fin P, Function.Injective e ∧ ∃ z : Fin (m + 2) → ℤ, ∑ k, (x (e k) - a (e k) - z k) ^ 2 < r ^ 2 := by
  classical
  intro P m hPm a x r hx
  set L := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z}
  -- `a ∈ L*(a)`, so `infDist x L*(a) < r` gives a point `w ∈ L*(a)` with `dist x w < r`
  have hne : L.Nonempty :=
    ⟨a, Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]; omega, fun i _ => ⟨0, by simp⟩⟩
  obtain ⟨w, ⟨s, hs, hsz⟩, hxw⟩ := (infDist_lt_iff hne).1 hx
  -- `e` enumerates `m + 2` of the indices `i ∈ s`, and `z k = w (e k) - a (e k)`
  obtain ⟨J, hJs, hJ⟩ := Finset.exists_subset_card_eq hs
  let e : Fin (m + 2) → Fin P := fun k => J.orderEmbOfFin hJ k
  have he : Function.Injective e := (J.orderEmbOfFin hJ).injective
  have hes : ∀ k, e k ∈ s := fun k => hJs (J.orderEmbOfFin_mem hJ k)
  choose z hz using fun k => hsz (e k) (hes k)
  refine ⟨e, he, z, ?_⟩
  have hterm : ∀ k, x (e k) - a (e k) - z k = x (e k) - w (e k) := fun k => by
    rw [← hz k]; ring
  -- the coordinate projection along `e` does not increase length
  have hsub : ∑ k, (x (e k) - w (e k)) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    have := Finset.sum_map Finset.univ ⟨e, he⟩ fun i => (x i - w i) ^ 2
    simp only [Function.Embedding.coeFn_mk] at this
    rw [← this]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun i _ _ => sq_nonneg _
  have hdist : ∑ i, (x i - w i) ^ 2 = dist x w ^ 2 := by
    rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.dist_eq, sq_abs]
  have h0 : 0 ≤ dist x w := dist_nonneg
  calc ∑ k, (x (e k) - a (e k) - z k) ^ 2 = ∑ k, (x (e k) - w (e k)) ^ 2 := by
        simp_rw [hterm]
    _ ≤ ∑ i, (x i - w i) ^ 2 := hsub
    _ = dist x w ^ 2 := hdist
    _ < r ^ 2 := by nlinarith
/-- **Simon Ch. 6, proof of 5.1** ((1)–(4) and the summation after them: the bad centres are
few).  Let `ρ` be a finite measure on `ℝᵈ` and `β > 0`.  For `g ∈ ℝᵈ` let
`O_r(g) = {y : |y − g − z| < r for some z ∈ ℤᵈ}` be the open Euclidean `r`-neighbourhood of
`g + ℤᵈ`.  Call `g` in the open cube `(1/4, 3/4)ᵈ` bad if `β rᵈ ρ(ℝᵈ) < ρ(O_r(g))` for some
`r ∈ (0, 1/4]`.  Then the bad set has Lebesgue outer measure at most `10ᵈ/β`.
By Vitali's covering lemma (`τ = 2`) there are bad centres `b` whose sup-metric balls
`B(b, r_b)` are pairwise disjoint and such that the balls `B(b, 3r_b)` cover the bad set.  The
sets `O_{r_b}(b)` are then pairwise disjoint too, so `Σ_b β r_bᵈ ≤ 1`, and the bad set has
measure at most `Σ_b (6r_b)ᵈ ≤ 6ᵈ/β ≤ 10ᵈ/β`. -/
theorem Submission.dimred_mbl_dt_gc_bad_set_volume : ∀ (d : ℕ) (ρ : Measure (Fin d → ℝ)), IsFiniteMeasure ρ → ∀ β : ℝ, 0 < β → volume {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ENNReal.ofReal (β * r ^ d) * ρ univ < ρ {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}} ≤ ENNReal.ofReal (10 ^ d / β) := by
  classical
  intro d ρ hρ β hβ
  set O : (Fin d → ℝ) → ℝ → Set (Fin d → ℝ) := fun g r =>
    {y | ∃ z : Fin d → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} with hO
  set Bad := {g : Fin d → ℝ | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r)}
  -- step 1: every `O_r(g)` is open, a union over `z ∈ ℤᵈ` of open sets
  have hOopen : ∀ g r, IsOpen (O g r) := by
    intro g r
    have : O g r = ⋃ z : Fin d → ℤ, {y | ∑ k, (y k - g k - z k) ^ 2 < r ^ 2} := by
      ext y; simp [hO]
    rw [this]
    exact isOpen_iUnion fun z => isOpen_lt (by fun_prop) continuous_const
  -- step 2: if `ρ(ℝᵈ) = 0` there are no bad centres
  by_cases h0 : ρ univ = 0
  · have : Bad = ∅ := by
      ext g
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨-, r, -, -, hr⟩
      rw [h0, mul_zero, measure_mono_null (subset_univ _) h0] at hr
      exact lt_irrefl _ hr
    rw [this, measure_empty]
    exact bot_le
  have hfin : ρ univ ≠ ∞ := measure_ne_top ρ univ
  -- step 3 (printed (3)): a radius `r_g ∈ (0, 1/4]` for every bad centre `g`
  have hrad : ∀ g ∈ Bad, ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ d) * ρ univ < ρ (O g r) := fun g hg => hg.2
  choose! rad hrad0 hrad1 hradlt using hrad
  -- step 4: Vitali's covering lemma for the balls `B(g, r_g)`, with `τ = 2` and `R = 1/4`
  obtain ⟨u, huBad, hudisj, hucov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun g => ball g (rad g)) Bad rad 2 one_lt_two (fun g hg => (hrad0 g hg).le) (1 / 4) hrad1
    (fun g hg => ⟨g, mem_ball_self (hrad0 g hg)⟩)
  -- step 5: `u` is countable, the balls being open, nonempty and pairwise disjoint
  have hucount : u.Countable := hudisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun g hg => ⟨g, mem_ball_self (hrad0 g (huBad hg))⟩)
  -- step 6 (printed (4), with `3` for `5`): the balls `B(b, 3 r_b)`, `b ∈ u`, cover the bad set
  have hBadsub : Bad ⊆ ⋃ b ∈ u, ball b (3 * rad b) := by
    intro g hg
    obtain ⟨b, hbu, ⟨y, hy1, hy2⟩, hle⟩ := hucov g hg
    refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
    rw [mem_ball] at hy1 hy2 ⊢
    calc dist g b ≤ dist g y + dist y b := dist_triangle _ _ _
      _ < rad g + rad b := by rw [dist_comm g y]; exact add_lt_add hy1 hy2
      _ ≤ 3 * rad b := by linarith
  -- step 7: the periodic sets `O_{r_b}(b)`, `b ∈ u`, are pairwise disjoint
  have hcoord : ∀ (y g : Fin d → ℝ) (r : ℝ) (z : Fin d → ℤ),
      ∑ k, (y k - g k - z k) ^ 2 < r ^ 2 → 0 < r → ∀ k, |y k - g k - z k| < r := by
    intro y g r z h hr k
    have hk : (y k - g k - z k) ^ 2 < r ^ 2 :=
      lt_of_le_of_lt (Finset.single_le_sum (f := fun i => (y i - g i - z i) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ k)) h
    exact abs_lt_of_sq_lt_sq hk hr.le
  have hOdisj : u.PairwiseDisjoint fun b => O b (rad b) := by
    intro b hb b' hb' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨z, hz⟩ ⟨z', hz'⟩
    have hb0 := hrad0 b (huBad hb)
    have hb'0 := hrad0 b' (huBad hb')
    have h1 := hcoord y b (rad b) z hz hb0
    have h2 := hcoord y b' (rad b') z' hz' hb'0
    have hr1 := hrad1 b (huBad hb)
    have hr2 := hrad1 b' (huBad hb')
    -- the centres lie in `(1/4, 3/4)ᵈ` and the radii are `≤ 1/4`, so the integer shifts agree
    have hzz : z = z' := by
      funext k
      have a1 := abs_lt.1 (h1 k)
      have a2 := abs_lt.1 (h2 k)
      have a3 := abs_lt.1 ((huBad hb).1 k)
      have a4 := abs_lt.1 ((huBad hb').1 k)
      have c1 : (z k : ℝ) < z' k + 1 := by linarith
      have c2 : (z' k : ℝ) < z k + 1 := by linarith
      have c1' : z k < z' k + 1 := by exact_mod_cast c1
      have c2' : z' k < z k + 1 := by exact_mod_cast c2
      omega
    subst hzz
    -- so `y − z` lies in both of the disjoint balls `B(b, r_b)` and `B(b', r_{b'})`
    have hv : (fun k => y k - z k) ∈ ball b (rad b) ∩ ball b' (rad b') := by
      constructor
      · rw [mem_ball, dist_pi_lt_iff hb0]
        intro k
        rw [Real.dist_eq]
        have := h1 k
        rwa [show y k - z k - b k = y k - b k - z k by ring]
      · rw [mem_ball, dist_pi_lt_iff hb'0]
        intro k
        rw [Real.dist_eq]
        have := h2 k
        rwa [show y k - z k - b' k = y k - b' k - z k by ring]
    exact (Set.disjoint_left.1 (hudisj hb hb' hne)) hv.1 hv.2
  -- step 8 (summation): `S = Σ_{b ∈ u} β r_bᵈ ≤ 1`
  set S : ℝ≥0∞ := ∑' b : u, ENNReal.ofReal (β * rad b ^ d)
  have hSle : S ≤ 1 := by
    have hsum : S * ρ univ ≤ 1 * ρ univ := by
      calc S * ρ univ = ∑' b : u, ENNReal.ofReal (β * rad b ^ d) * ρ univ :=
            (ENNReal.tsum_mul_right).symm
        _ ≤ ∑' b : u, ρ (O b (rad b)) :=
            ENNReal.tsum_le_tsum fun b => (hradlt b (huBad b.2)).le
        _ = ρ (⋃ b ∈ u, O b (rad b)) :=
            (measure_biUnion hucount hOdisj fun b _ => (hOopen _ _).measurableSet).symm
        _ ≤ ρ univ := measure_mono (subset_univ _)
        _ = 1 * ρ univ := (one_mul _).symm
    exact (ENNReal.mul_le_mul_iff_left h0 hfin).1 hsum
  -- step 9: the volume bound `Σ_b (6 r_b)ᵈ = (6ᵈ/β) S ≤ 6ᵈ/β ≤ 10ᵈ/β`
  calc volume Bad ≤ volume (⋃ b ∈ u, ball b (3 * rad b)) := measure_mono hBadsub
    _ ≤ ∑' b : u, volume (ball (b : Fin d → ℝ) (3 * rad b)) := measure_biUnion_le _ hucount _
    _ = ∑' b : u, ENNReal.ofReal (6 ^ d / β) * ENNReal.ofReal (β * rad b ^ d) := by
        refine tsum_congr fun b => ?_
        have hb0 := hrad0 b (huBad b.2)
        rw [Real.volume_pi_ball _ (by positivity), Fintype.card_fin,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (6 ^ d / β) * S := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (6 ^ d / β) * 1 := by gcongr
    _ ≤ ENNReal.ofReal (10 ^ d / β) := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        gcongr
        norm_num
/-- **Simon Ch. 6, proof of 5.1** (choice of a good centre: display (5) and the choice of
`a ∈ ⋂ⱼ pⱼ⁻¹(Gⱼ) ∩ B_{1/4}(q)`, with the open cube `Q = (1/4, 3/4)ᴾ` in place of the ball).  If
the sets `E_e ⊆ ℝᵈ` (`e : Fin d → Fin P`) have total outer measure `< (1/2)ᴾ`, then some `a ∈ Q`
has `(a_{e k})ₖ ∉ E_e` for every injective `e`.  For injective `e`, splitting the coordinates into
`range e` and its complement (Fubini) bounds the measure of `{a ∈ Q : (a_{e k})ₖ ∈ E_e}` by
`|E_e| · (1/2)^{P - d} ≤ |E_e|`; the union bound over all `e` then leaves part of `Q`, which has
volume `(1/2)ᴾ`, uncovered. -/
theorem Submission.dimred_mbl_dt_gc_cube_selection : ∀ (P d : ℕ) (E : (Fin d → Fin P) → Set (Fin d → ℝ)), ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ e : Fin d → Fin P, Function.Injective e → (fun k => a (e k)) ∉ E e := by
  classical
  intro P d E hsum
  -- Step 2 (Fubini): for injective `e`, the points of the cube whose `e`-projection lies in `F`
  -- have volume at most `volume F`
  have fubini : ∀ e : Fin d → Fin P, Function.Injective e → ∀ F : Set (Fin d → ℝ),
      volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ≤
        volume F := by
    intro e he F
    let p : Fin P → Prop := fun i => i ∈ range e
    let Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    have hΦ : MeasurePreserving Φ := by
      convert volume_preserving_piEquivPiSubtypeProd (fun _ : Fin P => ℝ) p
    let σ : Fin d ≃ {i // p i} := Equiv.ofInjective e he
    let ψ := (MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm
    have hψ : MeasurePreserving ψ :=
      (volume_measurePreserving_piCongrLeft (fun _ : {i // p i} => ℝ) σ).symm _
    have hψapp : ∀ u k, ψ u k = u (σ k) := by
      intro u k
      simp [ψ, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_symm_apply]
    let G : Set ({i // p i} → ℝ) := ψ ⁻¹' F
    let H : Set ({i // ¬ p i} → ℝ) := Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)
    have hsub : {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F} ⊆
        Φ ⁻¹' (G ×ˢ H) := by
      rintro x ⟨hx1, hx2⟩
      refine ⟨?_, fun i _ => hx1 i⟩
      show ψ (fun i => x i) ∈ F
      have : ψ (fun i : {i // p i} => x i) = fun k => x (e k) := by
        funext k; rw [hψapp]; rfl
      rw [this]; exact hx2
    have hG : volume G = volume F := hψ.measure_preimage_equiv F
    have hH : volume H ≤ 1 := by
      rw [Real.volume_pi_Ioo]
      refine Finset.prod_le_one fun i _ => ?_
      rw [ENNReal.ofReal_le_one]; norm_num
    calc volume {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ F}
        ≤ volume (Φ ⁻¹' (G ×ˢ H)) := measure_mono hsub
      _ = volume (G ×ˢ H) := hΦ.measure_preimage_equiv _
      _ = volume G * volume H := by
          rw [Measure.volume_eq_prod]; exact Measure.prod_prod G H
      _ ≤ volume G * 1 := by gcongr
      _ = volume F := by rw [mul_one, hG]
  have hI : ∀ t : ℝ, |t - 1 / 2| < 1 / 4 ↔ t ∈ Ioo (1 / 4 : ℝ) (3 / 4) := by
    intro t
    rw [abs_sub_lt_iff, mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- Step 1: the open cube `Q` in `Euclid P` has volume `(1/2)^P`
  let Q : Set (Euclid P) := {a | ∀ i, a i ∈ Ioo (1 / 4 : ℝ) (3 / 4)}
  have hofLp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin P)
  have hQ : volume Q = ENNReal.ofReal ((1 / 2) ^ P) := by
    have : Q = (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
        (Set.pi univ fun _ => Ioo (1 / 4 : ℝ) (3 / 4)) := by
      ext a; simp [Q, Set.mem_pi]
    rw [this, hofLp.measure_preimage_equiv, Real.volume_pi_Ioo, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by norm_num)]
    norm_num
  -- Step 3: the centres in `Q` with a bad `e`-projection
  let A : (Fin d → Fin P) → Set (Euclid P) := fun e =>
    {a | Function.Injective e ∧ a ∈ Q ∧ (fun k => a (e k)) ∈ E e}
  have hA : ∀ e, volume (A e) ≤ volume (E e) := by
    intro e
    by_cases he : Function.Injective e
    · have hsub : A e ⊆ (MeasurableEquiv.toLp 2 (Fin P → ℝ)).symm ⁻¹'
          {x : Fin P → ℝ | (∀ i, x i ∈ Ioo (1 / 4 : ℝ) (3 / 4)) ∧ (fun k => x (e k)) ∈ E e} := by
        rintro a ⟨-, haQ, haE⟩
        exact ⟨haQ, haE⟩
      calc volume (A e) ≤ _ := measure_mono hsub
        _ = _ := hofLp.measure_preimage_equiv _
        _ ≤ volume (E e) := fubini e he (E e)
    · have : A e = ∅ := by
        ext a; simp only [mem_empty_iff_false, iff_false]; exact fun h => he h.1
      rw [this, measure_empty]; exact bot_le
  -- Steps 4–5: union bound and choice of `a`
  by_contra hcon
  push Not at hcon
  have hcov : Q ⊆ ⋃ e, A e := by
    intro a haQ
    obtain ⟨e, he, haE⟩ := hcon a fun i => (hI _).2 (haQ i)
    exact mem_iUnion.2 ⟨e, he, haQ, haE⟩
  have : volume Q < volume Q :=
    calc volume Q ≤ volume (⋃ e, A e) := measure_mono hcov
      _ ≤ ∑ e, volume (A e) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ e, volume (E e) := Finset.sum_le_sum fun e _ => hA e
      _ < ENNReal.ofReal ((1 / 2) ^ P) := hsum
      _ = volume Q := hQ.symm
  exact lt_irrefl _ this
/-- **Simon Ch. 6, proof of 5.1** (choice of the good centre `a`; displays (6), (7)).  There is
`C`, depending only on `P` and `m`, such that for any finite measures `μ`, `μ'` on `ℝᴾ` some
centre `a` in the open cube `(1/4, 3/4)ᴾ` has `μ({x : dist(x, L*(a)) < r}) ≤ C r^{m+2} μ(ℝᴾ)` for
all `r ∈ (0, 1/4]`, and likewise for `μ'`.  Put `d = m + 2`, `K = Pᵈ` and `β = 2K·10ᵈ·2ᴾ + 1`.
For `e : Fin d → Fin P` let `E_e` be the union of the bad sets (`dimred_mbl_dt_gc_bad_set_volume`)
of the push-forwards of `μ` and `μ'` under `x ↦ (x_{e k})ₖ`.  Their volumes sum to at most
`2K·10ᵈ/β < (1/2)ᴾ`, so `dimred_mbl_dt_gc_cube_selection` gives a centre `a` all of whose
injective projections are good.  The tube cover `dimred_mbl_dt_gc_tube_cover` and finite
subadditivity then give the estimate with `C = Kβ`. -/
theorem Submission.dimred_mbl_dt_good_center : ∀ (P m : ℕ), m + 1 < P → ∃ C : NNReal, ∀ μ μ' : Measure (Euclid P), IsFiniteMeasure μ → IsFiniteMeasure μ' → ∃ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ univ ∧ μ' {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * μ' univ := by
  have c1 := Submission.dimred_mbl_dt_gc_tube_cover
  have c2 := Submission.dimred_mbl_dt_gc_bad_set_volume
  have c3 := Submission.dimred_mbl_dt_gc_cube_selection
  classical
  intro P m hPm
  -- the constants: `K = #(Fin (m + 2) → Fin P)`, `β = 2K·10^{m+2}·2ᴾ + 1` and `C = Kβ`
  set K : ℕ := Fintype.card (Fin (m + 2) → Fin P) with hK
  set β : ℝ := 2 * K * 10 ^ (m + 2) * 2 ^ P + 1 with hβ
  have hβpos : 0 < β := by positivity
  refine ⟨Real.toNNReal (K * β), ?_⟩
  intro μ μ' hμ hμ'
  -- the coordinate projections `x ↦ (x_{e k})ₖ` and the bad sets of the push-forwards
  let prj : (Fin (m + 2) → Fin P) → Euclid P → (Fin (m + 2) → ℝ) := fun e x k => x (e k)
  have hprj : ∀ e, Measurable (prj e) := fun e =>
    (continuous_pi fun k => PiLp.continuous_apply 2 (fun _ : Fin P => ℝ) (e k)).measurable
  let Bad : Measure (Fin (m + 2) → ℝ) → Set (Fin (m + 2) → ℝ) := fun ρ =>
    {g | (∀ k, |g k - 1 / 2| < 1 / 4) ∧ ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
      ENNReal.ofReal (β * r ^ (m + 2)) * ρ univ <
        ρ {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - g k - z k) ^ 2 < r ^ 2}}
  let E : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
    Bad (μ.map (prj e)) ∪ Bad (μ'.map (prj e))
  have hE : ∀ e, volume (E e) ≤ 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := by
    intro e
    calc volume (E e) ≤ volume (Bad (μ.map (prj e))) + volume (Bad (μ'.map (prj e))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (10 ^ (m + 2) / β) + ENNReal.ofReal (10 ^ (m + 2) / β) :=
          add_le_add (c2 (m + 2) _ inferInstance β hβpos) (c2 (m + 2) _ inferInstance β hβpos)
      _ = 2 * ENNReal.ofReal (10 ^ (m + 2) / β) := (two_mul _).symm
  -- the bad sets have total volume `≤ 2K·10^{m+2}/β < (1/2)ᴾ`
  have hsum : ∑ e, volume (E e) < ENNReal.ofReal ((1 / 2) ^ P) := by
    calc ∑ e, volume (E e) ≤ ∑ _e : Fin (m + 2) → Fin P, 2 * ENNReal.ofReal (10 ^ (m + 2) / β) :=
          Finset.sum_le_sum fun e _ => hE e
      _ = ENNReal.ofReal (2 * K * 10 ^ (m + 2) / β) := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
      _ < ENNReal.ofReal ((1 / 2) ^ P) := by
          rw [ENNReal.ofReal_lt_ofReal_iff (by positivity), div_lt_iff₀ hβpos, hβ]
          have h2 : ((1 : ℝ) / 2) ^ P * 2 ^ P = 1 := by
            rw [← mul_pow]; norm_num
          have h3 : (0 : ℝ) < (1 / 2) ^ P := by positivity
          have h4 : ((1 : ℝ) / 2) ^ P * (2 * K * 10 ^ (m + 2) * 2 ^ P + 1) =
              2 * K * 10 ^ (m + 2) * ((1 / 2) ^ P * 2 ^ P) + (1 / 2) ^ P := by ring
          rw [h4, h2]
          linarith
  -- a centre `a` in the cube none of whose injective projections is bad
  obtain ⟨a, ha, hgood⟩ := c3 P (m + 2) E hsum
  refine ⟨a, ha, ?_⟩
  intro r hr0 hr1
  -- the tube estimate for one measure `ν` all of whose projected bad sets avoid `a`
  have key : ∀ ν : Measure (Euclid P), IsFiniteMeasure ν →
      (∀ e : Fin (m + 2) → Fin P, Function.Injective e → prj e a ∉ Bad (ν.map (prj e))) →
      ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤
        (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
    intro ν hν hνgood
    let O : (Fin (m + 2) → Fin P) → Set (Fin (m + 2) → ℝ) := fun e =>
      {y | ∃ z : Fin (m + 2) → ℤ, ∑ k, (y k - prj e a k - z k) ^ 2 < r ^ 2}
    let T : (Fin (m + 2) → Fin P) → Set (Euclid P) := fun e =>
      {x | Function.Injective e ∧ prj e x ∈ O e}
    -- the tube about `L*(a)` is covered by the cylinders `prj_e⁻¹(O_r(prj_e a))`
    have hcover : {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ⊆ ⋃ e, T e := by
      intro x hx
      obtain ⟨e, he, z, hz⟩ := c1 P m hPm a x r hx
      exact mem_iUnion.2 ⟨e, he, z, hz⟩
    -- each cylinder has `ν`-measure at most `β r^{m+2} ν(ℝᴾ)`, as `prj_e a` is good
    have hT : ∀ e, ν (T e) ≤ ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
      intro e
      by_cases he : Function.Injective e
      · have hsub : T e ⊆ prj e ⁻¹' O e := fun x hx => hx.2
        have hcube : ∀ k, |prj e a k - 1 / 2| < 1 / 4 := fun k => ha (e k)
        have hnot := hνgood e he
        have hle : (ν.map (prj e)) (O e) ≤
            ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := by
          by_contra hlt
          exact hnot ⟨hcube, r, hr0, hr1, not_le.1 hlt⟩
        calc ν (T e) ≤ ν (prj e ⁻¹' O e) := measure_mono hsub
          _ ≤ (ν.map (prj e)) (O e) := Measure.le_map_apply (hprj e).aemeasurable _
          _ ≤ ENNReal.ofReal (β * r ^ (m + 2)) * (ν.map (prj e)) univ := hle
          _ = ENNReal.ofReal (β * r ^ (m + 2)) * ν univ := by
              rw [Measure.map_apply (hprj e) MeasurableSet.univ, preimage_univ]
      · have : T e = ∅ := by
          ext x
          simp only [mem_empty_iff_false, iff_false]
          exact fun hx => he hx.1
        rw [this, measure_empty]
        exact bot_le
    -- finite subadditivity over the `K` maps `e`
    calc ν {x | infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
          ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} < r} ≤ ν (⋃ e, T e) := measure_mono hcover
      _ ≤ ∑ e, ν (T e) := measure_iUnion_fintype_le ν T
      _ ≤ ∑ _e : Fin (m + 2) → Fin P, ENNReal.ofReal (β * r ^ (m + 2)) * ν univ :=
          Finset.sum_le_sum fun e _ => hT e
      _ = (Real.toNNReal (K * β) : ℝ≥0∞) * ENNReal.ofReal (r ^ (m + 2)) * ν univ := by
          rw [Finset.sum_const, Finset.card_univ, ← hK, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
            show ((Real.toNNReal (K * β) : ℝ≥0∞)) = ENNReal.ofReal (K * β) from rfl,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact ⟨key μ hμ fun e he h => hgood e he (Or.inl h),
    key μ' hμ' fun e he h => hgood e he (Or.inr h)⟩
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

/-- Local Lipschitz bounds along a segment give the global bound (step (6a) of the proof of the
skeleton retraction, Simon Ch. 6, Lemma 5.4): if every point `x + t(y − x)`, `t ∈ [0, 1]`, has a
neighbourhood on which `|f(w) − f(x + t(y − x))| ≤ K|w − (x + t(y − x))|`, then
`|f(y) − f(x)| ≤ K|y − x|`.  By continuous induction on `[0, 1]`, every `t ∈ [0, 1]` satisfies
`|f(x + t(y − x)) − f(x)| ≤ K t |y − x|`. -/
theorem dimred_mbl_dtsr_segment_lipschitz : ∀ (P : ℕ) (f : Euclid P → Euclid P) (x y : Euclid P) (K : ℝ), 0 ≤ K → (∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ w in 𝓝 (x + t • (y - x)), dist (f w) (f (x + t • (y - x))) ≤ K * dist w (x + t • (y - x))) → dist (f y) (f x) ≤ K * dist y x := by
  intro P f x y K _hK hloc
  -- Step 1: `g t = x + t(y − x)` is continuous and `|g s − g t| = |s − t| |y − x|`.
  let g : ℝ → Euclid P := fun t => x + t • (y - x)
  have hgcont : Continuous g := continuous_const.add (continuous_id.smul continuous_const)
  have hgdist : ∀ s t : ℝ, dist (g s) (g t) = |s - t| * dist y x := by
    intro s t
    simp only [g, dist_eq_norm]
    rw [show x + s • (y - x) - (x + t • (y - x)) = (s - t) • (y - x) by rw [sub_smul]; abel,
      norm_smul, Real.norm_eq_abs]
  -- Step 2: `f ∘ g` is continuous at each `t ∈ [0, 1]`: for `s` near `t`, `g s` lies in the
  -- neighbourhood of `g t` given by `hloc`, so `|f(g s) − f(g t)| ≤ K |s − t| |y − x| → 0`.
  have hfg : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun s => f (g s)) t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * (|s - t| * dist y x) := by
      filter_upwards [(hgcont.tendsto t).eventually (hloc t ht)] with s hs
      rw [← hgdist]
      exact hs
    have hlim : Tendsto (fun s : ℝ => K * (|s - t| * dist y x)) (𝓝 t) (𝓝 0) :=
      (continuous_const.mul ((continuous_id.sub continuous_const).abs.mul
        continuous_const)).tendsto' t 0 (by simp)
    exact tendsto_iff_dist_tendsto_zero.2
      (squeeze_zero' (Eventually.of_forall fun s => dist_nonneg) hev hlim)
  -- Step 3: `S = {t | |f(g t) − f(x)| ≤ K t |y − x|}` meets `[0, 1]` in a closed set, the
  -- preimage of `(−∞, 0]` under a function continuous on `[0, 1]`.
  let S : Set ℝ := {t | dist (f (g t)) (f x) ≤ K * t * dist y x}
  have hS : IsClosed (S ∩ Icc 0 1) := by
    have hcont : ContinuousOn (fun t => dist (f (g t)) (f x) - K * t * dist y x) (Icc 0 1) := by
      intro t ht
      have hd : ContinuousAt (fun s => dist (f (g s)) (f x)) t :=
        (hfg t ht).dist continuousAt_const
      have hl : Continuous fun s : ℝ => K * s * dist y x :=
        (continuous_const.mul continuous_id).mul continuous_const
      exact hd.continuousWithinAt.sub hl.continuousWithinAt
    convert hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := (0 : ℝ)))
      using 1
    ext t
    simp only [S, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Iic, sub_nonpos]
    tauto
  -- Step 4: `0 ∈ S`, since `g 0 = x`.
  have h0 : (0 : ℝ) ∈ S := by
    show dist (f (x + (0 : ℝ) • (y - x))) (f x) ≤ K * 0 * dist y x
    simp
  -- Step 5: if `t ∈ S ∩ [0, 1)`, then `s ∈ S` for `s > t` near `t`:
  -- `|f(g s) − f(x)| ≤ K (s − t) |y − x| + K t |y − x| = K s |y − x|`.
  have hstep : ∀ t ∈ S ∩ Ico (0 : ℝ) 1, S ∈ 𝓝[>] t := by
    rintro t ⟨htS, ht⟩
    have htS' : dist (f (g t)) (f x) ≤ K * t * dist y x := htS
    have hev : ∀ᶠ s in 𝓝 t, dist (f (g s)) (f (g t)) ≤ K * dist (g s) (g t) :=
      (hgcont.tendsto t).eventually (hloc t ⟨ht.1, ht.2.le⟩)
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hts
    have hts' : t < s := hts
    show dist (f (g s)) (f x) ≤ K * s * dist y x
    calc dist (f (g s)) (f x) ≤ dist (f (g s)) (f (g t)) + dist (f (g t)) (f x) :=
          dist_triangle _ _ _
      _ ≤ K * dist (g s) (g t) + K * t * dist y x := add_le_add hs htS'
      _ = K * s * dist y x := by rw [hgdist, abs_of_pos (sub_pos.mpr hts')]; ring
  -- Step 6: continuous induction on `[0, 1]` gives `[0, 1] ⊆ S`.
  have hsub : Icc (0 : ℝ) 1 ⊆ S := hS.Icc_subset_of_forall_mem_nhdsWithin h0 hstep
  -- Step 7: `1 ∈ S` and `g 1 = y`.
  have h1 : dist (f (g 1)) (f x) ≤ K * 1 * dist y x := hsub ⟨zero_le_one, le_rfl⟩
  have hg1 : g 1 = y := by simp [g]
  rwa [hg1, mul_one] at h1

/-- **Retraction onto the `n`-skeleton away from the dual skeleton** (Lemma D; Simon Ch. 6,
Lemma 5.4, chapter-06.txt lines 1493–1645, with `n = m + 1`).  Let
`L*(a) = {w : w_i − a_i ∈ ℤ for at least m + 2 indices i}` and `d = dist(·, L*(a))`.  Take
`ψ = Ψ_P` (`dimred_mbl_dtsr_face_retraction_family`) and `c₀` from
`dimred_mbl_dtsr_face_count_induction`.  If `x` lies in a closed unit cube `z + [0, 1]ᴾ`
(the face `F(z, univ)`) and `d(x) > 0`, then `dimred_mbl_dtsr_dual_dist_count` gives the
counting condition with `ρ = d(x)/√(m + 2)`, and the face induction with `j = P` puts `ψ(x)` in the
same cube (so `|ψ(x) − x| ≤ √P`) and in the `n`-skeleton, and gives
`|ψ(y) − ψ(x)| ≤ (√(m + 2) c₀/d(x))|y − x|` for `y` in that cube near `x`.  The finitely many
cubes through `x` cover a neighbourhood of `x` (`dimred_mbl_dtsr_cube_cover`).  Let
`0 < r ≤ 1/4` and `d(x), d(y) ≥ r`.  If `|x − y| < r/2`, then `d > r/2` on `[x, y]` (`d` is
`1`-Lipschitz), and `dimred_mbl_dtsr_segment_lipschitz` gives the constant `2√(m + 2) c₀/r`.
Otherwise `|ψ(x) − ψ(y)| ≤ 2√P + |x − y| ≤ (4√P + 1)|x − y|/r`.  So
`c = 2√(m + 2) c₀ + 4√P + 1` works. -/
theorem dimred_mbl_dt_skeleton_retraction : ∀ (P m : ℕ), m + 1 < P → ∃ c : ℝ, 0 < c ∧ ∀ a : Euclid P, (∀ i, |a i - 1 / 2| < 1 / 4) → ∃ ψ : Euclid P → Euclid P, (∀ x : Euclid P, 0 < infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, ψ x i = z) ∧ dist (ψ x) x ≤ Real.sqrt P) ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 4 → ∀ x y : Euclid P, r ≤ infDist x {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → r ≤ infDist y {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧ ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} → dist (ψ x) (ψ y) ≤ c / r * dist x y := by
  intro P m hPm
  -- Step 0: `c₀` from the face induction and `c = 2√(m + 2) c₀ + 4√P + 1`
  obtain ⟨c₀, hc₀, hind⟩ := Submission.dimred_mbl_dtsr_face_count_induction P m
  have hsq : (0 : ℝ) < Real.sqrt (m + 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1, by positivity, ?_⟩
  intro a ha
  -- Step 1: `ψ = Ψ_P` for the composite of the face retractions; the face induction at `j = P`
  obtain ⟨Ψ, hΨ0, hΨrec⟩ := Submission.dimred_mbl_dtsr_face_retraction_family P m a ha
  have key := hind a ha Ψ hΨ0 hΨrec P (by omega) le_rfl
  set L : Set (Euclid P) := {w : Euclid P | ∃ s : Finset (Fin P), m + 2 ≤ s.card ∧
    ∀ i ∈ s, ∃ z : ℤ, w i - a i = z} with hL
  -- Step 2: the closed unit cube `z + [0, 1]ᴾ` is the face `F(z, univ)`, of diameter `√P`
  have hcard : (Finset.univ : Finset (Fin P)).card = P := by simp
  have hface : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      ∀ i, (i ∈ (Finset.univ : Finset (Fin P)) → (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) ∧
        (i ∉ (Finset.univ : Finset (Fin P)) → u i = z i) :=
    fun z u hu i => ⟨fun _ => hu i, fun h => absurd (Finset.mem_univ i) h⟩
  have hdiam : ∀ (z : Fin P → ℤ) (u v : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      (∀ i, (z i : ℝ) ≤ v i ∧ v i ≤ z i + 1) → dist u v ≤ Real.sqrt P := by
    intro z u v hu hv
    rw [EuclideanSpace.dist_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, dist (u i) (v i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : dist (u i) (v i) ≤ 1 := by
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [(hu i).1, (hu i).2, (hv i).1, (hv i).2]
          have h0 : 0 ≤ dist (u i) (v i) := dist_nonneg
          nlinarith
      _ = P := by simp
  -- Step 3: on a cube through `u` with `d(u) > 0`, the face induction with
  -- `ρ = d(u)/√(m + 2)`; the counting condition is `dimred_mbl_dtsr_dual_dist_count`
  have hcube : ∀ (z : Fin P → ℤ) (u : Euclid P), (∀ i, (z i : ℝ) ≤ u i ∧ u i ≤ z i + 1) →
      0 < infDist u L →
      (∀ i, (i ∈ (Finset.univ : Finset (Fin P)) → (z i : ℝ) ≤ Ψ P u i ∧ Ψ P u i ≤ z i + 1) ∧
        (i ∉ (Finset.univ : Finset (Fin P)) → Ψ P u i = z i)) ∧
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ k : ℤ, Ψ P u i = k) ∧
      ∀ᶠ y in 𝓝[{w : Euclid P | ∀ i, (i ∈ (Finset.univ : Finset (Fin P)) →
          (z i : ℝ) ≤ w i ∧ w i ≤ z i + 1) ∧ (i ∉ (Finset.univ : Finset (Fin P)) → w i = z i)}] u,
        dist (Ψ P y) (Ψ P u) ≤ c₀ / (infDist u L / Real.sqrt (m + 2)) * dist y u :=
    fun z u hu hd => key z Finset.univ hcard u (hface z u hu) _ (div_pos hd hsq)
      (Submission.dimred_mbl_dtsr_dual_dist_count P m a u z)
  -- Step 4, part (i): the cube `⌊x⌋ + [0, 1]ᴾ` contains both `x` and `ψ(x)`
  have hfloor : ∀ u : Euclid P, ∀ i, ((⌊u i⌋ : ℤ) : ℝ) ≤ u i ∧ u i ≤ (⌊u i⌋ : ℤ) + 1 :=
    fun u i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have hpartI : ∀ x : Euclid P, 0 < infDist x L →
      (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, Ψ P x i = z) ∧
        dist (Ψ P x) x ≤ Real.sqrt P := by
    intro x hx
    obtain ⟨hmem, hint, -⟩ := hcube (fun i => ⌊x i⌋) x (hfloor x) hx
    exact ⟨hint, hdiam _ (Ψ P x) x (fun i => (hmem i).1 (Finset.mem_univ i)) (hfloor x)⟩
  -- Step 5: `|ψ(y) − ψ(w)| ≤ (√(m + 2) c₀/d(w))|y − w|` for `y` near `w`, from the finitely
  -- many cubes through `w` (`dimred_mbl_dtsr_cube_cover`)
  have hlocal : ∀ w : Euclid P, 0 < infDist w L → ∀ᶠ y in 𝓝 w,
      dist (Ψ P y) (Ψ P w) ≤ c₀ / (infDist w L / Real.sqrt (m + 2)) * dist y w := by
    intro w hw
    obtain ⟨Z, hZ, hcov⟩ := Submission.dimred_mbl_dtsr_cube_cover P w
    have hall : ∀ z ∈ Z, ∀ᶠ y : Euclid P in 𝓝 w, (∀ i, (z i : ℝ) ≤ y i ∧ y i ≤ z i + 1) →
        dist (Ψ P y) (Ψ P w) ≤ c₀ / (infDist w L / Real.sqrt (m + 2)) * dist y w := by
      intro z hz
      have h3 := (hcube z w (hZ z hz) hw).2.2
      rw [eventually_nhdsWithin_iff] at h3
      filter_upwards [h3] with y hy hyz
      exact hy (hface z y hyz)
    rw [← Finset.eventually_all] at hall
    filter_upwards [hall, hcov] with y hy hyz
    obtain ⟨z, hz, hyz⟩ := hyz
    exact hy z hz hyz
  refine ⟨Ψ P, hpartI, ?_⟩
  -- Step 6, part (ii)
  intro r hr hr4 x y hx hy
  have hc₀' : 0 ≤ 2 * Real.sqrt (m + 2) * c₀ := by positivity
  have hsP : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  by_cases hxy : dist x y < r / 2
  · -- Step 6a: `|x − y| < r/2`, so `d > r/2` on `[x, y]`; the segment argument with
    -- `K = 2√(m + 2) c₀/r`
    have hK : 0 ≤ 2 * Real.sqrt (m + 2) * c₀ / r := by positivity
    have hseg := dimred_mbl_dtsr_segment_lipschitz P (Ψ P) x y
      (2 * Real.sqrt (m + 2) * c₀ / r) hK ?_
    · rw [dist_comm (Ψ P x), dist_comm x]
      calc dist (Ψ P y) (Ψ P x) ≤ 2 * Real.sqrt (m + 2) * c₀ / r * dist y x := hseg
        _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist y x := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          apply div_le_div_of_nonneg_right _ hr.le
          linarith
    · intro t ht
      have hdist : dist (x + t • (y - x)) x ≤ dist x y := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1,
          ← dist_eq_norm, dist_comm y x]
        exact mul_le_of_le_one_left dist_nonneg ht.2
      -- `d` is `1`-Lipschitz
      have hdw : r / 2 < infDist (x + t • (y - x)) L := by
        have h1 := infDist_le_infDist_add_dist (x := x) (y := x + t • (y - x)) (s := L)
        rw [dist_comm] at h1
        linarith
      have hwpos : 0 < infDist (x + t • (y - x)) L := by linarith
      filter_upwards [hlocal _ hwpos] with w hw
      refine hw.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [div_div_eq_mul_div, div_le_div_iff₀ hwpos hr]
      have hc0 : 0 ≤ c₀ * Real.sqrt (m + 2) := by positivity
      nlinarith
  · -- Step 6b: `|x − y| ≥ r/2`, so `|ψ(x) − ψ(y)| ≤ 2√P + |x − y| ≤ (4√P + 1)|x − y|/r`
    have hxy : r / 2 ≤ dist x y := not_lt.mp hxy
    have h1 := (hpartI x (by linarith)).2
    have h2 := (hpartI y (by linarith)).2
    have hD : 0 ≤ dist x y := dist_nonneg
    calc dist (Ψ P x) (Ψ P y) ≤ dist (Ψ P x) x + dist x y + dist y (Ψ P y) :=
          dist_triangle4 _ _ _ _
      _ ≤ 2 * Real.sqrt P + dist x y := by rw [dist_comm y]; linarith
      _ ≤ (2 * Real.sqrt (m + 2) * c₀ + 4 * Real.sqrt P + 1) / r * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hr]
        nlinarith

end Submission

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

end GMT.Ch07
