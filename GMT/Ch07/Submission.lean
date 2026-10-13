import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter02.AreaLipschitz

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

/-- **Orthogonal frame adapted to an `n`-plane** (Step 0 of the graph first-variation estimate in
the tilt-excess step of Allard's theorem, used for Simon 7.4.3).  Let `T ⊆ ℝⁿ⁺ᵏ` have dimension
`n`, let `ι : ℝⁿ → ℝⁿ⁺ᵏ`, `ι' : ℝᵏ → ℝⁿ⁺ᵏ` be linear isometries with orthogonal ranges and
`ι(ℝⁿ) ⊆ T`, and let `P : ℝⁿ⁺ᵏ → ℝⁿ` satisfy `P ∘ ι = id` and `P ∘ ι' = 0`.  Then `range ι = T`
(both have dimension `n`), so `ι'w ∈ Tᗮ`, and `range ι' = Tᗮ` (both have dimension `k`).  Every
`y` splits as `y = p_T y + (y − p_T y) = ιu + ι'w` with `Py = u`.  This gives `⟪ιu', y⟫ = ⟪u', Py⟫`,
`p_T y = ι(Py)`, Pythagoras `|y|² = |Py|² + |y − p_T y|²`, and `|Py| ≤ |y|`. -/
theorem Submission.dorag_tes_gv_adapted_frame : ∀ (n k : ℕ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y)) ∧ (∀ y, T.starProjection y = ι (P y)) ∧ (∀ w, ι' w ∈ Tᗮ) ∧ (∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2) ∧ (∀ y, ‖P y‖ ≤ ‖y‖) := by
  intro n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `range ι ⊆ T`, and both have dimension `n`, so `range ι = T`
  have hrange : LinearMap.range ι.toLinearMap = T := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨v, rfl⟩
      exact hιT v
    · rw [LinearMap.finrank_range_of_inj ι.injective, finrank_euclideanSpace_fin, hT]
  -- (c): `ι'w` is orthogonal to every `ιv`, hence to `T`
  have hι'T : ∀ w, ι' w ∈ Tᗮ := by
    intro w
    rw [← hrange, Submodule.mem_orthogonal]
    rintro _ ⟨v, rfl⟩
    exact hιι' v w
  -- `range ι' ⊆ Tᗮ`, and both have dimension `(n + k) − n = k`, so `range ι' = Tᗮ`
  have hrange' : LinearMap.range ι'.toLinearMap = Tᗮ := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨w, rfl⟩
      exact hι'T w
    · have h := Submodule.finrank_add_finrank_orthogonal T
      rw [finrank_euclideanSpace_fin, hT] at h
      rw [LinearMap.finrank_range_of_inj ι'.injective, finrank_euclideanSpace_fin]
      omega
  -- `y = p_T y + (y − p_T y) = ιu + ι'w`
  have hdecomp : ∀ y, ∃ u w, y = ι u + ι' w := by
    intro y
    obtain ⟨u, hu⟩ : T.starProjection y ∈ LinearMap.range ι.toLinearMap :=
      hrange ▸ T.starProjection_apply_mem y
    obtain ⟨w, hw⟩ : y - T.starProjection y ∈ LinearMap.range ι'.toLinearMap :=
      hrange' ▸ T.sub_starProjection_mem_orthogonal y
    rw [LinearIsometry.coe_toLinearMap] at hu hw
    exact ⟨u, w, by rw [hu, hw, add_sub_cancel]⟩
  -- `P(ιu + ι'w) = u`
  have hP : ∀ u w, P (ι u + ι' w) = u := fun u w => by rw [map_add, hPι, hPι', add_zero]
  -- (a): `⟪ιu, ιu₀ + ι'w⟫ = ⟪u, u₀⟫ = ⟪u, P(ιu₀ + ι'w)⟫`
  have hadj : ∀ (u : Euclid n) (y : Euclid (n + k)), inner ℝ (ι u) y = inner ℝ u (P y) := by
    intro u y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, inner_add_right, hιι', add_zero, LinearIsometry.inner_map_map]
  -- (b): `p_T(ιu₀ + ι'w) = ιu₀ + 0 = ι(P(ιu₀ + ι'w))`
  have hpT : ∀ y, T.starProjection y = ι (P y) := by
    intro y
    obtain ⟨u₀, w, rfl⟩ := hdecomp y
    rw [hP, map_add, Submodule.starProjection_eq_self_iff.mpr (hιT u₀),
      (T.starProjection_apply_eq_zero_iff).mpr (hι'T w), add_zero]
  -- (d): Pythagoras for `y = p_T y + (y − p_T y)`, with `|p_T y| = |ι(Py)| = |Py|`
  have hpyth : ∀ y, ‖y‖ ^ 2 = ‖P y‖ ^ 2 + ‖y - T.starProjection y‖ ^ 2 := by
    intro y
    have h0 : inner ℝ (T.starProjection y) (y - T.starProjection y) = 0 := by
      rw [real_inner_comm]
      exact T.starProjection_inner_eq_zero y _ (T.starProjection_apply_mem y)
    have h1 : ‖T.starProjection y‖ = ‖P y‖ := by rw [hpT, LinearIsometry.norm_map]
    have h2 := norm_add_sq_real (T.starProjection y) (y - T.starProjection y)
    rw [add_sub_cancel, h0, h1] at h2
    linarith
  -- (e): `|Py|² ≤ |y|²` by (d)
  have hPle : ∀ y, ‖P y‖ ≤ ‖y‖ := by
    intro y
    have h : ‖P y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      rw [hpyth y]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  exact ⟨hadj, hpT, hι'T, hpyth, hPle⟩

/-- **Graph-plane estimates at one point** (Simon Ch. 5, proof of 4.5, (7), (9), (10),
`chapter-05.txt` lines 833–872).  `Q = {ιw + ι'(Lw)}` is the graph plane of `L`, `‖L‖ ≤ 1`, over
`T = ι(ℝⁿ)`, and (Q1), (Q2) are the tilt bounds `|⟨p_Q a, b⟩ − ⟨a, b⟩| ≤ t|a||b|` on `T` and
`|p_Q e|² ≤ t|e|²` on `Tᗮ`.  Let `α` be the Riesz vector of `λ = proj_j ∘ L`.  Every
`q = ιw + ι'(Lw) ∈ Q` has `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩`, so `p_Q(ι'ε_j) = p_Q(ια)` ((7)).  Hence
`⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t`, and (Q1) with `a = b = ια` gives
`‖λ‖² = |ια|² ≤ t + t|ια|² ≤ 2t`.  For `m` with Riesz vector `β`, `⟨ιβ, y⟩ = ⟨β, Py⟩`
(`dorag_tes_gv_adapted_frame`) gives `m(P p_Q(ι'ε_j)) = ⟨p_Q(ια), ιβ⟩`, Parseval gives
`Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`, and (Q1) bounds the difference by `t‖λ‖‖m‖ ≤ t‖m‖`. -/
theorem Submission.dorag_tes_gv_graph_plane_pointwise : ∀ (n k : ℕ) (T Q : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (L : Euclid n →L[ℝ] Euclid k) (j : Fin k) (t : ℝ), Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → Q = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ L.toLinearMap) → ‖L‖ ≤ 1 → 0 ≤ t → (∀ a b : Euclid (n + k), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ t * ‖a‖ * ‖b‖) → (∀ e : Euclid (n + k), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ t * ‖e‖ ^ 2) → ‖(EuclideanSpace.proj j).comp L‖ ^ 2 ≤ 2 * t ∧ ∀ m : Euclid n →L[ℝ] ℝ, |m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) - ∑ i : Fin n, ((EuclideanSpace.proj j).comp L) (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤ t * ‖m‖ := by
  intro n k T Q ι ι' P L j t hT hιι' hιT hPι hPι' hQ hL ht hQ1 hQ2
  obtain ⟨hadj, -, hι'T, -, -⟩ :=
    Submission.dorag_tes_gv_adapted_frame n k T ι ι' P hT hιι' hιT hPι hPι'
  -- `λ = proj_j ∘ L` has `|λw| = |(Lw)_j| ≤ |Lw| ≤ |w|`, so `‖λ‖ ≤ 1`
  have hlamj : ∀ w, (EuclideanSpace.proj j).comp L w = L w j := fun w => rfl
  have hlam1 : ‖(EuclideanSpace.proj j).comp L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    calc ‖(EuclideanSpace.proj j).comp L w‖ = ‖L w j‖ := by rw [hlamj]
      _ ≤ ‖L w‖ := PiLp.norm_apply_le (L w) j
      _ ≤ ‖L‖ * ‖w‖ := L.le_opNorm w
      _ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg w)
  generalize (EuclideanSpace.proj j).comp L = lam at hlam1 hlamj ⊢
  -- Riesz vectors: `⟨γ, w⟩ = μ w` and `|ιγ| = ‖μ‖`
  have riesz : ∀ μ : Euclid n →L[ℝ] ℝ,
      ∃ γ : Euclid n, (∀ w, inner ℝ γ w = μ w) ∧ ‖ι γ‖ = ‖μ‖ := fun μ =>
    ⟨(InnerProductSpace.toDual ℝ (Euclid n)).symm μ, fun _ => InnerProductSpace.toDual_symm_apply,
      by rw [ι.norm_map, LinearIsometryEquiv.norm_map]⟩
  obtain ⟨α, hα, ha⟩ := riesz lam
  -- (7): `ι'ε_j − ια ⊥ Q`, since `⟨q, ι'ε_j⟩ = λw = ⟨q, ια⟩` for `q = ιw + ι'(Lw)`
  have hgraph : Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))) =
      Q.starProjection (ι α) := by
    have hperp : ι' (EuclideanSpace.single j (1 : ℝ)) - ι α ∈ Qᗮ := by
      rw [Submodule.mem_orthogonal]
      intro q hq
      rw [hQ] at hq
      obtain ⟨w, rfl⟩ := LinearMap.mem_range.1 hq
      have h1 : inner ℝ (ι w) (ι' (EuclideanSpace.single j (1 : ℝ))) = 0 := hιι' _ _
      have h2 : inner ℝ (ι' (L w)) (ι' (EuclideanSpace.single j (1 : ℝ))) = lam w := by
        rw [LinearIsometry.inner_map_map, EuclideanSpace.inner_single_right, hlamj]
        simp
      have h3 : inner ℝ (ι w) (ι α) = lam w := by
        rw [LinearIsometry.inner_map_map, real_inner_comm, hα]
      have h4 : inner ℝ (ι' (L w)) (ι α) = 0 := by
        rw [real_inner_comm]
        exact hιι' _ _
      simp only [LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toLinearMap, ContinuousLinearMap.coe_coe]
      rw [inner_sub_right, inner_add_left, inner_add_left, h1, h2, h3, h4]
      ring
    have h0 := (Submodule.starProjection_apply_eq_zero_iff (K := Q)).2 hperp
    rwa [map_sub, sub_eq_zero] at h0
  -- (9): `⟨p_Q(ια), ια⟩ = |p_Q(ια)|² = |p_Q(ι'ε_j)|² ≤ t` by (Q2)
  have hpa : inner ℝ (Q.starProjection (ι α)) (ι α) = ‖Q.starProjection (ι α)‖ ^ 2 := by
    have h := Submodule.starProjection_inner_eq_zero (K := Q) (ι α) _
      (Q.starProjection_apply_mem (ι α))
    rw [inner_sub_left, sub_eq_zero] at h
    rw [real_inner_comm, h, real_inner_self_eq_norm_sq]
  have hpa_le : ‖Q.starProjection (ι α)‖ ^ 2 ≤ t := by
    have h := hQ2 _ (hι'T (EuclideanSpace.single j (1 : ℝ)))
    have he : ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
    rwa [he, one_pow, mul_one, hgraph] at h
  refine ⟨?_, fun m => ?_⟩
  · -- (Q1) with `a = b = ια`: `|ια|² ≤ |p_Q(ια)|² + t|ια|² ≤ t + t`
    have h := hQ1 (ι α) (ι α) (hιT α) (hιT α)
    rw [hpa, real_inner_self_eq_norm_sq, ha] at h
    have hsq : ‖lam‖ * ‖lam‖ ≤ 1 := by nlinarith [norm_nonneg lam]
    nlinarith [(abs_le.1 h).1, mul_le_mul_of_nonneg_left hsq ht]
  · -- (10): with `β` the Riesz vector of `m`, `m(P y) = ⟨β, P y⟩ = ⟨ιβ, y⟩`
    obtain ⟨β, hβ, hb⟩ := riesz m
    have hmP : m (P (Q.starProjection (ι' (EuclideanSpace.single j (1 : ℝ))))) =
        inner ℝ (Q.starProjection (ι α)) (ι β) := by
      rw [← hβ, ← hadj, hgraph, real_inner_comm]
    -- Parseval in the basis `(eᵢ)`: `Σᵢ λ(eᵢ)m(eᵢ) = ⟨α, β⟩ = ⟨ια, ιβ⟩`
    have hsum : ∑ i : Fin n, lam (EuclideanSpace.single i (1 : ℝ)) *
        m (EuclideanSpace.single i (1 : ℝ)) = inner ℝ (ι α) (ι β) := by
      rw [LinearIsometry.inner_map_map,
        ← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner α β]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.basisFun_apply, hα, real_inner_comm, hβ]
    rw [hmP, hsum]
    calc |inner ℝ (Q.starProjection (ι α)) (ι β) - inner ℝ (ι α) (ι β)|
        ≤ t * ‖ι α‖ * ‖ι β‖ := hQ1 _ _ (hιT α) (hιT β)
      _ = t * ‖lam‖ * ‖m‖ := by rw [ha, hb]
      _ ≤ t * 1 * ‖m‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam1 ht) (norm_nonneg m)
      _ = t * ‖m‖ := by rw [mul_one]
/-- First variation of a vertical field (Simon Ch. 4, 2.2–2.3): for differentiable `ζ` and a
fixed `e`, `D(ζe)(x) = Dζ(x)(·) e`, so `p_x ∘ D(ζe)(x)` is the rank-one map `y ↦ Dζ(x)(y) p_x e`
and `div_M(ζe)(x) = Dζ(x)(p_x e)`.  As `μ_V = (Hⁿ⌞M).withDensity θ` with `θ` measurable and
finite, `δV(ζe) = ∫_M θ Dζ(x)(p_x e) dHⁿ = ∫ Dζ(x)(p_x e) dμ_V`, with no integrability needed. -/
theorem Submission.dorag_tes_gv_vertical_field_first_variation : ∀ (m n : ℕ) (U : Set (Euclid m)) (R : IMRep U n) (ζ : Euclid m → ℝ) (e : Euclid m), Differentiable ℝ ζ → R.firstVariation (fun x => ζ x • e) = ∫ x, fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure := by
  intro m n U R ζ e hζ
  -- `div_M(ζe)(x) = trace(p_x ∘ Dζ(x).smulRight e) = trace(Dζ(x).smulRight (p_x e)) = Dζ(x)(p_x e)`
  have hdiv : ∀ x, tangentialDivergence n R.carrier (fun x => ζ x • e) x =
      fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection e) := by
    intro x
    unfold tangentialDivergence
    rw [fderiv_smul_const (hζ x) e]
    have hrank : (approxTangentPlane n R.carrier x).starProjection.toLinearMap ∘ₗ
        ((fderiv ℝ ζ x).smulRight e).toLinearMap =
        (fderiv ℝ ζ x).toLinearMap.smulRight
          ((approxTangentPlane n R.carrier x).starProjection e) := by
      ext y
      simp [map_smul]
    rw [hrank, LinearMap.trace_smulRight]
    rfl
  -- `μ_V = (Hⁿ⌞M).withDensity θ`, `θ` measurable and finite: `∫ g dμ_V = ∫_M θ g dHⁿ` for all `g`
  unfold IMRep.firstVariation IMRep.measure
  have hmeas : Measurable fun x => ((R.mult x : ℕ) : ℝ≥0∞) :=
    measurable_from_nat.comp R.measurable_mult
  rw [integral_withDensity_eq_integral_toReal_smul hmeas (Eventually.of_forall fun x => by simp)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hdiv x, ENNReal.toReal_natCast, smul_eq_mul]
/-- **Cutoff extension along a projection** (Steps 3.1–3.3 of the graph first-variation estimate):
if `n ≥ 1`, `ζ ∈ C¹(ℝⁿ)` has `tsupport ζ ⊆ B̆_{r/2}(0)` and `‖Dζ‖ ≤ G`, then
`ψ = (ζ ∘ φ) h₀`, `φ(x) = P(x − ξ)`, with `h₀` the `ContDiffBump` at `ξ` of radii `7r/8 < r`, is
`C¹` with compact support in `B_r(ξ)` and `|ψ| ≤ Gr/2` (`ζ` is `G`-Lipschitz and vanishes on the
sphere `|v| = r/2`).  If `|x − ξ|² ≤ |φ(x)|² + r²/16`, then `Dψ(x) = Dζ(φ(x)) ∘ P`: for
`|φ(x)| < r/2` we get `|x − ξ| < 7r/8`, so `h₀ = 1` near `x`; for `|φ(x)| ≥ r/2` both sides
vanish, `φ(x)` lying outside `tsupport ζ`. -/
theorem Submission.dorag_tes_gv_cutoff_extension : ∀ (n m : ℕ), 0 < n → ∀ (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ), 0 < r → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ∃ ψ : Euclid m → ℝ, ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ closedBall ξ r ∧ (∀ x, |ψ x| ≤ G * (r / 2)) ∧ ∀ x, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 → fderiv ℝ ψ x = (fderiv ℝ ζ (P (x - ξ))).comp P := by
  intro n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hζdiff : Differentiable ℝ ζ := hζ.differentiable one_ne_zero
  -- `ζ` is `G`-Lipschitz and vanishes outside `B̆_{r/2}(0)`
  have hζlip : ∀ v w, |ζ v - ζ w| ≤ G * ‖v - w‖ := by
    intro v w
    simpa [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (fun x _ => hζdiff x) (fun x _ => hζG x) (mem_univ w) (mem_univ v)
  have hζs' : ∀ v, r / 2 ≤ ‖v‖ → v ∉ tsupport ζ := by
    intro v hv h
    have := hζs h
    rw [mem_ball, dist_zero_right] at this
    linarith
  -- `|ζ v| ≤ G r/2`: compare `v` with `w = v + (r/2 − |v|) u` on the sphere `|w| = r/2`
  have hζsup : ∀ v, |ζ v| ≤ G * (r / 2) := by
    intro v
    by_cases hv : r / 2 ≤ ‖v‖
    · rw [image_eq_zero_of_notMem_tsupport (hζs' v hv), abs_zero]
      positivity
    · replace hv := not_le.mp hv
      obtain ⟨u, hu1, hu⟩ : ∃ u : Euclid n, ‖u‖ = 1 ∧ ‖v + (r / 2 - ‖v‖) • u‖ = r / 2 := by
        by_cases hv0 : v = 0
        · refine ⟨EuclideanSpace.single ⟨0, hn⟩ (1 : ℝ), by simp, ?_⟩
          subst hv0
          simp [norm_smul, abs_of_pos hr]
        · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
          refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne'], ?_⟩
          have : v + (r / 2 - ‖v‖) • (‖v‖⁻¹ • v) = ((r / 2) / ‖v‖) • v := by
            rw [smul_smul, ← one_smul ℝ v, smul_smul, ← add_smul, one_smul]
            congr 1
            field_simp
            ring
          rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity),
            div_mul_cancel₀ _ hvpos.ne']
      have hw : ζ (v + (r / 2 - ‖v‖) • u) = 0 := image_eq_zero_of_notMem_tsupport (hζs' _ hu.ge)
      calc |ζ v| = |ζ v - ζ (v + (r / 2 - ‖v‖) • u)| := by rw [hw, sub_zero]
        _ ≤ G * ‖v - (v + (r / 2 - ‖v‖) • u)‖ := hζlip _ _
        _ = G * (r / 2 - ‖v‖) := by
            rw [sub_add_cancel_left, norm_neg, norm_smul, hu1, mul_one, Real.norm_eq_abs,
              abs_of_pos (by linarith)]
        _ ≤ G * (r / 2) := by gcongr; linarith [norm_nonneg v]
  -- `ψ = (ζ ∘ φ) h₀`, `φ(y) = P(y − ξ)`
  let h0 : ContDiffBump ξ := ⟨7 * r / 8, r, by positivity, by linarith⟩
  have hφd : ∀ x, HasFDerivAt (fun y : Euclid m => P (y - ξ)) P x := by
    intro x
    have h := P.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const ξ)
    rwa [ContinuousLinearMap.comp_id] at h
  have hφc : Continuous (fun y : Euclid m => P (y - ξ)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  refine ⟨fun x => ζ (P (x - ξ)) * h0 x, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hζ.comp (P.contDiff.comp (contDiff_id.sub contDiff_const))).mul h0.contDiff
  · exact HasCompactSupport.mul_left (f := fun x => ζ (P (x - ξ))) h0.hasCompactSupport
  · exact tsupport_mul_subset_right.trans h0.tsupport_eq.subset
  · intro x
    rw [abs_mul, abs_of_nonneg h0.nonneg]
    calc |ζ (P (x - ξ))| * h0 x ≤ G * (r / 2) * 1 :=
          mul_le_mul (hζsup _) h0.le_one h0.nonneg (by positivity)
      _ = G * (r / 2) := mul_one _
  · intro x hx
    by_cases hφ : ‖P (x - ξ)‖ < r / 2
    · -- `|x − ξ|² < r²/4 + r²/16 < (7r/8)²`, so `h₀ = 1` near `x` and the chain rule applies
      have hx' : ‖x - ξ‖ < 7 * r / 8 := by
        have h1 : ‖x - ξ‖ ^ 2 < (7 * r / 8) ^ 2 := by nlinarith [norm_nonneg (P (x - ξ))]
        nlinarith [norm_nonneg (x - ξ)]
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun y => ζ (P (y - ξ)) := by
        filter_upwards [h0.eventuallyEq_one_of_mem_ball (show x ∈ ball ξ (7 * r / 8) by
          rwa [mem_ball, dist_eq_norm])] with y hy
        rw [hy, Pi.one_apply, mul_one]
      rw [hev.fderiv_eq]
      exact ((hζdiff _).hasFDerivAt.comp x (hφd x)).fderiv
    · -- `φ = P(· − ξ)` maps a neighbourhood of `x` outside `tsupport ζ`: both sides vanish
      have hns := hζs' _ (not_lt.mp hφ)
      have hev : (fun y => ζ (P (y - ξ)) * h0 y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [((isClosed_tsupport ζ).isOpen_compl.preimage hφc).mem_nhds hns] with y hy
        rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
      rw [hev.fderiv_eq, fderiv_of_notMem_tsupport ℝ hns]
      simp

/-- **First-variation bound for vertical cutoff fields** (Simon Ch. 5, proof of 4.5: the
first-variation identity (6) tested with the vertical field `X = ζ̃ e`).  Let `R` satisfy
`δV(X) = −∫ X · H dμ` for `X ∈ C¹_c` with `spt X ⊆ W ⊆ U`, where `|H| ≤ κ`, `μ = μ_V`, and
`x ↦ p_{TₓM}` is `μ`-measurable.  Let `B_r(ξ) ⊆ W`, `|Py| ≤ |y|`, and
`|x − ξ|² ≤ |P(x − ξ)|² + r²/16` on `spt μ ∩ B_r(ξ)`.  If `ζ ∈ C¹_c(ℝⁿ)`,
`spt ζ ⊆ B̆ⁿ_{r/2}(0)`, `‖Dζ‖ ≤ G` and `|e| ≤ 1`, then `u(x) = Dζ(P(x − ξ))(P(p_{TₓM} e))` is
`μ`-integrable on `B_r(ξ)` and `|∫_{B_r(ξ)} u dμ| ≤ G (κr/2) μ(B_r(ξ))`.
Proof: extend `ζ` to the cutoff `ψ` of `dorag_tes_gv_cutoff_extension`, test with `X = ψ e`,
compute `δV(X) = ∫ Dψ(p_{TₓM} e) dμ` by `dorag_tes_gv_vertical_field_first_variation`, localize
to `B_r(ξ)` (where `Dψ = Dζ(P(· − ξ)) ∘ P` on the conull set `spt μ`), and bound
`|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`. -/
theorem Submission.dorag_tes_gv_vertical_variation_bound : ∀ (n m : ℕ), 0 < n → ∀ (U W : Set (Euclid m)) (R : IMRep U n) (H : Euclid m → Euclid m) (κ : ℝ) (ξ : Euclid m) (r : ℝ) (P : Euclid m →L[ℝ] Euclid n) (ζ : Euclid n → ℝ) (G : ℝ) (e : Euclid m), W ⊆ U → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid m → Euclid m, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → (∀ y, ‖P y‖ ≤ ‖y‖) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16) → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ‖e‖ ≤ 1 → IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure ∧ ENNReal.ofReal |∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure| ≤ ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
  intro n m hn U W R H κ ξ r P ζ G e hWU hHκ hFV hp hr hBW hPle hspt hζ hζc hζs hζG he
  -- Step 1: `G, κ ≥ 0`.
  have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `μ(B_r(ξ)) < ∞`, since `B_r(ξ)` is a compact subset of `U`.
  have hfin : R.measure (closedBall ξ r) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall ξ r) (hBW.trans hWU)
  -- Step 3: the cutoff `ψ` extending `ζ ∘ P(· − ξ)`.
  obtain ⟨ψ, hψ, hψc, hψs, hψb, hψd⟩ :=
    Submission.dorag_tes_gv_cutoff_extension n m hn ξ r P ζ G hr hζ hζc hζs hζG
  have hψ0 : ∀ x, x ∉ closedBall ξ r → ψ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hψs h)
  -- Step 4: `X = ψ e` is an admissible test field.
  have hX : ContDiff ℝ 1 (fun x => ψ x • e) := hψ.smul contDiff_const
  have hXc : HasCompactSupport (fun x => ψ x • e) := hψc.smul_right
  have hXs : tsupport (fun x => ψ x • e) ⊆ W :=
    (tsupport_smul_subset_left _ _).trans (hψs.trans hBW)
  have hfv : R.firstVariation (fun x => ψ x • e) =
      -∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure := hFV _ hX hXc hXs
  -- Step 5: `δV(ψ e) = ∫ Dψ(x)(p_{TₓM} e) dμ`.
  rw [Submission.dorag_tes_gv_vertical_field_first_variation m n U R ψ e
    (hψ.differentiable one_ne_zero)] at hfv
  -- Step 6: localization to `B_r(ξ)`, where `Dψ = Dζ(P(· − ξ)) ∘ P` on `spt μ`.
  have hloc : ∫ x, fderiv ℝ ψ x ((approxTangentPlane n R.carrier x).starProjection e) ∂R.measure =
      ∫ x in closedBall ξ r, fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection e)) ∂R.measure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := closedBall ξ r)]
    · refine setIntegral_congr_ae measurableSet_closedBall ?_
      filter_upwards [Measure.support_mem_ae (μ := R.measure)] with x hxs hxB
      rw [hψd x (hspt x ⟨hxs, hxB⟩), ContinuousLinearMap.comp_apply]
    · intro x hx
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hψs h)), zero_apply]
  -- Step 8: `|ψ e · H| ≤ (Gr/2) κ 1_{B_r(ξ)}`, hence the bound on `∫ ψ e · H dμ`.
  have hpt : ∀ x, ‖inner ℝ (ψ x • e) (H x)‖ ≤
      (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x := by
    intro x
    by_cases hx : x ∈ closedBall ξ r
    · rw [indicator_of_mem hx, real_inner_smul_left, norm_mul, Real.norm_eq_abs,
        Real.norm_eq_abs]
      have heH : |inner ℝ e (H x)| ≤ κ :=
        calc |inner ℝ e (H x)| ≤ ‖e‖ * ‖H x‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * κ := mul_le_mul he (hHκ x) (norm_nonneg _) zero_le_one
          _ = κ := one_mul κ
      exact mul_le_mul (hψb x) heH (abs_nonneg _) (by positivity)
    · rw [indicator_of_notMem hx, hψ0 x hx, zero_smul, inner_zero_left, norm_zero]
  have hbd : |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure| ≤
      G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure‖
        ≤ ∫ x, (closedBall ξ r).indicator (fun _ => G * (r / 2) * κ) x ∂R.measure :=
          norm_integral_le_of_norm_le
            ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hfin))
            (Eventually.of_forall hpt)
      _ = G * (r / 2) * κ * R.measure.real (closedBall ξ r) := by
          rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
  -- Step 10: `u` is a.e. strongly measurable and bounded by `G`, hence integrable on `B_r(ξ)`.
  have hmeas : AEStronglyMeasurable (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) R.measure := by
    have hDζ : Continuous fun x : Euclid m => fderiv ℝ ζ (P (x - ξ)) :=
      (hζ.continuous_fderiv one_ne_zero).comp
        (P.continuous.comp (continuous_id.sub continuous_const))
    exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hDζ.aestronglyMeasurable.prodMk
        (P.continuous.comp_aestronglyMeasurable (hp.apply_continuousLinearMap e)))
  have hint : IntegrableOn (fun x => fderiv ℝ ζ (P (x - ξ))
      (P ((approxTangentPlane n R.carrier x).starProjection e))) (closedBall ξ r) R.measure := by
    refine Measure.integrableOn_of_bounded (M := G) hfin hmeas (Eventually.of_forall fun x => ?_)
    calc ‖fderiv ℝ ζ (P (x - ξ)) (P ((approxTangentPlane n R.carrier x).starProjection e))‖
        ≤ ‖fderiv ℝ ζ (P (x - ξ))‖ *
            ‖P ((approxTangentPlane n R.carrier x).starProjection e)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ G * 1 := mul_le_mul (hζG _)
          ((hPle _).trans ((Submodule.norm_starProjection_apply_le _ _).trans he))
          (norm_nonneg _) hG
      _ = G := mul_one G
  -- Steps 7 and 9: `∫_{B_r(ξ)} u dμ = −∫ ψ e · H dμ`, then pass to `ℝ≥0∞`.
  refine ⟨hint, ?_⟩
  rw [← hloc, hfv, abs_neg]
  calc ENNReal.ofReal |∫ x, inner ℝ (ψ x • e) (H x) ∂R.measure|
      ≤ ENNReal.ofReal (G * (κ * r / 2 * R.measure.real (closedBall ξ r))) :=
        ENNReal.ofReal_le_ofReal (hbd.trans_eq (by ring))
    _ = ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
        rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_mul (by positivity), ofReal_measureReal hfin]
/-- Splitting estimate for set integrals (the splitting of `B_r(ξ)` into the graph part and its
complement in the graph first-variation estimate, for abstract integrands).  If `g` is integrable
on `A`, then `∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g)`; the first term is bounded by `C`, the
second by `G μ(B ∖ F)` (as `|u| ≤ G` on `B` and `u = 0` on `(B ∖ A) ∩ F`), and the third by
`G ∫_B t` (as `|u − g| ≤ G t` on `A ⊆ B`).  Otherwise `∫_A g = 0`. -/
theorem Submission.dorag_tes_gv_split_integral_estimate : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (A B F : Set X) (u g t : X → ℝ) (G : ℝ) (C : ℝ≥0∞), MeasurableSet A → MeasurableSet B → MeasurableSet F → A ⊆ B → 0 ≤ G → IntegrableOn u B μ → ENNReal.ofReal |∫ x in B, u x ∂μ| ≤ C → (∀ᵐ x ∂μ, x ∈ B → |u x| ≤ G) → (∀ᵐ x ∂μ, x ∈ B → x ∉ A → x ∈ F → u x = 0) → (∀ᵐ x ∂μ, x ∈ A → |u x - g x| ≤ G * t x) → ENNReal.ofReal |∫ x in A, g x ∂μ| ≤ ENNReal.ofReal G * (∫⁻ x in B, ENNReal.ofReal (t x) ∂μ + μ (B \ F)) + C := by
  intro X _ μ A B F u g t G C hA hB hF hAB hG hu hC hbd hzero hdiff
  -- if `g` is not integrable on `A`, the left side is `ofReal |0| = 0`
  by_cases hg : IntegrableOn g A μ
  swap
  · rw [integral_undef hg]
    simp
  -- `∫_A g = ∫_B u − ∫_{B∖A} u − ∫_A (u − g)`
  have huA : IntegrableOn u A μ := hu.mono_set hAB
  have hgA : ∫ x in A, g x ∂μ =
      ∫ x in B, u x ∂μ - ∫ x in B \ A, u x ∂μ - ∫ x in A, (u x - g x) ∂μ := by
    rw [integral_sub huA hg, ← integral_inter_add_sdiff hA hu, inter_eq_right.mpr hAB]
    ring
  -- off `A`: `‖u‖ₑ ≤ ofReal G · 1_{X∖F}` a.e. on `B ∖ A`
  have hoff : ENNReal.ofReal |∫ x in B \ A, u x ∂μ| ≤ ENNReal.ofReal G * μ (B \ F) := by
    calc ENNReal.ofReal |∫ x in B \ A, u x ∂μ| = ‖∫ x in B \ A, u x ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ x in B \ A, ‖u x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in B \ A, Fᶜ.indicator (fun _ => ENNReal.ofReal G) x ∂μ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' (hB.diff hA)]
          filter_upwards [hbd, hzero] with x hxbd hxzero hx
          by_cases hxF : x ∈ F
          · simp [hxzero hx.1 hx.2 hxF]
          · rw [indicator_of_mem (mem_compl hxF), Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hxbd hx.1)
      _ = ENNReal.ofReal G * μ (Fᶜ ∩ (B \ A)) := by
          rw [lintegral_indicator_const hF.compl, Measure.restrict_apply hF.compl]
      _ ≤ ENNReal.ofReal G * μ (B \ F) := by
          gcongr
          exact fun x hx => ⟨hx.2.1, hx.1⟩
  -- on `A`: `‖u − g‖ₑ ≤ ofReal G · ofReal t` a.e. on `A`, and `A ⊆ B`
  have hon : ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| ≤
      ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
    calc ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| = ‖∫ x in A, (u x - g x) ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ x in A, ‖u x - g x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in A, ENNReal.ofReal G * ENNReal.ofReal (t x) ∂μ := by
          refine lintegral_mono_ae ?_
          rw [ae_restrict_iff' hA]
          filter_upwards [hdiff] with x hx hxA
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hG]
          exact ENNReal.ofReal_le_ofReal (hx hxA)
      _ = ENNReal.ofReal G * ∫⁻ x in A, ENNReal.ofReal (t x) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
          gcongr
  -- triangle inequality and subadditivity of `ofReal`, then the three bounds
  calc ENNReal.ofReal |∫ x in A, g x ∂μ|
      ≤ ENNReal.ofReal (|∫ x in B, u x ∂μ| + |∫ x in B \ A, u x ∂μ| +
          |∫ x in A, (u x - g x) ∂μ|) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hgA]
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ ENNReal.ofReal |∫ x in B, u x ∂μ| + ENNReal.ofReal |∫ x in B \ A, u x ∂μ| +
          ENNReal.ofReal |∫ x in A, (u x - g x) ∂μ| := by
        refine ENNReal.ofReal_add_le.trans ?_
        gcongr
        exact ENNReal.ofReal_add_le
    _ ≤ C + ENNReal.ofReal G * μ (B \ F) +
          ENNReal.ofReal G * ∫⁻ x in B, ENNReal.ofReal (t x) ∂μ := by
        gcongr
    _ = ENNReal.ofReal G * (∫⁻ x in B, ENNReal.ofReal (t x) ∂μ + μ (B \ F)) + C := by
        ring
/-- **Hilbert–Schmidt inequalities for orthogonal projections** (Simon Ch. 5, Remark 4.4 and
(10)–(11) in the proof of 4.5; chapter-05.txt lines 715–737, 869–883).  Write
`eᵢ = EuclideanSpace.single i 1`, `|A|² = Σᵢ ‖A eᵢ‖²` and `p_Q = Q.starProjection`.  Then
(a) `‖A y‖² ≤ |A|² ‖y‖²` (operator norm `≤` inner product norm); (b)
`|p_S − p_T|² ≤ 2|p_Q − p_S|² + 2|p_Q − p_T|²`; (c) `|⟨p_Q a, b⟩ − ⟨a, b⟩| ≤ |p_Q − p_T|² ‖a‖ ‖b‖`
for `a, b ∈ T`, since `⟨p_Q a, b⟩ − ⟨a, b⟩ = −⟨(p_Q − p_T) a, (p_Q − p_T) b⟩`; (d)
`‖p_Q e‖² ≤ |p_Q − p_T|² ‖e‖²` for `e ∈ Tᗮ`, since `p_Q e = (p_Q − p_T) e`. -/
theorem Submission.dorag_tes_projection_algebra : ∀ (N : ℕ), (∀ (A : Euclid N →L[ℝ] Euclid N) (y : Euclid N), ‖A y‖ ^ 2 ≤ (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖y‖ ^ 2) ∧ (∀ Q S T : Submodule ℝ (Euclid N), ∑ i : Fin N, ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 + 2 * ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∧ (∀ (Q T : Submodule ℝ (Euclid N)) (a b : Euclid N), a ∈ T → b ∈ T → |inner ℝ (Q.starProjection a) b - inner ℝ a b| ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖a‖ * ‖b‖) ∧ ∀ (Q T : Submodule ℝ (Euclid N)) (e : Euclid N), e ∈ Tᗮ → ‖Q.starProjection e‖ ^ 2 ≤ (∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖e‖ ^ 2 := by
  intro N
  -- (a): `y = Σᵢ yᵢ eᵢ`, so `‖Ay‖ ≤ Σᵢ |yᵢ| ‖Aeᵢ‖`; then Cauchy–Schwarz and `Σᵢ yᵢ² = ‖y‖²`.
  have ha : ∀ (A : Euclid N →L[ℝ] Euclid N) (y : Euclid N), ‖A y‖ ^ 2 ≤
      (∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖y‖ ^ 2 := by
    intro A y
    have hAy : A y = ∑ i : Fin N, y i • A (EuclideanSpace.single i (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr y]
      simp [map_sum, map_smul]
    have h1 : ‖A y‖ ≤ ∑ i : Fin N, |y i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [hAy]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      simp [norm_smul]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin N => |y i|)
      (fun i => ‖A (EuclideanSpace.single i (1 : ℝ))‖)
    have h3 : ∑ i : Fin N, |y i| ^ 2 = ‖y‖ ^ 2 := by
      simp [EuclideanSpace.real_norm_sq_eq]
    calc ‖A y‖ ^ 2 ≤ (∑ i : Fin N, |y i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ i : Fin N, |y i| ^ 2) * ∑ i : Fin N, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := h2
      _ = _ := by rw [h3, mul_comm]
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b): termwise `‖sᵢ − tᵢ‖ ≤ ‖qᵢ − sᵢ‖ + ‖qᵢ − tᵢ‖` and `(u + w)² ≤ 2u² + 2w²`.
    intro Q S T
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h : ‖S.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ≤
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ +
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ := by
      rw [norm_sub_rev (Q.starProjection _) (S.starProjection _)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    nlinarith [mul_self_le_mul_self (norm_nonneg _) h,
      sq_nonneg (‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ -
        ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T.starProjection (EuclideanSpace.single i (1 : ℝ))‖)]
  · -- (c): with `B = p_Q − p_T`, `⟨p_Q a, b⟩ − ⟨a, b⟩ = −⟨Ba, Bb⟩`; Cauchy–Schwarz and (a).
    intro Q T a b haT hbT
    have hBa := ha (Q.starProjection - T.starProjection) a
    have hBb := ha (Q.starProjection - T.starProjection) b
    simp only [sub_apply, Submodule.starProjection_eq_self_iff.mpr haT,
      Submodule.starProjection_eq_self_iff.mpr hbT] at hBa hBb
    have hid : inner ℝ (Q.starProjection a) b - inner ℝ a b =
        -inner ℝ (Q.starProjection a - a) (Q.starProjection b - b) := by
      have h1 : inner ℝ (Q.starProjection a) (Q.starProjection b) =
          inner ℝ (Q.starProjection a) b := by
        rw [Submodule.inner_starProjection_left_eq_right Q a,
          Submodule.starProjection_eq_self_iff.mpr (Q.starProjection_apply_mem b),
          ← Submodule.inner_starProjection_left_eq_right Q a]
      have h2 : inner ℝ a (Q.starProjection b) = inner ℝ (Q.starProjection a) b :=
        (Submodule.inner_starProjection_left_eq_right Q a b).symm
      simp only [inner_sub_left, inner_sub_right, h1, h2]
      ring
    rw [hid, abs_neg]
    refine (abs_real_inner_le_norm _ _).trans ?_
    set H := ∑ i : Fin N, ‖Q.starProjection (EuclideanSpace.single i (1 : ℝ)) -
      T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    have hH : 0 ≤ H := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsq : (‖Q.starProjection a - a‖ * ‖Q.starProjection b - b‖) ^ 2 ≤
        (H * ‖a‖ * ‖b‖) ^ 2 := by
      calc (‖Q.starProjection a - a‖ * ‖Q.starProjection b - b‖) ^ 2 =
            ‖Q.starProjection a - a‖ ^ 2 * ‖Q.starProjection b - b‖ ^ 2 := by ring
        _ ≤ (H * ‖a‖ ^ 2) * (H * ‖b‖ ^ 2) :=
          mul_le_mul hBa hBb (sq_nonneg _) (mul_nonneg hH (sq_nonneg _))
        _ = (H * ‖a‖ * ‖b‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (mul_nonneg hH (norm_nonneg _)) (norm_nonneg _)) two_ne_zero).mp hsq
  · -- (d): `p_T e = 0`, so `p_Q e = (p_Q − p_T) e`; then (a).
    intro Q T e he
    have hBe := ha (Q.starProjection - T.starProjection) e
    simp only [sub_apply,
      (Submodule.starProjection_apply_eq_zero_iff T).mpr he, sub_zero] at hBe
    exact hBe
/-- Squared columns of a derivative are bounded by its squared rows: for any `f : ℝⁿ → ℝᵏ` and
`v`, `Σᵢ |Df(v)eᵢ|² ≤ Σⱼ ‖Dfʲ(v)‖²`, where `fʲ = projⱼ ∘ f`.  If `f` is not differentiable at `v`,
then `Df(v) = 0` and the left side is `0`.  Otherwise `Dfʲ(v) = projⱼ ∘ Df(v)` by the chain rule;
the Riesz representative `u` of a functional `ψ` on `ℝⁿ` has `|u| = ‖ψ‖` and `uᵢ = ⟨u, eᵢ⟩ = ψ(eᵢ)`,
so `‖ψ‖² = Σᵢ ψ(eᵢ)²`, and exchanging the two finite sums gives equality. -/
theorem Submission.dorag_tes_gt_fderiv_columns_sq_le_rows_sq : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 := by
  intro n k f v
  by_cases hf : DifferentiableAt ℝ f v
  · have hrow : ∀ ψ : Euclid n →L[ℝ] ℝ,
        ∑ i : Fin n, ψ (EuclideanSpace.single i (1 : ℝ)) ^ 2 = ‖ψ‖ ^ 2 := by
      intro ψ
      rw [← LinearIsometryEquiv.norm_map (InnerProductSpace.toDual ℝ (Euclid n)).symm ψ,
        EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right, one_mul,
        conj_trivial]
    have hder : ∀ j : Fin k, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v =
        (EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).comp (fderiv ℝ f v) := fun j =>
      ((EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).hasFDerivAt.comp v hf.hasFDerivAt).fderiv
    refine le_of_eq ?_
    calc ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
        = ∑ i : Fin n, ∑ j : Fin k, fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ)) j ^ 2 :=
          Finset.sum_congr rfl fun i _ => EuclideanSpace.real_norm_sq_eq _
      _ = ∑ j : Fin k, ∑ i : Fin n, fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ)) j ^ 2 :=
          Finset.sum_comm
      _ = ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [hder j, ← hrow]; rfl
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp only [zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
/-- Exceptional parameter set for the multiplicity-one graph measure.  Let `μ = θ Hⁿ⌞M` be the
weight of `R = (M, θ, ·)`, `Φ(v) = ξ + ιv + ι'f(v)` with `|f(v) - f(w)| ≤ |v - w|`,
`|f| ≤ r/4`, `P ∘ ι = id`, `P ∘ ι' = 0`, and `D = B_{r/2}(0)`.  If `θ = 1` `μ`-a.e. on
`B̄_r(ξ) ⊆ W ⊆ U`, `Hⁿ((spt μ ∩ W) \ M) = 0` and `Hⁿ((range Φ \ spt μ) ∩ B̄_r(ξ)) ≤ a`, then
`μ(Φ(D)) < ∞`, and `Z = D ∩ Φ⁻¹(Mᶜ ∪ {θ ≠ 1})` is a Borel set with `Hⁿ(Φ(Z)) ≤ a` and
`∫_{Φ(D)} h dμ = ∫_{Φ(D \ Z)} h dHⁿ`.  As `P(Φ(v) - ξ) = v`, `Φ` is a continuous injection, so
`Φ(D)` is Borel; `Φ(D) ⊆ B̄_r(ξ)` by the triangle inequality, so `μ(Φ(D)) ≤ μ(B̄_r(ξ)) < ∞` by
local integrability of `θ`.  As `θ > 0` on `M`, `θ = 1` `Hⁿ`-a.e. on `M ∩ B̄_r(ξ)`; hence
`μ⌞Φ(D) = θ Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞Φ(D \ Z)`, and `Φ(Z)` lies in the union of
`(range Φ \ spt μ) ∩ B̄_r(ξ)`, `(spt μ ∩ W) \ M` and the null set `M ∩ B̄_r(ξ) ∩ {θ ≠ 1}`. -/
theorem Submission.dorag_tes_gt_graph_measure_exceptional_set : ∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), W ⊆ U → 0 < r → closedBall ξ r ⊆ W → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → R.measure ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) ≠ ∞ ∧ ∃ Z : Set (Euclid n), MeasurableSet Z ∧ μHE[n] ((fun v => ξ + ι v + ι' (f v)) '' Z) ≤ ENNReal.ofReal a ∧ ∀ h : Euclid (n + k) → ℝ≥0∞, Measurable h → ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h x ∂R.measure = ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' (ball (0 : Euclid n) (r / 2) \ Z), h x ∂μHE[n] := by
  intro n k U W R ξ r a ι ι' P f hWU _ hBW hPι hPι' hf hfr H1 H2 H3
  set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v) with hΦ
  set D : Set (Euclid n) := ball 0 (r / 2)
  have hμ : R.measure = (μHE[n].restrict R.carrier).withDensity fun x => (R.mult x : ℝ≥0∞) :=
    rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  -- `Φ` is continuous and injective (`P (Φ v - ξ) = v`), so `Φ '' D` is Borel.
  have hfc : Continuous f :=
    (LipschitzWith.mk_one fun v w => by simpa only [dist_eq_norm] using hf v w).continuous
  have hΦc : Continuous Φ := (continuous_const.add ι.continuous).add (ι'.continuous.comp hfc)
  have hΦξ : ∀ v, Φ v - ξ = ι v + ι' (f v) := fun v => by
    simp only [hΦ]
    abel
  have hPΦ : ∀ v, P (Φ v - ξ) = v := fun v => by rw [hΦξ, map_add, hPι, hPι', add_zero]
  have hΦD : MeasurableSet (Φ '' D) :=
    measurableSet_ball.image_of_continuousOn_injOn hΦc.continuousOn
      fun v _ w _ hvw => by rw [← hPΦ v, ← hPΦ w, hvw]
  -- `Φ` maps `D` into `closedBall ξ r`.
  have hΦB : ∀ v ∈ D, Φ v ∈ closedBall ξ r := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm, hΦξ]
    have hv' : ‖v‖ < r / 2 := mem_ball_zero_iff.1 hv
    calc ‖ι v + ι' (f v)‖ ≤ ‖ι v‖ + ‖ι' (f v)‖ := norm_add_le _ _
      _ = ‖v‖ + ‖f v‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
      _ ≤ r := by linarith [hfr v]
  -- `θ = 1` holds `Hⁿ`-a.e. on `M ∩ closedBall ξ r`, as `θ ≠ 0` on `M`.
  have H1' : ∀ᵐ x ∂μHE[n], x ∈ R.carrier → x ∈ closedBall ξ r → R.mult x = 1 := by
    rw [hμ, ae_withDensity_iff hθ, ae_restrict_iff' R.measurableSet_carrier] at H1
    filter_upwards [H1] with x hx hxM
    exact hx hxM (Nat.cast_ne_zero.2 (R.mult_pos x hxM).ne')
  set N := {x | x ∈ R.carrier ∧ x ∈ closedBall ξ r ∧ R.mult x ≠ 1}
  have hN : μHE[n] N = 0 := by
    refine measure_mono_null ?_ (ae_iff.1 H1')
    intro x hx
    simp only [mem_ofPred_eq, not_imp]
    exact hx
  set Z := D ∩ Φ ⁻¹' (R.carrierᶜ ∪ {x | R.mult x ≠ 1})
  refine ⟨?_, Z, ?_, ?_, ?_⟩
  · -- `μ (Φ '' D) ≤ μ (closedBall ξ r) < ∞`.
    have hB : R.measure (closedBall ξ r) ≠ ∞ := by
      rw [hμ, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact R.locallyIntegrable_mult _ (isCompact_closedBall ξ r) (hBW.trans hWU)
    refine ne_top_of_le_ne_top hB (measure_mono ?_)
    rintro _ ⟨v, hv, rfl⟩
    exact hΦB v hv
  · have hne : MeasurableSet {x | R.mult x ≠ 1} :=
      R.measurable_mult (measurableSet_singleton 1).compl
    exact measurableSet_ball.inter (hΦc.measurable (R.measurableSet_carrier.compl.union hne))
  · -- `Φ '' Z` lies in the off-support part, `(spt μ ∩ W) \ M`, or `N`.
    have hsub : Φ '' Z ⊆ (range Φ \ R.measure.support) ∩ closedBall ξ r ∪
        ((R.measure.support ∩ W) \ R.carrier ∪ N) := by
      rintro _ ⟨v, ⟨hvD, hvZ⟩, rfl⟩
      have hxB := hΦB v hvD
      by_cases hxM : Φ v ∈ R.carrier
      · have h1 : R.mult (Φ v) ≠ 1 := by
          rcases hvZ with h | h
          · exact absurd hxM h
          · exact h
        exact Or.inr (Or.inr ⟨hxM, hxB, h1⟩)
      · by_cases hxs : Φ v ∈ R.measure.support
        · exact Or.inr (Or.inl ⟨⟨hxs, hBW hxB⟩, hxM⟩)
        · exact Or.inl ⟨⟨mem_range_self v, hxs⟩, hxB⟩
    calc μHE[n] (Φ '' Z)
        ≤ μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r ∪
          ((R.measure.support ∩ W) \ R.carrier ∪ N)) := measure_mono hsub
      _ ≤ μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r) +
          μHE[n] ((R.measure.support ∩ W) \ R.carrier ∪ N) := measure_union_le _ _
      _ = μHE[n] ((range Φ \ R.measure.support) ∩ closedBall ξ r) := by
        rw [measure_union_null H2 hN, add_zero]
      _ ≤ ENNReal.ofReal a := H3
  · -- `μ⌞Φ(D) = θ Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞(Φ(D) ∩ M) = Hⁿ⌞Φ(D \ Z)`.
    have hae : (Φ '' D ∩ R.carrier : Set (Euclid (n + k))) =ᵐ[μHE[n]] Φ '' (D \ Z) := by
      refine Filter.eventuallyEqSet_iff.2 ?_
      filter_upwards [H1'] with x hx
      constructor
      · rintro ⟨⟨v, hvD, rfl⟩, hxM⟩
        refine ⟨v, ⟨hvD, fun hvZ => ?_⟩, rfl⟩
        rcases hvZ.2 with h | h
        · exact h hxM
        · exact h (hx hxM (hΦB v hvD))
      · rintro ⟨v, ⟨hvD, hvZ⟩, rfl⟩
        refine ⟨⟨v, hvD, rfl⟩, ?_⟩
        by_contra hxM
        exact hvZ ⟨hvD, Or.inl hxM⟩
    have hmeas : R.measure.restrict (Φ '' D) = μHE[n].restrict (Φ '' (D \ Z)) := by
      rw [hμ, restrict_withDensity hΦD, Measure.restrict_restrict hΦD]
      calc (μHE[n].restrict (Φ '' D ∩ R.carrier)).withDensity (fun x => (R.mult x : ℝ≥0∞))
          = (μHE[n].restrict (Φ '' D ∩ R.carrier)).withDensity 1 := by
            refine withDensity_congr_ae ?_
            rw [Filter.EventuallyEq, ae_restrict_iff' (hΦD.inter R.measurableSet_carrier)]
            filter_upwards [H1'] with x hx hxs
            obtain ⟨⟨v, hvD, rfl⟩, hxM⟩ := hxs
            simp [hx hxM (hΦB v hvD)]
        _ = μHE[n].restrict (Φ '' D ∩ R.carrier) := withDensity_one
        _ = μHE[n].restrict (Φ '' (D \ Z)) := Measure.restrict_congr_set hae
    intro h _
    rw [hmeas]
/-- Bounded transfer from a two-sided lower-integral comparison: let `Z` be measurable with
`m(Z) ≤ a`, `m(D), ν(S) < ∞`, `c ≥ 0` and `s ≥ 0` integrable on `D`, and suppose that
`∫⁻_{D∖Z} h dm ≤ ∫⁻_S h∘φ dν ≤ ∫⁻_{D∖Z} (1 + c s) h dm` for every measurable `h ≥ 0`.  Then
(a) `∫⁻_D g dm ≤ ∫⁻_S g∘φ dν + G a` for measurable `0 ≤ g ≤ G`, and
(b) `|∫_D g dm - ∫_S g∘φ dν| ≤ G (a + c ∫_D s dm)` for measurable `|g| ≤ G`.
For (a), the part of `∫⁻_D g` over `D ∩ Z` is at most `G m(Z) ≤ G a`, and the part over `D ∖ Z`
is at most `∫⁻_S g∘φ`.  For (b), bounded measurable functions are integrable on `D` and `S`, so
for measurable `0 ≤ h ≤ G` the comparison passes to Bochner integrals and gives
`-G a ≤ ∫_S h∘φ - ∫_D h ≤ G c ∫_D s`; this is applied to `g⁺` and `g⁻`, and `g = g⁺ - g⁻`. -/
theorem Submission.dorag_tes_gt_bounded_transfer_of_lintegral_bounds : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] [Nonempty X] (m : Measure X) (ν : Measure Y) (D Z : Set X) (S : Set Y) (φ : Y → X) (s : X → ℝ) (a c : ℝ), MeasurableSet D → MeasurableSet Z → Measurable φ → m D ≠ ∞ → ν S ≠ ∞ → m Z ≤ ENNReal.ofReal a → 0 ≤ a → 0 ≤ c → (∀ v, 0 ≤ s v) → IntegrableOn s D m → (∀ h : X → ℝ≥0∞, Measurable h → (∫⁻ v in D \ Z, h v ∂m) ≤ (∫⁻ y in S, h (φ y) ∂ν) ∧ (∫⁻ y in S, h (φ y) ∂ν) ≤ ∫⁻ v in D \ Z, ENNReal.ofReal (1 + c * s v) * h v ∂m) → (∀ (g : X → ℝ) (G : ℝ), Measurable g → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ G) → (∫⁻ v in D, ENNReal.ofReal (g v) ∂m) ≤ (∫⁻ y in S, ENNReal.ofReal (g (φ y)) ∂ν) + ENNReal.ofReal (G * a)) ∧ ∀ (g : X → ℝ) (G : ℝ), Measurable g → (∀ v, |g v| ≤ G) → |(∫ v in D, g v ∂m) - (∫ y in S, g (φ y) ∂ν)| ≤ G * (a + c * (∫ v in D, s v ∂m)) := by
  intro X Y _ _ _ m ν D Z S φ s a c hD hZ hφ hmD hνS hmZ ha hc hs hsD hcmp
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hmDZ : m (D ∩ Z) ≤ ENNReal.ofReal a := (measure_mono inter_subset_right).trans hmZ
  refine ⟨fun g G hg hg0 hgG => ?_, fun g G hg hgG => ?_⟩
  · have hG0 : 0 ≤ G := (hg0 x₀).trans (hgG x₀)
    have h1 : ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m ≤ ENNReal.ofReal (G * a) :=
      calc ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m ≤ ∫⁻ v in D ∩ Z, ENNReal.ofReal G ∂m :=
            lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hgG v)
        _ = ENNReal.ofReal G * m (D ∩ Z) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal G * ENNReal.ofReal a := by gcongr
        _ = ENNReal.ofReal (G * a) := (ENNReal.ofReal_mul hG0).symm
    have h2 := (hcmp (fun v => ENNReal.ofReal (g v)) (ENNReal.measurable_ofReal.comp hg)).1
    calc ∫⁻ v in D, ENNReal.ofReal (g v) ∂m
        = ∫⁻ v in D ∩ Z, ENNReal.ofReal (g v) ∂m + ∫⁻ v in D \ Z, ENNReal.ofReal (g v) ∂m :=
          (lintegral_inter_add_sdiff _ D hZ).symm
      _ ≤ ENNReal.ofReal (G * a) + ∫⁻ y in S, ENNReal.ofReal (g (φ y)) ∂ν := add_le_add h1 h2
      _ = _ := add_comm _ _
  · have hDZ : m.real (D ∩ Z) ≤ a := ENNReal.toReal_le_of_le_ofReal ha hmDZ
    have hsDZ : IntegrableOn s (D \ Z) m := hsD.mono_set Set.sdiff_subset
    have hint : ∀ (u : X → ℝ) (G : ℝ), Measurable u → (∀ v, ‖u v‖ ≤ G) →
        IntegrableOn u D m ∧ IntegrableOn (fun y => u (φ y)) S ν := fun u G hu huG =>
      ⟨Measure.integrableOn_of_bounded hmD hu.aestronglyMeasurable (ae_of_all _ huG),
        Measure.integrableOn_of_bounded hνS (hu.comp hφ).aestronglyMeasurable
          (ae_of_all _ fun y => huG (φ y))⟩
    -- the key estimate `-G a ≤ ∫_S h∘φ - ∫_D h ≤ G c ∫_D s` for measurable `0 ≤ h ≤ G`
    have key : ∀ (h : X → ℝ) (G : ℝ), Measurable h → (∀ v, 0 ≤ h v) → (∀ v, h v ≤ G) →
        -(G * a) ≤ (∫ y in S, h (φ y) ∂ν) - ∫ v in D, h v ∂m ∧
          (∫ y in S, h (φ y) ∂ν) - ∫ v in D, h v ∂m ≤ G * (c * ∫ v in D, s v ∂m) := by
      intro h G hh hh0 hhG
      have hG0 : 0 ≤ G := (hh0 x₀).trans (hhG x₀)
      have hnorm : ∀ v, ‖h v‖ ≤ G := fun v => (Real.norm_of_nonneg (hh0 v)).trans_le (hhG v)
      obtain ⟨hhD, hhS⟩ := hint h G hh hnorm
      have hhDZ : IntegrableOn h (D \ Z) m := hhD.mono_set Set.sdiff_subset
      have hshDZ : IntegrableOn (fun v => s v * h v) (D \ Z) m := by
        refine Integrable.mono' (hsDZ.const_mul G)
          (hsDZ.aestronglyMeasurable.mul hh.aestronglyMeasurable) (ae_of_all _ fun v => ?_)
        rw [Real.norm_of_nonneg (mul_nonneg (hs v) (hh0 v)), mul_comm G]
        exact mul_le_mul_of_nonneg_left (hhG v) (hs v)
      have hwDZ : IntegrableOn (fun v => (1 + c * s v) * h v) (D \ Z) m := by
        have e : (fun v => (1 + c * s v) * h v) = fun v => h v + c * (s v * h v) := by
          funext v; ring
        rw [e]
        exact hhDZ.add (hshDZ.const_mul c)
      obtain ⟨L1, L2⟩ := hcmp (fun v => ENNReal.ofReal (h v)) (ENNReal.measurable_ofReal.comp hh)
      have L2' : ∫⁻ y in S, ENNReal.ofReal (h (φ y)) ∂ν ≤
          ∫⁻ v in D \ Z, ENNReal.ofReal ((1 + c * s v) * h v) ∂m := by
        refine L2.trans (le_of_eq (lintegral_congr fun v => ?_))
        exact (ENNReal.ofReal_mul (add_nonneg zero_le_one (mul_nonneg hc (hs v)))).symm
      have eDZ : ∫ v in D \ Z, h v ∂m = (∫⁻ v in D \ Z, ENNReal.ofReal (h v) ∂m).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hh0) hhDZ.aestronglyMeasurable
      have eS : ∫ y in S, h (φ y) ∂ν = (∫⁻ y in S, ENNReal.ofReal (h (φ y)) ∂ν).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => hh0 (φ y))
          hhS.aestronglyMeasurable
      have eW : ∫ v in D \ Z, (1 + c * s v) * h v ∂m =
          (∫⁻ v in D \ Z, ENNReal.ofReal ((1 + c * s v) * h v) ∂m).toReal :=
        integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun v => mul_nonneg (add_nonneg zero_le_one (mul_nonneg hc (hs v))) (hh0 v))
          hwDZ.aestronglyMeasurable
      have B1 : ∫ v in D \ Z, h v ∂m ≤ ∫ y in S, h (φ y) ∂ν := by
        rw [eDZ, eS]
        exact ENNReal.toReal_mono hhS.lintegral_lt_top.ne L1
      have B2 : ∫ y in S, h (φ y) ∂ν ≤ ∫ v in D \ Z, (1 + c * s v) * h v ∂m := by
        rw [eS, eW]
        exact ENNReal.toReal_mono hwDZ.lintegral_lt_top.ne L2'
      have eD : ∫ v in D, h v ∂m = (∫ v in D ∩ Z, h v ∂m) + ∫ v in D \ Z, h v ∂m :=
        (integral_inter_add_sdiff hZ hhD).symm
      have I0 : 0 ≤ ∫ v in D ∩ Z, h v ∂m := integral_nonneg hh0
      have I1 : ∫ v in D ∩ Z, h v ∂m ≤ G * a := by
        have hn : ‖∫ v in D ∩ Z, h v ∂m‖ ≤ G * m.real (D ∩ Z) :=
          norm_setIntegral_le_of_norm_le_const
            ((measure_mono inter_subset_left).trans_lt hmD.lt_top) fun v _ => hnorm v
        exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hn).trans
          (mul_le_mul_of_nonneg_left hDZ hG0))
      have eW' : ∫ v in D \ Z, (1 + c * s v) * h v ∂m =
          (∫ v in D \ Z, h v ∂m) + c * ∫ v in D \ Z, s v * h v ∂m := by
        have e : ∀ v, (1 + c * s v) * h v = h v + c * (s v * h v) := fun v => by ring
        simp_rw [e]
        rw [integral_add hhDZ (hshDZ.const_mul c), integral_const_mul]
      have I2 : ∫ v in D \ Z, s v * h v ∂m ≤ G * ∫ v in D, s v ∂m :=
        calc ∫ v in D \ Z, s v * h v ∂m ≤ ∫ v in D \ Z, G * s v ∂m :=
              setIntegral_mono hshDZ (hsDZ.const_mul G) fun v => by
                rw [mul_comm G]
                exact mul_le_mul_of_nonneg_left (hhG v) (hs v)
          _ = G * ∫ v in D \ Z, s v ∂m := integral_const_mul G _
          _ ≤ G * ∫ v in D, s v ∂m :=
              mul_le_mul_of_nonneg_left (setIntegral_mono_set hsD (ae_of_all _ hs)
                (LE.le.eventuallySubset Set.sdiff_subset)) hG0
      have I3 : c * ∫ v in D \ Z, s v * h v ∂m ≤ c * (G * ∫ v in D, s v ∂m) :=
        mul_le_mul_of_nonneg_left I2 hc
      constructor
      · linarith
      · linarith
    have hG0 : 0 ≤ G := (abs_nonneg _).trans (hgG x₀)
    have hp : ∀ v, max (g v) 0 ≤ G := fun v => max_le ((le_abs_self _).trans (hgG v)) hG0
    have hn : ∀ v, max (-g v) 0 ≤ G := fun v => max_le ((neg_le_abs _).trans (hgG v)) hG0
    have hpm : Measurable fun v => max (g v) 0 := hg.max measurable_const
    have hnm : Measurable fun v => max (-g v) 0 := hg.neg.max measurable_const
    obtain ⟨hpD, hpS⟩ := hint _ G hpm fun v =>
      (Real.norm_of_nonneg (le_max_right _ _)).trans_le (hp v)
    obtain ⟨hnD, hnS⟩ := hint _ G hnm fun v =>
      (Real.norm_of_nonneg (le_max_right _ _)).trans_le (hn v)
    obtain ⟨k1, k2⟩ := key _ G hpm (fun v => le_max_right _ _) hp
    obtain ⟨k3, k4⟩ := key _ G hnm (fun v => le_max_right _ _) hn
    have eD : ∫ v in D, g v ∂m = (∫ v in D, max (g v) 0 ∂m) - ∫ v in D, max (-g v) 0 ∂m := by
      rw [← integral_sub hpD hnD]
      exact integral_congr_ae (ae_of_all _ fun v => (max_zero_sub_max_neg_zero_eq_self (g v)).symm)
    have eS : ∫ y in S, g (φ y) ∂ν =
        (∫ y in S, max (g (φ y)) 0 ∂ν) - ∫ y in S, max (-g (φ y)) 0 ∂ν := by
      rw [← integral_sub hpS hnS]
      exact integral_congr_ae
        (ae_of_all _ fun y => (max_zero_sub_max_neg_zero_eq_self (g (φ y))).symm)
    rw [eD, eS, abs_le]
    constructor
    · linarith
    · linarith
/-- Product bound used for the graph area Jacobian: if `0 ≤ λᵢ ≤ 1` for `i < m`, then
`1 ≤ Πᵢ (1 + λᵢ) ≤ 1 + 2ᵐ Σᵢ λᵢ`.  Induction on `m`, splitting off the last index:
`Π = P'(1 + μ)` and `Σ = S' + μ` with `0 ≤ μ ≤ 1`, `S' ≥ 0` and `1 ≤ P' ≤ 1 + 2ᵐS'`.  Then
`P'(1 + μ) - 1 = (P' - 1)(1 + μ) + μ ≥ 0` and
`P'(1 + μ) ≤ (1 + 2ᵐS')(1 + μ) ≤ 1 + 2ᵐ⁺¹S' + μ ≤ 1 + 2ᵐ⁺¹(S' + μ)`. -/
theorem Submission.dorag_tes_ga_prod_one_add_bounds : ∀ (m : ℕ) (lam : Fin m → ℝ), (∀ i, 0 ≤ lam i) → (∀ i, lam i ≤ 1) → 1 ≤ ∏ i, (1 + lam i) ∧ ∏ i, (1 + lam i) ≤ 1 + 2 ^ m * ∑ i, lam i := by
  intro m
  induction m with
  | zero => intro lam _ _; simp
  | succ m ih =>
    intro lam h0 h1
    obtain ⟨hP1, hP2⟩ := ih (fun i => lam i.castSucc) (fun i => h0 _) (fun i => h1 _)
    have hS : 0 ≤ ∑ i : Fin m, lam i.castSucc := Finset.sum_nonneg fun i _ => h0 _
    have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hμ0 := h0 (Fin.last m)
    have hμ1 := h1 (Fin.last m)
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, pow_succ]
    constructor
    · linarith [mul_nonneg (sub_nonneg.2 hP1) (by linarith : (0 : ℝ) ≤ 1 + lam (Fin.last m))]
    · linarith [mul_nonneg (sub_nonneg.2 hP2) (by linarith : (0 : ℝ) ≤ 1 + lam (Fin.last m)),
        mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 ^ m) hS) (sub_nonneg.2 hμ1),
        mul_nonneg hμ0 (by linarith : (0 : ℝ) ≤ 2 ^ m * 2 - 1)]
/-- **Gram operator of a linear graph** (Simon Ch. 5, after (14): `DᵢF · DⱼF = δᵢⱼ + Dᵢf · Dⱼf`
for the graph map `F(x) = (x, f(x))`; here `Df(x)` is an arbitrary `B` and the splitting
`ℝⁿ⁺ᵏ = ℝⁿ × ℝᵏ` is given by isometries `ι`, `ι'` with orthogonal ranges).  For `L = ι + ι' ∘ B`,
`L* L = id + B* B`: `⟪w, L* L u⟫ = ⟪L w, L u⟫` expands into four inner products; `ι`, `ι'`
preserve the two diagonal ones and orthogonality kills the two cross terms, leaving
`⟪w, u⟫ + ⟪B w, B u⟫ = ⟪w, (id + B* B) u⟫`. -/
theorem Submission.dorag_tes_ga_graph_linear_gram_identity : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (B : Euclid n →L[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L B).adjoint ∘L (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L B) = ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B := by
  intro n k ι ι' B h
  -- operators agree if `⟪w, · u⟫` agree for all `u, w`
  ext1 u
  refine ext_inner_left ℝ fun w => ?_
  -- `⟪w, L* L u⟫ = ⟪L w, L u⟫`, `⟪w, B* B u⟫ = ⟪B w, B u⟫`; expand, `ι` and `ι'` are isometric
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right, add_apply,
    ContinuousLinearMap.id_apply, LinearIsometry.coe_toContinuousLinearMap, inner_add_left,
    inner_add_right, LinearIsometry.inner_map_map]
  -- the cross terms vanish by orthogonality
  rw [h w (B u), inner_eq_zero_symm.mp (h u (B w))]
  ring

/-- Determinant bounds for `id + B* ∘ B` (graph area, steps 6–7).  If `B : ℝⁿ → ℝᵏ` has
`‖B‖ ≤ 1`, then `1 ≤ det (id + B* B) ≤ 1 + 2ⁿ ∑ᵢ |B eᵢ|²`: in an orthonormal eigenbasis of the
symmetric map `B* B` the eigenvalues are `λᵢ = |B bᵢ|² ∈ [0, 1]`, `det (id + B* B) = ∏ (1 + λᵢ)`,
and `∑ λᵢ = trace (B* B) = ∑ |B eᵢ|²`. -/
theorem Submission.dorag_tes_ga_det_id_add_adjoint_comp_bounds : ∀ (n k : ℕ) (B : Euclid n →L[ℝ] Euclid k), ‖B‖ ≤ 1 → 1 ≤ (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det ∧ (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det ≤ 1 + 2 ^ n * ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  intro n k B hB
  -- Step 1: `P = B* ∘ B` is symmetric, with `⟪x, P y⟫ = ⟪B x, B y⟫`
  let P : Euclid n →ₗ[ℝ] Euclid n := (B.adjoint ∘L B : Euclid n →L[ℝ] Euclid n)
  have hP : ∀ x y, inner ℝ x (P y) = inner ℝ (B x) (B y) := fun x y =>
    ContinuousLinearMap.adjoint_inner_right B x (B y)
  have hsym : P.IsSymmetric := fun x y => by
    rw [real_inner_comm, hP, hP, real_inner_comm]
  -- Step 2: an orthonormal eigenbasis `b` of `P`, with eigenvalues `lam`
  have hn : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  set b := hsym.eigenvectorBasis hn
  set lam := hsym.eigenvalues hn
  have hPb : ∀ i, P (b i) = lam i • b i := fun i => hsym.apply_eigenvectorBasis hn i
  -- Step 3: `lam i = ‖B (b i)‖ ^ 2`, so `0 ≤ lam i ≤ 1`
  have hlam : ∀ i, lam i = ‖B (b i)‖ ^ 2 := fun i => by
    rw [← real_inner_self_eq_norm_sq, ← hP, hPb, real_inner_smul_right, real_inner_self_eq_norm_sq,
      b.orthonormal.1 i, one_pow, mul_one]
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => (hlam i).symm ▸ sq_nonneg _
  have hlam1 : ∀ i, lam i ≤ 1 := fun i => by
    have h : ‖B (b i)‖ ≤ 1 :=
      calc ‖B (b i)‖ ≤ ‖B‖ * ‖b i‖ := B.le_opNorm _
        _ = ‖B‖ := by rw [b.orthonormal.1 i, mul_one]
        _ ≤ 1 := hB
    rw [hlam i]
    exact pow_le_one₀ (norm_nonneg _) h
  -- Step 4: the matrix of `id + P` in the basis `b` is `diagonal (1 + lam i)`
  have hdet : (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B).det = ∏ i, (1 + lam i) := by
    have hM : LinearMap.toMatrix b.toBasis b.toBasis
        ((ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B : Euclid n →L[ℝ] Euclid n) :
          Euclid n →ₗ[ℝ] Euclid n) = Matrix.diagonal (fun i => 1 + lam i) := by
      ext i j
      have hj : (ContinuousLinearMap.id ℝ (Euclid n) + B.adjoint ∘L B) (b j) = (1 + lam j) • b j := by
        rw [add_smul, one_smul, ← hPb j]
        rfl
      rw [LinearMap.toMatrix_apply, b.coe_toBasis, b.coe_toBasis_repr_apply, ContinuousLinearMap.coe_coe, hj,
        map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b.toBasis, hM, Matrix.det_diagonal]
  -- Step 5: `trace P` in the bases `b` and `e` gives `∑ lam i = ∑ ‖B e_i‖ ^ 2`
  have htr : ∑ i, lam i = ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    calc ∑ i, lam i = LinearMap.trace ℝ (Euclid n) P := (hsym.trace_eq_sum_eigenvalues hn).symm
      _ = ∑ i, inner ℝ (EuclideanSpace.basisFun (Fin n) ℝ i) (P (EuclideanSpace.basisFun (Fin n) ℝ i)) :=
        LinearMap.trace_eq_sum_inner P _
      _ = ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
        simp_rw [EuclideanSpace.basisFun_apply, hP, real_inner_self_eq_norm_sq]
  -- Step 6: the sibling `prod_bound` with `m = n`
  rw [hdet, ← htr]
  exact Submission.dorag_tes_ga_prod_one_add_bounds n lam hlam0 hlam1
/-- **Simon Ch. 5, between (14) and (15)** (`1 ≤ J_F ≤ 1 + C|∇f|²`), with the area formula
**Ch. 2, 3.5**: for a `1`-Lipschitz `f : ℝⁿ → ℝᵏ` and the graph map `Φ(v) = ξ + ιv + ι'f(v)`
over the orthogonal isometric embeddings `ι`, `ι'`,
`∫_A h ∘ Φ ≤ ∫_{Φ(A)} h dHⁿ ≤ ∫_A (1 + 2ⁿ Σᵢ |Df(v)eᵢ|²) h ∘ Φ`.  `Φ` is injective and
`2`-Lipschitz, so the injective Lipschitz area formula applies.  Where `f` is differentiable
(Rademacher), `DΦ = ι + ι' ∘ Df` with `‖Df‖ ≤ 1`, `DΦ*DΦ = I + Df*Df`, and
`1 ≤ J_Φ² = det(I + Df*Df) ≤ 1 + 2ⁿ Σᵢ |Df eᵢ|²`; since `J_Φ ≥ 0`, `1 ≤ J_Φ ≤ J_Φ²`. -/
theorem Submission.dorag_tes_lipschitz_graph_area_bounds : ∀ (n k : ℕ), 0 < n → ∀ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (ξ : Euclid (n + k)) (f : Euclid n → Euclid k) (A : Set (Euclid n)) (h : Euclid (n + k) → ℝ≥0∞), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → MeasurableSet A → Measurable h → (∫⁻ v in A, h (ξ + ι v + ι' (f v)) ≤ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n]) ∧ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' A, h x ∂μHE[n] ≤ ∫⁻ v in A, ENNReal.ofReal (1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * h (ξ + ι v + ι' (f v)) := by
  intro n k _hn ι ι' ξ f A h horth hf hA _hh
  set Φ : Euclid n → Euclid (n + k) := fun v => ξ + ι v + ι' (f v) with hΦ
  have hfL : LipschitzWith 1 f :=
    LipschitzWith.of_dist_le_mul fun v w => by simpa [dist_eq_norm] using hf v w
  -- Step 2: `Φ` is `2`-Lipschitz
  have hΦL : LipschitzWith 2 Φ := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hvw : Φ v - Φ w = ι (v - w) + ι' (f v - f w) := by
      simp only [hΦ, map_sub]; abel
    rw [hvw]
    calc ‖ι (v - w) + ι' (f v - f w)‖ ≤ ‖ι (v - w)‖ + ‖ι' (f v - f w)‖ := norm_add_le _ _
      _ = ‖v - w‖ + ‖f v - f w‖ := by rw [ι.norm_map, ι'.norm_map]
      _ ≤ ‖v - w‖ + ‖v - w‖ := by gcongr; exact hf v w
      _ = ((2 : NNReal) : ℝ) * ‖v - w‖ := by push_cast; ring
  -- Step 1: `Φ` is injective, since `ι(v - w) = ι'(f w - f v)` is orthogonal to itself
  have hΦi : Injective Φ := by
    intro v w hvw
    have h1 : ι (v - w) = ι' (f w - f v) := by
      have h2 : ι v + ι' (f v) = ι w + ι' (f w) := by
        simpa only [hΦ, add_assoc, add_right_inj] using hvw
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, h2, add_comm (ι w)]
    have h3 : ι (v - w) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℝ)]
      nth_rewrite 2 [h1]
      exact horth _ _
    exact sub_eq_zero.mp (ι.injective (h3.trans (map_zero ι).symm))
  -- Step 3: the area formula `∫_{Φ(A)} h dHⁿ = ∫_A J_Φ · h ∘ Φ`
  have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hΦL hA
    hΦi.injOn h
  rw [finrank_euclideanSpace_fin] at harea
  -- Steps 4–8: `1 ≤ J_Φ ≤ 1 + 2ⁿ Σᵢ |Df eᵢ|²` wherever `f` is differentiable
  have hJ : ∀ᵐ v ∂(volume : Measure (Euclid n)),
      1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v ∧
        Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v ≤
          1 + 2 ^ n * ∑ i : Fin n, ‖fderiv ℝ f v (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    filter_upwards [hfL.ae_differentiableAt (μ := volume)] with v hv
    have hB : ‖fderiv ℝ f v‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hfL
    have hD : HasFDerivAt Φ
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ f v) v := by
      have := ((ι.toContinuousLinearMap.hasFDerivAt (x := v)).add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp v hv.hasFDerivAt)).const_add ξ
      convert this using 1
      funext x
      simp [hΦ, add_assoc]
    have hsq := Poincare.SimonGMT.Chapter02.areaJacobianAt_sq_eq_det_adjoint_comp Φ v
    rw [hD.fderiv,
      Submission.dorag_tes_ga_graph_linear_gram_identity n k ι ι' (fderiv ℝ f v) horth] at hsq
    obtain ⟨hlo, hhi⟩ :=
      Submission.dorag_tes_ga_det_id_add_adjoint_comp_bounds n k (fderiv ℝ f v) hB
    have hJ0 := Poincare.SimonGMT.Chapter02.areaJacobianAt_nonneg Φ v
    have hJ1 : 1 ≤ Poincare.SimonGMT.Chapter02.areaJacobianAt Φ v := by nlinarith
    exact ⟨hJ1, by nlinarith⟩
  -- Step 9: integrate the a.e. bounds against `h ∘ Φ`
  rw [harea]
  constructor
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hJ] with v hv
    exact le_mul_of_one_le_left' (ENNReal.one_le_ofReal.mpr hv.1)
  · refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae hJ] with v hv
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hv.2) zero_le

/-- **Choice of a plane with small tilt and small height** (Simon Ch. 5, proof of 4.5, (1)–(2)).
Write `J(S) = ∫_{B_σ(ξ)} |p_{Q(x)} − p_S|² dμ` (Hilbert–Schmidt norm).  If `J(T) ≤ a`, keep
`S = T`: integrating `|p_T − p_{T₁}|² ≤ 2|p_{Q(x)} − p_T|² + 2|p_{Q(x)} − p_{T₁}|²` over
`B_σ(ξ)`, where `μ(B_σ(ξ)) ≥ M`, gives `|p_T − p_{T₁}|² ≤ 4a/M`, and then
`y − p_T y = (y − p_{T₁} y) + (p_{T₁} − p_T) y` gives the height bound.  Otherwise `S = T₁`,
as `J(T₁) ≤ a < J(T)`. -/
theorem Submission.dorag_tes_plane_reduction : ∀ (N : ℕ) (μ : Measure (Euclid N)) (Q : Euclid N → Submodule ℝ (Euclid N)) (ξ : Euclid N) (σ a M h₁ : ℝ) (T T₁ : Submodule ℝ (Euclid N)), 0 < σ → 0 ≤ a → 0 < M → AEStronglyMeasurable (fun x => (Q x).starProjection) μ → ENNReal.ofReal M ≤ μ (closedBall ξ σ) → ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T₁.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a → (∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - T₁.starProjection (x - ξ)‖ ≤ h₁) → ∃ S : Submodule ℝ (Euclid N), (S = T ∨ S = T₁) ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ENNReal.ofReal a ∧ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ≤ ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂μ ∧ ∀ x ∈ μ.support ∩ closedBall ξ σ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ h₁ + Real.sqrt (4 * a / M) * σ := by
  intro N μ Q ξ σ a M h₁ T T₁ hσ ha hM hQ hμB hJ₁ hh₁
  obtain ⟨hHS, htri, -, -⟩ := Submission.dorag_tes_projection_algebra N
  -- `τ S x = |p_{Q(x)} − p_S|²`, so that `J(S) = ∫_{B_σ(ξ)} τ S dμ`
  let τ : Submodule ℝ (Euclid N) → Euclid N → ℝ := fun S x =>
    ∑ i : Fin N, ‖(Q x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
      S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  change ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T₁ x) ∂μ ≤ ENNReal.ofReal a at hJ₁
  change ∃ S : Submodule ℝ (Euclid N), (S = T ∨ S = T₁) ∧
    ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ S x) ∂μ ≤ ENNReal.ofReal a ∧
    ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ S x) ∂μ ≤
      ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ ∧
    ∀ x ∈ μ.support ∩ closedBall ξ σ,
      ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ h₁ + Real.sqrt (4 * a / M) * σ
  by_cases hT : ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ ≤ ENNReal.ofReal a
  swap
  · -- `J(T) > a`: take `S = T₁`
    refine ⟨T₁, Or.inr rfl, hJ₁, hJ₁.trans (not_le.mp hT).le, fun x hx => ?_⟩
    have h₂ : 0 ≤ Real.sqrt (4 * a / M) * σ := mul_nonneg (Real.sqrt_nonneg _) hσ.le
    linarith [hh₁ x hx]
  -- `J(T) ≤ a`: keep `S = T`
  refine ⟨T, Or.inl rfl, hT, le_rfl, ?_⟩
  -- `c₀ = |p_T − p_{T₁}|²`
  set c₀ : ℝ := ∑ i : Fin N, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
    T₁.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have hc₀ : 0 ≤ c₀ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hτ : ∀ S x, 0 ≤ τ S x := fun S x => Finset.sum_nonneg fun i _ => sq_nonneg _
  -- each `x ↦ τ S x` is `μ`-a.e. measurable, being continuous in `p_{Q(x)}`
  have hmeas : ∀ S : Submodule ℝ (Euclid N),
      AEMeasurable (fun x => ENNReal.ofReal (τ S x)) (μ.restrict (closedBall ξ σ)) := by
    intro S
    have hcont : Continuous fun L : Euclid N →L[ℝ] Euclid N =>
        ∑ i : Fin N, ‖L (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
      continuous_finsetSum _ fun i _ =>
        ((continuous_id.clm_apply continuous_const).sub continuous_const).norm.pow 2
    exact (hcont.comp_aestronglyMeasurable hQ).aemeasurable.ennreal_ofReal.restrict
  -- `c₀ μ(B_σ(ξ)) ≤ 2 J(T) + 2 J(T₁) ≤ 4a`
  have hint : ENNReal.ofReal c₀ * μ (closedBall ξ σ) ≤ ENNReal.ofReal (4 * a) := by
    rw [← setLIntegral_const]
    calc ∫⁻ _ in closedBall ξ σ, ENNReal.ofReal c₀ ∂μ
        ≤ ∫⁻ x in closedBall ξ σ,
            (2 * ENNReal.ofReal (τ T x) + 2 * ENNReal.ofReal (τ T₁ x)) ∂μ := by
          refine lintegral_mono fun x => ?_
          calc ENNReal.ofReal c₀ ≤ ENNReal.ofReal (2 * τ T x + 2 * τ T₁ x) :=
                ENNReal.ofReal_le_ofReal (htri (Q x) T T₁)
            _ = 2 * ENNReal.ofReal (τ T x) + 2 * ENNReal.ofReal (τ T₁ x) := by
                rw [ENNReal.ofReal_add (mul_nonneg zero_le_two (hτ T x))
                    (mul_nonneg zero_le_two (hτ T₁ x)),
                  ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_mul zero_le_two,
                  ENNReal.ofReal_ofNat]
      _ = 2 * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T x) ∂μ +
            2 * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (τ T₁ x) ∂μ := by
          rw [lintegral_add_left' ((hmeas T).const_mul 2),
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ ≤ 2 * ENNReal.ofReal a + 2 * ENNReal.ofReal a := by gcongr
      _ = ENNReal.ofReal (4 * a) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          ring
  -- hence `c₀ ≤ 4a/M`, as `μ(B_σ(ξ)) ≥ M > 0`
  have hc₀M : c₀ ≤ 4 * a / M := by
    rw [le_div_iff₀ hM, ← ENNReal.ofReal_le_ofReal_iff (by linarith), ENNReal.ofReal_mul hc₀]
    calc ENNReal.ofReal c₀ * ENNReal.ofReal M ≤ ENNReal.ofReal c₀ * μ (closedBall ξ σ) := by
          gcongr
      _ ≤ ENNReal.ofReal (4 * a) := hint
  -- the height bound: `y − p_T y = (y − p_{T₁} y) + (p_{T₁} − p_T) y` with `y = x − ξ`
  intro x hx
  have hy : ‖x - ξ‖ ≤ σ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx.2
  have hA : ‖T.starProjection (x - ξ) - T₁.starProjection (x - ξ)‖ ≤
      Real.sqrt c₀ * ‖x - ξ‖ := by
    have h := hHS (T.starProjection - T₁.starProjection) (x - ξ)
    simp only [sub_apply] at h
    rw [← Real.sqrt_sq (norm_nonneg (T.starProjection (x - ξ) - T₁.starProjection (x - ξ))),
      ← Real.sqrt_sq (norm_nonneg (x - ξ)), ← Real.sqrt_mul hc₀]
    exact Real.sqrt_le_sqrt h
  calc ‖(x - ξ) - T.starProjection (x - ξ)‖
      = ‖((x - ξ) - T₁.starProjection (x - ξ)) +
          (T₁.starProjection (x - ξ) - T.starProjection (x - ξ))‖ := by
        rw [sub_add_sub_cancel]
    _ ≤ ‖(x - ξ) - T₁.starProjection (x - ξ)‖ +
          ‖T₁.starProjection (x - ξ) - T.starProjection (x - ξ)‖ := norm_add_le _ _
    _ ≤ h₁ + Real.sqrt (4 * a / M) * σ := by
        refine add_le_add (hh₁ x hx) ?_
        rw [norm_sub_rev]
        refine hA.trans ?_
        gcongr

/-- **First variation along a Lipschitz graph, tested with vertical fields** (Simon Ch. 5, proof
of 4.5, (5)–(13); chapter-05.txt lines 807–893).  Write `φ(x) = P(x − ξ)`, `Φ(v) = ξ + ιv + ι'f(v)`,
`D = B̆ⁿ_{r/2}(0)`, `fʲ = proj_j ∘ f` and `tilt(x) = Σᵢ ‖p_{TₓM} eᵢ − p_T eᵢ‖²`.  Then (i)
`∫_{Φ(D)} ‖Dfʲ(φ)‖² dμ ≤ 2 ∫_{B_r(ξ)} tilt dμ` ((9), (13)), and (ii) for `ζ ∈ C¹_c(D)` with
`‖Dζ‖ ≤ G`, `|∫_{Φ(D)} Σᵢ ∂ᵢfʲ(φ) ∂ᵢζ(φ) dμ| ≤ G (∫_{B_r(ξ)} tilt dμ + μ(B_r(ξ) \ Φ(ℝⁿ)) +
(κr/2) μ(B_r(ξ)))` ((8), (11), (12)).  On `Φ(D)` the graph identity (7) and
`dorag_tes_projection_algebra` (c), (d) give the pointwise bounds; the vertical field `ζ(φ) e`,
`e = ι' εⱼ`, is tested in the first variation (6). -/
theorem Submission.dorag_tes_graph_first_variation_estimate : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (T : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ T = n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, ι v ∈ T) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ x ∈ R.measure.support ∩ closedBall ξ r, ‖(x - ξ) - T.starProjection (x - ξ)‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → ∀ v : Euclid n, x = ξ + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ j : Fin k, ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2) ∂R.measure ≤ 2 * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) ∧ ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) (r / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → ENNReal.ofReal |∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)) ∂R.measure| ≤ ENNReal.ofReal G * (∫⁻ x in closedBall ξ r, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure + R.measure (closedBall ξ r \ range (fun v => ξ + ι v + ι' (f v))) + ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)) := by
  intro n k hn U W R H κ ξ r T ι ι' P f _ hWU _ hHκ hFV hpx hr hBW hT hιι' hιT hPι hPι' hfLip hfbd
    hheight htan
  -- Frame: `|y|² = |Py|² + |y − p_T y|²` and `|Py| ≤ |y|`.
  obtain ⟨-, -, -, hpyth, hPle⟩ :=
    Submission.dorag_tes_gv_adapted_frame n k T ι ι' P hT hιι' hιT hPι hPι'
  -- Graph geometry: `φ(Φ(v)) = v`, `|Φ(v) − ξ|² = |v|² + |f(v)|²`, `Φ(D) ⊆ B_r(ξ)`.
  have hLip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun v w => by
    simpa [dist_eq_norm] using hfLip v w
  have hΦsub : ∀ v, (ξ + ι v + ι' (f v)) - ξ = ι v + ι' (f v) := fun v => by abel
  have hPΦ : ∀ v, P ((ξ + ι v + ι' (f v)) - ξ) = v := fun v => by
    rw [hΦsub, map_add, hPι, hPι', add_zero]
  have hnormΦ : ∀ v, ‖(ξ + ι v + ι' (f v)) - ξ‖ ^ 2 = ‖v‖ ^ 2 + ‖f v‖ ^ 2 := fun v => by
    rw [hΦsub, norm_add_sq_real, hιι', LinearIsometry.norm_map, LinearIsometry.norm_map]; ring
  have hΦD : (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) ⊆ closedBall ξ r := by
    rintro _ ⟨v, hv, rfl⟩
    rw [mem_closedBall, dist_eq_norm]
    have hv' : ‖v‖ < r / 2 := by simpa using hv
    have h1 := hnormΦ v
    have h3 : ‖f v‖ ^ 2 ≤ (r / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hfbd v) 2
    have h4 : ‖v‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv'.le 2
    have h5 : ‖(ξ + ι v + ι' (f v)) - ξ‖ ^ 2 ≤ r ^ 2 := by nlinarith
    nlinarith [norm_nonneg ((ξ + ι v + ι' (f v)) - ξ)]
  -- `Φ(D) = {x | Φ(φ(x)) = x} ∩ φ⁻¹(D)` and `Φ(ℝⁿ) = {x | Φ(φ(x)) = x}` are Borel.
  have hΦcont : Continuous (fun v => ξ + ι v + ι' (f v)) :=
    (continuous_const.add ι.continuous).add (ι'.continuous.comp hLip.continuous)
  have hφcont : Continuous (fun x : Euclid (n + k) => P (x - ξ)) :=
    P.continuous.comp (continuous_id.sub continuous_const)
  have hclosed : IsClosed {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} :=
    isClosed_eq (hΦcont.comp hφcont) continuous_id
  have hAeq : (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) =
      {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} ∩
        (fun x => P (x - ξ)) ⁻¹' ball (0 : Euclid n) (r / 2) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · show ξ + ι (P ((ξ + ι v + ι' (f v)) - ξ)) + ι' (f (P ((ξ + ι v + ι' (f v)) - ξ))) =
          ξ + ι v + ι' (f v)
        rw [hPΦ v]
      · show P ((ξ + ι v + ι' (f v)) - ξ) ∈ ball (0 : Euclid n) (r / 2)
        rw [hPΦ v]; exact hv
    · rintro ⟨h1, h2⟩
      exact ⟨P (x - ξ), h2, h1⟩
  have hFeq : range (fun v => ξ + ι v + ι' (f v)) =
      {x : Euclid (n + k) | ξ + ι (P (x - ξ)) + ι' (f (P (x - ξ))) = x} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      show ξ + ι (P ((ξ + ι v + ι' (f v)) - ξ)) + ι' (f (P ((ξ + ι v + ι' (f v)) - ξ))) =
        ξ + ι v + ι' (f v)
      rw [hPΦ v]
    · intro h
      exact ⟨P (x - ξ), h⟩
  have hAmeas : MeasurableSet ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) := by
    rw [hAeq]
    exact hclosed.measurableSet.inter (isOpen_ball.preimage hφcont).measurableSet
  have hFmeas : MeasurableSet (range (fun v => ξ + ι v + ι' (f v))) := by
    rw [hFeq]; exact hclosed.measurableSet
  -- Pointwise bounds μ-a.e. on `Φ(D)` (Simon (7), (9)–(11)): the tangent identification
  -- `TₓM = range(ι + ι' ∘ Df(v))`, `Dfʲ(v) = proj_j ∘ Df(v)`, `‖Df(v)‖ ≤ 1`, and
  -- `dorag_tes_projection_algebra` (c), (d) for `(TₓM, T)` with `t = tilt(x)`.
  have hpa := Submission.dorag_tes_projection_algebra (n + k)
  have key : ∀ j : Fin k, ∀ᵐ x ∂R.measure,
      x ∈ (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) →
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2 ≤
          2 * (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∧
        ∀ m : Euclid n →L[ℝ] ℝ,
          |m (P ((approxTangentPlane n R.carrier x).starProjection
              (ι' (EuclideanSpace.single j (1 : ℝ))))) -
            ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
              (EuclideanSpace.single i (1 : ℝ)) * m (EuclideanSpace.single i (1 : ℝ))| ≤
            (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
              (EuclideanSpace.single i (1 : ℝ)) -
                T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖m‖ := by
    intro j
    filter_upwards [htan] with x hx hxA
    obtain ⟨v, hv, rfl⟩ := hxA
    obtain ⟨hdiff, hQ⟩ := hx (hΦD ⟨v, hv, rfl⟩) v rfl
    have hchain : fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v =
        (EuclideanSpace.proj j).comp (fderiv ℝ f v) :=
      ((EuclideanSpace.proj j : Euclid k →L[ℝ] ℝ).hasFDerivAt.comp v hdiff.hasFDerivAt).fderiv
    have hL : ‖fderiv ℝ f v‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (x₀ := v) hLip
    dsimp only
    rw [hPΦ v, hchain]
    exact Submission.dorag_tes_gv_graph_plane_pointwise n k T _ ι ι' P (fderiv ℝ f v) j
      (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier (ξ + ι v + ι' (f v))).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      hT hιι' hιT hPι hPι' hQ hL (Finset.sum_nonneg fun i _ => sq_nonneg _)
      (fun a b ha hb => hpa.2.2.1 _ T a b ha hb) (fun e he => hpa.2.2.2 _ T e he)
  refine ⟨fun j => ?_, fun j ζ G hζ hζc hζs hζG => ?_⟩
  · -- (i): integrate `‖Dfʲ(φ)‖² ≤ 2 tilt` over `Φ(D) ⊆ B_r(ξ)` ((9), (13)).
    calc ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          ENNReal.ofReal (‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))‖ ^ 2)
            ∂R.measure
        ≤ ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          2 * ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
          apply lintegral_mono_ae
          filter_upwards [(ae_restrict_iff' hAmeas).mpr (key j)] with x hx
          refine (ENNReal.ofReal_le_ofReal hx.1).trans_eq ?_
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
      _ = 2 * ∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2),
          ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure :=
          lintegral_const_mul' _ _ (by simp)
      _ ≤ 2 * ∫⁻ x in closedBall ξ r,
          ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
          gcongr
  · -- (ii): test the first variation with the vertical field `ζ(φ) e`, `e = ι' εⱼ` ((6), (8)),
    -- then split `B_r(ξ)` into `Φ(D)` and its complement ((11), (12)).
    have hG : 0 ≤ G := (norm_nonneg _).trans (hζG 0)
    have he1 : ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
    -- Height bound: `|x − ξ|² ≤ |φ(x)|² + r²/16` on `spt μ ∩ B_r(ξ)` (Simon (5)).
    have hloc : ∀ x ∈ R.measure.support ∩ closedBall ξ r,
        ‖x - ξ‖ ^ 2 ≤ ‖P (x - ξ)‖ ^ 2 + r ^ 2 / 16 := by
      intro x hx
      have h1 := hpyth (x - ξ)
      have h3 : ‖(x - ξ) - T.starProjection (x - ξ)‖ ^ 2 ≤ (r / 4) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hheight x hx) 2
      nlinarith
    obtain ⟨hint, hbound⟩ := Submission.dorag_tes_gv_vertical_variation_bound n (n + k) hn U W R H
      κ ξ r P ζ G (ι' (EuclideanSpace.single j (1 : ℝ))) hWU hHκ hFV hpx hr hBW hPle hloc hζ hζc
      hζs hζG he1.le
    have hu_bd : ∀ x, |fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection
          (ι' (EuclideanSpace.single j (1 : ℝ)))))| ≤ G := by
      intro x
      rw [← Real.norm_eq_abs]
      calc _ ≤ ‖fderiv ℝ ζ (P (x - ξ))‖ *
            ‖P ((approxTangentPlane n R.carrier x).starProjection
              (ι' (EuclideanSpace.single j (1 : ℝ))))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ G * 1 := by
          gcongr
          · exact hζG _
          · calc _ ≤ ‖(approxTangentPlane n R.carrier x).starProjection
                    (ι' (EuclideanSpace.single j (1 : ℝ)))‖ := hPle _
              _ ≤ ‖ι' (EuclideanSpace.single j (1 : ℝ))‖ :=
                  Submodule.norm_starProjection_apply_le _ _
              _ = 1 := he1
        _ = G := mul_one G
    -- On `(B_r(ξ) \ Φ(D)) ∩ Φ(ℝⁿ)`, `φ(x) ∉ D ⊇ tsupport ζ`, so `Dζ(φ(x)) = 0`.
    have hzero : ∀ x ∈ closedBall ξ r,
        x ∉ (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2) →
        x ∈ range (fun v => ξ + ι v + ι' (f v)) →
        fderiv ℝ ζ (P (x - ξ))
          (P ((approxTangentPlane n R.carrier x).starProjection
            (ι' (EuclideanSpace.single j (1 : ℝ))))) = 0 := by
      rintro x - hxA ⟨v, rfl⟩
      have hvD : v ∉ ball (0 : Euclid n) (r / 2) := fun hv => hxA ⟨v, hv, rfl⟩
      have hvs : v ∉ tsupport ζ := fun h => hvD (hζs h)
      dsimp only
      rw [hPΦ v, fderiv_of_notMem_tsupport ℝ hvs]
      rfl
    have hmain := Submission.dorag_tes_gv_split_integral_estimate (Euclid (n + k)) R.measure
      ((fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2)) (closedBall ξ r)
      (range (fun v => ξ + ι v + ι' (f v)))
      (fun x => fderiv ℝ ζ (P (x - ξ))
        (P ((approxTangentPlane n R.carrier x).starProjection
          (ι' (EuclideanSpace.single j (1 : ℝ))))))
      (fun x => ∑ i : Fin n, fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) (P (x - ξ))
        (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ (P (x - ξ)) (EuclideanSpace.single i (1 : ℝ)))
      (fun x => ∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
      G (ENNReal.ofReal G * (ENNReal.ofReal (κ * r / 2) * R.measure (closedBall ξ r)))
      hAmeas measurableSet_closedBall hFmeas hΦD hG hint hbound
      (Eventually.of_forall fun x _ => hu_bd x)
      (Eventually.of_forall fun x hxB hxA hxF => hzero x hxB hxA hxF)
      (by
        filter_upwards [key j] with x hx hxA
        obtain ⟨-, h2⟩ := hx hxA
        have ht : 0 ≤ ∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
            (EuclideanSpace.single i (1 : ℝ)) -
              T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
          Finset.sum_nonneg fun i _ => sq_nonneg _
        refine (h2 (fderiv ℝ ζ (P (x - ξ)))).trans ?_
        rw [mul_comm G]
        exact mul_le_mul_of_nonneg_left (hζG _) ht)
    rw [mul_add]
    exact hmain
/-- **Graph parameter transfer** (Simon Ch. 5, proof of 4.5, (14)–(16)).  Let
`Φ(v) = ξ + ιv + ι'f(v)` be the graph map of the `1`-Lipschitz `f`, `D = B̆_{r/2}(0)`,
`φ(x) = P(x − ξ)` (so `φ ∘ Φ = id`), and `μ = θHⁿ⌞M` with `θ = 1` `μ`-a.e. on `B_r(ξ)`.  Then
(a) `∫_D g ≤ ∫_{Φ(D)} g ∘ φ dμ + G·a` for measurable `0 ≤ g ≤ G`, and
(b) `|∫_D g − ∫_{Φ(D)} g ∘ φ dμ| ≤ G(a + 2ⁿ∫_D Σⱼ‖Dfʲ‖²)` for measurable `|g| ≤ G`.
The exceptional set lemma gives `μ(Φ(D)) < ∞` and a measurable `Z` with `Hⁿ(Φ(Z)) ≤ a` and
`∫_{Φ(D)} h dμ = ∫_{Φ(D ∖ Z)} h dHⁿ`; the graph area bounds then give `Lⁿ(Z) ≤ a` and
`∫_{D∖Z} h ≤ ∫_{Φ(D)} h ∘ φ dμ ≤ ∫_{D∖Z} (1 + 2ⁿs)h`, using `Σᵢ|Df eᵢ|² ≤ s = Σⱼ‖Dfʲ‖² ≤ k`;
the bounded transfer lemma yields (a) and (b). -/
theorem Submission.dorag_tes_graph_parameter_transfer : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (ξ : Euclid (n + k)) (r a : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (P : Euclid (n + k) →L[ℝ] Euclid n) (f : Euclid n → Euclid k), IsOpen W → W ⊆ U → 0 < r → closedBall ξ r ⊆ W → 0 ≤ a → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v, P (ι v) = v) → (∀ w, P (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) → (∀ v, ‖f v‖ ≤ r / 4) → (∀ᵐ x ∂R.measure, x ∈ closedBall ξ r → R.mult x = 1) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ r) ≤ ENNReal.ofReal a → (∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, 0 ≤ g v) → (∀ v, g v ≤ G) → (∫⁻ v in ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g v)) ≤ (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), ENNReal.ofReal (g (P (x - ξ))) ∂R.measure) + ENNReal.ofReal (G * a)) ∧ ∀ (g : Euclid n → ℝ) (G : ℝ), Measurable g → (∀ v, |g v| ≤ G) → |(∫ v in ball (0 : Euclid n) (r / 2), g v) - (∫ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), g (P (x - ξ)) ∂R.measure)| ≤ G * (a + 2 ^ n * (∫ v in ball (0 : Euclid n) (r / 2), ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2)) := by
  intro n k hn U W R ξ r a ι ι' P f _hW hWU hr hrW ha horth hPι hPι' hf hfr hmult hspt hF
  -- Step 0.1: `φ(Φ(v)) = v` for `φ(x) = P(x − ξ)`, and `φ` is measurable
  have hφΦ : ∀ v, P (ξ + ι v + ι' (f v) - ξ) = v := fun v => by
    rw [add_assoc, add_sub_cancel_left, map_add, hPι, hPι', add_zero]
  have hφ : Measurable fun x : Euclid (n + k) => P (x - ξ) :=
    (P.continuous.comp (continuous_id.sub continuous_const)).measurable
  -- Steps 1–2: `μ(Φ(D)) < ∞`, and the exceptional set `Z` with `Hⁿ(Φ(Z)) ≤ a` and
  -- `∫_{Φ(D)} h̃ dμ = ∫_{Φ(D ∖ Z)} h̃ dHⁿ`
  obtain ⟨hμD, Z, hZ, hΦZ, hμ⟩ :=
    Submission.dorag_tes_gt_graph_measure_exceptional_set n k U W R ξ r a ι ι' P f hWU hr hrW
      hPι hPι' hf hfr hmult hspt hF
  -- Step 1.3: `Lⁿ(Z) ≤ Hⁿ(Φ(Z)) ≤ a`, by the graph area lower bound with `h ≡ 1`
  have hZa : volume Z ≤ ENNReal.ofReal a := by
    have h1 := (Submission.dorag_tes_lipschitz_graph_area_bounds n k hn ι ι' ξ f Z
      (fun _ => 1) horth hf hZ measurable_const).1
    simp only [setLIntegral_one] at h1
    exact h1.trans hΦZ
  -- Step 0.6: each `fʲ` is `1`-Lipschitz, so `0 ≤ s = Σⱼ ‖Dfʲ‖² ≤ k`; `s` is measurable,
  -- hence integrable on `D`
  have hfj : ∀ j : Fin k, LipschitzWith 1 fun v => EuclideanSpace.proj j (f v) := fun j =>
    LipschitzWith.of_dist_le_mul fun v w => by
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
      exact (PiLp.norm_apply_le (f v - f w) j).trans (hf v w)
  have hs0 : ∀ v, 0 ≤ ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 :=
    fun v => Finset.sum_nonneg fun j _ => by positivity
  have hsD : IntegrableOn
      (fun v => ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2)
      (ball (0 : Euclid n) (r / 2)) := by
    refine IntegrableOn.of_bound measure_ball_lt_top (Measurable.aestronglyMeasurable
      (Finset.measurable_sum _ fun j _ => (measurable_fderiv ℝ _).norm.pow_const 2)) k
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_of_nonneg (hs0 v)]
    calc ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2
        ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
          pow_le_one₀ (norm_nonneg _) ((norm_fderiv_le_of_lipschitz ℝ (hfj j)).trans_eq
            NNReal.coe_one)
      _ = k := by simp
  -- Step 3, (3a): `∫_{D∖Z} h ≤ ∫_{Φ(D)} h ∘ φ dμ ≤ ∫_{D∖Z} (1 + 2ⁿs) h`, by the graph area
  -- bounds on `D ∖ Z` and `Σᵢ |Df(v)eᵢ|² ≤ Σⱼ ‖Dfʲ(v)‖²`
  have hbd : ∀ h : Euclid n → ℝ≥0∞, Measurable h →
      (∫⁻ v in ball (0 : Euclid n) (r / 2) \ Z, h v) ≤
        (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h (P (x - ξ))
          ∂R.measure) ∧
      (∫⁻ x in (fun v => ξ + ι v + ι' (f v)) '' ball (0 : Euclid n) (r / 2), h (P (x - ξ))
          ∂R.measure) ≤
        ∫⁻ v in ball (0 : Euclid n) (r / 2) \ Z, ENNReal.ofReal (1 + 2 ^ n *
          ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2) * h v := by
    intro h hh
    have hhφ : Measurable fun x => h (P (x - ξ)) := hh.comp hφ
    rw [hμ _ hhφ]
    obtain ⟨hlo, hhi⟩ := Submission.dorag_tes_lipschitz_graph_area_bounds n k hn ι ι' ξ f
      (ball 0 (r / 2) \ Z) _ horth hf (measurableSet_ball.diff hZ) hhφ
    simp only [hφΦ] at hlo hhi
    refine ⟨hlo, hhi.trans (lintegral_mono fun v => ?_)⟩
    gcongr
    exact Submission.dorag_tes_gt_fderiv_columns_sq_le_rows_sq n k f v
  -- Steps 4–5: (a) and (b), by the bounded transfer lemma
  exact Submission.dorag_tes_gt_bounded_transfer_of_lintegral_bounds (Euclid n) (Euclid (n + k))
    volume R.measure (ball 0 (r / 2)) Z ((fun v => ξ + ι v + ι' (f v)) '' ball 0 (r / 2))
    (fun x => P (x - ξ))
    (fun v => ∑ j : Fin k, ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2) a (2 ^ n)
    measurableSet_ball hZ hφ measure_ball_lt_top.ne hμD hZa ha (by positivity) hs0 hsD hbd

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
