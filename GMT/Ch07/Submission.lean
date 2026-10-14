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
/-- **Simon Ch. 2, §5** (frame trace bound for a first-order perturbation of the identity): if
`‖B‖ ≤ A`, `‖L − I − tB‖ ≤ η|t|` with `η ≤ 1`, and `τ₁, …, τₙ` is orthonormal in `ℝᴾ`, then
(i) `|Σₐ τₐ · Bτₐ| ≤ nA` and (ii) `Σₐ |Lτₐ|² − n ≤ 2t Σₐ τₐ · Bτₐ + 2nη|t| + n(A + 1)²t²`.
With `E = L − I − tB` and `wₐ = tBτₐ + Eτₐ` we have `Lτₐ = τₐ + wₐ`, `|wₐ| ≤ (A + 1)|t|` and
`τₐ · Eτₐ ≤ η|t|`; expand `|τₐ + wₐ|² = 1 + 2t τₐ · Bτₐ + 2 τₐ · Eτₐ + |wₐ|²` and sum over `a`. -/
theorem Submission.fvmb_perturbed_frame_sum_norm_sq_sub_le : ∀ (P n : ℕ) (A η t : ℝ) (B L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), η ≤ 1 → ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → Orthonormal ℝ τ → |∑ a, inner ℝ (τ a) (B (τ a))| ≤ (n : ℝ) * A ∧ ∑ a, ‖L (τ a)‖ ^ 2 - (n : ℝ) ≤ 2 * t * (∑ a, inner ℝ (τ a) (B (τ a))) + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by
  intro P n A η t B L τ hη hB hE hτ
  -- `E = L − I − tB`, so `‖E‖ ≤ η|t|`
  set E : Euclid P →L[ℝ] Euclid P := L - ContinuousLinearMap.id ℝ (Euclid P) - t • B with hEdef
  have hτ1 : ∀ a, ‖τ a‖ = 1 := hτ.1
  -- unit vectors: `|Bτₐ| ≤ A`, `|Eτₐ| ≤ η|t|` and `|τₐ · Bτₐ| ≤ A`
  have hBa : ∀ a, ‖B (τ a)‖ ≤ A := fun a =>
    calc ‖B (τ a)‖ ≤ ‖B‖ * ‖τ a‖ := B.le_opNorm _
      _ = ‖B‖ := by rw [hτ1 a, mul_one]
      _ ≤ A := hB
  have hEa : ∀ a, ‖E (τ a)‖ ≤ η * |t| := fun a =>
    calc ‖E (τ a)‖ ≤ ‖E‖ * ‖τ a‖ := E.le_opNorm _
      _ = ‖E‖ := by rw [hτ1 a, mul_one]
      _ ≤ η * |t| := hE
  have hDa : ∀ a, |inner ℝ (τ a) (B (τ a))| ≤ A := fun a =>
    calc |inner ℝ (τ a) (B (τ a))| ≤ ‖τ a‖ * ‖B (τ a)‖ := abs_real_inner_le_norm _ _
      _ = ‖B (τ a)‖ := by rw [hτ1 a, one_mul]
      _ ≤ A := hBa a
  refine ⟨?_, ?_⟩
  · calc |∑ a, inner ℝ (τ a) (B (τ a))| ≤ ∑ a, |inner ℝ (τ a) (B (τ a))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, A := Finset.sum_le_sum fun a _ => hDa a
      _ = (n : ℝ) * A := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  · -- one column: `|Lτₐ|² = |τₐ + wₐ|²` with `wₐ = tBτₐ + Eτₐ`
    have hcol : ∀ a, ‖L (τ a)‖ ^ 2 ≤
        1 + 2 * t * inner ℝ (τ a) (B (τ a)) + 2 * η * |t| + (A + 1) ^ 2 * t ^ 2 := by
      intro a
      have hL : L (τ a) = τ a + (t • B (τ a) + E (τ a)) := by
        simp only [hEdef, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
        abel
      have hw : ‖t • B (τ a) + E (τ a)‖ ≤ (A + 1) * |t| :=
        calc ‖t • B (τ a) + E (τ a)‖ ≤ ‖t • B (τ a)‖ + ‖E (τ a)‖ := norm_add_le _ _
          _ = |t| * ‖B (τ a)‖ + ‖E (τ a)‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |t| * A + η * |t| :=
              add_le_add (mul_le_mul_of_nonneg_left (hBa a) (abs_nonneg t)) (hEa a)
          _ ≤ |t| * A + 1 * |t| := by gcongr
          _ = (A + 1) * |t| := by ring
      have hwsq : ‖t • B (τ a) + E (τ a)‖ ^ 2 ≤ (A + 1) ^ 2 * t ^ 2 :=
        calc ‖t • B (τ a) + E (τ a)‖ ^ 2 ≤ ((A + 1) * |t|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hw 2
          _ = (A + 1) ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
      have hcross : inner ℝ (τ a) (E (τ a)) ≤ η * |t| :=
        calc inner ℝ (τ a) (E (τ a)) ≤ ‖τ a‖ * ‖E (τ a)‖ := real_inner_le_norm _ _
          _ = ‖E (τ a)‖ := by rw [hτ1 a, one_mul]
          _ ≤ η * |t| := hEa a
      rw [hL, norm_add_sq_real, hτ1 a, inner_add_right, real_inner_smul_right]
      linarith
    calc ∑ a, ‖L (τ a)‖ ^ 2 - (n : ℝ)
        ≤ ∑ a, (1 + 2 * t * inner ℝ (τ a) (B (τ a)) + 2 * η * |t| + (A + 1) ^ 2 * t ^ 2) -
            (n : ℝ) := by
          gcongr with a
          exact hcol a
      _ = 2 * t * (∑ a, inner ℝ (τ a) (B (τ a))) + 2 * (n : ℝ) * η * |t| +
            (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.sum_const, Finset.sum_const, ← Finset.mul_sum,
            Finset.card_fin, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
          ring
/-- **Simon Ch. 2, §5** (the expansion `J_t = 1 + t div_M X + O(t²)` behind the first variation
formula 5.3), scalar one-sided step: given `n`, `A ≥ 0`, `ε > 0` there are `0 < η ≤ 1` and
`δ > 0` such that `|t| < δ`, `|D| ≤ nA` and `g ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)` imply
`√g ≤ 1 + tD + ε|t|`.  With `σ = tD + nη|t| + n(A + 1)²t²/2` the hypothesis gives
`√g ≤ √(e^σ e^σ) = e^σ`; `|σ| ≤ c₀|t| ≤ 1` for `c₀ = (n + 1)(A + 2 + (A + 1)²)`, so
`e^σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + Kt²` with `K = n(A + 1)²/2 + c₀²`.  Take
`η = min(1, ε/(2n + 1))` (so `nη ≤ ε/2`) and `δ = min(1, 1/c₀, ε/(2K))` (so `Kt² ≤ (ε/2)|t|`). -/
theorem Submission.fvmb_sqrt_le_first_order_of_le_exp : ∀ (n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t D g : ℝ, |t| < δ → |D| ≤ (n : ℝ) * A → g ≤ Real.exp (2 * t * D + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2) → Real.sqrt g ≤ 1 + t * D + ε * |t| := by
  intro n A ε hA hε
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Step 1: the constants `c₀`, `K`, `η`, `δ`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ((n : ℝ) + 1) * (A + 2 + (A + 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (n : ℝ) * (A + 1) ^ 2 / 2 + c₀ ^ 2 := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hKpos : 0 < K := by
    rw [hK]; exact add_pos_of_nonneg_of_pos (by positivity) (pow_pos hc₀pos 2)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (ε / (2 * (n : ℝ) + 1)) := ⟨_, rfl⟩
  have h2n : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hηpos : 0 < η := by rw [hη]; exact lt_min one_pos (div_pos hε h2n)
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  -- Step 2: `nη ≤ ε/2`
  have hnη : (n : ℝ) * η ≤ ε / 2 := by
    have h1 : η * (2 * (n : ℝ) + 1) ≤ ε := by
      rw [← le_div_iff₀ h2n, hη]; exact min_le_right _ _
    linarith
  refine ⟨η, hηpos, hη1, min 1 (min (1 / c₀) (ε / (2 * K))),
    lt_min one_pos (lt_min (one_div_pos.mpr hc₀pos) (div_pos hε (mul_pos two_pos hKpos))), ?_⟩
  intro t D g ht hD hg
  -- Step 3: `|t| ≤ 1`, `|t| ≤ 1/c₀`, `|t| ≤ ε/(2K)`, `t² ≤ |t|`
  have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_left _ _)).le
  have htc : |t| ≤ 1 / c₀ := (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have htK : |t| ≤ ε / (2 * K) := (ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hta : 0 ≤ |t| := abs_nonneg t
  have ht2 : t ^ 2 ≤ |t| := by
    rw [← sq_abs]; nlinarith [mul_nonneg hta (sub_nonneg.mpr ht1)]
  -- Step 4: `√g ≤ exp σ`
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = t * D + (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 :=
    ⟨_, rfl⟩
  have hsqrt : Real.sqrt g ≤ Real.exp σ := by
    have h2σ : 2 * t * D + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 = σ + σ := by
      rw [hσ]; ring
    rw [h2σ, Real.exp_add] at hg
    calc Real.sqrt g ≤ Real.sqrt (Real.exp σ * Real.exp σ) := Real.sqrt_le_sqrt hg
      _ = Real.exp σ := Real.sqrt_mul_self (Real.exp_pos σ).le
  -- Step 5: `|σ| ≤ c₀|t|`
  have hσabs : |σ| ≤ c₀ * |t| := by
    have h1 : |t * D| ≤ |t| * ((n : ℝ) * A) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD hta
    have h2 : abs ((n : ℝ) * η * |t|) ≤ (n : ℝ) * |t| := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hn hηpos.le) hta)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hn hη1) hta
    have h3 : |(n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2| ≤ (n : ℝ) * (A + 1) ^ 2 * |t| := by
      have hc : (0 : ℝ) ≤ (n : ℝ) * (A + 1) ^ 2 := by positivity
      have hc2 : (0 : ℝ) ≤ (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by positivity
      rw [abs_of_nonneg (by positivity)]
      calc (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 ≤ (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by linarith
        _ ≤ (n : ℝ) * (A + 1) ^ 2 * |t| := mul_le_mul_of_nonneg_left ht2 hc
    have htri : |σ| ≤ |t * D| + abs ((n : ℝ) * η * |t|) + |(n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2| := by
      rw [hσ]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hcoef : (n : ℝ) * (A + 1 + (A + 1) ^ 2) ≤ c₀ := by
      rw [hc₀]; nlinarith [sq_nonneg (A + 1)]
    calc |σ| ≤ |t| * ((n : ℝ) * A) + (n : ℝ) * |t| + (n : ℝ) * (A + 1) ^ 2 * |t| := by linarith
      _ = (n : ℝ) * (A + 1 + (A + 1) ^ 2) * |t| := by ring
      _ ≤ c₀ * |t| := mul_le_mul_of_nonneg_right hcoef hta
  -- Step 6: `|σ| ≤ 1` and `σ² ≤ c₀²t²`
  have hσ1 : |σ| ≤ 1 := by
    calc |σ| ≤ c₀ * |t| := hσabs
      _ ≤ c₀ * (1 / c₀) := mul_le_mul_of_nonneg_left htc hc₀pos.le
      _ = 1 := mul_one_div_cancel hc₀pos.ne'
  have hσsq : σ ^ 2 ≤ c₀ ^ 2 * t ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg σ) hσabs 2
    rwa [sq_abs, mul_pow, sq_abs] at h
  -- Step 7: `exp σ ≤ 1 + σ + σ²`
  have hexp : Real.exp σ ≤ 1 + σ + σ ^ 2 := by
    have h := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hσ1)
    linarith
  -- Step 8: the error terms `nη|t| ≤ (ε/2)|t|` and `Kt² ≤ (ε/2)|t|`
  have hnηt : (n : ℝ) * η * |t| ≤ ε / 2 * |t| := mul_le_mul_of_nonneg_right hnη hta
  have hKt : K * t ^ 2 ≤ ε / 2 * |t| := by
    have hK' : K * |t| ≤ ε / 2 := by
      calc K * |t| ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left htK hKpos.le
        _ = ε / 2 := by field_simp
    calc K * t ^ 2 = (K * |t|) * |t| := by rw [← sq_abs t]; ring
      _ ≤ ε / 2 * |t| := mul_le_mul_of_nonneg_right hK' hta
  have hKt2 : K * t ^ 2 = (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 + c₀ ^ 2 * t ^ 2 := by
    rw [hK]; ring
  -- Step 9: `√g ≤ exp σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + Kt² ≤ 1 + tD + ε|t|`
  linarith
/-- **Gram determinant bound** (Simon Ch. 4, 1.9 and Ch. 2, §5, where the Jacobian is the square
root of such a Gram determinant): `det(vᵢ · vⱼ) ≤ exp(Σₐ |vₐ|² − n)` for `v₁, …, vₙ ∈ ℝᴾ`.
With `V eₐ = vₐ` on `ℝⁿ`, the Gram matrix is the matrix of `S = V*V` in the standard basis, so
`det G = Πᵢ λᵢ` and `Σₐ |vₐ|² = trace S = Σᵢ λᵢ` for the eigenvalues `λᵢ = |V uᵢ|² ≥ 0` of `S`;
multiply `λᵢ ≤ e^{λᵢ − 1}` (`s + 1 ≤ eˢ`) over `i`. -/
theorem Submission.fvmb_gram_det_le_exp_sum_norm_sq_sub : ∀ (P n : ℕ) (v : Fin n → Euclid P), Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) ≤ Real.exp (∑ a, ‖v a‖ ^ 2 - (n : ℝ)) := by
  intro P n v
  classical
  -- `V eₐ = vₐ` and the symmetric operator `S = V*V` on `ℝⁿ`
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let V : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Euclid P := b.toBasis.constr ℝ v
  let S := LinearMap.adjoint V ∘ₗ V
  have hS : S.IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self V
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hVe : ∀ a, V (b a) = v a := by
    intro a
    have := b.toBasis.constr_basis ℝ v a
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  have hSinner : ∀ x y, inner ℝ x (S y) = inner ℝ (V x) (V y) := by
    intro x y
    simp [S, LinearMap.adjoint_inner_right]
  -- the matrix of `S` is the Gram matrix, and `trace S = Σₐ |vₐ|²`
  have hmat :
      LinearMap.toMatrix b.toBasis b.toBasis S = Matrix.of fun i j => inner ℝ (v i) (v j) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, hSinner, hVe, hVe]
    rfl
  have hdet : LinearMap.det S = Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) := by
    rw [← LinearMap.det_toMatrix b.toBasis, hmat]
  have htr : LinearMap.trace ℝ _ S = ∑ a, ‖v a‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner S b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hSinner, hVe, real_inner_self_eq_norm_sq]
  -- spectral theorem: `det S = Πᵢ λᵢ`, `trace S = Σᵢ λᵢ`, with `λᵢ = ⟪uᵢ, S uᵢ⟫ = |V uᵢ|² ≥ 0`
  rw [← hdet, hS.det_eq_prod_eigenvalues hn, ← htr, hS.trace_eq_sum_eigenvalues hn]
  have hnonneg : ∀ i, 0 ≤ hS.eigenvalues hn i := by
    intro i
    have h1 := hS.apply_eigenvectorBasis hn i
    have hu : ‖hS.eigenvectorBasis hn i‖ = 1 := (hS.eigenvectorBasis hn).orthonormal.1 i
    have h2 : inner ℝ (hS.eigenvectorBasis hn i) (S (hS.eigenvectorBasis hn i)) =
        hS.eigenvalues hn i := by
      rw [h1, inner_smul_right, real_inner_self_eq_norm_sq, hu]
      simp
    rw [← h2, hSinner]
    exact real_inner_self_nonneg
  -- `0 ≤ λᵢ ≤ e^{λᵢ − 1}`, multiplied over `i`
  simp only [RCLike.ofReal_real_eq_id, id]
  calc ∏ i, hS.eigenvalues hn i ≤ ∏ i, Real.exp (hS.eigenvalues hn i - 1) := by
        refine Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => ?_)
        have := Real.add_one_le_exp (hS.eigenvalues hn i - 1)
        linarith
    _ = Real.exp (∑ i, hS.eigenvalues hn i - n) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib]
        simp

/-- **First-order Jacobian bound** (Simon Ch. 2, §5, where `J_t = 1 + t div_M X + O(t²)` gives the
first variation formula 5.3; here only `‖L − I − tB‖ ≤ η|t|` is assumed): for `|t| < δ`,
`‖B‖ ≤ A` and orthonormal `τ₁, …, τₙ`, `(det(Lτᵢ · Lτⱼ))^{1/2} ≤ 1 + t Σₐ τₐ · Bτₐ + ε|t|`.
With `D = Σₐ τₐ · Bτₐ`, the frame bound gives `|D| ≤ nA` and
`Σₐ |Lτₐ|² − n ≤ 2tD + 2nη|t| + n(A + 1)²t²`, so the Gram determinant bound gives
`det G ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)`; the scalar bound (which supplies `0 < η ≤ 1` and
`δ`) turns this into the claim. -/
theorem Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order : ∀ (P n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ B L : Euclid P →L[ℝ] Euclid P, ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (L (τ i)) (L (τ j)))) ≤ 1 + t * ∑ a, inner ℝ (τ a) (B (τ a)) + ε * |t| := by
  intro P n A ε hA hε
  -- `0 < η ≤ 1` and `δ` depend only on `n`, `A` and `ε`
  obtain ⟨η, hη, hη1, δ, hδ, hsqrt⟩ := Submission.fvmb_sqrt_le_first_order_of_le_exp n A ε hA hε
  refine ⟨η, hη, δ, hδ, fun t ht B L hB hL τ hτ => ?_⟩
  -- `|D| ≤ nA` and `Σₐ |Lτₐ|² − n ≤ 2tD + 2nη|t| + n(A + 1)²t²`
  obtain ⟨hD, htr⟩ :=
    Submission.fvmb_perturbed_frame_sum_norm_sq_sub_le P n A η t B L τ hη1 hB hL hτ
  refine hsqrt t _ _ ht hD ?_
  -- `det G ≤ exp(Σₐ |Lτₐ|² − n) ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)`
  exact (Submission.fvmb_gram_det_le_exp_sum_norm_sq_sub P n fun a => L (τ a)).trans
    (Real.exp_le_exp.mpr htr)
/-- **Simon Ch. 2, (4.18)–(4.20)** (tangential divergence in an orthonormal frame): if `τ₁, …, τₙ`
is an orthonormal basis of `Q`, then `trace(p_Q ∘ B) = Σₐ τₐ · Bτₐ`.  The orthogonality
characterization of the projection gives `p_Q z = Σₐ (τₐ · z) τₐ`, so `p_Q ∘ B` is the sum of the
rank-one maps `z ↦ (τₐ · Bz) τₐ`, and the trace of `z ↦ ℓ(z) v` is `ℓ(v)`. -/
theorem Submission.fvmb_trace_starProjection_comp_eq_sum_inner : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (τ : Fin n → Euclid P) (B : Euclid P →L[ℝ] Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ B.toLinearMap) = ∑ a, inner ℝ (τ a) (B (τ a)) := by
  intro P n Q τ B hτ hQ
  -- `p_Q z = Σₐ ⟪τₐ, z⟫ τₐ`: the right side lies in `Q` and `z` minus it is orthogonal to `Q`
  have hproj : ∀ z : Euclid P, Q.starProjection z = ∑ a, inner ℝ (τ a) z • τ a := by
    intro z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [← hQ]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · intro q hq
      rw [← hQ] at hq
      induction hq using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        rw [inner_sub_left, hτ.inner_left_fintype, real_inner_comm]
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  -- `p_Q ∘ B = Σₐ (z ↦ ⟪τₐ, Bz⟫ τₐ)`
  have hdecomp : Q.starProjection.toLinearMap ∘ₗ B.toLinearMap =
      ∑ a, ((innerₛₗ ℝ (τ a)) ∘ₗ B.toLinearMap).smulRight (τ a) := by
    ext z
    simp [hproj]
  -- `trace (z ↦ ℓ(z) v) = ℓ(v)` (`LinearMap.trace_smulRight`), summed over `a`
  rw [hdecomp, map_sum]
  simp
/-- **Simon 6.3.1, Ch. 3 Remark 1.5(1)**: for `Hⁿ`-a.e. `x ∈ M`, the orientation `ξ(x)` of an
integer multiplicity triple `(M, θ, ξ)` orients the chosen approximate tangent plane `TₓM`.
`R.orients` gives, a.e. on `M`, an approximate tangent plane `Q` at `x` oriented by `ξ(x)`; the
chosen witness `approxTangentPlane n M x` is then `Q`, approximate tangent planes being unique. -/
theorem Submission.fvmb_imrep_ae_unitOrientation_approxTangentPlane : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), IsUnitOrientationOf (R.orient x) (approxTangentPlane n R.carrier x) := by
  intro P n U R
  filter_upwards [R.orients] with x hx
  obtain ⟨Q, hQ, hξ⟩ := hx
  -- the chosen witness of `∃ Q', HasApproximateTangentSpaceAt n M x Q'` is `Q`
  have h : ∃ Q', HasApproximateTangentSpaceAt n R.carrier x Q' := ⟨Q, hQ⟩
  have hT : approxTangentPlane n R.carrier x = Q := by
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec.unique hQ
  rw [hT]
  exact hξ
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
/-- **Simon Ch. 2, 5.9; Ch. 4, 2.7**: the tangential divergence of the normal part of `X`.  If
`Q ≤ S`, `pr(x) = P_S`, `pr` and `X` are differentiable at `x` and `Y = X − pr·X` near `x`, then
`trace(p_Q ∘ DY(x)) = −X(x) · Σⱼ (Dpr(x)(p_Q eⱼ))^* (p_Q eⱼ)`: by the product rule
`DY(x) = DX(x) − P_S DX(x) − (Dpr(x)·)X(x)`, `trace(p_Q ∘ C) = Σⱼ ⟨p_Q eⱼ, C (p_Q eⱼ)⟩`, and `P_S`
fixes `p_Q eⱼ ∈ Q ⊆ S`. -/
theorem Submission.mcs_trace_normal_part_eq_neg_inner : ∀ (P : ℕ) (Q S : Submodule ℝ (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X Y : Euclid P → Euclid P) (x : Euclid P), Q ≤ S → pr x = S.starProjection → DifferentiableAt ℝ pr x → DifferentiableAt ℝ X x → Y =ᶠ[𝓝 x] (fun y => X y - pr y (X y)) → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ Y x).toLinearMap) = -inner ℝ (X x) (∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (Q.starProjection (EuclideanSpace.single j 1))) (Q.starProjection (EuclideanSpace.single j 1))) := by
  intro P Q S pr X Y x hQS hprx hpr hX hY
  -- Step 1: `DY(x)h = DX(x)h − P_S(DX(x)h) − (Dpr(x)h)(X(x))`
  have hDY : ∀ h, fderiv ℝ Y x h =
      fderiv ℝ X x h - S.starProjection (fderiv ℝ X x h) - fderiv ℝ pr x h (X x) := by
    intro h
    rw [hY.fderiv_eq, fderiv_fun_sub hX (hpr.clm_apply hX), fderiv_clm_apply hpr hX, hprx]
    simp only [sub_add_eq_sub_sub, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
  -- Step 2: `trace(p ∘ C) = Σⱼ ⟨p eⱼ, C (p eⱼ)⟩`
  have htr : ∀ C : Euclid P →L[ℝ] Euclid P,
      LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ C.toLinearMap) =
        ∑ j : Fin P, inner ℝ (Q.starProjection (EuclideanSpace.single j 1))
          (C (Q.starProjection (EuclideanSpace.single j 1))) := by
    intro C
    have hpp : Q.starProjection.toLinearMap ∘ₗ C.toLinearMap =
        Q.starProjection.toLinearMap ∘ₗ (Q.starProjection.toLinearMap ∘ₗ C.toLinearMap) := by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact (Submodule.starProjection_eq_self_iff.mpr (Q.starProjection_apply_mem (C w))).symm
    rw [hpp, LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact (Submodule.inner_starProjection_left_eq_right Q _ _).symm
  -- Steps 3 and 4: each term is `−⟨X(x), (Dpr(x)u)^* u⟩`, `u = p eⱼ ∈ Q ⊆ S`
  rw [htr, inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  set u := Q.starProjection (EuclideanSpace.single j 1)
  have huS : S.starProjection u = u :=
    Submodule.starProjection_eq_self_iff.mpr (hQS (Submodule.starProjection_apply_mem _ _))
  rw [hDY, inner_sub_right, inner_sub_right, ← Submodule.inner_starProjection_left_eq_right, huS,
    sub_self, zero_sub, ← ContinuousLinearMap.adjoint_inner_left (fderiv ℝ pr x u) (X x) u,
    real_inner_comm]
/-- **Simon Ch. 4, 2.7** (the tangential part `Xᵀ = χ · pr · X`): let `U, O ⊆ ℝᴾ` be open,
`N ⊆ O` with `(N̄ \ N) ∩ U = ∅`, `pr` of class `C¹` on `O` and `X ∈ C¹_c(U; ℝᴾ)`.  Then some
`Xᵀ ∈ C¹_c(U; ℝᴾ)` equals `y ↦ pr(y) X(y)` near every point of `N`.  The compact set
`K = spt X ∩ N̄` lies in `N` (as `(N̄ \ N) ∩ U = ∅`), hence in `O ∩ U`; take a `C¹` cutoff `χ` with
compact support in `O ∩ U` and `χ = 1` near `K`.  Near `x ∈ N`, `χ = 1` if `x ∈ spt X`, and
`X = 0` otherwise. -/
theorem Submission.mcs_exists_c1_field_eq_proj_near : ∀ (P : ℕ) (U N O : Set (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∃ XT : Euclid P → Euclid P, ContDiff ℝ 1 XT ∧ HasCompactSupport XT ∧ tsupport XT ⊆ U ∧ ∀ x ∈ N, XT =ᶠ[𝓝 x] (fun y => pr y (X y)) := by
  intro P U N O pr X hU hO hNO hpr hN hX hXc hXU
  -- Step 1: `K = spt X ∩ N̄` is compact and `K ⊆ N`, hence `K ⊆ W = O ∩ U`
  have hKc : IsCompact (tsupport X ∩ closure N) := hXc.isCompact.inter_right isClosed_closure
  have hKW : tsupport X ∩ closure N ⊆ O ∩ U := by
    rintro z ⟨hzX, hzN⟩
    have hz : z ∈ N := by
      by_contra hz
      exact eq_empty_iff_forall_notMem.1 hN z ⟨⟨hzN, hz⟩, hXU hzX⟩
    exact ⟨hNO hz, hXU hzX⟩
  -- Step 2: a `C¹` cutoff `χ` with `spt χ = V̄ ⊆ W` compact and `χ = 1` on `L`, `K ⊆ int L`
  obtain ⟨L, hLc, hLcl, hKL, hLW⟩ := exists_compact_closed_between hKc (hO.inter hU) hKW
  obtain ⟨V, hVo, hLV, hVW, hVc⟩ :=
    exists_open_between_and_isCompact_closure hLc (hO.inter hU) hLW
  obtain ⟨χ, hχ, -, hχV, hχL⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1) hVo hLcl hLV
  have hχ1 : ContDiff ℝ 1 χ := by exact_mod_cast hχ
  have hχt : tsupport χ = closure V := by rw [tsupport, hχV]
  -- Step 3: `Xᵀ = χ · pr · X`
  refine ⟨fun y => χ y • pr y (X y), ?_, ?_, ?_, ?_⟩
  -- Step 4: `Xᵀ` is `C¹`: product rule at points of `O`; `Xᵀ = 0` near `y ∉ O`, as `spt χ ⊆ O`
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · exact hχ1.contDiffAt.smul ((hpr.contDiffAt (hO.mem_nhds hy)).clm_apply hX.contDiffAt)
    · have hyχ : χ =ᶠ[𝓝 y] 0 := by
        rw [← notMem_tsupport_iff_eventuallyEq, hχt]
        exact fun h => hy (hVW h).1
      refine (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq ?_
      filter_upwards [hyχ] with z hz
      simp [hz]
  -- Step 5: `Xᵀ` vanishes off the compact set `V̄`, and `spt Xᵀ ⊆ spt χ = V̄ ⊆ W ⊆ U`
  · refine HasCompactSupport.intro' hVc isClosed_closure fun y hy => ?_
    have hχy : χ y = 0 := by
      rw [← notMem_support, hχV]
      exact fun h => hy (subset_closure h)
    simp [hχy]
  · refine (tsupport_smul_subset_left χ fun y => pr y (X y)).trans ?_
    rw [hχt]
    exact fun z hz => (hVW hz).2
  -- Step 6: `Xᵀ = pr · X` near `x ∈ N`: `χ = 1` near `x` if `x ∈ spt X`, else `X = 0` near `x`
  · intro x hx
    by_cases hxX : x ∈ tsupport X
    · filter_upwards [isOpen_interior.mem_nhds (hKL ⟨hxX, subset_closure hx⟩)] with y hy
      rw [(hχL y).1 (interior_subset hy), one_smul]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxX] with y hy
      simp [hy]
/-- **Simon Ch. 4, 2.2–2.3** (additivity of the first variation of `V = v(M, θ)`): if
`x ↦ p_{TₓM}` is `Hⁿ⌞M`-measurable and `X, Y ∈ C¹_c(U; ℝᴾ)`, then `δV(X + Y) = δV(X) + δV(Y)`.
For `Z ∈ C¹_c(U; ℝᴾ)`, `θ div_M Z` is `Hⁿ⌞M`-integrable: `div_M Z(x) = tr(pₓ ∘ DZ(x))` is
measurable, `|div_M Z| ≤ ‖tr‖ sup ‖DZ‖` on `spt Z` and `div_M Z = 0` off `spt Z`, and `θ` is
integrable on the compact `spt Z ⊆ U`.  Pointwise `D(X + Y) = DX + DY` and the trace is linear, so
`div_M (X + Y) = div_M X + div_M Y`; integrate. -/
theorem Submission.mcs_firstVariation_add : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X Y : Euclid P → Euclid P), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ U → R.firstVariation (X + Y) = R.firstVariation X + R.firstVariation Y := by
  intro P n U R X Y hp hX hXc hXU hY hYc hYU
  -- Step 1: the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and
  -- `div_M Z(x) = tr(pₓ ∘ DZ(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ (Z : Euclid P → Euclid P) (x : Euclid P), tangentialDivergence n R.carrier Z x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ Z x) := fun _ _ => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθ' : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  -- Step 2: `θ div_M Z` is `Hⁿ⌞M`-integrable for `Z ∈ C¹_c(U; ℝᴾ)`
  have hint : ∀ Z : Euclid P → Euclid P, ContDiff ℝ 1 Z → HasCompactSupport Z → tsupport Z ⊆ U →
      Integrable (fun x => (R.mult x : ℝ) * tangentialDivergence n R.carrier Z x)
        (μHE[n].restrict R.carrier) := by
    intro Z hZ hZc hZU
    have hD : Continuous (fderiv ℝ Z) := hZ.continuous_fderiv one_ne_zero
    -- Step 2(a): `div_M Z` is a.e. strongly measurable (`p` measurable, `DZ` continuous)
    have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier Z x)
        (μHE[n].restrict R.carrier) :=
      (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
        (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp hD.aestronglyMeasurable
    -- Step 2(b): `|θ div_M Z| ≤ ‖tr‖ C θ 1_K`, `K = spt Z`, `C = sup ‖DZ‖`
    obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hZc.fderiv ℝ)
    have hKm : MeasurableSet (tsupport Z) := (isClosed_tsupport Z).measurableSet
    have hbound : ∀ x, ‖(R.mult x : ℝ) * tangentialDivergence n R.carrier Z x‖ ≤
        (tsupport Z).indicator (fun x => ‖tr‖ * C * (R.mult x : ℝ)) x := by
      intro x
      rw [norm_mul, Real.norm_natCast, hdiv]
      by_cases hxK : x ∈ tsupport Z
      · rw [Set.indicator_of_mem hxK, mul_comm (R.mult x : ℝ)]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _)
          zero_le_one
      · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
          ContinuousLinearMap.comp_zero, map_zero, norm_zero, mul_zero]
    -- Step 2(c): `θ` is `Hⁿ⌞M`-integrable on `K`, since `∫_{M ∩ K} θ dHⁿ < ∞`
    have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) (tsupport Z) (μHE[n].restrict R.carrier) := by
      rw [IntegrableOn, Measure.restrict_restrict hKm, Set.inter_comm]
      simpa using integrable_toReal_of_lintegral_ne_top hθ'.aemeasurable
        (R.locallyIntegrable_mult _ hZc hZU)
    exact ((integrable_indicator_iff hKm).2 (Integrable.const_mul hθK (‖tr‖ * C))).mono'
      (hθ.aestronglyMeasurable.mul hmeas) (ae_of_all _ hbound)
  -- Step 3: `div_M (X + Y) = div_M X + div_M Y` pointwise
  have hadd : ∀ x, tangentialDivergence n R.carrier (X + Y) x =
      tangentialDivergence n R.carrier X x + tangentialDivergence n R.carrier Y x := by
    intro x
    rw [hdiv, hdiv, hdiv, fderiv_add (hX.differentiable one_ne_zero x)
      (hY.differentiable one_ne_zero x), ContinuousLinearMap.comp_add, map_add]
  -- Step 4: integrate, by `integral_add`
  simp only [IMRep.firstVariation, hadd, mul_add]
  exact integral_add (hint X hX hXc hXU) (hint Y hY hYc hYU)
/-- **Simon Ch. 4, 3.14–3.15**: the mean curvature field `H(x) = Σⱼ (Dpr(x)[p(x)eⱼ])^*(p(x)eⱼ)`
on `N ∩ U`, `H = 0` elsewhere, is `μ`-a.e. strongly measurable and bounded on compact `K ⊆ U`.
`N ∩ U = N̄ ∩ U` is Borel, `x ↦ (Dpr(x), p(x))` is a.e. strongly measurable and
`(B, q) ↦ Σⱼ (B(qeⱼ))^*(qeⱼ)` is continuous; for compact `K ⊆ U`, `K ∩ N̄ ⊆ N ⊆ O` is compact and
`Dpr` is continuous on the open `O`, so `‖H‖ ≤ P max(sup_{K ∩ N̄} ‖Dpr‖, 0)` on `K`. -/
theorem Submission.mcs_exists_meanCurvature_field : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U N O : Set (Euclid P)) (pr p : Euclid P → (Euclid P →L[ℝ] Euclid P)), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H μ ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ x ∈ K, ‖H x‖ ≤ Λ) ∧ ∀ x ∈ N ∩ U, H x = ∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1)) := by
  intro P μ U N O pr p hU hO hNO hpr hNU hp hp1
  -- `F(B, q) = Σⱼ (B(qeⱼ))^*(qeⱼ)`, `eⱼ` the standard basis of `ℝᴾ`, is continuous
  let F : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) × (Euclid P →L[ℝ] Euclid P) → Euclid P :=
    fun q => ∑ j : Fin P, ContinuousLinearMap.adjoint (q.1 (q.2 (EuclideanSpace.single j 1)))
      (q.2 (EuclideanSpace.single j 1))
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun j _ => ?_
    have hq : Continuous fun q : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) ×
        (Euclid P →L[ℝ] Euclid P) => q.2 (EuclideanSpace.single j 1) :=
      continuous_snd.clm_apply continuous_const
    exact (ContinuousLinearMap.adjoint.continuous.comp (continuous_fst.clm_apply hq)).clm_apply hq
  -- `N ∩ U = N̄ ∩ U` is Borel
  have hG : N ∩ U = closure N ∩ U := by
    refine Subset.antisymm (inter_subset_inter_left _ subset_closure) fun z hz => ⟨?_, hz.2⟩
    by_contra hzN
    have hz' : z ∈ (closure N \ N) ∩ U := ⟨⟨hz.1, hzN⟩, hz.2⟩
    rw [hNU] at hz'
    exact hz'
  have hGm : MeasurableSet (N ∩ U) := by
    rw [hG]
    exact isClosed_closure.measurableSet.inter hU.measurableSet
  -- `H = 1_{N ∩ U} F(Dpr, p)`
  refine ⟨(N ∩ U).indicator fun x => F (fderiv ℝ pr x, p x), ?_, ?_,
    fun x hx => indicator_of_mem hx _⟩
  · exact (hF.comp_aestronglyMeasurable
      ((measurable_fderiv ℝ pr).aestronglyMeasurable.prodMk hp)).indicator hGm
  -- `‖Dpr‖ ≤ C` on the compact `K ∩ N̄ ⊆ N ⊆ O`, so `‖H‖ ≤ P max(C, 0)` on `K`
  intro K hK hKU
  have hKN : K ∩ closure N ⊆ N ∩ U := fun x hx => by
    rw [hG]
    exact ⟨hx.2, hKU hx.1⟩
  obtain ⟨C, hC⟩ := (hK.inter_right isClosed_closure).exists_bound_of_continuousOn
    ((hpr.continuousOn_fderiv_of_isOpen hO le_rfl).mono fun x hx => hNO (hKN hx).1)
  refine ⟨P * max C 0, fun x hxK => ?_⟩
  by_cases hx : x ∈ N ∩ U
  · rw [indicator_of_mem hx]
    have hDx : ‖fderiv ℝ pr x‖ ≤ max C 0 :=
      (hC x ⟨hxK, subset_closure hx.1⟩).trans (le_max_left _ _)
    have hj : ∀ j : Fin P, ‖ContinuousLinearMap.adjoint
        (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1))‖ ≤
        max C 0 := by
      intro j
      have hu : ‖p x (EuclideanSpace.single j 1)‖ ≤ 1 :=
        calc ‖p x (EuclideanSpace.single j 1)‖
            ≤ ‖p x‖ * ‖(EuclideanSpace.single j 1 : Euclid P)‖ := (p x).le_opNorm _
          _ = ‖p x‖ := by simp
          _ ≤ 1 := hp1 x
      calc ‖ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1)))
              (p x (EuclideanSpace.single j 1))‖
          ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1)))‖ *
              ‖p x (EuclideanSpace.single j 1)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ pr x (p x (EuclideanSpace.single j 1))‖ *
              ‖p x (EuclideanSpace.single j 1)‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ ‖fderiv ℝ pr x‖ * ‖p x (EuclideanSpace.single j 1)‖ *
              ‖p x (EuclideanSpace.single j 1)‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ max C 0 * 1 * 1 := by gcongr
        _ = max C 0 := by ring
    calc ‖F (fderiv ℝ pr x, p x)‖
        ≤ ∑ j : Fin P, ‖ContinuousLinearMap.adjoint
            (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin P, max C 0 := Finset.sum_le_sum fun j _ => hj j
      _ = P * max C 0 := by simp
  · rw [indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
/-- **Flatness of a submanifold at a chart point** (step 2 of the approximate-tangent-space
argument; Simon Ch. 2, 4.1–4.3).  Let `ψ : V → W` be a 1:1 `C¹` map with `ψ(V) = W ∩ N`, proper
into `W`, and `Dψ(v)` injective.  Then near `ψ(v)` every `z ∈ N` lies within `ε|z − ψ(v)|` of
`ψ(v) + range Dψ(v)`.  Properness, continuity and injectivity of `ψ` force `z = ψ(β)` with `β`
close to `v`; the first-order expansion at `v` and the coercivity `|h| ≤ K|Dψ(v)h|` then absorb
the remainder. -/
theorem Submission.atsm_chart_image_flat : ∀ (P d : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → Injective (fderiv ℝ ψ v) → v ∈ V → ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z (ψ v) < ρ → ∃ h : Euclid d, ‖z - ψ v - fderiv ℝ ψ v h‖ ≤ ε * ‖z - ψ v‖ := by
  intro P d N W V ψ v hV hW hψ hinj himg hprop hLinj hv ε hε
  set L := fderiv ℝ ψ v with hLdef
  have hdiff : DifferentiableAt ℝ ψ v :=
    (hψ.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)
  have hL : HasFDerivAt ψ L v := hdiff.hasFDerivAt
  have hcont : ContinuousOn ψ V := hψ.continuousOn
  have hψvW : ψ v ∈ W := by
    have : ψ v ∈ ψ '' V := mem_image_of_mem ψ hv
    rw [himg] at this
    exact this.1
  -- coercivity of the injective derivative
  obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith (L : Euclid d →ₗ[ℝ] Euclid P)
    (LinearMap.ker_eq_bot.mpr hLinj)
  have hcoer : ∀ h : Euclid d, ‖h‖ ≤ K * ‖L h‖ := fun h =>
    ContinuousLinearMap.bound_of_antilipschitz L hK h
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
  set η : ℝ := min (1 / (2 * K)) (ε / (2 * K)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηK : η * K ≤ 1 / 2 := by
    calc η * K ≤ 1 / (2 * K) * K := by gcongr; exact min_le_left _ _
      _ = 1 / 2 := by field_simp
  have hηε : η * (2 * K) ≤ ε := by
    calc η * (2 * K) ≤ ε / (2 * K) * (2 * K) := by gcongr; exact min_le_right _ _
      _ = ε := by field_simp
  -- first-order expansion
  obtain ⟨σ, hσ, hσball⟩ := Metric.eventually_nhds_iff.1 (hL.isLittleO.bound hη)
  -- a compact set away from v
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψvW
  set δ₀ : ℝ := δ₁ / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hcbW : closedBall (ψ v) δ₀ ⊆ W := (closedBall_subset_ball (by linarith)).trans hδ₁W
  have hA : IsCompact (V ∩ ψ ⁻¹' closedBall (ψ v) δ₀) := hprop _ hcbW (isCompact_closedBall _ _)
  set C := (V ∩ ψ ⁻¹' closedBall (ψ v) δ₀) \ ball v σ with hCdef
  have hC : IsCompact C := hA.diff isOpen_ball
  have hCV : C ⊆ V := fun β hβ => hβ.1.1
  -- positive separation on C
  obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ β ∈ C, m ≤ ‖ψ β - ψ v‖ := by
    rcases C.eq_empty_or_nonempty with hCe | hCne
    · refine ⟨1, one_pos, fun β hβ => ?_⟩
      rw [hCe] at hβ
      exact hβ.elim
    · have hfc : ContinuousOn (fun β => ‖ψ β - ψ v‖) C :=
        ((hcont.mono hCV).sub continuousOn_const).norm
      obtain ⟨β₀, hβ₀C, hβ₀min⟩ := hC.exists_isMinOn hCne hfc
      refine ⟨‖ψ β₀ - ψ v‖, ?_, fun β hβ => (isMinOn_iff.mp hβ₀min) β hβ⟩
      rcases (norm_nonneg (ψ β₀ - ψ v)).lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have h0 : ψ β₀ = ψ v := by
          have h' := heq.symm
          rwa [norm_eq_zero, sub_eq_zero] at h'
        have hβv := hinj (hCV hβ₀C) hv h0
        apply hβ₀C.2
        rw [hβv]
        exact mem_ball_self hσ
  refine ⟨min δ₀ m, lt_min hδ₀ hm, ?_⟩
  intro z hzN hzd
  have hzcb : z ∈ closedBall (ψ v) δ₀ := mem_closedBall.2 (hzd.trans_le (min_le_left _ _)).le
  have hzim : z ∈ ψ '' V := by
    rw [himg]
    exact ⟨hcbW hzcb, hzN⟩
  obtain ⟨β, hβV, rfl⟩ := hzim
  have hβA : β ∈ V ∩ ψ ⁻¹' closedBall (ψ v) δ₀ := ⟨hβV, hzcb⟩
  have hβσ : dist β v < σ := by
    by_contra hcon
    have hβC : β ∈ C := ⟨hβA, fun hb => hcon (mem_ball.1 hb)⟩
    have h1 := hmC β hβC
    rw [← dist_eq_norm] at h1
    have h2 : min δ₀ m ≤ dist (ψ β) (ψ v) := (min_le_right _ _).trans h1
    linarith
  refine ⟨β - v, ?_⟩
  have hest : ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hσball hβσ
  have hLh : ‖L (β - v)‖ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by
    calc ‖L (β - v)‖ = ‖(ψ β - ψ v) - (ψ β - ψ v - L (β - v))‖ := by congr 1; abel
      _ ≤ ‖ψ β - ψ v‖ + ‖ψ β - ψ v - L (β - v)‖ := norm_sub_le _ _
      _ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by gcongr
  have hh : ‖β - v‖ ≤ 2 * K * ‖ψ β - ψ v‖ := by
    have h2 : ‖β - v‖ ≤ K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by
      calc ‖β - v‖ ≤ K * ‖L (β - v)‖ := hcoer (β - v)
        _ ≤ K * (‖ψ β - ψ v‖ + η * ‖β - v‖) := by gcongr
        _ = K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by ring
    have h3 : (η * K) * ‖β - v‖ ≤ 1 / 2 * ‖β - v‖ := by gcongr
    linarith
  calc ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ β - ψ v‖) := by gcongr
    _ = (η * (2 * K)) * ‖ψ β - ψ v‖ := by ring
    _ ≤ ε * ‖ψ β - ψ v‖ := by gcongr
/-- **Simon Ch. 3, Definition 1.4 and Remark 1.5(1)**: an approximate tangent space of `M` at `x`
lies in every subspace `T` along which a set `N` carrying `Hⁿ`-almost all of `M` is flat at `x`
(for each `ε > 0` there is `ρ > 0` such that every `z ∈ N` with `|z − x| < ρ` has some `t ∈ T`
with `|z − x − t| ≤ ε|z − x|`).  If `q ∈ Q \ T`, put `δ = dist(q, T) > 0` and
`g = max(0, δ/2 − |· − q|) ∈ C_c(ℝᴾ)`; `∫_Q g dHⁿ > 0` because `spt(Hⁿ⌞Q) = Q`.  With
`ε = δ / (2(|q| + δ))` and `0 < r < ρ / (|q| + δ)`, flatness makes `g` vanish on `η_{x,r}(M ∩ N)`,
and `Hⁿ(η_{x,r}(M \ N)) = 0`; so `∫_{η_{x,r}(M)} g dHⁿ = 0` for all small `r`, contradicting
the defining limit. -/
theorem Submission.atsm_approxTangent_le_of_flat : ∀ (P n : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q T : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z x < ρ → ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → HasApproximateTangentSpaceAt n M x Q → Q ≤ T := by
  intro P n N M x Q T hnull hflat hQ q hq
  by_contra hqT
  -- `T` is closed, so `δ = dist(q, T) > 0`
  have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
  have hδ : 0 < infDist q (T : Set (Euclid P)) :=
    (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
  set δ := infDist q (T : Set (Euclid P)) with hδdef
  -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
  set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
  have hgc : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg0 : 0 ≤ g := fun y => le_max_left _ _
  have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
    intro y hy
    by_contra h
    have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
    apply hy
    exact max_eq_left (by linarith)
  have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
    lt_max_of_lt_right (by linarith)
  have hgcs : HasCompactSupport g := by
    apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
    intro y hy
    by_contra h
    apply hy
    rw [mem_closedBall, dist_eq_norm]
    exact (hgsupp y h).le
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
  -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
  have hQn : Module.finrank ℝ Q = n := hQ.1
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
  have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
  have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
    hgc.integrable_of_hasCompactSupport hgcs
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg0 hint]
    have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
      rw [hsupp]
      exact hq
    have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
        (ball q (δ / 2)) :=
      (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
    refine hball.trans_le (measure_mono ?_)
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact (hgpos y hy).ne'
  -- constants: `ε (|q| + δ) = δ / 2`
  have hqδ : 0 < ‖q‖ + δ := by positivity
  set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
  have hε : 0 < ε := by positivity
  have hεq : ε * (‖q‖ + δ) = δ / 2 := by
    rw [hεdef]
    field_simp
  obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
  -- `∫_{η_{x,r}(M)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
  have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = 0 := by
    intro r hr hrρ
    -- `η_{x,r}(M \ N) = r⁻¹ (M \ N − x)` is `Hⁿ`-null
    have hnull' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N)) = 0 := by
      have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (M \ N)) := by
        rw [Set.image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq fun a b => dist_sub_right a b x
      rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, hnull, smul_zero]
    -- flatness: `g` vanishes on `η_{x,r}(M ∩ N)`
    have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ⊆
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M \ N) := by
      rintro y ⟨hgy, z, hzM, rfl⟩
      refine ⟨z, ⟨hzM, fun hzN => ?_⟩, rfl⟩
      have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
      set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
      have hy' : y = r⁻¹ • (z - x) := rfl
      have hzx : z - x = r • y := by
        rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
        calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
          _ < δ / 2 + ‖q‖ := by linarith
          _ = ‖q‖ + δ / 2 := by ring
      have hzxn : ‖z - x‖ = r * ‖y‖ := by
        rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
      have hdist : dist z x < ρ := by
        rw [dist_eq_norm, hzxn]
        calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
          _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
          _ = ρ := by field_simp
      obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
      have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
      have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
        rw [hy']
        exact (smul_sub _ _ _).symm
      have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
        rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
          _ = ε * ‖y‖ := by rw [hzxn]; field_simp
      have hle : δ ≤ ‖q - r⁻¹ • t‖ := by
        rw [← dist_eq_norm]
        exact infDist_le_dist_of_mem hrt
      have h2 : ε * ‖y‖ ≤ δ / 2 := by
        rw [← hεq]
        gcongr
        linarith
      have hlt : ‖q - r⁻¹ • t‖ < δ := by
        calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
          _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
          _ < δ / 2 + δ / 2 := by
            have h1 : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
            linarith
          _ = δ := by ring
      linarith
    -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(M)`, evaluated on the open set `{g ≠ 0}`
    have hopen : MeasurableSet {y | g y ≠ 0} :=
      (isOpen_ne_fun hgc continuous_const).measurableSet
    apply integral_eq_zero_of_ae
    rw [EventuallyEq, ae_iff]
    change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) {y | g y ≠ 0} = 0
    rw [Measure.restrict_apply hopen]
    exact measure_mono_null hsub hnull'
  -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
  have hlim := hQ.2 f
  have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n])
      =ᶠ[𝓝[>] 0] fun _ => 0 := by
    have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
    exact hvan r hr.1 hr.2
  have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M,
      f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' hev.symm
  have heq := tendsto_nhds_unique hlim hlim0
  have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
  linarith
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)
/-- Simon 6.2.23 (setting of the push-forward `φ_#T`; step 1 of the parent proof): a `C¹`
bijection `φ` of `ℝᴾ` with injective differential everywhere and `φ = id` off the compact set
`K ⊆ U` is bi-Lipschitz, and `φ⁻¹(U) = U`.  `‖Dφ‖` is bounded (continuous on `K`, `Dφ = I` off
`K`), so `φ` is Lipschitz by the mean value inequality; `φ` is proper (`φ⁻¹(C) ⊆ C ∪ K`), hence
a homeomorphism; `φ⁻¹` is `C¹` by the inverse function theorem and equals `id` off `K`, so it is
Lipschitz as well, i.e. `φ` is antilipschitz. -/
theorem Submission.dpf_c1_compact_perturbation_bilipschitz : ∀ (P : ℕ) (U K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → (∀ x, x ∉ K → φ x = x) → ∃ Λ : NNReal, LipschitzWith Λ φ ∧ AntilipschitzWith Λ φ ∧ φ ⁻¹' U = U := by
  intro P U K φ hK hKU hφ hbij hinj hfix
  -- Steps 1, 3 and 6: a `C¹` map `f` equal to the identity off `K` has bounded differential
  -- (`Df = I` on the open set `ℝᴾ \ K`, `‖Df‖` bounded on the compact `K`), hence is Lipschitz
  have hlip : ∀ f : Euclid P → Euclid P, ContDiff ℝ 1 f → (∀ x, x ∉ K → f x = x) →
      ∃ C : NNReal, LipschitzWith C f := by
    intro f hf hfixf
    obtain ⟨c, hc⟩ :=
      hK.exists_bound_of_continuousOn (hf.continuous_fderiv one_ne_zero).continuousOn
    refine ⟨max 1 c.toNNReal,
      lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) fun x => ?_⟩
    by_cases hx : x ∈ K
    · refine le_trans ?_ (le_max_right _ _)
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact (hc x hx).trans c.le_coe_toNNReal
    · have hev : f =ᶠ[𝓝 x] id := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy using hfixf y hy
      rw [hev.fderiv_eq, fderiv_id]
      refine le_trans ?_ (le_max_left _ _)
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact ContinuousLinearMap.norm_id_le
  -- Step 2: `φ⁻¹(U) = U`
  have hpre : φ ⁻¹' U = U := by
    ext x
    rw [mem_preimage]
    constructor
    · intro hx
      by_contra hxU
      have hxK : x ∉ K := fun h => hxU (hKU h)
      rw [hfix x hxK] at hx
      exact hxU hx
    · intro hx
      by_cases hxK : x ∈ K
      · apply hKU
        by_contra hφK
        have hφx : φ x = x := hbij.1 (hfix (φ x) hφK)
        exact hφK (by rwa [hφx])
      · rw [hfix x hxK]
        exact hx
  -- Step 4: `φ` is proper (`φ⁻¹(C) ⊆ C ∪ K`), hence closed, hence a homeomorphism
  have hcont : Continuous φ := hφ.continuous
  have hclosed : IsClosedMap φ := by
    refine (isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun C hC => ?_⟩).isClosedMap
    refine (hC.union hK).of_isClosed_subset (hC.isClosed.preimage hcont) fun x hx => ?_
    by_cases hxK : x ∈ K
    · exact Or.inr hxK
    · left
      simpa [hfix x hxK] using hx
  obtain ⟨e, rfl⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = φ :=
    ⟨(Equiv.ofBijective φ hbij).toHomeomorphOfContinuousClosed hcont hclosed, rfl⟩
  -- Step 5: `ψ = φ⁻¹` is `C¹`, each `Dφ(a)` being a linear isomorphism
  have hψ : ContDiff ℝ 1 e.symm := by
    refine e.contDiff_symm (f₀' := fun a => (LinearEquiv.ofInjectiveEndo
      (fderiv ℝ e a : Euclid P →ₗ[ℝ] Euclid P) (hinj a)).toContinuousLinearEquiv)
      (fun a => ?_) hφ
    have h1 : ((LinearEquiv.ofInjectiveEndo (fderiv ℝ e a : Euclid P →ₗ[ℝ] Euclid P)
        (hinj a)).toContinuousLinearEquiv : Euclid P →L[ℝ] Euclid P) = fderiv ℝ e a := by
      ext v
      rfl
    rw [h1]
    exact (hφ.differentiable one_ne_zero a).hasFDerivAt
  -- Step 6: `ψ = id` off `K`
  have hψfix : ∀ y, y ∉ K → e.symm y = y := fun y hy => e.symm_apply_eq.2 (hfix y hy).symm
  obtain ⟨C₁, hC₁⟩ := hlip e hφ hfix
  obtain ⟨C₂, hC₂⟩ := hlip e.symm hψ hψfix
  -- Steps 7 and 8: `φ` is `C₂`-antilipschitz; take `Λ = max C₁ C₂`
  refine ⟨max C₁ C₂, hC₁.weaken (le_max_left _ _), fun x y => ?_, hpre⟩
  calc edist x y = edist (e.symm (e x)) (e.symm (e y)) := by simp
    _ ≤ C₂ * edist (e x) (e y) := hC₂ _ _
    _ ≤ max C₁ C₂ * edist (e x) (e y) := by gcongr; exact le_max_right _ _
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
/-- **Image measure comparison** (image representation of the diffeomorphism push-forward, used
for Simon 7.1.2).  If `φ` is `Λ`-Lipschitz and `ψ` is a measurable left inverse of `φ`, then
`ψ_#(Hⁿ⌞φ(S)) ≤ Λⁿ Hⁿ⌞S` for every set `S`, not assumed measurable.  For Borel `A`,
`ψ⁻¹(A) ∩ φ(S) = φ(A ∩ S)`, and `Hⁿ(φ(A ∩ S)) ≤ Λⁿ Hⁿ(A ∩ S)` (Simon Ch. 2, 1.8(i)). -/
theorem Submission.dpfir_ii_map_restrict_image_le_smul : ∀ (P n : ℕ) (φ ψ : Euclid P → Euclid P) (Λ : NNReal) (S : Set (Euclid P)), LipschitzWith Λ φ → Measurable ψ → LeftInverse ψ φ → (μHE[n].restrict (φ '' S)).map ψ ≤ ((Λ : ℝ≥0∞) ^ n) • μHE[n].restrict S := by
  intro P n φ ψ Λ S hφ hψ hψφ
  refine Measure.le_iff.2 fun A hA => ?_
  -- `ψ⁻¹(A) ∩ φ(S) = φ(A ∩ S)`, as `ψ ∘ φ = id`
  have hset : ψ ⁻¹' A ∩ φ '' S = φ '' (A ∩ S) := by
    ext y
    constructor
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨by rwa [mem_preimage, hψφ x] at hy, hx⟩, rfl⟩
    · rintro ⟨x, ⟨hxA, hxS⟩, rfl⟩
      exact ⟨by rwa [mem_preimage, hψφ x], x, hxS, rfl⟩
  -- both sides are values of `μHE[n]`; no measurability of `S` or `φ '' S` is needed
  rw [Measure.map_apply hψ hA, Measure.restrict_apply (hψ hA), hset, Measure.smul_apply,
    Measure.restrict_apply hA, smul_eq_mul]
  exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
    hφ.lipschitzOnWith
/-- Lipschitz images of countably `n`-rectifiable sets are countably `n`-rectifiable (used in
Simon Ch. 6, 3.6–3.7; Ch. 3, Definition 1.1).  If `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and each
`Fⱼ` Lipschitz, then `φ(M) ⊆ φ(M₀) ∪ ⋃ⱼ (φ ∘ Fⱼ)(ℝⁿ)`, where `Hⁿ(φ(M₀)) ≤ Λⁿ Hⁿ(M₀) = 0`
(Simon Ch. 2, Theorem 1.8(i)) and `φ ∘ Fⱼ` is `Λ Kⱼ`-Lipschitz. -/
theorem Submission.dpfir_ii_countablyRectifiable_image_of_lipschitz : ∀ (P n : ℕ) (M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), LipschitzWith Λ φ → CountablyRectifiable n M → CountablyRectifiable n (φ '' M) := by
  intro P n M φ Λ hφ hM
  -- `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)` with `Hⁿ(M₀) = 0` and each `Fⱼ` Lipschitz
  obtain ⟨M₀, hM₀, F, hF, hMsub⟩ := hM
  refine ⟨φ '' M₀, ?_, fun j => φ ∘ F j, fun j => ?_, ?_⟩
  · -- `Hⁿ(φ(M₀)) ≤ Λⁿ Hⁿ(M₀) = 0`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hφ.lipschitzOnWith (s := M₀))
    rw [hM₀, mul_zero] at h
    exact nonpos_iff_eq_zero.1 h
  · -- `φ ∘ Fⱼ` is `Λ Kⱼ`-Lipschitz
    obtain ⟨K, hK⟩ := hF j
    exact ⟨Λ * K, hφ.comp hK⟩
  · -- `φ(M) ⊆ φ(M₀) ∪ ⋃ⱼ (φ ∘ Fⱼ)(ℝⁿ)`
    rintro _ ⟨x, hx, rfl⟩
    rcases hMsub hx with hx₀ | hxF
    · exact Or.inl (mem_image_of_mem φ hx₀)
    · obtain ⟨j, v, rfl⟩ := mem_iUnion.1 hxF
      exact Or.inr (mem_iUnion.2 ⟨j, v, rfl⟩)

/-- **Bi-Lipschitz image of an integer multiplicity triple** (image representation of the
diffeomorphism push-forward, used for Simon 7.1.2; cf. Simon 6.3.6–3.9 for injective `f`).  Let
`R = (M, θ, ξ)` be a triple in `U` and `φ : ℝᴾ → ℝᴾ` a bijection that is `Λ`-Lipschitz and
`Λ`-antilipschitz with `φ⁻¹(U) = U`.  If `η` is `Hⁿ⌞M`-a.e. strongly measurable and, for
`Hⁿ`-a.e. `x ∈ M`, `η(x)` orients the approximate tangent space of `φ(M)` at `φ(x)`, then
`(φ(M), θ ∘ φ⁻¹, η ∘ φ⁻¹)` is a triple in `U`.  The inverse `ψ = φ⁻¹` is `Λ`-Lipschitz, and
`ψ_#(Hⁿ⌞φ(S)) ≤ Λⁿ Hⁿ⌞S` makes `ψ` quasi-measure-preserving from `Hⁿ⌞φ(M)` to `Hⁿ⌞M` and gives
`∫_{φ(M) ∩ K} θ ∘ ψ dHⁿ ≤ Λⁿ ∫_{M ∩ φ⁻¹(K)} θ dHⁿ`. -/
theorem Submission.dpfir_bilipschitz_image_imrep_exists : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (φ : Euclid P → Euclid P) (Λ : NNReal) (η : Euclid P → MultiVector P n), Bijective φ → LipschitzWith Λ φ → AntilipschitzWith Λ φ → φ ⁻¹' U = U → AEStronglyMeasurable η (μHE[n].restrict R.carrier) → (∀ᵐ x ∂(μHE[n].restrict R.carrier), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (φ '' R.carrier) (φ x) Q ∧ IsUnitOrientationOf (η x) Q) → ∃ R' : IMRep U n, R'.carrier = φ '' R.carrier ∧ ∀ x, R'.mult (φ x) = R.mult x ∧ R'.orient (φ x) = η x := by
  intro P n U R φ Λ η hφ hφL hφA hU hη hηQ
  -- the two-sided inverse `ψ` of `φ` is `Λ`-Lipschitz, hence continuous and measurable
  obtain ⟨ψ, hleft, hright⟩ : ∃ ψ : Euclid P → Euclid P, LeftInverse ψ φ ∧ RightInverse ψ φ :=
    ⟨invFun φ, leftInverse_invFun hφ.1, rightInverse_invFun hφ.2⟩
  have hψc : Continuous ψ := (hφA.to_rightInverse hright).continuous
  have hψm : Measurable ψ := hψc.measurable
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
  -- `ψ_#(Hⁿ⌞φ(M)) ≤ Λⁿ Hⁿ⌞M`: `ψ` is quasi-measure-preserving from `Hⁿ⌞φ(M)` to `Hⁿ⌞M`
  have hqmp : Measure.QuasiMeasurePreserving ψ (μHE[n].restrict (φ '' R.carrier))
      (μHE[n].restrict R.carrier) :=
    ⟨hψm, Measure.absolutelyContinuous_of_le_smul
      (Submission.dpfir_ii_map_restrict_image_le_smul P n φ ψ Λ R.carrier hφL hψm hleft)⟩
  -- (a) `φ(M) = ψ⁻¹(M)` is Borel
  have hmeas : MeasurableSet (φ '' R.carrier) := by
    rw [image_eq_preimage_of_inverse hleft hright]
    exact hψm R.measurableSet_carrier
  -- (b) `φ(M) ⊆ φ(U) = U`, as `U = φ⁻¹(U)`
  have hsub : φ '' R.carrier ⊆ U := image_subset_iff.2 (R.carrier_subset.trans hU.symm.subset)
  -- (e) `θ(ψ(φ(x))) = θ(x) > 0` on `M`
  have hpos : ∀ y ∈ φ '' R.carrier, 0 < R.mult (ψ y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hleft x]
    exact R.mult_pos x hx
  -- (f) `∫_{φ(M) ∩ K} θ ∘ ψ dHⁿ ≤ Λⁿ ∫_{M ∩ φ⁻¹(K)} θ dHⁿ < ∞`, with `φ⁻¹(K) = ψ(K) ⊆ U` compact
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ y in φ '' R.carrier ∩ K, (R.mult (ψ y) : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hK' : IsCompact (φ ⁻¹' K) := by
      rw [← image_eq_preimage_of_inverse (f := ψ) (g := φ) hright hleft]
      exact hK.image hψc
    have hK'U : φ ⁻¹' K ⊆ U := (preimage_mono hKU).trans hU.subset
    have hle : ∫⁻ y in φ '' (R.carrier ∩ φ ⁻¹' K), (R.mult (ψ y) : ℝ≥0∞) ∂μHE[n] ≤
        (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ φ ⁻¹' K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
      calc ∫⁻ y in φ '' (R.carrier ∩ φ ⁻¹' K), (R.mult (ψ y) : ℝ≥0∞) ∂μHE[n]
          = ∫⁻ x, (R.mult x : ℝ≥0∞) ∂((μHE[n].restrict (φ '' (R.carrier ∩ φ ⁻¹' K))).map ψ) :=
            (lintegral_map hθm hψm).symm
        _ ≤ ∫⁻ x, (R.mult x : ℝ≥0∞)
              ∂(((Λ : ℝ≥0∞) ^ n) • μHE[n].restrict (R.carrier ∩ φ ⁻¹' K)) :=
            lintegral_mono' (Submission.dpfir_ii_map_restrict_image_le_smul P n φ ψ Λ _ hφL hψm
              hleft) le_rfl
        _ = (Λ : ℝ≥0∞) ^ n * ∫⁻ x in R.carrier ∩ φ ⁻¹' K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
            rw [lintegral_smul_measure, smul_eq_mul]
    rw [← image_inter_preimage]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (R.locallyIntegrable_mult _ hK' hK'U)) hle
  -- (h) the orientation hypothesis at `ψ(y)`, with `φ(ψ(y)) = y`
  have horients : ∀ᵐ y ∂(μHE[n].restrict (φ '' R.carrier)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (φ '' R.carrier) y Q ∧ IsUnitOrientationOf (η (ψ y)) Q := by
    filter_upwards [hqmp.ae hηQ] with y hy
    obtain ⟨Q, hQ, hηy⟩ := hy
    rw [hright y] at hQ
    exact ⟨Q, hQ, hηy⟩
  refine ⟨{ carrier := φ '' R.carrier
            mult := fun y => R.mult (ψ y)
            orient := fun y => η (ψ y)
            measurableSet_carrier := hmeas
            carrier_subset := hsub
            -- (c) Lipschitz images of countably `n`-rectifiable sets are rectifiable
            rectifiable :=
              Submission.dpfir_ii_countablyRectifiable_image_of_lipschitz P n R.carrier φ Λ hφL
                R.rectifiable
            -- (d) `θ ∘ ψ` is measurable
            measurable_mult := R.measurable_mult.comp hψm
            mult_pos := hpos
            locallyIntegrable_mult := hint
            -- (g) a.e. strong measurability transfers along `ψ`
            aestronglyMeasurable_orient := hη.comp_quasiMeasurePreserving hqmp
            orients := horients }, rfl, fun x => ⟨?_, ?_⟩⟩
  · exact congrArg R.mult (hleft x)
  · exact congrArg η (hleft x)
/-- **Pairing with a continuous covector field** (Simon Ch. 6, 3.1 (‡), 6.2.24(3)).  For an
integer multiplicity triple `R = (M, θ, ξ)` in `U` and a continuous `β : ℝᴾ → Λⁿ(ℝᴾ)` with
compact support `K = spt β ⊆ U`, `x ↦ θ(x) ⟨β(x), ξ(x)⟩` is `Hⁿ⌞M`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ`
with `τ` orthonormal `Hⁿ`-a.e. on `M`, so `|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by
`C θ 1_K` (`C` a bound for `‖β‖`), which is integrable because `∫_{M ∩ K} θ dHⁿ < ∞`. -/
theorem Submission.dpfir_imrep_pairing_continuous_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (β : Euclid P → Covector (Euclid P) n), Continuous β → HasCompactSupport β → tsupport β ⊆ U → Integrable (fun x => (R.mult x : ℝ) * R.orient x (β x)) (μHE[n].restrict R.carrier) := by
  intro P n U R β hβ hcpt hU
  set K : Set (Euclid P) := tsupport β
  /- Step 1: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ M`. -/
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
  /- Step 2: `β` is bounded by some `C` and vanishes off the compact, hence Borel, set
  `K = spt β ⊆ U`. -/
  obtain ⟨C, hC⟩ := hβ.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport β).measurableSet
  /- Step 3: `|θ ⟨β, ξ⟩| ≤ C θ 1_K` a.e. on `M`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (β x)‖ ≤ C * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm C]
      exact mul_le_mul_of_nonneg_left ((hx (β x)).trans (hC x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 4: `C θ 1_K` is integrable, since `∫_{M ∩ K} θ dHⁿ < ∞`. -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => C * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul C
  /- Step 5: the integrand is a.e. strongly measurable: `θ` is measurable, `ξ` is a.e. strongly
  measurable, `β` is continuous and evaluation `(ζ, α) ↦ ζ(α)` is continuous. -/
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (β x))
      (μHE[n].restrict R.carrier) :=
    hθm.aestronglyMeasurable.mul (happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hβ.aestronglyMeasurable))
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound
/-- **Area identity to Bochner integrals** (image representation of the diffeomorphism
push-forward, used for Simon 7.1.2).  Let `J ≥ 0` and `∫⁻ g dν = ∫⁻ J(x) g(φ(x)) dμ(x)` for every
`g : ℝᴾ → [0, ∞]`.  If `h` is `ν`-a.e. strongly measurable, `f` is `μ`-integrable and
`J(x) h(φ(x)) = f(x)` for `μ`-a.e. `x`, then `h` is `ν`-integrable and `∫ h dν = ∫ f dμ`.
Multiplication by `J(x) ≥ 0` commutes with `|·|`, `t⁺` and `t⁻`; apply the identity to `g = |h|`,
`h⁺`, `h⁻` and use `∫ F = ∫⁻ F⁺ − ∫⁻ F⁻`. -/
theorem Submission.dpfir_integral_eq_of_area_lintegral : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (φ : Euclid P → Euclid P) (J h f : Euclid P → ℝ), (∀ x, 0 ≤ J x) → (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y, g y ∂ν = ∫⁻ x, ENNReal.ofReal (J x) * g (φ x) ∂μ) → AEStronglyMeasurable h ν → Integrable f μ → (∀ᵐ x ∂μ, J x * h (φ x) = f x) → Integrable h ν ∧ ∫ y, h y ∂ν = ∫ x, f x ∂μ := by
  intro P μ ν φ J h f hJ harea hh hf hfh
  -- the identity for `g = |h|ₑ`, `ofReal h`, `ofReal (-h)`; the integrands agree `μ`-a.e.
  have habs : ∫⁻ y, ‖h y‖ₑ ∂ν = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    refine (harea fun y => ‖h y‖ₑ).trans (lintegral_congr_ae ?_)
    filter_upwards [hfh] with x hx
    rw [← hx, enorm_mul, Real.enorm_eq_ofReal (hJ x)]
  have hpos : ∫⁻ y, ENNReal.ofReal (h y) ∂ν = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    refine (harea fun y => ENNReal.ofReal (h y)).trans (lintegral_congr_ae ?_)
    filter_upwards [hfh] with x hx
    rw [← hx, ENNReal.ofReal_mul (hJ x)]
  have hneg : ∫⁻ y, ENNReal.ofReal (-h y) ∂ν = ∫⁻ x, ENNReal.ofReal (-f x) ∂μ := by
    refine (harea fun y => ENNReal.ofReal (-h y)).trans (lintegral_congr_ae ?_)
    filter_upwards [hfh] with x hx
    rw [← hx, ← mul_neg, ENNReal.ofReal_mul (hJ x)]
  -- `h` is `ν`-integrable, and `∫ F = (∫⁻ F⁺) - (∫⁻ F⁻)` on both sides
  have hint : Integrable h ν :=
    ⟨hh, hasFiniteIntegral_iff_enorm.2 (habs ▸ hasFiniteIntegral_iff_enorm.1 hf.hasFiniteIntegral)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hint,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf, hpos, hneg]
/-- **The chosen approximate tangent plane** (Simon Ch. 3, Remark 1.5(1), used for 7.1.2).  If `Q`
is an approximate tangent space of `M` at `x` (Ch. 3, 1.4), then `approxTangentPlane n M x = Q`:
`Q` witnesses the existential in its definition, so it returns the chosen plane, which is an
approximate tangent space of `M` at `x` and hence equals `Q` by uniqueness. -/
theorem Submission.dpf_itt_approxTangentPlane_eq : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), HasApproximateTangentSpaceAt n M x Q → approxTangentPlane n M x = Q := by
  intro P n M x Q hQ
  have h : ∃ Q', HasApproximateTangentSpaceAt n M x Q' := ⟨Q, hQ⟩
  unfold approxTangentPlane
  rw [dite_eq_left h]
  exact h.choose_spec.unique hQ
/-- **Bi-Lipschitz images of Borel, locally `Hⁿ`-finite subsets of `U`** (Simon 6.3.7, the image
`φ(M)` in the push-forward of `τ(M, θ, ξ)` by a diffeomorphism, used in 7.1.2).  If `M ⊆ U` is
Borel with `Hⁿ(M ∩ C) < ∞` for every compact `C ⊆ U`, and `φ : ℝᴾ → ℝᴾ` is `Λ`-Lipschitz and
`Λ'`-antilipschitz with `φ⁻¹(U) = U`, then `φ(M)` is Borel (Lusin–Souslin: `φ` is continuous and
injective), `φ(M) ⊆ U`, and `Hⁿ(φ(M) ∩ C) ≤ Λⁿ Hⁿ(M ∩ φ⁻¹(C)) < ∞` for every compact `C ⊆ U`,
because `φ⁻¹(C)` is closed and bounded, hence a compact subset of `φ⁻¹(U) = U`. -/
theorem Submission.dpf_itt_bilipschitz_image_locfin : ∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ Λ' : NNReal), MeasurableSet M → M ⊆ U → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → LipschitzWith Λ φ → AntilipschitzWith Λ' φ → φ ⁻¹' U = U → MeasurableSet (φ '' M) ∧ φ '' M ⊆ U ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (φ '' M ∩ C) ≠ ∞ := by
  intro P n U M φ Λ Λ' hM hMU hfin hL hA hU
  -- Step 1: `φ` is continuous (Lipschitz) and injective (antilipschitz)
  have hcont : Continuous φ := hL.continuous
  have hinj : Injective φ := hA.injective
  -- Step 2: `φ(M)` is Borel by the Lusin–Souslin theorem
  refine ⟨hM.image_of_continuousOn_injOn hcont.continuousOn hinj.injOn, ?_, ?_⟩
  -- Step 3: `φ(M) ⊆ U`, since `M ⊆ U = φ⁻¹(U)`
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ φ ⁻¹' U := by
      rw [hU]
      exact hMU hx
    exact hx'
  · intro C hC hCU
    -- Step 4: `K = φ⁻¹(C)` is closed and bounded, hence compact, and `K ⊆ φ⁻¹(U) = U`
    have hK : IsCompact (φ ⁻¹' C) :=
      Metric.isCompact_of_isClosed_isBounded (hC.isClosed.preimage hcont)
        (hA.isBounded_preimage hC.isBounded)
    have hKU : φ ⁻¹' C ⊆ U := by
      rw [← hU]
      exact preimage_mono hCU
    have hMK : μHE[n] (M ∩ φ ⁻¹' C) ≠ ∞ := hfin _ hK hKU
    -- Step 5: `Hⁿ(φ(S)) ≤ Λⁿ Hⁿ(S)`, since `μHE[n] = c • μH[n]` for a constant `c`
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hle (S : Set (Euclid P)) : μHE[n] (φ '' S) ≤ (Λ : ℝ≥0∞) ^ (n : ℝ) * μHE[n] S := by
      simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
        smul_eq_mul]
      calc _ ≤ _ * ((Λ : ℝ≥0∞) ^ (n : ℝ) * μH[n] S) :=
            mul_le_mul_right (hL.hausdorffMeasure_image_le hn S) _
        _ = _ := by ring
    -- Step 6: `φ(M) ∩ C = φ(M ∩ K)`, so `Hⁿ(φ(M) ∩ C) ≤ Λⁿ Hⁿ(M ∩ K) < ∞`
    rw [← image_inter_preimage]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hn ENNReal.coe_ne_top) hMK) (hle _)
/-- Composing a bi-Lipschitz immersed piece `F` with a bi-Lipschitz immersion `φ` of `ℝᴾ`:
`φ ∘ F` is `ΛL`-Lipschitz, bounded below on `B` by `m' = m / (Λ' + 1)`, differentiable on `B` with
injective derivative `D(φ ∘ F)(a) = Dφ(F a) ∘ DF(a)` (chain rule), and so
`range D(φ ∘ F)(a) = Dφ(F a)(range DF(a))`. -/
theorem Submission.dpf_itt_comp_bilipschitz_piece : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (φ : Euclid P → Euclid P) (B : Set (Euclid n)) (L Λ Λ' : NNReal) (m : ℝ), LipschitzWith L F → 0 < m → (∀ a ∈ B, ∀ a' ∈ B, m * ‖a - a'‖ ≤ ‖F a - F a'‖) → (∀ a ∈ B, DifferentiableAt ℝ F a ∧ Injective (fderiv ℝ F a)) → Differentiable ℝ φ → (∀ x, Injective (fderiv ℝ φ x)) → LipschitzWith Λ φ → AntilipschitzWith Λ' φ → LipschitzWith (Λ * L) (φ ∘ F) ∧ (∃ m' : ℝ, 0 < m' ∧ ∀ a ∈ B, ∀ a' ∈ B, m' * ‖a - a'‖ ≤ ‖(φ ∘ F) a - (φ ∘ F) a'‖) ∧ (∀ a ∈ B, DifferentiableAt ℝ (φ ∘ F) a ∧ Injective (fderiv ℝ (φ ∘ F) a)) ∧ ∀ a ∈ B, LinearMap.range (fderiv ℝ (φ ∘ F) a : Euclid n →ₗ[ℝ] Euclid P) = Submodule.map (fderiv ℝ φ (F a) : Euclid P →ₗ[ℝ] Euclid P) (LinearMap.range (fderiv ℝ F a : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F φ B L Λ Λ' m hF hm hlow hdiff hφ hφinj hφL hφA
  refine ⟨hφL.comp hF, ⟨m / ((Λ' : ℝ) + 1), div_pos hm (by positivity), fun a ha a' ha' => ?_⟩,
    fun a ha => ⟨(hφ (F a)).comp a (hdiff a ha).1, ?_⟩, fun a ha => ?_⟩
  · have h1 : ‖F a - F a'‖ ≤ (Λ' : ℝ) * ‖φ (F a) - φ (F a')‖ := by
      simpa only [dist_eq_norm] using hφA.le_mul_dist (F a) (F a')
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), comp_apply, comp_apply]
    nlinarith [hlow a ha a' ha', norm_nonneg (φ (F a) - φ (F a'))]
  · rw [fderiv_comp a (hφ (F a)) (hdiff a ha).1, ContinuousLinearMap.coe_comp]
    exact (hφinj (F a)).comp (hdiff a ha).2
  · rw [fderiv_comp a (hφ (F a)) (hdiff a ha).1, ContinuousLinearMap.toLinearMap_comp]
    exact LinearMap.range_comp _ _
/-- **A.e. transfer through Lipschitz pieces** (step 6 of the image tangent transport).  Let
`M ⊆ ℝᴾ` be Borel with `Hⁿ(M \ ⋃ᵢ Fᵢ(Bᵢ)) = 0` for Lipschitz `Fᵢ : ℝⁿ → ℝᴾ`.  If `p (Fᵢ b)` holds
for Lebesgue-a.e. `b ∈ Bᵢ`, then `p x` holds for `Hⁿ`-a.e. `x ∈ M`: the bad parameters
`Nᵢ ⊆ Bᵢ` are Lebesgue-null, so `Hⁿ(Fᵢ(Nᵢ)) ≤ Lᵢⁿ Hⁿ(Nᵢ) = 0` (`Hⁿ = Lⁿ` on `ℝⁿ`), and every
`x ∈ M` with `¬p x` lies in `(M \ ⋃ᵢ Fᵢ(Bᵢ)) ∪ ⋃ᵢ Fᵢ(Nᵢ)`. -/
theorem Submission.dpf_itt_ae_of_ae_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)) (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (p : Euclid P → Prop), MeasurableSet M → (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) → μHE[n] (M \ ⋃ i, F i '' B i) = 0 → (∀ i, ∀ᵐ b ∂(volume.restrict (B i)), p (F i b)) → ∀ᵐ x ∂(μHE[n].restrict M), p x := by
  intro P n M F B p hM hF hcov hp
  -- `μHE[n] = c • μH[n]` with `c ≠ 0`
  have hc := Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n
  -- the bad parameters `Nᵢ = {b ∈ Bᵢ | ¬p (Fᵢ b)}` have `μHE[n]`-null images
  have hnull : ∀ i, μHE[n] (F i '' {b | ¬(b ∈ B i → p (F i b))}) = 0 := by
    intro i
    obtain ⟨L, hL⟩ := hF i
    have hN : μHE[n] {b | ¬(b ∈ B i → p (F i b))} = 0 := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact ae_iff.mp (ae_imp_of_ae_restrict (hp i))
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, smul_eq_zero] at hN ⊢
    exact Or.inr (le_zero_iff.mp ((hL.hausdorffMeasure_image_le (Nat.cast_nonneg n) _).trans_eq
      (by rw [hN.resolve_left hc, mul_zero])))
  -- every bad point of `M` lies in `(M \ ⋃ᵢ Fᵢ(Bᵢ)) ∪ ⋃ᵢ Fᵢ(Nᵢ)`
  rw [ae_restrict_iff' hM, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_union_null hcov (measure_iUnion_null hnull))
  obtain ⟨hxM, hpx⟩ := not_imp.mp hx
  by_cases hxU : x ∈ ⋃ i, F i '' B i
  · obtain ⟨i, b, hb, rfl⟩ := mem_iUnion.mp hxU
    exact Or.inr (mem_iUnion.mpr ⟨i, b, fun h => hpx (h hb), rfl⟩)
  · exact Or.inl ⟨hxM, hxU⟩
/-- **Splitting `∫_{φ(M)}` along a Borel decomposition of `M`.**  Let `Aᵢ ⊆ M` (`i ∈ ℕ`) be
pairwise disjoint Borel sets with `Hⁿ(M \ ⋃ᵢ Aᵢ) = 0`, and let `φ : ℝᴾ → ℝᴾ` be injective and
`Λ`-Lipschitz.  Then `∫_{φ(M)} g dHⁿ = Σᵢ ∫_{φ(Aᵢ)} g dHⁿ` for every `g : ℝᴾ → [0, ∞]`.  The
`φ(Aᵢ)` are Borel (Lusin–Souslin) and pairwise disjoint, `⋃ᵢ φ(Aᵢ) ⊆ φ(M)`, and
`φ(M) \ ⋃ᵢ φ(Aᵢ) ⊆ φ(M \ ⋃ᵢ Aᵢ)` has `Hⁿ`-measure `≤ Λⁿ · 0` (Simon Ch. 2, 1.8(i)). -/
theorem Submission.dpf_raf_lintegral_image_eq_tsum_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)) (A : ℕ → Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), (∀ i, MeasurableSet (A i)) → (∀ i, A i ⊆ M) → Pairwise (fun i j => Disjoint (A i) (A j)) → μHE[n] (M \ ⋃ i, A i) = 0 → LipschitzWith Λ φ → Injective φ → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' M, g y ∂μHE[n] = ∑' i, ∫⁻ y in φ '' A i, g y ∂μHE[n] := by
  intro P n M A φ Λ hA hAM hdisj hnull hφ hinj g
  -- each `φ(Aᵢ)` is Borel: `φ` is continuous and injective (Lusin–Souslin)
  have hmeas : ∀ i, MeasurableSet (φ '' A i) := fun i =>
    (hA i).image_of_continuousOn_injOn hφ.continuous.continuousOn hinj.injOn
  -- the `φ(Aᵢ)` are pairwise disjoint, as `φ` is injective
  have hdisj' : Pairwise (Disjoint on fun i => φ '' A i) := fun i j hij =>
    (disjoint_image_iff hinj).mpr (hdisj hij)
  -- `⋃ᵢ φ(Aᵢ) ⊆ φ(M)`
  have hsub : (⋃ i, φ '' A i) ⊆ φ '' M := iUnion_subset fun i => image_mono (hAM i)
  -- `φ(M) \ ⋃ᵢ φ(Aᵢ) ⊆ φ(M \ ⋃ᵢ Aᵢ)`, which is `Hⁿ`-null by the Lipschitz image bound
  have hdiff : φ '' M \ ⋃ i, φ '' A i ⊆ φ '' (M \ ⋃ i, A i) := by
    rintro y ⟨⟨x, hxM, rfl⟩, hy⟩
    refine ⟨x, ⟨hxM, fun hx => hy ?_⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, mem_image_of_mem φ hi⟩
  have hnull' : μHE[n] (φ '' M \ ⋃ i, φ '' A i) = 0 := by
    refine measure_mono_null hdiff (le_antisymm ?_ zero_le)
    calc μHE[n] (φ '' (M \ ⋃ i, A i)) ≤ (Λ : ℝ≥0∞) ^ n * μHE[n] (M \ ⋃ i, A i) :=
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
            hφ.lipschitzOnWith
      _ = 0 := by rw [hnull, mul_zero]
  -- so `φ(M) = ⋃ᵢ φ(Aᵢ)` `Hⁿ`-a.e., and the integral is countably additive over the `φ(Aᵢ)`
  have hae : φ '' M =ᵐ[μHE[n]] ⋃ i, φ '' A i :=
    ae_eq_set.mpr ⟨hnull', by rw [sdiff_eq_empty.mpr hsub, measure_empty]⟩
  rw [setLIntegral_congr hae, lintegral_iUnion hmeas hdisj' g]
/-- **Area formula on one injective Lipschitz piece** (Simon Ch. 3, 2.3–2.6, used for the
diffeomorphism push-forward in 7.1.2).  Let `F : ℝⁿ → ℝᴾ` be Lipschitz and injective on the Borel
set `B`, let `φ : ℝᴾ → ℝᴾ` be differentiable, Lipschitz and injective on `F(B)`, and let
`Q(F(b)) = range DF(b)` for a.e. `b ∈ B`.  With `e` the standard orthonormal basis of `Q(x)` and
`J(x) = √det(Dφ(x)eₐ · Dφ(x)e_b)`, every `g ≥ 0` has
`∫_{φ(F(B))} g dHⁿ = ∫_{F(B)} J(x) g(φ(x)) dHⁿ(x)`.  Apply the Lipschitz area formula to `φ ∘ F`
and to `F`; a.e. on `B` the chain rule and `normDet (S ∘ T) = normDet (S|_{range T}) · normDet T`
give `J_{φ∘F}(b) = J(F(b)) J_F(b)`, and `normDet (S|_V)² = det(S eₐ · S e_b)` (Gram). -/
theorem Submission.dpf_raf_piece_area_formula_gram : ∀ (P n : ℕ) (Q : Euclid P → Submodule ℝ (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal) (F : Euclid n → Euclid P) (L : NNReal) (B : Set (Euclid n)), Differentiable ℝ φ → LipschitzWith Λ φ → LipschitzWith L F → MeasurableSet B → InjOn F B → InjOn φ (F '' B) → (∀ᵐ b ∂(volume.restrict B), Q (F b) = LinearMap.range (fderiv ℝ F b : Euclid n →ₗ[ℝ] Euclid P)) → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' (F '' B), g y ∂μHE[n] = ∫⁻ x in F '' B, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) i)) (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (φ x) ∂μHE[n] := by
  intro P n Q φ Λ F L B hφd hφ hF hB hFi hφi hQ g
  -- Gram identity: `normDet (T|_W) = √det(⟨T eₐ, T e_b⟩)`, `e = stdOrthonormalBasis ℝ V`, `V = W`
  have hgram : ∀ (T : Euclid P →L[ℝ] Euclid P) (V W : Submodule ℝ (Euclid P)), V = W →
      Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ V) =>
        inner ℝ (T (stdOrthonormalBasis ℝ V i)) (T (stdOrthonormalBasis ℝ V j)))) =
        ((T : Euclid P →ₗ[ℝ] Euclid P).domRestrict W).normDet := by
    rintro T V W rfl
    have h := ((T : Euclid P →ₗ[ℝ] Euclid P).domRestrict V).normDet_sq_eq_det_gram
      (stdOrthonormalBasis ℝ V)
    rw [RCLike.ofReal_real_eq_id, id] at h
    rw [← Real.sqrt_sq (LinearMap.normDet_nonneg _), h]
    rfl
  -- area formula for `φ ∘ F` (injective on `B`, `φ(F(B)) = (φ ∘ F)(B)`) and for `F`
  have hn : Module.finrank ℝ (Euclid n) = n := finrank_euclideanSpace_fin
  have hleft := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn (hφ.comp hF) hB
    (hφi.comp hFi (mapsTo_image F B)) g
  have hright := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hF hB hFi
    (fun x => ENNReal.ofReal (Real.sqrt (Matrix.det
      (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) =>
        inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) i))
          (fderiv ℝ φ x (stdOrthonormalBasis ℝ (Q x) j))))) * g (φ x))
  rw [hn] at hleft hright
  rw [← image_comp, hleft, hright]
  -- the integrands agree `λ⌞B`-a.e. (Rademacher and the hypothesis on `Q`)
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hF.ae_differentiableAt, hQ] with b hb hQb
  rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet,
    Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, fderiv_comp b (hφd (F b)) hb,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.normDet_comp,
    ← hgram (fderiv ℝ φ (F b)) (Q (F b)) _ hQb,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _), comp_apply]
  ring
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

/-- **Simon 6.3.7** (the approximate tangent space of `φ(M)` at `φ(x)` is spanned by the images
`Dφ(x)(τᵢ)`), for a bi-Lipschitz `C¹` map `φ` with injective derivative and `φ⁻¹(U) = U`: for
`Hⁿ`-a.e. `x ∈ M`, `M` has the approximate tangent space `Q(x) = approxTangentPlane n M x` at `x`
and `φ(M)` has the approximate tangent space `Dφ(x)(Q(x))` at `φ(x)`.  `M` is, up to an
`Hⁿ`-null set, the union of bi-Lipschitz pieces `Fᵢ(Bᵢ)`; for a.e. `b ∈ Bᵢ`,
`T_{Fᵢ(b)}M = range DFᵢ(b)` and `T_{φ(Fᵢ(b))}φ(M) = range D(φ ∘ Fᵢ)(b) = Dφ(Fᵢ(b))(range DFᵢ(b))`,
and Lipschitz images of null parameter sets are `Hⁿ`-null. -/
theorem Submission.dpf_approxTangent_bilipschitz_image_ae : ∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable n M → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → ContDiff ℝ 1 φ → (∀ x, Injective (fderiv ℝ φ x)) → LipschitzWith Λ φ → AntilipschitzWith Λ φ → φ ⁻¹' U = U → ∀ᵐ x ∂(μHE[n].restrict M), HasApproximateTangentSpaceAt n M x (approxTangentPlane n M x) ∧ HasApproximateTangentSpaceAt n (φ '' M) (φ x) (Submodule.map (fderiv ℝ φ x : Euclid P →ₗ[ℝ] Euclid P) (approxTangentPlane n M x)) := by
  intro P n U M φ Λ hU hM hMU hrect hloc hφ hφinj hlip hanti hpre
  -- Step 1: bi-Lipschitz pieces `Fᵢ(Bᵢ) ⊆ M` covering `M` up to an `Hⁿ`-null set
  obtain ⟨F, B, m, hFlip, hBmeas, hmpos, hFlow, hFdiff, -, hFM, -, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P n M hM hrect
  -- Step 3: `φ(M)` is Borel, contained in `U` and locally `Hⁿ`-finite in `U`
  obtain ⟨hφMmeas, hφMU, hφMloc⟩ :=
    Submission.dpf_itt_bilipschitz_image_locfin P n U M φ Λ Λ hM hMU hloc hlip hanti hpre
  -- Step 6: it suffices to prove the conclusion at `Fᵢ(b)` for a.e. `b ∈ Bᵢ`
  refine Submission.dpf_itt_ae_of_ae_pieces P n M F B _ hM hFlip hnull fun i => ?_
  obtain ⟨L, hL⟩ := hFlip i
  -- Step 4: `φ ∘ Fᵢ` is bi-Lipschitz on `Bᵢ`, with injective derivative of range
  -- `Dφ(Fᵢ(b))(range DFᵢ(b))`
  obtain ⟨hφFlip, ⟨m', hm'pos, hφFlow⟩, hφFdiff, hrange⟩ :=
    Submission.dpf_itt_comp_bilipschitz_piece P n (F i) φ (B i) L Λ Λ (m i) hL (hmpos i)
      (hFlow i) (hFdiff i) (hφ.differentiable one_ne_zero) hφinj hlip hanti
  -- Step 2: `T_{Fᵢ(b)}M = range DFᵢ(b)` for a.e. `b ∈ Bᵢ`
  have hM_ae := Submission.dpf_approxTangent_ae_bilipschitz_piece P n U M (F i) (B i) L (m i) hU
    hM hMU hloc hL (hBmeas i) (hmpos i) (hFlow i) (hFdiff i) (hFM i)
  -- Step 4: `T_{φ(Fᵢ(b))}φ(M) = range D(φ ∘ Fᵢ)(b)` for a.e. `b ∈ Bᵢ`
  have hφM_ae := Submission.dpf_approxTangent_ae_bilipschitz_piece P n U (φ '' M) (φ ∘ F i)
    (B i) (Λ * L) m' hU hφMmeas hφMU hφMloc hφFlip (hBmeas i) hm'pos hφFlow hφFdiff
    (by rw [image_comp]; exact image_mono (hFM i))
  -- Step 5: combine, using `Q(Fᵢ(b)) = range DFᵢ(b)` (uniqueness of approximate tangent planes)
  filter_upwards [hM_ae, hφM_ae, ae_restrict_mem (hBmeas i)] with b hb hφb hbB
  rw [Submission.dpf_itt_approxTangentPlane_eq P n M (F i b) _ hb, ← hrange b hbB]
  exact ⟨hb, hφb⟩
/-- **Simon Ch. 3, 2.3–2.6 (area formula, 2.6)** for an injective Lipschitz `C¹` map `φ` on a
countably `n`-rectifiable `M`, with the tangential Jacobian
`J(x) = (det(Dφ(x)eₐ · Dφ(x)e_b))^{1/2}`, `e` the standard orthonormal basis of `TₓM`:
`∫_{φ(M)} g dHⁿ = ∫_M J (g ∘ φ) dHⁿ` for every `g ≥ 0`.  Decompose `M` into disjoint bi-Lipschitz
pieces `Pᵢ = Fᵢ(Bᵢ)` up to an `Hⁿ`-null set.  For a.e. `b ∈ Bᵢ`, `T_{Fᵢ b}M = range DFᵢ(b)`
(density lemma and uniqueness of approximate tangent planes).  Both sides split along the pieces
(for `φ`, and for `id`), and on each piece the per-piece area identity applies. -/
theorem Submission.dpf_area_formula_bilipschitz_rectifiable : ∀ (P n : ℕ) (U M : Set (Euclid P)) (φ : Euclid P → Euclid P) (Λ : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable n M → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (M ∩ C) ≠ ∞) → ContDiff ℝ 1 φ → LipschitzWith Λ φ → Injective φ → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in φ '' M, g y ∂μHE[n] = ∫⁻ x in M, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane n M x)) => inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) i)) (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n M x) j))))) * g (φ x) ∂μHE[n] := by
  intro P n U M φ Λ hU hM hMU hrect hloc hφ1 hφ hφinj g
  -- Step 1: disjoint bi-Lipschitz pieces `Fᵢ(Bᵢ) ⊆ M`, covering `M` up to an `Hⁿ`-null set
  obtain ⟨F, B, m, hF, hB, hm, hlow, hdiff, hFBm, hFB, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P n M hM hrect
  -- `Fᵢ` is injective on `Bᵢ`: `mᵢ‖a - a'‖ ≤ ‖Fᵢ a - Fᵢ a'‖` with `mᵢ > 0`
  have hinj : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have h1 := hlow i a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    exact sub_eq_zero.mp (norm_le_zero_iff.mp (nonpos_of_mul_nonpos_right h1 (hm i)))
  -- Step 2: `T_{Fᵢ b}M = range DFᵢ(b)` for a.e. `b ∈ Bᵢ`
  have htan : ∀ i, ∀ᵐ b ∂(volume.restrict (B i)), approxTangentPlane n M (F i b) =
      LinearMap.range (fderiv ℝ (F i) b : Euclid n →ₗ[ℝ] Euclid P) := by
    intro i
    obtain ⟨L, hL⟩ := hF i
    filter_upwards [Submission.dpf_approxTangent_ae_bilipschitz_piece P n U M (F i) (B i) L (m i)
      hU hM hMU hloc hL (hB i) (hm i) (hlow i) (hdiff i) (hFB i)] with b hb
    have hex : ∃ Q, HasApproximateTangentSpaceAt n M (F i b) Q := ⟨_, hb⟩
    rw [approxTangentPlane, dite_eq_left hex]
    exact hex.choose_spec.unique hb
  -- Step 3: split both sides along the pieces (`φ`, resp. `id`, is Lipschitz and injective)
  have hsplit : ∀ w : Euclid P → ℝ≥0∞,
      ∫⁻ x in M, w x ∂μHE[n] = ∑' i, ∫⁻ x in F i '' B i, w x ∂μHE[n] := fun w => by
    simpa only [image_id] using Submission.dpf_raf_lintegral_image_eq_tsum_pieces P n M
      (fun i => F i '' B i) id 1 hFBm hFB hdisj hnull LipschitzWith.id injective_id w
  rw [Submission.dpf_raf_lintegral_image_eq_tsum_pieces P n M (fun i => F i '' B i) φ Λ hFBm hFB
    hdisj hnull hφ hφinj g, hsplit]
  -- Step 4: the area identity on each piece, with `Q = approxTangentPlane n M`
  refine tsum_congr fun i => ?_
  obtain ⟨L, hL⟩ := hF i
  exact Submission.dpf_raf_piece_area_formula_gram P n (approxTangentPlane n M) φ Λ (F i) L (B i)
    (hφ1.differentiable one_ne_zero) hφ hL (hB i) (hinj i) hφinj.injOn (htan i) g
/-- **Gram determinant = determinant of the compression** (Simon Ch. 3, (2.3)).  If `e` is an
orthonormal basis of a subspace `V ⊆ ℝᴾ`, `p = p_V` and `A : ℝᴾ → ℝᴾ` is linear, then
`det(⟨A eᵢ, A eⱼ⟩) = det(p A* A p + (I − p))`.  `T := p A* A p + (I − p)` maps `V` into `V` and
induces the identity on `ℝᴾ/V` (`T x − x = p A* A p x − p x ∈ V`), so `det T = det(T|_V)`
(`LinearMap.det_eq_det_mul_det`); the matrix of `T|_V` in `e` has entries
`⟨eᵢ, p A* A eⱼ⟩ = ⟨p eᵢ, A* A eⱼ⟩ = ⟨A eᵢ, A eⱼ⟩`, i.e. it is the Gram matrix. -/
theorem Submission.dpf_jm_gram_det_eq_det_compression : ∀ (P : ℕ) (V : Submodule ℝ (Euclid P)) {ι : Type} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V) (A : Euclid P →L[ℝ] Euclid P), Matrix.det (Matrix.of fun i j : ι => inner ℝ (A (e i)) (A (e j))) = (V.starProjection ∘L (A.adjoint ∘L A) ∘L V.starProjection + (ContinuousLinearMap.id ℝ (Euclid P) - V.starProjection)).det := by
  intro P V ι _ _ e A
  set p := V.starProjection with hp_def
  set T : Euclid P →L[ℝ] Euclid P :=
    p ∘L (A.adjoint ∘L A) ∘L p + (ContinuousLinearMap.id ℝ (Euclid P) - p) with hT_def
  -- `V` is `T`-invariant: `T v = p (A* A v)` for `v ∈ V`
  have hT : V ≤ V.comap (T : Euclid P →ₗ[ℝ] Euclid P) := by
    intro v hv
    have hpv : p v = v := Submodule.starProjection_eq_self_iff.mpr hv
    simp only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hT_def,
      add_apply, ContinuousLinearMap.comp_apply,
      sub_apply, ContinuousLinearMap.id_apply, hpv, sub_self, add_zero]
    exact V.starProjection_apply_mem _
  -- `T` induces the identity on `ℝᴾ/V`: `T x - x = p (A* A p x) - p x ∈ V`
  have hQ : V.mapQ V (T : Euclid P →ₗ[ℝ] Euclid P) hT = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.mapQ_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    have : (T : Euclid P →ₗ[ℝ] Euclid P) x - x = p ((A.adjoint ∘L A) (p x)) - p x := by
      simp only [ContinuousLinearMap.coe_coe, hT_def, add_apply,
        ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply]
      abel
    rw [this]
    exact V.sub_mem (V.starProjection_apply_mem _) (V.starProjection_apply_mem _)
  -- block-triangular determinant: `det T = det (T|_V) * det id`
  have hsplit := LinearMap.det_eq_det_mul_det V (T : Euclid P →ₗ[ℝ] Euclid P) hT
  rw [hQ, LinearMap.det_id, mul_one] at hsplit
  rw [ContinuousLinearMap.det, hsplit, ← LinearMap.det_toMatrix e.toBasis]
  -- the matrix of `T|_V` in `e` is the Gram matrix
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
  have hpj : p (e j) = e j := Submodule.starProjection_eq_self_iff.mpr (e j).2
  have hpi : p (e i) = e i := Submodule.starProjection_eq_self_iff.mpr (e i).2
  rw [Submodule.coe_inner, LinearMap.coe_restrict_apply]
  simp only [ContinuousLinearMap.coe_coe, hT_def, add_apply,
    ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.id_apply, hpj, sub_self, add_zero]
  rw [← Submodule.inner_starProjection_left_eq_right, hpi,
    ContinuousLinearMap.adjoint_inner_right]
/-- **A.e. strong measurability of `√det(p L* L p + I − p)`** (Simon Ch. 3, 2.3–2.4: `J^M_f` is
`Hⁿ`-measurable; used for the Jacobian in 7.1.2).  If `p, L : ℝᴾ → End(ℝᴾ)` are `μ`-a.e. strongly
measurable, then so is `x ↦ √det(p(x) ∘ L(x)* ∘ L(x) ∘ p(x) + (I − p(x)))`.  It is `Φ(p(x), L(x))`
for `Φ(q, B) = √det(q ∘ (B* ∘ B) ∘ q + (I − q))` on `End(ℝᴾ) × End(ℝᴾ)`, which is continuous
(the adjoint, composition, `det` in finite dimension and `√` are continuous), and a continuous
function of the a.e. strongly measurable pair `(p, L)` is a.e. strongly measurable. -/
theorem Submission.dpf_jm_aestronglyMeasurable_sqrt_det_compression : ∀ (P : ℕ) (μ : Measure (Euclid P)) (p L : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable p μ → AEStronglyMeasurable L μ → AEStronglyMeasurable (fun x => Real.sqrt ((p x ∘L ((L x).adjoint ∘L L x) ∘L p x + (ContinuousLinearMap.id ℝ (Euclid P) - p x)).det)) μ := by
  intro P μ p L hp hL
  -- `B ↦ B*` is a linear isometric equivalence of `End(ℝᴾ)`, hence continuous
  have hadj : Continuous fun q : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
      (q.2).adjoint :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid P) (F := Euclid P)).continuous.comp
      continuous_snd
  -- `Φ(q, B) = √det(q ∘ (B* ∘ B) ∘ q + (I − q))` is continuous on `End(ℝᴾ) × End(ℝᴾ)`
  have hΦ : Continuous fun q : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
      Real.sqrt ((q.1 ∘L ((q.2).adjoint ∘L q.2) ∘L q.1 +
        (ContinuousLinearMap.id ℝ (Euclid P) - q.1)).det) := by
    refine Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp ?_)
    refine Continuous.add ?_ (continuous_const.sub continuous_fst)
    exact continuous_fst.clm_comp ((hadj.clm_comp continuous_snd).clm_comp continuous_fst)
  -- compose with the a.e. strongly measurable pair `x ↦ (p x, L x)`
  have h := hΦ.comp_aestronglyMeasurable (hp.prodMk hL)
  exact h

/-- **The tangential Jacobian is a.e. strongly measurable** (Simon Ch. 3, 2.3 and the remark
"Thus `J^M_f` is `Hⁿ`-measurable", chapter-03.txt lines 362–385; step 7 of the push-forward
proof, Simon 6.2.23–2.24).  If `x ↦ p_{Q(x)}` (orthogonal projection onto `Q(x)`) and `x ↦ L(x)`
are `μ`-a.e. strongly measurable, so is `x ↦ (det(L(x)eₐ · L(x)e_b))^{1/2}`, `e` the standard
orthonormal basis of `Q(x)`: the Gram determinant is `det(p L(x)* L(x) p + I − p)`,
`p = p_{Q(x)}`, a continuous function of the pair `(p_{Q(x)}, L(x))`. -/
theorem Submission.dpf_aestronglyMeasurable_gramJacobian : ∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)) (L : Euclid P → (Euclid P →L[ℝ] Euclid P)), AEStronglyMeasurable (fun x => (Q x).starProjection) μ → AEStronglyMeasurable L μ → AEStronglyMeasurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (Q x)) => inner ℝ (L x (stdOrthonormalBasis ℝ (Q x) i)) (L x (stdOrthonormalBasis ℝ (Q x) j))))) μ := by
  intro P μ Q L hp hL
  -- for each `x`, `det(L(x)eₐ · L(x)e_b) = det(p L(x)* L(x) p + I − p)` with `p = p_{Q(x)}`
  simp_rw [Submission.dpf_jm_gram_det_eq_det_compression P (Q _) (stdOrthonormalBasis ℝ (Q _))
    (L _)]
  -- `(q, B) ↦ √det(q B* B q + I − q)` is continuous and `x ↦ (p_{Q(x)}, L(x))` is a.e. strongly
  -- measurable
  exact Submission.dpf_jm_aestronglyMeasurable_sqrt_det_compression P μ
    (fun x => (Q x).starProjection) L hp hL
/-- Basis independence of the Gram determinant `det(Dᵢf · Dⱼf)` of the Jacobian (Simon Ch. 6,
3.4–3.7; push-forward of an orientation in 7.1.2): if the orthonormal `n`-frame `τ` spans `Q`, then
`det(⟨L eᵢ, L eⱼ⟩) = det(⟨L τₐ, L τ_b⟩)` for `e = stdOrthonormalBasis ℝ Q`.  With
`L' = L ∘ ι_Q` and `T = L'^* L'`, the matrix of `T` in any orthonormal basis `b` of `Q` is the
Gram matrix `(⟨L bᵢ, L bⱼ⟩)`, so both determinants equal `det T`. -/
theorem Submission.dpf_det_gram_stdOrthonormalBasis_eq : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (L (τ i)) (L (τ j))) := by
  intro P n Q L τ hτ hQ
  -- `L' = L ∘ ι_Q : Q → ℝᴾ` and the endomorphism `T = L'^* L'` of `Q`
  let L' : Q →ₗ[ℝ] Euclid P := (L : Euclid P →ₗ[ℝ] Euclid P) ∘ₗ Q.subtype
  let T : Q →ₗ[ℝ] Q := LinearMap.adjoint L' ∘ₗ L'
  -- in an orthonormal basis `b` of `Q`, the matrix of `T` is the Gram matrix `(⟨L bᵢ, L bⱼ⟩)`
  have key : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (b : OrthonormalBasis ι ℝ Q),
      Matrix.det (Matrix.of fun i j : ι => inner ℝ (L (b i : Euclid P)) (L (b j : Euclid P))) =
        LinearMap.det T := by
    intro ι _ _ b
    rw [← LinearMap.det_toMatrix b.toBasis T]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
    simp only [T, LinearMap.comp_apply, LinearMap.adjoint_inner_right, Matrix.of_apply]
    rfl
  -- `τ`, regarded in `Q`, is an orthonormal basis of `Q`
  have hmem : ∀ a, τ a ∈ Q := fun a => hQ ▸ Submodule.subset_span (Set.mem_range_self a)
  let τ' : Fin n → Q := fun a => ⟨τ a, hmem a⟩
  have hτ' : Orthonormal ℝ τ' := by
    rw [orthonormal_iff_ite] at hτ ⊢
    exact hτ
  have hspan' : ⊤ ≤ Submodule.span ℝ (Set.range τ') := by
    have hmap : Submodule.map Q.subtype (Submodule.span ℝ (Set.range τ')) =
        Submodule.map Q.subtype ⊤ := by
      rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
      exact hQ
    rw [Submodule.map_injective_of_injective Q.injective_subtype hmap]
  have h2 := key (OrthonormalBasis.mk hτ' hspan')
  simp only [OrthonormalBasis.coe_mk] at h2
  exact (key (stdOrthonormalBasis ℝ Q)).trans h2.symm
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
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
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

/-- Orientation of the push-forward by an injective linear map (Simon Ch. 6, 3.4–3.5 and 3.7:
`L_#ξ = J η`): if `ξ` is a unit orientation of `Q`, `ζ(β) = ξ(β ∘ L)` and
`J = (det(Leₐ · Le_b))^{1/2}` for the orthonormal basis `e` of `Q`, then `0 < J ≤ ‖L‖ⁿ` and `J⁻¹ζ`
is a unit orientation of `L(Q)`.  With `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` and `σ` an orthonormal frame of
`span (Lτ) = L(Q)`, `β(Lτ) = det A · β(σ)` for `A = (⟨σᵢ, Lτⱼ⟩)`, and `J = |det A|`. -/
theorem Submission.dpf_unitOrientation_map_gramNormalized : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n) (L : Euclid P →L[ℝ] Euclid P) (J : ℝ), IsUnitOrientationOf ξ Q → Injective L → J = Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ Q) => inner ℝ (L (stdOrthonormalBasis ℝ Q i)) (L (stdOrthonormalBasis ℝ Q j)))) → 0 < J ∧ J ≤ ‖L‖ ^ n ∧ IsUnitOrientationOf (J⁻¹ • ξ.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM L)) (Submodule.map (L : Euclid P →ₗ[ℝ] Euclid P) Q) := by
  intro P n Q ξ L J hξ hL hJ
  -- `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `Q`
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  -- `Lτ` is linearly independent; let `σ` be an orthonormal frame of `span (Lτ)` (Gram–Schmidt)
  have hv : LinearIndependent ℝ fun i => L (τ i) :=
    hτ.linearIndependent.map' (L : Euclid P →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.mpr hL)
  obtain ⟨σ, hσ, hσv, hdet, hA0, hAle⟩ :=
    Submission.dpf_exists_orthonormal_frame_det_gram P n (fun i => L (τ i)) hv
  -- `α(Lτ) = det A · α(σ)` for every `n`-covector `α`, where `A = (⟨σᵢ, Lτⱼ⟩)`: the restriction
  -- of `α` to `span σ` is `α(σ) det_σ`, and the coordinates of `Lτⱼ` in the basis `σ` are `Aᵢⱼ`
  have hcov : ∀ α : Covector (Euclid P) n, α (fun j => L (τ j)) =
      (Matrix.of fun i j => inner ℝ (σ i) (L (τ j))).det * α σ := by
    intro α
    set S := Submodule.span ℝ (Set.range σ)
    have hvS : ∀ j, L (τ j) ∈ S := fun j => by
      rw [hσv]
      exact Submodule.subset_span (Set.mem_range_self j)
    let e : Module.Basis (Fin n) ℝ S := Module.Basis.span hσ.linearIndependent
    have he : ∀ i, (e i : Euclid P) = σ i := fun i => by
      rw [Module.Basis.span_apply hσ.linearIndependent i]
    let αS : S [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap S.subtype
    let w : Fin n → S := fun j => ⟨L (τ j), hvS j⟩
    have h1 : α (fun j => L (τ j)) = αS w := rfl
    have h2 : α σ = αS e := by
      show α σ = α (fun i => (e i : Euclid P))
      congr 1
      funext i
      exact (he i).symm
    have hrepr : ∀ i j, e.repr (w j) i = inner ℝ (σ i) (L (τ j)) := by
      intro i j
      have hs : L (τ j) = ∑ l, e.repr (w j) l • σ l := by
        have := congrArg Subtype.val (e.sum_repr (w j))
        simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
        exact this.symm
      rw [hs, hσ.inner_right_fintype]
    have hmat : e.toMatrix w = Matrix.of fun i j => inner ℝ (σ i) (L (τ j)) := by
      ext i j
      rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
    have h3 : αS w = αS e * e.det w := by
      conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αS]
      rfl
    rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
  generalize (Matrix.of fun i j => inner ℝ (σ i) (L (τ j))).det = d at hdet hA0 hAle hcov
  -- `J = √(det G(Le)) = √(det G(Lτ)) = √((det A)²) = |det A|`
  have hJd : J = |d| := by
    rw [hJ, Submission.dpf_det_gram_stdOrthonormalBasis_eq P n Q L τ hτ hτQ, hdet,
      Real.sqrt_sq_eq_abs]
  refine ⟨by rw [hJd]; exact abs_pos.mpr hA0, ?_, σ, hσ, ?_, ?_⟩
  · -- `J = |det A| ≤ ∏ᵢ ‖Lτᵢ‖ ≤ ‖L‖ⁿ`
    rw [hJd]
    refine hAle.trans ?_
    calc ∏ i, ‖L (τ i)‖ ≤ ∏ _i : Fin n, ‖L‖ :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => by
            simpa [hτ.1 i] using L.le_opNorm (τ i)
      _ = ‖L‖ ^ n := by simp
  · -- `span σ = span (Lτ) = L(span τ) = L(Q)`
    rw [hσv, ← hτQ, Submodule.map_span, ← Set.range_comp]
    rfl
  · -- `(J⁻¹ζ)(α) = J⁻¹ ξ(α ∘ L) = ±J⁻¹ α(Lτ) = ±(J⁻¹ det A) α(σ)` with `J⁻¹ det A = ±1`
    have hζ : ∀ α : Covector (Euclid P) n,
        (J⁻¹ • ξ.comp (ContinuousAlternatingMap.compContinuousLinearMapCLM L)) α =
          J⁻¹ * ξ (α.compContinuousLinearMap L) := fun α => rfl
    have hατ : ∀ α : Covector (Euclid P) n, α.compContinuousLinearMap L τ = d * α σ :=
      fun α => hcov α
    have hsign : J⁻¹ * d = 1 ∨ J⁻¹ * d = -1 := by
      rw [hJd]
      rcases hA0.lt_or_gt with h | h
      · exact Or.inr (by rw [abs_of_neg h, inv_neg, neg_mul, inv_mul_cancel₀ hA0])
      · exact Or.inl (by rw [abs_of_pos h, inv_mul_cancel₀ hA0])
    rcases hξτ with hξτ | hξτ <;> rcases hsign with hs | hs
    · exact Or.inl fun α => by rw [hζ, hξτ, hατ]; linear_combination α σ * hs
    · exact Or.inr fun α => by rw [hζ, hξτ, hατ]; linear_combination α σ * hs
    · exact Or.inr fun α => by rw [hζ, hξτ, hατ]; linear_combination -α σ * hs
    · exact Or.inl fun α => by rw [hζ, hξτ, hατ]; linear_combination -α σ * hs

/-- Simon 6.3.6–3.9 and 6.2.24(3) for a `C¹` bi-Lipschitz bijection `φ` with `φ⁻¹(U) = U`
(step 9 of the push-forward proof): `ω ↦ ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ⟩ dHⁿ` is the action of the
integer multiplicity triple `R' = (φ(M), θ ∘ φ⁻¹, η ∘ φ⁻¹)`, where `η = J⁻¹ ξ(· ∘ Dφ)` and `J` is
the Gram Jacobian of `Dφ` on `TₓM`.  A.e. on `M`, `0 < J` and `η(x)` orients
`Dφ(x)TₓM = T_{φ(x)}φ(M)`; the area formula then transfers the action from `φ(M)` to `M`. -/
theorem Submission.dpf_imrep_bilipschitz_image_rep : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (φ : Euclid P → Euclid P) (Λ : NNReal), IsOpen U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → LipschitzWith Λ φ → AntilipschitzWith Λ φ → φ ⁻¹' U = U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) → ∃ R' : IMRep U n, ∀ ω : TestFormOn U n, R'.action (ω : DifferentialForm (Euclid P) n) = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] := by
  intro P n U R φ Λ hU hφ hbij hinj hlip hanti hpre hproj
  -- Step 2: `θ ≥ 1` on `M`, so `M` has locally finite `Hⁿ`-measure in `U`
  have hfin : ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → μHE[n] (R.carrier ∩ C) ≠ ∞ := by
    intro C hC hCU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult C hC hCU) ?_
    calc μHE[n] (R.carrier ∩ C) = ∫⁻ _ in R.carrier ∩ C, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
        setLIntegral_mono' (R.measurableSet_carrier.inter hC.isClosed.measurableSet)
          fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1)
  have hφc : Continuous φ := hφ.continuous
  have hDφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  -- Step 3 (I): the Gram Jacobian `J` of `Dφ` on `TₓM` is a.e. strongly measurable
  obtain ⟨J, hJ⟩ : ∃ J : Euclid P → ℝ, J = fun x => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin (Module.finrank ℝ (approxTangentPlane n R.carrier x)) => inner ℝ (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n R.carrier x) i)) (fderiv ℝ φ x (stdOrthonormalBasis ℝ (approxTangentPlane n R.carrier x) j)))) :=
    ⟨_, rfl⟩
  have hJm : AEStronglyMeasurable J (μHE[n].restrict R.carrier) := by
    rw [hJ]
    exact Submission.dpf_aestronglyMeasurable_gramJacobian P (μHE[n].restrict R.carrier)
      (approxTangentPlane n R.carrier) (fderiv ℝ φ) hproj hDφ.aestronglyMeasurable
  -- Step 4: the orientation `η = J⁻¹ ζ`, `ζ(x)(β) = ξ(x)(β ∘ Dφ(x))`, in source coordinates
  set η : Euclid P → MultiVector P n := fun x => (J x)⁻¹ •
    (R.orient x).comp (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ φ x))
  have hηm : AEStronglyMeasurable η (μHE[n].restrict R.carrier) := by
    have hζ : AEStronglyMeasurable (fun x => (R.orient x).comp
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv ℝ φ x)))
        (μHE[n].restrict R.carrier) :=
      (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk
          (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp_aestronglyMeasurable
            hDφ.aestronglyMeasurable))
    exact hJm.aemeasurable.inv.aestronglyMeasurable.smul hζ
  -- Step 3: a.e. on `M`, `0 < J` and `η` orients `Dφ(x)TₓM`, the approximate tangent plane of
  -- `φ(M)` at `φ(x)` (`ξ(x)` orients `TₓM` by uniqueness of approximate tangent planes)
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier), 0 < J x ∧ ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n (φ '' R.carrier) (φ x) Q ∧ IsUnitOrientationOf (η x) Q := by
    filter_upwards [Submission.dpf_approxTangent_bilipschitz_image_ae P n U R.carrier φ Λ hU
      R.measurableSet_carrier R.carrier_subset R.rectifiable hfin hφ hinj hlip hanti hpre,
      R.orients] with x hx hξ
    obtain ⟨Q, hQ, hξQ⟩ := hξ
    rw [hQ.unique hx.1] at hξQ
    obtain ⟨hJpos, -, hηQ⟩ := Submission.dpf_unitOrientation_map_gramNormalized P n
      (approxTangentPlane n R.carrier x) (R.orient x) (fderiv ℝ φ x) (J x) hξQ (hinj x)
      (by rw [hJ])
    exact ⟨hJpos, _, hx.2, hηQ⟩
  -- Step 5: `R' = (φ(M), θ ∘ φ⁻¹, η ∘ φ⁻¹)` is an integer multiplicity triple in `U`
  obtain ⟨R', hR'c, hR'⟩ := Submission.dpfir_bilipschitz_image_imrep_exists P n U R φ Λ η hbij
    hlip hanti hpre hηm (hgood.mono fun x hx => hx.2)
  refine ⟨R', fun ω => ?_⟩
  obtain ⟨w, ⟨hws, hwc⟩, hwU⟩ := ω
  show R'.action w = ∫ x in R.carrier,
    (R.mult x : ℝ) * R.orient x ((w (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n]
  have hwcont : Continuous w := ContDiff.continuous hws
  -- Step 6(b): `β(x) = ω(φ(x)) ∘ Dφ(x)` is continuous with compact support `⊆ φ⁻¹(spt ω) ⊆ U`
  set β : Euclid P → Covector (Euclid P) n :=
    fun x => (w (φ x)).compContinuousLinearMap (fderiv ℝ φ x) with hβ
  have hβc : Continuous β :=
    (ContinuousAlternatingMap.continuous_compContinuousLinearMapCLM.comp hDφ).clm_apply
      (hwcont.comp hφc)
  have hβsupp : tsupport β ⊆ φ ⁻¹' tsupport w := by
    refine closure_minimal (fun x hx => subset_tsupport w fun h0 => hx ?_)
      ((isClosed_tsupport w).preimage hφc)
    ext v
    simp [hβ, h0]
  have hβcs : HasCompactSupport β :=
    (Metric.isCompact_of_isClosed_isBounded ((isClosed_tsupport w).preimage hφc)
      (hanti.isBounded_preimage hwc.isCompact.isBounded)).of_isClosed_subset
      (isClosed_tsupport β) hβsupp
  have hβU : tsupport β ⊆ U := hβsupp.trans ((preimage_mono hwU).trans hpre.subset)
  -- Step 6(a): `J(x) h(φ(x)) = g_ω(x)` a.e. on `M`, where `h = θ'⟨ω, ξ'⟩` and `g_ω = θ⟨β, ξ⟩`
  have hJh : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      J x * ((R'.mult (φ x) : ℝ) * R'.orient (φ x) (w (φ x))) =
        (R.mult x : ℝ) * R.orient x (β x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hmult, horient⟩ := hR' x
    have hηx : η x (w (φ x)) = (J x)⁻¹ * R.orient x (β x) := rfl
    rw [hmult, horient, hηx, mul_left_comm, mul_inv_cancel_left₀ hx.1.ne']
  -- Step 6(c)–(d): the area formula on `φ(M)` transfers integrability and the integral
  have harea : ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y, g y ∂(μHE[n].restrict R'.carrier) =
      ∫⁻ x, ENNReal.ofReal (J x) * g (φ x) ∂(μHE[n].restrict R.carrier) := by
    intro g
    rw [hR'c, hJ]
    exact Submission.dpf_area_formula_bilipschitz_rectifiable P n U R.carrier φ Λ hU
      R.measurableSet_carrier R.carrier_subset R.rectifiable hfin hφ hlip hbij.1 g
  exact (Submission.dpfir_integral_eq_of_area_lintegral P (μHE[n].restrict R.carrier)
    (μHE[n].restrict R'.carrier) φ J (fun y => (R'.mult y : ℝ) * R'.orient y (w y))
    (fun x => (R.mult x : ℝ) * R.orient x (β x)) (fun x => by rw [hJ]; exact Real.sqrt_nonneg _)
    harea (Submission.dpfir_imrep_pairing_continuous_integrable P n U R' w hwcont hwc
      hwU).aestronglyMeasurable
    (Submission.dpfir_imrep_pairing_continuous_integrable P n U R β hβc hβcs hβU) hJh).2
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

/-- **Simon Ch. 6, Remark 3.2(3)** (mass of an integer multiplicity current).  If
`R = (M, θ, ξ)` represents `T ∈ 𝒟ₙ(U)`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ = (θ Hⁿ⌞M)(W)` for every
open `W ⊆ U`.  A.e. on `M`, `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal `τ` (Gram determinant `1`), so
`covectorEuclideanNorm_gram_bounds` gives `|⟨β, ξ⟩| ≤ |β|_E` for every `n`-covector `β` and
`⟨β, ξ⟩ = 1` for some `β` with `|β|_E ≤ 1`.  The first bound gives
`T(ω) ≤ (θ Hⁿ⌞M)(spt ω) ≤ (θ Hⁿ⌞M)(W)` for every admissible `ω`.  Conversely, fix a compact
`K ⊆ W` and `η ∈ (0, 1)`.  The covector space is finite-dimensional, so the unit ball has a dense
sequence `βⱼ`; with a strongly measurable version of `ξ`, the disjointed sets
`Aⱼ ⊆ {⟨βⱼ, ξ⟩ > 1 − η}` cover `M` a.e.  Finitely many `Aⱼ` cover `K` up to measure `η`, and
inner regularity gives disjoint compacts `Cⱼ ⊆ K ∩ Aⱼ` exhausting them up to `η`.  Smooth plateau
functions `χⱼ` on disjoint thickenings of the `Cⱼ` inside `W` give an admissible
`ω = Σ χⱼ βⱼ` with `ω = βⱼ` on `Cⱼ`, whose support exceeds `⋃ Cⱼ` by measure `< η`; hence
`T(ω) ≥ (1 − η)(μ(K) − 2η) − η`.  Letting `η → 0` and exhausting `W` by compacts gives
`(θ Hⁿ⌞M)(W) ≤ M_W(T)`. -/
theorem Submission.imrep_represents_massOn_eq_measure : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → IsOpen W → W ⊆ U → T.massOn W = R.measure W := by
  intro P n U W T R hU hR hW hWU
  classical
  have hCB := Submission.covectorEuclideanNorm_gram_bounds P n
  have hpt : ∀ x, (∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q ∧
      IsUnitOrientationOf (R.orient x) Q) →
      (∀ β : Covector (Euclid P) n, |R.orient x β| ≤ covectorEuclideanNorm β) ∧
      ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 := by
    rintro x ⟨Q, -, τ, hτ, -, hsign⟩
    have hG : Matrix.det (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      have hI : (Matrix.of fun i j => inner ℝ (τ i) (τ j) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        ext i j
        rw [Matrix.of_apply, Matrix.one_apply]
        exact (orthonormal_iff_ite.mp hτ) i j
      rw [hI, Matrix.det_one]
    obtain ⟨α, hα1, hατ⟩ := hCB.2 τ hτ
    rcases hsign with h | h
    · refine ⟨fun β => ?_, α, hα1, by rw [h, hατ]⟩
      rw [h]
      simpa [hG] using hCB.1 β τ
    · refine ⟨fun β => ?_, -α, by rwa [covectorEuclideanNorm_neg], ?_⟩
      · rw [h, abs_neg]
        simpa [hG] using hCB.1 β τ
      · rw [h]
        simp [hατ]
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ x ∂R.measure, (∀ β : Covector (Euclid P) n,
      |R.orient x β| ≤ covectorEuclideanNorm β) ∧ ∃ β : Covector (Euclid P) n,
      covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 :=
    hac.ae_le (R.orients.mono fun x hx => hpt x hx)
  have hH1 : ∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) n,
      |R.orient x β| ≤ covectorEuclideanNorm β := hae.mono fun x hx => hx.1
  have hmeas : AEStronglyMeasurable R.orient R.measure := R.aestronglyMeasurable_orient.mono_ac hac
  have hrep : ∀ ω : TestFormOn U n,
      T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
    intro ω
    have hf : Measurable fun x => ((R.mult x : NNReal)) :=
      (measurable_of_countable (fun k : ℕ => (k : NNReal))).comp R.measurable_mult
    have key := integral_withDensity_eq_integral_smul (μ := μHE[n].restrict R.carrier) hf
      (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x))
    simp only [ENNReal.coe_natCast] at key
    rw [hR ω, IMRep.action, IMRep.measure, key]
    simp [NNReal.smul_def]
  have hH2 : ∀ᵐ x ∂R.measure, ∃ β : Covector (Euclid P) n,
      covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 := hae.mono fun x hx => hx.2
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ⊤ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, Set.inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Euclidean coefficient norm is absolutely homogeneous
  have hNsmul : ∀ (c : ℝ) (β : Covector (Euclid P) n),
      covectorEuclideanNorm (c • β) = |c| * covectorEuclideanNorm β := by
    intro c β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- the covector space is finite-dimensional (the coefficient map is injective)
  have hfd : FiniteDimensional ℝ (Covector (Euclid P) n) := by
    classical
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    let c : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
      { toFun := fun β f => β (fun i => e (f i))
        map_add' := fun β γ => by ext f; simp
        map_smul' := fun r β => by ext f; simp }
    refine FiniteDimensional.of_injective c ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext v
    have hv : v = fun i => ∑ k, (e.repr (v i) k) • e k := by
      funext i; exact (e.sum_repr (v i)).symm
    have key := β.toMultilinearMap.map_sum (fun i k => (e.repr (v i) k) • e k)
    have hsum : β v = ∑ r : Fin n → Fin P, β (fun i => (e.repr (v i) (r i)) • e (r i)) := by
      conv_lhs => rw [hv]
      exact key
    rw [hsum]
    change _ = (0 : ℝ)
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [β.map_smul_univ (fun i => e.repr (v i) (r i)) (fun i => e (r i))]
    have h0 : β (fun i => e (r i)) = 0 := congrFun hβ r
    rw [h0, smul_zero]
  -- smooth admissible plateau forms on finitely many disjoint compact pieces
  have hplat : ∀ (m : ℕ) (ν : Measure (Euclid P)) (W : Set (Euclid P)) (C : Fin m → Set (Euclid P))
      (b : Fin m → Covector (Euclid P) n) (δ : ℝ≥0∞), IsOpen W → ν W ≠ ⊤ →
      (∀ j, IsCompact (C j)) → (∀ j, C j ⊆ W) → (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ j, covectorEuclideanNorm (b j) ≤ 1) → δ ≠ 0 →
      ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ W ∧
        (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ (∀ j, ∀ x ∈ C j, ω x = b j) ∧
        ν (Function.support ω \ ⋃ j, C j) < δ := by
    intro m ν W C b δ hW hνW hC hCW hdisj hb hδ
    -- the per-piece error budget
    obtain ⟨d, hd0, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ δ := by
      rcases eq_or_ne δ ⊤ with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · exact ⟨δ.toReal, ENNReal.toReal_pos hδ h, by rw [ENNReal.ofReal_toReal h]⟩
    set η : ℝ≥0∞ := ENNReal.ofReal (d / (m + 1)) with hη
    have hηpos : η ≠ 0 := by
      rw [hη, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hmη : (m : ℝ≥0∞) * η < δ := by
      calc (m : ℝ≥0∞) * η = ENNReal.ofReal (m * (d / (m + 1))) := by
            rw [hη, ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
        _ < ENNReal.ofReal d := by
            rw [ENNReal.ofReal_lt_ofReal_iff hd0]
            calc (m : ℝ) * (d / (m + 1)) = d * (m / (m + 1)) := by ring
              _ < d * 1 := mul_lt_mul_of_pos_left
                  (by rw [div_lt_one (by positivity)]; linarith) hd0
              _ = d := mul_one d
        _ ≤ δ := hdδ
    -- choose a radius
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ (∀ j, cthickening r (C j) ⊆ W) ∧
        (∀ i j, i ≠ j → Disjoint (cthickening r (C i)) (cthickening r (C j))) ∧
        (∀ j, ν (cthickening r (C j)) < ν (C j) + η) := by
      refine (eventually_mem_nhdsWithin).and (Filter.eventually_all.2 fun j => ?_) |>.and
        (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_) |>.and
        (Filter.eventually_all.2 fun j => ?_) |>.mono fun r h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · obtain ⟨s, hs, hsW⟩ := (hC j).exists_cthickening_subset_open hW (hCW j)
        filter_upwards [Ioo_mem_nhdsGT hs] with r hr
        exact (cthickening_mono hr.2.le _).trans hsW
      · by_cases hij : i = j
        · exact Filter.Eventually.of_forall fun r h => (h hij).elim
        · obtain ⟨s, hs, hsd⟩ := (hdisj i j hij).exists_cthickenings (hC i) (hC j).isClosed
          filter_upwards [Ioo_mem_nhdsGT hs] with r hr _
          exact hsd.mono (cthickening_mono hr.2.le _) (cthickening_mono hr.2.le _)
      · obtain ⟨s, hs, hsW⟩ := (hC j).exists_cthickening_subset_open hW (hCW j)
        have hfin : ν (C j) ≠ ⊤ := ne_top_of_le_ne_top hνW (measure_mono (hCW j))
        have ht := tendsto_measure_cthickening_of_isClosed (μ := ν)
          ⟨s, hs, ne_top_of_le_ne_top hνW (measure_mono hsW)⟩ (hC j).isClosed
        exact (ht.mono_left nhdsWithin_le_nhds).eventually_lt_const (ENNReal.lt_add_right hfin hηpos)
    obtain ⟨r, hr0, hrW, hrd, hrν⟩ := hev.exists
    -- smooth plateau functions
    have hχ : ∀ j : Fin m, ∃ χ : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ range χ ⊆ Icc 0 1 ∧
        Function.support χ = thickening r (C j) ∧ ∀ x, x ∈ C j ↔ χ x = 1 := fun j =>
      exists_contDiff_support_eq_eq_one_iff isOpen_thickening (hC j).isClosed
        (self_subset_thickening hr0 _)
    choose χ hχs hχr hχsupp hχone using hχ
    -- membership in thickenings is exclusive
    have hexcl : ∀ i j x, x ∈ thickening r (C j) → i ≠ j → χ i x = 0 := by
      intro i j x hx hij
      rw [← Function.notMem_support, hχsupp]
      intro hxi
      exact Set.disjoint_left.mp (hrd i j hij) (thickening_subset_cthickening _ _ hxi)
        (thickening_subset_cthickening _ _ hx)
    set ω : DifferentialForm (Euclid P) n := fun x => ∑ j, χ j x • b j with hωdef
    have hsupp : Function.support ω ⊆ ⋃ j, cthickening r (C j) := by
      intro x hx
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have : χ j x ≠ 0 := fun h => hj (by simp [h])
      exact mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ (hχsupp j ▸ this)⟩
    have hFc : IsCompact (⋃ j, cthickening r (C j)) := isCompact_iUnion fun j => (hC j).cthickening
    have htsupp : tsupport ω ⊆ ⋃ j, cthickening r (C j) :=
      closure_minimal hsupp hFc.isClosed
    refine ⟨ω, ⟨?_, ?_⟩, htsupp.trans (iUnion_subset hrW), ?_, ?_, ?_⟩
    · exact ContDiff.sum fun j _ => (hχs j).smul contDiff_const
    · exact hFc.of_isClosed_subset (isClosed_tsupport _) htsupp
    · intro x
      by_cases hx : ∃ j, x ∈ thickening r (C j)
      · obtain ⟨j, hj⟩ := hx
        have : ω x = χ j x • b j := by
          rw [hωdef]
          exact Finset.sum_eq_single j (fun i _ hij => by rw [hexcl i j x hj hij, zero_smul])
            (by simp)
        rw [this, hNsmul]
        have h01 := hχr j (mem_range_self x)
        rw [abs_of_nonneg h01.1]
        calc χ j x * covectorEuclideanNorm (b j) ≤ 1 * 1 := mul_le_mul h01.2 (hb j) (covectorEuclideanNorm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · push Not at hx
        have : ω x = 0 := Finset.sum_eq_zero fun j _ => by
          rw [show χ j x = 0 from by rw [← Function.notMem_support, hχsupp]; exact hx j, zero_smul]
        rw [this, covectorEuclideanNorm_zero]; exact zero_le_one
    · intro j x hx
      have hxt : x ∈ thickening r (C j) := self_subset_thickening hr0 _ hx
      rw [hωdef]
      simp only
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hexcl i j x hxt hij, zero_smul]) (by simp),
        (hχone j x).1 hx, one_smul]
    · calc ν (Function.support ω \ ⋃ j, C j) ≤ ν (⋃ j, (cthickening r (C j) \ C j)) := by
            apply measure_mono
            intro x ⟨hx, hxC⟩
            obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
            have : χ j x ≠ 0 := fun h => hj (by simp [h])
            refine mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ (hχsupp j ▸ this), ?_⟩
            exact fun hxj => hxC (mem_iUnion.2 ⟨j, hxj⟩)
        _ ≤ ∑ j, ν (cthickening r (C j) \ C j) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _j : Fin m, η := by
            gcongr with j
            have hfin : ν (C j) ≠ ⊤ := ne_top_of_le_ne_top hνW (measure_mono (hCW j))
            exact (measure_sdiff_lt_of_lt_add (hC j).isClosed.measurableSet.nullMeasurableSet
              (self_subset_cthickening _) hfin (hrν j)).le
        _ = (m : ℝ≥0∞) * η := by simp
        _ < δ := hmη
  -- upper bound (supplied step 3)
  have hupper : T.massOn W ≤ R.measure W := by
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    show ENNReal.ofReal (T ω) ≤ R.measure W
    rw [hrep ω]
    set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hfdef
    have hfc : Continuous f := ω.2.1.1.continuous
    have hgm : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous.comp_aestronglyMeasurable
        (hmeas.prodMk hfc.aestronglyMeasurable)
    have hbd : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ₑ ≤ (tsupport f).indicator 1 x := by
      filter_upwards [hH1] with x hx
      by_cases hxs : x ∈ tsupport f
      · rw [Set.indicator_of_mem hxs, Pi.one_apply, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.mpr ((hx (f x)).trans (hω1 x))
      · rw [image_eq_zero_of_notMem_tsupport hxs]
        simp
    calc ENNReal.ofReal (∫ x, R.orient x (f x) ∂R.measure)
        ≤ ‖∫ x, R.orient x (f x) ∂R.measure‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖R.orient x (f x)‖ₑ ∂R.measure := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, (tsupport f).indicator 1 x ∂R.measure := lintegral_mono_ae hbd
      _ = R.measure (tsupport f) := lintegral_indicator_one (isClosed_tsupport _).measurableSet
      _ ≤ R.measure W := measure_mono hωW
  -- lower bound (supplied steps 4-7)
  have hlowerGen : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n),
      (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ⊤) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) n, |ξ x β| ≤ covectorEuclideanNorm β) →
      (∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1) →
      μ W ≤ T.massOn W := by
    intro μ ξ hrep hfin hmeas hH1 hH2
    set B : Set (Covector (Euclid P) n) := {β | covectorEuclideanNorm β ≤ 1} with hBdef
    have : Nonempty B := ⟨⟨0, by simp [hBdef]⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq B
    set ξ' := hmeas.mk ξ
    have hξ'm : StronglyMeasurable ξ' := hmeas.stronglyMeasurable_mk
    have hξξ' : ξ =ᵐ[μ] ξ' := hmeas.ae_eq_mk
    -- compact lower bound
    have hKbound : ∀ K, IsCompact K → K ⊆ W → μ K ≤ T.massOn W := by
      intro K hK hKW
      have hμK : μ K ≠ ⊤ := hfin K hK (hKW.trans hWU)
      have key : ∀ η : ℝ, 0 < η → η < 1 → ∃ ω : TestFormOn U n, ω ∈ massAdmissibleOn U n W ∧
          (1 - η) * (μ.real K - 2 * η) - η ≤ T ω := by
        intro η hη0 hη1
        set E : ℕ → Set (Euclid P) := fun j => {x | 1 - η < ξ' x (u j : Covector (Euclid P) n)}
          with hEdef
        have hEm : ∀ j, MeasurableSet (E j) := fun j =>
          measurableSet_lt measurable_const
            (StronglyMeasurable.apply_continuousLinearMap hξ'm (u j : Covector (Euclid P) n)).measurable
        have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ j, E j := by
          filter_upwards [hH2, hξξ'] with x ⟨β, hβ1, hβx⟩ hx
          have hopen : IsOpen {b : B | 1 - η < ξ x (b : Covector (Euclid P) n)} :=
            isOpen_lt continuous_const ((ξ x).continuous.comp continuous_subtype_val)
          obtain ⟨j, hj⟩ := hu.exists_mem_open hopen ⟨⟨β, hβ1⟩, by
            show 1 - η < ξ x β
            rw [hβx]; linarith⟩
          refine mem_iUnion.2 ⟨j, ?_⟩
          show 1 - η < ξ' x (u j : Covector (Euclid P) n)
          rw [← hx]; exact hj
        set A := disjointed E with hAdef
        have hAm : ∀ j, MeasurableSet (A j) := MeasurableSet.disjointed hEm
        have hAE : ∀ j, A j ⊆ E j := disjointed_subset E
        -- choose m
        obtain ⟨m, hm⟩ : ∃ m : ℕ, μ (K \ ⋃ j ∈ Finset.range m, A j) < ENNReal.ofReal η := by
          have hanti : Antitone fun m : ℕ => K \ ⋃ j ∈ Finset.range m, A j := by
            intro a b hab
            exact sdiff_subset_sdiff_right (biUnion_subset_biUnion_left
              (by simpa using Finset.range_subset_range.2 hab))
          have hlim := tendsto_measure_iInter_atTop (μ := μ)
            (fun m => (hK.isClosed.measurableSet.diff
              (Finset.measurableSet_biUnion _ fun j _ => hAm j)).nullMeasurableSet) hanti
            ⟨0, by simpa using hμK⟩
          have hnull : μ (⋃ j, E j)ᶜ = 0 :=
            measure_eq_zero_iff_ae_notMem.2 (hcov.mono fun x hx h => h hx)
          have hinter : μ (⋂ m : ℕ, K \ ⋃ j ∈ Finset.range m, A j) = 0 := by
            refine measure_mono_null ?_ hnull
            intro x hx
            rw [mem_iInter] at hx
            rw [← iUnion_disjointed, mem_compl_iff, mem_iUnion]
            rintro ⟨j, hj⟩
            exact (hx (j + 1)).2 (mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_self j), hj⟩)
          rw [hinter] at hlim
          exact (hlim.eventually (gt_mem_nhds (by simpa using hη0))).exists
        -- inner closed approximations inside K
        have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa [Measure.restrict_apply_univ] using hμK.lt_top⟩
        have hF : ∀ j : Fin m, ∃ F ⊆ K ∩ A j, IsClosed F ∧
            μ ((K ∩ A j) \ F) < ENNReal.ofReal (η / (m + 1)) := by
          intro j
          obtain ⟨F, hFsub, hFcl, hFμ⟩ := MeasurableSet.exists_isClosed_sdiff_lt (μ := μ.restrict K)
            (hK.isClosed.measurableSet.inter (hAm j)) (measure_ne_top _ _)
            (ε := ENNReal.ofReal (η / (m + 1))) (by
              rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
          refine ⟨F, hFsub, hFcl, ?_⟩
          rwa [Measure.restrict_apply' hK.isClosed.measurableSet,
            inter_eq_left.2 (sdiff_subset.trans inter_subset_left)] at hFμ
        choose F hFsub hFcl hFμ using hF
        have hFK : ∀ j, F j ⊆ K := fun j => (hFsub j).trans inter_subset_left
        have hFA : ∀ j, F j ⊆ A j := fun j => (hFsub j).trans inter_subset_right
        -- neighbourhood V of K
        obtain ⟨ρ, hρ, hρW⟩ := hK.exists_cthickening_subset_open hW hKW
        have hVμ : μ (thickening ρ K) ≠ ⊤ :=
          ne_top_of_le_ne_top (hfin _ hK.cthickening (hρW.trans hWU))
            (measure_mono (thickening_subset_cthickening _ _))
        have hVW : thickening ρ K ⊆ W := (thickening_subset_cthickening _ _).trans hρW
        obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀C, hω₀μ⟩ := hplat m μ (thickening ρ K) F
          (fun j => (u j : Covector (Euclid P) n)) (ENNReal.ofReal η) isOpen_thickening hVμ
          (fun j => hK.of_isClosed_subset (hFcl j) (hFK j))
          (fun j => (hFK j).trans (self_subset_thickening hρ _))
          (fun i j hij => (disjoint_disjointed E (Fin.val_injective.ne hij)).mono (hFA i) (hFA j))
          (fun j => (u j).2) (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hη0)
        let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVW.trans hWU)⟩
        refine ⟨ω, ⟨hω₀V.trans hVW, hω₀1⟩, ?_⟩
        rw [hrep ω]
        -- the integrand
        set g : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hgdef
        have hω₀c : Continuous ω₀ := hω₀t.1.continuous
        have hgm : AEStronglyMeasurable g μ :=
          (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous.comp_aestronglyMeasurable
            (hmeas.prodMk hω₀c.aestronglyMeasurable)
        have hg1 : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := by
          filter_upwards [hH1] with x hx
          rw [Real.norm_eq_abs]; exact (hx (ω₀ x)).trans (hω₀1 x)
        have hg0 : ∀ x, x ∉ Function.support ω₀ → g x = 0 := by
          intro x hx
          rw [Function.notMem_support] at hx
          simp [hgdef, hx]
        have hSV : Function.support ω₀ ⊆ thickening ρ K := (subset_tsupport _).trans hω₀V
        have hgi : Integrable g μ := by
          refine IntegrableOn.integrable_of_forall_notMem_eq_zero
            (Measure.integrableOn_of_bounded (s := thickening ρ K) hVμ hgm (M := 1) (ae_restrict_of_ae hg1)) ?_
          intro x hx; exact hg0 x (fun h => hx (hSV h))
        set C : Set (Euclid P) := ⋃ j, F j with hCdef
        have hCm : MeasurableSet C := MeasurableSet.iUnion fun j => (hFcl j).measurableSet
        have hCK : C ⊆ K := iUnion_subset hFK
        have hSm : MeasurableSet (Function.support ω₀) := hω₀c.isOpen_support.measurableSet
        -- lower bound on C
        have hC1 : (1 - η) * μ.real C ≤ ∫ x in C, g x ∂μ := by
          have hae : ∀ᵐ x ∂μ.restrict C, 1 - η ≤ g x := by
            rw [ae_restrict_iff' hCm]
            filter_upwards [hξξ'] with x hx hxC
            obtain ⟨j, hj⟩ := mem_iUnion.1 hxC
            have hxE : x ∈ E j := hAE j (hFA j hj)
            show 1 - η ≤ ξ x (ω₀ x)
            rw [hω₀C j x hj, hx]
            exact le_of_lt hxE
          calc (1 - η) * μ.real C = ∫ x in C, (1 - η) ∂μ := by
                rw [setIntegral_const, smul_eq_mul, mul_comm]
            _ ≤ ∫ x in C, g x ∂μ := by
                apply setIntegral_mono_ae_restrict _ hgi.integrableOn hae
                exact integrableOn_const (ne_top_of_le_ne_top hμK (measure_mono hCK))
        -- the rest
        have hrest : -(μ.real (Function.support ω₀ \ C)) ≤ ∫ x in Cᶜ, g x ∂μ := by
          rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hCm.compl
            (show Function.support ω₀ \ C ⊆ Cᶜ from fun x hx => hx.2)
            (fun x hx => hg0 x (fun h => hx.2 ⟨h, hx.1⟩))]
          have h := norm_setIntegral_le_of_norm_le_const_ae (f := g) (μ := μ)
            (s := Function.support ω₀ \ C) (C := 1)
            (lt_of_le_of_lt (measure_mono (sdiff_subset.trans hSV)) hVμ.lt_top)
            (ae_restrict_of_ae hg1)
          rw [Real.norm_eq_abs, one_mul] at h
          linarith [neg_abs_le (∫ x in Function.support ω₀ \ C, g x ∂μ)]
        have hsplit := integral_add_compl hCm hgi
        -- measure of C
        have hKC : μ.real K ≤ μ.real C + 2 * η := by
          have h1 : μ (K \ C) ≤ ENNReal.ofReal (2 * η) := by
            calc μ (K \ C) ≤ μ ((K \ ⋃ j ∈ Finset.range m, A j) ∪ ⋃ j : Fin m, ((K ∩ A j) \ F j)) := by
                  apply measure_mono
                  intro x ⟨hxK, hxC⟩
                  by_cases hx : x ∈ ⋃ j ∈ Finset.range m, A j
                  · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
                    refine Or.inr (mem_iUnion.2 ⟨⟨j, Finset.mem_range.1 hj⟩, ⟨hxK, hxj⟩, ?_⟩)
                    exact fun h => hxC (mem_iUnion.2 ⟨_, h⟩)
                  · exact Or.inl ⟨hxK, hx⟩
              _ ≤ μ (K \ ⋃ j ∈ Finset.range m, A j) + ∑ j : Fin m, μ ((K ∩ A j) \ F j) :=
                  (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
              _ ≤ ENNReal.ofReal η + ∑ _j : Fin m, ENNReal.ofReal (η / (m + 1)) :=
                  add_le_add hm.le (Finset.sum_le_sum fun j _ => (hFμ j).le)
              _ ≤ ENNReal.ofReal (2 * η) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
                    ← ENNReal.ofReal_add hη0.le (by positivity)]
                  apply ENNReal.ofReal_le_ofReal
                  have : (m : ℝ) * (η / (m + 1)) ≤ η := by
                    calc (m : ℝ) * (η / (m + 1)) = η * (m / (m + 1)) := by ring
                      _ ≤ η * 1 := mul_le_mul_of_nonneg_left
                          (by rw [div_le_one (by positivity)]; linarith) hη0.le
                      _ = η := mul_one η
                  linarith
          have h2 : μ K ≤ μ C + μ (K \ C) := by
            calc μ K ≤ μ (C ∪ (K \ C)) := measure_mono (fun x hx => by
                    by_cases h : x ∈ C
                    · exact Or.inl h
                    · exact Or.inr ⟨hx, h⟩)
              _ ≤ μ C + μ (K \ C) := measure_union_le _ _
          have hCfin : μ C ≠ ⊤ := ne_top_of_le_ne_top hμK (measure_mono hCK)
          have := h2.trans (add_le_add le_rfl h1)
          rw [← ENNReal.ofReal_toReal hμK, ← ENNReal.ofReal_toReal hCfin,
            ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)] at this
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
        have hSC : μ.real (Function.support ω₀ \ C) ≤ η := by
          have hfin' : μ (Function.support ω₀ \ C) ≠ ⊤ := ne_top_of_le_ne_top hVμ
            (measure_mono (sdiff_subset.trans hSV))
          rw [measureReal_def, ← ENNReal.ofReal_le_ofReal_iff hη0.le, ENNReal.ofReal_toReal hfin']
          exact hω₀μ.le
        have hmul : (1 - η) * (μ.real K - 2 * η) ≤ (1 - η) * μ.real C :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith [hC1, hrest, hsplit, hKC, hSC]
      -- conclude μ K ≤ massOn W
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      set a := μ.real K with hadef
      have ha : 0 ≤ a := measureReal_nonneg
      set η : ℝ := min (1 / 2) ((ε : ℝ) / (a + 3)) with hηdef
      have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
      have hη1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hηε : η * (a + 3) ≤ ε := by
        have := min_le_right (1 / 2 : ℝ) ((ε : ℝ) / (a + 3))
        rw [← hηdef] at this
        calc η * (a + 3) ≤ (ε : ℝ) / (a + 3) * (a + 3) := by gcongr
          _ = ε := div_mul_cancel₀ _ (by positivity)
      obtain ⟨ω, hωadm, hωT⟩ := key η hη0 hη1
      have hexp : (1 - η) * (a - 2 * η) - η = a - η * (a + 3) + 2 * η ^ 2 := by ring
      have hsq : 0 ≤ 2 * η ^ 2 := by positivity
      have hTε : a - ε ≤ T ω := by linarith
      calc μ K = ENNReal.ofReal a := (ENNReal.ofReal_toReal hμK).symm
        _ = ENNReal.ofReal ((a - ε) + ε) := by ring_nf
        _ ≤ ENNReal.ofReal (a - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ ≤ T.massOn W + ε := by
            gcongr
            · exact (ENNReal.ofReal_le_ofReal hTε).trans (T.le_massOn hωadm)
            · simp
    -- exhaustion
    obtain ⟨G, hGcl, hGW, hGU, hGmono⟩ := hW.exists_iUnion_isClosed
    set Kk : ℕ → Set (Euclid P) := fun k => G k ∩ closedBall 0 k with hKkdef
    have hKkc : ∀ k, IsCompact (Kk k) := fun k => (isCompact_closedBall 0 (k : ℝ)).inter_left (hGcl k)
    have hKkW : ∀ k, Kk k ⊆ W := fun k => inter_subset_left.trans (hGW k)
    have hKkmono : Monotone Kk := fun a b hab =>
      inter_subset_inter (hGmono hab) (closedBall_subset_closedBall (by exact_mod_cast hab))
    have hKkU : ⋃ k, Kk k = W := by
      apply Subset.antisymm (iUnion_subset hKkW)
      intro x hx
      rw [← hGU] at hx
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 hx
      obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.2 ⟨max k₀ k₁, hGmono (le_max_left _ _) hk₀, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk₁.trans (by exact_mod_cast le_max_right k₀ k₁)
    calc μ W = μ (⋃ k, Kk k) := by rw [hKkU]
      _ = ⨆ k, μ (Kk k) := hKkmono.measure_iUnion
      _ ≤ T.massOn W := iSup_le fun k => hKbound _ (hKkc k) (hKkW k)
  exact le_antisymm hupper (hlowerGen R.measure R.orient hrep hfin hmeas hH1 hH2)
/-- **Push-forward of an integer multiplicity current by a `C¹` diffeomorphism** (Simon Ch. 6,
2.23–2.24 and 3.3–3.9; the current `φ_#T` in the proof of 7.1.2).  Let `T = τ(M, θ, ξ)` and let
`φ` be a `C¹` bijection of `ℝᴾ` with `Dφ(x)` injective for every `x` and `φ = id` off a compact
`K ⊆ U`.  Then `S(ω) = ∫_M θ ⟨ω(φ(x)) ∘ Dφ(x), ξ(x)⟩ dHⁿ` defines a current `S = φ_#T`
(`Submission.dpf_pushforward_formula_current_exists`).  `φ` is bi-Lipschitz with `φ⁻¹(U) = U`
(`Submission.dpf_c1_compact_perturbation_bilipschitz`), so by the area formula and the
transport `T_{φ(x)}φ(M) = Dφ(x) TₓM` of approximate tangent planes, `S = τ(φ(M), θ ∘ φ⁻¹, ξ')`
with the induced orientation `ξ'` of 3.5/3.7 (`Submission.dpf_imrep_bilipschitz_image_rep`, which
needs `x ↦ p_{TₓM}` measurable: `Submission.imrep_approxTangent_starProjection_aesm`).  Hence `S`
is integer multiplicity.  Finally `∂S = 0` if `∂T = 0` (2.24(1), by smooth approximation of `φ`:
`Submission.dpf_pushforward_formula_boundaryVanishes`). -/
theorem Submission.imrep_c1_diffeo_pushforward_im : ∀ (P n : ℕ) (U K : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (φ : Euclid P → Euclid P), IsOpen U → R.Represents T → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → Bijective φ → (∀ x, Injective (fderiv ℝ φ x)) → (∀ x, x ∉ K → φ x = x) → ∃ S : GeometricCurrentOn U n, IsIntegerMultiplicity S ∧ (BoundaryVanishes T → BoundaryVanishes S) ∧ ∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ x)).compContinuousLinearMap (fderiv ℝ φ x)) ∂μHE[n] := by
  intro P n U K T R φ hU hR hK hKU hφ hbij hinj hid
  -- `φ` is bi-Lipschitz and `φ⁻¹(U) = U`
  obtain ⟨Λ, hLip, hAnti, hpre⟩ :=
    Submission.dpf_c1_compact_perturbation_bilipschitz P U K φ hK hKU hφ hbij hinj hid
  -- the push-forward integral is the action of a current `S`
  obtain ⟨S, hS⟩ := Submission.dpf_pushforward_formula_current_exists P n U K R φ hK hKU hφ hid
  -- an integer multiplicity triple `R'` on `φ(M)` has the same action
  obtain ⟨R', hR'⟩ := Submission.dpf_imrep_bilipschitz_image_rep P n U R φ Λ hU hφ hbij hinj
    hLip hAnti hpre (Submission.imrep_approxTangent_starProjection_aesm P n U R)
  exact ⟨S, ⟨R', fun ω => (hS ω).trans (hR' ω).symm⟩,
    Submission.dpf_pushforward_formula_boundaryVanishes P n U K T S R φ hU hR hK hKU hφ hid hS, hS⟩
/-- Tangential `C¹` deformations (Simon Ch. 2, before 5.8; Ch. 4, 2.5–2.6; step 3 of the proof
of 7.1.2).  A partition of unity splits `X = X₀ + Σᵢ χᵢX`: `X₀` vanishes on `N`, and `χᵢX` is
supported where `N` is straightened by `Ψ x = ψ(vₚ + g x) + (x - A g x)` (`A = Dψ(vₚ)`, `g A = id`,
so `DΨ(0) = I`; inverse function theorem, `Φ = Ψ⁻¹`).  `X₀` is deformed by `id + tX₀`, `Y = χᵢX`
by `Ψ (Φ y + t DΦ(y) Y(y))`, which keeps `N` since `DΦ Y` is tangent to the slice `{A g x = x}`
(`T_zN = range Dψ`) and has `Dφ_t = I + tDY + o(t)` uniformly (mean value inequality, symmetry of
`D²Ψ`).  Composition adds the expansions; for small `t` the result is a bijection with injective
derivative (`‖Dφ_t - I‖ ≤ 1/2`), and `φ_t = id` otherwise. -/
theorem Submission.tangential_c1_deformation_exists : ∀ (P d : ℕ) (U N : Set (Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → (∀ x ∈ N ∩ U, X x ∈ tangentSpace N x) → ∃ φ : ℝ → Euclid P → Euclid P, (∀ t, ContDiff ℝ 1 (φ t) ∧ Bijective (φ t) ∧ (∀ x, Injective (fderiv ℝ (φ t) x)) ∧ (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) (N ∩ U) (N ∩ U)) ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t| := by
  intro P d U N X hU hN hNU hX hXc hXU hXT
  classical
  -- small `t`: `|t| c < r` eventually as `t → 0`
  have hev : ∀ c r : ℝ, 0 < r → ∀ᶠ t in 𝓝 (0:ℝ), |t| * c < r := fun c r hr => by
    have h : ContinuousAt (fun t : ℝ => |t| * c) 0 :=
      (continuous_abs.mul continuous_const).continuousAt
    exact h.eventually_lt continuousAt_const
      (by show |(0:ℝ)| * c < r; rw [abs_zero, zero_mul]; exact hr)
  -- nonnegative bounds of continuous functions on compact sets
  have hbd : ∀ {F G : Type} [TopologicalSpace F] [SeminormedAddCommGroup G] (s : Set F) (f : F → G),
      IsCompact s → ContinuousOn f s → ∃ M, 0 ≤ M ∧ ∀ x ∈ s, ‖f x‖ ≤ M := fun s f hs hf =>
    let ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hf
    ⟨max M 0, le_max_right _ _, fun x hx => (hM x hx).trans (le_max_left _ _)⟩
  -- the algebra of the two expansions (`D²Ψ` symmetric)
  have halg : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (L1 L0 G DV : E →L[ℝ] E)
      (D2 : E →L[ℝ] E →L[ℝ] E) (w : E) (t : ℝ), (∀ u v, D2 u v = D2 v u) →
      L1.comp (G + t • DV) - L0.comp G - t • (L0.comp DV + (D2.comp G).flip w) =
        (L1 - L0 - t • D2 w).comp G + t • ((L1 - L0).comp DV) := by
    intro E _ _ L1 L0 G DV D2 w t hs
    ext v
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.flip_apply, map_add, map_smul, smul_sub, smul_add, hs (G v) w]
    abel
  have halg2 : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (Pm Q a a' b : E →L[ℝ] E)
      (t : ℝ), Pm.comp Q - ContinuousLinearMap.id ℝ E - t • (a + b) =
        (Pm - ContinuousLinearMap.id ℝ E - t • a').comp Q +
          (Q - ContinuousLinearMap.id ℝ E - t • b) + t • a'.comp (Q - ContinuousLinearMap.id ℝ E) +
          t • (a' - a) := by
    intro E _ _ Pm Q a a' b t
    ext v
    simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_sub, smul_sub, smul_add]
    abel
  -- conjugated deformations `φ_t y = Ψ (Φ y + t DΦ(y) Y(y))` near `spt Y`, `φ_t y = y` elsewhere
  have gconj : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
      (Ψ Φ Y Vf : E → E) (φ : ℝ → E → E) (B O : Set E), IsOpen B → IsOpen O →
      (∀ b ∈ B, ContDiffAt ℝ 2 Ψ b) → (∀ y ∈ O, ContDiffAt ℝ 2 Φ y ∧ Φ y ∈ B ∧ Ψ (Φ y) = y) →
      ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ O →
      (∀ y, Vf y = fderiv ℝ Φ y (Y y)) →
      (∀ t y, φ t y = if y ∈ O then Ψ (Φ y + t • Vf y) else y) →
      (∀ t y, y ∉ tsupport Y → φ t y = y) ∧
      ∃ C : ℝ, (∀ᶠ t in 𝓝 (0:ℝ), ContDiff ℝ 1 (φ t) ∧ (∀ y ∈ tsupport Y, Φ y + t • Vf y ∈ B) ∧
          ∀ y, ‖φ t y - y‖ ≤ C * |t|) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 (0:ℝ), ∀ y,
          ‖fderiv ℝ (φ t) y - ContinuousLinearMap.id ℝ E - t • fderiv ℝ Y y‖ ≤ ε * |t| := by
    intro E _ _ _ Ψ Φ Y Vf φ B O hB hO hΨ hΦ hY hYc hYO hVf hφ
    -- derivatives of `Ψ`, `DΨ`, `Φ` and `Vf = DΦ · Y`
    have hΦd : ∀ y ∈ O, HasFDerivAt Φ (fderiv ℝ Φ y) y := fun y hy =>
      ((hΦ y hy).1.differentiableAt two_ne_zero).hasFDerivAt
    have hΨ1 : ∀ b ∈ B, ContDiffAt ℝ 1 (fderiv ℝ Ψ) b := fun b hb =>
      (hΨ b hb).fderiv_right (by norm_num)
    have hΨd : ∀ b ∈ B, HasFDerivAt Ψ (fderiv ℝ Ψ b) b := fun b hb =>
      ((hΨ b hb).differentiableAt two_ne_zero).hasFDerivAt
    have hΨ2d : ∀ b ∈ B, HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) b) b := fun b hb =>
      ((hΨ1 b hb).differentiableAt one_ne_zero).hasFDerivAt
    have hVfC : ∀ y ∈ O, ContDiffAt ℝ 1 Vf y := fun y hy =>
      (((hΦ y hy).1.fderiv_right (by norm_num)).clm_apply hY.contDiffAt).congr_of_eventuallyEq
        (Eventually.of_forall hVf)
    have hVfd : ∀ y ∈ O, HasFDerivAt Vf (fderiv ℝ Vf y) y := fun y hy =>
      ((hVfC y hy).differentiableAt one_ne_zero).hasFDerivAt
    -- `DΨ(Φ y) ∘ DΦ(y) = id` on `O`, so `Y = DΨ(Φ) · Vf` there
    have hinv : ∀ y ∈ O, (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Φ y) = ContinuousLinearMap.id ℝ E :=
      fun y hy => ((hΨd _ (hΦ y hy).2.1).comp y (hΦd y hy)).unique
        ((hasFDerivAt_id y).congr_of_eventuallyEq
          (eventually_of_mem (hO.mem_nhds hy) fun z hz => (hΦ z hz).2.2))
    have hYΨ : ∀ y ∈ O, fderiv ℝ Ψ (Φ y) (Vf y) = Y y := fun y hy => by
      rw [hVf, ← ContinuousLinearMap.comp_apply, hinv y hy, ContinuousLinearMap.id_apply]
    have hid : ∀ t y, y ∉ tsupport Y → φ t y = y := fun t y hy => by
      rw [hφ]
      split_ifs with h
      · rw [hVf, image_eq_zero_of_notMem_tsupport hy, map_zero, smul_zero, add_zero,
          (hΦ y h).2.2]
      · rfl
    refine ⟨hid, ?_⟩
    -- compact sets and bounds
    have hK : IsCompact (tsupport Y) := hYc
    have hΦK : IsCompact (Φ '' tsupport Y) :=
      hK.image_of_continuousOn fun y hy => (hΦd y (hYO hy)).continuousAt.continuousWithinAt
    obtain ⟨η, hη, hηB⟩ := hΦK.exists_cthickening_subset_open hB
      (image_subset_iff.2 fun y hy => (hΦ y (hYO hy)).2.1)
    have hK₂ : IsCompact (cthickening η (Φ '' tsupport Y)) := hΦK.cthickening
    have hD2c : ContinuousOn (fderiv ℝ (fderiv ℝ Ψ)) (cthickening η (Φ '' tsupport Y)) :=
      fun c hc => ((hΨ1 c (hηB hc)).continuousAt_fderiv one_ne_zero).continuousWithinAt
    obtain ⟨M1, hM10, hM1⟩ := hbd _ (fderiv ℝ Ψ) hK₂ fun c hc =>
      (hΨ1 c (hηB hc)).continuousAt.continuousWithinAt
    obtain ⟨M2, hM20, hM2⟩ := hbd _ _ hK₂ hD2c
    obtain ⟨MΦ, hMΦ0, hMΦ⟩ := hbd _ (fderiv ℝ Φ) hK fun y hy =>
      ((hΦ y (hYO hy)).1.continuousAt_fderiv two_ne_zero).continuousWithinAt
    obtain ⟨MV, hMV0, hMV⟩ := hbd _ Vf hK fun y hy =>
      (hVfC y (hYO hy)).continuousAt.continuousWithinAt
    obtain ⟨MDV, hMDV0, hMDV⟩ := hbd _ (fderiv ℝ Vf) hK fun y hy =>
      ((hVfC y (hYO hy)).continuousAt_fderiv one_ne_zero).continuousWithinAt
    -- for small `t`, the segment `[Φ y, Φ y + t Vf y]` lies in a ball inside `cthickening η (Φ K)`
    have hball : ∀ y ∈ tsupport Y, ∀ t : ℝ, |t| * MV < η →
        closedBall (Φ y) (|t| * MV) ⊆ cthickening η (Φ '' tsupport Y) ∧
          Φ y + t • Vf y ∈ closedBall (Φ y) (|t| * MV) := fun y hy t ht =>
      ⟨(closedBall_subset_closedBall ht.le).trans
        (closedBall_subset_cthickening (mem_image_of_mem Φ hy) η), by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hMV y hy) (abs_nonneg t)⟩
    have hev0 : ∀ t, ∀ y ∈ O, φ t =ᶠ[𝓝 y] fun z => Ψ (Φ z + t • Vf z) := fun t y hy =>
      eventually_of_mem (hO.mem_nhds hy) fun z hz => by rw [hφ, ite_eq_left hz]
    have hev1 : ∀ t, ∀ y ∉ tsupport Y, φ t =ᶠ[𝓝 y] id := fun t y hy =>
      eventually_of_mem ((isClosed_tsupport Y).isOpen_compl.mem_nhds hy) fun z hz => hid t z hz
    refine ⟨M1 * MV, ?_, fun ε hε => ?_⟩
    · -- `C¹`, the deformed points stay in `B`, displacement `≤ M1 MV |t|`
      filter_upwards [hev MV η hη] with t ht
      have hmem : ∀ y ∈ tsupport Y, Φ y + t • Vf y ∈ B := fun y hy =>
        hηB ((hball y hy t ht).1 (hball y hy t ht).2)
      refine ⟨contDiff_iff_contDiffAt.2 fun y => ?_, hmem, fun y => ?_⟩
      · by_cases hy : y ∈ tsupport Y
        · have hyO := hYO hy
          exact (((hΨ _ (hmem y hy)).of_le (by norm_num)).comp y (((hΦ y hyO).1.of_le
            (by norm_num)).add ((hVfC y hyO).const_smul t))).congr_of_eventuallyEq (hev0 t y hyO)
        · exact contDiffAt_id.congr_of_eventuallyEq (hev1 t y hy)
      · by_cases hy : y ∈ tsupport Y
        · have hyO := hYO hy
          have h :=
            (convex_closedBall (Φ y) (|t| * MV)).norm_image_sub_le_of_norm_hasFDerivWithin_le
              (f := Ψ) (fun c hc => (hΨd c (hηB ((hball y hy t ht).1 hc))).hasFDerivWithinAt)
              (fun c hc => hM1 c ((hball y hy t ht).1 hc))
              (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0)) (hball y hy t ht).2
          rw [(hΦ y hyO).2.2, add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h
          rw [hφ, ite_eq_left hyO, mul_assoc, mul_comm MV]
          exact h.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hMV y hy)
            (abs_nonneg t)) hM10)
        · rw [hid t y hy, sub_self, norm_zero]
          exact mul_nonneg (mul_nonneg hM10 hMV0) (abs_nonneg t)
    -- the expansion `Dφ_t = I + t DY + o(t)`
    obtain ⟨ε₁, hε₁, hε₁b⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ * (MV * MΦ) ≤ ε / 2 := by
      have h1 : 0 < MV * MΦ + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hMV0 hMΦ0) one_pos
      refine ⟨ε / 2 / (MV * MΦ + 1), div_pos (half_pos hε) h1, ?_⟩
      rw [div_mul_eq_mul_div, div_le_iff₀ h1]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (half_pos hε).le
    obtain ⟨δ₂, hδ₂, hUC⟩ := Metric.uniformContinuousOn_iff_le.1
      (hK₂.uniformContinuousOn_of_continuous hD2c) ε₁ hε₁
    filter_upwards [hev MV η hη, hev MV δ₂ hδ₂,
      hev ((ε₁ * MV + M2 * MV) * MDV) (ε / 2) (half_pos hε)] with t ht1 ht2 ht3 y
    by_cases hy : y ∈ tsupport Y
    · have hyO := hYO hy
      have hΦyB := (hΦ y hyO).2.1
      obtain ⟨hsub, hmem⟩ := hball y hy t ht1
      have hΦyK : Φ y ∈ cthickening η (Φ '' tsupport Y) :=
        hsub (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0))
      have hbtw : Φ y + t • Vf y ∈ B := hηB (hsub hmem)
      have hDφ : fderiv ℝ (φ t) y = (fderiv ℝ Ψ (Φ y + t • Vf y)).comp
          (fderiv ℝ Φ y + t • fderiv ℝ Vf y) :=
        (((hΨd _ hbtw).comp y ((hΦd y hyO).add ((hVfd y hyO).const_smul t))).congr_of_eventuallyEq
          (hev0 t y hyO)).fderiv
      have hDY : fderiv ℝ Y y = (fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y) +
          ((fderiv ℝ (fderiv ℝ Ψ) (Φ y)).comp (fderiv ℝ Φ y)).flip (Vf y) :=
        ((((hΨ2d _ hΦyB).comp y (hΦd y hyO)).clm_apply (hVfd y hyO)).congr_of_eventuallyEq
          (eventually_of_mem (hO.mem_nhds hyO) fun z hz => (hYΨ z hz).symm)).fderiv
      have hsymm := (hΨ _ hΦyB).isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
      rw [hDφ, hDY, ← hinv y hyO, halg _ _ _ _ _ _ t hsymm]
      -- mean value inequality for `DΨ` on the ball
      have hm1 := (convex_closedBall (Φ y) (|t| * MV)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (f := fderiv ℝ Ψ) (φ := fderiv ℝ (fderiv ℝ Ψ) (Φ y))
        (fun c hc => (hΨ2d c (hηB (hsub hc))).hasFDerivWithinAt)
        (fun c hc => by
          rw [← dist_eq_norm]
          exact hUC c (hsub hc) _ hΦyK ((mem_closedBall.1 hc).trans ht2.le))
        (mem_closedBall_self (mul_nonneg (abs_nonneg t) hMV0)) hmem
      rw [add_sub_cancel_left, map_smul] at hm1
      have hw : ‖t • Vf y‖ ≤ |t| * MV := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMV y hy) (abs_nonneg t)
      have hA1 := hm1.trans (mul_le_mul_of_nonneg_left hw hε₁.le)
      have hA2 : ‖t • fderiv ℝ (fderiv ℝ Ψ) (Φ y) (Vf y)‖ ≤ |t| * (M2 * MV) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hM2 _ hΦyK) (hMV y hy) (norm_nonneg _) hM20)) (abs_nonneg t)
      have hA3 := (norm_le_norm_add_norm_sub' _ _).trans (add_le_add hA2 hA1)
      have hT1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hA1 (hMΦ y hy) (norm_nonneg _)
          (mul_nonneg hε₁.le (mul_nonneg (abs_nonneg t) hMV0)))
      have hT2 : ‖t • ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y))‖ ≤
          |t| * ((|t| * (M2 * MV) + ε₁ * (|t| * MV)) * MDV) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hA3 (hMDV y hy) (norm_nonneg _) (by positivity))) (abs_nonneg t)
      have h1 := mul_le_mul_of_nonneg_left hε₁b (abs_nonneg t)
      have h2 := mul_le_mul_of_nonneg_left ht3.le (abs_nonneg t)
      linarith only [norm_add_le ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y) -
        t • fderiv ℝ (fderiv ℝ Ψ) (Φ y) (Vf y)).comp (fderiv ℝ Φ y))
        (t • ((fderiv ℝ Ψ (Φ y + t • Vf y) - fderiv ℝ Ψ (Φ y)).comp (fderiv ℝ Vf y))), hT1, hT2,
        h1, h2]
    · rw [(hev1 t y hy).fderiv_eq, fderiv_id,
        image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_fderiv_subset ℝ h), smul_zero,
        sub_self, sub_zero, norm_zero]
      exact mul_nonneg hε.le (abs_nonneg t)
  -- `Good A`: a `C¹` family fixing `N` and `K = spt X` with `Dφ_t = I + t DA + o(t)` uniformly
  obtain ⟨Good, hGood⟩ : ∃ Good : (Euclid P → Euclid P) → Prop, ∀ A, Good A ↔
      ∃ φ : ℝ → Euclid P → Euclid P, ∃ C : ℝ, (∀ᶠ t in 𝓝 (0:ℝ), ContDiff ℝ 1 (φ t) ∧
        (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ t in 𝓝 (0:ℝ), ∀ x,
        ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ A x‖ ≤ ε * |t| :=
    ⟨_, fun _ => Iff.rfl⟩
  -- composition: `Good A`, `Good B` give `Good (A + B)` (`DA` uniformly continuous)
  have gadd : ∀ A B : Euclid P → Euclid P, ContDiff ℝ 1 A → HasCompactSupport A →
      ContDiff ℝ 1 B → HasCompactSupport B → Good A → Good B → Good (A + B) := by
    intro A B hA hAc hB hBc hGA hGB
    obtain ⟨φ, C₁, hφ, eφ⟩ := (hGood A).1 hGA
    obtain ⟨ψ, C₂, hψ, eψ⟩ := (hGood B).1 hGB
    refine (hGood _).2 ⟨fun t => φ t ∘ ψ t, C₁ + C₂, ?_, fun ε hε => ?_⟩
    · filter_upwards [hφ, hψ] with t h g
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨g1, g2, g3, g4⟩ := g
      refine ⟨h1.comp g1, fun x hx => ?_, h3.comp g3, fun x => ?_⟩
      · rw [Function.comp_apply, g2 x hx, h2 x hx]
      · rw [Function.comp_apply, add_mul]
        exact (norm_sub_le_norm_sub_add_norm_sub _ (ψ t x) _).trans (add_le_add (h4 _) (g4 _))
    · obtain ⟨MA, hMA⟩ :=
        (hAc.fderiv ℝ).exists_bound_of_continuous (hA.continuous_fderiv one_ne_zero)
      obtain ⟨MB, hMB⟩ :=
        (hBc.fderiv ℝ).exists_bound_of_continuous (hB.continuous_fderiv one_ne_zero)
      have hMA0 : 0 ≤ MA := (norm_nonneg _).trans (hMA 0)
      have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
      have hε4 : 0 < ε / 4 := by positivity
      obtain ⟨η, hη, hUC⟩ := Metric.uniformContinuous_iff.1
        ((hAc.fderiv ℝ).uniformContinuous_of_continuous (hA.continuous_fderiv one_ne_zero)) _ hε4
      filter_upwards [hφ, hψ, eφ (ε / 8) (by positivity), eψ (ε / 4) hε4,
        hev (ε / 4 + MB) 1 one_pos, hev ((ε / 4 + MB) * MA) (ε / 4) hε4, hev C₂ η hη]
        with t h g e1 e2 k1 k2 k3 x
      obtain ⟨h1, -, -, -⟩ := h
      obtain ⟨g1, -, -, g4⟩ := g
      rw [fderiv_comp x ((h1.differentiable one_ne_zero) _) ((g1.differentiable one_ne_zero) _),
        ((hA.differentiable one_ne_zero x).hasFDerivAt.add
          (hB.differentiable one_ne_zero x).hasFDerivAt).fderiv, halg2 _ _ _ (fderiv ℝ A (ψ t x))]
      have e1' := e1 (ψ t x)
      have e2' := e2 x
      have htb : ‖t • fderiv ℝ B x‖ ≤ |t| * MB := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hMB x) (abs_nonneg t)
      have hQI := (norm_le_norm_add_norm_sub' (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _)
        (t • fderiv ℝ B x)).trans (add_le_add htb e2')
      have hQ2 : ‖fderiv ℝ (ψ t) x‖ ≤ 2 := by
        have := (norm_le_norm_add_norm_sub' (fderiv ℝ (ψ t) x) (ContinuousLinearMap.id ℝ _)).trans
          (add_le_add ContinuousLinearMap.norm_id_le hQI)
        linarith only [this, k1]
      have hT1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul e1' hQ2 (norm_nonneg _) (mul_nonneg (by positivity) (abs_nonneg t)))
      have hT3 : ‖t • (fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _)‖ ≤
          |t| * (MA * (|t| * MB + ε / 4 * |t|)) := by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul (hMA _) hQI (norm_nonneg _) hMA0)) (abs_nonneg t)
      have hT4 : ‖t • (fderiv ℝ A (ψ t x) - fderiv ℝ A x)‖ ≤ |t| * (ε / 4) := by
        rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
        refine mul_le_mul_of_nonneg_left (hUC ?_).le (abs_nonneg t)
        rw [dist_eq_norm]
        exact (g4 x).trans_lt (by rw [mul_comm]; exact k3)
      have h2 := mul_le_mul_of_nonneg_left k2.le (abs_nonneg t)
      linarith only [norm_add₄_le (a := ((fderiv ℝ (φ t) (ψ t x) - ContinuousLinearMap.id ℝ _ -
        t • fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x))) (b := fderiv ℝ (ψ t) x -
          ContinuousLinearMap.id ℝ _ - t • fderiv ℝ B x)
        (c := t • (fderiv ℝ A (ψ t x)).comp (fderiv ℝ (ψ t) x - ContinuousLinearMap.id ℝ _))
        (d := t • (fderiv ℝ A (ψ t x) - fderiv ℝ A x)), hT1, e2', hT3, hT4, h2]
  -- near `p ∈ N`: straighten `N` by `Ψ x = ψ(vp + g x) + (x - A g x)` (`g A = id`, `DΨ(0) = I`)
  have glocal : ∀ p ∈ N, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∀ χ : Euclid P → ℝ,
      ContDiff ℝ 1 χ → tsupport χ ⊆ O → Good (fun x => χ x • X x) := by
    intro p hp
    obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hψinj, hψim, hψprop, hψD⟩ := hN p hp
    obtain ⟨vp, hvpV, hvp⟩ : p ∈ ψ '' V := by rw [hψim]; exact ⟨hpW, hp⟩
    have hψ2 : ∀ v ∈ V, ContDiffAt ℝ 2 ψ v := fun v hv => hψ.contDiffAt (hV.mem_nhds hv)
    obtain ⟨A, hA⟩ : ∃ A, A = fderiv ℝ ψ vp := ⟨_, rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : Euclid P →L[ℝ] Euclid d, ∀ a, g (A a) = a := by
      obtain ⟨g', hg'⟩ := LinearMap.exists_leftInverse_of_injective (A : Euclid d →ₗ[ℝ] Euclid P)
        (LinearMap.ker_eq_bot.2 (by rw [hA]; exact hψD vp hvpV))
      exact ⟨LinearMap.toContinuousLinearMap g', fun a => LinearMap.congr_fun hg' a⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid P → Euclid P, ∀ x, Ψ x = ψ (vp + g x) + (x - A (g x)) :=
      ⟨_, fun _ => rfl⟩
    have hΨC : ∀ x, vp + g x ∈ V → ContDiffAt ℝ 2 Ψ x := fun x hx =>
      (((hψ2 _ hx).comp x (contDiffAt_const.add g.contDiff.contDiffAt)).add
        (contDiffAt_id.sub (A.comp g).contDiff.contDiffAt)).congr_of_eventuallyEq
        (Eventually.of_forall hΨ)
    have hΨD : ∀ x, vp + g x ∈ V → HasFDerivAt Ψ ((fderiv ℝ ψ (vp + g x)).comp g +
        (ContinuousLinearMap.id ℝ _ - A.comp g)) x := fun x hx =>
      ((((hψ2 _ hx).differentiableAt two_ne_zero).hasFDerivAt.comp x
        (g.hasFDerivAt.const_add vp)).add ((hasFDerivAt_id x).sub
          (A.comp g).hasFDerivAt)).congr_of_eventuallyEq (Eventually.of_forall hΨ)
    have h0V : vp + g 0 ∈ V := by rw [map_zero, add_zero]; exact hvpV
    have hΨD0 : HasFDerivAt Ψ
        ((ContinuousLinearEquiv.refl ℝ (Euclid P) : Euclid P ≃L[ℝ] Euclid P) :
          Euclid P →L[ℝ] Euclid P) 0 := by
      have h := hΨD 0 h0V
      rw [map_zero, add_zero, ← hA, add_sub_cancel] at h
      rw [ContinuousLinearEquiv.coe_refl]
      exact h
    -- inverse function theorem
    have hstrict := (hΨC 0 h0V).hasStrictFDerivAt' hΨD0 two_ne_zero
    obtain ⟨H, hHcoe, h0H⟩ : ∃ H : OpenPartialHomeomorph (Euclid P) (Euclid P),
        ⇑H = Ψ ∧ (0 : Euclid P) ∈ H.source :=
      ⟨hstrict.toOpenPartialHomeomorph Ψ, hstrict.toOpenPartialHomeomorph_coe,
        hstrict.mem_toOpenPartialHomeomorph_source⟩
    have hΩ : IsOpen {x : Euclid P | vp + g x ∈ V} :=
      hV.preimage (continuous_const.add g.continuous)
    have hDΨc : ContinuousOn (fderiv ℝ Ψ) {x : Euclid P | vp + g x ∈ V} := fun x hx =>
      ((hΨC x hx).continuousAt_fderiv two_ne_zero).continuousWithinAt
    obtain ⟨B, hBo, h0B, hBH, hBV, hBe⟩ : ∃ B : Set (Euclid P), IsOpen B ∧ (0 : Euclid P) ∈ B ∧
        (∀ b ∈ B, b ∈ H.source) ∧ (∀ b ∈ B, vp + g b ∈ V) ∧
        ∀ b ∈ B, ∃ e : Euclid P ≃L[ℝ] Euclid P, (e : Euclid P →L[ℝ] Euclid P) = fderiv ℝ Ψ b :=
      ⟨_, H.open_source.inter (hDΨc.isOpen_inter_preimage hΩ ContinuousLinearEquiv.isOpen),
        ⟨h0H, h0V, _, hΨD0.fderiv.symm⟩, fun b hb => hb.1, fun b hb => hb.2.1, fun b hb => hb.2.2⟩
    obtain ⟨O, hOo, hO⟩ : ∃ O : Set (Euclid P), IsOpen O ∧
        ∀ y, y ∈ O ↔ y ∈ H.target ∧ H.symm y ∈ B :=
      ⟨_, H.isOpen_inter_preimage_symm hBo, fun y => Iff.rfl⟩
    have hΦ : ∀ y ∈ O, ContDiffAt ℝ 2 H.symm y ∧ H.symm y ∈ B ∧ Ψ (H.symm y) = y ∧
        ∀ u, fderiv ℝ H.symm y (fderiv ℝ Ψ (H.symm y) u) = u := by
      intro y hy
      obtain ⟨hyT, hyB⟩ := (hO y).1 hy
      obtain ⟨e, he⟩ := hBe _ hyB
      have hC : ContDiffAt ℝ 2 Ψ (H.symm y) := hΨC _ (hBV _ hyB)
      have hD : HasFDerivAt H (e : Euclid P →L[ℝ] Euclid P) (H.symm y) := by
        rw [hHcoe, he]; exact (hC.differentiableAt two_ne_zero).hasFDerivAt
      refine ⟨H.contDiffAt_symm hyT hD (hHcoe ▸ hC), hyB, hHcoe ▸ H.right_inv hyT, fun u => ?_⟩
      rw [(H.hasFDerivAt_symm hyT hD).fderiv, ← he]
      exact e.symm_apply_apply u
    have hΨB : ∀ b ∈ B, H.symm (Ψ b) = b := fun b hb => hHcoe ▸ H.left_inv (hBH b hb)
    have hpO : p ∈ O := by
      have hΨ0 : Ψ 0 = p := by rw [hΨ, map_zero, add_zero, map_zero, sub_zero, add_zero, hvp]
      rw [← hΨ0]
      refine (hO _).2 ⟨hHcoe ▸ H.map_source (hBH 0 h0B), ?_⟩
      rw [hΨB 0 h0B]; exact h0B
    -- the slice: near `p`, `Φ = H.symm` maps `N` into `{x | A (g x) = x}`
    obtain ⟨ε₁, hε₁, hε₁B⟩ : ∃ ε₁ > 0, ∀ v', dist v' vp < ε₁ → A (v' - vp) ∈ B := by
      have hc : Continuous fun v' => A (v' - vp) :=
        A.continuous.comp (continuous_id.sub continuous_const)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hBo.preimage hc) vp
        (by show A (vp - vp) ∈ B; rw [sub_self, map_zero]; exact h0B)
      exact ⟨ε, hε, fun v' hv' => hball (mem_ball.2 hv')⟩
    obtain ⟨δ₁, hδ₁, hδ₁V⟩ := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn
      hψinj (by rw [hψim]; exact inter_subset_left) hψprop vp hvpV ε₁ hε₁
    have hsl : ∀ z ∈ N, z ∈ O ∩ (W ∩ ball p δ₁) → A (g (H.symm z)) = H.symm z := by
      rintro z hzN ⟨-, hzW, hzp⟩
      obtain ⟨v', hv'V, rfl⟩ : z ∈ ψ '' V := by rw [hψim]; exact ⟨hzW, hzN⟩
      have hx := hε₁B v' (hδ₁V v' hv'V (by rw [hvp]; exact hzp))
      have hΨx : Ψ (A (v' - vp)) = ψ v' := by
        rw [hΨ, hg, add_sub_cancel, sub_self, add_zero]
      rw [← hΨx, hΨB _ hx, hg]
    refine ⟨O ∩ (W ∩ ball p δ₁), hOo.inter (hW.inter isOpen_ball), ⟨hpO, hpW, mem_ball_self hδ₁⟩,
      fun χ hχ hχO => ?_⟩
    -- the local field `Y = χ X` and its deformation `Ψ (Φ y + t DΦ(y) Y(y))`
    have hYX : tsupport (fun x => χ x • X x) ⊆ tsupport X := tsupport_smul_subset_right _ _
    have hYO : tsupport (fun x => χ x • X x) ⊆ O ∩ (W ∩ ball p δ₁) :=
      (tsupport_smul_subset_left _ _).trans hχO
    obtain ⟨Vf, hVf⟩ : ∃ Vf : Euclid P → Euclid P, ∀ y, Vf y = fderiv ℝ H.symm y (χ y • X y) :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → Euclid P → Euclid P,
        ∀ t y, φ t y = if y ∈ O then Ψ (H.symm y + t • Vf y) else y := ⟨_, fun _ _ => rfl⟩
    obtain ⟨hid, C, hφev, hexp⟩ := gconj Ψ H.symm (fun x => χ x • X x) Vf φ B O hBo hOo
      (fun b hb => hΨC b (hBV b hb)) (fun y hy => ⟨(hΦ y hy).1, (hΦ y hy).2.1, (hΦ y hy).2.2.1⟩)
      (hχ.smul hX) (hXc.mono (support_smul_subset_right χ X)) (fun y hy => (hYO hy).1) hVf hφ
    -- tangency: `DΦ(z) Y(z)` lies in `{x | A (g x) = x}` for `z ∈ N`
    have htan : ∀ z ∈ N, z ∈ tsupport (fun x => χ x • X x) → A (g (Vf z)) = Vf z := by
      intro z hzN hzY
      have hsz := hsl z hzN (hYO hzY)
      obtain ⟨-, hzB, hΨz, hinvz⟩ := hΦ z (hYO hzY).1
      have hzψ : ψ (vp + g (H.symm z)) = z := by
        rw [hΨ, hsz, sub_self, add_zero] at hΨz; exact hΨz
      have hT := Submission.chart_tangentSpace_eq_range_fderiv P d 2 N W V ψ (vp + g (H.symm z))
        (by norm_num) hV hW hψ hψinj hψim hψprop hψD (hBV _ hzB)
      rw [hzψ] at hT
      obtain ⟨h, hh⟩ : X z ∈ range (fderiv ℝ ψ (vp + g (H.symm z))) := by
        rw [← hT]; exact hXT z ⟨hzN, hXU (hYX hzY)⟩
      have hDΨu : fderiv ℝ Ψ (H.symm z) (A (χ z • h)) = χ z • X z := by
        rw [(hΨD _ (hBV _ hzB)).fderiv, add_apply, ContinuousLinearMap.comp_apply, sub_apply,
          ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, hg, sub_self, add_zero,
          map_smul, hh]
      rw [hVf, ← hDΨu, hinvz, hg]
    refine (hGood _).2 ⟨φ, C, ?_, hexp⟩
    filter_upwards [hφev] with t ht
    obtain ⟨h1, h2, h3⟩ := ht
    refine ⟨h1, fun x hx => hid t x fun h => hx (hYX h), fun z hz => ?_, h3⟩
    by_cases hzY : z ∈ tsupport (fun x => χ x • X x)
    · have hS : A (g (H.symm z + t • Vf z)) = H.symm z + t • Vf z := by
        rw [map_add, map_smul, map_add, map_smul, hsl z hz (hYO hzY), htan z hz hzY]
      rw [hφ, ite_eq_left (hYO hzY).1, hΨ, hS, sub_self, add_zero]
      exact ((Set.ext_iff.1 hψim _).1 (mem_image_of_mem ψ (hBV _ (h2 z hzY)))).2
    · rw [hid t z hzY]; exact hz
  -- `N ∩ K` is compact, as `(N̄ \ N) ∩ U = ∅`
  have hNK : IsCompact (N ∩ tsupport X) := by
    have h : N ∩ tsupport X = closure N ∩ tsupport X := by
      refine Subset.antisymm (inter_subset_inter_left _ subset_closure) fun x hx => ⟨?_, hx.2⟩
      by_contra hxN
      exact (hNU.subset ⟨⟨hx.1, hxN⟩, hXU hx.2⟩ : x ∈ (∅ : Set (Euclid P)))
    rw [h]; exact hXc.isCompact.inter_left isClosed_closure
  -- a partition of unity subordinate to finitely many straightening charts and `U \ N̄`
  choose O hOo hpO hOgood using fun p : ↥(N ∩ tsupport X) => glocal p.1 p.2.1
  obtain ⟨s, hs⟩ := hNK.elim_finite_subcover O hOo fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hpO ⟨x, hx⟩⟩
  have hGopen : ∀ j : Option ↥s, IsOpen (Option.elim j (U \ closure N) fun i => O i.1) := by
    rintro (_ | i)
    · exact hU.sdiff isClosed_closure
    · exact hOo _
  have hGcover : tsupport X ⊆ ⋃ j : Option ↥s, Option.elim j (U \ closure N) fun i => O i.1 := by
    intro x hx
    by_cases hxN : x ∈ N
    · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hs ⟨hxN, hx⟩)
      exact mem_iUnion.2 ⟨some ⟨i, hi⟩, hxi⟩
    · exact mem_iUnion.2 ⟨none, hXU hx, fun hxc =>
        (hNU.subset ⟨⟨hxc, hxN⟩, hXU hx⟩ : x ∈ (∅ : Set (Euclid P)))⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) (isClosed_tsupport X) _ hGopen hGcover
  have hfC : ∀ j, ContDiff ℝ 1 (f j) := fun j =>
    (contMDiff_iff_contDiff.1 (f j).contMDiff).of_le (by exact_mod_cast le_top)
  have hdecomp : ∑ j, (fun x => f j x • X x) = X := by
    funext x
    rw [Finset.sum_apply]
    by_cases hx : x ∈ tsupport X
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, f.sum_eq_one hx, one_smul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, smul_zero, Finset.sum_const_zero]
  have hpieces : ∀ j ∈ (Finset.univ : Finset (Option ↥s)), ContDiff ℝ 1 (fun x => f j x • X x) ∧
      HasCompactSupport (fun x => f j x • X x) ∧ Good (fun x => f j x • X x) := by
    rintro (_ | i) -
    · -- away from `N`: `id + t f₀ X`, as `f₀ X = 0` on `N`
      have hAC : ContDiff ℝ 1 (fun x => f none x • X x) := (hfC _).smul hX
      have hAc : HasCompactSupport (fun x => f none x • X x) :=
        hXc.mono (support_smul_subset_right (f none) X)
      refine ⟨hAC, hAc, (hGood _).2 ?_⟩
      obtain ⟨MA, hMA⟩ := hAc.exists_bound_of_continuous hAC.continuous
      refine ⟨fun t x => x + t • (f none x • X x), MA, Eventually.of_forall fun t =>
        ⟨contDiff_id.add (hAC.const_smul t), fun x hx => ?_, fun z hz => ?_, fun x => ?_⟩,
        fun ε hε => Eventually.of_forall fun t x => ?_⟩
      · beta_reduce
        rw [image_eq_zero_of_notMem_tsupport hx, smul_zero, smul_zero, add_zero]
      · have hz0 : f none z = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => (hf none h).2 (subset_closure hz)
        beta_reduce
        rw [hz0, zero_smul, smul_zero, add_zero]; exact hz
      · beta_reduce
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hMA x) (abs_nonneg t)
      · have hd : HasFDerivAt (fun x => x + t • (f none x • X x)) (ContinuousLinearMap.id ℝ _ +
            t • fderiv ℝ (fun x => f none x • X x) x) x :=
          (hasFDerivAt_id x).add ((hAC.differentiable one_ne_zero x).hasFDerivAt.const_smul t)
        beta_reduce
        rw [hd.fderiv, add_sub_cancel_left, sub_self, norm_zero]
        exact mul_nonneg hε.le (abs_nonneg t)
    · exact ⟨(hfC _).smul hX, hXc.mono (support_smul_subset_right (f (some i)) X),
        hOgood i.1 (f (some i)) (hfC _) (hf (some i))⟩
  obtain ⟨-, -, hGX⟩ := Finset.sum_induction_nonempty (fun j x => f j x • X x)
    (fun A => ContDiff ℝ 1 A ∧ HasCompactSupport A ∧ Good A)
    (fun A B hA hB => ⟨hA.1.add hB.1, hA.2.1.add hB.2.1,
      gadd A B hA.1 hA.2.1 hB.1 hB.2.1 hA.2.2 hB.2.2⟩)
    Finset.univ_nonempty hpieces
  rw [hdecomp] at hGX
  -- final family: `φ_t` for good small `t` (where `‖Dφ_t - I‖ ≤ 1/2`), `id` otherwise
  obtain ⟨φ, C, hφ, hexp⟩ := (hGood X).1 hGX
  obtain ⟨MX, hMX⟩ := (hXc.fderiv ℝ).exists_bound_of_continuous (hX.continuous_fderiv one_ne_zero)
  obtain ⟨η, hη, hηU⟩ := hXc.isCompact.exists_cthickening_subset_open hU hXU
  obtain ⟨G, hG⟩ : ∃ G : ℝ → Prop, ∀ t, G t ↔ (ContDiff ℝ 1 (φ t) ∧
      (∀ x, x ∉ tsupport X → φ t x = x) ∧ MapsTo (φ t) N N ∧ ∀ x, ‖φ t x - x‖ ≤ C * |t|) ∧
      (∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤
        1 / 4 * |t|) ∧ |t| * 1 < 1 ∧ |t| * MX < 1 / 4 ∧ |t| * C < η := ⟨_, fun _ => Iff.rfl⟩
  have hGev : ∀ᶠ t in 𝓝 (0:ℝ), G t := by
    filter_upwards [hφ, hexp (1 / 4) (by norm_num), hev 1 1 one_pos, hev MX (1 / 4) (by norm_num),
      hev C η hη] with t h1 h2 h3 h4 h5
    exact (hG t).2 ⟨h1, h2, h3, h4, h5⟩
  refine ⟨fun t => if G t then φ t else id, fun t => ?_, fun ε hε => ?_⟩
  · by_cases ht : G t
    · simp only [ht, ↓reduceIte]
      obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8⟩ := (hG t).1 ht
      have hD : ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P)‖ ≤ 1 / 2 := by
        intro x
        have hx := (norm_le_norm_add_norm_sub' (fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ _)
          (t • fderiv ℝ X x)).trans (add_le_add le_rfl (h5 x))
        rw [norm_smul, Real.norm_eq_abs] at hx
        have := mul_le_mul_of_nonneg_left (hMX x) (abs_nonneg t)
        linarith only [hx, this, h6, h7]
      have hdiff : Differentiable ℝ (φ t) := h1.differentiable one_ne_zero
      have happrox : ApproximatesLinearOn (φ t)
          ((ContinuousLinearEquiv.refl ℝ (Euclid P) : Euclid P ≃L[ℝ] Euclid P) :
            Euclid P →L[ℝ] Euclid P) univ (1 / 2 : NNReal) := by
        intro x _ y _
        have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := φ t)
          (φ := ContinuousLinearMap.id ℝ (Euclid P)) (s := univ)
          (fun z _ => (hdiff z).hasFDerivAt.hasFDerivWithinAt) (fun z _ => hD z) convex_univ
          (mem_univ y) (mem_univ x)
        simpa using this
      have hc : Subsingleton (Euclid P) ∨ (1 / 2 : NNReal) <
          ‖(((ContinuousLinearEquiv.refl ℝ (Euclid P)).symm : Euclid P ≃L[ℝ] Euclid P) :
            Euclid P →L[ℝ] Euclid P)‖₊⁻¹ := by
        rcases subsingleton_or_nontrivial (Euclid P) with h | h
        · exact Or.inl h
        · right; simp; norm_num
      refine ⟨h1, ⟨injOn_univ.1 (happrox.injOn hc), happrox.surjective hc⟩, fun x v w hvw => ?_,
        h2, fun x hx => ⟨h3 hx.1, ?_⟩⟩
      · have h0 := (fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ _).le_of_opNorm_le (hD x) (v - w)
        rw [sub_apply, map_sub, hvw, sub_self, zero_sub, norm_neg,
          ContinuousLinearMap.id_apply] at h0
        exact sub_eq_zero.1 (norm_le_zero_iff.1 (by linarith only [h0, norm_nonneg (v - w)]))
      · by_cases hxK : x ∈ tsupport X
        · refine hηU (mem_cthickening_of_dist_le _ x _ _ hxK ?_)
          rw [dist_eq_norm]
          exact (h4 x).trans (by rw [mul_comm]; exact h8.le)
        · rw [h2 x hxK]; exact hx.2
    · simp only [ht, ↓reduceIte]
      refine ⟨contDiff_id, bijective_id, fun x => ?_, fun x _ => rfl, fun x hx => hx⟩
      rw [fderiv_id]; exact injective_id
  · obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff.1 (hGev.and (hexp ε hε))
    refine ⟨δ, hδ, fun t ht x => ?_⟩
    obtain ⟨hGt, h2⟩ := h (show dist t 0 < δ by rwa [Real.dist_eq, sub_zero])
    simp only [hGt, ↓reduceIte]
    exact h2 x

/-- **First variation bound for the mass of a deformation** (Simon Ch. 4, 2.2; Ch. 2, 5.2–5.3).
Let `R = (M, θ, ξ)`, `μ_V(W) = ∫_{M ∩ W} θ dHⁿ < ∞`, `X ∈ C¹_c` with `spt X ⊆ W`, and let `φₜ` be
`C¹` maps with `φₜ = id` off `spt X` and `‖Dφₜ − I − t DX‖ ≤ ε|t|` for small `|t|`.  If `S` acts by
`S(ω) = ∫_M θ ⟨ω(φₜx) ∘ Dφₜ(x), ξ(x)⟩ dHⁿ`, then `M_W(S) ≤ μ_V(W) + t δV(X) + ε|t|` for small `|t|`.
At a.e. `x ∈ M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal basis `τ` of `TₓM` and
`div_M X(x) = Σₐ τₐ · DX(x)τₐ`, so on `W` the integrand is at most
`θ |ω|_E det(Dφₜτᵢ · Dφₜτⱼ)^{1/2} ≤ θ (1 + t div_M X + ε'|t|)`, `ε' = ε/(μ_V(W) + 1)`; off `W`,
`φₜ x = x ∉ spt ω` and the integrand vanishes.  Integrate (a non-integrable integrand has integral
`0` and the bound is nonnegative) and take the supremum over admissible `ω`. -/
theorem Submission.pushforward_action_massOn_le_first_variation : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P) (φ : ℝ → Euclid P → Euclid P), IsOpen W → R.measure W ≠ ∞ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → (∀ t, ContDiff ℝ 1 (φ t)) → (∀ t x, x ∉ tsupport X → φ t x = x) → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ x, ‖fderiv ℝ (φ t) x - ContinuousLinearMap.id ℝ (Euclid P) - t • fderiv ℝ X x‖ ≤ ε * |t|) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ S : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap (fderiv ℝ (φ t) x)) ∂μHE[n]) → S.massOn W ≤ ENNReal.ofReal ((R.measure W).toReal + t * R.firstVariation X + ε * |t|) := by
  intro P n U W R X φ hWo hRW hX hXc hXW _hφ hφid hφD ε hε
  classical
  have hDXc : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X = trace(p_{TₓM} ∘ DX)` is a.e. strongly measurable: `p_{TₓM}` is (TM) and the trace
  -- of a composition is continuous
  have hdvm : AEStronglyMeasurable (tangentialDivergence n R.carrier X)
      (μHE[n].restrict R.carrier) := by
    have h1 : Continuous fun L : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) L.toLinearMap :=
      ((LinearMap.trace ℝ (Euclid P)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    have h2 : Continuous fun pL : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
        LinearMap.trace ℝ (Euclid P) (pL.1.comp pL.2).toLinearMap :=
      h1.comp (continuous_fst.clm_comp continuous_snd)
    have h3 : Continuous fun pL : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
        LinearMap.trace ℝ (Euclid P) (pL.1.toLinearMap ∘ₗ pL.2.toLinearMap) := by
      simpa only [ContinuousLinearMap.toLinearMap_comp] using h2
    have hq := (Submission.imrep_approxTangent_starProjection_aesm P n U R).prodMk
      hDXc.aestronglyMeasurable
    have hr := h3.comp_aestronglyMeasurable hq
    exact hr
  set μ : Measure (Euclid P) := μHE[n].restrict R.carrier
  set θ : Euclid P → ℝ := fun x => (R.mult x : ℝ) with hθ
  set dv : Euclid P → ℝ := tangentialDivergence n R.carrier X
  set m : ℝ := (R.measure W).toReal with hm
  have hθ0 : ∀ x, 0 ≤ θ x := fun x => Nat.cast_nonneg _
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  -- `A` bounds `‖DX‖`: `DX` is continuous with compact support
  obtain ⟨C, hC⟩ := hDXc.bounded_above_of_compact_support (hXc.fderiv ℝ)
  set A : ℝ := max C 0
  have hA0 : 0 ≤ A := le_max_right _ _
  have hDXA : ∀ x, ‖fderiv ℝ X x‖ ≤ A := fun x => (hC x).trans (le_max_left _ _)
  -- constants: `ε' = ε / (m + 1)`; `η, δ₁` from the Jacobian bound at `(A, ε')`; `δ₂` from the
  -- hypothesis on `Dφₜ` at `η`
  set ε' : ℝ := ε / (m + 1) with hε'
  have hε'0 : 0 < ε' := div_pos hε (by linarith)
  obtain ⟨η, hη, δ₁, hδ₁, hJ⟩ :=
    Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order P n A ε' hA0 hε'0
  obtain ⟨δ₂, hδ₂, hD⟩ := hφD η hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht S hS => ?_⟩
  have ht₁ : |t| < δ₁ := ht.trans_le (min_le_left _ _)
  have ht₂ : |t| < δ₂ := ht.trans_le (min_le_right _ _)
  -- `θ 1_W` is integrable with integral `m`: `∫_{M ∩ W} θ dHⁿ = μ_V(W) < ∞`
  have hWm : MeasurableSet W := hWo.measurableSet
  have hθm : Measurable θ :=
    (measurable_from_nat (f := (Nat.cast : ℕ → ℝ))).comp R.measurable_mult
  have hRW' : R.measure W = ∫⁻ x in W, (R.mult x : ℝ≥0∞) ∂μ := withDensity_apply _ hWm
  have hθW : Integrable (W.indicator θ) μ := by
    rw [integrable_indicator_iff hWm]
    have := integrable_toReal_of_lintegral_ne_top (μ := μ.restrict W)
      (f := fun x => (R.mult x : ℝ≥0∞))
      ((measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp R.measurable_mult).aemeasurable
      (hRW' ▸ hRW)
    simpa [IntegrableOn, hθ] using this
  have hmW : ∫ x, W.indicator θ x ∂μ = m := by
    rw [integral_indicator hWm, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hθ0)
      hθm.aestronglyMeasurable, hm, hRW']
    simp only [hθ, ENNReal.ofReal_natCast]
  -- fix an admissible form `ω`; `g` is the integrand of `S(ω)` and `h` its majorant
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hS ω]
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℝ, g = fun x => (R.mult x : ℝ) * R.orient x
      (((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap
        (fderiv ℝ (φ t) x)) := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : Euclid P → ℝ,
      h = fun x => W.indicator θ x * (1 + ε' * |t|) + t * (θ x * dv x) := ⟨_, rfl⟩
  -- pointwise bounds at the a.e. points where `ξ(x)` orients `TₓM`
  have key : ∀ᵐ x ∂μ,
      g x ≤ h x ∧ 0 ≤ h x ∧ ‖θ x * dv x‖ ≤ ((n : ℝ) * A) * W.indicator θ x := by
    filter_upwards [Submission.fvmb_imrep_ae_unitOrientation_approxTangentPlane P n U R]
      with x hx
    obtain ⟨τ, hτ, hspan, hsign⟩ := hx
    -- `div_M X(x) = Σₐ τₐ · DX(x)τₐ`, hence `|div_M X(x)| ≤ nA`
    have hdvx : dv x = ∑ a, inner ℝ (τ a) (fderiv ℝ X x (τ a)) :=
      Submission.fvmb_trace_starProjection_comp_eq_sum_inner P n _ τ (fderiv ℝ X x) hτ hspan
    have hdvA : |dv x| ≤ n * A := by
      rw [hdvx]
      calc |∑ a, inner ℝ (τ a) (fderiv ℝ X x (τ a))|
          ≤ ∑ a, |inner ℝ (τ a) (fderiv ℝ X x (τ a))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Fin n, A := Finset.sum_le_sum fun a _ => by
          calc |inner ℝ (τ a) (fderiv ℝ X x (τ a))|
              ≤ ‖τ a‖ * ‖fderiv ℝ X x (τ a)‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖τ a‖ * (‖fderiv ℝ X x‖ * ‖τ a‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
            _ ≤ A := by rw [hτ.1 a, one_mul, mul_one]; exact hDXA x
        _ = n * A := by simp
    by_cases hxW : x ∈ W
    · -- in `W`, with `β = ω(φₜx) ∘ Dφₜ(x)`:
      -- `|ξ(x)(β)| = |ω(φₜx)(Dφₜτ)| ≤ |ω|_E det(Dφₜτᵢ · Dφₜτⱼ)^{1/2} ≤ 1 + t div_M X + ε'|t|`
      obtain ⟨β, hβ⟩ : ∃ β : Covector (Euclid P) n,
          β = ((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap
            (fderiv ℝ (φ t) x) := ⟨_, rfl⟩
      have hξ : |R.orient x β| =
          |(ω : DifferentialForm (Euclid P) n) (φ t x) fun i => fderiv ℝ (φ t) x (τ i)| := by
        rcases hsign with hs | hs
        · rw [hs, hβ, ContinuousAlternatingMap.compContinuousLinearMap_apply]
          rfl
        · rw [hs, abs_neg, hβ, ContinuousAlternatingMap.compContinuousLinearMap_apply]
          rfl
      have hJx := hJ t ht₁ (fderiv ℝ X x) (fderiv ℝ (φ t) x) (hDXA x) (hD t ht₂ x) τ hτ
      rw [← hdvx] at hJx
      have hbound : |R.orient x β| ≤ 1 + t * dv x + ε' * |t| := by
        rw [hξ]
        refine ((Submission.covectorEuclideanNorm_gram_bounds P n).1 _ _).trans ?_
        exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) (hω1 _)).trans hJx
      have hgx : g x = θ x * R.orient x β := by
        rw [hg, hβ]
      have hhx : h x = θ x * (1 + t * dv x + ε' * |t|) := by
        simp only [hh, Set.indicator_of_mem hxW]
        ring
      refine ⟨?_, ?_, ?_⟩
      · rw [hgx, hhx]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hbound) (hθ0 x)
      · rw [hhx]
        exact mul_nonneg (hθ0 x) ((abs_nonneg _).trans hbound)
      · rw [Set.indicator_of_mem hxW, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hθ0 x)]
        calc θ x * |dv x| ≤ θ x * (n * A) := mul_le_mul_of_nonneg_left hdvA (hθ0 x)
          _ = n * A * θ x := by ring
    · -- off `W`: `x ∉ spt X`, so `DX(x) = 0` and `φₜ x = x ∉ spt ω`
      have hxX : x ∉ tsupport X := fun hx => hxW (hXW hx)
      have hdv0 : dv x = 0 := by
        rw [hdvx, fderiv_of_notMem_tsupport ℝ hxX]
        simp
      have hω0 : (ω : DifferentialForm (Euclid P) n) (φ t x) = 0 := by
        rw [hφid t x hxX]
        exact image_eq_zero_of_notMem_tsupport fun hx => hxW (hωW hx)
      have hz : (0 : Covector (Euclid P) n).compContinuousLinearMap (fderiv ℝ (φ t) x) = 0 := by
        ext v
        simp
      have hg0 : g x = 0 := by
        simp only [hg, hω0, hz, map_zero, mul_zero]
      have hh0 : h x = 0 := by
        simp only [hh, Set.indicator_of_notMem hxW, hdv0, zero_mul, mul_zero, add_zero]
      refine ⟨by rw [hg0, hh0], by rw [hh0], ?_⟩
      rw [hdv0, Set.indicator_of_notMem hxW]
      simp
  -- integrate: `∫ g ≤ ∫ h = m (1 + ε'|t|) + t δV(X)` and `m ε' ≤ ε`
  have hθdv : Integrable (fun x => θ x * dv x) μ :=
    (hθW.const_mul ((n : ℝ) * A)).mono' (hθm.aestronglyMeasurable.mul hdvm)
      (key.mono fun x hx => hx.2.2)
  have hhint : Integrable h μ := by
    rw [hh]
    exact (hθW.mul_const _).add (hθdv.const_mul t)
  have hint_h : ∫ x, h x ∂μ = m * (1 + ε' * |t|) + t * R.firstVariation X := by
    simp only [hh]
    rw [integral_add (hθW.mul_const _) (hθdv.const_mul t), integral_mul_const,
      integral_const_mul, hmW]
    rfl
  have hgh : ∫ x, g x ∂μ ≤ ∫ x, h x ∂μ := by
    by_cases hgi : Integrable g μ
    · exact integral_mono_ae hgi hhint (key.mono fun x hx => hx.1)
    · rw [integral_undef hgi]
      exact integral_nonneg_of_ae (key.mono fun x hx => hx.2.1)
  have hεm : m * ε' ≤ ε := by
    rw [hε', mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hεm' : m * ε' * |t| ≤ ε * |t| := mul_le_mul_of_nonneg_right hεm (abs_nonneg t)
  calc ∫ x, (R.mult x : ℝ) * R.orient x
        (((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap
          (fderiv ℝ (φ t) x)) ∂μ = ∫ x, g x ∂μ := by rw [hg]
    _ ≤ ∫ x, h x ∂μ := hgh
    _ = m * (1 + ε' * |t|) + t * R.firstVariation X := hint_h
    _ = m + t * R.firstVariation X + m * ε' * |t| := by ring
    _ ≤ m + t * R.firstVariation X + ε * |t| := by linarith

/-- **Simon 7.1.2, first claim (pp. 181–182).**  If `T ∈ 𝒟ₙ(U)` is minimizing in `N ∩ U`
(`N` an embedded `C²` submanifold, `(N̄ \ N) ∩ U = ∅`), `∂T = 0` in `U`, and `T = τ(M, θ, ξ)` with
`Hⁿ(M \ N) = 0`, then `V = v(M, θ)` is stationary in `N ∩ U`.  Fix `X` tangent to `N` and an
open `W ⊂⊂ U` containing `spt X`.  If `μ_V(W) = 0`, then `div_M X = 0` `μ_V`-a.e.  Otherwise the
deformations `φ_t` push `T` forward to competitors with `spt(φ_{t#}T − T) ⊆ spt X ∩ N`, so
`μ_V(W) ≤ M_W(φ_{t#}T) ≤ μ_V(W) + t δV(X) + ε|t|` for all small `t` of both signs, which forces
`δV(X) = 0`.  No separate case `n = 0` is needed, since `∂S = ∂T` is vacuous there. -/
theorem Submission.stationaryAlong_of_minimizing_in_submanifold :
    ∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n),
      IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ →
      IsMinimizingIn T (N ∩ U) → BoundaryVanishes T → R.Represents T →
      μHE[n] (R.carrier \ N) = 0 → R.IsStationaryAlong N := by
  intro P n d U N T R hU hN hNU hmin hT hR hMN X hX hXc hXU hXN
  -- `∂S₁ = 0 = ∂S₂` gives `∂S₁ = ∂S₂` (vacuous in degree `0`).
  have hsame : ∀ {m : ℕ} (S₁ S₂ : GeometricCurrentOn U m), BoundaryVanishes S₁ →
      BoundaryVanishes S₂ → SameBoundary S₁ S₂ := by
    intro m S₁ S₂ h₁ h₂
    cases m with
    | zero => trivial
    | succ m => exact (show S₁.boundary = 0 from h₁).trans (show S₂.boundary = 0 from h₂).symm
  -- An open `W ⊂⊂ U` containing `K = spt X`, with `μ_V(W) < ∞` and `M_W(T) = μ_V(W)`.
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hXc hU hXU
  have hWm : MeasurableSet W := hWo.measurableSet
  have hRW : R.measure W = ∫⁻ x in W, (R.mult x : ℝ≥0∞) ∂(μHE[n].restrict R.carrier) := by
    rw [IMRep.measure, withDensity_apply _ hWm]
  have hRWfin : R.measure W ≠ ∞ := by
    rw [hRW, Measure.restrict_restrict hWm]
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult _ hWc hWU) (lintegral_mono_set ?_)
    exact fun x hx => ⟨hx.2, subset_closure hx.1⟩
  have hTW : T.massOn W = R.measure W :=
    Submission.imrep_represents_massOn_eq_measure P n U W T R hU hR hWo
      (subset_closure.trans hWU)
  -- If `μ_V(W) = 0`, then `Hⁿ(M ∩ W) = 0` and `DX = 0` off `W`, so `div_M X = 0` a.e. on `M`.
  by_cases hW0 : R.measure W = 0
  · have hMW : μHE[n].restrict R.carrier W = 0 := by
      refine le_antisymm ?_ bot_le
      calc μHE[n].restrict R.carrier W
          = ∫⁻ _ in W, 1 ∂(μHE[n].restrict R.carrier) := (setLIntegral_one W).symm
        _ ≤ ∫⁻ x in W, (R.mult x : ℝ≥0∞) ∂(μHE[n].restrict R.carrier) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae (ae_restrict_mem R.measurableSet_carrier)] with x hx
          exact Nat.one_le_cast.2 (R.mult_pos x hx)
        _ = 0 := by rw [← hRW, hW0]
    rw [IMRep.firstVariation]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hMW] with x hx
    have hDX : fderiv ℝ X x = 0 := fderiv_of_notMem_tsupport ℝ fun h => hx (hKW h)
    simp [tangentialDivergence, hDX]
  have hm : 0 < (R.measure W).toReal := ENNReal.toReal_pos hW0 hRWfin
  -- The deformations `φ_t` along `N`, fixing `ℝᴾ \ K` pointwise.
  obtain ⟨φ, hφ, hφD⟩ :=
    Submission.tangential_c1_deformation_exists P d U N X hU hN hNU hX hXc hXU hXN
  -- `K ∩ N = K ∩ N̄` is compact, since `(N̄ \ N) ∩ U = ∅` and `K ⊆ U`.
  have hKNc : IsCompact (tsupport X ∩ N) := by
    have h : tsupport X ∩ N = tsupport X ∩ closure N := by
      refine Subset.antisymm (inter_subset_inter_right _ subset_closure) ?_
      rintro x ⟨hxK, hxN⟩
      refine ⟨hxK, ?_⟩
      by_contra h
      exact hNU.subset ⟨⟨hxN, h⟩, hXU hxK⟩
    rw [h]
    exact hXc.inter_right isClosed_closure
  -- Every push-forward `φ_{t#}T` is an admissible competitor in 7.1.1, so `μ_V(W) ≤ M_W(φ_{t#}T)`.
  have hcomp : ∀ (t : ℝ) (S : GeometricCurrentOn U n), IsIntegerMultiplicity S →
      BoundaryVanishes S →
      (∀ ω : TestFormOn U n, S ω = ∫ x in R.carrier, (R.mult x : ℝ) *
        R.orient x (((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap
          (fderiv ℝ (φ t) x)) ∂μHE[n]) →
      R.measure W ≤ S.massOn W := by
    intro t S hSi hSb hSω
    -- `φ_t` is injective and fixes `ℝᴾ \ K` pointwise, so it maps `K` into `K`.
    have hφK : ∀ x ∈ tsupport X, φ t x ∈ tsupport X := by
      intro x hx
      by_contra h
      have hfix : φ t x = x := (hφ t).2.1.1 ((hφ t).2.2.2.1 _ h)
      exact h (by rwa [hfix])
    -- `spt(φ_{t#}T − T) ⊆ K ∩ N`: near `y ∉ K ∩ N` the integrands agree `Hⁿ`-a.e. on `M`.
    have hsub : (S - T).support ⊆ tsupport X ∩ N := by
      intro y hy
      by_contra hyKN
      obtain ⟨ε, hε, hεU⟩ :=
        Metric.isOpen_iff.1 (hU.inter hKNc.isClosed.isOpen_compl) y ⟨hy.1, hyKN⟩
      have hcl : closure (ball y (ε / 2)) ⊆ ball y ε :=
        closure_ball_subset_closedBall.trans (closedBall_subset_ball (half_lt_self hε))
      have hball : ball y (ε / 2) ∈ {V : Set (Euclid P) | IsOpen V ∧ IsCompact (closure V) ∧
          closure V ⊆ U ∧ (S - T).VanishesOn V} := by
        refine ⟨isOpen_ball,
          (isCompact_closedBall y (ε / 2)).closure_of_subset ball_subset_closedBall,
          fun z hz => (hεU (hcl hz)).1, ?_⟩
        intro ω hω
        have hω0 : ∀ z ∈ tsupport X ∩ N, (ω : DifferentialForm (Euclid P) n) z = 0 :=
          fun z hz => image_eq_zero_of_notMem_tsupport fun hzω =>
            (hεU (ball_subset_ball (half_le_self hε.le) (hω hzω))).2 hz
        change S ω - T ω = 0
        rw [hSω ω, hR ω, IMRep.action, sub_eq_zero]
        refine setIntegral_congr_ae R.measurableSet_carrier ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hMN] with x hxMN hxM
        have hxN : x ∈ N := by
          by_contra h
          exact hxMN ⟨hxM, h⟩
        have harg : ((ω : DifferentialForm (Euclid P) n) (φ t x)).compContinuousLinearMap
            (fderiv ℝ (φ t) x) = (ω : DifferentialForm (Euclid P) n) x := by
          by_cases hxK : x ∈ tsupport X
          · rw [hω0 x ⟨hxK, hxN⟩, hω0 (φ t x) ⟨hφK x hxK, ((hφ t).2.2.2.2 ⟨hxN, hXU hxK⟩).1⟩]
            ext v
            simp
          · have hφx : φ t =ᶠ[𝓝 x] id := by
              filter_upwards [(isClosed_tsupport X).isOpen_compl.mem_nhds hxK] with z hz
              exact (hφ t).2.2.2.1 z hz
            rw [hφx.fderiv_eq, fderiv_id, (hφ t).2.2.2.1 x hxK]
            ext v
            simp
        rw [harg]
      exact hy.2 (mem_sUnion_of_mem (mem_ball_self (half_pos hε)) hball)
    have hSTc : IsCompact (S - T).support := by
      have h : (S - T).support = (tsupport X ∩ N) ∩ ((S - T).zeroRegion)ᶜ :=
        Subset.antisymm (fun y hy => ⟨hsub hy, hy.2⟩) fun y hy => ⟨hXU hy.1.1, hy.2⟩
      rw [h]
      exact hKNc.inter_right (S - T).isOpen_zeroRegion.isClosed_compl
    rw [← hTW]
    exact hmin.2 W S hWo ⟨hWc, hWU⟩ hSi (hsame S T hSb hT) hSTc fun y hy =>
      ⟨⟨(hsub hy).2, hXU (hsub hy).1⟩, hKW (hsub hy).1⟩
  -- The expansion `M_W(φ_{t#}T) ≤ μ_V(W) + t δV(X) + ε|t|` for `|t| < δ` gives `|δV(X)| ≤ ε`.
  have hbound : ∀ ε : ℝ, 0 < ε → |R.firstVariation X| ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδS⟩ := Submission.pushforward_action_massOn_le_first_variation P n U W R X
      φ hWo hRWfin hX hXc hKW (fun t => (hφ t).1) (fun t => (hφ t).2.2.2.1) hφD ε hε
    have key : ∀ t : ℝ, |t| < δ → 0 ≤ t * R.firstVariation X + ε * |t| := by
      intro t ht
      obtain ⟨S, hSi, hSb, hSω⟩ := Submission.imrep_c1_diffeo_pushforward_im P n U
        (tsupport X) T R (φ t) hU hR hXc hXU (hφ t).1 (hφ t).2.1 (hφ t).2.2.1 (hφ t).2.2.2.1
      have h := (ENNReal.ofReal_toReal hRWfin).le.trans
        ((hcomp t S hSi (hSb hT) hSω).trans (hδS t ht S hSω))
      by_contra hneg
      exact not_lt.2 h ((ENNReal.ofReal_lt_ofReal_iff hm).2 (by linarith [not_le.1 hneg]))
    have h₁ := key (δ / 2) (by rw [abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)
    have h₂ := key (-(δ / 2)) (by rw [abs_neg, abs_of_pos (half_pos hδ)]; exact half_lt_self hδ)
    rw [abs_of_pos (half_pos hδ)] at h₁
    rw [abs_neg, abs_of_pos (half_pos hδ)] at h₂
    rw [abs_le]
    constructor <;> nlinarith
  by_contra ha
  have h := hbound (|R.firstVariation X| / 2) (half_pos (abs_pos.2 ha))
  linarith [abs_pos.2 ha]

/-- **`TₓM ⊆ TₓN`** (Simon Ch. 3, 1.4 and Ch. 2, §4, (4.1)–(4.3); used in Ch. 4, 2.6–2.7).  Let
`N` be an embedded `C¹` `d`-dimensional submanifold, `Hⁿ(M \ N) = 0` and `x ∈ N`.  Then every
approximate tangent plane `Q` of `M` at `x` lies in `TₓN`.  Write `x = ψ(v)` for a chart `ψ` of
`N` and `A = Dψ(v)`: `N` is flat at `x` along `A(ℝᵈ)` (`atsm_chart_image_flat`), hence
`Q ⊆ A(ℝᵈ)` (`atsm_approxTangent_le_of_flat`), and `A(ℝᵈ) = TₓN`
(`chart_tangentSpace_eq_range_fderiv`). -/
theorem Submission.approxTangent_le_submanifold_tangentSpace : ∀ (P n d : ℕ) (N M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), IsEmbeddedSubmanifold 1 d N → x ∈ N → μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → (Q : Set (Euclid P)) ⊆ tangentSpace N x := by
  intro P n d N M x Q hN hxN hnull hQ
  -- a chart `ψ : V → W ∩ N` of `N` around `x`, and `v ∈ V` with `ψ v = x`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, himg, hprop, hDψ⟩ := hN x hxN
  obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := by
    rw [himg]
    exact ⟨hxW, hxN⟩
  -- `N` is flat at `ψ v` along `A(ℝᵈ)`, `A = Dψ(v)`
  have hflat : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z (ψ v) < ρ →
      ∃ t ∈ LinearMap.range (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P),
        ‖z - ψ v - t‖ ≤ ε * ‖z - ψ v‖ := by
    intro ε hε
    obtain ⟨ρ, hρ, hρN⟩ := Submission.atsm_chart_image_flat P d N W V ψ v hV hW
      (by exact_mod_cast hψ) hinj himg hprop (hDψ v hv) hv ε hε
    refine ⟨ρ, hρ, fun z hz hzρ => ?_⟩
    obtain ⟨h, hh⟩ := hρN z hz hzρ
    exact ⟨_, LinearMap.mem_range_self (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P) h, hh⟩
  -- hence `Q ⊆ A(ℝᵈ)`, and `A(ℝᵈ) = T_{ψ v}N`
  have hQA := Submission.atsm_approxTangent_le_of_flat P n N M (ψ v) Q _ hnull hflat hQ
  rw [Submission.chart_tangentSpace_eq_range_fderiv P d 1 N W V ψ v le_rfl hV hW hψ hinj himg
    hprop hDψ hv]
  intro w hw
  exact LinearMap.mem_range.1 (hQA hw)

/-- **Simon Ch. 2, §4** (4.1–4.3 and the definition of `Cˡ` functions on `M`): the tangent
projection `z ↦ P_{T_zN}` of an embedded `C²` submanifold `N ⊆ ℝᴾ` is `C¹` on `N`, i.e. it is the
restriction to `N` of a map that is `C¹` on an open `O ⊇ N`.  Along a chart `ψ`,
`T_{ψ(v)}N = range Dψ(v)` (`Submission.chart_tangentSpace_eq_range_fderiv`), and the projection
onto `range L` is `L (L*L)⁻¹ L*`, a smooth function of `L` near each injective `L`.  The inverse
function theorem for `Λ ∘ ψ`, `Λ` a left inverse of `Dψ(v₀)`, gives a `C¹` left inverse `φ` of
`ψ` on an open subset of `ℝᴾ`; by 4.2 (`ψ` is proper, so a homeomorphism onto `W ∩ N`),
`φ ∘ ψ = id` on all of `N` near `ψ(v₀)`, so `y ↦ P_{range Dψ(φ(y))}` extends `P_N` near `ψ(v₀)`.
A smooth partition of unity on the union `O` of these neighbourhoods glues the local
extensions. -/
theorem Submission.submanifold_tangentProjection_c1_extension : ∀ (P d : ℕ) (N : Set (Euclid P)), IsEmbeddedSubmanifold 2 d N → ∃ (O : Set (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)), IsOpen O ∧ N ⊆ O ∧ ContDiffOn ℝ 1 pr O ∧ ∀ z ∈ N, pr z = (Submodule.span ℝ (tangentSpace N z)).starProjection := by
  intro P d N hN
  classical
  -- Step 1: `L ↦ P_{range L} = L (L*L)⁻¹ L*` is `C¹` near every injective `L₀`.
  have hproj : ∀ L₀ : Euclid d →L[ℝ] Euclid P, Injective L₀ →
      ContDiffAt ℝ 1 (fun L : Euclid d →L[ℝ] Euclid P =>
        (LinearMap.range (L : Euclid d →ₗ[ℝ] Euclid P)).starProjection) L₀ := by
    intro L₀ hL₀
    -- the adjoint `L ↦ L*`, as an `ℝ`-linear continuous map
    let adj : (Euclid d →L[ℝ] Euclid P) →L[ℝ] (Euclid P →L[ℝ] Euclid d) :=
      { toFun := fun L => ContinuousLinearMap.adjoint L
        map_add' := fun A B => map_add _ A B
        map_smul' := fun c A => by simp
        cont := ContinuousLinearMap.adjoint.continuous }
    have hadj : ∀ L, adj L = ContinuousLinearMap.adjoint L := fun _ => rfl
    -- the Gram operator `L*L` is invertible at `L₀`
    let G : (Euclid d →L[ℝ] Euclid P) → (Euclid d →L[ℝ] Euclid d) := fun L => adj L ∘L L
    have hG : ContDiff ℝ 1 G := adj.contDiff.clm_comp contDiff_id
    have hGunit : IsUnit (G L₀) := by
      have hinj : Injective (G L₀) := by
        intro x y hxy
        have h0 : G L₀ (x - y) = 0 := by simp [map_sub, hxy]
        have h1 : inner ℝ (L₀ (x - y)) (L₀ (x - y)) = 0 := by
          have := congrArg (fun z => inner ℝ z (x - y)) h0
          simpa only [G, ContinuousLinearMap.coe_comp, comp_apply, hadj,
            ContinuousLinearMap.adjoint_inner_left, inner_zero_left] using this
        have h2 : L₀ (x - y) = L₀ 0 := by rw [inner_self_eq_zero.1 h1, map_zero]
        exact sub_eq_zero.1 (hL₀ h2)
      rw [ContinuousLinearMap.isUnit_iff_bijective]
      refine ⟨hinj, ?_⟩
      simpa using (LinearMap.injective_iff_surjective
        (f := (G L₀ : Euclid d →ₗ[ℝ] Euclid d))).1 hinj
    let Γ : (Euclid d →L[ℝ] Euclid P) → (Euclid P →L[ℝ] Euclid P) :=
      fun L => L ∘L (Ring.inverse (G L) ∘L adj L)
    have hinv : ContDiffAt ℝ 1 (fun L => Ring.inverse (G L)) L₀ := by
      have h := contDiffAt_ringInverse ℝ (n := 1) hGunit.unit
      rw [IsUnit.unit_spec] at h
      exact h.comp L₀ hG.contDiffAt
    have hΓ : ContDiffAt ℝ 1 Γ L₀ :=
      contDiffAt_id.clm_comp (hinv.clm_comp adj.contDiff.contDiffAt)
    -- `Γ L = P_{range L}` wherever `L*L` is invertible, in particular near `L₀`
    have hev : ∀ᶠ L in 𝓝 L₀, IsUnit (G L) :=
      hG.continuous.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hGunit)
    refine hΓ.congr_of_eventuallyEq ?_
    filter_upwards [hev] with L hL
    ext1 x
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ⟨_, rfl⟩ ?_
    rintro w ⟨a, rfl⟩
    have hcancel : G L (Ring.inverse (G L) (adj L x)) = adj L x := by
      have := congrArg (fun T : Euclid d →L[ℝ] Euclid d => T (adj L x))
        (Ring.mul_inverse_cancel (G L) hL)
      simpa [mul_apply_eq_comp] using this
    -- `L*(x - Γ L x) = 0`, i.e. `x - Γ L x ⊥ range L`
    have hperp : adj L (x - Γ L x) = 0 := by
      have : adj L (Γ L x) = G L (Ring.inverse (G L) (adj L x)) := rfl
      rw [map_sub, this, hcancel, sub_self]
    have : inner ℝ (x - Γ L x) (L a) = inner ℝ (adj L (x - Γ L x)) a := by
      rw [hadj, ContinuousLinearMap.adjoint_inner_left]
    rw [ContinuousLinearMap.coe_coe, this, hperp, inner_zero_left]
  -- Step 2: a `C¹` left inverse, defined on an open subset of `ℝᴾ`, of a `C¹` immersion `ψ`
  -- near `v₀`: the inverse function theorem for `Λ ∘ ψ`, `Λ` a left inverse of `Dψ(v₀)`.
  have hlinv : ∀ (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen V →
      ContDiffOn ℝ 1 ψ V → v₀ ∈ V → Injective (fderiv ℝ ψ v₀) →
      ∃ (O : Set (Euclid P)) (φ : Euclid P → Euclid d) (ε : ℝ), 0 < ε ∧ IsOpen O ∧
        ContDiffOn ℝ 1 φ O ∧ MapsTo φ O V ∧
        ∀ v : Euclid d, dist v v₀ < ε → v ∈ V ∧ ψ v ∈ O ∧ φ (ψ v) = v := by
    intro V ψ v₀ hV hψ hv₀ hinj
    obtain ⟨Λl, hΛl⟩ := LinearMap.exists_leftInverse_of_injective
      (fderiv ℝ ψ v₀ : Euclid d →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.2 hinj)
    let Λ : Euclid P →L[ℝ] Euclid d := LinearMap.toContinuousLinearMap Λl
    have hΛ : ∀ x, Λ (fderiv ℝ ψ v₀ x) = x := fun x => by
      simpa [Λ] using LinearMap.congr_fun hΛl x
    have hid : Λ ∘L fderiv ℝ ψ v₀ = ContinuousLinearMap.id ℝ (Euclid d) := by
      ext1 x
      simp [hΛ]
    let χ : Euclid d → Euclid d := fun v => Λ (ψ v)
    have hψat : ∀ v ∈ V, ContDiffAt ℝ 1 ψ v := fun v hv => hψ.contDiffAt (hV.mem_nhds hv)
    have hχat : ∀ v ∈ V, ContDiffAt ℝ 1 χ v := fun v hv =>
      Λ.contDiff.contDiffAt.comp v (hψat v hv)
    have hχderiv : ∀ v ∈ V, HasFDerivAt χ (Λ ∘L fderiv ℝ ψ v) v := fun v hv =>
      Λ.hasFDerivAt.comp v ((hψat v hv).differentiableAt one_ne_zero).hasFDerivAt
    -- the open set where `D(Λ ∘ ψ)` is invertible
    let D : Set (Euclid d) := V ∩ (fun v => Λ ∘L fderiv ℝ ψ v) ⁻¹' {A | IsUnit A}
    have hDopen : IsOpen D :=
      (continuousOn_const.clm_comp
        (hψ.continuousOn_fderiv_of_isOpen hV le_rfl)).isOpen_inter_preimage hV Units.isOpen
    have hv₀D : v₀ ∈ D :=
      ⟨hv₀, show IsUnit (Λ ∘L fderiv ℝ ψ v₀) by rw [hid]; exact isUnit_one⟩
    -- the inverse function theorem for `χ = Λ ∘ ψ` at `v₀`, where `Dχ(v₀) = id`
    have hstrict : HasStrictFDerivAt χ
        ((ContinuousLinearEquiv.refl ℝ (Euclid d) : Euclid d ≃L[ℝ] Euclid d) :
          Euclid d →L[ℝ] Euclid d) v₀ := by
      refine (hχat v₀ hv₀).hasStrictFDerivAt' ?_ one_ne_zero
      have := hχderiv v₀ hv₀
      rw [hid] at this
      exact this
    let h := hstrict.toOpenPartialHomeomorph χ
    have hcoe : (h : Euclid d → Euclid d) = χ := rfl
    let S := h.source ∩ D
    have hSopen : IsOpen S := h.open_source.inter hDopen
    have hv₀S : v₀ ∈ S := ⟨hstrict.mem_toOpenPartialHomeomorph_source, hv₀D⟩
    let T := h.target ∩ h.symm ⁻¹' S
    have hTopen : IsOpen T := h.isOpen_inter_preimage_symm hSopen
    -- `h⁻¹` is `C¹` on `T`, where the derivative of `h` is invertible
    have hsymm : ∀ t ∈ T, ContDiffAt ℝ 1 h.symm t := by
      intro t ht
      have hs : h.symm t ∈ S := ht.2
      obtain ⟨u, hu⟩ := hs.2.2
      apply h.contDiffAt_symm ht.1 (f₀' := ContinuousLinearEquiv.unitsEquiv ℝ (Euclid d) u)
      · have he : ((ContinuousLinearEquiv.unitsEquiv ℝ (Euclid d) u : Euclid d ≃L[ℝ] Euclid d) :
            Euclid d →L[ℝ] Euclid d) = Λ ∘L fderiv ℝ ψ (h.symm t) := by
          ext1 x
          simp [ContinuousLinearEquiv.unitsEquiv_apply, hu]
        rw [he, hcoe]
        exact hχderiv _ hs.2.1
      · rw [hcoe]
        exact hχat _ hs.2.1
    obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hSopen v₀ hv₀S
    refine ⟨Λ ⁻¹' T, fun y => h.symm (Λ y), ε, hε, hTopen.preimage Λ.continuous, ?_, ?_, ?_⟩
    · intro y hy
      exact ((hsymm (Λ y) hy).comp y Λ.contDiff.contDiffAt).contDiffWithinAt
    · intro y hy
      exact (hy.2 : h.symm (Λ y) ∈ S).2.1
    · intro v hv
      have hvS : v ∈ S := hεS (mem_ball.2 hv)
      have hleft : h.symm (h v) = v := h.left_inv hvS.1
      refine ⟨hvS.2.1, ⟨h.map_source hvS.1, ?_⟩, hleft⟩
      show h.symm (h v) ∈ S
      rw [hleft]
      exact hvS
  -- Step 3: a proper injective chart has a continuous inverse: `ψ v` close to `ψ v₀` forces `v`
  -- close to `v₀`.
  have hprox : ∀ (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P)
      (v₀ : Euclid d), IsOpen W → ContinuousOn ψ V → InjOn ψ V →
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → ψ v₀ ∈ W →
      ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ v ∈ V, dist (ψ v) (ψ v₀) < ρ → dist v v₀ < ε := by
    intro V W ψ v₀ hW hψ hinj hprop hv₀ hv₀W ε hε
    obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW (ψ v₀) hv₀W
    -- `C = {v ∈ V : |ψ v - ψ v₀| ≤ r / 2, |v - v₀| ≥ ε}` is compact and `ψ v₀ ∉ ψ(C)`
    have hC : IsCompact ((V ∩ ψ ⁻¹' closedBall (ψ v₀) (r / 2)) ∩ (ball v₀ ε)ᶜ) :=
      (hprop _ ((closedBall_subset_ball (by linarith)).trans hrW)
        (isCompact_closedBall _ _)).inter_right isOpen_ball.isClosed_compl
    have himg := hC.image_of_continuousOn (hψ.mono fun x hx => hx.1.1)
    have hnot : ψ v₀ ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ v₀) (r / 2)) ∩ (ball v₀ ε)ᶜ) := by
      rintro ⟨w, ⟨⟨hwV, -⟩, hwb⟩, hw⟩
      exact hwb (by rw [hinj hwV hv₀ hw]; exact mem_ball_self hε)
    obtain ⟨ρ, hρ, hρC⟩ := Metric.isOpen_iff.1 himg.isClosed.isOpen_compl (ψ v₀) hnot
    refine ⟨min ρ (r / 2), lt_min hρ (by linarith), fun v hv hdist => ?_⟩
    by_contra hcon
    exact hρC (mem_ball.2 (lt_of_lt_of_le hdist (min_le_left _ _)))
      ⟨v, ⟨⟨hv, mem_closedBall.2 (lt_of_lt_of_le hdist (min_le_right _ _)).le⟩,
        fun hvb => hcon (mem_ball.1 hvb)⟩, rfl⟩
  -- Step 4: near each `p = ψ v₀ ∈ N`, `y ↦ P_{range Dψ(φ y)}` is a `C¹` extension of `P_N`.
  have hloc : ∀ p ∈ N, ∃ (U : Set (Euclid P)) (f : Euclid P → (Euclid P →L[ℝ] Euclid P)),
      IsOpen U ∧ p ∈ U ∧ ContDiffOn ℝ 1 f U ∧
        ∀ z ∈ N ∩ U, f z = (Submodule.span ℝ (tangentSpace N z)).starProjection := by
    intro p hp
    obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hinj, himg, hprop, hDψ⟩ := hN p hp
    have hpV : p ∈ ψ '' V := by rw [himg]; exact ⟨hpW, hp⟩
    obtain ⟨v₀, hv₀, rfl⟩ := hpV
    have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2))
    have hDψ1 : ContDiffOn ℝ 1 (fun v => fderiv ℝ ψ v) V := hψ.fderiv_of_isOpen hV (by norm_num)
    obtain ⟨O₁, φ, ε, hε, hO₁, hφ, hφV, hφψ⟩ := hlinv V ψ v₀ hV hψ1 hv₀ (hDψ v₀ hv₀)
    obtain ⟨ρ, hρ, hρε⟩ := hprox V W ψ v₀ hW hψ1.continuousOn hinj hprop hv₀ hpW ε hε
    refine ⟨O₁ ∩ ball (ψ v₀) ρ ∩ W,
      fun y => (LinearMap.range (fderiv ℝ ψ (φ y) : Euclid d →ₗ[ℝ] Euclid P)).starProjection,
      (hO₁.inter isOpen_ball).inter hW,
      ⟨⟨(hφψ v₀ (by simpa using hε)).2.1, mem_ball_self hρ⟩, hpW⟩, ?_, ?_⟩
    · intro y hy
      have hφy : φ y ∈ V := hφV hy.1.1
      exact ((hproj _ (hDψ _ hφy)).comp y ((hDψ1.contDiffAt (hV.mem_nhds hφy)).comp y
        (hφ.contDiffAt (hO₁.mem_nhds hy.1.1)))).contDiffWithinAt
    · rintro z ⟨hzN, ⟨hzO, hzρ⟩, hzW⟩
      have hzV : z ∈ ψ '' V := by rw [himg]; exact ⟨hzW, hzN⟩
      obtain ⟨v, hv, rfl⟩ := hzV
      -- `T_{ψ v}N = range Dψ(v)`
      have hspan : Submodule.span ℝ (tangentSpace N (ψ v)) =
          LinearMap.range (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P) := by
        rw [Submission.chart_tangentSpace_eq_range_fderiv P d 2 N W V ψ v (by norm_num) hV hW hψ
          hinj himg hprop hDψ hv, ← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range,
          Submodule.span_eq]
      show (LinearMap.range (fderiv ℝ ψ (φ (ψ v)) : Euclid d →ₗ[ℝ] Euclid P)).starProjection = _
      rw [(hφψ v (hρε v hv (mem_ball.1 hzρ))).2.2, hspan]
  -- Step 5: glue the local extensions by a smooth partition of unity on `O = ⋃ₚ Uₚ`.
  choose! U f hU hpU hf hfN using hloc
  let O : Set (Euclid P) := ⋃ p ∈ N, U p
  have hO : IsOpen O := isOpen_biUnion fun p hp => hU p hp
  have hNO : N ⊆ O := fun p hp => mem_biUnion hp (hpU p hp)
  let O' : TopologicalSpace.Opens (Euclid P) := ⟨O, hO⟩
  have : LocallyCompactSpace O' := ChartedSpace.locallyCompactSpace (Euclid P) O'
  let t : O' → Set (Euclid P →L[ℝ] Euclid P) := fun x =>
    if (x : Euclid P) ∈ N then {(Submodule.span ℝ (tangentSpace N x)).starProjection} else univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : (x : Euclid P) ∈ N
    · simp only [t, ite_eq_left hx]
      exact convex_singleton _
    · simp only [t, ite_eq_right hx]
      exact convex_univ
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local (n := 1)
    (modelWithCornersSelf ℝ (Euclid P)) ht fun x => by
      have hx : (x : Euclid P) ∈ ⋃ p ∈ N, U p := x.2
      obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx
      refine ⟨Subtype.val ⁻¹' U p,
        (continuous_subtype_val.isOpen_preimage _ (hU p hp)).mem_nhds hxp, fun y => f p y,
        fun y hy => ?_, fun y hy => ?_⟩
      · exact ContMDiffAt.contMDiffWithinAt ((contMDiffAt_subtype_iff (U := O') (f := f p)).2
          (contMDiffAt_iff_contDiffAt.2 ((hf p hp).contDiffAt ((hU p hp).mem_nhds hy))))
      · by_cases hyN : (y : Euclid P) ∈ N
        · simp only [t, ite_eq_left hyN, mem_singleton_iff]
          exact hfN p hp y ⟨hyN, hy⟩
        · simp only [t, ite_eq_right hyN, mem_univ]
  refine ⟨O, fun y => if hy : y ∈ O then g ⟨y, hy⟩ else 0, hO, hNO, fun y hy => ?_, fun z hz => ?_⟩
  · have hgy : ContMDiffAt (modelWithCornersSelf ℝ (Euclid P))
        (modelWithCornersSelf ℝ (Euclid P →L[ℝ] Euclid P)) 1
        (fun x : O' => (fun y => if hy : y ∈ O then g ⟨y, hy⟩ else 0) (x : Euclid P))
        ⟨y, hy⟩ := by
      refine (g.contMDiff ⟨y, hy⟩).congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      have hx : (x : Euclid P) ∈ O := x.2
      simp only [dite_eq_left hx]
    exact (contMDiffAt_iff_contDiffAt.1 ((contMDiffAt_subtype_iff (U := O')
      (f := fun y => if hy : y ∈ O then g ⟨y, hy⟩ else 0)).1 hgy)).contDiffWithinAt
  · have h1 := hg ⟨z, hNO hz⟩
    simp only [t, ite_eq_left hz, mem_singleton_iff] at h1
    show (if hy : z ∈ O then g ⟨z, hy⟩ else 0) = _
    rw [dite_eq_left (hNO hz)]
    exact h1

/-- **Simon Ch. 4, 2.7 and 3.14** (with Ch. 2, 5.9): if `V = v(M, θ)` is stationary in `N ∩ U`,
where `N` is an embedded `C²` submanifold with `(N̄ \ N) ∩ U = ∅` and `Hⁿ(M \ N) = 0`, then `V`
has generalized mean curvature `H` in `U`, bounded on compact subsets of `U`.  Extend
`z ↦ P_{T_zN}` to a `C¹` field `pr` on an open `O ⊇ N` and take `H` with
`H(x) = Σⱼ (Dpr(x)[p eⱼ])*(p eⱼ)` on `N ∩ U`, `p = p_{TₓM}`.  For `X ∈ C¹_c(U)`, the tangential
part `X^T` (equal to `pr·X` near `N`) is tangent to `N` on `N ∩ U`, so `δV(X^T) = 0` and
`δV(X) = δV(X − X^T)`.  At `Hⁿ`-a.e. `x ∈ M`, `x ∈ N` and `TₓM ⊆ TₓN`, so
`div_M(X − X^T)(x) = −X(x)·H(x)`; integrating against `θ` gives `δV(X) = −∫ X·H dμ_V`. -/
theorem Submission.meanCurvature_bounded_of_stationaryAlong : ∀ (P n d : ℕ) (U N : Set (Euclid P)) (R : IMRep U n), IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → μHE[n] (R.carrier \ N) = 0 → R.IsStationaryAlong N → R.HasLocallyBoundedMeanCurvature := by
  intro P n d U N R hU hN hNU hMN hstat
  -- the `C¹` extension `pr` of `z ↦ P_{T_zN}` to an open set `O ⊇ N`
  obtain ⟨O, pr, hO, hNO, hpr, hprN⟩ :=
    Submission.submanifold_tangentProjection_c1_extension P d N hN
  -- `p(x) = p_{TₓM}` is `Hⁿ⌞M`-a.e. strongly measurable, and `‖p(x)‖ ≤ 1`
  have hp : AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection)
      (μHE[n].restrict R.carrier) := Submission.imrep_approxTangent_starProjection_aesm P n U R
  -- `H` with `H(x) = Σⱼ (Dpr(x)[p eⱼ])*(p eⱼ)` on `N ∩ U`, measurable and bounded on compact
  -- subsets of `U`
  obtain ⟨H, hHm, hHb, hH⟩ := Submission.mcs_exists_meanCurvature_field P
    (μHE[n].restrict R.carrier) U N O pr _ hU hO hNO hpr hNU hp
    fun x => Submodule.starProjection_norm_le _
  -- `T_zN` is a linear subspace for `z ∈ N`, the range of `Dψ` in a chart
  have hTN : ∀ z ∈ N, ∃ T : Submodule ℝ (Euclid P), tangentSpace N z = T := by
    intro z hz
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, hψV, hproper, hDψ⟩ := hN z hz
    obtain ⟨v, hv, rfl⟩ : z ∈ ψ '' V := hψV ▸ ⟨hzW, hz⟩
    exact ⟨LinearMap.range (fderiv ℝ ψ v : Euclid d →ₗ[ℝ] Euclid P),
      Submission.chart_tangentSpace_eq_range_fderiv P d 2 N W V ψ v one_le_two hV hW hψ hinj hψV
        hproper hDψ hv⟩
  -- `C²` charts are `C¹` charts
  have hN1 : IsEmbeddedSubmanifold 1 d N := fun y hy => by
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, h⟩ := hN y hy
    exact ⟨V, W, ψ, hV, hW, hyW, hψ.of_le (by norm_num), h⟩
  -- `Hⁿ⌞M`-a.e. point lies in `N`, as `Hⁿ(M \ N) = 0`
  have hMN' : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ N := by
    rw [ae_restrict_iff' R.measurableSet_carrier]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hMN] with x hx hxM
    by_contra hxN
    exact hx ⟨hxM, hxN⟩
  refine ⟨H, hHm.mono_ac (withDensity_absolutelyContinuous _ _),
    fun K hK hKU => (hHb K hK hKU).imp fun Λ hΛ => ae_of_all _ hΛ, fun X hX hXc hXU => ?_⟩
  -- the tangential part `X^T ∈ C¹_c(U)`, equal to `pr·X` near every point of `N`
  obtain ⟨XT, hXT, hXTc, hXTU, hXTN⟩ :=
    Submission.mcs_exists_c1_field_eq_proj_near P U N O pr X hU hO hNO hpr hNU hX hXc hXU
  -- `X^T(z) = P_{T_zN} X(z) ∈ T_zN` on `N ∩ U`, so `δV(X^T) = 0` by stationarity
  have hXT0 : R.firstVariation XT = 0 := by
    refine hstat XT hXT hXTc hXTU fun z hz => ?_
    obtain ⟨T, hT⟩ := hTN z hz.1
    have hmem : XT z ∈ Submodule.span ℝ (tangentSpace N z) := by
      rw [(hXTN z hz.1).eq_of_nhds, hprN z hz.1]
      exact Submodule.starProjection_apply_mem _ _
    rw [hT, Submodule.span_eq] at hmem
    rwa [hT]
  -- `δV(X) = δV(X^T) + δV(X − X^T) = δV(X − X^T)`
  have hsplit : R.firstVariation X = R.firstVariation (X - XT) := by
    have h := Submission.mcs_firstVariation_add P n U R XT (X - XT) hp hXT hXTc hXTU (hX.sub hXT)
      (hXc.sub hXTc) ((tsupport_sub X XT).trans (union_subset hXU hXTU))
    rwa [add_sub_cancel, hXT0, zero_add] at h
  -- at `Hⁿ⌞M`-a.e. `x`: `x ∈ M ∩ N` and `TₓM ⊆ TₓN`, so `div_M(X − X^T)(x) = −X(x)·H(x)`
  have hdiv : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      tangentialDivergence n R.carrier (X - XT) x = -inner ℝ (X x) (H x) := by
    filter_upwards [ae_restrict_mem R.measurableSet_carrier, hMN', R.orients]
      with x hxM hxN ⟨Q, hQ, _⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have hTx : HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec
    have hQS : approxTangentPlane n R.carrier x ≤ Submodule.span ℝ (tangentSpace N x) :=
      fun u hu => Submodule.subset_span (Submission.approxTangent_le_submanifold_tangentSpace P n d
        N R.carrier x _ hN1 hxN hMN hTx hu)
    have hY : (X - XT) =ᶠ[𝓝 x] fun y => X y - pr y (X y) :=
      (hXTN x hxN).mono fun y hy => by rw [Pi.sub_apply, hy]
    have hprx : DifferentiableAt ℝ pr x :=
      (hpr.differentiableOn one_ne_zero).differentiableAt (hO.mem_nhds (hNO hxN))
    rw [tangentialDivergence, Submission.mcs_trace_normal_part_eq_neg_inner P _ _ pr X (X - XT) x
      hQS (hprN x hxN) hprx (hX.differentiable one_ne_zero x) hY, hH x ⟨hxN, R.carrier_subset hxM⟩]
  -- integrate against `θ`: `∫_M θ div_M(X − X^T) dHⁿ = −∫ X·H dμ_V`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
  rw [hsplit, IMRep.firstVariation, IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hdiv] with x hx
  rw [hx, ENNReal.toReal_natCast, smul_eq_mul, mul_neg]

/-- **Simon 7.1.2** (chapter-07.txt lines 29–60, with README erratum 1).  For a representation
`R = (M, θ, ξ)` of `T`, `Hⁿ(M ∖ spt T) = 0`, hence `Hⁿ(M ∖ N) = 0` because `spt T ⊆ N`.
Comparing `T` with the competitors `φ_{t#}T` of 1.2 (2), (3), where `φ_t` preserves `N ∩ U` and
is the identity off `spt X` (Ch. 4, 2.1 with `U ∩ N` in place of `U`), shows that `v(M, θ)` is
stationary in `N ∩ U`; stationarity in `N ∩ U` then gives a generalized mean curvature in `U`
that is bounded on compact sets (Ch. 4, 2.7 and 3.14).  The hypothesis `ℓ ≤ k` is not used. -/
theorem Submission.minimizing_implies_stationary : MinimizingImpliesStationary := by
  intro n k ℓ _hℓk U N T hU hN hNcl hTN hmin hbdry R hR
  -- `μ_T(U ∖ spt T) = 0` and `spt T ⊆ N`.
  have hnull : μHE[n] (R.carrier \ N) = 0 :=
    measure_mono_null (Set.sdiff_subset_sdiff_right hTN)
      (Submission.imrep_carrier_sdiff_support_null (n + k) n U T R hU hR)
  have hstat : R.IsStationaryAlong N :=
    Submission.stationaryAlong_of_minimizing_in_submanifold (n + k) n (n + ℓ) U N T R hU hN hNcl
      hmin hbdry hR hnull
  exact ⟨hstat, Submission.meanCurvature_bounded_of_stationaryAlong (n + k) n (n + ℓ) U N R hU hN
    hNcl hnull hstat⟩

/-- **Simon Ch. 3, proof of Theorem 1.6 "⇒"**, along a Lipschitz map `F : ℝᵏ → ℝᴾ`: if `Y` is
Borel with `Hᵏ(Y ∩ C) < ∞` for compact `C`, then for a.e. `u` with `F(u) ∈ Y`, `F`
differentiable at `u` and `DF(u)` injective, `Y` has approximate tangent space `DF(u)(ℝᵏ)` at
`F(u)`.  The Borel set `G` of such `u` is covered by countably many Borel pieces on which `F` is
`r(Aᵢ)`-close to some `Aᵢ = DF(yᵢ)`, where `2r(A)|w| ≤ |Aw|` for injective `A`.  Hence
`r(Aᵢ)|a − a'| ≤ |F(a) − F(a')|` on each piece, and the bi-Lipschitz piece lemma applies. -/
theorem Submission.idtp_fons_cs_sos_lipschitz_approx_tangent : ∀ (P k : ℕ) (F : Euclid k → Euclid P) (Y : Set (Euclid P)) (K : NNReal), 0 < k → LipschitzWith K F → MeasurableSet Y → (∀ C : Set (Euclid P), IsCompact C → μHE[k] (Y ∩ C) ≠ ∞) → ∀ᵐ u ∂(volume : Measure (Euclid k)), F u ∈ Y → DifferentiableAt ℝ F u → Function.Injective (fderiv ℝ F u) → HasApproximateTangentSpaceAt k Y (F u) (LinearMap.range (fderiv ℝ F u : Euclid k →ₗ[ℝ] Euclid P)) := by
  intro P k F Y K _hk hF hY hfin
  classical
  -- Step 1: the regular set `G = {u : DF(u) exists and is injective, F(u) ∈ Y}` is Borel
  set G : Set (Euclid k) :=
    ({u | DifferentiableAt ℝ F u} ∩ {u | Injective (fderiv ℝ F u)}) ∩ F ⁻¹' Y
  have hGm : MeasurableSet G :=
    ((measurableSet_of_differentiableAt ℝ F).inter
      (measurable_fderiv ℝ F ContinuousLinearMap.isOpen_injective.measurableSet)).inter
      (hF.continuous.measurable hY)
  -- Step 2: an injective `A` satisfies `c_A‖w‖ ≤ ‖Aw‖` with `c_A > 0`; tolerance `r(A) = c_A/2`
  have hlb : ∀ A : Euclid k →L[ℝ] Euclid P, Injective A →
      ∃ c : NNReal, 0 < c ∧ ∀ w, (c : ℝ) * ‖w‖ ≤ ‖A w‖ := by
    intro A hA
    obtain ⟨K', hK'pos, hK'⟩ :=
      (LinearMap.injective_iff_antilipschitz (A : Euclid k →ₗ[ℝ] Euclid P)).1 hA
    refine ⟨K'⁻¹, inv_pos.2 hK'pos, fun w => ?_⟩
    have hw := ZeroHomClass.bound_of_antilipschitz (A : Euclid k →ₗ[ℝ] Euclid P) hK' w
    have hK'r : (0 : ℝ) < K' := hK'pos
    rw [NNReal.coe_inv, inv_mul_le_iff₀ hK'r]
    simpa using hw
  choose! c hcpos hc using hlb
  let r : (Euclid k →L[ℝ] Euclid P) → NNReal := fun A => if Injective A then c A / 2 else 1
  have hr0 : ∀ A, r A ≠ 0 := by
    intro A
    simp only [r]
    split_ifs with h
    · exact (div_pos (hcpos A h) two_pos).ne'
    · exact one_ne_zero
  -- Step 3: countably many Borel pieces `G ∩ t n` on which `F` is `r(A n)`-close to `A n`
  obtain ⟨t, A, -, htm, hcov, happ, hAder⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F G (fderiv ℝ F)
      (fun u hu => hu.1.1.hasFDerivAt.hasFDerivWithinAt) r hr0
  -- Steps 4–5: on a nonempty piece, `A n = DF(y)` is injective, so `F` is bi-Lipschitz there
  -- and the bi-Lipschitz piece lemma gives the tangent planes
  have hpiece : ∀ n, ∀ᵐ u ∂(volume : Measure (Euclid k)), u ∈ G ∩ t n →
      HasApproximateTangentSpaceAt k Y (F u)
        (LinearMap.range (fderiv ℝ F u : Euclid k →ₗ[ℝ] Euclid P)) := by
    intro n
    rcases (G ∩ t n).eq_empty_or_nonempty with hB | hB
    · exact Eventually.of_forall fun u hu => by simp [hB] at hu
    obtain ⟨y, hyG, hAy⟩ := hAder (hB.mono inter_subset_left) n
    have hinj : Injective (A n) := hAy ▸ hyG.1.2
    have hrA : r (A n) = c (A n) / 2 := ite_eq_left hinj
    have hm : (0 : ℝ) < r (A n) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr0 _))
    have hbi : ∀ a ∈ G ∩ t n, ∀ a' ∈ G ∩ t n, (r (A n) : ℝ) * ‖a - a'‖ ≤ ‖F a - F a'‖ := by
      intro a ha a' ha'
      have h1 := happ n a ha a' ha'
      have h2 := hc (A n) hinj (a - a')
      have h3 : ‖A n (a - a')‖ ≤ ‖F a - F a'‖ + ‖F a - F a' - A n (a - a')‖ := by
        calc ‖A n (a - a')‖ = ‖(F a - F a') - (F a - F a' - A n (a - a'))‖ := by
              congr 1; abel
          _ ≤ ‖F a - F a'‖ + ‖F a - F a' - A n (a - a')‖ := norm_sub_le _ _
      rw [hrA] at h1 ⊢
      push_cast at h1 ⊢
      linarith
    exact (ae_restrict_iff' (hGm.inter (htm n))).1
      (Submission.dpf_approxTangent_ae_bilipschitz_piece P k univ Y F (G ∩ t n) K (r (A n))
        isOpen_univ hY (subset_univ _) (fun C hC _ => hfin C hC) hF (hGm.inter (htm n)) hm hbi
        (fun a ha => ⟨ha.1.1.1, ha.1.1.2⟩) (by rintro _ ⟨a, ha, rfl⟩; exact ha.1.2))
  -- Step 6: a.e. `u` lies in no exceptional set; a regular `u ∈ F⁻¹(Y)` lies in some piece
  filter_upwards [ae_all_iff.2 hpiece] with u hu hFu hdiff hinj
  have huG : u ∈ G := ⟨⟨hdiff, hinj⟩, hFu⟩
  obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov huG)
  exact hu n ⟨huG, hn⟩

/-- **Coarea formula for the projection onto a spine** (Federer 3.2.22 for `p = p_L` on `M`; the
splitting step behind Simon 7.3.5, chapter-07.txt lines 395–420).  Let `M ⊆ ℝᴾ` be Borel,
countably `n`-rectifiable and locally `Hⁿ`-finite, with an approximate tangent plane containing
`L` at `Hⁿ`-a.e. point, `d = dim L < n` and `m = n − d`.  Then for `Hᵈ`-a.e. `t ∈ L` the slice
`Mₜ = M ∩ p⁻¹(t)` is countably `m`-rectifiable with `Tan(Mₜ, x) = TₓM ∩ L⊥` for `Hᵐ`-a.e.
`x ∈ Mₜ`, and `∫_M g dHⁿ = ∫_L ∫_{Mₜ} g dHᵐ dHᵈ(t)` for Borel `g ≥ 0`.

Up to an `Hⁿ`-null set, `M` is the disjoint union of pieces `H(Ω)` with `H` Lipschitz and
bi-Lipschitz on `Ω ⊆ ℝⁿ ≅ L × ℝᵐ` and `p ∘ H = (first coordinate)`: a bi-Lipschitz piece
`F(T)` on which `F` is close to a linear map `A` with `L ⊆ range A` is reparametrized by
`u ↦ (pF(u), π_{ker pA}(u))`.  Because `L ⊆ range DH`, a shear shows `JH = J(H(t, ·))` (the
coarea factor is `1`), so the area formula for `H` and for its slices and Fubini give the
identity on each piece; `Hⁿ`-null sets have `Hᵐ`-null slices for a.e. `t` (covering argument and
Fatou).  The slices are covered by the slice maps `H(t, ·)`, and `lipschitz_tangent` applied to
them gives the tangent planes.  The argument runs over abstract finite-dimensional spaces
`V, F, B` and is instantiated at `ℝⁿ, ℝᴾ, ℝᵐ`. -/
theorem Submission.idtp_fons_cs_sos_spine_coarea : ∀ (P n : ℕ) (L : Submodule ℝ (Euclid P)) (M : Set (Euclid P)), Module.finrank ℝ L < n → MeasurableSet M → CountablyRectifiable n M → (∀ K : Set (Euclid P), IsCompact K → μHE[n] (M ∩ K) ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ∧ L ≤ Q) → (∀ᵐ t ∂(μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))), CountablyRectifiable (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) ∧ ∀ᵐ x ∂(μHE[n - Module.finrank ℝ L].restrict (M ∩ {x | L.starProjection x = t})), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt (n - Module.finrank ℝ L) (M ∩ {x | L.starProjection x = t}) x (Q ⊓ Lᗮ)) ∧ ∀ g : Euclid P → ℝ≥0∞, Measurable g → AEMeasurable (fun t => ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L]) (μHE[Module.finrank ℝ L].restrict (L : Set (Euclid P))) ∧ ∫⁻ x in M, g x ∂μHE[n] = ∫⁻ t in (L : Set (Euclid P)), ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[n - Module.finrank ℝ L] ∂μHE[Module.finrank ℝ L] := by
  intro P n L M hdn hM hrect hloc htan
  -- The argument runs over abstract spaces `V = ℝⁿ`, `F = ℝᴾ`, `B = ℝᵐ`; the Euclidean inputs
  -- (bi-Lipschitz pieces, pull-back of null sets along a piece, `lipschitz_tangent` in dimensions
  -- `n` and `m`, a.e. transfer through pieces) enter as hypotheses.
  have master : ∀ (V F B : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
      [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup F]
      [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] [MeasurableSpace B]
      [BorelSpace B] (n d m : ℕ) (L : Submodule ℝ F) (M : Set F),
      Module.finrank ℝ V = n → Module.finrank ℝ B = m → Module.finrank ℝ ↥L = d → d < n →
      n - d = m → MeasurableSet M → (∀ K : Set F, IsCompact K → μHE[n] (M ∩ K) ≠ ∞) →
      (∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ F, HasApproximateTangentSpaceAt n M x Q ∧
        L ≤ Q) →
      (∃ (Fp : ℕ → V → F) (Bp : ℕ → Set V) (mm : ℕ → ℝ),
        (∀ i, ∃ K : NNReal, LipschitzWith K (Fp i)) ∧ (∀ i, MeasurableSet (Bp i)) ∧
        (∀ i, 0 < mm i) ∧ (∀ i, ∀ a ∈ Bp i, ∀ a' ∈ Bp i, mm i * ‖a - a'‖ ≤ ‖Fp i a - Fp i a'‖) ∧
        (∀ i, ∀ a ∈ Bp i, DifferentiableAt ℝ (Fp i) a ∧ Injective (fderiv ℝ (Fp i) a)) ∧
        (∀ i, MeasurableSet (Fp i '' Bp i)) ∧ (∀ i, Fp i '' Bp i ⊆ M) ∧
        Pairwise (fun i j => Disjoint (Fp i '' Bp i) (Fp j '' Bp j)) ∧
        μHE[n] (M \ ⋃ i, Fp i '' Bp i) = 0) →
      (∀ (G : V → F) (S : Set V) (K : NNReal) (c : ℝ), LipschitzWith K G → MeasurableSet S →
        0 < c → (∀ a ∈ S, ∀ a' ∈ S, c * ‖a - a'‖ ≤ ‖G a - G a'‖) → MeasurableSet (G '' S) ∧
        ∀ p : F → Prop, (∀ᵐ y ∂(μHE[n].restrict (G '' S)), p y) →
          ∀ᵐ b ∂(volume.restrict S), p (G b)) →
      (∀ (G : V → F) (Y : Set F) (K : NNReal), LipschitzWith K G → MeasurableSet Y →
        (∀ C : Set F, IsCompact C → μHE[n] (Y ∩ C) ≠ ∞) → ∀ᵐ u ∂(volume : Measure V), G u ∈ Y →
        DifferentiableAt ℝ G u → Injective (fderiv ℝ G u) →
        HasApproximateTangentSpaceAt n Y (G u) (LinearMap.range (fderiv ℝ G u : V →ₗ[ℝ] F))) →
      (∀ (G : B → F) (Y : Set F) (K : NNReal), LipschitzWith K G → MeasurableSet Y →
        (∀ C : Set F, IsCompact C → μHE[m] (Y ∩ C) ≠ ∞) → ∀ᵐ u ∂(volume : Measure B), G u ∈ Y →
        DifferentiableAt ℝ G u → Injective (fderiv ℝ G u) →
        HasApproximateTangentSpaceAt m Y (G u) (LinearMap.range (fderiv ℝ G u : B →ₗ[ℝ] F))) →
      (∀ (S : Set F) (G : ℕ → B → F) (T : ℕ → Set B) (p : F → Prop), MeasurableSet S →
        (∀ i, ∃ K : NNReal, LipschitzWith K (G i)) → μHE[m] (S \ ⋃ i, G i '' T i) = 0 →
        (∀ i, ∀ᵐ b ∂(volume.restrict (T i)), p (G i b)) → ∀ᵐ x ∂(μHE[m].restrict S), p x) →
      (∀ᵐ t ∂(μHE[d].restrict (L : Set F)), (∃ M₀ : Set F, μHE[m] M₀ = 0 ∧ ∃ G : ℕ → B → F,
          (∀ j, ∃ K : NNReal, LipschitzWith K (G j)) ∧
          M ∩ {x | L.starProjection x = t} ⊆ M₀ ∪ ⋃ j, range (G j)) ∧
        ∀ᵐ x ∂(μHE[m].restrict (M ∩ {x | L.starProjection x = t})), ∀ Q : Submodule ℝ F,
          HasApproximateTangentSpaceAt n M x Q →
          HasApproximateTangentSpaceAt m (M ∩ {x | L.starProjection x = t}) x (Q ⊓ Lᗮ)) ∧
      ∀ g : F → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t => ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[m])
          (μHE[d].restrict (L : Set F)) ∧
        ∫⁻ x in M, g x ∂μHE[n] = ∫⁻ t in (L : Set F),
          ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[m] ∂μHE[d] := by
    intro V F B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n d m L M hV hBm hd hdn hmd hM hloc htan hpieces
      hptd hchV hchB hitt
    have hm0 : 0 < m := hmd ▸ Nat.sub_pos_of_lt hdn
    have hnd : n = d + m := by rw [← hmd, Nat.add_sub_cancel' hdn.le]
    -- the parameter splitting `V ≅ L × B`
    have hfinE : Module.finrank ℝ V = Module.finrank ℝ (WithLp 2 (↥L × B)) := by
      rw [(WithLp.linearEquiv 2 ℝ (↥L × B)).finrank_eq, Module.finrank_prod, hd, hBm, hV, hnd]
    obtain ⟨Θ⟩ : Nonempty (V ≃ₗᵢ[ℝ] WithLp 2 (↥L × B)) :=
      ⟨(stdOrthonormalBasis ℝ V).equiv (stdOrthonormalBasis ℝ _) (finCongr hfinE)⟩
    -- the base: `volume` on `L` is `Hᵈ⌞L`
    have hLmeas : MeasurableSet (L : Set F) := L.closed_of_finiteDimensional.measurableSet
    have hemb : MeasurableEmbedding (Subtype.val : ↥L → F) := MeasurableEmbedding.subtype_coe hLmeas
    have hmap : (volume : Measure ↥L).map Subtype.val = μHE[d].restrict (L : Set F) := by
      rw [← InnerProductSpace.euclideanHausdorffMeasure_eq_volume, hd,
        isometry_subtype_coe.map_euclideanHausdorffMeasure, Subtype.range_coe]
    -- Fubini in the parameters
    have hmp : MeasurePreserving (fun x : ↥L × B => Θ.symm (WithLp.toLp 2 x)) (volume.prod volume)
        volume :=
      Θ.symm.measurePreserving.comp (WithLp.volume_preserving_toLp _ _)
    have hvolV : (μHE[n] : Measure V) = volume := by
      rw [← hV]
      exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    -- the first coordinate `π₁ z = (Θ z).1 ∈ L` and the slice inclusion `jL s = Θ⁻¹(0, s)`
    obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : V →L[ℝ] F, ∀ z, π₁ z = (((Θ z).fst : ↥L) : F) :=
      ⟨L.subtypeL.comp ((ContinuousLinearMap.fst ℝ ↥L B).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℝ ↥L B).toContinuousLinearMap.comp
          (Θ.toContinuousLinearEquiv : V →L[ℝ] WithLp 2 (↥L × B)))), fun z => rfl⟩
    have hpπ : ∀ z, L.starProjection (π₁ z) = π₁ z := fun z =>
      Submodule.starProjection_eq_self_iff.mpr (by rw [hπ₁]; exact ((Θ z).fst).2)
    obtain ⟨jL, hjL⟩ : ∃ jL : B →L[ℝ] V, ∀ s, jL s = Θ.symm (WithLp.toLp 2 (0, s)) :=
      ⟨(Θ.symm.toContinuousLinearEquiv : WithLp 2 (↥L × B) →L[ℝ] V).comp
        ((WithLp.prodContinuousLinearEquiv 2 ℝ ↥L B).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ ↥L B)), fun s => rfl⟩
    have hjinj : Injective jL := fun s s' h => by
      rw [hjL, hjL] at h
      exact congrArg Prod.snd (WithLp.toLp_injective 2 (Θ.symm.injective h))
    have hjsplit : ∀ (t : ↥L) s, Θ.symm (WithLp.toLp 2 (t, s)) =
        Θ.symm (WithLp.toLp 2 (t, 0)) + jL s := fun t s => by
      rw [hjL, ← map_add, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
    -- **the Jacobian identity**: `J(DH) = J(DH ∘ jL)` when `p ∘ DH = π₁` and `L ⊆ range DH`
    have hLA : ∀ D : V →ₗ[ℝ] F, (∀ v, L.starProjection (D v) = π₁ v) → L ≤ LinearMap.range D →
        D.normDet = (D ∘ₗ (jL : B →ₗ[ℝ] V)).normDet ∧
        LinearMap.range (D ∘ₗ (jL : B →ₗ[ℝ] V)) = LinearMap.range D ⊓ Lᗮ := by
      intro D h1 h2
      have h1 : ∀ v, L.starProjection (D v) = ((Θ v).fst : F) := fun v => (h1 v).trans (hπ₁ v)
      obtain ⟨Y, hYdef⟩ : ∃ Y : B →ₗ[ℝ] F, Y = D ∘ₗ (jL : B →ₗ[ℝ] V) := ⟨_, rfl⟩
      rw [← hYdef]
      have hY : ∀ s, Y s = D (Θ.symm (WithLp.toLp 2 (0, s))) := fun s => by
        rw [hYdef]
        exact congrArg D (hjL s)
      have hYorth : ∀ s, Y s ∈ Lᗮ := fun s => by
        rw [← Submodule.orthogonalProjectionOnto_eq_zero_iff]
        apply Subtype.ext
        rw [← Submodule.starProjection_apply, hY, h1, LinearIsometryEquiv.apply_symm_apply]
        rfl
      have hsplit : ∀ w, D (Θ.symm w) = D (Θ.symm (WithLp.toLp 2 (w.fst, 0))) + Y w.snd :=
          fun w => by
        rw [hY, ← map_add, ← map_add, ← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add]
        rfl
      refine ⟨?_, ?_⟩
      · have hXY : ∀ τ : ↥L, D (Θ.symm (WithLp.toLp 2 (τ, 0))) - (τ : F) ∈ LinearMap.range Y := by
          intro τ
          obtain ⟨v, hv⟩ := h2 τ.2
          have hfst : (Θ v).fst = τ := Subtype.ext (by
            rw [← h1 v, show D v = (τ : F) from hv]
            exact Submodule.starProjection_eq_self_iff.mpr τ.2)
          refine ⟨-(Θ v).snd, ?_⟩
          have hs := hsplit (Θ v)
          rw [LinearIsometryEquiv.symm_apply_apply, hfst, show D v = (τ : F) from hv] at hs
          rw [map_neg, eq_sub_of_add_eq hs.symm]
          abel
        obtain ⟨Bm, hBm⟩ := Module.projective_lifting_property Y.rangeRestrict
          ((D ∘ₗ Θ.symm.toLinearIsometry.toLinearMap ∘ₗ
            (WithLp.linearEquiv 2 ℝ (↥L × B)).symm.toLinearMap
            ∘ₗ LinearMap.inl ℝ ↥L B - L.subtype).codRestrict (LinearMap.range Y) hXY)
          Y.surjective_rangeRestrict
        have hB : ∀ τ, Y (Bm τ) = D (Θ.symm (WithLp.toLp 2 (τ, 0))) - (τ : F) := fun τ =>
          congrArg Subtype.val (LinearMap.congr_fun hBm τ)
        obtain ⟨U, hU⟩ : ∃ U : WithLp 2 (↥L × B) →ₗ[ℝ] WithLp 2 (↥L × B), U = LinearMap.id +
            ((WithLp.linearEquiv 2 ℝ (↥L × B)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ ↥L B ∘ₗ Bm) ∘ₗ
            (LinearMap.fst ℝ ↥L B ∘ₗ (WithLp.linearEquiv 2 ℝ (↥L × B)).toLinearMap) := ⟨_, rfl⟩
        have hdetU : LinearMap.det U = 1 := by
          classical
          have hA : (LinearMap.fst ℝ ↥L B ∘ₗ (WithLp.linearEquiv 2 ℝ (↥L × B)).toLinearMap) ∘ₗ
              ((WithLp.linearEquiv 2 ℝ (↥L × B)).symm.toLinearMap ∘ₗ LinearMap.inr ℝ ↥L B ∘ₗ Bm) =
                0 :=
            LinearMap.ext fun τ => rfl
          let b := Module.finBasis ℝ (WithLp 2 (↥L × B))
          let c := Module.finBasis ℝ ↥L
          rw [← LinearMap.det_toMatrix b, hU, map_add, LinearMap.toMatrix_id,
            LinearMap.toMatrix_comp b c b, Matrix.det_one_add_mul_comm,
            ← LinearMap.toMatrix_comp c b c, hA, map_zero, add_zero, Matrix.det_one]
        obtain ⟨D₀, hD₀⟩ : ∃ D₀ : WithLp 2 (↥L × B) →ₗ[ℝ] F, ∀ w, D₀ w = (w.fst : F) + Y w.snd :=
          ⟨L.subtype ∘ₗ LinearMap.fst ℝ ↥L B ∘ₗ (WithLp.linearEquiv 2 ℝ (↥L × B)).toLinearMap +
            Y ∘ₗ LinearMap.snd ℝ ↥L B ∘ₗ (WithLp.linearEquiv 2 ℝ (↥L × B)).toLinearMap,
            fun w => rfl⟩
        have hfac : D ∘ₗ Θ.symm.toLinearIsometry.toLinearMap = D₀ ∘ₗ U := by
          refine LinearMap.ext fun w => ?_
          have hUw : U w = WithLp.toLp 2 (w.fst, w.snd + Bm w.fst) := by
            rw [hU]
            exact WithLp.ofLp_injective 2 (Prod.ext (add_zero _) rfl)
          change D (Θ.symm w) = D₀ (U w)
          rw [hUw, hD₀, hsplit w]
          change D (Θ.symm (WithLp.toLp 2 (w.fst, 0))) + Y w.snd =
            (w.fst : F) + Y (w.snd + Bm w.fst)
          rw [map_add, hB]
          abel
        have hD₀Y : D₀.normDet = Y.normDet := by
          classical
          let bA := stdOrthonormalBasis ℝ ↥L
          let bB := stdOrthonormalBasis ℝ B
          have hg := LinearMap.normDet_sq_eq_det_gram D₀ (bA.prod bB)
          have hgY := LinearMap.normDet_sq_eq_det_gram Y bB
          have hb1 : ∀ i, D₀ (bA.prod bB (Sum.inl i)) = (bA i : F) := fun i => by
            rw [OrthonormalBasis.prod_apply, hD₀]
            change (bA i : F) + Y 0 = _
            rw [map_zero, add_zero]
          have hb2 : ∀ j, D₀ (bA.prod bB (Sum.inr j)) = Y (bB j) := fun j => by
            rw [OrthonormalBasis.prod_apply, hD₀]
            change ((0 : ↥L) : F) + Y (bB j) = _
            rw [Submodule.coe_zero, zero_add]
          have hG : Matrix.gram ℝ (fun i => D₀ (bA.prod bB i)) =
              Matrix.fromBlocks 1 0 0 (Matrix.gram ℝ (fun j => Y (bB j))) := by
            ext (i | i) (j | j)
            · rw [Matrix.gram_apply, hb1, hb1, Matrix.fromBlocks_apply₁₁, Matrix.one_apply,
                ← Submodule.coe_inner, bA.inner_eq_ite]
            · rw [Matrix.gram_apply, hb1, hb2, Matrix.fromBlocks_apply₁₂]
              exact Submodule.inner_right_of_mem_orthogonal (bA i).2 (hYorth _)
            · rw [Matrix.gram_apply, hb1, hb2, Matrix.fromBlocks_apply₂₁]
              exact Submodule.inner_left_of_mem_orthogonal (bA j).2 (hYorth _)
            · rw [Matrix.gram_apply, hb2, hb2, Matrix.fromBlocks_apply₂₂, Matrix.gram_apply]
          rw [hG, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, ← hgY] at hg
          exact (sq_eq_sq₀ (LinearMap.normDet_nonneg _) (LinearMap.normDet_nonneg _)).mp
            (by exact_mod_cast hg)
        have e1 : (D ∘ₗ Θ.symm.toLinearIsometry.toLinearMap).normDet = D.normDet := by
          rw [LinearMap.normDet_comp_of_finrank_eq _ _ Θ.symm.toLinearEquiv.finrank_eq,
            Θ.symm.toLinearIsometry.normDet_eq_one, mul_one]
        rw [← e1, hfac, LinearMap.normDet_comp_of_finrank_eq U D₀ rfl,
          LinearMap.normDet_eq_abs_det U,
          hdetU, abs_one, mul_one, hD₀Y]
      · apply le_antisymm
        · rintro y ⟨s, rfl⟩
          exact ⟨⟨Θ.symm (WithLp.toLp 2 (0, s)), (hY s).symm⟩, hYorth s⟩
        · rintro y ⟨⟨v, rfl⟩, hy⟩
          have h0 : (Θ v).fst = 0 := by
            apply Subtype.ext
            rw [← h1 v, Submodule.starProjection_apply]
            exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy)
          refine ⟨(Θ v).snd, ?_⟩
          have hv : WithLp.toLp 2 ((0 : ↥L), (Θ v).snd) = Θ v :=
            WithLp.ofLp_injective 2 (Prod.ext h0.symm rfl)
          rw [hY, hv, LinearIsometryEquiv.symm_apply_apply]

    -- the constants of the reparametrization of a piece
    have hC : ∀ A : V →L[ℝ] F, ∃ C : NNReal, 0 < C ∧ ∀ v : V,
        ‖v‖ ≤ C * max ‖L.starProjection (A v)‖
          ‖(LinearMap.ker ((L.starProjection.comp A : V →L[ℝ] F) : V →ₗ[ℝ] F)).starProjection
            v‖ := by
      intro A
      obtain ⟨C, hC0, hCa⟩ := LinearMap.exists_antilipschitzWith
        (((L.starProjection.comp A : V →L[ℝ] F) : V →ₗ[ℝ] F).prod
          ((LinearMap.ker ((L.starProjection.comp A : V →L[ℝ] F) : V →ₗ[ℝ] F)).starProjection :
            V →ₗ[ℝ] V))
        (LinearMap.ker_eq_bot'.mpr fun v hv => by
          obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hv
          exact (Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_ker.mpr h1)).symm.trans h2)
      exact ⟨C, hC0, fun v => (ZeroHomClass.bound_of_antilipschitz _ hCa v).trans_eq (by
        rw [Prod.norm_def]; rfl)⟩
    choose C hCpos hCb using hC
    have hdim : Module.finrank ℝ V = Module.finrank ℝ ↥L + Module.finrank ℝ B := by
      rw [hV, hd, hBm, hnd]
    -- **one piece**: reparametrize `F'` on `T` over `L × B`, with `p ∘ H' = π₁`
    have hPCL : ∀ (F' : V → F) (K' : NNReal) (T : Set V) (A' : V →L[ℝ] F) (m' : ℝ),
        LipschitzWith K' F' → MeasurableSet T → 0 < m' →
        (∀ a ∈ T, ∀ a' ∈ T, m' * ‖a - a'‖ ≤ ‖F' a - F' a'‖) →
        ApproximatesLinearOn F' A' T (2 * C A')⁻¹ →
        (T.Nonempty → L ≤ LinearMap.range (A' : V →ₗ[ℝ] F)) →
        ∃ (H' : V → F) (Ω' : Set V), (∃ K : NNReal, LipschitzWith K H') ∧ MeasurableSet Ω' ∧
          (∃ c : ℝ, 0 < c ∧ ∀ z ∈ Ω', ∀ z' ∈ Ω', c * ‖z - z'‖ ≤ ‖H' z - H' z'‖) ∧
          H' '' Ω' = F' '' T ∧ ∀ z, L.starProjection (H' z) = π₁ z := by
      intro F' K' T A' m' hF' hT hm' hbil' happ hLA'
      rcases T.eq_empty_or_nonempty with hT0 | hTne
      · exact ⟨π₁, ∅, ⟨_, π₁.lipschitzWith⟩, MeasurableSet.empty,
          ⟨1, one_pos, fun z hz => absurd hz (Set.notMem_empty z)⟩,
          by rw [hT0, Set.image_empty, Set.image_empty], hpπ⟩
      have hLA'' := hLA' hTne
      -- `K = ker (p ∘ A')` has dimension `dim B`
      have hrange : LinearMap.range ((L.starProjection.comp A' : V →L[ℝ] F) : V →ₗ[ℝ] F) = L := by
        apply le_antisymm
        · rintro _ ⟨v, rfl⟩
          change L.starProjection (A' v) ∈ L
          rw [Submodule.starProjection_apply]
          exact (L.orthogonalProjectionOnto (A' v)).2
        · intro ℓ hℓ
          obtain ⟨w, hw⟩ := hLA'' hℓ
          refine ⟨w, ?_⟩
          change L.starProjection (A' w) = ℓ
          rw [show A' w = ℓ from hw]
          exact Submodule.starProjection_eq_self_iff.mpr hℓ
      have hKfin : Module.finrank ℝ (LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) :
          V →ₗ[ℝ] F)) = Module.finrank ℝ B := by
        have h := LinearMap.finrank_range_add_finrank_ker
          ((L.starProjection.comp A' : V →L[ℝ] F) : V →ₗ[ℝ] F)
        rw [hrange, hdim] at h
        exact Nat.add_left_cancel h
      obtain ⟨κ⟩ : Nonempty (↥(LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) : V →ₗ[ℝ] F))
          ≃ₗᵢ[ℝ] B) := ⟨(stdOrthonormalBasis ℝ _).equiv (stdOrthonormalBasis ℝ B) (finCongr hKfin)⟩
      obtain ⟨Λ, hΛ⟩ : ∃ Λ : F × V →L[ℝ] V, ∀ x y, Λ (x, y) =
          Θ.symm (WithLp.toLp 2 (L.orthogonalProjectionOnto x,
            κ ((LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) :
              V →ₗ[ℝ] F)).orthogonalProjectionOnto y))) :=
        ⟨(Θ.symm.toContinuousLinearEquiv : WithLp 2 (↥L × B) →L[ℝ] V).comp
          ((WithLp.prodContinuousLinearEquiv 2 ℝ ↥L B).symm.toContinuousLinearMap.comp
            (L.orthogonalProjectionOnto.prodMap
              ((κ.toContinuousLinearEquiv : _ →L[ℝ] B).comp
                (LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) :
                  V →ₗ[ℝ] F)).orthogonalProjectionOnto))), fun x y => rfl⟩
      have hΛ1 : ∀ x y, ‖L.starProjection x‖ ≤ ‖Λ (x, y)‖ := fun x y => by
        rw [hΛ, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
        exact WithLp.norm_fst_le (x := WithLp.toLp 2 (L.orthogonalProjectionOnto x, _))
      have hΛ2 : ∀ x y, ‖(LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) :
          V →ₗ[ℝ] F)).starProjection y‖ ≤ ‖Λ (x, y)‖ := fun x y => by
        rw [hΛ, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
        exact (κ.norm_map _).symm.trans_le (WithLp.norm_snd_le (x := WithLp.toLp 2 (_, _)))
      obtain ⟨Φ, hΦ⟩ : ∃ Φ : V → V, ∀ u, Φ u = Λ (F' u, u) := ⟨_, fun u => rfl⟩
      have hΦL : LipschitzWith (‖Λ‖₊ * max K' 1) Φ := by
        rw [show Φ = fun u => Λ (F' u, u) from funext hΦ]
        exact Λ.lipschitzWith.comp (hF'.prodMk LipschitzWith.id)
      have hΦsub : ∀ u u', Φ u - Φ u' = Λ (F' u - F' u', u - u') := fun u u' => by
        rw [hΦ, hΦ, ← map_sub]
        rfl
      have hCr : (C A' : ℝ) * ((2 * C A')⁻¹ : NNReal) = 1 / 2 := by
        have := (hCpos A').ne'
        push_cast
        field_simp
      have hkey : ∀ v ∈ T, ∀ w ∈ T, ‖v - w‖ ≤ 2 * C A' * ‖Φ v - Φ w‖ := by
        intro v hv w hw
        have h2 : ‖L.starProjection (A' (v - w))‖ ≤
            ‖Φ v - Φ w‖ + ((2 * C A')⁻¹ : NNReal) * ‖v - w‖ := by
          rw [show A' (v - w) = (F' v - F' w) - (F' v - F' w - A' (v - w)) from
            (sub_sub_cancel _ _).symm, map_sub, hΦsub]
          exact (norm_sub_le _ _).trans (add_le_add (hΛ1 _ _)
            ((L.norm_starProjection_apply_le _).trans (happ v hv w hw)))
        have h3 : ‖(LinearMap.ker ((L.starProjection.comp A' : V →L[ℝ] F) :
            V →ₗ[ℝ] F)).starProjection (v - w)‖ ≤
            ‖Φ v - Φ w‖ + ((2 * C A')⁻¹ : NNReal) * ‖v - w‖ := by
          rw [hΦsub]
          exact (hΛ2 _ _).trans (le_add_of_nonneg_right
            (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)))
        have h5 := (hCb A' (v - w)).trans (mul_le_mul_of_nonneg_left (max_le h2 h3) (C A').2)
        rw [mul_add, ← mul_assoc, hCr] at h5
        linarith only [h5]
      have hΦinj : InjOn Φ T := fun v hv w hw hvw => by
        have := hkey v hv w hw
        rw [hvw, sub_self, norm_zero, mul_zero] at this
        exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
      have hψ : ∀ u ∈ T, Function.invFunOn Φ T (Φ u) = u := fun u hu => hΦinj.leftInvOn_invFunOn hu
      have hH₀ : LipschitzOnWith (K' * (2 * C A')) (fun z => F' (Function.invFunOn Φ T z))
          (Φ '' T) := by
        apply LipschitzOnWith.of_dist_le_mul
        rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
        rw [hψ u hu, hψ u' hu', dist_eq_norm, dist_eq_norm]
        calc ‖F' u - F' u'‖ ≤ K' * ‖u - u'‖ := hF'.norm_sub_le u u'
          _ ≤ K' * (2 * C A' * ‖Φ u - Φ u'‖) := mul_le_mul_of_nonneg_left (hkey u hu u' hu') K'.2
          _ = _ := by push_cast; ring
      obtain ⟨h₁, hh₁L, hh₁eq⟩ := hH₀.extend_finite_dimension
      have hpq : ∀ y, L.starProjection (Lᗮ.starProjection y) = 0 := fun y => by
        rw [Submodule.starProjection_apply L, Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
          (by rw [Submodule.starProjection_apply]; exact (Lᗮ.orthogonalProjectionOnto y).2)]
        rfl
      have hH'Φ : ∀ u ∈ T, π₁ (Φ u) + Lᗮ.starProjection (h₁ (Φ u)) = F' u := by
        intro u hu
        have e1 : π₁ (Φ u) = L.starProjection (F' u) := by
          rw [hπ₁, hΦ, hΛ, LinearIsometryEquiv.apply_symm_apply, Submodule.starProjection_apply]
          rfl
        have e2 : h₁ (Φ u) = F' u := by
          rw [← hh₁eq ⟨u, hu, rfl⟩]
          exact congrArg F' (hψ u hu)
        rw [e1, e2]
        exact L.starProjection_add_starProjection_orthogonal (F' u)
      have hK1 : (0 : ℝ) < ((‖Λ‖₊ * max K' 1 : NNReal) : ℝ) + 1 :=
        add_pos_of_nonneg_of_pos (NNReal.coe_nonneg _) one_pos
      refine ⟨fun z => π₁ z + Lᗮ.starProjection (h₁ z), Φ '' T,
        ⟨_, π₁.lipschitzWith.add (Lᗮ.starProjection.lipschitzWith.comp hh₁L)⟩,
        hT.image_of_continuousOn_injOn hΦL.continuous.continuousOn hΦinj,
        ⟨m' * (((‖Λ‖₊ * max K' 1 : NNReal) : ℝ) + 1)⁻¹, mul_pos hm' (inv_pos.mpr hK1), ?_⟩, ?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩
        dsimp only
        rw [hH'Φ u hu, hH'Φ u' hu']
        calc m' * (((‖Λ‖₊ * max K' 1 : NNReal) : ℝ) + 1)⁻¹ * ‖Φ u - Φ u'‖
            ≤ m' * (((‖Λ‖₊ * max K' 1 : NNReal) : ℝ) + 1)⁻¹ *
              ((((‖Λ‖₊ * max K' 1 : NNReal) : ℝ) + 1) * ‖u - u'‖) :=
              mul_le_mul_of_nonneg_left ((hΦL.norm_sub_le u u').trans (mul_le_mul_of_nonneg_right
                (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)))
                (mul_nonneg hm'.le (inv_nonneg.mpr hK1.le))
          _ = m' * ‖u - u'‖ := by rw [mul_assoc, inv_mul_cancel_left₀ hK1.ne']
          _ ≤ ‖F' u - F' u'‖ := hbil' u hu u' hu'
      · rw [Set.image_image]
        exact Set.image_congr hH'Φ
      · intro z
        rw [map_add, hpq, add_zero, hpπ]

    -- **the pieces**: `M` is, up to a null set, the disjoint union of the `H k '' Ω k`
    obtain ⟨H, Ω, hHL, hΩm, hHbil, hHM, hdisj, hnull, hpH⟩ : ∃ (H : ℕ → V → F) (Ω : ℕ → Set V),
        (∀ k, ∃ K : NNReal, LipschitzWith K (H k)) ∧ (∀ k, MeasurableSet (Ω k)) ∧
        (∀ k, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Ω k, ∀ z' ∈ Ω k, c * ‖z - z'‖ ≤ ‖H k z - H k z'‖) ∧
        (∀ k, H k '' Ω k ⊆ M) ∧ Pairwise (fun k k' => Disjoint (H k '' Ω k) (H k' '' Ω k')) ∧
        μHE[n] (M \ ⋃ k, H k '' Ω k) = 0 ∧ (∀ k z, L.starProjection (H k z) = π₁ z) := by
      obtain ⟨Fp, Bp, mm, hFL, hBm, hmpos, hbil, hdiff, -, hFBM, hFdisj, hFnull⟩ := hpieces
      choose KF hKF using hFL
      -- a.e. on `Bp i`, the tangent plane `range DFp i` contains `L`
      have hgood : ∀ i, ∃ G : Set V, MeasurableSet G ∧ G ⊆ Bp i ∧ volume (Bp i \ G) = 0 ∧
          ∀ a ∈ G, L ≤ LinearMap.range (fderiv ℝ (Fp i) a : V →ₗ[ℝ] F) := by
        intro i
        have h1 := (hptd (Fp i) (Bp i) (KF i) (mm i) (hKF i) (hBm i) (hmpos i) (hbil i)).2 _
          (ae_restrict_of_ae_restrict_of_subset (hFBM i) htan)
        have h2 := ae_restrict_of_ae (s := Bp i) (hchV (Fp i) M (KF i) (hKF i) hM hloc)
        have h3 : ∀ᵐ a ∂(volume.restrict (Bp i)),
            L ≤ LinearMap.range (fderiv ℝ (Fp i) a : V →ₗ[ℝ] F) := by
          filter_upwards [h1, h2, ae_restrict_mem (hBm i)] with a ha1 ha2 haB
          obtain ⟨Q, hQ, hLQ⟩ := ha1
          rw [← hQ.unique (ha2 (hFBM i ⟨a, haB, rfl⟩) (hdiff i a haB).1 (hdiff i a haB).2)]
          exact hLQ
        rw [ae_restrict_iff' (hBm i)] at h3
        refine ⟨Bp i \ toMeasurable volume {a | ¬(a ∈ Bp i →
            L ≤ LinearMap.range (fderiv ℝ (Fp i) a : V →ₗ[ℝ] F))},
          (hBm i).diff (measurableSet_toMeasurable _ _), sdiff_subset, ?_, ?_⟩
        · refine measure_mono_null (fun a ha => ?_) ((measure_toMeasurable _).trans (ae_iff.mp h3))
          exact not_not.mp fun h => ha.2 ⟨ha.1, h⟩
        · rintro a ⟨haB, haN⟩
          by_contra hc
          exact haN (subset_toMeasurable _ _ fun h => hc (h haB))
      choose G hGm hGB hGnull hGL using hgood
      have hpart : ∀ i, ∃ (t : ℕ → Set V) (A : ℕ → V →L[ℝ] F),
          Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G i ⊆ ⋃ k, t k ∧
          (∀ k, ApproximatesLinearOn (Fp i) (A k) (G i ∩ t k) (2 * C (A k))⁻¹) ∧
          ((G i).Nonempty → ∀ k, ∃ y ∈ G i, A k = fderiv ℝ (Fp i) y) := fun i =>
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (Fp i) (G i)
          (fun a => fderiv ℝ (Fp i) a)
          (fun a ha => (hdiff i a (hGB i ha)).1.hasFDerivAt.hasFDerivWithinAt)
          (fun A => (2 * C A)⁻¹) (fun A => inv_ne_zero (mul_ne_zero two_ne_zero (hCpos A).ne'))
      choose t A htdisj htm hGt hAapp hAeq using hpart
      -- the pieces, indexed by `q ↦ (q.unpair.1, q.unpair.2)`
      have hpc : ∀ q : ℕ, ∃ (H' : V → F) (Ω' : Set V), (∃ K : NNReal, LipschitzWith K H') ∧
          MeasurableSet Ω' ∧
          (∃ c : ℝ, 0 < c ∧ ∀ z ∈ Ω', ∀ z' ∈ Ω', c * ‖z - z'‖ ≤ ‖H' z - H' z'‖) ∧
          H' '' Ω' = Fp q.unpair.1 '' (G q.unpair.1 ∩ t q.unpair.1 q.unpair.2) ∧
          ∀ z, L.starProjection (H' z) = π₁ z := fun q =>
        hPCL _ _ _ _ _ (hKF _) ((hGm _).inter (htm _ _)) (hmpos _)
          (fun a ha a' ha' => hbil _ a (hGB _ ha.1) a' (hGB _ ha'.1)) (hAapp _ _)
          (fun ⟨a, ha⟩ => by
            obtain ⟨y, hy, hAy⟩ := hAeq _ ⟨a, ha.1⟩ q.unpair.2
            rw [hAy]
            exact hGL _ y hy)
      choose H Ω hHL hΩm hHbil hHimg hpH using hpc
      have hinj : ∀ i, InjOn (Fp i) (Bp i) := fun i a ha a' ha' h => by
        have h0 := hbil i a ha a' ha'
        rw [h, sub_self, norm_zero, ← mul_zero (mm i)] at h0
        exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_mul_le_mul_left h0 (hmpos i)))
      refine ⟨H, Ω, hHL, hΩm, hHbil, fun q => ?_, fun q q' hqq' => ?_, ?_, hpH⟩
      · rw [hHimg]
        exact (image_mono (inter_subset_left.trans (hGB _))).trans (hFBM _)
      · show Disjoint (H q '' Ω q) (H q' '' Ω q')
        rw [hHimg, hHimg]
        rcases eq_or_ne q.unpair.1 q'.unpair.1 with hi | hi
        · have hk : q.unpair.2 ≠ q'.unpair.2 := fun hk => hqq' (by
            rw [← Nat.pair_unpair q, ← Nat.pair_unpair q', hi, hk])
          rw [Set.disjoint_left]
          rintro _ ⟨a, ha, rfl⟩ ⟨a', ha', hFa⟩
          rw [← hi] at ha' hFa
          have := hinj _ (hGB _ ha'.1) (hGB _ ha.1) hFa
          subst this
          exact Set.disjoint_left.mp (htdisj _ hk) ha.2 ha'.2
        · exact (hFdisj hi).mono (image_mono (inter_subset_left.trans (hGB _)))
            (image_mono (inter_subset_left.trans (hGB _)))
      · refine measure_mono_null (t := (M \ ⋃ i, Fp i '' Bp i) ∪ ⋃ i, Fp i '' (Bp i \ G i)) ?_
          (measure_union_null hFnull (measure_iUnion_null fun i => ?_))
        · rintro x ⟨hxM, hx⟩
          by_cases hxF : x ∈ ⋃ i, Fp i '' Bp i
          · obtain ⟨i, a, haB, rfl⟩ := mem_iUnion.mp hxF
            by_cases haG : a ∈ G i
            · obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt i haG)
              exact absurd (mem_iUnion.mpr ⟨Nat.pair i k, by
                rw [hHimg, Nat.unpair_pair]; exact ⟨a, ⟨haG, hk⟩, rfl⟩⟩) hx
            · exact Or.inr (mem_iUnion.mpr ⟨i, a, ⟨haB, haG⟩, rfl⟩)
          · exact Or.inl ⟨hxM, hxF⟩
        · refine le_antisymm
            ((Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn
            n (hKF i).lipschitzOnWith).trans ?_) bot_le
          rw [hvolV, hGnull i, mul_zero]
    choose KH hKH using hHL
    choose cH hcH hbH using hHbil
    -- **coarea on one piece**
    have hPP : ∀ k, (∀ g : F → ℝ≥0∞, Measurable g →
          AEMeasurable (fun t => ∫⁻ x in H k '' Ω k ∩ {x | L.starProjection x = t}, g x ∂μHE[m])
            (μHE[d].restrict (L : Set F)) ∧
          ∫⁻ x in H k '' Ω k, g x ∂μHE[n] = ∫⁻ t in (L : Set F),
            ∫⁻ x in H k '' Ω k ∩ {x | L.starProjection x = t}, g x ∂μHE[m] ∂μHE[d]) ∧
        (∀ᵐ t : ↥L ∂volume, ∀ᵐ s ∂(volume : Measure B), Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k →
          HasFDerivAt (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s))))
            ((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s)))).comp jL) s ∧
          Injective ((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s)))).comp jL) ∧
          HasApproximateTangentSpaceAt n M (H k (Θ.symm (WithLp.toLp 2 (t, s))))
            (LinearMap.range (fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s))) : V →ₗ[ℝ] F)) ∧
          LinearMap.range (((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s)))).comp jL :
              B →L[ℝ] F) : B →ₗ[ℝ] F) =
            LinearMap.range (fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s))) : V →ₗ[ℝ] F) ⊓ Lᗮ) ∧
        (∀ t : ↥L,
          (∃ K' : NNReal, LipschitzWith K' (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s))))) ∧
          MeasurableSet {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} ∧
          (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s)))) ''
              {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} =
            H k '' Ω k ∩ {x | L.starProjection x = t}) := by
      intro k
      have hinj : InjOn (H k) (Ω k) := fun z hz z' hz' h => by
        have h0 := hbH k z hz z' hz'
        rw [h, sub_self, norm_zero, ← mul_zero (cH k)] at h0
        exact sub_eq_zero.mp (norm_le_zero_iff.mp (le_of_mul_le_mul_left h0 (hcH k)))
      obtain ⟨-, hpull⟩ := hptd (H k) (Ω k) (KH k) (cH k) (hKH k) (hΩm k) (hcH k) (hbH k)
      -- almost every parameter is good
      have hgood : ∀ᵐ w ∂(volume.restrict (Ω k)), DifferentiableAt ℝ (H k) w ∧
          Injective (fderiv ℝ (H k) w) ∧
          HasApproximateTangentSpaceAt n M (H k w)
            (LinearMap.range (fderiv ℝ (H k) w : V →ₗ[ℝ] F)) ∧
          L ≤ LinearMap.range (fderiv ℝ (H k) w : V →ₗ[ℝ] F) := by
        have hz := Poincare.SimonGMT.Chapter02.area_image_compl_regularSet_eq_zero (hKH k) (Ω k)
        rw [hV] at hz
        filter_upwards [hpull _ (ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hz)),
          hpull _ (ae_restrict_of_ae_restrict_of_subset (hHM k) htan),
          ae_restrict_of_ae (hchV (H k) M (KH k) (hKH k) hM hloc), ae_restrict_mem (hΩm k)]
          with w hw1 hw2 hw3 hwΩ
        have hreg : DifferentiableAt ℝ (H k) w ∧ Injective (fderiv ℝ (H k) w) := by
          by_contra hcon
          exact hw1 ⟨w, ⟨hwΩ, hcon⟩, rfl⟩
        have hT := hw3 (hHM k ⟨w, hwΩ, rfl⟩) hreg.1 hreg.2
        obtain ⟨Q, hQ, hLQ⟩ := hw2
        exact ⟨hreg.1, hreg.2, hT, hQ.unique hT ▸ hLQ⟩
      -- `p ∘ DH = π₁`
      have hpD : ∀ w, DifferentiableAt ℝ (H k) w →
          ∀ v, L.starProjection (fderiv ℝ (H k) w v) = π₁ v := by
        intro w hw v
        have h1 : HasFDerivAt (fun z => L.starProjection (H k z))
            (L.starProjection.comp (fderiv ℝ (H k) w)) w :=
          L.starProjection.hasFDerivAt.comp w hw.hasFDerivAt
        have h2 : HasFDerivAt (fun z => L.starProjection (H k z)) π₁ w := by
          rw [show (fun z => L.starProjection (H k z)) = π₁ from funext (hpH k)]
          exact π₁.hasFDerivAt
        exact ContinuousLinearMap.ext_iff.mp (h1.unique h2) v
      have hjd : ∀ (t : ↥L) s, HasFDerivAt (fun s : B => Θ.symm (WithLp.toLp 2 (t, s))) jL s := by
        intro t s
        rw [show (fun s : B => Θ.symm (WithLp.toLp 2 (t, s))) =
          fun s => Θ.symm (WithLp.toLp 2 (t, 0)) + jL s from funext (hjsplit t)]
        exact jL.hasFDerivAt.const_add _
      have hsg := Measure.ae_ae_of_ae_prod
        (hmp.quasiMeasurePreserving.ae ((ae_restrict_iff' (hΩm k)).mp hgood))
      have hslice : ∀ t : ↥L,
          (∃ K' : NNReal, LipschitzWith K' (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s))))) ∧
          MeasurableSet {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} ∧
          (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s)))) ''
              {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} =
            H k '' Ω k ∩ {x | L.starProjection x = t} := by
        intro t
        have hjL' : LipschitzWith (0 + ‖jL‖₊) (fun s : B => Θ.symm (WithLp.toLp 2 (t, s))) := by
          rw [show (fun s : B => Θ.symm (WithLp.toLp 2 (t, s))) =
            fun s => Θ.symm (WithLp.toLp 2 (t, 0)) + jL s from funext (hjsplit t)]
          exact (LipschitzWith.const _).add jL.lipschitzWith
        refine ⟨⟨_, (hKH k).comp hjL'⟩, (hΩm k).preimage hjL'.continuous.measurable, ?_⟩
        apply le_antisymm
        · rintro _ ⟨s, hs, rfl⟩
          refine ⟨⟨_, hs, rfl⟩, ?_⟩
          change L.starProjection (H k _) = t
          rw [hpH, hπ₁, LinearIsometryEquiv.apply_symm_apply]
          rfl
        · rintro _ ⟨⟨z, hz, rfl⟩, hzt⟩
          have hzt' : (Θ z).fst = t := by
            apply Subtype.ext
            rw [← hπ₁, ← hpH]
            exact hzt
          have hz' : Θ.symm (WithLp.toLp 2 (t, (Θ z).snd)) = z := by
            rw [← hzt']
            exact Θ.symm_apply_apply z
          exact ⟨(Θ z).snd, show Θ.symm (WithLp.toLp 2 (t, (Θ z).snd)) ∈ Ω k from hz'.symm ▸ hz,
            congrArg (H k) hz'⟩
      refine ⟨fun g hg => ?_, ?_, hslice⟩
      · -- the Jacobian identity at good parameters
        have hJ : ∀ (t : ↥L) s, DifferentiableAt ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s))) →
            L ≤ LinearMap.range (fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s))) : V →ₗ[ℝ] F) →
            Poincare.SimonGMT.Chapter02.areaJacobianAt
                (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s)))) s =
              Poincare.SimonGMT.Chapter02.areaJacobianAt (H k) (Θ.symm (WithLp.toLp 2 (t, s))) := by
          intro t s h1 h4
          have hd' : HasFDerivAt (fun s => H k (Θ.symm (WithLp.toLp 2 (t, s))))
              ((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (t, s)))).comp jL) s :=
            h1.hasFDerivAt.comp s (hjd t s)
          rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet,
            Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, hd'.fderiv]
          exact (hLA _ (hpD _ h1) h4).1.symm
        obtain ⟨f, hf⟩ : ∃ f : V → ℝ≥0∞, f = (Ω k).indicator fun w =>
            ENNReal.ofReal (Poincare.SimonGMT.Chapter02.areaJacobianAt (H k) w) * g (H k w) :=
          ⟨_, rfl⟩
        have hfm : Measurable f := by
          rw [hf]
          exact ((Poincare.SimonGMT.Chapter02.measurable_areaJacobianAt (H k)).ennreal_ofReal.mul
            (hg.comp (hKH k).continuous.measurable)).indicator (hΩm k)
        have hfm2 : Measurable fun x : ↥L × B => f (Θ.symm (WithLp.toLp 2 x)) :=
          hfm.comp hmp.measurable
        -- the inner integrals agree for a.e. `t`
        have hinner : ∀ᵐ t : ↥L ∂volume, ∫⁻ s, f (Θ.symm (WithLp.toLp 2 (t, s))) =
            ∫⁻ x in H k '' Ω k ∩ {x | L.starProjection x = t}, g x ∂μHE[m] := by
          filter_upwards [hsg] with t ht
          obtain ⟨⟨K', hK'⟩, hΩt, himg⟩ := hslice t
          have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn hK' hΩt
            (fun s hs s' hs' h => hjinj (by
              have := hinj hs hs' h
              rwa [hjsplit t s, hjsplit t s', add_right_inj] at this)) g
          rw [hBm, himg] at harea
          rw [harea, ← lintegral_indicator hΩt]
          refine lintegral_congr_ae (ht.mono fun s hs => ?_)
          show f (Θ.symm (WithLp.toLp 2 (t, s))) = _
          by_cases hsΩ : Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k
          · obtain ⟨h1, -, -, h4⟩ := hs hsΩ
            rw [hf, indicator_of_mem hsΩ, indicator_of_mem
              (show s ∈ {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} from hsΩ), hJ t s h1 h4]
          · rw [hf, indicator_of_notMem hsΩ, indicator_of_notMem
              (show s ∉ {s | Θ.symm (WithLp.toLp 2 (t, s)) ∈ Ω k} from hsΩ)]
        have hint : ∫⁻ x in H k '' Ω k, g x ∂μHE[n] =
            ∫⁻ t : ↥L, ∫⁻ s, f (Θ.symm (WithLp.toLp 2 (t, s))) := by
          have harea := Poincare.SimonGMT.Chapter02.weighted_area_formula_lipschitz_injOn (hKH k)
            (hΩm k) hinj g
          rw [hV] at harea
          rw [harea, ← lintegral_indicator (hΩm k), ← hf, ← hmp.lintegral_comp hfm,
            lintegral_prod _ hfm2.aemeasurable]
        constructor
        · rw [← hmap, hemb.aemeasurable_map_iff]
          exact hfm2.lintegral_prod_right'.aemeasurable.congr hinner
        · rw [hint, ← hmap, hemb.lintegral_map]
          exact lintegral_congr_ae hinner
      · filter_upwards [hsg] with t ht
        filter_upwards [ht] with s hs hsΩ
        obtain ⟨h1, h2, h3, h4⟩ := hs hsΩ
        exact ⟨h1.hasFDerivAt.comp s (hjd t s), h2.comp hjinj, h3, (hLA _ (hpD _ h1) h4).2⟩
    -- **null sets have null slices** (Eilenberg's inequality for `p`, `Hⁿ`-null case)
    have hT4 : ∀ Z : Set F, μHE[n] Z = 0 → ∀ᵐ t ∂(μHE[d].restrict (L : Set F)),
        μHE[m] (Z ∩ {x | L.starProjection x = t}) = 0 := by
      intro Z hZ
      have hcH : ∀ k : ℕ, ∀ S : Set F, μHE[k] S = 0 ↔ μH[(k : ℝ)] S = 0 := fun k S => by
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul,
          mul_eq_zero, ENNReal.coe_eq_zero]
        exact or_iff_right (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero k)
      rw [hcH] at hZ
      -- fine covers of `Z` with small `∑ diamⁿ`
      have hcov : ∀ j : ℕ, ∃ C : ℕ → Set F, Z ⊆ ⋃ k, C k ∧
          (∀ k, ediam (C k) ≤ ((j : ℝ≥0∞) + 1)⁻¹) ∧
          ∑' k, ⨆ (_ : (C k).Nonempty), ediam (C k) ^ (n : ℝ) < ((j : ℝ≥0∞) + 1)⁻¹ := by
        intro j
        have hpos : (0 : ℝ≥0∞) < ((j : ℝ≥0∞) + 1)⁻¹ := ENNReal.inv_pos.mpr (by simp)
        have h0 : (⨅ (C : ℕ → Set F) (_ : Z ⊆ ⋃ k, C k)
            (_ : ∀ k, ediam (C k) ≤ ((j : ℝ≥0∞) + 1)⁻¹),
            ∑' k, ⨆ (_ : (C k).Nonempty), ediam (C k) ^ (n : ℝ)) < ((j : ℝ≥0∞) + 1)⁻¹ := by
          refine lt_of_le_of_lt ?_ hpos
          rw [← hZ, Measure.hausdorffMeasure_apply]
          exact le_iSup₂_of_le (f := fun (r : ℝ≥0∞) (_ : 0 < r) => ⨅ (C : ℕ → Set F)
            (_ : Z ⊆ ⋃ k, C k) (_ : ∀ k, ediam (C k) ≤ r),
            ∑' k, ⨆ (_ : (C k).Nonempty), ediam (C k) ^ (n : ℝ)) _ hpos le_rfl
        obtain ⟨C, hC⟩ := iInf_lt_iff.mp h0
        obtain ⟨hZC, hC⟩ := iInf_lt_iff.mp hC
        obtain ⟨hdiam, hC⟩ := iInf_lt_iff.mp hC
        exact ⟨C, hZC, hdiam, hC⟩
      choose C hZC hdiam hsum using hcov
      have hfin : ∀ j k, ediam (C j k) ≠ ⊤ := fun j k =>
        ((hdiam j k).trans_lt (ENNReal.inv_lt_top.mpr (by simp))).ne
      have hctr : ∀ j k, ∃ x : F, ∀ y ∈ C j k,
          dist (L.starProjection y) (L.starProjection x) ≤ Metric.diam (C j k) := by
        intro j k
        rcases (C j k).eq_empty_or_nonempty with h | ⟨x, hx⟩
        · exact ⟨0, fun y hy => absurd (h ▸ hy) (Set.notMem_empty y)⟩
        · refine ⟨x, fun y hy => ?_⟩
          rw [dist_eq_norm, ← map_sub]
          exact (L.norm_starProjection_apply_le _).trans
            ((dist_eq_norm y x).symm.trans_le (Metric.dist_le_diam_of_mem' (hfin j k) hy hx))
      choose x hx using hctr
      obtain ⟨ψ, hψdef⟩ : ∃ ψ : ℕ → F → ℝ≥0∞, ψ = fun j t => ∑' k,
          (closedBall (L.starProjection (x j k)) (Metric.diam (C j k))).indicator
            (fun _ => ediam (C j k) ^ (m : ℝ)) t := ⟨_, rfl⟩
      have hψm : ∀ j, Measurable (ψ j) := fun j => by
        rw [hψdef]
        exact Measurable.tsum fun k => measurable_const.indicator measurableSet_closedBall
      -- the slice covers
      have hslice : ∀ t, μH[(m : ℝ)] (Z ∩ {x | L.starProjection x = t}) ≤
          liminf (fun j => ψ j t) atTop := by
        intro t
        rw [hψdef]
        refine (Measure.hausdorffMeasure_le_liminf_tsum (m : ℝ) _ (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹)
          ?_ (fun (j k : ℕ) => C j k ∩ {x | L.starProjection x = t})
          (Eventually.of_forall fun j k => (ediam_mono inter_subset_left).trans (hdiam j k))
          (Eventually.of_forall fun j y hy => ?_)).trans
          (liminf_le_liminf (Eventually.of_forall fun j => ENNReal.tsum_le_tsum fun k => ?_))
        · exact (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun j => by
            simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        · obtain ⟨k, hk⟩ := mem_iUnion.mp (hZC j hy.1)
          exact mem_iUnion.mpr ⟨k, hk, hy.2⟩
        · rcases (C j k ∩ {x | L.starProjection x = t}).eq_empty_or_nonempty with h | ⟨y, hyC, hyt⟩
          · rw [h, ediam_empty, ENNReal.zero_rpow_of_pos (by exact_mod_cast hm0)]
            exact bot_le
          · rw [indicator_of_mem
              (show t ∈ closedBall (L.starProjection (x j k)) (Metric.diam (C j k))
              from hyt ▸ hx j k y hyC)]
            exact ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) (by positivity)
      -- integral bound
      obtain ⟨cB, hcB⟩ : ∃ c, (volume : Measure ↥L) (closedBall 0 1) = c := ⟨_, rfl⟩
      have hcBfin : cB ≠ ⊤ := hcB ▸ measure_closedBall_lt_top.ne
      have hψint : ∀ j, ∫⁻ t in (L : Set F), ψ j t ∂μHE[d] ≤ cB * ((j : ℝ≥0∞) + 1)⁻¹ := by
        intro j
        rw [hψdef, ← hmap,
          lintegral_tsum fun k =>
            (measurable_const.indicator measurableSet_closedBall).aemeasurable]
        calc ∑' k, ∫⁻ t, (closedBall (L.starProjection (x j k)) (Metric.diam (C j k))).indicator
              (fun _ => ediam (C j k) ^ (m : ℝ)) t ∂(volume.map Subtype.val)
            ≤ ∑' k, cB * ⨆ (_ : (C j k).Nonempty), ediam (C j k) ^ (n : ℝ) := by
              refine ENNReal.tsum_le_tsum fun k => ?_
              rw [lintegral_indicator_const measurableSet_closedBall, Measure.map_apply
                measurable_subtype_coe measurableSet_closedBall]
              have hball : (Subtype.val : ↥L → F) ⁻¹' closedBall (L.starProjection (x j k))
                  (Metric.diam (C j k)) = closedBall ⟨L.starProjection (x j k), by
                    rw [Submodule.starProjection_apply]; exact Submodule.coe_mem _⟩
                  (Metric.diam (C j k)) :=
                Set.ext fun _ => Iff.rfl
              rw [hball, Measure.addHaar_closedBall' _ _ Metric.diam_nonneg, hd, hcB]
              rcases (C j k).eq_empty_or_nonempty with h | h
              · rw [h, ediam_empty, ENNReal.zero_rpow_of_pos (by exact_mod_cast hm0), zero_mul]
                exact bot_le
              · rw [iSup_pos h, ENNReal.ofReal_pow Metric.diam_nonneg, Metric.diam,
                  ENNReal.ofReal_toReal (hfin j k), ← hmd, ENNReal.rpow_natCast,
                  ENNReal.rpow_natCast,
                  mul_comm cB, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hdn.le]
          _ = cB * ∑' k, ⨆ (_ : (C j k).Nonempty), ediam (C j k) ^ (n : ℝ) := ENNReal.tsum_mul_left
          _ ≤ cB * ((j : ℝ≥0∞) + 1)⁻¹ := mul_le_mul_right (hsum j).le _
      have hlim : ∫⁻ t in (L : Set F), liminf (fun j => ψ j t) atTop ∂μHE[d] = 0 := by
        refine le_antisymm ((lintegral_liminf_le hψm).trans ?_) bot_le
        have ht : Tendsto (fun j : ℕ => cB * ((j : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
          have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_inv_nat_nhds_zero.comp
            (tendsto_add_atTop_nat 1)) (Or.inr hcBfin)
          rw [mul_zero] at this
          exact this.congr fun j => by simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
        exact (liminf_le_liminf (Eventually.of_forall hψint)).trans_eq ht.liminf_eq
      filter_upwards [(lintegral_eq_zero_iff (Measurable.liminf hψm)).mp hlim] with t ht
      rw [hcH]
      exact le_antisymm ((hslice t).trans_eq ht) bot_le

    -- integrals over a disjoint union of pieces, up to a null set
    have hraf : ∀ (k : ℕ) (S : Set F) (A : ℕ → Set F), (∀ i, MeasurableSet (A i)) → (∀ i, A i ⊆ S) →
        Pairwise (fun i j => Disjoint (A i) (A j)) → μHE[k] (S \ ⋃ i, A i) = 0 →
        ∀ g : F → ℝ≥0∞, ∫⁻ y in S, g y ∂μHE[k] = ∑' i, ∫⁻ y in A i, g y ∂μHE[k] := by
      intro k S A hA hAS hdisj hnull g
      rw [← lintegral_iUnion hA hdisj]
      exact setLIntegral_congr (ae_eq_set.mpr ⟨hnull, by
        rw [sdiff_eq_empty.mpr (iUnion_subset hAS), measure_empty]⟩)
    have hPmeas : ∀ k, MeasurableSet (H k '' Ω k) := fun k =>
      (hptd (H k) (Ω k) (KH k) (cH k) (hKH k) (hΩm k) (hcH k) (hbH k)).1
    have hpm : ∀ t : F, MeasurableSet {x : F | L.starProjection x = t} := fun t =>
      measurableSet_eq_fun L.starProjection.continuous.measurable measurable_const
    have hZ := hT4 _ hnull
    -- **(ii)**
    have hii : ∀ g : F → ℝ≥0∞, Measurable g →
        AEMeasurable (fun t => ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[m])
          (μHE[d].restrict (L : Set F)) ∧
        ∫⁻ x in M, g x ∂μHE[n] = ∫⁻ t in (L : Set F),
          ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[m] ∂μHE[d] := by
      intro g hg
      have hsplitt : ∀ᵐ t ∂(μHE[d].restrict (L : Set F)),
          ∫⁻ x in M ∩ {x | L.starProjection x = t}, g x ∂μHE[m] =
            ∑' k, ∫⁻ x in H k '' Ω k ∩ {x | L.starProjection x = t}, g x ∂μHE[m] := by
        filter_upwards [hZ] with t ht
        refine hraf m _ (fun k => H k '' Ω k ∩ {x | L.starProjection x = t})
          (fun k => (hPmeas k).inter (hpm t)) (fun k => inter_subset_inter_left _ (hHM k))
          (fun k k' hkk' => (hdisj hkk').mono inter_subset_left inter_subset_left)
          (measure_mono_null (fun x hx => ?_) ht) g
        exact ⟨⟨hx.1.1, fun hx' => hx.2 (by
          obtain ⟨k, hk⟩ := mem_iUnion.mp hx'
          exact mem_iUnion.mpr ⟨k, hk, hx.1.2⟩)⟩, hx.1.2⟩
      refine ⟨(AEMeasurable.tsum fun k => ((hPP k).1 g hg).1).congr
        (hsplitt.mono fun t ht => ht.symm), ?_⟩
      rw [hraf n M (fun k => H k '' Ω k) hPmeas hHM hdisj hnull g, lintegral_congr_ae hsplitt,
        lintegral_tsum fun k => ((hPP k).1 g hg).1]
      exact tsum_congr fun k => ((hPP k).1 g hg).2
    -- local finiteness of almost every slice
    have hlocfin : ∀ᵐ t ∂(μHE[d].restrict (L : Set F)), ∀ C : Set F, IsCompact C →
        μHE[m] (M ∩ {x | L.starProjection x = t} ∩ C) ≠ ∞ := by
      have h1 : ∀ j : ℕ, ∀ᵐ t ∂(μHE[d].restrict (L : Set F)),
          μHE[m] (M ∩ {x | L.starProjection x = t} ∩ closedBall 0 j) ≠ ∞ := by
        intro j
        obtain ⟨hae, heq⟩ := hii ((closedBall (0 : F) j).indicator 1)
          (measurable_one.indicator measurableSet_closedBall)
        have hfin : ∫⁻ t in (L : Set F), ∫⁻ x in M ∩ {x | L.starProjection x = t},
            (closedBall (0 : F) j).indicator 1 x ∂μHE[m] ∂μHE[d] ≠ ∞ := by
          rw [← heq, lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, inter_comm]
          exact hloc _ (isCompact_closedBall _ _)
        filter_upwards [ae_lt_top' hae hfin] with t ht
        rw [lintegral_indicator_one measurableSet_closedBall,
          Measure.restrict_apply measurableSet_closedBall, inter_comm] at ht
        exact ht.ne
      filter_upwards [ae_all_iff.mpr h1] with t ht C hC
      obtain ⟨r, hr⟩ := hC.isBounded.subset_closedBall 0
      obtain ⟨j, hj⟩ := exists_nat_ge r
      exact ne_top_of_le_ne_top (ht j) (measure_mono (inter_subset_inter_right _
        (hr.trans (closedBall_subset_closedBall hj))))
    -- **(i)**
    refine ⟨?_, hii⟩
    have hslg : ∀ᵐ t ∂(μHE[d].restrict (L : Set F)), ∀ h : t ∈ L, ∀ k,
        ∀ᵐ s ∂(volume : Measure B), Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s)) ∈ Ω k →
          HasFDerivAt (fun s => H k (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s))))
            ((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s)))).comp jL) s ∧
          Injective ((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s)))).comp jL) ∧
          HasApproximateTangentSpaceAt n M (H k (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s))))
            (LinearMap.range (fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s))) : V →ₗ[ℝ] F)) ∧
          LinearMap.range (((fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s)))).comp jL :
              B →L[ℝ] F) : B →ₗ[ℝ] F) =
            LinearMap.range (fderiv ℝ (H k) (Θ.symm (WithLp.toLp 2 (⟨t, h⟩, s))) : V →ₗ[ℝ] F) ⊓
              Lᗮ := by
      rw [← hmap, hemb.ae_map_iff]
      filter_upwards [ae_all_iff.mpr fun k => (hPP k).2.1] with t ht _
      exact ht
    filter_upwards [hslg, hZ, hlocfin, ae_restrict_mem hLmeas] with t ht hZt hfin htL
    have hMt : MeasurableSet (M ∩ {x | L.starProjection x = t}) := hM.inter (hpm t)
    have hcov : (M ∩ {x | L.starProjection x = t}) \ ⋃ k,
        (fun s => H k (Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s)))) ''
          {s | Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s)) ∈ Ω k} ⊆
        (M \ ⋃ k, H k '' Ω k) ∩ {x | L.starProjection x = t} := by
      rintro x ⟨⟨hxM, hxt⟩, hx⟩
      refine ⟨⟨hxM, fun hx' => hx ?_⟩, hxt⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx'
      exact mem_iUnion.mpr ⟨k, by rw [((hPP k).2.2 ⟨t, htL⟩).2.2]; exact ⟨hk, hxt⟩⟩
    refine ⟨⟨(M \ ⋃ k, H k '' Ω k) ∩ {x | L.starProjection x = t}, hZt,
      fun k s => H k (Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s))), fun k => ((hPP k).2.2 ⟨t, htL⟩).1,
      fun x hx => ?_⟩, ?_⟩
    · by_cases hx' : x ∈ ⋃ k, H k '' Ω k
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hx'
        have hk' : x ∈ (fun s => H k (Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s)))) ''
            {s | Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s)) ∈ Ω k} := by
          rw [((hPP k).2.2 ⟨t, htL⟩).2.2]
          exact ⟨hk, hx.2⟩
        exact Or.inr (mem_iUnion.mpr ⟨k, image_subset_range _ _ hk'⟩)
      · exact Or.inl ⟨⟨hx.1, hx'⟩, hx.2⟩
    · refine hitt (M ∩ {x | L.starProjection x = t})
        (fun k s => H k (Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s))))
        (fun k => {s | Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s)) ∈ Ω k}) _ hMt
        (fun k => ((hPP k).2.2 ⟨t, htL⟩).1) (measure_mono_null hcov hZt) fun k => ?_
      obtain ⟨⟨K', hK'⟩, hBk, himg⟩ := (hPP k).2.2 ⟨t, htL⟩
      filter_upwards [ae_restrict_of_ae (ht htL k), ae_restrict_of_ae
        (hchB _ _ K' hK' hMt hfin), ae_restrict_mem hBk] with s hs1 hs2 hsB
      obtain ⟨hD, hinj, hT, hrange⟩ := hs1 hsB
      intro Q hQ
      have hmem : H k (Θ.symm (WithLp.toLp 2 (⟨t, htL⟩, s))) ∈ M ∩ {x | L.starProjection x = t} :=
        (inter_subset_inter_left _ (hHM k)) (himg ▸ mem_image_of_mem _ hsB)
      have hTm := hs2 hmem hD.differentiableAt (by rw [hD.fderiv]; exact hinj)
      rw [hD.fderiv, hrange] at hTm
      rw [hQ.unique hT]
      exact hTm

  -- instantiate at `ℝⁿ, ℝᴾ, ℝᵐ` with the accepted lemmas and the sibling `lipschitz_tangent`
  exact master (Euclid n) (Euclid P) (Euclid (n - Module.finrank ℝ L)) n (Module.finrank ℝ L)
    (n - Module.finrank ℝ L) L M finrank_euclideanSpace_fin finrank_euclideanSpace_fin rfl hdn rfl
    hM hloc htan (Submission.dpf_rectifiable_bilipschitz_pieces P n M hM hrect)
    (Submission.ptd_piece_image_measurable_ae_pullback P n)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P n G Y K
      (Nat.lt_of_le_of_lt (Nat.zero_le _) hdn) hG hY hYl)
    (fun G Y K hG hY hYl => Submission.idtp_fons_cs_sos_lipschitz_approx_tangent P _ G Y K
      (Nat.sub_pos_of_lt hdn) hG hY hYl)
    (Submission.dpf_itt_ae_of_ae_pieces P _)
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

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
