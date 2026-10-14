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
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
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

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0

/-- **Simon Ch. 6, 3.2(3) and 2.11–2.12**: if `T = τ(M, θ, ξ)` in the open set `U`, then
(i) `M_W(T) = μ_R(W)` for every open `W`, where `μ_R = θ Hⁿ⌞M`, and (ii) `spt T = U ∩ spt μ_R`.
`M_W(T) ≤ μ_R(W)` because admissible forms pair with `ξ` to at most `1`; `μ_R(W) ≤ M_W(T)` by
smoothing the dual covector field of `ξ` (Lusin); (ii) follows from (i) alone. -/
theorem Submission.dor_imrep_massOn_eq_measure_and_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) ∧ T.support = U ∩ R.measure.support := by
  intro P n U T R hU hR
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  exact ⟨hmass, Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass⟩
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

/-- **Simon Ch. 6, 2.27–2.29 and 3.9** (analytic toolkit, and the Lipschitz push-forward of
integer multiplicity currents vanishing off a compact set).  (i) If `X = τ(M, θ, ξ)` in `ℝᴾ`
vanishes off the compact `E`, then `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`, so `Hᵏ(M ∖ E) = 0` (`θ ≥ 1`
on `M`), `M(X) = μ_R(ℝᴾ) = μ_R(E) < ∞`, and `R.action γ` depends only on `γ|_E`.  (ii) Hadamard:
`|α(v)| ≤ |α| ∏ᵢ |vᵢ|`, from `|α(v)| ≤ |α| det(⟨vᵢ, vⱼ⟩)^{1/2}` and a Gram–Schmidt frame with
`det(⟨vᵢ, vⱼ⟩) = (det A)²`, `|det A| ≤ ∏ᵢ |vᵢ|`.  (iii) `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` a.e. with `τ`
orthonormal, so `|θ ξ(γ)| ≤ c θ` and `|R.action γ| ≤ c μ_R(ℝᴾ)`.  (iv) `F_j = ψ_j ⋆ F` with
normalized `C^∞` bumps `ψ_j` supported in `B_{1/(j+1)}(0)` are `Λ`-Lipschitz and
`|F_j - F| ≤ Λ/(j+1)`.  (v) A smooth Urysohn function for `cthickening 1 E ⊆ thickening 2 E`.
(vi) Given (IPF), `push k F X = Y_X(F)` for `Y_X` from (IPF) for a chosen finite-mass
representation of `X`: it is integer multiplicity, depends only on `F|_E`, is the limit of
`X(η_j) = R.action(F_j^#ω)`, has `M ≤ Λᵏ M(X)` (Hadamard with `‖DF_j‖ ≤ Λ`, then (iii)), and
vanishes off `F(E)` (for large `j`, `F_j(E)` avoids `spt ω`). -/
theorem Submission.dor_lmb_fcdp_toolkit_push : ((∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ') ∧ (∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal) ∧ (∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop) ∧ ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1) ∧ ((∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (Λ : NNReal) (F : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ (∀ F' : Euclid P → Euclid P, LipschitzWith Λ F' → EqOn F F' E → push k F X = push k F' X) ∧ (∀ (Fs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (push k F X ω))) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) := by
  -- (i) compactly vanishing integer multiplicity representations
  have hi : ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ' := by
    intro P k X R E hR hE hXE
    have hmass :=
      (Submission.dor_imrep_massOn_eq_measure_and_support P k univ X R isOpen_univ hR).1
    have hEm : MeasurableSet E := hE.isClosed.measurableSet
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
    -- `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`: admissible forms supported off `E` are killed by `X`
    have hμEc : R.measure Eᶜ = 0 := by
      rw [← hmass Eᶜ hE.isClosed.isOpen_compl]
      refine le_antisymm (sSup_le ?_) bot_le
      rintro _ ⟨ω, ⟨hωE, -⟩, rfl⟩
      dsimp only
      rw [hXE ω (subset_compl_iff_disjoint_right.mp hωE), ENNReal.ofReal_zero]
    -- `Hᵏ(M ∖ E) = 0`, since `θ ≥ 1` on `M`
    have hnull : μHE[k] (R.carrier \ E) = 0 := by
      rw [IMRep.measure, withDensity_apply_eq_zero' hθ.aemeasurable,
        Measure.restrict_apply' R.measurableSet_carrier] at hμEc
      refine measure_mono_null ?_ hμEc
      intro x hx
      exact ⟨⟨Nat.cast_ne_zero.mpr (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    -- `Hᵏ⌞M`-a.e. point lies in `E`
    have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
      rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
      refine measure_mono_null ?_ hnull
      intro x hx
      exact ⟨hx.2, hx.1⟩
    -- `μ_R(ℝᴾ) = μ_R(E) = ∫_{M ∩ E} θ dHᵏ < ∞`
    have hfin : R.measure univ ≠ ∞ := by
      rw [← measure_add_measure_compl hEm, hμEc, add_zero, IMRep.measure, withDensity_apply _ hEm,
        Measure.restrict_restrict hEm, inter_comm]
      exact R.locallyIntegrable_mult E hE (subset_univ E)
    refine ⟨hnull, hmass univ isOpen_univ, hfin, fun γ γ' hγ => ?_⟩
    -- the integrands agree on `E`, hence `Hᵏ⌞M`-a.e.
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hγ hx]
  -- (ii) Hadamard's inequality for the Euclidean coefficient norm
  have hii : ∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ := by
    intro N m α v
    by_cases hv : LinearIndependent ℝ v
    · obtain ⟨σ, -, -, hG, -, hA⟩ := Submission.dpf_exists_orthonormal_frame_det_gram N m v hv
      calc |α v| ≤ covectorEuclideanNorm α *
            Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j))) :=
            (Submission.covectorEuclideanNorm_gram_bounds N m).1 α v
        _ = covectorEuclideanNorm α * |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| := by
            rw [hG, Real.sqrt_sq_eq_abs]
        _ ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ :=
            mul_le_mul_of_nonneg_left hA (covectorEuclideanNorm_nonneg α)
    · -- a linearly dependent family is killed by every alternating map
      rw [show α v = 0 from α.toAlternatingMap.map_linearDependent v hv, abs_zero]
      exact mul_nonneg (covectorEuclideanNorm_nonneg α)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
  -- (iii) the action is bounded by `c μ_R(ℝᴾ)` when `γ` is bounded by `c` on orthonormal frames
  have hiii : ∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal := by
    intro P k U R γ c hfin hc hγ
    have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
    -- `∫⁻ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`, so `θ` is `Hᵏ⌞M`-integrable with `∫ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`
    have hlint : ∫⁻ x, ENNReal.ofReal (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) =
        R.measure univ := by
      rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_congr fun x => ENNReal.ofReal_natCast _
    have hθ0 : 0 ≤ᵐ[μHE[k].restrict R.carrier] fun x => (R.mult x : ℝ) :=
      ae_of_all _ fun x => Nat.cast_nonneg _
    have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) :=
      ⟨hθm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hθ0).mpr (hlint ▸ hfin.lt_top)⟩
    have hθI : ∫ x, (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) = (R.measure univ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hθ0 hθm.aestronglyMeasurable, hlint]
    rw [← Real.norm_eq_abs, IMRep.action]
    calc ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (γ x) ∂μHE[k]‖
        ≤ ∫ x, c * (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) := by
          refine norm_integral_le_of_norm_le (hθint.const_mul c) ?_
          -- a.e. `ξ(x)(β) = ±β(τ)` with `τ` orthonormal, so `|ξ(x)(γ x)| = |γ(x)(τ)| ≤ c`
          filter_upwards [hγ, R.orients] with x hx hor
          obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hor
          rw [norm_mul, Real.norm_natCast, mul_comm c]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rcases hξ with h | h
          · rw [h, Real.norm_eq_abs]
            exact hx τ hτ
          · rw [h, norm_neg, Real.norm_eq_abs]
            exact hx τ hτ
      _ = c * (R.measure univ).toReal := by rw [integral_const_mul, hθI]
  -- (iv) `C^∞` `Λ`-Lipschitz approximations by mollification
  have hiv : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop := by
    intro N N' Λ F hF
    -- normalized `C^∞` bumps `ψ = φ / ∫ φ` supported in `B_r(0)`
    have hker : ∀ r : ℝ, 0 < r → ∃ ψ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧ support ψ ⊆ ball 0 r := by
      intro r hr
      let φ : ContDiffBump (0 : Euclid N) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hr
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    choose ψ hψ hψc hψ0 hψ1 hψs using fun j : ℕ =>
      hker (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hFi : LocallyIntegrable F volume := hF.continuous.locallyIntegrable
    refine ⟨fun j => convolution (ψ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      fun j => (hψc j).contDiff_convolution_left _ (hψ j) hFi, fun j => ?_, ?_⟩
    · -- `ψ_j ⋆ F` is `Λ`-Lipschitz: it averages the differences `F(x - t) - F(x' - t)`
      have hconv : ∀ x, Integrable (fun t => ψ j t • F (x - t)) volume := fun x =>
        ((hψc j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hψ j).continuous hFi
          x).integrable
      refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      dsimp only
      rw [dist_eq_norm, convolution_def, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
      rw [← integral_sub (hconv x) (hconv x')]
      calc ‖∫ t, (ψ j t • F (x - t) - ψ j t • F (x' - t))‖ ≤ ∫ t, ψ j t * (Λ * dist x x') := by
            refine norm_integral_le_of_norm_le
              (((hψ j).continuous.integrable_of_hasCompactSupport (hψc j)).mul_const _)
              (ae_of_all _ fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hψ0 j t)]
            refine mul_le_mul_of_nonneg_left ?_ (hψ0 j t)
            rw [← dist_eq_norm]
            calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
              _ = Λ * dist x x' := by rw [dist_sub_right]
        _ = Λ * dist x x' := by rw [integral_mul_const, hψ1 j, one_mul]
    · -- `dist((ψ_j ⋆ F)(x), F(x)) ≤ Λ/(j+1)`, as `F` moves by `≤ Λ/(j+1)` on `B_{1/(j+1)}(x)`
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hlim : Tendsto (fun j : ℕ => (Λ : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
        rwa [mul_zero] at this
      filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj x
      rw [dist_comm]
      refine (dist_convolution_le (by positivity) (hψs j) (hψ0 j) (hψ1 j)
        hF.continuous.aestronglyMeasurable fun y hy => ?_).trans_lt hj
      calc dist (F y) (F x) ≤ Λ * dist y x := hF.dist_le_mul y x
        _ ≤ Λ * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left (mem_ball.mp hy).le Λ.coe_nonneg
  -- (v) smooth cut-off functions
  have hv : ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1 := by
    intro P E hE
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := 2) (E := E)) (isClosed_cthickening (δ := 1) (E := E))
      (cthickening_subset_thickening' two_pos one_lt_two E)
    refine ⟨χ, thickening 1 E, hχ, ?_, fun x => hχr ⟨x, rfl⟩, isOpen_thickening,
      self_subset_thickening one_pos E,
      fun x hx => (hχ1 x).mp (thickening_subset_cthickening 1 E hx)⟩
    exact HasCompactSupport.of_support_subset_isCompact (hE.cthickening (r := 2))
      (hχs ▸ thickening_subset_cthickening 2 E)
  refine ⟨⟨hi, hii, hiii, hiv, hv⟩, ?_⟩
  -- (vi) the push-forward operator, assuming (IPF)
  intro hIPF P
  -- for `X` with a finite-mass IM representation `R`, choose `Y_X` from (IPF) for `R`
  obtain ⟨Ych, hYch⟩ : ∃ Ych : ∀ k : ℕ, GeometricCurrentOn (univ : Set (Euclid P)) k →
      (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k,
      ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
        (∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧ R.measure univ ≠ ∞) →
        ∃ (R : IMRep (univ : Set (Euclid P)) k) (hR : R.measure univ ≠ ∞),
          R.Represents X ∧ Ych k X = Classical.choose (hIPF P P k R hR) := by
    classical
    exact ⟨fun k X => if h : ∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧
      R.measure univ ≠ ∞ then Classical.choose (hIPF P P k h.choose h.choose_spec.2)
      else fun _ => X, fun k X h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1, dite_eq_left h⟩⟩
  refine ⟨fun k F X => Ych k X F, ?_⟩
  rintro k Λ F E X hF hE ⟨R', hR'⟩ hXE
  dsimp only
  -- by (i) every representation of `X` has finite mass
  obtain ⟨R, hRfin, hRX, hY⟩ := hYch k X ⟨R', hR', (hi P k X R' E hR' hE hXE).2.2.1⟩
  obtain ⟨hYa, hYb⟩ := Classical.choose_spec (hIPF P P k R hRfin)
  rw [← hY] at hYa hYb
  obtain ⟨hnull, hmass, -, hloc⟩ := hi P k X R E hRX hE hXE
  have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨hx.2, hx.1⟩
  -- `C^∞` `Λ`-Lipschitz `F_j → F` by (iv); `push k F X (ω) = lim R.action(F_j^#ω)`
  obtain ⟨Fs, hFs, hFsL, hFsU⟩ := hiv P P Λ F hF
  have hFs1 : ∀ j, ContDiff ℝ 1 (Fs j) := fun j => (hFs j).of_le (by exact_mod_cast le_top)
  have hlim := (hYa F Λ hF).2 Fs hFs1 hFsL hFsU
  refine ⟨(hYa F Λ hF).1, fun F' hF' hFF' => hYb F F' Λ hF hF' ?_,
    fun Fs' ω ηs hFs' hFsL' hFsU' hη => ?_, ?_, fun ω hω => ?_⟩
  · -- (P2): `F = F'` on `E`, hence `Hᵏ⌞M`-a.e.
    filter_upwards [hae] with x hx using hFF' hx
  · -- (P3): `X(η_j) = R.action(η_j) = R.action(F_j^#ω) → push k F X (ω)`
    refine ((hYa F Λ hF).2 Fs' hFs' hFsL' hFsU' ω).congr fun j => ?_
    rw [hRX (ηs j)]
    exact hloc _ _ fun x hx => (hη j x hx).symm
  · -- (P4): for admissible `ω`, `|R.action(F_j^#ω)| ≤ Λᵏ μ_R(ℝᴾ)` by (ii) and (iii)
    rw [hmass, GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨-, hω1⟩, rfl⟩
    dsimp only
    have hbd : ∀ j, |R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))| ≤
        (Λ : ℝ) ^ k * (R.measure univ).toReal := by
      intro j
      refine hiii P k univ R _ _ hRfin (by positivity) (ae_of_all _ fun x τ hτ => ?_)
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      calc |(ω : DifferentialForm (Euclid P) k) (Fs j x) (fderiv ℝ (Fs j) x ∘ τ)|
          ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) (Fs j x)) *
            ∏ i, ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ := hii P k _ _
        _ ≤ 1 * ∏ _i : Fin k, (Λ : ℝ) := by
          refine mul_le_mul (hω1 _)
            (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
            (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
          -- `‖DF_j(x) τᵢ‖ ≤ ‖DF_j(x)‖ ≤ Λ`
          calc ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ ≤ ‖fderiv ℝ (Fs j) x‖ * ‖τ i‖ :=
                (fderiv ℝ (Fs j) x).le_opNorm _
            _ ≤ Λ := by
                rw [hτ.1 i, mul_one]
                exact norm_fderiv_le_of_lipschitz ℝ (hFsL j)
        _ = (Λ : ℝ) ^ k := by rw [one_mul, Fin.prod_const]
    have hle : Ych k X F ω ≤ (Λ : ℝ) ^ k * (R.measure univ).toReal :=
      le_of_tendsto' (hlim ω) fun j => (le_abs_self _).trans (hbd j)
    calc ENNReal.ofReal (Ych k X F ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * (R.measure univ).toReal) := ENNReal.ofReal_le_ofReal hle
      _ = (Λ : ℝ≥0∞) ^ k * R.measure univ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hRfin,
          ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
  · -- (P5): for large `j`, `F_j(E)` avoids `spt ω`, so `F_j^#ω = 0` on `E`
    obtain ⟨δ, hδ, hδK⟩ := (hE.image hF.continuous).exists_cthickening_subset_open
      (isClosed_tsupport _).isOpen_compl (subset_compl_iff_disjoint_left.mpr hω)
    have hev : ∀ᶠ j in atTop, R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) = 0 := by
      filter_upwards [Metric.tendstoUniformly_iff.mp hFsU δ hδ] with j hj
      refine (hloc _ 0 fun x hx => ?_).trans ?_
      · have hmem : Fs j x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
          hδK (thickening_subset_cthickening δ _
            (mem_thickening_iff.mpr ⟨F x, mem_image_of_mem F hx, by rw [dist_comm]; exact hj x⟩))
        rw [image_eq_zero_of_notMem_tsupport hmem]
        ext v
        simp
      · simp [IMRep.action]
    exact tendsto_nhds_unique (hlim ω) (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm))
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable
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

/-- **The cylinder over a rectifiable set** (the carrier of `[[(0,1)]] × T`, Simon Ch. 6, 2.17–2.21
and the proof of 2.27): let `M ⊆ ℝᴾ` be Borel and countably `k`-rectifiable with `Hᵏ(M) < ∞`, and
let `ι(t, x) = (t, x₁, …, x_P)`.  There is a Borel `C ⊆ ι((0,1) × M)` which is countably
`(k+1)`-rectifiable, satisfies `Hᵏ⁺¹⌞C = ι_#(L¹⌞(0,1) ⊗ Hᵏ⌞M)`, and for `Hᵏ⁺¹`-a.e. `y ∈ C`, if `M`
has approximate tangent space `Q` at `(y₁, …, y_P)` then `C` has approximate tangent space
`ℝe₀ ⊕ Q` at `y`.  Cut `M` into bi-Lipschitz pieces `F i (B i)` up to an `Hᵏ`-null set and take
`C = ι((0,1) × ⋃ F i (B i))`, parametrized by `G i(b) = ι(b₀, F i(b₁, …, b_k))` on
`π⁻¹((0,1) × B i)`, `π(b) = (b₀, (b₁, …, b_k))`.  The Gram matrix of `DG i(b)` is
`diag(1, Gram DF i)`, so `JG i = JF i ∘ π₂`; the area formula for `G i` and for `F i`, the measure
preserving `π` and Tonelli give the measure identity.  The tangent planes come from the piece lemma
for `F i` on `M` and for `G i` on `C`, with `range DG i(b) = ℝe₀ ⊕ range DF i(π₂ b)`. -/
theorem Submission.dor_lmb_fcdp_cylinder : ∀ (P k : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable k M → μHE[k] M ≠ ∞ → ∃ C : Set (Euclid (P + 1)), MeasurableSet C ∧ C ⊆ (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ M) ∧ CountablyRectifiable (k + 1) C ∧ μHE[k + 1].restrict C = ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict M)).map (fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) ∧ ∀ᵐ y ∂(μHE[k + 1].restrict C), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k M (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P) Q → HasApproximateTangentSpaceAt (k + 1) C y (Submodule.span ℝ (insert (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) ((fun v : Euclid P => (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Q : Set (Euclid P))))) := by
  intro P k M hM hrect hfin
  -- `ι_n(t, x) = (t, x₁, …, x_n)` and `π_n(y) = (y₀, (y₁, …, y_n))`, mutually inverse linear maps
  have hι : ∀ n : ℕ, ∃ L : ℝ × Euclid n →L[ℝ] Euclid (n + 1), ∀ p, L p =
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) : Euclid (n + 1)) := by
    intro n
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun p =>
          (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) : Euclid (n + 1))
        map_add' := ?_
        map_smul' := ?_ }, fun p => rfl⟩
    · intro p q
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · intro c p
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hπ : ∀ n : ℕ, ∃ L : Euclid (n + 1) →L[ℝ] ℝ × Euclid n, ∀ y,
      L y = (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid n)) := by
    intro n
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun y => (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid n))
        map_add' := ?_
        map_smul' := ?_ }, fun p => rfl⟩
    · intro p q
      ext <;> simp [Fin.tail]
    · intro c p
      ext <;> simp [Fin.tail]
  choose ιL hιL using hι
  choose πL hπL using hπ
  have hπι : ∀ n p, πL n (ιL n p) = p := by
    intro n p
    rw [hιL, hπL]
    simp
  have hιπ : ∀ n y, ιL n (πL n y) = y := by
    intro n y
    rw [hπL, hιL]
    simp
  have hinner : ∀ n p q, inner ℝ (ιL n p) (ιL n q) = p.1 * q.1 + inner ℝ p.2 q.2 := by
    intro n p q
    rw [hιL, hιL, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp [mul_comm]
  have hnorm : ∀ n p, ‖ιL n p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
    intro n p
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner, sq]
  have hιinj : ∀ n, Injective (ιL n) := fun n => LeftInverse.injective (hπι n)
  -- A1: `π_n` maps Lebesgue measure on `ℝⁿ⁺¹` to Lebesgue measure on `ℝ × ℝⁿ`
  have hπmp : ∀ n, MeasurePreserving (πL n) volume volume := by
    intro n
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin n))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).comp
        (PiLp.volume_preserving_ofLp (Fin (n + 1))))
    convert h using 1
    funext y
    rw [hπL]
    simp [MeasurableEquiv.piFinSuccAbove_apply]
  have hπe0 : ∀ n, πL n (EuclideanSpace.single 0 1) = (1, 0) := by
    intro n
    rw [hπL]
    ext
    · simp
    · simp [Fin.tail]
  have hπes : ∀ n (j : Fin n),
      πL n (EuclideanSpace.single j.succ 1) = (0, EuclideanSpace.single j 1) := by
    intro n j
    rw [hπL]
    ext l
    · simp
    · simp [Fin.tail, PiLp.single_apply]
  -- the statement's `ι`, `J`, `ê₀` and `pr` in terms of `ι_P` and `π_P`
  have hιfun : (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
      ιL P := funext fun p => (hιL P p).symm
  have hJfun : (fun v : Euclid P =>
      (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
      fun v => ιL P (0, v) := funext fun v => (hιL P (0, v)).symm
  have he0 : (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) = ιL P (1, 0) := by
    rw [← hπe0, hιπ]
  have hpr : ∀ y : Euclid (P + 1),
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P) = (πL P y).2 := fun y => by rw [hπL]
  rw [hιfun, hJfun, he0]
  simp only [hpr]
  -- B1: the bi-Lipschitz pieces `F i (B i)` of `M` (accepted `dpf_rectifiable_bilipschitz_pieces`)
  obtain ⟨F, B, m, hFL, hB, hm, hbi, hdiff, hFBm, hFBM, hdisj, hnull⟩ :=
    Submission.dpf_rectifiable_bilipschitz_pieces P k M hM hrect
  choose L hL using hFL
  have hFinj : ∀ i, InjOn (F i) (B i) := by
    intro i a ha a' ha' h
    have h1 := hbi i a ha a' ha'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖a - a'‖ ≤ 0 := by nlinarith [norm_nonneg (a - a'), hm i]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  -- `A i = F i (B i)`, `C i = ι((0,1) × A i)`, `G i = ι ∘ (id × F i) ∘ π` on
  -- `Bh i = π⁻¹((0,1) × B i)`
  set A : ℕ → Set (Euclid P) := fun i => F i '' B i
  set C : ℕ → Set (Euclid (P + 1)) := fun i => ιL P '' (Ioo (0 : ℝ) 1 ×ˢ A i)
  set G : ℕ → Euclid (k + 1) → Euclid (P + 1) := fun i b => ιL P ((πL k b).1, F i (πL k b).2)
  set Bh : ℕ → Set (Euclid (k + 1)) := fun i => πL k ⁻¹' (Ioo (0 : ℝ) 1 ×ˢ B i)
  have hmeas_img : ∀ T : Set (ℝ × Euclid P), MeasurableSet T → MeasurableSet (ιL P '' T) :=
    fun T hT => hT.image_of_continuousOn_injOn (ιL P).continuous.continuousOn (hιinj P).injOn
  have hCm : ∀ i, MeasurableSet (C i) := fun i => hmeas_img _ (measurableSet_Ioo.prod (hFBm i))
  have hCU : ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i) = ⋃ i, C i := by
    rw [prod_iUnion, image_iUnion]
  have hCdisj : Pairwise (Disjoint on C) := fun i j hij =>
    (disjoint_image_iff (hιinj P)).mpr (disjoint_prod.mpr (Or.inr (hdisj hij)))
  have hBhm : ∀ i, MeasurableSet (Bh i) := fun i =>
    (measurableSet_Ioo.prod (hB i)).preimage (πL k).continuous.measurable
  have hGC : ∀ i, G i '' Bh i = C i := by
    intro i
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨((πL k b).1, F i (πL k b).2), ⟨hb.1, mem_image_of_mem _ hb.2⟩, rfl⟩
    · rintro ⟨⟨t, x⟩, ⟨ht, u, hu, rfl⟩, rfl⟩
      refine ⟨ιL k (t, u), ?_, ?_⟩
      · show πL k (ιL k (t, u)) ∈ Ioo (0 : ℝ) 1 ×ˢ B i
        rw [hπι]
        exact ⟨ht, hu⟩
      · show ιL P ((πL k (ιL k (t, u))).1, F i (πL k (ιL k (t, u))).2) = ιL P (t, F i u)
        rw [hπι]
  -- A2: `G i` is Lipschitz
  have hGlip : ∀ i, ∃ K, LipschitzWith K (G i) := fun i =>
    ⟨_, (ιL P).lipschitzWith.comp ((LipschitzWith.prod_fst.comp (πL k).lipschitzWith).prodMk
      ((hL i).comp (LipschitzWith.prod_snd.comp (πL k).lipschitzWith)))⟩
  -- A3: `DG i(b) c = ι(c₀, DF i(π₂ b)(π₂ c))`, which is injective
  have hGd : ∀ i, ∀ b ∈ Bh i, HasFDerivAt (G i) ((ιL P).comp
      (((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) b := by
    intro i b hb
    have h1 : HasFDerivAt (Prod.map (id : ℝ → ℝ) (F i))
        ((ContinuousLinearMap.id ℝ ℝ).prodMap (fderiv ℝ (F i) (πL k b).2)) (πL k b) :=
      HasFDerivAt.prodMap (πL k b) (hasFDerivAt_id _) (hdiff i _ hb.2).1.hasFDerivAt
    exact (ιL P).hasFDerivAt.comp b (h1.comp b (πL k).hasFDerivAt)
  have hDap : ∀ i b c, ((ιL P).comp (((ContinuousLinearMap.id ℝ ℝ).prodMap
      (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) c =
      ιL P ((πL k c).1, fderiv ℝ (F i) (πL k b).2 (πL k c).2) := fun _ _ _ => rfl
  have hGdinj : ∀ i, ∀ b ∈ Bh i, Injective (fderiv ℝ (G i) b) := by
    intro i b hb c c' h
    rw [(hGd i b hb).fderiv, hDap, hDap] at h
    obtain ⟨h3, h4⟩ := Prod.mk.inj (hιinj P h)
    rw [← hιπ k c, ← hιπ k c']
    exact congrArg (ιL k) (Prod.ext h3 ((hdiff i _ hb.2).2 h4))
  -- A4: the Gram matrix of `DG i(b)` is `diag(1, Gram DF i(π₂ b))`, so `JG i(b) = JF i(π₂ b)`
  have hGJ : ∀ i, ∀ b ∈ Bh i, Real.sqrt (Matrix.det (Matrix.of fun a c : Fin (k + 1) =>
      inner ℝ (fderiv ℝ (G i) b (EuclideanSpace.single a 1))
        (fderiv ℝ (G i) b (EuclideanSpace.single c 1)))) =
      Real.sqrt (Matrix.det (Matrix.of fun a c : Fin k =>
        inner ℝ (fderiv ℝ (F i) (πL k b).2 (EuclideanSpace.single a 1))
          (fderiv ℝ (F i) (πL k b).2 (EuclideanSpace.single c 1)))) := by
    intro i b hb
    rw [(hGd i b hb).fderiv, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp only [Matrix.of_apply, hDap, hπe0, hπes, hinner, map_zero, inner_zero_left,
      inner_zero_right, Fin.succAbove_zero, mul_zero, zero_mul, add_zero, mul_one, Fin.val_zero,
      pow_zero, one_mul, Finset.sum_const_zero]
    congr 2
    ext a c
    simp only [Matrix.submatrix_apply, Matrix.of_apply, hπes, zero_mul, zero_add]
  -- B5(d): `range DG i(b) = span{ê₀} ⊔ J(range DF i(π₂ b))`
  have hGrange : ∀ i, ∀ b ∈ Bh i,
      LinearMap.range (fderiv ℝ (G i) b : Euclid (k + 1) →ₗ[ℝ] Euclid (P + 1)) =
      Submodule.span ℝ (insert (ιL P (1, 0)) ((fun v => ιL P (0, v)) ''
        (LinearMap.range (fderiv ℝ (F i) (πL k b).2 : Euclid k →ₗ[ℝ] Euclid P) :
          Set (Euclid P)))) := by
    intro i b hb
    rw [(hGd i b hb).fderiv]
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      have hsplit : ιL P ((πL k c).1, fderiv ℝ (F i) (πL k b).2 (πL k c).2) =
          (πL k c).1 • ιL P (1, 0) + ιL P (0, fderiv ℝ (F i) (πL k b).2 (πL k c).2) := by
        rw [← map_smul, ← map_add]
        congr 1
        ext <;> simp
      show ((ιL P).comp (((ContinuousLinearMap.id ℝ ℝ).prodMap
        (fderiv ℝ (F i) (πL k b).2)).comp (πL k))) c ∈ _
      rw [hDap, hsplit]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (mem_insert _ _)))
        (Submodule.subset_span (mem_insert_of_mem _ ⟨_, ⟨_, rfl⟩, rfl⟩))
    · rw [Submodule.span_le]
      rintro _ (rfl | ⟨_, ⟨w, rfl⟩, rfl⟩)
      · exact ⟨EuclideanSpace.single 0 1,
          by simp only [ContinuousLinearMap.coe_coe, hDap, hπe0, map_zero]⟩
      · exact ⟨ιL k (0, w), by simp only [ContinuousLinearMap.coe_coe, hDap, hπι]⟩
  -- B5(b): `min(1, m i) |b − b'| ≤ |G i b − G i b'|` on `Bh i`
  have hGlow : ∀ i, ∀ b ∈ Bh i, ∀ b' ∈ Bh i, min 1 (m i) * ‖b - b'‖ ≤ ‖G i b - G i b'‖ := by
    intro i b hb b' hb'
    have h1 : G i b - G i b' =
        ιL P ((πL k b).1 - (πL k b').1, F i (πL k b).2 - F i (πL k b').2) := by
      rw [← map_sub]
      rfl
    have h2 : b - b' = ιL k ((πL k b).1 - (πL k b').1, (πL k b).2 - (πL k b').2) := by
      rw [show ((πL k b).1 - (πL k b').1, (πL k b).2 - (πL k b').2) = πL k (b - b') by
        rw [map_sub]; rfl, hιπ]
    have hX : ‖b - b'‖ ^ 2 =
        ((πL k b).1 - (πL k b').1) ^ 2 + ‖(πL k b).2 - (πL k b').2‖ ^ 2 := by
      rw [h2, hnorm]
    have hY : ‖G i b - G i b'‖ ^ 2 =
        ((πL k b).1 - (πL k b').1) ^ 2 + ‖F i (πL k b).2 - F i (πL k b').2‖ ^ 2 := by
      rw [h1, hnorm]
    have hμ0 : 0 < min 1 (m i) := lt_min one_pos (hm i)
    have hμT : min 1 (m i) * ‖(πL k b).2 - (πL k b').2‖ ≤ ‖F i (πL k b).2 - F i (πL k b').2‖ :=
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans (hbi i _ hb.2 _ hb'.2)
    have e1 : min 1 (m i) ^ 2 * ((πL k b).1 - (πL k b').1) ^ 2 ≤ ((πL k b).1 - (πL k b').1) ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hμ0.le (min_le_left _ _))
    have e2 : (min 1 (m i) * ‖(πL k b).2 - (πL k b').2‖) ^ 2 ≤
        ‖F i (πL k b).2 - F i (πL k b').2‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hμ0.le (norm_nonneg _)) hμT 2
    refine (pow_le_pow_iff_left₀ (mul_nonneg hμ0.le (norm_nonneg _)) (norm_nonneg _)
      two_ne_zero).mp ?_
    rw [mul_pow, hX, hY, mul_add, ← mul_pow (min 1 (m i)) ‖(πL k b).2 - (πL k b').2‖]
    exact add_le_add e1 e2
  have hGinj : ∀ i, InjOn (G i) (Bh i) := by
    intro i b hb b' hb' h
    have h1 := hGlow i b hb b' hb'
    rw [h, sub_self, norm_zero] at h1
    have h2 : ‖b - b'‖ ≤ 0 := by nlinarith [norm_nonneg (b - b'), lt_min one_pos (hm i)]
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  have hfinA : ∀ i, IsFiniteMeasure (μHE[k].restrict (A i)) := fun i =>
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top hfin (measure_mono (hFBM i)))
  -- A5–A6: `Hᵏ⁺¹⌞C i = ι_#(L¹⌞(0,1) ⊗ Hᵏ⌞A i)`, by the area formula (accepted
  -- `codim1_lura_gram_area_formula`) for `G i` and for `F i`, the measure preserving `π`
  -- and Tonelli
  have hpiece : ∀ i, μHE[k + 1].restrict (C i) =
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict (A i))).map (ιL P) := by
    intro i
    have := hfinA i
    obtain ⟨hJm, hGA⟩ := Submission.codim1_lura_gram_area_formula k P (F i)
    have hGAh := (Submission.codim1_lura_gram_area_formula (k + 1) (P + 1) (G i)).2 (Bh i)
      (hBhm i) (fun b hb => (hGd i b hb).differentiableAt) (hGdinj i) (hGinj i)
    ext S hS
    have hιS : MeasurableSet (ιL P ⁻¹' S) := (ιL P).continuous.measurable hS
    have hhm : Measurable fun p : ℝ × Euclid k => ENNReal.ofReal (Real.sqrt (Matrix.det
        (Matrix.of fun a c : Fin k => inner ℝ (fderiv ℝ (F i) p.2 (EuclideanSpace.single a 1))
          (fderiv ℝ (F i) p.2 (EuclideanSpace.single c 1))))) *
        S.indicator 1 (ιL P (p.1, F i p.2)) :=
      (ENNReal.measurable_ofReal.comp (hJm.comp measurable_snd)).mul
        ((measurable_one.indicator hS).comp ((ιL P).continuous.comp
          (continuous_fst.prodMk ((hL i).continuous.comp continuous_snd))).measurable)
    rw [← lintegral_indicator_one (μ := μHE[k + 1].restrict (C i)) hS, ← hGC i, hGAh,
      Measure.map_apply (ιL P).continuous.measurable hS, Measure.prod_apply hιS,
      setLIntegral_congr_fun (hBhm i) (fun b hb => by rw [hGJ i b hb])]
    rw [(hπmp k).setLIntegral_comp_preimage (measurableSet_Ioo.prod (hB i)) hhm,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hhm.aemeasurable]
    refine lintegral_congr fun t => ?_
    rw [← lintegral_indicator_one (measurable_prodMk_left hιS)]
    exact (hGA (B i) (hB i) (fun a ha => (hdiff i a ha).1) (fun a ha => (hdiff i a ha).2)
      (hFinj i) (fun x => S.indicator 1 (ιL P (t, x)))).symm
  -- B4: sum over the pieces, using `Hᵏ(M ∖ ⋃ A i) = 0`
  have hMA : μHE[k].restrict M = Measure.sum fun i => μHE[k].restrict (A i) := by
    rw [← Measure.restrict_iUnion hdisj hFBm]
    refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨hnull, ?_⟩)
    rw [sdiff_eq_empty.mpr (iUnion_subset hFBM), measure_empty]
  have hmeasure : μHE[k + 1].restrict (ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i)) =
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict M)).map (ιL P) := by
    rw [hCU, Measure.restrict_iUnion hCdisj hCm, hMA, Measure.prod_sum_right,
      Measure.map_sum (ιL P).continuous.measurable.aemeasurable]
    exact congrArg Measure.sum (funext hpiece)
  -- B2: the cylinder `C = ι((0,1) × ⋃ A i) = ⋃ C i` is Borel with `Hᵏ⁺¹(C) = Hᵏ(M) < ∞`
  set Ctot := ιL P '' (Ioo (0 : ℝ) 1 ×ˢ ⋃ i, A i)
  have hCtotm : MeasurableSet Ctot :=
    hmeas_img _ (measurableSet_Ioo.prod (MeasurableSet.iUnion hFBm))
  have hCfin : μHE[k + 1] Ctot ≠ ∞ := by
    have : IsFiniteMeasure (μHE[k].restrict M) := isFiniteMeasure_restrict.mpr hfin
    have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr measure_Ioo_lt_top.ne
    rw [← Measure.restrict_apply_univ, hmeasure]
    exact measure_ne_top _ _
  -- B5: the tangent planes, piece by piece (accepted `dpf_approxTangent_ae_bilipschitz_piece`)
  have htan : ∀ i, ∀ᵐ y ∂(μHE[k + 1].restrict (C i)), ∀ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k M (πL P y).2 Q → HasApproximateTangentSpaceAt (k + 1) Ctot y
        (Submodule.span ℝ (insert (ιL P (1, 0))
          ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P))))) := by
    intro i
    obtain ⟨K, hK⟩ := hGlip i
    -- (a) `M` has approximate tangent space `range DF i(u)` at `F i u` for a.e. `u ∈ B i`
    have hTM := Submission.dpf_approxTangent_ae_bilipschitz_piece P k univ M (F i) (B i) (L i)
      (m i) isOpen_univ hM (subset_univ _)
      (fun K' _ _ => ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
      (hL i) (hB i) (hm i) (hbi i) (hdiff i) (hFBM i)
    -- (b) `C` has approximate tangent space `range DG i(b)` at `G i b` for a.e. `b ∈ Bh i`
    have hTC := Submission.dpf_approxTangent_ae_bilipschitz_piece (P + 1) (k + 1) univ Ctot (G i)
      (Bh i) K (min 1 (m i)) isOpen_univ hCtotm (subset_univ _)
      (fun K' _ _ => ne_top_of_le_ne_top hCfin (measure_mono inter_subset_left)) hK (hBhm i)
      (lt_min one_pos (hm i)) (hGlow i)
      (fun b hb => ⟨(hGd i b hb).differentiableAt, hGdinj i b hb⟩)
      (by rw [hGC i, hCU]; exact subset_iUnion C i)
    -- (c) (a) holds at `π₂ b` for a.e. `b ∈ Bh i`, since `π` is measure preserving
    have hTM' : ∀ᵐ b ∂(volume.restrict (Bh i)), HasApproximateTangentSpaceAt k M (F i (πL k b).2)
        (LinearMap.range (fderiv ℝ (F i) (πL k b).2 : Euclid k →ₗ[ℝ] Euclid P)) := by
      refine ((hπmp k).restrict_preimage
        (measurableSet_Ioo.prod (hB i))).quasiMeasurePreserving.ae
        (p := fun p : ℝ × Euclid k => HasApproximateTangentSpaceAt k M (F i p.2)
          (LinearMap.range (fderiv ℝ (F i) p.2 : Euclid k →ₗ[ℝ] Euclid P))) ?_
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      exact Measure.quasiMeasurePreserving_snd.ae hTM
    -- (d) there, uniqueness of approximate tangent spaces and `range DG i(b) = ℝe₀ ⊕ J(range DF i)`
    have hcomb : ∀ᵐ b ∂(volume.restrict (Bh i)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k M (πL P (G i b)).2 Q →
        HasApproximateTangentSpaceAt (k + 1) Ctot (G i b)
          (Submodule.span ℝ (insert (ιL P (1, 0))
            ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P))))) := by
      filter_upwards [hTC, hTM', ae_restrict_mem (hBhm i)] with b hbC hbM hb Q hQ
      have hprG : (πL P (G i b)).2 = F i (πL k b).2 := by
        show (πL P (ιL P ((πL k b).1, F i (πL k b).2))).2 = _
        rw [hπι]
      rw [hprG] at hQ
      rw [hQ.unique hbM, ← hGrange i b hb]
      exact hbC
    -- (e) the exceptional set is the image of a Lebesgue-null set under the Lipschitz `G i`
    rw [← hGC i, ae_iff, Measure.restrict_apply' ((hGC i).symm ▸ hCm i)]
    rw [ae_iff, Measure.restrict_apply' (hBhm i)] at hcomb
    refine measure_mono_null (t := G i '' ({b | ¬∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt k M (πL P (G i b)).2 Q →
        HasApproximateTangentSpaceAt (k + 1) Ctot (G i b) (Submodule.span ℝ (insert (ιL P (1, 0))
          ((fun v => ιL P (0, v)) '' (Q : Set (Euclid P)))))} ∩ Bh i)) ?_ ?_
    · rintro _ ⟨hy, b, hb, rfl⟩
      exact ⟨b, ⟨hy, hb⟩, rfl⟩
    · refine le_antisymm (le_trans
        (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (k + 1)
          hK.lipschitzOnWith) ?_) bot_le
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume, hcomb, mul_zero]
  refine ⟨Ctot, hCtotm, image_mono (prod_mono subset_rfl (iUnion_subset hFBM)), ?_, hmeasure, ?_⟩
  -- B3: `C ⊆ ⋃ range (G i)`, every `G i` being Lipschitz
  · refine ⟨∅, measure_empty, G, hGlip, ?_⟩
    rw [empty_union, hCU]
    exact iUnion_mono fun i => hGC i ▸ image_subset_range _ _
  · have hCC : μHE[k + 1].restrict Ctot = μHE[k + 1].restrict (⋃ i, C i) := by rw [hCU]
    rw [hCC, ae_restrict_iUnion_iff]
    exact htan

/-- **Simon Ch. 6, 2.27–2.29 and 3.9** (analytic toolkit, and the Lipschitz push-forward of
integer multiplicity currents vanishing off a compact set).  (i) If `X = τ(M, θ, ξ)` in `ℝᴾ`
vanishes off the compact `E`, then `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`, so `Hᵏ(M ∖ E) = 0` (`θ ≥ 1`
on `M`), `M(X) = μ_R(ℝᴾ) = μ_R(E) < ∞`, and `R.action γ` depends only on `γ|_E`.  (ii) Hadamard:
`|α(v)| ≤ |α| ∏ᵢ |vᵢ|`, from `|α(v)| ≤ |α| det(⟨vᵢ, vⱼ⟩)^{1/2}` and a Gram–Schmidt frame with
`det(⟨vᵢ, vⱼ⟩) = (det A)²`, `|det A| ≤ ∏ᵢ |vᵢ|`.  (iii) `ξ = ±τ₁ ∧ ⋯ ∧ τₖ` a.e. with `τ`
orthonormal, so `|θ ξ(γ)| ≤ c θ` and `|R.action γ| ≤ c μ_R(ℝᴾ)`.  (iv) `F_j = ψ_j ⋆ F` with
normalized `C^∞` bumps `ψ_j` supported in `B_{1/(j+1)}(0)` are `Λ`-Lipschitz and
`|F_j - F| ≤ Λ/(j+1)`.  (v) A smooth Urysohn function for `cthickening 1 E ⊆ thickening 2 E`.
(vi) Given (IPF), `push k F X = Y_X(F)` for `Y_X` from (IPF) for a chosen finite-mass
representation of `X`: it is integer multiplicity, depends only on `F|_E`, is the limit of
`X(η_j) = R.action(F_j^#ω)`, has `M ≤ Λᵏ M(X)` (Hadamard with `‖DF_j‖ ≤ Λ`, then (iii)), and
vanishes off `F(E)` (for large `j`, `F_j(E)` avoids `spt ω`). -/
theorem Submission.dor_lmb_fcdp_toolkit_push : ((∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ') ∧ (∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖) ∧ (∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal) ∧ (∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop) ∧ ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1) ∧ ((∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ push : ∀ k : ℕ, (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) k, ∀ (k : ℕ) (Λ : NNReal) (F : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (push k F X) ∧ (∀ F' : Euclid P → Euclid P, LipschitzWith Λ F' → EqOn F F' E → push k F X = push k F' X) ∧ (∀ (Fs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ((ω : DifferentialForm (Euclid P) k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (push k F X ω))) ∧ (push k F X).mass ≤ (Λ : ℝ≥0∞) ^ k * X.mass ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (F '' E) → push k F X ω = 0) := by
  -- (i) compactly vanishing integer multiplicity representations
  have hi : ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (R : IMRep (univ : Set (Euclid P)) k) (E : Set (Euclid P)), R.Represents X → IsCompact E → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → μHE[k] (R.carrier \ E) = 0 ∧ X.mass = R.measure univ ∧ R.measure univ ≠ ∞ ∧ ∀ γ γ' : DifferentialForm (Euclid P) k, EqOn γ γ' E → R.action γ = R.action γ' := by
    intro P k X R E hR hE hXE
    have hmass :=
      (Submission.dor_imrep_massOn_eq_measure_and_support P k univ X R isOpen_univ hR).1
    have hEm : MeasurableSet E := hE.isClosed.measurableSet
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
    -- `μ_R(ℝᴾ ∖ E) = M_{ℝᴾ∖E}(X) = 0`: admissible forms supported off `E` are killed by `X`
    have hμEc : R.measure Eᶜ = 0 := by
      rw [← hmass Eᶜ hE.isClosed.isOpen_compl]
      refine le_antisymm (sSup_le ?_) bot_le
      rintro _ ⟨ω, ⟨hωE, -⟩, rfl⟩
      dsimp only
      rw [hXE ω (subset_compl_iff_disjoint_right.mp hωE), ENNReal.ofReal_zero]
    -- `Hᵏ(M ∖ E) = 0`, since `θ ≥ 1` on `M`
    have hnull : μHE[k] (R.carrier \ E) = 0 := by
      rw [IMRep.measure, withDensity_apply_eq_zero' hθ.aemeasurable,
        Measure.restrict_apply' R.measurableSet_carrier] at hμEc
      refine measure_mono_null ?_ hμEc
      intro x hx
      exact ⟨⟨Nat.cast_ne_zero.mpr (R.mult_pos x hx.1).ne', hx.2⟩, hx.1⟩
    -- `Hᵏ⌞M`-a.e. point lies in `E`
    have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
      rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
      refine measure_mono_null ?_ hnull
      intro x hx
      exact ⟨hx.2, hx.1⟩
    -- `μ_R(ℝᴾ) = μ_R(E) = ∫_{M ∩ E} θ dHᵏ < ∞`
    have hfin : R.measure univ ≠ ∞ := by
      rw [← measure_add_measure_compl hEm, hμEc, add_zero, IMRep.measure, withDensity_apply _ hEm,
        Measure.restrict_restrict hEm, inter_comm]
      exact R.locallyIntegrable_mult E hE (subset_univ E)
    refine ⟨hnull, hmass univ isOpen_univ, hfin, fun γ γ' hγ => ?_⟩
    -- the integrands agree on `E`, hence `Hᵏ⌞M`-a.e.
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hγ hx]
  -- (ii) Hadamard's inequality for the Euclidean coefficient norm
  have hii : ∀ (N m : ℕ) (α : Covector (Euclid N) m) (v : Fin m → Euclid N), |α v| ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ := by
    intro N m α v
    by_cases hv : LinearIndependent ℝ v
    · obtain ⟨σ, -, -, hG, -, hA⟩ := Submission.dpf_exists_orthonormal_frame_det_gram N m v hv
      calc |α v| ≤ covectorEuclideanNorm α *
            Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j))) :=
            (Submission.covectorEuclideanNorm_gram_bounds N m).1 α v
        _ = covectorEuclideanNorm α * |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| := by
            rw [hG, Real.sqrt_sq_eq_abs]
        _ ≤ covectorEuclideanNorm α * ∏ i, ‖v i‖ :=
            mul_le_mul_of_nonneg_left hA (covectorEuclideanNorm_nonneg α)
    · -- a linearly dependent family is killed by every alternating map
      rw [show α v = 0 from α.toAlternatingMap.map_linearDependent v hv, abs_zero]
      exact mul_nonneg (covectorEuclideanNorm_nonneg α)
        (Finset.prod_nonneg fun i _ => norm_nonneg _)
  -- (iii) the action is bounded by `c μ_R(ℝᴾ)` when `γ` is bounded by `c` on orthonormal frames
  have hiii : ∀ (P k : ℕ) (U : Set (Euclid P)) (R : IMRep U k) (γ : DifferentialForm (Euclid P) k) (c : ℝ), R.measure univ ≠ ∞ → 0 ≤ c → (∀ᵐ x ∂(μHE[k].restrict R.carrier), ∀ τ : Fin k → Euclid P, Orthonormal ℝ τ → |γ x τ| ≤ c) → |R.action γ| ≤ c * (R.measure univ).toReal := by
    intro P k U R γ c hfin hc hγ
    have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
    -- `∫⁻ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`, so `θ` is `Hᵏ⌞M`-integrable with `∫ θ d(Hᵏ⌞M) = μ_R(ℝᴾ)`
    have hlint : ∫⁻ x, ENNReal.ofReal (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) =
        R.measure univ := by
      rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      exact lintegral_congr fun x => ENNReal.ofReal_natCast _
    have hθ0 : 0 ≤ᵐ[μHE[k].restrict R.carrier] fun x => (R.mult x : ℝ) :=
      ae_of_all _ fun x => Nat.cast_nonneg _
    have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) :=
      ⟨hθm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hθ0).mpr (hlint ▸ hfin.lt_top)⟩
    have hθI : ∫ x, (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) = (R.measure univ).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae hθ0 hθm.aestronglyMeasurable, hlint]
    rw [← Real.norm_eq_abs, IMRep.action]
    calc ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (γ x) ∂μHE[k]‖
        ≤ ∫ x, c * (R.mult x : ℝ) ∂(μHE[k].restrict R.carrier) := by
          refine norm_integral_le_of_norm_le (hθint.const_mul c) ?_
          -- a.e. `ξ(x)(β) = ±β(τ)` with `τ` orthonormal, so `|ξ(x)(γ x)| = |γ(x)(τ)| ≤ c`
          filter_upwards [hγ, R.orients] with x hx hor
          obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hor
          rw [norm_mul, Real.norm_natCast, mul_comm c]
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          rcases hξ with h | h
          · rw [h, Real.norm_eq_abs]
            exact hx τ hτ
          · rw [h, norm_neg, Real.norm_eq_abs]
            exact hx τ hτ
      _ = c * (R.measure univ).toReal := by rw [integral_const_mul, hθI]
  -- (iv) `C^∞` `Λ`-Lipschitz approximations by mollification
  have hiv : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ TendstoUniformly Fs F atTop := by
    intro N N' Λ F hF
    -- normalized `C^∞` bumps `ψ = φ / ∫ φ` supported in `B_r(0)`
    have hker : ∀ r : ℝ, 0 < r → ∃ ψ : Euclid N → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧ support ψ ⊆ ball 0 r := by
      intro r hr
      let φ : ContDiffBump (0 : Euclid N) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hr
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    choose ψ hψ hψc hψ0 hψ1 hψs using fun j : ℕ =>
      hker (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
    have hFi : LocallyIntegrable F volume := hF.continuous.locallyIntegrable
    refine ⟨fun j => convolution (ψ j) F (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      fun j => (hψc j).contDiff_convolution_left _ (hψ j) hFi, fun j => ?_, ?_⟩
    · -- `ψ_j ⋆ F` is `Λ`-Lipschitz: it averages the differences `F(x - t) - F(x' - t)`
      have hconv : ∀ x, Integrable (fun t => ψ j t • F (x - t)) volume := fun x =>
        ((hψc j).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) (hψ j).continuous hFi
          x).integrable
      refine LipschitzWith.of_dist_le_mul fun x x' => ?_
      dsimp only
      rw [dist_eq_norm, convolution_def, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply]
      rw [← integral_sub (hconv x) (hconv x')]
      calc ‖∫ t, (ψ j t • F (x - t) - ψ j t • F (x' - t))‖ ≤ ∫ t, ψ j t * (Λ * dist x x') := by
            refine norm_integral_le_of_norm_le
              (((hψ j).continuous.integrable_of_hasCompactSupport (hψc j)).mul_const _)
              (ae_of_all _ fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hψ0 j t)]
            refine mul_le_mul_of_nonneg_left ?_ (hψ0 j t)
            rw [← dist_eq_norm]
            calc dist (F (x - t)) (F (x' - t)) ≤ Λ * dist (x - t) (x' - t) := hF.dist_le_mul _ _
              _ = Λ * dist x x' := by rw [dist_sub_right]
        _ = Λ * dist x x' := by rw [integral_mul_const, hψ1 j, one_mul]
    · -- `dist((ψ_j ⋆ F)(x), F(x)) ≤ Λ/(j+1)`, as `F` moves by `≤ Λ/(j+1)` on `B_{1/(j+1)}(x)`
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hlim : Tendsto (fun j : ℕ => (Λ : ℝ) * (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ : ℝ)
        rwa [mul_zero] at this
      filter_upwards [hlim.eventually (gt_mem_nhds hε)] with j hj x
      rw [dist_comm]
      refine (dist_convolution_le (by positivity) (hψs j) (hψ0 j) (hψ1 j)
        hF.continuous.aestronglyMeasurable fun y hy => ?_).trans_lt hj
      calc dist (F y) (F x) ≤ Λ * dist y x := hF.dist_le_mul y x
        _ ≤ Λ * (1 / ((j : ℝ) + 1)) := mul_le_mul_of_nonneg_left (mem_ball.mp hy).le Λ.coe_nonneg
  -- (v) smooth cut-off functions
  have hv : ∀ (P : ℕ) (E : Set (Euclid P)), IsCompact E → ∃ (χ : Euclid P → ℝ) (W : Set (Euclid P)), ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ IsOpen W ∧ E ⊆ W ∧ ∀ x ∈ W, χ x = 1 := by
    intro P E hE
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := 2) (E := E)) (isClosed_cthickening (δ := 1) (E := E))
      (cthickening_subset_thickening' two_pos one_lt_two E)
    refine ⟨χ, thickening 1 E, hχ, ?_, fun x => hχr ⟨x, rfl⟩, isOpen_thickening,
      self_subset_thickening one_pos E,
      fun x hx => (hχ1 x).mp (thickening_subset_cthickening 1 E hx)⟩
    exact HasCompactSupport.of_support_subset_isCompact (hE.cthickening (r := 2))
      (hχs ▸ thickening_subset_cthickening 2 E)
  refine ⟨⟨hi, hii, hiii, hiv, hv⟩, ?_⟩
  -- (vi) the push-forward operator, assuming (IPF)
  intro hIPF P
  -- for `X` with a finite-mass IM representation `R`, choose `Y_X` from (IPF) for `R`
  obtain ⟨Ych, hYch⟩ : ∃ Ych : ∀ k : ℕ, GeometricCurrentOn (univ : Set (Euclid P)) k →
      (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k,
      ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
        (∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧ R.measure univ ≠ ∞) →
        ∃ (R : IMRep (univ : Set (Euclid P)) k) (hR : R.measure univ ≠ ∞),
          R.Represents X ∧ Ych k X = Classical.choose (hIPF P P k R hR) := by
    classical
    exact ⟨fun k X => if h : ∃ R : IMRep (univ : Set (Euclid P)) k, R.Represents X ∧
      R.measure univ ≠ ∞ then Classical.choose (hIPF P P k h.choose h.choose_spec.2)
      else fun _ => X, fun k X h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1, dite_eq_left h⟩⟩
  refine ⟨fun k F X => Ych k X F, ?_⟩
  rintro k Λ F E X hF hE ⟨R', hR'⟩ hXE
  dsimp only
  -- by (i) every representation of `X` has finite mass
  obtain ⟨R, hRfin, hRX, hY⟩ := hYch k X ⟨R', hR', (hi P k X R' E hR' hE hXE).2.2.1⟩
  obtain ⟨hYa, hYb⟩ := Classical.choose_spec (hIPF P P k R hRfin)
  rw [← hY] at hYa hYb
  obtain ⟨hnull, hmass, -, hloc⟩ := hi P k X R E hRX hE hXE
  have hae : ∀ᵐ x ∂(μHE[k].restrict R.carrier), x ∈ E := by
    rw [ae_iff, Measure.restrict_apply' R.measurableSet_carrier]
    refine measure_mono_null ?_ hnull
    intro x hx
    exact ⟨hx.2, hx.1⟩
  -- `C^∞` `Λ`-Lipschitz `F_j → F` by (iv); `push k F X (ω) = lim R.action(F_j^#ω)`
  obtain ⟨Fs, hFs, hFsL, hFsU⟩ := hiv P P Λ F hF
  have hFs1 : ∀ j, ContDiff ℝ 1 (Fs j) := fun j => (hFs j).of_le (by exact_mod_cast le_top)
  have hlim := (hYa F Λ hF).2 Fs hFs1 hFsL hFsU
  refine ⟨(hYa F Λ hF).1, fun F' hF' hFF' => hYb F F' Λ hF hF' ?_,
    fun Fs' ω ηs hFs' hFsL' hFsU' hη => ?_, ?_, fun ω hω => ?_⟩
  · -- (P2): `F = F'` on `E`, hence `Hᵏ⌞M`-a.e.
    filter_upwards [hae] with x hx using hFF' hx
  · -- (P3): `X(η_j) = R.action(η_j) = R.action(F_j^#ω) → push k F X (ω)`
    refine ((hYa F Λ hF).2 Fs' hFs' hFsL' hFsU' ω).congr fun j => ?_
    rw [hRX (ηs j)]
    exact hloc _ _ fun x hx => (hη j x hx).symm
  · -- (P4): for admissible `ω`, `|R.action(F_j^#ω)| ≤ Λᵏ μ_R(ℝᴾ)` by (ii) and (iii)
    rw [hmass, GeometricCurrentOn.mass, GeometricCurrentOn.massOn]
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨-, hω1⟩, rfl⟩
    dsimp only
    have hbd : ∀ j, |R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))| ≤
        (Λ : ℝ) ^ k * (R.measure univ).toReal := by
      intro j
      refine hiii P k univ R _ _ hRfin (by positivity) (ae_of_all _ fun x τ hτ => ?_)
      rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
      calc |(ω : DifferentialForm (Euclid P) k) (Fs j x) (fderiv ℝ (Fs j) x ∘ τ)|
          ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) (Fs j x)) *
            ∏ i, ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ := hii P k _ _
        _ ≤ 1 * ∏ _i : Fin k, (Λ : ℝ) := by
          refine mul_le_mul (hω1 _)
            (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_)
            (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
          -- `‖DF_j(x) τᵢ‖ ≤ ‖DF_j(x)‖ ≤ Λ`
          calc ‖(fderiv ℝ (Fs j) x ∘ τ) i‖ ≤ ‖fderiv ℝ (Fs j) x‖ * ‖τ i‖ :=
                (fderiv ℝ (Fs j) x).le_opNorm _
            _ ≤ Λ := by
                rw [hτ.1 i, mul_one]
                exact norm_fderiv_le_of_lipschitz ℝ (hFsL j)
        _ = (Λ : ℝ) ^ k := by rw [one_mul, Fin.prod_const]
    have hle : Ych k X F ω ≤ (Λ : ℝ) ^ k * (R.measure univ).toReal :=
      le_of_tendsto' (hlim ω) fun j => (le_abs_self _).trans (hbd j)
    calc ENNReal.ofReal (Ych k X F ω)
        ≤ ENNReal.ofReal ((Λ : ℝ) ^ k * (R.measure univ).toReal) := ENNReal.ofReal_le_ofReal hle
      _ = (Λ : ℝ≥0∞) ^ k * R.measure univ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hRfin,
          ENNReal.ofReal_pow NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
  · -- (P5): for large `j`, `F_j(E)` avoids `spt ω`, so `F_j^#ω = 0` on `E`
    obtain ⟨δ, hδ, hδK⟩ := (hE.image hF.continuous).exists_cthickening_subset_open
      (isClosed_tsupport _).isOpen_compl (subset_compl_iff_disjoint_left.mpr hω)
    have hev : ∀ᶠ j in atTop, R.action (fun x => ((ω : DifferentialForm (Euclid P) k)
        (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) = 0 := by
      filter_upwards [Metric.tendstoUniformly_iff.mp hFsU δ hδ] with j hj
      refine (hloc _ 0 fun x hx => ?_).trans ?_
      · have hmem : Fs j x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
          hδK (thickening_subset_cthickening δ _
            (mem_thickening_iff.mpr ⟨F x, mem_image_of_mem F hx, by rw [dist_comm]; exact hj x⟩))
        rw [image_eq_zero_of_notMem_tsupport hmem]
        ext v
        simp
      · simp [IMRep.action]
    exact tendsto_nhds_unique (hlim ω) (tendsto_const_nhds.congr' (hev.mono fun j hj => hj.symm))
/-- **Smooth pull-backs and the homotopy formula on forms** (Simon 6.2.23–6.2.26, dual form).
(a) The pull-back `Φ^#α(x) = α(Φ x) ∘ DΦ(x)` of a smooth form by a `C^∞` map is smooth.
(b) Let `F, G` be `C^∞`, `h(t, x) = F x + t(G x - F x)` the affine homotopy (6.2.26) and `ω` a
smooth `(k+1)`-form.  Then `Kω(x) = ∫₀¹ (ι_{G x - F x} ω(h(t, x))) ∘ D_x h(t, x) dt` is smooth and
`G^#ω - F^#ω = d(Kω) + K(dω)`, the homotopy formula 6.2.25 tested on `ω`.  The precomposition
`L ↦ (γ ↦ γ ∘ L)` is analytic, which gives (a).  For (b) we work on a proper normed space `E`:
with `H = h` on `ℝ × E`, `Θ = H^#ω` and `e = (1, 0)`, `dΘ = H^#(dω)` and Cartan's formula
`d(ι_e Θ) + ι_e dΘ = DΘ[e]` hold; pulling back by `y ↦ (t, y)` turns `ι_e Θ` and `ι_e dΘ` into the
integrands of `Kω` and `K(dω)` and `DΘ[e]` into `∂_t (h_t^#ω)`.  Integrating over `t ∈ [0, 1]`
and differentiating under the integral sign gives the formula. -/
theorem Submission.dor_lmb_fcdp_smooth_homotopy : (∀ (N N' m : ℕ) (Φ : Euclid N → Euclid N') (α : DifferentialForm (Euclid N') m), ContDiff ℝ (⊤ : ℕ∞) Φ → IsSmoothForm α → IsSmoothForm (fun x => (α (Φ x)).compContinuousLinearMap (fderiv ℝ Φ x))) ∧ ∀ (P k : ℕ) (F G : Euclid P → Euclid P) (ω : DifferentialForm (Euclid P) (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1, ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧ ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) - (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) = exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1, ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x + ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
  -- the pull-back `x ↦ α(x) ∘ L(x)` is `C^∞` when `α` and `L` are, as `L ↦ (γ ↦ γ ∘ L)` is analytic
  have hpb : ∀ (E₁ E₂ E₃ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
      [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
      (m : ℕ) (α : E₁ → E₂ [⋀^Fin m]→L[ℝ] ℝ) (L : E₁ → E₃ →L[ℝ] E₂),
      ContDiff ℝ (⊤ : ℕ∞) α → ContDiff ℝ (⊤ : ℕ∞) L →
        ContDiff ℝ (⊤ : ℕ∞) (fun x => (α x).compContinuousLinearMap (L x)) := by
    intro E₁ E₂ E₃ _ _ _ _ _ _ m α L hα hL
    have hΨ : ContDiff ℝ (⊤ : ℕ∞) (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E₃ →L[ℝ] E₂) → (E₂ [⋀^Fin m]→L[ℝ] ℝ) →L[ℝ] (E₃ [⋀^Fin m]→L[ℝ] ℝ)) :=
      (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).contDiff
    exact (hΨ.comp hL).clm_apply hα
  -- (a) `Φ^#α(x) = α(Φ x) ∘ DΦ(x)`
  refine ⟨fun N N' m Φ α hΦ hα => hpb (Euclid N) (Euclid N') (Euclid N) m (fun x => α (Φ x))
    (fderiv ℝ Φ) (hα.comp hΦ) (contDiff_infty_iff_fderiv.mp hΦ).2, ?_⟩
  -- (b) on an abstract proper normed space `E`, then for `E = ℝᴾ`
  suffices key : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] (k : ℕ)
      (F G : E → E) (ω : DifferentialForm E (k + 1)), ContDiff ℝ (⊤ : ℕ∞) F →
      ContDiff ℝ (⊤ : ℕ∞) G → IsSmoothForm ω → IsSmoothForm (fun x => ∫ t in (0 : ℝ)..1,
        ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
          (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x))) ∧
      ∀ x, (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
        (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
        exteriorDerivative (fun x' => ∫ t in (0 : ℝ)..1,
          ((ω (F x' + t • (G x' - F x'))).curryLeft (G x' - F x')).compContinuousLinearMap
            (fderiv ℝ F x' + t • (fderiv ℝ G x' - fderiv ℝ F x'))) x +
        ∫ t in (0 : ℝ)..1, ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
          (G x - F x)).compContinuousLinearMap (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) by
    intro P k F G ω hF hG hω
    exact key (Euclid P) k F G ω hF hG hω
  intro E _ _ _ k F G ω hF hG hω
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω := hω
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hr : minSmoothness ℝ 2 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have hF1 : Differentiable ℝ F := hF.differentiable hne
  have hG1 : Differentiable ℝ G := hG.differentiable hne
  have hω1 : Differentiable ℝ ω := hωs.differentiable hne
  -- `γ ↦ γ.curryLeft` is a linear isometry, hence `C^∞`
  have hcl : ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] (m : ℕ),
      ContDiff ℝ (⊤ : ℕ∞) (fun γ : E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ => γ.curryLeft) := by
    intro E₁ _ _ m
    have h := LinearIsometry.contDiff (𝕜 := ℝ) (E := E₁ [⋀^Fin (m + 1)]→L[ℝ] ℝ)
      (F := E₁ →L[ℝ] E₁ [⋀^Fin m]→L[ℝ] ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      ContinuousAlternatingMap.curryLeftLI
    exact h
  -- differentiation under the integral sign: `D_x ∫₀¹ f(t, x) dt = ∫₀¹ Df(t, x) ∘ J dt`, `J = inr`,
  -- with the bound `sup ‖Df ∘ J‖` over the compact set `[0, 1] × B̄(x₀, 1)`
  have hpar : ∀ (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f → ∀ x₀ : E,
      HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, f (t, x))
        (∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x₀ := by
    intro Y _ _ _ f hf x₀
    have : SecondCountableTopologyEither ℝ (E →L[ℝ] Y) := ⟨Or.inl inferInstance⟩
    have hf1 : Differentiable ℝ f := hf.differentiable hne
    have hDf : Continuous (fun p : ℝ × E => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
      (hf.continuous_fderiv hne).clm_comp continuous_const
    have hjt : ∀ x : E, Continuous (fun t : ℝ => ((t, x) : ℝ × E)) :=
      fun x => continuous_id.prodMk continuous_const
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod
      (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn hDf.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => f (t, x))
      (F' := fun x t => (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (bound := fun _ => C) (ball_mem_nhds x₀ one_pos)
      (Eventually.of_forall fun x => (hf.continuous.comp (hjt x)).aestronglyMeasurable)
      ((hf.continuous.comp (hjt x₀)).intervalIntegrable 0 1)
      (hDf.comp (hjt x₀)).aestronglyMeasurable ?_ intervalIntegrable_const ?_
    · rw [ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun t ht x hx => hC (t, x) ⟨?_, ?_⟩
      · rw [uIoc_of_le zero_le_one] at ht
        exact Ioc_subset_Icc_self ht
      · exact ball_subset_closedBall hx
    · exact Eventually.of_forall fun t x _ =>
        (hf1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  -- `x ↦ ∫₀¹ f(t, x) dt` is `C^n` for every `n`, by induction (for all `Y` at once)
  have hsm : ∀ (n : ℕ) (Y : Type) [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
      (f : ℝ × E → Y), ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ n (fun x => ∫ t in (0 : ℝ)..1, f (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro Y _ _ _ f hf
      rw [Nat.cast_zero, contDiff_zero]
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := fun x t => f (t, x)) (hf.continuous.comp continuous_swap) 0 1
    | succ n ih =>
      intro Y _ _ _ f hf
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, (fderiv ℝ f (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E),
        ih (E →L[ℝ] Y) (fun p => (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ ℝ E))
          ((contDiff_infty_iff_fderiv.mp hf).2.clm_comp contDiff_const), hpar Y f hf⟩
  have hcc : ∀ (m : ℕ) (g : Covector E m) (L : ℝ × E →L[ℝ] E) (L' : E →L[ℝ] ℝ × E),
      (g.compContinuousLinearMap L).compContinuousLinearMap L' =
        g.compContinuousLinearMap (L.comp L') := fun _ _ _ _ => rfl
  -- the homotopy `H(t, y) = F y + t • (G y - F y)` on `ℝ × E`: `DH(t, y) e = G y - F y` for
  -- `e = (1, 0)`, and `DH(t, y) ∘ J = DF y + t • (DG y - DF y)`
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ × E → E, H = fun p => F p.2 + p.1 • (G p.2 - F p.2) := ⟨_, rfl⟩
  have hHapp : ∀ (t : ℝ) (y : E), H (t, y) = F y + t • (G y - F y) := fun t y => by rw [hHdef]
  have hHs : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHdef]
    exact (hF.comp contDiff_snd).add
      (contDiff_fst.smul ((hG.comp contDiff_snd).sub (hF.comp contDiff_snd)))
  have hH1 : Differentiable ℝ H := hHs.differentiable hne
  have hDHe : ∀ (t : ℝ) (y : E), fderiv ℝ H (t, y) (1, 0) = G y - F y := by
    intro t y
    have h1 : HasDerivAt (fun s : ℝ => H (s, y)) (fderiv ℝ H (t, y) (1, 0)) t :=
      (hH1 (t, y)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    have h2 := ((hasDerivAt_id' t).smul_const (G y - F y)).const_add (F y)
    rw [one_smul] at h2
    simp only [← hHapp] at h2
    exact h1.unique h2
  have hDHJ : ∀ (t : ℝ) (y : E), (fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) =
      fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y) := by
    intro t y
    have h1 : HasFDerivAt (fun y' : E => H (t, y'))
        ((fderiv ℝ H (t, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
      (hH1 (t, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right t y)
    have h2 : HasFDerivAt (fun y' : E => F y' + t • (G y' - F y'))
        (fderiv ℝ F y + t • (fderiv ℝ G y - fderiv ℝ F y)) y :=
      (hF1 y).hasFDerivAt.add (((hG1 y).hasFDerivAt.sub (hF1 y).hasFDerivAt).const_smul t)
    simp only [← hHapp] at h2
    exact h1.unique h2
  -- `Θ = H^#ω` is `C^∞` with `dΘ = H^#(dω)`, and `ι_e Θ` is `C^∞`
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ : DifferentialForm (ℝ × E) (k + 1),
      Θ = fun p => (ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := ⟨_, rfl⟩
  have hΘs : ContDiff ℝ (⊤ : ℕ∞) Θ := by
    rw [hΘdef]
    exact hpb (ℝ × E) E (ℝ × E) (k + 1) (fun p => ω (H p)) (fderiv ℝ H) (hωs.comp hHs)
      (contDiff_infty_iff_fderiv.mp hHs).2
  have hΘ1 : Differentiable ℝ Θ := hΘs.differentiable hne
  have hdΘ : ∀ p, extDeriv Θ p = (extDeriv ω (H p)).compContinuousLinearMap (fderiv ℝ H p) := by
    intro p
    rw [hΘdef]
    exact extDeriv_pullback (hω1 (H p)) hHs.contDiffAt hr
  obtain ⟨ιΘ, hιΘdef⟩ : ∃ ιΘ : DifferentialForm (ℝ × E) k,
      ιΘ = fun p => (Θ p).curryLeft (1, 0) := ⟨_, rfl⟩
  have hιΘs : ContDiff ℝ (⊤ : ℕ∞) ιΘ := by
    rw [hιΘdef]
    exact ((hcl (ℝ × E) k).comp hΘs).clm_apply contDiff_const
  have hιΘ1 : Differentiable ℝ ιΘ := hιΘs.differentiable hne
  -- the integrands `κ` of `Kω` and `κd` of `K(dω)` are `ι_e Θ ∘ J` and `ι_e dΘ ∘ J`
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ × E → Covector E k, κ = fun p =>
      ((ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκapp : ∀ (t : ℝ) (x : E), κ (t, x) =
      ((ω (F x + t • (G x - F x))).curryLeft (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκdef]
  obtain ⟨κd, hκddef⟩ : ∃ κd : ℝ × E → Covector E (k + 1), κd = fun p =>
      ((extDeriv ω (F p.2 + p.1 • (G p.2 - F p.2))).curryLeft
        (G p.2 - F p.2)).compContinuousLinearMap
        (fderiv ℝ F p.2 + p.1 • (fderiv ℝ G p.2 - fderiv ℝ F p.2)) := ⟨_, rfl⟩
  have hκdapp : ∀ (t : ℝ) (x : E), κd (t, x) =
      ((exteriorDerivative ω (F x + t • (G x - F x))).curryLeft
        (G x - F x)).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := fun t x => by rw [hκddef]
  have hκeq : ∀ (t : ℝ) (y : E),
      (ιΘ (t, y)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) = κ (t, y) := by
    intro t y
    rw [hκapp, hιΘdef, hΘdef]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκdeq : ∀ (t : ℝ) (y : E), ((extDeriv Θ (t, y)).curryLeft (1, 0)).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E) = κd (t, y) := by
    intro t y
    rw [hκddef, hdΘ]
    simp only [ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDHe, hcc, hDHJ, hHapp]
  have hκs : ContDiff ℝ (⊤ : ℕ∞) κ := by
    have hκfun : κ = fun p => (ιΘ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) :=
      funext fun p => (hκeq p.1 p.2).symm
    rw [hκfun]
    exact hpb (ℝ × E) (ℝ × E) E k ιΘ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hιΘs contDiff_const
  -- `Kω` is `C^∞`
  simp only [← hκapp, ← hκdapp]
  refine ⟨contDiff_infty.mpr fun n => hsm n _ κ hκs, fun x => ?_⟩
  -- Cartan's formula for the constant field `e`: `d(ι_e Θ) + ι_e dΘ = DΘ[e]`
  have hcartan : ∀ p, extDeriv ιΘ p + (extDeriv Θ p).curryLeft (1, 0) = fderiv ℝ Θ p (1, 0) := by
    intro p
    ext v
    have h0 : Fin.removeNth 0 (Matrix.vecCons ((1 : ℝ), (0 : E)) v) = v := by simp
    have hs : ∀ i : Fin (k + 1), Fin.removeNth i.succ (Matrix.vecCons ((1 : ℝ), (0 : E)) v) =
        Matrix.vecCons ((1 : ℝ), (0 : E)) (Fin.removeNth i v) :=
      fun i => Fin.cons_comp_succ_succAbove _ v i
    rw [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
      extDeriv_apply (hιΘ1 p), extDeriv_apply (hΘ1 p), Fin.sum_univ_succ (n := k + 1)]
    simp only [hιΘdef, ContinuousAlternatingMap.curryLeft_apply_apply, h0, hs, Fin.val_zero,
      pow_zero, one_smul, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_succ]
    rw [fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p), add_left_comm,
      ← Finset.sum_add_distrib, Finset.sum_eq_zero, add_zero]
    intro i _
    rw [pow_succ, mul_neg_one, neg_smul, add_neg_cancel]
  -- pulling back by `y ↦ (t, y)`: `d(κ(t, ·))(x) = d(ι_e Θ)(t, x) ∘ J`
  have hj : ∀ (t : ℝ) (y : E),
      fderiv ℝ (fun y' : E => ((t, y') : ℝ × E)) y = ContinuousLinearMap.inr ℝ ℝ E :=
    fun t y => (hasFDerivAt_prodMk_right t y).fderiv
  have hpull : ∀ t : ℝ, extDeriv (fun x' => κ (t, x')) x =
      (extDeriv ιΘ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro t
    have h := extDeriv_pullback (ω := ιΘ) (f := fun y' : E => ((t, y') : ℝ × E)) (x := x)
      (hιΘ1 (t, x)) (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞)
        (fun y' : E => ((t, y') : ℝ × E))).contDiffAt hr
    simp only [hj, hκeq] at h
    exact h
  -- `Θ ∘ J` is `C^∞` with `D(Θ ∘ J)[e] = DΘ[e] ∘ J = d(κ(t, ·))(x) + κd(t, x)` at `(t, x)`
  have hΘ's : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hpb (ℝ × E) (ℝ × E) E (k + 1) Θ (fun _ => ContinuousLinearMap.inr ℝ ℝ E) hΘs contDiff_const
  have hΘ'1 : Differentiable ℝ
      (fun p => (Θ p).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E)) :=
    hΘ's.differentiable hne
  have hΘ'e : ∀ p, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) p (1, 0) =
      (fderiv ℝ Θ p (1, 0)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro p
    ext v
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ'1 p),
      ← fderiv_continuousAlternatingMap_apply_const_apply (hΘ1 p)]
    rfl
  have hpt : ∀ t : ℝ, fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0) =
      extDeriv (fun x' => κ (t, x')) x + κd (t, x) := by
    intro t
    rw [hΘ'e, ← hcartan, hpull, ← hκdeq]
    ext v
    rfl
  -- the fundamental theorem of calculus for `t ↦ Θ(t, x) ∘ J`
  have hjt : Continuous (fun t : ℝ => ((t, x) : ℝ × E)) := continuous_id.prodMk continuous_const
  have hc1 : Continuous (fun t : ℝ => fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
      (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) :=
    ((hΘ's.continuous_fderiv hne).comp hjt).clm_apply continuous_const
  have hβd : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => (Θ (s, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E))
      (fderiv ℝ (fun p => (Θ p).compContinuousLinearMap
        (ContinuousLinearMap.inr ℝ ℝ E)) (t, x) (1, 0)) t := by
    intro t
    have h := (hΘ'1 (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hβd t)
    (hc1.intervalIntegrable 0 1)
  -- `d(Kω)(x) = ∫₀¹ d(κ(t, ·))(x) dt`, as `d = alternatizeUncurryFin ∘ D` with a CLM
  have hκ1 : Differentiable ℝ κ := hκs.differentiable hne
  have hκt : ∀ t : ℝ, fderiv ℝ (fun x' => κ (t, x')) x =
      (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    fun t => ((hκ1 (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).fderiv
  have hc3 : Continuous (fun t : ℝ => (fderiv ℝ κ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) :=
    ((hκs.continuous_fderiv hne).comp hjt).clm_comp continuous_const
  have hi3 := Continuous.intervalIntegrable (E := E →L[ℝ] Covector E k) (μ := volume) hc3 0 1
  have hc4 : Continuous (fun t : ℝ => extDeriv (fun x' => κ (t, x')) x) := by
    simp only [extDeriv, hκt]
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ).continuous.comp hc3
  have hc2 : Continuous (fun t : ℝ => κd (t, x)) := by
    refine (hc1.sub hc4).congr fun t => ?_
    simp only [Pi.sub_apply]
    rw [hpt t, add_sub_cancel_left]
  have hdK : extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun x' => κ (t, x')) x := by
    simp only [extDeriv, hκt]
    rw [(hpar _ κ hκs x).fderiv]
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
      (E := E →L[ℝ] Covector E k) (F := Covector E (k + 1))
      (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℝ) hi3
    exact hcomm.symm
  -- `Θ(1, x) ∘ J = G^#ω(x)` and `Θ(0, x) ∘ J = F^#ω(x)`
  have hβ : ∀ t : ℝ, (Θ (t, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x + t • (G x - F x))).compContinuousLinearMap
        (fderiv ℝ F x + t • (fderiv ℝ G x - fderiv ℝ F x)) := by
    intro t
    rw [hΘdef]
    simp only [hcc, hDHJ, hHapp]
  have hβ1 : (Θ (1, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) := by
    rw [hβ, one_smul, one_smul, add_sub_cancel, add_sub_cancel]
  have hβ0 : (Θ (0, x)).compContinuousLinearMap (ContinuousLinearMap.inr ℝ ℝ E) =
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
    rw [hβ, zero_smul ℝ (G x - F x), zero_smul ℝ (fderiv ℝ G x - fderiv ℝ F x), add_zero,
      add_zero]
  -- `G^#ω - F^#ω = ∫₀¹ (d(κ(t, ·))(x) + κd(t, x)) dt = d(Kω)(x) + K(dω)(x)`
  show (ω (G x)).compContinuousLinearMap (fderiv ℝ G x) -
      (ω (F x)).compContinuousLinearMap (fderiv ℝ F x) =
    extDeriv (fun x' => ∫ t in (0 : ℝ)..1, κ (t, x')) x + ∫ t in (0 : ℝ)..1, κd (t, x)
  rw [← hβ1, ← hβ0, ← hftc, hdK, ← intervalIntegral.integral_add (hc4.intervalIntegrable 0 1)
    (hc2.intervalIntegrable 0 1)]
  exact intervalIntegral.integral_congr fun t _ => hpt t
/-- **The product `[[(0,1)]] × τ(M, θ, ξ)` as an integer multiplicity current** (Simon 6.2.17,
6.2.21).  For an `IMRep` `R = (M, θ, ξ)` of degree `k` in `ℝᴾ` with `μ_R(ℝᴾ) < ∞`, take the
cylinder `C ⊆ ι((0,1) × M)` of `dor_lmb_fcdp_cylinder`, with `Hᵏ⁺¹⌞C = ι_*(L¹⌞(0,1) ⊗ Hᵏ⌞M)`,
and put `R' = (C, θ ∘ pr, (ξ ∘ pr) ∘ c)`, `c(β) = (β ⌟ ê₀) ∘ J`, `J v = ι(0, v)`.  The measure
identity gives `μ_{R'}(ℝᴾ⁺¹) = μ_R(ℝᴾ)` and carries `Hᵏ⌞M`-null sets to `Hᵏ⁺¹⌞C`-null sets of
the form `pr⁻¹(N)`; `ê₀` followed by `J` of an orthonormal basis of `TₓM` is an orthonormal basis
of `ℝê₀ ⊕ J(TₓM)` realizing `ξ(x) ∘ c`; Fubini gives the action formula. -/
theorem Submission.dor_lmb_fcdp_product_imrep : ∀ (P k : ℕ) (R : IMRep (univ : Set (Euclid P)) k), R.measure univ ≠ ∞ → ∃ R' : IMRep (univ : Set (Euclid (P + 1))) (k + 1), R'.measure univ ≠ ∞ ∧ (∀ S : Set (Euclid P), MeasurableSet S → μHE[k] (R.carrier \ S) = 0 → μHE[k + 1] (R'.carrier \ ((fun p : ℝ × Euclid P => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) '' (Icc (0 : ℝ) 1 ×ˢ S))) = 0) ∧ ∀ β : DifferentialForm (Euclid (P + 1)) (k + 1), Continuous β → (∃ C : ℝ, ∀ y, ‖β y‖ ≤ C) → R'.action β = R.action (fun x => ∫ t in (0 : ℝ)..1, ((β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ) : Euclid (P + 1))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x)) := by
  intro P k R hR
  -- `μ_R(ℝᴾ) = ∫_M θ dHᵏ ≥ Hᵏ(M)`, as `θ ≥ 1` on `M`
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hRmeas : R.measure univ = ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
    rw [IMRep.measure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hMfin : μHE[k] R.carrier ≠ ∞ := by
    refine ne_top_of_le_ne_top hR ?_
    rw [hRmeas, ← setLIntegral_one]
    exact setLIntegral_mono hθm fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx)
  -- the cylinder `C ⊆ ι((0,1) × M)` with `Hᵏ⁺¹⌞C = ι_*(L¹⌞(0,1) ⊗ Hᵏ⌞M)`
  obtain ⟨C, hCm, hCsub, hCrect, hCmeas, hCtan⟩ :=
    Submission.dor_lmb_fcdp_cylinder P k R.carrier R.measurableSet_carrier R.rectifiable hMfin
  have : IsFiniteMeasure (μHE[k].restrict R.carrier) := isFiniteMeasure_restrict.2 hMfin
  have : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1)) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  -- `ι(t, x) = (t, x)` is a measurable embedding, with left inverse `y ↦ (y₀, pr y)`
  have hιc : Continuous (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) := by
    fun_prop
  have hprc : Continuous (fun y : Euclid (P + 1) =>
      (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P)) := by
    fun_prop
  have hιme : MeasurableEmbedding (fun p : ℝ × Euclid P =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) := by
    refine MeasurableEmbedding.of_measurable_inverse (g := fun y : Euclid (P + 1) =>
        (WithLp.ofLp y 0, (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) : Euclid P)))
      hιc.measurable ?_ (Continuous.measurable (by fun_prop)) fun p => rfl
    have hsurj : range (fun p : ℝ × Euclid P =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
        univ :=
      range_eq_univ.2 fun y : Euclid (P + 1) =>
        ⟨(WithLp.ofLp y 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))), by simp [Fin.cons_self_tail]⟩
    rw [hsurj]
    exact MeasurableSet.univ
  -- `J v = ι(0, v)` is linear isometric and is the `x`-derivative of `ι(t, x)`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid P →L[ℝ] Euclid (P + 1), ∀ v,
      J v = (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      { toFun := fun v =>
          (WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ) : Euclid (P + 1))
        map_add' := fun u v => by
          ext i
          induction i using Fin.cases <;> simp
        map_smul' := fun r v => by
          ext i
          induction i using Fin.cases <;> simp }, fun v => rfl⟩
  have hJinner : ∀ u v : Euclid P, inner ℝ (J u) (J v) = inner ℝ u v := by
    intro u v
    rw [hJ, hJ, PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_succ]
    simp
  have hfd : ∀ (t : ℝ) (x : Euclid P), fderiv ℝ (fun x' : Euclid P =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x = J := by
    intro t x
    have h : (fun x' : Euclid P =>
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) =
        fun x' => (WithLp.toLp 2 (Fin.cons t 0 : Fin (P + 1) → ℝ) : Euclid (P + 1)) + J x' := by
      funext x'
      rw [hJ]
      ext i
      induction i using Fin.cases <;> simp
    rw [h]
    exact (J.hasFDerivAt.const_add _).fderiv
  -- `c(γ) = (γ ⌟ ê₀) ∘ J`
  obtain ⟨c, hc⟩ : ∃ c : Covector (Euclid (P + 1)) (k + 1) →L[ℝ] Covector (Euclid P) k, ∀ γ,
      c γ = (γ.curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap
        J :=
    ⟨(ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ _ (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap), fun γ => rfl⟩
  -- `Hᵏ⌞M`-a.e. properties hold at `pr y` for `Hᵏ⁺¹⌞C`-a.e. `y`; `∫_C θ ∘ pr = ∫_M θ`
  have htr : ∀ {p : Euclid P → Prop}, (∀ᵐ x ∂μHE[k].restrict R.carrier, p x) →
      ∀ᵐ y ∂μHE[k + 1].restrict C, p (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) := by
    intro p hp
    rw [hCmeas, hιme.ae_map_iff]
    exact Measure.quasiMeasurePreserving_snd.ae hp
  have hlin : ∫⁻ y in C, (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞) ∂μHE[k + 1] =
      ∫⁻ x in R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[k] := by
    rw [hCmeas, hιme.lintegral_map]
    change ∫⁻ q, (R.mult q.2 : ℝ≥0∞)
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) = _
    rw [lintegral_prod (fun q : ℝ × Euclid P => (R.mult q.2 : ℝ≥0∞))
      (hθm.comp measurable_snd).aemeasurable]
    simp [Real.volume_Ioo]
  -- the fields of `R' = (C, θ ∘ pr, (ξ ∘ pr) ∘ c)`
  have hpos : ∀ y ∈ C, 0 < R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) := by
    intro y hy
    obtain ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩ := hCsub hy
    exact R.mult_pos x hx
  have hloc : ∀ K : Set (Euclid (P + 1)), IsCompact K → K ⊆ univ → ∫⁻ y in C ∩ K,
      (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞) ∂μHE[k + 1] ≠ ∞ := by
    intro K _ _
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_set inter_subset_left)
    rw [hlin, ← hRmeas]
    exact hR
  have hξm : AEStronglyMeasurable (fun y : Euclid (P + 1) =>
      (R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c) (μHE[k + 1].restrict C) := by
    rw [hCmeas, hιme.aestronglyMeasurable_map_iff]
    have hcomp : Continuous fun ζ : MultiVector P k => ζ.comp c :=
      continuous_id.clm_comp continuous_const
    exact hcomp.comp_aestronglyMeasurable R.aestronglyMeasurable_orient.comp_snd
  -- `(ê₀, Jτ₁, …, Jτₖ)` is an orthonormal basis of `ℝê₀ ⊕ J(Q)` realizing `ξ(pr y) ∘ c`
  have hor : ∀ᵐ y ∂(μHE[k + 1].restrict C), ∃ Q : Submodule ℝ (Euclid (P + 1)),
      HasApproximateTangentSpaceAt (k + 1) C y Q ∧
        IsUnitOrientationOf ((R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c) Q := by
    filter_upwards [htr R.orients, hCtan] with y ⟨Q, hQ, τ, hτ, hspan, hsign⟩ hy
    refine ⟨_, hy Q hQ,
      Fin.cons (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)) (J ∘ τ), ?_, ?_, ?_⟩
    · rw [orthonormal_iff_ite] at hτ ⊢
      intro i j
      induction i using Fin.cases <;> induction j using Fin.cases
      · simp
      · simp [EuclideanSpace.inner_single_left, hJ]
        exact (Fin.succ_ne_zero _).symm
      · simp [EuclideanSpace.inner_single_right, hJ]
      · simp [hJinner, hτ]
    · apply le_antisymm
      · rw [Fin.range_cons]
        refine Submodule.span_mono (insert_subset_insert ?_)
        rintro _ ⟨i, rfl⟩
        refine ⟨τ i, ?_, (hJ (τ i)).symm⟩
        rw [← hspan]
        exact Submodule.subset_span (mem_range_self i)
      · rw [Fin.range_cons, Submodule.span_le]
        rintro _ (rfl | ⟨v, hv, rfl⟩)
        · exact Submodule.subset_span (mem_insert _ _)
        · rw [← hspan] at hv
          dsimp only
          rw [← hJ]
          have h :=
            Submodule.apply_mem_span_image_of_mem_span (J : Euclid P →ₗ[ℝ] Euclid (P + 1)) hv
          rw [← range_comp] at h
          exact Submodule.span_mono (subset_insert _ _) h
    · rcases hsign with h | h
      · left
        intro γ
        rw [ContinuousLinearMap.comp_apply, h, hc]
        rfl
      · right
        intro γ
        rw [ContinuousLinearMap.comp_apply, h, hc]
        rfl
  refine ⟨⟨C, fun y => R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))),
    fun y => (R.orient (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))).comp c, hCm, subset_univ C,
    hCrect, R.measurable_mult.comp hprc.measurable, hpos, hloc, hξm, hor⟩, ?_, ?_, ?_⟩
  · -- (1) `μ_{R'}(ℝᴾ⁺¹) = μ_R(ℝᴾ)`
    show ((μHE[k + 1].restrict C).withDensity
      fun y => (R.mult (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) : ℝ≥0∞)) univ ≠ ∞
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlin, ← hRmeas]
    exact hR
  · -- (2) `C \ ι([0,1] × S) ⊆ C ∩ pr⁻¹(ℝᴾ \ S)`, which is `Hᵏ⁺¹`-null
    intro S hS hMS
    have hae : ∀ᵐ x ∂μHE[k].restrict R.carrier, x ∈ S :=
      (ae_restrict_iff' R.measurableSet_carrier).2
        (ae_iff.2 (measure_mono_null (fun x hx => not_imp.1 hx) hMS))
    have hnull := ae_iff.1 (htr hae)
    rw [Measure.restrict_apply' hCm] at hnull
    refine measure_mono_null ?_ hnull
    rintro y ⟨hyC, hyS⟩
    refine ⟨fun h => hyS ?_, hyC⟩
    obtain ⟨⟨t, x⟩, ⟨ht, -⟩, rfl⟩ := hCsub hyC
    exact ⟨(t, x), ⟨Ioo_subset_Icc_self ht, h⟩, rfl⟩
  · -- (3) Fubini, with the integrable bound `θ(x)‖c‖C_β` from `‖ξ‖ ≤ 1` a.e.
    rintro β hβc ⟨Cβ, hCβ⟩
    have hξbd : ∀ᵐ x ∂μHE[k].restrict R.carrier, ∀ α : Covector (Euclid P) k,
        ‖R.orient x α‖ ≤ ‖α‖ := by
      filter_upwards [R.orients] with x ⟨Q, _, τ, hτ, _, hsign⟩ α
      have h1 : ‖α τ‖ ≤ ‖α‖ := by
        simpa [hτ.1] using α.le_opNorm τ
      rcases hsign with h | h <;> rw [h α]
      · exact h1
      · rwa [norm_neg]
    have hθint : Integrable (fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) := by
      have h := integrable_toReal_of_lintegral_ne_top hθm.aemeasurable (hRmeas ▸ hR)
      simpa using h
    have : SecondCountableTopologyEither (ℝ × Euclid P) (Covector (Euclid P) k) :=
      secondCountableTopologyEither_of_left _ _
    have : SecondCountableTopologyEither ℝ (Covector (Euclid P) k) :=
      secondCountableTopologyEither_of_left _ _
    have hcb : ∀ y, ‖c (β y)‖ ≤ ‖c‖ * Cβ := fun y =>
      (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hCβ y) (norm_nonneg _))
    have hint : Integrable (fun q : ℝ × Euclid P => (R.mult q.2 : ℝ) *
        R.orient q.2 (c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ)))))
        ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) := by
      refine Integrable.mono' ((hθint.comp_snd _).mul_const (‖c‖ * Cβ)) ?_ ?_
      · refine ((measurable_from_nat.comp R.measurable_mult).comp
          measurable_snd).aestronglyMeasurable.mul ?_
        have h1 : AEStronglyMeasurable (fun q : ℝ × Euclid P => R.orient q.2)
            ((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) :=
          R.aestronglyMeasurable_orient.comp_snd
        have h2 : Continuous (fun q : ℝ × Euclid P =>
            c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ)))) :=
          c.continuous.comp (hβc.comp hιc)
        exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (h1.prodMk h2.aestronglyMeasurable)
      · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hξbd] with q hq
        rw [norm_mul, Real.norm_natCast]
        exact mul_le_mul_of_nonneg_left ((hq _).trans (hcb _)) (Nat.cast_nonneg _)
    have hintt : ∀ x : Euclid P, Integrable (fun t : ℝ =>
        c (β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ))))
        (volume.restrict (Ioo (0 : ℝ) 1)) := fun x =>
      Integrable.of_bound ((c.continuous.comp (hβc.comp
          (hιc.comp (continuous_id.prodMk continuous_const)))).aestronglyMeasurable)
        (‖c‖ * Cβ) (ae_of_all _ fun t => hcb _)
    -- the inner integral is `∫_{(0,1)} c(β(ι(t, x))) dt`
    have hω : (fun x : Euclid P => ∫ t in (0 : ℝ)..1, ((β
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ) : Euclid (P + 1))).curryLeft
          (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap
          (fderiv ℝ (fun x' : Euclid P =>
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x)) =
        fun x => ∫ t in Ioo (0 : ℝ) 1,
          c (β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ))) := by
      funext x
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      simp only [hfd, ← hc]
    rw [hω]
    simp only [IMRep.action]
    rw [hCmeas, hιme.integral_map]
    change ∫ q, (R.mult q.2 : ℝ) *
      R.orient q.2 (c (β (WithLp.toLp 2 (Fin.cons q.1 (WithLp.ofLp q.2) : Fin (P + 1) → ℝ))))
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (μHE[k].restrict R.carrier)) = _
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [integral_const_mul, ContinuousLinearMap.integral_comp_comm _ (hintt x)]
/-- **Cut-off affine homotopies on `ℝ^{P+1}`** (Simon 6.2.26–6.2.29).  For `y ∈ ℝ^{P+1}` write
`pr y = (y₁, …, y_P)` and `y₀`, and put
`H_{Φ,Ψ}(y) = Φ(pr y) + (a(y₀) χ(pr y)) • (Ψ(pr y) - Φ(pr y))`, where `a` is bounded and
Lipschitz and `χ` is Lipschitz with compact support `K`.  (A) `H_{F,G}` is Lipschitz: `φ = χ •
(G - F)` is bounded by `sup |χ| · sup_K ‖G - F‖` and Lipschitz (by cases on `K`), and
`H_{F,G}(y) = F(pr y) + a(y₀) • φ(pr y)`.  (B) For `C¹`, `Λ`-Lipschitz `Fⱼ → F`, `Gⱼ → G`
uniformly, every `H_{Fⱼ,Gⱼ}` is `C¹`, all are Lipschitz with the constant of (A) for the bound
`supⱼ sup_K ‖Gⱼ - Fⱼ‖ < ∞`, and `H_{Fⱼ,Gⱼ} → H_{F,G}` uniformly.  (C) Near `(t, x)` with
`x ∈ W` and `t ∈ (-1, 2)`, `H_{F',G'}(y) = F'(pr y) + y₀ • (G'(pr y) - F'(pr y))`, so
`DH(t,x) ê₀ = G'x - F'x` and `DH(t,x) ∘ J = DF'(x) + t (DG'(x) - DF'(x))` for `J v = (0, v)`;
`curryLeft_compContinuousLinearMap` turns `(H^#ω)(t,x)(ê₀, J ·)` into the integrand of 6.2.27. -/
theorem Submission.dor_lmb_fcdp_homotopy_maps : ∀ (P : ℕ) (Λ La Lχ : NNReal) (A : ℝ) (a : ℝ → ℝ) (χ : Euclid P → ℝ) (F G : Euclid P → Euclid P), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith La a → (∀ t, |a t| ≤ A) → LipschitzWith Lχ χ → HasCompactSupport χ → (∃ L : NNReal, LipschitzWith L (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ∀ Fs Gs : ℕ → Euclid P → Euclid P, (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ContDiff ℝ 1 (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ (∃ L : NNReal, ∀ j, LipschitzWith L (fun y : Euclid (P + 1) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))))) ∧ TendstoUniformly (fun j (y : Euclid (P + 1)) => Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (Gs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - Fs j (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) atTop) ∧ ∀ (F' G' : Euclid P → Euclid P) (W : Set (Euclid P)) (k : ℕ) (ω : DifferentialForm (Euclid P) (k + 1)) (t : ℝ) (x : Euclid P), ContDiff ℝ 1 a → ContDiff ℝ 1 χ → ContDiff ℝ 1 F' → ContDiff ℝ 1 G' → IsOpen W → (∀ z ∈ W, χ z = 1) → (∀ s ∈ Ioo (-1 : ℝ) 2, a s = s) → x ∈ W → t ∈ Ioo (-1 : ℝ) 2 → (((ω ((fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).compContinuousLinearMap (fderiv ℝ (fun y : Euclid (P + 1) => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)))).curryLeft (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ))).compContinuousLinearMap (fderiv ℝ (fun x' : Euclid P => (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))) x) = ((ω (F' x + t • (G' x - F' x))).curryLeft (G' x - F' x)).compContinuousLinearMap (fderiv ℝ F' x + t • (fderiv ℝ G' x - fderiv ℝ F' x)) := by
  intro P Λ La Lχ A a χ F G hF hG ha haA hχ hχc
  -- the coordinate maps `pr y = (y₁, …, y_P)` and `y ↦ y₀` are continuous linear
  let prL : Euclid (P + 1) →L[ℝ] Euclid P :=
    LinearMap.toContinuousLinearMap
      { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  let e0 : Euclid (P + 1) →L[ℝ] ℝ := EuclideanSpace.proj 0
  -- both are `1`-Lipschitz
  have hpr : ∀ y y' : Euclid (P + 1), dist (prL y) (prL y') ≤ dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succ]
    exact Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  have he0 : ∀ y y' : Euclid (P + 1), dist (e0 y) (e0 y') ≤ dist y y' :=
    fun y y' => PiLp.dist_apply_le y y' 0
  -- `0 ≤ A` and `|χ| ≤ B`
  have hA : 0 ≤ A := (abs_nonneg _).trans (haA 0)
  obtain ⟨B, hB⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  -- `H_{Φ,Ψ}` is Lipschitz, with a constant depending only on a bound `D` for `‖Ψ - Φ‖` on
  -- `K = spt χ`
  have key : ∀ (Φ Ψ : Euclid P → Euclid P), LipschitzWith Λ Φ → LipschitzWith Λ Ψ → ∀ D : ℝ,
      0 ≤ D → (∀ x ∈ tsupport χ, ‖Ψ x - Φ x‖ ≤ D) →
      LipschitzWith (Real.toNNReal (Λ + La * B * D + A * (Lχ * D + B * (2 * Λ))))
        (fun y : Euclid (P + 1) => Φ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) +
          (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) •
            (Ψ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) -
              Φ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) := by
    intro Φ Ψ hΦ hΨ D hD0 hD
    -- `φ = χ • (Ψ - Φ)` is bounded by `B * D` ...
    have hφb : ∀ x, ‖χ x • (Ψ x - Φ x)‖ ≤ B * D := by
      intro x
      by_cases hx : x ∈ tsupport χ
      · rw [norm_smul]
        exact mul_le_mul (hB x) (hD x hx) (norm_nonneg _) hB0
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero]
        exact mul_nonneg hB0 hD0
    -- ... and `(Lχ D + 2BΛ)`-Lipschitz, by cases on `spt χ`
    have hV : ∀ x x', ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ ≤ 2 * Λ * dist x x' := by
      intro x x'
      have h1 := hΨ.dist_le_mul x x'
      have h2 := hΦ.dist_le_mul x x'
      rw [dist_eq_norm] at h1 h2
      calc ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ = ‖(Ψ x - Ψ x') - (Φ x - Φ x')‖ := by congr 1; abel
        _ ≤ ‖Ψ x - Ψ x'‖ + ‖Φ x - Φ x'‖ := norm_sub_le _ _
        _ ≤ Λ * dist x x' + Λ * dist x x' := add_le_add h1 h2
        _ = 2 * Λ * dist x x' := by ring
    have hφL' : ∀ x x', x' ∈ tsupport χ →
        ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖ ≤ (Lχ * D + B * (2 * Λ)) * dist x x' := by
      intro x x' hx'
      have h1 : ‖χ x - χ x'‖ ≤ Lχ * dist x x' := by
        rw [← dist_eq_norm]; exact hχ.dist_le_mul x x'
      calc ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖
          = ‖(χ x - χ x') • (Ψ x' - Φ x') + χ x • ((Ψ x - Φ x) - (Ψ x' - Φ x'))‖ := by
            congr 1; simp only [sub_smul, smul_sub]; abel
        _ ≤ ‖χ x - χ x'‖ * ‖Ψ x' - Φ x'‖ + ‖χ x‖ * ‖(Ψ x - Φ x) - (Ψ x' - Φ x')‖ := by
            rw [← norm_smul, ← norm_smul]; exact norm_add_le _ _
        _ ≤ (Lχ * dist x x') * D + B * (2 * Λ * dist x x') :=
            add_le_add (mul_le_mul h1 (hD x' hx') (norm_nonneg _) (by positivity))
              (mul_le_mul (hB x) (hV x x') (norm_nonneg _) hB0)
        _ = (Lχ * D + B * (2 * Λ)) * dist x x' := by ring
    have hφL : ∀ x x',
        ‖χ x • (Ψ x - Φ x) - χ x' • (Ψ x' - Φ x')‖ ≤ (Lχ * D + B * (2 * Λ)) * dist x x' := by
      intro x x'
      by_cases hx' : x' ∈ tsupport χ
      · exact hφL' x x' hx'
      by_cases hx : x ∈ tsupport χ
      · rw [norm_sub_rev, dist_comm]; exact hφL' x' x hx
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx', zero_smul,
          zero_smul, sub_zero, norm_zero]
        positivity
    -- `H_{Φ,Ψ}(y) = Φ(p) + a(s) • φ(p)` with `p = pr y`, `s = y₀`
    refine LipschitzWith.of_dist_le' fun y y' => ?_
    change dist (Φ (prL y) + (a (e0 y) * χ (prL y)) • (Ψ (prL y) - Φ (prL y)))
      (Φ (prL y') + (a (e0 y') * χ (prL y')) • (Ψ (prL y') - Φ (prL y'))) ≤ _
    have hp := hpr y y'
    have hs := he0 y y'
    generalize prL y = p at hp ⊢
    generalize prL y' = p' at hp ⊢
    generalize e0 y = s at hs ⊢
    generalize e0 y' = s' at hs ⊢
    have hΦp : ‖Φ p - Φ p'‖ ≤ Λ * dist y y' := by
      rw [← dist_eq_norm]; exact (hΦ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hp Λ.2)
    have has : ‖a s - a s'‖ ≤ La * dist y y' := by
      rw [← dist_eq_norm]; exact (ha.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hs La.2)
    have has' : ‖a s'‖ ≤ A := by rw [Real.norm_eq_abs]; exact haA _
    have hφp := (hφL p p').trans (mul_le_mul_of_nonneg_left hp (by positivity))
    rw [dist_eq_norm]
    calc ‖(Φ p + (a s * χ p) • (Ψ p - Φ p)) - (Φ p' + (a s' * χ p') • (Ψ p' - Φ p'))‖
        = ‖(Φ p - Φ p') + ((a s - a s') • (χ p • (Ψ p - Φ p)) +
            a s' • (χ p • (Ψ p - Φ p) - χ p' • (Ψ p' - Φ p')))‖ := by
          congr 1; simp only [mul_smul, sub_smul, smul_sub]; abel
      _ ≤ ‖Φ p - Φ p'‖ + (‖a s - a s'‖ * ‖χ p • (Ψ p - Φ p)‖ +
            ‖a s'‖ * ‖χ p • (Ψ p - Φ p) - χ p' • (Ψ p' - Φ p')‖) := by
          rw [← norm_smul, ← norm_smul]
          exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ Λ * dist y y' + (La * dist y y' * (B * D) + A * ((Lχ * D + B * (2 * Λ)) * dist y y')) :=
          add_le_add hΦp (add_le_add (mul_le_mul has (hφb _) (norm_nonneg _) (by positivity))
            (mul_le_mul has' hφp (norm_nonneg _) hA))
      _ = (Λ + La * B * D + A * (Lχ * D + B * (2 * Λ))) * dist y y' := by ring
  -- (A): `D = sup_K ‖G - F‖`
  obtain ⟨D, hD⟩ := hχc.isCompact.exists_bound_of_continuousOn
    (hG.continuous.sub hF.continuous).continuousOn
  refine ⟨⟨_, key F G hF hG (max D 0) (le_max_right _ _) fun x hx =>
    (hD x hx).trans (le_max_left _ _)⟩, ?_, ?_⟩
  -- (B)
  · intro ha1 hχ1 Fs Gs hFs1 hGs1 hFsL hGsL hFsU hGsU
    refine ⟨fun j => ?_, ?_, ?_⟩
    · -- `H_j` is `C¹`
      exact ((hFs1 j).comp prL.contDiff).add (((ha1.comp e0.contDiff).mul
        (hχ1.comp prL.contDiff)).smul (((hGs1 j).comp prL.contDiff).sub
          ((hFs1 j).comp prL.contDiff)))
    · -- `D₂ = sup_j sup_K ‖Gs j - Fs j‖ < ∞`: `≤ D + 2` for `j ≥ N`, and finitely many `j < N`
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
        ((Metric.tendstoUniformly_iff.mp hFsU 1 one_pos).and
          (Metric.tendstoUniformly_iff.mp hGsU 1 one_pos))
      have hC : ∀ j, ∃ C, ∀ x ∈ tsupport χ, ‖Gs j x - Fs j x‖ ≤ C := fun j =>
        hχc.isCompact.exists_bound_of_continuousOn
          ((hGsL j).continuous.sub (hFsL j).continuous).continuousOn
      choose C hC using hC
      have hsum : 0 ≤ ∑ i ∈ Finset.range N, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      have hD₂ : ∀ j, ∀ x ∈ tsupport χ,
          ‖Gs j x - Fs j x‖ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by
        intro j x hx
        rcases le_or_gt N j with hj | hj
        · obtain ⟨h1, h2⟩ := hN j hj
          have e1 := h1 x
          have e2 := h2 x
          rw [dist_eq_norm] at e1 e2
          calc ‖Gs j x - Fs j x‖ = ‖(G x - F x) - (G x - Gs j x) + (F x - Fs j x)‖ := by
                congr 1; abel
            _ ≤ ‖G x - F x‖ + ‖G x - Gs j x‖ + ‖F x - Fs j x‖ :=
                (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
            _ ≤ max D 0 + 1 + 1 :=
                add_le_add (add_le_add ((hD x hx).trans (le_max_left _ _)) e2.le) e1.le
            _ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by linarith
        · calc ‖Gs j x - Fs j x‖ ≤ |C j| := (hC j x hx).trans (le_abs_self _)
            _ ≤ ∑ i ∈ Finset.range N, |C i| :=
                Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
                  (Finset.mem_range.mpr hj)
            _ ≤ max D 0 + 2 + ∑ i ∈ Finset.range N, |C i| := by linarith [le_max_right D 0]
      exact ⟨_, fun j => key (Fs j) (Gs j) (hFsL j) (hGsL j) _ (by positivity) (hD₂ j)⟩
    · -- `H_j → H` uniformly: `‖H_j - H‖ ≤ ‖Fs j - F‖ + A B (‖Gs j - G‖ + ‖Fs j - F‖)`
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hden : 0 < 1 + 2 * (A * B) := by positivity
      set δ := ε / (1 + 2 * (A * B))
      have hδ : 0 < δ := div_pos hε hden
      have hδε : δ + A * B * (δ + δ) = ε :=
        calc δ + A * B * (δ + δ) = δ * (1 + 2 * (A * B)) := by ring
          _ = ε := div_mul_cancel₀ ε hden.ne'
      filter_upwards [Metric.tendstoUniformly_iff.mp hFsU _ hδ,
        Metric.tendstoUniformly_iff.mp hGsU _ hδ] with j hFj hGj y
      change dist (F (prL y) + (a (e0 y) * χ (prL y)) • (G (prL y) - F (prL y)))
        (Fs j (prL y) + (a (e0 y) * χ (prL y)) • (Gs j (prL y) - Fs j (prL y))) < ε
      have hc : ‖a (e0 y) * χ (prL y)‖ ≤ A * B := by
        rw [norm_mul, Real.norm_eq_abs]; exact mul_le_mul (haA _) (hB _) (norm_nonneg _) hA
      have e1 := hFj (prL y)
      have e2 := hGj (prL y)
      generalize a (e0 y) * χ (prL y) = c at hc ⊢
      generalize prL y = p at e1 e2 ⊢
      rw [dist_eq_norm] at e1 e2 ⊢
      calc ‖(F p + c • (G p - F p)) - (Fs j p + c • (Gs j p - Fs j p))‖
          = ‖(F p - Fs j p) + c • ((G p - Gs j p) - (F p - Fs j p))‖ := by
            congr 1; simp only [smul_sub]; abel
        _ ≤ ‖F p - Fs j p‖ + ‖c‖ * (‖G p - Gs j p‖ + ‖F p - Fs j p‖) := by
            refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
        _ ≤ ‖F p - Fs j p‖ + A * B * (δ + δ) :=
            add_le_add le_rfl (mul_le_mul hc (add_le_add e2.le e1.le) (by positivity)
              (by positivity))
        _ < δ + A * B * (δ + δ) := by linarith
        _ = ε := hδε
  -- (C)
  · intro F' G' W k ω t x ha1 hχ1 hF'1 hG'1 hW hχW haI hxW ht
    -- `J v = (0, v)`
    let J : Euclid P →L[ℝ] Euclid (P + 1) :=
      LinearMap.toContinuousLinearMap
        { toFun := fun v => WithLp.toLp 2 (Fin.cons (0 : ℝ) (WithLp.ofLp v) : Fin (P + 1) → ℝ)
          map_add' := fun v w => by ext i; cases i using Fin.cases <;> simp
          map_smul' := fun c v => by ext i; cases i using Fin.cases <;> simp }
    set z : Euclid (P + 1) := WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x) : Fin (P + 1) → ℝ)
    set H' : Euclid (P + 1) → Euclid P := fun y => F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) +
      (a (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) •
        (G' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) -
          F' (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))
    set ι : Euclid P → Euclid (P + 1) := fun x' : Euclid P =>
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x') : Fin (P + 1) → ℝ) : Euclid (P + 1))
    have hprz : prL z = x := rfl
    have he0z : e0 z = t := rfl
    -- `ι(x') = ι(0) + J x'`, so `Dι(x) = J`
    have hι : fderiv ℝ ι x = J := by
      have : ι = fun x' => WithLp.toLp 2 (Fin.cons t 0 : Fin (P + 1) → ℝ) + J x' := by
        funext x'
        ext i
        cases i using Fin.cases <;> simp [ι, J]
      rw [this]
      exact (J.hasFDerivAt.const_add _).fderiv
    -- near `z`, `χ(pr y) = 1` and `a(y₀) = y₀`
    have hloc : H' =ᶠ[𝓝 z] fun y => F' (prL y) + e0 y • (G' (prL y) - F' (prL y)) := by
      have hO : IsOpen (prL ⁻¹' W ∩ e0 ⁻¹' Ioo (-1) 2) :=
        (hW.preimage prL.continuous).inter (isOpen_Ioo.preimage e0.continuous)
      have hzO : z ∈ prL ⁻¹' W ∩ e0 ⁻¹' Ioo (-1) 2 := by
        rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage, hprz, he0z]
        exact ⟨hxW, ht⟩
      filter_upwards [hO.mem_nhds hzO] with y hy
      have h1 : χ (prL y) = 1 := hχW _ hy.1
      have h2 : a (e0 y) = e0 y := haI _ hy.2
      change F' (prL y) + (a (e0 y) * χ (prL y)) • (G' (prL y) - F' (prL y)) = _
      rw [h1, h2, mul_one]
    -- the derivative of `F'(pr y) + y₀ • (G'(pr y) - F'(pr y))` at `z`
    have hF'd : HasFDerivAt F' (fderiv ℝ F' x) (prL z) := by
      rw [hprz]; exact (hF'1.differentiable one_ne_zero x).hasFDerivAt
    have hG'd : HasFDerivAt G' (fderiv ℝ G' x) (prL z) := by
      rw [hprz]; exact (hG'1.differentiable one_ne_zero x).hasFDerivAt
    have hd := (hF'd.comp z prL.hasFDerivAt).fun_add (e0.hasFDerivAt.fun_smul
      ((hG'd.comp z prL.hasFDerivAt).fun_sub (hF'd.comp z prL.hasFDerivAt)))
    have hfd : fderiv ℝ H' z = (fderiv ℝ F' x).comp prL +
        (e0 z • ((fderiv ℝ G' x).comp prL - (fderiv ℝ F' x).comp prL) +
          e0.smulRight (G' (prL z) - F' (prL z))) := by
      rw [hloc.fderiv_eq]; exact hd.fderiv
    -- `DH'(z) ê₀ = G'x - F'x` and `DH'(z) ∘ J = DF'(x) + t (DG'(x) - DF'(x))`
    have hDe : fderiv ℝ H' z (EuclideanSpace.single 0 1) = G' x - F' x := by
      have h0 : prL (EuclideanSpace.single 0 1) = 0 := by
        change (WithLp.toLp 2 (Fin.tail (WithLp.ofLp
          (EuclideanSpace.single (0 : Fin (P + 1)) (1 : ℝ)))) : Euclid P) = 0
        ext i
        simp [Fin.tail, Fin.succ_ne_zero]
      have h1 : e0 (EuclideanSpace.single 0 1) = 1 := by simp [e0]
      rw [hfd]
      simp [h0, h1, hprz]
    have hDJ : (fderiv ℝ H' z).comp J = fderiv ℝ F' x + t • (fderiv ℝ G' x - fderiv ℝ F' x) := by
      rw [hfd]
      ext1 v
      have h0 : prL (J v) = v := rfl
      have h1 : e0 (J v) = 0 := rfl
      simp [h0, h1, he0z]
    have hHz : H' z = F' x + t • (G' x - F' x) := by
      change F' (prL z) + (a (e0 z) * χ (prL z)) • (G' (prL z) - F' (prL z)) = _
      rw [hprz, he0z, hχW x hxW, haI t ht, mul_one]
    -- `((ω ∘ DH') ⌞ ê₀) ∘ J = (ω ⌞ DH' ê₀) ∘ (DH' ∘ J)`
    rw [hHz, hι, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap, hDe, ← hDJ]
    rfl

/-- **The affine homotopy operator** `h_#([[(0,1)]] × X)` (Simon 6.2.25–6.2.27).  Assume the
Lipschitz push-forward (IPF) of finite-mass integer multiplicity representations.  Fix an integer
multiplicity `X` vanishing off a compact `E₀`, represented by `R₀`, and let `R'` be the product
representation of `[[(0,1)]] × X` (`dor_lmb_fcdp_product_imrep`) and `Y'` its push-forward.  With
a smooth cut-off `χ = 1` near `E₀` and a smooth bounded `s` with `s(t) = t` on `(-1,2)`, put
`Ĥ(y) = F(pr y) + s(y₀)χ(pr y)(G − F)(pr y)` and `homot k F G X := Y'(Ĥ)`.  The cut-offs of the
definition are already smooth, so no separate a.e. comparison with a smooth `Ĥ*` is needed.  `Ĥ` is
Lipschitz and the smooth `Ĥⱼ` built from `Fⱼ, Gⱼ` converge to it (`dor_lmb_fcdp_homotopy_maps`), so
`homot` is integer multiplicity and local, and the product action formula with the pulled-back
integrand identity gives `R₀.action(Kⱼω) → homot(ω)`; locality of `R₀` on `E` gives (H3).  For (H4)
the segments `hⱼ(t,x)` eventually avoid `spt ω`, and for (H5) Hadamard's inequality gives
`|Kⱼω(x)(τ)| ≤ (δ + ε)Λᵏ` on `E` (`dor_lmb_fcdp_toolkit_push`). -/
theorem Submission.dor_lmb_fcdp_homot_operator : (∀ (N N' k : ℕ) (R : IMRep (univ : Set (Euclid N)) k), R.measure univ ≠ ∞ → ∃ Y : (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N')) k, (∀ (F : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → IsIntegerMultiplicity (Y F) ∧ ∀ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, LipschitzWith Λ (Fs j)) → TendstoUniformly Fs F atTop → ∀ ω : TestFormOn (univ : Set (Euclid N')) k, Tendsto (fun j => R.action (fun x => ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x))) atTop (𝓝 (Y F ω))) ∧ ∀ (F F' : Euclid N → Euclid N') (Λ : NNReal), LipschitzWith Λ F → LipschitzWith Λ F' → (∀ᵐ x ∂(μHE[k].restrict R.carrier), F x = F' x) → Y F = Y F') → ∀ P : ℕ, ∃ homot : ∀ k : ℕ, (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) k → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), ∀ (k : ℕ) (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (homot k F G X) ∧ (∀ F' G' : Euclid P → Euclid P, LipschitzWith Λ F' → LipschitzWith Λ G' → EqOn F F' E → EqOn G G' E → homot k F G X = homot k F' G' X) ∧ (∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (homot k F G X ω))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → homot k F G X ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (homot k F G X).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
  intro hIPF P
  obtain ⟨hT1, hT2, hT3, hT4, hT5⟩ := Submission.dor_lmb_fcdp_toolkit_push.1
  have h1top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- a.e. membership in `S` on a carrier `C` with `Hᵈ(C \ S) = 0`
  have hgen : ∀ (N d : ℕ) (C S : Set (Euclid N)), MeasurableSet C → μHE[d] (C \ S) = 0 →
      ∀ᵐ y ∂(μHE[d].restrict C), y ∈ S := by
    intro N d C S hC hS
    refine (ae_restrict_iff' hC).2 (ae_iff.2 (measure_mono_null (fun y hy => ?_) hS))
    exact not_imp.1 hy
  -- step 1: a `C¹` bounded Lipschitz `s : ℝ → ℝ` with `s t = t` on `(-1, 2)`, `s(t) = tφ(t)`
  obtain ⟨s, hs1, ⟨Ls, hsL⟩, ⟨As, hsA⟩, hsid⟩ : ∃ s : ℝ → ℝ, ContDiff ℝ 1 s ∧
      (∃ L : NNReal, LipschitzWith L s) ∧ (∃ A : ℝ, ∀ t, |s t| ≤ A) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 2, s t = t := by
    let φ : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 2, 5 / 2, by norm_num, by norm_num⟩
    have hc : ContDiff ℝ 1 (fun t : ℝ => t * φ t) := contDiff_id.mul (φ.contDiff (n := 1))
    have hcs : HasCompactSupport (fun t : ℝ => t * φ t) := φ.hasCompactSupport.mul_left (f := id)
    obtain ⟨A, hA⟩ := hc.continuous.bounded_above_of_compact_support hcs
    refine ⟨fun t => t * φ t, hc, ContDiff.lipschitzWith_of_hasCompactSupport hcs hc one_ne_zero,
      ⟨A, fun t => by simpa [Real.norm_eq_abs] using hA t⟩, fun t ht => ?_⟩
    have hmem : t ∈ closedBall (1 / 2 : ℝ) (3 / 2) := by
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hφ : φ t = 1 := φ.one_of_mem_closedBall hmem
    simp only [hφ, mul_one]
  -- step 2: for each current `X` choose the homotopy operator `F, G ↦ Y'(Ĥ_{F,G})`
  have key : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), ∃ H : (Euclid P → Euclid P) → (Euclid P → Euclid P) → GeometricCurrentOn (univ : Set (Euclid P)) (k + 1), ∀ (Λ : NNReal) (F G : Euclid P → Euclid P) (E : Set (Euclid P)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact E → IsIntegerMultiplicity X → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E → X ω = 0) → IsIntegerMultiplicity (H F G) ∧ (∀ F' G' : Euclid P → Euclid P, LipschitzWith Λ F' → LipschitzWith Λ G' → EqOn F F' E → EqOn G G' E → H F G = H F' G') ∧ (∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)) (ηs : ℕ → TestFormOn (univ : Set (Euclid P)) k), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → (∀ j, ∀ x ∈ E, (ηs j : DifferentialForm (Euclid P) k) x = ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x))) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (H F G ω))) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → H F G ω = 0) ∧ ∀ δ : ℝ, (∀ x ∈ E, dist (F x) (G x) ≤ δ) → (H F G).mass ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
    intro k X
    by_cases hX : ∃ E₀ : Set (Euclid P), IsCompact E₀ ∧ IsIntegerMultiplicity X ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
          Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) E₀ → X ω = 0
    swap
    · exact ⟨fun _ _ => 0, fun Λ F G E _ _ hE hXI hXE => absurd ⟨E, hE, hXI, hXE⟩ hX⟩
    -- `X = τ(R₀)` vanishes off the compact `E₀`; `R'` is the product representation of
    -- `[[(0,1)]] × X`, `Y'` its push-forward, `χ = 1` on an open `W ⊇ E₀`
    obtain ⟨E₀, hE₀, ⟨R₀, hR₀⟩, hXE₀⟩ := hX
    obtain ⟨-, hmass, hR₀fin, hlocE₀⟩ := hT1 P k X R₀ E₀ hR₀ hE₀ hXE₀
    obtain ⟨R', hR'fin, hR'ae, hR'act⟩ := Submission.dor_lmb_fcdp_product_imrep P k R₀ hR₀fin
    obtain ⟨Y, hYa, hYb⟩ := hIPF (P + 1) P (k + 1) R' hR'fin
    obtain ⟨χ, W, hχs, hχc, -, hWo, hE₀W, hχW⟩ := hT5 P E₀ hE₀
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le h1top
    obtain ⟨Lχ, hχL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ1 one_ne_zero
    -- pull-backs of test forms by `C¹` Lipschitz maps are continuous and bounded
    have hpull : ∀ (Φ : Euclid (P + 1) → Euclid P) (LΦ : NNReal), ContDiff ℝ 1 Φ →
        LipschitzWith LΦ Φ → ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1),
        Continuous (fun y => ((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
          (fderiv ℝ Φ y)) ∧
        ∃ C : ℝ, ∀ y, ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
          (fderiv ℝ Φ y)‖ ≤ C := by
      intro Φ LΦ hΦ hΦL ω
      have hωc : Continuous (ω : DifferentialForm (Euclid P) (k + 1)) := ω.property.1.1.continuous
      obtain ⟨Cω, hCω⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
      have hcomp : Continuous (ContinuousAlternatingMap.compContinuousLinearMapCLM :
          (Euclid (P + 1) →L[ℝ] Euclid P) →
            (Euclid P [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] (Euclid (P + 1) [⋀^Fin (k + 1)]→L[ℝ] ℝ)) :=
        continuousOn_univ.1
          (ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM univ).continuousOn
      refine ⟨(hcomp.comp (hΦ.continuous_fderiv one_ne_zero)).clm_apply (hωc.comp hΦ.continuous),
        Cω * (LΦ : ℝ) ^ (k + 1), fun y => ?_⟩
      calc ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)).compContinuousLinearMap
            (fderiv ℝ Φ y)‖
          ≤ ‖(ω : DifferentialForm (Euclid P) (k + 1)) (Φ y)‖ *
              ‖fderiv ℝ Φ y‖ ^ Fintype.card (Fin (k + 1)) :=
            ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
        _ ≤ Cω * (LΦ : ℝ) ^ (k + 1) := by
            rw [Fintype.card_fin]
            exact mul_le_mul (hCω _)
              (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hΦL) _)
              (by positivity) ((norm_nonneg _).trans (hCω 0))
    refine ⟨fun F G => Y (fun y => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))), ?_⟩
    intro Λ F G E hF hG hE _ hXE
    -- step 3: `Hᵏ(M \ E) = 0`, `M(X) = μ_{R₀}(ℝᴾ) < ∞` and `R₀` is local on `E`
    obtain ⟨hR₀E, -, -, hlocE⟩ := hT1 P k X R₀ E hR₀ hE hXE
    have hHM := Submission.dor_lmb_fcdp_homotopy_maps P Λ Ls Lχ As s χ F G hF hG hsL hsA hχL hχc
    -- step 4: `Ĥ` is Lipschitz
    obtain ⟨L₀, hL₀⟩ := hHM.1
    -- step 7: `R₀.action(Kⱼω) → homot k F G X (ω)`
    have hchar : ∀ (Fs Gs : ℕ → Euclid P → Euclid P) (ω : TestFormOn (univ : Set (Euclid P)) (k + 1)), (∀ j, ContDiff ℝ 1 (Fs j)) → (∀ j, ContDiff ℝ 1 (Gs j)) → (∀ j, LipschitzWith Λ (Fs j)) → (∀ j, LipschitzWith Λ (Gs j)) → TendstoUniformly Fs F atTop → TendstoUniformly Gs G atTop → Tendsto (fun j => R₀.action (fun x => ∫ t in (0 : ℝ)..1, (((ω : DifferentialForm (Euclid P) (k + 1)) (Fs j x + t • (Gs j x - Fs j x))).curryLeft (Gs j x - Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x + t • (fderiv ℝ (Gs j) x - fderiv ℝ (Fs j) x)))) atTop (𝓝 (Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω)) := by
      intro Fs Gs ω hFs hGs hFsL hGsL hFsu hGsu
      -- the smooth `Ĥⱼ` are `C¹`, uniformly Lipschitz and converge uniformly to `Ĥ`
      obtain ⟨hHj1, ⟨L, hHjL⟩, hHju⟩ := hHM.2.1 hs1 hχ1 Fs Gs hFs hGs hFsL hGsL hFsu hGsu
      have hlim := (hYa _ (max L₀ L) (hL₀.weaken (le_max_left _ _))).2 _ hHj1
        (fun j => (hHjL j).weaken (le_max_right _ _)) hHju ω
      refine Tendsto.congr (fun j => ?_) hlim
      -- product action formula, then the pulled-back integrand identity on `W ⊇ E₀`
      obtain ⟨hβc, hβb⟩ := hpull _ _ (hHj1 j) (hHjL j) ω
      refine (hR'act _ hβc hβb).trans
        (hlocE₀ _ _ (fun x hx => intervalIntegral.integral_congr (fun t ht => ?_)))
      rw [uIcc_of_le zero_le_one] at ht
      exact hHM.2.2 (Fs j) (Gs j) W k (ω : DifferentialForm (Euclid P) (k + 1)) t x hs1 hχ1
        (hFs j) (hGs j) hWo hχW hsid (hE₀W hx) ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- step 9: smooth Lipschitz approximations of `F` and `G`
    obtain ⟨Fa, hFa, hFaL, hFau⟩ := hT4 P P Λ F hF
    obtain ⟨Ga, hGa, hGaL, hGau⟩ := hT4 P P Λ G hG
    have hFa1 : ∀ j, ContDiff ℝ 1 (Fa j) := fun j => (hFa j).of_le h1top
    have hGa1 : ∀ j, ContDiff ℝ 1 (Ga j) := fun j => (hGa j).of_le h1top
    -- step 10 (H4): the segments `hⱼ(t,x)` eventually avoid `spt ω`
    have hH4 : ∀ ω : TestFormOn (univ : Set (Euclid P)) (k + 1), Disjoint (tsupport (ω : DifferentialForm (Euclid P) (k + 1))) {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} → Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω = 0 := by
      intro ω hω
      -- the trace `Σ` is compact
      have hTr : IsCompact {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} := by
        have hTreq : {y : Euclid P | ∃ x ∈ E, ∃ t ∈ Icc (0 : ℝ) 1, y = F x + t • (G x - F x)} =
            (fun p : ℝ × Euclid P => F p.2 + p.1 • (G p.2 - F p.2)) '' (Icc 0 1 ×ˢ E) := by
          ext y
          constructor
          · rintro ⟨x, hx, t, ht, rfl⟩
            exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
          · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
            exact ⟨x, hx, t, ht, rfl⟩
        rw [hTreq]
        exact (isCompact_Icc.prod hE).image ((hF.continuous.comp continuous_snd).add
          (continuous_fst.smul ((hG.continuous.comp continuous_snd).sub
            (hF.continuous.comp continuous_snd))))
      obtain ⟨d, hd, hdisj⟩ := Disjoint.exists_thickenings hω.symm hTr (isClosed_tsupport _)
      refine tendsto_nhds_unique (hchar Fa Ga ω hFa1 hGa1 hFaL hGaL hFau hGau)
        (tendsto_const_nhds.congr' ?_)
      filter_upwards [Metric.tendstoUniformly_iff.1 hFau d hd,
        Metric.tendstoUniformly_iff.1 hGau d hd] with j hjF hjG
      have h0 : R₀.action (0 : DifferentialForm (Euclid P) k) = 0 := by simp [IMRep.action]
      refine ((hlocE _ 0 (fun x hx => ?_)).trans h0).symm
      simp only [Pi.zero_apply]
      refine (intervalIntegral.integral_congr (g := fun _ => 0) (fun t ht => ?_)).trans
        intervalIntegral.integral_zero
      rw [uIcc_of_le zero_le_one] at ht
      -- `hⱼ(t,x)` lies within `d` of `F x + t(G x − F x) ∈ Σ`
      have hnot : Fa j x + t • (Ga j x - Fa j x) ∉
          tsupport (ω : DifferentialForm (Euclid P) (k + 1)) := by
        intro hmem
        refine Set.disjoint_left.1 hdisj ?_ (Metric.self_subset_thickening hd _ hmem)
        rw [Metric.mem_thickening_iff]
        refine ⟨F x + t • (G x - F x), ⟨x, hx, t, ht, rfl⟩, ?_⟩
        have e : Fa j x + t • (Ga j x - Fa j x) - (F x + t • (G x - F x)) =
            (1 - t) • (Fa j x - F x) + t • (Ga j x - G x) := by
          simp only [smul_sub, sub_smul, one_smul]
          abel
        have ha : ‖Fa j x - F x‖ < d := by rw [← dist_eq_norm, dist_comm]; exact hjF x
        have hb : ‖Ga j x - G x‖ < d := by rw [← dist_eq_norm, dist_comm]; exact hjG x
        rw [dist_eq_norm, e]
        calc ‖(1 - t) • (Fa j x - F x) + t • (Ga j x - G x)‖
            ≤ ‖(1 - t) • (Fa j x - F x)‖ + ‖t • (Ga j x - G x)‖ := norm_add_le _ _
          _ = (1 - t) * ‖Fa j x - F x‖ + t * ‖Ga j x - G x‖ := by
              rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
                Real.norm_of_nonneg ht.1]
          _ ≤ (1 - t) * max ‖Fa j x - F x‖ ‖Ga j x - G x‖ +
                t * max ‖Fa j x - F x‖ ‖Ga j x - G x‖ :=
              add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith [ht.2]))
                (mul_le_mul_of_nonneg_left (le_max_right _ _) ht.1)
          _ = max ‖Fa j x - F x‖ ‖Ga j x - G x‖ := by ring
          _ < d := max_lt ha hb
      have hz : (ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x)) = 0 :=
        image_eq_zero_of_notMem_tsupport hnot
      simp only [hz]
      ext v
      simp
    refine ⟨(hYa _ L₀ hL₀).1, ?_, ?_, hH4, ?_⟩
    -- step 6 (H2): `Ĥ_{F,G} = Ĥ_{F',G'}` on `ι([0,1] × E)`, which carries `R'` a.e.
    · intro F' G' hF' hG' hFF' hGG'
      obtain ⟨L₁, hL₁⟩ :=
        (Submission.dor_lmb_fcdp_homotopy_maps P Λ Ls Lχ As s χ F' G' hF' hG' hsL hsA hχL hχc).1
      refine hYb _ _ (max L₀ L₁) (hL₀.weaken (le_max_left _ _)) (hL₁.weaken (le_max_right _ _)) ?_
      filter_upwards [hgen (P + 1) (k + 1) R'.carrier _ R'.measurableSet_carrier
        (hR'ae E hE.isClosed.measurableSet hR₀E)] with y hy
      obtain ⟨⟨t, x⟩, ⟨-, hx⟩, rfl⟩ := hy
      have hx' : x ∈ E := hx
      simp only [Fin.tail_cons, WithLp.toLp_ofLp, hFF' hx', hGG' hx']
    -- step 8 (H3): `X(ηⱼ) = R₀.action(ηⱼ) = R₀.action(Kⱼω)` by locality on `E`
    · intro Fs Gs ω ηs hFs hGs hFsL hGsL hFsu hGsu hη
      refine Tendsto.congr (fun j => ?_) (hchar Fs Gs ω hFs hGs hFsL hGsL hFsu hGsu)
      exact (hlocE _ _ (fun x hx => (hη j x hx).symm)).trans (hR₀ (ηs j)).symm
    -- step 11 (H5): `|R₀.action(Kⱼω)| ≤ (δ + ε)Λᵏ M(X)` eventually, by Hadamard's inequality
    · intro δ hδ
      rcases E.eq_empty_or_nonempty with hE0 | ⟨x₀, hx₀⟩
      · refine le_trans (sSup_le ?_) zero_le
        rintro _ ⟨ω, -, rfl⟩
        simp only [hH4 ω (by simp [hE0]), ENNReal.ofReal_zero, le_refl]
      have hδ0 : 0 ≤ δ := dist_nonneg.trans (hδ x₀ hx₀)
      refine sSup_le ?_
      rintro _ ⟨ω, hωadm, rfl⟩
      have hωb : ∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (k + 1)) y) ≤ 1 :=
        hωadm.2
      have hε : ∀ ε : ℝ, 0 < ε → Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω ≤ (δ + ε) * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal) := by
        intro ε hε
        refine le_of_tendsto (hchar Fa Ga ω hFa1 hGa1 hFaL hGaL hFau hGau) ?_
        filter_upwards [Metric.tendstoUniformly_iff.1 hFau (ε / 2) (half_pos hε),
          Metric.tendstoUniformly_iff.1 hGau (ε / 2) (half_pos hε)] with j hjF hjG
        refine (le_abs_self _).trans ((hT3 P k univ R₀ _ ((δ + ε) * (Λ : ℝ) ^ k) hR₀fin
          (mul_nonneg (by linarith) (by positivity)) ?_).trans (le_of_eq (mul_assoc _ _ _)))
        filter_upwards [hgen P k R₀.carrier E R₀.measurableSet_carrier hR₀E] with x hx τ hτ
        beta_reduce
        rw [← Real.norm_eq_abs]
        refine (ContinuousAlternatingMap.le_opNorm _ _).trans ?_
        rw [Finset.prod_eq_one (fun i _ => hτ.1 i), mul_one]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := (δ + ε) * (Λ : ℝ) ^ k) (fun t ht => ?_)).trans (le_of_eq (by simp))
        rw [uIoc_of_le zero_le_one] at ht
        -- `|ω(hⱼ)| ≤ 1`, `‖Gⱼx − Fⱼx‖ ≤ δ + ε` and `‖DFⱼ(x) + t(DGⱼ(x) − DFⱼ(x))‖ ≤ Λ`
        have hωh : ‖(ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))‖ ≤ 1 := by
          refine ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
          rw [Real.norm_eq_abs, one_mul]
          exact (hT2 P (k + 1) _ v).trans (mul_le_of_le_one_left
            (Finset.prod_nonneg (fun i _ => norm_nonneg _)) (hωb _))
        have hV : ‖Ga j x - Fa j x‖ ≤ δ + ε := by
          have e : Ga j x - Fa j x = (Ga j x - G x) + (G x - F x) + (F x - Fa j x) := by abel
          have h1 : ‖Ga j x - G x‖ < ε / 2 := by rw [← dist_eq_norm, dist_comm]; exact hjG x
          have h2 : ‖G x - F x‖ ≤ δ := by rw [← dist_eq_norm, dist_comm]; exact hδ x hx
          have h3 : ‖F x - Fa j x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hjF x
          rw [e]
          calc ‖(Ga j x - G x) + (G x - F x) + (F x - Fa j x)‖
              ≤ ‖(Ga j x - G x) + (G x - F x)‖ + ‖F x - Fa j x‖ := norm_add_le _ _
            _ ≤ ‖Ga j x - G x‖ + ‖G x - F x‖ + ‖F x - Fa j x‖ :=
                add_le_add (norm_add_le _ _) le_rfl
            _ ≤ δ + ε := by linarith
        have hA : ‖fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x)‖ ≤ Λ :=
          mem_closedBall_zero_iff.1 ((convex_closedBall (0 : Euclid P →L[ℝ] Euclid P) Λ).add_smul_sub_mem
            (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ (hFaL j)))
            (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ (hGaL j))) ⟨ht.1.le, ht.2⟩)
        calc ‖(((ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))).curryLeft
              (Ga j x - Fa j x)).compContinuousLinearMap
              (fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x))‖
            ≤ ‖((ω : DifferentialForm (Euclid P) (k + 1)) (Fa j x + t • (Ga j x - Fa j x))).curryLeft
                (Ga j x - Fa j x)‖ *
              ‖fderiv ℝ (Fa j) x + t • (fderiv ℝ (Ga j) x - fderiv ℝ (Fa j) x)‖ ^
                Fintype.card (Fin k) :=
              ContinuousAlternatingMap.norm_compContinuousLinearMap_le _ _
          _ ≤ (1 * (δ + ε)) * (Λ : ℝ) ^ k := by
              rw [Fintype.card_fin]
              refine mul_le_mul ?_ (pow_le_pow_left₀ (norm_nonneg _) hA k) (by positivity)
                (by linarith)
              refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
              rw [ContinuousAlternatingMap.norm_curryLeft]
              exact mul_le_mul hωh hV (norm_nonneg _) zero_le_one
          _ = (δ + ε) * (Λ : ℝ) ^ k := by ring
      -- let `ε → 0`
      have hY : Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω ≤ δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal) := by
        have hc : Tendsto (fun ε : ℝ => (δ + ε) * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal))
            (𝓝[>] 0) (𝓝 (δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal))) := by
          have h := ((tendsto_const_nhds (x := δ)).add (tendsto_id (x := 𝓝 (0 : ℝ)))).mul
            (tendsto_const_nhds (x := (Λ : ℝ) ^ k * (R₀.measure univ).toReal))
          rw [add_zero] at h
          exact h.mono_left nhdsWithin_le_nhds
        exact ge_of_tendsto hc (eventually_nhdsWithin_of_forall (fun ε hε' => hε ε hε'))
      calc ENNReal.ofReal (Y (fun y : Euclid (P + 1) => F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) + (s (WithLp.ofLp y 0) * χ (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)))) • (G (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))) - F (WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))))) ω)
          ≤ ENNReal.ofReal (δ * ((Λ : ℝ) ^ k * (R₀.measure univ).toReal)) :=
            ENNReal.ofReal_le_ofReal hY
        _ = ENNReal.ofReal δ * (Λ : ℝ≥0∞) ^ k * X.mass := by
            rw [ENNReal.ofReal_mul hδ0, ENNReal.ofReal_mul (pow_nonneg (NNReal.coe_nonneg Λ) k),
              ENNReal.ofReal_pow (NNReal.coe_nonneg Λ), ENNReal.ofReal_coe_nnreal,
              ENNReal.ofReal_toReal hR₀fin, hmass, mul_assoc]
        _ ≤ ENNReal.ofReal δ * (2 * (Λ : ℝ≥0∞)) ^ k * X.mass := by
            gcongr
            exact le_mul_of_one_le_left zero_le one_le_two
  choose H hH using key
  exact ⟨fun k F G X => H k X F G, fun k Λ F G E X hF hG hE hXI hXE => hH k X Λ F G E hF hG hE hXI hXE⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
