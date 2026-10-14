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

/-- **A null set at whose points the measure is locally finite has open neighbourhoods of
arbitrarily small measure** (localized outer regularity).  The balls `B(x, r(x))` of finite
measure, `x ∈ A`, have a countable subfamily `B(i, r(i))`, `i ∈ T ⊆ A`, still covering `A`
(Lindelöf).  With budgets `δᵢ > 0`, `∑ᵢ δᵢ < ε`, outer regularity of the finite measure
`μ ⌞ B(i, r(i))` at `A` gives an open `Uᵢ ⊇ A` with `μ (Uᵢ ∩ B(i, r(i))) < δᵢ`; take
`O = ⋃ᵢ Uᵢ ∩ B(i, r(i))`. -/
theorem Submission.dorag_sn_open_superset_measure_lt : ∀ (N : ℕ) (μ : Measure (Euclid N)) (A : Set (Euclid N)), μ A = 0 → (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ μ (ball x r) ≠ ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ O : Set (Euclid N), IsOpen O ∧ A ⊆ O ∧ μ O < ε := by
  intro N μ A hA hloc ε hε
  choose! r hr hfin using hloc
  -- Lindelöf: countably many of the balls `B(x, r(x))`, `x ∈ A`, still cover `A`
  obtain ⟨T, hTA, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable A
    (fun x => ball x (r x)) fun x _ => isOpen_ball
  have : Countable T := hTc.to_subtype
  -- budgets `δᵢ > 0` with `∑ᵢ δᵢ < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' T
  -- outer regularity of the finite measure `μ ⌞ B(i, r(i))` at the null set `A`
  have hU : ∀ i : T, ∃ U : Set (Euclid N), A ⊆ U ∧ IsOpen U ∧
      μ (U ∩ ball (i : Euclid N) (r i)) < δ i := by
    intro i
    have : IsFiniteMeasure (μ.restrict (ball (i : Euclid N) (r i))) :=
      isFiniteMeasure_restrict.2 (hfin i (hTA i.2))
    obtain ⟨U, hAU, hUo, hUδ⟩ := A.exists_isOpen_lt_of_lt
      (μ := μ.restrict (ball (i : Euclid N) (r i))) (δ i)
      ((Measure.restrict_apply_le _ A).trans_lt (by rw [hA]; exact hδ i))
    exact ⟨U, hAU, hUo, by rwa [Measure.restrict_apply hUo.measurableSet] at hUδ⟩
  choose U hAU hUo hUδ using hU
  refine ⟨⋃ i : T, U i ∩ ball (i : Euclid N) (r i),
    isOpen_iUnion fun i => (hUo i).inter isOpen_ball, fun x hx => ?_, ?_⟩
  · obtain ⟨i, hiT, hxi⟩ :=
      mem_iUnion₂.1 (hTU.superset (mem_biUnion hx (mem_ball_self (hr x hx))))
    exact mem_iUnion.2 ⟨⟨i, hiT⟩, hAU _ hx, hxi⟩
  · calc μ (⋃ i : T, U i ∩ ball (i : Euclid N) (r i))
        ≤ ∑' i : T, μ (U i ∩ ball (i : Euclid N) (r i)) := measure_iUnion_le _
      _ ≤ ∑' i : T, δ i := ENNReal.tsum_le_tsum fun i => (hUδ i).le
      _ < ε := hδε
/-- **Simon Ch. 1, Theorem 3.3** (comparison theorem, p. 14), with a non-sharp constant and
`Hⁿ = μHE[n]` on `ℝᴺ`: if `ν(B̄_t(x)) ≥ c tⁿ` for all small `t > 0` at every point `x` of a subset
`A` of an open set `O`, then `Hⁿ(A) ≤ C ν(O)` with `C = C(n, c) < ∞`.  At each scale `δ` the
5-times covering lemma (Simon 3.4) selects, among the balls `B̄_r(x) ⊆ O` with `x ∈ A`, `10r ≤ δ`
and `ν(B̄_r(x)) ≥ c rⁿ`, a disjoint, hence countable, subfamily whose 5-times enlargements cover
`A`.  This `δ`-cover costs `Σ (10rⱼ)ⁿ ≤ (10ⁿ/c) Σ ν(B̄_{rⱼ}(xⱼ)) ≤ (10ⁿ/c) ν(O)`, and `μHE[n]` is
a finite multiple of `μH[n]`. -/
theorem Submission.dorag_sn_hausdorff_le_mul_of_lower_density : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
  intro N n c hc
  -- `μHE[n] = k • μH[n]` with a finite factor `k`; take `C = k · 10ⁿ / c`
  set k : NNReal :=
    Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)]
  refine ⟨(k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro ν A O hO hAO hA
  have hdiam : ∀ (y : Euclid N) (ρ : ℝ), ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
    intro y ρ
    apply ediam_le_of_forall_dist_le
    intro z hz w hw
    rw [mem_closedBall] at hz hw
    linarith [dist_triangle_right z w y]
  -- scale `δ = 1 / (m + 1)`: a countable disjoint family of admissible balls whose 5-times
  -- enlargements cover `A`, of total cost at most `(10ⁿ/c) ν(O)`
  have step : ∀ m : ℕ, ∃ u : Set (Euclid N × ℝ), u.Countable ∧
      (∀ p ∈ u, ediam (closedBall p.1 (5 * p.2)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1))) ∧
      A ⊆ ⋃ p : u, closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2) ∧
      ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) ≤
        ENNReal.ofReal (10 ^ n / c) * ν O := by
    intro m
    set δ : ℝ := 1 / ((m : ℝ) + 1)
    have hδpos : 0 < δ := by positivity
    -- the admissible balls, as (center, radius) pairs
    set T : Set (Euclid N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧
      closedBall p.1 p.2 ⊆ O ∧ ENNReal.ofReal (c * p.2 ^ n) ≤ ν (closedBall p.1 p.2)}
    obtain ⟨u, huT, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun p => p.1)
        (fun p => p.2) δ (fun p hp => by linarith [hp.2.2.1, hp.2.1]) 5 (by norm_num)
    -- disjoint balls with nonempty interiors in the separable space `ℝᴺ`
    have hucount : u.Countable := by
      refine hudisj.countable_of_nonempty_interior fun p hp => ?_
      exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huT hp).2.1)⟩
    refine ⟨u, hucount, fun p hp => ?_, ?_, ?_⟩
    · obtain ⟨-, -, hpδ, -, -⟩ := huT hp
      refine (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    · -- each `x ∈ A` is the center of a small admissible ball
      intro x hx
      obtain ⟨t₀, ht₀, hbound⟩ := hA x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
      set r : ℝ := min (t₀ / 2) (min (ε / 2) (δ / 10))
      have hrpos : 0 < r := by positivity
      have hr₁ := min_le_left (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₂ := min_le_right (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₃ := min_le_left (ε / 2) (δ / 10)
      have hr₄ := min_le_right (ε / 2) (δ / 10)
      have hmem : (x, r) ∈ T :=
        ⟨hx, hrpos, by linarith, (closedBall_subset_ball (by linarith)).trans hball,
          hbound r hrpos (by linarith)⟩
      obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hmem
      exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_closedBall_self hrpos.le)⟩
    · calc ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
          ≤ ∑' p : u, ENNReal.ofReal (10 ^ n / c) *
              ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            obtain ⟨-, hp0, -, -, hpν⟩ := huT p.2
            calc ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (2 * (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) :=
                  ENNReal.rpow_le_rpow (hdiam _ _) (Nat.cast_nonneg n)
              _ = ENNReal.ofReal (10 ^ n / c) * ENNReal.ofReal (c * (p : Euclid N × ℝ).2 ^ n) := by
                  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
                    ← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  field_simp
                  ring
              _ ≤ ENNReal.ofReal (10 ^ n / c) *
                    ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
                  gcongr
        _ = ENNReal.ofReal (10 ^ n / c) * ν (⋃ p ∈ u, closedBall p.1 p.2) := by
            rw [ENNReal.tsum_mul_left,
              measure_biUnion hucount hudisj fun p _ => measurableSet_closedBall]
        _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
            gcongr
            exact iUnion₂_subset fun p hp => (huT hp).2.2.2.1
  choose u hucount hudiam hucov husum using step
  have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
  -- covers of mesh `1 / (m + 1) → 0`
  have main : μH[(n : ℝ)] A ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
    calc μH[(n : ℝ)] A
        ≤ liminf (fun m => ∑' p : u m,
            ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)) atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) A
            (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) ?_
            (fun m p => closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2))
            (Eventually.of_forall fun m p => hudiam m p p.2) (Eventually.of_forall hucov)
          simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O :=
          liminf_le_of_frequently_le' (Frequently.of_forall husum)
  calc μHE[n] A = (k : ℝ≥0∞) * μH[(n : ℝ)] A := by
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul]
    _ ≤ (k : ℝ≥0∞) * (ENNReal.ofReal (10 ^ n / c) * ν O) := by gcongr
    _ = (k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c) * ν O := by rw [mul_assoc]
/-- **Simon Ch. 4, §3 (p. 90)**, the cutoff `φ` chosen after (3.3), with `1 + ε = A`: for `A > 1`
there is a `C¹` nonincreasing `φ` with `0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]`, `φ ≡ 0` on `[A, ∞)`,
`φ' ≤ 0`, and `φ'(u) ≠ 0` only for `1 < u < A`.  Take `φ(u) = Ψ((A − u)/(A − 1))` for Mathlib's
smooth transition `Ψ` (`Ψ = 0` on `(-∞, 0]`, `Ψ = 1` on `[1, ∞)`, monotone).  `φ` is antitone, so
`φ' ≤ 0`; on the plateaus `u` is a global extremum of `φ`, so `φ'(u) = 0`. -/
theorem Submission.doragm_sab_cutoff_profile : ∀ (A : ℝ), 1 < A → ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ Antitone φ ∧ (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) ∧ (∀ u, u ≤ 1 → φ u = 1) ∧ (∀ u, A ≤ u → φ u = 0) ∧ (∀ u, deriv φ u ≤ 0) ∧ (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) := by
  intro A hA
  -- `a = A − 1 > 0` and `φ(u) = Ψ((A − u)/a)` for the smooth transition `Ψ`
  have ha : 0 < A - 1 := sub_pos.2 hA
  set φ : ℝ → ℝ := fun u => Real.smoothTransition ((A - u) / (A - 1))
  -- `u ↦ (A − u)/a` is antitone and `Ψ` is monotone
  have hanti : Antitone φ := fun u v huv =>
    Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_left huv A) ha.le)
  have hbd : ∀ u, 0 ≤ φ u ∧ φ u ≤ 1 := fun u =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- `u ≤ 1` gives `(A − u)/a ≥ 1`, and `A ≤ u` gives `(A − u)/a ≤ 0`
  have h1 : ∀ u, u ≤ 1 → φ u = 1 := fun u hu =>
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ ha).2 (by linarith))
  have h0 : ∀ u, A ≤ u → φ u = 0 := fun u hu =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
  refine ⟨φ, ?_, hanti, hbd, h1, h0, fun u => hanti.deriv_nonpos, fun u hu => ?_⟩
  · -- `Ψ` is `C^∞` and `u ↦ (A − u)/a` is affine
    exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  · -- on the plateaus `u` is a global maximum (`φ u = 1`) or minimum (`φ u = 0`), so `φ'(u) = 0`
    by_contra hcon
    rcases le_or_gt u 1 with hu1 | hu1
    · refine hu (IsLocalMax.deriv_eq_zero ?_)
      exact (isMaxOn_univ_iff.2 fun v => (h1 u hu1).symm ▸ (hbd v).2).isLocalMax Filter.univ_mem
    · have hAu : A ≤ u := not_lt.1 fun h => hcon ⟨hu1, h⟩
      refine hu (IsLocalMin.deriv_eq_zero ?_)
      exact (isMinOn_univ_iff.2 fun v => (h0 u hAu).symm ▸ (hbd v).1).isLocalMin Filter.univ_mem
/-- **Integrating-factor comparison on `[s, t]`** (Simon Ch. 4, 3.16, p. 92: the integrating-factor
step, done here by comparing derivatives).  If `n I − τ I' + τ J = −h`, `|h| ≤ cτI`,
`J ≥ 0` and `G' ≤ J/τⁿ ≤ K G'` on `[s, t]` (`c ≥ 0`, `0 < s < t`), then with
`Φ_b(σ) = e^{bσ} σ⁻ⁿ I(σ)`: `G(t) − G(s) ≤ Φ_c(t) − Φ_c(s)` and
`Φ_{−c}(t) − Φ_{−c}(s) ≤ K (G(t) − G(s))`.  By the quotient rule and `(E)`,
`Φ_b' = e^{bτ}τ⁻ⁿ (J + bI + h/τ)`; since `cI + h/τ ≥ 0 ≥ −cI + h/τ` and `e^{−cτ} ≤ 1 ≤ e^{cτ}`,
`Φ_c − G` and `K G − Φ_{−c}` have nonnegative derivative, hence are nondecreasing on `[s, t]`. -/
theorem Submission.doragm_sab_exp_ratio_compare : ∀ (n : ℕ) (c K s t : ℝ) (I I' G G' J h : ℝ → ℝ), 0 ≤ c → 0 < s → s < t → (∀ τ ∈ Icc s t, HasDerivAt I (I' τ) τ) → (∀ τ ∈ Icc s t, HasDerivAt G (G' τ) τ) → (∀ τ ∈ Icc s t, (n : ℝ) * I τ - τ * I' τ + τ * J τ = -h τ) → (∀ τ ∈ Icc s t, |h τ| ≤ c * τ * I τ) → (∀ τ ∈ Icc s t, 0 ≤ J τ) → (∀ τ ∈ Icc s t, G' τ ≤ J τ / τ ^ n) → (∀ τ ∈ Icc s t, J τ / τ ^ n ≤ K * G' τ) → G t - G s ≤ Real.exp (c * t) / t ^ n * I t - Real.exp (c * s) / s ^ n * I s ∧ Real.exp (-(c * t)) / t ^ n * I t - Real.exp (-(c * s)) / s ^ n * I s ≤ K * (G t - G s) := by
  intro n c K s t I I' G G' J h hc hs hst hI hG hE hH hJ hC1 hC2
  -- every `τ ∈ [s, t]` is positive
  have hpos : ∀ τ ∈ Icc s t, 0 < τ := fun τ hτ => hs.trans_le hτ.1
  -- `Φ_b(σ) = e^{bσ}/σⁿ · I(σ)` has derivative `e^{bτ}/τⁿ · (J + bI + h/τ)`, by `(E)`
  have hΦ : ∀ b : ℝ, ∀ τ ∈ Icc s t, HasDerivAt (fun σ => Real.exp (b * σ) / σ ^ n * I σ)
      (Real.exp (b * τ) / τ ^ n * (J τ + b * I τ + h τ / τ)) τ := by
    intro b τ hτ
    have hτ0 : τ ≠ 0 := (hpos τ hτ).ne'
    have he : HasDerivAt (fun σ => Real.exp (b * σ)) (Real.exp (b * τ) * b) τ := by
      simpa using ((hasDerivAt_id τ).const_mul b).exp
    have hd := (he.fun_div (hasDerivAt_pow n τ) (pow_ne_zero n hτ0)).fun_mul (hI τ hτ)
    convert hd using 1
    have hI' : I' τ = ((n : ℝ) * I τ + τ * J τ + h τ) / τ := by
      field_simp
      linarith [hE τ hτ]
    rw [hI']
    rcases n with _ | m
    · simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, one_pow, div_one, zero_add]
      field_simp
      ring
    · simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ]
      field_simp
      ring
  -- a nonnegative derivative on `[s, t]` gives `f s ≤ f t`
  have hmono : ∀ f f' : ℝ → ℝ, (∀ τ ∈ Icc s t, HasDerivAt f (f' τ) τ) →
      (∀ τ ∈ Icc s t, 0 ≤ f' τ) → f s ≤ f t := by
    intro f f' hf hf'
    have hmon : MonotoneOn f (Icc s t) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc s t)
        (fun τ hτ => (hf τ hτ).continuousAt.continuousWithinAt) (fun τ hτ => ?_) (fun τ hτ => ?_)
      · rw [interior_Icc] at hτ
        exact (hf τ (Ioo_subset_Icc_self hτ)).hasDerivWithinAt
      · rw [interior_Icc] at hτ
        exact hf' τ (Ioo_subset_Icc_self hτ)
    exact hmon (left_mem_Icc.2 hst.le) (right_mem_Icc.2 hst.le) hst.le
  -- `|h| ≤ cτI` gives `cI + h/τ ≥ 0` and `−cI + h/τ ≤ 0`
  have hsign : ∀ τ ∈ Icc s t, 0 ≤ c * I τ + h τ / τ ∧ -c * I τ + h τ / τ ≤ 0 := by
    intro τ hτ
    have hτ0 := hpos τ hτ
    obtain ⟨hl, hu⟩ := abs_le.1 (hH τ hτ)
    have h1 : -(c * I τ) ≤ h τ / τ := by
      rw [le_div_iff₀ hτ0]; linarith
    have h2 : h τ / τ ≤ c * I τ := by
      rw [div_le_iff₀ hτ0]; linarith
    constructor <;> linarith
  constructor
  · -- (a): `Φ_c' ≥ e^{cτ} J/τⁿ ≥ J/τⁿ ≥ G'`, so `Φ_c − G` is nondecreasing
    have key := hmono (fun σ => Real.exp (c * σ) / σ ^ n * I σ - G σ)
      (fun τ => Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) - G' τ)
      (fun τ hτ => (hΦ c τ hτ).fun_sub (hG τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : 1 ≤ Real.exp (c * τ) := Real.one_le_exp (mul_nonneg hc (hpos τ hτ).le)
        have hA : 0 ≤ Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) :=
          mul_nonneg (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).1
        have hB : J τ / τ ^ n ≤ Real.exp (c * τ) * (J τ / τ ^ n) := le_mul_of_one_le_left hJn hexp
        have hsplit : Real.exp (c * τ) / τ ^ n * (J τ + c * I τ + h τ / τ) =
            Real.exp (c * τ) * (J τ / τ ^ n) + Real.exp (c * τ) / τ ^ n * (c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC1 τ hτ])
    linarith
  · -- (b): `Φ_{−c}' ≤ e^{−cτ} J/τⁿ ≤ J/τⁿ ≤ K G'`, so `K G − Φ_{−c}` is nondecreasing
    have key := hmono (fun σ => K * G σ - Real.exp (-c * σ) / σ ^ n * I σ)
      (fun τ => K * G' τ - Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ))
      (fun τ hτ => ((hG τ hτ).const_mul K).fun_sub (hΦ (-c) τ hτ)) (fun τ hτ => by
        have hτn : 0 < τ ^ n := pow_pos (hpos τ hτ) n
        have hJn : 0 ≤ J τ / τ ^ n := div_nonneg (hJ τ hτ) hτn.le
        have hexp : Real.exp (-c * τ) ≤ 1 :=
          Real.exp_le_one_iff.2 (by nlinarith [hpos τ hτ])
        have hA : Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (div_nonneg (Real.exp_pos _).le hτn.le) (hsign τ hτ).2
        have hB : Real.exp (-c * τ) * (J τ / τ ^ n) ≤ J τ / τ ^ n := mul_le_of_le_one_left hJn hexp
        have hsplit : Real.exp (-c * τ) / τ ^ n * (J τ + -c * I τ + h τ / τ) =
            Real.exp (-c * τ) * (J τ / τ ^ n) + Real.exp (-c * τ) / τ ^ n * (-c * I τ + h τ / τ) := by
          ring
        rw [hsplit]
        linarith [hC2 τ hτ])
    simp only [neg_mul] at key
    linarith
/-- **The mean-curvature term of a radial cutoff** (Simon Ch. 4, 3.16): if `φ ≥ 0` vanishes on
`[A, ∞)`, `τ > 0` and `‖H‖ ≤ κ`, then
`|∫ φ(|x − y|/τ) ⟨x − y, H x⟩ dμ| ≤ A κ τ ∫ φ(|x − y|/τ) dμ`.  Where `φ(|x − y|/τ) ≠ 0`,
`|x − y| < Aτ`, so Cauchy–Schwarz bounds the integrand by the integrable `Aκτ φ(|x − y|/τ)`. -/
theorem Submission.doragm_sab_curvature_term_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (H : Euclid P → Euclid P) (φ : ℝ → ℝ) (κ A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u) → (∀ u, A ≤ u → φ u = 0) → (∀ x, ‖H x‖ ≤ κ) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → |∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂μ| ≤ A * κ * τ * ∫ x, φ (‖x - y‖ / τ) ∂μ := by
  intro P μ y H φ κ A τ hτ hφ hφA hH hint
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hH 0)
  rw [← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hint.const_mul (A * κ * τ)) (ae_of_all μ fun x => ?_)
  rw [norm_mul, Real.norm_of_nonneg (hφ _)]
  by_cases h0 : φ (‖x - y‖ / τ) = 0
  · simp [h0]
  have hr : ‖x - y‖ ≤ A * τ :=
    ((div_lt_iff₀ hτ).mp (lt_of_not_ge fun hA => h0 (hφA _ hA))).le
  calc φ (‖x - y‖ / τ) * ‖inner ℝ (x - y) (H x)‖
      ≤ φ (‖x - y‖ / τ) * (‖x - y‖ * κ) :=
        mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hH x) (norm_nonneg _))) (hφ _)
    _ ≤ φ (‖x - y‖ / τ) * (A * τ * κ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hr hκ) (hφ _)
    _ = A * κ * τ * φ (‖x - y‖ / τ) := by ring
/-- **Simon Ch. 4, 3.5 (p. 90)**, comparison of the scale-derivative weights.  With
`r = |x − y|`, `d = −(r/τ²)·φ'(r/τ) ≥ 0` and `q = N/max(s, r)ⁿ`: where `φ'(r/τ) ≠ 0` we have
`τ < r < Aτ`, so `max(s, r) = r` and `r⁻ⁿ ≤ τ⁻ⁿ ≤ Aⁿr⁻ⁿ`; multiplying by `d·N ≥ 0` and
integrating gives `0 ≤ ∫ d·N dμ` and `∫ d·q dμ ≤ (∫ d·N dμ)/τⁿ ≤ Aⁿ ∫ d·q dμ`. -/
theorem Submission.doragm_sab_deriv_weight_squeeze : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (N : Euclid P → ℝ) (A s τ : ℝ), 1 < A → 0 < s → s ≤ τ → (∀ u, deriv φ u ≤ 0) → (∀ u, deriv φ u ≠ 0 → 1 < u ∧ u < A) → (∀ x, 0 ≤ N x) → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) μ → Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) μ → 0 ≤ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ ∧ ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ ≤ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ∧ (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂μ) / τ ^ n ≤ A ^ n * ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂μ := by
  intro P n μ y φ N A s τ hA hs hsτ hφ' hsupp hN hq hD
  have hτ : 0 < τ := hs.trans_le hsτ
  -- `d·N ≥ 0`: `r/τ² ≥ 0` and `φ' ≤ 0` give `d ≥ 0`, and `N ≥ 0`
  have hDnn : ∀ x, 0 ≤ -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x := fun x =>
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.2 (by positivity)) (hφ' _)) (hN x)
  -- pointwise, `d·q ≤ d·N/τⁿ ≤ Aⁿ·d·q`
  have hpt : ∀ x,
      -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ≤
          -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ∧
        -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x / τ ^ n ≤
          A ^ n * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) := by
    intro x
    by_cases h0 : deriv φ (‖x - y‖ / τ) = 0
    · -- `d(x) = 0`, so all three terms vanish
      simp [h0]
    · -- `1 < r/τ < A`, so `τ < r < Aτ` and `max(s, r) = r`
      obtain ⟨h1, h2⟩ := hsupp _ h0
      have hr1 : τ < ‖x - y‖ := (one_lt_div₀ hτ).1 h1
      have hr2 : ‖x - y‖ < A * τ := (div_lt_iff₀ hτ).1 h2
      have hr : 0 < ‖x - y‖ := hτ.trans hr1
      have hrA : ‖x - y‖ ^ n ≤ A ^ n * τ ^ n :=
        (pow_le_pow_left₀ hr.le hr2.le n).trans_eq (mul_pow A τ n)
      rw [max_eq_right (hsτ.trans hr1.le), ← mul_div_assoc]
      have hDx := hDnn x
      generalize -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x = D at hDx ⊢
      refine ⟨div_le_div_of_nonneg_left hDx (pow_pos hτ n) (pow_le_pow_left₀ hτ.le hr1.le n), ?_⟩
      -- `D/τⁿ ≤ Aⁿ·D/rⁿ ⟺ D·rⁿ ≤ Aⁿ·D·τⁿ`, from `rⁿ ≤ (Aτ)ⁿ` and `D ≥ 0`
      rw [mul_div_assoc', div_le_div_iff₀ (pow_pos hτ n) (pow_pos hr n)]
      calc D * ‖x - y‖ ^ n ≤ D * (A ^ n * τ ^ n) := mul_le_mul_of_nonneg_left hrA hDx
        _ = A ^ n * D * τ ^ n := by ring
  refine ⟨integral_nonneg hDnn, ?_, ?_⟩
  · -- `∫ d·q ≤ ∫ d·N/τⁿ = (∫ d·N)/τⁿ`
    rw [← integral_div]
    exact integral_mono hq (hD.div_const _) fun x => (hpt x).1
  · -- `(∫ d·N)/τⁿ = ∫ d·N/τⁿ ≤ ∫ Aⁿ·d·q = Aⁿ ∫ d·q`
    rw [← integral_div, ← integral_const_mul]
    exact integral_mono (hD.div_const _) (hq.const_mul _) fun x => (hpt x).2
/-- **Simon Ch. 4, (3.5)–(3.6) (p. 90)**, the passage from the smoothed to the sharp masses: if
`0 ≤ φ ≤ 1`, `φ ≡ 1` on `(-∞, 1]` and `φ ≡ 0` on `[A, ∞)`, then pointwise
`1_{B̄_τ(y)} ≤ φ(|x − y|/τ) ≤ 1_{B̄_{Aτ}(y)}`, so `μ(B̄_τ(y)) ≤ ∫ φ(|x − y|/τ) dμ ≤ μ(B̄_{Aτ}(y))`
in `[0, ∞]` (`ofReal ∫ f = ∫⁻ ofReal f` for integrable `f ≥ 0`; no finiteness of `μ` is needed). -/
theorem Submission.doragm_sab_cutoff_mass_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), 0 < τ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → Integrable (fun x => φ (‖x - y‖ / τ)) μ → μ (closedBall y τ) ≤ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ∧ ENNReal.ofReal (∫ x, φ (‖x - y‖ / τ) ∂μ) ≤ μ (closedBall y (A * τ)) := by
  intro P μ y φ A τ hτ hbd h1 h0 hint
  -- `ofReal ∫ f dμ = ∫⁻ ofReal f dμ` for the integrable `f(x) = φ(|x − y|/τ) ≥ 0`, and
  -- `μ(B̄_ρ(y)) = ∫⁻ 1_{B̄_ρ(y)} dμ` since closed balls are measurable
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => (hbd _).1),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y τ)),
    ← lintegral_indicator_one (measurableSet_closedBall : MeasurableSet (closedBall y (A * τ)))]
  refine ⟨lintegral_mono fun x => ?_, lintegral_mono fun x => ?_⟩
  · -- on `B̄_τ(y)`, `|x − y|/τ ≤ 1`, so `φ(|x − y|/τ) = 1`
    by_cases hx : x ∈ closedBall y τ
    · rw [indicator_of_mem hx, Pi.one_apply,
        h1 _ ((div_le_one hτ).2 (mem_closedBall_iff_norm.1 hx)), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hx]
      exact zero_le
  · -- `φ ≤ 1` everywhere, and off `B̄_{Aτ}(y)`, `|x − y|/τ > A`, so `φ(|x − y|/τ) = 0`
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (hbd _).2
    · rw [mem_closedBall_iff_norm, not_le] at hx
      rw [h0 _ ((le_div_iff₀ hτ).2 hx.le), ENNReal.ofReal_zero]
      exact zero_le
/-- The cutoff increment `Δ = ∫ φ(r/t) q dμ - ∫ φ(r/s) q dμ`, `r = ‖x - y‖`, lies between two
annular integrals of `F` (Simon Ch. 4, 3.5): `Δ ≥ 0` and, in `[0, ∞]`,
`∫⁻_{B̄_t(y) \ B̄_{As}(y)} F ≤ Δ ≤ ∫⁻_{B̄_{At}(y) \ B̄_s(y)} F`.  The point is that
`g = (φ(r/t) - φ(r/s)) q` is `≥ 0`, equals `q = F` on the first annulus and vanishes off the
second. -/
theorem Submission.doragm_sab_annulus_increment_sandwich : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q F : Euclid P → ℝ) (A s t : ℝ), 1 < A → 0 < s → s ≤ t → Antitone φ → (∀ u, 0 ≤ φ u ∧ φ u ≤ 1) → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → (∀ x, 0 ≤ q x) → (∀ x, s < ‖x - y‖ → F x = q x) → Integrable (fun x => φ (‖x - y‖ / s) * q x) μ → Integrable (fun x => φ (‖x - y‖ / t) * q x) μ → 0 ≤ (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ ∧ (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ) ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ∧ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ) ≤ ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (F x) ∂μ := by
  intro P μ y φ q F A s t hA hs hst hφ hφ01 hφ1 hφ0 hq hFq hint_s hint_t
  have ht : 0 < t := hs.trans_le hst
  -- Step 1: `Δ = ∫ g dμ` for the integrable `g = φ(r/t) q - φ(r/s) q`
  set g : Euclid P → ℝ := fun x => φ (‖x - y‖ / t) * q x - φ (‖x - y‖ / s) * q x with hg_def
  have hΔ : (∫ x, φ (‖x - y‖ / t) * q x ∂μ) - ∫ x, φ (‖x - y‖ / s) * q x ∂μ = ∫ x, g x ∂μ :=
    (integral_sub hint_t hint_s).symm
  -- Step 2: `g ≥ 0`, as `r/t ≤ r/s` and `φ` is antitone; so `ofReal Δ = ∫⁻ ofReal g`
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x =>
    sub_nonneg.2 (mul_le_mul_of_nonneg_right
      (hφ (div_le_div_of_nonneg_left (norm_nonneg _) hs hst)) (hq x))
  have hg_int : Integrable g μ := hint_t.sub hint_s
  rw [hΔ, ofReal_integral_eq_lintegral_ofReal hg_int (Eventually.of_forall hg_nonneg)]
  refine ⟨integral_nonneg hg_nonneg, ?_, ?_⟩
  · -- Step 3: on `B̄_t(y) \ B̄_{As}(y)`, `φ(r/t) = 1`, `φ(r/s) = 0` and `r > As > s`, so `g = q = F`
    calc (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (F x) ∂μ)
        = ∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (g x) ∂μ := by
          refine setLIntegral_congr_fun (measurableSet_closedBall.diff measurableSet_closedBall)
            fun x hx => ?_
          simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le] at hx
          have h1 : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 hx.1)
          have h0 : φ (‖x - y‖ / s) = 0 := hφ0 _ ((le_div_iff₀ hs).2 hx.2.le)
          simp only [hg_def, h1, h0, hFq x ((lt_mul_of_one_lt_left hs hA).trans hx.2), one_mul,
            zero_mul, sub_zero]
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := setLIntegral_le_lintegral _ _
  · -- Step 4: `ofReal g ≤ 1_{B̄_{At}(y) \ B̄_s(y)} ofReal F` pointwise
    rw [← lintegral_indicator (measurableSet_closedBall.diff measurableSet_closedBall)]
    refine lintegral_mono fun x => ?_
    rcases le_or_gt ‖x - y‖ s with hrs | hsr
    · -- `r ≤ s ≤ t`: `φ(r/t) = φ(r/s) = 1`, so `g = 0`
      have h1t : φ (‖x - y‖ / t) = 1 := hφ1 _ ((div_le_one ht).2 (hrs.trans hst))
      have h1s : φ (‖x - y‖ / s) = 1 := hφ1 _ ((div_le_one hs).2 hrs)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h1t, h1s, sub_self, le_refl]
    rcases le_or_gt ‖x - y‖ (A * t) with hrAt | hAtr
    · -- `s < r ≤ At`: `x` lies in the annulus, where `g ≤ φ(r/t) q ≤ q = F`
      have hx : x ∈ closedBall y (A * t) \ closedBall y s := by
        simp only [Set.mem_sdiff, mem_closedBall, dist_eq_norm, not_le]
        exact ⟨hrAt, hsr⟩
      rw [indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht1 := mul_le_mul_of_nonneg_right (hφ01 (‖x - y‖ / t)).2 (hq x)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      simp only [hg_def, hFq x hsr]
      linarith
    · -- `r > At`: `φ(r/t) = 0`, so `g = -φ(r/s) q ≤ 0`
      have h0t : φ (‖x - y‖ / t) = 0 := hφ0 _ ((le_div_iff₀ ht).2 hAtr.le)
      have hs0 := mul_nonneg (hφ01 (‖x - y‖ / s)).1 (hq x)
      refine (ENNReal.ofReal_of_nonpos ?_).trans_le zero_le
      simp only [hg_def, h0t, zero_mul]
      linarith
/-- **Simon Ch. 4, 3.4 and 3.16** (differentiating `ρ ↦ ∫ φ(r/ρ) dμ` under the integral sign):
for a `C¹` cutoff `φ` vanishing on `[A, ∞)` and a bounded weight `q`, with `0 < τ`, `Aτ < R₀`
and `ν(B̄_{R₀}(y)) < ∞`, the integrands `φ(|x - y|/τ) q` and `-(|x - y|/τ²) φ'(|x - y|/τ) q` are
`ν`-integrable and `σ ↦ ∫ φ(|x - y|/σ) q dν` has derivative `∫ -(|x - y|/τ²) φ'(|x - y|/τ) q dν`
at `τ`.  For `σ ∈ (τ/2, R₀/A)` both integrands vanish off `B̄_{R₀}(y)` and are bounded on it
uniformly in `σ`, so dominated differentiation applies. -/
theorem Submission.doragm_radial_cutoff_hasDerivAt : ∀ (P : ℕ) (ν : Measure (Euclid P)) (y : Euclid P) (φ : ℝ → ℝ) (q : Euclid P → ℝ) (A B τ R₀ : ℝ), ContDiff ℝ 1 φ → (∀ u, A ≤ u → φ u = 0) → 0 < A → 0 < τ → A * τ < R₀ → ν (closedBall y R₀) ≠ ∞ → AEStronglyMeasurable q ν → (∀ x, ‖q x‖ ≤ B) → Integrable (fun x => φ (‖x - y‖ / τ) * q x) ν ∧ Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x) ν ∧ HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * q x ∂ν) (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * q x ∂ν) τ := by
  intro P ν y φ q A B τ R₀ hφ hφA hA hτ hAτ hν hq hqB
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  -- `φ' = 0` on `(A, ∞)`, where `φ` vanishes identically
  have hφ'A : ∀ u, A < u → deriv φ u = 0 := fun u hu => by
    have h : φ =ᶠ[𝓝 u] fun _ => (0 : ℝ) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun v hv => hφA v (le_of_lt hv)
    rw [h.deriv_eq, deriv_const]
  have hR₀ : 0 < R₀ := (mul_pos hA hτ).trans hAτ
  -- bounds `C₀`, `C₁` for `|φ|`, `|φ'|` on `[0, 2R₀/τ]`
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc 0 (2 * R₀ / τ)) hφ'c.continuousOn
  have h0K : (0 : ℝ) ∈ Icc 0 (2 * R₀ / τ) := ⟨le_rfl, by positivity⟩
  have hC₀0 : 0 ≤ C₀ := (norm_nonneg _).trans (hC₀ 0 h0K)
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 h0K)
  -- the neighbourhood `(τ/2, R₀/A)` of `τ`
  have hτs : τ ∈ Ioo (τ / 2) (R₀ / A) := ⟨by linarith, by rw [lt_div_iff₀ hA]; linarith⟩
  have hs : Ioo (τ / 2) (R₀ / A) ∈ 𝓝 τ := Ioo_mem_nhds hτs.1 hτs.2
  -- for `σ ∈ (τ/2, R₀/A)`: off `B̄_{R₀}(y)`, `|x - y|/σ > A`; on it, `|x - y|/σ ∈ [0, 2R₀/τ]`
  have hout : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∉ closedBall y R₀, A < ‖x - y‖ / σ := by
    rintro σ ⟨hσ1, hσ2⟩ x hx
    rw [mem_closedBall_iff_norm, not_le] at hx
    rw [lt_div_iff₀ hA] at hσ2
    have hσ : 0 < σ := by linarith
    rw [lt_div_iff₀ hσ]
    linarith
  have hin : ∀ σ ∈ Ioo (τ / 2) (R₀ / A), ∀ x ∈ closedBall y R₀,
      ‖x - y‖ / σ ∈ Icc 0 (2 * R₀ / τ) := by
    rintro σ ⟨hσ1, -⟩ x hx
    rw [mem_closedBall_iff_norm] at hx
    have hσ : 0 < σ := by linarith
    refine ⟨by positivity, ?_⟩
    rw [div_le_div_iff₀ hσ hτ]
    nlinarith [norm_nonneg (x - y)]
  -- the integrands `F σ`, their `σ`-derivatives `F' σ`, and their measurability
  set F : ℝ → Euclid P → ℝ := fun σ x => φ (‖x - y‖ / σ) * q x with hF
  set F' : ℝ → Euclid P → ℝ := fun σ x => -(‖x - y‖ / σ ^ 2) * deriv φ (‖x - y‖ / σ) * q x
    with hF'
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hF_meas : ∀ σ, AEStronglyMeasurable (F σ) ν := fun σ =>
    (hφ.continuous.comp (hr.div_const σ)).aestronglyMeasurable.mul hq
  have hF'_meas : ∀ σ, AEStronglyMeasurable (F' σ) ν := fun σ =>
    ((hr.div_const _).neg.mul (hφ'c.comp (hr.div_const σ))).aestronglyMeasurable.mul hq
  -- constant multiples of `1_{B̄_{R₀}(y)}` are integrable, as `ν(B̄_{R₀}(y)) < ∞`
  have hind : ∀ c : ℝ, Integrable ((closedBall y R₀).indicator fun _ => c) ν := fun c =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hν)
  -- (a): `|F τ| ≤ C₀ B 1_{B̄_{R₀}(y)}`
  have hF_int : Integrable (F τ) ν := by
    refine (hind (C₀ * B)).mono' (hF_meas τ) (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF]
      simp only
      rw [norm_mul]
      exact mul_le_mul (hC₀ _ (hin τ hτs x hx)) (hqB x) (norm_nonneg _) hC₀0
    · rw [Set.indicator_of_notMem hx, hF]
      simp only
      rw [hφA _ (hout τ hτs x hx).le, zero_mul, norm_zero]
  -- domination: `|F' σ| ≤ (R₀/(τ/2)²) C₁ B 1_{B̄_{R₀}(y)}` for `σ ∈ (τ/2, R₀/A)`
  have h_bound : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A),
      ‖F' σ x‖ ≤ (closedBall y R₀).indicator (fun _ => R₀ / (τ / 2) ^ 2 * C₁ * B) x := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : 0 < σ := by linarith [hσs.1]
    by_cases hx : x ∈ closedBall y R₀
    · rw [Set.indicator_of_mem hx, hF']
      simp only
      rw [norm_mul, norm_mul, norm_neg, Real.norm_of_nonneg (by positivity)]
      have hrσ : ‖x - y‖ / σ ^ 2 ≤ R₀ / (τ / 2) ^ 2 :=
        calc ‖x - y‖ / σ ^ 2 ≤ R₀ / σ ^ 2 := by gcongr; exact mem_closedBall_iff_norm.1 hx
          _ ≤ R₀ / (τ / 2) ^ 2 := by gcongr; exact hσs.1.le
      exact mul_le_mul (mul_le_mul hrσ (hC₁ _ (hin σ hσs x hx)) (norm_nonneg _) (by positivity))
        (hqB x) (norm_nonneg _) (mul_nonneg (by positivity) hC₁0)
    · rw [Set.indicator_of_notMem hx, hF']
      simp only
      rw [hφ'A _ (hout σ hσs x hx), mul_zero, zero_mul, norm_zero]
  -- `∂_σ φ(|x - y|/σ) = -(|x - y|/σ²) φ'(|x - y|/σ)`
  have h_diff : ∀ᵐ x ∂ν, ∀ σ ∈ Ioo (τ / 2) (R₀ / A), HasDerivAt (F · x) (F' σ x) σ := by
    refine ae_of_all _ fun x σ hσs => ?_
    have hσ : σ ≠ 0 := by linarith [hσs.1]
    have h1 : HasDerivAt (fun σ => ‖x - y‖ / σ) (-(‖x - y‖ / σ ^ 2)) σ := by
      convert (hasDerivAt_inv hσ).const_mul ‖x - y‖ using 1
      · funext σ
        rw [div_eq_mul_inv]
      · ring
    have h2 : HasDerivAt (fun σ => φ (‖x - y‖ / σ))
        (deriv φ (‖x - y‖ / σ) * -(‖x - y‖ / σ ^ 2)) σ :=
      (hφd _).hasDerivAt.comp σ h1
    convert h2.mul_const (q x) using 1
    rw [hF']
    ring
  -- (b), (c): dominated differentiation under the integral sign
  obtain ⟨hF'_int, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall hF_meas) hF_int (hF'_meas τ) h_bound (hind _) h_diff
  exact ⟨hF_int, hF'_int, hderiv⟩
/-- The radial test field `X(x) = φ(|x − y|/τ)(x − y)` (Simon Ch. 4, 3.2–3.3, cutoff
`γ(r) = φ(r/τ)`) is `C¹` with compact support in `B̄_{Aτ}(y)`: it equals `x − y` on `B_τ(y)`, and
away from `y` the norm `|x − y|` is smooth. -/
theorem Submission.doragm_rfv_radial_field_c1 : ∀ (P : ℕ) (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → ContDiff ℝ 1 (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ HasCompactSupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ∧ tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
  intro P y φ A τ hφ hφ1 hφA hτ
  -- (iii) off `B̄_{Aτ}(y)` we have `A ≤ ‖x - y‖ / τ`, so `φ (‖x - y‖ / τ) = 0`
  have hsupp : tsupport (fun x : Euclid P => φ (‖x - y‖ / τ) • (x - y)) ⊆ closedBall y (A * τ) := by
    refine closure_minimal (support_subset_iff'.2 fun x hx => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    have hA : A ≤ ‖x - y‖ / τ := (le_div_iff₀ hτ).2 hx.le
    simp [hφA _ hA]
  -- (ii) a closed subset of the compact ball `B̄_{Aτ}(y)` is compact
  refine ⟨?_, (isCompact_closedBall y (A * τ)).of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp⟩
  -- (i) `C¹` at every point
  rw [contDiff_iff_contDiffAt]
  intro x
  have hsub : ContDiffAt ℝ 1 (fun z : Euclid P => z - y) x := contDiffAt_id.sub contDiffAt_const
  by_cases hxy : x = y
  · -- near `y` we have `‖z - y‖ / τ < 1`, so the field is `z ↦ z - y`
    subst hxy
    refine hsub.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds x hτ] with z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z - x‖ / τ ≤ 1 := (div_le_one hτ).2 hz.le
    simp [hφ1 _ h1]
  · -- away from `y` the norm `z ↦ ‖z - y‖` is smooth, since `x - y ≠ 0`
    have hnorm : ContDiffAt ℝ 1 (fun z : Euclid P => ‖z - y‖) x := hsub.norm ℝ (sub_ne_zero.2 hxy)
    exact (hφ.comp_contDiffAt x (hnorm.div_const τ)).smul hsub
/-- **Trace of the derivative of a radial field** (Simon Ch. 4, 3.2 and the identity after it,
with a subspace `Q` in place of `TₓM`; chapter-04.txt lines 225–262).  Let `φ` be `C¹` with
`φ = 1` on `(-∞, 1]`, `τ > 0`, `X(z) = φ(|z − y|/τ)(z − y)`, `p = Q.starProjection`, `v = x − y`
and `r = |v|`.  Then `trace(p ∘ DX(x)) = dim Q · φ(r/τ) + (r/τ) φ'(r/τ) (1 − |v − p v|²/r²)`.
`p` is a projection onto `Q`, so `trace p = dim Q` (`LinearMap.IsProj.trace`).  At `x = y` the
field is `z ↦ z − y` on `B_τ(y)`, so `DX(y) = I` and both sides equal `dim Q`.  For `x ≠ y`,
`DX(x) = φ(r/τ) I + φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, ·⟩ v` (`|z − y| = √(|z − y|²)`, chain and product
rules), the rank-one part has trace `φ'(r/τ) τ⁻¹ r⁻¹ ⟨v, p v⟩` (`LinearMap.trace_smulRight`), and
`⟨v, p v⟩ = r² − |v − p v|²` since `v − p v ⊥ p v`. -/
theorem Submission.doragm_rfv_trace_radial_field : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (y x : Euclid P) (φ : ℝ → ℝ) (τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → 0 < τ → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x).toLinearMap) = (Module.finrank ℝ Q : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) := by
  intro P Q y x φ τ hφ hφ1 hτ
  -- `p = Q.starProjection` is a projection onto `Q`, so its trace is `dim Q`.
  have htr : LinearMap.trace ℝ (Euclid P) Q.starProjection.toLinearMap = Module.finrank ℝ Q :=
    LinearMap.IsProj.trace ⟨fun w => Q.starProjection_apply_mem w,
      fun w hw => Submodule.starProjection_eq_self_iff.mpr hw⟩
  by_cases hxy : x = y
  · -- On `B(y, τ)` the field is `z ↦ z - y`, whose derivative is the identity.
    subst hxy
    have hev : (fun z : Euclid P => φ (‖z - x‖ / τ) • (z - x)) =ᶠ[𝓝 x] fun z => z - x := by
      filter_upwards [Metric.ball_mem_nhds x hτ] with z hz
      rw [hφ1 _ ((div_le_one hτ).mpr (mem_ball_iff_norm.mp hz).le), one_smul]
    rw [hev.fderiv_eq, fderiv_sub_const, fderiv_fun_id]
    simp [htr, hφ1 0 zero_le_one]
  · -- Derivative of `z ↦ ‖z - y‖` at `x ≠ y`, via `√(‖z - y‖²)`.
    have hr0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hsub : HasFDerivAt (fun z : Euclid P => z - y) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const y
    have hnorm := hsub.norm_sq.sqrt (pow_ne_zero 2 hr0.ne')
    have hsqrt : (fun z : Euclid P => √(‖z - y‖ ^ 2)) = fun z => ‖z - y‖ :=
      funext fun z => Real.sqrt_sq (norm_nonneg _)
    rw [hsqrt] at hnorm
    -- Chain rule for `c(z) = φ(‖z - y‖ / τ)`, then the product rule for `c(z) • (z - y)`.
    have hφd : HasDerivAt (fun t => φ (t / τ)) (deriv φ (‖x - y‖ / τ) * (1 / τ)) ‖x - y‖ :=
      ((hφ.differentiable one_ne_zero) _).hasDerivAt.comp _
        (HasDerivAt.div_const (hasDerivAt_id' ‖x - y‖) τ)
    have hX := (hφd.comp_hasFDerivAt x hnorm).smul hsub
    rw [show (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) =
      ((fun t => φ (t / τ)) ∘ fun z => ‖z - y‖) • fun z => z - y from rfl, hX.fderiv]
    -- `p ∘ (a I + ℓ(·) v) = a p + ℓ(·) p v`; the rank-one part has trace `ℓ(p v)`.
    have key : ∀ (a : ℝ) (ℓ : Euclid P →L[ℝ] ℝ) (v : Euclid P),
        LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap) =
          a * Module.finrank ℝ Q + ℓ (Q.starProjection v) := by
      intro a ℓ v
      have hcomp : Q.starProjection.toLinearMap ∘ₗ
          (a • ContinuousLinearMap.id ℝ (Euclid P) + ℓ.smulRight v).toLinearMap =
          a • Q.starProjection.toLinearMap +
            (ℓ : Euclid P →ₗ[ℝ] ℝ).smulRight (Q.starProjection v) := by
        ext w
        simp
      rw [hcomp, map_add, map_smul, htr, LinearMap.trace_smulRight, smul_eq_mul,
        ContinuousLinearMap.coe_coe]
    -- Pythagoras: `⟨v, p v⟩ = ‖v‖² - ‖v - p v‖²`, as `v - p v ⊥ p v`.
    have hinner : inner ℝ (x - y) (Q.starProjection (x - y)) =
        ‖x - y‖ ^ 2 - ‖(x - y) - Q.starProjection (x - y)‖ ^ 2 := by
      have h0 := Submodule.starProjection_inner_eq_zero (K := Q) (x - y)
        (Q.starProjection (x - y)) (Q.starProjection_apply_mem _)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at h0
      rw [norm_sub_sq_real (x - y) (Q.starProjection (x - y))]
      linarith
    rw [key]
    simp only [Function.comp_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
      Real.sqrt_sq (norm_nonneg _), hinner]
    field_simp
    ring
/-- **Simon Ch. 4, 2.2 and 4.1.1**: for `R = (M, θ, ξ)` and `X ∈ C¹_c(U; ℝᴾ)` with `x ↦ p_{TₓM}`
`μ_R`-measurable, `div_M X` is `μ_R`-integrable and `δV(X) = ∫_M θ div_M X dHⁿ = ∫ div_M X dμ_R`,
`μ_R = θ Hⁿ⌞M`.  `div_M X(x) = tr(p_{TₓM} ∘ DX(x))` is bounded by `‖tr‖ ‖DX(x)‖`, and it vanishes
off the compact `spt X ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dsmc_firstVariation_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure ∧ R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
  intro P n U R X hX hcpt hU hp
  -- the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and `div_M X(x) = tr(p_x ∘ DX(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ x, tangentialDivergence n R.carrier X x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ X x) := fun x => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
      (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp.aestronglyMeasurable
      hD.aestronglyMeasurable
  -- `|div_M X(x)| ≤ ‖tr‖ C 1_K(x)`, `K = spt X`, `C = sup ‖DX‖`
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hcpt.fderiv ℝ)
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hbound : ∀ x, ‖tangentialDivergence n R.carrier X x‖ ≤
      (tsupport X).indicator (fun _ => ‖tr‖ * C) x := by
    intro x
    rw [hdiv]
    by_cases hxK : x ∈ tsupport X
    · rw [Set.indicator_of_mem hxK]
      refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _) zero_le_one
    · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
        ContinuousLinearMap.comp_zero, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport X) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport X) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.firstVariation]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]
/-- The approximate tangent planes `TₓM` of `R = τ(M, θ, ξ)` are `n`-dimensional for `μ_R`-a.e.
`x`: by `R.orients`, `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane (Simon Ch. 3, 1.4), which is
`n`-dimensional by definition, and `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`. -/
theorem Submission.dorag_aa_ae_finrank_approxTangentPlane : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
  intro P n U R
  -- `μ_R = θ Hⁿ⌞M ≪ Hⁿ⌞M`, and `Hⁿ⌞M`-a.e. `x` has an approximate tangent plane
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le R.orients] with x hx
  obtain ⟨Q, hQ, -⟩ := hx
  -- `TₓM` is then the chosen approximate tangent plane, whose dimension is `n`
  have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
  rw [approxTangentPlane, dite_eq_left h]
  exact h.choose_spec.finrank_eq
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1

/-- **Simon Ch. 4, 3.2–3.3 with generalized mean curvature (3.14)**: the radial first-variation
identity.  The radial field `X(x) = φ(r/τ)(x − y)`, `r = |x − y|`, is `C¹` with support in
`B̄_{Aτ}(y) ⊆ W`, so `∫ div_M X dμ = δV(X) = −∫ X · H dμ` (2.2, and 3.14 (★) in `W`), and
wherever `dim TₓM = n`, i.e. `μ`-a.e., `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)`, where
`|(Dr)^⊥|² = |(x − y) − p_{TₓM}(x − y)|²/r²` (3.2).  Both terms are `μ`-integrable: `φ(r/τ)` is
continuous and vanishes off `B̄_{Aτ}(y)`, which has finite `μ`-measure, and the second term is
`div_M X − n φ(r/τ)` `μ`-a.e. -/
theorem Submission.doragm_radial_first_variation : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (φ : ℝ → ℝ) (A τ : ℝ), ContDiff ℝ 1 φ → (∀ u, u ≤ 1 → φ u = 1) → (∀ u, A ≤ u → φ u = 0) → 0 < τ → closedBall y (A * τ) ⊆ W → (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure) + (∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure) = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
  intro P n U W R H _ hWU hp hH y φ A τ hφ h1 h0 hτ hball
  -- `X(x) = φ(r/τ)(x − y)` is `C¹`, with compact support in `B̄_{Aτ}(y) ⊆ W ⊆ U`
  obtain ⟨hXc, hXcpt, hXK⟩ := Submission.doragm_rfv_radial_field_c1 P y φ A τ hφ h1 h0 hτ
  have hXW := hXK.trans hball
  -- `δV(X) = −∫ X · H dμ` by hypothesis, and `δV(X) = ∫ div_M X dμ` with `div_M X ∈ L¹(μ)`
  have hmc := hH _ hXc hXcpt hXW
  obtain ⟨hint, hfv⟩ := Submission.dsmc_firstVariation_eq_integral P n U R _ hXc hXcpt
    (hXW.trans hWU) hp.aemeasurable
  -- `div_M X = n φ(r/τ) + (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²)` wherever `dim TₓM = n`, i.e. `μ`-a.e.
  have hdiv : (fun x => tangentialDivergence n R.carrier
      (fun z : Euclid P => φ (‖z - y‖ / τ) • (z - y)) x) =ᵐ[R.measure] fun x =>
      (n : ℝ) * φ (‖x - y‖ / τ) + ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
        (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ 2) := by
    filter_upwards [Submission.dorag_aa_ae_finrank_approxTangentPlane P n U R] with x hx
    have htr := Submission.doragm_rfv_trace_radial_field P (approxTangentPlane n R.carrier x) y x
      φ τ hφ h1 hτ
    rw [hx] at htr
    exact htr
  -- `φ(r/τ)` is continuous and vanishes off the compact `K = B̄_{Aτ}(y)`, and `μ(K) < ∞`
  have hK : IsCompact (closedBall y (A * τ)) := isCompact_closedBall y (A * τ)
  have hKfin := (Submission.rsd_imrep_compact_measure_ne_top P n U R _ hK (hball.trans hWU)).2
  have hf₁c : Continuous fun x : Euclid P => φ (‖x - y‖ / τ) :=
    hφ.continuous.comp ((continuous_id.sub continuous_const).norm.div_const τ)
  have hf₁0 : ∀ x, x ∉ closedBall y (A * τ) → φ (‖x - y‖ / τ) = 0 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact h0 _ ((le_div_iff₀ hτ).2 hx.le)
  obtain ⟨C, hC⟩ := hf₁c.bounded_above_of_compact_support (HasCompactSupport.intro hK hf₁0)
  have hf₁ : Integrable (fun x : Euclid P => φ (‖x - y‖ / τ)) R.measure := by
    refine ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const (C := C) hKfin)).mono'
      hf₁c.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall y (A * τ)
    · rw [indicator_of_mem hx]
      exact hC x
    · rw [indicator_of_notMem hx, hf₁0 x hx, norm_zero]
  -- the second term is `div_M X − n φ(r/τ)` `μ`-a.e., hence integrable as well
  have hf₂ : Integrable (fun x => ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) *
      (1 - ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ 2)) R.measure := by
    refine (hint.sub (hf₁.const_mul (n : ℝ))).congr ?_
    filter_upwards [hdiv] with x hx
    simp only [Pi.sub_apply, hx, add_sub_cancel_left]
  -- `n ∫ φ(r/τ) dμ + ∫ (r/τ) φ'(r/τ)(1 − |(Dr)^⊥|²) dμ = ∫ div_M X dμ = δV(X) = −∫ X · H dμ`
  rw [← integral_const_mul, ← integral_add (hf₁.const_mul _) hf₂, ← integral_congr_ae hdiv,
    ← hfv, hmc]
  congr 1
  exact integral_congr_ae (ae_of_all _ fun x => real_inner_smul_left _ _ _)

/-- **Simon Ch. 4, 3.4–3.5 and 3.16** (smoothed annular monotonicity bounds, `|H| ≤ κ`): if
`A > 1`, `0 < s < t` and `B̄_{At}(y) ⊆ W`, then with `c = Aκ` and
`F_y = |(x − y) − p_x(x − y)|²/|x − y|^{n+2}`,
`∫_{B̄_t∖B̄_{As}} F_y dμ + e^{cs}s⁻ⁿμ(B̄_s) ≤ e^{ct}t⁻ⁿμ(B̄_{At})` and
`e^{−ct}t⁻ⁿμ(B̄_t) ≤ e^{−cs}s⁻ⁿμ(B̄_{As}) + Aⁿ∫_{B̄_{At}∖B̄_s} F_y dμ` in `[0, ∞]`.  For the profile
`φ`, `N = |(x − y) − p_x(x − y)|²/|x − y|²` and `q = N/max(s, |x − y|)ⁿ`, the scale functions
`I(τ) = ∫ φ(r/τ) dμ` and `G(τ) = ∫ φ(r/τ) q dμ` satisfy `n I − τ I' + τ J' = −h` (radial first
variation), `|h| ≤ Aκτ I` and `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'` on `[s, t]`; the integrating-factor comparison
bounds `G(t) − G(s)`, which lies between the two annular integrals, while `I(τ)` lies between
`μ(B̄_τ)` and `μ(B̄_{Aτ})`. -/
theorem Submission.doragm_smoothed_annular_bounds : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (A s t : ℝ), 1 < A → 0 < s → s < t → closedBall y (A * t) ⊆ W → (∫⁻ x in closedBall y t \ closedBall y (A * s), ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) * R.measure (closedBall y (A * t)) ∧ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) * R.measure (closedBall y (A * s)) + ENNReal.ofReal (A ^ n) * ∫⁻ x in closedBall y (A * t) \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp _ hκ hFV y A s t hA hs hst hball
  -- Step 1: `A > 0`, `t > 0`, and `c = Aκ ≥ 0` because `κ ≥ ‖H 0‖ ≥ 0`
  have hA0 : 0 < A := zero_lt_one.trans hA
  have ht : 0 < t := hs.trans hst
  have hc : 0 ≤ A * κ := mul_nonneg hA0.le ((norm_nonneg _).trans (hκ 0))
  -- a radius `R₀ = δ + At > At` with `B̄_{R₀}(y) ⊆ W`; this compact subset of `U` has finite mass
  obtain ⟨δ, hδ, hδW⟩ := (isCompact_closedBall y (A * t)).exists_cthickening_subset_open hW hball
  rw [cthickening_closedBall hδ.le (mul_pos hA0 ht).le] at hδW
  have hAτR₀ : ∀ τ ∈ Icc s t, A * τ < δ + A * t := fun τ hτ =>
    (mul_le_mul_of_nonneg_left hτ.2 hA0.le).trans_lt (lt_add_of_pos_left _ hδ)
  have hμR₀ : R.measure (closedBall y (δ + A * t)) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall _ _) (hδW.trans hWU)
  -- Step 2: the cutoff profile `φ`
  obtain ⟨φ, hφC, hφanti, hφbd, hφ1, hφ0, hφ'le, hφ'ne⟩ :=
    Submission.doragm_sab_cutoff_profile A hA
  -- Step 3: `N = |(x - y) - p_x(x - y)|²/|x - y|² ∈ [0, 1]` and `q = N/max(s, |x - y|)ⁿ ∈ [0, s⁻ⁿ]`
  obtain ⟨N, hN⟩ : ∃ N : Euclid P → ℝ, ∀ x, N x =
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2 :=
    ⟨_, fun _ => rfl⟩
  have hN01 : ∀ x, 0 ≤ N x ∧ N x ≤ 1 := by
    intro x
    rw [hN]
    refine ⟨by positivity,
      div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (by positivity)⟩
    -- `v - p_x v` is the projection of `v` onto `(TₓM)^⊥`
    rw [← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_starProjection_apply_le _ _
  have hr : Continuous fun x : Euclid P => ‖x - y‖ := (continuous_id.sub continuous_const).norm
  have hNm : AEStronglyMeasurable N R.measure := by
    have hpx : AEStronglyMeasurable
        (fun x => (approxTangentPlane n R.carrier x).starProjection (x - y)) R.measure :=
      (ContinuousLinearMap.id ℝ (Euclid P →L[ℝ] Euclid P)).aestronglyMeasurable_comp₂ hp
        (continuous_id.sub continuous_const).aestronglyMeasurable
    rw [show N = _ from funext hN]
    exact ((((continuous_id.sub continuous_const).aestronglyMeasurable.sub hpx).norm.aemeasurable
      |>.pow_const 2).div (hr.pow 2).measurable.aemeasurable).aestronglyMeasurable
  have hqm : AEStronglyMeasurable (fun x => N x / (max s ‖x - y‖) ^ n) R.measure :=
    (hNm.aemeasurable.div
      ((continuous_const.max hr).pow n).measurable.aemeasurable).aestronglyMeasurable
  have hq0 : ∀ x, 0 ≤ N x / (max s ‖x - y‖) ^ n := fun x =>
    div_nonneg (hN01 x).1 (pow_nonneg (hs.le.trans (le_max_left _ _)) n)
  have hqB : ∀ x, ‖N x / (max s ‖x - y‖) ^ n‖ ≤ 1 / s ^ n := by
    intro x
    rw [Real.norm_of_nonneg (hq0 x)]
    have hsn : 0 < s ^ n := pow_pos hs n
    have hDs : s ^ n ≤ (max s ‖x - y‖) ^ n := pow_le_pow_left₀ hs.le (le_max_left _ _) n
    calc N x / (max s ‖x - y‖) ^ n ≤ 1 / (max s ‖x - y‖) ^ n :=
          div_le_div_of_nonneg_right (hN01 x).2 (hsn.le.trans hDs)
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le hsn hDs
  -- `q = F_y` where `|x - y| > s`
  have hFq : ∀ x, s < ‖x - y‖ →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)
        = N x / (max s ‖x - y‖) ^ n := by
    intro x hx
    rw [max_eq_right hx.le, hN]
    ring
  -- Step 4: integrability and `τ`-derivatives of the cutoff integrals (weights `1`, `q`, `N`)
  have hcd1 : ∀ τ ∈ Icc s t, Integrable (fun x => φ (‖x - y‖ / τ)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure) τ := fun τ hτ => by
    simpa only [mul_one] using Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun _ => 1) A 1 τ (δ + A * t) hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀
      aestronglyMeasurable_const (fun _ => by simp)
  have hcdq : ∀ τ ∈ Icc s t,
      Integrable (fun x => φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) *
        (N x / (max s ‖x - y‖) ^ n)) R.measure ∧
      HasDerivAt (fun σ => ∫ x, φ (‖x - y‖ / σ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
        (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
          ∂R.measure) τ := fun τ hτ =>
    Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ
      (fun x => N x / (max s ‖x - y‖) ^ n) A (1 / s ^ n) τ (δ + A * t) hφC hφ0 hA0
      (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hqm hqB
  have hcdN : ∀ τ ∈ Icc s t,
      Integrable (fun x => -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x) R.measure :=
    fun τ hτ => (Submission.doragm_radial_cutoff_hasDerivAt P R.measure y φ N A 1 τ (δ + A * t)
      hφC hφ0 hA0 (hs.trans_le hτ.1) (hAτR₀ τ hτ) hμR₀ hNm
      (fun x => by rw [Real.norm_of_nonneg (hN01 x).1]; exact (hN01 x).2)).2.1
  -- Step 5: the identity `(E)`: `n I − τ I' + τ J' = −h` on `[s, t]`, from the radial first
  -- variation and `(r/τ) φ'(r/τ) (1 − N) = (−τ)(−(r/τ²) φ'(r/τ)) + τ (−(r/τ²) φ'(r/τ)) N`
  have hE : ∀ τ ∈ Icc s t, (n : ℝ) * (∫ x, φ (‖x - y‖ / τ) ∂R.measure)
      - τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
      + τ * (∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
      = -∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure := by
    intro τ hτ
    have hτ0 : 0 < τ := hs.trans_le hτ.1
    have hrv := Submission.doragm_radial_first_variation P n U W R H hW hWU hp hFV y φ A τ
      hφC hφ1 hφ0 hτ0
      ((closedBall_subset_closedBall (mul_le_mul_of_nonneg_left hτ.2 hA0.le)).trans hball)
    have hsplit : ∫ x, ‖x - y‖ / τ * deriv φ (‖x - y‖ / τ) * (1 - ‖(x - y) -
        (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ 2) ∂R.measure
        = ∫ x, (-τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ)) +
          τ * (-(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x)) ∂R.measure := by
      congr 1
      ext x
      rw [← hN x]
      generalize deriv φ (‖x - y‖ / τ) = d
      field_simp
      ring
    rw [hsplit, integral_add ((hcd1 τ hτ).2.1.const_mul _) ((hcdN τ hτ).const_mul _),
      integral_const_mul, integral_const_mul] at hrv
    linarith
  -- Steps 6–7: the curvature bound `|h| ≤ Aκτ I` and the comparison `G' ≤ τ⁻ⁿ J' ≤ Aⁿ G'`
  have hsq := fun τ (hτ : τ ∈ Icc s t) =>
    Submission.doragm_sab_deriv_weight_squeeze P n R.measure y φ N A s τ hA hs hτ.1 hφ'le hφ'ne
      (fun x => (hN01 x).1) (hcdq τ hτ).2.1 (hcdN τ hτ)
  -- Steps 8–9: the integrating-factor comparison on `[s, t]`
  obtain ⟨ha, hb⟩ := Submission.doragm_sab_exp_ratio_compare n (A * κ) (A ^ n) s t
    (fun τ => ∫ x, φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * (N x / (max s ‖x - y‖) ^ n)
      ∂R.measure)
    (fun τ => ∫ x, -(‖x - y‖ / τ ^ 2) * deriv φ (‖x - y‖ / τ) * N x ∂R.measure)
    (fun τ => ∫ x, φ (‖x - y‖ / τ) * inner ℝ (x - y) (H x) ∂R.measure)
    hc hs hst (fun τ hτ => (hcd1 τ hτ).2.2) (fun τ hτ => (hcdq τ hτ).2.2) hE
    (fun τ hτ => Submission.doragm_sab_curvature_term_le P R.measure y H φ κ A τ
      (hs.trans_le hτ.1) (fun u => (hφbd u).1) hφ0 hκ (hcd1 τ hτ).1)
    (fun τ hτ => (hsq τ hτ).1) (fun τ hτ => (hsq τ hτ).2.1) (fun τ hτ => (hsq τ hτ).2.2)
  -- Step 10: `μ(B̄_τ) ≤ I(τ) ≤ μ(B̄_{Aτ})` at `τ = s, t`, and the annular comparison
  have hsI : s ∈ Icc s t := left_mem_Icc.2 hst.le
  have htI : t ∈ Icc s t := right_mem_Icc.2 hst.le
  obtain ⟨hms, hmAs⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A s hs hφbd hφ1 hφ0 (hcd1 s hsI).1
  obtain ⟨hmt, hmAt⟩ :=
    Submission.doragm_sab_cutoff_mass_sandwich P R.measure y φ A t ht hφbd hφ1 hφ0 (hcd1 t htI).1
  obtain ⟨hΔ, hX, hY⟩ := Submission.doragm_sab_annulus_increment_sandwich P R.measure y φ
    (fun x => N x / (max s ‖x - y‖) ^ n)
    (fun x => ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) A s t hA hs hst.le hφanti hφbd hφ1 hφ0 hq0 hFq (hcdq s hsI).1
    (hcdq t htI).1
  beta_reduce at ha hb hΔ hX hY
  have hIs : 0 ≤ ∫ x, φ (‖x - y‖ / s) ∂R.measure := integral_nonneg fun x => (hφbd _).1
  -- Steps 11–12: combine in `[0, ∞]`
  refine ⟨?_, ?_⟩
  · calc _ ≤ ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          ENNReal.ofReal (Real.exp (A * κ * s) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) +
          Real.exp (A * κ * s) / s ^ n * ∫ x, φ (‖x - y‖ / s) ∂R.measure) := by
        rw [ENNReal.ofReal_add hΔ (mul_nonneg (by positivity) hIs),
          ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (A * κ * t) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  · calc _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n) *
          ENNReal.ofReal (∫ x, φ (‖x - y‖ / t) ∂R.measure) := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(A * κ * t)) / t ^ n * ∫ x, φ (‖x - y‖ / t) ∂R.measure) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n * (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          A ^ n * ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
            ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal (Real.exp (-(A * κ * s)) / s ^ n) *
            ENNReal.ofReal (∫ x, φ (‖x - y‖ / s) ∂R.measure) +
          ENNReal.ofReal (A ^ n) *
            ENNReal.ofReal ((∫ x, φ (‖x - y‖ / t) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) -
              ∫ x, φ (‖x - y‖ / s) * (N x / (max s ‖x - y‖) ^ n) ∂R.measure) := by
        rw [ENNReal.ofReal_add (mul_nonneg (by positivity) hIs) (mul_nonneg (by positivity) hΔ),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by gcongr

/-- **Annular monotonicity with bounded mean curvature** (Simon Ch. 4, 3.5 → 3.6 and 3.17,
"letting `ε ↓ 0`").  Let `μ = θ Hⁿ⌞M`, `|H| ≤ κ`,
`F_y(x) = |(x − y) − p_{TₓM}(x − y)|²/|x − y|^{n+2}` and `0 < s < t` with `B̄_t(y) ⊆ W`.  Then
(M1) `∫_{B̄_t∖B̄_s} F_y dμ + e^{κs} s⁻ⁿ μ(B̄_s) ≤ e^{κt} t⁻ⁿ μ(B̄_t)` and
(M2) `e^{−κt} t⁻ⁿ μ(B̄_t) ≤ e^{−κs} s⁻ⁿ μ(B̄_s) + ∫_{B̄_t∖B̄_s} F_y dμ`.

Choose `δ₀ > 0` with `B̄_{t+δ₀}(y) ⊆ W` and the widths `A_m = 1 + (δ₀/t)/(m + 1) ↓ 1`, and apply
the smoothed bounds `Submission.doragm_smoothed_annular_bounds` with `A = A_m`.  As `m → ∞`,
`μ(B̄_{A_mρ}) → μ(B̄_ρ)` by continuity from above (`μ(B̄_{t+δ₀}) < ∞`).  For `ν = F_y μ` the inner
annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`, and the outer annuli `B̄_{A_mt}∖B̄_s` decrease to
it with `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`, because `F_y(x) ≤ |x − y|⁻ⁿ`.  The coefficients
converge, and `e^{κs} ≤ e^{A_mκs}` as `κ ≥ 0`; passing to the limit gives (M1) and (M2). -/
theorem Submission.doragm_annular_monotonicity : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ (y : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure := by
  intro P n U W R H κ hW hWU hp hH hHκ hFV y s t hs hst hBt
  have hsm := Submission.doragm_smoothed_annular_bounds P n U W R H κ hW hWU hp hH hHκ hFV y
  have ht : 0 < t := hs.trans hst
  -- `κ ≥ 0`, since `‖H y‖ ≤ κ`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ y)
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Step 1: `B̄_{t+δ₀}(y) ⊆ W`, so `μ(B̄_ρ(y)) < ∞` for `ρ ≤ t + δ₀`
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hBt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hfinB : ∀ ρ, ρ ≤ δ₀ + t → R.measure (closedBall y ρ) ≠ ∞ := fun ρ hρ =>
    hfin _ (isCompact_closedBall y ρ) ((closedBall_subset_closedBall hρ).trans (hδ₀W.trans hWU))
  -- Step 2: the widths `A_m = 1 + (δ₀/t)/(m + 1)`: `A_m > 1`, `A_m ↓ 1` and `A_m t ≤ t + δ₀`
  obtain ⟨A, hA1, hAanti, hAlim, hAt⟩ : ∃ A : ℕ → ℝ, (∀ m, 1 < A m) ∧ Antitone A ∧
      Tendsto A atTop (𝓝 1) ∧ ∀ m, A m * t ≤ δ₀ + t := by
    have hc : 0 < δ₀ / t := div_pos hδ₀ ht
    have he : ∀ m : ℕ, 0 < 1 / ((m : ℝ) + 1) := fun m => by positivity
    have he1 : ∀ m : ℕ, 1 / ((m : ℝ) + 1) ≤ 1 := fun m =>
      (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    refine ⟨fun m => 1 + δ₀ / t * (1 / ((m : ℝ) + 1)), fun m => ?_, fun i j hij => ?_, ?_,
      fun m => ?_⟩
    · dsimp only
      linarith [mul_pos hc (he m)]
    · have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
      have := mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) + 1) hij') hc.le
      dsimp only
      linarith
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ₀ / t)).const_add 1
      rwa [mul_zero, add_zero] at h
    · have h2 : (1 + δ₀ / t * (1 / ((m : ℝ) + 1))) * t = t + δ₀ * (1 / ((m : ℝ) + 1)) := by
        field_simp
      dsimp only
      rw [h2]
      linarith [mul_le_mul_of_nonneg_left (he1 m) hδ₀.le]
  have hBA : ∀ m, closedBall y (A m * t) ⊆ W := fun m =>
    (closedBall_subset_closedBall (hAt m)).trans hδ₀W
  -- Step 3: for `0 < ρ ≤ t`, the balls `B̄_{A_mρ}` decrease to `B̄_ρ`, so
  -- `μ(B̄_{A_mρ}) → μ(B̄_ρ)` (continuity from above)
  have hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ t →
      Antitone (fun m => closedBall y (A m * ρ)) ∧
      (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ ∧
      Tendsto (fun m => R.measure (closedBall y (A m * ρ))) atTop
        (𝓝 (R.measure (closedBall y ρ))) := by
    intro ρ hρ hρt
    have hanti : Antitone (fun m => closedBall y (A m * ρ)) := fun i j hij =>
      closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (hAanti hij) hρ.le)
    have hinter : (⋂ m, closedBall y (A m * ρ)) = closedBall y ρ := by
      ext x
      simp only [mem_iInter, mem_closedBall]
      refine ⟨fun h => ?_, fun h m => h.trans (le_mul_of_one_le_left hρ.le (hA1 m).le)⟩
      have hlim : Tendsto (fun m => A m * ρ) atTop (𝓝 (1 * ρ)) := hAlim.mul_const ρ
      rw [one_mul] at hlim
      exact ge_of_tendsto' hlim h
    have hfin0 : R.measure (closedBall y (A 0 * ρ)) ≠ ∞ :=
      hfinB _ ((mul_le_mul_of_nonneg_left hρt (by linarith [hA1 0])).trans (hAt 0))
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ⟨hanti, hinter, h⟩
  obtain ⟨hanti_s, hinter_s, hlim_s⟩ := hball s hs hst.le
  obtain ⟨hanti_t, hinter_t, hlim_t⟩ := hball t ht le_rfl
  have hfin_s : R.measure (closedBall y s) ≠ ∞ := hfinB s (by linarith)
  have hfin_t : R.measure (closedBall y t) ≠ ∞ := hfinB t (by linarith)
  -- `ν = F_y μ`, so that `∫⁻_S F_y dμ = ν(S)` for Borel `S`
  obtain ⟨ν, hν⟩ : ∃ ν : Measure (Euclid P), ∀ S, MeasurableSet S →
      ∫⁻ x in S, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection
        (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure = ν S :=
    ⟨_, fun S hS => (withDensity_apply _ hS).symm⟩
  have hmeas : ∀ a b : ℝ, MeasurableSet (closedBall y a \ closedBall y b) := fun a b =>
    measurableSet_closedBall.diff measurableSet_closedBall
  -- the smoothed bounds (i'_m) and (ii'_m), with the annular integrals written via `ν`
  have hbd : ∀ m, ν (closedBall y t \ closedBall y (A m * s)) +
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) * R.measure (closedBall y s) ≤
        ENNReal.ofReal (Real.exp (A m * κ * t) / t ^ n) * R.measure (closedBall y (A m * t)) ∧
      ENNReal.ofReal (Real.exp (-(A m * κ * t)) / t ^ n) * R.measure (closedBall y t) ≤
        ENNReal.ofReal (Real.exp (-(A m * κ * s)) / s ^ n) * R.measure (closedBall y (A m * s)) +
        ENNReal.ofReal (A m ^ n) * ν (closedBall y (A m * t) \ closedBall y s) := by
    intro m
    rw [← hν _ (hmeas _ _), ← hν _ (hmeas _ _)]
    exact hsm (A m) s t (hA1 m) hs hst (hBA m)
  -- Step 4(a): the inner annuli `B̄_t∖B̄_{A_ms}` increase to `B̄_t∖B̄_s`
  have hin : Tendsto (fun m => ν (closedBall y t \ closedBall y (A m * s))) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hmono : Monotone fun m => closedBall y t \ closedBall y (A m * s) := fun i j hij =>
      sdiff_subset_sdiff_right (hanti_s hij)
    have h := tendsto_measure_iUnion_atTop (μ := ν) hmono
    rwa [← Set.sdiff_iInter, hinter_s] at h
  -- Step 4(b): `F_y(x) ≤ |x − y|⁻ⁿ ≤ s⁻ⁿ` off `B̄_s`, as `|v − p v| ≤ |v|`
  have hF : ∀ x : Euclid P, x ∉ closedBall y s →
      ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
        ‖x - y‖ ^ (n + 2) ≤ 1 / s ^ n := by
    intro x hx
    rw [mem_closedBall, not_le, dist_eq_norm] at hx
    have hr : 0 < ‖x - y‖ := hs.trans hx
    have hperp : ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ≤
        ‖x - y‖ := by
      rw [← Submodule.starProjection_orthogonal_val]
      exact Submodule.norm_starProjection_apply_le _ _
    calc ‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
          ‖x - y‖ ^ (n + 2)
        ≤ ‖x - y‖ ^ 2 / ‖x - y‖ ^ (n + 2) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hperp 2) (by positivity)
      _ = 1 / ‖x - y‖ ^ n := by
          rw [pow_add, div_mul_eq_div_div_swap, div_self (pow_ne_zero 2 hr.ne')]
      _ ≤ 1 / s ^ n := one_div_le_one_div_of_le (pow_pos hs n) (pow_le_pow_left₀ hs.le hx.le n)
  -- Step 4(b): the outer annuli `B̄_{A_mt}∖B̄_s` decrease to `B̄_t∖B̄_s`, the first having
  -- `ν(B̄_{A_0t}∖B̄_s) ≤ s⁻ⁿ μ(B̄_{A_0t}) < ∞`
  have hout : Tendsto (fun m => ν (closedBall y (A m * t) \ closedBall y s)) atTop
      (𝓝 (ν (closedBall y t \ closedBall y s))) := by
    have hanti' : Antitone fun m => closedBall y (A m * t) \ closedBall y s := fun i j hij =>
      sdiff_subset_sdiff_left (hanti_t hij)
    have hinter' : (⋂ m, closedBall y (A m * t) \ closedBall y s) =
        closedBall y t \ closedBall y s := by
      rw [← hinter_t]
      ext x
      simp only [mem_iInter, Set.mem_sdiff]
      exact ⟨fun h => ⟨fun m => (h m).1, (h 0).2⟩, fun h m => ⟨h.1 m, h.2⟩⟩
    have hle : ν (closedBall y (A 0 * t) \ closedBall y s) ≤
        ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) := by
      rw [← hν _ (hmeas _ _)]
      calc ∫⁻ x in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal
            (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
              ‖x - y‖ ^ (n + 2)) ∂R.measure
          ≤ ∫⁻ _ in closedBall y (A 0 * t) \ closedBall y s, ENNReal.ofReal (1 / s ^ n)
              ∂R.measure :=
            setLIntegral_mono' (hmeas _ _) fun x hx => ENNReal.ofReal_le_ofReal (hF x hx.2)
        _ = ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t) \ closedBall y s) :=
            setLIntegral_const _ _
        _ ≤ ENNReal.ofReal (1 / s ^ n) * R.measure (closedBall y (A 0 * t)) :=
            mul_le_mul' le_rfl (measure_mono sdiff_subset)
    have hfin' : ν (closedBall y (A 0 * t) \ closedBall y s) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinB _ (hAt 0))) hle
    have h := tendsto_measure_iInter_atTop (μ := ν)
      (fun m => (hmeas _ _).nullMeasurableSet) hanti' ⟨0, hfin'⟩
    rwa [hinter'] at h
  -- Step 5: the coefficients converge
  have hAκ : Tendsto (fun m => A m * κ) atTop (𝓝 κ) := by
    have h := hAlim.mul_const κ
    rwa [one_mul] at h
  have hexp : ∀ ρ : ℝ,
      Tendsto (fun m => ENNReal.ofReal (Real.exp (A m * κ * ρ) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n))) ∧
      Tendsto (fun m => ENNReal.ofReal (Real.exp (-(A m * κ * ρ)) / ρ ^ n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (-(κ * ρ)) / ρ ^ n))) := fun ρ =>
    ⟨ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).rexp).div_const _),
      ENNReal.tendsto_ofReal (((hAκ.mul_const ρ).neg.rexp).div_const _)⟩
  have hpow : Tendsto (fun m => ENNReal.ofReal (A m ^ n)) atTop (𝓝 1) := by
    have h := ENNReal.tendsto_ofReal (hAlim.pow n)
    rwa [one_pow, ENNReal.ofReal_one] at h
  rw [hν _ (hmeas _ _)]
  constructor
  · -- Step 6, (M1): `e^{κs} ≤ e^{A_mκs}`; pass to the limit in (i'_m)
    refine le_of_tendsto_of_tendsto' (hin.add tendsto_const_nhds)
      (ENNReal.Tendsto.mul (hexp t).1 (Or.inr hfin_t) hlim_t (Or.inr ENNReal.ofReal_ne_top))
      fun m => ?_
    have hcoef : ENNReal.ofReal (Real.exp (κ * s) / s ^ n) ≤
        ENNReal.ofReal (Real.exp (A m * κ * s) / s ^ n) := by
      refine ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (pow_pos hs n).le)
      rw [mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg hκ hs.le) (hA1 m).le
    exact le_trans (add_le_add le_rfl (mul_le_mul' hcoef le_rfl)) (hbd m).1
  · -- Step 7, (M2): pass to the limit in (ii'_m)
    have h := le_of_tendsto_of_tendsto'
      (ENNReal.Tendsto.mul_const (hexp t).2 (Or.inr hfin_t))
      ((ENNReal.Tendsto.mul (hexp s).2 (Or.inr hfin_s) hlim_s (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.mul hpow (Or.inl one_ne_zero) hout (Or.inr ENNReal.one_ne_top)))
      fun m => (hbd m).2
    rwa [one_mul] at h
/-- Lower density bound at a point with an approximate tangent plane (Simon Ch. 3, 1.5(3), and
Ch. 4, 4.10(1)): if `Q` is the approximate tangent space of `M` at `x`, `n ≥ 1` and `c < ωₙ`, then
`c ρⁿ ≤ Hⁿ(M ∩ B̄_ρ(x))` for all small `ρ > 0`.  Choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ` and test
against `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`, so `1_{B̄₁(0)} ≤ ψ ≤ 1_{B̄_{1+ε}(0)}`.  A linear
isometry `ℝⁿ → ℝᴾ` onto `Q` gives `∫_Q ψ dHⁿ ≥ Hⁿ(Q ∩ B₁(0)) = ωₙ`, while
`∫_{η_{x,r}(M)} ψ dHⁿ ≤ Hⁿ(B̄_{1+ε}(0) ∩ η_{x,r}(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{(1+ε)r}(x))`; the blow-up
integrals converge to `∫_Q ψ dHⁿ`, and `ρ = (1 + ε) r`. -/
theorem Submission.doragm_approxTangent_lower_density : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < n → HasApproximateTangentSpaceAt n M x Q → ∀ c : ℝ≥0∞, c < unitBallVolume n → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), c * ENNReal.ofReal (ρ ^ n) ≤ μHE[n] (M ∩ closedBall x ρ) := by
  intro P n M x Q _hn hQ c hc
  -- Step 1: `ωₙ < ∞`, so `c < ∞`; choose `ε > 0` with `c (1 + ε)ⁿ < ωₙ`
  have hω_top : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc_top : c ≠ ∞ := ne_top_of_lt hc
  have hcont : Tendsto (fun ε : ℝ => c * ENNReal.ofReal ((1 + ε) ^ n)) (𝓝 0) (𝓝 c) := by
    have h1 : Tendsto (fun ε : ℝ => (1 + ε) ^ n) (𝓝 0) (𝓝 1) := by
      have hc1 : Continuous fun ε : ℝ => (1 + ε) ^ n := by fun_prop
      simpa using hc1.tendsto 0
    simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h1) (Or.inr hc_top)
  obtain ⟨ε, hεω, hε⟩ := ((hcont.eventually (gt_mem_nhds hc)).filter_mono nhdsWithin_le_nhds |>.and
    (self_mem_nhdsWithin (s := Ioi (0 : ℝ)) (a := 0))).exists
  set A : ℝ := 1 + ε
  have hA : 0 < A := by linarith
  -- Step 2: the test function `ψ(y) = max 0 (min 1 ((1 + ε − |y|)/ε))`
  have hψcs : HasCompactSupport (fun y : Euclid P => max 0 (min 1 ((A - ‖y‖) / ε))) := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) A) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  let ψ : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 ((A - ‖y‖) / ε)), continuous_const.max
      (continuous_const.min ((continuous_const.sub continuous_norm).div_const ε))⟩, hψcs⟩
  have hψ_apply : ∀ y, ψ y = max 0 (min 1 ((A - ‖y‖) / ε)) := fun y => rfl
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => le_max_left _ _
  have hψle1 : ∀ y, ψ y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hψ1 : ∀ y : Euclid P, ‖y‖ ≤ 1 → ψ y = 1 := by
    intro y hy
    have hge : 1 ≤ (A - ‖y‖) / ε := by rw [le_div_iff₀ hε]; linarith
    rw [hψ_apply, min_eq_left hge, max_eq_right zero_le_one]
  have hψ_out : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) A → ψ y = 0 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    have hneg : (A - ‖y‖) / ε < 0 := div_neg_of_neg_of_pos (by linarith) hε
    rw [hψ_apply, min_eq_right (hneg.le.trans zero_le_one), max_eq_left hneg.le]
  -- Step 3: `Hⁿ(Q ∩ B₁(0)) = ωₙ`, via a linear isometry `ℝⁿ → ℝᴾ` onto `Q`
  have hplane : μHE[n] (ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P))) = unitBallVolume n := by
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ.1)
    have hj : Isometry (Q.subtypeₗᵢ ∘ b.repr.symm) := Q.subtypeₗᵢ.isometry.comp b.repr.symm.isometry
    have himg : (Q.subtypeₗᵢ ∘ b.repr.symm) '' ball (0 : Euclid n) 1 =
        ball (0 : Euclid P) 1 ∩ (Q : Set (Euclid P)) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨?_, (b.repr.symm v).2⟩
        rw [mem_ball_zero_iff] at hv ⊢
        rwa [Function.comp_apply, LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
      · rintro ⟨hy, hyQ⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_ball_zero_iff] at hy ⊢
          rwa [LinearIsometryEquiv.norm_map, ← Submodule.norm_coe]
        · simp
    rw [← himg, hj.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rfl
  have hL : (unitBallVolume n).toReal ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hQ.1
    calc (unitBallVolume n).toReal
        = ∫ y in ball (0 : Euclid P) 1, ψ y ∂((μHE[n] : Measure (Euclid P)).restrict Q) := by
          rw [setIntegral_congr_fun measurableSet_ball
            (fun y hy => hψ1 y (mem_ball_zero_iff.mp hy).le),
            setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
            Measure.restrict_apply measurableSet_ball, hplane]
      _ ≤ ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
          setIntegral_le_integral ψ.integrable (Eventually.of_forall hψ0)
  -- the blow-up integrals `a(r) = ∫_{η_r(M)} ψ dHⁿ` converge to `∫_Q ψ dHⁿ ≥ ωₙ > c (1 + ε)ⁿ`
  have hcA_top : c * ENNReal.ofReal (A ^ n) ≠ ∞ := ne_top_of_lt hεω
  have hcA_lt : (c * ENNReal.ofReal (A ^ n)).toReal < ∫ y in (Q : Set (Euclid P)), ψ y ∂μHE[n] :=
    (ENNReal.toReal_strict_mono hω_top hεω).trans_le hL
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (c * ENNReal.ofReal (A ^ n)).toReal <
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n] :=
    (hQ.2 ψ).eventually (lt_mem_nhds hcA_lt)
  -- Step 4: `ofReal (a(r)) ≤ Hⁿ(B̄_A(0) ∩ η_r(M)) = r⁻ⁿ Hⁿ(M ∩ B̄_{rA}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ T : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] T := by
    intro r hr T
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' T =
        AffineMap.homothety (0 : Euclid P) r⁻¹ '' ((fun y : Euclid P => y - x) '' T) := by
      rw [Set.image_image]
      refine Set.image_congr fun y _ => ?_
      change r⁻¹ • (y - x) = _
      rw [AffineMap.homothety_apply, vsub_eq_sub, sub_zero, vadd_eq_add, add_zero]
    have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himage, euclideanHausdorffMeasure_homothety_image n (0 : Euclid P) (inv_ne_zero hr.ne'),
      hτ.euclideanHausdorffMeasure_image, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm,
      Real.norm_of_nonneg (inv_pos.mpr hr).le]
  have hball : ∀ r : ℝ, 0 < r → closedBall (0 : Euclid P) A ∩
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (r * A)) := by
    intro r hr
    have hmem : ∀ y : Euclid P, Poincare.SimonGMT.Chapter03.blowUpMap x r y ∈
        closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A) := by
      intro y
      change r⁻¹ • (y - x) ∈ closedBall (0 : Euclid P) A ↔ y ∈ closedBall x (r * A)
      rw [mem_closedBall_zero_iff, mem_closedBall, dist_eq_norm, norm_smul,
        Real.norm_of_nonneg (inv_pos.mpr hr).le, ← div_eq_inv_mul, div_le_iff₀ hr, mul_comm A r]
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      exact ⟨z, ⟨hzM, (hmem z).mp hyB⟩, rfl⟩
    · rintro ⟨z, ⟨hzM, hzB⟩, rfl⟩
      exact ⟨(hmem z).mpr hzB, z, hzM, rfl⟩
  have hupper : ∀ r : ℝ, 0 < r →
      ENNReal.ofReal (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, ψ y ∂μHE[n]) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
    intro r hr
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hψ0)
      ψ.continuous.aestronglyMeasurable]
    refine ENNReal.ofReal_toReal_le.trans ?_
    calc ∫⁻ y, ENNReal.ofReal (ψ y)
          ∂((μHE[n] : Measure (Euclid P)).restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M))
        ≤ ∫⁻ y, (closedBall (0 : Euclid P) A).indicator 1 y
          ∂((μHE[n] : Measure (Euclid P)).restrict
            (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) A
          · rw [indicator_of_mem hy, Pi.one_apply]
            exact ENNReal.ofReal_le_one.mpr (hψle1 y)
          · rw [hψ_out y hy, ENNReal.ofReal_zero]
            exact zero_le
      _ = μHE[n] (closedBall (0 : Euclid P) A ∩
            Poincare.SimonGMT.Chapter03.blowUpMap x r '' M) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall]
      _ = ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [hball r hr, hscale r hr]
  -- Step 5: `c (rA)ⁿ ≤ Hⁿ(M ∩ B̄_{rA}(x))` for small `r > 0`; reparametrize `ρ = rA`
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      c * ENNReal.ofReal ((r * A) ^ n) ≤ μHE[n] (M ∩ closedBall x (r * A)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with r hr hr0
    have hr0' : 0 < r := hr0
    have h1 : c * ENNReal.ofReal (A ^ n) ≤
        ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) := by
      rw [← ENNReal.ofReal_toReal hcA_top]
      exact (ENNReal.ofReal_le_ofReal hr.le).trans (hupper r hr0')
    calc c * ENNReal.ofReal ((r * A) ^ n)
        = c * ENNReal.ofReal (A ^ n) * ENNReal.ofReal r ^ n := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg hr0'.le n), ENNReal.ofReal_pow hr0'.le,
            mul_comm (ENNReal.ofReal r ^ n), mul_assoc]
      _ ≤ ENNReal.ofReal (r⁻¹) ^ n * μHE[n] (M ∩ closedBall x (r * A)) * ENNReal.ofReal r ^ n := by
          gcongr
      _ = μHE[n] (M ∩ closedBall x (r * A)) := by
          rw [mul_comm (ENNReal.ofReal (r⁻¹) ^ n), mul_assoc, ← mul_pow,
            ← ENNReal.ofReal_mul (inv_nonneg.mpr hr0'.le), inv_mul_cancel₀ hr0'.ne',
            ENNReal.ofReal_one, one_pow, mul_one]
  have htend : Tendsto (fun ρ : ℝ => ρ / A) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using ((continuous_id.div_const A).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ρ hρ
      exact div_pos hρ hA
  filter_upwards [htend.eventually hev2] with ρ hρ
  rwa [div_mul_cancel₀ ρ hA.ne'] at hρ

/-- **Unit lower bound for the monotone ball ratio at support points** (Simon Ch. 4, 3.8–3.11
and 4.10(1)).  Let `μ = θ Hⁿ⌞M`, and let `f_z(ρ) = e^{κρ} ρ^{−n} μ(B_ρ(z))` be nondecreasing in
`ρ` whenever `B_ρ(z) ⊆ W`.  Then `ωₙ ≤ f_y(t)` for every `y ∈ spt μ` and `t > 0` with
`B_t(y) ⊆ W`.

Suppose `f_y(t) < ωₙ`.  By continuity from above there is `δ > 0` with `B_{t+δ}(y) ⊆ W` and
`b = e^{κt} t^{−n} μ(B_{t+δ}(y)) < c < ωₙ` for some `c`.  As `y ∈ spt μ`, `μ(B_δ(y)) > 0`, so
`B_δ(y)` contains a point `x` at which `M` has an approximate tangent space (`μ`-a.e. point does).
Then `Submission.doragm_approxTangent_lower_density` gives `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some
`0 < σ < t`.  Since `e^{κσ} ≥ 1`, `θ ≥ 1` on `M` and `B_t(x) ⊆ B_{t+δ}(y)`, monotonicity at `x`
gives `c ≤ f_x(σ) ≤ f_x(t) ≤ b`, a contradiction. -/
theorem Submission.doragm_support_ball_ratio_ge : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), 0 < n → IsOpen W → W ⊆ U → 0 ≤ κ → (∀ (z : Euclid P) (s t : ℝ), 0 < s → s < t → closedBall z t ⊆ W → ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall z s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall z t)) → ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro P n U W R κ hn hW hWU hκ hmono y hy t ht hyt
  -- `μ ≥ Hⁿ⌞M` on measurable sets, since `θ ≥ 1` on `M`
  have hHμ : ∀ S : Set (Euclid P), MeasurableSet S → μHE[n] (R.carrier ∩ S) ≤ R.measure S := by
    intro S hS
    rw [IMRep.measure, withDensity_apply _ hS, Measure.restrict_restrict hS, inter_comm,
      ← setLIntegral_one]
    apply setLIntegral_mono' (hS.inter R.measurableSet_carrier)
    intro x hx
    exact_mod_cast R.mult_pos x hx.2
  -- `μ` is finite on compact subsets of `U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- `μ`-a.e. point has an approximate tangent space, as `μ ≪ Hⁿ⌞M`
  have hgood : ∀ᵐ x ∂R.measure, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (R.orients.mono fun x ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩)
  -- suppose `f_y(t) < ωₙ`
  by_contra hlt
  rw [not_le] at hlt
  set A : ℝ≥0∞ := ENNReal.ofReal (Real.exp (κ * t) / t ^ n)
  -- `B_{t+δ₀}(y) ⊆ W`, and `μ(B_{t+δ₀/(m+1)}(y)) → μ(B_t(y))` by continuity from above
  obtain ⟨δ₀, hδ₀, hδ₀W⟩ := (isCompact_closedBall y t).exists_cthickening_subset_open hW hyt
  rw [cthickening_closedBall hδ₀.le ht.le] at hδ₀W
  have hanti : Antitone (fun m : ℕ => closedBall y (t + δ₀ / ((m : ℝ) + 1))) := by
    intro i j hij
    apply closedBall_subset_closedBall
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hij 1
    have : δ₀ / ((j : ℝ) + 1) ≤ δ₀ / ((i : ℝ) + 1) :=
      div_le_div_of_nonneg_left hδ₀.le hi hij'
    linarith
  have hinter : (⋂ m : ℕ, closedBall y (t + δ₀ / ((m : ℝ) + 1))) = closedBall y t := by
    ext z
    simp only [mem_iInter, mem_closedBall]
    constructor
    · intro h
      have hlim : Tendsto (fun m : ℕ => t + δ₀ * (1 / ((m : ℝ) + 1))) atTop (𝓝 (t + δ₀ * 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ₀)
      rw [mul_zero, add_zero] at hlim
      exact ge_of_tendsto' hlim fun m => by rw [mul_one_div]; exact h m
    · intro h m
      have : 0 < δ₀ / ((m : ℝ) + 1) := by positivity
      linarith
  have hfin0 : R.measure (closedBall y (t + δ₀ / (((0 : ℕ) : ℝ) + 1))) ≠ ∞ := by
    apply hfin _ (isCompact_closedBall _ _)
    refine Subset.trans (closedBall_subset_closedBall ?_) (hδ₀W.trans hWU)
    simp only [Nat.cast_zero, zero_add, div_one]
    linarith
  have hT : Tendsto (fun m : ℕ => A * R.measure (closedBall y (t + δ₀ / ((m : ℝ) + 1)))) atTop
      (𝓝 (A * R.measure (closedBall y t))) := by
    have h := tendsto_measure_iInter_atTop (μ := R.measure)
      (fun m => measurableSet_closedBall.nullMeasurableSet) hanti ⟨0, hfin0⟩
    rw [hinter] at h
    exact ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofReal_ne_top)
  -- fix `δ = δ₀/(m+1)` with `b = A μ(B_{t+δ}(y)) < c < ωₙ`
  obtain ⟨m, hm⟩ := (hT.eventually (gt_mem_nhds hlt)).exists
  set δ : ℝ := δ₀ / ((m : ℝ) + 1)
  have hδ : 0 < δ := by positivity
  have hδδ₀ : δ ≤ δ₀ := div_le_self hδ₀.le (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  obtain ⟨c, hbc, hcω⟩ := exists_between hm
  -- `y ∈ spt μ`, so `B_δ(y)` has positive measure and contains a point `x` with a tangent space
  have hpos : R.measure (ball y δ) ≠ 0 :=
    ((Measure.mem_support_iff_forall y).1 hy _ (ball_mem_nhds y hδ)).ne'
  obtain ⟨x, hx, Q, hQ⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae hgood)
  -- `B_t(x) ⊆ B_{t+δ}(y) ⊆ W`
  have hxy : dist x y < δ := mem_ball.1 hx
  have hBx : closedBall x t ⊆ closedBall y (t + δ) := closedBall_subset_closedBall' (by linarith)
  have hBxW : closedBall x t ⊆ W :=
    hBx.trans ((closedBall_subset_closedBall (by linarith)).trans hδ₀W)
  -- the tangent lower density at `x`: `c σⁿ ≤ Hⁿ(M ∩ B_σ(x))` for some `0 < σ < t`
  obtain ⟨σ, hσc, hσ0, hσt⟩ :=
    ((Submission.doragm_approxTangent_lower_density P n R.carrier x Q hn hQ c hcω).and
      (Ioo_mem_nhdsGT ht)).exists
  have hσn : 0 < σ ^ n := pow_pos hσ0 n
  have hcoef : ENNReal.ofReal (1 / σ ^ n) ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) :=
    ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right (Real.one_le_exp (mul_nonneg hκ hσ0.le)) hσn.le)
  have hone : ENNReal.ofReal (1 / σ ^ n) * ENNReal.ofReal (σ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), one_div, inv_mul_cancel₀ hσn.ne', ENNReal.ofReal_one]
  -- `c ≤ f_x(σ) ≤ f_x(t) ≤ b < c`
  have key : c ≤ A * R.measure (closedBall y (t + δ)) :=
    calc c = ENNReal.ofReal (1 / σ ^ n) * (c * ENNReal.ofReal (σ ^ n)) := by
          rw [mul_comm c, ← mul_assoc, hone, one_mul]
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * μHE[n] (R.carrier ∩ closedBall x σ) :=
          mul_le_mul' hcoef hσc
      _ ≤ ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (closedBall x σ) :=
          mul_le_mul' le_rfl (hHμ _ measurableSet_closedBall)
      _ ≤ A * R.measure (closedBall x t) := hmono x σ t hσ0 hσt hBxW
      _ ≤ A * R.measure (closedBall y (t + δ)) := mul_le_mul' le_rfl (measure_mono hBx)
  exact absurd (key.trans_lt hbc) (lt_irrefl c)
/-- **Radial cut-off** (step 1 of the tilt-excess/height estimate, Simon 5.2.1: `ζ ≡ 1` in
`B_{ρ/2}`, `ζ ≡ 0` outside `B_ρ`, `|∇ζ| ≤ 3/ρ`).  For `r > 0` there is a `C¹` function `ζ` on `ℝᴾ`
with `0 ≤ ζ ≤ 1`, `ζ = 1` on `B̄_{r/2}(ξ)`, `tsupport ζ ⊆ B̄_r(ξ)` and `‖Dζ‖ ≤ 3/r`.  Take
`ζ(x) = φ(‖x − ξ‖/r)` for a `C^∞` profile `φ` that is `1` on `(−∞, 1/2]`, `0` on `[1, ∞)` and
`3`-Lipschitz: `φ(σ) = 1 − c⁻¹∫_{1/2}^σ g`, where `g` is a smooth bump on `[1/2, 1]` equal to `1`
on `[7/12, 11/12]` and `c = ∫_{1/2}^1 g ≥ 1/3`.  Then `ζ` is constant near `ξ` and smooth away
from `ξ`, and `(3/r)`-Lipschitz by the reverse triangle inequality. -/
theorem Submission.dorag_th_radial_cutoff : ∀ (P : ℕ) (ξ : Euclid P) (r : ℝ), 0 < r → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) ∧ (∀ x ∈ closedBall ξ (r / 2), ζ x = 1) ∧ tsupport ζ ⊆ closedBall ξ r ∧ ∀ x, ‖fderiv ℝ ζ x‖ ≤ 3 / r := by
  intro P ξ r hr
  -- Steps 1–2: an admissible profile `φ`, the smoothTransition primitive of the Remark
  obtain ⟨φ, hφ_smooth, hφ_bounds, hφ_one, hφ_zero, hφ_lip⟩ : ∃ φ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ t, 0 ≤ φ t ∧ φ t ≤ 1) ∧ (∀ t, t ≤ 1 / 2 → φ t = 1) ∧
      (∀ t, 1 ≤ t → φ t = 0) ∧ LipschitzWith 3 φ := by
    -- the bump `g(t) = S(12(t − 1/2)) S(12(1 − t))`
    set g : ℝ → ℝ := fun t =>
      Real.smoothTransition (12 * (t - 1 / 2)) * Real.smoothTransition (12 * (1 - t)) with hg_eq
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      have h₁ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (t - 1 / 2) := by fun_prop
      have h₂ : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => 12 * (1 - t) := by fun_prop
      exact (Real.smoothTransition.contDiff.comp h₁).mul (Real.smoothTransition.contDiff.comp h₂)
    have hg_cont : Continuous g := hg_smooth.continuous
    have hg_int : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b =>
      hg_cont.intervalIntegrable a b
    have hg_nonneg : ∀ t, 0 ≤ g t := fun t =>
      mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have hg_le_one : ∀ t, g t ≤ 1 := fun t =>
      (mul_le_of_le_one_left (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)).trans
        (Real.smoothTransition.le_one _)
    have hg_left : ∀ t, t ≤ 1 / 2 → g t = 0 := fun t ht => by
      simp only [hg_eq]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
    have hg_right : ∀ t, 1 ≤ t → g t = 0 := fun t ht => by
      simp only [hg_eq]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith : 12 * (1 - t) ≤ 0), mul_zero]
    have hg_mid : ∀ t, 7 / 12 ≤ t → t ≤ 11 / 12 → g t = 1 := fun t h₁ h₂ => by
      simp only [hg_eq]
      rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith), mul_one]
    -- `c = ∫_{1/2}^1 g ≥ ∫_{7/12}^{11/12} 1 = 1/3`, so `c⁻¹ ≤ 3`
    set c : ℝ := ∫ s in (1 / 2 : ℝ)..1, g s with hc_eq
    have hc_ge : 1 / 3 ≤ c := by
      have h : ∫ s in (7 / 12 : ℝ)..(11 / 12), g s = 1 / 3 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
        · simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one]
          norm_num
        · intro s hs
          rw [uIcc_of_le (by norm_num)] at hs
          exact hg_mid s hs.1 hs.2
      rw [← h]
      exact intervalIntegral.integral_mono_interval (by norm_num) (by norm_num) (by norm_num)
        (ae_of_all _ hg_nonneg) (hg_int _ _)
    have hc_pos : 0 < c := by linarith
    have hcinv_le : c⁻¹ ≤ 3 := by
      rw [inv_le_comm₀ hc_pos (by norm_num)]
      linarith
    -- the primitive `F(t) = ∫_{1/2}^t g`, with `F' = g`
    set F : ℝ → ℝ := fun t => ∫ s in (1 / 2 : ℝ)..t, g s with hF_eq
    have hF_deriv : ∀ t, HasDerivAt F (g t) t := fun t =>
      (hg_cont.integral_hasStrictDerivAt (1 / 2) t).hasDerivAt
    have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F :=
      contDiff_infty_iff_deriv.2 ⟨fun t => (hF_deriv t).differentiableAt,
        (funext fun t => (hF_deriv t).deriv : deriv F = g) ▸ hg_smooth⟩
    have hF_left : ∀ t, t ≤ 1 / 2 → F t = 0 := fun t ht => by
      simp only [hF_eq]
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
      · simp
      · intro s hs
        rw [uIcc_of_ge ht] at hs
        exact hg_left s hs.2
    have hF_right : ∀ t, 1 ≤ t → F t = c := fun t ht => by
      simp only [hF_eq, hc_eq]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hg_int (1 / 2) 1) (hg_int 1 t)]
      have h : ∫ s in (1 : ℝ)..t, g s = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
        · simp
        · intro s hs
          rw [uIcc_of_le ht] at hs
          exact hg_right s hs.1
      rw [h, add_zero]
    have hF_bounds : ∀ t, 0 ≤ F t ∧ F t ≤ c := fun t => by
      rcases le_total t (1 / 2) with ht | ht
      · rw [hF_left t ht]
        exact ⟨le_rfl, hc_pos.le⟩
      rcases le_total 1 t with ht' | ht'
      · rw [hF_right t ht']
        exact ⟨hc_pos.le, le_rfl⟩
      exact ⟨intervalIntegral.integral_nonneg ht fun u _ => hg_nonneg u,
        intervalIntegral.integral_mono_interval le_rfl ht ht' (ae_of_all _ hg_nonneg) (hg_int _ _)⟩
    -- `φ = 1 − c⁻¹F`, with `φ' = −c⁻¹g`
    have hφ_deriv : ∀ t, HasDerivAt (fun t => 1 - c⁻¹ * F t) (-(c⁻¹ * g t)) t := fun t => by
      simpa using ((hF_deriv t).const_mul c⁻¹).const_sub 1
    refine ⟨fun t => 1 - c⁻¹ * F t, contDiff_const.sub (contDiff_const.mul hF_smooth), ?_, ?_, ?_, ?_⟩
    · intro t
      obtain ⟨h₀, h₁⟩ := hF_bounds t
      have hci : 0 ≤ c⁻¹ := inv_nonneg.2 hc_pos.le
      have h : c⁻¹ * F t ≤ 1 := by
        calc c⁻¹ * F t ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left h₁ hci
          _ = 1 := inv_mul_cancel₀ hc_pos.ne'
      exact ⟨by linarith, by linarith [mul_nonneg hci h₀]⟩
    · intro t ht
      simp only [hF_left t ht, mul_zero, sub_zero]
    · intro t ht
      simp only [hF_right t ht, inv_mul_cancel₀ hc_pos.ne', sub_self]
    · refine lipschitzWith_of_nnnorm_deriv_le (fun t => (hφ_deriv t).differentiableAt) fun t => ?_
      rw [(hφ_deriv t).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg,
        abs_of_nonneg (mul_nonneg (inv_nonneg.2 hc_pos.le) (hg_nonneg t))]
      calc c⁻¹ * g t ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left (hg_le_one t) (inv_nonneg.2 hc_pos.le)
        _ ≤ 3 := by rw [mul_one]; exact hcinv_le
        _ = ((3 : NNReal) : ℝ) := by norm_num
  -- Step 3: `ζ(x) = φ(‖x − ξ‖/r)`.  Step 6: `ζ` is `C^∞` — constant `1` on `B_{r/2}(ξ)`, and
  -- `φ` composed with the smooth map `‖· − ξ‖/r` on `ℝᴾ \ {ξ}`
  have hC : ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid P => φ (‖x - ξ‖ / r)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases eq_or_ne x ξ with rfl | hx
    · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds x (half_pos hr)] with y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hφ_one _ ((div_le_iff₀ hr).2 (by linarith))
    · have h : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Euclid P => ‖y - ξ‖ / r) x :=
        ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hx)).div_const r
      exact hφ_smooth.contDiffAt.comp x h
  -- Step 7: `ζ` is `(3/r)`-Lipschitz (`φ` is `3`-Lipschitz, reverse triangle inequality)
  have hlip : LipschitzWith (3 / r.toNNReal) fun y : Euclid P => φ (‖y - ξ‖ / r) := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [NNReal.coe_div, Real.coe_toNNReal r hr.le]
    calc dist (φ (‖y - ξ‖ / r)) (φ (‖z - ξ‖ / r))
        ≤ (3 : NNReal) * dist (‖y - ξ‖ / r) (‖z - ξ‖ / r) := hφ_lip.dist_le_mul _ _
      _ = 3 / r * |‖y - ξ‖ - ‖z - ξ‖| := by
          rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr, NNReal.coe_ofNat]; ring
      _ ≤ 3 / r * ‖(y - ξ) - (z - ξ)‖ := by gcongr; exact abs_norm_sub_norm_le _ _
      _ = (3 : NNReal) / r * dist y z := by
          rw [sub_sub_sub_cancel_right, dist_eq_norm, NNReal.coe_ofNat]
  refine ⟨fun x => φ (‖x - ξ‖ / r), hC.of_le (by norm_cast), fun x => hφ_bounds _,
    fun x hx => hφ_one _ ?_, ?_, fun x => ?_⟩
  -- Step 4: plateau, `‖x − ξ‖ ≤ r/2 ⇒ ‖x − ξ‖/r ≤ 1/2`
  · rw [Metric.mem_closedBall, dist_eq_norm] at hx
    rw [div_le_iff₀ hr]
    linarith
  -- Step 5: `ζ = 0` off `B_r(ξ)`, so `tsupport ζ ⊆ closure B_r(ξ) ⊆ B̄_r(ξ)`
  · refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro x hx
    by_contra hxb
    apply hx
    rw [Metric.mem_ball, dist_eq_norm, not_lt] at hxb
    exact hφ_zero _ ((le_div_iff₀ hr).2 (by linarith))
  -- Step 7: `‖Dζ(x)‖ ≤ 3/r` from the Lipschitz bound
  · have h := norm_fderiv_le_of_lipschitz ℝ hlip (x₀ := x)
    rwa [NNReal.coe_div, Real.coe_toNNReal r hr.le] at h
/-- Step 3 of the tilt-excess/height estimate (Simon Ch. 5, Lemma 2.1, display (2)): for
subspaces `T`, `S` of `ℝᴾ` with `dim T = dim S`,
`trace(p_T ∘ (I − p_S)) = ½ Σᵢ |p_T eᵢ − p_S eᵢ|²`, i.e. `½ |p_T − p_S|²` in the Hilbert–Schmidt
norm.  `p_T`, `p_S` are symmetric idempotents with `trace p_T = dim T`, `trace p_S = dim S`
(`p = ι ∘ π`, cyclicity), so `Σᵢ |(p_T − p_S) eᵢ|² = trace((p_T − p_S)²) =
dim T + dim S − 2 trace(p_T p_S)`, while `trace(p_T (I − p_S)) = dim T − trace(p_T p_S)`. -/
theorem Submission.dorag_th_trace_proj_comp_compl : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)), Module.finrank ℝ T = Module.finrank ℝ S → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) = 1 / 2 * ∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  intro P T S hTS
  -- step 2: `trace p_K = dim K`, as `p_K = ι ∘ π`, `π ∘ ι = id_K` and the trace is cyclic
  have htr : ∀ K : Submodule ℝ (Euclid P),
      LinearMap.trace ℝ (Euclid P) K.starProjection.toLinearMap =
        (Module.finrank ℝ K : ℝ) := by
    intro K
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
    have hcomp :
        K.orthogonalProjectionOnto.toLinearMap ∘ₗ K.subtypeL.toLinearMap = LinearMap.id := by
      ext x
      simp
    rw [hcomp, LinearMap.trace_id]
  set p : Euclid P →L[ℝ] Euclid P := T.starProjection
  set s : Euclid P →L[ℝ] Euclid P := S.starProjection
  have hp : LinearMap.trace ℝ (Euclid P) p.toLinearMap = (Module.finrank ℝ T : ℝ) := htr T
  have hs : LinearMap.trace ℝ (Euclid P) s.toLinearMap = (Module.finrank ℝ S : ℝ) := htr S
  -- step 1: `p` and `s` are symmetric idempotents
  have hp_symm : ∀ u w : Euclid P, inner ℝ (p u) w = inner ℝ u (p w) :=
    T.inner_starProjection_left_eq_right
  have hs_symm : ∀ u w : Euclid P, inner ℝ (s u) w = inner ℝ u (s w) :=
    S.inner_starProjection_left_eq_right
  have hpp : p.toLinearMap ∘ₗ p.toLinearMap = p.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap T.isIdempotentElem_starProjection.eq
  have hss : s.toLinearMap ∘ₗ s.toLinearMap = s.toLinearMap := by
    rw [← ContinuousLinearMap.toLinearMap_comp]
    exact congrArg ContinuousLinearMap.toLinearMap S.isIdempotentElem_starProjection.eq
  -- steps 3–4: `D = p - s` is symmetric, so `Σᵢ ‖D eᵢ‖² = Σᵢ ⟪eᵢ, D (D eᵢ)⟫ = trace (D ∘ D)`
  have hD : ∀ u w : Euclid P, inner ℝ ((p - s) u) w = inner ℝ u ((p - s) w) := by
    intro u w
    simp only [sub_apply, inner_sub_left, inner_sub_right, hp_symm, hs_symm]
  have hsum : ∑ i : Fin P,
      ‖p (EuclideanSpace.single i (1 : ℝ)) - s (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 =
        LinearMap.trace ℝ (Euclid P) ((p - s).toLinearMap ∘ₗ (p - s).toLinearMap) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ← hD,
      real_inner_self_eq_norm_sq, sub_apply]
  -- step 6: `p ∘ (I - s) = p - p ∘ s`
  have hlhs : p.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - s).toLinearMap =
      p.toLinearMap - p.toLinearMap ∘ₗ s.toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, ContinuousLinearMap.coe_id,
      LinearMap.comp_id]
  -- step 5: `D ∘ D = p + s - p ∘ s - s ∘ p` and `trace (s ∘ p) = trace (p ∘ s)`; step 7
  rw [hlhs, hsum, ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, hpp, hss, map_sub, map_sub, map_sub, map_sub,
    LinearMap.trace_comp_comm' p.toLinearMap s.toLinearMap, hp, hs, hTS]
  ring
/-- **Operator norm ≤ Hilbert–Schmidt norm** (step 3 of the tilt-excess estimate, Simon 5.2.1: the
bound `‖p_x − p_S‖ ≤ |p_x − p_S|` used for the cross term).  For every linear map `A` of `ℝᴾ` and
every `v ∈ ℝᴾ`, `|Av|² ≤ (Σᵢ |A eᵢ|²) |v|²`, where `eᵢ` is the standard basis.  Expanding
`v = Σᵢ vᵢ eᵢ` gives `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|` by the triangle inequality;
squaring and Cauchy–Schwarz give `|Av|² ≤ (Σᵢ vᵢ²)(Σᵢ |A eᵢ|²)`, and `Σᵢ vᵢ² = |v|²`. -/
theorem Submission.dorag_th_norm_apply_sq_le_hs : ∀ (P : ℕ) (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P), ‖A v‖ ^ 2 ≤ (∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v‖ ^ 2 := by
  intro P A v
  -- Step 1: `v = Σᵢ vᵢ eᵢ` in the orthonormal basis `EuclideanSpace.basisFun`
  have hv : v = ∑ i : Fin P, v i • EuclideanSpace.single i (1 : ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v).symm
  -- Step 2: `Av = Σᵢ vᵢ A eᵢ`, so `|Av| ≤ Σᵢ |vᵢ| |A eᵢ|`
  have hAv : A v = ∑ i : Fin P, v i • A (EuclideanSpace.single i (1 : ℝ)) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul]
  have h1 : ‖A v‖ ≤ ∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
    rw [hAv]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp [norm_smul]
  -- Step 3: Cauchy–Schwarz for finite sums, and `Σᵢ |vᵢ|² = |v|²`
  have h2 : (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 ≤
      (∑ i : Fin P, |v i| ^ 2) * ∑ i : Fin P, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ i : Fin P, |v i| ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sq_abs]
  -- Step 4: both sides of step 2 are nonnegative, so square it and combine with step 3
  calc ‖A v‖ ^ 2 ≤ (∑ i : Fin P, |v i| * ‖A (EuclideanSpace.single i (1 : ℝ))‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2
    _ = _ := by rw [h3, mul_comm]
/-- **Divergence of the tilt test field `X(y) = ζ(y)²((y − ξ) − p_S(y − ξ))`** (Simon Ch. 5, proof
of Lemma 2.1: the test field `X = ζ²(x)x′` and the computation of `div_M X`, chapter-05.txt
lines 222–247).  With `w(y) = (y − ξ) − p_S(y − ξ)`, `Dw(x) = I − p_S` and
`D(ζ²)(x) = 2ζ(x)Dζ(x)`, so by the product rule `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`
(`(L ⊗ u)h = L(h)u`).  Composing with `p_T`, linearity of the trace and `trace(L ⊗ u) = L(u)` give
`trace(p_T ∘ DX(x)) = ζ(x)² trace(p_T ∘ (I − p_S)) + 2ζ(x) Dζ(x)[p_T w(x)]`; for
`T = approxTangentPlane n M x` the left side is `tangentialDivergence n M X x = div_M X(x)`. -/
theorem Submission.dorag_th_trace_comp_fderiv_test_field : ∀ (P : ℕ) (T S : Submodule ℝ (Euclid P)) (ζ : Euclid P → ℝ) (ξ x : Euclid P), DifferentiableAt ℝ ζ x → LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (fderiv ℝ (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))) x).toLinearMap) = ζ x ^ 2 * LinearMap.trace ℝ (Euclid P) (T.starProjection.toLinearMap ∘ₗ (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) + 2 * ζ x * fderiv ℝ ζ x (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
  intro P T S ζ ξ x hζ
  -- Step 1: `w(y) = (y − ξ) − p_S(y − ξ)` is affine, with `Dw(x) = I − p_S`.
  have hw : HasFDerivAt (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ))
      (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) x := by
    have h : HasFDerivAt (fun y : Euclid P => y - ξ) (ContinuousLinearMap.id ℝ (Euclid P)) x :=
      (hasFDerivAt_id x).sub_const ξ
    have h' := h.sub (S.starProjection.hasFDerivAt.comp x h)
    rwa [ContinuousLinearMap.comp_id] at h'
  -- Step 2: `D(ζ²)(x) = 2ζ(x)·Dζ(x)`.
  have hg : HasFDerivAt (fun y => ζ y ^ 2) ((2 * ζ x) • fderiv ℝ ζ x) x := by
    simpa using hζ.hasFDerivAt.pow 2
  -- Step 3: product rule, `DX(x) = ζ(x)²(I − p_S) + (2ζ(x)Dζ(x)) ⊗ w(x)`.
  have hX : HasFDerivAt (fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ)))
      (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection) +
        ((2 * ζ x) • fderiv ℝ ζ x).smulRight ((x - ξ) - S.starProjection (x - ξ))) x :=
    hg.smul hw
  rw [hX.fderiv]
  -- Step 4: `p_T ∘ DX(x) = ζ(x)²(p_T ∘ (I − p_S)) + (2ζ(x)Dζ(x)) ⊗ p_T w(x)`.
  have hcomp : T.starProjection.toLinearMap ∘ₗ (ζ x ^ 2 • (ContinuousLinearMap.id ℝ (Euclid P) -
        S.starProjection) + ((2 * ζ x) • fderiv ℝ ζ x).smulRight
          ((x - ξ) - S.starProjection (x - ξ))).toLinearMap =
      ζ x ^ 2 • (T.starProjection.toLinearMap ∘ₗ
          (ContinuousLinearMap.id ℝ (Euclid P) - S.starProjection).toLinearMap) +
        (2 * ζ x) • (fderiv ℝ ζ x).toLinearMap.smulRight
          (T.starProjection ((x - ξ) - S.starProjection (x - ξ))) := by
    ext v
    simp [smul_smul]
  -- Steps 5–6: the trace is linear and `trace(L ⊗ u) = L(u)`.
  rw [hcomp, map_add, map_smul, map_smul, LinearMap.trace_smulRight, smul_eq_mul, smul_eq_mul,
    ContinuousLinearMap.coe_coe]

/-- **Simon, proof of Ch. 5, Lemma 2.1** (displays (1)–(3)), for an arbitrary cut-off `ζ`: with
`w(x) = (x − ξ) − p_S(x − ξ)`, `∫ζ²|p_{TₓM} − p_S|² dμ ≤ 16∫|Dζ|²|w|² dμ + 4∫κζ²|w| dμ`.
Test the first variation with `X = ζ²w`.  For `μ`-a.e. `x` we have `dim TₓM = n = dim S`, so
`div_M X = ½ζ²|p_{TₓM} − p_S|² + 2ζ Dζ[p_{TₓM}w]` (`dorag_th_trace_comp_fderiv_test_field`,
`dorag_th_trace_proj_comp_compl`).  As `p_S w = 0`, `|p_{TₓM}w| ≤ |p_{TₓM} − p_S| |w|`
(`dorag_th_norm_apply_sq_le_hs`), and `2αβ ≤ ¼α² + 4β²` bounds the cross term; `|⟨X, H⟩| ≤ κζ²|w|`.
Every integrand is bounded and vanishes off the compact `tsupport ζ ⊆ U`, which has finite
`μ`-measure, so the `¼`-term can be absorbed. -/
theorem Submission.dorag_th_tilt_energy_inequality : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (S : Submodule ℝ (Euclid P)) (ξ : Euclid P) (ζ : Euclid P → ℝ), W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → Module.finrank ℝ S = n → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ W → ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure := by
  intro P n U W R H κ S ξ ζ hWU hpM hH hHκ hMC hS hζC hζcpt hζW
  -- Step 1: `κ ≥ 0`.
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- Step 2: `K = tsupport ζ` is compact and `K ⊆ U`, so `μ(K) < ∞`.
  have hKm : MeasurableSet (tsupport ζ) := (isClosed_tsupport ζ).measurableSet
  have hμK : R.measure (tsupport ζ) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hζcpt (hζW.trans hWU)
  -- Step 3: bounded a.e. strongly measurable functions vanishing off `K` are integrable.
  have hint : ∀ f : Euclid P → ℝ, AEStronglyMeasurable f R.measure → (∃ C, ∀ x, |f x| ≤ C) →
      (∀ x, x ∉ tsupport ζ → f x = 0) → Integrable f R.measure := by
    rintro f hf ⟨C, hC⟩ h0
    have hg : Integrable ((tsupport ζ).indicator (fun _ => C)) R.measure :=
      (integrableOn_const hμK).integrable_indicator hKm
    refine hg.mono' hf (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact hC x
    · rw [Set.indicator_of_notMem hx, h0 x hx, norm_zero]
  -- Step 4: `|ζ| ≤ Z`, `‖Dζ‖ ≤ D'`, `|w| ≤ B` on `K`, `ζ = Dζ = 0` off `K`, `0 ≤ a ≤ 4P`.
  have hζ_cont : Continuous ζ := hζC.continuous
  have hDζ_cont : Continuous (fderiv ℝ ζ) := hζC.continuous_fderiv one_ne_zero
  have hζ0 : ∀ x, x ∉ tsupport ζ → ζ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hDζ0 : ∀ x, x ∉ tsupport ζ → fderiv ℝ ζ x = 0 := fun x hx => fderiv_of_notMem_tsupport ℝ hx
  have hw_cont : Continuous (fun y : Euclid P => (y - ξ) - S.starProjection (y - ξ)) := by fun_prop
  obtain ⟨Z, hZ⟩ := hζ_cont.bounded_above_of_compact_support hζcpt
  obtain ⟨D', hD'⟩ := hDζ_cont.bounded_above_of_compact_support (hζcpt.fderiv (𝕜 := ℝ))
  obtain ⟨B₁, hB₁⟩ := IsCompact.exists_bound_of_continuousOn hζcpt hw_cont.continuousOn
  set B := max B₁ 0
  have hB : ∀ x ∈ tsupport ζ, ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤ B :=
    fun x hx => (hB₁ x hx).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ ξ)
  have hD'0 : 0 ≤ D' := (norm_nonneg _).trans (hD' ξ)
  have hζsq : ∀ x, ζ x ^ 2 ≤ Z ^ 2 := by
    intro x
    have := hZ x; rw [Real.norm_eq_abs] at this
    nlinarith [abs_nonneg (ζ x), sq_abs (ζ x)]
  set a : Euclid P → ℝ := fun x => ∑ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
      (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have ha0 : ∀ x, 0 ≤ a x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have ha_le : ∀ x, a x ≤ 4 * P := by
    intro x
    have : ∀ i : Fin P, ‖(approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
          ≤ 4 := by
      intro i
      have h1 := (approxTangentPlane n R.carrier x).norm_starProjection_apply_le
        (EuclideanSpace.single i (1 : ℝ))
      have h2 := S.norm_starProjection_apply_le (EuclideanSpace.single i (1 : ℝ))
      have h3 := norm_sub_le ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ))) (S.starProjection (EuclideanSpace.single i (1 : ℝ)))
      simp only [PiLp.norm_single, norm_one] at h1 h2
      nlinarith [norm_nonneg ((approxTangentPlane n R.carrier x).starProjection
        (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ)))]
    calc a x ≤ ∑ _i : Fin P, (4 : ℝ) := Finset.sum_le_sum fun i _ => this i
      _ = 4 * P := by simp [mul_comm]
  -- Step 5: `a` and `x ↦ p_x w(x)` are `μ`-a.e. strongly measurable.
  have ha_meas : AEStronglyMeasurable a R.measure := by
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact (((hpM.apply_continuousLinearMap _).sub aestronglyMeasurable_const).norm).pow 2
  have hpw_meas : AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ))) R.measure :=
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (A : Euclid P →L[ℝ] Euclid P) (v : Euclid P) => A v)
      (by fun_prop) hpM hw_cont.aestronglyMeasurable
  -- Step 6: `F₁ = ζ²a`, `F₂ = 2ζ Dζ[p_x w]`, `F₃ = ⟨X, H⟩` (`X = ζ²w`), `G₁ = ‖Dζ‖²|w|²` and
  -- `G₂ = κζ²|w|` are bounded and vanish off `K`, hence are `μ`-integrable.
  set F1 : Euclid P → ℝ := fun x => ζ x ^ 2 * a x
  set F2 : Euclid P → ℝ := fun x => 2 * ζ x * fderiv ℝ ζ x
      ((approxTangentPlane n R.carrier x).starProjection ((x - ξ) - S.starProjection (x - ξ)))
  set X : Euclid P → Euclid P := fun y => ζ y ^ 2 • ((y - ξ) - S.starProjection (y - ξ))
  set F3 : Euclid P → ℝ := fun x => inner ℝ (X x) (H x)
  set G1 : Euclid P → ℝ := fun x => ‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2
  set G2 : Euclid P → ℝ := fun x => κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖
  have hX_cont : Continuous X := by fun_prop
  have hF1i : Integrable F1 R.measure := by
    refine hint F1 ((hζ_cont.aestronglyMeasurable.pow 2).mul ha_meas)
      ⟨Z ^ 2 * (4 * P), fun x => ?_⟩ (fun x hx => by simp [F1, hζ0 x hx])
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (ha0 x))]
    exact mul_le_mul (hζsq x) (ha_le x) (ha0 x) (sq_nonneg _)
  have hF2i : Integrable F2 R.measure := by
    refine hint F2 ?_ ⟨2 * Z * (D' * B), fun x => ?_⟩ (fun x hx => by simp [F2, hζ0 x hx])
    · exact (aestronglyMeasurable_const.mul hζ_cont.aestronglyMeasurable).mul
        (Continuous.comp_aestronglyMeasurable₂
          (g := fun (L : Euclid P →L[ℝ] ℝ) (v : Euclid P) => L v)
          (by fun_prop) hDζ_cont.aestronglyMeasurable hpw_meas)
    · by_cases hx : x ∈ tsupport ζ
      · have h1 : |ζ x| ≤ Z := by simpa [Real.norm_eq_abs] using hZ x
        have h2 : |fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
            ((x - ξ) - S.starProjection (x - ξ)))| ≤ D' * B := by
          rw [← Real.norm_eq_abs]
          calc _ ≤ ‖fderiv ℝ ζ x‖ * ‖(approxTangentPlane n R.carrier x).starProjection
                ((x - ξ) - S.starProjection (x - ξ))‖ := (fderiv ℝ ζ x).le_opNorm _
            _ ≤ D' * B := by
              apply mul_le_mul (hD' x) _ (norm_nonneg _) hD'0
              exact ((approxTangentPlane n R.carrier x).norm_starProjection_apply_le _).trans
                (hB x hx)
        simp only [F2, abs_mul, abs_two]
        have := mul_le_mul h1 h2 (abs_nonneg _) hZ0
        nlinarith [abs_nonneg (ζ x)]
      · simp only [F2, hζ0 x hx, mul_zero, zero_mul, abs_zero]
        positivity
  have hF3i : Integrable F3 R.measure := by
    refine hint F3 (Continuous.comp_aestronglyMeasurable₂
      (g := fun (u v : Euclid P) => (inner ℝ u v : ℝ)) continuous_inner
      hX_cont.aestronglyMeasurable hH) ⟨Z ^ 2 * B * κ, fun x => ?_⟩
      (fun x hx => by simp [F3, X, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · calc |F3 x| ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
        _ ≤ (Z ^ 2 * B) * κ := by
          apply mul_le_mul _ (hHκ x) (norm_nonneg _) (by positivity)
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
          exact mul_le_mul (hζsq x) (hB x hx) (norm_nonneg _) (sq_nonneg _)
    · simp only [F3, X, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_smul,
        inner_zero_left, abs_zero]
      positivity
  have hG1i : Integrable G1 R.measure := by
    refine hint G1 ((hDζ_cont.norm.pow 2).mul (hw_cont.norm.pow 2)).aestronglyMeasurable
      ⟨D' ^ 2 * B ^ 2, fun x => ?_⟩ (fun x hx => by simp [G1, hDζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hD' x) 2)
        (pow_le_pow_left₀ (norm_nonneg _) (hB x hx) 2) (sq_nonneg _) (sq_nonneg _)
    · simp only [G1, hDζ0 x hx, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
      positivity
  have hG2i : Integrable G2 R.measure := by
    refine hint G2 ((continuous_const.mul (hζ_cont.pow 2)).mul hw_cont.norm).aestronglyMeasurable
      ⟨κ * Z ^ 2 * B, fun x => ?_⟩ (fun x hx => by simp [G2, hζ0 x hx])
    by_cases hx : x ∈ tsupport ζ
    · rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hζsq x) hκ) (hB x hx) (norm_nonneg _)
        (by positivity)
    · simp only [G2, hζ0 x hx]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
        abs_zero]
      positivity
  -- Step 7: `X` is `C¹` with `tsupport X ⊆ K ⊆ W`, so `δV(X) = -∫F₃ dμ`.
  have hXC : ContDiff ℝ 1 X :=
    (hζC.pow 2).smul ((contDiff_id.sub contDiff_const).sub
      (S.starProjection.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hXsupp : tsupport X ⊆ tsupport ζ := by
    apply closure_mono
    intro y hy
    by_contra h
    apply hy
    simp only [Function.mem_support, not_not] at h
    simp [X, h]
  have hXcpt : HasCompactSupport X := hζcpt.mono' ((subset_tsupport X).trans hXsupp)
  have hMCX := hMC X hXC hXcpt (hXsupp.trans hζW)
  -- Step 8: `δV(X) = ∫ div_M X dμ`, since `μ = (Hⁿ⌞M).withDensity θ`.
  have hFV : R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
    have hm : Measurable (fun x => ((R.mult x : NNReal))) :=
      (measurable_from_nat (f := fun m : ℕ => (m : NNReal))).comp R.measurable_mult
    have h := integral_withDensity_eq_integral_smul hm
      (fun x => tangentialDivergence n R.carrier X x) (μ := μHE[n].restrict R.carrier)
    simp only [ENNReal.coe_natCast] at h
    rw [IMRep.measure, h, IMRep.firstVariation]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [NNReal.smul_def])
  rw [hFV] at hMCX
  -- Step 9: `dim TₓM = n` for `μ`-a.e. `x` (`R.orients`, `μ ≪ Hⁿ⌞M`).
  have hdim : ∀ᵐ x ∂R.measure, Module.finrank ℝ (approxTangentPlane n R.carrier x) = n := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec.1
  -- Step 10: `div_M X = ½F₁ + F₂` `μ`-a.e. (children (D) and (B)).
  have hdiv : (fun x => tangentialDivergence n R.carrier X x) =ᵐ[R.measure]
      (fun x => 1 / 2 * F1 x + F2 x) := by
    filter_upwards [hdim] with x hx
    have hd := Submission.dorag_th_trace_comp_fderiv_test_field P
      (approxTangentPlane n R.carrier x) S ζ ξ x ((hζC.differentiable one_ne_zero) x)
    rw [tangentialDivergence, hd,
      Submission.dorag_th_trace_proj_comp_compl P _ S (by rw [hx, hS])]
    simp only [F1, F2, a]
    ring
  -- Step 11: `½∫F₁ + ∫F₂ = ∫ div_M X dμ = δV(X) = -∫F₃`.
  have hid : 1 / 2 * ∫ x, F1 x ∂R.measure + ∫ x, F2 x ∂R.measure = -∫ x, F3 x ∂R.measure := by
    rw [← integral_const_mul, ← integral_add (hF1i.const_mul _) hF2i, ← integral_congr_ae hdiv]
    exact hMCX
  -- Step 12: cross term.  `p_S w = 0` gives `p_T w = (p_T - p_S)w`, so by child (C)
  -- `|L(p_T w)| ≤ ‖L‖ √|p_T - p_S|² |w|`; then `-F₂ ≤ ¼F₁ + 4G₁` by `2αβ ≤ ¼α² + 4β²`.
  have hcross : ∀ (T : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] ℝ) (v : Euclid P),
      |L (T.starProjection (v - S.starProjection v))| ≤
        ‖L‖ * (Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖v - S.starProjection v‖) := by
    intro T L v
    set w := v - S.starProjection v
    have hw : S.starProjection w = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff S).mpr
        (Submodule.sub_starProjection_mem_orthogonal v)
    have heq : T.starProjection w = (T.starProjection - S.starProjection) w := by
      simp [hw]
    have hsq := Submission.dorag_th_norm_apply_sq_le_hs P (T.starProjection - S.starProjection) w
    simp only [sub_apply] at hsq
    have hn : ‖(T.starProjection - S.starProjection) w‖ ≤
        Real.sqrt (∑ i : Fin P, ‖T.starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖w‖ := by
      rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg w),
        ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt (by simpa [sub_apply] using hsq)
    rw [heq]
    calc |L ((T.starProjection - S.starProjection) w)|
        ≤ ‖L‖ * ‖(T.starProjection - S.starProjection) w‖ := by
          rw [← Real.norm_eq_abs]; exact L.le_opNorm _
      _ ≤ _ := by gcongr
  have hb1 : ∀ x, -F2 x ≤ 1 / 4 * F1 x + 4 * G1 x := by
    intro x
    have ht := hcross (approxTangentPlane n R.carrier x) (fderiv ℝ ζ x) (x - ξ)
    set t := fderiv ℝ ζ x ((approxTangentPlane n R.carrier x).starProjection
      ((x - ξ) - S.starProjection (x - ξ)))
    set c := ‖fderiv ℝ ζ x‖
    set s := Real.sqrt (a x)
    set β := ‖(x - ξ) - S.starProjection (x - ξ)‖
    have hs : s ^ 2 = a x := Real.sq_sqrt (ha0 x)
    have hc0 : 0 ≤ c := norm_nonneg _
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hβ0 : 0 ≤ β := norm_nonneg _
    have h1 : -(2 * ζ x * t) ≤ 2 * |ζ x| * |t| := by
      have := neg_le_abs (2 * ζ x * t)
      rwa [abs_mul, abs_mul, abs_two] at this
    have h2 : 2 * |ζ x| * |t| ≤ 2 * |ζ x| * (c * (s * β)) := by gcongr
    have h3 : 2 * |ζ x| * (c * (s * β)) ≤ 1 / 4 * (ζ x ^ 2 * s ^ 2) + 4 * (c ^ 2 * β ^ 2) := by
      nlinarith [sq_nonneg (|ζ x| * s - 4 * c * β), sq_abs (ζ x), abs_nonneg (ζ x)]
    simp only [F1, F2, G1]
    rw [← hs]
    linarith
  -- Step 13: curvature term `-F₃ ≤ |X| |H| ≤ G₂`.
  have hb2 : ∀ x, -F3 x ≤ G2 x := by
    intro x
    calc -F3 x ≤ |F3 x| := neg_le_abs _
      _ ≤ ‖X x‖ * ‖H x‖ := abs_real_inner_le_norm _ _
      _ = ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ‖H x‖ := by
          simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (ζ x))]
      _ ≤ ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ * κ := by
          gcongr
          exact hHκ x
      _ = G2 x := by simp only [G2]; ring
  -- Step 14: integrate and absorb `¼∫F₁`: `∫F₁ ≤ 16∫G₁ + 4∫G₂`.
  have i1 : ∫ x, -F2 x ∂R.measure ≤ ∫ x, (1 / 4 * F1 x + 4 * G1 x) ∂R.measure :=
    integral_mono hF2i.neg ((hF1i.const_mul _).add (hG1i.const_mul _)) hb1
  have i2 : ∫ x, -F3 x ∂R.measure ≤ ∫ x, G2 x ∂R.measure := integral_mono hF3i.neg hG2i hb2
  rw [integral_neg] at i1 i2
  rw [integral_add (hF1i.const_mul _) (hG1i.const_mul _), integral_const_mul,
    integral_const_mul] at i1
  have hreal : ∫ x, F1 x ∂R.measure ≤ 16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure := by
    linarith
  -- Step 15: `F₁, G₁, G₂ ≥ 0` are integrable, so pass to lower integrals of `ofReal`.
  have hF1n : ∀ x, 0 ≤ F1 x := fun x => mul_nonneg (sq_nonneg _) (ha0 x)
  have hG1n : ∀ x, 0 ≤ G1 x := fun x => by positivity
  have hG2n : ∀ x, 0 ≤ G2 x := fun x => by positivity
  have l1 := ofReal_integral_eq_lintegral_ofReal hF1i (Filter.Eventually.of_forall hF1n)
  have l2 := ofReal_integral_eq_lintegral_ofReal hG1i (Filter.Eventually.of_forall hG1n)
  have l3 := ofReal_integral_eq_lintegral_ofReal hG2i (Filter.Eventually.of_forall hG2n)
  have hI1 : 0 ≤ ∫ x, G1 x ∂R.measure := integral_nonneg hG1n
  have hI2 : 0 ≤ ∫ x, G2 x ∂R.measure := integral_nonneg hG2n
  calc ∫⁻ x, ENNReal.ofReal (F1 x) ∂R.measure = ENNReal.ofReal (∫ x, F1 x ∂R.measure) := l1.symm
    _ ≤ ENNReal.ofReal (16 * ∫ x, G1 x ∂R.measure + 4 * ∫ x, G2 x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 16 * ENNReal.ofReal (∫ x, G1 x ∂R.measure) +
          ENNReal.ofReal 4 * ENNReal.ofReal (∫ x, G2 x ∂R.measure) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
    _ = _ := by rw [l2, l3]
/-- **The approximate tangent projection is `μ_V`-measurable** (Simon Ch. 3, 1.4 and 1.5(1);
Ch. 6, 3.1).  For `R = (M, θ, ξ)` with weight `μ_V = θ Hⁿ⌞M`, `x ↦ p_{TₓM}` is `μ_V`-a.e. strongly
measurable.  Since `μ_V ≪ Hⁿ⌞M`, it suffices to prove this for `Hⁿ⌞M`.  By uniqueness of
approximate tangent planes, `TₓM` is `Hⁿ⌞M`-a.e. the plane oriented by `ξ(x)`.  A unit simple
`n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and
`y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is `τ` with `τᵢ` replaced by `y`,
gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.  Hence `p_{TₓM} = G(ξ(x))` a.e.,
where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there is none).  `G` is Borel:
`Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of orthonormal frames and signs, and
`G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.dorag_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R
  classical
  -- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to prove measurability for `Hⁿ⌞M`
  refine AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (μHE[n].restrict R.carrier) fun x => (R.mult x : ℝ≥0∞)) ?_
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
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is the compact set `Φ(Ω ∩ F⁻¹(t))` together with the
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
  -- `Hⁿ⌞M`-a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes),
  -- so `p_{TₓM} = G(ξ(x))`
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

/-- **Monotonicity inequalities and the unit density lower bound** for bounded generalized mean
curvature (Simon Ch. 4, 3.16–3.17 with `‖H‖ ≤ κ`, and 4.10(1)).  Let `μ = θ Hⁿ⌞M` have generalized
mean curvature `H` in `W`, and let `F_y(x) = |p_x^⊥(x − y)|² / |x − y|^{n+2}`.
(1) The annular inequalities (M1) and (M2) are `Submission.doragm_annular_monotonicity` at
`P = n + k`.  The map `x ↦ p_x` is `μ`-measurable by
`Submission.dorag_approxTangent_starProjection_aesm`.
(2) Let `y ∈ spt μ`.  Since `κ ≥ ‖H 0‖ ≥ 0` and (M1) makes `ρ ↦ e^{κρ} ρ^{−n} μ(B_ρ(z))`
nondecreasing, `Submission.doragm_support_ball_ratio_ge` gives `e^{κs} s^{−n} μ(B_s(y)) ≥ ωₙ`.
With (M1) this yields `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{−n} μ(B_t(y))` for `0 < s < t`.
For `s = t/(m + 2)` the annuli increase to `B_t(y) \ {y}`, and `F_y(y) = 0`.  Monotone convergence
for the measure `F_y μ` therefore gives (D). -/
theorem Submission.dorag_monotonicity_density : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → (∀ (y : Euclid (n + k)) (s t : ℝ), 0 < s → s < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + ENNReal.ofReal (Real.exp (κ * s) / s ^ n) * R.measure (closedBall y s) ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) ∧ ENNReal.ofReal (Real.exp (-(κ * t)) / t ^ n) * R.measure (closedBall y t) ≤ ENNReal.ofReal (Real.exp (-(κ * s)) / s ^ n) * R.measure (closedBall y s) + ∫⁻ x in closedBall y t \ closedBall y s, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) ∧ ∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → (∫⁻ x in closedBall y t, ENNReal.ofReal (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 / ‖x - y‖ ^ (n + 2)) ∂R.measure) + unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
  intro n k hn U W R H κ hW hWU hH hHκ hFV
  -- (1) is the annular monotonicity, with `x ↦ p_x` measurable by the sibling lemma
  have hann := Submission.doragm_annular_monotonicity (n + k) n U W R H κ hW hWU
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hH hHκ hFV
  refine ⟨hann, fun y hy t ht hyt => ?_⟩
  -- `κ ≥ ‖H 0‖ ≥ 0`, and dropping the annular term of (M1) makes `ρ ↦ e^{κρ} ρ^{-n} μ(B_ρ(z))`
  -- nondecreasing, so this ratio is at least `ωₙ` at the support point `y`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hratio := Submission.doragm_support_ball_ratio_ge (n + k) n U W R κ hn hW hWU hκ
    (fun z s t hs hst hzt => le_add_self.trans (hann z s t hs hst hzt).1) y hy
  -- the integrand `F_y`, which vanishes at `y` because `‖0‖ ^ (n + 2) = 0`
  set F : Euclid (n + k) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (‖(x - y) - (approxTangentPlane n R.carrier x).starProjection (x - y)‖ ^ 2 /
      ‖x - y‖ ^ (n + 2)) with hF
  have hFy : F y = 0 := by simp [hF]
  -- for `0 < s < t`: `∫_{B_t(y) \ B_s(y)} F_y dμ + ωₙ ≤ e^{κt} t^{-n} μ(B_t(y))`
  have hannulus : ∀ s, 0 < s → s < t →
      (∫⁻ x in closedBall y t \ closedBall y s, F x ∂R.measure) + unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) :=
    fun s hs hst => (add_le_add le_rfl
      (hratio s hs ((closedBall_subset_closedBall hst.le).trans hyt))).trans
        (hann y s t hs hst hyt).1
  -- the annuli `B_t(y) \ B_{t/(m+2)}(y)` increase and cover `B_t(y) \ {y}`
  let A : ℕ → Set (Euclid (n + k)) := fun m => closedBall y t \ closedBall y (t / (m + 2))
  have hA : Monotone A := fun m m' hmm' => Set.sdiff_subset_sdiff_right
    (closedBall_subset_closedBall (div_le_div_of_nonneg_left ht.le (by positivity) (by gcongr)))
  have hcover : closedBall y t ⊆ (⋃ m, A m) ∪ {y} := by
    intro x hx
    by_cases hxy : x = y
    · exact Or.inr hxy
    have hd : 0 < dist x y := dist_pos.mpr hxy
    obtain ⟨m, hm⟩ := exists_nat_gt (t / dist x y)
    refine Or.inl (mem_iUnion.mpr ⟨m, hx, fun hxm => ?_⟩)
    rw [mem_closedBall, le_div_iff₀ (by positivity)] at hxm
    rw [div_lt_iff₀ hd] at hm
    nlinarith
  -- monotone convergence for the measure `F_y μ`
  have hν : ∀ s, MeasurableSet s → R.measure.withDensity F s = ∫⁻ x in s, F x ∂R.measure :=
    fun s hs => withDensity_apply F hs
  calc (∫⁻ x in closedBall y t, F x ∂R.measure) + unitBallVolume n
      = R.measure.withDensity F (closedBall y t) + unitBallVolume n := by
        rw [hν _ measurableSet_closedBall]
    _ ≤ (⨆ m, R.measure.withDensity F (A m)) + unitBallVolume n := by
        refine add_le_add ?_ le_rfl
        calc R.measure.withDensity F (closedBall y t)
            ≤ R.measure.withDensity F ((⋃ m, A m) ∪ {y}) := measure_mono hcover
          _ ≤ R.measure.withDensity F (⋃ m, A m) + R.measure.withDensity F {y} :=
            measure_union_le _ _
          _ = ⨆ m, R.measure.withDensity F (A m) := by
            rw [hA.measure_iUnion, hν _ (measurableSet_singleton y), lintegral_singleton, hFy,
              zero_mul, add_zero]
    _ = ⨆ m, (R.measure.withDensity F (A m) + unitBallVolume n) := ENNReal.iSup_add _
    _ ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t) := by
        refine iSup_le fun m => ?_
        have hm : (1 : ℝ) < m + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
        rw [hν (A m) (measurableSet_closedBall.diff measurableSet_closedBall)]
        exact hannulus _ (div_pos ht (by linarith)) (div_lt_self ht hm)

/-- **The support minus the carrier is `Hⁿ`-null** (Simon Ch. 1, 3.3; Ch. 4, 4.10(1)).  Let
`V = v(M, θ)` have mean curvature `H`, `|H| ≤ κ`, in the open set `W ⊆ U`, and let
`A = (spt μ_V ∩ W) \ M`.  Then `μ_V(A) = 0`, as `μ_V = θ Hⁿ⌞M` is concentrated on `M`.  At
`x ∈ A` the monotonicity bound `ωₙ ≤ e^{κt} t⁻ⁿ μ_V(B̄_t(x))` (`B̄_t(x) ⊆ W`) gives
`μ_V(B̄_t(x)) ≥ c tⁿ` for small `t`, with `c = ωₙ e^{-|κ|}`.  Since `μ_V` is locally finite at the
points of `A`, `A` has open neighbourhoods `O` with `μ_V(O) < ε`, and the density comparison
theorem gives `Hⁿ(A) ≤ C μ_V(O) ≤ C ε` with `C < ∞` depending only on `n + k`, `n` and `c`.
Letting `ε ↓ 0`, `Hⁿ(A) = 0`. -/
theorem Submission.dorag_support_sdiff_carrier_null : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 := by
  intro n k hn U W R H κ hW hWU hH hHκ hfv
  -- (D): `∫_{B̄_t(y)} F_y dμ_V + ωₙ ≤ e^{κt} t⁻ⁿ μ_V(B̄_t(y))` for `y ∈ spt μ_V`, `B̄_t(y) ⊆ W`
  have hD := (Submission.dorag_monotonicity_density n k hn U W R H κ hW hWU hH hHκ hfv).2
  -- `0 < ωₙ < ∞`, so `c = ωₙ e^{-|κ|} > 0`
  have hω0 : 0 < unitBallVolume n := by
    rw [unitBallVolume]
    exact measure_ball_pos _ _ one_pos
  have hωtop : unitBallVolume n ≠ ∞ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top.ne
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (unitBallVolume n).toReal * Real.exp (-|κ|) := ⟨_, rfl⟩
  have hc : 0 < c := hc_def ▸ mul_pos (ENNReal.toReal_pos hω0.ne' hωtop) (Real.exp_pos _)
  obtain ⟨C, hCtop, hcomp⟩ :=
    Submission.dorag_sn_hausdorff_le_mul_of_lower_density (n + k) n c hc
  -- step 1: `μ_V(Mᶜ) = 0`, as `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`; hence `μ_V(A) = 0`
  have hMc : R.measure R.carrierᶜ = 0 := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' R.measurableSet_carrier, compl_inter_self, measure_empty]
  have hA0 : R.measure ((R.measure.support ∩ W) \ R.carrier) = 0 :=
    measure_mono_null (fun x hx => hx.2) hMc
  -- every `x ∈ A ⊆ W` is the centre of a closed ball `B̄_r(x) ⊆ W`
  have hball : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier,
      ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ W := by
    intro x hx
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW x hx.1.2
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεW⟩
  -- a closed ball `B̄_r(x) ⊆ W ⊆ U` is a compact subset of `U`, so
  -- `μ_V(B̄_r(x)) = ∫_{M ∩ B̄_r(x)} θ dHⁿ < ∞`
  have hloc : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier,
      ∃ r : ℝ, 0 < r ∧ R.measure (ball x r) ≠ ∞ := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := hball x hx
    refine ⟨r, hr, ne_top_of_le_ne_top ?_ (measure_mono ball_subset_closedBall)⟩
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall x r) (hrW.trans hWU)
  -- step 2: for `x ∈ A` and `0 < t < min r 1`, (D) gives
  -- `μ_V(B̄_t(x)) ≥ e^{-κt} ωₙ tⁿ ≥ c tⁿ`, since `κt ≤ |κ|`
  have hdens : ∀ x ∈ (R.measure.support ∩ W) \ R.carrier, ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ R.measure (closedBall x t) := by
    intro x hx
    obtain ⟨r, hr, hrW⟩ := hball x hx
    refine ⟨min r 1, lt_min hr one_pos, fun t ht htr => ?_⟩
    have htW : closedBall x t ⊆ W :=
      (closedBall_subset_closedBall (htr.le.trans (min_le_left _ _))).trans hrW
    have h1 : unitBallVolume n ≤
        ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall x t) :=
      le_add_self.trans (hD x hx.1.1 t ht htW)
    have hkt : κ * t ≤ |κ| :=
      calc κ * t ≤ |κ| * t := mul_le_mul_of_nonneg_right (le_abs_self κ) ht.le
        _ ≤ |κ| := mul_le_of_le_one_right (abs_nonneg κ) (htr.le.trans (min_le_right _ _))
    have htn : t ^ n ≠ 0 := (pow_pos ht n).ne'
    have hexp : Real.exp (κ * t) ≠ 0 := (Real.exp_pos _).ne'
    calc ENNReal.ofReal (c * t ^ n)
        ≤ ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n * (unitBallVolume n).toReal) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hc_def, show Real.exp (-(κ * t)) * t ^ n * (unitBallVolume n).toReal =
            (unitBallVolume n).toReal * Real.exp (-(κ * t)) * t ^ n by ring]
          gcongr
      _ = ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n) * unitBallVolume n := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hωtop]
      _ ≤ ENNReal.ofReal (Real.exp (-(κ * t)) * t ^ n) *
          (ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall x t)) := by
          gcongr
      _ = R.measure (closedBall x t) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
            show Real.exp (-(κ * t)) * t ^ n * (Real.exp (κ * t) / t ^ n) = 1 by
              rw [Real.exp_neg]
              field_simp,
            ENNReal.ofReal_one, one_mul]
  -- steps 3–4: an open `O ⊇ A` with `μ_V(O) < ε` gives `Hⁿ(A) ≤ C μ_V(O) ≤ C ε`
  have hbound : ∀ ε : ℝ≥0∞, 0 < ε →
      μHE[n] ((R.measure.support ∩ W) \ R.carrier) ≤ C * ε := by
    intro ε hε
    obtain ⟨O, hO, hAO, hOε⟩ :=
      Submission.dorag_sn_open_superset_measure_lt (n + k) R.measure _ hA0 hloc ε hε
    calc μHE[n] ((R.measure.support ∩ W) \ R.carrier) ≤ C * R.measure O :=
          hcomp R.measure _ O hO hAO hdens
      _ ≤ C * ε := by gcongr
  -- step 5: `C < ∞`, so `C ε_j → 0` along `ε_j = 1 / j`, and `Hⁿ(A) = 0`
  have hlim : Tendsto (fun j : ℕ => C * (j : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero (Or.inr hCtop)
  exact nonpos_iff_eq_zero.mp
    (ge_of_tendsto' hlim fun j => hbound _ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top j)))
/-- **Gram identity for the linear graph map** (Simon Ch. 2, 3.3 and Example 3.6(3): the area
Jacobian of a graph).  If `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` are linear isometries with
`⟨ιv, ι'w⟩ = 0` and `T : ℝⁿ → ℝᵏ` is linear, then `A = ι + ι' ∘ T` has `A* ∘ A = id + T* ∘ T`.
Pair both sides with `y`: `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩ = ⟨ιx, ιy⟩ + ⟨ι'Tx, ι'Ty⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`,
the cross terms vanishing by orthogonality, and `⟨(id + T*T)x, y⟩ = ⟨x, y⟩ + ⟨Tx, Ty⟩`. -/
theorem Submission.doraggt_graph_map_gram_identity : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (T : Euclid n →ₗ[ℝ] Euclid k), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LinearMap.adjoint (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) ∘ₗ (ι.toLinearMap + ι'.toLinearMap ∘ₗ T) = LinearMap.id + LinearMap.adjoint T ∘ₗ T := by
  intro n k ι ι' T h
  -- the other cross term vanishes too, by symmetry of the real inner product
  have h' : ∀ v w, inner ℝ (ι' w) (ι v) = 0 := fun v w => by rw [real_inner_comm]; exact h v w
  -- endomorphisms of `ℝⁿ` agree once `⟨S x, y⟩` agrees for all `x, y`
  refine LinearMap.ext fun x => ext_inner_right ℝ fun y => ?_
  -- `⟨A*Ax, y⟩ = ⟨Ax, Ay⟩` and `⟨T*Tx, y⟩ = ⟨Tx, Ty⟩`; expand, isometries keep `⟨·, ·⟩`
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left, LinearMap.add_apply,
    LinearMap.id_apply, LinearIsometry.coe_toLinearMap, inner_add_left, inner_add_right,
    LinearIsometry.inner_map_map, h, h', add_zero, zero_add]

/-- **Metric and Hausdorff-measure properties of a Lipschitz graph map** (Simon Ch. 2,
Theorem 1.8(i); Steps 0, 1 and 3 of the graph-tangent argument for Allard's graph).  Let
`ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with orthogonal ranges, `g` an
`L`-Lipschitz map and `Ψ(u) = b + ιu + ι'(g u)`.  Then (i) `|u − u'| ≤ |Ψ(u) − Ψ(u')|`
(Pythagoras), (ii) `Ψ` is `(1 + L)`-Lipschitz, (iii) `Ψ(ℝⁿ)` is closed (antilipschitz and
uniformly continuous on the complete `ℝⁿ`), (iv) `Hⁿ(Ψ(ℝⁿ) ∩ K) < ∞` for compact `K` (by (i),
`Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))`), (v) `Hⁿ(Ψ(N)) = 0` if `Lⁿ(N) = 0`; (iv) and (v) use
`Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Hⁿ(A)` and `Hⁿ = Lⁿ` on `ℝⁿ`. -/
theorem Submission.doraggt_lipschitz_graph_map_basics : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (b : Euclid (n + k)) (g : Euclid n → Euclid k) (L : NNReal), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L g → (∀ u u' : Euclid n, dist u u' ≤ dist (b + ι u + ι' (g u)) (b + ι u' + ι' (g u'))) ∧ LipschitzWith (1 + L) (fun u => b + ι u + ι' (g u)) ∧ IsClosed (Set.range fun u => b + ι u + ι' (g u)) ∧ (∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range (fun u => b + ι u + ι' (g u)) ∩ K) ≠ ∞) ∧ ∀ N : Set (Euclid n), volume N = 0 → μHE[n] ((fun u => b + ι u + ι' (g u)) '' N) = 0 := by
  intro n k ι ι' b g L horth hg
  set Ψ : Euclid n → Euclid (n + k) := fun u => b + ι u + ι' (g u) with hΨ
  -- Step 1: `Ψ(u) − Ψ(u') = ι(u − u') + ι'(g u − g u')`.
  have hdiff : ∀ u u', Ψ u - Ψ u' = ι (u - u') + ι' (g u - g u') := by
    intro u u'
    simp only [hΨ, map_sub]
    abel
  -- Step 2 (i): Pythagoras, `|Ψ(u) − Ψ(u')|² = |u − u'|² + |g u − g u'|²`.
  have hdist : ∀ u u', dist u u' ≤ dist (Ψ u) (Ψ u') := by
    intro u u'
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth (u - u') (g u - g u'))
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  -- Step 3 (ii): triangle inequality and the Lipschitz bound for `g`.
  have hlip : LipschitzWith (1 + L) Ψ := by
    refine LipschitzWith.of_dist_le_mul fun u u' => ?_
    rw [dist_eq_norm, dist_eq_norm, hdiff]
    calc ‖ι (u - u') + ι' (g u - g u')‖ ≤ ‖ι (u - u')‖ + ‖ι' (g u - g u')‖ := norm_add_le _ _
      _ = ‖u - u'‖ + dist (g u) (g u') := by
          rw [LinearIsometry.norm_map, LinearIsometry.norm_map, dist_eq_norm]
      _ ≤ ‖u - u'‖ + L * ‖u - u'‖ := by
          rw [← dist_eq_norm u u']
          gcongr
          exact hg.dist_le_mul u u'
      _ = ((1 + L : NNReal) : ℝ) * ‖u - u'‖ := by
          push_cast
          ring
  -- Step 4 (iii): `Ψ` is antilipschitz and uniformly continuous on the complete `ℝⁿ`.
  have hclosed : IsClosed (Set.range Ψ) := by
    have hanti : AntilipschitzWith 1 Ψ :=
      AntilipschitzWith.of_le_mul_dist fun u u' => by simpa using hdist u u'
    exact hanti.isClosed_range hlip.uniformContinuous
  -- Step 5: `Hⁿ(Ψ(A)) ≤ (1 + L)ⁿ Lⁿ(A)`, using `Hⁿ = Lⁿ` on `ℝⁿ`.
  have himage : ∀ A : Set (Euclid n),
      μHE[n] (Ψ '' A) ≤ ((1 + L : NNReal) : ℝ≥0∞) ^ n * volume A := by
    intro A
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hlip.lipschitzOnWith (s := A))
    rwa [EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at h
  -- Step 6 (iv): `Ψ(ℝⁿ) ∩ K ⊆ Ψ(B̄ₘ(0))` for `K ⊆ B̄ₘ(Ψ(0))`, by (i).
  have hfin : ∀ K : Set (Euclid (n + k)), IsCompact K → μHE[n] (Set.range Ψ ∩ K) ≠ ∞ := by
    intro K hK
    obtain ⟨m, hm⟩ := hK.isBounded.subset_closedBall (Ψ 0)
    have hsub : Set.range Ψ ∩ K ⊆ Ψ '' closedBall 0 m := by
      rintro _ ⟨⟨u, rfl⟩, huK⟩
      exact ⟨u, mem_closedBall.2 ((hdist u 0).trans (mem_closedBall.1 (hm huK))), rfl⟩
    refine ne_top_of_le_ne_top ?_ ((measure_mono hsub).trans (himage _))
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) measure_closedBall_lt_top.ne
  -- Step 7 (v): null sets go to null sets.
  have hnull : ∀ N : Set (Euclid n), volume N = 0 → μHE[n] (Ψ '' N) = 0 := by
    intro N hN
    exact le_zero_iff.1 ((himage N).trans (by rw [hN, mul_zero]))
  exact ⟨hdist, hlip, hclosed, hfin, hnull⟩

/-- **Blow-ups of a graph are graphs of difference quotients** (Simon Ch. 3, 1.4: the dilation
`η_{x,λ}(y) = λ⁻¹(y − x)`).  Let `Φ(u) = a + ιu + ι'f(u)`, `r ≠ 0` and
`f_{v,r}(w) = r⁻¹(f(v + rw) − f(v))`.  By linearity
`η_{Φ(v),r}(Φ(u)) = ι(r⁻¹(u − v)) + ι'(r⁻¹(f(u) − f(v)))`, so the bijection `u = v + rw` of `ℝⁿ`
gives `η_{Φ(v),r}(Φ(ℝⁿ)) = {ιw + ι'f_{v,r}(w) : w ∈ ℝⁿ}`.  Where `f` is differentiable at
`v + rw`, the chain rule gives `Df_{v,r}(w) = r⁻¹ Df(v + rw) ∘ (r id) = Df(v + rw)`; elsewhere
`f_{v,r}` is not differentiable at `w` either (`f(u) = f(v) + r f_{v,r}(r⁻¹(u − v))`), and both
`fderiv`s are `0`. -/
theorem Submission.doraggt_graph_blowup_rescaling : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (r : ℝ), r ≠ 0 → Poincare.SimonGMT.Chapter03.blowUpMap (a + ι v + ι' (f v)) r '' Set.range (fun u => a + ι u + ι' (f u)) = Set.range (fun w => ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) ∧ ∀ w : Euclid n, fderiv ℝ (fun w' => r⁻¹ • (f (v + r • w') - f v)) w = fderiv ℝ f (v + r • w) := by
  intro n k ι ι' a f v r hr
  refine ⟨?_, fun w => ?_⟩
  · -- Steps 2–3: reparametrize `ℝⁿ` by the bijection `w ↦ v + r • w`
    have he : Function.Surjective fun w : Euclid n => v + r • w := fun u =>
      ⟨r⁻¹ • (u - v), by simp only [smul_inv_smul₀ hr, add_sub_cancel]⟩
    rw [← Set.range_comp, ← he.range_comp]
    congr 1
    funext w
    -- Step 1: `η(Φ(v + r • w)) = r⁻¹ • (r • ι w + (ι' (f (v + r • w)) - ι' (f v)))`
    simp only [Function.comp_apply, Poincare.SimonGMT.Chapter03.blowUpMap, map_add, map_smul,
      map_sub]
    rw [show a + (ι v + r • ι w) + ι' (f (v + r • w)) - (a + ι v + ι' (f v)) =
        r • ι w + (ι' (f (v + r • w)) - ι' (f v)) by abel, smul_add, inv_smul_smul₀ hr]
  · by_cases hf : DifferentiableAt ℝ f (v + r • w)
    · -- Step 4: chain rule through `w' ↦ v + r • w'`, whose derivative is `r • id`
      have h : HasFDerivAt (fun w' => r⁻¹ • (f (v + r • w') - f v))
          (r⁻¹ • (fderiv ℝ f (v + r • w)).comp (r • ContinuousLinearMap.id ℝ (Euclid n))) w :=
        ((hf.hasFDerivAt.comp w (((hasFDerivAt_id w).const_smul r).const_add v)).sub_const
          (f v)).const_smul r⁻¹
      rw [h.fderiv, ContinuousLinearMap.comp_smulₛₗ, RingHom.id_apply,
        ContinuousLinearMap.comp_id, inv_smul_smul₀ hr]
    · -- Step 5: `u ↦ r⁻¹ • (u - v)` maps `v + r • w` to `w` and
      -- `f u = f v + r • f_{v,r} (r⁻¹ • (u - v))`, so `f_{v,r}` is not differentiable at `w`
      -- either; both derivatives are `0`
      rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt]
      intro hg
      have hw : r⁻¹ • (v + r • w - v) = w := by rw [add_sub_cancel_left, inv_smul_smul₀ hr]
      rw [← hw] at hg
      have hL : DifferentiableAt ℝ (fun u : Euclid n => r⁻¹ • (u - v)) (v + r • w) :=
        (differentiableAt_id.sub_const v).const_smul r⁻¹
      refine hf ((((hg.comp (v + r • w) hL).const_smul r).const_add (f v)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun u => ?_))
      simp only [Pi.smul_apply, Function.comp_apply, smul_inv_smul₀ hr, add_sub_cancel]

/-- Difference quotients `r⁻¹(f(v + rw) − f(v))` of a map differentiable at `v` converge to
`Df(v)w` uniformly on every closed ball `B̄_R(0)` as `r ↓ 0` (the `o(|h|)` estimate in the
weighted blow-up limit of the Allard graph step).  With `R' = max R 1`, pick `ρ > 0` such that
`|f(v + h) − f(v) − Df(v)h| ≤ ε|h|/(2R')` for `|h| < ρ`.  For `0 < r < ρ/R'` and `|w| ≤ R`,
`|rw| < ρ`, and linearity of `Df(v)` gives `|Df(v)w − r⁻¹(f(v + rw) − f(v))| ≤ ε|w|/(2R') < ε`. -/
theorem Submission.dorwbl_diff_quotient_tendstoUniformlyOn : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), DifferentiableAt ℝ f v → ∀ R : ℝ, TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => r⁻¹ • (f (v + r • w) - f v)) (fun w => fderiv ℝ f v w) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
  intro n k f v hf R
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hR : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hc : 0 < ε / (2 * max R 1) := by positivity
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hc)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / max R 1 by positivity)] with r hr w hw
  obtain ⟨hr0, hrρ⟩ := hr
  have hw' : ‖w‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 hw).trans (le_max_left R 1)
  have hrw : ‖r • w‖ = r * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
  -- `|rw| ≤ rR' < ρ`, so the little-o bound applies to `h = rw`
  have hbound := hsmall (show dist (r • w) 0 < ρ by
    rw [dist_zero_right, hrw]
    calc r * ‖w‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hw' hr0.le
      _ < ρ / max R 1 * max R 1 := mul_lt_mul_of_pos_right hrρ hR
      _ = ρ := div_mul_cancel₀ ρ hR.ne')
  -- `Df(v)w − r⁻¹(f(v + rw) − f(v)) = −r⁻¹(f(v + rw) − f(v) − Df(v)(rw))`
  have hid : fderiv ℝ f v w - r⁻¹ • (f (v + r • w) - f v) =
      -(r⁻¹ • (f (v + r • w) - f v - fderiv ℝ f v (r • w))) := by
    simp only [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    abel
  rw [dist_eq_norm, hid, norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
  calc r⁻¹ * ‖f (v + r • w) - f v - fderiv ℝ f v (r • w)‖
      ≤ r⁻¹ * (ε / (2 * max R 1) * ‖r • w‖) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr0.le)
    _ = ε / (2 * max R 1) * ‖w‖ := by
        rw [hrw]
        field_simp
    _ ≤ ε / (2 * max R 1) * max R 1 := mul_le_mul_of_nonneg_left hw' hc.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- Test-function step (Step 8) of the weighted graph blow-up limit used for the tangent planes of
Lipschitz graphs (cf. Simon Ch. 3, proof of 1.6 "⇒", where `∫_{η_{x,λ}(N)} f dHⁿ → ∫_{T_x N} f dHⁿ`).
If `f : ℝⁿ → ℝᵏ` is differentiable at `v` and `ψ ∈ C_c(ℝ^{n+k})`, then
`U(r) = ∫_{B̄_R(0)} |ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) − ψ(ιw + ι'(Df(v)w))| dw → 0` as `r ↓ 0`.
The difference quotients tend to `Df(v)` uniformly on `B̄_R(0)`; the isometry `ι'` carries this to
the graph maps, and `ψ` is uniformly continuous, so eventually the integrand is at most
`ε / (Lⁿ(B̄_R(0)) + 1)` on the ball, which has finite measure.  Continuity of `f` is not used. -/
theorem Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (v : Euclid n) (ψ : Euclid (n + k) → ℝ), Continuous f → DifferentiableAt ℝ f v → Continuous ψ → HasCompactSupport ψ → ∀ R : ℝ, Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) (𝓝[>] 0) (𝓝 0) := by
  intro n k ι ι' f v ψ _hf hfv hψ hψc R
  -- the graph maps `Φ_r w = ι w + ι' (f_{v,r} w)` tend to `Φ w = ι w + ι' (Df(v) w)` uniformly on
  -- `B̄_R(0)`: `dist (Φ w) (Φ_r w) = dist (Df(v) w) (f_{v,r} w)` since `ι'` is an isometry
  have hΦ : TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => ι w + ι' (r⁻¹ • (f (v + r • w) - f v)))
      (fun w => ι w + ι' (fderiv ℝ f v w)) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
    have h := Submission.dorwbl_diff_quotient_tendstoUniformlyOn n k f v hfv R
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    filter_upwards [h ε hε] with r hr w hw
    simp only [dist_add_left, LinearIsometry.dist_map]
    exact hr w hw
  -- `ψ` is uniformly continuous (continuous with compact support), so `ψ ∘ Φ_r → ψ ∘ Φ` uniformly
  have hψΦ := (hψc.uniformContinuous_of_continuous hψ).comp_tendstoUniformlyOn hΦ
  rw [Metric.tendstoUniformlyOn_iff] at hψΦ
  have hB : volume (closedBall (0 : Euclid n) R) < ∞ := measure_closedBall_lt_top
  have hV : 0 ≤ volume.real (closedBall (0 : Euclid n) R) := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- with `η = ε / (Lⁿ(B̄_R(0)) + 1)`, eventually `|U(r)| ≤ η Lⁿ(B̄_R(0)) < ε`
  have hη : 0 < ε / (volume.real (closedBall (0 : Euclid n) R) + 1) := div_pos hε (by linarith)
  filter_upwards [hψΦ _ hη] with r hr
  rw [dist_zero_right]
  refine (norm_setIntegral_le_of_norm_le_const
    (C := ε / (volume.real (closedBall (0 : Euclid n) R) + 1)) hB fun w hw => ?_).trans_lt ?_
  · have h1 := hr w hw
    simp only [Function.comp_apply, Real.dist_eq] at h1
    rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
    exact h1.le
  · rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith

/-- Weighted blow-up limit at one good point `v`.  Let `f` be continuous and differentiable at
`v`, `G` Borel with `|G| ≤ C`, and `∫_{B_R(0)} |G(v + r w) - G(v)| dw → 0` as `r ↓ 0` for every
`R > 0`.  With `Φ_r w = ι w + ι'(r⁻¹(f(v + r w) - f(v)))` and `Φ w = ι w + ι'(Df(v) w)`, every
continuous compactly supported `ψ` has `∫ ψ(Φ_r w) G(v + r w) dw → G(v) ∫ ψ(Φ w) dw`.
Orthogonality gives `‖w‖ ≤ ‖ι w + ι' u‖`, so both integrands vanish off `B_R(0)` once
`spt ψ ⊆ B_R(0)`; there they differ by at most `C |ψ ∘ Φ_r - ψ ∘ Φ| + M |G(v + r ·) - G(v)|`
(`|ψ| ≤ M`), whose integral tends to `0`. -/
theorem Submission.dorwbl_weighted_blowup_tendsto_at_point : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (G : Euclid n → ℝ) (C : ℝ) (v : Euclid n), (∀ x y, inner ℝ (ι x) (ι' y) = 0) → Continuous f → Measurable G → (∀ u, |G u| ≤ C) → DifferentiableAt ℝ f v → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v|) (𝓝[>] 0) (𝓝 0)) → ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f G C v horth hf hG hGC hdiff hleb ψ hψ hψc
  -- `|ψ| ≤ M`, and `tsupport ψ ⊆ closedBall 0 R₀` with `R₀ ≤ R`, `0 < R`.
  obtain ⟨M, hM⟩ := hψc.exists_bound_of_continuous hψ
  have hψM : ∀ y, |ψ y| ≤ M := fun y => by rw [← Real.norm_eq_abs]; exact hM y
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hψM 0)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hGC 0)
  obtain ⟨R₀, hR₀⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Euclid (n + k))
  obtain ⟨R, hRpos, hR₀R⟩ : ∃ R : ℝ, 0 < R ∧ R₀ ≤ R :=
    ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), le_max_left _ _⟩
  have hBfin : volume (closedBall (0 : Euclid n) R) ≠ ∞ := measure_closedBall_lt_top.ne
  -- Pythagoras: `‖w‖ ≤ ‖ι w + ι' u‖`.
  have hpyth : ∀ (w : Euclid n) (u : Euclid k), ‖w‖ ≤ ‖ι w + ι' u‖ := by
    intro w u
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth w u)
    rw [LinearIsometry.norm_map, LinearIsometry.norm_map] at h
    refine (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).2 ?_
    rw [h]
    exact le_add_of_nonneg_right (mul_self_nonneg _)
  -- Both integrands vanish off `closedBall 0 R`.
  have hvanish : ∀ w : Euclid n, w ∉ closedBall (0 : Euclid n) R → ∀ u : Euclid k,
      ψ (ι w + ι' u) = 0 := by
    intro w hw u
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hw
    have h1 := hR₀ hmem
    rw [mem_closedBall_zero_iff] at h1 ⊢
    exact (hpyth w u).trans (h1.trans hR₀R)
  -- `C ∫_{B_R} |ψ ∘ Φ_r - ψ ∘ Φ| + M ∫_{B_R} |G(v + r ·) - G(v)| → 0`.
  have hU := Submission.dorwbl_test_fn_diff_quotient_integral_tendsto_zero n k ι ι' f v ψ hf
    hdiff hψ hψc R
  have hV := hleb R hRpos
  have hlim := (hU.const_mul C).add (hV.const_mul M)
  rw [mul_zero, mul_zero, add_zero] at hlim
  -- Pointwise: `a x - G(v) b = (a - b) x + b (x - G(v))`.
  have hpt : ∀ a b x : ℝ, |b| ≤ M → |x| ≤ C →
      |a * x - G v * b| ≤ C * |a - b| + M * |x - G v| := by
    intro a b x hb hx
    calc |a * x - G v * b| = |(a - b) * x + b * (x - G v)| := by congr 1; ring
      _ ≤ |(a - b) * x| + |b * (x - G v)| := abs_add_le _ _
      _ = |a - b| * |x| + |b| * |x - G v| := by rw [abs_mul, abs_mul]
      _ ≤ |a - b| * C + M * |x - G v| :=
        add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hb (abs_nonneg _))
      _ = C * |a - b| + M * |x - G v| := by ring
  -- For every `r`, the error is bounded by the quantity in `hlim`.
  have key : ∀ r : ℝ,
      ‖(∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) -
          G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))‖ ≤
        C * (∫ w in closedBall (0 : Euclid n) R,
            |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|) +
          M * ∫ w in closedBall (0 : Euclid n) R, |G (v + r • w) - G v| := by
    intro r
    have hcr : Continuous fun w : Euclid n => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) := by
      fun_prop
    have hc : Continuous fun w : Euclid n => ψ (ι w + ι' (fderiv ℝ f v w)) := by fun_prop
    have hGr : Measurable fun w : Euclid n => G (v + r • w) :=
      hG.comp (by fun_prop : Continuous fun w : Euclid n => v + r • w).measurable
    have ha : IntegrableOn
        (fun w => ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M * C) hBfin
        (hcr.measurable.mul hGr).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hψM _) (hGC _) (abs_nonneg _) hM0)
    have hb : IntegrableOn (fun w => G v * ψ (ι w + ι' (fderiv ℝ f v w)))
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C * M) hBfin
        (hc.measurable.const_mul (G v)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hGC _) (hψM _) (abs_nonneg _) hC0)
    have hΔ : IntegrableOn
        (fun w => |ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) - ψ (ι w + ι' (fderiv ℝ f v w))|)
        (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := M + M) hBfin
        (continuous_abs.measurable.comp (hcr.measurable.sub hc.measurable)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hψM _) (hψM _)))
    have hg : IntegrableOn (fun w => |G (v + r • w) - G v|) (closedBall (0 : Euclid n) R) :=
      Measure.integrableOn_of_bounded (M := C + C) hBfin
        (continuous_abs.measurable.comp (hGr.sub measurable_const)).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_abs]
          exact (abs_sub _ _).trans (add_le_add (hGC _) (hGC _)))
    have hA : (∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) =
        ∫ w in closedBall (0 : Euclid n) R,
          ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, zero_mul]
    have hB : G v * (∫ w, ψ (ι w + ι' (fderiv ℝ f v w))) =
        ∫ w in closedBall (0 : Euclid n) R, G v * ψ (ι w + ι' (fderiv ℝ f v w)) := by
      rw [← integral_const_mul]
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro w hw
      rw [hvanish w hw, mul_zero]
    rw [hA, hB, ← integral_sub ha hb, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hΔ.const_mul C) (hg.const_mul M)]
    refine norm_integral_le_of_norm_le ((hΔ.const_mul C).add (hg.const_mul M))
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs]
    exact hpt _ _ _ (hψM _) (hGC _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun r => norm_nonneg _) key hlim
/-- **Lebesgue points, rescaled** (Simon Ch. 1, Corollary 3.17, in the Lebesgue-point form of
Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`): if `g : ℝⁿ → ℝ` is locally
`Lⁿ`-integrable, then for `Lⁿ`-a.e. `v` and every `R > 0`, `∫_{B_R(0)} |g(v + rw) − g(v)| dw → 0`
as `r ↓ 0`.  The substitutions `u = rw`, `y = v + u` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))` give
`∫_{B_R(0)} |g(v + rw) − g(v)| dw = Lⁿ(B_R(0)) ⨍_{B_{rR}(v)} |g − g(v)|`, and these averages tend
to `0` at every Lebesgue point `v` of `g`. -/
theorem Submission.doraggt_ae_rescaled_lebesgue_point : ∀ (n : ℕ) (g : Euclid n → ℝ), LocallyIntegrable g volume → ∀ᵐ v ∂(volume : Measure (Euclid n)), ∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v|) (𝓝[>] 0) (𝓝 0) := by
  intro n g hg
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub
    (volume : Measure (Euclid n)) hg 1] with v hv R hR
  -- Lebesgue point: the averages over `closedBall v (r * R)` tend to `0` as `r ↓ 0`
  have hδ : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  have hA : Tendsto (fun r : ℝ => ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    have h := hv (fun _ => v) (fun r : ℝ => r * R) hδ (by
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      rw [one_mul]
      exact mem_closedBall_self (mul_pos hr hR).le)
    simpa only [Real.norm_eq_abs] using h
  -- change of variables `u = r • w` (dilation), `y = v + u` (translation)
  have key : ∀ r : ℝ, 0 < r → ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
      volume.real (closedBall (0 : Euclid n) R) * ⨍ y in closedBall v (r * R), |g y - g v| := by
    intro r hr
    have h1 : ∫ w in closedBall (0 : Euclid n) R, |g (v + r • w) - g v| =
        (r ^ n)⁻¹ • ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| := by
      rw [Measure.setIntegral_comp_smul_of_pos (volume : Measure (Euclid n))
        (fun u => |g (v + u) - g v|) _ hr, _root_.smul_closedBall _ _ hR.le, smul_zero,
        Real.norm_of_nonneg hr.le, finrank_euclideanSpace_fin]
    have h2 : ∫ u in closedBall (0 : Euclid n) (r * R), |g (v + u) - g v| =
        ∫ y in closedBall v (r * R), |g y - g v| := by
      have h := MeasurePreserving.setIntegral_preimage_emb
        (measurePreserving_add_left (volume : Measure (Euclid n)) v)
        (measurableEmbedding_addLeft v) (fun y => |g y - g v|) (closedBall v (r * R))
      simpa using h
    -- `∫_{B_{rR}(v)} = Lⁿ(B_{rR}(v)) ⨍_{B_{rR}(v)}` and `Lⁿ(B_{rR}(v)) = rⁿ Lⁿ(B_R(0))`
    have h3 := measure_smul_setAverage (μ := (volume : Measure (Euclid n)))
      (fun y => |g y - g v|) (s := closedBall v (r * R)) measure_closedBall_lt_top.ne
    rw [h1, h2, ← h3, smul_eq_mul, smul_eq_mul,
      Measure.addHaar_real_closedBall _ _ (mul_pos hr hR).le,
      Measure.addHaar_real_closedBall _ _ hR.le, finrank_euclideanSpace_fin, mul_pow]
    have hrn : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
    field_simp
  have hlim : Tendsto (fun r : ℝ => volume.real (closedBall (0 : Euclid n) R) *
      ⨍ y in closedBall v (r * R), |g y - g v|) (𝓝[>] 0) (𝓝 0) := by
    simpa using hA.const_mul (volume.real (closedBall (0 : Euclid n) R))
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact (key r hr).symm

/-- **Weighted blow-ups of a Lipschitz graph** (Simon Ch. 2, Theorem 1.4 (Rademacher) and Ch. 1,
Corollary 3.17).  Let `ι : ℝⁿ → ℝ^{n+k}` and `ι' : ℝᵏ → ℝ^{n+k}` be linear isometries with
orthogonal ranges, `f : ℝⁿ → ℝᵏ` Lipschitz and `G : ℝⁿ → ℝ` measurable with `|G| ≤ C`.  Then for
`Lⁿ`-a.e. `v`, `f` is differentiable at `v` and, for every continuous compactly supported `ψ`,
`∫ ψ(ιw + ι'(r⁻¹(f(v + rw) − f(v)))) G(v + rw) dw → G(v) ∫ ψ(ιw + ι'(Df(v)w)) dw` as `r ↓ 0`.
The bounded measurable weight `G` is locally integrable, so Rademacher's theorem and the rescaled
Lebesgue-point property of `G` hold simultaneously at a.e. `v`; at every such `v` the convergence
is the blow-up limit at a differentiability point that is a rescaled Lebesgue point of `G`. -/
theorem Submission.doraggt_ae_weighted_graph_blowup_tendsto : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal) (G : Euclid n → ℝ) (C : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → Measurable G → (∀ u, |G u| ≤ C) → ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧ ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ → Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w)) (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)))) := by
  intro n k ι ι' f L G C horth hf hG hGC
  -- `G` is bounded and measurable, hence integrable on every compact set
  have hloc : LocallyIntegrable G volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    exact Measure.integrableOn_of_bounded hK.measure_lt_top.ne hG.aestronglyMeasurable (M := C)
      (Eventually.of_forall fun u => (Real.norm_eq_abs (G u)).trans_le (hGC u))
  -- Rademacher and the rescaled Lebesgue-point property of `G` hold simultaneously a.e.
  filter_upwards [hf.ae_differentiableAt (μ := volume),
    Submission.doraggt_ae_rescaled_lebesgue_point n G hloc] with v hv hleb
  -- at such `v`, the blow-up limit holds for every test function `ψ`
  exact ⟨hv, Submission.dorwbl_weighted_blowup_tendsto_at_point n k ι ι' f G C v horth
    hf.continuous hG hGC hv hleb⟩

/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in an open set**
(Simon Ch. 1, 3.6 and Remark 3.7(2); chapter-01.txt lines 700–711).  If `U ⊆ ℝᴾ` is open and
`S ⊆ ℝᴾ` is Borel with `Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e.
`x ∈ U \ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B(y, r_y)` with
`B̄(y, r_y) ⊆ U` cover `U` (Lindelöf); the upper density theorem applies to each piece
`S ∩ B(y, r_y)`, of finite measure, and the piece agrees with `S` on small balls about
`x ∈ B(y, r_y)`. -/
theorem Submission.doraggt_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U` (Lindelöf).
  have hrad : ∀ y ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall y r ⊆ U := by
    intro y hy
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hrad
  obtain ⟨D, hDU, hDc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    (fun y hy => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y (hr0 y hy)))
  -- Steps 2 and 3, the upper density theorem for each finite-measure piece `S ∩ B(y, r y)`,
  -- simultaneously for the countably many `y ∈ D`.
  have hae : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] ((S ∩ ball y (r y)) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    refine Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball) ?_
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
  -- Step 4, near `x ∈ B(y, r y)` the piece and `S` agree.
  filter_upwards [hae] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcover hxU)
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεball)]
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
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
/-- Changing a set by parts of vanishing `n`-density at `x` does not change its approximate
tangent spaces at `x` (Simon Ch. 3, Definition 1.4 and Remark 1.5(2); proof of 3.1.6).  For
`f ∈ C_c(ℝᴾ)` with `|f| ≤ C`, `f = 0` off `B̄_R(0)` and `0 < r < r₀/R`, comparing both blow-up
integrals with the one over `η_{x,r}(A ∩ B)` gives `|∫_{η_{x,r}(A)} f dHⁿ − ∫_{η_{x,r}(B)} f dHⁿ| ≤
C Hⁿ(η_{x,r}(A \ B) ∩ B̄_R(0)) + C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`, and
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`. -/
theorem Submission.doraggt_approxTangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → 0 < r₀ → μHE[n] (A ∩ closedBall x r₀) ≠ ∞ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((A \ B) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n A B x r₀ hA hB hr₀ hAfin hBfin hAB hBA
  -- Step 1: it suffices that `∫_{η_r(A)} f − ∫_{η_r(B)} f → 0` for every `f ∈ C_c`
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n A B x fun f => ?_
  -- Step 2: `|f| ≤ C`, and `f = 0` off `B̄_R(0)` for some `R > 0`
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R, hR, hzero⟩ : ∃ R : ℝ, 0 < R ∧
      ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    obtain ⟨R₁, hR₁⟩ := (isBounded_iff_subset_closedBall (0 : Euclid P)).mp
      f.hasCompactSupport.isCompact.isBounded
    exact ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun y hy => image_eq_zero_of_notMem_tsupport
      fun h => hy (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))⟩
  -- Step 3: for `0 < r < r₀ / R`, `Hⁿ(η_r(S) ∩ B̄_R(0)) ≤ r⁻ⁿ Hⁿ(S ∩ B̄_{r₀}(x)) < ∞`
  have hfin : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall x r₀) ≠ ∞ → ∀ r ∈ Ioo 0 (r₀ / R),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) ≠ ∞ := by
    intro S hS r hr
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr.1).ne'))
      (ne_top_of_le_ne_top hS (measure_mono (inter_subset_inter_right _
        (closedBall_subset_closedBall ((lt_div_iff₀ hR).mp hr.2).le))))
  -- Step 4: `C Hⁿ(η_r(S) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x)) → 0` for `S = A \ B`, `B \ A`
  have herr : ∀ S : Set (Euclid P),
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun r : ℝ => C *
        (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R)).toReal)
        (𝓝[>] 0) (𝓝 0) := by
    intro S hS
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ => μHE[n] (S ∩ closedBall x ρ)) R hR hS)).const_mul C
    rw [ENNReal.toReal_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    rw [Function.comp_apply, Submission.regcomp_atl_blowUp_measure_scaling P n x r R S hr]
  -- Step 5: for `0 < r < r₀ / R`, compare both integrals with the one over `η_r(A ∩ B)`
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]‖ ≤
        C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A \ B) ∩
            closedBall 0 R)).toReal +
          C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩
            closedBall 0 R)).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
    have hA' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) A x r R C f
      f.continuous (hA.inter hB) hA inter_subset_left hr.1 (hfin A hAfin r hr) hC hzero
    have hB' := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n (A ∩ B) B x r R C f
      f.continuous (hA.inter hB) hB inter_subset_right hr.1 (hfin B hBfin r hr) hC hzero
    rw [Set.sdiff_self_inter] at hA'
    rw [Set.sdiff_inter_self_eq_sdiff] at hB'
    rw [← sub_sub_sub_cancel_right _ _
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (A ∩ B), f y ∂μHE[n])]
    exact (norm_sub_le _ _).trans (add_le_add hA' hB')
  -- Step 6: squeeze
  have hlim := (herr _ hAB).add (herr _ hBA)
  rw [add_zero] at hlim
  exact squeeze_zero_norm' hle hlim

/-- **Approximate tangent planes of two locally finite sets agree a.e. on their overlap** (Simon
Ch. 3, Remark 1.5(2) and the proof of Theorem 1.6 "⇒", chapter-03.txt lines 86–90 and 113–146,
stated symmetrically for two sets).  Let `W ⊆ ℝᴾ` be open and `A`, `B` Borel with `Hⁿ(A ∩ K)` and
`Hⁿ(B ∩ K)` finite for every compact `K ⊆ W`.  By the upper density theorem the densities of
`A ∖ B` and `B ∖ A` vanish at `Hⁿ`-a.e. `x ∈ W ∩ A ∩ B`; a closed ball about such `x` inside `W`
has finite measure in `A` and in `B`, so `A` and `B` have the same approximate tangent planes at
`x`. -/
theorem Submission.doraggt_ae_approxTangent_transfer : ∀ (P n : ℕ) (W A B : Set (Euclid P)), IsOpen W → MeasurableSet A → MeasurableSet B → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (A ∩ K) ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ W → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ W → x ∈ A → x ∈ B → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q := by
  intro P n W A B hW hA hB hAfin hBfin
  -- Step 1, the densities of `A ∖ B` and `B ∖ A` vanish `Hⁿ`-a.e. on `W` off these sets.
  have hAB := Submission.doraggt_local_density_zero P n W (A \ B) hW (hA.diff hB)
    fun K hK hKW => ne_top_of_le_ne_top (hAfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  have hBA := Submission.doraggt_local_density_zero P n W (B \ A) hW (hB.diff hA)
    fun K hK hKW => ne_top_of_le_ne_top (hBfin K hK hKW)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 2, at such `x ∈ W ∩ A ∩ B`, `x ∉ A ∖ B` and `x ∉ B ∖ A`, so both densities vanish.
  filter_upwards [hAB, hBA] with x hxAB hxBA hxW hxA hxB
  -- Step 3, `B̄(x, ε/2) ⊆ B(x, ε) ⊆ W` is compact, so `A` and `B` have finite measure in it.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
  have hsub : closedBall x (ε / 2) ⊆ W := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Step 4, the approximate tangent planes of `A` and `B` at `x` agree.
  exact Submission.doraggt_approxTangent_iff_of_density_zero P n A B x (ε / 2) hA hB
    (half_pos hε) (hAfin _ (isCompact_closedBall x (ε / 2)) hsub)
    (hBfin _ (isCompact_closedBall x (ε / 2)) hsub) (hxAB hxW fun h => h.2 hxB)
    (hxBA hxW fun h => h.2 hxA)

/-- **The approximate tangent plane of a Lipschitz graph, transferred to an integer multiplicity
carrier** (Simon Ch. 3, Definition 1.4, Remarks 1.5(1)–(2) and the proof of Theorem 1.6 "⇒";
Ch. 2, area formula 3.2–3.5 and Example 3.6(3); Ch. 1, Upper Density Theorem 3.6).
Let `Φ(u) = a + ιu + ι'(f u)`, `F = Φ(ℝⁿ)` and `P_v = range (ι + ι' ∘ Df(v))`.  With the graph
Jacobian `Ĵ(T) = normDet (ι + ι' ∘ T)` (continuous in `T`, SimonGMT `continuous_normDet`), the
injective Lipschitz area formula (SimonGMT `injective_area_formula_lipschitz`, Rademacher) gives
`Hⁿ⌞(graph of g through 0) = (w ↦ ιw + ι'(g w))_# (Ĵ(Dg) Lⁿ)` for Lipschitz `g`.  Applied to the
blow-ups `η_{Φ(v),r}(F)`, graphs of the difference quotients `f_{v,r}` with `Df_{v,r}(w) =
Df(v + rw)`, and to `P_v`, the graph of `Df(v)`, this turns the weighted blow-up limit for the
bounded measurable weight `G = Ĵ ∘ Df` into `HasApproximateTangentSpaceAt n F (Φ v) P_v` for
`Lⁿ`-a.e. `v`.  The exceptional parameters have `Hⁿ`-null image, and the approximate tangent
planes of `F` and of the carrier `M` agree `Hⁿ`-a.e. on `M ∩ F ∩ W` (both are Borel and locally
`Hⁿ`-finite in `W`, `θ ≥ 1` on `M`); uniqueness of the approximate tangent plane concludes. -/
theorem Submission.dorag_lipschitz_graph_approxTangent : ∀ (n k : ℕ), 0 < n → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (a : Euclid (n + k)) (f : Euclid n → Euclid k) (L : NNReal), IsOpen W → W ⊆ U → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → LipschitzWith L f → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = a + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
  intro n k _ U W R ι ι' a f L hW hWU horth hf
  -- Step 0: the graph Jacobian `Ĵ(T) = normDet (ι + ι' ∘ T)` is continuous in `T`.
  obtain ⟨Jh, hJh_def⟩ : ∃ Jh : (Euclid n →L[ℝ] Euclid k) → ℝ, ∀ T, Jh T =
      ((ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp T :
        Euclid n →L[ℝ] Euclid (n + k)) : Euclid n →ₗ[ℝ] Euclid (n + k)).normDet :=
    ⟨_, fun _ => rfl⟩
  have hJh : Continuous Jh := by
    rw [show Jh = fun T => ((ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp T :
        Euclid n →L[ℝ] Euclid (n + k)) : Euclid n →ₗ[ℝ] Euclid (n + k)).normDet from
      funext hJh_def]
    exact Poincare.SimonGMT.Chapter02.continuous_normDet.comp
      (continuous_const.add (continuous_const.clm_comp continuous_id))
  have hJh0 : ∀ T, 0 ≤ Jh T := fun T => by
    rw [hJh_def]
    exact LinearMap.normDet_nonneg _
  -- Step 2, area formula (Simon Ch. 2, 3.2–3.5) for a Lipschitz graph through the origin, as an
  -- identity of measures `Hⁿ⌞(graph g) = (w ↦ ιw + ι'(g w))_# (Ĵ(Dg) Lⁿ)` (Rademacher).
  have area : ∀ (g : Euclid n → Euclid k) (K : NNReal), LipschitzWith K g →
      (μHE[n] : Measure (Euclid (n + k))).restrict (Set.range fun u => ι u + ι' (g u)) =
        Measure.map (fun u => ι u + ι' (g u)) ((volume : Measure (Euclid n)).withDensity
          fun u => ENNReal.ofReal (Jh (fderiv ℝ g u))) := by
    intro g K hg
    obtain ⟨h1, h2, -, -, -⟩ :=
      Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 g K horth hg
    simp only [zero_add] at h1 h2
    have hinj : Injective fun u => ι u + ι' (g u) := fun u u' h => by
      have h' : ι u + ι' (g u) = ι u' + ι' (g u') := h
      have h3 := h1 u u'
      rw [h', dist_self] at h3
      exact dist_le_zero.1 h3
    have hmeas : Measurable fun u => ι u + ι' (g u) := h2.continuous.measurable
    ext S hS
    rw [Measure.restrict_apply hS, Measure.map_apply hmeas hS, withDensity_apply _ (hmeas hS),
      ← Set.image_preimage_eq_inter_range]
    have key :=
      Poincare.SimonGMT.Chapter02.injective_area_formula_lipschitz h2 (hmeas hS) hinj.injOn
    rw [finrank_euclideanSpace_fin] at key
    rw [key]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hg.ae_differentiableAt (μ := volume)] with u hu
    have hd : HasFDerivAt (fun u => ι u + ι' (g u))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ g u)) u :=
      ι.toContinuousLinearMap.hasFDerivAt.add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp u hu.hasFDerivAt)
    rw [Poincare.SimonGMT.Chapter02.areaJacobianAt_eq_normDet, hd.fderiv, hJh_def]
  -- Hence `∫_{graph g} ψ dHⁿ = ∫ ψ(ιw + ι'(g w)) Ĵ(Dg(w)) dw` for every continuous `ψ`.
  have areaInt : ∀ (g : Euclid n → Euclid k) (K : NNReal), LipschitzWith K g →
      ∀ ψ : Euclid (n + k) → ℝ, Continuous ψ →
        ∫ y in Set.range (fun u => ι u + ι' (g u)), ψ y ∂μHE[n] =
          ∫ w, ψ (ι w + ι' (g w)) * Jh (fderiv ℝ g w) := by
    intro g K hg ψ hψ
    have h2 := (Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 g K horth hg).2.1
    simp only [zero_add] at h2
    have hJm : Measurable fun u => ENNReal.ofReal (Jh (fderiv ℝ g u)) :=
      (hJh.measurable.comp (measurable_fderiv ℝ g)).ennreal_ofReal
    rw [area g K hg, integral_map h2.continuous.measurable.aemeasurable hψ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hJm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (hJh0 _), mul_comm]
  -- Step 1: the weight `G = Ĵ ∘ Df` is measurable and bounded (`‖Df‖ ≤ L`).
  obtain ⟨G, hG⟩ : ∃ G : Euclid n → ℝ, ∀ u, G u = Jh (fderiv ℝ f u) :=
    ⟨fun u => Jh (fderiv ℝ f u), fun _ => rfl⟩
  have hGm : Measurable G := by
    rw [show G = fun u => Jh (fderiv ℝ f u) from funext hG]
    exact hJh.measurable.comp (measurable_fderiv ℝ f)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : Euclid n →L[ℝ] Euclid k) L).exists_bound_of_continuousOn
      hJh.continuousOn
  have hGC : ∀ u, |G u| ≤ C := fun u => by
    rw [hG, ← Real.norm_eq_abs]
    exact hC _ (mem_closedBall_zero_iff.2 (norm_fderiv_le_of_lipschitz ℝ hf))
  -- Step 2, blow-up limit: at good parameters `v`, `F` has approximate tangent plane `P_v`
  -- at `Φ(v)`.
  have tangentF : ∀ v : Euclid n, (∀ ψ : Euclid (n + k) → ℝ, Continuous ψ → HasCompactSupport ψ →
        Tendsto (fun r : ℝ => ∫ w, ψ (ι w + ι' (r⁻¹ • (f (v + r • w) - f v))) * G (v + r • w))
          (𝓝[>] 0) (𝓝 (G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w))))) →
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) := by
    intro v hlim
    have hD1 := (Submission.doraggt_lipschitz_graph_map_basics n k ι ι' 0 (fderiv ℝ f v)
      ‖fderiv ℝ f v‖₊ horth (fderiv ℝ f v).lipschitzWith).1
    simp only [zero_add] at hD1
    have hPset : ((LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ
        (fderiv ℝ f v).toLinearMap) : Submodule ℝ (Euclid (n + k))) : Set (Euclid (n + k))) =
        Set.range fun u => ι u + ι' (fderiv ℝ f v u) := by
      rw [LinearMap.coe_range]
      rfl
    refine ⟨?_, fun ψ => ?_⟩
    · rw [LinearMap.finrank_range_of_inj, finrank_euclideanSpace_fin]
      intro u u' h
      have h' : ι u + ι' (fderiv ℝ f v u) = ι u' + ι' (fderiv ℝ f v u') := h
      have h3 := hD1 u u'
      rw [h', dist_self] at h3
      exact dist_le_zero.1 h3
    · have hval : ∫ y in ((LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ
          (fderiv ℝ f v).toLinearMap) : Submodule ℝ (Euclid (n + k))) : Set (Euclid (n + k))),
            ψ y ∂μHE[n] = G v * ∫ w, ψ (ι w + ι' (fderiv ℝ f v w)) := by
        rw [hPset, areaInt _ _ (fderiv ℝ f v).lipschitzWith ψ (map_continuous ψ)]
        simp only [ContinuousLinearMap.fderiv]
        rw [integral_mul_const, hG, mul_comm]
      rw [hval]
      refine (hlim ψ (map_continuous ψ) ψ.hasCompactSupport).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      have hfr : LipschitzWith L fun w' => r⁻¹ • (f (v + r • w') - f v) := by
        refine LipschitzWith.of_dist_le_mul fun w w' => ?_
        rw [dist_smul₀, dist_sub_right, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        calc r⁻¹ * dist (f (v + r • w)) (f (v + r • w'))
            ≤ r⁻¹ * (L * dist (v + r • w) (v + r • w')) :=
              mul_le_mul_of_nonneg_left (hf.dist_le_mul _ _) (inv_nonneg.2 hr.le)
          _ = L * dist w w' := by
              rw [dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le, mul_left_comm,
                inv_mul_cancel_left₀ hr.ne']
      obtain ⟨hset, hder⟩ := Submission.doraggt_graph_blowup_rescaling n k ι ι' a f v r hr.ne'
      rw [hset, areaInt _ L hfr ψ (map_continuous ψ)]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [hder w, hG]
  -- Steps 1–2: Rademacher and the weighted blow-up limit hold at `Lⁿ`-a.e. parameter.
  have hgood :=
    Submission.doraggt_ae_weighted_graph_blowup_tendsto n k ι ι' f L G C horth hf hGm hGC
  have hgood' : ∀ᵐ v ∂(volume : Measure (Euclid n)), DifferentiableAt ℝ f v ∧
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) :=
    hgood.mono fun v hv => ⟨hv.1, tangentF v hv.2⟩
  -- Steps 1 and 3: the bad parameters have `Hⁿ`-null image; `M` and `F` are Borel and locally
  -- `Hⁿ`-finite in `W` (`θ ≥ 1` on `M`), so their approximate tangent planes agree a.e. (Step 4).
  obtain ⟨-, -, hFclosed, hFfin, hnull⟩ :=
    Submission.doraggt_lipschitz_graph_map_basics n k ι ι' a f L horth hf
  have hN := hnull _ (ae_iff.1 hgood')
  have hMfin : ∀ K : Set (Euclid (n + k)), IsCompact K → K ⊆ W → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKW
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK (hKW.trans hWU)) ?_
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (R.measurableSet_carrier.inter hK.isClosed.measurableSet)
      fun x hx => ?_
    exact Nat.one_le_cast.2 (R.mult_pos x hx.1)
  have htransfer := Submission.doraggt_ae_approxTangent_transfer (n + k) n W R.carrier
    (Set.range fun u => a + ι u + ι' (f u)) hW R.measurableSet_carrier hFclosed.measurableSet
    hMfin (fun K hK _ => hFfin K hK)
  -- Step 5: conclusion, by uniqueness of the approximate tangent plane (Remark 1.5(1)).
  rw [ae_restrict_iff' (R.measurableSet_carrier.inter hW.measurableSet)]
  filter_upwards [htransfer, measure_eq_zero_iff_ae_notMem.1 hN] with x hxT hxN
  rintro ⟨hxM, hxW⟩ v rfl
  obtain ⟨hdiff, hF⟩ : DifferentiableAt ℝ f v ∧
      HasApproximateTangentSpaceAt n (Set.range fun u => a + ι u + ι' (f u)) (a + ι v + ι' (f v))
        (LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) := by
    by_contra hcon
    exact hxN ⟨v, hcon, rfl⟩
  have hM := (hxT hxW hxM ⟨v, rfl⟩ _).2 hF
  have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier (a + ι v + ι' (f v)) Q := ⟨_, hM⟩
  refine ⟨hdiff, ?_⟩
  rw [approxTangentPlane, dite_eq_left hex]
  exact hex.choose_spec.unique hM
/-- **Tilt-excess is controlled by height** (Simon Ch. 5, Lemma 2.1, with `|H| ≤ κ`).  With
`p_S^⊥ = I − p_S` and `C = 146`,
`∫_{B_{r/2}(ξ)} |p_{TₓM} − p_S|² dμ ≤ C (r⁻² ∫_{B_r(ξ)} |p_S^⊥(x − ξ)|² dμ + κ²r² μ(B_r(ξ)))`.
Take the radial cut-off `ζ` (`ζ = 1` on `B_{r/2}(ξ)`, `tsupport ζ ⊆ B_r(ξ)`, `|Dζ| ≤ 3/r`); the
energy inequality for the test field `ζ² p_S^⊥(x − ξ)` gives
`∫ ζ² |p_{TₓM} − p_S|² dμ ≤ 16 ∫ |Dζ|² |p_S^⊥(x − ξ)|² dμ + 4 ∫ κ ζ² |p_S^⊥(x − ξ)| dμ`.
As `ζ = 1` on `B_{r/2}(ξ)`, the left side bounds the tilt over the half ball.  Off `B_r(ξ)` both
`ζ` and `Dζ` vanish, while on `B_r(ξ)`, `16 |Dζ|² ≤ 144/r²` and, as `0 ≤ ζ ≤ 1` and `κ ≥ 0`,
`4 κ ζ² t ≤ 4 κ t ≤ 2 t²/r² + 2 κ² r²` for `t = |p_S^⊥(x − ξ)|`.  Finally `144 + 2 = 146` and
`2 ≤ 146`. -/
theorem Submission.dorag_tilt_height_estimate : ∀ (n k : ℕ), ∃ C : ℝ, 0 < C ∧ ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (r : ℝ) (S : Submodule ℝ (Euclid (n + k))), IsOpen W → W ⊆ U → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → 0 < r → closedBall ξ r ⊆ W → Module.finrank ℝ S = n → ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal C * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r, ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure + ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)) := by
  intro n k
  refine ⟨146, by norm_num, ?_⟩
  intro U W R H κ ξ r S _hW hWU hH hHκ hMC hr hball hS
  -- `κ ≥ 0`, since `‖H 0‖ ≤ κ`
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  -- the radial cut-off `ζ`; its support is compact and lies in `B_r(ξ) ⊆ W`
  obtain ⟨ζ, hζC, hζ01, hζ1, hζsupp, hζD⟩ := Submission.dorag_th_radial_cutoff (n + k) ξ r hr
  have hζcpt : HasCompactSupport ζ :=
    (isCompact_closedBall ξ r).of_isClosed_subset (isClosed_tsupport ζ) hζsupp
  -- the energy inequality for the test field `ζ² p_S^⊥(x − ξ)`
  have hE := Submission.dorag_th_tilt_energy_inequality (n + k) n U W R H κ S ξ ζ hWU
    (Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R) hH hHκ hMC hS hζC hζcpt
    (hζsupp.trans hball)
  -- the left side: `ζ = 1` on `B_{r/2}(ξ)`
  have h1 : ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤
      ∫⁻ x, ENNReal.ofReal (ζ x ^ 2 * ∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ (r / 2)
    · simp only [indicator_of_mem hx, hζ1 x hx, one_pow, one_mul, le_refl]
    · simp only [indicator_of_notMem hx, zero_le]
  -- the gradient term: `Dζ = 0` off `B_r(ξ)`, and `16 |Dζ|² ≤ 144/r²`
  have h2 : ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ ζ x‖ ^ 2 *
        ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure ≤
      ENNReal.ofReal 144 * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
        ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ r
    · simp only [indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hD : ‖fderiv ℝ ζ x‖ ^ 2 ≤ (3 / r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hζD x) 2
      calc 16 * (‖fderiv ℝ ζ x‖ ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2)
          ≤ 16 * ((3 / r) ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) := by gcongr
        _ = 144 * (1 / r ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) := by ring
    · simp [indicator_of_notMem hx, fderiv_of_notMem_tsupport ℝ fun h => hx (hζsupp h)]
  -- the mean-curvature term: `ζ = 0` off `B_r(ξ)`, and `4 κ ζ² t ≤ 2 t²/r² + 2 κ²r²`
  have h3 : ENNReal.ofReal 4 * ∫⁻ x, ENNReal.ofReal (κ * ζ x ^ 2 *
        ‖(x - ξ) - S.starProjection (x - ξ)‖) ∂R.measure ≤
      ENNReal.ofReal 2 * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
        ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure) +
      ENNReal.ofReal 2 * (ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)) := by
    rw [← mul_assoc (ENNReal.ofReal 2) (ENNReal.ofReal (κ ^ 2 * r ^ 2)), ← setLIntegral_const,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_add_right _ measurable_const, ← lintegral_indicator measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall ξ r
    · simp only [indicator_of_mem hx]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht : 0 ≤ ‖(x - ξ) - S.starProjection (x - ξ)‖ := norm_nonneg _
      have hz2 : ζ x ^ 2 ≤ 1 := pow_le_one₀ (hζ01 x).1 (hζ01 x).2
      have hκt : κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ≤
          κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ := by
        calc κ * ζ x ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖
            = κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ * ζ x ^ 2 := by ring
          _ ≤ κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ * 1 :=
            mul_le_mul_of_nonneg_left hz2 (mul_nonneg hκ ht)
          _ = κ * ‖(x - ξ) - S.starProjection (x - ξ)‖ := mul_one _
      -- `2ab ≤ a² + b²` with `a = t/r`, `b = κr`, where `t = |p_S^⊥(x − ξ)|`
      have hab := two_mul_le_add_sq (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) (κ * r)
      have e1 : 2 * (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) * (κ * r) =
          2 * (κ * ‖(x - ξ) - S.starProjection (x - ξ)‖) := by
        rw [show 2 * (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) * (κ * r) =
            2 * (κ * ‖(x - ξ) - S.starProjection (x - ξ)‖) * (r / r) by ring,
          div_self hr.ne', mul_one]
      have e2 : (‖(x - ξ) - S.starProjection (x - ξ)‖ / r) ^ 2 + (κ * r) ^ 2 =
          1 / r ^ 2 * ‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2 + κ ^ 2 * r ^ 2 := by ring
      linarith
    · simp [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport fun h => hx (hζsupp h)]
  -- combine: `144 + 2 = 146` and `2 ≤ 146`
  have arith : ∀ X Y : ℝ≥0∞,
      ENNReal.ofReal 144 * X + (ENNReal.ofReal 2 * X + ENNReal.ofReal 2 * Y) ≤
        ENNReal.ofReal 146 * (X + Y) := by
    intro X Y
    simp only [ENNReal.ofReal_ofNat]
    calc 144 * X + (2 * X + 2 * Y) ≤ 144 * X + (2 * X + 2 * Y) + 144 * Y := le_self_add
      _ = 146 * (X + Y) := by ring
  exact h1.trans (hE.trans ((add_le_add h2 h3).trans (arith _ _)))

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
