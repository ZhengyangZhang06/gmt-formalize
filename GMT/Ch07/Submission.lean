import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter03.SubmanifoldCover

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

/-- **Countable gluing of the co-area identity over disjoint Borel pieces** (Simon Ch. 3, 2.8–2.9
summed over the decomposition `M = ⋃ⱼ Mⱼ` of Remark 1.3).  If `g` vanishes off the pairwise disjoint
Borel pieces `S j ⊆ M` and each piece satisfies `∫ ∫_{(S j)_t} φ dν dt = ∫_{S j} |g| φ dμ` (with an
a.e.-measurable slice integral), then so does `M`: the slice `M_t = M ∩ {g ≠ 0} ∩ f⁻¹(t)` is the
disjoint union of the `(S j)_t`, both sides are series over `j`, and monotone convergence exchanges
`∫ dt` with `∑ⱼ`. -/
theorem Submission.dor_lmbsf_tg_coarea_gluing : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (M : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (g : Euclid P → Euclid P) (f : Euclid P → ℝ) (φ : Euclid P → ℝ≥0∞), MeasurableSet M → (∀ j, MeasurableSet (S j)) → Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ j, S j ⊆ M) → Measurable g → (∀ x, (∀ j, x ∉ S j) → g x = 0) → Measurable f → (∀ j, AEMeasurable (fun t => ∫⁻ x in S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) ∧ ∫⁻ t, (∫⁻ x in S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) = ∫⁻ x in S j, ‖g x‖ₑ * φ x ∂μ) → AEMeasurable (fun t => ∫⁻ x in M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) ∧ ∫⁻ t, (∫⁻ x in M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν) = ∫⁻ x in M, ‖g x‖ₑ * φ x ∂μ := by
  intro P μ ν M S g f φ _ hS hdisj hSM hg hg0 hf hpiece
  -- Step 1: `M_t = ⋃ⱼ (S j)_t`, since `g = 0` off `⋃ⱼ S j` and `S j ⊆ M`
  have hset : ∀ t : ℝ,
      M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} = ⋃ j, S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} := by
    intro t
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_iUnion]
    constructor
    · rintro ⟨⟨-, hgx⟩, hfx⟩
      obtain ⟨j, hj⟩ : ∃ j, x ∈ S j := by
        by_contra h
        exact hgx (hg0 x fun j hj => h ⟨j, hj⟩)
      exact ⟨j, ⟨hj, hgx⟩, hfx⟩
    · rintro ⟨j, ⟨hj, hgx⟩, hfx⟩
      exact ⟨⟨hSM j hj, hgx⟩, hfx⟩
  -- Step 2: the slices `(S j)_t` are Borel and pairwise disjoint
  have hmeas : ∀ (t : ℝ) j, MeasurableSet (S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) := fun t j =>
    ((hS j).inter (hg (measurableSet_singleton 0).compl)).inter (hf (measurableSet_singleton t))
  have hdisj' : ∀ t : ℝ, Pairwise (Disjoint on fun j => S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) :=
    fun t i j hij => (hdisj hij).mono (inter_subset_left.trans inter_subset_left)
      (inter_subset_left.trans inter_subset_left)
  -- Step 3: `∫_{M_t} φ dν = ∑ⱼ ∫_{(S j)_t} φ dν` for every `t`
  have hslice : ∀ t : ℝ, ∫⁻ x in M ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν =
      ∑' j, ∫⁻ x in S j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂ν := fun t => by
    rw [hset t, lintegral_iUnion (hmeas t) (hdisj' t)]
  -- Step 6: `|g| φ` vanishes off `⋃ⱼ S j ⊆ M`, so `∫_M |g| φ dμ = ∑ⱼ ∫_{S j} |g| φ dμ`
  have hsupp : support (fun x => ‖g x‖ₑ * φ x) ⊆ ⋃ j, S j := by
    intro x hx
    rw [mem_support] at hx
    by_contra h
    exact hx (by simp [hg0 x fun j hj => h (mem_iUnion.2 ⟨j, hj⟩)])
  have hrhs : ∫⁻ x in M, ‖g x‖ₑ * φ x ∂μ = ∑' j, ∫⁻ x in S j, ‖g x‖ₑ * φ x ∂μ := by
    rw [setLIntegral_eq_of_support_subset (hsupp.trans (iUnion_subset hSM)),
      ← setLIntegral_eq_of_support_subset hsupp, lintegral_iUnion hS hdisj]
  -- Steps 4, 5 and 7: the series is a.e.-measurable, and monotone convergence for series
  simp only [hslice]
  refine ⟨AEMeasurable.tsum fun j => (hpiece j).1, ?_⟩
  rw [lintegral_tsum fun j => (hpiece j).1, hrhs]
  exact tsum_congr fun j => (hpiece j).2
/-- **Approximate tangent spaces glue over a countable Borel cover** (Simon Ch. 3, Remark 1.5(2),
with the decomposition of Remark 1.3; used in Ch. 6, proof of Lemma 4.1(2)).  Assume tangent
locality (TL): for Borel `A ⊆ B ⊆ U`, `U` open and `B` locally `Hⁿ`-finite in `U`, the sets `B`
and `A` have the same approximate tangent spaces at `Hⁿ`-a.e. `x ∈ A`.  Let `B ⊆ U` be Borel and
locally `Hⁿ`-finite in `U`, and let Borel sets `S j ⊆ B` cover `B`.  If `S j` has approximate
tangent space `Q(x)` at `Hⁿ`-a.e. `x ∈ S j` for every `j`, then `B` has approximate tangent space
`Q(x)` at `Hⁿ`-a.e. `x ∈ B`.
* (TL) with `A = S j`, evaluated at `Q(x)`, transfers the tangent space from `S j` to `B`,
  `Hⁿ`-a.e. on `S j`.
* A countable union of null sets is null (`ae_restrict_iUnion_iff`), and `B ⊆ ⋃ j, S j`. -/
theorem Submission.dor_lmbsf_tg_tangent_gluing : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U B : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (Q : Euclid P → Submodule ℝ (Euclid P)), IsOpen U → MeasurableSet B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → (∀ j, MeasurableSet (S j)) → (∀ j, S j ⊆ B) → B ⊆ ⋃ j, S j → (∀ j, ∀ᵐ x ∂(μHE[n].restrict (S j)), HasApproximateTangentSpaceAt n (S j) x (Q x)) → ∀ᵐ x ∂(μHE[n].restrict B), HasApproximateTangentSpaceAt n B x (Q x) := by
  intro hTL P n U B S Q hU hB hBU hfin hS hSB hBS hpiece
  -- Steps 1–2: on `S j`, (TL) with `A = S j` turns `TₓS j = Q(x)` into `TₓB = Q(x)`
  have hj : ∀ j, ∀ᵐ x ∂(μHE[n].restrict (S j)), HasApproximateTangentSpaceAt n B x (Q x) := by
    intro j
    filter_upwards [hTL P n U (S j) B hU (hS j) hB (hSB j) hBU hfin, hpiece j] with x hx hxQ
    exact (hx (Q x)).2 hxQ
  -- Step 3: a countable union of null sets is null, so this holds `Hⁿ`-a.e. on `⋃ j, S j`
  have hcover : ∀ᵐ x ∂(μHE[n].restrict (⋃ j, S j)), HasApproximateTangentSpaceAt n B x (Q x) :=
    (ae_restrict_iUnion_iff S _).2 hj
  -- Step 4: restrict to `B ⊆ ⋃ j, S j`
  exact ae_restrict_of_ae_restrict_of_subset hBS hcover
/-- **Gluing weak limits over a countable a.e.-partition** (Simon Ch. 6, proof of 4.5(2): the
reduction to a single piece).  If the disjoint Borel pieces `S j ⊆ M` cover `M` up to a `μ`-null
set, the `u k` are dominated on `M` by the integrable `D`, and `∫_{S j} u k → ∫_{S j ∩ E} v` for
every `j`, then `∫_M u k → ∫_{M ∩ E} v`.  Countable additivity writes both sides as series over
the pieces, the terms are bounded by the summable `∫_{S j} D`, and Tannery's theorem (the `ε/3`
argument of Mathlib's `tendsto_tsum_of_dominated_convergence`, inlined) passes to the limit. -/
theorem Submission.dor_lmbsf_tg_weak_limit_gluing : ∀ (P : ℕ) (μ : Measure (Euclid P)) (M E : Set (Euclid P)) (S : ℕ → Set (Euclid P)) (u : ℕ → Euclid P → ℝ) (v D : Euclid P → ℝ), MeasurableSet M → MeasurableSet E → (∀ j, MeasurableSet (S j)) → Pairwise (fun i j => Disjoint (S i) (S j)) → (∀ j, S j ⊆ M) → μ (M \ ⋃ j, S j) = 0 → IntegrableOn D M μ → (∀ k, AEStronglyMeasurable (u k) (μ.restrict M)) → (∀ k, ∀ᵐ x ∂(μ.restrict M), ‖u k x‖ ≤ D x) → IntegrableOn v (M ∩ E) μ → (∀ j, Tendsto (fun k => ∫ x in S j, u k x ∂μ) atTop (𝓝 (∫ x in S j ∩ E, v x ∂μ))) → Tendsto (fun k => ∫ x in M, u k x ∂μ) atTop (𝓝 (∫ x in M ∩ E, v x ∂μ)) := by
  intro P μ M E S u v D _ hE hS hdisj hSM hnull hD hum hule hv hlim
  -- Step 1: `M =ᵐ ⋃ⱼ Sⱼ` and `M ∩ E =ᵐ ⋃ⱼ (Sⱼ ∩ E)`
  have hUM : (⋃ j, S j) ⊆ M := iUnion_subset hSM
  have hae : M =ᵐ[μ] ⋃ j, S j :=
    ae_eq_set.2 ⟨hnull, by rw [Set.sdiff_eq_empty.2 hUM, measure_empty]⟩
  have haeE : M ∩ E =ᵐ[μ] ⋃ j, S j ∩ E := by
    rw [← iUnion_inter]
    exact hae.inter .rfl
  -- Steps 2–4: `∫_M u k = Σⱼ ∫_{Sⱼ} u k` and `∫_{M ∩ E} v = Σⱼ ∫_{Sⱼ ∩ E} v`
  have hsum_u : ∀ k, HasSum (fun j => ∫ x in S j, u k x ∂μ) (∫ x in M, u k x ∂μ) := by
    intro k
    have hk : IntegrableOn (u k) M μ := Integrable.mono' hD (hum k) (hule k)
    rw [Measure.restrict_congr_set hae]
    exact hasSum_integral_iUnion hS hdisj (hk.congr_set_ae hae.symm)
  have hsum_v : HasSum (fun j => ∫ x in S j ∩ E, v x ∂μ) (∫ x in M ∩ E, v x ∂μ) := by
    rw [Measure.restrict_congr_set haeE]
    exact hasSum_integral_iUnion (fun j => (hS j).inter hE)
      (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
      (hv.congr_set_ae haeE.symm)
  -- Step 5: `|∫_{Sⱼ} u k| ≤ ∫_{Sⱼ} D`, and `Σⱼ ∫_{Sⱼ} D` converges
  have hsum_D : Summable fun j => ∫ x in S j, D x ∂μ :=
    (hasSum_integral_iUnion hS hdisj (hD.mono_set hUM)).summable
  have hbound : ∀ k j, ‖∫ x in S j, u k x ∂μ‖ ≤ ∫ x in S j, D x ∂μ := fun k j =>
    norm_integral_le_of_norm_le (hD.mono_set (hSM j))
      (ae_restrict_of_ae_restrict_of_subset (hSM j) (hule k))
  -- Step 6: Tannery's theorem, by an `ε/3` argument
  have tannery : ∀ (f : ℕ → ℕ → ℝ) (g bound : ℕ → ℝ), Summable bound →
      (∀ j, Tendsto (fun k => f k j) atTop (𝓝 (g j))) → (∀ k j, ‖f k j‖ ≤ bound j) →
      Tendsto (fun k => ∑' j, f k j) atTop (𝓝 (∑' j, g j)) := by
    intro f g bound h_sum hab h_bound
    have h_g_le (j : ℕ) : ‖g j‖ ≤ bound j :=
      le_of_tendsto (tendsto_norm.comp (hab j)) (Eventually.of_forall fun k => h_bound k j)
    have h_sumg : Summable (‖g ·‖) :=
      h_sum.of_norm_bounded fun j => (norm_norm (g j)).symm ▸ h_g_le j
    have h_suma (k : ℕ) : Summable (‖f k ·‖) :=
      h_sum.of_norm_bounded <| by simpa only [norm_norm] using h_bound k
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨B, hB⟩ := h_sum
    obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, dist (∑ j ∈ T, bound j) B < ε / 3 := by
      rw [HasSum, Metric.tendsto_nhds] at hB
      exact Eventually.exists <| hB _ (by positivity)
    -- the tail of `Σ bound` off `T` is `< ε/3`
    have h1 : ∑' (j : (Tᶜ : Set ℕ)), bound j < ε / 3 := by
      calc _ ≤ ‖∑' (j : (Tᶜ : Set ℕ)), bound j‖ := Real.le_norm_self _
           _ = ‖B - ∑ j ∈ T, bound j‖ := congrArg _ ?_
           _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
      simpa only [hB.summable.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hB.tsum_eq
    -- the finitely many terms on `T` converge
    have h2 : Tendsto (fun k => ∑ j ∈ T, f k j) atTop (𝓝 (∑ j ∈ T, g j)) :=
      tendsto_finsetSum _ fun j _ => hab j
    rw [Metric.tendsto_nhds] at h2
    filter_upwards [h2 (ε / 3) (by positivity)] with k hk
    rw [dist_eq_norm, ← (h_suma k).of_norm.tsum_sub h_sumg.of_norm,
      ← ((h_suma k).of_norm.sub h_sumg.of_norm).sum_add_tsum_compl (s := T),
      (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
    refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
    · simpa only [dist_eq_norm, Finset.sum_sub_distrib] using hk
    · rw [((h_suma k).subtype _).of_norm.tsum_sub (h_sumg.subtype _).of_norm]
      refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
      · refine ((norm_tsum_le_tsum_norm ((h_suma k).subtype _)).trans ?_).trans_lt h1
        exact ((h_suma k).subtype _).tsum_le_tsum (h_bound k ·) (hB.summable.subtype _)
      · refine ((norm_tsum_le_tsum_norm (h_sumg.subtype _)).trans ?_).trans_lt h1
        exact (h_sumg.subtype _).tsum_le_tsum (h_g_le ·) (hB.summable.subtype _)
  -- Step 7: conclusion
  have key := tannery _ _ _ hsum_D hlim hbound
  rw [hsum_v.tsum_eq] at key
  exact key.congr fun k => (hsum_u k).tsum_eq
/-- **Countably many `C¹` charts inside `U`** (Simon Ch. 2, §4 (4.1); Ch. 3, Lemma 1.2 and
Remark 1.3).  Let `U ⊆ ℝᴾ` be open and `M ⊆ U` with `M ⊆ N₀ ∪ ⋃ₗ Nₗ`, each `Nₗ` an embedded
`m`-dimensional `C¹` submanifold.  Then there are countably many charts `(Vₛ, ψₛ)`: `Vₛ ⊆ ℝᵐ`
open, `ψₛ` `C¹` and injective on `Vₛ` with injective differential at every point of `Vₛ`, and
`ψₛ(Vₛ) ⊆ U`, such that `M ⊆ N₀ ∪ ⋃ₛ ψₛ(Vₛ)`. -/
theorem Submission.dor_lmbsf_cp_submanifold_chart_cover : ∀ (P m : ℕ) (U M N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), IsOpen U → M ⊆ U → (∀ l, IsEmbeddedSubmanifold 1 m (N l)) → M ⊆ N₀ ∪ ⋃ l, N l → ∃ (V : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P), (∀ s, IsOpen (V s) ∧ ContDiffOn ℝ 1 (ψ s) (V s) ∧ InjOn (ψ s) (V s) ∧ (∀ y ∈ V s, Injective (fderiv ℝ (ψ s) y)) ∧ ψ s '' V s ⊆ U) ∧ M ⊆ N₀ ∪ ⋃ s, ψ s '' V s := by
  classical
  intro P m U M N₀ N hU hMU hN hMN
  -- a chart `(V, W, ψ)` of `Nₗ` at every `z ∈ Nₗ`, with `ψ(V) = W ∩ Nₗ`
  have hch : ∀ (l : ℕ) (z : N l), ∃ (V : Set (Euclid m)) (W : Set (Euclid P))
      (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ (z : Euclid P) ∈ W ∧
      ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ N l ∧ ∀ y ∈ V, Injective (fderiv ℝ ψ y) := by
    intro l z
    obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, -, hD⟩ := hN l z z.2
    exact ⟨V, W, ψ, hV, hW, hzW, by simpa using hψ, hinj, himg, hD⟩
  choose V W ψ hV hW hzW hψ hinj himg hD using hch
  -- Lindelöf: countably many `W l z`, `z ∈ T l`, cover `Nₗ`
  have hT : ∀ l, ∃ T : Set (N l), T.Countable ∧ ⋃ z ∈ T, W l z = ⋃ z, W l z :=
    fun l => TopologicalSpace.isOpen_iUnion_countable (W l) (hW l)
  choose T hTc hTU using hT
  let I := Σ l : ℕ, T l
  have : ∀ l, Countable (T l) := fun l => (hTc l).to_subtype
  have : Countable I := inferInstance
  -- shrink each domain to `V ∩ ψ⁻¹(U)`; the extra index `none` carries the empty chart
  let V' : Option I → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some i => V i.1 i.2 ∩ ψ i.1 i.2 ⁻¹' U
  let ψ' : Option I → Euclid m → Euclid P := fun o =>
    match o with
    | none => 0
    | some i => ψ i.1 i.2
  have hchart : ∀ o : Option I, IsOpen (V' o) ∧ ContDiffOn ℝ 1 (ψ' o) (V' o) ∧
      InjOn (ψ' o) (V' o) ∧ (∀ y ∈ V' o, Injective (fderiv ℝ (ψ' o) y)) ∧ ψ' o '' V' o ⊆ U := by
    intro o
    cases o with
    | none => simp [V', ψ']
    | some i =>
      refine ⟨(hψ i.1 i.2).continuousOn.isOpen_inter_preimage (hV i.1 i.2) hU,
        (hψ i.1 i.2).mono inter_subset_left, (hinj i.1 i.2).mono inter_subset_left,
        fun y hy => hD i.1 i.2 y hy.1, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hy.2
  -- enumerate the countable index set `Option I` by `ℕ`
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option I)
  refine ⟨fun s => V' (σ s), fun s => ψ' (σ s), fun s => hchart (σ s), ?_⟩
  -- covering: `x ∈ M ∩ Nₗ` lies in some `W l z ∩ Nₗ = ψ(V)`, and its preimage in `ψ⁻¹(U)`
  intro x hxM
  rcases hMN hxM with h0 | hx
  · exact Or.inl h0
  · right
    obtain ⟨l, hxl⟩ := mem_iUnion.1 hx
    have hxW : x ∈ ⋃ z ∈ T l, W l z := by
      rw [hTU l]
      exact mem_iUnion.2 ⟨⟨x, hxl⟩, hzW l ⟨x, hxl⟩⟩
    obtain ⟨z, hzT, hxz⟩ := mem_iUnion₂.1 hxW
    have hx' : x ∈ ψ l z '' V l z := by
      rw [himg l z]
      exact ⟨hxz, hxl⟩
    obtain ⟨v, hv, hvx⟩ := hx'
    obtain ⟨s, hs⟩ := hσ (some ⟨l, ⟨z, hzT⟩⟩)
    refine mem_iUnion.2 ⟨s, v, ?_, ?_⟩
    · show v ∈ V' (σ s)
      rw [hs]
      exact ⟨hv, by simpa [hvx] using hMU hxM⟩
    · show ψ' (σ s) v = x
      rw [hs]
      exact hvx
/-- **Simon Ch. 3, Lemma 1.2** ("only if", C¹ pieces of a chart), assuming the C¹ approximation
of Lipschitz functions (Ch. 2, Theorem 1.5).  Countably many balls `B_r(c)` with
`B̄_{2r}(c) ⊆ V` cover `V` (Lindelöf); `ψ` is Lipschitz on `B̄_{2r}(c)`, so `f ∘ ψ` has a Lipschitz
extension `ũ` from `B̄_r(c)` (McShane), and `C¹` functions `G_k` agree with `ũ` off a set of
measure `< (k+1)⁻¹`.  The pieces are `B̄_r(c) ∩ {ũ = G_k}` inside `C' = B̄_{2r}(c)`, enumerated
by `ℕ` with an empty piece as padding; the remainder lies in `⋃_b ⋂_k {ũ_b ≠ G_{b,k}}`, a null
set. -/
theorem Submission.dor_lmbsf_cp_chart_c1_pieces : (∀ (m : ℕ) (u : Euclid m → ℝ) (K : NNReal), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧ volume {y | u y ≠ G y} < ε) → ∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), IsOpen V → ContDiffOn ℝ 1 ψ V → LipschitzWith L f → ∃ (C C' : ℕ → Set (Euclid m)) (F : ℕ → Euclid m → ℝ), (∀ k, IsCompact (C k) ∧ IsCompact (C' k) ∧ Convex ℝ (C' k) ∧ C k ⊆ interior (C' k) ∧ C' k ⊆ V ∧ ContDiff ℝ 1 (F k) ∧ ∀ y ∈ C k, f (ψ y) = F k y) ∧ volume (V \ ⋃ k, C k) = 0 := by
  classical
  intro CA m P V ψ f L hV hψ hf
  -- balls `B_r(c)` with `r > 0` and `B̄_{2r}(c) ⊆ V`; countably many of them cover `V`
  let B := {p : Euclid m × ℝ // 0 < p.2 ∧ closedBall p.1 (2 * p.2) ⊆ V}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun b : B => ball b.1.1 b.1.2) (fun _ => isOpen_ball)
  have hcovV : V ⊆ ⋃ b ∈ T, ball b.1.1 b.1.2 := by
    intro v hv
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV v hv
    have hsub : closedBall v (2 * (ε / 3)) ⊆ V :=
      (closedBall_subset_ball (by linarith)).trans hball
    let b : B := ⟨(v, ε / 3), by positivity, hsub⟩
    rw [hTU]
    exact mem_iUnion.2 ⟨b, mem_ball_self (by positivity)⟩
  -- on each ball: a Lipschitz extension `u` of `f ∘ ψ` and `C¹` functions `G k` with
  -- `volume {u ≠ G k} < (k+1)⁻¹`
  have hdata : ∀ b : B, ∃ (G : ℕ → Euclid m → ℝ) (u : Euclid m → ℝ), (∀ k, ContDiff ℝ 1 (G k)) ∧
      Continuous u ∧ (∀ y ∈ closedBall b.1.1 b.1.2, f (ψ y) = u y) ∧
      ∀ k : ℕ, volume {y | u y ≠ G k y} < ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro b
    obtain ⟨Λ, hΛ⟩ := (hψ.mono b.2.2).exists_lipschitzOnWith one_ne_zero (convex_closedBall _ _)
      (isCompact_closedBall _ _)
    have hu : LipschitzOnWith (L * Λ) (f ∘ ψ) (closedBall b.1.1 b.1.2) :=
      (hf.comp_lipschitzOnWith hΛ).mono (closedBall_subset_closedBall (by linarith [b.2.1]))
    obtain ⟨u, hu', hequ⟩ := hu.extend_real
    have hk : ∀ k : ℕ, ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧
        volume {y | u y ≠ G y} < ((k : ℝ≥0∞) + 1)⁻¹ := fun k =>
      CA m u (L * Λ) hu' _ (ENNReal.inv_pos.2 (by simp))
    choose G hG hGvol using hk
    exact ⟨G, u, hG, hu'.continuous, fun y hy => hequ hy, hGvol⟩
  choose G u hG hucont hequ hGvol using hdata
  have : Countable T := hTc.to_subtype
  -- the pieces indexed by `Option (T × ℕ)`, with the empty piece at `none`
  let Cp : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, k) => closedBall b.1.1.1 b.1.1.2 ∩ {y | u b.1 y = G b.1 k y}
  let C'p : Option (T × ℕ) → Set (Euclid m) := fun o =>
    match o with
    | none => ∅
    | some (b, _) => closedBall b.1.1.1 (2 * b.1.1.2)
  let Fp : Option (T × ℕ) → Euclid m → ℝ := fun o =>
    match o with
    | none => 0
    | some (b, k) => G b.1 k
  have hprop : ∀ o, IsCompact (Cp o) ∧ IsCompact (C'p o) ∧ Convex ℝ (C'p o) ∧
      Cp o ⊆ interior (C'p o) ∧ C'p o ⊆ V ∧ ContDiff ℝ 1 (Fp o) ∧
      ∀ y ∈ Cp o, f (ψ y) = Fp o y := by
    intro o
    cases o with
    | none => exact ⟨isCompact_empty, isCompact_empty, convex_empty, empty_subset _, empty_subset _,
        contDiff_zero_fun, fun y hy => hy.elim⟩
    | some bk =>
      obtain ⟨b, k⟩ := bk
      refine ⟨(isCompact_closedBall _ _).inter_right
          (isClosed_eq (hucont b.1) (hG b.1 k).continuous),
        isCompact_closedBall _ _, convex_closedBall _ _, ?_, b.1.2.2, hG b.1 k, ?_⟩
      · intro y hy
        apply ball_subset_interior_closedBall
        have := hy.1
        rw [mem_closedBall] at this
        rw [mem_ball]
        linarith [b.1.2.1]
      · intro y hy
        exact (hequ b.1 y hy.1).trans hy.2
  obtain ⟨σ, hσ⟩ := exists_surjective_nat (Option (T × ℕ))
  refine ⟨fun s => Cp (σ s), fun s => C'p (σ s), fun s => Fp (σ s), fun s => hprop (σ s), ?_⟩
  -- the remainder lies in `⋃_b ⋂_k {u_b ≠ G_{b,k}}`
  have hsub : V \ ⋃ s, Cp (σ s) ⊆ ⋃ b : T, ⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y} := by
    rintro v ⟨hv, hvnot⟩
    obtain ⟨b, hbT, hvb⟩ := mem_iUnion₂.1 (hcovV hv)
    refine mem_iUnion.2 ⟨⟨b, hbT⟩, mem_iInter.2 fun k => ?_⟩
    intro heq
    obtain ⟨s, hs⟩ := hσ (some (⟨b, hbT⟩, k))
    apply hvnot
    refine mem_iUnion.2 ⟨s, ?_⟩
    rw [hs]
    exact ⟨ball_subset_closedBall hvb, heq⟩
  refine measure_mono_null hsub (measure_iUnion_null fun b => ?_)
  -- each `⋂_k {u_b ≠ G_{b,k}}` has measure `< (n+1)⁻¹ ≤ n⁻¹` for every `n`
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  have h1 : volume (⋂ k : ℕ, {y | u b.1 y ≠ G b.1 k y}) ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
    (measure_mono (iInter_subset _ n)).trans (hGvol b.1 n).le
  have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.2 le_self_add
  exact absurd (h1.trans h2) (not_le.2 hn)
/-- **Lipschitz (`C¹`) images of Lebesgue-null sets are `Hᵐ`-null** (Simon Ch. 3, §2, discussion
after 2.4; Ch. 2, Theorem 1.8(i)).  If `ψ` is `C¹` on an open `V ⊆ ℝᵐ` and `Z ⊆ V` is `Lᵐ`-null,
then `Hᵐ(ψ(Z)) = 0`: `ψ` is Lipschitz near each point of `V`, countably many such neighbourhoods
cover `V` (Lindelöf), and on each the Lipschitz image bound gives `Hᵐ(ψ(Z ∩ t)) ≤ Kᵐ Lᵐ(Z ∩ t) = 0`.
-/
theorem Submission.dor_lmbsf_cp_c1_image_null : ∀ (m P : ℕ) (V Z : Set (Euclid m)) (ψ : Euclid m → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → Z ⊆ V → volume Z = 0 → μHE[m] (ψ '' Z) = 0 := by
  intro m P V Z ψ hV hψ hZV hZ
  -- Step 1: every `y ∈ V` has an open neighbourhood on which `ψ` is Lipschitz
  have hloc : ∀ y : V, ∃ K : NNReal, ∃ t : Set (Euclid m), IsOpen t ∧ (y : Euclid m) ∈ t ∧
      LipschitzOnWith K ψ t := by
    intro y
    obtain ⟨K, t, ht, hK⟩ := (hψ.contDiffAt (hV.mem_nhds y.2)).exists_lipschitzOnWith
    obtain ⟨u, hut, hu, hyu⟩ := _root_.mem_nhds_iff.1 ht
    exact ⟨K, u, hu, hyu, hK.mono hut⟩
  choose K t ht hyt hK using hloc
  -- Step 2: Lindelöf gives a countable subfamily covering `V ⊇ Z`
  obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable t ht
  have hcov : Z ⊆ ⋃ y ∈ T, t y := by
    intro z hz
    have : z ∈ ⋃ y, t y := mem_iUnion.2 ⟨⟨z, hZV hz⟩, hyt _⟩
    rw [← hT] at this
    exact this
  -- Step 3: `ψ(Z) ⊆ ⋃_{y ∈ T} ψ(Z ∩ t y)`
  have hsub : ψ '' Z ⊆ ⋃ y ∈ T, ψ '' (Z ∩ t y) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hyT, hzy⟩ := mem_iUnion₂.1 (hcov hz)
    exact mem_iUnion₂.2 ⟨y, hyT, z, ⟨hz, hzy⟩, rfl⟩
  -- Steps 4 and 5: each piece is null by the Lipschitz image bound and `μHE[m] = volume`
  refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).2 fun y _ => ?_)
  refine le_antisymm ?_ zero_le
  calc μHE[m] (ψ '' (Z ∩ t y)) ≤ (K y : ℝ≥0∞) ^ m * μHE[m] (Z ∩ t y) :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
          ((hK y).mono inter_subset_right)
    _ = 0 := by
        rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
          measure_mono_null inter_subset_left hZ, mul_zero]
/-- **Approximate tangent planes of `M` on a chart piece** (Simon Ch. 3, Remark 1.5(2) and the
proof of Theorem 1.6 "⇒"; Step 7 of `dor_lmbsf_lipschitz_chart_pieces`).  Assume the locality
principle (TL): for Borel `A ⊆ B ⊆ U` with `Hⁿ(B ∩ K) < ∞` for compact `K ⊆ U`, at `Hⁿ`-a.e.
`x ∈ A` the sets `B` and `A` have the same approximate tangent spaces.  Let `ψ` be `C¹` on the
convex compact `C'` with `ψ(C') ⊆ U`, let `C ⊆ int C'` be compact, and let `ψ(C')` have
approximate tangent space `Dψ(y)(ℝᵐ)` at `ψ(y)` for `y ∈ int C'`.  Then at `Hᵐ`-a.e.
`x ∈ M ∩ ψ(C)`, `M` has approximate tangent space `Dψ(y)(ℝᵐ)` for every `y ∈ C` with `ψ(y) = x`.
`S = ψ(C')` is compact, and `Hᵐ(S) ≤ Λᵐ Lᵐ(C') < ∞` since `ψ` is Lipschitz on `C'`; apply (TL)
to `M ∩ ψ(C) ⊆ S` and to `M ∩ ψ(C) ⊆ M`. -/
theorem Submission.dor_lmbsf_cp_chart_tangent_ae : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P m : ℕ) (U M : Set (Euclid P)) (C C' : Set (Euclid m)) (ψ : Euclid m → Euclid P), IsOpen U → MeasurableSet M → M ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → ContDiffOn ℝ 1 ψ C' → ψ '' C' ⊆ U → IsCompact C → IsCompact C' → Convex ℝ C' → C ⊆ interior C' → (∀ y ∈ interior C', HasApproximateTangentSpaceAt m (ψ '' C') (ψ y) (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P))) → ∀ᵐ x ∂(μHE[m].restrict (M ∩ ψ '' C)), ∀ y ∈ C, ψ y = x → HasApproximateTangentSpaceAt m M x (LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P)) := by
  intro TL P m U M C C' ψ hU hM hMU hfin hψ hψU hC hC' hconv hCC' hIT
  have hψC' : ContinuousOn ψ C' := hψ.continuousOn
  have hCsub : C ⊆ C' := hCC'.trans interior_subset
  -- `S = ψ(C')` and `ψ(C)` are compact
  have hS : IsCompact (ψ '' C') := hC'.image_of_continuousOn hψC'
  have hSC : IsCompact (ψ '' C) := hC.image_of_continuousOn (hψC'.mono hCsub)
  -- `Hᵐ(S) ≤ Λᵐ Hᵐ(C') = Λᵐ Lᵐ(C') < ∞`, `ψ` being `Λ`-Lipschitz on the convex compact `C'`
  obtain ⟨Λ, hΛ⟩ := hψ.exists_lipschitzOnWith one_ne_zero hconv hC'
  have hSfin : μHE[m] (ψ '' C') ≠ ∞ := by
    refine ne_of_lt (lt_of_le_of_lt
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hΛ) ?_)
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hC'.measure_lt_top
  -- (TL) for `A = M ∩ ψ(C) ⊆ S` and for `A ⊆ M`
  have hA : MeasurableSet (M ∩ ψ '' C) := hM.inter hSC.isClosed.measurableSet
  have h1 := TL P m U (M ∩ ψ '' C) (ψ '' C') hU hA hS.isClosed.measurableSet
    (fun x hx => image_mono hCsub hx.2) hψU
    (fun K _ _ => ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left))
  have h2 := TL P m U (M ∩ ψ '' C) M hU hA hM inter_subset_left hMU hfin
  -- at `x = ψ y`, transfer the tangent plane of `S` to `A`, then to `M`
  filter_upwards [h1, h2] with x hx1 hx2 y hy hyx
  have hS' := hIT y (hCC' hy)
  rw [hyx] at hS'
  exact (hx2 _).2 ((hx1 _).1 hS')
/-- **Slicing (Simon Ch. 6, §4), chart pieces, step 8: the gradient bound at density points**
(the estimate behind `|∇ᴹf| ≤ Lip f`, cf. Simon Ch. 3, 2.1 and Ch. 2, 4.10).  Let `F = f ∘ ψ` on
a Borel set `Z ⊆ ℝᵐ`, with `F` and `ψ` differentiable at every point of `Z` and `f`
`L`-Lipschitz.  Assuming the direction property (DD) of density points, `|DF(y)e| ≤ L |Dψ(y)e|`
for `Lᵐ`-a.e. `y ∈ Z` and every `e`.  By the Lebesgue density theorem
(`Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`) a.e. `y ∈ Z` is a density point of
`Z`.  For a unit vector `v`, (DD) gives `yᵢ ∈ Z ∖ {y}` with `yᵢ → y` and
`(yᵢ − y)/|yᵢ − y| → v`.  The difference quotients satisfy `|F(yᵢ) − F(y)| ≤ L |ψ(yᵢ) − ψ(y)|`
and converge to `DF(y)v` and `Dψ(y)v` (`HasFDerivWithinAt.lim`), so `|DF(y)v| ≤ L |Dψ(y)v|`.
A general `e ≠ 0` follows by linearity from `v = e/|e|`. -/
theorem Submission.dor_lmbsf_cp_gradient_bound_ae : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (m P : ℕ) (Z : Set (Euclid m)) (F : Euclid m → ℝ) (ψ : Euclid m → Euclid P) (f : Euclid P → ℝ) (L : NNReal), MeasurableSet Z → (∀ y ∈ Z, DifferentiableAt ℝ F y ∧ DifferentiableAt ℝ ψ y) → (∀ y ∈ Z, f (ψ y) = F y) → LipschitzWith L f → ∀ᵐ y ∂volume, y ∈ Z → ∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖ := by
  intro DD m P Z F ψ f L hZ hdiff heq hf
  -- step 1: almost every point of `Z` is a Lebesgue density point of `Z`
  filter_upwards [Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hZ] with y hy hyZ
  have hdens : Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r))
      (𝓝[>] 0) (𝓝 1) := by
    simpa [Set.indicator_of_mem hyZ] using hy
  -- steps 2–5: the bound in a unit direction `v`
  have hunit : ∀ v : Euclid m, ‖v‖ = 1 → |fderiv ℝ F y v| ≤ (L : ℝ) * ‖fderiv ℝ ψ y v‖ := by
    intro v hv
    -- step 2: points `yᵢ ∈ Z ∖ {y}`, `yᵢ → y`, approaching `y` from the direction `v`
    obtain ⟨ys, hys, hlim, hdir⟩ := DD m Z y hdens v hv
    -- step 3: `|F(yᵢ) − F(y)| = |f(ψ(yᵢ)) − f(ψ(y))| ≤ L |ψ(yᵢ) − ψ(y)|`, divided by `|yᵢ − y|`
    have hineq : ∀ i, |‖ys i - y‖⁻¹ • (F (ys i) - F y)| ≤
        (L : ℝ) * ‖‖ys i - y‖⁻¹ • (ψ (ys i) - ψ y)‖ := by
      intro i
      have hci : 0 ≤ ‖ys i - y‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
      rw [smul_eq_mul, abs_mul, abs_of_nonneg hci, norm_smul, Real.norm_of_nonneg hci,
        ← heq _ (hys i).1, ← heq y hyZ]
      have h1 := hf.dist_le_mul (ψ (ys i)) (ψ y)
      rw [Real.dist_eq, dist_eq_norm] at h1
      calc ‖ys i - y‖⁻¹ * |f (ψ (ys i)) - f (ψ y)|
          ≤ ‖ys i - y‖⁻¹ * ((L : ℝ) * ‖ψ (ys i) - ψ y‖) := mul_le_mul_of_nonneg_left h1 hci
        _ = (L : ℝ) * (‖ys i - y‖⁻¹ * ‖ψ (ys i) - ψ y‖) := by ring
    -- step 4: the difference quotients along `yᵢ − y` converge to `DF(y)v` and `Dψ(y)v`
    have hd0 : Tendsto (fun i => ys i - y) atTop (𝓝 0) := by
      simpa using hlim.sub_const y
    have hF' := ((hdiff y hyZ).1.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    have hψ' := ((hdiff y hyZ).2.hasFDerivAt.hasFDerivWithinAt (s := univ)).lim hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    simp only [add_sub_cancel] at hF' hψ'
    -- step 5: the non-strict inequality passes to the limit
    exact le_of_tendsto_of_tendsto' hF'.abs (hψ'.norm.const_mul _) hineq
  -- step 6: a general `e ≠ 0` by linearity, from the unit vector `‖e‖⁻¹ • e`
  intro e
  by_cases he : e = 0
  · simp [he]
  · have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
    have hv : ‖‖e‖⁻¹ • e‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
    have h := hunit _ hv
    rw [map_smul, map_smul, smul_eq_mul, abs_mul, norm_smul, abs_inv, abs_norm, norm_inv,
      norm_norm] at h
    have hpos : 0 < ‖e‖⁻¹ := inv_pos.2 (norm_pos_iff.2 he)
    have h2 : ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by
      calc ‖e‖⁻¹ * |fderiv ℝ F y e| ≤ (L : ℝ) * (‖e‖⁻¹ * ‖fderiv ℝ ψ y e‖) := h
        _ = ‖e‖⁻¹ * ((L : ℝ) * ‖fderiv ℝ ψ y e‖) := by ring
    exact le_of_mul_le_mul_left h2 hpos
/-- **Disjoint Borel refinement of chart pieces** (Simon Ch. 3, Remark 1.3).  Let `M ⊆ ℝᴾ` be
Borel, `Cⱼ ⊆ ℝᵐ` compact and `ψⱼ` continuous on `Cⱼ`, with `μ(M ∖ ⋃ⱼ ψⱼ(Cⱼ)) = 0`, and suppose
that for `μ⌞(M ∩ ψⱼ(Cⱼ))`-a.e. `x` every `y ∈ Cⱼ` with `ψⱼ(y) = x` satisfies `Goodⱼ(y)`.  Then
there are Borel sets `Yⱼ ⊆ Cⱼ` of good points whose images `ψⱼ(Yⱼ) ⊆ M` are pairwise disjoint
and cover `M` up to a `μ`-null set. -/
theorem Submission.dor_lmbsf_cp_disjoint_refinement : ∀ (m P : ℕ) (μ : Measure (Euclid P)) (M : Set (Euclid P)) (C : ℕ → Set (Euclid m)) (ψ : ℕ → Euclid m → Euclid P) (Good : ℕ → Euclid m → Prop), MeasurableSet M → (∀ j, IsCompact (C j) ∧ ContinuousOn (ψ j) (C j)) → μ (M \ ⋃ j, ψ j '' C j) = 0 → (∀ j, ∀ᵐ x ∂(μ.restrict (M ∩ ψ j '' C j)), ∀ y ∈ C j, ψ j y = x → Good j y) → ∃ Y : ℕ → Set (Euclid m), (∀ j, MeasurableSet (Y j) ∧ Y j ⊆ C j ∧ ψ j '' Y j ⊆ M ∧ ∀ y ∈ Y j, Good j y) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μ (M \ ⋃ j, ψ j '' Y j) = 0 := by
  classical
  intro m P μ M C ψ Good hM hC hnull hgood
  -- `Eⱼ = ψⱼ(Cⱼ)` is compact, hence Borel, and `Aⱼ = M ∩ Eⱼ` is Borel
  let E : ℕ → Set (Euclid P) := fun j => ψ j '' C j
  have hEc : ∀ j, IsCompact (E j) := fun j => (hC j).1.image_of_continuousOn (hC j).2
  have hEm : ∀ j, MeasurableSet (E j) := fun j => (hEc j).isClosed.measurableSet
  let A : ℕ → Set (Euclid P) := fun j => M ∩ E j
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hM.inter (hEm j)
  -- a Borel set `Tⱼ` containing the exceptional points, with `μ(Tⱼ ∩ Aⱼ) = 0`
  have hT : ∀ j, ∃ T : Set (Euclid P), {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} ⊆ T ∧
      MeasurableSet T ∧ μ (T ∩ A j) = 0 := by
    intro j
    obtain ⟨T, hsub, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hgood j))
    exact ⟨T, hsub, hTm, by rwa [Measure.restrict_apply hTm] at hT0⟩
  choose T hTsub hTm hT0 using hT
  -- Remark 1.3: `Dⱼ = Aⱼ ∖ ⋃_{i<j} Aᵢ`; then `M'ⱼ = Dⱼ ∖ Tⱼ` and `Yⱼ = Cⱼ ∩ ψⱼ⁻¹(M'ⱼ)`
  let D : ℕ → Set (Euclid P) := disjointed A
  let M' : ℕ → Set (Euclid P) := fun j => D j \ T j
  have hDm : ∀ j, MeasurableSet (D j) := MeasurableSet.disjointed hAm
  have hM'm : ∀ j, MeasurableSet (M' j) := fun j => (hDm j).diff (hTm j)
  have hDA : ∀ j, D j ⊆ A j := disjointed_subset A
  -- `ψⱼ(Yⱼ) = M'ⱼ`, since `M'ⱼ ⊆ Aⱼ ⊆ ψⱼ(Cⱼ)`
  have himg : ∀ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) = M' j := by
    intro j
    ext x
    constructor
    · rintro ⟨y, ⟨_, hy⟩, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (hDA j hx.1).2
      exact ⟨y, ⟨hy, hx⟩, rfl⟩
  refine ⟨fun j => C j ∩ ψ j ⁻¹' M' j, fun j => ⟨?_, inter_subset_left, ?_, ?_⟩, ?_, ?_⟩
  · -- `Yⱼ` is Borel: on `Cⱼ`, `ψⱼ` agrees with the Borel map equal to `ψⱼ` on `Cⱼ`, `0` off it
    have hpw : Measurable ((C j).piecewise (ψ j) (fun _ => 0)) :=
      (hC j).2.measurable_piecewise continuousOn_const (hC j).1.isClosed.measurableSet
    have : C j ∩ ψ j ⁻¹' M' j = C j ∩ (C j).piecewise (ψ j) (fun _ => 0) ⁻¹' M' j := by
      ext y
      constructor
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
      · rintro ⟨hy, hy'⟩
        exact ⟨hy, by simpa [Set.piecewise_eq_of_mem _ _ _ hy] using hy'⟩
    show MeasurableSet (C j ∩ ψ j ⁻¹' M' j)
    rw [this]
    exact (hC j).1.isClosed.measurableSet.inter (hpw (hM'm j))
  · -- `ψⱼ(Yⱼ) = M'ⱼ ⊆ Aⱼ ⊆ M`
    rw [himg j]
    exact fun x hx => (hDA j hx.1).1
  · -- points of `Yⱼ` are good, since `ψⱼ(y) ∉ Tⱼ`
    intro y hy
    have hx : ψ j y ∉ T j := hy.2.2
    have : ψ j y ∉ {x | ¬ ∀ y ∈ C j, ψ j y = x → Good j y} := fun h => hx (hTsub j h)
    simp only [mem_ofPred_eq, not_not] at this
    exact this y hy.1 rfl
  · -- the images lie in the pairwise disjoint `Dⱼ`
    intro i j hij
    simp only
    rw [himg i, himg j]
    exact (disjoint_disjointed A hij).mono sdiff_subset sdiff_subset
  · -- `M ∖ ⋃ⱼ ψⱼ(Yⱼ) ⊆ (M ∖ ⋃ⱼ Eⱼ) ∪ ⋃ⱼ (Tⱼ ∩ Aⱼ)`, a `μ`-null set
    have hsub : M \ ⋃ j, ψ j '' (C j ∩ ψ j ⁻¹' M' j) ⊆ (M \ ⋃ j, E j) ∪ ⋃ j, (T j ∩ A j) := by
      rintro x ⟨hxM, hxnot⟩
      by_cases hxE : x ∈ ⋃ j, E j
      · right
        have hxA : x ∈ ⋃ j, A j := by
          obtain ⟨j, hj⟩ := mem_iUnion.1 hxE
          exact mem_iUnion.2 ⟨j, hxM, hj⟩
        rw [← iUnion_disjointed] at hxA
        obtain ⟨j, hj⟩ := mem_iUnion.1 hxA
        have hxT : x ∈ T j := by
          by_contra hxT
          exact hxnot (mem_iUnion.2 ⟨j, by rw [himg j]; exact ⟨hj, hxT⟩⟩)
        exact mem_iUnion.2 ⟨j, hxT, hDA j hj⟩
      · exact Or.inl ⟨hxM, hxE⟩
    refine measure_mono_null hsub ?_
    rw [measure_union_null_iff]
    exact ⟨hnull, measure_iUnion_null hT0⟩
/-- **Tangential lift of a gradient on a `C¹` chart** (Simon Ch. 2, §4; Ch. 3, 2.1).  Let `ψ` be
`C¹` on the open set `V ⊆ ℝᵐ` with injective differential and `F : ℝᵐ → ℝ` be `C¹`.  With
`A(y) = Dψ(y)`, `Γ(y) = A(y)* A(y)` and `a(y)` the Riesz vector of `DF(y)`, the field
`Φ(y) = A(y) Γ(y)⁻¹ a(y)` is continuous on `V`, lies in `Dψ(y)(ℝᵐ)`, satisfies
`⟨Φ(y), Dψ(y)e⟩ = DF(y)e`, and `|Φ(y)| ≤ L` whenever `|DF(y)e| ≤ L |Dψ(y)e|` for all `e`. -/
theorem Submission.dor_lmbsf_cp_chart_tangent_lift : ∀ (m P : ℕ) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (F : Euclid m → ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → ∃ Φ : Euclid m → Euclid P, ContinuousOn Φ V ∧ ∀ y ∈ V, Φ y ∈ LinearMap.range (fderiv ℝ ψ y : Euclid m →ₗ[ℝ] Euclid P) ∧ (∀ e : Euclid m, inner ℝ (Φ y) (fderiv ℝ ψ y e) = fderiv ℝ F y e) ∧ ∀ L : NNReal, (∀ e : Euclid m, |fderiv ℝ F y e| ≤ (L : ℝ) * ‖fderiv ℝ ψ y e‖) → ‖Φ y‖ ≤ (L : ℝ) := by
  classical
  intro m P V ψ F hV hψ hinj hF
  let A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun y => fderiv ℝ ψ y
  let Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) :=
    fun y => (ContinuousLinearMap.adjoint (A y)).comp (A y)
  let a : Euclid m → Euclid m :=
    fun y => (InnerProductSpace.toDual ℝ (Euclid m)).symm (fderiv ℝ F y)
  -- `Γ(y)` is injective, hence a unit, on `V`
  have hunit : ∀ y ∈ V, IsUnit (Γ y) := by
    intro y hy
    rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
      LinearMap.ker_eq_bot']
    intro e he
    have h1 : inner ℝ (Γ y e) e = ‖A y e‖ ^ 2 := by
      simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      exact real_inner_self_eq_norm_sq (A y e)
    have h2 : Γ y e = 0 := he
    rw [h2, inner_zero_left] at h1
    have h3 : A y e = 0 := by
      have : ‖A y e‖ = 0 := by nlinarith [norm_nonneg (A y e)]
      exact norm_eq_zero.1 this
    exact hinj y hy (by simpa [A] using h3)
  refine ⟨fun y => A y (Ring.inverse (Γ y) (a y)), ?_, ?_⟩
  · -- continuity: `fderiv`, adjoint, composition, `Ring.inverse` at units, evaluation
    have hA : ContinuousOn A V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hAadj : ContinuousOn (fun y => ContinuousLinearMap.adjoint (A y)) V :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous
        |>.comp_continuousOn hA
    have hΓ : ContinuousOn Γ V := hAadj.clm_comp hA
    have hinv : ContinuousOn (fun y => Ring.inverse (Γ y)) V := by
      intro y hy
      obtain ⟨u, hu⟩ := hunit y hy
      have hc := NormedRing.inverse_continuousAt u
      rw [hu] at hc
      exact hc.comp_continuousWithinAt (hΓ y hy)
    have ha : Continuous a :=
      (InnerProductSpace.toDual ℝ (Euclid m)).symm.continuous.comp
        (hF.continuous_fderiv one_ne_zero)
    exact hA.clm_apply (hinv.clm_apply ha.continuousOn)
  · intro y hy
    set w := Ring.inverse (Γ y) (a y) with hw
    have hΓw : Γ y w = a y := by
      obtain ⟨u, hu⟩ := hunit y hy
      rw [hw, ← hu, Ring.inverse_unit, ← mul_apply_eq_comp, Units.mul_inv, one_apply_eq_self]
    -- the defining identity `⟨A w, A e⟩ = ⟨Γ w, e⟩ = ⟨a, e⟩ = DF(y) e`
    have hdef : ∀ e : Euclid m, inner ℝ (A y w) (fderiv ℝ ψ y e) = fderiv ℝ F y e := by
      intro e
      have : inner ℝ (A y w) (A y e) = inner ℝ (Γ y w) e := by
        simp only [Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
      change inner ℝ (A y w) (A y e) = _
      rw [this, hΓw]
      simp [a, InnerProductSpace.toDual_symm_apply]
    refine ⟨⟨w, rfl⟩, hdef, fun L hL => ?_⟩
    -- `|Φ|² = DF(y) w ≤ L |A w| = L |Φ|`
    have hsq : ‖A y w‖ ^ 2 ≤ (L : ℝ) * ‖A y w‖ := by
      rw [← real_inner_self_eq_norm_sq]
      calc inner ℝ (A y w) (A y w) = fderiv ℝ F y w := hdef w
        _ ≤ |fderiv ℝ F y w| := le_abs_self _
        _ ≤ (L : ℝ) * ‖fderiv ℝ ψ y w‖ := hL w
    change ‖A y w‖ ≤ (L : ℝ)
    by_cases h0 : ‖A y w‖ = 0
    · rw [h0]; exact L.coe_nonneg
    · have hpos : 0 < ‖A y w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
/-- Borel gluing over pairwise disjoint injective images (Lusin–Souslin; the Borel field `g` on
the chart pieces in the slicing step of the proof of Simon 7.4.3): if `ψⱼ` is continuous and
injective and `Φⱼ` continuous on the Borel set `Yⱼ ⊆ ℝᵐ`, and the images `Mⱼ = ψⱼ(Yⱼ)` are
pairwise disjoint, then some Borel `g : ℝᴾ → ℝᴾ` has `g(ψⱼ(y)) = Φⱼ(y)` for `y ∈ Yⱼ` and `g = 0`
off `⋃ⱼ Mⱼ`.  `ψⱼ|_{Yⱼ}` is a measurable embedding, so the extension `gⱼ` of `Φⱼ|_{Yⱼ}` along it
by `0` is Borel; `g(x) = gₙ(x)` for the least `n` with `x ∈ Mₙ ∪ (⋃ⱼ Mⱼ)ᶜ`. -/
theorem Submission.dor_lmbsf_cp_measurable_glue : ∀ (m P : ℕ) (Y : ℕ → Set (Euclid m)) (ψ Φ : ℕ → Euclid m → Euclid P), (∀ j, MeasurableSet (Y j) ∧ ContinuousOn (ψ j) (Y j) ∧ InjOn (ψ j) (Y j) ∧ ContinuousOn (Φ j) (Y j)) → Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) → ∃ g : Euclid P → Euclid P, Measurable g ∧ (∀ j, ∀ y ∈ Y j, g (ψ j y) = Φ j y) ∧ ∀ x, (∀ j, x ∉ ψ j '' Y j) → g x = 0 := by
  classical
  intro m P Y ψ Φ hY hdisj
  -- Lusin–Souslin: `Mⱼ = ψⱼ(Yⱼ)` is Borel
  have hM : ∀ j, MeasurableSet (ψ j '' Y j) := fun j =>
    (hY j).1.image_of_continuousOn_injOn (hY j).2.1 (hY j).2.2.1
  -- `gⱼ`: the extension of `Φⱼ|_{Yⱼ}` by `0` along the measurable embedding `ψⱼ|_{Yⱼ}`
  obtain ⟨gj, hgj, hgj_val, hgj_zero⟩ : ∃ gj : ℕ → Euclid P → Euclid P,
      (∀ j, Measurable (gj j)) ∧ (∀ j, ∀ y ∈ Y j, gj j (ψ j y) = Φ j y) ∧
        ∀ j x, x ∉ ψ j '' Y j → gj j x = 0 := by
    have hemb : ∀ j, MeasurableEmbedding ((Y j).domRestrict (ψ j)) := fun j =>
      (hY j).2.1.measurableEmbedding (hY j).1 (hY j).2.2.1
    refine ⟨fun j => Function.extend ((Y j).domRestrict (ψ j)) ((Y j).domRestrict (Φ j)) 0,
      fun j => (hemb j).measurable_extend (hY j).2.2.2.domRestrict.measurable measurable_const,
      fun j y hy => (hemb j).injective.extend_apply _ _ ⟨y, hy⟩, fun j x hx => ?_⟩
    refine Function.extend_apply' _ _ x ?_
    rintro ⟨y, hy⟩
    exact hx ⟨y, y.2, hy⟩
  -- glue by least index: `g(x) = gₙ(x)` for the least `n` with `x ∈ Mₙ ∪ (⋃ⱼ Mⱼ)ᶜ`
  have hp : ∀ x, ∃ n, x ∈ ψ n '' Y n ∪ (⋃ j, ψ j '' Y j)ᶜ := fun x => by
    by_cases hx : x ∈ ⋃ j, ψ j '' Y j
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
      exact ⟨j, Set.mem_union_left _ hj⟩
    · exact ⟨0, Set.mem_union_right _ (Set.mem_compl hx)⟩
  refine ⟨fun x => gj (Nat.find (hp x)) x,
    Measurable.find (p := fun n x => x ∈ ψ n '' Y n ∪ (⋃ j, ψ j '' Y j)ᶜ) hgj
      (fun n => (hM n).union (MeasurableSet.iUnion hM).compl) hp, ?_, ?_⟩
  · -- at `ψⱼ(y)` the least index is `j`, by disjointness
    intro j y hy
    have hx : ψ j y ∈ ψ j '' Y j := Set.mem_image_of_mem _ hy
    have hfind : Nat.find (hp (ψ j y)) = j := by
      rcases Nat.find_spec (hp (ψ j y)) with h | h
      · by_contra hne
        exact Set.disjoint_left.1 (hdisj hne) h hx
      · exact absurd (Set.mem_iUnion.2 ⟨j, hx⟩) h
    show gj (Nat.find (hp (ψ j y))) (ψ j y) = Φ j y
    rw [hfind]
    exact hgj_val j y hy
  · -- off `⋃ⱼ Mⱼ` every `gₙ` vanishes
    intro x hx
    exact hgj_zero _ x (hx _)
/-- **A `C¹` immersion is locally injective.**  If `G : ℝᵐ → ℝᴾ` is `C¹` and `DG(x)` is injective,
then for some `r > 0` the map `G` and every `DG(z)`, `z ∈ B̄_r(x)`, are injective.  `L = DG(x)` is
anti-Lipschitz on the finite-dimensional `ℝᵐ`, `c ‖v‖ ≤ ‖L v‖` with `c > 0`, and continuity of
`DG` gives `‖DG(z) - L‖ ≤ c/2` on `B̄_r(x)`.  If `DG(z) u = 0` then
`c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`; if `G a = G b`, the mean value inequality
`‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖` gives `c ‖a - b‖ ≤ (c/2) ‖a - b‖`.  So `u = 0`, `a = b`. -/
theorem Submission.dor_lmbsf_c1c_immersion_local_injOn : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m), ContDiff ℝ 1 G → Function.Injective (fderiv ℝ G x) → ∃ r : ℝ, 0 < r ∧ Set.InjOn G (Metric.closedBall x r) ∧ ∀ z ∈ Metric.closedBall x r, Function.Injective (fderiv ℝ G z) := by
  intro P m G x hG hx
  set L : Euclid m →L[ℝ] Euclid P := fderiv ℝ G x
  -- `L` is injective on the finite-dimensional `ℝᵐ`, hence anti-Lipschitz: `c ‖v‖ ≤ ‖L v‖`
  obtain ⟨K, hKpos, hK⟩ :=
    (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hx)
  have hK' : (0 : ℝ) < K := hKpos
  set c : ℝ := (K : ℝ)⁻¹
  have hcpos : 0 < c := inv_pos.2 hK'
  have hLc : ∀ v, c * ‖v‖ ≤ ‖L v‖ := fun v =>
    (inv_mul_le_iff₀ hK').2 (L.bound_of_antilipschitz hK v)
  -- continuity of `DG` gives `δ > 0` with `‖DG(z) - L‖ ≤ c/2` on `B̄_{δ/2}(x)`
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.1 (hG.continuous_fderiv one_ne_zero) x (c / 2) (half_pos hcpos)
  have hbound : ∀ z ∈ closedBall x (δ / 2), ‖fderiv ℝ G z - L‖ ≤ c / 2 := by
    intro z hz
    have h := hδ z (lt_of_le_of_lt (mem_closedBall.1 hz) (half_lt_self hδpos))
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨δ / 2, half_pos hδpos, ?_, ?_⟩
  · -- mean value inequality: `‖G a - G b - L (a - b)‖ ≤ (c/2) ‖a - b‖`
    intro a ha b hb hab
    have hmvt := (convex_closedBall x (δ / 2)).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => (hG.differentiable one_ne_zero) z) hbound hb ha
    rw [hab, sub_self, zero_sub, norm_neg] at hmvt
    have h1 := hLc (a - b)
    have h2 : ‖a - b‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  · -- if `DG(z) u = 0` then `c ‖u‖ ≤ ‖L u‖ = ‖(DG(z) - L) u‖ ≤ (c/2) ‖u‖`
    intro z hz v w hvw
    have hu : fderiv ℝ G z (v - w) = 0 := by rw [map_sub, hvw, sub_self]
    have h1 := hLc (v - w)
    have h2 : ‖L (v - w)‖ ≤ c / 2 * ‖v - w‖ := by
      have h3 : L (v - w) = -((fderiv ℝ G z - L) (v - w)) := by
        rw [sub_apply, hu, zero_sub, neg_neg]
      rw [h3, norm_neg]
      calc ‖(fderiv ℝ G z - L) (v - w)‖ ≤ ‖fderiv ℝ G z - L‖ * ‖v - w‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ c / 2 * ‖v - w‖ := by gcongr; exact hbound z hz
    have h4 : ‖v - w‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (v - w)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 h4)
/-- **A `C¹` chart on a ball** (Simon Ch. 3, proof of Lemma 1.2, step 5): if `G : ℝᵐ → ℝᴾ` is
`C¹`, injective on `B̄_r(x)` and has injective derivative on `B_r(x)`, then `G(B_r(x))` is an
embedded `m`-dimensional `C¹` submanifold.  Every point is charted by `ψ = G` on `V = B_r(x)`
with `W = ℝᴾ \ G(∂B_r(x))`: `W` is open because the sphere is compact; injectivity on `B̄_r(x)`
gives `G(B_r(x)) ⊆ W`, so `ψ(V) = W ∩ G(B_r(x))`; and for compact `K ⊆ W`, sphere points map
outside `K`, so `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact. -/
theorem Submission.dor_lmbsf_c1c_injOn_closedBall_chart : ∀ (P m : ℕ) (G : Euclid m → Euclid P) (x : Euclid m) (r : ℝ), ContDiff ℝ 1 G → Set.InjOn G (Metric.closedBall x r) → (∀ z ∈ Metric.ball x r, Function.Injective (fderiv ℝ G z)) → IsEmbeddedSubmanifold 1 m (G '' Metric.ball x r) := by
  intro P m G x r hG hinj hD
  -- `W = ℝᴾ \ G(∂B_r(x))` is open: the sphere is compact and `G` is continuous
  have hW : IsOpen (G '' Metric.sphere x r)ᶜ :=
    ((isCompact_sphere x r).image hG.continuous).isClosed.isOpen_compl
  -- `G(B_r(x)) ⊆ W`: `G` is injective on `B̄_r(x)` and the sphere misses the open ball
  have hNW : G '' Metric.ball x r ⊆ (G '' Metric.sphere x r)ᶜ := by
    rintro _ ⟨v, hv, rfl⟩ ⟨s, hs, hsv⟩
    have hsv' : s = v :=
      hinj (Metric.sphere_subset_closedBall hs) (Metric.ball_subset_closedBall hv) hsv
    subst hsv'
    exact (Metric.mem_ball.1 hv).ne (Metric.mem_sphere.1 hs)
  -- the same chart `(V, W, ψ) = (B_r(x), W, G)` serves every point of `G(B_r(x))`
  intro y hy
  refine ⟨Metric.ball x r, (G '' Metric.sphere x r)ᶜ, G, Metric.isOpen_ball, hW, hNW hy, ?_,
    hinj.mono Metric.ball_subset_closedBall, (Set.inter_eq_right.2 hNW).symm, ?_, hD⟩
  · exact_mod_cast hG.contDiffOn
  -- properness: for compact `K ⊆ W`, `B_r(x) ∩ G⁻¹(K) = B̄_r(x) ∩ G⁻¹(K)` is compact
  · intro K hKW hK
    have hball : Metric.ball x r ∩ G ⁻¹' K = Metric.closedBall x r ∩ G ⁻¹' K := by
      refine Set.Subset.antisymm
        (Set.inter_subset_inter_left _ Metric.ball_subset_closedBall) ?_
      rintro z ⟨hz, hzK⟩
      refine ⟨?_, hzK⟩
      rcases (Metric.mem_closedBall.1 hz).lt_or_eq with h | h
      · exact Metric.mem_ball.2 h
      · exact (hKW (Set.mem_preimage.1 hzK) ⟨z, Metric.mem_sphere.2 h, rfl⟩).elim
    rw [hball]
    exact (isCompact_closedBall x r).inter_right (hK.isClosed.preimage hG.continuous)
/-- **A Lipschitz map `ℝᵐ → ℝᴾ` agrees with countably many `C¹` maps off a set with `Hᵐ`-null
image** (Simon Ch. 3, proof of Lemma 1.2), given the scalar `C¹` approximation (H) of Ch. 2,
Theorem 1.5.  Apply (H) to each `K`-Lipschitz coordinate `Fᵖ` with `ε = 1/i` and put
`Gᵢ = (g_{ip})_p`, so `Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`.  Hence `Z = ⋂ᵢ {F ≠ Gᵢ}` is
`Lᵐ`-null, `E = F(Z)` has `Hᵐ(E) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`, and off `Z`, `F = Gᵢ` for some `i`. -/
theorem Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces : ∀ (P m : ℕ) (F : Euclid m → Euclid P) (K : NNReal), LipschitzWith K F → (∀ (u : Euclid m → ℝ) (L : NNReal), LipschitzWith L u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ g : Euclid m → ℝ, ContDiff ℝ 1 g ∧ volume {y | u y ≠ g y} < ε) → ∃ (E : Set (Euclid P)) (G : ℕ → Euclid m → Euclid P), μHE[m] E = 0 ∧ (∀ i, ContDiff ℝ 1 (G i)) ∧ Set.range F ⊆ E ∪ ⋃ i, Set.range (G i) := by
  intro P m F K hF H
  -- the coordinates `Fᵖ` are `K`-Lipschitz, since `|a_p| ≤ |a|`
  have hcoord : ∀ p : Fin P, LipschitzWith K fun y => F y p := by
    intro p
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    calc dist (F a p) (F b p) = ‖(F a - F b) p‖ := by
          rw [PiLp.sub_apply, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ‖F a - F b‖ := PiLp.norm_apply_le _ _
      _ = dist (F a) (F b) := (dist_eq_norm _ _).symm
      _ ≤ K * dist a b := hF.dist_le_mul a b
  -- (H) for each coordinate with `ε = 1/i`: `Lᵐ({Fᵖ ≠ g_{ip}}) < 1/i`
  choose g hg hgvol using fun (i : ℕ) (p : Fin P) =>
    H (fun y => F y p) K (hcoord p) (i : ℝ≥0∞)⁻¹ (ENNReal.inv_pos.2 (ENNReal.natCast_ne_top i))
  -- `Gᵢ = (g_{ip})_p` is `C¹`
  obtain ⟨G, hGp⟩ : ∃ G : ℕ → Euclid m → Euclid P, ∀ i y p, G i y p = g i p y :=
    ⟨fun i y => WithLp.toLp 2 fun p => g i p y, fun _ _ _ => rfl⟩
  have hGc : ∀ i, ContDiff ℝ 1 (G i) := fun i =>
    (contDiff_piLp 2).2 fun p => by simpa only [hGp] using hg i p
  -- `Z = ⋂ᵢ {F ≠ Gᵢ}`: `Lᵐ(Z) ≤ Lᵐ({F ≠ Gᵢ}) ≤ Σ_p Lᵐ({Fᵖ ≠ g_{ip}}) ≤ P/i`
  set Z : Set (Euclid m) := ⋂ i, {y | F y ≠ G i y} with hZ_def
  have hZi : ∀ i : ℕ, volume Z ≤ (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by
    intro i
    calc volume Z ≤ volume (⋃ p : Fin P, {y | F y p ≠ g i p y}) := by
          refine measure_mono fun y hy => ?_
          have hne : F y ≠ G i y := mem_iInter.1 hy i
          by_contra hcon
          simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hcon
          exact hne (PiLp.ext fun p => by rw [hGp, hcon p])
      _ ≤ ∑ p : Fin P, volume {y | F y p ≠ g i p y} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin P, (i : ℝ≥0∞)⁻¹ := Finset.sum_le_sum fun p _ => (hgvol i p).le
      _ = (P : ℝ≥0∞) * (i : ℝ≥0∞)⁻¹ := by simp
  -- `P/i → 0`, so `Lᵐ(Z) = 0`
  have hZ0 : volume Z = 0 := by
    have ht := ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr (ENNReal.natCast_ne_top P))
    rw [mul_zero] at ht
    exact le_antisymm (ge_of_tendsto' ht hZi) zero_le
  refine ⟨F '' Z, G, ?_, hGc, ?_⟩
  · -- `Hᵐ(F(Z)) ≤ Kᵐ Hᵐ(Z) = Kᵐ Lᵐ(Z) = 0`
    have h := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
      (hF.lipschitzOnWith (s := Z))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume m, hZ0, mul_zero] at h
    exact le_antisymm h zero_le
  · -- `F z ∈ F(Z)` if `z ∈ Z`, otherwise `F z = Gᵢ z` for some `i`
    rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ Z
    · exact Or.inl ⟨z, hz, rfl⟩
    · rw [hZ_def] at hz
      simp only [mem_iInter, mem_ofPred_eq, not_forall, not_not] at hz
      obtain ⟨i, hi⟩ := hz
      exact Or.inr (mem_iUnion.2 ⟨i, z, hi.symm⟩)
/-- **Simon Ch. 3, proof of Lemma 1.2 ("only if"), last paragraph**, for one `C¹` map
`G : ℝᵐ → ℝᴾ`: `G(ℝᵐ) ⊆ N₀ ∪ ⋃ₗ Nₗ` with `Hᵐ(N₀) = 0` and each `Nₗ` an embedded `C¹`
`m`-submanifold.  `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null (Simon: by the area formula of
Ch. 2 §3).  Here this is checked directly: if `DG(x) e = 0`, `|e| = 1`, and `‖DG - DG(x)‖ ≤ λM`,
`‖DG‖ ≤ M` on `B̄_ρ(x)`, then with `Ψ = id + (λ⁻¹ - 1) e ⊗ e` (`det Ψ = λ⁻¹`) the map `G ∘ Ψ` is
`2M`-Lipschitz on `Ψ⁻¹(B̄_ρ(x))`, so `Hᵐ(G(B̄_ρ(x))) ≤ (2M)ᵐ λ |B̄_ρ(x)|`; a Besicovitch disjoint
cover of the critical points in `B_R(0)` gives `Hᵐ(G(·)) ≤ (2M)ᵐ λ |B̄_{R+1}(0)|` for every `λ`.
At a regular point `x`, `G` is injective with injective derivative on some `B̄_{r_x}(x)`, so
`G(B_{r_x}(x))` is a submanifold; countably many of these balls cover the regular set (Lindelöf,
left implicit by Simon), and no ball is needed if it is empty. -/
theorem Submission.dor_lmbsf_c1c_c1_range_cover : ∀ (P m : ℕ) (G : Euclid m → Euclid P), ContDiff ℝ 1 G → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ Set.range G ⊆ N₀ ∪ ⋃ l, N l := by
  intro P m G hG
  -- Step 1: `G` is differentiable everywhere, with continuous derivative.
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hDG : Continuous (fderiv ℝ G) := hG.continuous_fderiv one_ne_zero
  -- Step 2: the critical image `N₀ = G({x : DG(x) not injective})` is `Hᵐ`-null.
  have hN₀ : μHE[m] (G '' {x | ¬ Injective (fderiv ℝ G x)}) = 0 := by
    have hvol : (μHE[m] : Measure (Euclid m)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have hcov : {x | ¬ Injective (fderiv ℝ G x)} =
        ⋃ k : ℕ, {x | ¬ Injective (fderiv ℝ G x)} ∩ ball (0 : Euclid m) k := by
      rw [← inter_iUnion, iUnion_ball_nat, inter_univ]
    rw [hcov, image_iUnion]
    refine measure_iUnion_null fun k => ?_
    set R : ℝ := (k : ℝ)
    obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall (0 : Euclid m) (R + 1)).exists_bound_of_continuousOn
      hDG.continuousOn
    set M : ℝ := max M₀ 1
    have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hMK : ∀ y ∈ closedBall (0 : Euclid m) (R + 1), ‖fderiv ℝ G y‖ ≤ M :=
      fun y hy => (hM₀ y hy).trans (le_max_left _ _)
    -- one ball `B̄_ρ(x)` around a critical point `x`
    have hloc : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ x, ¬ Injective (fderiv ℝ G x) → ∀ ρ : ℝ,
        (∀ y ∈ closedBall x ρ, ‖fderiv ℝ G y - fderiv ℝ G x‖ ≤ lam * M) →
        closedBall x ρ ⊆ closedBall 0 (R + 1) →
        μHE[m] (G '' closedBall x ρ) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
      intro lam hlam0 hlam1 x hx ρ hρ hρK
      obtain ⟨v, hv0, hv⟩ : ∃ v, fderiv ℝ G x v = 0 ∧ v ≠ 0 := by
        simpa only [injective_iff_map_eq_zero, not_forall, exists_prop] using hx
      set e : Euclid m := (‖v‖⁻¹ : ℝ) • v
      have he : ‖e‖ = 1 := norm_smul_inv_norm hv
      have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
      have hDe : fderiv ℝ G x e = 0 := by simp [e, hv0]
      set Ψ : Euclid m →L[ℝ] Euclid m :=
        ContinuousLinearMap.id ℝ _ + (lam⁻¹ - 1) • (innerSL ℝ e).smulRight e
      have hΨ : ∀ u, Ψ u = u + ((lam⁻¹ - 1) * inner ℝ e u) • e := by
        intro u
        simp [Ψ, smul_smul]
      -- `det Ψ = 1 + (λ⁻¹ - 1) |e|² = λ⁻¹` (matrix determinant lemma)
      have hdet : LinearMap.det (Ψ : Euclid m →ₗ[ℝ] Euclid m) = lam⁻¹ := by
        have hee' : e.ofLp ⬝ᵥ e.ofLp = 1 := by
          rw [← hee, EuclideanSpace.inner_eq_star_dotProduct]
          simp
        set b := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
        have hmat : LinearMap.toMatrix b b (Ψ : Euclid m →ₗ[ℝ] Euclid m) =
            1 + Matrix.replicateCol Unit ((lam⁻¹ - 1) • e.ofLp) * Matrix.replicateRow Unit e.ofLp := by
          ext i j
          simp [LinearMap.toMatrix_apply, b, hΨ, Matrix.one_apply, Matrix.mul_apply,
            EuclideanSpace.inner_single_right, PiLp.single_apply]
          ring
        rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_one_add_replicateCol_mul_replicateRow,
          dotProduct_smul, hee', smul_eq_mul, mul_one]
        ring
      have hsurj : Surjective Ψ := by
        intro y
        refine ⟨y + ((lam - 1) * inner ℝ e y) • e, ?_⟩
        have hcoef : (lam - 1) * inner ℝ e y +
            (lam⁻¹ - 1) * (inner ℝ e y + (lam - 1) * inner ℝ e y * 1) = 0 := by
          field_simp
          ring
        rw [hΨ, inner_add_right, inner_smul_right, hee, add_assoc, ← add_smul, hcoef, zero_smul,
          add_zero]
      -- `D(G ∘ Ψ) u = DG u + (λ⁻¹ - 1) ⟨e, u⟩ DG e` with `‖DG e‖ = ‖(DG - DG(x)) e‖ ≤ λM`
      have hLip : LipschitzOnWith (2 * M).toNNReal (G ∘ Ψ) (Ψ ⁻¹' closedBall x ρ) := by
        refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
          (fun z _ => (hGd (Ψ z)).comp z Ψ.differentiableAt) (fun z hz => ?_)
          ((convex_closedBall x ρ).linear_preimage (Ψ : Euclid m →ₗ[ℝ] Euclid m))
        have hy : Ψ z ∈ closedBall x ρ := hz
        rw [fderiv_comp z (hGd (Ψ z)) Ψ.differentiableAt, ContinuousLinearMap.fderiv,
          ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
        have h1 : ‖fderiv ℝ G (Ψ z) u‖ ≤ M * ‖u‖ :=
          ((fderiv ℝ G (Ψ z)).le_opNorm u).trans
            (mul_le_mul_of_nonneg_right (hMK _ (hρK hy)) (norm_nonneg _))
        have h2 : ‖fderiv ℝ G (Ψ z) e‖ ≤ lam * M := by
          have h3 : fderiv ℝ G (Ψ z) e = (fderiv ℝ G (Ψ z) - fderiv ℝ G x) e := by
            rw [sub_apply, hDe, sub_zero]
          rw [h3]
          calc ‖(fderiv ℝ G (Ψ z) - fderiv ℝ G x) e‖
              ≤ ‖fderiv ℝ G (Ψ z) - fderiv ℝ G x‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
            _ ≤ lam * M := by rw [he, mul_one]; exact hρ _ hy
        have h4 : |lam⁻¹ - 1| ≤ lam⁻¹ := by
          have : 1 ≤ lam⁻¹ := (one_le_inv₀ hlam0).2 hlam1
          rw [abs_of_nonneg (by linarith)]
          linarith
        have h5 : |inner ℝ e u| ≤ ‖u‖ := by
          simpa [he] using abs_real_inner_le_norm e u
        rw [ContinuousLinearMap.comp_apply, hΨ u, map_add, map_smul]
        calc ‖fderiv ℝ G (Ψ z) u + ((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖
            ≤ ‖fderiv ℝ G (Ψ z) u‖ + ‖((lam⁻¹ - 1) * inner ℝ e u) • fderiv ℝ G (Ψ z) e‖ :=
              norm_add_le _ _
          _ = ‖fderiv ℝ G (Ψ z) u‖ + |lam⁻¹ - 1| * |inner ℝ e u| * ‖fderiv ℝ G (Ψ z) e‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_mul]
          _ ≤ M * ‖u‖ + lam⁻¹ * ‖u‖ * (lam * M) := by gcongr
          _ = 2 * M * ‖u‖ := by
              rw [show lam⁻¹ * ‖u‖ * (lam * M) = (lam⁻¹ * lam) * (M * ‖u‖) by ring,
                inv_mul_cancel₀ hlam0.ne', one_mul]
              ring
      have hvolΨ : volume (Ψ ⁻¹' closedBall x ρ) = ENNReal.ofReal lam * volume (closedBall x ρ) := by
        rw [Measure.addHaar_preimage_continuousLinearMap volume
          (by rw [hdet]; exact inv_ne_zero hlam0.ne'), hdet, inv_inv, abs_of_pos hlam0]
      calc μHE[m] (G '' closedBall x ρ) = μHE[m] ((G ∘ Ψ) '' (Ψ ⁻¹' closedBall x ρ)) := by
            rw [image_comp, image_preimage_eq _ hsurj]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * μHE[m] (Ψ ⁻¹' closedBall x ρ) :=
            Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hLip
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam * volume (closedBall x ρ) := by
            rw [hvol, hvolΨ, mul_assoc]
    -- `G` is `M`-Lipschitz on `B̄_{R+1}(0)`, so it maps volume-null sets there to `Hᵐ`-null sets
    have hLipK : LipschitzOnWith M.toNNReal G (closedBall 0 (R + 1)) := by
      refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun y _ => hGd y)
        (fun y hy => ?_) (convex_closedBall _ _)
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM.le]
      exact hMK y hy
    -- Besicovitch: disjoint balls `B̄_{ρ x}(x)` with `ρ x < r x` cover almost all critical points
    have hmain : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
        μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)) ≤
          ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
            volume (closedBall (0 : Euclid m) (R + 1)) := by
      intro lam hlam0 hlam1
      have hr : ∀ x : Euclid m, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
          ∀ y ∈ ball x r, ‖fderiv ℝ G y - fderiv ℝ G x‖ < lam * M := by
        intro x
        obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.1 hDG x (lam * M) (by positivity)
        refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun y hy => ?_⟩
        have h := hδ' y (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
        rwa [dist_eq_norm] at h
      choose r hr0 hr1 hr using hr
      obtain ⟨t, ρ, ht, hts, hρ, hnull, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae
        volume (fun _ => univ) ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R)
        (fun _ _ δ hδ => ⟨δ / 2, mem_univ _, half_pos hδ, half_lt_self hδ⟩) r (fun x _ => hr0 x)
      have hballK : ∀ x ∈ t, closedBall x (ρ x) ⊆ closedBall 0 (R + 1) := by
        intro x hx y hy
        have hx' : ‖x‖ < R := mem_ball_zero_iff.1 (hts hx).2
        rw [mem_closedBall, dist_eq_norm] at hy
        rw [mem_closedBall_zero_iff]
        calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith [(hρ x hx).2.2, hr1 x]
      have hsub : G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) ⊆
          G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \ ⋃ x ∈ t, closedBall x (ρ x)) ∪
            ⋃ x ∈ t, G '' closedBall x (ρ x) := by
        rintro _ ⟨y, hy, rfl⟩
        by_cases hyU : y ∈ ⋃ x ∈ t, closedBall x (ρ x)
        · obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
          exact Or.inr (mem_iUnion₂.2 ⟨x, hx, mem_image_of_mem G hyx⟩)
        · exact Or.inl (mem_image_of_mem G ⟨hy, hyU⟩)
      have h0 : μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
          ⋃ x ∈ t, closedBall x (ρ x))) = 0 := by
        refine le_antisymm ?_ bot_le
        calc μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)))
            ≤ (M.toNNReal : ℝ≥0∞) ^ m * μHE[m] (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
                ⋃ x ∈ t, closedBall x (ρ x)) :=
              Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m
                (hLipK.mono fun y hy =>
                  closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hy.1.2))
          _ = 0 := by rw [hvol, hnull, mul_zero]
      calc μHE[m] (G '' ({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R))
          ≤ μHE[m] (G '' (({x | ¬ Injective (fderiv ℝ G x)} ∩ ball 0 R) \
              ⋃ x ∈ t, closedBall x (ρ x))) + μHE[m] (⋃ x ∈ t, G '' closedBall x (ρ x)) :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ ∑' x : t, μHE[m] (G '' closedBall (x : Euclid m) (ρ x)) := by
            rw [h0, zero_add]
            exact measure_biUnion_le _ ht _
        _ ≤ ∑' x : t, ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (x : Euclid m) (ρ x)) :=
            ENNReal.tsum_le_tsum fun x => hloc lam hlam0 hlam1 x (hts x.2).1 (ρ x)
              (fun y hy => (hr x y (closedBall_subset_ball (hρ x x.2).2.2 hy)).le) (hballK x x.2)
        _ = ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (⋃ x ∈ t, closedBall x (ρ x)) := by
            rw [ENNReal.tsum_mul_left, measure_biUnion ht hdisj fun _ _ => measurableSet_closedBall]
        _ ≤ ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
              volume (closedBall (0 : Euclid m) (R + 1)) := by
            gcongr
            exact iUnion₂_subset hballK
    -- let `λ → 0`
    have hlim : Tendsto (fun lam : ℝ => ((2 * M).toNNReal : ℝ≥0∞) ^ m * ENNReal.ofReal lam *
        volume (closedBall (0 : Euclid m) (R + 1))) (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun lam : ℝ => ENNReal.ofReal lam) (𝓝[>] 0) (𝓝 0) := by
        simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
          nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul h1
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))) (Or.inr measure_closedBall_lt_top.ne)
    refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
    filter_upwards [Ioo_mem_nhdsGT one_pos] with lam hlam
    exact hmain lam hlam.1 hlam.2.le
  have hcrit : ∀ x, ¬ Injective (fderiv ℝ G x) → G x ∈ G '' {x | ¬ Injective (fderiv ℝ G x)} :=
    fun x hx => mem_image_of_mem G hx
  -- Step 3: at a regular point `x`, `G(B_{r_x}(x))` is an embedded `C¹` `m`-submanifold.
  have hchart : ∀ x : {x : Euclid m // Injective (fderiv ℝ G x)}, ∃ r : ℝ, 0 < r ∧
      IsEmbeddedSubmanifold 1 m (G '' ball (x : Euclid m) r) := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, hinj, hder⟩ := Submission.dor_lmbsf_c1c_immersion_local_injOn P m G x hG hx
    exact ⟨r, hr, Submission.dor_lmbsf_c1c_injOn_closedBall_chart P m G x r hG hinj
      fun z hz => hder z (ball_subset_closedBall hz)⟩
  choose r hr hN using hchart
  -- Step 4: with no regular point, `Nₗ = ∅` (vacuously a submanifold) and `G(ℝᵐ) ⊆ N₀`.
  rcases isEmpty_or_nonempty {x : Euclid m // Injective (fderiv ℝ G x)} with hR | hR
  · refine ⟨_, fun _ => ∅, hN₀, fun _ y hy => absurd hy (notMem_empty y), ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Or.inl (hcrit x fun hx => hR.false ⟨x, hx⟩)
  -- Otherwise countably many balls `B_{r_{xₗ}}(xₗ)` cover the regular set (Lindelöf).
  obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof
    {x : Euclid m | Injective (fderiv ℝ G x)}).indexed_countable_subcover
    (fun x : {x : Euclid m // Injective (fderiv ℝ G x)} => ball (x : Euclid m) (r x))
    (fun _ => isOpen_ball) fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr _)⟩
  refine ⟨_, fun l => G '' ball (f l : Euclid m) (r (f l)), hN₀, fun l => hN (f l), ?_⟩
  -- Step 5: `G(x) ∈ N₀` if `x` is critical, and `G(x) ∈ Nₗ` if `x ∈ B_{r_{xₗ}}(xₗ)`.
  rintro _ ⟨x, rfl⟩
  by_cases hx : Injective (fderiv ℝ G x)
  · obtain ⟨l, hl⟩ := mem_iUnion.mp
      (hf (show x ∈ {x : Euclid m | Injective (fderiv ℝ G x)} from hx))
    exact Or.inr (mem_iUnion.mpr ⟨l, mem_image_of_mem G hl⟩)
  · exact Or.inl (hcrit x hx)
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

/-- **Lusin's theorem** for `Lⁿ` with a closed set, `Lⁿ(B) = ∞` allowed (Simon Ch. 2, proof of
1.5, step 2, glued as in the infinite-measure case of Simon 1.15(2)).  On the bounded Borel shells
`S_j = {j ≤ ‖x‖ < j + 1}`, the compact form `dor_ims_lusin_measurable_continuousOn` gives compact
`K_j ⊆ B ∩ S_j` with `Lⁿ((B ∩ S_j) \ K_j) < δ_j` on which `g` is continuous, where `∑ δ_j < ε`.
As `K_j ⊆ S_j`, the family `(K_j)` is locally finite, so `C = ⋃ⱼ K_j` is closed and `g` is
continuous on `C`; and `B \ C ⊆ ⋃ⱼ (B ∩ S_j) \ K_j` has measure `< ε`. -/
theorem Submission.codim1_rdo_c1a_lusin_isClosed : ∀ (n : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (g : Euclid n → Y) (B : Set (Euclid n)), Measurable g → MeasurableSet B → ∀ ε : ℝ≥0∞, 0 < ε → ∃ C : Set (Euclid n), C ⊆ B ∧ IsClosed C ∧ ContinuousOn g C ∧ volume (B \ C) < ε := by
  intro n Y _ _ _ _ g B hg hB ε hε
  -- bounded Borel shells `S_j = {j ≤ ‖x‖ < j + 1}`, each of finite measure; `x ∈ S_⌊‖x‖⌋`
  set S : ℕ → Set (Euclid n) := fun j => {x | (j : ℝ) ≤ ‖x‖ ∧ ‖x‖ < j + 1}
  have hSm : ∀ j, MeasurableSet (S j) := fun j =>
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hSμ : ∀ j, volume (S j) ≠ ∞ := fun j =>
    ((measure_mono fun x hx => mem_closedBall_zero_iff.mpr hx.2.le).trans_lt
      measure_closedBall_lt_top).ne
  have hxS : ∀ x : Euclid n, x ∈ S ⌊‖x‖⌋₊ := fun x =>
    ⟨Nat.floor_le (norm_nonneg x), Nat.lt_floor_add_one _⟩
  -- weights `δ_j > 0` with `∑ δ_j < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  -- Lusin on each shell: compact `K_j ⊆ B ∩ S_j`, defect `< δ_j`, `g` continuous on `K_j`
  choose K hK hKB hKμ hKg using fun j =>
    Submission.dor_ims_lusin_measurable_continuousOn n volume (B ∩ S j) g (δ j) hg
      (hB.inter (hSm j)) (ne_top_of_le_ne_top (hSμ j) (measure_mono inter_subset_right))
      (hδ j).ne'
  -- `K_j ⊆ S_j`, so `ball x 1` meets `K_j` only for the finitely many `j < ‖x‖ + 1`
  have hlf : LocallyFinite K := by
    intro x
    refine ⟨ball x 1, ball_mem_nhds x one_pos, (finite_lt_nat ⌈‖x‖ + 1⌉₊).subset ?_⟩
    rintro j ⟨y, hyK, hyx⟩
    refine Nat.lt_ceil.mpr ((hKB j hyK).2.1.trans_lt ?_)
    calc ‖y‖ ≤ ‖x‖ + dist y x := norm_le_norm_add_const_of_dist_le le_rfl
      _ < ‖x‖ + 1 := by linarith [mem_ball.mp hyx]
  -- hence `C = ⋃ⱼ K_j` is closed and `g` is continuous on `C`
  refine ⟨⋃ j, K j, iUnion_subset fun j => (hKB j).trans inter_subset_left,
    hlf.isClosed_iUnion fun j => (hK j).isClosed,
    hlf.continuousOn_iUnion (fun j => (hK j).isClosed) hKg, ?_⟩
  -- `x ∈ B \ C` lies in `(B ∩ S_j) \ K_j` for `j = ⌊‖x‖⌋`
  calc volume (B \ ⋃ j, K j) ≤ volume (⋃ j, (B ∩ S j) \ K j) :=
        measure_mono fun x hx => mem_iUnion.mpr
          ⟨⌊‖x‖⌋₊, ⟨hx.1, hxS x⟩, fun hxK => hx.2 (mem_iUnion_of_mem _ hxK)⟩
    _ ≤ ∑' j, volume ((B ∩ S j) \ K j) := measure_iUnion_le _
    _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (hKμ j).le
    _ < ε := hδε
/-- **Egoroff's theorem** on `ℝⁿ` with a closed good set (steps 5–6 of Simon's proof of Ch. 2,
1.5).  If `C` is measurable (possibly `|C| = ∞`), `η_k` and `g` are measurable and `η_k → g`
pointwise on `C`, then for every `ε > 0` there is a closed `A ⊆ C` with `|C \ A| < ε` such that
`η_k → g` uniformly on every compact `Q ⊆ A`.  For weights `δ_j > 0` with `∑ δ_j < ε`, Egoroff on
the finite-measure sets `C ∩ B_{j+1}(0)` gives `t_j` with `|t_j| ≤ δ_j / 2`; put
`A₀ = C \ ⋃ t_j`.  Outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with excess `< δ_j / 2`,
so `A = (⋃ U_j)ᶜ ⊆ A₀` is closed and `C \ A ⊆ ⋃ (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`.  A compact
`Q ⊆ A` is bounded, so `Q ⊆ (C ∩ B_{j+1}(0)) \ t_j` for large `j`. -/
theorem Submission.codim1_rdo_c1a_egorov_isClosed : ∀ (n : ℕ) (C : Set (Euclid n)) (η : ℕ → Euclid n → ℝ) (g : Euclid n → ℝ), MeasurableSet C → (∀ k, Measurable (η k)) → Measurable g → (∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 (g x))) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → TendstoUniformlyOn η g atTop Q := by
  intro n C η g hC hη hg hconv ε hε
  -- weights `δ_j > 0` with `∑ δ_j < ε`; every `s ∩ B_{j+1}(0)` has finite measure
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have hB : ∀ (j : ℕ) (s : Set (Euclid n)), volume (s ∩ ball 0 (j + 1)) ≠ ∞ := fun j s =>
    ((measure_mono inter_subset_right).trans_lt measure_ball_lt_top).ne
  -- Egoroff on `C_j = C ∩ B_{j+1}(0)`: `η_k → g` uniformly on `C_j \ t_j`, `|t_j| ≤ δ_j / 2`
  choose t htC htm htμ htu using fun j : ℕ =>
    tendstoUniformlyOn_of_ae_tendsto (μ := volume) (fun k => (hη k).stronglyMeasurable)
      hg.stronglyMeasurable (hC.inter measurableSet_ball) (hB j C)
      (ae_of_all _ fun x hx => hconv x hx.1) (ENNReal.half_pos (hδ j).ne')
  -- `A₀ = C \ ⋃ t_j`; outer regularity gives open `U_j ⊇ A₀ᶜ ∩ B_{j+1}(0)` with small excess
  have hA₀ : MeasurableSet (C \ ⋃ j, t j) := hC.diff (MeasurableSet.iUnion htm)
  choose U hUD hUo hUf hUμ using fun j : ℕ =>
    (hA₀.compl.inter measurableSet_ball).exists_isOpen_sdiff_lt (hB j _)
      (ENNReal.half_pos (hδ j).ne').ne'
  -- the balls cover `A₀ᶜ`, so the closed set `A = (⋃ U_j)ᶜ` lies in `A₀`
  have hAA₀ : (⋃ j, U j)ᶜ ⊆ C \ ⋃ j, t j := by
    refine compl_subset_comm.1 fun x hx => ?_
    obtain ⟨j, hj⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨j, hUD j ⟨hx, mem_ball.2 (by linarith)⟩⟩
  refine ⟨(⋃ j, U j)ᶜ, hAA₀.trans sdiff_subset, (isOpen_iUnion hUo).isClosed_compl, ?_, ?_⟩
  -- `C \ A ⊆ ⋃_j (t_j ∪ (U_j \ (A₀ᶜ ∩ B_{j+1}(0))))`, and each piece has measure `≤ δ_j`
  · calc volume (C \ (⋃ j, U j)ᶜ)
        ≤ volume (⋃ j, (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1))))) := by
          refine measure_mono fun x ⟨hxC, hxU⟩ => ?_
          obtain ⟨j, hj⟩ := mem_iUnion.1 (not_not.1 hxU)
          by_cases hxt : x ∈ ⋃ i, t i
          · obtain ⟨i, hi⟩ := mem_iUnion.1 hxt
            exact mem_iUnion.2 ⟨i, Or.inl hi⟩
          · exact mem_iUnion.2 ⟨j, Or.inr ⟨hj, fun h => h.1 ⟨hxC, hxt⟩⟩⟩
      _ ≤ ∑' j, volume (t j ∪ (U j \ ((C \ ⋃ i, t i)ᶜ ∩ ball 0 (j + 1)))) :=
          measure_iUnion_le _
      _ ≤ ∑' j, δ j := ENNReal.tsum_le_tsum fun j => (measure_union_le _ _).trans <|
          (add_le_add (htμ j) (hUμ j).le).trans (ENNReal.add_halves _).le
      _ < ε := hδε
  -- a compact `Q ⊆ A` is bounded, so `Q ⊆ C_j \ t_j` for large `j`
  · intro Q hQ hQA
    obtain ⟨R, hR⟩ := hQ.isBounded.subset_ball 0
    obtain ⟨j, hj⟩ := exists_nat_ge R
    refine (htu j).mono fun x hx => ⟨⟨(hAA₀ (hQA hx)).1, ?_⟩, fun hxt => ?_⟩
    · exact ball_subset_ball (by linarith) (hR hx)
    · exact (hAA₀ (hQA hx)).2 (mem_iUnion.2 ⟨j, hxt⟩)
/-- **Whitney's hypothesis 1.6(∗) on a large closed set** (Simon Ch. 2, proof of Theorem 1.5).
Let `f : ℝⁿ → ℝ` be `L`-Lipschitz and differentiable at every point of the closed set `C`, with
`Df` continuous on `C`.  The remainder quotient `R(x, y) = |f(y) − f(x) − Df(x)(y − x)| / |y − x|`
is at most `2L`, and `η_k(x) = sup {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}` (`0` off `C`)
tends to `0` on `C`.  Each `{η_k > t}`, `t ≥ 0`, is relatively open in `C`, so `η_k` is Borel,
and Egorov's theorem in closed form gives a closed `A ⊆ C` with `Lⁿ(C \ A) < ε` such that
`η_k → 0` uniformly on every compact `Q ⊆ A`.  Then `R(x, y) ≤ η_k(x) < ε'` for `x ∈ Q`,
`y ∈ A`, `0 < |x − y| < 1/(k + 1)`. -/
theorem Submission.codim1_rdo_c1a_whitney_remainder : ∀ (n : ℕ) (f : Euclid n → ℝ) (L : NNReal) (C : Set (Euclid n)), LipschitzWith L f → IsClosed C → (∀ x ∈ C, DifferentiableAt ℝ f x) → ContinuousOn (fderiv ℝ f) C → ∀ ε : ℝ≥0∞, 0 < ε → ∃ A : Set (Euclid n), A ⊆ C ∧ IsClosed A ∧ volume (C \ A) < ε ∧ ∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ε' * ‖y - x‖ := by
  intro n f L C hf hC hdiff hDf ε hε
  classical
  -- the remainder quotient `R(x, y)`, bounded by `2L` since `‖Df(x)‖ ≤ L`
  let R : Euclid n → Euclid n → ℝ := fun x y => ‖f y - f x - fderiv ℝ f x (y - x)‖ / ‖y - x‖
  have hR_le : ∀ x y, R x y ≤ 2 * L := by
    intro x y
    refine div_le_of_le_mul₀ (norm_nonneg _) (by positivity) ?_
    calc ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ ‖f y - f x‖ + ‖fderiv ℝ f x (y - x)‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖y - x‖ + L * ‖y - x‖ := by
          refine add_le_add ?_ ?_
          · rw [← dist_eq_norm, ← dist_eq_norm]
            exact hf.dist_le_mul y x
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      _ = 2 * L * ‖y - x‖ := by ring
  -- `η_k(x) = sup E_k(x)`, `E_k(x) = {R(x, y) : y ∈ C, 0 < |y − x| < 1/(k + 1)}`, on `C`
  let E : ℕ → Euclid n → Set ℝ := fun k x =>
    R x '' {y | y ∈ C ∧ 0 < dist y x ∧ dist y x < 1 / ((k : ℝ) + 1)}
  let η : ℕ → Euclid n → ℝ := fun k x => if x ∈ C then sSup (E k x) else 0
  have hη_nonneg : ∀ k x, 0 ≤ η k x := by
    intro k x
    by_cases hx : x ∈ C
    · simp only [η, ite_eq_left hx]
      exact Real.sSup_nonneg (by
        rintro _ ⟨y, -, rfl⟩
        exact div_nonneg (norm_nonneg _) (norm_nonneg _))
    · simp only [η, ite_eq_right hx, le_refl]
  have hR_le_η : ∀ (k : ℕ) x y, x ∈ C → y ∈ C → 0 < dist y x → dist y x < 1 / ((k : ℝ) + 1) →
      R x y ≤ η k x := by
    intro k x y hx hy h0 h1
    simp only [η, ite_eq_left hx]
    exact le_csSup ⟨2 * L, by rintro _ ⟨z, -, rfl⟩; exact hR_le x z⟩ ⟨y, ⟨hy, h0, h1⟩, rfl⟩
  -- `η_k(x) → 0` for `x ∈ C`, by differentiability of `f` at `x`
  have hη_tendsto : ∀ x ∈ C, Tendsto (fun k => η k x) atTop (𝓝 0) := by
    intro x hx
    rw [Metric.tendsto_atTop]
    intro e he
    obtain ⟨ρ, hρ, hρx⟩ :=
      Metric.eventually_nhds_iff.mp ((hdiff x hx).hasFDerivAt.isLittleO.bound (half_pos he))
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hρ
    refine ⟨N, fun k hk => ?_⟩
    have hle : η k x ≤ e / 2 := by
      simp only [η, ite_eq_left hx]
      refine Real.sSup_le ?_ (half_pos he).le
      rintro _ ⟨y, ⟨-, -, h1⟩, rfl⟩
      exact div_le_of_le_mul₀ (norm_nonneg _) (half_pos he).le
        (hρx (h1.trans_le ((Nat.one_div_le_one_div hk).trans hN.le)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hη_nonneg k x)]
    exact hle.trans_lt (half_lt_self he)
  -- `{η_k > t}` is relatively open in the closed set `C` for `t ≥ 0`, so `η_k` is Borel
  have hη_meas : ∀ k, Measurable (η k) := by
    intro k
    refine measurable_of_Ioi fun t => ?_
    rcases lt_or_ge t 0 with ht | ht
    · convert MeasurableSet.univ
      exact eq_univ_of_forall fun x => ht.trans_le (hη_nonneg k x)
    have hUC : η k ⁻¹' Ioi t ⊆ C := by
      intro x hx
      by_contra hxC
      have hx' : t < η k x := hx
      simp only [η, ite_eq_right hxC] at hx'
      exact absurd hx' (not_lt.mpr ht)
    have hnhds : ∀ x ∈ η k ⁻¹' Ioi t, η k ⁻¹' Ioi t ∪ Cᶜ ∈ 𝓝 x := by
      intro x hx
      have hxC := hUC hx
      have hxt : t < sSup (E k x) := by
        have hx' : t < η k x := hx
        simpa only [η, ite_eq_left hxC] using hx'
      have hne : (E k x).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Real.sSup_empty] at hxt
        exact absurd hxt (not_lt.mpr ht)
      obtain ⟨_, ⟨y, ⟨hy, h0, h1⟩, rfl⟩, hty⟩ := exists_lt_of_lt_csSup hne hxt
      -- `z ↦ R(z, y)` is continuous within `C` at `x`, as `f` and `Df|_C` are continuous
      have hsub : ContinuousWithinAt (fun z => y - z) C x :=
        continuousWithinAt_const.sub continuousWithinAt_id
      have hnum : ContinuousWithinAt (fun z => ‖f y - f z - fderiv ℝ f z (y - z)‖) C x :=
        ((continuousWithinAt_const.sub hf.continuous.continuousWithinAt).sub
          ((hDf x hxC).clm_apply hsub)).norm
      have hRy : ContinuousWithinAt (fun z => R z y) C x :=
        hnum.div hsub.norm (norm_sub_pos_iff.mpr (dist_pos.mp h0)).ne'
      have hdist : Tendsto (fun z => dist y z) (𝓝 x) (𝓝 (dist y x)) :=
        tendsto_const_nhds.dist tendsto_id
      -- near `x`, every `z ∈ C` has `η_k(z) ≥ R(z, y) > t`
      filter_upwards [eventually_nhdsWithin_iff.mp (Filter.Tendsto.eventually_const_lt hty hRy),
        hdist.eventually_const_lt h0, hdist.eventually_lt_const h1] with z hz hz0 hz1
      by_cases hzC : z ∈ C
      · exact Or.inl ((hz hzC).trans_le (hR_le_η k z y hzC hy hz0 hz1))
      · exact Or.inr hzC
    have heq : η k ⁻¹' Ioi t = C ∩ interior (η k ⁻¹' Ioi t ∪ Cᶜ) := by
      refine Subset.antisymm
        (fun x hx => ⟨hUC hx, mem_interior_iff_mem_nhds.mpr (hnhds x hx)⟩) ?_
      rintro x ⟨hxC, hxI⟩
      rcases interior_subset hxI with hx | hx
      · exact hx
      · exact absurd hxC hx
    rw [heq]
    exact hC.measurableSet.inter isOpen_interior.measurableSet
  -- Egorov on `C`: a closed `A ⊆ C`, `Lⁿ(C \ A) < ε`, with `η_k → 0` uniformly on compact `Q ⊆ A`
  obtain ⟨A, hAC, hA, hCA, hunif⟩ := Submission.codim1_rdo_c1a_egorov_isClosed n C η
    (fun _ => 0) hC.measurableSet hη_meas measurable_const hη_tendsto ε hε
  refine ⟨A, hAC, hA, hCA, fun Q hQ hQA ε' hε' => ?_⟩
  -- `η_k < ε'` on `Q` for some `k`; take `δ = 1/(k + 1)`
  obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp (hunif Q hQ hQA) ε' hε').exists
  refine ⟨1 / ((k : ℝ) + 1), Nat.one_div_pos_of_nat, fun x hx y hy hxy => ?_⟩
  rcases eq_or_ne y x with rfl | hyx
  · simp
  have h0 : 0 < dist y x := dist_pos.mpr hyx
  have hηx : η k x < ε' := by
    have hkx := hk x hx
    rw [dist_comm, Real.dist_eq, sub_zero] at hkx
    exact (le_abs_self _).trans_lt hkx
  have hR : R x y ≤ ε' :=
    (hR_le_η k x y (hAC (hQA hx)) (hAC hy) h0 (by rwa [dist_comm])).trans hηx.le
  exact (div_le_iff₀ (norm_sub_pos_iff.mpr hyx)).mp hR
/-- **Whitney's `C¹` extension theorem** (Simon Ch. 2, 1.6; proof of Evans–Gariepy §6.5).  If
`A ⊆ ℝⁿ` is closed, `h` and `D` are continuous on `A`, and the remainder
`h y - h x - D x (y - x)` is `o(|y - x|)` uniformly for `x` in compact subsets of `A`, then some
`g ∈ C¹(ℝⁿ)` has `g = h` and `Dg = D` on `A`.  With `r x = min(1, dist(x, A)) / 100`, Vitali's
lemma selects disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `ℝⁿ \ A`;
nearby radii are comparable, so the overlap is uniformly bounded.  Rescaled bumps divided by
their locally finite sum give a partition of unity `w c` on `ℝⁿ \ A` with
`∑ ‖D(w c)(x)‖ ≤ M / r x`.  Put `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`, where
`P b x = h b + D b (x - b)` and `pr c ∈ A` is a nearest point. -/
theorem Submission.codim1_rdo_c1a_whitney_extension : ∀ (n : ℕ) (A : Set (Euclid n)) (h : Euclid n → ℝ) (D : Euclid n → (Euclid n →L[ℝ] ℝ)), IsClosed A → ContinuousOn h A → ContinuousOn D A → (∀ Q : Set (Euclid n), IsCompact Q → Q ⊆ A → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Q, ∀ y ∈ A, dist x y < δ → ‖h y - h x - D x (y - x)‖ ≤ ε * ‖y - x‖) → ∃ g : Euclid n → ℝ, ContDiff ℝ 1 g ∧ EqOn g h A ∧ ∀ a ∈ A, HasFDerivAt g (D a) a := by
  intro n A h D hA hh hD hrem
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  -- the Whitney radius `r x = min 1 (dist x A) / 100`
  obtain ⟨r, hr⟩ : ∃ r : Euclid n → ℝ, ∀ x, r x = min 1 (infDist x A) / 100 :=
    ⟨_, fun _ => rfl⟩
  have hr0 : ∀ x, 0 ≤ r x := fun x => by
    rw [hr]; exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)
  have hr1 : ∀ x, r x ≤ 1 / 100 := fun x => by
    rw [hr]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hrd : ∀ x, 100 * r x ≤ infDist x A := fun x => by
    rw [hr]; linarith [min_le_right (1 : ℝ) (infDist x A)]
  have hrpos : ∀ x, x ∉ A → 0 < r x := fun x hx => by
    rw [hr]
    exact div_pos (lt_min one_pos ((hA.notMem_iff_infDist_pos hne).mp hx)) (by norm_num)
  have hrlip : ∀ x y, r x ≤ r y + dist x y / 100 := fun x y => by
    have h₁ := ((lipschitz_infDist_pt A).const_min 1).dist_le_mul x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h₁
    have h₂ := (abs_sub_le_iff.mp h₁).1
    rw [hr, hr]; linarith
  -- radii of nearby centres are comparable
  have hnear : ∀ x c, dist x c ≤ r x + 10 * r c →
      r x / 2 ≤ r c ∧ r c ≤ 2 * r x ∧ dist x c ≤ 21 * r x := by
    intro x c hxc
    have h₁ := hrlip x c
    have h₂ := hrlip c x
    rw [dist_comm c x] at h₂
    have := hr0 x
    have := hr0 c
    exact ⟨by linarith, by linarith, by linarith⟩
  -- Vitali: disjoint balls `B(c, r c)`, `c ∈ Z`, whose fourfold enlargements cover `Aᶜ`
  obtain ⟨Z, hZA, hZdisj, hZcov⟩ : ∃ Z ⊆ Aᶜ, Z.PairwiseDisjoint (fun c => ball c (r c)) ∧
      ∀ x ∉ A, ∃ c ∈ Z, dist x c < 4 * r c := by
    obtain ⟨s, hs, hd, hc⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
      Aᶜ (fun x => x) r (1 / 100) (fun x _ => hr1 x) 4 (by norm_num)
    refine ⟨s, hs, hd, fun x hx => ?_⟩
    obtain ⟨c, hcs, hxc⟩ := hc x hx
    exact ⟨c, hcs, hxc (mem_ball_self (hrpos x hx))⟩
  have hsep : ∀ c ∈ Z, ∀ d ∈ Z, c ≠ d → r c ≤ dist c d := by
    intro c hc d hd hcd
    by_contra hlt
    have hdc : d ∈ ball c (r c) := by
      simpa only [mem_ball, dist_comm] using lt_of_not_ge hlt
    exact Set.disjoint_left.mp (hZdisj hc hd hcd) hdc (mem_ball_self (hrpos d (hZA hd)))
  -- a `1/2`-separated subset of `B̄(0, 21)` has at most `N` points
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ s : Set (Euclid n), s ⊆ closedBall (0 : Euclid n) 21 →
      s.Pairwise (fun x y => 1 / 2 ≤ dist x y) → s.Finite ∧ s.ncard ≤ N := by
    obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp
      (isCompact_closedBall (0 : Euclid n) 21).totallyBounded (1 / 4) (by norm_num)
    refine ⟨t.ncard, fun s hs hssep => ?_⟩
    have hc : ∀ x : s, ∃ y : t, dist (x : Euclid n) y < 1 / 4 := by
      intro x
      have hx := hcover (hs x.property)
      simp only [mem_iUnion, mem_ball, exists_prop] at hx
      obtain ⟨y, hyt, hxy⟩ := hx
      exact ⟨⟨y, hyt⟩, hxy⟩
    choose c hc using hc
    have hi : Injective c := by
      intro x y hxy
      by_contra hxy'
      have hne' : (x : Euclid n) ≠ (y : Euclid n) := fun e => hxy' (Subtype.ext e)
      have hd := hssep x.property y.property hne'
      have htri := dist_triangle (x : Euclid n) (c x : Euclid n) (y : Euclid n)
      have hxc := hc x
      have hyc := hc y
      rw [← hxy, dist_comm (y : Euclid n) (c x : Euclid n)] at hyc
      linarith
    have : Finite t := ht.to_subtype
    have : Finite s := Finite.of_injective c hi
    exact ⟨Set.toFinite s, Nat.card_le_card_of_injective c hi⟩
  -- bounded overlap: at most `N` centres are near any `x ∉ A`
  have hover : ∀ x ∉ A, {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.Finite ∧
      {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard ≤ N := by
    intro x hx
    have hrx : 0 < r x := hrpos x hx
    let f : Euclid n → Euclid n := fun c => (r x)⁻¹ • (c - x)
    have hf : Injective f := by
      intro c d hcd
      have e := congrArg (fun z : Euclid n => r x • z) hcd
      simpa [f, smul_smul, hrx.ne'] using e
    have hnorm : ∀ c ∈ {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}, ‖f c‖ ≤ 21 := by
      intro c hc
      have hd := (hnear x c hc.2).2.2
      rw [dist_comm, dist_eq_norm] at hd
      simp only [f]
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (r x)⁻¹ * ‖c - x‖ ≤ (r x)⁻¹ * (21 * r x) :=
            mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hrx.le)
        _ = 21 := by field_simp
    have hsep' : (f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}).Pairwise
        (fun y z => 1 / 2 ≤ dist y z) := by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ hcd
      have hcd' : c ≠ d := fun e => hcd (congrArg f e)
      have hdist := hsep c hc.1 d hd.1 hcd'
      have hrad := (hnear x c hc.2).1
      have hlow : r x / 2 ≤ ‖c - d‖ := by
        simpa only [dist_eq_norm] using hrad.trans hdist
      have hid : (c - x) - (d - x) = c - d := by abel
      simp only [f]
      rw [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hrx.le)]
      calc (1 : ℝ) / 2 = (r x)⁻¹ * (r x / 2) := by field_simp
        _ ≤ (r x)⁻¹ * ‖c - d‖ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hrx.le)
    have hsub : f '' {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c} ⊆ closedBall (0 : Euclid n) 21 := by
      rintro _ ⟨c, hc, rfl⟩
      simpa only [mem_closedBall, dist_zero_right] using hnorm c hc
    obtain ⟨hfin, hcard⟩ := hN _ hsub hsep'
    exact ⟨hfin.of_finite_image hf.injOn, by rwa [Set.ncard_image_of_injective _ hf] at hcard⟩
  -- the finite set `F x` of centres near `x ∉ A`
  have hfin : ∀ x ∉ A, {c : Z | dist x c ≤ r x + 10 * r c}.Finite := by
    intro x hx
    apply ((hover x hx).1.preimage (Subtype.val_injective (p := (· ∈ Z))).injOn).subset
    intro c hc
    exact ⟨c.property, hc⟩
  have hFex : ∀ x, ∃ s : Finset Z, x ∉ A → ∀ c : Z, c ∈ s ↔ dist x c ≤ r x + 10 * r c := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨∅, fun hx' => absurd hx hx'⟩
    · exact ⟨(hfin x hx).toFinset, fun _ c => by simp⟩
  choose F hF using hFex
  have hFcard : ∀ x ∉ A, (F x).card ≤ N := by
    intro x hx
    have hsub : (F x).map (Embedding.subtype _) ⊆ (hover x hx).1.toFinset := by
      intro c hc
      simp only [Finset.mem_map, Embedding.coe_subtype] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      rw [Set.Finite.mem_toFinset]
      exact ⟨c'.property, (hF x hx c').mp hc'⟩
    calc (F x).card = ((F x).map (Embedding.subtype _)).card := (Finset.card_map _).symm
      _ ≤ (hover x hx).1.toFinset.card := Finset.card_le_card hsub
      _ = {c | c ∈ Z ∧ dist x c ≤ r x + 10 * r c}.ncard :=
          (Set.ncard_eq_toFinset_card _ _).symm
      _ ≤ N := (hover x hx).2
  -- a smooth bump `ψ = 1` on `B̄(0, 4)`, `ψ = 0` off `B(0, 8)`
  obtain ⟨ψ, hψc, hψ0, hψ1, hψin, hψout, L, hL⟩ : ∃ ψ : Euclid n → ℝ, ContDiff ℝ 1 ψ ∧
      (∀ x, 0 ≤ ψ x) ∧ (∀ x, ψ x ≤ 1) ∧ (∀ x, ‖x‖ ≤ 4 → ψ x = 1) ∧
      (∀ x, 8 ≤ ‖x‖ → ψ x = 0) ∧ ∃ L : NNReal, LipschitzWith L ψ := by
    let b : ContDiffBump (0 : Euclid n) := ⟨4, 8, by norm_num, by norm_num⟩
    have hb : ContDiff ℝ 1 b := b.contDiff
    obtain ⟨L, hL⟩ := hb.lipschitzWith_of_hasCompactSupport b.hasCompactSupport one_ne_zero
    refine ⟨b, hb, fun x => b.nonneg, fun x => b.le_one, fun x hx => ?_, fun x hx => ?_, L, hL⟩
    · exact b.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr hx)
    · apply notMem_support.mp
      rw [b.support_eq]
      exact fun hxb => absurd (mem_ball_zero_iff.mp hxb) (not_lt.mpr hx)
  -- the rescaled bumps `φ c x = ψ ((x - c) / r c)`
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid n → Euclid n → ℝ, ∀ c x, φ c x = ψ ((r c)⁻¹ • (x - c)) :=
    ⟨_, fun _ _ => rfl⟩
  have hφfun : ∀ c, φ c = fun x => ψ ((r c)⁻¹ • (x - c)) := fun c => funext (hφ c)
  have hφc : ∀ c, ContDiff ℝ 1 (φ c) := by
    intro c
    rw [hφfun c]
    exact hψc.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hφ0 : ∀ c x, 0 ≤ φ c x := fun c x => by rw [hφ]; exact hψ0 _
  have hφin : ∀ c x, 0 < r c → dist x c ≤ 4 * r c → φ c x = 1 := by
    intro c x hc hx
    rw [hφ]
    apply hψin
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (r c)⁻¹ * dist x c ≤ (r c)⁻¹ * (4 * r c) :=
          mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
      _ = 4 := by field_simp
  have hφout : ∀ c x, 0 < r c → 8 * r c ≤ dist x c → φ c x = 0 := by
    intro c x hc hx
    rw [hφ]
    apply hψout
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← dist_eq_norm]
    calc (8 : ℝ) = (r c)⁻¹ * (8 * r c) := by field_simp
      _ ≤ (r c)⁻¹ * dist x c := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)
  obtain ⟨B, hB, hBb⟩ : ∃ B : ℝ, 0 < B ∧ ∀ c, 0 < r c → ∀ x, ‖fderiv ℝ (φ c) x‖ ≤ B / r c := by
    refine ⟨(L : ℝ) + 1, by positivity, fun c hc x => ?_⟩
    let ρ : NNReal := ⟨r c, hc.le⟩
    have hf : LipschitzWith ρ⁻¹ (fun y : Euclid n => (r c)⁻¹ • (y - c)) := by
      apply LipschitzWith.of_dist_le_mul
      intro y z
      have hid : (y - c) - (z - c) = y - z := by abel
      simp only [dist_eq_norm, ← smul_sub, hid, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hc.le), NNReal.coe_inv]
      exact le_rfl
    have hg : LipschitzWith (L * ρ⁻¹) (φ c) := by
      rw [hφfun c]
      exact hL.comp hf
    have hb := norm_fderiv_le_of_lipschitz ℝ hg (x₀ := x)
    simp only [NNReal.coe_mul, NNReal.coe_inv] at hb
    change ‖fderiv ℝ (φ c) x‖ ≤ (L : ℝ) * (r c)⁻¹ at hb
    refine hb.trans ?_
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hc.le)
  -- near `x ∉ A`, only the bumps indexed by `F x` are active
  have hφzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → φ c y = 0 := by
    intro x hx y hy c hc
    apply hφout c y (hrpos c (hZA c.property))
    have hnot : ¬ dist x c ≤ r x + 10 * r c := fun e => hc ((hF x hx c).mpr e)
    have ht := dist_triangle x y (c : Euclid n)
    rw [dist_comm x y] at ht
    have := hr0 (c : Euclid n)
    linarith
  have hyA : ∀ x ∉ A, ∀ y, dist y x < r x → y ∉ A := by
    intro x hx y hy hyA'
    have hi := infDist_le_dist_of_mem (x := x) hyA'
    have hr' := hrd x
    rw [dist_comm x y] at hi
    linarith [hr0 x]
  -- the locally finite sum `S = ∑ φ c`
  obtain ⟨S, hS⟩ : ∃ S : Euclid n → ℝ, ∀ x, S x = ∑ᶠ c : Z, φ c x := ⟨_, fun _ => rfl⟩
  have hSnear : ∀ x ∉ A, ∀ y, dist y x < r x → S y = ∑ c ∈ F x, φ c y := by
    intro x hx y hy
    rw [hS]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hcF
    exact hc (hφzero x hx y hy c hcF)
  have hSev : ∀ x ∉ A, S =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, φ c y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hSnear x hx y hy
  have hSc : ∀ x ∉ A, ContDiffAt ℝ 1 S x := fun x hx =>
    (ContDiff.sum (f := fun (c : Z) y => φ c y) (s := F x) fun c _ => hφc c).contDiffAt.congr_of_eventuallyEq
      (hSev x hx)
  have hSfd : ∀ x ∉ A, fderiv ℝ S x = ∑ c ∈ F x, fderiv ℝ (φ c) x := by
    intro x hx
    rw [(hSev x hx).fderiv_eq]
    exact fderiv_fun_sum (fun c _ => (hφc c).differentiable one_ne_zero x)
  have hS1 : ∀ x ∉ A, 1 ≤ S x := by
    intro x hx
    have hrx := hrpos x hx
    rw [hSnear x hx x (by simpa using hrx)]
    obtain ⟨c, hc, hxc⟩ := hZcov x hx
    have hi : (⟨c, hc⟩ : Z) ∈ F x := by
      rw [hF x hx]
      have := hr0 c
      show dist x c ≤ r x + 10 * r c
      linarith
    calc (1 : ℝ) = φ c x := (hφin c x (hrpos c (hZA hc)) hxc.le).symm
      _ ≤ ∑ c ∈ F x, φ c x :=
          Finset.single_le_sum (f := fun c : Z => φ c x) (fun c _ => hφ0 c x) hi
  -- the partition of unity `w c = φ c / S` on `Aᶜ`
  obtain ⟨w, hw⟩ : ∃ w : Z → Euclid n → ℝ, ∀ c x, w c x = φ c x / S x := ⟨_, fun _ _ => rfl⟩
  have hwfun : ∀ c, w c = fun x => φ c x / S x := fun c => funext (hw c)
  have hwc : ∀ c : Z, ∀ x ∉ A, ContDiffAt ℝ 1 (w c) x := by
    intro c x hx
    rw [hwfun c]
    exact (hφc c).contDiffAt.div (hSc x hx) (ne_of_gt (lt_of_lt_of_le one_pos (hS1 x hx)))
  have hw0 : ∀ c : Z, ∀ x ∉ A, 0 ≤ w c x := by
    intro c x hx
    rw [hw]
    exact div_nonneg (hφ0 c x) (le_trans zero_le_one (hS1 x hx))
  have hwzero : ∀ x ∉ A, ∀ y, dist y x < r x → ∀ c : Z, c ∉ F x → w c y = 0 := by
    intro x hx y hy c hc
    rw [hw, hφzero x hx y hy c hc, zero_div]
  have hwsum : ∀ x ∉ A, ∀ y, dist y x < r x → ∑ c ∈ F x, w c y = 1 := by
    intro x hx y hy
    simp only [hw, ← Finset.sum_div, ← hSnear x hx y hy]
    exact div_self (ne_of_gt (lt_of_lt_of_le one_pos (hS1 y (hyA x hx y hy))))
  have hwdsum : ∀ x ∉ A, ∑ c ∈ F x, fderiv ℝ (w c) x = 0 := by
    intro x hx
    have heq : (fun y => ∑ c ∈ F x, w c y) =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
      exact hwsum x hx y hy
    have hh' := heq.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_fun_const] at hh'
    rw [fderiv_fun_sum (fun c _ => (hwc c x hx).differentiableAt one_ne_zero)] at hh'
    exact hh'
  have hwd_le : ∀ x ∉ A, ∀ c : Z,
      ‖fderiv ℝ (w c) x‖ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
    intro x hx c
    have hS1x := hS1 x hx
    have hSpos : 0 < S x := lt_of_lt_of_le one_pos hS1x
    have hSi : (S x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hS1x
    have hSi2 : (S x ^ 2)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (show 1 ≤ S x ^ 2 by nlinarith)
    have hb := ((hφc c).differentiable one_ne_zero x).hasFDerivAt
    have hd := ((hSc x hx).differentiableAt one_ne_zero).hasFDerivAt
    have hi := (hasDerivAt_inv hSpos.ne').comp_hasFDerivAt x hd
    have hprod := hb.fun_mul hi
    have hder : fderiv ℝ (w c) x =
        φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x := by
      simpa only [hwfun, div_eq_mul_inv, Function.comp_def] using hprod.fderiv
    rw [hder]
    have hb0 := hφ0 c x
    have hb1 : φ c x ≤ 1 := by rw [hφ]; exact hψ1 _
    calc ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x) + (S x)⁻¹ • fderiv ℝ (φ c) x‖
        ≤ ‖φ c x • (-(S x ^ 2)⁻¹ • fderiv ℝ S x)‖ + ‖(S x)⁻¹ • fderiv ℝ (φ c) x‖ :=
          norm_add_le _ _
      _ = φ c x * ((S x ^ 2)⁻¹ * ‖fderiv ℝ S x‖) + (S x)⁻¹ * ‖fderiv ℝ (φ c) x‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hb0, norm_neg,
            Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x))),
            Real.norm_of_nonneg (inv_nonneg.mpr hSpos.le)]
      _ ≤ ‖fderiv ℝ (φ c) x‖ + ‖fderiv ℝ S x‖ := by
          have h₁ := mul_le_mul_of_nonneg_right hSi (norm_nonneg (fderiv ℝ (φ c) x))
          have h₂ := mul_le_mul_of_nonneg_right hSi2 (norm_nonneg (fderiv ℝ S x))
          have h₃ := mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (norm_nonneg (fderiv ℝ S x)))
          linarith
  -- `∑_{c ∈ F x} ‖D w_c(x)‖ ≤ M / r x`
  obtain ⟨M, hM, hMb⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∉ A, ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ M / r x := by
    refine ⟨2 * B * ((N : ℝ) + 1) ^ 2, by positivity, fun x hx => ?_⟩
    have hrx := hrpos x hx
    obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = 2 * B / r x := ⟨_, rfl⟩
    have hT : 0 ≤ T := by rw [hT_def]; positivity
    have hb' : ∀ c ∈ F x, ‖fderiv ℝ (φ c) x‖ ≤ T := by
      intro c hc
      have hcr := hrpos c (hZA c.property)
      have hlow := (hnear x c ((hF x hx c).mp hc)).1
      refine (hBb c hcr x).trans ?_
      calc B / r c ≤ B / (r x / 2) := div_le_div_of_nonneg_left hB.le (half_pos hrx) hlow
        _ = T := by rw [hT_def]; ring
    have hcard : ((F x).card : ℝ) ≤ N := by exact_mod_cast hFcard x hx
    have hsum : ‖fderiv ℝ S x‖ ≤ (N : ℝ) * T := by
      rw [hSfd x hx]
      calc ‖∑ c ∈ F x, fderiv ℝ (φ c) x‖ ≤ ∑ c ∈ F x, ‖fderiv ℝ (φ c) x‖ := norm_sum_le _ _
        _ ≤ ∑ _c ∈ F x, T := Finset.sum_le_sum hb'
        _ = ((F x).card : ℝ) * T := by simp
        _ ≤ (N : ℝ) * T := mul_le_mul_of_nonneg_right hcard hT
    have hw' : ∀ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ T + (N : ℝ) * T := fun c hc =>
      (hwd_le x hx c).trans (add_le_add (hb' c hc) hsum)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    calc ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ ≤ ∑ _c ∈ F x, (T + (N : ℝ) * T) := Finset.sum_le_sum hw'
      _ = ((F x).card : ℝ) * (T + (N : ℝ) * T) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ) * (T + (N : ℝ) * T) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ ((N : ℝ) + 1) ^ 2 * T := by nlinarith [mul_nonneg (add_nonneg hN0 zero_le_one) hT]
      _ = 2 * B * ((N : ℝ) + 1) ^ 2 / r x := by rw [hT_def]; ring
  -- the affine jets `P b x = h b + D b (x - b)`
  obtain ⟨P, hP⟩ : ∃ P : Euclid n → Euclid n → ℝ, ∀ b x, P b x = h b + D b (x - b) :=
    ⟨_, fun _ _ => rfl⟩
  have hPfun : ∀ b, P b = fun x => h b + D b (x - b) := fun b => funext (hP b)
  have hPc : ∀ b, ContDiff ℝ 1 (P b) := by
    intro b
    rw [hPfun b]
    exact contDiff_const.add ((D b).contDiff.comp (contDiff_id.sub contDiff_const))
  have hPd : ∀ b x, HasFDerivAt (P b) (D b) x := by
    intro b x
    have e := (((D b).hasFDerivAt (x := x)).sub_const (D b b)).const_add (h b)
    have hfun : (fun y => h b + D b (y - b)) = fun y => h b + (D b y - D b b) := by
      funext y
      rw [map_sub]
    rw [hPfun b, hfun]
    exact e
  have hPsub : ∀ a b x,
      ‖P b x - P a x‖ ≤ ‖h b - h a - D a (b - a)‖ + ‖D b - D a‖ * ‖x - b‖ := by
    intro a b x
    have heq : P b x - P a x = (h b - h a - D a (b - a)) + (D b - D a) (x - b) := by
      have hx : x - a = (x - b) + (b - a) := by abel
      simp only [hP, hx, map_add, sub_apply]
      ring
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((D b - D a).le_opNorm (x - b)))
  -- nearest points `pr x ∈ A`
  choose pr hprA hprd using fun x => hA.exists_infDist_eq_dist hne x
  have hprle : ∀ x, ∀ a ∈ A, dist x (pr x) ≤ dist x a := by
    intro x a ha
    rw [← hprd x]
    exact infDist_le_dist_of_mem ha
  have hpr2 : ∀ x, ∀ a ∈ A, dist (pr x) a ≤ 2 * dist x a := by
    intro x a ha
    have ht := dist_triangle (pr x) x a
    rw [dist_comm (pr x) x] at ht
    linarith [hprle x a ha]
  have hanc1 : ∀ x ∉ A, ∀ c : Z, c ∈ F x → dist x (pr c) ≤ 2 * infDist x A := by
    intro x hx c hc
    have hd := (hnear x c ((hF x hx c).mp hc)).2.2
    have hr' := hrd x
    have hi := infDist_le_infDist_add_dist (s := A) (x := (c : Euclid n)) (y := x)
    have ht := dist_triangle x (c : Euclid n) (pr c)
    rw [dist_comm (c : Euclid n) x] at hi
    rw [← hprd (c : Euclid n)] at ht
    linarith [infDist_nonneg (x := x) (s := A)]
  have hanc2 : ∀ x ∉ A, ∀ a ∈ A, ∀ c : Z, c ∈ F x → dist (pr c) a ≤ 3 * dist x a := by
    intro x hx a ha c hc
    have hd := hanc1 x hx c hc
    have hi := infDist_le_dist_of_mem (x := x) ha
    have ht := dist_triangle (pr c) x a
    rw [dist_comm (pr c) x] at ht
    linarith
  -- uniform estimates near a point of `A`
  have hloc : ∀ a ∈ A, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (∀ b ∈ A, dist b a < δ → ‖D b - D a‖ ≤ η) ∧
      ∀ b ∈ A, dist b a < δ → ∀ c ∈ A, dist c a < δ →
        ‖h c - h b - D b (c - b)‖ ≤ η * ‖c - b‖ := by
    intro a ha η hη
    obtain ⟨r₀, hr₀, hrem₀⟩ := hrem (A ∩ closedBall a 1)
      ((isCompact_closedBall a 1).inter_left hA) inter_subset_left η hη
    obtain ⟨η₀, hη₀, hD₀⟩ := Metric.continuousWithinAt_iff.mp (hD a ha) η hη
    have hδ1 : min 1 (min η₀ (r₀ / 3)) ≤ 1 := min_le_left _ _
    have hδη : min 1 (min η₀ (r₀ / 3)) ≤ η₀ := (min_le_right _ _).trans (min_le_left _ _)
    have hδr : min 1 (min η₀ (r₀ / 3)) ≤ r₀ / 3 := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨min 1 (min η₀ (r₀ / 3)), lt_min one_pos (lt_min hη₀ (by positivity)), hδ1, ?_, ?_⟩
    · intro b hb hba
      simpa only [dist_eq_norm] using (hD₀ hb (hba.trans_le hδη)).le
    · intro b hb hba c hc hca
      apply hrem₀ b ⟨hb, mem_closedBall.mpr (hba.le.trans hδ1)⟩ c hc
      have htri := dist_triangle b a c
      rw [dist_comm a c] at htri
      linarith
  -- convex combinations
  have hconv : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (s : Finset Z)
      (a : Z → ℝ) (v : Z → G) (b : ℝ), (∀ i ∈ s, 0 ≤ a i) → ∑ i ∈ s, a i = 1 →
      (∀ i ∈ s, ‖v i‖ ≤ b) → ‖∑ i ∈ s, a i • v i‖ ≤ b := by
    intro G _ _ s a v b ha hs hv
    calc ‖∑ i ∈ s, a i • v i‖ ≤ ∑ i ∈ s, ‖a i • v i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, a i * ‖v i‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_of_nonneg (ha i hi)]
      _ ≤ ∑ i ∈ s, a i * b :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hv i hi) (ha i hi)
      _ = b := by rw [← Finset.sum_mul, hs, one_mul]
  -- the extension: `g = h` on `A` and `g = ∑ w c • P (pr c)` off `A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid n → ℝ, ∀ x,
      g x = if x ∈ A then h x else ∑ᶠ c : Z, w c x * P (pr c) x := ⟨_, fun _ => rfl⟩
  have hgA : ∀ a ∈ A, g a = h a := fun a ha => by rw [hg, ite_eq_left ha]
  have hgnear : ∀ x ∉ A, ∀ y, dist y x < r x → g y = ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx y hy
    rw [hg, ite_eq_right (hyA x hx y hy)]
    apply finsum_eq_sum_of_support_subset
    intro c hc
    by_contra hc'
    apply hc
    show w c y * P (pr c) y = 0
    rw [hwzero x hx y hy c hc', zero_mul]
  have hgev : ∀ x ∉ A, g =ᶠ[𝓝 x] fun y => ∑ c ∈ F x, w c y * P (pr c) y := by
    intro x hx
    filter_upwards [ball_mem_nhds x (hrpos x hx)] with y hy
    exact hgnear x hx y hy
  have hgc : ∀ x ∉ A, ContDiffAt ℝ 1 g x := by
    intro x hx
    have hs : ContDiffAt ℝ 1 (fun y => ∑ c ∈ F x, w c y * P (pr c) y) x :=
      ContDiffAt.sum (fun c _ => (hwc c x hx).mul (hPc _).contDiffAt)
    exact hs.congr_of_eventuallyEq (hgev x hx)
  have hgfd : ∀ x ∉ A, fderiv ℝ g x =
      ∑ c ∈ F x, (w c x • D (pr c) + P (pr c) x • fderiv ℝ (w c) x) := by
    intro x hx
    rw [(hgev x hx).fderiv_eq]
    apply HasFDerivAt.fderiv
    apply HasFDerivAt.fun_sum
    intro c _
    exact ((hwc c x hx).differentiableAt one_ne_zero).hasFDerivAt.fun_mul (hPd _ x)
  -- `Dg = D` on `A`
  have hgd : ∀ a ∈ A, HasFDerivAt g (D a) a := by
    intro a ha
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have he : 0 < ε / 5 := by positivity
    obtain ⟨δ, hδ, -, hDδ, hremδ⟩ := hloc a ha (ε / 5) he
    have haa : dist a a < δ := by simpa using hδ
    filter_upwards [ball_mem_nhds a (show 0 < δ / 4 by positivity)] with x hx
    have hxa : dist x a < δ / 4 := hx
    rw [hgA a ha]
    by_cases hxA : x ∈ A
    · rw [hgA x hxA]
      have hr' := hremδ a ha haa x hxA (by linarith)
      exact hr'.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    · have hxx : dist x x < r x := by simpa using hrpos x hxA
      have hid : g x - h a - D a (x - a) = ∑ c ∈ F x, w c x • (P (pr c) x - P a x) := by
        rw [hgnear x hxA x hxx]
        simp only [smul_eq_mul, mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hwsum x hxA x hxx, one_mul, hP a x]
        ring
      rw [hid]
      apply hconv (F x) (fun c => w c x) (fun c => P (pr c) x - P a x) _
        (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx)
      intro c hc
      have hbA := hprA (c : Euclid n)
      have hba := hanc2 x hxA a ha c hc
      have hxb : dist x (pr c) ≤ 2 * dist x a :=
        (hanc1 x hxA c hc).trans
          (mul_le_mul_of_nonneg_left (infDist_le_dist_of_mem ha) (by norm_num))
      have hbaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr c) hbA hbaδ
      have hr' := hremδ a ha haa (pr c) hbA hbaδ
      have hba' : ‖pr c - a‖ ≤ 3 * ‖x - a‖ := by simpa only [dist_eq_norm] using hba
      have hxb' : ‖x - pr c‖ ≤ 2 * ‖x - a‖ := by simpa only [dist_eq_norm] using hxb
      calc ‖P (pr c) x - P a x‖
          ≤ ‖h (pr c) - h a - D a (pr c - a)‖ + ‖D (pr c) - D a‖ * ‖x - pr c‖ :=
            hPsub a (pr c) x
        _ ≤ (ε / 5) * ‖pr c - a‖ + (ε / 5) * ‖x - pr c‖ :=
            add_le_add hr' (mul_le_mul_of_nonneg_right hDb (norm_nonneg _))
        _ ≤ (ε / 5) * (3 * ‖x - a‖) + (ε / 5) * (2 * ‖x - a‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hba' he.le)
              (mul_le_mul_of_nonneg_left hxb' he.le)
        _ = ε * ‖x - a‖ := by ring
  -- `Dg` is continuous at the points of `A`
  have hgcont : ∀ a ∈ A, ContinuousAt (fderiv ℝ g) a := by
    intro a ha
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (2 * (1 + 700 * M)) := ⟨_, rfl⟩
    have hη : 0 < η := by rw [hη_def]; positivity
    have heq : η * (1 + 700 * M) = ε / 2 := by rw [hη_def]; field_simp
    have hηε : η ≤ ε / 2 := by nlinarith [mul_pos hη hM]
    obtain ⟨δ, hδ, hδ1, hDδ, hremδ⟩ := hloc a ha η hη
    refine ⟨δ / 4, by positivity, fun {x} hxa => ?_⟩
    rw [(hgd a ha).fderiv, dist_eq_norm]
    apply lt_of_le_of_lt (b := ε / 2) ?_ (by linarith)
    by_cases hxA : x ∈ A
    · rw [(hgd x hxA).fderiv]
      exact (hDδ x hxA (by linarith)).trans hηε
    · have hrx := hrpos x hxA
      have hxx : dist x x < r x := by simpa using hrx
      have hbA := hprA x
      have hbaδ : dist (pr x) a < δ := by
        linarith [hpr2 x a ha, dist_nonneg (x := x) (y := a)]
      have hDb := hDδ (pr x) hbA hbaδ
      have hdx : infDist x A ≤ 1 := by
        have hi := infDist_le_dist_of_mem (x := x) ha
        linarith
      have hscale : infDist x A = 100 * r x := by
        rw [hr x, min_eq_right hdx]
        ring
      have hD' : ∀ c ∈ F x, ‖D (pr c) - D a‖ ≤ η := by
        intro c hc
        apply hDδ _ (hprA c)
        have hi := hanc2 x hxA a ha c hc
        linarith [dist_nonneg (x := x) (y := a)]
      have hP' : ∀ c ∈ F x, ‖P (pr c) x - P (pr x) x‖ ≤ 700 * η * r x := by
        intro c hc
        have hdA := hprA (c : Euclid n)
        have hda := hanc2 x hxA a ha c hc
        have hdaδ : dist (pr c) a < δ := by linarith [dist_nonneg (x := x) (y := a)]
        have hxd := hanc1 x hxA c hc
        have hxb : dist x (pr x) = infDist x A := (hprd x).symm
        have hdb : dist (pr c) (pr x) ≤ 3 * infDist x A := by
          have ht := dist_triangle (pr c) x (pr x)
          rw [dist_comm (pr c) x, hxb] at ht
          linarith
        have hDd : ‖D (pr c) - D (pr x)‖ ≤ 2 * η := by
          calc ‖D (pr c) - D (pr x)‖ = ‖(D (pr c) - D a) - (D (pr x) - D a)‖ := by
                congr 1; abel
            _ ≤ ‖D (pr c) - D a‖ + ‖D (pr x) - D a‖ := norm_sub_le _ _
            _ ≤ η + η := add_le_add (hD' c hc) hDb
            _ = 2 * η := by ring
        have hre := hremδ (pr x) hbA hbaδ (pr c) hdA hdaδ
        have hdb' : ‖pr c - pr x‖ ≤ 3 * infDist x A := by
          simpa only [dist_eq_norm] using hdb
        have hxd' : ‖x - pr c‖ ≤ 2 * infDist x A := by simpa only [dist_eq_norm] using hxd
        calc ‖P (pr c) x - P (pr x) x‖
            ≤ ‖h (pr c) - h (pr x) - D (pr x) (pr c - pr x)‖ +
                ‖D (pr c) - D (pr x)‖ * ‖x - pr c‖ := hPsub (pr x) (pr c) x
          _ ≤ η * ‖pr c - pr x‖ + (2 * η) * ‖x - pr c‖ :=
              add_le_add hre (mul_le_mul_of_nonneg_right hDd (norm_nonneg _))
          _ ≤ η * (3 * infDist x A) + (2 * η) * (2 * infDist x A) :=
              add_le_add (mul_le_mul_of_nonneg_left hdb' hη.le)
                (mul_le_mul_of_nonneg_left hxd' (by positivity))
          _ = 700 * η * r x := by rw [hscale]; ring
      have hsplit : fderiv ℝ g x - D a = (∑ c ∈ F x, w c x • (D (pr c) - D a)) +
          ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x := by
        rw [hgfd x hxA]
        simp_rw [smul_sub, sub_smul]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_smul, ← Finset.smul_sum, hwsum x hxA x hxx, hwdsum x hxA,
          one_smul, smul_zero, sub_zero]
        abel
      rw [hsplit]
      calc ‖(∑ c ∈ F x, w c x • (D (pr c) - D a)) +
            ∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
          ≤ ‖∑ c ∈ F x, w c x • (D (pr c) - D a)‖ +
              ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ := norm_add_le _ _
        _ ≤ η + (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ := by
            apply add_le_add
            · exact hconv (F x) (fun c => w c x) (fun c => D (pr c) - D a) η
                (fun c _ => hw0 c x hxA) (hwsum x hxA x hxx) hD'
            · calc ‖∑ c ∈ F x, (P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖
                  ≤ ∑ c ∈ F x, ‖(P (pr c) x - P (pr x) x) • fderiv ℝ (w c) x‖ :=
                    norm_sum_le _ _
                _ ≤ ∑ c ∈ F x, (700 * η * r x) * ‖fderiv ℝ (w c) x‖ := by
                    apply Finset.sum_le_sum
                    intro c hc
                    rw [norm_smul]
                    exact mul_le_mul_of_nonneg_right (hP' c hc) (norm_nonneg _)
                _ = (700 * η * r x) * ∑ c ∈ F x, ‖fderiv ℝ (w c) x‖ :=
                    (Finset.mul_sum ..).symm
        _ ≤ η + (700 * η * r x) * (M / r x) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left (hMb x hxA) (by positivity))
        _ = η * (1 + 700 * M) := by field_simp
        _ = ε / 2 := heq
  refine ⟨g, ?_, fun a ha => hgA a ha, hgd⟩
  refine contDiff_one_iff_fderiv.mpr ⟨fun x => ?_, continuous_iff_continuousAt.mpr fun x => ?_⟩
  · by_cases hx : x ∈ A
    · exact (hgd x hx).differentiableAt
    · exact (hgc x hx).differentiableAt one_ne_zero
  · by_cases hx : x ∈ A
    · exact hgcont x hx
    · exact (hgc x hx).continuousAt_fderiv one_ne_zero

/-- **`C¹` approximation of Lipschitz functions** (Simon Ch. 2, Theorem 1.5, the part about
values).  If `u : ℝᵐ → ℝ` is `K`-Lipschitz and `ε > 0`, some `G ∈ C¹(ℝᵐ)` agrees with `u` off a
set of measure `< ε`.  By Rademacher's theorem, the Borel set `B` of points where `u` is
differentiable has null complement, and `Du` is Borel.  Lusin's theorem gives a closed `C ⊆ B`,
`Lᵐ(B \ C) < ε / 2`, on which `Du` is continuous.  Egorov's theorem applied to the Whitney
remainders gives a closed `A ⊆ C`, `Lᵐ(C \ A) < ε / 2`, on which `(u, Du)` satisfies Whitney's
condition 1.6(∗).  Whitney's extension theorem gives `G ∈ C¹` with `G = u` on `A`, and
`{u ≠ G} ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`. -/
theorem Submission.dor_lmbsf_lipschitz_c1_approx : ∀ (m : ℕ) (u : Euclid m → ℝ) (K : NNReal), LipschitzWith K u → ∀ ε : ℝ≥0∞, 0 < ε → ∃ G : Euclid m → ℝ, ContDiff ℝ 1 G ∧ volume {y | u y ≠ G y} < ε := by
  intro m u K hu ε hε
  -- Rademacher: the Borel set `B` of differentiability points of `u` has null complement
  set B : Set (Euclid m) := {x | DifferentiableAt ℝ u x}
  have hB : MeasurableSet B := measurableSet_of_differentiableAt ℝ u
  have hBc : volume Bᶜ = 0 := ae_iff.mp hu.ae_differentiableAt
  -- Lusin: a closed `C ⊆ B`, `Lᵐ(B \ C) < ε / 2`, on which `Du` is continuous
  obtain ⟨C, hCB, hC, hDC, hBC⟩ := Submission.codim1_rdo_c1a_lusin_isClosed m (fderiv ℝ u) B
    (measurable_fderiv ℝ u) hB (ε / 2) (ENNReal.half_pos hε.ne')
  -- Egorov on the Whitney remainders: a closed `A ⊆ C`, `Lᵐ(C \ A) < ε / 2`, satisfying 1.6(∗)
  obtain ⟨A, hAC, hA, hCA, hrem⟩ := Submission.codim1_rdo_c1a_whitney_remainder m u K C hu hC
    (fun x hx => hCB hx) hDC (ε / 2) (ENNReal.half_pos hε.ne')
  -- Whitney's extension theorem: `G ∈ C¹` with `G = u` on `A`
  obtain ⟨G, hG, hGA, -⟩ := Submission.codim1_rdo_c1a_whitney_extension m A u (fderiv ℝ u) hA
    hu.continuous.continuousOn (hDC.mono hAC) hrem
  refine ⟨G, hG, ?_⟩
  -- `{u ≠ G} ⊆ Aᶜ ⊆ Bᶜ ∪ (B \ C) ∪ (C \ A)`
  calc volume {y | u y ≠ G y} ≤ volume (Bᶜ ∪ ((B \ C) ∪ (C \ A))) := by
        refine measure_mono fun y hy => ?_
        have hyA : y ∉ A := fun hyA => hy (hGA hyA).symm
        by_cases hyB : y ∈ B
        · by_cases hyC : y ∈ C
          · exact Or.inr (Or.inr ⟨hyC, hyA⟩)
          · exact Or.inr (Or.inl ⟨hyB, hyC⟩)
        · exact Or.inl hyB
    _ ≤ volume Bᶜ + (volume (B \ C) + volume (C \ A)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ < ε / 2 + ε / 2 := by
        rw [hBc, zero_add]
        exact ENNReal.add_lt_add hBC hCA
    _ = ε := ENNReal.add_halves ε

/-- **Simon Ch. 3, Lemma 1.2, "only if" part** (chapter-03.txt lines 22–65): a countably
`m`-rectifiable `M ⊆ ℝᴾ` lies in `N₀ ∪ ⋃ₗ Nₗ` with `Hᵐ(N₀) = 0` and each `Nₗ` an embedded
`m`-dimensional `C¹` submanifold.  Write `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝᵐ)` with `Hᵐ(M₀) = 0` and `Fⱼ`
Lipschitz.  The `C¹` approximation theorem (Simon Ch. 2, Theorem 1.5) gives `C¹` maps `G_{ji}`
with `Fⱼ(ℝᵐ) ⊆ Eⱼ ∪ ⋃ᵢ G_{ji}(ℝᵐ)` and `Hᵐ(Eⱼ) = 0`.  Each `G_{ji}(ℝᵐ)` lies in an `Hᵐ`-null set
`N₀_{ji}` (the critical image, by the area formula) together with countably many submanifolds
`N_{jis}` (images of small balls about regular points).  Take
`N₀ = M₀ ∪ ⋃ⱼ Eⱼ ∪ ⋃_{j,i} N₀_{ji}` and `Nₗ = N_{jis}` for `l = Nat.pair j (Nat.pair i s)`. -/
theorem Submission.dor_lmbsf_rectifiable_c1_cover : ∀ (P m : ℕ) (M : Set (Euclid P)), CountablyRectifiable m M → ∃ (N₀ : Set (Euclid P)) (N : ℕ → Set (Euclid P)), μHE[m] N₀ = 0 ∧ (∀ l, IsEmbeddedSubmanifold 1 m (N l)) ∧ M ⊆ N₀ ∪ ⋃ l, N l := by
  intro P m M hM
  -- Step 1: `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝᵐ)` with `Hᵐ(M₀) = 0` and `Fⱼ` `Kⱼ`-Lipschitz
  obtain ⟨M₀, hM₀, F, hF, hMF⟩ := hM
  choose K hK using hF
  -- Steps 2–3: `Fⱼ(ℝᵐ) ⊆ Eⱼ ∪ ⋃ᵢ G_{ji}(ℝᵐ)` with `Hᵐ(Eⱼ) = 0` and `G_{ji}` `C¹`
  choose E G hE hG hFG using fun j =>
    Submission.dor_lmbsf_c1c_lipschitz_range_c1_pieces P m (F j) (K j) (hK j)
      (Submission.dor_lmbsf_lipschitz_c1_approx m)
  -- Steps 4–6: `G_{ji}(ℝᵐ) ⊆ N₀_{ji} ∪ ⋃ₛ N_{jis}` with `Hᵐ(N₀_{ji}) = 0` and `N_{jis}`
  -- embedded `C¹` submanifolds
  choose N₀' N' hN₀' hN' hGN using fun j i =>
    Submission.dor_lmbsf_c1c_c1_range_cover P m (G j i) (hG j i)
  -- Step 7: collect the null sets and enumerate the submanifolds by `l = ⟨j, ⟨i, s⟩⟩`
  refine ⟨M₀ ∪ (⋃ j, E j) ∪ ⋃ j, ⋃ i, N₀' j i,
    fun l => N' l.unpair.1 l.unpair.2.unpair.1 l.unpair.2.unpair.2,
    measure_union_null (measure_union_null hM₀ (measure_iUnion_null hE))
      (measure_iUnion_null fun j => measure_iUnion_null (hN₀' j)),
    fun l => hN' _ _ _, ?_⟩
  intro y hy
  rcases hMF hy with hy | hy
  · exact Or.inl (Or.inl (Or.inl hy))
  obtain ⟨j, hj⟩ := mem_iUnion.1 hy
  rcases hFG j hj with hy | hy
  · exact Or.inl (Or.inl (Or.inr (mem_iUnion.2 ⟨j, hy⟩)))
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  rcases hGN j i hi with hy | hy
  · exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨j, i, hy⟩))
  obtain ⟨s, hs⟩ := mem_iUnion.1 hy
  refine Or.inr (mem_iUnion.2 ⟨Nat.pair j (Nat.pair i s), ?_⟩)
  simpa only [Nat.unpair_pair] using hs
/-- **Local `C¹` globalization by a bump cutoff** (the cut-off step letting the globally `C¹`
results apply to a map that is only `C¹` on an open set).  Let `W` be open, `χ` be `C¹` on `W`
and `y ∈ W`; choose `B_ρ(y) ⊆ W` and the smooth bump `φ` centred at `y` with `φ = 1` on
`B̄_{ρ/4}(y)` and `tsupport φ = B̄_{ρ/2}(y) ⊆ W`.  Then `g = φ χ` is `C¹` near points of `W`
(product of a `C^∞` and a `C¹` map) and vanishes near points outside `W`, so `g` is `C¹` on
`ℝᵏ`; and `g = χ` on `B_ε(y)`, `ε = ρ/4`. -/
theorem Submission.dor_lmbsf_cit_c1_local_extension : ∀ (P k : ℕ) (W : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen W → ContDiffOn ℝ 1 χ W → y ∈ W → ∃ (g : Euclid k → Euclid P) (ε : ℝ), 0 < ε ∧ ball y ε ⊆ W ∧ ContDiff ℝ 1 g ∧ EqOn g χ (ball y ε) := by
  intro P k W χ y hW hχ hy
  -- Step 1, a ball `B_ρ(y) ⊆ W`.
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hW y hy
  -- Step 2, the bump `φ`: `φ = 1` on `B̄_{ρ/4}(y)` and `tsupport φ = B̄_{ρ/2}(y) ⊆ W`.
  let φ : ContDiffBump y := ⟨ρ / 4, ρ / 2, by positivity, by linarith⟩
  have hsupp : tsupport φ ⊆ W := by
    rw [φ.tsupport_eq]
    exact (closedBall_subset_ball (by change ρ / 2 < ρ; linarith)).trans hball
  -- Step 3, `g = φ χ` and `ε = ρ/4`, so `B_ε(y) ⊆ W`.
  refine ⟨fun x => φ x • χ x, ρ / 4, by positivity,
    (ball_subset_ball (by linarith)).trans hball, ?_, fun x hx => ?_⟩
  · -- Steps 4–6, `g` is `C¹` at every point.
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x ∈ W
    · -- Step 4, on `W`, `g` is the product of the `C^∞` map `φ` and the `C¹` map `χ`.
      exact φ.contDiffAt.fun_smul (hχ.contDiffAt (hW.mem_nhds hx))
    · -- Step 5, off `W`, `x ∉ tsupport φ` and `g = 0` near `x`.
      refine (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport φ).compl_mem_nhds fun h => hx (hsupp h)] with z hz
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul]
  · -- `φ = 1` on `B_ε(y) ⊆ B̄_{ρ/4}(y)`, so `g = χ` there.
    change φ x • χ x = χ x
    rw [φ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]
/-- **Simon Ch. 3, Lemma 1.2** (the inverse-function step of the "only if" part): if `G` is `C¹`
and `DG(x)` is injective, then `μ |a − b| ≤ |G(a) − G(b)|` on some ball `B_δ(x)`.  With
`|v| ≤ K |DG(x) v|` and `μ = 1/(2K)`, strict differentiability gives
`|G(a) − G(b) − DG(x)(a − b)| ≤ μ |a − b|` near `x`, so `|G(a) − G(b)| ≥ 2μ|a − b| − μ|a − b|`. -/
theorem Submission.codim1_rdo_c1cov_local_lower_lipschitz : ∀ (P n : ℕ) (G : Euclid n → Euclid P) (x : Euclid n), ContDiff ℝ 1 G → Injective (fderiv ℝ G x) → ∃ δ μ : ℝ, 0 < δ ∧ 0 < μ ∧ ∀ a ∈ ball x δ, ∀ b ∈ ball x δ, μ * ‖a - b‖ ≤ ‖G a - G b‖ := by
  intro P n G x hG hinj
  -- `L = DG(x)` is injective on the finite-dimensional `ℝⁿ`: `‖v‖ ≤ K ‖L v‖`
  obtain ⟨K, hK, hKL⟩ := (fderiv ℝ G x).injective_iff_antilipschitz.mp hinj
  have hbound : ∀ v, ‖v‖ ≤ K * ‖fderiv ℝ G x v‖ :=
    (fderiv ℝ G x).bound_of_antilipschitz hKL
  -- `μ = 1/(2K)`, so `‖L v‖ ≥ 2μ ‖v‖`
  set μ : ℝ := (2 * K)⁻¹ with hμ
  have hK' : (0 : ℝ) < K := hK
  have hμ0 : 0 < μ := by positivity
  -- `G` is `C¹`, so `L` is a strict derivative: `G` approximates `L` with constant `μ` near `x`
  obtain ⟨s, hs, hGs⟩ := (hG.contDiffAt.hasStrictFDerivAt one_ne_zero).approximates_deriv_on_nhds
    (c := ⟨μ, hμ0.le⟩) (Or.inr hμ0)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨δ, μ, hδ, hμ0, fun a ha b hb => ?_⟩
  have h1 : ‖G a - G b - fderiv ℝ G x (a - b)‖ ≤ μ * ‖a - b‖ := hGs a (hδs ha) b (hδs hb)
  have h2 : 2 * μ * ‖a - b‖ ≤ ‖fderiv ℝ G x (a - b)‖ := by
    calc 2 * μ * ‖a - b‖ ≤ 2 * μ * (K * ‖fderiv ℝ G x (a - b)‖) := by
          gcongr
          exact hbound (a - b)
      _ = ‖fderiv ℝ G x (a - b)‖ := by
          rw [hμ]
          field_simp
  -- triangle inequality: `‖L (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - L (a - b)‖`
  have h3 : ‖fderiv ℝ G x (a - b)‖ ≤ ‖G a - G b‖ + ‖G a - G b - fderiv ℝ G x (a - b)‖ := by
    simpa using norm_sub_le (G a - G b) (G a - G b - fderiv ℝ G x (a - b))
  linarith
/-- A lower Lipschitz bound at a point passes to the derivative (step 1 of the `C¹`-piece tangent
argument, Simon Ch. 3, 1.6): if `U` is open, `a ∈ U`, `g` is differentiable at `a` and
`m|x − a| ≤ |g(x) − g(a)|` on `U`, then `m|v| ≤ |Dg(a)v|`.  For small `t > 0`, `a + tv ∈ U`
gives `m|v| ≤ |t⁻¹(g(a + tv) − g(a))|`, and the quotients tend to `Dg(a)v` as `t ↓ 0`. -/
theorem Submission.codim1_rdo_c1pt_fderiv_lower_bound : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (U : Set (Euclid n)) (a : Euclid n) (m : ℝ), IsOpen U → a ∈ U → DifferentiableAt ℝ g a → (∀ x ∈ U, m * ‖x - a‖ ≤ ‖g x - g a‖) → ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := by
  intro P n g U a m hU ha hg hm v
  -- difference quotients `q(t) = t⁻¹ • (g (a + t • v) - g a)` tend to `Dg(a) v` as `t ↓ 0`
  have hq : Tendsto (fun t : ℝ => t⁻¹ • (g (a + t • v) - g a)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ g a v)) := by
    simpa only [inv_inv] using hg.hasFDerivAt.lim v (c := fun t : ℝ => t⁻¹)
      (tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero)
  -- `a + t • v → a` as `t → 0`, so `a + t • v ∈ U` for small `t` (`U` is a neighbourhood of `a`)
  have hline : Tendsto (fun t : ℝ => a + t • v) (𝓝 0) (𝓝 a) :=
    (continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 a (by simp)
  -- for small `t > 0`: `t * (m‖v‖) ≤ ‖g (a + t • v) - g a‖`, i.e. `m‖v‖ ≤ ‖q(t)‖`
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), m * ‖v‖ ≤ ‖t⁻¹ • (g (a + t • v) - g a)‖ := by
    filter_upwards [nhdsWithin_le_nhds (hline (hU.mem_nhds ha)), self_mem_nhdsWithin]
      with t htU ht
    have ht : (0 : ℝ) < t := ht
    have h := hm _ htU
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le, mul_left_comm] at h
    rwa [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), le_inv_mul_iff₀ ht]
  -- the non-strict inequality passes to the limit along the nontrivial filter `𝓝[>] 0`
  exact ge_of_tendsto hq.norm hle
/-- **Simon Ch. 2, (3.2) and (3.5)** (area formula for the blow-ups of an injective regular
image): if `g` is differentiable on the Borel set `B`, injective on `B` and `Dg(a)` is injective
for `a ∈ B`, then for `s > 0`, every `z` and every `f`,
`∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + s b) f(s⁻¹(g(z + s b) − g(z))) dLⁿ(b)`, where
`B_s = {b | z + s b ∈ B}` and `J_g = √det(Dg* ∘ Dg)`.  The rescaled map
`φ(b) = s⁻¹(g(z + s b) − g(z))` is injective on `B_s` with `Dφ(b) = Dg(z + s b)` and
`φ(B_s) = η_{g(z),s}(g(B))`, so this is the area formula for `φ`.  That formula is proved in
place: the linear case (3.1), sharp `Hⁿ` estimates for maps close to an injective linear map,
a measurable partition into such pieces, and the transport of the Jacobian-weighted measure,
following the pinned SimonGMT `Chapter02.AreaApproximation`, `AreaDerivative`, `AreaFormula`
and `WeightedArea` proofs, which lie outside this file's imports. -/
theorem Submission.codim1_rdo_c1pt_rescaled_area_formula : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (B : Set (Euclid n)) (z : Euclid n) (s : ℝ) (f : Euclid P → ℝ), MeasurableSet B → (∀ a ∈ B, DifferentiableAt ℝ g a) → InjOn g B → (∀ a ∈ B, Injective (fderiv ℝ g a)) → 0 < s → ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B), f y ∂μHE[n] = ∫ b in {b : Euclid n | z + s • b ∈ B}, Real.sqrt (((fderiv ℝ g (z + s • b)).adjoint ∘L fderiv ℝ g (z + s • b)).det) * f (s⁻¹ • (g (z + s • b) - g z)) := by
  intro P n g B z s f hB hdiff hinj hreg hs
  classical
  -- `J(L) = √det(L* ∘ L)` is the metric Jacobian of a linear map `L : ℝⁿ → ℝᴾ`
  obtain ⟨J, hJdef⟩ : ∃ J : (Euclid n →L[ℝ] Euclid P) → ℝ,
      J = fun L => Real.sqrt ((L.adjoint ∘L L).det) := ⟨_, rfl⟩
  have hJnonneg : ∀ L, 0 ≤ J L := fun L => by rw [hJdef]; exact Real.sqrt_nonneg _
  have hJcont : Continuous J := by
    rw [hJdef]
    exact Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))
  /- Simon (3.1), the linear area formula: an injective `L` factors as `ι ∘ M` with `ι` a
  linear isometry onto its range and `M` an endomorphism of `ℝⁿ`, so
  `Hⁿ(L(A)) = Lⁿ(M(A)) = |det M| Lⁿ(A)`, and `J(L)² = det(M* M) = (det M)² ≠ 0`. -/
  have hlin : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L →
      0 < J L ∧ ∀ A : Set (Euclid n), μHE[n] (L '' A) = ENNReal.ofReal (J L) * volume A := by
    intro L hL
    have hV : Module.finrank ℝ (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) = n := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let e : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) ≃ₗᵢ[ℝ] Euclid n :=
      ((stdOrthonormalBasis ℝ _).reindex (finCongr hV)).repr
    let ιI : Euclid n →ₗᵢ[ℝ] Euclid P :=
      (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)).subtypeₗᵢ.comp e.symm.toLinearIsometry
    let M : Euclid n →L[ℝ] Euclid n := (e : _ →L[ℝ] Euclid n) ∘L L.rangeRestrict
    have hLιM : L = ιI.toContinuousLinearMap ∘L M := by
      ext1 x
      show L x = ((e.symm (e (L.rangeRestrict x)) :
        LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) : Euclid P)
      rw [LinearIsometryEquiv.symm_apply_apply]
      rfl
    have hιadj : ιI.toContinuousLinearMap.adjoint ∘L ιI.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp ιI.norm_map
    have hdetadj : (ContinuousLinearMap.adjoint M).det = M.det := by
      have h := congrArg Matrix.det (LinearMap.toMatrix_adjoint (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin n) ℝ) (M : Euclid n →ₗ[ℝ] Euclid n))
      rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h
      simp only [star_trivial] at h
      exact h
    have hdet : (L.adjoint ∘L L).det = M.det ^ 2 := by
      have h1 : L.adjoint ∘L L = M.adjoint ∘L M := by
        rw [hLιM, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
          ← ContinuousLinearMap.comp_assoc _ _ M, hιadj, ContinuousLinearMap.one_def,
          ContinuousLinearMap.id_comp]
      have h2 : (M.adjoint ∘L M).det = M.adjoint.det * M.det :=
        LinearMap.det_comp _ _
      rw [h1, h2, hdetadj, sq]
    have hJ : J L = |M.det| := by
      rw [hJdef]
      dsimp only
      rw [hdet, Real.sqrt_sq_eq_abs]
    have hMinj : LinearMap.ker (M : Euclid n →ₗ[ℝ] Euclid n) = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hL
      have h := congrArg (fun v => ((e.symm v : LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)) :
        Euclid P)) hxy
      simpa [M] using h
    refine ⟨?_, fun A => ?_⟩
    · rw [hJ]
      exact abs_pos.mpr (fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hMinj)
    · rw [hJ, hLιM, ContinuousLinearMap.coe_comp, Set.image_comp,
        LinearIsometry.coe_toContinuousLinearMap, ιI.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact MeasureTheory.Measure.addHaar_image_linearMap volume (M : Euclid n →ₗ[ℝ] Euclid n) A
  -- comparison of pairwise distances gives comparison of the `Hⁿ` measures of the images
  have hdistcmp : ∀ (u v : Euclid n → Euclid P) (T : Set (Euclid n)) (K : NNReal), InjOn v T →
      (∀ x ∈ T, ∀ y ∈ T, dist (u x) (u y) ≤ K * dist (v x) (v y)) →
      μHE[n] (u '' T) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (v '' T) := by
    intro u v T K hv hK
    have hh : LipschitzOnWith K (u ∘ invFunOn v T) (v '' T) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hv.leftInvOn_invFunOn hx, hv.leftInvOn_invFunOn hy] using hK x hx y hy
    have himage : (u ∘ invFunOn v T) '' (v '' T) = u '' T := by
      rw [image_comp, hv.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  /- Near an injective `L`, one radius `δ` controls both the Jacobian of nearby linear maps and
  the `Hⁿ` measure of images under maps `δ`-approximating `L`, up to a factor `q > 1`. -/
  have hradius : ∀ L : Euclid n →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
          ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
            ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
        (∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P), ApproximatesLinearOn u L T δ →
          μHE[n] (u '' T) ≤ q * μHE[n] (L '' T) ∧ μHE[n] (L '' T) ≤ q * μHE[n] (u '' T)) := by
    intro L hL q hq
    obtain ⟨K, -, hK⟩ := (L : Euclid n →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hqR : (1 : ℝ) < q := hq
    have hJpos := (hlin L hL).1
    have hmul : J L < (q : ℝ) * J L := lt_mul_of_one_lt_left hJpos hqR
    have hnear : ∀ᶠ L' in 𝓝 L, J L' < (q : ℝ) * J L ∧ J L < (q : ℝ) * J L' :=
      (hJcont.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hJcont.continuousAt) hmul)
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      apply ContinuousAt.pow
      apply ContinuousAt.inv₀
      · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
      · simp
    have hεev : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
      (NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
        0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ n < q ∧ ((1 - δ * K)⁻¹) ^ n < q ∧ (δ : ℝ) < ε := by
      filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
        hupper.filter_mono nhdsWithin_le_nhds, hlower.filter_mono nhdsWithin_le_nhds,
        hεev.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    -- `‖(u x - u y) - L(x - y)‖ ≤ δ K ‖L x - L y‖` on `T`
    have herror : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P),
        ApproximatesLinearOn u L T δ → ∀ x ∈ T, ∀ y ∈ T,
          ‖u x - u y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ := by
      intro T u hu x hx y hy
      have hb : ‖x - y‖ ≤ K * ‖L x - L y‖ := by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      calc ‖u x - u y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hu x hx y hy
        _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left hb δ.2
        _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
    refine ⟨δ, hδ, fun L' hL' => ?_, fun T u hu => ⟨?_, ?_⟩⟩
    · have hdist : dist L' L < ε := by
        rw [dist_eq_norm]
        exact hL'.trans_lt hδε
      obtain ⟨h1, h2⟩ := hnear hdist
      constructor
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h1.le
      · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
        exact ENNReal.ofReal_le_ofReal h2.le
    · refine (hdistcmp u L T (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖u x - u y‖ ≤ ‖u x - u y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ :=
            add_le_add (herror T u hu x hx y hy) le_rfl
          _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
      · gcongr
        rw [← ENNReal.coe_pow]
        exact ENNReal.coe_le_coe.mpr hδupper.le
    · have hδR : (δ : ℝ) * K < 1 := hδK
      have hdist : ∀ x ∈ T, ∀ y ∈ T,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (u x) (u y) := by
        intro x hx y hy
        have h1 := herror T u hu x hx y hy
        have htriangle := norm_le_norm_add_norm_sub (u x - u y) (L x - L y)
        rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hδR)]
        linarith only [h1, htriangle]
      have huinj : InjOn u T := by
        intro x hx y hy hxy
        apply hL
        apply dist_le_zero.mp
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy
      refine (hdistcmp L u T _ huinj hdist).trans ?_
      gcongr
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_le_coe.mpr hδlower.le
  /- On almost every point of a measurable piece where `u` is `δ`-approximated by `A`, the
  derivative is `δ`-close to `A` (the density-point argument of Mathlib's
  `ApproximatesLinearOn.norm_fderiv_sub_le`, for rectangular derivatives). -/
  have hderivbound : ∀ (u : Euclid n → Euclid P) (T : Set (Euclid n)) (A : Euclid n →L[ℝ] Euclid P)
      (δ : NNReal) (u' : Euclid n → Euclid n →L[ℝ] Euclid P), ApproximatesLinearOn u A T δ →
      MeasurableSet T → (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) →
      ∀ᵐ x ∂(volume.restrict T), ‖u' x - A‖₊ ≤ δ := by
    intro u T A δ u' hf hT hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume T, ae_restrict_mem hT]
    intro x hx xT
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun w => ?_
    suffices H : ∀ ε, 0 < ε → ‖(u' x - A) w‖ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖w‖ + 0) + ‖u' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ := MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one volume T x hx
      (closedBall w ε) measurableSet_closedBall (measure_closedBall_pos volume w εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ T ⊆ {y : Euclid n | ‖u y - u x - (u' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xT).isLittleO εpos)
    have B₂ := (eventually_singleton_add_smul_subset (𝕜 := ℝ) (x := x)
      (isBounded_closedBall (x := w) (r := ε)) (ball_mem_nhds x ρpos)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    obtain ⟨r, ⟨y, ⟨yT, hy⟩⟩, rρ, rpos⟩ := (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, aw, ya⟩ : ∃ a, a ∈ closedBall w ε ∧ y = x + r • a := by
      have hy' := hy
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy'
      rcases hy' with ⟨a, aw, ha⟩
      exact ⟨a, aw, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖w‖ + ε :=
      calc ‖a‖ = ‖w + (a - w)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖w‖ + ‖a - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + ε := by grw [mem_closedBall_iff_norm.1 aw]
    have I : r * ‖(u' x - A) a‖ ≤ r * (δ + ε) * (‖w‖ + ε) :=
      calc r * ‖(u' x - A) a‖ = ‖(u' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖u y - u x - A (y - x) - (u y - u x - (u' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖u y - u x - A (y - x)‖ + ‖u y - u x - (u' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yT _ xT) (hρ ⟨rρ hy, yT⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖w‖ + ε) := by gcongr
    calc ‖(u' x - A) w‖ = ‖(u' x - A) a + (u' x - A) (w - a)‖ := by
          congr 1
          simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
          abel
      _ ≤ ‖(u' x - A) a‖ + ‖(u' x - A) (w - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ‖w - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I
            exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖w‖ + ε) + ‖u' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at aw
          gcongr
  /- Simon (3.2), measure form: for `u` injective on a measurable `T`, differentiable along `T`
  with injective derivative `u'`, `Hⁿ(u(T)) = ∫_T J(u'(x)) dLⁿ(x)`.  Partition `T` into
  measurable pieces on which `u` is close to linear maps `A i = u'(yᵢ)`, compare on each piece
  up to a factor `q²`, sum, and let `q ↓ 1`. -/
  have hmeasure : ∀ (T : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet T →
      (∀ x ∈ T, HasFDerivWithinAt u (u' x) T x) → (∀ x ∈ T, Injective (u' x)) → InjOn u T →
      μHE[n] (u '' T) = ∫⁻ x in T, ENNReal.ofReal (J (u' x)) := by
    intro T u u' hT hu' hreg' hinj'
    have hcmp : ∀ q : NNReal, 1 < q →
        μHE[n] (u '' T) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T, ENNReal.ofReal (J (u' x)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' T) := by
      intro q hq
      rcases eq_empty_or_nonempty T with rfl | hTne
      · simp
      have hchoice : ∀ L : Euclid n →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid n →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (J L') ≤ q * ENNReal.ofReal (J L) ∧
              ENNReal.ofReal (J L) ≤ q * ENNReal.ofReal (J L')) ∧
          (∀ (T' : Set (Euclid n)) (v : Euclid n → Euclid P), ApproximatesLinearOn v L T' δ →
            μHE[n] (v '' T') ≤ q * μHE[n] (L '' T') ∧
              μHE[n] (L '' T') ≤ q * μHE[n] (v '' T'))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, h1, h2⟩ := hradius L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨h1, h2⟩⟩
        · exact ⟨1, one_pos, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u T u' hu' δ
          (fun L => (hδpos L).ne')
      have hAreg : ∀ i, Injective (A i) := by
        intro i
        obtain ⟨x, hx, hA⟩ := hactual hTne i
        rw [hA]
        exact hreg' x hx
      have hTeq : T = ⋃ i, T ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[n] (u '' T) = ∑' i, μHE[n] (u '' (T ∩ t i)) := by
        conv_lhs => rw [hTeq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            hinj' inter_subset_left inter_subset_left
        · intro i
          apply (hT.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hu' x hx.1).continuousWithinAt.mono inter_subset_left
          · exact hinj'.mono inter_subset_left
      have hsumintegral : ∫⁻ x in T, ENNReal.ofReal (J (u' x)) =
          ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
        conv_lhs => rw [hTeq]
        exact lintegral_iUnion (fun i => hT.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[n] (u '' (T ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ∧
          ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by
        intro i
        have hJ := (hδ (A i) (hAreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (A i) (hAreg i)).2 (T ∩ t i) u (happrox i)
        have hlinA := (hlin (A i) (hAreg i)).2 (T ∩ t i)
        rw [hlinA] at harea_upper harea_lower
        have hderiv := hderivbound u (T ∩ t i) (A i) (δ (A i)) u' (happrox i) (hT.inter (ht i))
          (fun x hx => (hu' x hx.1).mono inter_subset_left)
        have hJupper : ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) ≤
            q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
          calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ ∫⁻ _ in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (A i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).1
            _ = q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (J (A i)) * volume (T ∩ t i) ≤
            q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
          calc ENNReal.ofReal (J (A i)) * volume (T ∩ t i)
              = ∫⁻ _ in T ∩ t i, ENNReal.ofReal (J (A i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in T ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (u' x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (u' x) hx).2
            _ = q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[n] (u '' (T ∩ t i)) ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) := by
                rw [pow_two, mul_assoc]
        · calc ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
              ≤ q * (ENNReal.ofReal (J (A i)) * volume (T ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[n] (u '' (T ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc ∑' i, μHE[n] (u '' (T ∩ t i))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x)) :=
              ENNReal.tsum_mul_left
      · calc ∑' i, ∫⁻ x in T ∩ t i, ENNReal.ofReal (J (u' x))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[n] (u '' (T ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = (q : ℝ≥0∞) ^ 2 * ∑' i, μHE[n] (u '' (T ∩ t i)) := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcmp q hq).2
  /- Simon (3.5), Bochner form: the Jacobian-weighted measure on `S` is transported by `u`
  to `Hⁿ ⌞ u(S)`, so `∫_{u(S)} f dHⁿ = ∫_S J(u'(x)) f(u(x)) dLⁿ(x)` for every `f`. -/
  have hbochner : ∀ (S : Set (Euclid n)) (u : Euclid n → Euclid P)
      (u' : Euclid n → Euclid n →L[ℝ] Euclid P), MeasurableSet S →
      (∀ x ∈ S, HasFDerivAt u (u' x) x) → (∀ x ∈ S, Injective (u' x)) → InjOn u S →
      Measurable u' → ∫ y in u '' S, f y ∂μHE[n] = ∫ x in S, J (u' x) * f (u x) := by
    intro S u u' hS hu' hreg' hinj' hmeas'
    have hcont : ContinuousOn u S := fun x hx => (hu' x hx).continuousAt.continuousWithinAt
    have hemb := hcont.measurableEmbedding hS hinj'
    have hsub := MeasurableEmbedding.subtype_coe hS
    have hJm : Measurable (fun x => J (u' x)) := hJcont.measurable.comp hmeas'
    have hmap : Measure.map (S.domRestrict u)
        ((volume.withDensity (fun x => ENNReal.ofReal (J (u' x)))).comap
          (Subtype.val : S → Euclid n)) = μHE[n].restrict (u '' S) := by
      ext t ht
      rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
      have hBm : MeasurableSet (Subtype.val '' ((S.domRestrict u) ⁻¹' t)) :=
        hsub.measurableSet_image' (hemb.measurable ht)
      have hBS : Subtype.val '' ((S.domRestrict u) ⁻¹' t) ⊆ S := by
        rintro x ⟨w, _, rfl⟩
        exact w.property
      rw [withDensity_apply _ hBm, ← hmeasure _ u u' hBm
        (fun x hx => (hu' x (hBS hx)).hasFDerivWithinAt) (fun x hx => hreg' x (hBS hx))
        (hinj'.mono hBS), Measure.restrict_apply ht]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨hw, ⟨w, w.property, rfl⟩⟩
      · rintro ⟨hy, x, hx, rfl⟩
        exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
    rw [← hmap, hemb.integral_map]
    simp only [Set.domRestrict_apply, ← Function.comp_apply (f := f), ENNReal.ofReal]
    rw [← hsub.integral_map, map_comap_subtype_coe hS,
      setIntegral_withDensity_eq_setIntegral_smul₀ (hJm.real_toNNReal.aemeasurable) _ hS]
    congr with x
    rw [NNReal.smul_def, Real.coe_toNNReal _ (hJnonneg _), smul_eq_mul, comp_apply]
  -- the rescaled map `φ(b) = s⁻¹ • (g (z + s • b) - g z)` on `B_s = {b | z + s • b ∈ B}`
  have hs0 : s ≠ 0 := hs.ne'
  have hBs : MeasurableSet {b : Euclid n | z + s • b ∈ B} :=
    hB.preimage ((measurable_const_add z).comp (measurable_const_smul s))
  have hderiv : ∀ b ∈ {b : Euclid n | z + s • b ∈ B},
      HasFDerivAt (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) (fderiv ℝ g (z + s • b)) b := by
    intro b hb
    have h1 : HasFDerivAt (fun b' : Euclid n => z + s • b')
        (s • ContinuousLinearMap.id ℝ (Euclid n)) b :=
      ((hasFDerivAt_id b).const_smul s).const_add z
    refine ((((hdiff _ hb).hasFDerivAt.comp b h1).sub_const (g z)).const_smul s⁻¹).congr_fderiv ?_
    ext1 v
    simp [smul_smul, inv_mul_cancel₀ hs0]
  have hinjφ : InjOn (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z))
      {b : Euclid n | z + s • b ∈ B} := by
    intro b hb b' hb' h
    have h' : g (z + s • b) = g (z + s • b') := by
      simpa [hs0] using h
    exact smul_right_injective _ hs0 (add_left_cancel (hinj hb hb' h'))
  have himage :
      (fun b : Euclid n => s⁻¹ • (g (z + s • b) - g z)) '' {b : Euclid n | z + s • b ∈ B} =
        Poincare.SimonGMT.Chapter03.blowUpMap (g z) s '' (g '' B) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨g (z + s • b), ⟨z + s • b, hb, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s⁻¹ • (a - z), ?_, ?_⟩
      · show z + s • s⁻¹ • (a - z) ∈ B
        rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
      · show s⁻¹ • (g (z + s • s⁻¹ • (a - z)) - g z) = s⁻¹ • (g a - g z)
        rw [smul_smul, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]
  have hmeasf' : Measurable (fun b : Euclid n => fderiv ℝ g (z + s • b)) :=
    (measurable_fderiv ℝ g).comp ((measurable_const_add z).comp (measurable_const_smul s))
  rw [← himage, hbochner _ _ (fun b : Euclid n => fderiv ℝ g (z + s • b)) hBs hderiv
    (fun b hb => hreg _ hb) hinjφ hmeasf', hJdef]
/-- **Gram cofactor identity** (the Jacobian identity `|G ∘ Φ| · JΦ = JΦₛ` of the co-area formula
for one straightened piece, Simon Ch. 3, 2.8–2.9).  If `u ∈ span{a₀, …, aₙ}`, `⟨u, a₀⟩ = 1` and
`⟨u, a_{k+1}⟩ = 0` for all `k`, then `det[⟨a_{i+1}, a_{j+1}⟩]_{i,j<n} = ‖u‖² · det[⟨aᵢ, aⱼ⟩]_{i,j≤n}`.
Write `u = ∑ cₗ aₗ`.  The Gram matrix `A = [⟨aᵢ, aⱼ⟩]` satisfies `A c = e₀` and `‖u‖² = c₀`, so
`adj(A) e₀ = adj(A) A c = det A · c`; the `(0, 0)` entry of `adj(A)` is the cofactor
`det[⟨a_{i+1}, a_{j+1}⟩]` (Cramer's rule).  No linear independence is needed. -/
theorem Submission.dor_lmbsf_pc_gram_det_succ_eq : ∀ (P n : ℕ) (a : Fin (n + 1) → Euclid P) (u : Euclid P), u ∈ Submodule.span ℝ (Set.range a) → inner ℝ u (a 0) = 1 → (∀ k : Fin n, inner ℝ u (a k.succ) = 0) → Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (a i.succ) (a j.succ)) = ‖u‖ ^ 2 * Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (a i) (a j)) := by
  intro P n a u hu h0 hk
  classical
  -- `u = ∑ cₗ aₗ`
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hu
  set A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j => inner ℝ (a i) (a j)
  -- `⟨u, aᵢ⟩ = δᵢ₀`
  have hua : ∀ i, inner ℝ u (a i) = (Pi.single 0 1 : Fin (n + 1) → ℝ) i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [h0]
    · simp [hk k, Fin.succ_ne_zero]
  -- `A c = e₀`
  have hAc : A.mulVec c = Pi.single 0 1 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    have : ∑ j, inner ℝ (a i) (a j) * c j = inner ℝ (a i) u := by
      rw [← hc, inner_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_smul_right]; ring
    rw [this, real_inner_comm, hua]
  -- `‖u‖² = c₀`
  have hnorm : ‖u‖ ^ 2 = c 0 := by
    rw [← real_inner_self_eq_norm_sq]
    calc inner ℝ u u = inner ℝ (∑ l, c l • a l) u := by rw [hc]
      _ = ∑ l, c l * inner ℝ (a l) u := by
          rw [sum_inner]; refine Finset.sum_congr rfl (fun l _ => ?_); rw [real_inner_smul_left]
      _ = c 0 := by
          have hl : ∀ l, inner ℝ (a l) u = (Pi.single 0 1 : Fin (n + 1) → ℝ) l := fun l => by
            rw [real_inner_comm, hua]
          simp_rw [hl]
          simp [Pi.single_apply]
  -- `adj(A) e₀ = adj(A) A c = det A · c`, read off at the `0`-th entry
  have hadj : A.adjugate.mulVec (A.mulVec c) = A.det • c := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hAc] at hadj
  have h00 := congrFun hadj 0
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul] at h00
  -- the `(0, 0)` cofactor of `A` is the Gram determinant of `a₁, …, aₙ`
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at h00
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero] at h00
  rw [hnorm, mul_comm, ← h00]
  rfl
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
/-- **Simon Ch. 2, (3.1)** in integral form (area formula for an injective linear map): for an
injective linear `L : ℝⁿ → ℝᴾ` and every `f`, `∫_{L(ℝⁿ)} f dHⁿ = √det(L* ∘ L) ∫_{ℝⁿ} f(Lb) dLⁿ(b)`.
Write `L = W ∘ A` with `W` a linear isometry of `ℝⁿ` onto `L(ℝⁿ)` and `A` an automorphism of `ℝⁿ`;
then `Hⁿ⌞L(ℝⁿ) = W#Lⁿ`, `Lⁿ = |det A| A#Lⁿ` and `det(L* ∘ L) = det(A* ∘ A) = (det A)²`. -/
theorem Submission.codim1_rdo_c1pt_linear_range_integral : ∀ (P n : ℕ) (L : Euclid n →L[ℝ] Euclid P) (f : Euclid P → ℝ), Injective L → ∫ y in (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)), f y ∂μHE[n] = Real.sqrt ((L.adjoint ∘L L).det) * ∫ b, f (L b) := by
  intro P n L f hL
  -- `L = W ∘ A`: `W` is a linear isometry of `ℝⁿ` onto `R = L(ℝⁿ)` (via an orthonormal basis of
  -- `R`, which has dimension `n`) and `A` is a surjective endomorphism of `ℝⁿ`
  obtain ⟨W, A, hWA, hA⟩ : ∃ (W : Euclid n →ₗᵢ[ℝ] Euclid P) (A : Euclid n →L[ℝ] Euclid n),
      (∀ x, W (A x) = L x) ∧ Surjective A := by
    let R := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P)
    have hrank : Module.finrank ℝ R = n :=
      (LinearMap.finrank_range_of_inj (f := (L : Euclid n →ₗ[ℝ] Euclid P)) hL).trans
        finrank_euclideanSpace_fin
    let bv : OrthonormalBasis (Fin n) ℝ R := (stdOrthonormalBasis ℝ R).reindex (finCongr hrank)
    refine ⟨R.subtypeₗᵢ.comp bv.repr.symm.toLinearIsometry,
      bv.repr.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        L.codRestrict R (fun x => LinearMap.mem_range_self _ x), fun x => by simp, fun z => ?_⟩
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (bv.repr.symm z).2
    refine ⟨x, ?_⟩
    have hx' : L.codRestrict R (fun x => LinearMap.mem_range_self _ x) x = bv.repr.symm z :=
      Subtype.ext hx
    simp [hx']
  have hAinj : Injective A := fun x y h => hL (by rw [← hWA x, ← hWA y, h])
  -- `L(ℝⁿ) = W(ℝⁿ)`
  have hrange : (LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) : Set (Euclid P)) =
      Set.range W := by
    rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe, ← hA.range_comp W]
    congr 1
    funext x
    exact (hWA x).symm
  -- `Hⁿ⌞W(ℝⁿ) = W#Hⁿ` (`W` is an isometry) and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hW : ∫ y in Set.range W, f y ∂μHE[n] = ∫ x, f (W x) := by
    rw [← W.isometry.map_euclideanHausdorffMeasure,
      W.isometry.isClosedEmbedding.measurableEmbedding.integral_map,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- change of variables `x = A b` on `ℝⁿ`
  have hAcv : ∫ x, f (W x) = |A.det| * ∫ b, f (W (A b)) := by
    have h := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun x _ => A.hasFDerivAt.hasFDerivWithinAt) hAinj.injOn (fun x => f (W x))
    rw [Set.image_univ, hA.range_eq, Measure.restrict_univ] at h
    rw [h, ← integral_const_mul]
    simp only [smul_eq_mul]
  -- `L* ∘ L = A* ∘ W* ∘ W ∘ A = A* ∘ A`, so `det (L* ∘ L) = (det A)²`
  have hdet : (L.adjoint ∘L L).det = A.det ^ 2 := by
    have hL' : L = W.toContinuousLinearMap ∘L A := ContinuousLinearMap.ext fun x => (hWA x).symm
    have h1 : L.adjoint ∘L L = A.adjoint ∘L A := by
      rw [hL', ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.comp_assoc,
        ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint _), W.adjoint_comp_self,
        ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have hadj : LinearMap.det (LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n)) =
        LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
      let b := EuclideanSpace.basisFun (Fin n) ℝ
      rw [← LinearMap.det_toMatrix b.toBasis, LinearMap.toMatrix_adjoint b b,
        Matrix.det_conjTranspose, LinearMap.det_toMatrix, star_trivial]
    rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.det,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
      ← ContinuousLinearMap.adjoint_toLinearMap, hadj, sq]
  rw [hrange, hW, hAcv, hdet, Real.sqrt_sq_eq_abs]
  simp only [hWA]
/-- Rescaled integrals over a `C¹` piece converge to the integral over its tangent map (proof of
Simon Ch. 3, Theorem 1.6, with a continuous weight `h`).  With `L = Dg(z)`,
`B_s = {b : z + s b ∈ B}` and `φ_s(b) = s⁻¹ (g(z + s b) − g(z))`:
`∫_{B_s} h(z + s b) f(φ_s(b)) db → h(z) ∫ f(L b) db` as `s ↓ 0`.  Take `f = 0` off `B_R(0)` and
`B̄_ρ(z) ⊆ B`.  For `0 < s < mρ/R`, `K = B̄_{R/m}(0) ⊆ B_s`, and the integrand vanishes on
`B_s \ K` because `|φ_s(b)| ≥ m|b| > R`.  On `K` it is bounded by `sup_{B̄_ρ(z)} |h| · sup |f|` and
tends pointwise to `h(z) f(L b)`, so dominated convergence applies.  Finally `f(L b) = 0` off `K`
because `|L b| ≥ m|b| > R`. -/
theorem Submission.codim1_rdo_c1pt_rescaled_integral_tendsto : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (h : Euclid n → ℝ) (B : Set (Euclid n)) (z : Euclid n) (m : ℝ) (f : Euclid P → ℝ), Continuous g → DifferentiableAt ℝ g z → Continuous h → IsOpen B → z ∈ B → 0 < m → (∀ a ∈ B, m * ‖a - z‖ ≤ ‖g a - g z‖) → (∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g z v‖) → Continuous f → HasCompactSupport f → Tendsto (fun s : ℝ => ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0) (𝓝 (h z * ∫ b, f (fderiv ℝ g z b))) := by
  intro P n g h B z m f hg hgz hh hB hzB hm hgB hL hf hfs
  -- Step 1: `f = 0` off `closedBall 0 R`
  obtain ⟨R, hR, hRf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR, hsub⟩ := hfs.isCompact.isBounded.subset_closedBall_lt 0 0
    refine ⟨R, hR, fun y hy => ?_⟩
    by_contra hne
    have hy' := hsub (subset_tsupport f hne)
    rw [mem_closedBall, dist_zero_right] at hy'
    linarith
  -- Step 2: `closedBall z ρ ⊆ B`
  obtain ⟨ρ, hρ, hρB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ closedBall z ρ ⊆ B := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 hB z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  -- Step 3: `K = closedBall 0 (R / m)`, `s₀ = m ρ / R`
  have hs₀ : 0 < m * ρ / R := div_pos (mul_pos hm hρ) hR
  have hKB : ∀ s : ℝ, 0 < s → s ≤ m * ρ / R → ∀ b ∈ closedBall (0 : Euclid n) (R / m),
      z + s • b ∈ closedBall z ρ := by
    intro s hs hss b hb
    rw [mem_closedBall, dist_zero_right] at hb
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
    calc s * ‖b‖ ≤ m * ρ / R * (R / m) := mul_le_mul hss hb (norm_nonneg _) hs₀.le
      _ = ρ := by field_simp
  have hout : ∀ s : ℝ, 0 < s → ∀ b : Euclid n, z + s • b ∈ B →
      b ∉ closedBall (0 : Euclid n) (R / m) → f (s⁻¹ • (g (z + s • b) - g z)) = 0 := by
    intro s hs b hbB hbK
    apply hRf
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hbK
    have h1 := hgB _ hbB
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le] at h1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    calc R < ‖b‖ * m := hbK
      _ = s⁻¹ * (m * (s * ‖b‖)) := by field_simp
      _ ≤ s⁻¹ * ‖g (z + s • b) - g z‖ := by gcongr
  -- Step 4: localisation to `K`
  have hloc : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ b in closedBall (0 : Euclid n) (R / m), h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) =
        ∫ b in {b : Euclid n | z + s • b ∈ B}, h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z)) := by
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    · exact (hB.preimage (continuous_const.add (continuous_const_smul s))).measurableSet
    · intro b hb
      exact hρB (hKB s hs.1 hs.2.le b hb)
    · rintro b ⟨hbB, hbK⟩
      rw [hout s hs.1 b hbB hbK, mul_zero]
  -- Step 5: uniform bounds
  obtain ⟨Λ, hΛ⟩ := (isCompact_closedBall z ρ).exists_bound_of_continuousOn hh.continuousOn
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfs
  -- Steps 6–8: dominated convergence on `K`
  have hdom : Tendsto (fun s : ℝ => ∫ b in closedBall (0 : Euclid n) (R / m),
      h (z + s • b) * f (s⁻¹ • (g (z + s • b) - g z))) (𝓝[>] 0)
      (𝓝 (∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => Λ * C) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun s => Continuous.aestronglyMeasurable ?_
      have hz : Continuous fun b : Euclid n => z + s • b :=
        continuous_const.add (continuous_const_smul s)
      exact (hh.comp hz).mul (hf.comp (((hg.comp hz).sub continuous_const).const_smul s⁻¹))
    · filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with b hb
      have hmem := hKB s hs.1 hs.2.le b hb
      rw [norm_mul]
      exact mul_le_mul (hΛ _ hmem) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hΛ _ hmem))
    · exact integrableOn_const measure_closedBall_lt_top.ne
    · refine Eventually.of_forall fun b => Tendsto.mul ?_ ?_
      · -- `h (z + s • b) → h z`
        have h1 : Tendsto (fun s : ℝ => z + s • b) (𝓝 0) (𝓝 (z + (0 : ℝ) • b)) :=
          (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
        rw [zero_smul, add_zero] at h1
        exact (hh.tendsto z).comp (h1.mono_left nhdsWithin_le_nhds)
      · -- difference quotients: `s⁻¹ • (g (z + s • b) - g z) → L b`
        have hc : Tendsto (fun s : ℝ => ‖s⁻¹‖) (𝓝[>] 0) atTop :=
          tendsto_norm_atTop_atTop.comp tendsto_inv_nhdsGT_zero
        have hlim := hgz.hasFDerivAt.lim b hc
        simp only [inv_inv] at hlim
        exact (hf.tendsto _).comp hlim
  -- Step 9: identification of the limit
  have hid : ∫ b in closedBall (0 : Euclid n) (R / m), h z * f (fderiv ℝ g z b) =
      h z * ∫ b, f (fderiv ℝ g z b) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_const_mul]
    intro b hb
    rw [mem_closedBall, dist_zero_right, not_le, div_lt_iff₀ hm] at hb
    rw [hRf _ (hb.trans_le ((mul_comm _ _).le.trans (hL b))), mul_zero]
  rw [← hid]
  exact hdom.congr' hloc

/-- **Approximate tangent space of a `C¹` piece** (Simon Ch. 3, 1.4; the step "since `x ∈ Nⱼ` and
`Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of the proof of
1.6 "⇒", chapter-03.txt lines 113–125).  Let `g` be `C¹` with `m|a − b| ≤ |g(a) − g(b)|` on
`B = B_r(c)`, `m > 0`, and `z ∈ B`.  Then `|Dg(a)v| ≥ m|v|`, so `Dg(a)` is injective for `a ∈ B`,
`g` is injective on `B` and `T = Dg(z)(ℝⁿ)` has dimension `n`.  By the area formula (Ch. 2, 3.2,
3.3, 3.5), `∫_{η_{g(z),s}(g(B))} f dHⁿ = ∫_{B_s} J_g(z + sb) f(s⁻¹(g(z + sb) − g(z))) db` for
`s > 0`.  The Jacobian `J_g = √det(Dg* ∘ Dg)` is continuous, so these integrals tend to
`J_g(z) ∫ f(Dg(z)b) db`, which is `∫_T f dHⁿ` by the linear area formula (Ch. 2, 3.1). -/
theorem Submission.codim1_rdo_c1_piece_approxTangent : ∀ (P n : ℕ) (g : Euclid n → Euclid P) (c : Euclid n) (r m : ℝ), ContDiff ℝ 1 g → 0 < m → (∀ a ∈ ball c r, ∀ b ∈ ball c r, m * ‖a - b‖ ≤ ‖g a - g b‖) → ∀ z ∈ ball c r, HasApproximateTangentSpaceAt n (g '' ball c r) (g z) (LinearMap.range (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n g c r m hg hm hlip z hz
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  -- a vector `x` with `m|x| ≤ 0` vanishes, since `m > 0`
  have hzero : ∀ x : Euclid n, m * ‖x‖ ≤ 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right hx hm)
  -- Step 1, `m|v| ≤ |Dg(a)v|` for `a ∈ B`, so `Dg(a)` is injective; `g` is injective on `B`.
  have hlow : ∀ a ∈ ball c r, ∀ v : Euclid n, m * ‖v‖ ≤ ‖fderiv ℝ g a v‖ := fun a ha =>
    Submission.codim1_rdo_c1pt_fderiv_lower_bound P n g (ball c r) a m isOpen_ball ha (hdiff a)
      fun x hx => hlip x hx a ha
  have hinj : ∀ a ∈ ball c r, Injective (fderiv ℝ g a) := by
    intro a ha v w hvw
    have h := hlow a ha (v - w)
    rw [map_sub, hvw, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  have hinjOn : InjOn g (ball c r) := by
    intro a ha b hb hab
    have h := hlip a ha b hb
    rw [hab, sub_self, norm_zero] at h
    exact sub_eq_zero.1 (hzero _ h)
  -- Step 2, the Jacobian `J_g(a) = √det(Dg(a)* ∘ Dg(a))` is continuous.
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hJ : Continuous fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      ((ContinuousLinearMap.adjoint.continuous.comp hcont).clm_comp hcont))
  refine ⟨?_, fun f => ?_⟩
  · -- `dim T = n`
    rw [LinearMap.finrank_range_of_inj (f := (fderiv ℝ g z : Euclid n →ₗ[ℝ] Euclid P))
      (hinj z hz), finrank_euclideanSpace_fin]
  · -- Steps 3–8, `∫_T f dHⁿ = J_g(z) ∫ f(Dg(z)b) db` is the limit of the rescaled area formulas.
    rw [Submission.codim1_rdo_c1pt_linear_range_integral P n (fderiv ℝ g z) f (hinj z hz)]
    refine (Submission.codim1_rdo_c1pt_rescaled_integral_tendsto P n g
      (fun a => Real.sqrt (((fderiv ℝ g a).adjoint ∘L fderiv ℝ g a).det)) (ball c r) z m f
      hdiff.continuous (hdiff z) hJ isOpen_ball hz hm (fun a ha => hlip a ha z hz) (hlow z hz)
      f.continuous f.hasCompactSupport).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (Submission.codim1_rdo_c1pt_rescaled_area_formula P n g (ball c r) z s f
      measurableSet_ball (fun a _ => hdiff a) hinjOn hinj hs).symm
/-- **Locality of approximate tangent spaces** (Simon Ch. 3, Definition 1.4): if `M' ⊆ M`, `M` is
Borel and `x ∉ closure (M \ M')`, then an approximate tangent space `Q` of `M'` at `x` is also one
of `M`.  Some `ρ > 0` has `|z − x| ≥ ρ` on `M \ M'`, and a test function `f` vanishes on
`|p| ≥ R`.  For `0 < r < ρ / R`, `η_{x,r}(M)` and `η_{x,r}(M')` differ only where
`|p| ≥ ρ / r > R`, so `∫_{η_{x,r}(M)} f dHⁿ = ∫_{η_{x,r}(M')} f dHⁿ` and the limit transfers. -/
theorem Submission.dor_lmbsf_cit_approxTangent_of_subset : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → M' ⊆ M → x ∉ closure (M \ M') → HasApproximateTangentSpaceAt n M' x Q → HasApproximateTangentSpaceAt n M x Q := by
  intro P n M M' x Q hM hM'M hx hM'
  refine ⟨hM'.1, fun f => ?_⟩
  -- `x ∉ closure (M \ M')`: some `ρ > 0` has `ρ ≤ |x − z|` for all `z ∈ M \ M'`
  obtain ⟨ρ, hρ, hρM⟩ : ∃ ρ > 0, ∀ z ∈ M \ M', ρ ≤ dist x z := by
    simpa only [Metric.mem_closure_iff, not_forall, not_exists, not_and, not_lt,
      exists_prop] using hx
  -- `f` has compact support: `f p = 0` once `R ≤ |p|`
  obtain ⟨R, hR, hfR⟩ : ∃ R : ℝ, 0 < R ∧ ∀ p : Euclid P, R ≤ ‖p‖ → f p = 0 :=
    f.hasCompactSupport.exists_pos_le_norm
  -- for `0 < r < ρ / R` the blown-up integrals over `M` and `M'` agree
  refine (hM'.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hρ hR)] with r hr
  obtain ⟨hr0, hrR⟩ := hr
  rw [lt_div_iff₀ hR] at hrR
  -- `η_{x,r}(M)` is the preimage of `M` under `p ↦ x + r p`, hence Borel
  have hmeas : MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M) := by
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
        (fun p : Euclid P => x + r • p) ⁻¹' M := by
      ext p
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr0.ne'] using hz
      · intro hp
        exact ⟨x + r • p, hp, by
          simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr0.ne']⟩
    rw [himage]
    exact hM.preimage (by fun_prop)
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas (image_mono hM'M) ?_
  -- a point of `η_{x,r}(M) \ η_{x,r}(M')` comes from `z ∈ M \ M'`, so its norm is `≥ ρ / r > R`
  rintro _ ⟨⟨z, hzM, rfl⟩, hzM'⟩
  have hz : z ∈ M \ M' := ⟨hzM, fun h => hzM' ⟨z, h, rfl⟩⟩
  apply hfR
  rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr0.le),
    ← dist_eq_norm, dist_comm, inv_mul_eq_div, le_div_iff₀ hr0]
  linarith [hρM z hz]

/-- **Approximate tangent space of an injective `C¹` image** (Simon Ch. 3, 1.4; the step "since
`x ∈ Nⱼ` and `Nⱼ` is a `C¹` submanifold, `lim_{λ↓0} ∫_{η_{x,λ}(Nⱼ)} f dHⁿ = ∫_{TₓNⱼ} f dHⁿ`" of
the proof of 1.6 "⇒", chapter-03.txt lines 113–125).  Let `χ` be `C¹` on the open `V ⊇ C`, `C`
compact, `χ` injective on `C`, `y ∈ int C` and `Dχ(y)` injective.  On a ball
`B_ε(y) ⊆ V ∩ int C`, `χ` agrees with a globally `C¹` map `g`, so `Dg(y) = Dχ(y)` and `g` has a
lower Lipschitz bound on some `B_δ(y) ⊆ B_ε(y)`.  Hence `χ(B_δ(y)) = g(B_δ(y))` has approximate
tangent space `Q = Dχ(y)(ℝᵏ)` at `χ(y)`.  The rest of `χ(C)` lies in the compact set
`χ(C \ B_δ(y))`, which misses `χ(y)` by injectivity, so it does not change the blow-up limits. -/
theorem Submission.dor_lmbsf_c1_image_approxTangent : ∀ (k P : ℕ) (V C : Set (Euclid k)) (χ : Euclid k → Euclid P) (y : Euclid k), IsOpen V → ContDiffOn ℝ 1 χ V → IsCompact C → C ⊆ V → InjOn χ C → y ∈ interior C → Injective (fderiv ℝ χ y) → HasApproximateTangentSpaceAt k (χ '' C) (χ y) (LinearMap.range (fderiv ℝ χ y : Euclid k →ₗ[ℝ] Euclid P)) := by
  intro k P V C χ y hV hχ hC hCV hinj hy hDχ
  -- Step 1, `χ` agrees on `B_ε(y) ⊆ W = V ∩ int C` with a globally `C¹` map `g`
  obtain ⟨g, ε, hε, hεW, hg, hgχ⟩ := Submission.dor_lmbsf_cit_c1_local_extension P k
    (V ∩ interior C) χ y (hV.inter isOpen_interior) (hχ.mono inter_subset_left)
    ⟨hCV (interior_subset hy), hy⟩
  -- Step 2, `g(y) = χ(y)` and `Dg(y) = Dχ(y)`, since `g = χ` near `y`
  have hgy : g y = χ y := hgχ (mem_ball_self hε)
  have hDg : fderiv ℝ g y = fderiv ℝ χ y :=
    (hgχ.eventuallyEq_of_mem (ball_mem_nhds y hε)).fderiv_eq
  -- Step 3, `μ|a − b| ≤ |g(a) − g(b)|` on `B_δ₀(y)`; take `δ = min(ε, δ₀)`
  obtain ⟨δ₀, μ, hδ₀, hμ, hlip⟩ :=
    Submission.codim1_rdo_c1cov_local_lower_lipschitz P k g y hg (by rwa [hDg])
  obtain ⟨δ, hδ, hδε, hδδ₀⟩ : ∃ δ : ℝ, 0 < δ ∧ ball y δ ⊆ ball y ε ∧ ball y δ ⊆ ball y δ₀ :=
    ⟨min ε δ₀, lt_min hε hδ₀, ball_subset_ball (min_le_left _ _),
      ball_subset_ball (min_le_right _ _)⟩
  -- Step 4, `M' = g(B_δ(y)) = χ(B_δ(y))` has approximate tangent space `Q` at `χ(y)`
  have hpiece := Submission.codim1_rdo_c1_piece_approxTangent P k g y δ μ hg hμ
    (fun a ha b hb => hlip a (hδδ₀ ha) b (hδδ₀ hb)) y (mem_ball_self hδ)
  rw [(hgχ.mono hδε).image_eq, hgy, hDg] at hpiece
  -- Step 5, `M = χ(C)` is compact, `M' ⊆ M`, and `M \ M' ⊆ χ(C \ B_δ(y))`, a compact set that
  -- misses `χ(y)` because `χ` is injective on `C`
  have hδC : ball y δ ⊆ C := hδε.trans (hεW.trans (inter_subset_right.trans interior_subset))
  have hχC : ContinuousOn χ C := hχ.continuousOn.mono hCV
  have hfar : χ y ∉ closure (χ '' C \ χ '' ball y δ) := by
    intro hcl
    obtain ⟨z, ⟨hzC, hzδ⟩, hzy⟩ := closure_minimal (subset_image_sdiff χ C (ball y δ))
      ((hC.diff isOpen_ball).image_of_continuousOn (hχC.mono sdiff_subset)).isClosed hcl
    rw [hinj hzC (interior_subset hy) hzy] at hzδ
    exact hzδ (mem_ball_self hδ)
  -- Step 6, the part of `χ(C)` away from `χ(y)` does not change the blow-up limits
  exact Submission.dor_lmbsf_cit_approxTangent_of_subset P k (χ '' C) (χ '' ball y δ) (χ y) _
    (hC.image_of_continuousOn hχC).isClosed.measurableSet (image_mono hδC) hfar hpiece
/-- **Density points see every direction.**  If `y` is a Lebesgue density point of an arbitrary set
`Z ⊆ ℝᵈ`, i.e. `Lᵈ(Z ∩ B̄_r(y)) / Lᵈ(B̄_r(y)) → 1` as `r ↓ 0`, then every unit vector `v` is a limit
of secant directions `(yᵢ - y)/|yᵢ - y|` with `yᵢ ∈ Z ∖ {y}` and `yᵢ → y`.  For `0 < η ≤ 1` and
`r > 0` the ball `B_{ηr/4}(y + (r/2)v)` lies in `B̄_r(y) ∖ {y}` and in the `η`-cone around `v`, and
it has measure `(η/4)ᵈ Lᵈ(B̄_r(y))`, so density one forces `Z` to meet it for all small `r`; take
`η = 1/(i+1)` and `r < 1/(i+1)`. -/
theorem Submission.dor_lmbsf_density_directions : ∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v) := by
  intro d Z y hdens v hv
  -- the ball `B_{ηr/4}(y + (r/2)v)` lies in `B_r(y) ∖ {y}`, inside the `η`-cone around `v`
  have cone : ∀ η r : ℝ, 0 < η → η ≤ 1 → 0 < r → ∀ z ∈ ball (y + (r / 2) • v) (η * r / 4),
      ‖z - y‖ < r ∧ z ≠ y ∧ ‖‖z - y‖⁻¹ • (z - y) - v‖ < η := by
    intro η r hη hη1 hr z hz
    have hs : (0 : ℝ) < r / 2 := by positivity
    -- the offset `w = z - y - (r/2)v` of `z` from the centre has `‖w‖ < ηr/4 ≤ r/4`
    have hw : ‖z - y - (r / 2) • v‖ < η * r / 4 := by
      rwa [mem_ball, dist_eq_norm, sub_add_eq_sub_sub] at hz
    have hw' : ‖z - y - (r / 2) • v‖ < r / 4 := hw.trans_le (by nlinarith)
    have hsv : ‖(r / 2) • v‖ = r / 2 := by rw [norm_smul, hv, mul_one, Real.norm_of_nonneg hs.le]
    have hdiff : |‖z - y‖ - r / 2| ≤ ‖z - y - (r / 2) • v‖ := by
      simpa only [hsv] using abs_norm_sub_norm_le (z - y) ((r / 2) • v)
    obtain ⟨hlo, hhi⟩ := abs_le.1 hdiff
    have hpos : 0 < ‖z - y‖ := by linarith
    refine ⟨by linarith, fun h => by rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl _ hpos,
      ?_⟩
    -- `‖z - y‖⁻¹ (z - y) - v = (‖z - y‖⁻¹ - (r/2)⁻¹) (z - y) + (r/2)⁻¹ w`
    have hdecomp : ‖z - y‖⁻¹ • (z - y) - v
        = (‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y) + (r / 2)⁻¹ • (z - y - (r / 2) • v) := by
      rw [sub_smul ‖z - y‖⁻¹ (r / 2)⁻¹ (z - y), smul_sub (r / 2)⁻¹ (z - y) ((r / 2) • v), smul_smul,
        inv_mul_cancel₀ hs.ne', one_smul]
      abel
    have h1 : ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by
      have hne : ‖z - y‖ ≠ 0 := hpos.ne'
      have e : (‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖ = (r / 2 - ‖z - y‖) / (r / 2) := by
        field_simp
      calc ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ = |(‖z - y‖⁻¹ - (r / 2)⁻¹) * ‖z - y‖| := by
            rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_norm]
        _ = |‖z - y‖ - r / 2| / (r / 2) := by rw [e, abs_div, abs_of_pos hs, abs_sub_comm]
        _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) := by gcongr
    have h2 : ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ = ‖z - y - (r / 2) • v‖ / (r / 2) := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_eq_div]
    calc ‖‖z - y‖⁻¹ • (z - y) - v‖
        ≤ ‖(‖z - y‖⁻¹ - (r / 2)⁻¹) • (z - y)‖ + ‖(r / 2)⁻¹ • (z - y - (r / 2) • v)‖ := by
          rw [hdecomp]; exact norm_add_le _ _
      _ ≤ ‖z - y - (r / 2) • v‖ / (r / 2) + ‖z - y - (r / 2) • v‖ / (r / 2) := by
          rw [h2]; linarith
      _ < η := by rw [← add_div, div_lt_iff₀ hs]; linarith
  -- for `0 < η ≤ 1`, `Z` meets `B_{ηr/4}(y + (r/2)v)` for all small `r > 0`: otherwise
  -- `Lᵈ(Z ∩ B̄_r(y)) ≤ Lᵈ(B̄_r(y)) - Lᵈ(B_{ηr/4}(y + (r/2)v)) = (1 - (η/4)ᵈ) Lᵈ(B̄_r(y))`
  have hit : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∃ z ∈ Z, z ∈ ball (y + (r / 2) • v) (η * r / 4) := by
    intro η hη hη1
    have hκ : ENNReal.ofReal ((η / 4) ^ d) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    obtain ⟨r₀, hr₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
      (hdens.eventually_const_lt (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hκ))
    refine ⟨r₀, hr₀, fun r hr hrr₀ => ?_⟩
    by_contra! hZ
    have hB : ball (y + (r / 2) • v) (η * r / 4) ⊆ closedBall y r := fun z hz => by
      rw [mem_closedBall, dist_eq_norm]; exact (cone η r hη hη1 hr z hz).1.le
    have hvol : volume (ball (y + (r / 2) • v) (η * r / 4))
        = ENNReal.ofReal ((η / 4) ^ d) * volume (closedBall y r) := by
      rw [Measure.addHaar_ball_of_pos volume _ (by positivity : (0 : ℝ) < η * r / 4),
        Measure.addHaar_closedBall volume _ hr.le, finrank_euclideanSpace_fin, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow, show η / 4 * r = η * r / 4 by ring]
    have hle : volume (Z ∩ closedBall y r)
        ≤ (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) :=
      calc volume (Z ∩ closedBall y r)
          ≤ volume (closedBall y r \ ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_mono fun z hz => ⟨hz.2, hZ z hz.1⟩
        _ = volume (closedBall y r) - volume (ball (y + (r / 2) • v) (η * r / 4)) :=
            measure_sdiff hB measurableSet_ball.nullMeasurableSet measure_ball_lt_top.ne
        _ = (1 - ENNReal.ofReal ((η / 4) ^ d)) * volume (closedBall y r) := by
            rw [hvol, ENNReal.sub_mul fun _ _ => measure_closedBall_lt_top.ne, one_mul]
    have hgt : 1 - ENNReal.ofReal ((η / 4) ^ d)
        < volume (Z ∩ closedBall y r) / volume (closedBall y r) := hsub ⟨hr, hrr₀⟩
    exact lt_irrefl _ (hgt.trans_le (ENNReal.div_le_of_le_mul hle))
  -- take `η = 1/(i+1)` and `0 < rᵢ < min(r₀, 1/(i+1))`
  have hη : ∀ i : ℕ, (0 : ℝ) < 1 / ((i : ℝ) + 1) := fun i => by positivity
  have hη1 : ∀ i : ℕ, 1 / ((i : ℝ) + 1) ≤ 1 := fun i =>
    (div_le_one (by positivity)).2 (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
  have hseq : ∀ i : ℕ, ∃ z ∈ Z, ∃ r : ℝ, 0 < r ∧ r < 1 / ((i : ℝ) + 1) ∧
      z ∈ ball (y + (r / 2) • v) (1 / ((i : ℝ) + 1) * r / 4) := by
    intro i
    obtain ⟨r₀, hr₀, h⟩ := hit _ (hη i) (hη1 i)
    have hm : 0 < min r₀ (1 / ((i : ℝ) + 1)) := lt_min hr₀ (hη i)
    obtain ⟨z, hzZ, hz⟩ := h (min r₀ (1 / ((i : ℝ) + 1)) / 2) (by positivity)
      (by linarith [min_le_left r₀ (1 / ((i : ℝ) + 1))])
    exact ⟨z, hzZ, _, by positivity, by linarith [min_le_right r₀ (1 / ((i : ℝ) + 1))], hz⟩
  choose ys hysZ rs hrs hrsi hysB using hseq
  have hcone := fun i => cone _ (rs i) (hη i) (hη1 i) (hrs i) (ys i) (hysB i)
  refine ⟨ys, fun i => ⟨hysZ i, (hcone i).2.1⟩, ?_, ?_⟩
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => ((hcone i).1.trans (hrsi i)).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => (hcone i).2.2.le)
      tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Chart pieces of a rectifiable set carrying a Lipschitz function** (Simon Ch. 3, Lemma 1.2,
Remarks 1.3 and 1.5(2), 2.1).  Given (TL), `M` is covered, up to an `H^{n+1}`-null set, by compact
pieces `ψⱼ(Cⱼ)` of injective `C¹` immersions `ψⱼ : Vⱼ → U` with `f ∘ ψⱼ = Fⱼ ∈ C¹` on `Cⱼ`
(index `j = Nat.pair s k`: piece `k` of chart `s`).  These are refined to disjoint Borel pieces
`ψⱼ(Yⱼ) ⊆ M` at whose points `TₓM = Dψⱼ(y)(ℝ^{n+1})` and `|DFⱼ(y)e| ≤ L|Dψⱼ(y)e|`; the tangential
lifts `Dψⱼ(DψⱼᵀDψⱼ)⁻¹∇Fⱼ` glue to a Borel `g` with `|g| ≤ L` (the gradient `∇^M f`). -/
theorem Submission.dor_lmbsf_lipschitz_chart_pieces : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U M : Set (Euclid P)) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → MeasurableSet M → M ⊆ U → CountablyRectifiable (n + 1) M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n + 1] (M ∩ K) ≠ ∞) → LipschitzWith L f → ∃ (V C Y : ℕ → Set (Euclid (n + 1))) (ψ : ℕ → Euclid (n + 1) → Euclid P) (F : ℕ → Euclid (n + 1) → ℝ) (g : Euclid P → Euclid P), (∀ j, IsOpen (V j) ∧ ContDiffOn ℝ 1 (ψ j) (V j) ∧ InjOn (ψ j) (V j) ∧ (∀ y ∈ V j, Injective (fderiv ℝ (ψ j) y)) ∧ ψ j '' V j ⊆ U) ∧ (∀ j, IsCompact (C j) ∧ C j ⊆ V j ∧ MeasurableSet (Y j) ∧ Y j ⊆ C j ∧ ContDiff ℝ 1 (F j)) ∧ (∀ j, ψ j '' Y j ⊆ M) ∧ Pairwise (fun i j => Disjoint (ψ i '' Y i) (ψ j '' Y j)) ∧ μHE[n + 1] (M \ ⋃ j, ψ j '' Y j) = 0 ∧ (∀ j, ∀ y ∈ Y j, f (ψ j y) = F j y ∧ HasApproximateTangentSpaceAt (n + 1) M (ψ j y) (LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P))) ∧ Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ (∀ x, (∀ j, x ∉ ψ j '' Y j) → g x = 0) ∧ ∀ j, ∀ y ∈ Y j, g (ψ j y) ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (g (ψ j y)) (fderiv ℝ (ψ j) y e) = fderiv ℝ (F j) y e := by
  intro TL P n U M f L hU hMmeas hMU hrect hfin hf
  -- `M ⊆ N₀ ∪ ⋃ₗ Nₗ` with `H^{n+1}(N₀) = 0` and embedded `C¹` submanifolds `Nₗ`
  obtain ⟨N₀, N, hN₀, hN, hMN⟩ := Submission.dor_lmbsf_rectifiable_c1_cover P (n + 1) M hrect
  -- countably many charts `ψₛ : Vₛ → U` with `M ⊆ N₀ ∪ ⋃ₛ ψₛ(Vₛ)`
  obtain ⟨V, ψ, hchart, hMV⟩ :=
    Submission.dor_lmbsf_cp_submanifold_chart_cover P (n + 1) U M N₀ N hU hMU hN hMN
  -- compact pieces `C s k ⊆ int C' s k`, `C' s k ⊆ Vₛ`, with `f ∘ ψₛ = F s k` on `C s k`,
  -- covering `Vₛ` up to a Lebesgue-null set
  choose C C' F hpiece hnull using fun s =>
    Submission.dor_lmbsf_cp_chart_c1_pieces Submission.dor_lmbsf_lipschitz_c1_approx (n + 1) P
      (V s) (ψ s) f L (hchart s).1 (hchart s).2.1 hf
  -- the pieces miss only `N₀ ∪ ⋃ₛ ψₛ(Vₛ ∖ ⋃ₖ C s k)`, which is `H^{n+1}`-null
  have hcov : μHE[n + 1] (M \ ⋃ j, ψ (Nat.unpair j).1 '' C (Nat.unpair j).1 (Nat.unpair j).2)
      = 0 := by
    refine measure_mono_null ?_ (measure_union_null hN₀ (measure_iUnion_null fun s =>
      Submission.dor_lmbsf_cp_c1_image_null (n + 1) P (V s) (V s \ ⋃ k, C s k) (ψ s)
        (hchart s).1 (hchart s).2.1 sdiff_subset (hnull s)))
    rintro x ⟨hxM, hx⟩
    rcases hMV hxM with hx₀ | hx₁
    · exact mem_union_left _ hx₀
    · obtain ⟨s, y, hyV, rfl⟩ := mem_iUnion.1 hx₁
      refine mem_union_right _ (mem_iUnion.2 ⟨s, y, ⟨hyV, fun hyC => hx ?_⟩, rfl⟩)
      obtain ⟨k, hyk⟩ := mem_iUnion.1 hyC
      exact mem_iUnion.2
        ⟨Nat.pair s k, by simpa only [Nat.unpair_pair] using mem_image_of_mem (ψ s) hyk⟩
  -- index the pieces by `j = Nat.pair s k`
  obtain ⟨Vj, ψj, Cj, C'j, Fj, hchartj, hpiecej, hcovj⟩ : ∃ (Vj : ℕ → Set (Euclid (n + 1)))
      (ψj : ℕ → Euclid (n + 1) → Euclid P) (Cj C'j : ℕ → Set (Euclid (n + 1)))
      (Fj : ℕ → Euclid (n + 1) → ℝ),
      (∀ j, IsOpen (Vj j) ∧ ContDiffOn ℝ 1 (ψj j) (Vj j) ∧ InjOn (ψj j) (Vj j) ∧
        (∀ y ∈ Vj j, Injective (fderiv ℝ (ψj j) y)) ∧ ψj j '' Vj j ⊆ U) ∧
      (∀ j, IsCompact (Cj j) ∧ IsCompact (C'j j) ∧ Convex ℝ (C'j j) ∧ Cj j ⊆ interior (C'j j) ∧
        C'j j ⊆ Vj j ∧ ContDiff ℝ 1 (Fj j) ∧ ∀ y ∈ Cj j, f (ψj j y) = Fj j y) ∧
      μHE[n + 1] (M \ ⋃ j, ψj j '' Cj j) = 0 :=
    ⟨fun j => V (Nat.unpair j).1, fun j => ψ (Nat.unpair j).1,
      fun j => C (Nat.unpair j).1 (Nat.unpair j).2, fun j => C' (Nat.unpair j).1 (Nat.unpair j).2,
      fun j => F (Nat.unpair j).1 (Nat.unpair j).2, fun j => hchart _, fun j => hpiece _ _, hcov⟩
  have hCV : ∀ j, Cj j ⊆ Vj j := fun j =>
    (hpiecej j).2.2.2.1.trans (interior_subset.trans (hpiecej j).2.2.2.2.1)
  -- (TL) and the tangent planes of `ψⱼ(C'ⱼ)`: `TₓM = Dψⱼ(y)(ℝ^{n+1})` a.e. on `M ∩ ψⱼ(Cⱼ)`
  have htan : ∀ j, ∀ᵐ x ∂(μHE[n + 1].restrict (M ∩ ψj j '' Cj j)), ∀ y ∈ Cj j, ψj j y = x →
      HasApproximateTangentSpaceAt (n + 1) M x
        (LinearMap.range (fderiv ℝ (ψj j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P)) := by
    intro j
    obtain ⟨hVo, hψc, hψi, hψd, hψU⟩ := hchartj j
    obtain ⟨hCc, hC'c, hC'conv, hCC', hC'V, -, -⟩ := hpiecej j
    exact Submission.dor_lmbsf_cp_chart_tangent_ae TL P (n + 1) U M (Cj j) (C'j j) (ψj j) hU
      hMmeas hMU hfin (hψc.mono hC'V) ((image_mono hC'V).trans hψU) hCc hC'c hC'conv hCC'
      fun y hy => Submission.dor_lmbsf_c1_image_approxTangent (n + 1) P (Vj j) (C'j j) (ψj j) y
        hVo hψc hC'c hC'V (hψi.mono hC'V) hy (hψd y (hC'V (interior_subset hy)))
  -- density points: `|DFⱼ(y)e| ≤ L|Dψⱼ(y)e|` off a Lebesgue-null set, whose image is null
  have hbd : ∀ j, ∀ᵐ x ∂(μHE[n + 1].restrict (M ∩ ψj j '' Cj j)), ∀ y ∈ Cj j, ψj j y = x →
      ∀ e : Euclid (n + 1), |fderiv ℝ (Fj j) y e| ≤ (L : ℝ) * ‖fderiv ℝ (ψj j) y e‖ := by
    intro j
    obtain ⟨hVo, hψc, -, -, -⟩ := hchartj j
    obtain ⟨hCc, -, -, -, -, hFc, hfF⟩ := hpiecej j
    have hae := ae_iff.1 (Submission.dor_lmbsf_cp_gradient_bound_ae
      Submission.dor_lmbsf_density_directions (n + 1) P (Cj j) (Fj j) (ψj j) f L hCc.measurableSet
      (fun y hy => ⟨hFc.differentiable one_ne_zero y,
        (hψc.differentiableOn one_ne_zero).differentiableAt (hVo.mem_nhds (hCV j hy))⟩) hfF hf)
    refine ae_restrict_of_ae (ae_iff.2 (measure_mono_null ?_
      (Submission.dor_lmbsf_cp_c1_image_null (n + 1) P (Vj j) _ (ψj j) hVo hψc ?_ hae)))
    · intro x hx
      by_contra hx'
      refine hx fun y hy hyx => ?_
      subst hyx
      by_contra hbad
      exact hx' ⟨y, fun h => hbad (h hy), rfl⟩
    · exact fun y hy => hCV j (not_imp.1 hy).1
  -- disjoint Borel pieces `ψⱼ(Yⱼ) ⊆ M` consisting of good points
  obtain ⟨Y, hY, hdisj, hYnull⟩ := Submission.dor_lmbsf_cp_disjoint_refinement (n + 1) P
    μHE[n + 1] M Cj ψj
    (fun j y => HasApproximateTangentSpaceAt (n + 1) M (ψj j y)
        (LinearMap.range (fderiv ℝ (ψj j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P)) ∧
      ∀ e : Euclid (n + 1), |fderiv ℝ (Fj j) y e| ≤ (L : ℝ) * ‖fderiv ℝ (ψj j) y e‖)
    hMmeas (fun j => ⟨(hpiecej j).1, (hchartj j).2.1.continuousOn.mono (hCV j)⟩) hcovj
    fun j => by
      filter_upwards [htan j, hbd j] with x h₁ h₂ y hy hyx
      subst hyx
      exact ⟨h₁ y hy rfl, h₂ y hy rfl⟩
  have hYV : ∀ j, Y j ⊆ Vj j := fun j => (hY j).2.1.trans (hCV j)
  -- tangential lifts `Φⱼ` of `DFⱼ` (e.g. `Dψⱼ(DψⱼᵀDψⱼ)⁻¹∇Fⱼ`), glued into a Borel `g`,
  -- zero off `⋃ⱼ ψⱼ(Yⱼ)`
  choose Φ hΦc hΦ using fun j => Submission.dor_lmbsf_cp_chart_tangent_lift (n + 1) P (Vj j)
    (ψj j) (Fj j) (hchartj j).1 (hchartj j).2.1 (hchartj j).2.2.2.1 (hpiecej j).2.2.2.2.2.1
  obtain ⟨g, hgm, hgval, hg0⟩ := Submission.dor_lmbsf_cp_measurable_glue (n + 1) P Y ψj Φ
    (fun j => ⟨(hY j).1, (hchartj j).2.1.continuousOn.mono (hYV j),
      (hchartj j).2.2.1.mono (hYV j), (hΦc j).mono (hYV j)⟩) hdisj
  refine ⟨Vj, Cj, Y, ψj, Fj, g, hchartj, fun j => ⟨(hpiecej j).1, hCV j, (hY j).1, (hY j).2.1,
    (hpiecej j).2.2.2.2.2.1⟩, fun j => (hY j).2.2.1, hdisj, hYnull,
    fun j y hy => ⟨(hpiecej j).2.2.2.2.2.2 y ((hY j).2.1 hy), ((hY j).2.2.2 y hy).1⟩, hgm,
    fun x => ?_, hg0, fun j y hy => ?_⟩
  · by_cases hx : ∃ j, x ∈ ψj j '' Y j
    · obtain ⟨j, y, hy, rfl⟩ := hx
      rw [hgval j y hy]
      exact (hΦ j y (hYV j hy)).2.2 L ((hY j).2.2.2 y hy).2
    · rw [hg0 x fun j hj => hx ⟨j, hj⟩, norm_zero]
      exact L.coe_nonneg
  · rw [hgval j y hy]
    exact ⟨(hΦ j y (hYV j hy)).1, (hΦ j y (hYV j hy)).2.1⟩

/-- **Slice area formula and Tonelli** (Simon Ch. 2, (3.5), sliced along the first coordinate).
Let `S ⊆ ℝⁿ⁺¹` be Borel and `Φ : ℝⁿ⁺¹ → ℝᴾ` differentiable with injective `DΦ(w)` at every
`w ∈ S` and injective on `S`; put `J'(w) = √det(⟨DΦ(w)eᵢ₊₁, DΦ(w)eⱼ₊₁⟩)`.  Then for Borel `φ ≥ 0`,
`t ↦ ∫_{Φ(S ∩ {w₀ = t})} φ dHⁿ` is a.e.-measurable and
`∫_ℝ ∫_{Φ(S ∩ {w₀ = t})} φ dHⁿ dt = ∫_S J'(w) φ(Φ(w)) dw`.  With `ins_t(z) = (t, z)` and
`ι(z) = (0, z)`, the slice `Φ(S ∩ {w₀ = t})` is the injective image of `S_t = ins_t⁻¹(S)` under
`Φ ∘ ins_t`, whose derivative `DΦ(ins_t z) ∘ ι` is injective with `ι eₖ = eₖ₊₁`; so the Gram area
formula (`codim1_lura_gram_area_formula`) gives `∫_{ℝⁿ} H(ins_t z) dz` for the Borel integrand
`H = 1_S · J' · (φ ∘ Φ)`.  The splitting `(t, z) ↦ ins_t(z)`, `ℝ × ℝⁿ ≅ ℝⁿ⁺¹`, is measure
preserving (`ofLp`, `piFinSuccAbove 0`, `toLp`), and Tonelli gives both claims. -/
theorem Submission.dor_lmbsf_pc_slice_area_tonelli : ∀ (P n : ℕ) (Φ : Euclid (n + 1) → Euclid P) (S : Set (Euclid (n + 1))), MeasurableSet S → (∀ w ∈ S, DifferentiableAt ℝ Φ w) → (∀ w ∈ S, Injective (fderiv ℝ Φ w)) → InjOn Φ S → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) = ∫⁻ w in S, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i.succ 1)) (fderiv ℝ Φ w (EuclideanSpace.single j.succ 1))))) * φ (Φ w) ∂volume := by
  have hR := Submission.codim1_lura_gram_area_formula
  intro P n Φ S hS hd hinj hInj φ hφ
  classical
  -- the slice embeddings `z ↦ (t, z)` and their common linear part `ι`
  let ins : ℝ → Euclid n → Euclid (n + 1) := fun t z =>
    WithLp.toLp 2 (Fin.cons t (WithLp.ofLp z) : Fin (n + 1) → ℝ)
  let ιlin : Euclid n →ₗ[ℝ] Euclid (n + 1) :=
    { toFun := fun z => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp z) : Fin (n + 1) → ℝ)
      map_add' := by
        intro y z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
      map_smul' := by
        intro c y; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp }
  let ι : Euclid n →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap ιlin
  have hins : ∀ t z, ins t z = ins t 0 + ι z := by
    intro t z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp [ins, ι, ιlin]
  have hinsD : ∀ t z, HasFDerivAt (ins t) ι z := by
    intro t z
    have : ins t = fun z => ins t 0 + ι z := funext (hins t)
    rw [this]
    exact ι.hasFDerivAt.const_add _
  have hιe : ∀ k : Fin n, ι (EuclideanSpace.single k 1) = EuclideanSpace.single k.succ 1 := by
    intro k; ext j; refine Fin.cases ?_ (fun l => ?_) j <;> simp [ι, ιlin, Pi.single_apply]
  -- slice Jacobian and integrand
  let J' : Euclid (n + 1) → ℝ := fun w => Real.sqrt (Matrix.det (Matrix.of fun i j : Fin n =>
    inner ℝ (fderiv ℝ Φ w (EuclideanSpace.single i.succ 1)) (fderiv ℝ Φ w (EuclideanSpace.single j.succ 1))))
  have hJ'm : Measurable J' := by
    have hc : Continuous (fun L : Euclid (n + 1) →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun i j : Fin n => inner ℝ (L (EuclideanSpace.single i.succ 1))
          (L (EuclideanSpace.single j.succ 1))))) := by
      refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
      refine continuous_pi fun k => continuous_pi fun l => ?_
      exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
    exact hc.measurable.comp (measurable_fderiv ℝ Φ)
  let H : Euclid (n + 1) → ℝ≥0∞ := S.indicator (fun w => ENNReal.ofReal (J' w) * φ (Φ w))
  have hΦc : ContinuousOn Φ S := fun w hw => (hd w hw).continuousAt.continuousWithinAt
  have hHm : Measurable H := by
    have hpw : Measurable (S.piecewise Φ (fun _ => 0)) :=
      hΦc.measurable_piecewise continuousOn_const hS
    have : H = S.indicator (fun w => ENNReal.ofReal (J' w) * φ (S.piecewise Φ (fun _ => 0) w)) := by
      ext w
      by_cases hw : w ∈ S
      · simp [H, hw, Set.piecewise_eq_of_mem]
      · simp [H, hw]
    rw [this]
    exact ((hJ'm.ennreal_ofReal).mul (hφ.comp hpw)).indicator hS
  -- the inner integral, slice by slice
  have hinner : ∀ t : ℝ, ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n] = ∫⁻ z, H (ins t z) := by
    intro t
    let St : Set (Euclid n) := ins t ⁻¹' S
    have hinsc : Continuous (ins t) := by
      have : ins t = fun z => ins t 0 + ι z := funext (hins t)
      rw [this]; exact continuous_const.add ι.continuous
    have hSt : MeasurableSet St := hinsc.measurable hS
    have himg : Φ '' (S ∩ {w | w 0 = t}) = (Φ ∘ ins t) '' St := by
      rw [image_comp]
      congr 1
      ext w
      constructor
      · rintro ⟨hwS, hwt⟩
        refine ⟨WithLp.toLp 2 (Fin.tail (WithLp.ofLp w)), ?_, ?_⟩
        · have : ins t (WithLp.toLp 2 (Fin.tail (WithLp.ofLp w))) = w := by
            ext j; refine Fin.cases ?_ (fun k => ?_) j
            · simpa [ins] using hwt.symm
            · simp [ins, Fin.tail]
          show ins t _ ∈ S
          rw [this]; exact hwS
        · ext j; refine Fin.cases ?_ (fun k => ?_) j
          · simpa [ins] using hwt.symm
          · simp [ins, Fin.tail]
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz, by simp [ins]⟩
    have hdt : ∀ z ∈ St, DifferentiableAt ℝ (Φ ∘ ins t) z := fun z hz =>
      (hd _ hz).comp z (hinsD t z).differentiableAt
    have hDt : ∀ z ∈ St, fderiv ℝ (Φ ∘ ins t) z = (fderiv ℝ Φ (ins t z)).comp ι := fun z hz =>
      ((hd _ hz).hasFDerivAt.comp z (hinsD t z)).fderiv
    have hιinj : Injective ι := by
      intro y z hyz
      ext k
      have := congrArg (fun v : Euclid (n + 1) => v k.succ) hyz
      simpa [ι, ιlin] using this
    have hinjt : ∀ z ∈ St, Injective (fderiv ℝ (Φ ∘ ins t) z) := by
      intro z hz
      rw [hDt z hz]
      exact (hinj _ hz).comp hιinj
    have hInjt : InjOn (Φ ∘ ins t) St := by
      intro y hy z hz hyz
      have h1 : ins t y = ins t z := hInj hy hz hyz
      have h2 : ι y = ι z := by
        rw [hins t y, hins t z] at h1; exact add_left_cancel h1
      exact hιinj h2
    rw [himg, (hR n P (Φ ∘ ins t)).2 St hSt hdt hinjt hInjt φ, ← lintegral_indicator hSt]
    congr 1
    ext z
    by_cases hz : z ∈ St
    · have hz' : ins t z ∈ S := hz
      simp only [indicator_of_mem hz, H, indicator_of_mem hz', hDt z hz, J',
        ContinuousLinearMap.comp_apply, hιe, comp_apply]
    · have hz' : ins t z ∉ S := hz
      simp only [indicator_of_notMem hz, H, indicator_of_notMem hz']
  -- the volume-preserving splitting `ℝ × ℝⁿ ≃ ℝⁿ⁺¹`
  have he : MeasurePreserving (fun p : ℝ × Euclid n => ins p.1 p.2) volume volume := by
    have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : Euclid n → (Fin n → ℝ)))
        (volume : Measure (ℝ × Euclid n)) (volume : Measure (ℝ × (Fin n → ℝ))) :=
      (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin n))
    have h2 := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have h3 := PiLp.volume_preserving_toLp (Fin (n + 1))
    have h := h3.comp (h2.comp h1)
    convert h using 1
    funext p
    simp [ins, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  have hHe : Measurable (fun p : ℝ × Euclid n => H (ins p.1 p.2)) := hHm.comp he.measurable
  refine ⟨?_, ?_⟩
  · simp_rw [hinner]
    exact hHe.lintegral_prod_right'.aemeasurable
  · simp_rw [hinner]
    rw [← lintegral_indicator hS]
    change ∫⁻ t, ∫⁻ z, H (ins t z) = ∫⁻ w, H w
    rw [← he.lintegral_comp hHm]
    exact (lintegral_prod _ hHe.aemeasurable).symm

/-- **Co-area formula for a patch parametrized over the slices `{w(0) = t}`** (Simon Ch. 2, §6).
Let `S ⊆ ℝⁿ⁺¹` be Borel, `Φ : ℝⁿ⁺¹ → ℝᴾ` differentiable with injective `DΦ(w)` at every `w ∈ S`
and injective on `S`, and let `G(Φ(w)) ∈ DΦ(w)(ℝⁿ⁺¹)` with `⟨G(Φ(w)), DΦ(w)e⟩ = e(0)` for
`w ∈ S`.  Then for Borel `φ ≥ 0`, `t ↦ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ` is a.e.-measurable and
`∫_ℝ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ dt = ∫_{Φ(S)} |G| φ dHⁿ⁺¹`.
Let `J(w)`, `J'(w)` be the Gram-determinant Jacobians of `DΦ(w)` on `e₀, …, eₙ` and on
`e₁, …, eₙ`.  Slicing gives `∫_ℝ ∫_{Φ(S ∩ {w(0) = t})} φ dHⁿ dt = ∫_S J'(w) φ(Φ(w)) dw`, the area
formula gives `∫_{Φ(S)} |G| φ dHⁿ⁺¹ = ∫_S J(w) |G(Φ(w))| φ(Φ(w)) dw`, and at `w ∈ S` the vector
`u = G(Φ(w))` lies in the span of the `aₗ = DΦ(w)eₗ` with `⟨u, aₗ⟩ = δₗ₀`, so the Gram cofactor
identity `det(⟨aᵢ₊₁, aⱼ₊₁⟩) = |u|² det(⟨aᵢ, aⱼ⟩)` gives `J'(w) = |u| J(w)`. -/
theorem Submission.dor_lmbsf_pc_param_coarea : ∀ (P n : ℕ) (Φ : Euclid (n + 1) → Euclid P) (S : Set (Euclid (n + 1))) (G : Euclid P → Euclid P), MeasurableSet S → (∀ w ∈ S, DifferentiableAt ℝ Φ w) → (∀ w ∈ S, Injective (fderiv ℝ Φ w)) → InjOn Φ S → (∀ w ∈ S, G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (Φ w)) (fderiv ℝ Φ w e) = e 0) → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in Φ '' (S ∩ {w | w 0 = t}), φ x ∂μHE[n]) = ∫⁻ x in Φ '' S, ‖G x‖ₑ * φ x ∂μHE[n + 1] := by
  intro P n Φ S G hS hd hinj hInj hG φ hφ
  -- slicing: the slice integral is a.e.-measurable in `t` and integrates to `∫_S J' · φ ∘ Φ`
  obtain ⟨hmeas, heq⟩ :=
    Submission.dor_lmbsf_pc_slice_area_tonelli P n Φ S hS hd hinj hInj φ hφ
  refine ⟨hmeas, ?_⟩
  -- area formula with weight `|G| φ`: `∫_{Φ(S)} |G| φ dHⁿ⁺¹ = ∫_S J · (|G| φ) ∘ Φ`
  rw [heq, (Submission.codim1_lura_gram_area_formula (n + 1) P Φ).2 S hS hd hinj hInj
    (fun x => ‖G x‖ₑ * φ x)]
  -- the integrands agree on `S`: `J'(w) = |G(Φ(w))| J(w)`
  refine setLIntegral_congr_fun hS fun w hw => ?_
  obtain ⟨⟨v, hv⟩, hinner⟩ := hG w hw
  set a : Fin (n + 1) → Euclid P := fun i => fderiv ℝ Φ w (EuclideanSpace.single i 1)
  -- `u = G(Φ(w)) = DΦ(w)v = Σₗ vₗ aₗ` lies in the span of the `aₗ`
  have hspan : G (Φ w) ∈ Submodule.span ℝ (Set.range a) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => v i, ?_⟩
    have hv' : fderiv ℝ Φ w v = G (Φ w) := hv
    rw [← hv']
    have hvsum : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    conv_rhs => rw [hvsum]
    simp [a, map_sum, map_smul]
  -- `⟨u, aₗ⟩ = eₗ(0) = δₗ₀`
  have ha0 : inner ℝ (G (Φ w)) (a 0) = 1 := by
    simp [a, hinner]
  have hak : ∀ k : Fin n, inner ℝ (G (Φ w)) (a k.succ) = 0 := by
    intro k
    simp [a, hinner, Fin.succ_ne_zero]
  -- Gram cofactor identity, then square roots
  have hgram := Submission.dor_lmbsf_pc_gram_det_succ_eq P n a (G (Φ w)) hspan ha0 hak
  simp only [a] at hgram
  rw [hgram, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  ring
/-- Step 6 of the oriented graph chart (zero-scale limit plane, Simon 7.5.8): the inverse function
theorem with a `C¹` local inverse on an open target (as used in Simon Ch. 2, §4).  If `φ` is `C¹`
on an open `V ∋ z₀` and `Dφ(z₀)` is injective, then `Dφ(z₀)` is invertible, so
`V₁ = V ∩ {z : Dφ(z) invertible}` is an open neighbourhood of `z₀`.  The inverse function theorem
restricted to `V₁` gives `φ : V₀ → O` bijective with inverse `χ`, and `χ` is `C¹` at every
`a ∈ O` because `Dφ(χ(a))` is invertible. -/
theorem Submission.codim1_zsl_gc_local_inverse : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 1 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (χ : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 1 χ O ∧ MapsTo χ O V₀ ∧ (∀ a ∈ O, φ (χ a) = a) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ χ (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  -- `Dφ(z₀)` is invertible (injective endomorphism of a finite-dimensional space)
  let L₀ : Euclid d ≃L[ℝ] Euclid d :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ φ z₀ : Euclid d →L[ℝ] Euclid d) : Euclid d →ₗ[ℝ] Euclid d)
      hinj).toContinuousLinearEquiv
  have hL₀ : (L₀ : Euclid d →L[ℝ] Euclid d) = fderiv ℝ φ z₀ := by
    ext x; rfl
  have hcd : ∀ z ∈ V, ContDiffAt ℝ 1 φ z := fun z hz => hφ.contDiffAt (hV.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV le_rfl
  -- the open set `V₁` where `Dφ` is invertible
  let V₁ : Set (Euclid d) :=
    V ∩ fderiv ℝ φ ⁻¹' range ((↑) : (Euclid d ≃L[ℝ] Euclid d) → Euclid d →L[ℝ] Euclid d)
  have hV₁ : IsOpen V₁ := hcont.isOpen_inter_preimage hV ContinuousLinearEquiv.isOpen
  have hz₀V₁ : z₀ ∈ V₁ := ⟨hz₀, L₀, hL₀⟩
  have hstrict : HasStrictFDerivAt φ (L₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hL₀]
    exact (hcd z₀ hz₀).hasStrictFDerivAt one_ne_zero
  -- the inverse function theorem, restricted to `V₁`
  obtain ⟨e, he, hz₀e, hsrc⟩ : ∃ e : OpenPartialHomeomorph (Euclid d) (Euclid d),
      ⇑e = φ ∧ z₀ ∈ e.source ∧ e.source ⊆ V₁ :=
    ⟨(hstrict.toOpenPartialHomeomorph φ).restrOpen V₁ hV₁, rfl,
      ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀V₁⟩, inter_subset_right⟩
  subst he
  refine ⟨e.source, e.target, e.symm, e.open_source, e.open_target, hz₀e,
    fun z hz => (hsrc hz).1, ?_, e.mapsTo_symm, fun a ha => e.right_inv ha,
    fun z hz => ⟨e.map_source hz, e.left_inv hz⟩⟩
  -- `χ = e.symm` is `C¹` at each `a ∈ O`, since `Dφ(χ(a))` is invertible
  intro a ha
  obtain ⟨hV', L, hL⟩ := hsrc (e.map_target ha)
  have hd : HasFDerivAt e (L : Euclid d →L[ℝ] Euclid d) (e.symm a) := by
    rw [hL]
    exact ((hcd _ hV').differentiableAt one_ne_zero).hasFDerivAt
  exact (e.contDiffAt_symm ha hd (hcd _ hV')).contDiffWithinAt

/-- Straightening charts for the co-area step of the limsup mass bound (density one implies
regular, Simon 7.5 via the co-area formula of Ch. 2, §5): if `F : ℝ^{n+1} → ℝ` is `C¹`, then
`{DF ≠ 0}` is covered by countably many open sets `Ψ_q(B_q)`, where `B_q` is open and `Ψ_q` is
`C¹`, injective and with bijective derivative on `B_q`, and `F(Ψ_q(w)) = w(0)` on `B_q`.  Near `y₀`
with `DF(y₀) e_i ≠ 0` the map `Θ(y) = (F(y), y ∘ i.succAbove)` has injective derivative at `y₀`, so
its local inverse `χ` on an open `O` (`codim1_zsl_gc_local_inverse`) is such a chart with
`y₀ ∈ χ(O)`; second countability selects countably many of these charts. -/
theorem Submission.dor_lmbsf_pc_straightening_cover : ∀ (n : ℕ) (F : Euclid (n + 1) → ℝ), ContDiff ℝ 1 F → ∃ (B : ℕ → Set (Euclid (n + 1))) (Ψ : ℕ → Euclid (n + 1) → Euclid (n + 1)), (∀ q, IsOpen (B q)) ∧ (∀ q, ContDiffOn ℝ 1 (Ψ q) (B q)) ∧ (∀ q, InjOn (Ψ q) (B q)) ∧ (∀ q, ∀ w ∈ B q, Bijective (fderiv ℝ (Ψ q) w)) ∧ (∀ q, ∀ w ∈ B q, F (Ψ q w) = w 0) ∧ (∀ q, IsOpen (Ψ q '' B q)) ∧ {y | fderiv ℝ F y ≠ 0} ⊆ ⋃ q, Ψ q '' B q := by
  have hR3 := Submission.codim1_zsl_gc_local_inverse
  intro n F hF
  classical
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  -- pointwise straightening
  have hloc : ∀ y₀ : Euclid (n + 1), fderiv ℝ F y₀ ≠ 0 →
      ∃ (B : Set (Euclid (n + 1))) (Ψ : Euclid (n + 1) → Euclid (n + 1)), IsOpen B ∧
        ContDiffOn ℝ 1 Ψ B ∧ InjOn Ψ B ∧ (∀ w ∈ B, Bijective (fderiv ℝ Ψ w)) ∧
        (∀ w ∈ B, F (Ψ w) = w 0) ∧ IsOpen (Ψ '' B) ∧ y₀ ∈ Ψ '' B := by
    intro y₀ hy₀
    have hexp : ∀ v : Euclid (n + 1), v = ∑ j, v j • EuclideanSpace.single j (1 : ℝ) := by
      intro v; ext j; simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), fderiv ℝ F y₀ (EuclideanSpace.single i 1) ≠ 0 := by
      by_contra! h
      apply hy₀
      ext1 v
      rw [hexp v, map_sum]
      simp [h]
    -- the linear part `y ↦ (0, y ∘ i.succAbove)`
    let Llin : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1) :=
      { toFun := fun y => WithLp.toLp 2 (Fin.cons 0 (fun k => y (i.succAbove k)) : Fin (n + 1) → ℝ)
        map_add' := by
          intro y z; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp
        map_smul' := by
          intro c y; ext j; refine Fin.cases ?_ (fun k => ?_) j <;> simp }
    let L : Euclid (n + 1) →L[ℝ] Euclid (n + 1) := LinearMap.toContinuousLinearMap Llin
    have hL0 : ∀ y, L y 0 = 0 := fun y => by simp [L, Llin]
    have hLs : ∀ y (k : Fin n), L y k.succ = y (i.succAbove k) := fun y k => by simp [L, Llin]
    let e0 : Euclid (n + 1) := EuclideanSpace.single 0 1
    let Θ : Euclid (n + 1) → Euclid (n + 1) := fun y => F y • e0 + L y
    have hΘ0 : ∀ y, Θ y 0 = F y := fun y => by simp [Θ, e0, hL0]
    have hΘc : ContDiff ℝ 1 Θ := (hF.smul contDiff_const).add L.contDiff
    have hΘD : ∀ y, fderiv ℝ Θ y = (fderiv ℝ F y).smulRight e0 + L := by
      intro y
      have h1 : HasFDerivAt (fun y => F y • e0) ((fderiv ℝ F y).smulRight e0) y :=
        (hFd y).hasFDerivAt.smul_const e0
      exact (h1.add L.hasFDerivAt).fderiv
    have hinj0 : Injective (fderiv ℝ Θ y₀) := by
      rw [hΘD y₀]
      have hker : ∀ h : Euclid (n + 1), ((fderiv ℝ F y₀).smulRight e0 + L) h = 0 → h = 0 := by
        intro h hh
        have hc0 := congrArg (fun v : Euclid (n + 1) => v 0) hh
        have hcs : ∀ k : Fin n, h (i.succAbove k) = 0 := by
          intro k
          have := congrArg (fun v : Euclid (n + 1) => v k.succ) hh
          simpa [e0, hLs, Fin.succ_ne_zero] using this
        have hhi : h = h i • EuclideanSpace.single i (1 : ℝ) := by
          ext j
          rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
          · simp
          · simp [hcs k, Fin.succAbove_ne]
        have hDF : fderiv ℝ F y₀ h = 0 := by simpa [e0, hL0] using hc0
        rw [hhi, map_smul, smul_eq_mul] at hDF
        have hi0 : h i = 0 := by
          rcases mul_eq_zero.mp hDF with h' | h'
          · exact h'
          · exact absurd h' hi
        rw [hhi, hi0, zero_smul]
      intro h1 h2 h12
      have := hker (h1 - h2) (by rw [map_sub, h12, sub_self])
      exact sub_eq_zero.mp this
    obtain ⟨V₀, O, χ, hV₀, hO, hy₀V₀, -, hχ, hχmaps, hΘχ, hχΘ⟩ :=
      hR3 (n + 1) Θ univ y₀ isOpen_univ (mem_univ _) hΘc.contDiffOn hinj0
    have hχd : ∀ a ∈ O, DifferentiableAt ℝ χ a := fun a ha =>
      (hχ.differentiableOn one_ne_zero a ha).differentiableAt (hO.mem_nhds ha)
    have himg : χ '' O = V₀ := by
      apply Subset.antisymm
      · rintro _ ⟨a, ha, rfl⟩; exact hχmaps ha
      · intro z hz; exact ⟨Θ z, (hχΘ z hz).1, (hχΘ z hz).2⟩
    refine ⟨O, χ, hO, hχ, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      rw [← hΘχ a ha, ← hΘχ b hb, hab]
    · intro a ha
      have hid : fderiv ℝ (Θ ∘ χ) a = ContinuousLinearMap.id ℝ (Euclid (n + 1)) := by
        rw [Filter.EventuallyEq.fderiv_eq (f₁ := Θ ∘ χ) (f := id) ?_, fderiv_id]
        filter_upwards [hO.mem_nhds ha] with b hb using hΘχ b hb
      rw [fderiv_comp a (hΘc.differentiable one_ne_zero _) (hχd a ha)] at hid
      have hli : Function.LeftInverse (fderiv ℝ Θ (χ a)) (fderiv ℝ χ a) := fun u => by
        simpa using DFunLike.congr_fun hid u
      have hinj : Injective (fderiv ℝ χ a) := hli.injective
      exact ⟨hinj, LinearMap.surjective_of_injective
        (f := (fderiv ℝ χ a : Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))) hinj⟩
    · intro a ha
      rw [← hΘ0, hΘχ a ha]
    · rw [himg]; exact hV₀
    · rw [himg]; exact hy₀V₀
  let O' : Set (Euclid (n + 1)) := {y | fderiv ℝ F y ≠ 0}
  choose! Bf Ψf hBf hΨf hinjf hbijf hFf hopenf hmemf using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun y : O' => Ψf y '' Bf y) (fun y => hopenf y y.2)
  by_cases hT : T.Nonempty
  · obtain ⟨e, he⟩ := hTc.exists_eq_range hT
    refine ⟨fun q => Bf (e q), fun q => Ψf (e q), fun q => hBf _ (e q).2, fun q => hΨf _ (e q).2,
      fun q => hinjf _ (e q).2, fun q => hbijf _ (e q).2, fun q => hFf _ (e q).2,
      fun q => hopenf _ (e q).2, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, hz⟩ := mem_iUnion₂.mp h1
    rw [he] at hzT
    obtain ⟨q, rfl⟩ := hzT
    exact mem_iUnion.mpr ⟨q, hz⟩
  · refine ⟨fun _ => ∅, fun _ => id, fun _ => isOpen_empty, fun _ => contDiff_id.contDiffOn,
      fun _ => injOn_empty _, fun _ _ h => absurd h (notMem_empty _),
      fun _ _ h => absurd h (notMem_empty _), fun _ => by simp, ?_⟩
    intro y hy
    have h1 : y ∈ ⋃ z : O', Ψf z '' Bf z := mem_iUnion.mpr ⟨⟨y, hy⟩, hmemf y hy⟩
    rw [← hTU] at h1
    obtain ⟨z, hzT, -⟩ := mem_iUnion₂.mp h1
    exact absurd ⟨z, hzT⟩ hT

/-- **Co-area formula on one straightened patch of a `C¹` chart** (Simon Ch. 2, §6; Ch. 3,
(2.8)–(2.9)).  Let `ψ : ℝⁿ⁺¹ → ℝᴾ` be `C¹` and injective with injective `Dψ` on the open set `V`,
`F : ℝⁿ⁺¹ → ℝ` be `C¹`, and `Ψ : ℝⁿ⁺¹ → ℝⁿ⁺¹` be `C¹` and injective with bijective `DΨ` on the
open set `B`, straightening `F` to the first coordinate: `F(Ψ(w)) = w(0)` on `B`.  Let
`Z ⊆ V ∩ Ψ(B)` be Borel, with `G(ψ(y)) ∈ Dψ(y)(ℝⁿ⁺¹)` and `⟨G(ψ(y)), Dψ(y)e⟩ = DF(y)e` for
`y ∈ Z`.  Then for Borel `φ ≥ 0`, `t ↦ ∫_{ψ(Z ∩ F⁻¹(t))} φ dHⁿ` is a.e.-measurable and
`∫_ℝ ∫_{ψ(Z ∩ F⁻¹(t))} φ dHⁿ dt = ∫_{ψ(Z)} |G| φ dHⁿ⁺¹`.
On the Borel patch `S = B ∩ Ψ⁻¹(Z)` the map `Φ = ψ ∘ Ψ` is injective, with injective derivative
`DΦ(w) = Dψ(Ψ(w)) ∘ DΨ(w)`.  Since `F ∘ Ψ` is the first coordinate on `B`,
`DF(Ψ(w)) ∘ DΨ(w) = (e ↦ e(0))`, so `G(Φ(w)) ∈ DΦ(w)(ℝⁿ⁺¹)` and `⟨G(Φ(w)), DΦ(w)e⟩ = e(0)`.  The
patch co-area formula applies to `(Φ, S)`, and `Φ(S) = ψ(Z)`,
`Φ(S ∩ {w(0) = t}) = ψ(Z ∩ F⁻¹(t))`. -/
theorem Submission.dor_lmbsf_pc_chart_patch_coarea : ∀ (P n : ℕ) (V B Z : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (Ψ : Euclid (n + 1) → Euclid (n + 1)) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ContDiff ℝ 1 F → IsOpen B → ContDiffOn ℝ 1 Ψ B → InjOn Ψ B → (∀ w ∈ B, Bijective (fderiv ℝ Ψ w)) → (∀ w ∈ B, F (Ψ w) = w 0) → MeasurableSet Z → Z ⊆ V → Z ⊆ Ψ '' B → (∀ y ∈ Z, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Z, ‖G x‖ₑ * φ x ∂μHE[n + 1] := by
  intro P n V B Z ψ F Ψ G hV hψ hψinj hψreg hF hB hΨ hΨinj hΨbij hFΨ hZ hZV hZB hG φ hφ
  have hΨd : ∀ w ∈ B, DifferentiableAt ℝ Ψ w := fun w hw =>
    (hΨ.differentiableOn one_ne_zero w hw).differentiableAt (hB.mem_nhds hw)
  have hψd : ∀ y ∈ V, DifferentiableAt ℝ ψ y := fun y hy =>
    (hψ.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy)
  -- the patch `S = B ∩ Ψ⁻¹(Z)` is Borel: `Ψ` is continuous on the open set `B`
  set S : Set (Euclid (n + 1)) := B ∩ Ψ ⁻¹' Z with hSdef
  have hSm : MeasurableSet S := by
    classical
    have hpw : Measurable (B.piecewise Ψ (fun _ => 0)) :=
      hΨ.continuousOn.measurable_piecewise continuousOn_const hB.measurableSet
    have : S = B ∩ (B.piecewise Ψ (fun _ => 0)) ⁻¹' Z := by
      ext w
      constructor
      · rintro ⟨hw, hwZ⟩
        exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hwZ⟩
      · rintro ⟨hw, hwZ⟩
        exact ⟨hw, by simpa [Set.piecewise_eq_of_mem _ _ _ hw] using hwZ⟩
    rw [this]
    exact hB.measurableSet.inter (hpw hZ)
  -- `Φ = ψ ∘ Ψ` is differentiable and injective on `S`, with `DΦ(w) = Dψ(Ψ(w)) ∘ DΨ(w)` injective
  set Φ : Euclid (n + 1) → Euclid P := ψ ∘ Ψ with hΦdef
  have hSZ : ∀ w ∈ S, Ψ w ∈ Z := fun w hw => hw.2
  have hΦd : ∀ w ∈ S, DifferentiableAt ℝ Φ w := fun w hw =>
    (hψd _ (hZV (hSZ w hw))).comp w (hΨd w hw.1)
  have hΦD : ∀ w ∈ S, fderiv ℝ Φ w = (fderiv ℝ ψ (Ψ w)).comp (fderiv ℝ Ψ w) := fun w hw =>
    fderiv_comp w (hψd _ (hZV (hSZ w hw))) (hΨd w hw.1)
  have hΦinjD : ∀ w ∈ S, Injective (fderiv ℝ Φ w) := by
    intro w hw
    rw [hΦD w hw]
    exact (hψreg _ (hZV (hSZ w hw))).comp (hΨbij w hw.1).1
  have hΦinj : InjOn Φ S := by
    intro a ha b hb hab
    exact hΨinj ha.1 hb.1 (hψinj (hZV (hSZ a ha)) (hZV (hSZ b hb)) hab)
  -- `F ∘ Ψ` is the first coordinate near every `w ∈ B`, so `DF(Ψ(w))(DΨ(w)e) = e(0)`
  have hDFΨ : ∀ w ∈ B, ∀ e : Euclid (n + 1), fderiv ℝ F (Ψ w) (fderiv ℝ Ψ w e) = e 0 := by
    intro w hw e
    have h1 : fderiv ℝ (F ∘ Ψ) w =
        fderiv ℝ (EuclideanSpace.proj (0 : Fin (n + 1)) : Euclid (n + 1) → ℝ) w := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hB.mem_nhds hw] with v hv
      simp [hFΨ v hv]
    have h2 : fderiv ℝ (F ∘ Ψ) w = (fderiv ℝ F (Ψ w)).comp (fderiv ℝ Ψ w) :=
      fderiv_comp w ((hF.differentiable one_ne_zero) _) (hΨd w hw)
    rw [h2, ContinuousLinearMap.fderiv] at h1
    have := congrArg (fun L : Euclid (n + 1) →L[ℝ] ℝ => L e) h1
    simpa using this
  -- the hypotheses on `G` transported to the parametrization `Φ`
  have hGΦ : ∀ w ∈ S, G (Φ w) ∈ LinearMap.range (fderiv ℝ Φ w : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧
      ∀ e : Euclid (n + 1), inner ℝ (G (Φ w)) (fderiv ℝ Φ w e) = e 0 := by
    intro w hw
    obtain ⟨⟨v, hv⟩, hinner⟩ := hG (Ψ w) (hSZ w hw)
    refine ⟨?_, ?_⟩
    · -- `G(Φ(w)) = Dψ(Ψ(w))v` and `v = DΨ(w)u` since `DΨ(w)` is surjective
      obtain ⟨u, hu⟩ := (hΨbij w hw.1).2 v
      refine ⟨u, ?_⟩
      have hv' : fderiv ℝ ψ (Ψ w) v = G (ψ (Ψ w)) := hv
      change fderiv ℝ Φ w u = G (Φ w)
      rw [hΦD w hw, ContinuousLinearMap.comp_apply, hu, hv']
      rfl
    · intro e
      rw [hΦD w hw, ContinuousLinearMap.comp_apply]
      change inner ℝ (G (ψ (Ψ w))) _ = _
      rw [hinner, hDFΨ w hw.1 e]
  -- the patch co-area formula for `(Φ, S)`
  obtain ⟨hmeas, heq⟩ :=
    Submission.dor_lmbsf_pc_param_coarea P n Φ S G hSm hΦd hΦinjD hΦinj hGΦ φ hφ
  -- back to the chart: `Φ(S) = ψ(Z)` and `Φ(S ∩ {w(0) = t}) = ψ(Z ∩ F⁻¹(t))`
  have himg : Φ '' S = ψ '' Z := by
    rw [hΦdef, image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
    · intro hy
      obtain ⟨w, hw, rfl⟩ := hZB hy
      exact ⟨w, ⟨hw, hy⟩, rfl⟩
  have himgt : ∀ t : ℝ, Φ '' (S ∩ {w | w 0 = t}) = ψ '' (Z ∩ F ⁻¹' {t}) := by
    intro t
    rw [hΦdef, image_comp]
    congr 1
    ext y
    constructor
    · rintro ⟨w, ⟨⟨hwB, hwZ⟩, hwt⟩, rfl⟩
      refine ⟨hwZ, ?_⟩
      simp only [mem_preimage, mem_singleton_iff, hFΨ w hwB]
      exact hwt
    · rintro ⟨hy, hFy⟩
      obtain ⟨w, hw, rfl⟩ := hZB hy
      refine ⟨w, ⟨⟨hw, hy⟩, ?_⟩, rfl⟩
      simp only [mem_preimage, mem_singleton_iff, hFΨ w hw] at hFy
      exact hFy
  simp only [himgt] at hmeas heq
  rw [himg] at heq
  exact ⟨hmeas, heq⟩
/-- **Gluing countably many co-area pieces** (countable additivity of `∫⁻`).  Let `ψ` be continuous
and injective on `Z = ⋃_q Z_q`, the `Z_q` pairwise disjoint Borel sets, and `F` Borel.  Images
under `ψ` of Borel subsets of `Z` are Borel (Lusin–Souslin) and images of disjoint subsets of `Z`
are disjoint, so `ψ(Z ∩ F⁻¹{t}) = ⋃_q ψ(Z_q ∩ F⁻¹{t})` and `ψ(Z) = ⋃_q ψ(Z_q)` are countable
disjoint Borel unions.  Hence `∫_{ψ(Z ∩ F⁻¹{t})} φ dHⁿ = Σ_q ∫_{ψ(Z_q ∩ F⁻¹{t})} φ dHⁿ`, a countable
sum of a.e.-measurable functions of `t`, and exchanging `∫ dt` with `Σ_q` turns the co-area
identities of the pieces into `∫_ℝ ∫_{ψ(Z ∩ F⁻¹{t})} φ dHⁿ dt = Σ_q ∫_{ψ(Z_q)} g dH^{n+1}
= ∫_{ψ(Z)} g dH^{n+1}`. -/
theorem Submission.dor_lmbsf_pc_coarea_glue : ∀ (P n : ℕ) (Z : Set (Euclid (n + 1))) (Zs : ℕ → Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (φ g : Euclid P → ℝ≥0∞), ContinuousOn ψ Z → InjOn ψ Z → Measurable F → (∀ q, MeasurableSet (Zs q)) → Pairwise (fun p q => Disjoint (Zs p) (Zs q)) → (⋃ q, Zs q) = Z → (∀ q, AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Zs q, g x ∂μHE[n + 1]) → AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧ ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n]) = ∫⁻ x in ψ '' Z, g x ∂μHE[n + 1] := by
  intro P n Z Zs ψ F φ g hψc hψinj hF hZsm hZsd hZsU hq
  have hZsZ : ∀ q, Zs q ⊆ Z := fun q => hZsU ▸ subset_iUnion Zs q
  -- images of Borel subsets of `Z` are Borel (Lusin–Souslin)
  have himgm : ∀ A : Set (Euclid (n + 1)), MeasurableSet A → A ⊆ Z → MeasurableSet (ψ '' A) :=
    fun A hA hAZ => hA.image_of_continuousOn_injOn (hψc.mono hAZ) (hψinj.mono hAZ)
  -- images of disjoint subsets of `Z` are disjoint (`ψ` is injective on `Z`)
  have himgd : ∀ A A' : Set (Euclid (n + 1)), A ⊆ Z → A' ⊆ Z → Disjoint A A' →
      Disjoint (ψ '' A) (ψ '' A') := by
    intro A A' hA hA' hd
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have := hψinj (hA' hb) (hA ha) hab
    exact Set.disjoint_left.mp hd ha (this ▸ hb)
  -- each slice integral is the sum of the slice integrals of the pieces
  have hslice : ∀ t : ℝ, ∫⁻ x in ψ '' (Z ∩ F ⁻¹' {t}), φ x ∂μHE[n] =
      ∑' q, ∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n] := by
    intro t
    have hU : ψ '' (Z ∩ F ⁻¹' {t}) = ⋃ q, ψ '' (Zs q ∩ F ⁻¹' {t}) := by
      rw [← image_iUnion, ← iUnion_inter, hZsU]
    rw [hU, lintegral_iUnion
      (fun q => himgm _ ((hZsm q).inter (hF (measurableSet_singleton t)))
        (inter_subset_left.trans (hZsZ q)))
      (fun p q hpq => himgd _ _ (inter_subset_left.trans (hZsZ p))
        (inter_subset_left.trans (hZsZ q)) ((hZsd hpq).mono inter_subset_left inter_subset_left))]
  -- likewise for the right-hand side
  have hrhs : ∫⁻ x in ψ '' Z, g x ∂μHE[n + 1] = ∑' q, ∫⁻ x in ψ '' Zs q, g x ∂μHE[n + 1] := by
    have hU : ψ '' Z = ⋃ q, ψ '' Zs q := by rw [← image_iUnion, hZsU]
    rw [hU]
    exact lintegral_iUnion (fun q => himgm _ (hZsm q) (hZsZ q))
      (fun p q hpq => himgd _ _ (hZsZ p) (hZsZ q) (hZsd hpq)) g
  simp only [hslice]
  refine ⟨AEMeasurable.tsum (fun q => (hq q).1), ?_⟩
  rw [lintegral_tsum (fun q => (hq q).1), hrhs]
  exact tsum_congr (fun q => (hq q).2)

/-- **Co-area formula on one `C¹` chart piece** (Simon Ch. 3, 2.8–2.9; Ch. 2, 3.5).  Let `ψ` be a
`C¹` injective immersion of the open `V ⊆ ℝⁿ⁺¹` into `ℝᴾ`, `Y ⊆ C ⊆ V` Borel, `F` a `C¹` function
with `f ∘ ψ = F` on `Y`, and `G` the tangential gradient of `f` along `ψ(Y)`.  On `Y`, `G(ψ(y)) = 0`
iff `DF(y) = 0` (write `G(ψ(y)) = Dψ(y)v`, so `|G(ψ(y))|² = DF(y)v`), hence for `Y' = Y ∩ {DF ≠ 0}`
every slice is `ψ(Y) ∩ {G ≠ 0} ∩ f⁻¹{t} = ψ(Y' ∩ F⁻¹{t})`, and `ψ(Y ∖ Y')` contributes nothing to
`∫_{ψ(Y)} |G| φ dHⁿ⁺¹`.  The straightening charts `Ψ_q(B_q)` cover `{DF ≠ 0}`; the Borel pieces
`Z_q = Y' ∩ disjointed (Ψ_q(B_q)) q` are pairwise disjoint with union `Y'`, each satisfies the
co-area identity on its chart, and gluing the pieces gives the identity on `Y'`. -/
theorem Submission.dor_lmbsf_piece_coarea : ∀ (P n : ℕ) (V C Y : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → ContDiff ℝ 1 F → (∀ y ∈ Y, f (ψ y) = F y) → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → Measurable G → ∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in ψ '' Y, ‖G x‖ₑ * φ x ∂μHE[n + 1] := by
  intro P n V C Y ψ F f G hV hψ hψinj hDψ _ hCV hY hYC hF hfF hG _ φ hφ
  have hYV : Y ⊆ V := hYC.trans hCV
  -- on `Y`, the tangential gradient vanishes exactly where `DF` does
  have hG0 : ∀ y ∈ Y, G (ψ y) = 0 ↔ fderiv ℝ F y = 0 := by
    intro y hy
    obtain ⟨⟨v, hv⟩, he⟩ := hG y hy
    constructor
    · intro h0
      refine ContinuousLinearMap.ext fun e => ?_
      rw [← he e, h0, inner_zero_left, zero_apply]
    · intro h0
      have hvv : inner ℝ (G (ψ y)) (G (ψ y)) = fderiv ℝ F y v := by
        rw [← he v]
        exact congrArg (inner ℝ (G (ψ y))) hv.symm
      rw [h0, zero_apply] at hvv
      exact inner_self_eq_zero.mp hvv
  -- the regular part `Y' = Y ∩ {DF ≠ 0}` is Borel
  obtain ⟨Y', hY'⟩ : ∃ Y' : Set (Euclid (n + 1)), Y' = Y ∩ {y | fderiv ℝ F y ≠ 0} := ⟨_, rfl⟩
  have hY'Y : Y' ⊆ Y := hY' ▸ inter_subset_left
  have hY'V : Y' ⊆ V := hY'Y.trans hYV
  have hY'm : MeasurableSet Y' := hY' ▸
    hY.inter (isOpen_ne_fun (hF.continuous_fderiv one_ne_zero) continuous_const).measurableSet
  have hmemY' : ∀ y ∈ Y, (y ∈ Y' ↔ fderiv ℝ F y ≠ 0) := fun y hy => by
    rw [hY']
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  -- every slice is the image of a slice of the regular part
  have hslice : ∀ t : ℝ, ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t} = ψ '' (Y' ∩ F ⁻¹' {t}) := by
    intro t
    ext x
    simp only [mem_inter_iff, mem_image, mem_ofPred_eq, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨⟨⟨y, hy, rfl⟩, hGx⟩, hft⟩
      exact ⟨y, ⟨(hmemY' y hy).mpr fun h => hGx ((hG0 y hy).mpr h), (hfF y hy).symm.trans hft⟩,
        rfl⟩
    · rintro ⟨y, ⟨hy, hFt⟩, rfl⟩
      exact ⟨⟨⟨y, hY'Y hy, rfl⟩, fun h => (hmemY' y (hY'Y hy)).mp hy ((hG0 y (hY'Y hy)).mp h)⟩,
        (hfF y (hY'Y hy)).trans hFt⟩
  -- the critical part `ψ(Y ∖ Y')` carries no `|G| φ`-mass
  have hrhs : ∫⁻ x in ψ '' Y, ‖G x‖ₑ * φ x ∂μHE[n + 1] =
      ∫⁻ x in ψ '' Y', ‖G x‖ₑ * φ x ∂μHE[n + 1] := by
    have hcrit : MeasurableSet (ψ '' (Y \ Y')) :=
      (hY.diff hY'm).image_of_continuousOn_injOn (hψ.continuousOn.mono (sdiff_subset.trans hYV))
        (hψinj.mono (sdiff_subset.trans hYV))
    have hdisj : Disjoint (ψ '' Y') (ψ '' (Y \ Y')) := by
      rw [Set.disjoint_left]
      rintro x ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
      have := hψinj (hYV hb.1) (hY'V ha) hab
      exact hb.2 (this ▸ ha)
    have hzero : ∫⁻ x in ψ '' (Y \ Y'), ‖G x‖ₑ * φ x ∂μHE[n + 1] = 0 := by
      refine setLIntegral_eq_zero₀ hcrit.nullMeasurableSet ?_
      rintro x ⟨y, ⟨hy, hy'⟩, rfl⟩
      have hDF : fderiv ℝ F y = 0 := not_not.mp fun h => hy' ((hmemY' y hy).mpr h)
      simp [(hG0 y hy).mpr hDF]
    rw [← union_sdiff_cancel hY'Y, image_union, lintegral_union hcrit hdisj, hzero, add_zero]
  -- countably many straightening charts cover `{DF ≠ 0}`; cut `Y'` into disjoint Borel pieces
  obtain ⟨B, Ψ, hBo, hΨc, hΨinj, hΨbij, hFΨ, hΨo, hcover⟩ :=
    Submission.dor_lmbsf_pc_straightening_cover n F hF
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ℕ → Set (Euclid (n + 1)),
      ∀ q, Zs q = Y' ∩ disjointed (fun q => Ψ q '' B q) q := ⟨_, fun _ => rfl⟩
  have hZsm : ∀ q, MeasurableSet (Zs q) := fun q => by
    rw [hZs]
    exact hY'm.inter (MeasurableSet.disjointed (fun p => (hΨo p).measurableSet) q)
  have hZsd : Pairwise (fun p q => Disjoint (Zs p) (Zs q)) := by
    intro p q hpq
    rw [hZs, hZs]
    exact Disjoint.mono inter_subset_right inter_subset_right (disjoint_disjointed _ hpq)
  have hZsU : (⋃ q, Zs q) = Y' := by
    simp only [hZs]
    rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
    intro y hy
    exact hcover ((hmemY' y (hY'Y hy)).mp hy)
  have hZsY' : ∀ q, Zs q ⊆ Y' := fun q => by
    rw [hZs]
    exact inter_subset_left
  have hZsΨ : ∀ q, Zs q ⊆ Ψ q '' B q := fun q => by
    rw [hZs]
    exact inter_subset_right.trans (disjointed_subset _ q)
  -- the co-area identity on each chart piece
  have hpatch : ∀ q, AEMeasurable (fun t : ℝ => ∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) ∧
      ∫⁻ t : ℝ, (∫⁻ x in ψ '' (Zs q ∩ F ⁻¹' {t}), φ x ∂μHE[n]) =
        ∫⁻ x in ψ '' Zs q, ‖G x‖ₑ * φ x ∂μHE[n + 1] := fun q =>
    Submission.dor_lmbsf_pc_chart_patch_coarea P n V (B q) (Zs q) ψ F (Ψ q) G hV hψ hψinj hDψ hF
      (hBo q) (hΨc q) (hΨinj q) (hΨbij q) (hFΨ q) (hZsm q) ((hZsY' q).trans hY'V) (hZsΨ q)
      (fun y hy => hG y (hY'Y (hZsY' q hy))) φ hφ
  -- glue the pieces
  have hglue := Submission.dor_lmbsf_pc_coarea_glue P n Y' Zs ψ F φ (fun x => ‖G x‖ₑ * φ x)
    (hψ.continuousOn.mono hY'V) (hψinj.mono hY'V) hF.continuous.measurable hZsm hZsd hZsU hpatch
  simp only [hslice, hrhs]
  exact hglue

/-- **Slice tangent-plane algebra** (Simon Ch. 6, Lemma 4.1 (2): `∇ᴹf(x) ∈ TₓM` and `TₓMₜ` is
the orthogonal complement of `∇ᴹf(x)` in `TₓM`).  Let `L : ℝᵐ → ℝᴾ` and `ℓ : ℝᵐ → ℝ` be linear,
`g ∈ L(ℝᵐ)` and `⟨g, L e⟩ = ℓ(e)` for every `e`.  Then `g = 0 ⇔ ℓ = 0` (if `ℓ = 0` and
`g = L w`, then `|g|² = ⟨g, L w⟩ = ℓ(w) = 0`), and `L(ℝᵐ) ∩ g^⊥ = L(ker ℓ)`, because `v = L e`
is orthogonal to `g` iff `ℓ(e) = ⟨g, L e⟩ = 0`. -/
theorem Submission.dor_lmbsf_pst_slice_plane_algebra : ∀ (m P : ℕ) (L : Euclid m →L[ℝ] Euclid P) (ℓ : Euclid m →L[ℝ] ℝ) (g : Euclid P), g ∈ LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P) → (∀ e : Euclid m, inner ℝ g (L e) = ℓ e) → (g = 0 ↔ ℓ = 0) ∧ LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ g)ᗮ = Submodule.map (L : Euclid m →ₗ[ℝ] Euclid P) (LinearMap.ker (ℓ : Euclid m →ₗ[ℝ] ℝ)) := by
  intro m P L ℓ g hg hgℓ
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · -- Step 1, `g = 0` gives `ℓ(e) = ⟨0, L e⟩ = 0` for every `e`
    ext e
    rw [← hgℓ e, h, inner_zero_left, zero_apply]
  · -- Step 2, `g = L w` and `ℓ = 0` give `⟨g, g⟩ = ⟨g, L w⟩ = ℓ(w) = 0`
    obtain ⟨w, hw⟩ := LinearMap.mem_range.1 hg
    have hgg := hgℓ w
    rw [ContinuousLinearMap.coe_coe] at hw
    rw [hw, h, zero_apply] at hgg
    exact inner_self_eq_zero.1 hgg
  · -- Steps 3–5, `v = L e` lies in `gᗮ` iff `ℓ(e) = ⟨g, L e⟩ = 0`
    ext v
    simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker,
      Submodule.mem_orthogonal_singleton_iff_inner_right, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨⟨e, rfl⟩, he⟩
      exact ⟨e, (hgℓ e).symm.trans he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨⟨e, rfl⟩, (hgℓ e).trans he⟩
/-- **Local `C¹` chart of a regular level set** (the implicit function theorem step of Simon
Ch. 2, §6, after 6.3, chapter-02.txt lines 1476–1482: off `{DF = 0}` a level set of a `C¹` map is
a `C¹` submanifold).  `ℓ = DF(y₀) ≠ 0` has `dim ker ℓ = n`; extending an isomorphism
`ker ℓ ≅ ℝⁿ` gives a linear `π` with `π × ℓ` invertible.  Invert `Θ = (π, F)` near `y₀` (inverse
function theorem) inside `W` and the open set where `DΘ` is invertible.  Then
`Λ(z) = Θ⁻¹(z, F(y₀))` on `D = {z | (z, F(y₀)) ∈ target}` has `π ∘ Λ = id`, `F ∘ Λ = F(y₀)` and
`DΛ(z) = DΘ(Λ z)⁻¹ ∘ inl`, injective with range `ker DF(Λ z)`.  For `c = π(y₀)`, `B̄_ρ(c) ⊆ D`
and `N = source ∩ π⁻¹(B_ρ(c))`, a point `y ∈ N` with `F(y) = F(y₀)` is `Λ(π y)`. -/
theorem Submission.dor_lmbsf_pst_level_set_local_chart : ∀ (n : ℕ) (W : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (y₀ : Euclid (n + 1)), IsOpen W → ContDiff ℝ 1 F → y₀ ∈ W → fderiv ℝ F y₀ ≠ 0 → ∃ (D : Set (Euclid n)) (Λ : Euclid n → Euclid (n + 1)) (c : Euclid n) (ρ : ℝ) (N : Set (Euclid (n + 1))), IsOpen D ∧ ContDiffOn ℝ 1 Λ D ∧ InjOn Λ D ∧ (∀ z ∈ D, Λ z ∈ W ∧ F (Λ z) = F y₀ ∧ Injective (fderiv ℝ Λ z) ∧ LinearMap.range (fderiv ℝ Λ z : Euclid n →ₗ[ℝ] Euclid (n + 1)) = LinearMap.ker (fderiv ℝ F (Λ z) : Euclid (n + 1) →ₗ[ℝ] ℝ)) ∧ closedBall c ρ ⊆ D ∧ IsOpen N ∧ y₀ ∈ N ∧ N ∩ F ⁻¹' {F y₀} ⊆ Λ '' ball c ρ := by
  intro n W F y₀ hW hF hy₀ hDF
  set ℓ : Euclid (n + 1) →L[ℝ] ℝ := fderiv ℝ F y₀
  set t : ℝ := F y₀
  set K := LinearMap.ker (ℓ : Euclid (n + 1) →ₗ[ℝ] ℝ)
  -- Step 1, `ℓ ≠ 0` is onto `ℝ`, so `dim K = n` by rank–nullity
  have hdimK : Module.finrank ℝ K = Module.finrank ℝ (Euclid n) := by
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, ℓ v₀ ≠ 0 := by
      by_contra! h
      exact hDF (ContinuousLinearMap.ext h)
    have hrange : LinearMap.range (ℓ : Euclid (n + 1) →ₗ[ℝ] ℝ) = ⊤ :=
      eq_top_iff.2 fun r _ => LinearMap.mem_range.2 ⟨(r / ℓ v₀) • v₀, by simp [hv₀]⟩
    have h : _ + Module.finrank ℝ K = _ :=
      LinearMap.finrank_range_add_finrank_ker (ℓ : Euclid (n + 1) →ₗ[ℝ] ℝ)
    rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
    rw [finrank_euclideanSpace_fin]
    omega
  -- Step 2, `π` extends an isomorphism `e : K ≃ ℝⁿ`, so `ℓ v = 0 = π v` forces `v = 0`
  obtain ⟨π, hπ⟩ : ∃ π : Euclid (n + 1) →L[ℝ] Euclid n, ∀ v, ℓ v = 0 → π v = 0 → v = 0 := by
    let e : K ≃ₗ[ℝ] Euclid n := LinearEquiv.ofFinrankEq _ _ hdimK
    obtain ⟨g, hg⟩ := LinearMap.exists_extend (e : K →ₗ[ℝ] Euclid n)
    refine ⟨LinearMap.toContinuousLinearMap g, fun v hv hπv => ?_⟩
    have hvK : v ∈ K := hv
    have h : e ⟨v, hvK⟩ = 0 := by
      have hgv := congrArg (fun f => f ⟨v, hvK⟩) hg
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe] at hgv
      rw [← hgv]
      exact hπv
    exact congrArg Subtype.val (e.injective (h.trans (map_zero e).symm))
  -- Step 3, `Θ = (π, F)` is `C¹` with `DΘ(y) = π × DF(y)`
  set Θ : Euclid (n + 1) → Euclid n × ℝ := fun y => (π y, F y)
  have hΘ : ContDiff ℝ 1 Θ := π.contDiff.prodMk hF
  have hΘd : ∀ y, HasFDerivAt Θ (π.prod (fderiv ℝ F y)) y := fun y =>
    π.hasFDerivAt.prodMk (hF.differentiable one_ne_zero y).hasFDerivAt
  -- Step 4, `π × ℓ` is injective by Step 2, hence (equal dimensions) an isomorphism `E₀`
  have hker₀ : LinearMap.ker (π.prod ℓ : Euclid (n + 1) →ₗ[ℝ] Euclid n × ℝ) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    have h : (π v, ℓ v) = ((0 : Euclid n), (0 : ℝ)) := hv
    exact hπ v (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hrange₀ : LinearMap.range (π.prod ℓ : Euclid (n + 1) →ₗ[ℝ] Euclid n × ℝ) = ⊤ := by
    have hdim : Module.finrank ℝ (Euclid (n + 1)) = Module.finrank ℝ (Euclid n × ℝ) := by
      rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
        finrank_euclideanSpace_fin]
    exact LinearMap.range_eq_top.2
      ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1
        (LinearMap.ker_eq_bot.1 hker₀))
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Euclid (n + 1) ≃L[ℝ] Euclid n × ℝ,
      (E₀ : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) = π.prod ℓ :=
    ⟨ContinuousLinearEquiv.ofBijective _ hker₀ hrange₀,
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  have hΘE₀ : HasFDerivAt Θ (E₀ : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) y₀ := by
    rw [hE₀]
    exact hΘd y₀
  -- the set `O` where `DΘ` is invertible is open (`DΘ` is continuous) and contains `y₀`
  set O : Set (Euclid (n + 1)) :=
    fderiv ℝ Θ ⁻¹' range ContinuousLinearEquiv.toContinuousLinearMap
  have hO : IsOpen O :=
    ContinuousLinearEquiv.isOpen.preimage (hΘ.continuous_fderiv one_ne_zero)
  have hy₀O : y₀ ∈ O := ⟨E₀, hΘE₀.fderiv.symm⟩
  -- Step 5, the inverse function theorem for `Θ` at `y₀`, restricted to `O ∩ W`
  have hΘs : HasStrictFDerivAt Θ (E₀ : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) y₀ :=
    hΘ.contDiffAt.hasStrictFDerivAt' hΘE₀ one_ne_zero
  obtain ⟨Φ, hΦ, hΦsrc, hy₀Φ⟩ : ∃ Φ : OpenPartialHomeomorph (Euclid (n + 1)) (Euclid n × ℝ),
      (Φ : Euclid (n + 1) → Euclid n × ℝ) = Θ ∧ Φ.source ⊆ O ∩ W ∧ y₀ ∈ Φ.source :=
    ⟨(hΘs.toOpenPartialHomeomorph Θ).restrOpen (O ∩ W) (hO.inter hW), rfl, inter_subset_right,
      ⟨hΘs.mem_toOpenPartialHomeomorph_source, hy₀O, hy₀⟩⟩
  -- Step 6, the chart `Λ(z) = Φ⁻¹(z, t)` on the open set `D = {z | (z, t) ∈ target Φ}`
  set D : Set (Euclid n) := (fun z => (z, t)) ⁻¹' Φ.target
  set Λ : Euclid n → Euclid (n + 1) := fun z => Φ.symm (z, t)
  have hD : IsOpen D := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
  -- Step 7, for `z ∈ D`, `Λ(z) ∈ source Φ ⊆ O ∩ W` and `Θ(Λ z) = (z, t)`
  have hΛsrc : ∀ z ∈ D, Λ z ∈ Φ.source := fun z hz => Φ.map_target hz
  have hΘΛ : ∀ z ∈ D, Θ (Λ z) = (z, t) := fun z hz => by
    rw [← hΦ]
    exact Φ.right_inv hz
  have hπΛ : ∀ z ∈ D, π (Λ z) = z := fun z hz => congrArg Prod.fst (hΘΛ z hz)
  have hFΛ : ∀ z ∈ D, F (Λ z) = t := fun z hz => congrArg Prod.snd (hΘΛ z hz)
  -- Step 9, `Λ` is `C¹` at `z ∈ D` with `DΛ(z) = E⁻¹ ∘ inl`, `E = DΘ(Λ z) = π × DF(Λ z)`
  have hΛd : ∀ z ∈ D, ∃ E : Euclid (n + 1) ≃L[ℝ] Euclid n × ℝ,
      (E : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) = π.prod (fderiv ℝ F (Λ z)) ∧
      HasFDerivAt Λ ((E.symm : Euclid n × ℝ →L[ℝ] Euclid (n + 1)).comp
        (ContinuousLinearMap.inl ℝ (Euclid n) ℝ)) z ∧ ContDiffAt ℝ 1 Λ z := by
    intro z hz
    obtain ⟨E, hE⟩ := (hΦsrc (hΛsrc z hz)).1
    have hEΘ : (E : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) = π.prod (fderiv ℝ F (Λ z)) := by
      rw [← (hΘd (Λ z)).fderiv]
      exact hE
    have hΦE : HasFDerivAt Φ (E : Euclid (n + 1) →L[ℝ] Euclid n × ℝ) (Φ.symm (z, t)) := by
      rw [hΦ, hEΘ]
      exact hΘd _
    have hΦC : ContDiffAt ℝ 1 Φ (Φ.symm (z, t)) := by
      rw [hΦ]
      exact hΘ.contDiffAt
    exact ⟨E, hEΘ, (Φ.hasFDerivAt_symm hz hΦE).comp z (hasFDerivAt_prodMk_left z t),
      (Φ.contDiffAt_symm hz hΦE hΦC).comp z (contDiffAt_id.prodMk contDiffAt_const)⟩
  -- Step 12, `c = π(y₀) ∈ D` since `(c, t) = Θ(y₀)`; `B̄_ρ(c) ⊆ B_ε(c) ⊆ D` for `ρ = ε/2`
  have hcD : π y₀ ∈ D := by
    show (π y₀, t) ∈ Φ.target
    have h := Φ.map_source hy₀Φ
    rw [hΦ] at h
    exact h
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD (π y₀) hcD
  -- Step 13, `N = source Φ ∩ π⁻¹(B_ρ(c))`
  refine ⟨D, Λ, π y₀, ε / 2, Φ.source ∩ π ⁻¹' ball (π y₀) (ε / 2), hD, fun z hz => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨E, -, -, hΛC⟩ := hΛd z hz
    exact hΛC.contDiffWithinAt
  · -- Step 8, `π ∘ Λ = id` on `D`
    intro z hz z' hz' h
    rw [← hπΛ z hz, ← hπΛ z' hz', h]
  · intro z hz
    obtain ⟨E, hEΘ, hΛE, -⟩ := hΛd z hz
    have hEv : ∀ v, E v = (π v, fderiv ℝ F (Λ z) v) := fun v => by
      rw [← ContinuousLinearEquiv.coe_coe, hEΘ]
      rfl
    refine ⟨(hΦsrc (hΛsrc z hz)).2, hFΛ z hz, ?_, ?_⟩
    · -- Step 10, `E⁻¹ ∘ inl` is injective
      rw [hΛE.fderiv]
      intro w w' h
      have h' : ((w, 0) : Euclid n × ℝ) = (w', 0) := E.symm.injective h
      exact congrArg Prod.fst h'
    · -- Step 11, `E v = (π v, DF(Λ z) v)`: `E⁻¹(w, 0) ∈ ker DF(Λ z)`, and `v = E⁻¹(π v, 0)`
      -- if `DF(Λ z) v = 0`
      rw [hΛE.fderiv]
      ext v
      rw [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨w, rfl⟩
        have h := hEv (E.symm (w, 0))
        rw [ContinuousLinearEquiv.apply_symm_apply] at h
        exact (congrArg Prod.snd h).symm
      · intro hv
        refine ⟨π v, E.injective ?_⟩
        change E (E.symm (π v, 0)) = E v
        rw [ContinuousLinearMap.coe_coe] at hv
        rw [ContinuousLinearEquiv.apply_symm_apply, hEv, hv]
  · exact (closedBall_subset_ball (half_lt_self hε)).trans hεD
  · exact Φ.open_source.inter (isOpen_ball.preimage π.continuous)
  · exact ⟨hy₀Φ, mem_ball_self (half_pos hε)⟩
  · -- `y ∈ N` with `F y = t` has `Φ(y) = (π y, t)`, so `Λ(π y) = Φ⁻¹(Φ y) = y`
    rintro y ⟨⟨hyΦ, hyB⟩, hyF⟩
    refine ⟨π y, hyB, ?_⟩
    have hyF' : F y = t := hyF
    have h := Φ.left_inv hyΦ
    rw [hΦ] at h
    show Φ.symm (π y, t) = y
    rw [← hyF']
    exact h

/-- **Countable chart cover of a regular level set** (Simon Ch. 2, before 6.4: "the implicit
function theorem implies that either `f⁻¹(y) ∖ C` is empty or else it is a `k`-dimensional `C¹`
submanifold", chapter-02.txt lines 1479–1496; used for the slice tangent planes of Ch. 6,
Lemma 4.1(2)).  Let `W ⊆ ℝ^{n+1}` be open, `F` be `C¹` and `t ∈ ℝ`.  There are countably many
`C¹` maps `Λ_k`, injective on open sets `D_k ⊇ B̄_{ρ_k}(c_k)` and with values in `W ∩ {F = t}`,
such that `DΛ_k(z)` is injective with range `ker DF(Λ_k z)` and every `y ∈ W` with `DF(y) ≠ 0`,
`F(y) = t` is `Λ_k(z)` for some `k` and `z ∈ B_{ρ_k}(c_k)`.  Take the local chart
(`dor_lmbsf_pst_level_set_local_chart`) at each such `y`, with neighbourhood `N_y`, and a
countable subfamily of the open sets `N_y` with the same union (second countability); if there
is no such `y`, take empty charts with `ρ_k = -1`. -/
theorem Submission.dor_lmbsf_pst_level_set_chart_cover : ∀ (n : ℕ) (W : Set (Euclid (n + 1))) (F : Euclid (n + 1) → ℝ) (t : ℝ), IsOpen W → ContDiff ℝ 1 F → ∃ (D : ℕ → Set (Euclid n)) (Λ : ℕ → Euclid n → Euclid (n + 1)) (c : ℕ → Euclid n) (ρ : ℕ → ℝ), (∀ k, IsOpen (D k)) ∧ (∀ k, ContDiffOn ℝ 1 (Λ k) (D k)) ∧ (∀ k, InjOn (Λ k) (D k)) ∧ (∀ k, ∀ z ∈ D k, Λ k z ∈ W ∧ F (Λ k z) = t ∧ Injective (fderiv ℝ (Λ k) z) ∧ LinearMap.range (fderiv ℝ (Λ k) z : Euclid n →ₗ[ℝ] Euclid (n + 1)) = LinearMap.ker (fderiv ℝ F (Λ k z) : Euclid (n + 1) →ₗ[ℝ] ℝ)) ∧ (∀ k, closedBall (c k) (ρ k) ⊆ D k) ∧ ∀ y ∈ W, fderiv ℝ F y ≠ 0 → F y = t → ∃ k, ∃ z ∈ ball (c k) (ρ k), Λ k z = y := by
  intro n W F t hW hF
  by_cases hne : ∃ y, y ∈ W ∧ fderiv ℝ F y ≠ 0 ∧ F y = t
  swap
  · -- Step 1, no regular point of `{F = t}` in `W`: empty charts, `B̄_{-1}(0) = ∅`
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => 0, fun _ => -1, fun _ => isOpen_empty,
      fun _ => contDiffOn_empty, fun _ => injOn_empty _,
      fun _ z hz => (Set.notMem_empty z hz).elim,
      fun _ => (closedBall_eq_empty.2 (by norm_num)).subset, fun y hyW hdF hFy => ?_⟩
    exact (hne ⟨y, hyW, hdF, hFy⟩).elim
  obtain ⟨y₀, hy₀⟩ := hne
  -- Step 2, a local chart `(D y, Λ y, c y, ρ y)` with neighbourhood `N y` at each regular point `y`
  choose D Λ c ρ N hD hΛ hinj hprop hcb hNo hyN hcov using
    fun y : {y // y ∈ W ∧ fderiv ℝ F y ≠ 0 ∧ F y = t} =>
      Submission.dor_lmbsf_pst_level_set_local_chart n W F y hW hF y.2.1 y.2.2.1
  -- Step 3, the `N y` with `y` in a countable `T` have the same union; `T ≠ ∅` as `y₀` is regular
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable N hNo
  have hT : ∀ y : {y // y ∈ W ∧ fderiv ℝ F y ≠ 0 ∧ F y = t},
      ∃ i ∈ T, (y : Euclid (n + 1)) ∈ N i := by
    intro y
    have hy : (y : Euclid (n + 1)) ∈ ⋃ i ∈ T, N i := by
      rw [hTU]
      exact mem_iUnion.2 ⟨y, hyN y⟩
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
    exact ⟨i, hi, hyi⟩
  obtain ⟨i₀, hi₀, -⟩ := hT ⟨y₀, hy₀⟩
  obtain ⟨e, rfl⟩ := hTc.exists_eq_range ⟨i₀, hi₀⟩
  -- Step 4, the charts at the points `e k`, where `F (e k) = t`
  refine ⟨fun k => D (e k), fun k => Λ (e k), fun k => c (e k), fun k => ρ (e k),
    fun k => hD (e k), fun k => hΛ (e k), fun k => hinj (e k), fun k z hz => ?_,
    fun k => hcb (e k), fun y hyW hdF hFy => ?_⟩
  · obtain ⟨h₁, h₂, h₃, h₄⟩ := hprop (e k) z hz
    exact ⟨h₁, h₂.trans (e k).2.2.2, h₃, h₄⟩
  · -- Step 5, `y ∈ N (e k) ∩ F⁻¹(F (e k)) ⊆ Λ (e k) '' B_{ρ (e k)}(c (e k))` for some `k`
    obtain ⟨_, ⟨k, rfl⟩, hyk⟩ := hT ⟨y, hyW, hdF, hFy⟩
    obtain ⟨z, hz, hzy⟩ := hcov (e k) ⟨hyk, hFy.trans (e k).2.2.2.symm⟩
    exact ⟨k, z, hz, hzy⟩
/-- **Approximate tangent spaces of compact `C¹` patches pass to `S`** (Simon Ch. 3, 1.4; the
locality step (TL) applied patch by patch).  Assume (TL).  Let `S` be Borel with `Hⁿ(S) < ∞`, and
for each `k` let `χ_k` be `C¹` on the open `D_k ⊇ K_k = B̄_{ρ_k}(c_k)` and injective on `K_k`.  The
patch `Σ_k = χ_k(K_k)` is compact with `Hⁿ(Σ_k) < ∞` (Lipschitz image of a compact ball), and
`A_k = S ∩ χ_k(B_{ρ_k}(c_k))` is Borel (Lusin–Souslin) with `A_k ⊆ Σ_k` and `A_k ⊆ S`.  Two
applications of (TL) with `U = ℝᴾ` give, `Hⁿ`-a.e. on `A_k`, `Σ_k`-tangent `Q` ⇒ `A_k`-tangent `Q`
⇒ `S`-tangent `Q`; intersecting over the countably many `k` gives the claim `Hⁿ`-a.e. on `S`. -/
theorem Submission.dor_lmbsf_pst_patch_tangent_transfer : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (S : Set (Euclid P)) (D : ℕ → Set (Euclid n)) (χ : ℕ → Euclid n → Euclid P) (c : ℕ → Euclid n) (ρ : ℕ → ℝ), MeasurableSet S → μHE[n] S ≠ ∞ → (∀ k, IsOpen (D k)) → (∀ k, ContDiffOn ℝ 1 (χ k) (D k)) → (∀ k, closedBall (c k) (ρ k) ⊆ D k) → (∀ k, InjOn (χ k) (closedBall (c k) (ρ k))) → ∀ᵐ x ∂(μHE[n].restrict S), ∀ k, ∀ z ∈ ball (c k) (ρ k), χ k z = x → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n (χ k '' closedBall (c k) (ρ k)) x Q → HasApproximateTangentSpaceAt n S x Q := by
  intro TL P n S D χ c ρ hS hSfin hD hχ hKD hinj
  -- Steps 1–7, for each patch `k`: `Hⁿ⌞S`-a.e., if `x ∈ A_k = S ∩ χ_k(B_k)`, every approximate
  -- tangent space of `Σ_k = χ_k(K_k)` at `x` is one of `S`
  have hpatch : ∀ k, ∀ᵐ x ∂(μHE[n].restrict S), x ∈ S ∩ χ k '' ball (c k) (ρ k) →
      ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n (χ k '' closedBall (c k) (ρ k)) x Q →
          HasApproximateTangentSpaceAt n S x Q := by
    intro k
    -- Step 1, `Σ_k` is compact, hence Borel
    have hχK : ContinuousOn (χ k) (closedBall (c k) (ρ k)) :=
      ((hχ k).mono (hKD k)).continuousOn
    have hsig : MeasurableSet (χ k '' closedBall (c k) (ρ k)) :=
      ((isCompact_closedBall _ _).image_of_continuousOn hχK).isClosed.measurableSet
    -- Step 2, `χ_k` is `L`-Lipschitz on the convex compact `K_k`, so `Hⁿ(Σ_k) ≤ Lⁿ Hⁿ(K_k) < ∞`
    obtain ⟨L, hL⟩ := ((hχ k).mono (hKD k)).exists_lipschitzOnWith one_ne_zero
      (convex_closedBall _ _) (isCompact_closedBall _ _)
    have hsigfin : μHE[n] (χ k '' closedBall (c k) (ρ k)) ≠ ∞ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) ?_)
        (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hL)
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact (isCompact_closedBall _ _).measure_lt_top.ne
    -- Step 3, `A_k` is Borel (Lusin–Souslin for the injective continuous `χ_k` on `B_k`)
    have hA : MeasurableSet (S ∩ χ k '' ball (c k) (ρ k)) :=
      hS.inter (measurableSet_ball.image_of_continuousOn_injOn
        (hχK.mono ball_subset_closedBall) ((hinj k).mono ball_subset_closedBall))
    -- Steps 4–6, `A_k ⊆ Σ_k` and `A_k ⊆ S`, and (TL) applies to both pairs with `U = ℝᴾ`
    have h1 := TL P n univ _ _ isOpen_univ hA hsig
      (inter_subset_right.trans (image_mono ball_subset_closedBall)) (subset_univ _)
      fun K _ _ => ne_top_of_le_ne_top hsigfin (measure_mono inter_subset_left)
    have h2 := TL P n univ _ _ isOpen_univ hA hS inter_subset_left (subset_univ _)
      fun K _ _ => ne_top_of_le_ne_top hSfin (measure_mono inter_subset_left)
    -- Step 7, `Hⁿ⌞A_k`-a.e., `Σ_k`-tangent `Q` ⇒ `A_k`-tangent `Q` ⇒ `S`-tangent `Q`
    have h3 : ∀ᵐ x ∂(μHE[n].restrict (S ∩ χ k '' ball (c k) (ρ k))),
        ∀ Q : Submodule ℝ (Euclid P),
          HasApproximateTangentSpaceAt n (χ k '' closedBall (c k) (ρ k)) x Q →
            HasApproximateTangentSpaceAt n S x Q := by
      filter_upwards [h1, h2] with x hx1 hx2 Q hQ
      exact (hx2 Q).2 ((hx1 Q).1 hQ)
    exact ae_restrict_of_ae ((ae_restrict_iff' hA).1 h3)
  -- Steps 8–9, intersect over the countably many `k`; `x = χ_k(z)` with `z ∈ B_k` lies in `A_k`
  filter_upwards [ae_all_iff.2 hpatch, ae_restrict_mem hS] with x hx hxS k z hz hzx Q hQ
  exact hx k ⟨hxS, z, hz, hzx⟩ Q hQ
/-- **Slices of one `C¹` chart piece** (Simon Ch. 6, Lemma 4.1(1),(2) for one piece; Ch. 2, 6.4
and Remark 4.4; Ch. 3, Lemma 1.2 "if").  For `y ∈ Y`, `G(ψ(y)) ≠ 0 ⇔ DF(y) ≠ 0`, so
`S_t = ψ(Y ∩ Γ_t)` with `Γ_t = {DF ≠ 0} ∩ F⁻¹(t)`, a Borel set by Lusin–Souslin.  Countably many
`C¹` graph charts `Λ_k` cover `Γ_t ∩ V`, and `χ_k := ψ ∘ Λ_k` is `C¹` with `Dχ_k(z)` injective of
range `Dψ(y)(ker DF(y)) = Dψ(y)(ℝ^{n+1}) ∩ G(ψ(y))^⊥`, `y = Λ_k(z)`.  (i) `S_t ⊆ ⋃_k χ_k(D_k)`.
(ii) The compact patch `χ_k(B̄_{ρ_k}(c_k))` has approximate tangent space `Dχ_k(z)(ℝⁿ)` at
`χ_k(z)`, `z ∈ B_{ρ_k}(c_k)`, and (TL) transfers it to `S_t`, `Hⁿ`-a.e. on `S_t`. -/
theorem Submission.dor_lmbsf_piece_slice_approxTangent : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (V C Y : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (f : Euclid P → ℝ) (G : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → ContDiff ℝ 1 F → (∀ y ∈ Y, f (ψ y) = F y) → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → ∀ t : ℝ, CountablyRectifiable n (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) ∧ (μHE[n] (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) ≠ ∞ → ∀ᵐ x ∂(μHE[n].restrict (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t})), ∀ y ∈ Y, ψ y = x → HasApproximateTangentSpaceAt n (ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}) x (LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓ (ℝ ∙ G x)ᗮ)) := by
  intro hTL P n V C Y ψ F f G hV hψ hψinj hDψ hC hCV hY hYC hF hfF hG t
  have hYV : Y ⊆ V := hYC.trans hCV
  -- Step 1, for `y ∈ Y`: `G(ψ(y)) = 0 ⇔ DF(y) = 0`, and
  -- `Dψ(y)(ℝ^{n+1}) ∩ G(ψ(y))^⊥ = Dψ(y)(ker DF(y))`
  have halg := fun y (hy : y ∈ Y) => Submission.dor_lmbsf_pst_slice_plane_algebra (n + 1) P
    (fderiv ℝ ψ y) (fderiv ℝ F y) (G (ψ y)) (hG y hy).1 (hG y hy).2
  set S := ψ '' Y ∩ {x | G x ≠ 0} ∩ f ⁻¹' {t}
  have hlevel : ∀ y ∈ Y, ψ y ∈ S → fderiv ℝ F y ≠ 0 ∧ F y = t := by
    rintro y hy ⟨⟨-, hGy⟩, hfy⟩
    exact ⟨fun h => hGy ((halg y hy).1.2 h), (hfF y hy).symm.trans hfy⟩
  -- so `S_t = ψ(Y ∩ Γ_t)`
  have hSeq : S = ψ '' (Y ∩ {y | fderiv ℝ F y ≠ 0} ∩ F ⁻¹' {t}) := by
    refine Subset.antisymm (fun x hx => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := hx.1.1
      exact ⟨y, ⟨⟨hy, (hlevel y hy hx).1⟩, (hlevel y hy hx).2⟩, rfl⟩
    · rintro x ⟨y, ⟨⟨hy, hDF⟩, hFy⟩, rfl⟩
      exact ⟨⟨mem_image_of_mem ψ hy, fun h => hDF ((halg y hy).1.1 h)⟩, (hfF y hy).trans hFy⟩
  -- Step 2, countably many `C¹` graph charts `Λ_k : D_k → Γ_t ∩ V` with
  -- `Γ_t ∩ V = ⋃_k Λ_k(B_{ρ_k}(c_k))`; `χ_k := ψ ∘ Λ_k` is `C¹` on `D_k` and injective on
  -- `B̄_{ρ_k}(c_k)`
  obtain ⟨D, Λ, c, ρ, hDo, hΛ, hΛinj, hΛD, hball, hcover⟩ :=
    Submission.dor_lmbsf_pst_level_set_chart_cover n V F t hV hF
  have hΛV : ∀ k, MapsTo (Λ k) (D k) V := fun k z hz => (hΛD k z hz).1
  have hχ : ∀ k, ContDiffOn ℝ 1 (ψ ∘ Λ k) (D k) := fun k => hψ.comp (hΛ k) (hΛV k)
  have hχinj : ∀ k, InjOn (ψ ∘ Λ k) (closedBall (c k) (ρ k)) := fun k =>
    (hψinj.comp (hΛinj k) (hΛV k)).mono (hball k)
  have hchart : ∀ y ∈ Y, ψ y ∈ S → ∃ k, ∃ z ∈ ball (c k) (ρ k), Λ k z = y := fun y hy hyS =>
    hcover y (hYV hy) (hlevel y hy hyS).1 (hlevel y hy hyS).2
  refine ⟨?_, fun hfin => ?_⟩
  · -- Step 3, (i): `S_t ⊆ ⋃_k χ_k(D_k)`, a countable union of `C¹` images of open sets
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion (fun k => (ψ ∘ Λ k) '' D k)
      fun k => Poincare.SimonGMT.Chapter03.countablyRectifiable_image_contDiffOn_open (hDo k)
        (hχ k)).mono fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx.1.1
    obtain ⟨k, z, hz, rfl⟩ := hchart y hy hx
    exact mem_iUnion.2 ⟨k, z, hball k (ball_subset_closedBall hz), rfl⟩
  -- Step 4, (ii): `S_t` is Borel, so (TL) transfers the tangent planes of the compact patches
  -- `χ_k(B̄_{ρ_k}(c_k))` to `S_t` at `Hⁿ`-a.e. `x ∈ S_t`
  have hSmeas : MeasurableSet S := by
    have hΓ : MeasurableSet (Y ∩ {y | fderiv ℝ F y ≠ 0} ∩ F ⁻¹' {t}) :=
      (hY.inter (isOpen_ne_fun (hF.continuous_fderiv one_ne_zero)
        continuous_const).measurableSet).inter
        (hF.continuous.measurable (measurableSet_singleton t))
    rw [hSeq]
    exact hΓ.image_of_continuousOn_injOn (hψ.continuousOn.mono fun y hy => hYV hy.1.1)
      (hψinj.mono fun y hy => hYV hy.1.1)
  filter_upwards [Submission.dor_lmbsf_pst_patch_tangent_transfer hTL P n S D (fun k => ψ ∘ Λ k)
    c ρ hSmeas hfin hDo hχ hball hχinj, ae_restrict_mem hSmeas] with x hx hxS
  rintro y hy rfl
  obtain ⟨k, z, hz, rfl⟩ := hchart y hy hxS
  -- Step 5, `Dχ_k(z) = Dψ(Λ_k z) ∘ DΛ_k(z)` is injective, with range
  -- `Dψ(Λ_k z)(ker DF(Λ_k z)) = Dψ(Λ_k z)(ℝ^{n+1}) ∩ G(χ_k z)^⊥`
  have hzD : z ∈ D k := hball k (ball_subset_closedBall hz)
  obtain ⟨-, -, hDΛ, hrangeΛ⟩ := hΛD k z hzD
  have hderiv : fderiv ℝ (ψ ∘ Λ k) z = (fderiv ℝ ψ (Λ k z)).comp (fderiv ℝ (Λ k) z) :=
    fderiv_comp z ((hψ.contDiffAt (hV.mem_nhds (hΛV k hzD))).differentiableAt one_ne_zero)
      (((hΛ k).contDiffAt ((hDo k).mem_nhds hzD)).differentiableAt one_ne_zero)
  have hrange : LinearMap.range (fderiv ℝ (ψ ∘ Λ k) z : Euclid n →ₗ[ℝ] Euclid P) =
      LinearMap.range (fderiv ℝ ψ (Λ k z) : Euclid (n + 1) →ₗ[ℝ] Euclid P) ⊓
        (ℝ ∙ G (ψ (Λ k z)))ᗮ := by
    rw [(halg _ hy).2, hderiv, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
      hrangeΛ]
  -- `image_tangent`: the patch `χ_k(B̄_{ρ_k}(c_k))` has approximate tangent space
  -- `Dχ_k(z)(ℝⁿ)` at `χ_k(z)`, since `z ∈ B_{ρ_k}(c_k) ⊆ int B̄_{ρ_k}(c_k)`
  have himage := Submission.dor_lmbsf_c1_image_approxTangent n P (D k) (closedBall (c k) (ρ k))
    (ψ ∘ Λ k) z (hDo k) (hχ k) (isCompact_closedBall _ _) (hball k) (hχinj k)
    (ball_subset_interior_closedBall hz)
    (by rw [hderiv, ContinuousLinearMap.coe_comp]; exact (hDψ _ (hYV hy)).comp hDΛ)
  rw [hrange] at himage
  exact hx k z hz rfl _ himage
/-- **Weak convergence of derivatives against `C¹` test fields.**  If the `uₖ : ℝᵈ → ℝ` are
`K`-Lipschitz and converge uniformly to `u`, and `Ψ : ℝᵈ → ℝᵈ` is `C¹` with compact support, then
`∫ Duₖ[Ψ] → ∫ Du[Ψ]`.  The limit `u` is again `K`-Lipschitz.  Writing `Ψ = Σₗ Ψₗ eₗ`,
Rademacher's theorem and integration by parts give `∫ Dv[Ψ] = Σₗ ∫ qₗ v` for every Lipschitz `v`,
where `qₗ = DΨₗ[-eₗ]` is continuous with compact support; dominated convergence with the bound
`|qₗ| (|u| + 1)` gives `∫ qₗ uₖ → ∫ qₗ u`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_weak_smooth : ∀ (d : ℕ) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ) (Ψ : Euclid d → Euclid d), (∀ k, LipschitzWith K (us k)) → TendstoUniformly us u atTop → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) atTop (𝓝 (∫ y, fderiv ℝ u y (Ψ y))) := by
  intro d K us u Ψ hus hU hΨ hΨc
  -- the uniform limit `u` is again `K`-Lipschitz
  have hu : LipschitzWith K u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at y))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x y)
  -- coordinates `Ψₗ = ⟨Ψ, eₗ⟩`: `C¹` with compact support
  set e : Fin d → Euclid d := fun l => EuclideanSpace.single l 1
  set g : Fin d → Euclid d → ℝ := fun l y => Ψ y l
  have hg_smooth : ∀ l, ContDiff ℝ 1 (g l) := fun l =>
    (EuclideanSpace.proj l : Euclid d →L[ℝ] ℝ).contDiff.comp hΨ
  have hg_supp : ∀ l, HasCompactSupport (g l) := fun l =>
    hΨc.comp_left (g := fun v : Euclid d => v l) (by simp)
  have hdecomp : ∀ (L : Euclid d →L[ℝ] ℝ) (x : Euclid d), L x = ∑ l, L (e l) * x l := by
    intro L x
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x]
    simp [map_sum, map_smul, e, EuclideanSpace.basisFun_apply, mul_comm]
  -- `qₗ = DΨₗ[-eₗ]` is continuous with compact support
  set q : Fin d → Euclid d → ℝ := fun l y => lineDeriv ℝ (g l) y (-(e l))
  have hq_eq : ∀ l, q l = fun y => fderiv ℝ (g l) y (-(e l)) := fun l => funext fun y =>
    ((hg_smooth l).differentiable one_ne_zero y).lineDeriv_eq_fderiv
  have hq_cont : ∀ l, Continuous (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_smooth l).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hq_supp : ∀ l, HasCompactSupport (q l) := by
    intro l
    rw [hq_eq l]
    exact ((hg_supp l).fderiv (𝕜 := ℝ)).comp_left (g := fun L : Euclid d →L[ℝ] ℝ => L (-(e l)))
      (by simp)
  -- for Lipschitz `v`, `∫ Dv[Ψ] = Σₗ ∫ Dv[eₗ] Ψₗ = Σₗ ∫ qₗ v` (Rademacher, integration by parts)
  have hsum : ∀ (v : Euclid d → ℝ) (C : NNReal), LipschitzWith C v →
      ∫ y, fderiv ℝ v y (Ψ y) = ∑ l, ∫ y, q l y * v y := by
    intro v C hv
    have h1 : (fun y => fderiv ℝ v y (Ψ y)) = fun y => ∑ l, fderiv ℝ v y (e l) * g l y := by
      funext y
      exact hdecomp _ _
    rw [h1, integral_finsetSum]
    · refine Finset.sum_congr rfl fun l _ => ?_
      obtain ⟨D, hD⟩ := (hg_smooth l).lipschitzWith_of_hasCompactSupport (hg_supp l) one_ne_zero
      rw [← hv.integral_lineDeriv_mul_eq hD (hg_supp l) (e l)]
      apply integral_congr_ae
      filter_upwards [hv.ae_differentiableAt] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    · intro l _
      have hgi : Integrable (g l) :=
        (hg_smooth l).continuous.integrable_of_hasCompactSupport (hg_supp l)
      refine Integrable.bdd_mul (c := C * ‖e l‖) hgi
        (measurable_fderiv_apply_const ℝ v (e l)).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
  rw [hsum u K hu]
  have hk : (fun k => ∫ y, fderiv ℝ (us k) y (Ψ y)) = fun k => ∑ l, ∫ y, q l y * us k y := by
    funext k
    exact hsum (us k) K (hus k)
  rw [hk]
  -- dominated convergence for each `∫ qₗ uₖ`, with bound `|qₗ| (|u| + 1)`
  refine tendsto_finsetSum _ fun l _ => ?_
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖q l y‖ * (‖u y‖ + 1))
  · exact Eventually.of_forall fun k => ((hq_cont l).mul (hus k).continuous).aestronglyMeasurable
  · rw [Metric.tendstoUniformly_iff] at hU
    filter_upwards [hU 1 one_pos] with k hk
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul]
    gcongr
    have h1 := hk y
    rw [dist_eq_norm] at h1
    have h2 : ‖us k y‖ ≤ ‖u y‖ + ‖u y - us k y‖ := by
      have := norm_sub_norm_le (us k y) (u y)
      rw [norm_sub_rev] at this
      linarith
    linarith
  · exact ((hq_cont l).norm.mul (hu.continuous.norm.add continuous_const))
      |>.integrable_of_hasCompactSupport (hq_supp l).norm.mul_right
  · exact Eventually.of_forall fun y => ((hU.tendsto_at y).const_mul (q l y))

/-- **Weak convergence of derivatives against `L¹` fields.**  If the `uₖ : ℝᵈ → ℝ` are
`K`-Lipschitz and converge uniformly to `u`, then `∫ Duₖ[Φ] → ∫ Du[Φ]` for every integrable
`Φ : ℝᵈ → ℝᵈ`.  The limit `u` is `K`-Lipschitz, and for `K`-Lipschitz `v` and integrable `Θ` the
field `Dv[Θ]` is integrable with `|∫ Dv[Θ]| ≤ K ∫ |Θ|`.  Given `ε > 0`, take a `C¹` compactly
supported `Ψ` with `∫ |Φ - Ψ| ≤ ε/(4K + 1)`: such fields are dense in `L¹`, as each `c 1_s` with
`|s| < ∞` is approximated by `f c`, `f` a smooth Urysohn function for a compact `L ⊆ s` inside an
open `W ⊇ s` with `|W \ L|` small.  Then `|∫ Dv[Φ] - ∫ Dv[Ψ]| ≤ ε/4` for `v = uₖ, u`, and
`∫ Duₖ[Ψ] → ∫ Du[Ψ]` by `dor_lmbsf_pwl_fderiv_weak_smooth`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_weak_integrable : ∀ (d : ℕ) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ) (Φ : Euclid d → Euclid d), (∀ k, LipschitzWith K (us k)) → TendstoUniformly us u atTop → Integrable Φ → Tendsto (fun k => ∫ y, fderiv ℝ (us k) y (Φ y)) atTop (𝓝 (∫ y, fderiv ℝ u y (Φ y))) := by
  intro d K us u Φ hus hU hΦ
  -- the uniform limit `u` is `K`-Lipschitz
  have hu : LipschitzWith K u := LipschitzWith.of_dist_le_mul fun x z =>
    le_of_tendsto ((hU.tendsto_at x).dist (hU.tendsto_at z))
      (Eventually.of_forall fun k => (hus k).dist_le_mul x z)
  -- `‖Dv‖ ≤ K` for `K`-Lipschitz `v`, so `Dv[Θ]` is integrable and `|∫ Dv[Θ]| ≤ K ∫ |Θ|`
  have hbound : ∀ v : Euclid d → ℝ, LipschitzWith K v → ∀ Θ : Euclid d → Euclid d,
      Integrable Θ → Integrable (fun y => fderiv ℝ v y (Θ y)) ∧
        ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ K * ∫ y, ‖Θ y‖ := by
    intro v hv Θ hΘ
    have hmeas : AEStronglyMeasurable (fun y => fderiv ℝ v y (Θ y)) volume :=
      Continuous.comp_aestronglyMeasurable
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid d) (F := ℝ)).continuous
        ((measurable_fderiv ℝ v).aestronglyMeasurable.prodMk hΘ.aestronglyMeasurable)
    have hle : ∀ y, ‖fderiv ℝ v y (Θ y)‖ ≤ K * ‖Θ y‖ := fun y =>
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hv) (norm_nonneg _))
    refine ⟨(hΘ.norm.const_mul K).mono' hmeas (Eventually.of_forall hle), ?_⟩
    calc ‖∫ y, fderiv ℝ v y (Θ y)‖ ≤ ∫ y, (K : ℝ) * ‖Θ y‖ :=
          norm_integral_le_of_norm_le (hΘ.norm.const_mul K) (Eventually.of_forall hle)
      _ = K * ∫ y, ‖Θ y‖ := integral_const_mul _ _
  -- `C¹` compactly supported fields are dense in `L¹`.  By `MemLp.induction_dense` it suffices to
  -- approximate `c 1_s` for `s` of finite measure: take a compact `L ⊆ s` and an open `W ⊇ s` with
  -- `|W \ L| < δ/|c|`, and a smooth `f : ℝᵈ → [0, 1]` with `f = 1` on `L` and support
  -- `W ∩ B_R(0) ⊇ L`; then `|f c - c 1_s| ≤ |c| 1_{W \ L}`.
  have hdense : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ Ψ : Euclid d → Euclid d,
      eLpNorm (Φ - Ψ) 1 volume ≤ ε ∧ ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ := by
    intro ε hε
    refine (memLp_one_iff_integrable.2 hΦ).induction_dense ENNReal.one_ne_top
      (fun Ψ => ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ) ?_ ?_ hε
    · intro c s hs hμs δ hδ
      rcases eq_or_ne c 0 with rfl | hc
      · exact ⟨0, by simp, contDiff_const, HasCompactSupport.zero⟩
      have hc0 : ‖c‖ₑ ≠ 0 := enorm_ne_zero.2 hc
      have hη : δ / ‖c‖ₑ / 2 ≠ 0 := by simp [ENNReal.div_eq_zero_iff, hδ]
      obtain ⟨W, hsW, hWo, -, hW⟩ := hs.exists_isOpen_sdiff_lt hμs.ne hη
      obtain ⟨L, hLs, hLc, hL⟩ := hs.exists_isCompact_sdiff_lt hμs.ne hη
      obtain ⟨R, hR⟩ := hLc.isBounded.subset_ball 0
      obtain ⟨f, hfs, hf01, hfsupp, hf1⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1)
        (hWo.inter isOpen_ball) hLc.isClosed (subset_inter (hLs.trans hsW) hR)
      have hf0 : ∀ x, x ∉ W ∩ ball 0 R → f x = 0 := fun x hx =>
        notMem_support.1 (hfsupp.symm ▸ hx)
      refine ⟨fun x => f x • c, ?_, hfs.smul contDiff_const, ?_⟩
      · have hpt : ∀ x, ‖((fun x => f x • c) - s.indicator fun _ => c) x‖
            ≤ ‖(W \ L).indicator (fun _ => c) x‖ := by
          intro x
          obtain ⟨hfx0, hfx1⟩ := hf01 (mem_range_self x)
          by_cases hxs : x ∈ s
          · by_cases hxL : x ∈ L
            · simp [indicator_of_mem hxs, (hf1 x).1 hxL]
            · rw [Pi.sub_apply, indicator_of_mem hxs,
                indicator_of_mem (mem_sdiff_of_mem (hsW hxs) hxL),
                show f x • c - c = (f x - 1) • c by rw [sub_smul, one_smul], norm_smul,
                Real.norm_eq_abs, abs_of_nonpos (by linarith)]
              exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
          · by_cases hxW : x ∈ W
            · rw [Pi.sub_apply, indicator_of_notMem hxs,
                indicator_of_mem (mem_sdiff_of_mem hxW fun h => hxs (hLs h)), sub_zero, norm_smul,
                Real.norm_eq_abs, abs_of_nonneg hfx0]
              exact mul_le_of_le_one_left (norm_nonneg _) hfx1
            · simp [indicator_of_notMem hxs, hf0 x fun h => hxW h.1]
        have hWL : volume (W \ L) ≤ δ / ‖c‖ₑ := by
          calc volume (W \ L) ≤ volume ((W \ s) ∪ (s \ L)) := measure_mono fun x hx => by
                by_cases h : x ∈ s
                · exact Or.inr ⟨h, hx.2⟩
                · exact Or.inl ⟨hx.1, h⟩
            _ ≤ volume (W \ s) + volume (s \ L) := measure_union_le _ _
            _ ≤ δ / ‖c‖ₑ / 2 + δ / ‖c‖ₑ / 2 := add_le_add hW.le hL.le
            _ = δ / ‖c‖ₑ := ENNReal.add_halves _
        calc eLpNorm ((fun x => f x • c) - s.indicator fun _ => c) 1 volume
            ≤ eLpNorm ((W \ L).indicator fun _ => c) 1 volume :=
              eLpNorm_mono ((hfs.continuous.smul continuous_const).aestronglyMeasurable.sub
                (aestronglyMeasurable_const.indicator hs)) hpt
          _ ≤ ‖c‖ₑ * volume (W \ L) := by
              simpa using eLpNorm_indicator_const_le c 1
                (μ := volume) (hWo.measurableSet.diff hLc.measurableSet).nullMeasurableSet
          _ ≤ ‖c‖ₑ * (δ / ‖c‖ₑ) := by gcongr
          _ = δ := ENNReal.mul_div_cancel hc0 enorm_ne_top
      · refine HasCompactSupport.intro (isCompact_closedBall 0 R) fun x hx => ?_
        rw [hf0 x fun h => hx (ball_subset_closedBall h.2), zero_smul]
    · rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
      exact ⟨hf.add hg, hf'.add hg'⟩
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  -- a `C¹` compactly supported `Ψ` with `∫ |Φ - Ψ| ≤ η`, where `Kη ≤ ε/4`
  set η : ℝ := ε / (4 * K + 1) with hη
  have hηpos : 0 < η := div_pos hε (by positivity)
  have hKη : (K : ℝ) * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [K.2]
  obtain ⟨Ψ, hΨε, hΨs, hΨc⟩ := hdense (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hηpos).ne'
  have hΨi : Integrable Ψ := hΨs.continuous.integrable_of_hasCompactSupport hΨc
  have hdiff : ∫ y, ‖(Φ - Ψ) y‖ ≤ η := by
    rw [integral_norm_eq_lintegral_enorm (hΦ.sub hΨi).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm (hΦ.sub hΨi).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hηpos.le hΨε
  -- replacing `Φ` by `Ψ` moves `∫ Dv[Φ]` by at most `Kη ≤ ε/4`
  have hclose : ∀ v : Euclid d → ℝ, LipschitzWith K v →
      dist (∫ y, fderiv ℝ v y (Φ y)) (∫ y, fderiv ℝ v y (Ψ y)) ≤ ε / 4 := by
    intro v hv
    rw [dist_eq_norm, ← integral_sub (hbound v hv Φ hΦ).1 (hbound v hv Ψ hΨi).1]
    calc ‖∫ y, (fderiv ℝ v y (Φ y) - fderiv ℝ v y (Ψ y))‖
        = ‖∫ y, fderiv ℝ v y ((Φ - Ψ) y)‖ := by simp only [Pi.sub_apply, map_sub]
      _ ≤ K * ∫ y, ‖(Φ - Ψ) y‖ := (hbound v hv (Φ - Ψ) (hΦ.sub hΨi)).2
      _ ≤ K * η := mul_le_mul_of_nonneg_left hdiff K.2
      _ ≤ ε / 4 := hKη
  -- `∫ Duₖ[Ψ] → ∫ Du[Ψ]` for the `C¹` compactly supported field `Ψ`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (Submission.dor_lmbsf_pwl_fderiv_weak_smooth d K us u Ψ hus hU hΨs hΨc) (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hclose (us k) (hus k)
  have h2 : dist (∫ y, fderiv ℝ (us k) y (Ψ y)) (∫ y, fderiv ℝ u y (Ψ y)) < ε / 2 := hN k hk
  have h3 := hclose u hu
  rw [dist_comm] at h3
  linarith [dist_triangle4 (∫ y, fderiv ℝ (us k) y (Φ y)) (∫ y, fderiv ℝ (us k) y (Ψ y))
    (∫ y, fderiv ℝ u y (Ψ y)) (∫ y, fderiv ℝ u y (Φ y))]
/-- **Functions agreeing on a measurable set have equal derivatives a.e. on it.**  Assume that
density points see every direction (the statement of `Submission.dor_lmbsf_density_directions`).
If `Z ⊆ ℝᵈ` is measurable and `v₁ = v₂` on `Z`, then `Dv₁(y) = Dv₂(y)` at `Lᵈ`-a.e. `y ∈ Z` where
both are differentiable.  By the Besicovitch density theorem a.e. `y ∈ Z` is a density point of `Z`;
there each unit vector `e` is a limit of `(yᵢ - y)/|yᵢ - y|` with `yᵢ ∈ Z ∖ {y}`, `yᵢ → y`, and the
difference quotients of `v₁ - v₂` along `yᵢ` vanish, so `(Dv₁(y) - Dv₂(y)) e = 0`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (d : ℕ) (Z : Set (Euclid d)) (v₁ v₂ : Euclid d → ℝ), MeasurableSet Z → EqOn v₁ v₂ Z → ∀ᵐ y ∂(volume : Measure (Euclid d)), y ∈ Z → DifferentiableAt ℝ v₁ y → DifferentiableAt ℝ v₂ y → fderiv ℝ v₁ y = fderiv ℝ v₂ y := by
  intro hDD d Z v₁ v₂ hZ hEq
  -- a.e. point of `Z` is a Lebesgue density point of `Z`
  have h := Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid d)) Z
  rw [ae_restrict_iff' hZ] at h
  filter_upwards [h] with y hy hyZ h1 h2
  have hden := hy hyZ
  set L := fderiv ℝ v₁ y - fderiv ℝ v₂ y with hLdef
  have hv : HasFDerivAt (fun x => v₁ x - v₂ x) L y := h1.hasFDerivAt.sub h2.hasFDerivAt
  -- along `yᵢ ∈ Z` with `(yᵢ - y)/|yᵢ - y| → e` the difference quotients of `v₁ - v₂` are `0`
  have hunit : ∀ e : Euclid d, ‖e‖ = 1 → L e = 0 := by
    intro e he
    obtain ⟨ys, hysZ, hys, hdir⟩ := hDD d Z y hden e he
    have hd0 : Tendsto (fun i => ys i - y) atTop (𝓝 0) := by
      simpa using hys.sub_const y
    have hlim := (hv.hasFDerivWithinAt (s := univ)).lim (l := atTop)
      (c := fun i => ‖ys i - y‖⁻¹) (d := fun i => ys i - y) hd0
      (Eventually.of_forall fun _ => mem_univ _) hdir
    have hzero : (fun i => ‖ys i - y‖⁻¹ • ((v₁ (y + (ys i - y)) - v₂ (y + (ys i - y))) -
        (v₁ y - v₂ y))) = fun _ => (0 : ℝ) := by
      funext i
      have hi : y + (ys i - y) = ys i := by abel
      rw [hi, hEq (hysZ i).1, hEq hyZ]
      simp
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  -- a linear map vanishing on unit vectors is `0`
  have hL : L = 0 := by
    ext e
    by_cases he : e = 0
    · simp [he]
    · have hn : ‖e‖ ≠ 0 := norm_ne_zero_iff.2 he
      have h1' : ‖‖e‖⁻¹ • e‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      have := hunit _ h1'
      rw [map_smul, smul_eq_mul, mul_eq_zero] at this
      rcases this with h | h
      · exact absurd (inv_eq_zero.1 h) hn
      · simpa using h
  exact sub_eq_zero.1 hL

/-- **Chain rule for the cutoff `γ ∘ F`, a.e. on a Borel set.**  Let `a < b`,
`γ(s) = min{1, max{0, (b - s)/(b - a)}}`, `F : ℝᵈ → ℝ` differentiable and `u` Lipschitz with
`u = γ ∘ F` on a Borel set `Z`.  Assuming the density-directions lemma (DD), for a.e. `y ∈ Z`,
`Du(y) = γ'(F(y)) DF(y)`, where `γ' = -(b - a)⁻¹` on `(a, b)` and `γ' = 0` elsewhere.  By
Rademacher `u` is differentiable a.e.  On the kink levels `Z ∩ {F = a}` and `Z ∩ {F = b}`, `u` agrees
with the constants `γ(a) = 1` and `γ(b) = 0`; off them `γ ∘ F` is, near `y`, identically `1`,
`(b - F)/(b - a)` or `0`, hence differentiable with derivative `γ'(F(y)) DF(y)`.  In each case the
agreement lemma `dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn` transfers the derivative to `u`. -/
theorem Submission.dor_lmbsf_pwl_fderiv_cutoff_comp_ae : (∀ (d : ℕ) (Z : Set (Euclid d)) (y : Euclid d), Tendsto (fun r => volume (Z ∩ closedBall y r) / volume (closedBall y r)) (𝓝[>] 0) (𝓝 1) → ∀ v : Euclid d, ‖v‖ = 1 → ∃ ys : ℕ → Euclid d, (∀ i, ys i ∈ Z ∧ ys i ≠ y) ∧ Tendsto ys atTop (𝓝 y) ∧ Tendsto (fun i => ‖ys i - y‖⁻¹ • (ys i - y)) atTop (𝓝 v)) → ∀ (d : ℕ) (Z : Set (Euclid d)) (F u : Euclid d → ℝ) (K : NNReal) (a b : ℝ), MeasurableSet Z → Differentiable ℝ F → LipschitzWith K u → a < b → (∀ y ∈ Z, u y = min 1 (max 0 ((b - F y) / (b - a)))) → ∀ᵐ y ∂(volume : Measure (Euclid d)), y ∈ Z → fderiv ℝ u y = (if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y := by
  intro hDD d Z F u K a b hZ hF hu hab hEq
  have hFc : Continuous F := hF.continuous
  have hba : 0 < b - a := sub_pos.2 hab
  set g : Euclid d → ℝ := fun y => min 1 (max 0 ((b - F y) / (b - a))) with hgdef
  -- the Borel pieces `Z ∩ {F ∉ {a, b}}`, `Z ∩ {F = a}`, `Z ∩ {F = b}`
  have hZ0 : MeasurableSet (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) := by
    refine hZ.inter ?_
    have h1 : MeasurableSet {y | F y ≠ a} :=
      (measurableSet_singleton a).compl.preimage hFc.measurable
    have h2 : MeasurableSet {y | F y ≠ b} :=
      (measurableSet_singleton b).compl.preimage hFc.measurable
    exact h1.inter h2
  have hZa : MeasurableSet (Z ∩ F ⁻¹' {a}) :=
    hZ.inter ((measurableSet_singleton a).preimage hFc.measurable)
  have hZb : MeasurableSet (Z ∩ F ⁻¹' {b}) :=
    hZ.inter ((measurableSet_singleton b).preimage hFc.measurable)
  -- Rademacher: `u` is differentiable a.e.
  have hdiff : ∀ᵐ y ∂(volume : Measure (Euclid d)), DifferentiableAt ℝ u y :=
    hu.ae_differentiableAt
  -- `u = γ ∘ F` off the kinks, `u = γ(a) = 1` on `{F = a}` and `u = γ(b) = 0` on `{F = b}`
  have h0 := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ {y | F y ≠ a ∧ F y ≠ b}) u g
    hZ0 (fun y hy => hEq y hy.1)
  have ha := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {a}) u (fun _ => 1)
    hZa (by
      intro y hy
      have hFy : F y = a := hy.2
      simp only [hEq y hy.1, hFy, div_self hba.ne']
      simp)
  have hb := Submission.dor_lmbsf_pwl_fderiv_eq_ae_of_eqOn hDD d (Z ∩ F ⁻¹' {b}) u (fun _ => 0)
    hZb (by
      intro y hy
      have hFy : F y = b := hy.2
      simp only [hEq y hy.1, hFy, sub_self, zero_div]
      simp)
  filter_upwards [hdiff, h0, ha, hb] with y hyd hy0 hya hyb hyZ
  -- kink levels: `Du(y) = 0 = γ'(F(y)) DF(y)`
  by_cases hFa : F y = a
  · have h := hya ⟨hyZ, hFa⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFa]
  by_cases hFb : F y = b
  · have h := hyb ⟨hyZ, hFb⟩ hyd (differentiableAt_const _)
    rw [h, fderiv_const_apply]
    simp [hFb]
  -- off the kinks `g = γ ∘ F` is locally `1`, `(b - F)/(b - a)` or `0`
  have hgd : HasFDerivAt g ((if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) y := by
    have hFd : HasFDerivAt F (fderiv ℝ F y) y := (hF y).hasFDerivAt
    rcases lt_or_gt_of_ne hFa with h | h
    · -- `F y < a`: `g = 1` near `y`
      have hev : g =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
        filter_upwards [hFc.continuousAt.eventually (gt_mem_nhds h)] with z hz
        have : 1 < (b - F z) / (b - a) := by
          rw [one_lt_div hba]; linarith
        simp only [hgdef]
        rw [max_eq_right (by linarith), min_eq_left this.le]
      have hn : ¬ (a < F y ∧ F y < b) := fun h' => absurd h'.1 (not_lt.2 h.le)
      simp only [hn, ite_false, zero_smul]
      exact (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hev
    · rcases lt_or_gt_of_ne hFb with h' | h'
      · -- `a < F y < b`: `g = (b - F)/(b - a)` near `y`
        have hev : g =ᶠ[𝓝 y] fun z => (b - F z) / (b - a) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h),
            hFc.continuousAt.eventually (gt_mem_nhds h')] with z hz1 hz2
          have hpos : 0 < (b - F z) / (b - a) := div_pos (by linarith) hba
          have hlt : (b - F z) / (b - a) < 1 := by
            rw [div_lt_one hba]; linarith
          simp only [hgdef]
          rw [max_eq_right hpos.le, min_eq_right hlt.le]
        have hy' : a < F y ∧ F y < b := ⟨h, h'⟩
        simp only [hy', and_self, ite_true]
        have hlin : HasFDerivAt (fun z => (b - F z) / (b - a))
            (-(b - a)⁻¹ • fderiv ℝ F y) y := by
          have := ((hasFDerivAt_const b y).sub hFd).const_mul (b - a)⁻¹
          convert this using 1
          · funext z
            simp only [Pi.sub_apply]
            rw [div_eq_inv_mul]
          · rw [zero_sub, smul_neg, neg_smul]
        exact hlin.congr_of_eventuallyEq hev
      · -- `F y > b`: `g = 0` near `y`
        have hev : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          filter_upwards [hFc.continuousAt.eventually (lt_mem_nhds h')] with z hz
          have : (b - F z) / (b - a) < 0 := div_neg_of_neg_of_pos (by linarith) hba
          simp only [hgdef]
          rw [max_eq_left this.le]
          simp
        have hn : ¬ (a < F y ∧ F y < b) := fun h'' => absurd h''.2 (not_lt.2 h'.le)
        simp only [hn, ite_false, zero_smul]
        exact (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
  have h := hy0 ⟨hyZ, hFa, hFb⟩ hyd hgd.differentiableAt
  rw [h, hgd.fderiv]
/-- **Cut-off localization of `hₖ ∘ ψ` near a compact subset of a `C¹` chart domain.**  Choose
`δ > 0` with `S = cthickening δ C ⊆ V` and a `C¹` Urysohn function `χ : ℝᵈ → [0, 1]` equal to `1`
on `cthickening (δ/2) C` and to `0` off `thickening δ C`, so `tsupport χ ⊆ S`.  Then
`uₖ = χ · (hₖ ∘ ψ)` and `u = χ · (h ∘ ψ)` agree with `hₖ ∘ ψ`, `h ∘ ψ` on `O = thickening (δ/2) C`.
On `S` the `hₖ ∘ ψ` are bounded by some `B` uniformly in `k` (`ψ(S)` is bounded, the `hₖ` are
`c`-Lipschitz and `hₖ(ψ(y₀))` converges), so the product and chain rules give
`‖Duₖ‖ ≤ B sup ‖Dχ‖ + c sup_S ‖Dψ‖`; `uₖ → u` uniformly because `0 ≤ χ ≤ 1`, and `u` is Lipschitz
as the pointwise limit of the `uₖ`.  For `C = ∅` all the functions are `0`. -/
theorem Submission.dor_lmbsf_pwl_chart_cutoff_localize : ∀ (P d : ℕ) (V C : Set (Euclid d)) (ψ : Euclid d → Euclid P) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (c : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → IsCompact C → C ⊆ V → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs h atTop → ∃ (O : Set (Euclid d)) (K : NNReal) (us : ℕ → Euclid d → ℝ) (u : Euclid d → ℝ), IsOpen O ∧ C ⊆ O ∧ (∀ k, LipschitzWith K (us k)) ∧ LipschitzWith K u ∧ TendstoUniformly us u atTop ∧ (∀ k, ∀ y ∈ O, us k y = hs k (ψ y)) ∧ ∀ y ∈ O, u y = h (ψ y) := by
  intro P d V C ψ hs h c hV hψ hC hCV hhs hhsb hU
  rcases C.eq_empty_or_nonempty with hCe | ⟨y₀, hy₀⟩
  · refine ⟨∅, 0, fun _ _ => 0, fun _ => 0, isOpen_empty, by simp [hCe],
      fun _ => LipschitzWith.const 0, LipschitzWith.const 0, ?_, by simp, by simp⟩
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun _ _ => by simpa using hε
  have hc : 0 ≤ c := (norm_nonneg _).trans (hhsb 0 0)
  -- the compact `S = cthickening δ C ⊆ V` and the cut-off `χ`, `1` near `C` and `0` off `S`
  obtain ⟨δ, hδ, hδV⟩ := hC.exists_cthickening_subset_open hV hCV
  have hδ2 : 0 < δ / 2 := by positivity
  set S := cthickening δ C
  have hS : IsCompact S := hC.cthickening
  have hst : Disjoint (thickening δ C)ᶜ (cthickening (δ / 2) C) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' hδ (by linarith) C
  obtain ⟨χ, hχs, hχr, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := 1)
    isOpen_thickening.isClosed_compl isClosed_cthickening hst
  have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
  have hsupp : tsupport χ ⊆ S := by
    apply closure_minimal _ isClosed_cthickening
    intro y hy
    by_contra hcon
    exact hy ((hχ0 y).1 (fun h' => hcon (thickening_subset_cthickening δ C h')))
  have hχc : HasCompactSupport χ := hS.of_isClosed_subset (isClosed_tsupport χ) hsupp
  -- bounds `Mχ` for `‖Dχ‖`, `Mψ` for `‖Dψ‖` on `S` and `B` for `|hₖ ∘ ψ|` on `S`, uniform in `k`
  obtain ⟨Mχ, hMχ⟩ := (hχc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hχs.continuous_fderiv one_ne_zero)
  obtain ⟨Mψ, hMψ⟩ := hS.exists_bound_of_continuousOn
    ((hψ.continuousOn_fderiv_of_isOpen hV le_rfl).mono hδV)
  have hy₀S : y₀ ∈ S := self_subset_cthickening C hy₀
  have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ y₀)
  have hMψ0 : 0 ≤ Mψ := (norm_nonneg _).trans (hMψ y₀ hy₀S)
  have hhsL : ∀ k, LipschitzWith ⟨c, hc⟩ (hs k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le ((hhs k).differentiable one_ne_zero) (fun x =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact hhsb k x))
  have hψS : IsCompact (ψ '' S) := hS.image_of_continuousOn (hψ.continuousOn.mono hδV)
  obtain ⟨D, hD⟩ := hψS.isBounded.subset_closedBall (ψ y₀)
  obtain ⟨B₀, hB₀⟩ := ((hU.tendsto_at (ψ y₀)).abs).bddAbove_range
  set B := B₀ + c * D
  have hB : ∀ k, ∀ y ∈ S, |hs k (ψ y)| ≤ B := by
    intro k y hy
    have h1 : |hs k (ψ y) - hs k (ψ y₀)| ≤ c * dist (ψ y) (ψ y₀) := by
      have := (hhsL k).dist_le_mul (ψ y) (ψ y₀)
      rw [Real.dist_eq] at this
      exact this
    have h2 : dist (ψ y) (ψ y₀) ≤ D := hD (mem_image_of_mem ψ hy)
    have h3 : |hs k (ψ y₀)| ≤ B₀ := hB₀ ⟨k, rfl⟩
    have h4 := abs_sub_abs_le_abs_sub (hs k (ψ y)) (hs k (ψ y₀))
    have h5 : c * dist (ψ y) (ψ y₀) ≤ c * D := mul_le_mul_of_nonneg_left h2 hc
    linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 y₀ hy₀S)
  set K : ℝ := B * Mχ + c * Mψ with hKdef
  have hK0 : 0 ≤ K := by positivity
  -- `uₖ = χ · (hₖ ∘ ψ)` has `‖Duₖ‖ ≤ K`: product and chain rules on `tsupport χ ⊆ S ⊆ V`, and
  -- `uₖ` vanishes near every point off `tsupport χ`
  set us : ℕ → Euclid d → ℝ := fun k y => χ y * hs k (ψ y) with husdef
  have hderiv : ∀ k y, DifferentiableAt ℝ (us k) y ∧ ‖fderiv ℝ (us k) y‖ ≤ K := by
    intro k y
    by_cases hy : y ∈ tsupport χ
    · have hyS : y ∈ S := hsupp hy
      have hyV : y ∈ V := hδV hyS
      have hψd : HasFDerivAt ψ (fderiv ℝ ψ y) y :=
        ((hψ.differentiableOn one_ne_zero y hyV).differentiableAt (hV.mem_nhds hyV)).hasFDerivAt
      have hhd : HasFDerivAt (hs k) (fderiv ℝ (hs k) (ψ y)) (ψ y) :=
        ((hhs k).differentiable one_ne_zero (ψ y)).hasFDerivAt
      have hχd : HasFDerivAt χ (fderiv ℝ χ y) y := (hχs.differentiable one_ne_zero y).hasFDerivAt
      have hprod : HasFDerivAt (us k) (χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) +
          (hs k ∘ ψ) y • fderiv ℝ χ y) y := hχd.mul (hhd.comp y hψd)
      refine ⟨hprod.differentiableAt, ?_⟩
      rw [hprod.fderiv]
      calc ‖χ y • (fderiv ℝ (hs k) (ψ y)).comp (fderiv ℝ ψ y) + (hs k ∘ ψ) y • fderiv ℝ χ y‖
          ≤ ‖χ y‖ * (‖fderiv ℝ (hs k) (ψ y)‖ * ‖fderiv ℝ ψ y‖) +
              ‖(hs k ∘ ψ) y‖ * ‖fderiv ℝ χ y‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, norm_smul]
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * (c * Mψ) + B * Mχ := by
            gcongr
            · rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 y).1]
              exact (hχ01 y).2
            · exact hhsb k (ψ y)
            · exact hMψ y hyS
            · rw [Real.norm_eq_abs]
              exact hB k y hyS
            · exact hMχ y
        _ = K := by rw [hKdef]; ring
    · have hev : us k =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        have : (tsupport χ)ᶜ ∈ 𝓝 y := (isClosed_tsupport χ).isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz
        simp [us, image_eq_zero_of_notMem_tsupport hz]
      have h0 : HasFDerivAt (us k) (0 : Euclid d →L[ℝ] ℝ) y :=
        (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev
      refine ⟨h0.differentiableAt, ?_⟩
      rw [h0.fderiv, norm_zero]
      exact hK0
  have husL : ∀ k, LipschitzWith ⟨K, hK0⟩ (us k) := fun k =>
    lipschitzWith_of_nnnorm_fderiv_le (fun y => (hderiv k y).1) (fun y =>
      NNReal.coe_le_coe.mp (by rw [coe_nnnorm]; exact (hderiv k y).2))
  -- `uₖ → u = χ · (h ∘ ψ)` uniformly since `0 ≤ χ ≤ 1`; the pointwise limit `u` is `K`-Lipschitz
  set u : Euclid d → ℝ := fun y => χ y * h (ψ y) with hudef
  have hUu : TendstoUniformly us u atTop := by
    rw [Metric.tendstoUniformly_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with k hk
    intro y
    have h1 := hk (ψ y)
    rw [Real.dist_eq] at h1 ⊢
    calc |u y - us k y| = |χ y| * |h (ψ y) - hs k (ψ y)| := by
          rw [← abs_mul]
          congr 1
          simp only [hudef, husdef]
          ring
      _ ≤ 1 * |h (ψ y) - hs k (ψ y)| := by
          gcongr
          rw [abs_of_nonneg (hχ01 y).1]
          exact (hχ01 y).2
      _ < ε := by linarith
  have huL : LipschitzWith ⟨K, hK0⟩ u := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    exact le_of_tendsto ((hUu.tendsto_at x).dist (hUu.tendsto_at y))
      (Eventually.of_forall fun k => (husL k).dist_le_mul x y)
  -- `χ = 1` on `O = thickening (δ / 2) C`
  have hχO : ∀ y ∈ thickening (δ / 2) C, χ y = 1 := fun y hy =>
    (hχ1 y).1 (thickening_subset_cthickening _ _ hy)
  refine ⟨thickening (δ / 2) C, ⟨K, hK0⟩, us, u, isOpen_thickening,
    self_subset_thickening hδ2 C, husL, huL, hUu, ?_, ?_⟩
  · intro k y hy
    simp [husdef, hχO y hy]
  · intro y hy
    simp [hudef, hχO y hy]
/-- **Continuous left inverse of an immersion's derivative.**  If `ψ` is `C¹` on the open set
`V ⊆ ℝᵈ` and `A(y) = Dψ(y)` is injective for every `y ∈ V`, then `R(y) = Γ(y)⁻¹ A(y)*`, with
`Γ(y) = A(y)* A(y)` the Gram operator, is a left inverse of `A(y)` depending continuously on
`y ∈ V`.  `Γ` is continuous on `V`, and `Γ(y)` is injective since `⟨Γ(y)z, z⟩ = |A(y)z|²`, hence
a unit of `L(ℝᵈ, ℝᵈ)`; `Ring.inverse` is continuous at units. -/
theorem Submission.dor_lmbsf_pwl_immersion_left_inverse : ∀ (P d : ℕ) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → ∃ R : Euclid d → (Euclid P →L[ℝ] Euclid d), ContinuousOn R V ∧ ∀ y ∈ V, (R y).comp (fderiv ℝ ψ y) = ContinuousLinearMap.id ℝ (Euclid d) := by
  intro P d V ψ hV hψ hinj
  let A : Euclid d → (Euclid d →L[ℝ] Euclid P) := fun y => fderiv ℝ ψ y
  -- the Gram operator `Γ(y) = A(y)* A(y)`
  let Γ : Euclid d → (Euclid d →L[ℝ] Euclid d) :=
    fun y => (ContinuousLinearMap.adjoint (A y)).comp (A y)
  -- `Γ(y)` is injective (`⟨Γ(y)z, z⟩ = |A(y)z|²`), hence bijective and a unit
  have hunit : ∀ y ∈ V, IsUnit (Γ y) := by
    intro y hy
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinjΓ : Injective (Γ y) := by
      intro z₁ z₂ hz
      have h0 : Γ y (z₁ - z₂) = 0 := by rw [map_sub, hz, sub_self]
      have h1 : inner ℝ (A y (z₁ - z₂)) (A y (z₁ - z₂)) = 0 := by
        rw [← ContinuousLinearMap.adjoint_inner_left]
        change inner ℝ (Γ y (z₁ - z₂)) (z₁ - z₂) = 0
        rw [h0, inner_zero_left]
      have h2 : A y (z₁ - z₂) = 0 := by
        simpa using h1
      have h3 : z₁ - z₂ = 0 := by
        apply hinj y hy
        rw [h2, map_zero]
      exact sub_eq_zero.1 h3
    have hsurj : Surjective (Γ y : Euclid d →ₗ[ℝ] Euclid d) :=
      LinearMap.injective_iff_surjective.1 hinjΓ
    exact ⟨hinjΓ, hsurj⟩
  refine ⟨fun y => (Ring.inverse (Γ y)).comp (ContinuousLinearMap.adjoint (A y)), ?_, ?_⟩
  · have hA : ContinuousOn A V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hAd : ContinuousOn (fun y => ContinuousLinearMap.adjoint (A y)) V :=
      ContinuousLinearMap.adjoint.continuous.comp_continuousOn hA
    have hΓ : ContinuousOn Γ V := hAd.clm_comp hA
    -- `Ring.inverse` is continuous at every unit
    have hinv : ContinuousOn (fun y => Ring.inverse (Γ y)) V := by
      intro y hy
      have := NormedRing.inverse_continuousAt (hunit y hy).unit
      rw [IsUnit.unit_spec] at this
      exact this.comp_continuousWithinAt (hΓ y hy)
    exact hinv.clm_comp hAd
  · intro y hy
    rw [ContinuousLinearMap.comp_assoc]
    exact Ring.inverse_mul_cancel _ (hunit y hy)

/-- **Chart transfer of a tangential pairing.**  Let `ψ` be an injective `C¹` immersion of an open
`V ⊆ ℝᵈ` into `ℝᴾ`, `Y ⊆ C ⊆ V` with `C` compact and `Y` Borel, `w ∈ L¹(Hᵈ⌞ψ(Y))`, and `W` a Borel
field with `|W| ≤ c'` that is `Hᵈ`-a.e. tangent to `ψ(Y)`.  Then one integrable `Φ`, vanishing off
`Y`, has `∫_{ψ(Y)} w β[W] dHᵈ = ∫ α[Φ] dLᵈ` whenever `β(ψ(y)) ∘ Dψ(y) = α(y)` on `Y`.  Near each
point of `C`, `ψ` is bi-Lipschitz, so the pull-back `ν(A) = Hᵈ(ψ(A ∩ Y))` of `Hᵈ⌞ψ(Y)` is a finite
measure mutually absolutely continuous with `Lᵈ⌞Y`.  With `J = dν/dLᵈ⌞Y` (the area Jacobian of
Simon Ch. 2, (3.5)), `∫_{ψ(Y)} g dHᵈ = ∫_Y J (g ∘ ψ) dLᵈ` for every `g`, and the tangency pulls
back to `Lᵈ`-a.e. `y ∈ Y`.  For a continuous left inverse `R` of `Dψ` on `V`, `E = R (W ∘ ψ)` is
bounded on `Y` by compactness of `C` and `Dψ E = W ∘ ψ` a.e. on `Y`, so `Φ = 1_Y J (w ∘ ψ) E`
works. -/
theorem Submission.dor_lmbsf_pwl_chart_pairing_transfer : ∀ (P d : ℕ) (V C Y : Set (Euclid d)) (ψ : Euclid d → Euclid P) (w : Euclid P → ℝ) (W : Euclid P → Euclid P) (c' : ℝ), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → IntegrableOn w (ψ '' Y) μHE[d] → Measurable W → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[d].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → W x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P)) → ∃ Φ : Euclid d → Euclid d, Integrable Φ ∧ (∀ y, y ∉ Y → Φ y = 0) ∧ ∀ (β : Euclid P → (Euclid P →L[ℝ] ℝ)) (α : Euclid d → (Euclid d →L[ℝ] ℝ)), (∀ y ∈ Y, (β (ψ y)).comp (fderiv ℝ ψ y) = α y) → ∫ x in ψ '' Y, w x * β x (W x) ∂μHE[d] = ∫ y, α y (Φ y) := by
  intro P d V C Y ψ w W c' hV hψ hψinj hDψ hC hCV hY hYC hw hWm hWb hWt
  have hYV : Y ⊆ V := hYC.trans hCV
  have hvol : (μHE[d] : Measure (Euclid d)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume d
  -- `ψ` is locally bi-Lipschitz on `V`
  have hloc : ∀ y ∈ V, ∃ U ∈ 𝓝 y, ∃ L K : NNReal, LipschitzOnWith L ψ U ∧
      ∀ a ∈ U, ∀ b ∈ U, dist a b ≤ K * dist (ψ a) (ψ b) := by
    intro y hy
    -- near `y`, `ψ` approximates `A = Dψ(y)` up to `(2K)⁻¹`, `K` an antilipschitz constant of `A`
    have hs : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y :=
      (hψ.contDiffAt (hV.mem_nhds hy)).hasStrictFDerivAt one_ne_zero
    obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith
      (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.mpr (hDψ y hy))
    obtain ⟨U, hU, hUA⟩ := hs.approximates_deriv_on_nhds (c := (2 * K)⁻¹)
      (Or.inr (by positivity))
    refine ⟨U, hU, ‖fderiv ℝ ψ y‖₊ + (2 * K)⁻¹, 2 * K,
      lipschitzOnWith_iff_restrict.mpr hUA.lipschitzWith, fun a ha b hb => ?_⟩
    have h1 : dist a b ≤ K * dist (fderiv ℝ ψ y a) (fderiv ℝ ψ y b) := hK.le_mul_dist a b
    have h2 : ‖ψ a - ψ b - fderiv ℝ ψ y (a - b)‖ ≤ ((2 * K)⁻¹ : NNReal) * ‖a - b‖ :=
      hUA a ha b hb
    rw [dist_eq_norm, dist_eq_norm, ← map_sub] at h1
    have h3 : ‖fderiv ℝ ψ y (a - b)‖ ≤ ‖ψ a - ψ b‖ + ‖ψ a - ψ b - fderiv ℝ ψ y (a - b)‖ := by
      have := norm_sub_le (ψ a - ψ b) (ψ a - ψ b - fderiv ℝ ψ y (a - b))
      rwa [sub_sub_cancel] at this
    have hK0 : (0 : ℝ) < K := hKpos
    have h4 : (K : ℝ) * ‖fderiv ℝ ψ y (a - b)‖ ≤ K * ‖ψ a - ψ b‖ + ‖a - b‖ / 2 := by
      have h5 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add le_rfl h2)) hK0.le
      calc (K : ℝ) * ‖fderiv ℝ ψ y (a - b)‖
          ≤ K * (‖ψ a - ψ b‖ + ((2 * K)⁻¹ : NNReal) * ‖a - b‖) := h5
        _ = K * ‖ψ a - ψ b‖ + ‖a - b‖ / 2 := by
          push_cast
          field_simp
    rw [dist_eq_norm, dist_eq_norm]
    push_cast
    linarith
  -- finitely many of these neighbourhoods, cut down to unit balls, cover `C ⊇ Y`
  choose! U hUn L K hL hK using hloc
  obtain ⟨t, htC, hCt⟩ := hC.elim_nhds_subcover (fun y => U y ∩ ball y 1)
    (fun y hy => inter_mem (hUn y (hCV hy)) (ball_mem_nhds y one_pos))
  have hcov : ∀ A ⊆ Y, A ⊆ ⋃ x ∈ t, A ∩ (U x ∩ ball x 1) := by
    intro A hA a ha
    obtain ⟨x, hx, hax⟩ := mem_iUnion₂.1 (hCt (hYC (hA ha)))
    exact mem_iUnion₂.2 ⟨x, hx, ha, hax⟩
  -- Hausdorff measure estimates on the pieces `U x ∩ B₁(x)`
  have hup : ∀ x ∈ t, ∀ B ⊆ U x ∩ ball x 1,
      μHE[d] (ψ '' B) ≤ (L x : ℝ≥0∞) ^ d * volume B := by
    intro x hx B hB
    rw [← hvol]
    exact Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d
      ((hL x (hCV (htC x hx))).mono (hB.trans inter_subset_left))
  have hlow : ∀ x ∈ t, ∀ B ⊆ U x ∩ ball x 1,
      volume B ≤ (K x : ℝ≥0∞) ^ d * μHE[d] (ψ '' B) := by
    intro x hx B hB
    have hxV := hCV (htC x hx)
    have hinj : InjOn ψ (U x) := fun a ha b hb hab => by
      have := hK x hxV a ha b hb
      rw [hab, dist_self, mul_zero] at this
      exact dist_le_zero.1 this
    have hg : LipschitzOnWith (K x) (invFunOn ψ (U x)) (ψ '' (U x)) := by
      refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
      obtain ⟨a, ha, rfl⟩ := hp
      obtain ⟨b, hb, rfl⟩ := hq
      rw [hinj.leftInvOn_invFunOn ha, hinj.leftInvOn_invFunOn hb]
      exact hK x hxV a ha b hb
    have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d
      (hg.mono (image_mono (hB.trans inter_subset_left)))
    rwa [hinj.invFunOn_image (hB.trans inter_subset_left), hvol] at this
  -- the pull-back `ν(A) = Hᵈ(ψ(A ∩ Y))` of `Hᵈ⌞ψ(Y)` to `Y`
  have hcont : ContinuousOn ψ Y := hψ.continuousOn.mono hYV
  have he := hcont.measurableEmbedding hY (hψinj.mono hYV)
  set νY : Measure Y := Measure.comap (Y.domRestrict ψ) μHE[d] with hνYdef
  set ν : Measure (Euclid d) := Measure.map Subtype.val νY with hνdef
  have hνapply : ∀ A, ν A = μHE[d] (ψ '' (A ∩ Y)) := by
    intro A
    rw [hνdef, (MeasurableEmbedding.subtype_coe hY).map_apply, hνYdef, he.comap_apply]
    congr 1
    ext p
    constructor
    · rintro ⟨⟨a, ha⟩, haA, rfl⟩
      exact ⟨a, ⟨haA, ha⟩, rfl⟩
    · rintro ⟨a, ⟨haA, ha⟩, rfl⟩
      exact ⟨⟨a, ha⟩, haA, rfl⟩
  -- `ν` and `Lᵈ⌞Y` are mutually absolutely continuous, and `ν` is finite
  have hνac : ν ≪ volume.restrict Y := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    rw [Measure.restrict_apply hA] at hA0
    rw [hνapply]
    refine measure_mono_null (image_mono (hcov _ inter_subset_right)) ?_
    rw [image_iUnion₂]
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => ?_
    exact le_zero_iff.1 ((hup x hx _ inter_subset_right).trans
      (by rw [measure_mono_null inter_subset_left hA0, mul_zero]))
  have hYν : volume.restrict Y ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
    rw [hνapply] at hA0
    rw [Measure.restrict_apply hA]
    refine measure_mono_null (hcov _ inter_subset_right) ?_
    refine (measure_biUnion_null_iff t.countable_toSet).2 fun x hx => ?_
    exact le_zero_iff.1 ((hlow x hx _ inter_subset_right).trans
      (by rw [measure_mono_null (image_mono inter_subset_left) hA0, mul_zero]))
  have hfin : μHE[d] (ψ '' Y) < ∞ := by
    calc μHE[d] (ψ '' Y) ≤ μHE[d] (⋃ x ∈ t, ψ '' (Y ∩ (U x ∩ ball x 1))) := by
          rw [← image_iUnion₂]
          exact measure_mono (image_mono (hcov Y subset_rfl))
      _ ≤ ∑ x ∈ t, μHE[d] (ψ '' (Y ∩ (U x ∩ ball x 1))) := measure_biUnion_finset_le _ _
      _ < ∞ := by
          refine ENNReal.sum_lt_top.2 fun x hx => ?_
          refine (hup x hx _ inter_subset_right).trans_lt
            (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ?_)
          exact (measure_mono (inter_subset_right.trans inter_subset_right)).trans_lt
            measure_ball_lt_top
  have : IsFiniteMeasure ν := ⟨by rw [hνapply, univ_inter]; exact hfin⟩
  -- the density `J = dν/dLᵈ⌞Y`
  set J : Euclid d → ℝ≥0∞ := ν.rnDeriv (volume.restrict Y)
  have hνJ : ν = (volume.restrict Y).withDensity J := by
    have h := Measure.haveLebesgueDecomposition_add ν (volume.restrict Y)
    rwa [Measure.singularPart_eq_zero_of_ac hνac, zero_add] at h
  have hJm : Measurable J := Measure.measurable_rnDeriv _ _
  have hJfin : ∀ᵐ y ∂(volume.restrict Y), J y < ∞ := Measure.rnDeriv_lt_top _ _
  -- `ψ` restricted to `Y` is a measurable embedding carrying `ν` to `Hᵈ⌞ψ(Y)`
  have hmapY : Measure.map (Y.domRestrict ψ) νY = μHE[d].restrict (ψ '' Y) := by
    rw [hνYdef, he.map_comap, range_domRestrict]
  -- the area formula `∫_{ψ(Y)} g dHᵈ = ∫_Y J (g ∘ ψ) dLᵈ`, for arbitrary `g`
  have harea : ∀ g : Euclid P → ℝ,
      ∫ x in ψ '' Y, g x ∂μHE[d] = ∫ y in Y, (J y).toReal * g (ψ y) := by
    intro g
    calc ∫ x in ψ '' Y, g x ∂μHE[d] = ∫ x, g x ∂(Measure.map (Y.domRestrict ψ) νY) := by
          rw [hmapY]
      _ = ∫ y : Y, g (ψ y) ∂νY := he.integral_map g
      _ = ∫ y, g (ψ y) ∂ν :=
          ((MeasurableEmbedding.subtype_coe hY).integral_map (fun y => g (ψ y))).symm
      _ = ∫ y, g (ψ y) ∂((volume.restrict Y).withDensity J) := by rw [← hνJ]
      _ = ∫ y in Y, (J y).toReal * g (ψ y) :=
          integral_withDensity_eq_integral_toReal_smul hJm hJfin _
  -- `J (w ∘ ψ)` is integrable on `Y`
  have hJw : IntegrableOn (fun y => (J y).toReal * w (ψ y)) Y := by
    have h1 : Integrable w (Measure.map (Y.domRestrict ψ) νY) := by rw [hmapY]; exact hw
    have h2 : Integrable (fun y => w (ψ y)) ν :=
      (MeasurableEmbedding.subtype_coe hY).integrable_map_iff.2 (he.integrable_map_iff.1 h1)
    rw [hνJ] at h2
    exact (integrable_withDensity_iff_integrable_smul' hJm hJfin).1 h2
  -- the tangency of `W` pulls back to `Lᵈ`-a.e. `y ∈ Y`
  have htan : ∀ᵐ y ∂(volume.restrict Y),
      W (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) := by
    have h1 : ∀ᵐ x ∂(Measure.map (Y.domRestrict ψ) νY), ∀ y ∈ Y, ψ y = x →
        W x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) := by
      rw [hmapY]; exact hWt
    have h2 := he.ae_map_iff.1 h1
    have h3 : ∀ᵐ y ∂ν, y ∈ Y →
        W (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid d →ₗ[ℝ] Euclid P) := by
      rw [hνdef, (MeasurableEmbedding.subtype_coe hY).ae_map_iff]
      filter_upwards [h2] with y hy _
      exact hy y y.2 rfl
    filter_upwards [hYν.ae_le h3, ae_restrict_mem hY] with y hy hyY
    exact hy hyY
  -- a continuous left inverse `R` of `Dψ` on `V`, with `‖R‖ ≤ M` on the compact `C`
  obtain ⟨R, hRc, hRinv⟩ := Submission.dor_lmbsf_pwl_immersion_left_inverse P d V ψ hV hψ hDψ
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hRc.mono hCV)
  -- the chart field `E = R (W ∘ ψ)`: a.e.-strongly measurable on `Y`, with `|E| ≤ M c'` there
  set E : Euclid d → Euclid d := fun y => R y (W (ψ y)) with hEdef
  have hEm : AEStronglyMeasurable E (volume.restrict Y) := by
    have hR : AEStronglyMeasurable R (volume.restrict Y) :=
      (hRc.mono hYV).aestronglyMeasurable hY
    have hWψ : AEStronglyMeasurable (fun y => W (ψ y)) (volume.restrict Y) :=
      (hWm.comp_aemeasurable (hcont.aemeasurable hY)).aestronglyMeasurable
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Euclid P) (F := Euclid d)).continuous
      |>.comp_aestronglyMeasurable (hR.prodMk hWψ)
  have hEb : ∀ᵐ y ∂(volume.restrict Y), ‖E y‖ ≤ M * c' := by
    filter_upwards [ae_restrict_mem hY] with y hy
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y (hYC hy))
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hM y (hYC hy)) (hWb _) (norm_nonneg _) hM0)
  -- `Φ = 1_Y J (w ∘ ψ) E`
  set Φ : Euclid d → Euclid d := Y.indicator (fun y => ((J y).toReal * w (ψ y)) • E y)
    with hΦdef
  have hΦi : Integrable Φ := by
    rw [hΦdef, integrable_indicator_iff hY]
    exact hJw.smul_bdd (M * c') hEm hEb
  refine ⟨Φ, hΦi, fun y hy => by simp [hΦdef, indicator_of_notMem hy], ?_⟩
  intro β α hβα
  rw [harea]
  have hcompl : ∀ y, y ∉ Y → α y (Φ y) = 0 := fun y hy => by
    simp [hΦdef, indicator_of_notMem hy]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
    (f := fun y => α y (Φ y)) hcompl]
  refine setIntegral_congr_ae hY ?_
  -- for a.e. `y ∈ Y`, `W(ψ(y)) = Dψ(y) z` gives `E(y) = R(y) Dψ(y) z = z`, so
  -- `J w(ψ(y)) β(ψ(y))[W(ψ(y))] = J w(ψ(y)) β(ψ(y))[Dψ(y) E(y)] = α(y)[Φ(y)]`
  filter_upwards [ae_restrict_iff' hY |>.1 htan] with y hyt hyY
  obtain ⟨z, hz⟩ := hyt hyY
  have hz' : fderiv ℝ ψ y z = W (ψ y) := hz
  have hEz : E y = z := by
    have := congrArg (fun T : Euclid d →L[ℝ] Euclid d => T z) (hRinv y (hYV hyY))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [hEdef]
    simp only
    rw [← hz', this]
  have hE : fderiv ℝ ψ y (E y) = W (ψ y) := by rw [hEz, hz']
  rw [hΦdef, indicator_of_mem hyY, map_smul, ← hβα y hyY, ContinuousLinearMap.comp_apply, hE,
    smul_eq_mul]
  ring

/-- **Weak limit of the cut-off gradients on one chart piece.**  Let
`γ(s) = min 1 (max 0 ((b - s) / (b - a)))`, with `γ'(s) = -(b - a)⁻¹` for `a < s < b` and
`γ'(s) = 0` otherwise.  Localize `h_k ∘ ψ` and `γ ∘ f ∘ ψ` near `C` to uniformly Lipschitz
`u_k → u` on `ℝⁿ⁺¹`, and use the area formula to write the pairings over `ψ(Y)` as `∫ α[Φ]`, for
one integrable chart field `Φ` vanishing off `Y`.  By the chain rule `Dh_k(ψ y) ∘ Dψ(y) = Du_k(y)`
on `Y`, so the left side is `∫ Du_k[Φ]`.  Since `⟨G(ψ y), Dψ(y)·⟩ = DF(y)` and `f ∘ ψ = F` on
`Y`, the right side is `∫ γ'(F) DF[Φ]`.  This is `∫ Du[Φ]`, as `Du = γ'(F) DF` a.e. on `Y` and
`Φ = 0` off `Y`.  Finally `∫ Du_k[Φ] → ∫ Du[Φ]` by weak-* convergence of the derivatives. -/
theorem Submission.dor_lmbsf_piece_weak_limit : ∀ (P n : ℕ) (V C Y : Set (Euclid (n + 1))) (ψ : Euclid (n + 1) → Euclid P) (F : Euclid (n + 1) → ℝ) (f : Euclid P → ℝ) (G : Euclid P → Euclid P) (L : NNReal) (a b c c' : ℝ) (hs : ℕ → Euclid P → ℝ) (w : Euclid P → ℝ) (W : Euclid P → Euclid P), IsOpen V → ContDiffOn ℝ 1 ψ V → InjOn ψ V → (∀ y ∈ V, Injective (fderiv ℝ ψ y)) → IsCompact C → C ⊆ V → MeasurableSet Y → Y ⊆ C → ContDiff ℝ 1 F → (∀ y ∈ Y, f (ψ y) = F y) → (∀ y ∈ Y, G (ψ y) ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P) ∧ ∀ e : Euclid (n + 1), inner ℝ (G (ψ y)) (fderiv ℝ ψ y e) = fderiv ℝ F y e) → Measurable G → LipschitzWith L f → a < b → (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop → IntegrableOn w (ψ '' Y) μHE[n + 1] → Measurable W → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[n + 1].restrict (ψ '' Y)), ∀ y ∈ Y, ψ y = x → W x ∈ LinearMap.range (fderiv ℝ ψ y : Euclid (n + 1) →ₗ[ℝ] Euclid P)) → Tendsto (fun k => ∫ x in ψ '' Y, w x * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in ψ '' Y ∩ {x | a < f x ∧ f x < b}, w x * (-(b - a)⁻¹ * inner ℝ (G x) (W x)) ∂μHE[n + 1])) := by
  intro P n V C Y ψ F f G L a b c c' hs w W hV hψ hψi hDψ hC hCV hY hYC hF hfF hGF _ hf hab hhs
    hhs' hU hw hW hW' hWt
  -- globally `K`-Lipschitz `u_k → u` with `u_k = h_k ∘ ψ` and `u = γ ∘ f ∘ ψ` on an open `O ⊇ C`
  obtain ⟨O, K, us, u, hO, hCO, hus, hu, hUu, husO, huO⟩ :=
    Submission.dor_lmbsf_pwl_chart_cutoff_localize P (n + 1) V C ψ hs
      (fun x => min 1 (max 0 ((b - f x) / (b - a)))) c hV hψ hC hCV hhs hhs' hU
  -- one integrable chart field `Φ`, vanishing off `Y`, with `∫_{ψ(Y)} w β[W] = ∫ α[Φ]` whenever
  -- `β(ψ y) ∘ Dψ(y) = α(y)` on `Y`
  obtain ⟨Φ, hΦ, hΦY, hΦpair⟩ :=
    Submission.dor_lmbsf_pwl_chart_pairing_transfer P (n + 1) V C Y ψ w W c' hV hψ hψi hDψ hC
      hCV hY hYC hw hW hW' hWt
  -- left side: `u_k = h_k ∘ ψ` near `y ∈ Y`, so `Dh_k(ψ y) ∘ Dψ(y) = Du_k(y)`
  have hlhs : ∀ k, ∫ x in ψ '' Y, w x * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]
      = ∫ y, fderiv ℝ (us k) y (Φ y) := by
    intro k
    refine hΦpair (fderiv ℝ (hs k)) (fderiv ℝ (us k)) fun y hy => ?_
    have hloc : us k =ᶠ[𝓝 y] hs k ∘ ψ :=
      eventually_of_mem (hO.mem_nhds (hCO (hYC hy))) fun z hz => husO k z hz
    have hψy : DifferentiableAt ℝ ψ y :=
      (hψ.contDiffAt (hV.mem_nhds (hCV (hYC hy)))).differentiableAt one_ne_zero
    rw [hloc.fderiv_eq, fderiv_comp y ((hhs k).differentiable one_ne_zero (ψ y)) hψy]
  -- right side: `γ'(f) ⟨G, ·⟩` pulls back along `ψ` to `γ'(F) DF` on `Y`
  have hS : MeasurableSet {x : Euclid P | a < f x ∧ f x < b} :=
    hf.continuous.measurable (measurableSet_Ioo (a := a) (b := b))
  have hrhs : ∫ x in ψ '' Y ∩ {x | a < f x ∧ f x < b},
        w x * (-(b - a)⁻¹ * inner ℝ (G x) (W x)) ∂μHE[n + 1]
      = ∫ y, ((if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) (Φ y) := by
    rw [← setIntegral_indicator hS]
    refine (integral_congr_ae (ae_of_all _ fun x => ?_)).trans
      (hΦpair (fun x => (if a < f x ∧ f x < b then -(b - a)⁻¹ else 0) • innerSL ℝ (G x))
        (fun y => (if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) fun y hy => ?_)
    · by_cases hx : a < f x ∧ f x < b
      · simp [hx, innerSL_apply_apply]
      · simp [hx]
    · have hpull : (innerSL ℝ (G (ψ y))).comp (fderiv ℝ ψ y) = fderiv ℝ F y :=
        ContinuousLinearMap.ext fun e => (hGF y hy).2 e
      simp only [ContinuousLinearMap.smul_comp, hfF y hy, hpull]
  -- `Du = γ'(F) DF` a.e. on `Y` and `Φ = 0` off `Y`
  have hcut := Submission.dor_lmbsf_pwl_fderiv_cutoff_comp_ae
    Submission.dor_lmbsf_density_directions (n + 1) Y F u K a b hY
    (hF.differentiable one_ne_zero) hu hab fun y hy => by
      simpa only [hfF y hy] using huO y (hCO (hYC hy))
  have hlim : ∫ y, ((if a < F y ∧ F y < b then -(b - a)⁻¹ else 0) • fderiv ℝ F y) (Φ y)
      = ∫ y, fderiv ℝ u y (Φ y) := by
    refine integral_congr_ae ?_
    filter_upwards [hcut] with y hy
    by_cases hyY : y ∈ Y
    · rw [hy hyY]
    · rw [hΦY y hyY, map_zero, map_zero]
  -- weak-* convergence `∫ Du_k[Φ] → ∫ Du[Φ]`
  rw [hrhs, hlim]
  exact (Submission.dor_lmbsf_pwl_fderiv_weak_integrable (n + 1) K us u Φ hus hUu hΦ).congr
    fun k => (hlhs k).symm

/-- **Tangential gradient of a Lipschitz function on an integer multiplicity triple** (Simon
Ch. 3, Remark 1.3, Remark 1.5(1), 2.1 and 2.8–2.10(2); Ch. 6, 4.1 and the reduction to one piece
in the proof of 4.5(2)).  `chart_pieces` decomposes `M = RT.carrier` up to an `H^{n+1}`-null set
into disjoint Borel chart pieces `P_j = ψ_j(Y_j)` and gives the Borel field `g` with `|g| ≤ L`,
`g = 0` off `⋃_j P_j` and `g(ψ_j y) ∈ range Dψ_j(y) = T_{ψ_j y}M` (uniqueness of approximate
tangent planes, Ch. 3, 1.5(1)), so (G1), (G2).  The piece results `piece_coarea`,
`piece_slice_tangent` and `piece_weak_limit` hold on every `P_j`, and the three gluing lemmas sum
them over `j`: (G3) by `coarea_gluing`; (G4a) since `M_t ⊆ ⋃_j (P_j)_t`, a countable union of
countably `n`-rectifiable sets; (G4b) by `tangent_gluing`, each piece slice having finite `Hⁿ`
measure as a subset of `M_t ∩ ψ_j(C_j)`, `ψ_j(C_j)` compact in `U`; (G5) by `weak_limit_gluing`
with weight `θ` and dominating function `c c' θ 1_K` (integrable since `θ` is locally
integrable). -/
theorem Submission.dor_lmbsf_tangential_gradient : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → LipschitzWith L f → ∃ g : Euclid P → Euclid P, Measurable g ∧ (∀ x, ‖g x‖ ≤ L) ∧ (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), g x ∈ approxTangentPlane (n + 1) RT.carrier x) ∧ (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in RT.carrier, ‖g x‖ₑ * φ x ∂μHE[n + 1]) ∧ (∀ t, CountablyRectifiable n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) ∧ (∀ t, (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})), HasApproximateTangentSpaceAt n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) RT.carrier x ⊓ (ℝ ∙ g x)ᗮ)) ∧ (∀ (a b : ℝ), a < b → ∀ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop → ∀ (W : Euclid P → Euclid P) (K : Set (Euclid P)) (c' : ℝ), Measurable W → IsCompact K → K ⊆ U → (∀ x, x ∉ K → W x = 0) → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), W x ∈ approxTangentPlane (n + 1) RT.carrier x) → Tendsto (fun k => ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)) ∂μHE[n + 1]))) := by
  intro hTL P n U RT f L hU hf
  have hMm : MeasurableSet RT.carrier := RT.measurableSet_carrier
  have hfm : Measurable f := hf.continuous.measurable
  have hθm : Measurable fun x => (RT.mult x : ℝ) := measurable_from_nat.comp RT.measurable_mult
  -- Step 0(b): `θ ≥ 1` on `M` is locally integrable, so `M` is locally `H^{n+1}`-finite
  have hθint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (fun x => (RT.mult x : ℝ)) (RT.carrier ∩ K) μHE[n + 1] := by
    intro K hK hKU
    have h := integrable_toReal_of_lintegral_ne_top
      (μ := μHE[n + 1].restrict (RT.carrier ∩ K)) (f := fun x => (RT.mult x : ℝ≥0∞))
      (measurable_from_nat.comp RT.measurable_mult).aemeasurable
      (RT.locallyIntegrable_mult K hK hKU)
    simp only [ENNReal.toReal_natCast] at h
    exact h
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      μHE[n + 1] (RT.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (RT.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (hMm.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.mpr (RT.mult_pos x hx.1)
  -- Step 0(c): `T_xM` is the approximate tangent space of `M` at `x` whenever one exists
  have hTM : ∀ x (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt (n + 1) RT.carrier x Q →
        approxTangentPlane (n + 1) RT.carrier x = Q := by
    intro x Q hQ
    have hex : ∃ Q, HasApproximateTangentSpaceAt (n + 1) RT.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left hex]
    exact hex.choose_spec.unique hQ
  -- Step 1: the chart pieces `P_j = ψ_j(Y_j)` and the field `g`
  obtain ⟨V, C, Y, ψ, F, g, hV, hCY, hYM, hdisj, hnull, hfT, hgm, hgL, hg0, hgT⟩ :=
    Submission.dor_lmbsf_lipschitz_chart_pieces hTL P n U RT.carrier f L hU hMm RT.carrier_subset
      RT.rectifiable hMfin hf
  have hTψ : ∀ j, ∀ y ∈ Y j, approxTangentPlane (n + 1) RT.carrier (ψ j y) =
      LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) := fun j y hy =>
    hTM _ _ (hfT j y hy).2
  -- `P_j` is Borel (Lusin–Souslin), and `P_j ⊆ ψ_j(C_j)`, a compact subset of `U`
  have hPm : ∀ j, MeasurableSet (ψ j '' Y j) := fun j =>
    (hCY j).2.2.1.image_of_continuousOn_injOn
      ((hV j).2.1.continuousOn.mono ((hCY j).2.2.2.1.trans (hCY j).2.1))
      ((hV j).2.2.1.mono ((hCY j).2.2.2.1.trans (hCY j).2.1))
  have hPC : ∀ j, IsCompact (ψ j '' C j) := fun j =>
    (hCY j).1.image_of_continuousOn ((hV j).2.1.continuousOn.mono (hCY j).2.1)
  have hPCU : ∀ j, ψ j '' C j ⊆ U := fun j => (image_mono (hCY j).2.1).trans (hV j).2.2.2.2
  have hPPC : ∀ j, ψ j '' Y j ⊆ ψ j '' C j := fun j => image_mono (hCY j).2.2.2.1
  -- Step 2: (G2), everywhere on `ℝ^P`
  have hG2 : ∀ x, g x ∈ approxTangentPlane (n + 1) RT.carrier x := by
    intro x
    by_cases hx : ∃ j, x ∈ ψ j '' Y j
    · obtain ⟨j, y, hy, rfl⟩ := hx
      rw [hTψ j y hy]
      exact (hgT j y hy).1
    · push Not at hx
      rw [hg0 x hx]
      exact Submodule.zero_mem _
  -- Step 3: `M_t` is the disjoint union of the Borel piece slices `(P_j)_t`
  have hgne : MeasurableSet {x | g x ≠ 0} := (hgm (measurableSet_singleton 0)).compl
  have hft : ∀ t : ℝ, MeasurableSet (f ⁻¹' {t}) := fun t => hfm (measurableSet_singleton t)
  have hcover : ∀ t, RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ⊆
      ⋃ j, ψ j '' Y j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} := by
    rintro t x ⟨⟨-, hgx⟩, hfx⟩
    by_contra hx
    simp only [mem_iUnion, not_exists] at hx
    exact hgx (hg0 x fun j hj => hx j ⟨⟨hj, hgx⟩, hfx⟩)
  have hsub : ∀ t j, ψ j '' Y j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ⊆
      RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} := fun t j =>
    inter_subset_inter_left _ (inter_subset_inter_left _ (hYM j))
  -- the piece results
  have hcoarea := fun j => Submission.dor_lmbsf_piece_coarea P n (V j) (C j) (Y j) (ψ j) (F j) f g
    (hV j).1 (hV j).2.1 (hV j).2.2.1 (hV j).2.2.2.1 (hCY j).1 (hCY j).2.1 (hCY j).2.2.1
    (hCY j).2.2.2.1 (hCY j).2.2.2.2 (fun y hy => (hfT j y hy).1) (hgT j) hgm
  have hslice := fun j => Submission.dor_lmbsf_piece_slice_approxTangent hTL P n (V j) (C j) (Y j)
    (ψ j) (F j) f g (hV j).1 (hV j).2.1 (hV j).2.2.1 (hV j).2.2.2.1 (hCY j).1 (hCY j).2.1
    (hCY j).2.2.1 (hCY j).2.2.2.1 (hCY j).2.2.2.2 (fun y hy => (hfT j y hy).1) (hgT j)
  refine ⟨g, hgm, hgL, Eventually.of_forall hG2, fun φ hφ => ?_, fun t => ?_, fun t hfin => ?_,
    ?_⟩
  · -- Step 4: (G3), summing the piece co-area formulas
    exact Submission.dor_lmbsf_tg_coarea_gluing P μHE[n + 1] μHE[n] RT.carrier
      (fun j => ψ j '' Y j) g f φ hMm hPm hdisj hYM hgm hg0 hfm fun j => hcoarea j φ hφ
  · -- Step 5: (G4a), a countable union of countably `n`-rectifiable piece slices
    exact (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun j => ψ j '' Y j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) fun j => (hslice j t).1).mono
        (hcover t)
  · -- Step 6: (G4b), gluing the approximate tangent spaces of the piece slices by (TL)
    refine Submission.dor_lmbsf_tg_tangent_gluing hTL P n U
      (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) (fun j => ψ j '' Y j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})
      (fun x => approxTangentPlane (n + 1) RT.carrier x ⊓ (ℝ ∙ g x)ᗮ) hU
      ((hMm.inter hgne).inter (hft t))
      (inter_subset_left.trans (inter_subset_left.trans RT.carrier_subset)) hfin
      (fun j => ((hPm j).inter hgne).inter (hft t)) (hsub t) (hcover t) fun j => ?_
    -- the piece slice lies in `M_t ∩ ψ_j(C_j)`, so it has finite `Hⁿ` measure
    have hSfin : μHE[n] (ψ j '' Y j ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) ≠ ∞ :=
      ne_top_of_le_ne_top (hfin _ (hPC j) (hPCU j)) (measure_mono (subset_inter (hsub t j)
        (inter_subset_left.trans (inter_subset_left.trans (hPPC j)))))
    filter_upwards [(hslice j t).2 hSfin, ae_restrict_mem (((hPm j).inter hgne).inter (hft t))]
      with x hx hxS
    obtain ⟨y, hy, rfl⟩ := hxS.1.1
    rw [hTψ j y hy]
    exact hx y hy rfl
  · -- Step 7: (G5), dominated convergence over the pieces with weight `θ`
    intro a b hab hs c hs1 hsc hsu W K c' hWm hK hKU hWK hWc hWT
    have hc : 0 ≤ c := (norm_nonneg _).trans (hsc 0 0)
    have hc' : 0 ≤ c' := (norm_nonneg _).trans (hWc 0)
    -- `κ θ 1_K` is integrable on `M` for every constant `κ`
    have hdom : ∀ κ : ℝ, IntegrableOn (K.indicator fun x => κ * (RT.mult x : ℝ)) RT.carrier
        μHE[n + 1] := by
      intro κ
      rw [IntegrableOn, integrable_indicator_iff hK.measurableSet, IntegrableOn,
        Measure.restrict_restrict hK.measurableSet, inter_comm]
      exact (hθint K hK hKU).const_mul κ
    refine Submission.dor_lmbsf_tg_weak_limit_gluing P μHE[n + 1] RT.carrier
      {x | a < f x ∧ f x < b} (fun j => ψ j '' Y j)
      (fun k x => (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x))
      (fun x => (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)))
      (K.indicator fun x => c * c' * (RT.mult x : ℝ)) hMm (hfm measurableSet_Ioo) hPm hdisj hYM
      hnull (hdom (c * c')) (fun k => ?_) (fun k => Eventually.of_forall fun x => ?_) ?_ fun j => ?_
    · -- the integrands are measurable
      exact hθm.aestronglyMeasurable.mul
        (Continuous.comp_aestronglyMeasurable₂
          (g := fun (Λ : Euclid P →L[ℝ] ℝ) (v : Euclid P) => Λ v)
          isBoundedBilinearMap_apply.continuous
          ((hs1 k).continuous_fderiv one_ne_zero).aestronglyMeasurable hWm.aestronglyMeasurable)
    · -- `|θ Dh_k[W]| ≤ c c' θ 1_K`
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm (c * c')]
        exact mul_le_mul_of_nonneg_left (((fderiv ℝ (hs k) x).le_opNorm (W x)).trans
          (mul_le_mul (hsc k x) (hWc x) (norm_nonneg _) hc)) (Nat.cast_nonneg _)
      · rw [indicator_of_notMem hxK, hWK x hxK, map_zero, mul_zero, norm_zero]
    · -- `|θ (-(b - a)⁻¹ ⟨g, W⟩)| ≤ (b - a)⁻¹ L c' θ 1_K`, so the limit integrand is integrable
      refine Integrable.mono' ((hdom ((b - a)⁻¹ * (L * c'))).mono_set inter_subset_left)
        (hθm.aestronglyMeasurable.mul (aestronglyMeasurable_const.mul
          (continuous_inner.comp_aestronglyMeasurable₂ hgm.aestronglyMeasurable
            hWm.aestronglyMeasurable))) (Eventually.of_forall fun x => ?_)
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, norm_mul, norm_mul, norm_neg, Real.norm_natCast, norm_inv,
          Real.norm_of_nonneg (sub_pos.2 hab).le, mul_comm _ (RT.mult x : ℝ)]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
          (inv_nonneg.2 (sub_pos.2 hab).le)) (Nat.cast_nonneg _)
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hgL x) (hWc x) (norm_nonneg _) L.coe_nonneg)
      · rw [indicator_of_notMem hxK, hWK x hxK, inner_zero_right, mul_zero, mul_zero, norm_zero]
    · -- `piece_weak_limit` on `P_j`, with `θ` integrable on `P_j ⊆ M ∩ ψ_j(C_j)`
      have hθj : IntegrableOn (fun x => (RT.mult x : ℝ)) (ψ j '' Y j) μHE[n + 1] :=
        (hθint _ (hPC j) (hPCU j)).mono_set (subset_inter (hYM j) (hPPC j))
      have hWj : ∀ᵐ x ∂(μHE[n + 1].restrict (ψ j '' Y j)), ∀ y ∈ Y j, ψ j y = x →
          W x ∈ LinearMap.range (fderiv ℝ (ψ j) y : Euclid (n + 1) →ₗ[ℝ] Euclid P) := by
        filter_upwards [ae_restrict_of_ae_restrict_of_subset (hYM j) hWT] with x hx
        rintro y hy rfl
        rw [← hTψ j y hy]
        exact hx
      exact Submission.dor_lmbsf_piece_weak_limit P n (V j) (C j) (Y j) (ψ j) (F j) f g L a b c c'
        hs (fun x => (RT.mult x : ℝ)) W (hV j).1 (hV j).2.1 (hV j).2.2.1 (hV j).2.2.2.1 (hCY j).1
        (hCY j).2.1 (hCY j).2.2.1 (hCY j).2.2.2.1 (hCY j).2.2.2.2 (fun y hy => (hfT j y hy).1)
        (hgT j) hgm hf hab hs1 hsc hsu hθj hWm hWc hWj
/-- Transfer of null sets to almost every slice (Simon 7.4.3, slicing step; co-area formula of
Ch. 2, 6.6 and slices of Ch. 6, 4.3): if the slice measures `ν_t` satisfy the co-area identity
`∫_ℝ ∫ φ dν_t dt = ∫ w φ dμ` for every Borel `φ ≥ 0`, then a property holding `μ`-a.e. holds
`ν_t`-a.e. for a.e. `t`.  With `Z ⊇ {¬p}` a Borel `μ`-null hull and `φ = 1_Z`, the right side
vanishes, so `ν_t(Z) = ∫ 1_Z dν_t = 0` for a.e. `t`. -/
theorem Submission.dor_lmbsf_si_coarea_ae_transfer : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (p : Euclid P → Prop), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → (∀ᵐ x ∂μ, p x) → ∀ᵐ t, ∀ᵐ x ∂(ν t), p x := by
  intro P μ ν w p hco hp
  -- a Borel `μ`-null hull `Z` of `{x | ¬p x}`
  set Z := toMeasurable μ {x | ¬p x} with hZ
  have hZm : MeasurableSet Z := measurableSet_toMeasurable _ _
  have hμZ : μ Z = 0 := by rw [hZ, measure_toMeasurable]; exact ae_iff.mp hp
  -- co-area identity for `φ = 1_Z`: `∫_ℝ ν_t(Z) dt = ∫ w 1_Z dμ = 0`
  obtain ⟨hae, heq⟩ := hco (Z.indicator 1) (measurable_one.indicator hZm)
  have hzero : ∫⁻ x, w x * Z.indicator 1 x ∂μ = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμZ] with x hx
    simp [indicator_of_notMem hx]
  rw [hzero, lintegral_eq_zero_iff' hae] at heq
  -- for a.e. `t`, `ν_t(Z) = 0`, so `ν_t`-a.e. `x` lies outside `Z ⊇ {¬p}`
  filter_upwards [heq] with t ht
  have hνZ : ν t Z = 0 := by
    rw [← lintegral_indicator_one hZm]; exact ht
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνZ] with x hx
  by_contra hpx
  exact hx (subset_toMeasurable μ {x | ¬p x} hpx)

/-- Orthonormal frame of `Q` adapted to a unit vector `ν ∈ Q` (Simon Ch. 6, 4.3, used for the
orientation of the slices in 7.4): if `dim Q = n + 1`, then `Q' = Q ∩ ν^⊥` has an orthonormal
basis `σ = (σ₁, …, σₙ)`, so that `(ν, σ₁, …, σₙ)` is an orthonormal basis of `Q`.  The dimension
count is `dim (ℝν) + dim (ν^⊥ ∩ Q) = dim Q`. -/
theorem Submission.dor_lmbsf_io_adapted_frame : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), Module.finrank ℝ Q = n + 1 → ν ∈ Q → ‖ν‖ = 1 → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Q ⊓ (ℝ ∙ ν)ᗮ ∧ Orthonormal ℝ (Fin.cons ν σ : Fin (n + 1) → Euclid P) ∧ (∀ i, σ i ∈ Q) ∧ ∀ i, inner ℝ ν (σ i) = 0 := by
  intro P n Q ν hQ hνQ hν
  set Q' : Submodule ℝ (Euclid P) := Q ⊓ (ℝ ∙ ν)ᗮ
  have hν0 : ν ≠ 0 := by
    intro h; rw [h, norm_zero] at hν; exact zero_ne_one hν
  have hle : (ℝ ∙ ν) ≤ Q := (Submodule.span_singleton_le_iff_mem ν Q).2 hνQ
  -- `dim Q' = n`
  have hdim : Module.finrank ℝ Q' = n := by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal hle
    rw [finrank_span_singleton hν0, hQ] at h1
    have : Q' = (ℝ ∙ ν)ᗮ ⊓ Q := inf_comm _ _
    rw [this]; omega
  -- `σ` is an orthonormal basis `b` of `Q'`, viewed in `ℝᴾ`
  let b : OrthonormalBasis (Fin n) ℝ Q' := (stdOrthonormalBasis ℝ Q').reindex (finCongr hdim)
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  have hσ : Orthonormal ℝ σ := b.orthonormal.comp_linearIsometry Q'.subtypeₗᵢ
  have hσmem : ∀ i, σ i ∈ Q' := fun i => (b i).2
  have hσspan : Submodule.span ℝ (Set.range σ) = Q' := by
    have hrange : Set.range σ = Q'.subtype '' Set.range b := by
      ext x; simp [σ]
    have htop : Submodule.span ℝ (Set.range b) = ⊤ := by simpa using b.toBasis.span_eq
    rw [hrange, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
  have hσQ : ∀ i, σ i ∈ Q := fun i => (hσmem i).1
  have hνσ : ∀ i, inner ℝ ν (σ i) = 0 := fun i =>
    (Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hσmem i).2
  refine ⟨σ, hσ, hσspan, ?_, hσQ, hνσ⟩
  -- `Fin.cons ν σ` is orthonormal: split both indices into `0` and successors
  rw [orthonormal_iff_ite] at hσ ⊢
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j
  · simp [hν]
  · simp [hνσ j', (Fin.succ_ne_zero j').symm]
  · simp [real_inner_comm, hνσ i', Fin.succ_ne_zero i']
  · simp [hσ i' j']
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

/-- Sign lemma for unit orientations (Simon 6.1.1; used for the slice orientation
`ξ ⌞ ∇^M f/|∇^M f|` of 6.4.3 in the slicing step of the proof of 7.4.3): if
`ζ = ±τ₁ ∧ ⋯ ∧ τₘ` is a unit orientation of `Q` and `ρ` is an orthonormal `m`-frame in `Q`, then
`ζ = ρ₁ ∧ ⋯ ∧ ρₘ` or `ζ = -ρ₁ ∧ ⋯ ∧ ρₘ`.  The change of frame `M = (⟨τᵢ, ρⱼ⟩)` satisfies
`Mᵀ M = I`, so `det M = ±1`, and `β(ρ) = det M · β(τ)` for every `m`-covector `β`. -/
theorem Submission.dor_lmbsf_io_orientation_frame_sign : ∀ (P m : ℕ) (ζ : MultiVector P m) (Q : Submodule ℝ (Euclid P)) (ρ : Fin m → Euclid P), IsUnitOrientationOf ζ Q → Orthonormal ℝ ρ → (∀ j, ρ j ∈ Q) → (∀ β : Covector (Euclid P) m, ζ β = β ρ) ∨ ∀ β : Covector (Euclid P) m, ζ β = -β ρ := by
  intro P m ζ Q ρ hζ hρ hρQ
  obtain ⟨τ, hτ, hspan, hsign⟩ := hζ
  set M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => inner ℝ (τ i) (ρ j) with hM
  have hρspan : ∀ j, ρ j ∈ Submodule.span ℝ (Set.range τ) := fun j => hspan ▸ hρQ j
  -- `β(ρ) = det M · β(τ)`
  have hdet : ∀ β : Covector (Euclid P) m, β ρ = M.det * β τ :=
    Submission.dgoj_covector_eq_det_mul_of_mem_span P m τ ρ hτ hρspan
  -- Parseval in `span τ`: `⟨x, y⟩ = ∑ᵢ ⟨τᵢ, x⟩ ⟨τᵢ, y⟩`
  have hparseval : ∀ x y : Euclid P, y ∈ Submodule.span ℝ (Set.range τ) →
      inner ℝ x y = ∑ i, inner ℝ (τ i) x * inner ℝ (τ i) y := by
    intro x y hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hy
    simp only [hτ.inner_right_fintype, inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [real_inner_comm, mul_comm]
  -- `M` is orthogonal, so `det M = ±1`
  have hMM : M.transpose * M = 1 := by
    ext j k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, hM, Matrix.of_apply]
    rw [← hparseval (ρ j) (ρ k) (hρspan k)]
    exact orthonormal_iff_ite.1 hρ j k
  have hdet2 : M.det * M.det = 1 := by
    have := congrArg Matrix.det hMM
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
  have hpm : M.det = 1 ∨ M.det = -1 := by
    have h0 : (M.det - 1) * (M.det + 1) = 0 := by linear_combination hdet2
    rcases mul_eq_zero.1 h0 with h | h
    · left; linarith
    · right; linarith
  rcases hsign with h | h <;> rcases hpm with hd | hd
  · left; intro β; rw [h, hdet, hd, one_mul]
  · right; intro β; rw [h, hdet, hd]; ring
  · right; intro β; rw [h, hdet, hd, one_mul]
  · left; intro β; rw [h, hdet, hd]; ring
/-- Step 3 of the orientation of a slice (Simon 6.4.3, `⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩`): if `ν` is a
unit vector orthogonal to `σ₀, …, σₙ₋₁`, then `(ν♭ ∧ α)(ν, σ₀, …, σₙ₋₁) = α(σ₀, …, σₙ₋₁)` for
every `n`-covector `α`, where `ν♭ ∧ α` is the alternatization of `w ↦ ⟨ν, w⟩ α`,
`(ν♭ ∧ α)(v) = ∑ᵢ (-1)ⁱ ⟨ν, vᵢ⟩ α(v₀, …, v̂ᵢ, …, vₙ)`.  The term `i = 0` is
`⟨ν, ν⟩ α(σ) = α(σ)`; every other term has a factor `⟨ν, σⱼ⟩ = 0`. -/
theorem Submission.dor_lmbsf_io_wedge_eval_cons : ∀ (P n : ℕ) (ν : Euclid P) (σ : Fin n → Euclid P) (α : Covector (Euclid P) n), ‖ν‖ = 1 → (∀ i, inner ℝ ν (σ i) = 0) → ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α) (Fin.cons ν σ : Fin (n + 1) → Euclid P) = α σ := by
  intro P n ν σ α hν hνσ
  -- expand at `v = (ν, σ₀, …, σₙ₋₁)` and split off the term `i = 0`
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ]
  -- `⟨ν, ν⟩ = ‖ν‖² = 1`, `v` without `v₀` is `σ`, and `⟨ν, vⱼ₊₁⟩ = ⟨ν, σⱼ⟩ = 0`
  simp [Fin.removeNth_zero, Fin.tail_cons, innerSL_apply_apply, hνσ, hν]

/-- Orientation of a slice (Simon Ch. 6, 4.3: `⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩`, and `ξ⌞ν` orients
`TₓM ∩ ν^⊥`): if the `(n+1)`-vector `ζ` orients `Q`, `ν ∈ Q` is a unit vector and
`⟨α, ζ'⟩ = ⟨ν♭ ∧ α, ζ⟩` for every `n`-covector `α`, then `ζ'` orients `Q ∩ ν^⊥`.  In an
orthonormal frame `(ν, σ)` of `Q` adapted to `ν`, `ζ` is `±` evaluation at `(ν, σ)` and
`(ν♭ ∧ α)(ν, σ) = α(σ)`, so `ζ'(α) = ±α(σ)`. -/
theorem Submission.dor_lmbsf_interior_product_orientation : ∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (ζ' : MultiVector P n) (Q : Submodule ℝ (Euclid P)) (ν : Euclid P), IsUnitOrientationOf ζ Q → ν ∈ Q → ‖ν‖ = 1 → (∀ α : Covector (Euclid P) n, ζ' α = ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α))) → IsUnitOrientationOf ζ' (Q ⊓ (ℝ ∙ ν)ᗮ) := by
  intro P n ζ ζ' Q ν hζ hνQ hν hζ'
  -- `dim Q = n + 1`, read off the orthonormal frame `τ` oriented by `ζ`
  have hdim : Module.finrank ℝ Q = n + 1 := by
    obtain ⟨τ, hτ, hτQ, -⟩ := hζ
    rw [← hτQ, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- an orthonormal frame `(ν, σ)` of `Q`, with `σ` an orthonormal basis of `Q ∩ ν^⊥`
  obtain ⟨σ, hσ, hσspan, hνσo, hσQ, hνσ⟩ :=
    Submission.dor_lmbsf_io_adapted_frame P n Q ν hdim hνQ hν
  have hνσQ : ∀ j, (Fin.cons ν σ : Fin (n + 1) → Euclid P) j ∈ Q := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hνQ
    · simpa using hσQ i
  -- `(ν♭ ∧ α)(ν, σ) = α(σ)`
  have hwedge : ∀ α : Covector (Euclid P) n,
      ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ ν).smulRight α)
        (Fin.cons ν σ : Fin (n + 1) → Euclid P) = α σ := fun α =>
    Submission.dor_lmbsf_io_wedge_eval_cons P n ν σ α hν hνσ
  -- `ζ` is `±` evaluation at `(ν, σ)`, so `ζ'` is `±` evaluation at `σ`
  refine ⟨σ, hσ, hσspan, ?_⟩
  rcases Submission.dor_lmbsf_io_orientation_frame_sign P (n + 1) ζ Q _ hζ hνσo hνσQ with h | h
  · exact Or.inl fun α => by rw [hζ' α, h, hwedge]
  · exact Or.inr fun α => by rw [hζ' α, h, hwedge]
/-- **Normalized mollifier** (step 2 of the smooth-to-`C¹` test reduction): for `r > 0` there is
a `C^∞` function `ρ ≥ 0` on `ℝⁿ` with compact support in `B_r(0)` and `∫ ρ = 1`.  Take the
`ContDiffBump` `B` centred at `0` with `rIn = r/2`, `rOut = r`, so `support B = B_r(0)`; its
integral `I` is positive since `B ≥ 0` and `volume (B_r(0)) > 0`, and `ρ = I⁻¹ B`.  (Mathlib's
`ContDiffBump.normed` is outside the import closure, so the normalization is done by hand.) -/
theorem Submission.dgcr_stc_exists_normalized_mollifier : ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ ρ : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball (0 : Euclid n) r := by
  intro n r hr
  -- the bump `B` with `rIn = r/2`, `rOut = r`
  let B : ContDiffBump (0 : Euclid n) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hBs : HasCompactSupport B := B.hasCompactSupport
  have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
  -- `I = ∫ B > 0`: `B ≥ 0` and `support B = B_r(0)` has positive measure
  have hI : 0 < ∫ x, B x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
    exact measure_ball_pos volume 0 hr
  refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
    fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
  · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
  · exact (support_mul_subset_right _ _).trans B.support_eq.subset
/-- **Mollification preserves the Lipschitz constant** (step 4 of the Lipschitz smoothing): if
`ψ ≥ 0` is continuous with compact support and `∫ ψ = 1`, and `g` is `K`-Lipschitz, then
`G x = ∫ ψ(y) g(x - y) dy` is `K`-Lipschitz.  Indeed `G x - G x'` is the integral of
`ψ(y) (g(x - y) - g(x' - y))`, whose absolute value is at most `ψ(y) K ‖x - x'‖`, and
`∫ ψ = 1`. -/
theorem Submission.cmcs_ls_mollify_lipschitz : ∀ (P : ℕ) (ψ g : Euclid P → ℝ) (K : NNReal), Continuous ψ → HasCompactSupport ψ → (∀ x, 0 ≤ ψ x) → ∫ x, ψ x = 1 → LipschitzWith K g → LipschitzWith K (fun x => ∫ y, ψ y * g (x - y)) := by
  intro P ψ g K hψc hψs hψ0 hψ1 hg
  -- step 1: `y ↦ ψ y * g (x - y)` is continuous with support in `support ψ`, hence integrable
  have hint : ∀ x : Euclid P, Integrable (fun y => ψ y * g (x - y)) := fun x =>
    (hψc.mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψs.mul_right
  -- step 5: it suffices to show `dist (G x) (G x') ≤ K * dist x x'`
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  -- step 2: `G x - G x'` is a single integral
  rw [Real.dist_eq, ← integral_sub (hint x) (hint x'), ← Real.norm_eq_abs]
  calc ‖∫ y, (ψ y * g (x - y) - ψ y * g (x' - y))‖
      ≤ ∫ y, ψ y * (K * dist x x') := by
        -- step 4: integrate the pointwise bound of step 3 against the integrable majorant
        refine norm_integral_le_of_norm_le
          ((hψc.integrable_of_hasCompactSupport (μ := volume) hψs).mul_const _)
          (Eventually.of_forall fun y => ?_)
        -- step 3: `|ψ y (g (x - y) - g (x' - y))| = ψ y dist (g (x - y)) (g (x' - y))`
        -- `≤ ψ y (K dist (x - y) (x' - y)) = ψ y (K dist x x')`
        rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψ0 y), ← Real.dist_eq,
          ← dist_sub_right x x' y]
        exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (hψ0 y)
    _ = K * dist x x' := by rw [integral_mul_const, hψ1, one_mul]

/-- **Smoothing of Lipschitz functions** (Simon Ch. 6, 4.8–4.9: use `f^{(σ)}` in place of a
Lipschitz `f`): a `K`-Lipschitz `g` on `ℝᴾ` and `σ > 0` give a `C^∞` function `g'` with
`‖Dg'‖ ≤ K`, `|g' − g| ≤ Kσ`, and `g'(x) = c` whenever `g ≡ c` on `B_σ(x)`.  Take the normalized
mollifier `ψ` (`support ψ ⊆ B_σ(0)`) and `g' = ψ ⋆ g`, `g'(x) = ∫ ψ(y) g(x − y) dy`: it is `C^∞`
(`ψ` is smooth with compact support, `g` is continuous) and `K`-Lipschitz, so `‖Dg'‖ ≤ K`.  The
last two claims are `dist_convolution_le` on `B_σ(x)`, with `ε = Kσ`, `z₀ = g(x)` and with
`ε = 0`, `z₀ = c`.  (`ContDiffBump.normed` and its convolution lemmas are outside the import
closure.) -/
theorem Submission.cmcs_lipschitz_smoothing : ∀ (P : ℕ) (g : Euclid P → ℝ) (K : NNReal) (σ : ℝ), LipschitzWith K g → 0 < σ → ∃ g' : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g' ∧ (∀ x, ‖fderiv ℝ g' x‖ ≤ K) ∧ (∀ x, |g' x - g x| ≤ K * σ) ∧ ∀ (x : Euclid P) (c : ℝ), (∀ y ∈ ball x σ, g y = c) → g' x = c := by
  intro P g K σ hg hσ
  obtain ⟨ψ, hψd, hψs, hψ0, hψ1, hψb⟩ := Submission.dgcr_stc_exists_normalized_mollifier P σ hσ
  -- `g' = ψ ⋆ g`
  have hconv : (fun x => ∫ y, ψ y * g (x - y)) =
      convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  refine ⟨fun x => ∫ y, ψ y * g (x - y), ?_, fun x => ?_, fun x => ?_, fun x c hc => ?_⟩
  · rw [hconv]
    exact hψs.contDiff_convolution_left _ hψd hg.continuous.locallyIntegrable
  · exact norm_fderiv_le_of_lipschitz ℝ
      (Submission.cmcs_ls_mollify_lipschitz P ψ g K hψd.continuous hψs hψ0 hψ1 hg)
  · -- `dist (g y) (g x) ≤ K ‖y − x‖ ≤ Kσ` on `B_σ(x)`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := g x)
      (mul_nonneg K.coe_nonneg hσ.le) hψb hψ0 hψ1 hg.continuous.aestronglyMeasurable
      (fun y hy => (hg.dist_le_mul y x).trans
        (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.coe_nonneg))
    rwa [← hconv, Real.dist_eq] at h
  · -- `g ≡ c` on `B_σ(x)`, so `dist (g' x) c ≤ 0`
    have h := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := c) le_rfl hψb hψ0 hψ1
      hg.continuous.aestronglyMeasurable (fun y hy => by rw [hc y hy, dist_self])
    rw [← hconv] at h
    exact dist_le_zero.1 h

/-- **Smoothing the Lipschitz cut-off** (step 1 of the Lipschitz Leibniz rule): for an
`L`-Lipschitz `f` on `ℝᴾ` and `a < b`, the cut-off `h = γ_{a,b} ∘ f`,
`h(x) = min{1, max{0, (b − f(x))/(b − a)}}`, is a uniform limit of `C^∞` functions `h_k` with
`‖Dh_k‖ ≤ c` and `|h_k| ≤ 2`.  The clamp `γ_{a,b}` is `(b − a)⁻¹`-Lipschitz, so `h` is
`K`-Lipschitz with `K = (b − a)⁻¹L`, and `|h| ≤ 1`.  `cmcs_lipschitz_smoothing` with
`σ_k = 1/((K + 1)(k + 1))` gives `C^∞` functions `h_k` with `‖Dh_k‖ ≤ K` and
`|h_k − h| ≤ Kσ_k ≤ 1/(k + 1)`; take `c = K`. -/
theorem Submission.dor_lmbsf_ll_cutoff_smooth_approx : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (a b : ℝ), LipschitzWith L f → a < b → ∃ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ (⊤ : ℕ∞) (hs k)) ∧ (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) ∧ (∀ k x, |hs k x| ≤ 2) ∧ TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop := by
  intro P f L a b hf hab
  have hba : 0 < b - a := sub_pos.mpr hab
  set h : Euclid P → ℝ := fun x => min 1 (max 0 ((b - f x) / (b - a))) with hh_def
  -- step 1: the clamp `γ_{a,b}` is `(b - a)⁻¹`-Lipschitz
  have hγ : LipschitzWith (Real.toNNReal (b - a)⁻¹)
      (fun s : ℝ => min 1 (max 0 ((b - s) / (b - a)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr hba.le)]
    simp only [Real.dist_eq]
    calc |min 1 (max 0 ((b - s) / (b - a))) - min 1 (max 0 ((b - t) / (b - a)))|
        ≤ |max 0 ((b - s) / (b - a)) - max 0 ((b - t) / (b - a))| :=
          abs_min_sub_min_le_max _ _ _ _ |>.trans (by simp)
      _ ≤ |(b - s) / (b - a) - (b - t) / (b - a)| := by
          rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
      _ = (b - a)⁻¹ * |s - t| := by
          rw [div_sub_div_same, abs_div, abs_of_pos hba, abs_sub_comm]
          ring_nf
  -- step 2: `h = γ_{a,b} ∘ f` is `K`-Lipschitz, `K = (b - a)⁻¹ L`
  set K : NNReal := Real.toNNReal (b - a)⁻¹ * L with hK_def
  have hhK : LipschitzWith K h := hγ.comp hf
  -- steps 4–5: smooth `h` at the scales `σ_k = 1/((K + 1)(k + 1))`
  have hσ : ∀ k : ℕ, 0 < 1 / (((K : ℝ) + 1) * ((k : ℝ) + 1)) := fun k => by positivity
  have hex := fun k : ℕ => Submission.cmcs_lipschitz_smoothing P h K
    (1 / (((K : ℝ) + 1) * ((k : ℝ) + 1))) hhK (hσ k)
  choose hs hs_smooth hs_deriv hs_close _ using hex
  -- `K σ_k ≤ 1/(k + 1)`
  have hKσ : ∀ k : ℕ, (K : ℝ) * (1 / (((K : ℝ) + 1) * ((k : ℝ) + 1))) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hK0 : (0 : ℝ) ≤ K := K.2
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- step 3: `|h| ≤ 1`
  have hh01 : ∀ x, |h x| ≤ 1 := by
    intro x
    rw [abs_le]
    constructor
    · simp only [h]; exact le_trans (by norm_num) (le_min (by norm_num) (le_max_left _ _))
    · exact min_le_left _ _
  -- step 6: take `c = K`
  refine ⟨hs, K, hs_smooth, hs_deriv, ?_, ?_⟩
  · -- `|h_k| ≤ |h_k - h| + |h| ≤ 1/(k + 1) + 1 ≤ 2`
    intro k x
    have h1 := hs_close k x
    have h2 := hKσ k
    have h3 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc |hs k x| = |(hs k x - h x) + h x| := by ring_nf
      _ ≤ |hs k x - h x| + |h x| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (h1.trans (h2.trans h3)) (hh01 x)
      _ = 2 := by norm_num
  · -- `|h_k - h| ≤ 1/(k + 1) ≤ 1/(N + 1) < ε` for `k ≥ N`
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with k hk x
    rw [dist_comm, Real.dist_eq]
    calc |hs k x - h x| ≤ (K : ℝ) * (1 / (((K : ℝ) + 1) * ((k : ℝ) + 1))) := hs_close k x
      _ ≤ 1 / ((k : ℝ) + 1) := hKσ k
      _ ≤ 1 / ((N : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact_mod_cast Nat.add_le_add_right hk 1
      _ < ε := hN
/-- **Simon 6.4.11** (Leibniz rule behind the cutoff identity
`T(γ∘f dω) − T(d(γ∘f ω)) = −T(γ'(f) df ∧ ω)`): if `g` and the `k`-form `η` are differentiable
at `x`, then `d(gη)(x) = g(x) dη(x) + dg(x) ∧ η(x)`, where `dg(x) ∧ η(x)` is the alternation of
`v ↦ Dg(x)(v) η(x)`.  Unfold `d = extDeriv = alternatizeUncurryFin ∘ fderiv`, apply the product
rule `fderiv_fun_smul`, and use additivity and `ℝ`-homogeneity of `alternatizeUncurryFin`. -/
theorem Submission.cmcs_cd_extDeriv_smul_leibniz : ∀ (P k : ℕ) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (x : Euclid P), DifferentiableAt ℝ g x → DifferentiableAt ℝ η x → exteriorDerivative (fun y => g y • η y) x = g x • exteriorDerivative η x + ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x)) := by
  intro P k g η x hg hη
  -- `d θ x = alternatizeUncurryFin (fderiv ℝ θ x)` by definition
  show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => g y • η y) x) =
    g x • ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ η x) +
      ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight (η x))
  -- product rule, then linearity of the alternation
  rw [fderiv_fun_smul hg hη, ContinuousAlternatingMap.alternatizeUncurryFin_add,
    ContinuousAlternatingMap.alternatizeUncurryFin_smul]
/-- **Simon Ch. 6, 4.11** (the multiplier step behind `T(γ∘f dω)` and `T(d(γ∘f ω))`): test forms
in `U` are closed under multiplication by `C^∞` functions.  For `ω ∈ 𝒟ⁿ(U)` and `g ∈ C^∞`, the
form `gω` is `C^∞`; it vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω ⊆ U`, and `spt(gω)` is
compact as a closed subset of the compact set `spt ω`.  Neither openness of `U` nor compact
support of `g` is needed. -/
theorem Submission.cmcs_cd_smul_mem_testFormOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (g : Euclid P → ℝ) (ω : TestFormOn U n), ContDiff ℝ (⊤ : ℕ∞) g → (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n := by
  intro P n U g ω hg
  -- `ω ∈ 𝒟ⁿ(U)`: `ω` is `C^∞`, `spt ω` is compact and `spt ω ⊆ U`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := hω.1.1
  have hcompact : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
  -- `gω` vanishes wherever `ω` does, so `spt(gω) ⊆ spt ω`
  have hsub : tsupport (fun x => g x • (ω : DifferentialForm (Euclid P) n) x) ⊆
      tsupport (ω : DifferentialForm (Euclid P) n) :=
    tsupport_smul_subset_right (fun x => g x) _
  -- `spt(gω)` is a closed subset of the compact set `spt ω`
  have hcpt : IsCompact (tsupport fun x => g x • (ω : DifferentialForm (Euclid P) n) x) :=
    hcompact.of_isClosed_subset (isClosed_tsupport _) hsub
  exact ⟨⟨hg.smul hsmooth, hcpt⟩, hsub.trans hω.2⟩

/-- **Simon 6.4.11, the cut-off defect identity**, with a smooth `g` in place of `γ ∘ f` and with
`T`, `∂T` written through integral representations `T = ξ μ`, `∂T = ξ' μ'`: for `g ∈ C^∞` and
`η ∈ 𝒟^k(U)`, `T(g dη) − ∂T(gη) = −T(dg ∧ η)`, where
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`.  The forms `gη` and `g dη` are test forms by
`cmcs_cd_smul_mem_testFormOn`, and `d(gη) − g dη = dg ∧ η` pointwise by the Leibniz rule
`cmcs_cd_extDeriv_smul_leibniz`.  Every equality of integrals is a representation hypothesis or
`integral_congr_ae` for a pointwise identity, so no integrability is needed. -/
theorem Submission.cmcs_cd_defect_identity : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = -∫ x, ξ x (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x))) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hT hbT hg
  -- Step 1: the test forms `dη`, `gη`, `g dη` and `d(gη)`
  let dη : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k η
  let ηg : TestFormOn U k :=
    ⟨fun x => g x • (η : DifferentialForm (Euclid P) k) x,
      Submission.cmcs_cd_smul_mem_testFormOn P k U g η hg⟩
  let ωg : TestFormOn U (k + 1) :=
    ⟨fun x => g x • (dη : DifferentialForm (Euclid P) (k + 1)) x,
      Submission.cmcs_cd_smul_mem_testFormOn P (k + 1) U g dη hg⟩
  let dηg : TestFormOn U (k + 1) := exteriorDerivativeTestOn U k ηg
  -- Step 2: the first integral is `T(g dη)`
  have h1 : ∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ =
      T ωg := by
    rw [hT ωg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) =
      ξ x (g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 3: the second integral is `∂T(gη) = T(d(gη))`
  have h2 : ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' = T dηg := by
    rw [show T dηg = T.boundary ηg from (GeometricCurrentOn.boundary_apply T ηg).symm, hbT ηg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) =
      ξ' x (g x • (η : DifferentialForm (Euclid P) k) x)
    rw [map_smul, smul_eq_mul]
  -- Step 4: pointwise, `d(gη) − g dη = dg ∧ η` by the Leibniz rule
  have h3 : ∀ x, ((dηg - ωg : TestFormOn U (k + 1)) : DifferentialForm (Euclid P) (k + 1)) x =
      ContinuousAlternatingMap.alternatizeUncurryFin
        ((fderiv ℝ g x).smulRight ((η : DifferentialForm (Euclid P) k) x)) := by
    intro x
    have hgx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
    have hηx : DifferentiableAt ℝ (η : DifferentialForm (Euclid P) k) x :=
      η.property.1.1.differentiable (by simp) x
    change exteriorDerivative (fun y => g y • (η : DifferentialForm (Euclid P) k) y) x -
      g x • exteriorDerivative (η : DifferentialForm (Euclid P) k) x = _
    rw [Submission.cmcs_cd_extDeriv_smul_leibniz P k g _ x hgx hηx]
    abel
  -- Step 5: linearity of `T`
  have h4 : T ωg - T dηg = -T (dηg - ωg) := by
    have hsub := LinearMap.map_sub (T.toCurrent : ↥(TestFormOn U (k + 1)) →ₗ[ℝ] ℝ) dηg ωg
    change T.toCurrent ωg - T.toCurrent dηg = -T.toCurrent (dηg - ωg)
    rw [hsub]
    ring
  -- Steps 6 and 7: `T(d(gη) − g dη)` as an integral
  rw [h1, h2, h4, hT]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => congrArg (ξ x) (h3 x))
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

/-- **Simon Ch. 6, 3.1 (‡)**: the integrand `θ ⟨ω, ξ⟩` of `τ(M, θ, ξ)(ω)` is `Hⁿ⌞M`-integrable.
`ω` is continuous with compact support `K = spt ω ⊆ U`, so `‖ω‖ ≤ C` and `ω = 0` off `K`, and
`‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e.; hence `|θ ⟨ω, ξ⟩| ≤ C θ 1_K`, integrable as `∫_{M ∩ K} θ dHⁿ < ∞`. -/
theorem Submission.rsd_cmr_ic_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  obtain ⟨⟨hsmooth, hcpt⟩, hsupp⟩ := hω
  have hcont : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  -- `‖ω‖ ≤ C`, and `K = spt ω` is closed
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hcont
  have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
    (isClosed_tsupport _).measurableSet
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- `1_K θ` is `Hⁿ⌞M`-integrable: `∫_{M ∩ K} θ dHⁿ < ∞`
  have hh : Integrable ((tsupport (ω : DifferentialForm (Euclid P) n)).indicator
      fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
    refine ⟨hθ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
    exact (R.locallyIntegrable_mult _ hcpt.isCompact hsupp).lt_top
  -- `θ ⟨ω, ξ⟩` is a.e. strongly measurable and dominated by `C θ 1_K`
  refine (hh.const_mul C).mono' (hθ.aestronglyMeasurable.mul
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable))) ?_
  filter_upwards [R.orients] with x hx
  obtain ⟨Q, -, hQ⟩ := hx
  have hξ := (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  by_cases hK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
  · rw [indicator_of_mem hK, norm_mul, Real.norm_natCast, mul_comm C]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖
        ≤ ‖R.orient x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (R.orient x).le_opNorm _
      _ ≤ 1 * C := mul_le_mul hξ (hC x) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · simp [indicator_of_notMem hK, image_eq_zero_of_notMem_tsupport hK]

/-- **Simon Ch. 6, 3.1 (‡) under bounded multipliers**: if `h_k` are measurable, `|h_k| ≤ C`
and `h_k → h` pointwise, then `∫_M θ h_k ⟨ω, ξ⟩ dHⁿ → ∫_M θ h ⟨ω, ξ⟩ dHⁿ`.  The integrands are
`h_k G` with `G = θ ⟨ω, ξ⟩` `Hⁿ⌞M`-integrable, dominated by `C |G|` and converging pointwise to
`h G`, so dominated convergence applies. -/
theorem Submission.dor_lmbsf_ll_action_mul_tendsto : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (C : ℝ), (∀ k, Measurable (hs k)) → (∀ k x, |hs k x| ≤ C) → (∀ x, Tendsto (fun k => hs k x) atTop (𝓝 (h x))) → Tendsto (fun k => ∫ x in R.carrier, (R.mult x : ℝ) * hs k x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) atTop (𝓝 (∫ x in R.carrier, (R.mult x : ℝ) * h x * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])) := by
  intro P n U R ω hs h C hmeas hbdd hlim
  -- `G = θ ⟨ω, ξ⟩` is `Hⁿ⌞M`-integrable
  have hG := Submission.rsd_cmr_ic_action_integrable P n U R ω
  set G : Euclid P → ℝ :=
    fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
  -- the integrands are `h_k G` and `h G`
  have key : ∀ k,
      (fun x => (R.mult x : ℝ) * hs k x * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        = fun x => hs k x * G x := by
    intro k; funext x; simp only [G]; ring
  have keyh : (fun x => (R.mult x : ℝ) * h x * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
      = fun x => h x * G x := by
    funext x; simp only [G]; ring
  rw [keyh]
  simp_rw [key]
  -- dominated convergence with bound `C |G|`
  refine tendsto_integral_of_dominated_convergence (fun x => C * ‖G x‖) ?_ ?_ ?_ ?_
  · intro k; exact (hmeas k).aestronglyMeasurable.mul hG.aestronglyMeasurable
  · exact hG.norm.const_mul C
  · intro k
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hbdd k x) (norm_nonneg _)
  · filter_upwards with x
    exact (hlim x).mul_const (G x)

/-- Signed co-area integral (Simon Ch. 2, 6.6, used for the slices in 7.4): if the slice
measures `ν t` satisfy the co-area identity `∫ (∫ φ dν_t) dt = ∫ w φ dμ` for every Borel
`φ ≥ 0`, and `∫ w |q| dμ < ∞`, then `t ↦ ∫ q dν_t` is integrable and
`∫ (∫ q dν_t) dt = ∫ w q dμ`.  Apply the identity to `q⁺` and `q⁻` and subtract; where
`w = ∞`, finiteness of `∫ w |q| dμ` forces `q = 0` `μ`-a.e. -/
theorem Submission.dor_lmbsf_si_coarea_signed_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : ℝ → Measure (Euclid P)) (w : Euclid P → ℝ≥0∞) (q : Euclid P → ℝ), (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x, φ x ∂(ν t)) ∧ ∫⁻ t, ∫⁻ x, φ x ∂(ν t) = ∫⁻ x, w x * φ x ∂μ) → Measurable w → Measurable q → ∫⁻ x, w x * ‖q x‖ₑ ∂μ ≠ ∞ → Integrable (fun t => ∫ x, q x ∂(ν t)) ∧ ∫ t, ∫ x, q x ∂(ν t) = ∫ x, (w x).toReal * q x ∂μ := by
  intro P μ ν w q hco hw hq hfin
  -- `q⁺ = ofReal q` and `q⁻ = ofReal (-q)` are Borel and bounded by `|q|`
  have hqp : Measurable fun x => ENNReal.ofReal (q x) := hq.ennreal_ofReal
  have hqn : Measurable fun x => ENNReal.ofReal (-q x) := hq.neg.ennreal_ofReal
  have hle_p : ∀ x, ENNReal.ofReal (q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hle_n : ∀ x, ENNReal.ofReal (-q x) ≤ ‖q x‖ₑ := fun x => by
    rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  -- the co-area identity for `q⁺`, `q⁻` and `|q|`, all with finite total integral
  obtain ⟨haeP, heqP⟩ := hco _ hqp
  obtain ⟨haeN, heqN⟩ := hco _ hqn
  obtain ⟨haeA, heqA⟩ := hco _ hq.enorm
  have hfinP : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (q x) ∂(ν t) ≠ ∞ := by
    rw [heqP]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_p x) _)
  have hfinN : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t) ≠ ∞ := by
    rw [heqN]; exact ne_top_of_le_ne_top hfin (lintegral_mono fun x => mul_le_mul_right (hle_n x) _)
  have hfinA : ∫⁻ t, ∫⁻ x, ‖q x‖ₑ ∂(ν t) ≠ ∞ := by rw [heqA]; exact hfin
  -- `q` is `ν t`-integrable for a.e. `t`, where `∫ q dν_t = ∫ q⁺ dν_t - ∫ q⁻ dν_t`
  have hint : ∀ᵐ t, Integrable q (ν t) := by
    filter_upwards [ae_lt_top' haeA hfinA] with t ht
    exact ⟨hq.aestronglyMeasurable, ht⟩
  have hrepr : (fun t => ∫ x, q x ∂(ν t)) =ᵐ[volume] fun t =>
      (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal - (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal := by
    filter_upwards [hint] with t ht
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part ht
  have hIP : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeP hfinP
  have hIN : Integrable (fun t => (∫⁻ x, ENNReal.ofReal (-q x) ∂(ν t)).toReal) :=
    integrable_toReal_of_lintegral_ne_top haeN hfinN
  refine ⟨(hIP.sub hIN).congr hrepr.symm, ?_⟩
  -- the left side is `(∫ w q⁺ dμ).toReal - (∫ w q⁻ dμ).toReal`
  rw [integral_congr_ae hrepr, integral_sub hIP hIN, integral_toReal haeP (ae_lt_top' haeP hfinP),
    integral_toReal haeN (ae_lt_top' haeN hfinN), heqP, heqN]
  -- `h = w q` is `μ`-integrable since `|h| ≤ w |q|`; split `∫ h dμ` into its two parts
  have hh : Integrable (fun x => (w x).toReal * q x) μ := by
    refine ⟨(hw.ennreal_toReal.mul hq).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hfin.lt_top
    rw [enorm_mul]
    gcongr
    rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hh]
  -- `w |q| < ∞` `μ`-a.e., and there `ofReal (w r) = w ofReal r` whenever `|r| ≤ |q|`
  -- (if `w = ∞` then `q = 0`, so `r = 0`)
  have hnull : ∀ᵐ x ∂μ, w x * ‖q x‖ₑ < ∞ := ae_lt_top (hw.mul hq.enorm) hfin
  have key : ∀ x, w x * ‖q x‖ₑ < ∞ → ∀ r : ℝ, |r| ≤ |q x| →
      ENNReal.ofReal ((w x).toReal * r) = w x * ENNReal.ofReal r := by
    intro x hx r hr
    by_cases hwx : w x = ∞
    · have hq0 : q x = 0 := by
        by_contra hq0
        rw [hwx, ENNReal.top_mul (by simpa using hq0)] at hx
        exact lt_irrefl _ hx
      have : r = 0 := by rw [hq0, abs_zero] at hr; exact abs_nonpos_iff.mp hr
      simp [this]
    · rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hwx]
  have e1 : ∫⁻ x, ENNReal.ofReal ((w x).toReal * q x) ∂μ = ∫⁻ x, w x * ENNReal.ofReal (q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    exact key x hx (q x) le_rfl
  have e2 : ∫⁻ x, ENNReal.ofReal (-((w x).toReal * q x)) ∂μ =
      ∫⁻ x, w x * ENNReal.ofReal (-q x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnull] with x hx
    rw [← mul_neg]
    exact key x hx (-q x) (by rw [abs_neg])
  rw [e1, e2]
/-- Countable compact exhaustion, swapping "for every compact `K ⊆ U`" and "for a.e. `t`" (used
for the local integrability of the slices of Simon Ch. 6, 4.1–4.3 in the slicing step of the
proof of 7.4.3): if every `F t` is monotone and, for each compact `K ⊆ U`, `F t K ≠ ∞` for a.e.
`t`, then for a.e. `t`, `F t K ≠ ∞` for all compact `K ⊆ U` at once.  The compact sets
`Kᵢ = B̄(0, i) ∖ {y : dist(y, Uᶜ) < 1/(i+1)}` lie in `U`, and every compact `K ⊆ U` lies in some
`Kᵢ` (it is bounded and at positive distance from `Uᶜ`); intersect the countably many full-measure
sets and use `F t K ≤ F t Kᵢ`. -/
theorem Submission.dor_lmbsf_si_ae_forall_compact : ∀ (P : ℕ) (U : Set (Euclid P)) (F : ℝ → Set (Euclid P) → ℝ≥0∞), IsOpen U → (∀ t, Monotone (F t)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∀ᵐ t, F t K ≠ ∞) → ∀ᵐ t, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → F t K ≠ ∞ := by
  intro P U F hU hmono hK
  -- the compact sets `Kᵢ = B̄(0, i) ∖ thickening (1/(i+1)) Uᶜ ⊆ U`
  let Kn : ℕ → Set (Euclid P) := fun i => closedBall 0 i \ thickening (1 / ((i : ℝ) + 1)) Uᶜ
  have hKc : ∀ i, IsCompact (Kn i) := fun i =>
    (isCompact_closedBall 0 (i : ℝ)).diff isOpen_thickening
  have hKU : ∀ i, Kn i ⊆ U := by
    intro i x hx
    by_contra hxU
    exact hx.2 (self_subset_thickening (by positivity) _ hxU)
  -- every compact `K ⊆ U` lies in some `Kᵢ`: `K ⊆ B̄(0, R)` and `thickening δ K ⊆ U`
  have hcover : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ i, K ⊆ Kn i := by
    intro K hKc' hKU'
    obtain ⟨δ, hδ, hδK⟩ := hKc'.exists_thickening_subset_open hU hKU'
    obtain ⟨R, hR⟩ := hKc'.isBounded.subset_closedBall 0
    obtain ⟨i₁, hi₁⟩ := exists_nat_ge R
    obtain ⟨i₂, hi₂⟩ := exists_nat_one_div_lt hδ
    refine ⟨max i₁ i₂, fun x hx => ⟨?_, ?_⟩⟩
    · exact closedBall_subset_closedBall (hi₁.trans (by exact_mod_cast le_max_left i₁ i₂)) (hR hx)
    · intro hxt
      rw [mem_thickening_iff] at hxt
      obtain ⟨y, hyU, hxy⟩ := hxt
      have hlt : (1 : ℝ) / ((max i₁ i₂ : ℕ) + 1) ≤ 1 / ((i₂ : ℝ) + 1) := by
        gcongr; exact_mod_cast le_max_right i₁ i₂
      have hy : y ∈ thickening δ K := by
        rw [mem_thickening_iff]
        exact ⟨x, hx, by rw [dist_comm]; linarith⟩
      exact hyU (hδK hy)
  -- for a.e. `t`, `F t Kᵢ ≠ ∞` for all `i` at once; then `F t K ≤ F t Kᵢ`
  have hall : ∀ᵐ t, ∀ i, F t (Kn i) ≠ ∞ := ae_all_iff.mpr fun i => hK _ (hKc i) (hKU i)
  filter_upwards [hall] with t ht K hKc' hKU'
  obtain ⟨i, hi⟩ := hcover K hKc' hKU'
  exact ne_top_of_le_ne_top (ht i) (hmono t hi)
/-- The orientation field of a slice (Simon Ch. 6, 4.3–4.4: `ξₜ = ξ⌞(∇ᴹf/|∇ᴹf|)`, with
`⟨v⌞w, a⟩ = ⟨v, w ∧ a⟩`; the slices of Ch. 6, 4.5 enter the upper mass bound in the proof of
7.4.3): for a strongly measurable `(n+1)`-vector field `ζ` and a Borel vector field `g`, the
`n`-vector field `ζ' = ζ⌞(g/|g|)`, `⟨α, ζ'⟩ = ⟨(g/|g|)♭ ∧ α, ζ⟩`, is strongly measurable,
`|g| ζ' = ζ⌞g`, and `|⟨g♭ ∧ α, ζ⟩| ≤ (n + 1) |ζ| |g| |α|`.  The wedge `(v, α) ↦ v♭ ∧ α` is
bounded bilinear with `|v♭ ∧ α| ≤ (n + 1) |v| |α|`, so `(ζ₀, v) ↦ ζ₀ ∘ (v♭ ∧ ·)` is continuous. -/
theorem Submission.dor_lmbsf_si_slice_orientation_field : ∀ (P n : ℕ) (ζ : Euclid P → MultiVector P (n + 1)) (g : Euclid P → Euclid P), StronglyMeasurable ζ → Measurable g → ∃ ζ' : Euclid P → MultiVector P n, StronglyMeasurable ζ' ∧ (∀ x (α : Covector (Euclid P) n), ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (‖g x‖⁻¹ • g x)).smulRight α))) ∧ (∀ x (α : Covector (Euclid P) n), ‖g x‖ * ζ' x α = ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))) ∧ ∀ x (α : Covector (Euclid P) n), |ζ x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight α))| ≤ ((n : ℝ) + 1) * ‖ζ x‖ * ‖g x‖ * ‖α‖ := by
  intro P n ζ g hζ hg
  -- the wedge `B(v, α) = v♭ ∧ α`, with `|v♭ ∧ α| ≤ (n + 1) |v| |α|`
  let B : Euclid P × Covector (Euclid P) n → Covector (Euclid P) (n + 1) := fun p =>
    ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ p.1).smulRight p.2)
  have hBnorm : ∀ v α, ‖B (v, α)‖ ≤ ((n : ℝ) + 1) * ‖v‖ * ‖α‖ := fun v α => by
    refine (ContinuousAlternatingMap.norm_alternatizeUncurryFin_le _).trans_eq ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_assoc]
  -- `B` is bilinear: compare the arguments of `alternatizeUncurryFin` at each `y`
  have hB : IsBoundedBilinearMap ℝ B :=
    { add_left := fun v w α => by
        simp only [B, map_add, ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
        congr 1
        ext y
        simp [add_smul]
      smul_left := fun c v α => by
        simp only [B, map_smul, ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        congr 1
        ext y
        simp [smul_smul]
      add_right := fun v α β => by
        simp only [B, ← ContinuousAlternatingMap.alternatizeUncurryFin_add]
        congr 1
        ext y
        simp
      smul_right := fun c v α => by
        simp only [B, ← ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        congr 1
        ext y
        simp [smul_smul, mul_comm]
      bound := ⟨(n : ℝ) + 1, by positivity, hBnorm⟩ }
  -- `A v = v♭ ∧ ·`, a continuous linear map in `v`
  let A : Euclid P →L[ℝ] Covector (Euclid P) n →L[ℝ] Covector (Euclid P) (n + 1) :=
    hB.toContinuousLinearMap
  -- `Ξ(ζ₀, v) = ζ₀ ∘ (v♭ ∧ ·)` is continuous, since composition is bounded bilinear
  let Ξ : MultiVector P (n + 1) × Euclid P → MultiVector P n := fun p => p.1.comp (A p.2)
  have hΞ : Continuous Ξ := isBoundedBilinearMap_comp.continuous.comp
    (continuous_fst.prodMk (A.continuous.comp continuous_snd))
  -- `ζ' = Ξ(ζ, g/|g|)`, where `g/|g|` is Borel
  have hν : Measurable fun x => ‖g x‖⁻¹ • g x := hg.norm.inv.smul hg
  refine ⟨fun x => Ξ (ζ x, ‖g x‖⁻¹ • g x),
    hΞ.comp_stronglyMeasurable (hζ.prodMk hν.stronglyMeasurable), fun x α => rfl, ?_, ?_⟩
  · -- `|g| ζ' = ζ⌞g`: linearity of `A` and of `ζ(x)`; trivial where `g(x) = 0`
    intro x α
    show ‖g x‖ * ζ x (A (‖g x‖⁻¹ • g x) α) = ζ x (A (g x) α)
    by_cases hgx : g x = 0
    · simp [hgx]
    · rw [map_smul, smul_apply, map_smul, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hgx), one_mul]
  · -- `|⟨g♭ ∧ α, ζ⟩| ≤ |ζ| |g♭ ∧ α| ≤ (n + 1) |ζ| |g| |α|`
    intro x α
    show |ζ x (A (g x) α)| ≤ _
    rw [← Real.norm_eq_abs]
    calc ‖ζ x (A (g x) α)‖ ≤ ‖ζ x‖ * ‖A (g x) α‖ := (ζ x).le_opNorm _
      _ ≤ ‖ζ x‖ * (((n : ℝ) + 1) * ‖g x‖ * ‖α‖) := by gcongr; exact hBnorm (g x) α
      _ = ((n : ℝ) + 1) * ‖ζ x‖ * ‖g x‖ * ‖α‖ := by ring
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
/-- The vector representing `β ↦ ζ(β ∧ α)` (steps 4(a), 4(b) of the parent proof; Simon Ch. 6,
proof of Lemma 4.5(2), display (3)).  Write `β ∧ α` for `alternatizeUncurryFin (β.smulRight α)`,
`eₗ` for the standard basis of `ℝᴾ` and `V = Σₗ ζ(⟨eₗ, ·⟩ ∧ α) eₗ`.  Then `ζ(β ∧ α) = β(V)` for
every `1`-covector `β`, as `β ↦ ζ(β ∧ α)` is linear and `β = Σₗ β(eₗ) ⟨eₗ, ·⟩`.  If `ζ` orients
`Q` and `v ∈ Qᗮ`, then `(⟨v, ·⟩ ∧ α)(τ) = Σᵢ (-1)ⁱ ⟨v, τᵢ⟩ α(…) = 0` for the basis `τ` of `Q`, so
`⟨v, V⟩ = ζ(⟨v, ·⟩ ∧ α) = 0` and `V ∈ Qᗮᗮ = Q`. -/
theorem Submission.dor_lmbsf_ll_wedge_representing_vector : ∀ (P n : ℕ) (ζ : MultiVector P (n + 1)) (α : Covector (Euclid P) n), (∀ β : Euclid P →L[ℝ] ℝ, ζ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α)) = β (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ))) ∧ ∀ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf ζ Q → (∑ l : Fin P, ζ (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight α)) • EuclideanSpace.single l (1 : ℝ)) ∈ Q := by
  intro P n ζ α
  -- `Φ(β) = ζ(β ∧ α)` is linear in `β`
  let Φ : (Euclid P →L[ℝ] ℝ) → ℝ := fun β =>
    ζ (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight α))
  have hΦadd : ∀ β₁ β₂ : Euclid P →L[ℝ] ℝ, Φ (β₁ + β₂) = Φ β₁ + Φ β₂ := by
    intro β₁ β₂
    have : (β₁ + β₂).smulRight α = β₁.smulRight α + β₂.smulRight α := by
      ext v; simp [add_smul]
    simp only [Φ, this, ContinuousAlternatingMap.alternatizeUncurryFin_add, map_add]
  have hΦsmul : ∀ (c : ℝ) (β : Euclid P →L[ℝ] ℝ), Φ (c • β) = c • Φ β := by
    intro c β
    have : (c • β).smulRight α = c • β.smulRight α := by
      ext v; simp [mul_smul]
    simp only [Φ, this, ContinuousAlternatingMap.alternatizeUncurryFin_smul, map_smul]
  let Φl : (Euclid P →L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := Φ, map_add' := hΦadd, map_smul' := hΦsmul }
  -- `β = Σₗ β(eₗ) ⟨eₗ, ·⟩`
  have hβexp : ∀ β : Euclid P →L[ℝ] ℝ, β = ∑ l : Fin P,
      β (EuclideanSpace.single l (1 : ℝ)) • innerSL ℝ (EuclideanSpace.single l (1 : ℝ)) := by
    intro β
    ext v
    have hv : v = ∑ l : Fin P, v l • EuclideanSpace.single l (1 : ℝ) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v]
      simp
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_left, map_one, one_mul,
      smul_eq_mul]
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, mul_comm]
  -- `ζ(β ∧ α) = Σₗ β(eₗ) ζ(⟨eₗ, ·⟩ ∧ α) = β(V)`
  have hid : ∀ β : Euclid P →L[ℝ] ℝ, Φ β = β (∑ l : Fin P,
      Φ (innerSL ℝ (EuclideanSpace.single l (1 : ℝ))) • EuclideanSpace.single l (1 : ℝ)) := by
    intro β
    have h1 : Φ β = Φl β := rfl
    rw [h1, hβexp β, map_sum]
    simp only [map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro l _
    simp only [Φl, LinearMap.coe_mk, AddHom.coe_mk]
    have := hβexp β
    rw [← this]
    ring
  refine ⟨hid, ?_⟩
  intro Q hQ
  obtain ⟨τ, -, hspan, hsign⟩ := hQ
  -- `ζ(⟨v, ·⟩ ∧ α) = ±(⟨v, ·⟩ ∧ α)(τ) = 0` for `v ∈ Qᗮ`, as every `τᵢ ∈ Q`
  have hzero : ∀ v ∈ Qᗮ, Φ (innerSL ℝ v) = 0 := by
    intro v hv
    have hτQ : ∀ i, τ i ∈ Q := fun i => hspan ▸ Submodule.subset_span (Set.mem_range_self i)
    have hval :
        ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ v).smulRight α) τ = 0 := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      apply Finset.sum_eq_zero
      intro i _
      simp [Submodule.inner_left_of_mem_orthogonal (hτQ i) hv]
    rcases hsign with h | h
    · simp only [Φ, h, hval]
    · simp only [Φ, h, hval, neg_zero]
  -- `⟨u, V⟩ = ζ(⟨u, ·⟩ ∧ α) = 0` for `u ∈ Qᗮ`, so `V ∈ Qᗮᗮ = Q`
  rw [← Submodule.orthogonal_orthogonal Q, Submodule.mem_orthogonal]
  intro u hu
  have := hid (innerSL ℝ u)
  rw [hzero u hu, innerSL_apply_apply] at this
  exact this.symm

/-- **A bounded Borel tangent field representing `β ↦ ⟨β ∧ ω, ξ⟩`** (Simon Ch. 6, proof of
Lemma 4.5(2), display (3)).  Let `R = (M, θ, ξ)` be an integer multiplicity `(n+1)`-triple and `ω`
a continuous `n`-form with `‖ω‖ ≤ B`.  Let `ξ₀` be a strongly measurable version of `ξ`, replaced
by `0` where its norm exceeds `1`.  Then `W = Σₗ ξ₀(eₗ♭ ∧ ω) eₗ` is Borel, vanishes where `ω` does
and is bounded by `P (n+1) B`.  For `H^{n+1}`-a.e. `x ∈ M`, `ξ(x)` orients `TₓM`, so `‖ξ(x)‖ ≤ 1`
and `ξ₀(x) = ξ(x)`; there `W(x)` is the representing vector of `β ↦ ⟨β ∧ ω(x), ξ(x)⟩`, which
lies in `TₓM`. -/
theorem Submission.dor_lmbsf_ll_tangent_wedge_field : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U (n + 1)) (ω : DifferentialForm (Euclid P) n) (B : ℝ), Continuous ω → (∀ x, ‖ω x‖ ≤ B) → ∃ (W : Euclid P → Euclid P) (c' : ℝ), Measurable W ∧ (∀ x, ω x = 0 → W x = 0) ∧ (∀ x, ‖W x‖ ≤ c') ∧ ∀ᵐ x ∂(μHE[n + 1].restrict R.carrier), W x ∈ approxTangentPlane (n + 1) R.carrier x ∧ ∀ β : Euclid P →L[ℝ] ℝ, R.orient x (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight (ω x))) = β (W x) := by
  intro P n U R ω B hω hB
  classical
  -- a strongly measurable version `ξ₁` of `ξ`, and its truncation `ξ₀` to the closed unit ball
  have hξm := R.aestronglyMeasurable_orient
  set ξ₁ : Euclid P → MultiVector P (n + 1) := hξm.mk R.orient with hξ₁_def
  have hξ₁ : StronglyMeasurable ξ₁ := hξm.stronglyMeasurable_mk
  have hξ₁ae : R.orient =ᵐ[μHE[n + 1].restrict R.carrier] ξ₁ := hξm.ae_eq_mk
  set S : Set (Euclid P) := {x | ‖ξ₁ x‖ ≤ 1} with hS_def
  have hS : MeasurableSet S :=
    measurableSet_le (hξ₁.norm (β := MultiVector P (n + 1))).measurable measurable_const
  set ξ₀ : Euclid P → MultiVector P (n + 1) := S.piecewise ξ₁ 0 with hξ₀_def
  have hξ₀ : StronglyMeasurable ξ₀ := hξ₁.piecewise hS stronglyMeasurable_const
  have hξ₀norm : ∀ x, ‖ξ₀ x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ S
    · rw [hξ₀_def, Set.piecewise_eq_of_mem _ _ _ hx]; exact hx
    · rw [hξ₀_def, Set.piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply]
      exact (norm_zero (E := MultiVector P (n + 1))).le.trans zero_le_one
  -- the coefficient forms `Aₗ = eₗ♭ ∧ ω` are continuous
  set e : Fin P → Euclid P := fun l => EuclideanSpace.single l (1 : ℝ) with he_def
  set A : Fin P → Euclid P → Covector (Euclid P) (n + 1) := fun l x =>
    ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (e l)).smulRight (ω x)) with hA_def
  have hA : ∀ l, Continuous (A l) := by
    intro l
    have h1 : Continuous (fun x => (innerSL ℝ (e l)).smulRight (ω x)) :=
      (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Euclid P)).continuous.comp
        (continuous_const.prodMk hω)
    have h2 := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ (n := n)).continuous.comp h1
    simpa [Function.comp_def, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply] using h2
  -- the coefficients `ξ₀(Aₗ)` are strongly measurable
  have hcoef : ∀ l, StronglyMeasurable (fun x => ξ₀ x (A l x)) := by
    intro l
    have h2 : StronglyMeasurable (A l) := (hA l).stronglyMeasurable
    exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) (n + 1)) (F := ℝ)).continuous.comp_stronglyMeasurable
      (hξ₀.prodMk h2)
  set W : Euclid P → Euclid P := fun x => ∑ l : Fin P, ξ₀ x (A l x) • e l with hW_def
  -- `‖Aₗ‖ ≤ (n+1) ‖eₗ♭‖ ‖ω‖ ≤ (n+1) B`
  have hAnorm : ∀ l x, ‖A l x‖ ≤ (n + 1) * B := by
    intro l x
    have h1 := ContinuousAlternatingMap.norm_alternatizeUncurryFin_le ((innerSL ℝ (e l)).smulRight (ω x))
    have h2 : ‖(innerSL ℝ (e l)).smulRight (ω x)‖ = ‖innerSL ℝ (e l)‖ * ‖ω x‖ :=
      ContinuousLinearMap.norm_smulRight_apply _ _
    have h3 : ‖innerSL ℝ (e l)‖ = 1 := by
      rw [innerSL_apply_norm]; simp [e]
    calc ‖A l x‖ ≤ (n + 1) * ‖(innerSL ℝ (e l)).smulRight (ω x)‖ := h1
      _ = (n + 1) * ‖ω x‖ := by rw [h2, h3, one_mul]
      _ ≤ (n + 1) * B := by gcongr; exact hB x
  refine ⟨W, (P : ℝ) * ((n + 1) * B), ?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ (fun l _ => (hcoef l).measurable.smul_const (e l))
  · intro x hx
    have hA0 : ∀ l, A l x = 0 := by
      intro l
      have h0 : (innerSL ℝ (e l)).smulRight (0 : Covector (Euclid P) n) = 0 := by ext; simp
      ext v
      simp only [hA_def, hx, h0, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      simp
    simp only [hW_def, hA0, map_zero, zero_smul, Finset.sum_const_zero]
  · intro x
    calc ‖W x‖ ≤ ∑ l : Fin P, ‖ξ₀ x (A l x) • e l‖ := norm_sum_le _ _
      _ ≤ ∑ l : Fin P, (n + 1) * B := by
          apply Finset.sum_le_sum
          intro l _
          rw [norm_smul]
          have he1 : ‖e l‖ = 1 := by simp [e]
          rw [he1, mul_one]
          calc ‖ξ₀ x (A l x)‖ ≤ ‖ξ₀ x‖ * ‖A l x‖ := (ξ₀ x).le_opNorm _
            _ ≤ 1 * ((n + 1) * B) := by
                gcongr
                · exact hξ₀norm x
                · exact hAnorm l x
            _ = (n + 1) * B := one_mul _
      _ = (P : ℝ) * ((n + 1) * B) := by simp
  -- a.e. on `M`: `ξ` orients `TₓM`, so `‖ξ‖ ≤ 1` and `ξ₀ = ξ₁ = ξ`; then `W` is the representing
  -- vector of `β ↦ ξ(β ∧ ω)`
  · filter_upwards [hξ₁ae, Submission.fvmb_imrep_ae_unitOrientation_approxTangentPlane P (n + 1) U R] with x hx1 hx2
    have hnorm : ‖R.orient x‖ ≤ 1 := Submission.unit_orientation_norm_le_one P (n + 1) _ _ hx2
    have hxS : x ∈ S := by
      show ‖ξ₁ x‖ ≤ 1
      rw [← hx1]; exact hnorm
    have hξ₀x : ξ₀ x = R.orient x := by
      rw [hξ₀_def, Set.piecewise_eq_of_mem _ _ _ hxS, hx1]
    obtain ⟨hidt, hmem⟩ := Submission.dor_lmbsf_ll_wedge_representing_vector P n (R.orient x) (ω x)
    have hWx : W x = ∑ l : Fin P, R.orient x (ContinuousAlternatingMap.alternatizeUncurryFin
        ((innerSL ℝ (EuclideanSpace.single l (1 : ℝ))).smulRight (ω x))) • EuclideanSpace.single l (1 : ℝ) := by
      simp only [hW_def, hA_def, he_def, hξ₀x]
    refine ⟨?_, ?_⟩
    · rw [hWx]; exact hmem _ hx2
    · intro β; rw [hWx]; exact hidt β

/-- **Simon Ch. 6, proof of Lemma 4.5(2), displays (1)–(4)** (Leibniz rule for the Lipschitz
cut-off `h = γ ∘ f`, `γ(s) = min{1, max{0, (b − s)/(b − a)}}`): if `T = τ(M, θ, ξ)`,
`∂T = τ(M', θ', ξ')` and the weak-limit property (G5) holds, then for `ω ∈ 𝒟ⁿ(U)` and `a < b`,
`∫_{M'} θ' h ⟨ω, ξ'⟩ dHⁿ = ∫_M θ h ⟨dω, ξ⟩ dH^{n+1} − (b − a)⁻¹ ∫_{M ∩ {a < f < b}} θ ⟨g♭ ∧ ω, ξ⟩
dH^{n+1}`.  Take `C^∞` functions `h_k → h` uniformly with `‖Dh_k‖ ≤ c` and `|h_k| ≤ 2`, and a
bounded Borel field `W`, zero off `spt ω`, with `W ∈ TₓM` and `ξ(β ∧ ω) = β(W)` for
`H^{n+1}`-a.e. `x ∈ M`.  The defect identity gives `∂T(h_k ω) = T(h_k dω) + ∫_M θ Dh_k[W]`.  As
`k → ∞` the outer terms converge by dominated convergence and the last term by (G5), with limit
`−(b − a)⁻¹ ∫_{M ∩ {a < f < b}} θ ⟨g, W⟩`, and `⟨g, W⟩ = ξ(g♭ ∧ ω)` a.e. on `M`. -/
theorem Submission.dor_lmbsf_lipschitz_cutoff_leibniz : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal) (g : Euclid P → Euclid P), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → Measurable g → (∀ x, ‖g x‖ ≤ L) → (∀ (a b : ℝ), a < b → ∀ (hs : ℕ → Euclid P → ℝ) (c : ℝ), (∀ k, ContDiff ℝ 1 (hs k)) → (∀ k x, ‖fderiv ℝ (hs k) x‖ ≤ c) → TendstoUniformly hs (fun x => min 1 (max 0 ((b - f x) / (b - a)))) atTop → ∀ (W : Euclid P → Euclid P) (K : Set (Euclid P)) (c' : ℝ), Measurable W → IsCompact K → K ⊆ U → (∀ x, x ∉ K → W x = 0) → (∀ x, ‖W x‖ ≤ c') → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), W x ∈ approxTangentPlane (n + 1) RT.carrier x) → Tendsto (fun k => ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1]) atTop (𝓝 (∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)) ∂μHE[n + 1]))) → ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = (∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - (b - a)⁻¹ * ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x))) ∂μHE[n + 1] := by
  intro P n U T RT RB f L g _hU hRT hRB hf _hgm _hgL hG5 ω a b hab
  -- `ω` is continuous and bounded, and `K = spt ω` is a compact subset of `U`
  obtain ⟨⟨hωs, hωK⟩, hωU⟩ : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := hωs.continuous
  obtain ⟨B, hB⟩ := hωc.bounded_above_of_compact_support hωK
  -- Step 1: `C^∞` cut-offs `h_k → h` uniformly, with `‖Dh_k‖ ≤ c` and `|h_k| ≤ 2`
  obtain ⟨hs, c, hs_smooth, hs_deriv, hs_bdd, hs_unif⟩ :=
    Submission.dor_lmbsf_ll_cutoff_smooth_approx P f L a b hf hab
  have hs_meas : ∀ k, Measurable (hs k) := fun k => (hs_smooth k).continuous.measurable
  -- Step 4: `W` is bounded, Borel and zero off `spt ω`; `W ∈ TₓM` and `ξ(β ∧ ω) = β(W)` a.e.
  obtain ⟨W, c', hWm, hW0, hWc, hWae⟩ :=
    Submission.dor_lmbsf_ll_tangent_wedge_field P n U RT (ω : DifferentialForm (Euclid P) n) B
      hωc hB
  -- Step 4(d): (G5) for `h_k`, `W` and `K = spt ω`
  have hmid := hG5 a b hab hs c (fun k => (hs_smooth k).of_le (by exact_mod_cast le_top))
    hs_deriv hs_unif W (tsupport (ω : DifferentialForm (Euclid P) n)) c' hWm hωK hωU
    (fun x hx => hW0 x (image_eq_zero_of_notMem_tsupport hx)) hWc (hWae.mono fun x hx => hx.1)
  -- Step 3: the outer terms converge by dominated convergence
  have hlimB : Tendsto (fun k => ∫ x in RB.carrier, (RB.mult x : ℝ) * hs k x *
      RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) atTop
      (𝓝 (∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) *
        RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])) :=
    Submission.dor_lmbsf_ll_action_mul_tendsto P n U RB ω hs
      (fun x => min 1 (max 0 ((b - f x) / (b - a)))) 2 hs_meas hs_bdd hs_unif.tendsto_at
  have hlimT : Tendsto (fun k => ∫ x in RT.carrier, (RT.mult x : ℝ) * hs k x *
      RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) atTop
      (𝓝 (∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) *
        RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1])) :=
    Submission.dor_lmbsf_ll_action_mul_tendsto P (n + 1) U RT (exteriorDerivativeTestOn U n ω) hs
      (fun x => min 1 (max 0 ((b - f x) / (b - a)))) 2 hs_meas hs_bdd hs_unif.tendsto_at
  -- Step 2: `T = (θ ξ) H^{n+1}⌞M` and `∂T = (θ' ξ') Hⁿ⌞M'`
  have hrepT : ∀ η : TestFormOn U (n + 1), T η = ∫ x, ((RT.mult x : ℝ) • RT.orient x)
      ((η : DifferentialForm (Euclid P) (n + 1)) x) ∂(μHE[n + 1].restrict RT.carrier) := by
    intro η
    rw [hRT η]
    simp only [IMRep.action, smul_apply, smul_eq_mul]
  have hrepB : ∀ η : TestFormOn U n, T.boundary η = ∫ x, ((RB.mult x : ℝ) • RB.orient x)
      ((η : DifferentialForm (Euclid P) n) x) ∂(μHE[n].restrict RB.carrier) := by
    intro η
    rw [hRB η]
    simp only [IMRep.action, smul_apply, smul_eq_mul]
  -- Steps 2 and 4(c): `∂T(h_k ω) = T(h_k dω) + T(dh_k ∧ ω)` and `ξ(dh_k ∧ ω) = Dh_k[W]` a.e.
  have hk : ∀ k, ∫ x in RB.carrier, (RB.mult x : ℝ) * hs k x *
      RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
      (∫ x in RT.carrier, (RT.mult x : ℝ) * hs k x *
        RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) +
      ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1] := by
    intro k
    have hid := Submission.cmcs_cd_defect_identity P n U T (μHE[n + 1].restrict RT.carrier)
      (μHE[n].restrict RB.carrier) (fun x => (RT.mult x : ℝ) • RT.orient x)
      (fun x => (RB.mult x : ℝ) • RB.orient x) (hs k) ω hrepT hrepB (hs_smooth k)
    have e1 : ∫ x, hs k x * ((RT.mult x : ℝ) • RT.orient x)
        (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x)
          ∂(μHE[n + 1].restrict RT.carrier) =
        ∫ x in RT.carrier, (RT.mult x : ℝ) * hs k x *
          RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1] :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [smul_apply, smul_eq_mul]
        ring)
    have e2 : ∫ x, hs k x * ((RB.mult x : ℝ) • RB.orient x)
        ((ω : DifferentialForm (Euclid P) n) x) ∂(μHE[n].restrict RB.carrier) =
        ∫ x in RB.carrier, (RB.mult x : ℝ) * hs k x *
          RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [smul_apply, smul_eq_mul]
        ring)
    have e3 : ∫ x, ((RT.mult x : ℝ) • RT.orient x)
        (ContinuousAlternatingMap.alternatizeUncurryFin ((fderiv ℝ (hs k) x).smulRight
          ((ω : DifferentialForm (Euclid P) n) x))) ∂(μHE[n + 1].restrict RT.carrier) =
        ∫ x in RT.carrier, (RT.mult x : ℝ) * fderiv ℝ (hs k) x (W x) ∂μHE[n + 1] := by
      refine integral_congr_ae ?_
      filter_upwards [hWae] with x hx
      rw [smul_apply, smul_eq_mul, hx.2]
    rw [e1, e2, e3] at hid
    linarith
  -- Step 4(e): the (G5) limit is `−(b − a)⁻¹ ∫_{M ∩ {a < f < b}} θ ξ(g♭ ∧ ω)`
  have hval : ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b},
      (RT.mult x : ℝ) * (-(b - a)⁻¹ * inner ℝ (g x) (W x)) ∂μHE[n + 1] =
      -(b - a)⁻¹ * ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) *
        RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight
          ((ω : DifferentialForm (Euclid P) n) x))) ∂μHE[n + 1] := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hWae] with x hx
    rw [hx.2, innerSL_apply_apply]
    ring
  -- Step 5: let `k → ∞`; limits are unique
  have hlim := tendsto_nhds_unique hlimB ((hlimT.add hmid).congr fun k => (hk k).symm)
  rw [hlim, hval]
  ring

/-- **The slices of an integer multiplicity triple** (Simon Ch. 6, Lemma 4.1, Remark 4.2, 4.3,
Definition 4.4 and the proof of Lemma 4.5(1)).  Let `RT = (M, θ, ξ)` be an integer multiplicity
`(n+1)`-triple in `U`, `f` `L`-Lipschitz and `g` Borel with `|g| ≤ L` and `g(x) ∈ TₓM` a.e. on `M`.
Assume the co-area identity on the slices `Mₜ = M ∩ {g ≠ 0} ∩ f⁻¹(t)`, that every `Mₜ` is
countably `n`-rectifiable and that, when `Hⁿ⌞Mₜ` is locally finite in `U`, `Mₜ` has approximate
tangent space `TₓM ∩ g(x)^⊥` a.e.  Let `ξ₀` be a strongly measurable version of `ξ` and
`ζ' = ξ₀ ⌞ (g/|g|)♭`.  For a.e. `t`, `θ Hⁿ⌞Mₜ` is locally finite and a.e. `x ∈ Mₜ` has `ξ₀(x)`
orienting `TₓM` and `g(x) ∈ TₓM`; then `Rₜ = (Mₜ, θ, ζ')` is an integer multiplicity `n`-triple
(`ζ'(x)` orients `TₓM ∩ g(x)^⊥`), and otherwise `Rₜ` is the empty triple.  The co-area identity
with `φ = θ 1_W` gives `∫ μ_{Rₜ}(W) dt ≤ L μ_{RT}(W)`.  The signed co-area identity for
`q = θ ζ'(ω)` and `q 1_{a<f<b}`, where `|g| q = θ ξ₀(g♭ ∧ ω)` and `|g| |q| ≤ (n+1) L sup|ω| θ` on
`spt ω`, gives the integrability of `t ↦ τ(Rₜ)(ω)` and, as `f ≡ t` on `Mₜ`,
`∫_a^b τ(Rₜ)(ω) dt = ∫_{M ∩ {a<f<b}} θ ⟨g♭ ∧ ω, ξ⟩ dH^{n+1}`. -/
theorem Submission.dor_lmbsf_slice_imreps : ∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (f : Euclid P → ℝ) (L : NNReal) (g : Euclid P → Euclid P), IsOpen U → LipschitzWith L f → Measurable g → (∀ x, ‖g x‖ ≤ L) → (∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier), g x ∈ approxTangentPlane (n + 1) RT.carrier x) → (∀ φ : Euclid P → ℝ≥0∞, Measurable φ → AEMeasurable (fun t => ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) ∧ ∫⁻ t, (∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, φ x ∂μHE[n]) = ∫⁻ x in RT.carrier, ‖g x‖ₑ * φ x ∂μHE[n + 1]) → (∀ t, CountablyRectifiable n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) → (∀ t, (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})), HasApproximateTangentSpaceAt n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) x (approxTangentPlane (n + 1) RT.carrier x ⊓ (ℝ ∙ g x)ᗮ)) → ∃ Rs : ℝ → IMRep U n, (∀ t, (Rs t).carrier ⊆ f ⁻¹' {t}) ∧ (∀ W : Set (Euclid P), MeasurableSet W → AEMeasurable (fun t => (Rs t).measure W) ∧ ∫⁻ t, (Rs t).measure W ≤ (L : ℝ≥0∞) * RT.measure W) ∧ (∀ ω : TestFormOn U n, Integrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) ∧ ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = ∫ x in RT.carrier ∩ {x | a < f x ∧ f x < b}, (RT.mult x : ℝ) * RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x))) ∂μHE[n + 1] := by
  intro P n U RT f L g hU hf hg hgL hgT hco hrect htan
  classical
  have hfm : Measurable f := hf.continuous.measurable
  have hθm : Measurable fun x => (RT.mult x : ℝ≥0∞) := measurable_from_nat.comp RT.measurable_mult
  have hθm' : Measurable fun x => (RT.mult x : ℝ) := measurable_from_nat.comp RT.measurable_mult
  have hgL' : ∀ x, ‖g x‖ₑ ≤ (L : ℝ≥0∞) := fun x =>
    enorm_le_coe.mpr (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact hgL x)
  have hMt : ∀ t, MeasurableSet (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) := fun t =>
    (RT.measurableSet_carrier.inter (hg (measurableSet_singleton 0).compl)).inter
      (hfm (measurableSet_singleton t))
  -- `∫_S 1_W θ = ∫_{S ∩ W} θ`
  have hind : ∀ W : Set (Euclid P), MeasurableSet W → ∀ (μ' : Measure (Euclid P))
      (S : Set (Euclid P)), ∫⁻ x in S, W.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μ' =
        ∫⁻ x in S ∩ W, (RT.mult x : ℝ≥0∞) ∂μ' := by
    intro W hW μ' S
    rw [lintegral_indicator hW, Measure.restrict_restrict hW, inter_comm W]
  -- a strongly measurable version `ξ₀` of the orientation `ξ` of `RT`, and the slice orientation
  -- field `ζ' = ξ₀ ⌞ (g/|g|)♭`
  obtain ⟨ξ₀, hξ₀, hξξ₀⟩ : ∃ ξ₀ : Euclid P → MultiVector P (n + 1), StronglyMeasurable ξ₀ ∧
      RT.orient =ᵐ[μHE[n + 1].restrict RT.carrier] ξ₀ :=
    ⟨_, RT.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      RT.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨ζ', hζ'm, hζ'ν, hζ'g, hζbd⟩ :=
    Submission.dor_lmbsf_si_slice_orientation_field P n ξ₀ g hξ₀ hg
  -- good points of `M`: `ξ₀(x)` is a unit orientation of `TₓM` and `g(x) ∈ TₓM`
  have hgood : ∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier),
      IsUnitOrientationOf (ξ₀ x) (approxTangentPlane (n + 1) RT.carrier x) ∧
        g x ∈ approxTangentPlane (n + 1) RT.carrier x := by
    filter_upwards [Submission.fvmb_imrep_ae_unitOrientation_approxTangentPlane P (n + 1) U RT,
      hξξ₀, hgT] with x h1 h2 h3
    exact ⟨h2 ▸ h1, h3⟩
  -- step 1: for a.e. `t`, a.e. point of `Mₜ` is a good point of `M`
  have hgood_t : ∀ᵐ t, ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})),
      IsUnitOrientationOf (ξ₀ x) (approxTangentPlane (n + 1) RT.carrier x) ∧
        g x ∈ approxTangentPlane (n + 1) RT.carrier x :=
    Submission.dor_lmbsf_si_coarea_ae_transfer P (μHE[n + 1].restrict RT.carrier)
      (fun t => μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) (fun x => ‖g x‖ₑ) _
      hco hgood
  -- step 2: for a.e. `t`, `θ Hⁿ⌞Mₜ` is locally finite in `U`; by the co-area identity with
  -- `φ = θ 1_K`, `∫ ∫_{Mₜ ∩ K} θ dHⁿ dt ≤ L ∫_{M ∩ K} θ dH^{n+1} < ∞` for compact `K ⊆ U`
  have hfin : ∀ᵐ t, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K, (RT.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    refine Submission.dor_lmbsf_si_ae_forall_compact P U
      (fun t K => ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K, (RT.mult x : ℝ≥0∞) ∂μHE[n])
      hU (fun t => by
        intro K₁ K₂ hK
        exact lintegral_mono_set (inter_subset_inter_right _ hK)) ?_
    intro K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    obtain ⟨hae, heq⟩ := hco _ (hθm.indicator hKm)
    have hlt : ∫⁻ t, ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t},
        K.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μHE[n] ≠ ∞ := by
      rw [heq]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.coe_ne_top (r := L))
        (RT.locallyIntegrable_mult K hK hKU)) ?_
      calc ∫⁻ x in RT.carrier, ‖g x‖ₑ * K.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μHE[n + 1]
          ≤ ∫⁻ x in RT.carrier, (L : ℝ≥0∞) * K.indicator (fun x => (RT.mult x : ℝ≥0∞)) x
              ∂μHE[n + 1] := lintegral_mono fun x => mul_le_mul' (hgL' x) le_rfl
        _ = (L : ℝ≥0∞) * ∫⁻ x in RT.carrier ∩ K, (RT.mult x : ℝ≥0∞) ∂μHE[n + 1] := by
          rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, hind K hKm]
    filter_upwards [ae_lt_top' hae hlt] with t ht
    rw [hind K hKm] at ht
    exact ht.ne
  -- the good levels
  obtain ⟨G, hGae, hGfin, hGgood⟩ : ∃ G : ℝ → Prop, (∀ᵐ t, G t) ∧
      (∀ t, G t → ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
        ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K, (RT.mult x : ℝ≥0∞) ∂μHE[n] ≠ ∞) ∧
      (∀ t, G t → ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})),
        IsUnitOrientationOf (ξ₀ x) (approxTangentPlane (n + 1) RT.carrier x) ∧
          g x ∈ approxTangentPlane (n + 1) RT.carrier x) :=
    ⟨_, hfin.and hgood_t, fun _ ht => ht.1, fun _ ht => ht.2⟩
  -- steps 3 and 4: `Rₜ = (Mₜ, θ, ζ')` for good `t`, the empty triple otherwise
  have hR : ∀ t, ∃ R : IMRep U n,
      R.carrier = (if G t then RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} else ∅) ∧
        R.mult = RT.mult ∧ R.orient = ζ' := by
    intro t
    by_cases ht : G t
    · -- `Hⁿ⌞Mₜ` is locally finite in `U`, as `θ ≥ 1` on `Mₜ`
      have hfinH : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
          μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K) ≠ ∞ := by
        intro K hK hKU
        refine ne_top_of_le_ne_top (hGfin t ht K hK hKU) ?_
        calc μHE[n] (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K)
            = ∫⁻ _ in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K, 1 ∂μHE[n] :=
              (setLIntegral_one _).symm
          _ ≤ ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t} ∩ K, (RT.mult x : ℝ≥0∞) ∂μHE[n] :=
              setLIntegral_mono' ((hMt t).inter hK.isClosed.measurableSet) fun x hx =>
                Nat.one_le_cast.mpr (RT.mult_pos x hx.1.1.1)
      -- `ζ'(x)` orients `TₓM ∩ g(x)^⊥`, the approximate tangent space of `Mₜ` at `x`
      have horients : ∀ᵐ x ∂(μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})),
          ∃ Q : Submodule ℝ (Euclid P),
            HasApproximateTangentSpaceAt n (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}) x Q ∧
              IsUnitOrientationOf (ζ' x) Q := by
        filter_upwards [htan t hfinH, hGgood t ht, ae_restrict_mem (hMt t)] with x hxT hxg hxM
        have hn : ‖g x‖ ≠ 0 := norm_ne_zero_iff.mpr hxM.1.2
        have h1 : ‖‖g x‖⁻¹ • g x‖ = 1 := by
          rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
        have h := Submission.dor_lmbsf_interior_product_orientation P n (ξ₀ x) (ζ' x)
          (approxTangentPlane (n + 1) RT.carrier x) (‖g x‖⁻¹ • g x) hxg.1
          (Submodule.smul_mem _ _ hxg.2) h1 (hζ'ν x)
        rw [Submodule.span_singleton_smul_eq (inv_ne_zero hn).isUnit] at h
        exact ⟨_, hxT, h⟩
      exact ⟨{ carrier := RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}
               mult := RT.mult
               orient := ζ'
               measurableSet_carrier := hMt t
               carrier_subset := fun x hx => RT.carrier_subset hx.1.1
               rectifiable := hrect t
               measurable_mult := RT.measurable_mult
               mult_pos := fun x hx => RT.mult_pos x hx.1.1
               locallyIntegrable_mult := hGfin t ht
               aestronglyMeasurable_orient := hζ'm.aestronglyMeasurable
               orients := horients }, by rw [ite_eq_left ht], rfl, rfl⟩
    · exact ⟨{ carrier := ∅
               mult := RT.mult
               orient := ζ'
               measurableSet_carrier := MeasurableSet.empty
               carrier_subset := empty_subset _
               rectifiable := (hrect t).mono (empty_subset _)
               measurable_mult := RT.measurable_mult
               mult_pos := fun x hx => absurd hx (notMem_empty x)
               locallyIntegrable_mult := fun K _ _ => by simp
               aestronglyMeasurable_orient := hζ'm.aestronglyMeasurable
               orients := by simp }, by rw [ite_eq_right ht], rfl, rfl⟩
  choose Rs hRc hRm hRo using hR
  -- mass and action of `Rₜ` at good levels
  have hmeas : ∀ W : Set (Euclid P), MeasurableSet W → ∀ t, G t →
      (Rs t).measure W = ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t},
        W.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μHE[n] := by
    intro W hW t ht
    rw [IMRep.measure, withDensity_apply _ hW, hRc t, hRm t, ite_eq_left ht, lintegral_indicator hW]
  have hact : ∀ (ω : DifferentialForm (Euclid P) n) t, G t →
      (Rs t).action ω = ∫ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t},
        (RT.mult x : ℝ) * ζ' x (ω x) ∂μHE[n] := by
    intro ω t ht
    rw [IMRep.action, hRc t, hRm t, hRo t, ite_eq_left ht]
  -- the signed co-area identity
  have hsig : ∀ q : Euclid P → ℝ, Measurable q →
      ∫⁻ x in RT.carrier, ‖g x‖ₑ * ‖q x‖ₑ ∂μHE[n + 1] ≠ ∞ →
      Integrable (fun t => ∫ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, q x ∂μHE[n]) ∧
        ∫ t, ∫ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t}, q x ∂μHE[n] =
          ∫ x in RT.carrier, ‖g x‖ * q x ∂μHE[n + 1] := by
    intro q hq hq'
    have h := Submission.dor_lmbsf_si_coarea_signed_integral P (μHE[n + 1].restrict RT.carrier)
      (fun t => μHE[n].restrict (RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t})) (fun x => ‖g x‖ₑ) q
      hco hg.enorm hq hq'
    simp only [toReal_enorm] at h
    exact h
  -- the integrand `q_ω = θ ζ'(ω)`: measurability and the co-area bound
  -- `|g| |q_ω| = θ |ξ₀(g♭ ∧ ω)| ≤ (n+1) L sup|ω| θ 1_{spt ω}` a.e. on `M`
  have hqm : ∀ ω : TestFormOn U n,
      Measurable fun x => (RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x) := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous ω.2.1.1
    exact hθm'.mul ((continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (hζ'm.prodMk hωc.stronglyMeasurable)).measurable
  have hqfin : ∀ ω : TestFormOn U n, ∫⁻ x in RT.carrier,
      ‖g x‖ₑ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n + 1] ≠
        ∞ := by
    intro ω
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.2.1.2.isCompact
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      hK.isClosed.measurableSet
    obtain ⟨c, hc⟩ := (ContDiff.continuous ω.2.1.1).bounded_above_of_compact_support ω.2.1.2
    have hbound : ∀ᵐ x ∂(μHE[n + 1].restrict RT.carrier),
        ‖g x‖ₑ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤
          (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
            (fun x => (RT.mult x : ℝ≥0∞) * ENNReal.ofReal (((n : ℝ) + 1) * L * c)) x := by
      filter_upwards [hgood] with x hx
      by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
      · rw [indicator_of_mem hxK]
        have hξ1 : ‖ξ₀ x‖ ≤ 1 := Submission.unit_orientation_norm_le_one P (n + 1) _ _ hx.1
        have hreal : ‖g x‖ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤
            (RT.mult x : ℝ) * (((n : ℝ) + 1) * L * c) := by
          have h1 : ‖g x‖ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖ =
              (RT.mult x : ℝ) * |ξ₀ x (ContinuousAlternatingMap.alternatizeUncurryFin
                ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x)))| := by
            rw [← hζ'g x]
            simp only [Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_norm]
            ring
          rw [h1]
          gcongr
          calc |ξ₀ x (ContinuousAlternatingMap.alternatizeUncurryFin
                ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x)))|
              ≤ ((n : ℝ) + 1) * ‖ξ₀ x‖ * ‖g x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ :=
                hζbd x _
            _ ≤ ((n : ℝ) + 1) * 1 * L * c := by
                gcongr
                exacts [hgL x, hc x]
            _ = ((n : ℝ) + 1) * L * c := by ring
        calc ‖g x‖ₑ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ
            = ENNReal.ofReal
                (‖g x‖ * ‖(RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)‖) := by
              rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
          _ ≤ ENNReal.ofReal ((RT.mult x : ℝ) * (((n : ℝ) + 1) * L * c)) :=
              ENNReal.ofReal_le_ofReal hreal
          _ = (RT.mult x : ℝ≥0∞) * ENNReal.ofReal (((n : ℝ) + 1) * L * c) := by
              rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      · simp [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
    rw [lintegral_indicator hKm, Measure.restrict_restrict hKm, inter_comm (tsupport _),
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top (RT.locallyIntegrable_mult _ hK ω.2.2) ENNReal.ofReal_ne_top
  refine ⟨Rs, fun t x hx => ?_, fun W hW => ?_, fun ω => ?_, fun ω a b hab => ?_⟩
  · -- (1): `Rₜ` is carried by `f⁻¹(t)`
    rw [hRc t] at hx
    split_ifs at hx with ht
    · exact hx.2
    · exact absurd hx (notMem_empty x)
  · -- (2): co-area identity with `φ = θ 1_W` and `|g| ≤ L`
    obtain ⟨hae, heq⟩ := hco _ (hθm.indicator hW)
    have hcongr : (fun t => (Rs t).measure W) =ᵐ[volume] fun t =>
        ∫⁻ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {t},
          W.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μHE[n] := by
      filter_upwards [hGae] with t ht using hmeas W hW t ht
    refine ⟨hae.congr hcongr.symm, ?_⟩
    rw [lintegral_congr_ae hcongr, heq]
    calc ∫⁻ x in RT.carrier, ‖g x‖ₑ * W.indicator (fun x => (RT.mult x : ℝ≥0∞)) x ∂μHE[n + 1]
        ≤ ∫⁻ x in RT.carrier, (L : ℝ≥0∞) * W.indicator (fun x => (RT.mult x : ℝ≥0∞)) x
            ∂μHE[n + 1] := lintegral_mono fun x => mul_le_mul' (hgL' x) le_rfl
      _ = (L : ℝ≥0∞) * RT.measure W := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, IMRep.measure, withDensity_apply _ hW,
          lintegral_indicator hW]
  · -- (3): `t ↦ τ(Rₜ)(ω)` agrees a.e. with the integrable `t ↦ ∫_{Mₜ} q_ω dHⁿ`
    obtain ⟨hint, -⟩ := hsig _ (hqm ω) (hqfin ω)
    refine hint.congr ?_
    filter_upwards [hGae] with t ht using (hact _ t ht).symm
  · -- (4'): signed co-area identity for `q_ω 1_{a<f<b}`, with `f ≡ t` on `Mₜ` and
    -- `|g| ζ'(ω) = ξ₀(g♭ ∧ ω)`
    have hS : MeasurableSet {x | a < f x ∧ f x < b} :=
      (measurableSet_lt measurable_const hfm).inter (measurableSet_lt hfm measurable_const)
    have hq'fin : ∫⁻ x in RT.carrier, ‖g x‖ₑ * ‖{x | a < f x ∧ f x < b}.indicator
        (fun x => (RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)) x‖ₑ
          ∂μHE[n + 1] ≠ ∞ := by
      refine ne_top_of_le_ne_top (hqfin ω) (lintegral_mono fun x => ?_)
      by_cases hx : x ∈ {x | a < f x ∧ f x < b}
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, enorm_zero, mul_zero]
        exact zero_le
    obtain ⟨-, heq⟩ := hsig _ ((hqm ω).indicator hS) hq'fin
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo, ← setIntegral_indicator hS]
    calc ∫ s, (Ioo a b).indicator (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n)) s
        = ∫ s, ∫ x in RT.carrier ∩ {x | g x ≠ 0} ∩ f ⁻¹' {s}, {x | a < f x ∧ f x < b}.indicator
            (fun x => (RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)) x
              ∂μHE[n] := by
          refine integral_congr_ae ?_
          filter_upwards [hGae] with s hs
          by_cases hs' : s ∈ Ioo a b
          · rw [indicator_of_mem hs', hact _ s hs]
            refine setIntegral_congr_fun (hMt s) fun x hx => ?_
            have hfx : f x = s := hx.2
            have hxS : x ∈ {x | a < f x ∧ f x < b} := by
              show a < f x ∧ f x < b
              rw [hfx]
              exact hs'
            rw [indicator_of_mem hxS]
          · rw [indicator_of_notMem hs']
            refine (setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_).symm
            have hfx : f x = s := hx.2
            have hxS : x ∉ {x | a < f x ∧ f x < b} := by
              show ¬(a < f x ∧ f x < b)
              rw [hfx]
              exact hs'
            exact indicator_of_notMem hxS _
      _ = ∫ x in RT.carrier, ‖g x‖ * {x | a < f x ∧ f x < b}.indicator
            (fun x => (RT.mult x : ℝ) * ζ' x ((ω : DifferentialForm (Euclid P) n) x)) x
              ∂μHE[n + 1] := heq
      _ = ∫ x in RT.carrier, {x | a < f x ∧ f x < b}.indicator (fun x => (RT.mult x : ℝ) *
            RT.orient x (ContinuousAlternatingMap.alternatizeUncurryFin
              ((innerSL ℝ (g x)).smulRight ((ω : DifferentialForm (Euclid P) n) x)))) x
                ∂μHE[n + 1] := by
          refine integral_congr_ae ?_
          filter_upwards [hξξ₀] with x hx
          by_cases hxS : x ∈ {x | a < f x ∧ f x < b}
          · rw [indicator_of_mem hxS, indicator_of_mem hxS, hx, ← hζ'g x]
            ring
          · rw [indicator_of_notMem hxS, indicator_of_notMem hxS, mul_zero]

/-- **Simon Ch. 6, 4.4–4.5(2) for an integer multiplicity `T = τ(M, θ, ξ)` and a Lipschitz `f`**
(for a.e. `t`, `R_t = (M ∩ {g ≠ 0} ∩ f⁻¹(t), θ, ξ⌞ν)` with `ν = g/|g|`).
`dor_lmbsf_tangential_gradient` gives the tangential gradient `g` of `f` along `M`: `|g| ≤ L`,
`g ∈ TₓM`, the co-area formula, rectifiable slices with tangent planes `TₓM ∩ g(x)^⊥`, and the
weak limit of the gradients of `C¹` approximations of `γ_{a,b} ∘ f`.  `dor_lmbsf_slice_imreps`
builds the slices, with (1)–(3) and `∫_a^b τ(R_s)(ω) ds = ∫_{M ∩ {a < f < b}} θ ξ(g♭ ∧ ω) dH^{n+1}`
(co-area, Simon 4.2).  `dor_lmbsf_lipschitz_cutoff_leibniz` is the Leibniz rule
`∂T(γω) = T(dγ ∧ ω) + T(γ dω)` for the Lipschitz cut-off `γ = γ_{a,b} ∘ f`, with
`T(dγ ∧ ω) = −(b − a)⁻¹ ∫_{M ∩ {a < f < b}} θ ξ(g♭ ∧ ω) dH^{n+1}`; solving it for this middle term
gives (4). -/
theorem Submission.dor_lmbs_imrep_slice_family : (∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (n + 1)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → RT.Represents T → RB.Represents T.boundary → LipschitzWith L f → ∃ Rs : ℝ → IMRep U n, (∀ t, (Rs t).carrier ⊆ f ⁻¹' {t}) ∧ (∀ W : Set (Euclid P), MeasurableSet W → AEMeasurable (fun t => (Rs t).measure W) ∧ ∫⁻ t, (Rs t).measure W ≤ (L : ℝ≥0∞) * RT.measure W) ∧ (∀ ω : TestFormOn U n, Integrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) ∧ ∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) := by
  intro hTL P n U T RT RB f L hU hRT hRB hf
  -- the tangential gradient `g` of `f` along `M`
  obtain ⟨g, hgm, hgL, hgtan, hcoarea, hrect, hslice, hweak⟩ :=
    Submission.dor_lmbsf_tangential_gradient hTL P n U RT f L hU hf
  -- the slices `R_t`, conclusions (1)–(3), and `∫_a^b τ(R_s)(ω) ds` as a middle term
  obtain ⟨Rs, hcarrier, hmass, hint, hmiddle⟩ :=
    Submission.dor_lmbsf_slice_imreps P n U RT f L g hU hf hgm hgL hgtan hcoarea hrect hslice
  refine ⟨Rs, hcarrier, hmass, hint, fun ω a b hab => ?_⟩
  -- (4): the Leibniz identity `A = B - (b - a)⁻¹ * S` solved for `S = (b - a) * (B - A)`
  rw [hmiddle ω a b hab, Submission.dor_lmbsf_lipschitz_cutoff_leibniz P n U T RT RB f L g hU hRT
    hRB hf hgm hgL hweak ω a b hab, sub_sub_cancel, mul_inv_cancel_left₀ (sub_pos.mpr hab).ne']
/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets
`Kᵢ = B̄(0, i + 1) ∩ {x : 1 / (i + 1) ≤ dist(x, y) for all y ∉ U}`: each `Kᵢ ⊆ U` (take `y = x`),
and a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and a radius `R` with
`C ⊆ B̄(0, R)`, so `C ⊆ Kᵢ` once `1 / (i + 1) < δ` and `R ≤ i + 1`. -/
theorem Submission.dor_lmbs_tfa_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) ((i : ℝ) + 1) ∩ ⋂ y ∈ Uᶜ, {x | 1 / ((i : ℝ) + 1) ≤ dist x y},
    fun i => ?_, fun i => ?_, fun C hC hCU => ?_⟩
  · exact (isCompact_closedBall _ _).inter_right
      (isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  · -- `x ∉ U` would give `1 / (i + 1) ≤ dist x x = 0`
    intro x hx
    by_contra hxU
    have h : 1 / ((i : ℝ) + 1) ≤ dist x x := mem_iInter₂.1 hx.2 x hxU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    obtain ⟨M, hM⟩ := exists_nat_ge R
    have hNi : (N : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_left N M
    have hMi : (M : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_right N M
    refine ⟨max N M, fun x hx => ⟨?_, mem_iInter₂.2 fun y hy => ?_⟩⟩
    · have hxR := mem_closedBall.1 (hR hx)
      rw [mem_closedBall]
      linarith
    · -- `y ∉ thickening δ C` gives `δ ≤ dist x y`
      have hxy : δ ≤ dist x y := by
        by_contra h
        exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
      have hle : 1 / (((max N M : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      show 1 / (((max N M : ℕ) : ℝ) + 1) ≤ dist x y
      linarith
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_lmbs_tfa_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
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

/-- Test forms supported in a fixed compact `K` have a countable subfamily `D` approximating every
such `ω` together with `dω`, uniformly on `ℝᴾ`.  The covector spaces are finite-dimensional
(`dor_lmbs_tfa_covector_finiteDimensional`), so `C(K, Λⁿ × Λⁿ⁺¹)` is second countable; pull back
a countable dense subset of the image of `X = {ω : spt ω ⊆ K}` under `Φ ω = (ω, dω)|_K`.  On `K`
the pointwise distances are at most the uniform distance; off `K` all four values vanish. -/
theorem Submission.dor_lmbs_tfa_fixed_support_dense : ∀ (P n : ℕ) (U K : Set (Euclid P)), IsCompact K → ∃ D : Set (TestFormOn U n), D.Countable ∧ (∀ η ∈ D, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ η ∈ D, (∀ x, dist ((ω : DifferentialForm (Euclid P) n) x) ((η : DifferentialForm (Euclid P) n) x) < ε) ∧ ∀ x, dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) (exteriorDerivative (η : DifferentialForm (Euclid P) n) x) < ε := by
  intro P n U K hK
  -- Step 1: a form supported in `K` vanishes off `K`, and so does its exterior derivative
  have hzero : ∀ η : TestFormOn U n, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K →
      ∀ x ∉ K, (η : DifferentialForm (Euclid P) n) x = 0 ∧
        exteriorDerivative (η : DifferentialForm (Euclid P) n) x = 0 := fun η hη x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (hη h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hη (tsupport_exteriorDerivative_subset _ h))⟩
  -- Step 2: `Λⁿ` and `Λⁿ⁺¹` are finite-dimensional, hence proper and second countable
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P n
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P (n + 1)
  have : ProperSpace (Covector (Euclid P) n) := FiniteDimensional.proper_real _
  have : ProperSpace (Covector (Euclid P) (n + 1)) := FiniteDimensional.proper_real _
  have : SecondCountableTopology (Covector (Euclid P) n) := secondCountable_of_proper
  have : SecondCountableTopology (Covector (Euclid P) (n + 1)) := secondCountable_of_proper
  -- Step 3: `K` is compact, so `C(K, Λⁿ × Λⁿ⁺¹)` carries the sup metric, and it is second
  -- countable: up to `ε`, `f` is determined by a modulus `j` of uniform continuity at scale `ε / 4`
  -- and by the indices, in a dense sequence `s`, of `ε / 4`-approximations of its values on a
  -- finite `1 / (j + 1)`-net `t j` of `K`
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := by
    refine Metric.secondCountable_of_countable_discretization
      (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1))) fun ε hε => ?_
    obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq
      (Covector (Euclid P) n × Covector (Euclid P) (n + 1))
    choose r hr using fun y : Covector (Euclid P) n × Covector (Euclid P) (n + 1) =>
      hs.exists_dist_lt y (by positivity : (0 : ℝ) < ε / 4)
    have hnet : ∀ j : ℕ, ∃ t : Finset K, ∀ x : K, ∃ p ∈ t, dist x p < 1 / ((j : ℝ) + 1) := by
      intro j
      obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (univ : Set K)).elim_nhds_subcover
        (fun x => ball x (1 / ((j : ℝ) + 1))) fun x _ => ball_mem_nhds x (by positivity)
      exact ⟨t, fun x => by simpa using ht (mem_univ x)⟩
    choose t ht using hnet
    have hmod : ∀ f : C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)), ∃ j : ℕ,
        ∀ x y : K, dist x y < 1 / ((j : ℝ) + 1) → dist (f x) (f y) < ε / 4 := by
      intro f
      obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
        (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 4) (by positivity)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, fun x y hxy => hfδ (hxy.trans hj)⟩
    choose J hJ using hmod
    refine ⟨ℕ × List ℕ, inferInstance, fun f => (J f, (t (J f)).toList.map fun p => r (f p)),
      fun f g hfg => (ContinuousMap.dist_le hε.le).2 fun x => ?_⟩
    obtain ⟨hj, hl⟩ := Prod.mk.inj hfg
    rw [← hj] at hl
    -- `x` is `1 / (j + 1)`-close to a net point `p`, where `f p` and `g p` have a common index
    obtain ⟨p, hp, hxp⟩ := ht (J f) x
    have hrp : r (f p) = r (g p) := List.map_inj_left.1 hl p (Finset.mem_toList.2 hp)
    have h₁ := hJ f x p hxp
    have h₂ := hr (f p)
    have h₃ := hr (g p)
    have h₄ := hJ g x p (hj ▸ hxp)
    rw [hrp] at h₂
    rw [dist_comm] at h₃ h₄
    linarith [dist_triangle4 (f x) (f p) (s (r (g p))) (g x),
      dist_triangle (s (r (g p))) (g p) (g x)]
  -- Step 4: `Φ ω = (ω, dω)|_K`
  let Φ : TestFormOn U n → C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := fun ω =>
    ⟨fun x => ((ω : DifferentialForm (Euclid P) n) x,
        exteriorDerivative (ω : DifferentialForm (Euclid P) n) x),
      (ω.property.1.1.continuous.prodMk
        (exteriorDerivative_isTestForm ω.property.1).1.continuous).comp continuous_subtype_val⟩
  let X : Set (TestFormOn U n) := {ω | tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K}
  -- Step 5: a countable `T ⊆ Φ(X)` dense in `Φ(X)`, and a choice `σ` of preimages in `X`
  obtain ⟨T, hTc, hTX, hXT⟩ := TopologicalSpace.exists_countable_dense_subset (Φ '' X)
  have hT : ∀ t ∈ T, ∃ η, η ∈ X ∧ Φ η = t := fun t ht => hTX ht
  choose! σ hσX hσΦ using hT
  -- Step 6: `D = σ(T)` is countable and supported in `K`
  refine ⟨σ '' T, hTc.image σ, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hσX t ht
  -- Step 7: pick `t ∈ T` with `dist (Φ ω) t < ε` and put `η = σ t`
  intro ω hω ε hε
  obtain ⟨t, ht, hdist⟩ := (Metric.mem_closure_iff
    (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)))).1 (hXT ⟨ω, hω, rfl⟩) ε hε
  rw [← hσΦ t ht] at hdist
  have key : ∀ x, dist ((ω : DifferentialForm (Euclid P) n) x)
      ((σ t : DifferentialForm (Euclid P) n) x) < ε ∧
      dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x)
        (exteriorDerivative (σ t : DifferentialForm (Euclid P) n) x) < ε := by
    intro x
    by_cases hx : x ∈ K
    · -- (a) on `K`: both distances are at most `dist (Φ ω) (Φ η) < ε`
      have h := (ContinuousMap.dist_apply_le_dist (f := Φ ω) (g := Φ (σ t)) ⟨x, hx⟩).trans_lt hdist
      rw [Prod.dist_eq] at h
      exact ⟨(le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩
    · -- (b) off `K`: all four values vanish
      obtain ⟨h₁, h₂⟩ := hzero ω hω x hx
      obtain ⟨h₃, h₄⟩ := hzero (σ t) (hσX t ht) x hx
      rw [h₁, h₂, h₃, h₄, dist_self, dist_self]
      exact ⟨hε, hε⟩
  exact ⟨σ t, ⟨t, ht, rfl⟩, fun x => (key x).1, fun x => (key x).2⟩

/-- **A countable family of test forms, dense for `ω` and `dω` with common compact supports**
(Simon Ch. 6, proof of 4.5(2), p. 157: "a countable dense set of `ω ∈ 𝒟ⁿ(U)`").  Take the
compact exhaustion `Kᵢ` of `U` (`dor_lmbs_tfa_compact_exhaustion`) and, for each `i`, a
countable `Dᵢ` approximating every `ω` with `spt ω ⊆ Kᵢ` uniformly together with `dω`
(`dor_lmbs_tfa_fixed_support_dense`); then `D = ⋃ᵢ Dᵢ`.  Given `ω`, `spt ω ⊆ Kᵢ` for some `i`,
and `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω` gives `ωₖ → ω`, `dωₖ → dω` uniformly. -/
theorem Submission.dor_lmbs_testForm_countable_approx : ∀ (P n : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ D : Set (TestFormOn U n), D.Countable ∧ ∀ ω : TestFormOn U n, ∃ (K : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), IsCompact K ∧ K ⊆ U ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K ∧ (∀ k, ωs k ∈ D) ∧ (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ K) ∧ TendstoUniformly (fun k x => (ωs k : DifferentialForm (Euclid P) n) x) (ω : DifferentialForm (Euclid P) n) atTop ∧ TendstoUniformly (fun k x => exteriorDerivative (ωs k : DifferentialForm (Euclid P) n) x) (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) atTop := by
  intro P n U hU
  -- step 1: the compact exhaustion `Kᵢ` of `U`
  obtain ⟨K, hKc, hKU, hKex⟩ := Submission.dor_lmbs_tfa_compact_exhaustion P U hU
  -- steps 2–4: a countable `Dᵢ` for the test forms supported in `Kᵢ`
  choose D hDc hDK hDω using fun i =>
    Submission.dor_lmbs_tfa_fixed_support_dense P n U (K i) (hKc i)
  -- step 5: `D = ⋃ᵢ Dᵢ`
  refine ⟨⋃ i, D i, Set.countable_iUnion hDc, fun ω => ?_⟩
  -- step 6: `spt ω` is a compact subset of `U`, so it lies in some `Kᵢ`
  obtain ⟨i, hi⟩ :=
    hKex (tsupport (ω : DifferentialForm (Euclid P) n)) ω.property.1.2 ω.property.2
  -- `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω`
  choose ωs hωsD hωs using fun k : ℕ =>
    hDω i ω hi (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε := fun ε hε => by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact (Nat.one_div_le_one_div hk).trans_lt hN
  refine ⟨K i, ωs, hKc i, hKU i, hi, fun k => Set.mem_iUnion.2 ⟨i, hωsD k⟩,
    fun k => hDK i (ωs k) (hωsD k), ?_, ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).1 x).trans hk
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).2 x).trans hk

/-- **From averaged slice identities to the pointwise slice identity** (Simon Ch. 6, end of the
proof of 4.5(2), with Remark 4.2).  If `s ↦ τ(R_s)(ω)` is locally integrable and its averages over
`[a, b]` are the cut-off integrals `∫_M θ γ_{a,b}(f) ⟨dω, ξ⟩ − ∫_{M'} θ' γ_{a,b}(f) ⟨ω, ξ'⟩`, then
for a.e. `t` and every `ω`, `τ(R_t)(ω) = ∫_{M ∩ {f < t}} θ ⟨dω, ξ⟩ − ∫_{M' ∩ {f < t}} θ' ⟨ω, ξ'⟩`.
For a fixed `ω` this follows from the Lebesgue differentiation theorem (left averages over
`[y, t]`, `y ↑ t`) and dominated convergence of the cut-offs `γ_{y,t}(f) → 1_{f < t}`; the null set
is made independent of `ω` with the countable family of `dor_lmbs_testForm_countable_approx`, and
the identity passes to all `ω` by dominated convergence along `ω_k → ω`, `dω_k → dω` uniformly with
supports in a common compact set. -/
theorem Submission.dor_lmbs_slice_identity_of_averages : ∀ (P n : ℕ) (U : Set (Euclid P)) (RT : IMRep U (n + 1)) (RB : IMRep U n) (Rs : ℝ → IMRep U n) (f : Euclid P → ℝ), IsOpen U → Measurable f → (∀ ω : TestFormOn U n, LocallyIntegrable (fun s => (Rs s).action (ω : DifferentialForm (Euclid P) n))) → (∀ (ω : TestFormOn U n) (a b : ℝ), a < b → ∫ s in a..b, (Rs s).action (ω : DifferentialForm (Euclid P) n) = (b - a) * ((∫ x in RT.carrier, (RT.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier, (RB.mult x : ℝ) * min 1 (max 0 ((b - f x) / (b - a))) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n])) → ∀ᵐ t, ∀ ω : TestFormOn U n, (Rs t).action (ω : DifferentialForm (Euclid P) n) = (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) * RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) - ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) * RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] := by
  intro P n U RT RB Rs f hU hf hloc havg
  -- Step 1: pairings with a triple `R = (N, φ, ζ)`.  A unit orientation has norm at most `1`, so
  -- `|φ ζ(β)| ≤ C φ 1_K` when `‖β‖ ≤ C` and `β = 0` off the compact `K ⊆ U`.
  have horient : ∀ (k : ℕ) (R : IMRep U k), ∀ᵐ x ∂(μHE[k].restrict R.carrier),
      ∀ α : Covector (Euclid P) k, ‖R.orient x α‖ ≤ ‖α‖ := by
    intro k R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hα : ‖α τ‖ ≤ ‖α‖ := by simpa [hτ.1] using α.le_opNorm τ
    rcases hξ with hξ | hξ <;> simpa [hξ α] using hα
  have hmult : ∀ (k : ℕ) (R : IMRep U k), Measurable fun x => (R.mult x : ℝ) :=
    fun k R => measurable_from_nat.comp R.measurable_mult
  have hmultK : ∀ (k : ℕ) (R : IMRep U k) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) (μHE[k].restrict R.carrier) := by
    intro k R K hK hKU
    rw [integrable_indicator_iff hK.measurableSet, IntegrableOn,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    refine ⟨(hmult k R).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Nat.cast_nonneg _)]
    simpa only [ENNReal.ofReal_natCast] using
      lt_top_iff_ne_top.2 (R.locallyIntegrable_mult K hK hKU)
  have hmeas : ∀ (k : ℕ) (R : IMRep U k) (β : Euclid P → Covector (Euclid P) k), Continuous β →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (β x))
        (μHE[k].restrict R.carrier) :=
    fun k R β hβ => (hmult k R).aestronglyMeasurable.mul
      (Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P k) (v : Covector (Euclid P) k) => L v)
        (continuous_fst.clm_apply continuous_snd) R.aestronglyMeasurable_orient
        hβ.aestronglyMeasurable)
  have hbound : ∀ (k : ℕ) (R : IMRep U k) (K : Set (Euclid P))
      (β : Euclid P → Covector (Euclid P) k) (C : ℝ), (∀ x, ‖β x‖ ≤ C) →
      (∀ x, x ∉ K → β x = 0) → ∀ᵐ x ∂(μHE[k].restrict R.carrier),
        ‖(R.mult x : ℝ) * R.orient x (β x)‖ ≤ C * K.indicator (fun x => (R.mult x : ℝ)) x := by
    intro k R K β C hC hK
    filter_upwards [horient k R] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm C]
      exact mul_le_mul_of_nonneg_left ((hx _).trans (hC x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, hK x hxK, map_zero, mul_zero, norm_zero, mul_zero]
  have hint : ∀ (k : ℕ) (R : IMRep U k) (K : Set (Euclid P))
      (β : Euclid P → Covector (Euclid P) k), IsCompact K → K ⊆ U → Continuous β →
      (∀ x, x ∉ K → β x = 0) →
      Integrable (fun x => (R.mult x : ℝ) * R.orient x (β x)) (μHE[k].restrict R.carrier) := by
    intro k R K β hK hKU hβ hβK
    obtain ⟨C, hC⟩ := hβ.bounded_above_of_compact_support (HasCompactSupport.intro hK hβK)
    exact ((hmultK k R K hK hKU).const_mul C).mono' (hmeas k R β hβ) (hbound k R K β C hC hβK)
  -- dominated convergence along `β_j → β` uniformly, with supports in a common compact `K`
  have hlim : ∀ (k : ℕ) (R : IMRep U k) (ν : Measure (Euclid P)) (K : Set (Euclid P))
      (βs : ℕ → Euclid P → Covector (Euclid P) k) (β : Euclid P → Covector (Euclid P) k),
      ν ≤ μHE[k].restrict R.carrier → IsCompact K → K ⊆ U → Continuous β →
      (∀ j, Continuous (βs j)) → (∀ x, x ∉ K → β x = 0) → (∀ j x, x ∉ K → βs j x = 0) →
      TendstoUniformly βs β atTop →
      Tendsto (fun j => ∫ x, (R.mult x : ℝ) * R.orient x (βs j x) ∂ν) atTop
        (𝓝 (∫ x, (R.mult x : ℝ) * R.orient x (β x) ∂ν)) := by
    intro k R ν K βs β hν hK hKU hβ hβs hβK hβsK hconv
    obtain ⟨C, hC⟩ := hβ.bounded_above_of_compact_support (HasCompactSupport.intro hK hβK)
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (C + 1) * K.indicator (fun x => (R.mult x : ℝ)) x)
      (Eventually.of_forall fun j => (hmeas k R (βs j) (hβs j)).mono_measure hν) ?_
      (((hmultK k R K hK hKU).const_mul (C + 1)).mono_measure hν)
      (Eventually.of_forall fun x => tendsto_const_nhds.mul
        (((R.orient x).continuous.tendsto (β x)).comp (hconv.tendsto_at x)))
    filter_upwards [Metric.tendstoUniformly_iff.1 hconv 1 one_pos] with j hj
    refine ae_mono hν (hbound k R K (βs j) (C + 1) (fun x => ?_) (hβsK j))
    have hjx : ‖β x - βs j x‖ < 1 := by simpa [dist_eq_norm] using hj x
    calc ‖βs j x‖ = ‖β x - (β x - βs j x)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖β x‖ + ‖β x - βs j x‖ := norm_sub_le _ _
      _ ≤ C + 1 := add_le_add (hC x) hjx.le
  -- Step 2: the cut-offs `γ_{y,t}(f) = min 1 (max 0 ((t - f) / (t - y)))` lie in `[0, 1]` and
  -- tend to `1_{f < t}` as `y ↑ t`.
  have hcut : ∀ (k : ℕ) (R : IMRep U k) (K : Set (Euclid P))
      (β : Euclid P → Covector (Euclid P) k) (t : ℝ), IsCompact K → K ⊆ U → Continuous β →
      (∀ x, x ∉ K → β x = 0) →
      Tendsto (fun y => ∫ x in R.carrier,
          (R.mult x : ℝ) * min 1 (max 0 ((t - f x) / (t - y))) * R.orient x (β x) ∂μHE[k])
        (𝓝[<] t)
        (𝓝 (∫ x in R.carrier ∩ {x | f x < t}, (R.mult x : ℝ) * R.orient x (β x) ∂μHE[k])) := by
    intro k R K β t hK hKU hβ hβK
    rw [← setIntegral_indicator
      (measurableSet_lt hf measurable_const : MeasurableSet {x | f x < t})]
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖(R.mult x : ℝ) * R.orient x (β x)‖) (Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => Eventually.of_forall fun x => ?_)
      (hint k R K β hK hKU hβ hβK).norm (Eventually.of_forall fun x => ?_)
    · have hγ : Measurable fun x => min (1 : ℝ) (max 0 ((t - f x) / (t - y))) :=
        measurable_const.min (measurable_const.max ((measurable_const.sub hf).div_const _))
      have h := (hmeas k R β hβ).mul hγ.aestronglyMeasurable
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
      ring
    · have h0 : 0 ≤ min (1 : ℝ) (max 0 ((t - f x) / (t - y))) :=
        le_min zero_le_one (le_max_left _ _)
      rw [mul_right_comm, norm_mul, Real.norm_of_nonneg h0]
      exact mul_le_of_le_one_right (norm_nonneg _) (min_le_left _ _)
    · by_cases hx : f x < t
      · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hx] with y hy
        have h1 : 1 ≤ (t - f x) / (t - y) :=
          (one_le_div (sub_pos.2 hy.2)).2 (by linarith [hy.1])
        rw [max_eq_right (zero_le_one.trans h1), min_eq_left h1, mul_one]
      · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        have h1 : (t - f x) / (t - y) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith [not_lt.1 hx]) (sub_pos.2 hy).le
        rw [max_eq_left h1, min_eq_right zero_le_one, mul_zero, zero_mul]
  -- Step 3: for a fixed `ω`, Lebesgue differentiation on `[y, t]`, `y ↑ t`, with (ii) for
  -- `(a, b) = (y, t)` identifies `τ(R_t)(ω)` with the limit of Step 2 off a null set.
  have hpt : ∀ ω : TestFormOn U n, ∀ᵐ t, (Rs t).action (ω : DifferentialForm (Euclid P) n) =
      (∫ x in RT.carrier ∩ {x | f x < t}, (RT.mult x : ℝ) *
          RT.orient x (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) ∂μHE[n + 1]) -
        ∫ x in RB.carrier ∩ {x | f x < t}, (RB.mult x : ℝ) *
          RB.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] := by
    intro ω
    have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
        tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := hω.1.2
    filter_upwards
      [(IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_average (hloc ω)]
      with t ht
    refine tendsto_nhds_unique ((ht.comp (Real.tendsto_Icc_vitaliFamily_left t)).congr' ?_)
      ((hcut (n + 1) RT _ _ t hK hω.2
        (ContDiff.continuous (exteriorDerivative_isTestForm hω.1).1)
        fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
          hx (tsupport_exteriorDerivative_subset _ h)).sub
      (hcut n RB _ _ t hK hω.2 (ContDiff.continuous hω.1.1)
        fun x hx => image_eq_zero_of_notMem_tsupport hx))
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < t)
    simp only [Function.comp_apply]
    rw [setAverage_eq, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_pos.2 hy).le,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hy.le, havg ω y t hy,
      smul_eq_mul, inv_mul_cancel_left₀ (sub_pos.2 hy).ne']
  -- Steps 4–6: one null set for the countable family `D`; every `ω` is a limit of forms in `D`
  -- with `ω_k → ω`, `dω_k → dω` uniformly and supports in one compact `K ⊆ U`.
  obtain ⟨D, hDc, hD⟩ := Submission.dor_lmbs_testForm_countable_approx P n U hU
  filter_upwards [(ae_ball_iff hDc).2 fun η _ => hpt η] with t ht ω
  obtain ⟨K, ωs, hK, hKU, hωK, hωsD, hωsK, hconv, hdconv⟩ := hD ω
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) := ω.2.1
  have hωs : ∀ j, IsTestForm (ωs j : DifferentialForm (Euclid P) n) := fun j => (ωs j).2.1
  have hA := hlim n (Rs t) _ K (fun j => (ωs j : DifferentialForm (Euclid P) n)) _ le_rfl hK hKU
    (ContDiff.continuous hω.1) (fun j => ContDiff.continuous (hωs j).1)
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hωK h))
    (fun j x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hωsK j h)) hconv
  have hB := (hlim (n + 1) RT (μHE[n + 1].restrict (RT.carrier ∩ {x | f x < t})) K
      (fun j => exteriorDerivative (ωs j : DifferentialForm (Euclid P) n)) _
      (Measure.restrict_mono inter_subset_left le_rfl) hK hKU
      (ContDiff.continuous (exteriorDerivative_isTestForm hω).1)
      (fun j => ContDiff.continuous (exteriorDerivative_isTestForm (hωs j)).1)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
        hx (hωK (tsupport_exteriorDerivative_subset _ h)))
      (fun j x hx => image_eq_zero_of_notMem_tsupport fun h =>
        hx (hωsK j (tsupport_exteriorDerivative_subset _ h))) hdconv).sub
    (hlim n RB (μHE[n].restrict (RB.carrier ∩ {x | f x < t})) K
      (fun j => (ωs j : DifferentialForm (Euclid P) n)) _
      (Measure.restrict_mono inter_subset_left le_rfl) hK hKU (ContDiff.continuous hω.1)
      (fun j => ContDiff.continuous (hωs j).1)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hωK h))
      (fun j x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hωsK j h)) hconv)
  exact tendsto_nhds_unique hA (hB.congr fun j => (ht (ωs j) (hωsD j)).symm)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
