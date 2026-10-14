import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward

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

/-- **Simon Ch. 2, 4.4** (graph chart): near `y ∈ M`, an embedded `C¹` submanifold `M ⊆ ℝᴾ` of
dimension `m` is the graph `F(a) = y + ιa + ι'u(a)` of a `C¹` map `u` with `u(0) = 0` and small
slope over its tangent plane `T = range ι` (`ι'` onto `Tᗮ`): `M` meets the cylinder
`Z = {y + ιa + ι'b : ‖a‖ < s, ‖b‖ < t}` exactly in `F(B_s(0))`, `F` is an injective immersion,
proper into `Z`, and `T_{F(a)}M = range DF(a)`.  Take isometries onto `T = range Dψ(v₀)` and `Tᗮ`
for a chart `ψ` with `ψ(v₀) = y`, invert `φ = ι*(ψ − y)` near `v₀` by the inverse function theorem
(inverse `χ`) and put `u = ι'*(ψ ∘ χ − y)`; properness of `ψ` shows that `M` near `y` is the image
under `ψ` of the domain of the local inverse. -/
theorem Submission.codim1_hcp_sr_graph_chart : ∀ (P m : ℕ) (M : Set (Euclid P)) (y : Euclid P), 1 ≤ m → IsEmbeddedSubmanifold 1 m M → y ∈ M → ∃ (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid (P - m) →ₗᵢ[ℝ] Euclid P), (∀ a b, inner ℝ (ι a) (ι' b) = 0) ∧ (∀ z : Euclid P, ∃ a b, z = ι a + ι' b) ∧ ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ (s t : ℝ) (u : Euclid m → Euclid (P - m)), 0 < s ∧ 0 < t ∧ s + t ≤ δ ∧ ContDiffOn ℝ 1 u (ball 0 s) ∧ u 0 = 0 ∧ (∀ a ∈ ball (0 : Euclid m) s, ‖fderiv ℝ u a‖ ≤ ε ∧ ‖u a‖ < t) ∧ IsOpen {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} ∧ M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} = (fun a => y + ι a + ι' (u a)) '' ball 0 s ∧ InjOn (fun a => y + ι a + ι' (u a)) (ball 0 s) ∧ (∀ a ∈ ball (0 : Euclid m) s, Injective (fderiv ℝ (fun a => y + ι a + ι' (u a)) a) ∧ tangentSpace M (y + ι a + ι' (u a)) = Set.range (fderiv ℝ (fun a => y + ι a + ι' (u a)) a)) ∧ ∀ K ⊆ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b}, IsCompact K → IsCompact (ball (0 : Euclid m) s ∩ (fun a => y + ι a + ι' (u a)) ⁻¹' K) := by
  intro P m M y _ hM hy
  obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hDψ⟩ := hM y hy
  have hψ1 : ContDiffOn ℝ 1 ψ V := by simpa using hψ
  have hψat : ∀ v ∈ V, ContDiffAt ℝ 1 ψ v := fun v hv => hψ1.contDiffAt (hV.mem_nhds hv)
  have hψd : ∀ v ∈ V, HasFDerivAt ψ (fderiv ℝ ψ v) v := fun v hv =>
    ((hψat v hv).differentiableAt one_ne_zero).hasFDerivAt
  obtain ⟨v₀, hv₀V, hψv₀⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hyW, hy⟩
  -- the tangent plane `T = range Dψ(v₀)` and its orthogonal complement
  set D := fderiv ℝ ψ v₀
  set T : Submodule ℝ (Euclid P) := LinearMap.range (D : Euclid m →ₗ[ℝ] Euclid P) with hT
  have hTrank : Module.finrank ℝ T = m := by
    rw [hT, LinearMap.finrank_range_of_inj (f := (D : Euclid m →ₗ[ℝ] Euclid P)) (hDψ v₀ hv₀V)]
    simp
  have hTorank : Module.finrank ℝ Tᗮ = P - m := by
    have := T.finrank_add_finrank_orthogonal
    rw [hTrank, finrank_euclideanSpace_fin] at this
    omega
  let e : T ≃ₗᵢ[ℝ] Euclid m := ((stdOrthonormalBasis ℝ T).reindex (finCongr hTrank)).repr
  let e' : Tᗮ ≃ₗᵢ[ℝ] Euclid (P - m) :=
    ((stdOrthonormalBasis ℝ Tᗮ).reindex (finCongr hTorank)).repr
  let ι : Euclid m →ₗᵢ[ℝ] Euclid P := T.subtypeₗᵢ.comp e.symm.toLinearIsometry
  let ι' : Euclid (P - m) →ₗᵢ[ℝ] Euclid P := Tᗮ.subtypeₗᵢ.comp e'.symm.toLinearIsometry
  have hιT : ∀ a, ι a ∈ T := fun a => (e.symm a).2
  have hι'T : ∀ b, ι' b ∈ Tᗮ := fun b => (e'.symm b).2
  have horth : ∀ a b, inner ℝ (ι a) (ι' b) = 0 := fun a b =>
    Submodule.inner_right_of_mem_orthogonal (hιT a) (hι'T b)
  have hspan : ∀ z : Euclid P, ∃ a b, z = ι a + ι' b := by
    intro z
    obtain ⟨w, hw, w', hw', rfl⟩ := T.exists_add_mem_mem_orthogonal z
    refine ⟨e ⟨w, hw⟩, e' ⟨w', hw'⟩, ?_⟩
    simp [ι, ι']
  have hDι : ∀ w, ∃ a, D w = ι a := fun w =>
    ⟨e ⟨D w, LinearMap.mem_range_self _ w⟩, by simp [ι]⟩
  -- the projections `π = ι*`, `π' = ι'*`
  set π : Euclid P →L[ℝ] Euclid m := ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hπ
  set π' : Euclid P →L[ℝ] Euclid (P - m) :=
    ContinuousLinearMap.adjoint ι'.toContinuousLinearMap with hπ'
  have hπι : ∀ a, π (ι a) = a := fun a => ext_inner_right ℝ fun a' => by
    rw [hπ, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      ι.inner_map_map]
  have hπι' : ∀ b, π (ι' b) = 0 := fun b => ext_inner_right ℝ fun a' => by
    rw [hπ, ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      inner_zero_left, real_inner_comm, horth]
  have hπ'ι : ∀ a, π' (ι a) = 0 := fun a => ext_inner_right ℝ fun b' => by
    rw [hπ', ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      inner_zero_left, horth]
  have hπ'ι' : ∀ b, π' (ι' b) = b := fun b => ext_inner_right ℝ fun b' => by
    rw [hπ', ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
      ι'.inner_map_map]
  have hdec : ∀ z, z = ι (π z) + ι' (π' z) := by
    intro z
    obtain ⟨a, b, rfl⟩ := hspan z
    simp [hπι, hπι', hπ'ι, hπ'ι']
  -- `φ(v) = π(ψ(v) − y)` has the invertible derivative `π ∘ Dψ(v₀)` at `v₀`
  set φ : Euclid m → Euclid m := fun v => π (ψ v - y)
  have hφat : ContDiffAt ℝ 1 φ v₀ :=
    π.contDiff.contDiffAt.comp v₀ ((hψat v₀ hv₀V).sub contDiffAt_const)
  have hφinj : Injective (π ∘L D) := by
    intro w w' h
    obtain ⟨a, ha⟩ := hDι w
    obtain ⟨a', ha'⟩ := hDι w'
    have h' : a = a' := by simpa [ha, ha', hπι] using h
    exact hDψ v₀ hv₀V (by rw [ha, ha', h'])
  let L : Euclid m ≃L[ℝ] Euclid m :=
    (LinearEquiv.ofInjectiveEndo (π ∘L D : Euclid m →ₗ[ℝ] Euclid m) hφinj).toContinuousLinearEquiv
  have hL : (L : Euclid m →L[ℝ] Euclid m) = π ∘L D := by
    ext1 w; rfl
  have hφd : HasFDerivAt φ (L : Euclid m →L[ℝ] Euclid m) v₀ := by
    rw [hL]
    exact π.hasFDerivAt.comp v₀ ((hψd v₀ hv₀V).sub_const y)
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hφs : HasStrictFDerivAt φ (L : Euclid m →L[ℝ] Euclid m) v₀ :=
    hφat.hasStrictFDerivAt' hφd hn
  set PH := hφs.toOpenPartialHomeomorph φ
  have hv₀src : v₀ ∈ PH.source := hφs.mem_toOpenPartialHomeomorph_source
  have hφv₀ : φ v₀ = 0 := by simp [φ, hψv₀]
  have h0tgt : (0 : Euclid m) ∈ PH.target := by
    rw [← hφv₀]; exact hφs.image_mem_toOpenPartialHomeomorph_target
  set χ : Euclid m → Euclid m := ⇑PH.symm
  have hχ0 : χ 0 = v₀ := by
    rw [← hφv₀]; exact PH.left_inv hv₀src
  have hχat : ContDiffAt ℝ 1 χ 0 := by
    refine PH.contDiffAt_symm h0tgt (f₀' := L) ?_ ?_
    · rw [show PH.symm 0 = v₀ from hχ0]; exact hφd
    · rw [show PH.symm 0 = v₀ from hχ0]; exact hφat
  -- the graph function `u(a) = π'(ψ(χ(a)) − y)`
  set u : Euclid m → Euclid (P - m) := fun a => π' (ψ (χ a) - y)
  have hFψ : ∀ a ∈ PH.target, y + ι a + ι' (u a) = ψ (χ a) := by
    intro a ha
    have h1 : π (ψ (χ a) - y) = a := PH.right_inv ha
    have h2 : ψ (χ a) - y = ι a + ι' (u a) := by
      conv_lhs => rw [hdec (ψ (χ a) - y)]
      rw [h1]
    rw [add_assoc, ← h2]
    abel
  -- every point of `M` near `y` is `ψ(v)` with `v` in the source of the local inverse
  have hψcont : ContinuousOn ψ V := hψ1.continuousOn
  obtain ⟨r, hr, hrW⟩ : ∃ r, 0 < r ∧ closedBall y r ⊆ W :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hW.mem_nhds hyW)
  have hCc : IsCompact ((V ∩ ψ ⁻¹' closedBall y r) \ PH.source) :=
    (hprop _ hrW (isCompact_closedBall y r)).diff PH.open_source
  have hyC : y ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall y r) \ PH.source) := by
    rintro ⟨v, ⟨⟨hvV, -⟩, hvs⟩, hψv⟩
    exact hvs (hinj hvV hv₀V (hψv.trans hψv₀.symm) ▸ hv₀src)
  obtain ⟨r₁, hr₁, hr₁C⟩ :
      ∃ r₁ > 0, ball y r₁ ⊆ (ψ '' ((V ∩ ψ ⁻¹' closedBall y r) \ PH.source))ᶜ :=
    Metric.isOpen_iff.1 ((hCc.image_of_continuousOn
      (hψcont.mono fun v hv => hv.1.1)).isClosed.isOpen_compl) y hyC
  set r₀ := min r r₁
  have hr₀ : 0 < r₀ := lt_min hr hr₁
  have hr₀W : ball y r₀ ⊆ W :=
    (ball_subset_ball (min_le_left _ _)).trans (ball_subset_closedBall.trans hrW)
  have hloc : ∀ z ∈ M, z ∈ ball y r₀ → ∃ v ∈ PH.source, ψ v = z := by
    intro z hzM hz
    have hzW : z ∈ closedBall y r :=
      ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hz)
    obtain ⟨v, hvV, rfl⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hrW hzW, hzM⟩
    refine ⟨v, ?_, rfl⟩
    by_contra hvs
    exact hr₁C (ball_subset_ball (min_le_right _ _) hz) ⟨v, ⟨⟨hvV, hzW⟩, hvs⟩, rfl⟩
  -- `u` is `C¹` near `0`, `u(0) = 0` and `Du(0) = 0`
  have hev1 : ∀ᶠ a in 𝓝 (0 : Euclid m), a ∈ PH.target := PH.open_target.mem_nhds h0tgt
  have hev2 : ∀ᶠ a in 𝓝 (0 : Euclid m), χ a ∈ V :=
    hχat.continuousAt.preimage_mem_nhds (by rw [hχ0]; exact hV.mem_nhds hv₀V)
  have hev3 : ∀ᶠ a in 𝓝 (0 : Euclid m), ContDiffAt ℝ 1 χ a := hχat.eventually (by simp)
  have hev4 : ∀ᶠ a in 𝓝 (0 : Euclid m), ContDiffAt ℝ 1 u a := by
    filter_upwards [hev2, hev3] with a ha2 ha3
    exact π'.contDiff.contDiffAt.comp a (((hψat _ ha2).comp a ha3).sub contDiffAt_const)
  have hu0 : u 0 = 0 := by simp [u, hχ0, hψv₀]
  have hu0at : ContDiffAt ℝ 1 u 0 := hev4.self_of_nhds
  have hDu0 : fderiv ℝ u 0 = 0 := by
    have h1 : HasFDerivAt (ψ ∘ χ) (D ∘L fderiv ℝ χ 0) 0 := by
      have hψ' : HasFDerivAt ψ D (χ 0) := by rw [hχ0]; exact hψd v₀ hv₀V
      exact hψ'.comp 0 (hχat.differentiableAt one_ne_zero).hasFDerivAt
    have h2 : HasFDerivAt u (π' ∘L (D ∘L fderiv ℝ χ 0)) 0 :=
      π'.hasFDerivAt.comp 0 (h1.sub_const y)
    rw [h2.fderiv]
    ext1 w
    obtain ⟨a, ha⟩ := hDι (fderiv ℝ χ 0 w)
    simp [ha, hπ'ι]
  have hDucont : ContinuousAt (fderiv ℝ u) 0 :=
    (hu0at.fderiv_right (m := 0) (by norm_num)).continuousAt
  refine ⟨ι, ι', horth, hspan, fun ε δ hε hδ => ?_⟩
  -- choice of `t` and `s`
  set t := min δ r₀ / 2 with htdef
  have ht0 : 0 < t := by positivity
  have hev5 : ∀ᶠ a in 𝓝 (0 : Euclid m), ‖fderiv ℝ u a‖ < ε :=
    hDucont.norm.eventually_lt continuousAt_const (by rw [hDu0, norm_zero]; exact hε)
  have hev6 : ∀ᶠ a in 𝓝 (0 : Euclid m), ‖u a‖ < t :=
    hu0at.continuousAt.norm.eventually_lt continuousAt_const (by rw [hu0, norm_zero]; exact ht0)
  obtain ⟨s₁, hs₁, hs₁ball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (hev1.and (hev2.and (hev4.and (hev5.and hev6))))
  set s := min s₁ t
  have hs : 0 < s := lt_min hs₁ ht0
  have hst : s ≤ t := min_le_right _ _
  have htt : t + t = min δ r₀ := by rw [htdef]; ring
  have hsδ : s + t ≤ δ := by linarith [min_le_left δ r₀]
  have hsr₀ : s + t ≤ r₀ := by linarith [min_le_right δ r₀]
  have hgood : ∀ a ∈ ball (0 : Euclid m) s, a ∈ PH.target ∧ χ a ∈ V ∧ ContDiffAt ℝ 1 u a ∧
      ‖fderiv ℝ u a‖ < ε ∧ ‖u a‖ < t :=
    fun a ha => hs₁ball a (ball_subset_ball (min_le_left _ _) ha)
  -- the graph map `F(a) = y + ιa + ι'u(a)`
  have hπF : ∀ a, π (y + ι a + ι' (u a) - y) = a := by
    intro a
    have : y + ι a + ι' (u a) - y = ι a + ι' (u a) := by abel
    rw [this, map_add, hπι, hπι', add_zero]
  have hFψ' : ∀ a ∈ ball (0 : Euclid m) s, y + ι a + ι' (u a) = ψ (χ a) :=
    fun a ha => hFψ a (hgood a ha).1
  have hFM : ∀ a ∈ ball (0 : Euclid m) s, y + ι a + ι' (u a) ∈ M := by
    intro a ha
    have : ψ (χ a) ∈ ψ '' V := ⟨χ a, (hgood a ha).2.1, rfl⟩
    rw [himg] at this
    rw [hFψ' a ha]
    exact this.2
  have hZball : ∀ a ∈ ball (0 : Euclid m) s, ∀ b ∈ ball (0 : Euclid (P - m)) t,
      y + ι a + ι' b ∈ ball y r₀ := by
    intro a ha b hb
    rw [mem_ball, dist_eq_norm]
    have : y + ι a + ι' b - y = ι a + ι' b := by abel
    rw [this]
    calc ‖ι a + ι' b‖ ≤ ‖ι a‖ + ‖ι' b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖b‖ := by rw [ι.norm_map, ι'.norm_map]
      _ < s + t := add_lt_add (mem_ball_zero_iff.1 ha) (mem_ball_zero_iff.1 hb)
      _ ≤ r₀ := hsr₀
  have hZ : ∀ z : Euclid P, (∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (P - m)) t,
      z = y + ι a + ι' b) ↔ (π (z - y) ∈ ball (0 : Euclid m) s ∧
        π' (z - y) ∈ ball (0 : Euclid (P - m)) t) := by
    intro z
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have : y + ι a + ι' b - y = ι a + ι' b := by abel
      rw [this, map_add, map_add, hπι, hπι', hπ'ι, hπ'ι', add_zero, zero_add]
      exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩
      refine ⟨_, ha, _, hb, ?_⟩
      rw [add_assoc, ← hdec]
      abel
  have hZopen : IsOpen {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
      ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} := by
    have : {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
        ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} =
        (fun z => π (z - y)) ⁻¹' ball 0 s ∩ (fun z => π' (z - y)) ⁻¹' ball 0 t := by
      ext z; exact hZ z
    rw [this]
    exact (isOpen_ball.preimage (π.continuous.comp (continuous_id.sub continuous_const))).inter
      (isOpen_ball.preimage (π'.continuous.comp (continuous_id.sub continuous_const)))
  have hMZ : M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
      ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} =
      (fun a => y + ι a + ι' (u a)) '' ball 0 s := by
    ext z
    constructor
    · rintro ⟨hzM, a, ha, b, hb, rfl⟩
      obtain ⟨v, hvs, hψv⟩ := hloc _ hzM (hZball a ha b hb)
      refine ⟨a, ha, ?_⟩
      have hφv : φ v = a := by
        show π (ψ v - y) = a
        rw [hψv]
        have : y + ι a + ι' b - y = ι a + ι' b := by abel
        rw [this, map_add, hπι, hπι', add_zero]
      have hχφ : χ (φ v) = v := PH.left_inv hvs
      calc y + ι a + ι' (u a) = ψ (χ a) := hFψ' a ha
        _ = ψ (χ (φ v)) := by rw [hφv]
        _ = ψ v := by rw [hχφ]
        _ = y + ι a + ι' b := hψv
    · rintro ⟨a, ha, rfl⟩
      exact ⟨hFM a ha, a, ha, u a, mem_ball_zero_iff.2 (hgood a ha).2.2.2.2, rfl⟩
  have hinjF : InjOn (fun a => y + ι a + ι' (u a)) (ball 0 s) := by
    intro a _ a' _ h
    have h' : y + ι a + ι' (u a) = y + ι a' + ι' (u a') := h
    calc a = π (y + ι a + ι' (u a) - y) := (hπF a).symm
      _ = π (y + ι a' + ι' (u a') - y) := by rw [h']
      _ = a' := hπF a'
  have hFd : ∀ a ∈ ball (0 : Euclid m) s, HasFDerivAt (fun a => y + ι a + ι' (u a))
      (ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ u a) a := by
    intro a ha
    have hu : HasFDerivAt u (fderiv ℝ u a) a :=
      ((hgood a ha).2.2.1.differentiableAt one_ne_zero).hasFDerivAt
    exact (ι.toContinuousLinearMap.hasFDerivAt.const_add y).add
      (ι'.toContinuousLinearMap.hasFDerivAt.comp a hu)
  have huC : ContDiffOn ℝ 1 u (ball 0 s) := fun a ha => (hgood a ha).2.2.1.contDiffWithinAt
  have hFC : ContDiffOn ℝ 1 (fun a => y + ι a + ι' (u a)) (ball (0 : Euclid m) s) :=
    (contDiffOn_const.add ι.contDiff.contDiffOn).add (ι'.contDiff.comp_contDiffOn huC)
  refine ⟨s, t, u, hs, ht0, hsδ, huC, hu0,
    fun a ha => ⟨(hgood a ha).2.2.2.1.le, (hgood a ha).2.2.2.2⟩, hZopen, hMZ, hinjF,
    fun a ha => ⟨?_, ?_⟩, ?_⟩
  · -- `DF(a)` is injective: `π ∘ DF(a) = id`
    rw [(hFd a ha).fderiv]
    intro w w' h
    have := congrArg π h
    simpa [hπι, hπι'] using this
  · -- tangent spaces
    rw [(hFd a ha).fderiv]
    ext v
    constructor
    · intro hv
      simp only [tangentSpace, mem_ofPred_eq] at hv
      obtain ⟨γ, -, hγM, hγ0, hγv⟩ := hv
      have hFZ : γ 0 ∈ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
          ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} :=
        ⟨a, ha, u a, mem_ball_zero_iff.2 (hgood a ha).2.2.2.2, hγ0⟩
      have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), γ τ ∈ M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
          ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} := by
        filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1),
          hγv.continuousAt.preimage_mem_nhds (hZopen.mem_nhds hFZ)] with τ hτ hτZ
        exact ⟨hγM hτ, hτZ⟩
      have hγF : γ =ᶠ[𝓝 0] (fun a => y + ι a + ι' (u a)) ∘ (fun τ => π (γ τ - y)) := by
        filter_upwards [hev] with τ hτ
        rw [hMZ] at hτ
        obtain ⟨a', -, h'⟩ := hτ
        have h'' : y + ι a' + ι' (u a') = γ τ := h'
        show γ τ = y + ι (π (γ τ - y)) + ι' (u (π (γ τ - y)))
        rw [← h'', hπF]
      have hα : HasDerivAt (fun τ => π (γ τ - y)) (π v) 0 :=
        π.hasFDerivAt.comp_hasDerivAt 0 (hγv.sub_const y)
      have hcomp := (hFd a ha).comp_hasDerivAt_of_eq 0 hα (by rw [hγ0, hπF])
      exact ⟨π v, (hγv.unique (hcomp.congr_of_eventuallyEq hγF)).symm⟩
    · rintro ⟨w, rfl⟩
      simp only [tangentSpace, mem_ofPred_eq]
      have has : ‖a‖ < s := mem_ball_zero_iff.1 ha
      set c := (s - ‖a‖) / (‖w‖ + 1) with hcdef
      have hc : 0 < c := div_pos (by linarith) (by positivity)
      have hcw : c * (‖w‖ + 1) = s - ‖a‖ := by rw [hcdef]; field_simp
      have hβball : ∀ τ : ℝ, a + (c * Real.sin (τ / c)) • w ∈ ball (0 : Euclid m) s := by
        intro τ
        rw [mem_ball_zero_iff]
        have h1 : |c * Real.sin (τ / c)| ≤ c := by
          rw [abs_mul, abs_of_pos hc]
          exact mul_le_of_le_one_right hc.le (Real.abs_sin_le_one _)
        calc ‖a + (c * Real.sin (τ / c)) • w‖ ≤ ‖a‖ + ‖(c * Real.sin (τ / c)) • w‖ :=
              norm_add_le _ _
          _ = ‖a‖ + |c * Real.sin (τ / c)| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖a‖ + c * ‖w‖ := by gcongr
          _ < ‖a‖ + c * (‖w‖ + 1) := by nlinarith
          _ = s := by rw [hcw]; ring
      have hβd : HasDerivAt (fun τ : ℝ => a + (c * Real.sin (τ / c)) • w) w 0 := by
        have h1 : HasDerivAt (fun τ : ℝ => c * Real.sin (τ / c)) 1 0 := by
          have h2 : HasDerivAt (fun τ : ℝ => τ / c) (1 / c) 0 :=
            (hasDerivAt_id (0 : ℝ)).div_const c
          have h3 := ((Real.hasDerivAt_sin ((0 : ℝ) / c)).comp 0 h2).const_mul c
          have h4 : c * (Real.cos (0 / c) * (1 / c)) = 1 := by
            rw [zero_div, Real.cos_zero, one_mul, mul_one_div_cancel hc.ne']
          rw [h4] at h3
          exact h3
        have := (h1.smul_const w).const_add a
        simpa using this
      refine ⟨(fun a => y + ι a + ι' (u a)) ∘ (fun τ : ℝ => a + (c * Real.sin (τ / c)) • w),
        ?_, ?_, ?_, ?_⟩
      · exact (hFC.comp_contDiff (contDiff_const.add ((contDiff_const.mul
          (Real.contDiff_sin.comp (contDiff_id.div_const c))).smul contDiff_const))
          hβball).contDiffOn
      · intro τ _
        exact hFM _ (hβball τ)
      · simp
      · exact (hFd a ha).comp_hasDerivAt_of_eq 0 hβd (by simp)
  · -- properness
    intro K hKZ hK
    have hKW : K ⊆ W := fun z hz => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hKZ hz
      exact hr₀W (hZball a ha b hb)
    have hMK : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext z
      constructor
      · rintro ⟨hzM, hzK⟩
        obtain ⟨v, hv, rfl⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hKW hzK, hzM⟩
        exact ⟨v, ⟨hv, hzK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have : ψ v ∈ ψ '' V := ⟨v, hv, rfl⟩
        rw [himg] at this
        exact ⟨this.2, hvK⟩
    have hMKc : IsCompact (M ∩ K) := by
      rw [hMK]
      exact (hprop K hKW hK).image_of_continuousOn (hψcont.mono inter_subset_left)
    have hpre : ball (0 : Euclid m) s ∩ (fun a => y + ι a + ι' (u a)) ⁻¹' K =
        (fun z => π (z - y)) '' (M ∩ K) := by
      ext a
      constructor
      · rintro ⟨ha, haK⟩
        exact ⟨_, ⟨hFM a ha, haK⟩, hπF a⟩
      · rintro ⟨z, ⟨hzM, hzK⟩, rfl⟩
        have hz : z ∈ M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s,
            ∃ b ∈ ball (0 : Euclid (P - m)) t, z = y + ι a + ι' b} := ⟨hzM, hKZ hzK⟩
        rw [hMZ] at hz
        obtain ⟨a, ha, rfl⟩ := hz
        refine ⟨?_, ?_⟩
        · show π (y + ι a + ι' (u a) - y) ∈ ball 0 s
          rw [hπF]
          exact ha
        · show y + ι (π (y + ι a + ι' (u a) - y)) + ι' (u (π (y + ι a + ι' (u a) - y))) ∈ K
          rw [hπF]
          exact hzK
    rw [hpre]
    exact hMKc.image (π.continuous.comp (continuous_id.sub continuous_const))

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
