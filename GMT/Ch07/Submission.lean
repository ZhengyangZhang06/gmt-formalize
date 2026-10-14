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

end Submission

end GMT.Ch07
