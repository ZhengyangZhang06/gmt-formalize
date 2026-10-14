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

/-- The translate `Q − a = {y | y + a ∈ Q}` of `Q = span τ`, `τ : Fin d → ℝᴾ` orthonormal, is a
`d`-dimensional embedded `Cʳ` submanifold (Simon Ch. 2, §4, (4.1)), with the single chart
`ψ(v) = ι(v) − a` on `V = ℝᵈ`, `W = ℝᴾ`: `ι(v) = ∑ⱼ vⱼ τⱼ` is a linear isometry of `ℝᵈ` onto `Q`,
so `ψ` is smooth, injective and proper, and `Dψ ≡ ι` is injective. -/
theorem Submission.codim1_zsl_op_translate_isEmbeddedSubmanifold : ∀ (P d r : ℕ) (Q : Submodule ℝ (Euclid P)) (τ : Fin d → Euclid P) (a : Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → IsEmbeddedSubmanifold r d {y | y + a ∈ Q} := by
  intro P d r Q τ a hτ hQ
  -- Step 1: the continuous linear map `ι v = ∑ⱼ vⱼ τⱼ`
  set ι : Euclid d →L[ℝ] Euclid P := ∑ j, (EuclideanSpace.proj j).smulRight (τ j) with hι_def
  have hι : ∀ v, ι v = ∑ j, v j • τ j := by
    intro v
    simp [hι_def]
  -- Step 2: `ι` is an isometry, by orthonormality of `τ`
  have hnorm : ∀ v, ‖ι v‖ = ‖v‖ := by
    intro v
    have h2 : ‖ι v‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hι, hτ.inner_sum,
        EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  -- Step 3: `ι` is injective
  have hinj : Injective ι := by
    intro v w hvw
    have h0 : ‖v - w‖ = 0 := by rw [← hnorm, map_sub, hvw, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 4: the range of `ι` is `Q`
  have hrange : ∀ z, z ∈ Q ↔ ∃ v, ι v = z := by
    intro z
    constructor
    · intro hz
      rw [← hQ] at hz
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hz
      exact ⟨WithLp.toLp 2 c, by rw [hι]; simpa using hc⟩
    · rintro ⟨v, rfl⟩
      rw [hι, ← hQ]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  -- Steps 5–7: the global chart `ψ v = ι v − a` with `V = ℝᵈ`, `W = ℝᴾ`
  intro y _
  refine ⟨univ, univ, fun v => ι v - a, isOpen_univ, isOpen_univ, mem_univ y,
    (ι.contDiff.sub contDiff_const).contDiffOn, ?_, ?_, ?_, ?_⟩
  -- `ψ` is injective on `V`
  · intro v _ w _ hvw
    exact hinj (sub_left_injective hvw)
  -- `ψ(V) = W ∩ A`, by Step 4
  · ext z
    rw [image_univ, univ_inter, mem_range]
    change (∃ v, ι v - a = z) ↔ z + a ∈ Q
    rw [hrange]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (sub_add_cancel _ _).symm⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, by rw [hv, add_sub_cancel_right]⟩
  -- `ψ` is proper: `ψ⁻¹(K)` is closed and bounded by `R + ‖a‖` (Heine–Borel)
  · intro K _ hK
    rw [univ_inter]
    refine Metric.isCompact_of_isClosed_isBounded
      (hK.isClosed.preimage (ι.continuous.sub continuous_const)) ?_
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    refine isBounded_iff_forall_norm_le.mpr ⟨R + ‖a‖, fun v hv => ?_⟩
    calc ‖v‖ = ‖(ι v - a) + a‖ := by rw [sub_add_cancel, hnorm]
      _ ≤ ‖ι v - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ R + ‖a‖ := by gcongr; exact hR _ hv
  -- `Dψ(z) = ι` is injective
  · intro z _
    rw [(ι.hasFDerivAt.sub_const a).fderiv]
    exact hinj
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- **Simon Ch. 3, 1.4** (change of variables under the blow-up `η_{x,r}`): for `r > 0`, every
set `M` and every `f`, `∫_{η_{x,r}(M)} f dHⁿ = r⁻ⁿ ∫_M f(η_{x,r}(y)) dHⁿ(y)`.
`η_{x,r} = (r⁻¹ • ·) ∘ (· − x)` is a homeomorphism with `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)` for every
`S` (translation is an isometry), so `Hⁿ⌞η_{x,r}(M) = r⁻ⁿ η_{x,r#}(Hⁿ⌞M)`. -/
theorem Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (r : ℝ), 0 < r → ∀ f : Euclid P → ℝ, ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] = r⁻¹ ^ n * ∫ y in M, f (Poincare.SimonGMT.Chapter03.blowUpMap x r y) ∂μHE[n] := by
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

/-- **Blow-ups of a region boundary** (Simon 7.5.1, `T = ∂[[E]]`; 6.2.23, `η_#T(ω) = T(η^#ω)`):
if `T = ∂[[E]]` in `U` with orientation `ξN`, then for `λ > 0` the blow-up `η_{y,λ#}T` is
`∂[[η_{y,λ}(E)]]` in `η_{y,λ}(U)` with orientation `w ↦ ξN(y + λw)`.  For `ω ∈ 𝒟ⁿ(η(U))` and
`ω' = ω ∘ η ∈ 𝒟ⁿ(U)`, `η_#T(ω) = λ⁻ⁿ T(ω')`; `ω' = λⁿ η^#ω` and `d` commutes with the affine
pull-back, so `dω'(z) = λ⁻¹ dω(η(z))`; the change of variables
`∫_{η(E)} g dH^{n+1} = λ^{-(n+1)} ∫_E g ∘ η dH^{n+1}` cancels the powers of `λ`. -/
theorem Submission.codim1_zsl_blowUp_isBoundaryOfRegion : ∀ (P n : ℕ) (U E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (y : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsBoundaryOfRegion T E ξN → IsBoundaryOfRegion (blowUp T y lam hlam.ne') (dilation y lam '' E) (fun w => ξN (y + lam • w)) := by
  intro P n U E ξN T y lam hlam hT ω
  have hne : lam ≠ 0 := hlam.ne'
  -- Steps 1–2: `ω' := ω ∘ η ∈ 𝒟ⁿ(U)`, `η_#T(ω) = λ⁻ⁿ T(ω')`, and `T(ω') = ∫_E ξN (dω')`.
  obtain ⟨ω', hω'⟩ := (Submission.dtc_blowUp_testForm_corr P n U y lam hlam).1 ω
  rw [(Submission.dtc_blowUp_testForm_corr P n U y lam hlam).2.2 T ω ω' hω', hT ω']
  -- Step 3: the affine pull-back `η^#α` of a `k`-form is `λ⁻ᵏ α ∘ η` (multilinearity), so
  -- `ω' = λⁿ η^#ω` and `dω' = λⁿ η^#(dω) = λ⁻¹ (dω) ∘ η`.
  have hpull : ∀ {k : ℕ} (α : DifferentialForm (Euclid P) k) (z : Euclid P),
      affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y)) α z =
        lam⁻¹ ^ k • α (dilation y lam z) := by
    intro k α z
    ext v
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  have hω'eq : (ω' : DifferentialForm (Euclid P) n) =
      lam ^ n • affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y))
        (ω : DifferentialForm (Euclid P) n) := by
    funext z
    rw [Pi.smul_apply, hpull, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul, hω' z]
  have hdω' : ∀ z, exteriorDerivative (ω' : DifferentialForm (Euclid P) n) z =
      lam⁻¹ • exteriorDerivative (ω : DifferentialForm (Euclid P) n) (dilation y lam z) := by
    intro z
    rw [hω'eq, exteriorDerivative_smul, exteriorDerivative_affinePullbackForm _ _ ω.property.1.1,
      Pi.smul_apply, hpull, smul_smul, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hne,
      one_pow, one_mul]
  -- Steps 5–6: `y + λ η(z) = z`, `blowUpMap y λ = η`, and the change of variables.
  have hηinv : ∀ z, y + lam • dilation y lam z = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hbl : Poincare.SimonGMT.Chapter03.blowUpMap y lam = dilation y lam := by
    funext z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub, sub_eq_neg_add]
    simp [dilation, dilationCLM]
  have hcov := Submission.setIntegral_blowUpMap_image_eq_inv_pow_mul P (n + 1) E y lam hlam
    (fun w => ξN (y + lam • w) (exteriorDerivative (ω : DifferentialForm (Euclid P) n) w))
  simp only [hbl, hηinv] at hcov
  -- Steps 4 and 7: pull `λ⁻¹` out of the integral; `λ⁻ⁿ · λ⁻¹ = λ^{-(n+1)}`.
  simp only [hcov, hdω', map_smul, smul_eq_mul, integral_const_mul]
  ring

/-- **Zero-scale blow-up centres lie within `O(λᵢ)` of `N`, and `x ∈ N`** (towards "by definition
of `𝒯`, `spt S ⊂` some `(n+1)`-dimensional subspace" in the proof of Simon 7.5.8,
chapter-07.txt lines 965–966, for the limits with `λ = 0` of the class `𝒯` of the proof of 7.4.4,
lines 646–649; `spt` is Simon 6.2.11, chapter-06.txt line 299).  Let `T = ∂[[E]]` in `U` with
`E ⊆ N` and `(N̄ \ N) ∩ U = ∅`, `xᵢ → x ∈ U`, `λᵢ > 0`, `λᵢ → 0`, and `η_{xᵢ,λᵢ#}T ⇀ S` in `ℝᴾ`
with `spt S ≠ ∅`.  Then `x ∈ N`, and for some `C₀ > 0` each `xᵢ` has a `p ∈ N` with
`|p − xᵢ| ≤ C₀λᵢ`.  By the blow-up region identity, `η_{xᵢ,λᵢ#}T(ω)` is
`∫_{η_{xᵢ,λᵢ}(E)} ⟨dω, ξ_N(xᵢ + λᵢ·)⟩ dH^{n+1}`, which vanishes when `spt ω` misses
`η_{xᵢ,λᵢ}(N)`; were `dist(xᵢ, N)/λᵢ` unbounded, then along a subsequence every test form would
eventually miss `η_{xᵢ,λᵢ}(N)`, so `S = 0` and `spt S = ∅`. -/
theorem Submission.codim1_zsl_blowUp_centres_near : ∀ (P n : ℕ) (U N E : Set (Euclid P)) (ξN : Euclid P → MultiVector P (n + 1)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n), (closure N \ N) ∩ U = ∅ → E ⊆ N → IsBoundaryOfRegion T E ξN → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → S.support.Nonempty → x ∈ N ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ i, ∃ p ∈ N, dist p (xs i) ≤ C₀ * lams i := by
  intro P n U N E ξN T x xs lams hlams S hNU hEN hT hxU hxs hlam hconv hS
  -- Step 1: write `ηᵢ := η_{xᵢ,λᵢ}`.  If `tsupport ω` misses `ηᵢ(N)`, then `ηᵢ#T(ω) = 0`: either
  -- `tsupport ω ⊄ ηᵢ(U)` (`currentEval` is `0`), or by the blow-up region identity `ηᵢ#T(ω)` is
  -- `∫_{ηᵢ(E)} ⟨dω, ξ_N(xᵢ + λᵢ·)⟩ dH^{n+1}`, with `ηᵢ(E) ⊆ ηᵢ(N)` and `tsupport dω ⊆ tsupport ω`.
  have hvanish : ∀ (i : ℕ) (ω : DifferentialForm (Euclid P) n),
      (∀ p ∈ N, dilation (xs i) (lams i) p ∉ tsupport ω) →
        currentEval (blowUp T (xs i) (lams i) (hlams i).ne') ω = 0 := by
    intro i ω hω
    rw [currentEval]
    split_ifs with h
    · rw [Submission.codim1_zsl_blowUp_isBoundaryOfRegion P n U E ξN T (xs i) (lams i) (hlams i)
        hT ⟨ω, h⟩]
      refine setIntegral_eq_zero_of_forall_eq_zero ?_
      rintro _ ⟨p, hp, rfl⟩
      have hd : dilation (xs i) (lams i) p ∉ tsupport (exteriorDerivative ω) :=
        fun hd => hω p (hEN hp) (tsupport_exteriorDerivative_subset ω hd)
      show ξN (xs i + lams i • dilation (xs i) (lams i) p)
        (exteriorDerivative ω (dilation (xs i) (lams i) p)) = 0
      rw [image_eq_zero_of_notMem_tsupport hd, map_zero]
    · rfl
  -- Step 2: `|ηᵢ(p)| = λᵢ⁻¹ |p − xᵢ|`.
  have hdil : ∀ (i : ℕ) (p : Euclid P),
      dist (dilation (xs i) (lams i) p) 0 = (lams i)⁻¹ * dist p (xs i) := by
    intro i p
    have h : dilation (xs i) (lams i) p = (lams i)⁻¹ • (p - xs i) := by
      rw [smul_sub, sub_eq_neg_add]
      rfl
    rw [h, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlams i)),
      dist_eq_norm]
  -- Steps 3–4: suppose that along a subsequence `σ`, for each `R`, eventually every `p ∈ N` has
  -- `|p − x_{σ j}| > λ_{σ j} R`.  A test form `ω` has `tsupport ω ⊆ B̄_R(0)` for some `R`, so it
  -- eventually misses `η_{σ j}(N)` and `S(ω) = lim η_{σ j}#T(ω) = 0`.  Then `S = 0` vanishes on
  -- `B_1(z)` for every `z`, contradicting `spt S ≠ ∅`.
  have hkey : ∀ σ : ℕ → ℕ, StrictMono σ →
      (∀ R : ℝ, ∀ᶠ j in atTop, ∀ p ∈ N, lams (σ j) * R < dist p (xs (σ j))) → False := by
    intro σ hσ hfar
    obtain ⟨z, hz⟩ := hS
    refine hz.2 (mem_sUnion.mpr ⟨ball z 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure,
      subset_univ _, fun ω _ => ?_⟩, mem_ball_self one_pos⟩)
    obtain ⟨⟨-, hcompact⟩, -⟩ := ω.property
    obtain ⟨R, hR⟩ := hcompact.isCompact.isBounded.subset_closedBall 0
    refine tendsto_nhds_unique ((hconv ω).comp hσ.tendsto_atTop) (tendsto_const_nhds.congr' ?_)
    filter_upwards [hfar R] with j hj
    refine (hvanish (σ j) (ω : DifferentialForm (Euclid P) n) fun p hp hpω => ?_).symm
    have h := mem_closedBall.mp (hR hpω)
    rw [hdil, inv_mul_le_iff₀ (hlams (σ j))] at h
    exact (hj p hp).not_ge h
  -- Step 5: `N ≠ ∅`, since otherwise the hypothesis of `hkey` holds vacuously for `σ = id`.
  have hNne : N.Nonempty := by
    by_contra hN0
    exact hkey id strictMono_id fun R => Eventually.of_forall fun j p hp => (hN0 ⟨p, hp⟩).elim
  -- Step 6: `dist(xᵢ, N)/λᵢ` is bounded above; otherwise there is `σ` with
  -- `dist(x_{σ j}, N) > jλ_{σ j}` for every `j`, and `hkey` applies.
  have hbdd : BddAbove (range fun i => infDist (xs i) N / lams i) := by
    by_contra hnb
    have hfreq : ∀ j : ℕ, ∃ᶠ i in atTop, (j : ℝ) < infDist (xs i) N / lams i := by
      intro j
      by_contra hj
      exact hnb (isBoundedUnder_of_eventually_le
        ((not_frequently.mp hj).mono fun i hi => not_lt.mp hi)).bddAbove_range
    obtain ⟨σ, hσ, hσr⟩ := extraction_forall_of_frequently hfreq
    refine hkey σ hσ fun R => ?_
    obtain ⟨J, hJ⟩ := exists_nat_ge R
    filter_upwards [eventually_ge_atTop J] with j hj p hp
    have h1 := (lt_div_iff₀ (hlams (σ j))).mp (hσr j)
    have h2 : infDist (xs (σ j)) N ≤ dist p (xs (σ j)) := by
      rw [dist_comm]
      exact infDist_le_dist_of_mem hp
    have h3 : R ≤ (j : ℝ) := hJ.trans (Nat.cast_le.mpr hj)
    calc lams (σ j) * R ≤ lams (σ j) * j := mul_le_mul_of_nonneg_left h3 (hlams (σ j)).le
      _ = j * lams (σ j) := mul_comm _ _
      _ < infDist (xs (σ j)) N := h1
      _ ≤ dist p (xs (σ j)) := h2
  obtain ⟨M, hM⟩ := hbdd
  have hdist : ∀ i, infDist (xs i) N ≤ M * lams i := fun i =>
    (div_le_iff₀ (hlams i)).mp (hM (mem_range_self i))
  -- Step 7: `C₀ := max M 0 + 1`, and `dist(xᵢ, N) ≤ Mλᵢ < C₀λᵢ` gives `p ∈ N`.
  refine ⟨?_, max M 0 + 1, add_pos_of_nonneg_of_pos (le_max_right M 0) one_pos, fun i => ?_⟩
  · -- Step 8: `dist(x, N) ≤ dist(xᵢ, N) + |x − xᵢ| ≤ Mλᵢ + |x − xᵢ| → 0`, so `x ∈ N̄ ∩ U ⊆ N`.
    have hlim : Tendsto (fun i => M * lams i + dist x (xs i)) atTop (𝓝 (M * 0 + dist x x)) :=
      (hlam.const_mul M).add (tendsto_const_nhds.dist hxs)
    rw [mul_zero, dist_self, add_zero] at hlim
    have h0 : infDist x N ≤ 0 := ge_of_tendsto' hlim fun i =>
      infDist_le_infDist_add_dist.trans (add_le_add (hdist i) le_rfl)
    have hcl : x ∈ closure N :=
      (mem_closure_iff_infDist_zero hNne).mpr (le_antisymm h0 infDist_nonneg)
    by_contra hxN
    exact hNU.subset ⟨⟨hcl, hxN⟩, hxU⟩
  · obtain ⟨p, hp, hpd⟩ := (infDist_lt_iff hNne).mp ((hdist i).trans_lt
      (mul_lt_mul_of_pos_right ((le_max_left M 0).trans_lt (lt_add_one _)) (hlams i)))
    exact ⟨p, hp, (dist_comm p (xs i)).trans_le hpd.le⟩
/-- Step 2 of the Lipschitz approximation lemma (Simon Ch. 5, Lemma 2.6, in Allard's theorem as used
for 7.4.3): orthonormal graph coordinates adapted to an `n`-plane `T₀ ⊆ ℝ^{n+k}`.  With orthonormal
bases `a` of `T₀` and `b` of `T₀ᗮ` (`dim T₀ᗮ = k`), `ι v = Σ vᵢaᵢ` and `ι' w = Σ wⱼbⱼ` are linear
isometries onto `T₀` and `T₀ᗮ`; hence `⟪ι v, ι' w⟫ = 0`, every `x = p_{T₀} x + (x − p_{T₀} x)` is
`ι v + ι' w`, and `p_{T₀}(ι v + ι' w) = ι v`. -/
theorem Submission.dorag_lip_orthonormal_coordinates : ∀ (n k : ℕ) (T₀ : Submodule ℝ (Euclid (n + k))), Module.finrank ℝ T₀ = n → ∃ (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ v, ι v ∈ T₀) ∧ (∀ x, ∃ v w, x = ι v + ι' w) ∧ (∀ v w, T₀.starProjection (ι v + ι' w) = ι v) := by
  intro n k T₀ hT₀
  -- `dim T₀ᗮ = k`, since `dim T₀ + dim T₀ᗮ = n + k`
  have hTo : Module.finrank ℝ T₀ᗮ = k := by
    have h := Submodule.finrank_add_finrank_orthogonal T₀
    rw [finrank_euclideanSpace_fin, hT₀] at h
    omega
  -- orthonormal bases of `T₀` and `T₀ᗮ` indexed by `Fin n` and `Fin k`
  let b := (stdOrthonormalBasis ℝ T₀).reindex (finCongr hT₀)
  let b' := (stdOrthonormalBasis ℝ T₀ᗮ).reindex (finCongr hTo)
  -- inverse coordinate maps followed by the inclusions of `T₀` and `T₀ᗮ`
  let ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k) := T₀.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k) := T₀ᗮ.subtypeₗᵢ.comp b'.repr.symm.toLinearIsometry
  have hιmem : ∀ v, ι v ∈ T₀ := fun v => (b.repr.symm v).2
  have hι'mem : ∀ w, ι' w ∈ T₀ᗮ := fun w => (b'.repr.symm w).2
  refine ⟨ι, ι', fun v w => Submodule.inner_right_of_mem_orthogonal (hιmem v) (hι'mem w), hιmem,
    ?_, ?_⟩
  · -- `x = p_{T₀} x + (x − p_{T₀} x)` with `p_{T₀} x ∈ T₀` and `x − p_{T₀} x ∈ T₀ᗮ`
    intro x
    refine ⟨b.repr ⟨T₀.starProjection x, Submodule.starProjection_apply_mem _ _⟩,
      b'.repr ⟨x - T₀.starProjection x, Submodule.sub_starProjection_mem_orthogonal x⟩, ?_⟩
    simp [ι, ι']
  · -- `p_{T₀}` fixes `ι v ∈ T₀` and kills `ι' w ∈ T₀ᗮ`
    intro v w
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (hιmem v),
      (Submodule.starProjection_apply_eq_zero_iff T₀).mpr (hι'mem w), add_zero]
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
/-- Steps 3(ii)–(iii) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3,
via Allard's theorem): if `τ` is an orthonormal `n`-frame whose span contains every `F eⱼ`, then
`det(F* ∘ F) = (det 𝒜)²` with `𝒜ᵢⱼ = ⟨τᵢ, F eⱼ⟩`.  Expanding `F eⱼ = Σₗ 𝒜ₗⱼ τₗ` gives the Gram
identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`, and the Gram matrix is the matrix of `F* ∘ F` in the standard
basis of `ℝⁿ`. -/
theorem Submission.dgoj_det_adjoint_comp_eq_det_sq : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P) (τ : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ)) → (F.adjoint ∘L F).det = (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det ^ 2 := by
  intro P n F τ hτ hb
  set A : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ))) with hA
  -- `F eⱼ = Σₗ 𝒜ₗⱼ τₗ`: the coordinates of a vector of `span τ` are its inner products with `τ`
  have hexp : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) = ∑ l, A l j • τ l := by
    intro j
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hb j)
    have hcA : ∀ l, A l j = c l := by
      intro l
      rw [hA, Matrix.of_apply, ← hc, hτ.inner_right_fintype]
    rw [← hc]
    simp only [hcA]
  -- the Gram identity `⟨F eᵢ, F eⱼ⟩ = (𝒜ᵀ𝒜)ᵢⱼ`
  have hgram : ∀ i j, inner ℝ (F (EuclideanSpace.single i (1 : ℝ)))
      (F (EuclideanSpace.single j (1 : ℝ))) = (A.transpose * A) i j := by
    intro i j
    rw [Matrix.mul_apply]
    conv_lhs => rw [hexp i]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_left, Matrix.transpose_apply]
    simp [hA]
  -- the matrix of `F* ∘ F` in the standard basis has entries `⟨eᵢ, F* F eⱼ⟩ = ⟨F eᵢ, F eⱼ⟩`
  let B := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmat : LinearMap.toMatrix B B ((F.adjoint ∘L F : Euclid n →L[ℝ] Euclid n) : Euclid n →ₗ[ℝ] Euclid n)
      = A.transpose * A := by
    ext i j
    rw [LinearMap.toMatrix_apply, ← hgram i j]
    simp only [B, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right, EuclideanSpace.inner_single_left]
    simp
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix B, hmat, Matrix.det_mul,
    Matrix.det_transpose, sq]
/-- Step 3 of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem): if `F : ℝⁿ → ℝᴾ` is injective, its range `L` has an orthonormal basis
`τ = (τ₁, …, τₙ)`, regarded as an orthonormal `n`-frame in `ℝᴾ` spanning `L`.  Since
`dim L = n`, reindex `stdOrthonormalBasis ℝ L` along `Fin (dim L) ≃ Fin n` and include it into
`ℝᴾ` by the linear isometry `L → ℝᴾ`. -/
theorem Submission.dgoj_exists_orthonormal_frame_range : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧ Submodule.span ℝ (Set.range τ) = LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) := by
  intro P n F hF
  set L := LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P) with hLdef
  -- `dim L = dim ℝⁿ = n`, since `F` is injective
  have hL : Module.finrank ℝ L = n := by
    rw [hLdef, LinearMap.finrank_range_of_inj hF, finrank_euclideanSpace_fin]
  let T : OrthonormalBasis (Fin n) ℝ L := (stdOrthonormalBasis ℝ L).reindex (finCongr hL)
  refine ⟨fun i => (T i : Euclid P), ?_, ?_⟩
  · -- the inclusion `L → ℝᴾ` is a linear isometry
    exact T.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  · -- `span (ι '' range T) = ι '' span (range T) = ι '' L = L`
    have h1 : (fun i => (T i : Euclid P)) = L.subtype ∘ T := rfl
    rw [h1, Set.range_comp, Submodule.span_image, ← T.coe_toBasis, T.toBasis.span_eq,
      Submodule.map_top, Submodule.range_subtype]

/-- **The normalized evaluation at `F e` is a unit orientation of `range F`** (Simon 6.1.1,
6.1.7; `√det(F* ∘ F)` is the area Jacobian of Ch. 2, 3.1/3.3).  For injective `F : ℝⁿ → ℝᴾ`,
`det(F* ∘ F) > 0`, and if `α(F e₁, …, F eₙ) = √det(F* ∘ F) ξ(α)` for every `n`-covector `α` then
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal frame `τ` of `range F`: with `d = det(⟨τᵢ, F eⱼ⟩)` one has
`det(F* ∘ F) = d² ≠ 0` and `α(F e) = d α(τ)`, so `|d| ξ(α) = d α(τ)` and the sign is that of `d`. -/
theorem Submission.dgoj_unitOrientation_of_injective : ∀ (P n : ℕ) (F : Euclid n →L[ℝ] Euclid P), Injective F → 0 < (F.adjoint ∘L F).det ∧ ∀ ξ : MultiVector P n, (∀ α : Covector (Euclid P) n, α (fun i => F (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt ((F.adjoint ∘L F).det) * ξ α) → IsUnitOrientationOf ξ (LinearMap.range (F : Euclid n →ₗ[ℝ] Euclid P)) := by
  intro P n F hF
  -- an orthonormal frame `τ` of `range F`; every `F eⱼ` lies in its span
  obtain ⟨τ, hτo, hτs⟩ := Submission.dgoj_exists_orthonormal_frame_range P n F hF
  have hb : ∀ j, F (EuclideanSpace.single j (1 : ℝ)) ∈ Submodule.span ℝ (Set.range τ) := by
    intro j
    rw [hτs]
    exact LinearMap.mem_range_self _ _
  -- `det(F* ∘ F) = d²` for `d = det(⟨τᵢ, F eⱼ⟩)`
  set d := (Matrix.of fun i j => inner ℝ (τ i) (F (EuclideanSpace.single j (1 : ℝ)))).det
  have hdet : (F.adjoint ∘L F).det = d ^ 2 :=
    Submission.dgoj_det_adjoint_comp_eq_det_sq P n F τ hτo hb
  -- `ker(F* ∘ F) = ker F = 0`, so `det(F* ∘ F) ≠ 0` and hence `d ≠ 0`
  have hd : d ≠ 0 := by
    intro h
    have h0 : (F.adjoint ∘L F).det = 0 := by rw [hdet, h, zero_pow two_ne_zero]
    apply LinearMap.det_eq_zero_iff_ker_ne_bot.1 h0
    rw [F.ker_adjoint_comp_self, LinearMap.ker_eq_bot]
    exact hF
  -- (i): `det(F* ∘ F) = d² > 0`
  refine ⟨by rw [hdet]; positivity, fun ξ hξ => ⟨τ, hτo, hτs, ?_⟩⟩
  -- (ii): `|d| ξ(α) = √det(F* ∘ F) ξ(α) = α(F e) = d α(τ)` for every `α`
  have key : ∀ α : Covector (Euclid P) n, |d| * ξ α = d * α τ := by
    intro α
    rw [← Real.sqrt_sq_eq_abs, ← hdet, ← hξ α]
    exact Submission.dgoj_covector_eq_det_mul_of_mem_span P n τ _ hτo hb α
  -- the sign of `d` decides between `ξ(α) = -α(τ)` and `ξ(α) = α(τ)`
  rcases hd.lt_or_gt with hneg | hpos
  · right
    intro α
    have h := key α
    rw [abs_of_neg hneg] at h
    apply mul_left_cancel₀ hd
    linarith
  · left
    intro α
    have h := key α
    rw [abs_of_pos hpos] at h
    exact mul_left_cancel₀ hd h
/-- Evaluation of `n`-covectors at an `n`-family `c`, `ev c = (α ↦ α c)`, is a continuous map
into `n`-vectors: `‖ev c - ev c'‖ ≤ n · max(‖c‖, ‖c'‖)ⁿ⁻¹ · ‖c - c'‖`. -/
theorem Submission.dgoj_exists_continuous_covector_eval : ∀ (P n : ℕ), ∃ ev : (Fin n → Euclid P) → MultiVector P n, Continuous ev ∧ ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := by
  intro P n
  let ev : (Fin n → Euclid P) → MultiVector P n := fun c =>
    LinearMap.mkContinuous
      { toFun := fun α => α c
        map_add' := fun α β => rfl
        map_smul' := fun r α => rfl }
      (∏ i, ‖c i‖) fun α => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        calc ‖α c‖ ≤ ‖α‖ * ∏ i, ‖c i‖ := α.le_opNorm c
          _ = (∏ i, ‖c i‖) * ‖α‖ := mul_comm _ _
  have hev : ∀ (c : Fin n → Euclid P) (α : Covector (Euclid P) n), ev c α = α c := fun c α => rfl
  refine ⟨ev, ?_, hev⟩
  have key : ∀ c c' : Fin n → Euclid P,
      ‖ev c - ev c'‖ ≤ (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := by
    intro c c'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun α => ?_
    rw [sub_apply, hev, hev]
    have h := α.norm_image_sub_le c c'
    rw [Fintype.card_fin] at h
    calc ‖α c - α c'‖ ≤ ‖α‖ * n * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ := h
      _ = (n : ℝ) * max ‖c‖ ‖c'‖ ^ (n - 1) * ‖c - c'‖ * ‖α‖ := by ring
  rw [continuous_iff_continuousAt]
  intro c₀
  have hcont : Continuous fun c : Fin n → Euclid P => (n : ℝ) * max ‖c‖ ‖c₀‖ ^ (n - 1) * ‖c - c₀‖ := by
    fun_prop
  have h0 := hcont.tendsto c₀
  simp only [sub_self, norm_zero, mul_zero] at h0
  have h1 : Tendsto (fun c => ‖ev c - ev c₀‖) (𝓝 c₀) (𝓝 0) :=
    squeeze_zero (fun c => norm_nonneg (ev c - ev c₀)) (fun c => key c c₀) h0
  exact (tendsto_iff_norm_sub_tendsto_zero (E := MultiVector P n) (f := ev) (b := ev c₀)).2 h1
/-- **A continuous determinant `n`-covector on `ℝⁿ`**: some `δ ∈ Λⁿ(ℝⁿ)` (a continuous
alternating `n`-form) has `δ(e₁, …, eₙ) = 1` for the standard basis `eᵢ`.  Take the volume form
`ω` of the orientation of the standard orthonormal basis `B`; Hadamard's inequality
`|ω(v)| ≤ ∏ᵢ ‖vᵢ‖` makes it continuous, and `ω = det_B` gives `δ(e₁, …, eₙ) = det_B(B) = 1`. -/
theorem Submission.dgoj_exists_det_covector : ∀ n : ℕ, ∃ δ : Covector (Euclid n) n, δ (fun i => EuclideanSpace.single i (1 : ℝ)) = 1 := by
  intro n
  have : Fact (Module.finrank ℝ (Euclid n) = n) := ⟨finrank_euclideanSpace_fin⟩
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let o : Orientation ℝ (Euclid n) (Fin n) := b.toBasis.orientation
  refine ⟨o.volumeForm.mkContinuous 1 fun m => ?_, ?_⟩
  · rw [one_mul, Real.norm_eq_abs]
    exact o.abs_volumeForm_apply_le m
  · rw [AlternatingMap.coe_mkContinuous, o.volumeForm_robust b rfl]
    have h : (fun i => EuclideanSpace.single i (1 : ℝ)) = ⇑b.toBasis := by
      funext i; simp [b]
    rw [h, Module.Basis.det_self]
/-- Steps 1–2 of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem): for linear isometries `ι : ℝⁿ → ℝ^{n+k}`, `ι' : ℝᵏ → ℝ^{n+k}` with
`⟨ιv, ι'w⟩ = 0` and `u` of class `C¹` on `D = B_s(0)`, the adjoint `ι*` is a left inverse of
`ι + ι'`, the derivative of the graph map `Φ(v) = z + ιv + ι'u(v)` is continuous on `D`, and
`ι* ∘ DΦ(v) = id` on `D`, because `DΦ(v) = ι + ι' ∘ Du(v)`. -/
theorem Submission.dgoj_graph_fderiv_left_inverse : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → ContDiffOn ℝ 1 u (ball 0 s) → (∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v) ∧ ContinuousOn (fderiv ℝ (fun v => z + ι v + ι' (u v))) (ball (0 : Euclid n) s) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ w : Euclid n, ι.toContinuousLinearMap.adjoint (fderiv ℝ (fun v => z + ι v + ι' (u v)) v w) = w := by
  intro n k ι ι' u z s horth hu
  -- (i) `⟨ι*(ιv + ι'w), v'⟩ = ⟨ιv, ιv'⟩ + ⟨ι'w, ιv'⟩ = ⟨v, v'⟩ + 0` for every `v'`
  have hadj : ∀ (v : Euclid n) (w : Euclid k), ι.toContinuousLinearMap.adjoint (ι v + ι' w) = v := by
    intro v w
    apply ext_inner_right ℝ
    intro v'
    rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left]
    have h1 : inner ℝ (ι' w) (ι.toContinuousLinearMap v') = 0 := by
      rw [real_inner_comm]; exact horth v' w
    rw [h1, add_zero]
    exact ι.inner_map_map v v'
  refine ⟨hadj, ?_, ?_⟩
  -- (ii) `Φ = (z + ι·) + ι' ∘ u` is `C¹` on the open ball, so `DΦ` is continuous there
  · have hΦ : ContDiffOn ℝ 1 (fun v => z + ι v + ι' (u v)) (ball 0 s) :=
      (contDiffOn_const.add ι.toContinuousLinearMap.contDiff.contDiffOn).add
        (ι'.toContinuousLinearMap.contDiff.comp_contDiffOn hu)
    exact hΦ.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  -- (iii) `DΦ(v) = ι + ι' ∘ Du(v)`, so `ι*(DΦ(v)w) = ι*(ιw + ι'(Du(v)w)) = w` by (i)
  · intro v hv w
    have hdu : DifferentiableAt ℝ u v :=
      (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hv)
    have hder : HasFDerivAt (fun v => z + ι v + ι' (u v))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v := by
      have h1 : HasFDerivAt (fun v => z + ι v) ι.toContinuousLinearMap v :=
        ι.toContinuousLinearMap.hasFDerivAt.const_add z
      have h2 : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
        ι'.toContinuousLinearMap.hasFDerivAt.comp v hdu.hasFDerivAt
      exact h1.add h2
    rw [hder.fderiv]
    exact hadj w _

/-- **Continuous unit orientation of a `C¹` graph and the Jacobian identity** (Simon 7.4.3, via
Allard's theorem; steps 3 and 7 of the graph-cycle argument).  Let `Φ(v) = z + ιv + ι'u(v)` on
`D = B_s(0)`, `F(v) = DΦ(v)`, `b(v) = (F(v)e₁, …, F(v)eₙ)`, `J(v) = √det(F(v)* ∘ F(v))` and
`Pr(x) = ι*(x - z)`, so that `Pr ∘ Φ = id` and `ι* ∘ F(v) = id` (hence `F(v)` is injective and
`J > 0` on `D`).  With `ev` the evaluation of `n`-covectors at `n`-families and `δ` the normalized
determinant covector of `ℝⁿ`, take `ξ(x) = J(Pr x)⁻¹ ev(b(Pr x))` and `β(x) = J(Pr x) (δ ∘ ι*)`.
Both are continuous on `Σ = Φ(D)` because `Pr` maps `Σ` into `D`; `ξ(β) = δ(ι* b) = δ(e) = 1` on
`Σ`; `J(v) ξ(Φ v)(α) = α(b(v))` is the Jacobian identity, and with it the pointwise frame argument
for injective `F(v)` makes `ξ(Φ v)` a unit orientation of `range F(v)`. -/
theorem Submission.dgcr_graph_orientation_jacobian : ∀ (n k : ℕ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (u : Euclid n → Euclid k) (z : Euclid (n + k)) (s : ℝ), 0 < n → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < s → ContDiffOn ℝ 1 u (ball 0 s) → ∃ (ξ : Euclid (n + k) → MultiVector (n + k) n) (β : Euclid (n + k) → Covector (Euclid (n + k)) n), ContinuousOn ξ ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ ContinuousOn β ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) ∧ (∀ x ∈ (fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s, ξ x (β x) = 1) ∧ (∀ v ∈ ball (0 : Euclid n) s, IsUnitOrientationOf (ξ (z + ι v + ι' (u v))) (LinearMap.range (fderiv ℝ (fun v => z + ι v + ι' (u v)) v : Euclid n →ₗ[ℝ] Euclid (n + k)))) ∧ ∀ v ∈ ball (0 : Euclid n) s, ∀ α : Covector (Euclid (n + k)) n, α (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => z + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => z + ι v + ι' (u v)) v).det) * ξ (z + ι v + ι' (u v)) α := by
  intro n k ι ι' u z s _hn horth _hs hu
  obtain ⟨hadj, hFc, hFinv⟩ := Submission.dgoj_graph_fderiv_left_inverse n k ι ι' u z s horth hu
  obtain ⟨ev, hevc, hev⟩ := Submission.dgoj_exists_continuous_covector_eval (n + k) n
  obtain ⟨δ, hδ⟩ := Submission.dgoj_exists_det_covector n
  -- `ι*`, the projection `Pr`, the derivative `F`, the frame `b`, the Jacobian `J` and `δ ∘ ι*`
  let ιs : Euclid (n + k) →L[ℝ] Euclid n := ι.toContinuousLinearMap.adjoint
  let Pr : Euclid (n + k) → Euclid n := fun x => ιs (x - z)
  let F : Euclid n → Euclid n →L[ℝ] Euclid (n + k) := fderiv ℝ (fun v => z + ι v + ι' (u v))
  let b : Euclid n → Fin n → Euclid (n + k) := fun v i => F v (EuclideanSpace.single i (1 : ℝ))
  let J : Euclid n → ℝ := fun v => Real.sqrt (((F v).adjoint ∘L F v).det)
  let β₀ : Covector (Euclid (n + k)) n := δ.compContinuousLinearMap ιs
  -- `Pr ∘ Φ = id`, so `Pr` maps `Σ = Φ(D)` into `D`
  have hPrΦ : ∀ v, Pr (z + ι v + ι' (u v)) = v := by
    intro v
    show ιs (z + ι v + ι' (u v) - z) = v
    rw [show z + ι v + ι' (u v) - z = ι v + ι' (u v) by abel]
    exact hadj v (u v)
  have hPrc : Continuous Pr := ιs.continuous.comp (continuous_id.sub continuous_const)
  have hmaps : MapsTo Pr ((fun v => z + ι v + ι' (u v)) '' ball (0 : Euclid n) s) (ball 0 s) := by
    rintro _ ⟨v, hv, rfl⟩
    rw [hPrΦ]
    exact hv
  -- `ι* ∘ F(v) = id` on `D`: `F(v)` is injective, so `J(v) > 0`
  have hinj : ∀ v ∈ ball (0 : Euclid n) s, Injective (F v) := by
    intro v hv x y hxy
    have h := congrArg ιs hxy
    rwa [hFinv v hv x, hFinv v hv y] at h
  have hpos : ∀ v ∈ ball (0 : Euclid n) s, 0 < J v := fun v hv =>
    Real.sqrt_pos.2 (Submission.dgoj_unitOrientation_of_injective (n + k) n (F v) (hinj v hv)).1
  -- continuity of `J` and of `b` on `D`
  have hJc : ContinuousOn J (ball 0 s) := by
    have h1 : ContinuousOn (fun v => (F v).adjoint ∘L F v) (ball 0 s) :=
      ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid n)
        (F := Euclid (n + k))).continuous.comp_continuousOn hFc).clm_comp hFc
    exact Real.continuous_sqrt.comp_continuousOn
      (ContinuousLinearMap.continuous_det.comp_continuousOn h1)
  have hbc : ContinuousOn b (ball 0 s) :=
    continuousOn_pi.2 fun i => hFc.clm_apply continuousOn_const
  -- `(δ ∘ ι*)(b(v)) = δ(e₁, …, eₙ) = 1`
  have hβ₀ : ∀ v ∈ ball (0 : Euclid n) s, β₀ (b v) = 1 := by
    intro v hv
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
    convert hδ using 2
    funext i
    exact hFinv v hv _
  refine ⟨fun x => (J (Pr x))⁻¹ • ev (b (Pr x)), fun x => J (Pr x) • β₀, ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hJc.comp hPrc.continuousOn hmaps).inv₀ fun x hx => (hpos _ (hmaps hx)).ne').smul
      (hevc.comp_continuousOn (hbc.comp hPrc.continuousOn hmaps))
  · exact (hJc.comp hPrc.continuousOn hmaps).smul continuousOn_const
  · rintro _ ⟨v, hv, rfl⟩
    simp only [hPrΦ]
    rw [smul_apply, hev, ContinuousAlternatingMap.smul_apply, hβ₀ v hv,
      smul_eq_mul, smul_eq_mul, mul_one, inv_mul_cancel₀ (hpos v hv).ne']
  · intro v hv
    refine (Submission.dgoj_unitOrientation_of_injective (n + k) n (F v) (hinj v hv)).2 _
      fun α => ?_
    simp only [hPrΦ]
    rw [smul_apply, hev, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (hpos v hv).ne', one_mul]
  · intro v hv α
    simp only [hPrΦ]
    rw [smul_apply, hev, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (hpos v hv).ne', one_mul]
/-- Steps 1–2 of the local comparison for a graph (Simon 7.5, codimension one regularity): for
linear isometries `ι : ℝᵐ → ℝ^{m+k}`, `ι' : ℝᵏ → ℝ^{m+k}` with `⟨ιv, ι'w⟩ = 0` and `g`
differentiable at `w₀`, the graph map `G(w) = ιw + ι'g(w)` has `DG(w₀) = ι + ι' ∘ Dg(w₀)`, and
`|h| ≤ |DG(w₀)h|` because `|DG(w₀)h|² = |h|² + |Dg(w₀)h|²`. -/
theorem Submission.codim1_zsl_ga_lc_graph_fderiv : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → DifferentiableAt ℝ g w₀ → fderiv ℝ (fun w => ι w + ι' (g w)) w₀ = ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ g w₀ ∧ ∀ h : Euclid m, ‖h‖ ≤ ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h‖ := by
  intro m k ι ι' g w₀ horth hg
  -- (1) sum and chain rules, then uniqueness: `DG(w₀) = ι + ι' ∘ Dg(w₀)`
  have hder : fderiv ℝ (fun w => ι w + ι' (g w)) w₀ =
      ι.toContinuousLinearMap + ι'.toContinuousLinearMap ∘L fderiv ℝ g w₀ :=
    (ι.toContinuousLinearMap.hasFDerivAt.add
      (ι'.toContinuousLinearMap.hasFDerivAt.comp w₀ hg.hasFDerivAt)).fderiv
  refine ⟨hder, fun h => ?_⟩
  -- (2) Pythagoras: `|ιh + ι'(Dg(w₀)h)|² = |h|² + 2 ⟨ιh, ι'(Dg(w₀)h)⟩ + |Dg(w₀)h|²`, where the
  -- middle term vanishes by orthogonality and `ι`, `ι'` preserve norms
  have hsq : ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h‖ ^ 2 =
      ‖h‖ ^ 2 + ‖fderiv ℝ g w₀ h‖ ^ 2 := by
    have happly : fderiv ℝ (fun w => ι w + ι' (g w)) w₀ h = ι h + ι' (fderiv ℝ g w₀ h) := by
      rw [hder]; rfl
    rw [happly, norm_add_sq_real, horth, ι.norm_map, ι'.norm_map]
    ring
  -- (3) `|h|² ≤ |DG(w₀)h|²`, and both norms are nonnegative
  refine (pow_le_pow_iff_left₀ (norm_nonneg h) (norm_nonneg _) two_ne_zero).1 ?_
  rw [hsq]
  exact le_add_of_nonneg_right (sq_nonneg _)
/-- Choice of the tolerance in the local comparison for the area of a `C¹` graph (Simon 2.3.2,
by the approximation argument from the linear case 2.3.1): for `m ∈ ℕ` and `t > 1` there is
`ε ∈ (0, 1)` with `(1 + ε)^m ≤ t(1 - ε)` and `1 + ε ≤ t(1 - ε)^m`.  By continuity at `0`, pick
`ε ∈ (0, 1)` with `q^{m+1} < t` for `q = (1 + ε)/(1 - ε)`; since `1 + ε ≤ q` and
`1/(1 - ε) ≤ q`, both `(1 + ε)^m/(1 - ε)` and `(1 + ε)/(1 - ε)^m` are at most `q^{m+1}`. -/
theorem Submission.codim1_zsl_ga_lc_eps_choice : ∀ (m : ℕ) (t : ℝ), 1 < t → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (1 + ε) ^ m ≤ t * (1 - ε) ∧ 1 + ε ≤ t * (1 - ε) ^ m := by
  intro m t ht
  -- (1) `φ(ε) = ((1 + ε)/(1 - ε))^{m+1}` is continuous at `0` and `φ(0) = 1 < t`
  have hφ : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ (m + 1)) 0 :=
    ((continuousAt_const.add continuousAt_id).div (continuousAt_const.sub continuousAt_id)
      (by norm_num)).pow (m + 1)
  have hφt : ∀ᶠ ε in 𝓝 (0 : ℝ), ((1 + ε) / (1 - ε)) ^ (m + 1) < t :=
    hφ.eventually_lt continuousAt_const (by simpa using ht)
  -- (2) `(0, 1) ∈ 𝓝[>] 0`, so some `ε ∈ (0, 1)` has `φ(ε) < t`
  have hφt' : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((1 + ε) / (1 - ε)) ^ (m + 1) < t :=
    hφt.filter_mono nhdsWithin_le_nhds
  have hIoo : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  obtain ⟨ε, hεt, hε0, hε1⟩ := (hφt'.and hIoo).exists
  have h1 : 0 < 1 - ε := by linarith
  have h2 : 0 < 1 + ε := by linarith
  -- (3) with `q = (1 + ε)/(1 - ε)`: `1 + ε ≤ q` and `1/(1 - ε) ≤ q`
  have hq1 : 1 + ε ≤ (1 + ε) / (1 - ε) := by
    rw [le_div_iff₀ h1]; nlinarith
  have hq2 : 1 / (1 - ε) ≤ (1 + ε) / (1 - ε) := div_le_div_of_nonneg_right (by linarith) h1.le
  have hq0 : 0 ≤ (1 + ε) / (1 - ε) := h2.le.trans hq1
  have hinv0 : 0 ≤ 1 / (1 - ε) := (one_div_pos.mpr h1).le
  refine ⟨ε, hε0, hε1, ?_, ?_⟩
  -- (4) `(1 + ε)^m/(1 - ε) ≤ q^m · q = q^{m+1} < t`; multiply by `1 - ε > 0`
  · have h : (1 + ε) ^ m * (1 / (1 - ε)) ≤ ((1 + ε) / (1 - ε)) ^ (m + 1) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ h2.le hq1 m) hq2 hinv0 (pow_nonneg hq0 m)
    have h' : (1 + ε) ^ m / (1 - ε) ≤ t := by
      rw [div_eq_mul_one_div]; linarith
    rwa [div_le_iff₀ h1] at h'
  -- (5) `(1 + ε)/(1 - ε)^m ≤ q · q^m = q^{m+1} < t`; multiply by `(1 - ε)^m > 0`
  · have h : (1 + ε) * (1 / (1 - ε)) ^ m ≤ ((1 + ε) / (1 - ε)) ^ (m + 1) := by
      rw [pow_succ']
      exact mul_le_mul hq1 (pow_le_pow_left₀ hinv0 hq2 m) (pow_nonneg hinv0 m) hq0
    have h' : (1 + ε) / (1 - ε) ^ m ≤ t := by
      rw [div_eq_mul_one_div, ← one_div_pow]; linarith
    rwa [div_le_iff₀ (pow_pos h1 m)] at h'

/-- Local `(1 ± ε)`-bi-Lipschitz comparison of a `C¹` graph map with its linearization (Simon 2.3.2,
by the approximation argument from the linear case 2.3.1): for linear isometries
`ι : ℝᵐ → ℝ^{m+k}`, `ι' : ℝᵏ → ℝ^{m+k}` with `⟨ιv, ι'w⟩ = 0`, `g` of class `C¹` on the open set
`D ∋ w₀`, `G(w) = ιw + ι'g(w)` and `L₀ = DG(w₀)`, there is `r > 0` with `B_r(w₀) ⊆ D` and
`(1 - ε)|L₀x - L₀y| ≤ |G(x) - G(y)| ≤ (1 + ε)|L₀x - L₀y|` for `x, y ∈ B_r(w₀)`.  With
`B₀ = Dg(w₀)` and `‖Dg(w) - B₀‖ < ε` on `B_r(w₀)`, the mean value inequality bounds
`e = g(x) - g(y) - B₀(x - y)` by `ε|x - y| ≤ ε|L₀(x - y)|`, and
`G(x) - G(y) = (L₀x - L₀y) + ι'e`. -/
theorem Submission.codim1_zsl_ga_lc_local_bilipschitz : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D : Set (Euclid m)) (ε : ℝ) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → 0 < ε → w₀ ∈ D → ∃ r : ℝ, 0 < r ∧ ball w₀ r ⊆ D ∧ ∀ x ∈ ball w₀ r, ∀ y ∈ ball w₀ r, (1 - ε) * ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ x - fderiv ℝ (fun w => ι w + ι' (g w)) w₀ y‖ ≤ ‖ι x + ι' (g x) - (ι y + ι' (g y))‖ ∧ ‖ι x + ι' (g x) - (ι y + ι' (g y))‖ ≤ (1 + ε) * ‖fderiv ℝ (fun w => ι w + ι' (g w)) w₀ x - fderiv ℝ (fun w => ι w + ι' (g w)) w₀ y‖ := by
  intro m k ι ι' g D ε w₀ horth hD hg hε hw₀
  -- Step 1: `g` is differentiable at every point of the open set `D`
  have hdiff : ∀ w ∈ D, DifferentiableAt ℝ g w := fun w hw =>
    (hg.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hw)
  -- Step 2: `L₀ = ι + ι' ∘ B₀` and `|h| ≤ |L₀h|` (sibling `graph_fderiv`)
  obtain ⟨hL₀, hlow⟩ :=
    Submission.codim1_zsl_ga_lc_graph_fderiv m k ι ι' g w₀ horth (hdiff w₀ hw₀)
  set L₀ := fderiv ℝ (fun w => ι w + ι' (g w)) w₀
  set B₀ := fderiv ℝ g w₀
  have hL₀app : ∀ h, L₀ h = ι h + ι' (B₀ h) := fun h => by rw [hL₀]; rfl
  -- Step 3: `r = min(r₁, r₂)` with `B_{r₁}(w₀) ⊆ D` and `‖Dg(w) - B₀‖ < ε` on `B_{r₂}(w₀)`
  obtain ⟨r₁, hr₁, hr₁D⟩ := Metric.isOpen_iff.mp hD w₀ hw₀
  obtain ⟨r₂, hr₂, hr₂B⟩ := Metric.continuousAt_iff.mp
    ((hg.continuousOn_fderiv_of_isOpen hD le_rfl).continuousAt (hD.mem_nhds hw₀)) ε hε
  have hrD : ball w₀ (min r₁ r₂) ⊆ D := (ball_subset_ball (min_le_left _ _)).trans hr₁D
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, hrD, fun x hx y hy => ?_⟩
  -- Step 4: mean value inequality for `g - B₀` on the convex ball
  have hmvi : ‖g x - g y - B₀ (x - y)‖ ≤ ε * ‖x - y‖ :=
    (convex_ball w₀ (min r₁ r₂)).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hrD hz))
      (fun z hz => by
        rw [← dist_eq_norm]
        exact (hr₂B ((mem_ball.mp hz).trans_le (min_le_right _ _))).le) hy hx
  -- Step 5: `G(x) - G(y) = (L₀x - L₀y) + ι'e` with `e = g(x) - g(y) - B₀(x - y)`
  have hdecomp : ι x + ι' (g x) - (ι y + ι' (g y)) =
      (L₀ x - L₀ y) + ι' (g x - g y - B₀ (x - y)) := by
    rw [hL₀app, hL₀app]
    simp only [map_sub]
    abel
  -- Step 6: `|ι'e| = |e| ≤ ε|x - y| ≤ ε|L₀(x - y)| = ε|L₀x - L₀y|`
  have herr : ‖ι' (g x - g y - B₀ (x - y))‖ ≤ ε * ‖L₀ x - L₀ y‖ := by
    rw [ι'.norm_map, ← map_sub L₀ x y]
    exact hmvi.trans (mul_le_mul_of_nonneg_left (hlow (x - y)) hε.le)
  -- Step 7: the triangle inequality in both directions
  have h1 := norm_add_le (L₀ x - L₀ y) (ι' (g x - g y - B₀ (x - y)))
  have h2 := norm_sub_le (L₀ x - L₀ y + ι' (g x - g y - B₀ (x - y))) (ι' (g x - g y - B₀ (x - y)))
  rw [add_sub_cancel_right] at h2
  rw [hdecomp]
  constructor <;> linarith
/-- Continuity of the Jacobian in the local comparison for the area formula of `C¹` graphs
(Simon Ch. 2, 3.1–3.3, used for the zero-scale limit plane of 7.5): if `F : ℝᵐ → ℝᴾ` is `C¹` on
the open set `D`, then `w ↦ √det(DF(w)* ∘ DF(w))` is continuous on `D`, being `Φ ∘ DF` with `DF`
continuous on `D` and `Φ(T) = √det(T* ∘ T)` continuous on `ℝᵐ →L ℝᴾ`. -/
theorem Submission.codim1_zsl_ga_lc_jacobian_continuousOn : ∀ (m P : ℕ) (F : Euclid m → Euclid P) (D : Set (Euclid m)), IsOpen D → ContDiffOn ℝ 1 F D → ContinuousOn (fun w => Real.sqrt (((fderiv ℝ F w).adjoint ∘L fderiv ℝ F w).det)) D := by
  intro m P F D hD hF
  -- (1) `F` is `C¹` on the open set `D`, so `DF` is continuous on `D`
  have hDF : ContinuousOn (fderiv ℝ F) D := hF.continuousOn_fderiv_of_isOpen hD le_rfl
  -- (2) `Φ(T) = √det(T* ∘ T)` is continuous: the adjoint is a linear isometric equivalence,
  -- composition is jointly continuous, `det` is continuous in finite dimension, and so is `√`
  have hΦ : Continuous fun T : Euclid m →L[ℝ] Euclid P => Real.sqrt ((T.adjoint ∘L T).det) :=
    Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
      (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_id))
  -- (3) the Jacobian is `Φ ∘ DF`
  exact hΦ.comp_continuousOn hDF
/-- Final step of the local comparison of `Hᵐ` on a `C¹` graph with the integral of its Jacobian
(Simon 7.5.8 via Ch. 2, 3.2–3.3): with `ε < 1`, `c ≥ 0`, `(1 + ε)ᵐ ≤ t(1 − ε)` and
`1 + ε ≤ t(1 − ε)ᵐ`, the `(1 ± ε)`-sandwiches `(1 − ε)ᵐ c X ≤ H ≤ (1 + ε)ᵐ c X` and
`(1 − ε) c X ≤ I ≤ (1 + ε) c X` in `[0, ∞]` give `H ≤ t I` and `I ≤ t H`. -/
theorem Submission.codim1_zsl_ga_lc_sandwich : ∀ (m : ℕ) (t ε c : ℝ) (X H I : ℝ≥0∞), ε < 1 → 0 ≤ c → (1 + ε) ^ m ≤ t * (1 - ε) → 1 + ε ≤ t * (1 - ε) ^ m → ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal c * X) ≤ H → H ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal c * X) → ENNReal.ofReal ((1 - ε) * c) * X ≤ I → I ≤ ENNReal.ofReal ((1 + ε) * c) * X → H ≤ ENNReal.ofReal t * I ∧ I ≤ ENNReal.ofReal t * H := by
  intro m t ε c X H I hε hc h1 h2 hHlo hHhi hIlo hIhi
  -- (1) `1 − ε > 0`, so `(1 − ε) c ≥ 0` and `(1 − ε)ᵐ c ≥ 0`
  have hpos : 0 < 1 - ε := sub_pos.mpr hε
  have hc1 : 0 ≤ (1 - ε) * c := mul_nonneg hpos.le hc
  have hcm : 0 ≤ (1 - ε) ^ m * c := mul_nonneg (pow_nonneg hpos.le m) hc
  -- (2) multiply both hypotheses on `t` by `c ≥ 0`
  have h1' : (1 + ε) ^ m * c ≤ t * ((1 - ε) * c) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h1 hc
  have h2' : (1 + ε) * c ≤ t * ((1 - ε) ^ m * c) := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 hc
  constructor
  -- (3) `H ≤ (1 + ε)ᵐ c X ≤ t ((1 − ε) c) X ≤ t I`
  · calc H ≤ ENNReal.ofReal ((1 + ε) ^ m) * (ENNReal.ofReal c * X) := hHhi
      _ = ENNReal.ofReal ((1 + ε) ^ m * c) * X := by rw [ENNReal.ofReal_mul' hc, mul_assoc]
      _ ≤ ENNReal.ofReal (t * ((1 - ε) * c)) * X := by gcongr ENNReal.ofReal ?_ * X
      _ = ENNReal.ofReal t * (ENNReal.ofReal ((1 - ε) * c) * X) := by
        rw [ENNReal.ofReal_mul' hc1, mul_assoc]
      _ ≤ ENNReal.ofReal t * I := by gcongr
  -- (4) `I ≤ (1 + ε) c X ≤ t ((1 − ε)ᵐ c) X ≤ t H`
  · calc I ≤ ENNReal.ofReal ((1 + ε) * c) * X := hIhi
      _ ≤ ENNReal.ofReal (t * ((1 - ε) ^ m * c)) * X := by gcongr ENNReal.ofReal ?_ * X
      _ = ENNReal.ofReal t * (ENNReal.ofReal ((1 - ε) ^ m) * (ENNReal.ofReal c * X)) := by
        rw [ENNReal.ofReal_mul' hcm, ENNReal.ofReal_mul' hc, mul_assoc, mul_assoc]
      _ ≤ ENNReal.ofReal t * H := by gcongr
/-- **Simon Ch. 2, 3.1** (linear area formula): for an injective linear `L : ℝⁿ → ℝᴾ`,
`det(L*L) > 0` and `Hⁿ(L(S)) = √det(L*L) · Lⁿ(S)` for every `S ⊆ ℝⁿ`.  An orthonormal basis of
`range L` gives a linear isometry `κ : ℝⁿ → ℝᴾ` onto `range L`.  Then `L = κ ∘ M` with
`M = κ* ∘ L`, so `L*L = M*M`, `det(L*L) = (det M)² > 0` and
`Hⁿ(L(S)) = Hⁿ(κ(M(S))) = Lⁿ(M(S)) = |det M| Lⁿ(S)`.  No measurability of `S` is needed. -/
theorem Submission.codim1_zsl_ga_linear_area : ∀ (n P : ℕ) (L : Euclid n →L[ℝ] Euclid P), Function.Injective L → 0 < (L.adjoint ∘L L).det ∧ ∀ S : Set (Euclid n), μHE[n] (L '' S) = ENNReal.ofReal (Real.sqrt ((L.adjoint ∘L L).det)) * volume S := by
  intro n P L hL
  -- step 1: a linear isometry `κ` of `ℝⁿ` onto `V = range L`
  set V : Submodule ℝ (Euclid P) := LinearMap.range (L : Euclid n →ₗ[ℝ] Euclid P) with hV
  have hdim : Module.finrank ℝ V = n := by
    rw [hV, LinearMap.finrank_range_of_inj hL]; simp
  let b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
  let κ : Euclid n →ₗᵢ[ℝ] Euclid P := V.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let K : Euclid n →L[ℝ] Euclid P := κ.toContinuousLinearMap
  have hKK : K.adjoint ∘L K = 1 := LinearIsometry.adjoint_comp_self κ
  have hrange : ∀ h, ∃ u, K u = L h := by
    intro h
    refine ⟨b.repr ⟨L h, LinearMap.mem_range_self _ h⟩, ?_⟩
    simp [K, κ]
  -- step 2: `L = κ ∘ M` with `M = κ* ∘ L` injective, so `det M ≠ 0`
  let M : Euclid n →L[ℝ] Euclid n := K.adjoint ∘L L
  have hKM : K ∘L M = L := by
    ext1 h
    obtain ⟨u, hu⟩ := hrange h
    have : K.adjoint (K u) = u := by
      simpa using congrArg (fun T : Euclid n →L[ℝ] Euclid n => T u) hKK
    simp only [M, ContinuousLinearMap.comp_apply, ← hu, this]
  have hMinj : Function.Injective M := by
    intro x y hxy
    apply hL
    rw [← hKM]
    simp [hxy]
  have hdetM : M.det ≠ 0 := by
    intro h0
    rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
    exact h0 (LinearMap.ker_eq_bot.mpr hMinj)
  -- step 3: `L*L = M*M` and `det M* = det M`, so `det(L*L) = (det M)²`
  have hLL : L.adjoint ∘L L = M.adjoint ∘L M := by
    conv_lhs => rw [← hKM]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc K.adjoint K M, hKK]
    rfl
  have hdetadj : M.adjoint.det = M.det := by
    let e := EuclideanSpace.basisFun (Fin n) ℝ
    have h2 := congrArg Matrix.det (LinearMap.toMatrix_adjoint e e (M : Euclid n →ₗ[ℝ] Euclid n))
    rw [Matrix.det_conjTranspose, LinearMap.det_toMatrix, LinearMap.det_toMatrix] at h2
    simpa [ContinuousLinearMap.det, ContinuousLinearMap.adjoint_toLinearMap] using h2
  have hdetLL : (L.adjoint ∘L L).det = M.det ^ 2 := by
    rw [hLL, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    rw [show LinearMap.det (M.adjoint : Euclid n →ₗ[ℝ] Euclid n) = M.adjoint.det from rfl, hdetadj]
    ring
  refine ⟨by rw [hdetLL]; positivity, fun S => ?_⟩
  -- step 4: `Hⁿ(L(S)) = Hⁿ(κ(M(S))) = Lⁿ(M(S)) = |det M| Lⁿ(S)`
  have himg : L '' S = K '' (M '' S) := by
    rw [← hKM, ContinuousLinearMap.coe_comp, Set.image_comp]
  have hiso : Isometry K := κ.isometry
  rw [himg, Isometry.euclideanHausdorffMeasure_image hiso,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_image_continuousLinearMap, hdetLL, Real.sqrt_sq_eq_abs]
/-- Relative bi-Lipschitz comparison of `Hⁿ` (Simon Ch. 2, Theorem 1.8(i), relative form).  If
`a‖Lx − Ly‖ ≤ ‖Fx − Fy‖ ≤ b‖Lx − Ly‖` for `x, y ∈ S` (`a > 0`, `b ≥ 0`), then
`aⁿ Hⁿ(L(S)) ≤ Hⁿ(F(S)) ≤ bⁿ Hⁿ(L(S))` for arbitrary (not necessarily measurable) `S`: the
transfer maps `φ = F ∘ (L|_S)⁻¹` on `L(S)` and `ψ = L ∘ (F|_S)⁻¹` on `F(S)` are well defined,
`b`- and `a⁻¹`-Lipschitz, and satisfy `φ(L(S)) = F(S)`, `ψ(F(S)) = L(S)`. -/
theorem Submission.codim1_zsl_ga_relative_lipschitz_measure : ∀ (n P : ℕ) (F L : Euclid n → Euclid P) (S : Set (Euclid n)) (a b : ℝ), 0 < a → 0 ≤ b → (∀ x ∈ S, ∀ y ∈ S, a * ‖L x - L y‖ ≤ ‖F x - F y‖ ∧ ‖F x - F y‖ ≤ b * ‖L x - L y‖) → ENNReal.ofReal (a ^ n) * μHE[n] (L '' S) ≤ μHE[n] (F '' S) ∧ μHE[n] (F '' S) ≤ ENNReal.ofReal (b ^ n) * μHE[n] (L '' S) := by
  intro n P F L S a b ha hb hFL
  -- Step 1: the transfer maps `φ = F ∘ (L|_S)⁻¹` and `ψ = L ∘ (F|_S)⁻¹` (`invFunOn`).
  obtain ⟨φ, hφ⟩ : ∃ φ : Euclid P → Euclid P, ∀ x ∈ S, φ (L x) = F x := by
    refine ⟨fun z => F (Function.invFunOn L S z), fun x hx => ?_⟩
    have hex : ∃ y ∈ S, L y = L x := ⟨x, hx, rfl⟩
    have h := (hFL _ (Function.invFunOn_mem hex) x hx).2
    rw [Function.invFunOn_eq hex, sub_self, norm_zero, mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Euclid P → Euclid P, ∀ x ∈ S, ψ (F x) = L x := by
    refine ⟨fun z => L (Function.invFunOn F S z), fun x hx => ?_⟩
    have hex : ∃ y ∈ S, F y = F x := ⟨x, hx, rfl⟩
    have h := (hFL _ (Function.invFunOn_mem hex) x hx).1
    rw [Function.invFunOn_eq hex, sub_self, norm_zero] at h
    have h0 : ‖L (Function.invFunOn F S (F x)) - L x‖ ≤ 0 :=
      le_of_mul_le_mul_left (h.trans (mul_zero a).ge) ha
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
  have himφ : φ '' (L '' S) = F '' S := by
    rw [Set.image_image]
    exact Set.image_congr hφ
  have himψ : ψ '' (F '' S) = L '' S := by
    rw [Set.image_image]
    exact Set.image_congr hψ
  -- Step 2: `φ` is `b`-Lipschitz on `L(S)` and `ψ` is `a⁻¹`-Lipschitz on `F(S)`.
  have hφlip : LipschitzOnWith (Real.toNNReal b) φ (L '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hφ x hx, hφ y hy, dist_eq_norm, dist_eq_norm]
    exact (hFL x hx y hy).2
  have hψlip : LipschitzOnWith (Real.toNNReal a⁻¹) ψ (F '' S) := by
    refine LipschitzOnWith.of_dist_le' ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hψ x hx, hψ y hy, dist_eq_norm, dist_eq_norm, inv_mul_eq_div, le_div_iff₀ ha]
    linarith [(hFL x hx y hy).1]
  -- Step 3: the Lipschitz image bound (Simon 2.1.8(i)) for `φ` and `ψ`.
  have hup := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hφlip
  have hlo := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hψlip
  rw [himφ] at hup
  rw [himψ] at hlo
  -- Steps 4–5: `(b⁺)ⁿ = ofReal (bⁿ)` and `ofReal (aⁿ) · (a⁻¹)ⁿ = 1`.
  have hb' : ((Real.toNNReal b : NNReal) : ℝ≥0∞) ^ n = ENNReal.ofReal (b ^ n) :=
    (ENNReal.ofReal_pow hb n).symm
  have ha' : ENNReal.ofReal (a ^ n) * ((Real.toNNReal a⁻¹ : NNReal) : ℝ≥0∞) ^ n = 1 := by
    change ENNReal.ofReal (a ^ n) * ENNReal.ofReal a⁻¹ ^ n = 1
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr ha.le), ← ENNReal.ofReal_mul (pow_nonneg ha.le n),
      ← mul_pow, mul_inv_cancel₀ ha.ne', one_pow, ENNReal.ofReal_one]
  rw [hb'] at hup
  refine ⟨?_, hup⟩
  calc ENNReal.ofReal (a ^ n) * μHE[n] (L '' S)
      ≤ ENNReal.ofReal (a ^ n) * (((Real.toNNReal a⁻¹ : NNReal) : ℝ≥0∞) ^ n * μHE[n] (F '' S)) :=
        mul_le_mul_of_nonneg_left hlo zero_le
    _ = μHE[n] (F '' S) := by rw [← mul_assoc, ha', one_mul]

/-- **Local comparison** for the `C¹` graph map `G(w) = ιw + ι'g(w)` (Simon Ch. 2, 3.2–3.3, by the
approximation argument based on the linear case 3.1): for `t > 1` and `w₀ ∈ D` there is a ball
`B_r(w₀) ⊆ D` on which `Hᵐ(G(B)) ≤ t ∫_B J` and `∫_B J ≤ t Hᵐ(G(B))` for every measurable `B`,
where `J(w) = √det(DG(w)*DG(w))`.  `L₀ = DG(w₀)` is injective, so `J₀ = J(w₀) > 0` and
`Hᵐ(L₀(B)) = J₀ Lᵐ(B)`.  On a small ball, `G` is `(1 ± ε)`-bi-Lipschitz relative to `L₀` and
`(1 − ε)J₀ ≤ J ≤ (1 + ε)J₀`, with `ε` chosen so that both sandwiches give the factor `t`. -/
theorem Submission.codim1_zsl_ga_local_comparison : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D : Set (Euclid m)) (t : ℝ) (w₀ : Euclid m), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → 1 < t → w₀ ∈ D → ∃ r : ℝ, 0 < r ∧ ball w₀ r ⊆ D ∧ ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w₀ r → μHE[m] ((fun w => ι w + ι' (g w)) '' B) ≤ ENNReal.ofReal t * ∫⁻ w in B, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) ∧ ∫⁻ w in B, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) ≤ ENNReal.ofReal t * μHE[m] ((fun w => ι w + ι' (g w)) '' B) := by
  intro m k ι ι' g D t w₀ hperp hD hg ht hw₀
  -- step 1: `ε ∈ (0, 1)` with `(1 + ε)ᵐ ≤ t(1 − ε)` and `1 + ε ≤ t(1 − ε)ᵐ`
  obtain ⟨ε, hε0, hε1, hεm, hε1m⟩ := Submission.codim1_zsl_ga_lc_eps_choice m t ht
  -- step 2: `‖h‖ ≤ ‖L₀ h‖` for `L₀ = DG(w₀)`, so `L₀` is injective, `J₀ = J(w₀) > 0` and
  -- `Hᵐ(L₀(S)) = J₀ Lᵐ(S)`
  have hgw₀ : DifferentiableAt ℝ g w₀ :=
    (hg.differentiableOn one_ne_zero).differentiableAt (hD.mem_nhds hw₀)
  set L₀ := fderiv ℝ (fun w => ι w + ι' (g w)) w₀
  have hL₀ : Function.Injective L₀ := by
    intro x y hxy
    have h : ‖x - y‖ ≤ ‖L₀ (x - y)‖ :=
      (Submission.codim1_zsl_ga_lc_graph_fderiv m k ι ι' g w₀ hperp hgw₀).2 (x - y)
    rw [map_sub, hxy, sub_self, norm_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  obtain ⟨hdet, harea⟩ := Submission.codim1_zsl_ga_linear_area m (m + k) L₀ hL₀
  set J : Euclid m → ℝ := fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
    fderiv ℝ (fun w => ι w + ι' (g w)) w).det)
  have hJ₀ : 0 < J w₀ := Real.sqrt_pos.mpr hdet
  -- step 3: `G` is `C¹` on `D`, so `J` is continuous at `w₀`: `|J − J₀| < εJ₀` on `B_δ(w₀)`
  have hG : ContDiffOn ℝ 1 (fun w => ι w + ι' (g w)) D :=
    ι.contDiff.contDiffOn.add (ι'.contDiff.comp_contDiffOn hg)
  obtain ⟨δ, hδ, hJδ⟩ := Metric.continuousAt_iff.mp
    ((Submission.codim1_zsl_ga_lc_jacobian_continuousOn m (m + k) _ D hD hG).continuousAt
      (hD.mem_nhds hw₀)) (ε * J w₀) (mul_pos hε0 hJ₀)
  -- step 4: `G` is `(1 ± ε)`-bi-Lipschitz relative to `L₀` on `B_{r₁}(w₀) ⊆ D`
  obtain ⟨r₁, hr₁, hr₁D, hbil⟩ :=
    Submission.codim1_zsl_ga_lc_local_bilipschitz m k ι ι' g D ε w₀ hperp hD hg hε0 hw₀
  refine ⟨min r₁ δ, lt_min hr₁ hδ, (Metric.ball_subset_ball (min_le_left _ _)).trans hr₁D,
    fun B hB hBr => ?_⟩
  -- step 5: `(1 − ε)ᵐ J₀ Lᵐ(B) ≤ Hᵐ(G(B)) ≤ (1 + ε)ᵐ J₀ Lᵐ(B)`
  have hB₁ : B ⊆ ball w₀ r₁ := hBr.trans (Metric.ball_subset_ball (min_le_left _ _))
  obtain ⟨hHlo, hHhi⟩ := Submission.codim1_zsl_ga_relative_lipschitz_measure m (m + k)
    (fun w => ι w + ι' (g w)) L₀ B (1 - ε) (1 + ε) (by linarith) (by linarith)
    fun x hx y hy => hbil x (hB₁ hx) y (hB₁ hy)
  rw [harea B] at hHlo hHhi
  -- step 6: `(1 − ε) J₀ Lᵐ(B) ≤ ∫_B J ≤ (1 + ε) J₀ Lᵐ(B)`
  have hJB : ∀ w ∈ B, (1 - ε) * J w₀ ≤ J w ∧ J w ≤ (1 + ε) * J w₀ := by
    intro w hw
    have h : |J w - J w₀| < ε * J w₀ :=
      hJδ ((Metric.mem_ball.mp (hBr hw)).trans_le (min_le_right _ _))
    rw [abs_sub_lt_iff] at h
    constructor <;> linarith
  have hIlo : ENNReal.ofReal ((1 - ε) * J w₀) * volume B ≤ ∫⁻ w in B, ENNReal.ofReal (J w) :=
    (setLIntegral_const B _).symm.trans_le
      (setLIntegral_mono' hB fun w hw => ENNReal.ofReal_le_ofReal (hJB w hw).1)
  have hIhi : ∫⁻ w in B, ENNReal.ofReal (J w) ≤ ENNReal.ofReal ((1 + ε) * J w₀) * volume B :=
    (setLIntegral_mono' hB fun w hw => ENNReal.ofReal_le_ofReal (hJB w hw).2).trans_eq
      (setLIntegral_const B _)
  -- step 7: the two sandwiches and the choice of `ε` give the factor `t`
  exact Submission.codim1_zsl_ga_lc_sandwich m t ε (J w₀) (volume B) _ _ hε1 hJ₀.le hεm hε1m
    hHlo hHhi hIlo hIhi

/-- **Area formula for a `C¹` graph over a measurable set** (Simon Ch. 2, 3.2–3.3, for the graph
map `G(w) = ι w + ι' (g w)` of a `g` that is `C¹` on an open `D`, with `ι`, `ι'` linear isometries
with orthogonal ranges): `μHE[m] (G '' A) = ∫⁻_A √det (DG* ∘ DG)` for measurable `A ⊆ D`.
`⟪ι v, G w⟫ = ⟪v, w⟫`, so `G` is injective; it is continuous on `D`.  For `t > 1`, countably many
of the balls of `codim1_zsl_ga_local_comparison` cover `D`; disjointing them cuts `A` into
measurable pieces with disjoint Borel images (Lusin–Souslin), and summing the local comparisons
gives `μHE[m] (G '' A) ≤ t ∫⁻_A J` and `∫⁻_A J ≤ t μHE[m] (G '' A)`.  Let `t ↓ 1`. -/
theorem Submission.codim1_zsl_ga_set_identity : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D A : Set (Euclid m)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → μHE[m] ((fun w => ι w + ι' (g w)) '' A) = ∫⁻ w in A, ENNReal.ofReal (Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) := by
  intro m k ι ι' g D A hperp hD hg hA hAD
  -- steps 2–3 for any injective `G` continuous on `D` and any density `J` comparable with
  -- `B ↦ μHE[m] (G '' B)` up to every factor `t > 1` on small balls around the points of `D`
  have main : ∀ (G : Euclid m → Euclid (m + k)) (J : Euclid m → ℝ≥0∞), Injective G →
      ContinuousOn G D → (∀ t : ℝ, 1 < t → ∀ w ∈ D, ∃ r : ℝ, 0 < r ∧ ball w r ⊆ D ∧
        ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w r →
          μHE[m] (G '' B) ≤ ENNReal.ofReal t * ∫⁻ x in B, J x ∧
            ∫⁻ x in B, J x ≤ ENNReal.ofReal t * μHE[m] (G '' B)) →
      μHE[m] (G '' A) = ∫⁻ x in A, J x := by
    intro G J hinj hcont hloc
    -- step 2: for fixed `t > 1`, `μHE[m] (G '' A) ≤ t ∫_A J` and `∫_A J ≤ t μHE[m] (G '' A)`
    have hstep : ∀ t : ℝ, 1 < t → μHE[m] (G '' A) ≤ ENNReal.ofReal t * ∫⁻ x in A, J x ∧
        ∫⁻ x in A, J x ≤ ENNReal.ofReal t * μHE[m] (G '' A) := by
      intro t ht
      -- (a) a comparison radius at each point of `D` (an arbitrary one elsewhere)
      have hr : ∀ w, ∃ r : ℝ, w ∈ D → 0 < r ∧ ball w r ⊆ D ∧
          ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ ball w r →
            μHE[m] (G '' B) ≤ ENNReal.ofReal t * ∫⁻ x in B, J x ∧
              ∫⁻ x in B, J x ≤ ENNReal.ofReal t * μHE[m] (G '' B) := by
        intro w
        by_cases hw : w ∈ D
        · obtain ⟨r, h⟩ := hloc t ht w hw
          exact ⟨r, fun _ => h⟩
        · exact ⟨1, fun h => absurd h hw⟩
      choose r hr using hr
      -- (b) countably many of these balls cover `D`; enumerate their centres
      obtain ⟨T, hTD, hTc, hDT⟩ := TopologicalSpace.countable_cover_nhdsWithin
        (f := fun w => ball w (r w)) (s := D) fun w hw =>
          mem_nhdsWithin_of_mem_nhds (ball_mem_nhds w (hr w hw).1)
      rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
      · simp
      obtain ⟨e, rfl⟩ := hTc.exists_eq_range <| by
        obtain ⟨x, hx, -⟩ := mem_iUnion₂.1 (hDT (hAD ha))
        exact ⟨x, hx⟩
      set V : ℕ → Set (Euclid m) := fun j => ball (e j) (r (e j))
      -- (c) the pieces `A ∩ disjointed V j` partition `A`, each inside one ball
      have hPm : ∀ j, MeasurableSet (A ∩ disjointed V j) := fun j =>
        hA.inter (MeasurableSet.disjointed (fun _ => measurableSet_ball) j)
      have hPd : Pairwise (Disjoint on fun j => A ∩ disjointed V j) := fun i j hij =>
        Disjoint.mono inter_subset_right inter_subset_right (disjoint_disjointed V hij)
      have hPA : ⋃ j, A ∩ disjointed V j = A := by
        rw [← inter_iUnion, iUnion_disjointed, inter_eq_left]
        intro x hx
        simpa only [biUnion_range] using hDT (hAD hx)
      -- (d) their images are disjoint Borel sets (`G` is injective; Lusin–Souslin)
      have hGm : ∀ j, MeasurableSet (G '' (A ∩ disjointed V j)) := fun j =>
        (hPm j).image_of_continuousOn_injOn (hcont.mono (inter_subset_left.trans hAD))
          hinj.injOn
      have hGd : Pairwise (Disjoint on fun j => G '' (A ∩ disjointed V j)) := fun i j hij =>
        (disjoint_image_iff hinj).2 (hPd hij)
      have hμ : μHE[m] (G '' A) = ∑' j, μHE[m] (G '' (A ∩ disjointed V j)) := by
        conv_lhs => rw [← hPA]
        rw [image_iUnion, measure_iUnion hGd hGm]
      have hJ : ∫⁻ x in A, J x = ∑' j, ∫⁻ x in A ∩ disjointed V j, J x := by
        conv_lhs => rw [← hPA]
        exact lintegral_iUnion hPm hPd J
      -- (e) sum the comparisons on the pieces
      have hc : ∀ j, μHE[m] (G '' (A ∩ disjointed V j)) ≤
            ENNReal.ofReal t * ∫⁻ x in A ∩ disjointed V j, J x ∧
          ∫⁻ x in A ∩ disjointed V j, J x ≤
            ENNReal.ofReal t * μHE[m] (G '' (A ∩ disjointed V j)) := fun j =>
        (hr (e j) (hTD (mem_range_self j))).2.2 _ (hPm j)
          (inter_subset_right.trans (disjointed_subset V j))
      rw [hμ, hJ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
      exact ⟨ENNReal.tsum_le_tsum fun j => (hc j).1, ENNReal.tsum_le_tsum fun j => (hc j).2⟩
    -- step 3: `x ≤ t y` for every `t > 1` gives `x ≤ y` (let `t ↓ 1`)
    have hlim : ∀ x y : ℝ≥0∞, (∀ t : ℝ, 1 < t → x ≤ ENNReal.ofReal t * y) → x ≤ y := by
      intro x y h
      have hty : Tendsto (fun t : ℝ => ENNReal.ofReal t * y) (𝓝[>] 1)
          (𝓝 (ENNReal.ofReal 1 * y)) :=
        ENNReal.Tendsto.mul_const
          ((ENNReal.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds) (Or.inl (by simp))
      simpa using ge_of_tendsto hty (eventually_nhdsWithin_of_forall fun t ht => h t ht)
    exact le_antisymm (hlim _ _ fun t ht => (hstep t ht).1) (hlim _ _ fun t ht => (hstep t ht).2)
  -- step 1: `⟪ι v, G w⟫ = ⟪v, w⟫`, so `G` is injective; `G` is continuous on `D`
  refine main _ _ (fun w₁ w₂ h => ext_inner_left ℝ fun v => ?_)
    (ι.continuous.continuousOn.add (ι'.continuous.comp_continuousOn hg.continuousOn))
    fun t ht w hw => Submission.codim1_zsl_ga_local_comparison m k ι ι' g D t w hperp hD hg ht hw
  simpa only [inner_add_right, LinearIsometry.inner_map_map, hperp, add_zero] using
    congrArg (inner ℝ (ι v)) h
/-- Bochner integrals over an injective continuous image (supplied steps 5–6 of the graph area
formula): if `μ(G(B)) = ∫_B J dLᵐ` for every measurable `B ⊆ A`, then `μ⌞G(A) = φ#ν` for the
measurable embedding `φ = G|_A` of the subtype `A` (Lusin–Souslin) and `ν` the restriction of `J Lᵐ`
to `A`, so `∫_{G(A)} f dμ = ∫_A J·(f ∘ G) dLᵐ` for every `f`. -/
theorem Submission.codim1_zsl_ga_integral_transfer : ∀ (m P : ℕ) (μ : Measure (Euclid P)) (G : Euclid m → Euclid P) (J : Euclid m → ℝ) (A : Set (Euclid m)) (f : Euclid P → ℝ), MeasurableSet A → ContinuousOn G A → InjOn G A → Measurable J → (∀ w ∈ A, 0 ≤ J w) → (∀ B : Set (Euclid m), MeasurableSet B → B ⊆ A → μ (G '' B) = ∫⁻ w in B, ENNReal.ofReal (J w)) → ∫ y in G '' A, f y ∂μ = ∫ w in A, J w * f (G w) := by
  intro m P μ G J A f hA hGc hGi hJm hJ hμ
  -- `G|_A` is a measurable embedding of the subtype `A` (Lusin–Souslin)
  have hφ : MeasurableEmbedding (A.domRestrict G) := hGc.measurableEmbedding hA hGi
  -- `ν` is the restriction to `A` of `J Lᵐ`
  let ν : Measure A := Measure.comap Subtype.val (volume.withDensity fun w => ENNReal.ofReal (J w))
  -- `μ⌞G(A) = (G|_A)#ν`: for measurable `Y`, `Y ∩ G(A) = G(A ∩ G⁻¹Y)`
  have hmap : μ.restrict (G '' A) = Measure.map (A.domRestrict G) ν := by
    ext Y hY
    have hpre : Subtype.val '' (A.domRestrict G ⁻¹' Y) = A ∩ G ⁻¹' Y :=
      Subtype.image_preimage_coe A (G ⁻¹' Y)
    have hB : MeasurableSet (A ∩ G ⁻¹' Y) := hpre ▸ hA.subtype_image (hφ.measurable hY)
    rw [Measure.restrict_apply hY, hφ.map_apply, (MeasurableEmbedding.subtype_coe hA).comap_apply,
      hpre, withDensity_apply _ hB, inter_comm, ← image_inter_preimage, hμ _ hB inter_subset_left]
  calc ∫ y in G '' A, f y ∂μ = ∫ y, f y ∂(Measure.map (A.domRestrict G) ν) := by rw [hmap]
    _ = ∫ x, f (G x) ∂ν := hφ.integral_map f
    _ = ∫ w, f (G w) ∂(Measure.map Subtype.val ν) :=
        ((MeasurableEmbedding.subtype_coe hA).integral_map fun w => f (G w)).symm
    -- `ENNReal.ofReal r = ↑r.toNNReal` by definition
    _ = ∫ w in A, f (G w) ∂(volume.withDensity fun w => ((J w).toNNReal : ℝ≥0∞)) := by
        rw [map_comap_subtype_coe hA]
        rfl
    _ = ∫ w in A, (J w).toNNReal • f (G w) :=
        setIntegral_withDensity_eq_setIntegral_smul hJm.real_toNNReal _ hA
    _ = ∫ w in A, J w * f (G w) := setIntegral_congr_fun hA fun w hw => by
        rw [NNReal.smul_def, Real.coe_toNNReal _ (hJ w hw), smul_eq_mul]
/-- **The coordinate covector `eⱼ ⌟ δ` on `ℝ^{m+1}`** (step 2 of the boundary weak-derivative
computation in the graph-cycle regularity step of Simon 7.4.3).  For `j ∈ Fin (m + 1)` there is a
continuous alternating `m`-form `β` on `ℝ^{m+1}` with `β(e₀, …, êᵢ, …, e_m) = (−1)ʲ` if `i = j`
and `0` otherwise: `β(w₁, …, w_m) = δ(eⱼ, w₁, …, w_m)` for the standard determinant form `δ`. -/
theorem Submission.dgcr_bwd_coordinate_covector : ∀ (m : ℕ) (j : Fin (m + 1)), ∃ β : Covector (Euclid (m + 1)) m, ∀ i : Fin (m + 1), β (i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ))) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
  intro m j
  classical
  -- The standard basis `b l = e_l` and its determinant `δ₀ c = det (c l r)_{r,l}`.
  let b : Module.Basis (Fin (m + 1)) ℝ (Euclid (m + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  have hb : (b : Fin (m + 1) → Euclid (m + 1)) = fun l => EuclideanSpace.single l (1 : ℝ) := by
    funext l; simp [b]
  have hdet : ∀ c : Fin (m + 1) → Euclid (m + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  -- `δ₀` is continuous (entrywise continuous matrix, then `det`), so it is a covector `δ`.
  have hcont : Continuous (fun c : Fin (m + 1) → Euclid (m + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (m + 1)) (m + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  -- `β = δ.curryLeft (b j)`, i.e. `β w = δ (b j, w₁, …, w_m)`.
  refine ⟨δ.curryLeft (b j), fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, ← hb]
  split_ifs with hij
  · -- `i = j`: `(b i, removeNth i b) = b ∘ (cycleRange i)⁻¹`, of sign `(−1)ⁱ`.
    subst hij
    have hc : (Matrix.vecCons (b i) (i.removeNth ⇑b) : Fin (m + 1) → Euclid (m + 1)) =
        ⇑b ∘ ⇑(Equiv.symm i.cycleRange) :=
      Fin.cons_removeNth_eq_comp_cycleRange_symm (⇑b) i
    rw [hc, AlternatingMap.map_perm, Module.Basis.det_self, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp [Units.smul_def]
  · -- `i ≠ j`: `e_j` occurs at positions `0` and `l.succ`, where `i.succAbove l = j`.
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := l.succ)
    · simp [Fin.removeNth_apply, hl]
    · exact (Fin.succ_ne_zero l).symm
/-- Translations are continuous in measure on balls: for measurable `F ⊆ ℝᵐ`,
`Lᵐ(((F − z) Δ F) ∩ B_R(0)) → 0` as `z → 0`, where `F − z = {v : v + z ∈ F}`.  Inner and outer
regularity give `K ⊆ A = F ∩ B_{R+1}(0) ⊆ O`, `K` compact, `O` open, with `Lᵐ(A \ K)` and
`Lᵐ(O \ A)` below `ε / 4`, and some `δ > 0` with the `δ`-thickening of `K` inside `O`.  For
`|z| < min(δ, 1)` the set lies in `((A \ K) − z) ∪ (O \ A) ∪ (A \ K) ∪ ((O \ A) − z)`, whose
measure is at most `ε` by translation invariance. -/
theorem Submission.codim1_zsl_pc_translate_tendsto_zero : ∀ (m : ℕ) (F : Set (Euclid m)) (R : ℝ), MeasurableSet F → Tendsto (fun z : Euclid m => volume (symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R)) (𝓝 0) (𝓝 0) := by
  intro m F R hF
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε4 : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  -- the bounded piece `A = F ∩ B(0, R+1)` of `F`
  obtain ⟨A, hA⟩ : ∃ A : Set (Euclid m), A = F ∩ ball (0 : Euclid m) (R + 1) := ⟨_, rfl⟩
  have hmem : ∀ v : Euclid m, v ∈ A ↔ v ∈ F ∧ ‖v‖ < R + 1 := by
    intro v
    rw [hA, Set.mem_inter_iff, mem_ball_zero_iff]
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact hF.inter measurableSet_ball
  have hAfin : volume A ≠ ∞ := by
    rw [hA]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) measure_ball_lt_top)
  -- inner and outer regularity: `K ⊆ A ⊆ O`, `K` compact, `O` open
  obtain ⟨K, hKA, hKc, hK⟩ := hAmeas.exists_isCompact_sdiff_lt hAfin hε4
  obtain ⟨O, hAO, hOo, -, hO⟩ := hAmeas.exists_isOpen_sdiff_lt hAfin hε4
  -- a uniform margin: `thickening δ K ⊆ O`
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_thickening_subset_open hOo (hKA.trans hAO)
  filter_upwards [ball_mem_nhds (0 : Euclid m) (lt_min hδ one_pos)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hzδ : ‖z‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have hsub : symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R ⊆
      ((fun v => v + z) ⁻¹' (A \ K) ∪ (O \ A)) ∪ ((A \ K) ∪ (fun v => v + z) ⁻¹' (O \ A)) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [mem_ball_zero_iff] at hv2
    have hvA : ‖v‖ < R + 1 := by linarith
    have hvzA : ‖v + z‖ < R + 1 :=
      calc ‖v + z‖ ≤ ‖v‖ + ‖z‖ := norm_add_le _ _
        _ < R + 1 := by linarith
    rcases Set.mem_symmDiff.1 hv1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `v + z ∈ F`, `v ∉ F`
      rw [mem_preimage] at ha
      left
      by_cases hK' : v + z ∈ K
      · right
        refine ⟨hδO (mem_thickening_iff.2 ⟨v + z, hK', ?_⟩), fun h => hb ((hmem v).1 h).1⟩
        rw [dist_self_add_right]
        exact hzδ
      · left
        exact ⟨(hmem (v + z)).2 ⟨ha, hvzA⟩, hK'⟩
    · -- `v ∈ F`, `v + z ∉ F`
      rw [mem_preimage] at hb
      right
      by_cases hK' : v ∈ K
      · right
        refine ⟨hδO (mem_thickening_iff.2 ⟨v, hK', ?_⟩), fun h => hb ((hmem (v + z)).1 h).1⟩
        rw [dist_self_add_left]
        exact hzδ
      · left
        exact ⟨(hmem v).2 ⟨ha, hvA⟩, hK'⟩
  calc volume (symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R)
      ≤ volume (((fun v => v + z) ⁻¹' (A \ K) ∪ (O \ A)) ∪
          ((A \ K) ∪ (fun v => v + z) ⁻¹' (O \ A))) := measure_mono hsub
    _ ≤ (volume ((fun v => v + z) ⁻¹' (A \ K)) + volume (O \ A)) +
          (volume (A \ K) + volume ((fun v => v + z) ⁻¹' (O \ A))) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ = (volume (A \ K) + volume (O \ A)) + (volume (A \ K) + volume (O \ A)) := by
        rw [measure_preimage_add_right (volume : Measure (Euclid m)) z (A \ K),
          measure_preimage_add_right (volume : Measure (Euclid m)) z (O \ A)]
    _ ≤ (ε / 2 / 2 + ε / 2 / 2) + (ε / 2 / 2 + ε / 2 / 2) :=
        add_le_add (add_le_add hK.le hO.le) (add_le_add hK.le hO.le)
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- Mollifying `u = 1_F` with any continuous `ρ ≥ 0`, `∫ρ = 1`, `spt ρ ⊆ B̄_δ(0)`, moves it by at
most `η` in `L¹(B_R(0))` once `δ` is small (Simon 2.5).  By `∫ρ = 1`,
`|ρ * u(v) - u(v)| ≤ ∫ρ(z)|u(v - z) - u(v)| dz`; Tonelli bounds `∫_{B_R}|ρ * u - u|` by
`∫ρ(z) L^m(((F + z) Δ F) ∩ B_R) dz`, and `codim1_zsl_pc_translate_tendsto_zero` makes the
translation defect `≤ η` for `|z| ≤ δ`. -/
theorem Submission.codim1_zsl_pc_mollify_indicator_l1 : ∀ (m : ℕ) (F : Set (Euclid m)) (R η : ℝ), MeasurableSet F → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : Euclid m → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z, δ < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤ ENNReal.ofReal η := by
  intro m F R η hF hη
  -- `δ = ε/2`, where the translation defect is `< η` on `B_ε(0)`.
  have hev : ∀ᶠ y in 𝓝 (0 : Euclid m),
      volume (symmDiff ((fun v => v + y) ⁻¹' F) F ∩ ball (0 : Euclid m) R) < ENNReal.ofReal η :=
    (Submission.codim1_zsl_pc_translate_tendsto_zero m F R hF).eventually
      (eventually_lt_nhds (ENNReal.ofReal_pos.2 hη))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro ρ hρc hρ0 hρsupp hρ1
  -- Facts about the indicator `u = 1_F`, which is then made opaque.
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hu_bd : ∀ x, ‖F.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  have hu_sd : ∀ v y : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) (v + y) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
        = (symmDiff ((fun w => w + y) ⁻¹' F) F).indicator 1 v := by
    intro v y
    by_cases h1 : v + y ∈ F <;> by_cases h2 : v ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  generalize F.indicator (fun _ => (1 : ℝ)) = u at hu_meas hu_bd hu_sd ⊢
  -- `ρ` is integrable (compact support), hence so is each convolution integrand.
  have hρ_cs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) (ε / 2)) fun x hx => ?_
    apply hρsupp
    simpa using hx
  have hρ_int : Integrable ρ := hρc.integrable_of_hasCompactSupport hρ_cs
  have hρ_meas : Measurable ρ := hρc.measurable
  have hint : ∀ v, Integrable (fun z => ρ z * u (v - z)) := by
    intro v
    refine hρ_int.mono
      (by exact (hρ_meas.mul (hu_meas.comp (measurable_const_sub v))).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    calc ‖ρ z‖ * ‖u (v - z)‖ ≤ ‖ρ z‖ * 1 := by gcongr; exact hu_bd _
      _ = ‖ρ z‖ := mul_one _
  -- Pointwise bound, using `∫ ρ = 1`.
  have hpt : ∀ v, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ ≤ ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ := by
    intro v
    have h1 : (∫ z, ρ z * u (v - z)) - u v = ∫ z, (ρ z * u (v - z) - ρ z * u v) := by
      rw [integral_sub (hint v) (hρ_int.mul_const (u v)), integral_mul_const (u v) ρ, hρ1,
        one_mul]
    rw [h1]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [← mul_sub, enorm_mul]
  -- The inner integral is the translation defect of `codim1_zsl_pc_translate_tendsto_zero`.
  have hΦ : ∀ z, ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ
      = volume (symmDiff ((fun v => v + -z) ⁻¹' F) F ∩ ball (0 : Euclid m) R) := by
    intro z
    have hS : MeasurableSet (symmDiff ((fun v => v + -z) ⁻¹' F) F) :=
      (hF.preimage (measurable_add_const _)).symmDiff hF
    rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
    refine lintegral_congr fun v => ?_
    rw [sub_eq_add_neg v z]
    exact hu_sd v (-z)
  have hmeas : Measurable (Function.uncurry fun (v z : Euclid m) =>
      ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m => ‖ρ p.2‖ₑ * ‖u (p.1 - p.2) - u p.1‖ₑ :=
      (hρ_meas.comp measurable_snd).enorm.mul
        ((hu_meas.comp (measurable_fst.sub measurable_snd)).sub
          (hu_meas.comp measurable_fst)).enorm
    exact this
  -- Tonelli, then `Φ(-z) ≤ η` wherever `ρ z ≠ 0`, and `∫⁻ ‖ρ‖ₑ = ofReal (∫ ρ) = 1`.
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_mono fun v => hpt v
    _ = ∫⁻ z, ∫⁻ v in ball (0 : Euclid m) R, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ z, ‖ρ z‖ₑ * ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ := by
        refine lintegral_congr fun z => ?_
        exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ z, ‖ρ z‖ₑ * ENNReal.ofReal η := by
        refine lintegral_mono fun z => ?_
        by_cases hz : ρ z = 0
        · simp [hz]
        · have hz' : ‖z‖ ≤ ε / 2 := by
            by_contra h
            exact hz (hρsupp z (not_le.1 h))
          gcongr
          rw [hΦ z]
          refine (hεP ?_).le
          rw [dist_zero_right, norm_neg]
          linarith
    _ = (∫⁻ z, ‖ρ z‖ₑ) * ENNReal.ofReal η := lintegral_mul_const _ (by fun_prop)
    _ = ENNReal.ofReal η := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hρ_int]
        have : (fun x => ‖ρ x‖) = ρ := funext fun x => Real.norm_of_nonneg (hρ0 x)
        rw [this, hρ1, ENNReal.ofReal_one, one_mul]
/-- `L¹` translation estimate for a `C¹` function `f : ℝᵐ → ℝ`:
`∫_{B_R(0)} |f(v + h) − f(v)| dv ≤ |h| ∫_{B_{R+|h|}(0)} ‖Df(w)‖ dw`.  By the fundamental theorem
of calculus along `t ↦ v + t h`, `|f(v + h) − f(v)| ≤ |h| ∫₀¹ ‖Df(v + t h)‖ dt`; integrate over
`B_R(0)`, exchange the order of integration (Tonelli) and use, for `t ∈ (0, 1]`, the inclusion
`B_R(0) + t h ⊆ B_{R+|h|}(0)` and the translation invariance of Lebesgue measure. -/
theorem Submission.codim1_zsl_pc_smooth_translate_l1 : ∀ (m : ℕ) (f : Euclid m → ℝ) (h : Euclid m) (R : ℝ), ContDiff ℝ 1 f → ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ ≤ ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
  intro m f h R hf
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hGc : Continuous (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hcont.enorm
  have hGm : Measurable (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hGc.measurable
  have hshift : Continuous (fun p : Euclid m × ℝ => p.1 + p.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hmeas2 : Measurable (uncurry fun (v : Euclid m) (t : ℝ) => ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    (hGc.comp hshift).measurable
  -- Steps 1–2: pointwise bound via the fundamental theorem of calculus along `t ↦ v + t • h`
  have key : ∀ v : Euclid m, ‖f (v + h) - f v‖ₑ ≤
      ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := by
    intro v
    have hseg : Continuous (fun t : ℝ => v + t • h) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (v + s • h))
        (fderiv ℝ f (v + t • h) h) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => v + s • h) h t :=
        (((hasDerivAt_id' t).smul_const h).const_add v).congr_deriv (one_smul ℝ h)
      exact (hdiff (v + t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have hc1 : Continuous (fun t : ℝ => fderiv ℝ f (v + t • h) h) :=
      (hcont.comp hseg).clm_apply continuous_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hc1.intervalIntegrable 0 1)
    simp only [one_smul, zero_smul, add_zero] at hFTC
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (v + t • h) h‖ₑ
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h) h‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_mono fun t =>
            (ContinuousLinearMap.le_opENorm (fderiv ℝ f (v + t • h)) h).trans_eq (mul_comm _ _)
      _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_const_mul _ (hGc.comp hseg).measurable
  have hmeasv : Measurable
      (fun v : Euclid m => ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    hmeas2.lintegral_prod_right
  -- Step 4: translation invariance of Lebesgue measure and inclusion of balls
  have hball : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ ≤
      ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
    intro t ht
    have ht' : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg h) ht.2
    have hsub : ball (0 : Euclid m) R ⊆
        (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖) := by
      intro v hv
      rw [mem_preimage, mem_ball_zero_iff]
      exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le (mem_ball_zero_iff.mp hv) ht')
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ
        ≤ ∫⁻ v in (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖),
            ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
          (measurePreserving_add_right volume (t • h)).setLIntegral_comp_preimage
            measurableSet_ball hGm
  -- Steps 3 and 5: integrate, exchange the order of integration (Tonelli), and conclude
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R,
          ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono key
    _ = ‖h‖ₑ * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_const_mul _ hmeasv
    _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ :=
        congrArg (‖h‖ₑ * ·) (lintegral_lintegral_swap hmeas2.aemeasurable)
    _ ≤ ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hball) _
    _ = ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
/-- Integration by parts for a Lipschitz `u` against `C¹` fields `Φᵢ` with compact support in
`B = B_R(0)`: `∫_B Σᵢ Du(x)eᵢ Φᵢ(x) dx = −∫_B u(x) Σᵢ DΦᵢ(x)eᵢ dx`.  Each `Φᵢ` is Lipschitz, so
Lipschitz integration by parts in direction `eᵢ` (`LipschitzWith.integral_lineDeriv_mul_eq`) applies
on `ℝⁿ`; by Rademacher, `lineDeriv u x eᵢ = Du(x)eᵢ` for a.e. `x`.  Both integrands are integrable
(`Du` is bounded by the Lipschitz constant) and vanish off `B`, so summing over `i` concludes. -/
theorem Submission.dorag_ha_lsc_ibp_lipschitz : ∀ (n : ℕ) (R : ℝ) (u : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∃ L : NNReal, LipschitzWith L u) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R u Φ ⟨L, hu⟩ hΦ hΦc hΦs
  set e : Fin n → Euclid n := fun i => EuclideanSpace.single i (1 : ℝ)
  have hΦL : ∀ i, ∃ C, LipschitzWith C (Φ i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hΦc i) (hΦ i) one_ne_zero
  choose C hC using hΦL
  -- integrability of the two families of integrands
  have hint1 : ∀ i, Integrable (fun x => fderiv ℝ u x (e i) * Φ i x) := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hΦ i).continuous.integrable_of_hasCompactSupport (hΦc i))
      (measurable_fderiv_apply_const ℝ u (e i)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    exact ((fderiv ℝ u x).le_opNorm (e i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  have hcontd : ∀ i, Continuous fun x => fderiv ℝ (Φ i) x (e i) := fun i =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint2 : ∀ i, Integrable (fun x => u x * fderiv ℝ (Φ i) x (e i)) := by
    intro i
    refine (hu.continuous.mul (hcontd i)).integrable_of_hasCompactSupport ?_
    exact ((hΦc i).fderiv_apply (𝕜 := ℝ) (e i)).mul_left
  -- per-coordinate identity on the whole space
  have key : ∀ i, ∫ x, fderiv ℝ u x (e i) * Φ i x = -∫ x, u x * fderiv ℝ (Φ i) x (e i) := by
    intro i
    have h1 :=
      hu.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid n))) (hC i) (hΦc i) (e i)
    have h2 : (fun x => lineDeriv ℝ u x (e i) * Φ i x) =ᵐ[volume]
        fun x => fderiv ℝ u x (e i) * Φ i x := by
      filter_upwards [hu.ae_differentiableAt] with x hx
      rw [hx.lineDeriv_eq_fderiv]
    have h3 : (fun x => lineDeriv ℝ (Φ i) x (-e i) * u x) =
        fun x => -(u x * fderiv ℝ (Φ i) x (e i)) := by
      funext x
      rw [(((hΦ i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
      ring
    rw [integral_congr_ae h2, h3, integral_neg] at h1
    exact h1
  -- integrands vanish off the ball
  have hzero1 : ∀ x, x ∉ ball (0 : Euclid n) R →
      ∑ i : Fin n, fderiv ℝ u x (e i) * Φ i x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hzero2 : ∀ x, x ∉ ball (0 : Euclid n) R →
      u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (e i) = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key i

namespace Submission

/-- Integration by parts on `B = B_R(0)` for `h` that is only `C¹` on `B`, against `C¹` fields
`Φᵢ` with compact support in `B`: `∫_B Σᵢ Dᵢh Φᵢ = -∫_B h Σᵢ DᵢΦᵢ`.  The supports of the `Φᵢ` lie
in some `B_{r₁}(0)`, `r₁ < R`.  A bump `χ` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ ⊆ B` makes
`h̃ = χh` a compactly supported `C¹`, hence Lipschitz, function, so `dorag_ha_lsc_ibp_lipschitz`
applies to `h̃`; both integrands only see `B_{r₁}(0)`, where `h̃ = h`. -/
theorem dorag_ha_lsc_ibp_c1_ball : ∀ (n : ℕ) (R : ℝ) (h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R h Φ hh hΦ hΦc hΦs
  -- `R ≤ 0`: the ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]; simp
  -- The supports of the `Φᵢ` lie in a smaller ball `B_{r₁}(0)`, `0 < r₁ < R`.
  set K := ⋃ i, tsupport (Φ i)
  have hKc : IsClosed K := isClosed_iUnion_of_finite fun i => isClosed_tsupport _
  have hKB : K ⊆ ball 0 R := iUnion_subset hΦs
  obtain ⟨r₁, ⟨hr₁0, hr₁R⟩, hK₁⟩ := exists_pos_lt_subset_ball hR hKc hKB
  -- `h̃ = χh` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ = B̄_{(r₁+R)/2}(0) ⊆ B` is `C¹_c`.
  let χ : ContDiffBump (0 : Euclid n) := ⟨r₁, (r₁ + R) / 2, hr₁0, by linarith⟩
  set ht : Euclid n → ℝ := fun x => χ x * h x
  have hχsupp : tsupport χ ⊆ ball 0 R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (show (r₁ + R) / 2 < R by linarith)
  have htC : ContDiff ℝ 1 ht := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact ((χ.contDiff.contDiffOn).mul hh).contDiffAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : ht =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [ht, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have htc : HasCompactSupport ht := χ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport htc htC one_ne_zero
  have key := Submission.dorag_ha_lsc_ibp_lipschitz n R ht Φ ⟨C, hC⟩ hΦ hΦc hΦs
  -- On `B_{r₁}(0)`, `h̃ = h` near each point; off it, every `Φᵢ` and `DΦᵢ` vanishes.
  have hone : ∀ y ∈ ball (0 : Euclid n) r₁, ht y = h y := by
    intro y hy
    simp [ht, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hEq : ∀ x ∈ ball (0 : Euclid n) r₁, ht =ᶠ[𝓝 x] h := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using hone y hy
  have hout : ∀ x, x ∉ ball (0 : Euclid n) r₁ → ∀ i, x ∉ tsupport (Φ i) :=
    fun x hx i h' => hx (hK₁ (mem_iUnion.2 ⟨i, h'⟩))
  have h1 : ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x =
      ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ ht x (EuclideanSpace.single i (1 : ℝ)) * Φ i x := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [(hEq x hx).fderiv_eq]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [image_eq_zero_of_notMem_tsupport (hout x hx i)]
  have h2 : ∫ x in ball (0 : Euclid n) R,
        h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ x in ball (0 : Euclid n) R,
        ht x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [hone x hx]
    · have : ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [fderiv_of_notMem_tsupport ℝ (hout x hx i)]; rfl
      simp only [this, mul_zero]
  rw [h1, h2, key]

/-- Duality bound for the variation of a smooth `g` (Simon Ch. 2, 2.5 (4)): if `∫ g div ψ ≤ c`
for every `C^∞` field `ψ` with compact support in `B = B_r(0)` and `|ψ| ≤ 1`, then
`∫_B |Dg| ≤ c`.  Applied to the coordinates `ψᵢ`, `dorag_ha_lsc_ibp_c1_ball` gives
`∫ g div ψ = -∫_B Σᵢ Dg(eᵢ) ψᵢ`.  With the gradient `G = ∇g`, `θₖ = 1/(k+1)` and bumps `χₖ`
with `χₖ = 1` on `B̄_{r(1-θₖ/2)}(0)` and `spt χₖ ⊆ B`, the fields
`ψₖ = -χₖ G/√(|G|² + θₖ²)` are admissible, so `∫_B χₖ |G|²/√(|G|² + θₖ²) ≤ c`.  The integrands
tend to `|G| = |Dg|` on `B`, and Fatou's lemma concludes. -/
theorem codim1_zsl_pc_smooth_grad_bound : ∀ (m : ℕ) (g : Euclid m → ℝ) (r c : ℝ), ContDiff ℝ (⊤ : ℕ∞) g → (∀ ψ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap ≤ c) → ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ g v‖ₑ ≤ ENNReal.ofReal c := by
  intro m g r c hg hψ
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]; simp
  set B := ball (0 : Euclid m) r with hB
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  -- Step 1: integration by parts in trace form, from `dorag_ha_lsc_ibp_c1_ball`.
  have ibp : ∀ ψ : Euclid m → Euclid m, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
      ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = -∫ v in B, ∑ i : Fin m, fderiv ℝ g v (EuclideanSpace.single i (1:ℝ)) * ψ v i := by
    intro ψ hψ1 hψc hψB
    have key := Submission.dorag_ha_lsc_ibp_c1_ball m r g (fun i x => ψ x i)
      (hg.of_le h1).contDiffOn (fun i => (contDiff_piLp 2).1 hψ1 i)
      (fun i => hψc.comp_left (g := fun w : Euclid m => w i) (by simp))
      (fun i => (tsupport_comp_subset (g := fun w : Euclid m => w i) (by simp) ψ).trans hψB)
    have hd : ∀ v (i : Fin m), fderiv ℝ (fun x => ψ x i) v
        = (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ ψ v) := fun v i => by
      have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (ψ v) i).comp v
        ((hψ1.differentiable one_ne_zero) v).hasFDerivAt
      exact h.fderiv
    have htr : ∀ v, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = ∑ i : Fin m, fderiv ℝ (fun x => ψ x i) v (EuclideanSpace.single i 1) := by
      intro v
      rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin m) ℝ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd]
      simp [EuclideanSpace.inner_single_left]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) ?_]
    · simp_rw [htr]
      simp only [] at key
      rw [key, neg_neg]
    · intro v hv
      have : fderiv ℝ ψ v = 0 := by
        by_contra hne
        exact hv (hψB (support_fderiv_subset ℝ hne))
      simp [this]
  -- Step 2: the gradient field `G = ∇g`.
  set L := fderiv ℝ g with hLdef
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := (contDiff_infty_iff_fderiv.1 hg).2
  set G : Euclid m → Euclid m := fun v => (InnerProductSpace.toDual ℝ (Euclid m)).symm (L v)
    with hGdef
  have hGi : ∀ v (i : Fin m), G v i = L v (EuclideanSpace.single i 1) := by
    intro v i
    have := EuclideanSpace.inner_single_left i (1:ℝ) (G v)
    rw [real_inner_comm, hGdef, InnerProductSpace.toDual_symm_apply] at this
    simpa using this.symm
  have hGn : ∀ v, ‖G v‖ = ‖L v‖ := fun v => LinearIsometryEquiv.norm_map _ _
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_piLp 2]
    intro i
    have : (fun x => G x i) = fun x => L x (EuclideanSpace.single i 1) := funext fun x => hGi x i
    rw [this]
    exact hL.clm_apply contDiff_const
  have hsum : ∀ v, ∑ i : Fin m, L v (EuclideanSpace.single i 1) * G v i = ‖G v‖ ^ 2 := by
    intro v
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hGi, Real.norm_eq_abs, sq_abs, sq]
  -- Step 3: parameters `θₖ`, bump cut-offs `χₖ` and test fields `ψₖ`.
  set θ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hθdef
  have hθpos : ∀ k, 0 < θ k := fun k => by positivity
  have hθle : ∀ k, θ k ≤ 1 := fun k => by
    rw [hθdef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ri : ℕ → ℝ := fun k => r * (1 - θ k / 2) with hridef
  set ro : ℕ → ℝ := fun k => r * (1 - θ k / 4) with hrodef
  have hri : ∀ k, 0 < ri k := fun k => mul_pos hr (by linarith [hθle k])
  have hrio : ∀ k, ri k < ro k := fun k => mul_lt_mul_of_pos_left (by linarith [hθpos k]) hr
  have hro : ∀ k, ro k < r := fun k => mul_lt_of_lt_one_right hr (by linarith [hθpos k])
  let χ : ℕ → ContDiffBump (0 : Euclid m) := fun k => ⟨ri k, ro k, hri k, hrio k⟩
  have hχ1 : ∀ v ∈ B, ∀ᶠ k in atTop, χ k v = 1 := by
    intro v hv
    have hlim : Tendsto ri atTop (𝓝 r) := by
      have := (tendsto_const_nhds (x := r)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub (hθlim.div_const 2))
      simpa using this
    have hv' : ‖v‖ < r := by simpa [hB] using hv
    filter_upwards [hlim.eventually_const_lt hv'] with k hk
    exact (χ k).one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hk.le)
  set s : ℕ → Euclid m → ℝ := fun k v => √(‖G v‖ ^ 2 + θ k ^ 2) with hsdef
  have hspos : ∀ k v, 0 < s k v := fun k v => Real.sqrt_pos.2 (by have := hθpos k; positivity)
  have hGs : ∀ k v, ‖G v‖ ≤ s k v := fun k v =>
    Real.le_sqrt_of_sq_le (by have := hθpos k; nlinarith)
  have hsc : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (s k) := fun k =>
    ((hG.norm_sq ℝ).add contDiff_const).sqrt (fun v => by have := hθpos k; positivity)
  set ψ : ℕ → Euclid m → Euclid m := fun k v => (-(χ k v / s k v)) • G v with hψdef
  set f : ℕ → Euclid m → ℝ := fun k v => χ k v * (‖G v‖ ^ 2 / s k v) with hfdef
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := fun k =>
    (((χ k).contDiff.div (hsc k) (fun v => (hspos k v).ne')).neg).smul hG
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ closedBall 0 (ro k) := by
    intro k
    rw [← (χ k).tsupport_eq]
    apply closure_mono
    intro v hv
    rw [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [hψdef, h0]
  have hψB : ∀ k, tsupport (ψ k) ⊆ B := fun k => (hψsupp k).trans (closedBall_subset_ball (hro k))
  have hψc : ∀ k, HasCompactSupport (ψ k) := fun k =>
    (isCompact_closedBall 0 (ro k)).of_isClosed_subset (isClosed_tsupport _) (hψsupp k)
  have hψn : ∀ k v, ‖ψ k v‖ ≤ 1 := by
    intro k v
    have hχ0 := (χ k).nonneg (x := v)
    have hχ1' := (χ k).le_one (x := v)
    simp only [hψdef, norm_smul, norm_neg, norm_div, Real.norm_eq_abs, abs_of_nonneg hχ0,
      abs_of_pos (hspos k v)]
    rw [div_mul_eq_mul_div, div_le_one (hspos k v)]
    calc χ k v * ‖G v‖ ≤ 1 * s k v := mul_le_mul hχ1' (hGs k v) (norm_nonneg _) zero_le_one
      _ = s k v := one_mul _
  -- Step 4: `∫ g div ψₖ = ∫_B fₖ ≤ c`.
  have hint_eq : ∀ k, ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ (ψ k) v).toLinearMap
      = ∫ v in B, f k v := by
    intro k
    rw [ibp (ψ k) ((hψs k).of_le h1) (hψc k) (hψB k), ← integral_neg]
    congr 1
    funext v
    have : ∀ i : Fin m, L v (EuclideanSpace.single i 1) * (ψ k v) i
        = -(χ k v / s k v) * (L v (EuclideanSpace.single i 1) * G v i) := fun i => by
      simp only [hψdef, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this, ← Finset.mul_sum, hsum, hfdef]
    ring
  have hle : ∀ k, ∫ v in B, f k v ≤ c := fun k =>
    (hint_eq k) ▸ hψ (ψ k) (hψs k) (hψc k) (hψB k) (hψn k)
  have hfc : ∀ k, Continuous (f k) := fun k =>
    (χ k).continuous.mul (((continuous_norm.comp hG.continuous).pow 2).div (hsc k).continuous
      (fun v => (hspos k v).ne'))
  have hfnn : ∀ k v, 0 ≤ f k v := fun k v =>
    mul_nonneg (χ k).nonneg (div_nonneg (sq_nonneg _) (hspos k v).le)
  have hfi : ∀ k, IntegrableOn (f k) B := fun k =>
    ((hfc k).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euclid m) r)).mono_set
      ball_subset_closedBall
  have hbound : ∀ k, ∫⁻ v in B, ENNReal.ofReal (f k v) ≤ ENNReal.ofReal c := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (ae_of_all _ (hfnn k))]
    exact ENNReal.ofReal_le_ofReal (hle k)
  -- Step 5: `fₖ → ‖Dg‖` on `B`, and Fatou's lemma.
  have htend : ∀ v ∈ B, Tendsto (fun k => ENNReal.ofReal (f k v)) atTop
      (𝓝 (ENNReal.ofReal ‖G v‖)) := by
    intro v hv
    apply ENNReal.tendsto_ofReal
    have hχt : Tendsto (fun k => χ k v) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [hχ1 v hv] with k hk; exact hk.symm)
    have hq : Tendsto (fun k => ‖G v‖ ^ 2 / s k v) atTop (𝓝 ‖G v‖) := by
      rcases eq_or_ne ‖G v‖ 0 with h0 | h0
      · simp [h0]
      · have hs : Tendsto (fun k => s k v) atTop (𝓝 (√(‖G v‖ ^ 2 + 0 ^ 2))) :=
          (tendsto_const_nhds.add (hθlim.pow 2)).sqrt
        have hne : √(‖G v‖ ^ 2 + 0 ^ 2) ≠ 0 := by
          rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]; exact h0
        have := (tendsto_const_nhds (x := ‖G v‖ ^ 2)).div hs hne
        convert this using 2
        rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _), sq, mul_self_div_self]
    have := hχt.mul hq
    rw [one_mul] at this
    exact this
  calc ∫⁻ v in B, ‖L v‖ₑ = ∫⁻ v in B, liminf (fun k => ENNReal.ofReal (f k v)) atTop := by
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        rw [(htend v hv).liminf_eq, hGn, ofReal_norm]
    _ ≤ liminf (fun k => ∫⁻ v in B, ENNReal.ofReal (f k v)) atTop :=
        lintegral_liminf_le (fun k => (hfc k).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end Submission
/-- Mollifying a test field (Simon Ch. 2, 2.5): with the reflected kernel `ρ̌(z) = ρ(-z)`, the
field `ψ' = ρ̌ ⋆ ψ` is `C^∞`, has compact support in `B_{r+ε}(0)` (`spt ψ ⊆ B_{r₁}(0)`, `r₁ < r`,
and `spt ρ̌ ⊆ B̄_ε(0)`) and satisfies `|ψ'| ≤ ∫ρ̌ = 1`.  Differentiating under the convolution and
commuting the trace with the integral gives `div ψ'(w) = ∫ ρ(z) div ψ(w + z) dz`; Fubini and the
measure-preserving shear `(v, z) ↦ (v + z, z)` then turn `∫ (ρ ⋆ 1_F) div ψ` into `∫_F div ψ'`. -/
theorem Submission.codim1_zsl_pc_mollify_test_field : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (ψ : Euclid m → Euclid m) (r ε : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∃ ψ' : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ HasCompactSupport ψ' ∧ tsupport ψ' ⊆ ball (0 : Euclid m) (r + ε) ∧ (∀ v, ‖ψ' v‖ ≤ 1) ∧ ∫ v, (∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap = ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap := by
  intro m F ρ ψ r ε hF hρ hρ0 hρε hρ1 hψ hψcs hψr hψ1
  -- basic facts about `ρ` and its reflection `ρ'`
  have hρc : Continuous ρ := hρ.continuous
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε z (by simpa using hz))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  set ρ' : Euclid m → ℝ := fun z => ρ (-z) with hρ'_def
  have hρ'c : Continuous ρ' := hρc.comp continuous_neg
  have hρ'cs : HasCompactSupport ρ' :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε (-z) (by simpa using hz))
  have hρ'smooth : ContDiff ℝ (⊤ : ℕ∞) ρ' := hρ.comp contDiff_neg
  have hρ'i : Integrable ρ' := hρ'c.integrable_of_hasCompactSupport hρ'cs
  have hρ'1 : ∫ z, ρ' z = 1 := by
    rw [show (∫ z, ρ' z) = ∫ z, ρ (-z) from rfl, integral_neg_eq_self ρ volume]
    exact hρ1
  -- the trace as a continuous linear map
  obtain ⟨Tr, hTr⟩ : ∃ Tr : (Euclid m →L[ℝ] Euclid m) →L[ℝ] ℝ, ∀ A : Euclid m →L[ℝ] Euclid m,
      Tr A = LinearMap.trace ℝ (Euclid m) A.toLinearMap :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid m)) ∘ₗ (ContinuousLinearMap.coeLM ℝ)), fun A => rfl⟩
  -- the mollified field `ψ' = ρ' ⋆ ψ`
  set L : ℝ →L[ℝ] Euclid m →L[ℝ] Euclid m := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set ψ' : Euclid m → Euclid m := convolution ρ' ψ L volume with hψ'_def
  have hψ'apply : ∀ w, ψ' w = ∫ t, ρ' t • ψ (w - t) := by
    intro w
    rw [hψ'_def, convolution_def]
    simp [L]
  -- support
  obtain ⟨r₁, hr₁r, hr₁⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψr
  have hsupp : support ψ' ⊆ closedBall 0 (r₁ + ε) := by
    intro w hw
    rw [Function.mem_support, hψ'apply] at hw
    by_contra hcon
    apply hw
    have hzero : ∀ t, ρ' t • ψ (w - t) = 0 := by
      intro t
      by_cases h1 : ρ' t = 0
      · simp [h1]
      by_cases h2 : ψ (w - t) = 0
      · simp [h2]
      exfalso
      apply hcon
      have ht : ‖t‖ ≤ ε := by
        by_contra h
        push Not at h
        exact h1 (hρε (-t) (by rwa [norm_neg]))
      have hwt : w - t ∈ ball (0 : Euclid m) r₁ := hr₁ (subset_tsupport ψ h2)
      rw [mem_ball_zero_iff] at hwt
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖(w - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ r₁ + ε := by linarith
    simp [hzero]
  have htsupp : tsupport ψ' ⊆ closedBall 0 (r₁ + ε) := closure_minimal hsupp isClosed_closedBall
  -- derivative of `ψ'` and its trace
  have hderiv : ∀ w, fderiv ℝ ψ' w =
      convolution ρ' (fderiv ℝ ψ) (ContinuousLinearMap.precompR (Euclid m) L) volume w := fun w =>
    (hψcs.hasFDerivAt_convolution_right L hρ'i.locallyIntegrable
      (hψ.of_le (by exact_mod_cast le_top)) w).fderiv
  have hG' : ∀ w, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
      ∫ z, ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap := by
    intro w
    have hint : Integrable (fun t => ρ' t • fderiv ℝ ψ (w - t)) :=
      (hψcs.fderiv (𝕜 := ℝ)).convolutionExists_right (ContinuousLinearMap.precompR (Euclid m) L)
        hρ'i.locallyIntegrable (hψ.continuous_fderiv (by simp)) w
    have h1 : fderiv ℝ ψ' w = ∫ t, ρ' t • fderiv ℝ ψ (w - t) := by
      rw [hderiv w, convolution_def]
      congr 1
    rw [← hTr, h1, ← ContinuousLinearMap.integral_comp_comm Tr hint,
      ← integral_neg_eq_self
        (fun z => ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap) volume]
    congr 1
    funext t
    rw [map_smul, smul_eq_mul, hTr, ← sub_eq_add_neg]
  refine ⟨ψ', ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ'cs.contDiff_convolution_left L hρ'smooth hψ.continuous.locallyIntegrable
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp
  · exact htsupp.trans (closedBall_subset_ball (by linarith))
  · intro v
    rw [hψ'apply]
    refine (norm_integral_le_of_norm_le hρ'i (ae_of_all _ fun t => ?_)).trans hρ'1.le
    rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hψ1 _)
  · -- Fubini
    set u : Euclid m → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
    set G : Euclid m → ℝ :=
      fun v => LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap with hG
    have hGeq : G = Tr ∘ fderiv ℝ ψ := by
      funext v
      simp only [G, Function.comp_apply, hTr]
    have hGc : Continuous G := by
      rw [hGeq]; exact Tr.continuous.comp (hψ.continuous_fderiv (by simp))
    have hGcs : HasCompactSupport G := by
      rw [hGeq]; exact (hψcs.fderiv (𝕜 := ℝ)).comp_left (map_zero Tr)
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
    have hum : Measurable u := measurable_const.indicator hF
    have hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := fun x => by
      by_cases hx : x ∈ F <;> simp [u, hx]
    set g : Euclid m × Euclid m → ℝ := fun p => ρ p.2 * u (p.1 - p.2) * G p.1 with hg
    have hgm : Measurable g :=
      ((hρc.measurable.comp measurable_snd).mul
        (hum.comp (measurable_fst.sub measurable_snd))).mul (hGc.measurable.comp measurable_fst)
    have hgi : Integrable g (volume.prod volume) := by
      refine Integrable.mono' (hGi.norm.mul_prod hρi) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      have h1 := hu01 (p.1 - p.2)
      have h2 := hρ0 p.2
      simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1.1]
      nlinarith [mul_nonneg (mul_nonneg h2 (abs_nonneg (G p.1))) (sub_nonneg.mpr h1.2)]
    have hT : MeasurePreserving (fun p : Euclid m × Euclid m => (p.1 + p.2, p.2))
        (volume.prod volume) (volume.prod volume) := measurePreserving_add_prod volume volume
    have hgTi : Integrable (fun p : Euclid m × Euclid m => g (p.1 + p.2, p.2))
        (volume.prod volume) :=
      (hT.integrable_comp hgm.aestronglyMeasurable).mpr hgi
    have hgT : ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) =
        ∫ p, g p ∂(volume.prod volume) := by
      have := integral_map (μ := volume.prod volume) hT.measurable.aemeasurable
        (f := g) (by rw [hT.map_eq]; exact hgm.aestronglyMeasurable)
      rw [hT.map_eq] at this
      exact this.symm
    have hLHS : ∫ v, (∫ z, ρ z * u (v - z)) * G v = ∫ p, g p ∂(volume.prod volume) := by
      rw [integral_prod g hgi]
      congr 1
      funext v
      rw [← integral_mul_const]
    have hRHS : ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
        ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hgTi, ← integral_indicator hF]
      congr 1
      funext w
      have h1 : ∀ z, g (w + z, z) = u w * (ρ z * G (w + z)) := fun z => by
        simp only [g, add_sub_cancel_right]
        ring
      dsimp only
      simp only [h1]
      rw [integral_const_mul, ← hG' w]
      by_cases hw : w ∈ F <;> simp [u, hw]
    exact hLHS.trans (hgT.symm.trans hRHS.symm)

/-- Gradient bound for a mollified indicator (Simon Ch. 2, 2.5; step 3 of the perimeter
compactness used for the zero-scale limit planes of 7.5).  Let `ρ ≥ 0` be `C^∞` with `∫ ρ = 1` and
`ρ = 0` off `B̄_ε(0)`, and let `∫_F div φ ≤ c` for every `C^∞` field `φ` with compact support in
`B_{r+ε}(0)` and `|φ| ≤ 1`.  Then `f = ρ ⋆ 1_F` is `C^∞` and `∫_{B_r(0)} |Df| ≤ c`.  As `ρ` has
compact support and `1_F` is locally integrable, `f` is `C^∞`
(`HasCompactSupport.contDiff_convolution_left`).  For a test field `ψ` in `B_r(0)` with
`|ψ| ≤ 1`, `codim1_zsl_pc_mollify_test_field` gives a test field `ψ'` in `B_{r+ε}(0)` with
`|ψ'| ≤ 1` and `∫ f div ψ = ∫_F div ψ' ≤ c`, and `codim1_zsl_pc_smooth_grad_bound` turns these
bounds into `∫_{B_r(0)} |Df| ≤ c`. -/
theorem Submission.codim1_zsl_pc_mollify_grad_bound : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (r ε c : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (r + ε) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) ∧ ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) v‖ₑ ≤ ENNReal.ofReal c := by
  intro m F ρ r ε c hF hρ hρ0 hρs hρ1 hP
  -- `f = ρ ⋆ 1_F` is `C^∞`: `ρ` is `C^∞` with support in `B̄_ε(0)`, `1_F` is locally integrable
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε) fun z hz => hρs z ?_
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  have hli : LocallyIntegrable (F.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hconv : (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z))
      = convolution ρ (F.indicator (fun _ => (1 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext v
    simp [convolution_def, smul_eq_mul]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) := by
    rw [hconv]
    exact hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hli
  refine ⟨hsmooth, Submission.codim1_zsl_pc_smooth_grad_bound m _ r c hsmooth ?_⟩
  -- a test field `ψ` in `B_r(0)` against `f` is a test field `ψ'` in `B_{r+ε}(0)` against `1_F`
  intro ψ hψ hψc hψs hψ1
  obtain ⟨ψ', hψ', hψ'c, hψ's, hψ'1, heq⟩ :=
    Submission.codim1_zsl_pc_mollify_test_field m F ρ ψ r ε hF hρ hρ0 hρs hρ1 hψ hψc hψs hψ1
  rw [heq]
  exact hP ψ' hψ' hψ'c hψ's hψ'1

/-- Translation estimate for sets of locally finite perimeter: if `∫_F div φ ≤ c` for all smooth
fields `φ` with `|φ| ≤ 1` and compact support in `B_{R+2}(0)`, then
`L^m(((F − h) Δ F) ∩ B_R(0)) ≤ c|h|` for `|h| ≤ 1`.  The left side is
`∫_{B_R}|1_F(v + h) − 1_F(v)| dv`, and `c ≥ 0` (test with `φ = 0`).  Given `η > 0`,
`codim1_zsl_pc_mollify_indicator_l1` gives a radius `δ`; a normalized bump `ρ` of radius
`s = min(δ, 1/2)` mollifies `1_F` to a smooth `f` with `∫_{B_{R+1}}‖Df‖ ≤ c`
(`codim1_zsl_pc_mollify_grad_bound`, since `B_{R+1+s} ⊆ B_{R+2}`) and `∫_{B_{R+1}}|f − 1_F| ≤ η`.
By `codim1_zsl_pc_smooth_translate_l1`, `∫_{B_R}|f(v + h) − f(v)| ≤ c|h|`; the triangle inequality
and translation invariance of `L^m` bound the left side by `c|h| + 2η`. -/
theorem Submission.codim1_zsl_pc_translation_estimate : ∀ (m : ℕ) (F : Set (Euclid m)) (R c : ℝ), MeasurableSet F → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (R + 2) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (c * ‖h‖) := by
  intro m F R c hF hc h hh
  -- `0 ≤ c`, by testing the hypothesis with `φ = 0`.
  have hc0 : 0 ≤ c := by
    have h0 := hc (fun _ => (0 : Euclid m)) contDiff_const HasCompactSupport.zero
      (by simp [tsupport]) (by simp)
    simpa using h0
  -- The measure of the symmetric difference as an `L¹` norm of indicators.
  have hχm : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hS : MeasurableSet (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
    (measurable_add_const h hF).symmDiff hF
  have hL : volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R)
      = ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
    rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
    refine lintegral_congr (fun v => ?_)
    by_cases h1 : v + h ∈ F <;> by_cases h2 : v ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  rw [hL]
  -- An `ε` of room: it suffices to prove the bound up to `ε = η + η`.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η + η = (ε : ℝ) :=
    ⟨(ε : ℝ) / 2, half_pos (by exact_mod_cast hε), add_halves _⟩
  -- The `L¹`-approximation radius `δ` on `B_{R+1}`, and the mollifier radius `s ≤ min(δ, 1/2)`.
  obtain ⟨δ, hδ, hmoll⟩ := Submission.codim1_zsl_pc_mollify_indicator_l1 m F (R + 1) η hF hη
  obtain ⟨s, hs, hsδ, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ s ≤ 1 / 2 :=
    ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_left _ _, min_le_right _ _⟩
  -- A smooth mollifier supported in `closedBall 0 s`: a normalized bump function.
  obtain ⟨ρ, hρ_smooth, hρ_nn, hρ_supp, hρ_int⟩ : ∃ ρ : Euclid m → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z, 0 ≤ ρ z) ∧ (∀ z, s < ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 := by
    obtain ⟨b, hb_out⟩ : ∃ b : ContDiffBump (0 : Euclid m), b.rOut = s :=
      ⟨⟨s / 2, s, half_pos hs, half_lt_self hs⟩, rfl⟩
    have hbi : Integrable b := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    have hbpos : 0 < ∫ x, b x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => b.nonneg' x) hbi, b.support_eq, hb_out]
      exact measure_ball_pos volume 0 hs
    refine ⟨fun x => (∫ y, b y)⁻¹ * b x, contDiff_const.mul b.contDiff,
      fun z => mul_nonneg (inv_nonneg.mpr hbpos.le) (b.nonneg' z), fun z hz => ?_, ?_⟩
    · have hz0 : b z = 0 := b.zero_of_le_dist (by rw [dist_zero_right, hb_out]; exact hz.le)
      simp [hz0]
    · show ∫ z, (∫ y, b y)⁻¹ * b z = 1
      rw [integral_const_mul]
      exact inv_mul_cancel₀ hbpos.ne'
  have hρ_supp' : ∀ z, δ < ‖z‖ → ρ z = 0 := fun z hz => hρ_supp z (lt_of_le_of_lt hsδ hz)
  -- The mollified indicator `f`: smooth, `∫_{B_{R+1}} ‖Df‖ ≤ c`, and `L¹`-close to `1_F`.
  obtain ⟨f, hf_smooth, hf_grad, hE⟩ : ∃ f : Euclid m → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∫⁻ v in ball (0 : Euclid m) (R + 1), ‖fderiv ℝ f v‖ₑ ≤ ENNReal.ofReal c ∧
      ∫⁻ v in ball (0 : Euclid m) (R + 1), ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
        ≤ ENNReal.ofReal η := by
    obtain ⟨h1, h2⟩ := Submission.codim1_zsl_pc_mollify_grad_bound m F ρ (R + 1) s c hF
      hρ_smooth hρ_nn hρ_supp hρ_int (fun φ hφ1 hφ2 hφ3 hφ4 =>
        hc φ hφ1 hφ2 (hφ3.trans (ball_subset_ball (by linarith))) hφ4)
    exact ⟨_, h1, h2, hmoll ρ hρ_smooth.continuous hρ_nn hρ_supp' hρ_int⟩
  have hfm : Measurable f := hf_smooth.continuous.measurable
  -- The translation estimate for the smooth function `f`.
  have htr := Submission.codim1_zsl_pc_smooth_translate_l1 m f h R
    (hf_smooth.of_le (by exact_mod_cast le_top))
  have hT : ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ ≤ ENNReal.ofReal (c * ‖h‖) := by
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ
        ≤ ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := htr
      _ ≤ ‖h‖ₑ * ENNReal.ofReal c := by
        gcongr
        exact (lintegral_mono_set (ball_subset_ball (by linarith))).trans hf_grad
      _ = ENNReal.ofReal (c * ‖h‖) := by
        rw [ENNReal.ofReal_mul hc0, ofReal_norm, mul_comm]
  -- The two `L¹` error terms, at `v + h` and at `v`.
  have hsub : ball (0 : Euclid m) R ⊆ (fun x => x + h) ⁻¹' ball (0 : Euclid m) (R + 1) := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    show v + h ∈ ball (0 : Euclid m) (R + 1)
    rw [mem_ball_zero_iff]
    calc ‖v + h‖ ≤ ‖v‖ + ‖h‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  have h9b : ∫⁻ v in ball (0 : Euclid m) R,
      ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤ ENNReal.ofReal η := by
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        ≤ ∫⁻ v in (fun x => x + h) ⁻¹' ball (0 : Euclid m) (R + 1),
            ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ w in ball (0 : Euclid m) (R + 1), ‖f w - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
          (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
            (measurableEmbedding_addRight h)
            (fun w => ‖f w - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) _
      _ ≤ ENNReal.ofReal η := hE
  have h9a : ∫⁻ v in ball (0 : Euclid m) R, ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
      ≤ ENNReal.ofReal η :=
    (lintegral_mono_set (ball_subset_ball (by linarith))).trans hE
  -- Pointwise triangle inequality.
  have hpt : ∀ v, ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤
      ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ + ‖f (v + h) - f v‖ₑ
        + ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
    intro v
    have e : F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v
        = -(f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)) + (f (v + h) - f v)
          + (f v - F.indicator (fun _ => (1 : ℝ)) v) := by ring
    rw [e, ← enorm_neg (f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h))]
    exact enorm_add₃_le
  have hg3m : Measurable (fun v => ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ) :=
    (hfm.sub hχm).enorm
  have hg2m : Measurable (fun v => ‖f (v + h) - f v‖ₑ) :=
    ((hfm.comp (measurable_add_const h)).sub hfm).enorm
  -- Conclusion: the left side is at most `η + c|h| + η`.
  calc ∫⁻ v in ball (0 : Euclid m) R,
        ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R,
          (‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ + ‖f (v + h) - f v‖ₑ
            + ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ)
          + (∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ)
          + ∫⁻ v in ball (0 : Euclid m) R, ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
        rw [lintegral_add_right _ hg3m, lintegral_add_right _ hg2m]
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (c * ‖h‖) + ENNReal.ofReal η :=
        add_le_add (add_le_add h9b hT) h9a
    _ = ENNReal.ofReal (c * ‖h‖) + (ENNReal.ofReal η + ENNReal.ofReal η) := by ring
    _ = ENNReal.ofReal (c * ‖h‖) + ε := by
        rw [← ENNReal.ofReal_add hη.le hη.le, hηε, ENNReal.ofReal_coe_nnreal]
/-- **Cube averages under a translation estimate** (Kolmogorov–Riesz averaging step): if
`Lᵐ(((F − h) Δ F) ∩ B_R(0)) ≤ C|h|` for `|h| ≤ 1`, then `1_F` is `KCδ`-close in `L¹(B_R(0))` to its
averages over the grid cubes `Q_δ(v)` of side `δ`, `δ√m ≤ 1`.  `Q_δ(v)` is a box of volume `δᵐ`
inside `B̄_{√m δ}(v)`, so `|1_F(v) − a(v)| ≤ δ⁻ᵐ ∫_{|h| ≤ √m δ} |1_F(v) − 1_F(v + h)| dh`; Tonelli
over `v ∈ B_R(0)` and `Lᵐ(B̄_{√m δ}(0)) = (√m δ)ᵐ Lᵐ(B₁(0))` give `K = (√m)^{m+1} Lᵐ(B₁(0))`. -/
theorem Submission.codim1_zsl_pc_cube_average_bound : ∀ (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set (Euclid m)) (R C δ : ℝ), MeasurableSet F → 0 ≤ C → 0 < δ → δ * Real.sqrt m ≤ 1 → (∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ ≤ ENNReal.ofReal (K * C * δ) := by
  intro m
  refine ⟨Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal, by positivity, ?_⟩
  intro F R C δ hF hC hδ hδm hsd
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hs0 : 0 ≤ Real.sqrt m * δ := by positivity
  have hs1 : Real.sqrt m * δ ≤ 1 := by rw [mul_comm]; exact hδm
  have hδm0 : 0 < δ ^ m := pow_pos hδ m
  -- Step 1: the cube `Q v` is (the preimage of) a half-open box of side `δ`
  have hQbox : ∀ v : Euclid m, {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} =
      (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) := by
    intro v
    ext w
    simp only [Set.mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico]
    refine forall_congr' fun j => ?_
    rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
  have hbox_meas : ∀ v : Euclid m,
      MeasurableSet (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) :=
    fun v => MeasurableSet.univ_pi fun j => measurableSet_Ico
  have hQvol : ∀ v : Euclid m,
      volume {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} = ENNReal.ofReal (δ ^ m) := by
    intro v
    rw [hQbox v, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (hbox_meas v).nullMeasurableSet, Real.volume_pi_Ico]
    have : ∀ j : Fin m, ((⌊v j / δ⌋ : ℝ) + 1) * δ - (⌊v j / δ⌋ : ℝ) * δ = δ := fun j => by ring
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hδ.le]
  -- Step 2: the cube lies in the closed ball of radius `√m δ` about `v`
  have hQball : ∀ v : Euclid m,
      {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} ⊆ closedBall v (Real.sqrt m * δ) := by
    intro v w hw
    rw [hQbox v] at hw
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico] at hw
    rw [mem_closedBall, EuclideanSpace.dist_eq]
    have hcoord : ∀ j, dist (w j) (v j) ^ 2 ≤ δ ^ 2 := by
      intro j
      have hwj := hw j
      have h1 := Int.floor_le (v j / δ)
      have h2 := Int.lt_floor_add_one (v j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      have hab : |w j - v j| ≤ δ := by
        rw [abs_le]; constructor <;> nlinarith [hwj.1, hwj.2]
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc Real.sqrt (∑ j, dist (w j) (v j) ^ 2) ≤ Real.sqrt (∑ _j : Fin m, δ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
      _ = Real.sqrt m * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hδ.le]
  -- Step 3: pointwise bound by an average of differences over the closed ball
  have hpt : ∀ (v : Euclid m) (Q : Set (Euclid m)), volume Q = ENNReal.ofReal (δ ^ m) →
      Q ⊆ closedBall v (Real.sqrt m * δ) →
      ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
    intro v Q hQv hQb
    have hQfin : volume Q ≠ ∞ := by rw [hQv]; exact ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict Q) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hQfin.lt_top⟩
    have hint_c : Integrable (fun _ : Euclid m => F.indicator (fun _ => (1 : ℝ)) v)
        (volume.restrict Q) := integrable_const _
    have hint_u : Integrable (F.indicator (fun _ => (1 : ℝ))) (volume.restrict Q) :=
      (integrable_const (1 : ℝ)).indicator hF
    have h1 : ∫ w in Q, F.indicator (fun _ => (1 : ℝ)) w = (volume (F ∩ Q)).toReal := by
      rw [integral_indicator_const (1 : ℝ) hF, smul_eq_mul, mul_one,
        measureReal_restrict_apply hF, measureReal_def]
    have h2 : F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m =
        (δ ^ m)⁻¹ * ∫ w in Q, (F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w) := by
      rw [integral_sub hint_c hint_u, setIntegral_const, h1, measureReal_def, hQv,
        ENNReal.toReal_ofReal hδm0.le, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hδm0.ne', one_mul, div_eq_inv_mul]
    have h3 : ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ := by
      rw [h2, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hδm0.le)]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    have h4 : ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ ≤
        ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
      calc ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ
          ≤ ∫⁻ w in closedBall v (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
            lintegral_mono_set hQb
        _ = ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
          rw [← lintegral_indicator measurableSet_closedBall,
            ← lintegral_indicator measurableSet_closedBall,
            ← lintegral_add_left_eq_self ((closedBall v (Real.sqrt m * δ)).indicator fun w =>
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) v]
          refine lintegral_congr fun h => ?_
          have hmem : v + h ∈ closedBall v (Real.sqrt m * δ) ↔
              h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ) := by
            rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
              sub_zero]
          by_cases hh : h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ)
          · rw [indicator_of_mem (hmem.2 hh), indicator_of_mem hh]
          · rw [indicator_of_notMem (mt hmem.1 hh), indicator_of_notMem hh]
    exact h3.trans (mul_le_mul' le_rfl h4)
  -- Step 4: integrate, swap the order of integration, and use the hypothesis
  have hind : ∀ v h : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ =
        (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v := by
    intro v h
    by_cases h1 : v ∈ F <;> by_cases h2 : v + h ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  have hinner : ∀ h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ),
      ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤
        ENNReal.ofReal (C * (Real.sqrt m * δ)) := by
    intro h hh
    have hh' : ‖h‖ ≤ Real.sqrt m * δ := mem_closedBall_zero_iff.1 hh
    calc ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        = ∫⁻ v in ball (0 : Euclid m) R, (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v :=
          lintegral_congr fun v => hind v h
      _ ≤ (volume.restrict (ball (0 : Euclid m) R)) (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
          lintegral_indicator_one_le _
      _ = volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) :=
          Measure.restrict_apply' measurableSet_ball
      _ ≤ ENNReal.ofReal (C * ‖h‖) := hsd h (hh'.trans hs1)
      _ ≤ ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh' hC)
  have hmeas2 : Measurable (uncurry fun (v h : Euclid m) =>
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m =>
        F.indicator (fun _ => (1 : ℝ)) p.1 - F.indicator (fun _ => (1 : ℝ)) (p.1 + p.2) :=
      (hu_meas.comp measurable_fst).sub (hu_meas.comp (measurable_fst.add measurable_snd))
    exact this.enorm
  have hV1fin : volume (ball (0 : Euclid m) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v -
        (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_mono fun v => hpt v _ (hQvol v) (hQball v)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ∫⁻ v in ball (0 : Euclid m) R,
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
        rw [lintegral_lintegral_swap (μ := volume.restrict (ball (0 : Euclid m) R))
          (ν := volume.restrict (closedBall (0 : Euclid m) (Real.sqrt m * δ)))
          hmeas2.aemeasurable]
    _ ≤ ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
        mul_le_mul' le_rfl (setLIntegral_mono measurable_const hinner)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * (ENNReal.ofReal (C * (Real.sqrt m * δ)) *
          (ENNReal.ofReal ((Real.sqrt m * δ) ^ m) * volume (ball (0 : Euclid m) 1))) := by
        rw [setLIntegral_const, Measure.addHaar_closedBall _ _ hs0, finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ) := by
        have e1 : Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ =
            ((δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m) *
              (volume (ball (0 : Euclid m) 1)).toReal := by
          rw [mul_pow]
          field_simp
          ring
        rw [e1, ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m)
            (by positivity), ENNReal.ofReal_toReal hV1fin,
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ))) (by positivity),
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹) (by positivity)]
        ring
/-- Common convergent subsequence for countably many bounded real sequences.  The points
`xᵢ = (b_k(i))_k` lie in the product `Π_k [-M_k, M_k]`, which is compact (Tychonoff,
`isCompact_univ_pi`); `ℝ^ι` is first countable since `ι` is countable, so `IsCompact.tendsto_subseq`
gives a strictly increasing `σ` and a limit `a` with `x_{σ(i)} → a`.  Evaluation at `k` is
continuous, hence `b_k(σ(i)) → a(k)` for every `k`. -/
theorem Submission.codim1_zsl_pc_diagonal_subseq : ∀ (ι : Type) [Countable ι] (b : ι → ℕ → ℝ) (M : ι → ℝ), (∀ k i, |b k i| ≤ M k) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ k, ∃ L : ℝ, Tendsto (fun i => b k (σ i)) atTop (𝓝 L) := by
  intro ι _ b M hb
  have hS : IsCompact (Set.pi univ (fun k => Icc (-M k) (M k))) :=
    isCompact_univ_pi (fun k => isCompact_Icc)
  have hx : ∀ i, (fun k => b k i) ∈ Set.pi univ (fun k => Icc (-M k) (M k)) := by
    intro i
    rw [Set.mem_univ_pi]
    intro k
    exact Set.mem_Icc.mpr (abs_le.mp (hb k i))
  obtain ⟨a, -, σ, hσ, hlim⟩ := hS.tendsto_subseq hx
  exact ⟨σ, hσ, fun k => ⟨a k, ((continuous_apply k).tendsto a).comp hlim⟩⟩
/-- Sets that are Cauchy in measure on every ball have a subsequence converging in measure on
every ball to a measurable set.  With `N_l` chosen for `R = l + 1`, `η = 2⁻ˡ`, the subsequence
`σ(l) = l + Σ_{k ≤ l} N_k` makes `E_l = (F_{σ(l+1)} Δ F_{σ(l)}) ∩ B_{l+1}(0)` summable in measure,
so by Borel–Cantelli (`ae_eventually_notMem`) a.e. `v` lies in only finitely many `E_l`.  For such
`v`, membership in `F_{σ(l)}` is eventually constant and equals membership in the liminf
`F' = ⋃_{l₀} ⋂_{l ≥ l₀} F_{σ(l)}`.  Continuity from above (`tendsto_measure_iInter_atTop`) on the
finite-measure ball `B_R(0)`, applied to `⋃_{l ≥ l₀} (F_{σ(l)} Δ F') ∩ B_R(0)`, concludes. -/
theorem Submission.codim1_zsl_pc_cauchy_limit_set : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hF hC
  -- Fast subsequence: `N l` works for `R = l + 1`, `η = 2⁻ˡ`, and `N l ≤ σ l'` for `l ≤ l'`.
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) ((l : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ l) :=
    fun l => hC ((l : ℝ) + 1) (by positivity) ((1 / 2 : ℝ) ^ l) (by positivity)
  choose N hN using hN
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, ∀ l, σ l = l + ∑ k ∈ Finset.range (l + 1), N k :=
    ⟨_, fun _ => rfl⟩
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro l
    simp only [hσ, Finset.sum_range_succ]
    omega
  have hσge : ∀ l l', l ≤ l' → N l ≤ σ l' := by
    intro l l' h
    have h1 : N l ≤ ∑ k ∈ Finset.range (l' + 1), N k :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    rw [hσ]
    omega
  -- The limit set: the points lying in `F (σ l)` for all large `l`.
  obtain ⟨F', hF'eq⟩ : ∃ F' : Set (Euclid m), F' = ⋃ l₀ : ℕ, ⋂ l : ℕ, ⋂ (_ : l₀ ≤ l), F (σ l) :=
    ⟨_, rfl⟩
  have hF'meas : MeasurableSet F' := by
    rw [hF'eq]
    exact MeasurableSet.iUnion fun l₀ => MeasurableSet.iInter fun l =>
      MeasurableSet.iInter fun _ => hF _
  have hF'mem : ∀ v, v ∈ F' ↔ ∃ l₀, ∀ l, l₀ ≤ l → v ∈ F (σ l) := by
    intro v
    rw [hF'eq]
    simp only [mem_iUnion, mem_iInter]
  -- The transition sets `E l` have summable measures.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set (Euclid m), ∀ l,
      E l = symmDiff (F (σ (l + 1))) (F (σ l)) ∩ ball (0 : Euclid m) ((l : ℝ) + 1) :=
    ⟨_, fun _ => rfl⟩
  have hEle : ∀ l, volume (E l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := by
    intro l
    rw [hE]
    exact hN l _ _ (hσge l (l + 1) (Nat.le_succ l)) (hσge l l le_rfl)
  have hsum : ∑' l, volume (E l) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  -- Borel–Cantelli: a.e. `v` is eventually outside `F (σ l) Δ F'`.
  have hae : ∀ᵐ v ∂(volume : Measure (Euclid m)),
      ∀ᶠ l in atTop, v ∉ symmDiff (F (σ l)) F' := by
    filter_upwards [ae_eventually_notMem hsum] with v hv
    have hball : ∀ᶠ l : ℕ in atTop, v ∈ ball (0 : Euclid m) ((l : ℝ) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt ‖v‖
      filter_upwards [eventually_ge_atTop n] with l hl
      rw [mem_ball_zero_iff]
      have : (n : ℝ) ≤ l := Nat.cast_le.mpr hl
      linarith
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp (hv.and hball)
    have hstep : ∀ l, l₁ ≤ l → (v ∈ F (σ (l + 1)) ↔ v ∈ F (σ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hl₁ l hl
      rw [hE] at h1
      have h3 : v ∉ symmDiff (F (σ (l + 1))) (F (σ l)) := fun h => h1 (Set.mem_inter h h2)
      rw [Set.mem_symmDiff] at h3
      tauto
    have hconst : ∀ l, l₁ ≤ l → (v ∈ F (σ l) ↔ v ∈ F (σ l₁)) := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact Iff.rfl
      | succ l hl ih => exact (hstep l hl).trans ih
    have hF'iff : v ∈ F' ↔ v ∈ F (σ l₁) := by
      rw [hF'mem]
      constructor
      · rintro ⟨l₀, hl₀⟩
        exact (hconst (max l₀ l₁) (le_max_right _ _)).mp (hl₀ _ (le_max_left _ _))
      · intro h
        exact ⟨l₁, fun l hl => (hconst l hl).mpr h⟩
    filter_upwards [eventually_ge_atTop l₁] with l hl
    rw [Set.mem_symmDiff]
    have := hconst l hl
    tauto
  refine ⟨σ, F', hσmono, hF'meas, fun R => ?_⟩
  -- Continuity from above for the tails `G l₀` inside the finite-measure ball `B_R(0)`.
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Euclid m), ∀ l₀,
      G l₀ = ⋃ l : ℕ, ⋃ (_ : l₀ ≤ l), symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R :=
    ⟨_, fun _ => rfl⟩
  have hGmem : ∀ l₀ v, v ∈ G l₀ ↔ ∃ l, l₀ ≤ l ∧ v ∈ symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R := by
    intro l₀ v
    rw [hG]
    simp only [mem_iUnion, exists_prop]
  have hGmeas : ∀ l₀, NullMeasurableSet (G l₀) volume := by
    intro l₀
    rw [hG]
    exact (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
      ((hF _).symmDiff hF'meas).inter measurableSet_ball).nullMeasurableSet
  have hGanti : Antitone G := by
    intro a b hab v hv
    rw [hGmem] at hv ⊢
    obtain ⟨l, hl, hv⟩ := hv
    exact ⟨l, hab.trans hl, hv⟩
  have hGfin : ∃ i, volume (G i) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclid m)) (r := R)).ne (measure_mono ?_)⟩
    intro v hv
    rw [hGmem] at hv
    obtain ⟨l, _, hv⟩ := hv
    exact hv.2
  have hGnull : volume (⋂ l₀, G l₀) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro v hv
    rw [mem_iInter] at hv
    intro hev
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp hev
    obtain ⟨l, hl, hvl⟩ := (hGmem l₁ v).mp (hv l₁)
    exact hl₁ l hl hvl.1
  have hGlim := tendsto_measure_iInter_atTop hGmeas hGanti hGfin
  rw [hGnull] at hGlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim (fun _ => zero_le) ?_
  intro l
  exact measure_mono (fun v hv => (hGmem l v).mpr ⟨l, le_rfl, hv⟩)

/-- Compactness from a uniform translation estimate: the precompactness part of Simon Ch. 2, 2.6,
proved with cube averages (Hanche-Olsen–Holden, Expo. Math. 28 (2010), Theorem 5).  The averages
`b_{(l,z)}(i) = Lᵐ(Fᵢ ∩ Q_{l,z})/δₗᵐ ∈ [0, 1]` over the grid cubes `Q_{l,z}` of side
`δₗ = 1/((l+1)(m+1))` all converge along one diagonal subsequence `σ₀`.  On `B_R`, the cube
average bound (`2KCδₗ`) and dominated convergence for the step functions make `F_{σ₀ i}` Cauchy
in measure, and `codim1_zsl_pc_cauchy_limit_set` extracts a further subsequence and the limit. -/
theorem Submission.codim1_zsl_pc_compact_of_translation : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ i in atTop, ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F i) (F i) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hFm hT
  obtain ⟨K, hK0, hK⟩ := Submission.codim1_zsl_pc_cube_average_bound m
  -- Step 1: the scales `δ l`
  obtain ⟨δ, hδpos, hδsqrt, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ l, 0 < δ l) ∧ (∀ l, δ l * Real.sqrt m ≤ 1) ∧
      Tendsto δ atTop (𝓝 0) := by
    have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hsq : Real.sqrt m ≤ (m:ℝ) + 1 := by
      have h1 : (m:ℝ) ≤ ((m:ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      calc Real.sqrt m ≤ Real.sqrt (((m:ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (m:ℝ) + 1 := Real.sqrt_sq hm1.le
    refine ⟨fun l => 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1), fun l => by positivity, fun l => ?_, ?_⟩
    · have hl1 : (0:ℝ) < (l:ℝ) + 1 := by positivity
      calc 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * Real.sqrt m
          ≤ 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * ((m:ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 1 / ((l:ℝ) + 1) := div_mul_cancel₀ _ hm1.ne'
        _ ≤ 1 := by
            rw [div_le_one hl1]
            linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const ((m:ℝ) + 1)
      rwa [zero_div] at h
  -- Step 2: grid cubes and cube averages
  set Q : ℕ → (Fin m → ℤ) → Set (Euclid m) := fun l z => {w : Euclid m | ∀ j, ⌊w j / δ l⌋ = z j}
    with hQ
  have hQvol : ∀ l (z : Fin m → ℤ), volume (Q l z) ≤ ENNReal.ofReal (δ l ^ m) := by
    intro l z
    have hQeq : Q l z = (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((z j : ℝ) * δ l) (((z j : ℝ) + 1) * δ l)) := by
      ext w
      simp only [hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Ico]
      refine forall_congr' fun j => ?_
      rw [Int.floor_eq_iff, le_div_iff₀ (hδpos l), div_lt_iff₀ (hδpos l)]
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
    have hsub : ∀ j : Fin m, ((z j : ℝ) + 1) * δ l - (z j : ℝ) * δ l = δ l := fun j => by ring
    simp only [hsub, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (hδpos l).le m).ge
  set b : ℕ × (Fin m → ℤ) → ℕ → ℝ := fun k i => (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m
    with hb
  have hb01 : ∀ k i, 0 ≤ b k i ∧ b k i ≤ 1 := by
    intro k i
    have hpos : 0 < δ k.1 ^ m := pow_pos (hδpos k.1) m
    show 0 ≤ (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ∧
      (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ≤ 1
    refine ⟨div_nonneg ENNReal.toReal_nonneg hpos.le, ?_⟩
    rw [div_le_one hpos]
    exact ENNReal.toReal_le_of_le_ofReal hpos.le
      ((measure_mono inter_subset_right).trans (hQvol k.1 k.2))
  -- Step 3: diagonal subsequence
  obtain ⟨σ₀, hσ₀, hL⟩ := Submission.codim1_zsl_pc_diagonal_subseq (ℕ × (Fin m → ℤ)) b
    (fun _ => 1) (fun k i => (abs_le.2 ⟨by linarith [(hb01 k i).1], (hb01 k i).2⟩ : |b k i| ≤ 1))
  choose L hL using hL
  have hL01 : ∀ k, 0 ≤ L k ∧ L k ≤ 1 := fun k =>
    ⟨ge_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).1),
      le_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).2)⟩
  -- measurability of the floor map and of coordinates
  have hfloor : Measurable (Int.floor : ℝ → ℤ) :=
    measurable_to_countable' fun n => by
      rw [Int.preimage_floor_singleton]
      exact measurableSet_Ico
  have hcoord : ∀ j : Fin m, Measurable (fun v : Euclid m => v j) := fun j =>
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin m → ℝ))
  -- Step 4: the subsequence is Cauchy in `L¹_loc`
  have hCauchy : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η := by
    intro R hR η hη
    obtain ⟨C, hC⟩ := hT R hR
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hC
    have hC'0 : (0:ℝ) ≤ max C 0 := le_max_right _ _
    have htrans : ∀ i, i₀ ≤ i → ∀ h : Euclid m, ‖h‖ ≤ 1 →
        volume (symmDiff ((fun v => v + h) ⁻¹' F (σ₀ i)) (F (σ₀ i)) ∩ ball (0 : Euclid m) R) ≤
          ENNReal.ofReal (max C 0 * ‖h‖) := by
      intro i hi h hh
      exact (hi₀ (σ₀ i) (le_trans hi (hσ₀.id_le i)) h hh).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    have hKC : 0 ≤ K * max C 0 := mul_nonneg hK0 hC'0
    have hlim0 : Tendsto (fun l => K * max C 0 * δ l) atTop (𝓝 0) := by
      have h := hδlim.const_mul (K * max C 0)
      rwa [mul_zero] at h
    obtain ⟨l, hl⟩ := (hlim0.eventually (gt_mem_nhds (show (0:ℝ) < η / 4 by positivity))).exists
    have hKCδ : 0 ≤ K * max C 0 * δ l := mul_nonneg hKC (hδpos l).le
    set kf : Euclid m → (Fin m → ℤ) := fun v j => ⌊v j / δ l⌋ with hkf
    have hkf_meas : Measurable kf := by
      rw [measurable_pi_iff]
      intro j
      exact hfloor.comp ((hcoord j).div_const (δ l))
    have hmeasA : ∀ i, Measurable (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) := fun i =>
      (measurable_of_countable (fun z : Fin m → ℤ => ‖b (l, z) (σ₀ i) - L (l, z)‖ₑ)).comp hkf_meas
    have hmeasU : ∀ i, Measurable
        (fun v => ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ) := fun i =>
      ((measurable_const.indicator (hFm (σ₀ i))).sub
        ((measurable_of_countable (fun z : Fin m → ℤ => b (l, z) (σ₀ i))).comp hkf_meas)).enorm
    have hDCT : Tendsto (fun i => ∫⁻ v in ball (0 : Euclid m) R,
        ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
      have hbound : ∀ i, (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
          ≤ᵐ[volume.restrict (ball (0 : Euclid m) R)] (fun _ => (1 : ℝ≥0∞)) := by
        intro i
        refine ae_of_all _ (fun v => ?_)
        have h1 := hb01 (l, kf v) (σ₀ i)
        have h2 := hL01 (l, kf v)
        show ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤ 1
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2
          (abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩)
      have hfin : ∫⁻ _, (1 : ℝ≥0∞) ∂(volume.restrict (ball (0 : Euclid m) R)) ≠ ∞ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
        exact measure_ball_lt_top.ne
      have hlim : ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid m) R)),
          Tendsto (fun i => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
        refine ae_of_all _ (fun v => ?_)
        have h := ((hL (l, kf v)).sub_const (L (l, kf v))).enorm
        rwa [sub_self, enorm_zero] at h
      have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hmeasA hbound
        hfin hlim
      rwa [lintegral_zero] at h
    obtain ⟨i₁, hi₁⟩ := ENNReal.tendsto_atTop_zero.1 hDCT (ENNReal.ofReal (η / 8))
      (ENNReal.ofReal_pos.2 (by positivity))
    refine ⟨max i₀ i₁, fun i j hi hj => ?_⟩
    have hi0 : i₀ ≤ i := le_trans (le_max_left _ _) hi
    have hj0 : i₀ ≤ j := le_trans (le_max_left _ _) hj
    have hi1 : i₁ ≤ i := le_trans (le_max_right _ _) hi
    have hj1 : i₁ ≤ j := le_trans (le_max_right _ _) hj
    have cube_i : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ i)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans i hi0)
    have cube_j : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ j)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans j hj0)
    have dct_i : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ i hi1
    have dct_j : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ j hj1
    have tri : ∀ a b c d e : ℝ, ‖a - e‖ₑ ≤ ‖a - b‖ₑ + ‖b - c‖ₑ + ‖d - c‖ₑ + ‖e - d‖ₑ := by
      intro a b c d e
      have h1 : a - e = (a - b) + (b - c) - (d - c) - (e - d) := by ring
      rw [h1]
      exact enorm_sub_le.trans (add_le_add (enorm_sub_le.trans (add_le_add (enorm_add_le _ _)
        le_rfl)) le_rfl)
    have hS : MeasurableSet (symmDiff (F (σ₀ i)) (F (σ₀ j))) := (hFm _).symmDiff (hFm _)
    have hpt : ∀ v, (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v ≤
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
          + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
          + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ := by
      intro v
      refine le_trans ?_ (tri _ _ _ _ _)
      by_cases h1 : v ∈ F (σ₀ i) <;> by_cases h2 : v ∈ F (σ₀ j) <;>
        simp [Set.mem_symmDiff, h1, h2]
    calc volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R)
        = ∫⁻ v in ball (0 : Euclid m) R,
            (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v := by
          rw [lintegral_indicator_one hS, Measure.restrict_apply hS]
      _ ≤ ∫⁻ v in ball (0 : Euclid m) R,
            (‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
              + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
              + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) :=
          lintegral_mono hpt
      _ = (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) := by
          rw [lintegral_add_right _ (hmeasU j), lintegral_add_right _ (hmeasA j),
            lintegral_add_right _ (hmeasA i)]
      _ ≤ ENNReal.ofReal (K * max C 0 * δ l) + ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8)
            + ENNReal.ofReal (K * max C 0 * δ l) :=
          add_le_add (add_le_add (add_le_add cube_i dct_i) dct_j) cube_j
      _ ≤ ENNReal.ofReal η := by
          have e2 : (0:ℝ) ≤ η / 8 := by positivity
          rw [← ENNReal.ofReal_add hKCδ e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8) e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8 + η / 8) hKCδ]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Step 5: extract a convergent subsequence
  obtain ⟨σ₁, F', hσ₁, hF', hlim⟩ :=
    Submission.codim1_zsl_pc_cauchy_limit_set m (fun i => F (σ₀ i)) (fun i => hFm _) hCauchy
  exact ⟨σ₀ ∘ σ₁, F', hσ₀.comp hσ₁, hF', hlim⟩
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
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
/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]

/-- Steps 1–3 of the oriented graph chart of an oriented `(n+1)`-submanifold `N` at a point (proof
of Simon 7.5.3–7.5.5; orientations as in Ch. 6, 2.1–2.2): orthonormal coordinates adapted to a unit
orientation `ξ` of a plane `Q ⊆ ℝ^{n+1+k}`.  The orthonormal frame of `ξ` gives `dim Q = n + 1`;
orthonormal coordinates `ι₀`, `ι'` adapted to `Q` have `range ι₀ = Q`; `ζ₀ = ι₀e₀ ∧ ⋯ ∧ ι₀eₙ` is a
unit orientation of `Q`, so `ξ = ±ζ₀`; if `ξ = -ζ₀`, then `ι := ι₀ ∘ ρ`, `ρ` the reflection with
`ρ e₀ = -e₀` and `ρ eⱼ = eⱼ` for `j ≠ 0`, has `α(ιe₀, …, ιeₙ) = -α(ι₀e₀, …, ι₀eₙ)`. -/
theorem Submission.codim1_zsl_gc_oriented_frame : ∀ (n k : ℕ) (Q : Submodule ℝ (Euclid (n + 1 + k))) (ξ : MultiVector (n + 1 + k) (n + 1)), IsUnitOrientationOf ξ Q → ∃ (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) ∧ Set.range ι = (Q : Set (Euclid (n + 1 + k))) ∧ ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξ α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ))) := by
  intro n k Q ξ hξ
  -- `dim Q = n + 1`: the orthonormal frame `τ` of `ξ` spans `Q`
  have hfin : Module.finrank ℝ Q = n + 1 := by
    obtain ⟨τ, hτ, hspan, -⟩ := hξ
    rw [← hspan, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- orthonormal coordinates `ι₀`, `ι'` adapted to `Q`
  obtain ⟨ι₀, ι', h_orth, h_mem, h_span, h_proj⟩ :=
    Submission.dorag_lip_orthonormal_coordinates (n + 1) k Q hfin
  -- `range ι₀ = Q`: for `q = ι₀ v + ι' w ∈ Q`, `q = p_Q q = ι₀ v`
  have h_range : Set.range ι₀ = (Q : Set (Euclid (n + 1 + k))) := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact h_mem v
    · intro hq
      obtain ⟨v, w, rfl⟩ := h_span q
      refine ⟨v, ?_⟩
      have h1 := h_proj v w
      rw [Submodule.starProjection_eq_self_iff.mpr hq] at h1
      exact h1.symm
  -- `τ₀ = (ι₀e₀, …, ι₀eₙ)` is an orthonormal frame spanning `Q`
  have h_on : Orthonormal ℝ (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ))) :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin (n + 1))).comp_linearIsometry ι₀
  have h_spanQ :
      Submodule.span ℝ (Set.range (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)))) = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact h_mem _
    · rw [finrank_span_eq_card h_on.linearIndependent, Fintype.card_fin, hfin]
  -- `ζ₀ = τ₀(0) ∧ ⋯ ∧ τ₀(n)` is a unit orientation of `Q`, so `ξ = ±ζ₀`
  let ζ₀ : MultiVector (n + 1 + k) (n + 1) :=
    ContinuousAlternatingMap.apply ℝ (Euclid (n + 1 + k)) ℝ
      (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)))
  have hζ₀ : IsUnitOrientationOf ζ₀ Q :=
    ⟨fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ)), h_on, h_spanQ,
      Or.inl fun α => rfl⟩
  rcases Submission.rsdic_unitOrientation_eq_or_eq_neg (n + 1 + k) (n + 1) ζ₀ ξ Q hζ₀ hξ with h | h
  · -- `ξ = ζ₀`: take `ι := ι₀`
    refine ⟨ι₀, ι', h_orth, h_span, h_range, fun α => ?_⟩
    rw [h]
    rfl
  · -- `ξ = -ζ₀`: take `ι := ι₀ ∘ ρ`, `ρ` the reflection in `e₀ᗮ`
    let ρ : Euclid (n + 1) ≃ₗᵢ[ℝ] Euclid (n + 1) :=
      (ℝ ∙ EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))ᗮ.reflection
    have hρρ : ∀ v, ρ (ρ v) = v := fun v => Submodule.reflection_reflection _ v
    have hρ0 : ρ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) =
        -EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) :=
      Submodule.reflection_orthogonalComplement_singleton_eq_neg _
    have hρj : ∀ j : Fin (n + 1), j ≠ 0 →
        ρ (EuclideanSpace.single j (1 : ℝ)) = EuclideanSpace.single j (1 : ℝ) := by
      intro j hj
      apply Submodule.reflection_mem_subspace_eq_self
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right, EuclideanSpace.inner_single_left]
      simp [Ne.symm hj]
    refine ⟨ι₀.comp ρ.toLinearIsometry, ι', fun v w => h_orth (ρ v) w, fun y => ?_, ?_,
      fun α => ?_⟩
    · -- `y = ι₀ v + ι' w = ι (ρ v) + ι' w`
      obtain ⟨v, w, rfl⟩ := h_span y
      exact ⟨ρ v, w, by simp [hρρ]⟩
    · -- `ρ` is onto
      rw [LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
        ρ.surjective.range_comp, h_range]
    · -- `(ιe₀, …, ιeₙ)` is `τ₀` with `τ₀(0)` replaced by `(-1) • τ₀(0)`
      have hfun : (fun j : Fin (n + 1) =>
            (ι₀.comp ρ.toLinearIsometry) (EuclideanSpace.single j (1 : ℝ))) =
          Function.update (fun j : Fin (n + 1) => ι₀ (EuclideanSpace.single j (1 : ℝ))) 0
            ((-1 : ℝ) • ι₀ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) := by
        funext j
        by_cases hj : j = 0
        · subst hj
          rw [Function.update_self, LinearIsometry.coe_comp, Function.comp_apply,
            LinearIsometryEquiv.coe_toLinearIsometry, hρ0, map_neg, neg_one_smul]
        · rw [Function.update_of_ne hj, LinearIsometry.coe_comp, Function.comp_apply,
            LinearIsometryEquiv.coe_toLinearIsometry, hρj j hj]
      rw [hfun, ContinuousAlternatingMap.map_update_smul, Function.update_eq_self, h]
      simp [ζ₀]
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

/-- A `d`-dimensional `C²` submanifold `N ⊆ ℝ^{d+k}` is, near `x ∈ N`, a `C¹` graph over its
tangent directions (Simon Ch. 2, §4, (4.1)): if `ℝ^{d+k} = ι(ℝᵈ) ⊕ ι'(ℝᵏ)` orthogonally and
`TₓN ⊆ ι(ℝᵈ)`, then `N ∩ B_s(x) ⊆ {x + ιv + ι'u(v) : v ∈ O} ⊆ N` with `u(0) = 0`, `Du(0) = 0`.
With `A = ι*`, `A' = ι'*` (so `y = ιAy + ι'A'y`) and a chart `ψ : V → W` with `ψ(z₀) = x`, the
map `Φ = A(ψ - x)` has `DΦ(z₀) = A Dψ(z₀)` injective since `Dψ(z₀)(ℝᵈ) ⊆ TₓN ⊆ ι(ℝᵈ)`; a local
inverse `χ : O → V₀` of `Φ` gives `u = A'(ψ ∘ χ - x)`, and `s` comes from the continuity of `ψ⁻¹`
at `x`. -/
theorem Submission.codim1_zsl_gc_local_graph : ∀ (d k : ℕ) (N : Set (Euclid (d + k))) (x : Euclid (d + k)) (ι : Euclid d →ₗᵢ[ℝ] Euclid (d + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (d + k)), IsEmbeddedSubmanifold 2 d N → x ∈ N → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (d + k), ∃ v w, y = ι v + ι' w) → tangentSpace N x ⊆ Set.range ι → ∃ (O : Set (Euclid d)) (u : Euclid d → Euclid k) (s : ℝ), IsOpen O ∧ (0 : Euclid d) ∈ O ∧ 0 < s ∧ ContDiffOn ℝ 1 u O ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∀ v ∈ O, x + ι v + ι' (u v) ∈ N) ∧ ∀ y ∈ N, dist y x < s → ∃ v ∈ O, y = x + ι v + ι' (u v) := by
  intro d k N x ι ι' hN hx horth hdecomp htan
  -- Step 0: left inverses of `ι`, `ι'` (the adjoints)
  obtain ⟨A, hAι, hAι'⟩ : ∃ A : Euclid (d + k) →L[ℝ] Euclid d,
      (∀ v, A (ι v) = v) ∧ (∀ w, A (ι' w) = 0) := by
    refine ⟨ContinuousLinearMap.adjoint ι.toContinuousLinearMap, fun v => ?_, fun w => ?_⟩
    · refine ext_inner_right ℝ fun v' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.inner_map_map]
    · refine ext_inner_right ℝ fun v' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        inner_zero_left, real_inner_comm]
      exact horth v' w
  obtain ⟨A', hA'ι, hA'ι'⟩ : ∃ A' : Euclid (d + k) →L[ℝ] Euclid k,
      (∀ v, A' (ι v) = 0) ∧ (∀ w, A' (ι' w) = w) := by
    refine ⟨ContinuousLinearMap.adjoint ι'.toContinuousLinearMap, fun v => ?_, fun w => ?_⟩
    · refine ext_inner_right ℝ fun w' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        inner_zero_left]
      exact horth v w'
    · refine ext_inner_right ℝ fun w' => ?_
      rw [ContinuousLinearMap.adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.inner_map_map]
  have hdec : ∀ y, y = ι (A y) + ι' (A' y) := by
    intro y
    obtain ⟨v, w, rfl⟩ := hdecomp y
    simp only [map_add, hAι, hAι', hA'ι, hA'ι', add_zero, zero_add]
  -- Step 1: a chart at `x`
  obtain ⟨V, W, ψ, hVo, hWo, hxW, hψ, hinj, himg, hprop, hfinj⟩ := hN x hx
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hx⟩
  have hψN : ψ '' V ⊆ N := by rw [himg]; exact inter_subset_right
  -- Step 2: the range of `Dψ(z₀)` lies in `range ι`
  have hrange : Set.range (fderiv ℝ ψ z₀) ⊆ Set.range ι := by
    have h := Submission.dsmc_chart_range_subset_tangentSpace (d + k) 2 d N V ψ (by norm_num)
      hVo hψ hψN z₀ hz₀V
    rw [hψz₀] at h
    exact h.trans htan
  -- Step 3: `Φ z = A (ψ z - x)` has injective derivative at `z₀`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by norm_num)
  have hψdiff : ∀ z ∈ V, DifferentiableAt ℝ ψ z := fun z hz =>
    (hψ1.differentiableOn_one z hz).differentiableAt (hVo.mem_nhds hz)
  have hΦC : ContDiffOn ℝ 1 (fun z => A (ψ z - x)) V :=
    A.contDiff.comp_contDiffOn (hψ1.sub contDiffOn_const)
  have hΦd : HasFDerivAt (fun z => A (ψ z - x)) (A.comp (fderiv ℝ ψ z₀)) z₀ :=
    A.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).hasFDerivAt.sub_const x)
  have hΦinj : Injective (fderiv ℝ (fun z => A (ψ z - x)) z₀) := by
    rw [hΦd.fderiv, injective_iff_map_eq_zero]
    intro h hh
    obtain ⟨v, hv⟩ := hrange (Set.mem_range_self h)
    rw [ContinuousLinearMap.comp_apply, ← hv, hAι] at hh
    apply hfinj z₀ hz₀V
    rw [← hv, hh, map_zero, map_zero]
  -- Step 4: local inverse `χ` of `Φ`
  obtain ⟨V₀, O, χ, hV₀o, hOo, hz₀V₀, hV₀V, hχC, hχmaps, hΦχ, hχΦ⟩ :=
    Submission.codim1_zsl_gc_local_inverse d (fun z => A (ψ z - x)) V z₀ hVo hz₀V hΦC hΦinj
  have hΦχ' : ∀ a ∈ O, A (ψ (χ a) - x) = a := hΦχ
  have hχΦ' : ∀ z ∈ V₀, A (ψ z - x) ∈ O ∧ χ (A (ψ z - x)) = z := hχΦ
  have hΦz₀ : A (ψ z₀ - x) = 0 := by rw [hψz₀, sub_self, map_zero]
  have h0O : (0 : Euclid d) ∈ O := hΦz₀ ▸ (hχΦ' z₀ hz₀V₀).1
  have hχ0 : χ 0 = z₀ := hΦz₀ ▸ (hχΦ' z₀ hz₀V₀).2
  -- Step 5: the graph identity
  have hkey : ∀ v ∈ O, ψ (χ v) = x + ι v + ι' (A' (ψ (χ v) - x)) := by
    intro v hv
    have h1 := hdec (ψ (χ v) - x)
    rw [hΦχ' v hv] at h1
    rw [add_assoc, ← h1, add_sub_cancel]
  -- Step 6: the radius `s`
  obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.mp hV₀o z₀ hz₀V₀
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hWo x hxW
  obtain ⟨δ, hδ, hδprop⟩ := Submission.dsmc_chart_inverse_continuity (d + k) d V W ψ
    hψ1.continuousOn hinj (by rw [himg]; exact inter_subset_left) hprop z₀ hz₀V ε hε
  refine ⟨O, fun v => A' (ψ (χ v) - x), min δ r, hOo, h0O, lt_min hδ hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact A'.contDiff.comp_contDiffOn
      ((hψ1.comp hχC (hχmaps.mono_right hV₀V)).sub contDiffOn_const)
  · show A' (ψ (χ 0) - x) = 0
    rw [hχ0, hψz₀, sub_self, map_zero]
  · have hχd : HasFDerivAt χ (fderiv ℝ χ 0) 0 :=
      ((hχC.differentiableOn_one 0 h0O).differentiableAt (hOo.mem_nhds h0O)).hasFDerivAt
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ (χ 0)) (χ 0) :=
      (hψdiff (χ 0) (hχ0 ▸ hz₀V)).hasFDerivAt
    have hud : HasFDerivAt (fun v => A' (ψ (χ v) - x))
        (A'.comp ((fderiv ℝ ψ (χ 0)).comp (fderiv ℝ χ 0))) 0 :=
      A'.hasFDerivAt.comp 0 ((hψd.comp 0 hχd).sub_const x)
    rw [hud.fderiv]
    ext1 h
    obtain ⟨v, hv⟩ := hrange (Set.mem_range_self (fderiv ℝ χ 0 h))
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hχ0, ← hv, hA'ι,
      zero_apply]
  · intro v hv
    show x + ι v + ι' (A' (ψ (χ v) - x)) ∈ N
    rw [← hkey v hv]
    exact hψN (mem_image_of_mem ψ (hV₀V (hχmaps hv)))
  · intro y hy hys
    have hyW : y ∈ W := hrball (mem_ball.mpr (lt_of_lt_of_le hys (min_le_right _ _)))
    obtain ⟨z, hzV, rfl⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hyW, hy⟩
    have hzV₀ : z ∈ V₀ := hεball (mem_ball.mpr (hδprop z hzV
      (by rw [hψz₀]; exact lt_of_lt_of_le hys (min_le_left _ _))))
    refine ⟨A (ψ z - x), (hχΦ' z hzV₀).1, ?_⟩
    exact (congrArg ψ (hχΦ' z hzV₀).2).symm.trans (hkey _ (hχΦ' z hzV₀).1)
/-- Steps 9–10 of the oriented graph chart of an embedded `(n+1)`-submanifold used for the
zero-scale limits of Simon 7.5.3–7.5.5 (codimension-one regularity, 7.5.8).  Let `ι`, `ι'` be
linear isometries with orthogonal ranges and `Γ(v) = x + ιv + ι'u(v)`, `u` continuous at `0` with
`u(0) = 0`.  If `Γ(O) ⊆ N` for an open `O ∋ 0` and every point of `N ∩ B_s(x)` is some `Γ(v)`,
`v ∈ O`, then for `δ₂ = s/2` and a small `δ₁ > 0`: `B_{δ₁} ⊆ O`, `u(B_{δ₁}) ⊆ B_{δ₂}` and the part
of `N` in the cylinder `{x + ιv + ι'w : |v| < δ₁, |w| < δ₂}` is exactly `Γ(B_{δ₁})`.  The cylinder
lies in `B_s(x)`, and `ιa + ι'b = 0` forces `a = 0` (Pythagoras), so the `ι`-coordinate of a point
of `N` in the cylinder is that of a graph point. -/
theorem Submission.codim1_zsl_gc_graph_cylinder : ∀ (d k : ℕ) (N : Set (Euclid (d + k))) (x : Euclid (d + k)) (ι : Euclid d →ₗᵢ[ℝ] Euclid (d + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (d + k)) (O : Set (Euclid d)) (u : Euclid d → Euclid k) (s : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen O → (0 : Euclid d) ∈ O → ContinuousAt u 0 → u 0 = 0 → 0 < s → (∀ v ∈ O, x + ι v + ι' (u v) ∈ N) → (∀ y ∈ N, dist y x < s → ∃ v ∈ O, y = x + ι v + ι' (u v)) → ∃ δ₁ δ₂ : ℝ, 0 < δ₁ ∧ 0 < δ₂ ∧ ball (0 : Euclid d) δ₁ ⊆ O ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, u v ∈ ball (0 : Euclid k) δ₂) ∧ N ∩ {y | ∃ v ∈ ball (0 : Euclid d) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid d) δ₁ := by
  intro d k N x ι ι' O u s horth hO h0O hu hu0 hs hN hfib
  -- `ι a + ι' b = 0` forces `a = 0` (Pythagoras)
  have hinj : ∀ a b, ι a + ι' b = 0 → a = 0 := by
    intro a b h
    have h1 := norm_add_sq_real (ι a) (ι' b)
    rw [h, horth, ι.norm_map, ι'.norm_map, norm_zero] at h1
    have h2 : ‖a‖ = 0 := by nlinarith [norm_nonneg a, sq_nonneg ‖b‖]
    exact norm_eq_zero.mp h2
  -- radii: `δ₂ = s / 2`, `δ₁ = min (min η ρ) (s / 2)`
  obtain ⟨η, hη, hηu⟩ := Metric.continuousAt_iff.mp hu (s / 2) (half_pos hs)
  obtain ⟨ρ, hρ, hρO⟩ := Metric.isOpen_iff.mp hO 0 h0O
  have hδ₁ : 0 < min (min η ρ) (s / 2) := lt_min (lt_min hη hρ) (half_pos hs)
  have hballO : ball (0 : Euclid d) (min (min η ρ) (s / 2)) ⊆ O :=
    (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hρO
  have hball2 : ∀ v ∈ ball (0 : Euclid d) (min (min η ρ) (s / 2)),
      u v ∈ ball (0 : Euclid k) (s / 2) := by
    intro v hv
    have hv' : dist v 0 < η :=
      lt_of_lt_of_le (mem_ball.mp hv) ((min_le_left _ _).trans (min_le_left _ _))
    have h := hηu hv'
    rw [hu0] at h
    exact mem_ball.mpr h
  refine ⟨min (min η ρ) (s / 2), s / 2, hδ₁, half_pos hs, hballO, hball2, ?_⟩
  ext y
  constructor
  · -- `N ∩ Z ⊆ Γ(B_{δ₁})`: a point of the cylinder lies in `B_s(x)`
    rintro ⟨hyN, v', hv', w', hw', rfl⟩
    have hv's : ‖v'‖ < s / 2 :=
      lt_of_lt_of_le (mem_ball_zero_iff.mp hv') (min_le_right _ _)
    have hw's : ‖w'‖ < s / 2 := mem_ball_zero_iff.mp hw'
    have hdist : dist (x + ι v' + ι' w') x < s := by
      rw [dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖ι v' + ι' w'‖ ≤ ‖ι v'‖ + ‖ι' w'‖ := norm_add_le _ _
        _ = ‖v'‖ + ‖w'‖ := by rw [ι.norm_map, ι'.norm_map]
        _ < s / 2 + s / 2 := add_lt_add hv's hw's
        _ = s := add_halves s
    obtain ⟨v, -, hv⟩ := hfib _ hyN hdist
    have hv2 : ι v' + ι' w' = ι v + ι' (u v) := by
      rw [add_assoc, add_assoc] at hv
      exact add_left_cancel hv
    have h3 : ι (v' - v) + ι' (w' - u v) = 0 := by
      rw [map_sub, map_sub, sub_add_sub_comm, hv2, sub_self]
    have hvv : v' = v := sub_eq_zero.mp (hinj _ _ h3)
    exact ⟨v, hvv ▸ hv', hv.symm⟩
  · -- `Γ(B_{δ₁}) ⊆ N ∩ Z`
    rintro ⟨v, hv, rfl⟩
    exact ⟨hN v (hballO hv), v, hv, u v, hball2 v hv, rfl⟩

/-- **The orientation of `N` along a `C¹` graph through `x` is the normalized Jacobian
orientation** (steps 11–15 of the oriented graph chart of `N` at `x` used for Simon 7.5.3–7.5.5;
tangent spaces as in Ch. 2, §4, orientations as in Ch. 6, 2.2).  Let `Γ(v) = x + ιv + ι'u(v)` on
`B = B_δ(0)`, with `u` of class `C¹`, `u(0) = 0`, `Du(0) = 0`, `Γ(B) ⊆ N` and
`ξ_N(x) = ιe₀ ∧ ⋯ ∧ ιeₙ`.  The Jacobian orientation `ξ` of the graph (with `ξ(β) = 1` on `Γ(B)`)
satisfies `α(DΓ(v)e) = J(v) ξ(Γ v)(α)`, `J = √det(DΓ* ∘ DΓ)`, and orients `range DΓ(v)`, which
lies in `T_{Γ(v)}N` and has the same dimension `n + 1`; so `ξ_N(Γ v) = ±ξ(Γ v)`.  The sign
`s(v) = ξ_N(Γ v)(β(Γ v)) = ±1` is continuous on the connected ball, and `s(0) = 1` since
`DΓ(0) = ι` and `J(0) = 1`; hence `ξ_N ∘ Γ = ξ ∘ Γ` on `B`. -/
theorem Submission.codim1_zsl_gc_orientation_along_graph : ∀ (n k : ℕ) (N : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (x : Euclid (n + 1 + k)) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ : ℝ), IsOrientation (n + 1) N ξN → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → 0 < δ → ContDiffOn ℝ 1 u (ball 0 δ) → u 0 = 0 → fderiv ℝ u 0 = 0 → (∀ v ∈ ball (0 : Euclid (n + 1)) δ, x + ι v + ι' (u v) ∈ N) → (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξN x α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) → ∀ v ∈ ball (0 : Euclid (n + 1)) δ, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α := by
  intro n k N ξN x ι ι' u δ hor horth hδ hu hu0 hDu0 hΓN hξx
  -- the Jacobian orientation `ξ` of the graph `Γ(B)` and its dual covector field `β`
  obtain ⟨ξ, β, hξc, hβc, hξβ, hξor, hJ⟩ :=
    Submission.dgcr_graph_orientation_jacobian (n + 1) k ι ι' u x δ (Nat.succ_pos n) horth hδ hu
  have h0 : (0 : Euclid (n + 1)) ∈ ball (0 : Euclid (n + 1)) δ := mem_ball_self hδ
  -- `Γ` is `C¹` on the ball and maps it into `N`
  have hΓC1 : ContDiffOn ℝ 1 (fun v => x + ι v + ι' (u v)) (ball (0 : Euclid (n + 1)) δ) := by
    have h1 : ContDiffOn ℝ 1 (fun v : Euclid (n + 1) => x + ι v) (ball (0 : Euclid (n + 1)) δ) :=
      contDiffOn_const.add ι.contDiff.contDiffOn
    exact h1.add (ι'.contDiff.comp_contDiffOn hu)
  have hΓcont : ContinuousOn (fun v => x + ι v + ι' (u v)) (ball (0 : Euclid (n + 1)) δ) :=
    hΓC1.continuousOn
  have hΓmaps : MapsTo (fun v => x + ι v + ι' (u v)) (ball (0 : Euclid (n + 1)) δ) N :=
    fun v hv => hΓN v hv
  have hΓimg : (fun v => x + ι v + ι' (u v)) '' (ball (0 : Euclid (n + 1)) δ) ⊆ N :=
    hΓmaps.image_subset
  -- `range DΓ(v) ⊆ T_{Γ(v)}N`
  have hrange := Submission.dsmc_chart_range_subset_tangentSpace (n + 1 + k) 1 (n + 1) N
    (ball (0 : Euclid (n + 1)) δ) (fun v => x + ι v + ι' (u v)) le_rfl isOpen_ball
    (by exact_mod_cast hΓC1) hΓimg
  -- a subspace with a unit `(n + 1)`-orientation has dimension `n + 1`
  have hfin : ∀ (ζ : MultiVector (n + 1 + k) (n + 1)) (Q : Submodule ℝ (Euclid (n + 1 + k))),
      IsUnitOrientationOf ζ Q → Module.finrank ℝ Q = n + 1 := by
    rintro ζ Q ⟨τ, hτ, hspan, -⟩
    rw [← hspan, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- pointwise, `range DΓ(v) = T_{Γ(v)}N` and so `ξ_N(Γ v) = ±ξ(Γ v)`
  have hsign : ∀ v ∈ ball (0 : Euclid (n + 1)) δ,
      ξN (x + ι v + ι' (u v)) = ξ (x + ι v + ι' (u v)) ∨
        ξN (x + ι v + ι' (u v)) = -ξ (x + ι v + ι' (u v)) := by
    intro v hv
    obtain ⟨Q, hQ, hξNQ⟩ := hor.2 _ (hΓN v hv)
    have hle : LinearMap.range (fderiv ℝ (fun v => x + ι v + ι' (u v)) v :
        Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1 + k)) ≤ Q := by
      rintro y ⟨w, rfl⟩
      have hmem : (fderiv ℝ (fun v => x + ι v + ι' (u v)) v) w ∈
          tangentSpace N (x + ι v + ι' (u v)) := hrange v hv ⟨w, rfl⟩
      rw [← hQ] at hmem
      exact hmem
    have heq := Submodule.eq_of_le_of_finrank_eq hle
      (by rw [hfin _ _ (hξor v hv), hfin _ _ hξNQ])
    have hξQ : IsUnitOrientationOf (ξ (x + ι v + ι' (u v))) Q := heq ▸ hξor v hv
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg _ _ _ _ Q hξQ hξNQ
  -- the sign `s(v) = ξ_N(Γ v)(β(Γ v))` is continuous on the ball and takes the values `±1`
  have hs_cont : ContinuousOn (fun v => ξN (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))))
      (ball (0 : Euclid (n + 1)) δ) := by
    have h1 : ContinuousOn (fun v => ξN (x + ι v + ι' (u v))) (ball (0 : Euclid (n + 1)) δ) :=
      hor.1.comp hΓcont hΓmaps
    have h2 : ContinuousOn (fun v => β (x + ι v + ι' (u v))) (ball (0 : Euclid (n + 1)) δ) :=
      hβc.comp hΓcont (mapsTo_image _ _)
    exact h1.clm_apply h2
  have hs_val : ∀ v ∈ ball (0 : Euclid (n + 1)) δ,
      ξN (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))) = 1 ∨
        ξN (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))) = -1 := by
    intro v hv
    have h1 : ξ (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))) = 1 := hξβ _ ⟨v, hv, rfl⟩
    rcases hsign v hv with h | h
    · left; rw [h, h1]
    · right; rw [h, neg_apply, h1]
  -- at `0`: `Γ(0) = x`, `DΓ(0) = ι`, `J(0) = 1`, so `ξ_N(x) = ξ(x)` and `s(0) = 1`
  have hΓ0 : x + ι 0 + ι' (u 0) = x := by simp [hu0]
  have hu_diff : DifferentiableAt ℝ u 0 :=
    (hu.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds h0)
  have hD0 : fderiv ℝ (fun v => x + ι v + ι' (u v)) 0 = ι.toContinuousLinearMap := by
    have h1 : HasFDerivAt (fun v : Euclid (n + 1) => x + ι v) ι.toContinuousLinearMap 0 :=
      ι.toContinuousLinearMap.hasFDerivAt.const_add x
    have h2 : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u 0)) 0 :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp 0 hu_diff.hasFDerivAt
    rw [hDu0, ContinuousLinearMap.comp_zero] at h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3.fderiv
  have hdet0 : Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) 0).adjoint ∘L
      fderiv ℝ (fun v => x + ι v + ι' (u v)) 0).det) = 1 := by
    rw [hD0, LinearIsometry.adjoint_comp_self]
    show Real.sqrt (LinearMap.det ((1 : Euclid (n + 1) →L[ℝ] Euclid (n + 1)) :
      Euclid (n + 1) →ₗ[ℝ] Euclid (n + 1))) = 1
    rw [ContinuousLinearMap.toLinearMap_one, map_one, Real.sqrt_one]
  have hξ0 : ξN x = ξ x := by
    ext α
    have h1 := hJ 0 h0 α
    rw [hdet0, one_mul, hΓ0, hD0] at h1
    rw [hξx α, ← h1]
    rfl
  have hs0 : ξN (x + ι 0 + ι' (u 0)) (β (x + ι 0 + ι' (u 0))) = 1 := by
    have h1 := hξβ (x + ι 0 + ι' (u 0)) ⟨0, h0, rfl⟩
    rw [hΓ0] at h1 ⊢
    rw [hξ0]
    exact h1
  -- `s ≡ 1` on the preconnected ball, by the intermediate value theorem
  have hconst : ∀ v ∈ ball (0 : Euclid (n + 1)) δ,
      ξN (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))) = 1 := by
    intro v hv
    rcases hs_val v hv with h | h
    · exact h
    · exfalso
      have hIcc := (convex_ball (0 : Euclid (n + 1)) δ).isPreconnected.intermediate_value hv h0
        hs_cont
      have hmem : (0 : ℝ) ∈ Icc (ξN (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))))
          (ξN (x + ι 0 + ι' (u 0)) (β (x + ι 0 + ι' (u 0)))) := by
        rw [h, hs0]
        constructor <;> norm_num
      obtain ⟨w, hw, hw0⟩ := hIcc hmem
      have hw0' : ξN (x + ι w + ι' (u w)) (β (x + ι w + ι' (u w))) = 0 := hw0
      rcases hs_val w hw with h' | h' <;> rw [h'] at hw0' <;> norm_num at hw0'
  -- hence `ξ_N(Γ v) = ξ(Γ v)`, and the Jacobian identity of `ξ` is the claim
  intro v hv α
  have hpos : ξN (x + ι v + ι' (u v)) = ξ (x + ι v + ι' (u v)) := by
    rcases hsign v hv with h | h
    · exact h
    · exfalso
      have h1 := hconst v hv
      have h2 : ξ (x + ι v + ι' (u v)) (β (x + ι v + ι' (u v))) = 1 := hξβ _ ⟨v, hv, rfl⟩
      rw [h, neg_apply, h2] at h1
      norm_num at h1
  rw [hpos]
  exact hJ v hv α

/-- Step 4 of the zero-scale limit plane argument (Simon 7.5.3–7.5.5; embedded submanifolds and
tangent spaces: Ch. 2, §4 (4.1); orientations: Ch. 6, 2.2): near `x ∈ N`, an oriented embedded `C²`
`(n+1)`-submanifold `N ⊆ ℝ^{n+1+k}` is an oriented `C¹` graph over its tangent plane.
`IsOrientation` gives `T_xN = Q₀` with `ξ_N(x)` a unit orientation of `Q₀`; isometries `ι` onto
`Q₀`, adapted to `ξ_N(x)`, and `ι'` orthogonal to it give (a) and (d).  As `T_xN ⊆ range ι`, `N`
is near `x` the graph of `Γ(v) = x + ιv + ι'u(v)` with `u` of class `C¹`, `u(0) = 0`, `Du(0) = 0`;
inside a cylinder `{x + ιv + ι'w : |v| < δ₁, |w| < δ₂}` this gives (b) and (c).  Along `Γ`, `ξ_N`
is the Jacobian orientation `α ↦ α(DΓ(v)e₀, …, DΓ(v)eₙ)/√det(DΓ(v)*DΓ(v))`, which is (e). -/
theorem Submission.codim1_zsl_oriented_graph_chart : ∀ (n k : ℕ) (N : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (x : Euclid (n + 1 + k)), IsEmbeddedSubmanifold 2 (n + 1) N → IsOrientation (n + 1) N ξN → x ∈ N → ∃ (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ₁ δ₂ : ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) ∧ (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) ∧ 0 < δ₁ ∧ 0 < δ₂ ∧ ContDiffOn ℝ 1 u (ball 0 δ₁) ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, u v ∈ ball (0 : Euclid k) δ₂) ∧ N ∩ {y | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, y = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid (n + 1)) δ₁ ∧ (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξN x α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) ∧ ∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α := by
  intro n k N ξN x hN hξN hx
  -- `T_xN = Q₀`, and `ξ_N(x)` is a unit orientation of `Q₀`
  obtain ⟨Q₀, hQ₀, hξx⟩ := hξN.2 x hx
  -- (a), (d): `ι` maps onto `Q₀` and is adapted to `ξ_N(x)`; `ι'` is orthogonal to `ι`
  obtain ⟨ι, ι', hperp, hspan, hrange, hframe⟩ :=
    Submission.codim1_zsl_gc_oriented_frame n k Q₀ (ξN x) hξx
  -- near `x`, `N` is the graph of `Γ(v) = x + ιv + ι'u(v)` over an open `O ∋ 0`
  obtain ⟨O, u, s, hO, hO0, hs, hu, hu0, hDu0, hΓN, hcover⟩ :=
    Submission.codim1_zsl_gc_local_graph (n + 1) k N x ι ι' hN hx hperp hspan
      (hQ₀.symm.trans hrange.symm).subset
  -- (b), (c): inside the cylinder `{x + ιv + ι'w : |v| < δ₁, |w| < δ₂}`, `N` is `Γ(B_{δ₁})`
  obtain ⟨δ₁, δ₂, hδ₁, hδ₂, hO₁, hmaps, hcyl⟩ :=
    Submission.codim1_zsl_gc_graph_cylinder (n + 1) k N x ι ι' O u s hperp hO hO0
      (hu.continuousOn.continuousAt (hO.mem_nhds hO0)) hu0 hs hΓN hcover
  have hu₁ : ContDiffOn ℝ 1 u (ball 0 δ₁) := hu.mono hO₁
  -- (e): along `Γ`, `ξ_N` is the Jacobian orientation normalized by `√det(DΓ*DΓ)`
  exact ⟨ι, ι', u, δ₁, δ₂, hperp, hspan, hδ₁, hδ₂, hu₁, hu0, hDu0, hmaps, hcyl, hframe,
    Submission.codim1_zsl_gc_orientation_along_graph n k N ξN x ι ι' u δ₁ hξN hperp hδ₁ hu₁ hu0
      hDu0 (fun v hv => hΓN v (hO₁ hv)) hframe⟩
/-- **Area formula for a `C¹` graph over an `m`-plane** (Simon Ch. 2, 3.1–3.3).  Let
`G(w) = ιw + ι'g(w)` with `ι`, `ι'` isometries onto orthogonal subspaces and `g` of class `C¹` on
the open set `D ⊇ A`, and `J(w) = √det(DG(w)* ∘ DG(w))`.  Then
`∫_{G(A)} f dHᵐ = ∫_A J(w) f(G(w)) dw` for every `f`.  `G` is continuous on `A` and injective
(`ι(w - w') = ι'(g w' - g w)` is orthogonal to itself), `J` is Borel as a continuous function of
`fderiv ℝ G`, and `Hᵐ(G(B)) = ∫_B J` for every measurable `B ⊆ A` (`codim1_zsl_ga_set_identity`);
`codim1_zsl_ga_integral_transfer` turns this weighted set identity into the Bochner identity. -/
theorem Submission.codim1_zsl_graph_area_formula : ∀ (m k : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + k)) (g : Euclid m → Euclid k) (D A : Set (Euclid m)) (f : Euclid (m + k) → ℝ), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → ∫ y in (fun w => ι w + ι' (g w)) '' A, f y ∂μHE[m] = ∫ w in A, Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det) * f (ι w + ι' (g w)) := by
  intro m k ι ι' g D A f horth hD hg hA hAD
  -- `G` is continuous on `A ⊆ D`, where `g` is `C¹`
  have hGc : ContinuousOn (fun w => ι w + ι' (g w)) A :=
    ι.continuous.continuousOn.add (ι'.continuous.comp_continuousOn (hg.continuousOn.mono hAD))
  -- `G` is injective: `ι (w - w') = ι' (g w' - g w)` is orthogonal to itself
  have hGi : Injective fun w => ι w + ι' (g w) := by
    intro w w' h
    have h1 : ι (w - w') = ι' (g w' - g w) := by
      rw [map_sub, map_sub, sub_eq_sub_iff_add_eq_add, add_comm (ι' (g w'))]
      exact h
    have h2 := horth (w - w') (g w' - g w)
    rw [← h1, inner_self_eq_zero] at h2
    exact sub_eq_zero.1 (ι.injective (h2.trans (map_zero ι).symm))
  -- `J = √det(DG* ∘ DG)` is Borel: a continuous function of the Borel map `fderiv ℝ G`
  have hJm : Measurable fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
      fderiv ℝ (fun w => ι w + ι' (g w)) w).det) := by
    have hc : Continuous fun T : Euclid m →L[ℝ] Euclid (m + k) =>
        Real.sqrt ((T.adjoint ∘L T).det) :=
      Real.continuous_sqrt.comp (ContinuousLinearMap.continuous_det.comp
        ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m)
          (F := Euclid (m + k))).continuous.clm_comp continuous_id))
    exact hc.measurable.comp (measurable_fderiv ℝ fun w => ι w + ι' (g w))
  -- `Hᵐ(G(B)) = ∫_B J` for measurable `B ⊆ A ⊆ D`; transfer to Bochner integrals
  exact Submission.codim1_zsl_ga_integral_transfer m (m + k) μHE[m] (fun w => ι w + ι' (g w))
    (fun w => Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L
      fderiv ℝ (fun w => ι w + ι' (g w)) w).det)) A f hA hGc hGi.injOn hJm
    (fun w _ => Real.sqrt_nonneg _) fun B hB hBA =>
      Submission.codim1_zsl_ga_set_identity m k ι ι' g D B horth hD hg hB (hBA.trans hAD)
/-- **Compactness for sets of locally bounded perimeter** (Simon Ch. 2, 2.6, for the indicators
`uᵢ = 1_{Fᵢ}`).  If for each `R > 0` the perimeters of the `Fᵢ` in `B_R(0)` are eventually at most
`c(R)` (`∫_{Fᵢ} div φ ≤ c(R)` for smooth `φ` with `spt φ ⊆ B_R(0)` and `|φ| ≤ 1`), then a
subsequence converges in `L¹_loc`: `L^m((F_{σ i} Δ F') ∩ B_R(0)) → 0` for every `R`.
For `R > 0` and `i ≥ i_{R+2}`, `codim1_zsl_pc_translation_estimate` (steps 1–4: mollify, integrate
by parts, use the fundamental theorem of calculus, let `ε → 0`) turns the bound `c(R + 2)` into
`L^m(((Fᵢ − h) Δ Fᵢ) ∩ B_R(0)) ≤ c(R + 2)|h|` for `|h| ≤ 1`.  From this uniform local translation
estimate, `codim1_zsl_pc_compact_of_translation` (steps 5–8: cube averages, a diagonal
subsequence, a fast Cauchy subsequence and its `liminf` set) gives `σ` and `F'`. -/
theorem Submission.codim1_zsl_perimeter_compactness : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F i, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball 0 R)) atTop (𝓝 0) := by
  intro m F hF hP
  -- Steps 5–8: a uniform local translation estimate gives `σ` and `F'`.
  refine Submission.codim1_zsl_pc_compact_of_translation m F hF fun R hR => ?_
  -- Steps 1–4: for `i ≥ i_{R+2}`, the perimeter bound `c(R + 2)` gives the estimate with `C = c`.
  obtain ⟨c, hc⟩ := hP (R + 2) (by linarith)
  exact ⟨c, hc.mono fun i hi =>
    Submission.codim1_zsl_pc_translation_estimate m (F i) R c (hF i) hi⟩

/-- **Graph integrals under `C¹`-flattening graphs and `L¹_loc`-convergent domains** (Simon 7.5.3,
7.5.5).  For `G_i(w) = ιw + ι'gᵢ(w)` on `B = B_R(0)` with `gᵢ → b`, `Dgᵢ → 0` uniformly on `B` and
`Lᵐ((Aᵢ Δ A) ∩ B) → 0`, `∫_{Aᵢ∩B} β(Gᵢ)(DGᵢ e₀, …, DGᵢ e_{m−1}) → ∫_{A∩B} β(ιw + ι'b)(ιe₀, …)`.
`β` is bounded by `M` and uniformly continuous, and `DGᵢ(w) = ι + ι' ∘ Dgᵢ(w)`, so the multilinear
bounds `le_opNorm` and `norm_image_sub_le` give `|hᵢ − h| ≤ 2ᵐ|β(Gᵢ) − β(ιw + ι'b)| + Mm2ᵐ‖Dgᵢ‖`
for the integrands, which therefore converge uniformly on `B`; the integrals then differ by at most
`Lᵐ(B) sup_B |hᵢ − h| + 2M Lᵐ((Aᵢ Δ A) ∩ B) → 0`. -/
theorem Submission.codim1_zsl_fl_graph_integral_tendsto : ∀ (m k P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (b : Euclid k) (R : ℝ) (β : Euclid P → Covector (Euclid P) m) (gs : ℕ → Euclid m → Euclid k) (As : ℕ → Set (Euclid m)) (A : Set (Euclid m)), Continuous β → HasCompactSupport β → (∀ i, MeasurableSet (As i)) → MeasurableSet A → Tendsto (fun i => volume (symmDiff (As i) A ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) → (∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, DifferentiableAt ℝ (gs i) w) → (∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid m) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → Tendsto (fun i => ∫ w in As i ∩ ball 0 R, β (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) atTop (𝓝 (∫ w in A ∩ ball 0 R, β (ι w + ι' b) (fun j => ι (EuclideanSpace.single j (1 : ℝ))))) := by
  intro m k P ι ι' b R β gs As A hβc hβs hAs hA hsymm hH1 hH2
  classical
  set B : Set (Euclid m) := ball (0 : Euclid m) R with hB
  have hBmeas : MeasurableSet B := measurableSet_ball
  have hBfin : volume B < ⊤ := measure_ball_lt_top
  obtain ⟨M, hM⟩ := hβc.bounded_above_of_compact_support hβs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hβu : UniformContinuous β := hβs.uniformContinuous_of_continuous hβc
  set e : Fin m → Euclid m := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hej : ∀ j, ‖e j‖ = 1 := by intro j; simp [he]
  set Φ : Euclid P × (Euclid m →L[ℝ] Euclid P) → ℝ := fun p => β p.1 (fun j => p.2 (e j)) with hΦ
  have hΦc : Continuous Φ := by
    have h1 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => β p.1 :=
      hβc.comp continuous_fst
    have h2 : Continuous fun p : Euclid P × (Euclid m →L[ℝ] Euclid P) => (fun j => p.2 (e j)) :=
      continuous_pi fun j => (continuous_eval_const (e j)).comp continuous_snd
    exact continuous_eval.comp (h1.prodMk h2)
  set G : ℕ → Euclid m → Euclid P := fun i w => ι w + ι' (gs i w) with hG
  set H : ℕ → Euclid m → ℝ := fun i w => Φ (G i w, fderiv ℝ (G i) w) with hH
  set H' : Euclid m → ℝ := fun w => β (ι w + ι' b) (fun j => ι (e j)) with hH'
  change Tendsto (fun i => ∫ w in As i ∩ B, H i w) atTop (𝓝 (∫ w in A ∩ B, H' w))
  have hD : ∀ i w, DifferentiableAt ℝ (gs i) w →
      fderiv ℝ (G i) w = ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w) := by
    intro i w hw
    have hι : HasFDerivAt (fun w => ι w) ι.toContinuousLinearMap w :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun w => ι' (gs i w))
        (ι'.toContinuousLinearMap.comp (fderiv ℝ (gs i) w)) w :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp w hw.hasFDerivAt
    exact (hι.add hι').fderiv
  have hH'b : ∀ w, ‖H' w‖ ≤ M := by
    intro w
    calc ‖H' w‖ ≤ ‖β (ι w + ι' b)‖ * ∏ j, ‖ι (e j)‖ := ContinuousAlternatingMap.le_opNorm _ _
      _ = ‖β (ι w + ι' b)‖ := by simp [hej]
      _ ≤ M := hM _
  have hH'c : Continuous H' := by
    have h1 : Continuous fun w : Euclid m => β (ι w + ι' b) :=
      hβc.comp (ι.continuous.add continuous_const)
    exact (continuous_eval_const (fun j => ι (e j))).comp h1
  -- pointwise estimate
  have hpt : ∀ i w, DifferentiableAt ℝ (gs i) w → ‖fderiv ℝ (gs i) w‖ ≤ 1 →
      ‖H i w - H' w‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ +
        M * m * 2 ^ m * ‖fderiv ℝ (gs i) w‖ := by
    intro i w hd hL1
    set L := fderiv ℝ (gs i) w with hL
    set u : Fin m → Euclid P := fun j => fderiv ℝ (G i) w (e j) with hueq
    set u' : Fin m → Euclid P := fun j => ι (e j) with hu'eq
    have hu : ∀ j, u j = ι (e j) + ι' (L (e j)) := by
      intro j
      simp [u, hD i w hd, L]
    have hunorm : ‖u‖ ≤ 2 := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro j
      rw [hu j]
      calc ‖ι (e j) + ι' (L (e j))‖ ≤ ‖ι (e j)‖ + ‖ι' (L (e j))‖ := norm_add_le _ _
        _ = 1 + ‖L (e j)‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map, hej]
        _ ≤ 1 + ‖L‖ * ‖e j‖ := by gcongr; exact L.le_opNorm _
        _ ≤ 2 := by rw [hej]; linarith
    have hu'norm : ‖u'‖ ≤ 1 := by
      rw [pi_norm_le_iff_of_nonneg zero_le_one]
      intro j
      simp [u', hej]
    have hdiff : ‖u - u'‖ ≤ ‖L‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro j
      rw [Pi.sub_apply, hu j]
      simp only [u', add_sub_cancel_left, LinearIsometry.norm_map]
      calc ‖L (e j)‖ ≤ ‖L‖ * ‖e j‖ := L.le_opNorm _
        _ = ‖L‖ := by rw [hej, mul_one]
    have h1 : ‖β (G i w) u - β (ι w + ι' b) u‖ ≤ 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ := by
      rw [← ContinuousAlternatingMap.sub_apply]
      calc _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * ∏ j, ‖u j‖ :=
            ContinuousAlternatingMap.le_opNorm _ _
        _ ≤ ‖β (G i w) - β (ι w + ι' b)‖ * 2 ^ m := by
          gcongr
          calc ∏ j, ‖u j‖ ≤ ∏ _j : Fin m, (2 : ℝ) :=
                Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
                  (fun j _ => (norm_le_pi_norm u j).trans hunorm)
            _ = 2 ^ m := by simp
        _ = _ := mul_comm _ _
    have h2 : ‖β (ι w + ι' b) u - β (ι w + ι' b) u'‖ ≤ M * m * 2 ^ m * ‖L‖ := by
      calc _ ≤ ‖β (ι w + ι' b)‖ * (Fintype.card (Fin m)) *
              (max ‖u‖ ‖u'‖) ^ (Fintype.card (Fin m) - 1) * ‖u - u'‖ :=
            ContinuousAlternatingMap.norm_image_sub_le _ _ _
        _ ≤ M * m * 2 ^ m * ‖L‖ := by
            rw [Fintype.card_fin]
            have hmax : max ‖u‖ ‖u'‖ ≤ 2 := max_le hunorm (hu'norm.trans (by norm_num))
            have hpow : (max ‖u‖ ‖u'‖) ^ (m - 1) ≤ 2 ^ m :=
              (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg _)) hmax _).trans
                (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
            gcongr
            exact hM _
    have hsplit : H i w - H' w =
        (β (G i w) u - β (ι w + ι' b) u) + (β (ι w + ι' b) u - β (ι w + ι' b) u') := by
      simp only [H, H', Φ, u, u']
      ring
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add h1 h2)
  -- uniform convergence on B
  have hunif : ∀ ε > 0, ∀ᶠ i in atTop, ∀ w ∈ B, ‖H i w - H' w‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδβ⟩ := Metric.uniformContinuous_iff.1 hβu (ε / (2 * 2 ^ m)) (by positivity)
    set X : ℝ := M * m * 2 ^ m with hX
    have hX0 : 0 ≤ X := by positivity
    set η : ℝ := min 1 (ε / (2 * (X + 1))) with hη
    have hηpos : 0 < η := lt_min one_pos (by positivity)
    filter_upwards [hH1, hH2 δ hδ, hH2 η hηpos] with i hi1 hi2 hi3
    intro w hw
    have hd := hi1 w hw
    have hL1 : ‖fderiv ℝ (gs i) w‖ ≤ 1 := (hi3 w hw).2.le.trans (min_le_left _ _)
    have hLη : ‖fderiv ℝ (gs i) w‖ ≤ ε / (2 * (X + 1)) :=
      (hi3 w hw).2.le.trans (min_le_right _ _)
    have hβd : ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / (2 * 2 ^ m) := by
      rw [← dist_eq_norm]
      apply le_of_lt
      apply hδβ
      rw [dist_eq_norm]
      simp only [G]
      rw [add_sub_add_left_eq_sub, ← map_sub, LinearIsometry.norm_map]
      exact (hi2 w hw).1
    refine (hpt i w hd hL1).trans ?_
    have e1 : 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ ε / 2 := by
      calc 2 ^ m * ‖β (G i w) - β (ι w + ι' b)‖ ≤ 2 ^ m * (ε / (2 * 2 ^ m)) := by gcongr
        _ = ε / 2 := by field_simp
    have e2 : X * ‖fderiv ℝ (gs i) w‖ ≤ ε / 2 := by
      calc X * ‖fderiv ℝ (gs i) w‖ ≤ X * (ε / (2 * (X + 1))) := by gcongr
        _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    linarith
  -- measurability
  have hHmeas : ∀ᶠ i in atTop, AEStronglyMeasurable (H i) (volume.restrict B) := by
    filter_upwards [hH1] with i hi
    have hGc : ContinuousOn (G i) B := fun w hw =>
      (ι.continuous.continuousAt.add
        (ι'.continuous.continuousAt.comp (hi w hw).continuousAt)).continuousWithinAt
    have h1 : AEStronglyMeasurable (G i) (volume.restrict B) := hGc.aestronglyMeasurable hBmeas
    have h2 : AEStronglyMeasurable (fderiv ℝ (G i)) (volume.restrict B) :=
      (measurable_fderiv ℝ (G i)).aestronglyMeasurable
    exact hΦc.comp_aestronglyMeasurable (h1.prodMk h2)
  -- the symmetric differences
  have hsymm' : Tendsto (fun i => (volume (symmDiff (As i) A ∩ B)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
    simpa [Function.comp_def] using this
  set VB : ℝ := (volume B).toReal with hVB
  have hVB0 : 0 ≤ VB := ENNReal.toReal_nonneg
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hunif (ε / (2 * (VB + 1))) (by positivity), hunif 1 one_pos, hHmeas,
    hsymm'.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (4 * (M + 1)) by positivity))]
    with i hi1 hi1' hi2 hi3
  have hsB : As i ∩ B ⊆ B := inter_subset_right
  have hsfin : volume (As i ∩ B) < ⊤ := (measure_mono hsB).trans_lt hBfin
  have htfin : volume (A ∩ B) < ⊤ := (measure_mono inter_subset_right).trans_lt hBfin
  have hsmeas : MeasurableSet (As i ∩ B) := (hAs i).inter hBmeas
  have htmeas : MeasurableSet (A ∩ B) := hA.inter hBmeas
  have hHi_int : IntegrableOn (H i) (As i ∩ B) := by
    refine IntegrableOn.of_bound hsfin (hi2.mono_measure (Measure.restrict_mono hsB le_rfl)) (M + 1) ?_
    refine (ae_restrict_iff' hsmeas).2 (Eventually.of_forall fun w hw => ?_)
    have h := hi1' w hw.2
    calc ‖H i w‖ = ‖(H i w - H' w) + H' w‖ := by rw [sub_add_cancel]
      _ ≤ ‖H i w - H' w‖ + ‖H' w‖ := norm_add_le _ _
      _ ≤ 1 + M := add_le_add h (hH'b w)
      _ = M + 1 := add_comm _ _
  have hH'_int : ∀ s : Set (Euclid m), volume s < ⊤ → IntegrableOn H' s := fun s hs =>
    IntegrableOn.of_bound hs hH'c.aestronglyMeasurable M (Eventually.of_forall hH'b)
  -- first term
  have hT1 : ‖(∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w‖ ≤ ε / (2 * (VB + 1)) * VB := by
    rw [← integral_sub hHi_int (hH'_int _ hsfin)]
    refine (norm_setIntegral_le_of_norm_le_const hsfin fun w hw => hi1 w hw.2).trans ?_
    gcongr
    exact measureReal_mono hsB hBfin.ne
  -- second term
  have hT2 : ‖(∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w‖ ≤
      2 * M * (volume (symmDiff (As i) A ∩ B)).toReal := by
    have e1 := integral_inter_add_sdiff htmeas (hH'_int _ hsfin)
    have e2 := integral_inter_add_sdiff hsmeas (hH'_int _ htfin)
    rw [inter_comm (A ∩ B)] at e2
    have hsub1 : (As i ∩ B) \ (A ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inl ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hsub2 : (A ∩ B) \ (As i ∩ B) ⊆ symmDiff (As i) A ∩ B := by
      rintro w ⟨⟨hwA, hwB⟩, hw⟩
      exact ⟨Or.inr ⟨hwA, fun h => hw ⟨h, hwB⟩⟩, hwB⟩
    have hΔfin : volume (symmDiff (As i) A ∩ B) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt hBfin
    have b1 : ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub1).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub1 hΔfin.ne
    have b2 : ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ ≤ M * (volume (symmDiff (As i) A ∩ B)).toReal := by
      refine (norm_setIntegral_le_of_norm_le_const ((measure_mono hsub2).trans_lt hΔfin)
        fun w _ => hH'b w).trans ?_
      gcongr
      exact measureReal_mono hsub2 hΔfin.ne
    have : (∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w =
        (∫ w in (As i ∩ B) \ (A ∩ B), H' w) - ∫ w in (A ∩ B) \ (As i ∩ B), H' w := by
      linarith
    rw [this]
    calc _ ≤ ‖∫ w in (As i ∩ B) \ (A ∩ B), H' w‖ + ‖∫ w in (A ∩ B) \ (As i ∩ B), H' w‖ :=
          norm_sub_le _ _
      _ ≤ _ := by linarith
  rw [dist_eq_norm]
  have hsum : (∫ w in As i ∩ B, H i w) - ∫ w in A ∩ B, H' w =
      ((∫ w in As i ∩ B, H i w) - ∫ w in As i ∩ B, H' w) +
        ((∫ w in As i ∩ B, H' w) - ∫ w in A ∩ B, H' w) := by ring
  rw [hsum]
  have hlt1 : ε / (2 * (VB + 1)) * VB < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hlt2 : 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal ≤ ε / 2 := by
    have h3 : (volume (symmDiff (As i) A ∩ B)).toReal < ε / (4 * (M + 1)) := hi3
    have h4 : 0 ≤ (volume (symmDiff (As i) A ∩ B)).toReal := ENNReal.toReal_nonneg
    calc 2 * M * (volume (symmDiff (As i) A ∩ B)).toReal
        ≤ 2 * (M + 1) * (volume (symmDiff (As i) A ∩ B)).toReal := by gcongr; linarith
      _ ≤ 2 * (M + 1) * (ε / (4 * (M + 1))) := by gcongr
      _ = ε / 2 := by field_simp; ring
  calc _ ≤ _ := norm_add_le _ _
    _ < ε := by linarith
/-- **Integrals over the image of a measurable set under an affine isometry `ℝᵐ → ℝᴾ`** (Simon
7.5.5 regards the limit set `F` as an `Hⁿ⁺¹`-measurable subset of the plane `TₓN` in this way).
`G(w) = ιw + c` is an isometry of the complete space `ℝᵐ`, hence a measurable embedding, so `G(A)`
is measurable.  `Hᵐ` is invariant under isometries and equals `Lᵐ` on `ℝᵐ`, so
`G_#Lᵐ = Hᵐ⌞G(ℝᵐ)` and, by injectivity, `Hᵐ⌞G(A) = G_#(Lᵐ⌞A)`; hence
`∫_{G(A)} f dHᵐ = ∫_A f(G(w)) dw` for every `f`. -/
theorem Submission.codim1_zsl_fl_isometry_image_setIntegral : ∀ (m P : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (c : Euclid P) (A : Set (Euclid m)), MeasurableSet A → MeasurableSet ((fun w => ι w + c) '' A) ∧ ∀ f : Euclid P → ℝ, ∫ y in (fun w => ι w + c) '' A, f y ∂μHE[m] = ∫ w in A, f (ι w + c) := by
  intro m P ι c A hA
  -- `G` is an isometry of the complete space `ℝᵐ`, hence a measurable embedding.
  have hiso : Isometry (fun w => ι w + c) := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_right_eq_sub, ← map_sub, LinearIsometry.norm_map]
  have hemb : MeasurableEmbedding (fun w => ι w + c) :=
    hiso.isClosedEmbedding.measurableEmbedding
  have hAimg : MeasurableSet ((fun w => ι w + c) '' A) := hemb.measurableSet_image' hA
  refine ⟨hAimg, fun f => ?_⟩
  -- `G_#Lᵐ = Hᵐ⌞G(ℝᵐ)`, hence `Hᵐ⌞G(A) = G_#(Lᵐ⌞A)`.
  have hmap : (volume : Measure (Euclid m)).map (fun w => ι w + c) =
      (μHE[m] : Measure (Euclid P)).restrict (range (fun w => ι w + c)) := by
    rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  have hres : (μHE[m] : Measure (Euclid P)).restrict ((fun w => ι w + c) '' A) =
      ((volume : Measure (Euclid m)).restrict A).map (fun w => ι w + c) := by
    rw [← preimage_image_eq A hemb.injective, ← hemb.restrict_map, hmap,
      Measure.restrict_restrict hAimg, inter_eq_left.mpr (image_subset_range _ _),
      preimage_image_eq A hemb.injective]
  rw [hres, hemb.integral_map]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- The tangent space of the translate `{z | z + a ∈ Q} = Q − a` at any of its points `y` is `Q`:
slopes `t⁻¹(γ t − γ 0)` of a curve in the translate lie in the closed subspace `Q` and tend to
`γ'(0)`, and the line `t ↦ y + t • v` realizes each `v ∈ Q` as a velocity. -/
theorem codim1_zsl_op_translate_tangentSpace_eq : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a y : Euclid P), y + a ∈ Q → tangentSpace {z | z + a ∈ Q} y = (Q : Set (Euclid P)) := by
  intro P Q a y hy
  -- Step 1: `Q` is finite-dimensional, hence closed.
  have hQ : IsClosed (Q : Set (Euclid P)) := Q.closed_of_finiteDimensional
  ext v
  constructor
  · -- Step 2: the slopes `t⁻¹(γ t − γ 0)` lie in `Q` for `t ∈ (−1, 1)` and tend to `v`.
    rintro ⟨γ, -, hγA, hγ0, hγv⟩
    have hIoo : Ioo (-1 : ℝ) 1 ∈ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    refine hQ.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.mp hγv) ?_
    filter_upwards [hIoo] with t ht
    have h1 : γ t + a ∈ Q := hγA ht
    have h2 : γ 0 + a ∈ Q := hγ0 ▸ hy
    rw [slope_def_module]
    exact Q.smul_mem _ (by simpa using Q.sub_mem h1 h2)
  · -- Step 3: the line `t ↦ y + t • v` witnesses `v ∈ tangentSpace {z | z + a ∈ Q} y`.
    intro hv
    refine ⟨fun t => y + t • v, ?_, ?_, by simp, ?_⟩
    · exact (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
    · intro t _
      show y + t • v + a ∈ Q
      rw [add_right_comm]
      exact Q.add_mem hy (Q.smul_mem t hv)
    · simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y

end Submission

/-- **Lemma A-plane** (Simon 7.5, class `𝒪`, p. 197; used for the zero-scale limits of
7.5.3–7.5.5).  If `ξ` is a unit orientation of the subspace `Q ⊆ ℝᴾ`, then `dim Q = n + 1` and the
offset plane `A = Q − a = {y : y + a ∈ Q}`, oriented by the constant `ξ`, is in class `𝒪` of `ℝᴾ`.
The orthonormal `τ` of `ξ` is linearly independent and spans `Q`, so `dim Q = n + 1`; `A` is an
embedded `C²` `(n + 1)`-submanifold, and `T_yA = Q` for `y ∈ A`, so the constant `ξ` orients `A`;
`A` is closed (the preimage of the finite-dimensional, hence closed, `Q`) and contains `−a`. -/
theorem Submission.codim1_zsl_offset_plane_inClassO : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P (n + 1)) (a : Euclid P), IsUnitOrientationOf ξ Q → Module.finrank ℝ Q = n + 1 ∧ InClassO n (univ : Set (Euclid P)) {y | y + a ∈ Q} (fun _ => ξ) := by
  intro P n Q ξ a hξ
  obtain ⟨τ, hτ, hspan, -⟩ := id hξ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- `dim Q = n + 1`: `τ` is a basis of `Q`
  · rw [← hspan, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- `A` is an embedded `C²` `(n + 1)`-submanifold
  · exact Submission.codim1_zsl_op_translate_isEmbeddedSubmanifold P (n + 1) 2 Q τ a hτ hspan
  -- the constant `ξ` orients `A`, as `T_yA = Q` for every `y ∈ A`
  · exact ⟨continuousOn_const, fun y hy =>
      ⟨Q, (Submission.codim1_zsl_op_translate_tangentSpace_eq P Q a y hy).symm, hξ⟩⟩
  -- `A` is closed, so `closure A \ A = ∅`
  · have hA : IsClosed {y : Euclid P | y + a ∈ Q} :=
      Q.closed_of_finiteDimensional.preimage (continuous_add_const a)
    rw [hA.closure_eq, Set.sdiff_self, empty_inter]
  -- `−a ∈ A`
  · exact ⟨-a, show -a + a ∈ Q by rw [neg_add_cancel]; exact Q.zero_mem, mem_univ _⟩
theorem Submission.dgcr_bwd_graph_pullback_extDeriv : ∀ (m k : ℕ) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (ψ : DifferentialForm (Euclid (m + 1)) m) (v : Euclid (m + 1)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsSmoothForm ψ → DifferentiableAt ℝ u v → exteriorDerivative (affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = exteriorDerivative ψ v (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m k ι ι' u z ψ v hperp hψ hu
  -- `L := ι*` is a left inverse of `ι` and annihilates the orthogonal factor `ι'`.
  have hLι : ∀ v', ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι v') = v' := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v' y
  have hLι' : ∀ w, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  -- Chain rule for the graph map `Φ v = z + ι v + ι' (u v)`.
  have hD : fderiv ℝ (fun v => z + ι v + ι' (u v)) v =
      ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v) := by
    have hι : HasFDerivAt (fun v => ι v) ι.toContinuousLinearMap v :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp v hu.hasFDerivAt
    have h1 := ((hasFDerivAt_const z v).add hι).add hι'
    rw [zero_add] at h1
    exact h1.fderiv
  -- `d` commutes with the affine pull-back; the base point is `v` and the frame is `eᵢ`.
  rw [exteriorDerivative_affinePullbackForm _ _ hψ]
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  · simp [map_add, hLι, hLι']
  · funext i
    simp [hD, hLι, hLι']

theorem Submission.codim1_zsl_fl_divergence_lift : ∀ (n k : ℕ) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → ∃ K : ℝ, 0 < K ∧ ∀ h R : ℝ, 0 < h → ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∃ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 (R + 2 * h) ∧ (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) ∧ ∀ (g : Euclid (n + 1) → Euclid k) (v : Euclid (n + 1)), DifferentiableAt ℝ g v → ‖g v‖ < h → exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι v + ι' (g v)) (fun j => fderiv ℝ (fun w => ι w + ι' (g w)) v (EuclideanSpace.single j (1 : ℝ))) = K⁻¹ * LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap := by
  intro n k ι ι' hperp hspan
  classical
  set π : Euclid (n + 1 + k) →L[ℝ] Euclid (n + 1) :=
    ContinuousLinearMap.adjoint ι.toContinuousLinearMap with hπeq
  set π' : Euclid (n + 1 + k) →L[ℝ] Euclid k :=
    ContinuousLinearMap.adjoint ι'.toContinuousLinearMap with hπ'eq
  have hπι : ∀ v, π (ι v) = v := by
    intro v
    apply ext_inner_right ℝ
    intro y
    rw [hπeq, ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v y
  have hπι' : ∀ w, π (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hπeq, ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  have hπ'ι' : ∀ w, π' (ι' w) = w := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [hπ'eq, ContinuousLinearMap.adjoint_inner_left]
    exact ι'.inner_map_map w y
  have hπ'ι : ∀ v, π' (ι v) = 0 := by
    intro v
    apply ext_inner_right ℝ
    intro y
    rw [hπ'eq, ContinuousLinearMap.adjoint_inner_left, inner_zero_left]
    exact hperp v y
  have hnorm_le : ∀ y, ‖y‖ ≤ ‖π y‖ + ‖π' y‖ := by
    intro y
    obtain ⟨v, w, rfl⟩ := hspan y
    simp only [map_add, hπι, hπι', hπ'ι', hπ'ι, add_zero, zero_add]
    calc ‖ι v + ι' w‖ ≤ ‖ι v‖ + ‖ι' w‖ := norm_add_le _ _
      _ = ‖v‖ + ‖w‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
  choose β hβ using Submission.dgcr_bwd_coordinate_covector n
  let Θ : Euclid (n + 1) →L[ℝ] Covector (Euclid (n + 1)) n :=
    ∑ j : Fin (n + 1), (EuclideanSpace.proj j : Euclid (n + 1) →L[ℝ] ℝ).smulRight (β j)
  have hΘe : ∀ (z : Euclid (n + 1)) (i : Fin (n + 1)),
      Θ z (i.removeNth (fun l : Fin (n + 1) => EuclideanSpace.single l (1 : ℝ))) =
        (-1 : ℝ) ^ (i : ℕ) * z i := by
    intro z i
    have hΘz : Θ z = ∑ j, z j • β j := by simp [Θ]
    rw [hΘz, ContinuousAlternatingMap.sum_apply]
    simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · rw [hβ i i, ite_eq_left rfl]
      ring
    · intro j _ hji
      rw [hβ j i, ite_eq_right (Ne.symm hji), mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  set N : ℝ := (Fintype.card (Fin n → Fin (n + 1 + k)) : ℝ) with hN
  set K : ℝ := Real.sqrt N * ‖Θ‖ * ‖π‖ ^ n + 1 with hK
  have hKpos : 0 < K := by positivity
  refine ⟨K, hKpos, ?_⟩
  intro h R hh φ hφ hφc hφs hφn
  let f : ContDiffBump (0 : Euclid k) := ⟨h, 2 * h, hh, by linarith⟩
  let α : DifferentialForm (Euclid (n + 1)) n := fun v => Θ (φ v)
  have hαsmooth : IsSmoothForm α := Θ.contDiff.comp hφ
  let ω₀ : DifferentialForm (Euclid (n + 1 + k)) n := fun y =>
    (K⁻¹ * f (π' y)) • affinePullbackForm π (-(π 0)) α y
  have hω₀smooth : IsSmoothForm ω₀ := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y => K⁻¹ * f (π' y)) :=
      contDiff_const.mul (f.contDiff.comp π'.contDiff)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (affinePullbackForm π (-(π 0)) α) :=
      affinePullbackForm_isSmoothForm π _ hαsmooth
    exact h1.smul h2
  set Q : Set (Euclid (n + 1 + k)) := {y | π y ∈ tsupport φ ∧ ‖π' y‖ ≤ 2 * h} with hQ
  have hQclosed : IsClosed Q :=
    ((isClosed_tsupport φ).preimage π.continuous).inter
      (isClosed_le (continuous_norm.comp π'.continuous) continuous_const)
  have hsuppQ : support ω₀ ⊆ Q := by
    intro y hy
    by_contra hyQ
    apply hy
    simp only [hQ, Set.mem_ofPred_eq, not_and_or, not_le] at hyQ
    rcases hyQ with h1 | h1
    · have h0 : φ (π y) = 0 := image_eq_zero_of_notMem_tsupport h1
      have hP : affinePullbackForm π (-(π 0)) α y = 0 := by
        ext m
        simp [affinePullbackForm, α, h0]
      show (K⁻¹ * f (π' y)) • affinePullbackForm π (-(π 0)) α y = 0
      rw [hP, smul_zero]
    · have h0 : f (π' y) = 0 := by
        rw [← Function.notMem_support, f.support_eq]
        simp only [mem_ball, dist_zero_right, not_lt]
        exact h1.le
      simp [ω₀, h0]
  have htsuppQ : tsupport ω₀ ⊆ Q := closure_minimal hsuppQ hQclosed
  have hQball : Q ⊆ ball 0 (R + 2 * h) := by
    rintro y ⟨hy1, hy2⟩
    have := hφs hy1
    rw [mem_ball, dist_zero_right] at this ⊢
    linarith [hnorm_le y]
  have hcpt : HasCompactSupport ω₀ :=
    (isCompact_closedBall (0 : Euclid (n + 1 + k)) (R + 2 * h)).of_isClosed_subset
      (isClosed_tsupport _) (htsuppQ.trans (hQball.trans ball_subset_closedBall))
  let ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n := ⟨ω₀, ⟨hω₀smooth, hcpt⟩, subset_univ _⟩
  refine ⟨ω, htsuppQ.trans hQball, ?_, ?_⟩
  · -- comass bound
    intro y
    change covectorEuclideanNorm (ω₀ y) ≤ 1
    have hM : ∀ I : Fin n → Fin (n + 1 + k),
        |ω₀ y (fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))| ≤
          K⁻¹ * (‖Θ‖ * ‖π‖ ^ n) := by
      intro I
      simp only [ω₀, ContinuousAlternatingMap.smul_apply, smul_eq_mul, affinePullbackForm,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      rw [abs_mul]
      have hζ : |K⁻¹ * f (π' y)| ≤ K⁻¹ := by
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 hKpos.le) f.nonneg)]
        exact mul_le_of_le_one_right (inv_nonneg.2 hKpos.le) f.le_one
      have hα : |α (-(π 0) + π y) (π ∘ fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))| ≤
          ‖Θ‖ * ‖π‖ ^ n := by
        rw [← Real.norm_eq_abs]
        calc _ ≤ ‖α (-(π 0) + π y)‖ *
              ∏ i, ‖(π ∘ fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i)) i‖ :=
              ContinuousAlternatingMap.le_opNorm _ _
          _ ≤ ‖Θ‖ * ∏ _i : Fin n, ‖π‖ := by
              gcongr with i
              · calc ‖Θ (φ (-(π 0) + π y))‖ ≤ ‖Θ‖ * ‖φ (-(π 0) + π y)‖ := Θ.le_opNorm _
                  _ ≤ ‖Θ‖ * 1 := by gcongr; exact hφn _
                  _ = ‖Θ‖ := mul_one _
              · calc ‖π (EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))‖
                    ≤ ‖π‖ * ‖EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i)‖ := π.le_opNorm _
                  _ = ‖π‖ := by simp
          _ = ‖Θ‖ * ‖π‖ ^ n := by simp
      exact mul_le_mul hζ hα (abs_nonneg _) (inv_nonneg.2 hKpos.le)
    have hsum : (∑ I : Fin n → Fin (n + 1 + k), if StrictMono I then
        (ω₀ y (fun i => EuclideanSpace.basisFun (Fin (n + 1 + k)) ℝ (I i))) ^ 2 else 0) ≤ 1 := by
      calc _ ≤ ∑ _I : Fin n → Fin (n + 1 + k), (K⁻¹ * (‖Θ‖ * ‖π‖ ^ n)) ^ 2 := by
            apply Finset.sum_le_sum
            intro I _
            split_ifs
            · exact sq_le_sq' (abs_le.1 (hM I)).1 (abs_le.1 (hM I)).2
            · positivity
        _ = (Real.sqrt N * (K⁻¹ * (‖Θ‖ * ‖π‖ ^ n))) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN, mul_pow (Real.sqrt N),
              Real.sq_sqrt (by positivity)]
        _ ≤ 1 ^ 2 := by
            gcongr
            rw [← mul_assoc, mul_comm (Real.sqrt N), mul_assoc, ← mul_assoc (Real.sqrt N),
              inv_mul_le_one₀ hKpos]
            linarith
        _ = 1 := one_pow 2
    unfold covectorEuclideanNorm
    calc _ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hsum
      _ = 1 := Real.sqrt_one
  · -- key identity
    intro g v hg hgv
    have hy₀ : π' (ι v + ι' (g v)) = g v := by simp [map_add, hπ'ι, hπ'ι']
    have hev : ω₀ =ᶠ[𝓝 (ι v + ι' (g v))] K⁻¹ • affinePullbackForm π (-(π 0)) α := by
      have hopen : IsOpen {y : Euclid (n + 1 + k) | ‖π' y‖ < h} :=
        isOpen_lt (continuous_norm.comp π'.continuous) continuous_const
      have hmem : ι v + ι' (g v) ∈ {y : Euclid (n + 1 + k) | ‖π' y‖ < h} := by
        simpa [hy₀] using hgv
      filter_upwards [hopen.mem_nhds hmem] with y hy
      have h1 : f (π' y) = 1 :=
        f.one_of_mem_closedBall (by simpa [mem_closedBall, dist_zero_right] using hy.le)
      simp [ω₀, h1]
    change exteriorDerivative ω₀ (ι v + ι' (g v)) _ = _
    rw [show exteriorDerivative ω₀ (ι v + ι' (g v)) =
        exteriorDerivative (K⁻¹ • affinePullbackForm π (-(π 0)) α) (ι v + ι' (g v)) from
        hev.extDeriv_eq, exteriorDerivative_smul]
    simp only [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    congr 1
    have h3 := Submission.dgcr_bwd_graph_pullback_extDeriv n k ι ι' g 0 α v hperp hαsmooth hg
    simp only [zero_add] at h3
    rw [h3]
    have hφd : DifferentiableAt ℝ φ v := (hφ.differentiable (by simp)).differentiableAt
    rw [exteriorDerivative_apply (hαsmooth.differentiable (by simp)).differentiableAt]
    have hfun : ∀ i : Fin (n + 1), (fun x => α x (i.removeNth
        (fun l : Fin (n + 1) => EuclideanSpace.single l (1 : ℝ)))) =
          fun x => (-1 : ℝ) ^ (i : ℕ) * φ x i := by
      intro i
      funext x
      exact hΘe (φ x) i
    simp only [hfun]
    have hder : ∀ i : Fin (n + 1), fderiv ℝ (fun x => (-1 : ℝ) ^ (i : ℕ) * φ x i) v
        (EuclideanSpace.single i (1 : ℝ)) =
          (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ φ v (EuclideanSpace.single i (1 : ℝ))) i := by
      intro i
      have hp : HasFDerivAt (fun x => φ x i)
          ((EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).comp (fderiv ℝ φ v)) v :=
        (EuclideanSpace.proj i : Euclid (n + 1) →L[ℝ] ℝ).hasFDerivAt.comp v hφd.hasFDerivAt
      rw [(hp.const_mul ((-1 : ℝ) ^ (i : ℕ))).fderiv]
      simp
    simp only [hder]
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (n + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
      EuclideanSpace.inner_single_left]
    rw [zsmul_eq_mul]
    push_cast
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

theorem Submission.codim1_zsl_fl_perimeter_bound : ∀ (n k : ℕ) (Us : ℕ → Set (Euclid (n + 1 + k))) (Ss : (i : ℕ) → GeometricCurrentOn (Us i) n) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (b : Euclid k) (gs : ℕ → Euclid (n + 1) → Euclid k) (Fs : ℕ → Set (Euclid (n + 1))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → (∀ i, MeasurableSet (Fs i)) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, DifferentiableAt ℝ (gs i) w) → (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in Fs i ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) ≤ c) → ∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ φ : Euclid (n + 1) → Euclid (n + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in Fs i, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ v).toLinearMap ≤ c := by
  intro n k Us Ss ι ι' b gs Fs hperp hspan hFs hH1 hH2 hH3 hH4 R hR
  -- Constants: `K` from the divergence lift, `h := ‖b‖ + 1`, `R₂ := R + 2h`, `c := K c₂`.
  obtain ⟨K, hK, hlift⟩ := Submission.codim1_zsl_fl_divergence_lift n k ι ι' hperp hspan
  set h : ℝ := ‖b‖ + 1 with hh
  have hhpos : 0 < h := by positivity
  set R₂ : ℝ := R + 2 * h with hR₂
  have hR₂pos : 0 < R₂ := by positivity
  obtain ⟨c₂, hc₂⟩ := hH4 R₂ hR₂pos
  refine ⟨K * c₂, ?_⟩
  -- (H1)–(H4) at radius `R₂` (with `ε = 1` in (H2)) hold simultaneously for all large `i`.
  filter_upwards [hH1 R₂ hR₂pos, hH2 R₂ 1 hR₂pos one_pos, hH3 R₂ hR₂pos, hc₂] with i hi1 hi2 hi3 hi4
  intro φ hφ hφc hφs hφn
  -- The lifted test form is admissible in (H4) and represented by (H3).
  obtain ⟨ω, hωs, hωn, hωd⟩ := hlift h R hhpos φ hφ hφc hφs hφn
  have hle := hi4 ω hωs hωn
  rw [hi3 ω hωs] at hle
  -- On `B_{R₂}`, `gs i` is differentiable with `‖gs i w‖ < h`, so the integrand is `K⁻¹ div φ`.
  have hcongr : ∫ w in Fs i ∩ ball 0 R₂, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n)
        (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w
          (EuclideanSpace.single j (1 : ℝ))) =
      ∫ w in Fs i ∩ ball 0 R₂, K⁻¹ * LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ w).toLinearMap := by
    apply setIntegral_congr_fun ((hFs i).inter measurableSet_ball)
    intro w hw
    apply hωd (gs i) w (hi1 w hw.2)
    have := (hi2 w hw.2).1
    calc ‖gs i w‖ = ‖(gs i w - b) + b‖ := by rw [sub_add_cancel]
      _ ≤ ‖gs i w - b‖ + ‖b‖ := norm_add_le _ _
      _ < 1 + ‖b‖ := by linarith
      _ = h := by ring
  rw [hcongr, integral_const_mul] at hle
  -- `div φ` vanishes off `tsupport φ ⊆ B_R ⊆ B_{R₂}`, so the ball can be dropped.
  have hdiv : ∫ w in Fs i ∩ ball 0 R₂, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ w).toLinearMap =
      ∫ w in Fs i, LinearMap.trace ℝ (Euclid (n + 1)) (fderiv ℝ φ w).toLinearMap := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hFs i) inter_subset_left ?_).symm
    intro w hw
    have hwnot : w ∉ tsupport φ := fun hmem =>
      hw.2 ⟨hw.1, ball_subset_ball (by linarith) (hφs hmem)⟩
    have h0 : fderiv ℝ φ w = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hwnot (tsupport_fderiv_subset ℝ hmem))
    simp [h0]
  rw [hdiv] at hle
  -- Multiply `K⁻¹ ∫_{Fs i} div φ ≤ c₂` by `K > 0`.
  have := mul_le_mul_of_nonneg_left hle hK.le
  rwa [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul] at this

/-- **Flat limit of the rescaled region boundaries** (Simon 7.5.3, 7.5.5; steps C1, D1, D5 and E3
of the supplied proof).  Let `Gᵢ(w) = ιw + ι'gᵢ(w)` with `gᵢ → b` in `C¹` on every ball (H1, H2),
`Sᵢ(ω) = ∫_{Fᵢ ∩ B_R} dω(Gᵢ)(DGᵢ e)` for `spt ω ⊆ B_R(0)` (H3), `Sᵢ` of locally bounded mass (H4),
and `Sᵢ ⇀ S`.  Then `S = ∂[[F]]` with `ξ_A = ιe₀ ∧ ⋯ ∧ ιeₙ` for a measurable `F` in the plane
`ι(ℝ^{n+1}) + ι'b`.  `codim1_zsl_fl_perimeter_bound` gives the local perimeter bounds of the `Fᵢ`,
`codim1_zsl_perimeter_compactness` a subsequence with `F_{σ i} → F'` in `L¹_loc`, and
`codim1_zsl_fl_graph_integral_tendsto` the limit `∫_{F' ∩ B_R} dω(G)(ιe)`, `G(w) = ιw + ι'b`, of
the integrals in (H3) along `σ`; with `Sᵢ ⇀ S` this is `S(ω)` when `spt ω ⊆ B_R(0)`.  As
`|G(w)| ≥ |w|`, the restriction to `B_R` can be dropped, and
`codim1_zsl_fl_isometry_image_setIntegral` moves the integral to `F := G(F')`. -/
theorem Submission.codim1_zsl_flat_graph_limit : ∀ (n k : ℕ) (Us : ℕ → Set (Euclid (n + 1 + k))) (Ss : (i : ℕ) → GeometricCurrentOn (Us i) n) (S : GeometricCurrentOn (univ : Set (Euclid (n + 1 + k))) n) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ξA : MultiVector (n + 1 + k) (n + 1)) (b : Euclid k) (gs : ℕ → Euclid (n + 1) → Euclid k) (Fs : ℕ → Set (Euclid (n + 1))), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ y : Euclid (n + 1 + k), ∃ v w, y = ι v + ι' w) → (∀ α : Covector (Euclid (n + 1 + k)) (n + 1), ξA α = α (fun j => ι (EuclideanSpace.single j (1 : ℝ)))) → ConvergesWeakly Ss S → (∀ i, MeasurableSet (Fs i)) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, DifferentiableAt ℝ (gs i) w) → (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ i in atTop, ∀ w ∈ ball (0 : Euclid (n + 1)) R, ‖gs i w - b‖ < ε ∧ ‖fderiv ℝ (gs i) w‖ < ε) → (∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in Fs i ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (gs i w)) (fun j => fderiv ℝ (fun w => ι w + ι' (gs i w)) w (EuclideanSpace.single j (1 : ℝ)))) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (n + 1 + k)) n) y) ≤ 1) → currentEval (Ss i) (ω : DifferentialForm (Euclid (n + 1 + k)) n) ≤ c) → ∃ F : Set (Euclid (n + 1 + k)), MeasurableSet F ∧ F ⊆ {y | ∃ w, y = ι w + ι' b} ∧ IsBoundaryOfRegion S F (fun _ => ξA) := by
  intro n k Us Ss S ι ι' ξA b gs Fs hperp hspan hξA hconv hFs hH1 hH2 hH3 hH4
  -- Part B: (H1)–(H4) give uniform local perimeter bounds for the `Fᵢ`.
  have hper := Submission.codim1_zsl_fl_perimeter_bound n k Us Ss ι ι' b gs Fs hperp hspan hFs
    hH1 hH2 hH3 hH4
  -- C1: BV compactness, `L^{n+1}((F_{σ i} Δ F') ∩ B_R) → 0` for every `R`.
  obtain ⟨σ, F', hσ, hF', hsymm⟩ := Submission.codim1_zsl_perimeter_compactness (n + 1) Fs hFs hper
  -- E1–E2: `F := G(F')` is measurable and `∫_F f dH^{n+1} = ∫_{F'} f ∘ G`.
  obtain ⟨hFmeas, htrans⟩ :=
    Submission.codim1_zsl_fl_isometry_image_setIntegral (n + 1) (n + 1 + k) ι (ι' b) F' hF'
  refine ⟨(fun w => ι w + ι' b) '' F', hFmeas, ?_, ?_⟩
  · rintro y ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  · intro ω
    -- D1: `dω` is a test form, and `spt ω ⊆ B_R(0)` for some `R > 0`.
    have hωtest : IsTestForm (ω : DifferentialForm (Euclid (n + 1 + k)) n) := ω.property.1
    have hdω := exteriorDerivative_isTestForm hωtest
    obtain ⟨R, hRpos, hR⟩ :=
      hωtest.2.isCompact.isBounded.subset_ball_lt 0 (0 : Euclid (n + 1 + k))
    -- D2–D4: along `σ` the graph integrals tend to the integral over the flat graph `G`.
    have hσt : Tendsto σ atTop atTop := hσ.tendsto_atTop
    have hlim := Submission.codim1_zsl_fl_graph_integral_tendsto (n + 1) k (n + 1 + k) ι ι' b R
      (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n)) (fun i => gs (σ i))
      (fun i => Fs (σ i)) F' hdω.1.continuous hdω.2 (fun i => hFs (σ i)) hF' (hsymm R)
      (hσt.eventually (hH1 R hRpos)) (fun ε hε => hσt.eventually (hH2 R ε hRpos hε))
    -- D5: by (H3) these integrals are eventually `S_{σ i}(ω)`, and `S_{σ i}(ω) → S(ω)`.
    have heq : (fun i => currentEval (Ss (σ i)) (ω : DifferentialForm (Euclid (n + 1 + k)) n))
        =ᶠ[atTop] fun i => ∫ w in Fs (σ i) ∩ ball 0 R,
          exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (gs (σ i) w))
            (fun j => fderiv ℝ (fun w => ι w + ι' (gs (σ i) w)) w
              (EuclideanSpace.single j (1 : ℝ))) := by
      filter_upwards [hσt.eventually (hH3 R hRpos)] with i hi
      exact hi ω hR
    have hS := tendsto_nhds_unique (((hconv ω).comp hσt).congr' heq) hlim
    -- E3: move the integral to `F = G(F')` and use `ξ_A(α) = α(ιe)`.
    rw [hS, htrans]
    simp only [hξA]
    symm
    -- `dω(G(w)) = 0` for `|w| ≥ R`, since `|G(w)|² = |w|² + |b|²` and `spt dω ⊆ B_R(0)`.
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hF' inter_subset_left
    rintro w ⟨hwF, hwB⟩
    have hwB' : R ≤ ‖w‖ := by
      by_contra hlt
      exact hwB ⟨hwF, by simpa using (not_le.1 hlt)⟩
    have hnorm : ‖w‖ ≤ ‖ι w + ι' b‖ := by
      have h2 : ‖ι w + ι' b‖ ^ 2 = ‖w‖ ^ 2 + ‖b‖ ^ 2 := by
        rw [norm_add_sq_real, hperp, LinearIsometry.norm_map, LinearIsometry.norm_map]
        ring
      nlinarith [norm_nonneg w, norm_nonneg (ι w + ι' b), sq_nonneg ‖b‖]
    have hnot : ι w + ι' b ∉
        tsupport (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n)) := by
      intro hmem
      have := hR (tsupport_exteriorDerivative_subset _ hmem)
      rw [mem_ball, dist_zero_right] at this
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot]
    rfl

end GMT.Ch07
