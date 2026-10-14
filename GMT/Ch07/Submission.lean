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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
