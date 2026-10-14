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

/-- The affine homotopy `h(t, x) = f(x) + t (g(x) − f(x))` from `f` to `g` (Simon 6.2.26, p. 140)
for smooth `f, g : ℝᴺ → ℝᴺ'`, with `(t, x) ∈ ℝ^{N+1}` written `ι(t, x)`, and the derivative facts
used for 2.27: `h` is `C^∞`, `dh_{ι(t,x)} e₀ = g(x) − f(x)`,
`dh_{ι(t,x)} ι(0, v) = df_x v + t (dg_x v − df_x v)` and
`‖dh_{ι(t,x)}‖ ≤ |g(x) − f(x)| + ‖df_x‖ + |t| (‖dg_x‖ + ‖df_x‖)`.  With `tl y = (y₁, …, y_N)` and
`hd y = y₀`, both continuous linear with `‖tl w‖, |hd w| ≤ ‖w‖`, `h = f ∘ tl + hd • (g ∘ tl − f ∘ tl)`
and the chain and product rules give
`dh_y w = df_{tl y} (tl w) + hd y (dg_{tl y} (tl w) − df_{tl y} (tl w)) + hd w (g(tl y) − f(tl y))`. -/
theorem Submission.cmcdt_lpoh_interp_calculus : ∀ (N N' : ℕ) (f g : Euclid N → Euclid N'), ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) g → ∃ h : Euclid (N + 1) → Euclid N', ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ (t : ℝ) (x : Euclid N), h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = f x + t • (g x - f x)) ∧ (∀ (t : ℝ) (x : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) = g x - f x) ∧ (∀ (t : ℝ) (x v : Euclid N), fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ f x v + t • (fderiv ℝ g x v - fderiv ℝ f x v)) ∧ ∀ (t : ℝ) (x : Euclid N), ‖fderiv ℝ h (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ ‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖) := by
  intro N N' f g hf hg
  -- the coordinate maps `tl y = (y₁, …, y_N)` and `hd y = y₀`
  let tlL : Euclid (N + 1) →ₗ[ℝ] Euclid N :=
    { toFun := fun y => WithLp.toLp 2 (Fin.tail (WithLp.ofLp y))
      map_add' := by intro y z; rfl
      map_smul' := by intro r y; rfl }
  let tl : Euclid (N + 1) →L[ℝ] Euclid N := LinearMap.toContinuousLinearMap tlL
  let hd : Euclid (N + 1) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (N + 1))
  have htl : ∀ y, tl y = WithLp.toLp 2 (Fin.tail (WithLp.ofLp y)) := fun y => rfl
  have hhd : ∀ y : Euclid (N + 1), hd y = WithLp.ofLp y 0 := fun y => rfl
  have htlι : ∀ (t : ℝ) (x : Euclid N), tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = x := by
    intro t x; rw [htl]; simp
  have hhdι : ∀ (t : ℝ) (x : Euclid N), hd (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = t := by
    intro t x; rw [hhd]; simp
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  set h : Euclid (N + 1) → Euclid N' := fun y => f (tl y) + hd y • (g (tl y) - f (tl y)) with hh
  -- `dh_y = df_{tl y} ∘ tl + hd y • (dg_{tl y} ∘ tl − df_{tl y} ∘ tl) + hd ⊗ (g(tl y) − f(tl y))`
  have hderiv : ∀ y, HasFDerivAt h ((fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y)))) y := by
    intro y
    have h1 : HasFDerivAt (fun y => f (tl y)) ((fderiv ℝ f (tl y)).comp tl) y :=
      (hfd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    have h2 : HasFDerivAt (fun y => g (tl y)) ((fderiv ℝ g (tl y)).comp tl) y :=
      (hgd (tl y)).hasFDerivAt.comp y tl.hasFDerivAt
    exact h1.add (hd.hasFDerivAt.smul (h2.sub h1))
  have hfd' : ∀ y, fderiv ℝ h y = (fderiv ℝ f (tl y)).comp tl +
      (hd y • ((fderiv ℝ g (tl y)).comp tl - (fderiv ℝ f (tl y)).comp tl) +
        hd.smulRight (g (tl y) - f (tl y))) := fun y => (hderiv y).fderiv
  have htle : tl (EuclideanSpace.single 0 1) = 0 := by
    rw [htl]; ext i; simp [Fin.tail]
  have hhde : hd (EuclideanSpace.single 0 1 : Euclid (N + 1)) = 1 := by
    rw [hhd]; simp
  have htlJ : ∀ v : Euclid N, tl (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = v := fun v => htlι 0 v
  have hhdJ : ∀ v : Euclid N, hd (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = 0 := fun v => hhdι 0 v
  -- `‖tl w‖ ≤ ‖w‖` and `|hd w| ≤ ‖w‖`
  have htln : ∀ w : Euclid (N + 1), ‖tl w‖ ≤ ‖w‖ := by
    intro w
    rw [htl, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    rw [Fin.sum_univ_succ]
    simp only [Fin.tail]
    have : 0 ≤ ‖WithLp.ofLp w 0‖ ^ 2 := by positivity
    linarith
  have hhdn : ∀ w : Euclid (N + 1), |hd w| ≤ ‖w‖ := by
    intro w
    rw [hhd, ← Real.norm_eq_abs]
    exact PiLp.norm_apply_le w 0
  refine ⟨h, (hf.comp tl.contDiff).add (hd.contDiff.smul ((hg.comp tl.contDiff).sub (hf.comp tl.contDiff))),
    ?_, ?_, ?_, ?_⟩
  · intro t x
    simp only [hh, htlι, hhdι]
  · intro t x
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htle, hhde, map_zero, sub_self, smul_zero, zero_add, one_smul,
      htlι]
  · intro t x v
    rw [hfd']
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlJ, hhdJ, zero_smul, add_zero, htlι, hhdι]
  · intro t x
    rw [hfd']
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    simp only [_root_.add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      _root_.smul_apply, _root_.sub_apply,
      ContinuousLinearMap.smulRight_apply, htlι, hhdι]
    have e1 : ‖fderiv ℝ f x (tl w)‖ ≤ ‖fderiv ℝ f x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e2 : ‖fderiv ℝ g x (tl w)‖ ≤ ‖fderiv ℝ g x‖ * ‖w‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact htln w)
    have e3 : ‖hd w • (g x - f x)‖ ≤ ‖g x - f x‖ * ‖w‖ := by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      gcongr
      exact hhdn w
    calc ‖fderiv ℝ f x (tl w) + (t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w)) + hd w • (g x - f x))‖
        ≤ ‖fderiv ℝ f x (tl w)‖ + (‖t • (fderiv ℝ g x (tl w) - fderiv ℝ f x (tl w))‖ + ‖hd w • (g x - f x)‖) :=
          (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ‖fderiv ℝ f x‖ * ‖w‖ + (|t| * (‖fderiv ℝ g x‖ * ‖w‖ + ‖fderiv ℝ f x‖ * ‖w‖) + ‖g x - f x‖ * ‖w‖) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add e2 e1)
      _ = (‖g x - f x‖ + ‖fderiv ℝ f x‖ + |t| * (‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖)) * ‖w‖ := by ring
/-- **Mollification of Lipschitz maps**: a `Λ`-Lipschitz `F : ℝᴺ → ℝᴺ'` has `C^∞`,
`Λ`-Lipschitz approximants `Fⱼ` with `|Fⱼ − F| ≤ Λ/(j + 1)`.  For `σ > 0` normalize the bump `b`
of a `ContDiffBump` at `0` with `rOut = σ` to `ϕ = b/∫b` (`∫b > 0` as `volume (B_σ(0)) > 0`), so
`ϕ ≥ 0`, `∫ϕ = 1` and `support ϕ ⊆ B_σ(0)`, and put `G = ϕ ⋆ F`.  Then `G` is `C^∞`,
`G x − G y = ∫ ϕ(t)(F(x − t) − F(y − t)) dt` gives the constant `Λ`, and `|G − F| ≤ Λσ` since
`|F y − F x| ≤ Λσ` on `B_σ(x)`.  Take `σ = 1/(j + 1)`. -/
theorem Submission.cmcdt_lpo_mollify_lipschitz : ∀ (N N' : ℕ) (Λ : NNReal) (F : Euclid N → Euclid N'), LipschitzWith Λ F → ∃ Fs : ℕ → Euclid N → Euclid N', (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, LipschitzWith Λ (Fs j)) ∧ ∀ (j : ℕ) (x : Euclid N), dist (Fs j x) (F x) ≤ (Λ : ℝ) / ((j : ℝ) + 1) := by
  intro N N' Λ F hF
  -- For each `σ > 0`: a `C^∞`, `Λ`-Lipschitz `G` with `|G − F| ≤ Λσ`
  have key : ∀ σ : ℝ, 0 < σ → ∃ G : Euclid N → Euclid N', ContDiff ℝ (⊤ : ℕ∞) G ∧
      LipschitzWith Λ G ∧ ∀ x, dist (G x) (F x) ≤ (Λ : ℝ) * σ := by
    intro σ hσ
    -- Step 1: the bump `b`: `C^∞`, `b ≥ 0`, `support b = B_σ(0)`, compact support
    let b : ContDiffBump (0 : Euclid N) := ⟨σ / 2, σ, half_pos hσ, half_lt_self hσ⟩
    have hbi : Integrable (b : Euclid N → ℝ) :=
      b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    -- Step 2: `∫ b > 0`, and the normalized bump `ϕ = (∫ b)⁻¹ b`
    have hIpos : 0 < ∫ t, b t := by
      rw [integral_pos_iff_support_of_nonneg (fun t => b.nonneg) hbi, b.support_eq]
      exact measure_ball_pos _ _ hσ
    set ϕ : Euclid N → ℝ := fun t => (∫ s, b s)⁻¹ * b t with hϕ
    have hϕd : ContDiff ℝ (⊤ : ℕ∞) ϕ := contDiff_const.mul b.contDiff
    have hϕs : HasCompactSupport ϕ := b.hasCompactSupport.mul_left
    have hϕn : ∀ t, 0 ≤ ϕ t := fun t => mul_nonneg (inv_nonneg.2 hIpos.le) b.nonneg
    have hϕ1 : ∫ t, ϕ t = 1 := by
      rw [hϕ, integral_const_mul]
      exact inv_mul_cancel₀ hIpos.ne'
    have hϕb : support ϕ ⊆ ball 0 σ := by
      intro t ht
      have : t ∈ support (b : Euclid N → ℝ) := Function.support_mul_subset_right _ _ ht
      rwa [b.support_eq] at this
    have hϕi : Integrable ϕ := hϕd.continuous.integrable_of_hasCompactSupport hϕs
    -- Step 3: `G = ϕ ⋆ F` is `C^∞`; its integrands `t ↦ ϕ t • F (x - t)` are integrable
    have hFc : Continuous F := hF.continuous
    have hex : ∀ x, Integrable (fun t => ϕ t • F (x - t)) := by
      intro x
      have := (hϕs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hϕd.continuous
        hFc.locallyIntegrable (μ := volume)) x
      simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply] using this
    refine ⟨convolution ϕ F (ContinuousLinearMap.lsmul ℝ ℝ) volume, ?_, ?_, ?_⟩
    · exact hϕs.contDiff_convolution_left _ hϕd hFc.locallyIntegrable
    -- Step 4: `‖G x − G y‖ ≤ ∫ ϕ(t) Λ‖x − y‖ dt = Λ‖x − y‖`
    · refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [convolution_def, ContinuousLinearMap.lsmul_apply]
      rw [dist_eq_norm, ← integral_sub (hex x) (hex y)]
      calc ‖∫ t, (ϕ t • F (x - t) - ϕ t • F (y - t))‖
          ≤ ∫ t, ϕ t * ((Λ : ℝ) * dist x y) := by
            refine norm_integral_le_of_norm_le (hϕi.mul_const _) (Eventually.of_forall fun t => ?_)
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hϕn t), ← dist_eq_norm]
            refine mul_le_mul_of_nonneg_left ?_ (hϕn t)
            calc dist (F (x - t)) (F (y - t)) ≤ (Λ : ℝ) * dist (x - t) (y - t) :=
                  hF.dist_le_mul _ _
              _ = (Λ : ℝ) * dist x y := by rw [dist_sub_right]
        _ = (Λ : ℝ) * dist x y := by rw [integral_mul_const, hϕ1, one_mul]
    -- Step 5: `|F y − F x| ≤ Λσ` on `B_σ(x)`, so `|G x − F x| ≤ Λσ` (`ϕ ≥ 0`, `∫ϕ = 1`)
    · intro x
      refine dist_convolution_le (by positivity) hϕb hϕn hϕ1 hFc.aestronglyMeasurable
        fun y hy => ?_
      calc dist (F y) (F x) ≤ (Λ : ℝ) * dist y x := hF.dist_le_mul _ _
        _ ≤ (Λ : ℝ) * σ := mul_le_mul_of_nonneg_left (mem_ball.1 hy).le Λ.coe_nonneg
  -- Step 6: `σ = 1/(j + 1)`
  choose G hG using fun j : ℕ => key (1 / ((j : ℝ) + 1)) (by positivity)
  refine ⟨G, fun j => (hG j).1, fun j => (hG j).2.1, fun j x => ?_⟩
  calc dist (G j x) (F x) ≤ (Λ : ℝ) * (1 / ((j : ℝ) + 1)) := (hG j).2.2 x
    _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring

/-- **Smooth approximation of a Lipschitz straight-line homotopy**: for `Λ`-Lipschitz
`F, G : ℝᴺ → ℝᴺ'` and `H(t, x) = F x + t(G x − F x)` on `[0, 1] × K` (`K` compact), take the
mollifications `Fⱼ, Gⱼ` of `F, G` (`|Fⱼ − F|, |Gⱼ − G| ≤ Λ/(j + 1)`, so `|DFⱼ|, |DGⱼ| ≤ Λ`) and
let `Hⱼ` be the `C^∞` interpolation `Hⱼ(t, x) = Fⱼ x + t(Gⱼ x − Fⱼ x)`.  Then
`|∂ₜHⱼ| = |Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`, `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` for
`t ∈ [0, 1]`, `|DHⱼ| ≤ sup_K |F − G| + 5Λ` on `[0, 1] × K`, and `Hⱼ → H` uniformly on
`[0, 1] × K` as `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` there. -/
theorem Submission.cmcdt_lpoh_smooth_approx : ∀ (N N' : ℕ) (Λ : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)), LipschitzWith Λ F → LipschitzWith Λ G → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (Fs Gs : ℕ → Euclid N → Euclid N') (Hs : ℕ → Euclid (N + 1) → Euclid N') (Λ' : ℝ), (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Gs j)) ∧ (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Hs j)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ)) ∧ (∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ)) ∧ TendstoUniformly Fs F atTop ∧ TendstoUniformly Gs G atTop ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) = Gs j x) ∧ (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) = Fs j x) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Gs j) x v) ∧ (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Fs j) x v) ∧ (∀ (j : ℕ) (t : ℝ) (x : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1)) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ (x v : Euclid N), ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖) ∧ (∀ (j : ℕ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, ‖fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))‖ ≤ Λ') ∧ TendstoUniformlyOn Hs H atTop {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
  intro N N' Λ F G H K hF hG hK hHK
  -- Step 1: mollify `F, G`; for each `j` interpolate `Fⱼ, Gⱼ` by the `C^∞` map `Hⱼ`
  obtain ⟨Fs, hFs, hFL, hFd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ F hF
  obtain ⟨Gs, hGs, hGL, hGd⟩ := Submission.cmcdt_lpo_mollify_lipschitz N N' Λ G hG
  choose Hs hHs hHι hHe hHJ hHn using
    fun j => Submission.cmcdt_lpoh_interp_calculus N N' (Fs j) (Gs j) (hFs j) (hGs j)
  -- `M` bounds `|F − G|` on the compact `K`
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ K, dist (F x) (G x) ≤ M := by
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
      ((hF.continuous.dist hG.continuous).continuousOn)
    exact ⟨M, fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM x hx)⟩
  -- Step 2: `Λ`-Lipschitz maps have `|DFⱼ|, |DGⱼ| ≤ Λ`
  have hDF : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Fs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hFL j)
  have hDG : ∀ (j : ℕ) (x : Euclid N), ‖fderiv ℝ (Gs j) x‖ ≤ (Λ : ℝ) :=
    fun j x => norm_fderiv_le_of_lipschitz ℝ (hGL j)
  -- Step 3: `Λ/(j + 1) → 0`, so a uniform error `Λ/(j + 1)` gives uniform convergence
  have hsmall : Tendsto (fun j : ℕ => (Λ : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Λ : ℝ)
    rw [mul_zero] at h
    refine h.congr (fun j => ?_)
    rw [mul_one_div]
  have hunif : ∀ (Es : ℕ → Euclid N → Euclid N') (E : Euclid N → Euclid N'),
      (∀ (j : ℕ) (x : Euclid N), dist (Es j x) (E x) ≤ (Λ : ℝ) / ((j : ℝ) + 1)) →
      TendstoUniformly Es E atTop := by
    intro Es E hE
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj x
    rw [dist_comm]
    exact (hE j x).trans_lt hj
  -- Step 6: `|Gⱼ − Fⱼ| ≤ |F − G| + 2Λ/(j + 1)`
  have hGF : ∀ (j : ℕ) (x : Euclid N),
      ‖Gs j x - Fs j x‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by
    intro j x
    rw [← dist_eq_norm]
    calc dist (Gs j x) (Fs j x) ≤ dist (Gs j x) (G x) + dist (G x) (F x) + dist (F x) (Fs j x) :=
          dist_triangle4 _ _ _ _
      _ ≤ (Λ : ℝ) / ((j : ℝ) + 1) + dist (F x) (G x) + (Λ : ℝ) / ((j : ℝ) + 1) := by
          gcongr
          · exact hGd j x
          · rw [dist_comm]
          · rw [dist_comm]; exact hFd j x
      _ = dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) := by ring
  refine ⟨Fs, Gs, Hs, M + 5 * (Λ : ℝ), hFs, hGs, hHs, hDF, hDG, hunif Fs F hFd, hunif Gs G hGd,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- Steps 4, 5: end values and end derivatives at `t = 1, 0`
  · intro j x; rw [hHι]; simp
  · intro j x; rw [hHι]; simp
  · intro j x v; rw [hHJ]; simp
  · intro j x v; rw [hHJ]; simp
  -- Step 7: `DHⱼ e₀ = Gⱼ − Fⱼ`
  · intro j t x; rw [hHe]; exact hGF j x
  -- Step 8: `DHⱼ(Jv) = (1 − t) DFⱼ v + t DGⱼ v` has norm `≤ Λ|v|` for `t ∈ [0, 1]`
  · intro j t ht x v
    rw [hHJ]
    have h1 : fderiv ℝ (Fs j) x v + t • (fderiv ℝ (Gs j) x v - fderiv ℝ (Fs j) x v) =
        (1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have hF' : ‖fderiv ℝ (Fs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDF j x)
    have hG' : ‖fderiv ℝ (Gs j) x v‖ ≤ (Λ : ℝ) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hDG j x)
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • fderiv ℝ (Fs j) x v + t • fderiv ℝ (Gs j) x v‖
        ≤ ‖(1 - t) • fderiv ℝ (Fs j) x v‖ + ‖t • fderiv ℝ (Gs j) x v‖ := norm_add_le _ _
      _ = (1 - t) * ‖fderiv ℝ (Fs j) x v‖ + t * ‖fderiv ℝ (Gs j) x v‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) * ‖v‖) + t * ((Λ : ℝ) * ‖v‖) := by gcongr
      _ = (Λ : ℝ) * ‖v‖ := by ring
  -- Step 9: `|DHⱼ| ≤ (M + 2Λ) + Λ + 1 · (Λ + Λ) = M + 5Λ` on `[0, 1] × K`
  · intro j t ht x hx
    refine (hHn j t x).trans ?_
    have h2 : 2 * (Λ : ℝ) / ((j : ℝ) + 1) ≤ 2 * (Λ : ℝ) :=
      div_le_self (by positivity) (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])
    have habs : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    calc ‖Gs j x - Fs j x‖ + ‖fderiv ℝ (Fs j) x‖ + |t| * (‖fderiv ℝ (Gs j) x‖ + ‖fderiv ℝ (Fs j) x‖)
        ≤ (M + 2 * (Λ : ℝ)) + (Λ : ℝ) + 1 * ((Λ : ℝ) + (Λ : ℝ)) := by
          gcongr
          · exact (hGF j x).trans (by linarith [hM x hx])
          · exact hDF j x
          · exact hDG j x
          · exact hDF j x
      _ = M + 5 * (Λ : ℝ) := by ring
  -- Step 10: `H − Hⱼ = (1 − t)(F − Fⱼ) + t(G − Gⱼ)` has norm `≤ Λ/(j + 1)` on `[0, 1] × K`
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with j hj y hy
    obtain ⟨t, ht, x, hx, rfl⟩ := hy
    rw [hHK x hx t ht, hHι, dist_eq_norm]
    have h1 : F x + t • (G x - F x) - (Fs j x + t • (Gs j x - Fs j x)) =
        (1 - t) • (F x - Fs j x) + t • (G x - Gs j x) := by
      simp only [smul_sub, sub_smul, one_smul]; abel
    rw [h1]
    have ht0 : 0 ≤ t := ht.1
    have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
    calc ‖(1 - t) • (F x - Fs j x) + t • (G x - Gs j x)‖
        ≤ ‖(1 - t) • (F x - Fs j x)‖ + ‖t • (G x - Gs j x)‖ := norm_add_le _ _
      _ = (1 - t) * ‖F x - Fs j x‖ + t * ‖G x - Gs j x‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ht1, Real.norm_of_nonneg ht0]
      _ ≤ (1 - t) * ((Λ : ℝ) / ((j : ℝ) + 1)) + t * ((Λ : ℝ) / ((j : ℝ) + 1)) := by
          gcongr
          · rw [← dist_eq_norm, dist_comm]; exact hFd j x
          · rw [← dist_eq_norm, dist_comm]; exact hGd j x
      _ = (Λ : ℝ) / ((j : ℝ) + 1) := by ring
      _ < ε := hj
/-- Coordinates for the products `[[(0,1)]] × T` and `{p} × T` (Simon 6.2.17, 6.2.21–2.22),
`ℝ × ℝᴺ ≅ ℝᴺ⁺¹`, `(t, x) ↦ (t, x₁, …, x_N)`: the composite of `id × ofLp`, `Fin.consLinearEquiv`
and `toLp` is a linear equivalence, continuous in finite dimension, with `L(1, 0) = e₀` and
`‖L(0, x)‖ = ‖x‖`. -/
theorem Submission.cmcdt_lpo_slice_coords : ∀ N : ℕ, ∃ L : (ℝ × Euclid N) ≃L[ℝ] Euclid (N + 1), (∀ (t : ℝ) (x : Euclid N), L (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) ∧ L (1, 0) = EuclideanSpace.single 0 1 ∧ ∀ x : Euclid N, ‖L (0, x)‖ = ‖x‖ := by
  intro N
  -- `(t, x) ↦ (t, ofLp x) ↦ Fin.cons t (ofLp x) ↦ toLp 2 (Fin.cons t (ofLp x))`
  let e : (ℝ × Euclid N) ≃ₗ[ℝ] Euclid (N + 1) :=
    ((LinearEquiv.refl ℝ ℝ).prodCongr (WithLp.linearEquiv 2 ℝ (Fin N → ℝ))).trans
      ((Fin.consLinearEquiv ℝ (fun _ : Fin (N + 1) => ℝ)).trans
        (WithLp.linearEquiv 2 ℝ (Fin (N + 1) → ℝ)).symm)
  -- `e` is continuous in finite dimension; (i) holds by unfolding the three maps
  have hL : ∀ (t : ℝ) (x : Euclid N),
      e.toContinuousLinearEquiv (t, x) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) :=
    fun _ _ => rfl
  refine ⟨e.toContinuousLinearEquiv, hL, ?_, fun x => ?_⟩
  · -- (ii): compare coordinates, splitting the index into `0` and `j.succ`
    rw [hL]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Fin.succ_ne_zero]
  · -- (iii): `‖L (0, x)‖² = ‖0‖² + ∑ⱼ ‖xⱼ‖² = ‖x‖²`
    rw [hL, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq x, Fin.sum_univ_succ]
    simp
/-- Smoothness of parametric integrals over `[0, 1]`, used for the slice form of `[[0, 1]] × T`
(Simon 6.2.17–2.22).  If `h : ℝ × ℝᴺ → V` is `C^∞`, then `x ↦ ∫₀¹ h(t, x) dt` is `C^∞` and its
derivative at `x` is `∫₀¹ D[x' ↦ h(t, x')](x) dt`.  The derivative formula is differentiation under
the integral sign, with the partial derivative bounded on `[0, 1] × closedBall x 1`; `C^n` follows
by induction on `n` over all value spaces, the derivative being a parametric integral of the
`C^∞` map `(t, x) ↦ D[x' ↦ h(t, x')](x)` with values in `L(ℝᴺ, V)`. -/
theorem Submission.cmcdt_lpo_slice_param_integral : ∀ (N : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (h : ℝ × Euclid N → V), ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ (⊤ : ℕ∞) (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) ∧ ∀ x : Euclid N, HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x')) (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x) x := by
  intro N
  -- Steps 1–2: `x' ↦ h (t, x')` has derivative `(fderiv ℝ h (t, x)).comp inr` at `x`, so the
  -- partial derivative `h₁ p = fderiv ℝ (fun x' => h (p.1, x')) p.2` is `C^∞` in `p`.
  have hsmooth : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h →
        ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) := by
    intro V _ _ h hh
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ h) := (contDiff_infty_iff_fderiv.1 hh).2
    have hpart : (fun p : ℝ × Euclid N => fderiv ℝ (fun x' : Euclid N => h (p.1, x')) p.2) =
        fun p => (fderiv ℝ h p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)) := by
      funext p
      exact (((contDiff_infty_iff_fderiv.1 hh).1 p).hasFDerivAt.comp p.2
        (hasFDerivAt_prodMk_right p.1 p.2)).fderiv
    rw [hpart]
    exact hd.clm_comp contDiff_const
  -- Step 3: differentiation under the integral sign, with a uniform bound on the partial
  -- derivative over the compact set `[0, 1] × closedBall x₀ 1`.
  have hderiv : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ∀ x₀ : Euclid N,
        HasFDerivAt (fun x' : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x'))
          (∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x₀) x₀ := by
    intro V _ _ h hh x₀
    have hdiff : Differentiable ℝ h := (contDiff_infty_iff_fderiv.1 hh).1
    have hc : Continuous h := hh.continuous
    have h₁c := (hsmooth V h hh).continuous
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall x₀ 1)).exists_bound_of_continuousOn
      h₁c.continuousOn
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun x t => h (t, x)) (F' := fun x t => fderiv ℝ (fun x' : Euclid N => h (t, x')) x)
      (bound := fun _ => B) (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x =>
        (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (h₁c.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · refine (ae_restrict_mem measurableSet_uIoc).mono fun t ht x hx => ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact hB (t, x) (Set.mk_mem_prod (Ioc_subset_Icc_self ht) (ball_subset_closedBall hx))
    · exact Eventually.of_forall fun t x _ =>
        ((hdiff (t, x)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).differentiableAt.hasFDerivAt
  -- Step 4: `C^n` for every `n`, by induction over all value spaces at once.
  have hind : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ × Euclid N → V),
      ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ n (fun x : Euclid N => ∫ t in (0 : ℝ)..1, h (t, x)) := by
    intro n
    induction n with
    | zero =>
      intro V _ _ h hh
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun x => (hderiv V h hh x).continuousAt
    | succ n ih =>
      intro V _ _ h hh
      rw [Nat.cast_add_one, contDiff_succ_iff_hasFDerivAt]
      exact ⟨fun x => ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => h (t, x')) x,
        ih (Euclid N →L[ℝ] V) _ (hsmooth V h hh), hderiv V h hh⟩
  -- Step 5.
  intro V _ _ _ h hh
  exact ⟨contDiff_infty.2 fun n => hind n V h hh, hderiv V h hh⟩

/-- **Coordinate splitting of `dβ` along `ℝ × ℝᴺ`** (pointwise form of Simon 6.2.17–2.21,
`∂([[0,1]] × T) = {1} × T − {0} × T − [[0,1]] × ∂T`).  Write `ι(s, y) = (s, y)`, `Jy = ι(0, y)` and
`e₀ = ι(1, 0)`; by `cmcdt_lpo_slice_coords`, `ι = L` for a continuous linear equivalence `L`.
Expand `dβ(ι(t, x))(e₀, Jv₀, …, Jvₖ) = Σᵢ (−1)ⁱ D[y ↦ β(y)(Ŵᵢ)](ι(t, x))(Wᵢ)` by
`exteriorDerivative_apply`, where `W = (e₀, Jv₀, …, Jvₖ)` and `Ŵᵢ` omits `Wᵢ`, and split off
`i = 0`.  As `y ↦ β(y)(u)` has derivative `m ↦ Dβ(y)(m)(u)`, the chain rule along `s ↦ ι(s, x)`
(derivative `e₀`) turns the `0`-th term into `d/ds|_{s=t} β(ι(s, x))(Jv)`.  For `i = j + 1`,
`Ŵᵢ = (e₀, J(removeNth j v))` and `Wᵢ = Jvⱼ`, and the chain rule along `x' ↦ ι(t, x')` (derivative
`J`) together with `(−1)^{j+1} = −(−1)^j` turns the term into
`−(−1)^j D[x' ↦ β(ι(t, x'))(e₀, J(removeNth j v))](x)(vⱼ)`. -/
theorem Submission.cmcdt_lpo_slice_extDeriv_split : ∀ (N k : ℕ) (β : DifferentialForm (Euclid (N + 1)) (k + 1)), Differentiable ℝ β → ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), exteriorDerivative β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = deriv (fun s : ℝ => β (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) t - ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) • fderiv ℝ (fun x' : Euclid N => β (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) := by
  intro N k β hβ t x v
  -- Step 1: the coordinate map `ι(s, y)` is `L (s, y)`, and `e₀ = L (1, 0)` (sibling `coords`)
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  simp only [← hL, ← hL1]
  -- Step 2: `y ↦ β y u` has derivative `m ↦ Dβ(y)(m)(u)`
  have hβu : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid (N + 1)),
      HasFDerivAt (fun z => β z u) (fderiv ℝ (fun z => β z u) y) y := fun u y =>
    ((hβ y).continuousAlternatingMap_apply_const u).hasFDerivAt
  -- Step 3: derivatives of the coordinate paths `s ↦ L (s, x)` and `x' ↦ L (t, x')`
  have hpath₁ : HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) t :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have hpath₂ : HasFDerivAt (fun x' : Euclid N => L (t, x'))
      ((L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))) x :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  have hslice : ∀ (u : Fin (k + 1) → Euclid (N + 1)) (y : Euclid N),
      fderiv ℝ (fun x' : Euclid N => β (L (t, x')) u) x y =
        fderiv ℝ (fun z => β z u) (L (t, x)) (L (0, y)) := by
    intro u y
    have h := (hβu u (L (t, x))).comp x hpath₂
    simp only [Function.comp_def] at h
    rw [h.fderiv]
    rfl
  -- Step 4: expand `dβ` and split off the index `0`
  rw [exteriorDerivative_apply (hβ _), Fin.sum_univ_succ, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · -- Step 5: the `0`-th term is `deriv φ t`, `φ s = β (L (s, x)) (Jv)`
    have h := (hβu (fun i => L (0, v i)) (L (t, x))).comp_hasDerivAt t hpath₁
    simp only [Function.comp_def] at h
    rw [h.deriv, Fin.val_zero, pow_zero, one_smul, Fin.removeNth_zero, Fin.tail_cons,
      Fin.cons_zero]
  · -- Step 6: the `(j + 1)`-st term, with `Ŵ = (e₀, J(removeNth j v))` and sign `−(−1)^j`
    refine Finset.sum_congr rfl fun j _ => ?_
    have hrem : Fin.removeNth j.succ
        (Fin.cons (L (1, 0)) (fun i => L (0, v i)) : Fin (k + 1 + 1) → Euclid (N + 1)) =
        Fin.cons (L (1, 0)) (fun i => L (0, Fin.removeNth j v i)) :=
      Fin.cons_comp_succ_succAbove (L (1, 0)) (fun i => L (0, v i)) j
    rw [hslice, hrem, Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
/-- **Simon 6.2.17** (the slice form of `[[0, 1]] × T`): for `ω ∈ 𝒟^{k+1}(ℝ^{N+1})` the fibre
integral `η(x)(v) = ∫₀¹ ω(t, x)(e₀, (0, v₁), …, (0, vₖ)) dt` is a test `k`-form on `ℝᴺ` with
`spt η ⊆ {x : (t, x) ∈ spt ω for some t ∈ [0, 1]}`.  In the coordinates `L (t, x) = (t, x)`,
`η` integrates `g (t, x) = Φ (ω (L (t, x)))` for the contraction
`Φ γ = γ (L (1, 0), J ·, …, J ·)`, `J y = L (0, y)`; it is smooth by the parametric integral
lemma and vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`. -/
theorem Submission.cmcdt_lpo_slice_fiber_form : ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))} := by
  intro N k ω
  set ω' : DifferentialForm (Euclid (N + 1)) (k + 1) :=
    (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω' := ω.property.1.1
  have hωc : HasCompactSupport ω' := ω.property.1.2
  -- coordinates `L (t, y) = (t, y)` with `L (1, 0) = e₀`, and `J y = L (0, y)`
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  let J : Euclid N →L[ℝ] Euclid (N + 1) :=
    (L : ℝ × Euclid N →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N))
  -- the contraction `Φ γ = γ (L (1, 0), J ·, …, J ·)` is continuous linear
  let Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp
      ((ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k) (L (1, 0))).comp
        ContinuousAlternatingMap.curryLeftLI.toContinuousLinearMap)
  have hΦ : ∀ (γ : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N),
      Φ γ v = γ (Fin.cons (L (1, 0)) fun i => L (0, v i)) := fun _ _ => rfl
  -- `g (t, x) = Φ (ω (L (t, x)))` is smooth, hence so is `η x = ∫₀¹ g (t, x) dt`
  let g : ℝ × Euclid N → Covector (Euclid N) k := fun p => Φ (ω' (L p))
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := Φ.contDiff.comp (hωs.comp L.contDiff)
  let η : DifferentialForm (Euclid N) k := fun x => ∫ t in (0 : ℝ)..1, g (t, x)
  have hηs : ContDiff ℝ (⊤ : ℕ∞) η :=
    (Submission.cmcdt_lpo_slice_param_integral N (Covector (Euclid N) k) g hg).1
  -- `η` vanishes off the compact set `snd '' (L⁻¹ (spt ω) ∩ [0, 1] × ℝᴺ)`
  have hS : IsCompact (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    (L.toHomeomorph.isCompact_preimage.2 hωc.isCompact).inter_right
      (isClosed_Icc.prod isClosed_univ)
  have hsupp : support η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) := by
    intro x hx
    by_contra hxS
    refine mem_support.1 hx ?_
    have h0 : EqOn (fun t => g (t, x)) (fun _ => 0) (uIcc 0 1) := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hnot : L (t, x) ∉ tsupport ω' := fun hmem =>
        hxS ⟨(t, x), ⟨hmem, ht, mem_univ _⟩, rfl⟩
      show Φ (ω' (L (t, x))) = 0
      rw [image_eq_zero_of_notMem_tsupport hnot, map_zero]
    exact (intervalIntegral.integral_congr h0).trans intervalIntegral.integral_zero
  have hηt : tsupport η ⊆ Prod.snd '' (L ⁻¹' tsupport ω' ∩ Icc (0 : ℝ) 1 ×ˢ univ) :=
    closure_minimal hsupp (hS.image continuous_snd).isClosed
  refine ⟨⟨η, ⟨hηs, (hS.image continuous_snd).of_isClosed_subset (isClosed_tsupport η) hηt⟩,
    subset_univ _⟩, fun x v => ?_, hηt.trans ?_⟩
  · -- evaluation at `v` commutes with the integral
    have hint : IntervalIntegrable (fun t => g (t, x)) volume 0 1 :=
      (hg.continuous.comp (Continuous.prodMk_left x)).intervalIntegrable 0 1
    let ev : Covector (Euclid N) k →L[ℝ] ℝ := ContinuousAlternatingMap.apply ℝ (Euclid N) ℝ v
    calc η x v = ev (∫ t in (0 : ℝ)..1, g (t, x)) := rfl
      _ = ∫ t in (0 : ℝ)..1, ev (g (t, x)) := (ev.intervalIntegral_comp_comm hint).symm
      _ = _ := intervalIntegral.integral_congr fun t _ => by
        change Φ (ω' (L (t, x))) v = _
        rw [hΦ, hL1]
        simp only [hL]
  · rintro _ ⟨⟨t, y⟩, ⟨hmem, ht, -⟩, rfl⟩
    rw [mem_preimage, hL] at hmem
    exact ⟨t, ht, hmem⟩

/-- **End slices of `[[0, 1]] × T`** (Simon Ch. 6, 2.22: `{p} × T(ω) = T(Σ_β ω_{0β}(p, ·) dy^β)`).
Write `ι(t, x) = (t, x₁, …, x_N)` and `Jv = ι(0, v)`.  For `ω ∈ 𝒟ᵏ(ℝ^{N+1})` and `s ∈ ℝ`, the
form `ρ(x)(v₁, …, vₖ) = ω(ι(s, x))(Jv₁, …, Jvₖ)` lies in `𝒟ᵏ(ℝ^N)`.  With the coordinates
`L(t, y) = ι(t, y)` of `cmcdt_lpo_slice_coords`, `ρ` is the pull-back of `ω` by the affine map
`x ↦ L(s, 0) + L(0, x)`, which is proper since `‖x‖ = ‖L(0, x)‖ ≤ ‖L(s, 0) + L(0, x)‖ + ‖L(s, 0)‖`.
-/
theorem Submission.cmcdt_lpo_slice_end_form : ∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N k s ω
  obtain ⟨L, hL, -, hLn⟩ := Submission.cmcdt_lpo_slice_coords N
  -- `J y = L(0, y)`, so that `L(s, 0) + J x = L(s, x)`
  obtain ⟨J, hJ⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1), ∀ y, J y = L (0, y) :=
    ⟨(L : (ℝ × Euclid N) →L[ℝ] Euclid (N + 1)).comp (ContinuousLinearMap.inr ℝ ℝ (Euclid N)),
      fun _ => rfl⟩
  have hsJ : ∀ x, L (s, 0) + J x = L (s, x) := fun x => by
    rw [hJ, ← map_add L, Prod.mk_add_mk, add_zero, zero_add]
  -- `x ↦ L(s, 0) + J x` is proper: `‖x‖ = ‖J x‖ ≤ ‖L(s, 0) + J x‖ + ‖L(s, 0)‖`
  have hcont : Continuous fun x => L (s, 0) + J x := continuous_const.add J.continuous
  have hproper : IsProperMap fun x => L (s, 0) + J x := by
    refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
    refine isCompact_of_isClosed_isBounded (hK.isClosed.preimage hcont)
      ((isBounded_closedBall (x := (0 : Euclid N)) (r := R + ‖L (s, 0)‖)).subset fun x hx => ?_)
    have hxR : ‖L (s, 0) + J x‖ ≤ R := mem_closedBall_zero_iff.1 (hR hx)
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ = ‖L (s, 0) + J x - L (s, 0)‖ := by rw [add_sub_cancel_left, hJ, hLn]
      _ ≤ ‖L (s, 0) + J x‖ + ‖L (s, 0)‖ := norm_sub_le _ _
      _ ≤ R + ‖L (s, 0)‖ := by linarith
  -- `ρ` is the affine pull-back of `ω`, a test form on `ℝ^N` by properness
  refine ⟨⟨affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k), ?_⟩,
    fun x v => ?_⟩
  · exact show IsTestForm _ ∧ _ from
      ⟨affinePullbackForm_isTestForm J (L (s, 0)) hproper ω.property.1, subset_univ _⟩
  · show affinePullbackForm J (L (s, 0)) (ω : DifferentialForm (Euclid (N + 1)) k) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    rw [hsJ, hL]
    congr 1
    funext i
    rw [Function.comp_apply, hJ, hL]

/-- **Slice homotopy identity in degree `k + 1`** (Simon 6.2.19, 6.2.21 at the level of forms:
`S_{dβ} = i₁^#β − i₀^#β − dS_β`).  Write `ι(t, x) = (t, x)`, `Jv = ι(0, v)` and `e₀ = ι(1, 0)`.
If `θ(x)(u) = ∫₀¹ β(ι(t, x))(e₀, Ju) dt` for all `x` and `u`, then
`∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`.

By `cmcdt_lpo_slice_extDeriv_split` the integrand is `∂ₜ[β(ι(t, x))(Jv)]` minus the alternating
sum of the `x`-derivatives of the slices `β(ι(t, ·))(e₀, J v̂ⱼ)`.  The first term integrates to
the boundary terms (fundamental theorem of calculus).  Differentiating the hypothesis under the
integral sign (`cmcdt_lpo_slice_param_integral`; smoothness via the linear coordinates of
`cmcdt_lpo_slice_coords`) and expanding `dθ` identifies the integral of the second term with
`dθ(x)(v)`. -/
theorem Submission.cmcdt_lpo_slice_homotopy_succ : ∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v := by
  intro N k β θ hθ x v
  set B := (β : DifferentialForm (Euclid (N + 1)) (k + 1))
  set Θ := (θ : DifferentialForm (Euclid N) k)
  have hBs : ContDiff ℝ (⊤ : ℕ∞) B := β.property.1.1
  have hΘd : Differentiable ℝ Θ := θ.property.1.1.differentiable (by simp)
  -- (1) `p ↦ B(ι p)(w)` is smooth for each fixed tuple `w`, as `ι` is the linear equivalence `L`
  obtain ⟨L, hL, -, -⟩ := Submission.cmcdt_lpo_slice_coords N
  have hG : ∀ w : Fin (k + 1) → Euclid (N + 1), ContDiff ℝ (⊤ : ℕ∞)
      fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w := by
    intro w
    have hfun : (fun p : ℝ × Euclid N => B (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))) w) =
        ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w ∘ B ∘ L := by
      funext p
      simp only [Function.comp_apply, ContinuousAlternatingMap.apply_apply, ← hL, Prod.mk.eta]
    rw [hfun]
    exact (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp
      (hBs.comp L.contDiff)
  -- (2) the `x`-derivative of each slice is continuous in `t`
  have hD : ∀ w : Fin (k + 1) → Euclid (N + 1), Continuous fun t : ℝ =>
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w) x :=
    fun w => Continuous.fderiv
      (f := fun (t : ℝ) (x' : Euclid N) => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x'))) w)
      (hG w) continuous_const (by simp)
  -- (3) differentiate the hypothesis on `θ` under the integral sign
  have hΘD : ∀ u : Fin k → Euclid N, fderiv ℝ (fun x' : Euclid N => Θ x' u) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t
        (WithLp.ofLp x'))) (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i)))))) x := by
    intro u
    rw [show (fun x' : Euclid N => Θ x' u) = _ from funext fun x' => hθ x' u]
    exact ((Submission.cmcdt_lpo_slice_param_integral N ℝ _ (hG _)).2 x).fderiv
  -- (4) split the integrand into a `t`-derivative and the alternating sum of `x`-derivatives
  simp only [Submission.cmcdt_lpo_slice_extDeriv_split N k B (hBs.differentiable (by simp))]
  -- (5) fundamental theorem of calculus for `φ(s) = B(ι(s, x))(Jv)`
  have hφ : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => B (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
      (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :=
    (hG _).comp (contDiff_id.prodMk contDiff_const)
  have hFTC := intervalIntegral.integral_deriv_eq_sub (fun s _ => hφ.differentiable (by simp) s)
    ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
  -- (6) the integral of the alternating sum is `dΘ(x)(v)`
  have hcont : ∀ j : Fin (k + 1), Continuous fun t : ℝ => (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) :=
    fun j => ((hD _).clm_apply continuous_const).fun_const_smul ((-1 : ℤ) ^ (j : ℕ))
  have hsum : ∫ t in (0 : ℝ)..1, ∑ j : Fin (k + 1), (-1 : ℤ) ^ (j : ℕ) •
      fderiv ℝ (fun x' : Euclid N => B (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x')))
        (Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))))) x (v j) =
      exteriorDerivative Θ x v := by
    rw [exteriorDerivative_apply (hΘd x) v,
      intervalIntegral.integral_finsetSum fun j _ => (hcont j).intervalIntegrable 0 1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΘD, ContinuousLinearMap.intervalIntegral_apply ((hD _).intervalIntegrable 0 1)]
    simp only [zsmul_eq_mul, intervalIntegral.integral_const_mul]
  -- (7) linearity of the integral
  rw [intervalIntegral.integral_sub ((hφ.continuous_deriv (by simp)).intervalIntegrable 0 1)
    ((continuous_finsetSum _ fun j _ => hcont j).intervalIntegrable 0 1), hFTC, hsum]

/-- **Slice homotopy identity in degree `0`** (Simon 6.2.21 without the `∂T` term).  For
`β ∈ 𝒟⁰(ℝ^{N+1})`, `x ∈ ℝ^N` and the empty tuple `w = J ∘ v`,
`∫₀¹ dβ(ι(t, x))(e₀) dt = β(ι(1, x))(w) − β(ι(0, x))(w)`, where `ι(t, x) = (t, x)`.
With the coordinates `L(t, x) = ι(t, x)`, `L(1, 0) = e₀` of `cmcdt_lpo_slice_coords`, the path
`φ(s) = β(L(s, x))(w)` is smooth with `φ′(s) = D[y ↦ β(y)(w)](L(s, x))(e₀)`, the single term
`i = 0` of `exteriorDerivative_apply` (as `removeNth 0 (e₀, w) = w`); the fundamental theorem of
calculus concludes. -/
theorem Submission.cmcdt_lpo_slice_homotopy_zero : ∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
  intro N β x v
  obtain ⟨L, hL, hL1, -⟩ := Submission.cmcdt_lpo_slice_coords N
  set ω : DifferentialForm (Euclid (N + 1)) 0 := (β : DifferentialForm (Euclid (N + 1)) 0)
  set w : Fin 0 → Euclid (N + 1) := fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω := β.property.1.1
  -- `y ↦ ω y w` is `ω` followed by the continuous linear evaluation at `w`
  have hωw : ContDiff ℝ (⊤ : ℕ∞) (fun y => ω y w) :=
    (ContinuousAlternatingMap.apply ℝ (Euclid (N + 1)) ℝ w).contDiff.comp hω
  -- chain rule along the path `s ↦ L (s, x)`, whose velocity is `L (1, 0)`
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => L (s, x)) (L (1, 0)) s := fun s =>
    L.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ω (L (s, x)) w)
      (fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0))) s := fun s =>
    ((hωw.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s (hpath s)
  -- in degree `0` the exterior derivative is the single term `i = 0`
  have hpt : ∀ s : ℝ, exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) =
      fderiv ℝ (fun y => ω y w) (L (s, x)) (L (1, 0)) := by
    intro s
    rw [exteriorDerivative_apply ((hω.differentiable (by simp)) _)]
    simp only [Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Int.reduceNeg,
      Fin.val_eq_zero, pow_zero, one_smul, Finset.sum_singleton, Fin.removeNth_zero,
      Fin.tail_cons, Fin.cons_zero]
  have hderiv : deriv (fun s : ℝ => ω (L (s, x)) w) =
      fun s => exteriorDerivative ω (L (s, x)) (Fin.cons (L (1, 0)) w) := by
    funext s
    rw [(hφ s).deriv, hpt]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => ω (L (s, x)) w) :=
    hωw.comp (L.contDiff.comp (contDiff_id.prodMk contDiff_const))
  -- fundamental theorem of calculus, then back to the coordinates of the statement
  have key := intervalIntegral.integral_deriv_eq_sub' (a := 0) (b := 1) _ hderiv
    (fun s _ => (hφ s).differentiableAt)
    (hderiv ▸ (hsmooth.continuous_deriv (by simp)).continuousOn)
  rw [hL1] at key
  simpa only [hL] using key
/-- **Simon 6.1.15, 6.2.17** (Minkowski's integral inequality for the Euclidean coefficient norm
`|·|` of 6.1.15, used for the slice forms defining `[[(0, 1)]] × T`): if `α(v) = ∫₀¹ f(t)(v) dt`
for all `v` and `|f(t)| ≤ c` on `[0, 1]`, then `|α| ≤ c`.  The coefficient vector
`κ(γ) = (γ(e_I))_{I strictly increasing} ∈ ℓ²` has `‖κ(γ)‖ = |γ|`, is continuous, and commutes
with the integral coordinatewise; hence `|α| = ‖∫₀¹ κ(f t) dt‖ ≤ c`. -/
theorem Submission.cmcdt_lpo_slice_covector_bound : ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c := by
  intro N k α f c hf hα hc
  classical
  -- the coefficient vector `κ γ = (γ(e_I))_I`, with `γ(e_I)` replaced by `0` unless `I` is
  -- strictly increasing
  let e : Fin N → Euclid N := fun j => EuclideanSpace.basisFun (Fin N) ℝ j
  let κ : Covector (Euclid N) k → EuclideanSpace ℝ (Fin k → Fin N) := fun γ =>
    WithLp.toLp 2 fun I => if StrictMono I then γ (fun i => e (I i)) else 0
  have hκnorm : ∀ γ, ‖κ γ‖ = covectorEuclideanNorm γ := by
    intro γ
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [κ, e, hI]
  have hκcont : Continuous κ := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun I => ?_)
    by_cases hI : StrictMono I
    · simp only [hI, ite_true]
      exact continuous_eval_const _
    · simp only [hI, ite_false]
      exact continuous_const
  have hint : IntervalIntegrable (fun t => κ (f t)) volume 0 1 :=
    (hκcont.comp hf).intervalIntegrable 0 1
  -- `κ α = ∫₀¹ κ (f t) dt`, coordinatewise
  have hκα : κ α = ∫ t in (0 : ℝ)..1, κ (f t) := by
    ext I
    refine Eq.trans ?_ ((EuclideanSpace.proj I :
      EuclideanSpace ℝ (Fin k → Fin N) →L[ℝ] ℝ).intervalIntegral_comp_comm hint)
    by_cases hI : StrictMono I
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_true]
      exact hα _
    · simp only [κ, EuclideanSpace.coe_proj, hI, ite_false, intervalIntegral.integral_zero]
  rw [← hκnorm, hκα]
  calc ‖∫ t in (0 : ℝ)..1, κ (f t)‖ ≤ c * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => by
          rw [hκnorm]
          exact hc t (Set.Ioc_subset_Icc_self (by simpa [Set.uIoc_of_le zero_le_one] using ht))
    _ = c := by simp

/-- **Slices of forms on `[0, 1] × ℝᴺ`** (Simon Ch. 6, 2.17–2.22, and the homotopy formula
2.25–2.27).  Write `ι(t, x) = (t, x₁, …, x_N)`, `Jv = ι(0, v)` and `e₀ = EuclideanSpace.single 0 1`.
(a) `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt` is a test form on `ℝᴺ`, supported in the set of `x`
with `ι(t, x) ∈ spt ω` for some `t ∈ [0, 1]` (`cmcdt_lpo_slice_fiber_form`); (b) the end slice
`ρ(x)(v) = ω(ι(s, x))(Jv)` is a test form (`cmcdt_lpo_slice_end_form`); (c) if `θ` is the
slice (a) of `β`, then `∫₀¹ dβ(ι(t, x))(e₀, Jv) dt = β(ι(1, x))(Jv) − β(ι(0, x))(Jv) − dθ(x)(v)`
(`cmcdt_lpo_slice_homotopy_succ`); (d) in degree `0` the same identity holds without `dθ`
(`cmcdt_lpo_slice_homotopy_zero`); (e) `|α| ≤ c` when `α = ∫₀¹ f(t) dt` for continuous `f` with
`|f(t)| ≤ c` on `[0, 1]` (`cmcdt_lpo_slice_covector_bound`).  The statement is the conjunction
of these five children. -/
theorem Submission.cmcdt_lpo_slice_forms : (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ tsupport (η : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | ∃ t ∈ Icc (0 : ℝ) 1, (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ (∀ (N k : ℕ) (s : ℝ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), ∃ ρ : TestFormOn (univ : Set (Euclid N)) k, ∀ (x : Euclid N) (v : Fin k → Euclid N), (ρ : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (N k : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (θ : TestFormOn (univ : Set (Euclid N)) k), (∀ (x : Euclid N) (v : Fin k → Euclid N), (θ : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (θ : DifferentialForm (Euclid N) k) x v) ∧ (∀ (N : ℕ) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (x : Euclid N) (v : Fin 0 → Euclid N), ∫ t in (0 : ℝ)..1, exteriorDerivative (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ (N k : ℕ) (α : Covector (Euclid N) k) (f : ℝ → Covector (Euclid N) k) (c : ℝ), Continuous f → (∀ v : Fin k → Euclid N, α v = ∫ t in (0 : ℝ)..1, f t v) → (∀ t ∈ Icc (0 : ℝ) 1, covectorEuclideanNorm (f t) ≤ c) → covectorEuclideanNorm α ≤ c :=
  ⟨Submission.cmcdt_lpo_slice_fiber_form, Submission.cmcdt_lpo_slice_end_form,
    Submission.cmcdt_lpo_slice_homotopy_succ, Submission.cmcdt_lpo_slice_homotopy_zero,
    Submission.cmcdt_lpo_slice_covector_bound⟩
/-- The cut-off pull-back of Simon 6.2.23: for a `C^∞` map `F : ℝᴺ → ℝ^{N'}`, `ω ∈ 𝒟ᵏ(ℝ^{N'})` and
a compact `K ⊆ ℝᴺ`, some `η = ζ F^#ω ∈ 𝒟ᵏ(ℝᴺ)` agrees with `F^#ω` on an open `W ⊇ K`, and
`dη = F^#(dω)` on `W` (as used in 6.2.24(1)).  Here `ζ` is a smooth bump equal to `1` on a ball
`W ⊇ K`.  `F^#ω` is smooth: as a multilinear map, `F^#ω(x) = ω(F x) ∘ (DF(x), …, DF(x))` depends
smoothly on `x`, and `γ ↦ (γ(e_{I 1}, …, e_{I k}))_I` is linear and injective into a
finite-dimensional space, so it has a continuous linear left inverse.  On `W`, `η = F^#ω` near
each point, so `dη = d(F^#ω) = F^#(dω)` (`extDeriv_pullback`). -/
theorem Submission.cmcdt_lpo_cutoff_pullback : ∀ (N N' k : ℕ) (F : Euclid N → Euclid N') (ω : TestFormOn (univ : Set (Euclid N')) k) (K : Set (Euclid N)), ContDiff ℝ (⊤ : ℕ∞) F → IsCompact K → ∃ (η : TestFormOn (univ : Set (Euclid N)) k) (W : Set (Euclid N)), IsOpen W ∧ K ⊆ W ∧ (∀ x ∈ W, (η : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x)) ∧ ∀ x ∈ W, exteriorDerivative (η : DifferentialForm (Euclid N) k) x = (exteriorDerivative (ω : DifferentialForm (Euclid N') k) (F x)).compContinuousLinearMap (fderiv ℝ F x) := by
  intro N N' k F ω K hF hK
  set ω₀ : DifferentialForm (Euclid N') k := (ω : DifferentialForm (Euclid N') k)
  have hω : ContDiff ℝ (⊤ : ℕ∞) ω₀ := ω.2.1.1
  have hDF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := hF.fderiv_right le_rfl
  -- the pull-back `P = F^#ω` is smooth
  set P : DifferentialForm (Euclid N) k :=
    fun x => (ω₀ (F x)).compContinuousLinearMap (fderiv ℝ F x)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    let ι : Covector (Euclid N) k →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ :=
      ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ
    have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x => ι (P x) := by
      have h := ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => Euclid N) (fun _ : Fin k => Euclid N') ℝ).contDiff.comp
          (contDiff_pi.2 fun _ => hDF)).clm_apply
        ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp (hω.comp hF))
      convert h using 1
      funext x
      ext v
      simp [ι, P, Function.comp_def]
    -- the values on basis tuples determine a covector
    let e := EuclideanSpace.basisFun (Fin N) ℝ
    let ev' : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euclid N) ℝ →L[ℝ]
        ((Fin k → Fin N) → ℝ) :=
      ContinuousLinearMap.pi fun I =>
        ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euclid N) ℝ fun i => e (I i)
    let ev : Covector (Euclid N) k →ₗ[ℝ] ((Fin k → Fin N) → ℝ) := (ev'.comp ι).toLinearMap
    have hev : LinearMap.ker ev = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro γ hγ
      have h' : γ.toAlternatingMap = (0 : Covector (Euclid N) k).toAlternatingMap := by
        refine e.toBasis.ext_alternating fun I _ => ?_
        have := congrFun hγ I
        simpa [ev, ev', ι, e] using this
      exact ContinuousAlternatingMap.toAlternatingMap_injective h'
    obtain ⟨ℓ, hℓ⟩ := ev.exists_leftInverse_of_injective hev
    have hPℓ : P = fun x => LinearMap.toContinuousLinearMap ℓ (ev' (ι (P x))) := by
      funext x
      exact (LinearMap.congr_fun hℓ (P x)).symm
    rw [hPℓ]
    exact (LinearMap.toContinuousLinearMap ℓ).contDiff.comp (ev'.contDiff.comp h1)
  -- a smooth bump `b`, equal to `1` on a ball `W ⊇ K`
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_ball_lt 0 (0 : Euclid N)
  let b : ContDiffBump (0 : Euclid N) := ⟨R, R + 1, hR, by linarith⟩
  have hb1 : ∀ x ∈ ball (0 : Euclid N) R, b x = 1 := fun x hx =>
    b.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hη : (fun x => b x • P x) ∈ TestFormOn (univ : Set (Euclid N)) k :=
    ⟨⟨b.contDiff.smul hP, b.hasCompactSupport.smul_right⟩, subset_univ _⟩
  refine ⟨⟨fun x => b x • P x, hη⟩, ball 0 R, isOpen_ball, hKR, fun x hx => ?_, fun x hx => ?_⟩
  · show b x • P x = P x
    rw [hb1 x hx, one_smul]
  · have heq : (fun x => b x • P x) =ᶠ[𝓝 x] P := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [hb1 y hy, one_smul]
    show extDeriv (fun x => b x • P x) x = _
    rw [heq.extDeriv_eq]
    exact extDeriv_pullback ((hω.differentiable (by simp)).differentiableAt) hF.contDiffAt
      (by simp)

/-- **Cut-off pull-backs along the smoothed homotopy and their limits** (Simon Ch. 6, §2: the
homotopy formula for Lipschitz maps via smooth approximation).  Write `ι(t, x) = (t, x₁, …, x_N)`,
`Jv = ι(0, v)` and `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` (compact).  With the smooth approximations
`F_j, G_j, H_j` of `cmcdt_lpoh_smooth_approx`, `β_j` is the cut-off pull-back of
`cmcdt_lpo_cutoff_pullback`, equal to `H_j^#ω` (and `dβ_j` to `H_j^#(dω)`) on an open `W_j ⊇ C`,
and `ρ_{s,j}(x) = β_j(ι(s, x)) ∘ J` is the affine pull-back of `β_j` by the isometric embedding
`ι(s, ·)`, a test form since `ι(s, ·)` is proper.  As `H_j ∘ ι(1, ·) = G_j` and
`H_j ∘ ι(0, ·) = F_j` with matching derivatives along `J`, `ρ_{1,j} = G_j^#ω` and
`ρ_{0,j} = F_j^#ω` near `K`, so (PA) gives the limits; the pointwise description of `β_j` on `C`
carries the derivative bounds of `cmcdt_lpoh_smooth_approx`. -/
theorem Submission.cmcdt_lpoh_pullback_limits : ∀ (lpush : ∀ (N N' k : ℕ), (Euclid N → Euclid N') → GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid N')) k), (∀ (N N' k : ℕ) (Λ : NNReal) (Λ' : ℝ) (F : Euclid N → Euclid N') (Fs : ℕ → Euclid N → Euclid N') (X : GeometricCurrentOn (univ : Set (Euclid N)) k) (ω : TestFormOn (univ : Set (Euclid N')) k) (ηs : ℕ → TestFormOn (univ : Set (Euclid N)) k), LipschitzWith Λ F → IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → (∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fs j)) → (∀ j, ∀ x ∈ X.support, ‖fderiv ℝ (Fs j) x‖ ≤ Λ') → TendstoUniformlyOn Fs F atTop X.support → (∀ j, ∃ W : Set (Euclid N), IsOpen W ∧ X.support ⊆ W ∧ ∀ x ∈ W, (ηs j : DifferentialForm (Euclid N) k) x = ((ω : DifferentialForm (Euclid N') k) (Fs j x)).compContinuousLinearMap (fderiv ℝ (Fs j) x)) → Tendsto (fun j => X (ηs j)) atTop (𝓝 (lpush N N' k F X ω))) → ∀ (N N' m : ℕ) (Λ L : NNReal) (F G : Euclid N → Euclid N') (H : Euclid (N + 1) → Euclid N') (K : Set (Euclid N)) (ω : TestFormOn (univ : Set (Euclid N')) m), LipschitzWith Λ F → LipschitzWith Λ G → LipschitzWith L H → IsCompact K → (∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, H (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = F x + t • (G x - F x)) → ∃ (β : ℕ → TestFormOn (univ : Set (Euclid (N + 1))) m) (ρ₁ ρ₀ : ℕ → TestFormOn (univ : Set (Euclid N)) m), (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₁ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (j : ℕ) (x : Euclid N) (v : Fin m → Euclid N), (ρ₀ j : DifferentialForm (Euclid N) m) x v = (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid N)) m, IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → X.support ⊆ K → Tendsto (fun j => X (ρ₁ j)) atTop (𝓝 (lpush N N' m G X ω)) ∧ Tendsto (fun j => X (ρ₀ j)) atTop (𝓝 (lpush N N' m F X ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) m, IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (β j)) atTop (𝓝 (lpush (N + 1) N' m H Y ω))) ∧ (∀ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (m + 1), IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} → Tendsto (fun j => Y (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j))) atTop (𝓝 (lpush (N + 1) N' (m + 1) H Y (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)))) ∧ ∀ (j : ℕ), ∀ x ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∃ (p : Euclid N') (D : Euclid (N + 1) →L[ℝ] Euclid N'), (β j : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) = ((ω : DifferentialForm (Euclid N') m) p).compContinuousLinearMap D ∧ ‖D (EuclideanSpace.single 0 1)‖ ≤ dist (F x) (G x) + 2 * (Λ : ℝ) / ((j : ℝ) + 1) ∧ ∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ (Λ : ℝ) * ‖v‖ := by
  intro lpush hPA N N' m Λ L F G H K ω hF hG hH hK hHK
  obtain ⟨Fs, Gs, Hs, Λ', hFs, hGs, hHs, hDF, hDG, hFu, hGu, hH1, hH0, hDH1, hDH0, hDe, hDJ, hDHb,
    hHu⟩ := Submission.cmcdt_lpoh_smooth_approx N N' Λ F G H K hF hG hK hHK
  -- `C = {ι(t, x) : t ∈ [0, 1], x ∈ K}` is compact
  set C : Set (Euclid (N + 1)) := {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ K,
    y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}
  have hιc : ∀ s : ℝ, Continuous
      (fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))) :=
    fun s => (PiLp.continuous_toLp 2 _).comp (continuous_const.finCons (PiLp.continuous_ofLp 2 _))
  have hCc : IsCompact C := by
    have : C = (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) ''
          (Icc (0 : ℝ) 1 ×ˢ K) := by
      ext y
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨(t, x), ⟨ht, hx⟩, rfl⟩
      · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    rw [this]
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  -- cut-off pull-backs `β_j = H_j^#ω` and `dβ_j = H_j^#(dω)` on an open `W_j ⊇ C`
  have hCP := fun j => Submission.cmcdt_lpo_cutoff_pullback (N + 1) N' m (Hs j) ω C (hHs j) hCc
  choose β W hWo hCW hβW hdβW using hCP
  -- end slices `ρ(x)(v) = β(ι(s, x))(Jv)`: the affine pull-back by the isometry `ι(s, ·)`
  have hslice : ∀ (s : ℝ) (β' : TestFormOn (univ : Set (Euclid (N + 1))) m),
      ∃ ρ : TestFormOn (univ : Set (Euclid N)) m, ∀ (x : Euclid N) (v : Fin m → Euclid N),
        (ρ : DifferentialForm (Euclid N) m) x v =
          (β' : DifferentialForm (Euclid (N + 1)) m) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) := by
    intro s β'
    let Jₗ : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun v w => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by
          ext i
          refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jₗ
    have hJ : ∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) := fun _ => rfl
    set b : Euclid (N + 1) := WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (0 : Euclid N))) with hb
    have hbJ : ∀ x, b + J x = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) := by
      intro x
      ext i
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [hb, hJ]
    have hproper : IsProperMap fun x => b + J x := by
      refine (Isometry.isClosedEmbedding (Isometry.of_dist_eq fun x y => ?_)).isProperMap
      rw [hbJ, hbJ, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq, Fin.sum_univ_succ]
      simp
    refine ⟨⟨affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m),
      affinePullbackForm_isTestForm J b hproper β'.property.1, subset_univ _⟩, fun x v => ?_⟩
    show affinePullbackForm J b (β' : DifferentialForm (Euclid (N + 1)) m) x v = _
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply, hbJ]
    rfl
  choose ρ hρ using fun (s : ℝ) (j : ℕ) => hslice s (β j)
  refine ⟨β, ρ 1, ρ 0, fun j x v => hρ 1 j x v, fun j x v => hρ 0 j x v, ?_, ?_, ?_, ?_⟩
  · -- (ii): near `K`, `ρ_{1,j} = G_j^#ω` and `ρ_{0,j} = F_j^#ω`
    intro X hXc hXm hXb hXK
    have hend : ∀ (s : ℝ) (Es : ℕ → Euclid N → Euclid N'),
        (∀ (j : ℕ) (x : Euclid N), Hs j (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) = Es j x) →
        (∀ (j : ℕ) (x v : Euclid N), fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
          (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) = fderiv ℝ (Es j) x v) →
        s ∈ Icc (0 : ℝ) 1 → ∀ j, ∃ W' : Set (Euclid N), IsOpen W' ∧ X.support ⊆ W' ∧ ∀ x ∈ W',
          (ρ s j : DifferentialForm (Euclid N) m) x =
            ((ω : DifferentialForm (Euclid N') m) (Es j x)).compContinuousLinearMap
              (fderiv ℝ (Es j) x) := by
      intro s Es hE hDE hs j
      refine ⟨(fun x : Euclid N => (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1)))
        ⁻¹' W j, (hWo j).preimage (hιc s), fun x hx => hCW j ⟨s, hs, x, hXK hx, rfl⟩,
        fun x hx => ?_⟩
      ext v
      rw [hρ s j x v, hβW j _ hx]
      simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, hE]
      congr 1
      funext i
      exact hDE j x (v i)
    constructor
    · exact hPA N N' m Λ Λ G Gs X ω (ρ 1) hG hXc hXm hXb hGs (fun j x _ => hDG j x)
        hGu.tendstoUniformlyOn (hend 1 Gs hH1 hDH1 ⟨zero_le_one, le_rfl⟩)
    · exact hPA N N' m Λ Λ F Fs X ω (ρ 0) hF hXc hXm hXb hFs (fun j x _ => hDF j x)
        hFu.tendstoUniformlyOn (hend 0 Fs hH0 hDH0 ⟨le_rfl, zero_le_one⟩)
  · -- (iii): (PA) for `H` with the approximations `H_j`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' m L Λ' H Hs Y ω β hH hYc hYm hYb hHs ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hβW j⟩
  · -- (iv): the same in degree `m + 1` for `dβ_j` and `dω`
    intro Y hYc hYm hYb hYC
    refine hPA (N + 1) N' (m + 1) L Λ' H Hs Y
      (exteriorDerivativeTestOn (univ : Set (Euclid N')) m ω)
      (fun j => exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) m (β j)) hH hYc hYm hYb hHs
      ?_ (hHu.mono hYC) ?_
    · intro j y hy
      obtain ⟨t, ht, x, hx, rfl⟩ := hYC hy
      exact hDHb j t ht x hx
    · intro j
      exact ⟨W j, hWo j, hYC.trans (hCW j), hdβW j⟩
  · -- (v): on `C`, `β_j = H_j^#ω` with the derivative bounds of the smoothed homotopy
    intro j x hx t ht
    exact ⟨Hs j (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      fderiv ℝ (Hs j) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))),
      hβW j _ (hCW j ⟨t, ht, x, hx, rfl⟩), hDe j t x, hDJ j t ht x⟩

/-- **Homotopy identity for a cylinder operator** (Simon Ch. 6, 2.17–2.22, and the homotopy
formula 2.25–2.27).  Let `cyl` take `X ∈ 𝒟ₖ(ℝᴺ)` to `cyl X ∈ 𝒟ₖ₊₁(ℝᴺ⁺¹)` with the slice property
(9): for `X` with compact support, `M(X) < ∞` and `M(∂X) < ∞`, and `ω ∈ 𝒟ᵏ⁺¹(ℝᴺ⁺¹)`,
`cyl X (ω) = X(η)` with `η(x)(v) = ∫₀¹ ω(ι(t, x))(e₀, Jv) dt`.  (a) In degree `0`, where
`boundaryMassOn X univ = 0`, (9) for `dβ` and the slice identity (d) of `cmcdt_lpo_slice_forms`
give `η = ρ₁ − ρ₀`, so `cyl X (dβ) = X(ρ₁) − X(ρ₀)`.  (b) In degree `k + 1`, (9) for `X` and `dβ`
gives `η`, (9) for `∂X` and `β` gives `θ` with `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and the slice
identity (c) gives `η = ρ₁ − ρ₀ − dθ`; by linearity of `X`,
`cyl X (dβ) = X(ρ₁) − X(ρ₀) − cyl ∂X (β)`. -/
theorem Submission.cmcdt_lpoh_cyl_identity : ∀ (cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1)), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : TestFormOn (univ : Set (Euclid N)) k, (∀ (x : Euclid N) (v : Fin k → Euclid N), (η : DifferentialForm (Euclid N) k) x v = ∫ t in (0 : ℝ)..1, (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = X η) → (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0) (β : TestFormOn (univ : Set (Euclid (N + 1))) 0) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₁ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (ρ₀ : DifferentialForm (Euclid N) 0) x v = (β : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N 0 X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β) = X ρ₁ - X ρ₀) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)) (β : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (ρ₁ ρ₀ : TestFormOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → IsCompact X.boundary.support → boundaryMassOn X.boundary univ < ∞ → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₁ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (ρ₀ : DifferentialForm (Euclid N) (k + 1)) x v = (β : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → cyl N (k + 1) X (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β) = X ρ₁ - X ρ₀ - cyl N k X.boundary β := by
  intro cyl h9
  -- the slice identities (c) and (d) of `cmcdt_lpo_slice_forms`
  obtain ⟨-, -, hc, hd, -⟩ := Submission.cmcdt_lpo_slice_forms
  refine ⟨?_, ?_⟩
  · intro N X β ρ₁ ρ₀ hXc hXm hρ₁ hρ₀
    -- Step 1: `boundaryMassOn X univ = 0` in degree `0`, so `X` is normal
    have hXb : boundaryMassOn X univ < ∞ := by
      show (0 : ℝ≥0∞) < ∞
      exact ENNReal.zero_lt_top
    -- Step 2: (9) for `X` and `dβ`
    obtain ⟨η, hη, hcyl⟩ := h9 N 0 X hXc hXm hXb
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 β)
    -- Step 3: `η = ρ₁ − ρ₀` by the slice identity (d); then linearity of `X`
    have hηeq : η = ρ₁ - ρ₀ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hd N β x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    rw [hcyl, hηeq]
    exact map_sub X.toCurrent ρ₁ ρ₀
  · intro N k X β ρ₁ ρ₀ hXc hXm hXbm hbc hbb hρ₁ hρ₀
    -- Steps 4–5: `boundaryMassOn X univ = M(∂X)`; (9) for `X` and `dβ`, and for `∂X` and `β`
    obtain ⟨η, hη, hcyl⟩ := h9 N (k + 1) X hXc hXm hXbm
      (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) β)
    obtain ⟨θ, hθ, hcylb⟩ := h9 N k X.boundary hbc hXbm hbb β
    -- Step 6: `η = ρ₁ − ρ₀ − dθ` by the slice identity (c)
    have hηeq : η = ρ₁ - ρ₀ - exteriorDerivativeTestOn (univ : Set (Euclid N)) k θ := by
      apply Subtype.ext
      funext x
      ext v
      rw [hη x v]
      have := hc N k β θ hθ x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply, hρ₁, hρ₀]
      exact this
    -- Step 7: `cyl ∂X (β) = ∂X(θ) = X(dθ)`, and linearity of `X`
    rw [hcyl, hcylb, hηeq]
    exact (map_sub X.toCurrent _ _).trans (by rw [map_sub X.toCurrent ρ₁ ρ₀]; rfl)
/-- **Covector bound for the `e₀`-slice of a pulled-back covector.**  Given the bounds
(L1) `|β ∘ A| ≤ ‖A‖ᵏ |β|` and (L2) `|β(v, ·)| ≤ ‖v‖ |β|` for the Euclidean coefficient norm
`|·| = covectorEuclideanNorm`, let `φ(v₁, …, v_k) = (D^#γ)(e₀, Jv₁, …, Jv_k)` with
`J v = (0, v)`, `‖D e₀‖ ≤ a` and `‖D (J v)‖ ≤ b ‖v‖`.  Then `φ = γ(D e₀, ·) ∘ (D ∘ J)`, so
`|φ| ≤ ‖D ∘ J‖ᵏ ‖D e₀‖ |γ| ≤ bᵏ a |γ|`. -/
theorem Submission.cmcdt_lpoh_phi_bound : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) → (∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → ∀ (N N' k : ℕ) (γ : Covector (Euclid N') (k + 1)) (D : Euclid (N + 1) →L[ℝ] Euclid N') (φ : Covector (Euclid N) k) (a b : ℝ), 0 ≤ b → ‖D (EuclideanSpace.single 0 1)‖ ≤ a → (∀ v : Euclid N, ‖D (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)))‖ ≤ b * ‖v‖) → (∀ v : Fin k → Euclid N, φ v = (γ.compContinuousLinearMap D) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → covectorEuclideanNorm φ ≤ b ^ k * a * covectorEuclideanNorm γ := by
  intro hL1 hL2 N N' k γ D φ a b hb hDe hDJ hφ
  /- Step 1: `J v = (0, v)` is linear (check coordinatewise), hence continuous linear. -/
  let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
      map_add' := by
        intro v w
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := by
        intro r v
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  let J : Euclid N →L[ℝ] Euclid (N + 1) := LinearMap.toContinuousLinearMap Jl
  /- Step 2: `φ = γ(D e₀, ·) ∘ (D ∘ J)`, since `D ∘ (e₀, Jv) = (D e₀, D (J v))`. -/
  have hφeq : φ = (γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
      (D.comp J) := by
    ext v
    rw [hφ v]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousAlternatingMap.curryLeft_apply_apply, ContinuousLinearMap.coe_comp]
    congr 1
    rw [Fin.comp_cons]
    rfl
  /- Step 3: `‖D ∘ J‖ ≤ b`. -/
  have hA : ‖D.comp J‖ ≤ b := ContinuousLinearMap.opNorm_le_bound _ hb hDJ
  /- Step 4: (L1) for `D ∘ J`, then (L2) for `D e₀`. -/
  rw [hφeq]
  calc covectorEuclideanNorm ((γ.curryLeft (D (EuclideanSpace.single 0 1))).compContinuousLinearMap
        (D.comp J))
      ≤ ‖D.comp J‖ ^ k * covectorEuclideanNorm (γ.curryLeft (D (EuclideanSpace.single 0 1))) :=
        hL1 N N' k (D.comp J) _
    _ ≤ b ^ k * (‖D (EuclideanSpace.single 0 1)‖ * covectorEuclideanNorm γ) := by
        gcongr
        · exact covectorEuclideanNorm_nonneg _
        · exact hL2 N' k _ γ
    _ ≤ b ^ k * (a * covectorEuclideanNorm γ) := by
        gcongr
        exact covectorEuclideanNorm_nonneg γ
    _ = b ^ k * a * covectorEuclideanNorm γ := by ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
