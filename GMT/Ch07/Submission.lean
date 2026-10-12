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

/-- **Campanato's criterion for the derivative** (steps 6 and 7 of the graph-`C¹` argument).  Let
`n ≥ 1`, `Ω ⊆ ℝⁿ` open, `C ≥ 0`, `s₁ > 0`, and suppose that for `Lⁿ`-a.e. `v ∈ Ω`, `f` is
differentiable at `v` and `∫_{B_s(v)} |Df(w) − Df(v)|² dw ≤ C s^{n+1}` for `0 < s ≤ s₁`, where
`|A|² = Σᵢ |A eᵢ|²`.  On the good set `G` of such `v`, averaging
`|Df(v₁) − Df(v₂)|² ≤ 2 |Df(w) − Df(v₁)|² + 2 |Df(w) − Df(v₂)|²` over the ball of radius `d / 2`
about the midpoint (`d = |v₁ − v₂| ≤ s₁`) gives `‖Df(v₁) − Df(v₂)‖² ≤ 2^{n+2} C ωₙ⁻¹ d`, so `Df` is
uniformly continuous on `G`.  As `Ω ∖ G` is null, `G` is dense in `Ω`, and `g = extendFrom G Df` is
continuous on `Ω`, equals `Df` on `G`, and hence is the derivative of `f` at a.e. point of `Ω`. -/
theorem Submission.dorag_gc_campanato_continuous_deriv : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (Ω : Set (Euclid n)) (C s₁ : ℝ), 0 < n → IsOpen Ω → 0 ≤ C → 0 < s₁ → (∀ᵐ v ∂volume, v ∈ Ω → DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ → ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤ ENNReal.ofReal (C * s ^ (n + 1))) → ∃ g : Euclid n → (Euclid n →L[ℝ] Euclid k), ContinuousOn g Ω ∧ ∀ᵐ v ∂volume, v ∈ Ω → HasFDerivAt f (g v) v := by
  -- scalar and vector inequalities proved in an empty context
  have aux_vec : ∀ (m : ℕ) (a b c : Euclid m), ‖a - b‖ ^ 2 ≤ 2 * ‖c - a‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
    intro m a b c
    have htri : ‖a - b‖ ≤ ‖c - a‖ + ‖c - b‖ := by
      calc ‖a - b‖ = ‖(c - b) - (c - a)‖ := by congr 1; abel
        _ ≤ ‖c - b‖ + ‖c - a‖ := norm_sub_le _ _
        _ = ‖c - a‖ + ‖c - b‖ := add_comm _ _
    nlinarith [norm_nonneg (a - b), norm_nonneg (c - a), norm_nonneg (c - b),
      sq_nonneg (‖c - a‖ - ‖c - b‖)]
  have aux_div : ∀ (d ω C X : ℝ) (m : ℕ), 0 < d → 0 < ω →
      (d / 2) ^ m * ω * X ≤ 4 * (C * d ^ (m + 1)) → X ≤ 2 ^ (m + 2) * C / ω * d := by
    intro d ω C X m hd hω h
    have hpos : 0 < (d / 2) ^ m * ω := by positivity
    have e : 4 * (C * d ^ (m + 1)) = (d / 2) ^ m * ω * (2 ^ (m + 2) * C / ω * d) := by
      rw [div_pow, pow_succ, pow_succ 2 (m + 1), pow_succ 2 m]
      field_simp
      ring
    rw [e] at h
    exact le_of_mul_le_mul_left h hpos
  have aux_eps : ∀ (M ε t : ℝ), 0 ≤ M → 0 < ε → 0 ≤ t → t < ε ^ 2 / (M + 1) → M * t < ε ^ 2 := by
    intro M ε t hM hε ht h
    have h1 : M * t ≤ M * (ε ^ 2 / (M + 1)) := by gcongr
    have h2 : M * (ε ^ 2 / (M + 1)) < ε ^ 2 := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg ε, sq_pos_of_pos hε]
    linarith
  intro n k f Ω C s₁ hn hΩ hC hs₁ hcamp
  have : Nontrivial (Euclid n) := by
    have : 0 < Module.finrank ℝ (Euclid n) := by simp [hn]
    exact Module.nontrivial_of_finrank_pos this
  obtain ⟨G, hG⟩ : ∃ G : Set (Euclid n), G = {v | v ∈ Ω ∧ (DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        ENNReal.ofReal (C * s ^ (n + 1)))} := ⟨_, rfl⟩
  have hnull : volume (Ω \ G) = 0 := by
    rw [ae_iff] at hcamp
    refine measure_mono_null (fun v hv => ?_) hcamp
    rw [hG] at hv
    exact fun h => hv.2 ⟨hv.1, h hv.1⟩
  have hGmem : ∀ v ∈ G, v ∈ Ω ∧ DifferentiableAt ℝ f v ∧ ∀ s : ℝ, 0 < s → s ≤ s₁ →
      ∫⁻ w in ball v s, ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f w - fderiv ℝ f v) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        ENNReal.ofReal (C * s ^ (n + 1)) := fun v hv => by rw [hG] at hv; exact hv
  clear hcamp hG
  have hHSnn : ∀ A : Euclid n →L[ℝ] Euclid k,
      0 ≤ ∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 :=
    fun A => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hop : ∀ A : Euclid n →L[ℝ] Euclid k,
      ‖A‖ ^ 2 ≤ ∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
    intro A
    have hbound : ‖A‖ ≤ Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
      have hx : x = ∑ i : Fin n, x i • EuclideanSpace.single i (1 : ℝ) := by
        ext j; simp [Pi.single_apply]
      calc ‖A x‖ = ‖∑ i : Fin n, x i • A (EuclideanSpace.single i (1 : ℝ))‖ := by
            conv_lhs => rw [hx]
            simp [map_sum, map_smul]
        _ ≤ ∑ i : Fin n, ‖x i‖ * ‖A (EuclideanSpace.single i (1 : ℝ))‖ := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            rw [norm_smul]
        _ ≤ Real.sqrt (∑ i : Fin n, ‖x i‖ ^ 2) *
              Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
        _ = Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) * ‖x‖ := by
            rw [EuclideanSpace.norm_eq, mul_comm]
    calc ‖A‖ ^ 2 ≤ (Real.sqrt (∑ i : Fin n, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ^ 2 := by
          gcongr
      _ = _ := Real.sq_sqrt (hHSnn A)
  have hmeas : ∀ A : Euclid n →L[ℝ] Euclid k, Measurable fun w => ENNReal.ofReal
      (∑ i : Fin n, ‖(fderiv ℝ f w - A) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro A
    have hc : Continuous fun B : Euclid n →L[ℝ] Euclid k =>
        ∑ i : Fin n, ‖B (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by fun_prop
    exact ENNReal.measurable_ofReal.comp (hc.measurable.comp ((measurable_fderiv ℝ f).sub_const A))
  have hωpos : (0 : ℝ≥0∞) < volume (ball (0 : Euclid n) 1) := measure_ball_pos _ _ one_pos
  have hωfin : volume (ball (0 : Euclid n) 1) ≠ ∞ := measure_ball_lt_top.ne
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Euclid n) 1)).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ ENNReal.toReal_pos hωpos.ne' hωfin
  have hωeq : volume (ball (0 : Euclid n) 1) = ENNReal.ofReal ω := by
    rw [hωdef]; exact (ENNReal.ofReal_toReal hωfin).symm
  -- pointwise inequality for the Hilbert–Schmidt squares
  have hpt : ∀ v₁ v₂ w : Euclid n,
      ENNReal.ofReal (∑ i : Fin n, ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        2 * ENNReal.ofReal (∑ i : Fin n,
          ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * ENNReal.ofReal (∑ i : Fin n,
          ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
    intro v₁ v₂ w
    have hreal : ∑ i : Fin n, ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤
        2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
        2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ => by
        simpa only [sub_apply] using aux_vec k
          (fderiv ℝ f v₁ (EuclideanSpace.single i 1))
          (fderiv ℝ f v₂ (EuclideanSpace.single i 1)) (fderiv ℝ f w (EuclideanSpace.single i 1))
    calc _ ≤ ENNReal.ofReal
          (2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
          2 * (∑ i : Fin n, ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
          simp
  -- Hölder estimate on G
  have hHolder : ∀ v₁ ∈ G, ∀ v₂ ∈ G, 0 < dist v₁ v₂ → dist v₁ v₂ ≤ s₁ →
      ‖fderiv ℝ f v₁ - fderiv ℝ f v₂‖ ^ 2 ≤ 2 ^ (n + 2) * C / ω * dist v₁ v₂ := by
    intro v₁ h₁ v₂ h₂ hd hds
    have hm1 : dist (midpoint ℝ v₁ v₂) v₁ = dist v₁ v₂ / 2 := by
      rw [dist_midpoint_left, Real.norm_eq_abs, abs_two]; ring
    have hm2 : dist (midpoint ℝ v₁ v₂) v₂ = dist v₁ v₂ / 2 := by
      rw [dist_midpoint_right, Real.norm_eq_abs, abs_two]; ring
    have hsub1 : ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2) ⊆ ball v₁ (dist v₁ v₂) :=
      ball_subset_ball' (by rw [hm1]; linarith)
    have hsub2 : ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2) ⊆ ball v₂ (dist v₁ v₂) :=
      ball_subset_ball' (by rw [hm2]; linarith)
    have hint : volume (ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2)) * ENNReal.ofReal (∑ i : Fin n,
        ‖(fderiv ℝ f v₁ - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ≤
        4 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) := by
      rw [mul_comm, ← setLIntegral_const]
      calc _ ≤ ∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), (2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
            2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
            lintegral_mono fun w => hpt v₁ v₂ w
        _ = (∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            ∫⁻ w in ball (midpoint ℝ v₁ v₂) (dist v₁ v₂ / 2), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            lintegral_add_left ((hmeas _).const_mul 2) _
        _ ≤ (∫⁻ w in ball v₁ (dist v₁ v₂), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            ∫⁻ w in ball v₂ (dist v₁ v₂), 2 * ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) :=
            add_le_add (lintegral_mono_set hsub1) (lintegral_mono_set hsub2)
        _ = 2 * (∫⁻ w in ball v₁ (dist v₁ v₂), ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₁) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) +
            2 * ∫⁻ w in ball v₂ (dist v₁ v₂), ENNReal.ofReal (∑ i : Fin n,
              ‖(fderiv ℝ f w - fderiv ℝ f v₂) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
            rw [lintegral_const_mul _ (hmeas _), lintegral_const_mul _ (hmeas _)]
        _ ≤ 2 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) + 2 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) :=
            by
              gcongr
              · exact (hGmem v₁ h₁).2.2 _ hd hds
              · exact (hGmem v₂ h₂).2.2 _ hd hds
        _ = 4 * ENNReal.ofReal (C * dist v₁ v₂ ^ (n + 1)) := by ring
    rw [Measure.addHaar_ball _ _ (by linarith : (0 : ℝ) ≤ dist v₁ v₂ / 2), finrank_euclideanSpace_fin, hωeq,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hint
    exact (hop _).trans (aux_div _ _ _ _ n hd hω hint)
  -- uniform continuity of the derivative on G
  have hUC : UniformContinuousOn (fderiv ℝ f) G := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    have hM0 : 0 ≤ 2 ^ (n + 2) * C / ω := by positivity
    refine ⟨min s₁ (ε ^ 2 / (2 ^ (n + 2) * C / ω + 1)),
      lt_min hs₁ (div_pos (pow_pos hε 2) (by linarith)), fun a ha b hb hab => ?_⟩
    rcases (dist_nonneg : 0 ≤ dist a b).lt_or_eq with hpos | hzero
    · have h1 := hHolder a ha b hb hpos (hab.le.trans (min_le_left _ _))
      have h3 : ‖fderiv ℝ f a - fderiv ℝ f b‖ ^ 2 < ε ^ 2 :=
        lt_of_le_of_lt h1 (aux_eps _ _ _ hM0 hε dist_nonneg (lt_of_lt_of_le hab (min_le_right _ _)))
      rw [dist_eq_norm]
      exact (abs_lt_of_sq_lt_sq' h3 hε.le).2
    · have : a = b := dist_eq_zero.1 hzero.symm
      subst this
      simpa using hε
  -- density of G in Ω
  have hdense : Ω ⊆ closure G := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hsub : ball x ε ∩ Ω ⊆ Ω \ G := fun y hy => ⟨hy.2, fun hyG => by
      have := hcon y hyG
      have hy1 : dist y x < ε := hy.1
      rw [dist_comm] at hy1
      exact absurd hy1 (not_lt.2 this)⟩
    have hpos : 0 < volume (ball x ε ∩ Ω) :=
      (isOpen_ball.inter hΩ).measure_pos _ ⟨x, mem_ball_self hε, hx⟩
    exact absurd (measure_mono_null hsub hnull) hpos.ne'
  -- the continuous extension
  have hlim : ∀ x ∈ Ω, ∃ y, Tendsto (fderiv ℝ f) (𝓝[G] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[G] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hdense hx)
    have hc : Cauchy (map (fderiv ℝ f) (𝓝[G] x)) := by
      rw [Metric.cauchy_iff]
      refine ⟨inferInstance, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC ε hε
      refine ⟨fderiv ℝ f '' (G ∩ ball x (δ / 2)), ?_, ?_⟩
      · rw [mem_map]
        refine mem_of_superset (inter_mem_nhdsWithin G (ball_mem_nhds x (half_pos hδ))) ?_
        intro y hy
        exact ⟨y, hy, rfl⟩
      · rintro _ ⟨a, ⟨haG, hax⟩, rfl⟩ _ ⟨b, ⟨hbG, hbx⟩, rfl⟩
        refine hδ' a haG b hbG ?_
        rw [mem_ball] at hax hbx
        calc dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
          _ < δ / 2 + δ / 2 := add_lt_add hax hbx
          _ = δ := by ring
    obtain ⟨y, hy⟩ := CompleteSpace.complete hc
    exact ⟨y, hy⟩
  refine ⟨extendFrom G (fderiv ℝ f), continuousOn_extendFrom hdense hlim, ?_⟩
  have hext := extendFrom_extends hUC.continuousOn
  rw [ae_iff]
  refine measure_mono_null (fun v hv => ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hv
  refine ⟨hv.1, fun hvG => hv.2 ?_⟩
  rw [hext v hvG]
  exact (hGmem v hvG).2.1.hasFDerivAt

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
