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
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- **Approximate tangent spaces under dilation** (Simon Ch. 3, 1.4).  For `c > 0` the blow-ups
of `c⁻¹M = {x : cx ∈ M}` at `z` are blow-ups of `M` at `cz`: `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)`, as
`(cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z)`.  Since `cr ↓ 0` as `r ↓ 0`, the limits defining `Q` as the
approximate tangent space of `M` at `cz` give the limits for `c⁻¹M` at `z`. -/
theorem Submission.approx_tangent_space_smul_preimage : ∀ (P n : ℕ) (M : Set (Euclid P)) (c : ℝ) (z : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < c → HasApproximateTangentSpaceAt n M (c • z) Q → HasApproximateTangentSpaceAt n ((fun x => c • x) ⁻¹' M) z Q := by
  intro P n M c z Q hc hT
  have hc0 : c ≠ 0 := hc.ne'
  -- `η_{cz,cr}(m) = (cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z) = η_{z,r}(c⁻¹m)`
  have hη : ∀ (r : ℝ) (m : Euclid P), Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) m =
      Poincare.SimonGMT.Chapter03.blowUpMap z r (c⁻¹ • m) := by
    intro r m
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, Poincare.SimonGMT.Chapter03.blowUpMap, mul_inv_rev,
      ← smul_smul, smul_sub c⁻¹, inv_smul_smul₀ hc0]
  -- `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)` for every `r`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap z r '' ((fun x => c • x) ⁻¹' M) =
      Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) '' M := by
    intro r
    ext y
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨c • m', hm', by rw [hη, inv_smul_smul₀ hc0]⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c⁻¹ • m, ?_, (hη r m).symm⟩
      show c • c⁻¹ • m ∈ M
      rwa [smul_inv_smul₀ hc0]
  -- `r ↦ cr` tends to `0` within `(0, ∞)`: it is continuous, vanishes at `0` and is positive
  -- for `r > 0`
  have hφ : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := (continuous_const_mul c).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  -- the limit at `cz` along `cr ↓ 0` is the limit at `z` along `r ↓ 0`
  refine ⟨hT.1, fun f => ((hT.2 f).comp hφ).congr fun r => ?_⟩
  rw [Function.comp_apply, hset r]

/-- **Dilating an integer multiplicity triple** (Simon Ch. 6, 3.1 and 2.23).  For `c > 0` and
`T x = c • x`, the triple `(T⁻¹M, θ ∘ T, ξ ∘ T)` is again integer multiplicity in `ℝᴾ`.  By the
change of variables `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M`, null sets, local integrability and
`Hⁿ⌞M`-a.e. statements transfer through the measurable embedding `T`; the maps `c⁻¹ • Fⱼ`
parametrize `T⁻¹M`, and approximate tangent spaces are dilation invariant. -/
theorem Submission.imrep_univ_smul_rescale_exists : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x) := by
  intro P n R c hc
  have hc0 : c ≠ 0 := hc.ne'
  -- `T x = c • x` is a homeomorphism of `ℝᴾ`, hence measurable and a measurable embedding
  have hT : Measurable (fun x : Euclid P => c • x) := measurable_const_smul c
  have hTemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc0).measurableEmbedding
  -- (CV): `T_#(Hⁿ⌞T⁻¹S) = c⁻ⁿ Hⁿ⌞S` and the lower-integral change of variables, for every `S`
  have hCV := Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
  -- (∗) `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M` for `M = R.carrier`
  have hstar := (hCV R.carrier).1
  refine ⟨{ carrier := (fun x : Euclid P => c • x) ⁻¹' R.carrier
            mult := fun x => R.mult (c • x)
            orient := fun x => R.orient (c • x)
            measurableSet_carrier := hT R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp hT
            mult_pos := fun x hx => R.mult_pos (c • x) hx
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl⟩
  · -- rectifiability: `T⁻¹M ⊆ T⁻¹M₀ ∪ ⋃ⱼ range (c⁻¹ • Fⱼ)` with `Hⁿ(T⁻¹M₀) = 0`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun x : Euclid P => c • x) ⁻¹' M₀, ?_, fun j w => c⁻¹ • F j w, fun j => ?_, ?_⟩
    · -- evaluate `T_#(Hⁿ⌞T⁻¹M₀) = c⁻ⁿ Hⁿ⌞M₀` on `univ`
      have h := congrArg (fun μ : Measure (Euclid P) => μ univ) (hCV M₀).1
      simp only at h
      rwa [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.smul_apply, Measure.restrict_apply_univ, hM₀, smul_zero] at h
    · -- `c⁻¹ • Fⱼ` is `‖c⁻¹‖₊ Kⱼ`-Lipschitz
      obtain ⟨K, hK⟩ := hF j
      exact ⟨‖c⁻¹‖₊ * K, (lipschitzWith_smul c⁻¹).comp hK⟩
    · -- if `c • z = Fⱼ w` then `z = c⁻¹ • Fⱼ w`
      intro z hz
      rcases hcover hz with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, w, by simp only [hw, inv_smul_smul₀ hc0]⟩)
  · -- local integrability: `T⁻¹M ∩ K = T⁻¹(M ∩ T(K))` with `T(K)` compact
    intro K hK _
    have hTK : IsCompact ((fun x : Euclid P => c • x) '' K) := hK.image (continuous_const_smul c)
    have hset : (fun x : Euclid P => c • x) ⁻¹' R.carrier ∩ K =
        (fun x : Euclid P => c • x) ⁻¹' (R.carrier ∩ (fun x : Euclid P => c • x) '' K) := by
      rw [preimage_inter, hTemb.injective.preimage_image]
    rw [hset, (hCV (R.carrier ∩ (fun x : Euclid P => c • x) '' K)).2.1 fun y => (R.mult y : ℝ≥0∞)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (R.locallyIntegrable_mult _ hTK (subset_univ _))
  · -- `ξ` is a.e.-strongly measurable for `c⁻ⁿ Hⁿ⌞M = T_#(Hⁿ⌞T⁻¹M)`; compose with `T`
    have h := R.aestronglyMeasurable_orient.smul_measure (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar] at h
    exact h.comp_aemeasurable hT.aemeasurable
  · -- the orientation statement holds `T_#(Hⁿ⌞T⁻¹M)`-a.e., i.e. at `c • z` for a.e. `z ∈ T⁻¹M`;
    -- there `Q` is also the approximate tangent space of `T⁻¹M` at `z`
    have h := Measure.ae_smul_measure R.orients (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar, hTemb.ae_map_iff] at h
    filter_upwards [h] with z ⟨Q, hQ, hξ⟩
    exact ⟨Q, Submission.approx_tangent_space_smul_preimage P n R.carrier c z Q hc hQ, hξ⟩
/-- **A cone takes equal values on dilated test forms** (Simon 7.3.1(2), via 6.2.23).
If `C ∈ 𝒟ₙ(ℝᴾ)` is a cone, `λ > 0` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)` defines a test
form with `C(ω') = C(ω)`.  As `η_{0,λ}(ℝᴾ) = ℝᴾ`, the cone property `η_{0,λ#}C = C` reads
`C(η_{0,λ}^# ω) = C(ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.cone_current_apply_dilation_pullback : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsConeCurrent C → ∀ lam : ℝ, 0 < lam → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) ∧ C ω' = C ω := by
  intro P n C hC lam hlam ω
  -- Step 1: the cone property `η_{0,λ#}C(ω) = C(ω)`.
  have hcone := hC lam hlam ω
  -- Step 2: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h] at hcone
  -- Steps 3–4: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω')` for the affine pullback `ω'` of `ω`,
  -- so `C(ω') = C(ω)`.
  refine ⟨_, fun y => ?_, hcone⟩
  -- Step 5: `ω'(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Action and weight of a dilated triple** (Simon 6.3.1 (‡) and Ch. 4, 1.1, under
`x ↦ cx`; used for the cone `C` of 7.3.1(2)).  If `c > 0` and `R' = (M', θ', ξ')` is
`R = (M, θ, ξ)` pulled back by `x ↦ cx`, i.e. `M' = {x : cx ∈ M}`, `θ'(x) = θ(cx)` and
`ξ'(x) = ξ(cx)`, then `τ(R')(ω) = τ(R)(ω_c)` with `ω_c(y) = c⁻ⁿ ω(c⁻¹y)` for every `n`-form `ω`,
and `μ_{R'}(A) = c⁻ⁿ μ_R(cA)` for every Borel `A`.  Both follow from the change of variables
`∫_{M'} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ`. -/
theorem Submission.imrep_smul_rescale_action_measure : ∀ (P n : ℕ) (R R' : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → R'.carrier = (fun x => c • x) ⁻¹' R.carrier → (∀ x, R'.mult x = R.mult (c • x)) → (∀ x, R'.orient x = R.orient (c • x)) → (∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action (fun y => (c⁻¹ ^ n) • ω (c⁻¹ • y))) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R'.measure A = ENNReal.ofReal (c⁻¹ ^ n) * R.measure ((fun x => c • x) '' A) := by
  intro P n R R' c hc hcar hmult horient
  -- `T x = cx` is a measurable embedding with `c⁻¹ (cz) = z`.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    measurableEmbedding_const_smul₀ hc.ne'
  have hinv : ∀ z : Euclid P, c⁻¹ • c • z = z := fun z => by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- Step 1: `R'.action ω = ∫_{T⁻¹M} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ` for
    -- `g(y) = θ(y) ξ(y)(ω(c⁻¹y))`.
    have hcv := (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      R.carrier).2.2 fun y => (R.mult y : ℝ) * R.orient y (ω (c⁻¹ • y))
    simp only [hinv] at hcv
    unfold IMRep.action
    rw [hcar]
    simp only [hmult, horient]
    -- Step 2: move `c⁻ⁿ` inside the integral and use the linearity of `ξ(y)`.
    rw [hcv, ← integral_const_mul]
    congr 1
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  · -- Step 3: `R'.measure A = ∫⁻_{A ∩ M'} θ(c·) dHⁿ`, and `A ∩ M' = T⁻¹(cA ∩ M)`.
    have hTA : MeasurableSet ((fun x : Euclid P => c • x) '' A) := hT.measurableSet_image.2 hA
    have hset : A ∩ R'.carrier =
        (fun x : Euclid P => c • x) ⁻¹' ((fun x : Euclid P => c • x) '' A ∩ R.carrier) := by
      rw [preimage_inter, preimage_image_eq _ hT.injective, hcar]
    unfold IMRep.measure
    rw [withDensity_apply _ hA, withDensity_apply _ hTA, Measure.restrict_restrict hA,
      Measure.restrict_restrict hTA, hset]
    simp only [hmult]
    -- Step 4: the lower-integral change of variables on `cA ∩ M`.
    exact (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      ((fun x : Euclid P => c • x) '' A ∩ R.carrier)).2.1 fun y => (R.mult y : ℝ≥0∞)
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
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

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

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
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
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl
/-- **Every current in `η(U)` is a blow-up**, `η = η_{x,λ}`, `λ > 0` (Simon Ch. 6, 2.23 and 3.9
for `η⁻¹`; used for the minimality of `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt
lines 326–338): every `S' ∈ 𝒟ₙ(η(U))` is `η_{x,λ#}S''` for some `S'' ∈ 𝒟ₙ(U)`, integer
multiplicity whenever `S'` is.  `κ = η_{−λ⁻¹x,λ⁻¹}` inverts `η`, so `κ(η(U)) = U`, and `S''` is
`κ_#S'` restricted to `U`: `dtc_blowUp_testForm_corr` for `η` and for `κ` gives
`η_#S''(ω) = λ⁻ⁿ κ_#S'(ω ∘ η) = λ⁻ⁿ λⁿ S'(ω)`, and a representation of `κ_#S'` in
`κ(η(U)) = U` (`dtc_blowUp_imrep`) represents `S''`. -/
theorem Submission.dtc_blowUp_preimage : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (S' : GeometricCurrentOn (dilation x lam '' U) n), ∃ S'' : GeometricCurrentOn U n, blowUp S'' x lam hlam.ne' = S' ∧ (IsIntegerMultiplicity S' → IsIntegerMultiplicity S'') := by
  intro P n U x lam hlam S'
  have hlam' : 0 < lam⁻¹ := inv_pos.mpr hlam
  -- `κ = η_{−λ⁻¹x,λ⁻¹}`, `κ(z) = x + λz`, is a two-sided inverse of `η = η_{x,λ}`
  have hκη : ∀ y, dilation (-(lam⁻¹ • x)) lam⁻¹ (dilation x lam y) = y := fun y => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hηκ : ∀ z, dilation x lam (dilation (-(lam⁻¹ • x)) lam⁻¹ z) = z := fun z => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hdom : dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) = U := by
    rw [image_image]
    simp only [hκη, image_id']
  have hUV : U ⊆ dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) := hdom.superset
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hblow' := (Submission.dtc_blowUp_testForm_corr P n (dilation x lam '' U)
    (-(lam⁻¹ • x)) lam⁻¹ hlam').2.2
  -- `S'' := κ_#S'`, restricted from `κ(η(U)) = U` to `U`
  refine ⟨(blowUp S' (-(lam⁻¹ • x)) lam⁻¹ hlam'.ne').restrictDomain hUV, ?_, ?_⟩
  · -- `η_#S''(ω) = λ⁻ⁿ S''(ω ∘ η)` and `κ_#S'(ω ∘ η) = λⁿ S'(ω)`, as `ω ∘ η ∘ κ = ω`
    ext ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow _ ω ω' hω', GeometricCurrentOn.restrictDomain_apply,
      hblow' S' (testFormOnInclusion hUV n ω') ω fun z => by
        rw [testFormOnInclusion_coe, hω', hηκ],
      ← mul_assoc, ← mul_pow, inv_inv, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]
  · -- a representation of `κ_#S'` in `κ(η(U)) = U` is one in `U`, and it represents `S''`
    rintro ⟨R₁, hR₁⟩
    obtain ⟨R₂, hR₂, -⟩ := Submission.dtc_blowUp_imrep P n (dilation x lam '' U) S'
      (-(lam⁻¹ • x)) lam⁻¹ hlam' R₁ hR₁
    exact ⟨{ R₂ with
        carrier_subset := R₂.carrier_subset.trans hdom.subset
        locallyIntegrable_mult := fun K hK hKU =>
          R₂.locallyIntegrable_mult K hK (hKU.trans hUV) },
      fun ω => hR₂ (testFormOnInclusion hUV n ω)⟩

/-- **Blow-ups preserve minimality** (Simon 7.1.1, chapter-07.txt lines 12–18, for `η = η_{x,λ}`,
`λ > 0`; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337): if `T` is
minimizing in `A`, then `η_#T` is minimizing in `η(A)`.

`η_#T` is integer multiplicity (`dtc_blowUp_imrep`).  A competitor `S'` for `η_#T` on
`W' ⊂⊂ η(U)` is `η_#S''` with `S''` integer multiplicity (`dtc_blowUp_preimage`), and `S''` is a
competitor for `T` on `W = η⁻¹(W') ⊂⊂ U`: `∂S'' = ∂T` and
`spt(S'' − T) = η⁻¹(spt(S' − η_#T)) ⊆ A ∩ W` (`dtc_blowUp_algebra`).  So
`M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')` (`dtc_blowUp_massOn_image`). -/
theorem Submission.dtc_blowUp_isMinimizingIn : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A) := by
  intro P n U A T x lam hlam hT
  obtain ⟨⟨R, hR⟩, hmin⟩ := hT
  obtain ⟨hsub, hinj, hspt, hbdry⟩ := Submission.dtc_blowUp_algebra P U x lam hlam
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨?_, fun W' S' hW'o hW'c hS'im hS'bd hS'c hS'A => ?_⟩
  · -- `η_#T` is integer multiplicity
    obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P n U T x lam hlam R hR
    exact ⟨R', hR'⟩
  -- `S' = η_#S''` with `S''` integer multiplicity
  obtain ⟨S'', rfl, hS''im⟩ := Submission.dtc_blowUp_preimage P n U x lam hlam S'
  -- `W = η⁻¹(W')` is open and `W ⊂⊂ U`, since `closure W = η⁻¹(closure W')` and `η⁻¹(η(U)) = U`
  have hWo : IsOpen (dilation x lam ⁻¹' W') := by
    rw [← he]
    exact hW'o.preimage e.continuous
  have hWc : CompactlyContained (dilation x lam ⁻¹' W') U := by
    obtain ⟨hc, hsub'⟩ := hW'c
    rw [← he] at hsub' ⊢
    refine ⟨?_, ?_⟩ <;> rw [← e.preimage_closure]
    · exact e.isCompact_preimage.2 hc
    · exact (preimage_mono hsub').trans (e.preimage_image U).subset
  -- `∂S'' = ∂T`: `η_#(∂S'') = ∂S' = ∂(η_#T) = η_#(∂T)` and `η_#` is injective
  have hbd : SameBoundary S'' T := by
    cases n with
    | zero => trivial
    | succ m =>
      show S''.boundary = T.boundary
      apply hinj
      rw [← hbdry, ← hbdry]
      exact hS'bd
  -- `spt(S' − η_#T) = η(spt(S'' − T))`, so `spt(S'' − T)` is compact and lies in `A ∩ W`
  have hspt' : (blowUp S'' x lam hlam.ne' - blowUp T x lam hlam.ne').support =
      dilation x lam '' (S'' - T).support := by
    rw [← hsub, hspt]
  rw [hspt', ← he] at hS'c hS'A
  have hc : IsCompact (S'' - T).support := e.isCompact_image.1 hS'c
  have hA : (S'' - T).support ⊆ A ∩ dilation x lam ⁻¹' W' := by
    intro y hy
    obtain ⟨⟨a, ha, hay⟩, hyW'⟩ := hS'A (mem_image_of_mem e hy)
    rw [← he]
    exact ⟨e.injective hay ▸ ha, hyW'⟩
  -- `M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')`, as `η(W) = W'`
  have hle := hmin _ S'' hWo hWc (hS''im hS'im) hbd hc hA
  have hW' : dilation x lam '' (dilation x lam ⁻¹' W') = W' := by
    rw [← he]
    exact e.image_preimage W'
  have hmT := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W')
  have hmS := Submission.dtc_blowUp_massOn_image P n U S'' x lam hlam (dilation x lam ⁻¹' W')
  rw [hW'] at hmT hmS
  rw [hmT, hmS]
  gcongr

/-- **Scaling of blow-ups** `η_{x,λ#}T`, `η = η_{x,λ}`, `λ > 0` (proof of Simon 7.3.1,
chapter-07.txt lines 326–338; push-forward 6.2.23 and 6.3.3–6.3.9): (1) the mass scaling
`M_{η(W)}(η_#T) = λ⁻ⁿ M_W(T)` of (1) there (`dtc_blowUp_massOn_image`); (2) a representation
`(M, θ, ξ)` of `T` pushes forward to one of `η_#T` with `μ_{η_#T}(B) = λ⁻ⁿ μ_T(η⁻¹(B))`
(`dtc_blowUp_imrep`); (3) `η_#T` is minimizing in `η(A)` if `T` is minimizing in `A`
(`dtc_blowUp_isMinimizingIn`).  The hypotheses `U` open and `n > 0` are not needed. -/
theorem Submission.dtc_blowUp_scaling : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsOpen U → 0 < n → (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W) ∧ (∀ R : IMRep U n, R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) ∧ (IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)) := by
  intro P n U A T x lam hlam _ _
  exact ⟨Submission.dtc_blowUp_massOn_image P n U T x lam hlam,
    Submission.dtc_blowUp_imrep P n U T x lam hlam,
    Submission.dtc_blowUp_isMinimizingIn P n U A T x lam hlam⟩
/-- **The weight of a cone is homogeneous of degree `n`** (proof of Simon 7.4.5,
chapter-07.txt lines 697–699, "by virtue of the fact that `C` is a cone").  If the cone `C` is
represented by `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` and `λ > 0`, then `μ(λA) = λⁿ μ(A)` for
every Borel `A`.  The dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, and
`R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·)) = C(λ⁻ⁿ ω(λ⁻¹·)) = C(ω)` as `η_{0,λ#}C = C`, so `R_λ` represents `C`.
By the uniqueness of the weight (Simon Ch. 6, 3.2(3)), `μ(A) = μ_{R_λ}(A) = λ⁻ⁿ μ(λA)`. -/
theorem Submission.cone_current_imrep_measure_smul_image : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n C R hC hR lam hlam A hA
  -- Step 1: the dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, with
  -- `R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·))` for every form `ω` and `μ_{R_λ}(A) = λ⁻ⁿ μ(λA)` for Borel `A`
  obtain ⟨Rl, hcar, hmult, horient⟩ := Submission.imrep_univ_smul_rescale_exists P n R lam hlam
  obtain ⟨haction, hmeasure⟩ :=
    Submission.imrep_smul_rescale_action_measure P n R Rl lam hlam hcar hmult horient
  -- Step 2: `R_λ` represents `C`: `C(ω) = C(ω') = R(ω') = R_λ(ω)` for `ω' = λ⁻ⁿ ω(λ⁻¹·)`
  have hRl : Rl.Represents C := by
    intro ω
    obtain ⟨ω', hω', hCω'⟩ := Submission.cone_current_apply_dilation_pullback P n C hC lam hlam ω
    rw [← hCω', hR ω', haction]
    congr 1
    funext y
    exact hω' y
  -- Step 3: the weight does not depend on the representation, so `μ_{R_λ} = μ` and
  -- `μ(A) = λ⁻ⁿ μ(λA)`
  have hA' := hmeasure A hA
  rw [Submission.imrep_measure_eq_of_represents_same_current P n univ C Rl R isOpen_univ hRl hR]
    at hA'
  -- Step 4: multiply by `λⁿ`, using `λⁿ λ⁻ⁿ = 1`
  have hpow : ENNReal.ofReal (lam ^ n) * ENNReal.ofReal (lam⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
      ENNReal.ofReal_one]
  rw [hA', ← mul_assoc, hpow, one_mul]

/-- **The ambient space and the calculus of the dilations** `η_{a,s}(v) = s⁻¹(v − a)`, `s > 0`,
and of the rescaled measures `ν^{a,s} = s⁻ⁿ η_{a,s#}ν` (used tacitly by Simon in the proof of
7.3.3(1), cf. (10) there, chapter-07.txt line 472): (1) `ℝᴾ` is an embedded `C²` submanifold of
itself (Simon Ch. 2, (4.1), with `ψ = id`); (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`;
(3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`; (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`;
(5) `η_{a,s}(ℝᴾ) = ℝᴾ` and `η_{a,s}` is open; (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`;
(7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`; (8) `ν^{0,1} = ν` and `η_{0,1}(A) = A`;
(9) `s⁻ⁿ η_{a,s#}(ν⌞B) = ν^{a,s}⌞η_{a,s}(B)` for Borel `B`.  All of this follows from `η_{a,s}`
being the affine homeomorphism `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`. -/
theorem Submission.idtp_fons_cc_ambient_calculus : (∀ P : ℕ, IsEmbeddedSubmanifold 2 P (univ : Set (Euclid P))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (A : Set (Euclid P)), 0 < s → MeasurableSet A → (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)) A = ENNReal.ofReal (s⁻¹ ^ n) * ν (dilation a s ⁻¹' A)) ∧ (∀ (P : ℕ) (a w : Euclid P) (s ρ : ℝ), 0 < s → dilation a s ⁻¹' ball w ρ = ball (a + s • w) (s * ρ)) ∧ (∀ (P : ℕ) (a c : Euclid P) (s ρ : ℝ), 0 < s → dilation a s '' ball c ρ = ball (dilation a s c) (ρ / s)) ∧ (∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s → dilation a s '' univ = univ ∧ ∀ A : Set (Euclid P), IsOpen A → IsOpen (dilation a s '' A)) ∧ (∀ (P : ℕ) (a y : Euclid P) (s t : ℝ) (A : Set (Euclid P)), 0 < s → 0 < t → dilation y t '' (dilation a s '' A) = dilation (a + s • y) (s * t) '' A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t → ENNReal.ofReal (t⁻¹ ^ n) • (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).map (dilation y t) = ENNReal.ofReal ((s * t)⁻¹ ^ n) • ν.map (dilation (a + s • y) (s * t))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)), ENNReal.ofReal ((1 : ℝ)⁻¹ ^ n) • ν.map (dilation 0 1) = ν ∧ ∀ A : Set (Euclid P), dilation (0 : Euclid P) 1 '' A = A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (B : Set (Euclid P)), 0 < s → MeasurableSet B → ENNReal.ofReal (s⁻¹ ^ n) • (ν.restrict B).map (dilation a s) = (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).restrict (dilation a s '' B)) := by
  -- Step 0: `η_{a,s}(v) = s⁻¹(v − a)`; for `s > 0` it is the affine homeomorphism
  -- `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`, hence measurable, injective and open
  have hdil : ∀ (P : ℕ) (a : Euclid P) (s : ℝ) (v : Euclid P), dilation a s v = s⁻¹ • (v - a) := by
    intro P a s v
    show -(s⁻¹ • a) + s⁻¹ • v = s⁻¹ • (v - a)
    rw [smul_sub, neg_add_eq_sub]
  have hmeas : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), Measurable (dilation a s) := fun P a s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  have hhomeo : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s →
      ∃ h : Euclid P ≃ₜ Euclid P, ⇑h = dilation a s := by
    intro P a s hs
    refine ⟨(Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs.ne')).trans
      (Homeomorph.addLeft (-(s⁻¹ • a))), ?_⟩
    funext v
    simp [dilation, dilationCLM]
  -- Step 6 (pointwise): `η_{y,t} ∘ η_{a,s} = η_{a+sy,st}`, as `(st)⁻¹ = t⁻¹s⁻¹`
  have hcomp : ∀ (P : ℕ) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t →
      dilation y t ∘ dilation a s = dilation (a + s • y) (s * t) := by
    intro P a y s t hs ht
    funext v
    rw [Function.comp_apply, hdil, hdil, hdil, mul_inv_rev, mul_smul, sub_add_eq_sub_sub,
      smul_sub s⁻¹ (v - a) (s • y), inv_smul_smul₀ hs.ne']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `ℝᴾ` is a `C²` submanifold of itself: `V = W = ℝᴾ`, `ψ = id`
    intro P y _
    refine ⟨univ, univ, id, isOpen_univ, isOpen_univ, mem_univ y, contDiffOn_id, injOn_id univ,
      by simp, fun K _ hK => by simpa using hK, fun z _ => ?_⟩
    rw [fderiv_id, ContinuousLinearMap.coe_id']
    exact injective_id
  · -- (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`
    intro P n ν a s A _ hA
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hmeas P a s) hA]
  · -- (3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`, as `η_{a,s}(v) − w = s⁻¹(v − (a + sw))`
    intro P a w s ρ hs
    ext v
    have hv : dilation a s v - w = s⁻¹ • (v - (a + s • w)) := by
      rw [hdil, sub_add_eq_sub_sub, smul_sub s⁻¹ (v - a) (s • w), inv_smul_smul₀ hs.ne']
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hv, norm_smul, norm_inv,
      Real.norm_of_nonneg hs.le, inv_mul_lt_iff₀ hs]
  · -- (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`: the image under `η_{a,s}` is the preimage
    -- under its inverse `u ↦ a + su`, and `a + su − c = s(u − η_{a,s}(c))`
    intro P a c s ρ hs
    rw [image_eq_preimage_of_inverse (f := dilation a s) (g := fun u => a + s • u)
      (fun v => show a + s • dilation a s v = v by rw [hdil, smul_inv_smul₀ hs.ne', add_sub_cancel])
      (fun u => show dilation a s (a + s • u) = u by
        rw [hdil, add_sub_cancel_left, inv_smul_smul₀ hs.ne'])]
    ext u
    have hu : a + s • u - c = s • (u - dilation a s c) := by
      rw [hdil, smul_sub, smul_inv_smul₀ hs.ne']
      abel
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hu, norm_smul,
      Real.norm_of_nonneg hs.le, lt_div_iff₀ hs, mul_comm]
  · -- (5) `η_{a,s}` is a homeomorphism: surjective and open
    intro P a s hs
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    rw [← hh]
    exact ⟨image_univ_of_surjective h.surjective, fun A hA => h.isOpenMap A hA⟩
  · -- (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`
    intro P a y s t A hs ht
    rw [← image_comp, hcomp P a y s t hs ht]
  · -- (7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`: `map_smul`, `map_map` and `t⁻ⁿs⁻ⁿ = (st)⁻ⁿ`
    intro P n ν a y s t hs ht
    rw [Measure.map_smul _ (hmeas P y t).aemeasurable, Measure.map_map (hmeas P y t) (hmeas P a s),
      hcomp P a y s t hs ht, smul_smul, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 ht.le) n),
      ← mul_pow, mul_inv_rev]
  · -- (8) `η_{0,1} = id`
    intro P n ν
    have h01 : dilation (0 : Euclid P) 1 = id := by
      funext v
      rw [hdil, inv_one, one_smul, sub_zero, id]
    refine ⟨?_, fun A => ?_⟩
    · rw [h01, Measure.map_id, inv_one, one_pow, ENNReal.ofReal_one, one_smul]
    · rw [h01, image_id]
  · -- (9) restriction commutes with the push-forward by the measurable embedding `η_{a,s}`,
    -- and `η_{a,s}⁻¹(η_{a,s}(B)) = B` by injectivity
    intro P n ν a s B hs _
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    have hemb : MeasurableEmbedding (dilation a s) := hh ▸ h.measurableEmbedding
    rw [Measure.restrict_smul, hemb.restrict_map, hemb.injective.preimage_image]

/-- **`n`-homogeneity of `f Hⁿ` for a dilation-invariant density `f`** (Simon Lemma 7.3.5,
chapter-07.txt lines 407–420, whose proof is "left to the reader": part (ii) of the invariance of
the mass measure `μ = Θ Hⁿ` of `S` when its density `Θ` is invariant under `w ↦ λw`, with an
arbitrary `f : ℝᴾ → [0, ∞]` in place of `ofReal ∘ Θ`).  If `λ > 0` and `f(λx) = f(x)` for all `x`,
then `(f Hⁿ)(λA) = λⁿ (f Hⁿ)(A)` for every Borel `A ⊆ ℝᴾ`.  `δ(x) = λx` is a homeomorphism, so
`λA = δ(A)` is Borel and `δ⁻¹(λA) = A`; the change of variables (ii) of
`Submission.euclid_hausdorff_dilation_change_of_variables` with `g = f` and `f ∘ δ = f` gives
`(f Hⁿ)(A) = λ⁻ⁿ (f Hⁿ)(λA)`, and `λⁿ λ⁻ⁿ = 1`. -/
theorem Submission.dimred_cs_mi_withDensity_dilate : ∀ (P n : ℕ) (f : Euclid P → ℝ≥0∞) (lam : ℝ), 0 < lam → (∀ x : Euclid P, f (lam • x) = f x) → ∀ A : Set (Euclid P), MeasurableSet A → (μHE[n] : Measure (Euclid P)).withDensity f ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * (μHE[n] : Measure (Euclid P)).withDensity f A := by
  intro P n f lam hlam hf A hA
  -- Step 1: `δ(x) = λx` is a homeomorphism, hence a measurable embedding: `D = δ(A)` is Borel and
  -- `δ⁻¹(D) = A` by injectivity.
  have hδ : MeasurableEmbedding (fun x : Euclid P => lam • x) :=
    (Homeomorph.smulOfNeZero lam hlam.ne').measurableEmbedding
  have hD : MeasurableSet ((fun x : Euclid P => lam • x) '' A) := hδ.measurableSet_image.2 hA
  have hpre : (fun x : Euclid P => lam • x) ⁻¹' ((fun x : Euclid P => lam • x) '' A) = A :=
    Set.preimage_image_eq A hδ.injective
  -- Steps 2–3: change of variables (ii) with `c = λ`, `M = D`, `g = f`; with `δ⁻¹(D) = A` and
  -- `f(λz) = f(z)` it reads `∫⁻_A f dHⁿ = λ⁻ⁿ ∫⁻_D f dHⁿ`.
  have h := (Submission.euclid_hausdorff_dilation_change_of_variables P n lam hlam
    ((fun x : Euclid P => lam • x) '' A)).2.1 f
  rw [hpre] at h
  simp only [hf] at h
  -- Steps 4–5: `ν(A) = λ⁻ⁿ ν(D)` by `withDensity_apply` (`A`, `D` Borel), and
  -- `ofReal(λⁿ) ofReal(λ⁻ⁿ) = ofReal((λλ⁻¹)ⁿ) = 1`.
  rw [withDensity_apply _ hD, withDensity_apply _ hA, h, ← mul_assoc,
    ← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
    ENNReal.ofReal_one, one_mul]

/-- **The domains `G = η_{x,λ}(B₂(0))` of the rescaled currents** (Simon 7.3.3, proof of 3.3(1),
item (9), chapter-07.txt lines 445–467: the limits of `η_{xᵢ,λᵢ#}T` with `λᵢ → λ > 0` live on
`η_{x,λ}(U)`).  For `λ > 0`: (a) `v ∈ G` iff `‖x + λv‖ < 2`; (b) `G` is open; (c) if `λ ≤ 1` and
`‖x‖ ≤ 1 − λ`, then `B₂(0) ⊆ G`, and `closedBall 0 R ⊆ G` whenever `λR ≤ 1`.
`η_{x,λ}(u) = λ⁻¹(u − x)` has inverse `v ↦ x + λv`, which gives (a); (b) follows from (a) by
`isOpen_lt`; (c) follows from (a) and `‖x + λv‖ ≤ ‖x‖ + λ‖v‖ ≤ 1 − λ + λ‖v‖`. -/
theorem Submission.idtp_fons_cc_psf_domain_geometry : ∀ (P : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ v : Euclid P, v ∈ dilation x lam '' ball 0 2 ↔ ‖x + lam • v‖ < 2) ∧ IsOpen (dilation x lam '' ball 0 2) ∧ (lam ≤ 1 → ‖x‖ ≤ 1 - lam → ball 0 2 ⊆ dilation x lam '' ball 0 2 ∧ ∀ R : ℝ, lam * R ≤ 1 → closedBall 0 R ⊆ dilation x lam '' ball 0 2) := by
  intro P x lam hlam
  -- Step 1: `η(u) = −λ⁻¹x + λ⁻¹u = λ⁻¹(u − x)`.
  have hη : ∀ u : Euclid P, dilation x lam u = lam⁻¹ • (u - x) := by
    intro u
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply]
    rw [neg_add_eq_sub, smul_sub]
  -- Steps 2–3, (a): `v = η(u)` iff `u = x + λv`, so `v ∈ η(B₂(0))` iff `‖x + λv‖ < 2`.
  have ha : ∀ v : Euclid P, v ∈ dilation x lam '' ball 0 2 ↔ ‖x + lam • v‖ < 2 := by
    intro v
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [hη, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
      exact mem_ball_zero_iff.1 hu
    · intro hv
      refine ⟨x + lam • v, mem_ball_zero_iff.2 hv, ?_⟩
      rw [hη, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
  refine ⟨ha, ?_, fun hlam1 hx => ⟨fun v hv => ?_, fun R hR v hv => ?_⟩⟩
  -- Step 4, (b): `G = {v | ‖x + λv‖ < 2}` is a strict sublevel set of a continuous function.
  · have hc : Continuous fun v : Euclid P => ‖x + lam • v‖ := by fun_prop
    rw [show dilation x lam '' ball 0 2 = {v | ‖x + lam • v‖ < 2} from Set.ext ha]
    exact isOpen_lt hc continuous_const
  -- Step 5, (c): `‖x + λv‖ ≤ ‖x‖ + λ‖v‖ < (1 − λ) + 2λ ≤ 2` for `‖v‖ < 2`.
  · have hv' : lam * ‖v‖ < lam * 2 := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hv) hlam
    rw [ha]
    calc ‖x + lam • v‖ ≤ ‖x‖ + ‖lam • v‖ := norm_add_le _ _
      _ = ‖x‖ + lam * ‖v‖ := by rw [norm_smul_of_nonneg hlam.le]
      _ < 2 := by linarith
  -- Step 6, (c): `‖x + λv‖ ≤ ‖x‖ + λ‖v‖ ≤ (1 − λ) + λR ≤ 2 − λ < 2` for `‖v‖ ≤ R`, `λR ≤ 1`.
  · have hv' : lam * ‖v‖ ≤ lam * R :=
      mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hv) hlam.le
    rw [ha]
    calc ‖x + lam • v‖ ≤ ‖x‖ + ‖lam • v‖ := norm_add_le _ _
      _ = ‖x‖ + lam * ‖v‖ := by rw [norm_smul_of_nonneg hlam.le]
      _ < 2 := by linarith
/-- **Finite positive total mass of the rescaled seed `μ₀` and of its rescalings; concentration of
`μ₀` on `B₂(0)`** (proof of Simon 7.3.3(1), chapter-07.txt lines 435–472: the rescaling and
translation to `U = B₂(0)` in (4) and the rescalings `η_{x,λ#}` of (10), at the level of weights).
If `r > 0` and `0 < μ(B_{2r}(z)) < ∞`, then `μ₀ = r⁻ⁿ η_{z,r#}(μ⌞B_{2r}(z))` has
`μ₀(ℝᴾ) = r⁻ⁿ μ(B_{2r}(z)) ∈ (0, ∞)` and `μ₀(ℝᴾ \ B₂(0)) = 0`, since `η_{z,r}⁻¹(B₂(0)) = B_{2r}(z)`;
and `μ₀^{x,λ} = λ⁻ⁿ η_{x,λ#}μ₀` has `μ₀^{x,λ}(ℝᴾ) = λ⁻ⁿ μ₀(ℝᴾ) ∈ (0, ∞)` for every `x` and
`λ > 0`.  Dilations are continuous, so `(c • η_#ν)(A) = c ν(η⁻¹(A))` for Borel `A`. -/
theorem Submission.idtp_fons_cc_psf_total_mass : ∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ (ball z (2 * r)) ≠ 0 → μ (ball z (2 * r)) ≠ ∞ → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → μ₀ univ ≠ 0 ∧ μ₀ univ ≠ ∞ ∧ μ₀ (ball (0 : Euclid P) 2)ᶜ = 0 ∧ ∀ (x : Euclid P) (lam : ℝ), 0 < lam → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ 0 ∧ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ ∞ := by
  intro P n μ μ₀ z r hr hB0 hBtop hμ₀
  -- Step 1: `η_{a,s}(u) = -(s⁻¹a) + s⁻¹u` is continuous, hence Borel measurable.
  have hmeas : ∀ (a : Euclid P) (s : ℝ), Measurable (dilation a s) := fun a s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  -- Step 2: `ofReal(s⁻ⁿ) ≠ 0` for `s > 0` (and `ofReal t ≠ ∞` for every `t`).
  have hc : ∀ s : ℝ, 0 < s → ENNReal.ofReal (s⁻¹ ^ n) ≠ 0 := fun s hs =>
    (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 hs) n)).ne'
  -- Step 3: `μ₀(ℝᴾ) = ofReal(r⁻ⁿ) μ(B_{2r}(z))`, a product of two elements of `(0, ∞)`.
  have huniv : μ₀ univ = ENNReal.ofReal (r⁻¹ ^ n) * μ (ball z (2 * r)) := by
    rw [hμ₀, Measure.smul_apply, Measure.map_apply (hmeas z r) MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]
  have h0 : μ₀ univ ≠ 0 := by
    rw [huniv]
    exact mul_ne_zero (hc r hr) hB0
  have htop : μ₀ univ ≠ ∞ := by
    rw [huniv]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop
  refine ⟨h0, htop, ?_, fun x lam hlam => ?_⟩
  -- Step 4: `η_{z,r}⁻¹(B₂(0)) = B_{2r}(z)`, as `‖r⁻¹(v - z)‖ < 2 ↔ ‖v - z‖ < 2r`; hence
  -- `μ₀(B₂(0)ᶜ) = ofReal(r⁻ⁿ) μ(B_{2r}(z)ᶜ ∩ B_{2r}(z)) = 0`.
  · have hball : dilation z r ⁻¹' ball (0 : Euclid P) 2 = ball z (2 * r) := by
      ext v
      have hv : dilation z r v = r⁻¹ • (v - z) := by
        simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_sub]
        abel
      rw [mem_preimage, mem_ball_zero_iff, hv, norm_smul, norm_inv, Real.norm_of_nonneg hr.le,
        mem_ball, dist_eq_norm, inv_mul_lt_iff₀ hr, mul_comm]
    rw [hμ₀, Measure.smul_apply, Measure.map_apply (hmeas z r) measurableSet_ball.compl,
      preimage_compl, hball, Measure.restrict_apply measurableSet_ball.compl, compl_inter_self,
      measure_empty, smul_zero]
  -- Step 5: `μ₀^{x,λ}(ℝᴾ) = ofReal(λ⁻ⁿ) μ₀(ℝᴾ)`, again a product of two elements of `(0, ∞)`.
  · have hmem : (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ =
        ENNReal.ofReal (lam⁻¹ ^ n) * μ₀ univ := by
      rw [Measure.smul_apply, Measure.map_apply (hmeas x lam) MeasurableSet.univ, preimage_univ,
        smul_eq_mul]
    rw [hmem]
    exact ⟨mul_ne_zero (hc lam hlam) h0, ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop⟩
/-- **Support relation for the rescaled measure `μ₀`** (proof of Simon 7.3.3, 3.3(1),
chapter-07.txt lines 445–467, the blow-ups `η_{x,λ#}T` with `x = 0`, `λ = 1` relative to the ball
`B_{2r}(z)`).  If `r > 0` and `μ₀ = r⁻ⁿ η_#(μ⌞B_{2r}(z))` with `η = η_{z,r}`, then for every
`w ∈ B₂(0)`: every ball about `w` has positive `μ₀`-measure iff every ball about `z + rw` has
positive `μ`-measure (`w ∈ spt μ₀` iff `z + rw ∈ spt μ`).  `η⁻¹(B_σ(w)) = B_{rσ}(z + rw)`, so
`μ₀(B_σ(w)) = r⁻ⁿ μ(B_{rσ}(z + rw) ∩ B_{2r}(z))`, and the intersection drops for `σ ≤ 2 − ‖w‖`;
the radii `min(2 − ‖w‖, ε/r)` resp. `min(ε, 2 − ‖w‖)` transfer nonvanishing in both directions
by monotonicity. -/
theorem Submission.idtp_fons_cc_psf_support : ∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → ∀ w ∈ ball (0 : Euclid P) 2, (∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (z + r • w) ε) ≠ 0 := by
  intro P n μ μ₀ z r hr hμ₀ w hw
  -- Step 1: `η = dilation z r`, `η(v) = −r⁻¹z + r⁻¹v`, is continuous, hence Borel measurable.
  have hη : Measurable (dilation z r) :=
    (continuous_const.add (dilationCLM P r).continuous).measurable
  -- Step 2: `η⁻¹(B_σ(w)) = B_{rσ}(z + rw)`, since `η(v) − w = r⁻¹(v − (z + rw))` and `r > 0`.
  have hpre : ∀ σ : ℝ, dilation z r ⁻¹' ball w σ = ball (z + r • w) (r * σ) := by
    intro σ
    ext v
    have hv : dilation z r v - w = r⁻¹ • (v - (z + r • w)) := by
      simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply]
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
      abel
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hv, norm_smul,
      Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr]
  -- Step 3: `μ₀(B_σ(w)) = c · μ(B_{rσ}(z + rw) ∩ B_{2r}(z))` with `c = ofReal(r⁻ⁿ)`.
  have hball : ∀ σ : ℝ, μ₀ (ball w σ) =
      ENNReal.ofReal (r⁻¹ ^ n) * μ (ball (z + r • w) (r * σ) ∩ ball z (2 * r)) := by
    intro σ
    rw [hμ₀, Measure.smul_apply, Measure.map_apply hη measurableSet_ball, hpre,
      Measure.restrict_apply measurableSet_ball, smul_eq_mul]
  -- Step 4: for `σ ≤ 2 − ‖w‖`, `B_{rσ}(z + rw) ⊆ B_{2r}(z)` (as `rσ + r‖w‖ ≤ 2r`), so the
  -- intersection drops.
  have hw2 : ‖w‖ < 2 := mem_ball_zero_iff.1 hw
  have hdrop : ∀ σ : ℝ, σ ≤ 2 - ‖w‖ →
      μ₀ (ball w σ) = ENNReal.ofReal (r⁻¹ ^ n) * μ (ball (z + r • w) (r * σ)) := by
    intro σ hσ
    have hsub : ball (z + r • w) (r * σ) ⊆ ball z (2 * r) := by
      apply ball_subset_ball'
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    rw [hball, inter_eq_left.2 hsub]
  -- Step 5: `c = ofReal(r⁻ⁿ) ≠ 0`.
  have hc : ENNReal.ofReal (r⁻¹ ^ n) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (inv_pos.2 hr) n
  constructor
  -- Step 6 (⇒): with `σ = min(2 − ‖w‖, ε/r)`, `c · μ(B_{rσ}(z + rw)) = μ₀(B_σ(w)) ≠ 0`, and
  -- `B_{rσ}(z + rw) ⊆ B_ε(z + rw)` since `rσ ≤ ε`.
  · intro h ε hε hzero
    have hσ : 0 < min (2 - ‖w‖) (ε / r) := lt_min (by linarith) (div_pos hε hr)
    have h1 := h _ hσ
    rw [hdrop _ (min_le_left _ _)] at h1
    refine right_ne_zero_of_mul h1 (measure_mono_null (ball_subset_ball ?_) hzero)
    calc r * min (2 - ‖w‖) (ε / r) ≤ r * (ε / r) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le
      _ = ε := mul_div_cancel₀ ε hr.ne'
  -- Step 7 (⇐): with `σ = min(ε, 2 − ‖w‖)`, `μ₀(B_σ(w)) = c · μ(B_{rσ}(z + rw)) ≠ 0` (both
  -- factors are nonzero), and `B_σ(w) ⊆ B_ε(w)`.
  · intro h ε hε hzero
    have hσ : 0 < min ε (2 - ‖w‖) := lt_min hε (by linarith)
    have h1 : μ₀ (ball w (min ε (2 - ‖w‖))) ≠ 0 := by
      rw [hdrop _ (min_le_right _ _)]
      exact mul_ne_zero hc (h _ (mul_pos hr hσ))
    exact h1 (measure_mono_null (ball_subset_ball (min_le_left _ _)) hzero)
/-- **Injectivity of the positive-scale family `(x, λ) ↦ ofReal(λ⁻ⁿ) η_{x,λ#}μ₀`** (proof of Simon
7.3.3(2), p. 189: clause (2) of the positive-scale family of rescalings; total masses recover `λ`,
barycenters recover `x`).  Let `n ≥ 1` and let `μ₀` be a measure on `ℝᴾ` with `0 < μ₀(ℝᴾ) < ∞` and
`μ₀(B_2(0)ᶜ) = 0`.  If `x, x' ∈ ℝᴾ`, `λ, λ' > 0` and
`ofReal(λ⁻ⁿ) η_{x,λ#}μ₀ = ofReal(λ'⁻ⁿ) η_{x',λ'#}μ₀`, then `x = x'` and `λ = λ'`.  The dilations
are continuous, so the total masses are `ofReal(λ⁻ⁿ) μ₀(ℝᴾ)` and `ofReal(λ'⁻ⁿ) μ₀(ℝᴾ)`; cancelling
`μ₀(ℝᴾ) ∈ (0, ∞)` and using that `t ↦ tⁿ` is injective on `[0, ∞)` gives `λ = λ'`.  The identity
is `μ₀`-integrable (`‖v‖ ≤ 2` `μ₀`-a.e.), and the barycenter
`∫ v d(ofReal(λ⁻ⁿ) η_{a,λ#}μ₀) = λ⁻ⁿ (m₀ (−λ⁻¹a) + λ⁻¹ ∫ v dμ₀)`, `m₀ = μ₀(ℝᴾ) ≠ 0`, determines
`a`. -/
theorem Submission.idtp_fons_cc_psf_injective : ∀ (P n : ℕ) (μ₀ : Measure (Euclid P)), 1 ≤ n → μ₀ univ ≠ 0 → μ₀ univ ≠ ∞ → μ₀ (ball (0 : Euclid P) 2)ᶜ = 0 → ∀ (x x' : Euclid P) (lam lam' : ℝ), 0 < lam → 0 < lam' → ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam) = ENNReal.ofReal (lam'⁻¹ ^ n) • μ₀.map (dilation x' lam') → x = x' ∧ lam = lam' := by
  intro P n μ₀ hn h0 htop hball x x' lam lam' hlam hlam' heq
  -- Step 1: `η_{a,s}(u) = −(s⁻¹a) + s⁻¹u` is continuous, hence measurable, so the total mass of
  -- `ofReal(s⁻ⁿ) η_{a,s#}μ₀` is `ofReal(s⁻ⁿ) μ₀(ℝᴾ)`.
  have hmeas : ∀ (a : Euclid P) (s : ℝ), Measurable (dilation a s) := fun a s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  have hmass : ∀ (a : Euclid P) (s : ℝ),
      (ENNReal.ofReal (s⁻¹ ^ n) • μ₀.map (dilation a s)) univ =
        ENNReal.ofReal (s⁻¹ ^ n) * μ₀ univ := fun a s => by
    rw [Measure.smul_apply, Measure.map_apply (hmeas a s) MeasurableSet.univ, preimage_univ,
      smul_eq_mul]
  -- Step 2: equal total masses; cancel `μ₀(ℝᴾ) ∈ (0, ∞)`, then `ofReal` and `t ↦ tⁿ` (`n ≠ 0`)
  -- are injective on `[0, ∞)`, so `λ⁻¹ = λ'⁻¹` and `λ = λ'`.
  have hlam_eq : lam = lam' := by
    have h1 : (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ =
        (ENNReal.ofReal (lam'⁻¹ ^ n) • μ₀.map (dilation x' lam')) univ := by
      rw [heq]
    rw [hmass, hmass, ENNReal.mul_left_inj h0 htop,
      ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity),
      pow_left_inj₀ (inv_nonneg.2 hlam.le) (inv_nonneg.2 hlam'.le) (by omega)] at h1
    exact inv_injective h1
  rw [← hlam_eq] at heq
  refine ⟨?_, hlam_eq⟩
  -- Step 3: `μ₀` is finite and `‖v‖ ≤ 2` `μ₀`-a.e., so the identity is `μ₀`-integrable, and
  -- `m₀ = μ₀(ℝᴾ).toReal ≠ 0`.
  have : IsFiniteMeasure μ₀ := ⟨lt_top_iff_ne_top.2 htop⟩
  have hball_ae : ∀ᵐ v ∂μ₀, v ∈ ball (0 : Euclid P) 2 := mem_ae_iff.2 hball
  have hid : Integrable (fun v : Euclid P => v) μ₀ :=
    (integrable_const (2 : ℝ)).mono' continuous_id.aestronglyMeasurable
      (hball_ae.mono fun v hv => (mem_ball_zero_iff.1 hv).le)
  have hid' : Integrable (fun v : Euclid P => lam⁻¹ • v) μ₀ := hid.smul lam⁻¹
  have hm : μ₀.real univ ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, htop⟩
  -- Step 4: the barycenter of `ofReal(λ⁻ⁿ) η_{a,λ#}μ₀` is `λ⁻ⁿ (m₀ (−λ⁻¹a) + λ⁻¹ ∫ v dμ₀)`.
  have hbar : ∀ a : Euclid P, ∫ v, v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation a lam)) =
      lam⁻¹ ^ n • (μ₀.real univ • -(lam⁻¹ • a) + lam⁻¹ • ∫ v, v ∂μ₀) := by
    intro a
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      integral_map (f := fun v : Euclid P => v) (hmeas a lam).aemeasurable
        continuous_id.aestronglyMeasurable]
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply]
    rw [integral_add (integrable_const _) hid', integral_const, integral_smul]
  -- Step 5: equal measures have equal barycenters; cancel `λ⁻ⁿ ≠ 0`, the common summand
  -- `λ⁻¹ ∫ v dμ₀`, `m₀ ≠ 0`, the negation and `λ⁻¹ ≠ 0`.
  have h1 : ∫ v, v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) =
      ∫ v, v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x' lam)) := by
    rw [heq]
  rw [hbar, hbar] at h1
  exact smul_right_injective (Euclid P) (inv_ne_zero hlam.ne') (neg_injective
    (smul_right_injective (Euclid P) hm (add_right_cancel
      (smul_right_injective (Euclid P) (pow_ne_zero n (inv_ne_zero hlam.ne')) h1))))
/-- **Uniqueness of vague limits** (basic fact (F6) of the positive-scale family step in the proof
of Simon 7.3.3(1), chapter-07.txt lines 443–467): two measures `ν₁`, `ν₂` on `ℝᴾ` that are finite
on compact sets and give the same integral to every continuous compactly supported `f : ℝᴾ → ℝ`
are equal.  Finiteness on compact sets makes `νᵢ` locally finite on the locally compact space
`ℝᴾ`, hence regular on the σ-compact metric space `ℝᴾ`, and regular measures are determined by
their integrals on `C_c(ℝᴾ, ℝ)` (Riesz–Markov–Kakutani uniqueness: Urysohn functions
`1_K ≤ f ≤ 1_V` and outer regularity give `ν₁(K) = ν₂(K)` for compact `K`; inner regularity on
open sets and outer regularity extend this to all Borel sets). -/
theorem Submission.idtp_fons_cc_psf_vague_unique : ∀ (P : ℕ) (ν₁ ν₂ : Measure (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → ν₁ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → ν₂ K ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x ∂ν₁ = ∫ x, f x ∂ν₂) → ν₁ = ν₂ := by
  intro P ν₁ ν₂ h₁ h₂ hint
  -- Step 1: `νᵢ(K) < ∞` for every compact `K`, i.e. `νᵢ` is finite on compact sets.
  have : IsFiniteMeasureOnCompacts ν₁ := ⟨fun K hK => (h₁ K hK).lt_top⟩
  have : IsFiniteMeasureOnCompacts ν₂ := ⟨fun K hK => (h₂ K hK).lt_top⟩
  -- Step 2: `ℝᴾ` is locally compact (closed balls are compact), so `νᵢ` is locally finite.
  have : IsLocallyFiniteMeasure ν₁ := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  have : IsLocallyFiniteMeasure ν₂ := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  -- Step 3: `ℝᴾ` is a σ-compact metric space with its Borel σ-algebra, so `νᵢ` is regular.
  have : ν₁.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν₁
  have : ν₂.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν₂
  -- Steps 4–6: every `f ∈ C_c(ℝᴾ, ℝ)` is continuous with compact support, so `∫ f dν₁ = ∫ f dν₂`;
  -- regular measures with equal integrals on `C_c(ℝᴾ, ℝ)` agree on compact sets (Urysohn and outer
  -- regularity), hence on open sets (inner regularity) and on all Borel sets (outer regularity).
  exact Measure.ext_of_integral_eq_on_compactlySupported fun f =>
    hint f f.continuous f.hasCompactSupport
/-- **Continuity of the rescaled push-forward integrals in the parameters `(x, λ)`, `λ > 0`** (proof
of Simon 7.3.3, chapter-07.txt lines 443–467: weak limits of `η_{xᵢ,λᵢ#}T` with `lim xᵢ = x` and
`lim λᵢ = λ > 0`).  Let `μ₀` be a finite measure on `ℝᴾ` and `f` continuous with compact support.
If `xᵢ → x` and `λᵢ → λ`, with `λᵢ > 0` and `λ > 0`, then
`∫ f d(λᵢ⁻ⁿ η_{xᵢ,λᵢ#}μ₀) → ∫ f d(λ⁻ⁿ η_{x,λ#}μ₀)`.  By `integral_smul_measure` and `integral_map`,
`∫ f d(s⁻ⁿ η_{a,s#}μ₀) = s⁻ⁿ ∫ f ∘ η_{a,s} dμ₀` for `s > 0`; `η_{xᵢ,λᵢ}(v) → η_{x,λ}(v)` pointwise
and `|f| ≤ C`, a constant that is `μ₀`-integrable, so dominated convergence and `λᵢ⁻ⁿ → λ⁻ⁿ`
conclude. -/
theorem Submission.idtp_fons_cc_psf_param_continuity : ∀ (P n : ℕ) (μ₀ : Measure (Euclid P)) (f : Euclid P → ℝ) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (x : Euclid P) (lam : ℝ), μ₀ univ ≠ ∞ → Continuous f → HasCompactSupport f → (∀ i, 0 < lams i) → 0 < lam → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 lam) → Tendsto (fun i => ∫ v, f v ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ v, f v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)))) := by
  intro P n μ₀ f xs lams x lam hμ₀ hf hfc hlams hlam hxs hlim
  have : IsFiniteMeasure μ₀ := ⟨lt_top_iff_ne_top.2 hμ₀⟩
  -- `η_{a,s}(u) = −s⁻¹a + s⁻¹u` is continuous, hence measurable.
  have hcont : ∀ (a : Euclid P) (s : ℝ), Continuous (dilation a s) := fun a s => by
    unfold dilation
    fun_prop
  -- Step 1: `∫ f d(ofReal(s⁻ⁿ) • η_{a,s#}μ₀) = s⁻ⁿ ∫ f ∘ η_{a,s} dμ₀` for `s > 0`, by
  -- `integral_smul_measure`, `toReal_ofReal` (`s⁻ⁿ ≥ 0`) and `integral_map`.
  have hformula : ∀ (a : Euclid P) (s : ℝ), 0 < s →
      ∫ v, f v ∂(ENNReal.ofReal (s⁻¹ ^ n) • μ₀.map (dilation a s)) =
        s⁻¹ ^ n * ∫ v, f (dilation a s v) ∂μ₀ := by
    intro a s hs
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
      integral_map (hcont a s).aemeasurable hf.aestronglyMeasurable]
  rw [funext fun i => hformula (xs i) (lams i) (hlams i), hformula x lam hlam]
  -- Step 2: `λᵢ⁻¹ → λ⁻¹`, as `λ ≠ 0`.
  have hinv : Tendsto (fun i => (lams i)⁻¹) atTop (𝓝 lam⁻¹) := hlim.inv₀ hlam.ne'
  -- Steps 3–5: `f(η_{xᵢ,λᵢ}(v)) → f(η_{x,λ}(v))` for every `v`, and `|f| ≤ C` with the constant
  -- `C` integrable for the finite measure `μ₀`; dominated convergence.
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hdct : Tendsto (fun i => ∫ v, f (dilation (xs i) (lams i) v) ∂μ₀) atTop
      (𝓝 (∫ v, f (dilation x lam v) ∂μ₀)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun i => (hf.comp (hcont _ _)).aestronglyMeasurable) (integrable_const C)
      (fun i => Eventually.of_forall fun v => hC _) (Eventually.of_forall fun v => ?_)
    have h1 : Tendsto (fun i => -((lams i)⁻¹ • xs i) + (lams i)⁻¹ • v) atTop
        (𝓝 (-(lam⁻¹ • x) + lam⁻¹ • v)) :=
      (hinv.smul hxs).neg.add (hinv.smul tendsto_const_nhds)
    exact (hf.tendsto _).comp h1
  -- Step 6: `λᵢ⁻ⁿ ∫ f ∘ η_{xᵢ,λᵢ} dμ₀ → λ⁻ⁿ ∫ f ∘ η_{x,λ} dμ₀`.
  exact (hinv.pow n).mul hdct

/-- **Domain recovery under vague limits** (Simon 7.3.3, proof of 3.3(1), items (7) and (9),
chapter-07.txt lines 445–467: a weak limit of `η_{xᵢ,λᵢ#}T` with `lim λᵢ = λ > 0` lives on
`η_{x,λ}(U)`), for an arbitrary finite measure `μ₀`.  Write `μ₀^{x,λ} = λ⁻ⁿ η_{x,λ#}μ₀` and
`G_{x,λ} = η_{x,λ}(B₂(0))`, and call `(x, λ)` admissible if `0 < λ ≤ 1` and `‖x‖ ≤ 1 − λ`.  If
admissible `μ₀^{xᵢ,λᵢ}` converge vaguely to a Radon measure `ν` and no `G_{xᵢ,λᵢ}` contains the
compact set `K`, then `ν = μ₀^{x,λ}` for an admissible `(x, λ)` with `K ⊄ G_{x,λ}`.  Since
`K ⊆ B̄_R(0)`, `K ⊄ G_{xᵢ,λᵢ}` forces `λᵢ ≥ R⁻¹`, so a subsequence of the parameters converges in
the compact set `B̄₁(0) × [R⁻¹, 1]`; continuity in the parameters and uniqueness of vague limits
identify `ν`, and if `K ⊆ G_{x,λ}`, the margin `2 − max_K ‖x + λv‖ > 0` absorbs the parameter
error, giving `K ⊆ G_{x_{ψ i},λ_{ψ i}}` for large `i`. -/
theorem Submission.idtp_fons_cc_psf_vague_closed : ∀ (P n : ℕ) (μ₀ : Measure (Euclid P)), μ₀ univ ≠ ∞ → ∀ (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ν : Measure (Euclid P)) (K : Set (Euclid P)), (∀ i, 0 < lams i ∧ lams i ≤ 1 ∧ ‖xs i‖ ≤ 1 - lams i) → (∀ K' : Set (Euclid P), IsCompact K' → ν K' ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun i => ∫ x, f x ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ x, f x ∂ν))) → IsCompact K → (∀ i, ¬ K ⊆ dilation (xs i) (lams i) '' ball 0 2) → ∃ (x : Euclid P) (lam : ℝ), (0 < lam ∧ lam ≤ 1 ∧ ‖x‖ ≤ 1 - lam) ∧ ν = (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ∧ ¬ K ⊆ dilation x lam '' ball 0 2 := by
  intro P n μ₀ hμ₀ xs lams ν K hadm hν hconv hK hnot
  -- Step 1: `K` is bounded, so `K ⊆ closedBall 0 R` for some `R > 0`.
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R, hRpos, hKR⟩ : ∃ R : ℝ, 0 < R ∧ K ⊆ closedBall 0 R :=
    ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  -- Step 2: `λᵢ ≥ R⁻¹`; otherwise `λᵢ R ≤ 1` and domain_geometry (c) gives
  -- `K ⊆ closedBall 0 R ⊆ G_{xᵢ,λᵢ}`.
  have hlow : ∀ i, R⁻¹ ≤ lams i := by
    intro i
    obtain ⟨hl0, hl1, hx⟩ := hadm i
    by_contra hlt
    rw [not_le] at hlt
    have hlR : lams i * R ≤ 1 :=
      calc lams i * R ≤ R⁻¹ * R := mul_le_mul_of_nonneg_right hlt.le hRpos.le
        _ = 1 := inv_mul_cancel₀ hRpos.ne'
    exact hnot i (hKR.trans
      (((Submission.idtp_fons_cc_psf_domain_geometry P (xs i) (lams i) hl0).2.2 hl1 hx).2 R hlR))
  -- Step 3: the parameters lie in the compact set `closedBall 0 1 × [R⁻¹, 1]`; extract a
  -- subsequence `(x_{ψ i}, λ_{ψ i}) → (x, λ)`.
  have hmem : ∀ i, (xs i, lams i) ∈ closedBall (0 : Euclid P) 1 ×ˢ Icc R⁻¹ (1 : ℝ) := by
    intro i
    obtain ⟨hl0, hl1, hx⟩ := hadm i
    refine ⟨?_, hlow i, hl1⟩
    rw [mem_closedBall_zero_iff]
    linarith
  obtain ⟨⟨x, lam⟩, ⟨-, hlamR, hlam1⟩, ψ, hψ, hlim⟩ :=
    ((isCompact_closedBall (0 : Euclid P) 1).prod isCompact_Icc).tendsto_subseq
      (x := fun i => (xs i, lams i)) hmem
  have hxlim : Tendsto (fun i => xs (ψ i)) atTop (𝓝 x) := hlim.fst_nhds
  have hllim : Tendsto (fun i => lams (ψ i)) atTop (𝓝 lam) := hlim.snd_nhds
  -- Step 4: `(x, λ)` is admissible.
  have hlam0 : 0 < lam := lt_of_lt_of_le (inv_pos.2 hRpos) hlamR
  have hxnorm : ‖x‖ ≤ 1 - lam :=
    le_of_tendsto_of_tendsto' hxlim.norm (hllim.const_sub 1) fun i => (hadm (ψ i)).2.2
  -- Step 5: param_continuity and uniqueness of limits give `∫ f dν = ∫ f dμ₀^{x,λ}`.
  have hint : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
      ∫ v, f v ∂ν = ∫ v, f v ∂(ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) :=
    fun f hf hfc => tendsto_nhds_unique ((hconv f hf hfc).comp hψ.tendsto_atTop)
      (Submission.idtp_fons_cc_psf_param_continuity P n μ₀ f (fun i => xs (ψ i))
        (fun i => lams (ψ i)) x lam hμ₀ hf hfc (fun i => (hadm (ψ i)).1) hlam0 hxlim hllim)
  -- Step 6: `μ₀^{x,λ}` is finite, so vague_unique gives `ν = μ₀^{x,λ}`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    exact continuous_const.add (dilationCLM P lam).continuous
  have hfin : ∀ K' : Set (Euclid P), IsCompact K' →
      (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) K' ≠ ∞ := by
    intro K' _
    refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ K'))
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hcont.measurable MeasurableSet.univ,
      preimage_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ₀
  refine ⟨x, lam, ⟨hlam0, hlam1, hxnorm⟩,
    Submission.idtp_fons_cc_psf_vague_unique P ν _ hν hfin hint, fun hsub => ?_⟩
  -- Step 7: if `K ⊆ G_{x,λ}`, then `M = max_K ‖x + λ v‖ < 2`, and for `i` large the margin
  -- `2 - M` absorbs the parameter error, so `K ⊆ G_{x_{ψ i},λ_{ψ i}}`, a contradiction.
  have hKne : K.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    exact hnot 0 (empty_subset _)
  have hh : Continuous fun v : Euclid P => ‖x + lam • v‖ := by fun_prop
  obtain ⟨v₀, hv₀, hmax⟩ := hK.exists_isMaxOn hKne hh.continuousOn
  have hM : ‖x + lam • v₀‖ < 2 :=
    ((Submission.idtp_fons_cc_psf_domain_geometry P x lam hlam0).1 v₀).1 (hsub hv₀)
  have hγ : 0 < 2 - ‖x + lam • v₀‖ := sub_pos.2 hM
  have hγR : 0 < (2 - ‖x + lam • v₀‖) / (2 * R) := div_pos hγ (mul_pos two_pos hRpos)
  have ev1 : ∀ᶠ i in atTop, ‖xs (ψ i) - x‖ < (2 - ‖x + lam • v₀‖) / 2 :=
    (Metric.tendsto_nhds.1 hxlim _ (half_pos hγ)).mono fun i hi => by rwa [dist_eq_norm] at hi
  have ev2 : ∀ᶠ i in atTop, |lams (ψ i) - lam| < (2 - ‖x + lam • v₀‖) / (2 * R) :=
    (Metric.tendsto_nhds.1 hllim _ hγR).mono fun i hi => by rwa [Real.dist_eq] at hi
  obtain ⟨i, hi1, hi2⟩ := (ev1.and ev2).exists
  refine hnot (ψ i) fun v hv => ((Submission.idtp_fons_cc_psf_domain_geometry P (xs (ψ i))
    (lams (ψ i)) (hadm (ψ i)).1).1 v).2 ?_
  have hvR : ‖v‖ ≤ R := mem_closedBall_zero_iff.1 (hKR hv)
  have hvM : ‖x + lam • v‖ ≤ ‖x + lam • v₀‖ := isMaxOn_iff.1 hmax v hv
  have h3 : |lams (ψ i) - lam| * ‖v‖ ≤ (2 - ‖x + lam • v₀‖) / 2 :=
    calc |lams (ψ i) - lam| * ‖v‖ ≤ (2 - ‖x + lam • v₀‖) / (2 * R) * R :=
          mul_le_mul hi2.le hvR (norm_nonneg v) hγR.le
      _ = (2 - ‖x + lam • v₀‖) / 2 := by rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hRpos.ne']
  have hsplit : xs (ψ i) + lams (ψ i) • v =
      (x + lam • v) + (xs (ψ i) - x) + (lams (ψ i) - lam) • v := by
    rw [sub_smul]
    abel
  calc ‖xs (ψ i) + lams (ψ i) • v‖
      = ‖(x + lam • v) + (xs (ψ i) - x) + (lams (ψ i) - lam) • v‖ := by rw [hsplit]
    _ ≤ ‖x + lam • v‖ + ‖xs (ψ i) - x‖ + ‖(lams (ψ i) - lam) • v‖ := norm_add₃_le
    _ = ‖x + lam • v‖ + ‖xs (ψ i) - x‖ + |lams (ψ i) - lam| * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs]
    _ < 2 := by linarith
/-- **A measure of finite positive mass is not `f Hⁿ` with `f` dilation-invariant** (`n ≥ 1`;
non-homogeneity of the positive-scale members `η_{x,λ#}T`, `λ > 0`, of the class `𝒯` in the proof
of Simon 7.3.3(1), chapter-07.txt lines 444–472).  If `f(tw) = f(w)` for all `t > 0`, then
`ρ = f Hⁿ` has `ρ(B_t(0)) = tⁿ ρ(B_1(0))` for `t > 0`, by
`Submission.dimred_cs_mi_withDensity_dilate` with `A = B_1(0)` and `tB_1(0) = B_t(0)`.  If
`ρ(B_1(0)) = 0`, the null balls `B_{m+1}(0)` cover `ℝᴾ` and `ρ(ℝᴾ) = 0`; otherwise
`t ρ(B_1(0)) ≤ tⁿ ρ(B_1(0)) ≤ ρ(ℝᴾ)` for `t ≥ 1`, with `t ρ(B_1(0)) → ∞`, so `ρ(ℝᴾ) = ∞`.  Either
way `ρ ≠ ν` when `0 < ν(ℝᴾ) < ∞`. -/
theorem Submission.idtp_fons_cc_psf_nonhomogeneous : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (f : Euclid P → ℝ≥0∞), 1 ≤ n → ν univ ≠ 0 → ν univ ≠ ∞ → (∀ t : ℝ, 0 < t → ∀ w : Euclid P, f (t • w) = f w) → ν ≠ (μHE[n] : Measure (Euclid P)).withDensity f := by
  intro P n ν f hn h0 htop hf hν
  -- Step 1: suppose `ν = ρ := f Hⁿ`; then `ρ(ℝᴾ) ≠ 0` and `ρ(ℝᴾ) ≠ ∞`.
  subst hν
  set ρ := (μHE[n] : Measure (Euclid P)).withDensity f
  -- Step 2: `ρ(B_t(0)) = ofReal(tⁿ) ρ(B_1(0))` for `t > 0`, by the dilation homogeneity with
  -- `A = B_1(0)` and `(w ↦ tw)(B_1(0)) = tB_1(0) = B_t(0)`.
  have hball : ∀ t : ℝ, 0 < t → ρ (ball 0 t) = ENNReal.ofReal (t ^ n) * ρ (ball 0 1) := by
    intro t ht
    have h := Submission.dimred_cs_mi_withDensity_dilate P n f t ht (hf t ht) (ball 0 1)
      measurableSet_ball
    rwa [Set.image_smul, smul_unitBall_of_pos ht] at h
  by_cases h1 : ρ (ball 0 1) = 0
  -- Step 3: if `ρ(B_1(0)) = 0`, every ball `B_{m+1}(0)` is null, and these balls cover `ℝᴾ`.
  · refine h0 ?_
    rw [← iUnion_ball_nat_succ (0 : Euclid P)]
    refine measure_iUnion_null fun m => ?_
    rw [hball (m + 1) (by positivity), h1, mul_zero]
  -- Step 4: otherwise `ofReal(t) ρ(B_1(0)) → ∞ · ρ(B_1(0)) = ∞`, while for `t ≥ 1` (and `n ≥ 1`)
  -- `ofReal(t) ρ(B_1(0)) ≤ ofReal(tⁿ) ρ(B_1(0)) = ρ(B_t(0)) ≤ ρ(ℝᴾ)`; so `ρ(ℝᴾ) = ∞`.
  · have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal t * ρ (ball 0 1)) atTop (𝓝 ∞) := by
      have h := ENNReal.Tendsto.mul_const ENNReal.tendsto_ofReal_atTop
        (Or.inl ENNReal.top_ne_zero) (b := ρ (ball 0 1))
      rwa [ENNReal.top_mul h1] at h
    refine htop (top_le_iff.mp (le_of_tendsto hlim ?_))
    filter_upwards [eventually_ge_atTop 1] with t ht
    calc ENNReal.ofReal t * ρ (ball 0 1) ≤ ENNReal.ofReal (t ^ n) * ρ (ball 0 1) := by
          gcongr
          simpa only [pow_one] using pow_le_pow_right₀ ht hn
      _ = ρ (ball 0 t) := (hball t (by linarith)).symm
      _ ≤ ρ univ := measure_mono (subset_univ _)

/-- **Transferred lower mass bound for the rescaled measures** (positive-scale family of the cone
class in the proof of Simon 7.3.3(1), chapter-07.txt lines 420–476: the "rescaling and translation"
reducing (2) to (4), and the family (10)–(11)).  Let `μ₀ = r⁻ⁿ η_{z,r#}(μ⌞B_{2r}(z))` and
`μ₀^{x,λ} = λ⁻ⁿ η_{x,λ#}μ₀`.  If `e^{−Λ₀σ} ωₙ σⁿ ≤ μ(B_σ(p))` for every `p ∈ spt μ` and
`0 < σ < ρ'` with `B̄_{ρ'}(p) ⊆ B̄_{2r}(z)`, then `e^{−rΛ₀ρ} ωₙ ρⁿ ≤ μ₀^{x,λ}(B_ρ(y))` whenever
`0 < λ ≤ 1`, `ρ > 0`, `B̄_ρ(y) ⊆ η_{x,λ}(B₂(0))` and `y ∈ spt μ₀^{x,λ}`.  With `s = rλ` and
`p = z + r(x + λy)`: `η_{a,t}⁻¹(B_σ(w)) = B_{tσ}(a + tw)` gives
`μ₀^{x,λ}(B_σ(y)) = λ⁻ⁿ r⁻ⁿ μ(B_{sσ}(p) ∩ B_{2r}(z))`; the membership test of
`Submission.idtp_fons_cc_psf_domain_geometry` gives `B̄_{sρ}(p) ⊆ B_{2r}(z)`, so the intersection
drops for `σ ≤ ρ` and `p ∈ spt μ`; compactness gives a margin `δ > 0` with
`B̄_{sρ+δ}(p) ⊆ B_{2r}(z)`; finally the bound at `p` with `σ = sρ` is rescaled by `λ⁻ⁿ r⁻ⁿ`, and
`e^{−rΛ₀ρ} ≤ e^{−Λ₀sρ}` as `Λ₀ ≥ 0`, `λ ≤ 1`. -/
theorem Submission.idtp_fons_cc_psf_lower_bound : ∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 0 < r → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → ∀ Λ₀ : ℝ, 0 ≤ Λ₀ → (∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ closedBall z (2 * r) → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ₀ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ μ (ball p σ)) → ∀ (x y : Euclid P) (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ → closedBall y ρ ⊆ dilation x lam '' ball 0 2 → (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ρ) := by
  intro P n μ μ₀ z r hr hμ₀ Λ₀ hΛ₀ hμ x y lam ρ hlam hlam1 hρ hsub hspt
  have hs : 0 < r * lam := mul_pos hr hlam
  -- Step 1: `η_{a,t}(v) = t⁻¹(v − a)` is continuous, hence measurable, and
  -- `η_{a,t}⁻¹(B_σ(w)) = B_{tσ}(a + tw)` for `t > 0`.
  have hmeas : ∀ (a : Euclid P) (t : ℝ), Measurable (dilation a t) := fun a t =>
    (continuous_const.add (dilationCLM P t).continuous).measurable
  have hpre : ∀ (a w : Euclid P) (t σ : ℝ), 0 < t →
      dilation a t ⁻¹' ball w σ = ball (a + t • w) (t * σ) := by
    intro a w t σ ht
    ext v
    have hv : dilation a t v - w = t⁻¹ • (v - (a + t • w)) := by
      simp only [dilation, dilationCLM, FunLike.coe_smul, ContinuousLinearMap.coe_id',
        Pi.smul_apply, id_eq]
      rw [smul_sub t⁻¹ v (a + t • w), smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    simp only [mem_preimage, mem_ball, dist_eq_norm]
    rw [hv, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht]
  -- Step 2: the ball formula `μ₀^{x,λ}(B_σ(y)) = λ⁻ⁿ r⁻ⁿ μ(B_{rλσ}(p) ∩ B_{2r}(z))`.
  obtain ⟨p, hp⟩ : ∃ p : Euclid P, p = z + r • (x + lam • y) := ⟨_, rfl⟩
  have hball : ∀ σ : ℝ, (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y σ) =
      ENNReal.ofReal (lam⁻¹ ^ n) * (ENNReal.ofReal (r⁻¹ ^ n) *
        μ (ball p (r * (lam * σ)) ∩ ball z (2 * r))) := by
    intro σ
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hmeas x lam) measurableSet_ball,
      hpre x y lam σ hlam, hμ₀, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (hmeas z r) measurableSet_ball, hpre z (x + lam • y) r (lam * σ) hr, ← hp,
      Measure.restrict_apply measurableSet_ball]
  -- Step 3: `B̄_{rλρ}(p) ⊆ B_{2r}(z)`: for `q` in the closed ball, `u = y + (rλ)⁻¹(q − p)` lies in
  -- `B̄_ρ(y) ⊆ η_{x,λ}(B₂(0))`, so `‖x + λu‖ < 2` (domain_geometry (a)), and `x + λu = r⁻¹(q − z)`.
  have hDG := Submission.idtp_fons_cc_psf_domain_geometry P x lam hlam
  have hcont : closedBall p (r * (lam * ρ)) ⊆ ball z (2 * r) := by
    intro q hq
    rw [mem_closedBall, dist_eq_norm] at hq
    have hu : y + (r * lam)⁻¹ • (q - p) ∈ closedBall y ρ := by
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 hs.le), inv_mul_le_iff₀ hs]
      linarith
    have h2 := (hDG.1 _).1 (hsub hu)
    have hxu : x + lam • (y + (r * lam)⁻¹ • (q - p)) = r⁻¹ • (q - z) := by
      rw [hp]
      match_scalars <;> field_simp <;> ring
    rw [hxu, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le), inv_mul_lt_iff₀ hr] at h2
    rw [mem_ball, dist_eq_norm]
    linarith
  -- Step 4: for `σ ≤ ρ` the intersection with `B_{2r}(z)` drops.
  have hball' : ∀ σ : ℝ, σ ≤ ρ →
      (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y σ) =
        ENNReal.ofReal (lam⁻¹ ^ n) * (ENNReal.ofReal (r⁻¹ ^ n) * μ (ball p (r * (lam * σ)))) := by
    intro σ hσ
    have hle : r * (lam * σ) ≤ r * (lam * ρ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσ hlam.le) hr.le
    rw [hball σ, inter_eq_left.2
      (ball_subset_closedBall.trans ((closedBall_subset_closedBall hle).trans hcont))]
  -- Step 5: `p ∈ spt μ`: with `σ = min(ρ, ε/(rλ))`, `μ₀^{x,λ}(B_σ(y)) ≠ 0` forces
  -- `μ(B_{rλσ}(p)) ≠ 0`, and `B_{rλσ}(p) ⊆ B_ε(p)`.
  have hp_spt : ∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0 := by
    intro ε hε h0
    obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, σ = min ρ (ε / (r * lam)) := ⟨_, rfl⟩
    have hσ : 0 < σ := hσdef ▸ lt_min hρ (div_pos hε hs)
    have hσε : r * (lam * σ) ≤ ε := by
      have h := hσdef ▸ min_le_right ρ (ε / (r * lam))
      rw [le_div_iff₀ hs] at h
      linarith
    apply hspt σ hσ
    rw [hball' σ (hσdef ▸ min_le_left _ _), measure_mono_null (ball_subset_ball hσε) h0, mul_zero,
      mul_zero]
  -- Step 6: a margin `δ > 0` with `B̄_{rλρ+δ}(p) ⊆ B_{2r}(z)` (compactness of `B̄_{rλρ}(p)`).
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall p (r * (lam * ρ))).exists_cthickening_subset_open
    isOpen_ball hcont
  rw [cthickening_closedBall hδ.le (mul_pos hr (mul_pos hlam hρ)).le] at hδsub
  -- Step 7: the hypothesis on `μ` at `p` with `σ = rλρ < ρ' = rλρ + δ`.
  have h7 := hμ p hp_spt (r * (lam * ρ)) (δ + r * (lam * ρ))
    (hδsub.trans ball_subset_closedBall) (by positivity) (by linarith)
  -- Step 8: `λ⁻ⁿ r⁻ⁿ (rλρ)ⁿ = ρⁿ`.
  have hkey : ENNReal.ofReal (lam⁻¹ ^ n) * ENNReal.ofReal (r⁻¹ ^ n) *
      ENNReal.ofReal ((r * (lam * ρ)) ^ n) = ENNReal.ofReal (ρ ^ n) := by
    have hc : lam⁻¹ * r⁻¹ * (r * (lam * ρ)) = ρ := by
      field_simp
    rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 hlam.le) n),
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (inv_nonneg.2 hlam.le) n)
        (pow_nonneg (inv_nonneg.2 hr.le) n)), ← mul_pow, ← mul_pow, hc]
  -- Step 9: `e^{−rΛ₀ρ} ≤ e^{−Λ₀rλρ}`, since `Λ₀rρ(1 − λ) ≥ 0`.
  have hexp : ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) ≤
      ENNReal.ofReal (Real.exp (-(Λ₀ * (r * (lam * ρ))))) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_exp]
    have h := mul_nonneg (mul_nonneg (mul_nonneg hΛ₀ hr.le) hρ.le) (sub_nonneg.2 hlam1)
    linarith
  rw [hball' ρ le_rfl]
  calc ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n))
      ≤ ENNReal.ofReal (Real.exp (-(Λ₀ * (r * (lam * ρ))))) *
          (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := by gcongr
    _ = ENNReal.ofReal (lam⁻¹ ^ n) * (ENNReal.ofReal (r⁻¹ ^ n) *
          (ENNReal.ofReal (Real.exp (-(Λ₀ * (r * (lam * ρ))))) *
            (unitBallVolume n * ENNReal.ofReal ((r * (lam * ρ)) ^ n)))) := by
        rw [← hkey]
        ring
    _ ≤ ENNReal.ofReal (lam⁻¹ ^ n) * (ENNReal.ofReal (r⁻¹ ^ n) * μ (ball p (r * (lam * ρ)))) := by
        gcongr

/-- **The positive-scale family `μ₀^{x,λ}`** (Simon 7.3.3, proof of 3.3(1), chapter-07.txt
lines 445–467: the blow-ups `η_{x,λ#}T` with `|x| < 1 − λ`, `0 < λ < 1`, and their domains
`U_S = η_{x,λ}(U)`, (6), (9), (10) there).  Let `0 < μ(B_{2r}(z)) < ∞`,
`μ₀ = r⁻ⁿ η_{z,r#}(μ⌞B_{2r}(z))`, `μ₀^{x,λ} = λ⁻ⁿ η_{x,λ#}μ₀` and `G_{x,λ} = η_{x,λ}(B_2(0))`;
`(x, λ)` is admissible if `0 < λ ≤ 1` and `‖x‖ ≤ 1 − λ`.  Then (1) `w ∈ B_2(0)` lies in `spt μ₀`
iff `z + rw ∈ spt μ`; (2) `(x, λ) ↦ μ₀^{x,λ}` is injective (the total mass recovers `λ`, the
barycenter `x`); (3) `0 < μ₀^{x,λ}(ℝᴾ) < ∞`; (4) `G_{x,λ}` is open and contains `B_2(0)` for
admissible `(x, λ)`; (5) a vague limit of admissible members whose domains all fail to contain
the compact set `K` is an admissible member whose domain does not contain `K`; (6) no member is
`f Hⁿ` with `f` constant on rays, as `f Hⁿ` has total mass `0` or `∞`; (7) if `Λ₀ ≥ 0` and
`e^{−Λ₀σ} ωₙ σⁿ ≤ μ(B_σ(p))` whenever `p ∈ spt μ`, `0 < σ < ρ` and
`closedBall p ρ ⊆ closedBall z (2r)`, then `e^{−rΛ₀ρ} ωₙ ρⁿ ≤ μ₀^{x,λ}(B_ρ(y))` whenever
`0 < λ ≤ 1`, `ρ > 0`, `closedBall y ρ ⊆ G_{x,λ}` and `y ∈ spt μ₀^{x,λ}`. -/
theorem Submission.idtp_fons_cc_positive_scale_family : ∀ (P n : ℕ) (μ μ₀ : Measure (Euclid P)) (z : Euclid P) (r : ℝ), 1 ≤ n → 0 < r → μ (ball z (2 * r)) ≠ 0 → μ (ball z (2 * r)) ≠ ∞ → μ₀ = ENNReal.ofReal (r⁻¹ ^ n) • (μ.restrict (ball z (2 * r))).map (dilation z r) → (∀ w ∈ ball (0 : Euclid P) 2, (∀ ε : ℝ, 0 < ε → μ₀ (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (z + r • w) ε) ≠ 0) ∧ (∀ (x x' : Euclid P) (lam lam' : ℝ), 0 < lam → 0 < lam' → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) = (ENNReal.ofReal (lam'⁻¹ ^ n) • μ₀.map (dilation x' lam')) → x = x' ∧ lam = lam') ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ 0 ∧ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) univ ≠ ∞) ∧ (∀ (x : Euclid P) (lam : ℝ), 0 < lam → lam ≤ 1 → ‖x‖ ≤ 1 - lam → IsOpen (dilation x lam '' ball 0 2) ∧ ball 0 2 ⊆ dilation x lam '' ball 0 2) ∧ (∀ (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (ν : Measure (Euclid P)) (K : Set (Euclid P)), (∀ i, 0 < lams i ∧ lams i ≤ 1 ∧ ‖xs i‖ ≤ 1 - lams i) → (∀ K' : Set (Euclid P), IsCompact K' → ν K' ≠ ∞) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun i => ∫ x, f x ∂(ENNReal.ofReal ((lams i)⁻¹ ^ n) • μ₀.map (dilation (xs i) (lams i)))) atTop (𝓝 (∫ x, f x ∂ν))) → IsCompact K → (∀ i, ¬ K ⊆ dilation (xs i) (lams i) '' ball 0 2) → ∃ (x : Euclid P) (lam : ℝ), (0 < lam ∧ lam ≤ 1 ∧ ‖x‖ ≤ 1 - lam) ∧ ν = (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ∧ ¬ K ⊆ dilation x lam '' ball 0 2) ∧ (∀ (x : Euclid P) (lam : ℝ) (f : Euclid P → ℝ≥0∞), 0 < lam → (∀ t : ℝ, 0 < t → ∀ w : Euclid P, f (t • w) = f w) → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) ≠ (μHE[n] : Measure (Euclid P)).withDensity f) ∧ ∀ Λ₀ : ℝ, 0 ≤ Λ₀ → (∀ p : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball p ε) ≠ 0) → ∀ σ ρ : ℝ, closedBall p ρ ⊆ closedBall z (2 * r) → 0 < σ → σ < ρ → ENNReal.ofReal (Real.exp (-(Λ₀ * σ))) * (unitBallVolume n * ENNReal.ofReal (σ ^ n)) ≤ μ (ball p σ)) → ∀ (x y : Euclid P) (lam ρ : ℝ), 0 < lam → lam ≤ 1 → 0 < ρ → closedBall y ρ ⊆ dilation x lam '' ball 0 2 → (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ε) ≠ 0) → ENNReal.ofReal (Real.exp (-(r * Λ₀ * ρ))) * (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) ≤ (ENNReal.ofReal (lam⁻¹ ^ n) • μ₀.map (dilation x lam)) (ball y ρ) := by
  intro P n μ μ₀ z r hn hr hB0 hBinf hμ₀
  -- Step 0 (and (3)): `μ₀` is a finite nonzero measure concentrated on `B_2(0)`, and every
  -- `μ₀^{x,λ}`, `λ > 0`, has finite nonzero total mass `λ⁻ⁿ r⁻ⁿ μ(B_{2r}(z))`
  obtain ⟨h0, hinf, hconc, hmass⟩ :=
    Submission.idtp_fons_cc_psf_total_mass P n μ μ₀ z r hr hB0 hBinf hμ₀
  -- (1) support relation; (2) injectivity; (3) total masses; (5) closedness under vague
  -- limits; (7) transferred lower bound
  refine ⟨Submission.idtp_fons_cc_psf_support P n μ μ₀ z r hr hμ₀,
    Submission.idtp_fons_cc_psf_injective P n μ₀ hn h0 hinf hconc, hmass,
    fun x lam hlam hlam1 hx => ?_, Submission.idtp_fons_cc_psf_vague_closed P n μ₀ hinf,
    fun x lam f hlam hf => ?_, Submission.idtp_fons_cc_psf_lower_bound P n μ μ₀ z r hr hμ₀⟩
  · -- (4) `G_{x,λ}` is open, and contains `B_2(0)` for admissible `(x, λ)`
    obtain ⟨-, hopen, hadm⟩ := Submission.idtp_fons_cc_psf_domain_geometry P x lam hlam
    exact ⟨hopen, (hadm hlam1 hx).1⟩
  · -- (6) a nonzero finite measure is not `f Hⁿ` for `f` constant on rays
    exact Submission.idtp_fons_cc_psf_nonhomogeneous P n _ f hn (hmass x lam hlam).1
      (hmass x lam hlam).2 hf

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
