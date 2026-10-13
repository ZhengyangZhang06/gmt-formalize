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

/-- **Degree-0 unit orientations** (Simon 6.1.1, 6.1.7; 6.2.2).  If `ξ ∈ Λ₀(ℝᴾ)` orients `Q`,
i.e. `⟨α, ξ⟩ = ±α(τ)` for every `0`-covector `α`, with `τ : Fin 0 → ℝᴾ` orthonormal spanning `Q`,
then `⟨α, ξ⟩ = s α(())` with `s = ±1`, since `τ` is the empty family `()`. -/
theorem Submission.regcomp_cop_zdr_unitOrientation_zero : ∀ (P : ℕ) (ξ : MultiVector P 0) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∃ s : ℝ, |s| = 1 ∧ ∀ α : Covector (Euclid P) 0, ξ α = s * α (fun i => i.elim0) := by
  intro P ξ Q hξ
  obtain ⟨τ, -, -, h | h⟩ := hξ
  -- `Fin 0 → ℝᴾ` has exactly one element, so `τ = ()`
  · exact ⟨1, abs_one, fun α => by rw [h α, one_mul, Subsingleton.elim τ fun i => i.elim0]⟩
  · exact ⟨-1, by rw [abs_neg, abs_one],
      fun α => by rw [h α, neg_one_mul, Subsingleton.elim τ fun i => i.elim0]⟩
/-- **`H⁰`-integral over a set meeting `K` in at most one point** (`H⁰ = μH[0]` is counting
measure, Simon Ch. 2).  If `F` vanishes off the measurable set `K` and `C ∩ K ⊆ {x}`, then
`∫_C F dH⁰ = 1_C(x) F(x)` for an arbitrary (possibly non-measurable) set `C`: `F = 1_K F`, so
`∫_C F dH⁰ = ∫_{C ∩ K} F dH⁰` by measurability of `K` alone, and `C ∩ K` is either `{x}`, of
`H⁰`-measure `1`, or empty, in which case `x ∈ C` forces `x ∉ K` and `F(x) = 0`. -/
theorem Submission.regcomp_cop_zdr_setIntegral_eq_indicator : ∀ (P : ℕ) (C K : Set (Euclid P)) (x : Euclid P) (F : Euclid P → ℝ), MeasurableSet K → (∀ z, z ∉ K → F z = 0) → C ∩ K ⊆ {x} → ∫ z in C, F z ∂μHE[0] = C.indicator F x := by
  intro P C K x F hK hF hCK
  -- `F = 1_K F`, and `∫_C 1_K F dH⁰ = ∫_{C ∩ K} F dH⁰` as `K` is measurable
  have hFK : K.indicator F = F := Set.indicator_eq_self.2 fun z hz => by
    by_contra hzK
    exact hz (hF z hzK)
  rw [← hFK, setIntegral_indicator hK]
  by_cases hx : x ∈ C ∩ K
  · -- `C ∩ K = {x}` and `H⁰{x} = 1`
    rw [Set.Subset.antisymm hCK (Set.singleton_subset_iff.2 hx), integral_singleton,
      measureReal_def, Measure.euclideanHausdorffMeasure_zero,
      Measure.hausdorffMeasure_zero_singleton, ENNReal.toReal_one, one_smul,
      Set.indicator_of_mem hx.1, Set.indicator_of_mem hx.2]
  · -- `C ∩ K = ∅`, and `1_C 1_K F` vanishes at `x`, since `x ∈ C` forces `x ∉ K`
    rw [Set.eq_empty_of_subset_empty fun z hz => hx (Set.mem_singleton_iff.1 (hCK hz) ▸ hz),
      setIntegral_empty]
    by_cases hxC : x ∈ C
    · rw [Set.indicator_of_mem hxC, Set.indicator_of_notMem fun hxK => hx ⟨hxC, hxK⟩]
    · rw [Set.indicator_of_notMem hxC]
/-- **Bump test `0`-forms** (`𝒟⁰(U)`, Simon Ch. 6, §2, with the Euclidean coefficient norm of
`M_W`, 6.2.5).  For `a > 0` with `B̄_a(z) ⊆ U` and `c ∈ ℝ`, put
`ω(x) = c·g(x)·ε₀`, where `g` is a smooth bump at `z` with `g = 1` on `B̄_{a/2}(z)`, `0 ≤ g ≤ 1`
and `g = 0` off `B_a(z)`, and `ε₀` is the constant `0`-covector `1`.  Then `ω ∈ 𝒟⁰(U)`,
`spt ω ⊆ B̄_a(z)`, `ω(z)() = c` and `ω = 0` off `B_a(z)`.  The only index map `Fin 0 → Fin P` is
the empty, strictly increasing one, so a `0`-covector `α` has coefficient norm `|α()|`, and
`|ω(x)()| = |c|·g(x) ≤ |c|`. -/
theorem Submission.regcomp_cop_zdr_exists_bumpForm : ∀ (P : ℕ) (U : Set (Euclid P)) (z : Euclid P) (a c : ℝ), 0 < a → closedBall z a ⊆ U → ∃ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ closedBall z a ∧ (ω : DifferentialForm (Euclid P) 0) z (fun i => i.elim0) = c ∧ (∀ x, x ∉ ball z a → (ω : DifferentialForm (Euclid P) 0) x = 0) ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) 0) x) ≤ |c| := by
  intro P U z a c ha haU
  -- in degree `0` the coefficient norm is `|α()|`: the only index map is the empty one
  have hnorm : ∀ α : Covector (Euclid P) 0,
      covectorEuclideanNorm α = |α (fun i => i.elim0)| := by
    intro α
    classical
    unfold covectorEuclideanNorm
    rw [Fintype.sum_unique]
    have hmono : StrictMono (default : Fin 0 → Fin P) := fun i => i.elim0
    rw [ite_eq_left hmono, Real.sqrt_sq_eq_abs]
    congr 1
    congr 1
    funext i
    exact i.elim0
  -- the bump `g` (radii `a/2 < a`), the constant `0`-covector `ε₀ = 1`, and `ω = c·g·ε₀`
  let g : ContDiffBump z := ⟨a / 2, a, half_pos ha, half_lt_self ha⟩
  let e : Covector (Euclid P) 0 :=
    ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ)
  have he : ∀ v, e v = 1 := fun v => rfl
  let f : DifferentialForm (Euclid P) 0 := fun x => (c * g x) • e
  -- (iii) `ω = 0` off `B_a(z)`, as `g` vanishes there
  have hzero : ∀ x, x ∉ ball z a → f x = 0 := by
    intro x hx
    have hgx : g x = 0 := g.zero_of_le_dist (by simpa [mem_ball, not_lt] using hx)
    simp [f, hgx]
  -- (i) `spt ω ⊆ closure (B_a(z)) ⊆ B̄_a(z)`
  have hts : tsupport f ⊆ closedBall z a := by
    refine (closure_mono ?_).trans closure_ball_subset_closedBall
    intro x hx
    by_contra h
    exact hx (hzero x h)
  -- `ω` is smooth with compact support in `B̄_a(z) ⊆ U`, so `ω ∈ 𝒟⁰(U)`
  have hsmooth : IsSmoothForm f := by
    unfold IsSmoothForm
    exact (contDiff_const.mul g.contDiff).smul contDiff_const
  have hcs : HasCompactSupport f :=
    (isCompact_closedBall z a).of_isClosed_subset (isClosed_tsupport f) hts
  refine ⟨⟨f, ⟨hsmooth, hcs⟩, hts.trans haU⟩, hts, ?_, hzero, ?_⟩
  -- (ii) `ω(z)() = c·g(z) = c`, as `g = 1` on `B̄_{a/2}(z)`
  · have hg1 : g z = 1 := g.one_of_mem_closedBall (mem_closedBall_self (half_pos ha).le)
    show (c * g z) • e (fun i => i.elim0) = c
    rw [hg1, he]
    simp
  -- (iv) `|ω(x)()| = |c|·g(x) ≤ |c|`, as `0 ≤ g ≤ 1`
  · intro x
    rw [hnorm]
    show |(c * g x) • e (fun i => i.elim0)| ≤ |c|
    rw [he, smul_eq_mul, mul_one, abs_mul]
    have h0 : 0 ≤ g x := g.nonneg
    have h1 : g x ≤ 1 := g.le_one
    rw [abs_of_nonneg h0]
    exact mul_le_of_le_one_right (abs_nonneg c) h1
/-- **Degree-0 integer multiplicity triples** (Simon Ch. 3, 1.1 and 1.4; Ch. 6, 3.1; `H⁰` is
counting measure, Ch. 2).  For `R = (M, θ, ξ) ∈ IMRep U 0`: (i) `M` is countable, since the null
set of the rectifiable cover has `H⁰`-measure `≥ 1` unless empty and `ℝ⁰` is a point; (ii) for
compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dH⁰ < ∞` and `H⁰(M ∩ K) ≤ μ_R(K)` as `θ ≥ 1` on `M`, so
`M ∩ K` is finite; (iii) each point of `M` has `H⁰⌞M`-mass `1`, so the a.e. orientation property
holds everywhere on `M`, and `ξ(x)` maps the constant covector `1` to `±1`, so `ξ(x) ≠ 0`;
(iv) for `U` open, carrier points have `μ_R`-mass `θ(x) ≥ 1`, and a point of `U \ M` has a
neighbourhood missing the locally finite `M`, so `U ∩ spt μ_R = M`. -/
theorem Submission.dor_zdm_imrep_zero_structure : ∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0), R.carrier.Countable ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → (R.carrier ∩ K).Finite ∧ R.measure K ≠ ∞) ∧ (∀ x ∈ R.carrier, (∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q) ∧ R.orient x ≠ 0) ∧ (IsOpen U → U ∩ R.measure.support = R.carrier) := by
  intro P U R
  -- `H⁰ = μH[0]`: points have mass `1` and nonempty sets mass `≥ 1`
  have hpt : ∀ z : Euclid P, μHE[0] ({z} : Set (Euclid P)) = 1 := fun z => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hne : ∀ S : Set (Euclid P), S.Nonempty → 1 ≤ μHE[0] S := fun S hS => by
    rw [Measure.euclideanHausdorffMeasure_zero]
    exact Measure.one_le_hausdorffMeasure_zero_of_nonempty hS
  -- (i) the null set `M₀` of the rectifiable cover is empty and each `F_j(ℝ⁰)` is a point
  have hcount : R.carrier.Countable := by
    obtain ⟨M₀, hM₀, F, -, hcover⟩ := R.rectifiable
    have hM₀e : M₀ = ∅ := by
      by_contra h
      have h1 := hne M₀ (Set.nonempty_iff_ne_empty.2 h)
      rw [hM₀] at h1
      simp at h1
    rw [hM₀e, Set.empty_union] at hcover
    exact Set.Countable.mono hcover
      (Set.countable_iUnion fun j => (Set.subsingleton_range (F j)).countable)
  -- (ii) `μ_R(K) = ∫_{M ∩ K} θ dH⁰ < ∞`, and `H⁰(M ∩ K) ≤ μ_R(K)` since `θ ≥ 1` on `M`
  have hloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      (R.carrier ∩ K).Finite ∧ R.measure K ≠ ∞ := by
    intro K hK hKU
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[0] := by
      rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_comm]
    have hfin : μHE[0] (R.carrier ∩ K) ≠ ∞ := by
      refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
      calc μHE[0] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, 1 ∂μHE[0] := (setLIntegral_one _).symm
        _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[0] :=
          setLIntegral_mono' (R.measurableSet_carrier.inter hKm) fun x hx => by
            exact_mod_cast R.mult_pos x hx.1
    refine ⟨?_, by rw [hmeas]; exact R.locallyIntegrable_mult K hK hKU⟩
    -- an infinite `M ∩ K` contains `m`-point sets of `H⁰`-measure `m` for every `m`
    by_contra hinf
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hfin
    obtain ⟨t, hts, rfl⟩ := Set.Infinite.exists_subset_card_eq hinf m
    have ht : μHE[0] (t : Set (Euclid P)) = t.card := by
      rw [← sum_measure_singleton]
      simp only [hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hle := measure_mono (μ := μHE[0]) hts
    rw [ht] at hle
    exact absurd hle (not_le.2 hm)
  -- (iii) every point of `M` has `H⁰⌞M`-mass `1`, so the a.e. property holds at each point
  have horient : ∀ x ∈ R.carrier, (∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q) ∧
      R.orient x ≠ 0 := by
    intro x hx
    have hQ : ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt 0 R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
      by_contra hnot
      have h1 : (μHE[0].restrict R.carrier) {x} = 0 :=
        measure_mono_null (Set.singleton_subset_iff.2 hnot) (ae_iff.1 R.orients)
      rw [Measure.restrict_apply' R.measurableSet_carrier, Set.singleton_inter_of_mem hx, hpt] at h1
      exact one_ne_zero h1
    refine ⟨hQ, fun h0 => ?_⟩
    -- `ξ(x)` maps the constant `0`-covector `1` to `±1`
    obtain ⟨Q, -, τ, -, -, hξ⟩ := hQ
    rcases hξ with h | h
    · have h1 := h (ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ))
      simp [h0, ContinuousAlternatingMap.constOfIsEmpty_apply] at h1
    · have h1 := h (ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (1 : ℝ))
      simp [h0, ContinuousAlternatingMap.constOfIsEmpty_apply] at h1
  refine ⟨hcount, hloc, horient, fun hU => Set.Subset.antisymm ?_ fun x hx => ?_⟩
  · -- (iv, ⊆) a point of `U \ M` has a neighbourhood missing the finite set `M ∩ B̄_{ε/2}(x)`
    rintro x ⟨hxU, hxs⟩
    by_contra hxM
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
    have hcb : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
    have hF := (hloc _ (isCompact_closedBall x (ε / 2)) hcb).1
    have hN : (R.carrier ∩ closedBall x (ε / 2))ᶜ ∩ closedBall x (ε / 2) ∈ 𝓝 x :=
      Filter.inter_mem (hF.isClosed.isOpen_compl.mem_nhds fun h => hxM h.1)
        (closedBall_mem_nhds x (half_pos hε))
    have h0 : (μHE[0].restrict R.carrier)
        ((R.carrier ∩ closedBall x (ε / 2))ᶜ ∩ closedBall x (ε / 2)) = 0 := by
      rw [Measure.restrict_apply' R.measurableSet_carrier]
      convert measure_empty (μ := (μHE[0] : Measure (Euclid P)))
      exact Set.eq_empty_iff_forall_notMem.2 fun z ⟨⟨h1, h2⟩, h3⟩ => h1 ⟨h3, h2⟩
    exact ((Measure.mem_support_iff_forall x).1 hxs _ hN).ne'
      (withDensity_absolutelyContinuous _ _ h0)
  · -- (iv, ⊇) a carrier point has `μ_R`-mass `θ(x) ≥ 1`
    refine ⟨R.carrier_subset hx, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    have hx1 : R.measure {x} = R.mult x := by
      rw [IMRep.measure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
        Measure.restrict_apply' R.measurableSet_carrier, Set.singleton_inter_of_mem hx, hpt,
        mul_one]
    calc (0 : ℝ≥0∞) < R.mult x := by exact_mod_cast R.mult_pos x hx
      _ = R.measure {x} := hx1.symm
      _ ≤ R.measure N := measure_mono (Set.singleton_subset_iff.2 (mem_of_mem_nhds hN))
/-- The point current `ω ↦ ξ₀(ω(x))` at `x ∈ U` (Simon 6.2.1, 6.2.11).  It is linear, and it is
continuous: if `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then `ωⱼ(x) → 0` by uniform
convergence of the order-`0` derivatives on `K` when `x ∈ K`, and `ωⱼ(x) = 0` when `x ∉ K`.  Let
`ξ₀(α₀) ≠ 0`.  For each open `W ∋ x`, a bump `φ` at `x` supported in `W` gives
`D(φα₀) = ξ₀(α₀) ≠ 0`, so `x ∈ spt D`.  Each `z ∈ U ∖ {x}` has a ball `B_ρ(z)` with
`B̄_ρ(z) ⊆ U` and `x ∉ B_ρ(z)`; `D` vanishes there, so `z ∉ spt D`. -/
theorem Submission.dor_zdm_point_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (ξ₀ : MultiVector P n), IsOpen U → x ∈ U → (∃ D : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, D ω = ξ₀ ((ω : DifferentialForm (Euclid P) n) x)) ∧ ∀ D : GeometricCurrentOn U n, (∀ ω : TestFormOn U n, D ω = ξ₀ ((ω : DifferentialForm (Euclid P) n) x)) → ξ₀ ≠ 0 → D.support = {x} := by
  intro P n U x ξ₀ hU hxU
  refine ⟨?_, fun D hD hξ₀ => ?_⟩
  · -- (a) `L(ω) = ξ₀(ω(x))` is linear and sequentially continuous
    let L : TestFormOn U n →ₗ[ℝ] ℝ :=
      { toFun := fun ω => ξ₀ ((ω : DifferentialForm (Euclid P) n) x)
        map_add' := fun ω η => by simp
        map_smul' := fun c ω => by simp }
    refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩
    obtain ⟨K, -, -, hωK, -, hderiv⟩ := hωs
    by_cases hxK : x ∈ K
    · -- `ωⱼ(x) → 0`: the order-`0` derivatives converge uniformly on `K ∋ x`
      have h0 := ((continuousMultilinearCurryFin0 ℝ (Euclid P)
        (Covector (Euclid P) n)).continuous.tendsto _).comp ((hderiv 0).tendsto_at hxK)
      have h1 : Tendsto (fun j => ((ωs j : TestFormOn U n) : DifferentialForm (Euclid P) n) x)
          atTop (𝓝 0) := by
        simpa [Function.comp_def] using h0
      simpa [L, Function.comp_def] using (ξ₀.continuous.tendsto 0).comp h1
    · -- `x ∉ K ⊇ tsupport ωⱼ`, so `ωⱼ(x) = 0` for every `j`
      have h : ∀ j, ((ωs j : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 :=
        fun j => image_eq_zero_of_notMem_tsupport fun hx => hxK (hωK j hx)
      simp [L, h]
  · -- (b) `D(ω) = 0` whenever `x ∉ tsupport ω`
    have hD0 : ∀ ω : TestFormOn U n, x ∉ tsupport (ω : DifferentialForm (Euclid P) n) →
        D ω = 0 := by
      intro ω hω
      rw [hD, image_eq_zero_of_notMem_tsupport hω, map_zero]
    apply Set.Subset.antisymm
    · -- every `z ∈ U ∖ {x}` lies in a ball `B_ρ(z)`, `B̄_ρ(z) ⊆ U`, `x ∉ B_ρ(z)`, where `D = 0`
      rintro z ⟨hzU, hz⟩
      by_contra hzx
      apply hz
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hzU
      have hd : 0 < dist z x := dist_pos.mpr hzx
      have hρ0 : 0 < min (ε / 2) (dist z x / 2) := lt_min (half_pos hε) (half_pos hd)
      have hρε : min (ε / 2) (dist z x / 2) < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
      have hρd : min (ε / 2) (dist z x / 2) < dist z x :=
        (min_le_right _ _).trans_lt (half_lt_self hd)
      refine Set.mem_sUnion_of_mem (mem_ball_self hρ0) ⟨isOpen_ball,
        (isCompact_closedBall z _).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall,
        closure_ball_subset_closedBall.trans ((closedBall_subset_ball hρε).trans hεU),
        fun ω hω => hD0 ω fun hx => ?_⟩
      have h1 : dist x z < min (ε / 2) (dist z x / 2) := hω hx
      rw [dist_comm] at h1
      linarith
    · -- `x ∈ spt D`: a bump form `φα₀` at `x` with `ξ₀(α₀) ≠ 0` fits in every open `W ∋ x`
      refine Set.singleton_subset_iff.mpr ⟨hxU, fun hx => ?_⟩
      obtain ⟨W, ⟨hWo, -, hWU, hWD⟩, hxW⟩ := hx
      obtain ⟨α₀, hα₀⟩ : ∃ α₀, ξ₀ α₀ ≠ 0 := by
        by_contra! h
        exact hξ₀ (ContinuousLinearMap.ext h)
      obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hWo x hxW
      let φ : ContDiffBump x := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
      let ω : DifferentialForm (Euclid P) n := fun y => φ y • α₀
      have hωW : tsupport ω ⊆ W := (tsupport_smul_subset_left _ _).trans
        (φ.tsupport_eq.trans_subset ((closedBall_subset_ball (half_lt_self hε)).trans hεW))
      have hωU : ω ∈ TestFormOn U n :=
        ⟨⟨φ.contDiff.smul contDiff_const, φ.hasCompactSupport.smul_right⟩,
          hωW.trans (subset_closure.trans hWU)⟩
      have h1 := hWD ⟨ω, hωU⟩ hωW
      rw [hD] at h1
      apply hα₀
      simpa [ω, φ.one_of_mem_closedBall (mem_closedBall_self φ.rIn_pos.le)] using h1

/-- **Erasing a point of a degree-0 triple** (Simon Ch. 3, 1.4; Ch. 6, 3.1; `H⁰` is counting
measure, Ch. 2).  For `R = (M, θ, ξ) ∈ IMRep U 0` and `x ∈ M`, `R' = (M ∖ {x}, θ, ξ)` is again a
triple: at `y ∈ M ∖ {x}` the blow-ups `η_{y,λ}(M)` and `η_{y,λ}(M ∖ {x})` differ only at
`η_{y,λ}(x)`, which leaves the support of each `f ∈ C_c` for small `λ`, so `M ∖ {x}` keeps the
approximate tangent space `TᵧM` oriented by `ξ(y)`; the other fields pass to the subset.  As
`H⁰⌞M = H⁰⌞(M ∖ {x}) + δₓ`, `μ_R = μ_{R'} + θ(x)δₓ`.  The integrand `θ⟨ω, ξ⟩` vanishes off the
compact `spt ω ⊆ U`, which meets `M` in a finite set, so it is integrable on `M`, and splitting
off `{x}` gives `R'(ω) = R(ω) − θ(x)⟨ω(x), ξ(x)⟩`. -/
theorem Submission.dor_zdm_imrep_zero_erase_point : ∀ (P : ℕ) (U : Set (Euclid P)) (R : IMRep U 0) (x : Euclid P), x ∈ R.carrier → ∃ R' : IMRep U 0, R'.carrier = R.carrier \ {x} ∧ R.measure = R'.measure + (R.mult x : ℝ≥0∞) • Measure.dirac x ∧ ∀ ω : TestFormOn U 0, R'.action (ω : DifferentialForm (Euclid P) 0) = R.action (ω : DifferentialForm (Euclid P) 0) - (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 0) x) := by
  intro P U R x hx
  -- (i) `M` is countable, (ii) `M ∩ K` is finite for compact `K ⊆ U`, (iii) `M` is oriented
  -- at each of its points
  obtain ⟨hcount, hloc, horient, -⟩ := Submission.dor_zdm_imrep_zero_structure P U R
  -- `H⁰{z} = 1`, as `μHE[0] = μH[0]`
  have hpt : ∀ z : Euclid P, μHE[0] ({z} : Set (Euclid P)) = 1 := fun z => by
    rw [Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton]
  have hxM : {x} ⊆ R.carrier := Set.singleton_subset_iff.2 hx
  have hM' : MeasurableSet (R.carrier \ {x}) :=
    R.measurableSet_carrier.diff (measurableSet_singleton x)
  -- step 1: at `y ∈ M ∖ {x}`, `M ∖ {x}` keeps the approximate tangent space `TᵧM` of `M`
  have htan : ∀ y ∈ R.carrier \ {x}, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt 0 (R.carrier \ {x}) y Q ∧
        IsUnitOrientationOf (R.orient y) Q := by
    rintro y ⟨hyM, hyx⟩
    obtain ⟨Q, hT, hξ⟩ := (horient y hyM).1
    refine ⟨Q, ⟨hT.1, fun f => ?_⟩, hξ⟩
    -- `spt f ⊆ B̄_a(0)` with `a > 0`, and `|x − y| > 0`
    obtain ⟨a, ha, hfa⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
    have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hyx h.symm)
    refine (hT.2 f).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (div_pos hd ha)] with r hr
    -- `f` vanishes at `η_{y,r}(x) = r⁻¹(x − y)`, whose norm `r⁻¹|x − y|` exceeds `a`
    have hfx : f (Poincare.SimonGMT.Chapter03.blowUpMap y r x) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
      have h1 := mem_closedBall_zero_iff.1 (hfa hmem)
      rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, norm_inv,
        Real.norm_of_nonneg hr.1.le, inv_mul_le_iff₀ hr.1] at h1
      have h2 := (lt_div_iff₀ ha).1 hr.2
      linarith
    -- `η_{y,r}(M)` is countable, hence Borel, and `η_{y,r}(M) ∖ η_{y,r}(M ∖ {x}) ⊆ {η_{y,r}(x)}`
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hcount.image _).measurableSet
      (Set.image_mono Set.sdiff_subset) ?_
    rintro _ ⟨⟨w, hw, rfl⟩, hws⟩
    by_cases hwx : w = x
    · rw [hwx]
      exact hfx
    · exact absurd ⟨w, ⟨hw, hwx⟩, rfl⟩ hws
  -- step 2: `R' = (M ∖ {x}, θ, ξ)`; the other fields of `R` pass to the smaller carrier
  let R' : IMRep U 0 :=
    { carrier := R.carrier \ {x}
      mult := R.mult
      orient := R.orient
      measurableSet_carrier := hM'
      carrier_subset := Set.sdiff_subset.trans R.carrier_subset
      rectifiable := R.rectifiable.mono Set.sdiff_subset
      measurable_mult := R.measurable_mult
      mult_pos := fun z hz => R.mult_pos z hz.1
      locallyIntegrable_mult := fun K hK hKU =>
        ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU)
          (lintegral_mono_set (Set.inter_subset_inter_left K Set.sdiff_subset))
      aestronglyMeasurable_orient :=
        R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono Set.sdiff_subset le_rfl)
      orients := (ae_restrict_iff' hM').2 (Eventually.of_forall htan) }
  refine ⟨R', rfl, ?_, fun ω => ?_⟩
  · -- step 3: `H⁰⌞M = H⁰⌞(M ∖ {x}) + H⁰{x} δₓ` and `δₓ.withDensity θ = θ(x) δₓ`
    have hsplit : μHE[0].restrict R.carrier =
        μHE[0].restrict (R.carrier \ {x}) + μHE[0].restrict {x} := by
      conv_lhs => rw [← Set.sdiff_union_of_subset hxM]
      exact Measure.restrict_union Set.disjoint_sdiff_left (measurableSet_singleton x)
    show (μHE[0].restrict R.carrier).withDensity (fun z => (R.mult z : ℝ≥0∞)) =
      (μHE[0].restrict (R.carrier \ {x})).withDensity (fun z => (R.mult z : ℝ≥0∞)) +
        (R.mult x : ℝ≥0∞) • Measure.dirac x
    rw [hsplit, withDensity_add_measure, Measure.restrict_singleton, hpt, one_smul,
      dirac_withDensity]
  · -- step 4: `g = θ⟨ω, ξ⟩` vanishes off the compact `spt ω ⊆ U`, which meets `M` finitely
    obtain ⟨⟨-, hK⟩, hKU⟩ := ω.2
    set g : Euclid P → ℝ :=
      fun z => (R.mult z : ℝ) * R.orient z ((ω : DifferentialForm (Euclid P) 0) z) with hg
    have hg0 : ∀ z ∉ tsupport (ω : DifferentialForm (Euclid P) 0), g z = 0 := fun z hz => by
      simp only [hg, image_eq_zero_of_notMem_tsupport hz, map_zero, mul_zero]
    have hgK : IntegrableOn g (R.carrier ∩ tsupport (ω : DifferentialForm (Euclid P) 0))
        μHE[0] := by
      rw [← Set.biUnion_of_singleton (R.carrier ∩ tsupport (ω : DifferentialForm (Euclid P) 0)),
        integrableOn_finite_biUnion (hloc _ hK.isCompact hKU).1]
      exact fun z _ => integrableOn_singleton (hx := (hpt z).trans_lt ENNReal.one_lt_top)
    have hgM : IntegrableOn g R.carrier μHE[0] :=
      hgK.of_forall_sdiff_eq_zero R.measurableSet_carrier fun z hz =>
        hg0 z fun hzK => hz.2 ⟨hz.1, hzK⟩
    -- `∫_M g = ∫_{M ∖ {x}} g + H⁰{x} g(x)` and `H⁰{x} = 1`
    have hsplit := setIntegral_union (μ := μHE[0]) Set.disjoint_sdiff_left
      (measurableSet_singleton x) (hgM.mono_set Set.sdiff_subset) (hgM.mono_set hxM)
    rw [Set.sdiff_union_of_subset hxM, integral_singleton, measureReal_def, hpt,
      ENNReal.toReal_one, one_smul] at hsplit
    show ∫ z in R.carrier \ {x}, g z ∂μHE[0] = ∫ z in R.carrier, g z ∂μHE[0] - g x
    rw [hsplit, add_sub_cancel_right]

/-- **Local form of a `0`-current at a regular point** (Simon 7.4.1 with `n = 0`; Ch. 2, §4).
If `y ∈ reg T`, `T ∈ 𝒟₀(U)`, then `T(ω) = c ω(y)()` with `|c| ≥ 1` whenever `spt ω ⊆ B_r(y)`.
Write `T = m[[M]]` in `B_ρ(y)`.  A chart `ψ : V → W` of the `0`-dimensional `M` at `y` has
domain `V ⊆ ℝ⁰ = {0}`, so `W ∩ M = ψ(V) = {y}`.  For `B_r(y) ⊆ W ∩ B_ρ(y)`, the integrand
`⟨ω, ξ⟩` vanishes off `spt ω`, which meets `M` at most in `y`; hence
`T(ω) = m ⟨ω(y), ξ(y)⟩ = m s ω(y)()`, where `⟨α, ξ(y)⟩ = s α()` with `|s| = 1`, and `c = ms`
has `|c| = |m| ≥ 1`. -/
theorem Submission.regcomp_cop_zdr_regular_local_form : ∀ (P : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U 0) (y : Euclid P), y ∈ regularSet T → ∃ r : ℝ, 0 < r ∧ ball y r ⊆ U ∧ ∃ c : ℝ, 1 ≤ |c| ∧ ∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ ball y r → T ω = c * (ω : DifferentialForm (Euclid P) 0) y (fun i => i.elim0) := by
  intro P U T y hy
  -- step 1: `T = m[[M]]` in `B_ρ(y)`, with `m ≠ 0` and `y ∈ M`, `M` oriented by `ξ`
  obtain ⟨-, ρ, hρ, hρU, m, M, ξ, hm, hyM, hM, hξ, -, hT⟩ := hy
  -- step 2a: a chart `ψ : V → W` at `y` has `V ⊆ ℝ⁰`, a subsingleton, so `W ∩ M ⊆ {y}`
  obtain ⟨V, W, ψ, -, hW, hyW, -, -, hψ, -, -⟩ := hM y hyM
  have hyψ : y ∈ ψ '' V := by
    rw [hψ]
    exact ⟨hyW, hyM⟩
  obtain ⟨z₀, -, hz₀⟩ := hyψ
  have hWM : W ∩ M ⊆ {y} := by
    rw [← hψ]
    rintro _ ⟨z, -, rfl⟩
    rw [Subsingleton.elim z z₀, hz₀]
    exact mem_singleton y
  -- step 2b: `r = min(r₀, ρ)` with `B_{r₀}(y) ⊆ W`, so `M ∩ B_r(y) ⊆ {y}`
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.isOpen_iff.mp hW y hyW
  have hrρ : ball y (min r₀ ρ) ⊆ ball y ρ := ball_subset_ball (min_le_right _ _)
  have hMr : M ∩ ball y (min r₀ ρ) ⊆ {y} := fun x hx =>
    hWM ⟨hr₀W (ball_subset_ball (min_le_left _ _) hx.2), hx.1⟩
  -- step 2c: `ξ(y)(α) = s α()` with `|s| = 1`, and `c = ms` has `|c| = |m| ≥ 1`
  obtain ⟨Q, -, hQ⟩ := hξ.2 y hyM
  obtain ⟨s, hs, hξs⟩ := Submission.regcomp_cop_zdr_unitOrientation_zero P (ξ y) Q hQ
  refine ⟨min r₀ ρ, lt_min hr₀ hρ, hrρ.trans hρU, m * s, ?_, fun ω hω => ?_⟩
  · rw [abs_mul, hs, mul_one]
    exact_mod_cast Int.one_le_abs hm
  -- step 2d: `⟨ω, ξ⟩` vanishes off `spt ω`, which meets `M` at most in `y`
  rw [hT ω (hω.trans hrρ), Submission.regcomp_cop_zdr_setIntegral_eq_indicator P M
      (tsupport (ω : DifferentialForm (Euclid P) 0)) y
      (fun x => ξ x ((ω : DifferentialForm (Euclid P) 0) x)) (isClosed_tsupport _).measurableSet
      (fun z hz => by simp only [image_eq_zero_of_notMem_tsupport hz, map_zero])
      ((inter_subset_inter_right M hω).trans hMr),
    indicator_of_mem hyM, hξs, mul_assoc]
/-- **A degree-0 point mass is carried by an isolated carrier point** (Simon Ch. 6, 3.1).  Let
`T = τ(C, θ, ξ) ∈ 𝒟₀(U)` with `T(ω) = c ω(y)`, `c ≠ 0`, for every `ω ∈ 𝒟⁰(U)` with
`spt ω ⊆ B_r(y) ⊆ U`.  As `C` is finite on compact subsets of `U` and `ξ(x) = ±` evaluation on `C`,
`T(ω) = θ(x) ξ(x)(ω(x))` whenever `spt ω ⊆ B̄_a(x)` and `C ∩ B̄_a(x) = {x}`.  A bump form at a point
`x ≠ y` of `C ∩ B_r(y)`, on a ball isolating `x` in `C` and missing `y`, then gives
`0 = c ω(y) = θ(x) ξ(x)(ω(x)) = ±θ(x) ≠ 0`; so `C ∩ B_r(y) ⊆ {y}`.  If `y ∉ C`, then `C` misses
`B_r(y)`, and a bump form at `y` gives `c = T(ω) = 0`; so `y ∈ C`. -/
theorem Submission.regcomp_cop_zdr_isolated_carrier_point : ∀ (P : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U 0) (R : IMRep U 0) (y : Euclid P) (r c : ℝ), R.Represents T → 0 < r → ball y r ⊆ U → c ≠ 0 → (∀ ω : TestFormOn U 0, tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ ball y r → T ω = c * (ω : DifferentialForm (Euclid P) 0) y (fun i => i.elim0)) → y ∈ R.carrier ∧ R.carrier ∩ ball y r ⊆ {y} := by
  intro P U T R y r c hRT hr hrU hc hloc
  -- (1) `C` is finite on compact subsets of `U`, and `ξ(x) = s ·` evaluation with `|s| = 1` on `C`
  obtain ⟨-, hfin, horient, -⟩ := Submission.dor_zdm_imrep_zero_structure P U R
  have hsgn : ∀ x ∈ R.carrier, ∃ s : ℝ, |s| = 1 ∧
      ∀ α : Covector (Euclid P) 0, R.orient x α = s * α (fun i => i.elim0) := by
    intro x hx
    obtain ⟨⟨Q, -, hQ⟩, -⟩ := horient x hx
    exact Submission.regcomp_cop_zdr_unitOrientation_zero P (R.orient x) Q hQ
  -- (2) the integrand `θ(z) ξ(z)(ω(z))` of `T(ω)` vanishes off `spt ω`
  have hvan : ∀ (ω : TestFormOn U 0) (z : Euclid P),
      z ∉ tsupport (ω : DifferentialForm (Euclid P) 0) →
        (R.mult z : ℝ) * R.orient z ((ω : DifferentialForm (Euclid P) 0) z) = 0 :=
    fun ω z hz => by rw [image_eq_zero_of_notMem_tsupport hz, map_zero, mul_zero]
  -- (3) `T(ω) = θ(x) ξ(x)(ω(x))` if `x ∈ C`, `C ∩ B̄_a(x) ⊆ {x}` and `spt ω ⊆ B̄_a(x)`
  have hatom : ∀ x ∈ R.carrier, ∀ (a : ℝ) (ω : TestFormOn U 0),
      R.carrier ∩ closedBall x a ⊆ {x} →
        tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ closedBall x a →
          T ω = (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) 0) x) := by
    intro x hx a ω hCa hωa
    rw [hRT ω, IMRep.action, Submission.regcomp_cop_zdr_setIntegral_eq_indicator P R.carrier
      (closedBall x a) x _ measurableSet_closedBall (fun z hz => hvan ω z fun h => hz (hωa h))
      hCa, indicator_of_mem hx]
  -- (4) `C ∩ B_r(y) ⊆ {y}`: a point `x ≠ y` of `C ∩ B_r(y)` is isolated in `C`, and a bump form
  -- at `x` vanishing at `y` has `T(ω) = c ω(y) = 0` but `T(ω) = θ(x) ξ(x)(ω(x)) = θ(x) s ≠ 0`
  have hstep4 : R.carrier ∩ ball y r ⊆ {y} := by
    rintro x ⟨hxC, hxr⟩
    by_contra hxy
    have hδ : 0 < dist x y := dist_pos.2 hxy
    have hrδ : 0 < r - dist x y := sub_pos.2 (mem_ball.1 hxr)
    -- (a), (b) `a₀ = min(r - δ, δ)/2` has `B̄_{a₀}(x) ⊆ B_r(y)` and `y ∉ B̄_{a₀}(x)`
    obtain ⟨a₀, ha₀, ha₀r, ha₀δ⟩ : ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < r - dist x y ∧ a₀ < dist x y :=
      ⟨min (r - dist x y) (dist x y) / 2, half_pos (lt_min hrδ hδ),
        (half_lt_self (lt_min hrδ hδ)).trans_le (min_le_left _ _),
        (half_lt_self (lt_min hrδ hδ)).trans_le (min_le_right _ _)⟩
    have ha₀sub : closedBall x a₀ ⊆ ball y r := fun z hz => mem_ball.2 <|
      calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
        _ < r := by linarith [mem_closedBall.1 hz]
    have hya₀ : y ∉ closedBall x a₀ := fun h => by
      rw [mem_closedBall, dist_comm] at h
      linarith
    -- (c) `(C ∩ B̄_{a₀}(x)) \ {x}` is finite, hence closed, and misses `x`
    have hcl : IsClosed ((R.carrier ∩ closedBall x a₀) \ {x}) :=
      ((hfin _ (isCompact_closedBall x a₀) (ha₀sub.trans hrU)).1.subset sdiff_subset).isClosed
    obtain ⟨ε, hε, hεball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x fun h => h.2 rfl
    -- (d) `a = min(ε/2, a₀)` has `C ∩ B̄_a(x) ⊆ {x}`
    obtain ⟨a, ha, haε, haa₀⟩ : ∃ a : ℝ, 0 < a ∧ a < ε ∧ a ≤ a₀ :=
      ⟨min (ε / 2) a₀, lt_min (half_pos hε) ha₀, (min_le_left _ _).trans_lt (half_lt_self hε),
        min_le_right _ _⟩
    have hBa : closedBall x a ⊆ closedBall x a₀ := closedBall_subset_closedBall haa₀
    have hCa : R.carrier ∩ closedBall x a ⊆ {x} := by
      rintro z ⟨hzC, hza⟩
      by_contra hzx
      exact hεball (mem_ball.2 ((mem_closedBall.1 hza).trans_lt haε)) ⟨⟨hzC, hBa hza⟩, hzx⟩
    -- (e) a bump form `ω` at `x` with `spt ω ⊆ B̄_a(x)` and `ω(x)(()) = 1`
    obtain ⟨ω, hωs, hωx, hωz, -⟩ :=
      Submission.regcomp_cop_zdr_exists_bumpForm P U x a 1 ha (hBa.trans (ha₀sub.trans hrU))
    -- (f) `T(ω) = c ω(y)(()) = 0`, as `y ∉ B̄_a(x)`
    have h1 : T ω = 0 := by
      rw [hloc ω (hωs.trans (hBa.trans ha₀sub)),
        hωz y fun h => hya₀ (hBa (ball_subset_closedBall h))]
      simp
    -- (g) `T(ω) = θ(x) ξ(x)(ω(x)) = θ(x) s ≠ 0`
    obtain ⟨s, hs, hsx⟩ := hsgn x hxC
    rw [hatom x hxC a ω hCa hωs, hsx, hωx, mul_one] at h1
    have hθ : (0 : ℝ) < R.mult x := by exact_mod_cast R.mult_pos x hxC
    have hs0 : s ≠ 0 := fun h => by
      rw [h, abs_zero] at hs
      exact zero_ne_one hs
    exact mul_ne_zero hθ.ne' hs0 h1
  -- (5) `y ∈ C`: otherwise `C` misses `B_r(y)` by (4), and a bump form at `y` has
  -- `T(ω) = c ω(y)(()) = c` but `T(ω) = 0`, its integrand vanishing on `C` by (2)
  refine ⟨?_, hstep4⟩
  by_contra hyC
  have hCr : ∀ z ∈ R.carrier, z ∉ ball y r := fun z hz hzr => by
    have hzy : z = y := hstep4 ⟨hz, hzr⟩
    exact hyC (hzy ▸ hz)
  obtain ⟨ω, hωs, hωy, -, -⟩ := Submission.regcomp_cop_zdr_exists_bumpForm P U y (r / 2) 1
    (half_pos hr) ((closedBall_subset_ball (half_lt_self hr)).trans hrU)
  have hωr : tsupport (ω : DifferentialForm (Euclid P) 0) ⊆ ball y r :=
    hωs.trans (closedBall_subset_ball (half_lt_self hr))
  have h0 : T ω = 0 := by
    rw [hRT ω, IMRep.action]
    exact setIntegral_eq_zero_of_forall_eq_zero fun z hz => hvan ω z fun h => hCr z hz (hωr h)
  rw [hloc ω hωr, hωy, mul_one] at h0
  exact hc h0

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
