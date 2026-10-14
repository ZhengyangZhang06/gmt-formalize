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

/-- `spt(S − T) ⊆ spt S ∪ spt T`.  A point `y ∈ U` outside `spt S ∪ spt T` lies in zero-region
sets `W₁` of `S` and `W₂` of `T`; then `W₁ ∩ W₂` is open, contains `y`, has compact closure in `U`
(a closed subset of `closure W₁`), and `S − T` vanishes on it, so `y ∉ spt(S − T)`. -/
theorem Submission.cbrld_ns_support_sub_subset : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n), (S - T).support ⊆ S.support ∪ T.support := by
  intro P n U S T y hy
  obtain ⟨hyU, hyZ⟩ := hy
  by_contra hST
  -- `y ∈ Z(S)` and `y ∈ Z(T)`, since `y ∈ U` lies in neither support
  have hS : y ∈ S.zeroRegion := not_not.mp fun h => hST (Or.inl ⟨hyU, h⟩)
  have hT : y ∈ T.zeroRegion := not_not.mp fun h => hST (Or.inr ⟨hyU, h⟩)
  obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hS
  obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hyW₂⟩ := mem_sUnion.mp hT
  -- `W₁ ∩ W₂` belongs to the family whose union is `Z(S − T)`
  have hcl : closure (W₁ ∩ W₂) ⊆ closure W₁ := closure_mono inter_subset_left
  refine hyZ (mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
    hW₁c.of_isClosed_subset isClosed_closure hcl, hcl.trans hW₁U, ?_⟩, hyW₁, hyW₂⟩)
  -- `(S − T)(ω) = S(ω) − T(ω) = 0 − 0`
  intro ω hω
  change S ω - T ω = 0
  rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
/-- `M_W(S − T) ≤ M_W(S) + M_W(T)`.  For every `W`-admissible `ω`, `−ω` is `W`-admissible as well
(`tsupport (−ω) = tsupport ω`, `|−ω(x)| = |ω(x)|`) and `(S − T)(ω) = S(ω) + T(−ω)`, so
`ofReal((S − T)(ω)) ≤ ofReal(S(ω)) + ofReal(T(−ω)) ≤ M_W(S) + M_W(T)`; take the supremum
over `ω`. -/
theorem Submission.cbrld_ns_massOn_sub_le : ∀ (P n : ℕ) (U W : Set (Euclid P)) (S T : GeometricCurrentOn U n), (S - T).massOn W ≤ S.massOn W + T.massOn W := by
  intro P n U W S T
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
  -- `(S − T)(ω) = S(ω) + T(−ω)`
  have heq : (S - T) ω = S ω + T (-ω) := by
    rw [show T (-ω) = -T ω from map_neg T.toCurrent ω]
    exact sub_eq_add_neg (S ω) (T ω)
  calc ENNReal.ofReal ((S - T) ω) = ENNReal.ofReal (S ω + T (-ω)) := by rw [heq]
    _ ≤ ENNReal.ofReal (S ω) + ENNReal.ofReal (T (-ω)) := ENNReal.ofReal_add_le
    _ ≤ S.massOn W + T.massOn W := add_le_add (S.le_massOn hω) (T.le_massOn hneg)
/-- **Mass of a current integrating over a ball** (first half of fact 1(e) in the null-set step
of the lower density bound used for Simon 7.2.4): if `|⟨α, ξ(y)⟩| ≤ |α|` for `μ`-a.e. `y` and
`A(ω) = ∫_{B_ρ(x)} ⟨ω(y), ξ(y)⟩ dμ(y)` for all `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `M(A) ≤ μ(B_ρ(x))`.  The bound
is trivial if `μ(B_ρ(x)) = ∞`; otherwise each admissible `ω` (`|ω| ≤ 1`) has
`A(ω) ≤ |∫_{B_ρ(x)} ⟨ω, ξ⟩ dμ| ≤ μ(B_ρ(x))`, and `M(A)` is the supremum of these values. -/
theorem Submission.cbrld_ns_ball_current_mass_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n) (x : Euclid P) (ρ : ℝ), (∀ᵐ y ∂μ, ∀ α : Covector (Euclid P) n, |ξ y α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ) → A.mass ≤ μ (ball x ρ) := by
  intro P n μ ξ A x ρ hξ hA
  -- the bound is trivial if `μ(B_ρ(x)) = ∞`
  rcases eq_top_or_lt_top (μ (ball x ρ)) with htop | hfin
  · exact htop ▸ le_top
  -- `M(A)` is the supremum of `A(ω)` over admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- `|⟨ω(y), ξ(y)⟩| ≤ |ω(y)| ≤ 1` for `μ⌞B_ρ(x)`-a.e. `y`
  have hbound : ∀ᵐ y ∂μ.restrict (ball x ρ),
      ‖ξ y ((ω : DifferentialForm (Euclid P) n) y)‖ ≤ 1 :=
    ae_restrict_of_ae (hξ.mono fun y hy => (Real.norm_eq_abs _).trans_le ((hy _).trans (hω.2 y)))
  have hle : A ω ≤ (μ (ball x ρ)).toReal := by
    rw [hA ω]
    calc ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ
        ≤ ‖∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ‖ := Real.le_norm_self _
      _ ≤ 1 * μ.real (ball x ρ) := norm_setIntegral_le_of_norm_le_const_ae hfin hbound
      _ = (μ (ball x ρ)).toReal := by rw [one_mul, measureReal_def]
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).2 hle
/-- `spt A ⊆ B̄_ρ(x)` when `A(ω) = ∫_{B_ρ(x)} ⟨ω(y), ξ(y)⟩ dμ(y)` for every test form `ω`.  If
`|y − x| > ρ`, then `W = B_r(y)`, `r = (|y − x| − ρ)/2 > 0`, is open with compact closure and
misses `B_ρ(x)`, so every test form supported in `W` vanishes on `B_ρ(x)` and `A` vanishes on `W`;
hence `y` lies in the zero region of `A` (Simon 6.2.11). -/
theorem Submission.cbrld_ns_ball_current_support_subset : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n) (x : Euclid P) (ρ : ℝ), (∀ ω : TestFormOn (univ : Set (Euclid P)) n, A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) n) y) ∂μ) → A.support ⊆ closedBall x ρ := by
  intro P n μ ξ A x ρ hA y hy
  by_contra hyx
  rw [mem_closedBall, not_le] at hyx
  -- `A` vanishes on `B_r(y)`, `r = (|y − x| − ρ)/2 > 0`, so `y` lies in the zero region of `A`
  have hr : 0 < (dist y x - ρ) / 2 := by linarith
  refine hy.2 (mem_sUnion_of_mem (mem_ball_self hr) ⟨isOpen_ball, ?_, subset_univ _, ?_⟩)
  · -- `closure B_r(y) ⊆ B̄_r(y)`, which is compact in the proper space `ℝᴾ`
    exact (isCompact_closedBall y _).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  · -- a test form supported in `B_r(y)` vanishes at every `z ∈ B_ρ(x)`, since `|z − y| > r`
    intro ω hω
    rw [hA ω]
    refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
    have hzω : z ∉ tsupport (ω : DifferentialForm (Euclid P) n) := by
      intro hz'
      have hzy := hω hz'
      rw [mem_ball] at hz hzy
      linarith [dist_triangle y z x, dist_comm z y]
    rw [image_eq_zero_of_notMem_tsupport hzω, map_zero]
/-- **Coordinate projections of `Hⁿ`-null sets are Lebesgue-null** (parent step 3).  For
injective `I : Fin n → Fin P` the coordinate projection `q x = (x (I k))ₖ : ℝᴾ → ℝⁿ` is
`1`-Lipschitz (the squares summed over `image I` are among those summed over `Fin P`), so
`μH[n] (q '' C) ≤ μH[n] C`.  `μHE[n] = c • μH[n]` with one nonzero constant `c` on every space,
and `μHE[n] = volume` on `ℝⁿ`; hence `μHE[n] C = 0` gives `volume (q '' C) = 0`.  No compactness
of `C` is needed. -/
theorem Submission.cmr_volume_coordProj_image_null : ∀ (P n : ℕ) (I : Fin n → Fin P) (C : Set (Euclid P)), Function.Injective I → μHE[n] C = 0 → volume ((fun x : Euclid P => (WithLp.toLp 2 (fun k => x (I k)) : Euclid n)) '' C) = 0 := by
  intro P n I C hI hC
  set q : Euclid P → Euclid n := fun x => WithLp.toLp 2 (fun k => x (I k))
  -- `q` is 1-Lipschitz: the squares summed over `image I` are among those summed over `Fin P`
  have hq : LipschitzWith 1 q := by
    refine LipschitzWith.mk_one fun x y => ?_
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k, dist ((q x).ofLp k) ((q y).ofLp k) ^ 2
        = ∑ k, dist (x.ofLp (I k)) (y.ofLp (I k)) ^ 2 := rfl
      _ = ∑ l ∈ Finset.univ.image I, dist (x.ofLp l) (y.ofLp l) ^ 2 := by
        rw [Finset.sum_image fun _ _ _ _ h => hI h]
      _ ≤ ∑ l, dist (x.ofLp l) (y.ofLp l) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  -- `μHE[n] = c • μH[n]` with `c ≠ 0`, so `μH[n] C = 0`
  have hc : (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
      μH[(n : ℝ)] : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul] at hC
  have hC' : μH[(n : ℝ)] C = 0 := (mul_eq_zero.mp hC).resolve_left hc
  -- `μH[n] (q '' C) ≤ 1 ^ n * μH[n] C = 0`
  have hqC : μH[(n : ℝ)] (q '' C) = 0 := by
    have h := hq.hausdorffMeasure_image_le (Nat.cast_nonneg n) C
    rw [hC', mul_zero] at h
    exact nonpos_iff_eq_zero.mp h
  -- on `ℝⁿ`, `volume = μHE[n] = c • μH[n]`
  rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hqC, smul_zero]
/-- **Simon 6.2.36** (`μ_T ≪ Hⁿ` for locally normal `T`; mass bound for the divergence
integral): let `T ∈ 𝒟_{m+1}(U)` satisfy `T(ω) = ∫ ⟨ω, ξ⟩ dμ`, and let `η`, `ζ` be test forms
supported in `spt b ⊆ W ⊆ U` with `|η|, |ζ| ≤ K` and `dη = b D θ + ζ`.  Then `ω = dη − ζ` is
a test form in `U` with `ω(x) = b(x) D(x) θ`, so `∫_W b ⟨θ, ξ⟩ D dμ = T(ω) = ∂T(η) − T(ζ)`,
and the evaluation bound gives `|∫_W b ⟨θ, ξ⟩ D dμ| ≤ K (M_W(∂T) + M_W(T))`. -/
theorem Submission.cmr_abs_integral_div_le_mass : ∀ (P m : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (m + 1)) (θ : Covector (Euclid P) (m + 1)) (b D : Euclid P → ℝ) (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)) (K : ℝ), W ⊆ U → T.massOn W ≠ ∞ → T.boundary.massOn W ≠ ∞ → (∀ ω : TestFormOn U (m + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μ) → (∀ (k : ℕ) (S : GeometricCurrentOn U k) (ω : TestFormOn U k) (r : ℝ), S.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) k) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ r) → |S ω| ≤ r * (S.massOn W).toReal) → tsupport b ⊆ W → IsTestForm η → IsTestForm ζ → tsupport η ⊆ tsupport b → tsupport ζ ⊆ tsupport b → (∀ x, covectorEuclideanNorm (η x) ≤ K) → (∀ x, covectorEuclideanNorm (ζ x) ≤ K) → (∀ x, exteriorDerivative η x = (b x * D x) • θ + ζ x) → |∫ x, b x * ξ x θ * D x ∂(μ.restrict W)| ≤ K * ((T.boundary.massOn W).toReal + (T.massOn W).toReal) := by
  intro P m U W T μ ξ θ b D η ζ K hWU hT hbT hrep hEB hb hη hζ hηb hζb hηK hζK hd
  -- `η`, `ζ` are test forms in `U`, supported in `spt b ⊆ W`
  have hηW : tsupport η ⊆ W := hηb.trans hb
  have hζW : tsupport ζ ⊆ W := hζb.trans hb
  let η' : TestFormOn U m := ⟨η, hη, hηW.trans hWU⟩
  let ζ' : TestFormOn U (m + 1) := ⟨ζ, hζ, hζW.trans hWU⟩
  -- `ω = dη − ζ` has `ω(x) = b(x) D(x) θ`
  have hω : ∀ x, ((exteriorDerivativeTestOn U m η' - ζ' : TestFormOn U (m + 1)) :
      DifferentialForm (Euclid P) (m + 1)) x = (b x * D x) • θ := by
    intro x
    change exteriorDerivative η x - ζ x = _
    rw [hd x, add_sub_cancel_right]
  -- `T(ω) = ∂T(η) − T(ζ)`, and the evaluation bound controls both terms
  have hTω : T (exteriorDerivativeTestOn U m η' - ζ') = T.boundary η' - T ζ' := by
    rw [GeometricCurrentOn.boundary_apply]
    exact map_sub T.toCurrent _ _
  have h1 : |T.boundary η'| ≤ K * (T.boundary.massOn W).toReal :=
    hEB m T.boundary η' K hbT hηW hηK
  have h2 : |T ζ'| ≤ K * (T.massOn W).toReal := hEB (m + 1) T ζ' K hT hζW hζK
  -- `b = 0` off `W`, so the integral over `W` is `T(ω)`
  have hint : ∫ x, b x * ξ x θ * D x ∂(μ.restrict W) =
      T (exteriorDerivativeTestOn U m η' - ζ') := by
    rw [hrep, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1
      funext x
      rw [hω x, map_smul, smul_eq_mul]
      ring
    · intro x hx
      have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hb h)
      rw [hbx, zero_mul, zero_mul]
  rw [hint, hTω, mul_add]
  exact (abs_sub _ _).trans (add_le_add h1 h2)
/-- Localization of the null-set argument (steps 5 and 6 of the null-set step of the mass
representation used for Simon 7.2.4): let `W ⊆ ℝᴾ` be open with `μ(W) < ∞`, `f` `μ`-a.e. strongly
measurable with `|f| ≤ c`, `q : ℝᴾ → ℝⁿ` measurable and `N ⊆ ℝⁿ` measurable.  Assume (TD): for a
finite `ν` and `ν`-integrable `h`, a bound `|∫ h · div g(q) dν| ≤ Λ` over all smooth compactly
supported `g` with `‖g‖ ≤ 1` forces `∫_{q⁻¹(N)} h dν = 0`; and (DB): for every smooth `b` compactly
supported in `W` such a bound holds for `h = b f` and `ν = μ⌞W`.  Then `f = 0` `μ`-a.e. on
`W ∩ q⁻¹(N)`.  The function `F := 1_{q⁻¹(N)} f` is bounded, hence locally integrable on `W`;
since `b` vanishes off `W`, (DB) and (TD) give `∫ b F dμ = ∫_{q⁻¹(N)} b f d(μ⌞W) = 0` for every
such `b`, and `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` gives `F = 0` `μ`-a.e. on
`W`. -/
theorem Submission.cmr_ae_zero_of_div_bounds : ∀ (P n : ℕ) (W : Set (Euclid P)) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (q : Euclid P → Euclid n) (N : Set (Euclid n)) (c : ℝ), IsOpen W → μ W < ∞ → AEStronglyMeasurable f μ → (∀ x, |f x| ≤ c) → Measurable q → MeasurableSet N → (∀ (ν : Measure (Euclid P)) (h : Euclid P → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∫ x in q ⁻¹' N, h x ∂ν = 0) → (∀ b : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → tsupport b ⊆ W → ∃ Λ : ℝ, ∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, b x * f x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂(μ.restrict W)| ≤ Λ) → ∀ᵐ x ∂μ, x ∈ W → q x ∈ N → f x = 0 := by
  intro P n W μ f q N c hW hμW hf hfc hq hN hTD hDB
  -- Step 1: `A := q⁻¹(N)` is measurable, `μ⌞W` is finite, `c ≥ 0`
  have hA : MeasurableSet (q ⁻¹' N) := hq hN
  have : IsFiniteMeasure (μ.restrict W) := isFiniteMeasure_restrict.2 hμW.ne
  have hc : 0 ≤ c := (abs_nonneg _).trans (hfc 0)
  -- Step 2: `F := 1_A f` is bounded by `c`, hence locally integrable on `W`
  have hFb : ∀ x, ‖(q ⁻¹' N).indicator f x‖ ≤ c := by
    intro x
    by_cases hx : x ∈ q ⁻¹' N
    · rw [indicator_of_mem hx, Real.norm_eq_abs]
      exact hfc x
    · rw [indicator_of_notMem hx, norm_zero]
      exact hc
  have hFloc : LocallyIntegrableOn ((q ⁻¹' N).indicator f) W μ :=
    IntegrableOn.locallyIntegrableOn
      (Integrable.of_bound (hf.indicator hA).restrict c (Eventually.of_forall hFb))
  -- Step 4: localization, once the integrals of step 3 vanish
  have hF0 : ∀ᵐ x ∂μ, x ∈ W → (q ⁻¹' N).indicator f x = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hFloc ?_
    -- Step 3: `∫ b • F dμ = 0` for smooth `b` compactly supported in `W`
    intro b hb hbc hbW
    -- (a) `h := b f` is `μ⌞W`-integrable
    obtain ⟨B, hB⟩ := hb.continuous.bounded_above_of_compact_support hbc
    have hh : Integrable (fun x => b x * f x) (μ.restrict W) := by
      refine Integrable.of_bound (hb.continuous.aestronglyMeasurable.mul hf.restrict) (B * c)
        (Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_eq_abs (f x)]
      exact mul_le_mul (hB x) (hfc x) (abs_nonneg _) ((norm_nonneg _).trans (hB x))
    -- (b) (DB) and (TD) give `∫_A b f d(μ⌞W) = 0`
    obtain ⟨Λ, hΛ⟩ := hDB b hb hbc hbW
    have h0 : ∫ x in q ⁻¹' N, b x * f x ∂(μ.restrict W) = 0 :=
      hTD (μ.restrict W) (fun x => b x * f x) Λ inferInstance hh hΛ
    -- (c) `b` vanishes off `W`, so `∫ b • F dμ = ∫ b • F d(μ⌞W)`
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := W) fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport fun hx' => hx (hbW hx'), zero_smul]]
    -- (d) `b • F = 1_A (b f)`, and (e) conclude
    have hbF : (fun x => b x • (q ⁻¹' N).indicator f x) =
        (q ⁻¹' N).indicator fun x => b x * f x := by
      funext x
      by_cases hx : x ∈ q ⁻¹' N
      · rw [indicator_of_mem hx, indicator_of_mem hx, smul_eq_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]
    rw [hbF, integral_indicator hA]
    exact h0
  -- Step 5: on `W ∩ q⁻¹(N)`, `f = F = 0`
  filter_upwards [hF0] with x hx hxW hxN
  rw [← indicator_of_mem (show x ∈ q ⁻¹' N from hxN) f]
  exact hx hxW
/-- **The mass measure vanishes where the orientation vanishes** (parent step 8 of the
representation `T = μ_T ∧ ξ⃗`).  Let `W ⊇ C` be measurable with `μ(W) < ∞` and `M_W(T) = μ(W)`,
let `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x` and all covectors `α` (`|·|_E` is
`covectorEuclideanNorm`), and let `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` for every test form `ω`.  If
`ξ = 0` `μ`-a.e. on `C`, then `μ(C) = 0`.  Fix an admissible `ω`, i.e. `tsupport ω ⊆ W` and
`|ω|_E ≤ 1`, and let `f(x) = ⟨ω(x), ξ(x)⟩`.  For `μ`-a.e. `x`, `|f(x)| ≤ 1_{W \ C}(x)`: `f = 0`
on `C` (where `ξ = 0`) and off `W` (where `ω = 0`), and `|f| ≤ |ω|_E ≤ 1` on `W \ C`.  Hence
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_{W \ C} dμ = μ(W \ C)`, whether or not `f` is integrable.
Taking the supremum gives `μ(W) = M_W(T) ≤ μ(W \ C)`, and `μ(W \ C) + μ(C) = μ(W)` with
`μ(W \ C) < ∞` forces `μ(C) = 0`. -/
theorem Submission.cmr_measure_null_of_orient_ae_zero : ∀ (P n : ℕ) (U W C : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), MeasurableSet W → MeasurableSet C → C ⊆ W → μ W < ∞ → T.massOn W = μ W → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → (∀ᵐ x ∂μ, x ∈ C → ξ x = 0) → μ C = 0 := by
  intro P n U W C T μ ξ hW hC hCW hμW hmass hξ hT hzero
  -- Step 1: `M_W(T) ≤ μ(W \ C)`; it suffices to bound `ofReal (T ω)` for each admissible `ω`
  have hle : T.massOn W ≤ μ (W \ C) := by
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    -- `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_{W \ C}(x)` for `μ`-a.e. `x`
    have hpt : ∀ᵐ x ∂μ,
        ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ (W \ C).indicator 1 x := by
      filter_upwards [hzero] with x hx
      by_cases hxC : x ∈ C
      · rw [hx hxC, zero_apply, enorm_zero]
        exact zero_le
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem (show x ∈ W \ C from ⟨hxW, hxC⟩), Pi.one_apply,
          Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
      · rw [image_eq_zero_of_notMem_tsupport fun h => hxW (hω.1 h), map_zero, enorm_zero]
        exact zero_le
    calc ENNReal.ofReal (T ω)
        = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
      _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, (W \ C).indicator 1 x ∂μ := lintegral_mono_ae hpt
      _ = μ (W \ C) := lintegral_indicator_one (hW.diff hC)
  -- Step 2: cancel the finite `μ(W \ C)` in `μ(W \ C) + μ(C) = μ(W) ≤ μ(W \ C) + 0`
  have hsplit : μ (W \ C) + μ C = μ W := by
    simpa only [inter_eq_right.mpr hCW] using measure_sdiff_add_inter (μ := μ) W hC
  have hfin : μ (W \ C) ≠ ∞ := ((measure_mono Set.sdiff_subset).trans_lt hμW).ne
  refine nonpos_iff_eq_zero.mp ((ENNReal.add_le_add_iff_left hfin).mp ?_)
  rw [hsplit, add_zero, ← hmass]
  exact hle
/-- Null sets from compact null sets (last step of the proof that the mass measure `μ_T` of a
locally normal current vanishes on `Hⁿ`-null sets, Simon 6.2.36, used for 7.2.4): let `U ⊆ ℝᴾ` be
open and `μ`, `ν` measures on `ℝᴾ` with `μ(ℝᴾ \ U) = 0`, `μ(K) < ∞` for compact `K ⊆ U`, and
`μ(C) = 0` for every compact `C ⊆ U` with `ν(C) = 0`.  Then every `ν`-null set is `μ`-null.
Take a measurable `ν`-null hull `E' ⊇ E` and exhaust `U` by the compact sets `Fᵢ ∩ B̄ⱼ(0)`,
`Fᵢ ⊆ U` closed.  Each `μ⌞(Fᵢ ∩ B̄ⱼ(0))` is finite, hence inner regular, so `μ(E' ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`
would give a compact `C ⊆ E'` with `μ(C ∩ Fᵢ ∩ B̄ⱼ(0)) > 0`, contradicting the hypothesis. -/
theorem Submission.cmr_null_of_compact_null : ∀ (P : ℕ) (U : Set (Euclid P)) (μ ν : Measure (Euclid P)), IsOpen U → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ν C = 0 → μ C = 0) → ∀ E : Set (Euclid P), ν E = 0 → μ E = 0 := by
  intro P U μ ν hU hUc hfin hnull E hE
  -- Step 1: a measurable `ν`-null hull `E' ⊇ E`
  obtain ⟨E', hEE', hE'm, hE'⟩ := exists_measurable_superset_of_null hE
  -- Step 2: `U = ⋃ₚ Kₚ` with `K_{(i,j)} = Fᵢ ∩ B̄ⱼ(0)` compact, `Fᵢ ⊆ U` closed
  obtain ⟨F, hFc, hFU, hFun, -⟩ := hU.exists_iUnion_isClosed
  have hK : ∀ p : ℕ × ℕ, IsCompact (F p.1 ∩ closedBall (0 : Euclid P) p.2) := fun p =>
    (isCompact_closedBall _ _).inter_left (hFc p.1)
  have hKU : ∀ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 ⊆ U := fun p =>
    inter_subset_left.trans (hFU p.1)
  have hcover : U ⊆ ⋃ p : ℕ × ℕ, F p.1 ∩ closedBall (0 : Euclid P) p.2 := by
    intro x hx
    rw [← hFun] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := exists_nat_ge (dist x 0)
    exact mem_iUnion.2 ⟨(i, j), hi, mem_closedBall.2 hj⟩
  -- Step 3: `μ(E' ∩ Kₚ) = 0` for every `p`, by inner regularity of the finite `μ⌞Kₚ`
  have hpiece : ∀ p : ℕ × ℕ, μ (E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) = 0 := by
    intro p
    set K := F p.1 ∩ closedBall (0 : Euclid P) p.2
    have : IsFiniteMeasure (μ.restrict K) :=
      isFiniteMeasure_restrict.2 (hfin K (hK p) (hKU p)).ne
    by_contra hne
    have hpos : 0 < μ.restrict K E' := by
      rw [Measure.restrict_apply hE'm]
      exact pos_iff_ne_zero.2 hne
    obtain ⟨C, hCE', hCc, hCpos⟩ := hE'm.exists_lt_isCompact_of_ne_top (measure_ne_top _ _) hpos
    rw [Measure.restrict_apply hCc.isClosed.measurableSet] at hCpos
    have hC0 : μ (C ∩ K) = 0 :=
      hnull (C ∩ K) (hCc.inter_right (hK p).isClosed) (inter_subset_right.trans (hKU p))
        (measure_mono_null (inter_subset_left.trans hCE') hE')
    exact hCpos.ne' hC0
  -- Step 4: `E ⊆ E' ⊆ Uᶜ ∪ ⋃ₚ (E' ∩ Kₚ)`, a `μ`-null set
  refine measure_mono_null hEE' (measure_mono_null (t := Uᶜ ∪
    ⋃ p : ℕ × ℕ, E' ∩ (F p.1 ∩ closedBall (0 : Euclid P) p.2)) ?_
    (measure_union_null hUc (measure_iUnion_null hpiece)))
  intro x hx
  by_cases hxU : x ∈ U
  · obtain ⟨p, hp⟩ := mem_iUnion.1 (hcover hxU)
    exact Or.inr (mem_iUnion.2 ⟨p, hx, hp⟩)
  · exact Or.inl hxU
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))
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
/-- **Jacobi's trace identity for column replacement** (parent fact (F3) of the divergence form
of the mass representation).  Let `M = (u j k)_{k,j}` be the matrix with columns `u j`.
Replacing column `i` by `A (u i)` and summing the determinants over `i` gives `tr(A) · det M`.
With `B` the matrix of `A` in the standard basis `e` of `ℝⁿ`, column `i` of `B M` is `A (u i)`,
so by Cramer's rule the `i`-th determinant is `(adj M · B M)_{i,i}`; then
`tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr B = det M · tr A`. -/
theorem Submission.cmr_df_det_update_sum_trace : ∀ (n : ℕ) (A : Euclid n →ₗ[ℝ] Euclid n) (u : Fin n → Euclid n), ∑ i : Fin n, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) = LinearMap.trace ℝ (Euclid n) A * Matrix.det (Matrix.of fun k j => u j k) := by
  intro n A u
  -- the standard basis `e` of `ℝⁿ`, the matrix `M` with columns `u j`, the matrix `B` of `A`
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun k j => u j k
  let B := LinearMap.toMatrix e e A
  -- Step 1: `A (u i) k = (B M)_{k,i}`, from `B *ᵥ e.repr x = e.repr (A x)` and `e.repr x = x`
  have hA : ∀ i k, A (u i) k = (B * M) k i := by
    intro i k
    have := congrFun (LinearMap.toMatrix_mulVec_repr e e A (u i)) k
    simpa [Matrix.mulVec, Matrix.mul_apply, dotProduct, e, B, M] using this.symm
  -- Step 2: the `i`-th summand is `det (M.updateCol i (B M)_{·,i}) = (adj M · B M)_{i,i}` (Cramer)
  have hcol : ∀ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
      (M.adjugate * (B * M)) i i := by
    intro i
    have h1 : (Matrix.of fun k j => Function.update u i (A (u i)) j k) =
        M.updateCol i (fun k => (B * M) k i) := by
      ext k j
      by_cases hj : j = i
      · subst hj
        simp [hA]
      · simp [hj, M]
    rw [h1, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  -- Step 3: `tr(adj M · B M) = tr(B · M adj M) = tr(B · (det M • 1)) = det M · tr A`
  calc ∑ i, Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k)
      = Matrix.trace (M.adjugate * (B * M)) := by
        simp only [hcol, Matrix.trace, Matrix.diag_apply]
    _ = Matrix.trace (B * (M * M.adjugate)) := by
        rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = LinearMap.trace ℝ (Euclid n) A * M.det := by
        rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul,
          LinearMap.trace_eq_matrix_trace ℝ e A, mul_comm]

/-- **Coordinate form of `Σᵢ (-1)ⁱ θ(L wᵢ, w₀, …, ŵᵢ, …, w_m) = tr(A) θ(w)`** (the trace step of
the divergence-form computation behind the mass representation in Simon 7.2.4).  Let `θ` be the
`(m+1)`-covector `θ(v) = det (v j (I k))_{k,j}` on `ℝᴾ`, let `A` be linear on `ℝ^{m+1}`, and let
`L : ℝᴾ → ℝᴾ` satisfy `(L v)(I k) = (A (p v))_k` with `p v = (v (I k))_k`.  Moving `L wᵢ` from
the front to slot `i` costs `(-1)ⁱ`, so the `i`-th term is `θ(w)` with `wᵢ` replaced by `L wᵢ`.
In the coordinates `uⱼ = p wⱼ` it is the determinant of `u` with its `i`-th column replaced by
`A uᵢ`.  Jacobi's identity `Submission.cmr_df_det_update_sum_trace` sums these determinants to
`tr(A) det u`, and `det u = θ(w)`. -/
theorem Submission.cmr_df_cons_sum_trace : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (L : Euclid P → Euclid P), (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → (∀ (v : Euclid P) (k : Fin (m + 1)), L v (I k) = A (WithLp.toLp 2 (fun k' => v (I k'))) k) → ∀ w : Fin (m + 1) → Euclid P, ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons (L (w i)) (i.removeNth w)) = LinearMap.trace ℝ (Euclid (m + 1)) A * θ w := by
  intro P m I θ A L hθ hL w
  -- Step 1: sign rule, `(-1)ⁱ θ(x, w₀, …, ŵᵢ, …, w_m) = θ(w with wᵢ replaced by x)`
  have h1 : ∀ (i : Fin (m + 1)) (x : Euclid P),
      (-1 : ℝ) ^ (i : ℕ) * θ (Fin.cons x (i.removeNth w)) = θ (Function.update w i x) := by
    intro i x
    rw [← Fin.insertNth_removeNth, ContinuousAlternatingMap.map_insertNth, zsmul_eq_mul]
    push_cast
    rfl
  -- the coordinate columns `uⱼ = p wⱼ ∈ ℝ^{m+1}`
  let u : Fin (m + 1) → Euclid (m + 1) := fun j => WithLp.toLp 2 (fun k => w j (I k))
  -- Step 2: the `i`-th term is `det u` with its `i`-th column replaced by `A uᵢ`, entrywise
  have h2 : ∀ i : Fin (m + 1), θ (Function.update w i (L (w i))) =
      Matrix.det (Matrix.of fun k j => Function.update u i (A (u i)) j k) := by
    intro i
    rw [hθ]
    congr 1
    ext k j
    rcases eq_or_ne j i with rfl | hj
    · simp [hL, u]
    · simp [Function.update_of_ne hj, u]
  -- Step 4: `det u = θ(w)`
  have h4 : Matrix.det (Matrix.of fun k j => u j k) = θ w := (hθ w).symm
  -- Step 3: Jacobi's identity
  simp_rw [h1, h2]
  rw [Submission.cmr_df_det_update_sum_trace (m + 1) A u, h4]
/-- **Exterior derivative of a function times a contracted covector** (used for the divergence
form in the mass-representation step of Simon 7.2.4).  If `b : ℝᴾ → ℝ` and `G : ℝᴾ → ℝᴾ` are
differentiable at `x` and `θ` is a fixed `(m+1)`-covector, then `η(y) = b(y) θ(G(y), ·)` has
`dη(x)(w₀, …, w_m) = Σᵢ (−1)ⁱ (Db(x)wᵢ · θ(G(x), ŵᵢ) + b(x) · θ(DG(x)wᵢ, ŵᵢ))`, where `ŵᵢ` is
`(w₀, …, w_m)` with `wᵢ` removed: each term of the alternating sum differentiates
`y ↦ b(y) θ(G(y), ŵᵢ)` by the product and chain rules. -/
theorem Submission.cmr_df_extDeriv_smul_curryLeft : ∀ (P m : ℕ) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ) (G : Euclid P → Euclid P) (x : Euclid P), DifferentiableAt ℝ b x → DifferentiableAt ℝ G x → ∀ w : Fin (m + 1) → Euclid P, exteriorDerivative (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x w = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w))) := by
  intro P m θ b G x hb hG w
  have hc : DifferentiableAt ℝ (fun y => ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    (ContinuousAlternatingMap.curryLeft θ).differentiableAt.comp x hG
  have hη : DifferentiableAt ℝ (fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y)) x :=
    hb.smul hc
  rw [exteriorDerivative_apply hη w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_continuousAlternatingMap_apply_const_apply hη, fderiv_fun_smul hb hc,
    fderiv_fun_comp x (ContinuousAlternatingMap.curryLeft θ).differentiableAt hG,
    ContinuousLinearMap.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply,
    smul_eq_mul, zsmul_eq_mul]
  simp only [Matrix.vecCons]
  push_cast
  ring
/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]
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
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Radial retraction onto the unit ball of `N = covectorEuclideanNorm`** (step 4 of the
approximation of a unit covector field by admissible test forms, used for Simon Ch. 6,
Remark 3.2(3)).  `ρ(a) = max(1, N(a))⁻¹ a` is continuous, `ρ(0) = 0`, `N(ρ(a)) ≤ 1`, and
`N(ρ(a) − b) ≤ 2 N(a − b)` whenever `N(b) ≤ 1`: if `N(a) > 1` then
`N(a − ρ(a)) = N(a) − 1 ≤ N(a − b)`, and the triangle inequality gives the factor `2`. -/
theorem Submission.rsd_mw_tfa_retraction : ∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b) := by
  intro P n
  obtain ⟨htri, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- the rescaling factor `max 1 (N a) ≥ 1` never vanishes
  have hpos : ∀ a : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm a) :=
    fun a => one_pos.trans_le (le_max_left _ _)
  refine ⟨fun a => (max 1 (covectorEuclideanNorm a))⁻¹ • a,
    ((continuous_const.max hcont).inv₀ fun a => (hpos a).ne').smul continuous_id, by simp,
    fun a => ?_, fun a b hb => ?_⟩
  · -- `N (ρ a) = N a / max 1 (N a) ≤ 1`
    dsimp only
    rw [hsmul, abs_of_pos (inv_pos.mpr (hpos a)), inv_mul_le_iff₀ (hpos a), mul_one]
    exact le_max_right _ _
  dsimp only
  rcases le_or_gt (covectorEuclideanNorm a) 1 with ha | ha
  · -- `N a ≤ 1`: `ρ a = a`
    rw [max_eq_left ha, inv_one, one_smul]
    linarith [covectorEuclideanNorm_nonneg (a - b)]
  -- `r := N a > 1`: `ρ a = r⁻¹ a`
  set r := covectorEuclideanNorm a with hr
  rw [max_eq_right ha.le]
  -- `N (a - ρ a) = (1 - r⁻¹) r = r - 1`
  have h₁ : covectorEuclideanNorm (a - r⁻¹ • a) = r - 1 := by
    rw [show a - r⁻¹ • a = (1 - r⁻¹) • a by module, hsmul,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ ha.le)), sub_mul, one_mul, ← hr,
      inv_mul_cancel₀ (one_pos.trans ha).ne']
  -- `r ≤ N (a - b) + N b ≤ N (a - b) + 1`
  have h₂ : r ≤ covectorEuclideanNorm (a - b) + 1 :=
    calc r = covectorEuclideanNorm (a - b + b) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (a - b) + covectorEuclideanNorm b := htri _ _
      _ ≤ covectorEuclideanNorm (a - b) + 1 := by linarith
  calc covectorEuclideanNorm (r⁻¹ • a - b)
      = covectorEuclideanNorm (-(a - r⁻¹ • a) + (a - b)) := by congr 1; abel
    _ ≤ covectorEuclideanNorm (-(a - r⁻¹ • a)) + covectorEuclideanNorm (a - b) := htri _ _
    _ = r - 1 + covectorEuclideanNorm (a - b) := by rw [covectorEuclideanNorm_neg, h₁]
    _ ≤ 2 * covectorEuclideanNorm (a - b) := by linarith

/-- **`L¹(ν)` approximation of a unit covector field by continuous compactly supported unit
fields** (steps 3–4 of the `L¹(ν)` approximation of a unit covector field by admissible test
forms).  Let `ν` be a finite Borel measure on `ℝᴾ` and `β` a `ν`-integrable `n`-covector field
with `N(β) ≤ 1` `ν`-a.e., `N = covectorEuclideanNorm`.  Continuous compactly supported maps are
dense in `L¹(ν)` (`ν` is regular), so one of them, `g₀`, has `∫ ‖β − g₀‖ dν ≤ η`.  With `ρ` the
retraction onto `{N ≤ 1}`, `g = ρ ∘ g₀` is continuous, compactly supported (`ρ 0 = 0`), has
`N(g) ≤ 1`, and `N(g − β) ≤ 2 N(g₀ − β) ≤ 2C ‖β − g₀‖` a.e., so `∫ N(g − β) dν ≤ 2Cη < δ`. -/
theorem Submission.rsd_mw_tfa_continuous_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g x - β x)) ∂ν < ENNReal.ofReal δ := by
  intro P n ν β hν hβ hβ1 δ hδ
  -- Step 1: the constant `C` of `norm_props` (iii), the retraction `ρ`, and the tolerance `η`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨ρ, hρc, hρ0, hρ1, hρ2⟩ := Submission.rsd_mw_tfa_retraction P n
  set η : ℝ := δ / (2 * (2 * C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: continuous compactly supported maps are dense in `L¹(ν)` (`ν` is finite, hence
  -- regular).  The contract does not import `Integrable.exists_hasCompactSupport_lintegral_sub_le`,
  -- so this goes through `MemLp.induction_dense`: `c • 1_s` is approximated by `φ • c`, with `φ`
  -- a Urysohn function for compact `K ⊆ s ⊆ U` open, `ν (U \ K)` small.
  have hind : ∀ (c : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : Euclid P → Covector (Euclid P) n,
        eLpNorm (g - s.indicator fun _ => c) 1 ν ≤ ε ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro c s hs hsν ε hε
    obtain ⟨t, ht0, htε⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hε
    have ht : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht0.ne'
    -- compact `K ⊆ s ⊆ U` open with `ν (s \ K) < t` and `ν (U \ s) < t`
    obtain ⟨K, hKs, hK, hsK⟩ := hs.exists_isCompact_sdiff_lt hsν.ne ht
    obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hsν.ne ht
    -- Urysohn: `φ = 1` on `K`, `φ = 0` off `U`, `0 ≤ φ ≤ 1`, compact support
    obtain ⟨φ, hφK, hφU, hφs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hgc : Continuous fun x => φ x • c := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • c, ?_, hgc, hφs.smul_right⟩
    -- pointwise `‖φ x • c - 1_s(x) c‖ₑ ≤ 1_{U \ K}(x) ‖c‖ₑ`
    have hle : ∀ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ≤
        (U \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      rw [← ofReal_norm]
      by_cases hxK : x ∈ K
      · simp [hφK hxK, hKs hxK]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxK), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [Pi.sub_apply, indicator_of_mem hxs, show φ x • c - c = (φ x - 1) • c by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          nlinarith [norm_nonneg c]
        · rw [Pi.sub_apply, indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg h0]
          nlinarith [norm_nonneg c]
      · simp [hφU hxU, show x ∉ s from fun h => hxU (hsU h), hxU]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (stronglyMeasurable_const.indicator hs).aestronglyMeasurable)]
    calc ∫⁻ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ∂ν
        ≤ ∫⁻ x, (U \ K).indicator (fun _ => ‖c‖ₑ) x ∂ν := lintegral_mono hle
      _ = ‖c‖ₑ * ν (U \ K) := lintegral_indicator_const (hU.measurableSet.diff hK.measurableSet) _
      _ ≤ ‖c‖ₑ * (ν (U \ s) + ν (s \ K)) := by
          gcongr
          refine (measure_mono fun x hx => ?_).trans (measure_union_le (U \ s) (s \ K))
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩
      _ ≤ ‖c‖ₑ * (t + t) := by gcongr
      _ = t * (2 * ‖c‖ₑ) := by ring
      _ ≤ ε := htε.le
  -- the density statement for `β`, with tolerance `η`
  obtain ⟨g₀, hg₀, hg₀c, hg₀s⟩ := (memLp_one_iff_integrable.2 hβ).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.mpr hη0).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hβ.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)] at hg₀
  -- Step 3: `g := ρ ∘ g₀`
  refine ⟨ρ ∘ g₀, hρc.comp hg₀c, hg₀s.comp_left hρ0, fun x => hρ1 _, ?_⟩
  -- Step 4: pointwise a.e. estimate
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x))
      ≤ ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ := by
    filter_upwards [hβ1] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc covectorEuclideanNorm ((ρ ∘ g₀) x - β x)
        ≤ 2 * covectorEuclideanNorm (g₀ x - β x) := hρ2 _ _ hx
      _ ≤ 2 * (C * ‖g₀ x - β x‖) := by gcongr; exact hC _
      _ = 2 * C * ‖β x - g₀ x‖ := by rw [norm_sub_rev]; ring
  -- Step 5: integration
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * C) * ∫⁻ x, ‖β x - g₀ x‖ₑ ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * C) * ENNReal.ofReal η := by gcongr; exact hg₀
    _ = ENNReal.ofReal (2 * C * η) := (ENNReal.ofReal_mul (by positivity)).symm
    -- Step 6: arithmetic
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ, hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smooth uniform approximation keeping the unit bound** (smoothing step in the proof of
`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is `covectorEuclideanNorm`).  Let
`η := δ/(2C + 1)`, where `|·|_E ≤ C‖·‖` (`Submission.rsd_mw_tfa_norm_props`).  A continuous
compactly supported covector field `g` with `|g|_E ≤ 1` is uniformly continuous, so
`‖g y − g x‖ < η` when `dist y x < r`.  Mollifying, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth
bump `φ ≥ 0` with `support φ = B_r(0)` is a `C^∞` field with `‖h' − g‖ ≤ η`; then
`|h' − g|_E ≤ Cη` and `|h'|_E ≤ 1 + Cη`.  The rescaled field `h = (1 + Cη)⁻¹h'` has `|h|_E ≤ 1`
and `|h − h'|_E = Cη(1 + Cη)⁻¹|h'|_E ≤ Cη`, hence `|h − g|_E ≤ 2Cη ≤ δ`. -/
theorem Submission.rsd_mw_tfa_smooth_uniform_approx : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n), Continuous g → HasCompactSupport g → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ h : Euclid P → Covector (Euclid P) n, ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ x, covectorEuclideanNorm (h x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (h x - g x) ≤ δ := by
  intro P n g hgc hgs hg1 δ hδ
  -- `N := covectorEuclideanNorm` is subadditive, absolutely homogeneous and `N ≤ C ‖·‖`
  obtain ⟨htri, hsmul, ⟨C, hC0, hCle⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: the tolerance `η = δ / (2C + 1)`
  set η : ℝ := δ / (2 * C + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hCη : 0 ≤ C * η := mul_nonneg hC0 hη0.le
  -- Step 2: `g` is uniformly continuous: `‖g y - g x‖ < η` whenever `dist y x < r`
  obtain ⟨r, hr, hgr⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη0
  -- Step 3: mollify, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ`, `support φ = B_r(0)`
  let φ : ContDiffBump (0 : Euclid P) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hr
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 r := hψφ.trans φ.support_eq.subset
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  obtain ⟨h', hh's, hh'g⟩ : ∃ h' : Euclid P → Covector (Euclid P) n,
      ContDiff ℝ (⊤ : ℕ∞) h' ∧ ∀ x, dist (h' x) (g x) ≤ η :=
    ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      (φ.hasCompactSupport.mono hψφ).contDiff_convolution_left _ (φ.contDiff.div_const _)
        hgc.locallyIntegrable,
      fun x => dist_convolution_le hη0.le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgr (mem_ball.mp hy)).le⟩
  -- Step 4: `N(h' - g) ≤ Cη` and `N(h') ≤ 1 + Cη`
  have hdiff : ∀ x, covectorEuclideanNorm (h' x - g x) ≤ C * η := fun x =>
    (hCle _).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hh'g x) hC0)
  have hh'1 : ∀ x, covectorEuclideanNorm (h' x) ≤ 1 + C * η := fun x =>
    calc covectorEuclideanNorm (h' x) = covectorEuclideanNorm ((h' x - g x) + g x) := by
          rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (h' x - g x) + covectorEuclideanNorm (g x) := htri _ _
      _ ≤ C * η + 1 := add_le_add (hdiff x) (hg1 x)
      _ = 1 + C * η := add_comm _ _
  -- Step 5: rescale by `s = (1 + Cη)⁻¹ ∈ (0, 1]`
  have hpos : 0 < 1 + C * η := by linarith
  have hne : 1 + C * η ≠ 0 := hpos.ne'
  set s : ℝ := (1 + C * η)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hpos
  refine ⟨fun x => s • h' x, hh's.const_smul s, fun x => ?_, fun x => ?_⟩
  · show covectorEuclideanNorm (s • h' x) ≤ 1
    rw [hsmul, abs_of_pos hs0, hs, inv_mul_le_iff₀ hpos, mul_one]
    exact hh'1 x
  · show covectorEuclideanNorm (s • h' x - g x) ≤ δ
    -- Step 6: `N(s h' - h') = |s - 1| N(h') = Cη s N(h') ≤ Cη`
    have hsh : s • h' x - h' x = (s - 1) • h' x := by module
    have hs1 : |s - 1| = C * η * s := by
      have hle : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      rw [abs_of_nonpos (by linarith), hs]
      field_simp
      ring
    have h6 : covectorEuclideanNorm (s • h' x - h' x) ≤ C * η := by
      rw [hsh, hsmul, hs1]
      calc C * η * s * covectorEuclideanNorm (h' x) ≤ C * η * s * (1 + C * η) :=
            mul_le_mul_of_nonneg_left (hh'1 x) (mul_nonneg hCη hs0.le)
        _ = C * η := by rw [hs]; field_simp
    -- Step 7: `N(s h' - g) ≤ N(s h' - h') + N(h' - g) ≤ 2Cη ≤ δ`
    calc covectorEuclideanNorm (s • h' x - g x)
        = covectorEuclideanNorm ((s • h' x - h' x) + (h' x - g x)) := by
          rw [sub_add_sub_cancel]
      _ ≤ covectorEuclideanNorm (s • h' x - h' x) + covectorEuclideanNorm (h' x - g x) :=
          htri _ _
      _ ≤ C * η + C * η := add_le_add h6 (hdiff x)
      _ ≤ δ := by
          have h2 : 0 < 2 * C + 1 := by linarith
          have h2C : C * η + C * η = 2 * C * δ / (2 * C + 1) := by rw [hη]; ring
          rw [h2C, div_le_iff₀ h2]
          nlinarith
/-- **Test forms approximating a unit-bounded integrable covector field in `L¹(ν)`** (the
approximation behind `M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is
`covectorEuclideanNorm`).  Let `m = ν(ℝᴾ)` and `δ = ε/(4(m + 1))`.  The smooth cut-off `χ` of
`Submission.rsd_mw_tfa_smooth_cutoff` satisfies `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`.  The
continuous field `g₁` of `Submission.rsd_mw_tfa_continuous_approx` satisfies `|g₁|_E ≤ 1` and
`∫ |g₁ − β|_E dν < ε/4`.  Its smoothing `g₂` (`Submission.rsd_mw_tfa_smooth_uniform_approx`)
satisfies `|g₂|_E ≤ 1` and `|g₂ − g₁|_E ≤ δ`.  Then `ω = χ g₂` is a test form, `tsupport ω ⊆ V`
and `|ω|_E ≤ 1`.  For a.e. `x`, `|ω − β|_E ≤ δ + |g₁ − β|_E` where `χ = 1`, and
`|ω − β|_E ≤ 2` where `χ ≠ 1`.  Integrating,
`∫ |ω − β|_E dν ≤ δm + ∫ |g₁ − β|_E dν + 2ν{χ ≠ 1} < ε/4 + ε/4 + ε/4 < ε`. -/
theorem Submission.rsd_mw_exists_testForm_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ ε : ℝ, 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν V β hν hV hVc hβ hβ1 ε hε
  -- `N := covectorEuclideanNorm` is subadditive and absolutely homogeneous
  obtain ⟨htri, hsmul, -, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: a smooth cut-off `χ` with `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`
  obtain ⟨χ, hχs, hχc, hχV, hχ01, hχν⟩ :=
    Submission.rsd_mw_tfa_smooth_cutoff P ν V hν hV hVc (ε / 8) (by positivity)
  -- Step 2: a continuous compactly supported `g₁` with `N(g₁) ≤ 1` and `∫ N(g₁ - β) dν < ε/4`
  obtain ⟨g₁, hg₁c, hg₁s, hg₁1, hg₁β⟩ :=
    Submission.rsd_mw_tfa_continuous_approx P n ν β hν hβ hβ1 (ε / 4) (by positivity)
  -- Step 3: a smooth `g₂` with `N(g₂) ≤ 1` and `N(g₂ - g₁) ≤ δ = ε/(4(m + 1))`, `m = ν(ℝᴾ)`
  set m : ℝ := (ν univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (4 * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g₂, hg₂s, hg₂1, hg₂g₁⟩ :=
    Submission.rsd_mw_tfa_smooth_uniform_approx P n g₁ hg₁c hg₁s hg₁1 δ hδ0
  -- Step 4: `ω = χ g₂` is a test form with `tsupport ω ⊆ V` and `N(ω) ≤ 1`
  have hω1 : ∀ x, covectorEuclideanNorm (χ x • g₂ x) ≤ 1 := fun x => by
    rw [hsmul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hg₂1 x)
  refine ⟨fun x => χ x • g₂ x, ⟨hχs.smul hg₂s, hχc.smul_right⟩,
    (tsupport_smul_subset_left χ g₂).trans hχV, hω1, ?_⟩
  -- Step 5: a.e., `N(ω - β) ≤ δ + N(g₁ - β)` where `χ = 1` and `N(ω - β) ≤ 2` on `S = {χ ≠ 1}`
  set S : Set (Euclid P) := {x | χ x ≠ 1}
  have hSm : MeasurableSet S := (isOpen_ne_fun hχs.continuous continuous_const).measurableSet
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ≤
      ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
        S.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    filter_upwards [hβ1] with x hx
    by_cases h1 : χ x = 1
    · rw [indicator_of_notMem (not_not.mpr h1), add_zero,
        ← ENNReal.ofReal_add hδ0.le (covectorEuclideanNorm_nonneg _), h1, one_smul]
      refine ENNReal.ofReal_le_ofReal ?_
      calc covectorEuclideanNorm (g₂ x - β x)
          = covectorEuclideanNorm ((g₂ x - g₁ x) + (g₁ x - β x)) := by rw [sub_add_sub_cancel]
        _ ≤ covectorEuclideanNorm (g₂ x - g₁ x) + covectorEuclideanNorm (g₁ x - β x) :=
          htri _ _
        _ ≤ δ + covectorEuclideanNorm (g₁ x - β x) := by linarith [hg₂g₁ x]
    · rw [indicator_of_mem h1]
      refine le_add_left (le_of_le_of_eq (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_ofNat 2))
      calc covectorEuclideanNorm (χ x • g₂ x - β x)
          = covectorEuclideanNorm (χ x • g₂ x + -β x) := by rw [sub_eq_add_neg]
        _ ≤ covectorEuclideanNorm (χ x • g₂ x) + covectorEuclideanNorm (-β x) := htri _ _
        _ ≤ 2 := by rw [covectorEuclideanNorm_neg]; linarith [hω1 x]
  -- Step 6: integrate, `∫ N(ω - β) dν ≤ δm + ∫ N(g₁ - β) dν + 2ν(S) < 3ε/4`
  have hδm : ENNReal.ofReal δ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← hm, ← ENNReal.ofReal_mul hδ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc δ * m ≤ δ * (m + 1) := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hS2 : 2 * ν S < ENNReal.ofReal (ε / 4) := by
    calc 2 * ν S = ν S + ν S := two_mul _
      _ < ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := ENNReal.add_lt_add hχν hχν
      _ = ENNReal.ofReal (ε / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
          S.indicator (fun _ => (2 : ℝ≥0∞)) x) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal δ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) ∂ν + 2 * ν S := by
        rw [lintegral_add_right _ (measurable_const.indicator hSm),
          lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hSm]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_le_of_lt
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hδm hg₁β) hS2
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)
/-- **Test forms in `U` restrict to compactly supported continuous maps on `U`** (the maps
`g_ω(x) = c(ω(x))` to which the Riesz representation theorem is applied for
`T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T`, Simon Ch. 6, 2.7–2.8; here for any continuous `f` with `f 0 = 0`).
Let `val : U → ℝᴾ` be the inclusion and `K = tsupport ω`.  The map `G = f ∘ ω ∘ val` is
continuous, since `ω` is smooth.  `K` is compact and `K ⊆ U = range val`, so `val⁻¹(K)` is
compact because `val` is inducing.  Off `val⁻¹(K)`, `ω(val x) = 0` and `G x = f 0 = 0`.  So `G`
has compact support in the Hausdorff space `U`, and `g = G ∈ C_c(U, ℝᵈ)`. -/
theorem Submission.cmrc_testForm_restrict_cc : ∀ (P n d : ℕ) (U : Set (Euclid P)) (f : Covector (Euclid P) n → EuclideanSpace ℝ (Fin d)), Continuous f → f 0 = 0 → ∀ ω : TestFormOn U n, ∃ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), ∀ x : U, g x = f ((ω : DifferentialForm (Euclid P) n) x) := by
  intro P n d U f hf hf0 ω
  -- `ω` is smooth with compact support `K = tsupport ω ⊆ U`
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  -- Step 1: `G = f ∘ ω ∘ val` is continuous
  have hGc : Continuous fun x : U => f ((ω : DifferentialForm (Euclid P) n) x) :=
    hf.comp ((ContDiff.continuous hωs).comp continuous_subtype_val)
  -- Step 2: `val⁻¹(K)` is compact, as `val` is inducing and `K ⊆ U = range val`
  have hK : IsCompact ((↑) ⁻¹' tsupport (ω : DifferentialForm (Euclid P) n) : Set U) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hωc.isCompact
      (by rwa [Subtype.range_coe])
  -- Step 3: `G x = f 0 = 0` for `x ∉ val⁻¹(K)`, so `G` has compact support
  have hGs : HasCompactSupport fun x : U => f ((ω : DifferentialForm (Euclid P) n) x) :=
    HasCompactSupport.intro hK fun x hx =>
      (congrArg f (image_eq_zero_of_notMem_tsupport
        (show (x : Euclid P) ∉ tsupport (ω : DifferentialForm (Euclid P) n) from hx))).trans hf0
  exact ⟨⟨⟨fun x => f ((ω : DifferentialForm (Euclid P) n) x), hGc⟩, hGs⟩, fun _ => rfl⟩
/-- **Polar normalization of a vector Riesz density and push-forward to `ℝᴾ`** (the normalization
`|T⃗| = 1` `μ_T`-a.e. in `T(ω) = ∫ ⟨ω, T⃗⟩ dμ_T`, Simon Ch. 6, 2.7, via the Riesz Representation
Theorem, Ch. 1, 4.14).  Write `ρ = ‖ν‖` and `ν̂ = ρ⁻¹ν` (with `0⁻¹ = 0`), so `ν = ρν̂`,
`‖ν̂‖ ≤ 1`, and `‖ν̂‖ = 1` where `ρ ≠ 0`.  Let `u` be `ν̂` extended by `0` off `U`,
`μ = val_*(ρμ₀)`, `ξ(y) = ⟨u(y), c(·)⟩` and `β = c⁻¹ ∘ u`.  Then `μ(Uᶜ) = 0`;
`μ(K) = ∫_{val⁻¹K} ‖ν‖ dμ₀ < ∞` for compact `K ⊆ U`; `|ξ(y)(α)| ≤ ‖c α‖ = |α|` by
Cauchy–Schwarz; `|β(y)| = ‖u(y)‖ ≤ 1`; `ξ(β) = ‖u‖² = 1` wherever the density `ρ` is nonzero;
and `∫ ξ(ω) dμ = ∫ ρ⟨ν̂, c(ω)⟩ dμ₀ = ∫ ⟨c(ω), ν⟩ dμ₀` for every `ω`. -/
theorem Submission.cmrc_polar_pushforward : ∀ (P n d : ℕ) (U : Set (Euclid P)) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (μ₀ : Measure U) (ν : U → EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → Measurable ν → (∀ K : Set U, IsCompact K → IntegrableOn ν K μ₀) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ AEStronglyMeasurable β μ ∧ (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) ∧ (∀ x, covectorEuclideanNorm (β x) ≤ 1) ∧ (∀ᵐ x ∂μ, ξ x (β x) = 1) ∧ ∀ ω : DifferentialForm (Euclid P) n, ∫ x, inner ℝ (c (ω x)) (ν x) ∂μ₀ = ∫ x, ξ x (ω x) ∂μ := by
  intro P n d U c μ₀ ν hU hc hν hloc
  -- Step 1: polar decomposition `ν = ρ • ν̂` with `ρ = ‖ν‖`
  set ρ : U → ℝ := fun x => ‖ν x‖ with hρ_def
  set νh : U → EuclideanSpace ℝ (Fin d) := fun x => (ρ x)⁻¹ • ν x with hνh_def
  have hρm : Measurable ρ := hν.norm
  have hνhm : Measurable νh := hρm.inv.smul hν
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => norm_nonneg _
  have hdecomp : ∀ x, ν x = ρ x • νh x := by
    intro x
    by_cases h : ρ x = 0
    · have h0 : ν x = 0 := norm_eq_zero.mp h
      simp [hνh_def, h0]
    · simp [hνh_def, smul_smul, mul_inv_cancel₀ h]
  have hνh_one : ∀ x, ρ x ≠ 0 → ‖νh x‖ = 1 := by
    intro x h
    simp only [hνh_def]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (hρ0 x), inv_mul_cancel₀ h]
  have hνh_le : ∀ x, ‖νh x‖ ≤ 1 := by
    intro x
    by_cases h : ρ x = 0
    · have h0 : ν x = 0 := norm_eq_zero.mp h
      simp [hνh_def, h0]
    · exact (hνh_one x h).le
  -- Step 2: `val` is a measurable embedding (`U` is open) and the density `ρ` is measurable
  have hval : MeasurableEmbedding (Subtype.val : U → Euclid P) :=
    MeasurableEmbedding.subtype_coe hU.measurableSet
  have hdens : Measurable fun x => ENNReal.ofReal (ρ x) := hρm.ennreal_ofReal
  -- Step 3: the unit field `u`, i.e. `ν̂` extended by `0` off `U`
  set u : Euclid P → EuclideanSpace ℝ (Fin d) := Function.extend Subtype.val νh 0 with hu_def
  have hu_val : ∀ x : U, u x = νh x := fun x => Subtype.val_injective.extend_apply _ _ x
  have hu_notin : ∀ y, y ∉ U → u y = 0 := by
    intro y hy
    rw [hu_def, Function.extend_apply']
    · rfl
    · rintro ⟨x, rfl⟩
      exact hy x.2
  have hum : Measurable u := hval.measurable_extend hνhm measurable_const
  have hu_le : ∀ y, ‖u y‖ ≤ 1 := by
    intro y
    by_cases hy : y ∈ U
    · have := hu_val ⟨y, hy⟩
      simp only at this
      rw [this]
      exact hνh_le _
    · rw [hu_notin y hy, norm_zero]
      exact zero_le_one
  -- Step 4: `μ = val_*(ρ μ₀)`, `ξ(y) = ⟨u(y), c(·)⟩` and `β = c⁻¹ ∘ u`
  refine ⟨(μ₀.withDensity fun x => ENNReal.ofReal (ρ x)).map Subtype.val,
    fun y => (innerSL ℝ (u y)).comp (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d)),
    fun y => c.symm (u y), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) `val⁻¹(Uᶜ) = ∅`
    rw [hval.map_apply]
    have hpre : (Subtype.val : U → Euclid P) ⁻¹' Uᶜ = ∅ := by
      ext x
      simp
    rw [hpre, measure_empty]
  · -- (b) `μ(K) = ∫⁻_{val⁻¹K} ‖ν‖ₑ dμ₀ < ∞`, as `val⁻¹K` is compact
    intro K hK hKU
    rw [hval.map_apply,
      withDensity_apply _ (hK.isClosed.measurableSet.preimage measurable_subtype_coe)]
    have hKc : IsCompact ((Subtype.val : U → Euclid P) ⁻¹' K) := by
      rw [Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
      · exact hK
      · simpa using hKU
    have hint := hloc _ hKc
    have heq : ∫⁻ x in Subtype.val ⁻¹' K, ENNReal.ofReal (ρ x) ∂μ₀ =
        ∫⁻ x in Subtype.val ⁻¹' K, ‖ν x‖ₑ ∂μ₀ := by
      congr 1
      funext x
      simp [hρ_def]
    rw [heq]
    exact hint.2
  · -- (c) `ξ` is a continuous function of the measurable `u`
    have hcont : Continuous (fun v : EuclideanSpace ℝ (Fin d) =>
        (innerSL ℝ v).comp (c : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin d))) :=
      (innerSL ℝ).continuous.clm_comp continuous_const
    exact (hcont.comp_stronglyMeasurable hum.stronglyMeasurable).aestronglyMeasurable
  · -- (d) Cauchy–Schwarz and `‖u‖ ≤ 1`
    intro y α
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, innerSL_apply_apply]
    rw [hc]
    calc |inner ℝ (u y) (c α)| ≤ ‖u y‖ * ‖c α‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖c α‖ := by gcongr; exact hu_le y
      _ = ‖c α‖ := one_mul _
  · -- (e) `β` is a continuous function of the measurable `u`
    exact (c.symm.continuous.comp_stronglyMeasurable hum.stronglyMeasurable).aestronglyMeasurable
  · -- (f) `‖β(y)‖ ≤ ‖c⁻¹‖ ‖u(y)‖ ≤ ‖c⁻¹‖`
    refine ⟨‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖, fun y => ?_⟩
    calc ‖c.symm (u y)‖
        ≤ ‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖ * ‖u y‖ :=
          (c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n).le_opNorm _
      _ ≤ ‖(c.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] Covector (Euclid P) n)‖ * 1 := by
          gcongr
          exact hu_le y
      _ = _ := mul_one _
  · -- (g) `|β(y)| = ‖c(c⁻¹(u y))‖ = ‖u y‖ ≤ 1`
    intro y
    rw [hc, c.apply_symm_apply]
    exact hu_le y
  · -- (h) `ξ(β) = ‖u‖² = 1` wherever the density `ρ` is nonzero
    rw [hval.ae_map_iff, ae_withDensity_iff hdens]
    refine ae_of_all _ (fun x hx => ?_)
    have hρx : ρ x ≠ 0 := by
      intro h
      apply hx
      simp [h]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, innerSL_apply_apply]
    rw [real_inner_self_eq_norm_sq, hu_val, hνh_one x hρx]
    norm_num
  · -- (i) push-forward, then the density, then `⟨c ω, ρ ν̂⟩ = ρ ⟨ν̂, c ω⟩` pointwise
    intro ω
    rw [hval.integral_map,
      integral_withDensity_eq_integral_toReal_smul hdens
        (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    congr 1
    funext x
    rw [ENNReal.toReal_ofReal (hρ0 x), smul_eq_mul]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, innerSL_apply_apply,
      hu_val]
    rw [hdecomp x, inner_smul_right, real_inner_comm]
/-- **Mass upper bound from a representation by a unit-bounded multivector field** (Simon
6.2.5; step 10 of the representation `T = μ_T ∧ ξ⃗`).  Suppose `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x`
and all covectors `α` (`|·|_E` is `covectorEuclideanNorm`), and `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`
for every test form `ω`.  Then `M_W(T) ≤ μ(W)` for every set `W`.  Fix an admissible `ω`, i.e.
`tsupport ω ⊆ W` and `|ω|_E ≤ 1`, and let `K = tsupport ω` (closed, hence Borel) and
`f(x) = ⟨ω(x), ξ(x)⟩`.  Then `|f| ≤ |ω|_E ≤ 1` on `K` and `f = 0` off `K`, so
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_K dμ = μ(K) ≤ μ(W)`; the middle inequality holds whether
or not `f` is integrable.  Taking the supremum over admissible `ω` gives `M_W(T) ≤ μ(W)`. -/
theorem Submission.cmrc_massOn_le_of_repr : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ W : Set (Euclid P), T.massOn W ≤ μ W := by
  intro P n U T μ ξ hξ hT W
  -- Step 1: it suffices to bound `ofReal (T ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  set K : Set (Euclid P) := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  -- Step 2: `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_K(x)` for every `x`
  have hpt : ∀ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ K.indicator 1 x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
  -- Step 3: `T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ μ(K) ≤ μ(W)`
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
    _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono hpt
    _ = μ K := lintegral_indicator_one hKm
    _ ≤ μ W := measure_mono hω.1

/-- **A norming field bounds `μ(W')` by the mass `M_W(T)`** (the inequality `μ_T(W') ≤ M_W(T)`
behind Simon 6.2.8, `μ_T(W) = M_W(T)`, for the representation 6.2.7 `T(ω) = ∫ ⟨ω, ξ⟩ dμ`;
`|·|_E` is `covectorEuclideanNorm`).  Let `W' ⊂⊂ U` be open with `W' ⊆ W`.  Then `ν = μ⌞W'` is
finite, as `closure W'` is a compact subset of `U`, and the bounded field `β` is `ν`-integrable.
For `ε > 0`, `Submission.rsd_mw_exists_testForm_approx` gives a test form `ω` with
`tsupport ω ⊆ W'`, `|ω|_E ≤ 1` and `∫ |ω − β|_E dν < ε`, so `ω` is admissible for `M_W(T)`.
The function `f = ξ(ω)` vanishes off `W'`, so `T(ω) = ∫ f dν`; and `ν`-a.e.
`1 − f = ξ(β − ω) ≤ |ω − β|_E`, since `ξ(β) = 1` and `|ξ(α)| ≤ |α|_E`.  Hence
`μ(W') − T(ω) = ∫ (1 − f) dν < ε`, and `μ(W') ≤ M_W(T) + ε` for every `ε > 0`. -/
theorem Submission.cmrc_measure_le_massOn_of_norming : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → AEStronglyMeasurable β μ → (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) → (∀ x, covectorEuclideanNorm (β x) ≤ 1) → (∀ᵐ x ∂μ, ξ x (β x) = 1) → ∀ W W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ T.massOn W := by
  intro P n U T μ ξ β hμK hξm hξ1 hT hβm hβC hβ1 hξβ W W' hW' hW'U hW'W
  -- `N := covectorEuclideanNorm`, `ν := μ⌞W'`
  -- Step 1: `ν` is finite (`closure W'` is a compact subset of `U`) and `ν(W'ᶜ) = 0`
  have hμW' : μ W' < ∞ := (measure_mono subset_closure).trans_lt (hμK _ hW'U.1 hW'U.2)
  have : IsFiniteMeasure (μ.restrict W') := isFiniteMeasure_restrict.2 hμW'.ne
  have hνc : μ.restrict W' W'ᶜ = 0 := by
    rw [Measure.restrict_apply hW'.measurableSet.compl, compl_inter_self, measure_empty]
  -- Step 2: `β` is bounded, hence `ν`-integrable
  obtain ⟨C, hC⟩ := hβC
  have hβi : Integrable β (μ.restrict W') :=
    Integrable.of_bound hβm.restrict C (Eventually.of_forall hC)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- Step 3: a test form `ω₀` with `tsupport ω₀ ⊆ W'`, `N(ω₀) ≤ 1` and `∫ N(ω₀ - β) dν < ε`
  obtain ⟨ω₀, hω₀, hω₀W', hω₀1, hω₀β⟩ := Submission.rsd_mw_exists_testForm_approx P n
    (μ.restrict W') W' β inferInstance hW' hνc hβi (Eventually.of_forall hβ1) ε
    (NNReal.coe_pos.2 hε)
  -- Step 4: `ω₀ ∈ 𝒟ⁿ(U)` is admissible for `M_W(T)`, so `T(ω₀) ≤ M_W(T)`
  let ω : TestFormOn U n := ⟨ω₀, hω₀, hω₀W'.trans (subset_closure.trans hW'U.2)⟩
  have hTω : ENNReal.ofReal (T ω) ≤ T.massOn W := T.le_massOn ⟨hω₀W'.trans hW'W, hω₀1⟩
  -- Step 5: `f = ξ(ω₀)` vanishes off `W'`, so `T(ω₀) = ∫ f dν`
  set f : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hf
  have hTf : T ω = ∫ x, f x ∂(μ.restrict W') := by
    rw [hT ω, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    simp [hf, image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W' h)]
  -- Step 6: `|f| ≤ N(ω₀) ≤ 1`, so `f` is `ν`-integrable
  have hf1 : ∀ x, |f x| ≤ 1 := fun x => (hξ1 x (ω₀ x)).trans (hω₀1 x)
  have hfm : AEStronglyMeasurable f μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξm.prodMk hω₀.1.continuous.aestronglyMeasurable)
  have hfi : Integrable f (μ.restrict W') :=
    Integrable.of_bound hfm.restrict 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf1 x)
  -- Step 7: `ν`-a.e., `1 - f = ξ(β - ω₀) ≤ N(ω₀ - β)`, since `ξ(β) = 1` and `|ξ(α)| ≤ N(α)`
  have hle : ∀ᵐ x ∂(μ.restrict W'), 1 - f x ≤ covectorEuclideanNorm (ω₀ x - β x) := by
    filter_upwards [ae_restrict_of_ae hξβ] with x hx
    have h := abs_le.1 (hξ1 x (ω₀ x - β x))
    rw [map_sub, hx] at h
    linarith [h.1]
  -- Step 8: `μ(W') - T(ω₀) = ∫ (1 - f) dν ≤ ∫ N(ω₀ - β) dν < ε`
  have hint : ENNReal.ofReal (μ.real W' - T ω) < ENNReal.ofReal ε := by
    have h1 : ∫ x, (1 - f x) ∂(μ.restrict W') = μ.real W' - T ω := by
      rw [integral_sub (integrable_const 1) hfi, integral_const, hTf, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ]
    have hgi : Integrable (fun x => 1 - f x) (μ.restrict W') := (integrable_const 1).sub hfi
    rw [← h1, ofReal_integral_eq_lintegral_ofReal hgi
      (Eventually.of_forall fun x => sub_nonneg.2 (le_of_abs_le (hf1 x)))]
    exact (lintegral_mono_ae (hle.mono fun x hx => ENNReal.ofReal_le_ofReal hx)).trans_lt hω₀β
  -- Step 9: `μ(W') ≤ T(ω₀) + ε ≤ M_W(T) + ε`
  calc μ W' = ENNReal.ofReal (T ω + (μ.real W' - T ω)) := by
        rw [add_sub_cancel, ofReal_measureReal hμW'.ne]
    _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal (μ.real W' - T ω) := ENNReal.ofReal_add_le
    _ ≤ T.massOn W + ε := add_le_add hTω (hint.le.trans_eq ENNReal.ofReal_coe_nnreal)
/-- Exhaustion by compactly contained open sets: if `U, W ⊆ ℝᴾ` are open, `μ(ℝᴾ \ U) = 0` and
`μ(W') ≤ m` for every open `W' ⊂⊂ U` with `W' ⊆ W`, then `μ(W) ≤ m`.  The open sets
`W'ⱼ = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` have closures inside the compact sets
`{y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} ⊆ W ∩ U`, increase with `j` and exhaust `W ∩ U`,
so `μ(W) = μ(W ∩ U) = supⱼ μ(W'ⱼ) ≤ m` by continuity from below. -/
theorem Submission.cmrc_measure_le_of_compactlyContained : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U W : Set (Euclid P)) (m : ℝ≥0∞), IsOpen U → IsOpen W → μ Uᶜ = 0 → (∀ W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ m) → μ W ≤ m := by
  intro P μ U W m hU hW hUc hm
  -- `V j = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` exhausts the open set `W ∩ U`
  set V : ℕ → Set (Euclid P) :=
    fun j => {y | ‖y‖ < j ∧ ((j : ℝ≥0∞) + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}
  have hd : Continuous fun y : Euclid P => infEDist y (W ∩ U)ᶜ := continuous_infEDist
  have hpos : ∀ j : ℕ, 0 < ((j : ℝ≥0∞) + 1)⁻¹ := fun j => ENNReal.inv_pos.2 (by simp)
  -- `closure (V j)` lies in `F j = {y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ}`, a compact
  -- subset of `W ∩ U`
  have hF : ∀ j : ℕ, IsCompact (closure (V j)) ∧ closure (V j) ⊆ W ∩ U := by
    intro j
    have hVF : closure (V j) ⊆
        {y : Euclid P | ‖y‖ ≤ j ∧ ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} :=
      closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const hd))
    refine ⟨(isCompact_closedBall (0 : Euclid P) (j : ℝ)).of_isClosed_subset isClosed_closure
      fun y hy => ?_, fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact (hVF hy).1
    · by_contra hy'
      have h := (hVF hy).2
      rw [infEDist_zero_of_mem hy'] at h
      exact (hpos j).not_ge h
  have hVsub : ∀ j, V j ⊆ W ∩ U := fun j => subset_closure.trans (hF j).2
  have hVm : ∀ j, μ (V j) ≤ m := fun j =>
    hm (V j) ((isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd))
      ⟨(hF j).1, (hF j).2.trans inter_subset_right⟩ ((hVsub j).trans inter_subset_left)
  have hmono : Monotone V := by
    intro j k hjk y hy
    refine ⟨hy.1.trans_le (by exact_mod_cast hjk), lt_of_le_of_lt ?_ hy.2⟩
    gcongr
  have hUnion : ⋃ j, V j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset hVsub) fun y hy => ?_
    have hne : infEDist y (W ∩ U)ᶜ ≠ 0 := fun h0 =>
      ((mem_iff_infEDist_zero_of_closed (hW.inter hU).isClosed_compl).2 h0) hy
    obtain ⟨j₁, hj₁⟩ := ENNReal.exists_inv_nat_lt hne
    obtain ⟨j₂, hj₂⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max j₁ j₂, hj₂.trans_le (by exact_mod_cast le_max_right j₁ j₂),
      lt_of_le_of_lt ?_ hj₁⟩
    gcongr
    norm_cast
    omega
  -- `μ W = μ (W ∩ U)` since `μ Uᶜ = 0`; continuity from below along the increasing `V j`
  calc μ W = μ (⋃ j, V j) := by rw [hUnion, measure_inter_conull hUc]
    _ = ⨆ j, μ (V j) := hmono.measure_iUnion
    _ ≤ m := iSup_le hVm

/-- **Uniform approximation by test forms** (extension of a current of locally finite mass to
continuous fields, approximating sequences).  Let `|α| = covectorEuclideanNorm α = ‖c α‖` for a
continuous linear equivalence `c` onto a Euclidean space.  A continuous, compactly supported
`n`-covector field `G` with `tsupport G ⊆ V` (`V` open) is uniformly `ε`-approximated in `|·|` by a
test form `ω` with `tsupport ω ⊆ V`.

Since `c` is linear, `|t • α| = |t| |α|`.  The field `c ∘ G` is continuous with compact support,
hence bounded, so `|G| ≤ s` for some `s > 0`.  Mollifying the unit field `g = s⁻¹ • G` with error
`ε / s` (`dor_ims_sua_mollify_unit_field`) gives a test form `ω₀` with `tsupport ω₀ ⊆ V`; then
`ω = s • ω₀` is a test form with `tsupport ω ⊆ V` and `|ω x − G x| = s |ω₀ x − g x| ≤ ε`. -/
theorem Submission.cmr_tfe_uniform_testForm_approx : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (V : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (ε : ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → IsOpen V → Continuous G → HasCompactSupport G → tsupport G ⊆ V → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ ∀ x, covectorEuclideanNorm (ω x - G x) ≤ ε := by
  intro P n d c V G ε hc hV hG hGs hGV hε
  -- (1) homogeneity: `|t • α| = ‖c (t • α)‖ = |t| ‖c α‖ = |t| |α|`
  have hsm : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := fun t α => by
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- (2) `c ∘ G` is continuous with compact support, so `|G| ≤ s` for some `s > 0`
  obtain ⟨C, hC⟩ := (hGs.comp_left (map_zero c)).exists_bound_of_continuous (c.continuous.comp hG)
  obtain ⟨s, hs, hGs'⟩ : ∃ s : ℝ, 0 < s ∧ ∀ x, covectorEuclideanNorm (G x) ≤ s :=
    ⟨max C 0 + 1, by positivity, fun x => by
      rw [hc]
      exact (hC x).trans ((le_max_left C 0).trans (le_add_of_nonneg_right zero_le_one))⟩
  -- (3) the normalized field `g = s⁻¹ • G` has `|g| ≤ 1`
  have hg1 : ∀ x, covectorEuclideanNorm (s⁻¹ • G x) ≤ 1 := fun x => by
    rw [hsm, abs_of_pos (inv_pos.mpr hs), inv_mul_le_iff₀ hs, mul_one]
    exact hGs' x
  -- (4) mollify `g` with error `ε / s`
  obtain ⟨ω₀, hω₀, hω₀V, -, hω₀g⟩ := Submission.dor_ims_sua_mollify_unit_field P n V
    (s⁻¹ • G) (ε / s) hV (hG.const_smul s⁻¹) (hGs.comp_left (smul_zero s⁻¹))
    ((tsupport_smul_subset_right (fun _ => s⁻¹) G).trans hGV) hg1 (div_pos hε hs)
  -- (5) `ω = s • ω₀` is a test form with `tsupport ω ⊆ V`
  refine ⟨s • ω₀, (testFormSubmodule n).smul_mem s hω₀,
    (tsupport_smul_subset_right (fun _ => s) ω₀).trans hω₀V, fun x => ?_⟩
  -- (6) `ω x - G x = s • (ω₀ x - g x)`, so `|ω x - G x| = s |ω₀ x - g x| ≤ s (ε / s) = ε`
  have hω : (s • ω₀) x - G x = s • (ω₀ x - s⁻¹ • G x) := by
    rw [Pi.smul_apply, smul_sub, smul_inv_smul₀ hs.ne']
  rw [hω, hsm, abs_of_pos hs]
  exact (le_div_iff₀' hs).mp (hω₀g x)
/-- **Limit functional along uniformly convergent test forms** (test-form extension, steps 4–5).
Let `|α| = ‖c α‖` for a continuous linear equivalence `c`, and let `|T ω| ≤ r m(W)` whenever
`W ⊂⊂ U` is open, `spt ω ⊆ W` and `|ω(x)| ≤ r` for all `x`.  Then there is `Φ` with
`T(ωₖ) → Φ(G)` whenever `spt ωₖ ⊆ W` for one open `W ⊂⊂ U` and all `k`, and
`|ωₖ(x) − G(x)| ≤ εₖ` for all `k`, `x`, with `εₖ → 0`.

For two such data `(W, ωₖ, εₖ)`, `(W', ω'ₗ, ε'ₗ)` of the same `G`, `ωₖ − ω'ₗ` is a test form with
`spt ⊆ W ∪ W' ⊂⊂ U` and `|ωₖ − ω'ₗ| ≤ εₖ + ε'ₗ`, so `|T(ωₖ) − T(ω'ₗ)| ≤ (εₖ + ε'ₗ) m(W ∪ W')`.
With equal data, `(T(ωₖ))` is Cauchy, hence convergent.  `Φ(G)` is the limit along chosen data
(`0` if there are none), and the estimate with `l = k` shows that every approximating sequence
of `G` tends to `Φ(G)`. -/
theorem Submission.cmr_tfe_exists_limit_functional : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, ∀ (G : Euclid P → Covector (Euclid P) n) (W : Set (Euclid P)) (ωs : ℕ → TestFormOn U n) (εs : ℕ → ℝ), IsOpen W → CompactlyContained W U → (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) → (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) → Tendsto εs atTop (𝓝 0) → Tendsto (fun k => T (ωs k)) atTop (𝓝 (Φ G)) := by
  intro P n d c U T m hc hm
  classical
  -- (1) `|α − β| ≤ |α| + |β|`, since `|·| = ‖c ·‖` with `c` linear
  have htri : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α - β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_sub]
    exact norm_sub_le _ _
  -- (2)–(3) the key estimate for two approximating data of the same `G`
  have hkey : ∀ (G : Euclid P → Covector (Euclid P) n) (W W' : Set (Euclid P))
      (ωs ωs' : ℕ → TestFormOn U n) (εs εs' : ℕ → ℝ), IsOpen W → CompactlyContained W U →
      (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) →
      (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) →
      IsOpen W' → CompactlyContained W' U →
      (∀ k, tsupport (ωs' k : DifferentialForm (Euclid P) n) ⊆ W') →
      (∀ k x, covectorEuclideanNorm ((ωs' k : DifferentialForm (Euclid P) n) x - G x) ≤ εs' k) →
      ∀ k l, |T (ωs k) - T (ωs' l)| ≤ (εs k + εs' l) * m (W ∪ W') := by
    intro G W W' ωs ωs' εs εs' hW hWU hωW hωG hW' hW'U hω'W hω'G k l
    -- `W ∪ W'` is open and `W ∪ W' ⊂⊂ U`
    have hWW'U : CompactlyContained (W ∪ W') U := by
      rw [CompactlyContained, closure_union]
      exact ⟨hWU.1.union hW'U.1, union_subset hWU.2 hW'U.2⟩
    -- the bound for `δ = ωs k − ωs' l`, and `T δ = T (ωs k) − T (ωs' l)` by linearity
    have h := hm (W ∪ W') (ωs k - ωs' l) (εs k + εs' l) (hW.union hW') hWW'U ?_ ?_
    · rwa [map_sub T.toCurrent] at h
    · rw [Submodule.coe_sub]
      exact (tsupport_sub _ _).trans (union_subset_union (hωW k) (hω'W l))
    · intro x
      rw [Submodule.coe_sub, Pi.sub_apply,
        ← sub_sub_sub_cancel_right ((ωs k : DifferentialForm (Euclid P) n) x) _ (G x)]
      exact (htri _ _).trans (add_le_add (hωG k x) (hω'G l x))
  -- (4) along approximating data, `(T (ωs k))` is Cauchy, hence convergent
  have hconv : ∀ (G : Euclid P → Covector (Euclid P) n) (W : Set (Euclid P))
      (ωs : ℕ → TestFormOn U n) (εs : ℕ → ℝ), IsOpen W → CompactlyContained W U →
      (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) →
      (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) →
      Tendsto εs atTop (𝓝 0) → ∃ L, Tendsto (fun k => T (ωs k)) atTop (𝓝 L) := by
    intro G W ωs εs hW hWU hωW hωG hε
    refine cauchySeq_tendsto_of_complete (cauchySeq_iff_tendsto_dist_atTop_0.mpr ?_)
    have h0 := ((hε.comp tendsto_fst).add (hε.comp tendsto_snd)).mul_const (m (W ∪ W))
    rw [add_zero, zero_mul, prod_atTop_atTop_eq] at h0
    refine squeeze_zero (fun _ => dist_nonneg) (fun p => ?_) h0
    rw [Real.dist_eq]
    exact hkey G W W ωs ωs εs εs hW hWU hωW hωG hW hWU hωW hωG p.1 p.2
  -- (5) `Φ G` is the limit along chosen approximating data of `G` (`0` if there are none)
  refine ⟨fun G => if h : ∃ (L : ℝ) (W : Set (Euclid P)) (ωs : ℕ → TestFormOn U n)
      (εs : ℕ → ℝ), IsOpen W ∧ CompactlyContained W U ∧
      (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) ∧
      (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) ∧
      Tendsto εs atTop (𝓝 0) ∧ Tendsto (fun k => T (ωs k)) atTop (𝓝 L) then h.choose else 0, ?_⟩
  -- (6) every approximating sequence of `G` tends to `Φ G`
  intro G W ωs εs hW hWU hωW hωG hε
  obtain ⟨L, hL⟩ := hconv G W ωs εs hW hWU hωW hωG hε
  have h : ∃ (L : ℝ) (W : Set (Euclid P)) (ωs : ℕ → TestFormOn U n) (εs : ℕ → ℝ),
      IsOpen W ∧ CompactlyContained W U ∧
      (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) ∧
      (∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤ εs k) ∧
      Tendsto εs atTop (𝓝 0) ∧ Tendsto (fun k => T (ωs k)) atTop (𝓝 L) :=
    ⟨L, W, ωs, εs, hW, hWU, hωW, hωG, hε, hL⟩
  dsimp only
  rw [dite_eq_left h]
  obtain ⟨W', ωs', εs', hW', hW'U, hω'W, hω'G, hε', hL'⟩ := h.choose_spec
  have h0 := (hε.add hε').mul_const (m (W ∪ W'))
  rw [add_zero, zero_mul] at h0
  have hdiff : Tendsto (fun k => T (ωs k) - T (ωs' k)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (Real.norm_eq_abs _).trans_le
      (hkey G W W' ωs ωs' εs εs' hW hWU hωW hωG hW' hW'U hω'W hω'G k k)) h0
  have hlim := hL'.add hdiff
  rw [add_zero] at hlim
  exact hlim.congr fun k => add_sub_cancel _ _

/-- **Extending a locally bounded current to continuous covector fields.**  Let `|α| = ‖c α‖` for
a continuous linear equivalence `c` onto `ℝᵈ`, and let `m` bound `T` locally: `|T(ω)| ≤ r m(W)`
whenever `W ⊂⊂ U` is open, `spt ω ⊆ W` and `|ω| ≤ r`.  Take `Φ` with `T(ωₖ) → Φ(G)` along test
forms `ωₖ` supported in one open `W ⊂⊂ U` with `|ωₖ − G| ≤ εₖ → 0`
(`cmr_tfe_exists_limit_functional`).  A compact subset of `U` lies in an open `W ⊂⊂ U`, and a
continuous `G` with compact support in `W` has such approximants with `εₖ = 1/(k+1)`
(`cmr_tfe_uniform_testForm_approx`).  Sums and multiples of approximants approximate `G₁ + G₂`
(in `W₁ ∪ W₂`) and `t G`, so additivity and homogeneity follow from the linearity of `T` and
uniqueness of limits; the constant sequence `ω` gives `Φ(ω) = T(ω)`; and `|ωₖ| ≤ r + 1/(k+1)`
gives `|T(ωₖ)| ≤ (r + 1/(k+1)) m(W)`, whence `|Φ(G)| ≤ r m(W)`. -/
theorem Submission.cmr_tfe_ambient_extension : ∀ (P n d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (m : Set (Euclid P) → ℝ), IsOpen U → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → (∀ (W : Set (Euclid P)) (ω : TestFormOn U n) (r : ℝ), IsOpen W → CompactlyContained W U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * m W) → ∃ Φ : (Euclid P → Covector (Euclid P) n) → ℝ, (∀ G₁ G₂ : Euclid P → Covector (Euclid P) n, Continuous G₁ → HasCompactSupport G₁ → tsupport G₁ ⊆ U → Continuous G₂ → HasCompactSupport G₂ → tsupport G₂ ⊆ U → Φ (G₁ + G₂) = Φ G₁ + Φ G₂) ∧ (∀ (t : ℝ) (G : Euclid P → Covector (Euclid P) n), Continuous G → HasCompactSupport G → tsupport G ⊆ U → Φ (t • G) = t * Φ G) ∧ (∀ ω : TestFormOn U n, Φ (ω : DifferentialForm (Euclid P) n) = T ω) ∧ ∀ (W : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n) (r : ℝ), IsOpen W → CompactlyContained W U → Continuous G → HasCompactSupport G → tsupport G ⊆ W → (∀ x, covectorEuclideanNorm (G x) ≤ r) → |Φ G| ≤ r * m W := by
  intro P n d c U T m hU hc hm
  -- (1) the limit functional `Φ`
  obtain ⟨Φ, hΦ⟩ := Submission.cmr_tfe_exists_limit_functional P n d c U T m hc hm
  -- `|α + β| ≤ |α| + |β|` and `|t • α| = |t| |α|`, read through `c`
  have hadd : ∀ α β : Covector (Euclid P) n,
      covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β := by
    intro α β
    rw [hc, hc, hc, map_add]
    exact norm_add_le _ _
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hc, hc, map_smul, norm_smul, Real.norm_eq_abs]
  -- (2) a compact subset of `U` lies in an open `W ⊂⊂ U`; and `W ⊂⊂ U` gives `W ⊆ U`
  have hnbhd : ∀ S : Set (Euclid P), IsCompact S → S ⊆ U →
      ∃ W, IsOpen W ∧ S ⊆ W ∧ CompactlyContained W U := by
    intro S hS hSU
    obtain ⟨W, hWo, hSW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
    exact ⟨W, hWo, hSW, hWc, hWU⟩
  have hsub : ∀ W, CompactlyContained W U → W ⊆ U := fun W hW => subset_closure.trans hW.2
  -- (3) approximants `ωₖ ∈ 𝒟ⁿ(U)` with `spt ωₖ ⊆ W` and `|ωₖ − G| ≤ 1/(k+1)`
  have happrox : ∀ (W : Set (Euclid P)) (G : Euclid P → Covector (Euclid P) n), IsOpen W →
      CompactlyContained W U → Continuous G → HasCompactSupport G → tsupport G ⊆ W →
      ∃ ωs : ℕ → TestFormOn U n, (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ W) ∧
        ∀ k x, covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x - G x) ≤
          1 / ((k : ℝ) + 1) := by
    intro W G hW hWU hG hGc hGW
    have hk : ∀ k : ℕ, ∃ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W ∧
        ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x - G x) ≤
          1 / ((k : ℝ) + 1) := by
      intro k
      obtain ⟨ω, hωt, hωW, hωe⟩ := Submission.cmr_tfe_uniform_testForm_approx P n d c
        W G (1 / ((k : ℝ) + 1)) hc hW hG hGc hGW (by positivity)
      exact ⟨⟨ω, hωt, hωW.trans (hsub W hWU)⟩, hωW, hωe⟩
    choose ωs hωW hωe using hk
    exact ⟨ωs, hωW, hωe⟩
  have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · -- (4) additivity: `ω¹ₖ + ω²ₖ` approximates `G₁ + G₂` in `W₁ ∪ W₂ ⊂⊂ U`
    intro G₁ G₂ hG₁ hG₁c hG₁U hG₂ hG₂c hG₂U
    obtain ⟨W₁, hW₁o, hG₁W₁, hW₁U⟩ := hnbhd _ hG₁c hG₁U
    obtain ⟨W₂, hW₂o, hG₂W₂, hW₂U⟩ := hnbhd _ hG₂c hG₂U
    obtain ⟨ω₁, hω₁W, hω₁e⟩ := happrox W₁ G₁ hW₁o hW₁U hG₁ hG₁c hG₁W₁
    obtain ⟨ω₂, hω₂W, hω₂e⟩ := happrox W₂ G₂ hW₂o hW₂U hG₂ hG₂c hG₂W₂
    have hWU : CompactlyContained (W₁ ∪ W₂) U := by
      refine ⟨?_, ?_⟩ <;> rw [closure_union]
      exacts [hW₁U.1.union hW₂U.1, union_subset hW₁U.2 hW₂U.2]
    have h := hΦ (G₁ + G₂) (W₁ ∪ W₂) (fun k => ω₁ k + ω₂ k)
      (fun k => 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1)) (hW₁o.union hW₂o) hWU
      (fun k => by
        simp only [Submodule.coe_add]
        exact (tsupport_add _ _).trans (union_subset_union (hω₁W k) (hω₂W k)))
      (fun k x => by
        simp only [Submodule.coe_add, Pi.add_apply]
        rw [add_sub_add_comm]
        exact (hadd _ _).trans (add_le_add (hω₁e k x) (hω₂e k x)))
      (by simpa only [add_zero] using hlim.add hlim)
    have h' : Tendsto (fun k => T (ω₁ k + ω₂ k)) atTop (𝓝 (Φ G₁ + Φ G₂)) :=
      ((hΦ G₁ W₁ ω₁ _ hW₁o hW₁U hω₁W hω₁e hlim).add
        (hΦ G₂ W₂ ω₂ _ hW₂o hW₂U hω₂W hω₂e hlim)).congr fun k =>
          (T.toCurrent.map_add (ω₁ k) (ω₂ k)).symm
    exact tendsto_nhds_unique h h'
  · -- (5) homogeneity: `t ωₖ` approximates `t G` with errors `|t|/(k+1)`
    intro t G hG hGc hGU
    obtain ⟨W, hWo, hGW, hWU⟩ := hnbhd _ hGc hGU
    obtain ⟨ωs, hωW, hωe⟩ := happrox W G hWo hWU hG hGc hGW
    have h := hΦ (t • G) W (fun k => t • ωs k) (fun k => |t| * (1 / ((k : ℝ) + 1))) hWo hWU
      (fun k => by
        simp only [Submodule.coe_smul]
        exact (tsupport_smul_subset_right (fun _ => t) _).trans (hωW k))
      (fun k x => by
        simp only [Submodule.coe_smul, Pi.smul_apply]
        have e : t • (ωs k : DifferentialForm (Euclid P) n) x - t • G x =
            t • ((ωs k : DifferentialForm (Euclid P) n) x - G x) := (smul_sub t _ _).symm
        rw [e, hsmul]
        exact mul_le_mul_of_nonneg_left (hωe k x) (abs_nonneg t))
      (by simpa only [mul_zero] using hlim.const_mul |t|)
    have h' : Tendsto (fun k => T (t • ωs k)) atTop (𝓝 (t * Φ G)) :=
      ((hΦ G W ωs _ hWo hWU hωW hωe hlim).const_mul t).congr fun k => by
        rw [T.toCurrent.map_smul, smul_eq_mul]
    exact tendsto_nhds_unique h h'
  · -- (6) agreement: the constant sequence `ω`, with errors `0`
    intro ω
    obtain ⟨W, hWo, hωW, hWU⟩ := hnbhd _ ω.property.1.2 ω.property.2
    exact tendsto_nhds_unique (hΦ (ω : DifferentialForm (Euclid P) n) W (fun _ => ω) (fun _ => 0)
      hWo hWU (fun _ => hωW) (fun _ x => by simp) tendsto_const_nhds) tendsto_const_nhds
  · -- (7) bound: `|ωₖ| ≤ r + 1/(k+1)`, so `|T(ωₖ)| ≤ (r + 1/(k+1)) m(W)`; let `k → ∞`
    intro W G r hWo hWU hG hGc hGW hr
    obtain ⟨ωs, hωW, hωe⟩ := happrox W G hWo hWU hG hGc hGW
    have hb : ∀ k : ℕ, |T (ωs k)| ≤ (r + 1 / ((k : ℝ) + 1)) * m W := by
      intro k
      refine hm W (ωs k) _ hWo hWU (hωW k) fun x => ?_
      calc covectorEuclideanNorm ((ωs k : DifferentialForm (Euclid P) n) x)
          = covectorEuclideanNorm (((ωs k : DifferentialForm (Euclid P) n) x - G x) + G x) := by
            rw [sub_add_cancel]
        _ ≤ 1 / ((k : ℝ) + 1) + r := (hadd _ _).trans (add_le_add (hωe k x) (hr x))
        _ = r + 1 / ((k : ℝ) + 1) := add_comm _ _
    have hmW : Tendsto (fun k : ℕ => (r + 1 / ((k : ℝ) + 1)) * m W) atTop (𝓝 (r * m W)) := by
      simpa only [add_zero] using ((tendsto_const_nhds (x := r)).add hlim).mul_const (m W)
    exact le_of_tendsto_of_tendsto' (hΦ G W ωs _ hWo hWU hωW hωe hlim).abs hmW hb
/-- **Simon 6.1.2, 6.1.5, 6.1.15** (the coefficient norm is Euclidean): `n`-covectors on `ℝᴾ`
with `|α|_E = (Σ_I α(e_I)²)^{1/2}`, `I` strictly increasing, form a Euclidean space `ℝᵈ`.  The
coefficient map `A α = (α(e_I))_I` (zero off the increasing `I`) into `ℝ^{Fin n → Fin P}` has
`‖A α‖ = |α|_E`, and it is injective by the Gram bound `|α v| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}`.
An orthonormal basis of `range A` identifies it isometrically with `ℝᵈ`; then covectors are
finite-dimensional, so this linear equivalence is continuous. -/
theorem Submission.cmr_covector_euclidean_equiv : ∀ (P n : ℕ), ∃ (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖ := by
  intro P n
  -- the coefficient map `A α = (α(e_I))_I`, zero off the strictly increasing `I`
  let A : Covector (Euclid P) n →ₗ[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    { toFun := fun α => WithLp.toLp 2 (fun I => if StrictMono I then
        α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) else 0)
      map_add' := fun α β => by
        ext I
        simp only [PiLp.add_apply, ContinuousAlternatingMap.add_apply]
        split_ifs <;> simp
      map_smul' := fun t α => by
        ext I
        simp only [PiLp.smul_apply, ContinuousAlternatingMap.smul_apply, RingHom.id_apply,
          smul_eq_mul]
        split_ifs <;> simp }
  -- `‖A α‖ = |α|_E`
  have hnorm : ∀ α, ‖A α‖ = covectorEuclideanNorm α := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [A, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
    split_ifs <;> simp
  -- `A` is injective: `|α|_E = 0` forces `α v = 0` by the Gram bound
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro α hα
    have h0 : covectorEuclideanNorm α = 0 := by rw [← hnorm, hα, norm_zero]
    ext v
    have hv := (Submission.covectorEuclideanNorm_gram_bounds P n).1 α v
    rw [h0, zero_mul] at hv
    simpa using abs_nonpos_iff.mp hv
  -- identify `range A` isometrically with `ℝᵈ` through an orthonormal basis
  let S := LinearMap.range A
  let b := stdOrthonormalBasis ℝ S
  let e₀ : Covector (Euclid P) n ≃ₗ[ℝ] S := LinearEquiv.ofInjective A hinj
  let c₀ : Covector (Euclid P) n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ S)) :=
    e₀.trans b.repr.toLinearEquiv
  have hc₀ : ∀ α, ‖c₀ α‖ = covectorEuclideanNorm α := by
    intro α
    have h1 : c₀ α = b.repr (e₀ α) := rfl
    rw [h1, LinearIsometryEquiv.norm_map, ← Submodule.norm_coe, LinearEquiv.ofInjective_apply,
      hnorm]
  -- covectors are finite-dimensional, so `c₀` is continuous
  have : FiniteDimensional ℝ (Covector (Euclid P) n) := LinearEquiv.finiteDimensional c₀.symm
  refine ⟨Module.finrank ℝ S, c₀.toContinuousLinearEquiv, fun α => ?_⟩
  rw [LinearEquiv.coe_toContinuousLinearEquiv', hc₀]
/-- **Test forms are Lipschitz in the Euclidean coefficient norm** (the constant `c` of the cone
inequality, Simon Ch. 6, 2.27/2.30 as used in 8.2(4)–(6)).  `ω` is `C^∞` with compact support, so
`Dω` is continuous with compact support and `‖Dω(z)‖ ≤ L₀` for some `L₀ ≥ 0`; the mean value
inequality on the convex set `ℝᴾ` gives `‖ω(x) - ω(y)‖ ≤ L₀ ‖x - y‖`.  With the bound
`covectorEuclideanNorm β ≤ C ‖β‖` of `Submission.rsd_mw_tfa_norm_props`, `c = C L₀` works. -/
theorem Submission.cbrld_cone_testForm_coeff_lipschitz : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : Euclid P, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y) ≤ c * dist x y := by
  intro P k U ω
  -- Step 1: the coefficient norm is dominated by the operator norm, `|β| ≤ C ‖β‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P k).2.2.1
  -- Step 2: `ω` is smooth with compact support, so `Dω` is continuous with compact support
  have hsm : IsSmoothForm (ω : DifferentialForm (Euclid P) k) := ω.property.1.1
  have hcs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.property.1.2
  have hcont : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) :=
    hsm.continuous_fderiv (by simp)
  have hcs' : HasCompactSupport (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) := hcs.fderiv ℝ
  -- Step 3: `Dω` is bounded, `‖Dω(z)‖ ≤ L ≤ max L 0`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, ‖fderiv ℝ (ω : DifferentialForm (Euclid P) k) z‖ ≤ L :=
    Continuous.bounded_above_of_compact_support
      (f := fderiv ℝ (ω : DifferentialForm (Euclid P) k)) hcont hcs'
  -- Step 4: the mean value inequality on the convex set `ℝᴾ`
  have hdiff : Differentiable ℝ (ω : DifferentialForm (Euclid P) k) :=
    hsm.differentiable (by simp)
  have hmv : ∀ x y : Euclid P, ‖(ω : DifferentialForm (Euclid P) k) x -
      (ω : DifferentialForm (Euclid P) k) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
  -- Step 5: `c = C · max L 0`
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right _ _), fun x y => ?_⟩
  have h1 := hC ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y)
  have h2 := mul_le_mul_of_nonneg_left (hmv x y) hC0
  rw [dist_eq_norm]
  calc covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x -
        (ω : DifferentialForm (Euclid P) k) y)
      ≤ C * ‖(ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y‖ := h1
    _ ≤ C * (max L 0 * ‖x - y‖) := h2
    _ = C * max L 0 * ‖x - y‖ := by ring
/-- **Simon 6.2.25, 6.2.30** (homotopy formula for a constant form): the affine contraction
`ψ(y) = (n + 1)⁻¹ • α.curryLeft (y - x₀)`, i.e. `ψ(y)(v₁, …, vₙ) = (n + 1)⁻¹ α(y - x₀, v₁, …, vₙ)`,
is a primitive of the constant `(n + 1)`-covector `α`.  Its derivative is the constant map
`(n + 1)⁻¹ • α.curryLeft`, and alternatizing `α.curryLeft` gives `(n + 1) • α`. -/
theorem Submission.cbrld_cone_extDeriv_affine_contraction : ∀ (P n : ℕ) (α : Covector (Euclid P) (n + 1)) (x₀ x : Euclid P), extDeriv (fun y : Euclid P => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀)) x = α := by
  intro P n α x₀ x
  -- `y ↦ α.curryLeft (y - x₀)` is affine with linear part `α.curryLeft`
  have h1 : HasFDerivAt (fun y : Euclid P => α.curryLeft (y - x₀)) α.curryLeft x := by
    have h := (α.curryLeft.hasFDerivAt (x := x - x₀)).comp x ((hasFDerivAt_id x).sub_const x₀)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have hd : HasFDerivAt (fun y : Euclid P => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀))
      (((n : ℝ) + 1)⁻¹ • α.curryLeft) x := h1.const_smul (((n : ℝ) + 1)⁻¹)
  -- `extDeriv ψ x = (n + 1)⁻¹ • alternatizeUncurryFin α.curryLeft = (n + 1)⁻¹ • (n + 1) • α`
  rw [extDeriv, hd.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_smul,
    ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [inv_mul_cancel₀ hn, one_smul]
/-- **Localization to a neighbourhood of `spt X`** (Simon 6.2.11): assuming (VO), i.e. that a
current kills every test form whose support misses its support, a current `X` takes the same
value on test forms `φ₁`, `φ₂` that agree on an open set `G ⊇ spt X`.  The difference `φ₁ - φ₂`
vanishes on `G`, so its topological support lies in the closed set `Gᶜ`, which misses `spt X`;
(VO) and linearity give `X(φ₁) - X(φ₂) = X(φ₁ - φ₂) = 0`. -/
theorem Submission.cbrld_cone_eval_eq_of_eqOn_open : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P k : ℕ) (U G : Set (Euclid P)) (X : GeometricCurrentOn U k) (φ₁ φ₂ : TestFormOn U k), IsOpen G → X.support ⊆ G → EqOn (φ₁ : DifferentialForm (Euclid P) k) (φ₂ : DifferentialForm (Euclid P) k) G → X φ₁ = X φ₂ := by
  intro VO P k U G X φ₁ φ₂ hG hspt heq
  -- `φ₁ - φ₂` vanishes on the open set `G`, so its topological support lies in `Gᶜ`
  have hsub : tsupport ((φ₁ - φ₂ : TestFormOn U k) : DifferentialForm (Euclid P) k) ⊆ Gᶜ := by
    apply closure_minimal _ hG.isClosed_compl
    intro x hx hxG
    apply hx
    change (φ₁ : DifferentialForm (Euclid P) k) x - (φ₂ : DifferentialForm (Euclid P) k) x = 0
    rw [heq hxG, sub_self]
  -- hence it misses `spt X ⊆ G`, and (VO) kills it
  have hdisj : Disjoint (tsupport ((φ₁ - φ₂ : TestFormOn U k) : DifferentialForm (Euclid P) k))
      X.support :=
    Disjoint.mono hsub hspt disjoint_compl_left
  have h := VO P k U X (φ₁ - φ₂) hdisj
  -- linearity of `X`
  have h2 := X.toCurrent.map_sub φ₁ φ₂
  change X (φ₁ - φ₂) = X φ₁ - X φ₂ at h2
  linarith
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2

/-- **Constant forms are boundaries near the support of a cycle** (steps 5 and 7 of the cone
inequality used in Simon Ch. 6, 8.2(4)–(6), via the homotopy formula 2.25 and the cone 2.30).
Assume (VO), the vanishing of a current on test forms supported off its support.  If
`X ∈ 𝒟_{n+1}(ℝᴾ)` has `∂X = 0` and `spt X ⊆ B_r(x₀)`, and the test form `φ` equals the constant
covector `α` on `B_r(x₀)`, then `X(φ) = 0`.  With the bump `ζ` (`ζ = 1` on `B̄_r(x₀)`) and the
primitive `ψ(y) = (n + 1)⁻¹ ι_{y−x₀} α` of `α` (`cbrld_cone_extDeriv_affine_contraction`), the
test form `η = ζψ` has `dη = dψ = α = φ` on `B_r(x₀)`, so `cbrld_cone_eval_eq_of_eqOn_open` gives
`X(φ) = X(dη) = ∂X(η) = 0`. -/
theorem Submission.cbrld_cone_cycle_eval_eq_zero_of_const_on_ball : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (x₀ : Euclid P) (r : ℝ) (α : Covector (Euclid P) (n + 1)) (φ : TestFormOn (univ : Set (Euclid P)) (n + 1)), 0 < r → X.boundary = 0 → X.support ⊆ ball x₀ r → (∀ x ∈ ball x₀ r, (φ : DifferentialForm (Euclid P) (n + 1)) x = α) → X φ = 0 := by
  intro VO P n X x₀ r α φ hr hbd hspt hφ
  -- Step 1: the cut-off `ζ`, equal to `1` on `B̄_r(x₀)`
  let ζ : ContDiffBump x₀ := ⟨r, r + 1, hr, by linarith⟩
  -- Step 2: the affine primitive `ψ` of `α`
  let ψ : DifferentialForm (Euclid P) n := fun y => ((n : ℝ) + 1)⁻¹ • α.curryLeft (y - x₀)
  have hψ : IsSmoothForm ψ :=
    (α.curryLeft.contDiff.comp (contDiff_id.sub contDiff_const)).const_smul _
  -- Step 3: the compactly supported primitive `η = ζψ`
  let g : DifferentialForm (Euclid P) n := fun y => ζ y • ψ y
  have hg : IsSmoothForm g := ζ.contDiff.smul hψ
  have hgc : HasCompactSupport g := ζ.hasCompactSupport.smul_right
  let η : TestFormOn (univ : Set (Euclid P)) n := ⟨g, ⟨hg, hgc⟩, subset_univ _⟩
  -- Step 4: `X(dη) = ∂X(η) = 0`
  have h0 : X (exteriorDerivativeTestOn univ n η) = 0 := by
    have h := congrArg (fun T : GeometricCurrentOn (univ : Set (Euclid P)) n => T η) hbd
    simpa using h
  -- Step 5: `φ = dη` on `B_r(x₀)`, since `η = ψ` near each point of the ball
  have heq : EqOn (φ : DifferentialForm (Euclid P) (n + 1))
      ((exteriorDerivativeTestOn univ n η : TestFormOn (univ : Set (Euclid P)) (n + 1)) :
        DifferentialForm (Euclid P) (n + 1)) (ball x₀ r) := by
    intro y hy
    rw [hφ y hy]
    change α = extDeriv g y
    have hev : g =ᶠ[𝓝 y] ψ := by
      filter_upwards [isOpen_ball.mem_nhds hy] with z hz
      simp [g, ζ.one_of_mem_closedBall (ball_subset_closedBall hz)]
    rw [hev.extDeriv_eq, Submission.cbrld_cone_extDeriv_affine_contraction P n α x₀ y]
  -- Step 6: localization to the open ball containing `spt X`
  rw [Submission.cbrld_cone_eval_eq_of_eqOn_open VO P (n + 1) univ (ball x₀ r) X φ _ isOpen_ball
    hspt heq, h0]
/-- A small scale below the lower density (Simon Ch. 6, 8.2 (2), with the lower density in place of
`Θ^{*n}`): `ωₙ > 0`, and if `liminf_{r ↓ 0} μ(B_r(x₁)) / (ωₙ rⁿ) < η₀`, then for every `δ > 0` there
is `s ∈ (0, δ)` with `μ(B_s(x₁)) < η₀ ωₙ sⁿ`.  The ratio is frequently below `η₀` along `r ↓ 0`;
clearing the nonzero, finite denominator `ωₙ sⁿ` at such an `s ∈ (0, δ)` gives the bound, and forces
`η₀ ≥ 0`. -/
theorem Submission.cbrldlf_exists_small_scale_of_lower_density : ∀ n : ℕ, 0 < (unitBallVolume n).toReal ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (η₀ δ : ℝ), 0 < δ → liminf (fun r : ℝ => μ (ball x₁ r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) < ENNReal.ofReal η₀ → ∃ s : ℝ, 0 < s ∧ s < δ ∧ μ (ball x₁ s) < ENNReal.ofReal (η₀ * (unitBallVolume n).toReal * s ^ n) := by
  intro n
  -- `ωₙ = volume (ball 0 1)` is positive (Haar measure on a nonempty open set) and finite.
  have hω₀ : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨ENNReal.toReal_pos hω₀ hωt, fun P μ x₁ η₀ δ hδ hlim => ?_⟩
  -- The ratio is frequently below `η₀`, and eventually `r ∈ (0, δ)`.
  obtain ⟨s, hs, hs₀, hsδ⟩ := ((frequently_lt_of_liminf_lt (by isBoundedDefault) hlim).and_eventually
    (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨s, hs₀, hsδ, ?_⟩
  -- Clear the denominator `ωₙ sⁿ`, which is nonzero and finite.
  rw [ENNReal.div_lt_iff (Or.inl (mul_ne_zero hω₀ (ENNReal.ofReal_pos.2 (pow_pos hs₀ n)).ne'))
    (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))] at hs
  -- `η₀ ≥ 0`, since otherwise the bound would be `μ (ball x₁ s) < 0`.
  have hη₀ : 0 ≤ η₀ := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_le.1 h).le, zero_mul] at hs
    exact ENNReal.not_lt_zero hs
  rwa [ENNReal.ofReal_mul (mul_nonneg hη₀ ENNReal.toReal_nonneg), ENNReal.ofReal_mul hη₀,
    ENNReal.ofReal_toReal hωt, mul_assoc]
/-- **Simon Ch. 6, 8.2 (3)–(4)** (constants of the isoperimetric filling, corrected), with
`p = m + 1` and `n = m + 2`: for `c ≥ 1` there is `a > 0` such that `0 ≤ F ≤ (a s)ⁿ` and
`0 ≤ M ≤ 2 n a F^{(n-1)/n}` imply `c (2cM)^{1/p} M ≤ F / 2` and `(2cM)^{1/p} ≤ s`.  Take
`K₀ = c (2c)^{1/p} (2n)^{n/p}`, `t = min {1 / (2K₀)^{m+1}, 1 / (4cn)}` and `a = t^{1/n}`, so
`a^{m+2} = t`. -/
theorem Submission.cbrldlf_exists_filling_constant : ∀ (m : ℕ) (c : ℝ), 1 ≤ c → ∃ a : ℝ, 0 < a ∧ ∀ (s F M : ℝ), 0 ≤ s → 0 ≤ F → F ≤ (a * s) ^ (m + 1 + 1) → 0 ≤ M → M ≤ 2 * ((m + 1 + 1 : ℕ) : ℝ) * a * F ^ ((((m + 1 + 1 : ℕ) : ℝ) - 1) / ((m + 1 + 1 : ℕ) : ℝ)) → c * (2 * c * M) ^ ((1 : ℝ) / (m + 1)) * M ≤ F / 2 ∧ (2 * c * M) ^ ((1 : ℝ) / (m + 1)) ≤ s := by
  intro m c hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  -- `p = m + 1` and `n = m + 2 = p + 1`
  have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn_eq : ((m + 1 + 1 : ℕ) : ℝ) = ((m : ℝ) + 1) + 1 := by push_cast; ring
  have hn : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by rw [hn_eq]; linarith
  have hpinv : (1 : ℝ) / ((m : ℝ) + 1) = (((m + 1 : ℕ) : ℝ))⁻¹ := by push_cast; rw [one_div]
  set p : ℝ := (m : ℝ) + 1 with hp_def
  set n : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hn_def
  -- Step 1: the constants `K₀ > 0`, `t > 0` and `a = t^{1/n} > 0`, with `a^{m+2} = t`
  set K₀ : ℝ := c * (2 * c) ^ (1 / p) * (2 * n) ^ (n / p) with hK₀_def
  have hK₀ : 0 < K₀ :=
    mul_pos (mul_pos hc0 (Real.rpow_pos_of_pos (by positivity) _))
      (Real.rpow_pos_of_pos (by positivity) _)
  set t : ℝ := min (1 / (2 * K₀) ^ (m + 1)) (1 / (4 * c * n)) with ht_def
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  set a : ℝ := t ^ (1 / n) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos ht _
  have ha_pow : a ^ (m + 1 + 1) = t := by
    rw [ha_def, hn_def, one_div]
    exact Real.rpow_inv_natCast_pow ht.le (by omega)
  -- Step 2 (i): `t^{1/p} ≤ ((1/(2K₀))^{m+1})^{1/(m+1)} = 1/(2K₀)`
  have hi : t ^ (1 / p) ≤ 1 / (2 * K₀) := by
    have h1 : t ≤ (1 / (2 * K₀)) ^ (m + 1) := by
      rw [one_div_pow]; exact min_le_left _ _
    have h2 : t ^ (1 / p) ≤ ((1 / (2 * K₀)) ^ (m + 1)) ^ (1 / p) :=
      Real.rpow_le_rpow ht.le h1 (by positivity)
    have h3 : ((1 / (2 * K₀)) ^ (m + 1)) ^ (1 / p) = 1 / (2 * K₀) := by
      rw [hpinv]
      exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    rw [h3] at h2
    exact h2
  -- Step 2 (ii): `t ≤ 1/(4cn)`
  have hii : t ≤ 1 / (4 * c * n) := min_le_right _ _
  refine ⟨a, ha, ?_⟩
  -- Step 3: `M ≤ b := 2 n a F^{p/n}`, since `(n - 1)/n = p/n`
  intro s F M hs hF hFas hM hMb
  have hexp : (n - 1) / n = p / n := by rw [hn_eq]; ring
  rw [hexp] at hMb
  set b : ℝ := 2 * n * a * F ^ (p / n) with hb_def
  have hb : 0 ≤ b := by positivity
  constructor
  · -- Step 4: `c (2cM)^{1/p} M = c (2c)^{1/p} M^{n/p}`, as `n/p = 1/p + 1`
    have h4 : c * (2 * c * M) ^ (1 / p) * M = c * (2 * c) ^ (1 / p) * M ^ (n / p) := by
      rw [Real.mul_rpow (by positivity) hM]
      have e : n / p = 1 / p + 1 := by rw [hn_eq]; field_simp; ring
      rw [e, Real.rpow_add' hM (by positivity), Real.rpow_one]
      ring
    -- Step 5: `M^{n/p} ≤ b^{n/p}`
    have h5 : M ^ (n / p) ≤ b ^ (n / p) := Real.rpow_le_rpow hM hMb (by positivity)
    -- Step 6: `b^{n/p} = (2n)^{n/p} t^{1/p} F`
    have h6 : b ^ (n / p) = (2 * n) ^ (n / p) * t ^ (1 / p) * F := by
      rw [hb_def, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul hF, ha_def, ← Real.rpow_mul ht.le]
      have e1 : p / n * (n / p) = 1 := by field_simp
      have e2 : 1 / n * (n / p) = 1 / p := by field_simp
      rw [e1, e2, Real.rpow_one]
    -- Step 7: `c (2cM)^{1/p} M ≤ K₀ t^{1/p} F ≤ F / 2` by (i)
    calc c * (2 * c * M) ^ (1 / p) * M = c * (2 * c) ^ (1 / p) * M ^ (n / p) := h4
      _ ≤ c * (2 * c) ^ (1 / p) * b ^ (n / p) := by gcongr
      _ = K₀ * t ^ (1 / p) * F := by rw [h6, hK₀_def]; ring
      _ ≤ K₀ * (1 / (2 * K₀)) * F := by gcongr
      _ = F / 2 := by field_simp
  · -- Step 8: `F^{p/n} ≤ ((a s)^{m+2})^{p/n} = (a s)^{m+1}`
    have h8 : F ^ (p / n) ≤ (a * s) ^ (m + 1) := by
      have h := Real.rpow_le_rpow hF hFas (by positivity : (0 : ℝ) ≤ p / n)
      have e : ((a * s) ^ (m + 1 + 1)) ^ (p / n) = (a * s) ^ (m + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have e' : ((m + 1 + 1 : ℕ) : ℝ) * (p / n) = ((m + 1 : ℕ) : ℝ) := by
          rw [← hn_def]; field_simp; rw [hp_def]; push_cast; ring
        rw [e', Real.rpow_natCast]
      rw [e] at h
      exact h
    -- Step 9: `2cM ≤ 4cn a^{m+2} s^{m+1} = 4cn t s^{m+1} ≤ s^{m+1}` by (ii)
    have h9 : 2 * c * M ≤ s ^ (m + 1) := by
      calc 2 * c * M ≤ 2 * c * (2 * n * a * F ^ (p / n)) := by gcongr
        _ ≤ 2 * c * (2 * n * a * (a * s) ^ (m + 1)) := by gcongr
        _ = 4 * c * n * a ^ (m + 1 + 1) * s ^ (m + 1) := by ring
        _ = 4 * c * n * t * s ^ (m + 1) := by rw [ha_pow]
        _ ≤ 4 * c * n * (1 / (4 * c * n)) * s ^ (m + 1) := by gcongr
        _ = s ^ (m + 1) := by field_simp
    -- Step 10: `(2cM)^{1/p} ≤ (s^{m+1})^{1/(m+1)} = s`
    have h10 := Real.rpow_le_rpow (by positivity) h9 (by positivity : (0 : ℝ) ≤ 1 / p)
    have e : (s ^ (m + 1)) ^ (1 / p) = s := by
      rw [hpinv]; exact Real.pow_rpow_inv_natCast hs (by omega)
    rw [e] at h10
    exact h10
/-- **Simon Ch. 6, proof of 8.2, (1)–(2)** (slices 4.6–4.9 by `f = |· − x₁|`, `Lip f = 1`): for a
cycle `C`, represent `∂C = 0` by the zero measure.  (SL) gives `A_ρ = C⌞B_ρ(x₁)` and `B_ρ = 0`,
`∂A_ρ` vanishes off `∂B_ρ(x₁)` (4.8) and `M(∂A_ρ) ≤ liminf_{h↓0} h⁻¹μ{ρ − h < |x − x₁| < ρ}` (4.9);
(ISP) makes `∂A_ρ` integer multiplicity for `ρ` outside a Lebesgue-null set. -/
theorem Submission.cbrld_sphere_slice_isIntegerMultiplicity : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (x₁ : Euclid P), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∃ N : Set ℝ, volume N = 0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ∉ N → ∃ A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in ball x₁ ρ, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ IsIntegerMultiplicity A.boundary ∧ A.boundary.support ⊆ sphere x₁ ρ ∧ A.boundary.mass ≤ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) := by
  intro hSL P d C μ ξ x₁ hCb hμ hξm hξb hC hISP
  -- step 1: `∂C = 0` is represented by the zero measure and the zero field of `d`-vectors
  have hμ0 : ∀ K : Set (Euclid P), IsCompact K → (0 : Measure (Euclid P)) K < ∞ :=
    fun K _ => by simp
  have hξ0m : AEStronglyMeasurable (0 : Euclid P → MultiVector P d) (0 : Measure (Euclid P)) :=
    aestronglyMeasurable_zero_measure _
  have hξ0b : ∀ᵐ x ∂(0 : Measure (Euclid P)), ∀ α : Covector (Euclid P) d,
      |(0 : Euclid P → MultiVector P d) x α| ≤ covectorEuclideanNorm α := by
    simp [ae_zero]
  have hCb0 : ∀ η : TestFormOn (univ : Set (Euclid P)) d,
      C.boundary η = ∫ x, (0 : Euclid P → MultiVector P d) x
        ((η : DifferentialForm (Euclid P) d) x) ∂(0 : Measure (Euclid P)) := by
    intro η
    rw [hCb, integral_zero_measure]
    rfl
  -- the slicing function `f = |· − x₁|` is `1`-Lipschitz
  have hf : LipschitzWith 1 (fun x : Euclid P => dist x x₁) := LipschitzWith.dist_left x₁
  -- step 3: (SL) for `C`, `f` and `L = 1`
  obtain ⟨A, B, hA, hB, hAB, hmass, -⟩ := hSL P d univ C μ 0 ξ 0 (fun x => dist x x₁) 1
    isOpen_univ (fun K hK _ => hμ K hK) (fun K hK _ => hμ0 K hK) hξm hξ0m hξb hξ0b hC hCb0 hf
  -- step 2: the exceptional set of (ISP) is Lebesgue-null
  have hISP' := hISP μ 0 ξ 0 hμ hμ0 hξm hξ0m hξb hξ0b hC hCb0 (fun x => dist x x₁) 1 hf
  refine ⟨_, ae_iff.mp hISP', fun ρ _ hρN => ?_⟩
  simp only [Set.mem_ofPred_eq, not_not] at hρN
  -- step 4: `B_ρ = 0`, so `∂A_ρ − B_ρ = ∂A_ρ`
  have hB0 : ∀ η, B ρ η = 0 := by
    intro η
    rw [hB ρ η, Measure.restrict_zero, integral_zero_measure]
  have hsub : (A ρ).boundary - B ρ = (A ρ).boundary := by
    ext η
    show (A ρ).boundary η - B ρ η = (A ρ).boundary η
    rw [hB0, sub_zero]
  refine ⟨A ρ, fun ω => hA ρ ω, ?_, ?_, ?_⟩
  · -- step 5: integer multiplicity
    rw [← hsub]
    exact hρN (A ρ) (B ρ) (hA ρ) (hB ρ)
  · -- step 6: `∂A_ρ` vanishes on a ball around every point off `∂B_ρ(x₁)`
    intro y hy
    by_contra hy'
    rw [Metric.mem_sphere] at hy'
    have hr : 0 < |dist y x₁ - ρ| / 2 := half_pos (abs_pos.mpr (sub_ne_zero.mpr hy'))
    apply hy.2
    refine Set.mem_sUnion_of_mem (mem_ball_self hr) ⟨isOpen_ball, ?_, subset_univ _, ?_⟩
    · exact (isCompact_closedBall y _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · intro η hη
      rw [hAB ρ η ?_, hB0]
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      have h1 : dist z y < |dist y x₁ - ρ| / 2 := hη hz
      have h2 : dist z x₁ = ρ := hz'
      have h3 := abs_dist_sub_le z y x₁
      rw [h2, abs_sub_comm] at h3
      linarith
  · -- step 7: the mass bound with `W = ℝᴾ`
    have h := hmass univ ρ isOpen_univ
    rw [hsub] at h
    simp only [ENNReal.coe_one, one_mul, univ_inter] at h
    exact h
/-- **Good radius** (Simon 7.2.4, choice of the slicing level; the factor-2 averaging of Ch. 2,
6.7(1)).  If `ρ < ρ'`, `μ(B̄_{ρ'}(y)) < ∞`, `∫ g dL¹ ≤ I` and `p` holds `L¹`-a.e., then some
`t ∈ (ρ, ρ')` has `p t`, `μ(∂B_t(y)) = 0` and `g t ≤ (2 / (ρ' - ρ)) I`: the levels failing `p` and
the (countably many) levels whose sphere charges the finite measure `μ⌞B̄_{ρ'}(y)` are `L¹`-null,
and by Markov's inequality the levels with `g t > (2 / (ρ' - ρ)) I` have `L¹`-measure at most
`(ρ' - ρ) / 2 < L¹((ρ, ρ'))`. -/
theorem Submission.dor_lmb_glc_good_radius : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (ρ ρ' : ℝ) (g : ℝ → ℝ≥0∞) (I : ℝ≥0∞) (p : ℝ → Prop), ρ < ρ' → μ (closedBall y ρ') ≠ ∞ → AEMeasurable g → ∫⁻ t, g t ≤ I → (∀ᵐ t, p t) → ∃ t : ℝ, ρ < t ∧ t < ρ' ∧ p t ∧ μ (sphere y t) = 0 ∧ g t ≤ ENNReal.ofReal (2 / (ρ' - ρ)) * I := by
  intro P μ y ρ ρ' g I p hρ hμ hg hI hp
  have hδ : 0 < ρ' - ρ := sub_pos.mpr hρ
  set c := ENNReal.ofReal (2 / (ρ' - ρ)) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ = ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rw [hc_def, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  -- `N₁`: the exceptional set of `p` is Lebesgue-null
  have hN₁ : volume {t : ℝ | ¬ p t} = 0 := ae_iff.mp hp
  -- `N₂`: only countably many spheres charge the finite measure `μ⌞B̄_{ρ'}(y)`
  have hfin : IsFiniteMeasure (μ.restrict (closedBall y ρ')) := isFiniteMeasure_restrict.mpr hμ
  have hcount : {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun s => isClosed_sphere.measurableSet)
      (fun s s' hss' => Set.disjoint_left.mpr fun x hx hx' =>
        hss' ((mem_sphere.mp hx).symm.trans (mem_sphere.mp hx')))
  have hN₂ : volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} = 0 :=
    hcount.measure_zero volume
  -- `N₃`: Markov's inequality gives `L¹(N₃) ≤ (ρ' - ρ) / 2`
  have hN₃ : volume {t : ℝ | c * I < g t} ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rcases eq_or_ne I 0 with h0 | h0
    · have hzero : ∫⁻ t, g t = 0 := le_antisymm (hI.trans h0.le) zero_le
      have hae : g =ᵐ[volume] 0 := (lintegral_eq_zero_iff' hg).mp hzero
      have hnull : volume {t : ℝ | c * I < g t} = 0 := by
        refine measure_mono_null (fun t ht => ?_) (ae_iff.mp hae)
        simp only [Set.mem_ofPred_eq, h0, mul_zero] at ht ⊢
        exact ht.ne'
      rw [hnull]
      exact zero_le
    rcases eq_or_ne I ∞ with htop | htop
    · have hempty : {t : ℝ | c * I < g t} = ∅ := by
        ext t
        simp [htop, ENNReal.mul_top hc0]
      rw [hempty, measure_empty]
      exact zero_le
    have hε0 : c * I ≠ 0 := mul_ne_zero hc0 h0
    have hεtop : c * I ≠ ∞ := ENNReal.mul_ne_top hctop htop
    calc volume {t : ℝ | c * I < g t} ≤ volume {t : ℝ | c * I ≤ g t} :=
          measure_mono fun t (ht : c * I < g t) => show c * I ≤ g t from ht.le
      _ ≤ (∫⁻ t, g t) / (c * I) := meas_ge_le_lintegral_div hg hε0 hεtop
      _ ≤ I / (c * I) := ENNReal.div_le_div_right hI _
      _ = c⁻¹ := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, mul_one]
      _ = ENNReal.ofReal ((ρ' - ρ) / 2) := hcinv
  -- covering: if no good `t` existed, then `(ρ, ρ') ⊆ N₁ ∪ N₂ ∪ N₃`
  by_contra hcon
  have hcover : Ioo ρ ρ' ⊆ {t : ℝ | ¬ p t} ∪
      {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪ {t : ℝ | c * I < g t} := by
    intro t ht
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, nonpos_iff_eq_zero]
      at hnot
    obtain ⟨⟨hpt, hνt⟩, hgt⟩ := hnot
    have hμt : μ (sphere y t) = 0 := by
      rwa [Measure.restrict_apply isClosed_sphere.measurableSet, Set.inter_eq_left.mpr
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall ht.2.le))] at hνt
    exact hcon ⟨t, ht.1, ht.2, hpt, hμt, hgt⟩
  have hle : ENNReal.ofReal (ρ' - ρ) ≤ ENNReal.ofReal ((ρ' - ρ) / 2) :=
    calc ENNReal.ofReal (ρ' - ρ) = volume (Ioo ρ ρ') := Real.volume_Ioo.symm
      _ ≤ volume ({t : ℝ | ¬ p t} ∪ {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪
          {t : ℝ | c * I < g t}) := measure_mono hcover
      _ ≤ volume {t : ℝ | ¬ p t} + volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} +
          volume {t : ℝ | c * I < g t} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
        rw [hN₁, hN₂, zero_add, zero_add]
        exact hN₃
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith
/-- **Integrability and zeroth-order bound of the pairing `∫_E ⟨ω, ξ⟩ dμ`** (Simon 6.2.4–6.2.5,
`μ⌞E ∧ ξ` as a current; used for restrictions of currents in the slicing argument of 7.2.4).
If `|⟨α, ξ(x)⟩| ≤ |α|` for every `n`-covector `α` and `μ`-a.e. `x`, and the continuous form
`ω` vanishes off a measurable `K` with `μ(K) < ∞` and `|ω| ≤ ε`, then `|ξ(ω)| ≤ ε 1_K`
`μ`-a.e., so `ξ(ω)` is `μ⌞E`-integrable and `|∫_E ξ(ω) dμ| ≤ ε μ(K ∩ E) ≤ ε μ(K)`. -/
theorem Submission.cmcs_rc_pairing_integrable_abs_le : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E K : Set (Euclid P)) (ω : DifferentialForm (Euclid P) n) (ε : ℝ), AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Continuous ω → MeasurableSet K → μ K < ∞ → (∀ x, x ∉ K → ω x = 0) → (∀ x, covectorEuclideanNorm (ω x) ≤ ε) → Integrable (fun x => ξ x (ω x)) (μ.restrict E) ∧ |∫ x in E, ξ x (ω x) ∂μ| ≤ ε * (μ K).toReal := by
  intro P n μ ξ E K ω ε hξm hξb hω hK hμK hzero hε
  -- Step 1: `ε ≥ 0`
  have hε0 : 0 ≤ ε := (covectorEuclideanNorm_nonneg _).trans (hε 0)
  -- Step 2: `F x = ξ x (ω x)` is a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => ξ x (ω x)) μ :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n)
      (F := ℝ)).continuous.comp_aestronglyMeasurable₂ (g := fun Λ α => Λ α) hξm
      hω.aestronglyMeasurable
  -- Step 3: `‖F x‖ ≤ K.indicator ε x` a.e.
  have hbd : ∀ᵐ x ∂μ, ‖ξ x (ω x)‖ ≤ K.indicator (fun _ => ε) x := by
    filter_upwards [hξb] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, Real.norm_eq_abs]
      exact (hx (ω x)).trans (hε x)
    · rw [indicator_of_notMem hxK, hzero x hxK, map_zero, norm_zero]
  -- Step 4: the dominating function is integrable
  have hg : Integrable (K.indicator (fun _ => ε)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  -- Step 5: integrability of `F`, then on `μ.restrict E`
  have hint : Integrable (fun x => ξ x (ω x)) μ := hg.mono' hmeas hbd
  refine ⟨hint.restrict, ?_⟩
  -- Step 6: `‖∫_E F‖ ≤ ∫_E g = ν.real K * ε`
  have h1 : ‖∫ x in E, ξ x (ω x) ∂μ‖ ≤ ∫ x in E, K.indicator (fun _ => ε) x ∂μ :=
    norm_integral_le_of_norm_le hg.restrict (ae_restrict_of_ae hbd)
  rw [integral_indicator_const ε hK, smul_eq_mul] at h1
  -- Step 7: `ν K = μ (K ∩ E) ≤ μ K`, multiply by `ε ≥ 0`
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hε0
  rw [measureReal_def, Measure.restrict_apply hK]
  exact ENNReal.toReal_mono hμK.ne (measure_mono inter_subset_left)
/-- **A linear functional on `𝒟ⁿ(U)` with zeroth-order bounds is a current** (Simon 6.2.1; used
for the restricted currents `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` in the slicing argument behind 7.2.4).  Suppose
every compact `K ⊆ U` has a `c` with `|L(ω)| ≤ c M` whenever `spt ω ⊆ K` and `‖ω(x)‖ ≤ M` for all
`x`.  Take `S = L`.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K ⊆ U`, the order-`0`
part of the uniform convergence on `K` gives `‖ωⱼ(x)‖ ≤ η` for large `j`.  Off `K` this holds
because `ωⱼ(x) = 0`.  With `η = δ / (|c| + 1)`, `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`. -/
theorem Submission.cmcs_rc_order_zero_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ c : ℝ, ∀ (ω : TestFormOn U n) (M : ℝ), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) → |L ω| ≤ c * M) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = L ω := by
  intro P n U L hL
  -- Step 1: `S = ⟨L, h⟩`, so `S ω = L ω` and only `L(ωⱼ) → 0` for `ωⱼ → 0` remains
  refine ⟨⟨L, fun ωs hconv => ?_⟩, fun ω => rfl⟩
  -- Step 2: the common compact support `K ⊆ U` and the constant `c` for `K`
  obtain ⟨K, hK, hKU, hsupp, -, hunif⟩ := hconv
  obtain ⟨c, hc⟩ := hL K hK hKU
  -- Step 3: order-`0` uniform convergence on `K`, to the zero form
  have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
  have hz : ∀ x, iteratedFDeriv ℝ 0
      ((0 : TestFormOn U n) : DifferentialForm (Euclid P) n) x = 0 := by
    intro x
    rw [← norm_eq_zero, norm_iteratedFDeriv_zero]
    simp
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hη : 0 < δ / (|c| + 1) := div_pos hδ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 _ hη)
  refine ⟨N, fun j hj => ?_⟩
  -- Steps 3–4: `‖ωⱼ(x)‖ ≤ η` on `K` by uniform convergence, and off `K` since `ωⱼ(x) = 0`
  have hsmall : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ δ / (|c| + 1) := by
    intro x
    by_cases hx : x ∈ K
    · have h := hN j hj x hx
      rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
      exact h.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
      exact hη.le
  -- Step 5: `|L(ωⱼ)| ≤ c η ≤ |c| η < δ`
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ c * (δ / (|c| + 1)) := hc (ωs j) _ (hsupp j) hsmall
    _ ≤ |c| * (δ / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hη.le
    _ < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg c]

/-- **Restriction of a measure-represented current** (Simon Ch. 6, 2.9:
`T ⌞ A(ω) = ∫_A ⟨ω, T⃗⟩ dμ_T`), for an arbitrary pair `(μ, ξ)` and an arbitrary set `E`: if `μ` is
finite on compact subsets of `U` and `ξ` is `μ`-a.e. strongly measurable with
`|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for `μ`-a.e. `x`, then
`ω ↦ ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` is a current in `U`.  By `rsd_mw_tfa_norm_props`, `|α| ≤ C ‖α‖`.
For `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, `cmcs_rc_pairing_integrable_abs_le` then
gives integrability on `μ ⌞ E` and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`.  The functional is linear
(`integral_add`, `integral_const_mul`), and `cmcs_rc_order_zero_current` turns the order-zero
bound into Simon's sequential continuity. -/
theorem Submission.cmcs_restrict_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (E : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → ∃ S : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, S ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
  intro P n U μ ξ E hμK hξm hξb
  -- Step 1: `|α| ≤ C ‖α‖` for every `n`-covector `α`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Steps 2 and 4: for `ω` supported in a compact `K ⊆ U` with `‖ω‖ ≤ M`, the pairing is
  -- `μ ⌞ E`-integrable and `|∫_E ⟨ω, ξ⟩ dμ| ≤ C M μ(K)`
  have hpair : ∀ (ω : TestFormOn U n) (K : Set (Euclid P)) (M : ℝ), IsCompact K → K ⊆ U →
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K →
      (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ M) →
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) ∧
        |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| ≤ C * M * (μ K).toReal := by
    intro ω K M hK hKU hsupp hM
    exact Submission.cmcs_rc_pairing_integrable_abs_le P n μ ξ E K
      (ω : DifferentialForm (Euclid P) n) (C * M) hξm hξb ω.property.1.1.continuous
      hK.measurableSet (hμK K hK hKU)
      (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hsupp h))
      (fun x => (hC _).trans (mul_le_mul_of_nonneg_left (hM x) hC0))
  -- Step 2: every test form is admissible, with `K = tsupport ω` and `M = sup ‖ω‖ < ∞`
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) (μ.restrict E) := by
    intro ω
    obtain ⟨M, hM⟩ := ω.property.1.1.continuous.bounded_above_of_compact_support ω.property.1.2
    exact (hpair ω _ M ω.property.1.2 ω.property.2 subset_rfl hM).1
  -- Step 3: `ω ↦ ∫_E ⟨ω, ξ⟩ dμ` is linear
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ
      map_add' := fun ω₁ ω₂ => by
        simp only [Submodule.coe_add, Pi.add_apply, map_add]
        exact integral_add (hint ω₁) (hint ω₂)
      map_smul' := fun c ω => by
        simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul c _ }
  -- Steps 4 and 5: the order-zero bound with `c_K = C μ(K)` makes `L` a current
  obtain ⟨S, hS⟩ := Submission.cmcs_rc_order_zero_current P n U L fun K hK hKU =>
    ⟨C * (μ K).toReal, fun ω M hsupp hM => by
      calc |L ω| = |∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ| := rfl
        _ ≤ C * M * (μ K).toReal := (hpair ω K M hK hKU hsupp hM).2
        _ = C * (μ K).toReal * M := by ring⟩
  exact ⟨S, hS⟩
/-- **Level splitting of a test form** (a step in the proof of Simon Ch. 6, 4.8,
`spt ⟨T, f, t₊⟩ ⊆ spt T ∩ {f = t}`).  If `tsupport η` misses the level set `{f = t}` of a
continuous `f`, then `η = η₁ + η₂` with test forms `η₁ = χ η` supported in `{f < t}` and
`η₂ = (1 - χ) η` supported in `{t < f}`.  Here `χ` is a smooth Urysohn function equal to `1` on
`K₋ = tsupport η ∩ {f ≤ t}` and to `0` on `K₊ = tsupport η ∩ {t ≤ f}`; these closed sets are
disjoint, with `K₋ ⊆ {f < t}` and `K₊ ⊆ {t < f}`, because `tsupport η` misses `{f = t}`. -/
theorem Submission.cmcs_ss_testForm_level_split : ∀ (P n : ℕ) (U : Set (Euclid P)) (f : Euclid P → ℝ) (t : ℝ) (η : TestFormOn U n), Continuous f → Disjoint (tsupport (η : DifferentialForm (Euclid P) n)) {x | f x = t} → ∃ η₁ η₂ : TestFormOn U n, η = η₁ + η₂ ∧ tsupport (η₁ : DifferentialForm (Euclid P) n) ⊆ {x | f x < t} ∧ tsupport (η₂ : DifferentialForm (Euclid P) n) ⊆ {x | t < f x} := by
  intro P n U f t η hf hη
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := η.property
  set e : DifferentialForm (Euclid P) n := (η : DifferentialForm (Euclid P) n)
  -- the closed halves `K₋ = K ∩ {f ≤ t}` and `K₊ = K ∩ {t ≤ f}` of `K = tsupport η` are
  -- disjoint, since `K` misses `{f = t}`
  have hKl : IsClosed (tsupport e ∩ {x | f x ≤ t}) :=
    (isClosed_tsupport e).inter (isClosed_le hf continuous_const)
  have hKu : IsClosed (tsupport e ∩ {x | t ≤ f x}) :=
    (isClosed_tsupport e).inter (isClosed_le continuous_const hf)
  have hd : Disjoint (tsupport e ∩ {x | t ≤ f x}) (tsupport e ∩ {x | f x ≤ t}) :=
    Set.disjoint_left.2 fun x hxu hxl => Set.disjoint_left.1 hη hxu.1 (le_antisymm hxl.2 hxu.2)
  -- a smooth `χ` with `χ = 0` on `K₊` and `χ = 1` on `K₋`
  obtain ⟨χ, hχ, -, hχ₀, hχ₁⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := (⊤ : ℕ∞)) hKu hKl hd
  -- `χ η` and `(1 - χ) η` are test forms in `U`, with sum `η`
  have h₁ : (fun x => χ x • e x) ∈ TestFormOn U n :=
    ⟨⟨hχ.smul hsmooth, hcpt.smul_left (f := χ)⟩, (tsupport_smul_subset_right χ e).trans hU⟩
  have h₂ : (fun x => (1 - χ x) • e x) ∈ TestFormOn U n :=
    ⟨⟨(contDiff_const.sub hχ).smul hsmooth, hcpt.smul_left (f := fun x => 1 - χ x)⟩,
      (tsupport_smul_subset_right (fun x => 1 - χ x) e).trans hU⟩
  refine ⟨⟨_, h₁⟩, ⟨_, h₂⟩, Subtype.ext (funext fun x => ?_), ?_, ?_⟩
  · change e x = χ x • e x + (1 - χ x) • e x
    rw [← add_smul, add_sub_cancel, one_smul]
  · -- `support (χ η) ⊆ K₋`, a closed subset of `{f < t}`
    have hs : support (fun x => χ x • e x) ⊆ tsupport e ∩ {x | f x ≤ t} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show f x ≤ t from le_of_not_ge fun h => ?_⟩
      exact left_ne_zero_of_smul hx ((hχ₀ x).1 ⟨he, h⟩)
    exact (closure_minimal hs hKl).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h
  · -- `support ((1 - χ) η) ⊆ K₊`, a closed subset of `{t < f}`
    have hs : support (fun x => (1 - χ x) • e x) ⊆ tsupport e ∩ {x | t ≤ f x} := fun x hx => by
      have he : x ∈ tsupport e := subset_tsupport e (right_ne_zero_of_smul hx)
      refine ⟨he, show t ≤ f x from le_of_not_ge fun h => left_ne_zero_of_smul hx ?_⟩
      rw [(hχ₁ x).1 ⟨he, h⟩, sub_self]
    exact (closure_minimal hs hKu).trans fun x hx =>
      lt_of_le_of_ne hx.2 fun h => Set.disjoint_left.1 hη hx.1 h.symm
/-- Restriction commutes with the boundary on forms supported in the restricting set (Simon 6.4.6,
used for 4.8): let `T(ω) = ∫ ⟨ω, ξ⟩ dμ` and `∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`, and let `A = T⌞S`,
`B = (∂T)⌞S` be given by the same integrals over `S`.  Then `∂A(θ) = B(θ)` whenever
`spt θ ⊆ S`.  Off `S` both `θ` and `dθ` vanish (`spt dθ ⊆ spt θ`), so both integrals over `S`
are integrals over `ℝᴾ`, and `∂A(θ) = A(dθ) = T(dθ) = ∂T(θ) = B(θ)`. -/
theorem Submission.cmcs_ss_boundary_eq_of_tsupport_subset : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, tsupport (θ : DifferentialForm (Euclid P) k) ⊆ S → A.boundary θ = B θ := by
  intro P k U T μ μ' ξ ξ' S A B hT hbT hA hB θ hθ
  -- `θ` and `dθ` vanish off `S`, as `spt dθ ⊆ spt θ ⊆ S`
  have hθ0 : ∀ x, x ∉ S → (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hθ h)
  have hdθ0 : ∀ x, x ∉ S → exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h =>
      hx (hθ (tsupport_exteriorDerivative_subset _ h))
  -- so, `ξ x` and `ξ' x` being linear, both integrals over `S` are integrals over `ℝᴾ`
  have hAT : ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ =
      ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hdθ0 x hx, map_zero]
  have hBT : ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' =
      ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hθ0 x hx, map_zero]
  -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ = ∫ ⟨dθ, ξ⟩ dμ = T(dθ) = ∂T(θ) = ∫ ⟨θ, ξ'⟩ dμ'`
  -- `= ∫_S ⟨θ, ξ'⟩ dμ' = B(θ)`
  calc A.boundary θ = A (exteriorDerivativeTestOn U k θ) := GeometricCurrentOn.boundary_apply A θ
    _ = ∫ x in S, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hA _
    _ = ∫ x, ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) ∂μ := hAT
    _ = T (exteriorDerivativeTestOn U k θ) := (hT (exteriorDerivativeTestOn U k θ)).symm
    _ = T.boundary θ := (GeometricCurrentOn.boundary_apply T θ).symm
    _ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hbT θ
    _ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ' := hBT.symm
    _ = B θ := (hB θ).symm
/-- Simon Ch. 6, 4.6–4.8 (support of the slice `∂(T⌞S) − (∂T)⌞S`, `S = {f < t}`): if
`A(ω) = ∫_S ⟨ω, ξ⟩ dμ` and `B(θ) = ∫_S ⟨θ, ξ'⟩ dμ'`, then `∂A(θ) = A(dθ) = 0` and `B(θ) = 0`
whenever `spt θ` misses `S`, because `θ` and `dθ` (`spt dθ ⊆ spt θ`) vanish on `S`. -/
theorem Submission.cmcs_ss_boundary_vanish_of_disjoint : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (S : Set (Euclid P)) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in S, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ θ : TestFormOn U k, Disjoint (tsupport (θ : DifferentialForm (Euclid P) k)) S → A.boundary θ = 0 ∧ B θ = 0 := by
  intro P k U μ μ' ξ ξ' S A B hA hB θ hθ
  -- `θ` vanishes on `S`, and so does `dθ`, as `tsupport dθ ⊆ tsupport θ`
  have hθS : ∀ x ∈ S, (θ : DifferentialForm (Euclid P) k) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (hθ.notMem_of_mem_right hx)
  have hdθS : ∀ x ∈ S, exteriorDerivative (θ : DifferentialForm (Euclid P) k) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun hx' =>
      hθ.notMem_of_mem_right hx (tsupport_exteriorDerivative_subset _ hx')
  refine ⟨?_, ?_⟩
  · -- `∂A(θ) = A(dθ) = ∫_S ⟨dθ, ξ⟩ dμ`
    rw [GeometricCurrentOn.boundary_apply, hA]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    change ξ x (exteriorDerivative (θ : DifferentialForm (Euclid P) k) x) = 0
    rw [hdθS x hx, map_zero]
  · rw [hB]
    exact setIntegral_eq_zero_of_forall_eq_zero fun x hx => by rw [hθS x hx, map_zero]

/-- **Simon Ch. 6, 4.8** (support of a slice): if `T = ξ μ` and `∂T = ξ' μ'` in `U`,
`A = T ⌞ {f < t}` and `B = (∂T) ⌞ {f < t}` (`f` continuous), then `∂A(η) = B(η)` for every
`η ∈ 𝒟ᵏ(U)` whose support misses the level set `{f = t}`; i.e. the slice `∂A − B` lives on
`{f = t}`.  Split `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {f > t}`
(`cmcs_ss_testForm_level_split`).  Below the level `∂A(η₁) = ∂T(η₁) = B(η₁)`
(`cmcs_ss_boundary_eq_of_tsupport_subset`); above it `∂A(η₂) = 0 = B(η₂)`
(`cmcs_ss_boundary_vanish_of_disjoint`), as `{f > t}` misses `{f < t}`.  Conclude by linearity
of `∂A` and `B`. -/
theorem Submission.cmcs_slice_support : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k), Continuous f → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ∀ η : TestFormOn U k, Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → A.boundary η = B η := by
  intro P k U T μ μ' ξ ξ' f t A B hf hT hbT hA hB η hη
  -- `η = η₁ + η₂` with `spt η₁ ⊆ {f < t}` and `spt η₂ ⊆ {t < f}`
  obtain ⟨η₁, η₂, rfl, h₁, h₂⟩ := Submission.cmcs_ss_testForm_level_split P k U f t η hf hη
  -- below the level: `∂A(η₁) = ∂T(η₁) = B(η₁)`
  have e₁ : A.boundary η₁ = B η₁ :=
    Submission.cmcs_ss_boundary_eq_of_tsupport_subset P k U T μ μ' ξ ξ' {x | f x < t} A B
      hT hbT hA hB η₁ h₁
  -- above the level: `∂A(η₂) = 0 = B(η₂)`, since `spt η₂ ⊆ {t < f}` misses `{f < t}`
  obtain ⟨e₂, e₂'⟩ := Submission.cmcs_ss_boundary_vanish_of_disjoint P k U μ μ' ξ ξ'
    {x | f x < t} A B hA hB η₂ (Set.disjoint_left.2 fun x hx hx' =>
      lt_asymm (show t < f x from h₂ hx) (show f x < t from hx'))
  -- `∂A` and `B` are linear
  rw [A.boundary.toCurrent.map_add, B.toCurrent.map_add, e₁, e₂, e₂']
/-- Integrability of the pairing `x ↦ ⟨ω(x), ξ(x)⟩`: if `μ` is finite on compact subsets of `U`,
`ξ` is `μ`-a.e. strongly measurable with `|⟨α, ξ(x)⟩| ≤ |α|` (Euclidean coefficient norm) for
`μ`-a.e. `x`, and `ω ∈ 𝒟ⁿ(U)`, then `x ↦ ⟨ω(x), ξ(x)⟩` is `μ`-integrable.  The coefficient norm
`|ω(x)|` is continuous with compact support, hence bounded by some `M`, so the pairing is
dominated by `M` times the indicator of `spt ω`, which is integrable as `μ(spt ω) < ∞`. -/
theorem Submission.cmcs_smp_pairing_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (ω : TestFormOn U n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) → Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) n) x)) μ := by
  intro P n U μ ξ ω hμ hξm hξ
  obtain ⟨w, ⟨hws, hwcs⟩, hwU⟩ := ω
  change Integrable (fun x => ξ x (w x)) μ
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous with compact support, hence bounded by some `M`
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  -- `(Λ, α) ↦ Λ α` is continuous, so the pairing is a.e. strongly measurable
  have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    isBoundedBilinearMap_apply.continuous
  have hmeas : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    hev.comp_aestronglyMeasurable₂ hξm hwc.aestronglyMeasurable
  -- domination by `M` times the indicator of `spt w`, integrable as `μ(spt w) < ∞`
  refine Integrable.mono' ((integrable_indicator_iff (isClosed_tsupport w).measurableSet).2
    (integrableOn_const (hμ _ hwcs hwU).ne)) hmeas ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs]
  by_cases hxK : x ∈ tsupport w
  · rw [indicator_of_mem hxK]
    exact (hx (w x)).trans ((Real.le_norm_self _).trans (hM x))
  · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK]
    simp
/-- **Dominated convergence for level cut-offs** (step 5 of the slice mass bound in the proof of
Simon 7.2.4, cut-offs `g_h` of the level set `{f < t}`).  If `F` is `μ`-integrable, `f` is
measurable and, for `0 < h < 1`, `g_h` is a.e. strongly measurable with `|g_h| ≤ C`, `g_h = 1` on
`{f ≤ t − h}` and `g_h = 0` on `{t ≤ f}`, then `∫ g_h F dμ → ∫_{f < t} F dμ` as `h → 0+`.
Along `𝓝[>] 0` eventually `0 < h < 1`, so `|g_h F| ≤ C|F|` (integrable); for each `x`,
`g_h(x)F(x)` is eventually `1_{f<t}(x)F(x)` (for `h < min (t − f x) 1` if `f x < t`, for all
`h ∈ (0, 1)` if `t ≤ f x`); dominated convergence along the countably generated `𝓝[>] 0`. -/
theorem Submission.cmcs_smp_cutoff_integral_tendsto : ∀ (P : ℕ) (μ : Measure (Euclid P)) (F f : Euclid P → ℝ) (t C : ℝ) (g : ℝ → Euclid P → ℝ), Integrable F μ → Measurable f → (∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) μ) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, |g h x| ≤ C) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, f x ≤ t - h → g h x = 1) → (∀ h : ℝ, 0 < h → h < 1 → ∀ x, t ≤ f x → g h x = 0) → Tendsto (fun h : ℝ => ∫ x, g h x * F x ∂μ) (𝓝[>] 0) (𝓝 (∫ x in {x | f x < t}, F x ∂μ)) := by
  intro P μ F f t C g hF hf hgm hgC hg1 hg0
  -- Step 2: eventually along `𝓝[>] 0`, `h ∈ (0, 1)`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- Step 1: `{f < t}` is measurable, so the limit is `∫ 1_{f<t} F dμ`
  have hs : MeasurableSet {x | f x < t} := measurableSet_lt hf measurable_const
  rw [← integral_indicator hs]
  -- Step 6: dominated convergence with the integrable bound `C‖F‖`
  refine tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖F x‖) ?_ ?_ ?_ ?_
  · -- Step 3: `g_h F` is a.e. strongly measurable for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    exact (hgm h hh.1 hh.2).mul hF.aestronglyMeasurable
  · -- Step 4: `|g_h F| ≤ C|F|` for `h ∈ (0, 1)`
    filter_upwards [hev] with h hh
    refine Eventually.of_forall fun x => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hgC h hh.1 hh.2 x) (norm_nonneg _)
  · exact hF.norm.const_mul C
  · -- Step 5: `g_h(x)F(x)` is eventually equal to `1_{f<t}(x)F(x)`
    refine Eventually.of_forall fun x => ?_
    by_cases hx : f x < t
    · rw [indicator_of_mem (show x ∈ {x | f x < t} from hx)]
      have hpos : 0 < min (t - f x) 1 := lt_min (by linarith) one_pos
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hpos] with h hh
      obtain ⟨h0, h1⟩ := hh
      have h1' : h < 1 := lt_of_lt_of_le h1 (min_le_right _ _)
      have h2 : h < t - f x := lt_of_lt_of_le h1 (min_le_left _ _)
      rw [hg1 h h0 h1' x (by linarith), one_mul]
    · rw [indicator_of_notMem (show x ∉ {x | f x < t} from hx)]
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with h hh
      rw [hg0 h hh.1 hh.2 x (not_lt.1 hx), zero_mul]
/-- **Simon Ch. 6, 4.9** (end of its proof, p. 158, where `b ↓ a` and then `ε ↓ 0`): if
`Φ(h) → z` as `h ↓ 0` and `|Φ(h)| ≤ L / (h (1 − h/2)) · v(h)` for `0 < h < 1`, then
`z ≤ L · liminf_{h ↓ 0} h⁻¹ v(h)` in `[0, ∞]`.  For `r > 1` eventually `(1 − h/2)⁻¹ < r`, so
`|z| = liminf |Φ(h)| ≤ r · L · liminf h⁻¹ v(h)`; then let `r ↓ 1`. -/
theorem Submission.cmcs_smp_liminf_bound : ∀ (L : NNReal) (z : ℝ) (Φ : ℝ → ℝ) (v : ℝ → ℝ≥0∞), Tendsto Φ (𝓝[>] 0) (𝓝 z) → (∀ h : ℝ, 0 < h → h < 1 → ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h) → ENNReal.ofReal z ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0) := by
  intro L z Φ v hΦ hb
  set X := (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * v h) (𝓝[>] 0)
  -- step 1: `(0, 1) ∈ 𝓝[>] 0`
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
  -- step 2: `ofReal |Φ h| → ofReal |z|`
  have hlimΦ : Tendsto (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) (𝓝 (ENNReal.ofReal |z|)) :=
    ENNReal.tendsto_ofReal hΦ.abs
  -- step 3: `ofReal z ≤ ofReal r * X` for every `r > 1`
  have key : ∀ r : ℝ, 1 < r → ENNReal.ofReal z ≤ ENNReal.ofReal r * X := by
    intro r hr
    -- 3a: `(1 - h / 2)⁻¹ → 1`, so eventually `(1 - h / 2)⁻¹ < r`
    have hcont : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝[>] 0) (𝓝 1) := by
      have : Tendsto (fun h : ℝ => (1 - h / 2)⁻¹) (𝓝 0) (𝓝 (1 - 0 / 2)⁻¹) :=
        (tendsto_const_nhds.sub (tendsto_id.div_const 2)).inv₀ (by norm_num)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hevr : ∀ᶠ h in 𝓝[>] (0 : ℝ), (1 - h / 2)⁻¹ < r := hcont.eventually (gt_mem_nhds hr)
    calc ENNReal.ofReal z ≤ ENNReal.ofReal |z| := ENNReal.ofReal_le_ofReal (le_abs_self z)
      _ = liminf (fun h => ENNReal.ofReal |Φ h|) (𝓝[>] 0) := hlimΦ.liminf_eq.symm
      _ ≤ liminf (fun h => ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)))
            (𝓝[>] 0) := by
          -- 3b, 3c: the eventual pointwise bound and monotonicity of `liminf`
          refine liminf_le_liminf ?_
          filter_upwards [hev, hevr] with h ⟨h0, h1⟩ hhr
          have h2 : 0 < 1 - h / 2 := by linarith
          have heq : (L : ℝ) / (h * (1 - h / 2)) = (1 - h / 2)⁻¹ * ((L : ℝ) * h⁻¹) := by
            field_simp
          calc ENNReal.ofReal |Φ h| ≤ ENNReal.ofReal ((L : ℝ) / (h * (1 - h / 2))) * v h :=
                hb h h0 h1
            _ = ENNReal.ofReal (1 - h / 2)⁻¹ * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                rw [heq, ENNReal.ofReal_mul (inv_nonneg.2 h2.le),
                  ENNReal.ofReal_mul L.coe_nonneg, ENNReal.ofReal_coe_nnreal]
                ring
            _ ≤ ENNReal.ofReal r * ((L : ℝ≥0∞) * (ENNReal.ofReal h⁻¹ * v h)) := by
                gcongr
      _ = ENNReal.ofReal r * X := by
          rw [ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
            ENNReal.liminf_const_mul_of_ne_top ENNReal.coe_ne_top]
  -- step 4: let `r ↓ 1`
  by_cases hXtop : X = ⊤
  · rw [hXtop]
    exact le_top
  · have htend : Tendsto (fun r : ℝ => ENNReal.ofReal r * X) (𝓝[>] 1)
        (𝓝 (ENNReal.ofReal 1 * X)) :=
      ENNReal.Tendsto.mul_const
        ((ENNReal.tendsto_ofReal tendsto_id).mono_left nhdsWithin_le_nhds) (Or.inr hXtop)
    simpa using ge_of_tendsto htend (eventually_nhdsWithin_of_forall fun r hr => key r hr)
/-- Strip estimate (Simon Ch. 6, 4.11: the bound for the right side `R` of 4.11): if `‖Dg‖ ≤ c`,
`Dg` vanishes off `S`, `spt η ⊆ W` and `|η| ≤ 1`, then `∫⁻ ‖Dg‖ |η| dμ ≤ c μ(W ∩ S)`.  The
integrand is dominated by `c 𝟙_{W ∩ S}`: on `W \ S` it vanishes because `Dg = 0`, off `W` because
`η = 0`.  No measurability is needed, as `∫⁻ c 𝟙_A dμ ≤ c μ(A)` for every set `A`. -/
theorem Submission.cmcs_smp_strip_lintegral_le : ∀ (P k : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (η : DifferentialForm (Euclid P) k) (W S : Set (Euclid P)) (c : ℝ), (∀ x, ‖fderiv ℝ g x‖ ≤ c) → (∀ x, fderiv ℝ g x ≠ 0 → x ∈ S) → tsupport η ⊆ W → (∀ x, covectorEuclideanNorm (η x) ≤ 1) → ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ∂μ ≤ ENNReal.ofReal c * μ (W ∩ S) := by
  intro P k μ g η W S c hc hS hW hη
  -- the integrand is dominated by the indicator of `W ∩ S` with value `ofReal c`
  refine le_trans (lintegral_mono fun x => ?_)
    (lintegral_indicator_const_le (W ∩ S) (ENNReal.ofReal c))
  show ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x)) ≤
    (W ∩ S).indicator (fun _ => ENNReal.ofReal c) x
  by_cases hx : x ∈ W ∩ S
  · rw [indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal
      ((mul_le_of_le_one_right (norm_nonneg _) (hη x)).trans (hc x))
  · rw [indicator_of_notMem hx]
    -- off `W ∩ S` a factor vanishes: `Dg(x) = 0` on `W \ S` and `η(x) = 0` off `W`
    have h0 : ‖fderiv ℝ g x‖ * covectorEuclideanNorm (η x) = 0 := by
      by_cases hxW : x ∈ W
      · obtain hD | hD := eq_or_ne (fderiv ℝ g x) 0
        · rw [hD, norm_zero, zero_mul]
        · exact absurd ⟨hxW, hS x hD⟩ hx
      · have hηx : η x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxW (hW h)
        rw [hηx, covectorEuclideanNorm_zero, mul_zero]
    rw [h0, ENNReal.ofReal_zero]
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
/-- **Orthonormal basis adapted to a linear functional** (used for the wedge-norm bound
`|β ∧ γ| ≤ ‖β‖ |γ|`, Simon 6.1): for a continuous linear functional `β` on `ℝᴾ` and `i₀ : Fin P`
there is an orthonormal basis `f` of `ℝᴾ` with `β(f_{i₀}) = ‖β‖` and `β(f_i) = 0` for `i ≠ i₀`.
Write `β = ⟨b, ·⟩` (Riesz, `‖b‖ = ‖β‖`).  If `b = 0`, the standard basis `e` works.  Otherwise the
reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ`, `u = ‖b‖⁻¹ b`, maps `e_{i₀}` to `u`, and `f = R ∘ e` has
`β(f_i) = ‖b‖ ⟨R e_{i₀}, R e_i⟩ = ‖b‖ ⟨e_{i₀}, e_i⟩`. -/
theorem Submission.cmcs_wn_adapted_orthonormalBasis : ∀ (P : ℕ) (β : Euclid P →L[ℝ] ℝ) (i₀ : Fin P), ∃ f : OrthonormalBasis (Fin P) ℝ (Euclid P), ∀ i : Fin P, β (f i) = if i = i₀ then ‖β‖ else 0 := by
  intro P β i₀
  set e := EuclideanSpace.basisFun (Fin P) ℝ
  -- Riesz representative: `β x = ⟪b, x⟫` and `‖b‖ = ‖β‖`
  set b : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm β with hb
  have hβb : ∀ x, β x = inner ℝ b x := fun x => InnerProductSpace.toDual_symm_apply.symm
  have hnorm : ‖b‖ = ‖β‖ := by
    rw [hb, LinearIsometryEquiv.norm_map]
  by_cases hb0 : b = 0
  · -- `β = 0`: the standard basis works
    refine ⟨e, fun i => ?_⟩
    have h0 : ‖β‖ = 0 := by rw [← hnorm, hb0, norm_zero]
    rw [hβb, hb0, inner_zero_left, h0, ite_self]
  · -- `u = ‖b‖⁻¹ b` is a unit vector and `b = ‖b‖ u`
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
    set u : Euclid P := ‖b‖⁻¹ • b with hu_def
    have hu : ‖u‖ = 1 := by
      rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hbpos.ne']
    have hbu : b = ‖b‖ • u := by
      rw [hu_def, smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
    -- the reflection `R` in `(ℝ ∙ (e_{i₀} − u))ᗮ` maps `e_{i₀}` to `u`
    have he : ‖e i₀‖ = 1 := e.orthonormal.1 i₀
    set R := (ℝ ∙ (e i₀ - u))ᗮ.reflection
    have hR : R (e i₀) = u := Submodule.reflection_sub (he.trans hu.symm)
    -- `f = R ∘ e`: `β(f_i) = ‖b‖ ⟪R e_{i₀}, R e_i⟫ = ‖β‖ ⟪e_{i₀}, e_i⟫`
    refine ⟨e.map R, fun i => ?_⟩
    rw [OrthonormalBasis.map_apply, hβb, hbu, real_inner_smul_left, ← hR,
      LinearIsometryEquiv.inner_map_map, hnorm, orthonormal_iff_ite.mp e.orthonormal i₀ i]
    by_cases hi : i = i₀
    · rw [ite_eq_left hi.symm, ite_eq_left hi, mul_one]
    · rw [ite_eq_right (Ne.symm hi), ite_eq_right hi, mul_zero]
/-- **`β ∧ γ` on tuples of a family adapted to `β`** (Simon 6.1.1–1.3; step 4 of the proof of
`|β ∧ γ| ≤ ‖β‖ |γ|`): if `β(v_a) = c` for `a = i₀` and `β(v_a) = 0` otherwise, then for every
`j : Fin (k + 1) → Fin P`, `(β ∧ γ)(v_{j(0)}, …, v_{j(k)})² ≤ c² Σ_{i, j(i) = i₀} γ(v ∘ ĵᵢ)²`,
where `ĵᵢ = i.removeNth j` deletes the `i`-th entry of `j`.  By definition
`(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`.  A repeated index in `j` makes `v ∘ j`
non-injective, so the left side vanishes (alternation); otherwise at most one `i₁` has
`j(i₁) = i₀`, only `i₁` contributes to either side, and `((−1)^{i₁})² = 1`. -/
theorem Submission.cmcs_wn_tuple_sq_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k) (v : Fin P → Euclid P) (i₀ : Fin P) (c : ℝ), Function.Injective v → (∀ i : Fin P, β (v i) = if i = i₀ then c else 0) → ∀ j : Fin (k + 1) → Fin P, (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ) (fun m => v (j m))) ^ 2 ≤ c ^ 2 * ∑ i : Fin (k + 1), if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0 := by
  intro P k β γ v i₀ c _hv hβ j
  classical
  -- the right side is `c²` times a sum of squares and zeros
  have hRHS : 0 ≤ c ^ 2 * ∑ i : Fin (k + 1),
      (if j i = i₀ then (γ (fun m => v (i.removeNth j m))) ^ 2 else 0) :=
    mul_nonneg (sq_nonneg c) (Finset.sum_nonneg fun i _ => by split_ifs <;> positivity)
  by_cases hj : Injective j
  · -- `(β ∧ γ)(v ∘ j) = Σᵢ (−1)ⁱ β(v_{j(i)}) γ(v ∘ ĵᵢ)`, with `β(v_{j(i)}) = c [j(i) = i₀]`
    have hexp : ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
        (fun m => v (j m)) = ∑ i : Fin (k + 1),
          (-1 : ℝ) ^ (i : ℕ) *
            ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) := by
      rw [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.smulRight_apply, hβ (j i)]
      simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rfl
    rw [hexp]
    by_cases hex : ∃ i₁, j i₁ = i₀
    · -- `j` is injective, so `i₁` is the only index with `j(i₁) = i₀`
      obtain ⟨i₁, hi₁⟩ := hex
      have huniq : ∀ i, i ≠ i₁ → j i ≠ i₀ := fun i hi h => hi (hj (h.trans hi₁.symm))
      rw [Finset.sum_eq_single i₁ (fun i _ hi => by rw [ite_eq_right (huniq i hi)]; ring)
          (fun h => absurd (Finset.mem_univ i₁) h),
        Finset.sum_eq_single i₁ (fun i _ hi => ite_eq_right (huniq i hi))
          (fun h => absurd (Finset.mem_univ i₁) h),
        ite_eq_left hi₁, ite_eq_left hi₁]
      have hsign : ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul]
        norm_num
      refine le_of_eq ?_
      calc ((-1 : ℝ) ^ (i₁ : ℕ) * (c * γ (fun m => v (i₁.removeNth j m)))) ^ 2
          = ((-1 : ℝ) ^ (i₁ : ℕ)) ^ 2 * (c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2) := by
            ring
        _ = c ^ 2 * (γ (fun m => v (i₁.removeNth j m))) ^ 2 := by rw [hsign, one_mul]
    · -- no index hits `i₀`: every term vanishes
      have h0 : ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
          ((if j i = i₀ then c else 0) * γ (fun m => v (i.removeNth j m))) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [ite_eq_right fun h => hex ⟨i, h⟩]; ring
      rw [h0]
      simpa using hRHS
  · -- a repeated index makes `v ∘ j` non-injective, and `β ∧ γ` is alternating
    have hvj : ¬ Injective (fun m => v (j m)) := fun h => hj (Injective.of_comp (f := v) h)
    rw [ContinuousAlternatingMap.map_eq_zero_of_not_injective _ _ hvj]
    simpa using hRHS
/-- **Fibres of `j ↦ removeNth i j`** (the counting step of the bound `|β ∧ γ| ≤ ‖β‖ |γ|` for the
Euclidean norm of covectors, Simon Ch. 6, 1.1–1.3, 1.15): for `i₀ : Fin P` and
`F : (Fin k → Fin P) → ℝ`,
`Σ_{j : Fin (k+1) → Fin P} Σ_i [j i = i₀] F(removeNth i j) = (k + 1) Σ_{j' : Fin k → Fin P} F j'`.
For fixed `i`, `j ↦ (j i, removeNth i j)` is a bijection onto `Fin P × (Fin k → Fin P)`
(`Fin.insertNthEquiv`), so only `j i = i₀` survives and each of the `k + 1` indices `i`
contributes `Σ_{j'} F j'`. -/
theorem Submission.cmcs_wn_removeNth_fiber_sum : ∀ (k P : ℕ) (i₀ : Fin P) (F : (Fin k → Fin P) → ℝ), ∑ j : Fin (k + 1) → Fin P, ∑ i : Fin (k + 1), (if j i = i₀ then F (i.removeNth j) else 0) = ((k : ℝ) + 1) * ∑ j' : Fin k → Fin P, F j' := by
  intro k P i₀ F
  rw [Finset.sum_comm]
  -- for fixed `i`, reindex along `j ↦ (j i, removeNth i j)`; only `j i = i₀` survives
  have hfib : ∀ i : Fin (k + 1),
      ∑ j : Fin (k + 1) → Fin P, (if j i = i₀ then F (i.removeNth j) else 0) =
        ∑ j' : Fin k → Fin P, F j' := by
    intro i
    rw [Fintype.sum_equiv (Fin.insertNthEquiv (fun _ => Fin P) i).symm
      (fun j => if j i = i₀ then F (i.removeNth j) else 0)
      (fun p => if p.1 = i₀ then F p.2 else 0) fun _ => rfl,
      Fintype.sum_prod_type, Fintype.sum_eq_single i₀]
    · simp
    · intro x hx
      simp [hx]
  -- each of the `k + 1` indices `i` contributes `Σ_{j'} F j'`
  rw [Finset.sum_congr rfl fun i _ => hfib i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_add_one]
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **`|β ∧ γ| ≤ ‖β‖ |γ|`** (Simon 6.1.1–1.3 and 1.15): for a linear functional `β` and a
`k`-covector `γ` on `ℝᴾ`, the Euclidean coefficient norm of the `(k+1)`-covector
`β ∧ γ = alternatizeUncurryFin (β.smulRight γ)` is at most `‖β‖ |γ|`.  Take an orthonormal basis
`f` with `β(fᵢ) = ‖β‖ [i = i₀]`; then `(β ∧ γ)(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²`.
Summing over `j`, each `j' : Fin k → Fin P` arises as `i.removeNth j` with `j i = i₀` for exactly
`k + 1` pairs `(i, j)`, so `(k+1)! |β ∧ γ|² ≤ ‖β‖² (k+1) k! |γ|²` by
`regcomp_covector_sq_sum_orthonormalBasis` in degrees `k + 1` and `k`.  For `P = 0` there are no
coordinate tuples and `|β ∧ γ| = 0`. -/
theorem Submission.cmcs_wedge_norm_le : ∀ (P k : ℕ) (β : Euclid P →L[ℝ] ℝ) (γ : Covector (Euclid P) k), covectorEuclideanNorm (ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)) ≤ ‖β‖ * covectorEuclideanNorm γ := by
  intro P k β γ
  classical
  set ω := ContinuousAlternatingMap.alternatizeUncurryFin (β.smulRight γ)
  have hrhs : 0 ≤ ‖β‖ * covectorEuclideanNorm γ :=
    mul_nonneg (norm_nonneg β) (covectorEuclideanNorm_nonneg γ)
  rcases Nat.eq_zero_or_pos P with hP | hP
  · -- `P = 0`: there is no tuple `Fin (k + 1) → Fin 0`, so `|ω| = 0`
    subst hP
    have h0 : covectorEuclideanNorm ω = 0 := by
      simp [covectorEuclideanNorm]
    rw [h0]
    exact hrhs
  · -- an orthonormal basis `f` with `β(fᵢ) = ‖β‖ [i = i₀]`
    set i₀ : Fin P := ⟨0, hP⟩
    obtain ⟨f, hf⟩ := Submission.cmcs_wn_adapted_orthonormalBasis P β i₀
    -- `ω(f ∘ j)² ≤ ‖β‖² Σᵢ [j i = i₀] γ(f ∘ i.removeNth j)²` for every `j`
    have hle : ∑ j : Fin (k + 1) → Fin P, (ω (fun m => f (j m))) ^ 2 ≤
        ∑ j : Fin (k + 1) → Fin P, ‖β‖ ^ 2 * ∑ i : Fin (k + 1),
          (if j i = i₀ then (γ (fun m => f (i.removeNth j m))) ^ 2 else 0) :=
      Finset.sum_le_sum fun j _ => Submission.cmcs_wn_tuple_sq_le P k β γ f i₀ ‖β‖
        f.orthonormal.linearIndependent.injective hf j
    -- count the fibres of `j ↦ i.removeNth j`, then `Σ_j α(f ∘ j)² = m! |α|²` for `m = k + 1, k`
    rw [← Finset.mul_sum,
      Submission.cmcs_wn_removeNth_fiber_sum k P i₀ (fun j' => (γ (fun m => f (j' m))) ^ 2),
      Submission.regcomp_covector_sq_sum_orthonormalBasis P (k + 1) ω f,
      Submission.regcomp_covector_sq_sum_orthonormalBasis P k γ f] at hle
    -- cancel `(k+1)! = (k+1) k! > 0`
    have hpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
    have hsq : covectorEuclideanNorm ω ^ 2 ≤ (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
      refine le_of_mul_le_mul_left ?_ hpos
      calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm ω ^ 2
          ≤ ‖β‖ ^ 2 * (((k : ℝ) + 1) * ((k.factorial : ℝ) * covectorEuclideanNorm γ ^ 2)) := hle
        _ = ((k + 1).factorial : ℝ) * (‖β‖ * covectorEuclideanNorm γ) ^ 2 := by
          push_cast [Nat.factorial_succ]
          ring
    exact (sq_le_sq₀ (covectorEuclideanNorm_nonneg ω) hrhs).mp hsq

/-- **Simon Ch. 6, 4.11 (p. 158), the estimate of the cutoff defect**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')` with `|⟨α, ξ⟩| ≤ |α|` `μ`-a.e.: for a `C^∞` function `g`
and `η ∈ 𝒟ᵏ(U)`, `|∫ g ⟨dη, ξ⟩ dμ − ∫ g ⟨η, ξ'⟩ dμ'| ≤ ∫ |Dg| |η| dμ` in `[0, ∞]`.  The left side
is `|T(g dη) − ∂T(gη)| = |T(dg ∧ η)| = |∫ ⟨dg ∧ η, ξ⟩ dμ|` (`cmcs_cd_defect_identity`, with
`dg ∧ η = alternatizeUncurryFin (Dg.smulRight η)`), which is at most `∫ |⟨dg ∧ η, ξ⟩| dμ` whether
or not the integrand is integrable; and `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|` `μ`-a.e. by the bound
on `ξ` and `cmcs_wedge_norm_le`. -/
theorem Submission.cmcs_cutoff_defect_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (g : Euclid P → ℝ) (η : TestFormOn U k), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → ContDiff ℝ (⊤ : ℕ∞) g → ENNReal.ofReal |∫ x, g x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ - ∫ x, g x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ'| ≤ ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ g x‖ * covectorEuclideanNorm ((η : DifferentialForm (Euclid P) k) x)) ∂μ := by
  intro P k U T μ μ' ξ ξ' g η hξ hT hbT hg
  -- Simon 4.11: `T(g dη) − ∂T(gη) = −T(dg ∧ η) = −∫ ⟨dg ∧ η, ξ⟩ dμ`
  rw [Submission.cmcs_cd_defect_identity P k U T μ μ' ξ ξ' g η hT hbT hg, abs_neg,
    ← Real.enorm_eq_ofReal_abs]
  -- `‖∫ G dμ‖ₑ ≤ ∫⁻ ‖G‖ₑ dμ` for every `G`, integrable or not; then bound `G` `μ`-a.e.
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_ae ?_)
  filter_upwards [hξ] with x hx
  -- `|⟨dg ∧ η, ξ⟩| ≤ |dg ∧ η| ≤ |Dg| |η|`
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal ((hx _).trans (Submission.cmcs_wedge_norm_le P k _ _))
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

/-- **Smooth cut-off between two levels of a Lipschitz function** (Simon Ch. 6, proof of 4.9, with
`f^{(σ)}` in place of `f`).  If `f : ℝᴾ → ℝ` is `L`-Lipschitz, `t ∈ ℝ` and `0 < h < 1`, there is a
`C^∞` function `g` with `|g| ≤ 2`, `‖Dg‖ ≤ L/(h(1 − h/2))`, `g = 1` on `{f ≤ t − h}`, `g = 0` on
`{f ≥ t}` and `Dg = 0` off the strip `{t − h < f < t}`.  With `δ = h²/4` and
`w = h − 2δ = h(1 − h/2)`, the clamp `G = max 0 (min 1 ((t − δ − f)/w))` is `(L/w)`-Lipschitz,
`G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`; `g` is its smoothing at scale
`σ = δ/(2(L + 1))` (`cmcs_lipschitz_smoothing`), so `|g − G| ≤ Lσ/w ≤ 1`.  As `2Lσ < δ`, `G` is
constant on `B_{2σ}(x)` when `f x ≤ t − h` or `t ≤ f x`; by locality `g` is then constant on
`B_σ(x)`, so `Dg(x) = 0`. -/
theorem Submission.cmcs_level_cutoff : ∀ (P : ℕ) (f : Euclid P → ℝ) (L : NNReal) (t h : ℝ), LipschitzWith L f → 0 < h → h < 1 → ∃ g : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧ (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧ (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧ (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
  intro P f L t h hf h0 h1
  -- parameters `δ = h²/4`, `w = h − 2δ = h(1 − h/2)` and `σ = δ/(2(L + 1))`, so `2Lσ < δ`
  set δ : ℝ := h ^ 2 / 4 with hδ
  set w : ℝ := h * (1 - h / 2) with hw
  have hw0 : 0 < w := mul_pos h0 (by linarith)
  have hδ0 : 0 < δ := by positivity
  have hL0 : (0 : ℝ) ≤ L := L.2
  set σ : ℝ := δ / (2 * ((L : ℝ) + 1)) with hσ
  have hσ0 : 0 < σ := by positivity
  have h2Lσ : 2 * (L : ℝ) * σ < δ := by
    rw [hσ, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the clamped profile `G = max 0 (min 1 ((t − δ − f)/w))`: `(L/w)`-Lipschitz, `|G| ≤ 1`,
  -- `G = 1` on `{f < t − h + δ}` and `G = 0` on `{f > t − δ}`
  set G : Euclid P → ℝ := fun x => max 0 (min 1 ((t - δ - f x) / w)) with hGdef
  set K : NNReal := L * Real.toNNReal w⁻¹ with hK
  have hKr : (K : ℝ) = L / w := by
    rw [hK, NNReal.coe_mul, Real.coe_toNNReal _ (inv_pos.2 hw0).le, div_eq_mul_inv]
  have hG : LipschitzWith K G := by
    have hlin : LipschitzWith K fun x => (t - δ - f x) / w := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      have hxy := hf.dist_le_mul x y
      rw [Real.dist_eq] at hxy
      rw [Real.dist_eq, hKr, show (t - δ - f x) / w - (t - δ - f y) / w = (f y - f x) / w by ring,
        abs_div, abs_of_pos hw0, abs_sub_comm, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hxy hw0.le
    exact (hlin.const_min 1).const_max 0
  have hG01 : ∀ y, |G y| ≤ 1 := by
    intro y
    simp only [hGdef]
    rw [abs_le]
    exact ⟨by linarith [le_max_left 0 (min 1 ((t - δ - f y) / w))],
      max_le zero_le_one (min_le_left _ _)⟩
  have hG1 : ∀ y, f y < t - h + δ → G y = 1 := by
    intro y hy
    have : 1 ≤ (t - δ - f y) / w := by rw [le_div_iff₀ hw0]; linarith
    simp [hGdef, min_eq_left this]
  have hG0 : ∀ y, t - δ < f y → G y = 0 := by
    intro y hy
    have : (t - δ - f y) / w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw0.le
    simp only [hGdef]
    exact max_eq_left ((min_le_right _ _).trans this)
  -- smoothing of `G` at scale `σ`
  obtain ⟨g, hgs, hgd, hga, hgl⟩ := Submission.cmcs_lipschitz_smoothing P G K σ hG hσ0
  -- plateaus: if `G = c` on `B_{2σ}(x)`, then `g = c` on `B_σ(x)`, so `g x = c` and `Dg(x) = 0`
  have hnear : ∀ x, ∀ c : ℝ, (∀ y ∈ ball x (2 * σ), G y = c) → g x = c ∧ fderiv ℝ g x = 0 := by
    intro x c hc
    have hball : ∀ x' ∈ ball x σ, g x' = c := fun x' hx' => hgl x' c fun y hy => hc y (by
      rw [mem_ball] at hx' hy ⊢
      linarith [dist_triangle y x' x])
    have hev : g =ᶠ[𝓝 x] fun _ => c := Filter.eventually_of_mem (ball_mem_nhds x hσ0) hball
    exact ⟨hball x (mem_ball_self hσ0), hev.fderiv_eq.trans (fderiv_const_apply c)⟩
  -- on `B_{2σ}(x)`, `|f y − f x| ≤ L |y − x| < 2Lσ < δ`
  have hclose : ∀ x, ∀ y ∈ ball x (2 * σ), |f y - f x| < δ := by
    intro x y hy
    have hd := hf.dist_le_mul y x
    rw [Real.dist_eq] at hd
    rw [mem_ball] at hy
    have : (L : ℝ) * dist y x ≤ L * (2 * σ) := mul_le_mul_of_nonneg_left hy.le hL0
    linarith
  have hlow : ∀ x, f x ≤ t - h → g x = 1 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 1 fun y hy => hG1 y (by linarith [(abs_lt.1 (hclose x y hy)).2])
  have hup : ∀ x, t ≤ f x → g x = 0 ∧ fderiv ℝ g x = 0 := fun x hx =>
    hnear x 0 fun y hy => hG0 y (by linarith [(abs_lt.1 (hclose x y hy)).1])
  refine ⟨g, hgs, fun x => ?_, fun x => (hgd x).trans_eq hKr, fun x hx => ?_,
    fun x hx => (hlow x hx).1, fun x hx => (hup x hx).1⟩
  · -- `|g| ≤ |G| + Kσ ≤ 2`, as `Kσ = Lδ/(2(L + 1)w) ≤ 1` (`δ ≤ 2w`)
    have hKσ : (K : ℝ) * σ ≤ 1 := by
      rw [hKr, hσ, div_mul_div_comm, div_le_one (by positivity)]
      have hδw : δ ≤ 2 * w := by rw [hδ, hw]; nlinarith
      nlinarith
    linarith [abs_sub_abs_le_abs_sub (g x) (G x), hga x, hG01 x]
  · -- `Dg = 0` on both plateaus, so `Dg(x) ≠ 0` forces `t − h < f x < t`
    by_contra hcon
    rcases not_and_or.1 hcon with hc | hc
    · exact hx (hlow x (not_lt.1 hc)).2
    · exact hx (hup x (not_lt.1 hc)).2

/-- **Mass of a slice, pointwise in `t`** (Simon 6.4.9, proved as in 6.4.11): let `T = ξ μ`,
`∂T = ξ' μ'` with `|ξ|, |ξ'| ≤ 1`, let `f` be `L`-Lipschitz, and let `A = T ⌞ {f < t}`,
`B = (∂T) ⌞ {f < t}`.  Then `M_W(∂A − B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})`.
For an admissible `η` and `h ∈ (0, 1)`, the smooth cut-off `g_h` of `cmcs_level_cutoff` gives
`Φ_h = ∫ g_h ξ(dη) dμ − ∫ g_h ξ'(η) dμ'` with `|Φ_h| ≤ ∫ |Dg_h| |η| dμ ≤ c_h μ(W ∩ S_h)`,
`c_h = L / (h(1 − h/2))`, `S_h = {t − h < f < t}` (`cmcs_cutoff_defect_bound`,
`cmcs_smp_strip_lintegral_le`); `Φ_h → (∂A − B)(η)` by dominated convergence
(`cmcs_smp_cutoff_integral_tendsto`), and `cmcs_smp_liminf_bound` passes to the liminf. -/
theorem Submission.cmcs_slice_mass_pointwise : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (A : GeometricCurrentOn U (k + 1)) (B : GeometricCurrentOn U k) (W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, T.boundary θ = ∫ x, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → (∀ ω : TestFormOn U (k + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ θ : TestFormOn U k, B θ = ∫ x in {x | f x < t}, ξ' x ((θ : DifferentialForm (Euclid P) k) x) ∂μ') → (A.boundary - B).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro P k U T μ μ' ξ ξ' f L t A B W hμ hμ' hξm hξm' hξ hξ' hT hbT hf hA hB
  -- Step 3: a cut-off `g h` for every `h ∈ (0, 1)` (junk value `0` for other `h`).
  have hcut : ∀ h : ℝ, ∃ g : Euclid P → ℝ, 0 < h → h < 1 →
      ContDiff ℝ (⊤ : ℕ∞) g ∧ (∀ x, |g x| ≤ 2) ∧
        (∀ x, ‖fderiv ℝ g x‖ ≤ L / (h * (1 - h / 2))) ∧
        (∀ x, fderiv ℝ g x ≠ 0 → t - h < f x ∧ f x < t) ∧
        (∀ x, f x ≤ t - h → g x = 1) ∧ (∀ x, t ≤ f x → g x = 0) := by
    intro h
    by_cases hh : 0 < h ∧ h < 1
    · obtain ⟨g, hg⟩ := Submission.cmcs_level_cutoff P f L t h hf hh.1 hh.2
      exact ⟨g, fun _ _ => hg⟩
    · exact ⟨0, fun h0 h1 => (hh ⟨h0, h1⟩).elim⟩
  choose g hg using hcut
  -- Step 1: it suffices to bound `ofReal ((∂A − B) η)` for one admissible `η`.
  apply sSup_le
  rintro r ⟨η, ⟨hηW, hη1⟩, rfl⟩
  have hZ : (A.boundary - B) η =
      (∫ x in {x | f x < t}, ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ' := by
    change A (exteriorDerivativeTestOn U k η) - B η = _
    rw [hA, hB]
    rfl
  -- Step 2: `F = ξ(dη)` is `μ`-integrable and `F' = ξ'(η)` is `μ'`-integrable.
  have hF : Integrable
      (fun x => ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x)) μ :=
    Submission.cmcs_smp_pairing_integrable P (k + 1) U μ ξ (exteriorDerivativeTestOn U k η)
      hμ hξm hξ
  have hF' : Integrable (fun x => ξ' x ((η : DifferentialForm (Euclid P) k) x)) μ' :=
    Submission.cmcs_smp_pairing_integrable P k U μ' ξ' η hμ' hξm' hξ'
  -- Step 5: `Φ h → (∂A − B)(η)` as `h ↓ 0`, by dominated convergence for each integral.
  have hfm : Measurable f := hf.continuous.measurable
  have hgm : ∀ ν : Measure (Euclid P), ∀ h : ℝ, 0 < h → h < 1 → AEStronglyMeasurable (g h) ν :=
    fun _ h h0 h1 => (hg h h0 h1).1.continuous.aestronglyMeasurable
  have hlim : Tendsto (fun h : ℝ =>
      (∫ x, g h x * ξ x (exteriorDerivative (η : DifferentialForm (Euclid P) k) x) ∂μ) -
        ∫ x, g h x * ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ')
      (𝓝[>] 0) (𝓝 ((A.boundary - B) η)) := by
    rw [hZ]
    exact (Submission.cmcs_smp_cutoff_integral_tendsto P μ _ f t 2 g hF hfm (hgm μ)
      (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
      (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2)).sub
      (Submission.cmcs_smp_cutoff_integral_tendsto P μ' _ f t 2 g hF' hfm (hgm μ')
        (fun h h0 h1 => (hg h h0 h1).2.1) (fun h h0 h1 => (hg h h0 h1).2.2.2.2.1)
        (fun h h0 h1 => (hg h h0 h1).2.2.2.2.2))
  -- Steps 4 and 6: `ofReal |Φ h| ≤ ofReal (L / (h (1 − h/2))) μ(W ∩ S_h)` for `h ∈ (0, 1)`,
  -- then pass to the liminf.
  refine Submission.cmcs_smp_liminf_bound L ((A.boundary - B) η) _
    (fun h => μ (W ∩ {x | t - h < f x ∧ f x < t})) hlim fun h h0 h1 => ?_
  obtain ⟨hgs, -, hgd, hgS, -, -⟩ := hg h h0 h1
  exact (Submission.cmcs_cutoff_defect_bound P k U T μ μ' ξ ξ' (g h) η hξ hT hbT hgs).trans
    (Submission.cmcs_smp_strip_lintegral_le P k μ (g h) (η : DifferentialForm (Euclid P) k) W
      {x | t - h < f x ∧ f x < t} _ hgd hgS hηW hη1)
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)
/-- **Inner-annulus quotients and the derivative of `r ↦ μ(B_r(x₁))`** (Simon Ch. 6: the
quotients `h⁻¹ M(T⌞{t − h < |x − ξ| < t})` of 4.9 are bounded by the derivative of
`r ↦ M(T⌞B_r(ξ))`, as used in the proof of 8.2, (2)).  If `μ(B_ρ(x₁)) < ∞` and
`F(r) = μ(B_r(x₁))` has derivative `d` at `ρ`, then
`liminf_{h ↓ 0} h⁻¹ μ{ρ − h < |x − x₁| < ρ} ≤ d`: for `h > 0` the annulus lies in
`B_ρ(x₁) \ B_{ρ−h}(x₁)`, of measure `F(ρ) − F(ρ − h)`, and the backward difference quotients
`h⁻¹ (F(ρ) − F(ρ − h))` tend to `d`. -/
theorem Submission.cbrld_radius_liminf_annulus_le_of_hasDerivAt : ∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (ρ d : ℝ), μ (ball x₁ ρ) ≠ ∞ → HasDerivAt (fun r : ℝ => (μ (ball x₁ r)).toReal) d ρ → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal d := by
  intro P μ x₁ ρ d hμ hd
  -- the backward difference quotients `h⁻¹ (F(ρ) − F(ρ − h))` tend to `d` as `h ↓ 0`
  have hq : Tendsto (fun h : ℝ => h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal))
      (𝓝[>] 0) (𝓝 d) := by
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    refine (hd.tendsto_slope_zero_left.comp hneg).congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [inv_neg, ← sub_eq_add_neg]
    ring
  have hlim : liminf (fun h : ℝ => ENNReal.ofReal
      (h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal))) (𝓝[>] 0) =
      ENNReal.ofReal d :=
    ((ENNReal.continuous_ofReal.tendsto d).comp hq).liminf_eq
  refine (liminf_le_liminf ?_).trans_eq hlim
  -- for `h > 0`, the annulus lies in `B_ρ(x₁) \ B_{ρ−h}(x₁)`, of measure `F(ρ) − F(ρ − h)`
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have hsub : ball x₁ (ρ - h) ⊆ ball x₁ ρ := ball_subset_ball (by linarith)
  have hfin : μ (ball x₁ (ρ - h)) ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono hsub)
  have hA : {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ} ⊆ ball x₁ ρ \ ball x₁ (ρ - h) :=
    fun x hx => ⟨mem_ball.mpr hx.2, fun hx' => lt_asymm hx.1 (mem_ball.mp hx')⟩
  calc ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}
      ≤ ENNReal.ofReal h⁻¹ * μ (ball x₁ ρ \ ball x₁ (ρ - h)) := by gcongr
    _ = ENNReal.ofReal h⁻¹ * ENNReal.ofReal
          ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal) := by
        rw [measure_sdiff hsub measurableSet_ball.nullMeasurableSet hfin,
          ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hμ,
          ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal)) :=
        (ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)).symm
/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem)**, from the scaled deformation theorem 5.3 in the
frozen form (DT), with constant `c ≥ 1` for `(P, m)`.  Let `Z ∈ 𝒟_{m+1}(ℝᴾ)` be integer
multiplicity with `spt Z` compact, `∂Z = 0` and `z = M(Z) < ∞`.  Apply (DT) to `T = Z` with
`K = spt Z`, `Λ = z` and `ρ = (2cz)^{1/(m+1)}` (`ρ = 1` if `z = 0`).  A current of zero mass is
zero (test `±sω` with `s‖ω‖_∞ ≤ 1`), so `M(S) ≤ cρ M(∂Z) = 0` gives `S = 0`, and
`M(Q) ≤ cz < ρ^{m+1}` excludes the second alternative, so `Q = 0` and `Z = ∂R`.  Then `Y = R` has
the mass and support bounds of (DT); if `z = 0`, also `M(R) = 0`, so `spt R = ∅`. -/
theorem Submission.cbr_isoperimetric_filling : (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P m : ℕ), ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support := by
  intro hDT P m
  obtain ⟨c, hc1, hDT⟩ := hDT P m
  refine ⟨(c : ℝ), by exact_mod_cast hc1, ?_⟩
  intro Z hZ hZc hZb hZm
  -- `M(0) = 0` and `spt 0 = ∅`
  have hmass0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).mass = 0 := by
    intro k
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  have hsupp0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).support = ∅ := by
    intro k
    refine eq_empty_of_forall_notMem fun x hx => hx.2 ?_
    exact ⟨ball x 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _,
      fun ω _ => rfl⟩, mem_ball_self one_pos⟩
  -- the Euclidean coefficient norm is absolutely homogeneous
  have hhom : ∀ (k : ℕ) (t : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro k t α
    simp only [covectorEuclideanNorm]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- a current of zero mass is zero: test `±sω` with `s‖ω‖_∞ ≤ 1`
  have hzero : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass = 0 →
      X = 0 := by
    intro k X hX
    ext ω
    have hω : Continuous (ω : DifferentialForm (Euclid P) k) := ω.property.1.1.continuous
    have hfc : Continuous (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) := by
      simp only [Function.comp_def, covectorEuclideanNorm]
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hω).pow 2)
        fun _ => continuous_const
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) :=
      ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k)
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hcs
    obtain ⟨s, hs, hsC⟩ : ∃ s : ℝ, 0 < s ∧ s * (|C| + 1) = 1 :=
      ⟨(|C| + 1)⁻¹, by positivity, inv_mul_cancel₀ (by positivity)⟩
    have hadm : ∀ t : ℝ, |t| ≤ s → t • ω ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      intro t ht
      refine ⟨subset_univ _, fun x => ?_⟩
      show covectorEuclideanNorm (t • (ω : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hhom]
      have h0 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
      have h1 : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ |C| + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg h0] at this
        linarith [le_abs_self C]
      calc |t| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x)
          ≤ s * (|C| + 1) := mul_le_mul ht h1 h0 hs.le
        _ = 1 := hsC
    have hX' : X.massOn univ = 0 := hX
    have h1 := X.le_massOn (hadm s (abs_of_pos hs).le)
    have h2 := X.le_massOn (hadm (-s) (by rw [abs_neg, abs_of_pos hs]))
    rw [hX', nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1 h2
    have e1 : X (s • ω) = s * X ω := map_smul X.toCurrent s ω
    have e2 : X ((-s) • ω) = -(s * X ω) := by
      rw [show X ((-s) • ω) = -s * X ω from map_smul X.toCurrent (-s) ω]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 : s * X ω = 0 := by linarith
    rw [GeometricCurrentOn.zero_apply]
    exact (mul_eq_zero.1 h3).resolve_left hs.ne'
  -- the scale `ρ`
  set z : ℝ := Z.mass.toReal
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  have hZmz : Z.mass = ENNReal.ofReal z := (ENNReal.ofReal_toReal hZm.ne).symm
  have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
  have hc0' : (0 : ℝ) < c := by exact_mod_cast zero_lt_one.trans_le hc1
  have hcz0 : 0 ≤ (c : ℝ) * z := mul_nonneg hc0 hz0
  obtain ⟨ρ, hρ0, hρlt, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ (c : ℝ) * z < ρ ^ (m + 1) ∧
      (z = 0 ∨ ρ = (2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) := by
    rcases hz0.eq_or_lt with h | h
    · exact ⟨1, one_pos, by rw [← h]; simp, Or.inl h.symm⟩
    · have hcz : 0 < 2 * (c : ℝ) * z := mul_pos (mul_pos two_pos hc0') h
      refine ⟨_, Real.rpow_pos_of_pos hcz _, ?_, Or.inr rfl⟩
      have hpow : ((2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = 2 * (c : ℝ) * z := by
        rw [one_div, ← Nat.cast_succ]
        exact Real.rpow_inv_natCast_pow hcz.le (Nat.succ_ne_zero m)
      rw [hpow]
      have : 0 < (c : ℝ) * z := mul_pos hc0' h
      linarith
  have hcρ : 0 ≤ (c : ℝ) * ρ := mul_nonneg hc0 hρ0.le
  -- apply (DT) to `T = Z`
  obtain ⟨𝒬, -, hDT⟩ := hDT ρ Z.support Z.mass.toNNReal hρ0 hZc
  obtain ⟨Q, -, R, S, -, -, hR, hZQS, hQ, hQm, -, hRm, hSm, hQR, -⟩ :=
    hDT Z hZ subset_rfl (ENNReal.coe_toNNReal hZm.ne).ge
      (by rw [hZb, hmass0]; exact ENNReal.zero_lt_top)
  -- `M(S) ≤ cρ M(∂Z) = 0`, so `S = 0`
  rw [hZb, hmass0, mul_zero, nonpos_iff_eq_zero] at hSm
  obtain rfl : S = 0 := hzero _ S hSm
  -- `M(Q) ≤ cz < ρ^{m+1}`, so `Q = 0`
  obtain rfl : Q = 0 := by
    refine hQ.resolve_right fun h => ?_
    have h' := h.trans hQm
    rw [hZmz, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_le_ofReal_iff hcz0] at h'
    linarith
  -- hence `Z = ∂R`
  have hRZ : R.boundary = Z := by
    rw [← hZQS]
    ext ω
    show Z ω - 0 - 0 = Z ω
    ring
  rcases hρ with h | rfl
  · -- `z = 0`: `M(R) ≤ cρ · 0 = 0`, so `R = 0`
    rw [hZmz, h, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at hRm
    refine ⟨R, hR, hRZ, hRm.trans_le zero_le, ?_⟩
    rw [hzero _ R hRm, hsupp0]
    exact empty_subset _
  · refine ⟨R, hR, hRZ, hRm.trans (le_of_eq ?_), subset_union_right.trans hQR⟩
    rw [ENNReal.ofReal_mul hcρ, ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal, hZmz]
/-- **Good slicing radius** (Simon Ch. 6, 8.2 (2)–(3): radii where `(F^{1/n})′` is controlled,
and `F′ = nF^{(n−1)/n}(F^{1/n})′`).  If `μ` is finite on compact sets, `n ≥ 1`, `a, s > 0`,
`μ(B_s(x₁)) < (as)ⁿ` and `L¹(N) = 0`, then some `ρ ∈ (0, s) \ N` has `μ(∂B_ρ(x₁)) = 0` and
`liminf_{h ↓ 0} h⁻¹ μ{ρ − h < |x − x₁| < ρ} ≤ 2na μ(B_ρ(x₁))^{(n−1)/n}`.  Let `F(r) = μ(B_r(x₁))`
and `G = F^{1/n}`: both are nondecreasing, `G(0) = 0` and `G(s) ≤ as`, so `∫_{(0,s)} G′ ≤ as`
(Lebesgue's inequality).  The good-radius lemma applied to `1_{(0,s)} G′` avoids `N`, the
non-differentiability points of `G` and the spheres charged by `μ`, with `G′(ρ) ≤ (2/s)·as = 2a`.
Then `F = Gⁿ` has derivative `nG(ρ)^{n−1}G′(ρ) ≤ 2na F(ρ)^{(n−1)/n}` at `ρ`, which bounds the
inner-annulus liminf. -/
theorem Submission.cbrld_exists_good_slice_radius : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (a s : ℝ) (N : Set ℝ), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → 1 ≤ n → 0 < a → 0 < s → μ (ball x₁ s) < ENNReal.ofReal ((a * s) ^ n) → volume N = 0 → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s ∧ ρ ∉ N ∧ μ (sphere x₁ ρ) = 0 ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal (2 * n * a * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n)) := by
  intro P n μ x₁ a s N hμ hn ha hs hμs hN
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0'.le
  -- `μ` is finite on balls (closed balls are compact)
  have hball : ∀ r : ℝ, μ (ball x₁ r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top (hμ _ (isCompact_closedBall x₁ r)).ne (measure_mono ball_subset_closedBall)
  -- `F(r) = μ(B_r(x₁))` and `G = F^{1/n}` are nondecreasing, `G(0) = 0`, `Gⁿ = F`, `G(s) ≤ as`
  set F : ℝ → ℝ := fun r => (μ (ball x₁ r)).toReal with hF_def
  set G : ℝ → ℝ := fun r => F r ^ (n : ℝ)⁻¹ with hG_def
  have hF0 : ∀ r, 0 ≤ F r := fun r => ENNReal.toReal_nonneg
  have hFmono : Monotone F := fun r r' hrr' =>
    ENNReal.toReal_mono (hball r') (measure_mono (ball_subset_ball hrr'))
  have hGmono : Monotone G := fun r r' hrr' => Real.rpow_le_rpow (hF0 r) (hFmono hrr') hinv
  have hFG : ∀ r, G r ^ n = F r := fun r => Real.rpow_inv_natCast_pow (hF0 r) hn0
  have hG0 : G 0 = 0 := by
    simp only [hG_def, hF_def, ball_zero, measure_empty, ENNReal.toReal_zero]
    exact Real.zero_rpow (inv_ne_zero hn0'.ne')
  have hGs : G s ≤ a * s :=
    calc G s ≤ ((a * s) ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (hF0 s) (ENNReal.toReal_lt_of_lt_ofReal hμs).le hinv
      _ = a * s := Real.pow_rpow_inv_natCast (mul_pos ha hs).le hn0
  -- Lebesgue's inequality: `∫⁻_{(0,s)} G′ ≤ G(s) − G(0) ≤ as`
  have hgm : AEMeasurable ((Ioo 0 s).indicator fun t => ENNReal.ofReal (deriv G t)) :=
    ((ENNReal.measurable_ofReal.comp (measurable_deriv G)).indicator measurableSet_Ioo).aemeasurable
  have hgI : ∫⁻ t, (Ioo 0 s).indicator (fun t => ENNReal.ofReal (deriv G t)) t ≤
      ENNReal.ofReal (a * s) := by
    rw [lintegral_indicator measurableSet_Ioo]
    refine (Submission.cmcs_smi_lintegral_ofReal_deriv_le G 0 s hGmono).trans ?_
    rw [hG0, sub_zero]
    exact ENNReal.ofReal_le_ofReal hGs
  -- the exceptional radii: `N` and the points where `G` is not differentiable
  have hp : ∀ᵐ t, t ∉ N ∧ DifferentiableAt ℝ G t :=
    (measure_eq_zero_iff_ae_notMem.mp hN).and hGmono.ae_differentiableAt
  obtain ⟨ρ, hρ0, hρs, ⟨hρN, hρd⟩, hρsph, hρg⟩ :=
    Submission.dor_lmb_glc_good_radius P μ x₁ 0 s _ _ _ hs (hμ _ (isCompact_closedBall x₁ s)).ne
      hgm hgI hp
  -- `G′(ρ) ≤ (2/s) · as = 2a`
  have hGd : deriv G ρ ≤ 2 * a := by
    rw [indicator_of_mem (mem_Ioo.mpr ⟨hρ0, hρs⟩), sub_zero,
      ← ENNReal.ofReal_mul (div_nonneg zero_le_two hs.le),
      show 2 / s * (a * s) = 2 * a by field_simp,
      ENNReal.ofReal_le_ofReal_iff (mul_pos two_pos ha).le] at hρg
    exact hρg
  refine ⟨ρ, hρ0, hρs, hρN, hρsph, ?_⟩
  -- `F = Gⁿ` has derivative `nG(ρ)^{n−1}G′(ρ)` at `ρ`
  have hFd : HasDerivAt F (n * G ρ ^ (n - 1) * deriv G ρ) ρ := by
    have h := hρd.hasDerivAt.fun_pow n
    rwa [show (fun r => G r ^ n) = F from funext hFG] at h
  refine (Submission.cbrld_radius_liminf_annulus_le_of_hasDerivAt P μ x₁ ρ _ (hball ρ) hFd).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- `G(ρ)^{n−1} = F(ρ)^{(n−1)/n}`, and `G′(ρ) ≤ 2a`
  have hpow : G ρ ^ (n - 1) = (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) := by
    rw [hG_def, hF_def]
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg, Nat.cast_sub hn,
      Nat.cast_one, inv_mul_eq_div]
  rw [hpow]
  have hX : 0 ≤ (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc (n : ℝ) * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) * deriv G ρ
      ≤ n * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) * (2 * a) := by gcongr
    _ = 2 * n * a * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) := by ring

/-- **Cone inequality for small cycles** (Simon Ch. 6, 2.27/2.30, as used in 8.2(4)–(6)).  Assume
(VO) and let `c ≥ 0` be a Lipschitz constant of `ω` in the Euclidean coefficient norm.  If
`∂X = 0`, `M(X) < ∞` and `spt X ⊆ B̄_ϱ(x₀)`, fix `ε > 0`, a bump `ζ` with `ζ = 1` on
`B̄_{ϱ+ε/2}(x₀)` and `ζ = 0` off `B_{ϱ+ε}(x₀)`, `α := ω(x₀)` and `φ := ζ (ω - α)`.  Then
`ω - φ = α` on `B_{ϱ+ε/2}(x₀) ⊇ spt X`, so `X(ω - φ) = 0` (a constant form is exact near `spt X`
and `∂X = 0`), while `|φ(x)| = ζ(x) |ω(x) - ω(x₀)| ≤ c (ϱ + ε)`.  Hence
`|X(ω)| = |X(φ)| ≤ c (ϱ + ε) M(X)`, and `ε ↓ 0` gives the claim. -/
theorem Submission.cbrld_cycle_eval_le_radius_mul_mass : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P n : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) (n + 1)), ∃ c : ℝ, 0 ≤ c ∧ ∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1)) (x₀ : Euclid P) (ϱ : ℝ), 0 < ϱ → X.boundary = 0 → X.mass < ∞ → X.support ⊆ closedBall x₀ ϱ → |X ω| ≤ c * ϱ * X.mass.toReal := by
  intro VO P n ω
  -- the constant depends only on `ω`: a Lipschitz constant in the coefficient norm
  obtain ⟨c, hc0, hc⟩ := Submission.cbrld_cone_testForm_coeff_lipschitz P (n + 1) univ ω
  refine ⟨c, hc0, fun X x₀ ϱ hϱ hbd hM hspt => ?_⟩
  have hsmul := (Submission.rsd_mw_tfa_norm_props P (n + 1)).2.1
  let α : Covector (Euclid P) (n + 1) := (ω : DifferentialForm (Euclid P) (n + 1)) x₀
  -- `|X(ω)| ≤ c (ϱ + ε) M(X)` for every `ε > 0`
  have hbound : ∀ ε : ℝ, 0 < ε → |X ω| ≤ c * (ϱ + ε) * X.mass.toReal := by
    intro ε hε
    -- the cut-off: `ζ = 1` on `B̄_{ϱ+ε/2}(x₀)` and `ζ = 0` off `B_{ϱ+ε}(x₀)`
    let ζ : ContDiffBump x₀ := ⟨ϱ + ε / 2, ϱ + ε, by linarith, by linarith⟩
    -- the test form `φ = ζ (ω - α)`
    let φ : TestFormOn (univ : Set (Euclid P)) (n + 1) :=
      ⟨fun x => ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α),
        ⟨ζ.contDiff.smul (ContDiff.sub ω.property.1.1 contDiff_const),
          ζ.hasCompactSupport.smul_right⟩, subset_univ _⟩
    -- `ω - φ = α` on `B_{ϱ+ε/2}(x₀) ⊇ spt X`, so the cycle `X` kills `ω - φ`
    have hconst : ∀ x ∈ ball x₀ (ϱ + ε / 2),
        ((ω - φ : TestFormOn (univ : Set (Euclid P)) (n + 1)) :
          DifferentialForm (Euclid P) (n + 1)) x = α := by
      intro x hx
      change (ω : DifferentialForm (Euclid P) (n + 1)) x -
        ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α) = α
      rw [ζ.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul, sub_sub_cancel]
    have h0 : X (ω - φ) = 0 :=
      Submission.cbrld_cone_cycle_eval_eq_zero_of_const_on_ball VO P n X x₀ (ϱ + ε / 2) α
        (ω - φ) (by linarith) hbd (hspt.trans (closedBall_subset_ball (by linarith))) hconst
    have hXφ : X ω = X φ := by
      have h := map_sub X.toCurrent ω φ
      change X (ω - φ) = X ω - X φ at h
      linarith
    -- `|φ(x)| = ζ(x) |ω(x) - ω(x₀)| ≤ c (ϱ + ε)`
    have hφ : ∀ x, covectorEuclideanNorm ((φ : DifferentialForm (Euclid P) (n + 1)) x) ≤
        c * (ϱ + ε) := by
      intro x
      change covectorEuclideanNorm (ζ x • ((ω : DifferentialForm (Euclid P) (n + 1)) x - α)) ≤
        c * (ϱ + ε)
      rw [hsmul, abs_of_nonneg (ζ.nonneg' x)]
      by_cases hx : dist x x₀ < ϱ + ε
      · calc ζ x * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (n + 1)) x - α)
            ≤ 1 * (c * (ϱ + ε)) :=
              mul_le_mul ζ.le_one ((hc x x₀).trans (mul_le_mul_of_nonneg_left hx.le hc0))
                (covectorEuclideanNorm_nonneg _) zero_le_one
          _ = c * (ϱ + ε) := one_mul _
      · rw [ζ.zero_of_le_dist (not_lt.1 hx), zero_mul]
        exact mul_nonneg hc0 (by linarith)
    rw [hXφ]
    exact Submission.cmr_abs_apply_le_massOn P (n + 1) univ univ X φ (c * (ϱ + ε)) hM.ne
      (subset_univ _) hφ
  -- let `ε ↓ 0`
  have hlim : Tendsto (fun ε : ℝ => c * (ϱ + ε) * X.mass.toReal) (𝓝[>] 0)
      (𝓝 (c * ϱ * X.mass.toReal)) := by
    have h := (show Continuous fun ε : ℝ => c * (ϱ + ε) * X.mass.toReal by fun_prop).tendsto 0
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)
/-- **Simon Ch. 1, Remark 3.11(3)** (via the Besicovitch Covering Lemma 3.12), with the balls
chosen inside an open set as in the proof of Theorem 3.13: let `μ` be finite on compact subsets of
`ℝᴾ`, `W` open and `E ⊆ W` (not necessarily measurable).  If every `x ∈ E` admits arbitrarily small
radii `ρ > 0` with `Q x ρ`, then countably many pairwise disjoint closed balls
`B̄_{r(x)}(x) ⊆ W`, `x ∈ t ⊆ E`, with `Q x (r x)`, cover `μ`-almost all of `E`.  Apply the
measurable Besicovitch covering theorem to the admissible radii `{ρ | B̄_ρ(x) ⊆ W ∧ Q x ρ}`. -/
theorem Submission.cbrldvc_exists_disjoint_closedBall_cover : ∀ (P : ℕ) (μ : Measure (Euclid P)) (Q : Euclid P → ℝ → Prop) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → IsOpen W → E ⊆ W → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q x ρ) → ∃ (t : Set (Euclid P)) (r : Euclid P → ℝ), t.Countable ∧ t ⊆ E ∧ (∀ x ∈ t, 0 < r x ∧ closedBall x (r x) ⊆ W ∧ Q x (r x)) ∧ t.PairwiseDisjoint (fun x => closedBall x (r x)) ∧ μ (E \ ⋃ x ∈ t, closedBall x (r x)) = 0 := by
  intro P μ Q E W hK hW hEW hQ
  -- finite on compacts, hence s-finite on the proper space `ℝᴾ`
  have : IsFiniteMeasureOnCompacts μ := ⟨hK⟩
  -- admissible radii: shrink below the radius `R` of an open ball `B_R(x) ⊆ W`
  have hf : ∀ x ∈ E, ∀ δ > 0, ({ρ | closedBall x ρ ⊆ W ∧ Q x ρ} ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW x (hEW hx)
    obtain ⟨ρ, hρ, hρδ, hQρ⟩ := hQ x hx (min δ R) (lt_min hδ hR)
    exact ⟨ρ, ⟨(closedBall_subset_ball (hρδ.trans_le (min_le_right _ _))).trans hRW, hQρ⟩, hρ,
      hρδ.trans_le (min_le_left _ _)⟩
  obtain ⟨t, r, ht, htE, hr, hμ, hdisj⟩ := Besicovitch.exists_disjoint_closedBall_covering_ae μ
    (fun x => {ρ | closedBall x ρ ⊆ W ∧ Q x ρ}) E hf (fun _ => 1) fun _ _ => zero_lt_one
  exact ⟨t, r, ht, htE, fun x hx => ⟨(hr x hx).2.1, (hr x hx).1.1, (hr x hx).1.2⟩, hdisj, hμ⟩
/-- **Summation over disjoint sets** (step 5 of the lower density bound used for Simon 7.2.4):
if `B(x)`, `x ∈ t`, are countably many disjoint measurable sets with `V = ⋃_{x ∈ t} B(x)` of finite
measure, `g` is integrable on `V` and `∫_{B(x)} g dμ ≤ θ μ(B(x))` for every `x ∈ t`, then
`∫_V g dμ ≤ θ μ(V)`.  Reindex by the countable subtype `↥t`; countable additivity gives
`∑ᵢ ∫_{B(i)} g dμ = ∫_V g dμ` and `∑ᵢ μ(B(i)) = μ(V) < ∞`, so the real series `∑ᵢ θ μ(B(i))`
converges to `θ μ(V)`, and the two series compare term by term (no sign condition on `θ`). -/
theorem Submission.cbrldvc_setIntegral_biUnion_le_mul_measure : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (t : Set (Euclid P)) (B : Euclid P → Set (Euclid P)), t.Countable → (∀ x ∈ t, MeasurableSet (B x)) → t.PairwiseDisjoint B → μ (⋃ x ∈ t, B x) < ∞ → IntegrableOn g (⋃ x ∈ t, B x) μ → (∀ x ∈ t, ∫ y in B x, g y ∂μ ≤ θ * (μ (B x)).toReal) → ∫ y in ⋃ x ∈ t, B x, g y ∂μ ≤ θ * (μ (⋃ x ∈ t, B x)).toReal := by
  intro P μ g θ t B ht hB hd hfin hg hle
  -- reindex `⋃ x ∈ t, B x` as `⋃ i : t, B i` over the countable subtype
  have : Countable t := ht.to_subtype
  have hBi : ∀ i : t, MeasurableSet (B i) := fun i => hB i i.2
  have hdi : Pairwise (Disjoint on fun i : t => B i) :=
    fun i j hij => hd i.2 j.2 (Subtype.coe_injective.ne hij)
  rw [biUnion_eq_iUnion] at hfin hg ⊢
  -- countable additivity of the integral
  have hint : HasSum (fun i : t => ∫ y in B i, g y ∂μ) (∫ y in ⋃ i : t, B i, g y ∂μ) :=
    hasSum_integral_iUnion hBi hdi hg
  -- countable additivity of the measure, read in `ℝ`
  have hμ : μ (⋃ i : t, B i) = ∑' i : t, μ (B i) := measure_iUnion hdi hBi
  have hfin' : ∑' i : t, μ (B i) ≠ ∞ := hμ ▸ hfin.ne
  have hmeas : HasSum (fun i : t => (μ (B i)).toReal) (μ (⋃ i : t, B i)).toReal := by
    rw [hμ, ENNReal.tsum_toReal_eq fun i => ENNReal.ne_top_of_tsum_ne_top hfin' i]
    exact ENNReal.hasSum_toReal hfin'
  -- compare the two series term by term
  exact hasSum_le (fun i : t => hle i i.2) hint (hmeas.mul_left θ)
/-- Complement bound in the covering step of the lower density estimate (cf. Simon Ch. 6, 8.2): if
`|g| ≤ 1` `μ`-a.e., `V ⊆ W` with `V` measurable, `μ W < ∞` and `∫_V g dμ ≤ θ μ(V)`, then
`∫_W g dμ = ∫_{W∖V} g dμ + ∫_V g dμ ≤ (μ(W) − μ(V)) + θ μ(V) = μ(W) − (1 − θ) μ(V)`. -/
theorem Submission.cbrldvc_setIntegral_le_sub_of_subset : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (V W : Set (Euclid P)), AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → MeasurableSet V → V ⊆ W → μ W < ∞ → ∫ y in V, g y ∂μ ≤ θ * (μ V).toReal → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ V).toReal := by
  intro P μ g θ V W hg hbd hV hVW hW hθ
  -- `μ V ≤ μ W < ∞` and `μ (W \ V) ≤ μ W < ∞`
  have hVW_le : μ V ≤ μ W := measure_mono hVW
  have hVfin : μ V ≠ ∞ := (hVW_le.trans_lt hW).ne
  have hWVfin : μ (W \ V) ≠ ∞ := ((measure_mono sdiff_subset).trans_lt hW).ne
  -- `|g| ≤ 1` a.e. makes `g` integrable on every set of finite measure
  have hgS : ∀ S : Set (Euclid P), μ S ≠ ∞ → IntegrableOn g S μ := fun S hS =>
    Measure.integrableOn_of_bounded (M := 1) hS hg
      (by filter_upwards [ae_restrict_of_ae hbd] with x hx; rwa [Real.norm_eq_abs])
  have hgV : IntegrableOn g V μ := hgS V hVfin
  have hgWV : IntegrableOn g (W \ V) μ := hgS (W \ V) hWVfin
  -- `∫_W g = ∫_{W∖V} g + ∫_V g`
  have hsplit : ∫ y in W, g y ∂μ = ∫ y in W \ V, g y ∂μ + ∫ y in V, g y ∂μ := by
    conv_lhs => rw [← sdiff_union_of_subset hVW]
    exact setIntegral_union disjoint_sdiff_left hV hgWV hgV
  -- `∫_{W∖V} g ≤ ∫_{W∖V} 1 = μ(W ∖ V)`
  have hcomp : ∫ y in W \ V, g y ∂μ ≤ (μ (W \ V)).toReal := by
    calc ∫ y in W \ V, g y ∂μ ≤ ∫ _ in W \ V, (1 : ℝ) ∂μ :=
          integral_mono_ae hgWV (integrableOn_const hWVfin)
            (by filter_upwards [ae_restrict_of_ae hbd] with x hx; exact (le_abs_self _).trans hx)
      _ = (μ (W \ V)).toReal := by rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  -- `μ(W ∖ V) = μ(W) − μ(V)`
  have hdiff : (μ (W \ V)).toReal = (μ W).toReal - (μ V).toReal := by
    rw [measure_sdiff hVW hV.nullMeasurableSet hVfin, ENNReal.toReal_sub_of_le hVW_le hW.ne]
  rw [hsplit]
  linarith

/-- **Covering inequality for the set integral of a bounded density** (the covering in the proof
of Simon Ch. 6, 8.2 after (4): pairwise disjoint closed balls covering almost all of the low
density set, with total measure at most `μ(W)`).  Let `μ` be finite on compact subsets of `ℝᴾ`,
`|g| ≤ 1` `μ`-a.e., `θ ≤ 1`, `W` open with `μ(W) < ∞`, and let every point of `E ⊆ W` be the
centre of arbitrarily small closed balls `B̄_ρ(x)` with `∫_{B̄_ρ(x)} g dμ ≤ θ μ(B̄_ρ(x))`.
Besicovitch gives countably many such balls, pairwise disjoint and contained in `W`, whose
union `V` covers `μ`-almost all of `E`.  By countable additivity `∫_V g dμ ≤ θ μ(V)`, and `g ≤ 1`
on `W \ V`, so `∫_W g dμ ≤ μ(W) − (1 − θ) μ(V) ≤ μ(W) − (1 − θ) μ(E)`. -/
theorem Submission.cbrld_vitali_setIntegral_le : ∀ (P : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (θ : ℝ) (E W : Set (Euclid P)), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable g μ → (∀ᵐ x ∂μ, |g x| ≤ 1) → θ ≤ 1 → IsOpen W → E ⊆ W → μ W < ∞ → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∫ y in closedBall x ρ, g y ∂μ ≤ θ * (μ (closedBall x ρ)).toReal) → ∫ y in W, g y ∂μ ≤ (μ W).toReal - (1 - θ) * (μ E).toReal := by
  intro P μ g θ E W hK hg hg1 hθ hW hEW hWfin hsmall
  -- steps 1–3: countably many pairwise disjoint admissible balls `B̄_{r(x)}(x) ⊆ W`, `x ∈ t`,
  -- covering `μ`-almost all of `E`
  obtain ⟨t, r, htc, -, hr, hdisj, hnull⟩ :=
    Submission.cbrldvc_exists_disjoint_closedBall_cover P μ
      (fun x ρ => ∫ y in closedBall x ρ, g y ∂μ ≤ θ * (μ (closedBall x ρ)).toReal) E W hK hW hEW
      hsmall
  -- step 4: their union `V` is measurable, `V ⊆ W`, `μ(V) < ∞` and `μ(E) ≤ μ(V)`
  have hVmeas : MeasurableSet (⋃ x ∈ t, closedBall x (r x)) :=
    MeasurableSet.biUnion htc fun _ _ => measurableSet_closedBall
  have hVW : ⋃ x ∈ t, closedBall x (r x) ⊆ W := iUnion₂_subset fun x hx => (hr x hx).2.1
  have hVfin : μ (⋃ x ∈ t, closedBall x (r x)) < ∞ := (measure_mono hVW).trans_lt hWfin
  have hEV : μ E ≤ μ (⋃ x ∈ t, closedBall x (r x)) := measure_mono_ae (ae_le_set.2 hnull)
  -- step 5: `∫_V g dμ ≤ θ μ(V)`, summing over the disjoint balls
  have hgV : IntegrableOn g (⋃ x ∈ t, closedBall x (r x)) μ :=
    Measure.integrableOn_of_bounded hVfin.ne hg (M := 1)
      (ae_restrict_of_ae (hg1.mono fun x hx => by rwa [Real.norm_eq_abs]))
  have hV : ∫ y in ⋃ x ∈ t, closedBall x (r x), g y ∂μ ≤
      θ * (μ (⋃ x ∈ t, closedBall x (r x))).toReal :=
    Submission.cbrldvc_setIntegral_biUnion_le_mul_measure P μ g θ t (fun x => closedBall x (r x))
      htc (fun _ _ => measurableSet_closedBall) hdisj hVfin hgV fun x hx => (hr x hx).2.2
  -- steps 6–7: `g ≤ 1` on `W \ V`; then `μ(E) ≤ μ(V)` and `1 − θ ≥ 0`
  calc ∫ y in W, g y ∂μ
      ≤ (μ W).toReal - (1 - θ) * (μ (⋃ x ∈ t, closedBall x (r x))).toReal :=
        Submission.cbrldvc_setIntegral_le_sub_of_subset P μ g θ _ W hg hg1 hVmeas hVW hWfin hV
    _ ≤ (μ W).toReal - (1 - θ) * (μ E).toReal :=
        sub_le_sub_left (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hVfin.ne hEV)
          (sub_nonneg.2 hθ)) _
/-- **Degree-zero mass gap** (Simon Ch. 6, footnote 5 to 8.2, the case `n = 1`), assuming the
mass representation `(MR)` `M_W(T) = μ_T(W)` for open `U`, `W`: an integer multiplicity
`0`-current `Z` in `ℝᴾ` with `M(Z) < 1` is zero.  If `Z = τ(M, θ, ξ)` and `x ∈ M`, then
`M(Z) = μ_Z(ℝᴾ) ≥ μ_Z({x}) = θ(x) H⁰({x}) = θ(x) ≥ 1`; hence `M = ∅` and every `Z(ω)` is an
integral over `∅`. -/
theorem Submission.cbrld_im_degree_zero_eq_zero_of_mass_lt_one : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P : ℕ) (Z : GeometricCurrentOn (univ : Set (Euclid P)) 0), IsIntegerMultiplicity Z → Z.mass < 1 → Z = 0 := by
  rintro hMR P Z ⟨R, hR⟩ hZ
  -- `(MR)` with `U = W = ℝᴾ`: `M(Z) = μ_Z(ℝᴾ)`
  have hmass : Z.mass = R.measure univ := hMR P 0 univ Z R isOpen_univ hR univ isOpen_univ
  -- a point `x ∈ M` would carry `μ_Z({x}) = θ(x) H⁰({x}) = θ(x) ≥ 1 > M(Z)`
  have hempty : R.carrier = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hx1 : R.measure {x} = (R.mult x : ℝ≥0∞) := by
      rw [IMRep.measure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
        Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_mem hx,
        Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton, mul_one]
    have h1 : (1 : ℝ≥0∞) ≤ R.measure {x} := hx1 ▸ Nat.one_le_cast.2 (R.mult_pos x hx)
    exact not_le.2 hZ (h1.trans ((measure_mono (subset_univ _)).trans hmass.ge))
  -- every `Z(ω)` is an integral over `M = ∅`
  ext ω
  rw [hR ω, GeometricCurrentOn.zero_apply, IMRep.action, hempty, setIntegral_empty]
/-- **Simon Ch. 6, proof of 8.2, (2)–(4)**, with the lower density in place of `Θ^{*n}`: small
fillings of sphere slices at points of small lower density.  For `n = d + 1` fix `a > 0` (`a = 1/4`
if `n = 1`; for `n = m + 2`, `cbrldlf_exists_filling_constant` for the constant `c` of (ISO)) and
put `η₀ = aⁿ/ωₙ`.  A scale `s ∈ (0, δ)` with `μ(B_s(x₁)) < (as)ⁿ`
(`cbrldlf_exists_small_scale_of_lower_density`) and the null set of
`cbrld_sphere_slice_isIntegerMultiplicity` give a good radius `ρ ∈ (0, s)`
(`cbrld_exists_good_slice_radius`): `A = C⌞B_ρ(x₁)` has an integer multiplicity boundary `Z = ∂A`
with `spt Z ⊆ ∂B_ρ(x₁)` and `M(Z) ≤ 2naF^{(n−1)/n}`, `F = μ(B_ρ(x₁))`.  If `n = 1`, then
`M(Z) ≤ 1/2`, so `Z = 0` (`cbrld_im_degree_zero_eq_zero_of_mass_lt_one`) and `S = 0`; if `n ≥ 2`,
`S` is the filling of `Z` given by (ISO), with `M(S) ≤ F/2` and `spt S` within `3√P·s` of
`∂B_ρ(x₁)`. -/
theorem Submission.cbrld_exists_small_filling_of_low_density : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P m : ℕ), ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support) → ∀ (P d : ℕ), ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∀ x₁ : Euclid P, liminf (fun r : ℝ => μ (ball x₁ r) / (unitBallVolume (d + 1) * ENNReal.ofReal (r ^ (d + 1)))) (𝓝[>] 0) < ENNReal.ofReal η₀ → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ μ (sphere x₁ ρ) = 0 ∧ ∃ (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in ball x₁ ρ, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ S.boundary = A.boundary ∧ S.mass ≤ ENNReal.ofReal (1 / 2) * μ (ball x₁ ρ) ∧ S.support ⊆ closedBall x₁ ((1 + 3 * Real.sqrt P) * δ) := by
  intro hSL hMR hISO P d
  -- Steps 1, 4 and 5: the choice of `a` and the filling of the sphere slice
  suffices H : ∃ a : ℝ, 0 < a ∧ ∀ (x₁ : Euclid P) (δ s ρ F : ℝ)
      (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), 0 < s → ρ < s → s < δ → 0 ≤ F →
      F ≤ (a * s) ^ (d + 1) → IsIntegerMultiplicity A.boundary →
      A.boundary.support ⊆ sphere x₁ ρ →
      A.boundary.mass ≤ ENNReal.ofReal (2 * ((d + 1 : ℕ) : ℝ) * a *
        F ^ ((((d + 1 : ℕ) : ℝ) - 1) / ((d + 1 : ℕ) : ℝ))) →
      ∃ S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), S.boundary = A.boundary ∧
        S.mass ≤ ENNReal.ofReal (F / 2) ∧ S.support ⊆ closedBall x₁ ((1 + 3 * Real.sqrt P) * δ) by
    obtain ⟨a, ha, H⟩ := H
    -- Step 0: `ωₙ > 0`; Step 1: `η₀ = aⁿ/ωₙ`
    obtain ⟨hw, hsmall⟩ := Submission.cbrldlf_exists_small_scale_of_lower_density (d + 1)
    refine ⟨a ^ (d + 1) / (unitBallVolume (d + 1)).toReal, div_pos (pow_pos ha _) hw, ?_⟩
    intro C μ ξ hCb hμ hξm hξb hC hISP x₁ hlim δ hδ
    -- Step 2: a scale `s ∈ (0, δ)` with `μ(B_s(x₁)) < η₀ωₙsⁿ = (as)ⁿ`
    obtain ⟨s, hs, hsδ, hμs⟩ := hsmall P μ x₁ _ δ hδ hlim
    rw [div_mul_cancel₀ _ hw.ne', ← mul_pow] at hμs
    -- Step 3: a good radius `ρ ∈ (0, s)` off the null set of the slices, and `A = C⌞B_ρ(x₁)`
    obtain ⟨N, hN, hslice⟩ :=
      Submission.cbrld_sphere_slice_isIntegerMultiplicity hSL P d C μ ξ x₁ hCb hμ hξm hξb hC hISP
    obtain ⟨ρ, hρ, hρs, hρN, hsph, hlimρ⟩ :=
      Submission.cbrld_exists_good_slice_radius P (d + 1) μ x₁ a s N hμ (by omega) ha hs hμs hN
    obtain ⟨A, hA, hAim, hAspt, hAmass⟩ := hslice ρ hρ hρN
    -- `F = μ(B_ρ(x₁)) ≤ μ(B_s(x₁)) < (as)ⁿ`
    have hμρ : μ (ball x₁ ρ) ≤ μ (ball x₁ s) := measure_mono (ball_subset_ball hρs.le)
    have hμρ_ne : μ (ball x₁ ρ) ≠ ∞ := (hμρ.trans_lt (hμs.trans ENNReal.ofReal_lt_top)).ne
    have hF : (μ (ball x₁ ρ)).toReal ≤ (a * s) ^ (d + 1) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hμρ.trans hμs.le)
    obtain ⟨S, hSb, hSmass, hSspt⟩ := H x₁ δ s ρ (μ (ball x₁ ρ)).toReal A hs hρs hsδ
      ENNReal.toReal_nonneg hF hAim hAspt (hAmass.trans hlimρ)
    -- Step 6
    refine ⟨ρ, hρ, hρs.trans hsδ, hsph, A, S, hA, hSb, ?_, hSspt⟩
    calc S.mass ≤ ENNReal.ofReal ((μ (ball x₁ ρ)).toReal / 2) := hSmass
      _ = ENNReal.ofReal (1 / 2) * μ (ball x₁ ρ) := by
        rw [show (μ (ball x₁ ρ)).toReal / 2 = 1 / 2 * (μ (ball x₁ ρ)).toReal by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ENNReal.ofReal_toReal hμρ_ne]
  cases d with
  | zero =>
    -- Step 4 (`n = 1`, `a = 1/4`): `M(∂A) ≤ 2a = 1/2 < 1`, so `∂A = 0` and `S = 0`
    refine ⟨1 / 4, by norm_num, fun x₁ δ s ρ F A _ _ _ _ _ hAim _ hAmass => ?_⟩
    have hZ : A.boundary = 0 := by
      refine Submission.cbrld_im_degree_zero_eq_zero_of_mass_lt_one hMR P _ hAim
        (hAmass.trans_lt ?_)
      rw [ENNReal.ofReal_lt_one]
      norm_num
    refine ⟨0, ?_, ?_, ?_⟩
    · rw [hZ]
      exact GeometricCurrentOn.ext fun ω => rfl
    · -- every value of the zero current is `0`
      refine sSup_le ?_
      rintro _ ⟨ω, -, rfl⟩
      simp
    · -- the zero current vanishes on every ball `B₁(y)`
      intro y hy
      exfalso
      apply hy.2
      exact Set.mem_sUnion_of_mem (mem_ball_self one_pos) ⟨isOpen_ball,
        (isCompact_closedBall y 1).of_isClosed_subset isClosed_closure
          closure_ball_subset_closedBall, subset_univ _, fun ω _ => rfl⟩
  | succ m =>
    -- Step 5 (`n = m + 2`): `S` is the filling of `Z = ∂A` given by (ISO)
    obtain ⟨c, hc, hiso⟩ := hISO P m
    obtain ⟨a, ha, hconst⟩ := Submission.cbrldlf_exists_filling_constant m c hc
    refine ⟨a, ha, fun x₁ δ s ρ F A hs hρs hsδ hF0 hF hAim hAspt hAmass => ?_⟩
    -- `∂Z = ∂∂A = 0`, `spt Z` is a closed subset of the sphere `∂B_ρ(x₁)` and `M(Z) < ∞`
    have hZb : A.boundary.boundary = 0 := GeometricCurrentOn.boundary_boundary A
    have hZcpt : IsCompact A.boundary.support := by
      refine (isCompact_sphere x₁ ρ).of_isClosed_subset ?_ hAspt
      rw [GeometricCurrentOn.support, ← Set.compl_eq_univ_sdiff]
      exact A.boundary.isOpen_zeroRegion.isClosed_compl
    obtain ⟨Y, -, hYb, hYmass, hYspt⟩ :=
      hiso A.boundary hAim hZcpt hZb (hAmass.trans_lt ENNReal.ofReal_lt_top)
    -- (a) `M(Y) ≤ F/2` and (b) `(2cM(Z))^{1/(m+1)} ≤ s`
    have hM := ENNReal.toReal_le_of_le_ofReal (by positivity) hAmass
    obtain ⟨hmass, hrad⟩ := hconst s F _ hs.le hF0 hF ENNReal.toReal_nonneg hM
    refine ⟨Y, hYb, hYmass.trans (ENNReal.ofReal_le_ofReal hmass), fun y hy => ?_⟩
    -- `y` lies within `3√P·s` of a point `z` of `spt Z ⊆ ∂B_ρ(x₁)`, and `ρ < s < δ`
    obtain ⟨z, hz, hyz⟩ := Metric.mem_thickening_iff.mp (hYspt hy)
    have hzx : dist z x₁ = ρ := hAspt hz
    have h3 := mul_le_mul_of_nonneg_left (hrad.trans hsδ.le)
      (by positivity : (0 : ℝ) ≤ 3 * Real.sqrt P)
    rw [Metric.mem_closedBall]
    linarith [dist_triangle y z x₁]

/-- **Comparison with a small filling** (Simon Ch. 6, proof of Theorem 8.2, (4)–(6), pp. 177–178,
for a single test form).  Suppose `∂S = ∂A` in `ℝᴾ`, `M(A) ≤ m < ∞`, `M(S) ≤ κm`,
`spt A, spt S ⊆ B̄_R(x)`, `|ω| ≤ 1`, and `ω` satisfies the cone inequality `|X(ω)| ≤ cϱM(X)` for
every cycle `X` of finite mass supported in a closed ball of radius `ϱ`.  Then `X = S − A` is such
a cycle, with `M(X) ≤ M(S) + M(A) ≤ (1 + κ)m` and `spt X ⊆ spt S ∪ spt A ⊆ B̄_R(x)`, so
`|X(ω)| ≤ cR(1 + κ)m`; and `S(ω) ≤ M(S) ≤ κm` because `ω` is admissible.  Hence
`A(ω) = S(ω) − X(ω) ≤ (κ + cR(1 + κ))m`. -/
theorem Submission.cbrld_ns_eval_le_of_small_filling : ∀ (P d : ℕ) (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (ω : TestFormOn (univ : Set (Euclid P)) (d + 1)) (m : ℝ≥0∞) (x : Euclid P) (c κ R : ℝ), 0 ≤ c → 0 ≤ κ → 0 < R → m < ∞ → (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) (d + 1)) y) ≤ 1) → (∀ (X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (x₀ : Euclid P) (ϱ : ℝ), 0 < ϱ → X.boundary = 0 → X.mass < ∞ → X.support ⊆ closedBall x₀ ϱ → |X ω| ≤ c * ϱ * X.mass.toReal) → S.boundary = A.boundary → A.mass ≤ m → S.mass ≤ ENNReal.ofReal κ * m → A.support ⊆ closedBall x R → S.support ⊆ closedBall x R → A ω ≤ (κ + c * R * (1 + κ)) * m.toReal := by
  intro P d A S ω m x c κ R hc hκ hR hm hω hcone hbd hA hS hsptA hsptS
  -- Step 1: the comparison current `X = S − A`, with `X(η) = S(η) − A(η)`.
  set X : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1) := S - A
  have hXapp : ∀ η, X η = S η - A η := fun _ => rfl
  -- Step 2: `∂X(η) = S(dη) − A(dη) = ∂S(η) − ∂A(η) = 0`.
  have hXbd : X.boundary = 0 := by
    ext η
    rw [GeometricCurrentOn.boundary_apply, hXapp, ← GeometricCurrentOn.boundary_apply,
      ← GeometricCurrentOn.boundary_apply, hbd, sub_self, GeometricCurrentOn.zero_apply]
  -- Step 3: `M(X) ≤ M(S) + M(A) ≤ κm + m < ∞`, hence `M(X) ≤ (1 + κ)m` as real numbers.
  have hκm : ENNReal.ofReal κ * m < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm
  have hsum : ENNReal.ofReal κ * m + m < ∞ := ENNReal.add_lt_top.2 ⟨hκm, hm⟩
  have hXmass : X.mass ≤ ENNReal.ofReal κ * m + m :=
    (Submission.cbrld_ns_massOn_sub_le P (d + 1) univ univ S A).trans (add_le_add hS hA)
  have hXfin : X.mass < ∞ := hXmass.trans_lt hsum
  have hXreal : X.mass.toReal ≤ (1 + κ) * m.toReal := by
    have h := ENNReal.toReal_mono hsum.ne hXmass
    rw [ENNReal.toReal_add hκm.ne hm.ne, ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at h
    linarith
  -- Step 4: `spt X ⊆ spt S ∪ spt A ⊆ B̄_R(x)`.
  have hXspt : X.support ⊆ closedBall x R :=
    (Submission.cbrld_ns_support_sub_subset P (d + 1) univ S A).trans (union_subset hsptS hsptA)
  -- Step 5: the cone inequality at `(x, R)`: `|X(ω)| ≤ cR·M(X) ≤ cR(1 + κ)m`.
  have hXω : |X ω| ≤ c * R * ((1 + κ) * m.toReal) :=
    (hcone X x R hR hXbd hXfin hXspt).trans
      (mul_le_mul_of_nonneg_left hXreal (mul_nonneg hc hR.le))
  -- Step 6: `ω` is `ℝᴾ`-admissible, so `S(ω) ≤ M(S) ≤ κm`.
  have hSω : S ω ≤ κ * m.toReal := by
    have hadm : ω ∈ massAdmissibleOn (univ : Set (Euclid P)) (d + 1) univ :=
      ⟨subset_univ _, hω⟩
    have h := (ENNReal.ofReal_le_iff_le_toReal hκm.ne).1 ((S.le_massOn hadm).trans hS)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] at h
  -- Step 7: `A(ω) = S(ω) − X(ω) ≤ S(ω) + |X(ω)| ≤ κm + cR(1 + κ)m`.
  have hAω : A ω = S ω - X ω := by rw [hXapp]; ring
  rw [hAω]
  linarith [neg_le_abs (X ω)]
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

/-- **Simon Ch. 6, 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U`, then
`M_W(T) = μ_R(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  The upper bound
`dor_ims_massOn_le_measure` and the lower bound `dor_ims_measure_le_massOn` give equality by
antisymmetry. -/
theorem Submission.cmc_massOn_eq_imRep_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := by
  intro P n U T R hU hR W hW
  exact le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
    (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
/-- **Simon 6.1.1–1.2** (coordinate covectors): (a) for every `I` the coordinate covector
`dx^I(v) = det(v_j(I k))_{k,j}` exists; (b) an `n`-vector vanishing on `dx^I` for every strictly
increasing `I` vanishes.  Every `n`-covector expands as `α = Σ_I α(e_I) dx^I` over strictly
increasing `I`: by `dx^I(e_J) = δ_IJ` the remainder vanishes on every `e_J`, so its coefficient
norm `|·|_E` is `0`, and `|·|_E` is the norm of a linear isomorphism onto `ℝᵈ`. -/
theorem Submission.cmr_coordinate_covectors_span : ∀ (P n : ℕ), (∀ I : Fin n → Fin P, ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) ∧ ∀ ζ : MultiVector P n, (∀ (I : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ζ θ = 0) → ζ = 0 := by
  intro P n
  refine ⟨Submission.cmr_cc_det_covector_exists P n, fun ζ hζ => ?_⟩
  classical
  -- `θ I = dx^I` for every `I`
  choose θ hθ using Submission.cmr_cc_det_covector_exists P n
  -- `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`
  have hδ : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      θ I (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 :=
    fun I J hI hJ => Submission.cmr_cc_det_covector_basis_kronecker P n I J (θ I) hI hJ (hθ I)
  -- `α = Σ_I α(e_I) dx^I` over strictly increasing `I`
  have hexp : ∀ α : Covector (Euclid P) n, α = ∑ I : Fin n → Fin P,
      if StrictMono I then α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) • θ I
      else 0 := by
    intro α
    obtain ⟨α', hα'⟩ : ∃ α', α' = α - ∑ I : Fin n → Fin P,
        if StrictMono I then α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)) • θ I
        else 0 := ⟨_, rfl⟩
    -- `α'(e_J) = α(e_J) - Σ_I α(e_I) δ_IJ = 0` for strictly increasing `J`
    have hJ : ∀ J : Fin n → Fin P, StrictMono J →
        α' (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = 0 := by
      intro J hJ
      rw [hα', ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.sum_apply,
        Finset.sum_eq_single J, ite_eq_left hJ, ContinuousAlternatingMap.smul_apply,
        hδ J J hJ hJ, ite_eq_left rfl, smul_eq_mul, mul_one, sub_self]
      · intro I _ hIJ
        split_ifs with hI
        · rw [ContinuousAlternatingMap.smul_apply, hδ I J hI hJ, ite_eq_right hIJ, smul_zero]
        · rfl
      · intro h
        exact absurd (Finset.mem_univ J) h
    -- so `|α'|_E = 0`, and `α' = 0` as `|·|_E` is the norm of a linear isomorphism onto `ℝᵈ`
    have hnorm : covectorEuclideanNorm α' = 0 := by
      unfold covectorEuclideanNorm
      rw [Finset.sum_eq_zero fun I _ => ?_, Real.sqrt_zero]
      split_ifs with hI
      · rw [hJ I hI, sq, mul_zero]
      · rfl
    obtain ⟨d, c, hc⟩ := Submission.cmr_covector_euclidean_equiv P n
    have hc0 : c α' = 0 := norm_eq_zero.mp ((hc α').symm.trans hnorm)
    rw [c.map_eq_zero_iff, hα'] at hc0
    exact sub_eq_zero.mp hc0
  -- `ζ` vanishes on every `dx^I`, hence on every covector
  refine ContinuousLinearMap.ext fun α => ?_
  rw [zero_apply, hexp α, map_sum]
  refine Finset.sum_eq_zero fun I _ => ?_
  split_ifs with hI
  · rw [map_smul, hζ I (θ I) hI (hθ I), smul_zero]
  · exact map_zero ζ
/-- **Extension of a current of locally finite mass to `C_c(U, ℝᵈ)`** (Simon Ch. 6, the remark
after 2.6 applying the Riesz representation theorem, Ch. 1, 4.14).  By hypothesis
`M_W(T) < ∞` for open `W ⊂⊂ U`, so `cmr_abs_apply_le_massOn` gives `|T(ω)| ≤ r M_W(T)` when
`spt ω ⊆ W` and `|ω| ≤ r`.  Hence `cmr_tfe_ambient_extension` extends `T` to a functional `Φ` on
continuous compactly supported covector fields in `U`, additive and homogeneous on them, with
`|Φ(G)| ≤ r M_W(T)` when `spt G ⊆ W` and `|G| ≤ r`.  For `g ∈ C_c(U, ℝᵈ)` let `g̃ = c⁻¹ ∘ g` on
`U` and `g̃ = 0` off `U` (`Function.extend`).  Then `g̃` is continuous with compact support,
`spt g̃ ⊆ spt g ⊆ U`, and `g ↦ g̃` is linear, so `L(g) = Φ(g̃)` is linear.  If `g = c ∘ ω` on `U`,
then `g̃ = ω`, so `L(g) = T(ω)`.  If `spt g ⊆ K` and `‖g‖ ≤ 1`, then `|g̃| = ‖c g̃‖ ≤ 1` and
`spt g̃ ⊆ W` for a fixed open `W ⊂⊂ U` containing `K`, so `|L(g)| ≤ M_W(T)`. -/
theorem Submission.cmr_testForm_extension_functional : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (d : ℕ) (c : Covector (Euclid P) n ≃L[ℝ] EuclideanSpace ℝ (Fin d)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖c α‖) → ∃ L : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ, (∀ (ω : TestFormOn U n) (g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d))), (∀ x : U, g x = c ((ω : DifferentialForm (Euclid P) n) x)) → L g = T ω) ∧ ∀ K : Set U, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M := by
  intro P n U T d c hU hfin hc
  -- (1) `Φ`, for the local mass bound `m W = M_W(T)` (finite for open `W ⊂⊂ U`)
  obtain ⟨Φ, hΦadd, hΦsmul, hΦT, hΦle⟩ := Submission.cmr_tfe_ambient_extension P n d c U T
    (fun W => (T.massOn W).toReal) hU hc fun W ω r hW hWU hωW hωr =>
      Submission.cmr_abs_apply_le_massOn P n U W T ω r (hfin W hW hWU).ne hωW hωr
  -- (2) the zero extension `g̃`: `c⁻¹ ∘ g` on `U`, `0` off `U`
  let G : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)) →
      Euclid P → Covector (Euclid P) n := fun g =>
    Function.extend Subtype.val (fun x : U => c.symm (g x)) 0
  have hGU : ∀ g (x : U), G g x = c.symm (g x) := fun g x =>
    Subtype.val_injective.extend_apply _ _ x
  have hGnU : ∀ g (y : Euclid P), y ∉ U → G g y = 0 := fun g y hy =>
    Function.extend_apply' _ _ y fun ⟨x, hx⟩ => hy (hx ▸ x.2)
  have hgc : ∀ g : CompactlySupportedContinuousMap U (EuclideanSpace ℝ (Fin d)),
      HasCompactSupport fun x : U => c.symm (g x) := fun g =>
    g.hasCompactSupport.comp_left (map_zero c.symm)
  have hGcont : ∀ g, Continuous (G g) := fun g =>
    HasCompactSupport.continuous_extend_zero hU (c.symm.continuous.comp g.continuous) (hgc g)
  have hGcs : ∀ g, HasCompactSupport (G g) := fun g =>
    (hgc g).extend_zero continuous_subtype_val
  have hGsupp : ∀ g, tsupport (G g) ⊆ Subtype.val '' tsupport g := fun g =>
    ((hgc g).tsupport_extend_zero_subset continuous_subtype_val).trans
      (image_mono (tsupport_comp_subset (map_zero c.symm) g))
  have hGsU : ∀ g, tsupport (G g) ⊆ U := fun g =>
    (hGsupp g).trans (Subtype.coe_image_subset U _)
  have hGadd : ∀ g₁ g₂, G (g₁ + g₂) = G g₁ + G g₂ := by
    intro g₁ g₂
    funext y
    by_cases hy : y ∈ U
    · obtain ⟨x, rfl⟩ : ∃ x : U, (x : Euclid P) = y := ⟨⟨y, hy⟩, rfl⟩
      rw [Pi.add_apply, hGU, hGU, hGU, CompactlySupportedContinuousMap.add_apply, map_add]
    · rw [Pi.add_apply, hGnU _ y hy, hGnU _ y hy, hGnU _ y hy, add_zero]
  have hGsmul : ∀ (t : ℝ) g, G (t • g) = t • G g := by
    intro t g
    funext y
    by_cases hy : y ∈ U
    · obtain ⟨x, rfl⟩ : ∃ x : U, (x : Euclid P) = y := ⟨⟨y, hy⟩, rfl⟩
      rw [Pi.smul_apply, hGU, hGU, CompactlySupportedContinuousMap.smul_apply, map_smul]
    · rw [Pi.smul_apply, hGnU _ y hy, hGnU _ y hy, smul_zero]
  -- (3) `L g = Φ g̃` is linear
  refine ⟨{ toFun := fun g => Φ (G g)
            map_add' := fun g₁ g₂ => by
              show Φ (G (g₁ + g₂)) = Φ (G g₁) + Φ (G g₂)
              rw [hGadd, hΦadd _ _ (hGcont g₁) (hGcs g₁) (hGsU g₁) (hGcont g₂) (hGcs g₂)
                (hGsU g₂)]
            map_smul' := fun t g => by
              show Φ (G (t • g)) = t • Φ (G g)
              rw [hGsmul, hΦsmul t _ (hGcont g) (hGcs g) (hGsU g), smul_eq_mul] }, ?_, ?_⟩
  · -- (i) `g = c ∘ ω` on `U` forces `g̃ = ω`
    intro ω g hg
    have hωU : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.property.2
    have hGω : G g = (ω : DifferentialForm (Euclid P) n) := by
      funext y
      by_cases hy : y ∈ U
      · obtain ⟨x, rfl⟩ : ∃ x : U, (x : Euclid P) = y := ⟨⟨y, hy⟩, rfl⟩
        rw [hGU, hg, c.symm_apply_apply]
      · have hy' : y ∉ tsupport (ω : DifferentialForm (Euclid P) n) := fun h => hy (hωU h)
        rw [hGnU g y hy, image_eq_zero_of_notMem_tsupport hy']
    show Φ (G g) = T ω
    rw [hGω, hΦT]
  · -- (ii) an open `W ⊂⊂ U` containing `K`, and `|Φ g̃| ≤ 1 · M_W(T)` for unit fields `g`
    intro K hK
    obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
      (hK.image continuous_subtype_val) hU (Subtype.coe_image_subset U K)
    refine ⟨1 * (T.massOn W).toReal, fun g hgK hg1 => ?_⟩
    show |Φ (G g)| ≤ 1 * (T.massOn W).toReal
    refine hΦle W (G g) 1 hW ⟨hWc, hWU⟩ (hGcont g) (hGcs g)
      ((hGsupp g).trans ((image_mono hgK).trans hKW)) fun y => ?_
    rw [hc]
    by_cases hy : y ∈ U
    · obtain ⟨x, rfl⟩ : ∃ x : U, (x : Euclid P) = y := ⟨⟨y, hy⟩, rfl⟩
      rw [hGU, c.apply_symm_apply]
      exact hg1 x
    · rw [hGnU g y hy, map_zero, norm_zero]
      exact zero_le_one
/-- Coordinate functionals of a locally bounded `L : C_c(X, ℝᵈ) → ℝ`: `Λᵢ(f) = L(f • eᵢ)` is
linear and locally bounded with the same constants.  `T f := f.compLeft (t ↦ t • eᵢ)` is linear
with `(T f)(x) = f(x) • eᵢ`, `tsupport (T f) ⊆ tsupport f` and `‖(T f)(x)‖ = |f(x)|`;
take `Λᵢ := L ∘ T`. -/
theorem Submission.cmr_vr_coordinate_functional : ∀ (X : Type) [TopologicalSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∀ i : Fin d, ∃ Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ, (∀ (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = Λ f) ∧ ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M := by
  intro X _ d L hL i
  -- `c t = t • eᵢ` is continuous and `c 0 = 0`, so `T f := f.compLeft c` has `(T f) x = f x • eᵢ`
  let c : C(ℝ, EuclideanSpace ℝ (Fin d)) :=
    ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), continuous_id.smul continuous_const⟩
  have hc0 : c 0 = 0 := zero_smul ℝ _
  have hT : ∀ (f : CompactlySupportedContinuousMap X ℝ) (x : X),
      f.compLeft c x = f x • EuclideanSpace.single i (1 : ℝ) :=
    fun f x => CompactlySupportedContinuousMap.compLeft_apply hc0 f x
  -- `T` is linear (pointwise, then extensionality); `Λ := L ∘ T`
  let T : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ]
      CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun f => f.compLeft c
      map_add' := fun f₁ f₂ => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.add_apply, add_smul]
      map_smul' := fun r f => CompactlySupportedContinuousMap.ext fun x => by
        simp only [hT, CompactlySupportedContinuousMap.smul_apply, RingHom.id_apply, smul_eq_mul,
          mul_smul] }
  refine ⟨L ∘ₗ T, fun f g hg => ?_, fun K hK => ?_⟩
  · -- `g = T f` by extensionality
    exact congrArg L (CompactlySupportedContinuousMap.ext fun x => (hg x).trans (hT f x).symm)
  · -- `tsupport (T f) ⊆ tsupport f ⊆ K` and `‖(T f) x‖ = |f x| ≤ 1`: same constant `M`
    obtain ⟨M, hM⟩ := hL K hK
    refine ⟨M, fun f hf hf1 => hM (T f) ?_ fun x => ?_⟩
    · have hTf : ⇑(T f) = fun x => f x • EuclideanSpace.single i (1 : ℝ) := funext (hT f)
      rw [hTf]
      exact (tsupport_smul_subset_left _ _).trans hf
    · show ‖f.compLeft c x‖ ≤ 1
      rw [hT, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      exact hf1 x
/-- Jordan decomposition of a locally bounded `Λ : C_c(X, ℝ) → ℝ`.  For `f : C_c(X, ℝ≥0)` put
`V f := sup {Λ h : |h| ≤ f}` (bounded above by rescaling the local bound on `tsupport f`).  `V` is
additive (clamp `h₁ := (h ⊓ f) ⊔ (-f)`) and `ℝ≥0`-homogeneous, so `V̂ := toRealPositiveLinear V`
is positive; `V̂ + Λ` is positive since `-k` is admissible for `k ≥ 0`, and `Λ = (V̂ + Λ) - V̂`. -/
theorem Submission.cmr_vr_jordan_decomposition : ∀ (X : Type) [TopologicalSpace X] (Λ : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, tsupport f ⊆ K → (∀ x, |f x| ≤ 1) → |Λ f| ≤ M) → ∃ Λ₁ Λ₂ : CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ, ∀ f : CompactlySupportedContinuousMap X ℝ, Λ f = Λ₁ f - Λ₂ f := by
  intro X _ Λ hΛ
  -- scaled bound: `tsupport f ⊆ K`, `|f| ≤ s` give `|Λ f| ≤ s * M_K` (`s = 0`, else rescale)
  have hscale : ∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ (f : CompactlySupportedContinuousMap X ℝ)
      (s : ℝ), tsupport f ⊆ K → 0 ≤ s → (∀ x, |f x| ≤ s) → |Λ f| ≤ s * M := by
    intro K hK
    obtain ⟨M, hM⟩ := hΛ K hK
    refine ⟨M, fun f s hfK hs hfs => ?_⟩
    rcases hs.eq_or_lt with rfl | hspos
    · have hf0 : f = 0 := by
        ext x
        simpa using hfs x
      simp [hf0]
    · have hsub : tsupport (s⁻¹ • f) ⊆ K :=
        (tsupport_smul_subset_right (fun _ : X => s⁻¹) f).trans hfK
      have hbd : ∀ x, |(s⁻¹ • f) x| ≤ 1 := by
        intro x
        rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
          abs_of_pos (inv_pos.mpr hspos)]
        calc s⁻¹ * |f x| ≤ s⁻¹ * s := mul_le_mul_of_nonneg_left (hfs x) (inv_pos.mpr hspos).le
          _ = 1 := inv_mul_cancel₀ hspos.ne'
      have h1 := hM _ hsub hbd
      rw [map_smul, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hspos)] at h1
      have := (inv_mul_le_iff₀ hspos).mp h1
      linarith
  -- `A f = {h : |h| ≤ f}` contains `0`, and `Λ '' A f` is bounded above: members of `A f` have
  -- `tsupport h ⊆ tsupport f` and `|h| ≤ max C 0` with `C` a bound for `f`
  let A : CompactlySupportedContinuousMap X NNReal → Set (CompactlySupportedContinuousMap X ℝ) :=
    fun f => {h | ∀ x, |h x| ≤ (f x : ℝ)}
  have hA0 : ∀ f, (0 : CompactlySupportedContinuousMap X ℝ) ∈ A f := by
    intro f x
    simp
  have hbdd : ∀ f, BddAbove (Λ '' A f) := by
    intro f
    obtain ⟨M, hM⟩ := hscale (tsupport f) f.hasCompactSupport.isCompact
    obtain ⟨C, hC⟩ := f.toReal.continuous.bounded_above_of_compact_support
      f.toReal.hasCompactSupport
    refine ⟨max C 0 * M, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have hsupp : tsupport h ⊆ tsupport f := by
      apply closure_mono
      intro x hx hfx
      apply hx
      have := hh x
      rw [hfx] at this
      simpa using this
    have hbd : ∀ x, |h x| ≤ max C 0 := by
      intro x
      refine (hh x).trans ((le_abs_self _).trans ?_)
      have h' : ‖f.toReal x‖ ≤ C := hC x
      rw [CompactlySupportedContinuousMap.toReal_apply, Real.norm_eq_abs] at h'
      exact h'.trans (le_max_left _ _)
    exact (le_abs_self _).trans (hM h _ hsupp (le_max_right _ _) hbd)
  -- the variation `V f = sup (Λ '' A f) ≥ Λ 0 = 0`
  let V : CompactlySupportedContinuousMap X NNReal → ℝ := fun f => sSup (Λ '' A f)
  have hle : ∀ f, ∀ h ∈ A f, Λ h ≤ V f := fun f h hh => le_csSup (hbdd f) ⟨h, hh, rfl⟩
  have hVle : ∀ f (c : ℝ), (∀ h ∈ A f, Λ h ≤ c) → V f ≤ c := by
    intro f c hc
    exact csSup_le ⟨0, 0, hA0 f, map_zero Λ⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
  have hV0 : ∀ f, 0 ≤ V f := fun f => by simpa using hle f 0 (hA0 f)
  -- additivity: `≤` by the clamp `h₁ = (h ⊓ f) ⊔ (-f)`, `h - h₁ ∈ A g`; `≥` by `h₁ + h₂ ∈ A (f + g)`
  have hadd : ∀ f g, V (f + g) = V f + V g := by
    intro f g
    apply le_antisymm
    · apply hVle
      intro h hh
      let h₁ : CompactlySupportedContinuousMap X ℝ := (h ⊓ f.toReal) ⊔ (-f.toReal)
      have hpt : ∀ x, |h₁ x| ≤ (f x : ℝ) ∧ |(h - h₁) x| ≤ (g x : ℝ) := by
        intro x
        have hx := hh x
        have hf0 : (0 : ℝ) ≤ f x := (f x).2
        have hg0 : (0 : ℝ) ≤ g x := (g x).2
        simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add] at hx
        simp only [h₁, CompactlySupportedContinuousMap.sub_apply,
          CompactlySupportedContinuousMap.sup_apply, CompactlySupportedContinuousMap.inf_apply,
          CompactlySupportedContinuousMap.neg_apply, CompactlySupportedContinuousMap.toReal_apply]
        rw [abs_le] at hx ⊢
        rw [abs_le]
        rcases le_total (h x) (f x) with h1 | h1
        · rw [min_eq_left h1]
          rcases le_total (h x) (-(f x : ℝ)) with h2 | h2
          · rw [max_eq_right h2]
            constructor <;> constructor <;> linarith
          · rw [max_eq_left h2]
            constructor <;> constructor <;> linarith
        · rw [min_eq_right h1, max_eq_left (by linarith)]
          constructor <;> constructor <;> linarith
      have h1mem : h₁ ∈ A f := fun x => (hpt x).1
      have h2mem : h - h₁ ∈ A g := fun x => (hpt x).2
      have e : Λ h = Λ h₁ + Λ (h - h₁) := by rw [map_sub]; ring
      rw [e]
      exact add_le_add (hle f h₁ h1mem) (hle g _ h2mem)
    · have key : V f ≤ V (f + g) - V g := by
        apply hVle
        intro h₁ hh₁
        have : V g ≤ V (f + g) - Λ h₁ := by
          apply hVle
          intro h₂ hh₂
          have hmem : h₁ + h₂ ∈ A (f + g) := by
            intro x
            simp only [CompactlySupportedContinuousMap.add_apply, NNReal.coe_add]
            exact (abs_add_le _ _).trans (add_le_add (hh₁ x) (hh₂ x))
          have := hle _ _ hmem
          rw [map_add] at this
          linarith
        linarith
      linarith
  -- homogeneity: `A 0 = {0}`; for `c > 0`, `h ↦ c⁻¹ • h` maps `A (c • f)` into `A f`
  have hzero : V 0 = 0 := by
    apply le_antisymm _ (hV0 0)
    apply hVle
    intro h hh
    have : h = 0 := by
      ext x
      simpa using hh x
    simp [this]
  have hsmul_le : ∀ (c : NNReal) f, V (c • f) ≤ c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply hVle
    intro h hh
    have hmem : (c : ℝ)⁻¹ • h ∈ A f := by
      intro x
      have := hh x
      simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, NNReal.coe_mul] at this
      rw [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hcpos)]
      rw [inv_mul_le_iff₀ hcpos]
      exact this
    have := hle f _ hmem
    rw [map_smul, smul_eq_mul] at this
    exact (inv_mul_le_iff₀ hcpos).mp this
  have hsmul : ∀ (c : NNReal) f, V (c • f) = c * V f := by
    intro c f
    rcases eq_or_ne c 0 with rfl | hc
    · simp [hzero]
    have hcpos : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
    apply le_antisymm (hsmul_le c f)
    have h := hsmul_le c⁻¹ (c • f)
    rw [inv_smul_smul₀ hc, NNReal.coe_inv] at h
    exact (le_inv_mul_iff₀ hcpos).mp h
  -- `V` is `ℝ≥0`-linear; `V̂ := toRealPositiveLinear V` is a positive functional on `C_c(X, ℝ)`
  let W : CompactlySupportedContinuousMap X NNReal →ₗ[NNReal] NNReal :=
    { toFun := fun f => ⟨V f, hV0 f⟩
      map_add' := fun f g => NNReal.eq (hadd f g)
      map_smul' := fun c f => NNReal.eq (hsmul c f) }
  let Vh := CompactlySupportedContinuousMap.toRealPositiveLinear W
  -- `V̂ + Λ` is positive: for `k ≥ 0`, `V̂ k = V k⁺` and `-k ∈ A k⁺`, so `-Λ k ≤ V̂ k`
  have hdom : ∀ k : CompactlySupportedContinuousMap X ℝ, 0 ≤ k → 0 ≤ Vh k + Λ k := by
    intro k hk
    have hkeq : k.nnrealPart.toReal = k := by
      ext x
      rw [CompactlySupportedContinuousMap.toReal_apply,
        CompactlySupportedContinuousMap.nnrealPart_apply]
      exact Real.coe_toNNReal _ (hk x)
    have hVk : Vh k = V k.nnrealPart := by
      have := CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal W k.nnrealPart
      rw [hkeq] at this
      exact this
    have hmem : -k ∈ A k.nnrealPart := by
      intro x
      rw [CompactlySupportedContinuousMap.neg_apply, abs_neg,
        CompactlySupportedContinuousMap.nnrealPart_apply, Real.coe_toNNReal _ (hk x)]
      exact (abs_of_nonneg (hk x)).le
    have := hle _ _ hmem
    rw [map_neg] at this
    rw [hVk]
    linarith
  refine ⟨PositiveLinearMap.mk₀ (Vh.toLinearMap + Λ) hdom, Vh, fun f => ?_⟩
  show Λ f = (Vh f + Λ f) - Vh f
  ring
/-- Common dominating measure (the common density step of the vector Riesz representation behind
the mass representation of currents, Simon Ch. 6, 2.7–2.8, used for Simon 7.2.4): if every `aᵢ`
and `bᵢ` (`i ∈ Fin m`) is finite on compact sets, then so is `μ₀ := ∑ᵢ (aᵢ + bᵢ)`, and
`aᵢ ≪ μ₀`, `bᵢ ≪ μ₀`.  Indeed `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`, so `μ₀(K)` is a
finite sum of finite terms for compact `K`, and `μ₀(s) = 0` forces `aᵢ(s) = bᵢ(s) = 0`. -/
theorem Submission.cmr_vr_cd_dominating_measure : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] (m : ℕ) (a b : Fin m → Measure X), (∀ i, IsFiniteMeasureOnCompacts (a i)) → (∀ i, IsFiniteMeasureOnCompacts (b i)) → ∃ μ₀ : Measure X, IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, a i ≪ μ₀) ∧ ∀ i, b i ≪ μ₀ := by
  intro X _ _ m a b ha hb
  -- Step 1: `μ₀ := ∑ᵢ (aᵢ + bᵢ)` has `μ₀(s) = ∑ᵢ (aᵢ(s) + bᵢ(s))` for every set `s`
  have hμ₀ : ∀ s : Set X, (∑ i, (a i + b i)) s = ∑ i, (a i s + b i s) := fun s => by
    simp only [Measure.finsetSum_apply, Measure.add_apply]
  refine ⟨∑ i, (a i + b i), ⟨fun K hK => ?_⟩, fun i s hs => ?_, fun i s hs => ?_⟩
  -- Step 2: for compact `K`, `μ₀(K)` is a finite sum of finite terms
  · rw [hμ₀, ENNReal.sum_lt_top]
    exact fun i _ =>
      ENNReal.add_lt_top.2 ⟨(ha i).lt_top_of_isCompact hK, (hb i).lt_top_of_isCompact hK⟩
  -- Step 3: if `μ₀(s) = 0`, every summand `aᵢ(s) + bᵢ(s)` vanishes
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).1
  · rw [hμ₀, Finset.sum_eq_zero_iff] at hs
    exact (add_eq_zero.1 (hs i (Finset.mem_univ i))).2
/-- **Radon–Nikodym density on `C_c`.**  If `μ₀`, `ξ` are finite on compact subsets of a locally
compact second countable space and `ξ ≪ μ₀`, then `ξ` has a measurable density `g`, `μ₀`-integrable
on compact sets, with `f·g` `μ₀`-integrable and `∫ f dξ = ∫ f g dμ₀` for every `f ∈ C_c(X, ℝ)`.
`X` is σ-compact, so `μ₀`, `ξ` are σ-finite and `ξ = μ₀.withDensity δ` for `δ = ξ.rnDeriv μ₀`
(the singular part vanishes since `ξ ≪ μ₀`), with `δ < ∞` `μ₀`-a.e.  Take `g = δ.toReal`: on a
compact `K`, `∫⁻_K δ dμ₀ < ∞` because `ξ(K) < ∞`.  A bounded `f` with compact support times `g` is
integrable on `tsupport f` and vanishes outside it.  The `T2Space` hypothesis is not used. -/
theorem Submission.cmr_vr_cd_density_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (μ₀ ξ : Measure X), IsFiniteMeasureOnCompacts μ₀ → IsFiniteMeasureOnCompacts ξ → ξ ≪ μ₀ → ∃ g : X → ℝ, Measurable g ∧ (∀ K : Set X, IsCompact K → IntegrableOn g K μ₀) ∧ ∀ f : CompactlySupportedContinuousMap X ℝ, Integrable (fun x => f x * g x) μ₀ ∧ ∫ x, f x ∂ξ = ∫ x, f x * g x ∂μ₀ := by
  intro X _ _ _ _ _ _ μ₀ ξ hμ₀ hξ hac
  -- `X` is σ-compact, so both measures are σ-finite and `(ξ, μ₀)` has a Lebesgue decomposition
  have : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite μ₀ := SigmaFinite.of_isFiniteMeasureOnCompacts μ₀
  have : SigmaFinite ξ := SigmaFinite.of_isFiniteMeasureOnCompacts ξ
  -- `ξ = μ₀.withDensity δ` with `δ = dξ/dμ₀` measurable and `μ₀`-a.e. finite
  set δ : X → ℝ≥0∞ := ξ.rnDeriv μ₀
  have hδm : Measurable δ := Measure.measurable_rnDeriv ξ μ₀
  have hξδ : ξ = μ₀.withDensity δ := by
    have h := Measure.haveLebesgueDecomposition_add ξ μ₀
    rwa [Measure.singularPart_eq_zero_of_ac hac, zero_add] at h
  have hδlt : ∀ᵐ x ∂μ₀, δ x < ∞ := Measure.rnDeriv_lt_top ξ μ₀
  -- `g = δ.toReal` is integrable on compact sets: `∫⁻_K δ dμ₀ < ∞` since `ξ(K) < ∞`
  have hgK : ∀ K : Set X, IsCompact K → IntegrableOn (fun x => (δ x).toReal) K μ₀ := by
    intro K hK
    have hlin : ∫⁻ x in K, δ x ∂μ₀ < ∞ :=
      Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top μ₀ hK.measure_lt_top.ne
    exact integrable_toReal_of_lintegral_ne_top hδm.aemeasurable hlin.ne
  refine ⟨fun x => (δ x).toReal, hδm.ennreal_toReal, hgK, fun f => ⟨?_, ?_⟩⟩
  -- `f` is bounded, so `f·g` is integrable on `tsupport f`, and it vanishes outside
  · obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
    have hon : IntegrableOn (fun x => f x * (δ x).toReal) (tsupport f) μ₀ :=
      Integrable.bdd_mul (c := C) (hgK _ f.hasCompactSupport.isCompact)
        (map_continuous f).measurable.aestronglyMeasurable (Eventually.of_forall hC)
    refine hon.integrable_of_forall_notMem_eq_zero fun x hx => ?_
    simp [image_eq_zero_of_notMem_tsupport hx]
  -- `∫ f dξ = ∫ δ.toReal • f dμ₀`
  · rw [hξδ, integral_withDensity_eq_integral_toReal_smul hδm hδlt]
    congr 1
    funext x
    exact (smul_eq_mul _ _).trans (mul_comm _ _)

/-- Common dominating measure and densities for finitely many pairs of positive functionals
(Riesz–Markov–Kakutani; Rudin, *Real and Complex Analysis*, Thm 2.14 and 6.10).  Let `X` be
locally compact, Hausdorff and second countable with its Borel σ-algebra, and let `Λ₁ᵢ, Λ₂ᵢ`
(`i ∈ Fin m`) be positive linear functionals on `C_c(X, ℝ)`.  Then there are a measure `μ₀`,
finite on compact sets, and measurable `ρᵢ`, `μ₀`-integrable on compact sets, with
`Λ₁ᵢ f - Λ₂ᵢ f = ∫ f ρᵢ dμ₀` for all `f ∈ C_c(X, ℝ)`.

Proof sketch:
* `bᵢ := rieszMeasure Λ₁ᵢ` and `aᵢ := rieszMeasure Λ₂ᵢ` are regular, hence finite on compact
  sets, and `∫ f dbᵢ = Λ₁ᵢ f`, `∫ f daᵢ = Λ₂ᵢ f`.
* `cmr_vr_cd_dominating_measure` gives a compact-finite `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`.
* `cmr_vr_cd_density_representation` gives locally integrable densities `gaᵢ`, `gbᵢ` with
  `∫ f daᵢ = ∫ f gaᵢ dμ₀`, `∫ f dbᵢ = ∫ f gbᵢ dμ₀`, both integrands integrable.
* With `ρᵢ := gbᵢ - gaᵢ`, linearity of the integral gives the representation. -/
theorem Submission.cmr_vr_common_density : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (m : ℕ) (Λ₁ Λ₂ : Fin m → (CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ)), ∃ (μ₀ : Measure X) (ρ : Fin m → X → ℝ), IsFiniteMeasureOnCompacts μ₀ ∧ (∀ i, Measurable (ρ i)) ∧ (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) ∧ ∀ (i : Fin m) (f : CompactlySupportedContinuousMap X ℝ), Λ₁ i f - Λ₂ i f = ∫ x, f x * ρ i x ∂μ₀ := by
  intro X _ _ _ _ _ _ m Λ₁ Λ₂
  -- Step 1 (RMK): the Riesz measures are regular, hence finite on compact sets
  have ha : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₂ i)) :=
    fun _ => inferInstance
  have hb : ∀ i, IsFiniteMeasureOnCompacts (RealRMK.rieszMeasure (Λ₁ i)) :=
    fun _ => inferInstance
  -- Step 2: a common compact-finite measure `μ₀` with `aᵢ ≪ μ₀` and `bᵢ ≪ μ₀`
  obtain ⟨μ₀, hμ₀, hac_a, hac_b⟩ := Submission.cmr_vr_cd_dominating_measure X m
    (fun i => RealRMK.rieszMeasure (Λ₂ i)) (fun i => RealRMK.rieszMeasure (Λ₁ i)) ha hb
  -- Step 3: locally integrable densities `gaᵢ`, `gbᵢ` of `aᵢ`, `bᵢ` with respect to `μ₀`
  choose ga hga_meas hga_int hga_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₂ i)) hμ₀ (ha i)
      (hac_a i)
  choose gb hgb_meas hgb_int hgb_rep using fun i =>
    Submission.cmr_vr_cd_density_representation X μ₀ (RealRMK.rieszMeasure (Λ₁ i)) hμ₀ (hb i)
      (hac_b i)
  -- Step 4: `ρᵢ := gbᵢ - gaᵢ` and linearity of the integral
  refine ⟨μ₀, fun i => gb i - ga i, hμ₀, fun i => (hgb_meas i).sub (hga_meas i),
    fun i K hK => (hgb_int i K hK).sub (hga_int i K hK), fun i f => ?_⟩
  obtain ⟨hgb_f, hgb_eq⟩ := hgb_rep i f
  obtain ⟨hga_f, hga_eq⟩ := hga_rep i f
  calc Λ₁ i f - Λ₂ i f
      = ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₁ i)) - ∫ x, f x ∂(RealRMK.rieszMeasure (Λ₂ i)) := by
        rw [RealRMK.integral_rieszMeasure, RealRMK.integral_rieszMeasure]
    _ = ∫ x, f x * gb i x ∂μ₀ - ∫ x, f x * ga i x ∂μ₀ := by rw [hgb_eq, hga_eq]
    _ = ∫ x, (f x * gb i x - f x * ga i x) ∂μ₀ := (integral_sub hgb_f hga_f).symm
    _ = ∫ x, f x * (gb i - ga i) x ∂μ₀ := by simp only [Pi.sub_apply, mul_sub]
/-- Assembly of coordinate densities (vector Riesz representation, coordinate step): if the
`i`-th coordinate functional `f ↦ L(f eᵢ)` has density `ρᵢ` w.r.t. `μ₀` for each `i`, then `L` has
the vector density `ν = Σᵢ ρᵢ eᵢ`, i.e. `L g = ∫ ⟨g, ν⟩ dμ₀`.  Write `g = Σᵢ gᵢ eᵢ` with
`gᵢ = ⟨g, eᵢ⟩ ∈ C_c(X)`; each `gᵢ ρᵢ` is integrable (bounded continuous times integrable on the
compact `tsupport gᵢ`, zero outside it), so the finite sum and the integral commute. -/
theorem Submission.cmr_vr_coordinate_assembly : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ) (μ₀ : Measure X) (ρ : Fin d → X → ℝ), (∀ i, Measurable (ρ i)) → (∀ i, ∀ K : Set X, IsCompact K → IntegrableOn (ρ i) K μ₀) → (∀ (i : Fin d) (f : CompactlySupportedContinuousMap X ℝ) (g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d))), (∀ x, g x = f x • EuclideanSpace.single i (1 : ℝ)) → L g = ∫ x, f x * ρ i x ∂μ₀) → ∃ ν : X → EuclideanSpace ℝ (Fin d), Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
  intro X _ _ _ d L μ₀ ρ hρm hρi hL
  -- `ν = Σᵢ ρᵢ eᵢ`
  refine ⟨fun x => ∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ),
    Finset.measurable_sum _ fun i _ => (hρm i).smul_const _,
    fun K hK => integrable_finsetSum _ fun i _ => (hρi i K hK).smul_const _, fun g => ?_⟩
  -- the coordinates `gᵢ = g(·)ᵢ ∈ C_c(X, ℝ)` and `Gᵢ = gᵢ eᵢ ∈ C_c(X, H)`
  obtain ⟨gc, hgc⟩ : ∃ gc : Fin d → CompactlySupportedContinuousMap X ℝ, ∀ i x, gc i x = g x i :=
    ⟨fun i => g.compLeft (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (by simp) g x⟩
  obtain ⟨G, hG⟩ : ∃ G : Fin d → CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)),
      ∀ i x, G i x = gc i x • EuclideanSpace.single i (1 : ℝ) :=
    ⟨fun i => (gc i).compLeft ⟨fun t => t • EuclideanSpace.single i (1 : ℝ), by fun_prop⟩,
      fun i x => CompactlySupportedContinuousMap.compLeft_apply (zero_smul ℝ _) (gc i) x⟩
  -- `g = Σᵢ Gᵢ`
  have hsum : g = ∑ i, G i := by
    ext x j
    simp [hG, hgc, Pi.single_apply]
  -- each `gᵢ ρᵢ` is integrable: bounded continuous times integrable on the compact `tsupport gᵢ`
  have hint : ∀ i, Integrable (fun x => gc i x * ρ i x) μ₀ := by
    intro i
    obtain ⟨C, hC⟩ := (gc i).continuous.bounded_above_of_compact_support (gc i).hasCompactSupport
    have hK : IntegrableOn (fun x => gc i x * ρ i x) (tsupport (gc i)) μ₀ :=
      Integrable.bdd_mul (hρi i _ (gc i).hasCompactSupport.isCompact)
        (gc i).continuous.aestronglyMeasurable (Eventually.of_forall hC)
    exact hK.integrable_of_forall_notMem_eq_zero fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  calc L g = ∑ i, L (G i) := (congrArg L hsum).trans (map_sum L G Finset.univ)
    _ = ∑ i, ∫ x, gc i x * ρ i x ∂μ₀ := Finset.sum_congr rfl fun i _ => hL i (gc i) (G i) (hG i)
    _ = ∫ x, ∑ i, gc i x * ρ i x ∂μ₀ := (integral_finsetSum _ fun i _ => hint i).symm
    _ = ∫ x, inner ℝ (g x) (∑ i, ρ i x • EuclideanSpace.single i (1 : ℝ)) ∂μ₀ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      dsimp only
      rw [inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_right, EuclideanSpace.inner_single_right, hgc, conj_trivial, one_mul, mul_comm]

/-- **Riesz representation of locally bounded functionals on `C_c(X, ℝ^d)`** (Simon Ch. 1, 4.14,
in the form used for currents in Ch. 6, 2.7).  If `X` is locally compact Hausdorff and second
countable and `L : C_c(X, ℝ^d) → ℝ` is linear with `|L g| ≤ M_K` whenever `spt g ⊆ K` and
`|g| ≤ 1`, then `L g = ∫ ⟨g, ν⟩ dμ₀` for a Borel measure `μ₀` finite on compact sets and a
measurable `ν : X → ℝ^d` integrable on compact sets.  The coordinate functionals
`Λᵢ f = L(f eᵢ)` are locally bounded, each splits as a difference `Pᵢ − Nᵢ` of positive
functionals (total variation), the Riesz–Markov–Kakutani measures of all `Pᵢ, Nᵢ` have densities
`ρᵢ` against one common `μ₀`, and `ν = Σᵢ ρᵢ eᵢ`. -/
theorem Submission.cmr_vector_riesz_representation : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (d : ℕ) (L : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)) →ₗ[ℝ] ℝ), (∀ K : Set X, IsCompact K → ∃ M : ℝ, ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), tsupport g ⊆ K → (∀ x, ‖g x‖ ≤ 1) → |L g| ≤ M) → ∃ (μ₀ : Measure X) (ν : X → EuclideanSpace ℝ (Fin d)), IsFiniteMeasureOnCompacts μ₀ ∧ Measurable ν ∧ (∀ K : Set X, IsCompact K → IntegrableOn ν K μ₀) ∧ ∀ g : CompactlySupportedContinuousMap X (EuclideanSpace ℝ (Fin d)), L g = ∫ x, inner ℝ (g x) (ν x) ∂μ₀ := by
  intro X _ _ _ _ _ _ d L hL
  -- step 1: the coordinate functionals `Λᵢ f = L(f eᵢ)`, locally bounded
  choose Λ hΛL hΛbd using Submission.cmr_vr_coordinate_functional X d L hL
  -- steps 2–3: Jordan decomposition `Λᵢ = Pᵢ − Nᵢ` into positive functionals
  choose Pos Neg hΛ using fun i => Submission.cmr_vr_jordan_decomposition X (Λ i) (hΛbd i)
  -- steps 4–6 and 8: one measure `μ₀` with `Pᵢ f − Nᵢ f = ∫ f ρᵢ dμ₀`
  obtain ⟨μ₀, ρ, hμ₀, hρm, hρint, hρ⟩ := Submission.cmr_vr_common_density X d Pos Neg
  -- steps 7 and 9: `ν = Σᵢ ρᵢ eᵢ` and `L g = Σᵢ ∫ gᵢ ρᵢ dμ₀ = ∫ ⟨g, ν⟩ dμ₀`
  obtain ⟨ν, hνm, hνint, hν⟩ := Submission.cmr_vr_coordinate_assembly X d L μ₀ ρ hρm hρint
    fun i f g hg => by rw [hΛL i f g hg, hΛ i f, hρ i f]
  exact ⟨μ₀, ν, hμ₀, hνm, hνint, hν⟩

/-- **Simon Ch. 6, 2.7–2.8** (Riesz representation of a current of locally finite mass): if
`M_W(T) < ∞` for every open `W ⊂⊂ U`, then `T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|⟨α, ξ⟩| ≤ |α|_E`,
`μ(ℝᴾ \ U) = 0`, `μ` finite on compact subsets of `U` and `M_W(T) = μ(W)` for open `W`.
Euclidean coordinates `c` on covectors (`|α|_E = ‖c α‖`) make `T` a locally bounded linear
functional `L` on `C_c(U, ℝᵈ)` with `L(c ∘ ω) = T ω`.  The vector Riesz theorem on the locally
compact space `U` gives `L g = ∫ ⟨g, ν⟩ dμ₀`.  Normalizing `ν` polarly and pushing `|ν| μ₀`
forward to `ℝᴾ` gives `μ`, the field `ξ = ⟨ν/|ν|, c(·)⟩` and a norming field `β` with
`ξ(β) = 1` `μ`-a.e.  Then `M_W(T) ≤ μ(W)` because `|ξ(ω)| ≤ |ω|_E ≤ 1`, while `μ(W') ≤ M_W(T)`
for open `W' ⊂⊂ U` inside `W` (test `T` on forms approximating `β`), and these `W'` exhaust
`W ∩ U`. -/
theorem Submission.cmr_exists_massRepresentation_core : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by
  intro P n U T hU hfin
  -- Step 1: Euclidean coordinates `c` on covectors, `|α|_E = ‖c α‖`
  obtain ⟨d, c, hc⟩ := Submission.cmr_covector_euclidean_equiv P n
  -- Step 2: `T` extends to a locally bounded linear functional `L` on `C_c(U, ℝᵈ)`
  obtain ⟨L, hLT, hLb⟩ := Submission.cmr_testForm_extension_functional P n U T d c hU hfin hc
  -- Step 3: vector Riesz representation `L g = ∫ ⟨g, ν⟩ dμ₀` on the locally compact space `U`
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  obtain ⟨μ₀, ν, -, hνm, hνi, hLν⟩ := Submission.cmr_vector_riesz_representation U d L hLb
  -- Steps 4–9: `μ = val_*(|ν| μ₀)`, `ξ = ⟨ν/|ν|, c(·)⟩` and the norming field `β`
  obtain ⟨μ, ξ, β, hμU, hμK, hξm, hξ1, hβm, hβb, hβ1, hξβ, hμν⟩ :=
    Submission.cmrc_polar_pushforward P n d U c μ₀ ν hU hc hνm hνi
  -- Step 8: `T ω = L(c ∘ ω) = ∫ ⟨c ∘ ω, ν⟩ dμ₀ = ∫ ξ(ω) dμ`
  have hT : ∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ := by
    intro ω
    obtain ⟨g, hg⟩ := Submission.cmrc_testForm_restrict_cc P n d U c c.continuous c.map_zero ω
    rw [← hLT ω g hg, hLν g, ← hμν (ω : DifferentialForm (Euclid P) n)]
    simp only [hg]
  -- Steps 10–12: `M_W(T) ≤ μ(W)`, and `μ(W) ≤ M_W(T)` by exhausting `W ∩ U` with `W' ⊂⊂ U`
  refine ⟨μ, ξ, hμU, hμK, fun W hW => le_antisymm
    (Submission.cmrc_massOn_le_of_repr P n U T μ ξ hξ1 hT W) ?_, hξm, hξ1, hT⟩
  exact Submission.cmrc_measure_le_of_compactlyContained P μ U W (T.massOn W) hU hW hμU
    fun W' hW' hW'U hW'W => Submission.cmrc_measure_le_massOn_of_norming P n U T μ ξ β hμK hξm
      hξ1 hT hβm hβb hβ1 hξβ W W' hW' hW'U hW'W
/-- **Directional difference estimate from the divergence bound** (steps 1–2 of the parent proof).
For `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible and `div g(y) = Da(y + v)(w)` (trace
of a rank-one map), so `|∫ h·Da(q + v)(w) dν| ≤ Λ`.  The fundamental theorem of calculus along
`s ↦ q x + s • z` and Fubini on `(0, 1] × X` (majorant `M‖z‖|h|`, `‖Da‖ ≤ M`) give
`∫ h·(a(q + z) − a(q)) dν = ∫₀¹ ∫ h·Da(q + s • z)(z) dν ds`, and `Da(p)(z) = ‖z‖·Da(p)(w)` with
`w = ‖z‖⁻¹ • z` bounds the inner integral by `Λ‖z‖`. -/
theorem Submission.cmr_tdn_directional_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, |a y| ≤ 1) → ∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖ := by
  intro n X _ ν q h Λ hν hq hh hdiv a ha hsupp hbd z
  -- Step 1: `a` is differentiable, `Da` is continuous with compact support, so `‖Da‖ ≤ M`
  have h0 : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ a := ha.differentiable h0
  have hcont : Continuous (fderiv ℝ a) := ha.continuous_fderiv h0
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support (hsupp.fderiv ℝ)
  -- Step 3: for `‖w‖ ≤ 1` the field `g(y) = a(y + v) • w` is admissible, with
  -- `div g(y) = Da(y + v)(w)`; this gives `(∗)`
  have key : ∀ v w : Euclid n, ‖w‖ ≤ 1 → |∫ x, h x * fderiv ℝ a (q x + v) w ∂ν| ≤ Λ := by
    intro v w hw
    set g : Euclid n → Euclid n := fun y => a (y + v) • w with hg_def
    have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g :=
      (ha.comp (contDiff_id.add contDiff_const)).smul contDiff_const
    have hg_supp : HasCompactSupport g :=
      (hsupp.comp_homeomorph (Homeomorph.addRight v)).smul_right (f' := fun _ => w)
    have hg_bd : ∀ y, ‖g y‖ ≤ 1 := by
      intro y
      simp only [hg_def, norm_smul, Real.norm_eq_abs]
      calc |a (y + v)| * ‖w‖ ≤ 1 * 1 := mul_le_mul (hbd _) hw (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have htrace : ∀ y, LinearMap.trace ℝ (Euclid n) (fderiv ℝ g y).toLinearMap
        = fderiv ℝ a (y + v) w := by
      intro y
      have h1 : HasFDerivAt (fun y => a (y + v)) (fderiv ℝ a (y + v)) y :=
        (hasFDerivAt_comp_add_right v).2 (hdiff (y + v)).hasFDerivAt
      rw [(h1.smul_const w).fderiv, ContinuousLinearMap.coe_smulRight,
        LinearMap.trace_smulRight]
      rfl
    simpa only [htrace] using hdiv g hg_smooth hg_supp hg_bd
  -- Step 4: fundamental theorem of calculus along `s ↦ q x + s • z`
  have hftc : ∀ x, ∫ s in (0 : ℝ)..1, h x * fderiv ℝ a (q x + s • z) z
      = h x * (a (q x + z) - a (q x)) := by
    intro x
    have hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s : ℝ => a (q x + s • z)) (fderiv ℝ a (q x + s • z) z) s := by
      intro s _
      have hline : HasDerivAt (fun s : ℝ => q x + s • z) z s := by
        simpa using ((hasDerivAt_id s).smul_const z).const_add (q x)
      exact (hdiff (q x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
    have hcontS : Continuous (fun s : ℝ => fderiv ℝ a (q x + s • z) z) :=
      (hcont.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
        continuous_const
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcontS.intervalIntegrable 0 1)]
    simp
  -- Step 5: Fubini on `Leb|(0, 1] ⊗ ν`, with integrable majorant `M‖z‖|h|`
  have hGint : Integrable (uncurry fun (s : ℝ) (x : X) => h x * fderiv ℝ a (q x + s • z) z)
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := by
    have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) 1)) := by
      rw [uIoc_of_le zero_le_one]; infer_instance
    have hmaj : Integrable (fun p : ℝ × X => (M * ‖z‖) * |h p.2|)
        ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) :=
      (hh.abs.comp_snd _).const_mul _
    refine hmaj.mono' ?_ ?_
    · have h1 : AEStronglyMeasurable (fun p : ℝ × X => h p.2)
          ((volume.restrict (uIoc (0 : ℝ) 1)).prod ν) := hh.aestronglyMeasurable.comp_snd
      have h2 : Continuous (fun p : ℝ × Euclid n => fderiv ℝ a (p.2 + p.1 • z) z) :=
        (hcont.comp (continuous_snd.add (continuous_fst.smul continuous_const))).clm_apply
          continuous_const
      have h3 : Measurable (fun p : ℝ × X => (p.1, q p.2)) :=
        measurable_fst.prodMk (hq.comp measurable_snd)
      exact h1.mul (h2.measurable.comp h3).aestronglyMeasurable
    · filter_upwards with p
      simp only [uncurry, Real.norm_eq_abs, abs_mul]
      have hp : |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ M * ‖z‖ :=
        calc |fderiv ℝ a (q p.2 + p.1 • z) z| = ‖fderiv ℝ a (q p.2 + p.1 • z) z‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ‖fderiv ℝ a (q p.2 + p.1 • z)‖ * ‖z‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M * ‖z‖ := by gcongr; exact hM _
      calc |h p.2| * |fderiv ℝ a (q p.2 + p.1 • z) z| ≤ |h p.2| * (M * ‖z‖) := by gcongr
        _ = M * ‖z‖ * |h p.2| := by ring
  have heq : ∫ x, h x * (a (q x + z) - a (q x)) ∂ν
      = ∫ s in (0 : ℝ)..1, ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν := by
    rw [intervalIntegral_integral_swap hGint]
    exact integral_congr_ae (Eventually.of_forall fun x => (hftc x).symm)
  -- Step 6: with `w = ‖z‖⁻¹ • z` (so `‖w‖ ≤ 1`, `z = ‖z‖ • w`, also for `z = 0`),
  -- `(∗)` bounds the inner integral by `Λ‖z‖` for every `s`
  set w : Euclid n := ‖z‖⁻¹ • z with hw_def
  have hw : ‖w‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hw_def, hz]
    · rw [hw_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
  have hzw : z = ‖z‖ • w := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [hw_def, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hz), one_smul]
  have hlin : ∀ p : Euclid n, fderiv ℝ a p z = ‖z‖ * fderiv ℝ a p w := by
    intro p
    conv_lhs => rw [hzw]
    rw [map_smul, smul_eq_mul]
  have hbound : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν‖ ≤ Λ * ‖z‖ := by
    intro s _
    have hrw : ∫ x, h x * fderiv ℝ a (q x + s • z) z ∂ν
        = ‖z‖ * ∫ x, h x * fderiv ℝ a (q x + s • z) w ∂ν := by
      rw [← integral_const_mul]
      congr 1
      ext x
      rw [hlin]
      ring
    rw [hrw, Real.norm_eq_abs, abs_mul, abs_norm, mul_comm Λ]
    exact mul_le_mul_of_nonneg_left (key (s • z) w hw) (norm_nonneg _)
  rw [heq]
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound
/-- **Ball-averaging estimate** (step 3 of the parent proof).  With `B = B_r(0)` and
`V = λ(B) ∈ (0, ∞)`, Fubini on `ν ⊗ λ⌞B` gives
`V ∫ h(x) a(q x) dν = ∫∫ h(x) a(q x + z) − ∫∫ h(x) (a(q x + z) − a(q x))`.  The second double
integral is at most `V Λ r` by the directional bound (`‖z‖ < r` on `B`), and the first at most
`(∫ |h| dν) ∫ a` since `0 ≤ ∫_B a(q x + z) dz ≤ ∫ a` by translation invariance.  Divide by `V`. -/
theorem Submission.cmr_tdn_ball_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ) (a : Euclid n → ℝ) (r : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → 0 ≤ Λ → Continuous a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → (∀ z : Euclid n, |∫ x, h x * (a (q x + z) - a (q x)) ∂ν| ≤ Λ * ‖z‖) → 0 < r → |∫ x, h x * a (q x) ∂ν| ≤ r * Λ + (volume (ball (0 : Euclid n) r)).toReal⁻¹ * (∫ x, |h x| ∂ν) * ∫ y, a y := by
  intro n X mX ν q h Λ a r hν hq hh hΛ ha ha_supp ha0 ha1 hdir hr
  -- the ball `B = B_r(0)`: measurable, inside `‖z‖ ≤ r`, of measure `λ(B) ∈ (0, ∞)`
  have hBm : MeasurableSet (ball (0 : Euclid n) r) := measurableSet_ball
  have hBr : ∀ z ∈ ball (0 : Euclid n) r, ‖z‖ ≤ r := fun z hz => (mem_ball_zero_iff.1 hz).le
  have hBpos : 0 < volume (ball (0 : Euclid n) r) := measure_ball_pos volume 0 hr
  have hBfin : volume (ball (0 : Euclid n) r) < ∞ := measure_ball_lt_top
  generalize ball (0 : Euclid n) r = B at hBm hBr hBpos hBfin ⊢
  have hV : 0 < (volume B).toReal := ENNReal.toReal_pos hBpos.ne' hBfin.ne
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin.ne
  have hμB : (volume.restrict B).real univ = (volume B).toReal := by
    rw [measureReal_def, Measure.restrict_apply_univ]
  generalize (volume B).toReal = V at hV hμB ⊢
  -- `a` is integrable, and so are its translates
  have ha_int : Integrable a volume := ha.integrable_of_hasCompactSupport ha_supp
  -- the integrands on `ν ⊗ λ⌞B`, dominated by `|h x|`
  have hm₁ : Measurable fun p : X × Euclid n => a (q p.1 + p.2) :=
    ha.measurable.comp ((hq.comp measurable_fst).add measurable_snd)
  have hm₀ : Measurable fun p : X × Euclid n => a (q p.1) :=
    ha.measurable.comp (hq.comp measurable_fst)
  have hh₁ : AEStronglyMeasurable (fun p : X × Euclid n => h p.1) (ν.prod (volume.restrict B)) :=
    hh.aestronglyMeasurable.comp_fst
  have hdom : Integrable (fun p : X × Euclid n => |h p.1|) (ν.prod (volume.restrict B)) :=
    hh.abs.comp_fst _
  have hG₂ : Integrable (fun p : X × Euclid n => h p.1 * a (q p.1 + p.2))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul hm₁.aestronglyMeasurable) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (ha1 _)
  have hG₁ : Integrable (fun p : X × Euclid n => h p.1 * (a (q p.1 + p.2) - a (q p.1)))
      (ν.prod (volume.restrict B)) := by
    refine hdom.mono' (hh₁.mul (hm₁.sub hm₀).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) (abs_sub_le_iff.2 ⟨?_, ?_⟩)
    · linarith [ha0 (q p.1), ha1 (q p.1 + p.2)]
    · linarith [ha0 (q p.1 + p.2), ha1 (q p.1)]
  -- `V F = ∫∫ h(x) a(q x + z) - ∫∫ h(x) (a(q x + z) - a(q x))` over `ν ⊗ λ⌞B`
  have hsplit : V * ∫ x, h x * a (q x) ∂ν =
      (∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))) -
        ∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B)) := by
    rw [← integral_sub hG₂ hG₁]
    have hfun : (fun p : X × Euclid n =>
        h p.1 * a (q p.1 + p.2) - h p.1 * (a (q p.1 + p.2) - a (q p.1))) =
        fun p => h p.1 * a (q p.1) := by
      funext p
      ring
    rw [hfun, integral_fun_fst (fun x => h x * a (q x)), hμB, smul_eq_mul]
  -- Fubini and the directional bound: `|∫∫ h(x) (a(q x + z) - a(q x))| ≤ V Λ r`
  have hJ : |∫ p, h p.1 * (a (q p.1 + p.2) - a (q p.1)) ∂(ν.prod (volume.restrict B))| ≤
      V * (Λ * r) := by
    rw [integral_prod_symm _ hG₁]
    have hb : ∀ᵐ z ∂(volume.restrict B), ‖∫ x, h x * (a (q x + z) - a (q x)) ∂ν‖ ≤ Λ * r := by
      filter_upwards [ae_restrict_mem hBm] with z hz
      rw [Real.norm_eq_abs]
      exact (hdir z).trans (mul_le_mul_of_nonneg_left (hBr z hz) hΛ)
    have := norm_integral_le_of_norm_le (integrable_const (Λ * r)) hb
    rw [integral_const, hμB, smul_eq_mul, Real.norm_eq_abs] at this
    exact this
  -- translation invariance: `|∫∫ h(x) a(q x + z)| ≤ (∫ |h|) ∫ a`
  have hM : |∫ p, h p.1 * a (q p.1 + p.2) ∂(ν.prod (volume.restrict B))| ≤
      (∫ x, |h x| ∂ν) * ∫ y, a y := by
    rw [integral_prod _ hG₂]
    have hb : ∀ x, ‖∫ z, h x * a (q x + z) ∂(volume.restrict B)‖ ≤ |h x| * ∫ y, a y := by
      intro x
      rw [integral_const_mul, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have h0 : 0 ≤ ∫ z, a (q x + z) ∂(volume.restrict B) := integral_nonneg fun z => ha0 _
      rw [abs_of_nonneg h0]
      exact (setIntegral_le_integral (ha_int.comp_add_left (q x))
        (Eventually.of_forall fun z => ha0 _)).trans_eq (integral_add_left_eq_self a (q x))
    have := norm_integral_le_of_norm_le (hh.abs.mul_const (∫ y, a y)) (Eventually.of_forall hb)
    rw [integral_mul_const, Real.norm_eq_abs] at this
    exact this
  -- conclusion: `V |F| ≤ (∫ |h|) ∫ a + V Λ r`, then divide by `V > 0`
  have key : V * |∫ x, h x * a (q x) ∂ν| ≤ (∫ x, |h x| ∂ν) * (∫ y, a y) + V * (Λ * r) := by
    rw [← abs_of_pos hV, ← abs_mul, abs_of_pos hV, hsplit]
    exact (abs_sub _ _).trans (add_le_add hM hJ)
  generalize ∫ x, h x * a (q x) ∂ν = F at key ⊢
  generalize ∫ x, |h x| ∂ν = H at key ⊢
  generalize ∫ y, a y = A at key ⊢
  have hV0 : V ≠ 0 := hV.ne'
  calc |F| ≤ (H * A + V * (Λ * r)) / V := by
        rw [le_div_iff₀ hV]
        linarith
    _ = r * Λ + V⁻¹ * H * A := by
        field_simp
        ring
/-- **Smooth cut-offs of a compact Lebesgue-null set** (steps 4 and 5(ii) of the parent proof).
With `δₖ = 1/(k+1)`, take `aₖ` smooth with values in `[0, 1]`, support `thickening δₖ K`, and
`aₖ = 1` exactly on `K` (`exists_contDiff_support_eq_eq_one_iff`).  Then `aₖ` vanishes off the
compact `cthickening δₖ K`; a point `y ∉ K = ⋂_{δ>0} cthickening δ K` misses some
`cthickening δ K`, so `aₖ(y) = 0` once `δₖ < δ`; and `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K) → λ(K) = 0`. -/
theorem Submission.cmr_tdn_null_set_cutoffs : ∀ (n : ℕ) (K : Set (Euclid n)), IsCompact K → volume K = 0 → ∃ a : ℕ → Euclid n → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (a k)) ∧ (∀ k, HasCompactSupport (a k)) ∧ (∀ k y, 0 ≤ a k y) ∧ (∀ k y, a k y ≤ 1) ∧ (∀ k, ∀ y ∈ K, a k y = 1) ∧ (∀ y, y ∉ K → ∀ᶠ k in atTop, a k y = 0) ∧ Tendsto (fun k => ∫ y, a k y) atTop (𝓝 0) := by
  intro n K hK hK0
  -- `aₖ`: smooth, `[0, 1]`-valued, with support `thickening δₖ K` and `aₖ = 1` exactly on `K`
  have hδ : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => by positivity
  have hex : ∀ k : ℕ, ∃ f : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ range f ⊆ Icc 0 1 ∧
      support f = thickening (1 / ((k : ℝ) + 1)) K ∧ ∀ x, x ∈ K ↔ f x = 1 := fun k =>
    exists_contDiff_support_eq_eq_one_iff isOpen_thickening hK.isClosed
      (self_subset_thickening (hδ k) K)
  choose a ha_smooth ha_range ha_supp ha_one using hex
  have hnonneg : ∀ k y, 0 ≤ a k y := fun k y => (ha_range k (mem_range_self y)).1
  have hle : ∀ k y, a k y ≤ 1 := fun k y => (ha_range k (mem_range_self y)).2
  -- `aₖ` vanishes off the compact `cthickening δₖ K`
  have hzero : ∀ (k : ℕ) y, y ∉ cthickening (1 / ((k : ℝ) + 1)) K → a k y = 0 := by
    intro k y hy
    by_contra h
    have hy' : y ∈ support (a k) := h
    rw [ha_supp k] at hy'
    exact hy (thickening_subset_cthickening _ _ hy')
  refine ⟨a, ha_smooth, fun k => HasCompactSupport.intro hK.cthickening (hzero k), hnonneg, hle,
    fun k y hy => (ha_one k y).1 hy, ?_, ?_⟩
  · -- `y ∉ K = ⋂_{δ>0} cthickening δ K`, so `y ∉ cthickening δ K ⊇ cthickening δₖ K` for some
    -- `δ > 0` and all `k` with `δₖ < δ`
    intro y hy
    rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening] at hy
    simp only [mem_iInter, not_forall] at hy
    obtain ⟨δ, hδpos, hyδ⟩ := hy
    obtain ⟨k₀, hk₀⟩ := exists_nat_one_div_lt hδpos
    filter_upwards [eventually_ge_atTop k₀] with k hk
    refine hzero k y fun hmem => hyδ (cthickening_mono ?_ K hmem)
    have hkk₀ : 1 / ((k : ℝ) + 1) ≤ 1 / ((k₀ : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    linarith
  · -- `0 ≤ ∫ aₖ ≤ λ(cthickening δₖ K)`, and `λ(cthickening δₖ K) → λ(K) = 0`
    have hmeas : Tendsto (fun k : ℕ => (volume (cthickening (1 / ((k : ℝ) + 1)) K)).toReal)
        atTop (𝓝 0) := by
      have h := (tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure (Euclid n)))
        hK).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [hK0] at h
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmeas
      (fun k => integral_nonneg (hnonneg k)) fun k => ?_
    set C := cthickening (1 / ((k : ℝ) + 1)) K
    have hCm : MeasurableSet C := isClosed_cthickening.measurableSet
    have hint : Integrable (C.indicator fun _ => (1 : ℝ)) volume :=
      (integrable_indicator_iff hCm).2 (integrableOn_const hK.cthickening.measure_lt_top.ne)
    have hind : ∀ y, a k y ≤ C.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hy : y ∈ C
      · rw [indicator_of_mem hy]
        exact hle k y
      · rw [indicator_of_notMem hy, hzero k y hy]
    calc ∫ y, a k y ≤ ∫ y, C.indicator (fun _ => (1 : ℝ)) y :=
          integral_mono_of_nonneg (Eventually.of_forall (hnonneg k)) hint
            (Eventually.of_forall hind)
      _ = (volume C).toReal := by
          rw [integral_indicator_const _ hCm]
          simp [measureReal_def]

/-- **Vanishing on compact null sets from an `ε + C ∫ a` bound** (steps 5(i) and 6 of the
top-dimensional null-set argument): let `q : X → ℝⁿ` be measurable and `h ∈ L¹(ν)` (`ν` need not
be finite), and suppose that for every `ε > 0` there is `C` with `|∫ h · a(q) dν| ≤ ε + C ∫ a`
for all smooth compactly supported `0 ≤ a ≤ 1`.  Then `∫_{q⁻¹K} h dν = 0` for every compact
Lebesgue-null `K ⊆ ℝⁿ`.  Along the cut-offs `a_k` of `K` given by
`Submission.cmr_tdn_null_set_cutoffs`, dominated convergence (majorant `|h|`) gives
`∫ h · a_k(q) dν → ∫_{q⁻¹K} h dν`, while `ε + C ∫ a_k → ε`; so `|∫_{q⁻¹K} h dν| ≤ ε` for every
`ε > 0`. -/
theorem Submission.cmr_tdn_null_of_average_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ), Measurable q → Integrable h ν → (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a : Euclid n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a → (∀ y, 0 ≤ a y) → (∀ y, a y ≤ 1) → |∫ x, h x * a (q x) ∂ν| ≤ ε + C * ∫ y, a y) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h hq hh hbd K hK hK0
  -- smooth cut-offs `a k` of `K`: `a k = 1` on `K`, `a k → 0` pointwise off `K`, `∫ a k → 0`
  obtain ⟨a, ha, hac, ha0, ha1, haK, haoff, haint⟩ :=
    Submission.cmr_tdn_null_set_cutoffs n K hK hK0
  -- dominated convergence with majorant `|h|`: `∫ h (a k ∘ q) dν → ∫ 1_{q⁻¹K} h dν`
  have hE : MeasurableSet (q ⁻¹' K) := hq hK.isClosed.measurableSet
  have hlim : Tendsto (fun k => ∫ x, h x * a k (q x) ∂ν) atTop
      (𝓝 (∫ x in q ⁻¹' K, h x ∂ν)) := by
    rw [← integral_indicator hE]
    refine tendsto_integral_of_dominated_convergence (fun x => |h x|)
      (fun k => hh.aestronglyMeasurable.mul
        ((ha k).continuous.measurable.comp hq).aestronglyMeasurable)
      hh.abs (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha0 k (q x))]
      exact mul_le_of_le_one_right (abs_nonneg _) (ha1 k (q x))
    · by_cases hx : q x ∈ K
      · have h1 : ∀ k, a k (q x) = 1 := fun k => haK k (q x) hx
        simp only [indicator_of_mem (show x ∈ q ⁻¹' K from hx), h1, mul_one]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem (show x ∉ q ⁻¹' K from hx)]
        refine tendsto_nhds_of_eventually_eq ?_
        filter_upwards [haoff (q x) hx] with k hk
        rw [hk, mul_zero]
  -- for `ε > 0`: `|∫ h (a k ∘ q) dν| ≤ ε + C ∫ a k → ε`, so `|∫_{q⁻¹K} h dν| ≤ ε`
  refine abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  obtain ⟨C, hC⟩ := hbd ε hε
  have hR : Tendsto (fun k => ε + C * ∫ y, a k y) atTop (𝓝 (ε + C * 0)) :=
    tendsto_const_nhds.add (haint.const_mul C)
  rw [mul_zero, add_zero] at hR
  rw [zero_add]
  exact le_of_tendsto_of_tendsto' hlim.abs hR fun k => hC (a k) (ha k) (hac k) (ha0 k) (ha1 k)

/-- **Lemma TD for `m = q_#(h ν)`** (top-dimensional step of the absolute continuity of normal
currents, Simon Ch. 6, 2.36): if `|∫ h · div g(q) dν| ≤ Λ` for all smooth compactly supported
fields `g` with `‖g‖ ≤ 1`, then `∫_{q⁻¹K} h dν = 0` for every compact Lebesgue-null `K ⊆ ℝⁿ`.
Testing with `g = 0` gives `Λ ≥ 0`, and `Submission.cmr_tdn_directional_bound` gives
`|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖` for smooth compactly supported `|a| ≤ 1`.  For `ε > 0`,
averaging over `B_r` with `rΛ ≤ ε` (`Submission.cmr_tdn_ball_average_bound`) gives
`|∫ h a(q) dν| ≤ ε + |B_r|⁻¹ ‖h‖₁ ∫ a` for smooth compactly supported `0 ≤ a ≤ 1`, and
`Submission.cmr_tdn_null_of_average_bound` turns these bounds into the claim. -/
theorem Submission.cmr_null_of_div_bound : ∀ (n : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X) (q : X → Euclid n) (h : X → ℝ) (Λ : ℝ), IsFiniteMeasure ν → Measurable q → Integrable h ν → (∀ g : Euclid n → Euclid n, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → (∀ y, ‖g y‖ ≤ 1) → |∫ x, h x * LinearMap.trace ℝ (Euclid n) (fderiv ℝ g (q x)).toLinearMap ∂ν| ≤ Λ) → ∀ K : Set (Euclid n), IsCompact K → volume K = 0 → ∫ x in q ⁻¹' K, h x ∂ν = 0 := by
  intro n X _ ν q h Λ hν hq hh hdiv
  -- `Λ ≥ 0`: the field `g = 0` has divergence `0`
  have hΛ : 0 ≤ Λ := by
    simpa using hdiv (fun _ => 0) contDiff_const HasCompactSupport.zero fun _ => by simp
  -- the translation estimate `|∫ h (a(q + z) − a(q)) dν| ≤ Λ‖z‖`
  have hdir := Submission.cmr_tdn_directional_bound n X ν q h Λ hν hq hh hdiv
  refine Submission.cmr_tdn_null_of_average_bound n X ν q h hq hh fun ε hε => ?_
  -- average over `B_r` with `r = ε / (Λ + 1)`, so that `rΛ ≤ ε`
  obtain ⟨r, hr, hrΛ⟩ : ∃ r : ℝ, 0 < r ∧ r * Λ ≤ ε := by
    refine ⟨ε / (Λ + 1), div_pos hε (by linarith), ?_⟩
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨(volume (ball (0 : Euclid n) r)).toReal⁻¹ * ∫ x, |h x| ∂ν, fun a ha hac ha0 ha1 => ?_⟩
  have hB := Submission.cmr_tdn_ball_average_bound n X ν q h Λ a r hν hq hh hΛ ha.continuous hac
    ha0 ha1 (hdir a ha hac fun y => abs_le.2 ⟨by linarith [ha0 y], ha1 y⟩) hr
  linarith

/-- **Divergence form of `b · (div g) ∘ p_I` against `θ = dx^I`** (the projection step
`p_I^#((div g) dy) = d(p_I^#γ)` of the mass representation used for Simon 7.2.4).  Let
`p_I x = (x_{I k})_k`, `ι y = ∑ₖ y_k e_{I k}` and `G = ι ∘ g ∘ p_I`, so that
`(DG(x) v)_{I k} = (Dg(p_I x)(p_I v))_k`.  Put `η = b • θ.curryLeft ∘ G` and
`ζ = dη − (b · tr Dg ∘ p_I) • θ`.  The formula for `dη` (`cmr_df_extDeriv_smul_curryLeft`) and
Jacobi's trace identity in coordinates (`cmr_df_cons_sum_trace`) give
`ζ(x)(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`.  Hence `‖η‖ ≤ sup|b| ‖θ‖ ‖ι‖` and
`‖ζ‖ ≤ (m + 1) sup‖Db‖ ‖θ‖ ‖ι‖`, both forms vanish off `tsupport b`, and part (iii) of
`rsd_mw_tfa_norm_props` turns these operator-norm bounds into a coefficient-norm bound `K`
that does not depend on `g`. -/
theorem Submission.cmr_coordinate_divergence_form : ∀ (P m : ℕ) (I : Fin (m + 1) → Fin P) (θ : Covector (Euclid P) (m + 1)) (b : Euclid P → ℝ), StrictMono I → (∀ v : Fin (m + 1) → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → ContDiff ℝ (⊤ : ℕ∞) b → HasCompactSupport b → ∃ K : ℝ, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → (∀ y, ‖g y‖ ≤ 1) → ∃ (η : DifferentialForm (Euclid P) m) (ζ : DifferentialForm (Euclid P) (m + 1)), IsTestForm η ∧ IsTestForm ζ ∧ tsupport η ⊆ tsupport b ∧ tsupport ζ ⊆ tsupport b ∧ (∀ x, covectorEuclideanNorm (η x) ≤ K) ∧ (∀ x, covectorEuclideanNorm (ζ x) ≤ K) ∧ ∀ x, exteriorDerivative η x = (b x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ + ζ x := by
  intro P m I θ b hI hθ hb hbc
  -- the coordinate projection `p = p_I` and the coordinate embedding `ι`, `(ι y)_{I k} = y_k`
  let p : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun k => x (I k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let ι : Euclid (m + 1) →L[ℝ] Euclid P := LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun j => ∑ k, if I k = j then y k else 0)
      map_add' := fun y z => by
        ext j
        simp only [PiLp.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      map_smul' := fun c y => by
        ext j
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp }
  have hι : ∀ y k, ι y (I k) = y k := by
    intro y k
    change (∑ k', if I k' = I k then y k' else 0) = y k
    simp [hI.injective.eq_iff]
  -- the constant `K`: (F1) from `rsd_mw_tfa_norm_props` (iii), `β₀ = sup |b|`, `β₁ = sup ‖Db‖`
  obtain ⟨Cm, hCm0, hCm⟩ := (Submission.rsd_mw_tfa_norm_props P m).2.2.1
  obtain ⟨Cn, hCn0, hCn⟩ := (Submission.rsd_mw_tfa_norm_props P (m + 1)).2.2.1
  obtain ⟨β₀, hβ₀⟩ := hb.continuous.bounded_above_of_compact_support hbc
  obtain ⟨β₁, hβ₁⟩ :=
    (hb.continuous_fderiv (by simp)).bounded_above_of_compact_support (hbc.fderiv ℝ)
  have hβ₀0 : 0 ≤ β₀ := (norm_nonneg _).trans (hβ₀ 0)
  have hβ₁0 : 0 ≤ β₁ := (norm_nonneg _).trans (hβ₁ 0)
  refine ⟨Cm * (β₀ * (‖θ‖ * ‖ι‖)) + Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))), ?_⟩
  intro g hg hg1
  -- the vector field `G = ι ∘ g ∘ p`: smooth, `‖G‖ ≤ ‖ι‖`, `DG(x) = ι ∘ Dg(p x) ∘ p`
  obtain ⟨G, hG⟩ : ∃ G : Euclid P → Euclid P, G = fun x => ι (g (p x)) := ⟨_, rfl⟩
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := hG ▸ ι.contDiff.comp (hg.comp p.contDiff)
  have hGb : ∀ x, ‖G x‖ ≤ ‖ι‖ := by
    intro x
    rw [hG]
    calc ‖ι (g (p x))‖ ≤ ‖ι‖ * ‖g (p x)‖ := ι.le_opNorm _
      _ ≤ ‖ι‖ * 1 := mul_le_mul_of_nonneg_left (hg1 _) (norm_nonneg _)
      _ = ‖ι‖ := mul_one _
  have hDG : ∀ x v, fderiv ℝ G x v = ι (fderiv ℝ g (p x) (p v)) := by
    intro x v
    have hgd : DifferentiableAt ℝ g (p x) := hg.differentiable (by simp) _
    have h : HasFDerivAt G (ι.comp ((fderiv ℝ g (p x)).comp p)) x := by
      rw [hG]
      exact ι.hasFDerivAt.comp x (hgd.hasFDerivAt.comp x p.hasFDerivAt)
    rw [h.fderiv]
    rfl
  -- `(DG(x) v)_{I k} = (Dg(p x)(p v))_k`, the hypothesis of `cmr_df_cons_sum_trace`
  have hL : ∀ x (v : Euclid P) (k : Fin (m + 1)), fderiv ℝ G x v (I k) =
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap
        (WithLp.toLp 2 (fun k' => v (I k'))) k := by
    intro x v k
    rw [hDG, hι]
    rfl
  -- the forms `η = b • θ.curryLeft ∘ G` and `ζ = dη − (b · tr Dg ∘ p) • θ`
  obtain ⟨η, hη⟩ : ∃ η : DifferentialForm (Euclid P) m,
      η = fun y => b y • ContinuousAlternatingMap.curryLeft θ (G y) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : DifferentialForm (Euclid P) (m + 1),
      ζ = fun x => exteriorDerivative η x - (b x * LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap) • θ := ⟨_, rfl⟩
  -- Step 1: `η` is a test form with `tsupport η ⊆ tsupport b`
  have hηs : tsupport η ⊆ tsupport b := by
    rw [hη]
    exact tsupport_smul_subset_left b _
  have hηT : IsTestForm η := by
    refine ⟨?_, hbc.mono' ((subset_tsupport η).trans hηs)⟩
    rw [hη]
    exact hb.smul ((ContinuousAlternatingMap.curryLeft θ).contDiff.comp hGs)
  -- Steps 2-4: `dη(x)(w) = Z_x(w) + b(x) S_x(w)` and `S_x(w) = tr Dg(p x) · θ(w)`,
  -- so `ζ(x)(w) = Z_x(w) = ∑ᵢ (−1)ⁱ Db(x)(wᵢ) θ(G x, w without wᵢ)`
  have hζZ : ∀ x (w : Fin (m + 1) → Euclid P), ζ x w = ∑ i : Fin (m + 1),
      (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w))) := by
    intro x w
    have hbx : DifferentiableAt ℝ b x := hb.differentiable (by simp) x
    have hGx : DifferentiableAt ℝ G x := hGs.differentiable (by simp) x
    have h1 := Submission.cmr_df_extDeriv_smul_curryLeft P m θ b G x hbx hGx w
    have h2 := Submission.cmr_df_cons_sum_trace P m I θ
      (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap (fderiv ℝ G x) hθ (hL x) w
    have h3 : ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)) + b x * θ (Fin.cons (fderiv ℝ G x (w i))
          (i.removeNth w))) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w))) + b x * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
          θ (Fin.cons (fderiv ℝ G x (w i)) (i.removeNth w)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hζ]
    simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul]
    rw [hη, h1, h3, h2]
    ring
  -- Step 4: `ζ` is a test form with `tsupport ζ ⊆ tsupport b`
  have hζsupp : support ζ ⊆ tsupport b := by
    intro x hx
    by_contra hxb
    have hbx : b x = 0 := image_eq_zero_of_notMem_tsupport hxb
    have hdη : exteriorDerivative η x = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      hxb (hηs (tsupport_exteriorDerivative_subset η h))
    exact hx (by rw [hζ]; simp [hbx, hdη])
  have hζs : tsupport ζ ⊆ tsupport b := closure_minimal hζsupp (isClosed_tsupport b)
  have hζT : IsTestForm ζ := by
    refine ⟨?_, hbc.mono' hζsupp⟩
    let tr : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid (m + 1)) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have htr : ContDiff ℝ (⊤ : ℕ∞) fun x : Euclid P => LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (WithLp.toLp 2 (fun k => x (I k)))).toLinearMap :=
      tr.contDiff.comp ((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).comp p.contDiff)
    rw [hζ]
    exact (exteriorDerivative_isTestForm hηT).1.sub ((hb.mul htr).smul contDiff_const)
  -- Step 5: operator-norm bounds, independent of `g`
  have hη_op : ∀ x, ‖η x‖ ≤ β₀ * (‖θ‖ * ‖ι‖) := by
    intro x
    rw [hη, norm_smul]
    refine mul_le_mul (hβ₀ x) ?_ (norm_nonneg _) hβ₀0
    calc ‖ContinuousAlternatingMap.curryLeft θ (G x)‖
        ≤ ‖ContinuousAlternatingMap.curryLeft θ‖ * ‖G x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖θ‖ * ‖ι‖ := by
        rw [ContinuousAlternatingMap.norm_curryLeft]
        exact mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
  have hζ_op : ∀ x, ‖ζ x‖ ≤ ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) := by
    intro x
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun w => ?_
    rw [hζZ x w]
    have hterm : ∀ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
        θ (Fin.cons (G x) (i.removeNth w)))‖ ≤ β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
      intro i
      have h1 : ‖fderiv ℝ b x (w i)‖ ≤ β₁ * ‖w i‖ :=
        ((fderiv ℝ b x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hβ₁ x) (norm_nonneg _))
      have h2 : ‖θ (Fin.cons (G x) (i.removeNth w))‖ ≤
          ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by
        calc ‖θ (Fin.cons (G x) (i.removeNth w))‖
            ≤ ‖θ‖ * ∏ j : Fin (m + 1),
                ‖(Fin.cons (G x) (i.removeNth w) : Fin (m + 1) → Euclid P) j‖ :=
              θ.le_opNorm _
          _ = ‖θ‖ * (‖G x‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              rw [Fin.prod_univ_succ]
              simp [Fin.removeNth_apply]
          _ ≤ ‖θ‖ * (‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by
              gcongr
              exact hGb x
          _ = ‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖ := by ring
      calc ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) * θ (Fin.cons (G x) (i.removeNth w)))‖
          = ‖fderiv ℝ b x (w i)‖ * ‖θ (Fin.cons (G x) (i.removeNth w))‖ := by
            simp [norm_mul]
        _ ≤ (β₁ * ‖w i‖) * (‖θ‖ * ‖ι‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = β₁ * (‖θ‖ * ‖ι‖) * (‖w i‖ * ∏ j : Fin m, ‖w (i.succAbove j)‖) := by ring
        _ = β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ := by
            rw [Fin.prod_univ_succAbove (fun j => ‖w j‖) i]
    calc ‖∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖
        ≤ ∑ i : Fin (m + 1), ‖(-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ b x (w i) *
          θ (Fin.cons (G x) (i.removeNth w)))‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin (m + 1), β₁ * (‖θ‖ * ‖ι‖) * ∏ j, ‖w j‖ :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = ((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖)) * ∏ j, ‖w j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  -- Steps 5-6: coefficient-norm bounds by (F1), and the identity, by definition of `ζ`
  have hK1 : 0 ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := by positivity
  have hK2 : 0 ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := by positivity
  refine ⟨η, ζ, hηT, hζT, hηs, hζs, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · calc covectorEuclideanNorm (η x) ≤ Cm * ‖η x‖ := hCm _
      _ ≤ Cm * (β₀ * (‖θ‖ * ‖ι‖)) := mul_le_mul_of_nonneg_left (hη_op x) hCm0
      _ ≤ _ := le_add_of_nonneg_right hK2
  · calc covectorEuclideanNorm (ζ x) ≤ Cn * ‖ζ x‖ := hCn _
      _ ≤ Cn * (((m : ℝ) + 1) * (β₁ * (‖θ‖ * ‖ι‖))) := mul_le_mul_of_nonneg_left (hζ_op x) hCn0
      _ ≤ _ := le_add_of_nonneg_left hK1
  · rw [hζ]
    exact (add_sub_cancel _ _).symm

/-- **Simon 6.2.36** (`μ_T` charges no `Hⁿ`-null set when `M_W(∂T) < ∞` for `W ⊂⊂ U`): if
`T(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|⟨α, ξ⟩| ≤ |α|`, `M_W(T) = μ(W)` and `μ` lives on `U`, then
`Hⁿ(E) = 0` implies `μ(E) = 0`.  For `n = 0`, `H⁰` is counting measure, so `E = ∅`.  For
`n = m + 1` it suffices to treat a compact `Hⁿ`-null `C ⊆ U`; take an open `W ⊂⊂ U` around `C`.
For each strictly increasing `I`, the coordinate projection `q_I` maps `C` onto a compact
Lebesgue-null `N ⊆ ℝⁿ`, and the coordinate divergence forms give
`|∫ b ⟨θ_I, ξ⟩ div g(q_I) dμ⌞W| ≤ K_b (M_W(∂T) + M_W(T))` uniformly in `‖g‖ ≤ 1`.  Hence
`⟨θ_I, ξ⟩ = 0` `μ`-a.e. on `W ∩ q_I⁻¹(N) ⊇ C`; the coordinate covectors `θ_I` determine `ξ`, so
`ξ = 0` `μ`-a.e. on `C`, and `M_W(T) = μ(W)` forces `μ(C) = 0`. -/
theorem Submission.cmr_null_of_representation : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → μ Uᶜ = 0 → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0 := by
  intro P n U T μ ξ hU hB hUc hK hmass hξm hξ hT
  -- Step 9: it suffices to treat compact `Hⁿ`-null subsets of `U`
  refine Submission.cmr_null_of_compact_null P U μ μHE[n] hU hUc hK ?_
  intro C hC hCU hC0
  cases n with
  | zero =>
    -- Step 1: `H⁰` is counting measure, so `C = ∅`
    rw [Measure.euclideanHausdorffMeasure_zero] at hC0
    have hCe : C = ∅ := eq_empty_of_forall_notMem fun x hx => by
      simpa [hC0] using measure_mono (μ := (μH[0] : Measure (Euclid P))) (singleton_subset_iff.2 hx)
    rw [hCe, measure_empty]
  | succ m =>
    -- Step 2: an open `W ⊂⊂ U` around `C`, of finite mass and boundary mass
    obtain ⟨δ, hδ, hδU⟩ := hC.exists_cthickening_subset_open hU hCU
    have hWo : IsOpen (thickening δ C) := isOpen_thickening
    have hCW : C ⊆ thickening δ C := self_subset_thickening hδ C
    have hWcl : closure (thickening δ C) ⊆ cthickening δ C :=
      closure_thickening_subset_cthickening δ C
    have hWc : CompactlyContained (thickening δ C) U :=
      ⟨hC.cthickening.of_isClosed_subset isClosed_closure hWcl, hWcl.trans hδU⟩
    have hWU : thickening δ C ⊆ U := subset_closure.trans hWc.2
    have hμW : μ (thickening δ C) < ∞ :=
      (measure_mono subset_closure).trans_lt (hK _ hWc.1 hWc.2)
    have hTW : T.massOn (thickening δ C) = μ (thickening δ C) := hmass _ hWo
    have hTW' : T.massOn (thickening δ C) ≠ ∞ := by rw [hTW]; exact hμW.ne
    have hbd : T.boundary.massOn (thickening δ C) ≠ ∞ := (hB _ hWo hWc).ne
    -- Steps 3–6: `⟨θ_I, ξ⟩ = 0` `μ`-a.e. on `C` for each coordinate covector `θ_I`
    obtain ⟨hθex, hspan⟩ := Submission.cmr_coordinate_covectors_span P (m + 1)
    choose θI hθI using hθex
    have hcoord : ∀ I : Fin (m + 1) → Fin P, StrictMono I →
        ∀ᵐ x ∂μ, x ∈ C → ξ x (θI I) = 0 := by
      intro I hI
      set q : Euclid P → Euclid (m + 1) := fun x => WithLp.toLp 2 (fun k => x (I k))
      have hqc : Continuous q := by fun_prop
      have hN : IsCompact (q '' C) := hC.image hqc
      have hNv : volume (q '' C) = 0 :=
        Submission.cmr_volume_coordProj_image_null P (m + 1) I C hI.injective hC0
      have h := Submission.cmr_ae_zero_of_div_bounds P (m + 1) (thickening δ C) μ
        (fun x => ξ x (θI I)) q (q '' C) (covectorEuclideanNorm (θI I)) hWo hμW
        (hξm.apply_continuousLinearMap _) (fun x => hξ x _) hqc.measurable hN.measurableSet
        (fun ν h Λ hν hh hΛ => Submission.cmr_null_of_div_bound (m + 1) (Euclid P) ν q h Λ hν
          hqc.measurable hh hΛ (q '' C) hN hNv) ?_
      · filter_upwards [h] with x hx hxC
        exact hx (hCW hxC) (mem_image_of_mem q hxC)
      · -- Step 4: the divergence bound, uniformly in `g`
        intro b hb hbc hbW
        obtain ⟨K, hK⟩ :=
          Submission.cmr_coordinate_divergence_form P m I (θI I) b hI (hθI I) hb hbc
        refine ⟨K * ((T.boundary.massOn (thickening δ C)).toReal +
          (T.massOn (thickening δ C)).toReal), fun g hg _ hg1 => ?_⟩
        obtain ⟨η, ζ, hη, hζ, hηb, hζb, hηK, hζK, hd⟩ := hK g hg hg1
        exact Submission.cmr_abs_integral_div_le_mass P m U (thickening δ C) T μ ξ (θI I) b
          (fun x => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g (q x)).toLinearMap) η ζ K
          hWU hTW' hbd hT (fun k S ω r => Submission.cmr_abs_apply_le_massOn P k U _ S ω r)
          hbW hη hζ hηb hζb hηK hζK hd
    -- Step 7: the coordinate covectors determine `ξ`, so `ξ = 0` `μ`-a.e. on `C`
    have hξC : ∀ᵐ x ∂μ, x ∈ C → ξ x = 0 := by
      have hall : ∀ᵐ x ∂μ, ∀ I : Fin (m + 1) → Fin P, StrictMono I → x ∈ C →
          ξ x (θI I) = 0 := by
        rw [ae_all_iff]
        intro I
        by_cases hI : StrictMono I
        · filter_upwards [hcoord I hI] with x hx _ using hx
        · exact ae_of_all _ fun x h => absurd h hI
      filter_upwards [hall] with x hx hxC
      refine hspan (ξ x) fun I θ hI hθ => ?_
      rw [show θ = θI I from ContinuousAlternatingMap.ext fun v => by rw [hθ, hθI]]
      exact hx I hI hxC
    -- Step 8: `M_W(T) = μ(W)` and `ξ = 0` a.e. on `C` force `μ(C) = 0`
    exact Submission.cmr_measure_null_of_orient_ae_zero P (m + 1) U (thickening δ C) C T μ ξ
      hWo.measurableSet hC.measurableSet hCW hμW hTW hξ hT hξC

/-- **The mass measure and orientation of a current of locally finite mass** (Simon Ch. 6,
2.7–2.8, with the absolute continuity 2.36; `|·|` is `covectorEuclideanNorm`).  Part I is the
Riesz representation `Submission.cmr_exists_massRepresentation_core`.  It gives a Borel measure
`μ = μ_T` with `μ(ℝᴾ ∖ U) = 0`, `μ` finite on compact subsets of `U` and `μ(W) = M_W(T)` for open
`W`, and an a.e. strongly measurable field `ξ` of `n`-vectors with `|⟨α, ξ(x)⟩| ≤ |α|` and
`T(ω) = ∫ ⟨ω, ξ⟩ dμ`.  Part II is `Submission.cmr_null_of_representation`, Simon's projection
argument.  If moreover `M_W(∂T) < ∞` for every open `W ⊂⊂ U`, every such pair `(μ, ξ)` satisfies
`μ(E) = 0` whenever `Hⁿ(E) = 0`. -/
theorem Submission.cmc_exists_massRepresentation : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0) := by
  intro P n U T hU hmass
  -- Part I (Simon 6.2.7–2.8): `T = ξ μ` with `μ(W) = M_W(T)` for every open `W`
  obtain ⟨μ, ξ, hμU, hμK, hμW, hξm, hξ1, hTξ⟩ :=
    Submission.cmr_exists_massRepresentation_core P n U T hU hmass
  refine ⟨μ, ξ, hμU, hμK, hμW, hξm, hξ1, hTξ, fun hbd => ?_⟩
  -- Part II (Simon 6.2.36): if also `M_W(∂T) < ∞` for all open `W ⊂⊂ U`, then `μ ≪ Hⁿ`
  exact Submission.cmr_null_of_representation P n U T μ ξ hU hbd hμU hμK hμW hξm hξ1 hTξ

/-- **Simon Ch. 6, remark before 4.10** (integrated lower left Dini derivative).  For monotone
`F : ℝ → ℝ`, the lower integral over `(a, b)` of `D(t) = liminf_{h → 0+} (F(t) - F(t - h)) / h`
is at most `F(b) - F(a)`.  `F` is differentiable a.e. (Lebesgue), and at a point of
differentiability the left difference quotients tend to `F'(t)`, so `D = F'` a.e.  Changing the
integrand on a null set needs no measurability of `D`, and `∫_(a,b) F' ≤ F(b) - F(a)` is
`cmcs_smi_lintegral_ofReal_deriv_le`. -/
theorem Submission.cmcs_smi_lintegral_left_dini_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  -- `D = ofReal ∘ deriv F` at every point of differentiability, hence a.e.
  have hae : ∀ᵐ t, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) =
      ENNReal.ofReal (deriv F t) := by
    filter_upwards [hF.ae_differentiableAt] with t ht
    -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    have hlim : Tendsto (fun h : ℝ => (F t - F (t - h)) / h) (𝓝[>] 0) (𝓝 (deriv F t)) := by
      refine (ht.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
      simp only [Function.comp_apply, smul_eq_mul]
      rw [← sub_eq_add_neg, inv_neg, div_eq_inv_mul]
      ring
    exact (ENNReal.tendsto_ofReal hlim).liminf_eq
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0)
      = ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) := lintegral_congr_ae (ae_restrict_of_ae hae)
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_ofReal_deriv_le F a b hF

/-- **Simon Ch. 6, the remark deriving 4.10 from 4.9, for a measure on `ℝ`.**  For any measure
`ν` on `ℝ`, `∫⁻_{(a,b)} liminf_{h → 0+} h⁻¹ ν((t − h, t)) dt ≤ ν((a, b))` (Simon applies this to
`ν((s, t)) = M_W(T ⌞ {s < f < t})`).  When `ν((a, b)) < ∞`, `F(s) = ν((a, min s b))` is finite
and monotone, with `F a = 0` and `F b = ν((a, b))`.  For `0 < h < t − a`, additivity on
`(a, t − h) ∪ (t − h, t) ⊆ (a, t)` gives `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`, so the left
density is at most the lower left Dini derivative of `F`, whose integral
`cmcs_smi_lintegral_left_dini_le` bounds by `F b − F a`. -/
theorem Submission.cmcs_smi_lintegral_left_density_le : ∀ (ν : Measure ℝ) (a b : ℝ), ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤ ν (Ioo a b) := by
  intro ν a b
  by_cases hN : ν (Ioo a b) = ∞
  · rw [hN]
    exact le_top
  -- the distribution function `F(s) = ν((a, min s b))` of `ν` on `(a, b)`
  set F : ℝ → ℝ := fun s => (ν (Ioo a (min s b))).toReal with hFdef
  have hfin : ∀ s, ν (Ioo a (min s b)) ≠ ∞ := fun s =>
    ne_top_of_le_ne_top hN (measure_mono (Ioo_subset_Ioo_right (min_le_right s b)))
  have hFmono : Monotone F := fun s s' hss' =>
    ENNReal.toReal_mono (hfin s') (measure_mono (Ioo_subset_Ioo_right (min_le_min_right b hss')))
  have hofF : ∀ s, ENNReal.ofReal (F s) = ν (Ioo a (min s b)) := fun s =>
    ENNReal.ofReal_toReal (hfin s)
  have hFa : F a = 0 := by
    simp only [hFdef]
    rw [Ioo_eq_empty (not_lt.2 (min_le_left a b)), measure_empty, ENNReal.toReal_zero]
  have hFb : F b = (ν (Ioo a b)).toReal := by
    simp only [hFdef, min_self]
  -- the strip estimate: for `0 < h < t − a`, `h⁻¹ ν((t − h, t)) ≤ (F t − F (t − h)) / h`
  have hstrip : ∀ t ∈ Ioo a b, ∀ h ∈ Ioo 0 (t - a),
      ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t) ≤ ENNReal.ofReal ((F t - F (t - h)) / h) := by
    intro t ht h hh
    have hmt : min t b = t := min_eq_left ht.2.le
    have hmth : min (t - h) b = t - h := min_eq_left (by linarith [hh.1, ht.2])
    have hunion : ν (Ioo a (t - h)) + ν (Ioo (t - h) t) ≤ ν (Ioo a t) := by
      rw [← measure_union _ measurableSet_Ioo]
      · refine measure_mono (union_subset ?_ ?_)
        · exact Ioo_subset_Ioo_right (by linarith [hh.1])
        · exact Ioo_subset_Ioo_left (by linarith [hh.2])
      · rw [Set.disjoint_left]
        intro x hx1 hx2
        linarith [hx1.2, hx2.1]
    have hle : ν (Ioo (t - h) t) ≤ ENNReal.ofReal (F t - F (t - h)) := by
      rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, hofF, hofF, hmt, hmth]
      refine ENNReal.le_sub_of_add_le_left ?_ hunion
      rw [← hmth]
      exact hfin (t - h)
    calc ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)
        ≤ ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)) := mul_le_mul_right hle _
      _ = ENNReal.ofReal ((F t - F (t - h)) / h) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hh.1.le), div_eq_inv_mul]
  -- `(0, t − a) ∈ 𝓝[>] 0`, so the strip estimate compares the two liminfs on `(a, b)`
  have hpt : ∀ t ∈ Ioo a b,
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) ≤
        liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) := by
    intro t ht
    refine liminf_le_liminf ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 ht.1)] with h hh
    exact hstrip t ht h hh
  calc ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0)
      ≤ ∫⁻ t in Ioo a b, liminf (fun h : ℝ => ENNReal.ofReal ((F t - F (t - h)) / h)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo hpt
    _ ≤ ENNReal.ofReal (F b - F a) := Submission.cmcs_smi_lintegral_left_dini_le F a b hFmono
    _ = ν (Ioo a b) := by rw [hFb, hFa, sub_zero, ENNReal.ofReal_toReal hN]

/-- **Simon Ch. 6, 4.10** (integrated slice-mass bound, with `μ(W ∩ {a < f < s})` in place of
`M_W(T⌞{a < f < s})`): if `m(t) ≤ L · liminf_{h↓0} h⁻¹ μ(W ∩ {t − h < f < t})` for every
`t ∈ (a, b)`, then `∫⁻_{(a,b)} m ≤ L · μ(W ∩ {a < f < b})`.  The push-forward `ν = f_#(μ⌞W)` has
`ν((s, t)) = μ(W ∩ {s < f < t})`, so the hypothesis reads
`m(t) ≤ L · liminf_{h↓0} h⁻¹ ν((t − h, t))`; pull `L` out of the lower integral (`L ≠ ∞`) and bound
the integrated lower left density of `ν` by `ν((a, b))` (`cmcs_smi_lintegral_left_density_le`).
No measurability of `m` is needed. -/
theorem Submission.cmcs_slice_mass_integral : ∀ (P : ℕ) (μ : Measure (Euclid P)) (f : Euclid P → ℝ) (W : Set (Euclid P)) (L : NNReal) (m : ℝ → ℝ≥0∞) (a b : ℝ), Measurable f → MeasurableSet W → (∀ t ∈ Ioo a b, m t ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) → ∫⁻ t in Ioo a b, m t ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by
  intro P μ f W L m a b hf _hW hm
  -- `ν = f_#(μ⌞W)`, so `ν((s, t)) = μ(f⁻¹(s, t) ∩ W) = μ(W ∩ {s < f < t})`
  set ν : Measure ℝ := (μ.restrict W).map f with hν
  have hνI : ∀ s t : ℝ, ν (Ioo s t) = μ (W ∩ {x | s < f x ∧ f x < t}) := by
    intro s t
    rw [hν, Measure.map_apply hf measurableSet_Ioo,
      Measure.restrict_apply (hf measurableSet_Ioo), Set.inter_comm]
    rfl
  calc ∫⁻ t in Ioo a b, m t
      ≤ ∫⁻ t in Ioo a b, (L : ℝ≥0∞) *
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => by simpa only [hνI] using hm t ht
    _ = (L : ℝ≥0∞) * ∫⁻ t in Ioo a b,
          liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ν (Ioo (t - h) t)) (𝓝[>] 0) :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top
    _ ≤ (L : ℝ≥0∞) * ν (Ioo a b) :=
        mul_le_mul_right (Submission.cmcs_smi_lintegral_left_density_le ν a b) _
    _ = (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}) := by rw [hνI]

/-- **Simon Ch. 6, 4.6–4.10 (slicing by a Lipschitz function, pp. 157–158)**, for `T` and `∂T`
represented by `(μ, ξ)` and `(μ', ξ')`: `A_t = T ⌞ {f < t}` and `B_t = (∂T) ⌞ {f < t}` (2.9, taken
through the given representations) are currents in `U`, and the slice `⟨T, f, t₋⟩ = ∂A_t − B_t`
(4.6) vanishes on forms supported off `{f = t}` (4.8), has
`M_W(⟨T, f, t₋⟩) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (4.9), and
`∫⁻_{(a,b)} M_W(⟨T, f, t₋⟩) dt ≤ L · μ(W ∩ {a < f < b})` (4.10).  `A_t`, `B_t` are chosen by
`cmcs_restrict_current`; 4.8 is `cmcs_slice_support` (`f` is continuous); 4.9 is
`cmcs_slice_mass_pointwise`; 4.10 is `cmcs_slice_mass_integral` applied to `t ↦ M_W(∂A_t − B_t)`
and the bound 4.9 (`f` is measurable, `W` open hence measurable). -/
theorem Submission.cmc_slice_mass_bounds : ∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b})) := by
  intro P k U T μ μ' ξ ξ' f L _hU hμ hμ' hξm hξm' hξ hξ' hT hbT hf
  -- `A t = T ⌞ {f < t}` and `B t = (∂T) ⌞ {f < t}` (Simon 2.9)
  choose A hA using fun t : ℝ =>
    Submission.cmcs_restrict_current P (k + 1) U μ ξ {x | f x < t} hμ hξm hξ
  choose B hB using fun t : ℝ =>
    Submission.cmcs_restrict_current P k U μ' ξ' {x | f x < t} hμ' hξm' hξ'
  -- Simon 4.9, for every `W` and `t`
  have hpt : ∀ (W : Set (Euclid P)) (t : ℝ), ((A t).boundary - B t).massOn W ≤
      (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
        μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := fun W t =>
    Submission.cmcs_slice_mass_pointwise P k U T μ μ' ξ ξ' f L t (A t) (B t) W hμ hμ' hξm hξm'
      hξ hξ' hT hbT hf (hA t) (hB t)
  refine ⟨A, B, hA, hB, fun t η hη => ?_, fun W t _ => hpt W t, fun W a b hW => ?_⟩
  · -- Simon 4.8
    exact Submission.cmcs_slice_support P k U T μ μ' ξ ξ' f t (A t) (B t) hf.continuous hT hbT
      (hA t) (hB t) η hη
  · -- Simon 4.10, from 4.9 on `(a, b)`
    exact Submission.cmcs_slice_mass_integral P μ f W L
      (fun t => ((A t).boundary - B t).massOn W) a b hf.continuous.measurable hW.measurableSet
      fun t _ => hpt W t

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

/-- **Null set of points with small fillings** (Simon Ch. 6, 8.2 (4)–(6); the lower density
bound in the proof of 7.2.4).  Assume (VO).  Let `μ = μ_C` be finite on compact sets with
`M_W(C) = μ(W)` for open `W`, and `C(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|ξ| ≤ 1` `μ`-a.e.  Let
`0 ≤ κ < 1 ≤ λ`.  Suppose that every `x ∈ E` has, at arbitrarily small scales `δ`, a radius
`ρ < δ` with `μ(∂B_ρ(x)) = 0` and a filling `S` with `∂S = ∂A`, where `A = C⌞B_ρ(x)`,
`M(S) ≤ κ μ(B_ρ(x))` and `spt S ⊆ B̄_{λδ}(x)`.  Then `μ(E) = 0`.
Fix `θ ∈ (κ, 1)` and a `W`-admissible `ω`.  The cone bound for the cycle `S − A` gives
`A(ω) ≤ θ μ(B_ρ(x))` at small scales.  The covering lemma then gives
`C(ω) ≤ μ(W) − (1 − θ) μ(E')` for each piece `E' = E ∩ B_k(0) ⊆ W = B_{k+1}(0)`.  Taking the
supremum over `ω` gives `μ(W) = M_W(C) ≤ μ(W) − (1 − θ) μ(E')`, so `μ(E') = 0`. -/
theorem Submission.cbrld_measure_eq_zero_of_small_fillings : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P d : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (κ lam : ℝ) (E : Set (Euclid P)), 0 ≤ κ → κ < 1 → 1 ≤ lam → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ W : Set (Euclid P), IsOpen W → C.massOn W = μ W) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ μ (sphere x ρ) = 0 ∧ ∃ (A S : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ y in ball x ρ, ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂μ) ∧ S.boundary = A.boundary ∧ S.mass ≤ ENNReal.ofReal κ * μ (ball x ρ) ∧ S.support ⊆ closedBall x (lam * δ)) → μ E = 0 := by
  intro hVO P d C μ ξ κ lam E hκ0 hκ1 hlam hμK hCμ hξm hξ hCξ hE
  have hball_fin : ∀ (x : Euclid P) (r : ℝ), μ (ball x r) < ∞ := fun x r =>
    (measure_mono ball_subset_closedBall).trans_lt (hμK _ (isCompact_closedBall x r))
  -- a fixed `θ ∈ (κ, 1)` plays the role of `κ + ε` in the covering lemma
  obtain ⟨θ, hκθ, hθ1⟩ := exists_between hκ1
  have hlam0 : 0 < lam := by linarith
  -- Steps 3–4: a piece `E' ⊆ E` inside an open `W` of finite measure is `μ`-null
  have hpiece : ∀ E' W : Set (Euclid P), E' ⊆ E → IsOpen W → E' ⊆ W → μ W < ∞ → μ E' = 0 := by
    intro E' W hE'E hWo hE'W hWfin
    have hE'fin : μ E' < ∞ := (measure_mono hE'W).trans_lt hWfin
    -- Step 3: every `W`-admissible `ω` satisfies `C(ω) ≤ μ(W) - (1 - θ) μ(E')`
    have hest : ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid P)) (d + 1) W,
        C ω ≤ (μ W).toReal - (1 - θ) * (μ E').toReal := by
      intro ω hω
      have hωc : Continuous (ω : DifferentialForm (Euclid P) (d + 1)) :=
        ContDiff.continuous ω.property.1.1
      -- `g(y) = ξ(y)(ω(y))` is `μ`-a.e. strongly measurable with `|g| ≤ 1` `μ`-a.e.
      have hgm : AEStronglyMeasurable
          (fun y => ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y)) μ :=
        (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hξm.prodMk hωc.aestronglyMeasurable) :)
      have hg1 : ∀ᵐ y ∂μ, |ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y)| ≤ 1 := by
        filter_upwards [hξ] with y hy
        exact (hy _).trans (hω.2 y)
      -- `g = 0` off `W`, so `C(ω) = ∫_W g dμ`
      have hCW : C ω = ∫ y in W, ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂μ := by
        rw [hCξ ω]
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
        rw [image_eq_zero_of_notMem_tsupport fun h => hy (hω.1 h), map_zero]
      -- the cone constant of `ω`
      obtain ⟨c, hc, hcone⟩ := Submission.cbrld_cycle_eval_le_radius_mul_mass hVO P d ω
      have hden : 0 < (c + 1) * lam * (1 + κ) :=
        mul_pos (mul_pos (by linarith) hlam0) (by linarith)
      obtain ⟨δ₀, hδ₀⟩ : ∃ δ₀ : ℝ, δ₀ = (θ - κ) / ((c + 1) * lam * (1 + κ)) := ⟨_, rfl⟩
      have hδ₀pos : 0 < δ₀ := by rw [hδ₀]; exact div_pos (by linarith) hden
      have hδ₀eq : δ₀ * ((c + 1) * lam * (1 + κ)) = θ - κ := by
        rw [hδ₀]; exact div_mul_cancel₀ _ hden.ne'
      -- Step 3(i): `∫_{B̄_ρ(x)} g dμ ≤ θ μ(B̄_ρ(x))` at arbitrarily small radii
      have hsmall : ∀ x ∈ E', ∀ δ' : ℝ, 0 < δ' → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ' ∧
          ∫ y in closedBall x ρ, ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y) ∂μ ≤
            θ * (μ (closedBall x ρ)).toReal := by
        intro x hx δ' hδ'
        have hδpos : 0 < min δ' δ₀ := lt_min hδ' hδ₀pos
        obtain ⟨ρ, hρ0, hρδ, hsph, A, S, hA, hbd, hSm, hSs⟩ := hE x (hE'E hx) (min δ' δ₀) hδpos
        refine ⟨ρ, hρ0, hρδ.trans_le (min_le_left _ _), ?_⟩
        have hR : 0 < lam * min δ' δ₀ := mul_pos hlam0 hδpos
        have hAs : A.support ⊆ closedBall x (lam * min δ' δ₀) :=
          (Submission.cbrld_ns_ball_current_support_subset P (d + 1) μ ξ A x ρ hA).trans
            (closedBall_subset_closedBall (hρδ.le.trans (le_mul_of_one_le_left hδpos.le hlam)))
        -- comparison with the cycle `S - A` at scale `R = λ min(δ', δ₀)`
        have hcmp := Submission.cbrld_ns_eval_le_of_small_filling P d A S ω (μ (ball x ρ)) x c κ
          (lam * min δ' δ₀) hc hκ0 hR (hball_fin x ρ) hω.2 hcone hbd
          (Submission.cbrld_ns_ball_current_mass_le P (d + 1) μ ξ A x ρ hξ hA) hSm hAs hSs
        have hcR : c * (lam * min δ' δ₀) * (1 + κ) ≤ θ - κ := by
          have h1 : 0 ≤ c * lam * (1 + κ) := mul_nonneg (mul_nonneg hc hlam0.le) (by linarith)
          have h2 : c * lam * (1 + κ) ≤ (c + 1) * lam * (1 + κ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hlam0.le)
              (by linarith)
          calc c * (lam * min δ' δ₀) * (1 + κ) = c * lam * (1 + κ) * min δ' δ₀ := by ring
            _ ≤ c * lam * (1 + κ) * δ₀ := mul_le_mul_of_nonneg_left (min_le_right _ _) h1
            _ ≤ (c + 1) * lam * (1 + κ) * δ₀ := mul_le_mul_of_nonneg_right h2 hδ₀pos.le
            _ = θ - κ := by rw [← hδ₀eq]; ring
        -- `μ(∂B_ρ(x)) = 0`, so closed and open balls agree `μ`-a.e.
        have hae : closedBall x ρ =ᵐ[μ] ball x ρ := by
          refine ae_eq_set.2 ⟨by rw [closedBall_sdiff_ball]; exact hsph, ?_⟩
          rw [sdiff_eq_empty.2 ball_subset_closedBall, measure_empty]
        rw [setIntegral_congr_set hae, measure_congr hae, ← hA ω]
        calc A ω ≤ (κ + c * (lam * min δ' δ₀) * (1 + κ)) * (μ (ball x ρ)).toReal := hcmp
          _ ≤ θ * (μ (ball x ρ)).toReal :=
            mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
      -- Step 3(ii): the covering lemma with `θ`
      rw [hCW]
      exact Submission.cbrld_vitali_setIntegral_le P μ
        (fun y => ξ y ((ω : DifferentialForm (Euclid P) (d + 1)) y)) θ E' W hμK hgm hg1
        hθ1.le hWo hE'W hWfin hsmall
    -- Step 4: `μ(W) = M_W(C) ≤ max(μ(W) - (1 - θ) μ(E'), 0)`
    have hmass : C.massOn W ≤ ENNReal.ofReal (max ((μ W).toReal - (1 - θ) * (μ E').toReal) 0) := by
      refine sSup_le ?_
      rintro _ ⟨ω, hω, rfl⟩
      exact ENNReal.ofReal_le_ofReal ((hest ω hω).trans (le_max_left _ _))
    rw [hCμ W hWo] at hmass
    have hreal := ENNReal.toReal_le_of_le_ofReal (le_max_right _ _) hmass
    by_contra hne
    have hpos : 0 < (μ E').toReal := ENNReal.toReal_pos hne hE'fin.ne
    have hWpos : 0 < (μ W).toReal :=
      hpos.trans_le (ENNReal.toReal_mono hWfin.ne (measure_mono hE'W))
    have hprod : 0 < (1 - θ) * (μ E').toReal := mul_pos (by linarith) hpos
    rcases le_total ((μ W).toReal - (1 - θ) * (μ E').toReal) 0 with h | h
    · rw [max_eq_right h] at hreal
      linarith
    · rw [max_eq_left h] at hreal
      linarith
  -- Step 2: `E = ⋃ₖ (E ∩ B_k(0))`, and each piece lies in the open `B_{k+1}(0)`
  have hcover : E ⊆ ⋃ k : ℕ, E ∩ ball (0 : Euclid P) k := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_nat_gt (dist y 0)
    exact mem_iUnion.2 ⟨k, hy, mem_ball.2 hk⟩
  exact measure_mono_null hcover (measure_iUnion_null fun k : ℕ =>
    hpiece (E ∩ ball (0 : Euclid P) k) (ball (0 : Euclid P) (k + 1)) inter_subset_left isOpen_ball
      (fun z hz => ball_subset_ball (by linarith) hz.2) (hball_fin _ _))

end GMT.Ch07
