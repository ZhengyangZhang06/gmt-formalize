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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
