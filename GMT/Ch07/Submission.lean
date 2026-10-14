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

/-- Directional derivatives of test forms are test forms: if `φ ∈ 𝒟^q(ℝᴾ)` and `v ∈ ℝᴾ`, then
`z ↦ Dφ(z)[v]` is again `C^∞` (`Dφ` is `C^∞`, as `∞ + 1 ≤ ∞`) with compact support
(`spt Dφ ⊆ spt φ`, and evaluation at `v` maps `0` to `0`). -/
theorem Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply : ∀ (P q : ℕ) (φ : DifferentialForm (Euclid P) q) (v : Euclid P), IsTestForm φ → IsTestForm (fun z => fderiv ℝ φ z v) := by
  rintro P q φ v ⟨hs, hc⟩
  refine ⟨?_, ?_⟩
  · -- `Dφ` is `C^∞`, hence so is its evaluation at the constant vector `v`
    exact (hs.fderiv_right (by simp)).clm_apply contDiff_const
  · -- `Dφ` has compact support, and `L ↦ L v` maps `0` to `0`
    exact (hc.fderiv ℝ).comp_left (g := fun L : Euclid P →L[ℝ] Covector (Euclid P) q => L v) rfl
/-- **Splitting the contracted exterior derivative** (Step 1 of the cube Stokes formula in the proof
of Simon 7.3.5, where minimality passes from `[[L]] × S₀` to `S₀`).  Let `g = (g₀, …, g_j)` be
vectors in `ℝᴾ` and let `flatD`, `flat`, `flatF a` contract covectors with `g`, resp. with `g`
without `g_a`: `flatD α v = α(g, v)`, `flat α v = α(g, v)`, `flatF a α v = α(g ∘ a.succAbove, v)`.
If the `n'`-form `ω` is differentiable at `x`, then
`flatD(dω(x)) = Σₐ (−1)ᵃ D[flatF a ∘ ω](x)[g_a] + (−1)^{j+1} d[flat ∘ ω](x)`.
Evaluate at a tuple `w` and put `V = (g, w)`.  As `dω(x)(V) = Σᵢ (−1)ⁱ (Dω(x)[Vᵢ])(V without Vᵢ)`,
`D[flatF a ∘ ω](x) = flatF a ∘ Dω(x)` and `D[flat ∘ ω](x) = flat ∘ Dω(x)`, both sides are
alternating sums of values of `Dω(x)`.  Split the sum over `i < n' + 1` at `j + 1`: the index
`a < j + 1` carries `g_a`, and omitting it leaves `(g ∘ a.succAbove, w)`; the index `j + 1 + l`
carries `w_l`, and omitting it leaves `(g, w without w_l)`, with sign `(−1)^{j+1}(−1)ˡ`. -/
theorem Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split : ∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : DifferentialForm (Euclid P) n') (x : Euclid P), DifferentiableAt ℝ ω x → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → flatD (exteriorDerivative ω x) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) • fderiv ℝ (fun z => flatF a (ω z)) x (g a) + (-1 : ℝ) ^ (j + 1) • exteriorDerivative (fun z => flat (ω z)) x := by
  intro P j m n' g h h₁ h₂ flatD flat flatF ω x hω hflatD hflat hflatF
  -- Step 1: chain rule, `D[flatF a ∘ ω](x) = flatF a ∘ Dω(x)` and `D[flat ∘ ω](x) = flat ∘ Dω(x)`
  have hβ : ∀ a, fderiv ℝ (fun z => flatF a (ω z)) x = (flatF a).comp (fderiv ℝ ω x) := fun a =>
    ((flatF a).hasFDerivAt.comp x hω.hasFDerivAt).fderiv
  have hγ : fderiv ℝ (fun z => flat (ω z)) x = flat.comp (fderiv ℝ ω x) :=
    (flat.hasFDerivAt.comp x hω.hasFDerivAt).fderiv
  -- Step 5: value formulas for `Fin.append` and `Fin.succAbove`
  have happL : ∀ {p q : ℕ} (u : Fin p → Euclid P) (v : Fin q → Euclid P) (k : Fin (p + q))
      (hk : (k : ℕ) < p), Fin.append u v k = u ⟨k, hk⟩ := fun u v k hk =>
    Fin.append_left u v ⟨k, hk⟩
  have happR : ∀ {p q : ℕ} (u : Fin p → Euclid P) (v : Fin q → Euclid P) (k : Fin (p + q))
      (hk : p ≤ (k : ℕ)), Fin.append u v k = v ⟨k - p, by have := k.isLt; omega⟩ := by
    intro p q u v k hk
    rw [← Fin.append_right u v ⟨k - p, by have := k.isLt; omega⟩]
    congr 1
    ext
    simp only [Fin.val_natAdd]
    omega
  have hsA : ∀ {N : ℕ} (p : Fin (N + 1)) (i : Fin N),
      ((p.succAbove i : Fin (N + 1)) : ℕ) = if (i : ℕ) < p then (i : ℕ) else i + 1 := by
    intro N p i
    rcases Nat.lt_or_ge (i : ℕ) p with hip | hip
    · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 hip), ite_eq_left hip]
      rfl
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 hip), ite_eq_right (by omega)]
      rfl
  -- Steps 2–4: evaluate at `w`; both sides become alternating sums of values of `Dω(x)`
  ext w
  rw [hflatD]
  simp only [exteriorDerivative, extDeriv, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, hβ, hγ, ContinuousLinearMap.comp_apply, hflatF, hflat]
  -- Step 7: omitting the index of value `a` from `V = (g, w)` leaves `(g ∘ a.succAbove, w)`
  have e2 : ∀ (a : Fin (j + 1)) (i : Fin (n' + 1)), (i : ℕ) = a →
      i.removeNth (Fin.append g w ∘ Fin.cast h₁) =
        Fin.append (g ∘ a.succAbove) w ∘ Fin.cast h₂ := by
    intro a i hi
    funext l
    have ha := a.isLt
    have hs := hsA i l
    rw [hi] at hs
    simp only [Fin.removeNth, Function.comp_apply]
    rcases Nat.lt_or_ge (l : ℕ) j with hlj | hlj
    · have hk1 : (Fin.cast h₂ l : ℕ) < j := by simpa using hlj
      have hk2 : (Fin.cast h₁ (i.succAbove l) : ℕ) < j + 1 := by
        rw [Fin.val_cast, hs]; split_ifs <;> omega
      rw [happL _ _ _ hk1, happL _ _ _ hk2, Function.comp_apply]
      congr 1
      ext
      simp only [Fin.val_cast, hs, hsA]
    · have hla : ¬ (l : ℕ) < a := by omega
      rw [ite_eq_right hla] at hs
      have hk1 : j ≤ (Fin.cast h₂ l : ℕ) := by simpa using hlj
      have hk2 : j + 1 ≤ (Fin.cast h₁ (i.succAbove l) : ℕ) := by
        rw [Fin.val_cast, hs]; omega
      rw [happR _ _ _ hk1, happR _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs]
      omega
  -- Step 8: omitting the index of value `j + 1 + l` from `V = (g, w)` leaves `(g, w without w_l)`
  have e4 : ∀ (l : Fin (m + 1)) (i : Fin (n' + 1)), (i : ℕ) = j + 1 + l →
      i.removeNth (Fin.append g w ∘ Fin.cast h₁) = Fin.append g (l.removeNth w) ∘ Fin.cast h := by
    intro l i hi
    funext k
    have hs := hsA i k
    rw [hi] at hs
    simp only [Fin.removeNth, Function.comp_apply]
    rcases Nat.lt_or_ge (k : ℕ) (j + 1) with hkj | hkj
    · rw [ite_eq_left (by omega)] at hs
      have hk1 : (Fin.cast h k : ℕ) < j + 1 := by simpa using hkj
      have hk2 : (Fin.cast h₁ (i.succAbove k) : ℕ) < j + 1 := by
        rw [Fin.val_cast, hs]; omega
      rw [happL _ _ _ hk1, happL _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs]
    · have hk1 : j + 1 ≤ (Fin.cast h k : ℕ) := by simpa using hkj
      have hk2 : j + 1 ≤ (Fin.cast h₁ (i.succAbove k) : ℕ) := by
        rw [Fin.val_cast, hs]; split_ifs <;> omega
      rw [happR _ _ _ hk1, happR _ _ _ hk2]
      congr 1
      ext
      simp only [Fin.val_cast, hs, hsA]
      split_ifs <;> omega
  -- Step 6: reindex along `Fin.cast h₁` and split the sum at `j + 1`
  rw [← Fin.sum_congr' _ h₁.symm, Fin.sum_univ_add (a := j + 1) (b := m + 1)]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hi : (((Fin.castAdd (m + 1) a).cast h₁.symm : Fin (n' + 1)) : ℕ) = a := by simp
    rw [e2 a _ hi]
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_left, hi,
      zsmul_eq_mul, smul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  · -- the sign `(−1)^{(j+1)+l} = (−1)^{j+1}(−1)^l`
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hi : (((Fin.natAdd (j + 1) l).cast h₁.symm : Fin (n' + 1)) : ℕ) = j + 1 + l := by simp
    rw [e4 l _ hi]
    simp only [Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self, Fin.append_right, hi,
      zsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
/-- **Interior product with a frame; translated test forms.**  (a) For `g = (g₁, …, g_k)` in
`ℝᴾ` and `n' = k + m`, `♭α(v) = α(g₁, …, g_k, v₁, …, v_m)` defines a continuous linear map
`♭ : Λ^{n'} → Λ^m`.  Updating `vⱼ` updates only the entry `natAdd k j` of `(g, v)`, so `♭α` is
multilinear; it is alternating because equal entries of `v` stay at distinct indices; it is
continuous; and `‖♭α‖ ≤ (∏ᵢ ‖gᵢ‖) ‖α‖`, so `α ↦ ♭α` is bounded (`LinearMap.mkContinuous`).
(b) For a continuous linear `Φ : Λᵃ → Λᵇ`, a test `a`-form `ω` and `t ∈ ℝᴾ`, `y ↦ Φ(ω(t + y))`
is smooth and vanishes off the closed set `{y : t + y ∈ spt ω}`, the compact translate
`spt ω − t`; hence it is a test form supported there.  This is the interior product `♭_g` of
the product construction `[[E]] ×_g A` used to split off the spine of a cone. -/
theorem Submission.dimred_cs_sos_mt_interior_product : ∀ P : ℕ, (∀ (k m n' : ℕ) (g : Fin k → Euclid P) (h : n' = k + m), ∃ flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m, ∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) ∧ ∀ (a b : ℕ) (flat : Covector (Euclid P) a →L[ℝ] Covector (Euclid P) b) (ω : DifferentialForm (Euclid P) a) (t : Euclid P), IsTestForm ω → IsTestForm (fun y => flat (ω (t + y))) ∧ tsupport (fun y => flat (ω (t + y))) ⊆ (fun y => t + y) ⁻¹' tsupport ω := by
  intro P
  refine ⟨fun k m n' g h => ?_, fun a b flat ω t hω => ?_⟩
  · -- (a) the interior product with the frame `g`; first identify `n'` with `k + m`
    subst h
    -- the entries `castAdd m i` (from `g`) and `natAdd k j` (from `v`) are distinct
    have hne : ∀ (i : Fin k) (j : Fin m), Fin.castAdd m i ≠ Fin.natAdd k j := by
      intro i j hc
      have hv := congrArg Fin.val hc
      have hi := i.isLt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    -- updating `v` at `j` updates `Fin.append g v` at `natAdd k j` (for any `DecidableEq`)
    have hupd : ∀ (_ : DecidableEq (Fin m)) (v : Fin m → Euclid P) (j : Fin m) (x : Euclid P),
        Fin.append g (Function.update v j x) =
          Function.update (Fin.append g v) (Fin.natAdd k j) x := by
      intro _ v j x
      funext z
      induction z using Fin.addCases with
      | left i => rw [Fin.append_left, Function.update_of_ne (hne i j), Fin.append_left]
      | right j' =>
        rw [Fin.append_right, Function.update_apply_of_injective _ (Fin.natAdd_injective m k)]
        congr 1
        funext i
        rw [Fin.append_right]
    -- `v ↦ Fin.append g v` is continuous: each entry is a constant `gᵢ` or a projection `vⱼ`
    have hcont : Continuous fun v : Fin m → Euclid P => Fin.append g v := by
      refine continuous_pi fun z => ?_
      induction z using Fin.addCases with
      | left i => simp only [Fin.append_left]; exact continuous_const
      | right j => simp only [Fin.append_right]; exact continuous_apply j
    -- `♭α (v) = α (g, v)` is a continuous alternating map
    let φ : Covector (Euclid P) (k + m) → Covector (Euclid P) m := fun α =>
      { toFun := fun v => α (Fin.append g v)
        map_update_add' := fun v j x y => by
          simp only [hupd _ v j, α.map_update_add]
        map_update_smul' := fun v j c x => by
          simp only [hupd _ v j, α.map_update_smul]
        cont := α.cont.comp hcont
        map_eq_zero_of_eq' := fun v i j hv hij =>
          α.map_eq_zero_of_eq (Fin.append g v) (i := Fin.natAdd k i) (j := Fin.natAdd k j)
            (by rw [Fin.append_right, Fin.append_right]; exact hv)
            ((Fin.natAdd_injective m k).ne hij) }
    have hφ : ∀ α v, φ α v = α (Fin.append g v) := fun α v => rfl
    -- `α ↦ ♭α` is linear
    let L : Covector (Euclid P) (k + m) →ₗ[ℝ] Covector (Euclid P) m :=
      { toFun := φ
        map_add' := fun α β => by
          ext v
          simp only [hφ, ContinuousAlternatingMap.add_apply]
        map_smul' := fun c α => by
          ext v
          simp only [hφ, ContinuousAlternatingMap.smul_apply, RingHom.id_apply] }
    -- and bounded: `|α (g, v)| ≤ ‖α‖ ∏ᵢ ‖gᵢ‖ ∏ⱼ ‖vⱼ‖`, so `‖♭α‖ ≤ (∏ᵢ ‖gᵢ‖) ‖α‖`
    have hbound : ∀ α, ‖L α‖ ≤ (∏ i, ‖g i‖) * ‖α‖ := by
      intro α
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
      calc ‖L α v‖ = ‖α (Fin.append g v)‖ := rfl
        _ ≤ ‖α‖ * ∏ z, ‖Fin.append g v z‖ := α.le_opNorm _
        _ = (∏ i, ‖g i‖) * ‖α‖ * ∏ j, ‖v j‖ := by
          rw [Fin.prod_univ_add]
          simp only [Fin.append_left, Fin.append_right]
          ring
    refine ⟨L.mkContinuous (∏ i, ‖g i‖) hbound, fun α v => ?_⟩
    rw [LinearMap.mkContinuous_apply, Fin.cast_refl, Function.comp_id]
    rfl
  · -- (b) off `{y : t + y ∈ spt ω}` the form `ω (t + y)` vanishes, hence so does its image
    have hsub : tsupport (fun y => flat (ω (t + y))) ⊆ (fun y => t + y) ⁻¹' tsupport ω := by
      refine closure_minimal (fun y hy => ?_)
        ((isClosed_tsupport ω).preimage (continuous_const.add continuous_id))
      by_contra hy'
      apply hy
      show flat (ω (t + y)) = 0
      rw [image_eq_zero_of_notMem_tsupport (f := ω) (x := t + y) hy', map_zero]
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ω := hω.1
    -- `{y : t + y ∈ spt ω}` is the compact translate `spt ω − t`
    have hK : IsCompact ((fun y => t + y) ⁻¹' tsupport ω) := by
      have hK' := (Homeomorph.addLeft t).isCompact_preimage.mpr hω.2
      rwa [Homeomorph.coe_addLeft] at hK'
    refine ⟨⟨?_, ?_⟩, hsub⟩
    · exact flat.contDiff.comp (hs.comp (contDiff_const.add contDiff_id))
    · exact hK.of_isClosed_subset (isClosed_tsupport _) hsub

/-- **Boundary on translated forms.**  If `∂Y = X` in `ℝᴾ`, `γ` is a test `m`-form and
`t ∈ ℝᴾ`, then `Y(d(γ(t + ·))) = X(γ(t + ·))`, both sides read by `currentEval`.  The translate
`γₜ = γ(t + ·)` is a test form (`dimred_cs_sos_mt_interior_product` (b) with `Φ = id`), and
translation commutes with `d`: `D(γ(t + ·))(y) = Dγ(t + y)` (`fderiv_comp_add_left`), so
`dγₜ = (dγ)(t + ·)`.  Hence both arguments are test forms supported in `ℝᴾ`, `currentEval`
evaluates the currents on them, and `Y(dγₜ) = ∂Y(γₜ) = X(γₜ)`. -/
theorem Submission.dimred_cs_sos_mt_cs_translate_boundary_eval : ∀ (P m : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (γ : DifferentialForm (Euclid P) m) (t : Euclid P), Y.boundary = X → IsTestForm γ → currentEval Y (fun y => exteriorDerivative γ (t + y)) = currentEval X (fun y => γ (t + y)) := by
  intro P m X Y γ t hYX hγ
  subst hYX
  -- the translate `γₜ = γ(t + ·)` is a test form (interior product (b) with `Φ = id`)
  have hγt : IsTestForm (fun y => γ (t + y)) :=
    ((Submission.dimred_cs_sos_mt_interior_product P).2 m m
      (ContinuousLinearMap.id ℝ (Covector (Euclid P) m)) γ t hγ).1
  -- translation commutes with `d`, since `D(γ(t + ·))(y) = Dγ(t + y)`
  have hd : exteriorDerivative (fun y => γ (t + y)) = fun y => exteriorDerivative γ (t + y) := by
    funext y
    show ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ (fun y => γ (t + y)) y) =
      ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ γ (t + y))
    rw [fderiv_comp_add_left]
  -- both forms are test forms supported in `ℝᴾ`, so `currentEval` evaluates on them
  have hmem : IsTestForm (fun y => γ (t + y)) ∧ tsupport (fun y => γ (t + y)) ⊆ univ :=
    ⟨hγt, subset_univ _⟩
  have hdmem : IsTestForm (fun y => exteriorDerivative γ (t + y)) ∧
      tsupport (fun y => exteriorDerivative γ (t + y)) ⊆ univ :=
    ⟨hd ▸ exteriorDerivative_isTestForm hγt, subset_univ _⟩
  -- unfold `currentEval`; `∂Y(γₜ) = Y(dγₜ)` and `dγₜ = (dγ)(t + ·)` as test forms
  rw [currentEval, currentEval, dite_eq_left hdmem, dite_eq_left hmem,
    GeometricCurrentOn.boundary_apply]
  exact congrArg Y (Subtype.ext hd.symm)

/-- **Slice identity for one translate.**  Write `β_a = ♭_{g ∘ a.succAbove} ω`, `γ = ♭_g ω` and
`δ_a = D_{g_a} β_a`.  At every point `t + y` the contraction of `dω` with the frame splits as
`♭_g dω = Σ_a (−1)^a δ_a + (−1)^{j+1} dγ` (`flat_extDeriv_split`).  Every translated form here
is a test form (interior product (b), `isTestForm_fderiv_apply`, `exteriorDerivative_isTestForm`),
so `Y` evaluates the splitting linearly, and the last term is
`Y(dγ(t + ·)) = ∂Y(γ(t + ·)) = X(γ(t + ·))` (`translate_boundary_eval`). -/
theorem Submission.dimred_cs_sos_mt_cs_slice_identity : ∀ (P j m n' : ℕ) (g : Fin (j + 1) → Euclid P) (h : n' = (j + 1) + m) (h₁ : n' + 1 = (j + 1) + (m + 1)) (h₂ : n' = j + (m + 1)) (X : GeometricCurrentOn (univ : Set (Euclid P)) m) (Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (flatD : Covector (Euclid P) (n' + 1) →L[ℝ] Covector (Euclid P) (m + 1)) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) m) (flatF : Fin (j + 1) → Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) (m + 1)) (ω : TestFormOn (univ : Set (Euclid P)) n') (t : Euclid P), Y.boundary = X → (∀ (α : Covector (Euclid P) (n' + 1)) (v : Fin (m + 1) → Euclid P), flatD α v = α (Fin.append g v ∘ Fin.cast h₁)) → (∀ (α : Covector (Euclid P) n') (v : Fin m → Euclid P), flat α v = α (Fin.append g v ∘ Fin.cast h)) → (∀ (a : Fin (j + 1)) (α : Covector (Euclid P) n') (v : Fin (m + 1) → Euclid P), flatF a α v = α (Fin.append (g ∘ a.succAbove) v ∘ Fin.cast h₂)) → currentEval Y (fun y => flatD (exteriorDerivative (ω : DifferentialForm (Euclid P) n') (t + y))) = ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) * currentEval Y (fun y => fderiv ℝ (fun z => flatF a ((ω : DifferentialForm (Euclid P) n') z)) (t + y) (g a)) + (-1 : ℝ) ^ (j + 1) * currentEval X (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) := by
  intro P j m n' g h h₁ h₂ X Y flatD flat flatF ω t hYX hD hflat hF
  -- `currentEval` is the current itself on test forms (every support lies in `univ`)
  have hev : ∀ (k : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (φ : DifferentialForm (Euclid P) k) (hφ : IsTestForm φ ∧ tsupport φ ⊆ univ),
      currentEval T φ = T ⟨φ, hφ⟩ := by
    intro k T φ hφ
    rw [currentEval, dite_eq_left hφ]
  -- work with the underlying form `w` of `ω`
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n') := ω.property.1
  generalize (ω : DifferentialForm (Euclid P) n') = w at hω ⊢
  -- `β_a = flatF a ∘ w` and `γ = flat ∘ w` are test forms (interior product (b), translate by `0`)
  have hβ : ∀ a : Fin (j + 1), IsTestForm (fun z => flatF a (w z)) := fun a => by
    simpa only [zero_add] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 n' (m + 1) (flatF a) w 0 hω).1
  have hγ : IsTestForm (fun z => flat (w z)) := by
    simpa only [zero_add] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 n' m flat w 0 hω).1
  -- the translates `♭_g dw (t + ·)`, `δ_a (t + ·)` and `dγ (t + ·)` are test forms
  have hFt : IsTestForm (fun y => flatD (exteriorDerivative w (t + y))) :=
    ((Submission.dimred_cs_sos_mt_interior_product P).2 (n' + 1) (m + 1) flatD _ t
      (exteriorDerivative_isTestForm hω)).1
  have hAt : ∀ a : Fin (j + 1),
      IsTestForm (fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a)) := fun a => by
    simpa only [ContinuousLinearMap.id_apply] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 (m + 1) (m + 1)
        (ContinuousLinearMap.id ℝ _) _ t
        (Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply P (m + 1) _ (g a) (hβ a))).1
  have hDt : IsTestForm (fun y => exteriorDerivative (fun z => flat (w z)) (t + y)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      ((Submission.dimred_cs_sos_mt_interior_product P).2 (m + 1) (m + 1)
        (ContinuousLinearMap.id ℝ _) _ t (exteriorDerivative_isTestForm hγ)).1
  -- the pointwise splitting at `t + y`, read as an identity of test forms in `ℝᴾ`
  have hsplit : (⟨fun y => flatD (exteriorDerivative w (t + y)), hFt, subset_univ _⟩ :
        TestFormOn (univ : Set (Euclid P)) (m + 1)) =
      ∑ a : Fin (j + 1), (-1 : ℝ) ^ (a : ℕ) •
        (⟨fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a), hAt a, subset_univ _⟩ :
          TestFormOn (univ : Set (Euclid P)) (m + 1)) +
      (-1 : ℝ) ^ (j + 1) •
        (⟨fun y => exteriorDerivative (fun z => flat (w z)) (t + y), hDt, subset_univ _⟩ :
          TestFormOn (univ : Set (Euclid P)) (m + 1)) := by
    refine Subtype.ext (funext fun y => ?_)
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.add_apply, Pi.smul_apply]
    exact Submission.dimred_cs_sos_mt_cs_flat_extDeriv_split P j m n' g h h₁ h₂ flatD flat flatF
      w (t + y) ((hω.1.differentiable (by simp)).differentiableAt) hD hflat hF
  -- the boundary term: `Y(dγ(t + ·)) = X(γ(t + ·))`
  have hbd : currentEval Y (fun y => exteriorDerivative (fun z => flat (w z)) (t + y)) =
      currentEval X (fun y => flat (w (t + y))) :=
    Submission.dimred_cs_sos_mt_cs_translate_boundary_eval P m X Y _ t hYX hγ
  have hA : ∀ a : Fin (j + 1),
      currentEval Y (fun y => fderiv ℝ (fun z => flatF a (w z)) (t + y) (g a)) =
        Y ⟨_, hAt a, subset_univ _⟩ := fun a => hev _ Y _ ⟨hAt a, subset_univ _⟩
  -- linearity of `Y`
  rw [← hbd, hev _ Y _ ⟨hFt, subset_univ _⟩, hev _ Y _ ⟨hDt, subset_univ _⟩, hsplit]
  simp only [map_add, map_sum, map_smul, smul_eq_mul, hA]
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

/-- Differentiation under the integral sign for the translations `y ↦ sv + y`: for every `t`,
`s ↦ τ(M, θ, ξ)(ω(sv + ·))` has derivative `τ(M, θ, ξ)(Dω(tv + ·)[v])` at `t`.  For
`s ∈ (t − 1, t + 1)` the integrands vanish off `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖` where
`spt ω ⊆ B̄_r(0)`, and are dominated by `K θ 1_B`, `K` bounding the continuous map
`(s, y) ↦ Dω(sv + y)[v]` on `[t − 1, t + 1] × B` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is integrable since
`θ` is locally `Hⁿ`-integrable. -/
theorem Submission.dimred_cs_ti_translate_action_hasDerivAt : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (ω : TestFormOn (univ : Set (Euclid P)) n) (v : Euclid P) (t : ℝ), HasDerivAt (fun s : ℝ => R.action (fun y => (ω : DifferentialForm (Euclid P) n) (s • v + y))) (R.action (fun y => fderiv ℝ (ω : DifferentialForm (Euclid P) n) (t • v + y) v)) t := by
  intro P n R ω v t
  have hws : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) n) := ω.property.1.1
  have hwc : HasCompactSupport (ω : DifferentialForm (Euclid P) n) := ω.property.1.2
  set w : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hw_def
  -- Step 1: `‖ξ(x)‖ ≤ 1` for `Hⁿ⌞M`-a.e. `x`
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact Submission.unit_orientation_norm_le_one P n Q _ hQ
  -- Step 2: a support radius `r` and a bound `K0` for `ω`; `ω` and `Dω` vanish off `spt ω`
  have hwcont : Continuous w := hws.continuous
  have hDw : Continuous (fderiv ℝ w) := hws.continuous_fderiv (by simp)
  obtain ⟨K0, hK0⟩ := hwcont.bounded_above_of_compact_support hwc
  obtain ⟨r, hr⟩ : ∃ r, tsupport w ⊆ closedBall (0 : Euclid P) r :=
    hwc.isCompact.isBounded.subset_closedBall 0
  have hvan : ∀ z, z ∉ tsupport w → w z = 0 ∧ fderiv ℝ w z = 0 := fun z hz =>
    ⟨image_eq_zero_of_notMem_tsupport hz,
      image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_fderiv_subset ℝ h))⟩
  -- Step 3: measurability of the integrands
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ φ : Euclid P → Covector (Euclid P) n, Continuous φ →
      AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y (φ y))
        (μHE[n].restrict R.carrier) :=
    fun φ hφ => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk hφ.aestronglyMeasurable))
  have hcF : ∀ s : ℝ, Continuous (fun y => w (s • v + y)) := fun s =>
    hwcont.comp (continuous_const.add continuous_id)
  have hΦ : Continuous (fun p : ℝ × Euclid P => fderiv ℝ w (p.1 • v + p.2) v) := by
    have hsy : Continuous (fun p : ℝ × Euclid P => p.1 • v + p.2) :=
      (continuous_fst.smul continuous_const).add continuous_snd
    exact (hDw.comp hsy).clm_apply continuous_const
  have hcF' : ∀ s : ℝ, Continuous (fun y => fderiv ℝ w (s • v + y) v) := fun s =>
    hΦ.comp (continuous_const.prodMk continuous_id)
  -- Step 4: localization in `B = B̄_ρ(0)`, `ρ = r + (|t| + 1)‖v‖`; the bound `K` of `Dω(sv+y)[v]`
  set ρ : ℝ := r + (|t| + 1) * ‖v‖ with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t - 1) (b := t + 1)).prod
    (isCompact_closedBall (0 : Euclid P) ρ) |>.exists_bound_of_continuousOn hΦ.continuousOn
  have hθB : IntegrableOn (fun x => (R.mult x : ℝ)) B (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- if `|s| ≤ |t| + 1` and `s v + y ∈ spt ω` then `y ∈ B`
  have hmemB : ∀ s : ℝ, |s| ≤ |t| + 1 → ∀ y : Euclid P, s • v + y ∈ tsupport w → y ∈ B := by
    intro s hs y hy
    have h1 : ‖s • v + y‖ ≤ r := by simpa using hr hy
    have h2 := norm_sub_le (s • v + y) (s • v)
    rw [add_sub_cancel_left] at h2
    have h3 : ‖s • v‖ ≤ (|t| + 1) * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    linarith
  have habs : ∀ s ∈ Icc (t - 1) (t + 1), |s| ≤ |t| + 1 := by
    intro s hs
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, neg_abs_le t, le_abs_self t]
  -- Step 5: hypotheses of the dominated differentiation theorem
  have hs : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y (w (s • v + y))) (μHE[n].restrict R.carrier) :=
    Eventually.of_forall fun s => hmeas _ (hcF s)
  have hF'_meas : AEStronglyMeasurable (fun y => (R.mult y : ℝ) * R.orient y
      (fderiv ℝ w (t • v + y) v)) (μHE[n].restrict R.carrier) := hmeas _ (hcF' t)
  have hF_int : Integrable (fun y => (R.mult y : ℝ) * R.orient y (w (t • v + y)))
      (μHE[n].restrict R.carrier) := by
    refine ((hθB.integrable_indicator hBm).const_mul K0).mono' (hmeas _ (hcF t)) ?_
    filter_upwards [hξ] with y hy
    by_cases hty : t • v + y ∈ tsupport w
    · have hyB := hmemB t (by linarith [abs_nonneg t]) y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y (w (t • v + y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖w (t • v + y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K0) := by
            gcongr
            exact hK0 _
        _ = K0 * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hty).1, map_zero, mul_zero, norm_zero]
      have hK0n : 0 ≤ K0 := le_trans (norm_nonneg _) (hK0 0)
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_bound : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      ‖(R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)‖ ≤
        K * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [hξ] with y hy s hs
    by_cases hsy : s • v + y ∈ tsupport w
    · have hyB := hmemB s (habs s (Ioo_subset_Icc_self hs)) y hsy
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      have hnorm := hK (s, y) ⟨Ioo_subset_Icc_self hs, hyB⟩
      calc (R.mult y : ℝ) * ‖R.orient y (fderiv ℝ w (s • v + y) v)‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖fderiv ℝ w (s • v + y) v‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * K) := by gcongr
        _ = K * (R.mult y : ℝ) := by ring
    · rw [(hvan _ hsy).2, zero_apply, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]
        have hKn : 0 ≤ K := le_trans (norm_nonneg _)
          (hK (t, y) ⟨⟨by linarith, by linarith⟩, hyB⟩)
        positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  have h_diff : ∀ᵐ y ∂(μHE[n].restrict R.carrier), ∀ s ∈ Ioo (t - 1) (t + 1),
      HasDerivAt (fun s => (R.mult y : ℝ) * R.orient y (w (s • v + y)))
        ((R.mult y : ℝ) * R.orient y (fderiv ℝ w (s • v + y) v)) s := by
    refine Eventually.of_forall fun y s _ => ?_
    have h1 : HasDerivAt (fun s : ℝ => s • v + y) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).add_const y
    have h2 : HasDerivAt (fun s : ℝ => w (s • v + y)) (fderiv ℝ w (s • v + y) v) s :=
      ((hws.differentiable (by simp)).differentiableAt (x := s • v + y)).hasFDerivAt.comp_hasDerivAt
        s h1
    exact ((R.orient y).hasFDerivAt.comp_hasDerivAt s h2).const_mul (R.mult y : ℝ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    ((hθB.integrable_indicator hBm).const_mul K) h_diff
  exact key.2
/-- Continuity of translates: for a continuous compactly supported `j`-form `η`,
`t ↦ τ(M, θ, ξ)(η(t + ·))` is continuous on `ℝᴾ`.  For `‖t − t₀‖ < 1` the integrands vanish off
`B = B̄_ρ(0)`, `ρ = r + ‖t₀‖ + 1` where `spt η ⊆ B̄_r(0)`, and are dominated by `C₀ θ 1_B`,
`C₀` bounding `‖η‖` (as `‖ξ‖ ≤ 1` a.e.); `θ 1_B` is integrable since `θ` is locally
`Hʲ`-integrable, so dominated convergence gives continuity at `t₀`. -/
theorem Submission.dimred_cs_sos_mt_si_translate_action_continuous : ∀ (P j : ℕ) (R : IMRep (univ : Set (Euclid P)) j) (η : DifferentialForm (Euclid P) j), Continuous η → HasCompactSupport η → Continuous (fun t : Euclid P => R.action (fun y => η (t + y))) := by
  intro P j R η hηc hηs
  -- Step 1: `‖ξ(y)‖ ≤ 1` for `Hʲ⌞M`-a.e. `y`, as `ξ(y) α = ±α(τ)` with `τ` orthonormal
  have hξ : ∀ᵐ y ∂(μHE[j].restrict R.carrier), ‖R.orient y‖ ≤ 1 := by
    filter_upwards [R.orients] with y hy
    obtain ⟨Q, -, τ, hτ, -, hτξ⟩ := hy
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
    have hbound : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.1] using α.le_opNorm τ
    rcases hτξ with h | h
    · rw [h, one_mul]
      exact hbound
    · rw [h, norm_neg, one_mul]
      exact hbound
  -- Step 2: a bound `C₀` for `η` and a support radius `r`
  obtain ⟨C₀, hC₀⟩ := hηc.bounded_above_of_compact_support hηs
  have hC₀n : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ 0)
  obtain ⟨r, hr⟩ : ∃ r, tsupport η ⊆ closedBall (0 : Euclid P) r :=
    hηs.isCompact.isBounded.subset_closedBall 0
  -- Step 3: measurability of the integrands
  have hθm : Measurable fun y => (R.mult y : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P j × Covector (Euclid P) j => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hmeas : ∀ t : Euclid P, AEStronglyMeasurable
      (fun y => (R.mult y : ℝ) * R.orient y (η (t + y))) (μHE[j].restrict R.carrier) :=
    fun t => hθm.aestronglyMeasurable.mul
      (happly.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.prodMk
          (hηc.comp (continuous_const.add continuous_id)).aestronglyMeasurable))
  -- Step 4: for each `y`, the integrand is continuous in `t`
  have hcont : ∀ y : Euclid P,
      Continuous fun t : Euclid P => (R.mult y : ℝ) * R.orient y (η (t + y)) := fun y =>
    continuous_const.mul
      ((R.orient y).continuous.comp (hηc.comp (continuous_id.add continuous_const)))
  rw [continuous_iff_continuousAt]
  intro t₀
  -- Step 5: the window `B = B̄_ρ(0)`, `ρ = r + ‖t₀‖ + 1`: if `‖t − t₀‖ < 1` and
  -- `t + y ∈ spt η`, then `y ∈ B`
  set ρ : ℝ := r + ‖t₀‖ + 1 with hρ
  set B : Set (Euclid P) := closedBall (0 : Euclid P) ρ with hB
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hmemB : ∀ t ∈ ball t₀ 1, ∀ y : Euclid P, t + y ∈ tsupport η → y ∈ B := by
    intro t ht y hy
    have h1 : ‖t + y‖ ≤ r := by simpa using hr hy
    have h2 : ‖t - t₀‖ < 1 := by rwa [mem_ball, dist_eq_norm] at ht
    have h3 := norm_sub_norm_le t t₀
    have h4 := norm_sub_le (t + y) t
    rw [add_sub_cancel_left] at h4
    simp only [hB, mem_closedBall, dist_zero_right, hρ]
    linarith
  -- Step 6: `θ 1_B` is integrable, `θ` being locally `Hʲ`-integrable
  have hθB : IntegrableOn (fun y => (R.mult y : ℝ)) B (μHE[j].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hBm, inter_comm]
    simpa only [Real.enorm_natCast] using
      (R.locallyIntegrable_mult B (isCompact_closedBall 0 ρ) (subset_univ _)).lt_top
  -- Step 7: domination by `C₀ θ 1_B` for `t ∈ B₁(t₀)`
  have h_bound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ y ∂(μHE[j].restrict R.carrier),
      ‖(R.mult y : ℝ) * R.orient y (η (t + y))‖ ≤
        C₀ * B.indicator (fun x => (R.mult x : ℝ)) y := by
    filter_upwards [ball_mem_nhds t₀ one_pos] with t ht
    filter_upwards [hξ] with y hy
    by_cases hty : t + y ∈ tsupport η
    · have hyB := hmemB t ht y hty
      rw [indicator_of_mem hyB, norm_mul, Real.norm_natCast]
      calc (R.mult y : ℝ) * ‖R.orient y (η (t + y))‖
          ≤ (R.mult y : ℝ) * (‖R.orient y‖ * ‖η (t + y)‖) := by
            gcongr; exact (R.orient y).le_opNorm _
        _ ≤ (R.mult y : ℝ) * (1 * C₀) := by
            gcongr
            exact hC₀ _
        _ = C₀ * (R.mult y : ℝ) := by ring
    · rw [image_eq_zero_of_notMem_tsupport hty, map_zero, mul_zero, norm_zero]
      by_cases hyB : y ∈ B
      · rw [indicator_of_mem hyB]; positivity
      · rw [indicator_of_notMem hyB, mul_zero]
  -- Step 8: dominated convergence
  show ContinuousAt (fun t => ∫ y in R.carrier, (R.mult y : ℝ) * R.orient y (η (t + y)) ∂μHE[j]) t₀
  exact continuousAt_of_dominated (Eventually.of_forall hmeas) h_bound
    ((hθB.integrable_indicator hBm).const_mul C₀)
    (Eventually.of_forall fun y => (hcont y).continuousAt)

/-- Differentiation of the slices `σ ↦ Y(Φ(ω(s + σv + ·)))` (step (5c) of the cube Stokes
argument): for `Y = τ(M, θ, ξ)` in `ℝᴾ`, a continuous linear `Φ : Λ^{n'} → Λ^q` and a test
`n'`-form `ω`, the derivative at `τ` is `Y(D(Φ ∘ ω)(s + τv + ·)[v])`.  The translate
`ω_s = Φ ∘ ω ∘ (s + ·)` is a test form (`dimred_cs_sos_mt_interior_product` (b)), so
`dimred_cs_ti_translate_action_hasDerivAt` differentiates `σ ↦ τ(M, θ, ξ)(ω_s(σv + ·))`; here
`ω_s(σv + y) = Φ(ω(s + σv + y))` and `Dω_s(z) = D(Φ ∘ ω)(s + z)`, and on these test forms
`currentEval Y` is `τ(M, θ, ξ)`. -/
theorem Submission.dimred_cs_sos_mt_cs_slice_hasDerivAt : ∀ (P q n' : ℕ) (Y : GeometricCurrentOn (univ : Set (Euclid P)) q) (RY : IMRep (univ : Set (Euclid P)) q) (Φ : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) q) (ω : TestFormOn (univ : Set (Euclid P)) n') (s v : Euclid P) (τ : ℝ), RY.Represents Y → HasDerivAt (fun σ : ℝ => currentEval Y (fun y => Φ ((ω : DifferentialForm (Euclid P) n') (s + σ • v + y)))) (currentEval Y (fun y => fderiv ℝ (fun z => Φ ((ω : DifferentialForm (Euclid P) n') z)) (s + τ • v + y) v)) τ := by
  intro P q n' Y RY Φ ω s v τ hRY
  set w : DifferentialForm (Euclid P) n' := (ω : DifferentialForm (Euclid P) n') with hw_def
  have hw : IsTestForm w := ω.property.1
  have hb := (Submission.dimred_cs_sos_mt_interior_product P).2
  -- Step 1: on a test form `ψ`, `currentEval Y ψ = Y ψ = τ(M, θ, ξ)(ψ)`
  have hEval : ∀ ψ : DifferentialForm (Euclid P) q, IsTestForm ψ →
      currentEval Y ψ = RY.action ψ := by
    intro ψ hψ
    have h : IsTestForm ψ ∧ tsupport ψ ⊆ (univ : Set (Euclid P)) := ⟨hψ, subset_univ _⟩
    rw [currentEval, dite_eq_left h]
    exact hRY ⟨ψ, h⟩
  -- Step 2: `β = Φ ∘ ω` and its translate `ω_s = β(s + ·)` are test forms
  set β : DifferentialForm (Euclid P) q := fun z => Φ (w z) with hβ_def
  have hβ : IsTestForm β := by
    simpa only [zero_add] using (hb n' q Φ w 0 hw).1
  set ωs : DifferentialForm (Euclid P) q := fun y => Φ (w (s + y)) with hωs_def
  have hωs : IsTestForm ωs ∧ tsupport ωs ⊆ (univ : Set (Euclid P)) :=
    ⟨(hb n' q Φ w s hw).1, subset_univ _⟩
  -- Step 3: `σ ↦ τ(M, θ, ξ)(ω_s(σv + ·))` has derivative `τ(M, θ, ξ)(Dω_s(τv + ·)[v])` at `τ`
  have key := Submission.dimred_cs_ti_translate_action_hasDerivAt P q RY ⟨ωs, hωs⟩ v τ
  -- Step 4: the function, as `ω_s(σv + y) = Φ(ω(s + σv + y))`
  have hfun : (fun σ : ℝ => currentEval Y (fun y => Φ (w (s + σ • v + y)))) =
      fun σ : ℝ => RY.action (fun y => ωs (σ • v + y)) := by
    funext σ
    rw [hEval _ (hb n' q Φ w (s + σ • v) hw).1]
    simp only [hωs_def, add_assoc]
  -- Step 5: the derivative, as `Dω_s(z) = Dβ(s + z)`; `y ↦ Dβ(s + τv + y)[v]` is a test form
  have hderiv : currentEval Y (fun y => fderiv ℝ β (s + τ • v + y) v) =
      RY.action (fun y => fderiv ℝ ωs (τ • v + y) v) := by
    have hβv : IsTestForm (fun z => fderiv ℝ β z v) :=
      Submission.dimred_cs_sos_mt_cs_isTestForm_fderiv_apply P q β v hβ
    have htr : IsTestForm (fun y => fderiv ℝ β (s + τ • v + y) v) := by
      simpa only [ContinuousLinearMap.id_apply] using
        (hb q q (ContinuousLinearMap.id ℝ (Covector (Euclid P) q)) _ (s + τ • v) hβv).1
    have hDs : ∀ z, fderiv ℝ ωs z = fderiv ℝ β (s + z) := fun z =>
      fderiv_comp_add_left (f := β) (x := z) s
    rw [hEval _ htr]
    congr 1
    funext y
    rw [hDs, add_assoc]
  -- Step 6: rewrite the function and the derivative in step 3
  rw [hfun, hderiv]
  exact key
/-- **The closed frame box is compact** (cube Stokes step in the proof of Simon 7.3.5, which the
book leaves to the reader).  Let `g = (g₁, …, g_k)` be orthonormal in `ℝᴾ` and `r ∈ ℝ`.  The map
`ι(u) = Σ uᵢgᵢ` is continuous, takes values in `span{gᵢ}` and satisfies `⟨gᵢ, ι(u)⟩ = uᵢ`.  Every
`t ∈ span{gᵢ}` is some `ι(c)`, so the box `{t ∈ span{gᵢ} : |⟨gᵢ, t⟩| ≤ r for all i}` is the image
`ι([-r, r]ᵏ)` of a compact cube, hence compact. -/
theorem Submission.dimred_cs_sos_mt_cs_frame_box_compact : ∀ (P k : ℕ) (g : Fin k → Euclid P) (r : ℝ), Orthonormal ℝ g → IsCompact {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} := by
  intro P k g r hg
  -- Step 1: `ι(u) = Σ uᵢgᵢ` lies in `span g`; its coordinates `⟨gᵢ, ι(u)⟩ = uᵢ` come from
  -- `Orthonormal.inner_right_fintype` below
  have hmem : ∀ u : Fin k → ℝ, ∑ i, u i • g i ∈ Submodule.span ℝ (Set.range g) := fun u =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- Step 2: the box is the image of the cube `Π [-r, r]` under `ι`
  have hbox : {t : Euclid P | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} =
      (fun u : Fin k → ℝ => ∑ i, u i • g i) '' Set.pi univ fun _ => Icc (-r) r := by
    ext t
    constructor
    · rintro ⟨ht, hr⟩
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 ht
      refine ⟨c, fun i _ => ?_, rfl⟩
      have hi := hr i
      rw [hg.inner_right_fintype c i] at hi
      exact abs_le.1 hi
    · rintro ⟨u, hu, rfl⟩
      refine ⟨hmem u, fun i => ?_⟩
      rw [hg.inner_right_fintype u i]
      exact abs_le.2 (hu i (mem_univ i))
  -- Step 3: `ι` is continuous and the cube is compact, so its image is compact
  rw [hbox]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const)
/-- Translates along `G` of an action carried by `Gᗮ` vanish outside a compact set: if
`μ_R(ℝᴾ \ Gᗮ) = 0` and `η` has compact support, then `τ(M, θ, ξ)(η(t + ·)) = 0` for every
`t ∈ G \ K`, `K = p(spt η)` with `p` the orthogonal projection onto `G`.  As `θ ≥ 1` on `M`,
`Hʲ`-a.e. `y ∈ M` lies in `Gᗮ`, and there `η(t + y) ≠ 0` would give `t = p(t + y) ∈ K`. -/
theorem Submission.dimred_cs_sos_mt_si_translate_action_eq_zero_of_concentrated : ∀ (P j : ℕ) (G : Submodule ℝ (Euclid P)) (R : IMRep (univ : Set (Euclid P)) j) (η : DifferentialForm (Euclid P) j), HasCompactSupport η → R.measure (Gᗮ : Set (Euclid P))ᶜ = 0 → ∃ K : Set (Euclid P), IsCompact K ∧ ∀ t ∈ G, t ∉ K → R.action (fun y => η (t + y)) = 0 := by
  intro P j G R η hη hG
  -- Step 1: `K = p(spt η)` is compact, `p` the orthogonal projection onto `G`
  refine ⟨G.starProjection '' tsupport η, hη.isCompact.image G.starProjection.continuous, ?_⟩
  intro t ht htK
  -- Step 2: `Hʲ⌞M`-a.e. point lies in `Gᗮ`, since `θ ≠ 0` on `M`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hae : ∀ᵐ y ∂(μHE[j].restrict R.carrier), y ∈ (Gᗮ : Set (Euclid P)) := by
    have h1 : ∀ᵐ y ∂R.measure, y ∈ (Gᗮ : Set (Euclid P)) := mem_ae_iff.2 hG
    filter_upwards [(ae_withDensity_iff hθ).1 h1, ae_restrict_mem R.measurableSet_carrier]
      with y hy hyM
    exact hy (by exact_mod_cast (R.mult_pos y hyM).ne')
  -- Step 3: the integrand vanishes at every `y ∈ Gᗮ`
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hae] with y hy
  have hty : t + y ∉ tsupport η := fun h => htK ⟨t + y, h, by
    rw [map_add, Submodule.starProjection_eq_self_iff.2 ht,
      G.starProjection_apply_eq_zero_iff.2 hy, add_zero]⟩
  simp only [Pi.zero_apply, image_eq_zero_of_notMem_tsupport hty, map_zero, mul_zero]
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

/-- **Mass of the current `Ξ(ω) = ∫ ⟨ω, ζ₀⟩ dν` with a constant multivector `ζ₀`** (Simon 6.2.5;
step 5(δ) of the integer-multiplicity criterion for cycles; `|·|_E` is `covectorEuclideanNorm`).
Suppose `ν` is finite on compact sets, `|⟨α, ζ₀⟩| ≤ s |α|_E` for every `α`, and `⟨β, ζ₀⟩ = s` for
some `β` with `|β|_E ≤ 1`.  Then `s ≥ 0`, because `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`.  Put `μ = s ν` and
`ξ ≡ s⁻¹ ζ₀`.  Then `|⟨α, ξ⟩| ≤ |α|_E` and `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ`; for `s = 0` both sides vanish,
since then `ζ₀ = 0`.  `Submission.cmrc_massOn_le_of_repr` gives `M_W(Ξ) ≤ μ(W) = s ν(W)`.  For
`s > 0` the constant field `β` norms `ξ`, as `⟨β, ξ⟩ = 1`.  So
`Submission.cmrc_measure_le_massOn_of_norming` gives `μ(W') ≤ M_W(Ξ)` for every open `W' ⊂⊂ ℝᴾ`
with `W' ⊆ W`, and `Submission.cmrc_measure_le_of_compactlyContained` gives `μ(W) ≤ M_W(Ξ)`. -/
theorem Submission.cbr_ci_const_vector_massOn : ∀ (P m : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P m) (s : ℝ) (Ξ : GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ α : Covector (Euclid P) m, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → (∃ β : Covector (Euclid P) m, covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω = ∫ x, ζ₀ ((ω : DifferentialForm (Euclid P) m) x) ∂ν) → ∀ W : Set (Euclid P), IsOpen W → Ξ.massOn W = ENNReal.ofReal s * ν W := by
  rintro P m ν ζ₀ s Ξ hνK hζ₀ ⟨β, hβ1, hζβ⟩ hΞ W hW
  -- Step 1: `s ≥ 0`, since `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`
  have hs : 0 ≤ s := by
    have h := hζ₀ β
    rw [hζβ] at h
    nlinarith [neg_le_abs s, covectorEuclideanNorm_nonneg β]
  -- Step 2: `ζ₀ = s (s⁻¹ ζ₀)`; for `s = 0` this says `ζ₀ = 0`, as `|⟨α, ζ₀⟩| ≤ 0`
  have hζs : ∀ α : Covector (Euclid P) m, s * (s⁻¹ * ζ₀ α) = ζ₀ α := by
    intro α
    rcases hs.eq_or_lt with h0 | hpos
    · have h := hζ₀ α
      rw [← h0, zero_mul, abs_nonpos_iff] at h
      rw [← h0, zero_mul, h]
    · rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  -- Step 3: the constant field `ξ ≡ s⁻¹ ζ₀` is unit-bounded, `|⟨α, ξ⟩| ≤ |α|_E`
  have hξ : ∀ (_ : Euclid P) (α : Covector (Euclid P) m),
      |(s⁻¹ • ζ₀) α| ≤ covectorEuclideanNorm α := by
    intro _ α
    rw [_root_.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    rcases hs.eq_or_lt with h0 | hpos
    · rw [← h0, abs_zero, inv_zero, zero_mul]
      exact covectorEuclideanNorm_nonneg α
    · rw [abs_of_pos hpos, inv_mul_le_iff₀ hpos]
      exact hζ₀ α
  -- Step 4: `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ` for `μ = s ν`
  have hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω =
      ∫ x, (s⁻¹ • ζ₀) ((ω : DifferentialForm (Euclid P) m) x) ∂(ENNReal.ofReal s • ν) := by
    intro ω
    rw [hΞ ω, integral_smul_measure, ENNReal.toReal_ofReal hs, smul_eq_mul,
      ← integral_const_mul]
    simp only [_root_.smul_apply, smul_eq_mul, hζs]
  have hμW : (ENNReal.ofReal s • ν) W = ENNReal.ofReal s * ν W := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [← hμW]
  -- Step 5: upper bound `M_W(Ξ) ≤ μ(W)`
  refine le_antisymm (Submission.cmrc_massOn_le_of_repr P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) hξ hrep W) ?_
  -- Step 6: lower bound `μ(W) ≤ M_W(Ξ)`; trivial for `s = 0`, where `μ = 0`
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, zero_smul, Measure.coe_zero, Pi.zero_apply]
    exact zero_le
  -- for `s > 0`, `μ` is finite on compact sets and the constant covector `β` norms `ξ`:
  -- `⟨β, ξ⟩ = s⁻¹ ⟨β, ζ₀⟩ = 1`
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ → (ENNReal.ofReal s • ν) K < ∞ := by
    intro K hK _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hνK K hK)
  have hξβ : ∀ᵐ _ ∂(ENNReal.ofReal s • ν), (s⁻¹ • ζ₀) β = 1 := Eventually.of_forall fun _ => by
    rw [_root_.smul_apply, smul_eq_mul, hζβ, inv_mul_cancel₀ hpos.ne']
  -- `μ(W') ≤ M_W(Ξ)` for open `W' ⊂⊂ ℝᴾ` with `W' ⊆ W`; exhaust `W` by such `W'`
  refine Submission.cmrc_measure_le_of_compactlyContained P (ENNReal.ofReal s • ν) univ W
    (Ξ.massOn W) isOpen_univ hW (by rw [compl_univ, measure_empty]) fun W' hW' hW'U hW'W => ?_
  exact Submission.cmrc_measure_le_massOn_of_norming P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) (fun _ => β) hμK aestronglyMeasurable_const hξ hrep
    aestronglyMeasurable_const ⟨‖β‖, fun _ => le_rfl⟩ (fun _ => hβ1) hξβ W W' hW' hW'U hW'W

/-- **Hausdorff measure of the affine plane through `a` spanned by an orthonormal frame `w`**
(Simon Ch. 1, 2.9, `Hᵐ = Lᵐ` on `ℝᵐ`, transported by an isometry; step 0 of the integer
multiplicity criterion for plane cycles).  Let `S = {y | y − a ∈ span w}`.  Orthonormality gives
`‖Σᵢ cᵢ wᵢ‖ = ‖c‖`, so `J(u) = a + Σᵢ uᵢ wᵢ` is an isometry of `Euclid m` onto `S`.  Hence
`J_*(Lᵐ) = J_*(Hᵐ) = Hᵐ⌞S`, and composing with the volume-preserving `toLp : ℝᵐ → Euclid m`
gives (i).  `S` is the preimage of the closed finite-dimensional subspace `span w` under
`y ↦ y − a`.  For compact `K`, `(Hᵐ⌞S)(K) = Lᵐ(J⁻¹K) < ∞`, as `J` is a closed embedding; and
`(Hᵐ⌞S)(B_r(a)) = Lᵐ(J⁻¹B_r(a)) > 0`, as `J⁻¹B_r(a)` is open and contains `0`. -/
theorem Submission.cbr_cipi_affine_plane_measure : ∀ (P m : ℕ) (w : Fin m → Euclid P) (a : Euclid P), Orthonormal ℝ w → Measure.map (fun z : Fin m → ℝ => a + ∑ i, z i • w i) volume = (μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ IsClosed {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ (∀ K : Set (Euclid P), IsCompact K → ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) K < ∞) ∧ ∀ r : ℝ, 0 < r → 0 < ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) (ball a r) := by
  intro P m w a hw
  set S : Set (Euclid P) := {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} with hS
  -- Step 1: `J(u) = a + Σᵢ uᵢ wᵢ` is an isometry, as `‖Σᵢ cᵢ wᵢ‖ = ‖c‖` by orthonormality
  set J : Euclid m → Euclid P := fun u => a + ∑ i, u i • w i
  have hnorm : ∀ c : Euclid m, ‖∑ i, c i • w i‖ = ‖c‖ := by
    intro c
    have h1 : ‖∑ i, c i • w i‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hw.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  have hJ : Isometry J := by
    refine Isometry.of_dist_eq fun u u' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← hnorm (u - u')]
    simp [J, sub_smul, Finset.sum_sub_distrib]
  -- Step 2: `range J = S`, as `y − a ∈ span w` iff `y − a = Σᵢ cᵢ wᵢ` for some `c`
  have hrange : range J = S := by
    ext y
    rw [hS, mem_range, mem_ofPred_eq, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fun i => u i, by simp [J]⟩
    · rintro ⟨c, hc⟩
      exact ⟨WithLp.toLp 2 c, by simp [J, hc]⟩
  -- Step 3: `J_*(Lᵐ) = J_*(Hᵐ) = Hᵐ⌞S`
  have hJm : Measurable J := hJ.continuous.measurable
  have hmapJ : Measure.map J volume = (μHE[m] : Measure (Euclid P)).restrict S := by
    rw [← hrange, ← hJ.map_euclideanHausdorffMeasure,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Step 4: (i), as the parametrisation is `J ∘ toLp` and `toLp` preserves volume
  · have hcomp : (fun z : Fin m → ℝ => a + ∑ i, z i • w i) = J ∘ WithLp.toLp 2 := rfl
    rw [hcomp, ← Measure.map_map hJm (PiLp.volume_preserving_toLp (Fin m)).measurable,
      (PiLp.volume_preserving_toLp (Fin m)).map_eq, hmapJ]
  -- Step 5: (ii), `S` is the preimage of the closed subspace `span w` under `y ↦ y − a`
  · exact (Submodule.closed_of_finiteDimensional _).preimage (continuous_id.sub continuous_const)
  -- Step 6: (iii), `(Hᵐ⌞S)(K) = Lᵐ(J⁻¹K) < ∞`, `J` being a closed embedding
  · intro K hK
    rw [← hmapJ, Measure.map_apply hJm hK.isClosed.measurableSet]
    exact (hJ.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  -- Step 7: (iv), `(Hᵐ⌞S)(B_r(a)) = Lᵐ(J⁻¹B_r(a)) > 0`, an open set containing `0`
  · intro r hr
    rw [← hmapJ, Measure.map_apply hJm measurableSet_ball]
    exact (isOpen_ball.preimage hJ.continuous).measure_pos _ ⟨0, by simp [J, hr]⟩

/-- **Coordinate boxes in the span of an orthonormal frame have `Hᵏ`-measure `(2r)ᵏ`** (Simon
Ch. 1, 2.9, `Hᵏ = Lᵏ` on `ℝᵏ`; box volumes for the splitting lemma, Ch. 7, 3.5).  Let
`G = span g` and `ι(u) = Σᵢ uᵢ gᵢ` for `u : Fin k → ℝ` with the sup norm.  By
`Submission.cbr_cipi_affine_plane_measure` at `a = 0`, `ι_*(Lᵏ) = Hᵏ⌞G`.  Both boxes are Borel
subsets of the closed subspace `G`, so `Hᵏ(S) = (Hᵏ⌞G)(S) = Lᵏ(ι⁻¹S)`.  Orthonormality gives
`ι(u) ∈ G` and `⟨gᵢ, ι(u)⟩ = uᵢ`, so the closed and open boxes pull back to the sup-norm balls
`closedBall 0 r` and `ball 0 r` of `ℝᵏ`, both of volume `(2r)ᵏ`. -/
theorem Submission.dimred_cs_sos_mt_fm_box_measure : ∀ (P k : ℕ) (g : Fin k → Euclid P), Orthonormal ℝ g → ∀ r : ℝ, 0 < r → μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} = ENNReal.ofReal ((2 * r) ^ k) ∧ μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < r} = ENNReal.ofReal ((2 * r) ^ k) := by
  intro P k g hg r hr
  set G : Set (Euclid P) := (Submodule.span ℝ (Set.range g) : Set (Euclid P))
  set ι : (Fin k → ℝ) → Euclid P := fun u => ∑ i, u i • g i
  -- Step 1: `ι_*(Lᵏ) = Hᵏ⌞G`, the affine plane measure at `a = 0`
  have hmap : Measure.map ι volume = (μHE[k] : Measure (Euclid P)).restrict G := by
    simpa [ι, G] using (Submission.cbr_cipi_affine_plane_measure P k g 0 hg).1
  -- Step 2: `ι` is continuous, `G` is closed, and the coordinates `|⟨gᵢ, ·⟩|` are continuous
  have hιm : Measurable ι :=
    (continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const).measurable
  have hGc : IsClosed G := (Submodule.span ℝ (Set.range g)).closed_of_finiteDimensional
  have hcont : ∀ i, Continuous fun t : Euclid P => |inner ℝ (g i) t| := fun i =>
    (continuous_const.inner continuous_id).abs
  -- Step 3: `Hᵏ(S) = (Hᵏ⌞G)(S) = Lᵏ(ι⁻¹S)` for Borel `S ⊆ G`
  have key : ∀ S : Set (Euclid P), MeasurableSet S → S ⊆ G → μHE[k] S = volume (ι ⁻¹' S) := by
    intro S hS hSG
    rw [← Measure.map_apply hιm hS, hmap, Measure.restrict_apply hS, inter_eq_left.mpr hSG]
  -- Step 4: `ι(u) ∈ G` and `⟨gᵢ, ι(u)⟩ = uᵢ` by orthonormality
  have hmemG : ∀ u, ι u ∈ Submodule.span ℝ (Set.range g) := fun u =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  have hcoord : ∀ u i, inner ℝ (g i) (ι u) = u i := fun u i => hg.inner_right_fintype u i
  refine ⟨?_, ?_⟩
  -- Step 5: the closed box pulls back to the sup-norm `closedBall 0 r`, of volume `(2r)ᵏ`
  · rw [key _ ?_ fun t ht => ht.1]
    · have hpre : ι ⁻¹' {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} =
          closedBall 0 r := by
        ext u
        simp only [mem_preimage, mem_ofPred_eq, hcoord, mem_closedBall_zero_iff,
          pi_norm_le_iff_of_nonneg hr.le, Real.norm_eq_abs]
        exact ⟨fun h => h.2, fun h => ⟨hmemG u, h⟩⟩
      rw [hpre, Real.volume_pi_closedBall _ hr.le, Fintype.card_fin]
    · rw [ofPred_and, ofPred_forall]
      exact hGc.measurableSet.inter (MeasurableSet.iInter fun i =>
        (isClosed_le (hcont i) continuous_const).measurableSet)
  -- Step 6: the open box pulls back to the sup-norm `ball 0 r`, of volume `(2r)ᵏ`
  · rw [key _ ?_ fun t ht => ht.1]
    · have hpre : ι ⁻¹' {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < r} =
          ball 0 r := by
        ext u
        simp only [mem_preimage, mem_ofPred_eq, hcoord, mem_ball_zero_iff, pi_norm_lt_iff hr,
          Real.norm_eq_abs]
        exact ⟨fun h => h.2, fun h => ⟨hmemG u, h⟩⟩
      rw [hpre, Real.volume_pi_ball _ hr, Fintype.card_fin]
    · rw [ofPred_and, ofPred_forall]
      exact hGc.measurableSet.inter (MeasurableSet.iInter fun i =>
        (isOpen_lt (hcont i) continuous_const).measurableSet)

/-- **The frame map of an orthonormal family pushes Lebesgue measure to `Hᵏ` on its span**
(Simon Ch. 1, 2.9, `Hᵏ = Lᵏ` on `ℝᵏ`; the coordinates of the splitting lemma, Ch. 7, 3.5).  Let
`G = span g` and `ι(u) = Σᵢ uᵢ gᵢ` for `u : Fin k → ℝ`.  (i) is
`Submission.cbr_cipi_affine_plane_measure` at `a = 0`, `ι_*(Lᵏ) = Hᵏ⌞G`, and (ii) is
`Submission.dimred_cs_sos_mt_fm_box_measure`: the closed and open coordinate boxes of `G` of
half-width `r` both have `Hᵏ`-measure `(2r)ᵏ`. -/
theorem Submission.dimred_cs_sos_mt_frame_measure : ∀ (P k : ℕ) (g : Fin k → Euclid P), Orthonormal ℝ g → (volume : Measure (Fin k → ℝ)).map (fun u => ∑ i, u i • g i) = μHE[k].restrict (Submodule.span ℝ (Set.range g) : Set (Euclid P)) ∧ ∀ r : ℝ, 0 < r → μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} = ENNReal.ofReal ((2 * r) ^ k) ∧ μHE[k] {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| < r} = ENNReal.ofReal ((2 * r) ^ k) := by
  intro P k g hg
  refine ⟨?_, Submission.dimred_cs_sos_mt_fm_box_measure P k g hg⟩
  -- (i): the affine plane measure at `a = 0`, where `0 + ι(u) = ι(u)` and `y − 0 = y`
  simpa using (Submission.cbr_cipi_affine_plane_measure P k g 0 hg).1

/-- **Frame-box integrals in frame coordinates** (step (5a) of the cube Stokes formula).  For an
orthonormal frame `g₁, …, gₖ` of `ℝᴾ` with span `G`, the frame map `ι(u) = ∑ᵢ uᵢ gᵢ` is a linear
isometry from Euclidean `ℝᵏ` onto `G`, so it pushes Lebesgue measure to `Hᵏ⌞G`.  The frame box
`Q = {t ∈ G : |⟨gᵢ, t⟩| ≤ r}` is closed, lies in `G`, and has preimage `ι⁻¹(Q) = [-r, r]ᵏ`; hence
`∫_Q f dHᵏ = ∫_{[-r, r]ᵏ} f(∑ᵢ uᵢ gᵢ) du` for every `f` (no integrability is needed). -/
theorem Submission.dimred_cs_sos_mt_cs_frame_box_integral : ∀ (P k : ℕ) (g : Fin k → Euclid P) (r : ℝ) (f : Euclid P → ℝ), Orthonormal ℝ g → ∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, f t ∂μHE[k] = ∫ u in {u : Fin k → ℝ | ∀ i, |u i| ≤ r}, f (∑ i, u i • g i) := by
  intro P k g r f hg
  -- Step 1: the frame map `ι u = ∑ᵢ uᵢ gᵢ` lands in `G` and has coordinates `⟨gᵢ, ι u⟩ = uᵢ`
  let ι : (Fin k → ℝ) →ₗ[ℝ] Euclid P := Fintype.linearCombination ℝ g
  have hcoord : ∀ u i, inner ℝ (g i) (ι u) = u i := fun u i => hg.inner_right_fintype u i
  have hrange : LinearMap.range ι = Submodule.span ℝ (Set.range g) :=
    Fintype.range_linearCombination ℝ g
  -- Step 2: `ι` is injective, hence a closed and so a measurable embedding
  have hemb : MeasurableEmbedding ι := by
    refine (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr ?_)).measurableEmbedding
    intro u v huv
    funext i
    rw [← hcoord u i, ← hcoord v i, huv]
  -- Step 3: `volume.map ι = Hᵏ⌞G`: on Euclidean `ℝᵏ` the frame map is a linear isometry onto `G`
  have hmap : (volume : Measure (Fin k → ℝ)).map ι =
      μHE[k].restrict (Submodule.span ℝ (Set.range g) : Set (Euclid P)) := by
    let L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] Euclid P :=
      ι ∘ₗ (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).toLinearMap
    have hL : ∀ x y, inner ℝ (L x) (L y) = inner ℝ x y := by
      intro x y
      simp [L, ι, Fintype.linearCombination_apply, hg.inner_sum, PiLp.inner_apply, mul_comm]
    have hiso : Isometry L := (L.isometryOfInner hL).isometry
    have hrangeL : Set.range L = (Submodule.span ℝ (Set.range g) : Set (Euclid P)) := by
      rw [← hrange, LinearMap.coe_range]
      exact (WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).surjective.range_comp ι
    calc (volume : Measure (Fin k → ℝ)).map ι
        = ((volume : Measure (Fin k → ℝ)).map (WithLp.toLp 2)).map L := by
          rw [Measure.map_map hiso.continuous.measurable
            (PiLp.volume_preserving_toLp (Fin k)).measurable]
          rfl
      _ = (μHE[k] : Measure (EuclideanSpace ℝ (Fin k))).map L := by
          rw [(PiLp.volume_preserving_toLp (Fin k)).map_eq,
            EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      _ = μHE[k].restrict (Submodule.span ℝ (Set.range g) : Set (Euclid P)) := by
          rw [hiso.map_euclideanHausdorffMeasure, hrangeL]
  -- Step 4: `Hᵏ⌞Q = (volume.map ι)⌞Q`, since `Q ⊆ G` is closed (`frame_box_compact`)
  have hQ : MeasurableSet
      {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} :=
    (Submission.dimred_cs_sos_mt_cs_frame_box_compact P k g r hg).isClosed.measurableSet
  have hrestrict :
      μHE[k].restrict {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} =
        ((volume : Measure (Fin k → ℝ)).map ι).restrict
          {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} := by
    rw [hmap, Measure.restrict_restrict hQ, Set.inter_eq_left.mpr fun t ht => ht.1]
  -- Step 5: `ι⁻¹(Q) = I`
  have hpre : ι ⁻¹' {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} =
      {u : Fin k → ℝ | ∀ i, |u i| ≤ r} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hcoord]
    exact and_iff_right (hrange ▸ LinearMap.mem_range_self ι u)
  -- Step 6: change of variables along the measurable embedding `ι`
  rw [hrestrict, hemb.setIntegral_map, hpre]
  rfl
/-- **Fubini and the fundamental theorem of calculus on a coordinate box** (steps (5b) and (5d)
of the cube Stokes formula in the minimality transfer of Simon 7.3.5).  Let `a ∈ Fin (j + 1)`,
`r > 0`, `Q = [-r, r]^{j+1}` and `Q' = [-r, r]^j`.  If `φ` is continuous and, on every line in the
coordinate direction `a`, `φ` is the derivative of `ψ`, then
`∫_Q φ = ∫_{Q'} (ψ(a.insertNth r u) - ψ(a.insertNth (-r) u)) du`.  The map
`e(τ, u) = a.insertNth τ u` is measure preserving and pulls `Q` back to `[-r, r] × Q'`.  The
integrand is continuous on this compact box, so Fubini applies, and for each `u` the fundamental
theorem of calculus evaluates the inner integral over `τ ∈ [-r, r]`. -/
theorem Submission.dimred_cs_sos_mt_cs_coord_box_ftc : ∀ (j : ℕ) (a : Fin (j + 1)) (r : ℝ) (φ ψ : (Fin (j + 1) → ℝ) → ℝ), 0 < r → Continuous φ → (∀ (u : Fin j → ℝ) (τ : ℝ), HasDerivAt (fun σ : ℝ => ψ (Fin.insertNth a σ u)) (φ (Fin.insertNth a τ u)) τ) → ∫ u in {u : Fin (j + 1) → ℝ | ∀ i, |u i| ≤ r}, φ u = ∫ u in {u : Fin j → ℝ | ∀ c, |u c| ≤ r}, (ψ (Fin.insertNth a r u) - ψ (Fin.insertNth a (-r) u)) := by
  intro j a r φ ψ hr hφ hψ
  -- Step 1: `e (τ, u') = a.insertNth τ u'` is measure preserving from `volume.prod volume`
  set e : ℝ × (Fin j → ℝ) ≃ᵐ (Fin (j + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => ℝ) a).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (j + 1) => ℝ) a).symm _
  have he_apply : ∀ p : ℝ × (Fin j → ℝ), e p = Fin.insertNth a p.1 p.2 := fun _ => rfl
  -- Step 2: `e` pulls the cube back to the box `[-r, r] ×ˢ I_j`, and `I_j` is compact
  set T : Set (Fin j → ℝ) := {u | ∀ c, |u c| ≤ r}
  have hpre : e ⁻¹' {u : Fin (j + 1) → ℝ | ∀ i, |u i| ≤ r} = Icc (-r) r ×ˢ T := by
    ext ⟨τ, u⟩
    simp only [mem_preimage, mem_ofPred_eq, he_apply, Fin.forall_iff_succAbove a,
      Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, mem_prod, mem_Icc, abs_le, T]
  have hT : IsCompact T := by
    have hTpi : T = Set.pi univ fun _ => Icc (-r) r := by
      ext u
      simp only [T, mem_ofPred_eq, mem_univ_pi, mem_Icc, abs_le]
    rw [hTpi]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous fun p : (Fin j → ℝ) × ℝ => φ (Fin.insertNth a p.2 p.1) :=
    hφ.comp (Continuous.finInsertNth (A := fun _ => ℝ) a continuous_snd continuous_fst)
  -- Steps 3–4: change of variables, then Fubini on the compact box `I_j ×ˢ [-r, r]`
  rw [← he.setIntegral_preimage_emb e.measurableEmbedding φ, hpre, Measure.volume_eq_prod,
    ← setIntegral_prod_swap, setIntegral_prod]
  · -- Step 5: the fundamental theorem of calculus in `τ`, for each `u'`
    congr 1
    funext u
    simp only [Prod.swap_prod_mk, he_apply]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hψ u τ)
      ((hcont.comp (Continuous.prodMk_right u)).intervalIntegrable _ _)
  · exact hcont.continuousOn.integrableOn_compact (hT.prod isCompact_Icc)

/-- **Frame-box FTC** (step 5 of the proof of `dimred_cs_sos_mt_cube_stokes`, for abstract `A`
and `b`).  Let `g = (g₀, …, g_j)` be orthonormal, `r > 0`, and let `σ ↦ b(s + σ g_a)` have
derivative `A(s + τ g_a)` at every `τ`.  Then
`∫_{Q_r} A dH^{j+1} = ∫_{Q'_a} b(s + r g_a) dHʲ(s) − ∫_{Q'_a} b(s − r g_a) dHʲ(s)`, where `Q_r` is
the box of radius `r` of the frame `g` and `Q'_a` that of the frame `g ∘ a.succAbove`.  In the
frame coordinates `ι(u) = ∑ᵢ uᵢ gᵢ` on `Q_r` and `ι_a(u') = ∑_c u'_c g_{a.succAbove c}` on `Q'_a`
(`dimred_cs_sos_mt_cs_frame_box_integral`) this is the coordinate FTC
`dimred_cs_sos_mt_cs_coord_box_ftc` for `φ = A ∘ ι` and `ψ = b ∘ ι`, as
`ι(a.insertNth τ u') = ι_a(u') + τ g_a`; both face integrands are continuous on the compact cube
`I_j = [−r, r]ʲ`, so the integral of their difference splits. -/
theorem Submission.dimred_cs_sos_mt_cs_frame_box_ftc : ∀ (P j : ℕ) (g : Fin (j + 1) → Euclid P) (a : Fin (j + 1)) (r : ℝ) (A b : Euclid P → ℝ), Orthonormal ℝ g → 0 < r → Continuous A → Continuous b → (∀ (s : Euclid P) (τ : ℝ), HasDerivAt (fun σ : ℝ => b (s + σ • g a)) (A (s + τ • g a)) τ) → ∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r}, A t ∂μHE[j + 1] = (∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, b (s + r • g a) ∂μHE[j]) - ∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧ ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, b (s - r • g a) ∂μHE[j] := by
  intro P j g a r A b hg hr hA hb hd
  -- the face frame `g ∘ a.succAbove` is orthonormal; `ι` and `ι_a` are continuous
  have hg' : Orthonormal ℝ (g ∘ a.succAbove) := hg.comp _ Fin.succAbove_right_injective
  have hι : Continuous fun u : Fin (j + 1) → ℝ => ∑ i, u i • g i :=
    continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hιa : Continuous fun u : Fin j → ℝ => ∑ c, u c • g (a.succAbove c) :=
    continuous_finsetSum _ fun c _ => (continuous_apply c).smul continuous_const
  -- splitting off the coordinate `a`: `ι(a.insertNth τ u') = ι_a(u') + τ g_a`
  have hsplit : ∀ (u : Fin j → ℝ) (τ : ℝ),
      ∑ i, (Fin.insertNth a τ u : Fin (j + 1) → ℝ) i • g i =
        ∑ c, u c • g (a.succAbove c) + τ • g a := by
    intro u τ
    rw [Fin.sum_univ_succAbove _ a, Fin.insertNth_apply_same, add_comm]
    simp only [Fin.insertNth_apply_succAbove]
  -- frame coordinates on `Q_r` (frame `g`) and on the face `Q'_a` (frame `g ∘ a.succAbove`)
  have hbox : ∫ t in {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r},
      A t ∂μHE[j + 1] = ∫ u in {u : Fin (j + 1) → ℝ | ∀ i, |u i| ≤ r}, A (∑ i, u i • g i) :=
    Submission.dimred_cs_sos_mt_cs_frame_box_integral P (j + 1) g r A hg
  have hface : ∀ f : Euclid P → ℝ,
      ∫ s in {s | s ∈ Submodule.span ℝ (Set.range (g ∘ a.succAbove)) ∧
        ∀ c, |inner ℝ (g (a.succAbove c)) s| ≤ r}, f s ∂μHE[j] =
        ∫ u in {u : Fin j → ℝ | ∀ c, |u c| ≤ r}, f (∑ c, u c • g (a.succAbove c)) :=
    fun f => Submission.dimred_cs_sos_mt_cs_frame_box_integral P j (g ∘ a.succAbove) r f hg'
  -- the coordinate FTC for `φ = A ∘ ι` and `ψ = b ∘ ι`, its face terms rewritten by `hsplit`
  have hftc : ∫ u in {u : Fin (j + 1) → ℝ | ∀ i, |u i| ≤ r}, A (∑ i, u i • g i) =
      ∫ u in {u : Fin j → ℝ | ∀ c, |u c| ≤ r},
        (b (∑ c, u c • g (a.succAbove c) + r • g a) -
          b (∑ c, u c • g (a.succAbove c) - r • g a)) := by
    refine (Submission.dimred_cs_sos_mt_cs_coord_box_ftc j a r (fun u => A (∑ i, u i • g i))
      (fun u => b (∑ i, u i • g i)) hr (hA.comp hι) fun u τ => ?_).trans ?_
    · simp only [hsplit]
      exact hd _ τ
    · simp only [hsplit, neg_smul, ← sub_eq_add_neg]
  -- both face integrands are continuous on the compact cube `I_j`, hence integrable there
  have hK : IsCompact {u : Fin j → ℝ | ∀ c, |u c| ≤ r} := by
    have hI : {u : Fin j → ℝ | ∀ c, |u c| ≤ r} = Set.univ.pi fun _ => Set.Icc (-r) r := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
    rw [hI]
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hint₁ : IntegrableOn (fun u : Fin j → ℝ => b (∑ c, u c • g (a.succAbove c) + r • g a))
      {u : Fin j → ℝ | ∀ c, |u c| ≤ r} :=
    (hb.comp (hιa.add continuous_const)).continuousOn.integrableOn_compact hK
  have hint₂ : IntegrableOn (fun u : Fin j → ℝ => b (∑ c, u c • g (a.succAbove c) - r • g a))
      {u : Fin j → ℝ | ∀ c, |u c| ≤ r} :=
    (hb.comp (hιa.sub continuous_const)).continuousOn.integrableOn_compact hK
  rw [hbox, hftc, hface (fun s => b (s + r • g a)), hface (fun s => b (s - r • g a)),
    integral_sub hint₁ hint₂]
/-- **Bounded subsets of the span of an orthonormal frame have finite `Hᵏ`-measure** (Simon
Ch. 1, 2.9, `Hᵏ = Lᵏ` on `ℝᵏ`; integrability over `G` in the splitting lemma, Ch. 7, 3.5).
Let `G = span g`.  A bounded `E ⊆ G` lies in some `closedBall 0 ρ`; put `r = max ρ 0 + 1 > 0`.
For `t ∈ E`, Cauchy–Schwarz and `‖gᵢ‖ = 1` give `|⟨gᵢ, t⟩| ≤ ‖t‖ ≤ ρ ≤ r`, so `E` lies in the
closed coordinate box of `G` of half-width `r`.  By `Submission.dimred_cs_sos_mt_frame_measure`
(ii) that box has `Hᵏ`-measure `(2r)ᵏ < ∞`, and monotonicity finishes. -/
theorem Submission.dimred_cs_sos_mt_si_span_bounded_measure_ne_top : ∀ (P k : ℕ) (g : Fin k → Euclid P), Orthonormal ℝ g → ∀ E : Set (Euclid P), E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → Bornology.IsBounded E → μHE[k] E ≠ ∞ := by
  intro P k g hg E hEG hE
  -- Step 1: `E ⊆ closedBall 0 ρ`; put `r = max ρ 0 + 1`, so that `0 < r` and `ρ ≤ r`
  obtain ⟨ρ, hρ⟩ := hE.subset_closedBall 0
  set r : ℝ := max ρ 0 + 1
  have hr : 0 < r := by linarith [le_max_right ρ 0]
  have hρr : ρ ≤ r := by linarith [le_max_left ρ 0]
  -- Step 2: `E` lies in the closed box of half-width `r`, by Cauchy–Schwarz and `‖gᵢ‖ = 1`
  have hbox : E ⊆ {t | t ∈ Submodule.span ℝ (Set.range g) ∧ ∀ i, |inner ℝ (g i) t| ≤ r} := by
    intro t ht
    refine ⟨hEG ht, fun i => ?_⟩
    calc |inner ℝ (g i) t| ≤ ‖g i‖ * ‖t‖ := abs_real_inner_le_norm _ _
      _ = ‖t‖ := by rw [hg.1 i, one_mul]
      _ ≤ ρ := mem_closedBall_zero_iff.mp (hρ ht)
      _ ≤ r := hρr
  -- Step 3: the box has `Hᵏ`-measure `(2r)ᵏ < ∞` by frame_measure (ii); monotonicity finishes
  refine ne_top_of_le_ne_top ?_ (measure_mono hbox)
  rw [((Submission.dimred_cs_sos_mt_frame_measure P k g hg).2 r hr).1]
  exact ENNReal.ofReal_ne_top
/-- **Slices of an integer multiplicity current are continuous and integrable over a frame span**
(the product construction of the splitting lemma, Ch. 7, 3.5).  Let `G = span g`, `η = Φ ∘ ω`
and `F(t) = T(η(t + ·))`.  By `Submission.dimred_cs_sos_mt_interior_product` (b) each
`η(t + ·)` is a test form, so `F(t) = τ(M, θ, ξ)(η(t + ·))` as `R_T` represents `T`.  (i) is
`Submission.dimred_cs_sos_mt_si_translate_action_continuous`, `η` being continuous with compact
support.  (ii) A bounded `E ⊆ G` has compact closure, on which the continuous `F` is bounded,
and finite `Hᵏ`-measure by `Submission.dimred_cs_sos_mt_si_span_bounded_measure_ne_top`.
(iii) If `μ_{R_T}(ℝᴾ \ Gᗮ) = 0`, then
`Submission.dimred_cs_sos_mt_si_translate_action_eq_zero_of_concentrated` gives a compact `K`
with `F = 0` on `G \ K`; `F` is integrable on the bounded set `E ∩ K` by (ii) and vanishes on
`E \ K`. -/
theorem Submission.dimred_cs_sos_mt_slice_integrable : ∀ (P k j n' : ℕ) (g : Fin k → Euclid P) (T : GeometricCurrentOn (univ : Set (Euclid P)) j) (RT : IMRep (univ : Set (Euclid P)) j) (flat : Covector (Euclid P) n' →L[ℝ] Covector (Euclid P) j) (ω : TestFormOn (univ : Set (Euclid P)) n'), Orthonormal ℝ g → RT.Represents T → Continuous (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) ∧ (∀ E : Set (Euclid P), MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → Bornology.IsBounded E → IntegrableOn (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) E μHE[k]) ∧ (RT.measure ((Submodule.span ℝ (Set.range g))ᗮ : Set (Euclid P))ᶜ = 0 → ∀ E : Set (Euclid P), MeasurableSet E → E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → IntegrableOn (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y)))) E μHE[k]) := by
  intro P k j n' g T RT flat ω hg hRT
  -- Step 1: `η = Φ ∘ ω` is continuous with compact support
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n') := ω.2.1
  have hωs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ω : DifferentialForm (Euclid P) n') := hω.1
  set η : DifferentialForm (Euclid P) j := fun z => flat ((ω : DifferentialForm (Euclid P) n') z)
  have hηc : Continuous η := flat.continuous.comp hωs.continuous
  have hηs : HasCompactSupport η := hω.2.comp_left flat.map_zero
  -- Step 2: `F(t) = T(η(t + ·)) = τ(M, θ, ξ)(η(t + ·))`, as `η(t + ·)` is a test form
  have hF : (fun t => currentEval T (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))))
      = fun t => RT.action (fun y => η (t + y)) := by
    funext t
    have hmem : IsTestForm (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) ∧
        tsupport (fun y => flat ((ω : DifferentialForm (Euclid P) n') (t + y))) ⊆ univ :=
      ⟨((Submission.dimred_cs_sos_mt_interior_product P).2 n' j flat ω t hω).1, subset_univ _⟩
    rw [currentEval, dite_eq_left hmem]
    exact hRT _
  rw [hF]
  -- Step 3 (i): continuity of translates
  have hcont : Continuous fun t => RT.action (fun y => η (t + y)) :=
    Submission.dimred_cs_sos_mt_si_translate_action_continuous P j RT η hηc hηs
  -- Step 4 (ii): `F` is bounded on the compact closure of `E`, and `Hᵏ(E) < ∞`
  have hii : ∀ E : Set (Euclid P), MeasurableSet E →
      E ⊆ (Submodule.span ℝ (Set.range g) : Set (Euclid P)) → Bornology.IsBounded E →
      IntegrableOn (fun t => RT.action (fun y => η (t + y))) E μHE[k] := by
    intro E hEm hEG hEb
    obtain ⟨C, hC⟩ := hEb.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
    refine Measure.integrableOn_of_bounded (M := C)
      (Submission.dimred_cs_sos_mt_si_span_bounded_measure_ne_top P k g hg E hEG hEb)
      hcont.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hEm] with t ht
    exact hC t (subset_closure ht)
  refine ⟨hcont, hii, fun hconc E hEm hEG => ?_⟩
  -- Step 5 (iii): `F = 0` on `G \ K`, so integrability on `E` reduces to the bounded `E ∩ K`
  obtain ⟨K, hK, hK0⟩ := Submission.dimred_cs_sos_mt_si_translate_action_eq_zero_of_concentrated
    P j (Submodule.span ℝ (Set.range g)) RT η hηs hconc
  refine IntegrableOn.of_forall_sdiff_eq_zero
    (hii (E ∩ K) (hEm.inter hK.isClosed.measurableSet) (inter_subset_left.trans hEG)
      (hK.isBounded.subset inter_subset_right)) hEm ?_
  rintro t ⟨htE, htEK⟩
  exact hK0 t (hEG htE) fun htK => htEK ⟨htE, htK⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
