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

/-- **Campanato's method** (Giaquinta 1983, Ch. III, Lemma 2.1; Giaquinta–Martinazzi 2012, §5.1.1,
§5.3).  (I) Iteration lemma: for `γ = (a + b)/2` and `τ ≤ 1/2` with `2Aτ^{a−γ} ≤ 1`, `ε₀ = τ^a`,
one step gives `φ(τρ') ≤ τ^γ φ(ρ') + Bρ'^b`; by induction `φ(τʲρ) ≤ τ^{jb}(φ(ρ) + D)` with
`D = Bρ^bτ^{−b}/(1 − τ^{γ−b})`, and `τ^{j+1}ρ < r ≤ τʲρ` interpolates between the scales.
(II) Campanato's Hölder criterion: integrating `2a‖g‖ ≤ ‖g‖² + a²` gives
`‖⨍_s f − c‖² |s| ≤ ∫_s ‖f − c‖²`, so averages over `B_r(y) ⊆ B_ρ(x)` with `ρ ≤ 2r` differ by at
most `(2ᵐ/ω)^{1/2} √K ρ^α` (`|B_r| = ω rᵐ`); telescoping over `ρ 2⁻ʲ` and continuity give
`‖f(x) − ⨍_{B_ρ(x)} f‖ ≤ C₁ √K ρ^α`; comparing `B_d(y) ⊆ B_{2d}(x)`, `d = ‖x − y‖`, concludes. -/
theorem Submission.codim1_hcp_sr_campanato_lemmas : (∀ (A a b : ℝ), 0 ≤ A → 0 < b → b < a → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (φ : ℝ → ℝ) (R₀ ε B : ℝ), 0 ≤ ε → ε ≤ ε₀ → 0 ≤ B → (∀ r : ℝ, 0 < r → r ≤ R₀ → 0 ≤ φ r) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ φ ρ) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ A * ((r / ρ) ^ a + ε) * φ ρ + B * ρ ^ b) → ∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ C * ((r / ρ) ^ b * φ ρ + B * r ^ b)) ∧ (∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α ≤ 1 → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (f : Euclid m → (Euclid m →L[ℝ] Euclid k)) (x₀ : Euclid m) (R ρ₁ K : ℝ), 0 < R → 0 < ρ₁ → 0 ≤ K → ContinuousOn f (closedBall x₀ (R + ρ₁)) → (∀ x ∈ ball x₀ R, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∫ z in ball x ρ, ‖f z - ⨍ z' in ball x ρ, f z'‖ ^ 2 ≤ K * ρ ^ ((m : ℝ) + 2 * α)) → ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖x - y‖ ≤ ρ₁ / 2 → ‖f x - f y‖ ≤ C₀ * Real.sqrt K * ‖x - y‖ ^ α) := by
  refine ⟨?_, ?_⟩
  · intro A a b hA hb hba
    set γ : ℝ := (a + b) / 2 with hγ_def
    have hag : 0 < a - γ := by rw [hγ_def]; linarith
    have hgb : 0 < γ - b := by rw [hγ_def]; linarith
    set τ : ℝ := min (1 / 2) (((2 * A + 1)⁻¹) ^ (1 / (a - γ)))
    have hτpos : 0 < τ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
    have hτlt1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hτA : 2 * A * τ ^ (a - γ) ≤ 1 := by
      have h1 : τ ^ (a - γ) ≤ (2 * A + 1)⁻¹ := by
        calc τ ^ (a - γ) ≤ (((2 * A + 1)⁻¹) ^ (1 / (a - γ))) ^ (a - γ) :=
              Real.rpow_le_rpow hτpos.le (min_le_right _ _) hag.le
          _ = (2 * A + 1)⁻¹ := by
              rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hag.ne', Real.rpow_one]
      calc 2 * A * τ ^ (a - γ) ≤ 2 * A * (2 * A + 1)⁻¹ := by gcongr
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            linarith
    set t : ℝ := τ ^ b with ht_def
    set q : ℝ := τ ^ (γ - b) with hq_def
    have htpos : 0 < t := Real.rpow_pos_of_pos hτpos _
    have hqpos : 0 < q := Real.rpow_pos_of_pos hτpos _
    have hqlt1 : q < 1 := Real.rpow_lt_one hτpos.le hτlt1 hgb
    have hqt : q * t = τ ^ γ := by
      rw [hq_def, ht_def, ← Real.rpow_add hτpos, sub_add_cancel]
    have hAτ : ∀ ε : ℝ, ε ≤ τ ^ a → A * (τ ^ a + ε) ≤ q * t := by
      intro ε hε
      have hsplit : τ ^ a = τ ^ (a - γ) * τ ^ γ := by
        rw [← Real.rpow_add hτpos, sub_add_cancel]
      have hτγ : 0 < τ ^ γ := Real.rpow_pos_of_pos hτpos _
      calc A * (τ ^ a + ε) ≤ A * (τ ^ a + τ ^ a) := by gcongr
        _ = (2 * A * τ ^ (a - γ)) * τ ^ γ := by rw [hsplit]; ring
        _ ≤ 1 * τ ^ γ := by gcongr
        _ = q * t := by rw [one_mul, hqt]
    have hC : 0 < 1 / t + 1 / (t ^ 2 * (1 - q)) :=
      add_pos (one_div_pos.2 htpos) (one_div_pos.2 (mul_pos (pow_pos htpos 2) (by linarith)))
    refine ⟨τ ^ a, 1 / t + 1 / (t ^ 2 * (1 - q)), Real.rpow_pos_of_pos hτpos _, hC, ?_⟩
    intro φ R₀ ε B hε0 hεle hB hφnn hφmono hφit r ρ hr hrρ hρR
    have hρ : 0 < ρ := hr.trans_le hrρ
    -- one step of the iteration: `φ(τρ') ≤ τ^γ φ(ρ') + Bρ'^b`
    have step : ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ R₀ → φ (τ * ρ') ≤ q * t * φ ρ' + B * ρ' ^ b := by
      intro ρ' hρ' hρ'R
      have h := hφit (τ * ρ') ρ' (mul_pos hτpos hρ')
        (mul_le_of_le_one_left hρ'.le hτlt1.le) hρ'R
      rw [mul_div_cancel_right₀ τ hρ'.ne'] at h
      calc φ (τ * ρ') ≤ A * (τ ^ a + ε) * φ ρ' + B * ρ' ^ b := h
        _ ≤ q * t * φ ρ' + B * ρ' ^ b := by
            have := mul_le_mul_of_nonneg_right (hAτ ε hεle) (hφnn ρ' hρ' hρ'R)
            linarith
    set D : ℝ := B * ρ ^ b / (t * (1 - q)) with hD_def
    have h1q : 0 < 1 - q := by linarith
    have hD : q * D + B * ρ ^ b / t = D := by
      rw [hD_def]
      field_simp
      ring
    have hφρ : 0 ≤ φ ρ := hφnn ρ hρ hρR
    have hDnn : 0 ≤ D :=
      div_nonneg (mul_nonneg hB (Real.rpow_nonneg hρ.le _)) (mul_nonneg htpos.le h1q.le)
    have hτjR : ∀ j : ℕ, τ ^ j * ρ ≤ R₀ := fun j =>
      (mul_le_of_le_one_left hρ.le (pow_le_one₀ hτpos.le hτlt1.le)).trans hρR
    -- iteration: `φ(τ^j ρ) ≤ t^j (φ(ρ) + D)`
    have iter : ∀ j : ℕ, φ (τ ^ j * ρ) ≤ t ^ j * (φ ρ + D) := by
      intro j
      induction j with
      | zero => simp; linarith
      | succ j ih =>
        have hτj : 0 < τ ^ j * ρ := mul_pos (pow_pos hτpos j) hρ
        have h := step (τ ^ j * ρ) hτj (hτjR j)
        rw [show τ * (τ ^ j * ρ) = τ ^ (j + 1) * ρ by ring,
          Real.mul_rpow (pow_nonneg hτpos.le j) hρ.le, ← Real.rpow_pow_comm hτpos.le] at h
        calc φ (τ ^ (j + 1) * ρ) ≤ q * t * φ (τ ^ j * ρ) + B * (t ^ j * ρ ^ b) := h
          _ ≤ q * t * (t ^ j * (φ ρ + D)) + B * (t ^ j * ρ ^ b) := by
              gcongr
          _ = t ^ (j + 1) * (q * (φ ρ + D) + B * ρ ^ b / t) := by
              field_simp
              ring
          _ ≤ t ^ (j + 1) * (φ ρ + D) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_pos htpos _).le
              have hqφ : q * φ ρ ≤ φ ρ := mul_le_of_le_one_left hφρ hqlt1.le
              linarith
    -- interpolation between consecutive scales
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hρ)
      ((div_le_one hρ).2 hrρ) hτpos hτlt1
    have hrj : r ≤ τ ^ j * ρ := (div_le_iff₀ hρ).1 hj2
    have h2 : t ^ (j + 1) ≤ (r / ρ) ^ b := by
      rw [ht_def, Real.rpow_pow_comm hτpos.le]
      exact Real.rpow_le_rpow (pow_nonneg hτpos.le _) hj1.le hb.le
    have h3 : t ^ j ≤ (r / ρ) ^ b / t := by
      rw [le_div_iff₀ htpos, ← pow_succ]
      exact h2
    have hrρb : (r / ρ) ^ b * ρ ^ b = r ^ b := by
      rw [← Real.mul_rpow (div_pos hr hρ).le hρ.le, div_mul_cancel₀ r hρ.ne']
    have h4 : 0 ≤ (r / ρ) ^ b * φ ρ := mul_nonneg (Real.rpow_nonneg (div_pos hr hρ).le _) hφρ
    have h5 : 0 ≤ B * r ^ b := mul_nonneg hB (Real.rpow_nonneg hr.le _)
    have h6 : 0 ≤ 1 / t := (one_div_pos.2 htpos).le
    have h7 : 0 ≤ 1 / (t ^ 2 * (1 - q)) := (one_div_pos.2 (mul_pos (pow_pos htpos 2) h1q)).le
    calc φ r ≤ φ (τ ^ j * ρ) := hφmono r (τ ^ j * ρ) hr hrj (hτjR j)
      _ ≤ t ^ j * (φ ρ + D) := iter j
      _ ≤ (r / ρ) ^ b / t * (φ ρ + D) := by gcongr
      _ = 1 / t * ((r / ρ) ^ b * φ ρ) + 1 / (t ^ 2 * (1 - q)) * (B * r ^ b) := by
          rw [hD_def, ← hrρb]
          field_simp
      _ ≤ (1 / t + 1 / (t ^ 2 * (1 - q))) * ((r / ρ) ^ b * φ ρ + B * r ^ b) := by
          linarith [mul_nonneg h6 h5, mul_nonneg h7 h4]
  · intro m k α hm hα _
    have : Nontrivial (Euclid m) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    -- `|B_r(x)| = ω rᵐ`
    set ω : ℝ := (volume (ball (0 : Euclid m) 1)).toReal
    have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
      measure_ball_lt_top.ne
    have hvol : ∀ (x : Euclid m) (r : ℝ), 0 < r → volume.real (ball x r) = ω * r ^ m := by
      intro x r hr
      rw [measureReal_def, Measure.addHaar_ball volume x hr.le, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_comm]
    set q : ℝ := (1 / 2 : ℝ) ^ α with hq_def
    have hq0 : 0 < q := Real.rpow_pos_of_pos one_half_pos _
    have hq1 : q < 1 := Real.rpow_lt_one one_half_pos.le one_half_lt_one hα
    set L : ℝ := Real.sqrt (2 ^ m / ω)
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hL2 : L ^ 2 = 2 ^ m / ω := Real.sq_sqrt (by positivity)
    set C₁ : ℝ := L / (1 - q)
    have hC₁ : 0 ≤ C₁ := div_nonneg hL (by linarith)
    have hLC : L = C₁ * (1 - q) := (div_mul_cancel₀ L (by linarith : (1 - q) ≠ 0)).symm
    refine ⟨(C₁ + L) * 2 ^ α + C₁ + 1, by positivity, ?_⟩
    intro f x₀ R ρ₁ K hR hρ₁ hK hf hcamp x hx y hy hxy
    -- integrability on the balls `B_ρ(x) ⊆ closedBall x₀ (R + ρ₁)`
    have hballsub : ∀ x ∈ ball x₀ R, ∀ ρ, ρ ≤ ρ₁ → ball x ρ ⊆ closedBall x₀ (R + ρ₁) := by
      intro x hx ρ hρ z hz
      rw [mem_closedBall]
      rw [mem_ball] at hx hz
      linarith [dist_triangle z x x₀]
    have hcpt : IsCompact (closedBall x₀ (R + ρ₁)) := isCompact_closedBall _ _
    have hfint : IntegrableOn f (closedBall x₀ (R + ρ₁)) := hf.integrableOn_compact hcpt
    have hf2int : ∀ c : Euclid m →L[ℝ] Euclid k,
        IntegrableOn (fun z => ‖f z - c‖ ^ 2) (closedBall x₀ (R + ρ₁)) := fun c =>
      ((hf.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
    -- `|s| (⨍_s f - c) = ∫_s (f - c)`
    have avg_sub : ∀ (s : Set (Euclid m)) (c : Euclid m →L[ℝ] Euclid k), volume s ≠ 0 →
        volume s ≠ ⊤ → IntegrableOn f s →
        volume.real s • ((⨍ z in s, f z) - c) = ∫ z in s, (f z - c) := by
      intro s c h0 htop hfs
      have hV : volume.real s ≠ 0 := (ENNReal.toReal_pos h0 htop).ne'
      rw [integral_sub hfs (integrableOn_const htop enorm_ne_top), setIntegral_const, setAverage_eq,
        smul_sub, smul_inv_smul₀ hV]
    -- Cauchy–Schwarz in the form `‖⨍_s f - c‖² |s| ≤ ∫_s ‖f - c‖²`
    have key : ∀ (s : Set (Euclid m)) (c : Euclid m →L[ℝ] Euclid k) (M : ℝ), volume s ≠ 0 →
        volume s ≠ ⊤ → IntegrableOn f s → IntegrableOn (fun z => ‖f z - c‖ ^ 2) s →
        ∫ z in s, ‖f z - c‖ ^ 2 ≤ M → ‖(⨍ z in s, f z) - c‖ ^ 2 * volume.real s ≤ M := by
      intro s c M h0 htop hfs hf2 hM
      have hV : 0 < volume.real s := ENNReal.toReal_pos h0 htop
      set a := ‖(⨍ z in s, f z) - c‖ with ha_def
      have ha0 : 0 ≤ a := norm_nonneg _
      have h2 : a * volume.real s ≤ ∫ z in s, ‖f z - c‖ := by
        rw [ha_def, mul_comm, ← Real.norm_of_nonneg hV.le, ← norm_smul, avg_sub s c h0 htop hfs]
        exact norm_integral_le_integral_norm _
      have h3 : ∫ z in s, 2 * a * ‖f z - c‖ ≤ ∫ z in s, (‖f z - c‖ ^ 2 + a ^ 2) :=
        integral_mono ((hfs.sub (integrableOn_const htop enorm_ne_top)).norm.const_mul (2 * a))
          (hf2.add (integrableOn_const htop enorm_ne_top)) fun z =>
            show 2 * a * ‖f z - c‖ ≤ ‖f z - c‖ ^ 2 + a ^ 2 by linarith [sq_nonneg (‖f z - c‖ - a)]
      rw [integral_const_mul, integral_add hf2 (integrableOn_const htop enorm_ne_top),
        setIntegral_const, smul_eq_mul] at h3
      linarith [mul_le_mul_of_nonneg_left h2 ha0]
    -- comparison of averages over `B_r(y) ⊆ B_ρ(x)` with `ρ ≤ 2r`
    have cmp : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ → ∀ (y : Euclid m) (r : ℝ), 0 < r →
        ball y r ⊆ ball x ρ → ρ ≤ 2 * r →
        ‖(⨍ z in ball y r, f z) - ⨍ z in ball x ρ, f z‖ ≤ L * Real.sqrt K * ρ ^ α := by
      intro x hx ρ hρ hρρ₁ y r hr hsub h2r
      have hsub' : ball y r ⊆ closedBall x₀ (R + ρ₁) := hsub.trans (hballsub x hx ρ hρρ₁)
      have h := key (ball y r) (⨍ z in ball x ρ, f z) (K * ρ ^ ((m : ℝ) + 2 * α))
        (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne (hfint.mono_set hsub')
        ((hf2int _).mono_set hsub') <| by
          refine (setIntegral_mono_set ((hf2int _).mono_set (hballsub x hx ρ hρρ₁))
            (Eventually.of_forall fun z => sq_nonneg _) hsub.eventuallyLE).trans ?_
          exact hcamp x hx ρ hρ hρρ₁
      set N := ‖(⨍ z in ball y r, f z) - ⨍ z in ball x ρ, f z‖
      rw [hvol y r hr, Real.rpow_add hρ, Real.rpow_natCast, mul_comm 2 α, Real.rpow_mul hρ.le,
        Real.rpow_two] at h
      have hrm : ρ ^ m ≤ 2 ^ m * r ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hρ.le h2r m
      have hrmpos : 0 < r ^ m := pow_pos hr m
      have hρα : 0 ≤ (ρ ^ α) ^ 2 := sq_nonneg _
      have h' : N ^ 2 * ω * r ^ m ≤ 2 ^ m * K * (ρ ^ α) ^ 2 * r ^ m := by
        calc N ^ 2 * ω * r ^ m = N ^ 2 * (ω * r ^ m) := by ring
          _ ≤ K * (ρ ^ m * (ρ ^ α) ^ 2) := h
          _ ≤ K * (2 ^ m * r ^ m * (ρ ^ α) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrm hρα) hK
          _ = 2 ^ m * K * (ρ ^ α) ^ 2 * r ^ m := by ring
      have hN2 : N ^ 2 ≤ (L * Real.sqrt K * ρ ^ α) ^ 2 := by
        rw [mul_pow, mul_pow, hL2, Real.sq_sqrt hK, div_mul_eq_mul_div, div_mul_eq_mul_div,
          le_div_iff₀ hω]
        linarith [le_of_mul_le_mul_right h' hrmpos]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hN2
    -- telescoping along the dyadic radii `ρ 2⁻ʲ`
    have tele : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ → ∀ j : ℕ,
        ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ ≤
          C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) := by
      intro x hx ρ hρ hρρ₁ j
      induction j with
      | zero => simp
      | succ j ih =>
        have hr : 0 < ρ * (1 / 2) ^ j := mul_pos hρ (pow_pos one_half_pos j)
        have hrρ : ρ * (1 / 2) ^ j ≤ ρ :=
          mul_le_of_le_one_right hρ.le (pow_le_one₀ one_half_pos.le one_half_lt_one.le)
        have hstep := cmp x hx (ρ * (1 / 2) ^ j) hr (hrρ.trans hρρ₁) x (ρ * (1 / 2) ^ j / 2)
          (half_pos hr) (ball_subset_ball (half_le_self hr.le)) (mul_div_cancel₀ _ two_ne_zero).ge
        rw [Real.mul_rpow hρ.le (pow_pos one_half_pos j).le, ← Real.rpow_pow_comm one_half_pos.le,
          ← hq_def] at hstep
        rw [show ρ * (1 / 2) ^ (j + 1) = ρ * (1 / 2) ^ j / 2 by rw [pow_succ]; ring]
        calc ‖(⨍ z in ball x (ρ * (1 / 2) ^ j / 2), f z) - ⨍ z in ball x ρ, f z‖
            ≤ ‖(⨍ z in ball x (ρ * (1 / 2) ^ j / 2), f z) - ⨍ z in ball x (ρ * (1 / 2) ^ j), f z‖
              + ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ L * Real.sqrt K * (ρ ^ α * q ^ j) + C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) :=
              add_le_add hstep ih
          _ = C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ (j + 1)) := by
              rw [hLC, pow_succ]
              ring
    -- `‖f(x) - ⨍_{B_ρ(x)} f‖ ≤ C₁ √K ρ^α`, letting the dyadic radii tend to `0`
    have hlim : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ →
        ‖f x - ⨍ z in ball x ρ, f z‖ ≤ C₁ * Real.sqrt K * ρ ^ α := by
      intro x hx ρ hρ hρρ₁
      have hcont : ContinuousAt f x := hf.continuousAt <| closedBall_mem_nhds_of_mem <| by
        rw [mem_ball] at hx ⊢
        linarith
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hδ hρ) one_half_lt_one
      have hr : 0 < ρ * (1 / 2) ^ j := mul_pos hρ (pow_pos one_half_pos j)
      have hrδ : ρ * (1 / 2) ^ j < δ := by
        rw [lt_div_iff₀ hρ] at hj
        linarith
      have hrρ : ρ * (1 / 2) ^ j ≤ ρ :=
        mul_le_of_le_one_right hρ.le (pow_le_one₀ one_half_pos.le one_half_lt_one.le)
      have hV : 0 < volume.real (ball x (ρ * (1 / 2) ^ j)) :=
        ENNReal.toReal_pos (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne
      have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun z => f z - f x)
        (C := ε) (s := ball x (ρ * (1 / 2) ^ j)) measure_ball_lt_top fun z hz => by
          rw [← dist_eq_norm]
          exact (hδε ((mem_ball.1 hz).trans hrδ)).le
      rw [← avg_sub _ (f x) (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne
        (hfint.mono_set ((ball_subset_ball hrρ).trans (hballsub x hx ρ hρρ₁))), norm_smul,
        Real.norm_of_nonneg hV.le, mul_comm ε] at hI
      have h1 := le_of_mul_le_mul_left hI hV
      have h2 := tele x hx ρ hρ hρρ₁ j
      have hqj : 0 ≤ q ^ j := pow_nonneg hq0.le j
      have hC : 0 ≤ C₁ * Real.sqrt K * ρ ^ α := by positivity
      calc ‖f x - ⨍ z in ball x ρ, f z‖
          ≤ ‖f x - ⨍ z in ball x (ρ * (1 / 2) ^ j), f z‖
            + ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) := by
            rw [norm_sub_rev]
            exact add_le_add h1 h2
        _ ≤ C₁ * Real.sqrt K * ρ ^ α + ε := by linarith [mul_nonneg hC hqj]
    -- conclusion: compare `⨍_{B_d(y)} f` with `⨍_{B_{2d}(x)} f`, `d = ‖x - y‖`
    rcases (norm_nonneg (x - y)).eq_or_lt with hd | hd
    · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hd
      subst hd
      simp only [sub_self, norm_zero]
      positivity
    · generalize hd_def : ‖x - y‖ = d at hxy hd ⊢
      have hd2 : 2 * d ≤ ρ₁ := by linarith
      have hsub : ball y d ⊆ ball x (2 * d) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have : dist y x = d := by rw [dist_eq_norm, norm_sub_rev, hd_def]
        linarith [dist_triangle z y x]
      have h2d : (2 * d) ^ α = 2 ^ α * d ^ α := Real.mul_rpow zero_le_two hd.le
      have e1 := hlim x hx (2 * d) (by linarith) hd2
      have e2 := cmp x hx (2 * d) (by linarith) hd2 y d hd hsub le_rfl
      have e3 := hlim y hy d hd (by linarith)
      rw [h2d] at e1 e2
      rw [norm_sub_rev] at e2 e3
      have hKd : 0 ≤ Real.sqrt K * d ^ α := by positivity
      calc ‖f x - f y‖
          ≤ ‖f x - ⨍ z in ball x (2 * d), f z‖ + ‖(⨍ z in ball x (2 * d), f z) - f y‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖f x - ⨍ z in ball x (2 * d), f z‖ + (‖(⨍ z in ball x (2 * d), f z) -
              ⨍ z in ball y d, f z‖ + ‖(⨍ z in ball y d, f z) - f y‖) :=
            add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
        _ ≤ C₁ * Real.sqrt K * (2 ^ α * d ^ α) + (L * Real.sqrt K * (2 ^ α * d ^ α) +
              C₁ * Real.sqrt K * d ^ α) := add_le_add e1 (add_le_add e2 e3)
        _ ≤ ((C₁ + L) * 2 ^ α + C₁ + 1) * Real.sqrt K * d ^ α := by linarith [hKd]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
