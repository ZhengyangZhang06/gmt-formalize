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

/-- **Isometric images: Borel, `Hᵏ`-measure and change of variables** (for the lattice faces
`F̆_p = Φ_p(Q₁)` in the deformation theorem, Simon Ch. 6 §5).  If `Φ : ℝᵏ → ℝᴾ` is an isometry and
`A ⊆ ℝᵏ` is Borel, then `Φ(A)` is Borel, `Hᵏ(Φ(A)) = Lᵏ(A)`, and
`∫_{Φ(A)} h dHᵏ = ∫_A h(Φ(y)) dy` for every `h : ℝᴾ → ℝ` (Bochner integrals: no integrability of
`h` is needed).  `Φ` is a closed, hence measurable, embedding; `Hᵏ` is isometry invariant and equals
`Lᵏ` on `ℝᵏ`; and `Φ_#Hᵏ = Hᵏ⌞range Φ` restricts to `Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A)`. -/
theorem Submission.dimred_mbl_dtfrpi_isometry_image_integral : ∀ (P k : ℕ) (Φ : Euclid k → Euclid P) (A : Set (Euclid k)), Isometry Φ → MeasurableSet A → MeasurableSet (Φ '' A) ∧ μHE[k] (Φ '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in Φ '' A, h x ∂μHE[k] = ∫ y in A, h (Φ y) := by
  intro P k Φ A hΦ hA
  -- step 1: `ℝᵏ` is complete, so `Φ` is a closed, hence measurable, embedding and `Φ(A)` is Borel
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  have hΦA : MeasurableSet (Φ '' A) := hemb.measurableSet_image.mpr hA
  -- step 4: `Hᵏ⌞Φ(A) = (Φ_#Hᵏ)⌞Φ(A) = Φ_#(Hᵏ⌞Φ⁻¹(Φ(A))) = Φ_#(Lᵏ⌞A)`, as `Φ_#Hᵏ = Hᵏ⌞range Φ`
  have hpush : μHE[k].restrict (Φ '' A) = (volume.restrict A).map Φ := by
    have h := hemb.restrict_map μHE[k] (Φ '' A)
    rwa [hΦ.map_euclideanHausdorffMeasure, Measure.restrict_restrict hΦA,
      Set.inter_eq_left.mpr (Set.image_subset_range Φ A), Set.preimage_image_eq A hemb.injective,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume k] at h
  refine ⟨hΦA, ?_, fun h => ?_⟩
  -- steps 2-3: `Hᵏ(Φ(A)) = Hᵏ(A) = Lᵏ(A)`, by isometry invariance and `Hᵏ = Lᵏ` on `ℝᵏ`
  · rw [hΦ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume k]
  -- step 5: change of variables along the measurable embedding `Φ`, valid for every `h`
  · rw [hpush, hemb.integral_map]
/-- **Simon Ch. 3, 1.4, flat case** (step 4(iii) of the proof of `dimred_mbl_dtfr_polyhedral_im`):
if `M` agrees with the affine plane `x + V` on `B_δ(x)`, i.e. `z ∈ M ⇔ z − x ∈ V` whenever
`|z − x| < δ`, then `V` is the approximate tangent space of `M` at `x`.  If `f ∈ C_c(ℝᴾ)` vanishes
off `B_R(0)`, then for `0 < r < δ/R` the blow-up `η_{x,r}(M)` agrees with `V` on `B_R(0)`, so
`∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ`: the integrals are eventually constant as `r ↓ 0`.  No
measurability of `M` is needed. -/
theorem Submission.dimred_mbl_dtfrpi_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (δ : ℝ), Module.finrank ℝ V = n → 0 < δ → (∀ z : Euclid P, dist z x < δ → (z ∈ M ↔ z - x ∈ V)) → HasApproximateTangentSpaceAt n M x V := by
  intro P n M x V δ hV hδ hM
  refine ⟨hV, fun f => ?_⟩
  -- `f` vanishes outside some ball `B(0, R)`
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
  obtain ⟨R, hRpos, hfz⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y ∉ ball (0 : Euclid P) R, f y = 0 := by
    refine ⟨max R₀ 0 + 1, by positivity,
      fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => hy ?_⟩
    have hy'' := hR₀ hy'
    rw [mem_closedBall, dist_zero_right] at hy''
    rw [mem_ball, dist_zero_right]
    linarith [le_max_left R₀ 0]
  -- restricting to the Borel ball `B(0, R)` does not change `∫ f`
  have hloc : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) R ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfz]
  -- for `0 < r < δ / R`, `η_{x,r}(M)` agrees with `V` on `B(0, R)`
  apply (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hRpos)] with r ⟨hr0, hrR⟩
  rw [lt_div_iff₀ hRpos] at hrR
  have hset : ball (0 : Euclid P) R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
      ball (0 : Euclid P) R ∩ (V : Set (Euclid P)) := by
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      refine ⟨hyB, V.smul_mem _ ((hM z ?_).1 hzM)⟩
      rw [mem_ball, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        norm_inv, Real.norm_of_nonneg hr0.le, inv_mul_lt_iff₀ hr0] at hyB
      rw [dist_eq_norm]
      linarith
    · rintro ⟨hyB, hyV⟩
      refine ⟨hyB, x + r • y, (hM _ ?_).2 ?_, ?_⟩
      · rw [mem_ball, dist_zero_right] at hyB
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
        calc r * ‖y‖ ≤ r * R := by gcongr
          _ < δ := hrR
      · rw [add_sub_cancel_left]
        exact V.smul_mem r hyV
      · rw [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, inv_smul_smul₀ hr0.ne']
  rw [hloc (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M), hset, ← hloc]
/-- **Coordinate `k`-planes and their unit orientations** (Simon Ch. 6, (1.2), (1.7): the simple
`k`-vector `e_{i₁} ∧ ⋯ ∧ e_{iₖ}` pairs with a `k`-covector `ω` as `ω(e_{i₁}, …, e_{iₖ})`; §5: a face
`F ∈ 𝓛ₖ` of the Deformation Theorem lies in such a coordinate plane, oriented by
`±e_{i₁} ∧ ⋯ ∧ e_{iₖ}`).  Let `ι : Fin k → Fin P` be strictly increasing, `τⱼ = e_{ι(j)}` and
`V = span{τⱼ}`.  The standard orthonormal basis composed with the injective `ι` is orthonormal,
hence linearly independent, so `dim V = k`.  Evaluation `α ↦ α(τ)` is linear with
`|α(τ)| ≤ ‖α‖ ∏ⱼ ‖τⱼ‖ = ‖α‖`, which gives the `k`-vector `e` with `e(α) = α(τ)`; the frame `τ`
witnesses that both `e` and `-e` are unit orientations of `V`. -/
theorem Submission.dimred_mbl_dtfrpi_coord_plane_orientation : ∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro P k ι hι
  -- step 1: `τ` is the orthonormal standard basis of `ℝᴾ` composed with the injective `ι`
  have hτ : Orthonormal ℝ (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P) :=
    EuclideanSpace.orthonormal_single.comp ι hι.injective
  -- step 2: an orthonormal family is linearly independent, so `dim V = #(Fin k) = k`
  have hV : Module.finrank ℝ (Submodule.span ℝ
      (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k := by
    rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- step 3: `α ↦ α(τ)` is linear (covector operations are pointwise) and bounded by `‖α‖`
  let e : MultiVector P k :=
    LinearMap.mkContinuous
      { toFun := fun α : Covector (Euclid P) k => α fun j => EuclideanSpace.single (ι j) (1 : ℝ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } 1
      fun α => by
        calc ‖α fun j => EuclideanSpace.single (ι j) (1 : ℝ)‖
            ≤ ‖α‖ * ∏ j, ‖(EuclideanSpace.single (ι j) (1 : ℝ) : Euclid P)‖ := α.le_opNorm _
          _ = 1 * ‖α‖ := by simp [hτ.1]
  refine ⟨hV, e, fun _ => rfl, ?_, ?_⟩
  -- step 4: the frame `τ` orients `V` with sign `+` for `e`
  · exact ⟨_, hτ, rfl, Or.inl fun _ => rfl⟩
  -- step 5: and with sign `-` for `-e`, as `(-e)(α) = -e(α)`
  · exact ⟨_, hτ, rfl, Or.inr fun _ => rfl⟩
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

/-- **Open lattice faces are disjoint, and their union is flat near each of its points** (Simon
Ch. 6, §5, chapter-06.txt lines 1841–1844 and 1899–1911: the interiors `F̆` of the faces
`F ∈ 𝓛ₙ`, and `P = Σ_F β_F [[F]]` with `M(P) = Σ_F |β_F|`).  Assume (FG), the type of
`dimred_mbl_dtfr_face_geometry`.  Let `S` be a finite set of pairs `p = (ι, b)` with `ι` strictly
increasing, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, `F̆_p = Φ_p((0,1)ᵏ)` and `C = ⋃_{q ∈ S} F̆_q`.
(a) A common point `Φ_p(t) = Φ_q(t')` of `F̆_p` and `F̆_q`, `p ≠ q`, is at distance `0` from itself,
while by the separation in (FG) that distance is at least `1` or some `min(tⱼ, 1 − tⱼ) > 0`.
(b) For `x = Φ_p(t)`, `t ∈ (0,1)ᵏ`, take `δ = min({1} ∪ {min(tⱼ, 1 − tⱼ)})` and let `|z − x| < δ`.
If `z = Φ_q(t') ∈ C`, separation forces `q = p`, so `z − x = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}` lies in
`V_p = span{e_{ι(j)}}`.  Conversely, if `z − x = Σⱼ cⱼ e_{ι(j)}`, then `z = Φ_p(t + c)` and, `Φ_p`
being an isometry, `|cⱼ| ≤ |c| = |z − x| < δ`, so `t + c ∈ (0,1)ᵏ` and `z ∈ F̆_p ⊆ C`. -/
theorem Submission.dimred_mbl_dtfrpi_face_union_local_plane : (∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)))) → ∀ (P k : ℕ) (S : Finset ((Fin k → Fin P) × (Fin P → ℤ))), (∀ p ∈ S, StrictMono p.1) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}) ((fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})) ∧ ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euclid P, dist z (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) < δ → (z ∈ ⋃ q ∈ S, (fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ↔ z - (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro FG P k S hS
  -- step 0: the isometry and separation facts of (FG) at `(P, k)`
  obtain ⟨-, FGpq⟩ := FG P k
  refine ⟨fun p hp q hq hpq => ?_, fun p hp t ht => ?_⟩
  -- step 1 (a): a common point `w = Φ_p(t) = Φ_q(t')` is at distance `0` from itself, against the
  -- separation of the open face `F̆_p` from the closed face of `q`
  · rw [Set.disjoint_left]
    rintro w ⟨t, ht, rfl⟩ ⟨t', ht', hw⟩
    beta_reduce at hw
    obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
    rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
    · rw [hw, dist_self] at h
      linarith
    · rw [hw, dist_self] at hj
      linarith [lt_min (ht j).1 (sub_pos.mpr (ht j).2)]
  -- step 2 (b): `δ := min ({1} ∪ {min(tⱼ, 1 − tⱼ)})`, so `0 < δ ≤ 1` and `δ ≤ min(tⱼ, 1 − tⱼ)`
  obtain ⟨δ, hδ, hδ1, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, δ ≤ min (t j) (1 - t j) := by
    let D : Finset ℝ := insert 1 (Finset.univ.image fun j => min (t j) (1 - t j))
    refine ⟨D.min' (Finset.insert_nonempty _ _), (Finset.lt_min'_iff _ _).mpr fun d hd => ?_,
      Finset.min'_le _ _ (Finset.mem_insert_self _ _), fun j => Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
      exact lt_min (ht j).1 (sub_pos.mpr (ht j).2)
  refine ⟨δ, hδ, fun z hz => ⟨fun hzC => ?_, fun hzV => ?_⟩⟩
  -- step 3 (⇒): `z = Φ_q(t')` with `q ∈ S` and `t' ∈ (0,1)ᵏ`
  · rw [Set.mem_iUnion₂] at hzC
    obtain ⟨q, hq, t', ht', hzq⟩ := hzC
    beta_reduce at hzq
    by_cases hpq : p = q
    -- for `q = p`, `z − x = Φ_p(t') − Φ_p(t) = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}`
    · subst hpq
      rw [← hzq, Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun j => t' j - t j, by simp only [sub_smul, Finset.sum_sub_distrib]; abel⟩
    -- for `q ≠ p`, separation gives `1 ≤ |z − x|` or `min(tⱼ, 1 − tⱼ) ≤ |z − x|`, both `≥ δ`
    · obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
      rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
      · rw [hzq, dist_comm] at h
        linarith
      · rw [hzq, dist_comm] at hj
        linarith [hδt j]
  -- step 4 (⇐): `z − x = Σⱼ cⱼ e_{ι(j)}`
  · rw [Submodule.mem_span_range_iff_exists_fun] at hzV
    obtain ⟨c, hc⟩ := hzV
    obtain ⟨hiso, -, -⟩ := FGpq p p (hS p hp) (hS p hp)
    -- `t' := t + c` has coordinates `tⱼ + cⱼ`, and `Φ_p(t') = x + (z − x) = z`
    have hcoord : ∀ j, (t + WithLp.toLp 2 c) j = t j + c j := fun j => by
      rw [PiLp.add_apply, PiLp.toLp_apply]
    have hz' : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, (t + WithLp.toLp 2 c) j • EuclideanSpace.single (p.1 j) (1 : ℝ) = z := by
      simp only [hcoord, add_smul, Finset.sum_add_distrib, hc]
      abel
    -- `|cⱼ| = |t'ⱼ − tⱼ| ≤ |t' − t| = |Φ_p(t') − Φ_p(t)| = |z − x| < δ`, as `Φ_p` is an isometry
    have hc' : ∀ j, |c j| < δ := fun j => by
      have h := PiLp.dist_apply_le (t + WithLp.toLp 2 c) t j
      rw [← hiso, hz', hcoord, Real.dist_eq, add_sub_cancel_left] at h
      exact h.trans_lt hz
    -- hence `0 < tⱼ + cⱼ < 1`, and `z = Φ_p(t') ∈ F̆_p ⊆ C`
    rw [Set.mem_iUnion₂]
    refine ⟨p, hp, t + WithLp.toLp 2 c, fun j => ?_, hz'⟩
    obtain ⟨hc₁, hc₂⟩ := abs_lt.mp (hc' j)
    rw [hcoord]
    constructor <;> linarith [hδt j, min_le_left (t j) (1 - t j), min_le_right (t j) (1 - t j)]
/-- **Finitely many disjoint oriented rectifiable pieces form an integer multiplicity current**
(Simon Ch. 6, Definition 3.1 and 6.3.1 (‡); used in the deformation theorem 6.5.1 for the
polyhedral currents, whose pieces are the open faces).  Let `S` be finite and, for `p ∈ S`, let
the pieces `F_p ⊆ U` be pairwise disjoint Borel sets with `Hᵏ(F_p) < ∞` and `F_p ⊆ G_p(ℝᵏ)` for
a Lipschitz `G_p`, let `m_p > 0`, and let `ξ_p` orient an approximate tangent space of
`C = ⋃_{q ∈ S} F_q` at each point of `F_p`.  Then `(C, θ, ξ)`, with `θ = Σ_q m_q 1_{F_q}` and
`ξ = ξ_p` on `F_p` (`0` off `C`), is an `IMRep`.  As `θ = m_p` and `ξ = ξ_p` on `F_p`, its action
is `Σ_p m_p ∫_{F_p} ⟨ω, ξ_p⟩ dHᵏ` and its mass measure of `ℝᴾ` is `Σ_p m_p Hᵏ(F_p)`. -/
theorem Submission.dimred_mbl_dtfrpi_finite_piece_imrep : ∀ (P k : ℕ) (I : Type) (U : Set (Euclid P)) (S : Finset I) (F : I → Set (Euclid P)) (m : I → ℕ) (ξ : I → MultiVector P k) (G : I → Euclid k → Euclid P), (∀ p ∈ S, MeasurableSet (F p)) → (∀ p ∈ S, F p ⊆ U) → (∀ p ∈ S, μHE[k] (F p) ≠ ∞) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (F p) (F q)) → (∀ p ∈ S, 0 < m p) → (∀ p ∈ S, ∃ K : NNReal, LipschitzWith K (G p)) → (∀ p ∈ S, F p ⊆ range (G p)) → (∀ p ∈ S, ∀ x ∈ F p, ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξ p) Q) → ∃ R : IMRep U k, (∀ ω : TestFormOn U k, R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, (m p : ℝ) * ∫ x in F p, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ R.measure univ = ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
  intro P k I U S F m ξ G hFm hFU hFfin hdisj hmpos hGlip hFG htan
  classical
  -- step 1: the carrier `C = ⋃_{q ∈ S} F_q` is Borel and lies in `U`
  have hCm : MeasurableSet (⋃ q ∈ S, F q) := Finset.measurableSet_biUnion S hFm
  have hCU : (⋃ q ∈ S, F q) ⊆ U := Set.iUnion₂_subset hFU
  -- step 2: a point of `F_p` lies in no other piece
  have hone : ∀ p ∈ S, ∀ q ∈ S, ∀ x ∈ F p, x ∈ F q → q = p := by
    intro p hp q hq x hxp hxq
    by_contra hqp
    exact Set.disjoint_left.mp (hdisj q hq p hp hqp) hxq hxp
  -- step 3: the multiplicity `θ = Σ_q m_q 1_{F_q}` is measurable and `θ = m_p > 0` on `F_p`
  let θ : Euclid P → ℕ := fun x => ∑ q ∈ S, (F q).indicator (fun _ => m q) x
  have hθm : Measurable θ :=
    Finset.measurable_sum S fun q hq => measurable_const.indicator (hFm q hq)
  have hθ : ∀ p ∈ S, ∀ x ∈ F p, θ x = m p := by
    intro p hp x hx
    show ∑ q ∈ S, (F q).indicator (fun _ => m q) x = m p
    rw [Finset.sum_eq_single_of_mem p hp]
    · exact Set.indicator_of_mem hx _
    · intro q hq hqp
      exact Set.indicator_of_notMem (fun hxq => hqp (hone p hp q hq x hx hxq)) _
  have hθpos : ∀ x ∈ ⋃ q ∈ S, F q, 0 < θ x := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    rw [hθ p hp x hxp]
    exact hmpos p hp
  -- step 4: the orientation, `ξ_p` on `F_p` and `0` off `C`: the right fold over a list of `S`
  -- of `(q, acc) ↦ if x ∈ F_q then ξ_q else acc`, starting from `0`
  let orient : List I → Euclid P → MultiVector P k := fun L x =>
    L.foldr (fun q acc => if x ∈ F q then ξ q else acc) 0
  have horient_sm : ∀ L : List I, (∀ q ∈ L, q ∈ S) → StronglyMeasurable (orient L) := by
    intro L
    induction L with
    | nil => exact fun _ => stronglyMeasurable_const
    | cons a L ih =>
      intro hL
      show StronglyMeasurable fun x => if x ∈ F a then ξ a else orient L x
      exact StronglyMeasurable.ite (hFm a (hL a List.mem_cons_self)) stronglyMeasurable_const
        (ih fun q hq => hL q (List.mem_cons_of_mem a hq))
  have horient : ∀ L : List I, (∀ q ∈ L, q ∈ S) → ∀ p ∈ L, ∀ x ∈ F p, orient L x = ξ p := by
    intro L
    induction L with
    | nil => intro _ p hp; simp at hp
    | cons a L ih =>
      intro hL p hpL x hx
      have hp : p ∈ S := hL p hpL
      show (if x ∈ F a then ξ a else orient L x) = ξ p
      by_cases hxa : x ∈ F a
      · rw [ite_eq_left hxa, hone p hp a (hL a List.mem_cons_self) x hx hxa]
      · rw [ite_eq_right hxa]
        refine ih (fun q hq => hL q (List.mem_cons_of_mem a hq)) p ?_ x hx
        rcases List.mem_cons.mp hpL with rfl | hpL'
        · exact absurd hx hxa
        · exact hpL'
  let ξC : Euclid P → MultiVector P k := orient S.toList
  have hSL : ∀ q ∈ S.toList, q ∈ S := fun q hq => Finset.mem_toList.mp hq
  have hξCm : StronglyMeasurable ξC := horient_sm S.toList hSL
  have hξC : ∀ p ∈ S, ∀ x ∈ F p, ξC x = ξ p := fun p hp =>
    horient S.toList hSL p (Finset.mem_toList.mpr hp)
  -- step 5: `C` is countably `k`-rectifiable, with `M₀ = ∅` and the Lipschitz maps `G_p` listed
  -- along `S.toList`, padded with constant maps
  have hrect : CountablyRectifiable k (⋃ q ∈ S, F q) := by
    refine ⟨∅, measure_empty, fun j => if h : j < S.toList.length then G (S.toList.get ⟨j, h⟩)
      else fun _ => 0, fun j => ?_, fun x hx => ?_⟩
    · by_cases h : j < S.toList.length
      · simp only [h, ↓reduceDIte]
        exact hGlip _ (hSL _ (List.get_mem _ _))
      · simp only [h, ↓reduceDIte]
        exact ⟨0, LipschitzWith.const 0⟩
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨y, rfl⟩ := hFG p hp hxp
      obtain ⟨⟨j, hj⟩, hjp⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hp)
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, y, ?_⟩)
      simp only [hj, ↓reduceDIte, hjp]
  -- step 6: `∫_C θ dHᵏ = Σ_p m_p Hᵏ(F_p) < ∞`, as the `F_p` are disjoint and `θ = m_p` on `F_p`
  have hpd : Set.PairwiseDisjoint (S : Set I) F := fun p hp q hq hpq => hdisj p hp q hq hpq
  have hθint : ∫⁻ x in ⋃ q ∈ S, F q, (θ x : ℝ≥0∞) ∂μHE[k] =
      ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
    rw [lintegral_biUnion_finset hpd hFm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hon : EqOn (fun x => (θ x : ℝ≥0∞)) (fun _ => (m p : ℝ≥0∞)) (F p) := by
      intro x hx
      simp only [hθ p hp x hx]
    rw [setLIntegral_congr_fun (hFm p hp) hon, setLIntegral_const]
  have hθfin : ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun p hp => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hFfin p hp)
  -- step 7: `∫_{C ∩ K} θ dHᵏ ≤ ∫_C θ dHᵏ < ∞`
  have hθloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ q ∈ S, F q) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := fun K _ _ =>
    ne_top_of_le_ne_top (by rw [hθint]; exact hθfin) (lintegral_mono_set Set.inter_subset_left)
  -- step 8: `ξ` orients an approximate tangent space at every point of `C`, hence `Hᵏ⌞C`-a.e.
  have horients : ∀ᵐ x ∂(μHE[k].restrict (⋃ q ∈ S, F q)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξC x) Q := by
    refine ae_restrict_of_forall_mem hCm fun x hx => ?_
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨Q, hQ, hξQ⟩ := htan p hp x hxp
    exact ⟨Q, hQ, by rw [hξC p hp x hxp]; exact hξQ⟩
  -- step 9: the triple `(C, θ, ξ)`
  let R : IMRep U k :=
    { carrier := ⋃ q ∈ S, F q
      mult := θ
      orient := ξC
      measurableSet_carrier := hCm
      carrier_subset := hCU
      rectifiable := hrect
      measurable_mult := hθm
      mult_pos := hθpos
      locallyIntegrable_mult := hθloc
      aestronglyMeasurable_orient := hξCm.aestronglyMeasurable
      orients := horients }
  refine ⟨R, fun ω => ?_, ?_⟩
  -- step 10: on `F_p` the integrand is `m_p ⟨ω, ξ_p⟩`, continuous with compact support and so
  -- integrable for the finite measure `Hᵏ⌞F_p`; the action splits over the disjoint pieces
  · have hωc : Continuous (ω : DifferentialForm (Euclid P) k) := ω.2.1.1.continuous
    have hωs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.2.1.2
    have hon : ∀ p ∈ S, EqOn (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x))
        (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x)) (F p) := by
      intro p hp x hx
      simp only [hθ p hp x hx, hξC p hp x hx]
    have hint : ∀ p ∈ S, IntegrableOn
        (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x)) (F p) μHE[k] := by
      intro p hp
      have : IsFiniteMeasure (μHE[k].restrict (F p)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hFfin p hp).lt_top⟩
      have hg : Integrable (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x))
          (μHE[k].restrict (F p)) :=
        (continuous_const.mul ((ξ p).continuous.comp hωc)).integrable_of_hasCompactSupport
          (hωs.comp_left (map_zero (ξ p))).mul_left
      exact IntegrableOn.congr_fun hg (hon p hp).symm (hFm p hp)
    show ∫ x in ⋃ q ∈ S, F q, (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] = _
    rw [integral_biUnion_finset S hFm hpd hint]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [setIntegral_congr_fun (hFm p hp) (hon p hp), integral_const_mul]
  -- step 11: `μ_T(ℝᴾ) = ∫ θ d(Hᵏ⌞C) = Σ_p m_p Hᵏ(F_p)`, by step 6
  · show ((μHE[k].restrict (⋃ q ∈ S, F q)).withDensity fun x => (θ x : ℝ≥0∞)) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hθint]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
