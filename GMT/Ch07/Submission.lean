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

/-- **Constant density on the support forces constant multiplicity** (Simon Ch. 3, Remark 1.8(2),
chapter-03.txt lines 298–313, with `μ_T = μ_V`, Ch. 6, Remark 3.2(3)).  Let `T = τ(M, θ, ξ)` in open
`U`, `μ_T = θHⁿ⌞M`, `B = B_ρ(p)`, and suppose `Θⁿ(μ_T, y) = k` for every `y ∈ spt T ∩ B`.
* `Θⁿ(μ_T, x) = θ(x)` for `μ_T`-a.e. `x`, as in the accepted `Submission.rsd_ae_hasMassDensity_mult`.
  This node has no dependency edges, so the accepted `Submission.rsd_*` lemmas used here are
  repeated as local steps.  Approximate tangent planes and Besicovitch differentiation give
  `μ_T(B̄_r(x))/(ωₙrⁿ) → θ(x)`, and `M_W(T) ≤ μ_T(W)` bounds `M_{B_r(x)}(T)` from above.  From
  below, test `T` against `χ g(x)`, with `g = J ∘ ξ` the unit covector field dual to `ξ` and `χ` a
  smooth cut-off, at a Lebesgue point `x` of `g` (Ch. 1, 3.16–3.17, chapter-01.txt lines 907–935):
  `M_{B_r(x)}(T) ≥ μ_T(B̄_{tr}(x)) − o(rⁿ)` for every `t < 1`.
* Such an `x` lies in `spt T`.  Otherwise `T` vanishes on an open `W ∋ x`, so `M_{B_r(x)}(T) = 0`
  for small `r` and `Θⁿ(μ_T, x) = 0`, whereas `θ(x) ≥ 1` on `M ∋ x`.
* If moreover `x ∈ B`, then `Θⁿ(μ_T, x) = k` as well; limits in `[0, ∞]` are unique, so
  `θ(x) = k`.  This is (a).
* `θ ≥ 1` on `M` gives `Hⁿ⌞M ≪ μ_T` (`withDensity_absolutelyContinuous'`), so (a) also holds
  `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ B)`-a.e., where a.e. point lies in `B`.  This is (b). -/
theorem Submission.idtp_ccd_sfv_mult_ae_eq_density : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (p : Euclid P) (ρ : ℝ) (k : ℕ), IsOpen U → R.Represents T → (∀ y ∈ T.support, y ∈ ball p ρ → HasMassDensity T y k) → (∀ᵐ x ∂R.measure, x ∈ ball p ρ → R.mult x = k) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ ball p ρ)), R.mult x = k := by
  -- Accepted `Submission.rsd_tendsto_closedBall_density_of_approxTangent`, inlined: an approximate
  -- tangent plane forces `Hⁿ(M ∩ B̄_ρ(x))/(ωₙρⁿ) → 1` (Ch. 3, Remark 1.5(3)).
  have rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
    intro P n M x Q s hs hfin hT
    obtain ⟨hQ, hconv⟩ := hT
    -- Step 1: `ωₙ ∈ (0, ∞)`
    set ω := unitBallVolume n with hωdef
    have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
    have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
    set w := ω.toReal with hwdef
    have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
    -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
    have hplane0 : ∀ t : ℝ, 0 ≤ t →
        μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
      intro t ht
      let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
      let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
      have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
        ext y
        constructor
        · rintro ⟨v, hv, rfl⟩
          refine ⟨(b.repr.symm v).2, ?_⟩
          rw [mem_closedBall, dist_zero_right] at hv ⊢
          have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
          exact this.trans_le hv
        · rintro ⟨hyQ, hy⟩
          refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
          · rw [mem_closedBall, dist_zero_right] at hy ⊢
            exact (b.repr.norm_map ⟨y, hyQ⟩).trans_le hy
          · exact congrArg Subtype.val (b.repr.symm_apply_apply ⟨y, hyQ⟩)
      rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
        EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
    -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
    have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
      intro r hr A
      have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
          (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
        rw [image_image]
        rfl
      have hiso : Isometry (fun y : Euclid P => y - x) :=
        Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
      rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
        hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
      congr 1
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [abs_of_pos hr]
    have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
      intro r hr t
      have key : ∀ z : Euclid P,
          ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
        intro z
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_pos hr, dist_eq_norm]
        rw [inv_mul_le_iff₀ hr, mul_comm r t]
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        rw [mem_closedBall, dist_zero_right, key] at hy
        exact ⟨z, ⟨hz, hy⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
        refine ⟨⟨z, hz, rfl⟩, ?_⟩
        rw [mem_closedBall, dist_zero_right, key]
        exact hzb
    have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
        (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
          ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
      intro r hr t
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
    have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
    have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
        (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
      intro r hr t ht
      rw [hνball r hr t]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
    -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
    have hbump : ∀ a b : ℝ, 0 < a → a < b →
        ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
          (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
      intro a b ha hab
      have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
        continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
      have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
        intro y hy
        have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
        rw [max_eq_left ((min_le_right _ _).trans h1)]
      let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
        { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
          continuous_toFun := hcont
          hasCompactSupport' := by
            refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
            intro y hy
            rw [mem_closedBall, dist_zero_right, not_le] at hy
            exact hzero y hy.le }
      have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
      refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
      · intro y
        by_cases hy : y ∈ closedBall (0 : Euclid P) a
        · rw [indicator_of_mem hy, Pi.one_apply, hf]
          rw [mem_closedBall, dist_zero_right] at hy
          have : 1 ≤ (b - ‖y‖) / (b - a) := by
            rw [le_div_iff₀ (by linarith)]; linarith
          rw [min_eq_left this, max_eq_right zero_le_one]
        · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
      · intro y
        by_cases hy : y ∈ closedBall (0 : Euclid P) b
        · rw [indicator_of_mem hy, Pi.one_apply, hf]
          exact max_le zero_le_one (min_le_left _ _)
        · rw [indicator_of_notMem hy, hf, hzero]
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hy.le
    -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
    have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
        Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h enorm_ne_top)
    have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
        ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
        Integrable f ν := by
      intro ν f t hf hfin' h0 hle
      refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
      exact hle y
    -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
    set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
    have hareal : ∀ r : ℝ, 0 < r →
        (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
      intro r hr
      rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
    have hplane : ∀ t : ℝ, 0 ≤ t →
        (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
      intro t ht
      rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
    have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
      intro t ht
      rw [hplane t ht]
      exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
    have hplanereal : ∀ t : ℝ, 0 ≤ t →
        (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
      intro t ht
      rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    -- Step 7: `a r → ωₙ`
    have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
      rw [tendsto_order]
      constructor
      · intro c hc
        have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
          have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        obtain ⟨ε, hcε, hε⟩ :=
          ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
        obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
        -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
        have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
          rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
          exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
            (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
        filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
          Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
        -- `∫_{η(M)} f ≤ a r`
        have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
        have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
          rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
          exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
            (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
        exact hr1.trans_le hle
      · intro c hc
        have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
          have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
          simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
        obtain ⟨ε, hcε, hε⟩ :=
          ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
        obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
        -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
        have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
          rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
          exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
            (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
        filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
          Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
        -- `a r ≤ ∫_{η(M)} f`
        have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
        have h2 : (1 + ε) * r ≤ s :=
          (mul_le_mul_of_nonneg_right (show 1 + ε ≤ 2 by linarith [hε.2]) hr2.1.le).trans
            (by linarith [hr2.2])
        have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
          rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
          exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
            (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
        exact hge.trans_lt hr1
    -- Step 8: back to the `ℝ≥0∞` quotient
    have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
        μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
      intro ρ hρ hρs
      have hρn : 0 < ρ ^ n := pow_pos hρ n
      rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
        ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
      congr 1
      simp only [hadef, inv_pow]
      field_simp
    have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
      have := ENNReal.tendsto_ofReal (ha.div_const w)
      rwa [div_self hw.ne', ENNReal.ofReal_one] at this
    refine hlim.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
    exact (hconvert ρ hρ.1 hρ.2).symm
  -- Accepted `Submission.rsd_tendsto_ball_density_of_closedBall`, inlined: densities computed with
  -- closed balls are also computed with open balls (Ch. 1, 3.1–3.2).
  have rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
    intro P n ν x θ hg
    set ω := unitBallVolume n
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
      have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
        refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
        have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
          (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      rw [one_mul] at hlim
      obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
        have h1 := (tendsto_order.1 hlim).1 a ha
        have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
        obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
        exact ⟨t, ht, ht'.1, ht'.2⟩
      have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
      have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
        rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
        exact hta
      -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
      have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
            simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ρ hρ
          exact mul_pos ht0 hρ
      have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
      filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
      simp only [Function.comp] at hρ
      have hρpos' : (0 : ℝ) < ρ := hρpos
      -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
      have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
          = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
          ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
          mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
      -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
      calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
            (ENNReal.div_mul_cancel hc0 hctop).symm
        _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
            (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
        _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
        _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
            gcongr
            exact closedBall_subset_ball (by nlinarith)
    · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
      filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
      refine lt_of_le_of_lt ?_ hρ
      gcongr
      exact ball_subset_closedBall
  -- Accepted `Submission.rsd_imrep_compact_measure_ne_top`, inlined: `Hⁿ(M ∩ K) < ∞` and `μ_T(K) < ∞`
  -- for compact `K ⊆ U` (Ch. 6, Definition 3.1).
  have rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
    intro P n U R K hK hKU
    have hint := R.locallyIntegrable_mult K hK hKU
    -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
    have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
      rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
        Measure.restrict_restrict hK.measurableSet, inter_comm]
    refine ⟨?_, by rw [hmeas]; exact hint⟩
    refine ne_top_of_le_ne_top hint ?_
    -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
    calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
          rw [setLIntegral_one]
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
          refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
          intro x hx
          exact_mod_cast R.mult_pos x hx.1
  -- Accepted `Submission.rsd_mw_wlm_orient_opNorm_le_one`, inlined: a unit orientation has operator
  -- norm at most `1`.
  have rsd_mw_wlm_orient_opNorm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
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
  -- Accepted `Submission.rsd_mw_wlm_eval_eq_integral_restrict`, inlined: `T(ω) = ∫ ⟨ω, ξ⟩ d(μ_T⌞V)`
  -- when `spt ω ⊆ V`.
  have rsd_mw_wlm_eval_eq_integral_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ (V : Set (Euclid P)) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ V → T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂(R.measure.restrict V) := by
    intro P n U T R hR V ω hωV
    rw [hR ω, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · -- `μ = (Hⁿ⌞M).withDensity θ` with `θ` read as a measurable `ℝ≥0`-valued density
      have hμ : R.measure = (μHE[n].restrict R.carrier).withDensity
          (fun x => ((R.mult x : NNReal) : ℝ≥0∞)) := by
        simp [IMRep.measure]
      have hmeas : Measurable fun x => (R.mult x : NNReal) :=
        measurable_from_nat.comp R.measurable_mult
      rw [hμ, integral_withDensity_eq_integral_smul hmeas]
      simp [IMRep.action, NNReal.smul_def]
    · -- off `V`, hence off `spt ω`, the form vanishes and so does `⟨ω, ξ⟩`
      intro x hx
      have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hx (hωV h)
      simp [h0]
  -- Accepted `Submission.rsd_mw_unit_orientation_dual`, inlined: `|ξ(α)| ≤ |α|` for a unit
  -- orientation `ξ`, and a dual field `J` with `|J(ξ)| = ξ(J(ξ)) = 1` (Ch. 6, Remark 2.6); here also
  -- `‖J w‖ ≤ C‖w‖`.
  have rsd_mw_unit_orientation_dual : ∀ (P n : ℕ), ∃ J : MultiVector P n →L[ℝ] Covector (Euclid P) n, (∃ C : ℝ, 0 ≤ C ∧ ∀ w : MultiVector P n, ‖J w‖ ≤ C * ‖w‖) ∧ ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (J ξ) = 1 ∧ ξ (J ξ) = 1 := by
    intro P n
    -- `D u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`, a continuous alternating map as an
    -- alternatization; `e^I = D (e ∘ I)` and `γ = D τ`
    let D : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
      ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun k => innerSL ℝ (u k))
    have hD : ∀ u v, D u v =
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
      intro u v
      simp only [D, ContinuousMultilinearMap.alternatization_apply_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
    -- `D u v = D v u` (determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
    have hDsymm : ∀ u v, D u v = D v u := by
      intro u v
      rw [hD, hD]
      refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
      rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
        ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
    -- `D u u = 1` for orthonormal `u`: only `σ = 1` contributes
    have hD1 : ∀ u, Orthonormal ℝ u → D u u = 1 := by
      intro u hu
      rw [hD, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul]
        refine Finset.prod_eq_one fun k _ => ?_
        rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    -- step 2: `e^I(e_K) = δ_IK` for strictly increasing `I`, `K`; a nonzero term forces
    -- `K ∘ σ = I`, so `range I = range K` and `I = K`
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp e.orthonormal
    have hK : ∀ I K : Fin n → Fin P, StrictMono I → StrictMono K →
        D (fun k => e (I k)) (fun k => e (K k)) = if I = K then 1 else 0 := by
      intro I K hI hK
      split_ifs with hIK
      · subst hIK
        exact hD1 _ (e.orthonormal.comp I hI.injective)
      · rw [hD]
        refine Finset.sum_eq_zero fun σ _ => ?_
        rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
        by_contra! h
        apply hIK
        have hKσ : K ∘ σ = I := funext fun k => by
          have := h k (Finset.mem_univ k)
          rw [he] at this
          split_ifs at this with hk
          · exact hk.symm
          · exact absurd rfl this
        rw [← StrictMono.range_inj_of_wellFoundedLT hI hK, ← hKσ, EquivLike.range_comp]
    -- step 1: `α = Σ_{I ∈ S} α(e_I) e^I`; both sides are alternating, so compare them on `e ∘ f`
    -- for injective `f`, and write `f = (f ∘ σ) ∘ σ⁻¹` with `f ∘ σ` strictly increasing
    let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
    have hE : ∀ α : Covector (Euclid P) n,
        α = ∑ I ∈ S, α (fun k => e (I k)) • D (fun k => e (I k)) := by
      intro α
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      refine e.toBasis.ext_alternating fun f hf => ?_
      simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
      set σ := Tuple.sort f
      have hfσ : StrictMono (f ∘ σ) :=
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
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hfσ hfσ, ite_eq_left rfl, smul_eq_mul,
          mul_one]
      · intro I hI hIf
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hfσ,
          ite_eq_right hIf, smul_zero]
      · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfσ⟩) h
    -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
    have hnorm : ∀ β : Covector (Euclid P) n,
        covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
      intro β
      rw [covectorEuclideanNorm, Finset.sum_filter]
    -- step 3 (Cauchy–Binet): `Σ_{I ∈ S} e^I(τ)² = 1` for orthonormal `τ`; evaluate the expansion
    -- of `γ = D τ` at `τ`, using `γ(τ) = 1` and `γ(e_I) = e^I(τ)`
    have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
        ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 = 1 := by
      intro τ hτ
      have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (D τ))
      simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, hD1 τ hτ] at h
      rw [h]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [hDsymm τ, sq]
    -- step 4: `J w = Σ_{I ∈ S} w(e^I) e^I`
    have hJ : ∀ w : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
        (D fun k => e (I k))).smulRight (D fun k => e (I k))) w =
        ∑ I ∈ S, w (D fun k => e (I k)) • D fun k => e (I k) := by
      intro w
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.apply_apply]
    -- (added) `‖J w‖ = ‖Σ_I w(e^I) e^I‖ ≤ Σ_I |w(e^I)| |e^I| ≤ (Σ_I |e^I|²) ‖w‖`
    have hJb : ∀ w : MultiVector P n, ‖∑ I ∈ S, w (D fun k => e (I k)) • D fun k => e (I k)‖ ≤
        (∑ I ∈ S, ‖D fun k => e (I k)‖ ^ 2) * ‖w‖ := by
      intro w
      rw [Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
      rw [norm_smul]
      calc ‖w (D fun k => e (I k))‖ * ‖D fun k => e (I k)‖
          ≤ ‖w‖ * ‖D fun k => e (I k)‖ * ‖D fun k => e (I k)‖ :=
            mul_le_mul_of_nonneg_right (w.le_opNorm _) (norm_nonneg _)
        _ = ‖D fun k => e (I k)‖ ^ 2 * ‖w‖ := by ring
    refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (D fun k => e (I k))).smulRight
      (D fun k => e (I k)), ⟨∑ I ∈ S, ‖D fun k => e (I k)‖ ^ 2,
        Finset.sum_nonneg fun I _ => sq_nonneg _, fun w => by rw [hJ]; exact hJb w⟩, ?_⟩
    -- step 5: `ξ(α) = s α(τ)` with `s = ±1`
    rintro ξ Q ⟨τ, hτ, -, hξ⟩
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
    have hCBτ := hCB τ hτ
    refine ⟨fun α => ?_, ?_, ?_⟩
    · -- (i) `|ξ(α)| = |Σ_I α(e_I) e^I(τ)| ≤ |α| (Σ_I e^I(τ)²)^{1/2} = |α|`
      rw [hξabs, hnorm]
      apply Real.abs_le_sqrt
      have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
      simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h
      rw [h]
      calc (∑ I ∈ S, α (fun k => e (I k)) * D (fun k => e (I k)) τ) ^ 2
          ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
    · -- (ii) `J(ξ)(e_K) = ξ(e^K)`, so `|J(ξ)|² = Σ_K ξ(e^K)² = Σ_K e^K(τ)² = 1`
      rw [hnorm, hJ]
      have : ∑ K ∈ S, (∑ I ∈ S, ξ (D fun k => e (I k)) • D fun k => e (I k))
          (fun k => e (K k)) ^ 2 = 1 := by
        rw [← hCBτ]
        refine Finset.sum_congr rfl fun K hK' => ?_
        rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single K]
        · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hK').2
            (Finset.mem_filter.mp hK').2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
        · intro I hI hIK
          rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
            (Finset.mem_filter.mp hK').2, ite_eq_right hIK, smul_zero]
        · exact fun h => absurd hK' h
      rw [this, Real.sqrt_one]
    · -- (iii) `ξ(J(ξ)) = Σ_I ξ(e^I)² = Σ_I e^I(τ)² = 1`
      rw [hJ, map_sum, ← hCBτ]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_smul, smul_eq_mul, hξ2, sq]
  -- Accepted `Submission.rsd_mw_massOn_le_measure`, inlined: `M_W(T) ≤ μ_T(W)` (Ch. 6, Remark 3.2(3),
  -- `≤` half).
  have rsd_mw_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
    intro P n U T R hT W
    obtain ⟨J, -, hJ⟩ := rsd_mw_unit_orientation_dual P n
    -- `|⟨α, ξ(x)⟩| ≤ |α|` at `Hⁿ`-a.e. `x ∈ M`, where `ξ(x)` is a unit simple `n`-vector
    have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
        |R.orient x α| ≤ covectorEuclideanNorm α := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, -, hQ⟩ := hx
      exact (hJ (R.orient x) Q hQ).1
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    show ENNReal.ofReal (T ω) ≤ R.measure W
    set S := tsupport (ω : DifferentialForm (Euclid P) n)
    have hS : MeasurableSet S := (isClosed_tsupport _).measurableSet
    rw [hT ω, IMRep.action]
    calc _ ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
            ∂μHE[n]‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in R.carrier,
            ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in R.carrier, S.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
          refine lintegral_mono_ae ?_
          filter_upwards [hξ] with x hx
          by_cases hxS : x ∈ S
          · -- `|θ⟨ω, ξ⟩| ≤ θ|ω| ≤ θ` on `spt ω`
            rw [indicator_of_mem hxS, enorm_mul, Real.enorm_natCast, Real.enorm_eq_ofReal_abs]
            exact mul_le_of_le_one_right zero_le
              (ENNReal.ofReal_le_one.2 ((hx _).trans (hω1 x)))
          · -- `ω = 0` off `spt ω`
            rw [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport hxS, map_zero, mul_zero,
              enorm_zero]
      _ = R.measure S := by rw [lintegral_indicator hS, IMRep.measure, withDensity_apply _ hS]
      _ ≤ R.measure W := measure_mono hωW
  intro P n U T R p ρ k hU hRT hk
  -- notation: `ν = Hⁿ⌞M` and `θ = R.mult`, so that `μ_T = R.measure = θν ≪ ν`
  set ν : Measure (Euclid P) := μHE[n].restrict R.carrier with hν
  set θ : Euclid P → ℝ≥0∞ := fun x => (R.mult x : ℝ≥0∞) with hθdef
  have hθm : Measurable θ := measurable_from_nat.comp R.measurable_mult
  have hνK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ν K ≠ ∞ := fun K hK hKU => by
    rw [hν, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
    exact (rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ∞ :=
    fun K hK hKU => (rsd_imrep_compact_measure_ne_top P n U R K hK hKU).2
  have hμν : R.measure ≪ ν := withDensity_absolutelyContinuous ν θ
  -- `‖ξ‖ ≤ 1` `ν`-a.e., as `ξ` is `ν`-a.e. a unit orientation
  have hξ1 : ∀ᵐ y ∂ν, ‖R.orient y‖ ≤ 1 := by
    filter_upwards [R.orients] with y hy
    obtain ⟨Q, -, hQ⟩ := hy
    exact rsd_mw_wlm_orient_opNorm_le_one P n Q (R.orient y) hQ
  have hξm : AEStronglyMeasurable R.orient R.measure := R.aestronglyMeasurable_orient.mono_ac hμν
  -- `|cα| = |c||α|` for the Euclidean coefficient norm
  have hNsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  obtain ⟨J, ⟨C, hC0, hC⟩, hJ⟩ := rsd_mw_unit_orientation_dual P n
  -- `g = J ∘ ξ` is integrable on compact subsets of `U`, as `‖J w‖ ≤ C‖w‖` and `‖ξ‖ ≤ 1` a.e.
  have hgi : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (fun y => J (R.orient y)) (R.measure.restrict K) := by
    intro K hK hKU
    have : IsFiniteMeasure (R.measure.restrict K) := isFiniteMeasure_restrict.2 (hμK K hK hKU)
    refine Integrable.mono' (integrable_const C)
      (J.continuous.comp_aestronglyMeasurable hξm.restrict) ?_
    filter_upwards [ae_restrict_of_ae (hμν.ae_le hξ1)] with y hy
    exact (hC _).trans (mul_le_of_le_one_right hC0 hy)
  -- Besicovitch differentiation (Ch. 1, 3.16–3.17), localized to `U` as in the accepted
  -- `Submission.rsd_ae_tendsto_withDensity_div_closedBall`: for `μ_T`-a.e. `x ∈ U`,
  -- `μ_T(B̄_r(x))/ν(B̄_r(x)) → θ(x)`, and `x` is a Lebesgue point of `g = J ∘ ξ`, i.e.
  -- `∫_{B̄_r(x)} ‖g − g(x)‖ dμ_T/μ_T(B̄_r(x)) → 0`.  Apply `Besicovitch.ae_tendsto_rnDeriv` to
  -- `ν⌞Kⱼ` and Lebesgue differentiation to `μ_T⌞Kⱼ`, for a compact exhaustion `Kⱼ` of `U`.
  have hdiff : ∀ᵐ x ∂R.measure, x ∈ U →
      Tendsto (fun r : ℝ => ν.withDensity θ (closedBall x r) / ν (closedBall x r)) (𝓝[>] 0)
        (𝓝 (θ x)) ∧
      Tendsto (fun r : ℝ =>
        (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure) /
          R.measure (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    set K : ℕ → Set (Euclid P) := fun j =>
      closedBall 0 ((j : ℝ) + 1) ∩ {y | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} with hKdef
    have hKclosed' : ∀ j : ℕ, IsClosed {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} := by
      intro j
      have : {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} =
          ⋂ z ∈ Uᶜ, {y | 1 / ((j : ℝ) + 1) ≤ dist y z} := by
        ext y; simp
      rw [this]
      exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
    have hKclosed : ∀ j, IsClosed (K j) := fun j => isClosed_closedBall.inter (hKclosed' j)
    have hKcpt : ∀ j, IsCompact (K j) := fun j =>
      (isCompact_closedBall (0 : Euclid P) _).inter_right (hKclosed' j)
    have hKU : ∀ j, K j ⊆ U := by
      intro j y hy
      by_contra hyU
      have h := hy.2 y hyU
      rw [dist_self] at h
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
    have hcover : ∀ x ∈ U, ∃ j : ℕ, ball x (1 / ((j : ℝ) + 1)) ⊆ K j := by
      intro x hx
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
      obtain ⟨j, hj⟩ := exists_nat_gt (max (2 / δ) ‖x‖)
      have hj1 : 2 / δ < (j : ℝ) + 1 := by
        have := le_max_left (2 / δ) ‖x‖; linarith
      have hj2 : ‖x‖ < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
      have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hsmall : 2 / ((j : ℝ) + 1) < δ := by
        rw [div_lt_iff₀ hjpos]
        rw [div_lt_iff₀ hδ] at hj1
        linarith
      refine ⟨j, fun y hy => ⟨?_, ?_⟩⟩
      · rw [mem_closedBall, dist_zero_right]
        have h1 : ‖y‖ ≤ ‖x‖ + dist y x := by
          have := norm_le_norm_add_norm_sub' y x
          rw [dist_eq_norm]; linarith [norm_sub_rev y x]
        have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
        have h3 : 1 / ((j : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hjpos]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        linarith
      · intro z hz
        have hxz : δ ≤ dist x z := by
          by_contra h
          exact hz (hball (by rw [mem_ball, dist_comm]; linarith))
        have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
        have htri := dist_triangle x y z
        have h4 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
        rw [dist_comm] at h2
        linarith
    -- Besicovitch differentiation and Lebesgue points on each `K j`, where `ν⌞K j` and
    -- `μ_T⌞K j` are finite and `g` is `μ_T⌞K j`-integrable
    have hj : ∀ j : ℕ, ∀ᵐ x ∂R.measure, x ∈ K j →
        Tendsto (fun r : ℝ => ((ν.withDensity θ).restrict (K j)) (closedBall x r) /
          (ν.restrict (K j)) (closedBall x r)) (𝓝[>] 0) (𝓝 (θ x)) ∧
        Tendsto (fun r : ℝ => (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ
          ∂(R.measure.restrict (K j))) / (R.measure.restrict (K j)) (closedBall x r)) (𝓝[>] 0)
          (𝓝 0) := by
      intro j
      have hKm : MeasurableSet (K j) := (hKclosed j).measurableSet
      have : IsFiniteMeasure (ν.restrict (K j)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hνK _ (hKcpt j) (hKU j)).lt_top⟩
      have : IsFiniteMeasure ((ν.withDensity θ).restrict (K j)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hμK _ (hKcpt j) (hKU j)).lt_top⟩
      have : IsFiniteMeasure (R.measure.restrict (K j)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hμK _ (hKcpt j) (hKU j)).lt_top⟩
      have h1 := Besicovitch.ae_tendsto_rnDeriv ((ν.withDensity θ).restrict (K j)) (ν.restrict (K j))
      have h2 := Measure.rnDeriv_withDensity (ν.restrict (K j)) hθm
      rw [← restrict_withDensity hKm] at h2
      have h3 : ∀ᵐ x ∂(ν.restrict (K j)), Tendsto (fun r : ℝ =>
          ((ν.withDensity θ).restrict (K j)) (closedBall x r) / (ν.restrict (K j)) (closedBall x r))
          (𝓝[>] 0) (𝓝 (θ x)) := by
        filter_upwards [h1, h2] with x hx1 hx2
        rwa [hx2] at hx1
      have h4 : ∀ᵐ x ∂(R.measure.restrict (K j)), Tendsto (fun r : ℝ =>
          (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂(R.measure.restrict (K j))) /
            (R.measure.restrict (K j)) (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
        filter_upwards [(Besicovitch.vitaliFamily (R.measure.restrict (K j))).ae_tendsto_lintegral_enorm_sub_div_of_integrable
          (hgi _ (hKcpt j) (hKU j))] with x hx
        exact hx.comp (Besicovitch.tendsto_filterAt _ x)
      exact (ae_restrict_iff' hKm).1 (Filter.Eventually.and ((hμν.restrict (K j)).ae_le h3) h4)
    filter_upwards [ae_all_iff.2 hj] with x hx hxU
    obtain ⟨j, hjK⟩ := hcover x hxU
    have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    have hxK : x ∈ K j := hjK (mem_ball_self hr)
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), closedBall x r ⊆ K j := by
      filter_upwards [Ioo_mem_nhdsGT hr] with r hr'
      exact (closedBall_subset_ball hr'.2).trans hjK
    refine ⟨((hx j hxK).1).congr' ?_, ((hx j hxK).2).congr' ?_⟩
    · filter_upwards [hev] with r hsub
      rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall,
        inter_eq_left.2 hsub]
    · filter_upwards [hev] with r hsub
      rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hsub,
        Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hsub]
  have hM : ∀ᵐ x ∂R.measure, x ∈ R.carrier := hμν.ae_le (ae_restrict_mem R.measurableSet_carrier)
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  -- Step 1: `Θⁿ(μ_T, x) = θ(x)` for `μ_T`-a.e. `x` (the accepted
  -- `Submission.rsd_ae_hasMassDensity_mult`).  `M_{B_r(x)}(T) ≤ μ_T(B_r(x))` gives the upper bound.
  -- For the lower bound, test `T` against `ω = χ g(x)`, where `g = J ∘ ξ` (`|g| = 1`, `⟨g, ξ⟩ = 1`
  -- a.e.) and `χ` is a smooth cut-off, `χ = 1` on `B̄_{tr}(x)`, `spt χ ⊆ B_r(x)`; at a Lebesgue
  -- point `x` of `g` this gives `M_{B_r(x)}(T) ≥ μ_T(B̄_{tr}(x)) − o(rⁿ)`.
  have hF1 : ∀ᵐ x ∂R.measure, HasMassDensity T x (R.mult x) := by
    filter_upwards [hM, hμν.ae_le R.orients, hdiff] with x hxM hQ hxd
    obtain ⟨Q, hxQ, hξQ⟩ := hQ
    have hxU : x ∈ U := R.carrier_subset hxM
    obtain ⟨s, hs, hsU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
    have hsub : ∀ r : ℝ, r ≤ s → closedBall x r ⊆ U := fun r hr =>
      (closedBall_subset_closedBall hr).trans hsU
    -- `μ_T(B̄_r(x))/(ωₙrⁿ) = [μ_T(B̄_r(x))/ν(B̄_r(x))] · [ν(B̄_r(x))/(ωₙrⁿ)] → θ(x) · 1`
    have hden := rsd_tendsto_closedBall_density_of_approxTangent P n R.carrier x Q s hs
      (rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x s) hsU).1 hxQ
    have hclosed : Tendsto (fun r : ℝ => R.measure (closedBall x r) /
        (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 (θ x)) := by
      have hprod := ENNReal.Tendsto.mul (hxd hxU).1 (Or.inr ENNReal.one_ne_top) hden
        (Or.inl one_ne_zero)
      rw [mul_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hs, hden.eventually_ne one_ne_zero] with r hr hne
      have hfin : μHE[n] (R.carrier ∩ closedBall x r) ≠ ∞ :=
        (rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x r)
          (hsub r hr.2.le)).1
      have hpos : μHE[n] (R.carrier ∩ closedBall x r) ≠ 0 := fun h0 =>
        hne (by rw [h0, ENNReal.zero_div])
      have hνr : ν (closedBall x r) = μHE[n] (R.carrier ∩ closedBall x r) := by
        rw [hν, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
      rw [hνr]
      exact ENNReal.div_mul_div_cancel hpos hfin
    have hopen := rsd_tendsto_ball_density_of_closedBall P n R.measure x (θ x) hclosed
    have hβN : covectorEuclideanNorm (J (R.orient x)) = 1 := (hJ _ Q hξQ).2.1
    have hθx : θ x ≠ ∞ := ENNReal.natCast_ne_top _
    have hθ0 : θ x ≠ 0 := Nat.cast_ne_zero.2 (R.mult_pos x hxM).ne'
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rw [ENNReal.ofReal_natCast, tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · -- lower bound: choose `t ∈ (0, 1)` with `a < tⁿθ(x)`
      have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ x) (𝓝[<] 1) (𝓝 (1 * θ x)) := by
        refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
        have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
          (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      rw [one_mul] at hlim
      obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ x ∧ 0 < t ∧ t < 1 := by
        have h1 := (tendsto_order.1 hlim).1 a ha
        have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
        obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
        exact ⟨t, ht, ht'.1, ht'.2⟩
      -- (i) for `0 < r ≤ s`: `μ_T(B̄_{tr}(x)) − ∫_{B̄_r(x)} ‖g − g(x)‖ dμ_T ≤ M_{B_r(x)}(T)`
      have hlow : ∀ r : ℝ, 0 < r → r ≤ s → R.measure (closedBall x (t * r)) -
          ∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure ≤
            T.massOn (ball x r) := by
        intro r hr hrs
        have htr : t * r < (1 + t) / 2 * r := mul_lt_mul_of_pos_right (by linarith) hr
        have htr' : (1 + t) / 2 * r < r := by
          have h := mul_lt_mul_of_pos_right (show (1 + t) / 2 < 1 by linarith) hr
          rwa [one_mul] at h
        have htr1 : closedBall x (t * r) ⊆ closedBall x r :=
          closedBall_subset_closedBall (mul_le_of_le_one_left hr.le ht1.le)
        -- the cut-off `χ` and the test form `ω = χ g(x)`, admissible for `M_{B_r(x)}(T)`
        let χ : ContDiffBump x := ⟨t * r, (1 + t) / 2 * r, mul_pos ht0 hr, htr⟩
        let ω : DifferentialForm (Euclid P) n := fun y => χ y • J (R.orient x)
        have hωt : IsTestForm ω := ⟨χ.contDiff.smul contDiff_const, χ.hasCompactSupport.smul_right⟩
        have hωs : tsupport ω ⊆ ball x r :=
          (tsupport_smul_subset_left (fun y => χ y) (fun _ => J (R.orient x))).trans
            (χ.tsupport_eq.trans_subset (closedBall_subset_ball htr'))
        let ω' : TestFormOn U n := ⟨ω, hωt, hωs.trans (ball_subset_closedBall.trans (hsub r hrs))⟩
        have hω1 : ∀ y, covectorEuclideanNorm (ω y) ≤ 1 := fun y => by
          show covectorEuclideanNorm (χ y • J (R.orient x)) ≤ 1
          rw [hNsmul, hβN, mul_one, abs_of_nonneg (χ.nonneg' y)]
          exact χ.le_one
        have hωy : ∀ y, R.orient y (ω y) = χ y * R.orient y (J (R.orient x)) := fun y =>
          (R.orient y).map_smul (χ y) (J (R.orient x))
        refine le_trans ?_ (T.le_massOn (show ω' ∈ massAdmissibleOn U n (ball x r) from ⟨hωs, hω1⟩))
        -- `T(ω) = ∫ ⟨ω, ξ⟩ d(μ_T⌞B̄_r(x))`, with `μ_T⌞B̄_r(x)` finite
        have hTω : T ω' = ∫ y, R.orient y (ω y) ∂(R.measure.restrict (closedBall x r)) :=
          rsd_mw_wlm_eval_eq_integral_restrict P n U T R hRT (closedBall x r) ω'
            (hωs.trans ball_subset_closedBall)
        have hfin : R.measure (closedBall x r) ≠ ∞ := hμK _ (isCompact_closedBall x r) (hsub r hrs)
        have : IsFiniteMeasure (R.measure.restrict (closedBall x r)) := isFiniteMeasure_restrict.2 hfin
        have hξr : AEStronglyMeasurable R.orient (R.measure.restrict (closedBall x r)) := hξm.restrict
        have hgr : Integrable (fun y => J (R.orient y)) (R.measure.restrict (closedBall x r)) :=
          hgi _ (isCompact_closedBall x r) (hsub r hrs)
        -- a.e. on `B̄_r(x)`: `‖ξ(y)‖ ≤ 1` and `⟨g(y), ξ(y)⟩ = 1`
        have hG : ∀ᵐ y ∂(R.measure.restrict (closedBall x r)),
            ‖R.orient y‖ ≤ 1 ∧ R.orient y (J (R.orient y)) = 1 := by
          filter_upwards [ae_restrict_of_ae (hμν.ae_le R.orients)] with y hy
          obtain ⟨Q', -, hQ'⟩ := hy
          exact ⟨rsd_mw_wlm_orient_opNorm_le_one P n Q' (R.orient y) hQ', (hJ _ Q' hQ').2.2⟩
        have hint1 : Integrable ((closedBall x (t * r)).indicator 1)
            (R.measure.restrict (closedBall x r)) :=
          (integrable_const (1 : ℝ)).indicator measurableSet_closedBall
        have hint2 : Integrable (fun y => ‖J (R.orient y) - J (R.orient x)‖)
            (R.measure.restrict (closedBall x r)) :=
          (hgr.sub (integrable_const (J (R.orient x)))).norm
        have hint3 : Integrable (fun y => R.orient y (ω y)) (R.measure.restrict (closedBall x r)) := by
          refine Integrable.mono' (integrable_const ‖J (R.orient x)‖) ?_ ?_
          · rw [show (fun y => R.orient y (ω y)) = fun y => χ y * R.orient y (J (R.orient x)) from
              funext hωy]
            exact χ.continuous.aestronglyMeasurable.mul
              ((ContinuousLinearMap.apply ℝ ℝ (J (R.orient x))).continuous.comp_aestronglyMeasurable
                hξr)
          · filter_upwards [hG] with y hy
            rw [hωy, norm_mul, Real.norm_of_nonneg (χ.nonneg' y)]
            calc χ y * ‖R.orient y (J (R.orient x))‖ ≤ 1 * (‖R.orient y‖ * ‖J (R.orient x)‖) :=
                  mul_le_mul χ.le_one ((R.orient y).le_opNorm _) (norm_nonneg _) zero_le_one
              _ ≤ ‖J (R.orient x)‖ := by
                  rw [one_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hy.1
        -- a.e., `1_{B̄_{tr}(x)} − ‖g − g(x)‖ ≤ χ ⟨g(x), ξ⟩`, as `⟨g, ξ⟩ = 1` and `‖ξ‖ ≤ 1`
        have hpt : ∀ᵐ y ∂(R.measure.restrict (closedBall x r)), (closedBall x (t * r)).indicator 1 y -
            ‖J (R.orient y) - J (R.orient x)‖ ≤ R.orient y (ω y) := by
          filter_upwards [hG] with y hy
          have h1 : R.orient y (ω y) =
              χ y + χ y * R.orient y (J (R.orient x) - J (R.orient y)) := by
            rw [hωy, (R.orient y).map_sub, hy.2, mul_sub, mul_one, add_sub_cancel]
          have h2 : |R.orient y (J (R.orient x) - J (R.orient y))| ≤
              ‖J (R.orient y) - J (R.orient x)‖ := by
            rw [← Real.norm_eq_abs, norm_sub_rev (J (R.orient y))]
            exact ((R.orient y).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hy.1)
          have h3 : (closedBall x (t * r)).indicator 1 y ≤ χ y := by
            by_cases hy' : y ∈ closedBall x (t * r)
            · rw [indicator_of_mem hy', Pi.one_apply]
              exact (χ.one_of_mem_closedBall hy').ge
            · rw [indicator_of_notMem hy']
              exact χ.nonneg' y
          have h4 : χ y * ‖J (R.orient y) - J (R.orient x)‖ ≤ ‖J (R.orient y) - J (R.orient x)‖ :=
            mul_le_of_le_one_left (norm_nonneg _) χ.le_one
          have h5 := mul_le_mul_of_nonneg_left (abs_le.1 h2).1 (χ.nonneg' y)
          rw [h1]
          linarith
        have hmono : ∫ y, ((closedBall x (t * r)).indicator 1 y -
            ‖J (R.orient y) - J (R.orient x)‖) ∂(R.measure.restrict (closedBall x r)) ≤
            ∫ y, R.orient y (ω y) ∂(R.measure.restrict (closedBall x r)) :=
          integral_mono_ae (hint1.sub hint2) hint3 hpt
        have hE1 : ∫ y, (closedBall x (t * r)).indicator 1 y ∂(R.measure.restrict (closedBall x r)) =
            (R.measure (closedBall x (t * r))).toReal := by
          rw [integral_indicator_one measurableSet_closedBall, measureReal_def,
            Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 htr1]
        have hE2 : ∫ y, ‖J (R.orient y) - J (R.orient x)‖ ∂(R.measure.restrict (closedBall x r)) =
            (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure).toReal :=
          integral_norm_eq_lintegral_enorm (hgr.1.sub aestronglyMeasurable_const)
        rw [integral_sub hint1 hint2, hE1, hE2] at hmono
        have hIfin : (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure) ≠ ∞ :=
          (hgr.sub (integrable_const (J (R.orient x)))).2.ne
        have hfin' : R.measure (closedBall x (t * r)) ≠ ∞ :=
          ne_top_of_le_ne_top hfin (measure_mono htr1)
        have hkey : R.measure (closedBall x (t * r)) -
            ∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure =
            ENNReal.ofReal ((R.measure (closedBall x (t * r))).toReal -
              (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure).toReal) := by
          rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin',
            ENNReal.ofReal_toReal hIfin]
        rw [hkey, hTω]
        exact ENNReal.ofReal_le_ofReal hmono
      -- (ii) `μ_T(B̄_{tr}(x))/(ωₙrⁿ) = tⁿ μ_T(B̄_{tr}(x))/(ωₙ(tr)ⁿ) → tⁿθ(x)`
      have hmap : Tendsto (fun r : ℝ => t * r) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h0 : Tendsto (fun r : ℝ => t * r) (𝓝 0) (𝓝 0) := by
            simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos ht0 hr
      have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
        rw [Ne, ENNReal.ofReal_eq_zero, not_le]
        positivity
      have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
      have hA : Tendsto (fun r : ℝ => R.measure (closedBall x (t * r)) /
          (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0)
          (𝓝 (θ x * ENNReal.ofReal (t ^ n))) := by
        refine (ENNReal.Tendsto.mul_const (hclosed.comp hmap) (Or.inr hctop)).congr'
          (Eventually.of_forall fun r => ?_)
        simp only [Function.comp]
        rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
          ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
          mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
      -- (iii) `∫_{B̄_r(x)} ‖g − g(x)‖ dμ_T/(ωₙrⁿ) = [⋯/μ_T(B̄_r(x))] · [μ_T(B̄_r(x))/(ωₙrⁿ)] → 0`
      have hB : Tendsto (fun r : ℝ =>
          (∫⁻ y in closedBall x r, ‖J (R.orient y) - J (R.orient x)‖ₑ ∂R.measure) /
            (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) (𝓝 0) := by
        have h := ENNReal.Tendsto.mul (hxd hxU).2 (Or.inr hθx) hclosed (Or.inr ENNReal.zero_ne_top)
        rw [zero_mul] at h
        refine h.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hs, hclosed.eventually_ne hθ0] with r hr hne
        have hfin : R.measure (closedBall x r) ≠ ∞ := hμK _ (isCompact_closedBall x r) (hsub r hr.2.le)
        have hpos : R.measure (closedBall x r) ≠ 0 := fun h0 => hne (by rw [h0, ENNReal.zero_div])
        exact ENNReal.div_mul_div_cancel hpos hfin
      -- (iv) `a < tⁿθ(x) = lim [μ_T(B̄_{tr}(x)) − ∫_{B̄_r(x)} ‖g − g(x)‖ dμ_T]/(ωₙrⁿ)`
      have hC := ENNReal.Tendsto.sub hA hB (Or.inl (ENNReal.mul_ne_top hθx hctop))
      rw [tsub_zero] at hC
      filter_upwards [(tendsto_order.1 hC).1 a (by rwa [mul_comm]), Ioo_mem_nhdsGT hs]
        with r hr hrs
      refine hr.trans_le ?_
      have hV : unitBallVolume n * ENNReal.ofReal (r ^ n) ≠ 0 :=
        mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hrs.1 n)).ne'
      rw [← ENNReal.sub_div (fun _ _ => hV)]
      exact ENNReal.div_le_div_right (hlow r hrs.1 hrs.2.le) _
    · -- upper bound: `M_{B_r(x)}(T) ≤ μ_T(B_r(x))` (Ch. 6, Remark 3.2(3), `≤` half)
      filter_upwards [(tendsto_order.1 hopen).2 b hb] with r hr
      exact (ENNReal.div_le_div_right (rsd_mw_massOn_le_measure P n U T R hRT _) _).trans_lt hr
  -- Step 2: conclusion (a)
  have ha : ∀ᵐ x ∂R.measure, x ∈ ball p ρ → R.mult x = k := by
    filter_upwards [hF1, hM] with x hx hxM hxB
    -- `x ∈ spt T`: otherwise `T` vanishes on an open `W ∋ x`, and `Θⁿ(μ_T, x) = 0 < θ(x)`
    have hxT : x ∈ T.support := by
      by_contra hxT
      have hxZ : x ∈ T.zeroRegion := by
        by_contra hxZ
        exact hxT (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
      obtain ⟨W, ⟨hWo, -, -, hTW⟩, hxW⟩ := mem_sUnion.mp hxZ
      obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hWo x hxW
      -- `M_{B_s(x)}(T) = 0` for `0 < s < r`: every admissible form is supported in `W`
      have h0 : Tendsto (fun s : ℝ => T.massOn (ball x s) /
          (unitBallVolume n * ENNReal.ofReal (s ^ n))) (𝓝[>] 0) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hr] with s hs
        have hm : T.massOn (ball x s) = 0 := by
          refine nonpos_iff_eq_zero.1 (sSup_le ?_)
          rintro _ ⟨ω, ⟨hωs, -⟩, rfl⟩
          exact (ENNReal.ofReal_eq_zero.2
            (hTW ω (hωs.trans ((ball_subset_ball hs.2.le).trans hrW))).le).le
        rw [hm, ENNReal.zero_div]
      have h1 := tendsto_nhds_unique hx.2 h0
      rw [ENNReal.ofReal_natCast, Nat.cast_eq_zero] at h1
      exact (R.mult_pos x hxM).ne' h1
    -- the density at `x ∈ spt T ∩ B` is both `θ(x)` and `k`
    have h2 := tendsto_nhds_unique hx.2 (hk x hxT hxB).2
    rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, Nat.cast_inj] at h2
  -- Step 3: `θ ≥ 1` on `M` gives `Hⁿ⌞M ≪ μ_T`, so (a) holds `Hⁿ⌞M`-a.e.; restrict to `M ∩ B`
  have hac : ν ≪ R.measure := by
    refine withDensity_absolutelyContinuous' hθm.aemeasurable ?_
    filter_upwards [ae_restrict_mem R.measurableSet_carrier] with x hx
    exact Nat.cast_ne_zero.2 (R.mult_pos x hx).ne'
  have hb : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ ball p ρ)), x ∈ ball p ρ → R.mult x = k :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (hac.ae_le ha)
  refine ⟨ha, ?_⟩
  filter_upwards [hb, ae_restrict_mem (R.measurableSet_carrier.inter isOpen_ball.measurableSet)]
    with x hx hxB
  exact hx hxB.2

/-- **Constant positive density puts the support inside the carrier, up to an `Hⁿ`-null set**
(step 4 of the first-variation formula for a constant-density sheet, in its support form; Simon
Ch. 1, Theorem 3.6 and Remark 3.7(2), chapter-01.txt lines 700–711; Ch. 6, Remark 3.2(3),
chapter-06.txt lines 755–770).  Let `T = τ(S, θ, ξ)` in the open set `U`, `B = B_ρ(p) ⊆ U`,
`k ≥ 1`, and `Θⁿ(μ_T, y) = k` at every `y ∈ spt T ∩ B`.  As `θ ≥ 1` on `S`, `Hⁿ⌞S` is locally
finite in `U`, so by the upper density theorem `Hⁿ(S ∩ B̄_r(x)) / rⁿ → 0` for `Hⁿ`-a.e.
`x ∈ U ∖ S`.  For such `x ∈ spt T ∩ B` and `0 < r < ρ − |x − p|`,
`M_{B_r(x)}(T) ≤ μ_T(B_r(x)) = k Hⁿ(S ∩ B_r(x))`: a unit simple `ξ` has `|⟨ω, ξ⟩| ≤ |ω|`, and
`θ = k` a.e. on `S ∩ B` (`Submission.idtp_ccd_sfv_mult_ae_eq_density`).  So the density ratio of
`T` at `x` is at most `(k / ωₙ) Hⁿ(S ∩ B̄_r(x)) / rⁿ → 0`, contradicting `Θⁿ(μ_T, x) = k ≥ 1`.
Hence `(spt T ∩ B) ∖ S` lies in the `Hⁿ`-null exceptional set. -/
theorem Submission.idtp_ccd_sfv_support_sdiff_carrier_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (p : Euclid P) (ρ : ℝ) (k : ℕ), IsOpen U → R.Represents T → ball p ρ ⊆ U → 1 ≤ k → (∀ y ∈ T.support, y ∈ ball p ρ → HasMassDensity T y k) → μHE[n] ((T.support ∩ ball p ρ) \ R.carrier) = 0 := by
  intro P n
  -- Step 2 input (Simon 1.3.3, 1.3.4 and 1.3.6, with the crude covering constant `6ⁿ`): if `S`
  -- is Borel with `Hⁿ(S) < ∞`, then `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` for `Hⁿ`-a.e. `x ∉ S`.  A failure
  -- at `x` puts `x` in a threshold set; Vitali's lemma and weak regularity of `Hⁿ⌞S` make every
  -- threshold set null.
  have upper_density_zero : ∀ S : Set (Euclid P), MeasurableSet S → μHE[n] S ≠ ∞ →
      ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S →
        Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0)
          (𝓝 0) := by
    intro S hS hfin
    -- (i) Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
    -- 3-fold enlargements cover the centres.
    have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
        (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
        ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
          u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
          E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
      intro E p δ hE
      obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
        (fun a : Euclid P × ℝ => closedBall a.1 a.2)
        {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
        (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
        (fun a ha => nonempty_closedBall.2 ha.2.1.le)
      refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
      · apply hdisj.countable_of_nonempty_interior
        intro a ha
        refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
        rw [isOpen_ball.interior_eq]
        exact mem_ball_self (huT ha).2.1
      · intro x hx
        obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
        obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
        refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
        rw [mem_closedBall]
        have h1 : dist w x ≤ ρ := hw1
        have h2 : dist w b.1 ≤ b.2 := hw2
        have hle' : ρ ≤ 2 * b.2 := hle
        calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
          _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
          _ ≤ 3 * b.2 := by linarith
    -- (ii) comparison (Simon 1.3.3 with the crude constant 6 ^ n).
    have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
        (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
        t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
      intro t E G ht0 httop hG hE
      have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
          (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
            t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
          u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
          E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
        fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
          (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
      choose u hucount hu hdisj hcover using hfam
      have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
      -- packing estimate
      have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
        intro j
        rw [← ENNReal.tsum_mul_left]
        calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
            ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
              ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
          _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
              (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
                fun a _ => hG.inter measurableSet_closedBall).symm
          _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
      -- diameter estimate
      have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
          ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
        intro j a
        apply ediam_le_of_forall_dist_le
        intro y hy z hz
        rw [mem_closedBall] at hy hz
        calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
              dist_triangle_right _ _ _
          _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
      have hterm : ∀ j, t * ∑' a : u j,
          ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
            6 ^ n * μHE[n] G := by
        intro j
        calc t * ∑' a : u j,
              ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
            ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
              gcongr with a
              rw [ENNReal.rpow_natCast]
              calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                  ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
                _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                  norm_num
          _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
              rw [ENNReal.tsum_mul_left]; ring
          _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
      have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
        (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
        (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
        (by
          rw [← ENNReal.ofReal_zero]
          apply ENNReal.tendsto_ofReal
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          simpa using this.const_mul 6)
        (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
          have := (hu j a a.2).2.2.1
          linarith)))
        (Eventually.of_forall fun j x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
      have hbound : ∀ j, ∑' a : u j,
          ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
            6 ^ n * μHE[n] G / t := by
        intro j
        rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
        exact hterm j
      have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
        hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
      calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
        _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
    -- (iii) each threshold set is null (Simon 1.3.6).
    have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
        μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
          t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
      intro t ht0 httop
      set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
      have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
        intro ε hε
        have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
        have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
          Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
        have hpos : t * ε / 6 ^ n ≠ 0 := by
          apply ENNReal.div_ne_zero.2
          exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
        obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
          (μ := (μHE[n] : Measure (Euclid P)).restrict S)
          (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
        have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
        have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
          rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
        have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
            t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
          intro x hx δ hδ
          obtain ⟨hxS, hfreq⟩ := hx
          have hxF : x ∉ F := fun h => hxS (hFS h)
          obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
          have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
            Ioo_mem_nhdsGT (by positivity)
          obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
          refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
          have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
            pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
          have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
          have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
            (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
          have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
            ext y
            constructor
            · rintro ⟨hyS, hyB⟩
              refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
              rw [mem_ball]
              have := mem_closedBall.1 hyB
              have := hρ.2
              have := min_le_right δ (r₁ / 2)
              linarith
            · rintro ⟨⟨hyS, _⟩, hyB⟩
              exact ⟨hyS, hyB⟩
          rw [← h2]
          exact h1.le
        have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
        have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
        have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
        have hlt : t * μH[(n : ℝ)] N < t * ε := by
          calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
            _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
            _ = t * ε := ENNReal.mul_div_cancel h6 h6'
        exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
      have hH : μH[(n : ℝ)] N = 0 := by
        by_contra h
        exact lt_irrefl _ (key _ h)
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
    -- (iv) every failure of convergence lies in a threshold set.
    rw [ae_iff]
    apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
    · intro x hx
      simp only [mem_ofPred_eq, Classical.not_imp] at hx
      obtain ⟨hxS, hnt⟩ := hx
      rw [ENNReal.tendsto_nhds_zero] at hnt
      push Not at hnt
      obtain ⟨ε, hε, hfreq⟩ := hnt
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
      calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
        _ < ε := hk
        _ < _ := hρ
    · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)
  -- Step 2 input, localized (Simon 1.3.7(2)): if `U` is open and `Hⁿ(S ∩ K) < ∞` for every
  -- compact `K ⊆ U`, the same holds for `Hⁿ`-a.e. `x ∈ U ∖ S`.  Countably many balls
  -- `B_{r_y}(y)` with `B̄_{r_y}(y) ⊆ U` cover `U`, and near `x ∈ B_{r_y}(y)` the piece
  -- `S ∩ B_{r_y}(y)` agrees with `S`.
  have local_density_zero : ∀ U S : Set (Euclid P), IsOpen U → MeasurableSet S →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S →
        Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0)
          (𝓝 0) := by
    intro U S hU hS hfin
    -- (i) a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U`.
    have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
      intro x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
    choose! r hr0 hrU using hr
    obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
      (f := fun y => ball y (r y)) (s := U)
      fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
    -- (ii) the finite-measure theorem on each piece `S ∩ B(y, r y)`, simultaneously
    -- for the countably many `y ∈ D`.
    have hpiece : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
        Tendsto (fun ρ : ℝ => μHE[n] (S ∩ ball y (r y) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
          (𝓝[>] 0) (𝓝 0) := by
      rw [ae_ball_iff hDc]
      intro y hy
      apply upper_density_zero _ (hS.inter measurableSet_ball)
      exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
        (measure_mono (inter_subset_inter_right S ball_subset_closedBall))
    -- (iii) localization: for small `ρ`, `B̄(x, ρ) ⊆ B(y, r y)`, so the piece agrees with `S`.
    filter_upwards [hpiece] with x hx hxU hxS
    obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov hxU)
    obtain ⟨ε, hε, hεy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
    refine (hx y hyD fun h => hxS h.1).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
    rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεy)]
  -- Step 5(d) input (Simon 6.2.6(a)): a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
  -- has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm.  Expand `α = Σ_I α(e_I) e^I` over
  -- strictly increasing `I`; Cauchy–Binet gives `Σ_I e^I(τ)² = 1`, then use Cauchy–Schwarz.
  have orient_le : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ξ Q → ∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α := by
    -- `D u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`, a continuous alternating map as an
    -- alternatization; `e^I = D (e ∘ I)` and `γ = D τ`
    let D : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
      ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun k => innerSL ℝ (u k))
    have hD : ∀ u v, D u v =
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
      intro u v
      simp only [D, ContinuousMultilinearMap.alternatization_apply_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
    -- `D u v = D v u` (determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
    have hDsymm : ∀ u v, D u v = D v u := by
      intro u v
      rw [hD, hD]
      refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
      rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
        ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
    -- `D u u = 1` for orthonormal `u`: only `σ = 1` contributes
    have hD1 : ∀ u, Orthonormal ℝ u → D u u = 1 := by
      intro u hu
      rw [hD, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul]
        refine Finset.prod_eq_one fun k _ => ?_
        rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `e^I(e_K) = δ_IK` for strictly increasing `I`, `K`; a nonzero term forces
    -- `K ∘ σ = I`, so `range I = range K` and `I = K`
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp e.orthonormal
    have hK : ∀ I K : Fin n → Fin P, StrictMono I → StrictMono K →
        D (fun k => e (I k)) (fun k => e (K k)) = if I = K then 1 else 0 := by
      intro I K hI hK
      split_ifs with hIK
      · subst hIK
        exact hD1 _ (e.orthonormal.comp I hI.injective)
      · rw [hD]
        refine Finset.sum_eq_zero fun σ _ => ?_
        rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
        by_contra! h
        apply hIK
        have hKσ : K ∘ σ = I := funext fun k => by
          have := h k (Finset.mem_univ k)
          rw [he] at this
          split_ifs at this with hk
          · exact hk.symm
          · exact absurd rfl this
        rw [← StrictMono.range_inj_of_wellFoundedLT hI hK, ← hKσ, EquivLike.range_comp]
    -- `α = Σ_{I ∈ S} α(e_I) e^I`; both sides are alternating, so compare them on `e ∘ f`
    -- for injective `f`, and write `f = (f ∘ σ) ∘ σ⁻¹` with `f ∘ σ` strictly increasing
    let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
    have hE : ∀ α : Covector (Euclid P) n,
        α = ∑ I ∈ S, α (fun k => e (I k)) • D (fun k => e (I k)) := by
      intro α
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      refine e.toBasis.ext_alternating fun f hf => ?_
      simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
      set σ := Tuple.sort f
      have hfσ : StrictMono (f ∘ σ) :=
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
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hfσ hfσ, ite_eq_left rfl, smul_eq_mul,
          mul_one]
      · intro I hI hIf
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hfσ,
          ite_eq_right hIf, smul_zero]
      · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfσ⟩) h
    -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
    have hnorm : ∀ β : Covector (Euclid P) n,
        covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
      intro β
      rw [covectorEuclideanNorm, Finset.sum_filter]
    -- Cauchy–Binet: `Σ_{I ∈ S} e^I(τ)² = 1` for orthonormal `τ`; evaluate the expansion
    -- of `γ = D τ` at `τ`, using `γ(τ) = 1` and `γ(e_I) = e^I(τ)`
    have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
        ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 = 1 := by
      intro τ hτ
      have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (D τ))
      simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul, hD1 τ hτ] at h
      rw [h]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [hDsymm τ, sq]
    -- `ξ(α) = ±α(τ)`, and `|Σ_I α(e_I) e^I(τ)| ≤ |α| (Σ_I e^I(τ)²)^{1/2} = |α|`
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have hξabs : |ξ α| = |α τ| := by
      rcases hξ with h | h
      · rw [h]
      · rw [h, abs_neg]
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * D (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCB τ hτ, mul_one]
  -- Step 5(d) input, the `≤` half of `M_W(T) = μ_T(W)` (Simon 6.3.2(3)): for admissible `ω`
  -- (`spt ω ⊆ W`, `|ω| ≤ 1`), `T(ω) ≤ ∫_S θ |⟨ω, ξ⟩| dHⁿ ≤ ∫_{S ∩ spt ω} θ dHⁿ ≤ μ_T(W)`.
  have massOn_le : ∀ (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n),
      R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
    intro U T R hT W
    -- `|⟨α, ξ(x)⟩| ≤ |α|` at `Hⁿ`-a.e. `x ∈ S`, where `ξ(x)` is a unit simple `n`-vector
    have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
        |R.orient x α| ≤ covectorEuclideanNorm α := by
      filter_upwards [R.orients] with x hx
      obtain ⟨Q, -, hQ⟩ := hx
      exact orient_le (R.orient x) Q hQ
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    show ENNReal.ofReal (T ω) ≤ R.measure W
    set S := tsupport (ω : DifferentialForm (Euclid P) n)
    have hS : MeasurableSet S := (isClosed_tsupport _).measurableSet
    rw [hT ω, IMRep.action]
    calc _ ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
            ∂μHE[n]‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in R.carrier,
            ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in R.carrier, S.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
          refine lintegral_mono_ae ?_
          filter_upwards [hξ] with x hx
          by_cases hxS : x ∈ S
          · -- `|θ⟨ω, ξ⟩| ≤ θ|ω| ≤ θ` on `spt ω`
            rw [indicator_of_mem hxS, enorm_mul, Real.enorm_natCast, Real.enorm_eq_ofReal_abs]
            exact mul_le_of_le_one_right zero_le
              (ENNReal.ofReal_le_one.2 ((hx _).trans (hω1 x)))
          · -- `ω = 0` off `spt ω`
            rw [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport hxS, map_zero, mul_zero,
              enorm_zero]
      _ = R.measure S := by rw [lintegral_indicator hS, IMRep.measure, withDensity_apply _ hS]
      _ ≤ R.measure W := measure_mono hωW
  intro U T R p ρ k hU hR hB hk hdens
  -- Step 1: `Hⁿ⌞S` is locally finite in `U`: `Hⁿ(S ∩ K) ≤ ∫_{S ∩ K} θ dHⁿ < ∞`, as `θ ≥ 1` on `S`.
  have hloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    refine setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet) ?_
    intro x hx
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (R.mult_pos x hx.1).ne'
  -- Step 2: `f_x(r) = Hⁿ(S ∩ B̄_r(x)) / rⁿ → 0` for every `x ∈ U ∖ S` off an `Hⁿ`-null set `Z`.
  have hZ := local_density_zero U R.carrier hU R.measurableSet_carrier hloc
  -- Step 3: `θ = k` at `Hⁿ⌞(S ∩ B)`-a.e. point.
  have hθ := (Submission.idtp_ccd_sfv_mult_ae_eq_density P n U T R p ρ k hU hR hdens).2
  -- Step 4: `0 < ωₙ < ∞`, so `k / ωₙ ≠ ∞`.
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hc : (k : ℝ≥0∞) / unitBallVolume n ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top k) hω0
  -- Step 6, reduced to step 5: `(spt T ∩ B) ∖ S ⊆ Z`.
  refine measure_mono_null ?_ (ae_iff.1 hZ)
  rintro x ⟨⟨hxT, hxB⟩, hxS⟩
  simp only [mem_ofPred_eq]
  intro hx
  -- Step 5(a), (b): `f_x(r) → 0`, while `g_x(r) = M_{B_r(x)}(T) / (ωₙ rⁿ) → k`.
  have hf := hx (hB hxB) hxS
  have hg := (hdens x hxT hxB).2
  -- Step 5(c)–(f): `g_x(r) ≤ (k / ωₙ) f_x(r)` for `0 < r < δ = ρ − |x − p|`.
  have hδ : 0 < ρ - dist x p := sub_pos.2 (mem_ball.1 hxB)
  have hle : ∀ r ∈ Ioo (0 : ℝ) (ρ - dist x p),
      T.massOn (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) ≤
        (k : ℝ≥0∞) / unitBallVolume n *
          (μHE[n] (R.carrier ∩ closedBall x r) / ENNReal.ofReal r ^ n) := by
    rintro r ⟨hr0, hrδ⟩
    have hrB : ball x r ⊆ ball p ρ := ball_subset_ball' (by linarith)
    -- `μ_T(B_r(x)) = ∫_{B_r(x) ∩ S} θ dHⁿ = k Hⁿ(S ∩ B_r(x))`
    have hμ : R.measure (ball x r) = (k : ℝ≥0∞) * μHE[n] (R.carrier ∩ ball x r) := by
      rw [IMRep.measure, withDensity_apply _ measurableSet_ball,
        Measure.restrict_restrict measurableSet_ball]
      have hae : ∀ᵐ y ∂(μHE[n].restrict (ball x r ∩ R.carrier)), R.mult y = k :=
        ae_restrict_of_ae_restrict_of_subset
          (fun y (hy : y ∈ ball x r ∩ R.carrier) =>
            (⟨hy.2, hrB hy.1⟩ : y ∈ R.carrier ∩ ball p ρ)) hθ
      have hcongr : ∫⁻ y in ball x r ∩ R.carrier, (R.mult y : ℝ≥0∞) ∂μHE[n] =
          ∫⁻ _ in ball x r ∩ R.carrier, (k : ℝ≥0∞) ∂μHE[n] :=
        lintegral_congr_ae (hae.mono fun y hy => by simp [hy])
      rw [hcongr, setLIntegral_const, inter_comm]
    calc T.massOn (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))
        ≤ R.measure (ball x r) / (unitBallVolume n * ENNReal.ofReal (r ^ n)) :=
          ENNReal.div_le_div_right (massOn_le U T R hR _) _
      _ = (k : ℝ≥0∞) / unitBallVolume n *
            (μHE[n] (R.carrier ∩ ball x r) / ENNReal.ofReal r ^ n) := by
          rw [hμ, ENNReal.ofReal_pow hr0.le,
            ENNReal.mul_div_mul_comm (Or.inl hω0) (Or.inl hωtop)]
      _ ≤ (k : ℝ≥0∞) / unitBallVolume n *
            (μHE[n] (R.carrier ∩ closedBall x r) / ENNReal.ofReal r ^ n) := by
          gcongr
          exact ball_subset_closedBall
  -- Step 5(g): `(k / ωₙ) f_x(r) → (k / ωₙ) · 0 = 0`.
  have hlim : Tendsto (fun r : ℝ => (k : ℝ≥0∞) / unitBallVolume n *
      (μHE[n] (R.carrier ∩ closedBall x r) / ENNReal.ofReal r ^ n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hf (Or.inr hc)
  -- Step 5(h): in the limit `k ≤ 0`, contradicting `k ≥ 1`; so `x ∈ Z`.
  have hle0 : ENNReal.ofReal (k : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto hg hlim
      (Filter.mem_of_superset (Ioo_mem_nhdsGT hδ) fun r hr => hle r hr)
  have hk0 : (k : ℝ) ≤ 0 := ENNReal.ofReal_eq_zero.1 (le_antisymm hle0 bot_le)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith
/-- **The tangent space of an embedded `C¹` submanifold** (Simon Ch. 2, §4, (4.3)).  If `M` is an
embedded `C¹` `d`-dimensional submanifold of `ℝᴾ` and `x ∈ M`, then `T_xM` is a linear subspace of
dimension `d`: for a local representation `ψ : V → W ∩ M` with `ψ(v) = x`, `T_xM` is the range of
the injective linear map `Dψ(v)`.  A `C¹` curve in `M` through `x` stays in `ψ(V)` near `0` and,
`ψ` being proper and injective, lifts to a curve in `V` converging to `v` at rate `O(t)` (`Dψ(v)` is
injective), so its velocity lies in the closed subspace `range Dψ(v)`; conversely `Dψ(v) u` is the
velocity of `t ↦ ψ(v + a sin(t / a) u)` for small `a > 0`. -/
theorem Submission.idtp_ccd_sfv_span_tangentSpace_finrank : ∀ (P d : ℕ) (M : Set (Euclid P)) (x : Euclid P), IsEmbeddedSubmanifold 1 d M → x ∈ M → (Submodule.span ℝ (tangentSpace M x) : Set (Euclid P)) = tangentSpace M x ∧ Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = d := by
  intro P d M x hM hx
  obtain ⟨V, W, ψ, hVo, hWo, hxW, hψC, hψinj, hψim, hprop, hψD⟩ := hM x hx
  obtain ⟨v, hvV, rfl⟩ : x ∈ ψ '' V := hψim ▸ ⟨hxW, hx⟩
  rw [Nat.cast_one] at hψC
  set L : Euclid d →L[ℝ] Euclid P := fderiv ℝ ψ v
  have hψd : HasFDerivAt ψ L v :=
    ((hψC.contDiffAt (hVo.mem_nhds hvV)).differentiableAt one_ne_zero).hasFDerivAt
  have hrange :
      Set.range L = ((LinearMap.range (L : Euclid d →ₗ[ℝ] Euclid P)) : Set (Euclid P)) := by
    rw [LinearMap.coe_range]; rfl
  have key : tangentSpace M (ψ v) = Set.range L := by
    ext w
    constructor
    · rintro ⟨γ, -, hγM, hγ0, hγd⟩
      -- lift `γ` near `0` to a curve `φ` in the compact set `S = V ∩ ψ⁻¹(B̄_r(ψ v))`
      have hγc : Tendsto γ (𝓝 0) (𝓝 (ψ v)) := hγ0 ▸ hγd.continuousAt.tendsto
      obtain ⟨r, hr, hrW⟩ := nhds_basis_closedBall.mem_iff.mp (hWo.mem_nhds hxW)
      set S := V ∩ ψ ⁻¹' closedBall (ψ v) r
      have hS : IsCompact S := hprop _ hrW (isCompact_closedBall _ _)
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 ∧ γ t ∈ closedBall (ψ v) r := by
        filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1),
          hγc (closedBall_mem_nhds _ hr)] with t h1 h2
        exact ⟨h1, h2⟩
      have hpre : ∀ t, t ∈ Ioo (-1 : ℝ) 1 ∧ γ t ∈ closedBall (ψ v) r → ∃ z ∈ S, ψ z = γ t := by
        rintro t ⟨ht, htK⟩
        obtain ⟨z, hz, hzt⟩ : γ t ∈ ψ '' V := hψim ▸ ⟨hrW htK, hγM ht⟩
        exact ⟨z, ⟨hz, by rw [mem_preimage, hzt]; exact htK⟩, hzt⟩
      classical
      set φ : ℝ → Euclid d := fun t =>
        if h : t ∈ Ioo (-1 : ℝ) 1 ∧ γ t ∈ closedBall (ψ v) r then (hpre t h).choose else v
        with hφ_def
      have hφ : ∀ᶠ t in 𝓝 (0 : ℝ), φ t ∈ S ∧ ψ (φ t) = γ t := hev.mono fun t ht => by
        rw [hφ_def]; dsimp only; rw [dite_eq_left ht]; exact (hpre t ht).choose_spec
      -- `φ t → v`: every cluster point `z ∈ S` has `ψ z = ψ v`
      have hφv : Tendsto φ (𝓝 0) (𝓝 v) := by
        refine hS.tendsto_nhds_of_unique_mapClusterPt (hφ.mono fun t ht => ht.1) ?_
        intro z hz hcl
        have hψz : ContinuousAt ψ z := hψC.continuousOn.continuousAt (hVo.mem_nhds hz.1)
        have h1 : MapClusterPt (ψ z) (𝓝 0) (ψ ∘ φ) := hcl.continuousAt_comp hψz
        have h2 : Tendsto (ψ ∘ φ) (𝓝 0) (𝓝 (ψ v)) := hγc.congr' (hφ.mono fun t ht => ht.2.symm)
        exact hψinj hz.1 hvV (eq_of_nhds_neBot (ClusterPt.mono h1 h2))
      -- `‖φ t - v‖ ≤ 2K ‖γ t - ψ v‖`, `K` an antilipschitz constant of `L`
      obtain ⟨K, hKpos, hK⟩ := (L : Euclid d →ₗ[ℝ] Euclid P).exists_antilipschitzWith
        (LinearMap.ker_eq_bot.mpr (hψD v hvV))
      have hK0 : (0 : ℝ) < K := hKpos
      have hKL : ∀ h, ‖h‖ ≤ K * ‖L h‖ := fun h => hK.le_mul_norm (map_zero _) h
      have h1 : (fun t => ψ (φ t) - ψ v - L (φ t - v)) =o[𝓝 0] (fun t => φ t - v) :=
        hψd.isLittleO.comp_tendsto hφv
      have h2 : (fun t => φ t - v) =O[𝓝 0] (fun t => γ t - ψ v) := by
        refine Asymptotics.IsBigO.of_bound (2 * K) ?_
        filter_upwards [h1.bound (c := 1 / (2 * K)) (by positivity), hφ] with t ht hφt
        rw [hφt.2] at ht
        have h4 : ‖L (φ t - v)‖ ≤ ‖γ t - ψ v‖ + 1 / (2 * K) * ‖φ t - v‖ := by
          calc ‖L (φ t - v)‖ = ‖(γ t - ψ v) - (γ t - ψ v - L (φ t - v))‖ := by congr 1; abel
            _ ≤ ‖γ t - ψ v‖ + ‖γ t - ψ v - L (φ t - v)‖ := norm_sub_le _ _
            _ ≤ ‖γ t - ψ v‖ + 1 / (2 * K) * ‖φ t - v‖ := by gcongr
        have h5 : ‖φ t - v‖ ≤ K * ‖γ t - ψ v‖ + ‖φ t - v‖ / 2 := by
          calc ‖φ t - v‖ ≤ K * ‖L (φ t - v)‖ := hKL _
            _ ≤ K * (‖γ t - ψ v‖ + 1 / (2 * K) * ‖φ t - v‖) := by gcongr
            _ = K * ‖γ t - ψ v‖ + ‖φ t - v‖ / 2 := by field_simp
        linarith
      have h6 : (fun t => φ t - v) =O[𝓝 0] (fun t : ℝ => t) := by
        have h' := hγd.isBigO_sub
        rw [hγ0] at h'
        simpa only [sub_zero] using h2.trans h'
      -- hence `t • w - L (φ t - v) = o(t)`, and `w` is a limit of points of `range L`
      have h7 : (fun t => ψ (φ t) - ψ v - L (φ t - v)) =o[𝓝 0] (fun t : ℝ => t) :=
        h1.trans_isBigO h6
      have h8 : (fun t => γ t - ψ v - L (φ t - v)) =o[𝓝 0] (fun t : ℝ => t) :=
        h7.congr' (hφ.mono fun t ht => by dsimp only; rw [ht.2]) EventuallyEq.rfl
      have h9 : (fun t => γ t - ψ v - t • w) =o[𝓝 0] (fun t : ℝ => t) := by
        have := hasDerivAt_iff_isLittleO.mp hγd
        simpa [hγ0] using this
      have h10 : (fun t => t • w - L (φ t - v)) =o[𝓝 0] (fun t : ℝ => t) :=
        (h8.sub h9).congr_left fun t => by abel
      have h11 : Tendsto (fun t : ℝ => t⁻¹ • (t • w - L (φ t - v))) (𝓝[≠] 0) (𝓝 0) :=
        h10.tendsto_inv_smul_nhds_zero.mono_left nhdsWithin_le_nhds
      have h12 : Tendsto (fun t : ℝ => L (t⁻¹ • (φ t - v))) (𝓝[≠] 0) (𝓝 w) := by
        have := (tendsto_const_nhds (x := w)).sub h11
        rw [sub_zero] at this
        refine this.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 0)
        rw [smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul, map_smul]
        abel
      have hclosed : IsClosed (Set.range L) :=
        hrange ▸ (LinearMap.range (L : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
      exact hclosed.mem_of_tendsto h12 (Eventually.of_forall fun t => ⟨_, rfl⟩)
    · rintro ⟨u, rfl⟩
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hVo v hvV
      set a : ℝ := δ / (‖u‖ + 1) with ha
      have ha0 : 0 < a := by positivity
      set c : ℝ → Euclid d := fun t => v + (a * Real.sin (t / a)) • u with hc
      have hcV : ∀ t, c t ∈ V := fun t => hδV (by
        rw [mem_ball, dist_eq_norm, hc, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_pos ha0]
        calc a * |Real.sin (t / a)| * ‖u‖ ≤ a * 1 * ‖u‖ := by
              gcongr; exact Real.abs_sin_le_one _
          _ < δ := by
              rw [mul_one, ha, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
              nlinarith [norm_nonneg u])
      have hcC : ContDiff ℝ 1 c := by
        rw [hc]; fun_prop
      have hcd : HasDerivAt c u 0 := by
        have h1 : HasDerivAt (fun t : ℝ => a * Real.sin (t / a)) 1 0 := by
          have := (((hasDerivAt_id (0 : ℝ)).div_const a).sin).const_mul a
          simpa [ha0.ne'] using this
        simpa only [one_smul] using (h1.smul_const u).const_add v
      refine ⟨ψ ∘ c, (hψC.comp_contDiff hcC hcV).contDiffOn, fun t _ => ?_, ?_, ?_⟩
      · exact ((hψim ▸ mem_image_of_mem ψ (hcV t)) : ψ (c t) ∈ W ∩ M).2
      · simp [hc]
      · exact hψd.comp_hasDerivAt_of_eq 0 hcd (by simp [hc])
  have hspan : Submodule.span ℝ (tangentSpace M (ψ v)) =
      LinearMap.range (L : Euclid d →ₗ[ℝ] Euclid P) := by
    rw [key, hrange, Submodule.span_eq]
  refine ⟨?_, ?_⟩
  · rw [hspan, ← hrange, key]
  · rw [hspan, LinearMap.finrank_range_of_inj (hψD v hvV), finrank_euclideanSpace_fin]

/-- **Approximate tangent planes of a carrier inside a `C¹` submanifold** (Simon Ch. 3,
Remark 1.5(2); used with Ch. 4, 2.6 for 7.3.3).  Let `R = (S, θ, ξ)` be an integer multiplicity
triple, `M` an embedded `C¹` `n`-dimensional submanifold, `IsOpen V` and `Hⁿ((S ∩ V) \ M) = 0`.
Then `TₓS = span TₓM` for `Hⁿ`-a.e. `x ∈ S ∩ V`.  For such `x` the field `orients` gives an
approximate tangent plane `Q` of `S` at `x` with `x ∈ M`, and the chosen plane is `Q`.  With a
chart `ψ` of `M` and `ψ(v) = x`, `M` is flat at `x` along `Dψ(v)(ℝⁿ)`; as `M ∪ Vᶜ` carries
`Hⁿ`-almost all of `S`, a bump at a point of `Q` off `Dψ(v)(ℝⁿ)` would have positive `Hⁿ⌞Q`
integral but vanishing blow-up integrals, so `Q ⊆ Dψ(v)(ℝⁿ)`.  Velocities of the curves
`ψ(v + h(t)a)` give `Dψ(v)(ℝⁿ) ⊆ TₓM`, and `dim Q = n = dim span TₓM`
(`idtp_ccd_sfv_span_tangentSpace_finrank`) forces `Q = span TₓM`. -/
theorem Submission.idtp_ccd_sfv_approxTangentPlane_eq_span_ae : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (M V : Set (Euclid P)), IsEmbeddedSubmanifold 1 n M → IsOpen V → μHE[n] ((R.carrier ∩ V) \ M) = 0 → ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ V)), approxTangentPlane n R.carrier x = Submodule.span ℝ (tangentSpace M x) := by
  intro P n U R N O hN hO hnull
  set S := R.carrier with hSdef
  have hSO : MeasurableSet (S ∩ O) := R.measurableSet_carrier.inter hO.measurableSet
  -- `Hⁿ⌞(S ∩ O)`-a.e. `x` has an approximate tangent plane of `S` (field `orients`), lies in
  -- `S ∩ O`, and lies in `N` (as `Hⁿ((S ∩ O) \ N) = 0`)
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (S ∩ O)), ∃ Q, HasApproximateTangentSpaceAt n S x Q :=
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients).mono
      fun x ⟨Q, hQ, _⟩ => ⟨Q, hQ⟩
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (S ∩ O)), x ∈ S ∩ O := ae_restrict_mem hSO
  have h3 : ∀ᵐ x ∂(μHE[n].restrict (S ∩ O)), x ∈ N := by
    rw [ae_iff, Measure.restrict_apply' hSO]
    refine measure_mono_null (fun y hy => ?_) hnull
    exact ⟨hy.2, hy.1⟩
  filter_upwards [h1, h2, h3] with x hx1 hx2 hxN
  obtain ⟨Q, hQ⟩ := hx1
  -- (a) the chosen plane is `Q` (Ch. 3, Remark 1.5(1))
  have hAQ : approxTangentPlane n S x = Q := by
    have h : ∃ Q', HasApproximateTangentSpaceAt n S x Q' := ⟨Q, hQ⟩
    unfold approxTangentPlane
    rw [dite_eq_left h]
    exact h.choose_spec.unique hQ
  -- (b) `Q ≤ T` whenever a set `N'` carrying `Hⁿ`-almost all of `S` is flat at `x` along `T`:
  -- for `q ∈ Q \ T` the bump `g = max(0, δ/2 − |· − q|)`, `δ = dist(q, T)`, has `∫_Q g dHⁿ > 0`,
  -- while `∫_{η_{x,r}(S)} g dHⁿ = 0` for all small `r`
  have hle : ∀ (N' : Set (Euclid P)) (T : Submodule ℝ (Euclid P)), μHE[n] (S \ N') = 0 →
      (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N', dist z x < ρ →
        ∃ t ∈ T, ‖z - x - t‖ ≤ ε * ‖z - x‖) → Q ≤ T := by
    intro N' T hnull' hflat q hq
    by_contra hqT
    -- `T` is closed, so `δ = dist(q, T) > 0`
    have hTc : IsClosed (T : Set (Euclid P)) := T.closed_of_finiteDimensional
    have hδ : 0 < infDist q (T : Set (Euclid P)) :=
      (hTc.notMem_iff_infDist_pos ⟨0, T.zero_mem⟩).1 hqT
    set δ := infDist q (T : Set (Euclid P)) with hδdef
    -- the bump `g = max(0, δ/2 − |· − q|)`, positive exactly on `B_{δ/2}(q)`
    set g : Euclid P → ℝ := fun y => max 0 (δ / 2 - ‖y - q‖) with hgdef
    have hgc : Continuous g :=
      continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
    have hg0 : 0 ≤ g := fun y => le_max_left _ _
    have hgsupp : ∀ y, g y ≠ 0 → ‖y - q‖ < δ / 2 := by
      intro y hy
      by_contra h
      have h' : δ / 2 ≤ ‖y - q‖ := not_lt.mp h
      apply hy
      exact max_eq_left (by linarith)
    have hgpos : ∀ y, ‖y - q‖ < δ / 2 → 0 < g y := fun y hy =>
      lt_max_of_lt_right (by linarith)
    have hgcs : HasCompactSupport g := by
      apply HasCompactSupport.intro (isCompact_closedBall q (δ / 2))
      intro y hy
      by_contra h
      apply hy
      rw [mem_closedBall, dist_eq_norm]
      exact (hgsupp y h).le
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hgc⟩, hgcs⟩
    -- `∫_Q g dHⁿ > 0`: `Hⁿ⌞Q` is regular with support `Q ∋ q`
    have hQn : Module.finrank ℝ Q = n := hQ.1
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQn
    have hsupp :=
      Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQn
    have hint : Integrable g ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))) :=
      hgc.integrable_of_hasCompactSupport hgcs
    have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
      rw [integral_pos_iff_support_of_nonneg hg0 hint]
      have hq' : q ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
        rw [hsupp]
        exact hq
      have hball : 0 < ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)))
          (ball q (δ / 2)) :=
        (Measure.mem_support_iff_forall q).1 hq' _ (ball_mem_nhds q (by linarith))
      refine hball.trans_le (measure_mono ?_)
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy
      exact (hgpos y hy).ne'
    -- constants: `ε (|q| + δ) = δ / 2`
    have hqδ : 0 < ‖q‖ + δ := by positivity
    set ε : ℝ := δ / (2 * (‖q‖ + δ)) with hεdef
    have hε : 0 < ε := by positivity
    have hεq : ε * (‖q‖ + δ) = δ / 2 := by
      rw [hεdef]
      field_simp
    obtain ⟨ρ, hρ, hflatρ⟩ := hflat ε hε
    -- `∫_{η_{x,r}(S)} g dHⁿ = 0` for `0 < r < ρ / (|q| + δ)`
    have hvan : ∀ r : ℝ, 0 < r → r < ρ / (‖q‖ + δ) →
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂μHE[n] = 0 := by
      intro r hr hrρ
      -- `η_{x,r}(S \ N') = r⁻¹ (S \ N' − x)` is `Hⁿ`-null
      have hnull'' : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S \ N')) = 0 := by
        have himg' : Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S \ N') =
            (fun y => r⁻¹ • y) '' ((fun y => y - x) '' (S \ N')) := by
          rw [Set.image_image]
          rfl
        have hiso : Isometry (fun y : Euclid P => y - x) :=
          Isometry.of_dist_eq fun a b => dist_sub_right a b x
        rw [himg', Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
          hiso.euclideanHausdorffMeasure_image, hnull', smul_zero]
      -- flatness: `g` vanishes on `η_{x,r}(S ∩ N')`
      have hsub : {y | g y ≠ 0} ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ⊆
          Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S \ N') := by
        rintro y ⟨hgy, z, hzS, rfl⟩
        refine ⟨z, ⟨hzS, fun hzN => ?_⟩, rfl⟩
        have hyq : ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z - q‖ < δ / 2 := hgsupp _ hgy
        set y := Poincare.SimonGMT.Chapter03.blowUpMap x r z with hy
        have hy' : y = r⁻¹ • (z - x) := rfl
        have hzx : z - x = r • y := by
          rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
        have hynorm : ‖y‖ < ‖q‖ + δ / 2 := by
          calc ‖y‖ = ‖(y - q) + q‖ := by rw [sub_add_cancel]
            _ ≤ ‖y - q‖ + ‖q‖ := norm_add_le _ _
            _ < δ / 2 + ‖q‖ := by linarith
            _ = ‖q‖ + δ / 2 := by ring
        have hzxn : ‖z - x‖ = r * ‖y‖ := by
          rw [hzx, norm_smul, Real.norm_of_nonneg hr.le]
        have hdist : dist z x < ρ := by
          rw [dist_eq_norm, hzxn]
          calc r * ‖y‖ ≤ r * (‖q‖ + δ) := by gcongr; linarith
            _ < ρ / (‖q‖ + δ) * (‖q‖ + δ) := by gcongr
            _ = ρ := by field_simp
        obtain ⟨t, htT, ht⟩ := hflatρ z hzN hdist
        have hrt : r⁻¹ • t ∈ T := T.smul_mem _ htT
        have hyt : y - r⁻¹ • t = r⁻¹ • (z - x - t) := by
          rw [hy']
          exact (smul_sub _ _ _).symm
        have hyt' : ‖y - r⁻¹ • t‖ ≤ ε * ‖y‖ := by
          rw [hyt, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
          calc r⁻¹ * ‖z - x - t‖ ≤ r⁻¹ * (ε * ‖z - x‖) := by gcongr
            _ = ε * ‖y‖ := by rw [hzxn]; field_simp
        have hle' : δ ≤ ‖q - r⁻¹ • t‖ := by
          rw [← dist_eq_norm]
          exact infDist_le_dist_of_mem hrt
        have h2' : ε * ‖y‖ ≤ δ / 2 := by
          rw [← hεq]
          gcongr
          linarith
        have hlt : ‖q - r⁻¹ • t‖ < δ := by
          calc ‖q - r⁻¹ • t‖ = ‖(q - y) + (y - r⁻¹ • t)‖ := by congr 1; abel
            _ ≤ ‖q - y‖ + ‖y - r⁻¹ • t‖ := norm_add_le _ _
            _ < δ / 2 + δ / 2 := by
              have h1' : ‖q - y‖ < δ / 2 := by rw [norm_sub_rev]; exact hyq
              linarith
            _ = δ := by ring
        linarith
      -- so `g = 0` a.e. for `Hⁿ⌞η_{x,r}(S)`, evaluated on the set `{g ≠ 0}`
      have hmeas : MeasurableSet {y | g y ≠ 0} :=
        (isOpen_ne_fun hgc continuous_const).measurableSet
      apply integral_eq_zero_of_ae
      rw [EventuallyEq, ae_iff]
      change (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S)) {y | g y ≠ 0} = 0
      rw [Measure.restrict_apply hmeas]
      exact measure_mono_null hsub hnull''
    -- the blow-up integrals of `g` are eventually `0`, so their limit `∫_Q g dHⁿ` is `0`
    have hlim := hQ.2 f
    have hev : (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S, f y ∂μHE[n])
        =ᶠ[𝓝[>] 0] fun _ => 0 := by
      have hpos' : 0 < ρ / (‖q‖ + δ) := by positivity
      filter_upwards [Ioo_mem_nhdsGT hpos'] with r hr
      exact hvan r hr.1 hr.2
    have hlim0 : Tendsto (fun r : ℝ => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' S,
        f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' hev.symm
    have heq := tendsto_nhds_unique hlim hlim0
    have hzero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := heq
    linarith
  -- a chart `ψ : Vc → W ∩ N` of `N` (Ch. 2, §4, (4.1)) and `v ∈ Vc` with `ψ v = x`
  obtain ⟨Vc, W, ψ, hVc, hW, hxW, hψ, hinj, himg, hprop, hDψ⟩ := hN x hxN
  obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' Vc := by
    rw [himg]
    exact ⟨hxW, hxN⟩
  have hψ1 : ContDiffOn ℝ 1 ψ Vc := by exact_mod_cast hψ
  -- (c) `N` is flat at `ψ v` along `Dψ(v)(ℝⁿ)`: properness, continuity and injectivity of `ψ`
  -- force `z = ψ(β)` with `β` close to `v`, and the first-order expansion at `v` together with
  -- the coercivity `|h| ≤ K|Dψ(v)h|` absorbs the remainder
  have hflatN : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ N, dist z (ψ v) < ρ →
      ∃ h : Euclid n, ‖z - ψ v - fderiv ℝ ψ v h‖ ≤ ε * ‖z - ψ v‖ := by
    intro ε hε
    set L := fderiv ℝ ψ v with hLdef
    have hdiff : DifferentiableAt ℝ ψ v :=
      (hψ1.differentiableOn one_ne_zero).differentiableAt (hVc.mem_nhds hv)
    have hL : HasFDerivAt ψ L v := hdiff.hasFDerivAt
    have hcont : ContinuousOn ψ Vc := hψ1.continuousOn
    -- coercivity of the injective derivative
    obtain ⟨K, hKpos, hK⟩ := LinearMap.exists_antilipschitzWith (L : Euclid n →ₗ[ℝ] Euclid P)
      (LinearMap.ker_eq_bot.mpr (hDψ v hv))
    have hcoer : ∀ h : Euclid n, ‖h‖ ≤ K * ‖L h‖ := fun h =>
      ContinuousLinearMap.bound_of_antilipschitz L hK h
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hKpos
    set η : ℝ := min (1 / (2 * K)) (ε / (2 * K)) with hηdef
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    have hηK : η * K ≤ 1 / 2 := by
      calc η * K ≤ 1 / (2 * K) * K := by gcongr; exact min_le_left _ _
        _ = 1 / 2 := by field_simp
    have hηε : η * (2 * K) ≤ ε := by
      calc η * (2 * K) ≤ ε / (2 * K) * (2 * K) := by gcongr; exact min_le_right _ _
        _ = ε := by field_simp
    -- first-order expansion
    obtain ⟨σ, hσ, hσball⟩ := Metric.eventually_nhds_iff.1 (hL.isLittleO.bound hη)
    -- a compact set away from `v`
    obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.isOpen_iff.1 hW (ψ v) hxW
    set δ₀ : ℝ := δ₁ / 2 with hδ₀eq
    have hδ₀ : 0 < δ₀ := by positivity
    have hcbW : closedBall (ψ v) δ₀ ⊆ W := (closedBall_subset_ball (by linarith)).trans hδ₁W
    have hA : IsCompact (Vc ∩ ψ ⁻¹' closedBall (ψ v) δ₀) :=
      hprop _ hcbW (isCompact_closedBall _ _)
    set C := (Vc ∩ ψ ⁻¹' closedBall (ψ v) δ₀) \ ball v σ with hCdef
    have hC : IsCompact C := hA.diff isOpen_ball
    have hCV : C ⊆ Vc := fun β hβ => hβ.1.1
    -- positive separation on `C`
    obtain ⟨m, hm, hmC⟩ : ∃ m : ℝ, 0 < m ∧ ∀ β ∈ C, m ≤ ‖ψ β - ψ v‖ := by
      rcases C.eq_empty_or_nonempty with hCe | hCne
      · refine ⟨1, one_pos, fun β hβ => ?_⟩
        rw [hCe] at hβ
        exact hβ.elim
      · have hfc : ContinuousOn (fun β => ‖ψ β - ψ v‖) C :=
          ((hcont.mono hCV).sub continuousOn_const).norm
        obtain ⟨β₀, hβ₀C, hβ₀min⟩ := hC.exists_isMinOn hCne hfc
        refine ⟨‖ψ β₀ - ψ v‖, ?_, fun β hβ => (isMinOn_iff.mp hβ₀min) β hβ⟩
        rcases (norm_nonneg (ψ β₀ - ψ v)).lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have h0 : ψ β₀ = ψ v := by
            have h' := heq.symm
            rwa [norm_eq_zero, sub_eq_zero] at h'
          have hβv := hinj (hCV hβ₀C) hv h0
          apply hβ₀C.2
          rw [hβv]
          exact mem_ball_self hσ
    refine ⟨min δ₀ m, lt_min hδ₀ hm, ?_⟩
    intro z hzN hzd
    have hzcb : z ∈ closedBall (ψ v) δ₀ := mem_closedBall.2 (hzd.trans_le (min_le_left _ _)).le
    have hzim : z ∈ ψ '' Vc := by
      rw [himg]
      exact ⟨hcbW hzcb, hzN⟩
    obtain ⟨β, hβV, rfl⟩ := hzim
    have hβA : β ∈ Vc ∩ ψ ⁻¹' closedBall (ψ v) δ₀ := ⟨hβV, hzcb⟩
    have hβσ : dist β v < σ := by
      by_contra hcon
      have hβC : β ∈ C := ⟨hβA, fun hb => hcon (mem_ball.1 hb)⟩
      have h1' := hmC β hβC
      rw [← dist_eq_norm] at h1'
      have h2' : min δ₀ m ≤ dist (ψ β) (ψ v) := (min_le_right _ _).trans h1'
      linarith
    refine ⟨β - v, ?_⟩
    have hest : ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hσball hβσ
    have hLh : ‖L (β - v)‖ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by
      calc ‖L (β - v)‖ = ‖(ψ β - ψ v) - (ψ β - ψ v - L (β - v))‖ := by congr 1; abel
        _ ≤ ‖ψ β - ψ v‖ + ‖ψ β - ψ v - L (β - v)‖ := norm_sub_le _ _
        _ ≤ ‖ψ β - ψ v‖ + η * ‖β - v‖ := by gcongr
    have hh : ‖β - v‖ ≤ 2 * K * ‖ψ β - ψ v‖ := by
      have h2' : ‖β - v‖ ≤ K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by
        calc ‖β - v‖ ≤ K * ‖L (β - v)‖ := hcoer (β - v)
          _ ≤ K * (‖ψ β - ψ v‖ + η * ‖β - v‖) := by gcongr
          _ = K * ‖ψ β - ψ v‖ + (η * K) * ‖β - v‖ := by ring
      have h3' : (η * K) * ‖β - v‖ ≤ 1 / 2 * ‖β - v‖ := by gcongr
      linarith
    calc ‖ψ β - ψ v - L (β - v)‖ ≤ η * ‖β - v‖ := hest
      _ ≤ η * (2 * K * ‖ψ β - ψ v‖) := by gcongr
      _ = (η * (2 * K)) * ‖ψ β - ψ v‖ := by ring
      _ ≤ ε * ‖ψ β - ψ v‖ := by gcongr
  -- (d) `Dψ(v)(ℝⁿ) ⊆ T_{ψ v}N` (Ch. 2, §4, (4.3)): `Dψ(v) a` is the velocity at `0` of the
  -- `C¹` curve `t ↦ ψ(v + h(t) a)` in `N`, `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
  have hrange : ∀ a : Euclid n, fderiv ℝ ψ v a ∈ tangentSpace N (ψ v) := by
    intro a
    have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
      ((hψ1.differentiableOn one_ne_zero).differentiableAt (hVc.mem_nhds hv)).hasFDerivAt
    have hVN : ψ '' Vc ⊆ N := himg ▸ inter_subset_right
    by_cases ha : a = 0
    · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
      subst ha
      refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hVN (mem_image_of_mem ψ hv), rfl, ?_⟩
      simpa using hasDerivAt_const (0 : ℝ) (ψ v)
    · obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hVc v hv
      have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
      set c : ℝ := ρ₀ / ‖a‖ with hc_def
      have hc : 0 < c := div_pos hρ₀ ha'
      have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
      set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
      -- `h` is smooth, `h'(0) = 1` and `|h| ≤ c / 2`
      have h_cd : ContDiff ℝ 1 h :=
        contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _))
          fun t => (hden t).ne'
      have h_deriv : HasDerivAt h 1 0 := by
        have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
          (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1)
          (hden 0).ne'
        convert this using 1
        simp
      have h_bd : ∀ t, |h t| ≤ c / 2 := by
        intro t
        rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
        have h1' : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
          rw [sq_abs]; field_simp
        rw [h1', le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (c - |t|)]
      -- `β` stays in `B_{ρ₀}(v) ⊆ Vc`, `β(0) = v` and `β'(0) = a`
      set β : ℝ → Euclid n := fun t => v + h t • a with hβ_def
      have hβV : ∀ t, β t ∈ Vc := fun t => hball <| by
        rw [Metric.mem_ball, dist_eq_norm, hβ_def]
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
          _ = ρ₀ / 2 := by rw [hc_def]; field_simp
          _ < ρ₀ := by linarith
      have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
      have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
      have hβ_deriv : HasDerivAt β a 0 := by
        have := HasDerivAt.const_add v (h_deriv.smul_const a)
        rwa [one_smul] at this
      -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(Vc) ⊆ N`, and `γ'(0) = Dψ(v) a`
      refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
        fun t _ => hVN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
      exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm
  -- (e) localize: `N ∪ Oᶜ` carries `Hⁿ`-almost all of `S` and is flat at `ψ v` along
  -- `Dψ(v)(ℝⁿ)`, since `B_s(ψ v) ⊆ O`; so `Q ≤ Dψ(v)(ℝⁿ) ≤ span T_{ψ v}N`
  obtain ⟨s, hs, hsO⟩ := Metric.isOpen_iff.mp hO (ψ v) hx2.2
  have hQT : Q ≤ LinearMap.range (fderiv ℝ ψ v : Euclid n →ₗ[ℝ] Euclid P) := by
    apply hle (N ∪ Oᶜ)
    · refine measure_mono_null (fun y hy => ?_) hnull
      simp only [Set.mem_sdiff, mem_union, mem_compl_iff, not_or, not_not] at hy
      exact ⟨⟨hy.1, hy.2.2⟩, hy.2.1⟩
    · intro ε hε
      obtain ⟨ρ, hρ, hρN⟩ := hflatN ε hε
      refine ⟨min ρ s, lt_min hρ hs, fun z hz hzd => ?_⟩
      have hzN : z ∈ N := by
        rcases hz with hz | hz
        · exact hz
        · exact absurd (hsO (mem_ball.2 (hzd.trans_le (min_le_right _ _)))) hz
      obtain ⟨h, hh⟩ := hρN z hzN (hzd.trans_le (min_le_left _ _))
      exact ⟨_, LinearMap.mem_range_self _ h, hh⟩
  have hTspan : LinearMap.range (fderiv ℝ ψ v : Euclid n →ₗ[ℝ] Euclid P) ≤
      Submodule.span ℝ (tangentSpace N (ψ v)) := by
    intro y hy
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hy
    exact Submodule.subset_span (hrange a)
  -- (f) `dim Q = n = dim span T_{ψ v}N` (sibling `tangent_space_dim`), so `Q = span T_{ψ v}N`
  rw [hAQ]
  exact Submodule.eq_of_le_of_finrank_eq (hQT.trans hTspan)
    (by rw [hQ.1, (Submission.idtp_ccd_sfv_span_tangentSpace_finrank P n N (ψ v) hN hxN).2])

/-- **First variation of a constant-density sheet** (Simon Ch. 4, 2.2–2.3, for the varifold
`v(M, θ)`; step 6(b) and the first equality of step 9 of the parent proof).  Let `T = τ(S, θ, ξ)`
in the open set `U`, `B = B_ρ(p) ⊆ U`, `k ≥ 1`, `M` an embedded `C¹` `n`-submanifold with
`spt T ∩ B = M ∩ B`, and `Θⁿ(μ_T, y) = k` at every `y ∈ spt T ∩ B`.  Then every `C¹` field `X`
with compact support in `B` has `δV(X) = k ∫_{M ∩ B} tr(p_{TₓM} ∘ DX(x)) dHⁿ(x)`.
* `(S ∩ B) ∖ M` is `Hⁿ`-null.  Its points lie off `spt T`, hence in the open zero region of `T`.
  A ball `B_r(x)` there misses `spt T`, so `idtp_ccd_sfv_mult_ae_eq_density` with density `0`
  gives `θ = 0` a.e. on `S ∩ B_r(x)`; as `θ ≥ 1` on `S`, `Hⁿ(S ∩ B_r(x)) = 0`.
* `(M ∩ B) ∖ S = (spt T ∩ B) ∖ S` is `Hⁿ`-null (`idtp_ccd_sfv_support_sdiff_carrier_null`).
* `θ = k` (`idtp_ccd_sfv_mult_ae_eq_density`) and `TₓS = span TₓM`
  (`idtp_ccd_sfv_approxTangentPlane_eq_span_ae`) hold `Hⁿ`-a.e. on `S ∩ B`.
* `DX = 0` off `spt X ⊆ B`, so `δV(X) = ∫_{S ∩ B} θ div_S X dHⁿ = k ∫_{S ∩ B} tr(p_{TₓM} DX) dHⁿ`,
  and `S ∩ B = M ∩ B` up to an `Hⁿ`-null set. -/
theorem Submission.idtp_ccd_sheet_first_variation : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n) (M : Set (Euclid P)) (p : Euclid P) (ρ : ℝ) (k : ℕ), IsOpen U → R.Represents T → ball p ρ ⊆ U → 1 ≤ k → IsEmbeddedSubmanifold 1 n M → T.support ∩ ball p ρ = M ∩ ball p ρ → (∀ y ∈ T.support, y ∈ ball p ρ → HasMassDensity T y k) → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball p ρ → R.firstVariation X = (k : ℝ) * ∫ x in M ∩ ball p ρ, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[n] := by
  intro P n U T R M p ρ k hU hRT hBU hk hM hsupp hdens X _ _ hXB
  have hS : MeasurableSet R.carrier := R.measurableSet_carrier
  -- Step 2: `(S ∩ B) \ M` is `Hⁿ`-null.  Its points lie off `spt T`, so in the open zero region
  -- of `T`.  A ball `B_r(x)` there misses `spt T`, so `idtp_ccd_sfv_mult_ae_eq_density` applies
  -- vacuously with `k = 0`: `θ = 0` a.e. on `S ∩ B_r(x)`, and `θ ≥ 1` on `S` makes this null.
  have hSM : μHE[n] ((R.carrier ∩ ball p ρ) \ M) = 0 := by
    refine measure_null_of_locally_null _ fun x hx => ?_
    have hxz : x ∈ T.zeroRegion := by
      by_contra hxz
      have hxT : x ∈ T.support ∩ ball p ρ :=
        ⟨mem_sdiff_of_mem (R.carrier_subset hx.1.1) hxz, hx.1.2⟩
      rw [hsupp] at hxT
      exact hx.2 hxT.1
    obtain ⟨r, hr, hrz⟩ := Metric.isOpen_iff.1 T.isOpen_zeroRegion x hxz
    have h0 := (Submission.idtp_ccd_sfv_mult_ae_eq_density P n U T R x r 0 hU hRT
      fun y hy hyr => absurd (hrz hyr) hy.2).2
    have hfalse : ∀ᵐ y ∂(μHE[n].restrict (R.carrier ∩ ball x r)), False := by
      filter_upwards [h0, ae_restrict_mem (hS.inter isOpen_ball.measurableSet)] with y hy hyS
      exact (R.mult_pos y hyS.1).ne' hy
    have hnull : μHE[n] (R.carrier ∩ ball x r) = 0 :=
      Measure.restrict_eq_zero.1 (ae_eq_bot.1 (eventually_false_iff_eq_bot.1 hfalse))
    refine ⟨((R.carrier ∩ ball p ρ) \ M) ∩ ball x r,
      inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hr)),
      measure_mono_null (fun y hy => ?_) hnull⟩
    exact ⟨hy.1.1.1, hy.2⟩
  -- Step 4: `(M ∩ B) \ S` is `Hⁿ`-null, as `spt T ∩ B = M ∩ B`; so `S ∩ B = M ∩ B` a.e.
  have hMS : μHE[n] ((M ∩ ball p ρ) \ R.carrier) = 0 := by
    rw [← hsupp]
    exact Submission.idtp_ccd_sfv_support_sdiff_carrier_null P n U T R p ρ k hU hRT hBU hk hdens
  have hSMae : R.carrier ∩ ball p ρ =ᵐ[μHE[n]] M ∩ ball p ρ := by
    refine ae_eq_set.2 ⟨measure_mono_null (fun y hy => ?_) hSM,
      measure_mono_null (fun y hy => ?_) hMS⟩
    · exact ⟨hy.1, fun hyM => hy.2 ⟨hyM, hy.1.2⟩⟩
    · exact ⟨hy.1, fun hyS => hy.2 ⟨hyS, hy.1.2⟩⟩
  -- Steps 3 and 5: `θ = k` and `TₓS = span TₓM` for `Hⁿ`-a.e. `x ∈ S ∩ B`.
  have hθ := (Submission.idtp_ccd_sfv_mult_ae_eq_density P n U T R p ρ k hU hRT hdens).2
  have hT := Submission.idtp_ccd_sfv_approxTangentPlane_eq_span_ae P n U R M (ball p ρ) hM
    isOpen_ball hSM
  -- Step 6: the integrand vanishes off `tsupport X ⊆ B`.
  have hS0 : ∀ x ∈ R.carrier \ (R.carrier ∩ ball p ρ),
      (R.mult x : ℝ) * tangentialDivergence n R.carrier X x = 0 := by
    intro x hx
    have hxX : x ∉ tsupport X := fun h => hx.2 ⟨hx.1, hXB h⟩
    simp [tangentialDivergence, fderiv_of_notMem_tsupport ℝ hxX]
  -- Step 7: evaluation.
  calc R.firstVariation X
      = ∫ x in R.carrier ∩ ball p ρ, (R.mult x : ℝ) * tangentialDivergence n R.carrier X x
          ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hS inter_subset_left hS0
    _ = ∫ x in R.carrier ∩ ball p ρ, (k : ℝ) * LinearMap.trace ℝ (Euclid P)
          ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
            (fderiv ℝ X x).toLinearMap) ∂μHE[n] := by
        refine integral_congr_ae ?_
        filter_upwards [hT, hθ] with x hxT hxθ
        simp only [tangentialDivergence, hxT, hxθ]
    _ = (k : ℝ) * ∫ x in R.carrier ∩ ball p ρ, LinearMap.trace ℝ (Euclid P)
          ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
            (fderiv ℝ X x).toLinearMap) ∂μHE[n] :=
        integral_const_mul _ _
    _ = _ := by rw [setIntegral_congr_set hSMae]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
