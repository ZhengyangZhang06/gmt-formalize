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

/-- **Faces of the unit cubical lattice** (Simon Ch. 6, §5: the `n`-faces `F ∈ 𝓛ₙ` used in the proof
of the deformation theorem 5.1).  Let `n = m + 1` and `p = (z, ι)` with `ι : Fin n → Fin P` strictly
increasing.  The map `Φ_p(y) = z + Σⱼ yⱼ e_{ι(j)}` has coordinates `z_{ι(k)} + y_k` at `ι(k)` and
`zᵢ` off `range ι`, so it is an isometric embedding `ℝⁿ → ℝᴾ` with `Φ_p⁻¹(F_p) = [0, 1]ⁿ` and
`F_p ⊆ range Φ_p`.  As `μHE[n] = volume` on `ℝⁿ`, `Φ_p#μHE[n] = μHE[n]⌞range Φ_p` and `∂[0, 1]ⁿ` is
Lebesgue-null, `Hⁿ⌞F_p = Φ_p#(Lⁿ⌞(0, 1)ⁿ)`; hence `Hⁿ(F_p) = 1` and
`∫_{F_p} f dHⁿ = ∫_{(0, 1)ⁿ} f ∘ Φ_p`.  `F_p` is closed with diameter `≤ √P`, and the non-integer
coordinates of a point of `Φ_p((0, 1)ⁿ)` determine `ι` and `z`, so it lies in no other face
`F_q`. -/
theorem Submission.dor_lmb_fcd_fr_face_geometry : ∀ (P m : ℕ) (p : (Fin P → ℤ) × (Fin (m + 1) → Fin P)), StrictMono p.2 → volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ μHE[m + 1] {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = 1 ∧ (μHE[m + 1] : Measure (Euclid P)).restrict {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} = Measure.map (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∀ f : Euclid P → ℝ, ∫ x in {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, f x ∂μHE[m + 1] = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, f (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ))) ∧ (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}) ∧ (∀ y y' : Euclid (m + 1), dist (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.2 j) (1 : ℝ)) = dist y y') ∧ (∀ x ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, ∀ x' ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}, dist x x' ≤ Real.sqrt P) ∧ IsClosed {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ∧ ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p → ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) ∉ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧ (i ∉ Set.range q.2 → x i = q.1 i)} := by
  intro P m p hp
  -- the face map `Φ = Φ_p`, the closed face `F = F_p`, the open cube `Q = Q₁`, the closed cube `C`
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ)
  let F : Set (Euclid P) := {x : Euclid P | ∀ i : Fin P,
    (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)}
  let Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  let C : Set (Euclid (m + 1)) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  show volume Q = 1 ∧ μHE[m + 1] F = 1 ∧
    (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) ∧
    (∀ f : Euclid P → ℝ, ∫ x in F, f x ∂μHE[m + 1] = ∫ y in Q, f (Φ y)) ∧
    (∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F) ∧
    (∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y') ∧
    (∀ x ∈ F, ∀ x' ∈ F, dist x x' ≤ Real.sqrt P) ∧ IsClosed F ∧
    ∀ q : (Fin P → ℤ) × (Fin (m + 1) → Fin P), StrictMono q.2 → q ≠ p →
      ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → Φ y ∉ {x : Euclid P | ∀ i : Fin P,
        (i ∈ Set.range q.2 → (q.1 i : ℝ) ≤ x i ∧ x i ≤ q.1 i + 1) ∧
          (i ∉ Set.range q.2 → x i = q.1 i)}
  have hinj : Injective p.2 := hp.injective
  -- Step 1: coordinates of `Φ`
  have hcoord : ∀ y i, Φ y i = p.1 i + ∑ j, if i = p.2 j then y j else 0 := by
    intro y i
    simp [Φ, Pi.single_apply]
  have hcoord_mem : ∀ y k, Φ y (p.2 k) = p.1 (p.2 k) + y k := by
    intro y k
    rw [hcoord]
    simp [hinj.eq_iff]
  have hcoord_nmem : ∀ y i, i ∉ range p.2 → Φ y i = p.1 i := by
    intro y i hi
    rw [hcoord, add_eq_left]
    exact Finset.sum_eq_zero fun j _ => ite_eq_right fun h => hi ⟨j, h.symm⟩
  -- Step 2: `Φ` is an isometry, hence a measurable embedding
  have hdist : ∀ y y' : Euclid (m + 1), dist (Φ y) (Φ y') = dist y y' := by
    intro y y'
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    symm
    refine Fintype.sum_of_injective p.2 hinj _ _ (fun i hi => ?_) (fun k => ?_)
    · rw [hcoord_nmem y i hi, hcoord_nmem y' i hi, dist_self]
      simp
    · rw [hcoord_mem, hcoord_mem, dist_add_left]
  have hiso : Isometry Φ := Isometry.of_dist_eq hdist
  have hemb : MeasurableEmbedding Φ := hiso.isClosedEmbedding.measurableEmbedding
  -- Step 3: `Φ` maps the closed cube `C` into `F`, `F ⊆ range Φ` and `Φ⁻¹(F) = C`
  have hCF : ∀ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) → Φ y ∈ F := by
    intro y hy i
    constructor
    · rintro ⟨k, rfl⟩
      rw [hcoord_mem]
      constructor <;> linarith [(hy k).1, (hy k).2]
    · exact hcoord_nmem y i
  have hFrange : F ⊆ range Φ := by
    intro x hx
    refine ⟨WithLp.toLp 2 fun k => x (p.2 k) - p.1 (p.2 k), PiLp.ext fun i => ?_⟩
    by_cases hi : i ∈ range p.2
    · obtain ⟨k, rfl⟩ := hi
      rw [hcoord_mem]
      simp
    · rw [hcoord_nmem _ i hi]
      exact ((hx i).2 hi).symm
  have hpreF : Φ ⁻¹' F = C := by
    ext y
    refine ⟨fun hy k => ?_, hCF y⟩
    have h := (hy (p.2 k)).1 ⟨k, rfl⟩
    rw [hcoord_mem] at h
    constructor <;> linarith [h.1, h.2]
  -- Step 4: `volume Q = volume C = 1`
  have hvol := PiLp.volume_preserving_ofLp (Fin (m + 1))
  have hQ_eq : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hC_eq : C = WithLp.ofLp ⁻¹' (Set.Icc (0 : Fin (m + 1) → ℝ) 1) := by
    ext y
    simp [C, Pi.le_def, forall_and]
  have hQmeas : MeasurableSet Q := by
    rw [hQ_eq]
    exact hvol.measurable (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hvolQ : volume Q = 1 := by
    rw [hQ_eq, hvol.measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hvolC : volume C = 1 := by
    rw [hC_eq, hvol.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
    simp
  have hQC : volume.restrict C = volume.restrict Q := by
    refine (Measure.restrict_congr_set ?_).symm
    refine ae_eq_of_subset_of_measure_ge (fun y hy i => ⟨(hy i).1.le, (hy i).2.le⟩)
      (hvolC.trans hvolQ.symm).le hQmeas.nullMeasurableSet ?_
    rw [hvolC]
    exact ENNReal.one_ne_top
  -- Step 5: `F` is closed
  have hcont : ∀ i : Fin P, Continuous fun x : Euclid P => x i := fun i =>
    PiLp.continuous_apply 2 _ i
  have hFclosed : IsClosed F := by
    have hF : F = ⋂ i : Fin P, {x : Euclid P | (i ∈ Set.range p.2 →
        (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} :=
      Set.ofPred_forall _
    rw [hF]
    refine isClosed_iInter fun i =>
      (isClosed_imp isOpen_const ?_).inter (isClosed_imp isOpen_const ?_)
    · exact (isClosed_le continuous_const (hcont i)).inter (isClosed_le (hcont i) continuous_const)
    · exact isClosed_eq (hcont i) continuous_const
  have hFmeas : MeasurableSet F := hFclosed.measurableSet
  -- Step 6: `Hⁿ⌞F = Φ#(volume⌞Q)`
  have hmeas :
      (μHE[m + 1] : Measure (Euclid P)).restrict F = Measure.map Φ (volume.restrict Q) := by
    have h1 : Measure.map Φ (volume : Measure (Euclid (m + 1))) =
        (μHE[m + 1] : Measure (Euclid P)).restrict (range Φ) := by
      rw [← hiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    rw [← hQC, ← hpreF, ← hemb.restrict_map, h1, Measure.restrict_restrict hFmeas,
      inter_eq_left.2 hFrange]
  -- Step 7: `Hⁿ(F) = 1`
  have hFmass : μHE[m + 1] F = 1 := by
    have h := congrArg (fun μ : Measure (Euclid P) => μ univ) hmeas
    simp only [Measure.restrict_apply_univ] at h
    rw [h, hemb.map_apply, preimage_univ, Measure.restrict_apply_univ, hvolQ]
  refine ⟨hvolQ, hFmass, hmeas, fun f => ?_, hCF, hdist, ?_, hFclosed, ?_⟩
  -- Step 8: the integral formula
  · rw [hmeas, hemb.integral_map]
  -- Step 9: `diam F ≤ √P`
  · intro x hx x' hx'
    rw [EuclideanSpace.dist_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, dist (x i) (x' i) ^ 2 ≤ ∑ _i : Fin P, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => pow_le_one₀ dist_nonneg ?_
          by_cases hi : i ∈ range p.2
          · have h := (hx i).1 hi
            have h' := (hx' i).1 hi
            rw [Real.dist_eq, abs_le]
            constructor <;> linarith [h.1, h.2, h'.1, h'.2]
          · rw [(hx i).2 hi, (hx' i).2 hi, dist_self]
            exact zero_le_one
      _ = P := by simp
  -- Step 10: the open face `Φ(Q)` meets no other closed face
  · intro q hq hqp y hy hx
    apply hqp
    have hsub : range p.2 ⊆ range q.2 := by
      rintro _ ⟨k, rfl⟩
      by_contra hk
      have h := (hx (p.2 k)).2 hk
      rw [hcoord_mem] at h
      have a1 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) := by linarith [(hy k).1]
      have a2 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [(hy k).2]
      have b1 : p.1 (p.2 k) < q.1 (p.2 k) := by exact_mod_cast a1
      have b2 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a2
      omega
    have hrange : range p.2 = range q.2 := by
      apply Set.eq_of_subset_of_card_le hsub
      rw [Set.card_range_of_injective hq.injective, Set.card_range_of_injective hinj]
    have h2 : p.2 = q.2 := (hp.range_inj_of_wellFoundedLT hq).1 hrange
    have h1 : p.1 = q.1 := by
      funext i
      by_cases hi : i ∈ range p.2
      · obtain ⟨k, rfl⟩ := hi
        have h := (hx (p.2 k)).1 (hrange ▸ ⟨k, rfl⟩)
        rw [hcoord_mem] at h
        have a1 : (q.1 (p.2 k) : ℝ) < p.1 (p.2 k) + 1 := by linarith [h.1, (hy k).2]
        have a2 : (p.1 (p.2 k) : ℝ) < q.1 (p.2 k) + 1 := by linarith [h.2, (hy k).1]
        have b1 : q.1 (p.2 k) < p.1 (p.2 k) + 1 := by exact_mod_cast a1
        have b2 : p.1 (p.2 k) < q.1 (p.2 k) + 1 := by exact_mod_cast a2
        omega
      · have h : (p.1 i : ℝ) = q.1 i := by
          rw [← hcoord_nmem y i hi]
          exact (hx i).2 (hrange ▸ hi)
        exact_mod_cast h
    exact Prod.ext h1.symm h2.symm

/-- **The `(m + 1)`-cells of the unit cubical lattice meeting a compact set** (Simon Ch. 6, proof
of the deformation theorem 5.1, (26)–(33), with `n = m + 1`).  `L_n` is the set of points of `ℝᴾ`
with at least `P − n` integer coordinates, `L_{n−1}` the set of those with at least `P − m`.
(0) `Hⁿ(L_{n−1}) = 0`: `L_{n−1}` lies in the countably many coordinate planes
`A(t, z) = {x : xᵢ = zᵢ, i ∈ t}`, `P ≤ m + |t|`, each the Lipschitz image of a space of dimension
`P − |t| < m + 1`.
(1) `L_n` is a finite union of finite intersections of the closed sets `{x : xᵢ ∈ ℤ}`.
(2) The faces `F_p` meeting the bounded set `K` have bounded integer corners, so they are finitely
many, and (3) by `diam F_p ≤ √P` they lie in the closed `√P`-neighbourhood of `K`.
(4) A point `x ∈ (L_n ∩ K) \ L_{n−1}` has exactly `n` non-integer coordinates; with `ι` their
increasing enumeration and `y` their fractional parts, `x = Φ_{(⌊x⌋, ι)}(y)`, `y ∈ Q₁`, and
`(⌊x⌋, ι)` is a face meeting `K`.  (5) By (0) this covers `Hⁿ`-a.e. point of `L_n ∩ K`. -/
theorem Submission.dor_lmb_fcd_fr_skeleton_cells : ∀ (P m : ℕ) (K : Set (Euclid P)), m + 1 < P → IsCompact K → ∃ s : Finset ((Fin P → ℤ) × (Fin (m + 1) → Fin P)), (∀ p ∈ s, StrictMono p.2) ∧ (∀ p ∈ s, {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧ (i ∉ Set.range p.2 → x i = p.1 i)} ⊆ cthickening (Real.sqrt P) K) ∧ IsClosed {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∧ ∀ᵐ x ∂(μHE[m + 1].restrict ({x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧ ∀ i ∈ t, ∃ z : ℤ, x i = z} ∩ K)), ∃ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.1 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x := by
  intro P m K hmP hK
  -- Step 0: `Hⁿ(L_{n−1}) = 0`, i.e. the points with at least `P − m` integer coordinates are
  -- `μHE[m + 1]`-null
  have hnull : μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
    -- each coordinate plane `A(s, z)` with `P ≤ m + |s|` is `μH[m + 1]`-null
    have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
        μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
      intro s hs z
      -- `A(s, z)` is the image of the Lipschitz map `g : t ↦ (zᵢ on s, tᵢ off s)`
      let g : ({i // i ∉ s} → ℝ) → Euclid P := fun t =>
        WithLp.toLp 2 fun i => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩
      have hg1 : LipschitzWith 1 fun t : {i // i ∉ s} → ℝ =>
          fun i : Fin P => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩ := by
        refine LipschitzWith.of_dist_le_mul fun t t' => ?_
        rw [NNReal.coe_one, one_mul]
        refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
        by_cases h : i ∈ s
        · simp [h]
        · simpa [h] using dist_le_pi_dist t t' ⟨i, h⟩
      have hg : LipschitzWith _ g := (PiLp.lipschitzWith_toLp 2 fun _ : Fin P => ℝ).comp hg1
      have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ g '' univ := by
        intro x hx
        refine ⟨fun j => x j.1, mem_univ _, ?_⟩
        ext i
        by_cases h : i ∈ s
        · simp [g, h, hx i h]
        · simp [g, h]
      -- the source of `g` has dimension `P − |s| ≤ m < m + 1`, so it is `μH[m + 1]`-null
      have hcard : Fintype.card {i // i ∉ s} ≤ m := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
        omega
      have huniv : (μH[((m + 1 : ℕ) : ℝ)] : Measure ({i // i ∉ s} → ℝ)) univ = 0 := by
        rw [← Metric.iUnion_ball_nat (0 : {i // i ∉ s} → ℝ)]
        refine measure_iUnion_null fun n => ?_
        refine (Measure.hausdorffMeasure_zero_or_top
          (d₁ := (Fintype.card {i // i ∉ s} : ℝ)) ?_ _).resolve_right ?_
        · exact_mod_cast Nat.lt_succ_of_le hcard
        · rw [hausdorffMeasure_pi_real]
          exact measure_ball_lt_top.ne
      refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
      calc μH[((m + 1 : ℕ) : ℝ)] (g '' univ)
          ≤ _ ^ ((m + 1 : ℕ) : ℝ) * μH[((m + 1 : ℕ) : ℝ)] (univ : Set ({i // i ∉ s} → ℝ)) :=
            hg.hausdorffMeasure_image_le (Nat.cast_nonneg _) univ
        _ = 0 := by rw [huniv, mul_zero]
    -- the set is covered by the countably many planes `A(s, z)`, `P ≤ m + |s|`, `z ∈ ℤᴾ`
    have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆ ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card})
          (z : Fin P → ℤ), {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
      rintro x ⟨s, hs, hx⟩
      choose! z hz using hx
      exact mem_iUnion₂.2 ⟨⟨s, hs⟩, z, hz⟩
    -- countable subadditivity gives `μH[m + 1]`-nullity, and `μHE[m + 1] = c • μH[m + 1]`
    have hnullH : μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
        ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 :=
      measure_mono_null hcover
        (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hnullH, smul_zero]
  -- Step 1: `L_n` is closed, a finite union of finite intersections of the closed sets
  -- `{x : xᵢ ∈ ℤ}`
  have hLclosed : IsClosed {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧
      ∀ i ∈ t, ∃ z : ℤ, x i = z} := by
    have hcoord : ∀ i : Fin P, IsClosed {x : Euclid P | ∃ z : ℤ, x i = z} := by
      intro i
      have h : {x : Euclid P | ∃ z : ℤ, x i = z} =
          (fun x : Euclid P => x i) ⁻¹' range ((↑) : ℤ → ℝ) := by
        ext x
        exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
      rw [h]
      exact Int.isClosedEmbedding_coe_real.isClosed_range.preimage (by fun_prop)
    have h : {x : Euclid P | ∃ t : Finset (Fin P), P ≤ m + 1 + t.card ∧
        ∀ i ∈ t, ∃ z : ℤ, x i = z} = ⋃ (t : Finset (Fin P)) (_ : P ≤ m + 1 + t.card),
          ⋂ i ∈ t, {x : Euclid P | ∃ z : ℤ, x i = z} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
    rw [h]
    exact isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
      isClosed_iInter fun i => isClosed_iInter fun _ => hcoord i
  classical
  -- Step 2: the faces `F_p` meeting `K ⊆ B̄_R(0)` have corners with `|zᵢ| ≤ ⌈R⌉ + 1`, so they
  -- form a finite set
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hKcoord : ∀ x ∈ K, ∀ i : Fin P, |x i| ≤ R := fun x hx i =>
    (Real.norm_eq_abs (x i)).symm.le.trans ((PiLp.norm_apply_le x i).trans (hR x hx))
  let faces : Set ((Fin P → ℤ) × (Fin (m + 1) → Fin P)) := {p | StrictMono p.2 ∧ ∃ k ∈ K,
    k ∈ {x : Euclid P | ∀ i : Fin P, (i ∈ Set.range p.2 → (p.1 i : ℝ) ≤ x i ∧ x i ≤ p.1 i + 1) ∧
      (i ∉ Set.range p.2 → x i = p.1 i)}}
  have hfin : faces.Finite := by
    refine ((Set.Finite.pi (t := fun _ : Fin P => Set.Icc (-(⌈R⌉ + 1)) (⌈R⌉ + 1))
      fun _ => Set.finite_Icc _ _).prod (Set.finite_univ (α := Fin (m + 1) → Fin P))).subset ?_
    rintro p ⟨-, k, hkK, hkF⟩
    have hceil := Int.le_ceil R
    refine ⟨fun i _ => ?_, mem_univ _⟩
    -- `zᵢ ≤ xᵢ ≤ R` and `zᵢ ≥ xᵢ − 1 ≥ −R − 1` for `x ∈ F_p ∩ K`
    obtain ⟨hk₁, hk₂⟩ := abs_le.1 (hKcoord k hkK i)
    have hzb : (p.1 i : ℝ) ≤ R ∧ -R - 1 ≤ (p.1 i : ℝ) := by
      by_cases hi : i ∈ Set.range p.2
      · obtain ⟨h₁, h₂⟩ := (hkF i).1 hi
        constructor <;> linarith
      · have h := (hkF i).2 hi
        constructor <;> linarith
    have h₁ : ((-(⌈R⌉ + 1) : ℤ) : ℝ) ≤ p.1 i := by
      push_cast
      linarith [hzb.2]
    have h₂ : (p.1 i : ℝ) ≤ ((⌈R⌉ + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [hzb.1]
    exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  refine ⟨hfin.toFinset, fun p hp => (hfin.mem_toFinset.1 hp).1, fun p hp => ?_, hLclosed, ?_⟩
  · -- Step 3: `diam F_p ≤ √P` and `F_p ∩ K ≠ ∅` give `F_p ⊆ cthickening √P K`
    obtain ⟨hp2, k, hkK, hkF⟩ := hfin.mem_toFinset.1 hp
    obtain ⟨-, -, -, -, -, -, hdiam, -, -⟩ := Submission.dor_lmb_fcd_fr_face_geometry P m p hp2
    exact fun x hx => mem_cthickening_of_dist_le x k _ K hkK (hdiam x hx k hkF)
  · -- Steps 4–5: off the null set `L_{n−1}` (step 0), every `x ∈ L_n ∩ K` is `Φ_p(y)` for a face
    -- `p` meeting `K` and some `y ∈ Q₁`
    rw [ae_restrict_iff' (hLclosed.inter hK.isClosed).measurableSet]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hxL' hx
    obtain ⟨⟨t, ht, hxt⟩, hxK⟩ := hx
    -- `T` the integer and `S` the non-integer coordinates of `x`: `|T| = P − n`, `|S| = n`
    set T : Finset (Fin P) := Finset.univ.filter fun i => ∃ z : ℤ, x i = z with hT
    set S : Finset (Fin P) := Finset.univ.filter fun i => ¬ ∃ z : ℤ, x i = z with hS
    have hTS : T.card + S.card = P := by
      rw [hT, hS, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
    have htT : t.card ≤ T.card := Finset.card_le_card fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ i, hxt i hi⟩
    have hT' : ¬ P ≤ m + T.card := fun h =>
      hxL' ⟨T, h, fun i hi => (Finset.mem_filter.1 hi).2⟩
    have hScard : S.card = m + 1 := by omega
    -- `ι` enumerates `S` increasingly, `z = ⌊x⌋`, and `y` collects the fractional parts
    let ι := S.orderEmbOfFin hScard
    have hιS : Set.range ι = S := Finset.range_orderEmbOfFin S hScard
    let y : Euclid (m + 1) := WithLp.toLp 2 fun k => Int.fract (x (ι k))
    have hy : ∀ k, 0 < y k ∧ y k < 1 := by
      intro k
      have hk : ι k ∈ S := Finset.orderEmbOfFin_mem S hScard k
      rw [hS, Finset.mem_filter] at hk
      exact ⟨Int.fract_pos.2 fun h => hk.2 ⟨_, h⟩, Int.fract_lt_one _⟩
    have hΦ : WithLp.toLp 2 (fun i => ((⌊x i⌋ : ℤ) : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) = x := by
      ext i
      rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
      simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i ∈ S
      · -- `i = ι(j₀)`: the coordinate is `⌊xᵢ⌋ + fract xᵢ = xᵢ`
        obtain ⟨j₀, rfl⟩ : i ∈ Set.range ι := by rw [hιS]; exact hi
        rw [Fintype.sum_eq_single j₀, ite_eq_left rfl]
        · exact Int.floor_add_fract _
        · intro j hj
          exact ite_eq_right (ι.injective.ne hj.symm)
      · -- `i ∉ range ι`: the coordinate is `⌊xᵢ⌋ = xᵢ ∈ ℤ`
        obtain ⟨z, hz⟩ : ∃ z : ℤ, x i = z := by
          by_contra h
          exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
        have h0 : ∀ j, (if i = ι j then y j else 0) = 0 := fun j =>
          ite_eq_right fun h => hi (by rw [h]; exact Finset.orderEmbOfFin_mem S hScard j)
        simp only [h0, Finset.sum_const_zero, add_zero, hz, Int.floor_intCast]
    -- `x = Φ_p(y) ∈ F_p ∩ K` for `p = (⌊x⌋, ι)`, so `p` is one of the faces
    let p : (Fin P → ℤ) × (Fin (m + 1) → Fin P) := (fun i => ⌊x i⌋, ι)
    have hΦp : WithLp.toLp 2 (fun i => (p.1 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.2 j) (1 : ℝ) = x := hΦ
    have hp : p ∈ faces := by
      refine ⟨ι.strictMono, x, hxK, ?_⟩
      obtain ⟨-, -, -, -, hcube, -, -, -, -⟩ :=
        Submission.dor_lmb_fcd_fr_face_geometry P m p ι.strictMono
      have h := hcube y fun k => ⟨(hy k).1.le, (hy k).2.le⟩
      rwa [hΦp] at h
    exact ⟨p, hfin.mem_toFinset.2 hp, y, hy, hΦp⟩
/-- **Unit orientations of the approximate tangent plane of a set in a coordinate plane** (Simon
Ch. 6, proof of 5.1, (26)–(27)).  Let `A ⊆ x + V`, `V = span{e_{ι j}}`, have approximate tangent
space `Q` at `x`, and let `ξ` orient `Q`.  The blow-ups `λ⁻¹(A − x)` lie in `V`, so every test
function vanishing on `V` has zero limit integral `∫_Q f dHⁿ`; since `Q` is the support of `Hⁿ⌞Q`,
this forces `Q ⊆ V`.  The orthonormal frame `τ` of `Q` then satisfies `τₖ = Σⱼ Mⱼₖ e_{ι j}` with
`MᵀM = 1`, so `α(τ) = det M · α(e_ι)` with `det M = ±1` for every `n`-covector `α`. -/
theorem Submission.dor_lmb_fcd_fr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  -- Step 1: every `q ∈ Q` has `qᵢ = 0` for `i ∉ range ι`
  have hQV : ∀ q ∈ Q, ∀ i, (∀ j, ι j ≠ i) → q i = 0 := by
    intro q hq i hi
    by_contra hqi
    have hc : 0 < |q i| := abs_pos.2 hqi
    -- the test function `g w = max 0 (|qᵢ| - |w - q|)`: positive near `q`, zero where `wᵢ = 0`
    let g : Euclid P → ℝ := fun w => max 0 (|q i| - dist w q)
    have hgc : Continuous g := by fun_prop
    have hgs : HasCompactSupport g := by
      refine HasCompactSupport.intro (isCompact_closedBall q |q i|) fun w hw => ?_
      rw [mem_closedBall, not_le] at hw
      exact max_eq_left (by linarith)
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := g
        continuous_toFun := hgc
        hasCompactSupport' := hgs }
    have hfg : ∀ w, f w = g w := fun _ => rfl
    have hg0 : ∀ w : Euclid P, w i = 0 → g w = 0 := by
      intro w hw
      have h1 : |q i| ≤ dist w q := by
        have h2 := PiLp.norm_apply_le (w - q) i
        rw [dist_eq_norm]
        simpa [hw] using h2
      exact max_eq_left (by linarith)
    -- the integrals over the blow-ups `λ⁻¹(A - x) ⊆ {wᵢ = 0}` vanish, so `∫_Q f dHⁿ = 0`
    have hlim : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] = 0 := by
      refine tendsto_nhds_unique (hQ.2 f) (tendsto_const_nhds.congr fun r => ?_)
      refine (setIntegral_eq_zero_of_forall_eq_zero ?_).symm
      rintro _ ⟨a, ha, rfl⟩
      rw [hfg]
      apply hg0
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, hA a ha i hi]
    -- but `q` lies in the support `Q` of `Hⁿ⌞Q` and `f > 0` near `q`, so `∫_Q f dHⁿ > 0`
    have hpos : 0 < ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
      have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
      have hf0 : (0 : Euclid P → ℝ) ≤ ⇑f := fun w => by rw [hfg]; exact le_max_left _ _
      rw [integral_pos_iff_support_of_nonneg hf0 f.integrable]
      have hq' : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
        rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
        exact hq
      refine (Measure.mem_support_iff_forall q).1 hq' _ ?_
      refine Filter.mem_of_superset (ball_mem_nhds q hc) fun w hw => ?_
      rw [mem_ball] at hw
      rw [Function.mem_support, hfg]
      exact (lt_max_of_lt_right (by linarith)).ne'
    linarith
  -- Step 2: the frame `τ` lies in `V = span{e_ι}`
  have hτV : ∀ k i, (∀ j, ι j ≠ i) → τ k i = 0 := fun k i hi =>
    hQV (τ k) (by rw [← hτQ]; exact Submodule.subset_span (mem_range_self k)) i hi
  -- coordinates `m k = (τ k (ι j))ⱼ` of `τ k` in the frame `e_ι`, and `L w = Σⱼ wⱼ e_{ι j}`
  let m : Fin n → Fin n → ℝ := fun k j => τ k (ι j)
  let L : (Fin n → ℝ) →ₗ[ℝ] Euclid P :=
    Fintype.linearCombination ℝ fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have hLm : ∀ k, L (m k) = τ k := by
    intro k
    refine PiLp.ext fun i => ?_
    simp only [L, m, Fintype.linearCombination_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, PiLp.single_apply, mul_ite, mul_one, mul_zero]
    by_cases h : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := h
      simp [hι.injective.eq_iff]
    · have h' : ∀ j, ι j ≠ i := fun j hj => h ⟨j, hj⟩
      rw [hτV k i h']
      exact Finset.sum_eq_zero fun j _ => ite_eq_right (h' j).symm
  have hLe : ∀ k, L (Pi.basisFun ℝ (Fin n) k) = EuclideanSpace.single (ι k) (1 : ℝ) := by
    intro k
    rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]
  -- Step 3: `M = (τ k (ι j))` is orthogonal, so `det M = ±1`
  let M : Matrix (Fin n) (Fin n) ℝ := (Pi.basisFun ℝ (Fin n)).toMatrix m
  have hMM : M.transpose * M = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.1 hτ k l, PiLp.inner_apply]
    simp only [Matrix.transpose_apply, M, Module.Basis.toMatrix_apply, Pi.basisFun_repr, m]
    refine Fintype.sum_of_injective ι hι.injective _ _ ?_ fun j => ?_
    · rintro i hi
      rw [hτV k i fun j hj => hi ⟨j, hj⟩]
      simp
    · simp [mul_comm]
  have hdet : M.det = 1 ∨ M.det = -1 := by
    have h := congrArg Matrix.det hMM
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
    exact mul_self_eq_one_iff.1 h
  -- Step 4: `α(τ) = det M · α(e_ι)` for every `n`-covector `α`
  have hα : ∀ α : Covector (Euclid P) n,
      α τ = M.det * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    intro α
    have key := DFunLike.congr_fun
      (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin n)) (α.toAlternatingMap.compLinearMap L)) m
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul,
      ContinuousAlternatingMap.coe_toAlternatingMap, hLm, hLe, Module.Basis.det_apply] at key
    rw [mul_comm] at key
    exact key
  rcases hξτ with h | h <;> rcases hdet with hd | hd
  · exact Or.inl fun α => by rw [h, hα, hd, one_mul]
  · exact Or.inr fun α => by rw [h, hα, hd, neg_one_mul]
  · exact Or.inr fun α => by rw [h, hα, hd, one_mul]
  · exact Or.inl fun α => by rw [h, hα, hd, neg_one_mul, neg_neg]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
