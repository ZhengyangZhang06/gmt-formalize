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

/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
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
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm

/-- **Chart lemma** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ` be a chart of `N` as in
`IsEmbeddedSubmanifold`: `Cʳ` (`r ≥ 1`) and injective on the open `V`, `ψ(V) = W ∩ N`, proper,
with `Dψ` injective on `V`.  For `v ∈ V`, `q = ψ(v)` and `A = Dψ(v)`: (i) `T_qN = A(ℝᵈ)`;
(ii) `ψ⁻¹` is continuous at `q`; (iii) every `y ∈ N` near `q` has `|y − q − Aa| ≤ ε|y − q|` for
some `a`.  (ii) is `dsmc_chart_inverse_continuity` (properness and injectivity), (iii) is
`dsmc_chart_secant_estimate` (differentiability at `v`, injectivity of `A` and (ii)), and (i)
combines `dsmc_tangentSpace_subset_range_of_secant` (by (iii), curve velocities lie in the closed
subspace `A(ℝᵈ)`) with `dsmc_chart_range_subset_tangentSpace` (the curves `t ↦ ψ(v + h(t)a)`). -/
theorem Submission.dsmc_chart_tangentSpace_eq_range : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → ∀ v ∈ V, tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - fderiv ℝ ψ v a‖ ≤ ε * ‖y - ψ v‖) := by
  intro P r d N V W ψ hr hV hW hψ hinj himg hprop hDψ v hv
  -- (ii): properness and injectivity of `ψ` on `V` make `ψ⁻¹` continuous at `ψ v`
  have hii : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε :=
    Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj
      (himg.subset.trans inter_subset_left) hprop v hv
  -- `ψ` is `C¹` on the open set `V ∋ v`, so `A = fderiv ℝ ψ v` is its derivative at `v`
  have hA : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    (hψ.differentiableOn (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr)).hasFDerivAt
      (hV.mem_nhds hv)
  -- (iii): the secant estimate at `ψ v`, from `hA`, injectivity of `A` and (ii)
  have hiii := Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW himg hv hA
    (hDψ v hv) hii
  -- (i): `T_{ψ v}N ⊆ A(ℝᵈ)` by (iii); `A(ℝᵈ) ⊆ T_{ψ v}N` since `ψ '' V ⊆ N`
  exact ⟨Set.Subset.antisymm
      (Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v) hiii)
      (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ
        (himg.subset.trans inter_subset_right) v hv),
    hii, hiii⟩
/-- **Simon Ch. 2, (4.18)–(4.20)** (tangential divergence in an orthonormal frame): if `τ₁, …, τₙ`
is an orthonormal basis of `Q`, then `trace(p_Q ∘ B) = Σₐ τₐ · Bτₐ`.  The orthogonality
characterization of the projection gives `p_Q z = Σₐ (τₐ · z) τₐ`, so `p_Q ∘ B` is the sum of the
rank-one maps `z ↦ (τₐ · Bz) τₐ`, and the trace of `z ↦ ℓ(z) v` is `ℓ(v)`. -/
theorem Submission.fvmb_trace_starProjection_comp_eq_sum_inner : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (τ : Fin n → Euclid P) (B : Euclid P →L[ℝ] Euclid P), Orthonormal ℝ τ → Submodule.span ℝ (Set.range τ) = Q → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ B.toLinearMap) = ∑ a, inner ℝ (τ a) (B (τ a)) := by
  intro P n Q τ B hτ hQ
  -- `p_Q z = Σₐ ⟪τₐ, z⟫ τₐ`: the right side lies in `Q` and `z` minus it is orthogonal to `Q`
  have hproj : ∀ z : Euclid P, Q.starProjection z = ∑ a, inner ℝ (τ a) z • τ a := by
    intro z
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [← hQ]
      exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · intro q hq
      rw [← hQ] at hq
      induction hq using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        rw [inner_sub_left, hτ.inner_left_fintype, real_inner_comm]
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [inner_smul_right, hx, mul_zero]
  -- `p_Q ∘ B = Σₐ (z ↦ ⟪τₐ, Bz⟫ τₐ)`
  have hdecomp : Q.starProjection.toLinearMap ∘ₗ B.toLinearMap =
      ∑ a, ((innerₛₗ ℝ (τ a)) ∘ₗ B.toLinearMap).smulRight (τ a) := by
    ext z
    simp [hproj]
  -- `trace (z ↦ ℓ(z) v) = ℓ(v)` (`LinearMap.trace_smulRight`), summed over `a`
  rw [hdecomp, map_sum]
  simp
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)
/-- **Injective area formula with the Gram-determinant Jacobian** (Simon Ch. 2, (3.3) and (3.5)).
For `f : ℝᵐ → ℝᴾ` let `Jf(x) = √det(⟨Df(x)eₖ, Df(x)eₗ⟩)`, `eₖ` the standard basis of `ℝᵐ`.  Then
(i) `Jf` is Borel; (ii) if `s` is Borel, `f` is differentiable with injective `Df(x)` at every
`x ∈ s` and `f` is injective on `s`, every `g ≥ 0` has `∫_{f(s)} g dHᵐ = ∫_s Jf(x) g(f(x)) dx`.
Write `G L = √det(⟨L eₖ, L eₗ⟩)` for linear `L : ℝᵐ → ℝᴾ`.  For injective `L`, `L = ι ∘ B` with
`ι` an isometry of `ℝᵐ` onto `range L` and `B` invertible, so `G L = |det B|` and
`Hᵐ(L(S)) = G L · |S|` (linear area formula).  `f` is cut into countably many Borel pieces on which
it is uniformly close to an injective linear map (`exists_partition_approximatesLinearOn_…`);
Lipschitz comparison bounds `Hᵐ(f(piece))` against the linear model, and at almost every point of
a piece `Df` is close to the model, so `G ∘ Df` is close to its value; letting the relative error
tend to `1` gives `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`, and the weighted formula follows by
transporting `Jf · volume` along the measurable embedding `f|s`.  (Adapted from Mathlib's
`MeasureTheory.Function.Jacobian` and SimonGMT Chapter 2 §3.) -/
theorem Submission.codim1_lura_gram_area_formula : ∀ (m P : ℕ) (f : Euclid m → Euclid P), Measurable (fun x => Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) ∧ ∀ s : Set (Euclid m), MeasurableSet s → (∀ x ∈ s, DifferentiableAt ℝ f x) → (∀ x ∈ s, Injective (fderiv ℝ f x)) → InjOn f s → ∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in f '' s, g y ∂μHE[m] = ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ f x (EuclideanSpace.single k 1)) (fderiv ℝ f x (EuclideanSpace.single l 1))))) * g (f x) ∂volume := by
  intro m P f
  -- `G L = √det(⟨L eₖ, L eₗ⟩)`, the Gram-determinant Jacobian of a linear `L : ℝᵐ → ℝᴾ`
  obtain ⟨G, hG⟩ : ∃ G : (Euclid m →L[ℝ] Euclid P) → ℝ, ∀ L, G L = Real.sqrt (Matrix.det
      (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
    ⟨_, fun L => rfl⟩
  simp only [← hG]
  -- `G` is continuous (polynomial in the entries, then `√`)
  have hGc : Continuous G := by
    have hGfun : G = fun L : Euclid m →L[ℝ] Euclid P => Real.sqrt (Matrix.det
        (Matrix.of fun k l : Fin m => inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) :=
      funext hG
    rw [hGfun]
    refine Real.continuous_sqrt.comp (Continuous.matrix_det ?_)
    refine continuous_pi fun k => continuous_pi fun l => ?_
    exact (continuous_id.clm_apply continuous_const).inner (continuous_id.clm_apply continuous_const)
  -- linear area formula: for injective `L`, `G L > 0` and `Hᵐ(L(S)) = G L · |S|`.  Write
  -- `L = ι ∘ B`, `ι : ℝᵐ → range L` an isometry, `B` invertible; Gram(L) = Gram(B) = BᵀB.
  have hlin : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → 0 < G L ∧
      ∀ S : Set (Euclid m), μHE[m] (L '' S) = ENNReal.ofReal (G L) * volume S := by
    intro L hL
    rw [hG]
    have hVdim : Module.finrank ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) = m := by
      rw [LinearMap.finrank_range_of_inj hL, finrank_euclideanSpace_fin]
    let φ := ((stdOrthonormalBasis ℝ (LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P))).reindex
      (finCongr hVdim)).repr
    let B : Euclid m →ₗ[ℝ] Euclid m :=
      φ.toLinearEquiv.toLinearMap ∘ₗ (L : Euclid m →ₗ[ℝ] Euclid P).rangeRestrict
    have hLB : ∀ x, L x =
        ((φ.symm (B x) : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P) := by
      intro x
      simp only [B, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.symm_apply_apply,
        LinearMap.codRestrict_apply, LinearMap.rangeRestrict]
      rfl
    have hι : Isometry (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) :=
      isometry_subtype_coe.comp φ.symm.isometry
    have hinner : ∀ k l : Fin m,
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)) =
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1)) := by
      intro k l
      rw [hLB, hLB, ← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
    have hdet : Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.det B) ^ 2 := by
      have hM : (Matrix.of fun k l : Fin m =>
          inner ℝ (B (EuclideanSpace.single k 1)) (B (EuclideanSpace.single l 1))) =
          (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B).transpose *
          LinearMap.toMatrix (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin m) ℝ).toBasis B := by
        ext k l
        simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
          LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr,
          EuclideanSpace.basisFun_apply, PiLp.inner_apply, Real.inner_apply]
      rw [hM, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix, sq]
    have hBinj : Injective B := by
      intro x y hxy
      apply hL
      rw [hLB, hLB, hxy]
    have hdetne : LinearMap.det B ≠ 0 := by
      have hu : IsUnit B :=
        (Module.End.isUnit_iff B).mpr ⟨hBinj, LinearMap.surjective_of_injective hBinj⟩
      exact ((LinearMap.isUnit_iff_isUnit_det B).mp hu).ne_zero
    have hGB : Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m =>
        inner ℝ (L (EuclideanSpace.single k 1)) (L (EuclideanSpace.single l 1)))) =
          |LinearMap.det B| := by
      simp_rw [hinner]
      rw [hdet, Real.sqrt_sq_eq_abs]
    refine ⟨by rw [hGB]; exact abs_pos.mpr hdetne, fun S => ?_⟩
    have himage : L '' S = (fun y : Euclid m =>
        ((φ.symm y : LinearMap.range (L : Euclid m →ₗ[ℝ] Euclid P)) : Euclid P)) '' (B '' S) := by
      rw [Set.image_image]
      exact Set.image_congr (fun x _ => hLB x)
    rw [himage, hι.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume, Measure.addHaar_image_linearMap, hGB]
  -- distance comparison `dist (φ x) (φ y) ≤ K dist (ψ x) (ψ y)` gives `Hᵐ(φ S) ≤ Kᵐ Hᵐ(ψ S)`
  have hdist : ∀ (φ ψ : Euclid m → Euclid P) (S : Set (Euclid m)) (K : NNReal), InjOn ψ S →
      (∀ x ∈ S, ∀ y ∈ S, dist (φ x) (φ y) ≤ K * dist (ψ x) (ψ y)) →
      μHE[m] (φ '' S) ≤ (K : ℝ≥0∞) ^ m * μHE[m] (ψ '' S) := by
    intro φ ψ S K hψ hφψ
    have hh : LipschitzOnWith K (φ ∘ invFunOn ψ S) (ψ '' S) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hψ.leftInvOn_invFunOn hx, hψ.leftInvOn_invFunOn hy] using
        hφψ x hx y hy
    have himage : (φ ∘ invFunOn ψ S) '' (ψ '' S) = φ '' S := by
      rw [image_comp, hψ.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn m hh
  -- near an injective `L`, one radius `δ` controls both `G` and images of `δ`-approximations of `L`
  have hrad : ∀ L : Euclid m →L[ℝ] Euclid P, Injective L → ∀ q : NNReal, 1 < q →
      ∃ δ : NNReal, 0 < δ ∧
        (∀ B : Euclid m →L[ℝ] Euclid P, ‖B - L‖ ≤ δ →
          ENNReal.ofReal (G B) ≤ q * ENNReal.ofReal (G L) ∧
            ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G B)) ∧
        (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
          μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
            ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t)) := by
    intro L hL q hq
    obtain ⟨hGpos, hLarea⟩ := hlin L hL
    obtain ⟨K, -, hK⟩ := (L : Euclid m →ₗ[ℝ] Euclid P).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hL)
    have hmul : G L < (q : ℝ) * G L := lt_mul_of_one_lt_left hGpos hq
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      ((hGc.continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul hGc.continuousAt) hmul))
    have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0, 0 < δ ∧ δ * K < 1 ∧ (1 + δ * K) ^ m < q ∧
        ((1 - δ * K)⁻¹) ^ m < q ∧ (δ : ℝ) < ε := by
      have h1 : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
        (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
      have h2 : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ m < q :=
        ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
          continuousAt_const (by simpa using hq)
      have h3 : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ m < q := by
        apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
        apply ContinuousAt.pow
        apply ContinuousAt.inv₀
        · exact continuousAt_const.sub (continuousAt_id.mul continuousAt_const)
        · simp
      have h4 : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
        (NNReal.continuous_coe.continuousAt).eventually_lt continuousAt_const (by simpa using hε)
      filter_upwards [self_mem_nhdsWithin, h1.filter_mono nhdsWithin_le_nhds,
        h2.filter_mono nhdsWithin_le_nhds, h3.filter_mono nhdsWithin_le_nhds,
        h4.filter_mono nhdsWithin_le_nhds] with δ hδ h1 h2 h3 h4
      exact ⟨hδ, h1, h2, h3, h4⟩
    obtain ⟨δ, hδ, hδK, hδupper, hδlower, hδε⟩ := hevent.exists
    refine ⟨δ, hδ, fun B hB => ?_, fun t φ hφ => ?_⟩
    · obtain ⟨hupper, hlower⟩ :=
        hnear (show dist B L < ε by rw [dist_eq_norm]; exact hB.trans_lt hδε)
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal hupper.le, ENNReal.ofReal_le_ofReal hlower.le⟩
    · have hb : ∀ x y, ‖x - y‖ ≤ K * ‖L x - L y‖ := fun x y => by
        simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
      have herr : ∀ x ∈ t, ∀ y ∈ t, ‖φ x - φ y - (L x - L y)‖ ≤ (δ : ℝ) * K * ‖L x - L y‖ :=
        fun x hx y hy => by
          calc ‖φ x - φ y - (L x - L y)‖ ≤ δ * ‖x - y‖ := by
                simpa only [map_sub] using hφ x hx y hy
            _ ≤ δ * (K * ‖L x - L y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
            _ = (δ : ℝ) * K * ‖L x - L y‖ := by ring
      have hδR : (δ : ℝ) * K < 1 := hδK
      have hdLφ : ∀ x ∈ t, ∀ y ∈ t,
          dist (L x) (L y) ≤ ((1 - δ * K)⁻¹ : NNReal) * dist (φ x) (φ y) := by
        intro x hx y hy
        have htri : ‖L x - L y‖ ≤ ‖φ x - φ y‖ + ‖φ x - φ y - (L x - L y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L x - L y) (φ x - φ y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδK.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith [herr x hx y hy, norm_nonneg (L x - L y)]
      constructor
      · refine (hdist φ L t (1 + δ * K) hL.injOn fun x hx y hy => ?_).trans ?_
        · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
          calc ‖φ x - φ y‖ ≤ ‖φ x - φ y - (L x - L y)‖ + ‖L x - L y‖ := norm_le_norm_sub_add _ _
            _ ≤ (δ : ℝ) * K * ‖L x - L y‖ + ‖L x - L y‖ := add_le_add (herr x hx y hy) le_rfl
            _ = (1 + (δ : ℝ) * K) * ‖L x - L y‖ := by ring
        · rw [hLarea]
          gcongr
          exact_mod_cast hδupper.le
      · have hφinj : InjOn φ t := fun x hx y hy hxy => hL (dist_le_zero.mp (by
          simpa only [hxy, dist_self, mul_zero] using hdLφ x hx y hy))
        rw [← hLarea]
        refine (hdist L φ t _ hφinj hdLφ).trans ?_
        gcongr
        exact_mod_cast hδlower.le
  -- on a `δ`-approximation piece, `‖Df(x) - A‖ ≤ δ` at almost every point (density points);
  -- this is Mathlib's `ApproximatesLinearOn.norm_fderiv_sub_le`, whose proof is codomain-free
  have hae : ∀ (t : Set (Euclid m)) (A : Euclid m →L[ℝ] Euclid P) (δ : NNReal),
      ApproximatesLinearOn f A t δ → MeasurableSet t →
      (∀ x ∈ t, HasFDerivWithinAt f (fderiv ℝ f x) t x) →
      ∀ᵐ x ∂(volume.restrict t), ‖fderiv ℝ f x - A‖₊ ≤ δ := by
    open scoped Pointwise in
    intro t A δ hf ht hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div volume t, ae_restrict_mem ht]
    intro x hx xt
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε →
        ‖(fderiv ℝ f x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖fderiv ℝ f x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      apply le_of_tendsto_of_tendsto tendsto_const_nhds this
      filter_upwards [self_mem_nhdsWithin]
      exact H
    intro ε εpos
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (t ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume t x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ : ∃ ρ > 0,
        ball x ρ ∩ t ⊆ {y : Euclid m | ‖f y - f x - (fderiv ℝ f x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.1 (hf' x xt).isLittleO εpos)
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
      apply nhdsWithin_le_nhds
      exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
    obtain ⟨r, ⟨y, ⟨yt, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (t ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(fderiv ℝ f x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(fderiv ℝ f x - A) a‖ = ‖(fderiv ℝ f x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (fderiv ℝ f x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
              Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (fderiv ℝ f x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ yt _ xt) (hρ ⟨rρ hy, yt⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(fderiv ℝ f x - A) z‖ = ‖(fderiv ℝ f x - A) a + (fderiv ℝ f x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(fderiv ℝ f x - A) a‖ + ‖(fderiv ℝ f x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖fderiv ℝ f x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- (i) `Jf = G ∘ Df` is Borel
  refine ⟨hGc.measurable.comp (measurable_fderiv ℝ f), ?_⟩
  intro s hs hf hreg hinj g
  -- unweighted area formula `Hᵐ(f(B)) = ∫_B Jf` for Borel `B ⊆ s`: compare piecewise up to `q²`
  have harea : ∀ B : Set (Euclid m), MeasurableSet B → B ⊆ s →
      μHE[m] (f '' B) = ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) := by
    intro B hB hBs
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[m] (f '' B) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) ≤ (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' B) := by
      intro q hq
      rcases eq_empty_or_nonempty B with rfl | hBne
      · simp
      have hchoice : ∀ L : Euclid m →L[ℝ] Euclid P, ∃ δ : NNReal, 0 < δ ∧ (Injective L →
          (∀ L' : Euclid m →L[ℝ] Euclid P, ‖L' - L‖ ≤ δ →
            ENNReal.ofReal (G L') ≤ q * ENNReal.ofReal (G L) ∧
              ENNReal.ofReal (G L) ≤ q * ENNReal.ofReal (G L')) ∧
          (∀ (t : Set (Euclid m)) (φ : Euclid m → Euclid P), ApproximatesLinearOn φ L t δ →
            μHE[m] (φ '' t) ≤ q * (ENNReal.ofReal (G L) * volume t) ∧
              ENNReal.ofReal (G L) * volume t ≤ q * μHE[m] (φ '' t))) := by
        intro L
        by_cases hL : Injective L
        · obtain ⟨δ, hδ, hJ, hLa⟩ := hrad L hL q hq
          exact ⟨δ, hδ, fun _ => ⟨hJ, hLa⟩⟩
        · exact ⟨1, zero_lt_one, fun h => (hL h).elim⟩
      choose δ hδpos hδ using hchoice
      have hfB : ∀ x ∈ B, HasFDerivWithinAt f (fderiv ℝ f x) B x :=
        fun x hx => (hf x (hBs hx)).hasFDerivAt.hasFDerivWithinAt
      obtain ⟨t, L, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B (fderiv ℝ f) hfB
          δ (fun L => (hδpos L).ne')
      have hLreg : ∀ i, Injective (L i) := by
        intro i
        obtain ⟨x, hx, hL⟩ := hactual hBne i
        rw [hL]
        exact hreg x (hBs hx)
      have hseq : B = ⋃ i, B ∩ t i := by
        rw [← inter_iUnion]
        exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
      have hsumimage : μHE[m] (f '' B) = ∑' i, μHE[m] (f '' (B ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        apply measure_iUnion
        · intro i j hij
          exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
            (hinj.mono hBs) inter_subset_left inter_subset_left
        · intro i
          apply (hB.inter (ht i)).image_of_continuousOn_injOn
          · exact fun x hx => (hf x (hBs hx.1)).continuousAt.continuousWithinAt
          · exact (hinj.mono hBs).mono inter_subset_left
      have hsumintegral : (∫⁻ x in B, ENNReal.ofReal (G (fderiv ℝ f x))) =
          ∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hB.inter (ht i))
          (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
      have hpiece : ∀ i, μHE[m] (f '' (B ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) ∧
          (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by
        intro i
        have hJ := (hδ (L i) (hLreg i)).1
        obtain ⟨harea_upper, harea_lower⟩ := (hδ (L i) (hLreg i)).2 (B ∩ t i) f (happrox i)
        have hderiv := hae (B ∩ t i) (L i) (δ (L i)) (happrox i) (hB.inter (ht i))
          (fun x hx => (hfB x hx.1).mono inter_subset_left)
        have hJupper : (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) ≤
            q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
          calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ ∫⁻ _ in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (L i)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).1
            _ = q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := by
                rw [setLIntegral_const, mul_assoc]
        have hJlower : ENNReal.ofReal (G (L i)) * volume (B ∩ t i) ≤
            q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
          calc ENNReal.ofReal (G (L i)) * volume (B ∩ t i)
              = ∫⁻ _ in B ∩ t i, ENNReal.ofReal (G (L i)) := (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in B ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (G (fderiv ℝ f x)) := by
                apply lintegral_mono_ae
                filter_upwards [hderiv] with x hx
                exact (hJ (fderiv ℝ f x) hx).2
            _ = q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
                lintegral_const_mul' _ _ ENNReal.coe_ne_top
        constructor
        · calc μHE[m] (f '' (B ∩ t i)) ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) :=
                harea_upper
            _ ≤ q * (q * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) := by
                rw [pow_two, mul_assoc]
        · calc (∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
              ≤ q * (ENNReal.ofReal (G (L i)) * volume (B ∩ t i)) := hJupper
            _ ≤ q * (q * μHE[m] (f '' (B ∩ t i))) := by gcongr
            _ = (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) := by rw [pow_two, mul_assoc]
      rw [hsumimage, hsumintegral]
      constructor
      · calc (∑' i, μHE[m] (f '' (B ∩ t i)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
          _ = _ := ENNReal.tsum_mul_left
      · calc (∑' i, ∫⁻ x in B ∩ t i, ENNReal.ofReal (G (fderiv ℝ f x)))
            ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[m] (f '' (B ∩ t i)) :=
              ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
          _ = _ := ENNReal.tsum_mul_left
    have hlimit : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    apply le_antisymm
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).1
    · apply ge_of_tendsto (hlimit _)
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact (hcomp q hq).2
  -- (ii) transport `Jf · volume` on `s` along the measurable embedding `f|s` onto `Hᵐ⌞f(s)`
  have hcont : ContinuousOn f s := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hemb := hcont.measurableEmbedding hs hinj
  have hsub := MeasurableEmbedding.subtype_coe hs
  have hmap : Measure.map (s.domRestrict f)
      ((volume.withDensity (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap
        (Subtype.val : s → Euclid m)) = μHE[m].restrict (f '' s) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply]
    have hB : MeasurableSet (Subtype.val '' ((s.domRestrict f) ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    have hBs : Subtype.val '' ((s.domRestrict f) ⁻¹' t) ⊆ s := by
      rintro x ⟨u, _, rfl⟩
      exact u.property
    rw [withDensity_apply _ hB, ← harea _ hB hBs, Measure.restrict_apply ht]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, ⟨u, u.property, rfl⟩⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  rw [← hmap, hemb.lintegral_map]
  change (∫⁻ x : s, (fun x : Euclid m => g (f x)) x ∂((volume.withDensity
    (fun x => ENNReal.ofReal (G (fderiv ℝ f x)))).comap (Subtype.val : s → Euclid m))) = _
  rw [lintegral_subtype_comap hs (fun x : Euclid m => g (f x)),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · simp only [eventually_true, ENNReal.ofReal_lt_top]
  · exact (hGc.measurable.comp (measurable_fderiv ℝ f)).ennreal_ofReal.aemeasurable
/-- **Gram-determinant chain rule along an orthonormal frame** (the Jacobian chain rule of the area
formula, used for Simon 7.5.8).  Let `Λ : ℝᵐ → ℝᵈ` be linear and `eₖ` the standard basis of `ℝᵐ`.
(i) If `Λ` is injective, `det[⟨Λeₖ, Λeₗ⟩] > 0`.  (ii) If `σ` is an orthonormal frame spanning
`range Λ` and `Γ : ℝᵈ → ℝᴾ` is linear, `det[⟨ΓΛeₖ, ΓΛeₗ⟩] = det[⟨Γσᵢ, Γσⱼ⟩] · det[⟨Λeₖ, Λeₗ⟩]`.
Writing `Λeₗ = ∑ₐ Rₐₗ σₐ` (`Rₐₗ = ⟨σₐ, Λeₗ⟩`), `[⟨GΛeₖ, GΛeₗ⟩] = Rᵀ[⟨Gσₐ, Gσ_b⟩]R` for every
linear `G`; take `G = Γ` and `G = id`.  For (i), let `σ` be an orthonormal basis of `range Λ` (of
dimension `m`): then `det[⟨Λeₖ, Λeₗ⟩] = (det R)²`, and `R` is invertible as `Λ` is injective. -/
theorem Submission.codim1_lura_gram_det_comp_orthonormal : ∀ (m d P : ℕ) (Λ : Euclid m →L[ℝ] Euclid d), (Injective Λ → 0 < Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1)) (Λ (EuclideanSpace.single l 1)))) ∧ ∀ (Γ : Euclid d →L[ℝ] Euclid P) (σ : Fin m → Euclid d), Orthonormal ℝ σ → Submodule.span ℝ (Set.range σ) = LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) → Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Γ (Λ (EuclideanSpace.single k 1))) (Γ (Λ (EuclideanSpace.single l 1)))) = Matrix.det (Matrix.of fun i j : Fin m => inner ℝ (Γ (σ i)) (Γ (σ j))) * Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1)) (Λ (EuclideanSpace.single l 1))) := by
  intro m d P Λ
  -- for an orthonormal frame `σ` of `range Λ`: `Λeₗ = ∑ₐ Rₐₗ σₐ`,
  -- `[⟨GΛeₖ, GΛeₗ⟩] = Rᵀ[⟨Gσₐ, Gσ_b⟩]R` and `det[⟨Λeₖ, Λeₗ⟩] = (det R)²` (`[⟨σₐ, σ_b⟩] = 1`)
  have frame : ∀ σ : Fin m → Euclid d, Orthonormal ℝ σ →
      Submodule.span ℝ (Set.range σ) = LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) →
      ∃ R : Matrix (Fin m) (Fin m) ℝ, (∀ l, Λ (EuclideanSpace.single l 1) = ∑ a, R a l • σ a) ∧
        (∀ (Q : ℕ) (G : Euclid d →L[ℝ] Euclid Q),
          (Matrix.of fun k l : Fin m => inner ℝ (G (Λ (EuclideanSpace.single k 1)))
            (G (Λ (EuclideanSpace.single l 1)))) =
            R.transpose * (Matrix.of fun a b : Fin m => inner ℝ (G (σ a)) (G (σ b))) * R) ∧
        Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (Λ (EuclideanSpace.single k 1))
          (Λ (EuclideanSpace.single l 1))) = R.det * R.det := by
    intro σ hσ hspan
    obtain ⟨R, hR⟩ : ∃ R : Matrix (Fin m) (Fin m) ℝ,
        ∀ l, Λ (EuclideanSpace.single l 1) = ∑ a, R a l • σ a := by
      refine ⟨Matrix.of fun a l => inner ℝ (σ a) (Λ (EuclideanSpace.single l 1)), fun l => ?_⟩
      have hl : Λ (EuclideanSpace.single l 1) ∈ Submodule.span ℝ (Set.range σ) :=
        hspan ▸ LinearMap.mem_range_self (Λ : Euclid m →ₗ[ℝ] Euclid d) _
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hl
      simp only [Matrix.of_apply]
      rw [← hc]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hσ.inner_right_fintype]
    have key : ∀ (Q : ℕ) (G : Euclid d →L[ℝ] Euclid Q),
        (Matrix.of fun k l : Fin m => inner ℝ (G (Λ (EuclideanSpace.single k 1)))
          (G (Λ (EuclideanSpace.single l 1)))) =
          R.transpose * (Matrix.of fun a b : Fin m => inner ℝ (G (σ a)) (G (σ b))) * R := by
      intro Q G
      ext k l
      rw [Matrix.of_apply, hR k, hR l]
      simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
        real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    refine ⟨R, hR, key, ?_⟩
    have hone : (Matrix.of fun a b : Fin m => inner ℝ (σ a) (σ b)) = 1 := by
      ext a b
      rw [Matrix.of_apply, orthonormal_iff_ite.mp hσ a b, Matrix.one_apply]
    have h := key d (ContinuousLinearMap.id ℝ (Euclid d))
    simp only [ContinuousLinearMap.id_apply] at h
    rw [h, hone, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose]
  refine ⟨fun hΛ => ?_, fun Γ σ hσ hspan => ?_⟩
  · -- (i): `σ` an orthonormal basis of `range Λ`, of dimension `m`; if `Rv = 0` then
    -- `Λ(∑ₗ vₗeₗ) = ∑ₐ (Rv)ₐσₐ = 0`, so `v = 0`: `det R ≠ 0`
    set W := LinearMap.range (Λ : Euclid m →ₗ[ℝ] Euclid d) with hW
    have hdim : Module.finrank ℝ W = m := by
      rw [hW, LinearMap.finrank_range_of_inj hΛ, finrank_euclideanSpace_fin]
    set b : OrthonormalBasis (Fin m) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
    have hσ : Orthonormal ℝ (fun a => (b a : Euclid d)) :=
      b.orthonormal.comp_linearIsometry W.subtypeₗᵢ
    have hspan : Submodule.span ℝ (Set.range fun a => (b a : Euclid d)) = W := by
      rw [show (fun a => (b a : Euclid d)) = W.subtype ∘ b from rfl, Set.range_comp,
        Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    obtain ⟨R, hR, -, hdet⟩ := frame _ hσ hspan
    rw [hdet]
    refine mul_self_pos.mpr fun h0 => ?_
    obtain ⟨v, hv, hRv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hv
    have hsum : Λ (∑ l, v l • EuclideanSpace.single l 1) = 0 := by
      simp only [map_sum, map_smul, hR, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul]
      refine Finset.sum_eq_zero fun a _ => ?_
      have ha : ∑ l, v l * R a l = 0 := by
        simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hRv a
      rw [ha, zero_smul]
    have hzero := hΛ (hsum.trans (map_zero Λ).symm)
    funext l
    exact Fintype.linearIndependent_iff.mp
      (EuclideanSpace.orthonormal_single (ι := Fin m) (𝕜 := ℝ)).linearIndependent v hzero l
  · -- (ii): `det(RᵀHR) = det R · det H · det R` with `H = [⟨Γσₐ, Γσ_b⟩]`
    obtain ⟨R, -, key, hdet⟩ := frame σ hσ hspan
    rw [key P Γ, hdet, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring

/-- **Gram determinant of a restricted adjoint square** (the Jacobian notation of the area
formula, Simon Ch. 2, 4.11–4.13).  Let `T ⊆ ℝᴾ` be a subspace with the induced inner product,
`B : ℝᴾ → ℝᴾ` linear and `σ` an orthonormal frame spanning `T`.  Then
`det((B ∘ ι_T)*(B ∘ ι_T)) = det[⟨Bσᵢ, Bσⱼ⟩]`.  Viewed in `T`, `σ` is orthonormal, and it spans
`T` since `dim T = k`, so it is an orthonormal basis `b` of `T`.  In `b` the matrix of
`(B ∘ ι_T)*(B ∘ ι_T)` has entries `⟨bᵢ, (B ∘ ι_T)*(B ∘ ι_T) bⱼ⟩ = ⟨Bσᵢ, Bσⱼ⟩` (adjoint). -/
theorem Submission.codim1_hcp_af_adjoint_det_eq_gram : ∀ (P k : ℕ) (T : Submodule ℝ (Euclid P)) (B : Euclid P →L[ℝ] Euclid P) (σ : Fin k → Euclid P), Orthonormal ℝ σ → Submodule.span ℝ (Set.range σ) = T → ((B.comp T.subtypeL).adjoint ∘L (B.comp T.subtypeL)).det = Matrix.det (Matrix.of fun i j : Fin k => inner ℝ (B (σ i)) (B (σ j))) := by
  intro P k T B σ hσ hT
  -- each `σ i` lies in `T`, and `σ`, viewed in `T`, is orthonormal
  have hσT : ∀ i, σ i ∈ T := fun i => hT ▸ Submodule.subset_span (mem_range_self i)
  have hb : Orthonormal ℝ fun i => (⟨σ i, hσT i⟩ : T) := hσ.codRestrict T hσT
  -- `dim T = k`, so this family spans `T` and is an orthonormal basis `b` of `T`
  have hk : Fintype.card (Fin k) = Module.finrank ℝ T := by
    rw [← hT, finrank_span_eq_card hσ.linearIndependent]
  obtain ⟨b, hbσ⟩ : ∃ b : OrthonormalBasis (Fin k) ℝ T, ∀ i, (b i : Euclid P) = σ i :=
    ⟨OrthonormalBasis.mk hb (hb.linearIndependent.span_eq_top_of_card_eq_finrank' hk).ge,
      fun i => by simp only [OrthonormalBasis.coe_mk]⟩
  -- the determinant is that of the matrix in `b`, whose `(i, j)` entry is
  -- `⟪b i, (B ∘ ι_T)† ((B ∘ ι_T) (b j))⟫ = ⟪B (σ i), B (σ j)⟫`
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [ContinuousLinearMap.comp_apply, Submodule.coe_subtypeL, Submodule.subtype_apply, hbσ,
    Matrix.of_apply]
/-- **Countable chart partition** (Simon Ch. 2, §4, (4.1), as used for the area formula on a
submanifold, 4.11–4.13).  Let `M ⊂ ℝᴾ` be an embedded `m`-dimensional `C¹` submanifold and `E ⊆ M`
Borel.  Each `y ∈ M` has a chart `ψ_y : V_y → W_y` as in (4.1) with `y ∈ W_y` (each `y ∉ M` gets
the empty chart), and by Lindelöf countably many `W_{y_k}` already cover `M`.  The pieces
`E_k = (E ∩ W_{y_k}) \ ⋃_{j<k} (E ∩ W_{y_j})` are Borel, pairwise disjoint, have union `E`, and
`E_k ⊆ W_{y_k} ∩ M`. -/
theorem Submission.codim1_hcp_af_chart_partition : ∀ (P m : ℕ) (M E : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → MeasurableSet E → E ⊆ M → ∃ (Es : ℕ → Set (Euclid P)) (Vs : ℕ → Set (Euclid m)) (Ws : ℕ → Set (Euclid P)) (ψs : ℕ → Euclid m → Euclid P), (∀ k, MeasurableSet (Es k)) ∧ Pairwise (fun i j => Disjoint (Es i) (Es j)) ∧ (⋃ k, Es k) = E ∧ ∀ k, IsOpen (Vs k) ∧ IsOpen (Ws k) ∧ ContDiffOn ℝ 1 (ψs k) (Vs k) ∧ InjOn (ψs k) (Vs k) ∧ ψs k '' Vs k = Ws k ∩ M ∧ (∀ K ⊆ Ws k, IsCompact K → IsCompact (Vs k ∩ ψs k ⁻¹' K)) ∧ (∀ z ∈ Vs k, Injective (fderiv ℝ (ψs k) z)) ∧ Es k ⊆ Ws k ∩ M := by
  intro P m M E hM hE hEM
  -- every `y` has a chart `(V_y, W_y, ψ_y)` satisfying (4.1), with `y ∈ W_y` if `y ∈ M`
  -- (for `y ∉ M` the empty chart `(∅, ∅, 0)`)
  have hchart : ∀ y : Euclid P, ∃ (V : Set (Euclid m)) (W : Set (Euclid P))
      (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧
        ψ '' V = W ∩ M ∧ (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
        (∀ z ∈ V, Injective (fderiv ℝ ψ z)) ∧ (y ∈ M → y ∈ W) := by
    intro y
    by_cases hy : y ∈ M
    · obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hD⟩ := hM y hy
      exact ⟨V, W, ψ, hV, hW, by exact_mod_cast hψ, hinj, himg, hprop, hD, fun _ => hyW⟩
    · exact ⟨∅, ∅, 0, isOpen_empty, isOpen_empty, contDiffOn_empty, injOn_empty _, by simp,
        by simp, by simp, fun h => absurd h hy⟩
  choose V W ψ hV hW hψ hinj himg hprop hD hyW using hchart
  -- Lindelöf: countably many `W_y`, `y ∈ T`, have the same union `⋃_y W_y ⊇ M`
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  -- enumerate `T ⊆ {y_0, y_1, …}`, so that `M ⊆ ⋃_k W_{y_k}`
  obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1 hTc
  have hcover : M ⊆ ⋃ k, W (f k) := by
    intro y hy
    have hyT : y ∈ ⋃ i ∈ T, W i := by
      rw [hTU]
      exact mem_iUnion.2 ⟨y, hyW y hy⟩
    obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 hyT
    obtain ⟨k, rfl⟩ := hf hiT
    exact mem_iUnion.2 ⟨k, hyi⟩
  -- the pieces `E_k = (E ∩ W_{y_k}) \ ⋃_{j<k} (E ∩ W_{y_j})` and the charts at `y_k`
  refine ⟨disjointed fun k => E ∩ W (f k), fun k => V (f k), fun k => W (f k),
    fun k => ψ (f k), MeasurableSet.disjointed fun k => hE.inter (hW (f k)).measurableSet,
    disjoint_disjointed _, ?_, fun k => ⟨hV (f k), hW (f k), hψ (f k), hinj (f k), himg (f k),
      hprop (f k), hD (f k), fun x hx => ?_⟩⟩
  -- `⋃_k E_k = ⋃_k (E ∩ W_{y_k}) = E ∩ ⋃_k W_{y_k} = E`, as `E ⊆ M ⊆ ⋃_k W_{y_k}`
  · rw [iUnion_disjointed, ← inter_iUnion]
    exact inter_eq_left.2 (hEM.trans hcover)
  -- `E_k ⊆ E ∩ W_{y_k} ⊆ W_{y_k} ∩ M`
  · have hx' := disjointed_subset _ k hx
    exact ⟨hx'.2, hEM hx'.1⟩

/-- **Jacobian factorization at a chart point** (Simon Ch. 2, 4.11 with §4, (4.3)).  Let
`ψ : V → W` be a local representation of `M` as in (4.1), `v ∈ V`, `Λ = Dψ(v)`,
`T = span T_{ψ(v)}M` and `B : ℝᴾ → ℝᴾ` linear.  Then
`√det[⟨BΛeₖ, BΛeₗ⟩] = √det[⟨Λeₖ, Λeₗ⟩] · √det((B ∘ ι_T)* (B ∘ ι_T))`.  By (4.3),
`T_{ψ(v)}M = Λ(ℝᵐ)`, so `T = range Λ`, of dimension `m` as `Λ` is injective.  For an orthonormal
frame `σ` of `range Λ`, `det[⟨BΛeₖ, BΛeₗ⟩] = det[⟨Bσᵢ, Bσⱼ⟩] · det[⟨Λeₖ, Λeₗ⟩]` with
`det[⟨Λeₖ, Λeₗ⟩] > 0`, and `det[⟨Bσᵢ, Bσⱼ⟩] = det((B ∘ ι_T)* (B ∘ ι_T))`; take square roots. -/
theorem Submission.codim1_hcp_af_chart_jacobian_factor : ∀ (P m : ℕ) (M W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (B : Euclid P →L[ℝ] Euclid P) (v : Euclid m), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (B (fderiv ℝ ψ v (EuclideanSpace.single k 1))) (B (fderiv ℝ ψ v (EuclideanSpace.single l 1))))) = Real.sqrt (Matrix.det (Matrix.of fun k l : Fin m => inner ℝ (fderiv ℝ ψ v (EuclideanSpace.single k 1)) (fderiv ℝ ψ v (EuclideanSpace.single l 1)))) * Real.sqrt (((B.comp (Submodule.span ℝ (tangentSpace M (ψ v))).subtypeL).adjoint ∘L (B.comp (Submodule.span ℝ (tangentSpace M (ψ v))).subtypeL)).det) := by
  intro P m M W V ψ B v hV hW hψ hinj hψV hproper hDψ hv
  -- `T_{ψ(v)}M = range Λ`, hence `T = span (range Λ) = range Λ`
  set L := LinearMap.range (fderiv ℝ ψ v : Euclid m →ₗ[ℝ] Euclid P) with hL
  have hT : Submodule.span ℝ (tangentSpace M (ψ v)) = L := by
    rw [Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W V ψ v le_rfl hV hW
      (by exact_mod_cast hψ) hinj hψV hproper hDψ hv]
    exact Submodule.span_eq L
  -- `Λ` is injective, so `range Λ` has dimension `m`; `σ` is an orthonormal frame of `range Λ`
  have hdim : Module.finrank ℝ L = m := by
    rw [hL, LinearMap.finrank_range_of_inj (hDψ v hv), finrank_euclideanSpace_fin]
  set b : OrthonormalBasis (Fin m) ℝ L := (stdOrthonormalBasis ℝ L).reindex (finCongr hdim)
  have hσ : Orthonormal ℝ (fun a => (b a : Euclid P)) :=
    b.orthonormal.comp_linearIsometry L.subtypeₗᵢ
  have hspan : Submodule.span ℝ (Set.range fun a => (b a : Euclid P)) = L := by
    rw [show (fun a => (b a : Euclid P)) = L.subtype ∘ b from rfl, Set.range_comp,
      Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  -- `det[⟨BΛeₖ, BΛeₗ⟩] = det[⟨Bσᵢ, Bσⱼ⟩] · det[⟨Λeₖ, Λeₗ⟩]` with `det[⟨Λeₖ, Λeₗ⟩] > 0`,
  -- and `det[⟨Bσᵢ, Bσⱼ⟩] = det((B ∘ ι_T)* (B ∘ ι_T))`
  obtain ⟨hpos, hchain⟩ :=
    Submission.codim1_lura_gram_det_comp_orthonormal m P P (fderiv ℝ ψ v)
  rw [hchain B _ hσ hspan,
    Submission.codim1_hcp_af_adjoint_det_eq_gram P m _ B _ hσ (hspan.trans hT.symm),
    Real.sqrt_mul' _ (hpos (hDψ v hv)).le]
  exact mul_comm _ _

/-- **Area formula on a Borel subset of one chart** (Simon Ch. 2, 4.11–4.13).  Let `(V, W, ψ)` be
a chart of `M` as in (4.1), `E ⊆ W ∩ M` Borel, and `Φ : ℝᴾ → ℝᴾ` a `C¹` map, injective on `E`,
with `DΦ(x)` injective for `x ∈ E`.  With `ι` the inclusion of `span T_xM` and
`J^MΦ(x) = √det((DΦ(x) ∘ ι)*(DΦ(x) ∘ ι))`, `Hᵐ(Φ(E)) = ∫_E J^MΦ dHᵐ`.  The coordinate piece
`F = V ∩ ψ⁻¹(E)` is Borel with `ψ(F) = E`.  The Euclidean area formula for `Φ ∘ ψ` (weight `1`)
and for `ψ` (weight `J^MΦ`) turns both sides into integrals over `F`, and the integrands agree:
`J_{Φ∘ψ} = J_ψ · (J^MΦ ∘ ψ)` by the chain rule and the chart Jacobian factorization. -/
theorem Submission.codim1_hcp_af_chart_area_formula : ∀ (P m : ℕ) (M E W : Set (Euclid P)) (V : Set (Euclid m)) (ψ : Euclid m → Euclid P) (Φ : Euclid P → Euclid P), IsOpen V → IsOpen W → ContDiffOn ℝ 1 ψ V → InjOn ψ V → ψ '' V = W ∩ M → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → MeasurableSet E → E ⊆ W ∩ M → ContDiff ℝ 1 Φ → InjOn Φ E → (∀ x ∈ E, Injective (fderiv ℝ Φ x)) → μHE[m] (Φ '' E) = ∫⁻ x in E, ENNReal.ofReal (Real.sqrt ((((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L ((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ∂μHE[m] := by
  classical
  intro P m M E W V ψ Φ hV hW hψ hinj hψV hproper hDψ hE hEWM hΦ hΦinj hDΦ
  -- Step 1: `F = V ∩ ψ⁻¹(E)` is Borel: on the open set `V`, `ψ` agrees with the Borel map equal
  -- to `ψ` on `V` and to `0` off `V`
  have hF : MeasurableSet (V ∩ ψ ⁻¹' E) := by
    have hψm : Measurable (V.piecewise ψ fun _ => (0 : Euclid P)) :=
      hψ.continuousOn.measurable_piecewise continuousOn_const hV.measurableSet
    have hFeq : V ∩ ψ ⁻¹' E = V ∩ V.piecewise ψ (fun _ => (0 : Euclid P)) ⁻¹' E := by
      ext v
      simp only [mem_inter_iff, mem_preimage]
      exact and_congr_right fun hv => by rw [piecewise_eq_of_mem _ _ _ hv]
    rw [hFeq]
    exact hV.measurableSet.inter (hψm hE)
  -- Step 2: `ψ(F) = E`, as `E ⊆ W ∩ M = ψ(V)`; hence `(Φ ∘ ψ)(F) = Φ(E)`
  have hψF : ψ '' (V ∩ ψ ⁻¹' E) = E := by
    refine Subset.antisymm (image_subset_iff.2 inter_subset_right) fun x hx => ?_
    obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := hψV ▸ hEWM hx
    exact ⟨v, ⟨hv, hx⟩, rfl⟩
  have hΦψF : (Φ ∘ ψ) '' (V ∩ ψ ⁻¹' E) = Φ '' E := by rw [image_comp, hψF]
  -- Step 3: `ψ` is differentiable on the open set `V`, `Φ` everywhere, and
  -- `D(Φ ∘ ψ)(v) = DΦ(ψ(v)) ∘ Dψ(v)` (chain rule)
  have hψd : ∀ v ∈ V, DifferentiableAt ℝ ψ v := fun v hv =>
    (hψ.differentiableOn one_ne_zero v hv).differentiableAt (hV.mem_nhds hv)
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable one_ne_zero
  have hchain : ∀ v ∈ V, fderiv ℝ (Φ ∘ ψ) v = (fderiv ℝ Φ (ψ v)).comp (fderiv ℝ ψ v) :=
    fun v hv => fderiv_comp v (hΦd (ψ v)) (hψd v hv)
  -- Step 4: on `F`, `ψ` and `Φ ∘ ψ` are injective with injective derivatives
  have hinjF : InjOn ψ (V ∩ ψ ⁻¹' E) := hinj.mono inter_subset_left
  have hΦψinjF : InjOn (Φ ∘ ψ) (V ∩ ψ ⁻¹' E) := fun v hv w hw hvw =>
    hinjF hv hw (hΦinj hv.2 hw.2 hvw)
  have hDΦψ : ∀ v ∈ V ∩ ψ ⁻¹' E, Injective (fderiv ℝ (Φ ∘ ψ) v) := fun v hv => by
    rw [hchain v hv.1, ContinuousLinearMap.coe_comp]
    exact (hDΦ (ψ v) hv.2).comp (hDψ v hv.1)
  -- Step 5: the area formula for `Φ ∘ ψ` on `F` with weight `1`: `Hᵐ(Φ(E)) = ∫_F J_{Φ∘ψ}`
  have h5 := (Submission.codim1_lura_gram_area_formula m P (Φ ∘ ψ)).2 (V ∩ ψ ⁻¹' E) hF
    (fun v hv => (hΦd (ψ v)).comp v (hψd v hv.1)) hDΦψ hΦψinjF fun _ => 1
  rw [hΦψF, setLIntegral_one] at h5
  -- Step 6: the area formula for `ψ` on `F` with weight `J^MΦ`:
  -- `∫_E J^MΦ dHᵐ = ∫_F J_ψ · (J^MΦ ∘ ψ)`
  have h6 := (Submission.codim1_lura_gram_area_formula m P ψ).2 (V ∩ ψ ⁻¹' E) hF
    (fun v hv => hψd v hv.1) (fun v hv => hDψ v hv.1) hinjF fun x => ENNReal.ofReal
      (Real.sqrt ((((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L
        ((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det))
  rw [hψF] at h6
  rw [h5, h6]
  -- Steps 7–8: `J_{Φ∘ψ}(v) = J_ψ(v) · J^MΦ(ψ(v))` on `F` (chart Jacobian with `B = DΦ(ψ(v))`)
  refine setLIntegral_congr_fun hF fun v hv => ?_
  simp only [mul_one, hchain v hv.1, ContinuousLinearMap.comp_apply]
  rw [Submission.codim1_hcp_af_chart_jacobian_factor P m M W V ψ (fderiv ℝ Φ (ψ v)) v hV hW hψ
    hinj hψV hproper hDψ hv.1, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
/-- An embedded `Cʳ` submanifold `M ⊆ ℝᴾ` (Simon Ch. 2, §4, (4.1)) is Borel, and it meets every
small closed ball about one of its points in a compact set.  For a chart `(V, W, ψ)` and a compact
`K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact because `ψ` is proper and continuous on `V`.  With `O`
the union of the chart domains `W`, `M = O ∩ closure M`: a point `p ∈ O ∩ closure M` lies in the
closure of the compact, hence closed, set `M ∩ closedBall p ε`.  So `M` is Borel. -/
theorem Submission.dimred_rpd_embedded_locally_closed : ∀ (P r d : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → MeasurableSet M ∧ ∀ y ∈ M, ∃ ε : ℝ, 0 < ε ∧ IsCompact (M ∩ closedBall y ε) := by
  intro P r d M hM
  -- step 1: for a chart `(V, W, ψ)` at `y` and compact `K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
      ∀ K ⊆ W, IsCompact K → IsCompact (M ∩ K) := by
    intro y hy
    obtain ⟨V, W, ψ, -, hW, hyW, hψ, -, himg, hprop, -⟩ := hM y hy
    refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
    have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨hxM, hxK⟩
        have hx : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, ⟨hv, hxK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have hv' : ψ v ∈ W ∩ M := by rw [← himg]; exact ⟨v, hv, rfl⟩
        exact ⟨hv'.2, hvK⟩
    rw [hEq]
    exact (hprop K hKW hK).image_of_continuousOn (hψ.continuousOn.mono inter_subset_left)
  refine ⟨?_, ?_⟩
  · -- steps 3-5: `O = ⋃_{y ∈ M} W_y` is open and `M = O ∩ closure M`, so `M` is Borel
    choose! Wf hWo hyW hcpt using key
    have hO : IsOpen (⋃ y ∈ M, Wf y) := isOpen_biUnion fun y hy => hWo y hy
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · -- `p ∈ O ∩ closure M` lies in the closure of the compact set `M ∩ closedBall p (r'/2)`
        rintro p ⟨hpO, hpcl⟩
        obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
        obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
        have hcb : closedBall p (r' / 2) ⊆ Wf y :=
          (closedBall_subset_ball (by linarith)).trans hball
        have hC := hcpt y hy (closedBall p (r' / 2)) hcb (isCompact_closedBall p (r' / 2))
        have h1 : p ∈ ball p (r' / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
        have h2 := isOpen_ball.inter_closure h1
        have hsub : ball p (r' / 2) ∩ M ⊆ M ∩ closedBall p (r' / 2) :=
          fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
        have h3 : p ∈ closure (M ∩ closedBall p (r' / 2)) := closure_mono hsub h2
        rw [hC.isClosed.closure_eq] at h3
        exact h3.1
    rw [hMeq]
    exact hO.measurableSet.inter isClosed_closure.measurableSet
  · -- step 2: a closed ball about `y` inside the chart domain `W` meets `M` in a compact set
    intro y hy
    obtain ⟨W, hW, hyW, hcpt⟩ := key y hy
    obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 hW y hyW
    exact ⟨r' / 2, by linarith,
      hcpt _ ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall y _)⟩
/-- **Simon Ch. 2, §5** (frame trace bound for a first-order perturbation of the identity): if
`‖B‖ ≤ A`, `‖L − I − tB‖ ≤ η|t|` with `η ≤ 1`, and `τ₁, …, τₙ` is orthonormal in `ℝᴾ`, then
(i) `|Σₐ τₐ · Bτₐ| ≤ nA` and (ii) `Σₐ |Lτₐ|² − n ≤ 2t Σₐ τₐ · Bτₐ + 2nη|t| + n(A + 1)²t²`.
With `E = L − I − tB` and `wₐ = tBτₐ + Eτₐ` we have `Lτₐ = τₐ + wₐ`, `|wₐ| ≤ (A + 1)|t|` and
`τₐ · Eτₐ ≤ η|t|`; expand `|τₐ + wₐ|² = 1 + 2t τₐ · Bτₐ + 2 τₐ · Eτₐ + |wₐ|²` and sum over `a`. -/
theorem Submission.fvmb_perturbed_frame_sum_norm_sq_sub_le : ∀ (P n : ℕ) (A η t : ℝ) (B L : Euclid P →L[ℝ] Euclid P) (τ : Fin n → Euclid P), η ≤ 1 → ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → Orthonormal ℝ τ → |∑ a, inner ℝ (τ a) (B (τ a))| ≤ (n : ℝ) * A ∧ ∑ a, ‖L (τ a)‖ ^ 2 - (n : ℝ) ≤ 2 * t * (∑ a, inner ℝ (τ a) (B (τ a))) + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by
  intro P n A η t B L τ hη hB hE hτ
  -- `E = L − I − tB`, so `‖E‖ ≤ η|t|`
  set E : Euclid P →L[ℝ] Euclid P := L - ContinuousLinearMap.id ℝ (Euclid P) - t • B with hEdef
  have hτ1 : ∀ a, ‖τ a‖ = 1 := hτ.1
  -- unit vectors: `|Bτₐ| ≤ A`, `|Eτₐ| ≤ η|t|` and `|τₐ · Bτₐ| ≤ A`
  have hBa : ∀ a, ‖B (τ a)‖ ≤ A := fun a =>
    calc ‖B (τ a)‖ ≤ ‖B‖ * ‖τ a‖ := B.le_opNorm _
      _ = ‖B‖ := by rw [hτ1 a, mul_one]
      _ ≤ A := hB
  have hEa : ∀ a, ‖E (τ a)‖ ≤ η * |t| := fun a =>
    calc ‖E (τ a)‖ ≤ ‖E‖ * ‖τ a‖ := E.le_opNorm _
      _ = ‖E‖ := by rw [hτ1 a, mul_one]
      _ ≤ η * |t| := hE
  have hDa : ∀ a, |inner ℝ (τ a) (B (τ a))| ≤ A := fun a =>
    calc |inner ℝ (τ a) (B (τ a))| ≤ ‖τ a‖ * ‖B (τ a)‖ := abs_real_inner_le_norm _ _
      _ = ‖B (τ a)‖ := by rw [hτ1 a, one_mul]
      _ ≤ A := hBa a
  refine ⟨?_, ?_⟩
  · calc |∑ a, inner ℝ (τ a) (B (τ a))| ≤ ∑ a, |inner ℝ (τ a) (B (τ a))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, A := Finset.sum_le_sum fun a _ => hDa a
      _ = (n : ℝ) * A := by rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  · -- one column: `|Lτₐ|² = |τₐ + wₐ|²` with `wₐ = tBτₐ + Eτₐ`
    have hcol : ∀ a, ‖L (τ a)‖ ^ 2 ≤
        1 + 2 * t * inner ℝ (τ a) (B (τ a)) + 2 * η * |t| + (A + 1) ^ 2 * t ^ 2 := by
      intro a
      have hL : L (τ a) = τ a + (t • B (τ a) + E (τ a)) := by
        simp only [hEdef, sub_apply, smul_apply, ContinuousLinearMap.id_apply]
        abel
      have hw : ‖t • B (τ a) + E (τ a)‖ ≤ (A + 1) * |t| :=
        calc ‖t • B (τ a) + E (τ a)‖ ≤ ‖t • B (τ a)‖ + ‖E (τ a)‖ := norm_add_le _ _
          _ = |t| * ‖B (τ a)‖ + ‖E (τ a)‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ ≤ |t| * A + η * |t| :=
              add_le_add (mul_le_mul_of_nonneg_left (hBa a) (abs_nonneg t)) (hEa a)
          _ ≤ |t| * A + 1 * |t| := by gcongr
          _ = (A + 1) * |t| := by ring
      have hwsq : ‖t • B (τ a) + E (τ a)‖ ^ 2 ≤ (A + 1) ^ 2 * t ^ 2 :=
        calc ‖t • B (τ a) + E (τ a)‖ ^ 2 ≤ ((A + 1) * |t|) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hw 2
          _ = (A + 1) ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
      have hcross : inner ℝ (τ a) (E (τ a)) ≤ η * |t| :=
        calc inner ℝ (τ a) (E (τ a)) ≤ ‖τ a‖ * ‖E (τ a)‖ := real_inner_le_norm _ _
          _ = ‖E (τ a)‖ := by rw [hτ1 a, one_mul]
          _ ≤ η * |t| := hEa a
      rw [hL, norm_add_sq_real, hτ1 a, inner_add_right, real_inner_smul_right]
      linarith
    calc ∑ a, ‖L (τ a)‖ ^ 2 - (n : ℝ)
        ≤ ∑ a, (1 + 2 * t * inner ℝ (τ a) (B (τ a)) + 2 * η * |t| + (A + 1) ^ 2 * t ^ 2) -
            (n : ℝ) := by
          gcongr with a
          exact hcol a
      _ = 2 * t * (∑ a, inner ℝ (τ a) (B (τ a))) + 2 * (n : ℝ) * η * |t| +
            (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.sum_const, Finset.sum_const, ← Finset.mul_sum,
            Finset.card_fin, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
          ring
/-- **Simon Ch. 2, §5** (the expansion `J_t = 1 + t div_M X + O(t²)` behind the first variation
formula 5.3), scalar one-sided step: given `n`, `A ≥ 0`, `ε > 0` there are `0 < η ≤ 1` and
`δ > 0` such that `|t| < δ`, `|D| ≤ nA` and `g ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)` imply
`√g ≤ 1 + tD + ε|t|`.  With `σ = tD + nη|t| + n(A + 1)²t²/2` the hypothesis gives
`√g ≤ √(e^σ e^σ) = e^σ`; `|σ| ≤ c₀|t| ≤ 1` for `c₀ = (n + 1)(A + 2 + (A + 1)²)`, so
`e^σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + Kt²` with `K = n(A + 1)²/2 + c₀²`.  Take
`η = min(1, ε/(2n + 1))` (so `nη ≤ ε/2`) and `δ = min(1, 1/c₀, ε/(2K))` (so `Kt² ≤ (ε/2)|t|`). -/
theorem Submission.fvmb_sqrt_le_first_order_of_le_exp : ∀ (n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t D g : ℝ, |t| < δ → |D| ≤ (n : ℝ) * A → g ≤ Real.exp (2 * t * D + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2) → Real.sqrt g ≤ 1 + t * D + ε * |t| := by
  intro n A ε hA hε
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Step 1: the constants `c₀`, `K`, `η`, `δ`
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ((n : ℝ) + 1) * (A + 2 + (A + 1) ^ 2) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (n : ℝ) * (A + 1) ^ 2 / 2 + c₀ ^ 2 := ⟨_, rfl⟩
  have hc₀pos : 0 < c₀ := by rw [hc₀]; positivity
  have hKpos : 0 < K := by
    rw [hK]; exact add_pos_of_nonneg_of_pos (by positivity) (pow_pos hc₀pos 2)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min 1 (ε / (2 * (n : ℝ) + 1)) := ⟨_, rfl⟩
  have h2n : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hηpos : 0 < η := by rw [hη]; exact lt_min one_pos (div_pos hε h2n)
  have hη1 : η ≤ 1 := by rw [hη]; exact min_le_left _ _
  -- Step 2: `nη ≤ ε/2`
  have hnη : (n : ℝ) * η ≤ ε / 2 := by
    have h1 : η * (2 * (n : ℝ) + 1) ≤ ε := by
      rw [← le_div_iff₀ h2n, hη]; exact min_le_right _ _
    linarith
  refine ⟨η, hηpos, hη1, min 1 (min (1 / c₀) (ε / (2 * K))),
    lt_min one_pos (lt_min (one_div_pos.mpr hc₀pos) (div_pos hε (mul_pos two_pos hKpos))), ?_⟩
  intro t D g ht hD hg
  -- Step 3: `|t| ≤ 1`, `|t| ≤ 1/c₀`, `|t| ≤ ε/(2K)`, `t² ≤ |t|`
  have ht1 : |t| ≤ 1 := (ht.trans_le (min_le_left _ _)).le
  have htc : |t| ≤ 1 / c₀ := (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have htK : |t| ≤ ε / (2 * K) := (ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hta : 0 ≤ |t| := abs_nonneg t
  have ht2 : t ^ 2 ≤ |t| := by
    rw [← sq_abs]; nlinarith [mul_nonneg hta (sub_nonneg.mpr ht1)]
  -- Step 4: `√g ≤ exp σ`
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = t * D + (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 :=
    ⟨_, rfl⟩
  have hsqrt : Real.sqrt g ≤ Real.exp σ := by
    have h2σ : 2 * t * D + 2 * (n : ℝ) * η * |t| + (n : ℝ) * (A + 1) ^ 2 * t ^ 2 = σ + σ := by
      rw [hσ]; ring
    rw [h2σ, Real.exp_add] at hg
    calc Real.sqrt g ≤ Real.sqrt (Real.exp σ * Real.exp σ) := Real.sqrt_le_sqrt hg
      _ = Real.exp σ := Real.sqrt_mul_self (Real.exp_pos σ).le
  -- Step 5: `|σ| ≤ c₀|t|`
  have hσabs : |σ| ≤ c₀ * |t| := by
    have h1 : |t * D| ≤ |t| * ((n : ℝ) * A) := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD hta
    have h2 : abs ((n : ℝ) * η * |t|) ≤ (n : ℝ) * |t| := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg hn hηpos.le) hta)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hn hη1) hta
    have h3 : |(n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2| ≤ (n : ℝ) * (A + 1) ^ 2 * |t| := by
      have hc : (0 : ℝ) ≤ (n : ℝ) * (A + 1) ^ 2 := by positivity
      have hc2 : (0 : ℝ) ≤ (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by positivity
      rw [abs_of_nonneg (by positivity)]
      calc (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 ≤ (n : ℝ) * (A + 1) ^ 2 * t ^ 2 := by linarith
        _ ≤ (n : ℝ) * (A + 1) ^ 2 * |t| := mul_le_mul_of_nonneg_left ht2 hc
    have htri : |σ| ≤ |t * D| + abs ((n : ℝ) * η * |t|) + |(n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2| := by
      rw [hσ]
      exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hcoef : (n : ℝ) * (A + 1 + (A + 1) ^ 2) ≤ c₀ := by
      rw [hc₀]; nlinarith [sq_nonneg (A + 1)]
    calc |σ| ≤ |t| * ((n : ℝ) * A) + (n : ℝ) * |t| + (n : ℝ) * (A + 1) ^ 2 * |t| := by linarith
      _ = (n : ℝ) * (A + 1 + (A + 1) ^ 2) * |t| := by ring
      _ ≤ c₀ * |t| := mul_le_mul_of_nonneg_right hcoef hta
  -- Step 6: `|σ| ≤ 1` and `σ² ≤ c₀²t²`
  have hσ1 : |σ| ≤ 1 := by
    calc |σ| ≤ c₀ * |t| := hσabs
      _ ≤ c₀ * (1 / c₀) := mul_le_mul_of_nonneg_left htc hc₀pos.le
      _ = 1 := mul_one_div_cancel hc₀pos.ne'
  have hσsq : σ ^ 2 ≤ c₀ ^ 2 * t ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg σ) hσabs 2
    rwa [sq_abs, mul_pow, sq_abs] at h
  -- Step 7: `exp σ ≤ 1 + σ + σ²`
  have hexp : Real.exp σ ≤ 1 + σ + σ ^ 2 := by
    have h := (le_abs_self _).trans (Real.abs_exp_sub_one_sub_id_le hσ1)
    linarith
  -- Step 8: the error terms `nη|t| ≤ (ε/2)|t|` and `Kt² ≤ (ε/2)|t|`
  have hnηt : (n : ℝ) * η * |t| ≤ ε / 2 * |t| := mul_le_mul_of_nonneg_right hnη hta
  have hKt : K * t ^ 2 ≤ ε / 2 * |t| := by
    have hK' : K * |t| ≤ ε / 2 := by
      calc K * |t| ≤ K * (ε / (2 * K)) := mul_le_mul_of_nonneg_left htK hKpos.le
        _ = ε / 2 := by field_simp
    calc K * t ^ 2 = (K * |t|) * |t| := by rw [← sq_abs t]; ring
      _ ≤ ε / 2 * |t| := mul_le_mul_of_nonneg_right hK' hta
  have hKt2 : K * t ^ 2 = (n : ℝ) * (A + 1) ^ 2 * t ^ 2 / 2 + c₀ ^ 2 * t ^ 2 := by
    rw [hK]; ring
  -- Step 9: `√g ≤ exp σ ≤ 1 + σ + σ² ≤ 1 + tD + nη|t| + Kt² ≤ 1 + tD + ε|t|`
  linarith
/-- **Gram determinant bound** (Simon Ch. 4, 1.9 and Ch. 2, §5, where the Jacobian is the square
root of such a Gram determinant): `det(vᵢ · vⱼ) ≤ exp(Σₐ |vₐ|² − n)` for `v₁, …, vₙ ∈ ℝᴾ`.
With `V eₐ = vₐ` on `ℝⁿ`, the Gram matrix is the matrix of `S = V*V` in the standard basis, so
`det G = Πᵢ λᵢ` and `Σₐ |vₐ|² = trace S = Σᵢ λᵢ` for the eigenvalues `λᵢ = |V uᵢ|² ≥ 0` of `S`;
multiply `λᵢ ≤ e^{λᵢ − 1}` (`s + 1 ≤ eˢ`) over `i`. -/
theorem Submission.fvmb_gram_det_le_exp_sum_norm_sq_sub : ∀ (P n : ℕ) (v : Fin n → Euclid P), Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) ≤ Real.exp (∑ a, ‖v a‖ ^ 2 - (n : ℝ)) := by
  intro P n v
  classical
  -- `V eₐ = vₐ` and the symmetric operator `S = V*V` on `ℝⁿ`
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let V : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] Euclid P := b.toBasis.constr ℝ v
  let S := LinearMap.adjoint V ∘ₗ V
  have hS : S.IsSymmetric := LinearMap.isSymmetric_adjoint_comp_self V
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hVe : ∀ a, V (b a) = v a := by
    intro a
    have := b.toBasis.constr_basis ℝ v a
    rw [OrthonormalBasis.coe_toBasis] at this
    exact this
  have hSinner : ∀ x y, inner ℝ x (S y) = inner ℝ (V x) (V y) := by
    intro x y
    simp [S, LinearMap.adjoint_inner_right]
  -- the matrix of `S` is the Gram matrix, and `trace S = Σₐ |vₐ|²`
  have hmat :
      LinearMap.toMatrix b.toBasis b.toBasis S = Matrix.of fun i j => inner ℝ (v i) (v j) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, hSinner, hVe, hVe]
    rfl
  have hdet : LinearMap.det S = Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) := by
    rw [← LinearMap.det_toMatrix b.toBasis, hmat]
  have htr : LinearMap.trace ℝ _ S = ∑ a, ‖v a‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner S b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hSinner, hVe, real_inner_self_eq_norm_sq]
  -- spectral theorem: `det S = Πᵢ λᵢ`, `trace S = Σᵢ λᵢ`, with `λᵢ = ⟪uᵢ, S uᵢ⟫ = |V uᵢ|² ≥ 0`
  rw [← hdet, hS.det_eq_prod_eigenvalues hn, ← htr, hS.trace_eq_sum_eigenvalues hn]
  have hnonneg : ∀ i, 0 ≤ hS.eigenvalues hn i := by
    intro i
    have h1 := hS.apply_eigenvectorBasis hn i
    have hu : ‖hS.eigenvectorBasis hn i‖ = 1 := (hS.eigenvectorBasis hn).orthonormal.1 i
    have h2 : inner ℝ (hS.eigenvectorBasis hn i) (S (hS.eigenvectorBasis hn i)) =
        hS.eigenvalues hn i := by
      rw [h1, inner_smul_right, real_inner_self_eq_norm_sq, hu]
      simp
    rw [← h2, hSinner]
    exact real_inner_self_nonneg
  -- `0 ≤ λᵢ ≤ e^{λᵢ − 1}`, multiplied over `i`
  simp only [RCLike.ofReal_real_eq_id, id]
  calc ∏ i, hS.eigenvalues hn i ≤ ∏ i, Real.exp (hS.eigenvalues hn i - 1) := by
        refine Finset.prod_le_prod₀ (fun i _ => hnonneg i) (fun i _ => ?_)
        have := Real.add_one_le_exp (hS.eigenvalues hn i - 1)
        linarith
    _ = Real.exp (∑ i, hS.eigenvalues hn i - n) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib]
        simp

/-- **First-order Jacobian bound** (Simon Ch. 2, §5, where `J_t = 1 + t div_M X + O(t²)` gives the
first variation formula 5.3; here only `‖L − I − tB‖ ≤ η|t|` is assumed): for `|t| < δ`,
`‖B‖ ≤ A` and orthonormal `τ₁, …, τₙ`, `(det(Lτᵢ · Lτⱼ))^{1/2} ≤ 1 + t Σₐ τₐ · Bτₐ + ε|t|`.
With `D = Σₐ τₐ · Bτₐ`, the frame bound gives `|D| ≤ nA` and
`Σₐ |Lτₐ|² − n ≤ 2tD + 2nη|t| + n(A + 1)²t²`, so the Gram determinant bound gives
`det G ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)`; the scalar bound (which supplies `0 < η ≤ 1` and
`δ`) turns this into the claim. -/
theorem Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order : ∀ (P n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ B L : Euclid P →L[ℝ] Euclid P, ‖B‖ ≤ A → ‖L - ContinuousLinearMap.id ℝ (Euclid P) - t • B‖ ≤ η * |t| → ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (L (τ i)) (L (τ j)))) ≤ 1 + t * ∑ a, inner ℝ (τ a) (B (τ a)) + ε * |t| := by
  intro P n A ε hA hε
  -- `0 < η ≤ 1` and `δ` depend only on `n`, `A` and `ε`
  obtain ⟨η, hη, hη1, δ, hδ, hsqrt⟩ := Submission.fvmb_sqrt_le_first_order_of_le_exp n A ε hA hε
  refine ⟨η, hη, δ, hδ, fun t ht B L hB hL τ hτ => ?_⟩
  -- `|D| ≤ nA` and `Σₐ |Lτₐ|² − n ≤ 2tD + 2nη|t| + n(A + 1)²t²`
  obtain ⟨hD, htr⟩ :=
    Submission.fvmb_perturbed_frame_sum_norm_sq_sub_le P n A η t B L τ hη1 hB hL hτ
  refine hsqrt t _ _ ht hD ?_
  -- `det G ≤ exp(Σₐ |Lτₐ|² − n) ≤ exp(2tD + 2nη|t| + n(A + 1)²t²)`
  exact (Submission.fvmb_gram_det_le_exp_sum_norm_sq_sub P n fun a => L (τ a)).trans
    (Real.exp_le_exp.mpr htr)
/-- Simon 6.2.24(1), reduction from `C¹` to smooth maps (step 3 of the push-forward proof): a `C¹`
map `φ` of `ℝᴾ` with `φ = id` off the compact set `K ⊆ U` is the pointwise `C¹` limit of `C^∞`
maps `ψₖ` that equal `id` off one compact `K' ⊆ U` and have uniformly bounded differentials.
`K' = cthickening δ K ⊆ U` and `ψₖ = id + ρₖ ⋆ (φ − id)`, `ρₖ` a normalized smooth bump supported
in `B_{δ/(k+2)}(0)`; then `Dψₖ = I + ρₖ ⋆ D(φ − id)`, so `‖Dψₖ‖ ≤ 1 + sup ‖D(φ − id)‖`, and the
mollifications of the continuous `φ − id` and `D(φ − id)` converge pointwise. -/
theorem Submission.dpf_smooth_approx_compact_perturbation : ∀ (P : ℕ) (U K : Set (Euclid P)) (φ : Euclid P → Euclid P), IsOpen U → IsCompact K → K ⊆ U → ContDiff ℝ 1 φ → (∀ x, x ∉ K → φ x = x) → ∃ (ψ : ℕ → Euclid P → Euclid P) (K' : Set (Euclid P)) (C : ℝ), IsCompact K' ∧ K' ⊆ U ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)) ∧ (∀ k x, x ∉ K' → ψ k x = x) ∧ (∀ k x, ‖fderiv ℝ (ψ k) x‖ ≤ C) ∧ (∀ x, Tendsto (fun k => ψ k x) atTop (𝓝 (φ x))) ∧ ∀ x, Tendsto (fun k => fderiv ℝ (ψ k) x) atTop (𝓝 (fderiv ℝ φ x)) := by
  intro P U K φ hU hK hKU hφ hfix
  -- Step 1: a margin `δ > 0` with `K' = cthickening δ K ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  -- Step 2: the perturbation `g = φ - id` is `C¹` and vanishes off `K`; `‖Dg‖ ≤ A`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → Euclid P, ∀ x, g x = φ x - x := ⟨fun x => φ x - x, fun _ => rfl⟩
  have hgφ : g = fun x => φ x - x := funext hg
  have hg1 : ContDiff ℝ 1 g := by
    rw [hgφ]
    exact hφ.sub contDiff_id
  have hgK : ∀ x, x ∉ K → g x = 0 := fun x hx => by rw [hg, hfix x hx, sub_self]
  have hgcs : HasCompactSupport g := HasCompactSupport.intro hK hgK
  have hgc : Continuous g := hg1.continuous
  have hDgc : Continuous (fderiv ℝ g) := hg1.continuous_fderiv one_ne_zero
  have hDg : ∀ x, fderiv ℝ g x = fderiv ℝ φ x - ContinuousLinearMap.id ℝ (Euclid P) := by
    intro x
    rw [hgφ]
    exact (((hφ.differentiable one_ne_zero) x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  obtain ⟨A, hA⟩ := hDgc.bounded_above_of_compact_support (hgcs.fderiv ℝ)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  -- Step 3: nonnegative smooth `ρ k` with `∫ ρ k = 1`, supported in `ball 0 (r k)`, where
  -- `r k = δ / (k + 2)`: the bump `β k` with `rOut = r k`, divided by its integral
  obtain ⟨r, hr0, hrδ, hrlim⟩ : ∃ r : ℕ → ℝ, (∀ k, 0 < r k) ∧ (∀ k, r k ≤ δ) ∧
      Tendsto r atTop (𝓝 0) := by
    refine ⟨fun k => δ / ((k : ℝ) + 2), fun k => by positivity, fun k => ?_, ?_⟩
    · exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  obtain ⟨ρ, hρs, hρn, hρi, hρsupp⟩ : ∃ ρ : ℕ → Euclid P → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k)) ∧ (∀ k x, 0 ≤ ρ k x) ∧ (∀ k, ∫ x, ρ k x = 1) ∧
      (∀ k, support (ρ k) ⊆ ball 0 (r k)) := by
    let β : ∀ k, ContDiffBump (0 : Euclid P) := fun k =>
      ⟨r k / 2, r k, half_pos (hr0 k), half_lt_self (hr0 k)⟩
    have hβi : ∀ k, 0 < ∫ x, β k x := fun k => by
      rw [integral_pos_iff_support_of_nonneg (fun x => (β k).nonneg)
        ((β k).continuous.integrable_of_hasCompactSupport (β k).hasCompactSupport),
        (β k).support_eq]
      exact measure_ball_pos _ _ (hr0 k)
    refine ⟨fun k x => (∫ y, β k y)⁻¹ * β k x, fun k => contDiff_const.mul (β k).contDiff,
      fun k x => mul_nonneg (inv_nonneg.2 (hβi k).le) (β k).nonneg, fun k => ?_,
      fun k x hx => ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ (hβi k).ne']
    · have hx' : x ∈ support (β k) := right_ne_zero_of_mul hx
      rwa [(β k).support_eq] at hx'
  have hρc : ∀ k, HasCompactSupport (ρ k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall 0 (r k)) fun x hx =>
      notMem_support.1 fun h => hx (ball_subset_closedBall (hρsupp k h))
  have hρloc : ∀ k, LocallyIntegrable (ρ k) volume := fun k => (hρs k).continuous.locallyIntegrable
  have hsmall : Tendsto (fun k => support (ρ k)) atTop (𝓝 (0 : Euclid P)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [(tendsto_order.1 hrlim).2 ε hε] with k hk
    exact (hρsupp k).trans ((ball_subset_ball hk.le).trans hεt)
  -- Steps 4 and 6: `ψ k = id + ρ k ⋆ g` has derivative `I + ρ k ⋆ Dg` (the `precompR`
  -- convolution of `hasFDerivAt_convolution_right` is the scalar one)
  have hL : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P).precompR (Euclid P) =
      (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (Euclid P →L[ℝ] Euclid P) →L[ℝ] (Euclid P →L[ℝ] Euclid P)) := by
    ext a f v
    simp [ContinuousLinearMap.precompR]
  have hderiv : ∀ k x, HasFDerivAt
      (fun y => y + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume y)
      (ContinuousLinearMap.id ℝ (Euclid P) +
        convolution (ρ k) (fderiv ℝ g) (ContinuousLinearMap.lsmul ℝ ℝ) volume x) x := by
    intro k x
    have h := hgcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (hρloc k) hg1 x
    rw [hL] at h
    exact (hasFDerivAt_id x).add h
  -- Step 5: off `K'`, `g = 0` on `ball x (r k)`, so `(ρ k ⋆ g) x = 0`
  have hsupp : ∀ k x, x ∉ cthickening δ K →
      convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
    intro k x hx
    have hgy : ∀ y ∈ ball x (r k), g y = 0 := fun y hy => hgK y fun hyK =>
      hx (mem_cthickening_of_dist_le x y δ K hyK ((mem_ball'.1 hy).le.trans (hrδ k)))
    rw [convolution_eq_right' _ (hρsupp k) fun y hy =>
      (hgy y hy).trans (hgy x (mem_ball_self (hr0 k))).symm, hgy x (mem_ball_self (hr0 k))]
    simp
  refine ⟨fun k x => x + convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume x,
    cthickening δ K, 1 + A, hK.cthickening, hδU, fun k => ?_, fun k x hx => ?_, fun k x => ?_,
    fun x => ?_, fun x => ?_⟩
  · exact contDiff_id.add
      ((hρc k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs k)
        hgc.locallyIntegrable)
  · simp only [hsupp k x hx, add_zero]
  · -- Step 6: `‖Dψ k‖ ≤ ‖I‖ + sup ‖Dg‖ ≤ 1 + A`
    rw [(hderiv k x).fderiv]
    refine (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le ?_)
    have h := dist_convolution_le (x₀ := x) (z₀ := 0) (μ := volume) hA0 (hρsupp k) (hρn k) (hρi k)
      hDgc.aestronglyMeasurable fun y _ => by rw [dist_zero_right]; exact hA y
    rwa [dist_zero_right] at h
  · -- Step 7: `ψ k x → x + g x = φ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hgc.aestronglyMeasurable) ((hgc.tendsto x).comp tendsto_snd)
      tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).add h
    rwa [hg x, add_sub_cancel] at h2
  · -- Step 7: `Dψ k x → I + Dg x = Dφ x`
    have h := convolution_tendsto_right (μ := volume) (φ := ρ) (g := fun _ => fderiv ℝ g)
      (k := fun _ => x) (Eventually.of_forall hρn) (Eventually.of_forall hρi) hsmall
      (Eventually.of_forall fun _ => hDgc.aestronglyMeasurable)
      ((hDgc.tendsto x).comp tendsto_snd) tendsto_const_nhds
    have h2 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ContinuousLinearMap.id ℝ (Euclid P))
      atTop (𝓝 (ContinuousLinearMap.id ℝ (Euclid P)))).add h
    rw [hDg x, add_sub_cancel] at h2
    exact h2.congr fun k => ((hderiv k x).fderiv).symm
/-- **Tangent projections of an embedded `C¹` submanifold** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let
`M ⊆ ℝᴾ` be an embedded `C¹` `m`-dimensional submanifold, `S_x = span T_xM` and `P_x` the
orthogonal projection onto `S_x`.  Then (a) `dim S_x = m` on `M`, (b) `x ↦ P_x` is continuous on
`M`, and (c) `x ↦ trace(P_x ∘ DX(x))` is continuous on `M` for every `C¹` field `X`.  For a chart
`(V, W, ψ)`, `S_{ψ(v)} = Dψ(v)(ℝᵐ)` by `dsmc_chart_tangentSpace_eq_range`, and for injective `D`
the projection onto `D(ℝᵐ)` is `D (D*D)⁻¹ D*`, continuous in `v` since `Dψ` is continuous and
inversion is continuous at units.  Continuity of `ψ⁻¹` on `W ∩ M` moves this to `x = ψ(v)`; (c)
follows as the trace is linear on the finite-dimensional space `L(ℝᴾ)`. -/
theorem Submission.codim1_hcp_fv_tangent_projection_continuousOn : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → (∀ x ∈ M, Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = m) ∧ ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) M ∧ ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → ContinuousOn (fun x => LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap)) M := by
  intro P m M hM
  -- step 1: the span of the range of a continuous linear map is its range
  have hspan_range : ∀ D : Euclid m →L[ℝ] Euclid P,
      Submodule.span ℝ (Set.range D) = LinearMap.range (D : Euclid m →ₗ[ℝ] Euclid P) := by
    intro D
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range, Submodule.span_eq]
  -- step 2: for injective `D`, `G = D*D` is a unit and `P_{range D} = D G⁻¹ D*`
  have hproj : ∀ D : Euclid m →L[ℝ] Euclid P, Injective D →
      IsUnit (ContinuousLinearMap.adjoint D ∘L D) ∧
      (LinearMap.range (D : Euclid m →ₗ[ℝ] Euclid P)).starProjection =
        D ∘L (Ring.inverse (ContinuousLinearMap.adjoint D ∘L D) ∘L ContinuousLinearMap.adjoint D) := by
    intro D hD
    set G := ContinuousLinearMap.adjoint D ∘L D
    -- (a) `Gw = 0` gives `|Dw|² = ⟨Gw, w⟩ = 0`, so `w = 0`; injective endomorphisms are units
    have hGinj : Injective G := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      apply hD
      rw [map_zero]
      have hnorm : ‖D w‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left]
        change inner ℝ (G w) w = 0
        rw [hw, inner_zero_left]
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hnorm)
    have hGunit : IsUnit G := ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hGinj, (LinearMap.injective_iff_surjective (f := (G : Euclid m →ₗ[ℝ] Euclid m))).mp hGinj⟩
    refine ⟨hGunit, ?_⟩
    -- (b) with `y = G⁻¹D*h`, `Dy ∈ range D` and `h - Dy ⊥ range D`, so `P h = Dy`
    ext1 h
    set y := Ring.inverse G (ContinuousLinearMap.adjoint D h)
    have hGy : G y = ContinuousLinearMap.adjoint D h := by
      rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hGunit, one_apply_eq_self]
    change _ = D y
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (LinearMap.mem_range_self (D : Euclid m →ₗ[ℝ] Euclid P) y) ?_
    rintro _ ⟨x, rfl⟩
    rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub]
    change inner ℝ (_ - G y) x = 0
    rw [hGy, sub_self, inner_zero_left]
  -- step 3: chart data at `y ∈ M`: `span T_{ψ v}M = range Dψ(v)` and `ψ⁻¹` is continuous
  have hlocal : ∀ y ∈ M, ∃ (V : Set (Euclid m)) (W : Set (Euclid P)) (ψ : Euclid m → Euclid P),
      IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ 1 ψ V ∧ ψ '' V = W ∩ M ∧
      (∀ z ∈ V, Injective (fderiv ℝ ψ z)) ∧
      (∀ v ∈ V, Submodule.span ℝ (tangentSpace M (ψ v)) =
        LinearMap.range (fderiv ℝ ψ v : Euclid m →ₗ[ℝ] Euclid P)) ∧
      (∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) := by
    intro y hy
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hder⟩ := hM y hy
    refine ⟨V, W, ψ, hV, hW, hyW, hψ, himg, hder, fun v hv => ?_, fun v hv => ?_⟩
    · have h := (Submission.dsmc_chart_tangentSpace_eq_range P 1 m M V W ψ le_rfl hV hW hψ hinj
        himg hprop hder v hv).1
      rw [h, hspan_range]
    · exact (Submission.dsmc_chart_tangentSpace_eq_range P 1 m M V W ψ le_rfl hV hW hψ hinj
        himg hprop hder v hv).2.1
  -- step 4, (a): `S_{ψ v} = range Dψ(v)` with `Dψ(v)` injective has dimension `m`
  have hfin : ∀ x ∈ M, Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = m := by
    intro x hx
    obtain ⟨V, W, ψ, hV, hW, hxW, hψ, himg, hder, hsp, -⟩ := hlocal x hx
    obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hx⟩
    rw [hsp v hv, LinearMap.finrank_range_of_inj (hder v hv), finrank_euclideanSpace_fin]
  -- step 5, (b): `x ↦ P_x` is continuous within `M` at every `y = ψ(v₀)`
  have hcont : ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) M := by
    intro y hy
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, himg, hder, hsp, hinv⟩ := hlocal y hy
    obtain ⟨v₀, hv₀, rfl⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hyW, hy⟩
    -- (a) `v ↦ D(v)`, `v ↦ D(v)*` and `v ↦ G(v) = D(v)*D(v)` are continuous on `V`
    have hD : ContinuousOn (fun v => fderiv ℝ ψ v) V := hψ.continuousOn_fderiv_of_isOpen hV le_rfl
    have hadj : Continuous (fun A : Euclid m →L[ℝ] Euclid P => ContinuousLinearMap.adjoint A) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous
    have hDt : ContinuousOn (fun v => ContinuousLinearMap.adjoint (fderiv ℝ ψ v)) V :=
      hadj.comp_continuousOn hD
    have hG : ContinuousOn
        (fun v => ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L fderiv ℝ ψ v) V :=
      hDt.clm_comp hD
    -- (b) each `G(v)` is a unit and inversion is continuous at units, so `R(v)` is continuous
    have hGinv : ContinuousOn (fun v =>
        Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L fderiv ℝ ψ v)) V := by
      intro v hv
      obtain ⟨u, hu⟩ := (hproj _ (hder v hv)).1
      have hinvc := NormedRing.inverse_continuousAt u
      rw [hu] at hinvc
      exact hinvc.comp_continuousWithinAt
        (f := fun v => ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L fderiv ℝ ψ v) (hG v hv)
    have hR : ContinuousOn (fun v => fderiv ℝ ψ v ∘L (Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L fderiv ℝ ψ v) ∘L
          ContinuousLinearMap.adjoint (fderiv ℝ ψ v))) V :=
      hD.clm_comp (hGinv.clm_comp hDt)
    -- (c) `P_{ψ v} = R(v)` on `V`
    have hPR : ∀ v ∈ V, (Submodule.span ℝ (tangentSpace M (ψ v))).starProjection =
        fderiv ℝ ψ v ∘L (Ring.inverse (ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L
          fderiv ℝ ψ v) ∘L ContinuousLinearMap.adjoint (fderiv ℝ ψ v)) := by
      intro v hv
      rw [← (hproj _ (hder v hv)).2]
      congr 1
      exact hsp v hv
    -- (d) `x ∈ M` near `ψ v₀` is `ψ v` with `v ∈ V` near `v₀`, so `P_x` is near `P_{ψ v₀}`
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hRat : ContinuousAt (fun v => fderiv ℝ ψ v ∘L (Ring.inverse
        (ContinuousLinearMap.adjoint (fderiv ℝ ψ v) ∘L fderiv ℝ ψ v) ∘L
          ContinuousLinearMap.adjoint (fderiv ℝ ψ v))) v₀ :=
      hR.continuousAt (hV.mem_nhds hv₀)
    obtain ⟨ρ, hρ, hρR⟩ := Metric.continuousAt_iff.mp hRat ε hε
    obtain ⟨δ₁, hδ₁, hδ₁inv⟩ := hinv v₀ hv₀ ρ hρ
    obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.mp hW (ψ v₀) hyW
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {x} hxM hxy => ?_⟩
    have hxW : x ∈ W := hδ₂W (lt_of_lt_of_le hxy (min_le_right _ _))
    obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hxM⟩
    have hvv : dist v v₀ < ρ := hδ₁inv v hv (lt_of_lt_of_le hxy (min_le_left _ _))
    rw [hPR v hv, hPR v₀ hv₀]
    exact hρR hvv
  -- step 6, (c): `T ↦ trace T` is linear on `L(ℝᴾ)`, hence continuous; compose with `P_x ∘ DX(x)`
  refine ⟨hfin, hcont, fun X hX => ?_⟩
  have htr : Continuous (fun T : Euclid P →L[ℝ] Euclid P =>
      LinearMap.trace ℝ (Euclid P) (T : Euclid P →ₗ[ℝ] Euclid P)) :=
    LinearMap.continuous_of_finiteDimensional
      ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hcomp : ContinuousOn (fun x =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection ∘L fderiv ℝ X x) M :=
    hcont.clm_comp (hX.continuous_fderiv one_ne_zero).continuousOn
  refine (htr.comp_continuousOn hcomp).congr fun x _ => ?_
  simp

/-- **Simon Ch. 2, (4.18)–(4.20)** (trace bound for a projected linear map): for a subspace `K` of
`ℝᴾ` and a continuous linear `L`, `|trace(p_K ∘ L)| ≤ (dim K) ‖L‖`.  For an orthonormal basis
`τ₁, …, τₙ` of `K`, `trace(p_K ∘ L) = Σₐ τₐ · Lτₐ`, and `|τₐ · Lτₐ| ≤ |τₐ| |Lτₐ| ≤ ‖L‖` by
Cauchy–Schwarz. -/
theorem Submission.codim1_hcp_fv_trace_comp_abs_le : ∀ (P : ℕ) (K : Submodule ℝ (Euclid P)) (L : Euclid P →L[ℝ] Euclid P), |LinearMap.trace ℝ (Euclid P) (K.starProjection.toLinearMap ∘ₗ L.toLinearMap)| ≤ (Module.finrank ℝ K : ℝ) * ‖L‖ := by
  intro P K L
  -- step 1: the standard orthonormal basis `e` of `K`, as vectors of `ℝᴾ`, is orthonormal
  set e := stdOrthonormalBasis ℝ K
  have hon : Orthonormal ℝ (fun i => ((e i : K) : Euclid P)) :=
    e.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  -- step 2: it spans `K`, the image of `span (range e) = ⊤` under the inclusion
  have hspan : Submodule.span ℝ (Set.range (fun i => ((e i : K) : Euclid P))) = K := by
    have h : Set.range (fun i => ((e i : K) : Euclid P)) = K.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    have htop : Submodule.span ℝ (Set.range e) = ⊤ := by
      simpa using e.toBasis.span_eq
    rw [h, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
  -- step 3: `trace(p_K ∘ L) = Σₐ ⟪τₐ, Lτₐ⟫`
  rw [Submission.fvmb_trace_starProjection_comp_eq_sum_inner P (Module.finrank ℝ K) K _ L hon hspan]
  -- steps 4-5: triangle inequality, then `|⟪τₐ, Lτₐ⟫| ≤ ‖τₐ‖ ‖L‖ ‖τₐ‖ = ‖L‖` termwise
  calc |∑ a, inner ℝ ((e a : K) : Euclid P) (L ((e a : K) : Euclid P))|
      ≤ ∑ a, |inner ℝ ((e a : K) : Euclid P) (L ((e a : K) : Euclid P))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin (Module.finrank ℝ K), ‖L‖ := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [hon.1 a, one_mul]
        exact (L.le_opNorm _).trans (by rw [hon.1 a, mul_one])
    _ = (Module.finrank ℝ K : ℝ) * ‖L‖ := by simp

/-- **Simon Ch. 2, §5** (the expansion `J_t = 1 + t div_M X + O(t²)` behind the first variation
formula 5.3, for the linear map `I + tB` on an `n`-plane): given `P`, `n`, `A ≥ 0` and `ε > 0`
there is `δ > 0` such that for `|t| < δ`, every subspace `K ⊆ ℝᴾ` with `dim K = n` and every `B`
with `‖B‖ ≤ A`, `(det(((I + tB) ∘ ι_K)* ((I + tB) ∘ ι_K)))^{1/2} ≤ 1 + t trace(p_K ∘ B) + ε|t|`.
In an orthonormal basis `e` of `K` the matrix of `((I + tB) ∘ ι_K)* ((I + tB) ∘ ι_K)` is the Gram
matrix `((I + tB)eᵢ · (I + tB)eⱼ)`, so the orthonormal-frame first-order bound applies with
`L = I + tB` (`‖L − I − tB‖ = 0`), and `Σₐ eₐ · Beₐ = trace(p_K ∘ B)` by the frame trace formula. -/
theorem Submission.codim1_hcp_fv_subspace_jacobian_first_order : ∀ (P n : ℕ) (A ε : ℝ), 0 ≤ A → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → ∀ (K : Submodule ℝ (Euclid P)) (B : Euclid P →L[ℝ] Euclid P), Module.finrank ℝ K = n → ‖B‖ ≤ A → Real.sqrt ((((ContinuousLinearMap.id ℝ (Euclid P) + t • B).comp K.subtypeL).adjoint ∘L ((ContinuousLinearMap.id ℝ (Euclid P) + t • B).comp K.subtypeL)).det) ≤ 1 + t * LinearMap.trace ℝ (Euclid P) (K.starProjection.toLinearMap ∘ₗ B.toLinearMap) + ε * |t| := by
  intro P n A ε hA hε
  -- step 1: `η` and `δ` of the orthonormal-frame bound depend only on `P`, `n`, `A` and `ε`
  obtain ⟨η, hη, δ, hδ, hgram⟩ :=
    Submission.fvmb_orthonormal_gram_sqrt_det_le_first_order P n A ε hA hε
  refine ⟨δ, hδ, fun t ht K B hK hB => ?_⟩
  -- step 3: the standard orthonormal basis `e` of `K` is an orthonormal frame of `ℝᴾ` spanning `K`
  subst hK
  set e := stdOrthonormalBasis ℝ K
  have hon : Orthonormal ℝ (fun i => ((e i : K) : Euclid P)) :=
    e.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hspan : Submodule.span ℝ (Set.range (fun i => ((e i : K) : Euclid P))) = K := by
    have h : Set.range (fun i => ((e i : K) : Euclid P)) = K.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    have htop : Submodule.span ℝ (Set.range e) = ⊤ := by
      simpa using e.toBasis.span_eq
    rw [h, Submodule.span_image, htop, Submodule.map_top, Submodule.range_subtype]
  -- step 4: the determinant on `K` is the Gram determinant of the frame `(L eᵢ)`
  have hgramdet : ∀ L : Euclid P →L[ℝ] Euclid P,
      ((L.comp K.subtypeL).adjoint ∘L (L.comp K.subtypeL)).det =
        Matrix.det (Matrix.of fun i j => inner ℝ (L ((e i : K) : Euclid P))
          (L ((e j : K) : Euclid P))) := by
    intro L
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix e.toBasis]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.repr_apply_apply, Matrix.of_apply]
    rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
    rfl
  -- steps 5-6: the frame bound for `L = I + tB`, where `‖L − I − tB‖ = 0`, and the frame trace
  rw [hgramdet, Submission.fvmb_trace_starProjection_comp_eq_sum_inner P _ K _ B hon hspan]
  refine hgram t ht B _ hB ?_ _ hon
  have : ContinuousLinearMap.id ℝ (Euclid P) + t • B - ContinuousLinearMap.id ℝ (Euclid P) -
      t • B = 0 := by abel
  rw [this, norm_zero]
  exact mul_nonneg hη.le (abs_nonneg t)

/-- Small deformations `x ↦ x + t • Z x` by a compactly supported `C¹` field `Z` are injective
immersions (the maps `φ_t` of Simon Ch. 2, 5.1–5.2).  `DZ` is continuous with compact support, so
`‖DZ‖ ≤ Λ` for some `Λ ≥ 0`, and `|t| < 1 / (Λ + 1)` gives `|t| Λ < 1`.  By the mean value
inequality `Z` is `Λ`-Lipschitz, so `a + t • Z a = b + t • Z b` forces `‖a - b‖ ≤ |t| Λ ‖a - b‖`,
i.e. `a = b`; in the same way the derivative `I + t • DZ(x)` is injective. -/
theorem Submission.codim1_hcp_fv_perturbation_injective : ∀ (P : ℕ) (Z : Euclid P → Euclid P), ContDiff ℝ 1 Z → HasCompactSupport Z → ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, |t| < c → Injective (fun x => x + t • Z x) ∧ ∀ x, Injective (fderiv ℝ (fun x => x + t • Z x) x) := by
  intro P Z hZ hZc
  have hdiff : Differentiable ℝ Z := hZ.differentiable one_ne_zero
  -- step 1: `DZ` is continuous with compact support, hence bounded by some `Λ ≥ 0`
  obtain ⟨Λ₀, hΛ₀⟩ := (hZ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hZc.fderiv (𝕜 := ℝ))
  obtain ⟨Λ, hΛ0, hΛ⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ x, ‖fderiv ℝ Z x‖ ≤ Λ :=
    ⟨max Λ₀ 0, le_max_right _ _, fun x => (hΛ₀ x).trans (le_max_left _ _)⟩
  -- step 2: `c = 1 / (Λ + 1)`, so `|t| < c` gives `|t| Λ < 1`
  refine ⟨1 / (Λ + 1), by positivity, fun t ht => ?_⟩
  have htΛ : |t| * Λ < 1 := by
    have h1 : |t| * (Λ + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at ht
    nlinarith [abs_nonneg t]
  -- step 3: mean value inequality, `‖Z a - Z b‖ ≤ Λ ‖a - b‖`
  have hlip : ∀ a b, ‖Z a - Z b‖ ≤ Λ * ‖a - b‖ := fun a b =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hdiff x) (fun x _ => hΛ x)
      (Set.mem_univ b) (Set.mem_univ a)
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · -- step 4: `a - b = t • (Z b - Z a)` gives `‖a - b‖ ≤ |t| Λ ‖a - b‖`, so `a = b`
    have hab' : a - b = t • Z b - t • Z a := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (t • Z b) b]; exact hab
    have hn : ‖a - b‖ ≤ |t| * Λ * ‖a - b‖ := by
      calc ‖a - b‖ = |t| * ‖Z b - Z a‖ := by
            rw [hab', ← smul_sub, norm_smul, Real.norm_eq_abs]
        _ ≤ |t| * (Λ * ‖b - a‖) := mul_le_mul_of_nonneg_left (hlip b a) (abs_nonneg t)
        _ = |t| * Λ * ‖a - b‖ := by rw [norm_sub_rev]; ring
    have h0 : ‖a - b‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖a - b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  · -- step 5: `D(x + t • Z x) = I + t • DZ(x)`, and `‖v - w‖ ≤ |t| Λ ‖v - w‖` as in step 4
    have hfd : fderiv ℝ (fun x => x + t • Z x) x =
        ContinuousLinearMap.id ℝ (Euclid P) + t • fderiv ℝ Z x :=
      ((hasFDerivAt_id x).add ((hdiff x).hasFDerivAt.const_smul t)).fderiv
    rw [hfd]
    intro v w hvw
    have hvw' : v - w = t • fderiv ℝ Z x w - t • fderiv ℝ Z x v := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm (t • fderiv ℝ Z x w) w]; exact hvw
    have hn : ‖v - w‖ ≤ |t| * Λ * ‖v - w‖ := by
      calc ‖v - w‖ = |t| * ‖fderiv ℝ Z x (w - v)‖ := by
            conv_lhs => rw [hvw']
            rw [← smul_sub, ← map_sub, norm_smul, Real.norm_eq_abs]
        _ ≤ |t| * (Λ * ‖w - v‖) :=
          mul_le_mul_of_nonneg_left ((fderiv ℝ Z x).le_of_opNorm_le (hΛ x) (w - v))
            (abs_nonneg t)
        _ = |t| * Λ * ‖v - w‖ := by rw [norm_sub_rev]; ring
    have h0 : ‖v - w‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖v - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
/-- Simon Ch. 2, §5 (first variation, 5.1–5.3), in one-sided form: if `M` is an embedded `C¹`
`m`-submanifold, `Z` is `C¹` with compact support, `E = M ∩ spt Z` has `Hᵐ(E) < ∞`, and
`Hᵐ(E) ≤ ∫_E J_t dHᵐ` for `|t| < t₀`, where `J_t` is the Jacobian of `Φ_t = id + tZ` along
`span T_xM`, then `∫_M div_M Z dHᵐ = 0`.  Instead of differentiating under the integral sign:
`J_t ≤ 1 + t div_M Z + ε|t|` uniformly on `E` for small `|t|`, so monotonicity of the lower
integral gives `0 ≤ t ∫_E div_M Z + ε|t| Hᵐ(E)`; `t = ±T/2` and `ε → 0` give
`∫_E div_M Z = 0`, and `div_M Z = 0` off `spt Z`. -/
theorem Submission.codim1_hcp_fv_jacobian_minimal_stationary : ∀ (P m : ℕ) (M : Set (Euclid P)) (Z : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 m M → ContDiff ℝ 1 Z → HasCompactSupport Z → μHE[m] (M ∩ tsupport Z) ≠ ∞ → (∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ ∫⁻ x in M ∩ tsupport Z, ENNReal.ofReal (Real.sqrt ((((fderiv ℝ (fun y => y + t • Z y) x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L ((fderiv ℝ (fun y => y + t • Z y) x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ∂μHE[m]) → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ Z x).toLinearMap) ∂μHE[m] = 0 := by
  intro P m M Z hM hZ hZc hfin ⟨t₀, ht₀, hmin⟩
  set τ : Euclid P → ℝ := fun x => LinearMap.trace ℝ (Euclid P)
    ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
      (fderiv ℝ Z x).toLinearMap) with hτ_def
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  have hEmeas : MeasurableSet (M ∩ tsupport Z) := hMmeas.inter (isClosed_tsupport Z).measurableSet
  obtain ⟨hfr, -, hdivc⟩ := Submission.codim1_hcp_fv_tangent_projection_continuousOn P m M hM
  have hdiff : Differentiable ℝ Z := hZ.differentiable one_ne_zero
  obtain ⟨Λ₀, hΛ₀⟩ := (hZ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hZc.fderiv (𝕜 := ℝ))
  set Λ := max Λ₀ 0 with hΛ_def
  have hΛ : ∀ x, ‖fderiv ℝ Z x‖ ≤ Λ := fun x => (hΛ₀ x).trans (le_max_left _ _)
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  -- |div_M Z| ≤ mΛ on M
  have hτb : ∀ x ∈ M, |τ x| ≤ m * Λ := by
    intro x hx
    have h := Submission.codim1_hcp_fv_trace_comp_abs_le P (Submodule.span ℝ (tangentSpace M x))
      (fderiv ℝ Z x)
    rw [hfr x hx] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hΛ x) (Nat.cast_nonneg m))
  -- measurability and integrability of div_M Z on E = M ∩ tsupport Z
  have hτmeas : AEStronglyMeasurable τ (μHE[m].restrict M) :=
    (hdivc Z hZ).aestronglyMeasurable hMmeas
  have hτmeasE : AEStronglyMeasurable τ (μHE[m].restrict (M ∩ tsupport Z)) :=
    hτmeas.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hτint : IntegrableOn τ (M ∩ tsupport Z) μHE[m] :=
    IntegrableOn.of_bound hfin.lt_top hτmeasE (m * Λ)
      (ae_restrict_of_forall_mem hEmeas fun x hx => by
        rw [Real.norm_eq_abs]; exact hτb x hx.1)
  -- derivative of the deformation Φ_t = id + tZ
  have hfd : ∀ (t : ℝ) (x : Euclid P), fderiv ℝ (fun y => y + t • Z y) x =
      ContinuousLinearMap.id ℝ (Euclid P) + t • fderiv ℝ Z x := fun t x =>
    ((hasFDerivAt_id x).add ((hdiff x).hasFDerivAt.const_smul t)).fderiv
  set a := (μHE[m] (M ∩ tsupport Z)).toReal with ha_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  set I := ∫ x in M ∩ tsupport Z, τ x ∂μHE[m] with hI_def
  -- one-sided first-order inequality: 0 ≤ t I + ε |t| a for small |t|
  have key : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, |t| < T → 0 ≤ t * I + ε * |t| * a := by
    intro ε hε
    obtain ⟨δ, hδ, hJ⟩ := Submission.codim1_hcp_fv_subspace_jacobian_first_order P m Λ ε hΛ0 hε
    refine ⟨min t₀ (min δ (1 / (m * Λ + 1))), lt_min ht₀ (lt_min hδ (by positivity)),
      fun t ht => ?_⟩
    have ht₀' : |t| < t₀ := lt_of_lt_of_le ht (min_le_left _ _)
    have htδ : |t| < δ := lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_left _ _))
    have htc : |t| < 1 / (m * Λ + 1) :=
      lt_of_lt_of_le ht ((min_le_right _ _).trans (min_le_right _ _))
    have htmΛ : |t| * (m * Λ) ≤ 1 := by
      have hpos : 0 < (m : ℝ) * Λ + 1 := by positivity
      rw [lt_div_iff₀ hpos] at htc
      nlinarith [abs_nonneg t, mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) hΛ0]
    have hnn : ∀ x ∈ M ∩ tsupport Z, 0 ≤ 1 + t * τ x + ε * |t| := by
      intro x hx
      have h1 : |t * τ x| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hτb x hx.1) (abs_nonneg t)).trans htmΛ
      have h2 : -1 ≤ t * τ x := (abs_le.mp h1).1
      nlinarith [abs_nonneg t]
    have hpt : ∀ x ∈ M ∩ tsupport Z,
        ENNReal.ofReal (Real.sqrt ((((fderiv ℝ (fun y => y + t • Z y) x).comp
          (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L
            ((fderiv ℝ (fun y => y + t • Z y) x).comp
              (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ≤
          ENNReal.ofReal (1 + t * τ x + ε * |t|) := by
      intro x hx
      apply ENNReal.ofReal_le_ofReal
      rw [hfd t x]
      exact hJ t htδ _ _ (hfr x hx.1) (hΛ x)
    have hc : IntegrableOn (fun _ : Euclid P => (1 : ℝ)) (M ∩ tsupport Z) μHE[m] :=
      integrableOn_const hfin
    have hc' : IntegrableOn (fun _ : Euclid P => ε * |t|) (M ∩ tsupport Z) μHE[m] :=
      integrableOn_const hfin
    have hint : IntegrableOn (fun x => 1 + t * τ x + ε * |t|) (M ∩ tsupport Z) μHE[m] :=
      (hc.add (hτint.const_mul t)).add hc'
    have h2 := (hmin t ht₀').trans (setLIntegral_mono' hEmeas hpt)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem hEmeas hnn)] at h2
    have hcalc : ∫ x in M ∩ tsupport Z, (1 + t * τ x + ε * |t|) ∂μHE[m] =
        a + t * I + ε * |t| * a := by
      have e1 : ∫ x in M ∩ tsupport Z, (1 + t * τ x + ε * |t|) ∂μHE[m] =
          ∫ x in M ∩ tsupport Z, (1 + t * τ x) ∂μHE[m] +
            ∫ x in M ∩ tsupport Z, ε * |t| ∂μHE[m] :=
        integral_add (hc.add (hτint.const_mul t)) hc'
      have e2 : ∫ x in M ∩ tsupport Z, (1 + t * τ x) ∂μHE[m] =
          ∫ x in M ∩ tsupport Z, (1 : ℝ) ∂μHE[m] + ∫ x in M ∩ tsupport Z, t * τ x ∂μHE[m] :=
        integral_add hc (hτint.const_mul t)
      rw [e1, e2, integral_const_mul, setIntegral_const, setIntegral_const]
      simp only [smul_eq_mul, Measure.real, ha_def, hI_def]
      ring
    rw [hcalc] at h2
    have hrhs : 0 ≤ a + t * I + ε * |t| * a := by
      rw [← hcalc]
      exact setIntegral_nonneg hEmeas hnn
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff hrhs] at h2
    linarith
  -- Fermat: |I| ≤ ε a for every ε > 0, hence I = 0
  have hI0 : I = 0 := by
    have hbound : ∀ ε : ℝ, 0 < ε → |I| ≤ ε * a := by
      intro ε hε
      obtain ⟨T, hT, hTI⟩ := key ε hε
      have hpos := hTI (T / 2) (by rw [abs_of_pos (by positivity)]; linarith)
      have hneg := hTI (-(T / 2)) (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
      rw [abs_of_pos (by positivity : (0:ℝ) < T / 2)] at hpos
      rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < T / 2)] at hneg
      have h1 : -(ε * a) ≤ I := by nlinarith
      have h2 : I ≤ ε * a := by nlinarith
      exact abs_le.mpr ⟨h1, h2⟩
    by_contra hne
    have hIpos : 0 < |I| := abs_pos.mpr hne
    have := hbound (|I| / (2 * (a + 1))) (by positivity)
    have hlt : |I| / (2 * (a + 1)) * a < |I| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- div_M Z vanishes on M \ tsupport Z, so ∫_M = ∫_{M ∩ tsupport Z}
  have hzero : ∀ x ∈ M \ (M ∩ tsupport Z), τ x = 0 := by
    intro x hx
    have hxs : x ∉ tsupport Z := fun h => hx.2 ⟨hx.1, h⟩
    have hD : fderiv ℝ Z x = 0 := by
      by_contra hne
      exact hxs (support_fderiv_subset ℝ hne)
    simp only [hτ_def, hD, ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, map_zero]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hMmeas inter_subset_left hzero]
  exact hI0
/-- Simon Ch. 2, §5 (p. 63), stationarity tested with `C¹` fields: if `M` is an embedded `C¹`
`m`-submanifold with `Hᵐ(M ∩ K) < ∞` for compact `K ⊆ U` and `∫_M div_M Z dHᵐ = 0` for every `C^∞`
field `Z` with compact support in `U`, then the same holds for every `C¹` such field `X`.  The `C^∞`
maps `ψₖ → id + X` of `dpf_smooth_approx_compact_perturbation` equal `id` off one compact `K' ⊆ U`,
so `Xₖ = ψₖ − id` are admissible, `‖DXₖ‖ ≤ C + 1`, `DXₖ = 0` off `K'` and `DXₖ → DX` pointwise.
With `dim T_xM = m`, `|div_M Xₖ| ≤ m(C + 1)·1_{K'}`, which is `Hᵐ⌞M`-integrable, so dominated
convergence gives `∫_M div_M X = lim ∫_M div_M Xₖ = 0`. -/
theorem Submission.codim1_hcp_fv_smooth_to_C1_stationary : ∀ (P m : ℕ) (U M : Set (Euclid P)), IsOpen U → IsEmbeddedSubmanifold 1 m M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ Z x).toLinearMap) ∂μHE[m] = 0) → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0 := by
  intro P m U M hU hM hfin hsmooth X hX hXc hXU
  -- Step 1: `M` is Borel, `dim T_xM = m` on `M`, and `div_M Y` is continuous on `M` for `C¹` `Y`
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  obtain ⟨hfr, -, hdivc⟩ := Submission.codim1_hcp_fv_tangent_projection_continuousOn P m M hM
  -- Step 2: `C^∞` maps `ψ k` equal to `id` off one compact `K' ⊆ U`, with `‖Dψ k‖ ≤ C` and
  -- `Dψ k → D(id + X)` pointwise
  obtain ⟨ψ, K', C, hK', hK'U, hψs, hψid, hψC, -, hψD⟩ :=
    Submission.dpf_smooth_approx_compact_perturbation P U (tsupport X) (fun x => x + X x) hU hXc
      hXU (contDiff_id.add hX) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  -- Step 3: the `C^∞` fields `Xk k = ψ k - id` vanish off `K'`, so `∫_M div_M (Xk k) = 0`
  set Xk : ℕ → Euclid P → Euclid P := fun k x => ψ k x - x
  have hXks : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Xk k) := fun k => (hψs k).sub contDiff_id
  have hXk0 : ∀ k x, x ∉ K' → Xk k x = 0 := fun k x hx => by simp [Xk, hψid k x hx]
  have hXkts : ∀ k, tsupport (Xk k) ⊆ K' := fun k =>
    closure_minimal (support_subset_iff'.2 (hXk0 k)) hK'.isClosed
  have hstat : ∀ k, ∫ x in M, LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap) ∂μHE[m] = 0 := fun k =>
    hsmooth (Xk k) (hXks k) (HasCompactSupport.intro hK' (hXk0 k)) ((hXkts k).trans hK'U)
  -- Step 4: `D(Xk k) = Dψ k - I`, so `‖D(Xk k)‖ ≤ C + 1`, `D(Xk k) → DX` and `D(Xk k) = 0` off `K'`
  have hψd : ∀ k, Differentiable ℝ (ψ k) := fun k => (hψs k).differentiable (by simp)
  have hDXk : ∀ k x, fderiv ℝ (Xk k) x = fderiv ℝ (ψ k) x - ContinuousLinearMap.id ℝ (Euclid P) :=
    fun k x => ((hψd k x).hasFDerivAt.sub (hasFDerivAt_id x)).fderiv
  have hDφ : ∀ x, fderiv ℝ (fun x => x + X x) x =
      ContinuousLinearMap.id ℝ (Euclid P) + fderiv ℝ X x :=
    fun x => ((hasFDerivAt_id x).add ((hX.differentiable one_ne_zero) x).hasFDerivAt).fderiv
  have hconv : ∀ x, Tendsto (fun k => fderiv ℝ (Xk k) x) atTop (𝓝 (fderiv ℝ X x)) := by
    intro x
    have h := (hψD x).sub_const (ContinuousLinearMap.id ℝ (Euclid P))
    rw [hDφ x, add_sub_cancel_left] at h
    simpa only [hDXk] using h
  have hDXkb : ∀ k x, ‖fderiv ℝ (Xk k) x‖ ≤ C + 1 := by
    intro k x
    rw [hDXk]
    exact (norm_sub_le _ _).trans (add_le_add (hψC k x) ContinuousLinearMap.norm_id_le)
  have hDXk0 : ∀ k x, x ∉ K' → fderiv ℝ (Xk k) x = 0 := fun k x hx =>
    fderiv_of_notMem_tsupport ℝ fun h => hx (hXkts k h)
  -- Step 5: the dominating function `g = m (C + 1) 1_{K'}` is integrable, `Hᵐ(M ∩ K') < ∞`
  set g : Euclid P → ℝ := K'.indicator (fun _ => (m : ℝ) * (C + 1)) with hg_def
  have hg : Integrable g (μHE[m].restrict M) := by
    rw [hg_def, integrable_indicator_iff hK'.isClosed.measurableSet]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply hK'.isClosed.measurableSet, inter_comm]
    exact hfin K' hK' hK'U
  -- `|div_M (Xk k)| ≤ dim T_xM ‖D(Xk k)‖ ≤ m (C + 1)` on `M ∩ K'`, and `div_M (Xk k) = 0` off `K'`
  have hbound : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ‖LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)‖ ≤ g x := by
    intro k
    filter_upwards [ae_restrict_mem hMmeas] with x hx
    by_cases hxK : x ∈ K'
    · rw [hg_def, indicator_of_mem hxK, Real.norm_eq_abs]
      have h := Submission.codim1_hcp_fv_trace_comp_abs_le P
        (Submodule.span ℝ (tangentSpace M x)) (fderiv ℝ (Xk k) x)
      rw [hfr x hx] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hDXkb k x) (Nat.cast_nonneg m))
    · rw [hg_def, indicator_of_notMem hxK, hDXk0 k x hxK]
      simp
  -- Step 6: `div_M (Xk k) → div_M X` pointwise, `L ↦ trace (P_x ∘ L)` being linear on a
  -- finite-dimensional space
  have hlim : ∀ᵐ x ∂(μHE[m].restrict M), Tendsto (fun k => LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)) atTop
      (𝓝 (LinearMap.trace ℝ (Euclid P)
        ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
          (fderiv ℝ X x).toLinearMap))) := by
    refine Eventually.of_forall fun x => ?_
    have htr : Continuous (fun T : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) (T : Euclid P →ₗ[ℝ] Euclid P)) :=
      LinearMap.continuous_of_finiteDimensional
        ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
    have hF : Continuous (fun L : Euclid P →L[ℝ] Euclid P => LinearMap.trace ℝ (Euclid P)
        ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ L.toLinearMap)) := by
      have := htr.comp (Continuous.clm_comp
        (g := fun _ : Euclid P →L[ℝ] Euclid P =>
          (Submodule.span ℝ (tangentSpace M x)).starProjection)
        (f := id) continuous_const continuous_id)
      refine this.congr fun L => ?_
      simp only [Function.comp_apply, id]
      rfl
    exact (hF.tendsto _).comp (hconv x)
  -- Step 7: `div_M (Xk k)` is continuous on the Borel set `M`, hence measurable
  have hmeas : ∀ k, AEStronglyMeasurable (fun x => LinearMap.trace ℝ (Euclid P)
      ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ
        (fderiv ℝ (Xk k) x).toLinearMap)) (μHE[m].restrict M) :=
    fun k => (hdivc (Xk k) ((hXks k).of_le (by exact_mod_cast le_top))).aestronglyMeasurable hMmeas
  -- Step 8: dominated convergence, `∫_M div_M X = lim ∫_M div_M (Xk k) = 0`
  have hT := tendsto_integral_of_dominated_convergence g hmeas hg hbound hlim
  simp only [hstat] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

/-- **Area formula on an embedded `C¹` submanifold** (Simon Ch. 2, 4.11–4.13, as used in Ch. 2,
5.1–5.2).  Let `M ⊂ ℝᴾ` be an embedded `m`-dimensional `C¹` submanifold, `E ⊆ M` Borel, and
`Φ : ℝᴾ → ℝᴾ` a `C¹` map that is injective on `E` with `DΦ(x)` injective for `x ∈ E`.  Then
`Hᵐ(Φ(E)) = ∫_E J^M Φ dHᵐ`, where `J^M Φ(x) = √det((DΦ(x) ∘ ι_x)*(DΦ(x) ∘ ι_x))` and
`ι_x : span T_xM → ℝᴾ` is the inclusion.  By Lindelöf countably many charts `W_k` cover `M`; on
each of the disjoint Borel pieces `E_k = (E ∩ W_k) \ ⋃_{j<k} (E ∩ W_j)` this is the area formula
in one chart.  Summing over `k` gives the claim: the integral is countably additive over the
`E_k`, and so is `Hᵐ(Φ(·))`, since the images `Φ(E_k)` are Borel (Lusin–Souslin) and pairwise
disjoint (`Φ` is injective on `E`). -/
theorem Submission.codim1_hcp_submanifold_area_formula : ∀ (P m : ℕ) (M E : Set (Euclid P)) (Φ : Euclid P → Euclid P), IsEmbeddedSubmanifold 1 m M → MeasurableSet E → E ⊆ M → ContDiff ℝ 1 Φ → InjOn Φ E → (∀ x ∈ E, Injective (fderiv ℝ Φ x)) → μHE[m] (Φ '' E) = ∫⁻ x in E, ENNReal.ofReal (Real.sqrt ((((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL).adjoint ∘L ((fderiv ℝ Φ x).comp (Submodule.span ℝ (tangentSpace M x)).subtypeL)).det)) ∂μHE[m] := by
  intro P m M E Φ hM hE hEM hΦ hΦinj hDΦ
  -- step 2: countably many charts `(V_k, W_k, ψ_k)` of `M` as in (4.1) and pairwise disjoint
  -- Borel pieces `E_k ⊆ W_k ∩ M` with `⋃_k E_k = E`
  obtain ⟨Es, Vs, Ws, ψs, hEs, hdisj, hunion, hcharts⟩ : ∃ (Es : ℕ → Set (Euclid P)) (Vs : ℕ → Set (Euclid m)) (Ws : ℕ → Set (Euclid P)) (ψs : ℕ → Euclid m → Euclid P), (∀ k, MeasurableSet (Es k)) ∧ Pairwise (fun i j => Disjoint (Es i) (Es j)) ∧ (⋃ k, Es k) = E ∧ ∀ k, IsOpen (Vs k) ∧ IsOpen (Ws k) ∧ ContDiffOn ℝ 1 (ψs k) (Vs k) ∧ InjOn (ψs k) (Vs k) ∧ ψs k '' Vs k = Ws k ∩ M ∧ (∀ K ⊆ Ws k, IsCompact K → IsCompact (Vs k ∩ ψs k ⁻¹' K)) ∧ (∀ z ∈ Vs k, Injective (fderiv ℝ (ψs k) z)) ∧ Es k ⊆ Ws k ∩ M := by
    -- every `y ∈ M` has a chart `(V_y, W_y, ψ_y)` with `y ∈ W_y`; every `y ∉ M` gets the empty
    -- chart `(∅, ∅, 0)`, which satisfies all chart conditions
    have hchart : ∀ y : Euclid P, ∃ (V : Set (Euclid m)) (W : Set (Euclid P))
        (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ ContDiffOn ℝ 1 ψ V ∧ InjOn ψ V ∧
          ψ '' V = W ∩ M ∧ (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧
          (∀ z ∈ V, Injective (fderiv ℝ ψ z)) ∧ (y ∈ M → y ∈ W) := by
      intro y
      by_cases hy : y ∈ M
      · obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hD⟩ := hM y hy
        exact ⟨V, W, ψ, hV, hW, by exact_mod_cast hψ, hinj, himg, hprop, hD, fun _ => hyW⟩
      · exact ⟨∅, ∅, 0, isOpen_empty, isOpen_empty, contDiffOn_empty, injOn_empty _, by simp,
          by simp, by simp, fun h => absurd h hy⟩
    choose V W ψ hV hW hψ hinj himg hprop hD hyW using hchart
    -- Lindelöf: the `W_y` with `y` in a countable set `T ⊆ {y_0, y_1, …}` already cover `M`
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
    obtain ⟨f, hf⟩ := Set.countable_iff_exists_subset_range.1 hTc
    have hcover : M ⊆ ⋃ k, W (f k) := by
      intro y hy
      have hyT : y ∈ ⋃ i ∈ T, W i := by
        rw [hTU]
        exact mem_iUnion.2 ⟨y, hyW y hy⟩
      obtain ⟨i, hiT, hyi⟩ := mem_iUnion₂.1 hyT
      obtain ⟨k, rfl⟩ := hf hiT
      exact mem_iUnion.2 ⟨k, hyi⟩
    -- `E_k = (E ∩ W_{y_k}) \ ⋃_{j<k} (E ∩ W_{y_j})`, with the chart at `y_k`
    refine ⟨disjointed fun k => E ∩ W (f k), fun k => V (f k), fun k => W (f k),
      fun k => ψ (f k), MeasurableSet.disjointed fun k => hE.inter (hW (f k)).measurableSet,
      disjoint_disjointed _, ?_, fun k => ⟨hV (f k), hW (f k), hψ (f k), hinj (f k), himg (f k),
        hprop (f k), hD (f k), fun x hx => ?_⟩⟩
    -- `⋃_k E_k = E ∩ ⋃_k W_{y_k} = E`, as `E ⊆ M ⊆ ⋃_k W_{y_k}`
    · rw [iUnion_disjointed, ← inter_iUnion]
      exact inter_eq_left.2 (hEM.trans hcover)
    -- `E_k ⊆ E ∩ W_{y_k} ⊆ W_{y_k} ∩ M`
    · have hx' := disjointed_subset _ k hx
      exact ⟨hx'.2, hEM hx'.1⟩
  choose hV hW hψ hinj himg hprop hD hEW using hcharts
  have hEsE : ∀ k, Es k ⊆ E := fun k => (subset_iUnion Es k).trans hunion.subset
  -- steps 4–8 on each piece `E_k ⊆ W_k ∩ M`: the area formula inside the chart `ψ_k`
  have hpiece := fun k => Submission.codim1_hcp_af_chart_area_formula P m M (Es k) (Ws k) (Vs k)
    (ψs k) Φ (hV k) (hW k) (hψ k) (hinj k) (himg k) (hprop k) (hD k) (hEs k) (hEW k) hΦ
    (hΦinj.mono (hEsE k)) fun x hx => hDΦ x (hEsE k hx)
  -- step 9: the images `Φ(E_k)` are Borel (Lusin–Souslin) and pairwise disjoint (`Φ` is
  -- injective on `E`), so `Hᵐ(Φ(E)) = Σ_k Hᵐ(Φ(E_k))`; the integral over `E` splits likewise
  have hΦEs : ∀ k, MeasurableSet (Φ '' Es k) := fun k =>
    (hEs k).image_of_continuousOn_injOn hΦ.continuous.continuousOn (hΦinj.mono (hEsE k))
  have hΦdisj : Pairwise (Disjoint on fun k => Φ '' Es k) := fun i j hij =>
    (hdisj hij).image hΦinj (hEsE i) (hEsE j)
  rw [← hunion, image_iUnion, measure_iUnion hΦdisj hΦEs, lintegral_iUnion hEs hdisj]
  exact tsum_congr hpiece

/-- **Simon Ch. 2, §5 (5.1–5.4)**: a deformation-minimal `C¹` submanifold is stationary.  Let
`M ⊆ U` be an embedded `C¹` `m`-submanifold with `Hᵐ(M ∩ K) < ∞` for compact `K ⊆ U`, whose area
does not decrease under the deformations `x ↦ x + tZ(x)`, `Z` smooth with compact support in `U`.
Then `∫_M div_M X dHᵐ = 0` for every `C¹` field `X` with compact support in `U`.  By smooth
approximation of `X` it suffices to take `X = Z` smooth.  `E = M ∩ spt Z` is Borel with
`Hᵐ(E) < ∞`, and for small `|t|` the map `Φₜ = id + tZ` is `C¹`, injective and has injective
differential.  So the area formula turns `Hᵐ(E) ≤ Hᵐ(Φₜ(E))` into `Hᵐ(E) ≤ ∫_E Jₜ dHᵐ`, and the
first-order expansion of the Jacobian `Jₜ` at `t = 0` gives `∫_M div_M Z dHᵐ = 0`. -/
theorem Submission.codim1_hcp_deformation_minimal_stationary : ∀ (P m : ℕ) (U M : Set (Euclid P)), IsOpen U → M ⊆ U → IsEmbeddedSubmanifold 1 m M → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ Z : Euclid P → Euclid P, ContDiff ℝ (⊤ : ℕ∞) Z → HasCompactSupport Z → tsupport Z ⊆ U → ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, |t| < t₀ → μHE[m] (M ∩ tsupport Z) ≤ μHE[m] ((fun x => x + t • Z x) '' (M ∩ tsupport Z))) → ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0 := by
  intro P m U M hU _ hM hfin hdef
  -- it suffices to prove `∫_M div_M Z dHᵐ = 0` for smooth `Z` with compact support in `U`
  refine Submission.codim1_hcp_fv_smooth_to_C1_stationary P m U M hU hM hfin
    fun Z hZ hZc hZU => ?_
  have hZ1 : ContDiff ℝ 1 Z := hZ.of_le (by exact_mod_cast le_top)
  -- `E = M ∩ spt Z` is Borel (`M` is) and `Hᵐ(E) < ∞` (`spt Z` is a compact subset of `U`)
  have hE : MeasurableSet (M ∩ tsupport Z) :=
    (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1.inter
      (isClosed_tsupport Z).measurableSet
  refine Submission.codim1_hcp_fv_jacobian_minimal_stationary P m M Z hM hZ1 hZc
    (hfin _ hZc.isCompact hZU) ?_
  -- for `|t| < min(t₀, c)`, `Φₜ = id + tZ` is `C¹`, injective and has injective differential, so
  -- the area formula rewrites `Hᵐ(Φₜ(E))` as `∫_E Jₜ dHᵐ`
  obtain ⟨t₀, ht₀, hmin⟩ := hdef Z hZ hZc hZU
  obtain ⟨c, hc, hinj⟩ := Submission.codim1_hcp_fv_perturbation_injective P Z hZ1 hZc
  refine ⟨min t₀ c, lt_min ht₀ hc, fun t ht => ?_⟩
  obtain ⟨hΦ, hDΦ⟩ := hinj t (ht.trans_le (min_le_right t₀ c))
  exact (hmin t (ht.trans_le (min_le_left t₀ c))).trans_eq
    (Submission.codim1_hcp_submanifold_area_formula P m M (M ∩ tsupport Z) (fun x => x + t • Z x)
      hM hE inter_subset_left (contDiff_id.add (hZ1.const_smul t)) hΦ.injOn fun x _ => hDΦ x)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
