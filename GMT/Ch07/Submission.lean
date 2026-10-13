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

/-- **Rescaled Gauss–Green identity** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi), the change
of variable `x → λₖ x` in (8), chapter-03.txt lines 661–665).  Suppose
`∫_F div φ dLᵐ⁺¹ = -∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly supported `φ` with `tsupport φ ⊆ D`.
If `r > 0` and `g` is `C¹` with compact support and `y + r • tsupport g ⊆ D`, then with
`F_{y,r} = {w : y + r w ∈ F}`, `r⁻ᵐ ∫ ⟨g((z - y)/r), ν(z)⟩ dμ(z) = -∫_{F_{y,r}} div g dLᵐ⁺¹`:
`φ = g((· - y)/r)` is admissible with `div φ = r⁻¹ (div g)((· - y)/r)`, and the substitution
`z = y + r w` has Jacobian `rᵐ⁺¹`. -/
theorem Submission.codim1_rdo_dg_tma_rescaled_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r : ℝ) (g : Euclid (m + 1) → Euclid (m + 1)), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → ContDiff ℝ 1 g → HasCompactSupport g → (∀ w ∈ tsupport g, y + r • w ∈ D) → (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ = -∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
  intro m D F μ ν y r g hF hGG hr hg hgc hD
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  -- the affine homeomorphism `A w = y + r • w` and its inverse
  let A : Euclid (m + 1) ≃ₜ Euclid (m + 1) :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y)
  have hA : ∀ w, A w = y + r • w := fun w => rfl
  have hAsymm : ∀ z, A.symm z = r⁻¹ • (z - y) := by
    intro z
    apply A.injective
    rw [A.apply_symm_apply, hA, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel
  -- `φ = g ∘ A⁻¹` is admissible in the Gauss–Green identity
  set φ : Euclid (m + 1) → Euclid (m + 1) := fun z => g (r⁻¹ • (z - y)) with hφdef
  have hφA : φ = g ∘ A.symm := by
    funext z
    simp [hφdef, hAsymm]
  have hφ : ContDiff ℝ 1 φ := hg.comp (by fun_prop)
  have hφts : tsupport φ = A '' tsupport g := by
    rw [hφA, tsupport_comp_eq_preimage _ A.symm, A.preimage_symm]
  have hφc : HasCompactSupport φ := by
    rw [HasCompactSupport, hφts]
    exact hgc.isCompact.image A.continuous
  have hφD : tsupport φ ⊆ D := by
    rw [hφts]
    rintro _ ⟨w, hw, rfl⟩
    rw [hA]
    exact hD w hw
  -- chain rule: `div φ (z) = r⁻¹ (div g) (r⁻¹ • (z - y))`
  have hfd : ∀ z, fderiv ℝ φ z = r⁻¹ • fderiv ℝ g (r⁻¹ • (z - y)) := by
    intro z
    have hin : HasFDerivAt (fun z : Euclid (m + 1) => r⁻¹ • (z - y))
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) z :=
      ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const y).const_smul (r⁻¹ : ℝ)
    have hgd := ((hg.differentiable one_ne_zero) (r⁻¹ • (z - y))).hasFDerivAt
    have h2 : HasFDerivAt φ ((fderiv ℝ g (r⁻¹ • (z - y))).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1)))) z := hgd.comp z hin
    rw [h2.fderiv]
    ext x
    simp
  have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = r⁻¹ * T (r⁻¹ • (z - y)) := by
    intro z
    rw [hfd]
    simp [hTdef, map_smul]
  have hGG' := hGG φ hφ hφc hφD
  simp_rw [htr] at hGG'
  rw [integral_const_mul] at hGG'
  -- change of variables `z = y + r • w`
  have hcv : ∫ z in F, T (r⁻¹ • (z - y)) =
      r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hpre : MeasurableSet ((fun w => y + r • w) ⁻¹' F) := hF.preimage (by fun_prop)
    rw [← integral_indicator hF, ← integral_indicator hpre]
    set Ψ : Euclid (m + 1) → ℝ := F.indicator (fun z => T (r⁻¹ • (z - y))) with hΨ
    have h1 : (fun w => ((fun w => y + r • w) ⁻¹' F).indicator T w) =
        fun w => Ψ (r • w + y) := by
      funext w
      rw [add_comm (r • w) y]
      by_cases hw : y + r • w ∈ F
      · rw [indicator_of_mem (show w ∈ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_mem hw]
        simp [smul_smul, inv_mul_cancel₀ hr.ne']
      · rw [indicator_of_notMem (show w ∉ (fun w => y + r • w) ⁻¹' F from hw), hΨ,
          indicator_of_notMem hw]
    rw [h1, Measure.integral_comp_smul volume (fun x => Ψ (x + y)) r,
      integral_add_right_eq_self Ψ y]
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    rw [abs_of_pos (inv_pos.2 (pow_pos hr _))]
    field_simp
  rw [hcv] at hGG'
  -- `rᵐ ∫_{F_{y,r}} div g = -∫ ⟨g ((z - y) / r), ν⟩ dμ`; divide by `rᵐ`
  have hrm : (r ^ m) ≠ 0 := pow_ne_zero _ hr.ne'
  have key : ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -(r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) := by
    have : r⁻¹ * (r ^ (m + 1) * ∫ w in (fun w => y + r • w) ⁻¹' F, T w) =
        r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
      rw [pow_succ]
      field_simp
    rw [this] at hGG'
    linarith
  rw [key]
  field_simp
/-- **Hausdorff measure on a hyperplane** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi),
chapter-03.txt lines 734–746).  For `v ≠ 0` in `ℝ^{m+1}` the hyperplane `P_v = (span{v})ᗮ` has
dimension `m`, so an orthonormal basis of `P_v` indexed by `Fin m` gives a linear isometry
`ι : ℝ^m → ℝ^{m+1}` onto `P_v`; in particular `⟨ι x, v⟩ = 0`.  `μHE[m]` is isometry invariant
(`ι_# μHE[m] = μHE[m]⌞range ι`) and equals Lebesgue measure on `ℝ^m`, hence
`μHE[m]⌞P_v = ι_# Lᵐ`. -/
theorem Submission.codim1_rdo_dg_tma_hyperplane_param : ∀ (m : ℕ) (v : Euclid (m + 1)), v ≠ 0 → ∃ ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1), (∀ x, inner ℝ (ι x) v = 0) ∧ (μHE[m] : Measure (Euclid (m + 1))).restrict ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))) = Measure.map ι volume := by
  intro m v hv
  set K : Submodule ℝ (Euclid (m + 1)) := (Submodule.span ℝ {v})ᗮ with hKdef
  -- `dim P_v = m`
  have : Fact (Module.finrank ℝ (Euclid (m + 1)) = m + 1) := ⟨by simp⟩
  have hK : Module.finrank ℝ K = m := Submodule.finrank_orthogonal_span_singleton hv
  -- `ι = (P_v ↪ ℝ^{m+1}) ∘ e`, `e : ℝ^m ≃ P_v` the inverse coordinates of an orthonormal basis
  let b : OrthonormalBasis (Fin m) ℝ K := (stdOrthonormalBasis ℝ K).reindex (finCongr hK)
  let e : Euclid m ≃ₗᵢ[ℝ] K := b.repr.symm
  let ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1) := K.subtypeₗᵢ.comp e.toLinearIsometry
  have hιK : ∀ x, ι x ∈ K := fun x => (e x).2
  refine ⟨ι, ?_, ?_⟩
  · intro x
    have h := hιK x
    rw [hKdef, Submodule.mem_orthogonal_singleton_iff_inner_right] at h
    rw [real_inner_comm]
    exact h
  · have hrange : Set.range ι = (K : Set (Euclid (m + 1))) := by
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact hιK x
      · intro hz
        refine ⟨e.symm ⟨z, hz⟩, ?_⟩
        simp [ι]
    -- `ι_# Lᵐ = ι_# μHE[m] = μHE[m]⌞range ι`
    rw [← hrange, ← ι.isometry.map_euclideanHausdorffMeasure,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
/-- **Simon Ch. 3, 4.3 (†)** (boundary-parallel directions): if `⟨u, v⟩ = 0` and `h` is `C¹` with
compact support, then `∫_H Dh(w)(u) dw = 0` on the half-space `H = {w : ⟨w, v⟩ > 0}`.  `H` is
invariant under `w ↦ w + t u`, so `Φ(t) = ∫_H h(w + t u) dw` is constant by translation
invariance of Lebesgue measure; differentiating under the integral sign at `t = 0` gives
`Φ'(0) = ∫_H Dh(w)(u) dw = 0`. -/
theorem Submission.codim1_rdo_dg_tma_tangential_halfspace : ∀ (P : ℕ) (v u : Euclid P) (h : Euclid P → ℝ), inner ℝ u v = 0 → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid P | 0 < inner ℝ w v}, fderiv ℝ h w u = 0 := by
  intro P v u h huv hh hhc
  set H : Set (Euclid P) := {w | 0 < inner ℝ w v} with hHdef
  -- Step 1: `H` is open, hence measurable, and invariant under translation along `u`
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hHinv : ∀ (t : ℝ) (w : Euclid P), w + t • u ∈ H ↔ w ∈ H := by
    intro t w
    simp [hHdef, inner_add_left, real_inner_smul_left, huv]
  -- Step 2: `Φ(t) = ∫_H h(w + t u) dw` does not depend on `t`
  have hconst : ∀ t : ℝ, ∫ w in H, h (w + t • u) = ∫ w in H, h w := by
    intro t
    rw [← integral_indicator hHmeas, ← integral_indicator hHmeas]
    have hfun : (fun w => H.indicator (fun w => h (w + t • u)) w) =
        fun w => H.indicator h (w + t • u) := by
      funext w
      by_cases hw : w ∈ H
      · rw [indicator_of_mem hw, indicator_of_mem ((hHinv t w).2 hw)]
      · rw [indicator_of_notMem hw, indicator_of_notMem (fun h' => hw ((hHinv t w).1 h'))]
    rw [hfun, integral_add_right_eq_self (fun w => H.indicator h w) (t • u)]
  -- Step 3: `|Dh(w + t u)(u)| ≤ M‖u‖ 1_{B̄_{R+‖u‖}(0)}(w)` for `|t| < 1`
  obtain ⟨R, hR⟩ := hhc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  have hdc : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support (hhc.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set bound : Euclid P → ℝ :=
    (closedBall (0 : Euclid P) (R + ‖u‖)).indicator (fun _ => M * ‖u‖) with hbound
  have hhd : Differentiable ℝ h := hh.differentiable one_ne_zero
  -- Step 4: differentiation under the integral sign at `t = 0`
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict H) (F := fun (t : ℝ) w => h (w + t • u))
    (F' := fun (t : ℝ) w => fderiv ℝ h (w + t • u) u) (x₀ := (0 : ℝ)) (bound := bound)
    (ball_mem_nhds (0 : ℝ) one_pos)
    (Eventually.of_forall fun t => (hh.continuous.comp (by fun_prop)).aestronglyMeasurable)
    (by
      simp only [zero_smul, add_zero]
      exact (hh.continuous.integrable_of_hasCompactSupport hhc).integrableOn)
    ((hdc.clm_apply continuous_const).comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun w t ht => by
      by_cases hwt : w + t • u ∈ tsupport h
      · have h1 : ‖w + t • u‖ ≤ R := by simpa using hR hwt
        have ht1 : |t| < 1 := by simpa using ht
        have h2 : ‖w‖ ≤ R + ‖u‖ := by
          calc ‖w‖ = ‖(w + t • u) - t • u‖ := by simp
            _ ≤ ‖w + t • u‖ + ‖t • u‖ := norm_sub_le _ _
            _ ≤ R + ‖u‖ := by
                rw [norm_smul, Real.norm_eq_abs]
                nlinarith [abs_nonneg t, norm_nonneg u]
        rw [hbound, indicator_of_mem (by simpa using h2)]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
      · have : fderiv ℝ h (w + t • u) = 0 := by
          by_contra hne
          exact hwt (support_fderiv_subset ℝ hne)
        rw [this, zero_apply, norm_zero]
        exact indicator_nonneg (fun _ _ => mul_nonneg hM0 (norm_nonneg _)) _)
    ((integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (measure_closedBall_lt_top).ne)).integrableOn
    (Eventually.of_forall fun w t _ => by
      have h1 : HasDerivAt (fun t : ℝ => w + t • u) u t := by
        simpa using ((hasDerivAt_id t).smul_const u).const_add w
      exact ((hhd (w + t • u)).hasFDerivAt.comp_hasDerivAt t h1))
  -- Step 5: `Φ` is constant, so `Φ'(0) = ∫_H Dh(w)(u) dw` vanishes
  have h0 : HasDerivAt (fun t : ℝ => ∫ w in H, h (w + t • u)) 0 0 := by
    have hfun : (fun t : ℝ => ∫ w in H, h (w + t • u)) = fun _ => ∫ w in H, h w :=
      funext hconst
    rw [hfun]
    exact hasDerivAt_const _ _
  have := key.2.unique h0
  simpa using this
/-- **Orthogonal Fubini: `(x, s) ↦ ι x + s v` preserves Lebesgue measure** (Simon Ch. 3, 4.3 (†),
step 2 of the proof).  Let `ι : ℝᵐ → ℝᵐ⁺¹` be a linear isometry and `v` a unit vector orthogonal
to its range.  The vectors `b_j = ι(e_j)` (`j < m`) and `b_m = v` are orthonormal, so they form an
orthonormal basis `B` of `ℝᵐ⁺¹`, and `B.repr⁻¹ : c ↦ Σⱼ cⱼ bⱼ` preserves Lebesgue measure.  The
coordinate map `S(x, s) = (x₀, …, x_{m-1}, s)` sends `Lᵐ ⊗ L¹` to `Lᵐ⁺¹` (`ofLp × id`, swap, the
inverse of `piFinSuccAbove` at the last index, `toLp`).  Finally `B.repr⁻¹ (S(x, s)) =
Σ_{j<m} xⱼ ι(eⱼ) + s v = ι x + s v`, so the map is the composition `B.repr⁻¹ ∘ S`. -/
theorem Submission.codim1_rdo_dg_tma_orthogonal_fubini : ∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → MeasurePreserving (fun p : Euclid m × ℝ => ι p.1 + p.2 • v) volume volume := by
  intro m ι v hv hιv
  -- Step 1: the adapted orthonormal basis `(ι e₀, …, ι e_{m-1}, v)`
  let b : Fin (m + 1) → Euclid (m + 1) :=
    Fin.lastCases v (fun i => ι (EuclideanSpace.single i (1 : ℝ)))
  have hb_last : b (Fin.last m) = v := by simp [b]
  have hb_cs : ∀ i : Fin m, b (Fin.castSucc i) = ι (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    simp [b]
  have hb : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hb_last, hv]
      | cast j =>
        rw [hb_last, hb_cs, real_inner_comm, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := j.isLt
        simp
        omega
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        rw [hb_last, hb_cs, hιv]
        simp only [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
        have := i.isLt
        simp
        omega
      | cast j =>
        rw [hb_cs, hb_cs, LinearIsometry.inner_map_map, EuclideanSpace.inner_single_left]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Fin.castSucc_inj]
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Euclid (m + 1)) := by simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hb hcard,
      (basisOfOrthonormalOfCardEqFinrank hb hcard).span_eq]
  let B : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)) := OrthonormalBasis.mk hb hsp
  have hB : ∀ i, B i = b i := by
    intro i
    simp [B]
  -- Step 2: the coordinate map `S(x, s) = (x₀, …, x_{m-1}, s)` preserves Lebesgue measure
  let S : Euclid m × ℝ → EuclideanSpace ℝ (Fin (m + 1)) :=
    fun p => WithLp.toLp 2 (Fin.snoc (WithLp.ofLp p.1) p.2)
  have hS : MeasurePreserving S volume volume := by
    have h1 : MeasurePreserving (fun p : Euclid m × ℝ => (WithLp.ofLp p.1, p.2))
        ((volume : Measure (Euclid m)).prod (volume : Measure ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)) :=
      (PiLp.volume_preserving_ofLp (Fin m)).prod (MeasurePreserving.id volume)
    have h2 : MeasurePreserving (Prod.swap : (Fin m → ℝ) × ℝ → ℝ × (Fin m → ℝ))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      Measure.measurePreserving_swap
    have h3 := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm
    have h4 := PiLp.volume_preserving_toLp (Fin (m + 1))
    have := h4.comp (h3.comp (h2.comp h1))
    convert this using 1
    funext p
    simp [S, MeasurableEquiv.piFinSuccAbove]
    rfl
  -- Step 3: `B.repr⁻¹` preserves Lebesgue measure and `B.repr⁻¹ ∘ S = (x, s) ↦ ι x + s v`
  have hΦ : MeasurePreserving (B.repr.symm : EuclideanSpace ℝ (Fin (m + 1)) → Euclid (m + 1))
      volume volume := B.measurePreserving_repr_symm
  have := hΦ.comp hS
  convert this using 1
  funext p
  simp only [comp_apply, S]
  rw [← OrthonormalBasis.sum_repr_symm, Fin.sum_univ_castSucc]
  simp only [hB, hb_last, hb_cs, Fin.snoc_castSucc, Fin.snoc_last]
  congr 1
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr p.1]
  simp [map_sum, map_smul]
/-- **Normal derivative over a half-space** (Simon Ch. 3, proof of Theorem 4.3, p. 82: the
integration `∫_{ℝⁿ} ∫_H ∂_{n+1} φ(x′, x^{n+1}) dx^{n+1} dx′` in the normal variable).  If
`ι : ℝ^m → ℝ^{m+1}` is a linear isometry, `v` is a unit vector normal to its range and `h` is `C¹`
with compact support, then `∫_{⟨w, v⟩ > 0} Dh(w)(v) dw = -∫_{ℝ^m} h(ι x) dx`.  The coordinates
`Θ(x, s) = ι x + s v` preserve Lebesgue measure (`codim1_rdo_dg_tma_orthogonal_fubini`) and satisfy
`⟨Θ(x, s), v⟩ = s`, so Fubini turns the left side into `∫ dx ∫_{s > 0} ∂ₛ h(ι x + s v) ds`; the
fundamental theorem of calculus on `(0, ∞)` for the compactly supported `C¹` function
`s ↦ h(ι x + s v)` gives `-h(ι x)`. -/
theorem Submission.codim1_rdo_dg_tma_normal_halfspace : ∀ (m : ℕ) (ι : Euclid m →ₗᵢ[ℝ] Euclid (m + 1)) (v : Euclid (m + 1)) (h : Euclid (m + 1) → ℝ), ‖v‖ = 1 → (∀ x, inner ℝ (ι x) v = 0) → ContDiff ℝ 1 h → HasCompactSupport h → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, fderiv ℝ h w v = -∫ x, h (ι x) := by
  intro m ι v h hv hιv hh hhc
  -- `Θ(x, s) = ι x + s v` is measure preserving, and `⟨Θ(x, s), v⟩ = s`
  have hMP := Submission.codim1_rdo_dg_tma_orthogonal_fubini m ι v hv hιv
  set Θ : Euclid m × ℝ → Euclid (m + 1) := fun p => ι p.1 + p.2 • v with hΘdef
  set H : Set (Euclid (m + 1)) := {w | 0 < inner ℝ w v} with hHdef
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  have hΘv : ∀ p, inner ℝ (Θ p) v = p.2 := by
    intro p
    simp [hΘdef, inner_add_left, real_inner_smul_left, hιv, hv]
  -- the integrand `G = 1_H · Dh(·)(v)` is integrable
  set G : Euclid (m + 1) → ℝ := H.indicator (fun w => fderiv ℝ h w v) with hGdef
  have hdc : Continuous (fun w => fderiv ℝ h w v) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hGint : Integrable G :=
    (hdc.integrable_of_hasCompactSupport (hhc.fderiv_apply ℝ v)).indicator hHmeas
  -- change of variables `w = Θ(x, s)` and Fubini
  rw [← integral_indicator hHmeas]
  change ∫ w, G w = _
  have hGae : AEStronglyMeasurable G (Measure.map Θ volume) := by
    rw [hMP.map_eq]
    exact hGint.aestronglyMeasurable
  rw [← hMP.map_eq, integral_map hMP.measurable.aemeasurable hGae]
  have hGΘint : Integrable (fun p => G (Θ p)) ((volume : Measure (Euclid m)).prod volume) :=
    (integrable_map_measure hGae hMP.measurable.aemeasurable).1 (by rwa [hMP.map_eq])
  rw [Measure.volume_eq_prod, integral_prod _ hGΘint, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ∫ s, G (Θ (x, s)) = -h (ι x)
  -- for fixed `x`, the fundamental theorem of calculus for `k(s) = h(ι x + s v)` on `(0, ∞)`
  set k : ℝ → ℝ := fun s => h (ι x + s • v) with hkdef
  have hk : ContDiff ℝ 1 k := hh.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hiso : Isometry (fun s : ℝ => ι x + s • v) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul, hv, mul_one]
  have hkc : HasCompactSupport k := hhc.comp_isClosedEmbedding hiso.isClosedEmbedding
  have hderiv : ∀ s, deriv k s = fderiv ℝ h (ι x + s • v) v := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => ι x + s • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add (ι x)
    exact (((hh.differentiable one_ne_zero) (ι x + s • v)).hasFDerivAt.comp_hasDerivAt s h1).deriv
  have hFTC : ∫ s in Ioi 0, deriv k s = -h (ι x) := by
    rw [hkc.integral_Ioi_deriv_eq hk 0]
    simp [hkdef]
  -- compare the integrands: `Θ(x, s) ∈ H` exactly when `s > 0`
  rw [← hFTC, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [hGdef, hHdef, indicator_apply, mem_ofPred_eq, hΘv, mem_Ioi]
  split_ifs
  · rw [hderiv]
  · rfl

/-- **Gauss–Green for a half-space** (used in the proof of Simon Ch. 3, Theorem 4.3).  For
`|v| = 1` and `g ∈ C¹_c(ℝ^{m+1}; ℝ^{m+1})`,
`∫_{⟨w, v⟩ > 0} div g dL^{m+1} = −∫_{v^⊥} ⟨g, v⟩ dHᵐ`.  With `ι : ℝᵐ → v^⊥` from
`codim1_rdo_dg_tma_hyperplane_param`, `(ι e₀, …, ι e_{m−1}, v)` is an orthonormal basis `b`, so
`div g = Σⱼ D⟨bⱼ, g⟩(bⱼ)`.  The `m` tangential terms integrate to `0` over the half-space
(`codim1_rdo_dg_tma_tangential_halfspace`), the normal term is `−∫ ⟨v, g(ι x)⟩ dx`
(`codim1_rdo_dg_tma_normal_halfspace`), and `Hᵐ⌞v^⊥ = ι_# Lᵐ` turns it into the boundary
integral. -/
theorem Submission.codim1_rdo_dg_tma_halfspace_gauss_green : ∀ (m : ℕ) (v : Euclid (m + 1)) (g : Euclid (m + 1) → Euclid (m + 1)), ‖v‖ = 1 → ContDiff ℝ 1 g → HasCompactSupport g → ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m] := by
  intro m v g hv hg hgc
  have hv0 : v ≠ 0 := by
    rintro rfl
    simp at hv
  obtain ⟨ι, hιv, hmap⟩ := Submission.codim1_rdo_dg_tma_hyperplane_param m v hv0
  -- the adapted orthonormal basis `(ι e₀, …, ι e_{m-1}, v)`
  let b : Fin (m + 1) → Euclid (m + 1) :=
    Fin.lastCases v (fun i => ι (EuclideanSpace.single i (1 : ℝ)))
  have hb_last : b (Fin.last m) = v := by simp [b]
  have hb_cs : ∀ i : Fin m, b (Fin.castSucc i) = ι (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    simp [b]
  have hb : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite]
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [hb_last, hv]
      | cast j =>
        rw [hb_last, hb_cs, real_inner_comm, hιv, ite_eq_right (Fin.castSucc_lt_last j).ne']
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [hb_last, hb_cs, hιv, ite_eq_right (Fin.castSucc_lt_last i).ne]
      | cast j =>
        rw [hb_cs, hb_cs, LinearIsometry.inner_map_map, EuclideanSpace.inner_single_left]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij, Fin.castSucc_inj]
  have hcard : Fintype.card (Fin (m + 1)) = Module.finrank ℝ (Euclid (m + 1)) := by simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← coe_basisOfOrthonormalOfCardEqFinrank hb hcard,
      (basisOfOrthonormalOfCardEqFinrank hb hcard).span_eq]
  let B : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)) := OrthonormalBasis.mk hb hsp
  have hB : ∀ i, B i = b i := by
    intro i
    simp [B]
  -- scalar components
  set h : Fin (m + 1) → Euclid (m + 1) → ℝ := fun i w => inner ℝ (b i) (g w) with hhdef
  have hh_cd : ∀ i, ContDiff ℝ 1 (h i) := fun i => contDiff_const.inner ℝ hg
  have hh_cs : ∀ i, HasCompactSupport (h i) := by
    intro i
    exact hgc.mono' (fun w hw => by
      by_contra hgw
      exact hw (by simp [hhdef, image_eq_zero_of_notMem_tsupport hgw]))
  have hfd : ∀ i w, fderiv ℝ (h i) w (b i) =
      inner ℝ (b i) ((fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) (b i)) := by
    intro i w
    have hgd : DifferentiableAt ℝ g w := (hg.differentiable one_ne_zero) w
    rw [hhdef]
    simp only
    rw [fderiv_inner_apply ℝ (differentiableAt_const (b i)) hgd]
    simp
  have htr : ∀ w, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = ∑ i, fderiv ℝ (h i) w (b i) := by
    intro w
    rw [LinearMap.trace_eq_sum_inner _ B]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd, hB]
  have hint : ∀ i, Integrable (fun w => fderiv ℝ (h i) w (b i))
      (volume.restrict {w : Euclid (m + 1) | 0 < inner ℝ w v}) := by
    intro i
    have hc : Continuous (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cd i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hcs : HasCompactSupport (fun w => fderiv ℝ (h i) w (b i)) :=
      ((hh_cs i).fderiv ℝ).mono' (fun w hw => by
        by_contra hne
        exact hw (by simp [image_eq_zero_of_notMem_tsupport hne]))
    exact (hc.integrable_of_hasCompactSupport hcs).integrableOn
  simp_rw [htr]
  rw [integral_finsetSum _ (fun i _ => hint i), Fin.sum_univ_castSucc]
  -- the `m` tangential terms vanish
  have htan : ∀ i : Fin m, ∫ w in {w : Euclid (m + 1) | 0 < inner ℝ w v},
      fderiv ℝ (h (Fin.castSucc i)) w (b (Fin.castSucc i)) = 0 := by
    intro i
    exact Submission.codim1_rdo_dg_tma_tangential_halfspace (m + 1) v (b (Fin.castSucc i))
      (h (Fin.castSucc i)) (by rw [hb_cs]; exact hιv _) (hh_cd _) (hh_cs _)
  simp_rw [htan, Finset.sum_const_zero, zero_add]
  -- the normal term, and `Hᵐ⌞v^⊥ = ι_# Lᵐ`
  rw [hb_last]
  have hnorm := Submission.codim1_rdo_dg_tma_normal_halfspace m ι v (h (Fin.last m)) hv hιv
    (hh_cd _) (hh_cs _)
  rw [hnorm, hmap]
  congr 1
  have hcont : Continuous (fun z => inner ℝ (g z) v) := hg.continuous.inner continuous_const
  rw [integral_map ι.continuous.aemeasurable hcont.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [hhdef, hb_last, real_inner_comm]
/-- **Blow-up convergence of the vector measure `ν μ` on `C¹` vector fields** (Simon Ch. 3,
Theorem 4.3 (De Giorgi), chapter-03.txt lines 588–746: the closing step "by 4.1, (1) and (2)",
lines 739–746, with the change of variables (8), line 664).  Let `F` be Borel with
`∫_F div φ = −∫ ⟨φ, ν⟩ dμ` for every `C¹_c` field `φ` with `spt φ ⊆ D`, where `B̄_{ρ₁}(y) ⊆ D`,
and let the blow-ups `F_r = {w : y + r w ∈ F}` satisfy `L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0` as
`r ↓ 0` for every `R`, where `H = {w : ⟨w, v⟩ > 0}`, `|v| = 1`.  Then for every `C¹_c` field `g`,
`r⁻ᵐ ∫ ⟨g(r⁻¹(z − y)), ν(z)⟩ dμ(z) → ∫_{v^⊥} ⟨g, v⟩ dHᵐ` as `r ↓ 0`.  With `spt g ⊆ B_R(0)`, the
rescaled Gauss–Green identity turns the left side into `−∫_{F_r} div g` for `r < ρ₁/R`;
`|∫_{F_r} div g − ∫_H div g| ≤ sup |div g| · L^{m+1}((F_r Δ H) ∩ B_R(0)) → 0`; and the half-space
Gauss–Green formula gives `∫_H div g = −∫_{v^⊥} ⟨g, v⟩ dHᵐ`. -/
theorem Submission.codim1_rdo_dg_tma_vector_convergence : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < ρ₁ → closedBall y ρ₁ ⊆ D → ‖v‖ = 1 → (∀ R : ℝ, Tendsto (fun r : ℝ => volume (symmDiff ((fun w => y + r • w) ⁻¹' F) {w | 0 < inner ℝ w v} ∩ ball (0 : Euclid (m + 1)) R)) (𝓝[>] 0) (𝓝 0)) → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ) (𝓝[>] 0) (𝓝 (∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))), inner ℝ (g z) v ∂μHE[m])) := by
  intro m D F μ ν y v ρ₁ hF hGG hρ₁ hball hv hblow g hg hgc
  -- Step 1: `spt g ⊆ B_R(0)`.  `T = div g = trace Dg` is continuous and vanishes off `B_R(0)`
  -- (`Dg = 0` off `spt g`), so it is integrable and bounded by some `M`.
  obtain ⟨R, hRpos, hR⟩ : ∃ R : ℝ, 0 < R ∧ tsupport g ⊆ ball (0 : Euclid (m + 1)) R := by
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  set T : Euclid (m + 1) → ℝ := fun w =>
    LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
    with hTdef
  have hTcont : Continuous T := by
    have h1 : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
    have h2 : Continuous (fun A : Euclid (m + 1) →L[ℝ] Euclid (m + 1) =>
        LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))) :=
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h2.comp h1
  have hTzero : ∀ w, w ∉ ball (0 : Euclid (m + 1)) R → T w = 0 := by
    intro w hw
    have hw' : w ∉ tsupport g := fun h => hw (hR h)
    have : fderiv ℝ g w = 0 := by
      by_contra hne
      exact hw' (support_fderiv_subset ℝ hne)
    simp [hTdef, this]
  have hTcs : HasCompactSupport T := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) R) ?_
    intro w hw
    exact hTzero w (fun h => hw (ball_subset_closedBall h))
  obtain ⟨M, hM⟩ : ∃ M, ∀ w, ‖T w‖ ≤ M := hTcont.bounded_above_of_compact_support hTcs
  have hTint : Integrable T := hTcont.integrable_of_hasCompactSupport hTcs
  set H : Set (Euclid (m + 1)) := {w | 0 < inner ℝ w v}
  have hHmeas : MeasurableSet H :=
    (isOpen_lt continuous_const (continuous_id.inner continuous_const)).measurableSet
  -- Step 2: for `0 < r < ρ₁/R` and `w ∈ spt g`, `|(y + r w) − y| = r|w| < ρ₁`, so
  -- `y + r w ∈ B̄_{ρ₁}(y) ⊆ D` and the rescaled Gauss–Green identity gives
  -- `r⁻ᵐ ∫ ⟨g(r⁻¹(z − y)), ν⟩ dμ = −∫_{F_r} T`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), (r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ =
      -∫ w in (fun w => y + r • w) ⁻¹' F, T w := by
    have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
      nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    refine Submission.codim1_rdo_dg_tma_rescaled_gauss_green m D F μ ν y r g hF hGG hr hg hgc ?_
    intro w hw
    apply hball
    have hwR : ‖w‖ < R := by simpa using hR hw
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    have : r * ‖w‖ ≤ r * R := mul_le_mul_of_nonneg_left hwR.le hr.le
    have h2 : r * R < ρ₁ := by
      have := (lt_div_iff₀ hRpos).mp hrR
      linarith
    linarith
  -- Steps 3–4: `|∫_{F_r} T − ∫_H T| ≤ M · L^{m+1}((F_r Δ H) ∩ B_R(0))`, since the integrand
  -- `(1_{F_r} − 1_H) T` vanishes off `(F_r Δ H) ∩ B_R(0)` and is bounded by `M` there; the
  -- right side tends to `0` by the blow-up hypothesis.
  have hlim : Tendsto (fun r : ℝ => ∫ w in (fun w => y + r • w) ⁻¹' F, T w) (𝓝[>] 0)
      (𝓝 (∫ w in H, T w)) := by
    have hbound : ∀ r : ℝ, 0 < r → ‖(∫ w in (fun w => y + r • w) ⁻¹' F, T w) - ∫ w in H, T w‖ ≤
        M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal := by
      intro r hr
      have hFr : MeasurableSet ((fun w => y + r • w) ⁻¹' F) :=
        hF.preimage (by fun_prop)
      rw [← integral_indicator hFr, ← integral_indicator hHmeas, ← integral_sub
        (hTint.indicator hFr) (hTint.indicator hHmeas)]
      have hS : MeasurableSet (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) :=
        ((hFr.symmDiff hHmeas)).inter measurableSet_ball
      have hfin : volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R) ≠ ∞ :=
        (measure_mono inter_subset_right).trans_lt measure_ball_lt_top |>.ne
      calc ‖∫ w, ((fun w => y + r • w) ⁻¹' F).indicator T w - H.indicator T w‖
          ≤ ∫ w, (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R).indicator (fun _ => M) w := by
            have hInt : Integrable ((symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
                ball (0 : Euclid (m + 1)) R).indicator (fun _ => M)) :=
              (integrable_indicator_iff hS).2 (integrableOn_const hfin)
            refine norm_integral_le_of_norm_le hInt (Eventually.of_forall fun w => ?_)
            have hMabs : ∀ w, |T w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
            by_cases hwB : w ∈ ball (0 : Euclid (m + 1)) R
            · by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [h1, h2, hwB, Set.mem_symmDiff, hMabs, norm_neg]
            · have hT0 := hTzero w hwB
              by_cases h1 : w ∈ (fun w => y + r • w) ⁻¹' F <;> by_cases h2 : w ∈ H <;>
                simp [h1, h2, hwB, hT0, Set.mem_symmDiff]
        _ = M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
              ball (0 : Euclid (m + 1)) R)).toReal := by
            rw [integral_indicator_const _ hS, smul_eq_mul, mul_comm, Measure.real]
    have h0 : Tendsto (fun r : ℝ => M * (volume (symmDiff ((fun w => y + r • w) ⁻¹' F) H ∩
          ball (0 : Euclid (m + 1)) R)).toReal) (𝓝[>] 0) (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hblow R)
      simpa using this.const_mul M
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hbound r hr
  -- Steps 5–6: `∫_H T = −∫_{v^⊥} ⟨g, v⟩ dHᵐ` by the half-space Gauss–Green formula, so
  -- `−∫_{F_r} T → ∫_{v^⊥} ⟨g, v⟩ dHᵐ`; by Step 2 the rescaled `ν μ`-integrals eventually agree.
  have hGGH := Submission.codim1_rdo_dg_tma_halfspace_gauss_green m v g hv hg hgc
  have hneg := hlim.neg
  rw [show (∫ w in H, T w) = -∫ z in ((Submodule.span ℝ {v})ᗮ : Set (Euclid (m + 1))),
      inner ℝ (g z) v ∂μHE[m] from hGGH, neg_neg] at hneg
  exact hneg.congr' (hev.mono fun r hr => hr.symm)
/-- **Normal-defect estimate** (Simon Ch. 3, 4.3 (†), "by 4.1, (1) and (2)"): weighting by
`⟨v, ν⟩` does not change blow-up limits.  Write `B_ρ = B̄_ρ(y)` and
`A(ρ) = μ(B_ρ)⁻¹ ∫_{B_ρ} ν dμ`.  Choose `R ≥ 1` with `tsupport f ⊆ B̄_R(0)` and `|f| ≤ M`; then
`f(r⁻¹(z − y)) ≠ 0` forces `z ∈ B_{rR}`, where `μ ≤ C (rR)ⁿ < ∞`.  Splitting
`f = f ⟨v, ν⟩ + f (1 − ⟨v, ν⟩)` with `0 ≤ 1 − ⟨v, ν⟩ ≤ 2` (Cauchy–Schwarz), the defect
`Δ(r) = r⁻ⁿ ∫ f(r⁻¹(z − y)) (1 − ⟨v, ν(z)⟩) dμ(z)` satisfies
`|Δ(r)| ≤ r⁻ⁿ M ∫_{B_{rR}} (1 − ⟨v, ν⟩) dμ = r⁻ⁿ M μ(B_{rR}) (1 − ⟨v, A(rR)⟩)
  ≤ M C Rⁿ |1 − ⟨v, A(rR)⟩|`, which tends to `0` because `A(rR) → v` and `⟨v, v⟩ = 1`. -/
theorem Submission.codim1_rdo_dg_tma_normal_defect : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₁ C L : ℝ) (f : Euclid P → ℝ), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 L) → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 L) := by
  intro P n μ ν y v ρ₁ C L f hνm hν1 hv hρ₁ hC hdens hA hf hfc hL
  -- Step 1: `tsupport f ⊆ B̄_R(0)` with `R ≥ 1`, and `|f| ≤ M`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  have hM' : ∀ w, |f w| ≤ M := fun w => by simpa [Real.norm_eq_abs] using hM w
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM' 0)
  set A : ℝ → Euclid P := fun ρ =>
    (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ with hAdef
  -- Step 2: Cauchy–Schwarz, `|⟨v, ν(z)⟩| ≤ 1`
  have hinner_le : ∀ z, inner ℝ v (ν z) ≤ 1 := by
    intro z
    have := real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hinner_abs : ∀ z, |inner ℝ v (ν z)| ≤ 1 := by
    intro z
    have := abs_real_inner_le_norm v (ν z)
    rwa [hv, hν1, one_mul] at this
  have hνinner_meas : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hνm
  -- Steps 3–6: for `0 < r` with `rR < ρ₁`, `|Δ(r)| ≤ M C Rⁿ |1 − ⟨v, A(rR)⟩|`
  have hbound : ∀ r : ℝ, 0 < r → r * R < ρ₁ →
      |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ| ≤
        M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
    intro r hr hrR
    set B := closedBall y (r * R) with hBdef
    have hBμ : μ B ≤ ENNReal.ofReal (C * (r * R) ^ n) := hdens _ (by positivity) hrR
    have hBfin : μ B ≠ ∞ := (hBμ.trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → f (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hR (subset_tsupport f hne)
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => f (r⁻¹ • (z - y))) := by fun_prop
    -- Step 3: integrability
    have hint1 : Integrable (fun z => f (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := M)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hM' _)
    have hint2 : Integrable (fun z => f (r⁻¹ • (z - y)) * inner ℝ v (ν z)) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_
        (fun z hz => by rw [hsupp z hz, zero_mul])
      refine Measure.integrableOn_of_bounded hBfin
        (hcont.aestronglyMeasurable.mul hνinner_meas.aestronglyMeasurable) (M := M)
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |f (r⁻¹ • (z - y))| * |inner ℝ v (ν z)| ≤ M * 1 :=
            mul_le_mul (hM' _) (hinner_abs z) (abs_nonneg _) hM0
        _ = M := mul_one M
    have hνint : IntegrableOn ν B μ :=
      Measure.integrableOn_of_bounded hBfin hνm.aestronglyMeasurable (M := 1)
        (Eventually.of_forall fun z => (hν1 z).le)
    -- Step 5: `∫_B (1 − ⟨v, ν⟩) dμ = μ(B) (1 − ⟨v, A(rR)⟩)`
    have hkey : ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ =
        (μ B).toReal * (1 - inner ℝ v (A (r * R))) := by
      have hint3 : IntegrableOn (fun z => inner ℝ v (ν z)) B μ :=
        Measure.integrableOn_of_bounded hBfin hνinner_meas.aestronglyMeasurable (M := 1)
          (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hinner_abs z)
      rw [integral_sub (integrableOn_const (C := (1 : ℝ)) hBfin) hint3, setIntegral_const,
        smul_eq_mul, mul_one]
      have hcomm : ∫ z in B, inner ℝ v (ν z) ∂μ = inner ℝ v (∫ z in B, ν z ∂μ) := by
        have := ContinuousLinearMap.integral_comp_comm (innerSL ℝ v) hνint
        simpa using this
      rw [hcomm, Measure.real]
      by_cases h0 : (μ B).toReal = 0
      · have hμ0 : μ B = 0 := by
          rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h | h
          · exact h
          · exact absurd h hBfin
        have : ∫ z in B, ν z ∂μ = 0 := by
          rw [Measure.restrict_eq_zero.2 hμ0, integral_zero_measure]
        rw [this, h0]
        simp
      · simp only [hAdef]
        rw [← hBdef, real_inner_smul_right]
        field_simp
    -- Step 4: splitting and the pointwise bound `|f (1 − ⟨v, ν⟩)| ≤ M (1 − ⟨v, ν⟩) 1_B`
    have hdiff : (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ =
        (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ := by
      rw [← mul_sub, ← integral_sub hint1 hint2]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      ring
    have hle : |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ| ≤
        M * ∫ z in B, (1 - inner ℝ v (ν z)) ∂μ := by
      have hbint : Integrable (fun z => B.indicator (fun z => M * (1 - inner ℝ v (ν z))) z) μ := by
        refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
        refine Measure.integrableOn_of_bounded hBfin
          (aestronglyMeasurable_const.mul
            (aestronglyMeasurable_const.sub hνinner_meas.aestronglyMeasurable)) (M := M * 2)
          (Eventually.of_forall fun z => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM0]
        refine mul_le_mul_of_nonneg_left ?_ hM0
        have := hinner_abs z
        rw [abs_le] at this ⊢
        constructor <;> linarith [this.1, this.2]
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hbint (Eventually.of_forall fun z => ?_)).trans ?_
      · by_cases hz : z ∈ B
        · rw [indicator_of_mem hz, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (sub_nonneg.2 (hinner_le z))]
          exact mul_le_mul_of_nonneg_right (hM' _) (sub_nonneg.2 (hinner_le z))
        · rw [indicator_of_notMem hz, hsupp z hz, zero_mul, norm_zero]
      · rw [integral_indicator measurableSet_closedBall, integral_const_mul]
    -- Step 6: `μ(B_{rR}) ≤ C (rR)ⁿ`
    have hμB : (μ B).toReal ≤ C * (r * R) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hBμ
    rw [hdiff, abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, f (r⁻¹ • (z - y)) * (1 - inner ℝ v (ν z)) ∂μ|
        ≤ (r ^ n)⁻¹ * (M * ((μ B).toReal * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
          refine hle.trans ?_
          rw [hkey]
          gcongr
          exact le_abs_self _
      _ ≤ (r ^ n)⁻¹ * (M * ((C * (r * R) ^ n) * |1 - inner ℝ v (A (r * R))|)) := by
          gcongr
      _ = M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))| := by
          rw [mul_pow]
          field_simp
  -- Step 7: `A(rR) → v`, so the bound tends to `0`
  have hAr : Tendsto (fun r : ℝ => A (r * R)) (𝓝[>] 0) (𝓝 v) := by
    refine hA.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const R
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hin : Tendsto (fun r : ℝ => inner ℝ v (A (r * R))) (𝓝[>] 0) (𝓝 1) := by
    have hic : Continuous (fun w : Euclid P => inner ℝ v w) := continuous_const.inner continuous_id
    have := (hic.tendsto v).comp hAr
    simpa [Function.comp_def, real_inner_self_eq_norm_sq, hv] using this
  have h0 : Tendsto (fun r : ℝ => M * (C * R ^ n) * |1 - inner ℝ v (A (r * R))|) (𝓝[>] 0)
      (𝓝 0) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hin).abs.const_mul (M * (C * R ^ n))
    simpa using this
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / R :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hRpos))
  have hΔ : Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ -
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ h0
    filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrR
    exact hbound r hr (by have := (lt_div_iff₀ hRpos).mp hrR; linarith)
  -- Step 8: `r⁻ⁿ ∫ f(r⁻¹(z − y)) dμ = r⁻ⁿ ∫ f(r⁻¹(z − y)) ⟨v, ν(z)⟩ dμ + Δ(r) → L`
  have := hL.add hΔ
  simpa using this
/-- **Uniform `C¹` approximation with support control** (Simon Ch. 3, proof of Theorem 4.3
(De Giorgi): "mollifying, there is `f_θ ∈ C_c^∞` with `spt f_θ ⊆ B_{R+1}(0)` and
`‖f − f_θ‖_∞ ≤ θ`").  `f` has compact support, so it is uniformly continuous; pick a modulus
`δ ≤ 1` for `θ`.  Convolving `f` with a nonnegative `C¹` bump `ψ`, `∫ ψ = 1`,
`spt ψ ⊆ B_δ(0)`, gives a `C¹` function `g` with `spt g ⊆ B_δ(0) + B̄_R(0) ⊆ B̄_{R+1}(0)` and
`|g(x) − f(x)| ≤ ∫ ψ(t) |f(x − t) − f(x)| dt ≤ θ`. -/
theorem Submission.codim1_rdo_dg_tma_smooth_approx : ∀ (P : ℕ) (f : Euclid P → ℝ) (R θ : ℝ), Continuous f → tsupport f ⊆ closedBall (0 : Euclid P) R → 0 < θ → ∃ g : Euclid P → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ tsupport g ⊆ closedBall (0 : Euclid P) (R + 1) ∧ ∀ x, |f x - g x| ≤ θ := by
  intro P f R θ hf hR hθ
  -- `f` is uniformly continuous; `δ = min δ₀ 1` is a modulus for `θ`
  have hfc : HasCompactSupport f :=
    (isCompact_closedBall (0 : Euclid P) R).of_isClosed_subset (isClosed_tsupport f) hR
  have huc : UniformContinuous f := hfc.uniformContinuous_of_continuous hf
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.1 huc θ hθ
  set δ := min δ₀ 1 with hδdef
  have hδpos : 0 < δ := lt_min hδ₀ one_pos
  -- the normalized bump `ψ = c⁻¹ ψ₀`, `c = ∫ ψ₀ > 0`
  obtain ⟨ψ₀, hψ₀ts, hψ₀c, hψ₀s, hψ₀r, hψ₀0⟩ :=
    exists_contDiff_tsupport_subset (E := Euclid P) (s := ball (0 : Euclid P) δ) (x := 0)
      (n := 1) (ball_mem_nhds 0 hδpos)
  have hψ₀nn : ∀ x, 0 ≤ ψ₀ x := fun x => (hψ₀r ⟨x, rfl⟩).1
  set c := ∫ x, ψ₀ x with hcdef
  have hc : 0 < c :=
    hψ₀s.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hψ₀c hψ₀nn
      (by rw [hψ₀0]; norm_num)
  set ψ : Euclid P → ℝ := fun x => c⁻¹ * ψ₀ x with hψdef
  have hψs : ContDiff ℝ 1 ψ := contDiff_const.mul hψ₀s
  have hψc : HasCompactSupport ψ := hψ₀c.mul_left
  have hψnn : ∀ x, 0 ≤ ψ x := fun x => mul_nonneg (inv_nonneg.2 hc.le) (hψ₀nn x)
  have hψint : ∫ x, ψ x = 1 := by
    rw [hψdef, integral_const_mul, ← hcdef, inv_mul_cancel₀ hc.ne']
  have hψsupp : ∀ t, ψ t ≠ 0 → ‖t‖ < δ := by
    intro t ht
    have : t ∈ tsupport ψ₀ := subset_tsupport ψ₀ (fun h0 => ht (by simp [hψdef, h0]))
    simpa using hψ₀ts this
  -- `g = ψ ⋆ f` is `C¹`
  set g : Euclid P → ℝ := convolution ψ f (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgdef
  have hg : ContDiff ℝ 1 g :=
    hψc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hψs hf.locallyIntegrable
  have hgval : ∀ x, g x = ∫ t, ψ t * f (x - t) := by
    intro x
    rw [hgdef, convolution_def]
    simp
  -- `spt g ⊆ spt ψ + spt f ⊆ B̄_{R+1}(0)`
  have hgsupp : support g ⊆ closedBall (0 : Euclid P) (R + 1) := by
    refine (support_convolution_subset _).trans ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    have ha' : ‖a‖ < δ := hψsupp a ha
    have hb' : ‖b‖ ≤ R := by simpa using hR (subset_tsupport f hb)
    rw [mem_closedBall, dist_zero_right]
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ R + 1 := by
          have : δ ≤ 1 := min_le_right _ _
          linarith
  have hgts : tsupport g ⊆ closedBall (0 : Euclid P) (R + 1) :=
    closure_minimal hgsupp isClosed_closedBall
  refine ⟨g, hg, (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport g) hgts,
    hgts, fun x => ?_⟩
  -- `g x − f x = ∫ ψ(t) (f(x − t) − f(x)) dt`, and the integrand is at most `ψ(t) θ`
  have hint1 : Integrable (fun t => ψ t * f (x - t)) :=
    (hψs.continuous.mul (hf.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hψc.mul_right
  have hint2 : Integrable (fun t => ψ t * f x) :=
    (hψs.continuous.integrable_of_hasCompactSupport hψc).mul_const _
  have hdiff : g x - f x = ∫ t, ψ t * (f (x - t) - f x) := by
    simp_rw [hgval, mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, hψint, one_mul]
  rw [abs_sub_comm, hdiff]
  calc |∫ t, ψ t * (f (x - t) - f x)| ≤ ∫ t, ψ t * θ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le
          ((hψs.continuous.integrable_of_hasCompactSupport hψc).mul_const _)
          (Eventually.of_forall fun t => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hψnn t)]
        by_cases ht : ψ t = 0
        · simp [ht]
        · refine mul_le_mul_of_nonneg_left ?_ (hψnn t)
          have h1 : dist (x - t) x < δ₀ := by
            rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
            exact (hψsupp t ht).trans_le (min_le_left _ _)
          exact (by simpa [Real.dist_eq] using (hδ h1).le)
    _ = θ := by rw [integral_mul_const, hψint, one_mul]

/-- **Blow-up convergence extends from `C¹` to continuous test functions** (Simon Ch. 3, 4.3 (†),
step 5 of the tangent-measure argument in De Giorgi's theorem; used for 7.5.8).  Let
`μ(B̄_ρ(y)) ≤ C ρⁿ` for `0 < ρ < ρ₁` and let `τ` be finite on closed balls.  If
`r⁻ⁿ ∫ g(r⁻¹(z − y)) dμ(z) → ∫ g dτ` as `r ↓ 0` for every `C¹` compactly supported `g`, the same
holds for every continuous compactly supported `f`.  With `tsupport f ⊆ B̄_R(0)`, `S = R + 1` and
`g` the `θ`-approximation of `f` given by `Submission.codim1_rdo_dg_tma_smooth_approx`,
`|r⁻ⁿ ∫ (f − g)(r⁻¹(z − y)) dμ| ≤ θ C Sⁿ` whenever `rS < ρ₁`, and `|∫ (f − g) dτ| ≤ θ τ(B̄_S(0))`;
take `θ = ε/(4K)` with `K = C Sⁿ + τ(B̄_S(0)) + 1`. -/
theorem Submission.codim1_rdo_dg_tma_continuous_extension : ∀ (P n : ℕ) (μ τ : Measure (Euclid P)) (y : Euclid P) (ρ₁ C : ℝ), 0 < ρ₁ → 0 ≤ C → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ R : ℝ, τ (closedBall (0 : Euclid P) R) ≠ ∞) → (∀ g : Euclid P → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, g z ∂τ))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ) (𝓝[>] 0) (𝓝 (∫ z, f z ∂τ)) := by
  intro P n μ τ y ρ₁ C hρ₁ hC hdens hτ hsmooth f hf hfc
  -- Step 1: `tsupport f ⊆ B̄_R(0)` with `R ≥ 0`, and `S = R + 1`.
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : tsupport f ⊆ closedBall 0 R :=
    hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  set S := R + 1 with hSdef
  have hS : 0 < S := by positivity
  -- Step 2: if `φ` is continuous, `|φ| ≤ c`, `φ = 0` off `B̄_S(0)` and `rS < ρ₁`, then
  -- `z ↦ φ(r⁻¹(z − y))` vanishes off `B̄_{rS}(y)`, is `μ`-integrable, and
  -- `|r⁻ⁿ ∫ φ(r⁻¹(z − y)) dμ| ≤ r⁻ⁿ c μ(B̄_{rS}(y)) ≤ c C Sⁿ`.
  have key : ∀ (φ : Euclid P → ℝ) (c r : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) → 0 < r → r * S < ρ₁ →
      Integrable (fun z => φ (r⁻¹ • (z - y))) μ ∧
        |(r ^ n)⁻¹ * ∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (C * S ^ n) := by
    intro φ c r hφ hφc hφs hr hrS
    set B := closedBall y (r * S) with hBdef
    have hBfin : μ B ≠ ∞ :=
      ((hdens (r * S) (by positivity) hrS).trans_lt ENNReal.ofReal_lt_top).ne
    have hsupp : ∀ z, z ∉ B → φ (r⁻¹ • (z - y)) = 0 := by
      intro z hz
      by_contra hne
      have h1 := hφs _ hne
      apply hz
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
        at h1
      rw [hBdef, mem_closedBall, dist_eq_norm]
      calc ‖z - y‖ = r * (r⁻¹ * ‖z - y‖) := by field_simp
        _ ≤ r * S := mul_le_mul_of_nonneg_left h1 hr.le
    have hcont : Continuous (fun z => φ (r⁻¹ • (z - y))) := by fun_prop
    have hint : Integrable (fun z => φ (r⁻¹ • (z - y))) μ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hcont.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have hc0 : 0 ≤ c := (abs_nonneg _).trans (hφc 0)
    have hle : |∫ z, φ (r⁻¹ • (z - y)) ∂μ| ≤ c * (μ B).toReal := by
      have h2 : ‖∫ z, φ (r⁻¹ • (z - y)) ∂μ‖ ≤ ∫ z, B.indicator (fun _ => c) z ∂μ := by
        refine norm_integral_le_of_norm_le
          ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
          (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ B
        · rw [indicator_of_mem hz]
          simpa [Real.norm_eq_abs] using hφc _
        · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
      rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
      simpa [Real.norm_eq_abs, mul_comm] using h2
    have hμ : (μ B).toReal ≤ C * (r * S) ^ n :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) (hdens _ (by positivity) hrS)
    rw [abs_mul, abs_of_pos (inv_pos.2 (pow_pos hr n))]
    calc (r ^ n)⁻¹ * |∫ z, φ (r⁻¹ • (z - y)) ∂μ|
        ≤ (r ^ n)⁻¹ * (c * (C * (r * S) ^ n)) := by
          gcongr
          exact hle.trans (mul_le_mul_of_nonneg_left hμ hc0)
      _ = c * (C * S ^ n) := by
          rw [mul_pow]
          field_simp
  -- Step 3: for `φ` as in step 2, `φ` is `τ`-integrable and `|∫ φ dτ| ≤ c T`,
  -- `T = τ(B̄_S(0))`.
  set T := (τ (closedBall (0 : Euclid P) S)).toReal with hTdef
  have keyτ : ∀ (φ : Euclid P → ℝ) (c : ℝ), Continuous φ → (∀ w, |φ w| ≤ c) →
      (∀ w, φ w ≠ 0 → w ∈ closedBall (0 : Euclid P) S) →
      Integrable φ τ ∧ |∫ z, φ z ∂τ| ≤ c * T := by
    intro φ c hφ hφc hφs
    have hBfin := hτ S
    have hsupp : ∀ z, z ∉ closedBall (0 : Euclid P) S → φ z = 0 := by
      intro z hz
      by_contra hne
      exact hz (hφs z hne)
    have hint : Integrable φ τ := by
      refine IntegrableOn.integrable_of_forall_notMem_eq_zero ?_ hsupp
      exact Measure.integrableOn_of_bounded hBfin hφ.aestronglyMeasurable (M := c)
        (Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hφc _)
    refine ⟨hint, ?_⟩
    have h2 : ‖∫ z, φ z ∂τ‖ ≤ ∫ z, (closedBall (0 : Euclid P) S).indicator (fun _ => c) z ∂τ := by
      refine norm_integral_le_of_norm_le
        ((integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const hBfin))
        (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ closedBall (0 : Euclid P) S
      · rw [indicator_of_mem hz]
        simpa [Real.norm_eq_abs] using hφc _
      · rw [indicator_of_notMem hz, hsupp z hz, norm_zero]
    rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real] at h2
    simpa [Real.norm_eq_abs, mul_comm, hTdef] using h2
  -- `f` is bounded and vanishes off `B̄_S(0)`; `K = C Sⁿ + T + 1 > 0`.
  have hfs : ∀ w, f w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    have := hR (subset_tsupport f hw)
    exact closedBall_subset_closedBall (by linarith) this
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfc
  have hMf' : ∀ w, |f w| ≤ Mf := fun w => by simpa [Real.norm_eq_abs] using hMf w
  set K := C * S ^ n + T + 1 with hKdef
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hK : 0 < K := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- Step 4: `g ∈ C¹_c` with `tsupport g ⊆ B̄_S(0)` and `|f − g| ≤ θ = ε/(4K)`.
  set θ := ε / (4 * K) with hθdef
  have hθ : 0 < θ := by positivity
  obtain ⟨g, hg, hgc, hgs, hfg⟩ :=
    Submission.codim1_rdo_dg_tma_smooth_approx P f R θ hf hR hθ
  have hgs' : ∀ w, g w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := fun w hw =>
    hgs (subset_tsupport g hw)
  obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hMg' : ∀ w, |g w| ≤ Mg := fun w => by simpa [Real.norm_eq_abs] using hMg w
  -- Step 5: eventually `|r⁻ⁿ ∫ g(r⁻¹(z − y)) dμ − ∫ g dτ| < ε/2`, and `r < ρ₁/S`.
  have hlim := Metric.tendsto_nhds.1 (hsmooth g hg hgc) (ε / 2) (by positivity)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < ρ₁ / S :=
    nhdsWithin_le_nhds (gt_mem_nhds (div_pos hρ₁ hS))
  filter_upwards [hlim, self_mem_nhdsWithin, hsmall] with r hr1 hr hrS
  have hrS' : r * S < ρ₁ := by
    have := (lt_div_iff₀ hS).mp hrS
    linarith
  -- Step 6: the `θ`-bounds for `f − g` from steps 2 and 3.
  have hdiff_s : ∀ w, (f - g) w ≠ 0 → w ∈ closedBall (0 : Euclid P) S := by
    intro w hw
    by_cases hfw : f w = 0
    · have : g w ≠ 0 := by
        intro hgw
        apply hw
        simp [hfw, hgw]
      exact hgs' w this
    · exact hfs w hfw
  have hd : ∀ w, |(f - g) w| ≤ θ := fun w => by simpa using hfg w
  obtain ⟨hint_f, -⟩ := key f Mf r hf hMf' hfs hr hrS'
  obtain ⟨hint_g, -⟩ := key g Mg r hg.continuous hMg' hgs' hr hrS'
  obtain ⟨-, hest⟩ := key (f - g) θ r (hf.sub hg.continuous) hd hdiff_s hr hrS'
  obtain ⟨hτf, -⟩ := keyτ f Mf hf hMf' hfs
  obtain ⟨hτg, -⟩ := keyτ g Mg hg.continuous hMg' hgs'
  obtain ⟨-, hestτ⟩ := keyτ (f - g) θ (hf.sub hg.continuous) hd hdiff_s
  have e1 : (r ^ n)⁻¹ * ∫ z, (f - g) (r⁻¹ • (z - y)) ∂μ =
      (r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ := by
    rw [← mul_sub, ← integral_sub hint_f hint_g]
    rfl
  have e2 : ∫ z, (f - g) z ∂τ = ∫ z, f z ∂τ - ∫ z, g z ∂τ := by
    rw [← integral_sub hτf hτg]
    rfl
  rw [e1] at hest
  rw [e2] at hestτ
  -- Step 7: the triangle inequality gives `< θ K + ε/2 = 3ε/4`.
  rw [Real.dist_eq] at hr1 ⊢
  have hθK : θ * (C * S ^ n) + θ * T ≤ ε / 2 := by
    have h1 : θ * (C * S ^ n) + θ * T ≤ θ * K := by
      rw [hKdef]
      nlinarith
    have h2 : θ * K = ε / 4 := by
      rw [hθdef]
      field_simp
    linarith
  calc |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - ∫ z, f z ∂τ|
      = |((r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ)
          + ((r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ)
          - (∫ z, f z ∂τ - ∫ z, g z ∂τ)| := by ring_nf
    _ ≤ |(r ^ n)⁻¹ * ∫ z, f (r⁻¹ • (z - y)) ∂μ - (r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ|
          + |(r ^ n)⁻¹ * ∫ z, g (r⁻¹ • (z - y)) ∂μ - ∫ z, g z ∂τ|
          + |∫ z, f z ∂τ - ∫ z, g z ∂τ| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < θ * (C * S ^ n) + ε / 2 + θ * T := by
        have := hr1
        linarith
    _ ≤ ε := by linarith
/-- **Differentiation of the unit normal** (Simon Ch. 3, (4.2); Ch. 1, 3.23): if `μ` is carried
by the open set `D` and is finite on compact subsets of `D`, then for `μ`-a.e. `y` the averages of
the bounded Borel field `ν` over `B̄_ρ(y)` tend to `ν(y)` as `ρ ↓ 0`.  Exhaust `D` by the compact
sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ)`; for the finite measure `μ⌞K a b` this is Mathlib's
Lebesgue–Besicovitch differentiation theorem along closed balls (`ae_tendsto_average` for
`Besicovitch.vitaliFamily`, with `Besicovitch.tendsto_filterAt`), and near a point of `D` the
averages for `μ` and for `μ⌞K a b` coincide. -/
theorem Submission.codim1_rdo_dg_normal_average_ae : ∀ (m : ℕ) (D : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), IsOpen D → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ y, ‖ν y‖ = 1) → ∀ᵐ y ∂μ, y ∈ D ∧ Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 (ν y)) := by
  intro m D μ ν hD hDc hK hν hν1
  -- the compact sets `K a b = B̄_a(0) \ U_{1/(b+1)}(Dᶜ) ⊆ D`
  let K : ℕ → ℕ → Set (Euclid (m + 1)) := fun a b =>
    closedBall 0 a \ thickening (1 / ((b : ℝ) + 1)) Dᶜ
  have hKc : ∀ a b, IsCompact (K a b) := fun a b =>
    (isCompact_closedBall _ _).diff isOpen_thickening
  have hKD : ∀ a b, K a b ⊆ D := fun a b x hx => by
    by_contra hxD
    exact hx.2 (self_subset_thickening (by positivity) _ hxD)
  -- Besicovitch differentiation of `ν` for the finite measures `μ⌞K a b`
  have hdiff : ∀ a b, ∀ᵐ y ∂μ, y ∈ K a b → Tendsto
      (fun ρ : ℝ => ⨍ z in closedBall y ρ, ν z ∂(μ.restrict (K a b))) (𝓝[>] 0) (𝓝 (ν y)) := by
    intro a b
    have : IsFiniteMeasure (μ.restrict (K a b)) :=
      isFiniteMeasure_restrict.2 (hK _ (hKc a b) (hKD a b))
    have hint : Integrable ν (μ.restrict (K a b)) :=
      Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun y => (hν1 y).le)
    have h := (Besicovitch.vitaliFamily (μ.restrict (K a b))).ae_tendsto_average
      hint.locallyIntegrable
    rw [ae_restrict_iff' (hKc a b).isClosed.measurableSet] at h
    filter_upwards [h] with y hy hyK
    exact (hy hyK).comp (Besicovitch.tendsto_filterAt _ y)
  -- `μ`-a.e. point lies in `D`
  have hDae : ∀ᵐ y ∂μ, y ∈ D := by
    have h := compl_mem_ae_iff.2 hDc
    rwa [compl_compl] at h
  filter_upwards [hDae, ae_all_iff.2 fun a => ae_all_iff.2 (hdiff a)] with y hyD hy
  refine ⟨hyD, ?_⟩
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hD y hyD
  obtain ⟨a, ha⟩ := exists_nat_ge (‖y‖ + 1)
  obtain ⟨b, hb⟩ := exists_nat_one_div_lt (half_pos hε)
  -- `B̄_ρ(y) ⊆ K a b` for `ρ < min 1 (ε / 2)`
  have hsub : ∀ ρ : ℝ, ρ < 1 → ρ < ε / 2 → closedBall y ρ ⊆ K a b := by
    intro ρ hρ1 hρε z hz
    refine ⟨?_, fun hzt => ?_⟩
    · rw [mem_closedBall_zero_iff]
      have := norm_le_of_mem_closedBall hz
      linarith
    · obtain ⟨w, hwD, hzw⟩ := mem_thickening_iff.1 hzt
      apply hwD
      apply hεD
      rw [mem_ball]
      have hzy := mem_closedBall.1 hz
      rw [dist_comm] at hzw
      calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ < ε := by linarith
  have hyK : y ∈ K a b := hsub 0 one_pos (half_pos hε) (mem_closedBall_self le_rfl)
  -- for small `ρ` the averages for `μ⌞K a b` and for `μ` over `B̄_ρ(y)` coincide
  refine (hy a b hyK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos (half_pos hε))] with ρ hρ
  have hρK := hsub ρ (hρ.2.trans_le (min_le_left _ _)) (hρ.2.trans_le (min_le_right _ _))
  rw [setAverage_eq, measureReal_def, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hρK, Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hρK]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
