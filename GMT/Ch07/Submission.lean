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

/-- Difference quotients `r⁻¹(f(v + rw) − f(v))` of a map differentiable at `v` converge to
`Df(v)w` uniformly on every closed ball `B̄_R(0)` as `r ↓ 0` (the `o(|h|)` estimate in the
weighted blow-up limit of the Allard graph step).  With `R' = max R 1`, pick `ρ > 0` such that
`|f(v + h) − f(v) − Df(v)h| ≤ ε|h|/(2R')` for `|h| < ρ`.  For `0 < r < ρ/R'` and `|w| ≤ R`,
`|rw| < ρ`, and linearity of `Df(v)` gives `|Df(v)w − r⁻¹(f(v + rw) − f(v))| ≤ ε|w|/(2R') < ε`. -/
theorem Submission.dorwbl_diff_quotient_tendstoUniformlyOn : ∀ (n k : ℕ) (f : Euclid n → Euclid k) (v : Euclid n), DifferentiableAt ℝ f v → ∀ R : ℝ, TendstoUniformlyOn (fun (r : ℝ) (w : Euclid n) => r⁻¹ • (f (v + r • w) - f v)) (fun w => fderiv ℝ f v w) (𝓝[>] 0) (closedBall (0 : Euclid n) R) := by
  intro n k f v hf R
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hR : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hc : 0 < ε / (2 * max R 1) := by positivity
  obtain ⟨ρ, hρ, hsmall⟩ := Metric.eventually_nhds_iff.1
    ((hasFDerivAt_iff_isLittleO_nhds_zero.1 hf.hasFDerivAt).bound hc)
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ρ / max R 1 by positivity)] with r hr w hw
  obtain ⟨hr0, hrρ⟩ := hr
  have hw' : ‖w‖ ≤ max R 1 := (mem_closedBall_zero_iff.1 hw).trans (le_max_left R 1)
  have hrw : ‖r • w‖ = r * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg hr0.le]
  -- `|rw| ≤ rR' < ρ`, so the little-o bound applies to `h = rw`
  have hbound := hsmall (show dist (r • w) 0 < ρ by
    rw [dist_zero_right, hrw]
    calc r * ‖w‖ ≤ r * max R 1 := mul_le_mul_of_nonneg_left hw' hr0.le
      _ < ρ / max R 1 * max R 1 := mul_lt_mul_of_pos_right hrρ hR
      _ = ρ := div_mul_cancel₀ ρ hR.ne')
  -- `Df(v)w − r⁻¹(f(v + rw) − f(v)) = −r⁻¹(f(v + rw) − f(v) − Df(v)(rw))`
  have hid : fderiv ℝ f v w - r⁻¹ • (f (v + r • w) - f v) =
      -(r⁻¹ • (f (v + r • w) - f v - fderiv ℝ f v (r • w))) := by
    simp only [map_smul, smul_sub, smul_smul, inv_mul_cancel₀ hr0.ne', one_smul]
    abel
  rw [dist_eq_norm, hid, norm_neg, norm_smul, norm_inv, Real.norm_of_nonneg hr0.le]
  calc r⁻¹ * ‖f (v + r • w) - f v - fderiv ℝ f v (r • w)‖
      ≤ r⁻¹ * (ε / (2 * max R 1) * ‖r • w‖) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hr0.le)
    _ = ε / (2 * max R 1) * ‖w‖ := by
        rw [hrw]
        field_simp
    _ ≤ ε / (2 * max R 1) * max R 1 := mul_le_mul_of_nonneg_left hw' hc.le
    _ = ε / 2 := by field_simp
    _ < ε := half_lt_self hε

/-- Rescaled area integrals at a rescaled Lebesgue point of `g₀ = 1_B·J`: with
`Φ_r(c) = r⁻¹(F(b + rc) − F(b))` and `Λ = DF(b)` injective, `∫ g₀(b + rc) f(Φ_r(c)) dc` tends to
`J(b) ∫ f(Λc) dc` as `r ↓ 0`.  Injectivity gives `|c| ≤ κ|Λc|`; with `spt f ⊆ B̄_{R₁}(0)` and
`|f| ≤ M`, the co-Lipschitz bound at `b` makes both integrands vanish off `D = B̄_ρ(0)`,
`ρ = R₁/m + κR₁ + 1`.  On `D`, `|u_r − v| ≤ M|g₀(b + r·) − J(b)| + K|f∘Φ_r − f∘Λ|`: the first term
has integral `→ 0` by hypothesis, the second `→ 0` uniformly since `Φ_r → Λ` uniformly on `D`
(`dorwbl_diff_quotient_tendstoUniformlyOn`) and `f` is uniformly continuous. -/
theorem Submission.codim1_lurpt_rescaled_integral_tendsto : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (J : Euclid n → ℝ) (K m : ℝ) (b : Euclid n) (f : Euclid P → ℝ), Continuous F → MeasurableSet B → Measurable J → (∀ a, 0 ≤ J a ∧ J a ≤ K) → 0 < m → (∀ a ∈ B, m * ‖a - b‖ ≤ ‖F a - F b‖) → DifferentiableAt ℝ F b → Injective (fderiv ℝ F b) → (∀ R : ℝ, 0 < R → Tendsto (fun r : ℝ => ∫ w in closedBall (0 : Euclid n) R, |B.indicator J (b + r • w) - J b|) (𝓝[>] 0) (𝓝 0)) → Continuous f → HasCompactSupport f → Tendsto (fun r : ℝ => ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume) (𝓝[>] 0) (𝓝 (J b * ∫ c, f (fderiv ℝ F b c) ∂volume)) := by
  intro P n F B J K m b f hF hB hJ hJK hm hco hdiff hinj hleb hfc hfs
  -- Step 1: `Λ = DF(b)` is injective on `ℝⁿ`, so `|c| ≤ κ|Λc|` for some `κ > 0`
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ c : Euclid n, ‖c‖ ≤ κ * ‖fderiv ℝ F b c‖ := by
    obtain ⟨κ, hκ0, hanti⟩ := LinearMap.exists_antilipschitzWith
      ((fderiv ℝ F b : Euclid n →L[ℝ] Euclid P) : Euclid n →ₗ[ℝ] Euclid P)
      (LinearMap.ker_eq_bot.2 hinj)
    exact ⟨κ, NNReal.coe_pos.2 hκ0, (fderiv ℝ F b).bound_of_antilipschitz hanti⟩
  -- Step 2: `f` vanishes outside `B̄_{R₁}(0)` and `|f| ≤ M`
  obtain ⟨R₁, hR₁, hf0⟩ : ∃ R₁ : ℝ, 0 ≤ R₁ ∧ ∀ y : Euclid P, R₁ < ‖y‖ → f y = 0 := by
    obtain ⟨R₀, hR₀⟩ := (IsCompact.isBounded hfs).subset_closedBall (0 : Euclid P)
    refine ⟨max R₀ 0, le_max_right R₀ 0, fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => ?_⟩
    exact (mem_closedBall_zero_iff.1 (hR₀ hy')).not_gt ((le_max_left R₀ 0).trans_lt hy)
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hfM : ∀ y, |f y| ≤ M := fun y => (Real.norm_eq_abs (f y)).symm.trans_le (hM y)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  -- Step 3: localization to `D = B̄_ρ(0)`
  have hR₁m : 0 ≤ R₁ / m := div_nonneg hR₁ hm.le
  have hκR₁ : 0 ≤ κ * R₁ := mul_nonneg hκ0.le hR₁
  obtain ⟨ρ, hρ, hρm, hρκ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ R₁ / m ≤ ρ ∧ κ * R₁ ≤ ρ :=
    ⟨R₁ / m + κ * R₁ + 1, by linarith, by linarith, by linarith⟩
  have hu0 : ∀ r : ℝ, 0 < r → ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) ρ →
      B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) = 0 := by
    intro r hr c hc
    rw [mem_closedBall_zero_iff, not_le] at hc
    by_cases hbc : b + r • c ∈ B
    · have h1 := hco _ hbc
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le] at h1
      have h3 : R₁ < m * ‖c‖ := by
        have := (div_lt_iff₀ hm).1 (hρm.trans_lt hc)
        linarith
      have h4 : r * R₁ < ‖F (b + r • c) - F b‖ := by
        nlinarith [mul_lt_mul_of_pos_left h3 hr]
      have h2 : R₁ < ‖r⁻¹ • (F (b + r • c) - F b)‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
        calc R₁ = r⁻¹ * (r * R₁) := (inv_mul_cancel_left₀ hr.ne' R₁).symm
          _ < r⁻¹ * ‖F (b + r • c) - F b‖ := mul_lt_mul_of_pos_left h4 (inv_pos.2 hr)
      rw [hf0 _ h2, mul_zero]
    · rw [indicator_of_notMem hbc, zero_mul]
  have hv0 : ∀ c : Euclid n, c ∉ closedBall (0 : Euclid n) ρ → J b * f (fderiv ℝ F b c) = 0 := by
    intro c hc
    rw [mem_closedBall_zero_iff, not_le] at hc
    have h2 : R₁ < ‖fderiv ℝ F b c‖ := by
      by_contra h
      have := mul_le_mul_of_nonneg_left (not_lt.1 h) hκ0.le
      linarith [hκ c]
    rw [hf0 _ h2, mul_zero]
  -- Step 4: bounds, measurability and integrability on `D`
  have hK : 0 ≤ K := (hJK b).1.trans (hJK b).2
  have hgK : ∀ a, |B.indicator J a| ≤ K := by
    intro a
    by_cases ha : a ∈ B
    · rw [indicator_of_mem ha, abs_of_nonneg (hJK a).1]
      exact (hJK a).2
    · rw [indicator_of_notMem ha, abs_zero]
      exact hK
  have hJbK : |J b| ≤ K := by
    rw [abs_of_nonneg (hJK b).1]
    exact (hJK b).2
  have hgm : ∀ r : ℝ, Measurable fun c : Euclid n => B.indicator J (b + r • c) := fun r =>
    (hJ.indicator hB).comp (by fun_prop)
  have hΦc : ∀ r : ℝ, Continuous fun c : Euclid n => f (r⁻¹ • (F (b + r • c) - F b)) := fun r =>
    hfc.comp (by fun_prop)
  have hΛc : Continuous fun c : Euclid n => f (fderiv ℝ F b c) :=
    hfc.comp (fderiv ℝ F b).continuous
  have hint : ∀ g : Euclid n → ℝ, Measurable g → ∀ C : ℝ, (∀ c, |g c| ≤ C) →
      IntegrableOn g (closedBall (0 : Euclid n) ρ) := fun g hg C hC =>
    Measure.integrableOn_of_bounded measure_closedBall_lt_top.ne hg.aestronglyMeasurable
      (Eventually.of_forall fun c => (Real.norm_eq_abs (g c)).trans_le (hC c))
  have hint_u : ∀ r : ℝ, IntegrableOn
      (fun c : Euclid n => B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)))
      (closedBall (0 : Euclid n) ρ) := fun r =>
    hint _ ((hgm r).mul (hΦc r).measurable) (K * M) fun c => by
      rw [abs_mul]
      exact mul_le_mul (hgK _) (hfM _) (abs_nonneg _) hK
  have hint_v : IntegrableOn (fun c : Euclid n => J b * f (fderiv ℝ F b c))
      (closedBall (0 : Euclid n) ρ) :=
    hint _ (hΛc.measurable.const_mul (J b)) (K * M) fun c => by
      rw [abs_mul]
      exact mul_le_mul hJbK (hfM _) (abs_nonneg _) hK
  have hint_A : ∀ r : ℝ, IntegrableOn (fun c : Euclid n => |B.indicator J (b + r • c) - J b|)
      (closedBall (0 : Euclid n) ρ) := fun r =>
    hint _ (continuous_abs.measurable.comp ((hgm r).sub measurable_const)) (K + K) fun c => by
      rw [abs_abs]
      exact (abs_sub _ _).trans (add_le_add (hgK _) hJbK)
  have hint_B : ∀ r : ℝ, IntegrableOn
      (fun c : Euclid n => |f (r⁻¹ • (F (b + r • c) - F b)) - f (fderiv ℝ F b c)|)
      (closedBall (0 : Euclid n) ρ) := fun r =>
    hint _ ((hΦc r).sub hΛc).abs.measurable (M + M) fun c => by
      rw [abs_abs]
      exact (abs_sub _ _).trans (add_le_add (hfM _) (hfM _))
  -- Step 5: both integrals live on `D`
  have hu : ∀ r : ℝ, 0 < r →
      ∫ c, B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) ∂volume =
        ∫ c in closedBall (0 : Euclid n) ρ,
          B.indicator J (b + r • c) * f (r⁻¹ • (F (b + r • c) - F b)) := fun r hr =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hu0 r hr)).symm
  have hv : J b * ∫ c, f (fderiv ℝ F b c) ∂volume =
      ∫ c in closedBall (0 : Euclid n) ρ, J b * f (fderiv ℝ F b c) := by
    rw [← integral_const_mul]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero hv0).symm
  -- Step 6: pointwise bound `|u_r − v| ≤ M|g₀(b + r·) − J(b)| + K|f∘Φ_r − f∘Λ|`
  have key : ∀ x y z w : ℝ, |z| ≤ M → |y| ≤ K →
      |x * z - y * w| ≤ M * |x - y| + K * |z - w| := by
    intro x y z w hz hy
    calc |x * z - y * w| = |(x - y) * z + y * (z - w)| := by congr 1; ring
      _ ≤ |(x - y) * z| + |y * (z - w)| := abs_add_le _ _
      _ = |x - y| * |z| + |y| * |z - w| := by rw [abs_mul, abs_mul]
      _ ≤ |x - y| * M + K * |z - w| :=
        add_le_add (mul_le_mul_of_nonneg_left hz (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hy (abs_nonneg _))
      _ = M * |x - y| + K * |z - w| := by ring
  -- Step 7: `f ∘ Φ_r → f ∘ Λ` uniformly on `D`
  have hU := Metric.tendstoUniformlyOn_iff.1
    ((hfs.uniformContinuous_of_continuous hfc).comp_tendstoUniformlyOn
      (Submission.dorwbl_diff_quotient_tendstoUniformlyOn n P F b hdiff ρ))
  have hBf : Tendsto (fun r : ℝ => ∫ c in closedBall (0 : Euclid n) ρ,
      |f (r⁻¹ • (F (b + r • c) - F b)) - f (fderiv ℝ F b c)|) (𝓝[>] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hV : 0 ≤ volume.real (closedBall (0 : Euclid n) ρ) := measureReal_nonneg
    have hε' : 0 < ε / (volume.real (closedBall (0 : Euclid n) ρ) + 1) := by positivity
    filter_upwards [hU _ hε'] with r hr
    have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (f := fun c : Euclid n => |f (r⁻¹ • (F (b + r • c) - F b)) - f (fderiv ℝ F b c)|)
      measure_closedBall_lt_top fun c hc => by
        have h := hr c hc
        rw [Real.dist_eq] at h
        rw [Real.norm_eq_abs, abs_abs, abs_sub_comm]
        exact h.le
    rw [Real.dist_eq, sub_zero, ← Real.norm_eq_abs]
    refine h1.trans_lt ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    linarith
  -- Step 8: the estimate and the limit
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim := ((hleb ρ hρ).const_mul M).add (hBf.const_mul K)
  rw [mul_zero, mul_zero, add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun r => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  rw [Real.dist_eq, hu r hr, hv, ← integral_sub (hint_u r) hint_v]
  calc |∫ c in closedBall (0 : Euclid n) ρ, (B.indicator J (b + r • c) *
          f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (fderiv ℝ F b c))|
      ≤ ∫ c in closedBall (0 : Euclid n) ρ, |B.indicator J (b + r • c) *
          f (r⁻¹ • (F (b + r • c) - F b)) - J b * f (fderiv ℝ F b c)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ c in closedBall (0 : Euclid n) ρ, (M * |B.indicator J (b + r • c) - J b| +
          K * |f (r⁻¹ • (F (b + r • c) - F b)) - f (fderiv ℝ F b c)|) :=
        setIntegral_mono_on (Integrable.abs (Integrable.sub (hint_u r) hint_v))
          (Integrable.add (Integrable.const_mul (hint_A r) M) (Integrable.const_mul (hint_B r) K))
          measurableSet_closedBall fun c _ => key _ _ _ _ (hfM _) hJbK
    _ = M * (∫ c in closedBall (0 : Euclid n) ρ, |B.indicator J (b + r • c) - J b|) +
          K * (∫ c in closedBall (0 : Euclid n) ρ,
            |f (r⁻¹ • (F (b + r • c) - F b)) - f (fderiv ℝ F b c)|) := by
        rw [integral_add (Integrable.const_mul (hint_A r) M) (Integrable.const_mul (hint_B r) K),
          integral_const_mul, integral_const_mul]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
