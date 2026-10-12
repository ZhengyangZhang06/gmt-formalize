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

/-- **Structure of a connected component of `reg T`** (Simon 7.4.1, as used in the proof of
7.5.11).  Let `T = τ(C, θ, ξ)` in the open set `U`, `y ∈ reg T`, `M₁` the connected component of
`reg T` through `y`, and `T₁(ω) = ∫_{M₁} ⟨ω, ξ⟩ dHⁿ`.  Then `M₁` is Borel, `Hⁿ(M₁ \ C) = 0`,
`closure M₁ ∩ U ⊆ M₁ ∪ sing T`, `sing T` is relatively closed in `U`, and near each `z ∈ M₁`
`T₁ = |m_z|⁻¹ T`.  Every `z ∈ reg T` has an open `O ∋ z` with `spt T ∩ O = M_z ∩ O` connected
and contained in `reg T` (proper charts; open pieces of `M_z` have positive `Hⁿ`-measure), and
on `O` the fundamental lemma of the calculus of variations and determinant covectors give
`M_z ⊆ C`, `θ = |m_z|` and `ξ = sign(m_z) ξ_z` `Hⁿ`-a.e. -/
theorem Submission.regcomp_regular_component_structure : ∀ (P m : ℕ) (U : Set (Euclid P)) (T T₁ : GeometricCurrentOn U (m + 1)) (R : IMRep U (m + 1)) (y : Euclid P), IsOpen U → R.Represents T → y ∈ regularSet T → (∀ ω : TestFormOn U (m + 1), T₁ ω = ∫ x in connectedComponentIn (regularSet T) y, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) → MeasurableSet (connectedComponentIn (regularSet T) y) ∧ μHE[m + 1] (connectedComponentIn (regularSet T) y \ R.carrier) = 0 ∧ closure (connectedComponentIn (regularSet T) y) ∩ U ⊆ connectedComponentIn (regularSet T) y ∪ singularSet T ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → IsCompact (singularSet T ∩ K)) ∧ ∀ z ∈ connectedComponentIn (regularSet T) y, ∃ G : Set (Euclid P), IsOpen G ∧ z ∈ G ∧ ∃ c : ℝ, ∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ G → T₁ ω = c * T ω := by
  intro P m U T T₁ R y hU hR hy hT₁
  classical
  /- Step 1 (unit orientations).  `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` satisfies `|⟨α, ξ⟩| ≤ ‖α‖`, is nonzero,
  and `θ ξ = m ξ'` with `θ > 0` forces `θ = |m|` and `ξ = sign(m) ξ'` (evaluate at the
  determinant covectors `u ↦ det ⟪τ_a, u_b⟫` of both frames). -/
  have hdet : ∀ c : Fin (m + 1) → Euclid P, ∃ α : Covector (Euclid P) (m + 1),
      ∀ u : Fin (m + 1) → Euclid P, α u = (Matrix.of fun b a => inner ℝ (c a) (u b)).det := by
    intro c
    let A : (Euclid P) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ :=
      (Matrix.detRowAlternating : (Fin (m + 1) → ℝ) [⋀^Fin (m + 1)]→ₗ[ℝ] ℝ).compLinearMap
        (LinearMap.pi fun a => (innerSL ℝ (c a)).toLinearMap)
    refine ⟨{ A with
      cont := by
        show Continuous fun u : Fin (m + 1) → Euclid P =>
          Matrix.det (fun b a => inner ℝ (c a) (u b))
        fun_prop }, fun u => rfl⟩
  have hone : ∀ τ : Fin (m + 1) → Euclid P, Orthonormal ℝ τ →
      (Matrix.of fun b a => inner ℝ (τ a) (τ b)).det = 1 := by
    intro τ hτ
    have h1 : (Matrix.of fun b a => inner ℝ (τ a) (τ b)) = 1 := by
      ext b a
      rw [Matrix.of_apply, Matrix.one_apply, orthonormal_iff_ite.mp hτ a b]
      by_cases hab : a = b
      · simp [hab]
      · simp [hab, Ne.symm hab]
    rw [h1, Matrix.det_one]
  have hUO : ∀ (ξ₀ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ξ₀ Q → ∃ τ : Fin (m + 1) → Euclid P, Orthonormal ℝ τ ∧
        ∃ e : ℝ, e ^ 2 = 1 ∧ ∀ α, ξ₀ α = e * α τ := by
    rintro ξ₀ Q ⟨τ, hτ, -, h | h⟩
    · exact ⟨τ, hτ, 1, by norm_num, fun α => by rw [h α, one_mul]⟩
    · exact ⟨τ, hτ, -1, by norm_num, fun α => by rw [h α, neg_one_mul]⟩
  have hUObound : ∀ (ξ₀ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ξ₀ Q → ∀ α : Covector (Euclid P) (m + 1), ‖ξ₀ α‖ ≤ ‖α‖ := by
    intro ξ₀ Q h α
    obtain ⟨τ, hτ, e, he, hξ⟩ := hUO ξ₀ Q h
    have he1 : ‖e‖ = 1 := by
      have h1 : |e| = |1| := (sq_eq_sq_iff_abs_eq_abs e 1).mp (by rw [he]; norm_num)
      rw [Real.norm_eq_abs, h1, abs_one]
    rw [hξ α, norm_mul, he1, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
      _ = ‖α‖ := by simp [hτ.1]
  have hUOne : ∀ (ξ₀ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ξ₀ Q → ξ₀ ≠ 0 := by
    intro ξ₀ Q h h0
    obtain ⟨τ, hτ, e, he, hξ⟩ := hUO ξ₀ Q h
    obtain ⟨α, hα⟩ := hdet τ
    have h1 : ξ₀ α = e := by rw [hξ, hα, hone τ hτ, mul_one]
    rw [h0, zero_apply] at h1
    rw [← h1] at he
    norm_num at he
  have hident : ∀ (ξ₁ ξ₂ : MultiVector P (m + 1)) (Q₁ Q₂ : Submodule ℝ (Euclid P)) (s k : ℝ),
      IsUnitOrientationOf ξ₁ Q₁ → IsUnitOrientationOf ξ₂ Q₂ → 0 < s → k ≠ 0 →
      s • ξ₁ = k • ξ₂ → ξ₁ = (k / |k|) • ξ₂ := by
    intro ξ₁ ξ₂ Q₁ Q₂ s k h₁ h₂ hs hk heq
    obtain ⟨τ₁, hτ₁, e₁, he₁, hξ₁⟩ := hUO ξ₁ Q₁ h₁
    obtain ⟨τ₂, hτ₂, e₂, he₂, hξ₂⟩ := hUO ξ₂ Q₂ h₂
    obtain ⟨α₁, hα₁⟩ := hdet τ₁
    obtain ⟨α₂, hα₂⟩ := hdet τ₂
    have h11 : α₁ τ₁ = 1 := by rw [hα₁]; exact hone τ₁ hτ₁
    have h22 : α₂ τ₂ = 1 := by rw [hα₂]; exact hone τ₂ hτ₂
    have h12 : α₂ τ₁ = α₁ τ₂ := by
      rw [hα₁, hα₂, ← Matrix.det_transpose]
      congr 1
      ext b a
      simp only [Matrix.transpose_apply, Matrix.of_apply]
      exact real_inner_comm _ _
    have E1 : s * (e₁ * α₁ τ₁) = k * (e₂ * α₁ τ₂) := by
      have := congrArg (fun f : MultiVector P (m + 1) => f α₁) heq
      simpa only [smul_apply, smul_eq_mul, hξ₁, hξ₂] using this
    have E2 : s * (e₁ * α₂ τ₁) = k * (e₂ * α₂ τ₂) := by
      have := congrArg (fun f : MultiVector P (m + 1) => f α₂) heq
      simpa only [smul_apply, smul_eq_mul, hξ₁, hξ₂] using this
    rw [h11] at E1
    rw [h22, h12] at E2
    set d := α₁ τ₂
    have he₂0 : e₂ ≠ 0 := by rintro rfl; norm_num at he₂
    have hd : d ^ 2 = 1 := by
      have h3 : k * e₂ * (1 - d ^ 2) = 0 := by linear_combination d * E1 - E2
      have h5 := (mul_eq_zero.mp h3).resolve_left (mul_ne_zero hk he₂0)
      linarith
    have hs2 : s ^ 2 = k ^ 2 := by
      linear_combination (-s ^ 2) * he₁ + (s * e₁ + k * e₂ * d) * E1 + k ^ 2 * e₂ ^ 2 * hd +
        k ^ 2 * he₂
    have hsk : s = |k| := by
      have := (sq_eq_sq_iff_abs_eq_abs s k).mp hs2
      rwa [abs_of_pos hs] at this
    have h6 : ξ₁ = s⁻¹ • (k • ξ₂) := by
      rw [← heq, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    rw [h6, smul_smul, hsk, div_eq_inv_mul]
  /- Step 2 (charts).  A proper chart `ψ : V → W` maps relatively closed subsets of `V` onto
  relatively closed subsets of `W`; hence `closure M ∩ W ⊆ M` and `M` is Borel.  Images `ψ(B)`
  of neighbourhoods have positive `Hⁿ`-measure: a linear left inverse `L` of `Dψ(v)` makes
  `L ∘ ψ` a local homeomorphism (inverse function theorem), and `L` is Lipschitz. -/
  have hL1 : ∀ (V : Set (Euclid (m + 1))) (W : Set (Euclid P)) (ψ : Euclid (m + 1) → Euclid P),
      IsOpen W → ContinuousOn ψ V → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) →
      ∀ F : Set (Euclid (m + 1)), IsClosed F → W ∩ closure (ψ '' (V ∩ F)) ⊆ ψ '' (V ∩ F) := by
    rintro V W ψ hW hψ hprop F hF w ⟨hwW, hwcl⟩
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW w hwW
    have hcB : closedBall w (ε / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hεW
    have hK : IsCompact (V ∩ ψ ⁻¹' closedBall w (ε / 2) ∩ F) :=
      (hprop _ hcB (isCompact_closedBall w (ε / 2))).inter_right hF
    have hKimg : IsCompact (ψ '' (V ∩ ψ ⁻¹' closedBall w (ε / 2) ∩ F)) :=
      hK.image_of_continuousOn (hψ.mono fun x hx => hx.1.1)
    have hsub : ball w (ε / 2) ∩ ψ '' (V ∩ F) ⊆ ψ '' (V ∩ ψ ⁻¹' closedBall w (ε / 2) ∩ F) := by
      rintro _ ⟨hb, v, ⟨hvV, hvF⟩, rfl⟩
      exact ⟨v, ⟨⟨hvV, ball_subset_closedBall hb⟩, hvF⟩, rfl⟩
    have hw : w ∈ closure (ball w (ε / 2) ∩ ψ '' (V ∩ F)) :=
      isOpen_ball.inter_closure ⟨mem_ball_self (by linarith), hwcl⟩
    exact image_mono (show V ∩ ψ ⁻¹' closedBall w (ε / 2) ∩ F ⊆ V ∩ F from
      fun v hv => ⟨hv.1.1, hv.2⟩) (closure_minimal hsub hKimg.isClosed hw)
  have hclM : ∀ (M : Set (Euclid P)) (V : Set (Euclid (m + 1))) (W : Set (Euclid P))
      (ψ : Euclid (m + 1) → Euclid P), IsOpen W → ContinuousOn ψ V →
      (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ψ '' V = W ∩ M →
      W ∩ closure M ⊆ M := by
    intro M V W ψ hW hψ hprop himg x hx
    have h1 : x ∈ W ∩ closure (ψ '' (V ∩ univ)) := by
      refine ⟨hx.1, ?_⟩
      rw [inter_univ, himg]
      exact hW.inter_closure hx
    have h2 := hL1 V W ψ hW hψ hprop univ isClosed_univ h1
    rw [inter_univ, himg] at h2
    exact h2.2
  have hMmeas : ∀ M : Set (Euclid P), IsEmbeddedSubmanifold 1 (m + 1) M → MeasurableSet M := by
    intro M hM
    choose! V W ψ hV hW hyW hψ hinj himg hprop hder using hM
    have hEq : M = (⋃ x ∈ M, W x) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · rintro x ⟨hx, hxcl⟩
        obtain ⟨y', hy', hxy'⟩ := mem_iUnion₂.mp hx
        exact hclM M (V y') (W y') (ψ y') (hW y' hy') (hψ y' hy').continuousOn (hprop y' hy')
          (himg y' hy') ⟨hxy', hxcl⟩
    rw [hEq]
    exact (isOpen_biUnion fun y' hy' => hW y' hy').measurableSet.inter
      isClosed_closure.measurableSet
  have hF2 : ∀ (ψ : Euclid (m + 1) → Euclid P) (v : Euclid (m + 1)),
      HasStrictFDerivAt ψ (fderiv ℝ ψ v) v → Injective (fderiv ℝ ψ v) →
      ∀ B ∈ 𝓝 v, 0 < μHE[m + 1] (ψ '' B) := by
    intro ψ v hstrict hinj B hB
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (fderiv ℝ ψ v).toLinearMap
      (LinearMap.ker_eq_bot.mpr hinj)
    set L : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap g
    have hL : ∀ w, L (fderiv ℝ ψ v w) = w := fun w => by
      have h1 := LinearMap.congr_fun hg w
      simpa [L] using h1
    have hcomp : L.comp (fderiv ℝ ψ v) =
        ((ContinuousLinearEquiv.refl ℝ (Euclid (m + 1)) :
          Euclid (m + 1) →L[ℝ] Euclid (m + 1))) := by
      refine ContinuousLinearMap.ext fun w => ?_
      rw [ContinuousLinearMap.comp_apply, hL w, ContinuousLinearEquiv.coe_refl,
        ContinuousLinearMap.id_apply]
    have h2 : HasStrictFDerivAt (L ∘ ψ)
        ((ContinuousLinearEquiv.refl ℝ (Euclid (m + 1)) :
          Euclid (m + 1) →L[ℝ] Euclid (m + 1))) v := by
      rw [← hcomp]
      exact L.hasStrictFDerivAt.comp v hstrict
    have hnhds : (L ∘ ψ) '' B ∈ 𝓝 ((L ∘ ψ) v) := by
      rw [← h2.map_nhds_eq_of_equiv]
      exact image_mem_map hB
    have hpos : 0 < μHE[m + 1] ((L ∘ ψ) '' B) := by
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      exact Measure.measure_pos_of_mem_nhds volume hnhds
    rw [image_comp] at hpos
    rw [pos_iff_ne_zero] at hpos ⊢
    intro h0
    apply hpos
    simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
      smul_eq_mul, mul_eq_zero, ENNReal.coe_eq_zero] at h0 ⊢
    rcases h0 with h0 | h0
    · exact absurd h0 (Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero _)
    · right
      have hlip := L.lipschitzWith.hausdorffMeasure_image_le (d := ((m + 1 : ℕ) : ℝ))
        (by positivity) (ψ '' B)
      rw [h0, mul_zero] at hlip
      exact nonpos_iff_eq_zero.mp hlip
  /- Step 3 (fundamental lemma of the calculus of variations).  Two `n`-vector fields whose
  pairings with every basis covector have the same integrals against all test functions `g`
  supported in the open set `G` agree a.e. on `G`; integrals of `g · ⟨α, 1_A φ⟩` are
  `∫_A ⟨g α, φ⟩`, and `x ↦ g(x) α` is a test form. -/
  have hKEYr : ∀ (K G : Set (Euclid P)) (f₁ f₂ : Euclid P → ℝ),
      MeasurableSet K → IsOpen G → G ⊆ K → IntegrableOn f₁ K μHE[m + 1] →
      IntegrableOn f₂ K μHE[m + 1] →
      (∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ G → ∫ x in K, g x * f₁ x ∂μHE[m + 1] = ∫ x in K, g x * f₂ x ∂μHE[m + 1]) →
      ∀ᵐ x ∂μHE[m + 1], x ∈ G → f₁ x = f₂ x := by
    intro K G f₁ f₂ hK hG hGK hi₁ hi₂ hint
    have hi : Integrable (f₁ - f₂) (μHE[m + 1].restrict K) := hi₁.sub hi₂
    have key := hG.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := μHE[m + 1].restrict K)
      (hi.integrableOn.locallyIntegrableOn) ?_
    · rw [ae_restrict_iff' hK] at key
      filter_upwards [key] with x hx hxG
      exact sub_eq_zero.mp (hx (hGK hxG) hxG)
    · intro g hg hgc hgG
      obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
      have hgm : AEStronglyMeasurable g (μHE[m + 1].restrict K) :=
        hg.continuous.aestronglyMeasurable
      have hb : ∀ᵐ x ∂(μHE[m + 1].restrict K), ‖g x‖ ≤ C := Eventually.of_forall hC
      have i1 : Integrable (fun x => g x * f₁ x) (μHE[m + 1].restrict K) := hi₁.bdd_mul hgm hb
      have i2 : Integrable (fun x => g x * f₂ x) (μHE[m + 1].restrict K) := hi₂.bdd_mul hgm hb
      have e : ∀ x, g x • (f₁ - f₂) x = g x * f₁ x - g x * f₂ x := by
        intro x
        simp only [Pi.sub_apply, smul_eq_mul]
        ring
      simp_rw [e]
      rw [integral_sub i1 i2, hint g hg hgc hgG, sub_self]
  have hfd : FiniteDimensional ℝ (Covector (Euclid P) (m + 1)) := by
    let L : Covector (Euclid P) (m + 1) →ₗ[ℝ] ((Fin (m + 1) → Fin P) → ℝ) :=
      { toFun := fun α J => α (fun i => EuclideanSpace.single (J i) 1)
        map_add' := by intro α β; ext J; simp
        map_smul' := by intro c α; ext J; simp }
    refine FiniteDimensional.of_injective L ?_
    intro α β h
    have h' : α.toMultilinearMap = β.toMultilinearMap := by
      refine Module.Basis.ext_multilinear
        (fun _ => (EuclideanSpace.basisFun (Fin P) ℝ).toBasis) ?_
      intro J
      simpa [L] using congrFun h J
    ext u
    exact congrArg (fun f => f u) h'
  have hKEY : ∀ (K G : Set (Euclid P)) (h₁ h₂ : Euclid P → MultiVector P (m + 1)),
      MeasurableSet K → IsOpen G → G ⊆ K →
      (∀ α : Covector (Euclid P) (m + 1), IntegrableOn (fun x => h₁ x α) K μHE[m + 1]) →
      (∀ α : Covector (Euclid P) (m + 1), IntegrableOn (fun x => h₂ x α) K μHE[m + 1]) →
      (∀ g : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ G → ∀ α : Covector (Euclid P) (m + 1),
          ∫ x in K, g x * h₁ x α ∂μHE[m + 1] = ∫ x in K, g x * h₂ x α ∂μHE[m + 1]) →
      ∀ᵐ x ∂μHE[m + 1], x ∈ G → h₁ x = h₂ x := by
    intro K G h₁ h₂ hK hG hGK hi₁ hi₂ hint
    let b := Module.finBasis ℝ (Covector (Euclid P) (m + 1))
    have hall : ∀ᵐ x ∂μHE[m + 1], ∀ i, x ∈ G → h₁ x (b i) = h₂ x (b i) := by
      rw [ae_all_iff]
      intro i
      exact hKEYr K G _ _ hK hG hGK (hi₁ (b i)) (hi₂ (b i))
        fun g hg hgc hgG => hint g hg hgc hgG (b i)
    filter_upwards [hall] with x hx hxG
    exact ContinuousLinearMap.coe_injective (b.ext fun i => hx i hxG)
  have hindint : ∀ (K A : Set (Euclid P)) (φ : Euclid P → MultiVector P (m + 1))
      (α : Covector (Euclid P) (m + 1)) (f : Euclid P → ℝ), MeasurableSet A →
      (∀ x ∈ A, φ x α = f x) → IntegrableOn f (A ∩ K) μHE[m + 1] →
      IntegrableOn (fun x => (A.indicator φ x) α) K μHE[m + 1] := by
    intro K A φ α f hA hφf h
    have e : (fun x => (A.indicator φ x) α) = A.indicator f := by
      funext x
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx, hφf x hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_apply]
    rw [e]
    refine (integrable_indicator_iff hA).mpr ?_
    show Integrable f ((μHE[m + 1].restrict K).restrict A)
    rw [Measure.restrict_restrict hA]
    exact h
  have hind : ∀ (K A : Set (Euclid P)) (φ : Euclid P → MultiVector P (m + 1))
      (g : Euclid P → ℝ) (α : Covector (Euclid P) (m + 1)), MeasurableSet A →
      (∀ x, x ∉ K → g x = 0) →
      ∫ x in K, g x * (A.indicator φ x) α ∂μHE[m + 1] = ∫ x in A, φ x (g x • α) ∂μHE[m + 1] := by
    intro K A φ g α hA hgK
    have h1 : (fun x => g x * (A.indicator φ x) α) = A.indicator (fun x => φ x (g x • α)) := by
      funext x
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx, map_smul, smul_eq_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_apply,
          mul_zero]
    rw [h1, setIntegral_indicator hA]
    symm
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA inter_subset_right fun x hx => ?_
    rw [hgK x (fun hxK => hx.2 ⟨hxK, hx.1⟩), zero_smul, map_zero]
  have hform : ∀ (g : Euclid P → ℝ) (α : Covector (Euclid P) (m + 1)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → HasCompactSupport g → tsupport g ⊆ U →
      ∃ ω : TestFormOn U (m + 1), (ω : DifferentialForm (Euclid P) (m + 1)) = (fun x => g x • α) ∧
        tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ tsupport g := by
    intro g α hg hgc hgU
    exact ⟨⟨fun x => g x • α, ⟨hg.smul contDiff_const, hgc.smul_right⟩,
      (tsupport_smul_subset_left _ _).trans hgU⟩, rfl, tsupport_smul_subset_left _ _⟩
  /- Step 4 (local sheets).  For `z ∈ reg T` with data `(ρ, m, M, ξ')`, a chart `ψ` at `z` and
  `O := W ∩ (closure ψ(V \ B_t(v₀)))ᶜ ∩ B_{ε/2}(z)` give `M ∩ O = ψ(B_t(v₀))` (connected), and
  `spt T ∩ O = M ∩ O ⊆ reg T`; on `O`, `M ⊆ C` a.e. and `ξ = sign(m) ξ'` a.e. -/
  have hsheet : ∀ z ∈ regularSet T, ∃ (O : Set (Euclid P)) (k : ℤ) (M : Set (Euclid P))
      (ξ' : Euclid P → MultiVector P (m + 1)),
      IsOpen O ∧ z ∈ O ∧ k ≠ 0 ∧ MeasurableSet M ∧
      T.support ∩ O ⊆ regularSet T ∧ T.support ∩ O = M ∩ O ∧ IsPreconnected (M ∩ O) ∧
      (∀ ω : TestFormOn U (m + 1), tsupport (ω : DifferentialForm (Euclid P) (m + 1)) ⊆ O →
        T ω = (k : ℝ) * ∫ x in M, ξ' x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1]) ∧
      (∀ᵐ x ∂μHE[m + 1], x ∈ M ∩ O →
        x ∈ R.carrier ∧ R.orient x = ((k : ℝ) / |(k : ℝ)|) • ξ' x) := by
    intro z hz
    obtain ⟨hzS, ρ, hρ, hballU, k, M, ξ', hk, hzM, hMsub, hξ', hfin, hrepz⟩ := hz
    have hM : MeasurableSet M := hMmeas M hMsub
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    obtain ⟨V, W, ψ, hVo, hWo, hzW, hψ, hinj, himg, hprop, hder⟩ := hMsub z hzM
    have hψc : ContinuousOn ψ V := hψ.continuousOn
    obtain ⟨v₀, hv₀V, hv₀z⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hzW, hzM⟩
    obtain ⟨ε, hε, hεsub⟩ :=
      Metric.isOpen_iff.mp (hWo.inter isOpen_ball) z ⟨hzW, mem_ball_self hρ⟩
    have hcB : closedBall z (ε / 2) ⊆ W ∩ ball z ρ :=
      (closedBall_subset_ball (by linarith)).trans hεsub
    have hcBU : closedBall z (ε / 2) ⊆ U := fun x hx => hballU (hcB hx).2
    have hnhd : V ∩ ψ ⁻¹' ball z (ε / 2) ∈ 𝓝 v₀ := by
      refine inter_mem (hVo.mem_nhds hv₀V)
        ((hψc.continuousAt (hVo.mem_nhds hv₀V)).preimage_mem_nhds ?_)
      rw [hv₀z]
      exact isOpen_ball.mem_nhds (mem_ball_self (by linarith))
    obtain ⟨t, ht, htsub⟩ := Metric.mem_nhds_iff.mp hnhd
    set O := W ∩ (closure (ψ '' (V ∩ (ball v₀ t)ᶜ)))ᶜ ∩ ball z (ε / 2)
    have hOopen : IsOpen O := (hWo.inter isClosed_closure.isOpen_compl).inter isOpen_ball
    have hOW : O ⊆ W := fun x hx => hx.1.1
    have hOcB : O ⊆ closedBall z (ε / 2) := fun x hx => ball_subset_closedBall hx.2
    have hOρ : O ⊆ ball z ρ := fun x hx => (hcB (hOcB hx)).2
    have hOU : O ⊆ U := hOρ.trans hballU
    have hMO : M ∩ O = ψ '' ball v₀ t := by
      apply Subset.antisymm
      · rintro x ⟨hxM, hxO⟩
        obtain ⟨v, hvV, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxO.1.1, hxM⟩
        refine ⟨v, ?_, rfl⟩
        by_contra hv
        exact hxO.1.2 (subset_closure ⟨v, ⟨hvV, hv⟩, rfl⟩)
      · rintro _ ⟨v, hv, rfl⟩
        have hvV : v ∈ V := (htsub hv).1
        have hψv : ψ v ∈ W ∩ M := by rw [← himg]; exact mem_image_of_mem ψ hvV
        refine ⟨hψv.2, ⟨hψv.1, fun hcl => ?_⟩, (htsub hv).2⟩
        obtain ⟨v', ⟨hv'V, hv'⟩, hv'eq⟩ :=
          hL1 V W ψ hWo hψc hprop _ isOpen_ball.isClosed_compl ⟨hψv.1, hcl⟩
        exact hv' (by rw [hinj hv'V hvV hv'eq]; exact hv)
    have hzO : z ∈ O := by
      have h1 : z ∈ M ∩ O := by rw [hMO]; exact ⟨v₀, mem_ball_self ht, hv₀z⟩
      exact h1.2
    -- `spt T ∩ O ⊆ M`: off `closure M`, `T = m[[M]]` vanishes
    have hSOM : T.support ∩ O ⊆ M := by
      rintro x ⟨hxS, hxO⟩
      refine hclM M V W ψ hWo hψc hprop himg ⟨hOW hxO, ?_⟩
      by_contra hxcl
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp
        (isClosed_closure.isOpen_compl.inter isOpen_ball) x ⟨hxcl, hOρ hxO⟩
      have hcB' : closedBall x (δ / 2) ⊆ (closure M)ᶜ ∩ ball z ρ :=
        (closedBall_subset_ball (by linarith)).trans hδsub
      apply hxS.2
      refine ⟨ball x (δ / 2), ⟨isOpen_ball, (isCompact_closedBall x (δ / 2)).of_isClosed_subset
        isClosed_closure closure_ball_subset_closedBall,
        closure_ball_subset_closedBall.trans fun y hy => hballU (hcB' hy).2, ?_⟩,
        mem_ball_self (by linarith)⟩
      intro ω hω
      rw [hrepz ω (hω.trans (ball_subset_closedBall.trans fun y hy => (hcB' hy).2)),
        setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
      intro x' hx'M
      have hx' : x' ∉ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) := fun h =>
        (hcB' (ball_subset_closedBall (hω h))).1 (subset_closure hx'M)
      rw [image_eq_zero_of_notMem_tsupport hx', map_zero]
    -- integrability on `closedBall z (ε / 2)`
    have hξ'int : ∀ α : Covector (Euclid P) (m + 1),
        IntegrableOn (fun x => ξ' x α) (M ∩ closedBall z (ε / 2)) μHE[m + 1] := by
      intro α
      have hfinB : μHE[m + 1] (M ∩ closedBall z (ε / 2)) ≠ ∞ :=
        hfin _ (isCompact_closedBall z (ε / 2)) fun x hx => (hcB hx).2
      have h1 := Measure.integrableOn_of_bounded (μ := μHE[m + 1].restrict M)
        (s := closedBall z (ε / 2)) (M := ‖α‖)
        (by rwa [Measure.restrict_apply measurableSet_closedBall, inter_comm])
        (((continuous_eval_const α).comp_continuousOn hξ'.1).aestronglyMeasurable hM) ?_
      · have e : (μHE[m + 1].restrict M).restrict (closedBall z (ε / 2)) =
            μHE[m + 1].restrict (M ∩ closedBall z (ε / 2)) := by
          rw [Measure.restrict_restrict measurableSet_closedBall, inter_comm]
        unfold IntegrableOn at h1 ⊢
        rwa [e] at h1
      · rw [Measure.restrict_restrict measurableSet_closedBall]
        filter_upwards [ae_restrict_mem (measurableSet_closedBall.inter hM)] with x hx
        obtain ⟨Q, -, hQ⟩ := hξ'.2 x hx.2
        exact hUObound _ _ hQ α
    have hintM : ∀ α : Covector (Euclid P) (m + 1),
        IntegrableOn (fun x => (M.indicator ξ' x) α) (closedBall z (ε / 2)) μHE[m + 1] :=
      fun α => hindint _ _ _ α _ hM (fun x _ => rfl) (hξ'int α)
    have hintMk : ∀ α : Covector (Euclid P) (m + 1),
        IntegrableOn (fun x => (M.indicator (fun x => (k : ℝ) • ξ' x) x) α)
          (closedBall z (ε / 2)) μHE[m + 1] :=
      fun α => hindint _ _ _ α (fun x => (k : ℝ) * ξ' x α) hM
        (fun x _ => by rw [smul_apply, smul_eq_mul]) ((hξ'int α).const_mul _)
    have hintC : ∀ α : Covector (Euclid P) (m + 1),
        IntegrableOn (fun x => (R.carrier.indicator (fun x => (R.mult x : ℝ) • R.orient x) x) α)
          (closedBall z (ε / 2)) μHE[m + 1] := by
      intro α
      refine hindint _ _ _ α (fun x => (R.mult x : ℝ) * R.orient x α) R.measurableSet_carrier
        (fun x _ => by rw [smul_apply, smul_eq_mul]) ?_
      have hlint := R.locallyIntegrable_mult (closedBall z (ε / 2))
        (isCompact_closedBall z (ε / 2)) hcBU
      have hmeas : Measurable fun x => (R.mult x : ℝ) :=
        (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp R.measurable_mult
      have hθint : Integrable (fun x => (R.mult x : ℝ))
          (μHE[m + 1].restrict (R.carrier ∩ closedBall z (ε / 2))) := by
        have h1 := integrable_toReal_of_lintegral_ne_top
          (μ := μHE[m + 1].restrict (R.carrier ∩ closedBall z (ε / 2)))
          (f := fun x => (R.mult x : ℝ≥0∞))
          ((measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0∞))).comp R.measurable_mult).aemeasurable
          hlint
        simpa using h1
      have h2 : AEStronglyMeasurable (fun x => R.orient x α)
          (μHE[m + 1].restrict (R.carrier ∩ closedBall z (ε / 2))) :=
        ((continuous_eval_const α).comp_aestronglyMeasurable
          R.aestronglyMeasurable_orient).mono_measure
            (Measure.restrict_mono inter_subset_left le_rfl)
      refine (hθint.mul_const ‖α‖).mono' (hmeas.aestronglyMeasurable.mul h2) ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients] with x hx
      obtain ⟨Q, -, hQ⟩ := hx
      rw [norm_mul, Real.norm_natCast]
      exact mul_le_mul_of_nonneg_left (hUObound _ _ hQ α) (Nat.cast_nonneg _)
    -- `M ∩ O ⊆ spt T`: otherwise `ξ_M = 0` a.e. on an open piece of `M`, of positive measure
    have hMOS : M ∩ O ⊆ T.support := by
      rintro x ⟨hxM, hxO⟩
      refine ⟨hOU hxO, fun hxZ => ?_⟩
      obtain ⟨W', ⟨hW'o, -, -, hW'v⟩, hxW'⟩ := hxZ
      have hG'o : IsOpen (W' ∩ O) := hW'o.inter hOopen
      have hae := hKEY (closedBall z (ε / 2)) (W' ∩ O) (M.indicator ξ') 0 measurableSet_closedBall
        hG'o (inter_subset_right.trans hOcB) hintM (fun _ => integrableOn_zero) ?_
      · have hnull : μHE[m + 1] (M ∩ (W' ∩ O)) = 0 := by
          rw [measure_eq_zero_iff_ae_notMem]
          filter_upwards [hae] with x' hx' hx'mem
          have h0 := hx' hx'mem.2
          rw [indicator_of_mem hx'mem.1, Pi.zero_apply] at h0
          obtain ⟨Q, -, hQ⟩ := hξ'.2 x' hx'mem.1
          exact hUOne _ _ hQ h0
        obtain ⟨v, hv, hvx⟩ : x ∈ ψ '' ball v₀ t := by rw [← hMO]; exact ⟨hxM, hxO⟩
        have hvV : v ∈ V := (htsub hv).1
        have hB : ball v₀ t ∩ ψ ⁻¹' (W' ∩ O) ∈ 𝓝 v := by
          refine inter_mem (isOpen_ball.mem_nhds hv)
            ((hψc.continuousAt (hVo.mem_nhds hvV)).preimage_mem_nhds ?_)
          rw [hvx]
          exact hG'o.mem_nhds ⟨hxW', hxO⟩
        have hpos := hF2 ψ v ((hψ.contDiffAt (hVo.mem_nhds hvV)).hasStrictFDerivAt (by norm_num))
          (hder v hvV) _ hB
        have hsub : ψ '' (ball v₀ t ∩ ψ ⁻¹' (W' ∩ O)) ⊆ M ∩ (W' ∩ O) := by
          rintro _ ⟨v', ⟨hv'b, hv'G⟩, rfl⟩
          have h1 : ψ v' ∈ M ∩ O := by rw [hMO]; exact mem_image_of_mem ψ hv'b
          exact ⟨h1.1, hv'G⟩
        exact absurd (measure_mono_null hsub hnull) hpos.ne'
      · intro g hg hgc hgG α
        have hgK : ∀ x, x ∉ closedBall z (ε / 2) → g x = 0 := fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h => hx (hOcB (hgG h).2)
        rw [hind _ _ _ g α hM hgK]
        simp only [Pi.zero_apply, zero_apply, mul_zero, integral_zero]
        obtain ⟨ω, hω, hωg⟩ := hform g α hg hgc ((hgG.trans inter_subset_right).trans hOU)
        have h1 := hrepz ω ((hωg.trans (hgG.trans inter_subset_right)).trans hOρ)
        have h2 : T ω = 0 := hW'v ω (hωg.trans (hgG.trans inter_subset_left))
        rw [h2, hω] at h1
        exact (mul_eq_zero.mp h1.symm).resolve_left hk'
    -- identification of `R` on the sheet
    have hKEY2 := hKEY (closedBall z (ε / 2)) O
      (R.carrier.indicator fun x => (R.mult x : ℝ) • R.orient x)
      (M.indicator fun x => (k : ℝ) • ξ' x)
      measurableSet_closedBall hOopen hOcB hintC hintMk ?_
    swap
    · intro g hg hgc hgO α
      have hgK : ∀ x, x ∉ closedBall z (ε / 2) → g x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport fun h => hx (hOcB (hgO h))
      obtain ⟨ω, hω, hωg⟩ := hform g α hg hgc (hgO.trans hOU)
      rw [hind _ _ _ g α R.measurableSet_carrier hgK, hind _ _ _ g α hM hgK]
      have h2 := hrepz ω ((hωg.trans hgO).trans hOρ)
      rw [hR ω, IMRep.action, hω] at h2
      simp only [smul_apply, smul_eq_mul]
      rw [integral_const_mul]
      exact h2
    have horient : ∀ᵐ x ∂μHE[m + 1], x ∈ R.carrier → ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt (m + 1) R.carrier x Q ∧ IsUnitOrientationOf (R.orient x) Q :=
      (ae_restrict_iff' R.measurableSet_carrier).mp R.orients
    have hfinal : ∀ᵐ x ∂μHE[m + 1], x ∈ M ∩ O →
        x ∈ R.carrier ∧ R.orient x = ((k : ℝ) / |(k : ℝ)|) • ξ' x := by
      filter_upwards [hKEY2, horient] with x hx1 hx2 hxMO
      have h := hx1 hxMO.2
      rw [indicator_of_mem hxMO.1] at h
      obtain ⟨Q', -, hQ'⟩ := hξ'.2 x hxMO.1
      by_cases hxC : x ∈ R.carrier
      · rw [indicator_of_mem hxC] at h
        obtain ⟨Q, -, hQ⟩ := hx2 hxC
        have hθ : (0 : ℝ) < R.mult x := by exact_mod_cast R.mult_pos x hxC
        exact ⟨hxC, hident _ _ _ _ _ _ hQ hQ' hθ hk' h⟩
      · rw [indicator_of_notMem hxC] at h
        exact absurd ((smul_eq_zero.mp h.symm).resolve_left hk') (hUOne _ _ hQ')
    refine ⟨O, k, M, ξ', hOopen, hzO, hk, hM, ?_, ?_, ?_, fun ω hω => hrepz ω (hω.trans hOρ),
      hfinal⟩
    · rintro x ⟨hxS, hxO⟩
      have hxM : x ∈ M := hSOM ⟨hxS, hxO⟩
      have hxρ : dist x z < ρ := mem_ball.mp (hOρ hxO)
      have hsub : ball x (ρ - dist x z) ⊆ ball z ρ := ball_subset_ball' (by linarith)
      exact ⟨hxS, ρ - dist x z, by linarith, hsub.trans hballU, k, M, ξ', hk, hxM, hMsub, hξ',
        fun K hK hKsub => hfin K hK (hKsub.trans hsub), fun ω hω => hrepz ω (hω.trans hsub)⟩
    · exact Subset.antisymm (fun x hx => ⟨hSOM hx, hx.2⟩) (fun x hx => ⟨hMOS hx, hx.2⟩)
    · rw [hMO]
      exact (convex_ball v₀ t).isPreconnected.image ψ (hψc.mono fun v hv => (htsub hv).1)
  /- Step 5 (assembly).  `reg T = spt T ∩ ⋃ O_z` is Borel and relatively open in `spt T`;
  `M₁ = reg T ∩ closure M₁` (components are closed); `M₁ ∩ O_z = M_z ∩ O_z` for `z ∈ M₁`. -/
  have hSmeas : MeasurableSet T.support :=
    hU.measurableSet.diff T.isOpen_zeroRegion.measurableSet
  have hScl : closure T.support ∩ U ⊆ T.support := by
    rintro x ⟨hxcl, hxU⟩
    exact ⟨hxU, closure_minimal (fun x hx => hx.2) T.isOpen_zeroRegion.isClosed_compl hxcl⟩
  choose! O k M ξ' hOopen hzO hk hMm hSOreg hSOeq hconn hrep hae using hsheet
  have hregeq : regularSet T = T.support ∩ ⋃ z ∈ regularSet T, O z := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hx.1, mem_biUnion hx (hzO x hx)⟩
    · rintro x ⟨hxS, hxO⟩
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hxO
      exact hSOreg z hz ⟨hxS, hxz⟩
  have hregmeas : MeasurableSet (regularSet T) := by
    rw [hregeq]
    exact hSmeas.inter (isOpen_biUnion fun z hz => hOopen z hz).measurableSet
  have hM₁reg : connectedComponentIn (regularSet T) y ⊆ regularSet T :=
    connectedComponentIn_subset _ _
  have hclosed : ∀ x ∈ closure (connectedComponentIn (regularSet T) y), x ∈ regularSet T →
      x ∈ connectedComponentIn (regularSet T) y := by
    intro x hxcl hxreg
    have hpre : IsPreconnected (insert x (connectedComponentIn (regularSet T) y)) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
        (insert_subset_iff.mpr ⟨hxcl, subset_closure⟩)
    exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ (mem_connectedComponentIn hy))
      (insert_subset_iff.mpr ⟨hxreg, hM₁reg⟩) (mem_insert _ _)
  have hM₁meas : MeasurableSet (connectedComponentIn (regularSet T) y) := by
    have h1 : connectedComponentIn (regularSet T) y =
        regularSet T ∩ closure (connectedComponentIn (regularSet T) y) := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨hM₁reg hx, subset_closure hx⟩
      · rintro x ⟨hxreg, hxcl⟩
        exact hclosed x hxcl hxreg
    rw [h1]
    exact hregmeas.inter isClosed_closure.measurableSet
  refine ⟨hM₁meas, ?_, ?_, ?_, ?_⟩
  · -- (ii) `Hⁿ(M₁ \ C) = 0`, by a countable subcover of the sheets
    obtain ⟨T', hT'sub, hT'c, hT'eq⟩ := TopologicalSpace.isOpen_biUnion_countable
      (connectedComponentIn (regularSet T) y) O (fun z hz => hOopen z (hM₁reg hz))
    have hsub : connectedComponentIn (regularSet T) y \ R.carrier ⊆
        ⋃ z ∈ T', (M z ∩ O z) \ R.carrier := by
      rintro x ⟨hxM₁, hxC⟩
      have hx' : x ∈ ⋃ z ∈ connectedComponentIn (regularSet T) y, O z :=
        mem_biUnion hxM₁ (hzO x (hM₁reg hxM₁))
      rw [← hT'eq] at hx'
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp hx'
      have hzreg := hM₁reg (hT'sub hz)
      have hxMO : x ∈ M z ∩ O z := by
        rw [← hSOeq z hzreg]
        exact ⟨(hM₁reg hxM₁).1, hxz⟩
      exact mem_biUnion hz ⟨hxMO, hxC⟩
    refine measure_mono_null hsub ((measure_biUnion_null_iff hT'c).mpr fun z hz => ?_)
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae z (hM₁reg (hT'sub hz))] with x hx hxmem
    exact hxmem.2 (hx hxmem.1).1
  · -- (iii) the frontier of `M₁` in `U` lies in `sing T`
    rintro x ⟨hxcl, hxU⟩
    have hxS : x ∈ T.support :=
      hScl ⟨closure_mono (hM₁reg.trans fun x hx => hx.1) hxcl, hxU⟩
    by_cases hxreg : x ∈ regularSet T
    · exact Or.inl (hclosed x hxcl hxreg)
    · exact Or.inr ⟨hxS, hxreg⟩
  · -- (iv) `sing T` is relatively closed in `U`
    intro K hK hKU
    have h1 : singularSet T ∩ K = K \ (T.zeroRegion ∪ ⋃ z ∈ regularSet T, O z) := by
      apply Subset.antisymm
      · rintro x ⟨⟨hxS, hxreg⟩, hxK⟩
        refine ⟨hxK, ?_⟩
        rintro (hxZ | hxO)
        · exact hxS.2 hxZ
        · exact hxreg (by rw [hregeq]; exact ⟨hxS, hxO⟩)
      · rintro x ⟨hxK, hx⟩
        have hxS : x ∈ T.support := ⟨hKU hxK, fun h => hx (Or.inl h)⟩
        exact ⟨⟨hxS, fun hxreg => hx (Or.inr (mem_biUnion hxreg (hzO x hxreg)))⟩, hxK⟩
    rw [h1]
    exact hK.diff (T.isOpen_zeroRegion.union (isOpen_biUnion fun z hz => hOopen z hz))
  · -- (v) `T₁ = |m_z|⁻¹ T` near each `z ∈ M₁`
    intro z hzM₁
    have hzreg := hM₁reg hzM₁
    refine ⟨O z, hOopen z hzreg, hzO z hzreg, 1 / |(k z : ℝ)|, fun ω hω => ?_⟩
    have hM₁O : connectedComponentIn (regularSet T) y ∩ O z = M z ∩ O z := by
      apply Subset.antisymm
      · rintro x ⟨hxM₁, hxO⟩
        rw [← hSOeq z hzreg]
        exact ⟨(hM₁reg hxM₁).1, hxO⟩
      · intro x hx
        have hzMO : z ∈ M z ∩ O z := by
          rw [← hSOeq z hzreg]
          exact ⟨hzreg.1, hzO z hzreg⟩
        have hsubreg : M z ∩ O z ⊆ regularSet T := by
          rw [← hSOeq z hzreg]
          exact hSOreg z hzreg
        have h1 := (hconn z hzreg).subset_connectedComponentIn hzMO hsubreg
        rw [← connectedComponentIn_eq hzM₁] at h1
        exact ⟨h1 hx, hx.2⟩
    have hvan : ∀ x, x ∉ O z → (ω : DifferentialForm (Euclid P) (m + 1)) x = 0 :=
      fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hω h)
    have hMOm : MeasurableSet (M z ∩ O z) := (hMm z hzreg).inter (hOopen z hzreg).measurableSet
    have hcongr : ∫ x in M z ∩ O z, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x)
          ∂μHE[m + 1] =
        ∫ x in M z ∩ O z, ((k z : ℝ) / |(k z : ℝ)|) *
          ξ' z x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] := by
      refine setIntegral_congr_ae hMOm ?_
      filter_upwards [hae z hzreg] with x hx hxMO
      rw [(hx hxMO).2, smul_apply, smul_eq_mul]
    calc T₁ ω = ∫ x in connectedComponentIn (regularSet T) y,
          R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] := hT₁ ω
      _ = ∫ x in connectedComponentIn (regularSet T) y ∩ O z,
          R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hM₁meas inter_subset_left
            (fun x hx => by rw [hvan x (fun h => hx.2 ⟨hx.1, h⟩), map_zero])
      _ = ∫ x in M z ∩ O z, R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x)
          ∂μHE[m + 1] := by rw [hM₁O]
      _ = ∫ x in M z ∩ O z, ((k z : ℝ) / |(k z : ℝ)|) *
          ξ' z x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] := hcongr
      _ = ∫ x in M z, ((k z : ℝ) / |(k z : ℝ)|) *
          ξ' z x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hMm z hzreg) inter_subset_left
            (fun x hx => by rw [hvan x (fun h => hx.2 ⟨hx.1, h⟩), map_zero, mul_zero])).symm
      _ = ((k z : ℝ) / |(k z : ℝ)|) * ∫ x in M z,
          ξ' z x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          integral_const_mul _ _
      _ = 1 / |(k z : ℝ)| * T ω := by
          rw [hrep z hzreg ω hω]
          ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
