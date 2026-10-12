import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.LinearAlgebra.Trace
import Poincare.SimonGMT.Chapter03.Rectifiable
import Poincare.SimonGMT.Chapter06.Mass
import Poincare.SimonGMT.Chapter06.CurrentLocalEquality
import Poincare.SimonGMT.Chapter06.AffineCurrentPushforward
import Poincare.SimonGMT.Chapter01.DensityComparison

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

/-- **Simon Ch. 6, Remark 3.2(1)**, step 3 (orientations `±τ₁ ∧ ⋯ ∧ τₙ` as in 2.1–2.2): two unit
orientations `v = ±τ₁ ∧ ⋯ ∧ τₙ`, `w = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` differ by a sign.
`τ` and `τ'` are orthonormal bases `b`, `b'` of `Q`; every alternating `n`-form on `Q` is a
multiple of `det_b`, so `α(τ') = det_b(b') α(τ)` for every `n`-covector `α`, and
`det_b(b') = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.rsdic_unitOrientation_eq_or_eq_neg : ∀ (P n : ℕ) (v w : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf v Q → IsUnitOrientationOf w Q → w = v ∨ w = -v := by
  rintro P n v w Q ⟨τ, hτ, hspan, hv⟩ ⟨τ', hτ', hspan', hw⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let u : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hu : Orthonormal ℝ u := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := u)]
      exact hσ
    have huspan : ⊤ ≤ Submodule.span ℝ (range u) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [u] using hc)⟩
    exact ⟨OrthonormalBasis.mk hu huspan, fun i => by simp [u]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  -- `det_b(b') = ±1`
  have hd := b.det_to_matrix_orthonormalBasis_real b'
  -- `α(τ') = det_b(b') α(τ)`: the restriction `α_Q` of `α` to `Q` is `α_Q(b) det_b`
  have hτ'τ : ∀ α : Covector (Euclid P) n, α τ' = b.toBasis.det b' * α τ := by
    intro α
    let f : Q [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap Q.subtype
    have hf : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
        (∀ i, (c i : Euclid P) = σ i) → f c = α σ := by
      intro c σ hc
      have hcσ : (fun i => Q.subtype (c i)) = σ := funext hc
      rw [AlternatingMap.compLinearMap_apply, hcσ, ContinuousAlternatingMap.coe_toAlternatingMap]
    have h := congrArg (fun g : Q [⋀^Fin n]→ₗ[ℝ] ℝ => g b') (f.eq_smul_basis_det b.toBasis)
    simp only [AlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis] at h
    rw [← hf b' τ' hb', h, hf b τ hb, mul_comm]
  -- `w = ±v`
  rcases hd with hd | hd <;> rcases hv with hv | hv <;> rcases hw with hw | hw
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
  · left; ext α; rw [hw, hv, hτ'τ, hd, neg_one_mul]
  · right; ext α; rw [neg_apply, hw, hv, hτ'τ, hd, neg_one_mul, neg_neg]
/-- **Simon Ch. 6, Remark 3.2(1)** (the representation step): if `1_M θ ξ = p₁ 1_{M₁} θ₁ ξ₁ +
p₂ 1_{M₂} θ₂ ξ₂` holds `Hⁿ`-a.e., then `τ(M, θ, ξ)(ω) = p₁ τ(M₁, θ₁, ξ₁)(ω) + p₂ τ(M₂, θ₂, ξ₂)(ω)`
for every `ω ∈ 𝒟ⁿ(U)`.  A unit orientation has `|⟨α, ξ⟩| ≤ ‖α‖`, so on each carrier `θ⟨ω, ξ⟩` is
dominated by `sup ‖ω‖ · θ 1_{spt ω}`, integrable by local integrability of `θ`.  Thus each action
is `∫ ⟨ω, 1_M θ ξ⟩ dHⁿ` with an integrable integrand, and the identity integrates linearly. -/
theorem Submission.rsdic_imrep_action_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ R : IMRep U n) (p₁ p₂ : ℤ), (∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x) → ∀ ω : TestFormOn U n, R.action (ω : DifferentialForm (Euclid P) n) = (p₁ : ℝ) * R₁.action (ω : DifferentialForm (Euclid P) n) + (p₂ : ℝ) * R₂.action (ω : DifferentialForm (Euclid P) n) := by
  intro P n U R₁ R₂ R p₁ p₂ hF ω
  -- `ω` is continuous, bounded by `W`, and supported in the compact `K = spt ω ⊆ U`
  obtain ⟨⟨hsmooth, hcpt⟩, hωU⟩ := ω.2
  have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  obtain ⟨W, hW⟩ := hωc.bounded_above_of_compact_support hcpt
  -- Step 1: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` has `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
  have hunit : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q →
      ∀ α : Covector (Euclid P) n, ‖ξ α‖ ≤ ‖α‖ := by
    rintro ξ Q ⟨τ, hτ, -, hξ⟩ α
    have h : ‖α τ‖ ≤ ‖α‖ := by
      calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := α.le_opNorm τ
        _ = ‖α‖ := by simp [hτ.norm_eq_one]
    rcases hξ with h' | h'
    · rw [h' α]; exact h
    · rw [h' α, norm_neg]; exact h
  -- Steps 2–3: for every `R' = (M', θ', ξ')`, `x ↦ (1_{M'} θ' ξ')(x)(ω(x))` is integrable with
  -- integral `τ(R')(ω)`
  have key : ∀ R' : IMRep U n,
      Integrable (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) μHE[n] ∧
      ∫ x, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
        R'.action (ω : DifferentialForm (Euclid P) n) := by
    intro R'
    have hfun : (fun x => R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x
        ((ω : DifferentialForm (Euclid P) n) x)) = R'.carrier.indicator
          (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)) := by
      funext x
      by_cases hx : x ∈ R'.carrier
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [hfun, integrable_indicator_iff R'.measurableSet_carrier,
      integral_indicator R'.measurableSet_carrier]
    refine ⟨?_, rfl⟩
    -- `θ'⟨ω, ξ'⟩` is a.e. strongly measurable: `(L, α) ↦ L(α)` is continuous
    have hmult : Measurable fun y => (R'.mult y : ℝ) := measurable_from_nat.comp R'.measurable_mult
    have hev : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
      continuous_fst.clm_apply continuous_snd
    have hmeas : AEStronglyMeasurable
        (fun y => (R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y))
        (μHE[n].restrict R'.carrier) :=
      hmult.aestronglyMeasurable.mul (hev.comp_aestronglyMeasurable
        (R'.aestronglyMeasurable_orient.prodMk hωc.aestronglyMeasurable))
    -- the dominating function `W θ' 1_K` is integrable on `M'`, as `∫_{M' ∩ K} θ' dHⁿ < ∞`
    have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
      (isClosed_tsupport _).measurableSet
    have hint : Integrable (fun y => W * (tsupport (ω : DifferentialForm (Euclid P) n)).indicator
        (fun y => (R'.mult y : ℝ)) y) (μHE[n].restrict R'.carrier) := by
      refine Integrable.const_mul ?_ W
      rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm]
      have h := integrable_toReal_of_lintegral_ne_top
        (μ := μHE[n].restrict (tsupport (ω : DifferentialForm (Euclid P) n) ∩ R'.carrier))
        (f := fun y => (R'.mult y : ℝ≥0∞))
        (measurable_from_nat.comp R'.measurable_mult).aemeasurable
        (by rw [Set.inter_comm]; exact R'.locallyIntegrable_mult _ hcpt hωU)
      simpa using h
    refine hint.mono' hmeas ?_
    filter_upwards [R'.orients] with y hyQ
    obtain ⟨Q, -, hQ⟩ := hyQ
    by_cases hy : y ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [Set.indicator_of_mem hy]
      calc ‖(R'.mult y : ℝ) * R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖
          = (R'.mult y : ℝ) * ‖R'.orient y ((ω : DifferentialForm (Euclid P) n) y)‖ := by
            rw [norm_mul, Real.norm_natCast]
        _ ≤ (R'.mult y : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) y‖ :=
            mul_le_mul_of_nonneg_left (hunit _ _ hQ _) (Nat.cast_nonneg _)
        _ ≤ (R'.mult y : ℝ) * W := mul_le_mul_of_nonneg_left (hW y) (Nat.cast_nonneg _)
        _ = W * (R'.mult y : ℝ) := mul_comm _ _
    · rw [Set.indicator_of_notMem hy, image_eq_zero_of_notMem_tsupport hy, map_zero, mul_zero,
        norm_zero, mul_zero]
  -- Step 4: integrate the a.e. identity evaluated at `ω(x)`, using linearity of the integral
  obtain ⟨-, he⟩ := key R
  obtain ⟨hi₁, he₁⟩ := key R₁
  obtain ⟨hi₂, he₂⟩ := key R₂
  rw [← he, ← he₁, ← he₂, ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi₁.const_mul _) (hi₂.const_mul _)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]

/-- **Simon Ch. 6, Remark 3.2(1)**: the difference of two integer multiplicity currents in the
open set `U` is integer multiplicity.  Let `S = τ(M₁, θ₁, ξ₁)`, `T = τ(M₂, θ₂, ξ₂)`.  By the Upper
Density Theorem (Ch. 1, 3.6) the carriers have density zero at `Hⁿ`-a.e. point outside them, and
approximate tangent spaces ignore sets of density zero (Ch. 3, 1.4–1.5), so `T_yM₁ = T_yM₂` and
`ξ₂(y) = σ(y) ξ₁(y)` with a Borel sign `σ = ±1` for `Hⁿ`-a.e. `y ∈ M₁ ∩ M₂`.  Then
`S − T = τ(M, m, ζ)` with `M = (M₁ \ M₂) ∪ (M₂ \ M₁) ∪ {y ∈ M₁ ∩ M₂ : θ₁ ≠ σθ₂}` and
`(m, ζ) = (θ₁, ξ₁)`, `(θ₂, −ξ₂)`, `(|θ₁ − σθ₂|, ±ξ₁)` on the three pieces. -/
theorem Submission.dtc_isIntegerMultiplicity_sub : ∀ (P n : ℕ) (U : Set (Euclid P)) (S T : GeometricCurrentOn U n), IsOpen U → 0 < n → IsIntegerMultiplicity S → IsIntegerMultiplicity T → IsIntegerMultiplicity (S - T) := by
  classical
  intro P n U S T hU _hn hS hT
  obtain ⟨R₁, hR₁⟩ := hS
  obtain ⟨R₂, hR₂⟩ := hT
  -- Step 1: carriers are locally `Hⁿ`-finite in `U` (multiplicities are `≥ 1`)
  have hfin : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    apply setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
    intro x hx
    have := R.mult_pos x hx.1
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 this)
  -- Step 2 (F1): Upper Density Theorem (Simon 1.3.6), localized to `U`
  have F1 : ∀ A : Set (Euclid P), MeasurableSet A →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (A ∩ K) ≠ ∞) →
      ∀ᵐ y ∂(μHE[n] : Measure (Euclid P)), y ∈ U → y ∉ A →
        Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) := by
    intro A hA hAfin
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hzero : ∀ y : Euclid P,
        Poincare.SimonGMT.Chapter01.dimensionalUpperDensity
          ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) A y = 0 →
        Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) := by
      intro y h
      have hq : Tendsto (Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient
          ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) A y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        apply tendsto_of_le_liminf_of_limsup_le (zero_le)
        exact h.le
      have hω0 : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) ≠ 0 :=
        (Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos hn0).ne'
      have hωt : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) ≠ ∞ :=
        Poincare.SimonGMT.Chapter01.realUnitBallVolume_ne_top _
      have h2 := ENNReal.Tendsto.const_mul hq (Or.inr hωt)
        (a := Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ))
      rw [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ hρ
      simp only [Poincare.SimonGMT.Chapter01.dimensionalDensityQuotient,
        Measure.toOuterMeasure_apply]
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (le_of_lt hρ), ← mul_div_assoc,
        ENNReal.mul_div_mul_left _ _ hω0 hωt]
    -- null sets of Simon's `Hⁿ` are `μHE[n]`-null
    have bridge : ∀ Z : Set (Euclid P),
        Poincare.SimonGMT.Chapter01.simonHausdorffOuterMeasureReal (n : ℝ) Z = 0 →
          (μHE[n] : Measure (Euclid P)) Z = 0 := by
      intro Z hZ
      rw [Poincare.SimonGMT.Chapter01.simonHausdorffOuterMeasureReal_eq_scaled_hausdorffMeasure
        hn0] at hZ
      rw [smul_apply, smul_eq_mul] at hZ
      have hc : Poincare.SimonGMT.Chapter01.realUnitBallVolume (n : ℝ) / (2 : ℝ≥0∞) ^ (n : ℝ)
          ≠ 0 :=
        ENNReal.div_ne_zero.mpr
          ⟨(Poincare.SimonGMT.Chapter01.realUnitBallVolume_pos hn0).ne', by simp⟩
      have hH : (μH[(n : ℝ)] : Measure (Euclid P)) Z = 0 := by
        simpa using (mul_eq_zero.mp hZ).resolve_left hc
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
    -- countable cover of `U` by balls whose closures are compact subsets of `U`
    let ι := {p : Euclid P × ℝ // 0 < p.2 ∧ closedBall p.1 p.2 ⊆ U}
    obtain ⟨J, hJc, hJU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun i : ι => ball i.1.1 i.1.2) (fun _ => isOpen_ball)
    have hcover : U ⊆ ⋃ i : ι, ball i.1.1 i.1.2 := by
      intro x hx
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
      exact mem_iUnion.mpr ⟨⟨(x, ε / 2), half_pos hε,
        (closedBall_subset_ball (half_lt_self hε)).trans hεU⟩, mem_ball_self (half_pos hε)⟩
    let N : ι → Set (Euclid P) := fun i => {x | x ∉ A ∩ ball i.1.1 i.1.2 ∧
      Poincare.SimonGMT.Chapter01.dimensionalUpperDensity
        ((μHE[n] : Measure (Euclid P)).toOuterMeasure) (n : ℝ) (A ∩ ball i.1.1 i.1.2) x ≠ 0}
    have hN : ∀ i, (μHE[n] : Measure (Euclid P)) (N i) = 0 := by
      intro i
      apply bridge
      apply Poincare.SimonGMT.Chapter01.simon_theorem_3_6 _
        (Poincare.SimonGMT.Chapter01.measure_toOuterMeasure_isBorelRegular _) hn0
      · exact le_toOuterMeasure_caratheodory _ _ (hA.inter measurableSet_ball)
      · have := hAfin (closedBall i.1.1 i.1.2) (isCompact_closedBall _ _) i.2.2
        exact lt_of_le_of_lt (measure_mono (inter_subset_inter_right _ ball_subset_closedBall))
          this.lt_top
    rw [ae_iff]
    apply measure_mono_null (t := ⋃ i ∈ J, N i)
    · intro y hy
      simp only [mem_ofPred_eq, not_imp] at hy
      obtain ⟨hyU, hyA, hnot⟩ := hy
      have hy' := hcover hyU
      rw [← hJU] at hy'
      obtain ⟨i, hiJ, hyi⟩ := mem_iUnion₂.mp hy'
      refine mem_iUnion₂.mpr ⟨i, hiJ, fun h => hyA h.1, fun hden => hnot ?_⟩
      rw [Poincare.SimonGMT.Chapter01.dimensionalUpperDensity_inter_of_mem_nhds _ _ _ _ _
        (isOpen_ball.mem_nhds hyi)] at hden
      exact hzero y hden
    · exact (measure_biUnion_null_iff hJc).mpr fun i _ => hN i
  -- Step 3 (F2): approximate tangent spaces ignore sets of zero `n`-density
  have F2 : ∀ (A A' : Set (Euclid P)) (y : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ),
      MeasurableSet A → MeasurableSet A' → 0 < s →
      μHE[n] (A ∩ closedBall y s) ≠ ∞ → μHE[n] (A' ∩ closedBall y s) ≠ ∞ →
      Tendsto (fun ρ : ℝ => μHE[n] (((A \ A') ∪ (A' \ A)) ∩ closedBall y ρ) /
        ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) →
      HasApproximateTangentSpaceAt n A y Q → HasApproximateTangentSpaceAt n A' y Q := by
    intro A A' y Q s hA hA' hs hAfin hA'fin hD hTA
    refine ⟨hTA.1, fun f => ?_⟩
    set D := (A \ A') ∪ (A' \ A) with hDdef
    have hfc : Continuous f := map_continuous f
    have hfcs : HasCompactSupport f := f.hasCompactSupport
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hfcs
    obtain ⟨L₀, hL₀⟩ := hfcs.isCompact.isBounded.subset_closedBall (0 : Euclid P)
    set L := max L₀ 1 with hLdef
    have hL : 0 < L := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hfL : ∀ z, z ∉ closedBall (0 : Euclid P) L → f z = 0 := by
      intro z hz
      apply image_eq_zero_of_notMem_tsupport
      intro hzt
      exact hz (closedBall_subset_closedBall (le_max_left _ _) (hL₀ hzt))
    have hDm : MeasurableSet D := (hA.diff hA').union (hA'.diff hA)
    have hinj : ∀ r : ℝ, 0 < r → Injective (Poincare.SimonGMT.Chapter03.blowUpMap y r) := by
      intro r hr a b hab
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap] at hab
      have := smul_right_injective (Euclid P) (inv_ne_zero hr.ne') hab
      simpa using this
    have hmeasIm : ∀ r : ℝ, 0 < r → ∀ Z : Set (Euclid P), MeasurableSet Z →
        MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z) := by
      intro r hr Z hZ
      have : Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z = (fun w => r • w + y) ⁻¹' Z := by
        ext w
        simp only [mem_image, mem_preimage, Poincare.SimonGMT.Chapter03.blowUpMap]
        constructor
        · rintro ⟨z, hz, rfl⟩
          rwa [smul_inv_smul₀ hr.ne', sub_add_cancel]
        · intro hw
          exact ⟨r • w + y, hw, by rw [add_sub_cancel_right, inv_smul_smul₀ hr.ne']⟩
      rw [this]
      exact hZ.preimage (by fun_prop)
    have hintOn : ∀ Z : Set (Euclid P), MeasurableSet Z →
        μHE[n] (Z ∩ closedBall 0 L) ≠ ∞ → IntegrableOn f Z μHE[n] := by
      intro Z hZ hZfin
      have h1 : IntegrableOn f (Z ∩ closedBall 0 L) μHE[n] :=
        Measure.integrableOn_of_bounded hZfin hfc.aestronglyMeasurable (M := C)
          (Eventually.of_forall hC)
      exact h1.of_forall_sdiff_eq_zero hZ (fun z hz => hfL z (fun h => hz.2 ⟨hz.1, h⟩))
    have hnormle : ∀ Z : Set (Euclid P), MeasurableSet Z →
        μHE[n] (Z ∩ closedBall 0 L) ≠ ∞ →
        ‖∫ z in Z, f z ∂μHE[n]‖ ≤ C * (μHE[n] : Measure (Euclid P)).real (Z ∩ closedBall 0 L) := by
      intro Z hZ hZfin
      rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hZ inter_subset_left
        (fun z hz => hfL z (fun h => hz.2 ⟨hz.1, h⟩))]
      exact norm_setIntegral_le_of_norm_le_const hZfin.lt_top (fun z _ => hC z)
    -- the scaling identity: reused child `regcomp_atl_blowUp_measure_scaling`
    have hscale : ∀ r : ℝ, 0 < r → ∀ Z : Set (Euclid P),
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z ∩ closedBall 0 L) =
          (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (Z ∩ closedBall y (r * L)) :=
      fun r hr Z => Submission.regcomp_atl_blowUp_measure_scaling P n y r L Z hr
    have hfinS : ∀ Z ⊆ A ∪ A', ∀ r, 0 < r → r * L ≤ s →
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap y r '' Z ∩ closedBall 0 L) ≠ ∞ := by
      intro Z hZ r hr hrs
      rw [hscale r hr]
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top
        (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne')) ?_
      apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAfin, hA'fin⟩)
      calc μHE[n] (Z ∩ closedBall y (r * L))
          ≤ μHE[n] ((A ∩ closedBall y s) ∪ (A' ∩ closedBall y s)) := by
            apply measure_mono
            rintro z ⟨hzZ, hzB⟩
            have hzB' : z ∈ closedBall y s := closedBall_subset_closedBall hrs hzB
            rcases hZ hzZ with h | h
            · exact Or.inl ⟨h, hzB'⟩
            · exact Or.inr ⟨h, hzB'⟩
        _ ≤ _ := measure_union_le _ _
    have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        ‖(∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' A', f z ∂μHE[n]) -
            ∫ z in Poincare.SimonGMT.Chapter03.blowUpMap y r '' A, f z ∂μHE[n]‖ ≤
          2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
            ENNReal.ofReal ((r * L) ^ n)).toReal) := by
      have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ r * L ≤ s := by
        filter_upwards [Ioo_mem_nhdsGT (div_pos hs hL)] with r hr
        refine ⟨hr.1, ?_⟩
        have := hr.2
        rw [lt_div_iff₀ hL] at this
        linarith
      filter_upwards [hpos] with r ⟨hr, hrs⟩
      set η := Poincare.SimonGMT.Chapter03.blowUpMap y r with hη
      have hinjr : Injective η := hinj r hr
      have hsub1 : A' ∩ A ⊆ A ∪ A' := fun z hz => Or.inl hz.2
      have hsub2 : A' \ A ⊆ A ∪ A' := fun z hz => Or.inr hz.1
      have hsub3 : A \ A' ⊆ A ∪ A' := fun z hz => Or.inl hz.1
      have hsubD : D ⊆ A ∪ A' := union_subset hsub3 hsub2
      have hI1 := hintOn _ (hmeasIm r hr _ (hA'.inter hA)) (hfinS _ hsub1 r hr hrs)
      have hI2 := hintOn _ (hmeasIm r hr _ (hA'.diff hA)) (hfinS _ hsub2 r hr hrs)
      have hI3 := hintOn _ (hmeasIm r hr _ (hA.diff hA')) (hfinS _ hsub3 r hr hrs)
      have hsplitA' : η '' A' = η '' (A' ∩ A) ∪ η '' (A' \ A) := by
        rw [← image_union, inter_union_sdiff]
      have hsplitA : η '' A = η '' (A' ∩ A) ∪ η '' (A \ A') := by
        rw [← image_union, inter_comm, inter_union_sdiff]
      have hdisj1 : Disjoint (η '' (A' ∩ A)) (η '' (A' \ A)) :=
        (disjoint_image_iff hinjr).mpr (disjoint_sdiff_inter.symm)
      have hdisj2 : Disjoint (η '' (A' ∩ A)) (η '' (A \ A')) := by
        rw [disjoint_image_iff hinjr, inter_comm]
        exact disjoint_sdiff_inter.symm
      rw [hsplitA', hsplitA, setIntegral_union hdisj1 (hmeasIm r hr _ (hA'.diff hA)) hI1 hI2,
        setIntegral_union hdisj2 (hmeasIm r hr _ (hA.diff hA')) hI1 hI3]
      have hfinD := hfinS D hsubD r hr hrs
      have hmono2 : (μHE[n] : Measure (Euclid P)).real (η '' (A' \ A) ∩ closedBall 0 L) ≤
          (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
        measureReal_mono (inter_subset_inter_left _ (image_mono subset_union_right)) hfinD
      have hmono3 : (μHE[n] : Measure (Euclid P)).real (η '' (A \ A') ∩ closedBall 0 L) ≤
          (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
        measureReal_mono (inter_subset_inter_left _ (image_mono subset_union_left)) hfinD
      have hn2 := hnormle _ (hmeasIm r hr _ (hA'.diff hA)) (hfinS _ hsub2 r hr hrs)
      have hn3 := hnormle _ (hmeasIm r hr _ (hA.diff hA')) (hfinS _ hsub3 r hr hrs)
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      have hkey : (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) =
          L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) / ENNReal.ofReal ((r * L) ^ n)).toReal := by
        have hfin' : μHE[n] (D ∩ closedBall y (r * L)) ≠ ∞ := by
          have h0 := hfinD
          rw [hscale r hr] at h0
          have ha0 : (ENNReal.ofReal r)⁻¹ ^ n ≠ 0 :=
            pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
          exact fun hb => h0 (ENNReal.mul_eq_top.mpr (Or.inl ⟨ha0, hb⟩))
        rw [measureReal_def, hscale r hr, ENNReal.toReal_mul, ENNReal.toReal_div,
          ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_pow, ENNReal.toReal_inv,
          ENNReal.toReal_ofReal hr.le, mul_pow]
        have hrn : r ^ n ≠ 0 := pow_ne_zero n hr.ne'
        have hLn : L ^ n ≠ 0 := pow_ne_zero n hL.ne'
        rw [inv_pow, mul_div_assoc', mul_comm (L ^ n), mul_div_mul_right _ _ hLn, div_eq_inv_mul]
      calc ‖(∫ z in η '' (A' ∩ A), f z ∂μHE[n]) + (∫ z in η '' (A' \ A), f z ∂μHE[n]) -
            ((∫ z in η '' (A' ∩ A), f z ∂μHE[n]) + ∫ z in η '' (A \ A'), f z ∂μHE[n])‖
          = ‖(∫ z in η '' (A' \ A), f z ∂μHE[n]) - ∫ z in η '' (A \ A'), f z ∂μHE[n]‖ := by
            congr 1; ring
        _ ≤ ‖∫ z in η '' (A' \ A), f z ∂μHE[n]‖ + ‖∫ z in η '' (A \ A'), f z ∂μHE[n]‖ :=
            norm_sub_le _ _
        _ ≤ C * (μHE[n] : Measure (Euclid P)).real (η '' (A' \ A) ∩ closedBall 0 L) +
            C * (μHE[n] : Measure (Euclid P)).real (η '' (A \ A') ∩ closedBall 0 L) :=
            add_le_add hn2 hn3
        _ ≤ C * (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) +
            C * (μHE[n] : Measure (Euclid P)).real (η '' D ∩ closedBall 0 L) :=
            add_le_add (mul_le_mul_of_nonneg_left hmono2 hC0)
              (mul_le_mul_of_nonneg_left hmono3 hC0)
        _ = 2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
              ENNReal.ofReal ((r * L) ^ n)).toReal) := by
            rw [hkey]; ring
    have hlim : Tendsto (fun r : ℝ => 2 * C * (L ^ n * (μHE[n] (D ∩ closedBall y (r * L)) /
        ENNReal.ofReal ((r * L) ^ n)).toReal)) (𝓝[>] 0) (𝓝 0) := by
      have hmap : Tendsto (fun r : ℝ => r * L) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have h0 : Tendsto (fun r : ℝ => r * L) (𝓝 0) (𝓝 (0 * L)) :=
            (continuous_id.mul continuous_const).tendsto 0
          rw [zero_mul] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hr hL
      have h1 := hD.comp hmap
      have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      have h3 := (h2.const_mul (L ^ n)).const_mul (2 * C)
      simpa [Function.comp_def] using h3
    have hdiff := squeeze_zero_norm' hbound hlim
    have h3 := (hTA.2 f).add hdiff
    simp only [add_zero, add_sub_cancel] at h3
    exact h3
  -- Steps 2–3 combined: a.e. on `A ∩ B` the tangent spaces of `A` and `B` coincide
  have F3 : ∀ A B : Set (Euclid P), MeasurableSet A → MeasurableSet B → A ⊆ U → B ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (A ∩ K) ≠ ∞) →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) →
      ∀ᵐ y ∂(μHE[n].restrict (A ∩ B)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n A y Q ↔ HasApproximateTangentSpaceAt n B y Q := by
    intro A B hA hB hAU hBU hAfin hBfin
    set D : Set (Euclid P) := (A \ B) ∪ (B \ A) with hD
    have hDmeas : MeasurableSet D := (hA.diff hB).union (hB.diff hA)
    have hDfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (D ∩ K) ≠ ∞ := by
      intro K hK hKU
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hAfin K hK hKU, hBfin K hK hKU⟩) ?_
      calc μHE[n] (D ∩ K) ≤ μHE[n] ((A ∩ K) ∪ (B ∩ K)) := by
            apply measure_mono
            rintro x ⟨hx | hx, hxK⟩
            · exact Or.inl ⟨hx.1, hxK⟩
            · exact Or.inr ⟨hx.1, hxK⟩
        _ ≤ μHE[n] (A ∩ K) + μHE[n] (B ∩ K) := measure_union_le _ _
    have h1 := F1 D hDmeas hDfin
    have h1' : ∀ᵐ y ∂(μHE[n].restrict (A ∩ B)), y ∈ U → y ∉ D →
        Tendsto (fun ρ : ℝ => μHE[n] (D ∩ closedBall y ρ) / ENNReal.ofReal (ρ ^ n))
          (𝓝[>] 0) (𝓝 0) :=
      ae_restrict_of_ae h1
    filter_upwards [h1', ae_restrict_mem (hA.inter hB)] with y hy hyAB
    have hyU : y ∈ U := hAU hyAB.1
    have hyD : y ∉ D := by
      rintro (h | h)
      · exact h.2 hyAB.2
      · exact h.2 hyAB.1
    have hdens := hy hyU hyD
    obtain ⟨s, hs, hsU⟩ : ∃ s > 0, closedBall y s ⊆ U := by
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hyU
      exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
    have hK : IsCompact (closedBall y s) := isCompact_closedBall y s
    have hAs := hAfin _ hK hsU
    have hBs := hBfin _ hK hsU
    intro Q
    constructor
    · intro hQ
      exact F2 A B y Q s hA hB hs hAs hBs hdens hQ
    · intro hQ
      have hdens' : Tendsto (fun ρ : ℝ => μHE[n] (((B \ A) ∪ (A \ B)) ∩ closedBall y ρ) /
          ENNReal.ofReal (ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
        simpa only [hD, Set.union_comm] using hdens
      exact F2 B A y Q s hB hA hs hBs hAs hdens' hQ
  -- Step 6 with Step 4 (reused child `rsdic_unitOrientation_eq_or_eq_neg`):
  -- `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hov : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)),
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    have hL := F3 R₁.carrier R₂.carrier R₁.measurableSet_carrier R₂.measurableSet_carrier
      R₁.carrier_subset R₂.carrier_subset (hfin R₁) (hfin R₂)
    have ho₁ : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R₁.carrier x Q ∧ IsUnitOrientationOf (R₁.orient x) Q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left R₁.orients
    have ho₂ : ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R₂.carrier x Q ∧ IsUnitOrientationOf (R₂.orient x) Q :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right R₂.orients
    filter_upwards [hL, ho₁, ho₂] with x hx h₁ h₂
    obtain ⟨Q₁, hT₁, hO₁⟩ := h₁
    obtain ⟨Q₂, hT₂, hO₂⟩ := h₂
    have hT₁' : HasApproximateTangentSpaceAt n R₂.carrier x Q₁ := (hx Q₁).1 hT₁
    have hQ : Q₁ = Q₂ := hT₁'.unique hT₂
    subst hQ
    exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₁ hO₁ hO₂
  -- Step 8: IMRep fields for sub-data of `R₁`, `R₂`
  have recombine : ∀ (M : Set (Euclid P)) (m : Euclid P → ℕ) (ζ : Euclid P → MultiVector P n),
      MeasurableSet M → M ⊆ R₁.carrier ∪ R₂.carrier → Measurable m → (∀ x ∈ M, 0 < m x) →
      (∀ x ∈ M, m x ≤ R₁.carrier.indicator R₁.mult x + R₂.carrier.indicator R₂.mult x) →
      AEStronglyMeasurable ζ (μHE[n].restrict M) →
      (∀ᵐ x ∂(μHE[n].restrict (M ∩ R₁.carrier)), ζ x = R₁.orient x ∨ ζ x = -R₁.orient x) →
      (∀ᵐ x ∂(μHE[n].restrict (M \ R₁.carrier)), ζ x = R₂.orient x ∨ ζ x = -R₂.orient x) →
      ∃ R : IMRep U n, R.carrier = M ∧ R.mult = m ∧ R.orient = ζ := by
    intro M m ζ hM hMsub hm hmpos hmle hζ h₁ h₂
    have hMU : M ⊆ U := hMsub.trans (union_subset R₁.carrier_subset R₂.carrier_subset)
    have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M ∩ K) ≠ ∞ := by
      intro K hK hKU
      refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin R₁ K hK hKU, hfin R₂ K hK hKU⟩) ?_
      calc μHE[n] (M ∩ K) ≤ μHE[n] ((R₁.carrier ∩ K) ∪ (R₂.carrier ∩ K)) := by
            apply measure_mono
            rintro x ⟨hx, hxK⟩
            rcases hMsub hx with h | h
            · exact Or.inl ⟨h, hxK⟩
            · exact Or.inr ⟨h, hxK⟩
        _ ≤ _ := measure_union_le _ _
    have hneg : ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ξ Q → IsUnitOrientationOf (-ξ) Q := by
      rintro ξ Q ⟨τ, hτ, hspan, h | h⟩
      · exact ⟨τ, hτ, hspan, Or.inr fun α => by simp [h α]⟩
      · exact ⟨τ, hτ, hspan, Or.inl fun α => by simp [h α]⟩
    have hpm : ∀ (ξ ξ' : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ξ' Q → (ξ = ξ' ∨ ξ = -ξ') → IsUnitOrientationOf ξ Q := by
      rintro ξ ξ' Q hO (h | h)
      · rw [h]; exact hO
      · rw [h]; exact hneg _ _ hO
    have horient : ∀ᵐ x ∂(μHE[n].restrict M), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q := by
      have key : ∀ᵐ x ∂(μHE[n].restrict ((M ∩ R₁.carrier) ∪ (M \ R₁.carrier))),
          ∃ Q : Submodule ℝ (Euclid P),
            HasApproximateTangentSpaceAt n M x Q ∧ IsUnitOrientationOf (ζ x) Q := by
        rw [ae_restrict_union_iff]
        constructor
        · have hL := F3 M R₁.carrier hM R₁.measurableSet_carrier hMU R₁.carrier_subset hMfin
            (hfin R₁)
          have ho := ae_restrict_of_ae_restrict_of_subset (inter_subset_right (s := M))
            R₁.orients
          filter_upwards [hL, ho, h₁] with x hx hox hζx
          obtain ⟨Q, hTQ, hO⟩ := hox
          exact ⟨Q, (hx Q).2 hTQ, hpm _ _ _ hO hζx⟩
        · have hL := F3 M R₂.carrier hM R₂.measurableSet_carrier hMU R₂.carrier_subset hMfin
            (hfin R₂)
          have hsub : M \ R₁.carrier ⊆ M ∩ R₂.carrier :=
            fun x hx => ⟨hx.1, (hMsub hx.1).resolve_left hx.2⟩
          have hL' := ae_restrict_of_ae_restrict_of_subset hsub hL
          have ho := ae_restrict_of_ae_restrict_of_subset (hsub.trans inter_subset_right)
            R₂.orients
          filter_upwards [hL', ho, h₂] with x hx hox hζx
          obtain ⟨Q, hTQ, hO⟩ := hox
          exact ⟨Q, (hx Q).2 hTQ, hpm _ _ _ hO hζx⟩
      rwa [inter_union_sdiff] at key
    have hrect : CountablyRectifiable n M := by
      have hU12 : CountablyRectifiable n
          (⋃ i : ℕ, (if i = 0 then R₁.carrier else R₂.carrier)) := by
        apply Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
        intro i
        split_ifs
        · exact R₁.rectifiable
        · exact R₂.rectifiable
      apply hU12.mono
      intro x hx
      rcases hMsub hx with h | h
      · exact mem_iUnion.2 ⟨0, by simpa using h⟩
      · exact mem_iUnion.2 ⟨1, by simpa using h⟩
    have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
        ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
      intro K hK hKU
      have hm1 : Measurable fun x => (R₁.mult x : ℝ≥0∞) :=
        measurable_from_nat.comp R₁.measurable_mult
      have hS1 : MeasurableSet (R₁.carrier ∩ K) :=
        R₁.measurableSet_carrier.inter hK.measurableSet
      have hS2 : MeasurableSet (R₂.carrier ∩ K) :=
        R₂.measurableSet_carrier.inter hK.measurableSet
      have hbound : ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n] ≤
          ∫⁻ x in R₁.carrier ∩ K, (R₁.mult x : ℝ≥0∞) ∂μHE[n] +
            ∫⁻ x in R₂.carrier ∩ K, (R₂.mult x : ℝ≥0∞) ∂μHE[n] := by
        calc ∫⁻ x in M ∩ K, (m x : ℝ≥0∞) ∂μHE[n]
            ≤ ∫⁻ x in M ∩ K, ((R₁.carrier ∩ K).indicator (fun x => (R₁.mult x : ℝ≥0∞)) x +
                (R₂.carrier ∩ K).indicator (fun x => (R₂.mult x : ℝ≥0∞)) x) ∂μHE[n] := by
              apply setLIntegral_mono' (hM.inter hK.measurableSet)
              intro x hx
              have h := hmle x hx.1
              have hxK := hx.2
              by_cases h1 : x ∈ R₁.carrier <;> by_cases h2 : x ∈ R₂.carrier <;>
                simp [h1, h2, hxK] at h ⊢ <;> exact_mod_cast h
          _ ≤ ∫⁻ x, ((R₁.carrier ∩ K).indicator (fun x => (R₁.mult x : ℝ≥0∞)) x +
                (R₂.carrier ∩ K).indicator (fun x => (R₂.mult x : ℝ≥0∞)) x) ∂μHE[n] :=
              setLIntegral_le_lintegral _ _
          _ = _ := by
              rw [lintegral_add_left (hm1.indicator hS1), lintegral_indicator hS1,
                lintegral_indicator hS2]
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨R₁.locallyIntegrable_mult K hK hKU,
        R₂.locallyIntegrable_mult K hK hKU⟩) hbound
    exact ⟨⟨M, m, ζ, hM, hMU, hrect, hm, hmpos, hint, hζ, horient⟩, rfl, rfl, rfl⟩
  -- Steps 5–7: Borel orientations, Borel sign, the new data `(M, m, ζ)`
  obtain ⟨R, hR⟩ : ∃ R : IMRep U n, ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      ∀ α : Covector (Euclid P) n,
        R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y α) x =
          R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) * R₁.orient y α) x -
            R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) * R₂.orient y α) x := by
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) := by
      let M : MetricSpace (MultiVector P n) := inferInstance
      have h1 : @TopologicalSpace.PseudoMetrizableSpace (MultiVector P n)
          (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) :=
        @UniformSpace.pseudoMetrizableSpace (MultiVector P n) PseudoMetricSpace.toUniformSpace
          inferInstance
      have h2 : @T0Space (MultiVector P n)
          (PseudoMetricSpace.toUniformSpace.toTopologicalSpace) := inferInstance
      exact @TopologicalSpace.MetrizableSpace.mk _ _ h1 h2
    have : ContinuousNeg (MultiVector P n) := by
      exact @IsTopologicalAddGroup.toContinuousNeg _ _ _ ContinuousLinearMap.isTopologicalAddGroup
    set M₁ := R₁.carrier with hM₁def
    set M₂ := R₂.carrier with hM₂def
    have hM₁ : MeasurableSet M₁ := R₁.measurableSet_carrier
    have hM₂ : MeasurableSet M₂ := R₂.measurableSet_carrier
    set ξt₁ := R₁.aestronglyMeasurable_orient.mk R₁.orient with hξt₁def
    set ξt₂ := R₂.aestronglyMeasurable_orient.mk R₂.orient with hξt₂def
    have hs₁ : StronglyMeasurable ξt₁ := R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk
    have hs₂ : StronglyMeasurable ξt₂ := R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk
    have he₁ : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₁ → R₁.orient x = ξt₁ x :=
      (ae_restrict_iff' hM₁).1 R₁.aestronglyMeasurable_orient.ae_eq_mk
    have he₂ : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₂ → R₂.orient x = ξt₂ x :=
      (ae_restrict_iff' hM₂).1 R₂.aestronglyMeasurable_orient.ae_eq_mk
    have hov' : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M₁ ∩ M₂ →
        R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x :=
      (ae_restrict_iff' (hM₁.inter hM₂)).1 hov
    set σ : Euclid P → ℤ := fun x => if ξt₂ x = ξt₁ x then 1 else -1 with hσdef
    have hσmeas : Measurable σ :=
      Measurable.ite (hs₂.measurableSet_eq_fun hs₁) measurable_const measurable_const
    set d : Euclid P → ℤ := fun x => (R₁.mult x : ℤ) - σ x * (R₂.mult x : ℤ) with hddef
    have hdmeas : Measurable d := by
      have h1 : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
      have h2 : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
      exact h1.sub (hσmeas.mul h2)
    set G : Set (Euclid P) := {x | x ∈ M₁ ∩ M₂ ∧ d x ≠ 0} with hGdef
    have hG : MeasurableSet G :=
      (hM₁.inter hM₂).inter (hdmeas (measurableSet_singleton 0).compl)
    set M : Set (Euclid P) := (M₁ \ M₂) ∪ (M₂ \ M₁) ∪ G with hMdef
    have hM : MeasurableSet M := ((hM₁.diff hM₂).union (hM₂.diff hM₁)).union hG
    set m : Euclid P → ℕ := fun x => if x ∈ M₁ \ M₂ then R₁.mult x
      else if x ∈ M₂ \ M₁ then R₂.mult x else if x ∈ M₁ ∩ M₂ then (d x).natAbs else 0
      with hmdef
    set ζ : Euclid P → MultiVector P n := fun x => if x ∈ M₁ \ M₂ then ξt₁ x
      else if x ∈ M₂ \ M₁ then -ξt₂ x else if 0 < d x then ξt₁ x else -ξt₁ x with hζdef
    have hmmeas : Measurable m := by
      refine Measurable.ite (hM₁.diff hM₂) R₁.measurable_mult
        (Measurable.ite (hM₂.diff hM₁) R₂.measurable_mult
          (Measurable.ite (hM₁.inter hM₂)
            ((Measurable.of_discrete (f := Int.natAbs)).comp hdmeas) measurable_const))
    have hζmeas : StronglyMeasurable ζ := by
      refine StronglyMeasurable.ite (hM₁.diff hM₂) hs₁
        (StronglyMeasurable.ite (hM₂.diff hM₁) hs₂.neg (StronglyMeasurable.ite ?_ hs₁ hs₁.neg))
      exact hdmeas (measurableSet_Ioi (a := (0 : ℤ)))
    have hMsub : M ⊆ M₁ ∪ M₂ := by
      rintro x ((h | h) | h)
      · exact Or.inl h.1
      · exact Or.inr h.1
      · exact Or.inl h.1.1
    have hmpos : ∀ x ∈ M, 0 < m x := by
      rintro x ((h | h) | h)
      · simp only [hmdef, ite_eq_left h]; exact R₁.mult_pos x h.1
      · have hn : x ∉ M₁ \ M₂ := fun h' => h.2 h'.1
        simp only [hmdef, ite_eq_right hn, ite_eq_left h]; exact R₂.mult_pos x h.1
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hmdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left h.1]
        exact Int.natAbs_pos.2 h.2
    have hσpm : ∀ x, σ x = 1 ∨ σ x = -1 := by
      intro x; simp only [hσdef]; split_ifs <;> simp
    have hmle : ∀ x ∈ M, m x ≤ M₁.indicator R₁.mult x + M₂.indicator R₂.mult x := by
      rintro x ((h | h) | h)
      · simp only [hmdef, ite_eq_left h, indicator_of_mem h.1, indicator_of_notMem h.2]; omega
      · have hn : x ∉ M₁ \ M₂ := fun h' => h.2 h'.1
        simp only [hmdef, ite_eq_right hn, ite_eq_left h, indicator_of_mem h.1, indicator_of_notMem h.2]
        omega
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hmdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left h.1, indicator_of_mem h.1.1,
          indicator_of_mem h.1.2]
        simp only [hddef]
        rcases hσpm x with hs | hs <;> rw [hs] <;> omega
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M ∩ M₁)), ζ x = R₁.orient x ∨ ζ x = -R₁.orient x := by
      rw [ae_restrict_iff' (hM.inter hM₁)]
      filter_upwards [he₁] with x hx hxM
      have hxe := hx hxM.2
      rcases hxM.1 with (h | h) | h
      · left; simp only [hζdef, ite_eq_left h]; exact hxe.symm
      · exact absurd hxM.2 h.2
      · have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 h.1.2
        have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 h.1.1
        simp only [hζdef, ite_eq_right hn1, ite_eq_right hn2]
        split_ifs
        · left; exact hxe.symm
        · right; rw [hxe]
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M \ M₁)), ζ x = R₂.orient x ∨ ζ x = -R₂.orient x := by
      rw [ae_restrict_iff' (hM.diff hM₁)]
      filter_upwards [he₂] with x hx hxM
      have hx2 : x ∈ M₂ \ M₁ := ⟨(hMsub hxM.1).resolve_left hxM.2, hxM.2⟩
      have hn1 : x ∉ M₁ \ M₂ := fun h' => hxM.2 h'.1
      right; simp only [hζdef, ite_eq_right hn1, ite_eq_left hx2]; rw [hx hx2.1]
    obtain ⟨R, hRc, hRm, hRo⟩ := recombine M m ζ hM hMsub hmmeas hmpos hmle
      hζmeas.aestronglyMeasurable h₁ h₂
    refine ⟨R, ?_⟩
    rw [hRc, hRm, hRo]
    filter_upwards [he₁, he₂, hov'] with x hx₁ hx₂ hx₃
    intro α
    by_cases hA : x ∈ M₁ <;> by_cases hB : x ∈ M₂
    · -- overlap
      have hAB : x ∈ M₁ ∩ M₂ := ⟨hA, hB⟩
      have hn1 : x ∉ M₁ \ M₂ := fun h' => h'.2 hB
      have hn2 : x ∉ M₂ \ M₁ := fun h' => h'.2 hA
      have e₁ := hx₁ hA
      have e₂ := hx₂ hB
      have hsig : R₂.orient x α = ((σ x : ℤ) : ℝ) * R₁.orient x α := by
        rcases hx₃ hAB with h | h
        · have : ξt₂ x = ξt₁ x := by rw [← e₁, ← e₂, h]
          simp only [hσdef, ite_eq_left this]; simp [h]
        · by_cases hq : ξt₂ x = ξt₁ x
          · have : R₂.orient x = R₁.orient x := by rw [e₁, e₂, hq]
            simp only [hσdef, ite_eq_left hq]; simp [this]
          · simp only [hσdef, ite_eq_right hq]; simp [h]
      rw [indicator_of_mem hA, indicator_of_mem hB, hsig]
      have hcoef : (R₁.mult x : ℝ) * R₁.orient x α -
          (R₂.mult x : ℝ) * (((σ x : ℤ) : ℝ) * R₁.orient x α) =
          ((d x : ℤ) : ℝ) * R₁.orient x α := by
        simp only [hddef]; push_cast; ring
      rw [hcoef]
      rcases lt_trichotomy (d x) 0 with hd | hd | hd
      · have hxM : x ∈ M := Or.inr ⟨hAB, hd.ne⟩
        rw [indicator_of_mem hxM]
        simp only [hmdef, hζdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left hAB, ite_eq_right (not_lt.2 hd.le)]
        have hc : (((d x).natAbs : ℕ) : ℝ) = -((d x : ℤ) : ℝ) := by
          have h1 : ((d x).natAbs : ℤ) = -(d x) := Int.ofNat_natAbs_of_nonpos hd.le
          have h2 : ((((d x).natAbs : ℕ) : ℤ) : ℝ) = ((-(d x) : ℤ) : ℝ) := by rw [h1]
          simpa using h2
        rw [hc, neg_apply, e₁]; ring
      · have hxM : x ∉ M := by
          rintro ((h | h) | h)
          · exact hn1 h
          · exact hn2 h
          · exact h.2 hd
        rw [indicator_of_notMem hxM, hd]; simp
      · have hxM : x ∈ M := Or.inr ⟨hAB, hd.ne'⟩
        rw [indicator_of_mem hxM]
        simp only [hmdef, hζdef, ite_eq_right hn1, ite_eq_right hn2, ite_eq_left hAB, ite_eq_left hd]
        have hc : (((d x).natAbs : ℕ) : ℝ) = ((d x : ℤ) : ℝ) := by
          have h1 : ((d x).natAbs : ℤ) = d x := Int.natAbs_of_nonneg hd.le
          have h2 : ((((d x).natAbs : ℕ) : ℤ) : ℝ) = ((d x : ℤ) : ℝ) := by rw [h1]
          simpa using h2
        rw [hc, e₁]
    · -- only in `M₁`
      have h : x ∈ M₁ \ M₂ := ⟨hA, hB⟩
      have hxM : x ∈ M := Or.inl (Or.inl h)
      rw [indicator_of_mem hxM, indicator_of_mem hA, indicator_of_notMem hB, sub_zero]
      simp only [hmdef, hζdef, ite_eq_left h]
      rw [hx₁ hA]
    · -- only in `M₂`
      have h : x ∈ M₂ \ M₁ := ⟨hB, hA⟩
      have hn : x ∉ M₁ \ M₂ := fun h' => hA h'.1
      have hxM : x ∈ M := Or.inl (Or.inr h)
      rw [indicator_of_mem hxM, indicator_of_notMem hA, indicator_of_mem hB, zero_sub]
      simp only [hmdef, hζdef, ite_eq_right hn, ite_eq_left h]
      rw [hx₂ hB, neg_apply]; ring
    · -- outside both
      have hxM : x ∉ M := fun h => (hMsub h).elim hA hB
      rw [indicator_of_notMem hxM, indicator_of_notMem hA, indicator_of_notMem hB, sub_zero]
  -- Step 9 (reused child `rsdic_imrep_action_int_combination` with `p₁ = 1`, `p₂ = -1`)
  have hRv : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)),
      R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
        ((1 : ℤ) : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x +
          ((-1 : ℤ) : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
    filter_upwards [hR] with x hx
    ext α
    have h := hx α
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases h0 : x ∈ R.carrier <;> by_cases h1 : x ∈ R₁.carrier <;>
      by_cases h2 : x ∈ R₂.carrier <;>
      simp only [indicator_of_mem, indicator_of_notMem, h0, h1, h2, not_false_eq_true,
        smul_apply, smul_eq_mul, zero_apply] at h ⊢ <;> push_cast <;> linarith
  refine ⟨R, fun ω => ?_⟩
  rw [Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R 1 (-1) hRv ω, ← hR₁ ω,
    ← hR₂ ω]
  have hsub : (S - T) ω = S ω - T ω := rfl
  rw [hsub]
  push_cast
  ring

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
