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

/-- An open `U ⊆ ℝᴾ` is exhausted by the compact sets
`Kᵢ = B̄(0, i + 1) ∩ {x : 1 / (i + 1) ≤ dist(x, y) for all y ∉ U}`: each `Kᵢ ⊆ U` (take `y = x`),
and a compact `C ⊆ U` has a margin `δ > 0` with `thickening δ C ⊆ U` and a radius `R` with
`C ⊆ B̄(0, R)`, so `C ⊆ Kᵢ` once `1 / (i + 1) < δ` and `R ≤ i + 1`. -/
theorem Submission.dor_lmbs_tfa_compact_exhaustion : ∀ (P : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ K : ℕ → Set (Euclid P), (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ U) ∧ ∀ C : Set (Euclid P), IsCompact C → C ⊆ U → ∃ i, C ⊆ K i := by
  intro P U hU
  refine ⟨fun i => closedBall (0 : Euclid P) ((i : ℝ) + 1) ∩ ⋂ y ∈ Uᶜ, {x | 1 / ((i : ℝ) + 1) ≤ dist x y},
    fun i => ?_, fun i => ?_, fun C hC hCU => ?_⟩
  · exact (isCompact_closedBall _ _).inter_right
      (isClosed_biInter fun y _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  · -- `x ∉ U` would give `1 / (i + 1) ≤ dist x x = 0`
    intro x hx
    by_contra hxU
    have h : 1 / ((i : ℝ) + 1) ≤ dist x x := mem_iInter₂.1 hx.2 x hxU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    linarith
  · obtain ⟨δ, hδ, hδU⟩ := hC.exists_thickening_subset_open hU hCU
    obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : Euclid P)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    obtain ⟨M, hM⟩ := exists_nat_ge R
    have hNi : (N : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_left N M
    have hMi : (M : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_right N M
    refine ⟨max N M, fun x hx => ⟨?_, mem_iInter₂.2 fun y hy => ?_⟩⟩
    · have hxR := mem_closedBall.1 (hR hx)
      rw [mem_closedBall]
      linarith
    · -- `y ∉ thickening δ C` gives `δ ≤ dist x y`
      have hxy : δ ≤ dist x y := by
        by_contra h
        exact hy (hδU (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
      have hle : 1 / (((max N M : ℕ) : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      show 1 / (((max N M : ℕ) : ℝ) + 1) ≤ dist x y
      linarith
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_lmbs_tfa_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v

/-- Test forms supported in a fixed compact `K` have a countable subfamily `D` approximating every
such `ω` together with `dω`, uniformly on `ℝᴾ`.  The covector spaces are finite-dimensional
(`dor_lmbs_tfa_covector_finiteDimensional`), so `C(K, Λⁿ × Λⁿ⁺¹)` is second countable; pull back
a countable dense subset of the image of `X = {ω : spt ω ⊆ K}` under `Φ ω = (ω, dω)|_K`.  On `K`
the pointwise distances are at most the uniform distance; off `K` all four values vanish. -/
theorem Submission.dor_lmbs_tfa_fixed_support_dense : ∀ (P n : ℕ) (U K : Set (Euclid P)), IsCompact K → ∃ D : Set (TestFormOn U n), D.Countable ∧ (∀ η ∈ D, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K) ∧ ∀ ω : TestFormOn U n, tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → ∀ ε : ℝ, 0 < ε → ∃ η ∈ D, (∀ x, dist ((ω : DifferentialForm (Euclid P) n) x) ((η : DifferentialForm (Euclid P) n) x) < ε) ∧ ∀ x, dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x) (exteriorDerivative (η : DifferentialForm (Euclid P) n) x) < ε := by
  intro P n U K hK
  -- Step 1: a form supported in `K` vanishes off `K`, and so does its exterior derivative
  have hzero : ∀ η : TestFormOn U n, tsupport (η : DifferentialForm (Euclid P) n) ⊆ K →
      ∀ x ∉ K, (η : DifferentialForm (Euclid P) n) x = 0 ∧
        exteriorDerivative (η : DifferentialForm (Euclid P) n) x = 0 := fun η hη x hx =>
    ⟨image_eq_zero_of_notMem_tsupport fun h => hx (hη h),
      image_eq_zero_of_notMem_tsupport fun h => hx (hη (tsupport_exteriorDerivative_subset _ h))⟩
  -- Step 2: `Λⁿ` and `Λⁿ⁺¹` are finite-dimensional, hence proper and second countable
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P n
  have := Submission.dor_lmbs_tfa_covector_finiteDimensional P (n + 1)
  have : ProperSpace (Covector (Euclid P) n) := FiniteDimensional.proper_real _
  have : ProperSpace (Covector (Euclid P) (n + 1)) := FiniteDimensional.proper_real _
  have : SecondCountableTopology (Covector (Euclid P) n) := secondCountable_of_proper
  have : SecondCountableTopology (Covector (Euclid P) (n + 1)) := secondCountable_of_proper
  -- Step 3: `K` is compact, so `C(K, Λⁿ × Λⁿ⁺¹)` carries the sup metric, and it is second
  -- countable: up to `ε`, `f` is determined by a modulus `j` of uniform continuity at scale `ε / 4`
  -- and by the indices, in a dense sequence `s`, of `ε / 4`-approximations of its values on a
  -- finite `1 / (j + 1)`-net `t j` of `K`
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : SecondCountableTopology C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := by
    refine Metric.secondCountable_of_countable_discretization
      (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1))) fun ε hε => ?_
    obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq
      (Covector (Euclid P) n × Covector (Euclid P) (n + 1))
    choose r hr using fun y : Covector (Euclid P) n × Covector (Euclid P) (n + 1) =>
      hs.exists_dist_lt y (by positivity : (0 : ℝ) < ε / 4)
    have hnet : ∀ j : ℕ, ∃ t : Finset K, ∀ x : K, ∃ p ∈ t, dist x p < 1 / ((j : ℝ) + 1) := by
      intro j
      obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (univ : Set K)).elim_nhds_subcover
        (fun x => ball x (1 / ((j : ℝ) + 1))) fun x _ => ball_mem_nhds x (by positivity)
      exact ⟨t, fun x => by simpa using ht (mem_univ x)⟩
    choose t ht using hnet
    have hmod : ∀ f : C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)), ∃ j : ℕ,
        ∀ x y : K, dist x y < 1 / ((j : ℝ) + 1) → dist (f x) (f y) < ε / 4 := by
      intro f
      obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.1
        (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / 4) (by positivity)
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt hδ
      exact ⟨j, fun x y hxy => hfδ (hxy.trans hj)⟩
    choose J hJ using hmod
    refine ⟨ℕ × List ℕ, inferInstance, fun f => (J f, (t (J f)).toList.map fun p => r (f p)),
      fun f g hfg => (ContinuousMap.dist_le hε.le).2 fun x => ?_⟩
    obtain ⟨hj, hl⟩ := Prod.mk.inj hfg
    rw [← hj] at hl
    -- `x` is `1 / (j + 1)`-close to a net point `p`, where `f p` and `g p` have a common index
    obtain ⟨p, hp, hxp⟩ := ht (J f) x
    have hrp : r (f p) = r (g p) := List.map_inj_left.1 hl p (Finset.mem_toList.2 hp)
    have h₁ := hJ f x p hxp
    have h₂ := hr (f p)
    have h₃ := hr (g p)
    have h₄ := hJ g x p (hj ▸ hxp)
    rw [hrp] at h₂
    rw [dist_comm] at h₃ h₄
    linarith [dist_triangle4 (f x) (f p) (s (r (g p))) (g x),
      dist_triangle (s (r (g p))) (g p) (g x)]
  -- Step 4: `Φ ω = (ω, dω)|_K`
  let Φ : TestFormOn U n → C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)) := fun ω =>
    ⟨fun x => ((ω : DifferentialForm (Euclid P) n) x,
        exteriorDerivative (ω : DifferentialForm (Euclid P) n) x),
      (ω.property.1.1.continuous.prodMk
        (exteriorDerivative_isTestForm ω.property.1).1.continuous).comp continuous_subtype_val⟩
  let X : Set (TestFormOn U n) := {ω | tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K}
  -- Step 5: a countable `T ⊆ Φ(X)` dense in `Φ(X)`, and a choice `σ` of preimages in `X`
  obtain ⟨T, hTc, hTX, hXT⟩ := TopologicalSpace.exists_countable_dense_subset (Φ '' X)
  have hT : ∀ t ∈ T, ∃ η, η ∈ X ∧ Φ η = t := fun t ht => hTX ht
  choose! σ hσX hσΦ using hT
  -- Step 6: `D = σ(T)` is countable and supported in `K`
  refine ⟨σ '' T, hTc.image σ, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hσX t ht
  -- Step 7: pick `t ∈ T` with `dist (Φ ω) t < ε` and put `η = σ t`
  intro ω hω ε hε
  obtain ⟨t, ht, hdist⟩ := (Metric.mem_closure_iff
    (α := C(K, Covector (Euclid P) n × Covector (Euclid P) (n + 1)))).1 (hXT ⟨ω, hω, rfl⟩) ε hε
  rw [← hσΦ t ht] at hdist
  have key : ∀ x, dist ((ω : DifferentialForm (Euclid P) n) x)
      ((σ t : DifferentialForm (Euclid P) n) x) < ε ∧
      dist (exteriorDerivative (ω : DifferentialForm (Euclid P) n) x)
        (exteriorDerivative (σ t : DifferentialForm (Euclid P) n) x) < ε := by
    intro x
    by_cases hx : x ∈ K
    · -- (a) on `K`: both distances are at most `dist (Φ ω) (Φ η) < ε`
      have h := (ContinuousMap.dist_apply_le_dist (f := Φ ω) (g := Φ (σ t)) ⟨x, hx⟩).trans_lt hdist
      rw [Prod.dist_eq] at h
      exact ⟨(le_max_left _ _).trans_lt h, (le_max_right _ _).trans_lt h⟩
    · -- (b) off `K`: all four values vanish
      obtain ⟨h₁, h₂⟩ := hzero ω hω x hx
      obtain ⟨h₃, h₄⟩ := hzero (σ t) (hσX t ht) x hx
      rw [h₁, h₂, h₃, h₄, dist_self, dist_self]
      exact ⟨hε, hε⟩
  exact ⟨σ t, ⟨t, ht, rfl⟩, fun x => (key x).1, fun x => (key x).2⟩

/-- **A countable family of test forms, dense for `ω` and `dω` with common compact supports**
(Simon Ch. 6, proof of 4.5(2), p. 157: "a countable dense set of `ω ∈ 𝒟ⁿ(U)`").  Take the
compact exhaustion `Kᵢ` of `U` (`dor_lmbs_tfa_compact_exhaustion`) and, for each `i`, a
countable `Dᵢ` approximating every `ω` with `spt ω ⊆ Kᵢ` uniformly together with `dω`
(`dor_lmbs_tfa_fixed_support_dense`); then `D = ⋃ᵢ Dᵢ`.  Given `ω`, `spt ω ⊆ Kᵢ` for some `i`,
and `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω` gives `ωₖ → ω`, `dωₖ → dω` uniformly. -/
theorem Submission.dor_lmbs_testForm_countable_approx : ∀ (P n : ℕ) (U : Set (Euclid P)), IsOpen U → ∃ D : Set (TestFormOn U n), D.Countable ∧ ∀ ω : TestFormOn U n, ∃ (K : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), IsCompact K ∧ K ⊆ U ∧ tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K ∧ (∀ k, ωs k ∈ D) ∧ (∀ k, tsupport (ωs k : DifferentialForm (Euclid P) n) ⊆ K) ∧ TendstoUniformly (fun k x => (ωs k : DifferentialForm (Euclid P) n) x) (ω : DifferentialForm (Euclid P) n) atTop ∧ TendstoUniformly (fun k x => exteriorDerivative (ωs k : DifferentialForm (Euclid P) n) x) (exteriorDerivative (ω : DifferentialForm (Euclid P) n)) atTop := by
  intro P n U hU
  -- step 1: the compact exhaustion `Kᵢ` of `U`
  obtain ⟨K, hKc, hKU, hKex⟩ := Submission.dor_lmbs_tfa_compact_exhaustion P U hU
  -- steps 2–4: a countable `Dᵢ` for the test forms supported in `Kᵢ`
  choose D hDc hDK hDω using fun i =>
    Submission.dor_lmbs_tfa_fixed_support_dense P n U (K i) (hKc i)
  -- step 5: `D = ⋃ᵢ Dᵢ`
  refine ⟨⋃ i, D i, Set.countable_iUnion hDc, fun ω => ?_⟩
  -- step 6: `spt ω` is a compact subset of `U`, so it lies in some `Kᵢ`
  obtain ⟨i, hi⟩ :=
    hKex (tsupport (ω : DifferentialForm (Euclid P) n)) ω.property.1.2 ω.property.2
  -- `ωₖ ∈ Dᵢ` within `1/(k+1)` of `ω` and of `dω`
  choose ωs hωsD hωs using fun k : ℕ =>
    hDω i ω hi (1 / ((k : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε := fun ε hε => by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    exact (Nat.one_div_le_one_div hk).trans_lt hN
  refine ⟨K i, ωs, hKc i, hKU i, hi, fun k => Set.mem_iUnion.2 ⟨i, hωsD k⟩,
    fun k => hDK i (ωs k) (hωsD k), ?_, ?_⟩
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).1 x).trans hk
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hsmall ε hε] with k hk x
    exact ((hωs k).2 x).trans hk
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
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))

/-- **Countable-test criterion** (Lemma CT): convergence on one fixed countable family of test
forms, together with local mass bounds, gives weak convergence in `ℝᴾ`.  The family `ωs`
enumerates the countable set `D` of `dor_lmbs_testForm_countable_approx` for `U = ℝᴾ`.  Given
`ω`, its approximants in `D` are supported in one compact `K ⊆ B = B_{R+1}(0)`; pick `ωs m`
uniformly `η`-close to `ω`.  Then `|ω − ωs m| ≤ C₀η` (`rsd_mw_tfa_norm_props` (iii)), so
`cmr_abs_apply_le_massOn` bounds `|A(ω) − A(ωs m)|` and, for `k ≥ k₀`, `|A_k(ω) − A_k(ωs m)|`
by `C₀ηΓ ≤ ε/4`; the tests `A_k(ωs m) → A(ωs m)` give the remaining `ε/2`. -/
theorem Submission.dimred_tr_ibl_countable_tests : ∀ (P n : ℕ), ∃ ωs : ℕ → TestFormOn (univ : Set (Euclid P)) n, ∀ (Vs : ℕ → Set (Euclid P)) (As : (k : ℕ) → GeometricCurrentOn (Vs k) n) (A : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ R : ℕ, ∃ (k₀ : ℕ) (Γ : ℝ≥0∞), Γ ≠ ∞ ∧ A.massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ ∧ ∀ k, k₀ ≤ k → ball (0 : Euclid P) ((R : ℝ) + 1) ⊆ Vs k ∧ (As k).massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ) → (∀ m, Tendsto (fun k => currentEval (As k) ((ωs m : TestFormOn (univ : Set (Euclid P)) n) : DifferentialForm (Euclid P) n)) atTop (𝓝 (A (ωs m)))) → ConvergesWeakly As A := by
  intro P n
  -- step 1: the countable family `D` for `U = ℝᴾ` is nonempty, so `D = range ωs`
  obtain ⟨D, hDc, hD⟩ := Submission.dor_lmbs_testForm_countable_approx P n univ isOpen_univ
  have hDne : D.Nonempty := by
    obtain ⟨_, ωs₀, -, -, -, hωs₀D, -⟩ := hD 0
    exact ⟨ωs₀ 0, hωs₀D 0⟩
  obtain ⟨ωs, hωs⟩ := hDc.exists_eq_range hDne
  refine ⟨ωs, fun Vs As A hM hT => ?_⟩
  intro ω
  -- step 2: `|α| ≤ C₀ ‖α‖`
  obtain ⟨-, -, ⟨C₀, hC₀, hC₀α⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- step 4: the approximants `ωs'` of `ω` lie in `D` and are supported in a compact `K`;
  -- `K ⊆ B = B_{R+1}(0)`, and the mass hypothesis for this `R` gives `k₀` and `Γ`
  obtain ⟨K, ωs', hK, -, hωK, hωs'D, hωs'K, hunif, -⟩ := hD ω
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Euclid P)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  have hKB : K ⊆ ball (0 : Euclid P) ((R : ℝ) + 1) := fun x hx => by
    rw [mem_ball]
    linarith [mem_closedBall.1 (hr hx)]
  obtain ⟨k₀, Γ, hΓ, hAΓ, hAsΓ⟩ := hM R
  have hG : 0 ≤ Γ.toReal := ENNReal.toReal_nonneg
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- step 9: `η = ε / (4 (C₀ Γ + 1))` has `C₀ η Γ ≤ ε / 4`
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (4 * (C₀ * Γ.toReal + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by
    rw [hη_def]
    positivity
  have hsmall : C₀ * η * Γ.toReal ≤ ε / 4 := by
    rw [hη_def, show C₀ * (ε / (4 * (C₀ * Γ.toReal + 1))) * Γ.toReal =
        C₀ * Γ.toReal * ε / (4 * (C₀ * Γ.toReal + 1)) by ring,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_nonneg hC₀ hG]
  -- step 5: `ωs m` is uniformly `η`-close to `ω`
  obtain ⟨j, hj⟩ := (Metric.tendstoUniformly_iff.1 hunif η hη).exists
  obtain ⟨m, hm⟩ : ωs' j ∈ range ωs := hωs ▸ hωs'D j
  rw [← hm] at hj
  have hmK : tsupport (ωs m : DifferentialForm (Euclid P) n) ⊆ K := hm ▸ hωs'K j
  -- step 6: `β = ω − ωs m` is supported in `B`, and `|β| ≤ C₀ η` pointwise
  have hβB : tsupport ((ω : DifferentialForm (Euclid P) n) - (ωs m : DifferentialForm (Euclid P) n))
      ⊆ ball (0 : Euclid P) ((R : ℝ) + 1) :=
    (tsupport_sub _ _).trans (union_subset (hωK.trans hKB) (hmK.trans hKB))
  have hβη : ∀ x, covectorEuclideanNorm
      (((ω : DifferentialForm (Euclid P) n) - (ωs m : DifferentialForm (Euclid P) n)) x) ≤
        C₀ * η := by
    intro x
    have h := hj x
    rw [dist_eq_norm] at h
    exact (hC₀α _).trans (mul_le_mul_of_nonneg_left h.le hC₀)
  -- steps 7 and 8: if `M_B(T) ≤ Γ` and `a`, `b` are `ω`, `ωs m` as test forms of the domain of
  -- `T`, then `|T(a) − T(b)| = |T(a − b)| ≤ C₀ η M_B(T) ≤ C₀ η Γ ≤ ε / 4`
  have key : ∀ (U' : Set (Euclid P)) (T : GeometricCurrentOn U' n) (a b : TestFormOn U' n),
      (a : DifferentialForm (Euclid P) n) = (ω : DifferentialForm (Euclid P) n) →
      (b : DifferentialForm (Euclid P) n) = (ωs m : DifferentialForm (Euclid P) n) →
      T.massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ → |T a - T b| ≤ ε / 4 := by
    intro U' T a b ha hb hTΓ
    rw [show T a - T b = T (a - b) from (map_sub T.toCurrent a b).symm]
    refine (Submission.cmr_abs_apply_le_massOn P n U' _ T (a - b) (C₀ * η)
      (ne_top_of_le_ne_top hΓ hTΓ) ?_ ?_).trans (le_trans ?_ hsmall)
    · rw [Submodule.coe_sub, ha, hb]
      exact hβB
    · rw [Submodule.coe_sub, ha, hb]
      exact hβη
    · exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hΓ hTΓ) (mul_nonneg hC₀ hη.le)
  have hlim : |A ω - A (ωs m)| ≤ ε / 4 := key univ A ω (ωs m) rfl rfl hAΓ
  -- step 10: the tests `currentEval (As k) (ωs m) → A (ωs m)`
  obtain ⟨k₁, hk₁⟩ := Metric.tendsto_atTop.1 (hT m) (ε / 2) (by positivity)
  refine ⟨max k₀ k₁, fun k hk => ?_⟩
  -- step 8: for `k ≥ k₀`, `ω` and `ωs m` are test forms of `Vs k`
  obtain ⟨hBk, hAkΓ⟩ := hAsΓ k (le_of_max_le_left hk)
  have hωk : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ Vs k :=
    ⟨ω.property.1, hωK.trans (hKB.trans hBk)⟩
  have hmk : IsTestForm (ωs m : DifferentialForm (Euclid P) n) ∧
      tsupport (ωs m : DifferentialForm (Euclid P) n) ⊆ Vs k :=
    ⟨(ωs m).property.1, hmK.trans (hKB.trans hBk)⟩
  have hseq : |currentEval (As k) (ω : DifferentialForm (Euclid P) n) -
      currentEval (As k) (ωs m : DifferentialForm (Euclid P) n)| ≤ ε / 4 := by
    unfold currentEval
    rw [dite_eq_left hωk, dite_eq_left hmk]
    exact key (Vs k) (As k) ⟨(ω : DifferentialForm (Euclid P) n), hωk⟩
      ⟨(ωs m : DifferentialForm (Euclid P) n), hmk⟩ rfl rfl hAkΓ
  -- step 11: `ε / 4 + ε / 2 + ε / 4`
  have h₂ := hk₁ k (le_of_max_le_right hk)
  rw [Real.dist_eq, abs_lt] at h₂ ⊢
  rw [abs_le] at hlim hseq
  constructor <;> linarith [hlim.1, hlim.2, hseq.1, hseq.2, h₂.1, h₂.2]

/-- **Diagonal limit**: if `A_{k,i} ⇀ Z_k` as `i → ∞` for every `k`, `Z_k ⇀ C` in `ℝᴾ`, and on
each ball `B = B_{R+1}(0)` the domains eventually contain `B` with `M_B(A_{k,i}) ≤ Γ(R)`
(`k ≥ k₀(R)`, `i` large) and `M_B(C) ≤ Γ(R)`, then some diagonal `A_{k,φ(k)}` converges weakly
to `C`.  With the countable test family `ωs` of `dimred_tr_ibl_countable_tests`, for each `k` the
finitely many conditions `|A_{k,i}(ωs m) − Z_k(ωs m)| < 1/(k+1)` (`m ≤ k`) and the domain and
mass bounds for the `R ≤ k` with `k₀(R) ≤ k` hold for all large `i`;
`Filter.extraction_forall_of_eventually` gives a strictly increasing `φ` meeting them at
`i = φ(k)`, and `dimred_tr_ibl_countable_tests` applies to `A_{k,φ(k)}` and `C`. -/
theorem Submission.dimred_tr_ibl_diagonal_limit : ∀ (P n : ℕ) (Vs : ℕ → ℕ → Set (Euclid P)) (As : (k i : ℕ) → GeometricCurrentOn (Vs k i) n) (Ws : ℕ → Set (Euclid P)) (Zs : (k : ℕ) → GeometricCurrentOn (Ws k) n) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), (∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n), Tendsto (fun i => currentEval (As k i) (ω : DifferentialForm (Euclid P) n)) atTop (𝓝 (currentEval (Zs k) (ω : DifferentialForm (Euclid P) n)))) → ConvergesWeakly Zs C → (∀ R : ℕ, ∃ (k₀ : ℕ) (Γ : ℝ≥0∞), Γ ≠ ∞ ∧ C.massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ ∧ ∀ k, k₀ ≤ k → ∀ᶠ i in atTop, ball (0 : Euclid P) ((R : ℝ) + 1) ⊆ Vs k i ∧ (As k i).massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ) → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => As k (φ k)) C := by
  intro P n Vs As Ws Zs C hAZ hZC hM
  -- step 1: the countable test family `ωs`
  obtain ⟨ωs, hωs⟩ := Submission.dimred_tr_ibl_countable_tests P n
  -- step 2: `k₀(R)` and `Γ(R)` for every `R`
  choose k₀ Γ hΓ hCΓ hAΓ using hM
  -- steps 3 and 4: for each `k`, the finitely many conditions `Q(k, i)` hold for all large `i`
  have hQ : ∀ k : ℕ, ∀ᶠ i in atTop,
      (∀ m ∈ Iic k, |currentEval (As k i) (ωs m : DifferentialForm (Euclid P) n) -
          currentEval (Zs k) (ωs m : DifferentialForm (Euclid P) n)| < 1 / ((k : ℝ) + 1)) ∧
      ∀ R ∈ Iic k, k₀ R ≤ k → ball (0 : Euclid P) ((R : ℝ) + 1) ⊆ Vs k i ∧
          (As k i).massOn (ball 0 ((R : ℝ) + 1)) ≤ Γ R := by
    intro k
    refine Filter.Eventually.and ?_ ?_
    · -- (a): `A_{k,i}(ωs m) → Z_k(ωs m)` as `i → ∞`, and `1 / (k + 1) > 0`
      refine (Filter.eventually_all_finite (Set.finite_Iic k)).2 fun m _ => ?_
      filter_upwards [Metric.tendsto_nhds.1 (hAZ k (ωs m)) (1 / ((k : ℝ) + 1))
        Nat.one_div_pos_of_nat] with i hi
      rwa [Real.dist_eq] at hi
    · -- (b): from step 2 if `k₀(R) ≤ k`, vacuous otherwise
      refine (Filter.eventually_all_finite (Set.finite_Iic k)).2 fun R _ => ?_
      by_cases hk : k₀ R ≤ k
      · exact (hAΓ R k hk).mono fun i hi _ => hi
      · exact Filter.Eventually.of_forall fun i h => absurd h hk
  -- step 5: the diagonal `φ`, with `Q(k, φ(k))` for every `k`
  obtain ⟨φ, hφ, hφQ⟩ := Filter.extraction_forall_of_eventually hQ
  -- step 8: `dimred_tr_ibl_countable_tests` for `A_{k,φ(k)}` and `C`
  refine ⟨φ, hφ, hωs (fun k => Vs k (φ k)) (fun k => As k (φ k)) C (fun R => ?_) fun m => ?_⟩
  · -- step 6: the mass hypothesis, from clause (b) for `k ≥ max (k₀ R) R`
    exact ⟨max (k₀ R) R, Γ R, hΓ R, hCΓ R, fun k hk =>
      (hφQ k).2 R (Set.mem_Iic.2 (le_of_max_le_right hk)) (le_of_max_le_left hk)⟩
  · -- step 7: clause (a) for `k ≥ m` squeezes `A_{k,φ(k)}(ωs m) − Z_k(ωs m)` to `0`, and
    -- `Z_k(ωs m) → C(ωs m)`
    have hdiff : Tendsto (fun k => currentEval (As k (φ k)) (ωs m : DifferentialForm (Euclid P) n) -
        currentEval (Zs k) (ωs m : DifferentialForm (Euclid P) n)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
      filter_upwards [Filter.eventually_ge_atTop m] with k hk
      rw [Real.norm_eq_abs]
      exact ((hφQ k).1 m (Set.mem_Iic.2 hk)).le
    simpa only [sub_add_cancel, zero_add] using hdiff.add (hZC (ωs m))
/-- **Simon 6.2.14 on varying domains**: mass bounds pass to `ConvergesWeakly`-limits.  If
`Tⱼ ⇀ S` and, for all large `j`, `W ⊆ Uⱼ` and `M_W(Tⱼ) ≤ B`, then `M_W(S) ≤ B`.  An admissible
`ω` for `M_W(S)` has `spt ω ⊆ W ⊆ Uⱼ`, so `currentEval Tⱼ ω = Tⱼ(ω)` with `ω` admissible for
`M_W(Tⱼ)`; hence eventually `ofReal (currentEval Tⱼ ω) ≤ B`, and the limit `ofReal (S(ω))` lies
in the closed set `{t ≤ B}`. -/
theorem Submission.idtp_convergesWeakly_massOn_le : ∀ (P n : ℕ) (Us : ℕ → Set (Euclid P)) (V : Set (Euclid P)) (Ts : (j : ℕ) → GeometricCurrentOn (Us j) n) (S : GeometricCurrentOn V n) (W : Set (Euclid P)) (B : ℝ≥0∞), ConvergesWeakly Ts S → (∀ᶠ j in atTop, W ⊆ Us j ∧ (Ts j).massOn W ≤ B) → S.massOn W ≤ B := by
  intro P n Us V Ts S W B hconv hev
  -- `M_W(S)` is the supremum of `ofReal (S(ω))` over admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  -- `ofReal (currentEval Tⱼ ω) → ofReal (S(ω))`, and `{t ≤ B}` is closed
  refine le_of_tendsto (ENNReal.tendsto_ofReal (hconv ω)) ?_
  -- for large `j`, `spt ω ⊆ W ⊆ Uⱼ`: `ω` is a test form of `Uⱼ`, admissible for `M_W(Tⱼ)`
  filter_upwards [hev] with j hj
  obtain ⟨hWU, hB⟩ := hj
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ Us j :=
    ⟨ω.2.1, hω.1.trans hWU⟩
  have heval : currentEval (Ts j) (ω : DifferentialForm (Euclid P) n) = Ts j ⟨_, h⟩ :=
    dite_eq_left h
  rw [heval]
  exact ((Ts j).le_massOn (W := W) (omega := ⟨_, h⟩) hω).trans hB
/-- **The dilation `η_{x,λ}` maps `B_ρ(x)` onto `B_{ρ/λ}(0)`** (Simon 7.3, `η_{x,λ}(y) = λ⁻¹(y − x)`,
`λ > 0`).  Since `‖η(y)‖ = λ⁻¹‖y − x‖`, `η⁻¹(B_{ρ/λ}(0)) = B_ρ(x)`; and since `η(x + λz) = z`,
`η(B_ρ(x)) = B_{ρ/λ}(0)`.  No sign condition on `ρ` is needed (both sides are empty if `ρ ≤ 0`). -/
theorem Submission.dtc_bc_cz_blowUp_eval_dilation_ball : ∀ (P : ℕ) (x : Euclid P) (ρ lam : ℝ), 0 < lam → dilation x lam ⁻¹' ball 0 (ρ / lam) = ball x ρ ∧ dilation x lam '' ball x ρ = ball 0 (ρ / lam) := by
  intro P x ρ lam hlam
  -- Step 1: `η(y) = −λ⁻¹x + λ⁻¹y = λ⁻¹(y − x)`.
  have h1 : ∀ y, dilation x lam y = lam⁻¹ • (y - x) := by
    intro y
    simp [dilation, dilationCLM, sub_eq_neg_add]
  -- Step 2: `η(y) ∈ B_{ρ/λ}(0) ↔ λ⁻¹‖y − x‖ < ρ/λ ↔ ‖y − x‖ < ρ ↔ y ∈ B_ρ(x)`.
  have hpre : dilation x lam ⁻¹' ball 0 (ρ / lam) = ball x ρ := by
    ext y
    rw [mem_preimage, mem_ball, mem_ball, dist_zero_right, h1, norm_smul, dist_eq_norm,
      Real.norm_eq_abs, abs_inv, abs_of_pos hlam, lt_div_iff₀ hlam, inv_mul_eq_div,
      div_mul_cancel₀ _ hlam.ne']
  refine ⟨hpre, Subset.antisymm ?_ ?_⟩
  · -- Step 3: `η(B_ρ(x)) ⊆ B_{ρ/λ}(0)` by the preimage identity.
    rw [image_subset_iff, hpre]
  · -- Step 4: `z = η(x + λz)` and `x + λz ∈ η⁻¹(B_{ρ/λ}(0)) = B_ρ(x)`.
    intro z hz
    have hz' : dilation x lam (x + lam • z) = z := by
      rw [h1, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
    refine ⟨x + lam • z, ?_, hz'⟩
    rw [← hpre, mem_preimage, hz']
    exact hz
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h
/-- **`currentEval` of the blow-up `η_{x,λ#}T` is `currentEval T ∘ η^#`** (Simon 6.2.23 for the
dilation `η = η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T ⇀ C` in the proof of 7.3.1, chapter-07.txt lines 329–337).  For every `n`-form `ω` on
`ℝᴾ`, `currentEval (η_{x,λ#}T) ω = currentEval T (η^#ω)`.  By multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`.  If `ω ∈ 𝒟ⁿ(η(U))`, then `ω' = ω ∘ η ∈ 𝒟ⁿ(U)` and
`η^#ω = λ⁻ⁿ ω' ∈ 𝒟ⁿ(U)`, so both sides are `λ⁻ⁿ T(ω')` (`Submission.dtc_blowUp_testForm_corr`).
Otherwise `η^#ω ∉ 𝒟ⁿ(U)` and both sides are `0`: if `η^#ω ∈ 𝒟ⁿ(U)`, then `λⁿ η^#ω = ω ∘ η` gives
`ω₁ ∈ 𝒟ⁿ(η(U))` with `ω₁ ∘ η = ω ∘ η`, and `ω₁ = ω` since `η(x + λz) = z`. -/
theorem Submission.dimred_tr_bc_currentEval_blowUp : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) := by
  intro P n U T x lam hlam ω
  have hne : lam ≠ 0 := hlam.ne'
  obtain ⟨hA1, hA2, hA3⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  -- Step 1 (multilinearity): `(η^#ω)(p) = ω(η(p))(λ⁻¹ ·, …, λ⁻¹ ·) = λ⁻ⁿ ω(η(p))`.
  have hpull : ∀ p, affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω p =
      lam⁻¹ ^ n • ω (dilation x lam p) := by
    intro p
    ext v
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  -- Step 2: `η` is surjective, `η(x + λz) = z`.
  have hsurj : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  unfold currentEval
  by_cases h : IsTestForm ω ∧ tsupport ω ⊆ dilation x lam '' U
  · -- Case 1: `ω ∈ 𝒟ⁿ(η(U))`.  With `ω' = ω ∘ η ∈ 𝒟ⁿ(U)` (part (a)), `η^#ω = λ⁻ⁿ ω'`, so
    -- `T(η^#ω) = λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)` (part (c)).
    rw [dite_eq_left h]
    obtain ⟨ω', hω'⟩ := hA1 ⟨ω, h⟩
    have hν : affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω =
        ((lam⁻¹ ^ n • ω' : TestFormOn U n) : DifferentialForm (Euclid P) n) := by
      funext p
      rw [hpull p, Submodule.coe_smul, Pi.smul_apply, hω' p]
    have h' : IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ∧
        tsupport (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ⊆ U := by
      rw [hν]
      exact (lam⁻¹ ^ n • ω').property
    have hν' : (⟨affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω, h'⟩ : TestFormOn U n) =
        lam⁻¹ ^ n • ω' := Subtype.ext hν
    rw [dite_eq_left h', hA3 T ⟨ω, h⟩ ω' hω', hν', map_smul, smul_eq_mul]
  · -- Case 2: `ω ∉ 𝒟ⁿ(η(U))`.  If `η^#ω ∈ 𝒟ⁿ(U)`, then part (b) applied to `λⁿ η^#ω = ω ∘ η`
    -- gives `ω₁ ∈ 𝒟ⁿ(η(U))` with `ω₁ ∘ η = ω ∘ η`, hence `ω₁ = ω` by surjectivity of `η`.
    rw [dite_eq_right h]
    have h' : ¬(IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ∧
        tsupport (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ⊆ U) := by
      intro h'
      obtain ⟨ω₁, hω₁⟩ := hA2 (lam ^ n • (⟨_, h'⟩ : TestFormOn U n))
      have hω₁ω : (ω₁ : DifferentialForm (Euclid P) n) = ω := by
        funext z
        have hz := hω₁ (x + lam • z)
        rw [hsurj z, Submodule.coe_smul, Pi.smul_apply] at hz
        change lam ^ n • affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω (x + lam • z) =
          (ω₁ : DifferentialForm (Euclid P) n) z at hz
        rw [← hz, hpull, hsurj z, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul]
      exact h (hω₁ω ▸ ω₁.property)
    rw [dite_eq_right h']
/-- **Composition of dilation pull-backs** (the pull-back `f^#` of 6.2.23, chapter-06.txt lines
404–409; needed for the closure (10) of `𝒯` under `η_{x,λ#}`, Appendix A.1, in the proof of
7.3.3(1), chapter-07.txt line 472).  For `λ ≠ 0`, `η_{y,μ} ∘ η_{x,λ} = η_{x+λy,λμ}`, since
`μ⁻¹(λ⁻¹(p − x) − y) = (λμ)⁻¹(p − x − λy)`; hence, by contravariance of the affine pull-back,
`η_{x,λ}^#(η_{y,μ}^#ω) = η_{x+λy,λμ}^#ω`. -/
theorem Submission.dimred_tr_bc_dilation_pullback_comp : ∀ (P n : ℕ) (x y : Euclid P) (lam mu : ℝ), lam ≠ 0 → ∀ ω : DifferentialForm (Euclid P) n, affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) (affinePullbackForm (dilationCLM P mu) (-(mu⁻¹ • y)) ω) = affinePullbackForm (dilationCLM P (lam * mu)) (-((lam * mu)⁻¹ • (x + lam • y))) ω := by
  intro P n x y lam mu hlam ω
  -- `dilationCLM P a` is `v ↦ a⁻¹ • v`.
  have hd : ∀ (a : ℝ) (v : Euclid P), dilationCLM P a v = a⁻¹ • v := fun _ _ => rfl
  -- Linear parts: `μ⁻¹(λ⁻¹v) = (λμ)⁻¹v`.
  have hlin : ∀ v : Euclid P,
      dilationCLM P mu (dilationCLM P lam v) = dilationCLM P (lam * mu) v := by
    intro v
    rw [hd, hd, hd, smul_smul, mul_inv, mul_comm mu⁻¹ lam⁻¹]
  -- Base points: `−μ⁻¹y + μ⁻¹(−λ⁻¹x + λ⁻¹p) = −(λμ)⁻¹(x + λy) + (λμ)⁻¹p`, as `(λμ)⁻¹λ = μ⁻¹`.
  have hbase : ∀ p : Euclid P,
      -(mu⁻¹ • y) + dilationCLM P mu (-(lam⁻¹ • x) + dilationCLM P lam p) =
        -((lam * mu)⁻¹ • (x + lam • y)) + dilationCLM P (lam * mu) p := by
    intro p
    have hcoef : (lam * mu)⁻¹ * lam = mu⁻¹ := by
      rw [mul_inv, mul_comm lam⁻¹ mu⁻¹, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
    simp only [hd, smul_add, smul_neg, smul_smul, hcoef]
    rw [mul_inv, mul_comm mu⁻¹ lam⁻¹]
    abel
  -- At `p` and `(v₁, …, vₙ)` both sides are `ω(b + Lp)(Lv₁, …, Lvₙ)` with the same `b + Lp`
  -- and the same `L`.
  funext p
  ext v
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hbase p]
  congr 1
  funext i
  exact hlin (v i)

/-- **Blow-up calculus for `η_{x,λ#}T`, `λ > 0`** (Simon 6.2.23 for the dilation
`η = η_{x,λ}(y) = λ⁻¹(y − x)`, chapter-06.txt lines 403–413; scaling identity (1) in the proof of
7.3.1, chapter-07.txt lines 329–331, and the closure (10) of `𝒯` under `η_{x,λ#}` in the proof of
7.3.3, chapter-07.txt line 472).  (i) `M_W(η_{x,λ#}T) = λ⁻ⁿ M_{η⁻¹(W)}(T)` for every `W ⊆ ℝᴾ`:
`η` is surjective (`η(x + λz) = z`), so `W = η(η⁻¹(W))` and this is the image form
`Submission.dtc_blowUp_massOn_image`.  (ii) `currentEval (η_{x,λ#}T) ω = currentEval T (η^#ω)`
(`Submission.dimred_tr_bc_currentEval_blowUp`).  (iii) Applying (ii) to `η_{y,μ#}` and then to
`η_{x,λ#}`, and composing the pull-backs, `η_{x,λ}^#(η_{y,μ}^#ω) = η_{x+λy,λμ}^#ω`
(`Submission.dimred_tr_bc_dilation_pullback_comp`), gives
`currentEval (η_{y,μ#}η_{x,λ#}T) ω = currentEval (η_{x+λy,λμ#}T) ω`. -/
theorem Submission.dimred_tr_blowup_calculus : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω := by
  intro P n U T x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- `η = η_{x,λ}` is surjective: `η(x + λz) = z`.
  have hsurj : Surjective (dilation x lam) := fun z =>
    ⟨x + lam • z, by simp [dilation, dilationCLM, smul_add, smul_smul, hne]⟩
  refine ⟨fun W => ?_, Submission.dimred_tr_bc_currentEval_blowUp P n U T x lam hlam, ?_⟩
  · -- (i) With `W' = η⁻¹(W)`, `η(W') = W`, so `M_W(η_{x,λ#}T) = M_{η(W')}(η_{x,λ#}T)`
    -- `= λ⁻ⁿ M_{W'}(T)`.
    have h := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W)
    rwa [image_preimage_eq W hsurj] at h
  · -- (iii) `currentEval (η_{y,μ#}η_{x,λ#}T) ω = currentEval (η_{x,λ#}T) (η_{y,μ}^#ω)`
    -- `= currentEval T (η_{x,λ}^#η_{y,μ}^#ω) = currentEval T (η_{x+λy,λμ}^#ω)`
    -- `= currentEval (η_{x+λy,λμ#}T) ω`.
    intro y mu hmu ω
    rw [Submission.dimred_tr_bc_currentEval_blowUp P n _ _ y mu hmu ω,
      Submission.dimred_tr_bc_currentEval_blowUp P n U T x lam hlam,
      Submission.dimred_tr_bc_dilation_pullback_comp P n x y lam mu hne,
      Submission.dimred_tr_bc_currentEval_blowUp P n U T (x + lam • y) (lam * mu)
        (mul_pos hlam hmu) ω]

/-- **Iterated zero-scale blow-up limits are zero-scale blow-up limits** (closure of the class `𝒯`
of limits `lim η_{xᵢ,λᵢ#}T`, `λᵢ → 0`, under `η_{y,s#}` followed by weak limits, in the proof of
Simon 7.3.3, chapter-07.txt lines 450–472, (10); Appendix A.1).  `B_{δ'}(x) ⊆ U`.  By
`Submission.dimred_tr_blowup_calculus` (i) and `η_{a,t}⁻¹(B_ρ(p)) = B_{tρ}(a + tp)`, once
`dist(a + tp, x) + tρ < min(δ, δ')` the blow-up `η_{a,t#}T` has `B_ρ(p)` in its domain and
`M_{B_ρ(p)}(η_{a,t#}T) = t⁻ⁿ M_{B_{tρ}(a+tp)}(T) ≤ Γρⁿ`; this holds eventually along `aᵢ → x`,
`tᵢ → 0`, so `Submission.idtp_convergesWeakly_massOn_le` gives `M_{B_ρ(p)}(S) ≤ Γρⁿ` and then
`M_{B_ρ(0)}(C) ≤ Γρⁿ`.  By (ii) and (iii), `currentEval (η_{xᵢ+λᵢy,λᵢsₖ#}T) ω =
currentEval (η_{xᵢ,λᵢ#}T) (η_{y,sₖ}^#ω) → currentEval S (η_{y,sₖ}^#ω) =
currentEval (η_{y,sₖ#}S) ω` as `i → ∞` (if `η_{y,sₖ}^#ω` is not a test form all terms are `0`),
and `Submission.dimred_tr_ibl_diagonal_limit` selects the diagonal `φ`. -/
theorem Submission.dimred_tr_iterated_blowup_limit : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C := by
  intro P n U T x xs lams hlams S y ss hss C hU hx hxs hlams0 _ hmass hb hc
  obtain ⟨δ, Γ, hδ, hT⟩ := hmass
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.isOpen_iff.1 hU x hx
  -- `η_{a,t}⁻¹(B_ρ(p)) = B_{tρ}(a + tp)`
  have hpre : ∀ (a p : Euclid P) (t ρ : ℝ), 0 < t →
      dilation a t ⁻¹' ball p ρ = ball (a + t • p) (t * ρ) := by
    intro a p t ρ ht
    ext z
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm]
    have hz : dilation a t z - p = t⁻¹ • (z - (a + t • p)) := by
      show -(t⁻¹ • a) + t⁻¹ • z - p = _
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      abel
    rw [hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_lt_iff₀ ht]
  -- `t⁻ⁿ Γ (tρ)ⁿ = Γ ρⁿ`
  have hscale : ∀ t ρ : ℝ, 0 < t → ENNReal.ofReal (t⁻¹ ^ n) * ENNReal.ofReal (Γ * (t * ρ) ^ n) =
      ENNReal.ofReal (Γ * ρ ^ n) := by
    intro t ρ ht
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [mul_pow, inv_pow]
    field_simp
  -- local domain and mass bound for a blow-up of `T` with centre near `x` and small scale
  have hloc : ∀ (a p : Euclid P) (t ρ : ℝ) (ht : 0 < t), 0 < ρ →
      dist (a + t • p) x + t * ρ < min δ δ' →
      ball p ρ ⊆ dilation a t '' U ∧
        (blowUp T a t ht.ne').massOn (ball p ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n) := by
    intro a p t ρ ht hρ hlt
    have htρ : 0 < t * ρ := mul_pos ht hρ
    have hd : 0 ≤ dist (a + t • p) x := dist_nonneg
    have hlt1 : dist (a + t • p) x + t * ρ < δ := hlt.trans_le (min_le_left _ _)
    have hlt2 : dist (a + t • p) x + t * ρ < δ' := hlt.trans_le (min_le_right _ _)
    have hsurj : ∀ z, dilation a t (a + t • z) = z := by
      intro z
      simp [dilation, dilationCLM, smul_add, smul_smul, ht.ne']
    refine ⟨fun z hz => ⟨a + t • z, ?_, hsurj z⟩, ?_⟩
    · apply hδ'U
      apply ball_subset_ball' (by linarith : t * ρ + dist (a + t • p) x ≤ δ')
      rw [← hpre a p t ρ ht, mem_preimage, hsurj z]
      exact hz
    · rw [(Submission.dimred_tr_blowup_calculus P n U T a t ht).1, hpre a p t ρ ht]
      calc ENNReal.ofReal (t⁻¹ ^ n) * T.massOn (ball (a + t • p) (t * ρ))
          ≤ ENNReal.ofReal (t⁻¹ ^ n) * ENNReal.ofReal (Γ * (t * ρ) ^ n) := by
            gcongr
            exact hT _ (mem_ball.2 (by linarith)) _ htρ (by linarith)
        _ = ENNReal.ofReal (Γ * ρ ^ n) := hscale t ρ ht
  -- these conditions hold eventually along centres `aᵢ → x` and scales `tᵢ → 0`
  have hev : ∀ (a : ℕ → Euclid P) (t : ℕ → ℝ), Tendsto a atTop (𝓝 x) →
      Tendsto t atTop (𝓝 0) → ∀ (p : Euclid P) (ρ : ℝ),
        ∀ᶠ i in atTop, dist (a i + t i • p) x + t i * ρ < min δ δ' := by
    intro a t ha ht p ρ
    have h1 : Tendsto (fun i => a i + t i • p) atTop (𝓝 x) := by
      simpa using ha.add (ht.smul_const p)
    have h2 : Tendsto (fun i => dist (a i + t i • p) x + t i * ρ) atTop (𝓝 0) := by
      simpa using (tendsto_iff_dist_tendsto_zero.1 h1).add (ht.mul_const ρ)
    exact h2.eventually (eventually_lt_nhds (lt_min hδ hδ'))
  -- mass bounds for `S`
  have hS : ∀ (p : Euclid P) (ρ : ℝ), 0 < ρ → S.massOn (ball p ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n) := by
    intro p ρ hρ
    refine Submission.idtp_convergesWeakly_massOn_le P n _ _ _ S (ball p ρ) _ hb ?_
    filter_upwards [hev xs lams hxs hlams0 p ρ] with i hi
    exact hloc (xs i) p (lams i) ρ (hlams i) hρ hi
  -- mass bounds for `C`
  have hC : ∀ ρ : ℝ, 0 < ρ → C.massOn (ball 0 ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n) := by
    intro ρ hρ
    refine Submission.idtp_convergesWeakly_massOn_le P n _ _ _ C (ball 0 ρ) _ hc
      (Eventually.of_forall fun k => ⟨fun z _ => ⟨y + ss k • z, mem_univ _, ?_⟩, ?_⟩)
    · simp [dilation, dilationCLM, smul_add, smul_smul, (hss k).ne']
    · rw [(Submission.dimred_tr_blowup_calculus P n univ S y (ss k) (hss k)).1,
        hpre y 0 (ss k) ρ (hss k), smul_zero, add_zero]
      calc ENNReal.ofReal ((ss k)⁻¹ ^ n) * S.massOn (ball y (ss k * ρ))
          ≤ ENNReal.ofReal ((ss k)⁻¹ ^ n) * ENNReal.ofReal (Γ * (ss k * ρ) ^ n) := by
            gcongr
            exact hS y _ (mul_pos (hss k) hρ)
        _ = ENNReal.ofReal (Γ * ρ ^ n) := hscale (ss k) ρ (hss k)
  -- inner convergence for fixed `k`
  have hinner : ∀ (k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n),
      Tendsto (fun i => currentEval (blowUp T (xs i + lams i • y) (lams i * ss k)
        (mul_pos (hlams i) (hss k)).ne') (ω : DifferentialForm (Euclid P) n)) atTop
        (𝓝 (currentEval (blowUp S y (ss k) (hss k).ne') (ω : DifferentialForm (Euclid P) n))) := by
    intro k ω
    set ν := affinePullbackForm (dilationCLM P (ss k)) (-((ss k)⁻¹ • y))
      (ω : DifferentialForm (Euclid P) n) with hν_def
    have h1 : ∀ i, currentEval (blowUp T (xs i + lams i • y) (lams i * ss k)
        (mul_pos (hlams i) (hss k)).ne') (ω : DifferentialForm (Euclid P) n) =
        currentEval (blowUp T (xs i) (lams i) (hlams i).ne') ν := fun i => by
      rw [← (Submission.dimred_tr_blowup_calculus P n U T (xs i) (lams i) (hlams i)).2.2 y (ss k)
          (hss k),
        (Submission.dimred_tr_blowup_calculus P n _ (blowUp T (xs i) (lams i) (hlams i).ne') y
          (ss k) (hss k)).2.1]
    have h2 : currentEval (blowUp S y (ss k) (hss k).ne') (ω : DifferentialForm (Euclid P) n) =
        currentEval S ν :=
      (Submission.dimred_tr_blowup_calculus P n univ S y (ss k) (hss k)).2.1 _
    simp only [h1, h2]
    by_cases hν : IsTestForm ν ∧ tsupport ν ⊆ (univ : Set (Euclid P))
    · have h3 : currentEval S ν = S ⟨ν, hν⟩ := dite_eq_left hν
      rw [h3]
      exact hb ⟨ν, hν⟩
    · have h3 : ∀ {V : Set (Euclid P)} (A : GeometricCurrentOn V n), currentEval A ν = 0 := by
        intro V A
        exact dite_eq_right fun h => hν ⟨h.1, subset_univ _⟩
      simp only [h3]
      exact tendsto_const_nhds
  -- diagonal selection
  refine Submission.dimred_tr_ibl_diagonal_limit P n
    (fun k i => dilation (xs i + lams i • y) (lams i * ss k) '' U)
    (fun k i => blowUp T (xs i + lams i • y) (lams i * ss k) (mul_pos (hlams i) (hss k)).ne')
    (fun k => dilation y (ss k) '' univ) (fun k => blowUp S y (ss k) (hss k).ne') C hinner hc ?_
  intro R
  refine ⟨0, ENNReal.ofReal (Γ * ((R : ℝ) + 1) ^ n), ENNReal.ofReal_ne_top,
    hC _ (by positivity), fun k _ => ?_⟩
  have ha : Tendsto (fun i => xs i + lams i • y) atTop (𝓝 x) := by
    simpa using hxs.add (hlams0.smul_const y)
  have ht : Tendsto (fun i => lams i * ss k) atTop (𝓝 0) := by
    simpa using hlams0.mul_const (ss k)
  filter_upwards [hev _ _ ha ht 0 ((R : ℝ) + 1)] with i hi
  exact hloc _ 0 _ _ (mul_pos (hlams i) (hss k)) (by positivity) hi

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
