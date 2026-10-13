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

/-- A small scale below the lower density (Simon Ch. 6, 8.2 (2), with the lower density in place of
`Θ^{*n}`): `ωₙ > 0`, and if `liminf_{r ↓ 0} μ(B_r(x₁)) / (ωₙ rⁿ) < η₀`, then for every `δ > 0` there
is `s ∈ (0, δ)` with `μ(B_s(x₁)) < η₀ ωₙ sⁿ`.  The ratio is frequently below `η₀` along `r ↓ 0`;
clearing the nonzero, finite denominator `ωₙ sⁿ` at such an `s ∈ (0, δ)` gives the bound, and forces
`η₀ ≥ 0`. -/
theorem Submission.cbrldlf_exists_small_scale_of_lower_density : ∀ n : ℕ, 0 < (unitBallVolume n).toReal ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (η₀ δ : ℝ), 0 < δ → liminf (fun r : ℝ => μ (ball x₁ r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))) (𝓝[>] 0) < ENNReal.ofReal η₀ → ∃ s : ℝ, 0 < s ∧ s < δ ∧ μ (ball x₁ s) < ENNReal.ofReal (η₀ * (unitBallVolume n).toReal * s ^ n) := by
  intro n
  -- `ωₙ = volume (ball 0 1)` is positive (Haar measure on a nonempty open set) and finite.
  have hω₀ : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωt : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  refine ⟨ENNReal.toReal_pos hω₀ hωt, fun P μ x₁ η₀ δ hδ hlim => ?_⟩
  -- The ratio is frequently below `η₀`, and eventually `r ∈ (0, δ)`.
  obtain ⟨s, hs, hs₀, hsδ⟩ := ((frequently_lt_of_liminf_lt (by isBoundedDefault) hlim).and_eventually
    (Ioo_mem_nhdsGT hδ)).exists
  refine ⟨s, hs₀, hsδ, ?_⟩
  -- Clear the denominator `ωₙ sⁿ`, which is nonzero and finite.
  rw [ENNReal.div_lt_iff (Or.inl (mul_ne_zero hω₀ (ENNReal.ofReal_pos.2 (pow_pos hs₀ n)).ne'))
    (Or.inl (ENNReal.mul_ne_top hωt ENNReal.ofReal_ne_top))] at hs
  -- `η₀ ≥ 0`, since otherwise the bound would be `μ (ball x₁ s) < 0`.
  have hη₀ : 0 ≤ η₀ := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_le.1 h).le, zero_mul] at hs
    exact ENNReal.not_lt_zero hs
  rwa [ENNReal.ofReal_mul (mul_nonneg hη₀ ENNReal.toReal_nonneg), ENNReal.ofReal_mul hη₀,
    ENNReal.ofReal_toReal hωt, mul_assoc]
/-- **Simon Ch. 6, 8.2 (3)–(4)** (constants of the isoperimetric filling, corrected), with
`p = m + 1` and `n = m + 2`: for `c ≥ 1` there is `a > 0` such that `0 ≤ F ≤ (a s)ⁿ` and
`0 ≤ M ≤ 2 n a F^{(n-1)/n}` imply `c (2cM)^{1/p} M ≤ F / 2` and `(2cM)^{1/p} ≤ s`.  Take
`K₀ = c (2c)^{1/p} (2n)^{n/p}`, `t = min {1 / (2K₀)^{m+1}, 1 / (4cn)}` and `a = t^{1/n}`, so
`a^{m+2} = t`. -/
theorem Submission.cbrldlf_exists_filling_constant : ∀ (m : ℕ) (c : ℝ), 1 ≤ c → ∃ a : ℝ, 0 < a ∧ ∀ (s F M : ℝ), 0 ≤ s → 0 ≤ F → F ≤ (a * s) ^ (m + 1 + 1) → 0 ≤ M → M ≤ 2 * ((m + 1 + 1 : ℕ) : ℝ) * a * F ^ ((((m + 1 + 1 : ℕ) : ℝ) - 1) / ((m + 1 + 1 : ℕ) : ℝ)) → c * (2 * c * M) ^ ((1 : ℝ) / (m + 1)) * M ≤ F / 2 ∧ (2 * c * M) ^ ((1 : ℝ) / (m + 1)) ≤ s := by
  intro m c hc
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  -- `p = m + 1` and `n = m + 2 = p + 1`
  have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hn_eq : ((m + 1 + 1 : ℕ) : ℝ) = ((m : ℝ) + 1) + 1 := by push_cast; ring
  have hn : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by rw [hn_eq]; linarith
  have hpinv : (1 : ℝ) / ((m : ℝ) + 1) = (((m + 1 : ℕ) : ℝ))⁻¹ := by push_cast; rw [one_div]
  set p : ℝ := (m : ℝ) + 1 with hp_def
  set n : ℝ := ((m + 1 + 1 : ℕ) : ℝ) with hn_def
  -- Step 1: the constants `K₀ > 0`, `t > 0` and `a = t^{1/n} > 0`, with `a^{m+2} = t`
  set K₀ : ℝ := c * (2 * c) ^ (1 / p) * (2 * n) ^ (n / p) with hK₀_def
  have hK₀ : 0 < K₀ :=
    mul_pos (mul_pos hc0 (Real.rpow_pos_of_pos (by positivity) _))
      (Real.rpow_pos_of_pos (by positivity) _)
  set t : ℝ := min (1 / (2 * K₀) ^ (m + 1)) (1 / (4 * c * n)) with ht_def
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  set a : ℝ := t ^ (1 / n) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos ht _
  have ha_pow : a ^ (m + 1 + 1) = t := by
    rw [ha_def, hn_def, one_div]
    exact Real.rpow_inv_natCast_pow ht.le (by omega)
  -- Step 2 (i): `t^{1/p} ≤ ((1/(2K₀))^{m+1})^{1/(m+1)} = 1/(2K₀)`
  have hi : t ^ (1 / p) ≤ 1 / (2 * K₀) := by
    have h1 : t ≤ (1 / (2 * K₀)) ^ (m + 1) := by
      rw [one_div_pow]; exact min_le_left _ _
    have h2 : t ^ (1 / p) ≤ ((1 / (2 * K₀)) ^ (m + 1)) ^ (1 / p) :=
      Real.rpow_le_rpow ht.le h1 (by positivity)
    have h3 : ((1 / (2 * K₀)) ^ (m + 1)) ^ (1 / p) = 1 / (2 * K₀) := by
      rw [hpinv]
      exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    rw [h3] at h2
    exact h2
  -- Step 2 (ii): `t ≤ 1/(4cn)`
  have hii : t ≤ 1 / (4 * c * n) := min_le_right _ _
  refine ⟨a, ha, ?_⟩
  -- Step 3: `M ≤ b := 2 n a F^{p/n}`, since `(n - 1)/n = p/n`
  intro s F M hs hF hFas hM hMb
  have hexp : (n - 1) / n = p / n := by rw [hn_eq]; ring
  rw [hexp] at hMb
  set b : ℝ := 2 * n * a * F ^ (p / n) with hb_def
  have hb : 0 ≤ b := by positivity
  constructor
  · -- Step 4: `c (2cM)^{1/p} M = c (2c)^{1/p} M^{n/p}`, as `n/p = 1/p + 1`
    have h4 : c * (2 * c * M) ^ (1 / p) * M = c * (2 * c) ^ (1 / p) * M ^ (n / p) := by
      rw [Real.mul_rpow (by positivity) hM]
      have e : n / p = 1 / p + 1 := by rw [hn_eq]; field_simp; ring
      rw [e, Real.rpow_add' hM (by positivity), Real.rpow_one]
      ring
    -- Step 5: `M^{n/p} ≤ b^{n/p}`
    have h5 : M ^ (n / p) ≤ b ^ (n / p) := Real.rpow_le_rpow hM hMb (by positivity)
    -- Step 6: `b^{n/p} = (2n)^{n/p} t^{1/p} F`
    have h6 : b ^ (n / p) = (2 * n) ^ (n / p) * t ^ (1 / p) * F := by
      rw [hb_def, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_mul hF, ha_def, ← Real.rpow_mul ht.le]
      have e1 : p / n * (n / p) = 1 := by field_simp
      have e2 : 1 / n * (n / p) = 1 / p := by field_simp
      rw [e1, e2, Real.rpow_one]
    -- Step 7: `c (2cM)^{1/p} M ≤ K₀ t^{1/p} F ≤ F / 2` by (i)
    calc c * (2 * c * M) ^ (1 / p) * M = c * (2 * c) ^ (1 / p) * M ^ (n / p) := h4
      _ ≤ c * (2 * c) ^ (1 / p) * b ^ (n / p) := by gcongr
      _ = K₀ * t ^ (1 / p) * F := by rw [h6, hK₀_def]; ring
      _ ≤ K₀ * (1 / (2 * K₀)) * F := by gcongr
      _ = F / 2 := by field_simp
  · -- Step 8: `F^{p/n} ≤ ((a s)^{m+2})^{p/n} = (a s)^{m+1}`
    have h8 : F ^ (p / n) ≤ (a * s) ^ (m + 1) := by
      have h := Real.rpow_le_rpow hF hFas (by positivity : (0 : ℝ) ≤ p / n)
      have e : ((a * s) ^ (m + 1 + 1)) ^ (p / n) = (a * s) ^ (m + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have e' : ((m + 1 + 1 : ℕ) : ℝ) * (p / n) = ((m + 1 : ℕ) : ℝ) := by
          rw [← hn_def]; field_simp; rw [hp_def]; push_cast; ring
        rw [e', Real.rpow_natCast]
      rw [e] at h
      exact h
    -- Step 9: `2cM ≤ 4cn a^{m+2} s^{m+1} = 4cn t s^{m+1} ≤ s^{m+1}` by (ii)
    have h9 : 2 * c * M ≤ s ^ (m + 1) := by
      calc 2 * c * M ≤ 2 * c * (2 * n * a * F ^ (p / n)) := by gcongr
        _ ≤ 2 * c * (2 * n * a * (a * s) ^ (m + 1)) := by gcongr
        _ = 4 * c * n * a ^ (m + 1 + 1) * s ^ (m + 1) := by ring
        _ = 4 * c * n * t * s ^ (m + 1) := by rw [ha_pow]
        _ ≤ 4 * c * n * (1 / (4 * c * n)) * s ^ (m + 1) := by gcongr
        _ = s ^ (m + 1) := by field_simp
    -- Step 10: `(2cM)^{1/p} ≤ (s^{m+1})^{1/(m+1)} = s`
    have h10 := Real.rpow_le_rpow (by positivity) h9 (by positivity : (0 : ℝ) ≤ 1 / p)
    have e : (s ^ (m + 1)) ^ (1 / p) = s := by
      rw [hpinv]; exact Real.pow_rpow_inv_natCast hs (by omega)
    rw [e] at h10
    exact h10
/-- **Simon Ch. 6, proof of 8.2, (1)–(2)** (slices 4.6–4.9 by `f = |· − x₁|`, `Lip f = 1`): for a
cycle `C`, represent `∂C = 0` by the zero measure.  (SL) gives `A_ρ = C⌞B_ρ(x₁)` and `B_ρ = 0`,
`∂A_ρ` vanishes off `∂B_ρ(x₁)` (4.8) and `M(∂A_ρ) ≤ liminf_{h↓0} h⁻¹μ{ρ − h < |x − x₁| < ρ}` (4.9);
(ISP) makes `∂A_ρ` integer multiplicity for `ρ` outside a Lebesgue-null set. -/
theorem Submission.cbrld_sphere_slice_isIntegerMultiplicity : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P d : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (x₁ : Euclid P), C.boundary = 0 → (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (d + 1)) (ξ' : Euclid P → MultiVector P d), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (d + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) d, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), C ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, (C).boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → ∀ (f : Euclid P → ℝ) (L : NNReal), LipschitzWith L f → ∀ᵐ t ∂(volume : Measure ℝ), ∀ (A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1)) (B : GeometricCurrentOn (univ : Set (Euclid P)) d), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) → (∀ η : TestFormOn (univ : Set (Euclid P)) d, B η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) d) x) ∂μ') → IsIntegerMultiplicity (A.boundary - B)) → ∃ N : Set ℝ, volume N = 0 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ∉ N → ∃ A : GeometricCurrentOn (univ : Set (Euclid P)) (d + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (d + 1), A ω = ∫ x in ball x₁ ρ, ξ x ((ω : DifferentialForm (Euclid P) (d + 1)) x) ∂μ) ∧ IsIntegerMultiplicity A.boundary ∧ A.boundary.support ⊆ sphere x₁ ρ ∧ A.boundary.mass ≤ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) := by
  intro hSL P d C μ ξ x₁ hCb hμ hξm hξb hC hISP
  -- step 1: `∂C = 0` is represented by the zero measure and the zero field of `d`-vectors
  have hμ0 : ∀ K : Set (Euclid P), IsCompact K → (0 : Measure (Euclid P)) K < ∞ :=
    fun K _ => by simp
  have hξ0m : AEStronglyMeasurable (0 : Euclid P → MultiVector P d) (0 : Measure (Euclid P)) :=
    aestronglyMeasurable_zero_measure _
  have hξ0b : ∀ᵐ x ∂(0 : Measure (Euclid P)), ∀ α : Covector (Euclid P) d,
      |(0 : Euclid P → MultiVector P d) x α| ≤ covectorEuclideanNorm α := by
    simp [ae_zero]
  have hCb0 : ∀ η : TestFormOn (univ : Set (Euclid P)) d,
      C.boundary η = ∫ x, (0 : Euclid P → MultiVector P d) x
        ((η : DifferentialForm (Euclid P) d) x) ∂(0 : Measure (Euclid P)) := by
    intro η
    rw [hCb, integral_zero_measure]
    rfl
  -- the slicing function `f = |· − x₁|` is `1`-Lipschitz
  have hf : LipschitzWith 1 (fun x : Euclid P => dist x x₁) := LipschitzWith.dist_left x₁
  -- step 3: (SL) for `C`, `f` and `L = 1`
  obtain ⟨A, B, hA, hB, hAB, hmass, -⟩ := hSL P d univ C μ 0 ξ 0 (fun x => dist x x₁) 1
    isOpen_univ (fun K hK _ => hμ K hK) (fun K hK _ => hμ0 K hK) hξm hξ0m hξb hξ0b hC hCb0 hf
  -- step 2: the exceptional set of (ISP) is Lebesgue-null
  have hISP' := hISP μ 0 ξ 0 hμ hμ0 hξm hξ0m hξb hξ0b hC hCb0 (fun x => dist x x₁) 1 hf
  refine ⟨_, ae_iff.mp hISP', fun ρ _ hρN => ?_⟩
  simp only [Set.mem_ofPred_eq, not_not] at hρN
  -- step 4: `B_ρ = 0`, so `∂A_ρ − B_ρ = ∂A_ρ`
  have hB0 : ∀ η, B ρ η = 0 := by
    intro η
    rw [hB ρ η, Measure.restrict_zero, integral_zero_measure]
  have hsub : (A ρ).boundary - B ρ = (A ρ).boundary := by
    ext η
    show (A ρ).boundary η - B ρ η = (A ρ).boundary η
    rw [hB0, sub_zero]
  refine ⟨A ρ, fun ω => hA ρ ω, ?_, ?_, ?_⟩
  · -- step 5: integer multiplicity
    rw [← hsub]
    exact hρN (A ρ) (B ρ) (hA ρ) (hB ρ)
  · -- step 6: `∂A_ρ` vanishes on a ball around every point off `∂B_ρ(x₁)`
    intro y hy
    by_contra hy'
    rw [Metric.mem_sphere] at hy'
    have hr : 0 < |dist y x₁ - ρ| / 2 := half_pos (abs_pos.mpr (sub_ne_zero.mpr hy'))
    apply hy.2
    refine Set.mem_sUnion_of_mem (mem_ball_self hr) ⟨isOpen_ball, ?_, subset_univ _, ?_⟩
    · exact (isCompact_closedBall y _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · intro η hη
      rw [hAB ρ η ?_, hB0]
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      have h1 : dist z y < |dist y x₁ - ρ| / 2 := hη hz
      have h2 : dist z x₁ = ρ := hz'
      have h3 := abs_dist_sub_le z y x₁
      rw [h2, abs_sub_comm] at h3
      linarith
  · -- step 7: the mass bound with `W = ℝᴾ`
    have h := hmass univ ρ isOpen_univ
    rw [hsub] at h
    simp only [ENNReal.coe_one, one_mul, univ_inter] at h
    exact h
/-- **Good radius** (Simon 7.2.4, choice of the slicing level; the factor-2 averaging of Ch. 2,
6.7(1)).  If `ρ < ρ'`, `μ(B̄_{ρ'}(y)) < ∞`, `∫ g dL¹ ≤ I` and `p` holds `L¹`-a.e., then some
`t ∈ (ρ, ρ')` has `p t`, `μ(∂B_t(y)) = 0` and `g t ≤ (2 / (ρ' - ρ)) I`: the levels failing `p` and
the (countably many) levels whose sphere charges the finite measure `μ⌞B̄_{ρ'}(y)` are `L¹`-null,
and by Markov's inequality the levels with `g t > (2 / (ρ' - ρ)) I` have `L¹`-measure at most
`(ρ' - ρ) / 2 < L¹((ρ, ρ'))`. -/
theorem Submission.dor_lmb_glc_good_radius : ∀ (P : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (ρ ρ' : ℝ) (g : ℝ → ℝ≥0∞) (I : ℝ≥0∞) (p : ℝ → Prop), ρ < ρ' → μ (closedBall y ρ') ≠ ∞ → AEMeasurable g → ∫⁻ t, g t ≤ I → (∀ᵐ t, p t) → ∃ t : ℝ, ρ < t ∧ t < ρ' ∧ p t ∧ μ (sphere y t) = 0 ∧ g t ≤ ENNReal.ofReal (2 / (ρ' - ρ)) * I := by
  intro P μ y ρ ρ' g I p hρ hμ hg hI hp
  have hδ : 0 < ρ' - ρ := sub_pos.mpr hρ
  set c := ENNReal.ofReal (2 / (ρ' - ρ)) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, Ne, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hcinv : c⁻¹ = ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rw [hc_def, ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div]
  -- `N₁`: the exceptional set of `p` is Lebesgue-null
  have hN₁ : volume {t : ℝ | ¬ p t} = 0 := ae_iff.mp hp
  -- `N₂`: only countably many spheres charge the finite measure `μ⌞B̄_{ρ'}(y)`
  have hfin : IsFiniteMeasure (μ.restrict (closedBall y ρ')) := isFiniteMeasure_restrict.mpr hμ
  have hcount : {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun s => isClosed_sphere.measurableSet)
      (fun s s' hss' => Set.disjoint_left.mpr fun x hx hx' =>
        hss' ((mem_sphere.mp hx).symm.trans (mem_sphere.mp hx')))
  have hN₂ : volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} = 0 :=
    hcount.measure_zero volume
  -- `N₃`: Markov's inequality gives `L¹(N₃) ≤ (ρ' - ρ) / 2`
  have hN₃ : volume {t : ℝ | c * I < g t} ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
    rcases eq_or_ne I 0 with h0 | h0
    · have hzero : ∫⁻ t, g t = 0 := le_antisymm (hI.trans h0.le) zero_le
      have hae : g =ᵐ[volume] 0 := (lintegral_eq_zero_iff' hg).mp hzero
      have hnull : volume {t : ℝ | c * I < g t} = 0 := by
        refine measure_mono_null (fun t ht => ?_) (ae_iff.mp hae)
        simp only [Set.mem_ofPred_eq, h0, mul_zero] at ht ⊢
        exact ht.ne'
      rw [hnull]
      exact zero_le
    rcases eq_or_ne I ∞ with htop | htop
    · have hempty : {t : ℝ | c * I < g t} = ∅ := by
        ext t
        simp [htop, ENNReal.mul_top hc0]
      rw [hempty, measure_empty]
      exact zero_le
    have hε0 : c * I ≠ 0 := mul_ne_zero hc0 h0
    have hεtop : c * I ≠ ∞ := ENNReal.mul_ne_top hctop htop
    calc volume {t : ℝ | c * I < g t} ≤ volume {t : ℝ | c * I ≤ g t} :=
          measure_mono fun t (ht : c * I < g t) => show c * I ≤ g t from ht.le
      _ ≤ (∫⁻ t, g t) / (c * I) := meas_ge_le_lintegral_div hg hε0 hεtop
      _ ≤ I / (c * I) := ENNReal.div_le_div_right hI _
      _ = c⁻¹ := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), mul_assoc,
          ENNReal.inv_mul_cancel h0 htop, mul_one]
      _ = ENNReal.ofReal ((ρ' - ρ) / 2) := hcinv
  -- covering: if no good `t` existed, then `(ρ, ρ') ⊆ N₁ ∪ N₂ ∪ N₃`
  by_contra hcon
  have hcover : Ioo ρ ρ' ⊆ {t : ℝ | ¬ p t} ∪
      {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪ {t : ℝ | c * I < g t} := by
    intro t ht
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt, nonpos_iff_eq_zero]
      at hnot
    obtain ⟨⟨hpt, hνt⟩, hgt⟩ := hnot
    have hμt : μ (sphere y t) = 0 := by
      rwa [Measure.restrict_apply isClosed_sphere.measurableSet, Set.inter_eq_left.mpr
        (sphere_subset_closedBall.trans (closedBall_subset_closedBall ht.2.le))] at hνt
    exact hcon ⟨t, ht.1, ht.2, hpt, hμt, hgt⟩
  have hle : ENNReal.ofReal (ρ' - ρ) ≤ ENNReal.ofReal ((ρ' - ρ) / 2) :=
    calc ENNReal.ofReal (ρ' - ρ) = volume (Ioo ρ ρ') := Real.volume_Ioo.symm
      _ ≤ volume ({t : ℝ | ¬ p t} ∪ {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} ∪
          {t : ℝ | c * I < g t}) := measure_mono hcover
      _ ≤ volume {t : ℝ | ¬ p t} + volume {s : ℝ | 0 < μ.restrict (closedBall y ρ') (sphere y s)} +
          volume {t : ℝ | c * I < g t} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ ENNReal.ofReal ((ρ' - ρ) / 2) := by
        rw [hN₁, hN₂, zero_add, zero_add]
        exact hN₃
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  linarith
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)
/-- **Inner-annulus quotients and the derivative of `r ↦ μ(B_r(x₁))`** (Simon Ch. 6: the
quotients `h⁻¹ M(T⌞{t − h < |x − ξ| < t})` of 4.9 are bounded by the derivative of
`r ↦ M(T⌞B_r(ξ))`, as used in the proof of 8.2, (2)).  If `μ(B_ρ(x₁)) < ∞` and
`F(r) = μ(B_r(x₁))` has derivative `d` at `ρ`, then
`liminf_{h ↓ 0} h⁻¹ μ{ρ − h < |x − x₁| < ρ} ≤ d`: for `h > 0` the annulus lies in
`B_ρ(x₁) \ B_{ρ−h}(x₁)`, of measure `F(ρ) − F(ρ − h)`, and the backward difference quotients
`h⁻¹ (F(ρ) − F(ρ − h))` tend to `d`. -/
theorem Submission.cbrld_radius_liminf_annulus_le_of_hasDerivAt : ∀ (P : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (ρ d : ℝ), μ (ball x₁ ρ) ≠ ∞ → HasDerivAt (fun r : ℝ => (μ (ball x₁ r)).toReal) d ρ → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal d := by
  intro P μ x₁ ρ d hμ hd
  -- the backward difference quotients `h⁻¹ (F(ρ) − F(ρ − h))` tend to `d` as `h ↓ 0`
  have hq : Tendsto (fun h : ℝ => h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal))
      (𝓝[>] 0) (𝓝 d) := by
    have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
    refine (hd.tendsto_slope_zero_left.comp hneg).congr' (Eventually.of_forall fun h => ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [inv_neg, ← sub_eq_add_neg]
    ring
  have hlim : liminf (fun h : ℝ => ENNReal.ofReal
      (h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal))) (𝓝[>] 0) =
      ENNReal.ofReal d :=
    ((ENNReal.continuous_ofReal.tendsto d).comp hq).liminf_eq
  refine (liminf_le_liminf ?_).trans_eq hlim
  -- for `h > 0`, the annulus lies in `B_ρ(x₁) \ B_{ρ−h}(x₁)`, of measure `F(ρ) − F(ρ − h)`
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  have hsub : ball x₁ (ρ - h) ⊆ ball x₁ ρ := ball_subset_ball (by linarith)
  have hfin : μ (ball x₁ (ρ - h)) ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono hsub)
  have hA : {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ} ⊆ ball x₁ ρ \ ball x₁ (ρ - h) :=
    fun x hx => ⟨mem_ball.mpr hx.2, fun hx' => lt_asymm hx.1 (mem_ball.mp hx')⟩
  calc ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}
      ≤ ENNReal.ofReal h⁻¹ * μ (ball x₁ ρ \ ball x₁ (ρ - h)) := by gcongr
    _ = ENNReal.ofReal h⁻¹ * ENNReal.ofReal
          ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal) := by
        rw [measure_sdiff hsub measurableSet_ball.nullMeasurableSet hfin,
          ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hμ,
          ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (h⁻¹ * ((μ (ball x₁ ρ)).toReal - (μ (ball x₁ (ρ - h))).toReal)) :=
        (ENNReal.ofReal_mul (inv_nonneg.mpr hh.le)).symm
/-- **Simon Ch. 6, 6.1 (Isoperimetric Theorem)**, from the scaled deformation theorem 5.3 in the
frozen form (DT), with constant `c ≥ 1` for `(P, m)`.  Let `Z ∈ 𝒟_{m+1}(ℝᴾ)` be integer
multiplicity with `spt Z` compact, `∂Z = 0` and `z = M(Z) < ∞`.  Apply (DT) to `T = Z` with
`K = spt Z`, `Λ = z` and `ρ = (2cz)^{1/(m+1)}` (`ρ = 1` if `z = 0`).  A current of zero mass is
zero (test `±sω` with `s‖ω‖_∞ ≤ 1`), so `M(S) ≤ cρ M(∂Z) = 0` gives `S = 0`, and
`M(Q) ≤ cz < ρ^{m+1}` excludes the second alternative, so `Q = 0` and `Z = ∂R`.  Then `Y = R` has
the mass and support bounds of (DT); if `z = 0`, also `M(R) = 0`, so `spt R = ∅`. -/
theorem Submission.cbr_isoperimetric_filling : (∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (ρ : ℝ) (K : Set (Euclid P)) (Λ : NNReal), 0 < ρ → IsCompact K → ∃ 𝒬 : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬.Finite ∧ ∀ T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity T → T.support ⊆ K → T.mass ≤ Λ → T.boundary.mass < ∞ → ∃ Q ∈ 𝒬, ∃ (R : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2)) (S : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsIntegerMultiplicity Q ∧ IsIntegerMultiplicity Q.boundary ∧ IsIntegerMultiplicity R ∧ T - Q - S = R.boundary ∧ (Q = 0 ∨ ENNReal.ofReal (ρ ^ (m + 1)) ≤ Q.mass) ∧ Q.mass ≤ c * T.mass ∧ Q.boundary.mass ≤ c * T.boundary.mass ∧ R.mass ≤ c * ENNReal.ofReal ρ * T.mass ∧ S.mass ≤ c * ENNReal.ofReal ρ * T.boundary.mass ∧ Q.support ∪ R.support ⊆ thickening (3 * Real.sqrt P * ρ) T.support ∧ Q.boundary.support ∪ S.support ⊆ thickening (3 * Real.sqrt P * ρ) T.boundary.support) → ∀ (P m : ℕ), ∃ c : ℝ, 1 ≤ c ∧ ∀ Z : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Z → IsCompact Z.support → Z.boundary = 0 → Z.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid P)) (m + 2), IsIntegerMultiplicity Y ∧ Y.boundary = Z ∧ Y.mass ≤ ENNReal.ofReal (c * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1)) * Z.mass.toReal) ∧ Y.support ⊆ thickening (3 * Real.sqrt P * (2 * c * Z.mass.toReal) ^ ((1 : ℝ) / (m + 1))) Z.support := by
  intro hDT P m
  obtain ⟨c, hc1, hDT⟩ := hDT P m
  refine ⟨(c : ℝ), by exact_mod_cast hc1, ?_⟩
  intro Z hZ hZc hZb hZm
  -- `M(0) = 0` and `spt 0 = ∅`
  have hmass0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).mass = 0 := by
    intro k
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    simp
  have hsupp0 : ∀ k : ℕ, (0 : GeometricCurrentOn (univ : Set (Euclid P)) k).support = ∅ := by
    intro k
    refine eq_empty_of_forall_notMem fun x hx => hx.2 ?_
    exact ⟨ball x 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _,
      fun ω _ => rfl⟩, mem_ball_self one_pos⟩
  -- the Euclidean coefficient norm is absolutely homogeneous
  have hhom : ∀ (k : ℕ) (t : ℝ) (α : Covector (Euclid P) k),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro k t α
    simp only [covectorEuclideanNorm]
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg t), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- a current of zero mass is zero: test `±sω` with `s‖ω‖_∞ ≤ 1`
  have hzero : ∀ (k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass = 0 →
      X = 0 := by
    intro k X hX
    ext ω
    have hω : Continuous (ω : DifferentialForm (Euclid P) k) := ω.property.1.1.continuous
    have hfc : Continuous (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) := by
      simp only [Function.comp_def, covectorEuclideanNorm]
      refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
      exact continuous_if_const _ (fun _ => ((continuous_eval_const _).comp hω).pow 2)
        fun _ => continuous_const
    have hcs : HasCompactSupport (covectorEuclideanNorm ∘ (ω : DifferentialForm (Euclid P) k)) :=
      ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k)
    obtain ⟨C, hC⟩ := hfc.bounded_above_of_compact_support hcs
    obtain ⟨s, hs, hsC⟩ : ∃ s : ℝ, 0 < s ∧ s * (|C| + 1) = 1 :=
      ⟨(|C| + 1)⁻¹, by positivity, inv_mul_cancel₀ (by positivity)⟩
    have hadm : ∀ t : ℝ, |t| ≤ s → t • ω ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      intro t ht
      refine ⟨subset_univ _, fun x => ?_⟩
      show covectorEuclideanNorm (t • (ω : DifferentialForm (Euclid P) k) x) ≤ 1
      rw [hhom]
      have h0 := covectorEuclideanNorm_nonneg ((ω : DifferentialForm (Euclid P) k) x)
      have h1 : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ |C| + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg h0] at this
        linarith [le_abs_self C]
      calc |t| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x)
          ≤ s * (|C| + 1) := mul_le_mul ht h1 h0 hs.le
        _ = 1 := hsC
    have hX' : X.massOn univ = 0 := hX
    have h1 := X.le_massOn (hadm s (abs_of_pos hs).le)
    have h2 := X.le_massOn (hadm (-s) (by rw [abs_neg, abs_of_pos hs]))
    rw [hX', nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1 h2
    have e1 : X (s • ω) = s * X ω := map_smul X.toCurrent s ω
    have e2 : X ((-s) • ω) = -(s * X ω) := by
      rw [show X ((-s) • ω) = -s * X ω from map_smul X.toCurrent (-s) ω]
      ring
    rw [e1] at h1
    rw [e2] at h2
    have h3 : s * X ω = 0 := by linarith
    rw [GeometricCurrentOn.zero_apply]
    exact (mul_eq_zero.1 h3).resolve_left hs.ne'
  -- the scale `ρ`
  set z : ℝ := Z.mass.toReal
  have hz0 : 0 ≤ z := ENNReal.toReal_nonneg
  have hZmz : Z.mass = ENNReal.ofReal z := (ENNReal.ofReal_toReal hZm.ne).symm
  have hc0 : (0 : ℝ) ≤ c := c.coe_nonneg
  have hc0' : (0 : ℝ) < c := by exact_mod_cast zero_lt_one.trans_le hc1
  have hcz0 : 0 ≤ (c : ℝ) * z := mul_nonneg hc0 hz0
  obtain ⟨ρ, hρ0, hρlt, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ (c : ℝ) * z < ρ ^ (m + 1) ∧
      (z = 0 ∨ ρ = (2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) := by
    rcases hz0.eq_or_lt with h | h
    · exact ⟨1, one_pos, by rw [← h]; simp, Or.inl h.symm⟩
    · have hcz : 0 < 2 * (c : ℝ) * z := mul_pos (mul_pos two_pos hc0') h
      refine ⟨_, Real.rpow_pos_of_pos hcz _, ?_, Or.inr rfl⟩
      have hpow : ((2 * (c : ℝ) * z) ^ ((1 : ℝ) / (m + 1))) ^ (m + 1) = 2 * (c : ℝ) * z := by
        rw [one_div, ← Nat.cast_succ]
        exact Real.rpow_inv_natCast_pow hcz.le (Nat.succ_ne_zero m)
      rw [hpow]
      have : 0 < (c : ℝ) * z := mul_pos hc0' h
      linarith
  have hcρ : 0 ≤ (c : ℝ) * ρ := mul_nonneg hc0 hρ0.le
  -- apply (DT) to `T = Z`
  obtain ⟨𝒬, -, hDT⟩ := hDT ρ Z.support Z.mass.toNNReal hρ0 hZc
  obtain ⟨Q, -, R, S, -, -, hR, hZQS, hQ, hQm, -, hRm, hSm, hQR, -⟩ :=
    hDT Z hZ subset_rfl (ENNReal.coe_toNNReal hZm.ne).ge
      (by rw [hZb, hmass0]; exact ENNReal.zero_lt_top)
  -- `M(S) ≤ cρ M(∂Z) = 0`, so `S = 0`
  rw [hZb, hmass0, mul_zero, nonpos_iff_eq_zero] at hSm
  obtain rfl : S = 0 := hzero _ S hSm
  -- `M(Q) ≤ cz < ρ^{m+1}`, so `Q = 0`
  obtain rfl : Q = 0 := by
    refine hQ.resolve_right fun h => ?_
    have h' := h.trans hQm
    rw [hZmz, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_le_ofReal_iff hcz0] at h'
    linarith
  -- hence `Z = ∂R`
  have hRZ : R.boundary = Z := by
    rw [← hZQS]
    ext ω
    show Z ω - 0 - 0 = Z ω
    ring
  rcases hρ with h | rfl
  · -- `z = 0`: `M(R) ≤ cρ · 0 = 0`, so `R = 0`
    rw [hZmz, h, ENNReal.ofReal_zero, mul_zero, nonpos_iff_eq_zero] at hRm
    refine ⟨R, hR, hRZ, hRm.trans_le zero_le, ?_⟩
    rw [hzero _ R hRm, hsupp0]
    exact empty_subset _
  · refine ⟨R, hR, hRZ, hRm.trans (le_of_eq ?_), subset_union_right.trans hQR⟩
    rw [ENNReal.ofReal_mul hcρ, ENNReal.ofReal_mul hc0, ENNReal.ofReal_coe_nnreal, hZmz]
/-- **Good slicing radius** (Simon Ch. 6, 8.2 (2)–(3): radii where `(F^{1/n})′` is controlled,
and `F′ = nF^{(n−1)/n}(F^{1/n})′`).  If `μ` is finite on compact sets, `n ≥ 1`, `a, s > 0`,
`μ(B_s(x₁)) < (as)ⁿ` and `L¹(N) = 0`, then some `ρ ∈ (0, s) \ N` has `μ(∂B_ρ(x₁)) = 0` and
`liminf_{h ↓ 0} h⁻¹ μ{ρ − h < |x − x₁| < ρ} ≤ 2na μ(B_ρ(x₁))^{(n−1)/n}`.  Let `F(r) = μ(B_r(x₁))`
and `G = F^{1/n}`: both are nondecreasing, `G(0) = 0` and `G(s) ≤ as`, so `∫_{(0,s)} G′ ≤ as`
(Lebesgue's inequality).  The good-radius lemma applied to `1_{(0,s)} G′` avoids `N`, the
non-differentiability points of `G` and the spheres charged by `μ`, with `G′(ρ) ≤ (2/s)·as = 2a`.
Then `F = Gⁿ` has derivative `nG(ρ)^{n−1}G′(ρ) ≤ 2na F(ρ)^{(n−1)/n}` at `ρ`, which bounds the
inner-annulus liminf. -/
theorem Submission.cbrld_exists_good_slice_radius : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (x₁ : Euclid P) (a s : ℝ) (N : Set ℝ), (∀ K : Set (Euclid P), IsCompact K → μ K < ∞) → 1 ≤ n → 0 < a → 0 < s → μ (ball x₁ s) < ENNReal.ofReal ((a * s) ^ n) → volume N = 0 → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s ∧ ρ ∉ N ∧ μ (sphere x₁ ρ) = 0 ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | ρ - h < dist x x₁ ∧ dist x x₁ < ρ}) (𝓝[>] 0) ≤ ENNReal.ofReal (2 * n * a * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n)) := by
  intro P n μ x₁ a s N hμ hn ha hs hμs hN
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hn0' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hinv : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0'.le
  -- `μ` is finite on balls (closed balls are compact)
  have hball : ∀ r : ℝ, μ (ball x₁ r) ≠ ∞ := fun r =>
    ne_top_of_le_ne_top (hμ _ (isCompact_closedBall x₁ r)).ne (measure_mono ball_subset_closedBall)
  -- `F(r) = μ(B_r(x₁))` and `G = F^{1/n}` are nondecreasing, `G(0) = 0`, `Gⁿ = F`, `G(s) ≤ as`
  set F : ℝ → ℝ := fun r => (μ (ball x₁ r)).toReal with hF_def
  set G : ℝ → ℝ := fun r => F r ^ (n : ℝ)⁻¹ with hG_def
  have hF0 : ∀ r, 0 ≤ F r := fun r => ENNReal.toReal_nonneg
  have hFmono : Monotone F := fun r r' hrr' =>
    ENNReal.toReal_mono (hball r') (measure_mono (ball_subset_ball hrr'))
  have hGmono : Monotone G := fun r r' hrr' => Real.rpow_le_rpow (hF0 r) (hFmono hrr') hinv
  have hFG : ∀ r, G r ^ n = F r := fun r => Real.rpow_inv_natCast_pow (hF0 r) hn0
  have hG0 : G 0 = 0 := by
    simp only [hG_def, hF_def, ball_zero, measure_empty, ENNReal.toReal_zero]
    exact Real.zero_rpow (inv_ne_zero hn0'.ne')
  have hGs : G s ≤ a * s :=
    calc G s ≤ ((a * s) ^ n) ^ (n : ℝ)⁻¹ :=
          Real.rpow_le_rpow (hF0 s) (ENNReal.toReal_lt_of_lt_ofReal hμs).le hinv
      _ = a * s := Real.pow_rpow_inv_natCast (mul_pos ha hs).le hn0
  -- Lebesgue's inequality: `∫⁻_{(0,s)} G′ ≤ G(s) − G(0) ≤ as`
  have hgm : AEMeasurable ((Ioo 0 s).indicator fun t => ENNReal.ofReal (deriv G t)) :=
    ((ENNReal.measurable_ofReal.comp (measurable_deriv G)).indicator measurableSet_Ioo).aemeasurable
  have hgI : ∫⁻ t, (Ioo 0 s).indicator (fun t => ENNReal.ofReal (deriv G t)) t ≤
      ENNReal.ofReal (a * s) := by
    rw [lintegral_indicator measurableSet_Ioo]
    refine (Submission.cmcs_smi_lintegral_ofReal_deriv_le G 0 s hGmono).trans ?_
    rw [hG0, sub_zero]
    exact ENNReal.ofReal_le_ofReal hGs
  -- the exceptional radii: `N` and the points where `G` is not differentiable
  have hp : ∀ᵐ t, t ∉ N ∧ DifferentiableAt ℝ G t :=
    (measure_eq_zero_iff_ae_notMem.mp hN).and hGmono.ae_differentiableAt
  obtain ⟨ρ, hρ0, hρs, ⟨hρN, hρd⟩, hρsph, hρg⟩ :=
    Submission.dor_lmb_glc_good_radius P μ x₁ 0 s _ _ _ hs (hμ _ (isCompact_closedBall x₁ s)).ne
      hgm hgI hp
  -- `G′(ρ) ≤ (2/s) · as = 2a`
  have hGd : deriv G ρ ≤ 2 * a := by
    rw [indicator_of_mem (mem_Ioo.mpr ⟨hρ0, hρs⟩), sub_zero,
      ← ENNReal.ofReal_mul (div_nonneg zero_le_two hs.le),
      show 2 / s * (a * s) = 2 * a by field_simp,
      ENNReal.ofReal_le_ofReal_iff (mul_pos two_pos ha).le] at hρg
    exact hρg
  refine ⟨ρ, hρ0, hρs, hρN, hρsph, ?_⟩
  -- `F = Gⁿ` has derivative `nG(ρ)^{n−1}G′(ρ)` at `ρ`
  have hFd : HasDerivAt F (n * G ρ ^ (n - 1) * deriv G ρ) ρ := by
    have h := hρd.hasDerivAt.fun_pow n
    rwa [show (fun r => G r ^ n) = F from funext hFG] at h
  refine (Submission.cbrld_radius_liminf_annulus_le_of_hasDerivAt P μ x₁ ρ _ (hball ρ) hFd).trans
    (ENNReal.ofReal_le_ofReal ?_)
  -- `G(ρ)^{n−1} = F(ρ)^{(n−1)/n}`, and `G′(ρ) ≤ 2a`
  have hpow : G ρ ^ (n - 1) = (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) := by
    rw [hG_def, hF_def]
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg, Nat.cast_sub hn,
      Nat.cast_one, inv_mul_eq_div]
  rw [hpow]
  have hX : 0 ≤ (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  calc (n : ℝ) * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) * deriv G ρ
      ≤ n * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) * (2 * a) := by gcongr
    _ = 2 * n * a * (μ (ball x₁ ρ)).toReal ^ (((n : ℝ) - 1) / n) := by ring
/-- **Degree-zero mass gap** (Simon Ch. 6, footnote 5 to 8.2, the case `n = 1`), assuming the
mass representation `(MR)` `M_W(T) = μ_T(W)` for open `U`, `W`: an integer multiplicity
`0`-current `Z` in `ℝᴾ` with `M(Z) < 1` is zero.  If `Z = τ(M, θ, ξ)` and `x ∈ M`, then
`M(Z) = μ_Z(ℝᴾ) ≥ μ_Z({x}) = θ(x) H⁰({x}) = θ(x) ≥ 1`; hence `M = ∅` and every `Z(ω)` is an
integral over `∅`. -/
theorem Submission.cbrld_im_degree_zero_eq_zero_of_mass_lt_one : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P : ℕ) (Z : GeometricCurrentOn (univ : Set (Euclid P)) 0), IsIntegerMultiplicity Z → Z.mass < 1 → Z = 0 := by
  rintro hMR P Z ⟨R, hR⟩ hZ
  -- `(MR)` with `U = W = ℝᴾ`: `M(Z) = μ_Z(ℝᴾ)`
  have hmass : Z.mass = R.measure univ := hMR P 0 univ Z R isOpen_univ hR univ isOpen_univ
  -- a point `x ∈ M` would carry `μ_Z({x}) = θ(x) H⁰({x}) = θ(x) ≥ 1 > M(Z)`
  have hempty : R.carrier = ∅ := by
    refine eq_empty_of_forall_notMem fun x hx => ?_
    have hx1 : R.measure {x} = (R.mult x : ℝ≥0∞) := by
      rw [IMRep.measure, withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
        Measure.restrict_apply (measurableSet_singleton x), singleton_inter_of_mem hx,
        Measure.euclideanHausdorffMeasure_zero, Measure.hausdorffMeasure_zero_singleton, mul_one]
    have h1 : (1 : ℝ≥0∞) ≤ R.measure {x} := hx1 ▸ Nat.one_le_cast.2 (R.mult_pos x hx)
    exact not_le.2 hZ (h1.trans ((measure_mono (subset_univ _)).trans hmass.ge))
  -- every `Z(ω)` is an integral over `M = ∅`
  ext ω
  rw [hR ω, GeometricCurrentOn.zero_apply, IMRep.action, hempty, setIntegral_empty]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
