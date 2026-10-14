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

/-- **Simon Ch. 4, 2.3** (tangential divergence of a rotation field): for the skew linear map
`A y = ⟨y, a⟩e − ⟨y, e⟩a` and `X = gA` with `g` differentiable at `x`,
`div_M X(x) = Dg(x)(p(Ax))`, `p = p_{TₓM}`.  The product rule gives `DX(x) = g(x)A + Dg(x)(·)Ax`,
so `p ∘ DX(x)` is a combination of the rank-one maps `u ↦ ⟨a, u⟩pe`, `u ↦ ⟨e, u⟩pa` and
`u ↦ Dg(x)(u)p(Ax)`, with traces `⟨a, pe⟩`, `⟨e, pa⟩` and `Dg(x)(p(Ax))`; `p` being
self-adjoint, `⟨a, pe⟩ = ⟨e, pa⟩`. -/
theorem Submission.idtp_cse_rc_rotation_divergence : ∀ (P n : ℕ) (M : Set (Euclid P)) (a e x : Euclid P) (g : Euclid P → ℝ), DifferentiableAt ℝ g x → tangentialDivergence n M (fun y : Euclid P => g y • (inner ℝ y a • e - inner ℝ y e • a)) x = fderiv ℝ g x ((approxTangentPlane n M x).starProjection (inner ℝ x a • e - inner ℝ x e • a)) := by
  intro P n M a e x g hg
  set p := (approxTangentPlane n M x).starProjection with hp
  -- `A y = ⟪y, a⟫ e − ⟪y, e⟫ a` is the continuous linear map `⟪a, ·⟫ e − ⟪e, ·⟫ a`
  set A : Euclid P →L[ℝ] Euclid P := (innerSL ℝ a).smulRight e - (innerSL ℝ e).smulRight a
    with hA
  have hAy : ∀ y, A y = inner ℝ y a • e - inner ℝ y e • a := fun y => by
    simp [A, real_inner_comm]
  have hX : (fun y : Euclid P => g y • (inner ℝ y a • e - inner ℝ y e • a)) =
      fun y => g y • A y := by
    funext y
    rw [hAy]
  -- product rule: `DX(x) = g(x) A + Dg(x)(·) Ax`
  have hD : fderiv ℝ (fun y => g y • A y) x = g x • A + (fderiv ℝ g x).smulRight (A x) := by
    rw [fderiv_fun_smul hg A.differentiableAt, A.fderiv]
  -- `p ∘ DX(x)` is a combination of rank-one maps
  have hdecomp : p.toLinearMap ∘ₗ (g x • A + (fderiv ℝ g x).smulRight (A x)).toLinearMap =
      g x • ((innerₛₗ ℝ a).smulRight (p e) - (innerₛₗ ℝ e).smulRight (p a)) +
        (fderiv ℝ g x).toLinearMap.smulRight (p (A x)) := by
    ext u
    simp [A, map_sub, map_smul]
  -- `trace (p ∘ A) = ⟪a, p e⟫ − ⟪e, p a⟫ = 0`, `p` being self-adjoint
  have hskew : inner ℝ a (p e) - inner ℝ e (p a) = 0 := by
    rw [hp, ← Submodule.inner_starProjection_left_eq_right, real_inner_comm, sub_self]
  -- `trace (z ↦ ℓ(z) v) = ℓ(v)` (`LinearMap.trace_smulRight`) for each rank-one term
  unfold tangentialDivergence
  rw [hX, hD, ← hp, hdecomp, map_add, map_smul, map_sub, LinearMap.trace_smulRight,
    LinearMap.trace_smulRight, LinearMap.trace_smulRight, innerₛₗ_apply_apply,
    innerₛₗ_apply_apply, hskew, smul_zero, zero_add, ContinuousLinearMap.coe_coe, hAy]
/-- **Conical `C¹` cutoff around a subspace** (step 4 of the parent proof).  With
`π = Q.starProjection` and `u(y) = ‖y − π y‖² / (s² ‖y‖²)`, take
`ζ(y) = smoothTransition((4/3)(1 − u(y)))`.  Off `0`, `u` is smooth, `‖x − π x‖ ≤ (s/2)‖x‖` gives
`u ≤ 1/4` and `ζ = 1`, `s‖x‖ ≤ ‖x − π x‖` gives `u ≥ 1` and `ζ = 0`, and `ζ` is constant near `x`
when either inequality is strict, so `Dζ(x) = 0` there. -/
theorem Submission.idtp_cse_rc_cone_cutoff : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → ∃ ζ : Euclid P → ℝ, (∀ x : Euclid P, x ≠ 0 → ContDiffAt ℝ 1 ζ x) ∧ (∀ x : Euclid P, x ≠ 0 → ‖x - Q.starProjection x‖ ≤ s / 2 * ‖x‖ → ζ x = 1) ∧ (∀ x : Euclid P, x ≠ 0 → s * ‖x‖ ≤ ‖x - Q.starProjection x‖ → ζ x = 0) ∧ (∀ x : Euclid P, x ≠ 0 → (‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ s * ‖x‖ < ‖x - Q.starProjection x‖) → fderiv ℝ ζ x = 0) := by
  intro P Q s hs
  let ζ : Euclid P → ℝ := fun y =>
    Real.smoothTransition (4 / 3 * (1 - ‖y - Q.starProjection y‖ ^ 2 / (s ^ 2 * ‖y‖ ^ 2)))
  -- (b): `‖x − π x‖ ≤ (s/2)‖x‖` gives `u x ≤ 1/4`, so the argument of `smoothTransition` is `≥ 1`
  have h1 : ∀ x : Euclid P, x ≠ 0 → ‖x - Q.starProjection x‖ ≤ s / 2 * ‖x‖ → ζ x = 1 := by
    intro x hx hle
    have hd : 0 < s ^ 2 * ‖x‖ ^ 2 := mul_pos (pow_pos hs 2) (pow_pos (norm_pos_iff.2 hx) 2)
    have hu : ‖x - Q.starProjection x‖ ^ 2 / (s ^ 2 * ‖x‖ ^ 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ hd]
      nlinarith [pow_le_pow_left₀ (norm_nonneg _) hle 2]
    exact Real.smoothTransition.one_of_one_le (by linarith)
  -- (c): `s‖x‖ ≤ ‖x − π x‖` gives `u x ≥ 1`, so the argument of `smoothTransition` is `≤ 0`
  have h0 : ∀ x : Euclid P, x ≠ 0 → s * ‖x‖ ≤ ‖x - Q.starProjection x‖ → ζ x = 0 := by
    intro x hx hle
    have hd : 0 < s ^ 2 * ‖x‖ ^ 2 := mul_pos (pow_pos hs 2) (pow_pos (norm_pos_iff.2 hx) 2)
    have hu : 1 ≤ ‖x - Q.starProjection x‖ ^ 2 / (s ^ 2 * ‖x‖ ^ 2) := by
      rw [le_div_iff₀ hd]
      nlinarith [pow_le_pow_left₀ (mul_nonneg hs.le (norm_nonneg x)) hle 2]
    exact Real.smoothTransition.zero_of_nonpos (by linarith)
  refine ⟨ζ, fun x hx => ?_, h1, h0, fun x hx hx' => ?_⟩
  · -- (a): `u` is smooth at `x ≠ 0` (the denominator `s² ‖x‖²` is nonzero)
    have hd : s ^ 2 * ‖x‖ ^ 2 ≠ 0 := (mul_pos (pow_pos hs 2) (pow_pos (norm_pos_iff.2 hx) 2)).ne'
    have hu : ContDiffAt ℝ 1
        (fun y : Euclid P => ‖y - Q.starProjection y‖ ^ 2 / (s ^ 2 * ‖y‖ ^ 2)) x :=
      ((contDiff_id.sub Q.starProjection.contDiff).norm_sq ℝ).contDiffAt.fun_div
        (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt) hd
    exact (Real.smoothTransition.contDiffAt (n := 1)).comp x
      (contDiffAt_const.mul (contDiffAt_const.sub hu))
  · -- (d): `ζ` is constant on an open neighbourhood of `x`
    rcases hx' with hlt | hlt
    · have hV : IsOpen ({y : Euclid P | y ≠ 0} ∩ {y | ‖y - Q.starProjection y‖ < s / 2 * ‖y‖}) :=
        isOpen_ne.inter (isOpen_lt (by fun_prop) (by fun_prop))
      have hev : ζ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
        filter_upwards [hV.mem_nhds ⟨hx, hlt⟩] with y hy
        exact h1 y hy.1 hy.2.le
      rw [hev.fderiv_eq, fderiv_const_apply]
    · -- the region `s‖y‖ < ‖y − π y‖` avoids `0`
      have hV : IsOpen {y : Euclid P | s * ‖y‖ < ‖y - Q.starProjection y‖} :=
        isOpen_lt (by fun_prop) (by fun_prop)
      have hev : ζ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hV.mem_nhds hlt] with y hy
        have hy0 : y ≠ 0 := by
          rintro rfl
          simp at hy
        exact h0 y hy0 hy.le
      rw [hev.fderiv_eq, fderiv_const_apply]
/-- **Orthogonal projection onto a 2-plane in an orthonormal frame** (the linear-algebra half of
the polar-angle differential `idtp_cse_rc_angle_fderiv`, used for Simon 7.3.3(1)).  If `a, e ∈ Q`
are orthonormal and `dim Q = 2`, then `π_Q y = ⟨y, a⟩ a + ⟨y, e⟩ e` and
`|π_Q y|² = ⟨y, a⟩² + ⟨y, e⟩²`.  The orthonormal pair `![a, e]` is independent, so it spans `Q`;
`y − (⟨y, a⟩ a + ⟨y, e⟩ e)` is orthogonal to `a` and `e`, hence to `Q`, and `π_Q y` is the unique
point of `Q` with this property. -/
theorem Submission.idtp_cse_rc_af_plane_projection : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → ∀ y : Euclid P, Q.starProjection y = inner ℝ y a • a + inner ℝ y e • e ∧ ‖Q.starProjection y‖ ^ 2 = inner ℝ y a ^ 2 + inner ℝ y e ^ 2 := by
  intro P Q a e hQ ha he ha1 he1 hae y
  -- `⟪a, a⟫ = ⟪e, e⟫ = 1` and `⟪a, e⟫ = ⟪e, a⟫ = 0`
  have haa : inner ℝ a a = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, ha1, one_pow]
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
  have hea : inner ℝ e a = (0 : ℝ) := by rw [real_inner_comm, hae]
  -- `![a, e]` is orthonormal, hence linearly independent
  have hv : Orthonormal ℝ ![a, e] := by
    rw [orthonormal_iff_ite]
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, haa, hee, hae, hea]
    simp
  -- `span {a, e} = Q`: the span lies in `Q` and has the same dimension `2`
  have hrange : Set.range ![a, e] = {a, e} := Matrix.range_cons_cons_empty a e ![]
  have hspan : Submodule.span ℝ {a, e} = Q := by
    rw [← hrange]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le, hrange, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨ha, he⟩
    · rw [finrank_span_eq_card hv.linearIndependent, hQ, Fintype.card_fin]
  -- `w = ⟪y, a⟫ a + ⟪y, e⟫ e` lies in `Q`, and `y - w` is orthogonal to `a` and `e`
  have hwQ : inner ℝ y a • a + inner ℝ y e • e ∈ Q :=
    Q.add_mem (Q.smul_mem _ ha) (Q.smul_mem _ he)
  have hya : inner ℝ (y - (inner ℝ y a • a + inner ℝ y e • e)) a = (0 : ℝ) := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, haa, hea]
    ring
  have hye : inner ℝ (y - (inner ℝ y a • a + inner ℝ y e • e)) e = (0 : ℝ) := by
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, hae, hee]
    ring
  -- so `y - w` is orthogonal to `span {a, e} = Q` (the kernel of `⟪y - w, ·⟫`), and `π y = w`
  have hproj : Q.starProjection y = inner ℝ y a • a + inner ℝ y e • e := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hwQ fun z hz => ?_
    have hK : Submodule.span ℝ {a, e} ≤
        LinearMap.ker (innerₛₗ ℝ (y - (inner ℝ y a • a + inner ℝ y e • e))) := by
      rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨by rw [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply, hya],
        by rw [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply, hye]⟩
    rw [← hspan] at hz
    have hz' := hK hz
    rwa [LinearMap.mem_ker, innerₛₗ_apply_apply] at hz'
  -- `‖π y‖² = ⟪w, w⟫ = ⟪y, a⟫² + ⟪y, e⟫²`
  refine ⟨hproj, ?_⟩
  rw [hproj, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
    haa, hee, hae, hea]
  ring
/-- **Differential of the polar angle `arctan (⟨y, e⟩ / ⟨y, a⟩)`** (the calculus step of the
rotation argument for cone sectors in Simon 7.3).  If `⟨x, a⟩ ≠ 0`, then
`f(y) = arctan (⟨y, e⟩ / ⟨y, a⟩)` is `C¹` near `x` and, for every `v`,
`Df(x) v = ⟨⟨x, a⟩ e - ⟨x, e⟩ a, v⟩ / (⟨x, a⟩² + ⟨x, e⟩²)`.
* `y ↦ ⟨y, a⟩ = innerSL ℝ a y` and `y ↦ ⟨y, e⟩` are continuous linear, hence smooth and their
  own derivatives; the quotient is `C¹` at `x` because `⟨x, a⟩ ≠ 0`, and so is its `arctan`.
* With `α = ⟨x, a⟩` and `β = ⟨x, e⟩`, the inverse, product and `arctan` chain rules give
  `Df(x) v = (1 + (β / α)²)⁻¹ (β (-(α²)⁻¹ ⟨a, v⟩) + α⁻¹ ⟨e, v⟩)`, which equals
  `(α ⟨e, v⟩ - β ⟨a, v⟩) / (α² + β²)` since `α² + β² ≥ α² > 0`. -/
theorem Submission.idtp_cse_rc_af_polar_angle_fderiv : ∀ (P : ℕ) (a e x : Euclid P), inner ℝ x a ≠ 0 → ContDiffAt ℝ 1 (fun y : Euclid P => Real.arctan (inner ℝ y e / inner ℝ y a)) x ∧ ∀ v : Euclid P, fderiv ℝ (fun y : Euclid P => Real.arctan (inner ℝ y e / inner ℝ y a)) x v = inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / (inner ℝ x a ^ 2 + inner ℝ x e ^ 2) := by
  intro P a e x hx
  -- Step 1: `y ↦ ⟨y, a⟩` and `y ↦ ⟨y, e⟩` are the continuous linear maps `innerSL ℝ a`, `innerSL ℝ e`
  have hLa : (fun y : Euclid P => inner ℝ y a) = innerSL ℝ a := by
    funext y; rw [innerSL_apply_apply, real_inner_comm]
  have hLe : (fun y : Euclid P => inner ℝ y e) = innerSL ℝ e := by
    funext y; rw [innerSL_apply_apply, real_inner_comm]
  have hda : HasFDerivAt (fun y : Euclid P => inner ℝ y a) (innerSL ℝ a) x :=
    hLa ▸ (innerSL ℝ a).hasFDerivAt
  have hde : HasFDerivAt (fun y : Euclid P => inner ℝ y e) (innerSL ℝ e) x :=
    hLe ▸ (innerSL ℝ e).hasFDerivAt
  -- Step 2: the quotient `q = ⟨·, e⟩ / ⟨·, a⟩` is `C¹` at `x`, and so is `arctan ∘ q`
  have hq : ContDiffAt ℝ 1 (fun y : Euclid P => inner ℝ y e / inner ℝ y a) x := by
    have hca : ContDiffAt ℝ 1 (fun y : Euclid P => inner ℝ y a) x :=
      hLa ▸ (innerSL ℝ a).contDiff.contDiffAt
    have hce : ContDiffAt ℝ 1 (fun y : Euclid P => inner ℝ y e) x :=
      hLe ▸ (innerSL ℝ e).contDiff.contDiffAt
    exact hce.fun_div hca hx
  refine ⟨hq.arctan, fun v => ?_⟩
  -- Step 3: `y ↦ ⟨y, a⟩⁻¹` has derivative `-(α²)⁻¹ ⟨a, ·⟩` at `x`
  have hdinv : HasFDerivAt (fun y : Euclid P => (inner ℝ y a)⁻¹)
      (-(inner ℝ x a ^ 2)⁻¹ • innerSL ℝ a) x :=
    (hasDerivAt_inv hx).comp_hasFDerivAt x hda
  -- Step 4: the product rule for `q = ⟨·, e⟩ ⬝ ⟨·, a⟩⁻¹`
  have hdq : HasFDerivAt (fun y : Euclid P => inner ℝ y e / inner ℝ y a)
      (inner ℝ x e • (-(inner ℝ x a ^ 2)⁻¹ • innerSL ℝ a) + (inner ℝ x a)⁻¹ • innerSL ℝ e) x := by
    simp only [div_eq_mul_inv]
    exact hde.fun_mul hdinv
  -- Step 5: the `arctan` chain rule and uniqueness of the derivative
  have hdf : HasFDerivAt (fun y : Euclid P => Real.arctan (inner ℝ y e / inner ℝ y a))
      ((1 / (1 + (inner ℝ x e / inner ℝ x a) ^ 2)) •
        (inner ℝ x e • (-(inner ℝ x a ^ 2)⁻¹ • innerSL ℝ a) + (inner ℝ x a)⁻¹ • innerSL ℝ e)) x :=
    hdq.arctan
  rw [hdf.fderiv]
  -- Step 6: algebra, with `α ≠ 0` and `α² + β² ≥ α² > 0`
  simp only [smul_apply, add_apply, innerSL_apply_apply, smul_eq_mul, inner_sub_left,
    real_inner_smul_left]
  have hden : inner ℝ x a ^ 2 + inner ℝ x e ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **Simon 7.3.3, proof of (1)** (2-dimensional minimizing cones, chapter text lines 501–504;
polar angle for the rotation field, Ch. 4, 2.2–2.6): if `a, e` is an orthonormal pair in the
`2`-dimensional subspace `Q`, then (i) `|p_Q y|² = (y · a)² + (y · e)²`, and (ii) on `{x · a > 0}`
the angle `f(y) = arctan((y · e)/(y · a))` is `C¹` with
`Df(x)v = ((x · a)e − (x · e)a) · v / |p_Q x|²`.  `(a, e)` is an orthonormal basis of `Q`, so
`p_Q y = (y · a)a + (y · e)e`, which gives (i); the quotient and `arctan` chain rules give `Df(x)v`
with denominator `(x · a)² + (x · e)²`, which is `|p_Q x|²` by (i). -/
theorem Submission.idtp_cse_rc_angle_fderiv : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → (∀ y : Euclid P, ‖Q.starProjection y‖ ^ 2 = inner ℝ y a ^ 2 + inner ℝ y e ^ 2) ∧ ∀ x : Euclid P, 0 < inner ℝ x a → ContDiffAt ℝ 1 (fun y : Euclid P => Real.arctan (inner ℝ y e / inner ℝ y a)) x ∧ ∀ v : Euclid P, fderiv ℝ (fun y : Euclid P => Real.arctan (inner ℝ y e / inner ℝ y a)) x v = inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / ‖Q.starProjection x‖ ^ 2 := by
  intro P Q a e hQ ha he ha1 he1 hae
  -- (i): `p_Q y = (y · a)a + (y · e)e`, so `|p_Q y|² = (y · a)² + (y · e)²`
  have hnorm : ∀ y : Euclid P, ‖Q.starProjection y‖ ^ 2 = inner ℝ y a ^ 2 + inner ℝ y e ^ 2 :=
    fun y => (Submission.idtp_cse_rc_af_plane_projection P Q a e hQ ha he ha1 he1 hae y).2
  refine ⟨hnorm, fun x hx => ?_⟩
  -- (ii): `x · a ≠ 0`, and the denominator `(x · a)² + (x · e)²` of `Df(x)v` is `|p_Q x|²` by (i)
  obtain ⟨hf, hDf⟩ := Submission.idtp_cse_rc_af_polar_angle_fderiv P a e x hx.ne'
  exact ⟨hf, fun v => by rw [hDf v, hnorm x]⟩

/-- **Support estimate for the angular test function** (steps 3–4 of the test-function
construction in the rotation argument for cone sectors, Simon 7.3).  Write `π = Q.starProjection`,
`α = ⟨y, a⟩ > 0` and `β = ⟨y, e⟩`, and assume `|π y|² = α² + β²`.  If `0 < s ≤ 1/4`,
`||y| − 1| < s`, `|arctan (β / α)| < s` and `|y − π y| < s |y|`, then `α > 1/2` and `|y| < 5/4`.
* `s ≤ 1/4 < π/4 = arctan 1` and `arctan` is increasing and odd, so `−1 < β / α < 1`; as `α > 0`,
  this is `−α < β < α`, hence `β² < α²`.
* `3/4 < |y| < 5/4`, and Pythagoras `|y|² = |π y|² + |y − π y|²` with `|y − π y|² < s² |y|²`,
  `s² ≤ 1/16` gives `|π y|² > (15/16) |y|² > 135/256`.
* So `2 α² > α² + β² = |π y|² > 135/256`, i.e. `α² > 135/512 > (1/2)²`, and `α > 1/2`. -/
theorem Submission.idtp_cse_rc_tf_support_bound : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e y : Euclid P) (s : ℝ), 0 < s → s ≤ 1 / 4 → ‖Q.starProjection y‖ ^ 2 = inner ℝ y a ^ 2 + inner ℝ y e ^ 2 → 0 < inner ℝ y a → |‖y‖ - 1| < s → |Real.arctan (inner ℝ y e / inner ℝ y a)| < s → ‖y - Q.starProjection y‖ < s * ‖y‖ → 1 / 2 < inner ℝ y a ∧ ‖y‖ < 5 / 4 := by
  intro P Q a e y s hs hs4 hproj ha hy harc hq
  -- Step 1: `s ≤ 1/4 < π/4` (as `π ≥ 2`), and `−s < arctan (β / α) < s`
  have hpi : s < Real.pi / 4 := by linarith [Real.two_le_pi]
  obtain ⟨harc₁, harc₂⟩ := abs_lt.1 harc
  -- Step 2: `−1 < β / α < 1`, since `arctan` is monotone with `arctan (±1) = ±π/4`
  have ht₁ : inner ℝ y e / inner ℝ y a < 1 := by
    by_contra h
    have h' := Real.arctan_strictMono.monotone (not_lt.1 h)
    rw [Real.arctan_one] at h'
    linarith
  have ht₂ : -1 < inner ℝ y e / inner ℝ y a := by
    by_contra h
    have h' := Real.arctan_strictMono.monotone (not_lt.1 h)
    rw [Real.arctan_neg, Real.arctan_one] at h'
    linarith
  -- Step 3: multiplying by `α > 0` gives `−α < β < α`, hence `β² < α²`
  rw [div_lt_one ha] at ht₁
  rw [lt_div_iff₀ ha] at ht₂
  have hβα : inner ℝ y e ^ 2 < inner ℝ y a ^ 2 := by nlinarith
  -- Step 4: Pythagoras `|y|² = |π y|² + |y − π y|²`, as `π_{Qᗮ} y = y − π y`
  have hpyth : ‖y‖ ^ 2 = ‖Q.starProjection y‖ ^ 2 + ‖y - Q.starProjection y‖ ^ 2 := by
    rw [← Submodule.starProjection_orthogonal_val]
    exact Q.norm_sq_eq_add_norm_sq_starProjection y
  -- Step 5: `3/4 < |y| < 5/4`, so `|y|² > 9/16`
  obtain ⟨hy₁, hy₂⟩ := abs_lt.1 hy
  have hy34 : 3 / 4 < ‖y‖ := by linarith
  have hysq : 9 / 16 < ‖y‖ ^ 2 := by nlinarith
  -- Step 6: `|y − π y|² < s² |y|²` and `s² ≤ 1/16`, so `|π y|² > (15/16) |y|² > 135/256`
  have hq2 : ‖y - Q.starProjection y‖ ^ 2 < (s * ‖y‖) ^ 2 :=
    pow_lt_pow_left₀ hq (norm_nonneg _) two_ne_zero
  have hs2 : s ^ 2 ≤ 1 / 16 := by nlinarith
  have hπ : 135 / 256 < ‖Q.starProjection y‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs2 (sq_nonneg ‖y‖)]
  -- Step 7: `2 α² > α² + β² = |π y|² > 135/256`, so `α² > (1/2)²` and `α > 1/2`
  refine ⟨?_, by linarith⟩
  have hα2 : (1 / 2 : ℝ) ^ 2 < inner ℝ y a ^ 2 := by nlinarith
  exact (pow_lt_pow_iff_left₀ (by norm_num) ha.le two_ne_zero).1 hα2
/-- **Extension by zero of a `C¹` function vanishing off a compact subset of `U`** (steps 5–7 of
the test-function construction for the rotation argument of Simon 7.3).  Let `U` be open,
`K ⊆ U` compact, `h` `C¹` at every point of `U`, and `h y ≠ 0`, `y ∈ U` force `y ∈ K`.  Then
`g = U.indicator h` is `C¹` with compact support, `Dg(x) = Dh(x)` on `U` and `Dg(x) = 0` off `U`.
* `g y ≠ 0` forces `y ∈ U` and `h y ≠ 0`, so `support g ⊆ K`; `K` is closed, so `tsupport g ⊆ K`,
  and `g` vanishes off the compact set `K`.
* For `x ∈ U`, `g = h` on the neighbourhood `U` of `x`; for `x ∉ U`, `x ∉ K ⊇ tsupport g`, so
  `g = 0` near `x`.  Either way `g` is `C¹` at `x` with the stated derivative. -/
theorem Submission.idtp_cse_rc_tf_indicator_extension : ∀ (P : ℕ) (U K : Set (Euclid P)) (h : Euclid P → ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ x ∈ U, ContDiffAt ℝ 1 h x) → (∀ y ∈ U, h y ≠ 0 → y ∈ K) → ContDiff ℝ 1 (U.indicator h) ∧ HasCompactSupport (U.indicator h) ∧ (∀ x ∈ U, fderiv ℝ (U.indicator h) x = fderiv ℝ h x) ∧ (∀ x ∉ U, fderiv ℝ (U.indicator h) x = 0) := by
  intro P U K h hU hK hKU hh hhK
  -- Step 1: `support g ⊆ K`: `g y ≠ 0` forces `y ∈ U` (else `g y = 0`) and then `h y = g y ≠ 0`
  have hsupp : ∀ y, U.indicator h y ≠ 0 → y ∈ K := by
    intro y hy
    by_cases hyU : y ∈ U
    · rw [Set.indicator_of_mem hyU] at hy
      exact hhK y hyU hy
    · exact absurd (Set.indicator_of_notMem hyU h) hy
  -- Step 2: `K` is compact, hence closed, so `tsupport g = closure (support g) ⊆ K`
  have htsupp : tsupport (U.indicator h) ⊆ K :=
    closure_minimal (fun y hy => hsupp y hy) hK.isClosed
  -- Step 4: for `x ∈ U`, `g = h` on the neighbourhood `U` of `x`
  have hin : ∀ x ∈ U, U.indicator h =ᶠ[𝓝 x] h := fun x hx => by
    filter_upwards [hU.mem_nhds hx] with y hy using Set.indicator_of_mem hy h
  -- Step 5: for `x ∉ U`, `x ∉ K ⊇ tsupport g`, so `g = 0` near `x`
  have hout : ∀ x ∉ U, U.indicator h =ᶠ[𝓝 x] fun _ => (0 : ℝ) := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.1 fun hxs => hx (hKU (htsupp hxs))
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, HasCompactSupport.intro hK fun y hy => ?_,
    fun x hx => (hin x hx).fderiv_eq, fun x hx => ?_⟩
  · -- Step 6: `g` is `C¹` at every point, by Steps 4 and 5
    by_cases hx : x ∈ U
    · exact (hh x hx).congr_of_eventuallyEq (hin x hx)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout x hx)
  · -- Step 3: `g` vanishes off the compact set `K`
    by_contra hy'
    exact hy (hsupp y hy')
  · -- Step 5: `Dg(x) = D0(x) = 0`
    rw [(hout x hx).fderiv_eq, fderiv_const_apply]
/-- **Derivative of `ψ(f) · l(|·|) · ζ` in a direction orthogonal to the position vector** (step 8,
formula (★), of the test function for the rotation argument in Simon 7.3).  If `x ≠ 0`,
`⟨x, v⟩ = 0`, `f` and `ζ` are differentiable at `x`, `ψ` at `f(x)` and `l` at `|x|`, then
`h(y) = ψ(f(y)) l(|y|) ζ(y)` has `Dh(x)v = ψ(f(x)) l(|x|) Dζ(x)v + ζ(x) l(|x|) ψ'(f(x)) Df(x)v`:
the radial term drops.
* `N = |·|` is differentiable at `x ≠ 0`; `D(N²)(x)` is `2|x| DN(x)` by the chain rule and
  `2⟨x, ·⟩` directly, so `2|x| DN(x)v = 2⟨x, v⟩ = 0` and `DN(x)v = 0`.
* The chain and product rules for `((ψ ∘ f) · (l ∘ N)) · ζ` give
  `Dh(x)v = ψ(f(x)) l(|x|) Dζ(x)v + ζ(x) (ψ(f(x)) l'(|x|) DN(x)v + l(|x|) ψ'(f(x)) Df(x)v)`. -/
theorem Submission.idtp_cse_rc_tf_product_fderiv : ∀ (P : ℕ) (f ζ : Euclid P → ℝ) (ψ l : ℝ → ℝ) (x v : Euclid P), x ≠ 0 → inner ℝ x v = 0 → DifferentiableAt ℝ f x → DifferentiableAt ℝ ψ (f x) → DifferentiableAt ℝ l ‖x‖ → DifferentiableAt ℝ ζ x → fderiv ℝ (fun y : Euclid P => ψ (f y) * l ‖y‖ * ζ y) x v = ψ (f x) * l ‖x‖ * fderiv ℝ ζ x v + ζ x * l ‖x‖ * (deriv ψ (f x) * fderiv ℝ f x v) := by
  intro P f ζ ψ l x v hx hxv hf hψ hl hζ
  -- Step 1: the norm `N = ‖·‖` is differentiable at `x ≠ 0`
  have hN : HasFDerivAt (fun y : Euclid P => ‖y‖) (fderiv ℝ (fun y : Euclid P => ‖y‖) x) x :=
    ((contDiffAt_norm ℝ (n := 1) hx).differentiableAt one_ne_zero).hasFDerivAt
  -- Step 2: `D(N²)(x) = 2‖x‖ DN(x)` (chain rule) and `D(‖·‖²)(x) = 2⟪x, ·⟫` agree; at `v` this
  -- reads `2‖x‖ DN(x) v = 2⟪x, v⟫ = 0`, so `DN(x) v = 0` as `‖x‖ ≠ 0`
  have hNv : fderiv ℝ (fun y : Euclid P => ‖y‖) x v = 0 := by
    have h2 := DFunLike.congr_fun ((hN.pow 2).unique (hasStrictFDerivAt_norm_sq x).hasFDerivAt) v
    simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, hxv, smul_zero, nsmul_eq_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one] at h2
    exact (mul_eq_zero.1 h2).resolve_left (mul_ne_zero two_ne_zero (norm_ne_zero_iff.2 hx))
  -- Step 3: chain rules for `F = ψ ∘ f` and `L = l ∘ N`
  have hF : HasFDerivAt (fun y : Euclid P => ψ (f y)) (deriv ψ (f x) • fderiv ℝ f x) x :=
    hψ.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt
  have hL : HasFDerivAt (fun y : Euclid P => l ‖y‖)
      (deriv l ‖x‖ • fderiv ℝ (fun y : Euclid P => ‖y‖) x) x :=
    hl.hasDerivAt.comp_hasFDerivAt x hN
  -- Step 4: the product rule, twice, for `h = (F ⬝ L) ⬝ ζ`
  rw [((hF.fun_mul hL).fun_mul hζ.hasFDerivAt).fderiv]
  -- Step 5: evaluate at `v`, drop the radial term `DL(x) v = l'(‖x‖) DN(x) v = 0`, rearrange
  simp only [add_apply, smul_apply, smul_eq_mul, hNv]
  ring

/-- **`C¹` angular test function adapted to the gap hypothesis** (steps 4, 5 and 7 of the parent
proof).  With `f(y) = arctan(⟨y,e⟩/⟨y,a⟩)`, the cutoff `ζ` of `idtp_cse_rc_cone_cutoff` and
`h = ψ(f)·l(|·|)·ζ`, take `g = 1_U·h` for `U = {⟨y,a⟩ > 0}`.  Where `h ≠ 0` in `U`, the support
hypotheses on `ψ`, `l` and `ζ` put `y` in `Z`, hence in the compact set
`K = {⟨y,a⟩ ≥ 1/2} ∩ B̄(0, 5/4) ⊆ U`; so `g` is `C¹` with compact support, `Dg = Dh` on `U` and
`Dg = 0` off `U`.  For `⟨x,v⟩ = 0`, `Dh(x)v = ψ(f x)·l(|x|)·Dζ(x)v + ζ(x)·l(|x|)·ψ'(f x)·Df(x)v`.
On `Z` the gap forces `|x − πx| < (s/2)|x|`, so `ζ(x) = 1` and `Dζ(x) = 0`; off `Z` the first term
vanishes by the gap and the second because its factors cannot all be nonzero. -/
theorem Submission.idtp_cse_rc_test_function : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ) (ψ l : ℝ → ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → s ≤ 1 / 4 → ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → ∃ g : Euclid P → ℝ, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ (∀ x v : Euclid P, inner ℝ x v = 0 → (0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖) → x ∈ {y : Euclid P | 0 < inner ℝ y a ∧ |‖y‖ - 1| < s ∧ |Real.arctan (inner ℝ y e / inner ℝ y a)| < s ∧ ‖y - Q.starProjection y‖ < s * ‖y‖} → fderiv ℝ g x v = deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * (inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / ‖Q.starProjection x‖ ^ 2)) ∧ (∀ x v : Euclid P, inner ℝ x v = 0 → (0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖) → x ∉ {y : Euclid P | 0 < inner ℝ y a ∧ |‖y‖ - 1| < s ∧ |Real.arctan (inner ℝ y e / inner ℝ y a)| < s ∧ ‖y - Q.starProjection y‖ < s * ‖y‖} → fderiv ℝ g x v = 0) := by
  intro P Q a e s ψ l hQ ha he hna hne hae hs hs4 hψ hl hψs hls
  -- step 1: the cutoff `ζ`, the identity `|πy|² = ⟨y,a⟩² + ⟨y,e⟩²` and `Df` on `⟨x,a⟩ > 0`
  obtain ⟨ζ, hζC, hζ1, hζ0, hζD⟩ := Submission.idtp_cse_rc_cone_cutoff P Q s hs
  obtain ⟨hπ, hf⟩ := Submission.idtp_cse_rc_angle_fderiv P Q a e hQ ha he hna hne hae
  have hne0 : ∀ x : Euclid P, 0 < inner ℝ x a → x ≠ 0 := by
    rintro x hx rfl
    simp at hx
  -- `f(y) ∈ (-s, s)` where `ψ(f y) ≠ 0` or `ψ'(f y) ≠ 0`, and `||y| - 1| < s` where `l(|y|) ≠ 0`
  have hψ_lt : ∀ t : ℝ, ψ t ≠ 0 → |t| < s := fun t ht => abs_lt.2 (hψs (subset_tsupport ψ ht))
  have hψ'_lt : ∀ t : ℝ, deriv ψ t ≠ 0 → |t| < s := fun t ht =>
    abs_lt.2 (hψs (support_deriv_subset ht))
  have hl_lt : ∀ y : Euclid P, l ‖y‖ ≠ 0 → |‖y‖ - 1| < s := fun y hy => by
    obtain ⟨h1, h2⟩ := hls (subset_tsupport l hy)
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  -- `ζ(y) ≠ 0` forces `|y − πy| < s|y|` (by (c))
  have hζ_lt : ∀ y : Euclid P, y ≠ 0 → ζ y ≠ 0 → ‖y - Q.starProjection y‖ < s * ‖y‖ :=
    fun y hy hζy => lt_of_not_ge fun hc => hζy (hζ0 y hy hc)
  -- step 2: `h = ψ(f)·l(|·|)·ζ`, extended by zero off `U = {⟨y,a⟩ > 0}`
  set U : Set (Euclid P) := {y | 0 < inner ℝ y a}
  set K : Set (Euclid P) := {y | 1 / 2 ≤ inner ℝ y a} ∩ closedBall 0 (5 / 4)
  set h : Euclid P → ℝ := fun y => ψ (Real.arctan (inner ℝ y e / inner ℝ y a)) * l ‖y‖ * ζ y
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hK : IsCompact K :=
    (isCompact_closedBall 0 (5 / 4)).inter_left (isClosed_le continuous_const (by fun_prop))
  have hKU : K ⊆ U := fun y hy => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hy.1
  -- step 7: `h` is `C¹` at each point of `U`
  have hC : ∀ x ∈ U, ContDiffAt ℝ 1 h x := fun x hx =>
    ((hψ.contDiffAt.comp x (hf x hx).1).mul
      (hl.contDiffAt.comp x (contDiffAt_norm ℝ (hne0 x hx)))).mul (hζC x (hne0 x hx))
  -- steps 3–5: where `h ≠ 0` in `U`, `y ∈ Z`, so `⟨y,a⟩ > 1/2` and `|y| < 5/4`
  have hsupp : ∀ y ∈ U, h y ≠ 0 → y ∈ K := by
    intro y hy hhy
    have h1 : ψ (Real.arctan (inner ℝ y e / inner ℝ y a)) ≠ 0 := fun h0 => hhy (by simp [h, h0])
    have h2 : l ‖y‖ ≠ 0 := fun h0 => hhy (by simp [h, h0])
    have h3 : ζ y ≠ 0 := fun h0 => hhy (by simp [h, h0])
    obtain ⟨hya, hyn⟩ := Submission.idtp_cse_rc_tf_support_bound P Q a e y s hs hs4 (hπ y) hy
      (hl_lt y h2) (hψ_lt _ h1) (hζ_lt y (hne0 y hy) h3)
    exact ⟨hya.le, mem_closedBall_zero_iff.2 hyn.le⟩
  obtain ⟨hg, hgc, hDin, hDout⟩ :=
    Submission.idtp_cse_rc_tf_indicator_extension P U K h hU hK hKU hC hsupp
  -- step 8, formula (★): for `⟨x,a⟩ > 0` and `⟨x,v⟩ = 0` the radial term drops
  have hprod : ∀ x v : Euclid P, 0 < inner ℝ x a → inner ℝ x v = 0 →
      fderiv ℝ h x v = ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * fderiv ℝ ζ x v +
        ζ x * l ‖x‖ * (deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) *
          (inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / ‖Q.starProjection x‖ ^ 2)) := by
    intro x v hxa hxv
    rw [← (hf x hxa).2 v]
    exact Submission.idtp_cse_rc_tf_product_fderiv P
      (fun y => Real.arctan (inner ℝ y e / inner ℝ y a)) ζ ψ l x v (hne0 x hxa) hxv
      (hf x hxa).1.differentiableAt_one (hψ.differentiable_one _) (hl.differentiable_one _)
      (hζC x (hne0 x hxa)).differentiableAt_one
  refine ⟨U.indicator h, hg, hgc, ?_, ?_⟩
  · -- step 9: on `Z` the gap forces `|x − πx| < (s/2)|x|`, so `ζ(x) = 1` and `Dζ(x) = 0`
    intro x v hxv hgap hxZ
    obtain ⟨hxa, hx1, hfx, hq⟩ := hxZ
    have hx0 := hne0 x hxa
    have hsx : 0 < s * ‖x‖ := mul_pos hs (norm_pos_iff.2 hx0)
    have hq2 : ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ := by
      rcases hgap hxa hx1 hfx with hq' | hq'
      · exact hq'
      · exact absurd hq' (by linarith)
    rw [hDin x hxa, hprod x v hxa hxv, hζ1 x hx0 hq2.le, hζD x hx0 (Or.inl hq2),
      zero_apply]
    ring
  · -- step 10: off `Z` both terms of (★) vanish
    intro x v hxv hgap hxZ
    by_cases hxa : 0 < inner ℝ x a
    · have hx0 := hne0 x hxa
      have hsx : 0 < s * ‖x‖ := mul_pos hs (norm_pos_iff.2 hx0)
      rw [hDin x hxa, hprod x v hxa hxv]
      -- first term: where `ψ(f x)·l(|x|) ≠ 0` the gap gives `Dζ(x) = 0` by (d)
      have t1 : ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * fderiv ℝ ζ x v = 0 := by
        by_cases h1 : ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) = 0
        · simp [h1]
        by_cases h2 : l ‖x‖ = 0
        · simp [h2]
        rw [hζD x hx0 ?_, zero_apply, mul_zero]
        rcases hgap hxa (hl_lt x h2) (hψ_lt _ h1) with hq | hq
        · exact Or.inl hq
        · exact Or.inr (by linarith)
      -- second term: `ζ(x)`, `l(|x|)`, `ψ'(f x)` all nonzero would put `x` in `Z`
      have t2 : ζ x * l ‖x‖ * (deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) *
          (inner ℝ (inner ℝ x a • e - inner ℝ x e • a) v / ‖Q.starProjection x‖ ^ 2)) = 0 := by
        by_cases h3 : ζ x = 0
        · simp [h3]
        by_cases h2 : l ‖x‖ = 0
        · simp [h2]
        by_cases h4 : deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) = 0
        · simp [h4]
        exact absurd ⟨hxa, hl_lt x h2, hψ'_lt _ h4, hζ_lt x hx0 h3⟩ hxZ
      rw [t1, t2, add_zero]
    · rw [hDout x hxa, zero_apply]

/-- **Rotation conservation on a cone sector** (Simon Ch. 4, 2.2–2.6: first variation of the
stationary `V = v(M, θ)` along a rotation field, as in the proof of 7.3.3(1)).  Let `(a, e)` be an
orthonormal basis of the 2-plane `Q`, `A y = ⟨y,a⟩e − ⟨y,e⟩a`, `f(y) = arctan(⟨y,e⟩/⟨y,a⟩)`,
`G(x) = |p_{TₓM}(Ax)|²/|πx|²` and `Z = {⟨x,a⟩ > 0, ||x| − 1| < s, |f(x)| < s, |x − πx| < s|x|}`.
If `V` is stationary, `p_{TₓM} x = x` and the gap condition hold `μ_V`-a.e., then
`ψ'(f)·l(|·|)·G` is `μ_V`-integrable on `Z` with integral `0`.
* With `g` from `idtp_cse_rc_test_function`, `X = gA` is `C¹` with compact support, so
  `0 = δV(X) = ∫_M θ div_M X dH²`, and `div_M X(x) = Dg(x)(p_{TₓM}(Ax))`
  (`idtp_cse_rc_rotation_divergence`).
* `μ_V`-a.e., `⟨x, p_{TₓM}(Ax)⟩ = ⟨p_{TₓM} x, Ax⟩ = ⟨x, Ax⟩ = 0` and
  `⟨Ax, p_{TₓM}(Ax)⟩ = |p_{TₓM}(Ax)|²`, so the derivative formulas of `g` give
  `Dg(x)(p_{TₓM}(Ax)) = 1_Z(x)·ψ'(f(x))·l(|x|)·G(x)`; as `μ_V = θ H²⌞M`, this yields
  `∫_Z ψ'(f)·l(|·|)·G dμ_V = δV(X) = 0`.
* `x ↦ p_{TₓM}` is `H²⌞M`-a.e. strongly measurable (`TₓM` is a.e. the plane oriented by `ξ(x)`,
  and the projection onto the plane of a unit simple 2-vector is a Borel function of it),
  `0 ≤ G ≤ 1` since `|Ax| = |πx|`, and `μ_V(Z) ≤ μ_V(B̄₂(0)) < ∞`. -/
theorem Submission.idtp_cse_rotation_conservation : ∀ (P : ℕ) (R : IMRep (univ : Set (Euclid P)) 2) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (s : ℝ), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → 0 < s → s ≤ 1 / 4 → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → R.firstVariation X = 0) → (∀ᵐ x ∂R.measure, (approxTangentPlane 2 R.carrier x).starProjection x = x) → (∀ᵐ x ∂R.measure, 0 < inner ℝ x a → |‖x‖ - 1| < s → |Real.arctan (inner ℝ x e / inner ℝ x a)| < s → ‖x - Q.starProjection x‖ < s / 2 * ‖x‖ ∨ 2 * s * ‖x‖ < ‖x - Q.starProjection x‖) → ∀ ψ l : ℝ → ℝ, ContDiff ℝ 1 ψ → ContDiff ℝ 1 l → tsupport ψ ⊆ Ioo (-s) s → tsupport l ⊆ Ioo (1 - s) (1 + s) → IntegrableOn (fun x : Euclid P => deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2)) {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} R.measure ∧ ∫ x in {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧ |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖}, deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ * (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2) ∂R.measure = 0 := by
  intro P R Q a e s hQ ha he hna hne hae hs hs4 hstat htan hgap ψ l hψ hl hψs hls
  classical
  -- step 6, measurability: `x ↦ p_{TₓM}` is `Hⁿ⌞M`-a.e. strongly measurable.  `TₓM` is a.e. the
  -- plane oriented by `ξ(x)`, and the projection onto the plane of a unit simple `n`-vector is a
  -- Borel function of it (the argument of `Submission.imrep_approxTangent_starProjection_aesm`)
  have haesm : ∀ (n : ℕ) (R : IMRep (univ : Set (Euclid P)) n),
      AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection)
        (μHE[n].restrict R.carrier) := by
    intro n R
    classical
    -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
    let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
      (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
    have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
      fun τ α => rfl
    -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
    let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
    have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
    let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
    have hΩ : IsCompact Ω := by
      refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
      · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
            ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
          ext τ
          simp [orthonormal_iff_ite]
        rw [hset]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
      · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
        rw [mem_closedBall_zero_iff]
        exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
    -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
    have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
      intro ζ Q
      constructor
      · rintro ⟨τ, hτ, hQ, h | h⟩
        · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
          ext α
          simp [Φ, hev, h]
        · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
          ext α
          simp [Φ, hev, h]
      · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
        refine ⟨τ, hτ, hQ, ?_⟩
        rcases hs with rfl | rfl
        · left
          intro α
          simp [Φ, hev]
        · right
          intro α
          simp [Φ, hev]
    -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
    have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
        ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro c
      let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
      let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
      have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
        intro u
        rw [← Matrix.det_transpose]
        rfl
      have hAc : Continuous fun u : Fin n → Euclid P => A u := by
        simp only [hA]
        exact Continuous.matrix_det (continuous_matrix fun k j => by
          simp only [Matrix.of_apply]
          exact continuous_const.inner (continuous_apply j))
      exact ⟨{ A with cont := hAc }, hA⟩
    -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
    -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
    have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
      rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
        Submodule.mem_orthogonal]
      intro y hy
      obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
      -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
      have h1 : α τ = inner ℝ y (τ i) := by
        rw [hα]
        have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
            (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
          ext k j
          by_cases hk : k = i
          · subst hk
            simp
          · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
        rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
          ← Matrix.cramer_apply, Matrix.cramer_one]
        rfl
      -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
      have h2 : α τ' = 0 := by
        rw [hα]
        refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
        simp only [Matrix.of_apply, Function.update_self]
        rw [real_inner_comm]
        exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
      have h3 : ζ α = 0 := by
        rcases hζ' with h | h <;> simp [h, h2]
      rcases hζ with h | h
      · rw [← h1, ← h, h3]
      · have h4 := h α
        rw [h3] at h4
        rw [← h1]
        linarith
    have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
      fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
    -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in
    -- `τ`
    let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
      fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
    have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
      intro ω v
      simp [F]
    have hFc : Continuous F := by
      refine continuous_clm_apply.mpr fun v => ?_
      simp only [hFapply]
      exact continuous_finsetSum _ fun k _ => by fun_prop
    have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
      rintro ⟨τ, s⟩ ⟨hτ, -⟩
      refine ContinuousLinearMap.ext fun v => ?_
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
      · rw [hFapply]
        exact Submodule.sum_mem _ fun k _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · intro w hw
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
        · rintro _ ⟨j, rfl⟩
          rw [hFapply, inner_sub_left, sum_inner]
          simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
        · simp
        · intro x y _ _ hx hy
          rw [inner_add_right, hx, hy, add_zero]
        · intro a x _ hx
          rw [inner_smul_right, hx, mul_zero]
    -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
    let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
      if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
    have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
      intro ζ Q hQ
      have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
      simp only [G, dite_eq_left hex]
      rw [huniq _ _ _ hex.choose_spec hQ]
    have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
      rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
    -- `G` is Borel: for closed `t`, `G⁻¹(t)` is a compact set `Φ(Ω ∩ F⁻¹(t))` together with the
    -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
    have hG : Measurable G := by
      refine measurable_of_isClosed fun t ht => ?_
      have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
          ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
        ext ζ
        simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
          Set.mem_compl_iff]
        by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
        · obtain ⟨Q, hQ⟩ := h
          obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
          have hGζ : G ζ = F ω := by
            rw [← hΦω]
            exact hGΦ ω hω
          constructor
          · intro hζt
            exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
          · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
            · rw [← hΦω', hGΦ ω' hω']
              exact hω't
            · exact absurd ⟨ω, hω, hΦω⟩ hn
        · have hGζ : G ζ = 0 := dite_eq_right h
          have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
            h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
          rw [hGζ]
          constructor
          · intro h0
            exact Or.inr ⟨hn, h0⟩
          · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
            · exact absurd ⟨ω', hω', hΦω'⟩ hn
            · exact h0
      rw [hset]
      exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
        ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
    -- a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes), so
    -- `p_{TₓM} = G(ξ(x))`
    have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
        =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
      filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
      have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
      have h1 : approxTangentPlane n R.carrier x = Q := by
        rw [approxTangentPlane, dite_eq_left hex]
        exact hex.choose_spec.unique hQ
      rw [Function.comp_apply, hGQ _ _ hor, h1]
    -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
    have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
      @PseudoEMetricSpace.pseudoMetrizableSpace _
        (inferInstance : PseudoEMetricSpace (MultiVector P n))
    exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
      ).congr hae.symm
  -- steps 1, 3: `|πy|² = ⟨y,a⟩² + ⟨y,e⟩²`; step 5: the `C¹` test function `g` of compact support
  obtain ⟨hπ, -⟩ := Submission.idtp_cse_rc_angle_fderiv P Q a e hQ ha he hna hne hae
  obtain ⟨g, hgC, hgc, hgZ, hgZc⟩ := Submission.idtp_cse_rc_test_function P Q a e s ψ l hQ ha he
    hna hne hae hs hs4 hψ hl hψs hls
  set Z : Set (Euclid P) := {x : Euclid P | 0 < inner ℝ x a ∧ |‖x‖ - 1| < s ∧
    |Real.arctan (inner ℝ x e / inner ℝ x a)| < s ∧ ‖x - Q.starProjection x‖ < s * ‖x‖} with hZ
  set φ : Euclid P → ℝ := fun x => deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a)) * l ‖x‖ *
    (‖(approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 /
      ‖Q.starProjection x‖ ^ 2) with hφ
  -- the rotation field `X = g A`, `A y = ⟨y,a⟩e − ⟨y,e⟩a`, is `C¹` with compact support
  set X : Euclid P → Euclid P := fun y => g y • (inner ℝ y a • e - inner ℝ y e • a) with hX
  have hAC : ContDiff ℝ 1 fun y : Euclid P => inner ℝ y a • e - inner ℝ y e • a :=
    ((contDiff_id.inner ℝ contDiff_const).smul contDiff_const).sub
      ((contDiff_id.inner ℝ contDiff_const).smul contDiff_const)
  have hXC : ContDiff ℝ 1 X := hgC.smul hAC
  have hXc : HasCompactSupport X := hgc.smul_right
  -- measurability of the angle `f`, of `Z` and of the multiplicity
  have hfm : Measurable fun x : Euclid P => Real.arctan (inner ℝ x e / inner ℝ x a) :=
    Real.continuous_arctan.measurable.comp
      ((continuous_id.inner continuous_const).measurable.div
        (continuous_id.inner continuous_const).measurable)
  have hZm : MeasurableSet Z := by
    simp only [hZ, Set.ofPred_and]
    exact (measurableSet_lt measurable_const
      (continuous_id.inner continuous_const).measurable).inter
      ((measurableSet_lt (continuous_norm.sub continuous_const).abs.measurable
        measurable_const).inter
        ((measurableSet_lt (continuous_abs.measurable.comp hfm) measurable_const).inter
          (measurableSet_lt (continuous_id.sub Q.starProjection.continuous).norm.measurable
            (continuous_const.mul continuous_norm).measurable)))
  have hmult : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
  -- step 2: `div_M X(x) = Dg(x)(p_{TₓM}(Ax))`
  have hdiv : ∀ x, tangentialDivergence 2 R.carrier X x = fderiv ℝ g x
      ((approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)) :=
    fun x => Submission.idtp_cse_rc_rotation_divergence P 2 R.carrier a e x g
      (hgC.differentiable_one x)
  -- step 7: `μ`-a.e., `Dg(x)(p_{TₓM}(Ax)) = 1_Z(x) φ(x)`
  have hpt : ∀ᵐ x ∂R.measure, fderiv ℝ g x
      ((approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)) =
        Z.indicator φ x := by
    filter_upwards [htan, hgap] with x hx hgx
    -- (a) `⟨x, p(Ax)⟩ = ⟨p x, Ax⟩ = ⟨x, Ax⟩ = 0` (radial tangency, `p` self-adjoint)
    have hxv : inner ℝ x (inner ℝ x a • e - inner ℝ x e • a) = (0 : ℝ) := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]
      ring
    have hxpv : inner ℝ x ((approxTangentPlane 2 R.carrier x).starProjection
        (inner ℝ x a • e - inner ℝ x e • a)) = (0 : ℝ) := by
      rw [← Submodule.inner_starProjection_left_eq_right, hx, hxv]
    -- (c) `⟨Ax, p(Ax)⟩ = |p(Ax)|²` (`p` idempotent and self-adjoint)
    have hvpv : inner ℝ (inner ℝ x a • e - inner ℝ x e • a)
        ((approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a)) =
          ‖(approxTangentPlane 2 R.carrier x).starProjection
            (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 := by
      have h1 := Submodule.starProjection_inner_eq_zero (K := approxTangentPlane 2 R.carrier x)
        (inner ℝ x a • e - inner ℝ x e • a)
        ((approxTangentPlane 2 R.carrier x).starProjection (inner ℝ x a • e - inner ℝ x e • a))
        (Submodule.starProjection_apply_mem _ _)
      rw [inner_sub_left, real_inner_self_eq_norm_sq] at h1
      linarith
    -- (b) on and off `Z`, the derivative formulas of the test function
    by_cases hxZ : x ∈ Z
    · rw [Set.indicator_of_mem hxZ, hgZ x _ hxpv hgx hxZ, hvpv]
    · rw [Set.indicator_of_notMem hxZ, hgZc x _ hxpv hgx hxZ]
  -- `μ = θ H²⌞M` with `θ` measurable: the identity holds `H²⌞M`-a.e. after multiplying by `θ`
  have hae2 : ∀ᵐ x ∂(μHE[2].restrict R.carrier),
      (R.mult x : ℝ) * tangentialDivergence 2 R.carrier X x = (R.mult x : ℝ) * Z.indicator φ x := by
    filter_upwards [(ae_withDensity_iff hmult).1 hpt] with x hx
    rcases eq_or_ne (R.mult x) 0 with h0 | h0
    · simp [h0]
    · rw [hdiv x, hx (by exact_mod_cast h0)]
  -- step 8: `∫_Z φ dμ = ∫ 1_Z φ dμ = ∫_M θ div_M X dH² = δV(X) = 0`
  have hint : ∫ x in Z, φ x ∂R.measure = 0 := by
    have h1 : ∫ x, Z.indicator φ x ∂R.measure =
        ∫ x in R.carrier, (R.mult x : ℝ) * Z.indicator φ x ∂μHE[2] := by
      rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hmult
        (ae_of_all _ fun x => ENNReal.natCast_lt_top (R.mult x))]
      simp only [ENNReal.toReal_natCast, smul_eq_mul]
    calc ∫ x in Z, φ x ∂R.measure = ∫ x, Z.indicator φ x ∂R.measure :=
          (integral_indicator hZm).symm
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * Z.indicator φ x ∂μHE[2] := h1
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * tangentialDivergence 2 R.carrier X x ∂μHE[2] :=
          integral_congr_ae (hae2.mono fun x hx => hx.symm)
      _ = R.firstVariation X := rfl
      _ = 0 := hstat X hXC hXc
  -- step 8, integrability: `φ` is `μ`-a.e. strongly measurable, bounded on `Z`, and `μ(Z) < ∞`
  have hπA : ∀ x : Euclid P,
      ‖inner ℝ x a • e - inner ℝ x e • a‖ ^ 2 = ‖Q.starProjection x‖ ^ 2 := by
    intro x
    have haa : inner ℝ a a = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hna, one_pow]
    have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hne, one_pow]
    have hea : inner ℝ e a = (0 : ℝ) := by rw [real_inner_comm, hae]
    rw [hπ x, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, haa,
      hee, hae, hea]
    ring
  have hφm : AEStronglyMeasurable φ R.measure := by
    have hpA : AEStronglyMeasurable (fun x => (approxTangentPlane 2 R.carrier x).starProjection
        (inner ℝ x a • e - inner ℝ x e • a)) R.measure :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : Euclid P →L[ℝ] Euclid P) (v : Euclid P) => L v)
        (continuous_fst.clm_apply continuous_snd)
        ((haesm 2 R).mono_ac (withDensity_absolutelyContinuous _ _))
        hAC.continuous.aestronglyMeasurable
    exact ((((hψ.continuous_deriv le_rfl).measurable.comp hfm).aemeasurable.mul
      (hl.continuous.comp continuous_norm).measurable.aemeasurable).mul
      ((hpA.aemeasurable.norm.pow_const 2).div
        (Q.starProjection.continuous.norm.pow 2).measurable.aemeasurable)).aestronglyMeasurable
  obtain ⟨Cψ, hCψ⟩ := (isCompact_Icc : IsCompact (Icc (-s) s)).exists_bound_of_continuousOn
    (hψ.continuous_deriv le_rfl).continuousOn
  obtain ⟨Cl, hCl⟩ := (isCompact_Icc : IsCompact (Icc (1 - s) (1 + s))).exists_bound_of_continuousOn
    hl.continuous.continuousOn
  have hbound : ∀ x ∈ Z, ‖φ x‖ ≤ Cψ * Cl := by
    intro x hx
    obtain ⟨-, hx1, hfx, -⟩ := hx
    obtain ⟨hf1, hf2⟩ := abs_lt.1 hfx
    obtain ⟨hn1, hn2⟩ := abs_lt.1 hx1
    have h1 := hCψ _ ⟨hf1.le, hf2.le⟩
    have h2 := hCl ‖x‖ ⟨by linarith, by linarith⟩
    -- `0 ≤ |p(Ax)|² / |πx|² ≤ 1`, as `|p(Ax)| ≤ |Ax|` and `|Ax| = |πx|`
    have h3 : ‖‖(approxTangentPlane 2 R.carrier x).starProjection
        (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (by positivity), ← hπA x]
      exact div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _)
        (Submodule.norm_starProjection_apply_le _ _) 2) (sq_nonneg _)
    have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans h1
    have hCl0 : 0 ≤ Cl := (norm_nonneg _).trans h2
    calc ‖φ x‖ = ‖deriv ψ (Real.arctan (inner ℝ x e / inner ℝ x a))‖ * ‖l ‖x‖‖ *
          ‖‖(approxTangentPlane 2 R.carrier x).starProjection
            (inner ℝ x a • e - inner ℝ x e • a)‖ ^ 2 / ‖Q.starProjection x‖ ^ 2‖ := by
          simp only [hφ, norm_mul]
      _ ≤ Cψ * Cl * 1 :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hCψ0) h3 (norm_nonneg _)
            (mul_nonneg hCψ0 hCl0)
      _ = Cψ * Cl := mul_one _
  -- `Z ⊆ B̄₂(0)` and `μ(B̄₂(0)) = ∫_{M ∩ B̄₂(0)} θ dH² < ∞`
  have hfin : R.measure Z ≠ ∞ := by
    have hZb : Z ⊆ closedBall (0 : Euclid P) 2 := by
      intro x hx
      obtain ⟨-, hx1, -, -⟩ := hx
      rw [mem_closedBall_zero_iff]
      linarith [(abs_lt.1 hx1).2]
    refine ne_top_of_le_ne_top ?_ (measure_mono hZb)
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, Set.inter_comm]
    exact R.locallyIntegrable_mult _ (isCompact_closedBall _ _) (subset_univ _)
  exact ⟨Measure.integrableOn_of_bounded hfin hφm (ae_restrict_of_forall_mem hZm hbound), hint⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
