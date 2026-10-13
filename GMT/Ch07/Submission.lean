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

/-- Orientation normal form (Simon Ch. 6, 1.1 and 2.2; step 1 of the graph chart in Ch. 7, §5):
a unit orientation `ξ = ±τ₀ ∧ ⋯ ∧ τₘ` of `Q` equals `ι(e₀) ∧ ⋯ ∧ ι(eₘ)` for a linear isometry
`ι : ℝ^{m+1} → ℝᴾ` with range `Q`.  If the sign is `−`, replace `τ₀` by `−τ₀`: the family stays
orthonormal with the same span, and `α(τ') = −α(τ)` by linearity of `α` in slot `0`.  Then `ι` is
the linear map `eᵢ ↦ τ'ᵢ`; it sends the standard orthonormal basis to an orthonormal family, so it
is an isometry, and its range is `span τ' = Q`. -/
theorem Submission.codim1_rdo_gc_unitOrientation_isometry : ∀ (P m : ℕ) (ξ : MultiVector P (m + 1)) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ∃ ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid P, Set.range ι = (Q : Set (Euclid P)) ∧ ∀ α : Covector (Euclid P) (m + 1), ξ α = α (fun i => ι (EuclideanSpace.single i 1)) := by
  intro P m ξ Q ⟨τ, hτ, hspan, hsign⟩
  -- normalize the sign: an orthonormal `τ'` spanning `Q` with `ξ(α) = α(τ')`
  obtain ⟨τ', hτ', hspan', hξ'⟩ : ∃ τ' : Fin (m + 1) → Euclid P, Orthonormal ℝ τ' ∧
      Submodule.span ℝ (Set.range τ') = Q ∧ ∀ α : Covector (Euclid P) (m + 1), ξ α = α τ' := by
    rcases hsign with h | h
    · exact ⟨τ, hτ, hspan, h⟩
    · -- `τ' = update τ 0 (−τ₀)`
      refine ⟨Function.update τ 0 ((-1 : ℝ) • τ 0), ?_, ?_, ?_⟩
      · rw [orthonormal_iff_ite] at hτ ⊢
        intro i j
        rcases eq_or_ne i 0 with rfl | hi <;> rcases eq_or_ne j 0 with rfl | hj
        · simp only [Function.update_self, inner_smul_left, inner_smul_right, hτ 0 0]
          norm_num
        · simp [Function.update_of_ne hj, hτ 0 j, hj.symm]
        · simp [hτ i 0, hi]
        · simp only [Function.update_of_ne hi, Function.update_of_ne hj, hτ i j]
      · rw [← hspan]
        apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          rcases eq_or_ne i 0 with rfl | hi
          · simp only [Function.update_self]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
          · rw [Function.update_of_ne hi]; exact Submodule.subset_span ⟨i, rfl⟩
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          rcases eq_or_ne i 0 with rfl | hi
          · have h0 : Function.update τ 0 ((-1 : ℝ) • τ 0) 0 ∈
                Submodule.span ℝ (Set.range (Function.update τ 0 ((-1 : ℝ) • τ 0))) :=
              Submodule.subset_span ⟨0, rfl⟩
            have h1 := Submodule.smul_mem _ (-1 : ℝ) h0
            simpa using h1
          · have h0 : Function.update τ 0 ((-1 : ℝ) • τ 0) i ∈
                Submodule.span ℝ (Set.range (Function.update τ 0 ((-1 : ℝ) • τ 0))) :=
              Submodule.subset_span ⟨i, rfl⟩
            rwa [Function.update_of_ne hi] at h0
      · intro α
        rw [h α, α.map_update_smul, Function.update_eq_self]
        simp
  -- `ι` is the linear map `eᵢ ↦ τ'ᵢ`, an isometry since it maps an orthonormal basis to `τ'`
  let B := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let f : Euclid (m + 1) →ₗ[ℝ] Euclid P := B.toBasis.constr ℝ τ'
  have hfB : ∀ i, f (B i) = τ' i := fun i => by
    have := B.toBasis.constr_basis ℝ τ' i
    rwa [OrthonormalBasis.coe_toBasis] at this
  have hf : Orthonormal ℝ (f ∘ B.toBasis) := by
    convert hτ' using 1; funext i; exact hfB i
  let ι := f.isometryOfOrthonormal (v := B.toBasis) (by simp [B.orthonormal]) hf
  refine ⟨ι, ?_, ?_⟩
  · -- `range ι = span τ' = Q`
    have : Set.range ι = Set.range f := rfl
    rw [this, ← LinearMap.coe_range, ← hspan']
    congr 1
    rw [Module.Basis.constr_range]
  · -- `ξ(α) = α(τ') = α(ι e₀, …, ι eₘ)`
    intro α
    rw [hξ' α]
    congr 1
    funext i
    have : (EuclideanSpace.single i 1 : Euclid (m + 1)) = B i := by simp [B]
    rw [this]
    exact (hfB i).symm
/-- **`C²` inverse function theorem with a `C²` inverse on a neighbourhood** (graph chart of
`N ∈ 𝒪` over its tangent plane, step 4: `φ : V₀ → O` is bijective with `C²` inverse).  If
`φ : ℝᵈ → ℝᵈ` is `C²` on an open `V ∋ z₀` and `Dφ(z₀)` is injective, there are open sets `V₀`, `O`
with `z₀ ∈ V₀ ⊆ V` such that `φ : V₀ → O` is a bijection whose inverse `g` is `C²` on `O`.
`Dφ` is continuous on `V`, so `V' = {z ∈ V : Dφ(z) injective}` is open; the strict-derivative
inverse function theorem gives an open partial homeomorphism `Φ = φ` with `z₀ ∈ Φ.source`; take
`V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀` and `g = Φ.symm`, which is `C²` at every
`y ∈ O` because `Dφ(g y)` is invertible. -/
theorem Submission.codim1_rdo_gc_local_inverse_c2 : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 2 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (g : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 2 g O ∧ MapsTo g O V₀ ∧ (∀ y ∈ O, φ (g y) = y) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ g (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  -- step 1: `φ` is `C²` and differentiable at every point of `V`, and `Dφ` is continuous on `V`
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV (by norm_num)
  have hdiff : ∀ z ∈ V, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hφ.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  -- step 2: an injective endomorphism of `ℝᵈ` is a continuous linear equivalence
  have equivOf : ∀ L : Euclid d →L[ℝ] Euclid d, Injective L →
      ∃ E : Euclid d ≃L[ℝ] Euclid d, (E : Euclid d →L[ℝ] Euclid d) = L := by
    intro L hL
    have hsurj : Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨(LinearEquiv.ofBijective (L : Euclid d →ₗ[ℝ] Euclid d)
      ⟨hL, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  -- step 3: `V' = {z ∈ V : Dφ(z) injective}` is open and contains `z₀`
  set V' := V ∩ (fderiv ℝ φ) ⁻¹' {L | Injective L} with hV'eq
  have hV' : IsOpen V' := hcont.isOpen_inter_preimage hV ContinuousLinearMap.isOpen_injective
  have hz₀' : z₀ ∈ V' := ⟨hz₀, hinj⟩
  -- step 4: the inverse function theorem at `z₀` gives `Φ = φ` with `z₀ ∈ Φ.source`
  obtain ⟨E₀, hE₀⟩ := equivOf _ hinj
  have hstrict : HasStrictFDerivAt φ (E₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hE₀]; exact (hφ.contDiffAt (hV.mem_nhds hz₀)).hasStrictFDerivAt (by norm_num)
  set Φ := hstrict.toOpenPartialHomeomorph φ with hΦeq
  have hΦcoe : ∀ z, Φ z = φ z := fun z => rfl
  -- steps 5–6: `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀`, `g = Φ.symm`; for `y ∈ O`,
  -- `g y ∈ V₀` and `φ (g y) = y`
  have hV₀ : IsOpen (Φ.source ∩ V') := Φ.open_source.inter hV'
  refine ⟨Φ.source ∩ V', Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ V'), Φ.symm, hV₀,
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV₀,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀'⟩, fun z hz => hz.2.1, ?_,
    fun y hy => hy.2, fun y hy => by rw [← hΦcoe]; exact Φ.right_inv hy.1, fun z hz => ?_⟩
  -- step 7: `g` is `C²` at every `y ∈ O`, since `Dφ(g y)` is invertible
  · intro y hy
    have hz : Φ.symm y ∈ V' := hy.2.2
    obtain ⟨E, hE⟩ := equivOf _ hz.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ.contDiffAt_symm hy.1
    · rw [hE]; exact hdiff _ hz.1
    · exact hφ.contDiffAt (hV.mem_nhds hz.1)
  -- step 6(b): for `z ∈ V₀`, `φ z ∈ O` and `g (φ z) = z`
  · have h1 : Φ.symm (Φ z) = z := Φ.left_inv hz.1
    rw [← hΦcoe]
    exact ⟨⟨Φ.map_source hz.1, by rw [Set.mem_preimage, h1]; exact hz⟩, h1⟩
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

/-- **Graph over the tangent plane** (Simon Ch. 2, §4).  Let `N` be an embedded `C²`
`d`-submanifold, `x ∈ N ∩ U` with `U` open, and `ι : ℝᵈ → ℝᴾ` a linear isometry onto `T_xN`.
Then `B̄_{δ₁+δ₂}(x) ⊆ U` and over `B_{δ₁}(0)` the set `N` is the graph `v ↦ x + ιv + u(v)` of a
`C²` map `u ⊥ ι(ℝᵈ)` with `u(0) = 0`, `Du(0) = 0`, `‖Du‖ ≤ 1` and `‖u‖ < δ₂/2`; a point
`x + ιv + h ∈ N` with `|v| < δ₁`, `|h| < δ₂` and `h ⊥ ι(ℝᵈ)` has `h = u(v)`.
For a chart `ψ` with `ψ(z₀) = x`, `Dψ(z₀)(ℝᵈ) = T_xN = ι(ℝᵈ)` and `ψ⁻¹` is continuous at `x`
(`dsmc_chart_tangentSpace_eq_range`), so `φ = ι*(ψ − x)` has injective derivative `ι*Dψ(z₀)` at
`z₀` and a `C²` local inverse `g : O → V₀` (`codim1_rdo_gc_local_inverse_c2`).  Put
`u(v) = ψ(g(v)) − x − ιv`.  Then `ι*u = 0` on `O`, and `Du(0)` maps into `ι(ℝᵈ)` and is orthogonal
to it, so `Du(0) = 0`.  Near `x`, `N` lies in `ψ(V₀)`, and `x + ιv + h = ψ(z)` gives `φ(z) = v`,
so `z = g(v)` and `h = u(v)`. -/
theorem Submission.codim1_rdo_gc_graph_over_tangent : ∀ (P d : ℕ) (U N : Set (Euclid P)) (x : Euclid P) (ι : Euclid d →ₗᵢ[ℝ] Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → x ∈ N ∩ U → Set.range ι = tangentSpace N x → ∃ (u : Euclid d → Euclid P) (δ₁ δ₂ : ℝ), 0 < δ₁ ∧ 0 < δ₂ ∧ closedBall x (δ₁ + δ₂) ⊆ U ∧ u 0 = 0 ∧ fderiv ℝ u 0 = 0 ∧ ContDiffOn ℝ 2 u (ball 0 δ₁) ∧ (∀ v ∈ ball (0 : Euclid d) δ₁, (∀ w : Euclid d, inner ℝ (ι w) (u v) = 0) ∧ ‖fderiv ℝ u v‖ ≤ 1 ∧ ‖u v‖ < δ₂ / 2 ∧ x + ι v + u v ∈ N) ∧ ∀ (v : Euclid d) (h : Euclid P), ‖v‖ < δ₁ → ‖h‖ < δ₂ → (∀ w : Euclid d, inner ℝ (ι w) h = 0) → x + ι v + h ∈ N → h = u v := by
  intro P d U N x ι hU hN hx hι
  -- a chart `ψ` with `ψ(z₀) = x`: `Dψ(z₀)(ℝᵈ) = T_xN = ι(ℝᵈ)` and `ψ⁻¹` is continuous at `x`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hψinj, hψimg, hprop, hDψ⟩ := hN x hx.1
  obtain ⟨z₀, hz₀V, hψz₀⟩ : x ∈ ψ '' V := by rw [hψimg]; exact ⟨hxW, hx.1⟩
  obtain ⟨htan, hinvc, -⟩ := Submission.dsmc_chart_tangentSpace_eq_range P 2 d N V W ψ
    (by norm_num) hV hW hψ hψinj hψimg hprop hDψ z₀ hz₀V
  rw [hψz₀] at htan hinvc
  have hrangeψ : Set.range (fderiv ℝ ψ z₀) = Set.range ι := by rw [← htan, hι]
  have hψ2 : ContDiffOn ℝ 2 ψ V := by exact_mod_cast hψ
  -- the adjoint `ι*`: `⟨ιw, h⟩ = ⟨w, ι*h⟩`, `ι*ι = 1`, and `ι*h = 0` if `h ⊥ ι(ℝᵈ)`
  set ιs : Euclid P →L[ℝ] Euclid d := ι.toContinuousLinearMap.adjoint with hιs
  have hadj : ∀ w h, inner ℝ (ι w) h = inner ℝ w (ιs h) := fun w h => by
    rw [hιs, ContinuousLinearMap.adjoint_inner_right]; rfl
  have hιsι : ∀ w, ιs (ι w) = w := by
    intro w
    apply ext_inner_left ℝ
    intro w'
    rw [← hadj, LinearIsometry.inner_map_map]
  have hιs0 : ∀ h, (∀ w, inner ℝ (ι w) h = 0) → ιs h = 0 := by
    intro h hh
    apply ext_inner_left ℝ
    intro w
    rw [← hadj, hh w, inner_zero_right]
  -- `φ = ι*(ψ − x)` is `C²` on `V`, with injective derivative `ι*Dψ(z₀)` at `z₀`
  have hψdiff : ∀ z ∈ V, HasFDerivAt ψ (fderiv ℝ ψ z) z := fun z hz =>
    ((hψ2.contDiffAt (hV.mem_nhds hz)).differentiableAt (by norm_num)).hasFDerivAt
  let φ : Euclid d → Euclid d := fun z => ιs (ψ z - x)
  have hφ : ContDiffOn ℝ 2 φ V := ιs.contDiff.comp_contDiffOn (hψ2.sub contDiffOn_const)
  have hφderiv : HasFDerivAt φ (ιs.comp (fderiv ℝ ψ z₀)) z₀ :=
    ιs.hasFDerivAt.comp z₀ ((hψdiff z₀ hz₀V).sub_const x)
  have hφinj : Injective (fderiv ℝ φ z₀) := by
    rw [hφderiv.fderiv]
    intro a₁ a₂ h
    have h1 : ιs (fderiv ℝ ψ z₀ (a₁ - a₂)) = 0 := by
      have h' : ιs (fderiv ℝ ψ z₀ a₁) = ιs (fderiv ℝ ψ z₀ a₂) := h
      rw [map_sub, map_sub, h', sub_self]
    obtain ⟨w, hw⟩ : fderiv ℝ ψ z₀ (a₁ - a₂) ∈ Set.range ι := hrangeψ ▸ ⟨a₁ - a₂, rfl⟩
    rw [← hw, hιsι] at h1
    have h2 : fderiv ℝ ψ z₀ (a₁ - a₂) = fderiv ℝ ψ z₀ 0 := by rw [← hw, h1, map_zero, map_zero]
    exact sub_eq_zero.mp (hDψ z₀ hz₀V h2)
  -- the `C²` local inverse `g : O → V₀` of `φ`; `φ(z₀) = 0`, so `0 ∈ O` and `g(0) = z₀`
  obtain ⟨V₀, O, g, hV₀, hO, hz₀V₀, hV₀V, hg, hgmaps, hφg, hgφ⟩ :=
    Submission.codim1_rdo_gc_local_inverse_c2 d φ V z₀ hV hz₀V hφ hφinj
  have hφz₀ : φ z₀ = 0 := by simp [φ, hψz₀]
  obtain ⟨h0O, hg0⟩ := hgφ z₀ hz₀V₀
  rw [hφz₀] at h0O hg0
  -- the graph map `u(v) = ψ(g(v)) − x − ιv`: on `O` it is `C²`, `ι*u = 0` and `x + ιv + u(v) ∈ N`
  let u : Euclid d → Euclid P := fun v => ψ (g v) - x - ι v
  have hGu : ∀ v, x + ι v + u v = ψ (g v) := fun v => by simp only [u]; abel
  have hu0 : u 0 = 0 := by simp [u, hg0, hψz₀]
  have hgV : MapsTo g O V := fun y hy => hV₀V (hgmaps hy)
  have huC2 : ContDiffOn ℝ 2 u O :=
    ((hψ2.comp hg hgV).sub contDiffOn_const).sub ι.toContinuousLinearMap.contDiff.contDiffOn
  have hιsu : ∀ v ∈ O, ιs (u v) = 0 := by
    intro v hv
    have h1 : ιs (ψ (g v) - x) = v := hφg v hv
    simp only [u, map_sub, hιsι]
    rw [← map_sub, h1, sub_self]
  have horthO : ∀ v ∈ O, ∀ w, inner ℝ (ι w) (u v) = 0 := by
    intro v hv w
    rw [hadj, hιsu v hv, inner_zero_right]
  have hmemO : ∀ v ∈ O, x + ι v + u v ∈ N := fun v hv => by
    rw [hGu]
    have h1 : ψ (g v) ∈ ψ '' V := ⟨g v, hgV hv, rfl⟩
    rw [hψimg] at h1
    exact h1.2
  have hudiff : ∀ v ∈ O, HasFDerivAt u (fderiv ℝ u v) v := fun v hv =>
    ((huC2.contDiffAt (hO.mem_nhds hv)).differentiableAt (by norm_num)).hasFDerivAt
  -- `Du(0) = 0`: every `Du(0)c` lies in `ι(ℝᵈ)` and is orthogonal to `ι(ℝᵈ)`
  have hDu0 : fderiv ℝ u 0 = 0 := by
    have hgdiff : HasFDerivAt g (fderiv ℝ g 0) 0 :=
      ((hg.contDiffAt (hO.mem_nhds h0O)).differentiableAt (by norm_num)).hasFDerivAt
    have hψg : HasFDerivAt (fun v => ψ (g v)) ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0)) 0 := by
      have h' : HasFDerivAt ψ (fderiv ℝ ψ z₀) (g 0) := by rw [hg0]; exact hψdiff z₀ hz₀V
      exact h'.comp 0 hgdiff
    have huder : HasFDerivAt u ((fderiv ℝ ψ z₀).comp (fderiv ℝ g 0) - ι.toContinuousLinearMap) 0 :=
      (hψg.sub_const x).sub ι.toContinuousLinearMap.hasFDerivAt
    ext1 c
    -- `⟨ιw, Du(0)c⟩ = 0`: differentiate `⟨ιw, u⟩ = 0` on the neighbourhood `O` of `0`
    have horthD : ∀ w, inner ℝ (ι w) (fderiv ℝ u 0 c) = 0 := by
      intro w
      have hloc : (fun v' => inner ℝ (ι w) (u v')) =ᶠ[𝓝 0] fun _ => (0 : ℝ) :=
        Filter.eventually_of_mem (hO.mem_nhds h0O) (fun v' hv' => horthO v' hv' w)
      have hd : HasFDerivAt (fun v' => inner ℝ (ι w) (u v'))
          ((innerSL ℝ (ι w)).comp (fderiv ℝ u 0)) 0 :=
        (innerSL ℝ (ι w)).hasFDerivAt.comp 0 (hudiff 0 h0O)
      have hd0 : HasFDerivAt (fun v' => inner ℝ (ι w) (u v')) (0 : Euclid d →L[ℝ] ℝ) 0 :=
        (hasFDerivAt_const (0 : ℝ) 0).congr_of_eventuallyEq hloc
      have h2 := congrArg (fun L => L c) (hd.unique hd0)
      simpa using h2
    -- `Du(0)c = Dψ(z₀)(Dg(0)c) − ιc = ι(w₁ − c)` with `Dψ(z₀)(Dg(0)c) = ιw₁`
    obtain ⟨w₁, hw₁⟩ : fderiv ℝ ψ z₀ (fderiv ℝ g 0 c) ∈ Set.range ι :=
      hrangeψ ▸ ⟨fderiv ℝ g 0 c, rfl⟩
    have hDuc : fderiv ℝ u 0 c = ι (w₁ - c) := by
      rw [huder.fderiv, map_sub]
      simp [hw₁]
    have h3 := horthD (w₁ - c)
    rw [← hDuc, real_inner_self_eq_norm_sq] at h3
    simpa using h3
  -- `N ∩ B_s(x) ⊆ ψ(V₀)`, by continuity of `ψ⁻¹` at `x`; also `B_s(x) ⊆ W ∩ U`
  obtain ⟨ε, hε, hballV₀⟩ := Metric.isOpen_iff.mp hV₀ z₀ hz₀V₀
  obtain ⟨δC, hδC, hδCprop⟩ := hinvc ε hε
  obtain ⟨ρW, hρW, hballW⟩ := Metric.isOpen_iff.mp hW x hxW
  obtain ⟨ρU, hρU, hballU⟩ := Metric.isOpen_iff.mp hU x hx.2
  set s := min (min ρW δC) ρU with hs
  have hspos : 0 < s := lt_min (lt_min hρW hδC) hρU
  have hNball : ∀ q ∈ N, dist q x < s → ∃ z ∈ V₀, ψ z = q := by
    intro q hq hqx
    have hqW : q ∈ W :=
      hballW (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_left _ _)))
    obtain ⟨z, hzV, rfl⟩ : q ∈ ψ '' V := by rw [hψimg]; exact ⟨hqW, hq⟩
    have h1 := hδCprop z hzV (lt_of_lt_of_le hqx (le_trans (min_le_left _ _) (min_le_right _ _)))
    exact ⟨z, hballV₀ h1, rfl⟩
  -- `δ₂ = s/4`, and `δ₁ ≤ δ₂` so small that `B_{δ₁}(0) ⊆ O`, `‖u‖ < δ₂/2`, `‖Du‖ < 1` there
  set r₁ := s / 4 with hr₁eq
  have hr₁ : 0 < r₁ := by positivity
  have hucont : ContinuousAt u 0 := huC2.continuousOn.continuousAt (hO.mem_nhds h0O)
  have hDucont : ContinuousAt (fderiv ℝ u) 0 :=
    (huC2.continuousOn_fderiv_of_isOpen hO (by norm_num)).continuousAt (hO.mem_nhds h0O)
  obtain ⟨ρ₁, hρ₁, hρ₁prop⟩ := Metric.continuousAt_iff.mp hucont (r₁ / 2) (by positivity)
  obtain ⟨ρ₂, hρ₂, hρ₂prop⟩ := Metric.continuousAt_iff.mp hDucont 1 one_pos
  obtain ⟨ρ₃, hρ₃, hρ₃O⟩ := Metric.isOpen_iff.mp hO 0 h0O
  set δ₁ := min (min (min ρ₁ ρ₂) ρ₃) r₁ with hδ₁eq
  have hδ₁pos : 0 < δ₁ := lt_min (lt_min (lt_min hρ₁ hρ₂) hρ₃) hr₁
  have hδ₁ρ₁ : δ₁ ≤ ρ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hδ₁ρ₂ : δ₁ ≤ ρ₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδ₁ρ₃ : δ₁ ≤ ρ₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₁r₁ : δ₁ ≤ r₁ := min_le_right _ _
  have hballO : ball (0 : Euclid d) δ₁ ⊆ O := (ball_subset_ball hδ₁ρ₃).trans hρ₃O
  refine ⟨u, δ₁, r₁, hδ₁pos, hr₁, ?_, hu0, hDu0, huC2.mono hballO, ?_, ?_⟩
  · -- `B̄_{δ₁+δ₂}(x) ⊆ B_s(x) ⊆ U`
    intro q hq
    apply hballU
    rw [mem_closedBall] at hq
    rw [mem_ball]
    have : s ≤ ρU := min_le_right _ _
    linarith
  · intro v hv
    have hvO := hballO hv
    have hv0 : dist v 0 < δ₁ := hv
    refine ⟨horthO v hvO, ?_, ?_, hmemO v hvO⟩
    · have h1 := hρ₂prop (lt_of_lt_of_le hv0 hδ₁ρ₂)
      rw [hDu0, dist_zero_right] at h1
      exact h1.le
    · have h1 := hρ₁prop (lt_of_lt_of_le hv0 hδ₁ρ₁)
      rw [hu0, dist_zero_right] at h1
      exact h1
  · -- uniqueness: `q = x + ιv + h ∈ N ∩ B_s(x)` is `ψ(z)` with `z ∈ V₀` and `φ(z) = v`, so
    -- `z = g(v)` and `x + ιv + u(v) = ψ(g(v)) = q`
    intro v h hv hh horthh hq
    have hvO : v ∈ O := hballO (by rw [mem_ball, dist_zero_right]; exact hv)
    have hqx : dist (x + ι v + h) x < s := by
      rw [dist_eq_norm, show x + ι v + h - x = ι v + h by abel]
      calc ‖ι v + h‖ ≤ ‖ι v‖ + ‖h‖ := norm_add_le _ _
        _ = ‖v‖ + ‖h‖ := by rw [LinearIsometry.norm_map]
        _ < δ₁ + r₁ := add_lt_add hv hh
        _ ≤ r₁ + r₁ := by linarith
        _ < s := by rw [hr₁eq]; linarith
    obtain ⟨z, hzV₀, hψz⟩ := hNball _ hq hqx
    have hφz : φ z = v := by
      show ιs (ψ z - x) = v
      rw [hψz, show x + ι v + h - x = ι v + h by abel, map_add, hιsι, hιs0 h horthh, add_zero]
    have hgz : g v = z := by rw [← hφz]; exact (hgφ z hzV₀).2
    have h1 := hGu v
    rw [hgz, hψz] at h1
    exact (add_left_cancel h1).symm
/-- Steps 3–5 of the orientation push-forward (Simon 6.3.4–3.5, with the orthonormal basis of
`span v` chosen by Gram–Schmidt): a linearly independent family `v` in `ℝᴾ` has an orthonormal
frame `σ` with the same span such that `A = (⟨σᵢ, vⱼ⟩)` satisfies `det(⟨vᵢ, vⱼ⟩) = (det A)²`,
`det A ≠ 0` and `|det A| ≤ ∏ᵢ |vᵢ|`.  Gram–Schmidt in `W = span v` makes `A` the upper-triangular
matrix of `v` in an orthonormal basis of `W`, and Parseval gives `(⟨vᵢ, vⱼ⟩) = AᵀA`. -/
theorem Submission.dpf_exists_orthonormal_frame_det_gram : ∀ (P n : ℕ) (v : Fin n → Euclid P), LinearIndependent ℝ v → ∃ σ : Fin n → Euclid P, Orthonormal ℝ σ ∧ Submodule.span ℝ (Set.range σ) = Submodule.span ℝ (Set.range v) ∧ Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ^ 2 ∧ Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) ≠ 0 ∧ |Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j))| ≤ ∏ i, ‖v i‖ := by
  intro P n v hv
  set W := Submodule.span ℝ (Set.range v)
  -- `v` regarded in `W` is a linearly independent spanning family `w`
  let w : Fin n → W := fun j => ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩
  have hw : LinearIndependent ℝ w := LinearIndependent.of_comp W.subtype hv
  have hspan_w : Submodule.span ℝ (Set.range w) = ⊤ := by
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
    rfl
  -- the Gram–Schmidt orthonormal basis `b` of `W`, and `σ = b` regarded in `ℝᴾ`
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis (finrank_span_eq_card hv) w
  let σ : Fin n → Euclid P := fun i => (b i : Euclid P)
  -- `A` is the (upper-triangular) matrix of `w` in the basis `b`
  have hA : (Matrix.of fun i j => inner ℝ (σ i) (v j)) = b.toBasis.toMatrix w := by
    ext i j
    rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, Submodule.coe_inner]
    rfl
  have hdet : Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (v j)) =
      ∏ i, inner ℝ (σ i) (v i) := by
    rw [hA, ← Module.Basis.det_apply, InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    rfl
  refine ⟨σ, b.orthonormal.comp_linearIsometry W.subtypeₗᵢ, ?_, ?_, ?_, ?_⟩
  · -- `span σ = W`
    have hb : Submodule.span ℝ (Set.range b) = ⊤ := b.toBasis.span_eq
    have hσ : Set.range σ = W.subtype '' Set.range b := Set.range_comp _ _
    rw [hσ, Submodule.span_image, hb, Submodule.map_top, Submodule.range_subtype]
  · -- Parseval: `(⟨vᵢ, vⱼ⟩) = AᵀA`
    have hG : (Matrix.of fun i j => inner ℝ (v i) (v j)) =
        Matrix.transpose (Matrix.of fun i j => inner ℝ (σ i) (v j)) *
          Matrix.of fun i j => inner ℝ (σ i) (v j) := by
      ext i j
      have hp := b.sum_inner_mul_inner (w i) (w j)
      simp only [Submodule.coe_inner] at hp
      rw [Matrix.mul_apply, Matrix.of_apply, ← hp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, real_inner_comm]
    rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
  · -- `det A = det_b w` is a unit
    rw [hA, ← Module.Basis.det_apply]
    exact ((Module.Basis.is_basis_iff_det b.toBasis).mp ⟨hw, hspan_w⟩).ne_zero
  · -- Cauchy–Schwarz on the diagonal entries
    rw [hdet, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    calc |inner ℝ (σ i) (v i)| ≤ ‖σ i‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖v i‖ := by rw [show ‖σ i‖ = 1 from b.norm_eq_one i, one_mul]
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]

/-- Step (6c) of the graph chart in the codimension-one regularity theorem (Simon 7.5.8; unit
orientations as in Simon 6.2.2): for linearly independent `b₁, …, bₘ` in `ℝᴾ` the Gram determinant
`Γ = det(⟨bᵢ, bⱼ⟩)` is positive, and an `m`-vector `ξ` with `⟨α, ξ⟩ √Γ = α(b₁, …, bₘ)` for every
`m`-covector `α` is a unit orientation of `span b`.  For the Gram–Schmidt frame `σ` of `span b` and
`A = (⟨σᵢ, bⱼ⟩)`, `Γ = (det A)²`, `√Γ = |det A|` and `α(b) = det A · α(σ)`, so
`ξ = ±σ₁ ∧ ⋯ ∧ σₘ`. -/
theorem Submission.codim1_rdo_gc_gram_unitOrientation : ∀ (P m : ℕ) (b : Fin m → Euclid P), LinearIndependent ℝ b → 0 < Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) ∧ ∀ ξ : MultiVector P m, (∀ α : Covector (Euclid P) m, ξ α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))) = α b) → IsUnitOrientationOf ξ (Submodule.span ℝ (Set.range b)) := by
  intro P m b hb
  obtain ⟨σ, hσ, hspan, hgram, hA, -⟩ := Submission.dpf_exists_orthonormal_frame_det_gram P m b hb
  set A := Matrix.det (Matrix.of fun i j => inner ℝ (σ i) (b j)) with hAeq
  have hpos : 0 < Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j)) := by
    rw [hgram]; positivity
  refine ⟨hpos, fun ξ hξ => ?_⟩
  have hmem : ∀ j, b j ∈ Submodule.span ℝ (Set.range σ) := fun j => by
    rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcov := Submission.dgoj_covector_eq_det_mul_of_mem_span P m σ b hσ hmem
  have hsqrt : Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (b i) (b j))) = |A| := by
    rw [hgram, Real.sqrt_sq_eq_abs]
  refine ⟨σ, hσ, hspan, ?_⟩
  rcases lt_or_gt_of_ne hA with hneg | hpos'
  · right
    intro α
    have h1 := hξ α
    rw [hsqrt, abs_of_neg hneg, hcov α] at h1
    have h2 : A * ξ α = A * (-α σ) := by linarith
    exact mul_left_cancel₀ hA h2
  · left
    intro α
    have h1 := hξ α
    rw [hsqrt, abs_of_pos hpos', hcov α] at h1
    have h2 : A * ξ α = A * α σ := by linarith
    exact mul_left_cancel₀ hA h2

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
