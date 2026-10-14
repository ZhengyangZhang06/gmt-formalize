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

/-- **Gauss–Green measure** (Simon Ch. 2, 2.1–2.2 and Ch. 3, 4.1, with the Riesz representation
Ch. 1, 4.14): if `φ ↦ ∫_F div φ` is bounded on smooth fields with `|φ| ≤ 1` supported in each
compact `K ⊆ D`, it is `φ ↦ -∫ ⟨φ, ν⟩ dμ` on `C¹` fields compactly supported in `D`, for a measure
`μ` carried by `D`, finite on its compact subsets, and a Borel unit field `ν`.  For each coordinate
`i`, `g ↦ ±∫_F div (g eᵢ)` has positive part `f ↦ sup {±∫_F div (g eᵢ) : g smooth, 0 ≤ g ≤ f}` on
`C_c(D, ℝ≥0)` (additive by smooth approximation under a continuous ceiling), represented by
Riesz–Markov–Kakutani on the open subspace `D`; the `2(m + 1)` measures are densities against their
sum (Lebesgue decomposition), the density field is normalized and the measure pushed forward to
`ℝ^{m+1}`; `C¹` fields are reached by mollification. -/
theorem Submission.codim1_rdo_dg_gauss_green_measure : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))), IsOpen D → MeasurableSet F → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C) → ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)), μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧ (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
  intro m D F hD hF hbound
  classical
  -- the trace as a continuous linear functional and the functional `T φ = ∫_F div φ`
  obtain ⟨trc, htrc⟩ : ∃ trc : (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ] ℝ, ∀ A,
      trc A = LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid (m + 1))).comp (ContinuousLinearMap.coeLM ℝ)), fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : (Euclid (m + 1) → Euclid (m + 1)) → ℝ,
      ∀ φ, T φ = ∫ y in F, trc (fderiv ℝ φ y) := ⟨_, fun _ => rfl⟩
  have hTeq : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ∫ y in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ φ y : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = T φ := by
    intro φ
    rw [hT]
    simp only [htrc]
  have hbound' : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ,
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → (∀ y, ‖φ y‖ ≤ 1) → T φ ≤ C := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound K hK hKD
    refine ⟨C, fun φ h1 h2 h3 h4 => ?_⟩
    rw [← hTeq φ]
    exact hC φ h1 h2 h3 h4
  suffices H : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ by
    obtain ⟨μ, ν, h1, h2, h3, h4, h5⟩ := H
    exact ⟨μ, ν, h1, h2, h3, h4, fun φ hφ hφc hφD => (hTeq φ).trans (h5 φ hφ hφc hφD)⟩
  -- Step 1: `T` is linear on `C¹` compactly supported fields, and locally bounded
  have hdiv_int : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      Integrable (fun y => trc (fderiv ℝ φ y)) (volume.restrict F) := fun φ hφ hc =>
    ((trc.continuous.comp (hφ.continuous_fderiv one_ne_zero)).integrable_of_hasCompactSupport
      ((hc.fderiv ℝ).comp_left trc.map_zero)).restrict
  have hT_add : ∀ φ ψ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → T (φ + ψ) = T φ + T ψ := by
    intro φ ψ hφ hφc hψ hψc
    simp only [hT]
    rw [← integral_add (hdiv_int φ hφ hφc) (hdiv_int ψ hψ hψc)]
    congr 1; ext y
    rw [fderiv_add (hφ.differentiable one_ne_zero y) (hψ.differentiable one_ne_zero y), map_add]
  have hT_smul : ∀ (c : ℝ) (φ : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 φ →
      T (c • φ) = c * T φ := by
    intro c φ hφ
    simp only [hT]
    rw [← integral_const_mul]
    congr 1; ext y
    rw [fderiv_const_smul (hφ.differentiable one_ne_zero y),
      map_smul, smul_eq_mul]
  have hT0 : T 0 = 0 := by simp [hT]
  have hbd : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ K → ∀ M : ℝ, 0 ≤ M → (∀ y, ‖φ y‖ ≤ M) → |T φ| ≤ C * M := by
    intro K hK hKD
    obtain ⟨C, hC⟩ := hbound' K hK hKD
    have hC0 : 0 ≤ C := by
      simpa [hT0] using hC 0 contDiff_const HasCompactSupport.zero (by simp) (by simp)
    refine ⟨C, hC0, fun φ hφ hφc hφK M hM hφM => ?_⟩
    rcases hM.eq_or_lt with rfl | hMpos
    · have : φ = 0 := funext fun y => norm_le_zero_iff.1 (hφM y)
      simp [this, hT0]
    · have hsm : ContDiff ℝ (⊤ : ℕ∞) (M⁻¹ • φ) := contDiff_const.smul hφ
      have hsK : tsupport (M⁻¹ • φ) ⊆ K :=
        (tsupport_smul_subset_right (fun _ => M⁻¹) φ).trans hφK
      have hsn : ∀ y, ‖(M⁻¹ • φ) y‖ ≤ 1 := fun y => by
        rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hM)]
        calc M⁻¹ * ‖φ y‖ ≤ M⁻¹ * M := by gcongr; exact hφM y
          _ = 1 := inv_mul_cancel₀ hMpos.ne'
      have h1 := hC _ hsm (hφc.smul_left) hsK hsn
      have h2 := hC (-(M⁻¹ • φ)) hsm.neg (hφc.smul_left).neg (by rwa [tsupport_neg]) (fun y => by
        rw [Pi.neg_apply, norm_neg]; exact hsn y)
      rw [hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h1
      rw [show -(M⁻¹ • φ) = (-M⁻¹) • φ by rw [neg_smul],
        hT_smul _ _ (hφ.of_le (by exact_mod_cast le_top))] at h2
      rw [abs_le]
      constructor
      · have := mul_le_mul_of_nonneg_left h2 hM
        rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h1 hM
        rw [← mul_assoc, mul_inv_cancel₀ hMpos.ne'] at this
        linarith
  -- compact subsets of `D` and compact supports on the subtype `D`
  have hsubK : ∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D →
      IsCompact (Subtype.val ⁻¹' K : Set D) := fun K hK hKD =>
    Subtype.isCompact_iff.2 (by rwa [Subtype.image_preimage_coe, inter_eq_right.2 hKD])
  have hcs : ∀ (h : Euclid (m + 1) → ℝ) (K : Set (Euclid (m + 1))), IsCompact K →
      support h ⊆ K → HasCompactSupport h ∧ tsupport h ⊆ K := fun h K hK hhK =>
    ⟨hK.of_isClosed_subset (isClosed_tsupport h) (closure_minimal hhK hK.isClosed),
      closure_minimal hhK hK.isClosed⟩
  -- smooth approximation of `a` under a continuous ceiling `u` (smooth partitions of unity)
  have happrox : ∀ (u a : Euclid (m + 1) → ℝ), Continuous u → Continuous a →
      (∀ z, 0 ≤ a z ∧ a z ≤ u z) → ∀ ε : ℝ, 0 < ε →
      ∃ a' : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) a' ∧
        ∀ z, 0 ≤ a' z ∧ a' z ≤ u z ∧ |a' z - a z| < ε := by
    intro u a hu ha hau ε hε
    have hloc : ∀ y : Euclid (m + 1), ∃ c : ℝ, ∀ᶠ z in 𝓝 y, c ∈ Icc 0 (u z) ∩ ball (a z) ε := by
      intro y
      refine ⟨max 0 (a y - ε / 2), ?_⟩
      have h1 : ∀ᶠ z in 𝓝 y, |a z - a y| < ε / 2 := by
        have := (ha.tendsto y).eventually (ball_mem_nhds (a y) (half_pos hε))
        filter_upwards [this] with z hz
        simpa [Real.dist_eq] using hz
      have h2 : ∀ᶠ z in 𝓝 y, max 0 (a y - ε / 2) ≤ u z := by
        by_cases hay : a y - ε / 2 ≤ 0
        · exact Eventually.of_forall fun z => by
            rw [max_eq_left hay]; exact (hau z).1.trans (hau z).2
        · rw [not_le] at hay
          have hlt : a y - ε / 2 < u y := by linarith [(hau y).2]
          have := (hu.tendsto y).eventually (lt_mem_nhds hlt)
          filter_upwards [this] with z hz
          rw [max_eq_right hay.le]; exact hz.le
      filter_upwards [h1, h2] with z hz1 hz2
      refine ⟨⟨le_max_left _ _, hz2⟩, ?_⟩
      rw [mem_ball, Real.dist_eq]
      have : |max 0 (a y - ε / 2) - a y| ≤ ε / 2 := by
        rcases le_total (a y - ε / 2) 0 with h | h
        · rw [max_eq_left h, zero_sub, abs_neg, abs_of_nonneg (hau y).1]; linarith
        · rw [max_eq_right h]; rw [show a y - ε / 2 - a y = -(ε / 2) by ring, abs_neg,
            abs_of_pos (half_pos hε)]
      calc |max 0 (a y - ε / 2) - a z| ≤ |max 0 (a y - ε / 2) - a y| + |a y - a z| :=
            abs_sub_le _ _ _
        _ < ε / 2 + ε / 2 := by
          have : |a y - a z| < ε / 2 := by rw [abs_sub_comm]; exact hz1
          linarith
        _ = ε := by ring
    obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
      (modelWithCornersSelf ℝ (Euclid (m + 1))) (n := ⊤)
      (t := fun z => Icc 0 (u z) ∩ ball (a z) ε)
      (fun z => (convex_Icc _ _).inter (convex_ball _ _)) hloc
    refine ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z => ?_⟩
    have := hg z
    simp only [mem_inter_iff, mem_Icc, mem_ball, Real.dist_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  -- Step 2: the positive part of a locally bounded functional, via Riesz–Markov–Kakutani on `D`
  have hpos : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ : Measure D, IsFiniteMeasureOnCompacts μ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → (∀ y, 0 ≤ g y) →
          BddAbove (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) ∧
          ∫ x : D, g x ∂μ = sSup (S '' {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
            tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y}) := by
    intro S hSadd hSsmul hSbd
    have hS0 : S 0 = 0 := by simpa using hSsmul 0 0 contDiff_const
    -- `A u`: smooth `h`, `0 ≤ h ≤ u`, compactly supported in `D`; the functional is `sup S(A u)`
    obtain ⟨A, hA⟩ : ∃ A : (Euclid (m + 1) → ℝ) → Set (Euclid (m + 1) → ℝ), ∀ u h, h ∈ A u ↔
        (ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
          ∀ y, 0 ≤ h y ∧ h y ≤ u y) :=
      ⟨fun u => {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ u y}, fun _ _ => Iff.rfl⟩
    have hA0 : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → (0 : Euclid (m + 1) → ℝ) ∈ A u :=
      fun u hu => (hA u 0).2 ⟨contDiff_const, HasCompactSupport.zero, by simp,
        fun y => ⟨le_rfl, hu y⟩⟩
    have hAsupp : ∀ u h, h ∈ A u → support h ⊆ support u := by
      intro u h hh y hy huy
      obtain ⟨-, -, -, h4⟩ := (hA u h).1 hh
      have := h4 y
      rw [huy] at this
      exact hy (le_antisymm this.2 this.1)
    have hbddA : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → BddAbove (S '' A u) := by
      intro u hu hu0 K hK hKD huK
      obtain ⟨C, hC⟩ := hSbd K hK hKD
      obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support (hcs u K hK huK).1
      refine ⟨C * M, ?_⟩
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨h1, h2, -, h4⟩ := (hA u h).1 hh
      refine hC h h1 h2 (hcs h K hK ((hAsupp u h hh).trans huK)).2 M
        ((norm_nonneg _).trans (hM 0)) fun y => ?_
      rw [abs_of_nonneg (h4 y).1]
      exact (h4 y).2.trans ((le_abs_self _).trans (hM y))
    have hle_sup : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ h ∈ A u, S h ≤ sSup (S '' A u) :=
      fun u hu hu0 K hK hKD huK h hh => le_csSup (hbddA u hu hu0 K hK hKD huK) ⟨h, hh, rfl⟩
    have hsup_le : ∀ u : Euclid (m + 1) → ℝ, (∀ y, 0 ≤ u y) → ∀ c : ℝ,
        (∀ h ∈ A u, S h ≤ c) → sSup (S '' A u) ≤ c := fun u hu c hc =>
      csSup_le ⟨S 0, 0, hA0 u hu, rfl⟩ (by rintro _ ⟨h, hh, rfl⟩; exact hc h hh)
    -- additivity
    have hadd : ∀ u₁ u₂ : Euclid (m + 1) → ℝ, Continuous u₁ → (∀ y, 0 ≤ u₁ y) →
        Continuous u₂ → (∀ y, 0 ≤ u₂ y) → ∀ K₁ K₂, IsCompact K₁ → K₁ ⊆ D → support u₁ ⊆ K₁ →
        IsCompact K₂ → K₂ ⊆ D → support u₂ ⊆ K₂ →
        sSup (S '' A (u₁ + u₂)) = sSup (S '' A u₁) + sSup (S '' A u₂) := by
      intro u₁ u₂ hu₁ hu₁0 hu₂ hu₂0 K₁ K₂ hK₁ hK₁D hu₁K hK₂ hK₂D hu₂K
      have hu0 : ∀ y, 0 ≤ (u₁ + u₂) y := fun y => add_nonneg (hu₁0 y) (hu₂0 y)
      have huK : support (u₁ + u₂) ⊆ K₁ ∪ K₂ := fun y hy => by
        by_contra hy'
        apply hy
        have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
        have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
        rw [Pi.add_apply, notMem_support.1 (fun h => hy1 (hu₁K h)),
          notMem_support.1 (fun h => hy2 (hu₂K h)), add_zero]
      have hKK : IsCompact (K₁ ∪ K₂) := hK₁.union hK₂
      have hKKD : K₁ ∪ K₂ ⊆ D := union_subset hK₁D hK₂D
      apply le_antisymm
      · apply hsup_le (u₁ + u₂) hu0
        intro g hg
        obtain ⟨hg1, hg2, hg3, hg4⟩ := (hA (u₁ + u₂) g).1 hg
        obtain ⟨C, hC⟩ := hSbd (K₁ ∪ K₂) hKK hKKD
        apply le_of_forall_pos_le_add
        intro ε hε
        obtain ⟨δ, hδ0, hCδ⟩ : ∃ δ : ℝ, 0 < δ ∧ C * (2 * δ) ≤ ε := by
          refine ⟨ε / (2 * (|C| + 1)), div_pos hε (by positivity), ?_⟩
          have hpos' : (0 : ℝ) < |C| + 1 := by positivity
          have : C * (2 * (ε / (2 * (|C| + 1)))) = C * ε / (|C| + 1) := by
            field_simp
          rw [this, div_le_iff₀ hpos', mul_comm ε]
          exact mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right
            zero_le_one)) hε.le
        have ha : Continuous fun y => min (g y) (u₁ y) := hg1.continuous.min hu₁
        obtain ⟨a', ha'1, ha'2⟩ := happrox u₁ (fun y => min (g y) (u₁ y)) hu₁ ha
          (fun z => ⟨le_min (hg4 z).1 (hu₁0 z), min_le_right _ _⟩) δ hδ0
        have hb : ∀ z, 0 ≤ g z - min (g z) (u₁ z) ∧ g z - min (g z) (u₁ z) ≤ u₂ z := by
          intro z
          refine ⟨sub_nonneg.2 (min_le_left _ _), ?_⟩
          have h' : g z ≤ u₁ z + u₂ z := (hg4 z).2
          rcases le_total (g z) (u₁ z) with h | h
          · rw [min_eq_left h, sub_self]; exact hu₂0 z
          · rw [min_eq_right h]; linarith
        obtain ⟨b', hb'1, hb'2⟩ := happrox u₂ (fun y => g y - min (g y) (u₁ y)) hu₂
          (hg1.continuous.sub ha) hb δ hδ0
        have ha'K : support a' ⊆ K₁ := fun y hy => hu₁K fun h => hy (by
          have := ha'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hb'K : support b' ⊆ K₂ := fun y hy => hu₂K fun h => hy (by
          have := hb'2 y; rw [h] at this; exact le_antisymm this.2.1 this.1)
        have hcsa' := hcs a' K₁ hK₁ ha'K
        have hcsb' := hcs b' K₂ hK₂ hb'K
        have ha'A : a' ∈ A u₁ := (hA u₁ a').2 ⟨ha'1, hcsa'.1, hcsa'.2.trans hK₁D,
          fun z => ⟨(ha'2 z).1, (ha'2 z).2.1⟩⟩
        have hb'A : b' ∈ A u₂ := (hA u₂ b').2 ⟨hb'1, hcsb'.1, hcsb'.2.trans hK₂D,
          fun z => ⟨(hb'2 z).1, (hb'2 z).2.1⟩⟩
        have hgK : support g ⊆ K₁ ∪ K₂ := (hAsupp (u₁ + u₂) g hg).trans huK
        have hrK : support (g - a' - b') ⊆ K₁ ∪ K₂ := fun y hy => by
          by_contra hy'
          apply hy
          have hy1 : y ∉ K₁ := fun h => hy' (Or.inl h)
          have hy2 : y ∉ K₂ := fun h => hy' (Or.inr h)
          rw [Pi.sub_apply, Pi.sub_apply, notMem_support.1 (fun h => hy' (hgK h)),
            notMem_support.1 (fun h => hy1 (ha'K h)), notMem_support.1 (fun h => hy2 (hb'K h)),
            sub_zero, sub_zero]
        have hrcs := hcs (g - a' - b') (K₁ ∪ K₂) hKK hrK
        have hr1 : ContDiff ℝ (⊤ : ℕ∞) (g - a' - b') := (hg1.sub ha'1).sub hb'1
        have hrb : ∀ y, |(g - a' - b') y| ≤ 2 * δ := fun y => by
          have h1 := (ha'2 y).2.2
          have h2 := (hb'2 y).2.2
          rw [Pi.sub_apply, Pi.sub_apply]
          have e : g y - a' y - b' y =
              -((a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))) := by ring
          rw [e, abs_neg]
          calc |(a' y - min (g y) (u₁ y)) + (b' y - (g y - min (g y) (u₁ y)))|
              ≤ |a' y - min (g y) (u₁ y)| + |b' y - (g y - min (g y) (u₁ y))| :=
                abs_add_le _ _
            _ ≤ 2 * δ := by linarith
        have hSr := hC (g - a' - b') hr1 hrcs.1 hrcs.2 (2 * δ) (by positivity) hrb
        have hdec : S ((a' + b') + (g - a' - b')) = S a' + S b' + S (g - a' - b') := by
          rw [hSadd (a' + b') (g - a' - b') (ha'1.add hb'1) (hcsa'.1.add hcsb'.1) hr1 hrcs.1,
            hSadd a' b' ha'1 hcsa'.1 hb'1 hcsb'.1]
        rw [show (a' + b') + (g - a' - b') = g by abel] at hdec
        have h1 := hle_sup u₁ hu₁ hu₁0 K₁ hK₁ hK₁D hu₁K a' ha'A
        have h2 := hle_sup u₂ hu₂ hu₂0 K₂ hK₂ hK₂D hu₂K b' hb'A
        linarith
      · have key : ∀ h₁ ∈ A u₁, ∀ h₂ ∈ A u₂, S h₁ + S h₂ ≤ sSup (S '' A (u₁ + u₂)) := by
          intro h₁ hh₁ h₂ hh₂
          obtain ⟨a1, a2, a3, a4⟩ := (hA u₁ h₁).1 hh₁
          obtain ⟨b1, b2, b3, b4⟩ := (hA u₂ h₂).1 hh₂
          rw [← hSadd h₁ h₂ a1 a2 b1 b2]
          have hmem : h₁ + h₂ ∈ A (u₁ + u₂) := (hA (u₁ + u₂) (h₁ + h₂)).2 ⟨a1.add b1,
            a2.add b2, (tsupport_add h₁ h₂).trans (union_subset a3 b3),
            fun y => ⟨add_nonneg (a4 y).1 (b4 y).1, add_le_add (a4 y).2 (b4 y).2⟩⟩
          exact hle_sup (u₁ + u₂) (hu₁.add hu₂) hu0 (K₁ ∪ K₂) hKK hKKD huK (h₁ + h₂) hmem
        have : sSup (S '' A u₁) ≤ sSup (S '' A (u₁ + u₂)) - sSup (S '' A u₂) := by
          apply hsup_le u₁ hu₁0
          intro h₁ hh₁
          have : sSup (S '' A u₂) ≤ sSup (S '' A (u₁ + u₂)) - S h₁ := by
            apply hsup_le u₂ hu₂0
            intro h₂ hh₂
            have := key h₁ hh₁ h₂ hh₂
            linarith
          linarith
        linarith
    -- homogeneity
    have hsmul : ∀ u : Euclid (m + 1) → ℝ, Continuous u → (∀ y, 0 ≤ u y) →
        ∀ K, IsCompact K → K ⊆ D → support u ⊆ K → ∀ c : ℝ, 0 ≤ c →
        sSup (S '' A (c • u)) = c * sSup (S '' A u) := by
      intro u hu hu0 K hK hKD huK c hc
      have hcu0 : ∀ y, 0 ≤ (c • u) y := fun y => mul_nonneg hc (hu0 y)
      have hcuK : support (c • u) ⊆ K := (support_const_smul_subset c u).trans huK
      have hcuc : Continuous (c • u) := hu.const_smul c
      rcases hc.eq_or_lt with hc0 | hcpos
      · subst hc0
        rw [zero_mul]
        apply le_antisymm
        · apply hsup_le ((0 : ℝ) • u) hcu0
          intro h hh
          obtain ⟨-, -, -, h4⟩ := (hA ((0 : ℝ) • u) h).1 hh
          have : h = 0 := funext fun y => le_antisymm (by
            have := (h4 y).2
            rwa [Pi.smul_apply, zero_smul] at this) (h4 y).1
          rw [this, hS0]
        · have h0 := hle_sup ((0 : ℝ) • u) hcuc hcu0 K hK hKD hcuK 0 (hA0 ((0 : ℝ) • u) hcu0)
          rwa [hS0] at h0
      · apply le_antisymm
        · apply hsup_le (c • u) hcu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA (c • u) h).1 hh
          have hmem : c⁻¹ • h ∈ A u := (hA u (c⁻¹ • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c⁻¹) h2,
            (tsupport_smul_subset_right (fun _ => c⁻¹) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg (inv_nonneg.2 hc) (h4 y).1, by
                rw [Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hcpos]
                have := (h4 y).2
                rwa [Pi.smul_apply, smul_eq_mul] at this⟩⟩
          have := hle_sup u hu hu0 K hK hKD huK (c⁻¹ • h) hmem
          have e : S h = c * S (c⁻¹ • h) := by
            rw [hSsmul c⁻¹ h h1, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
          rw [e]
          exact mul_le_mul_of_nonneg_left this hc
        · rw [← le_div_iff₀' hcpos]
          apply hsup_le u hu0
          intro h hh
          obtain ⟨h1, h2, h3, h4⟩ := (hA u h).1 hh
          have hmem : c • h ∈ A (c • u) := (hA (c • u) (c • h)).2 ⟨contDiff_const.smul h1,
            HasCompactSupport.smul_left (f := fun _ => c) h2,
            (tsupport_smul_subset_right (fun _ => c) h).trans h3, fun y => ⟨by
              rw [Pi.smul_apply, smul_eq_mul]
              exact mul_nonneg hc (h4 y).1, by
                rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
                exact mul_le_mul_of_nonneg_left (h4 y).2 hc⟩⟩
          have := hle_sup (c • u) hcuc hcu0 K hK hKD hcuK (c • h) hmem
          rw [hSsmul c h h1] at this
          rw [le_div_iff₀' hcpos]
          exact this
    -- extension by zero of `f ∈ C_c(D, ℝ≥0)`; `f ↦ sup S(A (ext f))` is `ℝ≥0`-linear
    obtain ⟨ext, hext⟩ : ∃ ext : CompactlySupportedContinuousMap D NNReal →
        Euclid (m + 1) → ℝ, ∀ f y, ext f y = if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0 :=
      ⟨fun f y => if h : y ∈ D then ((f ⟨y, h⟩ : NNReal) : ℝ) else 0, fun _ _ => rfl⟩
    have hextK : ∀ f : CompactlySupportedContinuousMap D NNReal,
        IsCompact (Subtype.val '' tsupport f) ∧ Subtype.val '' tsupport f ⊆ D := fun f =>
      ⟨f.hasCompactSupport.image continuous_subtype_val, by rintro _ ⟨x, -, rfl⟩; exact x.2⟩
    have hext_supp : ∀ f : CompactlySupportedContinuousMap D NNReal,
        support (ext f) ⊆ Subtype.val '' tsupport f := by
      intro f y hy
      rw [mem_support, hext] at hy
      by_cases h : y ∈ D
      · rw [dite_eq_left h] at hy
        refine ⟨⟨y, h⟩, subset_tsupport _ ?_, rfl⟩
        intro h0
        apply hy
        rw [h0]
        rfl
      · rw [dite_eq_right h] at hy
        exact absurd rfl hy
    have hext_nonneg : ∀ f y, 0 ≤ ext f y := by
      intro f y
      rw [hext]
      split_ifs
      · exact NNReal.coe_nonneg _
      · exact le_rfl
    have hext_cont : ∀ f : CompactlySupportedContinuousMap D NNReal, Continuous (ext f) := by
      intro f
      rw [continuous_iff_continuousAt]
      intro y
      by_cases hy : y ∈ Subtype.val '' tsupport f
      · have hyD : y ∈ D := (hextK f).2 hy
        have hcont : ContinuousOn (ext f) D := by
          rw [continuousOn_iff_continuous_domRestrict]
          have : D.domRestrict (ext f) = fun x : D => ((f x : NNReal) : ℝ) := by
            funext x
            rw [Set.domRestrict_apply, hext, dite_eq_left x.2]
          rw [this]
          exact NNReal.continuous_coe.comp f.continuous
        exact hcont.continuousAt (hD.mem_nhds hyD)
      · have : ext f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [(hextK f).1.isClosed.isOpen_compl.mem_nhds hy] with z hz
          by_contra hne
          exact hz (hext_supp f hne)
        exact continuousAt_const.congr this.symm
    have hext_add : ∀ f g : CompactlySupportedContinuousMap D NNReal,
        ext (f + g) = ext f + ext g := by
      intro f g
      funext y
      simp only [hext, Pi.add_apply]
      split_ifs
      · simp
      · simp
    have hext_smul : ∀ (c : NNReal) (f : CompactlySupportedContinuousMap D NNReal),
        ext (c • f) = (c : ℝ) • ext f := by
      intro c f
      funext y
      simp only [hext, Pi.smul_apply]
      split_ifs
      · simp
      · simp
    have hΛ0 : ∀ f : CompactlySupportedContinuousMap D NNReal, 0 ≤ sSup (S '' A (ext f)) :=
      fun f => by
        have := hle_sup (ext f) (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2
          (hext_supp f) 0 (hA0 _ (hext_nonneg f))
        rwa [hS0] at this
    let Λn : CompactlySupportedContinuousMap D NNReal →ₗ[NNReal] NNReal :=
      { toFun := fun f => ⟨sSup (S '' A (ext f)), hΛ0 f⟩
        map_add' := fun f g => by
          apply NNReal.eq
          change sSup (S '' A (ext (f + g))) = sSup (S '' A (ext f)) + sSup (S '' A (ext g))
          rw [hext_add]
          exact hadd _ _ (hext_cont f) (hext_nonneg f) (hext_cont g) (hext_nonneg g) _ _
            (hextK f).1 (hextK f).2 (hext_supp f) (hextK g).1 (hextK g).2 (hext_supp g)
        map_smul' := fun c f => by
          apply NNReal.eq
          change sSup (S '' A (ext (c • f))) = (c : ℝ) * sSup (S '' A (ext f))
          rw [hext_smul]
          exact hsmul _ (hext_cont f) (hext_nonneg f) _ (hextK f).1 (hextK f).2 (hext_supp f)
            c c.2 }
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    refine ⟨RealRMK.rieszMeasure (CompactlySupportedContinuousMap.toRealPositiveLinear Λn),
      inferInstance, ?_⟩
    intro g hg hgc hgD hg0
    have hAg : A g = {h | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ D ∧
        ∀ y, 0 ≤ h y ∧ h y ≤ g y} := by
      ext h
      exact hA g h
    rw [← hAg]
    refine ⟨hbddA g hg.continuous hg0 (tsupport g) hgc hgD (subset_tsupport g), ?_⟩
    have hgcs : HasCompactSupport (fun x : D => Real.toNNReal (g x)) := by
      refine (hsubK _ hgc hgD).of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal ?_ ((isClosed_tsupport g).preimage continuous_subtype_val))
      intro x hx
      apply subset_tsupport g
      intro h0
      apply hx
      simp [h0]
    let fg : CompactlySupportedContinuousMap D NNReal :=
      ⟨⟨fun x => Real.toNNReal (g x),
        continuous_real_toNNReal.comp (hg.continuous.comp continuous_subtype_val)⟩, hgcs⟩
    have hfg : ext fg = g := by
      funext y
      rw [hext]
      by_cases h : y ∈ D
      · rw [dite_eq_left h]
        exact Real.coe_toNNReal _ (hg0 y)
      · rw [dite_eq_right h]
        exact (image_eq_zero_of_notMem_tsupport (fun h' => h (hgD h'))).symm
    calc ∫ x : D, g x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn))
        = ∫ x : D, (CompactlySupportedContinuousMap.toReal fg) x ∂(RealRMK.rieszMeasure
          (CompactlySupportedContinuousMap.toRealPositiveLinear Λn)) := by
          congr 1
          funext x
          rw [CompactlySupportedContinuousMap.toReal_apply]
          exact (Real.coe_toNNReal _ (hg0 x)).symm
      _ = CompactlySupportedContinuousMap.toRealPositiveLinear Λn
          (CompactlySupportedContinuousMap.toReal fg) := RealRMK.integral_rieszMeasure _ _
      _ = (Λn fg : ℝ) := by rw [CompactlySupportedContinuousMap.eq_toRealPositiveLinear_toReal]
      _ = sSup (S '' A (ext fg)) := rfl
      _ = sSup (S '' A g) := by rw [hfg]
  -- Step 3: Jordan decomposition of a locally bounded functional on smooth functions
  have hcsD : ∀ f : Euclid (m + 1) → ℝ, HasCompactSupport f → tsupport f ⊆ D →
      HasCompactSupport (fun x : D => f x) := by
    intro f hfc hfD
    refine (hsubK _ hfc hfD).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal ?_ ((isClosed_tsupport f).preimage continuous_subtype_val))
    intro x hx
    exact subset_tsupport f hx
  have hintD : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ → ∀ f : Euclid (m + 1) → ℝ,
      Continuous f → HasCompactSupport f → tsupport f ⊆ D → Integrable (fun x : D => f x) μ := by
    intro μ hμ f hf hfc hfD
    exact (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport (hcsD f hfc hfD)
  have hjordan : ∀ S : (Euclid (m + 1) → ℝ) → ℝ,
      (∀ g h : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        ContDiff ℝ (⊤ : ℕ∞) h → HasCompactSupport h → S (g + h) = S g + S h) →
      (∀ (c : ℝ) (g : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → S (c • g) = c * S g) →
      (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → ∃ C : ℝ, ∀ g : Euclid (m + 1) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ K → ∀ M : ℝ, 0 ≤ M →
          (∀ y, |g y| ≤ M) → S g ≤ C * M) →
      ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧ IsFiniteMeasureOnCompacts μ₂ ∧
        ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ D → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
    intro S hSadd hSsmul hSbd
    obtain ⟨μ₁, hμ₁, h₁⟩ := hpos S hSadd hSsmul hSbd
    have hSneg : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → S (-g) = -S g :=
      fun g hg => by
        rw [show -g = (-1 : ℝ) • g by rw [neg_one_smul], hSsmul (-1) g hg, neg_one_mul]
    obtain ⟨μ₂, hμ₂, h₂⟩ := hpos (fun g => -S g)
      (fun g h hg hgc hh hhc => by rw [hSadd g h hg hgc hh hhc, neg_add])
      (fun c g hg => by rw [hSsmul c g hg, mul_neg])
      (fun K hK hKD => by
        obtain ⟨C, hC⟩ := hSbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (-g) hg.neg hgc.neg (by rwa [tsupport_neg]) M hM
          (fun y => by rw [Pi.neg_apply, abs_neg]; exact hgM y)
        rwa [hSneg g hg] at this)
    refine ⟨μ₁, μ₂, hμ₁, hμ₂, ?_⟩
    have hnn : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ D → (∀ y, 0 ≤ g y) → S g = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro g hg hgc hgD hg0
      obtain ⟨hb₁, he₁⟩ := h₁ g hg hgc hgD hg0
      obtain ⟨hb₂, he₂⟩ := h₂ g hg hgc hgD hg0
      rw [he₁, he₂]
      set Ag := {h : Euclid (m + 1) → ℝ | ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ D ∧ ∀ y, 0 ≤ h y ∧ h y ≤ g y} with hAg
      have hgA : g ∈ Ag := ⟨hg, hgc, hgD, fun y => ⟨hg0 y, le_rfl⟩⟩
      have hsubA : ∀ h ∈ Ag, g - h ∈ Ag := fun h hh =>
        ⟨hg.sub hh.1, hgc.sub hh.2.1, (tsupport_sub g h).trans (union_subset hgD hh.2.2.1),
          fun y => ⟨sub_nonneg.2 (hh.2.2.2 y).2, sub_le_self _ (hh.2.2.2 y).1⟩⟩
      have hdec : ∀ h ∈ Ag, S g = S (g - h) + S h := fun h hh => by
        rw [← hSadd (g - h) h (hg.sub hh.1) (hgc.sub hh.2.1) hh.1 hh.2.1, sub_add_cancel]
      have hne : Ag.Nonempty := ⟨g, hgA⟩
      have i1 : sSup ((fun g => -S g) '' Ag) ≤ sSup (S '' Ag) - S g := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₁ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      have i2 : sSup (S '' Ag) ≤ S g + sSup ((fun g => -S g) '' Ag) := by
        apply csSup_le (hne.image _)
        rintro _ ⟨h, hh, rfl⟩
        have := le_csSup hb₂ ⟨g - h, hsubA h hh, rfl⟩
        have e := hdec h hh
        linarith
      linarith
    -- a general `g`: add `M χ`, with `|g| ≤ M` and a smooth cutoff `χ = 1` on `tsupport g`
    intro g hg hgc hgD
    obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hgc hD hgD
    obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
      (isOpen_thickening (δ := δ) (E := tsupport g)) (isClosed_tsupport g)
      (self_subset_thickening hδ _)
    have hχK : support χ ⊆ cthickening δ (tsupport g) :=
      hχs ▸ thickening_subset_cthickening δ _
    have hχcs := hcs χ (cthickening δ (tsupport g)) (IsCompact.cthickening hgc) hχK
    obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hχ01 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := fun y => hχr ⟨y, rfl⟩
    have hψ : ContDiff ℝ (⊤ : ℕ∞) (M • χ) := contDiff_const.smul hχ
    have hψcs : HasCompactSupport (M • χ) := HasCompactSupport.smul_left (f := fun _ => M) hχcs.1
    have hψD : tsupport (M • χ) ⊆ D :=
      (tsupport_smul_subset_right (fun _ => M) χ).trans (hχcs.2.trans hδD)
    have hψ0 : ∀ y, 0 ≤ (M • χ) y := fun y => by
      rw [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hM0 (hχ01 y).1
    have hgψ0 : ∀ y, 0 ≤ (g + M • χ) y := fun y => by
      by_cases hy : y ∈ tsupport g
      · rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hχ1 y).1 hy, mul_one]
        have := hM y
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (g y)]
      · rw [Pi.add_apply, image_eq_zero_of_notMem_tsupport hy, zero_add]; exact hψ0 y
    have e1 := hnn (g + M • χ) (hg.add hψ) (hgc.add hψcs)
      ((tsupport_add g (M • χ)).trans (union_subset hgD hψD)) hgψ0
    have e2 := hnn (M • χ) hψ hψcs hψD hψ0
    rw [hSadd g (M • χ) hg hgc hψ hψcs] at e1
    have i1 : ∀ μ : Measure D, IsFiniteMeasureOnCompacts μ →
        ∫ x : D, (g + M • χ) x ∂μ = ∫ x : D, g x ∂μ + ∫ x : D, (M • χ) x ∂μ := by
      intro μ hμ
      simp only [Pi.add_apply]
      exact integral_add (hintD μ hμ g hg.continuous hgc hgD)
        (hintD μ hμ (M • χ) hψ.continuous hψcs hψD)
    rw [i1 μ₁ hμ₁, i1 μ₂ hμ₂] at e1
    linarith
  -- Step 4: representation of `T` on smooth fields
  have hsm_rep : ∃ (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)),
      μ Dᶜ = 0 ∧ (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) ∧ Measurable ν ∧
      (∀ y, ‖ν y‖ = 1) ∧ ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = -∫ y, inner ℝ (φ y) (ν y) ∂μ := by
    -- the standard basis
    obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (m + 1)) ℝ (Euclid (m + 1)),
        b = EuclideanSpace.basisFun (Fin (m + 1)) ℝ := ⟨_, rfl⟩
    have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.norm_eq_one i
    have hbinner : ∀ (x : Euclid (m + 1)) (i : Fin (m + 1)), inner ℝ x (b i) = x i := by
      intro x i; rw [hb]; exact EuclideanSpace.inner_basisFun_real _ x i
    have hbsum : ∀ x : Euclid (m + 1), ∑ i, x i • b i = x := by
      intro x; rw [hb]; exact (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).sum_repr x
    -- coordinate functionals
    have hcomp : ∀ i : Fin (m + 1), ∃ μ₁ μ₂ : Measure D, IsFiniteMeasureOnCompacts μ₁ ∧
        IsFiniteMeasureOnCompacts μ₂ ∧ ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          HasCompactSupport g → tsupport g ⊆ D →
          T (fun y => g y • b i) = ∫ x : D, g x ∂μ₁ - ∫ x : D, g x ∂μ₂ := by
      intro i
      have hsm : ∀ g : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ContDiff ℝ (⊤ : ℕ∞) (fun y => g y • b i) := fun g hg => hg.smul contDiff_const
      have hcs1 : ∀ g : Euclid (m + 1) → ℝ, HasCompactSupport g →
          HasCompactSupport (fun y => g y • b i) := fun g hg =>
        hg.comp_left (g := fun r : ℝ => r • b i) (zero_smul ℝ (b i))
      apply hjordan (fun g => T (fun y => g y • b i))
      · intro g h hg hgc hh hhc
        have e : (fun y => (g + h) y • b i) = (fun y => g y • b i) + (fun y => h y • b i) := by
          funext y; rw [Pi.add_apply, Pi.add_apply, add_smul]
        change T (fun y => (g + h) y • b i) = T (fun y => g y • b i) + T (fun y => h y • b i)
        rw [e, hT_add _ _ ((hsm g hg).of_le (by exact_mod_cast le_top)) (hcs1 g hgc)
          ((hsm h hh).of_le (by exact_mod_cast le_top)) (hcs1 h hhc)]
      · intro c g hg
        have e : (fun y => (c • g) y • b i) = c • (fun y => g y • b i) := by
          funext y; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_smul]
        change T (fun y => (c • g) y • b i) = c * T (fun y => g y • b i)
        rw [e, hT_smul c _ ((hsm g hg).of_le (by exact_mod_cast le_top))]
      · intro K hK hKD
        obtain ⟨C, -, hC⟩ := hbd K hK hKD
        refine ⟨C, fun g hg hgc hgK M hM hgM => ?_⟩
        have := hC (fun y => g y • b i) (hsm g hg) (hcs1 g hgc)
          ((tsupport_smul_subset_left g (fun _ => b i)).trans hgK) M hM (fun y => by
            rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs]; exact hgM y)
        exact (le_abs_self _).trans this
    choose μ₁ μ₂ hμ₁ hμ₂ hrep using hcomp
    -- coordinates of a field
    have hcoord_sm : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) (fun y => φ y i) := fun φ i hφ =>
      (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hφ
    have hcoord_cs : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        HasCompactSupport φ → HasCompactSupport (fun y => φ y i) := fun φ i hφ =>
      hφ.comp_left (g := fun v : Euclid (m + 1) => v i) rfl
    have hcoord_ts : ∀ (φ : Euclid (m + 1) → Euclid (m + 1)) (i : Fin (m + 1)),
        tsupport (fun y => φ y i) ⊆ tsupport φ := fun φ i =>
      tsupport_comp_subset (g := fun v : Euclid (m + 1) => v i) rfl φ
    have hTdecomp : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → T φ = ∑ i, T (fun y => φ y i • b i) := by
      intro φ hφ hφc
      have key : ∀ s : Finset (Fin (m + 1)),
          ContDiff ℝ 1 (∑ i ∈ s, fun y => φ y i • b i) ∧
          HasCompactSupport (∑ i ∈ s, fun y => φ y i • b i) ∧
          T (∑ i ∈ s, fun y => φ y i • b i) = ∑ i ∈ s, T (fun y => φ y i • b i) := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          exact ⟨contDiff_const, HasCompactSupport.zero, hT0⟩
        | insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          have h1 : ContDiff ℝ 1 (fun y => φ y j • b j) :=
            ((hcoord_sm φ j hφ).smul contDiff_const).of_le (by exact_mod_cast le_top)
          have h2 : HasCompactSupport (fun y => φ y j • b j) :=
            (hcoord_cs φ j hφc).comp_left (g := fun r : ℝ => r • b j) (zero_smul ℝ _)
          exact ⟨h1.add ih.1, h2.add ih.2.1, by rw [hT_add _ _ h1 h2 ih.1 ih.2.1, ih.2.2]⟩
      have hφeq : φ = ∑ i, fun y => φ y i • b i := by
        funext y
        rw [Finset.sum_apply]
        exact (hbsum (φ y)).symm
      conv_lhs => rw [hφeq]
      exact (key Finset.univ).2.2
    -- the dominating measure on `D`
    have : LocallyCompactSpace D := hD.locallyCompactSpace
    obtain ⟨μD, hμD⟩ : ∃ μD : Measure D, μD = ∑ i, (μ₁ i + μ₂ i) := ⟨_, rfl⟩
    have hμDK : ∀ K : Set D, IsCompact K → μD K < ∞ := by
      intro K hK
      rw [hμD, Measure.finsetSum_apply]
      refine ENNReal.sum_lt_top.2 fun i _ => ?_
      rw [Measure.add_apply]
      exact ENNReal.add_lt_top.2 ⟨(hμ₁ i).lt_top_of_isCompact hK, (hμ₂ i).lt_top_of_isCompact hK⟩
    have : IsFiniteMeasureOnCompacts μD := ⟨hμDK⟩
    have hRN : ∀ ν : Measure D, IsFiniteMeasureOnCompacts ν → ν ≤ μD →
        ∃ r : D → ℝ≥0∞, Measurable r ∧ (∀ᵐ x ∂μD, r x < ∞) ∧ ν = μD.withDensity r := by
      intro ν hν hle
      have := hν
      refine ⟨ν.rnDeriv μD, Measure.measurable_rnDeriv _ _, Measure.rnDeriv_lt_top _ _, ?_⟩
      have := Measure.haveLebesgueDecomposition_add ν μD
      rwa [Measure.singularPart_eq_zero_of_ac (Measure.absolutelyContinuous_of_le hle),
        zero_add] at this
    have hle₁ : ∀ i, μ₁ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_self_add
    have hle₂ : ∀ i, μ₂ i ≤ μD := fun i => Measure.le_iff'.2 fun s => by
      rw [hμD, Measure.finsetSum_apply]
      refine le_trans ?_ (Finset.single_le_sum (f := fun j => (μ₁ j + μ₂ j) s)
        (fun j _ => zero_le) (Finset.mem_univ i))
      rw [Measure.add_apply]
      exact le_add_self
    choose r₁ hr₁m hr₁lt hr₁ using fun i => hRN (μ₁ i) (hμ₁ i) (hle₁ i)
    choose r₂ hr₂m hr₂lt hr₂ using fun i => hRN (μ₂ i) (hμ₂ i) (hle₂ i)
    -- the density field `H`
    obtain ⟨c, hc⟩ : ∃ c : Fin (m + 1) → D → ℝ, ∀ i x, c i x = (r₁ i x).toReal - (r₂ i x).toReal :=
      ⟨fun i x => (r₁ i x).toReal - (r₂ i x).toReal, fun _ _ => rfl⟩
    have hcm : ∀ i, Measurable (c i) := fun i => by
      have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
      rw [this]
      exact (hr₁m i).ennreal_toReal.sub (hr₂m i).ennreal_toReal
    obtain ⟨H, hH⟩ : ∃ H : D → Euclid (m + 1), ∀ x, H x = ∑ i, c i x • b i :=
      ⟨fun x => ∑ i, c i x • b i, fun _ => rfl⟩
    have hHm : Measurable H := by
      have : H = fun x => ∑ i, c i x • b i := funext hH
      rw [this]
      exact Finset.measurable_sum _ fun i _ => (hcm i).smul_const (b i)
    have hrepD : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ D → T φ = ∫ x : D, inner ℝ (φ x) (H x) ∂μD := by
      intro φ hφ hφc hφD
      rw [hTdecomp φ hφ hφc]
      have hterm : ∀ i, Integrable (fun x : D => c i x * φ x i) μD ∧
          T (fun y => φ y i • b i) = ∫ x : D, c i x * φ x i ∂μD := by
        intro i
        have hgi := hcoord_sm φ i hφ
        have hgc := hcoord_cs φ i hφc
        have hgD := (hcoord_ts φ i).trans hφD
        have I₁ := hintD (μ₁ i) (hμ₁ i) (fun y => φ y i) hgi.continuous hgc hgD
        have I₂ := hintD (μ₂ i) (hμ₂ i) (fun y => φ y i) hgi.continuous hgc hgD
        rw [hrep i (fun y => φ y i) hgi hgc hgD]
        rw [hr₁ i] at I₁ ⊢
        rw [hr₂ i] at I₂ ⊢
        have J₁ := (integrable_withDensity_iff_integrable_smul' (hr₁m i) (hr₁lt i)).1 I₁
        have J₂ := (integrable_withDensity_iff_integrable_smul' (hr₂m i) (hr₂lt i)).1 I₂
        rw [integral_withDensity_eq_integral_toReal_smul (hr₁m i) (hr₁lt i),
          integral_withDensity_eq_integral_toReal_smul (hr₂m i) (hr₂lt i), ← integral_sub J₁ J₂]
        have e : (fun x : D => c i x * φ x i) =
            fun x : D => (r₁ i x).toReal • φ x i - (r₂ i x).toReal • φ x i := by
          funext x
          rw [hc, smul_eq_mul, smul_eq_mul, sub_mul]
        rw [e]
        exact ⟨J₁.sub J₂, rfl⟩
      rw [Finset.sum_congr rfl fun i _ => (hterm i).2,
        ← integral_finsetSum _ fun i _ => (hterm i).1]
      congr 1
      funext x
      rw [hH, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_right, hbinner]
    -- normalization to a unit field
    obtain ⟨ν', hν'⟩ : ∃ ν' : D → Euclid (m + 1), ∀ x,
        ν' x = if H x = 0 then b 0 else ‖H x‖⁻¹ • H x :=
      ⟨fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x, fun _ => rfl⟩
    have hν'm : Measurable ν' := by
      have : ν' = fun x => if H x = 0 then b 0 else ‖H x‖⁻¹ • H x := funext hν'
      rw [this]
      exact Measurable.ite (measurableSet_eq_fun hHm measurable_const) measurable_const
        (hHm.norm.inv.smul hHm)
    have hν'1 : ∀ x, ‖ν' x‖ = 1 := by
      intro x
      rw [hν']
      split_ifs with h
      · exact hb1 0
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h)]
    have hHν : ∀ (v : Euclid (m + 1)) (x : D),
        (‖H x‖₊ : ℝ) • inner ℝ v (ν' x) = inner ℝ v (H x) := by
      intro v x
      rw [hν', coe_nnnorm, smul_eq_mul]
      split_ifs with h
      · rw [h, norm_zero, zero_mul, inner_zero_right]
      · rw [real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.2 h), one_mul]
    obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure D,
        μ' = μD.withDensity (fun x => ((‖H x‖₊ : NNReal) : ℝ≥0∞)) := ⟨_, rfl⟩
    have hμ'K : ∀ K : Set D, IsCompact K → μ' K < ∞ := by
      intro K hK
      have hKm : MeasurableSet K := hK.measurableSet
      have hlt : ∀ (r : D → ℝ≥0∞) (ν : Measure D), Measurable r → IsFiniteMeasureOnCompacts ν →
          ν = μD.withDensity r → IntegrableOn (fun x => (r x).toReal) K μD := by
        intro r ν hr hν hνr
        apply integrable_toReal_of_lintegral_ne_top hr.aemeasurable
        rw [← withDensity_apply _ hKm, ← hνr]
        exact (hν.lt_top_of_isCompact hK).ne
      have hci : ∀ i, IntegrableOn (c i) K μD := by
        intro i
        have : c i = fun x => (r₁ i x).toReal - (r₂ i x).toReal := funext (hc i)
        rw [this]
        exact (hlt _ _ (hr₁m i) (hμ₁ i) (hr₁ i)).sub (hlt _ _ (hr₂m i) (hμ₂ i) (hr₂ i))
      have hHK : IntegrableOn H K μD := by
        have : H = fun x => ∑ i, c i x • b i := funext hH
        rw [this]
        exact integrable_finsetSum _ fun i _ => (hci i).smul_const (b i)
      rw [hμ', withDensity_apply _ hKm]
      exact hHK.hasFiniteIntegral
    -- push forward to `ℝ^{m+1}`
    refine ⟨Measure.map Subtype.val μ', fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.map_apply measurable_subtype_coe hD.measurableSet.compl]
      have : (Subtype.val ⁻¹' Dᶜ : Set D) = ∅ := by
        ext x
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
        exact x.2
      rw [this, measure_empty]
    · intro K hK hKD
      rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
      exact (hμ'K _ (hsubK K hK hKD)).ne
    · exact Measurable.dite hν'm.neg measurable_const hD.measurableSet
    · intro y
      by_cases hy : y ∈ D
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_left hy, norm_neg, hν'1]
      · show ‖(if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0)‖ = 1
        rw [dite_eq_right hy, hb1]
    · intro φ hφ hφc hφD
      rw [(MeasurableEmbedding.subtype_coe hD.measurableSet).integral_map]
      have e : (fun x : D => inner ℝ (φ x) ((fun y => if hy : y ∈ D then -ν' ⟨y, hy⟩ else b 0) x))
          = fun x : D => -inner ℝ (φ x) (ν' x) := by
        funext x
        show inner ℝ (φ x) (if hy : (x : Euclid (m + 1)) ∈ D then -ν' ⟨x, hy⟩ else b 0) =
          -inner ℝ (φ x) (ν' x)
        rw [dite_eq_left x.2, Subtype.coe_eta, inner_neg_right]
      rw [e, integral_neg, neg_neg, hrepD φ hφ hφc hφD, hμ',
        integral_withDensity_eq_integral_smul hHm.nnnorm]
      congr 1
      funext x
      rw [NNReal.smul_def]
      exact (hHν (φ x) x).symm
  obtain ⟨μ, ν, hμD, hμK, hνm, hν1, hsmooth⟩ := hsm_rep
  refine ⟨μ, ν, hμD, hμK, hνm, hν1, ?_⟩
  -- Step 5: `C¹` fields, by mollification
  -- normalized mollifiers
  have hmoll : ∀ r : ℝ, 0 < r → ∃ ρ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧
      HasCompactSupport ρ ∧ (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x = 1 ∧ support ρ ⊆ ball 0 r := by
    intro r hr
    let B : ContDiffBump (0 : Euclid (m + 1)) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
    have hBs : HasCompactSupport B := B.hasCompactSupport
    have hBi : Integrable B := B.continuous.integrable_of_hasCompactSupport hBs
    have hI : 0 < ∫ x, B x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => B.nonneg' x) hBi, B.support_eq]
      exact measure_ball_pos volume 0 hr
    refine ⟨fun x => (∫ y, B y)⁻¹ * B x, contDiff_const.mul B.contDiff, hBs.mul_left,
      fun x => mul_nonneg (inv_nonneg.2 hI.le) (B.nonneg' x), ?_, ?_⟩
    · rw [integral_const_mul, inv_mul_cancel₀ hI.ne']
    · exact (support_mul_subset_right _ _).trans B.support_eq.subset
  have hprec : ContinuousLinearMap.precompR (Euclid (m + 1))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid (m + 1) →L[ℝ] Euclid (m + 1)) =
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (Euclid (m + 1) →L[ℝ] Euclid (m + 1)) →L[ℝ]
        (Euclid (m + 1) →L[ℝ] Euclid (m + 1))) := by
    ext x A v
    simp [ContinuousLinearMap.precompR]
  intro φ hφ hφc hφD
  obtain ⟨δ, hδ, hδD⟩ := IsCompact.exists_cthickening_subset_open hφc hD hφD
  set K' := cthickening δ (tsupport φ) with hK'
  have hK'c : IsCompact K' := IsCompact.cthickening hφc
  have hK'm : MeasurableSet K' := isClosed_cthickening.measurableSet
  -- radii
  obtain ⟨rr, hrr0, hrrδ, hrrlim⟩ : ∃ rr : ℕ → ℝ, (∀ n, 0 < rr n) ∧ (∀ n, rr n ≤ δ) ∧
      Tendsto rr atTop (𝓝 0) := by
    refine ⟨fun n => δ / ((n : ℝ) + 1), fun n => div_pos hδ (by positivity), fun n => ?_, ?_⟩
    · exact div_le_self hδ.le (by
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
    · exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  choose ρ hρs hρc hρ0 hρ1 hρsupp using fun n => hmoll (rr n) (hrr0 n)
  -- mollified fields
  obtain ⟨φn, hφn⟩ : ∃ φn : ℕ → Euclid (m + 1) → Euclid (m + 1),
      ∀ n, φn n = convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    ⟨fun n => convolution (ρ n) φ (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun _ => rfl⟩
  have hφn_sm : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φn n) := fun n => by
    rw [hφn]
    exact (hρc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρs n)
      hφ.continuous.locallyIntegrable
  have hφn_supp : ∀ n, support (φn n) ⊆ K' := fun n => by
    rw [hφn]
    refine (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans ?_
    refine (Set.add_subset_add (hρsupp n) (subset_tsupport φ)).trans ?_
    rw [ball_add_zero]
    exact (thickening_subset_cthickening _ _).trans (cthickening_mono (hrrδ n) _)
  have hφn_cs : ∀ n, HasCompactSupport (φn n) ∧ tsupport (φn n) ⊆ K' := fun n =>
    ⟨hK'c.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hφn_supp n) hK'c.isClosed),
      closure_minimal (hφn_supp n) hK'c.isClosed⟩
  -- bounds
  obtain ⟨Mφ, hMφ⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  have hMφ0 : 0 ≤ Mφ := (norm_nonneg _).trans (hMφ 0)
  have hdφc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv one_ne_zero
  obtain ⟨M', hM'⟩ := hdφc.bounded_above_of_compact_support (hφc.fderiv ℝ)
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  have hφn_bd : ∀ n y, ‖φn n y‖ ≤ Mφ := fun n y => by
    rw [hφn, ← dist_zero_right]
    exact dist_convolution_le hMφ0 (hρsupp n) (hρ0 n) (hρ1 n)
      hφ.continuous.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hMφ x)
  have hsmall : Tendsto (fun n => support (ρ n)) atTop (𝓝 (0 : Euclid (m + 1))).smallSets := by
    rw [tendsto_smallSets_iff]
    intro t ht
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht
    filter_upwards [hrrlim.eventually (gt_mem_nhds hε)] with n hn
    exact (hρsupp n).trans ((ball_subset_ball hn.le).trans hεt)
  have hφn_lim : ∀ y, Tendsto (fun n => φn n y) atTop (𝓝 (φ y)) := fun y => by
    simp only [hφn]
    exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1) hsmall
      (Eventually.of_forall fun _ => hφ.continuous.aestronglyMeasurable)
      ((hφ.continuous.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- derivatives
  have hdφn : ∀ n y, fderiv ℝ (φn n) y =
      convolution (ρ n) (fderiv ℝ φ) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := fun n y => by
    rw [hφn, ← hprec]
    exact (hφc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
      (hρs n).continuous.locallyIntegrable hφ y).fderiv
  have hdφn_bd : ∀ n y, ‖fderiv ℝ (φn n) y‖ ≤ M' := fun n y => by
    rw [hdφn, ← dist_zero_right]
    exact dist_convolution_le hM'0 (hρsupp n) (hρ0 n) (hρ1 n)
      hdφc.aestronglyMeasurable (fun x _ => by rw [dist_zero_right]; exact hM' x)
  have hdφn_lim : ∀ y, Tendsto (fun n => fderiv ℝ (φn n) y) atTop (𝓝 (fderiv ℝ φ y)) :=
    fun y => by
      simp only [hdφn]
      exact convolution_tendsto_right (Eventually.of_forall hρ0) (Eventually.of_forall hρ1)
        hsmall (Eventually.of_forall fun _ => hdφc.aestronglyMeasurable)
        ((hdφc.tendsto y).comp tendsto_snd) tendsto_const_nhds
  -- convergence of the left side
  have hL : Tendsto (fun n => T (φn n)) atTop (𝓝 (T φ)) := by
    simp only [hT]
    refine tendsto_integral_of_dominated_convergence (K'.indicator fun _ => ‖trc‖ * M')
      (fun n => (trc.continuous.comp ((hφn_sm n).continuous_fderiv (by simp))).aestronglyMeasurable)
      ?_ (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · exact ((integrable_indicator_iff hK'm).2
        (integrableOn_const hK'c.measure_lt_top.ne)).restrict
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        exact (trc.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hdφn_bd n y) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        have : fderiv ℝ (φn n) y = 0 :=
          notMem_support.1 fun h => hy ((hφn_cs n).2 (support_fderiv_subset ℝ h))
        rw [this, map_zero, norm_zero]
    · exact (trc.continuous.tendsto _).comp (hdφn_lim y)
  -- convergence of the right side
  have hR : Tendsto (fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ) atTop
      (𝓝 (-∫ y, inner ℝ (φ y) (ν y) ∂μ)) := by
    refine Tendsto.neg (tendsto_integral_of_dominated_convergence (K'.indicator fun _ => Mφ)
      (fun n => (Continuous.measurable2 continuous_inner (hφn_sm n).continuous.measurable
        hνm).aestronglyMeasurable) ?_ (fun n => Eventually.of_forall fun y => ?_)
      (Eventually.of_forall fun y => ?_))
    · exact (integrable_indicator_iff hK'm).2
        (integrableOn_const (hμK K' hK'c hδD))
    · by_cases hy : y ∈ K'
      · rw [indicator_of_mem hy]
        refine (norm_inner_le_norm _ _).trans ?_
        rw [hν1, mul_one]
        exact hφn_bd n y
      · rw [indicator_of_notMem hy]
        have : φn n y = 0 := notMem_support.1 fun h => hy (hφn_supp n h)
        rw [this, inner_zero_left, norm_zero]
    · exact (hφn_lim y).inner tendsto_const_nhds
  have hLR : (fun n => T (φn n)) = fun n => -∫ y, inner ℝ (φn n y) (ν y) ∂μ := by
    funext n
    exact hsmooth (φn n) (hφn_sm n) (hφn_cs n).1 ((hφn_cs n).2.trans hδD)
  rw [hLR] at hL
  exact tendsto_nhds_unique hL hR

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
