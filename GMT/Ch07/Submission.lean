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

/-- **Simon Ch. 3, Lemma 1.2 and Remark 1.3**, with bi-Lipschitz Borel pieces in place of `C¹`
submanifolds: a Borel countably `n`-rectifiable `M ⊆ ℝᴾ` is, up to an `Hⁿ`-null set, the disjoint
union of Borel sets `Fᵢ(Bᵢ) ⊆ M`, where `Fᵢ : ℝⁿ → ℝᴾ` is Lipschitz, `Bᵢ` is Borel,
`mᵢ|a − a'| ≤ |Fᵢ(a) − Fᵢ(a')|` on `Bᵢ` for some `mᵢ > 0`, and `DFᵢ` exists and is injective on
`Bᵢ`.  Each Lipschitz `Fⱼ` of the cover maps its non-differentiability points (Rademacher) and
its critical points (the image of `{JFⱼ = 0}`) to `Hⁿ`-null sets.  Mathlib's partition lemma cuts
the regular points into pieces on which `Fⱼ` is close to an injective linear map, hence
bi-Lipschitz; the images of the pieces are Borel (Lusin–Souslin) and are made disjoint as in
Remark 1.3. -/
theorem Submission.dpf_rectifiable_bilipschitz_pieces : ∀ (P n : ℕ) (M : Set (Euclid P)), MeasurableSet M → CountablyRectifiable n M → ∃ (F : ℕ → Euclid n → Euclid P) (B : ℕ → Set (Euclid n)) (m : ℕ → ℝ), (∀ i, ∃ L : NNReal, LipschitzWith L (F i)) ∧ (∀ i, MeasurableSet (B i)) ∧ (∀ i, 0 < m i) ∧ (∀ i, ∀ a ∈ B i, ∀ a' ∈ B i, m i * ‖a - a'‖ ≤ ‖F i a - F i a'‖) ∧ (∀ i, ∀ a ∈ B i, DifferentiableAt ℝ (F i) a ∧ Injective (fderiv ℝ (F i) a)) ∧ (∀ i, MeasurableSet (F i '' B i)) ∧ (∀ i, F i '' B i ⊆ M) ∧ Pairwise (fun i j => Disjoint (F i '' B i) (F j '' B j)) ∧ μHE[n] (M \ ⋃ i, F i '' B i) = 0 := by
  intro P n M hM hrect
  have hvol : (μHE[n] : Measure (Euclid n)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
  -- Step 1: the rectifiable cover `M ⊆ M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ)`
  obtain ⟨M₀, hM₀, F₀, hF₀, hcover⟩ := hrect
  choose K hK using hF₀
  -- Step 2: the regular sets `Gⱼ` are Borel and `Hⁿ(Fⱼ(ℝⁿ ∖ Gⱼ)) = 0`
  have hGmeas : ∀ f : Euclid n → Euclid P,
      MeasurableSet {a | DifferentiableAt ℝ f a ∧ Injective (fderiv ℝ f a)} := fun f =>
    (measurableSet_of_differentiableAt ℝ f).inter
      (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet)
  -- Step 2(a): nondifferentiability points have null image (Rademacher)
  have hrad : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | ¬ DifferentiableAt ℝ f a}) = 0 := by
    intro f L hf
    have hz : volume {a : Euclid n | ¬ DifferentiableAt ℝ f a} = 0 :=
      ae_iff.mp (hf.ae_differentiableAt (μ := volume))
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hf.lipschitzOnWith (s := {a | ¬ DifferentiableAt ℝ f a}))
    rw [hvol, hz, mul_zero] at hle
    exact le_antisymm hle bot_le
  -- Step 2(b): critical points have null image.  On a piece where `f` is `ε`-close to a
  -- rank-deficient `A` (`Av = 0`, `‖v‖ = 1`), `|f a - f a'| ≤ (L + 1)|D a - D a'|` for
  -- `D = id - (1 - ε) v ⊗ v`, and `det D = ε`.
  have hsard : ∀ (f : Euclid n → Euclid P) (L : NNReal), LipschitzWith L f →
      μHE[n] (f '' {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}) = 0 := by
    intro f L hf
    set S := {a | DifferentiableAt ℝ f a ∧ ¬ Injective (fderiv ℝ f a)}
    have hSmeas : MeasurableSet S :=
      (measurableSet_of_differentiableAt ℝ f).inter
        (measurable_fderiv ℝ f ContinuousLinearMap.isOpen_injective.measurableSet).compl
    have hR : ∀ R : ℕ, μHE[n] (f '' (S ∩ ball (0 : Euclid n) R)) = 0 := by
      intro R
      set s := S ∩ ball (0 : Euclid n) R
      have hsmeas : MeasurableSet s := hSmeas.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (f '' s) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
        intro ε hε hε1
        rcases s.eq_empty_or_nonempty with hse | hsne
        · rw [hse, image_empty, measure_empty]; exact bot_le
        obtain ⟨t, A, htdisj, htmeas, hst, hA, hAy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s (fderiv ℝ f)
            (fun x hx => hx.1.1.hasFDerivAt.hasFDerivWithinAt) (fun _ => ε) (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (f '' (s ∩ t k)) ≤
            ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
          intro k
          obtain ⟨y, hy, hAk⟩ := hAy hsne k
          have hAnorm : ‖A k‖ ≤ L := hAk ▸ norm_fderiv_le_of_lipschitz ℝ hf
          have hAni : ¬ Injective (A k) := hAk ▸ hy.1.2
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ A k v = 0 := by
            simp only [Injective, not_forall] at hAni
            obtain ⟨a, b, hab, hne⟩ := hAni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c : ℝ := 1 - (ε : ℝ) with hc
          have hc0 : 0 ≤ c := by
            rw [hc]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hAD : ∀ h, A k (D h) = A k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc]; ring
          have hfD : ∀ a ∈ s ∩ t k, ∀ a' ∈ s ∩ t k,
              ‖f a - f a'‖ ≤ ((L : ℝ) + 1) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hA k a ha a' ha'
            have h2 : ‖A k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hAD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (f a - f a') (A k (a - a'))
            linarith
          have himg : μHE[n] (f '' (s ∩ t k)) ≤
              ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := by
            set X := s ∩ t k
            set g := Function.invFunOn D X
            have hg : ∀ y ∈ D '' X, g y ∈ X ∧ D (g y) = y :=
              fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
            have hLip : LipschitzOnWith (L + 1) (f ∘ g) (D '' X) := by
              refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
              obtain ⟨hgy, hDy⟩ := hg y hy
              obtain ⟨hgy', hDy'⟩ := hg y' hy'
              simp only [comp_apply, dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
              calc ‖f (g y) - f (g y')‖ ≤ ((L : ℝ) + 1) * ‖D (g y) - D (g y')‖ :=
                    hfD _ hgy _ hgy'
                _ = _ := by rw [hDy, hDy']
            have hsub : f '' X ⊆ (f ∘ g) '' (D '' X) := by
              rintro _ ⟨a, ha, rfl⟩
              refine ⟨D a, mem_image_of_mem D ha, ?_⟩
              obtain ⟨hga, hDa⟩ := hg (D a) (mem_image_of_mem D ha)
              have := hfD _ hga _ ha
              rw [hDa, sub_self, norm_zero, mul_zero] at this
              exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
            exact (measure_mono hsub).trans
              (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hLip)
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c * v i) = 1 - c * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc]; ring
          calc μHE[n] (f '' (s ∩ t k)) ≤
                ((L + 1 : NNReal) : ℝ≥0∞) ^ n * μHE[n] (D '' (s ∩ t k)) := himg
            _ = ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := by
              rw [hvol, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
                NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
              push_cast
              ring
        calc μHE[n] (f '' s) ≤ μHE[n] (⋃ k, f '' (s ∩ t k)) := by
              apply measure_mono
              rintro _ ⟨a, ha, rfl⟩
              obtain ⟨k, hk⟩ := mem_iUnion.mp (hst ha)
              exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
          _ ≤ ∑' k, μHE[n] (f '' (s ∩ t k)) := measure_iUnion_le _
          _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (s ∩ t k) * ε := ENNReal.tsum_le_tsum hpiece
          _ = ((L : ℝ≥0∞) + 1) ^ n * volume (⋃ k, s ∩ t k) * ε := by
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, measure_iUnion]
              · exact fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right
              · exact fun k => hsmeas.inter (htmeas k)
          _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by
              gcongr
              exact iUnion_subset fun k => inter_subset_left.trans inter_subset_right
      have hfin : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have htend : Tendsto (fun ε : NNReal =>
          ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * (ε : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
          rw [← ENNReal.coe_zero]
          exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
        simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hfin)
      refine le_antisymm (ge_of_tendsto htend ?_) bot_le
      filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
      exact hbound ε hε.1 hε.2
    refine measure_mono_null ?_ (measure_iUnion_null hR)
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
    exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
  set G : ℕ → Set (Euclid n) := fun j =>
    {a | DifferentiableAt ℝ (F₀ j) a ∧ Injective (fderiv ℝ (F₀ j) a)}
  have hGnull : ∀ j, μHE[n] (F₀ j '' (G j)ᶜ) = 0 := by
    intro j
    refine measure_mono_null ?_ (measure_union_null (hrad _ _ (hK j)) (hsard _ _ (hK j)))
    rintro _ ⟨a, ha, rfl⟩
    by_cases hd : DifferentiableAt ℝ (F₀ j) a
    · exact Or.inr ⟨a, ⟨hd, fun hi => ha ⟨hd, hi⟩⟩, rfl⟩
    · exact Or.inl ⟨a, hd, rfl⟩
  -- Step 3: a coercivity constant `c(A)` for every injective `A`; radius `r(A) = c(A)/2 ≠ 0`
  have hcoer : ∀ A : Euclid n →L[ℝ] Euclid P, ∃ c : NNReal, 0 < c ∧
      (Injective A → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖A h‖) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨C, Cpos, hC⟩ := A.injective_iff_antilipschitz.mp hA
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := A.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖A h‖) := by gcongr
        _ = ‖A h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hA⟩
  choose c hcpos hc using hcoer
  -- Step 4: Mathlib's partition of `Gⱼ` into pieces on which `Fⱼ` is close to linear
  have hpart : ∀ j, ∃ (t : ℕ → Set (Euclid n)) (A : ℕ → Euclid n →L[ℝ] Euclid P),
      Pairwise (Disjoint on t) ∧ (∀ k, MeasurableSet (t k)) ∧ G j ⊆ ⋃ k, t k ∧
      (∀ k, ApproximatesLinearOn (F₀ j) (A k) (G j ∩ t k) (c (A k) / 2)) ∧
      ((G j).Nonempty → ∀ k, ∃ y ∈ G j, A k = fderiv ℝ (F₀ j) y) := fun j =>
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt (F₀ j) (G j) (fderiv ℝ (F₀ j))
      (fun x hx => hx.1.hasFDerivAt.hasFDerivWithinAt) (fun A => c A / 2)
      (fun A => (div_pos (hcpos A) two_pos).ne')
  choose t A htdisj htmeas hGt hAapprox hAy using hpart
  -- Step 5: `Fⱼ` is bi-Lipschitz on `Gⱼ ∩ tⱼₖ` with lower constant `c(Aⱼₖ)/2`
  have hlow : ∀ j k, ∀ a ∈ G j ∩ t j k, ∀ a' ∈ G j ∩ t j k,
      ((c (A j k) / 2 : NNReal) : ℝ) * ‖a - a'‖ ≤ ‖F₀ j a - F₀ j a'‖ := by
    intro j k a ha a' ha'
    obtain ⟨y, hy, hAk⟩ := hAy j ⟨a, ha.1⟩ k
    have hinj : Injective (A j k) := hAk ▸ hy.2
    have h1 := hc (A j k) hinj (a - a')
    have h2 := hAapprox j k a ha a' ha'
    have h3 := norm_sub_norm_le (A j k (a - a')) (F₀ j a - F₀ j a')
    rw [norm_sub_rev (A j k (a - a'))] at h3
    push_cast at h2 ⊢
    linarith
  -- Step 6: enumerate the pieces by `i ↦ (unpair i)`; their images are Borel (Lusin–Souslin)
  set Fi : ℕ → Euclid n → Euclid P := fun i => F₀ (Nat.unpair i).1 with hFi
  set Di : ℕ → Set (Euclid n) := fun i =>
    G (Nat.unpair i).1 ∩ t (Nat.unpair i).1 (Nat.unpair i).2 with hDi
  set mi : ℕ → ℝ := fun i =>
    ((c (A (Nat.unpair i).1 (Nat.unpair i).2) / 2 : NNReal) : ℝ) with hmi
  have hDmeas : ∀ i, MeasurableSet (Di i) := fun i =>
    (hGmeas _).inter (htmeas _ _)
  have hmipos : ∀ i, 0 < mi i := fun i => by
    simp only [hmi, NNReal.coe_div, NNReal.coe_ofNat]
    exact div_pos (hcpos _) two_pos
  have hlowi : ∀ i, ∀ a ∈ Di i, ∀ a' ∈ Di i, mi i * ‖a - a'‖ ≤ ‖Fi i a - Fi i a'‖ :=
    fun i => hlow _ _
  have hNmeas : ∀ i, MeasurableSet (Fi i '' Di i) := by
    intro i
    refine (hDmeas i).image_of_continuousOn_injOn (hK _).continuous.continuousOn ?_
    intro a ha a' ha' h
    have := hlowi i a ha a' ha'
    rw [h, sub_self, norm_zero] at this
    have h0 : ‖a - a'‖ = 0 := by
      rcases (norm_nonneg (a - a')).eq_or_lt with h0 | h0
      · exact h0.symm
      · linarith [mul_pos (hmipos i) h0]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  -- Step 7: disjointify the images inside `M`
  set Ñ : ℕ → Set (Euclid P) := fun i => Fi i '' Di i ∩ M
  have hÑmeas : ∀ i, MeasurableSet (Ñ i) := fun i => (hNmeas i).inter hM
  set B : ℕ → Set (Euclid n) := fun i => Di i ∩ Fi i ⁻¹' disjointed Ñ i with hB
  have himg : ∀ i, Fi i '' B i = disjointed Ñ i := by
    intro i
    rw [hB, image_inter_preimage]
    exact inter_eq_right.mpr ((disjointed_subset Ñ i).trans inter_subset_left)
  refine ⟨Fi, B, mi, fun i => ⟨K _, hK _⟩,
    fun i => (hDmeas i).inter ((hK _).continuous.measurable (MeasurableSet.disjointed hÑmeas i)),
    hmipos, fun i a ha a' ha' => hlowi i a ha.1 a' ha'.1, fun i a ha => ha.1.1,
    fun i => himg i ▸ MeasurableSet.disjointed hÑmeas i,
    fun i => himg i ▸ ((disjointed_subset Ñ i).trans inter_subset_right), ?_, ?_⟩
  · intro i j hij
    rw [himg i, himg j]
    exact disjoint_disjointed Ñ hij
  -- Step 8: the remainder lies in `M₀ ∪ ⋃ⱼ Fⱼ(ℝⁿ ∖ Gⱼ)`
  · have hU : (⋃ i, Fi i '' B i) = ⋃ i, Ñ i := by
      simp_rw [himg]
      exact iUnion_disjointed
    rw [hU]
    refine measure_mono_null ?_ (measure_union_null hM₀ (measure_iUnion_null hGnull))
    rintro x ⟨hxM, hxN⟩
    rcases hcover hxM with hx0 | hx
    · exact Or.inl hx0
    · obtain ⟨j, a, rfl⟩ := mem_iUnion.mp hx
      by_cases ha : a ∈ G j
      · exfalso
        obtain ⟨k, hk⟩ := mem_iUnion.mp (hGt j ha)
        apply hxN
        refine mem_iUnion.mpr ⟨Nat.pair j k, ⟨a, ?_, ?_⟩, hxM⟩
        · simp only [hDi, Nat.unpair_pair]
          exact ⟨ha, hk⟩
        · simp only [hFi, Nat.unpair_pair]
      · exact Or.inr (mem_iUnion.mpr ⟨j, a, ha, rfl⟩)

/-- **Product-null lemma**: if `Z ⊆ ℝᴺ` has `Hⁿ(Z) = 0`, then the cylinder `Ψ(ℝ × Z) ⊆ ℝᴺ⁺¹`,
`Ψ(t, x) = (t, x₁, …, x_N)`, has `Hⁿ⁺¹(Ψ(ℝ × Z)) = 0`.  Since `μHE = c • μH` with `c ≠ 0` and `Ψ`
is linear, hence Lipschitz for the max metric on `ℝ × ℝᴺ`, it suffices that `μH[n + 1](ℝ × Z) = 0`;
for `n = 0`, `Z = ∅`.  Given `ε ∈ (0, 1]`, cover `Z` by sets `Cⱼ` with `diam Cⱼ ≤ ε` and
`Σ (diam Cⱼ)ⁿ < ε`, pick `eⱼ > 0` with `Σ eⱼ < ε`, and cut each strip `[m, m + 1] × Cⱼ` into
`⌊1/dⱼ⌋ + 1` boxes of side `dⱼ = max(diam Cⱼ, eⱼ)`; their `(n + 1)`-cost is `≤ 4ε`. -/
theorem Submission.dimred_mbl_dt_lp_imc_product_null : ∀ (N n : ℕ) (Z : Set (Euclid N)), μHE[n] Z = 0 → μHE[n + 1] ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (univ ×ˢ Z)) = 0 := by
  intro N n Z hZ
  -- Step 1: `μHE[d] = c_d • μH[d]` with `c_d ≠ 0`, so it suffices to work with `μH`
  have hZ' : μH[(n : ℝ)] Z = 0 := by
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
      mul_eq_zero] at hZ
    exact hZ.resolve_left
      (by simpa using Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply]
  suffices h : μH[((n + 1 : ℕ) : ℝ)] ((fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (univ ×ˢ Z)) = 0 by
    rw [h, smul_zero]
  -- Step 3: for `n = 0`, `μH[0] Z = 0` forces `Z = ∅`
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hZe : Z = ∅ := by
      rcases Z.eq_empty_or_nonempty with h | h
      · exact h
      · have := Measure.one_le_hausdorffMeasure_zero_of_nonempty h
        rw [Nat.cast_zero] at hZ'
        rw [hZ'] at this
        exact absurd this (by simp)
    simp [hZe]
  -- Step 2: `Ψ` is linear, hence Lipschitz for the max metric on `ℝ × ℝᴺ`
  let L : (ℝ × Euclid N) →ₗ[ℝ] Euclid (N + 1) :=
    { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
      map_add' := fun p q => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp
      map_smul' := fun c p => by
        ext i
        refine Fin.cases ?_ (fun i => ?_) i <;> simp }
  have hL : LipschitzWith ‖LinearMap.toContinuousLinearMap L‖₊ (fun p : ℝ × Euclid N =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) :=
    (LinearMap.toContinuousLinearMap L).lipschitzWith
  refine le_antisymm ((hL.hausdorffMeasure_image_le (by positivity) _).trans ?_) bot_le
  suffices hprod : μH[((n + 1 : ℕ) : ℝ)] (univ ×ˢ Z : Set (ℝ × Euclid N)) = 0 by
    rw [hprod, mul_zero]
  -- in the max metric, `diam (I × C) ≤ max (diam I) (diam C)`
  have hdiam_prod : ∀ (s : Set ℝ) (c : Set (Euclid N)),
      ediam (s ×ˢ c) ≤ max (ediam s) (ediam c) := by
    intro s c
    refine ediam_le ?_
    rintro ⟨a, x⟩ ⟨ha, hx⟩ ⟨b, y⟩ ⟨hb, hy⟩
    rw [Prod.edist_eq]
    exact max_le_max (edist_le_ediam_of_mem ha hb) (edist_le_ediam_of_mem hx hy)
  -- Steps 4–8: each strip `[m, m + 1] × Z` is `μH[n + 1]`-null
  have hstrip : ∀ m : ℤ, μH[((n + 1 : ℕ) : ℝ)] (Icc (m : ℝ) (m + 1) ×ˢ Z) = 0 := by
    intro m
    have hcov : ∀ ε : ℝ≥0∞, 0 < ε → ε ≤ 1 → ∃ t : ℕ × ℕ → Set (ℝ × Euclid N),
        Icc (m : ℝ) (m + 1) ×ˢ Z ⊆ ⋃ i, t i ∧ (∀ i, ediam (t i) ≤ ε) ∧
          ∑' i, ediam (t i) ^ ((n + 1 : ℕ) : ℝ) ≤ 4 * ε := by
      intro ε hε hε1
      -- Step 5: covers `C j` of `Z` with mesh `≤ ε` and `n`-cost `< ε`
      obtain ⟨C, hZC, hCε, hCsum⟩ : ∃ C : ℕ → Set (Euclid N), Z ⊆ ⋃ j, C j ∧
          (∀ j, ediam (C j) ≤ ε) ∧ ∑' j, ⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ) < ε := by
        have h0 : (⨅ (C : ℕ → Set (Euclid N)) (_ : Z ⊆ ⋃ j, C j) (_ : ∀ j, ediam (C j) ≤ ε),
            ∑' j, ⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) < ε := by
          refine lt_of_le_of_lt ?_ hε
          rw [← hZ', Measure.hausdorffMeasure_apply]
          exact le_iSup₂_of_le ε hε le_rfl
        simpa only [iInf_lt_iff, exists_prop] using h0
      obtain ⟨e, he0, hesum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
      have hCtop : ∀ j, ediam (C j) ≠ ⊤ := fun j =>
        ((hCε j).trans_lt (hε1.trans_lt ENNReal.one_lt_top)).ne
      have hele : ∀ j, (e j : ℝ≥0∞) < ε := fun j => (ENNReal.le_tsum j).trans_lt hesum
      -- side lengths `d j = max (diam C j) (e j) ∈ (0, 1]`
      set d : ℕ → ℝ := fun j => max (ediam (C j)).toReal (e j) with hd
      have hdpos : ∀ j, 0 < d j := fun j => lt_max_of_lt_right (he0 j)
      have hdofReal : ∀ j, ENNReal.ofReal (d j) = max (ediam (C j)) (e j) := by
        intro j
        rw [hd, ENNReal.ofReal_max, ENNReal.ofReal_toReal (hCtop j), ENNReal.ofReal_coe_nnreal]
      have hdε : ∀ j, ENNReal.ofReal (d j) ≤ ε := fun j => by
        rw [hdofReal]
        exact max_le (hCε j) (hele j).le
      have hd1 : ∀ j, d j ≤ 1 := by
        intro j
        have := (hdε j).trans hε1
        rwa [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at this
      -- Step 6: boxes `[m + q d j, m + (q + 1) d j] × C j`, `q < p j`
      set p : ℕ → ℕ := fun j => ⌊1 / d j⌋₊ + 1 with hp
      set t : ℕ → ℕ → Set (ℝ × Euclid N) := fun j q =>
        if q < p j then Icc (m + q * d j) (m + (q + 1) * d j) ×ˢ C j else ∅ with ht
      have hpiece : ∀ j q, ediam (t j q) ≤ ENNReal.ofReal (d j) := by
        intro j q
        simp only [ht]
        split_ifs
        · refine (hdiam_prod _ _).trans (max_le ?_ ?_)
          · rw [Real.ediam_Icc]
            exact le_of_eq (congrArg ENNReal.ofReal (by ring))
          · rw [hdofReal]
            exact le_max_left _ _
        · simp
      refine ⟨fun i => t i.1 i.2, ?_, fun i => (hpiece i.1 i.2).trans (hdε i.1), ?_⟩
      · rintro ⟨s, x⟩ ⟨⟨hs1, hs2⟩, hx⟩
        obtain ⟨j, hxj⟩ := mem_iUnion.1 (hZC hx)
        have hsm : 0 ≤ (s - m) / d j := div_nonneg (sub_nonneg.2 hs1) (hdpos j).le
        have hq1 : (⌊(s - m) / d j⌋₊ : ℝ) ≤ (s - m) / d j := Nat.floor_le hsm
        have hq2 : (s - m) / d j < ⌊(s - m) / d j⌋₊ + 1 := Nat.lt_floor_add_one _
        have hqp : ⌊(s - m) / d j⌋₊ < p j := by
          refine Nat.lt_succ_of_le (Nat.floor_mono ?_)
          exact div_le_div_of_nonneg_right (by linarith) (hdpos j).le
        refine mem_iUnion.2 ⟨(j, ⌊(s - m) / d j⌋₊), ?_⟩
        simp only [ht, hqp, ↓reduceIte]
        refine ⟨⟨?_, ?_⟩, hxj⟩
        · rw [le_div_iff₀ (hdpos j)] at hq1
          linarith
        · rw [div_lt_iff₀ (hdpos j)] at hq2
          linarith
      -- Step 7: the `(n + 1)`-cost is `≤ 2 Σ (diam C j)ⁿ + 2 Σ e j ≤ 4ε`
      have hcostj : ∀ j, ∑' q, ediam (t j q) ^ ((n + 1 : ℕ) : ℝ) ≤
          2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) := by
        intro j
        rw [tsum_eq_sum (s := Finset.range (p j)) ?_]
        · calc ∑ q ∈ Finset.range (p j), ediam (t j q) ^ ((n + 1 : ℕ) : ℝ)
              ≤ ∑ q ∈ Finset.range (p j), ENNReal.ofReal (d j) ^ (n + 1) := by
                refine Finset.sum_le_sum fun q _ => ?_
                rw [ENNReal.rpow_natCast]
                exact pow_le_pow_left' (hpiece j q) _
            _ = (p j : ℝ≥0∞) * ENNReal.ofReal (d j) * ENNReal.ofReal (d j) ^ n := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]
                ring
            _ ≤ 2 * ENNReal.ofReal (d j) ^ n := by
                gcongr
                rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
                  show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
                apply ENNReal.ofReal_le_ofReal
                have h1 : (⌊1 / d j⌋₊ : ℝ) ≤ 1 / d j := Nat.floor_le (by positivity)
                simp only [hp]
                push_cast
                calc ((⌊1 / d j⌋₊ : ℝ) + 1) * d j ≤ (1 / d j + 1) * d j := by gcongr
                  _ = 1 + d j := by rw [add_mul, one_div, inv_mul_cancel₀ (hdpos j).ne', one_mul]
                  _ ≤ 2 := by linarith [hd1 j]
            _ ≤ 2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) := by
                gcongr
                rw [hdofReal]
                rcases le_total (ediam (C j)) (e j : ℝ≥0∞) with h | h
                · rw [max_eq_right h]
                  refine le_add_left ?_
                  exact pow_le_of_le_one zero_le ((hele j).le.trans hε1) hn.ne'
                · rw [max_eq_left h]
                  refine le_add_right ?_
                  rcases (C j).eq_empty_or_nonempty with hC | hC
                  · rw [hC, ediam_empty, zero_pow hn.ne']
                    exact zero_le
                  · rw [← ENNReal.rpow_natCast]
                    exact le_iSup_of_le hC le_rfl
        · intro q hq
          rw [Finset.mem_range] at hq
          simp only [ht, hq, ↓reduceIte, ediam_empty]
          exact ENNReal.zero_rpow_of_pos (by positivity)
      calc ∑' i : ℕ × ℕ, ediam (t i.1 i.2) ^ ((n + 1 : ℕ) : ℝ)
          = ∑' j, ∑' q, ediam (t j q) ^ ((n + 1 : ℕ) : ℝ) :=
            ENNReal.tsum_prod (f := fun j q => ediam (t j q) ^ ((n + 1 : ℕ) : ℝ))
        _ ≤ ∑' j, 2 * ((⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + e j) :=
            ENNReal.tsum_le_tsum hcostj
        _ = 2 * (∑' j, (⨆ _ : (C j).Nonempty, ediam (C j) ^ (n : ℝ)) + ∑' j, (e j : ℝ≥0∞)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        _ ≤ 2 * (ε + ε) := by gcongr
        _ = 4 * ε := by ring
    -- Step 8: covers with mesh and cost tending to `0`
    choose t ht using fun k : ℕ => hcov ((k : ℝ≥0∞) + 1)⁻¹ (ENNReal.inv_pos.2 (by simp))
      (ENNReal.inv_le_one.2 le_add_self)
    have hr : Tendsto (fun k : ℕ => ((k : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      simpa [Function.comp_def] using this
    refine le_antisymm ?_ bot_le
    calc μH[((n + 1 : ℕ) : ℝ)] (Icc (m : ℝ) (m + 1) ×ˢ Z)
        ≤ liminf (fun k => ∑' i, ediam (t k i) ^ ((n + 1 : ℕ) : ℝ)) atTop :=
          Measure.hausdorffMeasure_le_liminf_tsum _ _ _ hr t
            (Eventually.of_forall fun k => (ht k).2.1) (Eventually.of_forall fun k => (ht k).1)
      _ ≤ liminf (fun k : ℕ => 4 * ((k : ℝ≥0∞) + 1)⁻¹) atTop :=
          liminf_le_liminf (Eventually.of_forall fun k => (ht k).2.2)
      _ = 0 := by
          refine Tendsto.liminf_eq ?_
          simpa using ENNReal.Tendsto.const_mul hr (Or.inr ENNReal.ofNat_ne_top)
  -- Step 4: `ℝ × Z` is the union of the strips
  refine measure_mono_null ?_ (measure_iUnion_null hstrip)
  rintro ⟨s, x⟩ ⟨-, hx⟩
  exact mem_iUnion.2 ⟨⌊s⌋, ⟨Int.floor_le s, (Int.lt_floor_add_one s).le⟩, hx⟩
/-- **Suspension of a map** (the product pieces `Ĝ(t, u) = (t, G(u))` of a cylinder over a
rectifiable set): if `Ĝ(t, u) = (t, G(u))` for `G : ℝⁿ → ℝᴺ`, then `Ĝ` is `max(1, L)`-Lipschitz
when `G` is `L`-Lipschitz, `min(1, m)|z − z'| ≤ |Ĝ(z) − Ĝ(z')|` on `ℝ × A` when
`m|a − a'| ≤ |G(a) − G(a')|` on `A`, and, where `G` is differentiable at `u`, `Ĝ` is
differentiable at `(t, u)` with `DĜ(t, u)(s, w) = (s, DG(u)w)`.  Hence `DĜ(t, u)` is injective
when `DG(u)` is, its range is `ℝe₀ ⊕ (0, range DG(u))`, and its Gram matrix is
`diag(1, Gram(DG(u)))`, so the two Gram determinants agree. -/
theorem Submission.dimred_mbl_dt_lp_imc_suspension : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (Gh : Euclid (n + 1) → Euclid (N + 1)), (∀ (t : ℝ) (u : Euclid n), Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp (G u)))) → (∀ L : NNReal, LipschitzWith L G → LipschitzWith (max 1 L) Gh) ∧ (∀ (m : ℝ) (A : Set (Euclid n)), (∀ a ∈ A, ∀ a' ∈ A, m * ‖a - a'‖ ≤ ‖G a - G a'‖) → ∀ (t t' : ℝ), ∀ u ∈ A, ∀ u' ∈ A, min 1 m * ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (n + 1)) - WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u'))‖ ≤ ‖Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) - Gh (WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')))‖) ∧ ∀ (t : ℝ) (u : Euclid n), DifferentiableAt ℝ G u → DifferentiableAt ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) ∧ (∀ (s : ℝ) (w : Euclid n), fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))) = WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w)))) ∧ (Injective (fderiv ℝ G u) → Injective (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))))) ∧ LinearMap.range (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) : Euclid (n + 1) →ₗ[ℝ] Euclid (N + 1)) = Submodule.span ℝ (insert (EuclideanSpace.single 0 1) ((fun v : Euclid N => (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v)) : Euclid (N + 1))) '' (LinearMap.range (fderiv ℝ G u : Euclid n →ₗ[ℝ] Euclid N) : Set (Euclid N)))) ∧ Matrix.det (Matrix.of fun i j : Fin (n + 1) => inner ℝ (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single i 1)) (fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) (EuclideanSpace.single j 1))) = Matrix.det (Matrix.of fun i j : Fin n => inner ℝ (fderiv ℝ G u (EuclideanSpace.single i 1)) (fderiv ℝ G u (EuclideanSpace.single j 1))) := by
  intro N n G Gh hGh
  -- `Φ_d(t, u) = (t, u₁, …, u_d)` is a bijection `ℝ × ℝᵈ → ℝᵈ⁺¹`, linear in `(t, u)`,
  -- with `⟨Φ_d(s, v), Φ_d(s', v')⟩ = s s' + ⟨v, v'⟩`
  have hsurj : ∀ z : Euclid (n + 1), ∃ (t : ℝ) (u : Euclid n),
      z = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) := fun z =>
    ⟨WithLp.ofLp z 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)), by simp [Fin.cons_self_tail]⟩
  have hinj : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1)) =
        WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')) → t = t' ∧ u = u' := by
    intro d t t' u u' h
    obtain ⟨h1, h2⟩ := Fin.cons_inj.1 (WithLp.toLp_injective 2 h)
    exact ⟨h1, WithLp.ofLp_injective 2 h2⟩
  have hsub : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1)) -
          WithLp.toLp 2 (Fin.cons t' (WithLp.ofLp u')) =
        WithLp.toLp 2 (Fin.cons (t - t') (WithLp.ofLp (u - u'))) := by
    intro d t t' u u'
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hinner : ∀ (d : ℕ) (s s' : ℝ) (v v' : Euclid d),
      inner ℝ (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp v)) : Euclid (d + 1))
        (WithLp.toLp 2 (Fin.cons s' (WithLp.ofLp v'))) = s * s' + inner ℝ v v' := by
    intro d s s' v v'
    simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
  have hnorm : ∀ (d : ℕ) (t : ℝ) (u : Euclid d),
      ‖(WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)) : Euclid (d + 1))‖ ^ 2 = t ^ 2 + ‖u‖ ^ 2 := by
    intro d t u
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner, sq]
  refine ⟨fun L hL => LipschitzWith.of_dist_le_mul fun z z' => ?_,
    fun m A hA t t' u hu u' hu' => ?_, fun t u hG => ?_⟩
  · -- (i) `|Gh z − Gh z'|² = (z₀ − z'₀)² + |G(tail z) − G(tail z')|² ≤ max(1, L)²|z − z'|²`
    obtain ⟨t, u, rfl⟩ := hsurj z
    obtain ⟨t', u', rfl⟩ := hsurj z'
    rw [dist_eq_norm, dist_eq_norm, hGh, hGh, hsub, hsub]
    have hGL : ‖G u - G u'‖ ≤ L * ‖u - u'‖ := by
      simpa only [dist_eq_norm] using hL.dist_le_mul u u'
    have hM1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hML : (L : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by simp
    have hb : ‖G u - G u'‖ ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * ‖u - u'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (hGL.trans (mul_le_mul_of_nonneg_right hML (norm_nonneg _))) 2
    have hs : (t - t') ^ 2 ≤ ((max 1 L : NNReal) : ℝ) ^ 2 * (t - t') ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hM1)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hnorm, hnorm]
    linarith
  · -- (ii) `min(1, m)²|Φ(t, u) − Φ(t', u')|² ≤ (t − t')² + |G u − G u'|²`
    rw [hGh, hGh, hsub, hsub]
    rcases le_or_gt (min 1 m) 0 with hk | hk
    · exact (mul_nonpos_of_nonpos_of_nonneg hk (norm_nonneg _)).trans (norm_nonneg _)
    have hb : min 1 m ^ 2 * ‖u - u'‖ ^ 2 ≤ ‖G u - G u'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity)
        ((mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans
          (hA u hu u' hu')) 2
    have hs : min 1 m ^ 2 * (t - t') ^ 2 ≤ (t - t') ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hk.le (min_le_left _ _))
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hnorm, hnorm]
    linarith
  · -- (iii) `Gh = cs ∘ (p₀, G ∘ tl)` with continuous linear `p₀`, `tl`, `cs`
    obtain ⟨p0, hp0⟩ : ∃ p0 : Euclid (n + 1) →L[ℝ] ℝ, ∀ z, p0 z = WithLp.ofLp z 0 :=
      ⟨EuclideanSpace.proj 0, fun z => rfl⟩
    obtain ⟨tl, htl⟩ : ∃ tl : Euclid (n + 1) →L[ℝ] Euclid n,
        ∀ z, tl z = WithLp.toLp 2 (Fin.tail (WithLp.ofLp z)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun z => WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))
          map_add' := fun x y => rfl
          map_smul' := fun c x => rfl }, fun z => rfl⟩
    obtain ⟨cs, hcs⟩ : ∃ cs : ℝ × Euclid N →L[ℝ] Euclid (N + 1),
        ∀ p, cs p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :=
      ⟨LinearMap.toContinuousLinearMap
        { toFun := fun p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2))
          map_add' := fun x y => by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := fun c x => by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp }, fun p => rfl⟩
    have hGfun : Gh = fun y => cs (p0 y, G (tl y)) := by
      funext y
      obtain ⟨s, w, rfl⟩ := hsurj y
      simp [hGh, hcs, hp0, htl]
    have htlz : tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) = u := by simp [htl]
    have hD : HasFDerivAt Gh (cs.comp (p0.prod ((fderiv ℝ G u).comp tl)))
        (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u))) := by
      have hG' : HasFDerivAt G (fderiv ℝ G u) (tl (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))) := by
        rw [htlz]
        exact hG.hasFDerivAt
      rw [hGfun]
      exact cs.hasFDerivAt.comp _ (p0.hasFDerivAt.prodMk (hG'.comp _ tl.hasFDerivAt))
    have hform : ∀ (s : ℝ) (w : Euclid n),
        fderiv ℝ Gh (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp u)))
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp w))) =
          WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w))) := by
      intro s w
      rw [hD.fderiv]
      simp [hcs, hp0, htl]
    refine ⟨hD.differentiableAt, hform, fun hinjG y y' hyy => ?_, ?_, ?_⟩
    · -- injectivity
      obtain ⟨s, w, rfl⟩ := hsurj y
      obtain ⟨s', w', rfl⟩ := hsurj y'
      rw [hform, hform] at hyy
      obtain ⟨rfl, hw⟩ := hinj N s s' _ _ hyy
      rw [hinjG hw]
    · -- range
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        obtain ⟨s, w, rfl⟩ := hsurj y
        have hsplit : (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp (fderiv ℝ G u w))) : Euclid (N + 1)) =
            s • EuclideanSpace.single 0 1 +
              WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (fderiv ℝ G u w))) := by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        rw [ContinuousLinearMap.coe_coe, hform, hsplit]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨_, ⟨w, rfl⟩, rfl⟩))
      · rw [Submodule.span_le, Set.insert_subset_iff]
        refine ⟨⟨WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp (0 : Euclid n))), ?_⟩, ?_⟩
        · rw [ContinuousLinearMap.coe_coe, hform, map_zero]
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        · rintro _ ⟨v, ⟨w, rfl⟩, rfl⟩
          exact ⟨WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp w)), by
            rw [ContinuousLinearMap.coe_coe, hform]; rfl⟩
    · -- Gram determinant: block diagonal `diag(1, Gram(DG(u)c))`
      have hb0 : (EuclideanSpace.single 0 1 : Euclid (n + 1)) =
          WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp (0 : Euclid n))) := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;> simp
      have hbs : ∀ j : Fin n, (EuclideanSpace.single j.succ 1 : Euclid (n + 1)) =
          WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (EuclideanSpace.single j 1 : Euclid n))) := by
        intro j
        ext i
        refine Fin.cases ?_ (fun k => ?_) i <;> simp [PiLp.single_apply, Pi.single_apply]
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
      · simp only [Matrix.of_apply, Fin.val_zero, pow_zero, one_mul, hb0, hform, map_zero,
          hinner, inner_zero_left, mul_one, add_zero, Fin.succAbove_zero]
        congr 1
        ext i j
        simp [hbs, hform, hinner]
      · intro j _
        simp [Matrix.of_apply, hb0, hbs, hform, hinner]

/-- **The cylinder over one piece.**  Let `G : ℝⁿ → ℝᴺ` be Lipschitz, `A ⊆ ℝⁿ` Borel, `G`
injective on `A` and differentiable at every point of `A`, and `Hⁿ(G(A)) < ∞`.  Then
`Ψ(t, x) = (t, x)` carries `(L¹⌞(0, 1)) × (Hⁿ⌞G(A))` to `Hⁿ⁺¹⌞Ψ((0, 1) × G(A))`.  By
`Measure.prod_eq` it suffices that `Hⁿ⁺¹(Ψ(s × G(B))) = |s| Hⁿ(G(B))` for Borel `s ⊆ (0, 1)` and
`B ⊆ A`.  Where `DG` is injective, Mathlib's partition lemma cuts `B` into Borel pieces on which `G`
is `(1 + 2δ)`-bi-Lipschitz relative to a linear `S` with `|S h| = |DG(y) h|`; the Lipschitz image
bound compares `Hⁿ(G(P))` and `Hⁿ⁺¹(Ψ(s × G(P)))` with `Lⁿ(S(P))` and `|s| Lⁿ(S(P))`, and `δ → 0`.
Where `DG` is not injective, `G(B)` and the cylinder over it are null (Sard: on each piece `G` is
`(L + 1)`-Lipschitz relative to a linear `D` with `det D = ε`). -/
theorem Submission.dimred_mbl_dt_lp_imc_piece_measure : ∀ (N n : ℕ) (G : Euclid n → Euclid N) (A : Set (Euclid n)) (L : NNReal), LipschitzWith L G → MeasurableSet A → InjOn G A → (∀ a ∈ A, DifferentiableAt ℝ G a) → μHE[n] (G '' A) ≠ ∞ → Measure.map (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) (((volume : Measure ℝ).restrict (Ioo 0 1)).prod (μHE[n].restrict (G '' A))) = μHE[n + 1].restrict ((fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) '' (Ioo (0 : ℝ) 1 ×ˢ (G '' A))) := by
  intro N n G A L hG hA hinj hdiff hfin
  -- Step 0.  `Φ_d(t, u) = (t, u₁, …, u_d)` is a continuous bijection `ℝ × ℝᵈ → ℝᵈ⁺¹` with
  -- `|Φ_d(t, u) − Φ_d(t', u')|² = (t − t')² + |u − u'|²`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (d : ℕ) → ℝ × Euclid d → Euclid (d + 1),
      ∀ d p, Φ d p = WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :=
    ⟨fun d p => WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)), fun _ _ => rfl⟩
  have hΦfun : ∀ d, (fun p : ℝ × Euclid d =>
      (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (d + 1))) = Φ d :=
    fun d => funext fun p => (hΦ d p).symm
  rw [hΦfun N]
  have hΦc : ∀ d, Continuous (Φ d) := fun d => by
    rw [← hΦfun d]
    fun_prop
  have hΦi : ∀ d, Injective (Φ d) := by
    rintro d ⟨t, u⟩ ⟨t', u'⟩ h
    rw [hΦ, hΦ] at h
    obtain ⟨h1, h2⟩ := Fin.cons_injective2 (WithLp.toLp_injective 2 h)
    exact Prod.ext h1 (WithLp.ofLp_injective 2 h2)
  have hΦs : ∀ d, Surjective (Φ d) := fun d z =>
    ⟨(WithLp.ofLp z 0, WithLp.toLp 2 (Fin.tail (WithLp.ofLp z))), by simp [hΦ, Fin.cons_self_tail]⟩
  have hΦe : ∀ d, MeasurableEmbedding (Φ d) := fun d => (hΦc d).measurableEmbedding (hΦi d)
  have hΦsub : ∀ (d : ℕ) (t t' : ℝ) (u u' : Euclid d),
      Φ d (t, u) - Φ d (t', u') = Φ d (t - t', u - u') := by
    intro d t t' u u'
    simp only [hΦ]
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hΦinner : ∀ (d : ℕ) (s s' : ℝ) (v v' : Euclid d),
      inner ℝ (Φ d (s, v)) (Φ d (s', v')) = s * s' + inner ℝ v v' := by
    intro d s s' v v'
    simp [hΦ, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm]
  have hΦnorm : ∀ (d : ℕ) (t : ℝ) (u : Euclid d), ‖Φ d (t, u)‖ ^ 2 = t ^ 2 + ‖u‖ ^ 2 := by
    intro d t u
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hΦinner, sq]
  -- a `K`-Lipschitz comparison `y ↔ x` (`K ≥ 1`) extends to the cylinders `Φ(t, y) ↔ Φ(t, x)`
  have hcyl : ∀ (d₁ d₂ : ℕ) (K t t' : ℝ) (x x' : Euclid d₁) (y y' : Euclid d₂), 1 ≤ K →
      ‖y - y'‖ ≤ K * ‖x - x'‖ → ‖Φ d₂ (t, y) - Φ d₂ (t', y')‖ ≤ K * ‖Φ d₁ (t, x) - Φ d₁ (t', x')‖ := by
    intro d₁ d₂ K t t' x x' y y' hK hyx
    rw [hΦsub, hΦsub]
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hΦnorm, hΦnorm]
    have h1 : ‖y - y'‖ ^ 2 ≤ K ^ 2 * ‖x - x'‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hyx 2
    have h2 : (t - t') ^ 2 ≤ K ^ 2 * (t - t') ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hK)
    linarith
  have himgprod : ∀ (d d' : ℕ) (f : Euclid d → Euclid d') (s : Set ℝ) (P : Set (Euclid d)),
      (fun p : ℝ × Euclid d => Φ d' (p.1, f p.2)) '' (s ×ˢ P) = Φ d' '' (s ×ˢ (f '' P)) := by
    intro d d' f s P
    ext z
    simp only [mem_image, mem_prod, Prod.exists]
    constructor
    · rintro ⟨t, a, ⟨ht, ha⟩, rfl⟩
      exact ⟨t, f a, ⟨ht, a, ha, rfl⟩, rfl⟩
    · rintro ⟨t, _, ⟨ht, a, ha, rfl⟩, rfl⟩
      exact ⟨t, a, ⟨ht, ha⟩, rfl⟩
  -- `Hᵈ` is Lebesgue measure on `ℝᵈ`, and `Φ_n` carries `L¹ × Lⁿ` to `Lⁿ⁺¹`
  have hvol : ∀ d : ℕ, (μHE[d] : Measure (Euclid d)) = volume := fun d =>
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume d
  have hΦmp : MeasurePreserving (Φ n) := by
    have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (WithLp.ofLp : Euclid n → (Fin n → ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (Euclid n)))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) :=
      (MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin n))
    have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        (volume : Measure (Fin (n + 1) → ℝ)) :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have h3 := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp (h2.comp h1)
    rw [← hΦfun n]
    convert h3 using 1
    funext p
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have hvolΦ : ∀ (s : Set ℝ) (Q : Set (Euclid n)),
      μHE[n + 1] (Φ n '' (s ×ˢ Q)) = volume s * μHE[n] Q := by
    intro s Q
    rw [hvol (n + 1), hvol n, ← hΦmp.map_eq, (hΦe n).map_apply, preimage_image_eq _ (hΦi n),
      Measure.volume_eq_prod, Measure.prod_prod]
  -- Comparison of images: if `|v a − v a'| ≤ K|u a − u a'|` on `P`, then `Hᵈ(v(P)) ≤ Kᵈ Hᵈ(u(P))`
  have hcomp : ∀ (α : Type) (k₁ k₂ d : ℕ) (u : α → Euclid k₁) (v : α → Euclid k₂) (P : Set α)
      (K : NNReal), (∀ a ∈ P, ∀ a' ∈ P, ‖v a - v a'‖ ≤ K * ‖u a - u a'‖) →
      μHE[d] (v '' P) ≤ (K : ℝ≥0∞) ^ d * μHE[d] (u '' P) := by
    intro α k₁ k₂ d u v P K h
    rcases P.eq_empty_or_nonempty with hP | ⟨a₀, -⟩
    · simp [hP]
    have : Nonempty α := ⟨a₀⟩
    set g := Function.invFunOn u P
    have hg : ∀ y ∈ u '' P, g y ∈ P ∧ u (g y) = y :=
      fun y hy => ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
    have hLip : LipschitzOnWith K (v ∘ g) (u '' P) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      obtain ⟨hgy, huy⟩ := hg y hy
      obtain ⟨hgy', huy'⟩ := hg y' hy'
      simp only [comp_apply, dist_eq_norm]
      calc ‖v (g y) - v (g y')‖ ≤ K * ‖u (g y) - u (g y')‖ := h _ hgy _ hgy'
        _ = K * ‖y - y'‖ := by rw [huy, huy']
    have hsub : v '' P ⊆ (v ∘ g) '' (u '' P) := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨u a, mem_image_of_mem u ha, ?_⟩
      obtain ⟨hga, hua⟩ := hg (u a) (mem_image_of_mem u ha)
      have := h _ hga _ ha
      rw [hua, sub_self, norm_zero, mul_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    exact (measure_mono hsub).trans
      (Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn d hLip)
  -- Limits `ε → 0` and `δ → 0`
  have hlim0 : ∀ x C : ℝ≥0∞, C ≠ ∞ → (∀ ε : NNReal, 0 < ε → ε ≤ 1 → x ≤ C * ε) → x = 0 := by
    intro x C hC h
    have h0 : Tendsto (fun ε : NNReal => (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
      rw [← ENNReal.coe_zero]
      exact (ENNReal.tendsto_coe.mpr tendsto_id).mono_left nhdsWithin_le_nhds
    have htend : Tendsto (fun ε : NNReal => C * (ε : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul h0 (Or.inr hC)
    refine le_antisymm (ge_of_tendsto htend ?_) bot_le
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' NNReal)] with ε hε
    exact h ε hε.1 hε.2
  have hlim1 : ∀ (x y : ℝ≥0∞) (m : ℕ),
      (∀ δ : NNReal, 0 < δ → δ ≤ 1 / 2 → x ≤ ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ m * y) → x ≤ y := by
    intro x y m h
    have h1 : Tendsto (fun δ : NNReal => (((1 + 2 * δ) ^ m : NNReal) : ℝ≥0∞)) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous fun δ : NNReal => (1 + 2 * δ) ^ m := by fun_prop
      rw [← ENNReal.coe_one]
      exact ENNReal.tendsto_coe.mpr ((hc.tendsto' 0 1 (by simp)).mono_left nhdsWithin_le_nhds)
    have htend : Tendsto (fun δ : NNReal => (((1 + 2 * δ) ^ m : NNReal) : ℝ≥0∞) * y) (𝓝[>] 0)
        (𝓝 y) := by
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    refine ge_of_tendsto htend ?_
    filter_upwards [Ioc_mem_nhdsGT (show (0 : NNReal) < 1 / 2 by norm_num)] with δ hδ
    rw [ENNReal.coe_pow]
    exact h δ hδ.1 hδ.2
  -- Step 1.  Linear algebra: coercivity `c(T)|h| ≤ |T h|` and an `S` with `|S h| = |T h|` for
  -- injective `T`
  have hcoer : ∀ T : Euclid n →L[ℝ] Euclid N, ∃ c : NNReal, 0 < c ∧
      (Injective T → ∀ h, (c : ℝ) * ‖h‖ ≤ ‖T h‖) := by
    intro T
    by_cases hT : Injective T
    · obtain ⟨C, Cpos, hC⟩ := T.injective_iff_antilipschitz.mp hT
      refine ⟨C⁻¹, inv_pos.mpr Cpos, fun _ h => ?_⟩
      have hb := T.bound_of_antilipschitz hC h
      have hC0 : (0 : ℝ) < C := Cpos
      rw [NNReal.coe_inv]
      calc (C : ℝ)⁻¹ * ‖h‖ ≤ (C : ℝ)⁻¹ * (C * ‖T h‖) := by gcongr
        _ = ‖T h‖ := by field_simp
    · exact ⟨1, one_pos, fun h => absurd h hT⟩
  choose c hcpos hc using hcoer
  have hiso : ∀ T : Euclid n →L[ℝ] Euclid N, ∃ S : Euclid n →ₗ[ℝ] Euclid n,
      Injective T → ∀ h, ‖S h‖ = ‖T h‖ := by
    intro T
    by_cases hT : Injective T
    · have hr : Module.finrank ℝ (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid N)) = n := by
        rw [LinearMap.finrank_range_of_inj hT, finrank_euclideanSpace_fin]
      let e := (stdOrthonormalBasis ℝ (LinearMap.range (T : Euclid n →ₗ[ℝ] Euclid N))).repr.trans
        (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hr))
      refine ⟨e.toLinearEquiv.toLinearMap ∘ₗ (T : Euclid n →ₗ[ℝ] Euclid N).rangeRestrict,
        fun _ h => ?_⟩
      rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        LinearIsometryEquiv.norm_map]
      rfl
    · exact ⟨0, fun h => absurd h hT⟩
  choose S hS using hiso
  -- Step 2.  Regular part: for Borel `X ⊆ A` on which `DG` is injective,
  -- `Hⁿ⁺¹(Φ_N(s × G(X))) = |s| Hⁿ(G(X))`
  have hreg : ∀ (X : Set (Euclid n)) (s : Set ℝ), MeasurableSet X → MeasurableSet s → X ⊆ A →
      (∀ a ∈ X, Injective (fderiv ℝ G a)) →
      μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) = volume s * μHE[n] (G '' X) := by
    intro X s hX hs hXA hXi
    rcases X.eq_empty_or_nonempty with hXe | hXne
    · simp [hXe]
    have hbound : ∀ δ : NNReal, 0 < δ → δ ≤ 1 / 2 →
        μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) ≤
            ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' X)) ∧
          volume s * μHE[n] (G '' X) ≤
            ((1 + 2 * δ : NNReal) : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) := by
      intro δ hδ hδ2
      set K : NNReal := 1 + 2 * δ with hKdef
      have hδ0 : (0 : ℝ) ≤ δ := NNReal.coe_nonneg δ
      have hδ' : (δ : ℝ) ≤ 1 / 2 := by exact_mod_cast hδ2
      have hK1 : (1 : ℝ) ≤ K := by
        rw [hKdef]
        push_cast
        linarith
      -- Mathlib's partition of `X` into Borel pieces on which `G` is `δ c(T)`-close to `T = DG(y)`
      obtain ⟨t, T, htdisj, htmeas, hXt, hT, hTy⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G X (fderiv ℝ G)
          (fun x hx => (hdiff x (hXA hx)).hasFDerivAt.hasFDerivWithinAt) (fun T => δ * c T)
          (fun T => (mul_pos hδ (hcpos T)).ne')
      -- on each piece `G` is `K`-bi-Lipschitz relative to `S(T)`, so both `Hⁿ(G(P))` and
      -- `Hⁿ⁺¹(Φ_N(s × G(P)))` are within `K^{2n+1}` of `Lⁿ(S P)` resp. `|s| Lⁿ(S P)`
      have hpiece : ∀ k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) ≤
            (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) ∧
          volume s * μHE[n] (G '' (X ∩ t k)) ≤
            (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
        intro k
        obtain ⟨y, hy, hTk⟩ := hTy hXne k
        have hTinj : Injective (T k) := hTk ▸ hXi y hy
        have hST : ∀ a a', ‖S (T k) a - S (T k) a'‖ = ‖T k (a - a')‖ := fun a a' => by
          rw [← map_sub, hS (T k) hTinj]
        have happ : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖G a - G a' - T k (a - a')‖ ≤ δ * ‖T k (a - a')‖ := by
          intro a ha a' ha'
          have h1 := hT k a ha a' ha'
          have h2 := hc (T k) hTinj (a - a')
          simp only [NNReal.coe_mul] at h1
          calc ‖G a - G a' - T k (a - a')‖ ≤ δ * c (T k) * ‖a - a'‖ := h1
            _ = δ * (c (T k) * ‖a - a'‖) := by ring
            _ ≤ δ * ‖T k (a - a')‖ := by gcongr
        have hGS : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖G a - G a'‖ ≤ K * ‖S (T k) a - S (T k) a'‖ := by
          intro a ha a' ha'
          have h1 := happ a ha a' ha'
          have h2 := norm_sub_norm_le (G a - G a') (T k (a - a'))
          rw [hST, hKdef]
          push_cast
          linarith [mul_nonneg hδ0 (norm_nonneg (T k (a - a')))]
        have hSG : ∀ a ∈ X ∩ t k, ∀ a' ∈ X ∩ t k,
            ‖S (T k) a - S (T k) a'‖ ≤ K * ‖G a - G a'‖ := by
          intro a ha a' ha'
          have h1 := happ a ha a' ha'
          have h2 := norm_sub_norm_le (T k (a - a')) (G a - G a')
          rw [norm_sub_rev (T k (a - a'))] at h2
          rw [hST, hKdef]
          push_cast
          have h3 : (1 - (δ : ℝ)) * ‖T k (a - a')‖ ≤ ‖G a - G a'‖ := by linarith
          have h4 : (1 + 2 * (δ : ℝ)) * ((1 - δ) * ‖T k (a - a')‖) ≤
              (1 + 2 * (δ : ℝ)) * ‖G a - G a'‖ :=
            mul_le_mul_of_nonneg_left h3 (by linarith)
          have h5 : 0 ≤ (δ : ℝ) * (1 - 2 * δ) * ‖T k (a - a')‖ :=
            mul_nonneg (mul_nonneg hδ0 (by linarith)) (norm_nonneg _)
          linarith
        have ha := hcomp (Euclid n) n N n (S (T k)) G (X ∩ t k) K hGS
        have hb := hcomp (Euclid n) N n n G (S (T k)) (X ∩ t k) K hSG
        have hc1 := hcomp (ℝ × Euclid n) (n + 1) (N + 1) (n + 1)
          (fun p => Φ n (p.1, S (T k) p.2)) (fun p => Φ N (p.1, G p.2)) (s ×ˢ (X ∩ t k)) K
          (fun p hp p' hp' => hcyl n N K p.1 p'.1 _ _ _ _ hK1 (hGS _ hp.2 _ hp'.2))
        have hd1 := hcomp (ℝ × Euclid n) (N + 1) (n + 1) (n + 1)
          (fun p => Φ N (p.1, G p.2)) (fun p => Φ n (p.1, S (T k) p.2)) (s ×ˢ (X ∩ t k)) K
          (fun p hp p' hp' => hcyl N n K p.1 p'.1 _ _ _ _ hK1 (hSG _ hp.2 _ hp'.2))
        rw [himgprod n N G, himgprod n n (S (T k)), hvolΦ] at hc1
        rw [himgprod n N G, himgprod n n (S (T k)), hvolΦ] at hd1
        constructor
        · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k))))
              ≤ (K : ℝ≥0∞) ^ (n + 1) * (volume s * μHE[n] (S (T k) '' (X ∩ t k))) := hc1
            _ ≤ (K : ℝ≥0∞) ^ (n + 1) * (volume s * ((K : ℝ≥0∞) ^ n * μHE[n] (G '' (X ∩ t k)))) := by
              gcongr
            _ = (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) := by ring
        · calc volume s * μHE[n] (G '' (X ∩ t k))
              ≤ volume s * ((K : ℝ≥0∞) ^ n * μHE[n] (S (T k) '' (X ∩ t k))) := by gcongr
            _ = (K : ℝ≥0∞) ^ n * (volume s * μHE[n] (S (T k) '' (X ∩ t k))) := by ring
            _ ≤ (K : ℝ≥0∞) ^ n * ((K : ℝ≥0∞) ^ (n + 1) *
                μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k))))) := by gcongr
            _ = (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by ring
      -- sum over the pieces: the images are Borel (Lusin–Souslin) and disjoint (`G` is injective)
      have hGPmeas : ∀ k, MeasurableSet (G '' (X ∩ t k)) := fun k =>
        (hX.inter (htmeas k)).image_of_continuousOn_injOn hG.continuous.continuousOn
          (hinj.mono (inter_subset_left.trans hXA))
      have hCPmeas : ∀ k, MeasurableSet (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := fun k =>
        (hΦe N).measurableSet_image.2 (hs.prod (hGPmeas k))
      have hGPdisj : Pairwise (Disjoint on fun k => G '' (X ∩ t k)) := by
        intro i j hij
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
        have hba : b = a := hinj (hXA hb.1) (hXA ha.1) hab
        exact Set.disjoint_left.mp (htdisj hij) ha.2 (hba ▸ hb.2)
      have hCPdisj : Pairwise (Disjoint on fun k => Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
        intro i j hij
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
        have hqp' : q = p := hΦi N hqp
        subst hqp'
        exact Set.disjoint_left.mp (hGPdisj hij) hp.2 hq.2
      have hGU : G '' X = ⋃ k, G '' (X ∩ t k) := by
        rw [← image_iUnion, ← inter_iUnion, inter_eq_left.mpr hXt]
      have hCU : Φ N '' (s ×ˢ (G '' X)) = ⋃ k, Φ N '' (s ×ˢ (G '' (X ∩ t k))) := by
        rw [hGU, prod_iUnion, image_iUnion]
      constructor
      · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' X)))
            = ∑' k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) := by
              rw [hCU, measure_iUnion hCPdisj hCPmeas]
          _ ≤ ∑' k, (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' (X ∩ t k))) :=
              ENNReal.tsum_le_tsum fun k => (hpiece k).1
          _ = (K : ℝ≥0∞) ^ (2 * n + 1) * (volume s * μHE[n] (G '' X)) := by
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hGU,
                measure_iUnion hGPdisj hGPmeas]
      · calc volume s * μHE[n] (G '' X) = ∑' k, volume s * μHE[n] (G '' (X ∩ t k)) := by
              rw [ENNReal.tsum_mul_left, hGU, measure_iUnion hGPdisj hGPmeas]
          _ ≤ ∑' k, (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ t k)))) :=
              ENNReal.tsum_le_tsum fun k => (hpiece k).2
          _ = (K : ℝ≥0∞) ^ (2 * n + 1) * μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) := by
              rw [ENNReal.tsum_mul_left, hCU, measure_iUnion hCPdisj hCPmeas]
    exact le_antisymm (hlim1 _ _ _ fun δ hδ hδ2 => (hbound δ hδ hδ2).1)
      (hlim1 _ _ _ fun δ hδ hδ2 => (hbound δ hδ hδ2).2)
  -- Step 3.  Critical part (Sard): for Borel `X ⊆ A` on which `DG` is not injective, `G(X)` and
  -- the cylinder over it are null.  On a piece where `G` is `ε`-close to a rank-deficient `T`
  -- (`Tv = 0`, `|v| = 1`), `|G a − G a'| ≤ (L + 1)|D a − D a'|` for `D = id − (1 − ε) v ⊗ v`,
  -- and `det D = ε`.
  have hcrit : ∀ (X : Set (Euclid n)) (s : Set ℝ), MeasurableSet X → X ⊆ A →
      (∀ a ∈ X, ¬ Injective (fderiv ℝ G a)) → volume s ≠ ∞ →
      μHE[n] (G '' X) = 0 ∧ μHE[n + 1] (Φ N '' (s ×ˢ (G '' X))) = 0 := by
    intro X s hX hXA hXi hs
    have hR : ∀ R : ℕ, μHE[n] (G '' (X ∩ ball 0 R)) = 0 ∧
        μHE[n + 1] (Φ N '' (s ×ˢ (G '' (X ∩ ball 0 R)))) = 0 := by
      intro R
      set Y := X ∩ ball (0 : Euclid n) R with hYdef
      have hYmeas : MeasurableSet Y := hX.inter measurableSet_ball
      have hbound : ∀ ε : NNReal, 0 < ε → ε ≤ 1 →
          μHE[n] (G '' Y) ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε ∧
          μHE[n + 1] (Φ N '' (s ×ˢ (G '' Y))) ≤
            ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) * ε := by
        intro ε hε hε1
        rcases Y.eq_empty_or_nonempty with hYe | hYne
        · simp [hYe]
        obtain ⟨t, T, htdisj, htmeas, hYt, hT, hTy⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt G Y (fderiv ℝ G)
            (fun x hx => (hdiff x (hXA hx.1)).hasFDerivAt.hasFDerivWithinAt) (fun _ => ε)
            (fun _ => hε.ne')
        have hpiece : ∀ k, μHE[n] (G '' (Y ∩ t k)) ≤
              ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε ∧
            μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k)))) ≤
              ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε := by
          intro k
          obtain ⟨y, hy, hTk⟩ := hTy hYne k
          have hTnorm : ‖T k‖ ≤ L := hTk ▸ norm_fderiv_le_of_lipschitz ℝ hG
          have hTni : ¬ Injective (T k) := hTk ▸ hXi y hy.1
          obtain ⟨v, hv1, hv0⟩ : ∃ v : Euclid n, ‖v‖ = 1 ∧ T k v = 0 := by
            simp only [Injective, not_forall] at hTni
            obtain ⟨a, b, hab, hne⟩ := hTni
            have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
            refine ⟨‖a - b‖⁻¹ • (a - b), norm_smul_inv_norm hne', ?_⟩
            rw [map_smul, map_sub, hab, sub_self, smul_zero]
          set c₀ : ℝ := 1 - (ε : ℝ) with hc₀
          have hc₀0 : 0 ≤ c₀ := by
            rw [hc₀]; linarith [show (ε : ℝ) ≤ 1 from hε1]
          set D : Euclid n →L[ℝ] Euclid n :=
            ContinuousLinearMap.id ℝ (Euclid n) - c₀ • (innerSL ℝ v).smulRight v with hD
          have hDapp : ∀ h, D h = h - (c₀ * inner ℝ v h) • v := by
            intro h
            simp [hD, mul_smul]
          have hTD : ∀ h, T k (D h) = T k h := by
            intro h
            rw [hDapp, map_sub, map_smul, hv0, smul_zero, sub_zero]
          have hinD : ∀ h, inner ℝ v (D h) = (ε : ℝ) * inner ℝ v h := by
            intro h
            rw [hDapp, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv1, hc₀]
            ring
          have hεD : ∀ h, (ε : ℝ) * ‖h‖ ≤ ‖D h‖ := by
            intro h
            have heq : (ε : ℝ) • h = (ε : ℝ) • D h + (c₀ * inner ℝ v (D h)) • v := by
              rw [hinD, hDapp, smul_sub, ← sub_eq_zero]
              rw [hc₀]
              module
            calc (ε : ℝ) * ‖h‖ = ‖(ε : ℝ) • h‖ := by
                  rw [norm_smul, NNReal.norm_eq]
              _ ≤ ‖(ε : ℝ) • D h‖ + ‖(c₀ * inner ℝ v (D h)) • v‖ := heq ▸ norm_add_le _ _
              _ ≤ (ε : ℝ) * ‖D h‖ + c₀ * ‖D h‖ := by
                  gcongr
                  · rw [norm_smul, NNReal.norm_eq]
                  · rw [norm_smul, hv1, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg hc₀0]
                    gcongr
                    exact (abs_real_inner_le_norm v (D h)).trans (by rw [hv1, one_mul])
              _ = ‖D h‖ := by rw [hc₀]; ring
          have hGD : ∀ a ∈ Y ∩ t k, ∀ a' ∈ Y ∩ t k,
              ‖G a - G a'‖ ≤ ((L + 1 : NNReal) : ℝ) * ‖D a - D a'‖ := by
            intro a ha a' ha'
            have h1 := hT k a ha a' ha'
            have h2 : ‖T k (a - a')‖ ≤ L * ‖D a - D a'‖ := by
              rw [← map_sub, ← hTD (a - a')]
              exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
            have h3 : (ε : ℝ) * ‖a - a'‖ ≤ ‖D a - D a'‖ := by
              rw [← map_sub]
              exact hεD (a - a')
            have h4 := norm_sub_norm_le (G a - G a') (T k (a - a'))
            push_cast
            linarith
          have hdet : LinearMap.det (D : Euclid n →ₗ[ℝ] Euclid n) = ε := by
            rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
            have hM : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
                (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (D : Euclid n →ₗ[ℝ] Euclid n) =
                1 + Matrix.replicateCol Unit (fun i => -c₀ * v i) *
                  Matrix.replicateRow Unit (fun j => v j) := by
              ext i j
              simp [hD, LinearMap.toMatrix_apply, Matrix.one_apply,
                EuclideanSpace.inner_single_right, Matrix.mul_apply, Matrix.replicateCol_apply,
                Matrix.replicateRow_apply]
              ring
            rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
            have h2 : ∑ i, v i ^ 2 = 1 := by
              have := EuclideanSpace.norm_sq_eq v
              simp only [hv1, one_pow, Real.norm_eq_abs, sq_abs] at this
              exact this.symm
            simp only [dotProduct]
            calc 1 + ∑ i, v i * (-c₀ * v i) = 1 - c₀ * ∑ i, v i ^ 2 := by
                  rw [Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
                  exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)
              _ = ε := by rw [h2, mul_one, hc₀]; ring
          have hDvol : ∀ Q : Set (Euclid n), μHE[n] (D '' Q) = volume Q * ε := by
            intro Q
            rw [hvol n, MeasureTheory.Measure.addHaar_image_continuousLinearMap, hdet,
              NNReal.abs_eq, ENNReal.ofReal_coe_nnreal, mul_comm]
          have h1 := hcomp (Euclid n) n N n D G (Y ∩ t k) (L + 1) hGD
          have h2 := hcomp (ℝ × Euclid n) (n + 1) (N + 1) (n + 1)
            (fun p => Φ n (p.1, D p.2)) (fun p => Φ N (p.1, G p.2)) (s ×ˢ (Y ∩ t k)) (L + 1)
            (fun p hp p' hp' => hcyl n N _ p.1 p'.1 _ _ _ _
              (by have := NNReal.coe_nonneg L; push_cast; linarith) (hGD _ hp.2 _ hp'.2))
          rw [hDvol] at h1
          rw [himgprod n N G, himgprod n n D, hvolΦ, hDvol] at h2
          constructor
          · calc μHE[n] (G '' (Y ∩ t k))
                ≤ ((L + 1 : NNReal) : ℝ≥0∞) ^ n * (volume (Y ∩ t k) * ε) := h1
              _ = ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε := by push_cast; ring
          · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k))))
                ≤ ((L + 1 : NNReal) : ℝ≥0∞) ^ (n + 1) * (volume s * (volume (Y ∩ t k) * ε)) := h2
              _ = ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε := by
                push_cast; ring
        have hvolU : ∑' k, volume (Y ∩ t k) ≤ volume (ball (0 : Euclid n) R) := by
          rw [← measure_iUnion (fun i j hij => (htdisj hij).mono inter_subset_right inter_subset_right)
            (fun k => hYmeas.inter (htmeas k))]
          exact measure_mono (iUnion_subset fun k => inter_subset_left.trans inter_subset_right)
        constructor
        · calc μHE[n] (G '' Y) ≤ ∑' k, μHE[n] (G '' (Y ∩ t k)) := by
                refine (measure_mono ?_).trans (measure_iUnion_le _)
                rintro _ ⟨a, ha, rfl⟩
                obtain ⟨k, hk⟩ := mem_iUnion.mp (hYt ha)
                exact mem_iUnion.mpr ⟨k, a, ⟨ha, hk⟩, rfl⟩
            _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ n * volume (Y ∩ t k) * ε :=
                ENNReal.tsum_le_tsum fun k => (hpiece k).1
            _ = ((L : ℝ≥0∞) + 1) ^ n * (∑' k, volume (Y ∩ t k)) * ε := by
                rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
            _ ≤ ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) * ε := by gcongr
        · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' Y)))
              ≤ ∑' k, μHE[n + 1] (Φ N '' (s ×ˢ (G '' (Y ∩ t k)))) := by
                refine (measure_mono ?_).trans (measure_iUnion_le _)
                rintro _ ⟨⟨τ, x⟩, ⟨hτ, a, ha, rfl⟩, rfl⟩
                obtain ⟨k, hk⟩ := mem_iUnion.mp (hYt ha)
                exact mem_iUnion.mpr ⟨k, ⟨τ, G a⟩, ⟨hτ, a, ⟨ha, hk⟩, rfl⟩, rfl⟩
            _ ≤ ∑' k, ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (Y ∩ t k)) * ε :=
                ENNReal.tsum_le_tsum fun k => (hpiece k).2
            _ = ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * ∑' k, volume (Y ∩ t k)) * ε := by
                rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
            _ ≤ ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) * ε := by
                gcongr
      have hfin1 : ((L : ℝ≥0∞) + 1) ^ n * volume (ball (0 : Euclid n) R) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) measure_ball_lt_top.ne
      have hfin2 : ((L : ℝ≥0∞) + 1) ^ (n + 1) * (volume s * volume (ball (0 : Euclid n) R)) ≠ ∞ :=
        ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp))
          (ENNReal.mul_ne_top hs measure_ball_lt_top.ne)
      exact ⟨hlim0 _ _ hfin1 fun ε hε hε1 => (hbound ε hε hε1).1,
        hlim0 _ _ hfin2 fun ε hε hε1 => (hbound ε hε hε1).2⟩
    constructor
    · refine measure_mono_null ?_ (measure_iUnion_null fun R => (hR R).1)
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
      exact mem_iUnion.mpr ⟨R, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩
    · refine measure_mono_null ?_ (measure_iUnion_null fun R => (hR R).2)
      rintro _ ⟨⟨τ, x⟩, ⟨hτ, a, ha, rfl⟩, rfl⟩
      obtain ⟨R, hR'⟩ := exists_nat_gt ‖a‖
      exact mem_iUnion.mpr ⟨R, ⟨τ, G a⟩, ⟨hτ, a, ⟨ha, mem_ball_zero_iff.mpr hR'⟩, rfl⟩, rfl⟩
  -- Step 4.  Both parts: `Hⁿ⁺¹(Φ_N(s × G(B))) = |s| Hⁿ(G(B))` for Borel `B ⊆ A`, `|s| < ∞`
  have hmeasI : MeasurableSet {a : Euclid n | Injective (fderiv ℝ G a)} :=
    measurable_fderiv ℝ G ContinuousLinearMap.isOpen_injective.measurableSet
  have hcore : ∀ (s : Set ℝ) (B : Set (Euclid n)), MeasurableSet s → volume s ≠ ∞ →
      MeasurableSet B → B ⊆ A →
      μHE[n + 1] (Φ N '' (s ×ˢ (G '' B))) = volume s * μHE[n] (G '' B) := by
    intro s B hs hsfin hB hBA
    obtain ⟨hc1, hc2⟩ := hcrit (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ) s (hB.inter hmeasI.compl)
      (inter_subset_left.trans hBA) (fun a ha => ha.2) hsfin
    have hr := hreg (B ∩ {a | Injective (fderiv ℝ G a)}) s (hB.inter hmeasI) hs
      (inter_subset_left.trans hBA) (fun a ha => ha.2)
    have hGB : G '' B = G '' (B ∩ {a | Injective (fderiv ℝ G a)}) ∪
        G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ) := by
      rw [← image_union, inter_union_compl]
    apply le_antisymm
    · calc μHE[n + 1] (Φ N '' (s ×ˢ (G '' B)))
          ≤ μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)})))) +
            μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ)))) := by
            rw [hGB, prod_union, image_union]
            exact measure_union_le _ _
        _ = volume s * μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)})) := by
            rw [hc2, add_zero, hr]
        _ ≤ volume s * μHE[n] (G '' B) :=
            mul_le_mul' le_rfl (measure_mono (image_mono inter_subset_left))
    · calc volume s * μHE[n] (G '' B)
          ≤ volume s * (μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)})) +
            μHE[n] (G '' (B ∩ {a | Injective (fderiv ℝ G a)}ᶜ))) := by
            rw [hGB]
            exact mul_le_mul' le_rfl (measure_union_le _ _)
        _ = μHE[n + 1] (Φ N '' (s ×ˢ (G '' (B ∩ {a | Injective (fderiv ℝ G a)})))) := by
            rw [hc1, add_zero, hr]
        _ ≤ μHE[n + 1] (Φ N '' (s ×ˢ (G '' B))) :=
            measure_mono (image_mono (prod_mono subset_rfl (image_mono inter_subset_left)))
  -- Step 5.  Both measures agree on rectangles (`Measure.prod_eq`); push forward by `Φ_N`
  have hEmeas : MeasurableSet (G '' A) :=
    hA.image_of_continuousOn_injOn hG.continuous.continuousOn hinj
  have : IsFiniteMeasure (μHE[n].restrict (G '' A)) := isFiniteMeasure_restrict.mpr hfin
  have hprod : ((volume : Measure ℝ).restrict (Ioo 0 1)).prod (μHE[n].restrict (G '' A)) =
      Measure.comap (Φ N) (μHE[n + 1].restrict (Φ N '' (Ioo 0 1 ×ˢ (G '' A)))) := by
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [(hΦe N).comap_apply, Measure.restrict_apply ((hΦe N).measurableSet_image.2 (hs.prod ht)),
      ← image_inter (hΦi N), prod_inter_prod, Measure.restrict_apply hs, Measure.restrict_apply ht,
      inter_comm t (G '' A), ← image_inter_preimage]
    exact hcore _ _ (hs.inter measurableSet_Ioo)
      ((measure_mono inter_subset_right).trans_lt measure_Ioo_lt_top).ne
      (hA.inter (hG.continuous.measurable ht)) inter_subset_left
  rw [hprod, (hΦe N).map_comap, (hΦs N).range_eq, Measure.restrict_univ]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
