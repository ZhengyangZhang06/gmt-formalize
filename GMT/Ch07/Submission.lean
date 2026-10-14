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

/-- **Simon 6.5.1** (proof, (31): `Lⁿ` of the interior of a unit face is `1`): the open unit cube
`{y : 0 < yᵢ < 1}` of `ℝᵏ` has volume `1`.  It is the preimage of the box `∏ᵢ (0, 1)` under the
volume-preserving `ofLp : ℝᵏ → (Fin k → ℝ)`, and the box has volume `∏ᵢ (1 - 0) = 1` (the empty
product if `k = 0`). -/
theorem Submission.cmcdtfrfg_cube_volume : ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro k
  -- the box `∏ᵢ (0, 1)` in `Fin k → ℝ`
  have hB : MeasurableSet (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  -- the cube is `ofLp⁻¹` of the box
  have hpre : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  rw [hpre, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp
/-- **Coordinates of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face of the
cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P`, `b ∈ ℤᴾ`, `y ∈ ℝᵏ` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)}`: coordinates are additive and linear and `(eᵢ)ₗ = [l = i]`, so
`Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`.  At `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`,
giving `b_{ι(m)} + yₘ`; for `l` outside the range of `ι` every summand vanishes, giving `bₗ`. -/
theorem Submission.cmcdtfrfg_face_coord : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ) (y : Euclid k), Function.Injective ι → (∀ m, (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (ι m) = (b (ι m) : ℝ) + y m) ∧ (∀ l, (∀ m, ι m ≠ l) → (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l = (b l : ℝ)) := by
  intro P k ι b y hι
  -- steps 1-2: `Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`
  have hcoord : ∀ l : Fin P, (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) l =
      (b l : ℝ) + ∑ j, if ι j = l then y j else 0 := by
    intro l
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact if_congr eq_comm rfl rfl
  refine ⟨fun m => ?_, fun l hl => ?_⟩
  -- step 3: at `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`
  · rw [hcoord, Fintype.sum_eq_single m fun j hj => ite_eq_right (hι.ne hj), ite_eq_left rfl]
  -- step 4: for `l` outside the range of `ι` every summand vanishes
  · rw [hcoord, Finset.sum_eq_zero fun j _ => ite_eq_right (hl j), add_zero]

/-- **Isometry and diameter of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face
of the cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P` and `b ∈ ℤᴾ`, the
map `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry `ℝᵏ → ℝᴾ`: by `face_coord` the coordinate gap of
`Φ(y)` and `Φ(y')` is `yₘ - y'ₘ` at `ι(m)` and `0` off the range of `ι`, so reindexing the sum of
squared gaps along `ι` gives `|Φ(y) - Φ(y')| = |y - y'|`.  On the closed unit cube every squared gap
is at most `1`, so `|y - y'| ≤ √k ≤ √P`, as `k ≤ P` by injectivity of `ι`. -/
theorem Submission.cmcdtfrfg_face_isometry_diam : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ), Function.Injective ι → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) ≤ Real.sqrt P) := by
  intro P k ι b hι
  -- (a), steps 1-5: `|Φ(y) - Φ(y')|² = Σₗ |Φ(y)ₗ - Φ(y')ₗ|² = Σₘ |yₘ - y'ₘ|² = |y - y'|²`
  have hiso : ∀ y y' : Euclid k,
      dist (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) =
      dist y y' := by
    intro y y'
    -- step 2: the coordinates of `Φ(y)` and `Φ(y')`
    obtain ⟨hy, hyc⟩ := Submission.cmcdtfrfg_face_coord P k ι b y hι
    obtain ⟨hy', hy'c⟩ := Submission.cmcdtfrfg_face_coord P k ι b y' hι
    rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
    congr 1
    -- steps 3-4: reindex the sum of squared gaps along the injective `ι`
    symm
    refine Fintype.sum_of_injective ι hι _ _ (fun l hl => ?_) fun m => ?_
    -- off the range of `ι` the gap is `bₗ - bₗ = 0`
    · have hl' : ∀ m, ι m ≠ l := fun m hm => hl ⟨m, hm⟩
      rw [hyc l hl', hy'c l hl', dist_self, sq, mul_zero]
    -- at `ι(m)` the gap is `(b_{ι(m)} + yₘ) - (b_{ι(m)} + y'ₘ) = yₘ - y'ₘ`
    · rw [hy m, hy' m, dist_add_left]
  refine ⟨hiso, fun y y' hy hy' => ?_⟩
  -- (b), step 6: on the unit cube `-1 ≤ yₘ - y'ₘ ≤ 1`, so every squared gap is at most `1`
  have hgap : ∀ m, dist (y m) (y' m) ^ 2 ≤ 1 := by
    intro m
    obtain ⟨hy₀, hy₁⟩ := hy m
    obtain ⟨hy'₀, hy'₁⟩ := hy' m
    rw [Real.dist_eq, sq_abs, sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  -- step 7: `k = #(Fin k) ≤ #(Fin P) = P`, as `ι` is injective
  have hkP : k ≤ P := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ι hι
  -- step 8: `|Φ(y) - Φ(y')| = |y - y'| = √(Σₘ |yₘ - y'ₘ|²) ≤ √k ≤ √P`
  rw [hiso, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ m, dist (y m) (y' m) ^ 2 ≤ ∑ _m : Fin k, (1 : ℝ) := Finset.sum_le_sum fun m _ => hgap m
    _ = k := by simp
    _ ≤ P := by exact_mod_cast hkP
/-- **Separation of distinct unit lattice faces** (Simon Ch. 6, §5, chapter-06.txt lines 1841–1918:
the faces `F ∈ 𝓛ₖ` and their interiors `F̆`).  For `p = (ι, b) ≠ q = (ι', b')` with `ι, ι'`
strictly increasing, `x = Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` with `y ∈ (0,1)ᵏ` and `z = Φ_q(y')` with
`y' ∈ [0,1]ᵏ`, either `1 ≤ |x − z|` or `min(yⱼ, 1 − yⱼ) ≤ |x − z|` for some `j`.  If some
`z_{ι(j)}` lies outside `(b_{ι(j)}, b_{ι(j)} + 1) ∋ x_{ι(j)} = b_{ι(j)} + yⱼ`, the coordinate `ι(j)`
gives the second alternative.  Otherwise no `z_{ι(j)}` is an integer, so `range ι ⊆ range ι'` and
`ι = ι'` (both enumerate the same `k`-element set increasingly), `b = b'` on `range ι`, and a
coordinate `l ∉ range ι` with `b_l ≠ b'_l` gives `|x_l − z_l| = |b_l − b'_l| ≥ 1`.  The coordinates
of `x` and `z` are `cmcdtfrfg_face_coord`. -/
theorem Submission.cmcdtfrfg_face_separation : ∀ (P k : ℕ) (p q : (Fin k → Fin P) × (Fin P → ℤ)), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) := by
  intro P k p q hp hq hpq y y' hy hy'
  -- step 1: the coordinates of `x = Φ_p(y)` and `z = Φ_q(y')`
  obtain ⟨hx₁, hx₂⟩ := Submission.cmcdtfrfg_face_coord P k p.1 p.2 y hp.injective
  obtain ⟨hz₁, hz₂⟩ := Submission.cmcdtfrfg_face_coord P k q.1 q.2 y' hq.injective
  set x := WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  set z := WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)
  -- step 2: `|x_l − z_l| ≤ |x − z|`
  have hcoord : ∀ l, |x l - z l| ≤ dist x z := fun l => by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le x z l
  by_cases hA : ∃ j, ¬((p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1)
  · -- step 3 (Case A): `z_{ι(j)} ∉ (b_{ι(j)}, b_{ι(j)} + 1)` while `x_{ι(j)} = b_{ι(j)} + y_j`
    obtain ⟨j, hj⟩ := hA
    obtain ⟨hy₀, hy₁⟩ := hy j
    refine Or.inr ⟨j, le_trans ?_ (hcoord (p.1 j))⟩
    rw [hx₁ j]
    rcases not_and_or.mp hj with h | h
    · calc min (y j) (1 - y j) ≤ y j := min_le_left _ _
        _ ≤ (p.2 (p.1 j) : ℝ) + y j - z (p.1 j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := le_abs_self _
    · calc min (y j) (1 - y j) ≤ 1 - y j := min_le_right _ _
        _ ≤ z (p.1 j) - ((p.2 (p.1 j) : ℝ) + y j) := by linarith [not_lt.mp h]
        _ ≤ |(p.2 (p.1 j) : ℝ) + y j - z (p.1 j)| := by rw [abs_sub_comm]; exact le_abs_self _
  -- step 4 (Case B): `b_{ι(j)} < z_{ι(j)} < b_{ι(j)} + 1` for every `j`
  have hB : ∀ j, (p.2 (p.1 j) : ℝ) < z (p.1 j) ∧ z (p.1 j) < p.2 (p.1 j) + 1 :=
    fun j => not_not.mp fun h => hA ⟨j, h⟩
  refine Or.inl ?_
  -- step 5: `range ι ⊆ range ι'`, since `z_l = b'_l ∈ ℤ` for `l ∉ range ι'`
  have hsub : ∀ j, ∃ m, q.1 m = p.1 j := by
    intro j
    by_contra hne
    obtain ⟨h₁, h₂⟩ := hB j
    rw [hz₂ (p.1 j) fun m hm => hne ⟨m, hm⟩] at h₁ h₂
    have h₁' : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) := h₁
    have h₂' : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := h₂
    have : p.2 (p.1 j) < q.2 (p.1 j) := by exact_mod_cast h₁'
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₂'
    omega
  -- step 6: `ι = ι'`, both being the increasing enumeration of the `k`-element set `range ι'`
  have hι : p.1 = q.1 := by
    have hcard : (Finset.univ.image q.1).card = k := by
      rw [Finset.card_image_of_injective _ hq.injective, Finset.card_univ, Fintype.card_fin]
    refine (Finset.orderEmbOfFin_unique hcard (fun j => ?_) hp).trans
      (Finset.orderEmbOfFin_unique hcard
        (fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j)) hq).symm
    obtain ⟨m, hm⟩ := hsub j
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩
  -- step 7: `b = b'` on `range ι`, since `b_{ι(j)} = ⌊z_{ι(j)}⌋ = b'_{ι(j)}`
  have hb : ∀ j, p.2 (p.1 j) = q.2 (p.1 j) := by
    intro j
    obtain ⟨h₁, h₂⟩ := hB j
    obtain ⟨h₃, h₄⟩ := hy' j
    have hzj := hz₁ j
    rw [← hι] at hzj
    rw [hzj] at h₁ h₂
    have h₅ : (p.2 (p.1 j) : ℝ) < q.2 (p.1 j) + 1 := by linarith
    have h₆ : (q.2 (p.1 j) : ℝ) < p.2 (p.1 j) + 1 := by linarith
    have : p.2 (p.1 j) < q.2 (p.1 j) + 1 := by exact_mod_cast h₅
    have : q.2 (p.1 j) < p.2 (p.1 j) + 1 := by exact_mod_cast h₆
    omega
  -- step 8: as `p ≠ q`, some `l ∉ range ι` has `b_l ≠ b'_l`, and there `x_l = b_l`, `z_l = b'_l`
  obtain ⟨l, hl⟩ := Function.ne_iff.mp fun h : p.2 = q.2 => hpq (Prod.ext hι h)
  have hlι : ∀ m, p.1 m ≠ l := by
    rintro m rfl
    exact hl (hb m)
  calc (1 : ℝ) ≤ |(p.2 l : ℝ) - q.2 l| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hl)
    _ = |x l - z l| := by rw [hx₂ l hlι, hz₂ l (hι ▸ hlι)]
    _ ≤ dist x z := hcoord l

/-- **Geometry of unit lattice faces** (Simon Ch. 6, §5, Lemma 2.1 and the faces `F ∈ 𝓛ₖ` of the
deformation theorem, for faces of any dimension `k`).  `(0)` `vol((0,1)ᵏ) = 1`.  For `p = (ι, b)`
with `ι` strictly increasing and `b ∈ ℤᴾ`, the face map `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` is `(a)` an
isometry `ℝᵏ → ℝᴾ` with `(b)` `dist(Φ_p y, Φ_p y') ≤ √P` on `[0,1]ᵏ`; `(c)` if `q ≠ p`,
`y ∈ (0,1)ᵏ` and `y' ∈ [0,1]ᵏ`, then `dist(Φ_p y, Φ_q y') ≥ 1` or `≥ min(yⱼ, 1 − yⱼ)` for some
`j`.  A strictly increasing `ι` is injective, so `(a)`, `(b)` are `cmcdtfrfg_face_isometry_diam`;
`(0)` is `cmcdtfrfg_cube_volume` and `(c)` is `cmcdtfrfg_face_separation`. -/
theorem Submission.cmcdtfr_face_geometry : ∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) := by
  intro P k
  refine ⟨Submission.cmcdtfrfg_cube_volume k, fun p q hp hq => ?_⟩
  -- `(a)`, `(b)` for the face map of `p`, whose strictly increasing `p.1` is injective
  obtain ⟨hiso, hdiam⟩ := Submission.cmcdtfrfg_face_isometry_diam P k p.1 p.2 hp.injective
  -- `(c)`: the open face of `p` against the closed face of `q ≠ p`
  exact ⟨hiso, hdiam, Submission.cmcdtfrfg_face_separation P k p q hp hq⟩
/-- **The `m`-skeleton of the unit cubical lattice is `H^{m+1}`-null** (Simon Ch. 6, proof of the
deformation theorem 5.1, (26)–(33): `Hⁿ(L_{n−1}) = 0`, `n = m + 1`).  The points of `ℝᴾ` with at
least `P − m` integer coordinates lie in the countably many coordinate planes
`A(s, z) = {x : xᵢ = zᵢ for i ∈ s}`, `P ≤ m + |s|`, `z ∈ ℤᴾ`.  Each `A(s, z)` is the image of the
Lipschitz map `ℝ^{Fin P \ s} → ℝᴾ`, `t ↦ (zᵢ on s, tᵢ off s)`, whose source is `μH[m + 1]`-null:
it is a union of balls of finite `μH[P − |s|]` (= Lebesgue) measure, and `P − |s| < m + 1`.
Finally `μHE[m + 1]` is a multiple of `μH[m + 1]`. -/
theorem Submission.cmcdtfr_skeleton_null : ∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
  intro P m
  -- Step 1: each coordinate plane `A(s, z)` with `P ≤ m + |s|` is `μH[m + 1]`-null
  have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
      μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
    intro s hs z
    -- `A(s, z)` is the image of the Lipschitz map `g : t ↦ (zᵢ on s, tᵢ off s)`
    let g : ({i // i ∉ s} → ℝ) → Euclid P := fun t =>
      WithLp.toLp 2 fun i => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩
    have hg1 : LipschitzWith 1 fun t : {i // i ∉ s} → ℝ =>
        fun i : Fin P => if h : i ∈ s then (z i : ℝ) else t ⟨i, h⟩ := by
      refine LipschitzWith.of_dist_le_mul fun t t' => ?_
      rw [NNReal.coe_one, one_mul]
      refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
      by_cases h : i ∈ s
      · simp [h]
      · simpa [h] using dist_le_pi_dist t t' ⟨i, h⟩
    have hg : LipschitzWith _ g := (PiLp.lipschitzWith_toLp 2 fun _ : Fin P => ℝ).comp hg1
    have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ g '' univ := by
      intro x hx
      refine ⟨fun j => x j.1, mem_univ _, ?_⟩
      ext i
      by_cases h : i ∈ s
      · simp [g, h, hx i h]
      · simp [g, h]
    -- the source of `g` has dimension `P − |s| ≤ m < m + 1`, so it is `μH[m + 1]`-null
    have hcard : Fintype.card {i // i ∉ s} ≤ m := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      omega
    have huniv : (μH[((m + 1 : ℕ) : ℝ)] : Measure ({i // i ∉ s} → ℝ)) univ = 0 := by
      rw [← Metric.iUnion_ball_nat (0 : {i // i ∉ s} → ℝ)]
      refine measure_iUnion_null fun n => ?_
      refine (Measure.hausdorffMeasure_zero_or_top
        (d₁ := (Fintype.card {i // i ∉ s} : ℝ)) ?_ _).resolve_right ?_
      · exact_mod_cast Nat.lt_succ_of_le hcard
      · rw [hausdorffMeasure_pi_real]
        exact measure_ball_lt_top.ne
    refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
    calc μH[((m + 1 : ℕ) : ℝ)] (g '' univ)
        ≤ _ ^ ((m + 1 : ℕ) : ℝ) * μH[((m + 1 : ℕ) : ℝ)] (univ : Set ({i // i ∉ s} → ℝ)) :=
          hg.hausdorffMeasure_image_le (Nat.cast_nonneg _) univ
      _ = 0 := by rw [huniv, mul_zero]
  -- Step 2: the set is covered by the countably many planes `A(s, z)`, `P ≤ m + |s|`, `z ∈ ℤᴾ`
  have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆ ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card})
        (z : Fin P → ℤ), {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
    rintro x ⟨s, hs, hx⟩
    choose! z hz using hx
    exact mem_iUnion₂.2 ⟨⟨s, hs⟩, z, hz⟩
  -- Step 3: countable subadditivity gives `μH[m + 1]`-nullity, and `μHE[m + 1] = c • μH[m + 1]`
  have hnull : μH[((m + 1 : ℕ) : ℝ)] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧
      ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 :=
    measure_mono_null hcover
      (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
  rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hnull, smul_zero]
/-- **Simon Ch. 3, 1.4** (the test-function argument of Remark 1.5(3)): if `A − x ⊆ V` for a
subspace `V`, then every approximate tangent space `Q` of `A` at `x` lies in `V`.  Every blow-up
`η_{x,r}(A) = r⁻¹(A − x)` lies in `V`.  At `q ∈ Q \ V`, `d = dist(q, V) > 0` (`V` is closed), and
the bump `g = max(0, d/2 − |· − q|) ∈ C_c` vanishes on `V`, so all blow-up integrals of `g` vanish
and the limit gives `∫_Q g dHⁿ = 0`.  But `Hⁿ⌞Q` is regular with support `Q ∋ q` (`dim Q = n`), and
`g ≥ 0` has support `B_{d/2}(q)`, so `∫_Q g dHⁿ > 0`. -/
theorem Submission.cmcdtfrpo_approxTangent_le_of_sub_mem : ∀ (P n : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q V : Submodule ℝ (Euclid P)), (∀ a ∈ A, a - x ∈ V) → HasApproximateTangentSpaceAt n A x Q → Q ≤ V := by
  intro P n A x Q V hAV hQ q hq
  by_contra hqV
  -- `d = dist(q, V) > 0`, as `V` is closed
  have hd : 0 < infDist q (V : Set (Euclid P)) :=
    (V.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, V.zero_mem⟩).mp hqV
  set d := infDist q (V : Set (Euclid P))
  -- the bump `g = max(0, d/2 − dist(·, q))`: continuous, `≥ 0`, support `B_{d/2}(q)`, zero on `V`
  set g : Euclid P → ℝ := fun y => max 0 (d / 2 - dist y q)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hg_nonneg : 0 ≤ g := fun y => le_max_left _ _
  have hg_supp : support g = ball q (d / 2) := by
    ext y
    simp only [mem_support, mem_ball, g]
    constructor
    · intro h
      by_contra h'
      exact h (max_eq_left (by linarith [not_lt.mp h']))
    · intro h
      exact (lt_max_of_lt_right (by linarith : (0 : ℝ) < d / 2 - dist y q)).ne'
  have hg_cpt : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall q (d / 2)) fun y hy => ?_
    simp only [mem_closedBall, not_le] at hy
    exact max_eq_left (by linarith)
  have hgV : ∀ v ∈ V, g v = 0 := by
    intro v hv
    have h1 : d ≤ dist q v := infDist_le_dist_of_mem (SetLike.mem_coe.mpr hv)
    rw [dist_comm] at h1
    exact max_eq_left (by linarith)
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_cpt⟩
  -- every blow-up `η_{x,r}(A) = r⁻¹(A − x)` lies in `V`, so all blow-up integrals of `f` vanish
  have hzero : ∀ r : ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] = 0 := by
    intro r
    apply setIntegral_eq_zero_of_forall_eq_zero
    rintro _ ⟨a, ha, rfl⟩
    exact hgV _ (V.smul_mem r⁻¹ (hAV a ha))
  -- uniqueness of limits along `𝓝[>] 0` gives `∫_Q g dHⁿ = 0`
  have hQint : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := by
    refine tendsto_nhds_unique (hQ.2 f) ?_
    simp only [hzero]
    exact tendsto_const_nhds
  -- `Hⁿ⌞Q` is regular with support `Q ∋ q` (`dim Q = n`), so `∫_Q g dHⁿ > 0`
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ.1
  have hint : Integrable g (μHE[n].restrict (Q : Set (Euclid P))) :=
    hg_cont.integrable_of_hasCompactSupport hg_cpt
  have hqsupp : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
    rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
    exact hq
  have hball : 0 < μHE[n].restrict (Q : Set (Euclid P)) (ball q (d / 2)) :=
    (Measure.mem_support_iff_forall q).mp hqsupp _ (ball_mem_nhds q (half_pos hd))
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg_nonneg hint, hg_supp]
    exact hball
  exact hpos.ne' hQint
/-- **Orthonormal frames of one plane agree up to a global sign** (Simon Ch. 6, §1 and §3: an
`n`-plane is oriented by `±τ₁ ∧ ⋯ ∧ τₙ` for any orthonormal basis `τ` of it).  If `τ` and `e` are
orthonormal `n`-frames in `ℝᴾ` spanning the same subspace `W`, then for every `n`-covector `α`,
`α(τ) = c α(e)` with `c = det_e(τ)`, the determinant of `τ` in the basis `e` of `W`
(`AlternatingMap.eq_smul_basis_det` for `α` restricted to `W`); `c = ±1`, being the change-of-basis
determinant between two orthonormal bases of `W`. -/
theorem Submission.cmcdtfrpo_orthonormal_frame_sign : ∀ (P n : ℕ) (τ e : Fin n → Euclid P), Orthonormal ℝ τ → Orthonormal ℝ e → Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range e) → (∀ α : Covector (Euclid P) n, α τ = α e) ∨ (∀ α : Covector (Euclid P) n, α τ = -α e) := by
  intro P n τ e hτ he hspan
  -- Step 1: the basis `b` of `W = span (range e)` with `b j = e j`, so `finrank W = n`
  let W : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e)
  have hli : LinearIndependent ℝ e := he.linearIndependent
  let b : Module.Basis (Fin n) ℝ W := Module.Basis.span hli
  have hb : ∀ j, (b j : Euclid P) = e j := Module.Basis.coe_span_apply hli
  have hfin : Module.finrank ℝ W = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  -- Step 2: `τ` as a family `τW` in `W`
  have hτW : ∀ j, τ j ∈ W := fun j => hspan.le (Submodule.subset_span (Set.mem_range_self j))
  let τW : Fin n → W := fun j => ⟨τ j, hτW j⟩
  -- Step 3: `α(τ) = det_b(τW) α(e)` for every `n`-covector `α`
  have key : ∀ α : Covector (Euclid P) n, α τ = b.det τW * α e := by
    intro α
    let αW : W [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap W.subtype
    have h := congrArg (fun f : W [⋀^Fin n]→ₗ[ℝ] ℝ => f τW) (αW.eq_smul_basis_det b)
    have hτ' : (fun j => W.subtype (τW j)) = τ := rfl
    have he' : (fun j => W.subtype (b j)) = e := funext hb
    simp only [αW, AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h
    rw [hτ', he'] at h
    rw [mul_comm]
    exact h
  -- Step 4: `det_b(τW) = ±1`, since `b` and `τW` are orthonormal bases of `W`
  have hbon : Orthonormal ℝ b := by
    rw [orthonormal_iff_ite] at he ⊢
    intro i j
    rw [Submodule.coe_inner, hb, hb]
    exact he i j
  have hτWon : Orthonormal ℝ τW := by
    rw [orthonormal_iff_ite] at hτ ⊢
    intro i j
    rw [Submodule.coe_inner]
    exact hτ i j
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range τW) :=
    (hτWon.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, hfin])).ge
  have hc : b.det τW = 1 ∨ b.det τW = -1 := by
    have h := (b.toOrthonormalBasis hbon).det_to_matrix_orthonormalBasis_real
      (OrthonormalBasis.mk hτWon hsp)
    rwa [Module.Basis.toBasis_toOrthonormalBasis, OrthonormalBasis.coe_mk] at h
  -- Step 5: the sign `det_b(τW)` does not depend on `α`
  rcases hc with h | h
  · exact Or.inl fun α => by rw [key, h, one_mul]
  · exact Or.inr fun α => by rw [key, h, neg_one_mul]

/-- **Faces in a coordinate plane are oriented by `±e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`** (Simon Ch. 6, 5.1
(26); Ch. 3, 1.4).  If `A` lies in the coordinate plane `x + V`, `V = span{e_{ι(j)}}`, then
`A − x ⊆ V`, so every approximate tangent space `Q` of `A` at `x` satisfies `Q ≤ V`
(`cmcdtfrpo_approxTangent_le_of_sub_mem`), hence `Q = V` as both have dimension `n`.  A unit
orientation `ξ = ±τ` of `Q` then uses an orthonormal frame `τ` of `V`, and `α(τ) = ±α(e_ι)` with a
sign independent of `α` (`cmcdtfrpo_orthonormal_frame_sign`). -/
theorem Submission.cmcdtfr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  -- the coordinate frame `e j = e_{ι(j)}` (orthonormal, `ι` being injective) and `V = span e`
  set e : Fin n → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have he : Orthonormal ℝ e := EuclideanSpace.orthonormal_single.comp ι hι.injective
  set V : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e) with hV
  -- Step 1: `A − x ⊆ V`, since `(a − x)_i = 0` off `range ι`
  have hAV : ∀ a ∈ A, a - x ∈ V := by
    intro a ha
    rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr (a - x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [EuclideanSpace.basisFun_apply]
      exact V.smul_mem _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [EuclideanSpace.basisFun_repr, PiLp.sub_apply, hA a ha i fun j hj => hi ⟨j, hj⟩,
        sub_self, zero_smul]
      exact V.zero_mem
  -- Step 2: `Q ≤ V`, hence `Q = V` as `dim Q = n = dim V`
  have hQV : Q = V := by
    refine Submodule.eq_of_le_of_finrank_eq
      (Submission.cmcdtfrpo_approxTangent_le_of_sub_mem P n A x Q V hAV hQ) ?_
    rw [hQ.1, hV, finrank_span_eq_card he.linearIndependent, Fintype.card_fin]
  -- Step 3: `ξ = ±τ` for an orthonormal frame `τ` of `Q = V`, and `α(τ) = ±α(e)`
  obtain ⟨τ, hτ, hτQ, hξτ⟩ := hξ
  rcases hξτ with h1 | h1 <;>
    rcases Submission.cmcdtfrpo_orthonormal_frame_sign P n τ e hτ he (hτQ.trans hQV) with h2 | h2
  · exact Or.inl fun α => by rw [h1, h2]
  · exact Or.inr fun α => by rw [h1, h2]
  · exact Or.inr fun α => by rw [h1, h2]
  · exact Or.inl fun α => by rw [h1, h2, neg_neg]

/-- **Points of the `(m + 1)`-skeleton off the `m`-skeleton lie in open `(m + 1)`-faces** (Simon
Ch. 6, proof of the deformation theorem 5.1: `L_n \ L_{n−1}` is the union of the interiors `F̆` of
the faces `F ∈ 𝓛_n`, `n = m + 1`).  If `x ∈ ℝᴾ` has at least `P − (m + 1)` integer coordinates but
not `P − m` of them, its set `J` of integer coordinates has exactly `P − (m + 1)` elements, so the
increasing enumeration `ι` of `Jᶜ` is defined on `Fin (m + 1)`.  With `b = ⌊x⌋` and
`yⱼ = fract(x_{ι(j)}) ∈ (0, 1)` (as `x_{ι(j)} ∉ ℤ`), the face point `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
is `x`: its coordinate is `⌊xᵢ⌋ = xᵢ` for `i ∈ J` and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j)`. -/
theorem Submission.cmcdtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x := by
  classical
  intro P m x ⟨s, hs, hsx⟩ hnot
  -- step 1: the set `J` of integer coordinates of `x`
  set J : Finset (Fin P) := Finset.univ.filter fun i => ∃ z : ℤ, x i = z
  have hJx : ∀ i ∈ J, ∃ z : ℤ, x i = z := fun i hi => (Finset.mem_filter.mp hi).2
  -- step 2: `s ⊆ J`, so `P ≤ m + 1 + |J|`
  have hsJ : s.card ≤ J.card :=
    Finset.card_le_card fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsx i hi⟩
  -- step 3: `m + |J| < P`, otherwise `J` itself would contradict the second hypothesis
  have hJP : m + J.card < P := by
    by_contra h
    exact hnot ⟨J, by omega, hJx⟩
  -- step 4: `|Jᶜ| = P − |J| = m + 1`
  have hcard : Jᶜ.card = m + 1 := by
    have h := Finset.card_add_card_compl J
    rw [Fintype.card_fin] at h
    omega
  -- step 5: `ι` enumerates `Jᶜ` increasingly
  set ι : Fin (m + 1) ↪o Fin P := Jᶜ.orderEmbOfFin hcard with hι
  have hιJ : ∀ j, ι j ∉ J := fun j => Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Jᶜ hcard j)
  -- step 6: the base point `b = ⌊x⌋` and the parameters `yⱼ = fract(x_{ι(j)})`
  refine ⟨(ι, fun i => ⌊x i⌋), WithLp.toLp 2 fun j => Int.fract (x (ι j)), ι.strictMono,
    fun j => ?_, ?_⟩
  -- step 7: `0 < yⱼ < 1`, as `x_{ι(j)}` is not an integer
  · refine ⟨Int.fract_pos.mpr fun h => hιJ j ?_, Int.fract_lt_one _⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⌊x (ι j)⌋, h⟩
  -- step 8: `Φ_p(y)ᵢ = ⌊xᵢ⌋ + Σⱼ [i = ι(j)] yⱼ = xᵢ` for every `i`
  · ext i
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases hi : i ∈ J
    -- (a) `i ∈ J`: no summand survives and `⌊xᵢ⌋ = xᵢ`
    · obtain ⟨z, hz⟩ := hJx i hi
      rw [Finset.sum_eq_zero fun j _ => ite_eq_right fun h : i = ι j => hιJ j (h ▸ hi), add_zero,
        hz, Int.floor_intCast]
    -- (b) `i = ι(j₀)`: only the summand `j₀` survives and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ`
    · obtain ⟨j₀, rfl⟩ : i ∈ Set.range ι := by
        rw [hι, Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr (Finset.mem_compl.mpr hi)
      rw [Fintype.sum_eq_single j₀ fun j hj => ite_eq_right fun h => hj (ι.injective h).symm,
        ite_eq_left rfl, Int.floor_add_fract]
/-- **Only finitely many unit lattice faces meet a compact set** (Simon Ch. 6, proof of the
deformation theorem 5.1, after (33): the sum `P = Σ_{F ∈ 𝓛ₙ} β_F [[F]]` runs over the finitely many
faces meeting the compact `spt Q`).  Let `p = (ι, b)`, `ι : Fin k → Fin P` arbitrary, `b ∈ ℤᴾ`,
and `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` for some `y ∈ [0,1]ᵏ`.  Then `Φ_p(y)ᵢ = bᵢ + Sᵢ` with
`Sᵢ = Σⱼ [ι(j) = i] yⱼ ∈ [0, k]`, and `|Φ_p(y)ᵢ| ≤ ‖Φ_p(y)‖ ≤ ρ` on the bounded `K`, so
`−⌈ρ⌉ − k ≤ bᵢ ≤ ⌈ρ⌉`.  Hence `p` lies in the finite set `(Fin k → Fin P) × [−N, N]ᴾ`,
`N = ⌈ρ⌉ + k`. -/
theorem Submission.cmcdtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite := by
  intro P k K hK
  -- step 1: `K` is bounded, `‖x‖ ≤ ρ` on `K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- step 4: the set lies in `(Fin k → Fin P) × [−N, N]ᴾ`, `N = ⌈ρ⌉ + k`
  refine (Set.finite_univ.prod (Set.Finite.pi fun _ : Fin P =>
    Set.finite_Icc (-(⌈ρ⌉ + k)) (⌈ρ⌉ + k))).subset ?_
  rintro p ⟨y, hy, hx⟩
  refine ⟨Set.mem_univ p.1, Set.mem_univ_pi.mpr fun i => ?_⟩
  -- the coordinate formula `Φ(y)ᵢ = bᵢ + Sᵢ`, `Sᵢ = Σⱼ [ι(j) = i] yⱼ`
  have hcoord : (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i =
      (p.2 i : ℝ) + ∑ j, if p.1 j = i then y j else 0 := by
    rw [PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    exact if_congr eq_comm rfl rfl
  -- step 2: `0 ≤ Sᵢ ≤ k`
  have hS₀ : 0 ≤ ∑ j, if p.1 j = i then y j else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs; exacts [(hy j).1, le_rfl]
  have hS₁ : ∑ j, (if p.1 j = i then y j else 0) ≤ k :=
    calc ∑ j, (if p.1 j = i then y j else 0) ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by split_ifs; exacts [(hy j).2, zero_le_one]
      _ = k := by simp
  -- step 3: `|bᵢ + Sᵢ| = |Φ(y)ᵢ| ≤ ‖Φ(y)‖ ≤ ρ ≤ ⌈ρ⌉`, so `−⌈ρ⌉ − k ≤ bᵢ ≤ ⌈ρ⌉`
  have hxi : ‖(WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) i‖ ≤ ρ :=
    le_trans (PiLp.norm_apply_le _ i) (hρ _ hx)
  rw [hcoord, Real.norm_eq_abs, abs_le] at hxi
  have hρc := Int.le_ceil ρ
  constructor
  · have h : ((-(⌈ρ⌉ + k) : ℤ) : ℝ) ≤ p.2 i := by push_cast; linarith [hxi.1]
    exact_mod_cast h
  · have h : (p.2 i : ℝ) ≤ ((⌈ρ⌉ + k : ℤ) : ℝ) := by push_cast; linarith [hxi.2]
    exact_mod_cast h
/-- **On a Borel subset of a coordinate `n`-plane the orientation is a Borel sign times
`e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`** (Simon Ch. 6, proof of 5.1, (26)–(28): the orientation of `T` on a
face `F̆` of the cube lattice).  Assume (IMC-b), the restriction `τ(M ∩ E, θ, ξ)` of `τ(M, θ, ξ)`
to a Borel set `E` (`U` open), and (PO), `cmcdtfr_plane_orientation`.  Let `E` lie in the
coordinate plane through `c` spanned by `e_ι = (e_{ι(0)}, …, e_{ι(n-1)})`.  The restriction
orients the approximate tangent planes `Q` of `M ∩ E` by `ξ(x)` a.e., and points of `M ∩ E` agree
with `x` off `range ι`, so (PO) gives `ξ(x) = ±e` a.e. on `M ∩ E`, where `e = (α ↦ α(e_ι))`.  For
a strongly measurable version `ξ̃` of `ξ`, the sign `σ = 1` on `{ξ̃ = e}`, `-1` on
`{ξ̃ ≠ e, ξ̃ = -e}`, `0` elsewhere is Borel with `|σ| ≤ 1`, and `ξ(x)(α) = σ(x) α(e_ι)` a.e. on
`M ∩ E`. -/
theorem Submission.cmcdtfrsd_coordinate_plane_orientation_sign : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  intro hIMC hPO P n U R ι c E hU hι hE hEc
  classical
  -- Step 1: (IMC-b) restricts `R` to `M ∩ E` keeping `ξ`, and `R'.orients` orients its tangents
  obtain ⟨-, R', -, hcarr, -, horient⟩ := hIMC P n U R E hU hE
  have hor := R'.orients
  rw [hcarr, horient] at hor
  -- Step 2: points of `M ∩ E` agree with `x ∈ M ∩ E` off `range ι`, so (PO) gives `ξ(x) = ±e_ι`
  have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
  have hsign : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)),
      (∀ α : Covector (Euclid P) n,
          R.orient x α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨
        ∀ α : Covector (Euclid P) n,
          R.orient x α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    filter_upwards [hor, ae_restrict_mem hME] with x ⟨Q, hQ, hξ⟩ hx
    refine hPO P n ι (R.carrier ∩ E) x Q (R.orient x) hι (fun a ha i hi => ?_) hQ hξ
    rw [hEc a ha.2 i hi, hEc x hx.2 i hi]
  -- Step 3: a strongly measurable version `ξ̃` of `ξ`, equal to `ξ` a.e. on `M ∩ E ⊆ M`
  set ξ' := R.aestronglyMeasurable_orient.mk R.orient
  have hξ'm : StronglyMeasurable ξ' := R.aestronglyMeasurable_orient.stronglyMeasurable_mk
  have hξξ' : R.orient =ᵐ[μHE[n].restrict (R.carrier ∩ E)] ξ' :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.aestronglyMeasurable_orient.ae_eq_mk
  -- Step 4: the coordinate `n`-vector `e = (α ↦ α(e_ι))`
  set e : MultiVector P n :=
    ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  -- Step 5: the sign `σ`; `{ξ̃ = ±e}` are Borel, as `MultiVector P n` is metrizable (the
  -- pseudometrizability of its normed structure is not found by instance search)
  have hT0 : T0Space (MultiVector P n) := inferInstance
  have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
    let m : PseudoMetricSpace (MultiVector P n) := inferInstance
    { toPseudoMetrizableSpace := ⟨⟨m.toUniformSpace, rfl,
        @EMetric.instIsCountablyGeneratedUniformity _ m.toPseudoEMetricSpace⟩⟩
      toT0Space := hT0 }
  refine ⟨fun x => if ξ' x = e then 1 else if ξ' x = -e then -1 else 0,
    Measurable.ite (hξ'm.measurableSet_eq_fun stronglyMeasurable_const) measurable_const
      (Measurable.ite (hξ'm.measurableSet_eq_fun stronglyMeasurable_const) measurable_const
        measurable_const), fun x => ?_, ?_⟩
  · dsimp only
    split_ifs <;> norm_num
  -- Step 6: case analysis on `ξ(x) = ±e`
  filter_upwards [hsign, hξξ'] with x hx hxx' α
  rcases hx with h | h
  · -- `ξ(x) = e`, so `ξ̃(x) = e` and `σ(x) = 1`
    have hxe : ξ' x = e := hxx' ▸ ContinuousLinearMap.ext fun β => h β
    rw [h α, ite_eq_left hxe, Int.cast_one, one_mul]
  · -- `ξ(x) = -e`, so `ξ̃(x) = -e`; `σ(x) = 1` if also `ξ̃(x) = e`, else `σ(x) = -1`
    have hxe : ξ' x = -e := hxx' ▸ ContinuousLinearMap.ext fun β => h β
    by_cases hxe' : ξ' x = e
    · rw [ite_eq_left hxe', Int.cast_one, one_mul, hxx', hxe']
      rfl
    · rw [h α, ite_eq_right hxe', ite_eq_left hxe, Int.cast_neg, Int.cast_one, neg_one_mul]

/-- **On one open lattice face an integer multiplicity current is an integer `L¹` density**
(Simon Ch. 6, proof of the deformation theorem 5.1, (33)).  Let `Φ_p(y) = b + ∑ⱼ yⱼ e_{ι(j)}` be
an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  `F̆` is Borel and lies in the coordinate plane
through `b`, so by `cmcdtfrsd_coordinate_plane_orientation_sign` the orientation of
`R = (M, θ, ξ)` is `ξ = σ E_p` `Hⁿ`-a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel.  As `Φ_p` is an
isometry and `Hⁿ = vol` on `ℝⁿ`, `Hⁿ⌞F̆ = Φ_p # (vol⌞Q₁)`, so the integer function
`u = (1_M θ σ) ∘ Φ_p` satisfies `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{Q₁} u ⟨ω ∘ Φ_p, E_p⟩` and
`∫_{Q₁} |u| ≤ ∫_{Q₁} (1_M θ) ∘ Φ_p = μ_R(F̆) < ∞` (`F̆` lies in a compact set). -/
theorem Submission.cmcdtfrsd_face_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro hIMC hPO P n R p hι hΦ
  -- notation: `Φ = Φ_p`, `Q₁` the open unit cube of `ℝⁿ`, `F̆ = Φ(Q₁)` the open face
  set Φ : Euclid n → Euclid P := fun y => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
    ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  set Q₁ : Set (Euclid n) := {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}
  -- Step 1: `Q₁` and `F̆` are Borel (`Φ` is an isometry, hence a measurable embedding)
  have hQ₁ : MeasurableSet Q₁ := by
    have hQ : Q₁ = ⋂ i, ({y : Euclid n | 0 < y i} ∩ {y : Euclid n | y i < 1}) := by
      ext y
      simp [Q₁]
    rw [hQ]
    refine MeasurableSet.iInter fun i => ?_
    have hm : Measurable fun y : Euclid n => y i :=
      (EuclideanSpace.proj i).continuous.measurable
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  have hF : MeasurableSet (Φ '' Q₁) := hemb.measurableSet_image' hQ₁
  -- Step 2: `F̆` lies in the coordinate plane through `b`
  have hplane : ∀ a ∈ Φ '' Q₁, ∀ i, (∀ j, p.1 j ≠ i) →
      a i = (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) : Euclid P) i := by
    rintro _ ⟨y, -, rfl⟩ i hi
    have hi' : ∀ j, i ≠ p.1 j := fun j h => hi j h.symm
    simp [Φ, hi']
  -- Step 3: the orientation is `σ E_p` a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel
  obtain ⟨σ, hσm, hσ1, hσ⟩ := Submission.cmcdtfrsd_coordinate_plane_orientation_sign hIMC hPO
    P n univ R p.1 (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (Φ '' Q₁) isOpen_univ hι hF hplane
  -- Step 4: change of variables, `Hⁿ⌞F̆ = Φ_# (vol⌞Q₁)`
  have hrestr : μHE[n].restrict (Φ '' Q₁) = (volume.restrict Q₁).map Φ := by
    calc μHE[n].restrict (Φ '' Q₁) = (μHE[n].restrict (range Φ)).restrict (Φ '' Q₁) :=
          (Measure.restrict_restrict_of_subset (image_subset_range Φ Q₁)).symm
      _ = ((volume : Measure (Euclid n)).map Φ).restrict (Φ '' Q₁) := by
          rw [← hΦ.map_euclideanHausdorffMeasure,
            EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      _ = (volume.restrict Q₁).map Φ := by
          rw [hemb.restrict_map, hΦ.injective.preimage_image]
  have hint : ∀ f : Euclid P → ℝ, ∫ x in Φ '' Q₁, f x ∂μHE[n] = ∫ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hemb.integral_map]
  have hlint : ∀ f : Euclid P → ℝ≥0∞,
      ∫⁻ x in Φ '' Q₁, f x ∂μHE[n] = ∫⁻ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hemb.lintegral_map]
  -- Step 5: the density `u = g ∘ Φ`, `g = 1_M θ σ`, dominated by `h = 1_M θ`
  set g : Euclid P → ℝ := R.carrier.indicator fun x => (R.mult x : ℝ) * (σ x : ℝ)
  set h : Euclid P → ℝ := R.carrier.indicator fun x => (R.mult x : ℝ)
  have hgm : Measurable g :=
    (((measurable_of_countable fun k : ℕ => (k : ℝ)).comp R.measurable_mult).mul
      ((measurable_of_countable fun k : ℤ => (k : ℝ)).comp hσm)).indicator
      R.measurableSet_carrier
  have hgh : ∀ x, |g x| ≤ h x := by
    intro x
    by_cases hx : x ∈ R.carrier
    · simp only [g, h, indicator_of_mem hx, abs_mul, Nat.abs_cast]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (by exact_mod_cast hσ1 x)
    · simp [g, h, indicator_of_notMem hx]
  -- Step 6: `∫⁻_{Q₁} h ∘ Φ = R.measure F̆`
  have hmass : ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) = R.measure (Φ '' Q₁) := by
    rw [← hlint fun x => ENNReal.ofReal (h x)]
    have hh : (fun x => ENNReal.ofReal (h x)) =
        R.carrier.indicator fun x => (R.mult x : ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ R.carrier <;> simp [h, hx]
    rw [hh, lintegral_indicator R.measurableSet_carrier, IMRep.measure, withDensity_apply _ hF,
      Measure.restrict_restrict R.measurableSet_carrier, Measure.restrict_restrict hF,
      inter_comm]
  -- Step 7: `R.measure F̆ < ∞`, `F̆` lying in the compact set `Φ(toLp [0, 1]ⁿ)`
  have hfin : R.measure (Φ '' Q₁) ≠ ∞ := by
    have hK : IsCompact (Φ '' (WithLp.toLp 2 '' Icc (0 : Fin n → ℝ) 1)) :=
      (isCompact_Icc.image (PiLp.continuous_toLp 2 _)).image hΦ.continuous
    have hFK : Φ '' Q₁ ⊆ Φ '' (WithLp.toLp 2 '' Icc (0 : Fin n → ℝ) 1) := by
      refine image_mono fun y hy => ?_
      exact ⟨WithLp.ofLp y, ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩,
        WithLp.toLp_ofLp _ y⟩
    refine ne_top_of_le_ne_top ?_ (measure_mono hFK)
    rw [IMRep.measure, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult _ hK (subset_univ _)
  -- Step 8: integrability of `u` and the mass bound
  have hle : ∀ y, ENNReal.ofReal |g (Φ y)| ≤ ENNReal.ofReal (h (Φ y)) :=
    fun y => ENNReal.ofReal_le_ofReal (hgh _)
  have hui : IntegrableOn (fun y => g (Φ y)) Q₁ := by
    refine ⟨(hgm.comp hΦ.continuous.measurable).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 ?_⟩
    calc ∫⁻ y in Q₁, ‖g (Φ y)‖ₑ = ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| := by
          simp_rw [Real.enorm_eq_ofReal_abs]
      _ ≤ ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) := lintegral_mono hle
      _ = R.measure (Φ '' Q₁) := hmass
      _ < ∞ := lt_top_iff_ne_top.2 hfin
  refine ⟨fun y => g (Φ y), fun y => ?_, hui, ?_, fun ω => ?_⟩
  · -- Step 5(b): `u` is integer valued
    by_cases hy : Φ y ∈ R.carrier
    · exact ⟨(R.mult (Φ y) : ℤ) * σ (Φ y), by simp [g, indicator_of_mem hy]⟩
    · exact ⟨0, by simp [g, indicator_of_notMem hy]⟩
  · rw [ofReal_integral_eq_lintegral_ofReal hui.abs (ae_of_all _ fun y => abs_nonneg _),
      ← hmass]
    exact lintegral_mono hle
  · -- Step 9: the integral identity
    have hMF : MeasurableSet (R.carrier ∩ Φ '' Q₁) := R.measurableSet_carrier.inter hF
    calc ∫ x in R.carrier ∩ Φ '' Q₁,
            (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
        = ∫ x in R.carrier ∩ Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := by
          refine setIntegral_congr_ae hMF ?_
          filter_upwards [(ae_restrict_iff' hMF).1 hσ] with x hx hxMF
          rw [hx hxMF, show g x = (R.mult x : ℝ) * (σ x : ℝ) from indicator_of_mem hxMF.1 _]
          ring
      _ = ∫ x in Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hF inter_subset_right
            ?_).symm
          intro x hx
          have hxM : x ∉ R.carrier := fun hxM => hx.2 ⟨hxM, hx.1⟩
          simp [g, indicator_of_notMem hxM]
      _ = ∫ y in Q₁, g (Φ y) * (ω : DifferentialForm (Euclid P) n) (Φ y)
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := hint _
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]
/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors
(alternating maps agreeing on distinct basis vectors are equal), so
`Φ α = (α(e ∘ I))_{I : Fin n → Fin P}` is an injective linear map into the finite-dimensional
space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.lcn_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `Φ α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `Φ α = Φ β` makes `α` and `β` agree on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective Φ fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)

/-- **Simon Ch. 6, 3.1 (‡)**: for an integer multiplicity triple `(M, θ, ξ)` in `U`, a compact
`K ⊆ U` and an `n`-covector `α`, the component `θ ⟨α, ξ⟩` is `Hⁿ`-integrable on `M ∩ K`.  `θ` is
locally `Hⁿ`-integrable, and `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, so `‖ξ‖ ≤ 1` and
`|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ`, an integrable majorant on `M ∩ K`. -/
theorem Submission.lcn_mult_mul_orient_apply_integrableOn : ∀ (P n : ℕ) (U K : Set (Euclid P)) (R : IMRep U n), IsCompact K → K ⊆ U → ∀ α : Covector (Euclid P) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x α) (R.carrier ∩ K) μHE[n] := by
  intro P n U K R hK hKU α
  -- `μ := Hⁿ⌞(M ∩ K) ≤ Hⁿ⌞M`
  have hμ : μHE[n].restrict (R.carrier ∩ K) ≤ μHE[n].restrict R.carrier :=
    Measure.restrict_mono inter_subset_left le_rfl
  -- `θ` is `μ`-integrable, as `∫⁻_{M ∩ K} θ dHⁿ < ∞`; hence so is `‖α‖ θ`
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hmaj : Integrable (fun x => ‖α‖ * (R.mult x : ℝ)) (μHE[n].restrict (R.carrier ∩ K)) := by
    simpa using (integrable_toReal_of_lintegral_ne_top hθ.aemeasurable
      (R.locallyIntegrable_mult K hK hKU)).const_mul ‖α‖
  -- `‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e., hence `μ`-a.e.
  have hξ : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ K)), ‖R.orient x‖ ≤ 1 := by
    refine ae_mono hμ ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `θ ⟨α, ξ⟩` is `μ`-a.e. strongly measurable: `ξ` is, and evaluation at `α` is continuous
  have hm : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ K)) := by
    have hξα : AEStronglyMeasurable (fun x => R.orient x α) (μHE[n].restrict (R.carrier ∩ K)) :=
      (ContinuousLinearMap.apply ℝ ℝ α).continuous.comp_aestronglyMeasurable
        (R.aestronglyMeasurable_orient.mono_measure hμ)
    exact (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable.mul hξα
  -- domination: `|θ ⟨α, ξ⟩| ≤ θ ‖ξ‖ ‖α‖ ≤ ‖α‖ θ` `μ`-a.e.
  refine hmaj.mono' hm ?_
  filter_upwards [hξ] with x hx
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
  calc (R.mult x : ℝ) * |R.orient x α| ≤ (R.mult x : ℝ) * (‖R.orient x‖ * ‖α‖) := by
        gcongr
        exact (Real.norm_eq_abs _).symm.trans_le ((R.orient x).le_opNorm α)
    _ ≤ (R.mult x : ℝ) * (1 * ‖α‖) := by gcongr
    _ = ‖α‖ * R.mult x := by ring

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then for every
`n`-covector `α`, `⟨α, ξ⟩ = 0` `Hⁿ`-a.e. on `M ∩ W`.  Let `ν = Hⁿ⌞(M ∩ closure W)`; then
`f = θ ⟨α, ξ⟩` is `ν`-integrable (`lcn_mult_mul_orient_apply_integrableOn`, `closure W` being a
compact subset of `U`).  For smooth `g` with compact support in `W`, `ω = g α` is a test form in
`U` supported in `W`, so `0 = T(ω) = ∫_M θ ⟨g α, ξ⟩ dHⁿ = ∫ g f dν` (`g = 0` off `W`).  The
fundamental lemma of the calculus of variations on `W` gives `f = 0` `ν`-a.e. on `W`; as
`Hⁿ⌞(M ∩ W) ≤ ν` and `θ > 0` on `M`, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. -/
theorem Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → ∀ α : Covector (Euclid P) n, ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x α = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW α
  -- `f = θ ⟨α, ξ⟩` is integrable for `ν = Hⁿ⌞(M ∩ closure W)`
  have hf : Integrable (fun x => (R.mult x : ℝ) * R.orient x α)
      (μHE[n].restrict (R.carrier ∩ closure W)) :=
    Submission.lcn_mult_mul_orient_apply_integrableOn P n U (closure W) R hWc hWU α
  -- fundamental lemma on the open set `W`: `f = 0` `ν`-a.e. on `W`
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ closure W)), x ∈ W →
      (R.mult x : ℝ) * R.orient x α = 0 := by
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hf.locallyIntegrable.locallyIntegrableOn W) fun g hg hgc hgW => ?_
    -- `ω = g α` is a test form in `U` supported in `W`, so `T(ω) = 0`
    have hωW : tsupport (fun x => g x • α) ⊆ W := (tsupport_smul_subset_left g _).trans hgW
    have hω : (fun x => g x • α) ∈ TestFormOn U n :=
      ⟨⟨hg.smul contDiff_const, hgc.smul_right⟩, hωW.trans (subset_closure.trans hWU)⟩
    calc ∫ x, g x • ((R.mult x : ℝ) * R.orient x α) ∂(μHE[n].restrict (R.carrier ∩ closure W))
        = ∫ x in R.carrier ∩ closure W, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          congr 1
          funext x
          rw [map_smul, smul_eq_mul, smul_eq_mul]
          ring
      -- `g = 0` off `closure W`, so the integral over `M` is the integral over `M ∩ closure W`
      _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (g x • α) ∂μHE[n] := by
          refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
            inter_subset_left fun x hx => ?_).symm
          have hgx : g x = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, subset_closure (hgW h)⟩
          rw [hgx, zero_smul, map_zero, mul_zero]
      _ = T ⟨_, hω⟩ := (hRT ⟨_, hω⟩).symm
      _ = 0 := hTW ⟨_, hω⟩ hωW
  -- pass to `Hⁿ⌞(M ∩ W) ≤ ν` and cancel `θ > 0` on `M`
  have hle : μHE[n].restrict (R.carrier ∩ W) ≤ μHE[n].restrict (R.carrier ∩ closure W) :=
    Measure.restrict_mono (inter_subset_inter_right _ subset_closure) le_rfl
  filter_upwards [ae_mono hle hae,
    ae_restrict_mem (R.measurableSet_carrier.inter hW.measurableSet)] with x hx hxMW
  have hθ : (R.mult x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (R.mult_pos x hxMW.1).ne'
  exact (mul_eq_zero.mp (hx hxMW.2)).resolve_left hθ

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` vanishes on an open `W ⊂⊂ U`, then
`Hⁿ(M ∩ W) = 0`.  `Λⁿ` is finite-dimensional (`lcn_covector_finiteDimensional`); for each `α` of
a basis, `⟨α, ξ⟩ = 0` `Hⁿ⌞(M ∩ W)`-a.e. (`lcn_orient_apply_ae_eq_zero_of_vanishesOn`), so
`ξ = 0` `Hⁿ⌞(M ∩ W)`-a.e.  But `ξ` is `Hⁿ`-a.e. on `M` a unit orientation, hence nonzero
(`imsupp_unit_orientation_ne_zero_norm_le_one`), so `Hⁿ⌞(M ∩ W) = 0`. -/
theorem Submission.imrep_carrier_inter_null_of_vanishesOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → IsOpen W → IsCompact (closure W) → closure W ⊆ U → T.VanishesOn W → μHE[n] (R.carrier ∩ W) = 0 := by
  intro P n U W T R hRT hW hWc hWU hTW
  -- a basis `α₁, …, α_N` of the finite-dimensional space `Λⁿ`
  have := Submission.lcn_covector_finiteDimensional P n
  let b := Module.finBasis ℝ (Covector (Euclid P) n)
  -- `⟨αₖ, ξ⟩ = 0` for every `k`, `Hⁿ⌞(M ∩ W)`-a.e.
  have h0 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ k, R.orient x (b k) = 0 :=
    ae_all_iff.mpr fun k =>
      Submission.lcn_orient_apply_ae_eq_zero_of_vanishesOn P n U W T R hRT hW hWc hWU hTW (b k)
  -- `ξ ≠ 0` `Hⁿ⌞M`-a.e., hence `Hⁿ⌞(M ∩ W)`-a.e.
  have h1 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), R.orient x ≠ 0 := by
    refine ae_mono (Measure.restrict_mono inter_subset_left le_rfl) ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).1
  -- a functional on `Λⁿ` vanishing on a basis is zero, so `Hⁿ⌞(M ∩ W)`-a.e. `x` is impossible
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), False := by
    filter_upwards [h0, h1] with x hx hne
    exact hne (ContinuousLinearMap.coe_injective (b.ext fun k => hx k))
  exact Measure.restrict_eq_zero.mp (ae_eq_bot.mp (eventually_false_iff_eq_bot.mp h2))

/-- **Simon 6.2.11, 6.3.2(3)**: if `T = τ(M, θ, ξ)` in `U`, then `Hⁿ(M ∖ spt T) = 0`, i.e.
`μ_T(U ∖ spt T) = 0`.  As `M ⊆ U` and `spt T = U ∖ Z`, `M ∖ spt T ⊆ M ∩ Z`, where the zero region
`Z = ⋃ 𝒲` is the union of the open `W ⊂⊂ U` on which `T` vanishes.  `ℝᴾ` is second countable, so
`Z = ⋃_{W ∈ 𝒮} W` for a countable `𝒮 ⊆ 𝒲`; each `Hⁿ(M ∩ W) = 0`
(`imrep_carrier_inter_null_of_vanishesOn`), and countable subadditivity concludes. -/
theorem Submission.imrep_carrier_sdiff_support_null : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
  intro P n U T R _ hRT
  -- the zero region `Z = ⋃₀ 𝒲` is the union of a countable subfamily `𝒮 ⊆ 𝒲`
  obtain ⟨𝒮, h𝒮c, h𝒮W, h𝒮⟩ := TopologicalSpace.isOpen_sUnion_countable
    {W : Set (Euclid P) | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ T.VanishesOn W}
    fun W hW => hW.1
  -- `M ∖ spt T ⊆ ⋃_{W ∈ 𝒮} M ∩ W`: a point of `M ⊆ U` outside `spt T = U ∖ Z` lies in `Z`
  have hsub : R.carrier \ T.support ⊆ ⋃ W ∈ 𝒮, R.carrier ∩ W := by
    rintro x ⟨hxM, hxS⟩
    have hxZ : x ∈ ⋃₀ 𝒮 := by
      rw [h𝒮]
      by_contra hxZ
      exact hxS (mem_sdiff_of_mem (R.carrier_subset hxM) hxZ)
    obtain ⟨W, hW, hxW⟩ := mem_sUnion.mp hxZ
    exact mem_biUnion hW ⟨hxM, hxW⟩
  -- `Hⁿ(M ∩ W) = 0` for each of the countably many `W ∈ 𝒮`
  refine measure_mono_null hsub ((measure_biUnion_null_iff h𝒮c).mpr fun W hW => ?_)
  obtain ⟨hWo, hWc, hWU, hTW⟩ := h𝒮W hW
  exact Submission.imrep_carrier_inter_null_of_vanishesOn P n U W T R hRT hWo hWc hWU hTW
/-- **Integrability of the action integrand** (Simon Ch. 6, 3.1 (‡)).  For an integer
multiplicity triple `R = (C, θ, ξ)` in `U` and `ω ∈ 𝒟ⁿ(U)`, `x ↦ θ(x) ⟨ω(x), ξ(x)⟩` is
`Hⁿ⌞C`-integrable: `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal `Hⁿ`-a.e. on `C`, so
`|⟨α, ξ(x)⟩| ≤ ‖α‖`, and the integrand is dominated by `B θ 1_{spt ω}` (`B` a bound for `‖ω‖`),
which is integrable because `spt ω` is a compact subset of `U` and `∫_{C ∩ K} θ dHⁿ < ∞` for
such `K`. -/
theorem Submission.regcomp_rim_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  set K : Set (Euclid P) := tsupport f
  /- Step 1: `ω` is continuous, bounded by some `B`, and vanishes off the compact set
  `K = spt ω ⊆ U`. -/
  have hcont : Continuous f := hsmooth.continuous
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet K := (isClosed_tsupport f).measurableSet
  /- Step 2: `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal gives `|⟨α, ξ(x)⟩| = |α(τ)| ≤ ‖α‖`
  for `Hⁿ`-a.e. `x ∈ C`. -/
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      ‖R.orient x α‖ ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hor⟩ := hx
    have hατ : ‖α τ‖ ≤ ‖α‖ := by
      simpa [hτ.norm_eq_one] using α.le_opNorm τ
    rcases hor with h | h
    · rw [h]
      exact hατ
    · rw [h, norm_neg]
      exact hατ
  /- Step 3: the integrand is a.e. strongly measurable (evaluation is continuous). -/
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have happly : Continuous fun p : MultiVector P n × Covector (Euclid P) n => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  have hev : AEStronglyMeasurable (fun x => R.orient x (f x)) (μHE[n].restrict R.carrier) :=
    happly.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable)
  have hF : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (f x))
      (μHE[n].restrict R.carrier) := hθm.aestronglyMeasurable.mul hev
  /- Step 4: `B θ 1_K` is integrable, since `∫_{C ∩ K} θ dHⁿ < ∞`. -/
  have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) K (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, Measure.restrict_restrict hKm, inter_comm]
    simpa only [Real.enorm_natCast] using (R.locallyIntegrable_mult K hcpt hU).lt_top
  have hg : Integrable (fun x => B * K.indicator (fun x => (R.mult x : ℝ)) x)
      (μHE[n].restrict R.carrier) := (hθK.integrable_indicator hKm).const_mul B
  /- Step 5: `|θ ⟨ω, ξ⟩| ≤ B θ 1_K` a.e. on `C`. -/
  have hbound : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (f x)‖ ≤ B * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (f x)).trans (hB x)) (Nat.cast_nonneg _)
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
      simp
  /- Step 6: dominated by an integrable function. -/
  exact hg.mono' hF hbound

/-- **Unit-face decomposition of an integer multiplicity current on the `(m+1)`-skeleton**
(Simon Ch. 6, proof of the deformation theorem 5.1, (26)–(28) and (33)).  Let `Q₀ = τ(M, θ, ξ)` in
`ℝᴾ`, `n = m + 1`, with `spt Q₀ ⊆ K` compact and `spt Q₀ ⊆ L_n`.  The faces `p = (ι, b)` whose
closed face `Φ_p([0,1]ⁿ)` meets `spt Q₀` form a finite set `s`, and distinct open faces
`F̆_p = Φ_p((0,1)ⁿ)` are disjoint Borel sets (`Φ_p` is an isometry).  `M ∖ ⋃_{p ∈ s} F̆_p` lies in
`(M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null: off `L_m`, a point of `spt Q₀ ⊆ L_n` lies on an open
face.  On each face `face_density` gives an integer density `u_p` with
`∫_{M ∩ F̆_p} θ ⟨ω, ξ⟩ dHⁿ = ∫_{(0,1)ⁿ} u_p(y) ω(Φ_p y)(E_p) dy` and `∫ |u_p| ≤ μ(F̆_p)`,
`μ = θ Hⁿ⌞M`.  Summing over the disjoint faces gives the representation of `Q₀(ω)`, and
`Σ_p ∫ |u_p| ≤ μ(ℝᴾ) = M(Q₀)` by the mass hypothesis (MR). -/
theorem Submission.cmcdtfr_skeleton_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ) (K : Set (Euclid P)) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → ∃ (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q₀.mass ∧ (∀ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.support) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro _hVO hMR hIMC P m K Q₀ hK hQ₀ hQK hQL
  -- Step 1: an integer multiplicity representation `R = (M, θ, ξ)` of `Q₀`
  obtain ⟨R, hR⟩ := hQ₀
  -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` and the open unit cube `Q₁`
  let Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  -- Step 8: `Φ_p` is an isometry (`face_geometry` (a)), so the open face `F̆_p = Φ_p(Q₁)` is Borel
  have hiso : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → Isometry (Φ p) :=
    fun p hp => Isometry.of_dist_eq ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p p hp hp).1
  have hQ₁ : MeasurableSet Q₁ := by
    have hpre : Q₁ = WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Q₁, Set.mem_pi]
    rw [hpre]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  have hF : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      MeasurableSet (Φ p '' Q₁) :=
    fun p hp => (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image' hQ₁
  -- Step 6: distinct open faces are disjoint (`face_geometry` (c))
  have hdisj : ∀ p q : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 →
      p ≠ q → Disjoint (Φ p '' Q₁) (Φ q '' Q₁) := by
    intro p q hp hq hpq
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h : 1 ≤ dist (Φ p y) (Φ q y') ∨ ∃ j, min (y j) (1 - y j) ≤ dist (Φ p y) (Φ q y') :=
      ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p q hp hq).2.2 hpq y y' hy
        fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩
    rw [hyy', dist_self] at h
    rcases h with h | ⟨j, hj⟩
    · exact absurd h (by norm_num)
    · obtain ⟨hy₀, hy₁⟩ := hy j
      exact absurd hj (not_le.mpr (lt_min hy₀ (by linarith)))
  -- Step 5: the finite set `s` of faces `p` whose closed face meets `spt Q₀ ⊆ K`
  obtain ⟨s, hs⟩ : ∃ s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ)), ∀ p, p ∈ s ↔
      StrictMono p.1 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support := by
    have hfin : {p : (Fin (m + 1) → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧
        ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support}.Finite :=
      (Submission.cmcdtfrsd_faces_meeting_compact_finite P (m + 1) K hK).subset
        fun p ⟨_, y, hy, hyQ⟩ => ⟨y, hy, hQK hyQ⟩
    exact ⟨hfin.toFinset, fun p => hfin.mem_toFinset⟩
  -- Steps 9–11: the integer densities `u_p` on the faces (`face_density`)
  have hfd : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      ∃ u : Euclid (m + 1) → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u Q₁ ∧
        ENNReal.ofReal (∫ y in Q₁, |u y|) ≤ R.measure (Φ p '' Q₁) ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
          ∫ x in R.carrier ∩ Φ p '' Q₁, (R.mult x : ℝ) *
              R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
            ∫ y in Q₁, u y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y)
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) :=
    fun p hp => Submission.cmcdtfrsd_face_density hIMC.2.1 Submission.cmcdtfr_plane_orientation
      P (m + 1) R p hp (hiso p hp)
  choose! u hu_int hu_integ hu_mass hu_rep using hfd
  refine ⟨s, u, fun p hp => ((hs p).1 hp).1, fun p hp => hu_int p ((hs p).1 hp).1,
    fun p hp => hu_integ p ((hs p).1 hp).1, ?_, fun p hp => ((hs p).1 hp).2, fun ω => ?_⟩
  · -- Step 11: `Σ_p ∫|u_p| ≤ Σ_p μ(F̆_p) = μ(⋃_p F̆_p) ≤ μ(ℝᴾ) = M(Q₀)`, the last step by (MR)
    calc ENNReal.ofReal (∑ p ∈ s, ∫ y in Q₁, |u p y|)
        = ∑ p ∈ s, ENNReal.ofReal (∫ y in Q₁, |u p y|) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => integral_nonneg fun y => abs_nonneg (u p y)
      _ ≤ ∑ p ∈ s, R.measure (Φ p '' Q₁) :=
          Finset.sum_le_sum fun p hp => hu_mass p ((hs p).1 hp).1
      _ = R.measure (⋃ p ∈ s, Φ p '' Q₁) :=
          (measure_biUnion_finset (fun p hp q hq hpq =>
            hdisj p q ((hs p).1 hp).1 ((hs q).1 hq).1 hpq) fun p hp => hF p ((hs p).1 hp).1).symm
      _ ≤ R.measure univ := measure_mono (subset_univ _)
      _ = Q₀.mass := (hMR P (m + 1) univ Q₀ R isOpen_univ hR univ isOpen_univ).symm
  · -- Step 7: `M ∖ ⋃_{p ∈ s} (M ∩ F̆_p) ⊆ (M ∖ spt Q₀) ∪ L_m`, an `Hⁿ`-null set
    have hnull : μHE[m + 1] (R.carrier \ ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁)) = 0 := by
      refine measure_mono_null ?_ (measure_union_null
        (Submission.imrep_carrier_sdiff_support_null P (m + 1) univ Q₀ R isOpen_univ hR)
        (Submission.cmcdtfr_skeleton_null P m))
      rintro x ⟨hxM, hx⟩
      by_cases hxS : x ∈ Q₀.support
      · -- `x ∈ spt Q₀ ⊆ L_{m+1}`; off `L_m` it lies on an open face `F̆_p` with `p ∈ s`
        refine Or.inr (by_contra fun hxL => ?_)
        obtain ⟨p, y, hp, hy, rfl⟩ :=
          Submission.cmcdtfrsd_skeleton_point_on_open_face P m _ (hQL hxS) hxL
        exact hx (mem_iUnion₂.2 ⟨p, (hs p).2 ⟨hp, y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hxS⟩,
          hxM, y, hy, rfl⟩)
      · exact Or.inl ⟨hxM, hxS⟩
    have hae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁) := by
      refine ae_eq_set.2 ⟨hnull, ?_⟩
      rw [Set.sdiff_eq_empty.2 (iUnion₂_subset fun p _ => inter_subset_left), measure_empty]
    -- Step 12: split `Q₀(ω) = ∫_M θ ⟨ω, ξ⟩ dHⁿ` over the disjoint faces and change variables
    have hint := Submission.regcomp_rim_action_integrable P (m + 1) univ R ω
    calc Q₀ ω = ∫ x in R.carrier,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          hR ω
      _ = ∫ x in ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁),
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          setIntegral_congr_set hae
      _ = ∑ p ∈ s, ∫ x in R.carrier ∩ Φ p '' Q₁,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] :=
          integral_biUnion_finset s
            (fun p hp => R.measurableSet_carrier.inter (hF p ((hs p).1 hp).1))
            (fun p hp q hq hpq => (hdisj p q ((hs p).1 hp).1 ((hs q).1 hq).1 hpq).mono
              inter_subset_right inter_subset_right)
            fun p _ => IntegrableOn.mono_set hint inter_subset_left
      _ = _ := Finset.sum_congr rfl fun p hp => hu_rep p ((hs p).1 hp).1 ω

/-- **Disjoint neighbourhoods of the open unit faces** (Simon Ch. 6, §5, proof of 5.1: the open
faces `F̆` get pairwise disjoint neighbourhoods `N_F`).  For `p = (ι, b)` with `ι` strictly
increasing, `π_p(x) = (x_{ι(j)} − b_{ι(j)})ⱼ` is a continuous left inverse of the face map
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`; put `d_p(x) = |x − Φ_p(π_p x)|`.  `N_p` is the set of `x` with
`π_p(x) ∈ (0,1)ᵏ`, `2 d_p(x) < 1` and `2 d_p(x) < min(π_p(x)ⱼ, 1 − π_p(x)ⱼ)` for all `j`: a finite
intersection of strict inequalities between continuous functions, hence open, and it contains
`Φ_p((0,1)ᵏ)`, where `d_p = 0`.  The separation hypothesis gives `2 d_p(x) < |Φ_p(π_p x) − Φ_q(y')|`
for `x ∈ N_p`, `q ≠ p` and `y' ∈ [0,1]ᵏ`.  For `x = Φ_q(y')` this reads `2 d_p(x) < d_p(x)`, so
`Φ_q([0,1]ᵏ)` misses `N_p`; for `x ∈ N_p ∩ N_q` the bounds for `(p, q)` and `(q, p)` contradict the
triangle inequality. -/
theorem Submission.cmcdtfrbv_face_neighbourhoods : ∀ (P k : ℕ), (∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) → ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → IsOpen (N p) ∧ (∀ y : Euclid k, (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N p) ∧ ∀ q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono q.1 → q ≠ p → (∀ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∉ N p) ∧ Disjoint (N p) (N q) := by
  intro P k hS
  -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P, ∀ p y,
      Φ p y = WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hΦ] at hS ⊢
  -- the projections `π_p(x) = (x_{ι(j)} − b_{ι(j)})ⱼ`
  obtain ⟨π, hπ⟩ : ∃ π : (Fin k → Fin P) × (Fin P → ℤ) → Euclid P → Euclid k, ∀ p x,
      π p x = WithLp.toLp 2 (fun j => x (p.1 j) - (p.2 (p.1 j) : ℝ)) := ⟨_, fun _ _ => rfl⟩
  -- step 1: `Φ_p` and `π_p` are continuous
  have hΦc : ∀ p, Continuous (Φ p) := fun p => by
    rw [show Φ p = _ from funext (hΦ p)]
    exact continuous_const.add (continuous_finsetSum _ fun j _ =>
      (PiLp.continuous_apply 2 _ j).smul continuous_const)
  have hπc : ∀ p, Continuous (π p) := fun p => by
    rw [show π p = _ from funext (hπ p)]
    exact (PiLp.continuous_toLp 2 _).comp
      (continuous_pi fun j => (PiLp.continuous_apply 2 _ (p.1 j)).sub continuous_const)
  -- step 2: `π_p(Φ_p y) = y`, as `Φ_p(y)_{ι(m)} = b_{ι(m)} + yₘ` for injective `ι`
  have hleft : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → ∀ y, π p (Φ p y) = y := by
    intro p hp y
    have hcoord : ∀ l : Fin P, Φ p y l = (p.2 l : ℝ) + ∑ j, if p.1 j = l then y j else 0 := by
      intro l
      rw [hΦ, PiLp.add_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      exact if_congr eq_comm rfl rfl
    ext m
    rw [hπ, PiLp.toLp_apply, hcoord,
      Fintype.sum_eq_single m fun j hj => ite_eq_right (hp.injective.ne hj), ite_eq_left rfl]
    ring
  -- step 3: `N_p = {x : π_p(x) ∈ (0,1)ᵏ, 2 d_p(x) < 1, 2 d_p(x) < min(π_p(x)ⱼ, 1 − π_p(x)ⱼ)}`
  obtain ⟨N, hN⟩ : ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p, N p =
      {x | (∀ j, 0 < π p x j ∧ π p x j < 1) ∧ 2 * dist x (Φ p (π p x)) < 1 ∧
        ∀ j, 2 * dist x (Φ p (π p x)) < min (π p x j) (1 - π p x j)} := ⟨_, fun _ => rfl⟩
  -- step 6: `2 d_p(x) < |Φ_p(π_p x) − Φ_q(y')|` for `x ∈ N_p`, `q ≠ p` and `y' ∈ [0,1]ᵏ`
  have hkey : ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q →
      ∀ x ∈ N p, ∀ y' : Euclid k, (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) →
        2 * dist x (Φ p (π p x)) < dist (Φ p (π p x)) (Φ q y') := by
    intro p q hp hq hpq x hx y' hy'
    rw [hN] at hx
    obtain ⟨ht, hd₁, hd⟩ := hx
    rcases hS p q hp hq hpq (π p x) y' ht hy' with h | ⟨j, h⟩
    · linarith
    · linarith [hd j]
  -- points of `N_r` project into `[0,1]ᵏ`
  have hmem : ∀ r x, x ∈ N r → ∀ j, 0 ≤ π r x j ∧ π r x j ≤ 1 := fun r x hx j => by
    rw [hN] at hx
    exact ⟨(hx.1 j).1.le, (hx.1 j).2.le⟩
  refine ⟨N, fun p hp => ⟨?_, fun y hy => ?_, fun q hq hqp => ⟨fun y hy hx => ?_, ?_⟩⟩⟩
  · -- step 4: `N_p` is a finite intersection of open sets `{f < h}`, `f`, `h` continuous
    have hcj : ∀ j, Continuous fun x => π p x j := fun j =>
      (PiLp.continuous_apply 2 _ j).comp (hπc p)
    have hd : Continuous fun x => 2 * dist x (Φ p (π p x)) :=
      continuous_const.mul (continuous_id.dist ((hΦc p).comp (hπc p)))
    rw [hN]
    simp only [ofPred_and, ofPred_forall]
    exact (isOpen_iInter_of_finite fun j => (isOpen_lt continuous_const (hcj j)).inter
      (isOpen_lt (hcj j) continuous_const)).inter ((isOpen_lt hd continuous_const).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt hd ((hcj j).min (continuous_const.sub (hcj j)))))
  · -- step 5: `π_p(Φ_p y) = y`, so `d_p(Φ_p y) = 0`
    rw [hN, Set.mem_ofPred_eq, hleft p hp y, dist_self, mul_zero]
    exact ⟨hy, one_pos, fun j => lt_min (hy j).1 (sub_pos.mpr (hy j).2)⟩
  · -- step 7: for `x = Φ_q(y)`, step 6 with `y' = y` gives `2 d_p(x) < d_p(x)`
    have h := hkey p q hp hq hqp.symm (Φ q y) hx y hy
    linarith [dist_comm (Φ q y) (Φ p (π p (Φ q y))),
      dist_nonneg (x := Φ q y) (y := Φ p (π p (Φ q y)))]
  · -- step 8: step 6 for `(p, q)` and `(q, p)` contradicts the triangle inequality
    rw [Set.disjoint_left]
    intro x hxp hxq
    have h₁ := hkey p q hp hq hqp.symm x hxp (π q x) (hmem q x hxq)
    have h₂ := hkey q p hq hp hqp x hxq (π p x) (hmem p x hxp)
    have h₃ := dist_triangle (Φ p (π p x)) x (Φ q (π q x))
    linarith [dist_comm (Φ p (π p x)) x, dist_comm (Φ q (π q x)) (Φ p (π p x))]
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion
/-- **Simon 6.2.11** (a current vanishes off its support).  If `ω ∈ 𝒟ⁿ(U)` and
`spt ω ∩ spt S = ∅`, then `S(ω) = 0`.  The compact set `K = spt ω ⊆ U` lies in the zero region of
`S`, so finitely many open `W₁, …, Wₘ` on which `S` vanishes cover `K`.  A smooth partition of
unity `ψ₁, …, ψₘ` on `K` subordinate to them splits `ω = Σᵢ ψᵢω` into test forms with
`spt (ψᵢω) ⊆ Wᵢ`, each annihilated by `S`. -/
theorem Submission.dtc_vanish_off_support : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0 := by
  intro P n U S ω hdisj
  classical
  -- `K = spt ω` is a compact subset of `U`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKc : IsCompact K := ω.property.1.2
  have hKU : K ⊆ U := ω.property.2
  -- `K` lies in the zero region `⋃₀ 𝒲`, hence in finitely many members of `𝒲`
  let 𝒲 : Set (Set (Euclid P)) :=
    {W | IsOpen W ∧ IsCompact (closure W) ∧ closure W ⊆ U ∧ S.VanishesOn W}
  have hKZ : K ⊆ ⋃ W : 𝒲, (W : Set (Euclid P)) := by
    intro x hx
    have hxZ : x ∈ S.zeroRegion := by
      by_contra hxZ
      exact Set.disjoint_left.mp hdisj hx ⟨hKU hx, hxZ⟩
    rwa [GeometricCurrentOn.zeroRegion, Set.sUnion_eq_iUnion] at hxZ
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun W : 𝒲 => (W : Set (Euclid P)))
    (fun W => W.2.1) hKZ
  let Wt : t → Set (Euclid P) := fun i => ((i : 𝒲) : Set (Euclid P))
  have hKt : K ⊆ ⋃ i, Wt i := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩
  -- a smooth partition of unity `ψᵢ` on `K` with `spt ψᵢ ⊆ Wᵢ`
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hKc.isClosed Wt (fun i => (i : 𝒲).2.1) hKt
  -- each `ψᵢω` is a test form in `U` supported in `Wᵢ`
  have hmem : ∀ i, (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ∈ TestFormOn U n ∧
      tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ Wt i := by
    intro i
    have hsK : tsupport (fun x => ψ i x • (ω : DifferentialForm (Euclid P) n) x) ⊆ K :=
      tsupport_smul_subset_right _ _
    refine ⟨⟨⟨?_, ?_⟩, hsK.trans hKU⟩, (tsupport_smul_subset_left _ _).trans (hψ i)⟩
    · exact (contMDiff_iff_contDiff.mp (ψ i).contMDiff).smul ω.property.1.1
    · exact IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) hsK
  let ωi : t → TestFormOn U n := fun i => ⟨_, (hmem i).1⟩
  -- `ω = Σᵢ ψᵢω`, since `Σᵢ ψᵢ = 1` on `K` and `ω = 0` off `K`
  have hsum : ω = ∑ i, ωi i := by
    apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    change (ω : DifferentialForm (Euclid P) n) x =
      ∑ i, ψ i x • (ω : DifferentialForm (Euclid P) n) x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_smul, ← finsum_eq_sum_of_fintype, ψ.sum_eq_one hx, one_smul]
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [h0]
  -- linearity: `S(ω) = Σᵢ S(ψᵢω) = 0`
  change S.toCurrent ω = 0
  rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ => (i : 𝒲).2.2.2.2 (ωi i) (hmem i).2

/-- The union of the closed faces `Φ_q([0,1]^{m+1})`, `q = (ι, b) ∈ s`, of the affine maps
`Φ_q(y) = b + Σⱼ yⱼ e_{ι(j)}` is compact.  The closed unit cube `C ⊆ ℝ^{m+1}` is closed (an
intersection of coordinate half-spaces) and bounded (`‖y‖ ≤ √(m + 1)` on `C`), hence compact
since `ℝ^{m+1}` is proper.  Each `Φ_q` is continuous, so each `Φ_q(C)` is compact, and the set
is the finite union `⋃_{q ∈ s} Φ_q(C)`. -/
theorem Submission.cmcdtfrbvbsf_closed_faces_isCompact : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))), IsCompact {x : Euclid P | ∃ q ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = x} := by
  intro P m s
  -- the closed unit cube `C ⊆ ℝ^{m+1}`
  set C : Set (Euclid (m + 1)) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1} with hC_def
  -- `C` is closed: an intersection of coordinate half-spaces
  have hC_closed : IsClosed C := by
    simp only [hC_def, Set.ofPred_forall, Set.ofPred_and]
    exact isClosed_iInter fun i =>
      (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  -- `C` is bounded: `‖y‖ ≤ √(m + 1)` on `C`
  have hC_bdd : Bornology.IsBounded C := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨√(m + 1), fun y hy => ?_⟩
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]
            exact pow_le_one₀ (hy i).1 (hy i).2
      _ = m + 1 := by simp
  -- `C` is compact, `ℝ^{m+1}` being proper
  have hC : IsCompact C := Metric.isCompact_of_isClosed_isBounded hC_closed hC_bdd
  -- each face `Φ_q(C)` is compact, `Φ_q` being continuous
  have hΦ : ∀ q ∈ s, IsCompact ((fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' C) :=
    fun q _ => hC.image (by fun_prop)
  -- the set is the finite union `⋃_{q ∈ s} Φ_q(C)`
  convert s.isCompact_biUnion hΦ using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_image, exists_prop, hC_def]
/-- **Deformation theorem, face replacement** (Simon 6.5).  Let `Q₀` be the `(m+1)`-current
`Q₀(ω) = Σ_{p ∈ s} ∫_{(0,1)^{m+1}} u_p(y) ω(Φ_p y)(e_{ι_p(0)}, …, e_{ι_p(m)}) dy` with
`Φ_p(y) = b_p + Σⱼ yⱼ e_{ι_p(j)}`, and let `Z` be the union of the closed faces `Φ_q([0,1]^{m+1})`,
`q ∈ s`.  If `spt γ ∩ Z = ∅` then `∂Q₀(γ) = Q₀(dγ) = 0` (Simon (6.2.3)): `spt dγ ⊆ spt γ`, so
`dγ` vanishes at every `Φ_p(y)`, `y ∈ (0,1)^{m+1}`, and every integrand is zero. -/
theorem Submission.cmcdtfrbvbsf_boundary_vanish_off_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ γ : TestFormOn (univ : Set (Euclid P)) m, Disjoint (tsupport (γ : DifferentialForm (Euclid P) m)) {x : Euclid P | ∃ q ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = x} → Q₀.boundary γ = 0 := by
  intro P m s u Q₀ hQ₀ γ hdisj
  -- `∂Q₀(γ) = Q₀(dγ)`, expanded with the representation of `Q₀`
  rw [GeometricCurrentOn.boundary_apply, hQ₀]
  -- each integrand vanishes on `(0,1)^{m+1}`: `Φ_p(y)` lies on the closed faces, which miss
  -- `spt dγ ⊆ spt γ`
  refine Finset.sum_eq_zero fun p hp => setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
  have hx : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
      ∉ tsupport (exteriorDerivativeTestOn univ m γ : DifferentialForm (Euclid P) (m + 1)) :=
    fun hx => Set.disjoint_left.mp hdisj
      (tsupport_exteriorDerivative_subset (γ : DifferentialForm (Euclid P) m) hx)
      ⟨p, hp, y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
  rw [image_eq_zero_of_notMem_tsupport hx, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
    mul_zero]

/-- **The boundary of a sum of face integrals is supported on the closed faces.**  Let
`Q₀(ω) = Σ_{p ∈ s} ∫_{(0,1)^{m+1}} u_p(y) ω(Φ_p y)(e_{ι_p(0)}, …, e_{ι_p(m)}) dy` with
`Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}`.  Then `spt ∂Q₀ ⊆ Z := ⋃_{q ∈ s} Φ_q([0,1]^{m+1})`.  `Z` is
compact, and `∂Q₀(γ) = Q₀(dγ) = 0` whenever `spt γ ∩ Z = ∅`, because `spt dγ ⊆ spt γ` misses every
`Φ_p((0,1)^{m+1})`.  Hence `spt ∂Q₀ ⊆ Z` by Simon 6.2.11. -/
theorem Submission.cmcdtfrbv_boundary_support_subset_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ Q₀.boundary.support, ∃ q ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = x := by
  intro P m s u Q₀ hQ₀ x hx
  -- `Z` is a compact subset of `ℝ^P` and `∂Q₀` kills every test form whose support misses `Z`,
  -- so `spt ∂Q₀ ⊆ Z`; membership in `Z` is the conclusion
  exact (Submission.rsd_cmr_support_subset_of_vanish P m univ _ Q₀.boundary isOpen_univ
    (Submission.cmcdtfrbvbsf_closed_faces_isCompact P m s) (subset_univ _)
    (Submission.cmcdtfrbvbsf_boundary_vanish_off_faces P m s u Q₀ hQ₀)).1 hx
/-- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
`n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
formula, and the Leibniz formula with `|x(l)| ≤ ‖x‖` gives `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`, so
`θ⁰` is continuous. -/
theorem Submission.cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
  intro P n I
  -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
  let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun x k => x (I k)
      map_add' := fun x y => by
        funext k
        simp
      map_smul' := fun c x => by
        funext k
        simp }
  -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
  let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
  -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
  have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  -- Step 4: the Leibniz formula, `|sign σ| = 1` and `|x(l)| ≤ ‖x‖` give
  -- `|θ⁰(v)| ≤ n! ∏ⱼ ‖vⱼ‖`
  have hbound : ∀ v : Fin n → Euclid P, ‖θ₀ v‖ ≤ (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
    intro v
    rw [hθ₀, Real.norm_eq_abs, Matrix.det_apply]
    calc |∑ σ : Equiv.Perm (Fin n),
            Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j|
        ≤ ∑ σ : Equiv.Perm (Fin n),
            |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ∏ j, ‖v j‖ := by
          refine Finset.sum_le_sum fun σ _ => ?_
          have hσ : |Equiv.Perm.sign σ • ∏ j, Matrix.of (fun k j => v j (I k)) (σ j) j| =
              ∏ j, |v j (I (σ j))| := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
              simp [h, Finset.abs_prod]
          rw [hσ]
          gcongr with j
          rw [← Real.norm_eq_abs]
          exact PiLp.norm_apply_le (v j) (I (σ j))
      _ = (n.factorial : ℝ) * ∏ j, ‖v j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
            nsmul_eq_mul]
  -- Step 5: `θ = θ⁰.mkContinuous n!` is an `n`-covector with the same values as `θ⁰`
  exact ⟨θ₀.mkContinuous (n.factorial : ℝ) hbound, hθ₀⟩
/-- **Kronecker property of the determinant covectors** (Simon 6.1, chapter-06.txt lines 22–47:
`dxʲ(v) = vⱼ`, `dx^{i₁} ∧ ⋯ ∧ dx^{iₙ}(v₁, …, vₙ) = det(dx^{iₖ}(vⱼ))` (1.1), and
`ω_α = ω(e_{i₁}, …, e_{iₙ})` for the basis `{dx^α : α ∈ I_{n,P}}` (1.2)): if `I`, `J` are strictly
increasing and `θ(v) = det (v_j(I k))_{k,j}`, then `θ(e_{J 1}, …, e_{J n}) = δ_{IJ}`.  The matrix
of `θ(e_J)` has entries `[I k = J j]`.  It is the identity if `I = J`.  Otherwise some `I k₀` is
not a value of `J` (else `range I ⊆ range J`, both have `n` elements, so the ranges agree and the
strictly increasing maps agree), and row `k₀` vanishes. -/
theorem Submission.cmr_cc_det_covector_basis_kronecker : ∀ (P n : ℕ) (I J : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → StrictMono J → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → θ (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 := by
  intro P n I J θ hI hJ hθ
  -- Step 1: `θ(e_J) = det M` with `M k j = e_{J j}(I k)`
  rw [hθ]
  -- Step 2: `M k j = e_{J j}(I k) = if I k = J j then 1 else 0`
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  by_cases hIJ : I = J
  · -- Step 3: if `I = J`, injectivity of `J` gives `M = 1`, so `det M = 1`
    rw [ite_eq_left hIJ]
    subst hIJ
    refine (congrArg Matrix.det ?_).trans Matrix.det_one
    ext k j
    simp only [Matrix.of_apply, Matrix.one_apply, hI.injective.eq_iff]
  · -- Step 4: if `I ≠ J`, some `I k₀` is not a value of `J`: otherwise `range I ⊆ range J`,
    -- both ranges have `n` elements, so they are equal and `I = J`
    rw [ite_eq_right hIJ]
    obtain ⟨k₀, hk₀⟩ : ∃ k₀, I k₀ ∉ Set.range J := by
      by_contra hcon
      have hsub : Set.range I ⊆ Set.range J := by
        rintro _ ⟨k, rfl⟩
        by_contra hk
        exact hcon ⟨k, hk⟩
      have hcard : (Set.range J).ncard ≤ (Set.range I).ncard :=
        ((Set.ncard_range_of_injective hJ.injective).trans
          (Set.ncard_range_of_injective hI.injective).symm).le
      exact hIJ ((hI.range_inj_of_wellFoundedLT hJ).1 (Set.eq_of_subset_of_ncard_le hsub hcard))
    -- Step 5: row `k₀` of `M` vanishes, so `det M = 0`
    refine Matrix.det_eq_zero_of_row_eq_zero k₀ fun j => ?_
    simp only [Matrix.of_apply]
    exact ite_eq_right fun hEq => hk₀ ⟨j, hEq.symm⟩

/-- **Face covectors of a coordinate `(m+1)`-plane** (Simon Ch. 6, (1.1), (1.2), (1.15)): for
strictly increasing `ι : Fin (m + 1) → Fin P` put `J_j = ι ∘ j.succAbove` (the `j`-th index
dropped) and `ε_j = (-1)^j dx^{J_j}`, with `dx^{J_j}` from `Submission.cmr_cc_det_covector_exists`.
The `J_j` are strictly increasing and pairwise distinct (for `j ≠ j'`, `ι j` is a value of `J_{j'}`
but not of `J_j`), so by `Submission.cmr_cc_det_covector_basis_kronecker` the coefficient
`α_c(e_I)` of `α_c = Σ_j c_j ε_j` is `(-1)^j c_j` if `I = J_j` and `0` for every other strictly
increasing `I`.  This gives `α_c(e_{J_j}) = (-1)^j c_j` and `|α_c| = √(Σ_j c_j²)`. -/
theorem Submission.cmcdtfrbv_face_covectors : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P), StrictMono ι → ∃ ε : Fin (m + 1) → Covector (Euclid P) m, (∀ c : Fin (m + 1) → ℝ, covectorEuclideanNorm (∑ j, c j • ε j) = Real.sqrt (∑ j, c j ^ 2)) ∧ ∀ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)), (∑ j', c j' • ε j') (fun k => EuclideanSpace.single (ι (j.succAbove k)) (1 : ℝ)) = (-1) ^ (j : ℕ) * c j := by
  intro P m ι hι
  -- Step 1: the face indices `J_j = ι ∘ j.succAbove` are strictly increasing
  obtain ⟨J, hJ⟩ : ∃ J : Fin (m + 1) → Fin m → Fin P, ∀ j k, J j k = ι (j.succAbove k) :=
    ⟨fun j k => ι (j.succAbove k), fun _ _ => rfl⟩
  have hJmono : ∀ j, StrictMono (J j) := by
    intro j a b hab
    rw [hJ, hJ]
    exact hι (Fin.strictMono_succAbove j hab)
  -- Step 2: `j ↦ J_j` is injective: for `j ≠ j'`, `ι j` is a value of `J_{j'}` but not of `J_j`
  have hJinj : Injective J := by
    intro j j' h
    by_contra hne
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    have h1 : J j z = ι j := by rw [h, hJ, hz]
    rw [hJ] at h1
    exact Fin.succAbove_ne j z (hι.injective h1)
  -- Step 3: `θ_j = dx^{J_j}` by `det_covector_exists`, and `ε_j = (-1)^j θ_j`
  choose θ hθ using fun j => Submission.cmr_cc_det_covector_exists P m (J j)
  obtain ⟨ε, hε⟩ : ∃ ε : Fin (m + 1) → Covector (Euclid P) m,
      ∀ j, ε j = ((-1 : ℝ) ^ (j : ℕ)) • θ j :=
    ⟨fun j => ((-1 : ℝ) ^ (j : ℕ)) • θ j, fun _ => rfl⟩
  -- Steps 4–5: by `det_covector_kronecker`, on a strictly increasing `I`
  -- `α_c(e_I) = Σ_{j'} [J_{j'} = I] (-1)^{j'} c_{j'}`
  have hval : ∀ (c : Fin (m + 1) → ℝ) (I : Fin m → Fin P), StrictMono I →
      (∑ j', c j' • ε j') (fun k => EuclideanSpace.basisFun (Fin P) ℝ (I k)) =
        ∑ j', if J j' = I then (-1) ^ (j' : ℕ) * c j' else 0 := by
    intro c I hI
    rw [ContinuousAlternatingMap.sum_apply]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, hε, ContinuousAlternatingMap.smul_apply,
      Submission.cmr_cc_det_covector_basis_kronecker P m (J j') I (θ j') (hJmono j') hI (hθ j')]
    split_ifs
    · rw [smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
    · rw [smul_zero, smul_zero]
  -- Step 6: `α_c(e_{J_j}) = (-1)^j c_j`, since only `j' = j` has `J_{j'} = J_j`
  have hface : ∀ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)),
      (∑ j', c j' • ε j') (fun k => EuclideanSpace.basisFun (Fin P) ℝ (J j k)) =
        (-1) ^ (j : ℕ) * c j := by
    intro c j
    rw [hval c (J j) (hJmono j), Finset.sum_eq_single j]
    · exact ite_eq_left rfl
    · intro j' _ hj'
      exact ite_eq_right fun h => hj' (hJinj h)
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  refine ⟨ε, fun c => ?_, fun c j => ?_⟩
  · -- Step 7: the squared coefficient of `α_c` on a strictly increasing `I` is `c_j²` if
    -- `I = J_j` and `0` otherwise, so the squared coefficients sum to `Σ_j c_j²`
    rw [covectorEuclideanNorm]
    congr 1
    symm
    refine Fintype.sum_of_injective J hJinj _ _ (fun I hI => ?_) (fun j => ?_)
    · split_ifs with hmono
      · have h0 : (∑ j', if J j' = I then (-1 : ℝ) ^ (j' : ℕ) * c j' else 0) = 0 :=
          Finset.sum_eq_zero fun j' _ => ite_eq_right fun h => hI ⟨j', h⟩
        rw [hval c I hmono, h0]
        ring
      · rfl
    · rw [ite_eq_left (hJmono j), hface c j]
      rcases neg_one_pow_eq_or ℝ (j : ℕ) with h | h <;> rw [h] <;> ring
  · -- Step 6 with `e_l = EuclideanSpace.single l 1`
    have hv : (fun k => EuclideanSpace.single (ι (j.succAbove k)) (1 : ℝ)) =
        fun k => EuclideanSpace.basisFun (Fin P) ℝ (J j k) := by
      funext k
      rw [EuclideanSpace.basisFun_apply, hJ]
    rw [hv]
    exact hface c j
/-- **Cut-off lift of a vector field on a face** (Simon Ch. 6, proof of 5.1, displays (27)–(28):
the test forms giving `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|`, as in 2.35).  Let
`Φ_p(y) = b + Σ_j y_j e_{ι(j)}` be the chart of the face and `π(x) = (x_{ι(j)} − b_{ι(j)})_j` its
affine left inverse.  Put `G = χ · (g ∘ π)`, where the smooth cut-off `χ : ℝᴾ → [0, 1]` equals
`1` near the compact set `K = Φ_p(spt g) ⊆ N` and is supported in `N`.  Then `G = g ∘ π` near
each `Φ_p(y)` with `y ∈ (0,1)ⁿ`.  So `D(G_a)(Φ_p y)(e_{ι(a)}) = (Dg(y) ê_a)_a` by the chain rule,
and the sum over `a` is `trace Dg(y)`. -/
theorem Submission.cmcdtfrbv_cutoff_field : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ G : Euclid P → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ tsupport G ⊆ N ∧ (∀ x, ‖G x‖ ≤ 1) ∧ ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → ∑ a, fderiv ℝ (fun x => G x a) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (EuclideanSpace.single (p.1 a) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
  intro P m p N g hmono hN hΦN hg hgc hgQ hg1
  -- Step 1: the face chart `Φ_p` and its affine left inverse `π = L - c₀`
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let L : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (p.1 j))
      map_add' := fun x x' => by ext j; simp
      map_smul' := fun c x => by ext j; simp }
  have hL : ∀ x, L x = WithLp.toLp 2 (fun j => x (p.1 j)) := fun x => rfl
  let c₀ : Euclid (m + 1) := WithLp.toLp 2 (fun j => (p.2 (p.1 j) : ℝ))
  let π : Euclid P → Euclid (m + 1) := fun x => L x - c₀
  -- (i) `L e_{ι(a)} = ê_a` and (ii) `π (Φ_p y) = y`, since `ι` is injective
  have hLe : ∀ a, L (EuclideanSpace.single (p.1 a) (1 : ℝ)) = EuclideanSpace.single a (1 : ℝ) := by
    intro a
    ext j
    simp [hL, PiLp.single_apply, hmono.injective.eq_iff]
  have hπΦ : ∀ y, π (Φ y) = y := by
    intro y
    ext j
    simp [π, hL, c₀, Φ, Pi.single_apply, hmono.injective.eq_iff]
  have hΦc : Continuous Φ := by fun_prop
  have hπc : ContDiff ℝ (⊤ : ℕ∞) π := L.contDiff.sub contDiff_const
  -- Steps 2–3: `K = Φ_p(spt g)` is a compact subset of `N`, and `cthickening δ K ⊆ N`
  have hKc : IsCompact (Φ '' tsupport g) := hgc.isCompact.image hΦc
  have hKN : Φ '' tsupport g ⊆ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΦN y (hgQ hy)
  obtain ⟨δ, hδ, hδN⟩ := hKc.exists_cthickening_subset_open hN hKN
  have hr0 : 0 < δ / 3 := by positivity
  -- Step 4: smooth `χ` with values in `[0, 1]`, `χ = 1` exactly on `cthickening (δ / 3) K` and
  -- `spt χ ⊆ cthickening (2 δ / 3) K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := 2 * (δ / 3)) (E := Φ '' tsupport g))
    (isClosed_cthickening (δ := δ / 3) (E := Φ '' tsupport g))
    (cthickening_subset_thickening' (by positivity) (by linarith) _)
  have hχK : tsupport χ ⊆ cthickening (2 * (δ / 3)) (Φ '' tsupport g) := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  -- Step 5: `G = χ · (g ∘ π)` is smooth, compactly supported in `N` and bounded by `1`
  refine ⟨fun x => χ x • g (π x), hχ.smul (hg.comp hπc), ?_, ?_, ?_, ?_⟩
  · exact hKc.cthickening.of_isClosed_subset (isClosed_tsupport _)
      ((tsupport_smul_subset_left _ _).trans hχK)
  · exact (tsupport_smul_subset_left _ _).trans
      (hχK.trans ((cthickening_mono (by linarith) _).trans hδN))
  · intro x
    have hx := hχr (mem_range_self x)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans (hg1 _)
  · intro y hy
    -- Step 6: `G = g ∘ π` near `Φ_p y`; case A: `χ = 1` near `K`, case B: `g ∘ π = 0` nearby
    have hloc : (fun x => χ x • g (π x)) =ᶠ[𝓝 (Φ y)] fun x => g (π x) := by
      by_cases hyg : y ∈ tsupport g
      · have hmem : Φ y ∈ thickening (δ / 3) (Φ '' tsupport g) :=
          self_subset_thickening hr0 _ (mem_image_of_mem Φ hyg)
        filter_upwards [isOpen_thickening.mem_nhds hmem] with x hx
        rw [(hχ1 x).1 (thickening_subset_cthickening _ _ hx), one_smul]
      · have hopen : IsOpen (π ⁻¹' (tsupport g)ᶜ) :=
          (isClosed_tsupport g).isOpen_compl.preimage hπc.continuous
        have hmem : Φ y ∈ π ⁻¹' (tsupport g)ᶜ := by
          simpa [hπΦ] using hyg
        filter_upwards [hopen.mem_nhds hmem] with x hx
        rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]
    -- Step 7: by the chain rule, `D(G_a)(Φ_p y)(e_{ι(a)}) = (Dg(y)(L e_{ι(a)}))_a = (Dg(y) ê_a)_a`
    have hgd : HasFDerivAt g (fderiv ℝ g y) (π (Φ y)) := by
      rw [hπΦ]
      exact (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
    have hπd : HasFDerivAt π L (Φ y) := L.hasFDerivAt.sub_const c₀
    have key : ∀ a, fderiv ℝ (fun x => (χ x • g (π x)) a) (Φ y)
        (EuclideanSpace.single (p.1 a) (1 : ℝ)) =
          fderiv ℝ g y (EuclideanSpace.single a (1 : ℝ)) a := by
      intro a
      have hcoord : (fun x => (χ x • g (π x)) a) =ᶠ[𝓝 (Φ y)] fun x => g (π x) a :=
        hloc.fun_comp (fun v => v a)
      have hd : HasFDerivAt (fun x => g (π x) a)
          ((PiLp.proj 2 (fun _ : Fin (m + 1) => ℝ) a).comp ((fderiv ℝ g y).comp L)) (Φ y) := by
        have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (g (π (Φ y))) a).comp (Φ y)
          (hgd.comp (Φ y) hπd)
        exact h
      rw [hcoord.fderiv_eq, hd.fderiv]
      simp [hLe]
    -- Step 8: `trace A = Σ_a (A ê_a)_a` in the standard orthonormal basis of `Euclid (m + 1)`
    show ∑ a, fderiv ℝ (fun x => (χ x • g (π x)) a) (Φ y)
      (EuclideanSpace.single (p.1 a) (1 : ℝ)) = _
    simp only [key]
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    simp [EuclideanSpace.inner_single_left]

/-- **The divergence test form of a face** (Simon Ch. 6, proof of the deformation theorem 5.1).
With the face covectors `εⱼ` of `ι = p.1` (`cmcdtfrbv_face_covectors`) and the cutoff field
`G = χ · (g ∘ π)` (`cmcdtfrbv_cutoff_field`), `γ(x) = Σⱼ Gⱼ(x) εⱼ` is a test form on `ℝᴾ` with
`tsupport γ ⊆ tsupport G ⊆ N` and `|γ(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`.  As
`γ(x)(removeNth i E) = (-1)ⁱ Gᵢ(x)` for `E = (e_{ι j})ⱼ`, `exteriorDerivative_apply` gives
`dγ(Φ_p y)(E) = Σᵢ DGᵢ(Φ_p y)(e_{ι i}) = trace Dg(y)` for `y ∈ Q₁`. -/
theorem Submission.cmcdtfrbv_divergence_test_form : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ γ : TestFormOn (univ : Set (Euclid P)) m, tsupport (γ : DifferentialForm (Euclid P) m) ⊆ N ∧ (∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → exteriorDerivative (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
  intro P m p N g hι hN hΦN hg hgc hgs hg1
  -- Step 1: the face covectors `εⱼ` of `ι = p.1`
  obtain ⟨ε, hεn, hεf⟩ := Submission.cmcdtfrbv_face_covectors P m p.1 hι
  -- Step 2: the cutoff field `G = χ · (g ∘ π)`
  obtain ⟨G, hG, hGc, hGN, hG1, hGd⟩ :=
    Submission.cmcdtfrbv_cutoff_field P m p N g hι hN hΦN hg hgc hgs hg1
  -- Step 3: `ω(x) = Σⱼ Gⱼ(x) εⱼ`
  set ω : DifferentialForm (Euclid P) m := fun x => ∑ j, G x j • ε j with hω
  -- Step 4: `ω` is smooth, as each coefficient `Gⱼ = proj j ∘ G` is
  have hGj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun x => G x j := fun j =>
    (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hωs : ContDiff ℝ (⊤ : ℕ∞) ω :=
    ContDiff.sum fun j _ => (hGj j).smul contDiff_const
  -- Step 5: `supp ω ⊆ supp G`, so `ω` has compact support and `tsupport ω ⊆ tsupport G ⊆ N`
  have hωG : support ω ⊆ support G := by
    intro x hx
    rw [mem_support] at hx ⊢
    contrapose! hx
    simp [hω, hx]
  have hωT : IsTestForm ω ∧ tsupport ω ⊆ (univ : Set (Euclid P)) :=
    ⟨⟨hωs, hGc.mono hωG⟩, subset_univ _⟩
  refine ⟨⟨ω, hωT⟩, (closure_mono hωG).trans hGN, fun x => ?_, fun y hy => ?_⟩
  · -- Step 6: `|ω(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`
    calc covectorEuclideanNorm (ω x) = Real.sqrt (∑ j, G x j ^ 2) := hεn fun j => G x j
      _ = ‖G x‖ := by rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ 1 := hG1 x
  · -- Step 7: `dω(Φ y)(E) = Σᵢ (-1)ⁱ D[ω(·)(removeNth i E)](Φ y)(e_{ι i})`; by the face
    -- evaluation `ω(·)(removeNth i E) = (-1)ⁱ Gᵢ`, so the `i`-th term is `DGᵢ(Φ y)(e_{ι i})`
    show exteriorDerivative ω _ _ = _
    rw [exteriorDerivative_apply ((hωs.differentiable (by simp)) _), ← hGd y hy]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hface : (fun x => ω x (i.removeNth fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) =
        fun x => (-1 : ℝ) ^ (i : ℕ) * G x i :=
      funext fun x => hεf (fun j => G x j) i
    rw [hface, fderiv_const_mul ((hGj i).differentiable (by simp) _), smul_apply,
      smul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← mul_assoc, ← mul_pow,
      neg_one_mul, neg_neg, one_pow, one_mul]
/-- Local mass is superadditive over finitely many pairwise disjoint regions (Simon 6.2.5):
`∑_{i ∈ s} M_{N_i}(S) ≤ M_{⋃_{i ∈ s} N_i}(S)`.  If `ω_A`, `ω_B` are admissible for disjoint
regions `A`, `B`, then at each point at most one of them is nonzero, so `ω_A + ω_B` is admissible
for `A ∪ B` and `S(ω_A + ω_B) = S(ω_A) + S(ω_B)`; replacing a form with negative value by `0`
gives `M_A(S) + M_B(S) ≤ M_{A ∪ B}(S)`, and induction on `s` finishes. -/
theorem Submission.cmcdtfrbv_massOn_disjoint_sum_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ι : Type) (s : Finset ι) (N : ι → Set (Euclid P)), (↑s : Set ι).PairwiseDisjoint N → ∑ i ∈ s, S.massOn (N i) ≤ S.massOn (⋃ i ∈ s, N i) := by
  classical
  intro P n U S ι s N hN
  -- the zero form is admissible for every region
  have hzero : ∀ A : Set (Euclid P), (0 : TestFormOn U n) ∈ massAdmissibleOn U n A :=
    fun A => ⟨by simp, fun x => by simp⟩
  -- forms admissible for disjoint regions glue to a form admissible for the union
  have hglue : ∀ A B : Set (Euclid P), Disjoint A B → ∀ ωA ∈ massAdmissibleOn U n A,
      ∀ ωB ∈ massAdmissibleOn U n B, ωA + ωB ∈ massAdmissibleOn U n (A ∪ B) := by
    intro A B hAB ωA hA ωB hB
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_add]
      exact (tsupport_add _ _).trans (union_subset_union hA.1 hB.1)
    · rw [Submodule.coe_add, Pi.add_apply]
      by_cases hx : x ∈ tsupport (ωA : DifferentialForm (Euclid P) n)
      · have hxB : x ∉ tsupport (ωB : DifferentialForm (Euclid P) n) := fun h =>
          hAB.notMem_of_mem_left (hA.1 hx) (hB.1 h)
        rw [image_eq_zero_of_notMem_tsupport hxB, add_zero]
        exact hA.2 x
      · rw [image_eq_zero_of_notMem_tsupport hx, zero_add]
        exact hB.2 x
  -- superadditivity on two disjoint regions
  have htwo : ∀ A B : Set (Euclid P), Disjoint A B →
      S.massOn A + S.massOn B ≤ S.massOn (A ∪ B) := by
    intro A B hAB
    have key : ∀ ωA ∈ massAdmissibleOn U n A, ∀ ωB ∈ massAdmissibleOn U n B,
        ENNReal.ofReal (S ωA) + ENNReal.ofReal (S ωB) ≤ S.massOn (A ∪ B) := by
      intro ωA hA ωB hB
      rcases le_or_gt (S ωA) 0 with hωA | hωA
      · rw [ENNReal.ofReal_of_nonpos hωA, zero_add]
        exact S.le_massOn ⟨hB.1.trans subset_union_right, hB.2⟩
      rcases le_or_gt (S ωB) 0 with hωB | hωB
      · rw [ENNReal.ofReal_of_nonpos hωB, add_zero]
        exact S.le_massOn ⟨hA.1.trans subset_union_left, hA.2⟩
      rw [← ENNReal.ofReal_add hωA.le hωB.le, ← map_add S.toCurrent ωA ωB]
      exact S.le_massOn (hglue A B hAB ωA hA ωB hB)
    calc S.massOn A + S.massOn B
        = (⨆ ω ∈ massAdmissibleOn U n A, ENNReal.ofReal (S ω)) +
            ⨆ ω ∈ massAdmissibleOn U n B, ENNReal.ofReal (S ω) := by
          simp only [GeometricCurrentOn.massOn, sSup_image]
      _ ≤ S.massOn (A ∪ B) := ENNReal.biSup_add_biSup_le ⟨0, hzero A⟩ ⟨0, hzero B⟩ key
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 ha)] at hN
    have hdisj : Disjoint (N a) (⋃ i ∈ s, N i) := by
      simp only [Set.disjoint_iUnion_right]
      exact fun i hi => hN.2 i hi
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    calc S.massOn (N a) + ∑ i ∈ s, S.massOn (N i)
        ≤ S.massOn (N a) + S.massOn (⋃ i ∈ s, N i) := add_le_add le_rfl (ih hN.1)
      _ ≤ S.massOn (N a ∪ ⋃ i ∈ s, N i) := htwo _ _ hdisj

/-- **Boundary variation on the open faces of a lattice chain** (Simon Ch. 6, proof of 5.1,
displays (27)–(28) and (32), chapter-06.txt lines 1849–1893: `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|` by the
reasoning of 2.35).  Let `Q₀(ω) = Σ_{p ∈ s} ∫_{Q₁} u_p(y) ω(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) dy`
with `M(∂Q₀) < ∞`.  The separation `(c)` of `cmcdtfr_face_geometry` and
`cmcdtfrbv_face_neighbourhoods` give open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing every
other closed face; put `V_p = M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`.  Then `Σ_p V_p ≤ M(∂Q₀)` by
`cmcdtfrbv_massOn_disjoint_sum_le`.  `(i)` The test form `γ` of `cmcdtfrbv_divergence_test_form`
is admissible for `N_p` with `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = div g(y)` on `Q₁`, and `dγ`
vanishes on the other faces, so `∫ u_p div g = Q₀(dγ) = ∂Q₀(γ) ≤ V_p`.  `(ii)` If `V_p ≠ 0`, some
admissible `γ` for `N_p` has `∂Q₀(γ) > 0`; by (VO) `tsupport γ ⊆ N_p` meets `spt ∂Q₀`, which lies
on the closed faces (`cmcdtfrbv_boundary_support_subset_faces`), and of these only the face of
`p` meets `N_p`.  The integrability of the `u_p` is not needed. -/
theorem Submission.cmcdtfr_boundary_variation : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → Q₀.boundary.mass < ∞ → ∃ V : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q₀.boundary.mass ∧ (∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p) ∧ (∀ p ∈ s, V p ≠ 0 → ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.boundary.support) := by
  intro hVO P m s u Q₀ hs _hu hQ₀ hmass
  -- step 1: open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing the other closed faces, from the
  -- separation `(c)` of `face_geometry`
  obtain ⟨N, hN⟩ := Submission.cmcdtfrbv_face_neighbourhoods P (m + 1)
    fun p q hp hq => ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p q hp hq).2.2
  -- step 3: `M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`, so `V_p := M_{N_p}(∂Q₀)` is a real number
  have hfin : ∀ p, Q₀.boundary.massOn (N p) ≠ ∞ := fun p =>
    ne_top_of_le_ne_top hmass.ne (Q₀.boundary.massOn_mono (subset_univ (N p)))
  refine ⟨fun p => (Q₀.boundary.massOn (N p)).toReal, fun p _ => ENNReal.toReal_nonneg, ?_, ?_,
    ?_⟩
  · -- step 9: the `N_p`, `p ∈ s`, are pairwise disjoint, so `Σ_p M_{N_p}(∂Q₀) ≤ M(∂Q₀)`
    have hdisj : (s : Set ((Fin (m + 1) → Fin P) × (Fin P → ℤ))).PairwiseDisjoint N := by
      intro p hp q hq hpq
      exact ((hN p (hs p hp)).2.2 q (hs q hq) hpq.symm).2
    rw [ENNReal.ofReal_sum_of_nonneg fun p _ => ENNReal.toReal_nonneg]
    calc ∑ p ∈ s, ENNReal.ofReal (Q₀.boundary.massOn (N p)).toReal
        = ∑ p ∈ s, Q₀.boundary.massOn (N p) :=
          Finset.sum_congr rfl fun p _ => ENNReal.ofReal_toReal (hfin p)
      _ ≤ Q₀.boundary.massOn (⋃ p ∈ s, N p) :=
          Submission.cmcdtfrbv_massOn_disjoint_sum_le P m univ Q₀.boundary _ s N hdisj
      _ ≤ Q₀.boundary.mass := Q₀.boundary.massOn_mono (subset_univ _)
  · intro p hp g hg hgc hgs hgb
    obtain ⟨hNo, hNF, hNq⟩ := hN p (hs p hp)
    -- step 5: the test form `γ` for `g` is admissible for `N_p`, so `∂Q₀(γ) ≤ V_p`
    obtain ⟨γ, hγs, hγn, hγd⟩ := Submission.cmcdtfrbv_divergence_test_form P m p (N p) g
      (hs p hp) hNo hNF hg hgc hgs hgb
    have hle : Q₀.boundary γ ≤ (Q₀.boundary.massOn (N p)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin p)).1 (Q₀.boundary.le_massOn ⟨hγs, hγn⟩)
    -- the open unit cube `Q₁` is measurable
    have hcoord : ∀ i : Fin (m + 1), Measurable fun y : Euclid (m + 1) => y i := fun i =>
      (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 _)
    have hQ₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
      rw [show {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
          ⋂ i, ({y | 0 < y i} ∩ {y | y i < 1}) by ext y; simp]
      exact MeasurableSet.iInter fun i =>
        (measurableSet_lt measurable_const (hcoord i)).inter
          (measurableSet_lt (hcoord i) measurable_const)
    -- steps 6–8: `∂Q₀(γ) = Q₀(dγ) = Σ_q ∫_{Q₁} u_q(y) dγ(Φ_q y)(E_q) dy = ∫_{Q₁} u_p div g`
    have hval : Q₀.boundary γ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
      rw [GeometricCurrentOn.boundary_apply, hQ₀, Finset.sum_eq_single_of_mem p hp]
      · -- step 6: `dγ(Φ_p y)(E_p) = trace Dg(y)` for `y ∈ Q₁`
        refine setIntegral_congr_fun hQ₁ fun y hy => ?_
        change u p y * exteriorDerivative (γ : DifferentialForm (Euclid P) m) _ _ = _
        rw [hγd y hy]
      · -- step 7: for `q ≠ p`, `Φ_q(Q₁)` misses `N_p ⊇ tsupport γ ⊇ tsupport dγ`
        intro q hq hqp
        refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
        have hz : exteriorDerivative (γ : DifferentialForm (Euclid P) m)
            (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
              ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = 0 :=
          image_eq_zero_of_notMem_tsupport fun h => (hNq q (hs q hq) hqp).1 y
            (fun i => ⟨(hy i).1.le, (hy i).2.le⟩) (hγs (tsupport_exteriorDerivative_subset _ h))
        change u q y * exteriorDerivative (γ : DifferentialForm (Euclid P) m) _ _ = 0
        rw [hz]
        simp
    rw [← hval]
    exact hle
  · intro p hp hV
    -- step 10: `V_p ≠ 0` gives `M_{N_p}(∂Q₀) > 0`, so some admissible `γ` for `N_p` has
    -- `∂Q₀(γ) > 0`
    have hpos : 0 < Q₀.boundary.massOn (N p) := by
      refine pos_iff_ne_zero.2 fun h => hV ?_
      simp only [h, ENNReal.toReal_zero]
    unfold GeometricCurrentOn.massOn at hpos
    obtain ⟨_, ⟨γ, hγ, rfl⟩, hγpos⟩ := lt_sSup_iff.1 hpos
    -- by (VO), `tsupport γ ⊆ N_p` meets `spt ∂Q₀` at some `x`
    obtain ⟨x, hxγ, hx⟩ := Set.not_disjoint_iff.1 fun hd =>
      (ENNReal.ofReal_pos.1 hγpos).ne' (hVO P m univ Q₀.boundary γ hd)
    -- step 2: `x = Φ_q(y)` with `q ∈ s` and `y ∈ [0,1]ⁿ`; step 1: `q = p`, since `x ∈ N_p`
    obtain ⟨q, hq, y, hy, rfl⟩ :=
      Submission.cmcdtfrbv_boundary_support_subset_faces P m s u Q₀ hQ₀ x hx
    by_cases hqp : q = p
    · subst hqp
      exact ⟨y, hy, hx⟩
    · exact absurd (hγ.1 hxγ) (((hN p (hs p hp)).2.2 q (hs q hq) hqp).1 y hy)
/-- **Coefficient bounds for the Euclidean covector norm** (Simon Ch. 6, 1.15; facts used for the
face currents in the proof of the Deformation Theorem 6.5.1, displays (29)–(30) and (34)).  With
`e` the standard basis of `ℝᴾ`, let `f J = α(e_{J(0)}, …, e_{J(k-1)})²` for strictly increasing
`J : Fin k → Fin P` and `f J = 0` otherwise, so `|α|² = ∑_J f J` is a sum of nonnegative terms.
(i) The single term `f I = α(e_I)²` is at most the sum.  (ii) For strictly increasing
`ι : Fin (k+1) → Fin P` the faces `ι ∘ i.succAbove` are strictly increasing and pairwise
distinct, so `∑_i α(e_{ι ∘ i.succAbove})²` is a sub-sum of `∑_J f J`. -/
theorem Submission.cmcdtfrfic_coeff_bounds : ∀ (P k : ℕ) (α : Covector (Euclid P) k), (∀ I : Fin k → Fin P, StrictMono I → |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α) ∧ ∀ ι : Fin (k + 1) → Fin P, StrictMono ι → ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2 ≤ covectorEuclideanNorm α ^ 2 := by
  intro P k α
  -- Step 1: `|α| = √(∑_J f J)` with `f ≥ 0` and `f J = α(e_J)²` for strictly increasing `J`
  obtain ⟨f, hf0, hfJ, hnorm⟩ : ∃ f : (Fin k → Fin P) → ℝ, (∀ J, 0 ≤ f J) ∧
      (∀ J, StrictMono J → f J = (α (fun j => EuclideanSpace.single (J j) (1 : ℝ))) ^ 2) ∧
      covectorEuclideanNorm α = √(∑ J, f J) := by
    refine ⟨_, fun J => ?_, fun J hJ => ?_, rfl⟩
    · split_ifs <;> positivity
    · rw [ite_eq_left hJ]
      simp only [EuclideanSpace.basisFun_apply]
  have hS : 0 ≤ ∑ J, f J := Finset.sum_nonneg fun J _ => hf0 J
  refine ⟨fun I hI => ?_, fun ι hι => ?_⟩
  -- Step 2 (i): the single term `f I = α(e_I)²` is at most the sum, so `|α(e_I)| ≤ √(∑_J f J)`
  · rw [hnorm]
    exact Real.abs_le_sqrt ((hfJ I hI).symm.trans_le
      (Finset.single_le_sum (fun J _ => hf0 J) (Finset.mem_univ I)))
  -- Step 3 (ii): the faces `ι ∘ i.succAbove` are strictly increasing and pairwise distinct
  · have hinj : Function.Injective fun i : Fin (k + 1) => ι ∘ i.succAbove :=
      fun i i' h => Fin.succAbove_left_injective (hι.injective.comp_left h)
    -- Step 4: so the left side is the sub-sum of `∑_J f J = |α|²` over the faces
    rw [hnorm, Real.sq_sqrt hS]
    calc ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2
        = ∑ i : Fin (k + 1), f (ι ∘ i.succAbove) :=
          Finset.sum_congr rfl fun i _ => (hfJ _ (hι.comp (Fin.strictMono_succAbove i))).symm
      _ = ∑ J ∈ Finset.univ.image fun i : Fin (k + 1) => ι ∘ i.succAbove, f J :=
          (Finset.sum_image fun i _ i' _ h => hinj h).symm
      _ ≤ ∑ J, f J := Finset.sum_le_univ_sum_of_nonneg hf0

/-- **The divergence field of a face** (Simon Ch. 6, proof of Theorem 5.1, (29)–(30): the field
`G_p` of the face-current construction).  Let `γ` be a smooth `m`-form on `ℝᴾ`,
`ι : Fin (m + 1) → Fin P` strictly increasing, `a ∈ ℝᴾ`, `E = (e_{ι 0}, …, e_{ι m})` and
`Φ(y) = a + Σⱼ yⱼ e_{ι j}`.  Put `Gᵢ(y) = (−1)ⁱ γ(Φ y)(E⁽ⁱ⁾)`, where `E⁽ⁱ⁾ = i.removeNth E` omits
`e_{ι i}`.  Then `G` is `C^∞`; `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²` by the coefficient bound
`cmcdtfrfic_coeff_bounds` (ii); and, as `DΦ(y) bᵢ = e_{ι i}`,
`trace DG(y) = Σᵢ (DG(y) bᵢ)ᵢ = Σᵢ (−1)ⁱ D(γ(·)(E⁽ⁱ⁾))(Φ y) e_{ι i} = dγ(Φ y)(E)`
(`exteriorDerivative_apply`). -/
theorem Submission.cmcdtfrfic_divergence_field : ∀ (P m : ℕ) (γ : DifferentialForm (Euclid P) m) (ι : Fin (m + 1) → Fin P) (a : Euclid P), ContDiff ℝ (⊤ : ℕ∞) γ → StrictMono ι → ∃ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y, ‖G y‖ ≤ covectorEuclideanNorm (γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) = exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  intro P m γ ι a hγ hι
  classical
  -- the affine map `Φ = a + L`, `L y = Σⱼ yⱼ e_{ι j}`, with `L bᵢ = e_{ι i}`
  set E : Fin (m + 1) → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  let L : Euclid (m + 1) →L[ℝ] Euclid P := ∑ j, (EuclideanSpace.proj j).smulRight (E j)
  have hL : ∀ y : Euclid (m + 1), L y = ∑ j, y j • E j := fun y => by simp [L]
  let Φ : Euclid (m + 1) → Euclid P := fun y => a + L y
  have hΦE : ∀ y : Euclid (m + 1),
      a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) = Φ y := fun y => by simp [Φ, hL, E]
  have hΦd : ∀ y, HasFDerivAt Φ L y := fun y => L.hasFDerivAt.const_add a
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := contDiff_const.add L.contDiff
  have hLb : ∀ i : Fin (m + 1), L (EuclideanSpace.single i 1) = E i := fun i => by simp [hL]
  -- the coefficients `gᵢ = γ(·)(E⁽ⁱ⁾)`: evaluation at a fixed tuple is continuous linear
  let g : Fin (m + 1) → Euclid P → ℝ := fun i x => γ x (i.removeNth E)
  have hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (g i) := fun i =>
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (i.removeNth E)).contDiff.comp hγ
  -- the field `Gᵢ(y) = (−1)ⁱ gᵢ(Φ y)`
  let G : Euclid (m + 1) → Euclid (m + 1) :=
    fun y => WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ) * g i (Φ y)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G :=
    contDiff_euclidean.2 fun i => contDiff_const.mul ((hg i).comp hΦs)
  refine ⟨G, hGs, fun y => ?_, fun y => ?_⟩
  · -- `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²`
    rw [hΦE y, EuclideanSpace.norm_eq, ← Real.sqrt_sq (covectorEuclideanNorm_nonneg (γ (Φ y)))]
    refine Real.sqrt_le_sqrt (le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_)
      ((Submission.cmcdtfrfic_coeff_bounds P m (γ (Φ y))).2 ι hι))
    simp only [G, g, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul]
    rw [show (-1 : ℝ) ^ ((i : ℕ) * 2) = 1 by rw [mul_comm, pow_mul, neg_one_sq, one_pow], one_mul]
    rfl
  · -- `trace DG(y) = Σᵢ (DG(y) bᵢ)ᵢ` and `dγ(Φ y)(E) = Σᵢ (−1)ⁱ Dgᵢ(Φ y) e_{ι i}`
    rw [hΦE y, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ),
      exteriorDerivative_apply (hγ.differentiable (by simp)).differentiableAt E]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    -- `(DG(y) bᵢ)ᵢ = D(Gᵢ)(y) bᵢ = (−1)ⁱ Dgᵢ(Φ y)(L bᵢ)`, by uniqueness of the derivative
    have hGi := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (G y) i).comp y
      (hGs.differentiable (by simp) y).hasFDerivAt
    have hGi' : HasFDerivAt ((fun f : Euclid (m + 1) => f i) ∘ G)
        (((-1 : ℝ) ^ (i : ℕ)) • (fderiv ℝ (g i) (Φ y)).comp L) y :=
      (((hg i).differentiable (by simp) (Φ y)).hasFDerivAt.comp y (hΦd y)).const_mul _
    have happ := congrArg (fun T => T (EuclideanSpace.single i (1 : ℝ))) (hGi.unique hGi')
    simp only [ContinuousLinearMap.comp_apply, FunLike.coe_smul, Pi.smul_apply, PiLp.proj_apply,
      hLb] at happ
    simp only [map_one, one_mul, ContinuousLinearMap.coe_coe]
    rw [happ, zsmul_eq_mul]
    simp [g]
/-- **Simon Ch. 6, proof of 5.1, (29)–(30)**: integrable densities on finitely many unit faces
define a current.  For `p = (ι, b) ∈ s` let `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`,
`E_p = (e_{ι(0)}, …, e_{ι(m)})`, and let `w_p` be integrable on the open unit cube
`Q₁ ⊆ ℝ^{m+1}`.  As the `e_l` are unit vectors, `|ω(x)(E_p)| ≤ ‖ω(x)‖`, which is bounded because
`ω` is continuous with compact support; so `y ↦ w_p(y) ω(Φ_p(y))(E_p)` is integrable on `Q₁`, and
`L(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy` is linear with
`|L(ω)| ≤ (Σ_{p ∈ s} ∫_{Q₁} |w_p|) δ` whenever `‖ω(x)‖ ≤ δ` for all `x`.  Order-`0` uniform
convergence on a common compact set, and vanishing off it, give the sequential continuity of
`L`. -/
theorem Submission.cmcdtfrfic_current_exists : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s w hw
  -- the face maps `Φ_p`, the frames `E_p` and the open unit cube `Q₁`
  let Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let E : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → Euclid P := fun p j =>
    EuclideanSpace.single (p.1 j) (1 : ℝ)
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
  -- `y ↦ ω(Φ_p(y))(E_p)` is continuous
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
      Continuous (ω : DifferentialForm (Euclid P) (m + 1)) :=
    fun ω => ω.property.1.1.continuous
  have hΦ : ∀ p, Continuous (Φ p) := fun p =>
    continuous_const.add (continuous_finsetSum _ fun j _ =>
      (PiLp.continuous_apply 2 _ j).smul continuous_const)
  have hh : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) p,
      Continuous fun y => (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p) :=
    fun ω p => (continuous_eval_const _).comp ((hcont ω).comp (hΦ p))
  -- `|α(E_p)| ≤ ‖α‖`, the `e_l` being unit vectors
  have hev : ∀ (α : Covector (Euclid P) (m + 1)) p, ‖α (E p)‖ ≤ ‖α‖ := by
    intro α p
    simpa [E, PiLp.norm_single] using α.le_opNorm (E p)
  -- (I): `w_p` is integrable on `Q₁`, and `y ↦ ω(Φ_p(y))(E_p)` is continuous and bounded
  have hI : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s,
      IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p))
        Q₁ := by
    intro ω p hp
    obtain ⟨C, hC⟩ := ω.property.1.2.exists_bound_of_continuous (hcont ω)
    exact (hw p hp).mul_bdd (c := C) (hh ω p).aestronglyMeasurable
      (Eventually.of_forall fun y => (hev _ p).trans (hC _))
  -- the linear functional `L(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy`
  let L : TestFormOn (univ : Set (Euclid P)) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω =>
        ∑ p ∈ s, ∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)
      map_add' := by
        intro ω η
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← integral_add (hI ω p hp) (hI η p hp)]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, mul_add]
      map_smul' := by
        intro c ω
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        ring }
  -- `|L(ω)| ≤ A δ` whenever `‖ω(x)‖ ≤ δ` for all `x`, where `A = Σ_{p ∈ s} ∫_{Q₁} |w_p|`
  set A : ℝ := ∑ p ∈ s, ∫ y in Q₁, |w p y| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
  have hest : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (δ : ℝ),
      (∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ δ) → |L ω| ≤ A * δ := by
    intro ω δ hδ
    have hterm : ∀ p ∈ s,
        |∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)| ≤
          (∫ y in Q₁, |w p y|) * δ := by
      intro p hp
      rw [← integral_mul_const δ (fun y => |w p y|)]
      refine (Real.norm_eq_abs _).symm.le.trans ?_
      refine norm_integral_le_of_norm_le ((hw p hp).abs.mul_const δ)
        (Eventually.of_forall fun y => ?_)
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((hev _ p).trans (hδ _)) (abs_nonneg _)
    calc |L ω|
        ≤ ∑ p ∈ s, |∫ y in Q₁, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (Φ p y) (E p)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, (∫ y in Q₁, |w p y|) * δ := Finset.sum_le_sum hterm
      _ = A * δ := by rw [hA, Finset.sum_mul]
  -- sequential continuity: order-`0` uniform convergence on the common compact set `K`
  have hseq : ∀ (ωs : ℕ → TestFormOn (univ : Set (Euclid P)) (m + 1)),
      TestFormOnConverges ωs 0 → Tendsto (fun j => L (ωs j)) atTop (𝓝 0) := by
    intro ωs hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := hunif 0
    rw [Metric.tendstoUniformlyOn_iff] at h0
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h0 _ hδ)
    refine ⟨N, fun j hj => ?_⟩
    have hbd : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ ε / (A + 1) := by
      intro x
      by_cases hx : x ∈ K
      · have := hN j hj x hx
        rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp] at this
        simp only [Function.comp_apply, Submodule.coe_zero, Pi.zero_apply, map_zero,
          dist_zero_left, LinearIsometryEquiv.norm_map] at this
        exact this.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp j h)), norm_zero]
        exact hδ.le
    rw [Real.dist_eq, sub_zero]
    calc |L (ωs j)| ≤ A * (ε / (A + 1)) := hest (ωs j) _ hbd
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  exact ⟨hI, ⟨L, hseq⟩, fun ω => rfl⟩
/-- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30)): let
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy` for every test form `ω`,
where `p = (ι_p, b_p)`, `Q₁ = (0, 1)ⁿ`, `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and each `w_p` is
integrable on `Q₁`.  Then every `x ∈ spt D` is `Φ_p(y)` for some `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0` and
some `y ∈ [0, 1]ⁿ`.  Otherwise `x` lies outside the compact union `Z` of the closed faces
`Φ_p([0, 1]ⁿ)` with `∫_{Q₁} |w_p| ≠ 0`, so a ball `B_r(x)` misses `Z`.  If `spt ω ⊆ B_r(x)`, every
summand vanishes: `w_p = 0` a.e. on `Q₁` when `∫_{Q₁} |w_p| = 0`, and `ω = 0` on `Φ_p(Q₁) ⊆ Z`
otherwise.  So `D` vanishes on `B_r(x)` and `x ∈ zeroRegion D`, contradicting `x ∈ spt D`. -/
theorem Submission.cmcdtfrfic_support_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x := by
  classical
  intro P m s w D hw hD x hx
  by_contra hne
  -- `Z`: the union of the closed faces `Φ_p([0, 1]ⁿ)` over the `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0`
  let Z : Set (Euclid P) :=
    ⋃ p ∈ s.filter fun p => (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0,
      (fun z : Fin (m + 1) → ℝ =>
        WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, z j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ''
        Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  -- `Z` is compact: a finite union of continuous images of the compact cube
  have hZ : IsCompact Z := Finset.isCompact_biUnion _ fun p _ =>
    (isCompact_univ_pi fun _ => isCompact_Icc).image (by fun_prop)
  -- by assumption, `x ∉ Z`
  have hxZ : x ∉ Z := by
    intro hxZ
    obtain ⟨p, hp, z, hz, hzx⟩ := Set.mem_iUnion₂.mp hxZ
    obtain ⟨hps, hpw⟩ := Finset.mem_filter.mp hp
    exact hne ⟨p, hps, hpw, WithLp.toLp 2 z, fun i => hz i (Set.mem_univ i), hzx⟩
  -- a ball `B_r(x)` disjoint from the closed set `Z`
  obtain ⟨r, hr, hrZ⟩ := Metric.isOpen_iff.mp hZ.isClosed.isOpen_compl x hxZ
  -- `D` vanishes on `B_r(x)`, so `x ∈ zeroRegion D`, contradicting `x ∈ spt D`
  refine hx.2 (Set.mem_sUnion.mpr ⟨Metric.ball x r, ⟨Metric.isOpen_ball,
    (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      Metric.closure_ball_subset_closedBall, Set.subset_univ _, fun ω hω => ?_⟩,
    Metric.mem_ball_self hr⟩)
  rw [hD ω]
  refine Finset.sum_eq_zero fun p hp => ?_
  by_cases hpw : (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) = 0
  · -- `∫_{Q₁} |w_p| = 0`: `w_p = 0` a.e. on `Q₁`, so the integrand vanishes a.e.
    have h0 := (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (w p y)) (hw p hp).abs).mp hpw
    refine integral_eq_zero_of_ae (h0.mono fun y hy => ?_)
    have hy' : w p y = 0 := abs_eq_zero.mp hy
    show w p y * _ = 0
    rw [hy', zero_mul]
  · -- `∫_{Q₁} |w_p| ≠ 0`: `Φ_p(Q₁) ⊆ Z` misses `B_r(x) ⊇ spt ω`, so the integrand vanishes on `Q₁`
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    have hyZ : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Z :=
      Set.mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpw⟩)
        ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
    have hω0 : (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hrZ (hω h) hyZ
    rw [hω0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]

/-- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30) and (34)): for faces
`p = (ι_p, b_p) ∈ s` with `ι_p` strictly increasing and densities `w_p` integrable on
`Q₁ = (0, 1)ⁿ`, put `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy`.  The integrands are
integrable and `D` is a current (I)–(II).  Every such `D` has (a) `M(D) ≤ Σ_p ∫_{Q₁} |w_p|`, since
`|ω(x)(e_{ι_p})| ≤ |ω(x)| ≤ 1` for admissible `ω`; (b) `M(∂D) ≤ Σ_p B_p` whenever
`|∫_{Q₁} w_p div G| ≤ B_p` for all smooth `G` with `|G| ≤ 1`, since `∂D(γ) = D(dγ)` and on the face
`p` the integrand `dγ(Φ_p(y))(e_{ι_p})` is `div G_p(y)` for a smooth `G_p` with
`|G_p| ≤ |γ ∘ Φ_p| ≤ 1`; (c) `spt D` lies in the closed faces with `∫_{Q₁} |w_p| ≠ 0`. -/
theorem Submission.cmcdtfr_face_integral_current : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ∧ (∀ B : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ B p) → D.boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, B p)) ∧ (∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x) := by
  intro P m s w hι hw
  -- (I)–(II): the integrands are integrable and the formula defines a current
  obtain ⟨hint, hex⟩ := Submission.cmcdtfrfic_current_exists P m s w hw
  -- (III)(c) is the support lemma; (a) and (b) bound each admissible evaluation
  refine ⟨hint, hex, fun D hD => ⟨?_, fun B hB => ?_,
    Submission.cmcdtfrfic_support_faces P m s w D hw hD⟩⟩
  · -- (a): for admissible `ω`, `|w_p(y) ω(Φ_p(y))(e_{ι_p})| ≤ |w_p(y)| |ω(Φ_p(y))| ≤ |w_p(y)|`
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hD ω]
    refine Finset.sum_le_sum fun p hp => (Real.le_norm_self _).trans
      (norm_integral_le_of_norm_le (hw p hp).abs (ae_of_all _ fun y => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      (((Submission.cmcdtfrfic_coeff_bounds P (m + 1) _).1 p.1 (hι p hp)).trans (hω.2 _))
  · -- (b): for admissible `γ`, `∂D(γ) = D(dγ)`, and on the face `p` the integrand is
    -- `w_p div G_p` with `|G_p| ≤ |γ ∘ Φ_p| ≤ 1`, so the `p`-th summand is at most `B_p`
    refine sSup_le ?_
    rintro r ⟨γ, hγ, rfl⟩
    refine ENNReal.ofReal_le_ofReal ?_
    rw [GeometricCurrentOn.boundary_apply, hD]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨G, hG, hGn, hGt⟩ := Submission.cmcdtfrfic_divergence_field P m
      (γ : DifferentialForm (Euclid P) m) p.1 (WithLp.toLp 2 fun i => (p.2 i : ℝ))
      γ.property.1.1 (hι p hp)
    calc _ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
          integral_congr_ae (ae_of_all _ fun y => congrArg (w p y * ·) (hGt y).symm)
      _ ≤ |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| := le_abs_self _
      _ ≤ B p := hB p hp G hG fun y => (hGn y).trans (hγ.2 _)

/-- **Isometric images: Borel, `Hᵏ`-measure and change of variables** (Simon Ch. 6 §5, deformation
theorem: integrals over a unit lattice face `Φ_p((0,1)ᵏ)` are computed on its parameter cube).  For
an isometry `Φ : ℝᵏ → ℝᴾ` and a Borel set `A ⊆ ℝᵏ`, `Φ(A)` is Borel, `Hᵏ(Φ(A)) = Lᵏ(A)` and
`∫_{Φ(A)} h dHᵏ = ∫_A h ∘ Φ dLᵏ` for every `h : ℝᴾ → ℝ`.  As `ℝᵏ` is complete, `Φ` is a closed,
hence measurable, embedding; `Hᵏ` is isometry invariant and equals `Lᵏ` on `ℝᵏ`; and
`Φ_#Hᵏ = Hᵏ⌞range Φ` restricts to `Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A)`, so changing variables along `Φ` needs no
integrability of `h` (both Bochner integrals vanish when it fails). -/
theorem Submission.cmcdtfrpi_isometry_image_integral : ∀ (P k : ℕ) (Φ : Euclid k → Euclid P) (A : Set (Euclid k)), Isometry Φ → MeasurableSet A → MeasurableSet (Φ '' A) ∧ μHE[k] (Φ '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in Φ '' A, h x ∂μHE[k] = ∫ y in A, h (Φ y) := by
  intro P k Φ A hΦ hA
  -- step 1: `ℝᵏ` is complete, so the isometry `Φ` is a closed, hence measurable, embedding
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  refine ⟨hemb.measurableSet_image.mpr hA, ?_, fun h => ?_⟩
  -- steps 2-3: `Hᵏ(Φ(A)) = Hᵏ(A) = Lᵏ(A)`, by isometry invariance and `Hᵏ = Lᵏ` on `ℝᵏ`
  · rw [hΦ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- step 4: `Hᵏ⌞Φ(A) = (Hᵏ⌞range Φ)⌞Φ(A) = (Φ_#Hᵏ)⌞Φ(A) = Φ_#(Hᵏ⌞Φ⁻¹(Φ(A))) = Φ_#(Lᵏ⌞A)`
  have hpush : μHE[k].restrict (Φ '' A) = (volume.restrict A).map Φ := by
    rw [← Measure.restrict_restrict_of_subset (image_subset_range Φ A),
      ← hΦ.map_euclideanHausdorffMeasure, hemb.restrict_map, hemb.injective.preimage_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  -- step 5: change of variables along the measurable embedding `Φ`, for every `h`
  rw [hpush, hemb.integral_map]
/-- **A set that agrees with `x + V` near `x` has approximate tangent space `V` at `x`** (Simon
Ch. 3, Definition 1.4; applied to the open unit lattice faces carrying an integer polyhedral chain
in the deformation theorem, Simon Ch. 6, §5).  Let `f ∈ C_c(ℝᴾ)` vanish off the ball
`B = B(0, R)` and `0 < r < δ / R`.  For `y ∈ B`, both a `z` with `η_{x,r}(z) = y` and
`z = x + r y` satisfy `|z − x| = r|y| < rR < δ`, so the hypothesis gives
`B ∩ η_{x,r}(M) = B ∩ V`.  As `f = 0` off the Borel ball `B`, `∫_S f dHⁿ = ∫_{B ∩ S} f dHⁿ` for
every set `S`; hence `∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ` for `r ∈ (0, δ / R)`, and the blow-up
integrals are eventually constant as `r ↓ 0`.  No measurability of `M` is used. -/
theorem Submission.cmcdtfrpi_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (δ : ℝ), Module.finrank ℝ V = n → 0 < δ → (∀ z : Euclid P, dist z x < δ → (z ∈ M ↔ z - x ∈ V)) → HasApproximateTangentSpaceAt n M x V := by
  intro P n M x V δ hV hδ hM
  -- step 1: `dim V = n` is a hypothesis; fix `f ∈ C_c(ℝᴾ)`
  refine ⟨hV, fun f => ?_⟩
  -- step 2: `tsupport f ⊆ B̄(0, R₀)`, so `f` vanishes off `B = B(0, R)` for `R = max R₀ 0 + 1`
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R, hR, hf⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y ∉ ball (0 : Euclid P) R, f y = 0 :=
    ⟨max R₀ 0 + 1, by positivity, fun y hy => image_eq_zero_of_notMem_tsupport fun hyf =>
      hy (mem_ball.2 ((mem_closedBall.1 (hR₀ hyf)).trans_lt (by linarith [le_max_left R₀ 0])))⟩
  -- step 4: `∫_S f dHⁿ = ∫_{B ∩ S} f dHⁿ` for every set `S`, as `(Hⁿ⌞S)⌞B = Hⁿ⌞(B ∩ S)`
  have hB : ∀ S : Set (Euclid P), ∫ y in S, f y ∂μHE[n] = ∫ y in ball 0 R ∩ S, f y ∂μHE[n] :=
    fun S => by
      rw [← Measure.restrict_restrict (measurableSet_ball : MeasurableSet (ball (0 : Euclid P) R)),
        setIntegral_eq_integral_of_forall_compl_eq_zero hf]
  -- step 6: the blow-up integrals are constant for `r ∈ (0, δ / R) ∈ 𝓝[>] 0`
  refine (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR)] with r ⟨hr, hrR⟩
  have hrδ : r * R < δ := (lt_div_iff₀ hR).1 hrR
  -- step 3: `B ∩ η_{x,r}(M) = B ∩ V`
  have hset : ball (0 : Euclid P) R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
      ball 0 R ∩ (V : Set (Euclid P)) := by
    ext y
    constructor
    · -- `y = r⁻¹ (z − x)` with `z ∈ M`: `|z − x| = r|y| < rR < δ`, so `z − x ∈ V` and `y ∈ V`
      rintro ⟨hyB, z, hz, rfl⟩
      have hy : ‖r⁻¹ • (z - x)‖ < R := mem_ball_zero_iff.1 hyB
      have hzx : dist z x < δ :=
        calc dist z x = ‖r • r⁻¹ • (z - x)‖ := by rw [smul_inv_smul₀ hr.ne', dist_eq_norm]
          _ = r * ‖r⁻¹ • (z - x)‖ := by rw [norm_smul, Real.norm_of_nonneg hr.le]
          _ < r * R := mul_lt_mul_of_pos_left hy hr
          _ < δ := hrδ
      exact ⟨hyB, V.smul_mem r⁻¹ ((hM z hzx).1 hz)⟩
    · -- `y ∈ V`: `z = x + r y` has `z − x = r y ∈ V` and `|z − x| = r|y| < rR < δ`, so `z ∈ M`
      rintro ⟨hyB, hyV⟩
      have hzx : dist (x + r • y) x < δ :=
        calc dist (x + r • y) x = r * ‖y‖ := by
              rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg hr.le]
          _ < r * R := mul_lt_mul_of_pos_left (mem_ball_zero_iff.1 hyB) hr
          _ < δ := hrδ
      refine ⟨hyB, x + r • y, (hM _ hzx).2 ?_, ?_⟩
      · rw [add_sub_cancel_left]
        exact V.smul_mem r hyV
      -- `η_{x,r}(x + r y) = r⁻¹ (r y) = y`
      · change r⁻¹ • (x + r • y - x) = y
        rw [add_sub_cancel_left, inv_smul_smul₀ hr.ne']
  -- step 5: `∫_{η_{x,r}(M)} f = ∫_{B ∩ η_{x,r}(M)} f = ∫_{B ∩ V} f = ∫_V f`
  rw [hB, hB (V : Set (Euclid P)), hset]
/-- **Coordinate `k`-planes and their unit orientations** (Simon Ch. 6, (1.2), (1.7): the
`k`-vector `e_α = e_{i₁} ∧ ⋯ ∧ e_{iₖ}` pairs as `⟨ω, e_α⟩ = ω(e_{i₁}, …, e_{iₖ})`; §5: a face
`F ∈ 𝓛ₖ` lies in a coordinate `k`-plane, oriented by `±e_α` as in (27)).  For strictly increasing
`ι : Fin k → Fin P` the frame `τⱼ = e_{ι(j)}` is the standard orthonormal basis of `ℝᴾ` composed
with the injective `ι`, hence orthonormal and linearly independent, so `V = span{τⱼ}` has
dimension `k`.  Evaluation `α ↦ α(τ)` is linear with `|α(τ)| ≤ ‖α‖ ∏ⱼ ‖τⱼ‖ = ‖α‖`, which gives
the `k`-vector `e` with `e(α) = α(τ)`; the frame `τ` itself witnesses that `e` and `-e` are unit
orientations of `V`. -/
theorem Submission.cmcdtfrpi_coord_plane_orientation : ∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro P k ι hι
  -- step 1: `τ = (eᵢ)ᵢ ∘ ι` is orthonormal, as `ι` is injective
  have hτ : Orthonormal ℝ (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P) :=
    EuclideanSpace.orthonormal_single.comp ι hι.injective
  -- step 3: `α ↦ α(τ)` is linear, and `|α(τ)| ≤ ‖α‖ ∏ⱼ ‖τⱼ‖ = ‖α‖`
  let e : MultiVector P k :=
    LinearMap.mkContinuous
      { toFun := fun α : Covector (Euclid P) k => α fun j => EuclideanSpace.single (ι j) (1 : ℝ)
        map_add' := fun α β => rfl
        map_smul' := fun c α => rfl } 1
      fun α => by
        calc ‖α fun j => EuclideanSpace.single (ι j) (1 : ℝ)‖
            ≤ ‖α‖ * ∏ j, ‖(EuclideanSpace.single (ι j) (1 : ℝ) : Euclid P)‖ := α.le_opNorm _
          _ = 1 * ‖α‖ := by simp [hτ.1]
  -- step 2: an orthonormal family is linearly independent, so `dim V = #(Fin k) = k`
  refine ⟨by rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin], e, fun α => rfl,
    ?_, ?_⟩
  -- step 4: the frame `τ` orients `V` with sign `+` for `e`
  · exact ⟨_, hτ, rfl, Or.inl fun α => rfl⟩
  -- step 5: and with sign `-` for `-e`
  · exact ⟨_, hτ, rfl, Or.inr fun α => rfl⟩
/-- **Open lattice faces are disjoint, and their union is flat near each of its points** (Simon
Ch. 6, §5, chapter-06.txt lines 1841 and 1924–1927: the interiors `F̆` of the faces `F ∈ 𝓛ₖ`, as
used to see that `P = Σ_F β_F [[F]]` is integer multiplicity).  Assume `(FG)`, the frozen type of
`cmcdtfr_face_geometry`.  Let `S` be a finite set of pairs `p = (ι, b)` with `ι` strictly
increasing, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, `F̆_p = Φ_p((0,1)ᵏ)` and `C = ⋃_{q ∈ S} F̆_q`.
`(a)` Distinct open faces are disjoint: a common point would be at distance `0` from itself,
against the separation in `(FG)`.  `(b)` For `p ∈ S`, `t ∈ (0,1)ᵏ` and
`δ = min({1} ∪ {min(tⱼ, 1 − tⱼ)})`, every `z` with `|z − Φ_p(t)| < δ` has `z ∈ C` iff
`z − Φ_p(t) ∈ V_p = span{e_{ι(j)}}`.  By separation, a point of `C` this close to `Φ_p(t)` lies
on `F̆_p`, so `z − Φ_p(t) = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}`.  Conversely, if `z − Φ_p(t) = Σⱼ cⱼ e_{ι(j)}`
then `z = Φ_p(t + c)`, and the isometry in `(FG)` gives `|cⱼ| ≤ |c| = |z − Φ_p(t)| < δ`, so
`t + c ∈ (0,1)ᵏ`. -/
theorem Submission.cmcdtfrpi_face_union_local_plane : (∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)))) → ∀ (P k : ℕ) (S : Finset ((Fin k → Fin P) × (Fin P → ℤ))), (∀ p ∈ S, StrictMono p.1) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}) ((fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})) ∧ ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euclid P, dist z (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) < δ → (z ∈ ⋃ q ∈ S, (fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ↔ z - (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro hFG P k S hS
  refine ⟨fun p hp q hq hpq => ?_, fun p hp t ht => ?_⟩
  · -- step 1: a common point `Φ_p(y) = Φ_q(y')` is at distance `0` from itself, against the
    -- separation of the open face of `p` from the closed face of `q ≠ p`
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    beta_reduce at hyy'
    have hy₁ : ∀ i, 0 < y i ∧ y i < 1 := hy
    have hy'₁ : ∀ i, 0 < y' i ∧ y' i < 1 := hy'
    rcases ((hFG P k).2 p q (hS p hp) (hS q hq)).2.2 hpq y y' hy₁
        (fun i => ⟨(hy'₁ i).1.le, (hy'₁ i).2.le⟩) with h | ⟨j, hj⟩
    · rw [hyy', dist_self] at h
      linarith
    · rw [hyy', dist_self] at hj
      linarith [lt_min (hy₁ j).1 (sub_pos.mpr (hy₁ j).2)]
  -- step 2: `δ = min({1} ∪ {min(tⱼ, 1 - tⱼ)}) > 0`, so `δ ≤ 1` and `δ ≤ min(tⱼ, 1 - tⱼ)`
  obtain ⟨δ, hδ₀, hδ₁, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, δ ≤ min (t j) (1 - t j) := by
    let D := insert (1 : ℝ) (Finset.univ.image fun j => min (t j) (1 - t j))
    have hD : D.Nonempty := Finset.insert_nonempty _ _
    refine ⟨D.min' hD, (Finset.lt_min'_iff D hD).mpr fun d hd => ?_,
      D.min'_le 1 (Finset.mem_insert_self 1 _), fun j =>
      D.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
      exact lt_min (ht j).1 (sub_pos.mpr (ht j).2)
  refine ⟨δ, hδ₀, fun z hz => ⟨fun hzC => ?_, fun hzV => ?_⟩⟩
  · -- step 3 (⇒): `z = Φ_q(t')` for some `q ∈ S` and `t' ∈ (0,1)ᵏ`
    obtain ⟨q, hq, t', ht', hzt'⟩ := Set.mem_iUnion₂.mp hzC
    beta_reduce at hzt'
    rcases eq_or_ne p q with rfl | hpq
    · -- `q = p`: the constant `b` cancels, so `z - Φ_p(t) = Σⱼ (t'ⱼ - tⱼ) e_{ι(j)} ∈ V_p`
      rw [← hzt', add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [← sub_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · -- `q ≠ p`: separation gives `1 ≤ |z - Φ_p(t)|` or `min(tⱼ, 1 - tⱼ) ≤ |z - Φ_p(t)|`,
      -- both impossible as `|z - Φ_p(t)| < δ`
      have ht'₁ : ∀ i, 0 < t' i ∧ t' i < 1 := ht'
      rcases ((hFG P k).2 p q (hS p hp) (hS q hq)).2.2 hpq t t' ht
          (fun i => ⟨(ht'₁ i).1.le, (ht'₁ i).2.le⟩) with h | ⟨j, hj⟩
      · rw [hzt', dist_comm] at h
        linarith
      · rw [hzt', dist_comm] at hj
        linarith [hδt j]
  · -- step 4 (⇐): `z - Φ_p(t) = Σⱼ cⱼ e_{ι(j)}` for some `c ∈ ℝᵏ`
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hzV
    beta_reduce at hc
    -- `t' = t + c` has `Φ_p(t') = Φ_p(t) + (z - Φ_p(t)) = z`
    have hzt' : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, (t + WithLp.toLp 2 c) j • EuclideanSpace.single (p.1 j) (1 : ℝ) = z := by
      simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, hc]
      abel
    -- by the isometry, `|cⱼ| ≤ |t' - t| = |Φ_p(t') - Φ_p(t)| = |z - Φ_p(t)| < δ ≤ min(tⱼ, 1 - tⱼ)`
    have hiso := ((hFG P k).2 p p (hS p hp) (hS p hp)).1 (t + WithLp.toLp 2 c) t
    rw [hzt'] at hiso
    have hc₁ : ∀ j, |c j| < min (t j) (1 - t j) := fun j => by
      have h := PiLp.dist_apply_le (t + WithLp.toLp 2 c) t j
      rw [PiLp.add_apply, PiLp.toLp_apply, Real.dist_eq, add_sub_cancel_left] at h
      linarith [hδt j]
    -- so `t' ∈ (0,1)ᵏ`, and `z = Φ_p(t') ∈ F̆_p ⊆ C`
    refine Set.mem_iUnion₂.mpr ⟨p, hp, t + WithLp.toLp 2 c, fun j => ?_, hzt'⟩
    obtain ⟨h₁, h₂⟩ := abs_lt.mp (hc₁ j)
    rw [PiLp.add_apply, PiLp.toLp_apply]
    constructor <;> linarith [min_le_left (t j) (1 - t j), min_le_right (t j) (1 - t j)]
/-- **A finite disjoint family of oriented rectifiable pieces is an integer multiplicity triple**
(Simon Ch. 6, 3.1 and (‡) of 6.3.1; used for the faces of the deformation theorem 6.5.1).  Let
`F_p ⊆ U` (`p ∈ S`, `S` finite) be pairwise disjoint Borel sets with `Hᵏ(F_p) < ∞` and
`F_p ⊆ G_p(ℝᵏ)` for Lipschitz `G_p`, `m_p > 0`, and `ξ_p` orient an approximate tangent space of
`C = ⋃_{q ∈ S} F_q` at every point of `F_p`.  Then `(C, θ, ξ)` with `θ = Σ_q m_q 1_{F_q}` and
`ξ = ξ_p` on `F_p` (`0` off `C`) is an `IMRep`; the action and `μ_T(ℝᴾ) = ∫_C θ dHᵏ` split over the
disjoint pieces, where `θ = m_p` and `ξ = ξ_p`. -/
theorem Submission.cmcdtfrpi_finite_piece_imrep : ∀ (P k : ℕ) (I : Type) (U : Set (Euclid P)) (S : Finset I) (F : I → Set (Euclid P)) (m : I → ℕ) (ξ : I → MultiVector P k) (G : I → Euclid k → Euclid P), (∀ p ∈ S, MeasurableSet (F p)) → (∀ p ∈ S, F p ⊆ U) → (∀ p ∈ S, μHE[k] (F p) ≠ ∞) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (F p) (F q)) → (∀ p ∈ S, 0 < m p) → (∀ p ∈ S, ∃ K : NNReal, LipschitzWith K (G p)) → (∀ p ∈ S, F p ⊆ range (G p)) → (∀ p ∈ S, ∀ x ∈ F p, ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξ p) Q) → ∃ R : IMRep U k, (∀ ω : TestFormOn U k, R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, (m p : ℝ) * ∫ x in F p, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ R.measure univ = ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
  intro P k I U S F m ξ G hFm hFU hFfin hdisj hmpos hGlip hFG htan
  classical
  -- step 1: the carrier `C = ⋃_{q ∈ S} F_q` is Borel and lies in `U`
  have hCm : MeasurableSet (⋃ q ∈ S, F q) := Finset.measurableSet_biUnion S hFm
  have hCU : (⋃ q ∈ S, F q) ⊆ U := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    exact hFU p hp hxp
  -- step 2: a point of `C` lies in exactly one piece
  have huniq : ∀ p ∈ S, ∀ q ∈ S, ∀ x ∈ F p, x ∈ F q → q = p := by
    intro p hp q hq x hxp hxq
    by_contra hne
    exact Set.disjoint_left.mp (hdisj p hp q hq (Ne.symm hne)) hxp hxq
  -- step 3: the multiplicity `θ = Σ_q m_q 1_{F_q}` is measurable and equals `m_p` on `F_p`
  let θ : Euclid P → ℕ := fun x => ∑ q ∈ S, (F q).indicator (fun _ => m q) x
  have hθm : Measurable θ :=
    Finset.measurable_sum S (fun q hq => measurable_const.indicator (hFm q hq))
  have hθeq : ∀ p ∈ S, ∀ x ∈ F p, θ x = m p := by
    intro p hp x hx
    simp only [θ]
    rw [Finset.sum_eq_single p]
    · simp [Set.indicator_of_mem hx]
    · intro q hq hqp
      have hxq : x ∉ F q := fun h => hqp (huniq p hp q hq x hx h)
      simp [Set.indicator_of_notMem hxq]
    · intro hp'; exact absurd hp hp'
  -- step 4: the orientation `ξ = ξ_p` on `F_p`, `0` off `C`, as a fold of `if x ∈ F_q` over a
  -- list of `S` (a `Finset` sum of indicators would need `ContinuousAdd (MultiVector P k)`)
  let fold : List I → Euclid P → MultiVector P k := fun L x =>
    L.foldr (fun q acc => if x ∈ F q then ξ q else acc) 0
  have hfold_sm : ∀ L : List I, (∀ q ∈ L, q ∈ S) → StronglyMeasurable (fold L) := by
    intro L
    induction L with
    | nil => intro _; exact stronglyMeasurable_const
    | cons a L ih =>
      intro hL
      have ha : a ∈ S := hL a List.mem_cons_self
      have hrest : ∀ q ∈ L, q ∈ S := fun q hq => hL q (List.mem_cons_of_mem a hq)
      show StronglyMeasurable (fun x => if x ∈ F a then ξ a else fold L x)
      exact StronglyMeasurable.ite (hFm a ha) stronglyMeasurable_const (ih hrest)
  have hfold_eq : ∀ L : List I, (∀ q ∈ L, q ∈ S) → ∀ p ∈ S, p ∈ L → ∀ x ∈ F p,
      fold L x = ξ p := by
    intro L
    induction L with
    | nil => intro _ p _ hpL; simp at hpL
    | cons a L ih =>
      intro hL p hp hpL x hx
      have ha : a ∈ S := hL a List.mem_cons_self
      have hrest : ∀ q ∈ L, q ∈ S := fun q hq => hL q (List.mem_cons_of_mem a hq)
      simp only [fold, List.foldr_cons]
      by_cases hxa : x ∈ F a
      · obtain rfl : a = p := huniq p hp a ha x hx hxa
        simp only [hxa, ↓reduceIte]
      · simp only [hxa, ↓reduceIte]
        have hpa : p ≠ a := fun h => hxa (h ▸ hx)
        have hpL' : p ∈ L := by
          rcases List.mem_cons.mp hpL with h | h
          · exact absurd h hpa
          · exact h
        exact ih hrest p hp hpL' x hx
  let ξf : Euclid P → MultiVector P k := fold S.toList
  have hξsm : StronglyMeasurable ξf := hfold_sm S.toList (fun q hq => Finset.mem_toList.mp hq)
  have hξeq : ∀ p ∈ S, ∀ x ∈ F p, ξf x = ξ p := fun p hp x hx =>
    hfold_eq S.toList (fun q hq => Finset.mem_toList.mp hq) p hp (Finset.mem_toList.mpr hp) x hx
  -- step 5: `C` is countably `k`-rectifiable, covered by the ranges of the Lipschitz `G_p`
  -- (listed along `S.toList`, padded with constant maps) up to `M₀ = ∅`
  have hrect : CountablyRectifiable k (⋃ q ∈ S, F q) := by
    refine ⟨∅, measure_empty, fun j => if h : j < S.toList.length then G (S.toList.get ⟨j, h⟩)
      else fun _ => 0, ?_, ?_⟩
    · intro j
      by_cases h : j < S.toList.length
      · simp only [h, ↓reduceDIte]
        exact hGlip _ (Finset.mem_toList.mp (List.get_mem _ _))
      · simp only [h, ↓reduceDIte]
        exact ⟨0, LipschitzWith.const 0⟩
    · intro x hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      right
      obtain ⟨y, hy⟩ := hFG p hp hxp
      obtain ⟨⟨j, hj⟩, hjp⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hp)
      refine Set.mem_iUnion.mpr ⟨j, y, ?_⟩
      simp only [hj, ↓reduceDIte, hjp, hy]
  -- step 6: `∫_C θ dHᵏ = Σ_p m_p Hᵏ(F_p) < ∞`, splitting over the disjoint pieces
  have hpd : Set.PairwiseDisjoint (↑S) F := fun p hp q hq hpq => hdisj p hp q hq hpq
  have hlint : ∫⁻ x in ⋃ q ∈ S, F q, (θ x : ℝ≥0∞) ∂μHE[k] =
      ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
    rw [lintegral_biUnion_finset hpd hFm]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [setLIntegral_congr_fun (hFm p hp) (g := fun _ => (m p : ℝ≥0∞))
      (fun x hx => by simp only [hθeq p hp x hx]), lintegral_const,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hsum_ne : ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr (fun p hp => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hFfin p hp))
  -- step 8: `ξ` orients an approximate tangent space at every point of `C`, hence a.e.
  have horients : ∀ᵐ x ∂(μHE[k].restrict (⋃ q ∈ S, F q)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξf x) Q := by
    refine ae_restrict_of_forall_mem hCm (fun x hx => ?_)
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨Q, hQ, hor⟩ := htan p hp x hxp
    exact ⟨Q, hQ, by rw [hξeq p hp x hxp]; exact hor⟩
  -- step 9: the triple `(C, θ, ξ)`; step 7 (local integrability) is `∫_{C ∩ K} θ ≤ ∫_C θ < ∞`
  let R : IMRep U k :=
    { carrier := ⋃ q ∈ S, F q
      mult := θ
      orient := ξf
      measurableSet_carrier := hCm
      carrier_subset := hCU
      rectifiable := hrect
      measurable_mult := hθm
      mult_pos := by
        intro x hx
        obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
        rw [hθeq p hp x hxp]; exact hmpos p hp
      locallyIntegrable_mult := by
        intro K _ _
        exact ne_top_of_le_ne_top (hlint ▸ hsum_ne) (lintegral_mono_set Set.inter_subset_left)
      aestronglyMeasurable_orient := hξsm.aestronglyMeasurable
      orients := horients }
  refine ⟨R, ?_, ?_⟩
  -- step 10: the action splits over the pieces, on which the integrand is the continuous,
  -- compactly supported `m_p ξ_p(ω)`, integrable for the finite measure `Hᵏ⌞F_p`
  · intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) k) := ω.2.1.1.continuous
    have hωs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.2.1.2
    show ∫ x in ⋃ q ∈ S, F q, (θ x : ℝ) * ξf x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] = _
    have hint : ∀ p ∈ S, IntegrableOn
        (fun x => (θ x : ℝ) * ξf x ((ω : DifferentialForm (Euclid P) k) x)) (F p) μHE[k] := by
      intro p hp
      have : IsFiniteMeasure (μHE[k].restrict (F p)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (hFfin p hp)⟩
      have hg : Integrable (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x))
          (μHE[k].restrict (F p)) := by
        refine Continuous.integrable_of_hasCompactSupport
          (continuous_const.mul ((ξ p).continuous.comp hωc)) ?_
        exact (hωs.comp_left (map_zero (ξ p))).mul_left
      refine IntegrableOn.congr_fun hg (fun x hx => ?_) (hFm p hp)
      simp only [hθeq p hp x hx, hξeq p hp x hx]
    rw [integral_biUnion_finset S hFm (fun p hp q hq hpq => hdisj p hp q hq hpq) hint]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (hFm p hp) (fun x hx => ?_)
    simp only [hθeq p hp x hx, hξeq p hp x hx]
  -- step 11: `μ_T(ℝᴾ) = ∫ θ d(Hᵏ⌞C) = Σ_p m_p Hᵏ(F_p)` by step 6
  · show ((μHE[k].restrict (⋃ q ∈ S, F q)).withDensity fun x => (θ x : ℝ≥0∞)) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hlint]

/-- **Integer polyhedral chains on unit lattice faces are integer multiplicity, with mass
`Σ |β_p|`** (Simon Ch. 6, proof of 5.1, after (38): "`P`, `R` are integer multiplicity … should
be evident", and the identity `M(P) = Σ_F |β_F|` used for (36); for faces of any dimension `k`).
Let `T(ω) = Σ_{p ∈ s} β_p ∫_{(0,1)ᵏ} ω(Φ_p y)(e_{ι(0)}, …, e_{ι(k−1)}) dy` with
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` for `p = (ι, b)`.  The open faces `F̆_p = Φ_p((0,1)ᵏ)` with
`β_p ≠ 0` are disjoint Borel isometric images of the unit cube, so `Hᵏ(F̆_p) = 1`; near each of
its points their union `C` is the plane `x + V_p`, `V_p = span{e_{ι(j)}}`, which is therefore the
approximate tangent space of `C` there, oriented by `sign(β_p) e_ι`.  So
`(C, Σ_p |β_p| 1_{F̆_p}, sign(β_p) e_ι)` is an integer multiplicity triple, whose action is `T` by
the change of variables along the isometries `Φ_p`.  Then `M(T) = μ_T(ℝᴾ) = Σ_p |β_p|` by (MR), and
`T = 0` unless some `|β_p| ≥ 1`. -/
theorem Submission.cmcdtfr_polyhedral_im : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P k : ℕ) (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → IsIntegerMultiplicity T ∧ T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) ∧ (T = 0 ∨ 1 ≤ T.mass) := by
  intro hMR P k s β T hmono hT
  -- notation: the face maps `Φ_p`, the frames `τ_p = (e_{ι(j)})ⱼ`, the planes `V_p = span τ_p`,
  -- the open unit cube `Q₁` and the faces with nonzero coefficient `S = {p ∈ s : β_p ≠ 0}`
  let Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let τ : (Fin k → Fin P) × (Fin P → ℤ) → Fin k → Euclid P := fun p j =>
    EuclideanSpace.single (p.1 j) (1 : ℝ)
  let V : (Fin k → Fin P) × (Fin P → ℤ) → Submodule ℝ (Euclid P) := fun p =>
    Submodule.span ℝ (range (τ p))
  let Q₁ : Set (Euclid k) := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}
  let S := s.filter fun p => β p ≠ 0
  have hS : ∀ p ∈ S, p ∈ s ∧ β p ≠ 0 := fun p hp => Finset.mem_filter.mp hp
  have hSmono : ∀ p ∈ S, StrictMono p.1 := fun p hp => hmono p (hS p hp).1
  have hT' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in Q₁, (ω : DifferentialForm (Euclid P) k) (Φ p y) (τ p) :=
    hT
  -- the terms with `β_p = 0` vanish, so sums over `s` are sums over `S`
  have hsum : ∀ f : (Fin k → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, β p = 0 → f p = 0) →
      ∑ p ∈ S, f p = ∑ p ∈ s, f p := fun f hf =>
    Finset.sum_filter_of_ne fun p hp hfp hβ => hfp (hf p hp hβ)
  -- step 1: by `face_geometry`, `vol(Q₁) = 1` and every face map `Φ_p` is an isometry
  obtain ⟨hvol, hFG⟩ := Submission.cmcdtfr_face_geometry P k
  have hiso : ∀ p ∈ s, Isometry (Φ p) := fun p hp =>
    Isometry.of_dist_eq (hFG p p (hmono p hp) (hmono p hp)).1
  have hQm : MeasurableSet Q₁ := by
    have hpre : Q₁ = WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
      ext y
      simp [Q₁, Set.mem_pi]
    rw [hpre]
    exact (PiLp.volume_preserving_ofLp (Fin k)).measurable
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
  -- step 2: the open face `F̆_p = Φ_p(Q₁)` is Borel with `Hᵏ(F̆_p) = 1`, and integrals over it are
  -- integrals over `Q₁` (`isometry_image_integral`)
  have hface : ∀ p ∈ s, MeasurableSet (Φ p '' Q₁) ∧ μHE[k] (Φ p '' Q₁) = 1 ∧
      ∀ h : Euclid P → ℝ, ∫ x in Φ p '' Q₁, h x ∂μHE[k] = ∫ y in Q₁, h (Φ p y) := fun p hp => by
    obtain ⟨hm, hμ, hint⟩ :=
      Submission.cmcdtfrpi_isometry_image_integral P k (Φ p) Q₁ (hiso p hp) hQm
    exact ⟨hm, hμ.trans hvol, hint⟩
  -- steps 1 and 4(ii): the open faces of `S` are disjoint, and near each `x ∈ F̆_p` their union
  -- `C` agrees with `x + V_p` (`face_union_local_plane`)
  obtain ⟨hdisj, hflat⟩ :=
    Submission.cmcdtfrpi_face_union_local_plane Submission.cmcdtfr_face_geometry P k S hSmono
  have hflat' : ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧
      ∀ z : Euclid P, dist z (Φ p t) < δ → (z ∈ ⋃ q ∈ S, Φ q '' Q₁ ↔ z - Φ p t ∈ V p) :=
    hflat
  -- step 4(i): the unit `k`-vectors `e_p`, `e_p(α) = α(τ_p)`, with `±e_p` orienting `V_p`
  -- (`coord_plane_orientation`; `e_p = 0` if `p.1` is not strictly increasing)
  have hex : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), ∃ e : MultiVector P k, StrictMono p.1 →
      (∀ α : Covector (Euclid P) k, e α = α (τ p)) ∧ IsUnitOrientationOf e (V p) ∧
        IsUnitOrientationOf (-e) (V p) := fun p => by
    by_cases hp : StrictMono p.1
    · obtain ⟨-, e, he⟩ := Submission.cmcdtfrpi_coord_plane_orientation P k p.1 hp
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose e he using hex
  -- the orientation `ξ_p = sign(β_p) e_p` of the face `F̆_p`
  let ξ : (Fin k → Fin P) × (Fin P → ℤ) → MultiVector P k := fun p =>
    if 0 < β p then e p else -e p
  -- step 3: the faces of `S` with multiplicities `|β_p|` and orientations `ξ_p` form an integer
  -- multiplicity triple `R` (`finite_piece_imrep`); step 4(iii): at `x = Φ_p(t)` the approximate
  -- tangent space of `C` is `V_p` (`local_plane_tangent`), of dimension `k`
  obtain ⟨R, hRact, hRmeas⟩ := Submission.cmcdtfrpi_finite_piece_imrep P k _ univ S
    (fun p => Φ p '' Q₁) (fun p => (β p).natAbs) ξ Φ (fun p hp => (hface p (hS p hp).1).1)
    (fun _ _ => subset_univ _)
    (fun p hp => by rw [(hface p (hS p hp).1).2.1]; exact ENNReal.one_ne_top) hdisj
    (fun p hp => Int.natAbs_pos.mpr (hS p hp).2)
    (fun p hp => ⟨1, (hiso p (hS p hp).1).lipschitzWith⟩) (fun _ _ => image_subset_range _ _)
    (fun p hp x hx => by
      obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨δ, hδ, hloc⟩ := hflat' p hp t ht
      refine ⟨V p, Submission.cmcdtfrpi_local_plane_tangent P k _ _ (V p) δ
        (Submission.cmcdtfrpi_coord_plane_orientation P k p.1 (hSmono p hp)).1 hδ hloc, ?_⟩
      by_cases hβ : 0 < β p
      · rw [show ξ p = e p from ite_eq_left hβ]
        exact (he p (hSmono p hp)).2.1
      · rw [show ξ p = -e p from ite_eq_right hβ]
        exact (he p (hSmono p hp)).2.2)
  have hRact' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, ((β p).natAbs : ℝ) *
        ∫ x in Φ p '' Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] := hRact
  have hRmeas' : R.measure univ = ∑ p ∈ S, ((β p).natAbs : ℝ≥0∞) * μHE[k] (Φ p '' Q₁) :=
    hRmeas
  -- step 5: `R` represents `T`: `|β_p| ∫_{F̆_p} ξ_p(ω) dHᵏ = β_p ∫_{Q₁} ω(Φ_p y)(τ_p) dy`
  have hrep : R.Represents T := by
    intro ω
    rw [hT' ω, hRact' ω, ← hsum]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hτ := (he p (hSmono p hp)).1
      rw [(hface p (hS p hp).1).2.2]
      rcases (hS p hp).2.lt_or_gt with hneg | hpos
      · -- `β_p < 0`: `ξ_p = -e_p` and `|β_p| = -β_p`
        rw [show ξ p = -e p from ite_eq_right (not_lt.mpr hneg.le)]
        simp only [neg_apply, hτ, integral_neg]
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (Int.cast_lt_zero.mpr hneg)]
        ring
      · -- `β_p > 0`: `ξ_p = e_p` and `|β_p| = β_p`
        rw [show ξ p = e p from ite_eq_left hpos]
        simp only [hτ]
        rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (Int.cast_pos.mpr hpos)]
    · intro p _ hβ
      simp [hβ]
  -- step 6: by (MR) on `U = W = ℝᴾ`, `M(T) = μ_T(ℝᴾ) = Σ_{p ∈ S} |β_p| Hᵏ(F̆_p) = Σ_{p ∈ s} |β_p|`
  have hmass : T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := by
    have hTR : T.mass = R.measure univ := hMR P k univ T R isOpen_univ hrep univ isOpen_univ
    rw [hTR, hRmeas', ← hsum (fun p => |(β p : ℝ)|) fun p _ hβ => by simp [hβ],
      ENNReal.ofReal_sum_of_nonneg fun p _ => abs_nonneg _]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [(hface p (hS p hp).1).2.1, mul_one, ← Int.cast_abs, ← Nat.cast_natAbs,
      ENNReal.ofReal_natCast]
  refine ⟨⟨R, hrep⟩, hmass, ?_⟩
  -- step 7: if `S = ∅`, every `β_p` vanishes and `T = 0`; otherwise `M(T) ≥ |β_p| ≥ 1`, `p ∈ S`
  rcases S.eq_empty_or_nonempty with hS0 | ⟨p, hp⟩
  · left
    ext ω
    rw [hT' ω, GeometricCurrentOn.zero_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [not_not.mp (Finset.filter_eq_empty_iff.mp hS0 hp)]
    simp
  · right
    rw [hmass, ENNReal.one_le_ofReal]
    calc (1 : ℝ) ≤ |(β p : ℝ)| := by exact_mod_cast Int.one_le_abs (hS p hp).2
      _ ≤ ∑ q ∈ s, |(β q : ℝ)| :=
        Finset.single_le_sum (f := fun q => |(β q : ℝ)|) (fun q _ => abs_nonneg _) (hS p hp).1
/-- **Fundamental theorem of calculus in one coordinate on the open unit cube.**  For `G ∈ C¹` on
`ℝ^{k+1}` and a coordinate `i`, `∂ᵢG = DG(·)eᵢ` is integrable on `Q^{k+1} = (0, 1)^{k+1}` and
`∫_{Q^{k+1}} ∂ᵢG = ∫_{Q^k} G(·, xᵢ = 1) − ∫_{Q^k} G(·, xᵢ = 0)`.  The measure-preserving `toLp`
carries the open boxes of `Fin d → ℝ` onto the cubes, `(t, z) ↦ insertNth i t z` splits off the
`i`-th coordinate, Fubini puts the `t`-integral inside, and along each line
`t ↦ insertNth i t z = insertNth i 0 z + t eᵢ` the fundamental theorem of calculus applies. -/
theorem Submission.cmcdtfrcb_cube_partial_ftc : ∀ (k : ℕ) (i : Fin (k + 1)) (G : Euclid (k + 1) → ℝ), ContDiff ℝ 1 G → IntegrableOn (fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1} ∧ ∫ y in {y : Euclid (k + 1) | ∀ j, 0 < y j ∧ y j < 1}, fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = (∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) (WithLp.ofLp y)))) - ∫ y in {y : Euclid k | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) (WithLp.ofLp y))) := by
  intro k i G hG
  have hGd : Differentiable ℝ G := hG.differentiable one_ne_zero
  have hg : Continuous fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) :=
    (hG.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- the open box of `Fin d → ℝ` lies in the compact box `Icc 0 1`
  have hBsub : ∀ d : ℕ, {x : Fin d → ℝ | ∀ j, 0 < x j ∧ x j < 1} ⊆ Icc 0 1 :=
    fun d x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
  -- `toLp` transports the open box of `Fin d → ℝ` onto the open cube of `Euclid d`
  have htr : ∀ (d : ℕ) (f : Euclid d → ℝ), ∫ y in {y : Euclid d | ∀ j, 0 < y j ∧ y j < 1}, f y
      = ∫ x in {x : Fin d → ℝ | ∀ j, 0 < x j ∧ x j < 1}, f (WithLp.toLp 2 x) := fun d f =>
    ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding f _).symm
  -- the faces `xᵢ = c` in the coordinates of `Fin k → ℝ`
  have hface : ∀ c : ℝ, IntegrableOn (fun z : Fin k → ℝ => G (WithLp.toLp 2 (Fin.insertNth i c z)))
      {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1} := fun c =>
    ((hG.continuous.comp ((PiLp.continuous_toLp 2 _).comp
      (Continuous.finInsertNth i continuous_const continuous_id))).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set (hBsub k)
  refine ⟨?_, ?_⟩
  · refine (hg.continuousOn.integrableOn_compact
      ((isCompact_Icc (a := (0 : Fin (k + 1) → ℝ)) (b := 1)).image
        (PiLp.continuous_toLp 2 _))).mono_set ?_
    intro y hy
    exact ⟨WithLp.ofLp y, ⟨fun j => (hy j).1.le, fun j => (hy j).2.le⟩, rfl⟩
  -- the line `t ↦ insertNth i t z` is affine with direction `eᵢ`
  have hline : ∀ (z : Fin k → ℝ) (t : ℝ), (WithLp.toLp 2 (Fin.insertNth i t z) : Euclid (k + 1))
      = WithLp.toLp 2 (Fin.insertNth i 0 z) + t • EuclideanSpace.single i (1 : ℝ) := by
    intro z t
    ext j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨l, rfl⟩
    · simp
    · simp [Fin.succAbove_ne]
  -- the fundamental theorem of calculus along each line
  have hftc : ∀ z : Fin k → ℝ, ∫ t in Ioo (0 : ℝ) 1,
      fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ))
        = G (WithLp.toLp 2 (Fin.insertNth i 1 z)) - G (WithLp.toLp 2 (Fin.insertNth i 0 z)) := by
    intro z
    have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => G (WithLp.toLp 2 (Fin.insertNth i t z)))
        (fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ))) t := by
      intro t
      have hγ : HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (Fin.insertNth i t z) : Euclid (k + 1)))
          (EuclideanSpace.single i (1 : ℝ)) t := by
        have h := ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add
          (WithLp.toLp 2 (Fin.insertNth i 0 z) : Euclid (k + 1))
        rw [one_smul] at h
        convert h using 1
        funext s
        exact hline z s
      exact (hGd _).hasFDerivAt.comp_hasDerivAt t hγ
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      ((hg.comp ((PiLp.continuous_toLp 2 _).comp
        (Continuous.finInsertNth i continuous_id continuous_const))).intervalIntegrable 0 1)
  -- splitting off the `i`-th coordinate
  have hmp : MeasurePreserving
      (fun p : ℝ × (Fin k → ℝ) => (Fin.insertNth i p.1 p.2 : Fin (k + 1) → ℝ)) volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm _
  have hemb : MeasurableEmbedding
      (fun p : ℝ × (Fin k → ℝ) => (Fin.insertNth i p.1 p.2 : Fin (k + 1) → ℝ)) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) i).symm.measurableEmbedding
  have hpre : (fun p : ℝ × (Fin k → ℝ) => (Fin.insertNth i p.1 p.2 : Fin (k + 1) → ℝ)) ⁻¹'
      {x | ∀ j, 0 < x j ∧ x j < 1} = Ioo (0 : ℝ) 1 ×ˢ {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1} := by
    ext ⟨t, z⟩
    simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_Ioo]
    rw [Fin.forall_iff_succAbove i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  have hint : Integrable
      (fun p : ℝ × (Fin k → ℝ) =>
        fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2)) (EuclideanSpace.single i (1 : ℝ)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod
        (volume.restrict {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1})) := by
    rw [Measure.prod_restrict]
    exact ((hg.comp ((PiLp.continuous_toLp 2 _).comp
      (Continuous.finInsertNth i continuous_fst continuous_snd))).continuousOn.integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)).mono_set (prod_mono Ioo_subset_Icc_self (hBsub k))
  rw [htr (k + 1), htr k, htr k]
  calc ∫ x in {x : Fin (k + 1) → ℝ | ∀ j, 0 < x j ∧ x j < 1},
        fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ))
      = ∫ p in Ioo (0 : ℝ) 1 ×ˢ {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1},
          fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2))
            (EuclideanSpace.single i (1 : ℝ)) := by
        rw [← hpre]
        exact (hmp.setIntegral_preimage_emb hemb
          (fun x => fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ))) _).symm
    _ = ∫ z in {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1}, ∫ t in Ioo (0 : ℝ) 1,
          fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ)) := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
        exact integral_prod_symm _ hint
    _ = ∫ z in {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1},
          (G (WithLp.toLp 2 (Fin.insertNth i 1 z)) - G (WithLp.toLp 2 (Fin.insertNth i 0 z))) :=
        integral_congr_ae (Eventually.of_forall hftc)
    _ = _ := integral_sub (hface 1) (hface 0)
/-- Along the affine coordinate cube `Φ y = a + Σⱼ yⱼ e_{ι j}`, the exterior derivative of a `C¹`
`m`-form `γ` on `E = (e_{ι j})ⱼ` is the divergence `Σᵢ ∂ᵢFᵢ` of the coefficient fields
`Fᵢ(y) = (-1)ⁱ γ(Φ y)(E ∘ succAbove i)`, and each `Fᵢ` is `C¹`.  `Φ = a + L` with `L` continuous
linear and `L eᵢ = e_{ι i}`; expand `dγ(Φ y)(E)` by `exteriorDerivative_apply`
(`removeNth i E = E ∘ succAbove i`) and apply the chain rule to `Fᵢ`. -/
theorem Submission.cmcdtfrcb_pullback_divergence : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (a : Euclid P) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ 1 γ → (∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))) ∧ ∀ y : Euclid (m + 1), exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), fderiv ℝ (fun z : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)) := by
  intro P m ι a γ hγ
  -- `Φ y = a + L y` with `L v = Σⱼ vⱼ e_{ι j}` continuous linear, and `L eᵢ = e_{ι i}`
  let L : Euclid (m + 1) →L[ℝ] Euclid P :=
    ∑ j, (EuclideanSpace.proj j).smulRight (EuclideanSpace.single (ι j) (1 : ℝ))
  have hL : ∀ v : Euclid (m + 1),
      a + L v = a + ∑ j, v j • EuclideanSpace.single (ι j) (1 : ℝ) := by
    intro v
    simp [L]
  have hΦ : ∀ y : Euclid (m + 1), HasFDerivAt
      (fun z : Euclid (m + 1) => a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) L y := by
    intro y
    simpa only [hL] using (L.hasFDerivAt (x := y)).const_add a
  have hΦc : ContDiff ℝ 1
      fun z : Euclid (m + 1) => a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ) := by
    simpa only [hL] using (contDiff_const (c := a)).add L.contDiff
  have hLe : ∀ i : Fin (m + 1),
      L (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single (ι i) (1 : ℝ) := by
    intro i
    simp [L]
  refine ⟨fun i => ?_, fun y => ?_⟩
  · -- `Fᵢ = (-1)ⁱ · ev_{E ∘ succAbove i} ∘ γ ∘ Φ`, evaluation being continuous linear
    exact contDiff_const.mul ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
      fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)).contDiff.comp
        (hγ.comp hΦc))
  · -- `dγ(Φ y)(E) = Σᵢ (-1)ⁱ D[γ(·)(removeNth i E)](Φ y)(e_{ι i})`; match the terms with the
    -- chain rule `DFᵢ(y) eᵢ = (-1)ⁱ D[γ(·)(E ∘ succAbove i)](Φ y)(L eᵢ)`
    rw [exteriorDerivative_apply ((hγ.differentiable one_ne_zero) _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    set x := a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)
    set u : Fin m → Euclid P := fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)
    have hg : HasFDerivAt (fun x' => γ x' u) (fderiv ℝ (fun x' => γ x' u) x) x :=
      (((hγ.differentiable one_ne_zero) x).continuousAlternatingMap_apply_const u).hasFDerivAt
    have hF : HasFDerivAt
        (fun z : Euclid (m + 1) =>
          (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) u)
        ((-1 : ℝ) ^ (i : ℕ) • (fderiv ℝ (fun x' => γ x' u) x).comp L) y :=
      (hg.comp y (hΦ y)).const_mul _
    -- `removeNth i E = E ∘ succAbove i = u` and `E i = e_{ι i}`
    show (-1 : ℤ) ^ (i : ℕ) •
      fderiv ℝ (fun x' => γ x' u) x (EuclideanSpace.single (ι i) (1 : ℝ)) = _
    rw [hF.fderiv]
    simp [hLe]

/-- **Stokes' formula for one oriented lattice unit cube** (the cubes of the lattice of Simon
Ch. 6, §5).  For `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` on the open unit cube `Q^{m+1}` (`b ∈ ℤᴾ`, `ι`
arbitrary) and a `C¹` `m`-form `γ`,
`∫_{Q^{m+1}} dγ(Φ y)(e_{ι(0)}, …, e_{ι(m)}) = Σᵢ (−1)ⁱ (∫_{Q^m} γ(Φ¹ᵢ)(E'ᵢ) − ∫_{Q^m} γ(Φ⁰ᵢ)(E'ᵢ))`,
where `Φᶜᵢ(y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}` and `E'ᵢ = (e_{ι(succAbove i l)})ₗ`.
By `cmcdtfrcb_pullback_divergence` the integrand is `Σᵢ ∂ᵢFᵢ` with the `C¹` functions
`Fᵢ(y) = (−1)ⁱ γ(Φ y)(E'ᵢ)`; `cmcdtfrcb_cube_partial_ftc` integrates each `∂ᵢFᵢ` to the
difference of the integrals of `Fᵢ` over the faces `yᵢ = 1` and `yᵢ = 0`, and
`Φ(insertNth i c y') = Φᶜᵢ(y')`. -/
theorem Submission.cmcdtfrcb_cube_stokes : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ 1 γ → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * ((∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) - ∫ y in {y : Euclid m | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) := by
  intro P m ι b γ hγ
  -- `dγ(Φ y)(E) = Σᵢ ∂ᵢFᵢ(y)`, with every `Fᵢ` of class `C¹`
  obtain ⟨hC1, hpt⟩ := Submission.cmcdtfrcb_pullback_divergence P m ι
    (WithLp.toLp 2 (fun k => (b k : ℝ))) γ hγ
  simp only [hpt]
  -- each `∂ᵢFᵢ` is integrable on the cube, so the finite sum leaves the integral
  rw [integral_finsetSum _ fun i _ => (Submission.cmcdtfrcb_cube_partial_ftc m i _ (hC1 i)).1]
  refine Finset.sum_congr rfl fun i _ => ?_
  -- `∫ ∂ᵢFᵢ` is the difference of the face integrals of `Fᵢ` at `yᵢ = 1` and `yᵢ = 0`
  rw [(Submission.cmcdtfrcb_cube_partial_ftc m i _ (hC1 i)).2]
  -- `Φ(insertNth i c y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}`
  have hface : ∀ (c : ℝ) (y : Euclid m),
      WithLp.toLp 2 (fun k => (b k : ℝ)) +
          ∑ j, (WithLp.toLp 2 (Fin.insertNth i c (WithLp.ofLp y)) : Euclid (m + 1)) j •
            EuclideanSpace.single (ι j) (1 : ℝ) =
        WithLp.toLp 2 (fun k => (b k : ℝ)) + c • EuclideanSpace.single (ι i) (1 : ℝ) +
          ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ) := by
    intro c y
    rw [Fin.sum_univ_succAbove _ i, add_assoc]
    simp
  -- the front face is based at `b + e_{ι(i)}`
  have hbase : WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) =
      WithLp.toLp 2 (fun k => (b k : ℝ)) + EuclideanSpace.single (ι i) (1 : ℝ) := by
    ext k
    by_cases hk : k = ι i
    · subst hk
      simp
    · simp [hk]
  simp only [hface, one_smul, zero_smul, add_zero, ← hbase]
  rw [integral_const_mul, integral_const_mul, mul_sub]
/-- Regrouping the faces of a lattice chain (boundary of an integer polyhedral chain
`∑_{F ∈ Lₙ} β_F [[F]]`, Simon Ch. 6, 5.1): index an oriented lattice `(m+1)`-cube by `p = (ι, b)`
with `ι` strictly increasing, and its `i`-th front and back faces by
`(ι ∘ succAbove i, b + 𝟙_{ι i})` and `(ι ∘ succAbove i, b)`.  Then the signed face sum
`∑_p β_p ∑_i (-1)ⁱ (I(front) - I(back))` is an integer combination `∑_{q ∈ s'} β'_q I(q)` of
lattice `m`-cube indices, uniformly in `I`: take for `s'` all the faces and
`β'_q = ∑_{p,i} β_p (-1)ⁱ ([front = q] - [back = q])`; the `q`-sum then picks out the two faces. -/
theorem Submission.cmcdtfrcb_face_regroup : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ q ∈ s', StrictMono q.1) ∧ ∀ I : (Fin m → Fin P) × (Fin P → ℤ) → ℝ, ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2)) = ∑ q ∈ s', (β' q : ℝ) * I q := by
  classical
  intro P m s β hs
  -- the front and back copies of the `i`-th face of `p`
  set fr : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → (Fin m → Fin P) × (Fin P → ℤ) :=
    fun p i => (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1)
  set bk : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Fin (m + 1) → (Fin m → Fin P) × (Fin P → ℤ) :=
    fun p i => (p.1 ∘ Fin.succAbove i, p.2)
  -- `s'` is the set of all faces
  set S : Finset ((Fin m → Fin P) × (Fin P → ℤ)) :=
    s.biUnion fun p => Finset.univ.biUnion fun i => {fr p i, bk p i} with hS
  have hfS : ∀ p ∈ s, ∀ i, fr p i ∈ S := fun p hp i =>
    Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩⟩
  have hbS : ∀ p ∈ s, ∀ i, bk p i ∈ S := fun p hp i =>
    Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩⟩
  refine ⟨S, fun q => ∑ p ∈ s, ∑ i : Fin (m + 1), β p * (-1) ^ (i : ℕ) *
      ((if fr p i = q then 1 else 0) - (if bk p i = q then 1 else 0)), ?_, ?_⟩
  · -- a face `ι ∘ succAbove i` of a strictly increasing `ι` is strictly increasing
    intro q hq
    simp only [hS, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hq
    obtain ⟨p, hp, i, rfl | rfl⟩ := hq
    · exact (hs p hp).comp (Fin.strictMono_succAbove i)
    · exact (hs p hp).comp (Fin.strictMono_succAbove i)
  · intro I
    -- the `q`-sum over `S` picks out the two faces
    have key : ∀ p ∈ s, ∀ i : Fin (m + 1),
        ∑ q ∈ S, (β p : ℝ) * (-1) ^ (i : ℕ) *
            ((if fr p i = q then 1 else 0) - (if bk p i = q then 1 else 0)) * I q =
          (β p : ℝ) * ((-1) ^ (i : ℕ) * (I (fr p i) - I (bk p i))) := by
      intro p hp i
      simp only [mul_sub, sub_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_sub_distrib, Finset.sum_ite_eq, hfS p hp i, hbS p hp i, ite_true]
      ring
    calc ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) *
            (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2))
        = ∑ p ∈ s, ∑ i : Fin (m + 1), ∑ q ∈ S, (β p : ℝ) * (-1) ^ (i : ℕ) *
            ((if fr p i = q then 1 else 0) - (if bk p i = q then 1 else 0)) * I q := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => (key p hp i).symm
      _ = ∑ q ∈ S, ∑ p ∈ s, ∑ i : Fin (m + 1), (β p : ℝ) * (-1) ^ (i : ℕ) *
            ((if fr p i = q then 1 else 0) - (if bk p i = q then 1 else 0)) * I q :=
          (Finset.sum_congr rfl fun p _ => Finset.sum_comm).trans Finset.sum_comm
      _ = ∑ q ∈ S, ((∑ p ∈ s, ∑ i : Fin (m + 1), β p * (-1) ^ (i : ℕ) *
            ((if fr p i = q then 1 else 0) - (if bk p i = q then 1 else 0)) : ℤ) : ℝ) * I q := by
          refine Finset.sum_congr rfl fun q _ => ?_
          push_cast
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_mul]

/-- **Boundary of a lattice chain** (Simon Ch. 6, 5.1, step 8 of the deformation theorem: the
boundary of an integer lattice chain is an integer lattice chain).  Index an oriented lattice
`(m+1)`-cube by `p = (ι, b)`, `Φ_p y = b + Σⱼ yⱼ e_{ι j}`, and let `T = Σ_{p ∈ s} β_p [[p]]`.  For a
test `m`-form `γ`, `∂T(γ) = T(dγ) = Σ_p β_p ∫_{(0,1)^{m+1}} dγ(Φ_p y)(e_ι) dy`; cubical Stokes
turns each integral into the signed face sum
`Σᵢ (-1)ⁱ ([[ι ∘ succAbove i, b + 𝟙_{ι i}]](γ) - [[ι ∘ succAbove i, b]](γ))`, and regrouping
these faces gives integers `β'_q` on strictly increasing indices `q ∈ s'`, chosen independently
of `γ`. -/
theorem Submission.cmcdtfr_chain_boundary : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s', StrictMono p.1) ∧ ∀ γ : TestFormOn (univ : Set (Euclid P)) m, T.boundary γ = ∑ p ∈ s', (β' p : ℝ) * ∫ y in {y : Euclid m | ∀ i, 0 < y i ∧ y i < 1}, (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s β T hs hT
  -- one regrouping `(s', β')` of the signed faces serves every face functional `I`
  obtain ⟨s', β', hs', hI⟩ := Submission.cmcdtfrcb_face_regroup P m s β hs
  refine ⟨s', β', hs', fun γ => ?_⟩
  -- test forms are smooth, in particular `C¹`
  have hγ : ContDiff ℝ 1 (γ : DifferentialForm (Euclid P) m) := γ.property.1.1.of_le (by simp)
  -- `∂T(γ) = T(dγ)`; expand `T`, and the right side as the regrouped face sum of `I q = [[q]](γ)`
  rw [GeometricCurrentOn.boundary_apply, hT, ← hI fun q =>
    ∫ y in {y : Euclid m | ∀ i, 0 < y i ∧ y i < 1}, (γ : DifferentialForm (Euclid P) m)
      (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ))
      (fun j => EuclideanSpace.single (q.1 j) (1 : ℝ))]
  -- cube by cube, `[[p]](dγ)` is the signed sum of the faces of `p` (cubical Stokes)
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  exact Submission.cmcdtfrcb_cube_stokes P m p.1 p.2 γ hγ
/-- **Simon 6.5.1** (finiteness of the lattice chains `P = Σ_F β_F [[F]]`): for compact
`K ⊆ ℝᴾ` and `Λ ∈ ℝ`, only finitely many currents `T = Σ_{p ∈ s} β_p [[F_p]]` exist whose unit
`k`-faces `F_p = b + {Σⱼ yⱼ e_{ι(j)} : y ∈ [0,1]ᵏ}` (`p = (ι, b)`, `ι` increasing, `b ∈ ℤᴾ`) all
meet `K` and whose integer coefficients satisfy `Σ_p |β_p| ≤ Λ`.  `K` is bounded, `‖x‖ ≤ R`, so a
face meeting it has `‖b‖ ≤ R + k`: the admissible `p` lie in the finite set `S` of pairs with
`b ∈ [-⌊R + k⌋, ⌊R + k⌋]ᴾ`.  Hence `T = Σ_{p ∈ S} c_p [[F_p]]`, `c_p = β_p` on `s` and `0` off it,
with `c : S → [-⌊Λ⌋, ⌊Λ⌋] ∩ ℤ`, a finite set; and `c` determines `T` (`GeometricCurrentOn.ext`). -/
theorem Submission.cmcdtfr_finite_family : ∀ (P k : ℕ) (K : Set (Euclid P)) (Λ : ℝ), IsCompact K → {T : GeometricCurrentOn (univ : Set (Euclid P)) k | ∃ (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ K) ∧ ∑ p ∈ s, |(β p : ℝ)| ≤ Λ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))}.Finite := by
  intro P k K Λ hK
  -- step 1: `K` is bounded
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  -- step 2: the lower corners of the faces meeting `K` lie in the box `[-⌊R + k⌋, ⌊R + k⌋]ᴾ`
  let S : Finset ((Fin k → Fin P) × (Fin P → ℤ)) :=
    Finset.univ ×ˢ Fintype.piFinset fun _ => Finset.Icc (-⌊R + k⌋) ⌊R + k⌋
  have hSK : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), (∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        ∈ K) → p ∈ S := by
    rintro ⟨ι, b⟩ ⟨y, hy, hyK⟩
    have hw : ‖∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)‖ ≤ k := by
      calc ‖∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)‖
          ≤ ∑ j, ‖y j • EuclideanSpace.single (ι j) (1 : ℝ)‖ := norm_sum_le _ _
        _ ≤ ∑ _j : Fin k, (1 : ℝ) := Finset.sum_le_sum fun j _ => by
            rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
              abs_of_nonneg (hy j).1]
            exact (hy j).2
        _ = k := by simp
    have hb : ‖(WithLp.toLp 2 (fun i => (b i : ℝ)) : Euclid P)‖ ≤ R + k :=
      calc ‖(WithLp.toLp 2 (fun i => (b i : ℝ)) : Euclid P)‖
          = ‖(WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))
              - ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)‖
              + ‖∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)‖ := norm_sub_le _ _
        _ ≤ R + k := add_le_add (hR _ hyK) hw
    simp only [S, Finset.mem_product, Finset.mem_univ, true_and, Fintype.mem_piFinset,
      Finset.mem_Icc]
    intro i
    have hi := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (b i : ℝ)) : Euclid P) i
    rw [PiLp.toLp_apply, Real.norm_eq_abs] at hi
    obtain ⟨hi₁, hi₂⟩ := abs_le.mp (hi.trans hb)
    have h₁ : -b i ≤ ⌊R + k⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by linarith, Int.le_floor.mpr hi₂⟩
  -- steps 3–5: each such current is `∑_{p ∈ S} c p [[p]]` with `c : S → [-⌊Λ⌋, ⌊Λ⌋]`, and is
  -- determined by `c`
  let I : (Fin k → Fin P) × (Fin P → ℤ) → TestFormOn (univ : Set (Euclid P)) k → ℝ := fun p ω =>
    ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k)
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
      (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
  have hC : (Set.pi Set.univ fun _ : S => Set.Icc (-⌊Λ⌋) ⌊Λ⌋).Finite :=
    Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine (hC.biUnion fun c _ => Set.Subsingleton.finite (s := {T : GeometricCurrentOn
    (univ : Set (Euclid P)) k | ∀ ω, T ω = ∑ p : S, (c p : ℝ) * I p ω}) ?_).subset ?_
  · intro T₁ h₁ T₂ h₂
    exact GeometricCurrentOn.ext fun ω => (h₁ ω).trans (h₂ ω).symm
  · rintro T ⟨s, β, -, hsK, hΛ, hT⟩
    have hsS : s ⊆ S := fun p hp => hSK p (hsK p hp)
    have hβ : ∀ p ∈ s, |(β p : ℝ)| ≤ Λ := fun p hp =>
      (Finset.single_le_sum (fun q _ => abs_nonneg (β q : ℝ)) hp).trans hΛ
    have hΛ0 : 0 ≤ Λ := (Finset.sum_nonneg fun q _ => abs_nonneg (β q : ℝ)).trans hΛ
    refine Set.mem_biUnion (x := fun p : S => if (p : (Fin k → Fin P) × (Fin P → ℤ)) ∈ s then β p
      else 0) ?_ ?_
    · intro p _
      simp only [Set.mem_Icc]
      split_ifs with hp
      · obtain ⟨h₁, h₂⟩ := abs_le.mp (hβ p hp)
        have h₃ : -β p ≤ ⌊Λ⌋ := Int.le_floor.mpr (by push_cast; linarith)
        exact ⟨by linarith, Int.le_floor.mpr h₂⟩
      · have h₀ : (0 : ℤ) ≤ ⌊Λ⌋ := Int.le_floor.mpr (by simpa using hΛ0)
        exact ⟨by linarith, h₀⟩
    · intro ω
      rw [hT ω, Finset.sum_coe_sort S (fun p => ((if p ∈ s then β p else 0 : ℤ) : ℝ) * I p ω),
        ← Finset.sum_subset hsS]
      · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left hp]
      · intro p _ hp
        rw [ite_eq_right hp, Int.cast_zero, zero_mul]
/-- **Simon, Ch. 6, proof of 5.1** ((29)–(30): subtracting `β [[F]]` does not change the boundary
in `F̊`).  If `g : ℝⁿ → ℝⁿ` is `C¹` with compact support in the open unit cube `Q₁ = (0, 1)ⁿ`, then
`∫_{Q₁} div g = 0`.  `Dg` vanishes off `tsupport g ⊆ Q₁`, so the integral over `Q₁` is the
integral over `ℝⁿ`; in the standard basis `div g = Σᵢ ∂ᵢ gᵢ`, and each `∫ ∂ᵢ gᵢ = 0` by
integration by parts against the constant `1` (the compactly supported `C¹` component `gᵢ` is
Lipschitz). -/
theorem Submission.cmcdt_cbm_integral_div_eq_zero : ∀ (m : ℕ) (g : Euclid (m + 1) → Euclid (m + 1)), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) = 0 := by
  intro m g hg hgc hgQ
  -- `Dg` vanishes off `tsupport g ⊆ Q₁`, so the integral over `Q₁` is the integral over `ℝⁿ`
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_]
  swap
  · have h0 : fderiv ℝ g y = 0 := by
      by_contra h
      exact hy (hgQ (support_fderiv_subset ℝ h))
    rw [h0, ContinuousLinearMap.toLinearMap_zero, map_zero]
  -- `div g = Σᵢ ∂ᵢ gᵢ` in the standard basis `eᵢ`
  let e := EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
      ∑ i, (fderiv ℝ g y (e i)) i := by
    intro y
    rw [LinearMap.trace_eq_sum_inner _ e]
    simp only [e, EuclideanSpace.basisFun_inner, ContinuousLinearMap.coe_coe]
  simp_rw [htr]
  have hdiff : Differentiable ℝ g := hg.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ => ?_
    -- the `i`-th component `gᵢ` is `C¹` with compact support, hence Lipschitz
    let u : Euclid (m + 1) → ℝ := fun y => g y i
    have hu : ContDiff ℝ 1 u := (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hg
    have huc : HasCompactSupport u := hgc.comp_left (g := fun v : Euclid (m + 1) => v i) (by simp)
    obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport huc hu one_ne_zero
    -- integration by parts against the constant `1`
    have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume)
      (LipschitzWith.const (1 : ℝ)) hC huc (-e i)
    have h1 : ∀ x, lineDeriv ℝ (fun _ : Euclid (m + 1) => (1 : ℝ)) x (-e i) = 0 := fun x =>
      ((hasFDerivAt_const (1 : ℝ) x).hasLineDerivAt (-e i)).lineDeriv
    have h2 : ∀ x, lineDeriv ℝ u x (-(-e i)) = fderiv ℝ g x (e i) i := by
      intro x
      rw [neg_neg]
      exact (((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x
        (hdiff x).hasFDerivAt).hasLineDerivAt (e i)).lineDeriv
    simp only [h1, h2, zero_mul, integral_zero, mul_one] at key
    exact key.symm
  · intro i _
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · fun_prop
    · exact (hgc.fderiv ℝ).comp_left
        (g := fun L : Euclid (m + 1) →L[ℝ] Euclid (m + 1) => L (e i) i) (by simp)
/-- The open unit cube `Q₁ = {y : 0 < yᵢ < 1 ∀ i}` of `ℝ^{m+1}` has Lebesgue measure `1`.  The
coordinate map `ofLp : ℝ^{m+1} → (Fin (m + 1) → ℝ)` is measure preserving and `Q₁` is the
preimage of the measurable box `∏ᵢ (0, 1)`, whose volume is `∏ᵢ (1 − 0) = 1`. -/
theorem Submission.cmcdt_cbm_bvp_unit_cube_volume : ∀ m : ℕ, volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro m
  have hset : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' Set.pi Set.univ (fun _ : Fin (m + 1) => Set.Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
    (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
  simp
/-- **Oscillation bound passes to `L¹` limits** (step 2 of the BV Poincaré inequality on cubes,
cf. Simon Ch. 2, 2.7).  Let `Q_δ = {z : δ < z_i < 1 − δ ∀ i}` with `δ ≥ 0`, `u` integrable on
`Q₁ = {y : 0 < y_i < 1 ∀ i}`, and `v_k` continuous with
`∫_{Q_δ}∫_{Q_δ} |v_k(x) − v_k(y)| dy dx ≤ K` and `ε_k = ∫_{Q_δ} |v_k − u| → 0`.  Then
`∫_{Q_δ}∫_{Q_δ} |u(x) − u(y)| dy dx ≤ K`.  `Q_δ ⊆ Q₁` lies in the compact box `[0, 1]^{m+1}`, so
`μ = vol⌞Q_δ` is finite and `u, v_k ∈ L¹(μ)`; `(x, y) ↦ |v_k(x) − v_k(y)|` is `μ ⊗ μ`-integrable
(Fubini).  Integrating `|u(x) − u(y)| ≤ |v_k(x) − v_k(y)| + |u(x) − v_k(x)| + |v_k(y) − u(y)|`
twice gives `D(u) ≤ K + 2 vol(Q_δ) ε_k`; let `k → ∞`. -/
theorem Submission.cmcdt_cbm_bvp_osc_le_of_l1_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (v : ℕ → Euclid (m + 1) → ℝ) (δ K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → 0 ≤ δ → (∀ k, Continuous (v k)) → (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - v k y| ≤ K) → Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K := by
  intro m u v δ K hu hδ hv hK hlim
  set S : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- `Q_δ ⊆ Q₁`, using `δ ≥ 0`
  have hSQ : S ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- `Q₁` lies in the compact closed box `toLp '' [0, 1]^{m+1}`
  have hKc : IsCompact ((WithLp.toLp 2) ''
      (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) : Set (Fin (m + 1) → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hSK : S ⊆ (WithLp.toLp 2) ''
      (Set.Icc (fun _ => (0 : ℝ)) (fun _ => 1) : Set (Fin (m + 1) → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hSQ hz j).1.le, fun j => (hSQ hz j).2.le⟩, rfl⟩
  -- hence `μ = vol⌞Q_δ` is a finite measure, and `u` and every `v k` are `μ`-integrable
  have hSfin : volume S < ∞ := (measure_mono hSK).trans_lt hKc.measure_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSfin.ne
  have huS : Integrable u (volume.restrict S) := hu.mono_set hSQ
  have hvS : ∀ k, Integrable (v k) (volume.restrict S) := fun k =>
    ((hv k).continuousOn.integrableOn_compact hKc).mono_set hSK
  -- `D(u) ≤ D(v k) + 2 vol(Q_δ) ε_k ≤ K + 2 vol(Q_δ) ε_k`
  have key : ∀ k, ∫ x in S, ∫ y in S, |u x - u y| ≤
      K + 2 * volume.real S * ∫ x in S, |v k x - u x| := by
    intro k
    have hw := hvS k
    have hwu : Integrable (fun x => |v k x - u x|) (volume.restrict S) := (hw.sub huS).abs
    have huw : Integrable (fun x => |u x - v k x|) (volume.restrict S) := (huS.sub hw).abs
    -- Fubini: `x ↦ ∫_{Q_δ} |v k x - v k y| dy` is integrable
    have hg : Integrable (fun x => ∫ y in S, |v k x - v k y|) (volume.restrict S) :=
      ((hw.comp_fst (volume.restrict S)).sub
        (hw.comp_snd (volume.restrict S))).abs.integral_prod_left
    -- inner integral, for fixed `x`
    have inner : ∀ x, ∫ y in S, |u x - u y| ≤
        (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
          ∫ y in S, |v k y - u y| := by
      intro x
      have h1 : Integrable (fun y => |v k x - v k y|) (volume.restrict S) :=
        ((integrable_const (v k x)).sub hw).abs
      have h2 : Integrable (fun y => |v k x - v k y| + |u x - v k x|) (volume.restrict S) :=
        h1.add (integrable_const |u x - v k x|)
      calc ∫ y in S, |u x - u y|
          ≤ ∫ y in S, (|v k x - v k y| + |u x - v k x| + |v k y - u y|) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
              (h2.add hwu) (Eventually.of_forall fun y => ?_)
            calc |u x - u y| = |(v k x - v k y) + (u x - v k x) + (v k y - u y)| := by ring_nf
              _ ≤ |v k x - v k y| + |u x - v k x| + |v k y - u y| := abs_add_three _ _ _
        _ = (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
              ∫ y in S, |v k y - u y| := by
            rw [integral_add h2 hwu, integral_add h1 (integrable_const _), setIntegral_const,
              smul_eq_mul]
    -- outer integral
    have hg2 : Integrable (fun x => (∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x|)
        (volume.restrict S) :=
      hg.add (huw.const_mul _)
    have hsymm : ∫ x in S, |u x - v k x| = ∫ x in S, |v k x - u x| := by
      congr 1
      funext x
      exact abs_sub_comm _ _
    calc ∫ x in S, ∫ y in S, |u x - u y|
        ≤ ∫ x in S, ((∫ y in S, |v k x - v k y|) + volume.real S * |u x - v k x| +
            ∫ y in S, |v k y - u y|) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun x => integral_nonneg fun y => abs_nonneg _)
            (hg2.add (integrable_const _)) (Eventually.of_forall inner)
      _ = (∫ x in S, ∫ y in S, |v k x - v k y|) + volume.real S * (∫ x in S, |u x - v k x|) +
            volume.real S * ∫ y in S, |v k y - u y| := by
          rw [integral_add hg2 (integrable_const _), integral_add hg (huw.const_mul _),
            integral_const_mul, setIntegral_const, smul_eq_mul]
      _ = (∫ x in S, ∫ y in S, |v k x - v k y|) +
            2 * volume.real S * ∫ x in S, |v k x - u x| := by
          rw [hsymm]
          ring
      _ ≤ K + 2 * volume.real S * ∫ x in S, |v k x - u x| := by
          linarith [hK k]
  -- let `k → ∞`
  have hlim' : Tendsto (fun k => K + 2 * volume.real S * ∫ x in S, |v k x - u x|) atTop
      (𝓝 (K + 2 * volume.real S * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
  rw [mul_zero, add_zero] at hlim'
  exact ge_of_tendsto' hlim' key

/-- **Exhausting `Q₁` by the inner cubes `Q_δ`** (the limit `δ ↓ 0` in the cube Poincaré
inequality, Simon Ch. 2, 2.7, where `U` is first replaced by an inner set
`W = {x ∈ U : dist(x, ∂U) > σ}`): if `u` is integrable on `Q₁ = (0, 1)ⁿ` and
`∫_{Q_δ}∫_{Q_δ} |u(x) − u(y)| dy dx ≤ K` for every inner cube `Q_δ = (δ, 1 − δ)ⁿ`, `0 < δ < 1/2`,
then `∫_{Q₁}∫_{Q₁} |u(x) − u(y)| dy dx ≤ K`.  As `vol(Q₁) = 1`, `|u(x) − u(y)|` is integrable on
`Q₁ × Q₁`; the products `Q_{δⱼ} × Q_{δⱼ}`, `δⱼ = 1/(j + 3)`, increase to `Q₁ × Q₁`, so by Fubini
and continuity of the integral along increasing unions the double integrals over `Q_{δⱼ}` tend
to the one over `Q₁`. -/
theorem Submission.cmcdt_cbm_bvp_osc_le_of_inner_cubes : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (K : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤ K) → ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| ≤ K := by
  intro m u K hu hK
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  let Q : ℝ → Set (Euclid (m + 1)) := fun δ => {z | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- step 1: every `Q δ` is measurable
  have hQm : ∀ δ : ℝ, MeasurableSet (Q δ) := by
    intro δ
    have hQ : Q δ = ⋂ i, ({z : Euclid (m + 1) | δ < z i} ∩ {z | z i < 1 - δ}) := by
      ext z; simp [Q]
    rw [hQ]
    refine MeasurableSet.iInter fun i => ?_
    have hc : Measurable fun z : Euclid (m + 1) => z i :=
      (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i).measurable
    exact (measurableSet_lt measurable_const hc).inter (measurableSet_lt hc measurable_const)
  -- step 2: `|u x - u y|` is integrable on `Q₁ × Q₁`, since `vol(Q₁) = 1`
  have hu' : Integrable u (volume.restrict Q₁) := hu
  have : IsFiniteMeasure (volume.restrict Q₁) := isFiniteMeasure_restrict.2 (by
    rw [hQ₁, Submission.cmcdt_cbm_bvp_unit_cube_volume m]; exact ENNReal.one_ne_top)
  let F : Euclid (m + 1) × Euclid (m + 1) → ℝ := fun p => |u p.1 - u p.2|
  have hFi : IntegrableOn F (Q₁ ×ˢ Q₁) ((volume : Measure (Euclid (m + 1))).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact ((hu'.comp_fst _).sub (hu'.comp_snd _)).abs
  -- step 3: the cubes `Q (δ j)`, `δ j = 1 / (j + 3)`, increase
  let δ : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 3)
  have hδpos : ∀ j, 0 < δ j := fun j => by positivity
  have hδlt : ∀ j, δ j < 1 / 2 := fun j =>
    one_div_lt_one_div_of_lt (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hδanti : Antitone δ := fun j k hjk =>
    one_div_le_one_div_of_le (by positivity) (by simpa using (Nat.cast_le.2 hjk : (j : ℝ) ≤ k))
  have hδlim : Tendsto δ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop)
  have hQmono : Monotone fun j => Q (δ j) := fun j k hjk z hz i =>
    ⟨(hδanti hjk).trans_lt (hz i).1, (hz i).2.trans_le (by linarith [hδanti hjk])⟩
  -- step 4: they exhaust `Q₁`
  have hU : ⋃ j, Q (δ j) = Q₁ := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun j z hz i =>
      ⟨(hδpos j).trans (hz i).1, (hz i).2.trans (by linarith [hδpos j])⟩) fun x hx => ?_
    have hev : ∀ᶠ j in atTop, ∀ i, δ j < x i ∧ x i < 1 - δ j := by
      refine Filter.eventually_all.2 fun i => ?_
      filter_upwards [hδlim.eventually_lt_const (hx i).1,
        hδlim.eventually_lt_const (sub_pos.2 (hx i).2)] with j h1 h2
      exact ⟨h1, by linarith⟩
    obtain ⟨j, hj⟩ := hev.exists
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  -- step 5: the products `Q (δ j) × Q (δ j)` increase to `Q₁ × Q₁`
  let s : ℕ → Set (Euclid (m + 1) × Euclid (m + 1)) := fun j => Q (δ j) ×ˢ Q (δ j)
  have hsm : ∀ j, MeasurableSet (s j) := fun j => (hQm _).prod (hQm _)
  have hsmono : Monotone s := fun j k hjk => Set.prod_mono (hQmono hjk) (hQmono hjk)
  have hsU : ⋃ j, s j = Q₁ ×ˢ Q₁ := by
    rw [Set.iUnion_prod_of_monotone hQmono hQmono, hU]
  -- steps 6-7: Fubini on each `s j` and continuity along the increasing union
  have hlim := tendsto_setIntegral_of_monotone
    (μ := (volume : Measure (Euclid (m + 1))).prod volume) (f := F) hsm hsmono (hsU ▸ hFi)
  rw [hsU, setIntegral_prod F hFi] at hlim
  have hD : ∀ j, ∫ p in s j, F p ∂(volume : Measure (Euclid (m + 1))).prod volume =
      ∫ x in Q (δ j), ∫ y in Q (δ j), |u x - u y| := fun j =>
    setIntegral_prod F (hFi.mono_set (hsU ▸ Set.subset_iUnion s j))
  -- step 8: pass to the limit in `D(δ j) ≤ K`
  exact le_of_tendsto' (hlim.congr hD) fun j => hK (δ j) (hδpos j) (hδlt j)
/-- **Mean deviation is bounded by the double-integral oscillation** (step 4 of the BV Poincaré
inequality on cubes, cf. Simon Ch. 2, 2.7).  If `vol(S) = 1` and `u` is integrable on `S`, then,
with `c = ∫_S u`, `∫_S |u − c| ≤ ∫_S ∫_S |u(x) − u(y)| dy dx`.  `μ = vol⌞S` is a probability
measure, so `u(x) − c = ∫_S (u(x) − u(y)) dy` and `|u(x) − c| ≤ ∫_S |u(x) − u(y)| dy`; the right
side is integrable in `x` (Fubini), and integrating over `S` gives the claim. -/
theorem Submission.cmcdt_cbm_bvp_mean_dev_le_osc : ∀ (m : ℕ) (S : Set (Euclid (m + 1))) (u : Euclid (m + 1) → ℝ), volume S = 1 → IntegrableOn u S → ∫ x in S, |u x - ∫ y in S, u y| ≤ ∫ x in S, ∫ y in S, |u x - u y| := by
  intro m S u hS hu
  -- `μ = vol⌞S` is a probability measure, since `μ univ = vol S = 1`
  have : IsProbabilityMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ, hS]⟩
  have hSr : volume.real S = 1 := by rw [measureReal_def, hS, ENNReal.toReal_one]
  have huS : Integrable u (volume.restrict S) := hu
  -- Fubini: `x ↦ ∫_S |u x - u y| dy` is integrable on `S`
  have hg : Integrable (fun x => ∫ y in S, |u x - u y|) (volume.restrict S) :=
    ((huS.comp_fst (volume.restrict S)).sub
      (huS.comp_snd (volume.restrict S))).abs.integral_prod_left
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) hg
    (Eventually.of_forall fun x => ?_)
  -- for fixed `x`, `u x - c = ∫_S (u x - u y) dy`, hence `|u x - c| ≤ ∫_S |u x - u y| dy`
  have hx : ∫ y in S, (u x - u y) = u x - ∫ y in S, u y := by
    rw [integral_sub (integrable_const _) huS, setIntegral_const, hSr, one_smul]
  calc |u x - ∫ y in S, u y| = |∫ y in S, (u x - u y)| := by rw [hx]
    _ ≤ ∫ y in S, |u x - u y| := abs_integral_le_integral_abs
/-- A continuous `f` on `ℝᵏ` is bounded and integrable on the open unit cube
`Q₁ = {0 < yᵢ < 1}`.  The closed cube `K = {0 ≤ yᵢ ≤ 1}`, the image of the compact box `Icc 0 1`
of `Fin k → ℝ` under `toLp`, is compact and contains `Q₁`; a continuous function is bounded on
`K` and integrable on `K` for the Haar measure `volume`, hence on `Q₁`. -/
theorem Submission.cmcdt_cbm_bvt_cube_cont_bound : ∀ (k : ℕ) (f : Euclid k → ℝ), Continuous f → (∃ M : ℝ, ∀ y ∈ {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, |f y| ≤ M) ∧ IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
  intro k f hf
  -- the closed cube `K = {0 ≤ yᵢ ≤ 1}` is the image of the compact box `Icc 0 1` of `Fin k → ℝ`
  have hK : IsCompact (WithLp.toLp 2 '' Icc (0 : Fin k → ℝ) 1 : Set (Euclid k)) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  have hQK : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ⊆ WithLp.toLp 2 '' Icc (0 : Fin k → ℝ) 1 :=
    fun y hy => ⟨WithLp.ofLp y, ⟨fun i => (hy i).1.le, fun i => (hy i).2.le⟩, WithLp.toLp_ofLp 2 y⟩
  -- `f` is bounded and integrable on the compact `K`, hence on `Q₁ ⊆ K`
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨⟨M, fun y hy => by simpa only [Real.norm_eq_abs] using hM y (hQK hy)⟩,
    (hf.continuousOn.integrableOn_compact hK).mono_set hQK⟩
/-- **L¹ limit of an affine bound** (step 2 of the BV trace estimate).  If
`|∫_S v_k h| ≤ A + B ∫_S |v_k|` for all `k`, `B ≥ 0`, `|h| ≤ M` on `S` and `v_k → w` in `L¹(S)`,
then `|∫_S w h| ≤ A + B ∫_S |w|`: with `ε_k = ∫_S |v_k − w|`,
`|∫_S w h − ∫_S v_k h| ≤ M ε_k` and `∫_S |v_k| ≤ ∫_S |w| + ε_k`, so
`|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k` for every `k`; let `k → ∞`. -/
theorem Submission.cmcdt_cbm_bvt_l1_limit : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (S : Set α) (v : ℕ → α → ℝ) (w h : α → ℝ) (A B M : ℝ), MeasurableSet S → 0 ≤ B → (∀ k, IntegrableOn (v k) S μ) → IntegrableOn w S μ → AEStronglyMeasurable h (μ.restrict S) → (∀ x ∈ S, |h x| ≤ M) → Tendsto (fun k => ∫ x in S, |v k x - w x| ∂μ) atTop (𝓝 0) → (∀ k, |∫ x in S, v k x * h x ∂μ| ≤ A + B * ∫ x in S, |v k x| ∂μ) → |∫ x in S, w x * h x ∂μ| ≤ A + B * ∫ x in S, |w x| ∂μ := by
  intro α _ μ S v w h A B M hS hB hv hw hh hM hlim hbd
  -- `|h| ≤ M` holds `μ⌞S`-a.e., so `w h` and `v_k h` are integrable on `S`
  have hMae : ∀ᵐ x ∂(μ.restrict S), ‖h x‖ ≤ M :=
    (ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]
      exact hM x hx)
  have hwh : IntegrableOn (fun x => w x * h x) S μ := Integrable.mul_bdd hw hh hMae
  have hvh : ∀ k, IntegrableOn (fun x => v k x * h x) S μ := fun k =>
    Integrable.mul_bdd (hv k) hh hMae
  -- for every `k`: `|∫_S w h| ≤ A + B ∫_S |w| + (B + M) ε_k`
  have hk : ∀ k, |∫ x in S, w x * h x ∂μ| ≤
      A + B * (∫ x in S, |w x| ∂μ) + (B + M) * ∫ x in S, |v k x - w x| ∂μ := by
    intro k
    -- `|∫_S w h − ∫_S v_k h| ≤ M ε_k`
    have hdiff : |(∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ| ≤
        M * ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_sub hwh (hvh k)]
      calc |∫ x in S, (w x * h x - v k x * h x) ∂μ|
          ≤ ∫ x in S, |w x * h x - v k x * h x| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ x in S, M * |v k x - w x| ∂μ := by
          refine integral_mono_ae (hwh.sub (hvh k)).abs (((hv k).sub hw).abs.const_mul M) ?_
          filter_upwards [hMae] with x hx
          rw [← sub_mul, abs_mul, abs_sub_comm, mul_comm]
          exact mul_le_mul_of_nonneg_right (by rwa [Real.norm_eq_abs] at hx) (abs_nonneg _)
        _ = M * ∫ x in S, |v k x - w x| ∂μ := integral_const_mul M _
    -- `∫_S |v_k| ≤ ∫_S |w| + ε_k`
    have hwi : IntegrableOn (fun x => |w x|) S μ := hw.abs
    have hvwi : IntegrableOn (fun x => |v k x - w x|) S μ := ((hv k).sub hw).abs
    have hvw : ∫ x in S, |v k x| ∂μ ≤ (∫ x in S, |w x| ∂μ) + ∫ x in S, |v k x - w x| ∂μ := by
      rw [← integral_add hwi hvwi]
      refine integral_mono (hv k).abs (hwi.add hvwi) fun x => ?_
      calc |v k x| = |w x + (v k x - w x)| := by rw [add_sub_cancel]
        _ ≤ |w x| + |v k x - w x| := abs_add_le _ _
    have htri : |∫ x in S, w x * h x ∂μ| ≤
        |∫ x in S, v k x * h x ∂μ| + |(∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ| := by
      have := abs_add_le (∫ x in S, v k x * h x ∂μ)
        ((∫ x in S, w x * h x ∂μ) - ∫ x in S, v k x * h x ∂μ)
      rwa [add_sub_cancel] at this
    linarith [hbd k, mul_le_mul_of_nonneg_left hvw hB]
  -- let `k → ∞`: `ε_k → 0`
  have hT : Tendsto (fun k => A + B * (∫ x in S, |w x| ∂μ) + (B + M) * ∫ x in S, |v k x - w x| ∂μ)
      atTop (𝓝 (A + B * (∫ x in S, |w x| ∂μ) + (B + M) * 0)) :=
    tendsto_const_nhds.add (hlim.const_mul (B + M))
  rw [mul_zero, add_zero] at hT
  exact ge_of_tendsto' hT hk
/-- Exhaustion of the open unit cube `Q₁ = {0 < yᵢ < 1}` by the shrunken cubes
`Q_δ = {δ < zᵢ < 1 - δ}`: if `f` is integrable on `Q₁`, then `∫_{Q_δ} f → ∫_{Q₁} f` as `δ → 0⁺`.
For `δ > 0`, `∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f`, and every `y ∈ Q₁` lies in `Q_δ` for all small
`δ > 0`; dominated convergence on `Q₁` with bound `|f|` concludes. -/
theorem Submission.cmcdt_cbm_bvt_cube_exhaust : ∀ (k : ℕ) (f : Euclid k → ℝ), IntegrableOn f {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} → Tendsto (fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y) (𝓝[>] 0) (𝓝 (∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, f y)) := by
  intro k f hf
  -- each `{z | ∀ i, a < z i ∧ z i < b}` is a finite intersection of open half-spaces
  have hmeas : ∀ a b : ℝ, MeasurableSet {z : Euclid k | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    have h : {z : Euclid k | ∀ i, a < z i ∧ z i < b} =
        ⋂ i, ({z : Euclid k | a < z i} ∩ {z : Euclid k | z i < b}) := by
      ext z
      simp
    rw [h]
    refine IsOpen.measurableSet (isOpen_iInter_of_finite fun i => ?_)
    exact (isOpen_lt continuous_const (PiLp.continuous_apply _ _ i)).inter
      (isOpen_lt (PiLp.continuous_apply _ _ i) continuous_const)
  -- for `δ > 0`, `∫_{Q_δ} f = ∫_{Q₁} 1_{Q_δ} f`
  have heq : (fun δ : ℝ => ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1},
      {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}.indicator f y) =ᶠ[𝓝[>] 0]
      fun δ : ℝ => ∫ y in {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ}, f y := by
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [setIntegral_indicator (hmeas _ _), inter_eq_right.2]
    intro z hz i
    exact ⟨hδ.trans (hz i).1, (hz i).2.trans (by linarith)⟩
  refine Tendsto.congr' heq ?_
  -- dominated convergence on `Q₁` with bound `|f|`
  refine tendsto_integral_filter_of_dominated_convergence (fun y => ‖f y‖)
    (Eventually.of_forall fun δ => hf.aestronglyMeasurable.indicator (hmeas _ _))
    (Eventually.of_forall fun δ => Eventually.of_forall fun y => norm_indicator_le_norm_self _ _)
    hf.norm ?_
  rw [ae_restrict_iff' (by simpa using hmeas 0 1)]
  refine Eventually.of_forall fun y hy => tendsto_const_nhds.congr' ?_
  -- every `y ∈ Q₁` lies in `Q_δ` for all small `δ > 0`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ i, δ < y i ∧ y i < 1 - δ := by
    rw [Filter.eventually_all]
    intro i
    have h1 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < y i := eventually_lt_nhds (hy i).1
    have h2 : ∀ᶠ δ in 𝓝 (0 : ℝ), δ < 1 - y i := eventually_lt_nhds (by linarith [(hy i).2])
    exact nhdsWithin_le_nhds ((h1.and h2).mono fun δ h => ⟨h.1, by linarith [h.2]⟩)
  filter_upwards [hev] with δ hδ
  exact (indicator_of_mem (show y ∈ {z : Euclid k | ∀ i, δ < z i ∧ z i < 1 - δ} from hδ) f).symm
/-- **Adjoint identity for mollification** (Simon Ch. 2, 2.5).  If `η : ℝᴾ → ℝ` is `C¹` with
compact support, `η̌(z) = η(−z)`, and `u`, `s` are integrable, then
`∫ D(η ⋆ u)(x)(s x) dx = −∫ u div(η̌ ⋆ s)`, where `div G = trace DG`.  Differentiating under the
integral, `D(η ⋆ u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz` and, since `Dη̌(y) = −Dη(−y)`,
`div(η̌ ⋆ s)(z) = −∫ Dη(x − z)(s x) dx`; Fubini applies to `Dη(x − z)(s x) u(z)`, which is
dominated by `C ‖s x‖ |u z|` with `C = sup ‖Dη‖`. -/
theorem Submission.cmcdt_cbm_sa_mollify_adjoint : ∀ (P : ℕ) (η u : Euclid P → ℝ) (s : Euclid P → Euclid P), ContDiff ℝ 1 η → HasCompactSupport η → Integrable u → Integrable s → ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) = -∫ z, u z * LinearMap.trace ℝ (Euclid P) (fderiv ℝ (convolution (fun z => η (-z)) s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z : Euclid P →ₗ[ℝ] Euclid P) := by
  intro P η u s hη hηc hu hs
  -- Step 1: `Dη` is continuous with compact support, hence bounded by some `C`.
  have hDc : Continuous (fderiv ℝ η) := hη.continuous_fderiv one_ne_zero
  have hDcs : HasCompactSupport (fderiv ℝ η) := hηc.fderiv ℝ
  obtain ⟨C, hC⟩ := hDc.bounded_above_of_compact_support hDcs
  -- Step 2: `η̌ = η ∘ (−id)` is `C¹` with compact support, and `Dη̌(y) = −Dη(−y)` (chain rule).
  set ηr : Euclid P → ℝ := fun z => η (-z)
  have hηr : ContDiff ℝ 1 ηr := hη.comp contDiff_neg
  have hηrc : HasCompactSupport ηr := hηc.comp_homeomorph (Homeomorph.neg (Euclid P))
  have hDrc : Continuous (fderiv ℝ ηr) := hηr.continuous_fderiv one_ne_zero
  have hDrcs : HasCompactSupport (fderiv ℝ ηr) := hηrc.fderiv ℝ
  have hDr : ∀ y, fderiv ℝ ηr y = -fderiv ℝ η (-y) := by
    intro y
    have h1 : HasFDerivAt ηr ((fderiv ℝ η (-y)).comp (-ContinuousLinearMap.id ℝ (Euclid P))) y :=
      ((hη.differentiable one_ne_zero) (-y)).hasFDerivAt.comp y (hasFDerivAt_id y).neg
    rw [h1.fderiv]
    ext v
    simp
  -- Step 3: `D(η ⋆ u)(x) = (Dη ⋆ u)(x)`, so `D(η ⋆ u)(x)(s x) = ∫ Dη(x − z)(s x) u(z) dz`.
  have hLHS : ∀ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x) =
      ∫ z, fderiv ℝ η (x - z) (s x) * u z := by
    intro x
    rw [(hηc.hasFDerivAt_convolution_left _ hη hu.locallyIntegrable x).fderiv, convolution_eq_swap,
      ContinuousLinearMap.integral_apply
        ((hDcs.convolutionExists_left _ hDc hu.locallyIntegrable x).integrable_swap)]
    simp
  -- Step 4: `div(η̌ ⋆ s)(z) = trace D(η̌ ⋆ s)(z) = ∫ Dη̌(z − x)(s x) dx`: the trace `T` is a
  -- continuous linear functional, and the trace of the rank-one map `v ↦ a(v) w` is `a(w)`.
  have hRHS : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (convolution ηr s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
        Euclid P →ₗ[ℝ] Euclid P) = ∫ x, fderiv ℝ ηr (z - x) (s x) := by
    let T : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      (LinearMap.trace ℝ (Euclid P) ∘ₗ ContinuousLinearMap.coeLM ℝ)
    have hTA : ∀ A : Euclid P →L[ℝ] Euclid P,
        T A = LinearMap.trace ℝ (Euclid P) (A : Euclid P →ₗ[ℝ] Euclid P) := fun A => rfl
    have hrk : ∀ (a : Euclid P →L[ℝ] ℝ) (w : Euclid P), T (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w) = a w := by
      intro a w
      have h : ((ContinuousLinearMap.precompL (Euclid P)
          (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P) a w :
            Euclid P →L[ℝ] Euclid P) : Euclid P →ₗ[ℝ] Euclid P) =
          (a : Euclid P →ₗ[ℝ] ℝ).smulRight w := by
        ext v
        simp
      rw [hTA, h, LinearMap.trace_smulRight]
      rfl
    intro z
    rw [(hηrc.hasFDerivAt_convolution_left _ hηr hs.locallyIntegrable z).fderiv,
      convolution_eq_swap]
    have hT := ContinuousLinearMap.integral_comp_comm T
      ((hDrcs.convolutionExists_left (ContinuousLinearMap.precompL (Euclid P)
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Euclid P →L[ℝ] Euclid P)) hDrc
          hs.locallyIntegrable z).integrable_swap)
    simp_rw [hrk] at hT
    exact hT.symm
  -- Step 5: Fubini for `H(x, z) = Dη(x − z)(s x) u(z)`, dominated by `C ‖s x‖ |u z|`.
  have hint : Integrable (uncurry fun x z => fderiv ℝ η (x - z) (s x) * u z)
      ((volume : Measure (Euclid P)).prod volume) := by
    refine Integrable.mono' ((hs.norm.mul_prod hu.norm).const_mul C) ?_ (Eventually.of_forall ?_)
    · exact ((ContinuousLinearMap.apply ℝ ℝ).aestronglyMeasurable_comp₂
        hs.aestronglyMeasurable.comp_fst
        (hDc.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hu.aestronglyMeasurable.comp_snd
    · rintro ⟨x, z⟩
      simp only [uncurry_apply_pair, norm_mul]
      calc ‖fderiv ℝ η (x - z) (s x)‖ * ‖u z‖ ≤ (C * ‖s x‖) * ‖u z‖ := by
            gcongr
            exact ((fderiv ℝ η (x - z)).le_opNorm (s x)).trans (by gcongr; exact hC _)
        _ = C * (‖s x‖ * ‖u z‖) := by ring
  -- Step 6: combine, using `Dη̌(z − x) = −Dη(x − z)` to identify the swapped integral.
  calc ∫ x, fderiv ℝ (convolution η u (ContinuousLinearMap.lsmul ℝ ℝ) volume) x (s x)
      = ∫ x, ∫ z, fderiv ℝ η (x - z) (s x) * u z := by simp_rw [hLHS]
    _ = ∫ z, ∫ x, fderiv ℝ η (x - z) (s x) * u z := integral_integral_swap hint
    _ = -∫ z, u z * LinearMap.trace ℝ (Euclid P)
          (fderiv ℝ (convolution ηr s (ContinuousLinearMap.lsmul ℝ ℝ) volume) z :
            Euclid P →ₗ[ℝ] Euclid P) := by
      rw [← integral_neg]
      congr 1
      funext z
      rw [hRHS z, ← integral_const_mul, ← integral_neg]
      congr 1
      funext x
      rw [hDr, neg_sub, neg_apply]
      ring
/-- Convolving with a probability density `k ≥ 0`, `∫ k = 1`, does not increase the `L¹` norm:
`∫⁻ ‖k ⋆ g‖ₑ ≤ ∫⁻ ‖g‖ₑ` (Young's inequality `‖k ⋆ g‖₁ ≤ ‖k‖₁ ‖g‖₁`).  As `∫ k = 1 ≠ 0`, `k` is
integrable and `∫⁻ ‖k‖ₑ = ofReal (∫ k) = 1`.  Pointwise `‖(k ⋆ g)(x)‖ₑ ≤ ∫⁻ ‖k t‖ₑ ‖g (x - t)‖ₑ dt`;
Tonelli and translation invariance of Lebesgue measure turn the right side, integrated in `x`,
into `(∫⁻ ‖k‖ₑ) (∫⁻ ‖g‖ₑ)`. -/
theorem Submission.cmcdt_cbm_sa_ml_l1_contraction : ∀ (n : ℕ) (k g : Euclid n → ℝ), (∀ z, 0 ≤ k z) → ∫ z, k z = 1 → AEStronglyMeasurable g volume → ∫⁻ x, ‖convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ≤ ∫⁻ x, ‖g x‖ₑ := by
  intro n k g hk0 hk1 hg
  -- `k` is integrable because `∫ k = 1 ≠ 0`, and it has unit mass `∫⁻ ‖k‖ₑ = 1`.
  have hk_int : Integrable k := integrable_of_integral_eq_one hk1
  have hk_mass : ∫⁻ t, ‖k t‖ₑ = 1 := by
    rw [lintegral_enorm_of_nonneg hk0,
      ← ofReal_integral_eq_lintegral_ofReal hk_int (ae_of_all _ hk0), hk1, ENNReal.ofReal_one]
  -- The convolution integrand is jointly a.e.-measurable, as Tonelli requires.
  have hmeas : AEMeasurable (uncurry fun (x t : Euclid n) => ‖k t‖ₑ * ‖g (x - t)‖ₑ)
      (volume.prod volume) := by
    refine (hk_int.aestronglyMeasurable.convolution_integrand
      (ContinuousLinearMap.lsmul ℝ ℝ) hg).enorm.congr (ae_of_all _ fun p => ?_)
    simp [uncurry]
  calc ∫⁻ x, ‖convolution k g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ
      ≤ ∫⁻ x, ∫⁻ t, ‖k t‖ₑ * ‖g (x - t)‖ₑ := by
        refine lintegral_mono fun x => ?_
        rw [convolution_def]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun t => ?_
        simp
    _ = ∫⁻ t, ∫⁻ x, ‖k t‖ₑ * ‖g (x - t)‖ₑ := lintegral_lintegral_swap hmeas
    _ = ∫⁻ t, ‖k t‖ₑ * ∫⁻ x, ‖g x‖ₑ := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top,
          lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t]
    _ = (∫⁻ t, ‖k t‖ₑ) * ∫⁻ x, ‖g x‖ₑ := lintegral_mul_const'' _ hk_int.aestronglyMeasurable.enorm
    _ = ∫⁻ x, ‖g x‖ₑ := by rw [hk_mass, one_mul]
/-- Uniform `L¹` approximate identity for a continuous compactly supported `h : ℝⁿ → ℝ`: for
`ε > 0` there is `r > 0` with `∫⁻ ‖ρ ⋆ h - h‖ₑ ≤ ε` for every `ρ ≥ 0` with `∫ ρ = 1` and
`spt ρ ⊆ B_r(0)`.  Take `tsupport h ⊆ B̄_R(0)`, `S = B̄_{R+1}(0)`, `η = ε / (Lⁿ(S) + 1)`, and by
uniform continuity `r ≤ 1` with `|h(y) - h(x)| < η` for `|y - x| < r`.  On `S`,
`dist_convolution_le` gives `|ρ ⋆ h - h| ≤ η`; off `S`, `h` and `ρ ⋆ h` vanish.  Integrating,
`∫⁻ ‖ρ ⋆ h - h‖ₑ ≤ η Lⁿ(S) ≤ ε`. -/
theorem Submission.cmcdt_cbm_sa_ml_compact_support_approx : ∀ (n : ℕ) (h : Euclid n → ℝ), Continuous h → HasCompactSupport h → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n h hc hcs ε hε
  -- `tsupport h ⊆ B̄_R(0)`; the error lives in the compact set `S = B̄_{R+1}(0)`
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : Euclid n)
  set S : Set (Euclid n) := closedBall (0 : Euclid n) (R + 1) with hS
  have hSm : MeasurableSet S := measurableSet_closedBall
  have hSfin : volume S ≠ ∞ := measure_closedBall_lt_top.ne
  set V : ℝ := (volume S).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- the pointwise tolerance `η = ε / (V + 1)`, and `r ≤ 1` from uniform continuity
  set η : ℝ := ε / (V + 1) with hη
  have hη0 : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hδh⟩ :=
    Metric.uniformContinuous_iff.1 (hcs.uniformContinuous_of_continuous hc) η hη0
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro ρ hρ0 hρ1 hρs
  have hzero : ∀ y : Euclid n, R < ‖y‖ → h y = 0 := by
    intro y hy
    by_contra hne
    have : y ∈ closedBall (0 : Euclid n) R := hR (subset_tsupport h hne)
    rw [mem_closedBall_zero_iff] at this
    linarith
  -- pointwise bound by `η` on `S`, and `0` off `S`
  have hpt : ∀ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ ≤
      S.indicator (fun _ => ENNReal.ofReal η) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_ofReal (dist_convolution_le hη0.le hρs hρ0 hρ1
        hc.aestronglyMeasurable fun y hy => (hδh ?_).le)
      exact lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _)
    · rw [indicator_of_notMem hx]
      rw [hS, mem_closedBall_zero_iff, not_le] at hx
      have hconv : convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x = 0 := by
        rw [convolution_def]
        refine integral_eq_zero_of_ae (ae_of_all _ fun t => ?_)
        by_cases ht : ρ t = 0
        · simp [ht]
        · have ht' : ‖t‖ < 1 :=
            lt_of_lt_of_le (mem_ball_zero_iff.1 (hρs ht)) (min_le_right _ _)
          have hxt : R < ‖x - t‖ := by
            have := norm_sub_norm_le x t
            linarith
          simp [hzero _ hxt]
      rw [hconv, hzero x (by linarith), sub_zero, enorm_zero]
  calc ∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ
      ≤ ∫⁻ x, S.indicator (fun _ => ENNReal.ofReal η) x := lintegral_mono hpt
    _ = ENNReal.ofReal η * volume S := lintegral_indicator_const hSm _
    _ = ENNReal.ofReal (η * V) := by
        rw [ENNReal.ofReal_mul hη0.le, hV, ENNReal.ofReal_toReal hSfin]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith

/-- **`L¹` approximate identity** (Simon 2.5: mollifications converge in `L¹`).  For integrable
`f` on `ℝⁿ` and `ε > 0` there is `r > 0` with `∫ |ρ ⋆ f − f| ≤ ε` for every continuous `ρ ≥ 0`
with `∫ ρ = 1` and `spt ρ ⊆ B_r(0)`.  `volume` is regular, so `f` is `L¹`-close to a continuous
compactly supported `h` (indicators of sets of finite measure are approximated by Urysohn
functions); `Submission.cmcdt_cbm_sa_ml_compact_support_approx` gives `r` for `h`, and in
`ρ ⋆ f − f = ρ ⋆ (f − h) + (ρ ⋆ h − h) − (f − h)` the first term is at most `∫ |f − h|` by
`Submission.cmcdt_cbm_sa_ml_l1_contraction`. -/
theorem Submission.cmcdt_cbm_sa_mollify_l1 : ∀ (n : ℕ) (f : Euclid n → ℝ), Integrable f → ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ ∀ ρ : Euclid n → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid n) r → ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤ ENNReal.ofReal ε := by
  intro n f hf ε hε
  have hε4 : 0 < ε / 4 := by positivity
  -- Density: `volume` is regular, so for measurable `s` of finite measure an Urysohn function
  -- `φ`, equal to `1` on a compact `F ⊆ s` and to `0` off an open `V ⊇ s`, has compact support
  -- and `|φ c − 1_s c| ≤ |1_{V \ F} c|` with `vol (V \ F)` small; hence some continuous `h` with
  -- compact support has `∫ |f − h| ≤ ε / 4`
  have hind : ∀ (c : ℝ) ⦃s : Set (Euclid n)⦄, MeasurableSet s → volume s < ∞ →
      ∀ {δ : ℝ≥0∞}, δ ≠ 0 → ∃ φ : Euclid n → ℝ,
        eLpNorm (φ - s.indicator fun _ => c) 1 volume ≤ δ ∧
          (Continuous φ ∧ HasCompactSupport φ) := by
    intro c s hs hsfin δ hδ
    obtain ⟨η, hη, hηδ⟩ := exists_eLpNorm_indicator_le (μ := (volume : Measure (Euclid n)))
      ENNReal.one_ne_top c hδ
    have hη2 : (η : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.coe_pos.2 hη).ne').ne'
    obtain ⟨F, hFs, hF, hsF⟩ := hs.exists_isCompact_sdiff_lt hsfin.ne hη2
    obtain ⟨V, hsV, hV, -, hVs⟩ := hs.exists_isOpen_sdiff_lt hsfin.ne hη2
    obtain ⟨φ, hφF, hφV, hφcs, hφ⟩ :=
      exists_continuous_one_zero_of_isCompact hF hV.isClosed_compl
        (disjoint_compl_right_iff_subset.2 (hFs.trans hsV))
    have hφc : Continuous fun x => φ x * c := φ.continuous.mul continuous_const
    refine ⟨fun x => φ x * c, (eLpNorm_mono (hφc.aestronglyMeasurable.sub
      (aestronglyMeasurable_const.indicator hs)) fun x => ?_).trans (hηδ (V \ F) ?_
      (hV.measurableSet.diff hF.measurableSet).nullMeasurableSet), hφc, hφcs.mul_right⟩
    · -- pointwise: `0` on `F` and off `V`, at most `|c|` on `V \ F`
      show ‖φ x * c - s.indicator (fun _ => c) x‖ ≤ ‖(V \ F).indicator (fun _ => c) x‖
      by_cases hxF : x ∈ F
      · rw [hφF hxF, indicator_of_mem (hFs hxF), Pi.one_apply, one_mul, sub_self, norm_zero]
        exact norm_nonneg _
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ F from ⟨hxV, hxF⟩)]
        by_cases hxs : x ∈ s
        · rw [indicator_of_mem hxs]
          calc ‖φ x * c - c‖ = |φ x - 1| * ‖c‖ := by
                rw [← sub_one_mul, norm_mul, Real.norm_eq_abs]
            _ ≤ 1 * ‖c‖ := by
                gcongr
                rw [abs_le]
                constructor <;> linarith [(hφ x).1, (hφ x).2]
            _ = ‖c‖ := one_mul _
        · rw [indicator_of_notMem hxs, sub_zero, norm_mul, Real.norm_eq_abs,
            abs_of_nonneg (hφ x).1]
          exact mul_le_of_le_one_left (norm_nonneg _) (hφ x).2
      · rw [hφV (mem_compl hxV), Pi.zero_apply, zero_mul,
          indicator_of_notMem fun h => hxV (hsV h), sub_zero, norm_zero]
        exact norm_nonneg _
    · -- `V \ F ⊆ (V \ s) ∪ (s \ F)`
      calc volume (V \ F) ≤ volume ((V \ s) ∪ (s \ F)) := measure_mono fun x hx => by
            by_cases hxs : x ∈ s
            exacts [Or.inr ⟨hxs, hx.2⟩, Or.inl ⟨hx.1, hxs⟩]
        _ ≤ volume (V \ s) + volume (s \ F) := measure_union_le _ _
        _ ≤ η / 2 + η / 2 := add_le_add hVs.le hsF.le
        _ = η := ENNReal.add_halves _
  obtain ⟨h, hfh, hhc, hhcs⟩ := (memLp_one_iff_integrable.2 hf).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun _ _ h₁ h₂ => ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩) (ENNReal.ofReal_pos.2 hε4).ne'
  have hh : Integrable h := hhc.integrable_of_hasCompactSupport hhcs
  have hfh' : Integrable (f - h) := hf.sub hh
  rw [eLpNorm_one_eq_lintegral_enorm hfh'.aestronglyMeasurable] at hfh
  -- The compactly supported case gives `r`, chosen before `ρ`
  obtain ⟨r, hr, hB⟩ :=
    Submission.cmcdt_cbm_sa_ml_compact_support_approx n h hhc hhcs (ε / 4) hε4
  refine ⟨r, hr, fun ρ hρc hρ0 hρ1 hρs => ?_⟩
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) r) fun x hx =>
      by_contra fun hne => hx (ball_subset_closedBall (hρs hne))
  -- `ρ ⋆ f = ρ ⋆ (f − h) + ρ ⋆ h`; both convolutions exist everywhere and are continuous
  have hex₁ := hρcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hfh'.locallyIntegrable
  have hex₂ := hρcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hh.locallyIntegrable
  have hc₁ := hρcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hfh'.locallyIntegrable
  have hc₂ := hρcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρc
    hh.locallyIntegrable
  -- The triangle inequality, then `ε / 4` for each of the three terms
  have hpt : ∀ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ ≤
      ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ + ‖(f - h) x‖ₑ := by
    intro x
    have hsplit := (hex₁ x).distrib_add (hex₂ x)
    rw [sub_add_cancel] at hsplit
    rw [hsplit, show ∀ a b : ℝ, a + b - f x = a + (b - h x) - (f - h) x from fun a b => by
      rw [Pi.sub_apply]; ring]
    exact enorm_sub_le.trans (add_le_add (enorm_add_le _ _) le_rfl)
  have hm₁ : AEMeasurable
      (fun x => ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) volume :=
    hc₁.enorm.measurable.aemeasurable
  have hm₂ : AEMeasurable
      (fun x => ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
        ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ) volume :=
    (hc₁.enorm.add (hc₂.sub hhc).enorm).measurable.aemeasurable
  calc ∫⁻ x, ‖convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x‖ₑ
      ≤ ∫⁻ x, (‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ +
          ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ + ‖(f - h) x‖ₑ) :=
        lintegral_mono hpt
    _ = (∫⁻ x, ‖convolution ρ (f - h) (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ) +
          (∫⁻ x, ‖convolution ρ h (ContinuousLinearMap.lsmul ℝ ℝ) volume x - h x‖ₑ) +
          ∫⁻ x, ‖(f - h) x‖ₑ := by
        rw [lintegral_add_left' hm₂, lintegral_add_left' hm₁]
    _ ≤ ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) := by
        gcongr
        · exact (Submission.cmcdt_cbm_sa_ml_l1_contraction n ρ (f - h) hρ0 hρ1
            hfh'.aestronglyMeasurable).trans hfh
        · exact hB ρ hρ0 hρ1 hρs
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε4.le hε4.le, ← ENNReal.ofReal_add (by positivity) hε4.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
/-- **Segment estimate for `C¹` functions.**  For `v ∈ C¹(ℝⁿ)` and `x, y ∈ ℝⁿ`,
`|v(x) − v(y)| ≤ ‖x − y‖ ∫₀¹ ‖Dv((1 − t)y + tx)‖ dt`.  Along `p(t) = (1 − t)y + tx` the chain rule
gives `(v ∘ p)'(t) = Dv(p(t))(x − y)`, which is continuous in `t`; the fundamental theorem of
calculus, `|∫ f| ≤ ∫ |f|` and the operator-norm bound `|Dv(p(t))(x − y)| ≤ ‖x − y‖ ‖Dv(p(t))‖`
finish the proof. -/
theorem Submission.cmcdt_cbm_sp_segment_bound : ∀ (n : ℕ) (v : Euclid n → ℝ) (x y : Euclid n), ContDiff ℝ 1 v → |v x - v y| ≤ ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ := by
  intro n v x y hv
  have hdiff : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  -- the segment `p(t) = (1 - t) • y + t • x`, with `p 0 = y`, `p 1 = x` and `p' = x - y`
  obtain ⟨p, hp⟩ : ∃ p : ℝ → Euclid n, p = fun t => (1 - t) • y + t • x := ⟨_, rfl⟩
  have hpc : Continuous p := by rw [hp]; fun_prop
  have hpd : ∀ t, HasDerivAt p (x - y) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (1 - t) • y) ((-1 : ℝ) • y) t :=
      ((hasDerivAt_id t).const_sub 1).smul_const y
    have h2 : HasDerivAt (fun t : ℝ => t • x) ((1 : ℝ) • x) t := (hasDerivAt_id t).smul_const x
    rw [hp]
    convert h1.add h2 using 1
    simp only [neg_smul, one_smul]
    abel
  -- chain rule: `(v ∘ p)'(t) = Dv(p(t))(x - y)`, a continuous function of `t`
  have hγ : ∀ t, HasDerivAt (fun t => v (p t)) (fderiv ℝ v (p t) (x - y)) t := fun t =>
    (hdiff (p t)).hasFDerivAt.comp_hasDerivAt t (hpd t)
  have hγc : Continuous fun t => fderiv ℝ v (p t) (x - y) :=
    (hcont.comp hpc).clm_apply continuous_const
  -- fundamental theorem of calculus
  have hftc : ∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y) = v x - v y := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ t)
      (hγc.intervalIntegrable 0 1)]
    simp [hp]
  have hpt : ∀ t, (1 - t) • y + t • x = p t := fun t => by rw [hp]
  simp only [hpt]
  rw [← hftc, ← Real.norm_eq_abs]
  calc ‖∫ t in (0 : ℝ)..1, fderiv ℝ v (p t) (x - y)‖
      ≤ ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t) (x - y)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, ‖x - y‖ * ‖fderiv ℝ v (p t)‖ := by
        apply intervalIntegral.integral_mono_on zero_le_one
        · exact hγc.norm.intervalIntegrable 0 1
        · exact (continuous_const.mul (hcont.comp hpc).norm).intervalIntegrable 0 1
        · intro t _
          rw [mul_comm]
          exact (fderiv ℝ v (p t)).le_opNorm (x - y)
    _ = ‖x - y‖ * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v (p t)‖ :=
        intervalIntegral.integral_const_mul _ _
/-- **Slice bound on a convex set.**  For convex measurable `Q ⊆ ℝⁿ`, measurable `g ≥ 0` and
`t ∈ [0, 1]`, `∫_Q ∫_Q g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(Q) ∫_Q g`.  If `s ≥ 1/2` and `c + sQ ⊆ Q`,
the Haar scaling `v ↦ sv` and translation invariance give
`∫_Q g(c + sv) dv ≤ ∫ (1_Q g)(c + sv) dv = s⁻ⁿ ∫_Q g ≤ 2ⁿ ∫_Q g`.  By convexity of `Q`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `Q` gives the claim. -/
theorem Submission.cmcdt_cbm_sp_convex_slice_bound : ∀ (n : ℕ) (Q : Set (Euclid n)) (g : Euclid n → ℝ≥0∞), Convex ℝ Q → MeasurableSet Q → Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
  intro n Q g hQc hQm hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • Q ⊆ Q`, then `∫_Q g(c + s v) dv ≤ 2ⁿ ∫_Q g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ Q, c + s • v ∈ Q) →
      ∫⁻ v in Q, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in Q, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = Q.indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator hQm
    -- change of variables `v ↦ s • v` (Haar scaling) followed by translation invariance
    have hcv : ∫⁻ v, F (c + s • v) = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z, F z := by
      have h1 : ∫⁻ w, F (c + w) ∂(Measure.map (fun v : Euclid n => s • v) volume)
          = ∫⁻ v, F (c + s • v) :=
        lintegral_map (hF.comp (measurable_const_add c)) (measurable_const_smul s)
      rw [← h1, Measure.map_addHaar_smul volume hs0.ne', lintegral_smul_measure,
        lintegral_add_left_eq_self F c, finrank_euclideanSpace_fin, smul_eq_mul]
    have hs2 : s⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hs0 two_pos]
      linarith
    calc ∫⁻ v in Q, g (c + s • v)
        = ∫⁻ v in Q, F (c + s • v) := by
          refine setLIntegral_congr_fun hQm fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in Q, g z := by
          rw [hcv, hFdef, lintegral_indicator hQm]
      _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
          gcongr
          calc ENNReal.ofReal |(s ^ n)⁻¹| = ENNReal.ofReal s⁻¹ ^ n := by
                rw [abs_of_pos (by positivity), ← inv_pow, ENNReal.ofReal_pow (by positivity)]
            _ ≤ ENNReal.ofReal 2 ^ n := by gcongr
            _ = 2 ^ n := by rw [ENNReal.ofReal_ofNat]
  -- the integrand is jointly measurable
  have hmeas : Measurable (fun p : Euclid n × Euclid n => g ((1 - t) • p.2 + t • p.1)) :=
    hg.comp (by fun_prop)
  rcases le_total (1 / 2 : ℝ) t with h | h
  · -- `t ≥ 1/2`: Tonelli, then change variables in `x` with `c = (1 - t) • y`, `s = t`
    rw [lintegral_lintegral_swap (f := fun x y => g ((1 - t) • y + t • x)) hmeas.aemeasurable]
    calc ∫⁻ y in Q, ∫⁻ x in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact hQc hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in Q, 2 ^ n * ∫⁻ z in Q, g z := by
          refine setLIntegral_mono' hQm fun x hx => ?_
          calc ∫⁻ y in Q, g ((1 - t) • y + t • x)
              = ∫⁻ y in Q, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in Q, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact hQc hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality for `C¹` functions on a convex set.**  If `Q ⊆ ℝⁿ` is convex and
measurable, `‖x - y‖ ≤ d` on `Q` and `v` is `C¹`, then
`∫_Q ∫_Q |v(x) - v(y)| ≤ 2ⁿ d Lⁿ(Q) ∫_Q ‖Dv‖`.  For `x, y ∈ Q`,
`cmcdt_cbm_sp_segment_bound` and `‖x - y‖ ≤ d` give
`|v(x) - v(y)| ≤ d ∫₀¹ ‖Dv((1 - t)y + tx)‖ dt`.  Integrate over `Q × Q` and move the
`t`-integral outside (Tonelli); then `cmcdt_cbm_sp_convex_slice_bound` bounds each slice by
`2ⁿ Lⁿ(Q) ∫_Q ‖Dv‖`.  As `Q` is bounded and `‖Dv‖` is continuous, the bound is finite, so it
passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.cmcdt_cbm_sp_convex_poincare : ∀ (n : ℕ) (Q : Set (Euclid n)) (v : Euclid n → ℝ) (d : ℝ), Convex ℝ Q → MeasurableSet Q → 0 ≤ d → (∀ x ∈ Q, ∀ y ∈ Q, ‖x - y‖ ≤ d) → ContDiff ℝ 1 v → ∫ x in Q, ∫ y in Q, |v x - v y| ≤ 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
  intro n Q v d hQc hQm hd hdiam hv
  have hseg := Submission.cmcdt_cbm_sp_segment_bound n v
  have hslice := Submission.cmcdt_cbm_sp_convex_slice_bound n Q
  have hcont : Continuous v := hv.continuous
  -- Step 1: `Q` is bounded, so `Lⁿ(Q) < ∞`, and `∫_Q g < ∞` for `g = ofReal ‖Dv‖`
  have hFc : Continuous fun z => ‖fderiv ℝ v z‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hQb : Bornology.IsBounded Q :=
    Metric.isBounded_iff.2 ⟨d, fun x hx y hy => by rw [dist_eq_norm]; exact hdiam x hx y hy⟩
  have hQfin : volume Q < ∞ := hQb.measure_lt_top
  obtain ⟨C, hC⟩ : ∃ C, ∀ z ∈ closure Q, ‖‖fderiv ℝ v z‖‖ ≤ C :=
    hQb.isCompact_closure.exists_bound_of_continuousOn hFc.continuousOn
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal ‖fderiv ℝ v z‖ :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal ‖fderiv ℝ v z‖ := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hFc.measurable.ennreal_ofReal
  have hJ : ∫⁻ z in Q, g z ≠ ∞ := by
    have h1 : ∫⁻ z in Q, g z ≤ ∫⁻ _ in Q, ENNReal.ofReal C :=
      setLIntegral_mono' hQm fun z hz => by
        rw [hgx]
        exact ENNReal.ofReal_le_ofReal (by simpa using hC z (subset_closure hz))
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQfin)).ne
  -- Step 2: for `x, y ∈ Q`, `|v x - v y| ≤ d ∫_(0,1] ‖Dv((1 - t) y + t x)‖ dt`
  have hpt : ∀ x ∈ Q, ∀ y ∈ Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    intro x hx y hy
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ v ((1 - t) • y + t • x)‖ with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => norm_nonneg _
    have h1 : |v x - v y| ≤ d * G :=
      (hseg x y hv).trans (mul_le_mul_of_nonneg_right (hdiam x hx y hy) hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ v ((1 - t) • y + t • x)‖)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hFc.comp h).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => norm_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal |v x - v y| ≤ ENNReal.ofReal (d * G) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal d * ENNReal.ofReal G := ENNReal.ofReal_mul hd
      _ ≤ _ := by gcongr
  -- Step 3: Tonelli moves the `t`-integral outside
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in Q, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in Q, ∫⁻ y in Q, ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q, g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in Q, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in Q, g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  -- Step 4: integrate step 2 over `Q × Q` and bound each slice by `convex_slice_bound`
  have hI : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y| ≤
      ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |v x - v y|
        ≤ ∫⁻ x in Q, ∫⁻ y in Q,
            ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => hpt x hx y hy
      _ = ENNReal.ofReal d * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in Q, ∫⁻ y in Q,
            g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rw [hswap]
      _ ≤ ENNReal.ofReal d * ∫⁻ _ in Ioc (0 : ℝ) 1, 2 ^ n * volume Q * ∫⁻ z in Q, g z := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hQc hQm hg t (Ioc_subset_Icc_self ht)) _
      _ = ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
  -- Step 5: the bound is finite, so it passes to Bochner integrals
  have hK : Measurable fun x : Euclid n => ∫⁻ y in Q, ENNReal.ofReal |v x - v y| := by
    have h : Continuous fun p : Euclid n × Euclid n => |v p.1 - v p.2| := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal |v p.1 - v p.2|)
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in Q, |v x - v y| =
      (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => abs_nonneg _)
      (by fun_prop : Continuous fun y => |v x - v y|).aestronglyMeasurable
  have hrhs : ∫ z in Q, ‖fderiv ℝ v z‖ = (∫⁻ z in Q, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => norm_nonneg _)
      hFc.aestronglyMeasurable]
    simp only [hgx]
  have hfin : ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hQfin.ne) hJ)
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      = ∫ x in Q, (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal := by simp only [hinner]
    _ = (∫⁻ x in Q, ENNReal.ofReal (∫⁻ y in Q, ENNReal.ofReal |v x - v y|).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal d * (2 ^ n * volume Q * ∫⁻ z in Q, g z)).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ n * d * (volume Q).toReal * ∫ z in Q, ‖fderiv ℝ v z‖ := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hd]
        ring
/-- **Geometry of the open cube** `Q_δ = {z : δ < zᵢ < 1 − δ for all i} ⊂ ℝⁿ`, `δ ≥ 0`.  `Q_δ` is
convex (coordinatewise convex combinations), measurable (a finite intersection of sets cut out by
the continuous coordinates), has diameter at most `√n` (`|xᵢ − yᵢ| < 1 − 2δ ≤ 1`), and
`Lⁿ(Q_δ) ≤ 1`, since `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))` and `ofLp` is measure preserving. -/
theorem Submission.cmcdt_cbm_sp_cube_geometry : ∀ (n : ℕ) (δ : ℝ), 0 ≤ δ → Convex ℝ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ MeasurableSet {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ∧ (∀ x ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ∀ y ∈ {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖x - y‖ ≤ Real.sqrt n) ∧ volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ≤ 1 := by
  intro n δ hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- convexity: `a xᵢ + b yᵢ − δ = a (xᵢ − δ) + b (yᵢ − δ) > 0`, and likewise below `1 − δ`
    refine convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab i => ?_
    have hxi := hx i
    have hyi := hy i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hb' : b = 1 - a := by linarith
    subst hb'
    constructor
    · nlinarith [mul_pos ha (sub_pos.2 hxi.1), mul_pos hb (sub_pos.2 hyi.1)]
    · nlinarith [mul_pos ha (sub_pos.2 hxi.2), mul_pos hb (sub_pos.2 hyi.2)]
  · -- measurability: `Q_δ = ⋂ᵢ {δ < zᵢ} ∩ {zᵢ < 1 − δ}` with continuous coordinates
    have hc : ∀ i : Fin n, Continuous fun z : Euclid n => z i := fun i => by fun_prop
    have : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} =
        ⋂ i, ({z : Euclid n | δ < z i} ∩ {z : Euclid n | z i < 1 - δ}) := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hc i).measurable).inter
        (measurableSet_lt (hc i).measurable measurable_const)
  · -- diameter: `(xᵢ − yᵢ)² ≤ 1` for each `i`, so `‖x − y‖ ≤ √(∑ᵢ 1) = √n`
    intro x hx y hy
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖(x - y) i‖ ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have hxi := hx i
          have hyi := hy i
          simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = n := by simp
  · -- volume: `Q_δ ⊆ ofLp⁻¹(∏ᵢ (0, 1))`, and `ofLp` is measure preserving
    have hsub : {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
        WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) := by
      intro z hz
      simp only [mem_preimage, mem_univ_pi, mem_Ioo]
      intro i
      exact ⟨by linarith [(hz i).1], by linarith [(hz i).2]⟩
    calc volume {z : Euclid n | ∀ i, δ < z i ∧ z i < 1 - δ}
        ≤ volume (WithLp.ofLp ⁻¹' (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) : Set (Euclid n)) :=
          measure_mono hsub
      _ = volume (Set.univ.pi fun _ : Fin n => Ioo (0 : ℝ) 1) :=
          (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage
            (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet
      _ = 1 := by rw [Real.volume_pi_Ioo]; simp

/-- **Poincaré inequality for `C¹` functions on the cube** `Q_δ = {z : δ < zᵢ < 1 − δ for all i}`
`⊂ ℝⁿ`, `n = m + 1`, `δ ≥ 0`: `∫_{Q_δ} ∫_{Q_δ} |v(x) − v(y)| dy dx ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`.  `Q_δ` is
convex and measurable, with diameter at most `√n` and `Lⁿ(Q_δ) ≤ 1`; the convex Poincaré
inequality with `d = √n` bounds the left side by `2ⁿ √n Lⁿ(Q_δ) ∫_{Q_δ} ‖Dv‖ ≤ 2ⁿ √n ∫_{Q_δ} ‖Dv‖`.
-/
theorem Submission.cmcdt_cbm_smooth_poincare : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (δ : ℝ), ContDiff ℝ 1 v → 0 ≤ δ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x - v y| ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v δ hv hδ
  obtain ⟨hconv, hmeas, hdiam, hvol⟩ := Submission.cmcdt_cbm_sp_cube_geometry (m + 1) δ hδ
  set Q := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  have hvol' : (volume Q).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])
  calc ∫ x in Q, ∫ y in Q, |v x - v y|
      ≤ 2 ^ (m + 1) * Real.sqrt ↑(m + 1) * (volume Q).toReal * ∫ x in Q, ‖fderiv ℝ v x‖ :=
        -- the convex Poincaré inequality with `d = √n`
        Submission.cmcdt_cbm_sp_convex_poincare (m + 1) Q v (Real.sqrt ↑(m + 1)) hconv hmeas
          (Real.sqrt_nonneg _) hdiam hv
    _ ≤ 2 ^ (m + 1) * Real.sqrt ↑(m + 1) * 1 * ∫ x in Q, ‖fderiv ℝ v x‖ := by gcongr
    _ = 2 ^ (m + 1) * Real.sqrt (m + 1) * ∫ x in Q, ‖fderiv ℝ v x‖ := by
        rw [mul_one, Nat.cast_add_one]
/-- The open unit cube `Q₁ = {y : 0 < yᵢ < 1 for all i}` of `ℝᵏ` has Lebesgue measure `1`: it is
the preimage of the box `∏ᵢ (0, 1)` under the measure-preserving coordinate map
`ofLp : ℝᵏ → (Fin k → ℝ)`, and `vol ∏ᵢ (0, 1) = ∏ᵢ (1 − 0) = 1` (the empty product if `k = 0`). -/
theorem Submission.cmcdt_cbm_im_cube_volume : ∀ k : ℕ, volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
  intro k
  -- `Q₁` is the preimage under `ofLp` of the measurable box `B = ∏ᵢ (0, 1)`
  have hB : MeasurableSet (univ.pi fun _ : Fin k => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQ : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
      WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin k => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Set.mem_pi]
  -- `ofLp` preserves volume, and `vol B = ∏ᵢ ofReal (1 - 0) = 1`
  rw [hQ, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp
/-- **Simon, proof of Ch. 6, 5.1, (31)** (integer median): an integer-valued `μ`-a.e.-measurable
`u` on a probability space has an integer `β` with `μ{u ≥ β} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`.
`F(t) = μ{u ≤ t}` is nondecreasing, tends to `1` along `ℕ` (continuity from below) and to `0`
along `−ℕ` (continuity from above, the sets `{u ≤ t}` being `μ`-null-measurable), so
`{z ∈ ℤ : F(z) ≥ 1/2}` has a least element `β`; then `F(β − 1) < 1/2`, and as `u` is
integer-valued, `{u ≥ β} = {u ≤ β − 1}ᶜ` has measure `1 − F(β − 1) > 1/2`. -/
theorem Submission.cmcdt_cbm_im_integer_median_exists : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ), IsProbabilityMeasure μ → AEMeasurable u μ → (∀ x, ∃ z : ℤ, u x = z) → ∃ β : ℤ, 1 / 2 ≤ μ.real {x | (β : ℝ) ≤ u x} ∧ 1 / 2 ≤ μ.real {x | u x ≤ (β : ℝ)} := by
  intro X _ μ u _ hu hint
  -- the sublevel sets `{u ≤ t}` are null-measurable, and `F(t) = μ{u ≤ t}` is nondecreasing
  have hnm : ∀ t : ℝ, NullMeasurableSet {x | u x ≤ t} μ := fun t =>
    hu.nullMeasurableSet_preimage measurableSet_Iic
  have hmono : ∀ s t : ℝ, s ≤ t → μ.real {x | u x ≤ s} ≤ μ.real {x | u x ≤ t} :=
    fun s t hst => measureReal_mono fun x (hx : u x ≤ s) => hx.trans hst
  -- upper tail: `F(n) → 1` (continuity from below)
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, 1 / 2 < μ.real {x | u x ≤ (n : ℝ)} := by
    have hm : Monotone fun n : ℕ => {x | u x ≤ (n : ℝ)} :=
      fun m n hmn x (hx : u x ≤ m) => hx.trans (Nat.cast_le.mpr hmn)
    have hU : (⋃ n : ℕ, {x | u x ≤ (n : ℝ)}) = univ :=
      eq_univ_of_forall fun x => mem_iUnion.mpr (exists_nat_ge (u x))
    have h := tendsto_measure_iUnion_atTop (μ := μ) hm
    rw [hU, measure_univ] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
    rw [ENNReal.toReal_one] at h'
    exact (h'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).exists
  -- lower tail: `F(-n) → 0` (continuity from above)
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, μ.real {x | u x ≤ -(n : ℝ)} < 1 / 2 := by
    have hm : Antitone fun n : ℕ => {x | u x ≤ -(n : ℝ)} :=
      fun m n hmn x (hx : u x ≤ -(n : ℝ)) => hx.trans (neg_le_neg (Nat.cast_le.mpr hmn))
    have hI : (⋂ n : ℕ, {x | u x ≤ -(n : ℝ)}) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (-u x)
      have hxn : u x ≤ -(n : ℝ) := mem_iInter.mp hx n
      linarith
    have h := tendsto_measure_iInter_atTop (μ := μ) (fun n => hnm _) hm ⟨0, measure_ne_top _ _⟩
    rw [hI, measure_empty] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h'
    exact (h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).exists
  -- `β`: the least integer `z` with `F(z) ≥ 1/2`
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd
    (P := fun z : ℤ => 1 / 2 ≤ μ.real {x | u x ≤ (z : ℝ)})
    ⟨-(n₀ : ℤ), fun z hz => by
      by_contra hlt
      have hz' : (z : ℝ) ≤ -(n₀ : ℝ) := by exact_mod_cast (not_le.mp hlt).le
      linarith [hmono _ _ hz']⟩
    ⟨n₁, by exact_mod_cast hn₁.le⟩
  refine ⟨β, ?_, hβ⟩
  -- `F(β - 1) < 1/2` by minimality
  have hβ1 : μ.real {x | u x ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 := by
    by_contra h
    have := hβmin (β - 1) (not_lt.mp h)
    omega
  -- `u` is integer-valued, so `{β ≤ u} = {u ≤ β - 1}ᶜ`
  have hset : {x | (β : ℝ) ≤ u x} = {x | u x ≤ ((β - 1 : ℤ) : ℝ)}ᶜ := by
    ext x
    obtain ⟨z, hz⟩ := hint x
    rw [mem_compl_iff, mem_ofPred, mem_ofPred, hz, Int.cast_le, Int.cast_le]
    omega
  rw [hset, probReal_compl_eq_one_sub₀ (hnm _)]
  linarith
/-- **A median minimizes the mean absolute deviation.**  If `μ` is a probability measure, `u` is
`μ`-integrable and `β` is a median of `u` (`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`), then
`∫ |u − β| dμ ≤ ∫ |u − c| dμ` for every `c`.  For `c ≥ β` take `s = {u ≤ β}`, `d = c − β`; for
`c < β` take `s = {β ≤ u}`, `d = β − c`.  Then `|u − c| − |u − β|` equals `d` on `s` and is
`≥ −d` off `s` (triangle inequality), so integrating `d (2·1_s − 1) ≤ |u − c| − |u − β|` gives
`∫ |u − c| − ∫ |u − β| ≥ d (2μ(s) − 1) ≥ 0`. -/
theorem Submission.cmcdt_cbm_im_median_minimizes : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → ∀ c : ℝ, ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
  intro X _ μ u β _ hu hge hle c
  -- every `|u − a|` is integrable
  have hint : ∀ a : ℝ, Integrable (fun x => |u x - a|) μ := fun a =>
    (hu.sub (integrable_const a)).abs
  -- key step: integrate `d (2·1_s − 1) ≤ |u − c| − |u − β|`, using `μ(s) ≥ 1/2` and `d ≥ 0`
  have key : ∀ s : Set X, NullMeasurableSet s μ → 1 / 2 ≤ μ.real s → ∀ d : ℝ, 0 ≤ d →
      (∀ x, s.indicator (fun _ => 2 * d) x - d ≤ |u x - c| - |u x - β|) →
      ∫ x, |u x - β| ∂μ ≤ ∫ x, |u x - c| ∂μ := by
    intro s hs hs2 d hd hpt
    have hind : Integrable (s.indicator fun _ => 2 * d) μ :=
      (integrable_const (2 * d)).indicator₀ hs
    have h : ∫ x, (s.indicator (fun _ => 2 * d) x - d) ∂μ ≤ ∫ x, (|u x - c| - |u x - β|) ∂μ :=
      integral_mono (hind.sub (integrable_const d)) ((hint c).sub (hint β)) hpt
    rw [integral_sub hind (integrable_const d), integral_sub (hint c) (hint β),
      integral_indicator₀ hs, setIntegral_const, integral_const, probReal_univ, smul_eq_mul,
      smul_eq_mul, one_mul] at h
    nlinarith
  rcases le_or_gt β c with hc | hc
  · -- `c ≥ β`: `s = {u ≤ β}`, `d = c − β`
    refine key {x | u x ≤ β} (hu.aemeasurable.nullMeasurableSet_preimage measurableSet_Iic) hle
      (c - β) (sub_nonneg.mpr hc) fun x => ?_
    by_cases hx : u x ≤ β
    · rw [indicator_of_mem (show x ∈ {x | u x ≤ β} from hx), abs_of_nonpos (by linarith),
        abs_of_nonpos (by linarith)]
      linarith
    · rw [indicator_of_notMem (show x ∉ {x | u x ≤ β} from hx)]
      have := abs_sub_le (u x) c β
      rw [abs_of_nonneg (sub_nonneg.mpr hc)] at this
      linarith
  · -- `c < β`: `s = {β ≤ u}`, `d = β − c`
    refine key {x | β ≤ u x} (hu.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici) hge
      (β - c) (sub_nonneg.mpr hc.le) fun x => ?_
    by_cases hx : β ≤ u x
    · rw [indicator_of_mem (show x ∈ {x | β ≤ u x} from hx), abs_of_nonneg (by linarith),
        abs_of_nonneg (by linarith)]
      linarith
    · rw [indicator_of_notMem (show x ∉ {x | β ≤ u x} from hx)]
      have := abs_sub_le (u x) c β
      rw [abs_of_nonpos (sub_nonpos.mpr hc.le)] at this
      linarith
/-- **Simon Ch. 6, proof of 5.1, (35)**: a median `β` of an integrable `u` on a probability space
(`μ{β ≤ u} ≥ 1/2` and `μ{u ≤ β} ≥ 1/2`, Simon's (31)) satisfies `|β| ≤ 2 ∫ |u| dμ`.  According to
the sign of `β`, one of the two median halves lies in `{|β| ≤ |u|}`, so Markov's inequality for
`|u|` at level `|β|` gives `|β| / 2 ≤ ∫ |u| dμ`. -/
theorem Submission.cmcdt_cbm_im_median_abs_le : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (u : X → ℝ) (β : ℝ), IsProbabilityMeasure μ → Integrable u μ → 1 / 2 ≤ μ.real {x | β ≤ u x} → 1 / 2 ≤ μ.real {x | u x ≤ β} → |β| ≤ 2 * ∫ x, |u x| ∂μ := by
  intro X _ μ u β _ hu hge hle
  -- Markov's inequality for `|u|` at level `|β|`
  have hM : |β| * μ.real {x | |β| ≤ |u x|} ≤ ∫ x, |u x| ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg (u x)) hu.abs |β|
  -- one of the two median halves lies in `{|β| ≤ |u|}`
  have hhalf : 1 / 2 ≤ μ.real {x | |β| ≤ |u x|} := by
    rcases le_or_gt 0 β with hβ | hβ
    · refine hge.trans (measureReal_mono fun x (hx : β ≤ u x) => ?_)
      show |β| ≤ |u x|
      rw [abs_of_nonneg hβ, abs_of_nonneg (hβ.trans hx)]
      exact hx
    · refine hle.trans (measureReal_mono fun x (hx : u x ≤ β) => ?_)
      show |β| ≤ |u x|
      rw [abs_of_neg hβ, abs_of_neg (hx.trans_lt hβ)]
      exact neg_le_neg hx
  linarith [mul_le_mul_of_nonneg_left hhalf (abs_nonneg β)]
/-- **Simon, proof of Ch. 6, 5.1, (31) and (35)** (integer median on the unit cube): an
integer-valued `u` integrable on `Q₁ = (0, 1)ⁿ` has an integer median `β`, which minimizes
`c ↦ ∫_{Q₁} |u − c|` and satisfies `|β| ≤ 2 ∫_{Q₁} |u|`.  As `vol(Q₁) = 1`, `μ = vol⌞Q₁` is a
probability measure; `β` is an integer median of `u` for `μ`, and a median minimizes the mean
absolute deviation and is bounded by twice the mean of `|u|`. -/
theorem Submission.cmcdt_cbm_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, (∀ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c|) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hint hu
  -- `μ = vol⌞Q₁` is a probability measure, since `vol(Q₁) = 1`
  have hμ : IsProbabilityMeasure
      (volume.restrict {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) :=
    ⟨by rw [Measure.restrict_apply_univ, Submission.cmcdt_cbm_im_cube_volume]⟩
  -- an integer median `β` of `u` for `μ`
  obtain ⟨β, hge, hle⟩ := Submission.cmcdt_cbm_im_integer_median_exists _ _ u hμ
    hu.integrable.aemeasurable hint
  -- `β` minimizes `c ↦ ∫_{Q₁} |u − c|` and `|β| ≤ 2 ∫_{Q₁} |u|`
  exact ⟨β, Submission.cmcdt_cbm_im_median_minimizes _ _ u β hμ hu hge hle,
    Submission.cmcdt_cbm_im_median_abs_le _ _ u β hμ hu hge hle⟩
/-- **Continuous functions are integrable on open boxes** (fact (F3) in the proof of the smooth
trace estimate on a cube, cf. Simon 2.8–2.9).  The open box `{z : a < z_j < b ∀ j}` lies in the
image under `toLp 2` of the closed order interval `Icc (fun _ => a) (fun _ => b)` of
`Fin n → ℝ`, which is compact, and a continuous function is integrable on a compact set
(`ContinuousOn.integrableOn_compact`). -/
theorem Submission.cmcdt_cbm_st_box_integrableOn : ∀ (n : ℕ) (h : Euclid n → ℝ) (a b : ℝ), Continuous h → IntegrableOn h {z : Euclid n | ∀ j, a < z j ∧ z j < b} := by
  intro n h a b hh
  -- the open box lies in the closed box `K = toLp '' Icc (fun _ => a) (fun _ => b)`
  have hsub : {z : Euclid n | ∀ j, a < z j ∧ z j < b} ⊆
      (WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ)) :=
    fun z hz => ⟨z.ofLp, ⟨fun j => (hz j).1.le, fun j => (hz j).2.le⟩, rfl⟩
  -- `K` is compact: a closed order interval of `Fin n → ℝ` under the continuous map `toLp 2`
  have hKc : IsCompact ((WithLp.toLp 2) '' (Set.Icc (fun _ => a) (fun _ => b) : Set (Fin n → ℝ))) :=
    isCompact_Icc.image (PiLp.continuous_toLp 2 _)
  exact (hh.continuousOn.integrableOn_compact hKc).mono_set hsub
/-- Coordinate slicing (Fubini in the `i`-th coordinate) on the open cube
`Q = {z : a < z_j < b ∀ j}` of `ℝ^{m+1}`.  Write `ι(t, y) = toLp 2 (Fin.insertNth i t y)` (the
point with `i`-th coordinate `t` and remaining coordinates `y`) and `Q' = {y : a < y_k < b ∀ k}`
in `ℝ^m`.  If `a ≤ b` and `h` is integrable on `Q`, then `y ↦ ∫_a^b h(ι(t, y)) dt` is integrable
on `Q'` and `∫_Q h = ∫_{Q'} ∫_a^b h(ι(t, y)) dt dy`.  `(t, y) ↦ ι(t, y)` is the inverse of
`MeasurableEquiv.piFinSuccAbove` followed by `toLp 2`, a measure-preserving equivalence
`ℝ × ℝ^m ≃ ℝ^{m+1}` that maps `(a, b) × Q'` onto `Q`; then use Fubini with outer variable `y`. -/
theorem Submission.cmcdt_cbm_st_slice_integral : ∀ (m : ℕ) (i : Fin (m + 1)) (a b : ℝ) (h : Euclid (m + 1) → ℝ), a ≤ b → IntegrableOn h {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b} → IntegrableOn (fun y : Fin m → ℝ => ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y))) {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b} ∧ ∫ x in {z : Euclid (m + 1) | ∀ j, a < z j ∧ z j < b}, h x = ∫ y in {y : Fin m → ℝ | ∀ j, a < y j ∧ y j < b}, ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
  intro m i a b h hab hint
  set Q : Set (Euclid (m + 1)) := {z | ∀ j, a < z j ∧ z j < b} with hQ
  set Q' : Set (Fin m → ℝ) := {y | ∀ j, a < y j ∧ y j < b} with hQ'
  -- `E (t, y) = toLp 2 (insertNth i t y)`: a measure-preserving equivalence `ℝ × ℝ^m ≃ ℝ^{m+1}`
  let E : ℝ × (Fin m → ℝ) ≃ᵐ Euclid (m + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm.trans
      (MeasurableEquiv.toLp 2 (Fin (m + 1) → ℝ))
  have hE : MeasurePreserving E (volume.prod volume) volume :=
    (PiLp.volume_preserving_toLp (Fin (m + 1))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have hEapply : ∀ p : ℝ × (Fin m → ℝ), E p = WithLp.toLp 2 (Fin.insertNth i p.1 p.2) :=
    fun p => rfl
  -- `E⁻¹(Q) = (a, b) × Q'`
  have hpre : E ⁻¹' Q = Ioo a b ×ˢ Q' := by
    ext ⟨t, y⟩
    simp only [Set.mem_preimage, hEapply, Q, Q', Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
    rw [Fin.forall_iff_succAbove i]
    simp
  have hint' : Integrable (fun p => h (E p))
      ((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
    rw [Measure.prod_restrict, ← hpre]
    exact (hE.integrableOn_comp_preimage E.measurableEmbedding).2 hint
  -- for `a ≤ b` the inner integral over `(a, b)` is the interval integral `∫_a^b`
  have hinner : ∀ y : Fin m → ℝ, ∫ t in Ioo a b, h (E (t, y)) =
      ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
    intro y
    rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    rfl
  refine ⟨?_, ?_⟩
  · have := hint'.integral_prod_right
    simp only [hinner] at this
    exact this
  · calc ∫ x in Q, h x = ∫ p in E ⁻¹' Q, h (E p) ∂(volume.prod volume) :=
          (hE.setIntegral_preimage_emb E.measurableEmbedding h Q).symm
      _ = ∫ p, h (E p) ∂((volume.restrict (Ioo a b)).prod (volume.restrict Q')) := by
          rw [hpre, Measure.prod_restrict]
      _ = ∫ y in Q', ∫ t in Ioo a b, h (E (t, y)) := integral_prod_symm _ hint'
      _ = ∫ y in Q', ∫ t in a..b, h (WithLp.toLp 2 (Fin.insertNth i t y)) := by
          simp only [hinner]
/-- **One-dimensional boundary term and trace estimate** (the one-dimensional core of the trace
estimate behind Simon Ch. 2, 2.8–2.9).  If `a < b`, `φ, γ` are `C¹` and `|γ| ≤ 1`, then
`|∫_a^b (φγ)'| ≤ (2/(b − a)) ∫_a^b |φ| + 2 ∫_a^b |φ'|`.  By the fundamental theorem of calculus
the left side is `|φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(a)| + |φ(b)|`.  For `c, t ∈ [a, b]`,
`|φ(c)| ≤ |φ(t)| + ∫_a^b |φ'|`; averaging over `t ∈ [a, b]` gives
`|φ(c)| ≤ (b − a)⁻¹ ∫_a^b |φ| + ∫_a^b |φ'|`, applied at `c = a` and `c = b`. -/
theorem Submission.cmcdt_cbm_st_interval_bound : ∀ (φ γ : ℝ → ℝ) (a b : ℝ), ContDiff ℝ 1 φ → ContDiff ℝ 1 γ → (∀ t, |γ t| ≤ 1) → a < b → |∫ t in a..b, deriv (fun s => φ s * γ s) t| ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
  intro φ γ a b hφ hγ hγb hab
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hφ'c : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpc : ContDiff ℝ 1 (fun s => φ s * γ s) := hφ.mul hγ
  -- Step 1: fundamental theorem of calculus for the product
  have hftc : ∫ t in a..b, deriv (fun s => φ s * γ s) t = φ b * γ b - φ a * γ a :=
    intervalIntegral.integral_deriv_eq_sub (fun t _ => (hpc.differentiable one_ne_zero) t)
      ((hpc.continuous_deriv le_rfl).intervalIntegrable _ _)
  -- Step 2: the one-dimensional trace inequality at a point `c ∈ [a, b]`
  have htrace : ∀ c ∈ Icc a b,
      |φ c| ≤ (b - a)⁻¹ * (∫ t in a..b, |φ t|) + ∫ t in a..b, |deriv φ t| := by
    intro c hc
    set D := ∫ t in a..b, |deriv φ t| with hD
    -- 2a: `|φ(c)| ≤ |φ(t)| + D` for `t ∈ [a, b]`, by FTC on the segment between `t` and `c`
    have hpt : ∀ t ∈ Icc a b, |φ c| ≤ |φ t| + D := by
      intro t ht
      have hsub : φ c - φ t = ∫ s in t..c, deriv φ s :=
        (intervalIntegral.integral_deriv_eq_sub (fun s _ => hφd s)
          (hφ'c.intervalIntegrable _ _)).symm
      have hle : |∫ s in t..c, deriv φ s| ≤ D := by
        have habs : |∫ s in t..c, deriv φ s| ≤ |∫ s in t..c, (|deriv φ s|)| := by
          simpa only [Real.norm_eq_abs] using
            (intervalIntegral.norm_integral_le_abs_integral_norm (f := deriv φ) (a := t) (b := c)
              (μ := volume))
        refine habs.trans ?_
        rcases le_total t c with htc | hct
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg htc fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval ht.1 htc hc.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
        · rw [intervalIntegral.integral_symm, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hct fun s _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hc.1 hct ht.2
            (Eventually.of_forall fun s => abs_nonneg _) (hφ'c.abs.intervalIntegrable _ _)
      calc |φ c| = |φ t + (φ c - φ t)| := by ring_nf
        _ ≤ |φ t| + |φ c - φ t| := abs_add_le _ _
        _ ≤ |φ t| + D := by rw [hsub]; gcongr
    -- 2b: average over `t ∈ [a, b]`
    have hint : ∫ t in a..b, |φ c| ≤ ∫ t in a..b, (|φ t| + D) :=
      intervalIntegral.integral_mono_on hab.le intervalIntegrable_const
        ((hφd.continuous.abs.add continuous_const).intervalIntegrable _ _) hpt
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (hφd.continuous.abs.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul] at hint
    -- 2c: divide by `b - a > 0`
    have hba : 0 < b - a := sub_pos.mpr hab
    rw [inv_mul_eq_div, ← sub_le_iff_le_add, le_div_iff₀ hba]
    nlinarith
  -- Step 3: `|φ(b)γ(b) − φ(a)γ(a)| ≤ |φ(b)| + |φ(a)|`, then Step 2 at `c = a` and `c = b`
  have hA := htrace a ⟨le_rfl, hab.le⟩
  have hB := htrace b ⟨hab.le, le_rfl⟩
  rw [hftc]
  have hγa := hγb a
  have hγb' := hγb b
  calc |φ b * γ b - φ a * γ a| ≤ |φ b * γ b| + |φ a * γ a| := abs_sub _ _
    _ = |φ b| * |γ b| + |φ a| * |γ a| := by rw [abs_mul, abs_mul]
    _ ≤ |φ b| * 1 + |φ a| * 1 := by gcongr
    _ = |φ b| + |φ a| := by ring
    _ ≤ 2 / (b - a) * (∫ t in a..b, |φ t|) + 2 * ∫ t in a..b, |deriv φ t| := by
        have : 2 / (b - a) = (b - a)⁻¹ + (b - a)⁻¹ := by ring
        rw [this]; linarith

/-- **One-coordinate divergence and trace estimate on `Q_δ`** (steps 2–4 of the smooth trace
estimate on a cube, cf. Simon 2.8–2.9).  For `C¹` functions `v, g` on `ℝ^{m+1}` with `|g| ≤ 1` and
`0 ≤ δ ≤ 1/4`, `|∫_{Q_δ} D(vg)(x)e_i dx| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖`.  Slice `Q_δ` along the
coordinate `i` (`cmcdt_cbm_st_slice_integral`); on each line `t ↦ ι(t, y)` the one-dimensional
boundary and trace estimate (`cmcdt_cbm_st_interval_bound`) applies, the side length
`1 − 2δ ≥ 1/2` gives `2/(1 − 2δ) ≤ 4`, and `|Dv(x)e_i| ≤ ‖Dv(x)‖`; then integrate over the
slice variable `y`. -/
theorem Submission.cmcdt_cbm_st_coord_bound : ∀ (m : ℕ) (v g : Euclid (m + 1) → ℝ) (i : Fin (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 g → (∀ y, |g y| ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)| ≤ 4 * (∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, |v x|) + 2 * ∫ x in {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ}, ‖fderiv ℝ v x‖ := by
  intro m v g i δ hv hg hgb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ j, δ < z j ∧ z j < 1 - δ} with hQ
  set Q' : Set (Fin m → ℝ) := {y : Fin m → ℝ | ∀ j, δ < y j ∧ y j < 1 - δ} with hQ'
  have hab : δ < 1 - δ := by linarith
  -- the line `t ↦ ι t y` through the slice point `y` in direction `e_i`
  set ι : ℝ → (Fin m → ℝ) → Euclid (m + 1) := fun t y => WithLp.toLp 2 (Fin.insertNth i t y)
    with hι
  have hι_affine : ∀ t y, ι t y = ι 0 y + t • EuclideanSpace.single i 1 := by
    intro t y
    ext j
    induction j using Fin.succAboveCases i with
    | x => simp [ι]
    | p j => simp [ι, Fin.succAbove_ne]
  have hι_deriv : ∀ t y, HasDerivAt (fun s => ι s y) (EuclideanSpace.single i 1) t := by
    intro t y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    simpa using ((hasDerivAt_id t).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add (ι 0 y)
  have hι_cd : ∀ y, ContDiff ℝ 1 (fun s => ι s y) := by
    intro y
    have : (fun s => ι s y) = fun s => ι 0 y + s • EuclideanSpace.single i (1 : ℝ) := by
      funext s; exact hι_affine s y
    rw [this]
    exact contDiff_const.add (contDiff_id.smul contDiff_const)
  have hvg : ContDiff ℝ 1 (fun y => v y * g y) := hv.mul hg
  set F : Euclid (m + 1) → ℝ := fun x => fderiv ℝ (fun y => v y * g y) x (EuclideanSpace.single i 1)
    with hF
  set H : Euclid (m + 1) → ℝ := fun x => 4 * |v x| + 2 * ‖fderiv ℝ v x‖ with hH
  have hFc : Continuous F := (hvg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : Continuous fun x => |v x| := hv.continuous.abs
  have hDvc : Continuous fun x => ‖fderiv ℝ v x‖ := (hv.continuous_fderiv one_ne_zero).norm
  have hHc : Continuous H := (continuous_const.mul hvc).add (continuous_const.mul hDvc)
  obtain ⟨-, hFslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) F hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hFc)
  obtain ⟨hHint, hHslice⟩ := Submission.cmcdt_cbm_st_slice_integral m i δ (1 - δ) H hab.le
    (Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hHc)
  have hHsplit : ∫ x in Q, H x = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [integral_add ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hvc).const_mul 4)
      ((Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hDvc).const_mul 2),
      integral_const_mul, integral_const_mul]
  -- the one-dimensional estimate on each line
  have hline : ∀ y, |∫ t in δ..(1 - δ), F (ι t y)| ≤ ∫ t in δ..(1 - δ), H (ι t y) := by
    intro y
    have hφ : ContDiff ℝ 1 (fun s => v (ι s y)) := hv.comp (hι_cd y)
    have hγ : ContDiff ℝ 1 (fun s => g (ι s y)) := hg.comp (hι_cd y)
    have hderiv_prod : ∀ t, deriv (fun s => v (ι s y) * g (ι s y)) t = F (ι t y) := by
      intro t
      have := ((hvg.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have hderiv_v : ∀ t, deriv (fun s => v (ι s y)) t =
        fderiv ℝ v (ι t y) (EuclideanSpace.single i 1) := by
      intro t
      have := ((hv.differentiable one_ne_zero (ι t y)).hasFDerivAt).comp_hasDerivAt t
        (hι_deriv t y)
      exact this.deriv
    have h1 := Submission.cmcdt_cbm_st_interval_bound (fun s => v (ι s y)) (fun s => g (ι s y))
      δ (1 - δ) hφ hγ (fun t => hgb _) hab
    simp only [hderiv_prod, hderiv_v] at h1
    have hcoef : 2 / (1 - δ - δ) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hint_nonneg : 0 ≤ ∫ t in δ..(1 - δ), |v (ι t y)| :=
      intervalIntegral.integral_nonneg hab.le fun t _ => abs_nonneg _
    have hcont_v : Continuous fun t => |v (ι t y)| := hφ.continuous.abs
    have hcont_Dv : Continuous fun t => ‖fderiv ℝ v (ι t y)‖ := hDvc.comp (hι_cd y).continuous
    have hcont_dv : Continuous fun t => |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| :=
      (((hv.continuous_fderiv one_ne_zero).comp (hι_cd y).continuous).clm_apply
        continuous_const).abs
    have hmono : ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| ≤
        ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      refine intervalIntegral.integral_mono_on hab.le (hcont_dv.intervalIntegrable _ _)
        (hcont_Dv.intervalIntegrable _ _) fun t _ => ?_
      have := (fderiv ℝ v (ι t y)).le_opNorm (EuclideanSpace.single i 1)
      rw [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] at this
      exact this
    have hHline : ∫ t in δ..(1 - δ), H (ι t y) =
        4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
      simp only [H]
      rw [intervalIntegral.integral_add ((hcont_v.intervalIntegrable _ _).const_mul 4)
        ((hcont_Dv.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    rw [hHline]
    calc |∫ t in δ..(1 - δ), F (ι t y)|
        ≤ 2 / (1 - δ - δ) * (∫ t in δ..(1 - δ), |v (ι t y)|) +
            2 * ∫ t in δ..(1 - δ), |fderiv ℝ v (ι t y) (EuclideanSpace.single i 1)| := h1
      _ ≤ 4 * (∫ t in δ..(1 - δ), |v (ι t y)|) + 2 * ∫ t in δ..(1 - δ), ‖fderiv ℝ v (ι t y)‖ := by
        gcongr
  calc |∫ x in Q, F x|
      = |∫ y in Q', ∫ t in δ..(1 - δ), F (ι t y)| := by rw [hFslice]
    _ ≤ ∫ y in Q', |∫ t in δ..(1 - δ), F (ι t y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y in Q', ∫ t in δ..(1 - δ), H (ι t y) :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hHint
          (Eventually.of_forall hline)
    _ = ∫ x in Q, H x := hHslice.symm
    _ = 4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := hHsplit
/-- **Product rule for the divergence**, at one point (step 1 of the smooth trace estimate on a
cube, cf. Simon Ch. 2, 2.8).  If `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` (`ℝⁿ = Euclid (m + 1)`) are
differentiable at `x`, then `v(x) div G(x) = Σᵢ Dᵢ(v Gᵢ)(x) − Dv(x) G(x)`, where
`div G(x) = trace DG(x)` and `Dᵢ` is the derivative along `eᵢ = EuclideanSpace.single i 1`.
In the standard orthonormal basis `trace DG(x) = Σᵢ (DG(x) eᵢ)ᵢ`; the product rule gives
`Dᵢ(v Gᵢ)(x) = v(x) (DG(x) eᵢ)ᵢ + Gᵢ(x) Dv(x) eᵢ`, and `Σᵢ Gᵢ(x) Dv(x) eᵢ = Dv(x) G(x)`. -/
theorem Submission.cmcdt_cbm_st_div_product : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (x : Euclid (m + 1)), DifferentiableAt ℝ v x → DifferentiableAt ℝ G x → v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = ∑ i, fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) - fderiv ℝ v x (G x) := by
  intro m v G x hv hG
  -- derivative of the coordinate `Gᵢ = projᵢ ∘ G`
  have hGi : ∀ i : Fin (m + 1), HasFDerivAt (fun y => G y i)
      ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x)) x := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp x hG.hasFDerivAt
  -- product rule, evaluated at `eᵢ`
  have hprod : ∀ i : Fin (m + 1),
      fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) =
        v x * (fderiv ℝ G x (EuclideanSpace.single i 1)) i +
          G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    intro i
    have h : HasFDerivAt (fun y => v y * G y i)
        (v x • (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G x) +
          G x i • fderiv ℝ v x) x := hv.hasFDerivAt.mul (hGi i)
    rw [h.fderiv]
    simp
  -- trace in the standard orthonormal basis
  have htrace : LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      ∑ i, (fderiv ℝ G x (EuclideanSpace.single i 1)) i := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
    simp
  -- `G x = Σᵢ (G x)ᵢ eᵢ`, hence `Dv(x) (G x) = Σᵢ (G x)ᵢ Dv(x) eᵢ`
  have hexp : G x = ∑ i, G x i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hDvG : fderiv ℝ v x (G x) = ∑ i, G x i * fderiv ℝ v x (EuclideanSpace.single i 1) := by
    conv_lhs => rw [hexp]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [htrace, hDvG, Finset.mul_sum]
  simp only [hprod, Finset.sum_add_distrib]
  ring

/-- **Smooth trace estimate on the cube `Q_δ`** (step 5 of the cube BV median estimate, smooth
part; the smooth case of Simon Ch. 2, 2.8–2.9).  Let `n = m + 1`, `0 ≤ δ ≤ 1/4` and
`Q_δ = {y : δ < y_i < 1 − δ ∀ i}`.  For `C¹` maps `v : ℝⁿ → ℝ` and `G : ℝⁿ → ℝⁿ` with `|G| ≤ 1`,
`|∫_{Q_δ} v div G| ≤ (2n + 1) ∫_{Q_δ} ‖Dv‖ + 4n ∫_{Q_δ} |v|`, where `div G = trace DG`.
By the product rule (`cmcdt_cbm_st_div_product`), `v div G = Σᵢ Dᵢ(v Gᵢ) − Dv(G)`, and all terms
are continuous, hence integrable on `Q_δ` (`cmcdt_cbm_st_box_integrableOn`).  Each coordinate
term satisfies `|∫_{Q_δ} Dᵢ(v Gᵢ)| ≤ 4 ∫_{Q_δ} |v| + 2 ∫_{Q_δ} ‖Dv‖` (`cmcdt_cbm_st_coord_bound`
with `g = Gᵢ`, `|Gᵢ| ≤ |G| ≤ 1`), and `|Dv(G)| ≤ ‖Dv‖`.  Summing over the `n` coordinates gives
the bound. -/
theorem Submission.cmcdt_cbm_smooth_trace : ∀ (m : ℕ) (v : Euclid (m + 1) → ℝ) (G : Euclid (m + 1) → Euclid (m + 1)) (δ : ℝ), ContDiff ℝ 1 v → ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → 0 ≤ δ → δ ≤ 1 / 4 → |∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x)| ≤ (2 * (m + 1) + 1) * (∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v x| := by
  intro m v G δ hv hG hGb hδ0 hδ1
  set Q : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} with hQ
  -- the coordinates `Gᵢ` of `G` are `C¹`, with `|Gᵢ| ≤ ‖G‖ ≤ 1`
  have hGi : ∀ i : Fin (m + 1), ContDiff ℝ 1 (fun y => G y i) := fun i =>
    (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hGib : ∀ (i : Fin (m + 1)) (y : Euclid (m + 1)), |G y i| ≤ 1 := fun i y => by
    rw [← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le (G y) i).trans (hGb y)
  -- `Fᵢ = Dᵢ(v Gᵢ)`, `D = Dv(G)` and `‖Dv‖` are continuous, hence integrable on `Q_δ`
  set F : Fin (m + 1) → Euclid (m + 1) → ℝ :=
    fun i x => fderiv ℝ (fun y => v y * G y i) x (EuclideanSpace.single i 1) with hF
  set D : Euclid (m + 1) → ℝ := fun x => fderiv ℝ v x (G x) with hD
  have hFc : ∀ i, Continuous (F i) := fun i =>
    ((hv.mul (hGi i)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : Continuous D := (hv.continuous_fderiv one_ne_zero).clm_apply hG.continuous
  have hFint : ∀ i, IntegrableOn (F i) Q := fun i =>
    Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ (hFc i)
  have hDint : IntegrableOn D Q := Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ hDc
  have hDvint : IntegrableOn (fun x => ‖fderiv ℝ v x‖) Q :=
    Submission.cmcdt_cbm_st_box_integrableOn _ _ _ _ (hv.continuous_fderiv one_ne_zero).norm
  -- step 1: `∫ v div G = Σᵢ ∫ Fᵢ − ∫ D`
  have hpt : ∀ x, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) = (∑ i, F i x) - D x :=
    fun x => Submission.cmcdt_cbm_st_div_product m v G x (hv.differentiable one_ne_zero x)
      (hG.differentiable one_ne_zero x)
  have hsplit : ∫ x in Q, v x * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G x) =
      (∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x := by
    simp only [hpt]
    rw [integral_sub (integrable_finsetSum _ fun i _ => hFint i) hDint,
      integral_finsetSum _ fun i _ => hFint i]
  -- step 2: each coordinate term is bounded by `4 ∫ |v| + 2 ∫ ‖Dv‖`
  have hcoord : ∀ i, |∫ x in Q, F i x| ≤
      4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖ := fun i =>
    Submission.cmcdt_cbm_st_coord_bound m v (fun y => G y i) i δ hv (hGi i) (hGib i) hδ0 hδ1
  -- step 3: `|∫ Dv(G)| ≤ ∫ ‖Dv‖`, since `‖G‖ ≤ 1`
  have hDbound : |∫ x in Q, D x| ≤ ∫ x in Q, ‖fderiv ℝ v x‖ := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hDvint (Eventually.of_forall fun x => ?_)
    calc ‖D x‖ ≤ ‖fderiv ℝ v x‖ * ‖G x‖ := (fderiv ℝ v x).le_opNorm (G x)
      _ ≤ ‖fderiv ℝ v x‖ * 1 := mul_le_mul_of_nonneg_left (hGb x) (norm_nonneg _)
      _ = ‖fderiv ℝ v x‖ := mul_one _
  -- step 4: sum over the `m + 1` coordinates
  rw [hsplit]
  calc |(∑ i, ∫ x in Q, F i x) - ∫ x in Q, D x|
      ≤ |∑ i, ∫ x in Q, F i x| + |∫ x in Q, D x| := abs_sub _ _
    _ ≤ (∑ i, |∫ x in Q, F i x|) + |∫ x in Q, D x| :=
        add_le_add_left (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ (∑ _i : Fin (m + 1), (4 * (∫ x in Q, |v x|) + 2 * ∫ x in Q, ‖fderiv ℝ v x‖)) +
          ∫ x in Q, ‖fderiv ℝ v x‖ :=
        add_le_add (Finset.sum_le_sum fun i _ => hcoord i) hDbound
    _ = (2 * (m + 1) + 1) * (∫ x in Q, ‖fderiv ℝ v x‖) + 4 * (m + 1) * ∫ x in Q, |v x| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
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
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm

/-- **Simon Ch. 6, 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U`, then
`M_W(T) = μ_R(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W`.  The upper bound
`dor_ims_massOn_le_measure` and the lower bound `dor_ims_measure_le_massOn` give equality by
antisymmetry. -/
theorem Submission.cmc_massOn_eq_imRep_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := by
  intro P n U T R hU hR W hW
  exact le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
    (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
/-- Localized Besicovitch density (Simon Ch. 1, Theorem 3.16; Mathlib's
`Besicovitch.ae_tendsto_measure_inter_div`).  Let `U` be open, `A ⊆ B ⊆ U` Borel, and
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`.  Then for `Hⁿ⌞A`-a.e. `x` and every `ε > 0`,
`Hⁿ((B \ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for all small `ρ > 0`.

Proof sketch:
* Cover `U` by countably many open balls `B_r(y)` with `B̄_r(y) ⊆ U`.
* On each ball, `ν = Hⁿ⌞(B ∩ B̄_r(y))` is finite, so Besicovitch gives
  `ν(A ∩ B̄_ρ(x))/ν(B̄_ρ(x)) → 1` for `ν⌞A = (Hⁿ⌞A)⌞B̄_r(y)`-a.e. `x`.
* For `x ∈ B_r(y)` and small `ρ`, this quotient is `b/a`, where
  `b = Hⁿ(A ∩ B̄_ρ(x))` and `a = Hⁿ(B ∩ B̄_ρ(x)) < ∞`.
* If `ε ≥ 1`, the bound is monotonicity.
* If `ε < 1`, eventually `b/a > 1 − ε`, which forces `0 < a < ∞`; hence
  `Hⁿ((B \ A) ∩ B̄_ρ(x)) = a − b ≤ εa`. -/
theorem Submission.rsdic_tl_ae_excess_le : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Step 1: countably many balls `B(y, r y)`, `y ∈ D`, with `B̄(y, r y) ⊆ U` cover `U`
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨δ / 2, half_pos hδ, (closedBall_subset_ball (half_lt_self hδ)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Step 2: Besicovitch's density theorem for the finite measures `Hⁿ⌞(B ∩ B̄(y, r y))`
  have hpiece : ∀ᵐ x ∂(μHE[n].restrict A), ∀ y ∈ D, x ∈ closedBall y (r y) →
      Tendsto (fun ρ : ℝ => (μHE[n].restrict (B ∩ closedBall y (r y))) (A ∩ closedBall x ρ) /
        (μHE[n].restrict (B ∩ closedBall y (r y))) (closedBall x ρ)) (𝓝[>] 0) (𝓝 1) := by
    rw [ae_ball_iff hDc]
    intro y hy
    have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) :=
      ⟨by
        rw [Measure.restrict_apply_univ]
        exact (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy))).lt_top⟩
    have h := Besicovitch.ae_tendsto_measure_inter_div
      ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))) A
    -- `(Hⁿ⌞(B ∩ K))⌞A = (Hⁿ⌞A)⌞K` since `A ⊆ B`
    have hres : ((μHE[n] : Measure (Euclid P)).restrict (B ∩ closedBall y (r y))).restrict A =
        ((μHE[n] : Measure (Euclid P)).restrict A).restrict (closedBall y (r y)) := by
      rw [Measure.restrict_restrict hA, Measure.restrict_restrict measurableSet_closedBall]
      congr 1
      ext z
      exact ⟨fun ⟨hzA, _, hzK⟩ => ⟨hzK, hzA⟩, fun ⟨hzK, hzA⟩ => ⟨hzA, hAB hzA, hzK⟩⟩
    rwa [hres, ae_restrict_iff' measurableSet_closedBall] at h
  filter_upwards [hpiece, ae_restrict_mem hA] with x hx hxA ε hε
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov (hBU (hAB hxA)))
  obtain ⟨δ, hδ, hδy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  have hsmall : ∀ ρ : ℝ, ρ < δ → closedBall x ρ ⊆ closedBall y (r y) := fun ρ hρ =>
    ((closedBall_subset_ball hρ).trans hδy).trans ball_subset_closedBall
  have hBK : MeasurableSet (B ∩ closedBall y (r y)) := hB.inter measurableSet_closedBall
  -- Step 3: for `ρ < δ` the quotient is `Hⁿ(A ∩ B̄_ρ(x)) / Hⁿ(B ∩ B̄_ρ(x))`
  have hT : Tendsto (fun ρ : ℝ => μHE[n] (A ∩ closedBall x ρ) / μHE[n] (B ∩ closedBall x ρ))
      (𝓝[>] 0) (𝓝 1) := by
    refine (hx y hyD (ball_subset_closedBall hxy)).congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with ρ hρ
    rw [Measure.restrict_apply' hBK, Measure.restrict_apply' hBK]
    congr 2
    · ext z
      exact ⟨fun ⟨hz, _⟩ => hz, fun ⟨hzA, hzx⟩ => ⟨⟨hzA, hzx⟩, hAB hzA, hsmall ρ hρ.2 hzx⟩⟩
    · ext z
      exact ⟨fun ⟨hzx, hzB, _⟩ => ⟨hzB, hzx⟩, fun ⟨hzB, hzx⟩ => ⟨hzx, hzB, hsmall ρ hρ.2 hzx⟩⟩
  have hfinρ : ∀ ρ : ℝ, ρ < δ → μHE[n] (B ∩ closedBall x ρ) ≠ ∞ := fun ρ hρ =>
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hyD)))
      (measure_mono (inter_subset_inter_right B (hsmall ρ hρ)))
  -- `Hⁿ((B \ A) ∩ B̄_ρ(x)) + Hⁿ(A ∩ B̄_ρ(x)) = Hⁿ(B ∩ B̄_ρ(x))`
  have hsplit : ∀ ρ : ℝ, μHE[n] ((B \ A) ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) =
      μHE[n] (B ∩ closedBall x ρ) := by
    intro ρ
    rw [← measure_union _ (hA.inter measurableSet_closedBall)]
    · congr 1
      ext z
      constructor
      · rintro (⟨⟨hzB, -⟩, hzx⟩ | ⟨hzA, hzx⟩)
        · exact ⟨hzB, hzx⟩
        · exact ⟨hAB hzA, hzx⟩
      · rintro ⟨hzB, hzx⟩
        by_cases hzA : z ∈ A
        · exact Or.inr ⟨hzA, hzx⟩
        · exact Or.inl ⟨⟨hzB, hzA⟩, hzx⟩
    · rw [Set.disjoint_left]
      rintro z ⟨⟨-, hzA⟩, -⟩ ⟨hzA', -⟩
      exact hzA hzA'
  -- Step 4: the excess estimate
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- `ε ≥ 1`: monotonicity
    refine Eventually.of_forall fun ρ => ?_
    calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
          measure_mono (inter_subset_inter_left _ sdiff_subset)
      _ = 1 * μHE[n] (B ∩ closedBall x ρ) := (one_mul _).symm
      _ ≤ ε * μHE[n] (B ∩ closedBall x ρ) := by gcongr
  · -- `ε < 1`: eventually `b / a > 1 − ε`, with `a ≠ ∞`
    have hsub : 1 - ε < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hε.ne'
    filter_upwards [hT (isOpen_Ioi.mem_nhds hsub), Ioo_mem_nhdsGT hδ] with ρ hρq hρ
    set a := μHE[n] (B ∩ closedBall x ρ)
    set b := μHE[n] (A ∩ closedBall x ρ)
    set e := μHE[n] ((B \ A) ∩ closedBall x ρ)
    have hatop : a ≠ ∞ := hfinρ ρ hρ.2
    have hsplitρ : e + b = a := hsplit ρ
    -- `a ≠ 0`, since otherwise `b / a = 0 / 0 = 0 ≤ 1 − ε`
    have ha0 : a ≠ 0 := by
      intro h0
      have hb0 : b = 0 := nonpos_iff_eq_zero.1 (h0 ▸ hsplitρ ▸ le_add_self)
      have : b / a = 0 := by rw [hb0, ENNReal.zero_div]
      rw [mem_preimage, this, mem_Ioi] at hρq
      exact not_lt_zero hρq
    have hlt : (1 - ε) * a < b :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)).1 hρq
    -- `e + (1 − ε)a ≤ e + b = a = εa + (1 − ε)a`, and `(1 − ε)a ≠ ∞`
    have h1 : e + (1 - ε) * a ≤ ε * a + (1 - ε) * a := by
      calc e + (1 - ε) * a ≤ e + b := by gcongr
        _ = a := hsplitρ
        _ = (ε + (1 - ε)) * a := by rw [add_tsub_cancel_of_le hε1.le, one_mul]
        _ = ε * a + (1 - ε) * a := add_mul _ _ _
    exact ENNReal.le_of_add_le_add_right (ENNReal.mul_ne_top (by simp) hatop) h1
/-- Zero `n`-density of the excess `B ∖ A` (step 5 of the tangent-locality argument): if
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` for `0 < ρ < r₁`, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and for every `ε > 0`
eventually `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))`, then `ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_ρ(x)) → 0`.
Subadditivity and `ε = 1/2` give `Hⁿ(B ∩ B̄_ρ(x)) ≤ 2Cρⁿ` for small `ρ` (cancelling the finite
half), and then `ε = δ/(2C + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ δρⁿ`. -/
theorem Submission.rsdic_tl_excess_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ C r₁ : ℝ), 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → 0 < r₁ → (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) → (∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ ε * μHE[n] (B ∩ closedBall x ρ)) → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n A B x r₀ C r₁ hr₀ hfin hr₁ hA hBA
  -- Steps 1–3: eventually `Hⁿ(B ∩ B̄_ρ(x)) ≤ K ρⁿ` with `K = 2 ofReal(C)`
  set K : ℝ≥0∞ := 2 * ENNReal.ofReal C with hK
  have hB : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μHE[n] (B ∩ closedBall x ρ) ≤ K * ENNReal.ofReal ρ ^ n := by
    -- Step 1: eventually `0 < ρ < min r₀ r₁`, so `Hⁿ(B ∩ B̄_ρ(x)) ≤ Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
    filter_upwards [Ioo_mem_nhdsGT (lt_min hr₀ hr₁),
      hBA 2⁻¹ (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top)] with ρ hρ he
    have hρ₀ : ρ ≤ r₀ := (hρ.2.trans_le (min_le_left _ _)).le
    have hρ₁ : ρ < r₁ := hρ.2.trans_le (min_le_right _ _)
    have hfinρ : μHE[n] (B ∩ closedBall x ρ) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right B
        (closedBall_subset_closedBall hρ₀)))
    -- Step 2: subadditivity, `Hⁿ(B ∩ B̄_ρ) ≤ Hⁿ(A ∩ B̄_ρ) + Hⁿ((B ∖ A) ∩ B̄_ρ)`
    have hsub : μHE[n] (B ∩ closedBall x ρ) ≤
        μHE[n] (A ∩ closedBall x ρ) + μHE[n] ((B \ A) ∩ closedBall x ρ) := by
      refine (measure_mono ?_).trans (measure_union_le _ _)
      rintro y ⟨hyB, hyρ⟩
      by_cases hyA : y ∈ A
      · exact Or.inl ⟨hyA, hyρ⟩
      · exact Or.inr ⟨⟨hyB, hyA⟩, hyρ⟩
    -- Step 3: with `ε = 1/2`, cancelling the finite half gives `Hⁿ(B ∩ B̄_ρ)/2 ≤ Hⁿ(A ∩ B̄_ρ)`
    have hhalf : μHE[n] (B ∩ closedBall x ρ) / 2 ≤ μHE[n] (A ∩ closedBall x ρ) := by
      refine (ENNReal.add_le_add_iff_right (ENNReal.div_ne_top hfinρ two_ne_zero)).1 ?_
      rw [ENNReal.add_halves, ENNReal.div_eq_inv_mul]
      exact hsub.trans (add_le_add_right he _)
    calc μHE[n] (B ∩ closedBall x ρ)
        = μHE[n] (B ∩ closedBall x ρ) / 2 + μHE[n] (B ∩ closedBall x ρ) / 2 :=
          (ENNReal.add_halves _).symm
      _ ≤ μHE[n] (A ∩ closedBall x ρ) + μHE[n] (A ∩ closedBall x ρ) := add_le_add hhalf hhalf
      _ = 2 * μHE[n] (A ∩ closedBall x ρ) := (two_mul _).symm
      _ ≤ 2 * ENNReal.ofReal (C * ρ ^ n) := by gcongr; exact hA ρ hρ.1 hρ₁
      _ = K * ENNReal.ofReal ρ ^ n := by
          rw [ENNReal.ofReal_mul' (pow_nonneg hρ.1.le n), ENNReal.ofReal_pow hρ.1.le, hK,
            mul_assoc]
  -- Step 4: for `δ ∈ (0, ∞)`, `ε = δ/(K + 1)` gives `Hⁿ((B ∖ A) ∩ B̄_ρ) ≤ δρⁿ` eventually
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  by_cases hδt : δ = ∞
  · exact Eventually.of_forall fun ρ => hδt ▸ le_top
  have hK1 : K + 1 ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top,
      ENNReal.one_ne_top⟩
  have hK0 : K + 1 ≠ 0 := by positivity
  filter_upwards [hB, hBA _ (ENNReal.div_pos hδ.ne' hK1)] with ρ hρB hρe
  refine ENNReal.div_le_of_le_mul ?_
  calc μHE[n] ((B \ A) ∩ closedBall x ρ) ≤ δ / (K + 1) * μHE[n] (B ∩ closedBall x ρ) := hρe
    _ ≤ δ / (K + 1) * ((K + 1) * ENNReal.ofReal ρ ^ n) := by
        gcongr
        exact hρB.trans (by gcongr; exact le_self_add)
    _ = δ * ENNReal.ofReal ρ ^ n := by rw [← mul_assoc, ENNReal.div_mul_cancel hK0 hK1]
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0`:
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  As `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left side
is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; and `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`,
which multiplies `Hⁿ` by `‖r⁻¹‖₊ⁿ = r⁻ⁿ`, followed by the translation by `−x`, an isometry. -/
theorem Submission.rsdic_tl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`, since `r > 0`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- `η(S) ∩ B̄_R(0) = η(S ∩ B̄_{rR}(x))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm, ← mul_inv_cancel_left₀ hr.ne' ‖z - x‖]
      exact mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm, ← inv_mul_cancel_left₀ hr.ne' R]
      exact mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
  -- `η = τ ∘ h`: the homothety `h` of centre `x` and ratio `r⁻¹`, then the translation by `−x`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- `μ(η(T)) = μ(h(T)) = ‖r⁻¹‖₊ⁿ μ(T) = (ofReal r)⁻¹ⁿ μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  rw [hset, hscale]

/-- **Simon Ch. 3, Remark 1.5(2)** (locality of approximate tangent spaces): if `A ⊆ B` are Borel,
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`, then `B` and `A` have
the same approximate tangent spaces at `x`.  If `f ∈ C_c` vanishes off `B̄_R(0)` and `|f| ≤ M`,
then for `0 < ρ < r₀/R` the difference `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
is at most `M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = M ρ⁻ⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x))` in absolute value,
and this tends to `0`. -/
theorem Submission.rsdic_tl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens Q
  -- Step 1: for `ρ ≠ 0`, `η_{x,ρ}` is injective and `η_{x,ρ}(S) = (y ↦ x + ρy)⁻¹(S)`
  have hinj : ∀ ρ : ℝ, ρ ≠ 0 → Injective (Poincare.SimonGMT.Chapter03.blowUpMap x ρ) := by
    intro ρ hρ a b hab
    exact sub_left_injective (smul_right_injective (Euclid P) (inv_ne_zero hρ) hab)
  have hmeas : ∀ ρ : ℝ, ρ ≠ 0 → ∀ S : Set (Euclid P), MeasurableSet S →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S) := by
    intro ρ hρ S hS
    have himage : Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S =
        (fun y => x + ρ • y) ⁻¹' S := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_inv_smul₀ hρ] using hz
      · intro hy
        exact ⟨x + ρ • y, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, inv_smul_smul₀ hρ]⟩
    rw [himage]
    exact hS.preimage (by fun_prop)
  -- Steps 2–7: for every `f ∈ C_c`, `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f → 0`
  have key : ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      Tendsto (fun ρ : ℝ =>
        (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0) := by
    intro f
    -- Step 2: `f` vanishes off `B̄_R(0)` for some `R > 0`, and `|f| ≤ M`
    obtain ⟨R, hRpos, hout⟩ : ∃ R : ℝ, 0 < R ∧
        ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
      obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
      exact ⟨max R₀ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun y hy =>
        image_eq_zero_of_notMem_tsupport fun hy' =>
          hy (closedBall_subset_closedBall (le_max_left _ _) (hR₀ hy'))⟩
    obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    -- Step 3: `f` is integrable on `S` whenever `Hⁿ(S ∩ B̄_R(0)) < ∞`
    have hint : ∀ S : Set (Euclid P), μHE[n] (S ∩ closedBall 0 R) ≠ ∞ →
        IntegrableOn (fun y => f y) S μHE[n] := by
      intro S hS
      refine Integrable.mono' (g := (closedBall (0 : Euclid P) R).indicator fun _ => M) ?_
        f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
      · rw [integrable_indicator_iff measurableSet_closedBall]
        refine integrableOn_const ?_
        rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
        exact hS
      · by_cases hy : y ∈ closedBall (0 : Euclid P) R
        · rw [Set.indicator_of_mem hy]
          exact hM y
        · rw [Set.indicator_of_notMem hy, hout y hy, norm_zero]
    -- Steps 4–6 give `|∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f| ≤ M Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0))` for
    -- `0 < ρ < r₀/R`; step 7 sends the bound to `0`
    refine squeeze_zero_norm' (a := fun ρ : ℝ => M *
      (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R)).toReal)
      ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hRpos)] with ρ hρ
      have hρ0 : 0 < ρ := hρ.1
      have hρR : ρ * R < r₀ := (lt_div_iff₀ hRpos).1 hρ.2
      -- Step 4: for `S ⊆ B`, `Hⁿ(η_{x,ρ}(S) ∩ B̄_R(0)) = ρ⁻ⁿ Hⁿ(S ∩ B̄_{ρR}(x)) < ∞`
      have hfinS : ∀ S ⊆ B,
          μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' S ∩ closedBall 0 R) ≠ ∞ := by
        intro S hS
        rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R S hρ0]
        exact ENNReal.mul_ne_top
          (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hρ0).ne'))
          (ne_top_of_le_ne_top hfin
            (measure_mono (inter_subset_inter hS (closedBall_subset_closedBall hρR.le))))
      -- Step 5: `∫_{η_{x,ρ}(B)} f − ∫_{η_{x,ρ}(A)} f = ∫_{η_{x,ρ}(B ∖ A)} f`
      have hsplit : (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' B, f y ∂μHE[n]) -
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' A, f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] := by
        rw [image_sdiff (hinj ρ hρ0.ne'), setIntegral_sdiff (hmeas ρ hρ0.ne' A hA)
          (hint _ (hfinS B subset_rfl)) (image_mono hAB)]
      -- Step 6: `f = 0` off `B̄_R(0)` and `|f| ≤ M`
      have hball : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A), f y ∂μHE[n] =
          ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R,
            f y ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas ρ hρ0.ne' _ (hB.diff hA))
          inter_subset_left fun y hy => hout y fun h => hy.2 ⟨hy.1, h⟩
      rw [hsplit, hball]
      exact norm_setIntegral_le_of_norm_le_const (lt_top_iff_ne_top.2 (hfinS _ sdiff_subset))
        fun y _ => hM y
    -- Step 7: `Hⁿ(η_{x,ρ}(B ∖ A) ∩ B̄_R(0)) = Rⁿ Hⁿ((B ∖ A) ∩ B̄_{ρR}(x)) / (ρR)ⁿ → 0`, by (†)
    -- along `ρ ↦ ρR`
    have hlin : Tendsto (fun ρ : ℝ => ρ * R) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
        exact mul_pos hρ hRpos
    have hsmall : Tendsto (fun ρ : ℝ =>
        μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' (B \ A) ∩ closedBall 0 R))
        (𝓝[>] 0) (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (hdens.comp hlin)
        (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) :
          (0 : ℝ≥0∞) ≠ 0 ∨ ENNReal.ofReal R ^ n ≠ ∞)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
      have hβ : ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (pow_ne_zero n (ENNReal.ofReal_pos.2 hRpos).ne')
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      simp only [Function.comp_apply]
      rw [Submission.rsdic_tl_blowUp_measure_scaling P n x ρ R (B \ A) hρ,
        ENNReal.ofReal_mul hρ.le, mul_pow, ← ENNReal.inv_pow, div_eq_mul_inv,
        ENNReal.mul_inv (Or.inl (pow_ne_zero n (ENNReal.ofReal_pos.2 hρ).ne'))
          (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
      calc ENNReal.ofReal R ^ n * (μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹))
          = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R))) := by ring
        _ = (ENNReal.ofReal ρ ^ n)⁻¹ * μHE[n] ((B \ A) ∩ closedBall x (ρ * R)) := by
          rw [hβ, one_mul]
    have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsmall).const_mul M
    rwa [ENNReal.toReal_zero, mul_zero] at h
  -- Step 8: transfer the limits of Definition 1.4 in both directions
  constructor
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).sub (key f)
    rw [sub_zero] at h
    exact h.congr fun ρ => sub_sub_cancel _ _
  · rintro ⟨hdim, hconv⟩
    refine ⟨hdim, fun f => ?_⟩
    have h := (hconv f).add (key f)
    rw [add_zero] at h
    exact h.congr fun ρ => add_sub_cancel _ _
/-- **Simon Ch. 3, Remark 1.5(3)**: if `D` has an approximate tangent space at `x` and
`Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, then `Hⁿ(D ∩ B̄_ρ(x)) ≤ Cρⁿ` for all small `ρ > 0`.  Test the tangent
condition with `f = max(0, min(1, 2 − |y|)) ∈ C_c`: for `ρ ≤ r₀/2`, `f` is integrable on
`η_{x,ρ}(D)` (as `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿHⁿ(D ∩ B̄_{r₀}(x)) < ∞`), and
`ρ⁻ⁿHⁿ(D ∩ B̄_ρ(x)) ≤ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ → ∫_Q f dHⁿ =: L`, so
`C = L + 1` works. -/
theorem Submission.rsdic_measure_closedBall_le_of_tangent : ∀ (P n : ℕ) (D : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (r₀ : ℝ), MeasurableSet D → 0 < r₀ → μHE[n] (D ∩ closedBall x r₀) ≠ ∞ → HasApproximateTangentSpaceAt n D x Q → ∃ C r₁ : ℝ, 0 < r₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (D ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n) := by
  intro P n D x Q r₀ _ hr₀ hfin hT
  -- Step 1 (scaling): `Hⁿ(a + c • W) = |c|ⁿ Hⁿ(W)`, by translation invariance and homogeneity
  have hscale : ∀ (a : Euclid P) (c : ℝ), c ≠ 0 → ∀ W : Set (Euclid P),
      μHE[n] ((fun t => a + c • t) '' W) = ‖c‖₊ ^ n • μHE[n] W := by
    intro a c hc W
    have himg : (fun t => a + t) '' ((fun t => c • t) '' W) = (fun t => a + c • t) '' W :=
      Set.image_image _ _ _
    have hsm := Measure.euclideanHausdorffMeasure_smul₀ (E := Euclid P) n hc W
    rw [← Set.image_smul] at hsm
    rw [← himg, (isometry_add_left a).euclideanHausdorffMeasure_image, hsm]
  -- Step 2: the test function `f = max(0, min(1, 2 − |y|)) ∈ C_c`, `1_{B̄₁(0)} ≤ f ≤ 1_{B̄₂(0)}`
  have hout : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) 2 → max 0 (min 1 (2 - ‖y‖)) = 0 := by
    intro y hy
    rw [mem_closedBall_zero_iff, not_le] at hy
    exact max_eq_left ((min_le_right _ _).trans (by linarith))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
    ⟨⟨fun y => max 0 (min 1 (2 - ‖y‖)), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall 0 2) hout⟩
  have hf0 : ∀ y, 0 ≤ f y := fun y => le_max_left _ _
  have hf1 : ∀ y, f y ≤ 1 := fun y => max_le zero_le_one (min_le_left _ _)
  have hfB : ∀ y ∈ closedBall (0 : Euclid P) 1, f y = 1 := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    show max 0 (min 1 (2 - ‖y‖)) = 1
    rw [min_eq_left (by linarith), max_eq_right zero_le_one]
  -- Step 5: choose `r₁` with `∫_{η_{x,ρ}(D)} f dHⁿ < L + 1` and `ρ < r₀/2` for `0 < ρ < r₁`
  set L := ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n]
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D, f y ∂μHE[n]) < L + 1 ∧
        ρ < r₀ / 2 :=
    ((hT.2 f).eventually_lt_const (lt_add_one L)).and
      (Filter.mem_of_superset (Ioo_mem_nhdsGT (half_pos hr₀)) fun ρ hρ => hρ.2)
  obtain ⟨r₁, hr₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨L + 1, r₁, hr₁, fun ρ hρ hρr₁ => ?_⟩
  obtain ⟨hg, hρr₀⟩ := hsub ⟨hρ, hρr₁⟩
  set T := Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' D
  have hnorm : ∀ d : Euclid P, ‖d - x‖ = ρ * ‖ρ⁻¹ • (d - x)‖ := by
    intro d
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hρ.le, mul_inv_cancel_left₀ hρ.ne']
  -- Step 3: `Hⁿ(η_{x,ρ}(D) ∩ B̄₂(0)) ≤ ρ⁻ⁿ Hⁿ(D ∩ B̄_{r₀}(x)) < ∞`, so `f` is integrable on
  -- `η_{x,ρ}(D)`
  have hTfin : μHE[n] (T ∩ closedBall 0 2) ≠ ∞ := by
    have hsubset : T ∩ closedBall 0 2 ⊆
        (fun t => -(ρ⁻¹ • x) + ρ⁻¹ • t) '' (D ∩ closedBall x r₀) := by
      rintro _ ⟨⟨d, hd, rfl⟩, hd2⟩
      refine ⟨d, ⟨hd, ?_⟩, ?_⟩
      · rw [mem_closedBall_zero_iff] at hd2
        rw [mem_closedBall, dist_eq_norm, hnorm d]
        have : ρ * ‖ρ⁻¹ • (d - x)‖ ≤ ρ * 2 := mul_le_mul_of_nonneg_left hd2 hρ.le
        linarith
      · simp only [Poincare.SimonGMT.Chapter03.blowUpMap, smul_sub]
        abel
    refine ne_top_of_le_ne_top ?_ (measure_mono hsubset)
    rw [hscale _ _ (inv_ne_zero hρ.ne'), ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin
  have hint : Integrable (fun y => f y) (μHE[n].restrict T) := by
    refine Integrable.mono' (g := (closedBall (0 : Euclid P) 2).indicator fun _ => (1 : ℝ)) ?_
      f.continuous.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    · rw [integrable_indicator_iff measurableSet_closedBall]
      refine integrableOn_const ?_
      rw [Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      exact hTfin
    · by_cases hy : y ∈ closedBall (0 : Euclid P) 2
      · rw [Set.indicator_of_mem hy, Real.norm_of_nonneg (hf0 y)]
        exact hf1 y
      · rw [Set.indicator_of_notMem hy, norm_le_zero_iff]
        exact hout y hy
  -- Step 4: `D ∩ B̄_ρ(x) ⊆ x + ρ • (η_{x,ρ}(D) ∩ B̄₁(0))` and
  -- `Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ ∫_{η_{x,ρ}(D)} f dHⁿ < L + 1`
  have hsub1 : D ∩ closedBall x ρ ⊆ (fun t => x + ρ • t) '' (T ∩ closedBall 0 1) := by
    rintro d ⟨hd, hdx⟩
    refine ⟨ρ⁻¹ • (d - x), ⟨⟨d, hd, rfl⟩, ?_⟩, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, hnorm d] at hdx
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      have : ρ * 1 < ρ * ‖ρ⁻¹ • (d - x)‖ := mul_lt_mul_of_pos_left hlt hρ
      linarith
    · simp only [smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hball : μHE[n] (T ∩ closedBall 0 1) ≤ ENNReal.ofReal (L + 1) :=
    calc μHE[n] (T ∩ closedBall 0 1)
        = ∫⁻ y, (closedBall (0 : Euclid P) 1).indicator 1 y ∂(μHE[n].restrict T) := by
          rw [lintegral_indicator_one measurableSet_closedBall,
            Measure.restrict_apply measurableSet_closedBall, Set.inter_comm]
      _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(μHE[n].restrict T) := by
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ closedBall (0 : Euclid P) 1
          · rw [Set.indicator_of_mem hy, hfB y hy, Pi.one_apply, ENNReal.ofReal_one]
          · rw [Set.indicator_of_notMem hy]
            exact zero_le
      _ = ENNReal.ofReal (∫ y, f y ∂(μHE[n].restrict T)) :=
          (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf0)).symm
      _ ≤ ENNReal.ofReal (L + 1) := ENNReal.ofReal_le_ofReal hg.le
  -- Step 6: `Hⁿ(D ∩ B̄_ρ(x)) ≤ ρⁿ Hⁿ(η_{x,ρ}(D) ∩ B̄₁(0)) ≤ (L + 1)ρⁿ`
  calc μHE[n] (D ∩ closedBall x ρ)
      ≤ μHE[n] ((fun t => x + ρ • t) '' (T ∩ closedBall 0 1)) := measure_mono hsub1
    _ = ‖ρ‖₊ ^ n • μHE[n] (T ∩ closedBall 0 1) := hscale _ _ hρ.ne' _
    _ ≤ ‖ρ‖₊ ^ n • ENNReal.ofReal (L + 1) := by
        rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left hball zero_le
    _ = ENNReal.ofReal ((L + 1) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul' (pow_nonneg hρ.le n), ENNReal.ofReal_pow hρ.le, ENNReal.smul_def,
          smul_eq_mul, mul_comm, ENNReal.coe_pow, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hρ.le]

/-- **Simon Ch. 3, Remarks 1.5(2) and 1.8(1)**: if `A ⊆ B ⊆ U` are Borel and `Hⁿ(B ∩ K) < ∞` for
compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same approximate tangent spaces
at `x`.  Off a `Hⁿ⌞A`-null set independent of `Q`, `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) ≤ ε Hⁿ(B ∩ B̄_ρ(x))` for
small `ρ` (Besicovitch).  A tangent plane of `B` or of `A` at `x` gives
`Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` (Remark 1.5(3), using `A ⊆ B` in the first case), hence
`Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, and then the blow-up integrals of `B` and `A` have the same
limits. -/
theorem Submission.rsdic_ae_tangent_iff_of_subset : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–4: for `Hⁿ⌞A`-a.e. `x`, `x ∈ A` and the excess of `B` over `A` near `x` is eventually
  -- small relative to `Hⁿ(B ∩ B̄_ρ(x))`; the exceptional set does not depend on `Q`
  filter_upwards [Submission.rsdic_tl_ae_excess_le P n U A B hU hA hB hAB hBU hfin,
    ae_restrict_mem hA] with x hexc hxA Q
  -- a compact ball `B̄_{s/2}(x) ⊆ B_s(x) ⊆ U`, so `Hⁿ(B ∩ B̄_{s/2}(x)) < ∞`
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x (hBU (hAB hxA))
  have hr₀ : 0 < s / 2 := half_pos hs
  have hBfin : μHE[n] (B ∩ closedBall x (s / 2)) ≠ ∞ :=
    hfin _ (isCompact_closedBall x (s / 2)) ((closedBall_subset_ball (half_lt_self hs)).trans hsU)
  have hAB' : ∀ ρ : ℝ, μHE[n] (A ∩ closedBall x ρ) ≤ μHE[n] (B ∩ closedBall x ρ) :=
    fun ρ => measure_mono (inter_subset_inter_left _ hAB)
  -- Steps 5–7: a growth bound `Hⁿ(A ∩ B̄_ρ(x)) ≤ Cρⁿ` gives `Hⁿ((B ∖ A) ∩ B̄_ρ(x)) = o(ρⁿ)`, which
  -- forces equal approximate tangent spaces
  have key : ∀ C r₁ : ℝ, 0 < r₁ →
      (∀ ρ : ℝ, 0 < ρ → ρ < r₁ → μHE[n] (A ∩ closedBall x ρ) ≤ ENNReal.ofReal (C * ρ ^ n)) →
      (HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q) :=
    fun C r₁ hr₁ hgrowth =>
      Submission.rsdic_tl_tangent_iff_of_density_zero P n A B x (s / 2) hA hB hAB hr₀ hBfin
        (Submission.rsdic_tl_excess_density_zero P n A B x (s / 2) C r₁ hr₀ hBfin hr₁ hgrowth hexc)
        Q
  constructor
  · -- the growth bound for `B` passes to `A ⊆ B`
    intro hTB
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n B x Q (s / 2) hB hr₀ hBfin hTB
    exact (key C r₁ hr₁ fun ρ hρ hρr₁ => (hAB' ρ).trans (hgrowth ρ hρ hρr₁)).1 hTB
  · intro hTA
    obtain ⟨C, r₁, hr₁, hgrowth⟩ :=
      Submission.rsdic_measure_closedBall_le_of_tangent P n A x Q (s / 2) hA hr₀
        (ne_top_of_le_ne_top hBfin (hAB' (s / 2))) hTA
    exact (key C r₁ hr₁ hgrowth).2 hTA
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Evaluation on an orthonormal frame is bounded by the Euclidean coefficient norm** (Simon
Ch. 6, Remark 2.6(a); step 1(a) of the mass formula, Remark 6.3.2(3)): `|α(τ)| ≤ |α|_E` for every
`n`-covector `α` and orthonormal `τ₁, …, τₙ` in `ℝᴾ`.  Extend `τ` to an orthonormal basis `f` of
`ℝᴾ` with `f ∘ ι = τ`, `ι = Fin.castLE`.  For every permutation `π`,
`α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²`, and `π ↦ ι ∘ π` is injective, so
`n! α(τ)² ≤ Σ_j α(f ∘ j)² = n! |α|_E²` by `regcomp_covector_sq_sum_orthonormalBasis`. -/
theorem Submission.regcomp_covector_eval_orthonormal_le : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (τ : Fin n → Euclid P), Orthonormal ℝ τ → |α τ| ≤ covectorEuclideanNorm α := by
  intro P n α τ hτ
  classical
  -- Step 1: `n ≤ P`, and an orthonormal basis `f` of `ℝᴾ` with `f (ι k) = τ k`, `ι = Fin.castLE`
  have hnP : n ≤ P := by
    simpa [finrank_euclideanSpace_fin] using hτ.linearIndependent.fintype_card_le_finrank
  let ι : Fin n → Fin P := Fin.castLE hnP
  have hι : Injective ι := Fin.castLE_injective hnP
  let v : Fin P → Euclid P := fun i => if h : (i : ℕ) < n then τ ⟨i, h⟩ else 0
  let s : Set (Fin P) := {i | (i : ℕ) < n}
  have hvs : Orthonormal ℝ (s.domRestrict v) := by
    let e : s → Fin n := fun i => ⟨i.1, i.2⟩
    have he : Injective e := fun a b hab =>
      Subtype.ext (Fin.ext (congrArg (Fin.val : Fin n → ℕ) hab))
    have hve : s.domRestrict v = τ ∘ e := by
      funext i
      have hi : ((i : Fin P) : ℕ) < n := i.2
      simp [v, e, hi]
    rw [hve]
    exact hτ.comp e he
  obtain ⟨f, hf⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) hvs
  have hfι : ∀ k, f (ι k) = τ k := by
    intro k
    rw [hf (ι k) k.2]
    simp [v, ι]
  -- Step 2: `α(f ∘ (ι ∘ π))² = α(τ ∘ π)² = α(τ)²` for every permutation `π`
  let Φ : Equiv.Perm (Fin n) → (Fin n → Fin P) := fun π => ι ∘ π
  have hΦ : Injective Φ := fun π π' h => Equiv.ext fun k => hι (congrFun h k)
  have hperm : ∀ π : Equiv.Perm (Fin n), α (fun k => f (Φ π k)) ^ 2 = α τ ^ 2 := by
    intro π
    have h1 : (fun k => f (Φ π k)) = τ ∘ π := funext fun k => hfι (π k)
    have h2 : α (τ ∘ π) = Equiv.Perm.sign π • α τ := α.toAlternatingMap.map_perm τ π
    rw [h1, h2]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  -- Step 3: `n! α(τ)² = Σ_π α(f ∘ (ι ∘ π))² ≤ Σ_j α(f ∘ j)²`, the terms being nonnegative
  have hle : (n.factorial : ℝ) * α τ ^ 2 ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
    calc (n.factorial : ℝ) * α τ ^ 2
        = ∑ j ∈ Finset.univ.image Φ, α (fun k => f (j k)) ^ 2 := by
          rw [Finset.sum_image fun π _ π' _ h => hΦ h]
          simp only [hperm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ j : Fin n → Fin P, α (fun k => f (j k)) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => sq_nonneg _
  -- Step 4: `Σ_j α(f ∘ j)² = n! |α|_E²` (`regcomp_covector_sq_sum_orthonormalBasis`); cancel `n!`
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis P n α f] at hle
  have hsq : α τ ^ 2 ≤ covectorEuclideanNorm α ^ 2 :=
    le_of_mul_le_mul_left hle (Nat.cast_pos.mpr n.factorial_pos)
  -- Step 5: `|α(τ)| ≤ |α|_E`, since `|α|_E ≥ 0`
  exact abs_le_of_sq_le_sq hsq (covectorEuclideanNorm_nonneg α)
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-- **`ξ` orients the approximate tangent space of every locally finite `C ⊇ B`, a.e. on
`B ⊆ M`** (Simon 6.3.1, chapter-06.txt lines 733–748, with Ch. 3, 1.4–1.6, chapter-03.txt
lines 77–144, where the proof of 1.6 shows `TₓM = TₓNⱼ` a.e. on `Mⱼ ⊆ Nⱼ` by the Upper Density
Theorem).  Let `R = (M, θ, ξ)` be an `IMRep` in `U`, and `B ⊆ M`, `B ⊆ C ⊆ U` Borel with `C`
locally `Hⁿ`-finite in `U`.  `M` is locally `Hⁿ`-finite in `U` since `θ ≥ 1` on `M`, so tangent
locality gives `TₓB = TₓM` and `TₓB = TₓC` for `Hⁿ`-a.e. `x ∈ B`; `ξ(x)` orients `TₓM` for
`Hⁿ`-a.e. `x ∈ M ⊇ B`. -/
theorem Submission.rsdic_imrep_ae_tangent_orient_of_subset : ∀ (P n : ℕ) (U B C : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet B → MeasurableSet C → B ⊆ R.carrier → B ⊆ C → C ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (C ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict B), ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n C x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
  intro P n U B C R hU hB hC hBM hBC hCU hCfin
  -- `M` is locally `Hⁿ`-finite in `U`: `Hⁿ(M ∩ K) = ∫_{M∩K} 1 dHⁿ ≤ ∫_{M∩K} θ dHⁿ < ∞`
  have hMfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    exact (setLIntegral_one _).symm.trans_le
      (setLIntegral_mono' (R.measurableSet_carrier.inter hK.measurableSet)
        fun x hx => Nat.one_le_cast.2 (R.mult_pos x hx.1))
  -- `TₓM = TₓB` and `TₓC = TₓB` for `Hⁿ`-a.e. `x ∈ B` (tangent locality for `B ⊆ M`, `B ⊆ C`)
  have hM := Submission.rsdic_ae_tangent_iff_of_subset P n U B R.carrier hU hB
    R.measurableSet_carrier hBM R.carrier_subset hMfin
  have hC' := Submission.rsdic_ae_tangent_iff_of_subset P n U B C hU hB hC hBC hCU hCfin
  -- `ξ(x)` orients `TₓM` for `Hⁿ`-a.e. `x ∈ M`, hence for `Hⁿ`-a.e. `x ∈ B`
  filter_upwards [hM, hC', ae_restrict_of_ae_restrict_of_subset hBM R.orients]
    with x hxM hxC ⟨Q, hQ, hξ⟩
  exact ⟨Q, (hxC Q).2 ((hxM Q).1 hQ), hξ⟩
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

/-- **Simon 6.3.2(1)**, agreement on the overlap (step 3 of the proof that `p₁T₁ + p₂T₂` is
integer multiplicity).  Let `R₁ = (M₁, θ₁, ξ₁)` and `R₂ = (M₂, θ₂, ξ₂)` be integer multiplicity
triples in the open set `U`.  `M₂` is Borel and locally `Hⁿ`-finite in `U`:
`Hⁿ(M₂ ∩ K) ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞` for compact `K ⊆ U`, as `θ₂ ≥ 1` on `M₂`.  So for `Hⁿ`-a.e.
`x ∈ M₁ ∩ M₂` both `ξ₁(x)` (tangent transfer from `M₁` to `M₂ ⊇ M₁ ∩ M₂`) and `ξ₂(x)` orient
`TₓM₂`, which is unique (Ch. 3, Remark 1.5(1)); two unit orientations of one subspace agree up
to sign. -/
theorem Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n), IsOpen U → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∩ R₂.carrier)), R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
  intro P n U R₁ R₂ hU
  -- `M₂` is locally `Hⁿ`-finite in `U`: `Hⁿ(M₂ ∩ K) = ∫_{M₂ ∩ K} 1 dHⁿ ≤ ∫_{M₂ ∩ K} θ₂ dHⁿ < ∞`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R₂.carrier ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (R₂.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono' (R₂.measurableSet_carrier.inter hK.measurableSet) fun x hx =>
      Nat.one_le_cast.2 (R₂.mult_pos x hx.1)
  -- a.e. on `M₁ ∩ M₂`, `ξ₁` orients `TₓM₂` (tangent transfer with `B = M₁ ∩ M₂`, `C = M₂`) ...
  have h₁ := Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (R₁.carrier ∩ R₂.carrier)
    R₂.carrier R₁ hU (R₁.measurableSet_carrier.inter R₂.measurableSet_carrier)
    R₂.measurableSet_carrier inter_subset_left inter_subset_right R₂.carrier_subset hfin
  -- ... and so does `ξ₂`, as `R₂.orients` holds a.e. on `M₂ ⊇ M₁ ∩ M₂`
  have h₂ := ae_restrict_of_ae_restrict_of_subset
    (inter_subset_right : R₁.carrier ∩ R₂.carrier ⊆ R₂.carrier) R₂.orients
  filter_upwards [h₁, h₂] with x ⟨Q₁, hT₁, hξ₁⟩ ⟨Q₂, hT₂, hξ₂⟩
  -- `TₓM₂` is unique, and two unit orientations of one subspace agree up to sign
  rw [hT₁.unique hT₂] at hξ₁
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P n (R₁.orient x) (R₂.orient x) Q₂ hξ₁ hξ₂

/-- **Simon Ch. 6, Remark 3.2(1)** (the construction step): for IMReps `R₁ = (M₁, θ₁, ξ₁)`,
`R₂ = (M₂, θ₂, ξ₂)` in an open `U` and `p₁, p₂ ∈ ℤ` there is an IMRep `R = (M', θ', ξ')` in `U`
with `1_{M'} θ' ξ' = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` `Hⁿ`-a.e.  Take Borel versions `η₁, η₂`
of the orientations and the Borel sign `σ = ±1` according as `η₂ = η₁` or not; as `ξ₂ = ±ξ₁`
a.e. on `M₁ ∩ M₂`, `η₂ = σ η₁` there.  With `c = p₁ θ₁ 1_{M₁} + p₂ θ₂ (σ 1_{M₁ ∩ M₂} + 1_{M₂ \ M₁})`
and `ζ = η₁` on `M₁`, `ζ = η₂` off `M₁`, put `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`, `θ' = |c|`,
`ξ' = sgn(c) ζ`.  Then `1_{M'} θ' ξ' = c ζ` is the combination a.e., `|c| ≤ |p₁| θ₁ 1_{M₁} +
|p₂| θ₂ 1_{M₂}` gives local integrability, and `ξ' = ±ξᵢ` orients `T_x M'` a.e. on `M' ∩ M₁`
(`i = 1`) and on `M' \ M₁ ⊆ M₂` (`i = 2`). -/
theorem Submission.rsdic_exists_imrep_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (R₁ R₂ : IMRep U n) (p₁ p₂ : ℤ), IsOpen U → ∃ R : IMRep U n, ∀ᵐ x ∂μHE[n], R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x = (p₁ : ℝ) • R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x + (p₂ : ℝ) • R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U R₁ R₂ p₁ p₂ hU
  classical
  have hM₁ := R₁.measurableSet_carrier
  have hM₂ := R₂.measurableSet_carrier
  -- Step 1: Borel versions `η₁, η₂` of the orientations, equal to them a.e. on the carriers
  obtain ⟨η₁, hη₁, hη₁e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → R₁.orient x = η x :=
    ⟨_, R₁.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₁).mp R₁.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨η₂, hη₂, hη₂e⟩ : ∃ η : Euclid P → MultiVector P n, StronglyMeasurable η ∧
      ∀ᵐ x ∂μHE[n], x ∈ R₂.carrier → R₂.orient x = η x :=
    ⟨_, R₂.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      (ae_restrict_iff' hM₂).mp R₂.aestronglyMeasurable_orient.ae_eq_mk⟩
  -- Step 2: `ξ₂ = ±ξ₁` a.e. on `M₁ ∩ M₂`
  have hpm : ∀ᵐ x ∂μHE[n], x ∈ R₁.carrier → x ∈ R₂.carrier →
      R₂.orient x = R₁.orient x ∨ R₂.orient x = -R₁.orient x := by
    filter_upwards [(ae_restrict_iff' (hM₁.inter hM₂)).mp
      (Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n U R₁ R₂ hU)] with x hx h₁ h₂
    exact hx ⟨h₁, h₂⟩
  -- Step 3: the coefficient `c` (with the Borel sign `σ`) and the orientation field `ζ`
  have hE : MeasurableSet {x | η₂ x = η₁ x} := by
    -- `Λₙ(ℝᴾ)` carries the strong operator topology; it is the topology of the operator norm
    have : TopologicalSpace.MetrizableSpace (MultiVector P n) :=
      { toPseudoMetrizableSpace := ⟨⟨PseudoMetricSpace.toUniformSpace, rfl,
          Metric.uniformity_basis_dist_inv_nat_succ.isCountablyGenerated⟩⟩
        toT0Space := inferInstance }
    exact hη₂.measurableSet_eq_fun hη₁
  obtain ⟨c, hc⟩ : ∃ c : Euclid P → ℤ, c = fun x =>
      (if x ∈ R₁.carrier then p₁ * R₁.mult x else 0) +
        (if x ∈ R₂.carrier then
          (if x ∈ R₁.carrier then (if η₂ x = η₁ x then 1 else -1) else 1) * (p₂ * R₂.mult x)
        else 0) := ⟨_, rfl⟩
  have hc_meas : Measurable c := by
    have hθ₁ : Measurable fun x => (R₁.mult x : ℤ) := measurable_from_nat.comp R₁.measurable_mult
    have hθ₂ : Measurable fun x => (R₂.mult x : ℤ) := measurable_from_nat.comp R₂.measurable_mult
    rw [hc]
    exact (Measurable.ite hM₁ (measurable_const.mul hθ₁) measurable_const).add
      (Measurable.ite hM₂ ((Measurable.ite hM₁ (Measurable.ite hE measurable_const measurable_const)
        measurable_const).mul (measurable_const.mul hθ₂)) measurable_const)
  have hc_off : ∀ x, x ∉ R₁.carrier → x ∉ R₂.carrier → c x = 0 := by
    intro x h₁ h₂
    simp [hc, h₁, h₂]
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid P → MultiVector P n,
      ζ = fun x => if x ∈ R₁.carrier then η₁ x else η₂ x := ⟨_, rfl⟩
  have hζ_meas : StronglyMeasurable ζ := by
    rw [hζ]
    exact StronglyMeasurable.ite hM₁ hη₁ hη₂
  have hζ₁ : ∀ x, x ∈ R₁.carrier → ζ x = η₁ x := fun x hx => by simp [hζ, hx]
  have hζ₂ : ∀ x, x ∉ R₁.carrier → ζ x = η₂ x := fun x hx => by simp [hζ, hx]
  -- the new carrier `M' = (M₁ ∪ M₂) ∩ {c ≠ 0}`
  obtain ⟨M', hM'⟩ : ∃ M' : Set (Euclid P),
      M' = (R₁.carrier ∪ R₂.carrier) ∩ {x | c x ≠ 0} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ M' ↔ (x ∈ R₁.carrier ∨ x ∈ R₂.carrier) ∧ c x ≠ 0 := by
    intro x
    rw [hM']
    rfl
  have hM'meas : MeasurableSet M' := by
    rw [hM']
    exact (hM₁.union hM₂).inter (hc_meas (measurableSet_singleton 0).compl)
  have hM'U : M' ⊆ U := fun x hx =>
    ((hmem x).mp hx).1.elim (fun h => R₁.carrier_subset h) fun h => R₂.carrier_subset h
  -- Step 5: `1_{M'} |c| sgn(c) ζ = c ζ` everywhere
  have hind : ∀ x, M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x =
      (c x : ℝ) • ζ x := by
    intro x
    by_cases hx : x ∈ M'
    · rw [indicator_of_mem hx, smul_smul]
      congr 1
      have h : (((c x).sign * ((c x).natAbs : ℤ) : ℤ) : ℝ) = (c x : ℝ) := by
        rw [Int.sign_mul_natAbs]
      rw [Int.cast_mul, Int.cast_natCast] at h
      rw [mul_comm]
      exact h
    · rw [indicator_of_notMem hx]
      have hc0 : c x = 0 := by
        by_contra hcx
        by_cases hA : x ∈ R₁.carrier ∨ x ∈ R₂.carrier
        · exact hx ((hmem x).mpr ⟨hA, hcx⟩)
        · exact hcx (hc_off x (fun h => hA (Or.inl h)) fun h => hA (Or.inr h))
      rw [hc0, Int.cast_zero, zero_smul]
  -- Step 6 (d): `|c| ≤ |p₁| θ₁ 1_{M₁} + |p₂| θ₂ 1_{M₂}`, so `θ' = |c|` is locally integrable
  have hθ₁e : Measurable fun x => (R₁.mult x : ℝ≥0∞) := measurable_from_nat.comp R₁.measurable_mult
  have hθ₂e : Measurable fun x => (R₂.mult x : ℝ≥0∞) := measurable_from_nat.comp R₂.measurable_mult
  have hbound : ∀ x, ((c x).natAbs : ℝ≥0∞) ≤
      (p₁.natAbs : ℝ≥0∞) * R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x +
        (p₂.natAbs : ℝ≥0∞) * R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x := by
    intro x
    have key : (c x).natAbs ≤ p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
        p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) := by
      rw [hc]
      refine (Int.natAbs_add_le _ _).trans (add_le_add ?_ ?_)
      · split_ifs <;> simp [Int.natAbs_mul]
      · split_ifs <;> simp [Int.natAbs_mul]
    calc ((c x).natAbs : ℝ≥0∞)
        ≤ ((p₁.natAbs * (if x ∈ R₁.carrier then R₁.mult x else 0) +
            p₂.natAbs * (if x ∈ R₂.carrier then R₂.mult x else 0) : ℕ) : ℝ≥0∞) := by
          exact_mod_cast key
      _ = _ := by
          by_cases h₁ : x ∈ R₁.carrier <;> by_cases h₂ : x ∈ R₂.carrier <;> simp [h₁, h₂]
  have hlocint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in M' ∩ K, ((c x).natAbs : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (b := ∫⁻ x in K, ((p₁.natAbs : ℝ≥0∞) *
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ≥0∞)) x + (p₂.natAbs : ℝ≥0∞) *
        R₂.carrier.indicator (fun y => (R₂.mult y : ℝ≥0∞)) x) ∂μHE[n]) ?_
      ((lintegral_mono hbound).trans (lintegral_mono_set inter_subset_right))
    rw [lintegral_add_left ((hθ₁e.indicator hM₁).const_mul _),
      lintegral_const_mul _ (hθ₁e.indicator hM₁), lintegral_const_mul _ (hθ₂e.indicator hM₂),
      lintegral_indicator hM₁, lintegral_indicator hM₂, Measure.restrict_restrict hM₁,
      Measure.restrict_restrict hM₂]
    exact ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₁.locallyIntegrable_mult K hK hKU),
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (R₂.locallyIntegrable_mult K hK hKU)⟩
  -- Step 6 (f): `Hⁿ(M' ∩ K) ≤ Hⁿ(M₁ ∩ K) + Hⁿ(M₂ ∩ K) < ∞`, as `θᵢ ≥ 1` on `Mᵢ`
  have hfinR : ∀ (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U →
      μHE[n] (R.carrier ∩ K) ≠ ∞ := by
    intro R K hK hKU
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    rw [← setLIntegral_one]
    exact setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) fun x hx =>
      Nat.one_le_cast.mpr (R.mult_pos x hx.1)
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞ := by
    intro K hK hKU
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hfinR R₁ K hK hKU, hfinR R₂ K hK hKU⟩)
      ((measure_mono ?_).trans (measure_union_le _ _))
    rintro x ⟨hx, hxK⟩
    exact ((hmem x).mp hx).1.elim (fun h => Or.inl ⟨h, hxK⟩) fun h => Or.inr ⟨h, hxK⟩
  -- `sgn(c) ξ` is a unit orientation of `Q` when `c ≠ 0` and `ξ` is one
  have hsign : ∀ (k : ℤ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), k ≠ 0 →
      IsUnitOrientationOf ξ Q → IsUnitOrientationOf ((k.sign : ℝ) • ξ) Q := by
    rintro k ξ Q hk ⟨τ, hτ, hspan, hξ⟩
    refine ⟨τ, hτ, hspan, ?_⟩
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [Int.sign_eq_neg_one_of_neg hk]
      rcases hξ with h | h
      · exact Or.inr fun α => by simp [h α]
      · exact Or.inl fun α => by simp [h α]
    · rw [Int.sign_eq_one_of_pos hk]
      simpa using hξ
  -- Step 6 (f): the orientation condition, separately on `M' ∩ M₁` and on `M' \ M₁ ⊆ M₂`
  have horient : ∀ᵐ x ∂(μHE[n].restrict M'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n M' x Q ∧
        IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
    have h₁ : ∀ᵐ x ∂(μHE[n].restrict (M' ∩ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' ∩ R₁.carrier)
          M' R₁ hU (hM'meas.inter hM₁) hM'meas inter_subset_right inter_subset_left hM'U hfin,
        ae_restrict_mem (hM'meas.inter hM₁), ae_restrict_of_ae hη₁e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₁ x hxB.2, ← hxη hxB.2]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h₂ : ∀ᵐ x ∂(μHE[n].restrict (M' \ R₁.carrier)), ∃ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M' x Q ∧
          IsUnitOrientationOf (((c x).sign : ℝ) • ζ x) Q := by
      have hsub : M' \ R₁.carrier ⊆ R₂.carrier := fun x hx =>
        ((hmem x).mp hx.1).1.resolve_left hx.2
      filter_upwards [Submission.rsdic_imrep_ae_tangent_orient_of_subset P n U (M' \ R₁.carrier)
          M' R₂ hU (hM'meas.diff hM₁) hM'meas hsub Set.sdiff_subset hM'U hfin,
        ae_restrict_mem (hM'meas.diff hM₁), ae_restrict_of_ae hη₂e] with x hx hxB hxη
      obtain ⟨Q, hQ, hξQ⟩ := hx
      refine ⟨Q, hQ, ?_⟩
      rw [hζ₂ x hxB.2, ← hxη (hsub hxB)]
      exact hsign (c x) _ Q ((hmem x).mp hxB.1).2 hξQ
    have h := (ae_restrict_union_iff (M' ∩ R₁.carrier) (M' \ R₁.carrier) _).mpr ⟨h₁, h₂⟩
    rwa [Set.inter_union_sdiff] at h
  -- Step 6: `R = (M', |c|, sgn(c) ζ)` is an IMRep in `U`
  refine ⟨{ carrier := M'
            mult := fun x => (c x).natAbs
            orient := fun x => ((c x).sign : ℝ) • ζ x
            measurableSet_carrier := hM'meas
            carrier_subset := hM'U
            rectifiable := ?_
            measurable_mult := (measurable_of_countable Int.natAbs).comp hc_meas
            mult_pos := fun x hx => Int.natAbs_pos.mpr ((hmem x).mp hx).2
            locallyIntegrable_mult := hlocint
            aestronglyMeasurable_orient :=
              (((measurable_of_countable fun k : ℤ => (k.sign : ℝ)).comp
                hc_meas).stronglyMeasurable.smul hζ_meas).aestronglyMeasurable
            orients := horient }, ?_⟩
  · -- `M' ⊆ M₁ ∪ M₂ ⊆ ⋃ᵢ (M₁, M₂, M₂, …)ᵢ`
    refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_iUnion
      (fun i : ℕ => if i = 0 then R₁.carrier else R₂.carrier) fun i => ?_).mono ?_
    · split_ifs
      exacts [R₁.rectifiable, R₂.rectifiable]
    · intro x hx
      rcases ((hmem x).mp hx).1 with h | h
      · exact mem_iUnion.mpr ⟨0, by simpa using h⟩
      · exact mem_iUnion.mpr ⟨1, by simpa using h⟩
  -- Steps 4 and 7: `c ζ = p₁ 1_{M₁} θ₁ ξ₁ + p₂ 1_{M₂} θ₂ ξ₂` wherever `ηᵢ = ξᵢ` on `Mᵢ` and
  -- `ξ₂ = ±ξ₁` on `M₁ ∩ M₂`, i.e. `Hⁿ`-a.e.
  filter_upwards [hη₁e, hη₂e, hpm] with x hx₁e hx₂e hx₁₂
  show M'.indicator (fun y => ((c y).natAbs : ℝ) • (((c y).sign : ℝ) • ζ y)) x = _
  rw [hind x]
  by_cases hx₁ : x ∈ R₁.carrier <;> by_cases hx₂ : x ∈ R₂.carrier
  · rw [indicator_of_mem hx₁, indicator_of_mem hx₂, hx₁e hx₁, hx₂e hx₂, hζ₁ x hx₁]
    by_cases hxE : η₂ x = η₁ x
    · have hcx : c x = p₁ * R₁.mult x + p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE]
      rw [hcx, hxE]
      push_cast
      module
    · have hcx : c x = p₁ * R₁.mult x - p₂ * R₂.mult x := by
        simp [hc, hx₁, hx₂, hxE, sub_eq_add_neg]
      have hneg : η₂ x = -η₁ x := by
        rcases hx₁₂ hx₁ hx₂ with h | h
        · exact absurd (by rw [← hx₂e hx₂, h, hx₁e hx₁]) hxE
        · rw [← hx₂e hx₂, h, hx₁e hx₁]
      rw [hcx, hneg]
      push_cast
      module
  · rw [indicator_of_mem hx₁, indicator_of_notMem hx₂, hx₁e hx₁, hζ₁ x hx₁]
    have hcx : c x = p₁ * R₁.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_mem hx₂, hx₂e hx₂, hζ₂ x hx₁]
    have hcx : c x = p₂ * R₂.mult x := by simp [hc, hx₁, hx₂]
    rw [hcx]
    push_cast
    module
  · rw [indicator_of_notMem hx₁, indicator_of_notMem hx₂, hc_off x hx₁ hx₂, smul_zero,
      smul_zero, add_zero, Int.cast_zero, zero_smul]
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

/-- **Simon Ch. 6, Remark 3.2(1)**: if `T₁, T₂ ∈ 𝒟ₙ(U)` are integer multiplicity and
`p₁, p₂ ∈ ℤ`, then `S = p₁T₁ + p₂T₂` is integer multiplicity.  Write `Tᵢ = τ(Mᵢ, θᵢ, ξᵢ)`.  The
orientations agree up to sign `Hⁿ`-a.e. on `M₁ ∩ M₂`, which gives a triple `(M', θ', ξ')` in `U`
with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` `Hⁿ`-a.e.; integrating `⟨ω, ·⟩` for
`ω ∈ 𝒟ⁿ(U)` then gives `S = τ(M', θ', ξ')`. -/
theorem Submission.rsd_isIntegerMultiplicity_int_combination : ∀ (P n : ℕ) (U : Set (Euclid P)) (T₁ T₂ S : GeometricCurrentOn U n) (p₁ p₂ : ℤ), IsOpen U → IsIntegerMultiplicity T₁ → IsIntegerMultiplicity T₂ → (∀ ω : TestFormOn U n, S ω = (p₁ : ℝ) * T₁ ω + (p₂ : ℝ) * T₂ ω) → IsIntegerMultiplicity S := by
  intro P n U T₁ T₂ S p₁ p₂ hU hT₁ hT₂ hS
  -- Representations `T₁ = τ(M₁, θ₁, ξ₁)` and `T₂ = τ(M₂, θ₂, ξ₂)`.
  obtain ⟨R₁, hR₁⟩ := hT₁
  obtain ⟨R₂, hR₂⟩ := hT₂
  -- A triple `R = (M', θ', ξ')` in `U` with `θ'ξ'1_{M'} = p₁θ₁ξ₁1_{M₁} + p₂θ₂ξ₂1_{M₂}` a.e.
  obtain ⟨R, hR⟩ := Submission.rsdic_exists_imrep_int_combination P n U R₁ R₂ p₁ p₂ hU
  -- Hence `τ(R)(ω) = p₁τ(R₁)(ω) + p₂τ(R₂)(ω) = p₁T₁(ω) + p₂T₂(ω) = S(ω)`.
  refine ⟨R, fun ω => ?_⟩
  rw [hS ω, hR₁ ω, hR₂ ω,
    Submission.rsdic_imrep_action_int_combination P n U R₁ R₂ R p₁ p₂ hR ω]

/-- **Integer multiplicity calculus** (Simon Ch. 3, Remark 1.5(2) and the proof of 1.6 "⇒";
Ch. 6, Remarks 2.6, 2.9 and 3.2(1)).
(a) Locality: for Borel `M ⊆ M' ⊆ U`, `M'` locally `Hⁿ`-finite in the open `U`, `TₓM = TₓM'` for
`Hⁿ`-a.e. `x ∈ M` (tangent locality with the two sides exchanged).
(b) Restriction: for an `IMRep` `R = (M, θ, ξ)` in the open `U` and Borel `E`, `(M ∩ E, θ, ξ)` is
an `IMRep`: `M` is locally `Hⁿ`-finite in `U` (`θ ≥ 1` on `M`), so (a) for `M ∩ E ⊆ M` transfers
`TₓM` to `Tₓ(M ∩ E)` a.e. on `M ∩ E`; it defines a current `τ(M ∩ E, θ, ξ)`.
(c) Differences: `A − B = 1 · A + (−1) · B` is an integer combination.
(d) Orientation bound: `Hⁿ`-a.e. on `M`, `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so
`|⟨α, ξ(x)⟩| = |α(τ)| ≤ |α|`. -/
theorem Submission.cmc_imRep_locality_restrict_sub : (∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) := by
  -- (a) tangent locality for `M ⊆ M'`, with the two sides of `↔` exchanged
  have ha : ∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M →
      MeasurableSet M' → M ⊆ M' → M' ⊆ U →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) →
      ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
    intro P n U M M' hU hM hM' hMM' hM'U hfin
    filter_upwards [Submission.rsdic_ae_tangent_iff_of_subset P n U M M' hU hM hM' hMM' hM'U
      hfin] with x hx Q
    exact (hx Q).symm
  refine ⟨ha, ?_, ?_, ?_⟩
  · -- (b) the restriction `(M ∩ E, θ, ξ)` of `R = (M, θ, ξ)`
    intro P n U R E hU hE
    have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
    -- `TₓM = Tₓ(M ∩ E)` a.e. on `M ∩ E`, `M` being locally `Hⁿ`-finite in `U`
    have htan : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ Q : Submodule ℝ (Euclid P),
        HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt n (R.carrier ∩ E) x Q := by
      filter_upwards [ha P n U (R.carrier ∩ E) R.carrier hU hME R.measurableSet_carrier
        inter_subset_left R.carrier_subset fun K hK hKU =>
          (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1] with x hx Q
      exact (hx Q).2
    obtain ⟨R', hcar, hmult, horient⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ E) R
      R.mult hME inter_subset_left R.measurable_mult (fun x hx => R.mult_pos x hx.1)
      (fun x _ => le_rfl) htan
    -- the current `τ(M ∩ E, θ, ξ)`
    obtain ⟨A, hA⟩ := Submission.dtc_imrep_current P n U R'
    exact ⟨A, R', hA, hcar, hmult, horient⟩
  · -- (c) `A − B = 1 · A + (−1) · B`
    intro P n U A B hU hA hB
    refine Submission.rsd_isIntegerMultiplicity_int_combination P n U A B (A - B) 1 (-1) hU hA hB
      fun ω => ?_
    show A ω - B ω = _
    push_cast
    ring
  · -- (d) `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, a.e. on `M`
    intro P n U R
    filter_upwards [R.orients] with x hx α
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    have hατ := Submission.regcomp_covector_eval_orthonormal_le P n α τ hτ
    rcases hξ with h | h
    · rw [h α]
      exact hατ
    · rw [h α, abs_neg]
      exact hατ

/-- **Face replacement** (Simon Ch. 6, proof of 5.1, displays (26)–(37); the BV facts on the
faces come from `cmcdt_cube_bv_median`).  Let `Q₀` be integer multiplicity, `n = m + 1`,
`spt Q₀ ⊆ K ∩ Lₙ`, `M(Q₀) ≤ Λ` and `M(∂Q₀) < ∞`.  Over the open unit `n`-faces `F̆`,
`Q₀ = Σ_F ũ_F [[F̆]]` with integer densities `ũ_F`, `Σ_F ∫|ũ_F| ≤ M(Q₀)`
(`cmcdtfr_skeleton_decomposition`); testing `∂Q₀` near `F̆` bounds the variation of `ũ_F` by
`V_F` with `Σ_F V_F ≤ M(∂Q₀)` (`cmcdtfr_boundary_variation`).  Integer medians `β_F` of the
`ũ_F` (`cmcdt_cube_bv_median`, constant `c_B`) give `Pc = Σ_F β_F [[F]]`, which lies in the
finite family of integer chains on faces meeting `K` with `Σ|β_F| ≤ 2Λ`
(`cmcdtfr_finite_family`).  Then `M(Q₀ − Pc)`, `M(∂(Q₀ − Pc)) ≤ c_B M(∂Q₀)`
(`cmcdtfr_face_integral_current`), so `M(∂Pc) ≤ (1 + c_B) M(∂Q₀)` as
`∂Pc = ∂Q₀ − ∂(Q₀ − Pc)`; `Pc` and `∂Pc` are integer multiplicity, `M(Pc) = Σ|β_F| ≤ 2M(Q₀)`,
and `Pc = 0` or `M(Pc) ≥ 1` (`cmcdtfr_polyhedral_im`, `cmcdtfr_chain_boundary`).  A face
carrying `Pc` meets `spt Q₀`, a face carrying `Q₀ − Pc` meets `spt ∂Q₀` (there `V_F ≠ 0`), and a
face has diameter `≤ √P` (`cmcdtfr_face_geometry`).  Take `c = max(2, 1 + c_B)`. -/
theorem Submission.cmcdt_face_replacement : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (K : Set (Euclid P)) (Λ : NNReal), IsCompact K → ∃ 𝒬₀ : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬₀.Finite ∧ ∀ Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → Q₀.mass ≤ Λ → Q₀.boundary.mass < ∞ → ∃ Pc ∈ 𝒬₀, IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity Pc.boundary ∧ (Pc = 0 ∨ 1 ≤ Pc.mass) ∧ Pc.mass ≤ c * Q₀.mass ∧ Pc.boundary.mass ≤ c * Q₀.boundary.mass ∧ (Q₀ - Pc).mass ≤ c * Q₀.boundary.mass ∧ Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support ∧ (Q₀ - Pc).support ∪ Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
  intro hVO hMR hIMC P m
  -- support and mass calculus for currents in `ℝᴾ`: `spt(A − B) ⊆ spt A ∪ spt B`,
  -- `spt ∂A ⊆ spt A` and `M(A − B) ≤ M(A) + M(B)`
  have hspt_sub : ∀ (k : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid P)) k),
      (A - B).support ⊆ A.support ∪ B.support := by
    intro k A B x hx
    simp only [GeometricCurrentOn.support, Set.mem_sdiff, mem_union, mem_univ, true_and] at hx ⊢
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hx
    obtain ⟨hA, hB⟩ := h
    simp only [GeometricCurrentOn.zeroRegion, mem_sUnion, mem_ofPred_eq] at hA hB ⊢
    obtain ⟨W₁, ⟨hW₁o, hW₁c, -, hW₁v⟩, hxW₁⟩ := hA
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hxW₂⟩ := hB
    refine ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
      hW₁c.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩, hxW₁, hxW₂⟩
    show A ω - B ω = 0
    rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
  have hspt_bd : ∀ (k : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid P)) (k + 1)),
      A.boundary.support ⊆ A.support := by
    intro k A x hx
    simp only [GeometricCurrentOn.support, Set.mem_sdiff] at hx ⊢
    refine ⟨hx.1, fun hxA => hx.2 ?_⟩
    simp only [GeometricCurrentOn.zeroRegion, mem_sUnion, mem_ofPred_eq] at hxA ⊢
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxA
    refine ⟨W, ⟨hWo, hWc, hWU, fun γ hγ => ?_⟩, hxW⟩
    exact hWv (exteriorDerivativeTestOn univ k γ)
      ((tsupport_exteriorDerivative_subset _).trans hγ)
  have hmass_sub : ∀ (k : ℕ) (A B : GeometricCurrentOn (univ : Set (Euclid P)) k),
      (A - B).mass ≤ A.mass + B.mass := by
    intro k A B
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    have hnω : -ω ∈ massAdmissibleOn (univ : Set (Euclid P)) k univ := by
      refine ⟨subset_univ _, fun x => ?_⟩
      have h := hω.2 x
      rwa [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by
          congr 1
          show A ω - B ω = A ω + B (-ω)
          rw [show B (-ω) = -B ω from map_neg B.toCurrent ω, sub_eq_add_neg]
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.mass + B.mass := add_le_add (A.le_massOn hω) (B.le_massOn hnω)
  -- `c_B` from the cube BV median lemma and `c := max(2, 1 + c_B)`
  obtain ⟨cB, hcB, hmedian⟩ := Submission.cmcdt_cube_bv_median m
  refine ⟨Real.toNNReal (max 2 (1 + cB)),
    Real.one_le_toNNReal.2 (le_max_of_le_left one_le_two), fun K Λ hK => ?_⟩
  -- `𝒬₀`: the integer chains `Σ β_F [[F]]` on faces meeting `K` with `Σ|β_F| ≤ 2Λ`
  refine ⟨_, Submission.cmcdtfr_finite_family P (m + 1) K (2 * (Λ : ℝ)) hK, ?_⟩
  intro Q₀ hQ₀ hQ₀K hQ₀L hQ₀Λ hQ₀b
  -- `Q₀ = Σ_F ũ_F [[F̆]]` over the open faces `F̆` meeting `spt Q₀`
  obtain ⟨s, u, hs, huZ, huI, hSu, huspt, hQ₀rep⟩ :=
    Submission.cmcdtfr_skeleton_decomposition hVO hMR hIMC P m K Q₀ hK hQ₀ hQ₀K hQ₀L
  -- the variations `V_F` of the `ũ_F`, with `Σ_F V_F ≤ M(∂Q₀)`
  obtain ⟨V, hV0, hSV, hVbd, hVspt⟩ :=
    Submission.cmcdtfr_boundary_variation hVO P m s u Q₀ hs huI hQ₀rep hQ₀b
  -- integer medians `β_F` (`β_F := 0` off `s`)
  have hmed : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), ∃ b : ℤ, p ∈ s →
      (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y - b| ≤ cB * V p) ∧
      |(b : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| ∧
      ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) →
        |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          (u p y - b) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ cB * V p := by
    intro p
    by_cases hp : p ∈ s
    · obtain ⟨b, hb⟩ := hmedian (u p) (V p) (huZ p hp) (huI p hp) (hVbd p hp)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose β hβ using hmed
  -- the face currents with densities `β_F` (this is `Pc`), `ũ_F` and `ũ_F − β_F`
  have hcube : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} = 1 :=
    (Submission.cmcdtfr_face_geometry P (m + 1)).1
  have hβI : ∀ p ∈ s, IntegrableOn (fun _ : Euclid (m + 1) => (β p : ℝ))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun p _ =>
    integrableOn_const (by rw [hcube]; exact ENNReal.one_ne_top)
  obtain ⟨hβω, ⟨Pc, hPc⟩, hPcD⟩ :=
    Submission.cmcdtfr_face_integral_current P m s (fun p _ => (β p : ℝ)) hs hβI
  obtain ⟨huω, -, -⟩ := Submission.cmcdtfr_face_integral_current P m s u hs huI
  obtain ⟨-, -, hdD⟩ := Submission.cmcdtfr_face_integral_current P m s
    (fun p y => u p y - (β p : ℝ)) hs fun p hp => (huI p hp).sub (hβI p hp)
  -- `Pc = Σ_F β_F [[F]]`
  have hPcrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Pc ω =
      ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro ω
    rw [hPc ω]
    exact Finset.sum_congr rfl fun p _ => integral_const_mul _ _
  -- `Q₀ − Pc = Σ_F (ũ_F − β_F) [[F̆]]`
  have hdrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), (Q₀ - Pc) ω =
      ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u p y - (β p : ℝ)) * (ω : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro ω
    show Q₀ ω - Pc ω = _
    rw [hQ₀rep ω, hPc ω, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← integral_sub (huω ω p hp) (hβω ω p hp)]
    congr 1
    ext y
    ring
  -- integrality of `Pc` and `∂Pc`, `M(Pc) = Σ|β_F|`, and `Pc = 0` or `M(Pc) ≥ 1`
  obtain ⟨hPcIM, hPcmass, hPc01⟩ :=
    Submission.cmcdtfr_polyhedral_im hMR P (m + 1) s β Pc hs hPcrep
  obtain ⟨s', β', hs', hPcbrep⟩ := Submission.cmcdtfr_chain_boundary P m s β Pc hs hPcrep
  obtain ⟨hPcbIM, -, -⟩ :=
    Submission.cmcdtfr_polyhedral_im hMR P m s' β' Pc.boundary hs' hPcbrep
  -- mass and support bounds for `Pc` and `Q₀ − Pc` from their face densities
  obtain ⟨-, -, hPcspt⟩ := hPcD Pc hPc
  obtain ⟨hdmass, hdbmass, hdspt⟩ := hdD (Q₀ - Pc) hdrep
  have hdb : (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, cB * V p) :=
    hdbmass (fun p => cB * V p) fun p hp G hG hG1 => (hβ p hp).2.2 G hG hG1
  -- `Σ|β_F| ≤ 2 Σ_F ∫|ũ_F| ≤ 2Λ`, `Σ_F ∫|ũ_F − β_F| ≤ c_B Σ_F V_F`
  have hβsum : ∑ p ∈ s, |(β p : ℝ)| ≤
      2 * ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hβ p hp).2.1
  have hSuΛ : ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y| ≤
      (Λ : ℝ) := by
    have h := hSu.trans hQ₀Λ
    rw [← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff Λ.coe_nonneg).1 h
  have hdsum : ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
      |u p y - (β p : ℝ)| ≤ cB * ∑ p ∈ s, V p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hβ p hp).1
  have hdb' : (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal cB * Q₀.boundary.mass := by
    calc (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, cB * V p) := hdb
      _ = ENNReal.ofReal cB * ENNReal.ofReal (∑ p ∈ s, V p) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_mul hcB.le]
      _ ≤ ENNReal.ofReal cB * Q₀.boundary.mass := mul_le_mul' le_rfl hSV
  -- `∂Pc = ∂Q₀ − ∂(Q₀ − Pc)`
  have hPcb_eq : Pc.boundary = Q₀.boundary - (Q₀ - Pc).boundary := by
    ext γ
    show Pc (exteriorDerivativeTestOn univ m γ) = Q₀ (exteriorDerivativeTestOn univ m γ) -
      (Q₀ (exteriorDerivativeTestOn univ m γ) - Pc (exteriorDerivativeTestOn univ m γ))
    ring
  -- supports: a face carrying `Pc` meets `spt Q₀`, a face carrying `Q₀ − Pc` meets `spt ∂Q₀`
  -- (there `V_F ≠ 0`), and a face has diameter `≤ √P`
  have hdiam := fun p (hp : p ∈ s) =>
    ((Submission.cmcdtfr_face_geometry P (m + 1)).2 p p (hs p hp) (hs p hp)).2.1
  have hPcsupp : Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support := by
    intro x hx
    obtain ⟨p, hp, -, y, hy, rfl⟩ := hPcspt x hx
    obtain ⟨y', hy', hy'Q⟩ := huspt p hp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  have hdsupp : (Q₀ - Pc).support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
    intro x hx
    obtain ⟨p, hp, hne, y, hy, rfl⟩ := hdspt x hx
    have hVp : V p ≠ 0 := by
      intro h0
      apply hne
      have h1 := (hβ p hp).1
      rw [h0, mul_zero] at h1
      exact le_antisymm h1 (integral_nonneg fun y => abs_nonneg _)
    obtain ⟨y', hy', hy'Q⟩ := hVspt p hp hVp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  have hPcbsupp : Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
    intro x hx
    rw [hPcb_eq] at hx
    rcases hspt_sub m _ _ hx with h | h
    · exact self_subset_cthickening _ h
    · exact hdsupp (hspt_bd m _ h)
  refine ⟨Pc, ?_, hPcIM, hPcbIM, hPc01, ?_, ?_, ?_, hPcsupp, union_subset hdsupp hPcbsupp⟩
  · -- `Pc ∈ 𝒬₀`
    rw [Set.mem_ofPred_eq]
    refine ⟨s, β, hs, fun p hp => ?_, by linarith, hPcrep⟩
    obtain ⟨y, hy, hyQ⟩ := huspt p hp
    exact ⟨y, hy, hQ₀K hyQ⟩
  · -- `M(Pc) = Σ|β_F| ≤ 2M(Q₀)`
    show Pc.mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.mass
    calc Pc.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := hPcmass
      _ ≤ ENNReal.ofReal (2 * _) := ENNReal.ofReal_le_ofReal hβsum
      _ = ENNReal.ofReal 2 * ENNReal.ofReal _ := ENNReal.ofReal_mul zero_le_two
      _ ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hSu
  · -- `M(∂Pc) ≤ M(∂Q₀) + M(∂(Q₀ − Pc)) ≤ (1 + c_B)M(∂Q₀)`
    show Pc.boundary.mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass
    calc Pc.boundary.mass ≤ Q₀.boundary.mass + (Q₀ - Pc).boundary.mass := by
          rw [hPcb_eq]
          exact hmass_sub m _ _
      _ ≤ Q₀.boundary.mass + ENNReal.ofReal cB * Q₀.boundary.mass := add_le_add le_rfl hdb'
      _ = ENNReal.ofReal (1 + cB) * Q₀.boundary.mass := by
          rw [ENNReal.ofReal_add zero_le_one hcB.le, ENNReal.ofReal_one, add_mul, one_mul]
      _ ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  · -- `M(Q₀ − Pc) ≤ Σ_F ∫|ũ_F − β_F| ≤ c_B M(∂Q₀)`
    show (Q₀ - Pc).mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass
    calc (Q₀ - Pc).mass ≤ ENNReal.ofReal _ := hdmass
      _ ≤ ENNReal.ofReal (cB * ∑ p ∈ s, V p) := ENNReal.ofReal_le_ofReal hdsum
      _ = ENNReal.ofReal cB * ENNReal.ofReal (∑ p ∈ s, V p) := ENNReal.ofReal_mul hcB.le
      _ ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [le_max_right 2 (1 + cB)])) hSV

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Smoothing a field `s` with `|s| ≤ 1` and `s = 0` off `Q_δ` by a nonnegative unit-mass `C^∞`
kernel `ρ` supported in `B_σ(0)`, `σ < δ`, gives a `C^∞` field `ρ ⋆ s` with `|ρ ⋆ s| ≤ 1` whose
topological support is compact and lies in `Q₁` (the mollification step of Simon Ch. 2, 2.5 and
2.7, as used in the proof of the deformation theorem, Ch. 6, 5.1).  The support of `ρ ⋆ s` lies
in the closed box `{δ − σ ≤ y_i ≤ 1 − δ + σ}`, which is compact and contained in `Q₁`. -/
theorem cmcdt_cbm_sa_smoothed_field : ∀ (m : ℕ) (δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ) (s : Euclid (m + 1) → Euclid (m + 1)), 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → AEStronglyMeasurable s volume → (∀ x, ‖s x‖ ≤ 1) → (∀ x, x ∉ {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} → s x = 0) → ContDiff ℝ (⊤ : ℕ∞) (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ HasCompactSupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ∧ tsupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∧ ∀ y, ‖convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume y‖ ≤ 1 := by
  intro m δ σ ρ s hσ hσδ hρ hρ0 hρ1 hρs hs hs1 hs0
  -- Step 1: `ρ` vanishes off `closedBall 0 σ`, so it has compact support and is integrable.
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => ?_
    by_contra h
    exact hx (ball_subset_closedBall (hρs h))
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  -- Step 2: `s` is measurable and bounded by `1`, hence integrable on compact sets.
  have hsl : LocallyIntegrable s volume := by
    rw [locallyIntegrable_iff]
    exact fun K hK => Measure.integrableOn_of_bounded hK.measure_lt_top.ne hs
      (Eventually.of_forall hs1)
  -- Step 3: `ρ` is `C^∞` with compact support and `s` is locally integrable, so `ρ ⋆ s` is `C^∞`.
  have hG : ContDiff ℝ (⊤ : ℕ∞) (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    hρc.contDiff_convolution_left _ hρ hsl
  -- Step 4: `‖ρ t • s (y − t)‖ ≤ ρ t` and `∫ ρ = 1`.
  have hbd : ∀ y, ‖convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume y‖ ≤ 1 := by
    intro y
    rw [convolution_def]
    refine (norm_integral_le_of_norm_le hρi (Eventually.of_forall fun t => ?_)).trans hρ1.le
    rw [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
    exact mul_le_of_le_one_right (hρ0 t) (hs1 _)
  -- Step 5: `support (ρ ⋆ s) ⊆ support s + support ρ ⊆ Q_δ + B_σ(0)` lies in the box `P`,
  -- since `|t_i| ≤ |t| < σ`.
  set P : Set (Euclid (m + 1)) := {y | ∀ i, δ - σ ≤ y i ∧ y i ≤ 1 - δ + σ}
  have hsupp : support (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ P := by
    intro y hy
    obtain ⟨a, ha, t, ht, rfl⟩ :=
      support_convolution_subset_swap (ContinuousLinearMap.lsmul ℝ ℝ) hy
    have ha' : ∀ i, δ < a i ∧ a i < 1 - δ := by
      by_contra h
      exact ha (hs0 a h)
    have ht' : ‖t‖ < σ := mem_ball_zero_iff.mp (hρs ht)
    intro i
    have hti : |t i| < σ := lt_of_le_of_lt (PiLp.norm_apply_le t i) ht'
    obtain ⟨h1, h2⟩ := abs_lt.mp hti
    obtain ⟨h3, h4⟩ := ha' i
    simp only [PiLp.add_apply]
    constructor <;> linarith
  -- Step 6: `P` is compact (the preimage of a product of intervals under `PiLp.homeomorph`)
  -- and lies in `Q₁` because `0 < δ − σ` and `1 − δ + σ < 1`.
  have hPc : IsCompact P := by
    have h := (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ : Fin (m + 1) => isCompact_Icc (a := δ - σ) (b := 1 - δ + σ))
    convert h using 1
    ext y
    simp only [mem_preimage, mem_univ_pi, mem_Icc]
    rfl
  have hPQ : P ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro y hy i
    obtain ⟨h1, h2⟩ := hy i
    constructor <;> linarith
  -- Step 7: `tsupport (ρ ⋆ s)` is a closed subset of the compact set `P ⊆ Q₁`.
  have hts : tsupport (convolution ρ s (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆ P :=
    closure_minimal hsupp hPc.isClosed
  exact ⟨hG, hPc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hPQ, hbd⟩

end Submission

/-- **Mollification does not increase the variation on `Q_δ`** (the duality step of Simon
Ch. 2, 2.5 (4)–(5)).  Let `u` be integrable on the open unit cube `Q₁` with `∫_{Q₁} u div g ≤ V`
for every smooth compactly supported field `g` with `spt g ⊆ Q₁` and `|g| ≤ 1`, and let `ρ ≥ 0`
be a smooth kernel with `∫ρ = 1` and `spt ρ ⊆ B_σ(0)`, `0 < σ < δ`.  Then `f = ρ ⋆ 1_{Q₁}u`
satisfies `∫_{Q_δ} ‖Df‖ ≤ V`.  With `w` the Riesz representative of `Df` and the unit field
`s = 1_{Q_δ} w/|w|`, the field `G = ρ̌ ⋆ s` (`ρ̌(z) = ρ(−z)`) is admissible
(`cmcdt_cbm_sa_smoothed_field`), and `cmcdt_cbm_sa_mollify_adjoint` gives
`∫_{Q_δ} ‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V`, the last step by testing with `−G`. -/
theorem Submission.cmcdt_cbm_sa_grad_bound : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ σ : ℝ) (ρ : Euclid (m + 1) → ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < σ → σ < δ → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → ∫ z, ρ z = 1 → support ρ ⊆ ball (0 : Euclid (m + 1)) σ → ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (convolution ρ ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}.indicator u) (ContinuousLinearMap.lsmul ℝ ℝ) volume) x‖ ≤ V := by
  intro m u V δ σ ρ hu hV hσ hσδ hρ hρ0 hρ1 hρs
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qδ : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 0(b): the cubes are measurable (finite intersections of coordinate half-spaces)
  have hcoord : ∀ i : Fin (m + 1), Measurable (fun y : Euclid (m + 1) => y i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hcube : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    have : {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
        ⋂ i, ({y : Euclid (m + 1) | a < y i} ∩ {y | y i < b}) := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hcoord i)).inter
        (measurableSet_lt (hcoord i) measurable_const)
  have hQ1m : MeasurableSet Q1 := hcube 0 1
  have hQδm : MeasurableSet Qδ := hcube δ (1 - δ)
  -- Step 0(c), 0(d): `Q_δ ⊆ Q₁ ⊆ closedBall 0 √n`, so both have finite measure
  have hQδQ1 : Qδ ⊆ Q1 := fun y hy i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  have hQ1fin : volume Q1 < ∞ := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))).2 ⟨Real.sqrt (m + 1), ?_⟩
      |>.measure_lt_top
    intro y hy
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 := hy i
          rw [Real.norm_eq_abs, abs_of_pos h1.1]
          nlinarith [h1.1, h1.2]
      _ = (m + 1 : ℝ) := by simp
  have hQδfin : volume Qδ < ∞ := (measure_mono hQδQ1).trans_lt hQ1fin
  -- Step 0(e): `ū = 1_{Q₁}u` is integrable
  set ub : Euclid (m + 1) → ℝ := Q1.indicator u with hub
  have hub_int : Integrable ub := (integrable_indicator_iff hQ1m).2 hu
  -- Step 0(f): `ρ` is `C¹` with compact support (`spt ρ ⊆ closedBall 0 σ`)
  have hρc : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) σ) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall (hρs h))
  have hρC1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast le_top)
  -- Step 2: the Riesz representative `w` of `Df` and the unit field `s = 1_{Q_δ} |w|⁻¹ w`
  set f : Euclid (m + 1) → ℝ := convolution ρ ub (ContinuousLinearMap.lsmul ℝ ℝ) volume
  set w : Euclid (m + 1) → Euclid (m + 1) :=
    fun x => (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm (fderiv ℝ f x)
  have hw_meas : Measurable w :=
    (InnerProductSpace.toDual ℝ (Euclid (m + 1))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)
  have hw_norm : ∀ x, ‖w x‖ = ‖fderiv ℝ f x‖ := fun x => LinearIsometryEquiv.norm_map _ _
  have hw_apply : ∀ x, fderiv ℝ f x (w x) = ‖w x‖ ^ 2 := fun x => by
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq]
  set s : Euclid (m + 1) → Euclid (m + 1) := Qδ.indicator (fun x => ‖w x‖⁻¹ • w x) with hs
  have hs_meas : Measurable s := ((hw_meas.norm.inv).smul hw_meas).indicator hQδm
  have hs_le : ∀ x, ‖s x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ Qδ
    · rw [hs, Set.indicator_of_mem hx, norm_smul, norm_inv, norm_norm]
      by_cases h0 : ‖w x‖ = 0
      · simp [h0]
      · rw [inv_mul_cancel₀ h0]
    · rw [hs, Set.indicator_of_notMem hx, norm_zero]; exact zero_le_one
  have hs_zero : ∀ x, x ∉ Qδ → s x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hs_int : Integrable s := by
    rw [hs, integrable_indicator_iff hQδm]
    exact Measure.integrableOn_of_bounded (M := 1) hQδfin.ne
      ((hw_meas.norm.inv).smul hw_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [norm_smul, norm_inv, norm_norm]
        by_cases h0 : ‖w x‖ = 0
        · simp [h0]
        · rw [inv_mul_cancel₀ h0])
  -- Step 2(e): `Df(x)(s(x)) = 1_{Q_δ}(x) ‖Df(x)‖`
  have hs_apply : ∀ x, fderiv ℝ f x (s x) = Qδ.indicator (fun x => ‖fderiv ℝ f x‖) x := by
    intro x
    by_cases hx : x ∈ Qδ
    · rw [hs, Set.indicator_of_mem hx, Set.indicator_of_mem hx, map_smul, hw_apply,
        smul_eq_mul, ← hw_norm]
      by_cases h0 : ‖w x‖ = 0
      · simp [h0]
      · field_simp
    · rw [hs, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, map_zero]
  -- Step 3: the reflected kernel `ρ̌(z) = ρ(−z)` satisfies the kernel hypotheses
  have hρr_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ (-z)) := hρ.comp contDiff_neg
  have hρr_nonneg : ∀ z, 0 ≤ (fun z => ρ (-z)) z := fun z => hρ0 (-z)
  have hρr_int : ∫ z, (fun z => ρ (-z)) z = 1 := by
    simp only
    rw [integral_neg_eq_self]
    exact hρ1
  have hρr_supp : support (fun z => ρ (-z)) ⊆ ball (0 : Euclid (m + 1)) σ := by
    intro z hz
    have h := hρs (show -z ∈ support ρ from hz)
    simpa using h
  -- Step 4: the smoothed field `G = ρ̌ ⋆ s` is admissible
  set G : Euclid (m + 1) → Euclid (m + 1) :=
    convolution (fun z => ρ (-z)) s (ContinuousLinearMap.lsmul ℝ ℝ) volume
  obtain ⟨hG_smooth, hG_cpt, hG_tsupp, hG_le⟩ :=
    Submission.cmcdt_cbm_sa_smoothed_field m δ σ (fun z => ρ (-z)) s hσ hσδ hρr_smooth
      hρr_nonneg hρr_int hρr_supp hs_meas.aestronglyMeasurable hs_le hs_zero
  -- Step 5: testing the variation hypothesis with `−G` gives `−∫_{Q₁} u div G ≤ V`
  have h5 := hV (-G) hG_smooth.neg hG_cpt.neg (by rw [tsupport_neg]; exact hG_tsupp)
    (fun y => by rw [Pi.neg_apply, norm_neg]; exact hG_le y)
  have h5' : -∫ y in Q1, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) ≤ V := by
    rw [← integral_neg]
    convert h5 using 3 with y
    rw [fderiv_neg, ContinuousLinearMap.toLinearMap_neg, map_neg, mul_neg]
  -- Step 6: the adjoint identity `∫ Df(s) = −∫ ū div G`
  have h6 := Submission.cmcdt_cbm_sa_mollify_adjoint (m + 1) ρ ub s hρC1 hρc hub_int hs_int
  -- Step 7: `∫ ū div G = ∫_{Q₁} u div G`
  have h7 : ∫ z, ub z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) =
      ∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := by
    rw [← integral_indicator hQ1m]
    congr 1
    funext z
    by_cases hz : z ∈ Q1
    · simp [hub, hz]
    · simp [hub, hz]
  -- Step 8: `∫_{Q_δ} ‖Df‖ = ∫ Df(s) = −∫_{Q₁} u div G ≤ V`
  calc ∫ x in Qδ, ‖fderiv ℝ f x‖
      = ∫ x, Qδ.indicator (fun x => ‖fderiv ℝ f x‖) x := (integral_indicator hQδm).symm
    _ = ∫ x, fderiv ℝ f x (s x) := by
        congr 1
        funext x
        exact (hs_apply x).symm
    _ = -∫ z, ub z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := h6
    _ = -∫ z in Q1, u z * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G z) := by rw [h7]
    _ ≤ V := h5'

/-- **Smooth approximation with the variation bound on `Q_δ`** (Simon Ch. 2, 2.5, as used in the
proof of 2.7 and of the deformation theorem, Ch. 6, 5.1).  If `u` is integrable on `Q₁` and
`∫_{Q₁} u div g ≤ V` for every smooth compactly supported field `g` with `spt g ⊆ Q₁` and
`|g| ≤ 1`, then for `δ > 0` the mollifications `v_k = ρ_k ⋆ 1_{Q₁}u` are `C^∞` and satisfy
`∫_{Q_δ} ‖Dv_k‖ ≤ V` and `∫_{Q_δ} |v_k − u| → 0`.  Here `ρ_k` is the unit-mass normalization of
the bump of radius `σ_k = δ/(k + 2) < δ`; the bound is `cmcdt_cbm_sa_grad_bound`, and since
`1_{Q₁}u = u` on `Q_δ ⊆ Q₁`, the convergence follows from `cmcdt_cbm_sa_mollify_l1` as
`σ_k → 0`. -/
theorem Submission.cmcdt_cbm_smooth_approx : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V δ : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → 0 < δ → ∃ v : ℕ → Euclid (m + 1) → ℝ, (∀ k, ContDiff ℝ 1 (v k)) ∧ (∀ k, ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, ‖fderiv ℝ (v k) x‖ ≤ V) ∧ Tendsto (fun k => ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |v k x - u x|) atTop (𝓝 0) := by
  intro m u V δ hu hV hδ
  set Q1 : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set Qδ : Set (Euclid (m + 1)) := {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}
  -- Step 0: the cubes are measurable, `Q_δ ⊆ Q₁`, and `ū = 1_{Q₁}u` is integrable
  have hcoord : ∀ i : Fin (m + 1), Measurable (fun y : Euclid (m + 1) => y i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hcube : ∀ a b : ℝ, MeasurableSet {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} := by
    intro a b
    have : {y : Euclid (m + 1) | ∀ i, a < y i ∧ y i < b} =
        ⋂ i, ({y : Euclid (m + 1) | a < y i} ∩ {y | y i < b}) := by
      ext y; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (hcoord i)).inter
        (measurableSet_lt (hcoord i) measurable_const)
  have hQ1m : MeasurableSet Q1 := hcube 0 1
  have hQδm : MeasurableSet Qδ := hcube δ (1 - δ)
  have hQδQ1 : Qδ ⊆ Q1 := fun y hy i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  set ub : Euclid (m + 1) → ℝ := Q1.indicator u
  have hub_int : Integrable ub := (integrable_indicator_iff hQ1m).2 hu
  -- Step 1: radii `σ_k = δ/(k + 2) ∈ (0, δ)` and kernels `ρ_k = b_k / ∫ b_k`, where `b_k` is the
  -- `C^∞` bump with `b_k = 1` on `B_{σ_k/2}(0)`, `0 ≤ b_k ≤ 1` and `support b_k = B_{σ_k}(0)`
  set σ : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2)
  have hσ0 : ∀ k, 0 < σ k := fun k => div_pos hδ (by positivity)
  have hσδ : ∀ k, σ k < δ := fun k =>
    div_lt_self hδ (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  let b : ℕ → ContDiffBump (0 : Euclid (m + 1)) := fun k =>
    ⟨σ k / 2, σ k, half_pos (hσ0 k), half_lt_self (hσ0 k)⟩
  have hb_int : ∀ k, 0 < ∫ y, b k y := fun k => by
    refine (integral_pos_iff_support_of_nonneg (b k).nonneg'
      ((b k).continuous.integrable_of_hasCompactSupport (b k).hasCompactSupport)).2 ?_
    rw [(b k).support_eq]
    exact measure_ball_pos volume _ (b k).rOut_pos
  set ρ : ℕ → Euclid (m + 1) → ℝ := fun k x => b k x / ∫ y, b k y
  have hρ_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => (b k).contDiff.div_const _
  have hρ_nonneg : ∀ k z, 0 ≤ ρ k z := fun k z => div_nonneg (b k).nonneg (hb_int k).le
  have hρ_one : ∀ k, ∫ z, ρ k z = 1 := fun k => by
    show ∫ z, b k z / ∫ y, b k y = 1
    rw [integral_div, div_self (hb_int k).ne']
  have hρ_supp : ∀ k, support (ρ k) = ball (0 : Euclid (m + 1)) (σ k) := fun k => by
    show support (fun x => b k x / ∫ y, b k y) = ball 0 (b k).rOut
    rw [support_div, (b k).support_eq, support_const (hb_int k).ne', inter_univ]
  have hρ_cpt : ∀ k, HasCompactSupport (ρ k) := fun k =>
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid (m + 1)) (σ k)) fun x hx => by
      by_contra h
      exact hx (ball_subset_closedBall ((hρ_supp k).subset h))
  -- Step 2: `v_k = ρ_k ⋆ ū` is `C^∞` (differentiation under the integral sign), hence `C¹`
  refine ⟨fun k => convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume, fun k => ?_,
    fun k => ?_, ?_⟩
  · exact ((hρ_cpt k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρ_smooth k)
      hub_int.locallyIntegrable).of_le (by exact_mod_cast le_top)
  -- Step 3: the variation bound `∫_{Q_δ} ‖Dv_k‖ ≤ V`, since `0 < σ_k < δ`
  · exact Submission.cmcdt_cbm_sa_grad_bound m u V δ (σ k) (ρ k) hu hV (hσ0 k) (hσδ k) (hρ_smooth k)
      (hρ_nonneg k) (hρ_one k) (hρ_supp k).subset
  -- Step 4: given `ε > 0`, `cmcdt_cbm_sa_mollify_l1` gives `r > 0` with `‖ρ ⋆ ū − ū‖₁ ≤ ε/2` for
  -- unit-mass kernels supported in `B_r(0)`; `σ_k ≤ r` for `k ≥ N > δ/r`, and `ū = u` on `Q_δ`
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨r, hr, hL1⟩ :=
      Submission.cmcdt_cbm_sa_mollify_l1 (m + 1) ub hub_int (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_gt (δ / r)
    refine ⟨N, fun k hk => ?_⟩
    have hσr : σ k ≤ r := by
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      have h1 : δ < r * ((k : ℝ) + 2) := by
        rw [mul_comm]
        exact (div_lt_iff₀ hr).1 (by linarith)
      exact (div_le_iff₀ (by positivity)).2 h1.le
    have hL := hL1 (ρ k) (hρ_smooth k).continuous (hρ_nonneg k) (hρ_one k)
      ((hρ_supp k).subset.trans (ball_subset_ball hσr))
    rw [dist_zero_right]
    calc ‖∫ x in Qδ, |convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x|‖
        ≤ (∫⁻ x in Qδ, ENNReal.ofReal
            ‖|convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - u x|‖).toReal :=
          norm_integral_le_lintegral_norm _
      _ = (∫⁻ x in Qδ,
            ‖convolution (ρ k) ub (ContinuousLinearMap.lsmul ℝ ℝ) volume x - ub x‖ₑ).toReal := by
          congr 1
          refine setLIntegral_congr_fun hQδm fun x hx => ?_
          have hx1 : ub x = u x := indicator_of_mem (hQδQ1 hx) u
          rw [hx1, Real.norm_eq_abs, abs_abs, Real.enorm_eq_ofReal_abs]
      _ ≤ ε / 2 := ENNReal.toReal_le_of_le_ofReal (half_pos hε).le
          ((setLIntegral_le_lintegral _ _).trans hL)
      _ < ε := half_lt_self hε

/-- **BV Poincaré inequality on the unit cube** (Simon Ch. 2, 2.7, as used for the first line of
(32) in the proof of Ch. 6, 5.1).  Let `n = m + 1` and `Q_δ = (δ, 1 − δ)ⁿ`, `Q₁ = Q_0`.  If
`u ∈ L¹(Q₁)` and `∫_{Q₁} u div g ≤ V` for all `g ∈ C^∞_c(Q₁; ℝⁿ)` with `|g| ≤ 1`, then
`∫_{Q₁} |u − c| ≤ 2^{n+1} √n V` for the mean `c = ∫_{Q₁} u`.  Testing with `g = 0` gives
`V ≥ 0`.  For `0 < δ < 1/2` the `C¹` functions `v_k` of `cmcdt_cbm_smooth_approx` have
`∫_{Q_δ} |Dv_k| ≤ V` and `v_k → u` in `L¹(Q_δ)`, so `cmcdt_cbm_smooth_poincare` bounds their
oscillation `∫_{Q_δ}∫_{Q_δ} |v_k(x) − v_k(y)|` by `K = 2ⁿ√n V`, and the bound passes to `u`
(`cmcdt_cbm_bvp_osc_le_of_l1_approx`), then to `Q₁` as `δ ↓ 0`
(`cmcdt_cbm_bvp_osc_le_of_inner_cubes`).  As `|Q₁| = 1`, `∫_{Q₁} |u − c|` is at most the
oscillation of `u` over `Q₁` (`cmcdt_cbm_bvp_mean_dev_le_osc`), and `K ≤ 2^{n+1}√n V`. -/
theorem Submission.cmcdt_cbm_bv_poincare : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ c : ℝ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - c| ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := by
  intro m u V hu hV
  -- Step 0: `V ≥ 0`, testing with `g = 0`
  have hV0 : 0 ≤ V := by
    simpa using hV 0 contDiff_zero_fun .zero (by simp only [tsupport_zero, empty_subset])
      (by simp)
  -- Step 2: for `0 < δ < 1/2` the oscillation of `u` over `Q_δ` is at most `K = 2ⁿ√n V`
  have hδ : ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∫ x in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
        ∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ}, |u x - u y| ≤
        2 ^ (m + 1) * Real.sqrt (m + 1) * V := by
    intro δ hδ _
    obtain ⟨v, hv, hvV, hvu⟩ := Submission.cmcdt_cbm_smooth_approx m u V δ hu hV hδ
    refine Submission.cmcdt_cbm_bvp_osc_le_of_l1_approx m u v δ _ hu hδ.le
      (fun k => (hv k).continuous) (fun k => ?_) hvu
    exact (Submission.cmcdt_cbm_smooth_poincare m (v k) δ (hv k) hδ.le).trans
      (mul_le_mul_of_nonneg_left (hvV k) (by positivity))
  -- Steps 3–4: let `δ ↓ 0`, then compare with the mean `c = ∫_{Q₁} u` (`|Q₁| = 1`)
  refine ⟨∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y, ?_⟩
  calc _ ≤ ∫ x in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u x - u y| :=
        Submission.cmcdt_cbm_bvp_mean_dev_le_osc m _ u
          (Submission.cmcdt_cbm_bvp_unit_cube_volume m) hu
    _ ≤ 2 ^ (m + 1) * Real.sqrt (m + 1) * V :=
        Submission.cmcdt_cbm_bvp_osc_le_of_inner_cubes m u _ hu hδ
    _ ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := by
      gcongr
      · norm_num
      · omega
/-- **Trace estimate on the unit cube** (step 5 of the median argument; it replaces the appeal to
Simon Ch. 2, 2.8–2.9 in the second line of (32) in the proof of Ch. 6, 5.1).  `div G = tr DG` is
continuous, so `|div G| ≤ M` on `Q₁`.  For `δ ∈ (0, 1/4)` the `C¹` functions `v_k` of
`cmcdt_cbm_smooth_approx` have `∫_{Q_δ} ‖Dv_k‖ ≤ V` and `v_k → w` in `L¹(Q_δ)`, so the smooth
estimate `cmcdt_cbm_smooth_trace` on `Q_δ` passes to `w` (`cmcdt_cbm_bvt_l1_limit`); `Q_δ ⊆ Q₁`
bounds `∫_{Q_δ} |w|` by `∫_{Q₁} |w|`, and `δ → 0⁺` by `cmcdt_cbm_bvt_cube_exhaust`. -/
theorem Submission.cmcdt_cbm_bv_trace : ∀ (m : ℕ) (w : Euclid (m + 1) → ℝ) (V : ℝ), IntegrableOn w {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
  intro m w V hw hV G hG hG1
  -- the cubes `{a < z_i < b}` are open, and `Q_δ ⊆ Q₁` for `δ ≥ 0`
  have hopen : ∀ a b : ℝ, IsOpen {z : Euclid (m + 1) | ∀ i, a < z i ∧ z i < b} := by
    intro a b
    simp only [ofPred_forall, ofPred_and]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hsub : ∀ δ : ℝ, 0 ≤ δ → {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ} ⊆
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := fun δ hδ z hz i =>
    ⟨hδ.trans_lt (hz i).1, (hz i).2.trans_le (by linarith)⟩
  -- `div G = tr ∘ DG` is continuous, hence bounded by `M` on `Q₁`
  have hdc : Continuous fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
    ((LinearMap.trace ℝ (Euclid (m + 1))).comp
      (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional.comp
      (hG.continuous_fderiv one_ne_zero)
  obtain ⟨⟨M, hM⟩, -⟩ := Submission.cmcdt_cbm_bvt_cube_cont_bound (m + 1) _ hdc
  -- for `δ ∈ (0, 1/4)`: `|∫_{Q_δ} w div G| ≤ (2n + 1) V + 4n ∫_{Q₁} |w|`
  have hδbound : ∀ δ ∈ Ioo (0 : ℝ) (1 / 4),
      |∫ y in {z : Euclid (m + 1) | ∀ i, δ < z i ∧ z i < 1 - δ},
          w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (2 * (m + 1) + 1) * V +
          4 * (m + 1) * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w y| := by
    rintro δ ⟨hδ0, hδ⟩
    have hQ := hsub δ hδ0.le
    -- `C¹` approximations `v_k → w` in `L¹(Q_δ)` with `∫_{Q_δ} ‖Dv_k‖ ≤ V`
    obtain ⟨v, hv, hvV, hvw⟩ := Submission.cmcdt_cbm_smooth_approx m w V δ hw hV hδ0
    refine (Submission.cmcdt_cbm_bvt_l1_limit volume _ v w
      (fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)) ((2 * (m + 1) + 1) * V)
      (4 * (m + 1)) M (hopen δ (1 - δ)).measurableSet (by positivity)
      (fun k => (Submission.cmcdt_cbm_bvt_cube_cont_bound (m + 1) (v k)
        (hv k).continuous).2.mono_set hQ)
      (hw.mono_set hQ) hdc.aestronglyMeasurable (fun y hy => hM y (hQ hy)) hvw
      fun k => ?_).trans ?_
    · -- the smooth estimate on `Q_δ`, with `∫_{Q_δ} ‖Dv_k‖ ≤ V`
      refine (Submission.cmcdt_cbm_smooth_trace m (v k) G δ (hv k) hG hG1 hδ0.le hδ.le).trans ?_
      gcongr _ * ?_ + _
      exact hvV k
    · -- `∫_{Q_δ} |w| ≤ ∫_{Q₁} |w|`
      gcongr _ + _ * ?_
      exact setIntegral_mono_set (Integrable.abs hw) (ae_of_all _ fun y => abs_nonneg (w y))
        (ae_of_all _ hQ)
  -- `δ → 0⁺`: `∫_{Q_δ} w div G → ∫_{Q₁} w div G`, with `w div G` integrable on `Q₁`
  have hwG : IntegrableOn (fun y => w y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y))
      {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    Integrable.mul_bdd hw hdc.aestronglyMeasurable
      (ae_restrict_of_forall_mem (hopen 0 1).measurableSet fun y hy => hM y hy)
  exact le_of_tendsto (Submission.cmcdt_cbm_bvt_cube_exhaust (m + 1) _ hwG).abs
    (Filter.mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)) hδbound)

/-- **Poincaré and trace inequalities on the unit cube with an integer median** (part C of the
proof of the deformation theorem, Simon Ch. 6, 5.1, displays (26)–(33), replacing the appeal to
the BV facts Ch. 6, 2.35–2.37 and Ch. 2, 2.7, 2.9).  Let `n = m + 1` and `Q₁ = (0, 1)ⁿ`.  If `u`
is integer-valued and integrable on `Q₁`, and `∫_{Q₁} u div g ≤ V` for every smooth `g` with
compact support in `Q₁` and `|g| ≤ 1`, then an integer `β` satisfies `∫_{Q₁} |u − β| ≤ cV`,
`|β| ≤ 2 ∫_{Q₁} |u|` and `|∫_{Q₁} (u − β) div G| ≤ cV` for every smooth `G` with `|G| ≤ 1`, where
`c = 2ⁿ⁺¹√n + (2n + 1) + 4n · 2ⁿ⁺¹√n`.  Testing with `g = 0` gives `V ≥ 0`.  The integer median
`β` of `cmcdt_cbm_integer_median` minimizes `c ↦ ∫_{Q₁} |u − c|`, so the Poincaré inequality
`cmcdt_cbm_bv_poincare` gives the first bound.  Since `∫_{Q₁} div g = 0`
(`cmcdt_cbm_integral_div_eq_zero`), `u − β` satisfies the hypothesis with the same `V`, and the
trace estimate `cmcdt_cbm_bv_trace` gives
`|∫_{Q₁} (u − β) div G| ≤ (2n + 1)V + 4n ∫_{Q₁} |u − β|`. -/
theorem Submission.cmcdt_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  have hA : (0 : ℝ) ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) := by positivity
  refine ⟨2 ^ (m + 2) * Real.sqrt (m + 1) + (2 * (m + 1) + 1) +
    4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1)), by positivity, ?_⟩
  intro u V hint hu hV
  -- Step 0: `V ≥ 0`, testing with `g = 0`
  have hV0 : 0 ≤ V := by
    simpa using hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp [tsupport])
      (fun _ => by simp)
  have hAV : 0 ≤ 2 ^ (m + 2) * Real.sqrt (m + 1) * V := mul_nonneg hA hV0
  have hmV : 0 ≤ (m : ℝ) * V := mul_nonneg m.cast_nonneg hV0
  have hmAV : 0 ≤ (m : ℝ) * (2 ^ (m + 2) * Real.sqrt (m + 1) * V) := mul_nonneg m.cast_nonneg hAV
  -- `Q₁` is the preimage of the box `(0, 1)ⁿ ⊆ Fin n → ℝ`, so it has volume `1`
  have hQ : volume {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ≠ ⊤ := by
    have hpre : {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} =
        (WithLp.ofLp : Euclid (m + 1) → Fin (m + 1) → ℝ) ⁻¹' Set.pi univ fun _ => Ioo 0 1 := by
      ext y
      simp [Set.mem_pi]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  -- Steps 3–4: `∫_{Q₁} |u − β| ≤ ∫_{Q₁} |u − c₀| ≤ 2ⁿ⁺¹√n V` for the integer median `β`
  obtain ⟨c₀, hc₀⟩ := Submission.cmcdt_cbm_bv_poincare m u V hu hV
  obtain ⟨β, hβmin, hβ⟩ := Submission.cmcdt_cbm_integer_median m u hint hu
  have h1 : ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤
      2 ^ (m + 2) * Real.sqrt (m + 1) * V :=
    (hβmin c₀).trans hc₀
  refine ⟨β, h1.trans (by nlinarith), hβ, fun G hG hG1 => ?_⟩
  -- Step 0: `u − β` is integrable on `Q₁` and, as `∫_{Q₁} div g = 0`, satisfies the hypothesis
  -- with the same `V`
  have hw : IntegrableOn (fun y => u y - β) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
    hu.sub (integrableOn_const hQ)
  have hwV : ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g →
      HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} →
      (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V := by
    intro g hg hgc hgQ hg1
    -- `div g` is continuous with compact support, hence integrable
    have hd : Integrable fun y => LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
      have htr : Continuous fun A : Euclid (m + 1) →L[ℝ] Euclid (m + 1) =>
          LinearMap.trace ℝ (Euclid (m + 1)) (A : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) :=
        (LinearMap.trace ℝ (Euclid (m + 1)) ∘ₗ
          ContinuousLinearMap.coeLM ℝ).continuous_of_finiteDimensional
      exact (htr.comp (hg.continuous_fderiv (by simp))).integrable_of_hasCompactSupport
        ((hgc.fderiv ℝ).comp_left (by simp))
    have hdiv := Submission.cmcdt_cbm_integral_div_eq_zero m g
      (hg.of_le (by exact_mod_cast le_top)) hgc hgQ
    by_cases hud : IntegrableOn
        (fun y => u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
    · -- `∫ (u − β) div g = ∫ u div g − β ∫ div g = ∫ u div g ≤ V`
      simp_rw [sub_mul]
      rw [integral_sub hud (hd.const_mul _).integrableOn, integral_const_mul, hdiv, mul_zero,
        sub_zero]
      exact hV g hg hgc hgQ hg1
    · -- otherwise `(u − β) div g` is not integrable either, and its integral vanishes
      have hnot : ¬IntegrableOn
          (fun y => (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y))
          {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
        intro h
        refine hud ((h.add (hd.const_mul (β : ℝ)).integrableOn).congr_fun_ae
          (ae_of_all _ fun y => ?_))
        simp only [Pi.add_apply]
        ring
      rw [integral_undef hnot]
      exact hV0
  -- Step 5: the trace estimate for `u − β`
  calc |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)|
      ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) *
          ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| :=
        Submission.cmcdt_cbm_bv_trace m (fun y => u y - β) V hw hwV G
          (hG.of_le (by exact_mod_cast le_top)) hG1
    _ ≤ (2 * (m + 1) + 1) * V + 4 * (m + 1) * (2 ^ (m + 2) * Real.sqrt (m + 1) * V) := by
        gcongr
    _ ≤ _ := by nlinarith

end GMT.Ch07
