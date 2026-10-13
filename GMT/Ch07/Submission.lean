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

/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]

/-- **Simon Ch. 6, Remark 3.2(3)** (mass of an integer multiplicity current).  If
`R = (M, θ, ξ)` represents `T ∈ 𝒟ₙ(U)`, then `M_W(T) = ∫_{M ∩ W} θ dHⁿ = (θ Hⁿ⌞M)(W)` for every
open `W ⊆ U`.  A.e. on `M`, `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for an orthonormal `τ` (Gram determinant `1`), so
`covectorEuclideanNorm_gram_bounds` gives `|⟨β, ξ⟩| ≤ |β|_E` for every `n`-covector `β` and
`⟨β, ξ⟩ = 1` for some `β` with `|β|_E ≤ 1`.  The first bound gives
`T(ω) ≤ (θ Hⁿ⌞M)(spt ω) ≤ (θ Hⁿ⌞M)(W)` for every admissible `ω`.  Conversely, fix a compact
`K ⊆ W` and `η ∈ (0, 1)`.  The covector space is finite-dimensional, so the unit ball has a dense
sequence `βⱼ`; with a strongly measurable version of `ξ`, the disjointed sets
`Aⱼ ⊆ {⟨βⱼ, ξ⟩ > 1 − η}` cover `M` a.e.  Finitely many `Aⱼ` cover `K` up to measure `η`, and
inner regularity gives disjoint compacts `Cⱼ ⊆ K ∩ Aⱼ` exhausting them up to `η`.  Smooth plateau
functions `χⱼ` on disjoint thickenings of the `Cⱼ` inside `W` give an admissible
`ω = Σ χⱼ βⱼ` with `ω = βⱼ` on `Cⱼ`, whose support exceeds `⋃ Cⱼ` by measure `< η`; hence
`T(ω) ≥ (1 − η)(μ(K) − 2η) − η`.  Letting `η → 0` and exhausting `W` by compacts gives
`(θ Hⁿ⌞M)(W) ≤ M_W(T)`. -/
theorem Submission.imrep_represents_massOn_eq_measure : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → IsOpen W → W ⊆ U → T.massOn W = R.measure W := by
  intro P n U W T R hU hR hW hWU
  classical
  have hCB := Submission.covectorEuclideanNorm_gram_bounds P n
  have hpt : ∀ x, (∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q ∧
      IsUnitOrientationOf (R.orient x) Q) →
      (∀ β : Covector (Euclid P) n, |R.orient x β| ≤ covectorEuclideanNorm β) ∧
      ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 := by
    rintro x ⟨Q, -, τ, hτ, -, hsign⟩
    have hG : Matrix.det (Matrix.of fun i j => inner ℝ (τ i) (τ j)) = 1 := by
      have hI : (Matrix.of fun i j => inner ℝ (τ i) (τ j) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        ext i j
        rw [Matrix.of_apply, Matrix.one_apply]
        exact (orthonormal_iff_ite.mp hτ) i j
      rw [hI, Matrix.det_one]
    obtain ⟨α, hα1, hατ⟩ := hCB.2 τ hτ
    rcases hsign with h | h
    · refine ⟨fun β => ?_, α, hα1, by rw [h, hατ]⟩
      rw [h]
      simpa [hG] using hCB.1 β τ
    · refine ⟨fun β => ?_, -α, by rwa [covectorEuclideanNorm_neg], ?_⟩
      · rw [h, abs_neg]
        simpa [hG] using hCB.1 β τ
      · rw [h]
        simp [hατ]
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hae : ∀ᵐ x ∂R.measure, (∀ β : Covector (Euclid P) n,
      |R.orient x β| ≤ covectorEuclideanNorm β) ∧ ∃ β : Covector (Euclid P) n,
      covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 :=
    hac.ae_le (R.orients.mono fun x hx => hpt x hx)
  have hH1 : ∀ᵐ x ∂R.measure, ∀ β : Covector (Euclid P) n,
      |R.orient x β| ≤ covectorEuclideanNorm β := hae.mono fun x hx => hx.1
  have hmeas : AEStronglyMeasurable R.orient R.measure := R.aestronglyMeasurable_orient.mono_ac hac
  have hrep : ∀ ω : TestFormOn U n,
      T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
    intro ω
    have hf : Measurable fun x => ((R.mult x : NNReal)) :=
      (measurable_of_countable (fun k : ℕ => (k : NNReal))).comp R.measurable_mult
    have key := integral_withDensity_eq_integral_smul (μ := μHE[n].restrict R.carrier) hf
      (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x))
    simp only [ENNReal.coe_natCast] at key
    rw [hR ω, IMRep.action, IMRep.measure, key]
    simp [NNReal.smul_def]
  have hH2 : ∀ᵐ x ∂R.measure, ∃ β : Covector (Euclid P) n,
      covectorEuclideanNorm β ≤ 1 ∧ R.orient x β = 1 := hae.mono fun x hx => hx.2
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K ≠ ⊤ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.isClosed.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet, Set.inter_comm]
    exact R.locallyIntegrable_mult K hK hKU
  -- Euclidean coefficient norm is absolutely homogeneous
  have hNsmul : ∀ (c : ℝ) (β : Covector (Euclid P) n),
      covectorEuclideanNorm (c • β) = |c| * covectorEuclideanNorm β := by
    intro c β
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c)]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  -- the covector space is finite-dimensional (the coefficient map is injective)
  have hfd : FiniteDimensional ℝ (Covector (Euclid P) n) := by
    classical
    let e := EuclideanSpace.basisFun (Fin P) ℝ
    let c : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
      { toFun := fun β f => β (fun i => e (f i))
        map_add' := fun β γ => by ext f; simp
        map_smul' := fun r β => by ext f; simp }
    refine FiniteDimensional.of_injective c ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext v
    have hv : v = fun i => ∑ k, (e.repr (v i) k) • e k := by
      funext i; exact (e.sum_repr (v i)).symm
    have key := β.toMultilinearMap.map_sum (fun i k => (e.repr (v i) k) • e k)
    have hsum : β v = ∑ r : Fin n → Fin P, β (fun i => (e.repr (v i) (r i)) • e (r i)) := by
      conv_lhs => rw [hv]
      exact key
    rw [hsum]
    change _ = (0 : ℝ)
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [β.map_smul_univ (fun i => e.repr (v i) (r i)) (fun i => e (r i))]
    have h0 : β (fun i => e (r i)) = 0 := congrFun hβ r
    rw [h0, smul_zero]
  -- smooth admissible plateau forms on finitely many disjoint compact pieces
  have hplat : ∀ (m : ℕ) (ν : Measure (Euclid P)) (W : Set (Euclid P)) (C : Fin m → Set (Euclid P))
      (b : Fin m → Covector (Euclid P) n) (δ : ℝ≥0∞), IsOpen W → ν W ≠ ⊤ →
      (∀ j, IsCompact (C j)) → (∀ j, C j ⊆ W) → (∀ i j, i ≠ j → Disjoint (C i) (C j)) →
      (∀ j, covectorEuclideanNorm (b j) ≤ 1) → δ ≠ 0 →
      ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ W ∧
        (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ (∀ j, ∀ x ∈ C j, ω x = b j) ∧
        ν (Function.support ω \ ⋃ j, C j) < δ := by
    intro m ν W C b δ hW hνW hC hCW hdisj hb hδ
    -- the per-piece error budget
    obtain ⟨d, hd0, hdδ⟩ : ∃ d : ℝ, 0 < d ∧ ENNReal.ofReal d ≤ δ := by
      rcases eq_or_ne δ ⊤ with h | h
      · exact ⟨1, one_pos, by simp [h]⟩
      · exact ⟨δ.toReal, ENNReal.toReal_pos hδ h, by rw [ENNReal.ofReal_toReal h]⟩
    set η : ℝ≥0∞ := ENNReal.ofReal (d / (m + 1)) with hη
    have hηpos : η ≠ 0 := by
      rw [hη, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
    have hmη : (m : ℝ≥0∞) * η < δ := by
      calc (m : ℝ≥0∞) * η = ENNReal.ofReal (m * (d / (m + 1))) := by
            rw [hη, ENNReal.ofReal_mul (Nat.cast_nonneg m), ENNReal.ofReal_natCast]
        _ < ENNReal.ofReal d := by
            rw [ENNReal.ofReal_lt_ofReal_iff hd0]
            calc (m : ℝ) * (d / (m + 1)) = d * (m / (m + 1)) := by ring
              _ < d * 1 := mul_lt_mul_of_pos_left
                  (by rw [div_lt_one (by positivity)]; linarith) hd0
              _ = d := mul_one d
        _ ≤ δ := hdδ
    -- choose a radius
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r ∧ (∀ j, cthickening r (C j) ⊆ W) ∧
        (∀ i j, i ≠ j → Disjoint (cthickening r (C i)) (cthickening r (C j))) ∧
        (∀ j, ν (cthickening r (C j)) < ν (C j) + η) := by
      refine (eventually_mem_nhdsWithin).and (Filter.eventually_all.2 fun j => ?_) |>.and
        (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_) |>.and
        (Filter.eventually_all.2 fun j => ?_) |>.mono fun r h => ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
      · obtain ⟨s, hs, hsW⟩ := (hC j).exists_cthickening_subset_open hW (hCW j)
        filter_upwards [Ioo_mem_nhdsGT hs] with r hr
        exact (cthickening_mono hr.2.le _).trans hsW
      · by_cases hij : i = j
        · exact Filter.Eventually.of_forall fun r h => (h hij).elim
        · obtain ⟨s, hs, hsd⟩ := (hdisj i j hij).exists_cthickenings (hC i) (hC j).isClosed
          filter_upwards [Ioo_mem_nhdsGT hs] with r hr _
          exact hsd.mono (cthickening_mono hr.2.le _) (cthickening_mono hr.2.le _)
      · obtain ⟨s, hs, hsW⟩ := (hC j).exists_cthickening_subset_open hW (hCW j)
        have hfin : ν (C j) ≠ ⊤ := ne_top_of_le_ne_top hνW (measure_mono (hCW j))
        have ht := tendsto_measure_cthickening_of_isClosed (μ := ν)
          ⟨s, hs, ne_top_of_le_ne_top hνW (measure_mono hsW)⟩ (hC j).isClosed
        exact (ht.mono_left nhdsWithin_le_nhds).eventually_lt_const (ENNReal.lt_add_right hfin hηpos)
    obtain ⟨r, hr0, hrW, hrd, hrν⟩ := hev.exists
    -- smooth plateau functions
    have hχ : ∀ j : Fin m, ∃ χ : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ range χ ⊆ Icc 0 1 ∧
        Function.support χ = thickening r (C j) ∧ ∀ x, x ∈ C j ↔ χ x = 1 := fun j =>
      exists_contDiff_support_eq_eq_one_iff isOpen_thickening (hC j).isClosed
        (self_subset_thickening hr0 _)
    choose χ hχs hχr hχsupp hχone using hχ
    -- membership in thickenings is exclusive
    have hexcl : ∀ i j x, x ∈ thickening r (C j) → i ≠ j → χ i x = 0 := by
      intro i j x hx hij
      rw [← Function.notMem_support, hχsupp]
      intro hxi
      exact Set.disjoint_left.mp (hrd i j hij) (thickening_subset_cthickening _ _ hxi)
        (thickening_subset_cthickening _ _ hx)
    set ω : DifferentialForm (Euclid P) n := fun x => ∑ j, χ j x • b j with hωdef
    have hsupp : Function.support ω ⊆ ⋃ j, cthickening r (C j) := by
      intro x hx
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      have : χ j x ≠ 0 := fun h => hj (by simp [h])
      exact mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ (hχsupp j ▸ this)⟩
    have hFc : IsCompact (⋃ j, cthickening r (C j)) := isCompact_iUnion fun j => (hC j).cthickening
    have htsupp : tsupport ω ⊆ ⋃ j, cthickening r (C j) :=
      closure_minimal hsupp hFc.isClosed
    refine ⟨ω, ⟨?_, ?_⟩, htsupp.trans (iUnion_subset hrW), ?_, ?_, ?_⟩
    · exact ContDiff.sum fun j _ => (hχs j).smul contDiff_const
    · exact hFc.of_isClosed_subset (isClosed_tsupport _) htsupp
    · intro x
      by_cases hx : ∃ j, x ∈ thickening r (C j)
      · obtain ⟨j, hj⟩ := hx
        have : ω x = χ j x • b j := by
          rw [hωdef]
          exact Finset.sum_eq_single j (fun i _ hij => by rw [hexcl i j x hj hij, zero_smul])
            (by simp)
        rw [this, hNsmul]
        have h01 := hχr j (mem_range_self x)
        rw [abs_of_nonneg h01.1]
        calc χ j x * covectorEuclideanNorm (b j) ≤ 1 * 1 := mul_le_mul h01.2 (hb j) (covectorEuclideanNorm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · push Not at hx
        have : ω x = 0 := Finset.sum_eq_zero fun j _ => by
          rw [show χ j x = 0 from by rw [← Function.notMem_support, hχsupp]; exact hx j, zero_smul]
        rw [this, covectorEuclideanNorm_zero]; exact zero_le_one
    · intro j x hx
      have hxt : x ∈ thickening r (C j) := self_subset_thickening hr0 _ hx
      rw [hωdef]
      simp only
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [hexcl i j x hxt hij, zero_smul]) (by simp),
        (hχone j x).1 hx, one_smul]
    · calc ν (Function.support ω \ ⋃ j, C j) ≤ ν (⋃ j, (cthickening r (C j) \ C j)) := by
            apply measure_mono
            intro x ⟨hx, hxC⟩
            obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
            have : χ j x ≠ 0 := fun h => hj (by simp [h])
            refine mem_iUnion.2 ⟨j, thickening_subset_cthickening _ _ (hχsupp j ▸ this), ?_⟩
            exact fun hxj => hxC (mem_iUnion.2 ⟨j, hxj⟩)
        _ ≤ ∑ j, ν (cthickening r (C j) \ C j) := measure_iUnion_fintype_le _ _
        _ ≤ ∑ _j : Fin m, η := by
            gcongr with j
            have hfin : ν (C j) ≠ ⊤ := ne_top_of_le_ne_top hνW (measure_mono (hCW j))
            exact (measure_sdiff_lt_of_lt_add (hC j).isClosed.measurableSet.nullMeasurableSet
              (self_subset_cthickening _) hfin (hrν j)).le
        _ = (m : ℝ≥0∞) * η := by simp
        _ < δ := hmη
  -- upper bound (supplied step 3)
  have hupper : T.massOn W ≤ R.measure W := by
    apply sSup_le
    rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
    show ENNReal.ofReal (T ω) ≤ R.measure W
    rw [hrep ω]
    set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n) with hfdef
    have hfc : Continuous f := ω.2.1.1.continuous
    have hgm : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous.comp_aestronglyMeasurable
        (hmeas.prodMk hfc.aestronglyMeasurable)
    have hbd : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ₑ ≤ (tsupport f).indicator 1 x := by
      filter_upwards [hH1] with x hx
      by_cases hxs : x ∈ tsupport f
      · rw [Set.indicator_of_mem hxs, Pi.one_apply, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.mpr ((hx (f x)).trans (hω1 x))
      · rw [image_eq_zero_of_notMem_tsupport hxs]
        simp
    calc ENNReal.ofReal (∫ x, R.orient x (f x) ∂R.measure)
        ≤ ‖∫ x, R.orient x (f x) ∂R.measure‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x, ‖R.orient x (f x)‖ₑ ∂R.measure := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, (tsupport f).indicator 1 x ∂R.measure := lintegral_mono_ae hbd
      _ = R.measure (tsupport f) := lintegral_indicator_one (isClosed_tsupport _).measurableSet
      _ ≤ R.measure W := measure_mono hωW
  -- lower bound (supplied steps 4-7)
  have hlowerGen : ∀ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n),
      (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) →
      (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ⊤) → AEStronglyMeasurable ξ μ →
      (∀ᵐ x ∂μ, ∀ β : Covector (Euclid P) n, |ξ x β| ≤ covectorEuclideanNorm β) →
      (∀ᵐ x ∂μ, ∃ β : Covector (Euclid P) n, covectorEuclideanNorm β ≤ 1 ∧ ξ x β = 1) →
      μ W ≤ T.massOn W := by
    intro μ ξ hrep hfin hmeas hH1 hH2
    set B : Set (Covector (Euclid P) n) := {β | covectorEuclideanNorm β ≤ 1} with hBdef
    have : Nonempty B := ⟨⟨0, by simp [hBdef]⟩⟩
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq B
    set ξ' := hmeas.mk ξ
    have hξ'm : StronglyMeasurable ξ' := hmeas.stronglyMeasurable_mk
    have hξξ' : ξ =ᵐ[μ] ξ' := hmeas.ae_eq_mk
    -- compact lower bound
    have hKbound : ∀ K, IsCompact K → K ⊆ W → μ K ≤ T.massOn W := by
      intro K hK hKW
      have hμK : μ K ≠ ⊤ := hfin K hK (hKW.trans hWU)
      have key : ∀ η : ℝ, 0 < η → η < 1 → ∃ ω : TestFormOn U n, ω ∈ massAdmissibleOn U n W ∧
          (1 - η) * (μ.real K - 2 * η) - η ≤ T ω := by
        intro η hη0 hη1
        set E : ℕ → Set (Euclid P) := fun j => {x | 1 - η < ξ' x (u j : Covector (Euclid P) n)}
          with hEdef
        have hEm : ∀ j, MeasurableSet (E j) := fun j =>
          measurableSet_lt measurable_const
            (StronglyMeasurable.apply_continuousLinearMap hξ'm (u j : Covector (Euclid P) n)).measurable
        have hcov : ∀ᵐ x ∂μ, x ∈ ⋃ j, E j := by
          filter_upwards [hH2, hξξ'] with x ⟨β, hβ1, hβx⟩ hx
          have hopen : IsOpen {b : B | 1 - η < ξ x (b : Covector (Euclid P) n)} :=
            isOpen_lt continuous_const ((ξ x).continuous.comp continuous_subtype_val)
          obtain ⟨j, hj⟩ := hu.exists_mem_open hopen ⟨⟨β, hβ1⟩, by
            show 1 - η < ξ x β
            rw [hβx]; linarith⟩
          refine mem_iUnion.2 ⟨j, ?_⟩
          show 1 - η < ξ' x (u j : Covector (Euclid P) n)
          rw [← hx]; exact hj
        set A := disjointed E with hAdef
        have hAm : ∀ j, MeasurableSet (A j) := MeasurableSet.disjointed hEm
        have hAE : ∀ j, A j ⊆ E j := disjointed_subset E
        -- choose m
        obtain ⟨m, hm⟩ : ∃ m : ℕ, μ (K \ ⋃ j ∈ Finset.range m, A j) < ENNReal.ofReal η := by
          have hanti : Antitone fun m : ℕ => K \ ⋃ j ∈ Finset.range m, A j := by
            intro a b hab
            exact sdiff_subset_sdiff_right (biUnion_subset_biUnion_left
              (by simpa using Finset.range_subset_range.2 hab))
          have hlim := tendsto_measure_iInter_atTop (μ := μ)
            (fun m => (hK.isClosed.measurableSet.diff
              (Finset.measurableSet_biUnion _ fun j _ => hAm j)).nullMeasurableSet) hanti
            ⟨0, by simpa using hμK⟩
          have hnull : μ (⋃ j, E j)ᶜ = 0 :=
            measure_eq_zero_iff_ae_notMem.2 (hcov.mono fun x hx h => h hx)
          have hinter : μ (⋂ m : ℕ, K \ ⋃ j ∈ Finset.range m, A j) = 0 := by
            refine measure_mono_null ?_ hnull
            intro x hx
            rw [mem_iInter] at hx
            rw [← iUnion_disjointed, mem_compl_iff, mem_iUnion]
            rintro ⟨j, hj⟩
            exact (hx (j + 1)).2 (mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_self j), hj⟩)
          rw [hinter] at hlim
          exact (hlim.eventually (gt_mem_nhds (by simpa using hη0))).exists
        -- inner closed approximations inside K
        have : IsFiniteMeasure (μ.restrict K) := ⟨by simpa [Measure.restrict_apply_univ] using hμK.lt_top⟩
        have hF : ∀ j : Fin m, ∃ F ⊆ K ∩ A j, IsClosed F ∧
            μ ((K ∩ A j) \ F) < ENNReal.ofReal (η / (m + 1)) := by
          intro j
          obtain ⟨F, hFsub, hFcl, hFμ⟩ := MeasurableSet.exists_isClosed_sdiff_lt (μ := μ.restrict K)
            (hK.isClosed.measurableSet.inter (hAm j)) (measure_ne_top _ _)
            (ε := ENNReal.ofReal (η / (m + 1))) (by
              rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity)
          refine ⟨F, hFsub, hFcl, ?_⟩
          rwa [Measure.restrict_apply' hK.isClosed.measurableSet,
            inter_eq_left.2 (sdiff_subset.trans inter_subset_left)] at hFμ
        choose F hFsub hFcl hFμ using hF
        have hFK : ∀ j, F j ⊆ K := fun j => (hFsub j).trans inter_subset_left
        have hFA : ∀ j, F j ⊆ A j := fun j => (hFsub j).trans inter_subset_right
        -- neighbourhood V of K
        obtain ⟨ρ, hρ, hρW⟩ := hK.exists_cthickening_subset_open hW hKW
        have hVμ : μ (thickening ρ K) ≠ ⊤ :=
          ne_top_of_le_ne_top (hfin _ hK.cthickening (hρW.trans hWU))
            (measure_mono (thickening_subset_cthickening _ _))
        have hVW : thickening ρ K ⊆ W := (thickening_subset_cthickening _ _).trans hρW
        obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀C, hω₀μ⟩ := hplat m μ (thickening ρ K) F
          (fun j => (u j : Covector (Euclid P) n)) (ENNReal.ofReal η) isOpen_thickening hVμ
          (fun j => hK.of_isClosed_subset (hFcl j) (hFK j))
          (fun j => (hFK j).trans (self_subset_thickening hρ _))
          (fun i j hij => (disjoint_disjointed E (Fin.val_injective.ne hij)).mono (hFA i) (hFA j))
          (fun j => (u j).2) (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hη0)
        let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVW.trans hWU)⟩
        refine ⟨ω, ⟨hω₀V.trans hVW, hω₀1⟩, ?_⟩
        rw [hrep ω]
        -- the integrand
        set g : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hgdef
        have hω₀c : Continuous ω₀ := hω₀t.1.continuous
        have hgm : AEStronglyMeasurable g μ :=
          (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous.comp_aestronglyMeasurable
            (hmeas.prodMk hω₀c.aestronglyMeasurable)
        have hg1 : ∀ᵐ x ∂μ, ‖g x‖ ≤ 1 := by
          filter_upwards [hH1] with x hx
          rw [Real.norm_eq_abs]; exact (hx (ω₀ x)).trans (hω₀1 x)
        have hg0 : ∀ x, x ∉ Function.support ω₀ → g x = 0 := by
          intro x hx
          rw [Function.notMem_support] at hx
          simp [hgdef, hx]
        have hSV : Function.support ω₀ ⊆ thickening ρ K := (subset_tsupport _).trans hω₀V
        have hgi : Integrable g μ := by
          refine IntegrableOn.integrable_of_forall_notMem_eq_zero
            (Measure.integrableOn_of_bounded (s := thickening ρ K) hVμ hgm (M := 1) (ae_restrict_of_ae hg1)) ?_
          intro x hx; exact hg0 x (fun h => hx (hSV h))
        set C : Set (Euclid P) := ⋃ j, F j with hCdef
        have hCm : MeasurableSet C := MeasurableSet.iUnion fun j => (hFcl j).measurableSet
        have hCK : C ⊆ K := iUnion_subset hFK
        have hSm : MeasurableSet (Function.support ω₀) := hω₀c.isOpen_support.measurableSet
        -- lower bound on C
        have hC1 : (1 - η) * μ.real C ≤ ∫ x in C, g x ∂μ := by
          have hae : ∀ᵐ x ∂μ.restrict C, 1 - η ≤ g x := by
            rw [ae_restrict_iff' hCm]
            filter_upwards [hξξ'] with x hx hxC
            obtain ⟨j, hj⟩ := mem_iUnion.1 hxC
            have hxE : x ∈ E j := hAE j (hFA j hj)
            show 1 - η ≤ ξ x (ω₀ x)
            rw [hω₀C j x hj, hx]
            exact le_of_lt hxE
          calc (1 - η) * μ.real C = ∫ x in C, (1 - η) ∂μ := by
                rw [setIntegral_const, smul_eq_mul, mul_comm]
            _ ≤ ∫ x in C, g x ∂μ := by
                apply setIntegral_mono_ae_restrict _ hgi.integrableOn hae
                exact integrableOn_const (ne_top_of_le_ne_top hμK (measure_mono hCK))
        -- the rest
        have hrest : -(μ.real (Function.support ω₀ \ C)) ≤ ∫ x in Cᶜ, g x ∂μ := by
          rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hCm.compl
            (show Function.support ω₀ \ C ⊆ Cᶜ from fun x hx => hx.2)
            (fun x hx => hg0 x (fun h => hx.2 ⟨h, hx.1⟩))]
          have h := norm_setIntegral_le_of_norm_le_const_ae (f := g) (μ := μ)
            (s := Function.support ω₀ \ C) (C := 1)
            (lt_of_le_of_lt (measure_mono (sdiff_subset.trans hSV)) hVμ.lt_top)
            (ae_restrict_of_ae hg1)
          rw [Real.norm_eq_abs, one_mul] at h
          linarith [neg_abs_le (∫ x in Function.support ω₀ \ C, g x ∂μ)]
        have hsplit := integral_add_compl hCm hgi
        -- measure of C
        have hKC : μ.real K ≤ μ.real C + 2 * η := by
          have h1 : μ (K \ C) ≤ ENNReal.ofReal (2 * η) := by
            calc μ (K \ C) ≤ μ ((K \ ⋃ j ∈ Finset.range m, A j) ∪ ⋃ j : Fin m, ((K ∩ A j) \ F j)) := by
                  apply measure_mono
                  intro x ⟨hxK, hxC⟩
                  by_cases hx : x ∈ ⋃ j ∈ Finset.range m, A j
                  · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
                    refine Or.inr (mem_iUnion.2 ⟨⟨j, Finset.mem_range.1 hj⟩, ⟨hxK, hxj⟩, ?_⟩)
                    exact fun h => hxC (mem_iUnion.2 ⟨_, h⟩)
                  · exact Or.inl ⟨hxK, hx⟩
              _ ≤ μ (K \ ⋃ j ∈ Finset.range m, A j) + ∑ j : Fin m, μ ((K ∩ A j) \ F j) :=
                  (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
              _ ≤ ENNReal.ofReal η + ∑ _j : Fin m, ENNReal.ofReal (η / (m + 1)) :=
                  add_le_add hm.le (Finset.sum_le_sum fun j _ => (hFμ j).le)
              _ ≤ ENNReal.ofReal (2 * η) := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m),
                    ← ENNReal.ofReal_add hη0.le (by positivity)]
                  apply ENNReal.ofReal_le_ofReal
                  have : (m : ℝ) * (η / (m + 1)) ≤ η := by
                    calc (m : ℝ) * (η / (m + 1)) = η * (m / (m + 1)) := by ring
                      _ ≤ η * 1 := mul_le_mul_of_nonneg_left
                          (by rw [div_le_one (by positivity)]; linarith) hη0.le
                      _ = η := mul_one η
                  linarith
          have h2 : μ K ≤ μ C + μ (K \ C) := by
            calc μ K ≤ μ (C ∪ (K \ C)) := measure_mono (fun x hx => by
                    by_cases h : x ∈ C
                    · exact Or.inl h
                    · exact Or.inr ⟨hx, h⟩)
              _ ≤ μ C + μ (K \ C) := measure_union_le _ _
          have hCfin : μ C ≠ ⊤ := ne_top_of_le_ne_top hμK (measure_mono hCK)
          have := h2.trans (add_le_add le_rfl h1)
          rw [← ENNReal.ofReal_toReal hμK, ← ENNReal.ofReal_toReal hCfin,
            ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)] at this
          exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
        have hSC : μ.real (Function.support ω₀ \ C) ≤ η := by
          have hfin' : μ (Function.support ω₀ \ C) ≠ ⊤ := ne_top_of_le_ne_top hVμ
            (measure_mono (sdiff_subset.trans hSV))
          rw [measureReal_def, ← ENNReal.ofReal_le_ofReal_iff hη0.le, ENNReal.ofReal_toReal hfin']
          exact hω₀μ.le
        have hmul : (1 - η) * (μ.real K - 2 * η) ≤ (1 - η) * μ.real C :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        linarith [hC1, hrest, hsplit, hKC, hSC]
      -- conclude μ K ≤ massOn W
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      set a := μ.real K with hadef
      have ha : 0 ≤ a := measureReal_nonneg
      set η : ℝ := min (1 / 2) ((ε : ℝ) / (a + 3)) with hηdef
      have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
      have hη1 : η < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
      have hηε : η * (a + 3) ≤ ε := by
        have := min_le_right (1 / 2 : ℝ) ((ε : ℝ) / (a + 3))
        rw [← hηdef] at this
        calc η * (a + 3) ≤ (ε : ℝ) / (a + 3) * (a + 3) := by gcongr
          _ = ε := div_mul_cancel₀ _ (by positivity)
      obtain ⟨ω, hωadm, hωT⟩ := key η hη0 hη1
      have hexp : (1 - η) * (a - 2 * η) - η = a - η * (a + 3) + 2 * η ^ 2 := by ring
      have hsq : 0 ≤ 2 * η ^ 2 := by positivity
      have hTε : a - ε ≤ T ω := by linarith
      calc μ K = ENNReal.ofReal a := (ENNReal.ofReal_toReal hμK).symm
        _ = ENNReal.ofReal ((a - ε) + ε) := by ring_nf
        _ ≤ ENNReal.ofReal (a - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
        _ ≤ T.massOn W + ε := by
            gcongr
            · exact (ENNReal.ofReal_le_ofReal hTε).trans (T.le_massOn hωadm)
            · simp
    -- exhaustion
    obtain ⟨G, hGcl, hGW, hGU, hGmono⟩ := hW.exists_iUnion_isClosed
    set Kk : ℕ → Set (Euclid P) := fun k => G k ∩ closedBall 0 k with hKkdef
    have hKkc : ∀ k, IsCompact (Kk k) := fun k => (isCompact_closedBall 0 (k : ℝ)).inter_left (hGcl k)
    have hKkW : ∀ k, Kk k ⊆ W := fun k => inter_subset_left.trans (hGW k)
    have hKkmono : Monotone Kk := fun a b hab =>
      inter_subset_inter (hGmono hab) (closedBall_subset_closedBall (by exact_mod_cast hab))
    have hKkU : ⋃ k, Kk k = W := by
      apply Subset.antisymm (iUnion_subset hKkW)
      intro x hx
      rw [← hGU] at hx
      obtain ⟨k₀, hk₀⟩ := mem_iUnion.1 hx
      obtain ⟨k₁, hk₁⟩ := exists_nat_ge ‖x‖
      refine mem_iUnion.2 ⟨max k₀ k₁, hGmono (le_max_left _ _) hk₀, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      exact hk₁.trans (by exact_mod_cast le_max_right k₀ k₁)
    calc μ W = μ (⋃ k, Kk k) := by rw [hKkU]
      _ = ⨆ k, μ (Kk k) := hKkmono.measure_iUnion
      _ ≤ T.massOn W := iSup_le fun k => hKbound _ (hKkc k) (hKkW k)
  exact le_antisymm hupper (hlowerGen R.measure R.orient hrep hfin hmeas hH1 hH2)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
