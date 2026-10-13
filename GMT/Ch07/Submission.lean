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

/-- Graph representation of a blow-up of `T = ∂[[E]]` (used in the proof of Simon 7.5.5,
pp. 199–200).  Let `Γ(v) = x + ιv + ι'u(v)` be a `C¹` graph chart of `N` over `B_{δ₁}`
(`ι, ι'` orthogonal isometries spanning `ℝ^{n+1+k}`) whose Jacobian orients `ξN`, let
`y = x + ιs + ι't`, `G(w) = ιw + ι'(λ⁻¹(u(s + λw) − t))` and
`F' = {w : s + λw ∈ B_{δ₁}, Γ(s + λw) ∈ E}`.  If `η_{y,λ#}T = ∂[[η_{y,λ}(E)]]` and the area
formula for `C¹` graphs holds, then `F'` is measurable and
`η_{y,λ#}T(ω) = ∫_{F' ∩ B_R} dω(G(w))(DG(w)e₀, …, DG(w)eₙ) dw` for `ω ∈ 𝒟ⁿ(ℝ^{n+1+k})` with
`spt ω ⊆ B_R`, whenever `|s| + λR < δ₁`, `|t| + λR < δ₂` and `B_{λR}(y) ⊆ U`.  Here
`y + λG(w) = Γ(s + λw)` and `DG(w) = DΓ(s + λw)`; Pythagoras and the chart identity give
`η_{y,λ}(E) ∩ B_R ⊆ G(F' ∩ B_R) ⊆ η_{y,λ}(E)`, and `dω = 0` off `B_R`. -/
theorem Submission.codim1_zsl_gbl_blowUp_graph_representation : ∀ (n k : ℕ) (U N E : Set (Euclid (n + 1 + k))) (ξN : Euclid (n + 1 + k) → MultiVector (n + 1 + k) (n + 1)) (T : GeometricCurrentOn U n) (x y : Euclid (n + 1 + k)) (lam : ℝ) (hlam : 0 < lam) (ι : Euclid (n + 1) →ₗᵢ[ℝ] Euclid (n + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + 1 + k)) (u : Euclid (n + 1) → Euclid k) (δ₁ δ₂ : ℝ) (s : Euclid (n + 1)) (t : Euclid k), MeasurableSet E → E ⊆ N → IsBoundaryOfRegion (blowUp T y lam hlam.ne') (dilation y lam '' E) (fun z => ξN (y + lam • z)) → (∀ (g : Euclid (n + 1) → Euclid k) (D A : Set (Euclid (n + 1))) (f : Euclid (n + 1 + k) → ℝ), IsOpen D → ContDiffOn ℝ 1 g D → MeasurableSet A → A ⊆ D → ∫ z in (fun w => ι w + ι' (g w)) '' A, f z ∂μHE[n + 1] = ∫ w in A, Real.sqrt (((fderiv ℝ (fun w => ι w + ι' (g w)) w).adjoint ∘L fderiv ℝ (fun w => ι w + ι' (g w)) w).det) * f (ι w + ι' (g w))) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ z : Euclid (n + 1 + k), ∃ v w, z = ι v + ι' w) → ContDiffOn ℝ 1 u (ball 0 δ₁) → N ∩ {z | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∃ w ∈ ball (0 : Euclid k) δ₂, z = x + ι v + ι' w} = (fun v => x + ι v + ι' (u v)) '' ball (0 : Euclid (n + 1)) δ₁ → (∀ v ∈ ball (0 : Euclid (n + 1)) δ₁, ∀ α : Covector (Euclid (n + 1 + k)) (n + 1), α (fun j => fderiv ℝ (fun v => x + ι v + ι' (u v)) v (EuclideanSpace.single j (1 : ℝ))) = Real.sqrt (((fderiv ℝ (fun v => x + ι v + ι' (u v)) v).adjoint ∘L fderiv ℝ (fun v => x + ι v + ι' (u v)) v).det) * ξN (x + ι v + ι' (u v)) α) → y = x + ι s + ι' t → MeasurableSet {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∧ ∀ R : ℝ, ‖s‖ + lam * R < δ₁ → ‖t‖ + lam * R < δ₂ → ball y (lam * R) ⊆ U → ∀ ω : TestFormOn (univ : Set (Euclid (n + 1 + k))) n, tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ ball 0 R → currentEval (blowUp T y lam hlam.ne') (ω : DifferentialForm (Euclid (n + 1 + k)) n) = ∫ w in {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧ x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} ∩ ball 0 R, exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) (ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) (fun j => fderiv ℝ (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) w (EuclideanSpace.single j (1 : ℝ))) := by
  intro n k U N E ξN T x y lam hlam ι ι' u δ₁ δ₂ s t hE hEN hbd harea horth hspan hu hchart
    hjac hy
  have hlam0 : lam ≠ 0 := hlam.ne'
  -- Step 1: measurability of F'
  have hΓcont : ContinuousOn (fun v => x + ι v + ι' (u v)) (ball (0 : Euclid (n + 1)) δ₁) := by
    have hcu : ContinuousOn u (ball (0 : Euclid (n + 1)) δ₁) := hu.continuousOn
    exact (continuousOn_const.add ι.continuous.continuousOn).add
      (ι'.continuous.comp_continuousOn hcu)
  have hA₀ : MeasurableSet {v : Euclid (n + 1) | v ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι v + ι' (u v) ∈ E} := by
    classical
    have hpw : Measurable ((ball (0 : Euclid (n + 1)) δ₁).piecewise
        (fun v => x + ι v + ι' (u v)) (fun _ => (0 : Euclid (n + 1 + k)))) :=
      hΓcont.measurable_piecewise continuousOn_const measurableSet_ball
    have heq : {v : Euclid (n + 1) | v ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
        x + ι v + ι' (u v) ∈ E} = ball (0 : Euclid (n + 1)) δ₁ ∩
          (ball (0 : Euclid (n + 1)) δ₁).piecewise (fun v => x + ι v + ι' (u v))
            (fun _ => (0 : Euclid (n + 1 + k))) ⁻¹' E := by
      ext v
      simp only [Set.mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hv, hvE⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv]⟩
      · rintro ⟨hv, hvE⟩
        exact ⟨hv, by rwa [Set.piecewise_eq_of_mem _ _ _ hv] at hvE⟩
    rw [heq]
    exact measurableSet_ball.inter (hpw hE)
  have haff : Continuous (fun w : Euclid (n + 1) => s + lam • w) :=
    continuous_const.add (continuous_id.const_smul lam)
  have hF : MeasurableSet {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E} :=
    haff.measurable hA₀
  refine ⟨hF, ?_⟩
  intro R hR1 hR2 hRU ω hω
  set F' := {w : Euclid (n + 1) | s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ ∧
      x + ι (s + lam • w) + ι' (u (s + lam • w)) ∈ E}
  -- Step 2: the dilation
  have hdil : ∀ z : Euclid (n + 1 + k), dilation y lam (y + lam • z) = z := by
    intro z
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply,
      smul_add, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    abel
  have hdil' : ∀ e : Euclid (n + 1 + k), y + lam • dilation y lam e = e := by
    intro e
    simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply,
      smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hlam0, one_smul]
    abel
  have hηE : dilation y lam '' E = (fun z => y + lam • z) ⁻¹' E := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa [hdil' e] using he
    · intro hz
      exact ⟨y + lam • z, hz, hdil z⟩
  have hηEmeas : MeasurableSet (dilation y lam '' E) := by
    rw [hηE]
    exact (continuous_const.add (continuous_id.const_smul lam)).measurable hE
  have hballU : ball (0 : Euclid (n + 1 + k)) R ⊆ dilation y lam '' U := by
    intro z hz
    refine ⟨y + lam • z, hRU ?_, hdil z⟩
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam.le]
    rw [mem_ball, dist_zero_right] at hz
    exact mul_lt_mul_of_pos_left hz hlam
  -- Step 3: evaluation of the blow-up
  have hωtest : IsTestForm (ω : DifferentialForm (Euclid (n + 1 + k)) n) := ω.2.1
  have hcur : currentEval (blowUp T y lam hlam.ne') (ω : DifferentialForm (Euclid (n + 1 + k)) n) =
      ∫ z in dilation y lam '' E, ξN (y + lam • z)
        (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z) ∂μHE[n + 1] := by
    have h : IsTestForm (ω : DifferentialForm (Euclid (n + 1 + k)) n) ∧
        tsupport (ω : DifferentialForm (Euclid (n + 1 + k)) n) ⊆ dilation y lam '' U :=
      ⟨hωtest, hω.trans hballU⟩
    unfold currentEval
    rw [dite_eq_left h]
    exact hbd ⟨ω, h⟩
  -- Step 4: Pythagoras and (4.1)
  have hpyth : ∀ (a : Euclid (n + 1)) (b : Euclid k),
      ‖a‖ ≤ ‖ι a + ι' b‖ ∧ ‖b‖ ≤ ‖ι a + ι' b‖ := by
    intro a b
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth a b)
    rw [ι.norm_map, ι'.norm_map] at h
    have h0 := norm_nonneg (ι a + ι' b)
    have ha := norm_nonneg a
    have hb := norm_nonneg b
    constructor <;> nlinarith
  have h41 : ∀ w : Euclid (n + 1),
      y + lam • (ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) =
        x + ι (s + lam • w) + ι' (u (s + lam • w)) := by
    intro w
    rw [hy]
    simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hlam0,
      one_smul]
    abel
  -- Step 5: Y ⊆ η(E)
  set G : Euclid (n + 1) → Euclid (n + 1 + k) :=
    fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))
  have hYsub : G '' (F' ∩ ball 0 R) ⊆ dilation y lam '' E := by
    rintro _ ⟨w, ⟨hwF, _⟩, rfl⟩
    rw [hηE, mem_preimage]
    simp only [G]
    rw [h41 w]
    exact hwF.2
  -- Step 6: f vanishes on η(E) \ Y
  have hvan : ∀ z ∈ dilation y lam '' E \ G '' (F' ∩ ball 0 R),
      ξN (y + lam • z)
        (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z) = 0 := by
    rintro z ⟨hzE, hzY⟩
    by_cases hzR : z ∈ ball (0 : Euclid (n + 1 + k)) R
    · exfalso
      apply hzY
      rw [hηE, mem_preimage] at hzE
      obtain ⟨a, b, hzab⟩ := hspan z
      have hzn : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hzR
      obtain ⟨ha, hb⟩ := hpyth a b
      rw [← hzab] at ha hb
      have he : y + lam • z = x + ι (s + lam • a) + ι' (t + lam • b) := by
        rw [hy, hzab]
        simp only [map_add, map_smul, smul_add]
        abel
      have hsa : s + lam • a ∈ ball (0 : Euclid (n + 1)) δ₁ := by
        rw [mem_ball, dist_zero_right]
        calc ‖s + lam • a‖ ≤ ‖s‖ + ‖lam • a‖ := norm_add_le _ _
          _ = ‖s‖ + lam * ‖a‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
          _ < ‖s‖ + lam * R := by
            have := mul_lt_mul_of_pos_left (ha.trans_lt hzn) hlam
            linarith
          _ < δ₁ := hR1
      have htb : t + lam • b ∈ ball (0 : Euclid k) δ₂ := by
        rw [mem_ball, dist_zero_right]
        calc ‖t + lam • b‖ ≤ ‖t‖ + ‖lam • b‖ := norm_add_le _ _
          _ = ‖t‖ + lam * ‖b‖ := by rw [norm_smul, Real.norm_of_nonneg hlam.le]
          _ < ‖t‖ + lam * R := by
            have := mul_lt_mul_of_pos_left (hb.trans_lt hzn) hlam
            linarith
          _ < δ₂ := hR2
      have hmem : y + lam • z ∈ N ∩ {z | ∃ v ∈ ball (0 : Euclid (n + 1)) δ₁,
          ∃ w ∈ ball (0 : Euclid k) δ₂, z = x + ι v + ι' w} :=
        ⟨hEN hzE, s + lam • a, hsa, t + lam • b, htb, he⟩
      rw [hchart] at hmem
      obtain ⟨v, hv, hve⟩ := hmem
      have hsw : s + lam • (lam⁻¹ • (v - s)) = v := by
        rw [smul_smul, mul_inv_cancel₀ hlam0, one_smul]
        abel
      simp only at hve
      have hGw : G (lam⁻¹ • (v - s)) = z := by
        apply smul_right_injective _ hlam0
        apply add_left_cancel (a := y)
        show y + lam • (ι (lam⁻¹ • (v - s)) + ι' (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t))) =
          y + lam • z
        rw [h41 (lam⁻¹ • (v - s)), hsw]
        exact hve
      refine ⟨lam⁻¹ • (v - s), ⟨⟨?_, ?_⟩, ?_⟩, hGw⟩
      · rw [hsw]; exact hv
      · rw [hsw, hve]; exact hzE
      · -- |w| ≤ |G w| = |z| < R
        have := (hpyth (lam⁻¹ • (v - s)) (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t))).1
        rw [mem_ball, dist_zero_right]
        have hGw' : ι (lam⁻¹ • (v - s)) + ι' (lam⁻¹ • (u (s + lam • (lam⁻¹ • (v - s))) - t)) = z :=
          hGw
        rw [hGw'] at this
        exact this.trans_lt hzn
    · have hzt : z ∉ tsupport (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n)) :=
        fun h => hzR (hω (tsupport_exteriorDerivative_subset _ h))
      rw [image_eq_zero_of_notMem_tsupport hzt, map_zero]
  -- Step 7: restriction of the integral
  have hrestr := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := μHE[n + 1])
    (f := fun z => ξN (y + lam • z)
      (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z)) hηEmeas hYsub hvan
  -- Step 8: area formula
  set D : Set (Euclid (n + 1)) := (fun w => s + lam • w) ⁻¹' ball (0 : Euclid (n + 1)) δ₁
  have hDopen : IsOpen D := isOpen_ball.preimage haff
  have hgC1 : ContDiffOn ℝ 1 (fun w => lam⁻¹ • (u (s + lam • w) - t)) D := by
    have haffC : ContDiff ℝ 1 (fun w : Euclid (n + 1) => s + lam • w) :=
      contDiff_const.add (contDiff_id.const_smul lam)
    have h1 : ContDiffOn ℝ 1 (fun w => u (s + lam • w)) D :=
      hu.comp haffC.contDiffOn (fun w hw => hw)
    exact (h1.sub contDiffOn_const).const_smul lam⁻¹
  have hAmeas : MeasurableSet (F' ∩ ball (0 : Euclid (n + 1)) R) := hF.inter measurableSet_ball
  have hAD : F' ∩ ball (0 : Euclid (n + 1)) R ⊆ D := fun w hw => hw.1.1
  have harea' := harea (fun w => lam⁻¹ • (u (s + lam • w) - t)) D (F' ∩ ball 0 R)
    (fun z => ξN (y + lam • z) (exteriorDerivative (ω : DifferentialForm (Euclid (n + 1 + k)) n) z))
    hDopen hgC1 hAmeas hAD
  -- Step 9: the derivative of G
  have hDG : ∀ w ∈ D, fderiv ℝ (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t))) w =
      fderiv ℝ (fun v => x + ι v + ι' (u v)) (s + lam • w) := by
    intro w hw
    have hv : s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ := hw
    have hud : DifferentiableAt ℝ u (s + lam • w) :=
      (hu.differentiableOn one_ne_zero _ hv).differentiableAt (isOpen_ball.mem_nhds hv)
    set L := fderiv ℝ u (s + lam • w)
    have hLd : HasFDerivAt u L (s + lam • w) := hud.hasFDerivAt
    have haffd : HasFDerivAt (fun w : Euclid (n + 1) => s + lam • w)
        (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1))) w :=
      (((ContinuousLinearMap.id ℝ (Euclid (n + 1))).hasFDerivAt (x := w)).const_smul
        lam).const_add s
    have hcomp : HasFDerivAt (fun w => u (s + lam • w))
        (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1)))) w :=
      hLd.comp w haffd
    have hg : HasFDerivAt (fun w => lam⁻¹ • (u (s + lam • w) - t))
        (lam⁻¹ • (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1))))) w :=
      (hcomp.sub_const t).const_smul lam⁻¹
    have hLeq : lam⁻¹ • (L.comp (lam • ContinuousLinearMap.id ℝ (Euclid (n + 1)))) = L := by
      ext1 e
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    rw [hLeq] at hg
    have hG : HasFDerivAt (fun w => ι w + ι' (lam⁻¹ • (u (s + lam • w) - t)))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp L) w :=
      (ι.toContinuousLinearMap.hasFDerivAt).add (ι'.toContinuousLinearMap.hasFDerivAt.comp w hg)
    have hΓd : HasFDerivAt (fun v => x + ι v + ι' (u v))
        (ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp L) (s + lam • w) :=
      ((ι.toContinuousLinearMap.hasFDerivAt (x := s + lam • w)).const_add x).add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp (s + lam • w) hLd)
    rw [hG.fderiv, hΓd.fderiv]
  -- Steps 10-11: pointwise identity and conclusion
  rw [hcur, hrestr]
  simp only [G]
  rw [harea']
  refine setIntegral_congr_fun hAmeas ?_
  intro w hw
  have hwD : w ∈ D := hAD hw
  have hv : s + lam • w ∈ ball (0 : Euclid (n + 1)) δ₁ := hwD
  simp only
  rw [hDG w hwD, h41 w]
  exact (hjac (s + lam • w) hv _).symm

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
