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

/-- **Simon Ch. 6, proof of 5.1, step 4** (with `n = m + 1`): a point `x ∈ ℝᴾ` of the lattice
`(m + 1)`-skeleton `L_{m+1}` (at least `P − (m + 1)` integer coordinates) that is not in the
`m`-skeleton `L_m` (fewer than `P − m` integer coordinates) lies on an open unit lattice
`(m + 1)`-face.  The set `J` of integer coordinates of `x` has `P = m + 1 + |J|`, so its
complement is the range of a strictly increasing `ι : Fin (m + 1) → Fin P`.  With `b = ⌊x⌋`
and `y_j = fract(x_{ι(j)})`, which lies in `(0, 1)` as `x_{ι(j)} ∉ ℤ`, coordinatewise
`b + Σⱼ yⱼ e_{ι(j)} = x`: `⌊xᵢ⌋ = xᵢ` for `i ∈ J`, `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j₀)`. -/
theorem Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) = x := by
  classical
  rintro P m x ⟨s, hsP, hs⟩ hnot
  -- Step 1: the set `J` of integer coordinates of `x`
  obtain ⟨J, hJ⟩ : ∃ J : Finset (Fin P), ∀ i, i ∈ J ↔ ∃ z : ℤ, x i = z :=
    ⟨Finset.univ.filter fun i => ∃ z : ℤ, x i = z, fun i => by simp⟩
  -- Steps 2–4: `s ⊆ J` gives `P ≤ m + 1 + |J|`, and `J` itself is not admissible in (ii), so
  -- `m + |J| < P`; hence `|Jᶜ| = P − |J| = m + 1`
  have hcard : Jᶜ.card = m + 1 := by
    have h1 : s.card ≤ J.card := Finset.card_le_card fun i hi => (hJ i).2 (hs i hi)
    have h2 : ¬ P ≤ m + J.card := fun h => hnot ⟨J, h, fun i hi => (hJ i).1 hi⟩
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  -- Step 5: the increasing enumeration `ι` of `Jᶜ`
  obtain ⟨ι, hιmono, hιJ, hιrange⟩ : ∃ ι : Fin (m + 1) → Fin P,
      StrictMono ι ∧ (∀ j, ι j ∉ J) ∧ ∀ i, i ∉ J → ∃ j, ι j = i := by
    refine ⟨Jᶜ.orderEmbOfFin hcard, (Jᶜ.orderEmbOfFin hcard).strictMono,
      fun j => Finset.mem_compl.1 (Jᶜ.orderEmbOfFin_mem hcard j), fun i hi => ?_⟩
    have hrange : i ∈ Set.range (Jᶜ.orderEmbOfFin hcard) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_compl.2 hi
    exact hrange
  -- Steps 6–7: `p = (ι, ⌊x⌋)` and `y_j = fract(x_{ι(j)}) ∈ (0, 1)`, since `x_{ι(j)} ∉ ℤ`
  refine ⟨(ι, fun i => ⌊x i⌋), WithLp.toLp 2 fun j => Int.fract (x (ι j)), hιmono,
    fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [PiLp.toLp_apply]
    exact Int.fract_pos.2 fun h => hιJ j ((hJ (ι j)).2 ⟨_, h⟩)
  · rw [PiLp.toLp_apply]
    exact Int.fract_lt_one _
  -- Step 8: the `i`-th coordinate is `⌊xᵢ⌋ + Σⱼ [i = ι(j)] fract(x_{ι(j)}) = xᵢ`
  refine PiLp.ext fun i => ?_
  simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hi : i ∈ J
  · -- (a) `i ∈ J`: no `ι(j)` equals `i`, and `⌊xᵢ⌋ = xᵢ` as `xᵢ ∈ ℤ`
    obtain ⟨z, hz⟩ := (hJ i).1 hi
    rw [Finset.sum_eq_zero, add_zero, hz, Int.floor_intCast]
    exact fun j _ => ite_eq_right fun h : i = ι j => hιJ j (h ▸ hi)
  · -- (b) `i = ι(j₀)`: only the `j₀` summand survives, and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ`
    obtain ⟨j₀, rfl⟩ := hιrange i hi
    rw [Finset.sum_eq_single j₀, ite_eq_left rfl, Int.floor_add_fract]
    · exact fun j _ hj => ite_eq_right fun h => hj (hιmono.injective h.symm)
    · exact fun h => absurd (Finset.mem_univ j₀) h
/-- Only finitely many unit lattice faces `b + Σⱼ [0, 1] e_{ι(j)}` (`b ∈ ℤᴾ`, `ι : Fin k → Fin P`
arbitrary) meet a compact `K ⊆ ℝᴾ` (Simon Ch. 6, §5).  If `‖x‖ ≤ ρ` on `K` and
`Φ(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` with `y ∈ [0, 1]ᵏ`, then `Φ(y)ᵢ = bᵢ + Sᵢ` with `0 ≤ Sᵢ ≤ k`
and `|Φ(y)ᵢ| ≤ ρ`, so `|bᵢ| ≤ ⌈ρ⌉ + k`: the set lies in the finite set `(all ι) × [-N, N]ᴾ`. -/
theorem Submission.dimred_mbl_dtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ K}.Finite := by
  intro P k K hK
  -- `K` is bounded: `‖x‖ ≤ ρ` for `x ∈ K`
  obtain ⟨ρ, hρ⟩ := hK.isBounded.exists_norm_le
  -- the set lies in `(Fin k → Fin P) × [-N, N]ᴾ`, `N = ⌈ρ⌉ + k`, which is finite
  refine (Set.finite_univ.prod (Set.Finite.pi fun _ =>
    Set.finite_Icc (-(⌈ρ⌉ + k)) (⌈ρ⌉ + k))).subset ?_
  rintro ⟨ι, b⟩ ⟨y, hy, hxK⟩
  refine ⟨Set.mem_univ _, fun i _ => ?_⟩
  -- coordinate formula `Φ(y)ᵢ = bᵢ + Sᵢ`, `Sᵢ = Σⱼ [i = ι j] yⱼ`
  have hcoord : (WithLp.toLp 2 (fun i => (b i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) i =
      (b i : ℝ) + ∑ j, if i = ι j then y j else 0 := by
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  -- `|bᵢ + Sᵢ| = |Φ(y)ᵢ| ≤ ‖Φ(y)‖ ≤ ρ`
  have hxi : |(b i : ℝ) + ∑ j, if i = ι j then y j else 0| ≤ ρ := by
    rw [← hcoord, ← Real.norm_eq_abs]
    exact (PiLp.norm_apply_le _ i).trans (hρ _ hxK)
  -- `0 ≤ Sᵢ ≤ k`: each of the `k` summands lies in `[0, 1]`
  have hS0 : 0 ≤ ∑ j, if i = ι j then y j else 0 :=
    Finset.sum_nonneg fun j _ => by split_ifs <;> linarith [(hy j).1]
  have hS1 : (∑ j, if i = ι j then y j else 0) ≤ k :=
    calc (∑ j, if i = ι j then y j else 0) ≤ ∑ _j : Fin k, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by split_ifs <;> linarith [(hy j).2]
      _ = k := by simp
  -- hence `-(⌈ρ⌉ + k) ≤ bᵢ ≤ ⌈ρ⌉ + k`
  obtain ⟨h1, h2⟩ := abs_le.mp hxi
  have hc := Int.le_ceil ρ
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · have : ((-(⌈ρ⌉ + k) : ℤ) : ℝ) ≤ b i := by push_cast; linarith
    exact_mod_cast this
  · have : (b i : ℝ) ≤ ((⌈ρ⌉ + k : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
/-- **Simon Ch. 6, 1.1, 3.1 and Ch. 3, 1.4**: on a Borel set `E` lying in the coordinate `n`-plane
`{a : aᵢ = cᵢ for i ∉ range ι}`, the orientation `ξ` of an integer multiplicity triple
`(M, θ, ξ)` in an open `U` is `Hⁿ`-a.e. on `M ∩ E` a Borel sign `σ ∈ {−1, 0, 1}` times the
coordinate `n`-vector `e_ι = e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`, `⟨α, e_ι⟩ = α(e_{ι(1)}, …, e_{ι(n)})`.
This is assumed: (IMC-b) the restriction of `(M, θ, ξ)` to `M ∩ E` is a triple with the same
`ξ`; (PO) a unit orientation of an approximate tangent plane at `x` of a set whose points agree
with `x` off `range ι` is `±e_ι`.  By (IMC-b), `ξ(x)` orients an approximate tangent plane of
`M ∩ E` at `Hⁿ`-a.e. `x ∈ M ∩ E`; points of `E` agree with `x` off `range ι`, so (PO) gives
`ξ(x) = ±e_ι`.  For a strongly measurable version `ξ̃` of `ξ`, `σ = 1` on `{ξ̃ = e_ι}`,
`σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}` and `σ = 0` elsewhere is Borel (the operator-norm topology
on `n`-vectors is metrizable), and `ξ = ξ̃ = σ e_ι` `Hⁿ`-a.e. on `M ∩ E`. -/
theorem Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ι : Fin n → Fin P) (c : Euclid P) (E : Set (Euclid P)), IsOpen U → StrictMono ι → MeasurableSet E → (∀ a ∈ E, ∀ i, (∀ j, ι j ≠ i) → a i = c i) → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
  classical
  intro hIMC hPO P n U R ι c E hU hι hE hEc
  have hME : MeasurableSet (R.carrier ∩ E) := R.measurableSet_carrier.inter hE
  -- (IMC-b): the restriction `R'` of `R` to `M ∩ E` keeps `ξ`, so `Hⁿ`-a.e. on `M ∩ E`, `ξ(x)`
  -- orients an approximate tangent plane of `M ∩ E` at `x`
  obtain ⟨_, R', _, hR'c, _, hR'o⟩ := hIMC P n U R E hU hE
  have h1 := R'.orients
  rw [hR'c, hR'o] at h1
  -- (PO): `ξ(x) = ±e_ι` a.e. on `M ∩ E`, as all points of `E` agree with `x` off `range ι`
  have h2 : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)),
      (∀ α : Covector (Euclid P) n,
        R.orient x α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨
      ∀ α : Covector (Euclid P) n,
        R.orient x α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    filter_upwards [h1, ae_restrict_mem hME] with x hxQ hx
    obtain ⟨Q, hQ, hξQ⟩ := hxQ
    refine hPO P n ι (R.carrier ∩ E) x Q (R.orient x) hι (fun a ha i hi => ?_) hQ hξQ
    rw [hEc a ha.2 i hi, hEc x hx.2 i hi]
  -- a strongly measurable version `ξ̃` of `ξ`; `ξ = ξ̃` a.e. on `M`, hence on `M ∩ E`
  obtain ⟨ξt, hξt, h3⟩ : ∃ ξt : Euclid P → MultiVector P n, StronglyMeasurable ξt ∧
      R.orient =ᵐ[μHE[n].restrict R.carrier] ξt :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  have h3' : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ E)), R.orient x = ξt x :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left h3
  -- the coordinate `n`-vector `e_ι`
  obtain ⟨e, he⟩ : ∃ e : MultiVector P n, ∀ α : Covector (Euclid P) n,
      e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) :=
    ⟨ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _, fun α => rfl⟩
  -- the operator-norm topology on `n`-vectors is metrizable, so `{ξ̃ = ±e_ι}` are Borel
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    ⟨⟨(inferInstance : PseudoMetricSpace (MultiVector P n)).toUniformSpace, rfl,
      @EMetric.instIsCountablyGeneratedUniformity _
        (inferInstance : PseudoMetricSpace (MultiVector P n)).toPseudoEMetricSpace⟩⟩
  have hm1 : MeasurableSet {x | ξt x = e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  have hm2 : MeasurableSet {x | ξt x = -e} := hξt.measurableSet_eq_fun stronglyMeasurable_const
  -- `σ = 1` on `{ξ̃ = e_ι}`, `σ = −1` on `{ξ̃ ≠ e_ι, ξ̃ = −e_ι}`, `σ = 0` elsewhere
  refine ⟨fun x => if ξt x = e then 1 else if ξt x = -e then -1 else 0,
    Measurable.ite hm1 measurable_const (Measurable.ite hm2 measurable_const measurable_const),
    fun x => ?_, ?_⟩
  · dsimp only
    split_ifs <;> simp
  · filter_upwards [h2, h3'] with x hx hxt α
    rcases hx with h | h
    · -- `ξ(x) = e_ι`, so `ξ̃(x) = e_ι` and `σ(x) = 1`
      have hte : ξt x = e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => (h β).trans (he β).symm)
      rw [ite_eq_left hte, h α, Int.cast_one, one_mul]
    · -- `ξ(x) = −e_ι`, so `ξ̃(x) = −e_ι`; `σ(x) = 1` only if also `ξ̃(x) = e_ι`
      have hte : ξt x = -e :=
        hxt.symm.trans (ContinuousLinearMap.ext fun β => by rw [h β, neg_apply, he β])
      by_cases hte' : ξt x = e
      · rw [ite_eq_left hte', Int.cast_one, one_mul, hxt, hte', he α]
      · rw [ite_eq_right hte', ite_eq_left hte, Int.cast_neg, Int.cast_one, neg_one_mul, h α]

/-- **Simon Ch. 6, proof of 5.1, (27)–(28) (p. 167)**, on one open face of the unit lattice: let
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` be an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  Then
`τ(M, θ, ξ)⌞F̆`, pulled back to `Q₁`, is `u(y) ⟨ω(Φ_p(y)), e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}⟩ dy` for an
integer-valued `u ∈ L¹(Q₁)` with `∫_{Q₁} |u| ≤ μ_V(F̆)`.  `F̆` is Borel and lies in the coordinate
plane through `b`, so `coordinate_plane_orientation_sign` gives `ξ = σ e_{ι(0)} ∧ ⋯ ∧ e_{ι(n−1)}`
`Hⁿ`-a.e. on `M ∩ F̆`, with `σ` integer-valued and `|σ| ≤ 1`.  Take `u = (1_M θ σ) ∘ Φ_p`: isometry
invariance of `μHE` and `μHE = Lⁿ` on `ℝⁿ` give `Hⁿ⌞F̆ = Φ_p#(Lⁿ⌞Q₁)`, and `μ_V(F̆) < ∞` because
`F̆` lies in the compact set `Φ_p([0, 1]ⁿ)`. -/
theorem Submission.dimred_mbl_dtfrsd_face_density : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) → (∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ)))) → ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} ∧ ENNReal.ofReal (∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∫ x in R.carrier ∩ (fun y : Euclid n => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] = ∫ y in {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, u y * (ω : DifferentialForm (Euclid P) n) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro hIMC hPO P n R p hι hiso
  -- name the parametrization `Φ = Φ_p`, the open cube `Q₁` and the frame `Ep = E_p`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid n → Euclid P, Φ = fun y : Euclid n =>
      WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Set (Euclid n), Q₁ = {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1} :=
    ⟨_, rfl⟩
  obtain ⟨Ep, hEp⟩ : ∃ Ep : Fin n → Euclid P,
      Ep = fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) :=
    ⟨_, rfl⟩
  have hΦiso : Isometry Φ := by rw [hΦ]; exact hiso
  suffices H : ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u Q₁ ∧
      ENNReal.ofReal (∫ y in Q₁, |u y|) ≤ R.measure (Φ '' Q₁) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) n,
        ∫ x in R.carrier ∩ Φ '' Q₁,
            (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] =
          ∫ y in Q₁, u y * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep by
    subst hΦ hQ₁ hEp
    exact H
  -- `Q₁` is open, `Φ` is a measurable embedding (an isometry), so `F̆ = Φ(Q₁)` is Borel
  have hQ₁meas : MeasurableSet Q₁ := by
    have hopen : IsOpen Q₁ := by
      have : Q₁ = ⋂ i, {y : Euclid n | 0 < y i ∧ y i < 1} := by
        rw [hQ₁]; ext y; simp
      rw [this]
      refine isOpen_iInter_of_finite fun i => ?_
      have hc : Continuous fun y : Euclid n => y i := by fun_prop
      exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
    exact hopen.measurableSet
  have hΦme : MeasurableEmbedding Φ := hΦiso.isClosedEmbedding.measurableEmbedding
  have hFmeas : MeasurableSet (Φ '' Q₁) := hΦme.measurableSet_image.2 hQ₁meas
  have hMmeas : MeasurableSet R.carrier := R.measurableSet_carrier
  -- `F̆` lies in the coordinate plane through `b`: `aᵢ = bᵢ` for `a ∈ F̆` and `i ∉ range ι`
  have hplane : ∀ a ∈ Φ '' Q₁, ∀ i, (∀ j, p.1 j ≠ i) →
      a i = (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) : Euclid P) i := by
    rintro a ⟨y, -, rfl⟩ i hi
    rw [hΦ]
    simp [Ne.symm (hi _)]
  -- `ξ = σ E_p`, `|σ| ≤ 1`, `Hⁿ`-a.e. on `M ∩ F̆`
  obtain ⟨σ, hσmeas, hσle, hσae⟩ :=
    Submission.dimred_mbl_dtfrsd_coordinate_plane_orientation_sign hIMC hPO P n univ R p.1
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (Φ '' Q₁) isOpen_univ hι hFmeas hplane
  rw [← hEp] at hσae
  -- change of variables: `Hⁿ⌞F̆ = Φ#(Lⁿ⌞Q₁)`
  have hrestr : μHE[n].restrict (Φ '' Q₁) =
      Measure.map Φ ((volume : Measure (Euclid n)).restrict Q₁) := by
    rw [← Measure.restrict_restrict_of_subset (image_subset_range Φ Q₁),
      ← hΦiso.map_euclideanHausdorffMeasure, EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      hΦme.restrict_map, hΦme.injective.preimage_image]
  have hcov : ∀ f : Euclid P → ℝ, ∫ x in Φ '' Q₁, f x ∂μHE[n] = ∫ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.integral_map]
  have hlcov : ∀ f : Euclid P → ℝ≥0∞, ∫⁻ x in Φ '' Q₁, f x ∂μHE[n] = ∫⁻ y in Q₁, f (Φ y) := by
    intro f
    rw [hrestr, hΦme.lintegral_map]
  -- the density `g = 1_M θ σ` (so `u = g ∘ Φ`) and the weight `θ' = 1_M θ`
  obtain ⟨g, hg⟩ : ∃ g : Euclid P → ℝ,
      g = R.carrier.indicator (fun x => (R.mult x : ℝ) * (σ x : ℝ)) := ⟨_, rfl⟩
  obtain ⟨θ', hθ'⟩ : ∃ θ' : Euclid P → ℝ≥0∞,
      θ' = R.carrier.indicator (fun x => (R.mult x : ℝ≥0∞)) := ⟨_, rfl⟩
  have hgM : ∀ x ∈ R.carrier, g x = (R.mult x : ℝ) * (σ x : ℝ) := fun x hx => by
    rw [hg]; exact indicator_of_mem hx _
  have hg0 : ∀ x ∉ R.carrier, g x = 0 := fun x hx => by
    rw [hg]; exact indicator_of_notMem hx _
  have hgmeas : Measurable g := by
    rw [hg]
    refine Measurable.indicator ?_ hMmeas
    exact ((Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).mul
      ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp hσmeas)
  have hgint : ∀ x, ∃ z : ℤ, g x = z := by
    intro x
    by_cases hx : x ∈ R.carrier
    · exact ⟨(R.mult x : ℤ) * σ x, by rw [hgM x hx]; push_cast; ring⟩
    · exact ⟨0, by rw [hg0 x hx]; simp⟩
  have hgle : ∀ x, ENNReal.ofReal |g x| ≤ θ' x := by
    intro x
    by_cases hx : x ∈ R.carrier
    · rw [hgM x hx, hθ', indicator_of_mem hx, abs_mul, Nat.abs_cast]
      have h1 : |(σ x : ℝ)| ≤ 1 := by exact_mod_cast hσle x
      calc ENNReal.ofReal ((R.mult x : ℝ) * |(σ x : ℝ)|) ≤ ENNReal.ofReal (R.mult x : ℝ) :=
            ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (Nat.cast_nonneg _) h1)
        _ = (R.mult x : ℝ≥0∞) := ENNReal.ofReal_natCast _
    · rw [hg0 x hx, hθ', indicator_of_notMem hx]; simp
  -- `μ_V(F̆) = ∫_{F̆} 1_M θ dHⁿ = ∫_{Q₁} θ' ∘ Φ`
  have hmass : R.measure (Φ '' Q₁) = ∫⁻ y in Q₁, θ' (Φ y) := by
    rw [← hlcov θ', hθ', IMRep.measure, ← withDensity_indicator hMmeas,
      withDensity_apply _ hFmeas]
  -- `μ_V(F̆) ≤ μ_V(Φ([0, 1]ⁿ)) < ∞` by local integrability of `θ`
  have hfin : R.measure (Φ '' Q₁) < ∞ := by
    obtain ⟨C, hCc, hQC⟩ : ∃ C : Set (Euclid n), IsCompact C ∧ Q₁ ⊆ C := by
      refine ⟨WithLp.toLp 2 '' (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1),
        (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _), ?_⟩
      intro y hy
      rw [hQ₁] at hy
      exact ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
    have hKc : IsCompact (Φ '' C) := hCc.image hΦiso.continuous
    have hKfin : R.measure (Φ '' C) ≠ ∞ := by
      rw [IMRep.measure, withDensity_apply _ hKc.measurableSet,
        Measure.restrict_restrict hKc.measurableSet, inter_comm]
      exact R.locallyIntegrable_mult _ hKc (subset_univ _)
    exact lt_of_le_of_lt (measure_mono (image_mono hQC)) hKfin.lt_top
  -- integrability of `u = g ∘ Φ` on `Q₁` and `∫_{Q₁} |u| ≤ μ_V(F̆)`
  have hlint : ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| ≤ R.measure (Φ '' Q₁) := by
    rw [hmass]
    exact lintegral_mono fun y => hgle (Φ y)
  have huint : Integrable (fun y => g (Φ y)) ((volume : Measure (Euclid n)).restrict Q₁) := by
    refine ⟨(hgmeas.comp hΦiso.continuous.measurable).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hlint hfin
  refine ⟨fun y => g (Φ y), fun y => hgint (Φ y), huint, ?_, fun ω => ?_⟩
  · exact (ofReal_integral_eq_lintegral_ofReal huint.abs
      (Eventually.of_forall fun y => abs_nonneg _)).trans_le hlint
  -- `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{F̆} g ω(E_p) dHⁿ = ∫_{Q₁} u ω(Φ ·)(E_p)`
  calc ∫ x in R.carrier ∩ Φ '' Q₁,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]
      = ∫ x in R.carrier ∩ Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine integral_congr_ae ?_
        filter_upwards [hσae, ae_restrict_mem (hMmeas.inter hFmeas)] with x hx hxm
        rw [hx, hgM x hxm.1]
        ring
    _ = ∫ x in Φ '' Q₁, g x * (ω : DifferentialForm (Euclid P) n) x Ep ∂μHE[n] := by
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hFmeas inter_subset_right
          ?_).symm
        intro x hx
        rw [hg0 x (fun h => hx.2 ⟨h, hx.1⟩), zero_mul]
    _ = ∫ y in Q₁, g (Φ y) * (ω : DifferentialForm (Euclid P) n) (Φ y) Ep :=
        hcov (fun x => g x * (ω : DifferentialForm (Euclid P) n) x Ep)
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
/-- **Disjoint neighbourhoods of the open unit faces** (Simon Ch. 6, §5, proof of 5.1, step 1: the
interiors `F̆` of the faces get pairwise disjoint neighbourhoods).  For `p = (ι, b)` with `ι`
strictly increasing let `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, and for `t ∈ (0,1)ᵏ` let `B_p(t)` be the set
of `x` with `2|x − Φ_p(t)| < 1` and `2|x − Φ_p(t)| < min(tⱼ, 1 − tⱼ)` for all `j`.  Then
`N_p = ⋃_{t ∈ (0,1)ᵏ} B_p(t)` is a union of finite intersections of open sets, hence open, and it
contains `Φ_p((0,1)ᵏ)` (take `t = y`).  The separation hypothesis gives
`2|x − Φ_p(t)| < |Φ_p(t) − Φ_q(y')|` for `x ∈ B_p(t)`, `q ≠ p` and `y' ∈ [0,1]ᵏ`.  For
`x = Φ_q(y')` this reads `2|x − Φ_p(t)| < |x − Φ_p(t)|`, so `Φ_q([0,1]ᵏ)` misses `N_p`; for
`x ∈ B_p(t) ∩ B_q(t')` the bounds for `(p, q, t, t')` and `(q, p, t', t)` contradict the triangle
inequality. -/
theorem Submission.dimred_mbl_dtfrbv_face_neighbourhoods : ∀ (P k : ℕ), (∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) → ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → IsOpen (N p) ∧ (∀ y : Euclid k, (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N p) ∧ ∀ q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono q.1 → q ≠ p → (∀ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∉ N p) ∧ Disjoint (N p) (N q) := by
  intro P k hS
  -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P, ∀ p y,
      Φ p y = WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hΦ] at hS ⊢
  -- step 1: `B_p(t) = {x : 2|x − Φ_p t| < 1, 2|x − Φ_p t| < min(tⱼ, 1 − tⱼ) ∀ j}` and
  -- `N_p = ⋃_{t ∈ (0,1)ᵏ} B_p(t)`
  obtain ⟨B, hB⟩ : ∃ B : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Set (Euclid P), ∀ p t,
      B p t = {x | 2 * dist x (Φ p t) < 1} ∩
        ⋂ j, {x | 2 * dist x (Φ p t) < min (t j) (1 - t j)} := ⟨_, fun _ _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p,
      N p = ⋃ t ∈ {t : Euclid k | ∀ j, 0 < t j ∧ t j < 1}, B p t := ⟨_, fun _ => rfl⟩
  -- step 4: `2|x − Φ_p t| < |Φ_p t − Φ_q y'|` for `x ∈ B_p(t)`, `q ≠ p` and `y' ∈ [0,1]ᵏ`
  have hkey : ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q →
      ∀ t : Euclid k, (∀ j, 0 < t j ∧ t j < 1) → ∀ y' : Euclid k, (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) →
        ∀ x ∈ B p t, 2 * dist x (Φ p t) < dist (Φ p t) (Φ q y') := by
    intro p q hp hq hpq t ht y' hy' x hx
    simp only [hB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx
    rcases hS p q hp hq hpq t y' ht hy' with h | ⟨j, h⟩
    · exact lt_of_lt_of_le hx.1 h
    · exact lt_of_lt_of_le (hx.2 j) h
  refine ⟨N, fun p hp => ⟨?_, fun y hy => ?_, fun q hq hqp => ⟨fun y hy hx => ?_, ?_⟩⟩⟩
  · -- step 2: each `B_p(t)` is a finite intersection of open sets `{x : 2|x − Φ_p t| < c}`
    rw [hN]
    refine isOpen_biUnion fun t _ => ?_
    have hd : Continuous fun x : Euclid P => 2 * dist x (Φ p t) :=
      continuous_const.mul (continuous_id.dist continuous_const)
    rw [hB]
    exact (isOpen_lt hd continuous_const).inter
      (isOpen_iInter_of_finite fun j => isOpen_lt hd continuous_const)
  · -- step 3: `Φ_p(y) ∈ B_p(y)`, as `|Φ_p y − Φ_p y| = 0 < min(yⱼ, 1 − yⱼ)`
    rw [hN]
    refine Set.mem_biUnion (show y ∈ {t : Euclid k | ∀ j, 0 < t j ∧ t j < 1} from hy) ?_
    simp only [hB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, dist_self, mul_zero]
    exact ⟨one_pos, fun j => lt_min (hy j).1 (sub_pos.mpr (hy j).2)⟩
  · -- step 5: for `x = Φ_q(y) ∈ B_p(t)`, step 4 with `y' = y` gives `2|x − Φ_p t| < |x − Φ_p t|`
    rw [hN] at hx
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
    rw [Set.mem_ofPred_eq] at ht
    have h := hkey p q hp hq hqp.symm t ht y hy (Φ q y) hxt
    rw [dist_comm (Φ p t)] at h
    linarith [dist_nonneg (x := Φ q y) (y := Φ p t)]
  · -- step 6: step 4 for `(p, q, t, t')` and `(q, p, t', t)` contradicts the triangle inequality
    rw [Set.disjoint_left]
    intro x hxp hxq
    rw [hN] at hxp hxq
    obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxp
    obtain ⟨t', ht', hxt'⟩ := Set.mem_iUnion₂.mp hxq
    rw [Set.mem_ofPred_eq] at ht ht'
    have h₁ := hkey p q hp hq hqp.symm t ht t' (fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩) x hxt
    have h₂ := hkey q p hq hp hqp t' ht' t (fun i => ⟨(ht i).1.le, (ht i).2.le⟩) x hxt'
    have h₃ := dist_triangle (Φ p t) x (Φ q t')
    linarith [dist_comm (Φ p t) x, dist_comm (Φ q t') (Φ p t)]
/-- Local mass is superadditive over a finite pairwise disjoint family (Simon 6.2.5; the summation
over faces in the proof of 6.5.1): `∑_{i ∈ s} M_{N_i}(S) ≤ M_W(S)` for `W = ⋃_{i ∈ s} N_i`.
Forms `ω_i` admissible for the pairwise disjoint `N_i` have at most one nonzero value at each
point, so `∑_{i ∈ s} ω_i` is admissible for `W`, and `S(∑ ω_i) = ∑ S(ω_i)`.  Choosing `ω_i` with
`S(ω_i) ≥ 0` and `M_{N_i}(S) ≤ S(ω_i) + ε / #s`, and letting `ε → 0`, gives the inequality. -/
theorem Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ι : Type) (s : Finset ι) (N : ι → Set (Euclid P)), (↑s : Set ι).PairwiseDisjoint N → ∑ i ∈ s, S.massOn (N i) ≤ S.massOn (⋃ i ∈ s, N i) := by
  classical
  intro P n U S ι s N hN
  -- gluing: forms admissible for the pairwise disjoint `N i` sum to a form admissible for `W`
  have hglue : ∀ ω : ι → TestFormOn U n, (∀ i ∈ s, ω i ∈ massAdmissibleOn U n (N i)) →
      (∑ i ∈ s, ω i) ∈ massAdmissibleOn U n (⋃ i ∈ s, N i) := by
    intro ω hω
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_sum, Finset.sum_fn]
      have hsupp : support (fun x => ∑ i ∈ s, (ω i : DifferentialForm (Euclid P) n) x) ⊆
          ⋃ i ∈ s, tsupport (ω i : DifferentialForm (Euclid P) n) :=
        (Finset.support_sum s fun i => (ω i : DifferentialForm (Euclid P) n)).trans
          (iUnion₂_mono fun i _ => subset_tsupport _)
      exact (closure_minimal hsupp (isClosed_biUnion_finset fun i _ => isClosed_tsupport _)).trans
        (iUnion₂_mono fun i hi => (hω i hi).1)
    · rw [Submodule.coe_sum, Finset.sum_apply]
      by_cases hx : ∃ i ∈ s, x ∈ tsupport (ω i : DifferentialForm (Euclid P) n)
      · -- `x` lies in at most one `N i`, so at most one summand is nonzero at `x`
        obtain ⟨i, hi, hxi⟩ := hx
        rw [Finset.sum_eq_single i (fun j hj hji => image_eq_zero_of_notMem_tsupport fun hxj =>
          Set.disjoint_left.1 (hN hj hi hji) ((hω j hj).1 hxj) ((hω i hi).1 hxi))
          (fun h => absurd hi h)]
        exact (hω i hi).2 x
      · rw [Finset.sum_eq_zero fun i hi =>
          image_eq_zero_of_notMem_tsupport fun hxi => hx ⟨i, hi, hxi⟩, covectorEuclideanNorm_zero]
        exact zero_le_one
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hW => ?_
  have hδ : (ε : ℝ≥0∞) / s.card ≠ 0 :=
    ENNReal.div_ne_zero.2 ⟨ENNReal.coe_ne_zero.2 hε.ne', ENNReal.natCast_ne_top _⟩
  -- near-optimal forms: `S(ω_i) ≥ 0` and `M_{N_i}(S) ≤ S(ω_i) + ε / #s`
  have happrox : ∀ i ∈ s, ∃ ω ∈ massAdmissibleOn U n (N i), 0 ≤ S ω ∧
      S.massOn (N i) ≤ ENNReal.ofReal (S ω) + (ε : ℝ≥0∞) / s.card := by
    intro i hi
    by_cases h0 : S.massOn (N i) = 0
    · exact ⟨0, ⟨by simp, fun x => by simp⟩, by simp, by simp [h0]⟩
    have hfin : S.massOn (N i) ≠ ∞ :=
      ((S.massOn_mono (Finset.subset_set_biUnion_of_mem (f := N) hi)).trans_lt hW).ne
    obtain ⟨_, ⟨ω, hω, rfl⟩, hlt⟩ := lt_sSup_iff.1 (ENNReal.sub_lt_self hfin h0 hδ)
    exact ⟨ω, hω, (ENNReal.ofReal_pos.1 (zero_le.trans_lt hlt)).le,
      tsub_le_iff_right.1 hlt.le⟩
  choose! ω hω hpos happ using happrox
  calc ∑ i ∈ s, S.massOn (N i)
      ≤ ∑ i ∈ s, (ENNReal.ofReal (S (ω i)) + (ε : ℝ≥0∞) / s.card) := Finset.sum_le_sum happ
    _ = ENNReal.ofReal (S (∑ i ∈ s, ω i)) + s.card * ((ε : ℝ≥0∞) / s.card) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, map_sum,
        ENNReal.ofReal_sum_of_nonneg hpos]
    _ ≤ S.massOn (⋃ i ∈ s, N i) + ε := add_le_add (S.le_massOn (hglue ω hω)) ENNReal.mul_div_le
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

/-- **Admissible test form with prescribed values on a face** (Simon Ch. 6, proof of the
deformation theorem 5.1, displays (26)–(28), with the test forms of 2.35).  Let
`Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` be the chart of the face `p = (ι, b)` and
`π(x) = (x_{ι(j)} − b_{ι(j)})ⱼ` its affine left inverse.  The compact set `K = Φ_p(spt g) ⊆ N`
has `cthickening δ K ⊆ N` for some `δ > 0`, and a smooth `χ : ℝᴾ → [0, 1]` with support
`thickening δ K` equals `1` exactly on `K`.  So `G = χ · (g ∘ π)` is smooth, compactly supported
in `N`, bounded by `1`, and `G ∘ Φ_p = g`.  With the face covectors `εⱼ` of `ι`
(`Submission.cmcdtfrbv_face_covectors`), `γ(x) = Σⱼ Gⱼ(x) εⱼ` is a test form with
`tsupport γ ⊆ N` and `|γ(x)| = ‖G x‖ ≤ 1`, and `γ(Φ_p y)(e_{ι ∘ i.succAbove}) = (-1)ⁱ gᵢ(y)`. -/
theorem Submission.dimred_mbl_dtfrbv_face_test_form : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ γ : TestFormOn (univ : Set (Euclid P)) m, tsupport (γ : DifferentialForm (Euclid P) m) ⊆ N ∧ (∀ x, covectorEuclideanNorm ((γ : DifferentialForm (Euclid P) m) x) ≤ 1) ∧ ∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), g y i = (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m) (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)) := by
  intro P m p N g hι hN hΦN hg hgc hgQ hg1
  -- Step 1: the face chart `Φ_p`, its affine left inverse `π = L - c₀`, and `π ∘ Φ_p = id`
  -- (the `ι(j)`-th coordinate of `Φ_p y` is `b_{ι(j)} + yⱼ`, as `ι` is injective)
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  let L : Euclid P →L[ℝ] Euclid (m + 1) := LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (p.1 j))
      map_add' := fun x x' => by ext j; simp
      map_smul' := fun c x => by ext j; simp }
  have hL : ∀ x, L x = WithLp.toLp 2 (fun j => x (p.1 j)) := fun x => rfl
  let c₀ : Euclid (m + 1) := WithLp.toLp 2 (fun j => (p.2 (p.1 j) : ℝ))
  let π : Euclid P → Euclid (m + 1) := fun x => L x - c₀
  have hπΦ : ∀ y, π (Φ y) = y := by
    intro y
    ext j
    simp [π, hL, c₀, Φ, Pi.single_apply, hι.injective.eq_iff]
  have hΦc : Continuous Φ := by fun_prop
  have hπc : ContDiff ℝ (⊤ : ℕ∞) π := L.contDiff.sub contDiff_const
  -- Step 2: `K = Φ_p(spt g)` is a compact subset of `N`, so `cthickening δ K ⊆ N` for some `δ > 0`
  have hKc : IsCompact (Φ '' tsupport g) := hgc.isCompact.image hΦc
  have hKN : Φ '' tsupport g ⊆ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact hΦN y (hgQ hy)
  obtain ⟨δ, hδ, hδN⟩ := hKc.exists_cthickening_subset_open hN hKN
  -- Step 3: smooth `χ` with values in `[0, 1]`, support `thickening δ K` and `χ = 1` exactly on
  -- `K`; so `tsupport χ ⊆ cthickening δ K ⊆ N`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := Φ '' tsupport g)) hKc.isClosed
    (self_subset_thickening hδ _)
  have hχK : tsupport χ ⊆ cthickening δ (Φ '' tsupport g) := by
    rw [tsupport, hχs]
    exact closure_thickening_subset_cthickening _ _
  -- Step 4: `G = χ · (g ∘ π)` is smooth, compactly supported in `N` and bounded by `1`, and
  -- `G ∘ Φ_p = g`, since `χ = 1` on `K` and `g = 0` off `spt g`
  obtain ⟨G, hG, hGc, hGN, hG1, hGΦ⟩ : ∃ G : Euclid P → Euclid (m + 1),
      ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ tsupport G ⊆ N ∧ (∀ x, ‖G x‖ ≤ 1) ∧
        ∀ y, G (Φ y) = g y := by
    refine ⟨fun x => χ x • g (π x), hχ.smul (hg.comp hπc), ?_, ?_, ?_, fun y => ?_⟩
    · exact hKc.cthickening.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_smul_subset_left _ _).trans hχK)
    · exact (tsupport_smul_subset_left _ _).trans (hχK.trans hδN)
    · intro x
      have hx := hχr (mem_range_self x)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hx.2).trans (hg1 _)
    · show χ (Φ y) • g (π (Φ y)) = g y
      rw [hπΦ]
      by_cases hyg : y ∈ tsupport g
      · rw [(hχ1 (Φ y)).1 (mem_image_of_mem Φ hyg), one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hyg, smul_zero]
  -- Step 5: the face covectors `εⱼ` of `ι = p.1`
  obtain ⟨ε, hεn, hεf⟩ := Submission.cmcdtfrbv_face_covectors P m p.1 hι
  -- Step 6: `γ(x) = Σⱼ Gⱼ(x) εⱼ` is smooth and `supp γ ⊆ supp G`, so `γ` is a test form on `ℝᴾ`
  -- with `tsupport γ ⊆ tsupport G ⊆ N`
  set γ : DifferentialForm (Euclid P) m := fun x => ∑ j, G x j • ε j with hγ
  have hGj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun x => G x j := fun j =>
    (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).contDiff.comp hG
  have hγs : ContDiff ℝ (⊤ : ℕ∞) γ :=
    ContDiff.sum fun j _ => (hGj j).smul contDiff_const
  have hγG : support γ ⊆ support G := by
    intro x hx
    rw [mem_support] at hx ⊢
    contrapose! hx
    simp [hγ, hx]
  have hγT : IsTestForm γ ∧ tsupport γ ⊆ (univ : Set (Euclid P)) :=
    ⟨⟨hγs, hGc.mono hγG⟩, subset_univ _⟩
  refine ⟨⟨γ, hγT⟩, (closure_mono hγG).trans hGN, fun x => ?_, fun y i => ?_⟩
  · -- Step 7: `|γ(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`
    calc covectorEuclideanNorm (γ x) = Real.sqrt (∑ j, G x j ^ 2) := hεn fun j => G x j
      _ = ‖G x‖ := by rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
      _ ≤ 1 := hG1 x
  · -- Step 8: `γ(Φ_p y)(e_{ι ∘ i.succAbove}) = (-1)ⁱ Gᵢ(Φ_p y) = (-1)ⁱ gᵢ(y)`, and `((-1)ⁱ)² = 1`
    have hface : γ (Φ y) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)) =
        (-1 : ℝ) ^ (i : ℕ) * G (Φ y) i :=
      hεf (fun j => G (Φ y) j) i
    show g y i = (-1 : ℝ) ^ (i : ℕ) *
      γ (Φ y) (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ))
    rw [hface, hGΦ y]
    rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> rw [h] <;> ring
/-- **Isometric images: Borel, `Hᵏ`-measure and change of variables** (for the lattice faces
`F̆_p = Φ_p(Q₁)` in the deformation theorem, Simon Ch. 6 §5).  If `Φ : ℝᵏ → ℝᴾ` is an isometry and
`A ⊆ ℝᵏ` is Borel, then `Φ(A)` is Borel, `Hᵏ(Φ(A)) = Lᵏ(A)`, and
`∫_{Φ(A)} h dHᵏ = ∫_A h(Φ(y)) dy` for every `h : ℝᴾ → ℝ` (Bochner integrals: no integrability of
`h` is needed).  `Φ` is a closed, hence measurable, embedding; `Hᵏ` is isometry invariant and equals
`Lᵏ` on `ℝᵏ`; and `Φ_#Hᵏ = Hᵏ⌞range Φ` restricts to `Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A)`. -/
theorem Submission.dimred_mbl_dtfrpi_isometry_image_integral : ∀ (P k : ℕ) (Φ : Euclid k → Euclid P) (A : Set (Euclid k)), Isometry Φ → MeasurableSet A → MeasurableSet (Φ '' A) ∧ μHE[k] (Φ '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in Φ '' A, h x ∂μHE[k] = ∫ y in A, h (Φ y) := by
  intro P k Φ A hΦ hA
  -- step 1: `ℝᵏ` is complete, so `Φ` is a closed, hence measurable, embedding and `Φ(A)` is Borel
  have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
  have hΦA : MeasurableSet (Φ '' A) := hemb.measurableSet_image.mpr hA
  -- step 4: `Hᵏ⌞Φ(A) = (Φ_#Hᵏ)⌞Φ(A) = Φ_#(Hᵏ⌞Φ⁻¹(Φ(A))) = Φ_#(Lᵏ⌞A)`, as `Φ_#Hᵏ = Hᵏ⌞range Φ`
  have hpush : μHE[k].restrict (Φ '' A) = (volume.restrict A).map Φ := by
    have h := hemb.restrict_map μHE[k] (Φ '' A)
    rwa [hΦ.map_euclideanHausdorffMeasure, Measure.restrict_restrict hΦA,
      Set.inter_eq_left.mpr (Set.image_subset_range Φ A), Set.preimage_image_eq A hemb.injective,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume k] at h
  refine ⟨hΦA, ?_, fun h => ?_⟩
  -- steps 2-3: `Hᵏ(Φ(A)) = Hᵏ(A) = Lᵏ(A)`, by isometry invariance and `Hᵏ = Lᵏ` on `ℝᵏ`
  · rw [hΦ.euclideanHausdorffMeasure_image, EuclideanSpace.euclideanHausdorffMeasure_eq_volume k]
  -- step 5: change of variables along the measurable embedding `Φ`, valid for every `h`
  · rw [hpush, hemb.integral_map]
/-- **Simon Ch. 3, 1.4, flat case** (step 4(iii) of the proof of `dimred_mbl_dtfr_polyhedral_im`):
if `M` agrees with the affine plane `x + V` on `B_δ(x)`, i.e. `z ∈ M ⇔ z − x ∈ V` whenever
`|z − x| < δ`, then `V` is the approximate tangent space of `M` at `x`.  If `f ∈ C_c(ℝᴾ)` vanishes
off `B_R(0)`, then for `0 < r < δ/R` the blow-up `η_{x,r}(M)` agrees with `V` on `B_R(0)`, so
`∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ`: the integrals are eventually constant as `r ↓ 0`.  No
measurability of `M` is needed. -/
theorem Submission.dimred_mbl_dtfrpi_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (δ : ℝ), Module.finrank ℝ V = n → 0 < δ → (∀ z : Euclid P, dist z x < δ → (z ∈ M ↔ z - x ∈ V)) → HasApproximateTangentSpaceAt n M x V := by
  intro P n M x V δ hV hδ hM
  refine ⟨hV, fun f => ?_⟩
  -- `f` vanishes outside some ball `B(0, R)`
  obtain ⟨R₀, hR₀⟩ := f.hasCompactSupport.isBounded.subset_closedBall 0
  obtain ⟨R, hRpos, hfz⟩ : ∃ R : ℝ, 0 < R ∧ ∀ y ∉ ball (0 : Euclid P) R, f y = 0 := by
    refine ⟨max R₀ 0 + 1, by positivity,
      fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => hy ?_⟩
    have hy'' := hR₀ hy'
    rw [mem_closedBall, dist_zero_right] at hy''
    rw [mem_ball, dist_zero_right]
    linarith [le_max_left R₀ 0]
  -- restricting to the Borel ball `B(0, R)` does not change `∫ f`
  have hloc : ∀ S : Set (Euclid P),
      ∫ y in S, f y ∂μHE[n] = ∫ y in ball (0 : Euclid P) R ∩ S, f y ∂μHE[n] := by
    intro S
    rw [← Measure.restrict_restrict measurableSet_ball,
      setIntegral_eq_integral_of_forall_compl_eq_zero hfz]
  -- for `0 < r < δ / R`, `η_{x,r}(M)` agrees with `V` on `B(0, R)`
  apply (Filter.tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hRpos)] with r ⟨hr0, hrR⟩
  rw [lt_div_iff₀ hRpos] at hrR
  have hset : ball (0 : Euclid P) R ∩ Poincare.SimonGMT.Chapter03.blowUpMap x r '' M =
      ball (0 : Euclid P) R ∩ (V : Set (Euclid P)) := by
    ext y
    constructor
    · rintro ⟨hyB, z, hzM, rfl⟩
      refine ⟨hyB, V.smul_mem _ ((hM z ?_).1 hzM)⟩
      rw [mem_ball, dist_zero_right, Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul,
        norm_inv, Real.norm_of_nonneg hr0.le, inv_mul_lt_iff₀ hr0] at hyB
      rw [dist_eq_norm]
      linarith
    · rintro ⟨hyB, hyV⟩
      refine ⟨hyB, x + r • y, (hM _ ?_).2 ?_, ?_⟩
      · rw [mem_ball, dist_zero_right] at hyB
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr0.le]
        calc r * ‖y‖ ≤ r * R := by gcongr
          _ < δ := hrR
      · rw [add_sub_cancel_left]
        exact V.smul_mem r hyV
      · rw [Poincare.SimonGMT.Chapter03.blowUpMap, add_sub_cancel_left, inv_smul_smul₀ hr0.ne']
  rw [hloc (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M), hset, ← hloc]
/-- **Coordinate `k`-planes and their unit orientations** (Simon Ch. 6, (1.2), (1.7): the simple
`k`-vector `e_{i₁} ∧ ⋯ ∧ e_{iₖ}` pairs with a `k`-covector `ω` as `ω(e_{i₁}, …, e_{iₖ})`; §5: a face
`F ∈ 𝓛ₖ` of the Deformation Theorem lies in such a coordinate plane, oriented by
`±e_{i₁} ∧ ⋯ ∧ e_{iₖ}`).  Let `ι : Fin k → Fin P` be strictly increasing, `τⱼ = e_{ι(j)}` and
`V = span{τⱼ}`.  The standard orthonormal basis composed with the injective `ι` is orthonormal,
hence linearly independent, so `dim V = k`.  Evaluation `α ↦ α(τ)` is linear with
`|α(τ)| ≤ ‖α‖ ∏ⱼ ‖τⱼ‖ = ‖α‖`, which gives the `k`-vector `e` with `e(α) = α(τ)`; the frame `τ`
witnesses that both `e` and `-e` are unit orientations of `V`. -/
theorem Submission.dimred_mbl_dtfrpi_coord_plane_orientation : ∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro P k ι hι
  -- step 1: `τ` is the orthonormal standard basis of `ℝᴾ` composed with the injective `ι`
  have hτ : Orthonormal ℝ (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P) :=
    EuclideanSpace.orthonormal_single.comp ι hι.injective
  -- step 2: an orthonormal family is linearly independent, so `dim V = #(Fin k) = k`
  have hV : Module.finrank ℝ (Submodule.span ℝ
      (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k := by
    rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  -- step 3: `α ↦ α(τ)` is linear (covector operations are pointwise) and bounded by `‖α‖`
  let e : MultiVector P k :=
    LinearMap.mkContinuous
      { toFun := fun α : Covector (Euclid P) k => α fun j => EuclideanSpace.single (ι j) (1 : ℝ)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl } 1
      fun α => by
        calc ‖α fun j => EuclideanSpace.single (ι j) (1 : ℝ)‖
            ≤ ‖α‖ * ∏ j, ‖(EuclideanSpace.single (ι j) (1 : ℝ) : Euclid P)‖ := α.le_opNorm _
          _ = 1 * ‖α‖ := by simp [hτ.1]
  refine ⟨hV, e, fun _ => rfl, ?_, ?_⟩
  -- step 4: the frame `τ` orients `V` with sign `+` for `e`
  · exact ⟨_, hτ, rfl, Or.inl fun _ => rfl⟩
  -- step 5: and with sign `-` for `-e`, as `(-e)(α) = -e(α)`
  · exact ⟨_, hτ, rfl, Or.inr fun _ => rfl⟩
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

/-- **Geometry of unit lattice faces** (Simon Ch. 6, §5, deformation theorem: the faces `F ∈ 𝓛ₖ`,
`Hᵏ(F̆) = 1`, `diam F ≤ √P` and Lemma 2.1, for faces of any common dimension `k`).  The open unit
cube of `ℝᵏ` has volume `1` (`cmcdtfrfg_cube_volume`).  For `p = (ι, b)` with `ι` strictly
increasing, hence injective, the face map `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry and
`|Φ_p(y) − Φ_p(y')| ≤ √P` on the closed unit cube (`cmcdtfrfg_face_isometry_diam`).  For
`p ≠ q`, `y ∈ (0,1)ᵏ` and `y' ∈ [0,1]ᵏ`, either `1 ≤ |Φ_p(y) − Φ_q(y')|` or
`min(yⱼ, 1 − yⱼ) ≤ |Φ_p(y) − Φ_q(y')|` for some `j` (`cmcdtfrfg_face_separation`). -/
theorem Submission.dimred_mbl_dtfr_face_geometry : ∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) := by
  intro P k
  -- step 1: the open unit cube has volume `1`
  refine ⟨Submission.cmcdtfrfg_cube_volume k, fun p q hp hq => ?_⟩
  -- steps 2-4: `ι` is injective, so `Φ_p` is an isometry and the closed face has diameter `≤ √P`
  obtain ⟨hiso, hdiam⟩ := Submission.cmcdtfrfg_face_isometry_diam P k p.1 p.2 hp.injective
  -- steps 5-8: distinct faces are separated
  exact ⟨hiso, hdiam, Submission.cmcdtfrfg_face_separation P k p q hp hq⟩
/-- **The `(n − 1)`-skeleton of the unit cubical lattice is `Hⁿ`-null** (Simon Ch. 6, proof of the
deformation theorem 5.1, where `spt Q ⊆ Lₙ` (22) is split over the open `n`-faces (26)–(28):
`Hⁿ(L_{n−1}) = 0`, here `n = m + 1`).  The points of `ℝᴾ` with at least `P − m` integer
coordinates lie in the countably many coordinate planes `A(s, z) = {x : xᵢ = zᵢ for i ∈ s}`,
`P ≤ m + |s|`, `z ∈ ℤᴾ`.  Each `A(s, z)` is the image of an isometry `ψ : ℝʳ → ℝᴾ`,
`r = P − |s| ≤ m`, and `ℝʳ` is `μHE[m + 1]`-null: it is a countable union of balls of finite
`μHE[r]` (= Lebesgue) measure, and `r < m + 1`. -/
theorem Submission.dimred_mbl_dtfr_skeleton_null : ∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
  intro P m
  -- (3) `ℝʳ`, `r ≤ m`, is a countable union of closed balls of finite `μHE[r]` = Lebesgue measure,
  -- so each ball, and hence `ℝʳ`, is `μHE[m + 1]`-null
  have hnull : ∀ r : ℕ, r ≤ m → (μHE[m + 1] : Measure (Euclid r)) univ = 0 := by
    intro r hr
    rw [← Metric.iUnion_closedBall_nat (0 : Euclid r)]
    refine measure_iUnion_null fun k => ?_
    refine (Measure.euclideanHausdorffMeasure_zero_or_top (d₁ := r) (d₂ := m + 1) (by omega)
      _).resolve_right ?_
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact measure_closedBall_lt_top.ne
  -- (2), (4) each plane `A(s, z)` with `P ≤ m + |s|` is the image of an isometry `ψ : ℝʳ → ℝᴾ`,
  -- `r = P − |s| ≤ m`, hence `μHE[m + 1]`-null
  have hplane : ∀ s : Finset (Fin P), P ≤ m + s.card → ∀ z : Fin P → ℤ,
      μHE[m + 1] {x : Euclid P | ∀ i ∈ s, x i = z i} = 0 := by
    intro s hs z
    obtain ⟨r, hr⟩ : ∃ r, sᶜ.card = r := ⟨_, rfl⟩
    have hrm : r ≤ m := by
      rw [← hr, Finset.card_compl, Fintype.card_fin]
      omega
    -- `κ : Fin r ↪ Fin P` enumerates the coordinates outside `s`
    obtain ⟨κ, hκs, hκ⟩ : ∃ κ : Fin r ↪ Fin P, (∀ l, κ l ∉ s) ∧ Finset.univ.map κ = sᶜ :=
      ⟨(sᶜ.orderEmbOfFin hr).toEmbedding,
        fun l => Finset.mem_compl.1 (sᶜ.orderEmbOfFin_mem hr l), sᶜ.map_orderEmbOfFin_univ hr⟩
    -- `ψ t = (zᵢ on s, 0 off s) + Σₗ tₗ e_{κ l}` has `ψ t = z` on `s` and `ψ t (κ l) = t l`
    obtain ⟨ψ, hψs, hψκ⟩ : ∃ ψ : Euclid r → Euclid P,
        (∀ t, ∀ i ∈ s, ψ t i = z i) ∧ ∀ t l, ψ t (κ l) = t l := by
      refine ⟨fun t => WithLp.toLp 2 (fun i => if i ∈ s then (z i : ℝ) else 0) +
        ∑ l, t l • EuclideanSpace.single (κ l) (1 : ℝ), fun t i hi => ?_, fun t l => ?_⟩
      · have h0 : ∀ l, i ≠ κ l := fun l h => hκs l (h ▸ hi)
        simp [hi, h0]
      · simp [Pi.single_apply, hκs l]
    -- `ψ` is an isometry: `ψ t − ψ t'` has coordinate `tₗ − t'ₗ` at `κ l` and `0` on `s`
    have hiso : Isometry ψ := by
      refine Isometry.of_dist_eq fun t t' => ?_
      rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
      congr 1
      rw [← Finset.sum_subset (Finset.subset_univ sᶜ), ← hκ, Finset.sum_map]
      · simp only [hψκ]
      · intro i _ hi
        have hi' : i ∈ s := by simpa using hi
        simp [hψs t i hi', hψs t' i hi']
    -- `A(s, z) ⊆ ψ '' univ`: `x = ψ (x ∘ κ)` for `x ∈ A(s, z)`
    have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ ψ '' univ := by
      intro x hx
      refine ⟨WithLp.toLp 2 fun l => x (κ l), mem_univ _, ?_⟩
      ext i
      by_cases hi : i ∈ s
      · rw [hψs _ i hi, hx i hi]
      · have hi' : i ∈ Finset.univ.map κ := by
          rw [hκ]
          exact Finset.mem_compl.2 hi
        obtain ⟨l, -, rfl⟩ := Finset.mem_map.1 hi'
        rw [hψκ, PiLp.toLp_apply]
    exact measure_mono_null hsub (by rw [hiso.euclideanHausdorffMeasure_image]; exact hnull r hrm)
  -- (1) `L_m ⊆ ⋃ A(s, z)` over the countably many `s` with `P ≤ m + |s|` and `z ∈ ℤᴾ`
  -- (`zᵢ = ⌊xᵢ⌋`)
  have hcover : {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} ⊆
      ⋃ (s : {s : Finset (Fin P) // P ≤ m + s.card}) (z : Fin P → ℤ),
        {x : Euclid P | ∀ i ∈ s.1, x i = z i} := by
    rintro x ⟨s, hs, hx⟩
    refine mem_iUnion₂.2 ⟨⟨s, hs⟩, fun i => ⌊x i⌋, fun i hi => ?_⟩
    obtain ⟨w, hw⟩ := hx i hi
    simp [hw]
  -- (5) countable subadditivity
  exact measure_mono_null hcover
    (measure_iUnion_null fun s => measure_iUnion_null fun z => hplane s.1 s.2 z)
/-- **Simon Ch. 3, Definition 1.4** (the test-function argument of Remark 1.5(3)): if
`a − x ∈ V` for every `a ∈ A`, where `V` is a linear subspace, then every approximate tangent
space `Q` of `A` at `x` is contained in `V`.  Every blow-up `η_{x,r}(A) = r⁻¹(A − x)` lies in
`V`.  For `q ∈ Q \ V` let `d = dist(q, V) > 0` (`V` is closed); the bump
`g = max(0, d/2 − |· − q|) ∈ C_c` vanishes on `V`, so all blow-up integrals of `g` vanish and
in the limit `∫_Q g dHⁿ = 0`.  Since `dim Q = n`, `Hⁿ⌞Q` is regular with support `Q ∋ q`, and
`g ≥ 0` has support `B_{d/2}(q)`, so `∫_Q g dHⁿ > 0`, a contradiction. -/
theorem Submission.dimred_mbl_dtfrpo_approxTangent_le_of_sub_mem : ∀ (P n : ℕ) (A : Set (Euclid P)) (x : Euclid P) (Q V : Submodule ℝ (Euclid P)), (∀ a ∈ A, a - x ∈ V) → HasApproximateTangentSpaceAt n A x Q → Q ≤ V := by
  intro P n A x Q V hAV hQ q hqQ
  by_contra hqV
  -- `d = dist(q, V) > 0`: `V` is closed (finite dimension) and contains `0`
  have hd : 0 < infDist q (V : Set (Euclid P)) :=
    (V.closed_of_finiteDimensional.notMem_iff_infDist_pos ⟨0, V.zero_mem⟩).mp hqV
  set d := infDist q (V : Set (Euclid P))
  -- the bump `g = max(0, d/2 − dist(·, q))`
  set g : Euclid P → ℝ := fun y => max 0 (d / 2 - dist y q)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hg_nonneg : 0 ≤ g := fun y => le_max_left 0 _
  have hg_far : ∀ y, d / 2 ≤ dist y q → g y = 0 := fun y hy =>
    max_eq_left (sub_nonpos.mpr hy)
  have hg_supp : Function.support g = ball q (d / 2) := by
    ext y
    rw [Function.mem_support, mem_ball]
    constructor
    · intro hy
      by_contra hy'
      exact hy (hg_far y (not_lt.mp hy'))
    · intro hy
      exact (lt_max_of_lt_right (sub_pos.mpr hy)).ne'
  have hg_cpt : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall q (d / 2)) fun y hy => hg_far y ?_
    rw [mem_closedBall, not_le] at hy
    exact hy.le
  -- `g` vanishes on `V`, as `dist(v, q) ≥ dist(q, V) = d` there
  have hg_V : ∀ v ∈ V, g v = 0 := by
    intro v hv
    refine hg_far v ?_
    have h : d ≤ dist q v := infDist_le_dist_of_mem (SetLike.mem_coe.mpr hv)
    rw [dist_comm] at h
    linarith
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_cpt⟩
  -- the blow-up `η_{x,r}(A)` lies in `V`, so its integral of `f` is `0` (no measurability)
  have hblow : ∀ r : ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] = 0 := by
    intro r
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    rintro _ ⟨a, ha, rfl⟩
    exact hg_V _ (V.smul_mem r⁻¹ (hAV a ha))
  -- uniqueness of limits along `𝓝[>] 0`: `∫_Q g dHⁿ = 0`
  have hQ_zero : ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] = 0 := by
    refine tendsto_nhds_unique (hQ.2 f) ?_
    simp only [hblow]
    exact tendsto_const_nhds
  -- `dim Q = n`: `Hⁿ⌞Q` is regular with support `Q ∋ q`, so `∫_Q g dHⁿ > 0`
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
    (E := Euclid P) hQ.1
  have hg_int : Integrable g (μHE[n].restrict (Q : Set (Euclid P))) :=
    hg_cont.integrable_of_hasCompactSupport hg_cpt
  have hq_supp : q ∈ (μHE[n].restrict (Q : Set (Euclid P))).support := by
    rw [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ.1]
    exact hqQ
  have hball : 0 < μHE[n].restrict (Q : Set (Euclid P)) (ball q (d / 2)) :=
    (Measure.mem_support_iff_forall q).mp hq_supp _ (ball_mem_nhds q (half_pos hd))
  have hQ_pos : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
    rw [integral_pos_iff_support_of_nonneg hg_nonneg hg_int, hg_supp]
    exact hball
  exact hQ_pos.ne' hQ_zero
/-- **Two orthonormal frames of one plane evaluate covectors equally up to one sign** (Simon
Ch. 6, §1 and §3: an `n`-plane is oriented by `±τ₁ ∧ ⋯ ∧ τₙ` for any orthonormal basis `τ` of
it).  If the orthonormal `n`-frames `τ` and `e` of `ℝᴾ` span the same subspace `W`, then
`α(τ) = α(e) · c` for every `n`-covector `α`, where `c = det_e(τ)` is the determinant of `τ` in
the basis `e` of `W` (`AlternatingMap.eq_smul_basis_det` for `α` restricted to `W`).  As the
change-of-basis determinant between two orthonormal bases of `W`, `c = ±1`. -/
theorem Submission.dimred_mbl_dtfrpo_orthonormal_frame_sign : ∀ (P n : ℕ) (τ e : Fin n → Euclid P), Orthonormal ℝ τ → Orthonormal ℝ e → Submodule.span ℝ (Set.range τ) = Submodule.span ℝ (Set.range e) → (∀ α : Covector (Euclid P) n, α τ = α e) ∨ (∀ α : Covector (Euclid P) n, α τ = -α e) := by
  intro P n τ e hτ he hspan
  -- Step 1: `W = span (range e)` has the basis `b = Basis.span` with `b j = e j`, so `finrank W = n`
  let W : Submodule ℝ (Euclid P) := Submodule.span ℝ (Set.range e)
  have he_li : LinearIndependent ℝ e := he.linearIndependent
  let b : Module.Basis (Fin n) ℝ W := Module.Basis.span he_li
  have hb : ∀ j, (b j : Euclid P) = e j := Module.Basis.coe_span_apply he_li
  have hrank : Module.finrank ℝ W = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  -- Step 2: each `τ j` lies in `span (range τ) = W`, giving the family `τW` in `W`
  have hτW : ∀ j, τ j ∈ W := fun j => hspan.le (Submodule.subset_span (Set.mem_range_self j))
  let τW : Fin n → W := Set.codRestrict τ W hτW
  -- Step 3: restricting `α` to `W`, `eq_smul_basis_det` gives `α(τ) = α(e) · det_b(τW)`
  have hdet : ∀ α : Covector (Euclid P) n, α τ = α e * b.det τW := by
    intro α
    have h := congrArg (fun f : W [⋀^Fin n]→ₗ[ℝ] ℝ => f τW)
      ((α.toAlternatingMap.compLinearMap W.subtype).eq_smul_basis_det b)
    have hτ' : (fun j => W.subtype (τW j)) = τ := rfl
    have he' : (fun j => W.subtype (b j)) = e := funext hb
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h
    rw [hτ', he'] at h
    exact h
  -- Step 4: `b` and `τW` are orthonormal bases of `W`, so `det_b(τW) = ±1`
  have hb_on : Orthonormal ℝ b := by
    have h := orthonormal_span he
    convert h using 1
    funext j
    exact Module.Basis.span_apply he_li j
  have hτW_on : Orthonormal ℝ τW := hτ.codRestrict W hτW
  have hτW_sp : ⊤ ≤ Submodule.span ℝ (Set.range τW) :=
    (hτW_on.linearIndependent.span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, hrank])).ge
  have hc : b.det τW = 1 ∨ b.det τW = -1 := by
    have h := (b.toOrthonormalBasis hb_on).det_to_matrix_orthonormalBasis_real
      (OrthonormalBasis.mk hτW_on hτW_sp)
    rwa [Module.Basis.toBasis_toOrthonormalBasis, OrthonormalBasis.coe_mk] at h
  -- Step 5: the sign `det_b(τW)` does not depend on `α`
  rcases hc with hc | hc
  · exact Or.inl fun α => by rw [hdet α, hc, mul_one]
  · exact Or.inr fun α => by rw [hdet α, hc, mul_neg_one]

/-- **Orientation of a set lying in a coordinate plane** (Simon Ch. 6, §5, (26)–(27): on a face
of the lattice the orientation is `±e₁ ∧ ⋯ ∧ eₙ`; Ch. 3, Definition 1.4).  If `a_i = x_i` for
every `a ∈ A` and every `i ∉ range ι`, and `ξ` is a unit orientation of an approximate tangent
space `Q` of `A` at `x`, then `ξ = ±e_{ι 0} ∧ ⋯ ∧ e_{ι (n−1)}`.  Every `a − x` lies in
`V = span {e_{ι j}}`, so `Q ≤ V`; as `dim Q = n = dim V`, `Q = V`.  Then `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` for
an orthonormal basis `τ` of `V`, and `α(τ) = ±α(e_ι)` with one sign for all `n`-covectors `α`. -/
theorem Submission.dimred_mbl_dtfr_plane_orientation : ∀ (P n : ℕ) (ι : Fin n → Fin P) (A : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), StrictMono ι → (∀ a ∈ A, ∀ i, (∀ j, ι j ≠ i) → a i = x i) → HasApproximateTangentSpaceAt n A x Q → IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, ξ α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∨ (∀ α : Covector (Euclid P) n, ξ α = -α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) := by
  intro P n ι A x Q ξ hι hA hQ hξ
  -- Step 1: the coordinate frame `e j = e_{ι j}` is orthonormal (`ι` is injective)
  set e : Fin n → Euclid P := fun j => EuclideanSpace.single (ι j) (1 : ℝ)
  have he : Orthonormal ℝ e :=
    (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin P)).comp ι hι.injective
  -- Step 2: `v = ∑ i, v i • e_i` lies in `V = span (range e)` if `v i = 0` for `i ∉ range ι`
  have hmem : ∀ v : Euclid P, (∀ i, (∀ j, ι j ≠ i) → v i = 0) →
      v ∈ Submodule.span ℝ (Set.range e) := by
    intro v hv
    rw [← (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h : ∃ j, ι j = i
    · obtain ⟨j, rfl⟩ := h
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, ?_⟩)
      rw [EuclideanSpace.basisFun_apply]
    · rw [EuclideanSpace.basisFun_repr, hv i (fun j hj => h ⟨j, hj⟩), zero_smul]
      exact Submodule.zero_mem _
  -- Step 3: `a − x ∈ V` for `a ∈ A`, so `Q ≤ V`; `dim Q = n = dim V` gives `Q = V`
  have hAV : ∀ a ∈ A, a - x ∈ Submodule.span ℝ (Set.range e) := fun a ha =>
    hmem _ fun i hi => by rw [PiLp.sub_apply, hA a ha i hi, sub_self]
  have hQV := Submission.dimred_mbl_dtfrpo_approxTangent_le_of_sub_mem P n A x Q _ hAV hQ
  have hQeq : Q = Submodule.span ℝ (Set.range e) := Submodule.eq_of_le_of_finrank_eq hQV (by
    rw [hQ.1, finrank_span_eq_card he.linearIndependent, Fintype.card_fin])
  -- Step 4: `ξ = ±τ` for an orthonormal frame `τ` of `Q = V`, and `α(τ) = ±α(e)` uniformly
  obtain ⟨τ, hτ, hτQ, hσ⟩ := hξ
  rcases Submission.dimred_mbl_dtfrpo_orthonormal_frame_sign P n τ e hτ he (hτQ.trans hQeq)
    with hc | hc <;> rcases hσ with hσ | hσ
  · exact Or.inl fun α => by rw [hσ α, hc α]
  · exact Or.inr fun α => by rw [hσ α, hc α]
  · exact Or.inr fun α => by rw [hσ α, hc α]
  · exact Or.inl fun α => by rw [hσ α, hc α, neg_neg]
/-- **Integrable densities on finitely many unit faces define a current** (Simon Ch. 6, proof of
Theorem 5.1, displays (27)–(30)).  Let `Q₁ ⊆ ℝ^{m+1}` be the open unit cube and, for
`p = (ι, b) ∈ s`, `Φₚ(y) = b + Σⱼ yⱼ e_{ι j}`, `Eₚ = (e_{ι j})ⱼ`, with `wₚ` integrable on `Q₁`.
(I) For every test form `ω`, `y ↦ wₚ(y) ω(Φₚ y)(Eₚ)` is integrable on `Q₁`: it is `wₚ` times a
continuous function bounded by `supₓ ‖ω(x)‖`, as `|α(Eₚ)| ≤ ‖α‖` (the `e_l` are unit vectors).
(II) `L(ω) = Σₚ ∫_{Q₁} wₚ(y) ω(Φₚ y)(Eₚ) dy` is linear with `|L(ω)| ≤ (Σₚ ∫_{Q₁} |wₚ|) · δ`
whenever `‖ω(x)‖ ≤ δ` for all `x`; order-0 uniform convergence on a common compact set then
gives `L(ωⱼ) → 0` for `ωⱼ → 0`, so `L` is a current. -/
theorem Submission.dimred_mbl_dtfric_current_exists : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  intro P m s w hint
  -- Step 1: the face map `Φₚ` is continuous
  have hΦcont : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), Continuous (fun y : Euclid (m + 1) =>
      WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro p
    exact continuous_const.add
      (continuous_finsetSum _ fun j _ => (PiLp.continuous_apply 2 _ j).smul continuous_const)
  -- Step 2: `y ↦ ω(Φₚ y)(Eₚ)` is continuous (evaluation at `Eₚ` is continuous linear)
  have hhcont : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1))
      (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)),
      Continuous (fun y : Euclid (m + 1) => (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) := by
    intro ω p
    have hω : Continuous (ω : DifferentialForm (Euclid P) (m + 1)) := ω.property.1.1.continuous
    exact (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
      (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))).continuous.comp (hω.comp (hΦcont p))
  -- Step 3: `|α(Eₚ)| ≤ ‖α‖`, since `‖e_l‖ = 1`
  have hop : ∀ (α : Covector (Euclid P) (m + 1)) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)),
      ‖α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ ‖α‖ := by
    intro α p
    have := α.le_opNorm (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
    simpa [PiLp.norm_single] using this
  -- Step 4: a test form is bounded (continuous with compact support)
  have hbdd : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∃ C : ℝ,
      ∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ C := by
    intro ω
    exact ω.property.1.2.exists_bound_of_continuous ω.property.1.1.continuous
  -- Step 5: (I), integrable times bounded measurable
  have hI : ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s,
      IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)))
        {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} := by
    intro ω p hp
    obtain ⟨C, hC⟩ := hbdd ω
    exact (hint p hp).mul_bdd (hhcont ω p).aestronglyMeasurable
      (Eventually.of_forall fun y => (hop _ p).trans (hC _))
  -- Step 6: the functional `L` is linear, by (I)
  let L : TestFormOn (univ : Set (Euclid P)) (m + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * (ω : DifferentialForm (Euclid P) (m + 1))
            (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))
      map_add' := by
        intro ω η
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← integral_add (hI ω p hp) (hI η p hp)]
        apply integral_congr_ae
        filter_upwards with y
        simp [mul_add]
      map_smul' := by
        intro c ω
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with y
        simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
          smul_eq_mul]
        ring }
  -- Step 7: `|L(ω)| ≤ A δ` whenever `‖ω(x)‖ ≤ δ` for all `x`, `A = Σₚ ∫_{Q₁} |wₚ|`
  set A : ℝ := ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
  have hest : ∀ (ω : TestFormOn (univ : Set (Euclid P)) (m + 1)) (δ : ℝ),
      (∀ x, ‖(ω : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ δ) → |L ω| ≤ A * δ := by
    intro ω δ hδ
    calc |L ω| ≤ ∑ p ∈ s, |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
          w p y * (ω : DifferentialForm (Euclid P) (m + 1))
            (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
            (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) * δ := by
          apply Finset.sum_le_sum
          intro p hp
          have hpt : ∀ y : Euclid (m + 1), ‖w p y * (ω : DifferentialForm (Euclid P) (m + 1))
              (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ |w p y| * δ := by
            intro y
            rw [norm_mul, Real.norm_eq_abs (w p y)]
            exact mul_le_mul_of_nonneg_left ((hop _ p).trans (hδ _)) (abs_nonneg _)
          have h := norm_integral_le_of_norm_le ((hint p hp).abs.mul_const δ)
            (Eventually.of_forall hpt)
          rw [integral_mul_const, Real.norm_eq_abs] at h
          exact h
      _ = A * δ := by rw [hA, Finset.sum_mul]
  -- Step 8: sequential continuity at `0`, from order-0 uniform convergence on the compact `K`
  -- and `ωⱼ = 0` off `K`
  have hcont : ∀ ωseq : ℕ → TestFormOn (univ : Set (Euclid P)) (m + 1),
      TestFormOnConverges ωseq 0 → Tendsto (fun j => L (ωseq j)) atTop (𝓝 0) := by
    intro ωseq hconv
    obtain ⟨K, -, -, hsupp, -, hunif⟩ := hconv
    have h0 := Metric.tendstoUniformlyOn_iff.mp (hunif 0)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (A + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (A + 1)) hδ)
    refine ⟨N, fun j hj => ?_⟩
    have hsmall : ∀ x, ‖(ωseq j : DifferentialForm (Euclid P) (m + 1)) x‖ ≤ ε / (A + 1) := by
      intro x
      by_cases hx : x ∈ K
      · have h := hN j hj x hx
        have hz : iteratedFDeriv ℝ 0
            ((0 : TestFormOn (univ : Set (Euclid P)) (m + 1)) : DifferentialForm (Euclid P) (m + 1))
              x = 0 := by
          simp
        rw [hz, dist_zero_left, norm_iteratedFDeriv_zero] at h
        exact h.le
      · have hx' : x ∉ tsupport (ωseq j : DifferentialForm (Euclid P) (m + 1)) :=
          fun h => hx (hsupp j h)
        rw [image_eq_zero_of_notMem_tsupport hx', norm_zero]
        exact hδ.le
    rw [Real.dist_eq, sub_zero]
    calc |L (ωseq j)| ≤ A * (ε / (A + 1)) := hest _ _ hsmall
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  -- Step 9: `D = ⟨L, Step 8⟩` satisfies the formula by definition
  exact ⟨hI, ⟨⟨L, hcont⟩, fun ω => rfl⟩⟩
/-- **Mass bound for a current given by integrable densities on coordinate unit faces** (Simon
Ch. 6, proof of Theorem 5.1, (28) and the first line of (30)).  Let `n = m + 1`, `Q₁ = (0, 1)ⁿ`,
and for `p = (ι, b)` let `Φ_p(y) = b + Σ_j y_j e_{ι(j)}` and `E_p = (e_{ι(0)}, …, e_{ι(m)})`.  If
every `ι` is strictly increasing, every `w_p` is integrable on `Q₁` and
`D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(E_p) dy` for every test form `ω`, then
`M(D) ≤ Σ_{p ∈ s} ∫_{Q₁} |w_p|`.  For strictly increasing `I`, `α(e_I)²` is one nonnegative
summand of `|α|² = Σ_{J strictly increasing} α(e_J)²`, so `|α(e_I)| ≤ |α|`.  Hence for an
admissible `ω` (`|ω(x)| ≤ 1`) the integrand of each face term is bounded by `|w_p|`, an integrable
majorant. -/
theorem Submission.dimred_mbl_dtfric_mass_le : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) := by
  intro P m s w D hmono hint hD
  -- Step 1 (F1): for strictly increasing `I`, `α(e_I)²` is one nonnegative summand of `|α|²`,
  -- so `|α(e_I)| ≤ |α|`
  have hcoef : ∀ (α : Covector (Euclid P) (m + 1)) (I : Fin (m + 1) → Fin P), StrictMono I →
      |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α := by
    intro α I hI
    unfold covectorEuclideanNorm
    apply Real.abs_le_sqrt
    have hnn : ∀ J ∈ (Finset.univ : Finset (Fin (m + 1) → Fin P)), 0 ≤
        (if StrictMono J then (α (fun i => EuclideanSpace.basisFun (Fin P) ℝ (J i))) ^ 2
          else 0) := by
      intro J _
      split_ifs <;> positivity
    have hI' := Finset.single_le_sum hnn (Finset.mem_univ I)
    simpa [hI, EuclideanSpace.basisFun_apply] using hI'
  -- Step 2: `M(D)` is the supremum of `D ω` over admissible `ω`; bound each `D ω`
  change D.massOn univ ≤ _
  unfold GeometricCurrentOn.massOn
  apply sSup_le
  rintro r ⟨ω, hω, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hD ω]
  -- Step 5: compare the two sums term by term
  apply Finset.sum_le_sum
  intro p hp
  -- Step 3: `|w_p(y) ω(Φ_p y)(E_p)| ≤ |w_p(y)| |ω(Φ_p y)| ≤ |w_p(y)|` by Step 1 with `I = p.1`
  have hbound : ∀ y : Euclid (m + 1),
      ‖w p y * (ω : DifferentialForm (Euclid P) (m + 1))
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))‖ ≤ |w p y| := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := (hcoef _ p.1 (hmono p hp)).trans (hω.2
      (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
    calc _ ≤ |w p y| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |w p y| := mul_one _
  -- Step 4: `∫ w_p h ≤ |∫ w_p h| ≤ ∫ |w_p|`, with the integrable majorant `|w_p|`
  have hint' := norm_integral_le_of_norm_le (hint p hp).abs (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs] at hint'
  exact (le_abs_self _).trans hint'
/-- **Support of a face current** (Simon Ch. 6, proof of Theorem 5.1, the face currents of (27)).
Let `D ∈ 𝒟_{m+1}(ℝᴾ)` act by `D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p y)(E_p) dy`, where `Q₁` is the
open unit cube, each `w_p` is integrable on `Q₁`, `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and
`E_p = (e_{ι_p(j)})_j`.  Then every `x ∈ spt D` is `Φ_p(y)` for some `p ∈ s` with
`∫_{Q₁} |w_p| ≠ 0` and some `y` in the closed unit cube.  Otherwise `x` lies outside the compact
union `Z` of the closed faces `Φ_p([0,1]^{m+1})` with `∫_{Q₁} |w_p| ≠ 0`, so some ball `B` about
`x` misses `Z`.  Each face integral of a test form supported in `B` vanishes: either `w_p = 0`
a.e. on `Q₁`, or the form vanishes on `Φ_p(Q₁) ⊆ Z`.  So `D` vanishes on `B`, and `x` lies in the
zero region of `D`, contradicting `x ∈ spt D`. -/
theorem Submission.dimred_mbl_dtfric_support_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x := by
  intro P m s w D hint hD x hx
  -- Step 1: otherwise `x` misses every closed face `Φ_p(Cⁿ)` with `∫_{Q₁} |w_p| ≠ 0`
  by_contra hcon
  push Not at hcon
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}
  set C : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, 0 ≤ y i ∧ y i ≤ 1}
  set Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P :=
    fun p y => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
    with hΦ
  set s' := s.filter (fun p => (∫ y in Q, |w p y|) ≠ 0) with hs'
  set Z : Set (Euclid P) := ⋃ p ∈ s', Φ p '' C with hZ
  -- Step 2: `Z` is compact, so some ball about `x` misses it
  have hCcomp : IsCompact C := by
    have hpi : IsCompact (Set.pi univ (fun _ : Fin (m + 1) => Icc (0 : ℝ) 1)) :=
      isCompact_univ_pi (fun _ => isCompact_Icc)
    have himg := hpi.image (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ))
    convert himg using 1
    ext y
    constructor
    · intro hy
      refine ⟨WithLp.ofLp y, ?_, by simp⟩
      intro i _
      exact ⟨(hy i).1, (hy i).2⟩
    · rintro ⟨z, hz, rfl⟩ i
      exact ⟨(hz i (mem_univ i)).1, (hz i (mem_univ i)).2⟩
  have hΦcont : ∀ p, Continuous (Φ p) := by
    intro p
    exact continuous_const.add
      (continuous_finsetSum _ fun j _ => (PiLp.continuous_apply 2 _ j).smul continuous_const)
  have hZcomp : IsCompact Z := s'.isCompact_biUnion (fun p _ => hCcomp.image (hΦcont p))
  have hxZ : x ∉ Z := by
    intro hxZ
    simp only [hZ, mem_iUnion, mem_image] at hxZ
    obtain ⟨p, hp, y, hy, hyx⟩ := hxZ
    rw [hs', Finset.mem_filter] at hp
    exact hcon p hp.1 hp.2 y hy hyx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hZcomp.isClosed.isOpen_compl x hxZ
  -- Step 3: `D` vanishes on `ball x r`, face by face
  have hvan : D.VanishesOn (ball x r) := by
    intro ω hω
    rw [hD ω]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hp0 : (∫ y in Q, |w p y|) = 0
    · -- (a) `w_p = 0` a.e. on `Q₁`
      have habs : (fun y => |w p y|) =ᵐ[volume.restrict Q] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (w p y)) (hint p hp).abs).mp hp0
      apply integral_eq_zero_of_ae
      filter_upwards [habs] with y hy
      have : w p y = 0 := abs_eq_zero.mp hy
      simp [this]
    · -- (b) `ω` vanishes on `Φ_p(Q₁) ⊆ Z`
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      have hyC : y ∈ C := fun i => ⟨(hy i).1.le, (hy i).2.le⟩
      have hps' : p ∈ s' := by rw [hs', Finset.mem_filter]; exact ⟨hp, hp0⟩
      have hmemZ : Φ p y ∈ Z := mem_biUnion hps' (mem_image_of_mem _ hyC)
      have hnot : Φ p y ∉ tsupport (ω : DifferentialForm (Euclid P) (m + 1)) := by
        intro hin
        exact hball (hω hin) hmemZ
      have h0 := image_eq_zero_of_notMem_tsupport hnot
      simp only [hΦ] at h0
      simp [h0]
  -- Step 4: `ball x r` is open with compact closure, so `x` lies in the zero region of `D`
  have hxzero : x ∈ D.zeroRegion := by
    refine mem_sUnion.mpr ⟨ball x r, ⟨isOpen_ball, ?_, subset_univ _, hvan⟩, mem_ball_self hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall
  -- Step 5: this contradicts `x ∈ spt D`
  exact hx.2 hxzero
/-- Deformation theorem, face replacement: divergence form of `dγ` on a coordinate face.  For
`Φ(y) = b + ∑ⱼ yⱼ e_{ι j}` and `G(y)ᵢ = (−1)ⁱ γ(Φ y)(e_{ι ∘ succAbove i})` (`γ(Φ y)` on the
frame `E = (e_{ι 0}, …, e_{ι m})` with its `i`-th vector removed), `G` is smooth,
`‖G(y)‖ ≤ |γ(Φ y)|` and `dγ(Φ y)(E) = div G(y) = trace DG(y)`. -/
theorem Submission.dimred_mbl_dtfr_face_divergence : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m) (G : Euclid (m + 1) → Euclid (m + 1)), StrictMono ι → ContDiff ℝ (⊤ : ℕ∞) γ → (∀ (y : Euclid (m + 1)) (i : Fin (m + 1)), G y i = (-1 : ℝ) ^ (i : ℕ) * γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun l => EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ))) → ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y : Euclid (m + 1), ‖G y‖ ≤ covectorEuclideanNorm (γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y : Euclid (m + 1), exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) := by
  intro P m ι b γ G hι hγ hG
  classical
  -- `Φ y = c + L y` parametrizes the face; `L y = ∑ j, y j • e_{ι j}`
  let L : Euclid (m + 1) →L[ℝ] Euclid P :=
    ∑ j, (EuclideanSpace.proj j : Euclid (m + 1) →L[ℝ] ℝ).smulRight
      (EuclideanSpace.single (ι j) (1 : ℝ))
  let Φ : Euclid (m + 1) → Euclid P := fun y =>
    WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)
  have hL : ∀ y, L y = ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ) := by
    intro y
    simp [L]
  have hΦL : Φ = fun y => WithLp.toLp 2 (fun k => (b k : ℝ)) + L y := by
    funext y
    simp only [Φ, hL]
  have hΦd : ∀ y, HasFDerivAt Φ L y := by
    intro y
    rw [hΦL]
    exact L.hasFDerivAt.const_add _
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    rw [hΦL]
    exact contDiff_const.add L.contDiff
  -- `ev i α = α (w i)`, `w i` the frame with its `i`-th vector removed
  let w : Fin (m + 1) → Fin m → Euclid P := fun i l =>
    EuclideanSpace.single (ι (Fin.succAbove i l)) (1 : ℝ)
  let ev : Fin (m + 1) → Covector (Euclid P) m →L[ℝ] ℝ := fun i =>
    ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (w i)
  have hGi : ∀ y i, G y i = (-1 : ℝ) ^ (i : ℕ) * ev i (γ (Φ y)) := fun y i => hG y i
  have hGc : ∀ i, (fun y => G y i) = fun y => (-1 : ℝ) ^ (i : ℕ) * ev i (γ (Φ y)) := by
    intro i
    funext y
    exact hGi y i
  have hγd : Differentiable ℝ γ := hγ.differentiable (by simp)
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_euclidean]
    intro i
    rw [hGc i]
    exact contDiff_const.mul ((ev i).contDiff.comp (hγ.comp hΦs))
  refine ⟨hGs, ?_, ?_⟩
  · -- `‖G y‖² = ∑ i, γ(Φ y)(w i)²` is a sub-sum of `|γ(Φ y)|²`
    intro y
    show ‖G y‖ ≤ covectorEuclideanNorm (γ (Φ y))
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    apply Real.sqrt_le_sqrt
    let g : (Fin m → Fin P) → ℝ := fun I => if StrictMono I then
      (γ (Φ y) (fun l => EuclideanSpace.basisFun (Fin P) ℝ (I l))) ^ 2 else 0
    have hinj : Function.Injective fun i : Fin (m + 1) => ι ∘ Fin.succAbove i :=
      hι.injective.comp_left.comp Fin.succAbove_left_injective
    have hterm : ∀ i, ‖G y i‖ ^ 2 = g (ι ∘ Fin.succAbove i) := by
      intro i
      have hmono : StrictMono (ι ∘ Fin.succAbove i) := hι.comp (Fin.strictMono_succAbove i)
      simp only [g, hmono, ↓reduceIte, Real.norm_eq_abs, sq_abs, hGi, mul_pow]
      rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;> simp [h, ev, w]
    calc ∑ i, ‖G y i‖ ^ 2 = ∑ i, g (ι ∘ Fin.succAbove i) := Finset.sum_congr rfl fun i _ => hterm i
      _ = ∑ I ∈ Finset.univ.image fun i : Fin (m + 1) => ι ∘ Fin.succAbove i, g I :=
        (Finset.sum_image hinj.injOn).symm
      _ ≤ ∑ I, g I :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun I _ _ => by
          simp only [g]
          split_ifs <;> positivity
  · -- both sides are `∑ i, (-1)^i Dγ(Φ y)(e_{ι i})(w i)`
    intro y
    show exteriorDerivative γ (Φ y) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) =
      LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)
    have hcoord : ∀ i (v : Euclid (m + 1)),
        fderiv ℝ G y v i = (-1 : ℝ) ^ (i : ℕ) * (fderiv ℝ γ (Φ y) (L v)) (w i) := by
      intro i v
      have h1 : HasFDerivAt (fun y => G y i)
          ((EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).comp (fderiv ℝ G y)) y :=
        (EuclideanSpace.proj i : Euclid (m + 1) →L[ℝ] ℝ).hasFDerivAt.comp y
          ((hGs.differentiable (by simp)) y).hasFDerivAt
      have h2 : HasFDerivAt (fun y => G y i)
          ((-1 : ℝ) ^ (i : ℕ) • (ev i).comp ((fderiv ℝ γ (Φ y)).comp L)) y := by
        rw [hGc i]
        exact ((ev i).hasFDerivAt.comp y ((hγd (Φ y)).hasFDerivAt.comp y (hΦd y))).const_mul _
      have h3 := congrArg (fun f : Euclid (m + 1) →L[ℝ] ℝ => f v) (h1.unique h2)
      simpa [ev] using h3
    have hfd : ∀ (i : Fin (m + 1)) (x : Euclid P),
        fderiv ℝ (fun x => γ x (Fin.removeNth i fun j => EuclideanSpace.single (ι j) (1 : ℝ))) x =
          (ev i).comp (fderiv ℝ γ x) := fun i x =>
      ((ev i).hasFDerivAt.comp x (hγd x).hasFDerivAt).fderiv
    rw [exteriorDerivative_apply (hγd _),
      LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis,
      Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfd]
    simp [Matrix.diag, LinearMap.toMatrix_apply, hcoord, hL, ev, w, zsmul_eq_mul]
/-- `spt(A − B) ⊆ spt A ∪ spt B`, `M_W(A − B) ≤ M_W(A) + M_W(B)`, `spt ∂A ⊆ spt A` and
`∂(A − B) = ∂A − ∂B`.  A point of `U` in zero-region sets `W₁` of `A` and `W₂` of `B` lies in
`W₁ ∩ W₂`, an open set with compact closure in `U` on which `A − B` vanishes.  For a `W`-admissible
`ω`, `−ω` is `W`-admissible and `(A − B)(ω) = A(ω) + B(−ω)`.  A zero-region set of `A` is one of
`∂A`, since `tsupport dγ ⊆ tsupport γ`.  Finally `∂(A − B)(γ) = A(dγ) − B(dγ) = (∂A − ∂B)(γ)`. -/
theorem Submission.dimred_mbl_dtfr_current_calculus : (∀ (P n : ℕ) (U W : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).support ⊆ A.support ∪ B.support ∧ (A - B).massOn W ≤ A.massOn W + B.massOn W) ∧ ∀ (P m : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U (m + 1)), A.boundary.support ⊆ A.support ∧ (A - B).boundary = A.boundary - B.boundary := by
  refine ⟨fun P n U W A B => ⟨?_, ?_⟩, fun P m U A B => ⟨?_, ?_⟩⟩
  · -- `spt(A − B) ⊆ spt A ∪ spt B`
    rintro y ⟨hyU, hyZ⟩
    by_contra hAB
    have hA : y ∈ A.zeroRegion := not_not.mp fun h => hAB (Or.inl ⟨hyU, h⟩)
    have hB : y ∈ B.zeroRegion := not_not.mp fun h => hAB (Or.inr ⟨hyU, h⟩)
    obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hA
    obtain ⟨W₂, ⟨hW₂o, -, -, hW₂v⟩, hyW₂⟩ := mem_sUnion.mp hB
    -- `W₁ ∩ W₂` belongs to the family whose union is the zero region of `A − B`
    have hcl : closure (W₁ ∩ W₂) ⊆ closure W₁ := closure_mono inter_subset_left
    refine hyZ (mem_sUnion.mpr ⟨W₁ ∩ W₂, ⟨hW₁o.inter hW₂o,
      hW₁c.of_isClosed_subset isClosed_closure hcl, hcl.trans hW₁U, fun ω hω => ?_⟩, hyW₁, hyW₂⟩)
    change A ω - B ω = 0
    rw [hW₁v ω (hω.trans inter_subset_left), hW₂v ω (hω.trans inter_subset_right), sub_zero]
  · -- `M_W(A − B) ≤ M_W(A) + M_W(B)`
    refine sSup_le ?_
    rintro r ⟨ω, hω, rfl⟩
    -- `−ω` is `W`-admissible
    have hneg : -ω ∈ massAdmissibleOn U n W := by
      refine ⟨?_, fun x => ?_⟩
      · show tsupport (-(ω : DifferentialForm (Euclid P) n)) ⊆ W
        rw [tsupport_neg]
        exact hω.1
      · show covectorEuclideanNorm (-(ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [covectorEuclideanNorm_neg]
        exact hω.2 x
    -- `(A − B)(ω) = A(ω) + B(−ω)`
    have heq : (A - B) ω = A ω + B (-ω) := by
      rw [show B (-ω) = -B ω from map_neg B.toCurrent ω]
      exact sub_eq_add_neg (A ω) (B ω)
    calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [heq]
      _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
      _ ≤ A.massOn W + B.massOn W := add_le_add (A.le_massOn hω) (B.le_massOn hneg)
  · -- `spt ∂A ⊆ spt A`: a zero-region set of `A` is one of `∂A`
    rintro y ⟨hyU, hyZ⟩
    refine ⟨hyU, fun hA => hyZ ?_⟩
    obtain ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, hW₁v⟩, hyW₁⟩ := mem_sUnion.mp hA
    refine mem_sUnion.mpr ⟨W₁, ⟨hW₁o, hW₁c, hW₁U, fun γ hγ => ?_⟩, hyW₁⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hW₁v _ ((tsupport_exteriorDerivative_subset (γ : DifferentialForm (Euclid P) m)).trans hγ)
  · -- `∂(A − B)(γ) = (A − B)(dγ) = A(dγ) − B(dγ) = (∂A − ∂B)(γ)`
    ext γ
    rfl

/-- **Simon Ch. 6, proof of 5.1, (26)–(28) and (33)** (with `n = m + 1`): an integer
multiplicity `Q₀ ∈ 𝒟ₙ(ℝᴾ)` with `spt Q₀` in a compact `K` and in the lattice `n`-skeleton `L_n`
is a finite sum of integer `L¹` densities on open unit lattice `n`-faces
`F̆_p = Φ_p((0, 1)ⁿ)`, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` (`p = (ι, b)`, `ι` increasing):
`Q₀(ω) = Σ_p ∫_{(0,1)ⁿ} u_p(y) ⟨ω(Φ_p(y)), e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}⟩ dy`, `Σ_p ∫ |u_p| ≤ M(Q₀)`.
Write `Q₀ = τ(M, θ, ξ)`.  The faces whose open face meets `spt Q₀ ⊆ K` are finitely many, and
distinct open faces are disjoint (face_geometry).  `M` lies in their union up to
`(M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null (`imrep_carrier_sdiff_support_null`, skeleton_null), as
a point of `L_n ∖ L_m` lies on an open face.  On each face `Q₀⌞F̆_p` is an integer density `u_p`
with `∫ |u_p| ≤ μ_{Q₀}(F̆_p)` (face_density; `Φ_p` is an isometry).  Summing over the disjoint
faces gives the representation and, by (MR), `Σ_p ∫ |u_p| ≤ μ_{Q₀}(ℝᴾ) = M(Q₀)`. -/
theorem Submission.dimred_mbl_dtfr_skeleton_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ) (K : Set (Euclid P)) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → ∃ (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q₀.mass ∧ (∀ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.support) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
  classical
  intro _ hMR hIMC P m K Q₀ hK hQ₀ hQ₀K hQ₀L
  obtain ⟨-, hIMCb, -, -⟩ := hIMC
  -- Step 1: an integer multiplicity representation `R = (M, θ, ξ)` of `Q₀`
  obtain ⟨R, hR⟩ := hQ₀
  -- the open unit cube `Q₁ = (0, 1)ⁿ` and the open faces `F̆_p = Φ_p(Q₁)`
  set Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ₁
  set F : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Set (Euclid P) := fun p =>
    (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' Q₁
  -- Step 8: for increasing `ι`, `Φ_p` is an isometry (face_geometry (a)), hence a measurable
  -- embedding, so the open faces are Borel
  have hiso : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 →
      Isometry (fun y : Euclid (m + 1) => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) := fun p hp =>
    Isometry.of_dist_eq ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p p hp hp).1
  have hQ₁o : IsOpen Q₁ := by
    rw [hQ₁, ofPred_forall]
    exact isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)).inter
        (isOpen_lt (PiLp.continuous_apply 2 _ i) continuous_const)
  have hFm : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → MeasurableSet (F p) :=
    fun p hp => (hiso p hp).isClosedEmbedding.measurableEmbedding.measurableSet_image'
      hQ₁o.measurableSet
  -- Step 6: distinct open faces are disjoint (face_geometry (c))
  have hdisj : ∀ p q : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 →
      p ≠ q → Disjoint (F p) (F q) := by
    intro p q hp hq hpq
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
    have h0 : dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
          ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = 0 :=
      dist_eq_zero.2 hyy'.symm
    rcases ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p q hp hq).2.2 hpq y y' hy
      (fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩) with h | ⟨j, hj⟩
    · linarith [h.trans_eq h0]
    · linarith [hj.trans_eq h0, lt_min (hy j).1 (sub_pos.2 (hy j).2)]
  -- Step 5: the faces `p` (with `ι` increasing) whose open face meets `spt Q₀` form a finite set,
  -- since `spt Q₀ ⊆ K` is compact
  have hSfin : {p : (Fin (m + 1) → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧
      ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Q₀.support}.Finite :=
    (Submission.dimred_mbl_dtfrsd_faces_meeting_compact_finite P (m + 1) K hK).subset
      fun p ⟨_, y, hy, hyS⟩ => ⟨y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hQ₀K hyS⟩
  set s := hSfin.toFinset
  have hsS : ∀ p ∈ s, StrictMono p.1 ∧
      ∃ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) ∧ WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ) ∈ Q₀.support :=
    fun p hp => hSfin.mem_toFinset.1 hp
  have hpd : Set.Pairwise (↑s) (Disjoint on F) := by
    intro p hp q hq hpq
    exact hdisj p q (hsS p hp).1 (hsS q hq).1 hpq
  -- Steps 8 and 10–12 for one face (face_density): an integer density `u_p` on `Q₁`
  have hfd : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), ∃ v : Euclid (m + 1) → ℝ,
      StrictMono p.1 → (∀ y, ∃ z : ℤ, v y = z) ∧ IntegrableOn v Q₁ ∧
        ENNReal.ofReal (∫ y in Q₁, |v y|) ≤ R.measure (F p) ∧
        ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1),
          ∫ x in R.carrier ∩ F p, (R.mult x : ℝ) *
              R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] =
            ∫ y in Q₁, v y * (ω : DifferentialForm (Euclid P) (m + 1))
              (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
                ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    intro p
    by_cases hp : StrictMono p.1
    · obtain ⟨v, hv⟩ := Submission.dimred_mbl_dtfrsd_face_density hIMCb
        Submission.dimred_mbl_dtfr_plane_orientation P (m + 1) R p hp (hiso p hp)
      exact ⟨v, fun _ => hv⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose u hu using hfd
  refine ⟨s, u, fun p hp => (hsS p hp).1, fun p hp => (hu p (hsS p hp).1).1,
    fun p hp => (hu p (hsS p hp).1).2.1, ?_, ?_, ?_⟩
  · -- Step 11: `Σ_p ∫_{Q₁} |u_p| ≤ Σ_p μ(F̆_p) = μ(⋃_p F̆_p) ≤ μ(ℝᴾ) = M(Q₀)`, by (MR)
    calc ENNReal.ofReal (∑ p ∈ s, ∫ y in Q₁, |u p y|)
        = ∑ p ∈ s, ENNReal.ofReal (∫ y in Q₁, |u p y|) :=
          ENNReal.ofReal_sum_of_nonneg fun p _ => integral_nonneg fun y => abs_nonneg _
      _ ≤ ∑ p ∈ s, R.measure (F p) :=
          Finset.sum_le_sum fun p hp => (hu p (hsS p hp).1).2.2.1
      _ = R.measure (⋃ p ∈ s, F p) :=
          (measure_biUnion_finset hpd fun p hp => hFm p (hsS p hp).1).symm
      _ ≤ R.measure univ := measure_mono (subset_univ _)
      _ = Q₀.mass := (hMR P (m + 1) univ Q₀ R isOpen_univ hR univ isOpen_univ).symm
  · -- each closed face of `s` meets `spt Q₀`
    intro p hp
    obtain ⟨-, y, hy, hyS⟩ := hsS p hp
    exact ⟨y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hyS⟩
  · -- Step 12: the representation of `Q₀(ω)`
    intro ω
    -- Step 7: `M ∖ ⋃_p (M ∩ F̆_p) ⊆ (M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null by Steps 2 and 3
    have hnull : μHE[m + 1] (R.carrier \ ⋃ p ∈ s, R.carrier ∩ F p) = 0 := by
      refine measure_mono_null ?_ (measure_union_null
        (Submission.imrep_carrier_sdiff_support_null P (m + 1) univ Q₀ R isOpen_univ hR)
        (Submission.dimred_mbl_dtfr_skeleton_null P m))
      rintro x ⟨hxM, hxU⟩
      by_cases hxS : x ∈ Q₀.support
      · refine mem_union_right _ ?_
        by_contra hxL
        -- Step 4: `x ∈ L_n ∖ L_m` lies on an open face `F̆_p`, and `p ∈ s` as `x ∈ spt Q₀`
        obtain ⟨p, y, hp, hy, hpy⟩ :=
          Submission.dimred_mbl_dtfrsd_skeleton_point_on_open_face P m x (hQ₀L hxS) hxL
        refine hxU (mem_iUnion₂.2 ⟨p, hSfin.mem_toFinset.2 ⟨hp, y, hy, ?_⟩, hxM, y, hy, hpy⟩)
        rw [hpy]
        exact hxS
      · exact mem_union_left _ ⟨hxM, hxS⟩
    have hae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, R.carrier ∩ F p := by
      refine ae_eq_set.2 ⟨hnull, ?_⟩
      rw [sdiff_eq_empty.2 (iUnion₂_subset fun p _ => inter_subset_left)]
      exact measure_empty
    have hint := Submission.regcomp_rim_action_integrable P (m + 1) univ R ω
    have hpd' : Set.Pairwise (↑s) (Disjoint on fun p => R.carrier ∩ F p) := by
      intro p hp q hq hpq
      exact Disjoint.mono inter_subset_right inter_subset_right (hpd hp hq hpq)
    rw [hR ω]
    show ∫ x in R.carrier, (R.mult x : ℝ) *
      R.orient x ((ω : DifferentialForm (Euclid P) (m + 1)) x) ∂μHE[m + 1] = _
    rw [setIntegral_congr_set hae, integral_biUnion_finset s
      (fun p hp => R.measurableSet_carrier.inter (hFm p (hsS p hp).1)) hpd'
      (fun p _ => IntegrableOn.mono_set hint inter_subset_left)]
    exact Finset.sum_congr rfl fun p hp => (hu p (hsS p hp).1).2.2.2 ω

/-- **Currents given by integrable densities on finitely many unit faces** (Simon Ch. 6, proof of
Theorem 5.1, displays (27)–(30) and (34)).  Let `Q₁ ⊆ ℝ^{m+1}` be the open unit cube and, for
`p = (ι, b) ∈ s` with `ι` strictly increasing, `Φₚ(y) = b + Σⱼ yⱼ e_{ι j}`, `Eₚ = (e_{ι j})ⱼ`,
with `wₚ` integrable on `Q₁`.  Then (I) each `y ↦ wₚ(y) ω(Φₚ y)(Eₚ)` is integrable on `Q₁`;
(II) `D(ω) = Σₚ ∫_{Q₁} wₚ(y) ω(Φₚ y)(Eₚ) dy` defines a current; and every such `D` has
(a) `M(D) ≤ Σₚ ∫_{Q₁} |wₚ|`, (b) `M(∂D) ≤ Σₚ Bₚ` whenever `|∫_{Q₁} wₚ div G| ≤ Bₚ` for every
smooth `G` with `|G| ≤ 1`, and (c) `spt D` in the closed faces `Φₚ([0,1]^{m+1})` with
`∫_{Q₁} |wₚ| ≠ 0`.  For (b), an admissible `γ` gives on each face the smooth field
`Gₚ(y)ᵢ = (−1)ⁱ γ(Φₚ y)(Eₚ ∘ succAbove i)`, with `|Gₚ| ≤ |γ ∘ Φₚ| ≤ 1` and
`dγ(Φₚ y)(Eₚ) = div Gₚ(y)`; so `∂D(γ) = D(dγ) = Σₚ ∫_{Q₁} wₚ div Gₚ ≤ Σₚ Bₚ`. -/
theorem Submission.dimred_mbl_dtfr_face_integral_current : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ (∃ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ∧ (∀ B : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ B p) → D.boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, B p)) ∧ (∀ x ∈ D.support, ∃ p ∈ s, (∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x) := by
  intro P m s w hmono hint
  -- Step 1: (I) and (II), by `dimred_mbl_dtfric_current_exists`
  obtain ⟨hI, D₀, hD₀⟩ := Submission.dimred_mbl_dtfric_current_exists P m s w hint
  refine ⟨hI, ⟨D₀, hD₀⟩, fun D hD => ⟨?_, ?_, ?_⟩⟩
  -- Step 2: (III)(a), by `dimred_mbl_dtfric_mass_le`
  · exact Submission.dimred_mbl_dtfric_mass_le P m s w D hmono hint hD
  -- Step 3: (III)(b).  `M(∂D)` is the supremum of `∂D(γ)` over admissible `γ`; bound each
  -- `∂D(γ) = D(dγ)` face by face
  · intro B hB
    change D.boundary.massOn univ ≤ _
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro r ⟨γ, hγ, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    rw [GeometricCurrentOn.boundary_apply, hD]
    apply Finset.sum_le_sum
    intro p hp
    -- the field `Gₚ(y)ᵢ = (−1)ⁱ γ(Φₚ y)(Eₚ ∘ succAbove i)` of `dimred_mbl_dtfr_face_divergence`
    -- is smooth, with `‖Gₚ(y)‖ ≤ |γ(Φₚ y)|` and `dγ(Φₚ y)(Eₚ) = div Gₚ(y)`
    set G : Euclid (m + 1) → Euclid (m + 1) := fun y => WithLp.toLp 2 (fun i : Fin (m + 1) =>
      (-1 : ℝ) ^ (i : ℕ) * (γ : DifferentialForm (Euclid P) m)
        (WithLp.toLp 2 (fun k => (p.2 k : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
        (fun l => EuclideanSpace.single (p.1 (Fin.succAbove i l)) (1 : ℝ)))
    obtain ⟨hGsmooth, hGnorm, hGdiv⟩ := Submission.dimred_mbl_dtfr_face_divergence P m p.1 p.2
      (γ : DifferentialForm (Euclid P) m) G (hmono p hp) γ.property.1.1 (fun y i => rfl)
    -- `‖Gₚ‖ ≤ 1`, since `γ` is admissible
    have hG1 : ∀ y, ‖G y‖ ≤ 1 := fun y => (hGnorm y).trans (hγ.2 _)
    -- the form underlying the test form `dγ` is `exteriorDerivative γ`
    have hdiv : ∀ y, w p y * ((exteriorDerivativeTestOn (univ : Set (Euclid P)) m γ :
        TestFormOn (univ : Set (Euclid P)) (m + 1)) : DifferentialForm (Euclid P) (m + 1))
          (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) =
        w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) := by
      intro y
      rw [← hGdiv y]
      rfl
    -- the `p`-th face term is `∫_{Q₁} wₚ div Gₚ ≤ |∫_{Q₁} wₚ div Gₚ| ≤ Bₚ`
    calc _ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
          integral_congr_ae (Eventually.of_forall hdiv)
      _ ≤ |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| := le_abs_self _
      _ ≤ B p := hB p hp G hGsmooth hG1
  -- Step 4: (III)(c), by `dimred_mbl_dtfric_support_faces`
  · exact Submission.dimred_mbl_dtfric_support_faces P m s w D hint hD
/-- **Boundary variation on the open faces of a lattice chain** (Simon Ch. 6, proof of 5.1,
displays (27)–(28) and (32): `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|` by the reasoning of 2.35).  Let
`Q₀(ω) = Σ_{p ∈ s} ∫_{Q₁} u_p(y) ω(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) dy` with `M(∂Q₀) < ∞`.  The
separation `(c)` of `Submission.dimred_mbl_dtfr_face_geometry` and
`Submission.dimred_mbl_dtfrbv_face_neighbourhoods` give open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint
and missing every other closed face; put `V_p = M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`.  Then
`Σ_p V_p ≤ M(∂Q₀)` by `Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le`.  `(i)` The test form
`γ` of `Submission.dimred_mbl_dtfrbv_face_test_form` is admissible for `N_p` and has
`gᵢ(y) = (-1)ⁱ γ(Φ_p y)(e_{ι ∘ i.succAbove})`, so `Submission.dimred_mbl_dtfr_face_divergence`
(with `G := g`) gives `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = div g(y)`.  `dγ` vanishes on the other
faces, so `∫ u_p div g = Q₀(dγ) = ∂Q₀(γ) ≤ V_p`.  `(ii)` If `V_p ≠ 0`, some admissible `γ` for
`N_p` has `∂Q₀(γ) > 0`; by (VO) `tsupport γ ⊆ N_p` meets `spt ∂Q₀ ⊆ spt Q₀`
(`Submission.dimred_mbl_dtfr_current_calculus`).  By
`Submission.dimred_mbl_dtfr_face_integral_current`, `spt Q₀` lies on the closed faces, and of
these only the face of `p` meets `N_p`. -/
theorem Submission.dimred_mbl_dtfr_boundary_variation : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (u p) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * (ω : DifferentialForm (Euclid P) (m + 1)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → Q₀.boundary.mass < ∞ → ∃ V : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q₀.boundary.mass ∧ (∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p) ∧ (∀ p ∈ s, V p ≠ 0 → ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Q₀.boundary.support) := by
  intro hVO P m s u Q₀ hs hu hQ₀ hmass
  -- step 1: open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing the other closed faces, from the
  -- separation `(c)` of `face_geometry`
  obtain ⟨N, hN⟩ := Submission.dimred_mbl_dtfrbv_face_neighbourhoods P (m + 1)
    fun p q hp hq => ((Submission.dimred_mbl_dtfr_face_geometry P (m + 1)).2 p q hp hq).2.2
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
          Submission.dimred_mbl_dtfrbv_massOn_disjoint_sum_le P m univ Q₀.boundary _ s N hdisj
      _ ≤ Q₀.boundary.mass := Q₀.boundary.massOn_mono (subset_univ _)
  · intro p hp g hg hgc hgs hgb
    obtain ⟨hNo, hNF, hNq⟩ := hN p (hs p hp)
    -- step 5: the test form `γ` for `g` is admissible for `N_p`, so `∂Q₀(γ) ≤ V_p`
    obtain ⟨γ, hγs, hγn, hγg⟩ := Submission.dimred_mbl_dtfrbv_face_test_form P m p (N p) g
      (hs p hp) hNo hNF hg hgc hgs hgb
    have hle : Q₀.boundary γ ≤ (Q₀.boundary.massOn (N p)).toReal :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin p)).1 (Q₀.boundary.le_massOn ⟨hγs, hγn⟩)
    -- step 6: `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = trace Dg(y)`, by `face_divergence` with `G := g`
    have hdiv := (Submission.dimred_mbl_dtfr_face_divergence P m p.1 p.2
      (γ : DifferentialForm (Euclid P) m) g (hs p hp) γ.property.1.1 hγg).2.2
    -- steps 7–8: `∂Q₀(γ) = Q₀(dγ) = Σ_q ∫_{Q₁} u_q(y) dγ(Φ_q y)(E_q) dy = ∫_{Q₁} u_p div g`
    have hval : Q₀.boundary γ = ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1},
        u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
      rw [GeometricCurrentOn.boundary_apply, hQ₀, Finset.sum_eq_single_of_mem p hp]
      · congr 1
        funext y
        change u p y * exteriorDerivative (γ : DifferentialForm (Euclid P) m) _ _ = _
        rw [hdiv y]
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
    -- step 2: `spt ∂Q₀ ⊆ spt Q₀` (`current_calculus`), so `face_integral_current` gives
    -- `x = Φ_q(y)` with `q ∈ s` and `y ∈ [0,1]ⁿ`; step 1: `q = p`, since `x ∈ N_p`
    obtain ⟨q, hq, -, y, hy, rfl⟩ :=
      ((Submission.dimred_mbl_dtfr_face_integral_current P m s u hs hu).2.2 Q₀ hQ₀).2.2 x
        ((Submission.dimred_mbl_dtfr_current_calculus.2 P m univ Q₀ Q₀).1 hx)
    by_cases hqp : q = p
    · subst hqp
      exact ⟨y, hy, hx⟩
    · exact absurd (hγ.1 hxγ) (((hN p (hs p hp)).2.2 q (hs q hq) hqp).1 y hy)

/-- **Open lattice faces are disjoint, and their union is flat near each of its points** (Simon
Ch. 6, §5, chapter-06.txt lines 1841–1844 and 1899–1911: the interiors `F̆` of the faces
`F ∈ 𝓛ₙ`, and `P = Σ_F β_F [[F]]` with `M(P) = Σ_F |β_F|`).  Assume (FG), the type of
`dimred_mbl_dtfr_face_geometry`.  Let `S` be a finite set of pairs `p = (ι, b)` with `ι` strictly
increasing, `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`, `F̆_p = Φ_p((0,1)ᵏ)` and `C = ⋃_{q ∈ S} F̆_q`.
(a) A common point `Φ_p(t) = Φ_q(t')` of `F̆_p` and `F̆_q`, `p ≠ q`, is at distance `0` from itself,
while by the separation in (FG) that distance is at least `1` or some `min(tⱼ, 1 − tⱼ) > 0`.
(b) For `x = Φ_p(t)`, `t ∈ (0,1)ᵏ`, take `δ = min({1} ∪ {min(tⱼ, 1 − tⱼ)})` and let `|z − x| < δ`.
If `z = Φ_q(t') ∈ C`, separation forces `q = p`, so `z − x = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}` lies in
`V_p = span{e_{ι(j)}}`.  Conversely, if `z − x = Σⱼ cⱼ e_{ι(j)}`, then `z = Φ_p(t + c)` and, `Φ_p`
being an isometry, `|cⱼ| ≤ |c| = |z − x| < δ`, so `t + c ∈ (0,1)ᵏ` and `z ∈ F̆_p ⊆ C`. -/
theorem Submission.dimred_mbl_dtfrpi_face_union_local_plane : (∀ (P k : ℕ), volume {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)))) → ∀ (P k : ℕ) (S : Finset ((Fin k → Fin P) × (Fin P → ℤ))), (∀ p ∈ S, StrictMono p.1) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}) ((fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})) ∧ ∀ p ∈ S, ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → ∃ δ : ℝ, 0 < δ ∧ ∀ z : Euclid P, dist z (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) < δ → (z ∈ ⋃ q ∈ S, (fun y : Euclid k => WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ↔ z - (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
  intro FG P k S hS
  -- step 0: the isometry and separation facts of (FG) at `(P, k)`
  obtain ⟨-, FGpq⟩ := FG P k
  refine ⟨fun p hp q hq hpq => ?_, fun p hp t ht => ?_⟩
  -- step 1 (a): a common point `w = Φ_p(t) = Φ_q(t')` is at distance `0` from itself, against the
  -- separation of the open face `F̆_p` from the closed face of `q`
  · rw [Set.disjoint_left]
    rintro w ⟨t, ht, rfl⟩ ⟨t', ht', hw⟩
    beta_reduce at hw
    obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
    rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
    · rw [hw, dist_self] at h
      linarith
    · rw [hw, dist_self] at hj
      linarith [lt_min (ht j).1 (sub_pos.mpr (ht j).2)]
  -- step 2 (b): `δ := min ({1} ∪ {min(tⱼ, 1 − tⱼ)})`, so `0 < δ ≤ 1` and `δ ≤ min(tⱼ, 1 − tⱼ)`
  obtain ⟨δ, hδ, hδ1, hδt⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, δ ≤ min (t j) (1 - t j) := by
    let D : Finset ℝ := insert 1 (Finset.univ.image fun j => min (t j) (1 - t j))
    refine ⟨D.min' (Finset.insert_nonempty _ _), (Finset.lt_min'_iff _ _).mpr fun d hd => ?_,
      Finset.min'_le _ _ (Finset.mem_insert_self _ _), fun j => Finset.min'_le _ _
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j)))⟩
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact one_pos
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hd
      exact lt_min (ht j).1 (sub_pos.mpr (ht j).2)
  refine ⟨δ, hδ, fun z hz => ⟨fun hzC => ?_, fun hzV => ?_⟩⟩
  -- step 3 (⇒): `z = Φ_q(t')` with `q ∈ S` and `t' ∈ (0,1)ᵏ`
  · rw [Set.mem_iUnion₂] at hzC
    obtain ⟨q, hq, t', ht', hzq⟩ := hzC
    beta_reduce at hzq
    by_cases hpq : p = q
    -- for `q = p`, `z − x = Φ_p(t') − Φ_p(t) = Σⱼ (t'ⱼ − tⱼ) e_{ι(j)}`
    · subst hpq
      rw [← hzq, Submodule.mem_span_range_iff_exists_fun]
      exact ⟨fun j => t' j - t j, by simp only [sub_smul, Finset.sum_sub_distrib]; abel⟩
    -- for `q ≠ p`, separation gives `1 ≤ |z − x|` or `min(tⱼ, 1 − tⱼ) ≤ |z − x|`, both `≥ δ`
    · obtain ⟨-, -, hsep⟩ := FGpq p q (hS p hp) (hS q hq)
      rcases hsep hpq t t' ht fun i => ⟨(ht' i).1.le, (ht' i).2.le⟩ with h | ⟨j, hj⟩
      · rw [hzq, dist_comm] at h
        linarith
      · rw [hzq, dist_comm] at hj
        linarith [hδt j]
  -- step 4 (⇐): `z − x = Σⱼ cⱼ e_{ι(j)}`
  · rw [Submodule.mem_span_range_iff_exists_fun] at hzV
    obtain ⟨c, hc⟩ := hzV
    obtain ⟨hiso, -, -⟩ := FGpq p p (hS p hp) (hS p hp)
    -- `t' := t + c` has coordinates `tⱼ + cⱼ`, and `Φ_p(t') = x + (z − x) = z`
    have hcoord : ∀ j, (t + WithLp.toLp 2 c) j = t j + c j := fun j => by
      rw [PiLp.add_apply, PiLp.toLp_apply]
    have hz' : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, (t + WithLp.toLp 2 c) j • EuclideanSpace.single (p.1 j) (1 : ℝ) = z := by
      simp only [hcoord, add_smul, Finset.sum_add_distrib, hc]
      abel
    -- `|cⱼ| = |t'ⱼ − tⱼ| ≤ |t' − t| = |Φ_p(t') − Φ_p(t)| = |z − x| < δ`, as `Φ_p` is an isometry
    have hc' : ∀ j, |c j| < δ := fun j => by
      have h := PiLp.dist_apply_le (t + WithLp.toLp 2 c) t j
      rw [← hiso, hz', hcoord, Real.dist_eq, add_sub_cancel_left] at h
      exact h.trans_lt hz
    -- hence `0 < tⱼ + cⱼ < 1`, and `z = Φ_p(t') ∈ F̆_p ⊆ C`
    rw [Set.mem_iUnion₂]
    refine ⟨p, hp, t + WithLp.toLp 2 c, fun j => ?_, hz'⟩
    obtain ⟨hc₁, hc₂⟩ := abs_lt.mp (hc' j)
    rw [hcoord]
    constructor <;> linarith [hδt j, min_le_left (t j) (1 - t j), min_le_right (t j) (1 - t j)]
/-- **Finitely many disjoint oriented rectifiable pieces form an integer multiplicity current**
(Simon Ch. 6, Definition 3.1 and 6.3.1 (‡); used in the deformation theorem 6.5.1 for the
polyhedral currents, whose pieces are the open faces).  Let `S` be finite and, for `p ∈ S`, let
the pieces `F_p ⊆ U` be pairwise disjoint Borel sets with `Hᵏ(F_p) < ∞` and `F_p ⊆ G_p(ℝᵏ)` for
a Lipschitz `G_p`, let `m_p > 0`, and let `ξ_p` orient an approximate tangent space of
`C = ⋃_{q ∈ S} F_q` at each point of `F_p`.  Then `(C, θ, ξ)`, with `θ = Σ_q m_q 1_{F_q}` and
`ξ = ξ_p` on `F_p` (`0` off `C`), is an `IMRep`.  As `θ = m_p` and `ξ = ξ_p` on `F_p`, its action
is `Σ_p m_p ∫_{F_p} ⟨ω, ξ_p⟩ dHᵏ` and its mass measure of `ℝᴾ` is `Σ_p m_p Hᵏ(F_p)`. -/
theorem Submission.dimred_mbl_dtfrpi_finite_piece_imrep : ∀ (P k : ℕ) (I : Type) (U : Set (Euclid P)) (S : Finset I) (F : I → Set (Euclid P)) (m : I → ℕ) (ξ : I → MultiVector P k) (G : I → Euclid k → Euclid P), (∀ p ∈ S, MeasurableSet (F p)) → (∀ p ∈ S, F p ⊆ U) → (∀ p ∈ S, μHE[k] (F p) ≠ ∞) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (F p) (F q)) → (∀ p ∈ S, 0 < m p) → (∀ p ∈ S, ∃ K : NNReal, LipschitzWith K (G p)) → (∀ p ∈ S, F p ⊆ range (G p)) → (∀ p ∈ S, ∀ x ∈ F p, ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξ p) Q) → ∃ R : IMRep U k, (∀ ω : TestFormOn U k, R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, (m p : ℝ) * ∫ x in F p, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k]) ∧ R.measure univ = ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
  intro P k I U S F m ξ G hFm hFU hFfin hdisj hmpos hGlip hFG htan
  classical
  -- step 1: the carrier `C = ⋃_{q ∈ S} F_q` is Borel and lies in `U`
  have hCm : MeasurableSet (⋃ q ∈ S, F q) := Finset.measurableSet_biUnion S hFm
  have hCU : (⋃ q ∈ S, F q) ⊆ U := Set.iUnion₂_subset hFU
  -- step 2: a point of `F_p` lies in no other piece
  have hone : ∀ p ∈ S, ∀ q ∈ S, ∀ x ∈ F p, x ∈ F q → q = p := by
    intro p hp q hq x hxp hxq
    by_contra hqp
    exact Set.disjoint_left.mp (hdisj q hq p hp hqp) hxq hxp
  -- step 3: the multiplicity `θ = Σ_q m_q 1_{F_q}` is measurable and `θ = m_p > 0` on `F_p`
  let θ : Euclid P → ℕ := fun x => ∑ q ∈ S, (F q).indicator (fun _ => m q) x
  have hθm : Measurable θ :=
    Finset.measurable_sum S fun q hq => measurable_const.indicator (hFm q hq)
  have hθ : ∀ p ∈ S, ∀ x ∈ F p, θ x = m p := by
    intro p hp x hx
    show ∑ q ∈ S, (F q).indicator (fun _ => m q) x = m p
    rw [Finset.sum_eq_single_of_mem p hp]
    · exact Set.indicator_of_mem hx _
    · intro q hq hqp
      exact Set.indicator_of_notMem (fun hxq => hqp (hone p hp q hq x hx hxq)) _
  have hθpos : ∀ x ∈ ⋃ q ∈ S, F q, 0 < θ x := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    rw [hθ p hp x hxp]
    exact hmpos p hp
  -- step 4: the orientation, `ξ_p` on `F_p` and `0` off `C`: the right fold over a list of `S`
  -- of `(q, acc) ↦ if x ∈ F_q then ξ_q else acc`, starting from `0`
  let orient : List I → Euclid P → MultiVector P k := fun L x =>
    L.foldr (fun q acc => if x ∈ F q then ξ q else acc) 0
  have horient_sm : ∀ L : List I, (∀ q ∈ L, q ∈ S) → StronglyMeasurable (orient L) := by
    intro L
    induction L with
    | nil => exact fun _ => stronglyMeasurable_const
    | cons a L ih =>
      intro hL
      show StronglyMeasurable fun x => if x ∈ F a then ξ a else orient L x
      exact StronglyMeasurable.ite (hFm a (hL a List.mem_cons_self)) stronglyMeasurable_const
        (ih fun q hq => hL q (List.mem_cons_of_mem a hq))
  have horient : ∀ L : List I, (∀ q ∈ L, q ∈ S) → ∀ p ∈ L, ∀ x ∈ F p, orient L x = ξ p := by
    intro L
    induction L with
    | nil => intro _ p hp; simp at hp
    | cons a L ih =>
      intro hL p hpL x hx
      have hp : p ∈ S := hL p hpL
      show (if x ∈ F a then ξ a else orient L x) = ξ p
      by_cases hxa : x ∈ F a
      · rw [ite_eq_left hxa, hone p hp a (hL a List.mem_cons_self) x hx hxa]
      · rw [ite_eq_right hxa]
        refine ih (fun q hq => hL q (List.mem_cons_of_mem a hq)) p ?_ x hx
        rcases List.mem_cons.mp hpL with rfl | hpL'
        · exact absurd hx hxa
        · exact hpL'
  let ξC : Euclid P → MultiVector P k := orient S.toList
  have hSL : ∀ q ∈ S.toList, q ∈ S := fun q hq => Finset.mem_toList.mp hq
  have hξCm : StronglyMeasurable ξC := horient_sm S.toList hSL
  have hξC : ∀ p ∈ S, ∀ x ∈ F p, ξC x = ξ p := fun p hp =>
    horient S.toList hSL p (Finset.mem_toList.mpr hp)
  -- step 5: `C` is countably `k`-rectifiable, with `M₀ = ∅` and the Lipschitz maps `G_p` listed
  -- along `S.toList`, padded with constant maps
  have hrect : CountablyRectifiable k (⋃ q ∈ S, F q) := by
    refine ⟨∅, measure_empty, fun j => if h : j < S.toList.length then G (S.toList.get ⟨j, h⟩)
      else fun _ => 0, fun j => ?_, fun x hx => ?_⟩
    · by_cases h : j < S.toList.length
      · simp only [h, ↓reduceDIte]
        exact hGlip _ (hSL _ (List.get_mem _ _))
      · simp only [h, ↓reduceDIte]
        exact ⟨0, LipschitzWith.const 0⟩
    · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨y, rfl⟩ := hFG p hp hxp
      obtain ⟨⟨j, hj⟩, hjp⟩ := List.mem_iff_get.mp (Finset.mem_toList.mpr hp)
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, y, ?_⟩)
      simp only [hj, ↓reduceDIte, hjp]
  -- step 6: `∫_C θ dHᵏ = Σ_p m_p Hᵏ(F_p) < ∞`, as the `F_p` are disjoint and `θ = m_p` on `F_p`
  have hpd : Set.PairwiseDisjoint (S : Set I) F := fun p hp q hq hpq => hdisj p hp q hq hpq
  have hθint : ∫⁻ x in ⋃ q ∈ S, F q, (θ x : ℝ≥0∞) ∂μHE[k] =
      ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) := by
    rw [lintegral_biUnion_finset hpd hFm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hon : EqOn (fun x => (θ x : ℝ≥0∞)) (fun _ => (m p : ℝ≥0∞)) (F p) := by
      intro x hx
      simp only [hθ p hp x hx]
    rw [setLIntegral_congr_fun (hFm p hp) hon, setLIntegral_const]
  have hθfin : ∑ p ∈ S, (m p : ℝ≥0∞) * μHE[k] (F p) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun p hp => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (hFfin p hp)
  -- step 7: `∫_{C ∩ K} θ dHᵏ ≤ ∫_C θ dHᵏ < ∞`
  have hθloc : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in (⋃ q ∈ S, F q) ∩ K, (θ x : ℝ≥0∞) ∂μHE[k] ≠ ∞ := fun K _ _ =>
    ne_top_of_le_ne_top (by rw [hθint]; exact hθfin) (lintegral_mono_set Set.inter_subset_left)
  -- step 8: `ξ` orients an approximate tangent space at every point of `C`, hence `Hᵏ⌞C`-a.e.
  have horients : ∀ᵐ x ∂(μHE[k].restrict (⋃ q ∈ S, F q)), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, F q) x Q ∧ IsUnitOrientationOf (ξC x) Q := by
    refine ae_restrict_of_forall_mem hCm fun x hx => ?_
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨Q, hQ, hξQ⟩ := htan p hp x hxp
    exact ⟨Q, hQ, by rw [hξC p hp x hxp]; exact hξQ⟩
  -- step 9: the triple `(C, θ, ξ)`
  let R : IMRep U k :=
    { carrier := ⋃ q ∈ S, F q
      mult := θ
      orient := ξC
      measurableSet_carrier := hCm
      carrier_subset := hCU
      rectifiable := hrect
      measurable_mult := hθm
      mult_pos := hθpos
      locallyIntegrable_mult := hθloc
      aestronglyMeasurable_orient := hξCm.aestronglyMeasurable
      orients := horients }
  refine ⟨R, fun ω => ?_, ?_⟩
  -- step 10: on `F_p` the integrand is `m_p ⟨ω, ξ_p⟩`, continuous with compact support and so
  -- integrable for the finite measure `Hᵏ⌞F_p`; the action splits over the disjoint pieces
  · have hωc : Continuous (ω : DifferentialForm (Euclid P) k) := ω.2.1.1.continuous
    have hωs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.2.1.2
    have hon : ∀ p ∈ S, EqOn (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x))
        (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x)) (F p) := by
      intro p hp x hx
      simp only [hθ p hp x hx, hξC p hp x hx]
    have hint : ∀ p ∈ S, IntegrableOn
        (fun x => (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x)) (F p) μHE[k] := by
      intro p hp
      have : IsFiniteMeasure (μHE[k].restrict (F p)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact (hFfin p hp).lt_top⟩
      have hg : Integrable (fun x => (m p : ℝ) * ξ p ((ω : DifferentialForm (Euclid P) k) x))
          (μHE[k].restrict (F p)) :=
        (continuous_const.mul ((ξ p).continuous.comp hωc)).integrable_of_hasCompactSupport
          (hωs.comp_left (map_zero (ξ p))).mul_left
      exact IntegrableOn.congr_fun hg (hon p hp).symm (hFm p hp)
    show ∫ x in ⋃ q ∈ S, F q, (θ x : ℝ) * ξC x ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] = _
    rw [integral_biUnion_finset S hFm hpd hint]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [setIntegral_congr_fun (hFm p hp) (hon p hp), integral_const_mul]
  -- step 11: `μ_T(ℝᴾ) = ∫ θ d(Hᵏ⌞C) = Σ_p m_p Hᵏ(F_p)`, by step 6
  · show ((μHE[k].restrict (⋃ q ∈ S, F q)).withDensity fun x => (θ x : ℝ≥0∞)) univ = _
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hθint]

/-- **Lattice polyhedral chains are integer multiplicity, with mass `Σ_F |β_F|`** (Simon Ch. 6,
§5, in the proof of the deformation theorem 6.5.1: `P = Σ_F β_F [[F]]` is integer multiplicity
and `M(P) = Σ_F |β_F|`).  Here `T(ω) = Σ_{p ∈ s} β_p ∫_{(0,1)ᵏ} ⟨ω(Φ_p y), e_{ι(0)} ∧ ⋯ ∧
e_{ι(k-1)}⟩ dy`, where `Φ_p(y) = b + Σ_j y_j e_{ι(j)}` maps `(0,1)ᵏ` isometrically onto the open
lattice face `F̆_p` of `p = (ι, b)`.  The open faces with `β_p ≠ 0` are disjoint, and near each of
its points their union `C` agrees with the plane of that face, which is therefore its approximate
tangent space.  So `C`, with multiplicity `|β_p|` and orientation
`sign(β_p) e_{ι(0)} ∧ ⋯ ∧ e_{ι(k-1)}` on `F̆_p`, represents `T`.  The hypothesis (MR)
(`M_W(T) = μ_R(W)` for open `W` whenever the `IMRep` `R` represents `T`) then gives
`M(T) = Σ_p |β_p| Hᵏ(F̆_p) = Σ_p |β_p|`, which is at least `1` unless every `β_p` vanishes, and
then `T = 0`. -/
theorem Submission.dimred_mbl_dtfr_polyhedral_im : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ∀ (P k : ℕ) (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) k), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y in {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}, (ω : DifferentialForm (Euclid P) k) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → IsIntegerMultiplicity T ∧ T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) ∧ (T = 0 ∨ 1 ≤ T.mass) := by
  intro MR P k s β T hmono hT
  -- step 1: the open cube `Q₁ = (0,1)ᵏ` is Borel with volume `1`, and each `Φ_p` is an isometry
  let Q₁ : Set (Euclid k) := {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}
  let Φ : (Fin k → Fin P) × (Fin P → ℤ) → Euclid k → Euclid P := fun p y =>
    WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
  obtain ⟨hvol, hFG⟩ := Submission.dimred_mbl_dtfr_face_geometry P k
  have hQm : MeasurableSet Q₁ := by
    have hQ : Q₁ = ⋂ i, ({y : Euclid k | 0 < y i} ∩ {y | y i < 1}) := by
      ext y
      exact ⟨fun h => mem_iInter.2 h, fun h => mem_iInter.1 h⟩
    rw [hQ]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
        (measurableSet_lt (PiLp.continuous_apply 2 _ i).measurable measurable_const)
  have hiso : ∀ p ∈ s, Isometry (Φ p) := fun p hp =>
    Isometry.of_dist_eq (hFG p p (hmono p hp) (hmono p hp)).1
  -- step 2: the open face `F̆_p = Φ_p(Q₁)` is Borel, `Hᵏ(F̆_p) = 1`, and
  -- `∫_{F̆_p} h dHᵏ = ∫_{Q₁} h ∘ Φ_p`
  have hface : ∀ p ∈ s, MeasurableSet (Φ p '' Q₁) ∧ μHE[k] (Φ p '' Q₁) = 1 ∧
      ∀ h : Euclid P → ℝ, ∫ x in Φ p '' Q₁, h x ∂μHE[k] = ∫ y in Q₁, h (Φ p y) := by
    intro p hp
    obtain ⟨h₁, h₂, h₃⟩ :=
      Submission.dimred_mbl_dtfrpi_isometry_image_integral P k (Φ p) Q₁ (hiso p hp) hQm
    exact ⟨h₁, h₂.trans hvol, h₃⟩
  -- step 3: the faces `S` with `β_p ≠ 0`, the `k`-vectors `e_p = e_{ι(0)} ∧ ⋯ ∧ e_{ι(k-1)}` and the
  -- orientations `ξ_p = sign(β_p) e_p`
  obtain ⟨S, hS⟩ : ∃ S, S = s.filter fun p => β p ≠ 0 := ⟨_, rfl⟩
  have hSs : ∀ p ∈ S, p ∈ s ∧ β p ≠ 0 := fun p hp => Finset.mem_filter.mp (hS ▸ hp)
  have hSmono : ∀ p ∈ S, StrictMono p.1 := fun p hp => hmono p (hSs p hp).1
  have hE : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), ∃ e : MultiVector P k, StrictMono p.1 →
      Module.finrank ℝ (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) = k ∧
      (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧
      IsUnitOrientationOf e (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) ∧
      IsUnitOrientationOf (-e) (Submodule.span ℝ
        (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
    intro p
    by_cases hp : StrictMono p.1
    · obtain ⟨hrank, e, he⟩ := Submission.dimred_mbl_dtfrpi_coord_plane_orientation P k p.1 hp
      exact ⟨e, fun _ => ⟨hrank, he⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose e he using hE
  let ξ : (Fin k → Fin P) × (Fin P → ℤ) → MultiVector P k := fun p =>
    if 0 < β p then e p else -e p
  -- step 4: the open faces in `S` are disjoint, and near `x = Φ_p(t)` their union
  -- `C = ⋃_{q ∈ S} F̆_q` is the plane `x + V_p`; so `V_p` is the approximate tangent space of `C`
  -- at `x`, and `ξ_p` orients it
  obtain ⟨hdisj, hflat⟩ := Submission.dimred_mbl_dtfrpi_face_union_local_plane
    Submission.dimred_mbl_dtfr_face_geometry P k S hSmono
  have htan : ∀ p ∈ S, ∀ x ∈ Φ p '' Q₁, ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt k (⋃ q ∈ S, Φ q '' Q₁) x Q ∧ IsUnitOrientationOf (ξ p) Q := by
    rintro p hp x ⟨t, ht, rfl⟩
    obtain ⟨δ, hδ, hloc⟩ := hflat p hp t ht
    obtain ⟨hrank, -, hep, hen⟩ := he p (hSmono p hp)
    refine ⟨_, Submission.dimred_mbl_dtfrpi_local_plane_tangent P k _ _ _ δ hrank hδ hloc, ?_⟩
    by_cases hβ : 0 < β p
    · rw [show ξ p = e p from ite_eq_left hβ]
      exact hep
    · rw [show ξ p = -e p from ite_eq_right hβ]
      exact hen
  -- step 5: the `IMRep` `R = (C, θ, ξ)`, with `θ = |β_p|` and `ξ = ξ_p` on `F̆_p`
  have hfin : ∀ p ∈ S, μHE[k] (Φ p '' Q₁) ≠ ∞ := fun p hp => by
    rw [(hface p (hSs p hp).1).2.1]
    exact ENNReal.one_ne_top
  obtain ⟨R, hRact, hRmass⟩ := Submission.dimred_mbl_dtfrpi_finite_piece_imrep P k _ univ S
    (fun p => Φ p '' Q₁) (fun p => (β p).natAbs) ξ Φ (fun p hp => (hface p (hSs p hp).1).1)
    (fun _ _ => subset_univ _) hfin hdisj (fun p hp => Int.natAbs_pos.mpr (hSs p hp).2)
    (fun p hp => ⟨1, (hiso p (hSs p hp).1).lipschitzWith⟩) (fun p _ => image_subset_range _ _)
    htan
  have hRact' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      R.action (ω : DifferentialForm (Euclid P) k) = ∑ p ∈ S, ((β p).natAbs : ℝ) *
        ∫ x in Φ p '' Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] := hRact
  have hRmass' : R.measure univ = ∑ p ∈ S, ((β p).natAbs : ℝ≥0∞) * μHE[k] (Φ p '' Q₁) := hRmass
  -- step 6: `R` represents `T`: the change of variables `Φ_p` gives
  -- `|β_p| ∫_{F̆_p} ⟨ω, ξ_p⟩ dHᵏ = β_p ∫_{Q₁} ⟨ω ∘ Φ_p, e_p⟩`, and the faces with `β_p = 0`
  -- contribute `0`
  have hRep : R.Represents T := by
    intro ω
    rw [hT ω, hRact' ω, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    split_ifs with hβ
    · obtain ⟨-, he₁, -, -⟩ := he p (hmono p hp)
      have hcv : ∫ x in Φ p '' Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) x) ∂μHE[k] =
          ∫ y in Q₁, ξ p ((ω : DifferentialForm (Euclid P) k) (Φ p y)) :=
        (hface p hp).2.2 fun x => ξ p ((ω : DifferentialForm (Euclid P) k) x)
      show (β p : ℝ) * ∫ y in Q₁, (ω : DifferentialForm (Euclid P) k) (Φ p y)
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) = _
      rw [hcv]
      by_cases hpos : 0 < β p
      · have habs : ((β p).natAbs : ℝ) = β p := by
          rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (Int.cast_pos.mpr hpos)]
        rw [show ξ p = e p from ite_eq_left hpos, habs]
        simp only [he₁]
      · have habs : ((β p).natAbs : ℝ) = -β p := by
          rw [Nat.cast_natAbs, Int.cast_abs,
            abs_of_neg (Int.cast_lt_zero.mpr (lt_of_le_of_ne (not_lt.mp hpos) hβ))]
        rw [show ξ p = -e p from ite_eq_right hpos, habs]
        simp only [neg_apply, he₁, integral_neg, neg_mul_neg]
    · rw [not_not.mp hβ, Int.cast_zero, zero_mul]
  -- step 7: by (MR), `M(T) = μ_R(ℝᴾ) = Σ_{p ∈ S} |β_p| Hᵏ(F̆_p) = Σ_{p ∈ s} |β_p|`
  have hmass : T.mass = ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := by
    have hTR : T.mass = R.measure univ := MR P k univ T R isOpen_univ hRep univ isOpen_univ
    rw [hTR, hRmass', ENNReal.ofReal_sum_of_nonneg fun p _ => abs_nonneg _, hS,
      Finset.sum_filter_of_ne]
    · refine Finset.sum_congr rfl fun p hp => ?_
      rw [(hface p hp).2.1, mul_one, ← ENNReal.ofReal_natCast, Nat.cast_natAbs, Int.cast_abs]
    · intro p _ h hβ
      exact h (by simp [hβ])
  -- step 8: `T = 0` if every `β_p` vanishes; otherwise `M(T) ≥ |β_p| ≥ 1` for some `p ∈ s`
  refine ⟨⟨R, hRep⟩, hmass, ?_⟩
  by_cases h0 : ∃ p ∈ s, β p ≠ 0
  · right
    obtain ⟨p, hp, hβ⟩ := h0
    rw [hmass, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) ≤ |(β p : ℝ)| := by exact_mod_cast Int.one_le_abs hβ
      _ ≤ ∑ q ∈ s, |(β q : ℝ)| :=
        Finset.single_le_sum (f := fun q => |(β q : ℝ)|) (fun q _ => abs_nonneg _) hp
  · left
    ext ω
    rw [hT ω, GeometricCurrentOn.zero_apply]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hβ : β p = 0 := by
      by_contra hβ
      exact h0 ⟨p, hp, hβ⟩
    rw [hβ, Int.cast_zero, zero_mul]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
