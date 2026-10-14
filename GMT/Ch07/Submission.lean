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

/-- Orthonormal partner of a unit vector `u` in a 2-plane `Q`: pick `w ∈ Q \ span {u}`
(`dim span {u} = 1 < 2`), put `e = e'/‖e'‖` with `e' = w - ⟨w, u⟩u`; then `(u, e)` is
orthonormal, so `span {u, e} = Q` by dimension, and `v = au + be` gives `a = ⟨v, u⟩`,
`b = ⟨v, e⟩`. -/
theorem Submission.idtp_ccd_scsp_cc_plane_orthonormal : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (u : Euclid P), Module.finrank ℝ Q = 2 → u ∈ Q → ‖u‖ = 1 → ∃ e : Euclid P, e ∈ Q ∧ ‖e‖ = 1 ∧ inner ℝ u e = 0 ∧ ∀ v ∈ Q, v = inner ℝ v u • u + inner ℝ v e • e := by
  intro P Q u hQ huQ hu
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have huu : inner ℝ u u = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hu]; norm_num
  -- some `w ∈ Q` lies outside `span {u}`
  obtain ⟨w, hwQ, hw⟩ : ∃ w ∈ Q, w ∉ Submodule.span ℝ {u} := by
    rw [← IsConcreteLE.not_le_iff_exists]
    intro h
    have h1 := Submodule.finrank_mono h
    rw [hQ, finrank_span_singleton hu0] at h1
    omega
  -- Gram–Schmidt step
  set e' := w - inner ℝ w u • u with he'
  have he'Q : e' ∈ Q := Q.sub_mem hwQ (Q.smul_mem _ huQ)
  have he'0 : e' ≠ 0 := by
    intro h
    apply hw
    have : w = inner ℝ w u • u := sub_eq_zero.mp h
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  have hue' : inner ℝ u e' = (0 : ℝ) := by
    rw [he', inner_sub_right, real_inner_smul_right, huu, real_inner_comm]; ring
  have hne : ‖e'‖ ≠ 0 := norm_ne_zero_iff.mpr he'0
  set e := ‖e'‖⁻¹ • e' with he
  have heQ : e ∈ Q := Q.smul_mem _ he'Q
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hne]
  have hue : inner ℝ u e = (0 : ℝ) := by
    rw [he, real_inner_smul_right, hue', mul_zero]
  have hee : inner ℝ e e = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hen]; norm_num
  have heu : inner ℝ e u = (0 : ℝ) := by rw [real_inner_comm, hue]
  -- `span {u, e} = Q`
  have hon : Orthonormal ℝ ![u, e] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hu, hen, hue, heu]
  have hspan : Submodule.span ℝ {u, e} = Q := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro x (rfl | rfl)
      · exact huQ
      · exact heQ
    · have := finrank_span_eq_card hon.linearIndependent
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union] at this
      rw [this, hQ, Fintype.card_fin]
  refine ⟨e, heQ, hen, hue, ?_⟩
  intro v hv
  rw [← hspan] at hv
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
  simp only [inner_add_left, real_inner_smul_left, huu, heu, hue, hee]
  simp
/-- Polar coordinates `F(x) = (‖x‖, arctan(⟨x, e⟩/⟨x, u⟩))` on the half-space
`H = {x | 0 < ⟨x, u⟩}`: both coordinates are `C¹` on `H`, since `0 ∉ H` and `⟨x, u⟩ ≠ 0` on `H`.
At `p = r₀u` the norm `√(‖x‖²)` has derivative `⟨u, ·⟩`, and the product rule for
`⟨x, e⟩ · ⟨x, u⟩⁻¹` with `⟨p, e⟩ = 0` and `arctan' 0 = 1` gives `⟨e, ·⟩/r₀`; the coordinate
projections and uniqueness of the derivative identify `DF(p)`. -/
theorem Submission.idtp_ccd_scsp_cc_polar_map : ∀ (P : ℕ) (u e : Euclid P) (r₀ : ℝ), ‖u‖ = 1 → inner ℝ u e = 0 → 0 < r₀ → ContDiffOn ℝ 1 (fun x : Euclid P => (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) {x : Euclid P | 0 < inner ℝ x u} ∧ ∀ h : Euclid P, fderiv ℝ (fun x : Euclid P => (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) (r₀ • u) h = !₂[inner ℝ u h, inner ℝ e h / r₀] := by
  intro P u e r₀ hu hue hr₀
  -- `H = {0 < ⟨x, u⟩}` is open and does not contain `0`
  have hHopen : IsOpen {x : Euclid P | 0 < inner ℝ x u} :=
    isOpen_lt continuous_const (continuous_id.inner continuous_const)
  have hc0 : ∀ x ∈ {x : Euclid P | 0 < inner ℝ x u},
      ContDiffAt ℝ 1 (fun x : Euclid P => ‖x‖) x := by
    intro x hx
    refine contDiffAt_norm ℝ ?_
    rintro rfl
    simp only [mem_ofPred_eq, inner_zero_left, lt_self_iff_false] at hx
  have hc1 : ∀ x ∈ {x : Euclid P | 0 < inner ℝ x u},
      ContDiffAt ℝ 1 (fun x : Euclid P => Real.arctan (inner ℝ x e / inner ℝ x u)) x := by
    intro x hx
    have ha : ContDiff ℝ 1 (fun x : Euclid P => inner ℝ x e) := contDiff_id.inner ℝ contDiff_const
    have hb : ContDiff ℝ 1 (fun x : Euclid P => inner ℝ x u) := contDiff_id.inner ℝ contDiff_const
    exact Real.contDiff_arctan.contDiffAt.comp x (ha.contDiffAt.div hb.contDiffAt (ne_of_gt hx))
  -- `F` is `C¹` on `H` coordinatewise
  have hCD : ContDiffOn ℝ 1 (fun x : Euclid P =>
      (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2))
      {x : Euclid P | 0 < inner ℝ x u} := by
    rw [contDiffOn_piLp]
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      exact fun x hx => (hc0 x hx).contDiffWithinAt
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact fun x hx => (hc1 x hx).contDiffWithinAt
  refine ⟨hCD, fun h => ?_⟩
  -- values at `p = r₀ • u`
  have hpu : inner ℝ (r₀ • u) u = r₀ := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hu]; ring
  have hpe : inner ℝ (r₀ • u) e = (0 : ℝ) := by
    rw [real_inner_smul_left, hue, mul_zero]
  have hpn : ‖r₀ • u‖ = r₀ := by
    rw [norm_smul, hu, Real.norm_eq_abs, abs_of_pos hr₀, mul_one]
  have hpH : r₀ • u ∈ {x : Euclid P | 0 < inner ℝ x u} := by
    show 0 < inner ℝ (r₀ • u) u
    rw [hpu]; exact hr₀
  have hdiff : DifferentiableAt ℝ (fun x : Euclid P =>
      (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) (r₀ • u) :=
    (hCD.contDiffAt (hHopen.mem_nhds hpH)).differentiableAt one_ne_zero
  -- the norm `√(‖x‖²)` has derivative `⟨p, ·⟩ / ‖p‖ = ⟨u, ·⟩` at `p`
  have hd0 : HasFDerivAt (fun x : Euclid P => ‖x‖) (innerSL ℝ u) (r₀ • u) := by
    have h2 : HasFDerivAt (fun x : Euclid P => ‖x‖ ^ 2) (2 • innerSL ℝ (r₀ • u)) (r₀ • u) :=
      (hasStrictFDerivAt_norm_sq (r₀ • u)).hasFDerivAt
    have h3 := h2.sqrt (by rw [hpn]; positivity)
    simp only [Real.sqrt_sq (norm_nonneg _)] at h3
    convert h3 using 1
    ext v
    simp only [coe_innerSL_apply, hpn, one_div, mul_inv_rev, map_smul, smul_apply, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  -- `⟨x, e⟩ · ⟨x, u⟩⁻¹` has derivative `⟨e, ·⟩ / r₀` at `p`, as `⟨p, e⟩ = 0`
  have ha : HasFDerivAt (fun x : Euclid P => inner ℝ x e) (innerSL ℝ e) (r₀ • u) := by
    convert (innerSL ℝ e).hasFDerivAt using 1
    ext x; simp [real_inner_comm]
  have hb : HasFDerivAt (fun x : Euclid P => inner ℝ x u) (innerSL ℝ u) (r₀ • u) := by
    convert (innerSL ℝ u).hasFDerivAt using 1
    ext x; simp [real_inner_comm]
  have hbinv : HasFDerivAt (fun x : Euclid P => (inner ℝ x u)⁻¹)
      ((-(r₀ ^ 2)⁻¹) • innerSL ℝ u) (r₀ • u) := by
    have h1 := hasDerivAt_inv (show r₀ ≠ 0 from ne_of_gt hr₀)
    rw [← hpu] at h1
    have h2 := h1.comp_hasFDerivAt (r₀ • u) hb
    rw [hpu] at h2
    exact h2
  have hq : HasFDerivAt (fun x : Euclid P => inner ℝ x e / inner ℝ x u)
      (r₀⁻¹ • innerSL ℝ e) (r₀ • u) := by
    have h1 := ha.fun_mul hbinv
    simp only [hpe, hpu, zero_smul, zero_add] at h1
    simpa only [div_eq_mul_inv] using h1
  -- `arctan' 0 = 1`
  have hd1 : HasFDerivAt (fun x : Euclid P => Real.arctan (inner ℝ x e / inner ℝ x u))
      (r₀⁻¹ • innerSL ℝ e) (r₀ • u) := by
    convert hq.arctan using 1
    simp [hpe, hpu]
  -- identify `fderiv` through the two coordinate projections
  have hproj : ∀ i : Fin 2, HasFDerivAt (fun x : Euclid P =>
      (EuclideanSpace.proj i : StrongDual ℝ (Euclid 2))
        (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2))
      ((EuclideanSpace.proj i : StrongDual ℝ (Euclid 2)).comp (fderiv ℝ (fun x : Euclid P =>
        (!₂[‖x‖, Real.arctan (inner ℝ x e / inner ℝ x u)] : Euclid 2)) (r₀ • u))) (r₀ • u) :=
    fun i => (EuclideanSpace.proj i : StrongDual ℝ (Euclid 2)).hasFDerivAt.comp (r₀ • u)
      hdiff.hasFDerivAt
  have e0 := (hproj 0).unique (by simpa only [Fin.isValue, PiLp.proj_apply,
    Matrix.cons_val_zero] using hd0)
  have e1 := (hproj 1).unique (by simpa only [Fin.isValue, PiLp.proj_apply,
    Matrix.cons_val_one, Matrix.cons_val_fin_one] using hd1)
  have v0 := congrArg (fun f => f h) e0
  have v1 := congrArg (fun f => f h) e1
  simp only [Fin.isValue, ContinuousLinearMap.comp_apply, PiLp.proj_apply, coe_innerSL_apply,
    smul_apply, smul_eq_mul] at v0 v1
  ext i
  fin_cases i
  · simpa [real_inner_comm] using v0
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [v1, div_eq_inv_mul]
/-- **Shrinking a local inverse chart to a coordinate square.**  Choose `ε > 0` with
`B_ε(F p) ⊆ O` and put `s = min(ε, r₀)/4`, so `0 < s < r₀`.  The open square
`R_s = (r₀ - s, r₀ + s) × (-s, s)` lies in `B_ε((r₀, 0)) ⊆ O`, since every `w ∈ R_s` has
`|w - (r₀, 0)|² < 2s² < ε²`.  `N = N₀ ∩ (U ∩ F⁻¹(R_s))` is open because `F` is continuous on the
open set `U`, and it contains `p`; as `G(O) = M ∩ N₀` and `F ∘ G = id` on `O`, `M ∩ N = G(R_s)`. -/
theorem Submission.idtp_ccd_scsp_cc_square_shrink : ∀ (P : ℕ) (M U N₀ : Set (Euclid P)) (O : Set (Euclid 2)) (F : Euclid P → Euclid 2) (G : Euclid 2 → Euclid P) (p : Euclid P) (r₀ : ℝ), 0 < r₀ → IsOpen U → ContinuousOn F U → IsOpen O → IsOpen N₀ → F p = !₂[r₀, 0] → F p ∈ O → p ∈ N₀ → N₀ ⊆ U → G '' O = M ∩ N₀ → (∀ w ∈ O, F (G w) = w) → ∃ (s : ℝ) (N : Set (Euclid P)), 0 < s ∧ s < r₀ ∧ IsOpen N ∧ p ∈ N ∧ N ⊆ U ∧ {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} ⊆ O ∧ M ∩ N = G '' {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} := by
  intro P M U N₀ O F G p r₀ hr₀ hU hF hO hN₀ hFp hFpO hpN₀ hN₀U hGO hFG
  -- Step 1: a ball `B_ε(F p) ⊆ O`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO (F p) hFpO
  -- Step 2: `s = min(ε, r₀)/4`, so `0 < s < r₀` and `s ≤ ε/4`
  set s := min ε r₀ / 4 with hs_def
  have hs : 0 < s := div_pos (lt_min hε hr₀) four_pos
  have hsr : s < r₀ := by linarith [min_le_right ε r₀]
  have hsε : s ≤ ε / 4 := by linarith [min_le_left ε r₀]
  set R : Set (Euclid 2) := {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s}
    with hR_def
  -- Step 3: `R_s ⊆ B_ε(F p) ⊆ O`, since `(w₀ - r₀)² + w₁² < 2s² ≤ ε²/8 < ε²` on `R_s`
  have hRO : R ⊆ O := by
    rintro w ⟨⟨h0l, h0r⟩, h1l, h1r⟩
    apply hball
    rw [Metric.mem_ball, EuclideanSpace.dist_eq, hFp, Real.sqrt_lt' hε]
    simp only [Real.dist_eq, sq_abs, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_zero]
    have h0 : (w 0 - r₀) ^ 2 < s ^ 2 := sq_lt_sq' (by linarith) (by linarith)
    have h1 : w 1 ^ 2 < s ^ 2 := sq_lt_sq' (by linarith) (by linarith)
    have h2 : s ^ 2 ≤ (ε / 4) ^ 2 := pow_le_pow_left₀ hs.le hsε 2
    nlinarith [pow_pos hε 2]
  -- Step 4: `R_s` is open (preimages of open intervals under the coordinate maps)
  have hRopen : IsOpen R :=
    (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 0)).inter
      (isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ 1))
  -- Step 5: `N = N₀ ∩ (U ∩ F⁻¹(R_s))` is open and lies in `U`
  refine ⟨s, N₀ ∩ (U ∩ F ⁻¹' R), hs, hsr, hN₀.inter (hF.isOpen_inter_preimage hU hRopen), ?_,
    fun x hx => hx.2.1, hRO, ?_⟩
  -- Step 6: `p ∈ N`, as `F p = (r₀, 0) ∈ R_s`
  · refine ⟨hpN₀, hN₀U hpN₀, ?_⟩
    show F p ∈ R
    rw [hFp, hR_def]
    simp only [Fin.isValue, mem_Ioo, mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact ⟨⟨by linarith, by linarith⟩, by linarith, hs⟩
  · ext x
    constructor
    -- Step 7: `M ∩ N ⊆ G(R_s)`: `x = G w` with `w ∈ O`, and `w = F x ∈ R_s`
    · rintro ⟨hxM, hxN₀, -, hxR⟩
      obtain ⟨w, hwO, rfl⟩ : x ∈ G '' O := hGO ▸ ⟨hxM, hxN₀⟩
      refine ⟨w, ?_, rfl⟩
      rw [← hFG w hwO]
      exact hxR
    -- Step 8: `G(R_s) ⊆ M ∩ N`: `w ∈ O`, so `G w ∈ M ∩ N₀ ⊆ U` and `F (G w) = w ∈ R_s`
    · rintro ⟨w, hwR, rfl⟩
      have hwO := hRO hwR
      have hmem : G w ∈ M ∩ N₀ := hGO ▸ mem_image_of_mem G hwO
      refine ⟨hmem.1, hmem.2, hN₀U hmem.2, ?_⟩
      show F (G w) ∈ R
      rw [hFG w hwO]
      exact hwR
/-- **Radial extension of the cone chart** (step 8 of the parent proof).  Fix `α ∈ (-s, s)` and
let `A = {t ∈ (r₀ - s, r₀ + s) : G (t, α) = t γ(α)}`, which contains `r₀`.  `A` is open: for `t ∈ A`
and `t′` near `t`, the point `t′ γ(α)` stays in the open set `N`, lies in `M` by radial invariance
(`t′ γ(α) = (t′ / t) • t γ(α)`), so it is `G w` for some `w` in the square, and `F ∘ G = id`
together with `F (t′ γ(α)) = (t′, α)` forces `w = (t′, α)`.  `A` is relatively closed since
`t ↦ G (t, α)` and `t ↦ t γ(α)` are continuous on the open interval and limits are unique.  The
interval is preconnected, so `G (t, α) = t γ(α)` on the whole square, which gives both
conclusions. -/
theorem Submission.idtp_ccd_scsp_cc_radial_extension : ∀ (P : ℕ) (M N : Set (Euclid P)) (p : Euclid P) (ρ r₀ s : ℝ) (F : Euclid P → Euclid 2) (G : Euclid 2 → Euclid P) (γ : ℝ → Euclid P), 0 < s → s < r₀ → IsOpen N → N ⊆ ball p ρ → (∀ x ∈ M ∩ ball p ρ, ∀ t : ℝ, 0 < t → t • x ∈ ball p ρ → t • x ∈ M) → ContinuousOn G {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} → M ∩ N = G '' {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} → (∀ w : Euclid 2, w 0 ∈ Ioo (r₀ - s) (r₀ + s) → w 1 ∈ Ioo (-s) s → F (G w) = w) → (∀ α ∈ Ioo (-s) s, ‖γ α‖ = 1 ∧ G !₂[r₀, α] = r₀ • γ α ∧ ∀ t : ℝ, 0 < t → F (t • γ α) = !₂[t, α]) → (∀ w : Euclid 2, w 0 ∈ Ioo (r₀ - s) (r₀ + s) → w 1 ∈ Ioo (-s) s → G w = w 0 • γ (w 1)) ∧ M ∩ N = (fun q : ℝ × ℝ => q.1 • γ q.2) '' (Ioo (r₀ - s) (r₀ + s) ×ˢ Ioo (-s) s) := by
  intro P M N p ρ r₀ s F G γ hs hsr hN hNb hrad hGc hMN hFG hγ
  -- the radial identity on each horizontal segment `J × {α}` of the coordinate square
  have key : ∀ α ∈ Ioo (-s) s, ∀ t ∈ Ioo (r₀ - s) (r₀ + s), G !₂[t, α] = t • γ α := by
    intro α hα
    obtain ⟨hγn, hG0, hF⟩ := hγ α hα
    -- `t ↦ G (t, α)` is continuous on `J`
    have hmaps : MapsTo (fun t : ℝ => (!₂[t, α] : Euclid 2)) (Ioo (r₀ - s) (r₀ + s))
        {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} := by
      intro t ht
      exact ⟨by simpa using ht, by simpa using hα⟩
    have hφ : ContinuousOn (fun t : ℝ => G !₂[t, α]) (Ioo (r₀ - s) (r₀ + s)) :=
      hGc.comp (by fun_prop) hmaps
    -- `A = {t ∈ J : G (t, α) = t γ(α)}`
    set A : Set ℝ := {t | t ∈ Ioo (r₀ - s) (r₀ + s) ∧ G !₂[t, α] = t • γ α}
    -- `A` is open: nearby `t′ γ(α)` stay in `N`, lie in `M` by radial invariance, and `F ∘ G = id`
    -- identifies their chart coordinates as `(t′, α)`
    have hAo : IsOpen A := by
      rw [Metric.isOpen_iff]
      rintro t ⟨htJ, hGt⟩
      have hx : t • γ α ∈ M ∩ N := by
        rw [hMN, ← hGt]
        exact mem_image_of_mem G (hmaps htJ)
      obtain ⟨η₀, hη₀, hball⟩ := Metric.isOpen_iff.1 hN _ hx.2
      refine ⟨min η₀ (t - (r₀ - s)), lt_min hη₀ (by linarith [htJ.1]), fun t' ht' => ?_⟩
      rw [Metric.mem_ball, Real.dist_eq] at ht'
      have h1 : |t' - t| < η₀ := lt_of_lt_of_le ht' (min_le_left _ _)
      have h2 : |t' - t| < t - (r₀ - s) := lt_of_lt_of_le ht' (min_le_right _ _)
      have h3 := neg_abs_le (t' - t)
      have ht0 : 0 < t := by linarith [htJ.1]
      have ht'0 : 0 < t' := by linarith
      have hyN : t' • γ α ∈ N := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, ← sub_smul, norm_smul, hγn, mul_one, Real.norm_eq_abs]
        exact h1
      have hyM : t' • γ α ∈ M := by
        have h := hrad _ ⟨hx.1, hNb hx.2⟩ (t' / t) (div_pos ht'0 ht0)
        rw [smul_smul, div_mul_cancel₀ _ ht0.ne'] at h
        exact h (hNb hyN)
      have hy : t' • γ α ∈ G '' {w : Euclid 2 | w 0 ∈ Ioo (r₀ - s) (r₀ + s) ∧ w 1 ∈ Ioo (-s) s} := by
        rw [← hMN]
        exact ⟨hyM, hyN⟩
      obtain ⟨w, hwR, hGw⟩ := hy
      have hw : w = !₂[t', α] := by
        rw [← hFG w hwR.1 hwR.2, hGw, hF t' ht'0]
      subst hw
      refine ⟨?_, hGw⟩
      simpa using hwR.1
    -- `closure A ∩ J ⊆ A`: both sides are continuous on the open interval `J`
    have hAc : closure A ∩ Ioo (r₀ - s) (r₀ + s) ⊆ A := by
      rintro t ⟨htc, htJ⟩
      refine ⟨htJ, ?_⟩
      have : (𝓝[A] t).NeBot := mem_closure_iff_nhdsWithin_neBot.1 htc
      have t1 : Tendsto (fun u : ℝ => G !₂[u, α]) (𝓝[A] t) (𝓝 (G !₂[t, α])) :=
        ((hφ.continuousAt (isOpen_Ioo.mem_nhds htJ)).tendsto).mono_left nhdsWithin_le_nhds
      have t2 : Tendsto (fun u : ℝ => G !₂[u, α]) (𝓝[A] t) (𝓝 (t • γ α)) := by
        refine (((continuous_id.smul continuous_const).tendsto t).mono_left
          nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hu.2.symm
      exact tendsto_nhds_unique t1 t2
    -- `J` is preconnected and meets `A` at `r₀`
    have hr₀ : r₀ ∈ Ioo (r₀ - s) (r₀ + s) := ⟨by linarith, by linarith⟩
    have hJA := isPreconnected_Ioo.subset_of_closure_inter_subset hAo ⟨r₀, hr₀, hr₀, hG0⟩ hAc
    exact fun t ht => (hJA ht).2
  -- first conclusion: every `w ∈ R` is `(w₀, w₁)`
  have hfirst : ∀ w : Euclid 2, w 0 ∈ Ioo (r₀ - s) (r₀ + s) → w 1 ∈ Ioo (-s) s →
      G w = w 0 • γ (w 1) := by
    intro w hw0 hw1
    have hw : w = !₂[w 0, w 1] := by
      ext i
      fin_cases i <;> simp
    rw [← key (w 1) hw1 (w 0) hw0, ← hw]
  -- second conclusion: `M ∩ N = G(R)` is the image of `J × I` under `(t, α) ↦ t γ(α)`
  refine ⟨hfirst, ?_⟩
  rw [hMN]
  ext x
  constructor
  · rintro ⟨w, ⟨hw0, hw1⟩, rfl⟩
    exact ⟨(w 0, w 1), ⟨hw0, hw1⟩, (hfirst w hw0 hw1).symm⟩
  · rintro ⟨⟨t, α⟩, ⟨ht, hα⟩, rfl⟩
    refine ⟨!₂[t, α], ⟨?_, ?_⟩, key α hα t ht⟩
    · simpa using ht
    · simpa using hα

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
