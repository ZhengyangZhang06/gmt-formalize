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

/-- **Area formula with a bounded Borel Jacobian on an injective Lipschitz piece** (Simon Ch. 3,
§2, used in 7.5).  Let `F : ℝⁿ → ℝᴾ` be `L`-Lipschitz and injective on the Borel set `B`.  Then the
metric Jacobian `J = √det(DF* DF)` is Borel with `0 ≤ J ≤ Lⁿ`, `∫_{F(B)} g dHⁿ = ∫_B J (g ∘ F) dλ`
for every `g ≥ 0`, and `Hⁿ(DF(a)(S)) = J(a) λ(S)` for all `a` and all `S`.

The proof is self-contained within the frozen imports: the linear area formula (factor `T` through
a linear isometry onto its range), the regular area formula on measurable pieces where `F` is close
to an injective linear map, Rademacher's theorem for the non-differentiability set, and the
injective graph `x ↦ (F x, ε x)` for the rank-deficient set. -/
theorem Submission.codim1_lurpt_piece_area_jacobian : ∀ (P n : ℕ) (F : Euclid n → Euclid P) (B : Set (Euclid n)) (L : NNReal), LipschitzWith L F → MeasurableSet B → InjOn F B → ∃ J : Euclid n → ℝ, Measurable J ∧ (∀ a, 0 ≤ J a ∧ J a ≤ (L : ℝ) ^ n) ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ y in F '' B, g y ∂μHE[n] = ∫⁻ x in B, ENNReal.ofReal (J x) * g (F x) ∂volume) ∧ ∀ (a : Euclid n) (S : Set (Euclid n)), μHE[n] (fderiv ℝ F a '' S) = ENNReal.ofReal (J a) * volume S := by
  intro P n F B L hF hB hFi
  -- The metric Jacobian `Jac W T = √det(T* T)` of a linear map `T : ℝⁿ → W`: the linear area
  -- formula, positivity exactly on injective maps, nonnegativity and continuity.
  obtain ⟨Jac, hJac, hJnonneg, hJcont⟩ : ∃ Jac : ∀ (W : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℝ W] [FiniteDimensional ℝ W], (Euclid n →L[ℝ] W) → ℝ,
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [MeasurableSpace W] [BorelSpace W] (T : Euclid n →L[ℝ] W),
        (∀ S : Set (Euclid n), μHE[n] (T '' S) = ENNReal.ofReal (Jac W T) * volume S) ∧
        (Injective T ↔ 0 < Jac W T)) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        (T : Euclid n →L[ℝ] W), 0 ≤ Jac W T) ∧
      (∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
        Continuous (Jac W)) := by
    refine ⟨fun W _ _ _ T => √((ContinuousLinearMap.adjoint T ∘L T).det), fun W _ _ _ _ _ T => ?_,
      fun W _ _ _ T => Real.sqrt_nonneg _, fun W _ _ _ => Real.continuous_sqrt.comp
        (ContinuousLinearMap.continuous_det.comp
          (Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id))⟩
    dsimp only
    by_cases hT : Injective T
    · -- `T = U ∘ A` with `U` a linear isometry onto `range T` and `A` an endomorphism of `ℝⁿ`.
      have hRn : Module.finrank ℝ (LinearMap.range (T : Euclid n →ₗ[ℝ] W)) = n :=
        (LinearMap.finrank_range_of_inj hT).trans finrank_euclideanSpace_fin
      let e : LinearMap.range (T : Euclid n →ₗ[ℝ] W) ≃ₗᵢ[ℝ] Euclid n :=
        ((stdOrthonormalBasis ℝ _).reindex (finCongr hRn)).repr
      let U : Euclid n →ₗᵢ[ℝ] W :=
        (LinearMap.range (T : Euclid n →ₗ[ℝ] W)).subtypeₗᵢ.comp e.symm.toLinearIsometry
      let A : Euclid n →L[ℝ] Euclid n := e.toLinearIsometry.toContinuousLinearMap ∘L
        T.codRestrict _ (fun x => LinearMap.mem_range_self (T : Euclid n →ₗ[ℝ] W) x)
      have hUA : T = U.toContinuousLinearMap ∘L A := by
        ext x
        change T x = ((e.symm (e (T.codRestrict _
          (fun x => LinearMap.mem_range_self (T : Euclid n →ₗ[ℝ] W) x) x)) :
            LinearMap.range (T : Euclid n →ₗ[ℝ] W)) : W)
        rw [LinearIsometryEquiv.symm_apply_apply]
        rfl
      have hdet : (ContinuousLinearMap.adjoint T ∘L T).det = A.det ^ 2 := by
        have h1 : ContinuousLinearMap.adjoint T ∘L T = ContinuousLinearMap.adjoint A ∘L A := by
          rw [hUA, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
            ← ContinuousLinearMap.comp_assoc _ _ A, LinearIsometry.adjoint_comp_self,
            ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
        have h2 : LinearMap.det (ContinuousLinearMap.adjoint A : Euclid n →ₗ[ℝ] Euclid n) =
            LinearMap.det (A : Euclid n →ₗ[ℝ] Euclid n) := by
          rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
            ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (A : Euclid n →ₗ[ℝ] Euclid n),
            show (ContinuousLinearMap.adjoint A : Euclid n →ₗ[ℝ] Euclid n) =
              LinearMap.adjoint (A : Euclid n →ₗ[ℝ] Euclid n) from rfl,
            LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose, star_trivial]
        rw [h1, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
          h2, sq]
      rw [hdet, Real.sqrt_sq_eq_abs]
      refine ⟨fun S => ?_, ⟨fun _ => abs_pos.mpr fun h0 => ?_, fun _ => hT⟩⟩
      · calc μHE[n] (T '' S) = μHE[n] (U '' (A '' S)) := by
              rw [image_image]; conv_lhs => rw [hUA]
              rfl
          _ = μHE[n] (A '' S) := U.isometry.euclideanHausdorffMeasure_image _
          _ = volume (A '' S) := by rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
          _ = _ := Measure.addHaar_image_linearMap volume (A : Euclid n →ₗ[ℝ] Euclid n) S
      · rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
        refine h0 (LinearMap.ker_eq_bot.mpr fun x y hxy => hT ?_)
        rw [hUA, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
        exact congrArg U hxy
    · have hker : LinearMap.ker (T : Euclid n →ₗ[ℝ] W) ≠ ⊥ :=
        fun h => hT (LinearMap.ker_eq_bot.mp h)
      have h0 : (ContinuousLinearMap.adjoint T ∘L T).det = 0 := by
        rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot,
          ContinuousLinearMap.ker_adjoint_comp_self]
        exact hker
      rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero]
      refine ⟨fun S => ?_, iff_of_false hT (lt_irrefl 0)⟩
      obtain ⟨V, hV⟩ := Submodule.exists_isCompl (LinearMap.ker (T : Euclid n →ₗ[ℝ] W))
      have hVtop : V ≠ ⊤ := fun h => hker (by simpa [h] using hV.inf_eq_bot)
      have hsub : T '' S ⊆ T '' (V : Set (Euclid n)) := by
        rintro _ ⟨x, -, rfl⟩
        obtain ⟨k, hk, v, hv, rfl⟩ :=
          Submodule.mem_sup.mp (hV.sup_eq_top.symm ▸ Submodule.mem_top (x := x))
        exact ⟨v, hv, by rw [map_add, show T k = 0 from LinearMap.mem_ker.mp hk, zero_add]⟩
      have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
        (T.lipschitzWith.lipschitzOnWith (s := (V : Set (Euclid n))))
      rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
        Measure.addHaar_submodule volume V hVtop, mul_zero] at hle
      rw [zero_mul]
      exact le_antisymm ((measure_mono hsub).trans hle) bot_le
  -- Comparing pairwise distances compares the `n`-dimensional measures of the two images.
  have hcmp : ∀ (W : Type) [NormedAddCommGroup W] [MeasurableSpace W] [BorelSpace W]
      (f g : Euclid n → W) (s : Set (Euclid n)) (K : NNReal), InjOn g s →
      (∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) →
      μHE[n] (f '' s) ≤ (K : ℝ≥0∞) ^ n * μHE[n] (g '' s) := by
    intro W _ _ _ f g s K hg hfg
    have hh : LipschitzOnWith K (f ∘ invFunOn g s) (g '' s) := by
      rw [lipschitzOnWith_iff_dist_le_mul]
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa only [comp_apply, hg.leftInvOn_invFunOn hx, hg.leftInvOn_invFunOn hy] using
        hfg x hx y hy
    have himage : (f ∘ invFunOn g s) '' (g '' s) = f '' s := by
      rw [image_comp, hg.invFunOn_image Subset.rfl]
    simpa only [himage] using
      Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n hh
  -- Near an injective linear map `A`, both the Jacobian and the image measure of any map that is
  -- `δ`-close to `A` agree with those of `A` up to a factor `q > 1`.
  have hrad : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W] (A : Euclid n →L[ℝ] W), Injective A →
      ∀ q : NNReal, 1 < q → ∃ δ : NNReal, 0 < δ ∧
        (∀ A' : Euclid n →L[ℝ] W, ‖A' - A‖ ≤ δ →
          ENNReal.ofReal (Jac W A') ≤ q * ENNReal.ofReal (Jac W A) ∧
          ENNReal.ofReal (Jac W A) ≤ q * ENNReal.ofReal (Jac W A')) ∧
        (∀ (s : Set (Euclid n)) (f : Euclid n → W), ApproximatesLinearOn f A s δ →
          μHE[n] (f '' s) ≤ q * (ENNReal.ofReal (Jac W A) * volume s) ∧
          ENNReal.ofReal (Jac W A) * volume s ≤ q * μHE[n] (f '' s)) := by
    intro W _ _ _ _ _ A hA q hq
    obtain ⟨K, -, hK⟩ := (A : Euclid n →ₗ[ℝ] W).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.mpr hA)
    have hb : ∀ x y, ‖x - y‖ ≤ K * ‖A x - A y‖ := fun x y => by
      simpa only [dist_eq_norm, ContinuousLinearMap.coe_coe] using hK.le_mul_dist x y
    have herr : ∀ (δ : NNReal) (s : Set (Euclid n)) (f : Euclid n → W),
        ApproximatesLinearOn f A s δ → ∀ x ∈ s, ∀ y ∈ s,
        ‖f x - f y - (A x - A y)‖ ≤ (δ : ℝ) * K * ‖A x - A y‖ := by
      intro δ s f hf x hx y hy
      calc _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
        _ ≤ δ * (K * ‖A x - A y‖) := mul_le_mul_of_nonneg_left (hb x y) δ.2
        _ = _ := by ring
    have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ * K < 1 :=
      (continuousAt_id.mul continuousAt_const).eventually_lt continuousAt_const (by simp)
    have hupper : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ * K) ^ n < q :=
      ((continuousAt_const.add (continuousAt_id.mul continuousAt_const)).pow _).eventually_lt
        continuousAt_const (by simpa using hq)
    have hlower : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ * K)⁻¹) ^ n < q := by
      apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
      exact ((continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).inv₀
        (by simp)).pow _
    obtain ⟨δ₀, hδ₀, hδ₀s, hδ₀u, hδ₀l⟩ : ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ * K < 1 ∧
        (1 + δ₀ * K) ^ n < q ∧ ((1 - δ₀ * K)⁻¹) ^ n < q :=
      ((eventually_mem_nhdsWithin (s := Ioi (0 : NNReal)) (a := 0)).and
        ((hsmall.and (hupper.and hlower)).filter_mono nhdsWithin_le_nhds)).exists
    have hJ : 0 < Jac W A := ((hJac W A).2).1 hA
    have hqR : (1 : ℝ) < q := hq
    have hmul : Jac W A < (q : ℝ) * Jac W A := by nlinarith
    obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp
      (((hJcont W).continuousAt.eventually_lt continuousAt_const hmul).and
        (continuousAt_const.eventually_lt (continuousAt_const.mul (hJcont W).continuousAt) hmul))
    refine ⟨min δ₀ ⟨ε / 2, (half_pos hε).le⟩, lt_min hδ₀ (half_pos hε), fun A' hA' => ?_,
      fun s f hf => ⟨?_, ?_⟩⟩
    · obtain ⟨h1, h2⟩ := hnear (show dist A' A < ε by
        rw [dist_eq_norm]
        exact hA'.trans_lt (lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (half_lt_self hε)))
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q),
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
      exact ⟨ENNReal.ofReal_le_ofReal h1.le, ENNReal.ofReal_le_ofReal h2.le⟩
    · have hf₀ := hf.mono_num (min_le_left _ _)
      rw [← (hJac W A).1 s]
      refine (hcmp W f A s (1 + δ₀ * K) hA.injOn fun x hx y hy => ?_).trans ?_
      · simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one, NNReal.coe_mul]
        calc ‖f x - f y‖ ≤ ‖f x - f y - (A x - A y)‖ + ‖A x - A y‖ := norm_le_norm_sub_add _ _
          _ ≤ (δ₀ : ℝ) * K * ‖A x - A y‖ + ‖A x - A y‖ :=
            add_le_add (herr δ₀ s f hf₀ x hx y hy) le_rfl
          _ = (1 + (δ₀ : ℝ) * K) * ‖A x - A y‖ := by ring
      · gcongr
        exact_mod_cast hδ₀u.le
    · have hf₀ := hf.mono_num (min_le_left _ _)
      have hδR : (δ₀ : ℝ) * K < 1 := hδ₀s
      have hdist : ∀ x ∈ s, ∀ y ∈ s,
          dist (A x) (A y) ≤ ((1 - δ₀ * K)⁻¹ : NNReal) * dist (f x) (f y) := by
        intro x hx y hy
        have h1 := herr δ₀ s f hf₀ x hx y hy
        have h2 : ‖A x - A y‖ ≤ ‖f x - f y‖ + ‖f x - f y - (A x - A y)‖ := by
          simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (A x - A y) (f x - f y)
        simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ₀s.le, NNReal.coe_one,
          NNReal.coe_mul, inv_mul_eq_div]
        rw [le_div_iff₀ (sub_pos.mpr hδR)]
        nlinarith
      have hfinj : InjOn f s := fun x hx y hy hxy => hA (dist_le_zero.mp (by
        simpa only [hxy, dist_self, mul_zero] using hdist x hx y hy))
      rw [← (hJac W A).1 s]
      refine (hcmp W A f s _ hfinj hdist).trans ?_
      gcongr
      exact_mod_cast hδ₀l.le
  -- At almost every point of a measurable piece on which `f` is `δ`-close to `A`, the derivative
  -- of `f` is `δ`-close to `A` (Lebesgue density, as in Mathlib's `ApproximatesLinearOn`
  -- argument for square Jacobians, here for rectangular derivatives).
  have hderiv : ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Euclid n → W}
      {s : Set (Euclid n)} {A : Euclid n →L[ℝ] W} {δ : NNReal}, ApproximatesLinearOn f A s δ →
      MeasurableSet s → ∀ f' : Euclid n → Euclid n →L[ℝ] W,
      (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) → ∀ᵐ x ∂(volume.restrict s), ‖f' x - A‖₊ ≤ δ := by
    intro W _ _ f s A δ hf hs f' hf'
    filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (volume : Measure (Euclid n)) s,
      ae_restrict_mem hs] with x hx xs
    apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
    suffices H : ∀ ε, 0 < ε → ‖(f' x - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε by
      have : Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε) (𝓝[>] 0)
          (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖f' x - A‖ * 0)) :=
        Tendsto.mono_left (Continuous.tendsto (by fun_prop) 0) nhdsWithin_le_nhds
      simp only [add_zero, mul_zero] at this
      exact le_of_tendsto_of_tendsto tendsto_const_nhds this
        (eventually_nhdsWithin_of_forall fun ε hε => H ε hε)
    intro ε εpos
    open Pointwise in
    have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
      Measure.eventually_nonempty_inter_smul_of_density_one volume s x hx _
        measurableSet_closedBall (measure_closedBall_pos volume z εpos).ne'
    obtain ⟨ρ, ρpos, hρ⟩ :
        ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : Euclid n | ‖f y - f x - (f' x) (y - x)‖ ≤ ε * ‖y - x‖} :=
      mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xs).isLittleO εpos)
    open Pointwise in
    have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ :=
      nhdsWithin_le_nhds (eventually_singleton_add_smul_subset isBounded_closedBall
        (ball_mem_nhds x ρpos))
    open Pointwise in
    obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ : ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
        {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
      (B₁.and (B₂.and self_mem_nhdsWithin)).exists
    obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
      open Pointwise in
      simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
      rcases hy with ⟨a, az, ha⟩
      exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
    have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
      calc ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
        _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
    have I : r * ‖(f' x - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
      calc r * ‖(f' x - A) a‖ = ‖(f' x - A) (r • a)‖ := by
            simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
        _ = ‖f y - f x - A (y - x) - (f y - f x - (f' x) (y - x))‖ := by
            simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left,
              FunLike.coe_sub, Pi.sub_apply, map_smul, smul_sub]
        _ ≤ ‖f y - f x - A (y - x)‖ + ‖f y - f x - (f' x) (y - x)‖ := norm_sub_le _ _
        _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩)
        _ = r * (δ + ε) * ‖a‖ := by
            simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            ring
        _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
    calc ‖(f' x - A) z‖ = ‖(f' x - A) a + (f' x - A) (z - a)‖ := by
          rw [← map_add, add_sub_cancel]
      _ ≤ ‖(f' x - A) a‖ + ‖(f' x - A) (z - a)‖ := norm_add_le _ _
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ‖z - a‖ := by
          apply add_le_add
          · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
          · apply ContinuousLinearMap.le_opNorm
      _ ≤ (δ + ε) * (‖z‖ + ε) + ‖f' x - A‖ * ε := by
          rw [mem_closedBall_iff_norm'] at az
          gcongr
  -- The area formula for an injective map whose derivative is injective on a measurable set.
  have hreg : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W] (s : Set (Euclid n)) (f : Euclid n → W)
      (f' : Euclid n → Euclid n →L[ℝ] W), MeasurableSet s →
      (∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) → (∀ x ∈ s, Injective (f' x)) → InjOn f s →
      μHE[n] (f '' s) = ∫⁻ x in s, ENNReal.ofReal (Jac W (f' x)) ∂volume := by
    intro W _ _ _ _ _ s f f' hs hf' hinjd hinj
    have hcomp : ∀ q : NNReal, 1 < q →
        μHE[n] (f '' s) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s, ENNReal.ofReal (Jac W (f' x)) ∂volume ∧
        ∫⁻ x in s, ENNReal.ofReal (Jac W (f' x)) ∂volume ≤ (q : ℝ≥0∞) ^ 2 * μHE[n] (f '' s) := by
      intro q hq
      rcases eq_empty_or_nonempty s with rfl | hsne
      · simp
      have hchoice : ∀ A : Euclid n →L[ℝ] W, ∃ δ : NNReal, 0 < δ ∧ (Injective A →
          (∀ A' : Euclid n →L[ℝ] W, ‖A' - A‖ ≤ δ →
            ENNReal.ofReal (Jac W A') ≤ q * ENNReal.ofReal (Jac W A) ∧
            ENNReal.ofReal (Jac W A) ≤ q * ENNReal.ofReal (Jac W A')) ∧
          (∀ (t : Set (Euclid n)) (g : Euclid n → W), ApproximatesLinearOn g A t δ →
            μHE[n] (g '' t) ≤ q * (ENNReal.ofReal (Jac W A) * volume t) ∧
            ENNReal.ofReal (Jac W A) * volume t ≤ q * μHE[n] (g '' t))) := by
        intro A
        by_cases hA : Injective A
        · obtain ⟨δ, hδ, h⟩ := hrad W A hA q hq
          exact ⟨δ, hδ, fun _ => h⟩
        · exact ⟨1, one_pos, fun h => (hA h).elim⟩
      choose δ hδpos hδ using hchoice
      obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
        exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
          (fun A => (hδpos A).ne')
      have hseq : s = ⋃ i, s ∩ t i := by
        rw [← inter_iUnion]
        exact (inter_eq_left.mpr hcover).symm
      have hpiece : ∀ i, μHE[n] (f '' (s ∩ t i)) ≤
            (q : ℝ≥0∞) ^ 2 * ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac W (f' x)) ∂volume ∧
          ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac W (f' x)) ∂volume ≤
            (q : ℝ≥0∞) ^ 2 * μHE[n] (f '' (s ∩ t i)) := by
        intro i
        obtain ⟨x₀, hx₀, hAi⟩ := hactual hsne i
        obtain ⟨hJ, harea⟩ := hδ (A i) (hAi ▸ hinjd x₀ hx₀)
        obtain ⟨hup, hlow⟩ := harea (s ∩ t i) f (happrox i)
        have hd := hderiv W (happrox i) (hs.inter (ht i)) f'
          (fun x hx => (hf' x hx.1).mono inter_subset_left)
        have hJup : ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac W (f' x)) ∂volume ≤
            q * (ENNReal.ofReal (Jac W (A i)) * volume (s ∩ t i)) := by
          calc _ ≤ ∫⁻ _ in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (Jac W (A i)) ∂volume :=
                lintegral_mono_ae (hd.mono fun x hx => (hJ (f' x) hx).1)
            _ = _ := by rw [setLIntegral_const, mul_assoc]
        have hJlow : ENNReal.ofReal (Jac W (A i)) * volume (s ∩ t i) ≤
            q * ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac W (f' x)) ∂volume := by
          calc _ = ∫⁻ _ in s ∩ t i, ENNReal.ofReal (Jac W (A i)) ∂volume :=
                (setLIntegral_const _ _).symm
            _ ≤ ∫⁻ x in s ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (Jac W (f' x)) ∂volume :=
                lintegral_mono_ae (hd.mono fun x hx => (hJ (f' x) hx).2)
            _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
        rw [pow_two, mul_assoc, mul_assoc]
        exact ⟨hup.trans (by gcongr), hJup.trans (by gcongr)⟩
      have hsumimage : μHE[n] (f '' s) = ∑' i, μHE[n] (f '' (s ∩ t i)) := by
        conv_lhs => rw [hseq, image_iUnion]
        exact measure_iUnion (fun i j hij => Disjoint.image (Disjoint.mono inter_subset_right
            inter_subset_right (hdisj hij)) hinj inter_subset_left inter_subset_left)
          fun i => (hs.inter (ht i)).image_of_continuousOn_injOn
            (fun x hx => (hf' x hx.1).continuousWithinAt.mono inter_subset_left)
            (hinj.mono inter_subset_left)
      have hsumint : ∫⁻ x in s, ENNReal.ofReal (Jac W (f' x)) ∂volume =
          ∑' i, ∫⁻ x in s ∩ t i, ENNReal.ofReal (Jac W (f' x)) ∂volume := by
        conv_lhs => rw [hseq]
        exact lintegral_iUnion (fun i => hs.inter (ht i))
          (pairwise_disjoint_mono hdisj fun _ => inter_subset_right) _
      rw [hsumimage, hsumint]
      exact ⟨(ENNReal.tsum_le_tsum fun i => (hpiece i).1).trans_eq ENNReal.tsum_mul_left,
        (ENNReal.tsum_le_tsum fun i => (hpiece i).2).trans_eq ENNReal.tsum_mul_left⟩
    have hlim : ∀ a : ℝ≥0∞, Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
      intro a
      have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
        (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
      simpa only [one_pow, one_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
    exact le_antisymm
      (ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun q hq => (hcomp q hq).1))
      (ge_of_tendsto (hlim _) (eventually_nhdsWithin_of_forall fun q hq => (hcomp q hq).2))
  have hJ0 : ∀ T : Euclid n →L[ℝ] Euclid P, Jac (Euclid P) T = 0 ↔ ¬Injective T := fun T =>
    ⟨fun h hT => (((hJac _ T).2).1 hT).ne' h,
      fun h => le_antisymm (not_lt.mp fun h' => h (((hJac _ T).2).2 h')) (hJnonneg _ T)⟩
  -- Rank-deficient differentiability points have null image: `F` is the projection of the
  -- injective graph `x ↦ (F x, ε x)`, whose Jacobian tends to `0` there as `ε → 0`.
  set C := {x | DifferentiableAt ℝ F x ∧ ¬Injective (fderiv ℝ F x)} with hCdef
  have hCm : MeasurableSet C := by
    have hCeq : C = {x | DifferentiableAt ℝ F x} ∩
        (fun x => Jac (Euclid P) (fderiv ℝ F x)) ⁻¹' {0} := by
      ext x
      simp only [hCdef, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, hJ0]
    rw [hCeq]
    exact (measurableSet_of_differentiableAt ℝ F).inter
      ((hJcont _).measurable.comp (measurable_fderiv ℝ F) (measurableSet_singleton 0))
  have hcrit : μHE[n] (F '' C) = 0 := by
    let G : (Euclid n →L[ℝ] Euclid P) → ℝ → (Euclid n →L[ℝ] WithLp 2 (Euclid P × Euclid n)) :=
      fun T ε => (WithLp.prodContinuousLinearEquiv 2 ℝ (Euclid P)
        (Euclid n)).symm.toContinuousLinearMap ∘L (T.prod (ε • ContinuousLinearMap.id ℝ (Euclid n)))
    have hGc : Continuous fun p : (Euclid n →L[ℝ] Euclid P) × ℝ =>
        Jac (WithLp 2 (Euclid P × Euclid n)) (G p.1 p.2) :=
      (hJcont _).comp (continuous_const.clm_comp ((ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
        (continuous_fst.prodMk (continuous_snd.smul continuous_const))))
    have hGinj : ∀ (T : Euclid n →L[ℝ] Euclid P) (ε : ℝ) (x y : Euclid n),
        G T ε x = G T ε y → T x = T y ∧ ε • x = ε • y := fun T ε x y h =>
      ⟨congrArg WithLp.fst h, congrArg WithLp.snd h⟩
    have hG0 : ∀ T : Euclid n →L[ℝ] Euclid P, ¬Injective T →
        Jac (WithLp 2 (Euclid P × Euclid n)) (G T 0) = 0 := by
      intro T hT
      refine le_antisymm (not_lt.mp fun h => hT fun x y hxy => ((hJac _ (G T 0)).2.2 h) ?_)
        (hJnonneg _ _)
      show WithLp.toLp 2 (T x, (0 : ℝ) • x) = WithLp.toLp 2 (T y, (0 : ℝ) • y)
      rw [hxy, zero_smul, zero_smul]
    have hk : ∀ k : ℕ, μHE[n] (F '' (C ∩ closedBall 0 k)) = 0 := by
      intro k
      have ht : MeasurableSet (C ∩ closedBall (0 : Euclid n) k) :=
        hCm.inter measurableSet_closedBall
      obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : Euclid n →L[ℝ] Euclid P) L).prod
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn hGc.continuousOn
      have hle : ∀ ε : ℝ, 0 < ε → μHE[n] (F '' (C ∩ closedBall 0 k)) ≤
          ∫⁻ x in C ∩ closedBall 0 k, ENNReal.ofReal (Jac _ (G (fderiv ℝ F x) ε)) ∂volume := by
        intro ε hε
        rw [← hreg _ _ (fun x => WithLp.toLp 2 (F x, ε • x)) (fun x => G (fderiv ℝ F x) ε) ht
          (fun x hx => ((WithLp.prodContinuousLinearEquiv 2 ℝ (Euclid P)
            (Euclid n)).symm.toContinuousLinearMap.hasFDerivAt.comp x
              (hx.1.1.hasFDerivAt.prodMk ((hasFDerivAt_id x).const_smul ε))).hasFDerivWithinAt)
          (fun x _ y z h => smul_right_injective _ hε.ne' (hGinj _ ε y z h).2)
          (fun x _ y _ h => smul_right_injective _ hε.ne' (congrArg WithLp.snd h))]
        have hp : LipschitzWith 1 (WithLp.fst : WithLp 2 (Euclid P × Euclid n) → Euclid P) :=
          LipschitzWith.of_dist_le_mul fun x y => by simpa using WithLp.dist_fst_le x y
        have := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
          (hp.lipschitzOnWith (s := (fun x : Euclid n => WithLp.toLp 2 (F x, ε • x)) ''
            (C ∩ closedBall 0 k)))
        rwa [image_image, ENNReal.coe_one, one_pow, one_mul] at this
      have hfin : ∫⁻ _ in C ∩ closedBall (0 : Euclid n) k, ENNReal.ofReal M ∂volume ≠ ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          ((measure_mono inter_subset_right).trans_lt measure_closedBall_lt_top).ne
      have hlim := tendsto_lintegral_filter_of_dominated_convergence
        (μ := volume.restrict (C ∩ closedBall 0 k))
        (F := fun ε x => ENNReal.ofReal (Jac _ (G (fderiv ℝ F x) ε))) (f := fun _ => 0)
        (fun _ => ENNReal.ofReal M) (l := 𝓝[>] (0 : ℝ))
        (Eventually.of_forall fun ε => ((hGc.comp (continuous_id.prodMk
          continuous_const)).measurable.comp (measurable_fderiv ℝ F)).ennreal_ofReal)
        (by
          filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε
          exact Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
            (hM (fderiv ℝ F x, ε) ⟨mem_closedBall_zero_iff.mpr (norm_fderiv_le_of_lipschitz ℝ hF),
              by linarith [hε.1], hε.2.le⟩)))
        hfin
        (by
          filter_upwards [ae_restrict_mem ht] with x hx
          exact ((ENNReal.continuous_ofReal.comp (hGc.comp (continuous_const.prodMk
            continuous_id))).tendsto' 0 0 (by
              show ENNReal.ofReal (Jac _ (G (fderiv ℝ F x) 0)) = 0
              rw [hG0 _ hx.1.2, ENNReal.ofReal_zero])).mono_left nhdsWithin_le_nhds)
      rw [lintegral_zero] at hlim
      exact le_antisymm (ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε =>
        hle ε hε)) bot_le
    refine measure_mono_null ?_ (measure_iUnion_null hk)
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨⌈‖x‖⌉₊, x, ⟨hx, mem_closedBall_zero_iff.mpr (Nat.le_ceil _)⟩, rfl⟩
  -- Rademacher: the points of non-differentiability have null image.
  have hnd : μHE[n] (F '' {x | ¬DifferentiableAt ℝ F x}) = 0 := by
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hF.lipschitzOnWith (s := {x | ¬DifferentiableAt ℝ F x}))
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      ae_iff.mp (hF.ae_differentiableAt (μ := volume)), mul_zero] at hle
    exact le_antisymm hle bot_le
  -- The area formula on measurable subsets of `B`.
  set R := {x | DifferentiableAt ℝ F x ∧ Injective (fderiv ℝ F x)} with hRdef
  have hRm : MeasurableSet R := by
    have hReq : R = {x | DifferentiableAt ℝ F x} \ C := by
      ext x
      rw [Set.mem_sdiff]
      exact ⟨fun h => ⟨h.1, fun h' => h'.2 h.2⟩, fun h => ⟨h.1, not_not.mp fun hi => h.2 ⟨h.1, hi⟩⟩⟩
    rw [hReq]
    exact (measurableSet_of_differentiableAt ℝ F).diff hCm
  have hset : ∀ A ⊆ B, MeasurableSet A →
      μHE[n] (F '' A) = ∫⁻ x in A, ENNReal.ofReal (Jac (Euclid P) (fderiv ℝ F x)) ∂volume := by
    intro A hAB hA
    have h1 : μHE[n] (F '' A) = μHE[n] (F '' (A ∩ R)) := by
      refine le_antisymm ?_ (measure_mono (image_mono inter_subset_left))
      calc μHE[n] (F '' A) ≤
            μHE[n] (F '' (A ∩ R) ∪ (F '' {x | ¬DifferentiableAt ℝ F x} ∪ F '' C)) := by
            refine measure_mono ?_
            rintro _ ⟨x, hx, rfl⟩
            by_cases hd : DifferentiableAt ℝ F x
            · by_cases hi : Injective (fderiv ℝ F x)
              · exact Or.inl ⟨x, ⟨hx, hd, hi⟩, rfl⟩
              · exact Or.inr (Or.inr ⟨x, ⟨hd, hi⟩, rfl⟩)
            · exact Or.inr (Or.inl ⟨x, hd, rfl⟩)
        _ ≤ μHE[n] (F '' (A ∩ R)) + μHE[n] (F '' {x | ¬DifferentiableAt ℝ F x} ∪ F '' C) :=
            measure_union_le _ _
        _ = μHE[n] (F '' (A ∩ R)) := by rw [measure_union_null hnd hcrit, add_zero]
    rw [h1, hreg (Euclid P) (A ∩ R) F (fderiv ℝ F) (hA.inter hRm)
      (fun x hx => hx.2.1.hasFDerivAt.hasFDerivWithinAt) (fun x hx => hx.2.2)
      (hFi.mono (inter_subset_left.trans hAB)), ← lintegral_indicator (hA.inter hRm),
      ← lintegral_indicator hA]
    refine lintegral_congr_ae ?_
    filter_upwards [hF.ae_differentiableAt (μ := volume)] with x hd
    by_cases hxA : x ∈ A
    · by_cases hxR : x ∈ R
      · rw [indicator_of_mem hxA, indicator_of_mem (show x ∈ A ∩ R from ⟨hxA, hxR⟩)]
      · rw [indicator_of_mem hxA, indicator_of_notMem (fun h => hxR h.2),
          (hJ0 _).mpr (fun hi => hxR ⟨hd, hi⟩), ENNReal.ofReal_zero]
    · rw [indicator_of_notMem hxA, indicator_of_notMem (fun h => hxA h.1)]
  -- Weighted transport through the measurable embedding `F|_B`.
  have hemb := hF.continuous.continuousOn.measurableEmbedding hB hFi
  have hsub := MeasurableEmbedding.subtype_coe hB
  have hJm : Measurable fun x => Jac (Euclid P) (fderiv ℝ F x) :=
    (hJcont _).measurable.comp (measurable_fderiv ℝ F)
  have hmap : Measure.map (B.domRestrict F) ((volume.withDensity
      fun x => ENNReal.ofReal (Jac (Euclid P) (fderiv ℝ F x))).comap Subtype.val) =
      μHE[n].restrict (F '' B) := by
    ext t ht
    rw [Measure.map_apply hemb.measurable ht, hsub.comap_apply, Measure.restrict_apply ht]
    have hA : MeasurableSet (Subtype.val '' (B.domRestrict F ⁻¹' t)) :=
      hsub.measurableSet_image' (hemb.measurable ht)
    rw [withDensity_apply _ hA, ← hset _ (by rintro _ ⟨u, -, rfl⟩; exact u.2) hA]
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨hu, u, u.2, rfl⟩
    · rintro ⟨hy, x, hx, rfl⟩
      exact ⟨x, ⟨⟨x, hx⟩, hy, rfl⟩, rfl⟩
  refine ⟨fun x => Jac (Euclid P) (fderiv ℝ F x), hJm, fun a => ⟨hJnonneg _ _, ?_⟩, fun g => ?_,
    fun a S => (hJac _ (fderiv ℝ F a)).1 S⟩
  · -- `J a ≤ Lⁿ`: compare `Hⁿ(DF(a)(D₁))` with `Lⁿ λ(D₁)` on the closed unit ball `D₁`.
    have hD0 : volume (closedBall (0 : Euclid n) 1) ≠ 0 :=
      (measure_closedBall_pos volume 0 one_pos).ne'
    have hDtop : volume (closedBall (0 : Euclid n) 1) ≠ ∞ := measure_closedBall_lt_top.ne
    have hle := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      ((fderiv ℝ F a).lipschitzWith.lipschitzOnWith (s := closedBall (0 : Euclid n) 1))
    rw [(hJac _ (fderiv ℝ F a)).1, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] at hle
    have hnorm : ‖fderiv ℝ F a‖₊ ≤ L := by
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact norm_fderiv_le_of_lipschitz ℝ hF
    have hle' : ENNReal.ofReal (Jac (Euclid P) (fderiv ℝ F a)) ≤ ENNReal.ofReal ((L : ℝ) ^ n) := by
      rw [ENNReal.ofReal_pow L.coe_nonneg, ENNReal.ofReal_coe_nnreal,
        ← ENNReal.mul_le_mul_iff_left hD0 hDtop]
      refine hle.trans ?_
      gcongr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle'
  · rw [← hmap, hemb.lintegral_map]
    refine (lintegral_subtype_comap hB (fun y => g (F y))).trans ?_
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hB]
    · rfl
    · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
    · exact hJm.ennreal_ofReal.aemeasurable

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
