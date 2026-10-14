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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

namespace Submission

/-- Integer median of an integer-valued function on the open unit cube `Q₁ ⊆ ℝ^{m+1}` (Simon
Ch. 6, 5.1, (31) and (35)): some `β ∈ ℤ` has `Lⁿ(Q₁ ∩ {β ≤ u}) ≥ 1/2`, `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`
and `|β| ≤ 2 ∫_{Q₁} |u|`.  `β` is the least integer with `Lⁿ(Q₁ ∩ {u ≤ β}) ≥ 1/2`; integrality
makes `{β ≤ u}` the complement of `{u ≤ β - 1}`, and Chebyshev's inequality for `|u|` gives both
the existence of `β` and the bound. -/
theorem dor_lmb_fcd_cp_integer_median : ∀ (m : ℕ) (u : Euclid (m + 1) → ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → ∃ β : ℤ, 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | (β : ℝ) ≤ u y}) ∧ 1 / 2 ≤ volume ({y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} ∩ {y | u y ≤ (β : ℝ)}) ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| := by
  intro m u hZ hu
  set Q : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1} with hQ
  -- Step 0: `Q₁` is the preimage of the box `(0, 1)ⁿ` under the measure-preserving coordinate map,
  -- so it is measurable with `Lⁿ(Q₁) = 1`.
  have hbox : MeasurableSet (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hQeq : Q = WithLp.ofLp ⁻¹' (univ.pi fun _ : Fin (m + 1) => Ioo (0 : ℝ) 1) := by
    ext y
    simp [Q, Set.mem_pi]
  have hQm : MeasurableSet Q := by
    rw [hQeq]
    exact (PiLp.volume_preserving_ofLp (Fin (m + 1))).measurable hbox
  have hQ1 : volume Q = 1 := by
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage hbox.nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp
  -- Work with the probability measure `μ = Lⁿ⌞Q₁`; `Lⁿ(Q₁ ∩ s) = μ(s)` for every set `s`.
  set μ : Measure (Euclid (m + 1)) := volume.restrict Q with hμQ
  have hμ : ∀ s, volume (Q ∩ s) = μ s := fun s => by
    rw [hμQ, Measure.restrict_apply' hQm, inter_comm]
  have hμuniv : μ univ = 1 := by rw [← hμ, inter_univ, hQ1]
  have : IsFiniteMeasure μ := ⟨by rw [hμuniv]; exact ENNReal.one_lt_top⟩
  simp only [hμ]
  set I := ∫ y, |u y| ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => abs_nonneg _
  -- Chebyshev: `ε μ({ε ≤ |u|}) ≤ ∫ |u| dμ`; no measurability of `u` is needed.
  have hmarkov : ∀ ε : ℝ, ε * μ.real {y | ε ≤ |u y|} ≤ I := fun ε =>
    mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
      (Integrable.abs (μ := μ) hu) ε
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by norm_num
  -- Tails: for `N > 2 ∫ |u|`, `μ({N ≤ |u|}) < 1/2`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * I)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by linarith) hN
  have htail : μ {y | (N : ℝ) ≤ |u y|} < 1 / 2 := by
    have h1 := hmarkov N
    have h2 : μ.real {y | (N : ℝ) ≤ |u y|} < 1 / 2 := not_le.1 fun h => by nlinarith
    rw [← hhalf, measureReal_def] at h2
    exact (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by norm_num)).1 h2
  -- `μ(A) + μ(B) ≥ 1` and `μ(B) < 1/2` force `μ(A) ≥ 1/2`.
  have hcompl : ∀ a b : ℝ≥0∞, 1 ≤ a + b → b < 1 / 2 → 1 / 2 ≤ a := by
    intro a b hab hb
    refine not_lt.1 fun h => ?_
    have h' := ENNReal.add_lt_add h hb
    rw [ENNReal.add_halves] at h'
    exact absurd hab (not_le.2 h')
  -- Steps 1–2: the least integer `β` with `μ({u ≤ β}) ≥ 1/2` (Simon (31)).  It exists since
  -- `μ({u ≤ N}) ≥ 1/2` while `μ({u ≤ z}) < 1/2` for `z < -N`.
  have hS : ∃ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} := by
    refine ⟨N, hcompl _ (μ {y | u y ≤ ((N : ℤ) : ℝ)}ᶜ) (hμuniv ▸ measure_univ_le_add_compl _)
      (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail)⟩
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, Int.cast_natCast] at hy ⊢
    exact hy.le.trans (le_abs_self _)
  have hSb : ∃ b : ℤ, ∀ z : ℤ, 1 / 2 ≤ μ {y | u y ≤ z} → b ≤ z := by
    refine ⟨-N, fun z hz => not_lt.1 fun hlt => ?_⟩
    have hz' : (z : ℝ) ≤ -(N : ℝ) := by exact_mod_cast hlt.le
    refine absurd hz (not_le.2 (lt_of_le_of_lt (measure_mono fun y hy => ?_) htail))
    simp only [mem_ofPred_eq] at hy ⊢
    linarith [neg_abs_le (u y)]
  obtain ⟨β, hβ, hβmin⟩ := Int.exists_least_of_bdd hSb hS
  have hβ1 : μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} < 1 / 2 :=
    not_le.1 fun h => by have := hβmin (β - 1) h; omega
  -- Step 3: by integrality `{β ≤ u}ᶜ = {u ≤ β - 1}`, so `μ({β ≤ u}) ≥ 1 - μ({u ≤ β - 1}) ≥ 1/2`.
  have hup : 1 / 2 ≤ μ {y | (β : ℝ) ≤ u y} := by
    refine hcompl _ _ ?_ hβ1
    calc (1 : ℝ≥0∞) = μ univ := hμuniv.symm
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | (β : ℝ) ≤ u y}ᶜ := measure_univ_le_add_compl _
      _ ≤ μ {y | (β : ℝ) ≤ u y} + μ {y | u y ≤ ((β - 1 : ℤ) : ℝ)} := by
        gcongr
        intro y hy
        simp only [mem_compl_iff, mem_ofPred_eq, not_le] at hy ⊢
        obtain ⟨k, hk⟩ := hZ y
        rw [hk] at hy ⊢
        have hk' : k < β := by exact_mod_cast hy
        have hk'' : k ≤ β - 1 := by omega
        exact_mod_cast hk''
  refine ⟨β, hup, hβ, ?_⟩
  -- Step 4 (Simon (35)): `{|β| ≤ |u|}` contains `{β ≤ u}` (`β ≥ 0`) or `{u ≤ β}` (`β ≤ 0`), so it
  -- has measure `≥ 1/2`, and Chebyshev gives `|β| / 2 ≤ ∫ |u|`.
  have hbig : 1 / 2 ≤ μ {y | |(β : ℝ)| ≤ |u y|} := by
    rcases le_total 0 β with h0 | h0
    · refine hup.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (0 : ℝ) ≤ β := by exact_mod_cast h0
      rw [abs_of_nonneg h0']
      exact hy.trans (le_abs_self _)
    · refine hβ.trans (measure_mono fun y hy => ?_)
      simp only [mem_ofPred_eq] at hy ⊢
      have h0' : (β : ℝ) ≤ 0 := by exact_mod_cast h0
      rw [abs_of_nonpos h0']
      exact (neg_le_neg hy).trans (neg_le_abs _)
  have hbig' : 1 / 2 ≤ μ.real {y | |(β : ℝ)| ≤ |u y|} := by
    have h := ENNReal.toReal_mono (measure_ne_top μ _) hbig
    rwa [hhalf, ← measureReal_def] at h
  have h4 := hmarkov |(β : ℝ)|
  nlinarith [abs_nonneg (β : ℝ)]
/-- Deviation from a `θ`-median `β` is controlled by the double-integral oscillation (Simon Ch. 2,
Lemma 2.7, proof): `∫_W |v − β| ≤ (1 + θ⁻¹) |W|⁻¹ ∫_W ∫_W |v(x) − v(y)|`.  With the mean
`v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`; Markov's inequality on the half
`{β ≤ v}` or `{v ≤ β}` on the far side of `β` from `v̄` gives `|W| |v̄ − β| ≤ θ⁻¹ ∫_W |v − v̄|`. -/
theorem dor_lmb_fcd_cp_median_deviation : ∀ (P : ℕ) (W : Set (Euclid P)) (v : Euclid P → ℝ) (β θ : ℝ), MeasurableSet W → volume W ≠ ∞ → IntegrableOn v W → 0 < θ → θ * (volume W).toReal ≤ (volume (W ∩ {y | β ≤ v y})).toReal → θ * (volume W).toReal ≤ (volume (W ∩ {y | v y ≤ β})).toReal → ∫ y in W, |v y - β| ≤ (1 + θ⁻¹) * ((volume W).toReal)⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
  intro P W v β θ hW hWfin hv hθ hge hle
  -- `volume⌞W` is a finite measure; write `m = |W|`
  have : IsFiniteMeasure (volume.restrict W) := isFiniteMeasure_restrict.mpr hWfin
  set m := (volume W).toReal
  -- Step 0: if `|W| = 0`, then `volume⌞W = 0` and both sides vanish
  rcases (ENNReal.toReal_nonneg : 0 ≤ m).eq_or_lt with hm | hm
  · have hW0 : volume W = 0 :=
      ((ENNReal.toReal_eq_zero_iff _).mp hm.symm).resolve_right hWfin
    simp [Measure.restrict_eq_zero.mpr hW0]
  -- Step 1: integrability; the partial integral is integrable by Fubini
  have hvi : Integrable v (volume.restrict W) := hv
  have hint : ∀ c : ℝ, Integrable (fun x => |v x - c|) (volume.restrict W) := fun c =>
    (hvi.sub (integrable_const c)).abs
  have hprod : Integrable (fun p : Euclid P × Euclid P => |v p.1 - v p.2|)
      ((volume.restrict W).prod (volume.restrict W)) :=
    ((hvi.comp_fst _).sub (hvi.comp_snd _)).abs
  have hG : Integrable (fun x => ∫ y in W, |v x - v y|) (volume.restrict W) :=
    hprod.integral_prod_left
  -- Step 2: with the mean `v̄ = |W|⁻¹ ∫_W v`, `|v x − v̄| ≤ |W|⁻¹ ∫_W |v x − v y| dy`
  set vbar := m⁻¹ * ∫ y in W, v y with hvbar
  have hpt : ∀ x, |v x - vbar| ≤ m⁻¹ * ∫ y in W, |v x - v y| := by
    intro x
    have h1 : ∫ y in W, (v x - v y) = m * v x - ∫ y in W, v y := by
      rw [integral_sub (integrable_const _) hvi, integral_const, measureReal_restrict_apply_univ,
        smul_eq_mul]
      rfl
    have h2 : v x - vbar = m⁻¹ * ∫ y in W, (v x - v y) := by
      rw [h1, hvbar, mul_sub, ← mul_assoc, inv_mul_cancel₀ hm.ne', one_mul]
    rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hm)]
    exact mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (inv_nonneg.mpr hm.le)
  have hJ : ∫ x in W, |v x - vbar| ≤ m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by
    rw [← integral_const_mul]
    exact integral_mono (hint vbar) (hG.const_mul _) hpt
  -- Step 3: `|v − v̄| ≥ |β − v̄|` on the half on the far side of `β`, which has measure `≥ θ|W|`
  set I := ∫ x in W, |v x - vbar| with hI
  have hmeas : θ * m ≤ (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} := by
    rcases le_total vbar β with hb | hb
    · refine hge.trans ?_
      rw [show (volume (W ∩ {y | β ≤ v y})).toReal = (volume.restrict W).real {y | β ≤ v y} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : β ≤ v x) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonneg (sub_nonneg.mpr hb), abs_of_nonneg (by linarith)]
      linarith
    · refine hle.trans ?_
      rw [show (volume (W ∩ {y | v y ≤ β})).toReal = (volume.restrict W).real {y | v y ≤ β} by
        rw [Measure.real, Measure.restrict_apply' hW, Set.inter_comm]]
      refine measureReal_mono (fun x (hx : v x ≤ β) => ?_)
      show |β - vbar| ≤ |v x - vbar|
      rw [abs_of_nonpos (sub_nonpos.mpr hb), abs_of_nonpos (by linarith)]
      linarith
  -- Markov's inequality for `|v − v̄|` at level `|β − v̄|`
  have hM : |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} ≤ I :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (hint vbar) _
  have hmed : m * |vbar - β| ≤ θ⁻¹ * I := by
    rw [abs_sub_comm, le_inv_mul_iff₀ hθ]
    calc θ * (m * |β - vbar|) = |β - vbar| * (θ * m) := by ring
      _ ≤ |β - vbar| * (volume.restrict W).real {x | |β - vbar| ≤ |v x - vbar|} :=
        mul_le_mul_of_nonneg_left hmeas (abs_nonneg _)
      _ ≤ I := hM
  -- Step 4: triangle inequality `|v − β| ≤ |v − v̄| + |v̄ − β|`
  have htri : ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := by
    have h3 : ∫ y in W, (|v y - vbar| + |vbar - β|) = I + m * |vbar - β| := by
      rw [integral_add (hint vbar) (integrable_const _), integral_const,
        measureReal_restrict_apply_univ, smul_eq_mul]
      rfl
    rw [← h3]
    exact integral_mono (hint β) ((hint vbar).add (integrable_const _))
      fun y => abs_sub_le (v y) vbar β
  calc ∫ y in W, |v y - β| ≤ I + m * |vbar - β| := htri
    _ ≤ I + θ⁻¹ * I := by linarith
    _ = (1 + θ⁻¹) * I := by ring
    _ ≤ (1 + θ⁻¹) * (m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y|) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = (1 + θ⁻¹) * m⁻¹ * ∫ x in W, ∫ y in W, |v x - v y| := by ring
/-- Fubini identity for mixed points on the cube `Q_δ = {y | ∀ i, δ < y i < 1 - δ}`: if `a_k(x, y)`
takes the coordinates `j < k` from `y` and the others from `x`, then
`∫_{Q_δ} ∫_{Q_δ} h(a_k(x, y)) dy dx = vol(Q_δ) ∫_{Q_δ} h`.  The swap `σ` exchanging `x_j` and `y_j`
for `j < k` is an involution preserving `vol ⊗ vol` (a factorwise product of swaps and identities)
and `Q_δ × Q_δ`, so Fubini on the finite measure space `Q_δ × Q_δ` turns the left side into
`∫_{Q_δ × Q_δ} h(x)`. -/
theorem dor_lmb_fcd_cp_mixed_point_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ y in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) = (volume {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}).toReal * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- the coordinate swap on `(Fin (m+1) → ℝ)²`
  have hτ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      ((fun j => if j < k then p.2 j else p.1 j), (fun j => if j < k then p.1 j else p.2 j)))
      (volume.prod volume) (volume.prod volume) := by
    set A := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1))
    have hA : MeasurePreserving A (Measure.pi fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
        ((volume : Measure (Fin (m + 1) → ℝ)).prod volume) :=
      measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin (m + 1)) (fun _ => volume) (fun _ => volume)
    let f : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun j => if j < k then Prod.swap else id
    have hf : ∀ j, MeasurePreserving (f j) ((volume : Measure ℝ).prod volume)
        ((volume : Measure ℝ).prod volume) := by
      intro j
      by_cases hj : j < k
      · simp only [f, hj, ite_true]
        exact Measure.measurePreserving_swap
      · simp only [f, hj, ite_false]
        exact MeasurePreserving.id _
    have hP := measurePreserving_pi (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume)
      (fun _ : Fin (m + 1) => (volume : Measure ℝ).prod volume) hf
    have hcomp := (hA.comp hP).comp hA.symm
    convert hcomp using 1
    funext p
    ext j
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
    · by_cases hj : j < k <;>
        simp [A, f, hj, MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  -- the same swap on `Euclid (m+1) × Euclid (m+1)`
  set σ : Euclid (m + 1) × Euclid (m + 1) → Euclid (m + 1) × Euclid (m + 1) := fun p =>
    (WithLp.toLp 2 (fun j => if j < k then p.2 j else p.1 j),
      WithLp.toLp 2 (fun j => if j < k then p.1 j else p.2 j)) with hσdef
  have hσ : MeasurePreserving σ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (PiLp.volume_preserving_ofLp (Fin (m + 1)))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (PiLp.volume_preserving_toLp (Fin (m + 1)))
    have := (h2.comp hτ).comp h1
    convert this using 1
    funext p
    rfl
  have hσσ : ∀ p, σ (σ p) = p := by
    intro p
    ext j
    · by_cases hj : j < k <;> simp [hσdef, hj]
    · by_cases hj : j < k <;> simp [hσdef, hj]
  let σe : (Euclid (m + 1) × Euclid (m + 1)) ≃ᵐ (Euclid (m + 1) × Euclid (m + 1)) :=
    { toFun := σ
      invFun := σ
      left_inv := hσσ
      right_inv := hσσ
      measurable_toFun := hσ.measurable
      measurable_invFun := hσ.measurable }
  have hemb : MeasurableEmbedding σ := σe.measurableEmbedding
  have hpre : σ ⁻¹' (Q ×ˢ Q) = Q ×ˢ Q := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hσdef]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · by_cases hi : i < k
        · simpa [hi] using h2 i
        · simpa [hi] using h1 i
      · by_cases hi : i < k
        · simpa [hi] using h1 i
        · simpa [hi] using h2 i
  have hQm : MeasurableSet Q := by
    have : Q = ⋂ i, ({y : Euclid (m + 1) | δ < y i} ∩ {y | y i < 1 - δ}) := by
      ext y; simp [hQ]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (by fun_prop)).inter (measurableSet_lt (by fun_prop) measurable_const)
  have hσQ : MeasurePreserving σ ((volume.prod volume).restrict (Q ×ˢ Q))
      ((volume.prod volume).restrict (Q ×ˢ Q)) := by
    have := hσ.restrict_preimage_emb hemb (Q ×ˢ Q)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict Q) =
      ((volume : Measure (Euclid (m + 1))).prod volume).restrict (Q ×ˢ Q) :=
    Measure.prod_restrict Q Q
  have hQfin : volume Q ≠ ∞ := by
    have hb : Bornology.IsBounded Q := by
      rw [Metric.isBounded_iff_subset_closedBall (0 : Euclid (m + 1))]
      refine ⟨Real.sqrt (((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2), fun y hy => ?_⟩
      rw [mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (|δ| + |1 - δ|) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            have := hy i
            rw [Real.norm_eq_abs]
            have h1 : |y i| ≤ |δ| + |1 - δ| := by
              rw [abs_le]
              constructor <;> cases abs_cases δ <;> cases abs_cases (1 - δ) <;> linarith [this.1, this.2]
            exact pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ((m : ℝ) + 1) * (|δ| + |1 - δ|) ^ 2 := by simp
    exact hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.2 hQfin
  -- integrability of `p ↦ h p.1` on `Q × Q`
  have hint1 : Integrable (fun p : Euclid (m + 1) × Euclid (m + 1) => h p.1)
      ((volume.restrict Q).prod (volume.restrict Q)) := hh.comp_fst (volume.restrict Q)
  have hint2 : Integrable (fun p => h (σ p).1) ((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr] at hint1 ⊢
    exact (hσQ.integrable_comp_emb hemb).2 hint1
  -- compute
  have e1 : ∫ x in Q, ∫ y in Q, h (WithLp.toLp 2 (fun j => if j < k then y j else x j)) =
      ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (σ p).1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) := by
    rw [hrestr]
    exact hσQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict Q)) =
      (volume Q).toReal * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    rw [integral_const_mul]
/-- Fubini along the `k`-th coordinate of the cube `Q_δ = (δ, 1 − δ)^{m+1}` (Simon Ch. 2,
proof of Lemma 2.7): for `h` integrable on `Q_δ`,
`∫_{Q_δ} ∫_δ^{1−δ} h(x[k ↦ t]) dt dx = (1 − 2δ) ∫_{Q_δ} h`.  The slice swap
`ρ(x, t) = (x[k ↦ t], x_k)` is a measure-preserving involution of `Euclid (m + 1) × ℝ` that maps
`Q_δ × (δ, 1 − δ)` onto itself. -/
theorem dor_lmb_fcd_cp_slice_integral : ∀ (m : ℕ) (δ : ℝ) (k : Fin (m + 1)) (h : Euclid (m + 1) → ℝ), IntegrableOn h {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} → ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, ∫ t in Ioo δ (1 - δ), h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) = (1 - 2 * δ) * ∫ x in {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ}, h x := by
  intro m δ k h hh
  set Q : Set (Euclid (m + 1)) := {y : Euclid (m + 1) | ∀ i, δ < y i ∧ y i < 1 - δ} with hQ
  -- Step 0: if `δ ≥ 1/2` the cube is empty and both sides vanish.
  rcases le_or_gt (1 / 2) δ with hδ | hδ
  · have hQe : Q = ∅ := by
      ext y
      simp only [hQ, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_forall]
      exact ⟨0, fun h0 => by linarith [h0.1, h0.2]⟩
    simp [hQe]
  -- Step 2: the slice swap on `(Fin (m + 1) → ℝ) × ℝ` preserves volume.  Under
  -- `piFinSuccAbove` it is `((a, b), c) ↦ ((c, b), a)`, a composition of swaps and
  -- reassociations.
  have hρ : MeasurePreserving (fun p : (Fin (m + 1) → ℝ) × ℝ => (Function.update p.1 k p.2, p.1 k))
      (volume.prod volume) (volume.prod volume) := by
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    have he : MeasurePreserving e (volume : Measure (Fin (m + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) k
    set T : (ℝ × (Fin m → ℝ)) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ := fun q => ((q.2, q.1.2), q.1.1) with hTdef
    have hT : MeasurePreserving T (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) := by
      have s1 : MeasurePreserving (Prod.map Prod.swap id : (ℝ × (Fin m → ℝ)) × ℝ → ((Fin m → ℝ) × ℝ) × ℝ)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have s2 := measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)
      have s3 : MeasurePreserving (Prod.map id Prod.swap : (Fin m → ℝ) × (ℝ × ℝ) → (Fin m → ℝ) × (ℝ × ℝ))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume))
          ((volume : Measure (Fin m → ℝ)).prod ((volume : Measure ℝ).prod volume)) :=
        (MeasurePreserving.id _).prod Measure.measurePreserving_swap
      have s4 := (measurePreserving_prodAssoc (volume : Measure (Fin m → ℝ)) (volume : Measure ℝ)
        (volume : Measure ℝ)).symm
      have s5 : MeasurePreserving (Prod.map Prod.swap id : ((Fin m → ℝ) × ℝ) × ℝ → (ℝ × (Fin m → ℝ)) × ℝ)
          (((volume : Measure (Fin m → ℝ)).prod (volume : Measure ℝ)).prod volume)
          (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
        Measure.measurePreserving_swap.prod (MeasurePreserving.id _)
      have := s5.comp (s4.comp (s3.comp (s2.comp s1)))
      convert this using 1
      funext q
      rfl
    have hE2 : MeasurePreserving (e.prodCongr (MeasurableEquiv.refl ℝ))
        ((volume : Measure (Fin (m + 1) → ℝ)).prod (volume : Measure ℝ))
        (((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))).prod volume) :=
      he.prod (MeasurePreserving.id _)
    have hfull := (hE2.symm.comp hT).comp hE2
    convert hfull using 1
    funext p
    ext j
    · simp only [Function.comp, e, T]
      simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
    · simp [e, T, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove_symm_apply,
        MeasurableEquiv.piFinSuccAbove_apply]
  -- Steps 1–2: the same map `ρ` on `Euclid (m + 1) × ℝ` (via `ofLp`/`toLp`) is a
  -- measure-preserving involution, hence a measurable embedding.
  set ρ : Euclid (m + 1) × ℝ → Euclid (m + 1) × ℝ := fun p =>
    (WithLp.toLp 2 (Function.update (WithLp.ofLp p.1) k p.2), p.1 k) with hρdef
  have hρE : MeasurePreserving ρ (volume.prod volume) (volume.prod volume) := by
    have h1 := (PiLp.volume_preserving_ofLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have h2 := (PiLp.volume_preserving_toLp (Fin (m + 1))).prod (MeasurePreserving.id (volume : Measure ℝ))
    have := (h2.comp hρ).comp h1
    convert this using 1
    funext p
    rfl
  have hρρ : ∀ p, ρ (ρ p) = p := by
    intro p
    ext j
    · by_cases hj : j = k
      · subst hj; simp [hρdef]
      · simp [hρdef]
    · simp [hρdef]
  let ρe : (Euclid (m + 1) × ℝ) ≃ᵐ (Euclid (m + 1) × ℝ) :=
    { toFun := ρ
      invFun := ρ
      left_inv := hρρ
      right_inv := hρρ
      measurable_toFun := hρE.measurable
      measurable_invFun := hρE.measurable }
  have hemb : MeasurableEmbedding ρ := ρe.measurableEmbedding
  -- Step 3: `ρ⁻¹(Q × I) = Q × I`, so `ρ` preserves `(vol⌞Q) ⊗ (vol⌞I)`.
  set I : Set ℝ := Ioo δ (1 - δ) with hI
  have hpre : ρ ⁻¹' (Q ×ˢ I) = Q ×ˢ I := by
    ext p
    simp only [mem_preimage, mem_prod, hQ, mem_ofPred_eq, hρdef, hI, mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · simpa using h1 k
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => ?_, ?_⟩
      · by_cases hi : i = k
        · subst hi; simpa using h2
        · simpa [hi] using h1 i
      · exact h1 k
  have hρQ : MeasurePreserving ρ ((volume.prod volume).restrict (Q ×ˢ I))
      ((volume.prod volume).restrict (Q ×ˢ I)) := by
    have := hρE.restrict_preimage_emb hemb (Q ×ˢ I)
    rwa [hpre] at this
  have hrestr : (volume.restrict Q).prod (volume.restrict I) =
      ((volume : Measure (Euclid (m + 1))).prod (volume : Measure ℝ)).restrict (Q ×ˢ I) :=
    Measure.prod_restrict Q I
  -- Step 4: `(x, t) ↦ h x` and `(x, t) ↦ h (x[k ↦ t])` are integrable on `Q × I`.
  have hfinI : IsFiniteMeasure (volume.restrict I) := isFiniteMeasure_restrict.2 (by simp [hI])
  have hint1 : Integrable (fun p : Euclid (m + 1) × ℝ => h p.1)
      ((volume.restrict Q).prod (volume.restrict I)) := hh.comp_fst (volume.restrict I)
  have hint2 : Integrable (fun p => h (ρ p).1) ((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr] at hint1 ⊢
    exact (hρQ.integrable_comp_emb hemb).2 hint1
  -- Step 5: Fubini, the change of variables `ρ`, and `vol(I) = 1 − 2δ`.
  have e1 : ∫ x in Q, ∫ t in I, h (WithLp.toLp 2 (Function.update (WithLp.ofLp x) k t)) =
      ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [integral_prod _ hint2]
  have e2 : ∫ p, h (ρ p).1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) := by
    rw [hrestr]
    exact hρQ.integral_comp hemb (fun p => h p.1)
  have e3 : ∫ p, h p.1 ∂((volume.restrict Q).prod (volume.restrict I)) =
      (1 - 2 * δ) * ∫ x in Q, h x := by
    rw [integral_prod _ hint1]
    simp only [integral_const, Measure.real, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, hI, Real.volume_Ioo]
    rw [integral_const_mul, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [e1, e2, e3]

end Submission

end GMT.Ch07
