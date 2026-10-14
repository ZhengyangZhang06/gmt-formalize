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

/-- Integer median of an integer-valued function of bounded variation on the open unit cube
(the BV facts used in Simon 6.5.1, (26)–(33)): the Poincaré inequality, the bound on the median
and the boundary estimate.  The proof works with translations: for a smooth `ψ` supported in an
open `S` whose segments `S + [0, 1] h` stay in the cube, the field `(∫₀¹ ψ(· - τh) dτ) h` is
admissible, which bounds `∫ (u(x + h) - u(x)) ψ(x) dx`; a duality argument (smooth cut-offs and
inner regularity) turns this into an `L¹` bound for translation differences.  Integrating over
`h` gives the Poincaré inequality, the least integer `β` with `|{u ≤ β}| ≥ 1/2` is a median, and
difference quotients of `G` together with slab estimates near the faces give the boundary bound. -/
theorem Submission.dtc_bc_tc_cl_dfm_cube_bv_median : ∀ m : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ (u : Euclid (m + 1) → ℝ) (V : ℝ), (∀ y, ∃ z : ℤ, u y = z) → IntegrableOn u {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V) → ∃ β : ℤ, ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y - β| ≤ c * V ∧ |(β : ℝ)| ≤ 2 * ∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, |u y| ∧ ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y in {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ c * V := by
  intro m
  /- Step 1: duality.  If `|∫ f ψ| ≤ B` for all smooth `ψ` with compact support in the open set
  `S` and `|ψ| ≤ 1`, then `∫_S |f| ≤ 2 B`: smooth cut-offs give `|∫_K f| ≤ B` for compact
  `K ⊆ S`, inner regularity extends this to measurable subsets, and we split `S` by the sign of
  `f`. -/
  have hdual : ∀ (f : Euclid (m + 1) → ℝ) (S : Set (Euclid (m + 1))) (B : ℝ), Integrable f →
      Measurable f → IsOpen S → volume S ≠ ⊤ →
      (∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
        (∀ x, |ψ x| ≤ 1) → |∫ x, f x * ψ x| ≤ B) → ∫ x in S, |f x| ≤ 2 * B := by
    intro f S B hf hfm hSo hSfin hB
    have H1 : ∀ K, IsCompact K → K ⊆ S → |∫ x in K, f x| ≤ B := by
      intro K hK hKS
      obtain ⟨δ, hδ, hδS⟩ := hK.exists_cthickening_subset_open hSo hKS
      have hr : ∀ k : ℕ, 0 < δ / (k + 2) := fun k => by positivity
      have hrδ : ∀ k : ℕ, δ / (k + 2) ≤ δ := fun k =>
        div_le_self hδ.le (by linarith only [(k.cast_nonneg : (0:ℝ) ≤ k)])
      choose ψ hψsm hψr hψs hψ1 using fun k : ℕ =>
        exists_contDiff_support_eq_eq_one_iff (n := ⊤)
          (isOpen_thickening : IsOpen (thickening (δ / (k + 2)) K))
          hK.isClosed (self_subset_thickening (hr k) K)
      have htsupp : ∀ k, tsupport (ψ k) ⊆ cthickening (δ / (k + 2)) K := fun k => by
        rw [tsupport, hψs k]; exact closure_thickening_subset_cthickening _ _
      have hψabs : ∀ k x, |ψ k x| ≤ 1 := fun k x => by
        have := hψr k (mem_range_self x)
        rw [abs_le]; exact ⟨by linarith only [this.1], this.2⟩
      have hbd : ∀ k, |∫ x, f x * ψ k x| ≤ B := fun k => hB (ψ k) (hψsm k)
          ((hK.cthickening).of_isClosed_subset (isClosed_tsupport _) (htsupp k))
          ((htsupp k).trans ((cthickening_mono (hrδ k) K).trans hδS)) (hψabs k)
      have hlim : Tendsto (fun k => ∫ x, f x * ψ k x) atTop (𝓝 (∫ x, K.indicator f x)) := by
        refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
          (fun k => hf.aestronglyMeasurable.mul (hψsm k).continuous.aestronglyMeasurable) hf.abs
          (fun k => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun x => ?_)
        · rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hψabs k x)
        · by_cases hx : x ∈ K
          · rw [indicator_of_mem hx]
            have : ∀ k, ψ k x = 1 := fun k => (hψ1 k x).1 hx
            simp only [this, mul_one, tendsto_const_nhds]
          · rw [indicator_of_notMem hx]
            obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl x hx
            have hev : ∀ᶠ k : ℕ in atTop, ψ k x = 0 := by
              obtain ⟨k₀, hk₀⟩ := exists_nat_gt (δ / ε)
              filter_upwards [Filter.eventually_ge_atTop k₀] with k hk
              have hxt : x ∉ thickening (δ / (k + 2)) K := by
                intro hxt
                obtain ⟨y, hyK, hxy⟩ := mem_thickening_iff.1 hxt
                have hk2 : (k₀:ℝ) ≤ k := by exact_mod_cast hk
                have hk' : δ < ε * ((k:ℝ) + 2) := by
                  rw [div_lt_iff₀ hε] at hk₀
                  have := mul_le_mul_of_nonneg_right hk2 hε.le
                  linarith only [hk₀, this, hε]
                have : δ / (k + 2) < ε := by
                  rw [div_lt_iff₀ (by positivity)]; linarith only [hk']
                exact hball (mem_ball.2 (by rw [dist_comm]; linarith only [hxy, this])) hyK
              rw [← hψs k] at hxt
              exact notMem_support.1 hxt
            exact tendsto_const_nhds.congr' (by
              filter_upwards [hev] with k hk; rw [hk, mul_zero])
      rw [integral_indicator hK.isClosed.measurableSet] at hlim
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have H2 : ∀ T, MeasurableSet T → T ⊆ S → |∫ x in T, f x| ≤ B := by
      intro T hT hTS
      have hTfin : volume T ≠ ⊤ := ne_top_of_le_ne_top hSfin (measure_mono hTS)
      have : ∀ j : ℕ, ∃ K ⊆ T, IsCompact K ∧ volume T < volume K + ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
        fun j => hT.exists_isCompact_lt_add hTfin
          (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
      choose K hKT hKc hKlt using this
      have hdiff : Tendsto (fun j => volume (T \ K j)) atTop (𝓝 0) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)) (fun _ => bot_le)
          (fun j => ?_)
        rw [Function.comp_apply, measure_sdiff (hKT j)
          (hKc j).isClosed.measurableSet.nullMeasurableSet
          (ne_top_of_le_ne_top hTfin (measure_mono (hKT j)))]
        exact tsub_le_iff_left.2 (hKlt j).le
      have hconv := hf.tendsto_setIntegral_nhds_zero hdiff
      have hle : ∀ j, |∫ x in T, f x| ≤ B + |∫ x in T \ K j, f x| := fun j => by
        rw [← union_sdiff_cancel (hKT j), setIntegral_union disjoint_sdiff_right
          (hT.diff (hKc j).isClosed.measurableSet) hf.integrableOn hf.integrableOn,
          union_sdiff_cancel (hKT j)]
        have := H1 (K j) (hKc j) ((hKT j).trans hTS)
        exact (abs_add_le _ _).trans (by linarith only [this])
      have hconv' : Tendsto (fun j => B + |∫ x in T \ K j, f x|) atTop (𝓝 (B + |0|)) :=
        tendsto_const_nhds.add ((continuous_abs.tendsto 0).comp hconv)
      rw [abs_zero, add_zero] at hconv'
      exact ge_of_tendsto' hconv' hle
    have hP : MeasurableSet {x | 0 ≤ f x} := measurableSet_le measurable_const hfm
    have hSm := hSo.measurableSet
    have e : ∫ x in S, |f x| =
        (∫ x in S ∩ {x | 0 ≤ f x}, f x) - ∫ x in S \ {x | 0 ≤ f x}, f x := by
      rw [← integral_inter_add_sdiff hP hf.abs.integrableOn, sub_eq_add_neg, ← integral_neg]
      congr 1
      · exact setIntegral_congr_fun (hSm.inter hP) (fun x hx => abs_of_nonneg hx.2)
      · exact setIntegral_congr_fun (hSm.diff hP) (fun x hx => abs_of_neg (not_le.1 hx.2))
    rw [e]
    have h1 := H2 _ (hSm.inter hP) inter_subset_left
    have h2 := H2 _ (hSm.diff hP) sdiff_subset
    linarith only [h1, h2, le_abs_self (∫ x in S ∩ {x | 0 ≤ f x}, f x),
      neg_abs_le (∫ x in S \ {x | 0 ≤ f x}, f x)]
  /- Step 2: the segment average `Ψ z = ∫₀¹ ψ (z - τ h) dτ` of a smooth compactly supported `ψ`
  is smooth, and its derivative in the direction `h` is `ψ z - ψ (z - h)`. -/
  have hΨd : ∀ (h : Euclid (m + 1)) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ z, HasFDerivAt (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h))
        (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) z := by
    intro h F _ _ _ ψ hψ hψc z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    obtain ⟨C, hC⟩ := hdc.bounded_above_of_compact_support (hψc.fderiv ℝ)
    have hsc : Continuous fun τ : ℝ => τ • h := continuous_id.smul continuous_const
    have hcont : ∀ x : Euclid (m + 1), Continuous fun τ : ℝ => ψ (x - τ • h) := fun x =>
      hψ.continuous.comp (continuous_const.sub hsc)
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
      (μ := volume.restrict (Ioc (0:ℝ) 1)) (F := fun x τ => ψ (x - τ • h))
      (F' := fun x τ => fderiv ℝ ψ (x - τ • h)) (bound := fun _ => C) (s := univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable
    · exact (hcont z).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact ((hdc.comp (continuous_const.sub hsc)).stronglyMeasurable
        (h := secondCountableTopologyEither_of_left ℝ _)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun τ x _ => hC _
    · exact integrableOn_const (by simp)
    · refine Filter.Eventually.of_forall fun τ x _ => ?_
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (x - τ • h)) (x - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 := h1.comp x ((hasFDerivAt_id x).sub_const (τ • h))
      rwa [ContinuousLinearMap.comp_id] at h2
  have hΨs : ∀ (h : Euclid (m + 1)) (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      [CompleteSpace F] (ψ : Euclid (m + 1) → F), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ContDiff ℝ k (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) := by
    intro h k
    induction k with
    | zero =>
      intro F _ _ _ ψ hψ hψc
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
        (hΨd h F ψ hψ hψc z).continuousAt)
    | succ k ih =>
      intro F _ _ _ ψ hψ hψc
      have hfd : fderiv ℝ (fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)) =
          fun z => ∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h) :=
        funext fun z => (hΨd h F ψ hψ hψc z).fderiv
      refine contDiff_succ_iff_fderiv.2 ⟨fun z => (hΨd h F ψ hψ hψc z).differentiableAt,
        fun h => absurd h (WithTop.natCast_ne_top k), ?_⟩
      rw [hfd]
      exact ih (Euclid (m + 1) →L[ℝ] F) (fderiv ℝ ψ) (contDiff_infty_iff_fderiv.1 hψ).2
        (hψc.fderiv ℝ)
  have hΨh : ∀ (h : Euclid (m + 1)) (ψ : Euclid (m + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ∀ z, (∫ τ in Ioc (0:ℝ) 1, fderiv ℝ ψ (z - τ • h)) h = ψ z - ψ (z - h) := by
    intro h ψ hψ z
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hdc : Continuous (fderiv ℝ ψ) := hψ1.continuous_fderiv one_ne_zero
    have hLc : Continuous fun τ : ℝ => fderiv ℝ ψ (z - τ • h) :=
      hdc.comp (continuous_const.sub (continuous_id.smul continuous_const))
    rw [ContinuousLinearMap.integral_apply (hLc.integrableOn_Icc.mono_set Ioc_subset_Icc_self),
      ← intervalIntegral.integral_of_le zero_le_one]
    have hderiv : ∀ τ ∈ uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => ψ (z - τ • h))
        (-(fderiv ℝ ψ (z - τ • h) h)) τ := by
      intro τ _
      have h1 : HasFDerivAt ψ (fderiv ℝ ψ (z - τ • h)) (z - τ • h) :=
        (hψ1.differentiable one_ne_zero _).hasFDerivAt
      have h2 : HasDerivAt (fun τ : ℝ => z - τ • h) (-h) τ := by
        have := ((hasDerivAt_id τ).smul_const h).const_sub z
        rwa [one_smul] at this
      have := h1.comp_hasDerivAt τ h2
      rwa [map_neg] at this
    have hint : IntervalIntegrable (fun τ : ℝ => -(fderiv ℝ ψ (z - τ • h) h)) volume 0 1 :=
      (((ContinuousLinearMap.apply ℝ ℝ h).continuous.comp hLc).neg).intervalIntegrable 0 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    rw [intervalIntegral.integral_neg, one_smul, zero_smul, sub_zero] at this
    linarith only [this]
  /- Step 3: the constants: `R` bounds the diameter of the cube, `CP` is the Poincaré constant. -/
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = m + 1 := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by rw [hR_def]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hR : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨CP, hCP_def⟩ : ∃ CP : ℝ,
      CP = 4 * R * (volume (closedBall (0 : Euclid (m + 1)) R)).toReal := ⟨_, rfl⟩
  have hCP : 0 ≤ CP := by rw [hCP_def]; positivity
  refine ⟨CP + (m + 1) * (10 + 4 * CP) + 1, by positivity, ?_⟩
  intro u V hint huQ hV
  set Q := {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} with hQ_def
  /- Step 4: the cube, `V ≥ 0`, and a measurable version `ub` of `u 1_Q`. -/
  have hQo : IsOpen Q := by
    have : Q = ⋂ i, {y : Euclid (m + 1) | 0 < y i ∧ y i < 1} := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_iInter]
    rw [this]
    refine isOpen_iInter_of_finite fun i => ?_
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  have hQm : MeasurableSet Q := hQo.measurableSet
  have hQvol : volume Q = 1 := by
    have : Q = WithLp.ofLp ⁻¹' (Set.univ.pi fun _ => Ioo (0:ℝ) 1) := by
      ext y; simp only [hQ_def, mem_ofPred_eq, mem_preimage, mem_univ_pi, mem_Ioo]
    rw [this, (PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, Real.volume_pi_Ioo]
    simp
  have hQfin : volume Q ≠ ⊤ := by rw [hQvol]; exact ENNReal.one_ne_top
  have hV0 : 0 ≤ V := by
    have := hV (fun _ => 0) contDiff_const HasCompactSupport.zero (by simp) (by simp)
    simpa using this
  obtain ⟨ub, hub_meas, hub_int, hub_zero, hub_ae⟩ : ∃ ub : Euclid (m + 1) → ℝ, Measurable ub ∧
      Integrable ub ∧ (∀ y ∉ Q, ub y = 0) ∧ ∀ᵐ y ∂(volume.restrict Q), ub y = u y := by
    refine ⟨Q.indicator (huQ.aestronglyMeasurable.mk u),
      huQ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.indicator hQm, ?_,
      fun y hy => indicator_of_notMem hy _, ?_⟩
    · rw [integrable_indicator_iff hQm]
      exact huQ.congr huQ.aestronglyMeasurable.ae_eq_mk
    · filter_upwards [huQ.aestronglyMeasurable.ae_eq_mk, ae_restrict_mem hQm] with y hy hyQ
      rw [indicator_of_mem hyQ, ← hy]
  /- Step 5: the weak translation estimate.  If `S` is open, `S + [0, 1] h ⊆ Q`, and every line
  parallel to `h` meets `S` in parameter length `≤ lam`, then the field
  `g = (lam ‖h‖)⁻¹ Ψ h` is admissible and `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`. -/
  have hweak : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam → h ≠ 0 →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∀ ψ : Euclid (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ S →
      (∀ x, |ψ x| ≤ 1) → -∫ x, (ub (x + h) - ub x) * ψ x ≤ lam * ‖h‖ * V := by
    intro S h lam hSo hseg hlam hh0 hmult ψ hψ hψc hψS hψ1
    have hA : 0 < lam * ‖h‖ := mul_pos hlam (norm_pos_iff.2 hh0)
    obtain ⟨Ψ, hΨ_def⟩ : ∃ Ψ : Euclid (m + 1) → ℝ,
        Ψ = fun z => ∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h) := ⟨_, rfl⟩
    obtain ⟨g, hg_def⟩ : ∃ g : Euclid (m + 1) → Euclid (m + 1),
        g = fun z => ((lam * ‖h‖)⁻¹ * Ψ z) • h := ⟨_, rfl⟩
    have hΨsm : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
      rw [hΨ_def]; exact contDiff_infty.2 fun k => hΨs h k ℝ ψ hψ hψc
    have hgsm : ContDiff ℝ (⊤ : ℕ∞) g := by
      rw [hg_def]; exact (contDiff_const.mul hΨsm).smul contDiff_const
    -- `g` is supported in the compact set `spt ψ + [0, 1] h ⊆ Q`
    obtain ⟨K, hK_def⟩ : ∃ K : Set (Euclid (m + 1)),
        K = (fun p : Euclid (m + 1) × ℝ => p.1 + p.2 • h) '' (tsupport ψ ×ˢ Icc (0:ℝ) 1) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := by
      rw [hK_def]
      exact (hψc.isCompact.prod isCompact_Icc).image
        (continuous_fst.add (continuous_snd.smul continuous_const))
    have hKQ : K ⊆ Q := by
      rw [hK_def]
      rintro _ ⟨⟨x, τ⟩, ⟨hx, hτ⟩, rfl⟩
      exact hseg x (hψS hx) τ hτ
    have hgK : ∀ z ∉ K, g z = 0 := by
      intro z hz
      have : Ψ z = 0 := by
        rw [hΨ_def]
        refine setIntegral_eq_zero_of_forall_eq_zero fun τ hτ => ?_
        by_contra hne
        refine hz (hK_def ▸ ⟨⟨z - τ • h, τ⟩, ⟨subset_tsupport _ hne, Ioc_subset_Icc_self hτ⟩, ?_⟩)
        exact sub_add_cancel z (τ • h)
      rw [hg_def]; simp only [this, mul_zero, zero_smul]
    have hgc : HasCompactSupport g := HasCompactSupport.intro hKc hgK
    have hgQ : tsupport g ⊆ Q := (closure_minimal (fun z hz => by
      by_contra hzK; exact hz (hgK z hzK)) hKc.isClosed).trans hKQ
    -- `|Ψ| ≤ lam`, hence `‖g‖ ≤ 1`
    have hΨb : ∀ z, |Ψ z| ≤ lam := by
      intro z
      have hmeas : MeasurableSet {τ : ℝ | z - τ • h ∈ S} :=
        (hSo.preimage (continuous_const.sub (continuous_id.smul continuous_const))).measurableSet
      rw [hΨ_def]
      calc |∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)| = ‖∫ τ in Ioc (0:ℝ) 1, ψ (z - τ • h)‖ := rfl
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, ‖ψ (z - τ • h)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ τ in Ioc (0:ℝ) 1, {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
            ((integrable_indicator_iff hmeas).2 (integrable_const (1:ℝ)).integrableOn) ?_
          refine Filter.Eventually.of_forall fun τ => ?_
          show ‖ψ (z - τ • h)‖ ≤ {τ : ℝ | z - τ • h ∈ S}.indicator 1 τ
          by_cases hτ : z - τ • h ∈ S
          · rw [indicator_of_mem (show τ ∈ {τ : ℝ | z - τ • h ∈ S} from hτ), Pi.one_apply]
            exact hψ1 (z - τ • h)
          · rw [indicator_of_notMem (show τ ∉ {τ : ℝ | z - τ • h ∈ S} from hτ),
              image_eq_zero_of_notMem_tsupport (fun h' => hτ (hψS h')), norm_zero]
        _ = (volume.restrict (Ioc (0:ℝ) 1)).real {τ : ℝ | z - τ • h ∈ S} :=
          integral_indicator_one hmeas
        _ ≤ lam := by
          rw [Measure.real, Measure.restrict_apply hmeas]
          exact ENNReal.toReal_le_of_le_ofReal hlam.le (hmult z)
    have hgb : ∀ z, ‖g z‖ ≤ 1 := by
      intro z
      rw [hg_def, norm_smul, norm_mul, norm_inv, Real.norm_of_nonneg hA.le, Real.norm_eq_abs]
      calc (lam * ‖h‖)⁻¹ * |Ψ z| * ‖h‖ ≤ (lam * ‖h‖)⁻¹ * lam * ‖h‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hΨb z) (inv_nonneg.2 hA.le))
              (norm_nonneg h)
        _ = 1 := by rw [mul_assoc, inv_mul_cancel₀ hA.ne']
    -- `div g = (lam ‖h‖)⁻¹ (ψ - ψ (· - h))`
    have htr : ∀ z, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g z) =
        (lam * ‖h‖)⁻¹ * (ψ z - ψ (z - h)) := by
      intro z
      have hd : HasFDerivAt g (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
          fderiv ℝ ψ (z - τ • h)).smulRight h) z := by
        rw [hg_def, hΨ_def]
        exact ((hΨd h ℝ ψ hψ hψc z).const_mul (lam * ‖h‖)⁻¹).smul_const h
      rw [hd.fderiv]
      refine (LinearMap.trace_smulRight (((lam * ‖h‖)⁻¹ • ∫ τ in Ioc (0:ℝ) 1,
        fderiv ℝ ψ (z - τ • h) : Euclid (m + 1) →L[ℝ] ℝ) : Euclid (m + 1) →ₗ[ℝ] ℝ) h).trans ?_
      rw [ContinuousLinearMap.coe_coe, smul_apply, hΨh h ψ hψ z, smul_eq_mul]
    -- the hypothesis applied to `g`
    have hψb : ∀ x, ‖ψ x‖ ≤ 1 := hψ1
    have hint1 : Integrable fun x => ub x * ψ x :=
      hub_int.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hψb)
    have hint2 : Integrable fun x => ub x * ψ (x - h) :=
      hub_int.mul_bdd (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => hψb _)
    have hint3 : Integrable fun x => ub (x + h) * ψ x :=
      (hub_int.comp_add_right h).mul_bdd hψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hψb)
    have key := hV g hgsm hgc hgQ hgb
    have e1 : ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) =
        (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
      calc ∫ y in Q, u y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y)
          = ∫ y in Q, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) := by
            refine integral_congr_ae ?_
            filter_upwards [hub_ae] with y hy
            rw [htr y, hy]
        _ = ∫ y, ub y * ((lam * ‖h‖)⁻¹ * (ψ y - ψ (y - h))) :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
              rw [hub_zero y hy, zero_mul]
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ y, ub y * ψ (y - h)) := by
            rw [← integral_sub hint1 hint2, ← integral_const_mul]
            congr 1; funext y; ring
        _ = (lam * ‖h‖)⁻¹ * ((∫ y, ub y * ψ y) - ∫ x, ub (x + h) * ψ x) := by
            congr 2
            rw [← integral_add_right_eq_self (fun y => ub y * ψ (y - h)) h]
            simp only [add_sub_cancel_right]
        _ = (lam * ‖h‖)⁻¹ * -∫ x, (ub (x + h) - ub x) * ψ x := by
            rw [← integral_sub hint1 hint3, ← integral_neg]
            congr 2; funext x; ring
    rw [e1] at key
    have := mul_le_mul_of_nonneg_left key hA.le
    rwa [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at this
  /- Step 6: the `L¹` translation estimate `∫_S |ub (x + h) - ub x| ≤ 2 lam ‖h‖ V`. -/
  have hGEN : ∀ (S : Set (Euclid (m + 1))) (h : Euclid (m + 1)) (lam : ℝ), IsOpen S →
      (∀ x ∈ S, ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q) → 0 < lam →
      (∀ z, volume ({τ : ℝ | z - τ • h ∈ S} ∩ Ioc (0:ℝ) 1) ≤ ENNReal.ofReal lam) →
      ∫ x in S, |ub (x + h) - ub x| ≤ 2 * (lam * ‖h‖ * V) := by
    intro S h lam hSo hseg hlam hmult
    by_cases hh : h = 0
    · subst hh; simp
    have hSQ : S ⊆ Q := fun x hx => by
      have := hseg x hx 0 ⟨le_rfl, zero_le_one⟩; rwa [zero_smul, add_zero] at this
    have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hQfin (measure_mono hSQ)
    refine hdual (fun x => ub (x + h) - ub x) S (lam * ‖h‖ * V)
      ((hub_int.comp_add_right h).sub hub_int)
      ((hub_meas.comp (measurable_add_const h)).sub hub_meas) hSo hSfin ?_
    intro ψ hψ hψc hψS hψ1
    have h1 := hweak S h lam hSo hseg hlam hh hmult ψ hψ hψc hψS hψ1
    have h2 := hweak S h lam hSo hseg hlam hh hmult (-ψ) hψ.neg hψc.neg
      (by rwa [tsupport_neg]) (fun x => by rw [Pi.neg_apply, abs_neg]; exact hψ1 x)
    have e2 : ∫ x, (ub (x + h) - ub x) * (-ψ) x = -∫ x, (ub (x + h) - ub x) * ψ x := by
      rw [← integral_neg]; congr 1; funext x; rw [Pi.neg_apply]; ring
    rw [e2] at h2
    rw [abs_le]; constructor <;> linarith only [h1, h2]
  clear hweak hdual hΨh hΨs hΨd
  /- Step 7: the Poincaré inequality.  Translating `y = x + h` and swapping the integrals,
  `∫_Q ∫_Q |ub y - ub x| ≤ ∫_{‖h‖ ≤ R} 2 ‖h‖ V dh`. -/
  have hnormle : ∀ v : Euclid (m + 1), (∀ i, |v i| ≤ 1) → ‖v‖ ≤ R := by
    intro v hv
    have h1 : ‖v‖ ^ 2 ≤ R := by
      rw [EuclideanSpace.norm_sq_eq, hR_def]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (m + 1), (1:ℝ) := Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs, sq_abs]; exact (sq_le_one_iff_abs_le_one _).2 (hv i)
        _ = m + 1 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
              Nat.cast_add, Nat.cast_one]
    exact (sq_le_sq₀ (norm_nonneg v) hR.le).1 (h1.trans (le_self_pow₀ hR1 two_ne_zero))
  have hnorm : ∀ x h : Euclid (m + 1), x ∈ Q → x + h ∈ Q → ‖h‖ ≤ R := fun x h hx hxh =>
    hnormle h fun i => by
      have h1 := hx i; have h2 := hxh i
      rw [PiLp.add_apply] at h2
      rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]
  have hnormQ : ∀ y ∈ Q, ‖y‖ ≤ R := fun y hy =>
    hnormle y fun i => abs_le.2 ⟨by linarith only [(hy i).1], (hy i).2.le⟩
  have hsegA : ∀ h : Euclid (m + 1), ∀ x ∈ (fun x => x + h) ⁻¹' Q ∩ Q,
      ∀ τ ∈ Icc (0:ℝ) 1, x + τ • h ∈ Q := by
    rintro h x ⟨hxh, hx⟩ τ ⟨hτ0, hτ1⟩ i
    have h1 := hx i; have h2 := hxh i
    rw [PiLp.add_apply] at h2
    rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rcases le_total 0 (h i) with hhi | hhi
    · have p1 := mul_nonneg hτ0 hhi
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) hhi
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
    · have p1 := mul_nonneg hτ0 (neg_nonneg.2 hhi)
      have p2 := mul_nonneg (sub_nonneg.2 hτ1) (neg_nonneg.2 hhi)
      constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2, p1, p2]
  have hAo : ∀ h : Euclid (m + 1), IsOpen ((fun x => x + h) ⁻¹' Q ∩ Q) := fun h =>
    (hQo.preimage (continuous_id.add continuous_const)).inter hQo
  have hTR : ∀ h : Euclid (m + 1),
      ∫ x in (fun x => x + h) ⁻¹' Q ∩ Q, |ub (x + h) - ub x| ≤ 2 * (‖h‖ * V) := by
    intro h
    have := hGEN _ h 1 (hAo h) (hsegA h) one_pos (fun z => by
      rw [ENNReal.ofReal_one]
      exact (measure_mono inter_subset_right).trans (by rw [Real.volume_Ioc, sub_zero,
        ENNReal.ofReal_one]))
    rwa [one_mul] at this
  have hJ : ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| ≤
      ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) := by
    have hΦ : (Function.uncurry fun x h : Euclid (m + 1) =>
          Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) =
        {p : Euclid (m + 1) × Euclid (m + 1) | p.2 + p.1 ∈ Q}.indicator
          (fun p => ENNReal.ofReal |ub (p.2 + p.1) - ub p.1|) := by
      funext ⟨x, h⟩
      simp only [Function.uncurry_apply_pair, Set.indicator_apply, mem_ofPred_eq]
    have hΦm : Measurable (Function.uncurry fun x h : Euclid (m + 1) =>
        Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x)) := by
      rw [hΦ]
      exact (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
        ((hub_meas.comp (measurable_snd.add measurable_fst)).sub
          (hub_meas.comp measurable_fst)))).indicator
        (hQm.preimage (measurable_snd.add measurable_fst))
    calc ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x|
        = ∫⁻ x in Q, ∫⁻ h, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) := by
          refine lintegral_congr fun x => ?_
          rw [← lintegral_indicator hQm, lintegral_add_right_eq_self]
      _ = ∫⁻ h, ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) :=
          lintegral_lintegral_swap hΦm.aemeasurable
      _ ≤ ∫⁻ h, (closedBall (0 : Euclid (m + 1)) R).indicator
            (fun _ => ENNReal.ofReal (2 * (R * V))) h := by
          refine lintegral_mono fun h => ?_
          have hAm := (hAo h).measurableSet
          have e1 : ∫⁻ x in Q, Q.indicator (fun y => ENNReal.ofReal |ub y - ub x|) (h + x) =
              ∫⁻ x in (fun x => x + h) ⁻¹' Q ∩ Q, ENNReal.ofReal |ub (x + h) - ub x| := by
            rw [← Measure.restrict_restrict (hQm.preimage (measurable_add_const h)),
              ← lintegral_indicator (hQm.preimage (measurable_add_const h))]
            refine lintegral_congr fun x => ?_
            rw [add_comm h x]
            by_cases hx : x + h ∈ Q
            · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ (fun x => x + h) ⁻¹' Q from hx)]
            · rw [indicator_of_notMem hx,
                indicator_of_notMem (show x ∉ (fun x => x + h) ⁻¹' Q from hx)]
          have hint : IntegrableOn (fun x => |ub (x + h) - ub x|) ((fun x => x + h) ⁻¹' Q ∩ Q) :=
            ((hub_int.comp_add_right h).sub hub_int).abs.integrableOn
          rw [e1, ← ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun x => abs_nonneg _)]
          by_cases hh : h ∈ closedBall (0 : Euclid (m + 1)) R
          · rw [indicator_of_mem hh]
            refine ENNReal.ofReal_le_ofReal ((hTR h).trans ?_)
            have : ‖h‖ ≤ R := by rwa [mem_closedBall, dist_zero_right] at hh
            have := mul_le_mul_of_nonneg_right this hV0
            linarith only [this]
          · rw [indicator_of_notMem hh]
            have hempty : (fun x => x + h) ⁻¹' Q ∩ Q = ∅ := by
              refine Set.eq_empty_of_forall_notMem fun x hx => hh ?_
              rw [mem_closedBall, dist_zero_right]; exact hnorm x h hx.2 hx.1
            rw [hempty, Measure.restrict_empty, integral_zero_measure, ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R) :=
          lintegral_indicator_const measurableSet_closedBall _
  clear hsegA hAo hnormle
  /- Step 8: the integer median `β`: the least integer with `|{ub ≤ β} ∩ Q| ≥ 1/2`. -/
  have hμprob : IsProbabilityMeasure (volume.restrict Q) :=
    isProbabilityMeasure_iff.2 (by rw [Measure.restrict_apply_univ, hQvol])
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∫ y in Q, |ub y| := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM_def ▸ integral_nonneg fun y => abs_nonneg _
  have hmarkov : ∀ ε : ℝ, ε * (volume.restrict Q).real {y | ε ≤ |ub y|} ≤ M := fun ε =>
    hM_def ▸ mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
      hub_int.integrableOn.abs ε
  have hmeasle : ∀ c : ℝ, MeasurableSet {y | ub y ≤ c} := fun c =>
    measurableSet_le hub_meas measurable_const
  have hmeasge : ∀ c : ℝ, MeasurableSet {y | c ≤ ub y} := fun c =>
    measurableSet_le measurable_const hub_meas
  have hlow : ∀ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} → -(2 * M) ≤ k := by
    intro k hk
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (volume.restrict Q).real {y | ub y ≤ k} ≤
        (volume.restrict Q).real {y | -(k:ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y (hy : ub y ≤ k) => by
        show -(k:ℝ) ≤ |ub y|; linarith only [hy, neg_abs_le (ub y)])
    have h3 := mul_le_mul_of_nonneg_left (hk.trans h1)
      (by linarith only [hlt, hM0] : (0:ℝ) ≤ -(k:ℝ))
    linarith only [hmarkov (-(k:ℝ)), h3, hlt]
  have hex : ∃ k : ℤ, 1/2 ≤ (volume.restrict Q).real {y | ub y ≤ k} := by
    refine ⟨⌊2 * M⌋ + 1, ?_⟩
    have hk₀ : 2 * M < ((⌊2 * M⌋ + 1 : ℤ) : ℝ) := by
      rw [Int.cast_add, Int.cast_one]; exact Int.lt_floor_add_one _
    have h2 : (volume.restrict Q).real {y | ub y ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} :=
      measureReal_mono (fun y hy => by
        rw [mem_compl_iff, mem_ofPred_eq, not_le] at hy
        exact hy.le.trans (le_abs_self _))
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    by_contra h4
    rw [not_le] at h4
    have h5 := mul_le_mul_of_nonneg_left (show 1/2 ≤ (volume.restrict Q).real
      {y | ((⌊2 * M⌋ + 1 : ℤ) : ℝ) ≤ |ub y|} by linarith only [h2, h3, h4])
      (by linarith only [hk₀, hM0] : (0:ℝ) ≤ ((⌊2 * M⌋ + 1 : ℤ) : ℝ))
    linarith only [h5, hmarkov ((⌊2 * M⌋ + 1 : ℤ) : ℝ), hk₀]
  obtain ⟨β, hβP, hβmin⟩ := Int.exists_least_of_bdd ⟨⌊-(2 * M)⌋, fun k hk =>
    Int.cast_le.1 ((Int.floor_le _).trans (hlow k hk))⟩ hex
  have hβge : 1/2 ≤ (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
    have hβ1 : ¬ (1/2 ≤ (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}) := fun h => by
      have := hβmin (β - 1) h; omega
    rw [not_le] at hβ1
    have h3 := measureReal_add_measureReal_compl (μ := volume.restrict Q)
      (hmeasle ((β - 1 : ℤ) : ℝ))
    rw [probReal_univ] at h3
    have h4 : (volume.restrict Q).real {y | ub y ≤ ((β - 1 : ℤ) : ℝ)}ᶜ ≤
        (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} := by
      rw [measureReal_def, measureReal_def]
      refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
      filter_upwards [hub_ae] with y hy
      intro hy'
      obtain ⟨z, hz⟩ := hint y
      rw [mem_compl_iff, mem_ofPred_eq, not_le, hy, hz] at hy'
      show (β:ℝ) ≤ ub y
      rw [hy, hz]
      have : β - 1 < z := by exact_mod_cast hy'
      exact_mod_cast (show β ≤ z by omega)
    linarith only [h3, h4, hβ1]
  have hβabs : |(β:ℝ)| ≤ 2 * M := by
    rcases le_or_gt 0 (β:ℝ) with h0 | h0
    · rw [abs_of_nonneg h0]
      have h2 : (volume.restrict Q).real {y | (β:ℝ) ≤ ub y} ≤
          (volume.restrict Q).real {y | (β:ℝ) ≤ |ub y|} :=
        measureReal_mono fun y (hy : (β:ℝ) ≤ ub y) => hy.trans (le_abs_self _)
      linarith only [mul_le_mul_of_nonneg_left (hβge.trans h2) h0, hmarkov β]
    · rw [abs_of_neg h0]; linarith only [hlow β hβP]
  have hhalf : ∀ s : Set (Euclid (m + 1)), MeasurableSet s → 1/2 ≤ (volume.restrict Q).real s →
      (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) := by
    intro s hs h
    rw [← Measure.restrict_apply hs, ← ofReal_measureReal (measure_ne_top _ _)]
    calc (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      _ ≤ _ := ENNReal.ofReal_le_ofReal h
  have hhalf1 := hhalf _ (hmeasle β) hβP
  have hhalf2 := hhalf _ (hmeasge β) hβge
  -- `|ub x - β| ≤ 2 ∫_Q |ub y - ub x| dy`, since `β` is a median
  have hpt : ∀ x, ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
    intro x
    have hhalf' : ∀ a : ℝ≥0∞, a = 2 * (a * (1/2)) := fun a => by
      rw [one_div, mul_comm, mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
        mul_one]
    have hgm : Measurable fun y => ENNReal.ofReal |ub y - ub x| :=
      ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hub_meas.sub measurable_const))
    have key : ∀ s : Set (Euclid (m + 1)), (1/2 : ℝ≥0∞) ≤ volume (s ∩ Q) →
        (∀ y ∈ s, |ub x - β| ≤ |ub y - ub x|) →
        ENNReal.ofReal |ub x - β| ≤ 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := by
      intro s hs hle
      rw [hhalf' (ENNReal.ofReal |ub x - β|)]
      refine mul_le_mul_right ?_ 2
      calc ENNReal.ofReal |ub x - β| * (1/2) ≤ ENNReal.ofReal |ub x - β| * volume (s ∩ Q) :=
            mul_le_mul_right hs _
        _ = ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub x - β| := (setLIntegral_const _ _).symm
        _ ≤ ∫⁻ y in s ∩ Q, ENNReal.ofReal |ub y - ub x| :=
            setLIntegral_mono hgm fun y hy => ENNReal.ofReal_le_ofReal (hle y hy.1)
        _ ≤ ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono_set inter_subset_right
    rcases le_total (β:ℝ) (ub x) with hx | hx
    · refine key _ hhalf1 fun y (hy : ub y ≤ β) => ?_
      rw [abs_of_nonneg (sub_nonneg.2 hx), abs_sub_comm]
      exact (by linarith only [hy] : ub x - β ≤ ub x - ub y).trans (le_abs_self _)
    · refine key _ hhalf2 fun y (hy : (β:ℝ) ≤ ub y) => ?_
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hx)]
      exact (by linarith only [hy] : β - ub x ≤ ub y - ub x).trans (le_abs_self _)
  have hP1 : ∫ y in Q, |ub y - β| ≤ CP * V := by
    have hlin : ∫⁻ x in Q, ENNReal.ofReal |ub x - β| ≤
        2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R)) := by
      calc ∫⁻ x in Q, ENNReal.ofReal |ub x - β|
          ≤ ∫⁻ x in Q, 2 * ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| := lintegral_mono hpt
        _ = 2 * ∫⁻ x in Q, ∫⁻ y in Q, ENNReal.ofReal |ub y - ub x| :=
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top
        _ ≤ _ := mul_le_mul_right hJ 2
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun y => |ub y - (β:ℝ)|)
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (continuous_abs.measurable.comp (hub_meas.sub measurable_const)).aestronglyMeasurable]
    calc (∫⁻ x in Q, ENNReal.ofReal |ub x - β|).toReal
        ≤ (2 * (ENNReal.ofReal (2 * (R * V)) * volume (closedBall (0 : Euclid (m + 1)) R))).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne)) hlin
      _ = CP * V := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofNat, hCP_def]; ring
  have hβM : |(β:ℝ)| ≤ 2 * ∫ y in Q, |u y| := by
    have : ∫ y in Q, |u y| = M := by
      rw [hM_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hβabs
  clear hpt hhalf hhalf1 hhalf2 hlow hex hβmin hβge hβP hβabs hmarkov hJ hmeasle hmeasge hμprob
    hM0 hM_def hint
  /- Step 9: slabs `{y ∈ Q | a < y i < a + s}`.  Translating along `e i` compares the integrals
  of `|ub - β|` over two slabs of width `s` up to `2 s V`; averaging over the `N` slabs of width
  `1/N` bounds a boundary slab by `(∫_Q |ub - β| + 2 V) / N`. -/
  have hcoord : ∀ (i j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
      (x + t • EuclideanSpace.single i (1:ℝ)) j = if j = i then x j + t else x j := by
    intro i j x t
    by_cases hj : j = i <;> simp [hj]
  have hslabo : ∀ (i : Fin (m + 1)) (a s : ℝ),
      IsOpen {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := by
    intro i a s
    have hc : Continuous (fun y : Euclid (m + 1) => y i) := (EuclideanSpace.proj i).continuous
    exact hQo.inter ((isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const))
  have hslab : ∀ (i : Fin (m + 1)) (s a a' : ℝ), 0 < s → 0 ≤ a → a + s ≤ 1 → 0 ≤ a' →
      a' + s ≤ 1 →
      ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s}, |ub y - β| ≤
        (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s}, |ub y - β|) +
          2 * (s * V) := by
    intro i s a a' hs ha has ha' has'
    rcases eq_or_ne a a' with haa | haa
    · subst haa; linarith only [mul_nonneg hs.le hV0]
    obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = a' - a := ⟨_, rfl⟩
    have ht : t ≠ 0 := by rw [ht_def]; exact sub_ne_zero.2 (Ne.symm haa)
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (r : ℝ),
        (x + r • e) j = if j = i then x j + r else x j := by
      subst he_def; exact fun j x r => hcoord i j x r
    obtain ⟨S, hS_def⟩ : ∃ S : Set (Euclid (m + 1)),
        S = {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + s} := ⟨_, rfl⟩
    obtain ⟨S', hS'_def⟩ : ∃ S' : Set (Euclid (m + 1)),
        S' = {y : Euclid (m + 1) | y ∈ Q ∧ a' < y i ∧ y i < a' + s} := ⟨_, rfl⟩
    rw [← hS_def, ← hS'_def]
    have hSo : IsOpen S := hS_def ▸ hslabo i a s
    have hSm : MeasurableSet S := hSo.measurableSet
    have hS'm : MeasurableSet S' := (hS'_def ▸ hslabo i a' s).measurableSet
    have hSfin : volume S ≠ ⊤ := by
      refine ne_top_of_le_ne_top hQfin (measure_mono fun y hy => ?_)
      rw [hS_def] at hy; exact hy.1
    have hnh : ‖t • e‖ = |t| := by
      rw [he_def, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hmem : ∀ x, x ∈ S ↔ x + t • e ∈ S' := by
      intro x
      rw [hS_def, hS'_def]
      show (x ∈ Q ∧ a < x i ∧ x i < a + s) ↔
        (x + t • e ∈ Q ∧ a' < (x + t • e) i ∧ (x + t • e) i < a' + s)
      rw [hce, ite_eq_left rfl]
      constructor
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        rw [hce]; split_ifs with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha', has']
        · exact hxQ j
      · rintro ⟨hxQ, h1, h2⟩
        refine ⟨fun j => ?_, by linarith only [h1, ht_def], by linarith only [h2, ht_def]⟩
        have := hxQ j
        rw [hce] at this
        split_ifs at this with hj
        · subst hj; constructor <;> linarith only [h1, h2, ht_def, ha, has]
        · exact this
    have hgen := hGEN S (t • e) (s / |t|) hSo (by
        rintro x hx τ ⟨hτ0, hτ1⟩ j
        rw [hS_def] at hx
        obtain ⟨hxQ, h1, h2⟩ := hx
        rw [smul_smul, hce]
        split_ifs with hj
        · subst hj
          have e1 : τ * t = τ * a' - τ * a := by rw [ht_def]; ring
          have p1 := mul_nonneg (sub_nonneg.2 hτ1) ha
          have p2 := mul_nonneg hτ0 ha'
          have p3 := mul_nonneg (sub_nonneg.2 hτ1) (by linarith only [has] : (0:ℝ) ≤ 1 - a - s)
          have p4 := mul_nonneg hτ0 (by linarith only [has'] : (0:ℝ) ≤ 1 - a' - s)
          constructor <;> linarith only [h1, h2, e1, p1, p2, p3, p4]
        · exact hxQ j) (div_pos hs (abs_pos.2 ht)) (fun z => by
        have hsub : {τ : ℝ | z - τ • (t • e) ∈ S} ∩ Ioc (0:ℝ) 1 ⊆
            (fun τ => t * τ) ⁻¹' Ioo (z i - a - s) (z i - a) := by
          rintro τ ⟨hτ, -⟩
          rw [mem_ofPred_eq, hS_def] at hτ
          have h1 := hτ.2
          have hzi : (z - τ • (t • e)) i = z i - τ * t := by
            rw [smul_smul, sub_eq_add_neg, ← neg_smul, hce, ite_eq_left rfl, ← sub_eq_add_neg]
          rw [hzi] at h1
          rw [mem_preimage, mem_Ioo, mul_comm]
          exact ⟨by linarith only [h1.2], by linarith only [h1.1]⟩
        refine (measure_mono hsub).trans (le_of_eq ?_)
        rw [Real.volume_preimage_mul_left ht, Real.volume_Ioo, ← ENNReal.ofReal_mul (abs_nonneg _),
          abs_inv, show z i - a - (z i - a - s) = s by ring, div_eq_inv_mul])
    rw [hnh, div_mul_cancel₀ s (abs_ne_zero.2 ht)] at hgen
    have htrans : ∫ x in S, |ub (x + t • e) - β| = ∫ y in S', |ub y - β| := by
      rw [← integral_indicator hSm, ← integral_indicator hS'm,
        ← integral_add_right_eq_self (fun y => S'.indicator (fun y => |ub y - β|) y) (t • e)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hi1 : IntegrableOn (fun x => |ub (x + t • e) - β|) S :=
      ((hub_int.comp_add_right (t • e)).integrableOn.sub (integrableOn_const hSfin)).abs
    have hi2 : IntegrableOn (fun x => |ub (x + t • e) - ub x|) S :=
      ((hub_int.comp_add_right (t • e)).sub hub_int).abs.integrableOn
    calc ∫ y in S, |ub y - β|
        ≤ ∫ x in S, (|ub (x + t • e) - ub x| + |ub (x + t • e) - β|) := by
          refine setIntegral_mono_on ((hub_int.integrableOn.sub (integrableOn_const hSfin)).abs)
            (hi2.add hi1) hSm fun x _ => ?_
          have := abs_sub_le (ub x) (ub (x + t • e)) β
          rwa [abs_sub_comm (ub x) (ub (x + t • e))] at this
      _ = (∫ x in S, |ub (x + t • e) - ub x|) + ∫ x in S, |ub (x + t • e) - β| :=
          integral_add hi2 hi1
      _ ≤ (∫ y in S', |ub y - β|) + 2 * (s * V) := by rw [htrans]; linarith only [hgen]
  have hstrip : ∀ (i : Fin (m + 1)) (N : ℕ), 1 ≤ N → ∀ a : ℝ, 0 ≤ a → a + 1 / N ≤ 1 →
      (N:ℝ) * ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
        (∫ y in Q, |ub y - β|) + 2 * V := by
    intro i N hN a ha haN
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    have hk : ∀ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ a < y i ∧ y i < a + 1 / N}, |ub y - β| ≤
          (∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N},
            |ub y - β|) + 2 * (1 / N * V) := fun k hk =>
      hslab i (1 / N) a (k / N) (one_div_pos.2 hNpos) ha haN
        (div_nonneg (Nat.cast_nonneg k) hNpos.le)
        (by rw [← add_div, div_le_one hNpos]
            exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hk))
    have hsum := Finset.sum_le_sum hk
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] at hsum
    have hdisj : (↑(Finset.range N) : Set ℕ).Pairwise (Disjoint on fun k : ℕ =>
        {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}) := by
      intro k _ k' _ hkk'
      rw [Function.onFun, Set.disjoint_left]
      rintro y ⟨_, h1, h2⟩ ⟨_, h1', h2'⟩
      rcases lt_or_gt_of_ne hkk' with hlt | hlt
      · have : (k:ℝ) / N + 1 / N ≤ k' / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2, h1']
      · have : (k':ℝ) / N + 1 / N ≤ k / N := by
          rw [← add_div]
          exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt hlt) hNpos.le
        linarith only [this, h2', h1]
    have hint : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hunion : ∑ k ∈ Finset.range N,
        ∫ y in {y : Euclid (m + 1) | y ∈ Q ∧ (k / N : ℝ) < y i ∧ y i < k / N + 1 / N}, |ub y - β|
          ≤ ∫ y in Q, |ub y - β| := by
      rw [← integral_biUnion_finset (Finset.range N) (fun k _ => (hslabo i _ _).measurableSet)
        hdisj (fun k _ => hint.mono_set (fun y hy => hy.1))]
      refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => abs_nonneg _) ?_
      refine LE.le.eventuallySubset ?_
      intro y hy
      rw [mem_iUnion₂] at hy
      obtain ⟨k, _, hy⟩ := hy
      exact hy.1
    have : (N:ℝ) * (2 * (1 / N * V)) = 2 * V := by
      rw [mul_left_comm, ← mul_assoc (N:ℝ), mul_one_div_cancel hNpos.ne', one_mul]
    linarith only [hsum, hunion, this]
  clear hslab hGEN
  /- Step 10: difference quotients.  For `F` continuous with `|F| ≤ 1` and `s = 1/(2N)`,
  `∫_Q (ub - β) (F (· + s e) - F) / s` is the integral of `F` against the difference
  `w (· - s e) - w` of `w = (ub - β) 1_Q`, which is controlled by a translation estimate and the
  two boundary slabs. -/
  have hDQ : ∀ (i : Fin (m + 1)) (F : Euclid (m + 1) → ℝ), Continuous F → (∀ y, |F y| ≤ 1) →
      ∀ N : ℕ, 1 ≤ N →
      |∫ y in Q, (ub y - β) * ((2 * N : ℝ) *
        (F (y + (2 * N : ℝ)⁻¹ • EuclideanSpace.single i (1:ℝ)) - F y))|
        ≤ 10 * V + 4 * ∫ y in Q, |ub y - β| := by
    intro i F hFc hF1 N hN
    obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
    have hce : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)) (t : ℝ),
        (x + t • e) j = if j = i then x j + t else x j := by
      subst he_def; exact fun j x t => hcoord i j x t
    have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
    have hNpos : (0:ℝ) < N := Nat.cast_pos.2 hN
    obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = 2 * N := ⟨_, rfl⟩
    rw [← he_def, ← hc_def]
    have hc : 0 < c := hc_def ▸ mul_pos two_pos hNpos
    obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = c⁻¹ := ⟨_, rfl⟩
    rw [← hs_def]
    have hs : 0 < s := hs_def ▸ inv_pos.2 hc
    have hcs : c * s = 1 := hs_def ▸ mul_inv_cancel₀ hc.ne'
    have hsN : s < 1 / N := by
      rw [hs_def, hc_def, one_div]
      exact inv_strictAnti₀ hNpos (by linarith only [hNpos])
    have hcm : ∀ (j : Fin (m + 1)) (x : Euclid (m + 1)),
        (x - s • e) j = if j = i then x j - s else x j := by
      intro j x
      rw [sub_eq_add_neg, ← neg_smul, hce, ← sub_eq_add_neg]
    obtain ⟨wb, hwb_def⟩ : ∃ wb : Euclid (m + 1) → ℝ, wb = Q.indicator fun y => ub y - β :=
      ⟨_, rfl⟩
    have hwb_int : Integrable wb := hwb_def ▸
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).integrable_indicator hQm
    have hFb : ∀ y, ‖F y‖ ≤ 1 := hF1
    have hi1 : Integrable fun y => wb y * F (y + s • e) :=
      hwb_int.mul_bdd (hFc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => hFb _)
    have hi2 : Integrable fun y => wb y * F y :=
      hwb_int.mul_bdd hFc.aestronglyMeasurable (Filter.Eventually.of_forall hFb)
    have hi3 : Integrable fun x => wb (x - s • e) * F x :=
      (hwb_int.comp_sub_right (s • e)).mul_bdd hFc.aestronglyMeasurable
        (Filter.Eventually.of_forall hFb)
    have e1 : ∫ y in Q, (ub y - β) * (c * (F (y + s • e) - F y)) =
        c * ∫ x, (wb (x - s • e) - wb x) * F x := by
      rw [← integral_indicator hQm]
      have : ∀ y, Q.indicator (fun y => (ub y - β) * (c * (F (y + s • e) - F y))) y =
          c * (wb y * F (y + s • e) - wb y * F y) := fun y => by
        rw [indicator_mul_left, ← hwb_def]; ring
      simp only [this]
      rw [integral_const_mul, integral_sub hi1 hi2,
        ← integral_sub_right_eq_self (fun y => wb y * F (y + s • e)) (s • e)]
      simp only [sub_add_cancel]
      rw [← integral_sub hi3 hi2]
      simp only [sub_mul]
    -- the pointwise bound: interior differences and the two boundary slabs
    obtain ⟨A, hA_def⟩ : ∃ A : Set (Euclid (m + 1)), A = (fun x => x + s • e) ⁻¹' Q ∩ Q :=
      ⟨_, rfl⟩
    obtain ⟨S0, hS0_def⟩ : ∃ S0 : Set (Euclid (m + 1)),
        S0 = {y : Euclid (m + 1) | y ∈ Q ∧ (0:ℝ) < y i ∧ y i < 0 + 1 / N} := ⟨_, rfl⟩
    obtain ⟨S1, hS1_def⟩ : ∃ S1 : Set (Euclid (m + 1)),
        S1 = {y : Euclid (m + 1) | y ∈ Q ∧ (1 - 1 / N : ℝ) < y i ∧ y i < (1 - 1 / N) + 1 / N} :=
      ⟨_, rfl⟩
    have hAm : MeasurableSet A := hA_def ▸ (hQm.preimage (measurable_add_const _)).inter hQm
    have hS0m : MeasurableSet S0 := hS0_def ▸ (hslabo i _ _).measurableSet
    have hS1m : MeasurableSet S1 := hS1_def ▸ (hslabo i _ _).measurableSet
    have hpt : ∀ x, |wb (x - s • e) - wb x| ≤
        A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) +
          S0.indicator (fun y => |ub y - β|) x +
          S1.indicator (fun y => |ub y - β|) (x - s • e) := by
      intro x
      have n1 := indicator_nonneg (fun z _ => abs_nonneg (ub (z + s • e) - ub z)) (x - s • e)
        (s := A)
      have n2 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) x (s := S0)
      have n3 := indicator_nonneg (fun y _ => abs_nonneg (ub y - β)) (x - s • e) (s := S1)
      rw [hwb_def]
      by_cases hx : x ∈ Q <;> by_cases hxs : x - s • e ∈ Q
      · have hA : x - s • e ∈ A := by rw [hA_def]; exact ⟨by rwa [mem_preimage, sub_add_cancel], hxs⟩
        rw [indicator_of_mem hx, indicator_of_mem hxs, indicator_of_mem hA, sub_add_cancel,
          show ub (x - s • e) - (β:ℝ) - (ub x - β) = -(ub x - ub (x - s • e)) by ring, abs_neg]
        linarith only [n2, n3]
      · have hS0 : x ∈ S0 := by
          rw [hS0_def]
          refine ⟨hx, (hx i).1, ?_⟩
          by_contra hge
          rw [not_lt] at hge
          apply hxs
          intro j
          rw [hcm]
          split_ifs with hj
          · subst hj; constructor <;> linarith only [(hx j).2, hge, hsN, hs]
          · exact hx j
        rw [indicator_of_mem hx, indicator_of_notMem hxs, indicator_of_mem hS0, zero_sub, abs_neg]
        linarith only [n1, n3]
      · have hS1 : x - s • e ∈ S1 := by
          rw [hS1_def]
          refine ⟨hxs, ?_, ?_⟩
          · by_contra hle
            rw [not_lt, hcm, ite_eq_left rfl] at hle
            apply hx
            intro j
            have := hxs j
            rw [hcm] at this
            split_ifs at this with hj
            · subst hj; constructor <;> linarith only [this.1, hle, hsN, hs]
            · exact this
          · have := (hxs i).2; linarith only [this]
        rw [indicator_of_notMem hx, indicator_of_mem hxs, indicator_of_mem hS1, sub_zero]
        linarith only [n1, n2]
      · rw [indicator_of_notMem hx, indicator_of_notMem hxs, sub_zero, abs_zero]
        linarith only [n1, n2, n3]
    -- integrate the three terms
    have hg1 : Integrable fun z => |ub (z + s • e) - ub z| :=
      ((hub_int.comp_add_right _).sub hub_int).abs
    have hg2 : IntegrableOn (fun y => |ub y - β|) Q :=
      (hub_int.integrableOn.sub (integrableOn_const hQfin)).abs
    have hT1i : Integrable fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) :=
      (hg1.indicator hAm).comp_sub_right (s • e)
    have hT2i : Integrable (S0.indicator fun y => |ub y - β|) :=
      (hg2.mono_set (fun y hy => by rw [hS0_def] at hy; exact hy.1)).integrable_indicator hS0m
    have hT3i : Integrable fun x => S1.indicator (fun y => |ub y - β|) (x - s • e) :=
      ((hg2.mono_set (fun y hy => by rw [hS1_def] at hy; exact hy.1)).integrable_indicator
        hS1m).comp_sub_right (s • e)
    have hI1 : ∫ x, A.indicator (fun z => |ub (z + s • e) - ub z|) (x - s • e) ≤ 2 * (s * V) := by
      rw [integral_sub_right_eq_self (fun x => A.indicator (fun z => |ub (z + s • e) - ub z|) x)
        (s • e), integral_indicator hAm, hA_def]
      have := hTR (s • e)
      rwa [norm_smul, hne, mul_one, Real.norm_of_nonneg hs.le] at this
    have hI3 : ∫ x, S1.indicator (fun y => |ub y - β|) (x - s • e) = ∫ y in S1, |ub y - β| := by
      rw [integral_sub_right_eq_self (fun x => S1.indicator (fun y => |ub y - β|) x) (s • e),
        integral_indicator hS1m]
    have hb2 : (N:ℝ) * ∫ y in S0, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS0_def ▸
      hstrip i N hN 0 le_rfl (by rw [zero_add, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
    have hb3 : (N:ℝ) * ∫ y in S1, |ub y - β| ≤ (∫ y in Q, |ub y - β|) + 2 * V := hS1_def ▸
      hstrip i N hN (1 - 1 / N) (by rw [sub_nonneg, div_le_one hNpos]; exact Nat.one_le_cast.2 hN)
        (by rw [sub_add_cancel])
    have hmain : ∫ x, |wb (x - s • e) - wb x| ≤
        2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β| := by
      refine (integral_mono ((hwb_int.comp_sub_right _).sub hwb_int).abs
        ((hT1i.add hT2i).add hT3i) hpt).trans ?_
      rw [integral_add' (hT1i.add hT2i) hT3i, integral_add' hT1i hT2i, integral_indicator hS0m, hI3]
      linarith only [hI1]
    have hbound : |∫ x, (wb (x - s • e) - wb x) * F x| ≤ ∫ x, |wb (x - s • e) - wb x| := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hwb_int.comp_sub_right _).sub hwb_int).abs
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hF1 x)
    rw [e1, abs_mul, abs_of_pos hc]
    have h5 := mul_le_mul_of_nonneg_left (hbound.trans hmain) hc.le
    have h6 : c * (2 * (s * V) + (∫ y in S0, |ub y - β|) + ∫ y in S1, |ub y - β|) =
        2 * (c * s) * V + 2 * ((N:ℝ) * ∫ y in S0, |ub y - β|) +
          2 * ((N:ℝ) * ∫ y in S1, |ub y - β|) := by
      rw [hc_def]; ring
    rw [h6, hcs] at h5
    linarith only [h5, hb2, hb3]
  clear hstrip hslabo hcoord hTR
  /- Step 11: the boundary estimate (3): write `div G = ∑ᵢ ∂ᵢ Gᵢ` and pass to the limit in the
  difference quotients by dominated convergence. -/
  obtain ⟨I, hI_def⟩ : ∃ I : ℝ, I = ∫ y in Q, |ub y - β| := ⟨_, rfl⟩
  rw [← hI_def] at hDQ hP1
  have hwi : IntegrableOn (fun y => ub y - β) Q :=
    hub_int.integrableOn.sub (integrableOn_const hQfin)
  have h3 : ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) →
      |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤
        (m + 1) * (10 * V + 4 * I) := by
    intro G hG hG1
    have hG1' : ContDiff ℝ 1 G := hG.of_le (by exact_mod_cast le_top)
    have hdG : Continuous (fderiv ℝ G) := hG1'.continuous_fderiv one_ne_zero
    have hGd : ∀ y, HasFDerivAt G (fderiv ℝ G y) y := fun y =>
      (hG1'.differentiable one_ne_zero y).hasFDerivAt
    have hterm : ∀ i : Fin (m + 1),
        |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| ≤
          10 * V + 4 * I := by
      intro i
      obtain ⟨e, he_def⟩ : ∃ e : Euclid (m + 1), e = EuclideanSpace.single i (1:ℝ) := ⟨_, rfl⟩
      rw [← he_def]
      have hne : ‖e‖ = 1 := by rw [he_def, PiLp.norm_single, norm_one]
      obtain ⟨Fi, hFi_def⟩ : ∃ Fi : Euclid (m + 1) → ℝ, Fi = fun y => G y i := ⟨_, rfl⟩
      have hFid : ∀ y, HasFDerivAt Fi ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y)) y :=
        fun y => by
          rw [hFi_def]; exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y (hGd y)
      have hFic : Continuous Fi := by
        rw [hFi_def]; exact (EuclideanSpace.proj i).continuous.comp hG.continuous
      have hFi1 : ∀ y, |Fi y| ≤ 1 := fun y => by
        rw [hFi_def, ← Real.norm_eq_abs]; exact (PiLp.norm_apply_le (G y) i).trans (hG1 y)
      have hdFc : Continuous fun y => (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ G y) :=
        continuous_const.clm_comp hdG
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) (R + 1)).exists_bound_of_continuousOn
        hdFc.continuousOn
      have hC' : ∀ y ∈ closedBall (0 : Euclid (m + 1)) (R + 1), ‖fderiv ℝ Fi y‖ ≤ C :=
        fun y hy => by rw [(hFid y).fderiv]; exact hC y hy
      have hmvt : ∀ y ∈ Q, ∀ t : ℝ, 0 < t → |Fi (y + t • e) - Fi y| ≤ C * t ∨ 1 < t := by
        intro y hy t ht0
        rcases le_or_gt t 1 with ht1 | ht1
        · left
          have hny := hnormQ y hy
          have hyK : y ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]; linarith only [hny]
          have hyK' : y + t • e ∈ closedBall (0 : Euclid (m + 1)) (R + 1) := by
            rw [mem_closedBall, dist_zero_right]
            refine (norm_add_le _ _).trans ?_
            rw [norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le]
            linarith only [hny, ht1]
          have := (convex_closedBall (0 : Euclid (m + 1)) (R + 1)).norm_image_sub_le_of_norm_fderiv_le
            (fun z _ => (hFid z).differentiableAt) hC' hyK hyK'
          rwa [add_sub_cancel_left, norm_smul, hne, mul_one, Real.norm_of_nonneg ht0.le,
            Real.norm_eq_abs] at this
        · right; exact ht1
      obtain ⟨c, hc_def⟩ : ∃ c : ℕ → ℝ, c = fun N => 2 * ((N + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
      have hcpos : ∀ N, 0 < c N := fun N => by
        rw [hc_def]; exact mul_pos two_pos (Nat.cast_pos.2 N.succ_pos)
      have hc1 : ∀ N, ¬ 1 < (c N)⁻¹ := fun N => by
        rw [not_lt, inv_le_one₀ (hcpos N), hc_def]
        have : (1:ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.one_le_cast.2 N.succ_pos
        linarith only [this]
      have hctend : Tendsto (fun N => ‖c N‖) atTop atTop := by
        have : (fun N => ‖c N‖) = fun N : ℕ => 2 * ((N + 1 : ℕ) : ℝ) := by
          funext N; rw [Real.norm_of_nonneg (hcpos N).le, hc_def]
        rw [this]
        exact Tendsto.const_mul_atTop two_pos
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      have hlim : Tendsto
          (fun N => ∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y)))
          atTop (𝓝 (∫ y in Q, (ub y - β) * (fderiv ℝ G y e) i)) := by
        refine tendsto_integral_of_dominated_convergence (fun y => |ub y - β| * C) (fun N => ?_)
          (hwi.abs.mul_const C) (fun N => ?_) ?_
        · exact (hub_meas.sub measurable_const).aestronglyMeasurable.mul
            (continuous_const.mul ((hFic.comp (continuous_id.add continuous_const)).sub
              hFic)).aestronglyMeasurable
        · refine (ae_restrict_iff' hQm).2 (Filter.Eventually.of_forall fun y hy => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (hcpos N)]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have := (hmvt y hy (c N)⁻¹ (inv_pos.2 (hcpos N))).resolve_right (hc1 N)
          calc c N * |Fi (y + (c N)⁻¹ • e) - Fi y| ≤ c N * (C * (c N)⁻¹) :=
                mul_le_mul_of_nonneg_left this (hcpos N).le
            _ = C := by rw [mul_comm C, ← mul_assoc, mul_inv_cancel₀ (hcpos N).ne', one_mul]
        · refine Filter.Eventually.of_forall fun y => ?_
          have := (hFid y).lim e hctend
          simp only [smul_eq_mul] at this
          exact this.const_mul _
      have hbd : ∀ N, |∫ y in Q, (ub y - β) * (c N * (Fi (y + (c N)⁻¹ • e) - Fi y))| ≤
          10 * V + 4 * I := fun N => by
        have := hDQ i Fi hFic hFi1 (N + 1) (by omega)
        rwa [← he_def, show (2 * ((N + 1 : ℕ) : ℝ)) = c N by rw [hc_def]] at this
      exact le_of_tendsto' ((continuous_abs.tendsto _).comp hlim) hbd
    have htr : ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∑ i, (fderiv ℝ G y (EuclideanSpace.single i 1)) i := by
      intro y
      rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis]
      simp [Matrix.trace, LinearMap.toMatrix_apply]
    have hint_i : ∀ i : Fin (m + 1), Integrable
        (fun y => (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i) (volume.restrict Q) := by
      intro i
      have hcont : Continuous fun y => (fderiv ℝ G y (EuclideanSpace.single i 1)) i :=
        (EuclideanSpace.proj i).continuous.comp (hdG.clm_apply continuous_const)
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euclid (m + 1)) R).exists_bound_of_continuousOn
        hcont.continuousOn
      refine hwi.mul_bdd hcont.aestronglyMeasurable ((ae_restrict_iff' hQm).2
        (Filter.Eventually.of_forall fun y hy => hC y ?_))
      rw [mem_closedBall, dist_zero_right]; exact hnormQ y hy
    calc |∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)|
        = |∑ i, ∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| := by
          rw [← integral_finsetSum _ fun i _ => hint_i i]
          congr 2; funext y
          rw [htr y, Finset.mul_sum]
      _ ≤ ∑ i, |∫ y in Q, (ub y - β) * (fderiv ℝ G y (EuclideanSpace.single i 1)) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (m + 1), (10 * V + 4 * I) := Finset.sum_le_sum fun i _ => hterm i
      _ = (m + 1) * (10 * V + 4 * I) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
            Nat.cast_one]
  /- Conclusion. -/
  have hm0 : (0:ℝ) ≤ m + 1 := add_nonneg (Nat.cast_nonneg m) zero_le_one
  have hcV : CP * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V := by
    refine mul_le_mul_of_nonneg_right ?_ hV0
    have := mul_nonneg hm0 (by linarith only [hCP] : (0:ℝ) ≤ 10 + 4 * CP)
    linarith only [this]
  refine ⟨β, ?_, hβM, ?_⟩
  · have : ∫ y in Q, |u y - β| = I := by
      rw [hI_def]; exact integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]; exact hP1.trans hcV
  · intro G hG hG1
    have : ∫ y in Q, (u y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) =
        ∫ y in Q, (ub y - β) * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
      integral_congr_ae (by filter_upwards [hub_ae] with y hy; rw [hy])
    rw [this]
    refine (h3 G hG hG1).trans ?_
    have h1 : (m + 1) * (10 * V + 4 * I) ≤ (m + 1) * (10 * V + 4 * (CP * V)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hP1]) hm0
    have h2 : (m + 1) * (10 * V + 4 * (CP * V)) = (m + 1) * (10 + 4 * CP) * V := by ring
    have h4 : (m + 1) * (10 + 4 * CP) * V ≤ (CP + (m + 1) * (10 + 4 * CP) + 1) * V :=
      mul_le_mul_of_nonneg_right (by linarith only [hCP]) hV0
    linarith only [h1, h2, h4]
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

/-- **Face replacement** (Simon Ch. 6, proof of the deformation theorem 5.1, displays (26)–(37);
the BV facts on the faces come from the sibling `dtc_bc_tc_cl_dfm_cube_bv_median`).  Let `Q₀` be
integer multiplicity with `n = m + 1`, `spt Q₀ ⊆ K ∩ Lₙ`, `M(Q₀) ≤ Λ` and `M(∂Q₀) < ∞`.
* Over the open unit `n`-faces `F̆ = Φ_p((0,1)ⁿ)`, `Q₀ = Σ_F ũ_F [[F̆]]` with integer densities
  `ũ_F` and `Σ_F ∫|ũ_F| ≤ M(Q₀)`: `Hⁿ(L_{n-1}) = 0`, `μ_{Q₀}` vanishes off `spt Q₀`, and on a face
  the orientation is `±e_F` (approximate tangent planes of subsets of a coordinate plane).
* Testing `∂Q₀` with forms built from vector fields on a face bounds the variation of `ũ_F` by
  `V_F = M_{N_F}(∂Q₀)` for pairwise disjoint open `N_F ⊇ F̆`, so `Σ_F V_F ≤ M(∂Q₀)`.
* Integer medians `β_F` (the sibling, constant `c_B`) give `Pc = Σ_F β_F [[F]]`, an element of the
  finite family of integer chains on faces meeting `cthickening √P K` with `Σ|β_F| ≤ 2Λ`, and
  `M(Q₀ − Pc), M(∂(Q₀ − Pc)) ≤ c_B M(∂Q₀)`; hence `M(∂Pc) ≤ (1 + c_B) M(∂Q₀)`.
* `Pc` and `∂Pc` (cubical Stokes) are integer multiplicity, `M(Pc) ≤ Σ|β_F| ≤ 2M(Q₀)`, and
  `M(Pc) ≥ 1` unless every `β_F = 0`, the open faces being disjoint with `Hⁿ(F̆) = 1`; a face carrying `Pc` meets `spt Q₀`, a face carrying `Q₀ − Pc` meets `spt ∂Q₀`,
  and faces have diameter `≤ √P`.  Take `c = max(2, 1 + c_B)`. -/
theorem Submission.dtc_bc_tc_cl_dfm_face_replacement : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P m : ℕ), ∃ c : NNReal, 1 ≤ c ∧ ∀ (K : Set (Euclid P)) (Λ : NNReal), IsCompact K → ∃ 𝒬₀ : Set (GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), 𝒬₀.Finite ∧ ∀ Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → Q₀.mass ≤ Λ → Q₀.boundary.mass < ∞ → ∃ Pc ∈ 𝒬₀, IsIntegerMultiplicity Pc ∧ IsIntegerMultiplicity Pc.boundary ∧ (Pc = 0 ∨ 1 ≤ Pc.mass) ∧ Pc.mass ≤ c * Q₀.mass ∧ Pc.boundary.mass ≤ c * Q₀.boundary.mass ∧ (Q₀ - Pc).mass ≤ c * Q₀.boundary.mass ∧ Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support ∧ (Q₀ - Pc).support ∪ Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
  intro hVO hMR hIMC
  /- **Simon 6.5.1** (proof, (31): `Lⁿ` of the interior of a unit face is `1`): the open unit cube
  `{y : 0 < yᵢ < 1}` of `ℝᵏ` has volume `1`.  It is the preimage of the box `∏ᵢ (0, 1)` under the
  volume-preserving `ofLp : ℝᵏ → (Fin k → ℝ)`, and the box has volume `∏ᵢ (1 - 0) = 1` (the empty
  product if `k = 0`). -/
  have cmcdtfrfg_cube_volume : ∀ k : ℕ, (volume : Measure (Euclid k)) {y | ∀ i, 0 < y i ∧ y i < 1} = 1 := by
    clear hVO hMR hIMC
    intro k
    -- the box `∏ᵢ (0, 1)` in `Fin k → ℝ`
    have hB : MeasurableSet (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioo
    -- the cube is `ofLp⁻¹` of the box
    have hpre : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
      ext y
      simp only [mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, mem_Ioo, forall_const]
    rw [hpre, (PiLp.volume_preserving_ofLp (Fin k)).measure_preimage hB.nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp only [sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]
  /- **Coordinates of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face of the
  cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P`, `b ∈ ℤᴾ`, `y ∈ ℝᵏ` and
  `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}`: coordinates are additive and linear and `(eᵢ)ₗ = [l = i]`, so
  `Φ(y)ₗ = bₗ + Σⱼ [ι(j) = l] yⱼ`.  At `l = ι(m)` injectivity of `ι` leaves only the summand `j = m`,
  giving `b_{ι(m)} + yₘ`; for `l` outside the range of `ι` every summand vanishes, giving `bₗ`. -/
  have cmcdtfrfg_face_coord : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ) (y : Euclid k), Function.Injective ι → (∀ m, (HAdd.hAdd (WithLp.toLp 2 (fun i => (b i : ℝ))) (∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))) (ι m) = (b (ι m) : ℝ) + y m) ∧ (∀ l, (∀ m, ι m ≠ l) → (HAdd.hAdd (WithLp.toLp 2 (fun i => (b i : ℝ))) (∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))) l = (b l : ℝ)) := by
    clear cmcdtfrfg_cube_volume hVO hMR hIMC
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
  /- **Isometry and diameter of the lattice face map** (Simon Ch. 6 §5, deformation theorem: a face
  of the cube lattice parametrised over `ℝᵏ`).  For injective `ι : Fin k → Fin P` and `b ∈ ℤᴾ`, the
  map `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` is an isometry `ℝᵏ → ℝᴾ`: by `face_coord` the coordinate gap of
  `Φ(y)` and `Φ(y')` is `yₘ - y'ₘ` at `ι(m)` and `0` off the range of `ι`, so reindexing the sum of
  squared gaps along `ι` gives `|Φ(y) - Φ(y')| = |y - y'|`.  On the closed unit cube every squared gap
  is at most `1`, so `|y - y'| ≤ √k ≤ √P`, as `k ≤ P` by injectivity of `ι`. -/
  have cmcdtfrfg_face_isometry_diam : ∀ (P k : ℕ) (ι : Fin k → Fin P) (b : Fin P → ℤ), Function.Injective ι → (∀ y y' : Euclid k, dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (b i : ℝ))) (∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (b i : ℝ))) (∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) ≤ Real.sqrt P) := by
    clear cmcdtfrfg_cube_volume hVO hMR hIMC
    intro P k ι b hι
    -- (a), steps 1-5: `|Φ(y) - Φ(y')|² = Σₗ |Φ(y)ₗ - Φ(y')ₗ|² = Σₘ |yₘ - y'ₘ|² = |y - y'|²`
    have hiso : ∀ y y' : Euclid k,
        dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (b i : ℝ))) (∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))
          (WithLp.toLp 2 (fun i => (b i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (ι j) (1 : ℝ)) =
        dist y y' := by
      intro y y'
      -- step 2: the coordinates of `Φ(y)` and `Φ(y')`
      have hcy := cmcdtfrfg_face_coord P k ι b y hι
      have hy := hcy.1
      have hyc := hcy.2
      have hcy' := cmcdtfrfg_face_coord P k ι b y' hι
      have hy' := hcy'.1
      have hy'c := hcy'.2
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
    clear cmcdtfrfg_face_coord
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
      _ = k := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      _ ≤ P := by exact_mod_cast hkP
  /- **Separation of distinct unit lattice faces** (Simon Ch. 6, §5, chapter-06.txt lines 1841–1918:
  the faces `F ∈ 𝓛ₖ` and their interiors `F̆`).  For `p = (ι, b) ≠ q = (ι', b')` with `ι, ι'`
  strictly increasing, `x = Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` with `y ∈ (0,1)ᵏ` and `z = Φ_q(y')` with
  `y' ∈ [0,1]ᵏ`, either `1 ≤ |x − z|` or `min(yⱼ, 1 − yⱼ) ≤ |x − z|` for some `j`.  If some
  `z_{ι(j)}` lies outside `(b_{ι(j)}, b_{ι(j)} + 1) ∋ x_{ι(j)} = b_{ι(j)} + yⱼ`, the coordinate `ι(j)`
  gives the second alternative.  Otherwise no `z_{ι(j)}` is an integer, so `range ι ⊆ range ι'` and
  `ι = ι'` (both enumerate the same `k`-element set increasingly), `b = b'` on `range ι`, and a
  coordinate `l ∉ range ι` with `b_l ≠ b'_l` gives `|x_l − z_l| = |b_l − b'_l| ≥ 1`.  The coordinates
  of `x` and `z` are `cmcdtfrfg_face_coord`. -/
  have cmcdtfrfg_face_separation : ∀ (P k : ℕ) (p q : (Fin k → Fin P) × (Fin P → ℤ)), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfrfg_face_isometry_diam hVO hMR hIMC
    intro P k p q hp hq hpq y y' hy hy'
    -- step 1: the coordinates of `x = Φ_p(y)` and `z = Φ_q(y')`
    have hcx := cmcdtfrfg_face_coord P k p.1 p.2 y hp.injective
    have hx₁ := hcx.1
    have hx₂ := hcx.2
    have hcz := cmcdtfrfg_face_coord P k q.1 q.2 y' hq.injective
    clear cmcdtfrfg_face_coord
    have hz₁ := hcz.1
    have hz₂ := hcz.2
    generalize HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) =
      x at hx₁ hx₂ ⊢
    generalize WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ) =
      z at hz₁ hz₂ ⊢
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
  clear cmcdtfrfg_face_coord
  /- **Geometry of unit lattice faces** (Simon Ch. 6, §5, Lemma 2.1 and the faces `F ∈ 𝓛ₖ` of the
  deformation theorem, for faces of any dimension `k`).  `(0)` `vol((0,1)ᵏ) = 1`.  For `p = (ι, b)`
  with `ι` strictly increasing and `b ∈ ℤᴾ`, the face map `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` is `(a)` an
  isometry `ℝᵏ → ℝᴾ` with `(b)` `dist(Φ_p y, Φ_p y') ≤ √P` on `[0,1]ᵏ`; `(c)` if `q ≠ p`,
  `y ∈ (0,1)ᵏ` and `y' ∈ [0,1]ᵏ`, then `dist(Φ_p y, Φ_q y') ≥ 1` or `≥ min(yⱼ, 1 − yⱼ)` for some
  `j`.  A strictly increasing `ι` is injective, so `(a)`, `(b)` are `cmcdtfrfg_face_isometry_diam`;
  `(0)` is `cmcdtfrfg_cube_volume` and `(c)` is `cmcdtfrfg_face_separation`. -/
  have cmcdtfr_face_geometry : ∀ (P k : ℕ), (volume : Measure (Euclid k)) {y | ∀ i, 0 < y i ∧ y i < 1} = 1 ∧ ∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → (∀ y y' : Euclid k, dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = dist y y') ∧ (∀ y y' : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (p.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ≤ Real.sqrt P) ∧ (p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) := by
    clear hVO hMR hIMC
    intro P k
    refine ⟨cmcdtfrfg_cube_volume k, fun p q hp hq => ?_⟩
    -- `(a)`, `(b)` for the face map of `p`, whose strictly increasing `p.1` is injective
    clear cmcdtfrfg_cube_volume
    have hfi := cmcdtfrfg_face_isometry_diam P k p.1 p.2 hp.injective
    clear cmcdtfrfg_face_isometry_diam
    have hiso := hfi.1
    have hdiam := hfi.2
    -- `(c)`: the open face of `p` against the closed face of `q ≠ p`
    exact ⟨hiso, hdiam, cmcdtfrfg_face_separation P k p q hp hq⟩
  clear cmcdtfrfg_face_isometry_diam cmcdtfrfg_face_separation
  /- **Cut-off lift of a vector field on a face** (Simon Ch. 6, proof of 5.1, displays (27)–(28):
  the test forms giving `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|`, as in 2.35).  Let
  `Φ_p(y) = b + Σ_j y_j e_{ι(j)}` be the chart of the face and `π(x) = (x_{ι(j)} − b_{ι(j)})_j` its
  affine left inverse.  Put `G = χ · (g ∘ π)`, where the smooth cut-off `χ : ℝᴾ → [0, 1]` equals
  `1` near the compact set `K = Φ_p(spt g) ⊆ N` and is supported in `N`.  Then `G(Φ_p y) = g(y)`
  for `y ∈ (0,1)ⁿ`: `π ∘ Φ_p = id`, and `χ = 1` where `g ≠ 0`. -/
  have cmcdtfrbv_cutoff_field : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ G : Euclid P → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ HasCompactSupport G ∧ tsupport G ⊆ N ∧ (∀ x, ‖G x‖ ≤ 1) ∧ ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → G (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) = g y := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry hVO hMR hIMC
    intro P m p N g hmono hN hΦN hg hgc hgQ hg1
    -- Step 1: the face chart `Φ_p` and its affine left inverse `π(x) = (x_{ι(j)} - b_{ι(j)})ⱼ`
    let Φ : Euclid (m + 1) → Euclid P := fun y =>
      HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
    let π : Euclid P → Euclid (m + 1) := fun x =>
      WithLp.toLp 2 (fun j => x (p.1 j) - (p.2 (p.1 j) : ℝ))
    -- `π (Φ_p y) = y`, since `ι` is injective
    have hπΦ : ∀ y, π (Φ y) = y := by
      intro y
      ext j
      simp only [PiLp.add_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, PiLp.ofLp_single, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, hmono.injective.eq_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, add_sub_cancel_left, π, Φ]
    have hΦc : Continuous Φ := by fun_prop
    have hπc : ContDiff ℝ (⊤ : ℕ∞) π :=
      contDiff_euclidean.2 fun j => show ContDiff ℝ (⊤ : ℕ∞) fun x : Euclid P =>
        x (p.1 j) - (p.2 (p.1 j) : ℝ) from (EuclideanSpace.proj (𝕜 := ℝ) (p.1 j)).contDiff.sub contDiff_const
    -- Steps 2–3: `K = Φ_p(spt g)` is a compact subset of `N`, and `cthickening δ K ⊆ N`
    have hKc : IsCompact (Φ '' tsupport g) := hgc.isCompact.image hΦc
    have hKN : Φ '' tsupport g ⊆ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hΦN y (hgQ hy)
    obtain ⟨δ, hδ, hδN⟩ := hKc.exists_cthickening_subset_open hN hKN
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
    · -- Step 6: `G(Φ_p y) = χ(Φ_p y) g(y) = g(y)`, as `χ = 1` on `Φ_p(spt g)`
      intro y _
      show χ (Φ y) • g (π (Φ y)) = g y
      rw [hπΦ]
      by_cases hgy : g y = 0
      · rw [hgy, smul_zero]
      · rw [(hχ1 _).1 (self_subset_cthickening _ (mem_image_of_mem Φ (subset_tsupport g hgy))),
          one_smul]
  /- **Kronecker property of the determinant covectors** (Simon 6.1, chapter-06.txt lines 22–47:
  `dxʲ(v) = vⱼ`, `dx^{i₁} ∧ ⋯ ∧ dx^{iₙ}(v₁, …, vₙ) = det(dx^{iₖ}(vⱼ))` (1.1), and
  `ω_α = ω(e_{i₁}, …, e_{iₙ})` for the basis `{dx^α : α ∈ I_{n,P}}` (1.2)): if `I`, `J` are strictly
  increasing and `θ(v) = det (v_j(I k))_{k,j}`, then `θ(e_{J 1}, …, e_{J n}) = δ_{IJ}`.  The matrix
  of `θ(e_J)` has entries `[I k = J j]`.  It is the identity if `I = J`.  Otherwise some `I k₀` is
  not a value of `J` (else `range I ⊆ range J`, both have `n` elements, so the ranges agree and the
  strictly increasing maps agree), and row `k₀` vanishes. -/
  have cmr_cc_det_covector_basis_kronecker : ∀ (P n : ℕ) (I J : Fin n → Fin P) (θ : Covector (Euclid P) n), StrictMono I → StrictMono J → (∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k))) → θ (fun j => EuclideanSpace.basisFun (Fin P) ℝ (J j)) = if I = J then 1 else 0 := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field hVO hMR hIMC
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
  /- **The coordinate covector `dx^I`** (Simon Ch. 6, §1): for `I : Fin n → Fin P` some
  `n`-covector `θ` on `ℝᴾ` has `θ(v₁, …, vₙ) = det (vⱼ(I k))_{k,j}`.  With the coordinate
  projection `p_I x = (x(I k))_k`, `θ⁰ = det ∘ p_I` is alternating, `det Mᵀ = det M` gives the
  formula, and `θ⁰` is continuous as the determinant and the coordinates are. -/
  have cmr_cc_det_covector_exists : ∀ (P n : ℕ) (I : Fin n → Fin P), ∃ θ : Covector (Euclid P) n, ∀ v : Fin n → Euclid P, θ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field cmr_cc_det_covector_basis_kronecker hVO hMR hIMC
    intro P n I
    -- Step 1: the coordinate projection `p_I x = (x(I k))_k` is linear
    let p : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      { toFun := fun x k => x (I k)
        map_add' := fun x y => by
          funext k
          simp only [PiLp.add_apply, Pi.add_apply]
        map_smul' := fun c x => by
          funext k
          simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]}
    -- Step 2: `θ⁰ = Θ ∘ p_I`, with `Θ` the determinant as an alternating map in the rows
    let θ₀ : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap p
    -- Step 3: `θ⁰(v) = det (vⱼ(I k))_{j,k} = det (vⱼ(I k))_{k,j}` by `det Mᵀ = det M`
    have hθ₀ : ∀ v : Fin n → Euclid P, θ₀ v = Matrix.det (Matrix.of fun k j => v j (I k)) := by
      intro v
      rw [← Matrix.det_transpose]
      rfl
    -- Step 4: `θ⁰` is continuous, the determinant and the coordinates being continuous
    exact ⟨{ θ₀ with
      cont := (Continuous.matrix_det (A := fun v : Fin n → Euclid P => Matrix.of fun k j => v j (I k))
        (continuous_matrix fun k j => (PiLp.continuous_apply 2 _ (I k)).comp (continuous_apply j))).congr
          fun v => (hθ₀ v).symm }, hθ₀⟩
  /- **Face covectors of a coordinate `(m+1)`-plane** (Simon Ch. 6, (1.1), (1.2), (1.15)): for
  strictly increasing `ι : Fin (m + 1) → Fin P` put `J_j = ι ∘ j.succAbove` (the `j`-th index
  dropped) and `ε_j = (-1)^j dx^{J_j}`, with `dx^{J_j}` from `Submission.cmr_cc_det_covector_exists`.
  The `J_j` are strictly increasing and pairwise distinct (for `j ≠ j'`, `ι j` is a value of `J_{j'}`
  but not of `J_j`), so by `Submission.cmr_cc_det_covector_basis_kronecker` the coefficient
  `α_c(e_I)` of `α_c = Σ_j c_j ε_j` is `(-1)^j c_j` if `I = J_j` and `0` for every other strictly
  increasing `I`.  This gives `α_c(e_{J_j}) = (-1)^j c_j` and `|α_c| = √(Σ_j c_j²)`. -/
  have cmcdtfrbv_face_covectors : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P), StrictMono ι → ∃ ε : Fin (m + 1) → Covector (Euclid P) m, (∀ c : Fin (m + 1) → ℝ, covectorEuclideanNorm (∑ j, c j • ε j) = Real.sqrt (∑ j, c j ^ 2)) ∧ ∀ (c : Fin (m + 1) → ℝ) (j : Fin (m + 1)), (∑ j', c j' • ε j') (fun k => EuclideanSpace.single (ι (j.succAbove k)) (1 : ℝ)) = (-1) ^ (j : ℕ) * c j := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field hVO hMR hIMC
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
    choose θ hθ using fun j => cmr_cc_det_covector_exists P m (J j)
    clear cmr_cc_det_covector_exists
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
        cmr_cc_det_covector_basis_kronecker P m (J j') I (θ j') (hJmono j') hI (hθ j')]
      split_ifs
      · rw [smul_eq_mul, smul_eq_mul, mul_one, mul_comm]
      · rw [smul_zero, smul_zero]
    -- Step 6: `α_c(e_{J_j}) = (-1)^j c_j`, since only `j' = j` has `J_{j'} = J_j`
    clear cmr_cc_det_covector_basis_kronecker
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
  /- Along the affine coordinate cube `Φ y = a + Σⱼ yⱼ e_{ι j}`, the exterior derivative of a smooth
  `m`-form `γ` on `E = (e_{ι j})ⱼ` is the divergence `Σᵢ ∂ᵢFᵢ` of the coefficient fields
  `Fᵢ(y) = (-1)ⁱ γ(Φ y)(E ∘ succAbove i)`, and each `Fᵢ` is smooth.  `Φ = a + L` with `L` continuous
  linear and `L eᵢ = e_{ι i}`; expand `dγ(Φ y)(E)` by `exteriorDerivative_apply`
  (`removeNth i E = E ∘ succAbove i`) and apply the chain rule to `Fᵢ`. -/
  have cmcdtfrcb_pullback_divergence : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (a : Euclid P) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ (⊤ : ℕ∞) γ → (∀ i : Fin (m + 1), ContDiff ℝ (⊤ : ℕ∞) (fun y : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))) ∧ ∀ y : Euclid (m + 1), exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), fderiv ℝ (fun z : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrbv_face_covectors hVO hMR hIMC
    intro P m ι a γ hγ
    have hr : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by decide
    -- `Φ y = a + L y` with `L v = Σⱼ vⱼ e_{ι j}` continuous linear, and `L eᵢ = e_{ι i}`
    let L : Euclid (m + 1) →L[ℝ] Euclid P :=
      ∑ j, (EuclideanSpace.proj j).smulRight (EuclideanSpace.single (ι j) (1 : ℝ))
    have hL : ∀ v : Euclid (m + 1),
        a + L v = a + ∑ j, v j • EuclideanSpace.single (ι j) (1 : ℝ) := by
      intro v
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, L]
    have hΦ : ∀ y : Euclid (m + 1), HasFDerivAt
        (fun z : Euclid (m + 1) => a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ)) L y := by
      intro y
      simpa only [hL] using (L.hasFDerivAt (x := y)).const_add a
    have hΦc : ContDiff ℝ (⊤ : ℕ∞)
        fun z : Euclid (m + 1) => a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ) := by
      simpa only [hL] using (contDiff_const (c := a)).add L.contDiff
    have hLe : ∀ i : Fin (m + 1),
        L (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single (ι i) (1 : ℝ) := by
      intro i
      simp only [sum_apply, ContinuousLinearMap.smulRight_apply, PiLp.proj_apply, PiLp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, L]
    refine ⟨fun i => ?_, fun y => ?_⟩
    · -- `Fᵢ = (-1)ⁱ · ev_{E ∘ succAbove i} ∘ γ ∘ Φ`, evaluation being continuous linear
      exact contDiff_const.mul ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
        fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)).contDiff.comp
          (hγ.comp hΦc))
    · -- `dγ(Φ y)(E) = Σᵢ (-1)ⁱ D[γ(·)(removeNth i E)](Φ y)(e_{ι i})`; match the terms with the
      -- chain rule `DFᵢ(y) eᵢ = (-1)ⁱ D[γ(·)(E ∘ succAbove i)](Φ y)(L eᵢ)`
      rw [exteriorDerivative_apply ((hγ.differentiable hr) _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hF : HasFDerivAt
          (fun z : Euclid (m + 1) =>
            (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, z j • EuclideanSpace.single (ι j) (1 : ℝ))
              (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))
          ((-1 : ℝ) ^ (i : ℕ) • (fderiv ℝ (fun x' => γ x'
            (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))
              (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))).comp L) y :=
        ((((hγ.differentiable hr) _).continuousAlternatingMap_apply_const _).hasFDerivAt.comp y
          (hΦ y)).const_mul _
      -- `removeNth i E = E ∘ succAbove i` and `E i = e_{ι i}`
      show (-1 : ℤ) ^ (i : ℕ) • fderiv ℝ (fun x' => γ x'
        (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)))
          (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (EuclideanSpace.single (ι i) (1 : ℝ)) = _
      rw [hF.fderiv]
      simp only [Int.reduceNeg, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_apply, ContinuousLinearMap.comp_apply, hLe, smul_eq_mul]
  /- The open unit cube `(0, 1)ᵏ ⊆ ℝᵏ` is open: it is `ofLp⁻¹` of the open box `∏ᵢ (0, 1)`. -/
  have dfmf_cube_open : ∀ k : ℕ, IsOpen {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrbv_face_covectors cmcdtfrcb_pullback_divergence hVO hMR hIMC
    intro k
    have hpre : {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} =
        WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin k => Ioo (0 : ℝ) 1) := by
      ext y
      simp only [mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, mem_Ioo, forall_const]
    rw [hpre]
    exact (isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo).preimage (PiLp.continuous_ofLp 2 _)
  /- **The trace of a derivative is the sum of the partial derivatives of the components**:
  `trace DG(y) = Σᵢ ∂ᵢGᵢ(y)` (in the standard orthonormal basis of `ℝᵏ`). -/
  have dfmf_trace_fderiv : ∀ (k : ℕ) (G : Euclid k → Euclid k) (y : Euclid k), DifferentiableAt ℝ G y → LinearMap.trace ℝ (Euclid k) (fderiv ℝ G y) = ∑ i, fderiv ℝ (fun z => G z i) y (EuclideanSpace.single i (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmcdtfrbv_cutoff_field cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrbv_face_covectors cmcdtfrcb_pullback_divergence dfmf_cube_open hVO hMR hIMC
    intro k G y hG
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin k) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(((hasFDerivWithinAt_piLp 2).1 hG.hasFDerivAt.hasFDerivWithinAt i).hasFDerivAt
        Filter.univ_mem).fderiv, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left,
      map_one, one_mul]
    rfl
  /- **The divergence test form of a face** (Simon Ch. 6, proof of the deformation theorem 5.1).
  With the face covectors `εⱼ` of `ι = p.1` (`cmcdtfrbv_face_covectors`) and the cutoff field `G`
  with `G ∘ Φ_p = g` on `Q₁` (`cmcdtfrbv_cutoff_field`), `γ(x) = Σⱼ Gⱼ(x) εⱼ` is a test form on
  `ℝᴾ` with `tsupport γ ⊆ tsupport G ⊆ N` and `|γ(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`.  As
  `γ(x)(E⁽ⁱ⁾) = (-1)ⁱ Gᵢ(x)`, `dγ(Φ_p y)(E) = Σᵢ ∂ᵢ(Gᵢ ∘ Φ_p)(y) = Σᵢ ∂ᵢgᵢ(y) = trace Dg(y)` for
  `y ∈ Q₁`. -/
  have cmcdtfrbv_divergence_test_form : ∀ (P m : ℕ) (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (N : Set (Euclid P)) (g : Euclid (m + 1) → Euclid (m + 1)), StrictMono p.1 → IsOpen N → (∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ N) → ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∃ γ : TestFormOn (univ : Set (Euclid P)) m, tsupport γ.1 ⊆ N ∧ (∀ x, covectorEuclideanNorm (γ.1 x) ≤ 1) ∧ ∀ y : Euclid (m + 1), (∀ i, 0 < y i ∧ y i < 1) → exteriorDerivative γ.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) = LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists hVO hMR hIMC
    intro P m p N g hι hN hΦN hg hgc hgs hg1
    -- Step 1: the face covectors `εⱼ` of `ι = p.1`
    obtain ⟨ε, hεn, hεf⟩ := cmcdtfrbv_face_covectors P m p.1 hι
    -- Step 2: the cutoff field `G = χ · (g ∘ π)`
    clear cmcdtfrbv_face_covectors
    obtain ⟨G, hG, hGc, hGN, hG1, hGd⟩ :=
      cmcdtfrbv_cutoff_field P m p N g hι hN hΦN hg hgc hgs hg1
    -- Step 3: `ω(x) = Σⱼ Gⱼ(x) εⱼ`
    clear cmcdtfrbv_cutoff_field
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
      simp only [hω, hx, PiLp.zero_apply, zero_smul, Finset.sum_const_zero]
    have hωT : IsTestForm ω ∧ tsupport ω ⊆ (univ : Set (Euclid P)) :=
      ⟨⟨hωs, hGc.mono hωG⟩, subset_univ _⟩
    refine ⟨⟨ω, hωT⟩, (closure_mono hωG).trans hGN, fun x => ?_, fun y hy => ?_⟩
    · -- Step 6: `|ω(x)| = √(Σⱼ Gⱼ(x)²) = ‖G x‖ ≤ 1`
      calc covectorEuclideanNorm (ω x) = Real.sqrt (∑ j, G x j ^ 2) := hεn fun j => G x j
        _ = ‖G x‖ := by rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]
        _ ≤ 1 := hG1 x
    · -- Step 7: `dω(Φ y)(E) = Σᵢ ∂ᵢFᵢ(y)` (`cmcdtfrcb_pullback_divergence`) with
      -- `Fᵢ(z) = (−1)ⁱ ω(Φ z)(E⁽ⁱ⁾) = Gᵢ(Φ z)` (face covectors), which is `gᵢ(z)` on the open cube
      -- `Q₁ ∋ y` (cutoff field); and `Σᵢ ∂ᵢgᵢ(y) = trace Dg(y)` (`dfmf_trace_fderiv`)
      have hpd := cmcdtfrcb_pullback_divergence P m p.1
        (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) ω hωs
      have hd := hpd.2
      show exteriorDerivative ω _ _ = _
      rw [hd y, dfmf_trace_fderiv _ g y ((hg.differentiable (by decide)) y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h : (fun z : Euclid (m + 1) => (-1 : ℝ) ^ (i : ℕ) *
          ω (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, z j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
            (fun j => EuclideanSpace.single ((p.1 ∘ Fin.succAbove i) j) (1 : ℝ))) =ᶠ[𝓝 y]
          fun z => g z i := by
        filter_upwards [(dfmf_cube_open (m + 1)).mem_nhds hy] with z hz
        rw [show ω _ (fun j => EuclideanSpace.single ((p.1 ∘ Fin.succAbove i) j) (1 : ℝ)) =
            (-1 : ℝ) ^ (i : ℕ) * G _ i from hεf (fun j => G _ j) i, ← mul_assoc, ← mul_pow,
          neg_one_mul, neg_neg, one_pow, one_mul, hGd z hz]
      rw [h.fderiv_eq]
  clear cmcdtfrbv_cutoff_field cmcdtfrbv_face_covectors
  /- **Disjoint neighbourhoods of the open unit faces** (Simon Ch. 6, §5, proof of 5.1: the open
  faces `F̆` get pairwise disjoint neighbourhoods `N_F`).  For `p = (ι, b)` with `ι` strictly
  increasing, `π_p(x) = (x_{ι(j)} − b_{ι(j)})ⱼ` is a continuous left inverse of the face map
  `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`; put `d_p(x) = |x − Φ_p(π_p x)|`.  `N_p` is the set of `x` with
  `π_p(x) ∈ (0,1)ᵏ`, `2 d_p(x) < 1` and `2 d_p(x) < min(π_p(x)ⱼ, 1 − π_p(x)ⱼ)` for all `j`: a finite
  intersection of strict inequalities between continuous functions, hence open, and it contains
  `Φ_p((0,1)ᵏ)`, where `d_p = 0`.  The separation hypothesis gives `2 d_p(x) < |Φ_p(π_p x) − Φ_q(y')|`
  for `x ∈ N_p`, `q ≠ p` and `y' ∈ [0,1]ᵏ`.  For `x = Φ_q(y')` this reads `2 d_p(x) < d_p(x)`, so
  `Φ_q([0,1]ᵏ)` misses `N_p`; for `x ∈ N_p ∩ N_q` the bounds for `(p, q)` and `(q, p)` contradict the
  triangle inequality. -/
  have cmcdtfrbv_face_neighbourhoods : ∀ (P k : ℕ), (∀ p q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → StrictMono q.1 → p ≠ q → ∀ y y' : Euclid k, (∀ j, 0 < y j ∧ y j < 1) → (∀ i, 0 ≤ y' i ∧ y' i ≤ 1) → 1 ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ)) ∨ ∃ j, min (y j) (1 - y j) ≤ dist (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) + ∑ j, y' j • EuclideanSpace.single (q.1 j) (1 : ℝ))) → ∃ N : (Fin k → Fin P) × (Fin P → ℤ) → Set (Euclid P), ∀ p : (Fin k → Fin P) × (Fin P → ℤ), StrictMono p.1 → IsOpen (N p) ∧ (∀ y : Euclid k, (∀ i, 0 < y i ∧ y i < 1) → (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ N p) ∧ ∀ q : (Fin k → Fin P) × (Fin P → ℤ), StrictMono q.1 → q ≠ p → (∀ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (HAdd.hAdd (WithLp.toLp 2 (fun i => (q.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ))) ∉ N p) ∧ Disjoint (N p) (N q) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrbv_divergence_test_form hVO hMR hIMC
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
  /- Local mass is superadditive over finitely many pairwise disjoint regions (Simon 6.2.5):
  `∑_{i ∈ s} M_{N_i}(S) ≤ M_{⋃_{i ∈ s} N_i}(S)`.  If `ω_A`, `ω_B` are admissible for disjoint
  regions `A`, `B`, then at each point at most one of them is nonzero, so `ω_A + ω_B` is admissible
  for `A ∪ B` and `S(ω_A + ω_B) = S(ω_A) + S(ω_B)`; replacing a form with negative value by `0`
  gives `M_A(S) + M_B(S) ≤ M_{A ∪ B}(S)`, and induction on `s` finishes. -/
  have cmcdtfrbv_massOn_disjoint_sum_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ι : Type) (s : Finset ι) (N : ι → Set (Euclid P)), (↑s : Set ι).PairwiseDisjoint N → ∑ i ∈ s, S.massOn (N i) ≤ S.massOn (⋃ i ∈ s, N i) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrbv_divergence_test_form cmcdtfrbv_face_neighbourhoods hVO hMR hIMC
    classical
    intro P n U S ι s N hN
    -- the zero form is admissible for every region
    have hzero : ∀ A : Set (Euclid P), (0 : TestFormOn U n) ∈ massAdmissibleOn U n A :=
      fun A => ⟨by simp only [ZeroMemClass.coe_zero, tsupport_zero, empty_subset], fun x => by simp only [ZeroMemClass.coe_zero, Pi.zero_apply, covectorEuclideanNorm_zero, zero_le_one]⟩
    -- forms admissible for disjoint regions glue to a form admissible for the union
    have hglue : ∀ A B : Set (Euclid P), Disjoint A B → ∀ ωA ∈ massAdmissibleOn U n A,
        ∀ ωB ∈ massAdmissibleOn U n B, ωA + ωB ∈ massAdmissibleOn U n (A ∪ B) := by
      intro A B hAB ωA hA ωB hB
      refine ⟨?_, fun x => ?_⟩
      · exact (tsupport_add _ _).trans (union_subset_union hA.1 hB.1)
      · show covectorEuclideanNorm (ωA.1 x +
          ωB.1 x) ≤ 1
        by_cases hx : x ∈ tsupport ωA.1
        · have hxB : x ∉ tsupport ωB.1 := fun h =>
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
    | empty => simp only [Finset.sum_empty, Finset.notMem_empty, iUnion_of_empty, iUnion_empty, zero_le]
    | insert a s ha ih =>
      rw [Finset.coe_insert, Set.pairwiseDisjoint_insert_of_notMem (Finset.mem_coe.not.2 ha)] at hN
      have hdisj : Disjoint (N a) (⋃ i ∈ s, N i) := by
        simp only [Set.disjoint_iUnion_right]
        exact fun i hi => hN.2 i hi
      rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
      calc S.massOn (N a) + ∑ i ∈ s, S.massOn (N i)
          ≤ S.massOn (N a) + S.massOn (⋃ i ∈ s, N i) := add_le_add le_rfl (ih hN.1)
        _ ≤ S.massOn (N a ∪ ⋃ i ∈ s, N i) := htwo _ _ hdisj
  /- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30)): let
  `D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy` for every test form `ω`,
  where `p = (ι_p, b_p)`, `Q₁ = (0, 1)ⁿ`, `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and each `w_p` is
  integrable on `Q₁`.  Then every `x ∈ spt D` is `Φ_p(y)` for some `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0` and
  some `y ∈ [0, 1]ⁿ`.  Otherwise `x` lies outside the compact union `Z` of the closed faces
  `Φ_p([0, 1]ⁿ)` with `∫_{Q₁} |w_p| ≠ 0`, so a ball `B_r(x)` misses `Z`.  If `spt ω ⊆ B_r(x)`, every
  summand vanishes: `w_p = 0` a.e. on `Q₁` when `∫_{Q₁} |w_p| = 0`, and `ω = 0` on `Φ_p(Q₁) ⊆ Z`
  otherwise.  So `D` vanishes on `B_r(x)` and `x ∈ zeroRegion D`, contradicting `x ∈ spt D`. -/
  have cmcdtfrfic_support_faces : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, IntegrableOn (w p) {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid (m + 1)))) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, w p y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∀ x ∈ D.support, ∃ p ∈ s, (∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) = x := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrbv_divergence_test_form cmcdtfrbv_face_neighbourhoods cmcdtfrbv_massOn_disjoint_sum_le hVO hMR hIMC
    classical
    intro P m s w D hw hD x hx
    by_contra hne
    -- `Z`: the union of the closed faces `Φ_p([0, 1]ⁿ)` over the `p ∈ s` with `∫_{Q₁} |w_p| ≠ 0`
    let Z : Set (Euclid P) :=
      ⋃ p ∈ s.filter fun p => (∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0,
        (fun z : Fin (m + 1) → ℝ =>
          HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, z j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ''
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
    by_cases hpw : (∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) = 0
    · -- `∫_{Q₁} |w_p| = 0`: `w_p = 0` a.e. on `Q₁`, so the integrand vanishes a.e.
      have h0 := (integral_eq_zero_iff_of_nonneg (fun y => abs_nonneg (w p y)) (hw p hp).abs).mp hpw
      refine integral_eq_zero_of_ae (h0.mono fun y hy => ?_)
      have hy' : w p y = 0 := abs_eq_zero.mp hy
      show w p y * _ = 0
      rw [hy', zero_mul]
    · -- `∫_{Q₁} |w_p| ≠ 0`: `Φ_p(Q₁) ⊆ Z` misses `B_r(x) ⊇ spt ω`, so the integrand vanishes on `Q₁`
      refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
      have hyZ : HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ Z :=
        Set.mem_biUnion (Finset.mem_filter.mpr ⟨hp, hpw⟩)
          ⟨WithLp.ofLp y, fun i _ => ⟨(hy i).1.le, (hy i).2.le⟩, rfl⟩
      have hω0 : ω.1
          (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hrZ (hω h) hyZ
      rw [hω0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]
  /- The open unit cube `(0, 1)ᵏ ⊆ ℝᵏ` is Borel, being open (`dfmf_cube_open`). -/
  have dfmf_cube_meas : ∀ k : ℕ, MeasurableSet {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_trace_fderiv cmcdtfrbv_divergence_test_form cmcdtfrbv_face_neighbourhoods cmcdtfrbv_massOn_disjoint_sum_le cmcdtfrfic_support_faces hVO hMR hIMC
    intro k
    exact (dfmf_cube_open k).measurableSet
  /- `spt ∂A ⊆ spt A` (Simon 6.2.11, 6.2.3): a region on which `A` vanishes is one on which
  `∂A` vanishes, as `spt dγ ⊆ spt γ`. -/
  have dfmf_support_boundary_subset : ∀ (P m : ℕ) (A : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), A.boundary.support ⊆ A.support := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrbv_divergence_test_form cmcdtfrbv_face_neighbourhoods cmcdtfrbv_massOn_disjoint_sum_le cmcdtfrfic_support_faces dfmf_cube_meas hVO hMR hIMC
    intro P m A x hx
    refine ⟨hx.1, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := hxA
    exact ⟨W, ⟨hWo, hWc, hWU, fun γ hγ => hWv (exteriorDerivativeTestOn univ m γ)
      ((tsupport_exteriorDerivative_subset _).trans hγ)⟩, hxW⟩
  /- **Boundary variation on the open faces of a lattice chain** (Simon Ch. 6, proof of 5.1,
  displays (27)–(28) and (32), chapter-06.txt lines 1849–1893: `M(∂Q ⌞ F̆) = ∫_{F̆} |Dθ_F|` by the
  reasoning of 2.35).  Let `Q₀(ω) = Σ_{p ∈ s} ∫_{Q₁} u_p(y) ω(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) dy`
  with `M(∂Q₀) < ∞`.  The separation `(c)` of `cmcdtfr_face_geometry` and
  `cmcdtfrbv_face_neighbourhoods` give open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing every
  other closed face; put `V_p = M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`.  Then `Σ_p V_p ≤ M(∂Q₀)` by
  `cmcdtfrbv_massOn_disjoint_sum_le`.  `(i)` The test form `γ` of `cmcdtfrbv_divergence_test_form`
  is admissible for `N_p` with `dγ(Φ_p y)(e_{ι(0)}, …, e_{ι(m)}) = div g(y)` on `Q₁`, and `dγ`
  vanishes on the other faces, so `∫ u_p div g = Q₀(dγ) = ∂Q₀(γ) ≤ V_p`.  `(ii)` If `V_p ≠ 0`, some
  admissible `γ` for `N_p` has `∂Q₀(γ) > 0`; by (VO) `tsupport γ ⊆ N_p` meets `spt ∂Q₀`, which lies
  on the closed faces (`spt ∂Q₀ ⊆ spt Q₀`, `cmcdtfrfic_support_faces`), and of these only the
  face of `p` meets `N_p`. -/
  have cmcdtfr_boundary_variation : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (u p) {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid (m + 1)))) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, u p y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → Q₀.boundary.mass < ∞ → ∃ V : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, 0 ≤ V p) ∧ ENNReal.ofReal (∑ p ∈ s, V p) ≤ Q₀.boundary.mass ∧ (∀ p ∈ s, ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g → tsupport g ⊆ {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} → (∀ y, ‖g y‖ ≤ 1) → ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) ≤ V p) ∧ (∀ p ∈ s, V p ≠ 0 → ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ Q₀.boundary.support) := by
    clear cmcdtfrfg_cube_volume cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv hMR hIMC
    intro P m s u Q₀ hs hu hQ₀ hmass
    -- step 1: open `N_p ⊇ Φ_p(Q₁)`, pairwise disjoint and missing the other closed faces, from the
    -- separation `(c)` of `face_geometry`
    obtain ⟨N, hN⟩ := cmcdtfrbv_face_neighbourhoods P (m + 1)
      fun p q hp hq => ((cmcdtfr_face_geometry P (m + 1)).2 p q hp hq).2.2
    -- step 3: `M_{N_p}(∂Q₀) ≤ M(∂Q₀) < ∞`, so `V_p := M_{N_p}(∂Q₀)` is a real number
    clear cmcdtfr_face_geometry cmcdtfrbv_face_neighbourhoods
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
            cmcdtfrbv_massOn_disjoint_sum_le P m univ Q₀.boundary _ s N hdisj
        _ ≤ Q₀.boundary.mass := Q₀.boundary.massOn_mono (subset_univ _)
    · intro p hp g hg hgc hgs hgb
      have hNp := hN p (hs p hp)
      have hNo := hNp.1
      have hNF := hNp.2.1
      have hNq := hNp.2.2
      -- step 5: the test form `γ` for `g` is admissible for `N_p`, so `∂Q₀(γ) ≤ V_p`
      obtain ⟨γ, hγs, hγn, hγd⟩ := cmcdtfrbv_divergence_test_form P m p (N p) g
        (hs p hp) hNo hNF hg hgc hgs hgb
      have hle : Q₀.boundary γ ≤ (Q₀.boundary.massOn (N p)).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal (hfin p)).1 (Q₀.boundary.le_massOn ⟨hγs, hγn⟩)
      -- the open unit cube `Q₁` is measurable
      have hQ₁ : MeasurableSet {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1} :=
        dfmf_cube_meas (m + 1)
      -- steps 6–8: `∂Q₀(γ) = Q₀(dγ) = Σ_q ∫_{Q₁} u_q(y) dγ(Φ_q y)(E_q) dy = ∫_{Q₁} u_p div g`
      have hval : Q₀.boundary γ = ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1},
          u p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g y) := by
        rw [GeometricCurrentOn.boundary_apply, hQ₀, Finset.sum_eq_single_of_mem p hp]
        · -- step 6: `dγ(Φ_p y)(E_p) = trace Dg(y)` for `y ∈ Q₁`
          exact setIntegral_congr_fun hQ₁ fun y hy => congrArg (u p y * ·) (hγd y hy)
        · -- step 7: for `q ≠ p`, `Φ_q(Q₁)` misses `N_p ⊇ tsupport γ ⊇ tsupport dγ`
          intro q hq hqp
          refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
          have hz : exteriorDerivative γ.1
              (WithLp.toLp 2 (fun i => (q.2 i : ℝ)) +
                ∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)) = 0 :=
            image_eq_zero_of_notMem_tsupport fun h => (hNq q (hs q hq) hqp).1 y
              (fun i => ⟨(hy i).1.le, (hy i).2.le⟩) (hγs (tsupport_exteriorDerivative_subset _ h))
          change u q y * exteriorDerivative γ.1 _ _ = 0
          rw [hz]
          simp only [ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_zero]
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
      obtain ⟨q, hq, -, y, hy, rfl⟩ := cmcdtfrfic_support_faces P m s u Q₀ hu hQ₀ x
        (dfmf_support_boundary_subset P m Q₀ hx)
      by_cases hqp : q = p
      · subst hqp
        exact ⟨y, hy, hx⟩
      · exact absurd (hγ.1 hxγ) (((hN p (hs p hp)).2.2 q (hs q hq) hqp).1 y hy)
  clear cmcdtfrbv_divergence_test_form cmcdtfrbv_face_neighbourhoods cmcdtfrbv_massOn_disjoint_sum_le
  /- **Fundamental theorem of calculus in one coordinate on the open unit cube.**  For smooth `G` on
  `ℝ^{k+1}` and a coordinate `i`, `∂ᵢG = DG(·)eᵢ` is integrable on `Q^{k+1} = (0, 1)^{k+1}` and
  `∫_{Q^{k+1}} ∂ᵢG = ∫_{Q^k} G(·, xᵢ = 1) − ∫_{Q^k} G(·, xᵢ = 0)`.  The measure-preserving `toLp`
  carries the open boxes of `Fin d → ℝ` onto the cubes, `(t, z) ↦ insertNth i t z` splits off the
  `i`-th coordinate, Fubini puts the `t`-integral inside, and along each line
  `t ↦ insertNth i t z = insertNth i 0 z + t eᵢ` the fundamental theorem of calculus applies. -/
  have cmcdtfrcb_cube_partial_ftc : ∀ (k : ℕ) (i : Fin (k + 1)) (G : Euclid (k + 1) → ℝ), ContDiff ℝ (⊤ : ℕ∞) G → IntegrableOn (fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) {y | ∀ j, 0 < y j ∧ y j < 1} (volume : Measure (Euclid (k + 1))) ∧ ∫ y : Euclid (k + 1) in {y | ∀ j, 0 < y j ∧ y j < 1}, fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = (∫ y : Euclid k in {y | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) (WithLp.ofLp y)))) - ∫ y : Euclid k in {y | ∀ j, 0 < y j ∧ y j < 1}, G (WithLp.toLp 2 (Fin.insertNth i (0 : ℝ) (WithLp.ofLp y))) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation hVO hMR hIMC
    intro k i G hG
    have hGd : Differentiable ℝ G := hG.differentiable (by decide)
    have hg : Continuous fun y => fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) :=
      (hG.continuous_fderiv (by decide)).clm_apply continuous_const
    -- the open box of `Fin d → ℝ` lies in the compact box `Icc 0 1`
    have hBsub : ∀ d : ℕ, {x : Fin d → ℝ | ∀ j, 0 < x j ∧ x j < 1} ⊆ Icc 0 1 :=
      fun d x hx => ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩
    -- `toLp` transports the open box of `Fin d → ℝ` onto the open cube of `Euclid d`
    have htr : ∀ (d : ℕ) (f : Euclid d → ℝ), ∫ y : Euclid d in {y | ∀ j, 0 < y j ∧ y j < 1}, f y
        = ∫ x : Fin d → ℝ in {x | ∀ j, 0 < x j ∧ x j < 1}, f (WithLp.toLp 2 x) := fun d f =>
      ((PiLp.volume_preserving_toLp (Fin d)).setIntegral_preimage_emb
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding f _).symm
    -- the faces `xᵢ = c` in the coordinates of `Fin k → ℝ`
    have hface : ∀ c : ℝ, IntegrableOn (fun z : Fin k → ℝ => G (WithLp.toLp 2 (Fin.insertNth i c z)))
        {z | ∀ j, 0 < z j ∧ z j < 1} (volume : Measure (Fin k → ℝ)) := fun c =>
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
      · simp only [Fin.insertNth_apply_same, PiLp.add_apply, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one, zero_add]
      · simp only [Fin.insertNth_apply_succAbove, PiLp.add_apply, PiLp.smul_apply, ne_eq, Fin.succAbove_ne, not_false_eq_true, PiLp.single_eq_of_ne, smul_eq_mul, mul_zero, add_zero]
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
    calc ∫ x : Fin (k + 1) → ℝ in {x | ∀ j, 0 < x j ∧ x j < 1},
          fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ))
        = ∫ p in Ioo (0 : ℝ) 1 ×ˢ {z : Fin k → ℝ | ∀ j, 0 < z j ∧ z j < 1},
            fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i p.1 p.2))
              (EuclideanSpace.single i (1 : ℝ)) := by
          rw [← hpre]
          exact (hmp.setIntegral_preimage_emb hemb
            (fun x => fderiv ℝ G (WithLp.toLp 2 x) (EuclideanSpace.single i (1 : ℝ))) _).symm
      _ = ∫ z : Fin k → ℝ in {z | ∀ j, 0 < z j ∧ z j < 1}, ∫ t in Ioo (0 : ℝ) 1,
            fderiv ℝ G (WithLp.toLp 2 (Fin.insertNth i t z)) (EuclideanSpace.single i (1 : ℝ)) := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
          exact integral_prod_symm _ hint
      _ = ∫ z : Fin k → ℝ in {z | ∀ j, 0 < z j ∧ z j < 1},
            (G (WithLp.toLp 2 (Fin.insertNth i 1 z)) - G (WithLp.toLp 2 (Fin.insertNth i 0 z))) :=
          integral_congr_ae (Eventually.of_forall hftc)
      _ = _ := integral_sub (hface 1) (hface 0)
  /- **Stokes' formula for one oriented lattice unit cube** (the cubes of the lattice of Simon
  Ch. 6, §5).  For `Φ(y) = b + Σⱼ yⱼ e_{ι(j)}` on the open unit cube `Q^{m+1}` (`b ∈ ℤᴾ`, `ι`
  arbitrary) and a smooth `m`-form `γ`,
  `∫_{Q^{m+1}} dγ(Φ y)(e_{ι(0)}, …, e_{ι(m)}) = Σᵢ (−1)ⁱ (∫_{Q^m} γ(Φ¹ᵢ)(E'ᵢ) − ∫_{Q^m} γ(Φ⁰ᵢ)(E'ᵢ))`,
  where `Φᶜᵢ(y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}` and `E'ᵢ = (e_{ι(succAbove i l)})ₗ`.
  By `cmcdtfrcb_pullback_divergence` the integrand is `Σᵢ ∂ᵢFᵢ` with the smooth functions
  `Fᵢ(y) = (−1)ⁱ γ(Φ y)(E'ᵢ)`; `cmcdtfrcb_cube_partial_ftc` integrates each `∂ᵢFᵢ` to the
  difference of the integrals of `Fᵢ` over the faces `yᵢ = 1` and `yᵢ = 0`, and
  `Φ(insertNth i c y') = Φᶜᵢ(y')`. -/
  have cmcdtfrcb_cube_stokes : ∀ (P m : ℕ) (ι : Fin (m + 1) → Fin P) (b : Fin P → ℤ) (γ : DifferentialForm (Euclid P) m), ContDiff ℝ (⊤ : ℕ∞) γ → ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, exteriorDerivative γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) = ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * ((∫ y : Euclid m in {y | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) - ∫ y : Euclid m in {y | ∀ j, 0 < y j ∧ y j < 1}, γ (WithLp.toLp 2 (fun k => (b k : ℝ)) + ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ))) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_trace_fderiv cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation hVO hMR hIMC
    intro P m ι b γ hγ
    -- `dγ(Φ y)(E) = Σᵢ ∂ᵢFᵢ(y)`, with every `Fᵢ` smooth
    have hpd := cmcdtfrcb_pullback_divergence P m ι
      (WithLp.toLp 2 (fun k => (b k : ℝ))) γ hγ
    clear cmcdtfrcb_pullback_divergence
    have hC1 := hpd.1
    have hpt := hpd.2
    simp only [hpt]
    -- each `∂ᵢFᵢ` is integrable on the cube, so the finite sum leaves the integral
    rw [integral_finsetSum _ fun i _ => (cmcdtfrcb_cube_partial_ftc m i _ (hC1 i)).1]
    refine Finset.sum_congr rfl fun i _ => ?_
    -- `∫ ∂ᵢFᵢ` is the difference of the face integrals of `Fᵢ` at `yᵢ = 1` and `yᵢ = 0`
    rw [(cmcdtfrcb_cube_partial_ftc m i _ (hC1 i)).2]
    -- `Φ(insertNth i c y') = b + c e_{ι(i)} + Σₗ y'ₗ e_{ι(succAbove i l)}`
    clear cmcdtfrcb_cube_partial_ftc
    have hface : ∀ (c : ℝ) (y : Euclid m),
        WithLp.toLp 2 (fun k => (b k : ℝ)) +
            ∑ j, (WithLp.toLp 2 (Fin.insertNth i c (WithLp.ofLp y)) : Euclid (m + 1)) j •
              EuclideanSpace.single (ι j) (1 : ℝ) =
          WithLp.toLp 2 (fun k => (b k : ℝ)) + c • EuclideanSpace.single (ι i) (1 : ℝ) +
            ∑ j, y j • EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ) := by
      intro c y
      rw [Fin.sum_univ_succAbove _ i, add_assoc]
      simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, comp_apply]
    -- the front face is based at `b + e_{ι(i)}`
    have hbase : WithLp.toLp 2 (fun k => ((b + Pi.single (ι i) 1 : Fin P → ℤ) k : ℝ)) =
        WithLp.toLp 2 (fun k => (b k : ℝ)) + EuclideanSpace.single (ι i) (1 : ℝ) := by
      ext k
      by_cases hk : k = ι i
      · subst hk
        simp only [Pi.add_apply, Pi.single_eq_same, Int.cast_add, Int.cast_one, PiLp.add_apply, PiLp.single_eq_same]
      · simp only [Pi.add_apply, ne_eq, hk, not_false_eq_true, Pi.single_eq_of_ne, add_zero, PiLp.add_apply, PiLp.single_eq_of_ne]
    simp only [hface, one_smul, zero_smul, add_zero, ← hbase]
    rw [integral_const_mul, integral_const_mul, mul_sub]
  clear cmcdtfrcb_cube_partial_ftc
  /- Regrouping the faces of a lattice chain (boundary of an integer polyhedral chain
  `∑_{F ∈ Lₙ} β_F [[F]]`, Simon Ch. 6, 5.1): index an oriented lattice `(m+1)`-cube by `p = (ι, b)`
  with `ι` strictly increasing, and its `i`-th front and back faces by
  `(ι ∘ succAbove i, b + 𝟙_{ι i})` and `(ι ∘ succAbove i, b)`.  Then the signed face sum
  `∑_p β_p ∑_i (-1)ⁱ (I(front) - I(back))` is an integer combination `∑_{q ∈ s'} β'_q I(q)` of
  lattice `m`-cube indices, uniformly in `I`: take for `s'` all the faces and
  `β'_q = ∑_{p,i} β_p (-1)ⁱ ([front = q] - [back = q])`; the `q`-sum then picks out the two faces. -/
  have cmcdtfrcb_face_regroup : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ q ∈ s', StrictMono q.1) ∧ ∀ I : (Fin m → Fin P) × (Fin P → ℤ) → ℝ, ∑ p ∈ s, (β p : ℝ) * ∑ i : Fin (m + 1), (-1 : ℝ) ^ (i : ℕ) * (I (p.1 ∘ Fin.succAbove i, p.2 + Pi.single (p.1 i) 1) - I (p.1 ∘ Fin.succAbove i, p.2)) = ∑ q ∈ s', (β' q : ℝ) * I q := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfrcb_cube_stokes hVO hMR hIMC
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
      Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp only [Finset.mem_insert, Finset.mem_singleton, true_or]⟩⟩
    have hbS : ∀ p ∈ s, ∀ i, bk p i ∈ S := fun p hp i =>
      Finset.mem_biUnion.2 ⟨p, hp, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp only [Finset.mem_insert, Finset.mem_singleton, or_true]⟩⟩
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
  /- **Boundary of a lattice chain** (Simon Ch. 6, 5.1, step 8 of the deformation theorem: the
  boundary of an integer lattice chain is an integer lattice chain).  Index an oriented lattice
  `(m+1)`-cube by `p = (ι, b)`, `Φ_p y = b + Σⱼ yⱼ e_{ι j}`, and let `T = Σ_{p ∈ s} β_p [[p]]`.  For a
  test `m`-form `γ`, `∂T(γ) = T(dγ) = Σ_p β_p ∫_{(0,1)^{m+1}} dγ(Φ_p y)(e_ι) dy`; cubical Stokes
  turns each integral into the signed face sum
  `Σᵢ (-1)ⁱ ([[ι ∘ succAbove i, b + 𝟙_{ι i}]](γ) - [[ι ∘ succAbove i, b]](γ))`, and regrouping
  these faces gives integers `β'_q` on strictly increasing indices `q ∈ s'`, chosen independently
  of `γ`. -/
  have cmcdtfr_chain_boundary : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (β : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℤ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), (∀ p ∈ s, StrictMono p.1) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∃ (s' : Finset ((Fin m → Fin P) × (Fin P → ℤ))) (β' : (Fin m → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s', StrictMono p.1) ∧ ∀ γ : TestFormOn (univ : Set (Euclid P)) m, T.boundary γ = ∑ p ∈ s', (β' p : ℝ) * ∫ y : Euclid m in {y | ∀ i, 0 < y i ∧ y i < 1}, γ.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation hVO hMR hIMC
    intro P m s β T hs hT
    -- one regrouping `(s', β')` of the signed faces serves every face functional `I`
    obtain ⟨s', β', hs', hI⟩ := cmcdtfrcb_face_regroup P m s β hs
    clear cmcdtfrcb_face_regroup
    refine ⟨s', β', hs', fun γ => ?_⟩
    -- `∂T(γ) = T(dγ)`; expand `T`, and the right side as the regrouped face sum of `I q = [[q]](γ)`
    rw [GeometricCurrentOn.boundary_apply, hT, ← hI fun q =>
      ∫ y : Euclid m in {y | ∀ i, 0 < y i ∧ y i < 1}, γ.1
        (HAdd.hAdd (WithLp.toLp 2 (fun i => (q.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (q.1 j) (1 : ℝ)))
        (fun j => EuclideanSpace.single (q.1 j) (1 : ℝ))]
    -- cube by cube, `[[p]](dγ)` is the signed sum of the faces of `p` (cubical Stokes)
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    exact cmcdtfrcb_cube_stokes P m p.1 p.2 γ γ.2.1.1
  clear cmcdtfrcb_cube_stokes cmcdtfrcb_face_regroup
  /- **Coefficient bounds for the Euclidean covector norm** (Simon Ch. 6, 1.15; facts used for the
  face currents in the proof of the Deformation Theorem 6.5.1, displays (29)–(30) and (34)).  With
  `e` the standard basis of `ℝᴾ`, let `f J = α(e_{J(0)}, …, e_{J(k-1)})²` for strictly increasing
  `J : Fin k → Fin P` and `f J = 0` otherwise, so `|α|² = ∑_J f J` is a sum of nonnegative terms.
  (i) The single term `f I = α(e_I)²` is at most the sum.  (ii) For strictly increasing
  `ι : Fin (k+1) → Fin P` the faces `ι ∘ i.succAbove` are strictly increasing and pairwise
  distinct, so `∑_i α(e_{ι ∘ i.succAbove})²` is a sub-sum of `∑_J f J`. -/
  have cmcdtfrfic_coeff_bounds : ∀ (P k : ℕ) (α : Covector (Euclid P) k), (∀ I : Fin k → Fin P, StrictMono I → |α (fun j => EuclideanSpace.single (I j) (1 : ℝ))| ≤ covectorEuclideanNorm α) ∧ ∀ ι : Fin (k + 1) → Fin P, StrictMono ι → ∑ i : Fin (k + 1), (α (fun j => EuclideanSpace.single (ι (i.succAbove j)) (1 : ℝ))) ^ 2 ≤ covectorEuclideanNorm α ^ 2 := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists cmcdtfrcb_pullback_divergence dfmf_cube_open dfmf_trace_fderiv cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary hVO hMR hIMC
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
  /- **The divergence field of a face** (Simon Ch. 6, proof of Theorem 5.1, (29)–(30): the field
  `G_p` of the face-current construction).  For a smooth `m`-form `γ`, strictly increasing
  `ι : Fin (m + 1) → Fin P`, `a ∈ ℝᴾ`, `E = (e_{ι 0}, …, e_{ι m})` and `Φ(y) = a + Σⱼ yⱼ e_{ι j}`,
  put `Gᵢ(y) = (−1)ⁱ γ(Φ y)(E⁽ⁱ⁾)`, `E⁽ⁱ⁾ = E ∘ succAbove i`.  Then `G` is `C^∞`,
  `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²` (`cmcdtfrfic_coeff_bounds` (ii)), and
  `trace DG(y) = Σᵢ ∂ᵢGᵢ(y) = dγ(Φ y)(E)` (`dfmf_trace_fderiv`, `cmcdtfrcb_pullback_divergence`). -/
  have cmcdtfrfic_divergence_field : ∀ (P m : ℕ) (γ : DifferentialForm (Euclid P) m) (ι : Fin (m + 1) → Fin P) (a : Euclid P), ContDiff ℝ (⊤ : ℕ∞) γ → StrictMono ι → ∃ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ y, ‖G y‖ ≤ covectorEuclideanNorm (γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)))) ∧ ∀ y, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) = exteriorDerivative γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ)) (fun j => EuclideanSpace.single (ι j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary hVO hMR hIMC
    intro P m γ ι a hγ hι
    -- `Gᵢ(y) = (−1)ⁱ γ(Φ y)(E⁽ⁱ⁾)` is smooth and `dγ(Φ y)(E) = Σᵢ ∂ᵢGᵢ(y)`
    have hpd := cmcdtfrcb_pullback_divergence P m ι a γ hγ
    clear cmcdtfrcb_pullback_divergence
    have hF := hpd.1
    have hd := hpd.2
    have hG : ContDiff ℝ (⊤ : ℕ∞) fun y : Euclid (m + 1) => WithLp.toLp 2 fun i : Fin (m + 1) =>
        (-1 : ℝ) ^ (i : ℕ) * γ (a + ∑ j, y j • EuclideanSpace.single (ι j) (1 : ℝ))
          (fun j => EuclideanSpace.single ((ι ∘ Fin.succAbove i) j) (1 : ℝ)) :=
      contDiff_euclidean.2 hF
    refine ⟨_, hG, fun y => ?_, fun y => ?_⟩
    · -- `|G(y)|² = Σᵢ γ(Φ y)(E⁽ⁱ⁾)² ≤ |γ(Φ y)|²`
      rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (covectorEuclideanNorm_nonneg _)]
      refine Real.sqrt_le_sqrt (le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_)
        ((cmcdtfrfic_coeff_bounds P m _).2 ι hι))
      rw [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, mul_pow, ← pow_mul, mul_comm (i : ℕ) 2,
        pow_mul, neg_one_sq, one_pow, one_mul]
      rfl
    · -- `trace DG(y) = Σᵢ ∂ᵢGᵢ(y) = dγ(Φ y)(E)`
      rw [dfmf_trace_fderiv _ _ y ((hG.differentiable (by decide)) y), hd y]
  clear cmcdtfrcb_pullback_divergence dfmf_trace_fderiv
  /- `|α(e_{ι(0)}, …, e_{ι(k-1)})| ≤ ‖α‖`: the `e_l` are unit vectors (`le_opNorm`). -/
  have dfmf_eval_frame_le : ∀ (P k : ℕ) (ι : Fin k → Fin P) (α : Covector (Euclid P) k), ‖α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))‖ ≤ ‖α‖ := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfrfic_coeff_bounds cmcdtfrfic_divergence_field hVO hMR hIMC
    intro P k ι α
    refine (α.le_opNorm _).trans_eq ?_
    rw [Finset.prod_eq_one fun j _ => by rw [PiLp.norm_single, norm_one], mul_one]
  /- **Evaluations of a test form on a coordinate frame are bounded and continuous**: for a
  continuous `Φ` and `w ∈ L¹(S, μ)`, `y ↦ w(y) ω(Φ y)(e_{ι(1)}, …, e_{ι(n)})` is integrable on `S`,
  since `|ω(x)(e_ι)| ≤ ‖ω(x)‖` (`dfmf_eval_frame_le`) is bounded (`ω` is continuous with compact
  support). -/
  have dfmf_form_eval_integrable : ∀ (P n k : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) n) (ι : Fin n → Fin P) (Φ : Euclid k → Euclid P) (w : Euclid k → ℝ) (S : Set (Euclid k)) (μ : Measure (Euclid k)), Continuous Φ → IntegrableOn w S μ → IntegrableOn (fun y => w y * ω.1 (Φ y) (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) S μ := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open cmcdtfrfic_support_faces dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfrfic_coeff_bounds cmcdtfrfic_divergence_field hVO hMR hIMC
    intro P n k ω ι Φ w S μ hΦ hw
    have hωc : Continuous ω.1 := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := ω.property.1.2.exists_bound_of_continuous hωc
    exact hw.mul_bdd (c := C) ((continuous_eval_const _).comp (hωc.comp hΦ)).aestronglyMeasurable
      (Eventually.of_forall fun y => (dfmf_eval_frame_le P n ι _).trans (hC _))
  clear dfmf_eval_frame_le
  /- **Simon Ch. 6, proof of Theorem 5.1** (the face currents of (29)–(30) and (34)): for faces
  `p = (ι_p, b_p) ∈ s` with `ι_p` strictly increasing and densities `w_p` integrable on
  `Q₁ = (0, 1)ⁿ`, put `Φ_p(y) = b_p + Σ_j y_j e_{ι_p(j)}` and
  `D(ω) = Σ_{p ∈ s} ∫_{Q₁} w_p(y) ω(Φ_p(y))(e_{ι_p(0)}, …, e_{ι_p(m)}) dy`.  The integrands are
  integrable and `D` is a current (I)–(II).  Every such `D` has (a) `M(D) ≤ Σ_p ∫_{Q₁} |w_p|`, since
  `|ω(x)(e_{ι_p})| ≤ |ω(x)| ≤ 1` for admissible `ω`; (b) `M(∂D) ≤ Σ_p B_p` whenever
  `|∫_{Q₁} w_p div G| ≤ B_p` for all smooth `G` with `|G| ≤ 1`, since `∂D(γ) = D(dγ)` and on the face
  `p` the integrand `dγ(Φ_p(y))(e_{ι_p})` is `div G_p(y)` for a smooth `G_p` with
  `|G_p| ≤ |γ ∘ Φ_p| ≤ 1`; (c) `spt D` lies in the closed faces with `∫_{Q₁} |w_p| ≠ 0`. -/
  have cmcdtfr_face_integral_current : ∀ (P m : ℕ) (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (w : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) → (∀ p ∈ s, IntegrableOn (w p) {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid (m + 1)))) → (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), ∀ p ∈ s, IntegrableOn (fun y => w p y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) {y : Euclid (m + 1) | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ D : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1), (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), D ω = ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, w p y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) → D.mass ≤ ENNReal.ofReal (∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ∧ (∀ B : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → ℝ, (∀ p ∈ s, ∀ G : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ (⊤ : ℕ∞) G → (∀ y, ‖G y‖ ≤ 1) → |∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| ≤ B p) → D.boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, B p)) ∧ (∀ x ∈ D.support, ∃ p ∈ s, (∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |w p y|) ≠ 0 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) = x) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary hVO hMR hIMC
    intro P m s w hι hw
    -- (III)(c) is the support lemma; (a) and (b) bound each admissible evaluation
    refine ⟨fun ω p hp => ?_, fun D hD => ⟨?_, fun B hB => ?_,
      cmcdtfrfic_support_faces P m s w D hw hD⟩⟩
    · -- (I): `w_p` is integrable on `Q₁` and `Φ_p` is continuous (`dfmf_form_eval_integrable`)
      exact dfmf_form_eval_integrable P (m + 1) (m + 1) ω p.1 _ (w p) _ _
        (continuous_const.add (continuous_finsetSum _ fun j _ =>
          (PiLp.continuous_apply 2 _ j).smul continuous_const)) (hw p hp)
    · -- (a): for admissible `ω`, `|w_p(y) ω(Φ_p(y))(e_{ι_p})| ≤ |w_p(y)| |ω(Φ_p(y))| ≤ |w_p(y)|`
      refine sSup_le ?_
      rintro r ⟨ω, hω, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hD ω]
      refine Finset.sum_le_sum fun p hp => (Real.le_norm_self _).trans
        (norm_integral_le_of_norm_le (hw p hp).abs (ae_of_all _ fun y => ?_))
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (((cmcdtfrfic_coeff_bounds P (m + 1) _).1 p.1 (hι p hp)).trans (hω.2 _))
    · -- (b): for admissible `γ`, `∂D(γ) = D(dγ)`, and on the face `p` the integrand is
      -- `w_p div G_p` with `|G_p| ≤ |γ ∘ Φ_p| ≤ 1`, so the `p`-th summand is at most `B_p`
      refine sSup_le ?_
      rintro r ⟨γ, hγ, rfl⟩
      refine ENNReal.ofReal_le_ofReal ?_
      rw [GeometricCurrentOn.boundary_apply, hD]
      refine Finset.sum_le_sum fun p hp => ?_
      obtain ⟨G, hG, hGn, hGt⟩ := cmcdtfrfic_divergence_field P m
        γ.1 p.1 (WithLp.toLp 2 fun i => (p.2 i : ℝ))
        γ.property.1.1 (hι p hp)
      calc _ = ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y) :=
            integral_congr_ae (ae_of_all _ fun y => congrArg (w p y * ·) (hGt y).symm)
        _ ≤ |∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1},
            w p y * LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ G y)| := le_abs_self _
        _ ≤ B p := hB p hp G hG fun y => (hGn y).trans (hγ.2 _)
  clear cmcdtfrfic_support_faces cmcdtfrfic_coeff_bounds cmcdtfrfic_divergence_field
  /- **Only finitely many unit lattice faces meet a compact set** (Simon Ch. 6, proof of the
  deformation theorem 5.1, after (33): the sum `P = Σ_{F ∈ 𝓛ₙ} β_F [[F]]` runs over the finitely many
  faces meeting the compact `spt Q`).  Let `p = (ι, b)`, `ι : Fin k → Fin P` arbitrary, `b ∈ ℤᴾ`,
  and `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)} ∈ K` for some `y ∈ [0,1]ᵏ`.  Then `Φ_p(y)ᵢ = bᵢ + Sᵢ` with
  `Sᵢ = Σⱼ [ι(j) = i] yⱼ ∈ [0, k]`, and `|Φ_p(y)ᵢ| ≤ ‖Φ_p(y)‖ ≤ ρ` on the bounded `K`, so
  `−⌈ρ⌉ − k ≤ bᵢ ≤ ⌈ρ⌉`.  Hence `p` lies in the finite set `(Fin k → Fin P) × [−N, N]ᴾ`,
  `N = ⌈ρ⌉ + k`. -/
  have cmcdtfrsd_faces_meeting_compact_finite : ∀ (P k : ℕ) (K : Set (Euclid P)), IsCompact K → {p : (Fin k → Fin P) × (Fin P → ℤ) | ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) ∈ K}.Finite := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current hVO hMR hIMC
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
        _ = k := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
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
  /- **Simon 6.5.1** (finiteness of the lattice chains `P = Σ_F β_F [[F]]`): for compact
  `K ⊆ ℝᴾ` and `Λ ∈ ℝ`, only finitely many currents `T = Σ_{p ∈ s} β_p [[F_p]]` exist whose unit
  `k`-faces `F_p = b + {Σⱼ yⱼ e_{ι(j)} : y ∈ [0,1]ᵏ}` (`p = (ι, b)`, `ι` increasing, `b ∈ ℤᴾ`) all
  meet `K` and whose integer coefficients satisfy `Σ_p |β_p| ≤ Λ`.  Only the faces of a finite set
  `S` meet `K` (`cmcdtfrsd_faces_meeting_compact_finite`).  Hence `T = Σ_{p ∈ S} c_p [[F_p]]`, `c_p = β_p` on `s` and `0` off it,
  with `c : S → [-⌊Λ⌋, ⌊Λ⌋] ∩ ℤ`, a finite set; and `c` determines `T` (`GeometricCurrentOn.ext`). -/
  have cmcdtfr_finite_family : ∀ (P k : ℕ) (K : Set (Euclid P)) (Λ : ℝ), IsCompact K → {T : GeometricCurrentOn (univ : Set (Euclid P)) k | ∃ (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ K) ∧ ∑ p ∈ s, |(β p : ℝ)| ≤ Λ ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, T ω = ∑ p ∈ s, (β p : ℝ) * ∫ y : Euclid k in {y | ∀ i, 0 < y i ∧ y i < 1}, ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))}.Finite := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current hVO hMR hIMC
    intro P k K Λ hK
    -- steps 1–2: only finitely many faces meet `K` (`cmcdtfrsd_faces_meeting_compact_finite`)
    have hfin := cmcdtfrsd_faces_meeting_compact_finite P k K hK
    clear cmcdtfrsd_faces_meeting_compact_finite
    let S : Finset ((Fin k → Fin P) × (Fin P → ℤ)) := hfin.toFinset
    have hSK : ∀ p : (Fin k → Fin P) × (Fin P → ℤ), (∃ y : Euclid k, (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
        (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
          ∈ K) → p ∈ S := fun p hp => hfin.mem_toFinset.2 hp
    -- steps 3–5: each such current is `∑_{p ∈ S} c p [[p]]` with `c : S → [-⌊Λ⌋, ⌊Λ⌋]`, and is
    -- determined by `c`
    let I : (Fin k → Fin P) × (Fin P → ℤ) → TestFormOn (univ : Set (Euclid P)) k → ℝ := fun p ω =>
      ∫ y : Euclid k in {y | ∀ i, 0 < y i ∧ y i < 1}, ω.1
        (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
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
        · have h₀ : (0 : ℤ) ≤ ⌊Λ⌋ := Int.le_floor.mpr (by simpa only [Int.cast_zero] using hΛ0)
          exact ⟨by linarith, h₀⟩
      · intro ω
        rw [hT ω, Finset.sum_coe_sort S (fun p => ((if p ∈ s then β p else 0 : ℤ) : ℝ) * I p ω),
          ← Finset.sum_subset hsS]
        · exact Finset.sum_congr rfl fun p hp => by rw [ite_eq_left hp]
        · intro p _ hp
          rw [ite_eq_right hp, Int.cast_zero, zero_mul]
  /- **The `m`-skeleton of the unit cubical lattice is `H^{m+1}`-null** (Simon Ch. 6, proof of the
  deformation theorem 5.1, (26)–(33): `Hⁿ(L_{n−1}) = 0`, `n = m + 1`).  The points of `ℝᴾ` with at
  least `P − m` integer coordinates lie in the countably many coordinate planes
  `A(s, z) = {x : xᵢ = zᵢ for i ∈ s}`, `P ≤ m + |s|`, `z ∈ ℤᴾ`.  Each `A(s, z)` is the image of the
  Lipschitz map `ℝ^{Fin P \ s} → ℝᴾ`, `t ↦ (zᵢ on s, tᵢ off s)`, whose source is `μH[m + 1]`-null:
  it is a union of balls of finite `μH[P − |s|]` (= Lebesgue) measure, and `P − |s| < m + 1`.
  Finally `μHE[m + 1]` is a multiple of `μH[m + 1]`. -/
  have cmcdtfr_skeleton_null : ∀ (P m : ℕ), μHE[m + 1] {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} = 0 := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family hVO hMR hIMC
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
        · simp only [h, ↓reduceDIte, dist_self, dist_nonneg]
        · simpa only [h, ↓reduceDIte] using dist_le_pi_dist t t' ⟨i, h⟩
      have hg : LipschitzWith _ g := (PiLp.lipschitzWith_toLp 2 fun _ : Fin P => ℝ).comp hg1
      have hsub : {x : Euclid P | ∀ i ∈ s, x i = z i} ⊆ g '' univ := by
        intro x hx
        refine ⟨fun j => x j.1, mem_univ _, ?_⟩
        ext i
        by_cases h : i ∈ s
        · simp only [h, ↓reduceDIte, hx i h, g]
        · simp only [h, ↓reduceDIte, g]
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
  /- **Coordinate `k`-planes and their unit orientations** (Simon Ch. 6, (1.2), (1.7): the
  `k`-vector `e_α = e_{i₁} ∧ ⋯ ∧ e_{iₖ}` pairs as `⟨ω, e_α⟩ = ω(e_{i₁}, …, e_{iₖ})`; §5: a face
  `F ∈ 𝓛ₖ` lies in a coordinate `k`-plane, oriented by `±e_α` as in (27)).  For strictly increasing
  `ι : Fin k → Fin P` the frame `τⱼ = e_{ι(j)}` is the standard orthonormal basis of `ℝᴾ` composed
  with the injective `ι`, hence orthonormal and linearly independent, so `V = span{τⱼ}` has
  dimension `k`.  Evaluation `α ↦ α(τ)` is continuous linear, which gives the `k`-vector `e` with
  `e(α) = α(τ)`; the frame `τ` itself witnesses that `e` and `-e` are unit orientations of `V`. -/
  have cmcdtfrpi_coord_plane_orientation : ∀ (P k : ℕ) (ι : Fin k → Fin P), StrictMono ι → Module.finrank ℝ (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) = k ∧ ∃ e : MultiVector P k, (∀ α : Covector (Euclid P) k, e α = α (fun j => EuclideanSpace.single (ι j) (1 : ℝ))) ∧ IsUnitOrientationOf e (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) ∧ IsUnitOrientationOf (-e) (Submodule.span ℝ (range (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P))) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null hVO hMR hIMC
    intro P k ι hι
    -- step 1: `τ = (eᵢ)ᵢ ∘ ι` is orthonormal, as `ι` is injective
    have hτ : Orthonormal ℝ (fun j => EuclideanSpace.single (ι j) (1 : ℝ) : Fin k → Euclid P) :=
      EuclideanSpace.orthonormal_single.comp ι hι.injective
    -- step 3: `e = (α ↦ α(τ))`, evaluation at `τ` being continuous linear
    let e : MultiVector P k :=
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun j => EuclideanSpace.single (ι j) (1 : ℝ)
    -- step 2: an orthonormal family is linearly independent, so `dim V = #(Fin k) = k`
    refine ⟨by rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin], e, fun α => rfl,
      ?_, ?_⟩
    -- step 4: the frame `τ` orients `V` with sign `+` for `e`
    · exact ⟨_, hτ, rfl, Or.inl fun α => rfl⟩
    -- step 5: and with sign `-` for `-e`
    · exact ⟨_, hτ, rfl, Or.inr fun α => rfl⟩
  /- **Isometric images: Borel, `Hᵏ`-measure and change of variables** (Simon Ch. 6 §5, deformation
  theorem: integrals over a unit lattice face `Φ_p((0,1)ᵏ)` are computed on its parameter cube).  For
  an isometry `Φ : ℝᵏ → ℝᴾ` and a Borel set `A ⊆ ℝᵏ`, `Φ(A)` is Borel, `Hᵏ(Φ(A)) = Lᵏ(A)` and
  `∫_{Φ(A)} h dHᵏ = ∫_A h ∘ Φ dLᵏ` for every `h : ℝᴾ → ℝ`.  As `ℝᵏ` is complete, `Φ` is a closed,
  hence measurable, embedding; `Hᵏ` is isometry invariant and equals `Lᵏ` on `ℝᵏ`; and
  `Φ_#Hᵏ = Hᵏ⌞range Φ` restricts to `Hᵏ⌞Φ(A) = Φ_#(Lᵏ⌞A)`, so changing variables along `Φ` needs no
  integrability of `h` (both Bochner integrals vanish when it fails). -/
  have cmcdtfrpi_isometry_image_integral : ∀ (P k : ℕ) (Φ : Euclid k → Euclid P) (A : Set (Euclid k)), Isometry Φ → MeasurableSet A → MeasurableSet (Φ '' A) ∧ μHE[k] (Φ '' A) = volume A ∧ ∀ h : Euclid P → ℝ, ∫ x in Φ '' A, h x ∂μHE[k] = ∫ y in A, h (Φ y) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null cmcdtfrpi_coord_plane_orientation hVO hMR hIMC
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
  /- **A set that agrees with `x + V` near `x` has approximate tangent space `V` at `x`** (Simon
  Ch. 3, Definition 1.4; applied to the open unit lattice faces carrying an integer polyhedral chain
  in the deformation theorem, Simon Ch. 6, §5).  Let `f ∈ C_c(ℝᴾ)` vanish off the ball
  `B = B(0, R)` and `0 < r < δ / R`.  For `y ∈ B`, both a `z` with `η_{x,r}(z) = y` and
  `z = x + r y` satisfy `|z − x| = r|y| < rR < δ`, so the hypothesis gives
  `B ∩ η_{x,r}(M) = B ∩ V`.  As `f = 0` off the Borel ball `B`, `∫_S f dHⁿ = ∫_{B ∩ S} f dHⁿ` for
  every set `S`; hence `∫_{η_{x,r}(M)} f dHⁿ = ∫_V f dHⁿ` for `r ∈ (0, δ / R)`, and the blow-up
  integrals are eventually constant as `r ↓ 0`.  No measurability of `M` is used. -/
  have cmcdtfrpi_local_plane_tangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (V : Submodule ℝ (Euclid P)) (δ : ℝ), Module.finrank ℝ V = n → 0 < δ → (∀ z : Euclid P, dist z x < δ → (z ∈ M ↔ z - x ∈ V)) → HasApproximateTangentSpaceAt n M x V := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_open dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null cmcdtfrpi_coord_plane_orientation cmcdtfrpi_isometry_image_integral hVO hMR hIMC
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
  /- **The integer multiplicity triple of one open unit face** (Simon Ch. 6, 2.2 and §5: `[[F]]` for
  a unit lattice face `F`).  For `p = (ι, b)` with `ι` strictly increasing, `Φ_p` is an isometry, so
  the open face `F̆ = Φ_p((0,1)ᵏ)` is Borel with `Hᵏ(F̆) = 1` and lies in the range of the Lipschitz
  `Φ_p`.  Near `x = Φ_p(t)`, `F̆` agrees with the plane `x + V`, `V = span{e_{ι(j)}}`, which is
  therefore its approximate tangent space, oriented by `e = (α ↦ α(e_ι))`.  So `(F̆, 1, e)` is an
  `IMRep` with action `ω ↦ ∫_{(0,1)ᵏ} ω(Φ_p y)(e_ι) dy`. -/
  have dfmf_face_imrep : ∀ (P k : ℕ) (p : (Fin k → Fin P) × (Fin P → ℤ)), StrictMono p.1 → ∃ R : IMRep (univ : Set (Euclid P)) k, R.carrier = (fun y : Euclid k => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} ∧ (∀ x, R.mult x = 1) ∧ (∀ x (α : Covector (Euclid P) k), R.orient x α = α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ μHE[k] R.carrier = 1 ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) k, R.action ω.1 = ∫ y : Euclid k in {y | ∀ i, 0 < y i ∧ y i < 1}, ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    clear cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null hVO hMR hIMC
    intro P k p hp
    -- `Φ_p` is an isometry; `F̆ = Φ_p(Q₁)` is Borel with `Hᵏ(F̆) = vol(Q₁) = 1`
    have hΦ := ((cmcdtfr_face_geometry P k).2 p p hp hp).1
    clear cmcdtfr_face_geometry
    have hiso : Isometry (fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
        ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) := Isometry.of_dist_eq hΦ
    have hF :=
      cmcdtfrpi_isometry_image_integral P k _ _ hiso (dfmf_cube_meas k)
    clear dfmf_cube_meas cmcdtfrpi_isometry_image_integral
    have hFm := hF.1
    have hFμ := hF.2.1
    have hFint := hF.2.2
    have hF1 := hFμ.trans (cmcdtfrfg_cube_volume k)
    -- the coordinate plane `V` (dimension `k`) and its unit orientation `e`
    clear cmcdtfrfg_cube_volume
    obtain ⟨hdim, e, he, heV, -⟩ := cmcdtfrpi_coord_plane_orientation P k p.1 hp
    -- near `x = Φ_p(t)`, `F̆` agrees with `x + V`, so `V` is its approximate tangent space
    clear cmcdtfrpi_coord_plane_orientation
    have htan : ∀ t : Euclid k, (∀ i, 0 < t i ∧ t i < 1) → HasApproximateTangentSpaceAt k
        ((fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
          ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1})
        (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, t j • EuclideanSpace.single (p.1 j) (1 : ℝ)))
        (Submodule.span ℝ (range (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ) : Fin k → Euclid P))) := by
      intro t ht
      -- a ball `B(t, δ) ⊆ Q₁`, `Q₁` being open
      obtain ⟨δ, hδ₀, hδt⟩ := Metric.isOpen_iff.1 (dfmf_cube_open k) t ht
      refine cmcdtfrpi_local_plane_tangent P k _ _ _ δ hdim hδ₀ fun z hz =>
        ⟨fun hzC => ?_, fun hzV => ?_⟩
      · -- (⇒) `z = Φ_p(t')`, so `z - Φ_p(t) = Σⱼ (t'ⱼ - tⱼ) e_{ι(j)} ∈ V`
        obtain ⟨t', -, rfl⟩ := hzC
        beta_reduce
        rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [← sub_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · -- (⇐) `z - Φ_p(t) = Σⱼ cⱼ e_{ι(j)}` and `z = Φ_p(t + c)` with `|c| = |z - Φ_p(t)| < δ`,
        -- so `t + c ∈ B(t, δ) ⊆ Q₁`
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hzV
        beta_reduce at hc
        have hzt' : WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
            ∑ j, (t + WithLp.toLp 2 c) j • EuclideanSpace.single (p.1 j) (1 : ℝ) = z := by
          simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib, hc]
          abel
        refine ⟨t + WithLp.toLp 2 c, hδt ?_, hzt'⟩
        rw [mem_ball, ← hΦ (t + WithLp.toLp 2 c) t, hzt']
        exact hz
    clear dfmf_cube_open cmcdtfrpi_local_plane_tangent
    refine ⟨{ carrier := _
              mult := fun _ => 1
              orient := fun _ => e
              measurableSet_carrier := hFm
              carrier_subset := subset_univ _
              rectifiable := ⟨∅, measure_empty, fun _ => _, fun _ => ⟨1, hiso.lipschitzWith⟩,
                fun x hx => Or.inr (mem_iUnion.2 ⟨0, image_subset_range _ _ hx⟩)⟩
              measurable_mult := measurable_const
              mult_pos := fun _ _ => one_pos
              locallyIntegrable_mult := fun K _ _ => by
                rw [Nat.cast_one, setLIntegral_one]
                exact ne_top_of_le_ne_top (hF1.symm ▸ ENNReal.one_ne_top)
                  (measure_mono inter_subset_left)
              aestronglyMeasurable_orient := aestronglyMeasurable_const
              orients := ae_restrict_of_forall_mem hFm fun x hx => by
                obtain ⟨t, ht, rfl⟩ := hx
                exact ⟨_, htan t ht, heV⟩ }, rfl, fun _ => rfl, fun _ α => he α, hF1, fun ω => ?_⟩
    -- the action: `∫_{F̆} ⟨ω, e⟩ dHᵏ = ∫_{Q₁} ω(Φ_p y)(e_ι) dy`
    show ∫ x in _, ((1 : ℕ) : ℝ) * e (ω.1 x) ∂μHE[k] = _
    rw [hFint]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [Nat.cast_one, one_mul, he]
  clear dfmf_cube_open cmcdtfrpi_coord_plane_orientation cmcdtfrpi_isometry_image_integral cmcdtfrpi_local_plane_tangent
  /- **On an open lattice face the orientation is a Borel sign times `e_{ι(1)} ∧ ⋯ ∧ e_{ι(n)}`**
  (Simon Ch. 6, proof of 5.1, (26)–(28)).  The open face `F̆ = Φ_p((0,1)ⁿ)` carries the integer
  multiplicity triple `(F̆, 1, e)`, `e = (α ↦ α(e_ι))` (`dfmf_face_imrep`), and two integer
  multiplicity triples have orientations agreeing up to sign a.e. on the intersection of their
  carriers (`rsdic_imrep_ae_orient_eq_or_eq_neg_inter`), so `ξ(x) = ±e` a.e. on `M ∩ F̆`.  With `ξ̃`
  a strongly measurable version of `ξ` and `θ = dx^ι` (`θ(e_ι) = 1`), `σ = sign ξ̃(·)(θ)` is Borel,
  and `ξ(x) = σ(x) e` a.e. on `M ∩ F̆`. -/
  have cmcdtfrsd_coordinate_plane_orientation_sign : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → ∃ σ : Euclid P → ℤ, Measurable σ ∧ (∀ x, |σ x| ≤ 1) ∧ ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ (fun y : Euclid n => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1})), ∀ α : Covector (Euclid P) n, R.orient x α = (σ x : ℝ) * α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary dfmf_form_eval_integrable cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null hVO hMR hIMC
    intro P n R p hι
    -- Step 1: the face triple `(F̆, 1, e)`; on `M ∩ F̆` the orientation of `R` is `±e`
    obtain ⟨Rp, hRpc, -, hRpo, -, -⟩ := dfmf_face_imrep P n p hι
    clear dfmf_face_imrep
    have hsign : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ (fun y : Euclid n =>
        HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ''
          {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1})),
        (∀ α : Covector (Euclid P) n,
            R.orient x α = α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∨
          ∀ α : Covector (Euclid P) n,
            R.orient x α = -α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
      rw [inter_comm, ← hRpc]
      filter_upwards [Submission.rsdic_imrep_ae_orient_eq_or_eq_neg_inter P n univ Rp R
        isOpen_univ] with x hx
      rcases hx with h | h
      · exact Or.inl fun α => by rw [h, hRpo]
      · exact Or.inr fun α => by rw [h, neg_apply, hRpo]
    -- Step 2: the coordinate covector `θ = dx^ι`, `θ(e_ι) = 1`
    obtain ⟨θ, hθ⟩ := cmr_cc_det_covector_exists P n p.1
    clear cmr_cc_det_covector_exists
    have hθ1 : θ (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) = 1 := by
      have h := cmr_cc_det_covector_basis_kronecker P n p.1 p.1 θ hι hι hθ
      rw [ite_eq_left rfl] at h
      simpa only [EuclideanSpace.basisFun_apply] using h
    -- Step 3: a strongly measurable version `ξ̃` of `ξ`; `ξ̃(·)(θ)` is measurable
    clear cmr_cc_det_covector_basis_kronecker
    have hξξ' : R.orient =ᵐ[μHE[n].restrict (R.carrier ∩ (fun y : Euclid n =>
        HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ''
          {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1})]
        R.aestronglyMeasurable_orient.mk R.orient :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left R.aestronglyMeasurable_orient.ae_eq_mk
    have hf : Measurable fun x => R.aestronglyMeasurable_orient.mk R.orient x θ :=
      ((ContinuousLinearMap.apply ℝ ℝ θ).continuous.comp_stronglyMeasurable
        R.aestronglyMeasurable_orient.stronglyMeasurable_mk).measurable
    -- Step 4: `σ = sign ξ̃(·)(θ)`
    refine ⟨fun x => if 0 < R.aestronglyMeasurable_orient.mk R.orient x θ then 1
        else if R.aestronglyMeasurable_orient.mk R.orient x θ < 0 then -1 else 0,
      Measurable.ite (measurableSet_lt measurable_const hf) measurable_const
        (Measurable.ite (measurableSet_lt hf measurable_const) measurable_const measurable_const),
      fun x => ?_, ?_⟩
    · dsimp only
      split_ifs <;> decide
    -- Step 5: `ξ(x) = ±e` gives `ξ̃(x)(θ) = ±1`, hence `σ(x) = ±1`
    filter_upwards [hsign, hξξ'] with x hx hxx' α
    rcases hx with h | h
    · have h1 : 0 < R.aestronglyMeasurable_orient.mk R.orient x θ := by
        rw [← hxx', h θ, hθ1]
        exact one_pos
      rw [ite_eq_left h1, h α, Int.cast_one, one_mul]
    · have h1 : R.aestronglyMeasurable_orient.mk R.orient x θ < 0 := by
        rw [← hxx', h θ, hθ1]
        exact neg_one_lt_zero
      rw [ite_eq_right h1.not_gt, ite_eq_left h1, h α, Int.cast_neg, Int.cast_one, neg_one_mul]
  /- **On one open lattice face an integer multiplicity current is an integer `L¹` density**
  (Simon Ch. 6, proof of the deformation theorem 5.1, (33)).  Let `Φ_p(y) = b + ∑ⱼ yⱼ e_{ι(j)}` be
  an isometry, `Q₁ = (0, 1)ⁿ` and `F̆ = Φ_p(Q₁)`.  `F̆` is Borel, and by
  `cmcdtfrsd_coordinate_plane_orientation_sign` the orientation of
  `R = (M, θ, ξ)` is `ξ = σ E_p` `Hⁿ`-a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel.  As `Φ_p` is an
  isometry and `Hⁿ = vol` on `ℝⁿ`, `Hⁿ⌞F̆ = Φ_p # (vol⌞Q₁)`, so the integer function
  `u = (1_M θ σ) ∘ Φ_p` satisfies `∫_{M ∩ F̆} θ ⟨ω, ξ⟩ dHⁿ = ∫_{Q₁} u ⟨ω ∘ Φ_p, E_p⟩` and
  `∫_{Q₁} |u| ≤ ∫_{Q₁} (1_M θ) ∘ Φ_p = μ_R(F̆) < ∞` (`F̆` lies in a compact set). -/
  have cmcdtfrsd_face_density : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (p : (Fin n → Fin P) × (Fin P → ℤ)), StrictMono p.1 → Isometry (fun y : Euclid n => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) → ∃ u : Euclid n → ℝ, (∀ y, ∃ z : ℤ, u y = z) ∧ IntegrableOn u {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid n)) ∧ ENNReal.ofReal (∫ y : Euclid n in {y | ∀ i, 0 < y i ∧ y i < 1}, |u y|) ≤ R.measure ((fun y : Euclid n => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) n, IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (ω.1 x)) (R.carrier ∩ (fun y : Euclid n => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}) μHE[n] ∧ ∫ x in R.carrier ∩ (fun y : Euclid n => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}, (R.mult x : ℝ) * R.orient x (ω.1 x) ∂μHE[n] = ∫ y : Euclid n in {y | ∀ i, 0 < y i ∧ y i < 1}, u y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null dfmf_face_imrep hVO hMR hIMC
    intro P n R p hι hΦ
    -- notation: `Φ = Φ_p`, `Q₁` the open unit cube of `ℝⁿ`, `F̆ = Φ(Q₁)` the open face
    set Φ : Euclid n → Euclid P := fun y => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
      ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)
    set Q₁ : Set (Euclid n) := {y : Euclid n | ∀ i, 0 < y i ∧ y i < 1}
    -- Step 1: `Q₁` and `F̆` are Borel (`Φ` is an isometry, hence a measurable embedding)
    have hQ₁ : MeasurableSet Q₁ := dfmf_cube_meas n
    clear dfmf_cube_meas
    have hemb : MeasurableEmbedding Φ := hΦ.isClosedEmbedding.measurableEmbedding
    have hF : MeasurableSet (Φ '' Q₁) := hemb.measurableSet_image' hQ₁
    -- Step 2: the orientation is `σ E_p` a.e. on `M ∩ F̆`, with `σ ∈ {-1, 0, 1}` Borel
    obtain ⟨σ, hσm, hσ1, hσ⟩ := cmcdtfrsd_coordinate_plane_orientation_sign P n R p hι
    -- Step 3: change of variables, `Hⁿ⌞F̆ = Φ_# (vol⌞Q₁)`
    clear cmcdtfrsd_coordinate_plane_orientation_sign
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
    -- Step 4: the density `u = g ∘ Φ`, `g = 1_M θ σ`, dominated by `h = 1_M θ`
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
      · simp only [indicator_of_notMem hx, abs_zero, Std.le_refl, g, h]
    -- Step 5: `∫⁻_{Q₁} h ∘ Φ = R.measure F̆`
    have hmass : ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) = R.measure (Φ '' Q₁) := by
      rw [← hlint fun x => ENNReal.ofReal (h x)]
      have hh : (fun x => ENNReal.ofReal (h x)) =
          R.carrier.indicator fun x => (R.mult x : ℝ≥0∞) := by
        funext x
        by_cases hx : x ∈ R.carrier <;> simp only [hx, indicator_of_mem, ENNReal.ofReal_natCast, h, not_false_eq_true, indicator_of_notMem, ENNReal.ofReal_zero]
      rw [hh, lintegral_indicator R.measurableSet_carrier, IMRep.measure, withDensity_apply _ hF,
        Measure.restrict_restrict R.measurableSet_carrier, Measure.restrict_restrict hF,
        inter_comm]
    -- Step 6: `R.measure F̆ < ∞`, `F̆` lying in the compact set `Φ(toLp [0, 1]ⁿ)`
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
    -- Step 7: integrability of `u` and the mass bound
    have hle : ∀ y, ENNReal.ofReal |g (Φ y)| ≤ ENNReal.ofReal (h (Φ y)) :=
      fun y => ENNReal.ofReal_le_ofReal (hgh _)
    have hui : IntegrableOn (fun y => g (Φ y)) Q₁ (volume : Measure (Euclid n)) := by
      refine ⟨(hgm.comp hΦ.continuous.measurable).aestronglyMeasurable,
        hasFiniteIntegral_iff_enorm.2 ?_⟩
      calc ∫⁻ y in Q₁, ‖g (Φ y)‖ₑ = ∫⁻ y in Q₁, ENNReal.ofReal |g (Φ y)| := by
            simp_rw [Real.enorm_eq_ofReal_abs]
        _ ≤ ∫⁻ y in Q₁, ENNReal.ofReal (h (Φ y)) := lintegral_mono hle
        _ = R.measure (Φ '' Q₁) := hmass
        _ < ∞ := lt_top_iff_ne_top.2 hfin
    refine ⟨fun y => g (Φ y), fun y => ?_, hui, ?_, fun ω => ?_⟩
    · -- Step 4(b): `u` is integer valued
      by_cases hy : Φ y ∈ R.carrier
      · exact ⟨(R.mult (Φ y) : ℤ) * σ (Φ y), by simp only [indicator_of_mem hy, Int.cast_mul, Int.cast_natCast, g]⟩
      · exact ⟨0, by simp only [indicator_of_notMem hy, Int.cast_zero, g]⟩
    · rw [ofReal_integral_eq_lintegral_ofReal hui.abs (ae_of_all _ fun y => abs_nonneg _),
        ← hmass]
      exact lintegral_mono hle
    · -- Step 8: the integrand is `g ⟨ω, E_p⟩` a.e. on `M ∩ F̆`, which is integrable on `F̆`
      have hMF : MeasurableSet (R.carrier ∩ Φ '' Q₁) := R.measurableSet_carrier.inter hF
      have hae : (fun x => (R.mult x : ℝ) * R.orient x (ω.1 x))
          =ᵐ[μHE[n].restrict (R.carrier ∩ Φ '' Q₁)] fun x => g x *
            ω.1 x (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
        filter_upwards [hσ, ae_restrict_mem hMF] with x hx hxMF
        rw [hx, show g x = (R.mult x : ℝ) * (σ x : ℝ) from indicator_of_mem hxMF.1 _]
        ring
      have hgF : IntegrableOn g (Φ '' Q₁) μHE[n] := by
        rw [IntegrableOn, hrestr]
        exact hemb.integrable_map_iff.2 hui
      have hωE : IntegrableOn (fun x => g x * ω.1 x
          (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) (Φ '' Q₁) μHE[n] :=
        dfmf_form_eval_integrable P n P ω p.1 (fun x => x) g _ _ continuous_id hgF
      refine ⟨(hωE.mono_set inter_subset_right).congr_fun_ae hae.symm, ?_⟩
      calc ∫ x in R.carrier ∩ Φ '' Q₁,
              (R.mult x : ℝ) * R.orient x (ω.1 x) ∂μHE[n]
          = ∫ x in R.carrier ∩ Φ '' Q₁, g x * ω.1 x
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := integral_congr_ae hae
        _ = ∫ x in Φ '' Q₁, g x * ω.1 x
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) ∂μHE[n] := by
            refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hF inter_subset_right
              ?_).symm
            intro x hx
            have hxM : x ∉ R.carrier := fun hxM => hx.2 ⟨hxM, hx.1⟩
            simp only [indicator_of_notMem hxM, zero_mul, g]
        _ = ∫ y in Q₁, g (Φ y) * ω.1 (Φ y)
              (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := hint _
  clear dfmf_form_eval_integrable cmcdtfrsd_coordinate_plane_orientation_sign
  /- **Points of the `(m + 1)`-skeleton off the `m`-skeleton lie in open `(m + 1)`-faces** (Simon
  Ch. 6, proof of the deformation theorem 5.1: `L_n \ L_{n−1}` is the union of the interiors `F̆` of
  the faces `F ∈ 𝓛_n`, `n = m + 1`).  If `x ∈ ℝᴾ` has at least `P − (m + 1)` integer coordinates but
  not `P − m` of them, its set `J` of integer coordinates has exactly `P − (m + 1)` elements, so the
  increasing enumeration `ι` of `Jᶜ` is defined on `Fin (m + 1)`.  With `b = ⌊x⌋` and
  `yⱼ = fract(x_{ι(j)}) ∈ (0, 1)` (as `x_{ι(j)} ∉ ℤ`), the face point `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}`
  is `x`: its coordinate is `⌊xᵢ⌋ = xᵢ` for `i ∈ J` and `⌊xᵢ⌋ + fract(xᵢ) = xᵢ` for `i = ι(j)`. -/
  have cmcdtfrsd_skeleton_point_on_open_face : ∀ (P m : ℕ) (x : Euclid P), (∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → (¬ ∃ s : Finset (Fin P), P ≤ m + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z) → ∃ (p : (Fin (m + 1) → Fin P) × (Fin P → ℤ)) (y : Euclid (m + 1)), StrictMono p.1 ∧ (∀ i, 0 < y i ∧ y i < 1) ∧ HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) = x := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null dfmf_face_imrep cmcdtfrsd_face_density hVO hMR hIMC
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
  /- **`μ_T` vanishes off `spt T`** (Simon 6.2.11 with (MR)): if `R` represents `T` in `ℝᴾ`, then
  `Hⁿ(M ∖ spt T) = 0`.  `ℝᴾ ∖ spt T` is the open zero region `Z` of `T`; a form admissible for `Z`
  misses `spt T`, so `T` kills it (VO) and `M_Z(T) = 0`; by (MR) `∫_{M ∩ Z} θ dHⁿ = M_Z(T) = 0`, and
  `θ ≥ 1` on `M`. -/
  have dfmf_carrier_sdiff_support_null : ∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), R.Represents T → μHE[n] (R.carrier \ T.support) = 0 := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_cube_meas dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_finite_family cmcdtfr_skeleton_null dfmf_face_imrep cmcdtfrsd_face_density cmcdtfrsd_skeleton_point_on_open_face hIMC
    intro P n T R hR
    have hZo : IsOpen T.zeroRegion := T.isOpen_zeroRegion
    -- `M_Z(T) = 0`: an admissible form for `Z` misses `spt T = ℝᴾ ∖ Z`
    have h0 : T.massOn T.zeroRegion = 0 := by
      refine nonpos_iff_eq_zero.1 (sSup_le ?_)
      rintro _ ⟨ω, hω, rfl⟩
      exact (ENNReal.ofReal_eq_zero.2
        (hVO P n univ T ω (Set.disjoint_left.2 fun x hx hxS => hxS.2 (hω.1 hx))).le).le
    -- (MR): `∫_{Z ∩ M} θ dHⁿ = M_Z(T) = 0`
    clear hVO
    rw [hMR P n univ T R isOpen_univ hR _ hZo, IMRep.measure,
      withDensity_apply _ hZo.measurableSet,
      Measure.restrict_restrict hZo.measurableSet] at h0
    -- `M ∖ spt T = Z ∩ M` and `Hⁿ(Z ∩ M) ≤ ∫_{Z ∩ M} θ dHⁿ`, as `θ ≥ 1` on `M`
    clear hMR
    have hset : R.carrier \ T.support = T.zeroRegion ∩ R.carrier :=
      Set.ext fun x => ⟨fun h => ⟨not_not.1 fun hx => h.2 ⟨mem_univ x, hx⟩, h.1⟩,
        fun h => ⟨h.2, fun hx => hx.2 h.1⟩⟩
    rw [hset]
    exact le_antisymm (le_of_le_of_eq ((setLIntegral_one _).symm.le.trans
      (setLIntegral_mono' (hZo.measurableSet.inter R.measurableSet_carrier) fun x hx =>
        Nat.one_le_cast.2 (R.mult_pos x hx.2))) h0) zero_le
  /- **Unit-face decomposition of an integer multiplicity current on the `(m+1)`-skeleton**
  (Simon Ch. 6, proof of the deformation theorem 5.1, (26)–(28) and (33)).  Let `Q₀ = τ(M, θ, ξ)` in
  `ℝᴾ`, `n = m + 1`, with `spt Q₀ ⊆ K` compact and `spt Q₀ ⊆ L_n`.  The faces `p = (ι, b)` whose
  closed face `Φ_p([0,1]ⁿ)` meets `spt Q₀` form a finite set `s`, and distinct open faces
  `F̆_p = Φ_p((0,1)ⁿ)` are disjoint Borel sets (`Φ_p` is an isometry).  `M ∖ ⋃_{p ∈ s} F̆_p` lies in
  `(M ∖ spt Q₀) ∪ L_m`, which is `Hⁿ`-null: off `L_m`, a point of `spt Q₀ ⊆ L_n` lies on an open
  face.  On each face `face_density` gives an integer density `u_p` with
  `∫_{M ∩ F̆_p} θ ⟨ω, ξ⟩ dHⁿ = ∫_{(0,1)ⁿ} u_p(y) ω(Φ_p y)(E_p) dy` and `∫ |u_p| ≤ μ(F̆_p)`,
  `μ = θ Hⁿ⌞M`.  Summing over the disjoint faces gives the representation of `Q₀(ω)`, and
  `Σ_p ∫ |u_p| ≤ μ(ℝᴾ) = M(Q₀)` by the mass hypothesis (MR). -/
  have cmcdtfr_skeleton_decomposition : ∀ (P m : ℕ) (K : Set (Euclid P)) (Q₀ : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)), IsCompact K → IsIntegerMultiplicity Q₀ → Q₀.support ⊆ K → Q₀.support ⊆ {x : Euclid P | ∃ s : Finset (Fin P), P ≤ m + 1 + s.card ∧ ∀ i ∈ s, ∃ z : ℤ, x i = z} → ∃ (s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ))) (u : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → ℝ), (∀ p ∈ s, StrictMono p.1) ∧ (∀ p ∈ s, ∀ y, ∃ z : ℤ, u p y = z) ∧ (∀ p ∈ s, IntegrableOn (u p) {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid (m + 1)))) ∧ ENNReal.ofReal (∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |u p y|) ≤ Q₀.mass ∧ (∀ p ∈ s, ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) ∈ Q₀.support) ∧ ∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), Q₀ ω = ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, u p y * ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ)) := by
    clear cmcdtfrfg_cube_volume cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfr_finite_family dfmf_face_imrep hVO hIMC
    intro P m K Q₀ hK hQ₀ hQK hQL
    -- Step 1: an integer multiplicity representation `R = (M, θ, ξ)` of `Q₀`
    obtain ⟨R, hR⟩ := hQ₀
    -- the face maps `Φ_p(y) = b + Σⱼ yⱼ e_{ι(j)}` and the open unit cube `Q₁`
    let Φ : (Fin (m + 1) → Fin P) × (Fin P → ℤ) → Euclid (m + 1) → Euclid P := fun p y =>
      HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))
    let Q₁ : Set (Euclid (m + 1)) := {y | ∀ i, 0 < y i ∧ y i < 1}
    -- Step 8: `Φ_p` is an isometry (`face_geometry` (a)), so the open face `F̆_p = Φ_p(Q₁)` is Borel
    have hiso : ∀ p : (Fin (m + 1) → Fin P) × (Fin P → ℤ), StrictMono p.1 → Isometry (Φ p) :=
      fun p hp => Isometry.of_dist_eq ((cmcdtfr_face_geometry P (m + 1)).2 p p hp hp).1
    have hQ₁ : MeasurableSet Q₁ := dfmf_cube_meas (m + 1)
    clear dfmf_cube_meas
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
        ((cmcdtfr_face_geometry P (m + 1)).2 p q hp hq).2.2 hpq y y' hy
          fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩
      rw [hyy', dist_self] at h
      rcases h with h | ⟨j, hj⟩
      · exact absurd h (by norm_num)
      · obtain ⟨hy₀, hy₁⟩ := hy j
        exact absurd hj (not_le.mpr (lt_min hy₀ (by linarith)))
    -- Step 5: the finite set `s` of faces `p` whose closed face meets `spt Q₀ ⊆ K`
    clear cmcdtfr_face_geometry
    obtain ⟨s, hs⟩ : ∃ s : Finset ((Fin (m + 1) → Fin P) × (Fin P → ℤ)), ∀ p, p ∈ s ↔
        StrictMono p.1 ∧ ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support := by
      have hfin : {p : (Fin (m + 1) → Fin P) × (Fin P → ℤ) | StrictMono p.1 ∧
          ∃ y : Euclid (m + 1), (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ Φ p y ∈ Q₀.support}.Finite :=
        (cmcdtfrsd_faces_meeting_compact_finite P (m + 1) K hK).subset
          fun p ⟨_, y, hy, hyQ⟩ => ⟨y, hy, hQK hyQ⟩
      exact ⟨hfin.toFinset, fun p => hfin.mem_toFinset⟩
    -- Steps 9–11: the integer densities `u_p` on the faces (`face_density`)
    clear cmcdtfrsd_faces_meeting_compact_finite
    choose! u hu_int hu_integ hu_mass hu_rep using fun p (hp : StrictMono p.1) =>
      cmcdtfrsd_face_density P (m + 1) R p hp (hiso p hp)
    clear cmcdtfrsd_face_density
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
          (dfmf_carrier_sdiff_support_null P (m + 1) Q₀ R hR)
          (cmcdtfr_skeleton_null P m))
        rintro x ⟨hxM, hx⟩
        by_cases hxS : x ∈ Q₀.support
        · -- `x ∈ spt Q₀ ⊆ L_{m+1}`; off `L_m` it lies on an open face `F̆_p` with `p ∈ s`
          refine Or.inr (by_contra fun hxL => ?_)
          obtain ⟨p, y, hp, hy, rfl⟩ :=
            cmcdtfrsd_skeleton_point_on_open_face P m _ (hQL hxS) hxL
          exact hx (mem_iUnion₂.2 ⟨p, (hs p).2 ⟨hp, y, fun i => ⟨(hy i).1.le, (hy i).2.le⟩, hxS⟩,
            hxM, y, hy, rfl⟩)
        · exact Or.inl ⟨hxM, hxS⟩
      have hae : R.carrier =ᵐ[μHE[m + 1]] ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁) := by
        refine ae_eq_set.2 ⟨hnull, ?_⟩
        rw [Set.sdiff_eq_empty.2 (iUnion₂_subset fun p _ => inter_subset_left), measure_empty]
      -- Step 12: split `Q₀(ω) = ∫_M θ ⟨ω, ξ⟩ dHⁿ` over the disjoint faces and change variables
      calc Q₀ ω = ∫ x in R.carrier,
            (R.mult x : ℝ) * R.orient x (ω.1 x) ∂μHE[m + 1] :=
            hR ω
        _ = ∫ x in ⋃ p ∈ s, (R.carrier ∩ Φ p '' Q₁),
            (R.mult x : ℝ) * R.orient x (ω.1 x) ∂μHE[m + 1] :=
            setIntegral_congr_set hae
        _ = ∑ p ∈ s, ∫ x in R.carrier ∩ Φ p '' Q₁,
            (R.mult x : ℝ) * R.orient x (ω.1 x) ∂μHE[m + 1] :=
            integral_biUnion_finset s
              (fun p hp => R.measurableSet_carrier.inter (hF p ((hs p).1 hp).1))
              (fun p hp q hq hpq => (hdisj p q ((hs p).1 hp).1 ((hs q).1 hq).1 hpq).mono
                inter_subset_right inter_subset_right)
              fun p hp => (hu_rep p ((hs p).1 hp).1 ω).1
        _ = _ := Finset.sum_congr rfl fun p hp => (hu_rep p ((hs p).1 hp).1 ω).2
  clear dfmf_cube_meas cmcdtfrsd_faces_meeting_compact_finite cmcdtfr_skeleton_null cmcdtfrsd_face_density cmcdtfrsd_skeleton_point_on_open_face dfmf_carrier_sdiff_support_null
  /- **Integer polyhedral chains are integer multiplicity** (Simon Ch. 6, 3.2(1) and §5): for
  strictly increasing faces `p ∈ s` and integers `β_p`, `Σ_p β_p [[F̆_p]]` is represented by an
  integer multiplicity triple `R`, built by induction on `s` from the triples of the single faces
  (`dfmf_face_imrep`) with the integer-combination lemmas `rsdic_exists_imrep_int_combination`,
  `rsdic_imrep_action_int_combination`.  Moreover `θ ⟨α, ξ⟩ 1_M = Σ_p β_p ⟨α, e_p⟩ 1_{F̆_p}` a.e. -/
  have dfmf_chain_imrep : ∀ (P k : ℕ) (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ), (∀ p ∈ s, StrictMono p.1) → ∃ R : IMRep (univ : Set (Euclid P)) k, (∀ ω : TestFormOn (univ : Set (Euclid P)) k, R.action ω.1 = ∑ p ∈ s, (β p : ℝ) * ∫ y : Euclid k in {y | ∀ i, 0 < y i ∧ y i < 1}, ω.1 (HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) ∧ ∀ᵐ x ∂μHE[k], ∀ α : Covector (Euclid P) k, R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y α) x = ∑ p ∈ s, (β p : ℝ) * ((fun y : Euclid k => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}).indicator (fun _ => α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) x := by
    clear cmcdtfrfg_cube_volume cmcdtfr_face_geometry cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfr_finite_family cmcdtfr_skeleton_decomposition hVO hMR hIMC
    intro P k s β hs
    -- evaluation commutes with indicators
    have hev : ∀ (S : Set (Euclid P)) (f : Euclid P → MultiVector P k) (x : Euclid P)
        (α : Covector (Euclid P) k), S.indicator f x α = S.indicator (fun y => f y α) x := by
      intro S f x α
      by_cases hx : x ∈ S
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_apply]
    induction s using Finset.induction_on with
    | empty =>
      -- the empty triple
      refine ⟨{ carrier := ∅
                mult := fun _ => 0
                orient := fun _ => 0
                measurableSet_carrier := MeasurableSet.empty
                carrier_subset := empty_subset _
                rectifiable :=
                  Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
                measurable_mult := measurable_const
                mult_pos := fun _ h => absurd h (notMem_empty _)
                locallyIntegrable_mult := fun K _ _ => by
                  rw [empty_inter, Measure.restrict_empty, lintegral_zero_measure]
                  exact ENNReal.zero_ne_top
                aestronglyMeasurable_orient := aestronglyMeasurable_const
                orients := by rw [Measure.restrict_empty, ae_zero]; exact Filter.eventually_bot },
        fun ω => ?_, ae_of_all _ fun x α => ?_⟩
      · exact setIntegral_empty.trans Finset.sum_empty.symm
      · rw [indicator_of_notMem (notMem_empty x), Finset.sum_empty]
    | insert p s hp ih =>
      obtain ⟨R, hRa, hRi⟩ := ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
      obtain ⟨Rp, hRpc, hRpm, hRpo, -, hRpa⟩ :=
        dfmf_face_imrep P k p (hs p (Finset.mem_insert_self p s))
      -- `R' = 1 · R + β_p · R_p`
      obtain ⟨R', hR'⟩ :=
        Submission.rsdic_exists_imrep_int_combination P k univ R Rp 1 (β p) isOpen_univ
      refine ⟨R', fun ω => ?_, ?_⟩
      · rw [Submission.rsdic_imrep_action_int_combination P k univ R Rp R' 1 (β p) hR' ω, hRa ω,
          hRpa ω, Finset.sum_insert hp, Int.cast_one, one_mul, add_comm]
      · filter_upwards [hR', hRi] with x hx hxi α
        have h := congrArg (fun T : MultiVector P k => T α) hx
        simp only [add_apply, smul_apply, hev,
          smul_eq_mul, Int.cast_one, one_mul] at h
        rw [Finset.sum_insert hp, ← hxi α, ← hRpc]
        refine (show _ = _ from h).trans ?_
        rw [add_comm]
        congr 1
        congr 1
        by_cases hxp : x ∈ Rp.carrier
        · rw [indicator_of_mem hxp, indicator_of_mem hxp, hRpm, hRpo, Nat.cast_one, one_mul]
        · rw [indicator_of_notMem hxp, indicator_of_notMem hxp]
  /- **A nonzero integer polyhedral chain has mass `≥ 1`** (Simon Ch. 6, §5, after (38)).  If `R`
  satisfies `θ ⟨α, ξ⟩ 1_M = Σ_p β_p ⟨α, e_p⟩ 1_{F̆_p}` a.e. and `β_q ≠ 0`, then testing with
  `α = dx^{ι_q}` (`α(e_q) = 1`) shows that a.e. point of `F̆_q` lies in `M` (the open faces are
  disjoint, `cmcdtfr_face_geometry`), and `θ ≥ 1` on `M`; so
  `μ_R(ℝᴾ) ≥ ∫_{F̆_q} θ 1_M dHᵏ ≥ Hᵏ(F̆_q) = 1`. -/
  have dfmf_chain_mass_ge : ∀ (P k : ℕ) (s : Finset ((Fin k → Fin P) × (Fin P → ℤ))) (β : (Fin k → Fin P) × (Fin P → ℤ) → ℤ) (R : IMRep (univ : Set (Euclid P)) k), (∀ p ∈ s, StrictMono p.1) → (∀ᵐ x ∂μHE[k], ∀ α : Covector (Euclid P) k, R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y α) x = ∑ p ∈ s, (β p : ℝ) * ((fun y : Euclid k => HAdd.hAdd (WithLp.toLp 2 (fun i => (p.2 i : ℝ))) (∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ))) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1}).indicator (fun _ => α (fun j => EuclideanSpace.single (p.1 j) (1 : ℝ))) x) → ∀ q ∈ s, β q ≠ 0 → 1 ≤ R.measure univ := by
    clear cmcdtfrfg_cube_volume dfmf_support_boundary_subset cmcdtfr_boundary_variation cmcdtfr_chain_boundary cmcdtfr_face_integral_current cmcdtfr_finite_family cmcdtfr_skeleton_decomposition dfmf_chain_imrep hVO hMR hIMC
    intro P k s β R hs hR q hq hβq
    -- the coordinate covector `θ = dx^{ι_q}`, `θ(e_{ι_q}) = 1`
    obtain ⟨θ, hθ⟩ := cmr_cc_det_covector_exists P k q.1
    clear cmr_cc_det_covector_exists
    have hθ1 : θ (fun j => EuclideanSpace.single (q.1 j) (1 : ℝ)) = 1 := by
      have h := cmr_cc_det_covector_basis_kronecker P k q.1 q.1 θ (hs q hq) (hs q hq) hθ
      rw [ite_eq_left rfl] at h
      simpa only [EuclideanSpace.basisFun_apply] using h
    -- the open face `F̆_q` (`Hᵏ(F̆_q) = 1`), disjoint from the other open faces
    clear cmr_cc_det_covector_basis_kronecker
    obtain ⟨Rq, hRqc, -, -, hRq1, -⟩ := dfmf_face_imrep P k q (hs q hq)
    clear dfmf_face_imrep
    have hdisj : ∀ p ∈ s, p ≠ q → ∀ x ∈ Rq.carrier,
        x ∉ (fun y : Euclid k => WithLp.toLp 2 (fun i => (p.2 i : ℝ)) +
          ∑ j, y j • EuclideanSpace.single (p.1 j) (1 : ℝ)) '' {y : Euclid k | ∀ i, 0 < y i ∧ y i < 1} := by
      intro p hp hpq x hx hxp
      rw [hRqc] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', hyy'⟩ := hxp
      beta_reduce at hyy'
      rcases ((cmcdtfr_face_geometry P k).2 q p (hs q hq) (hs p hp)).2.2 (Ne.symm hpq) y y'
          hy (fun i => ⟨(hy' i).1.le, (hy' i).2.le⟩) with h | ⟨j, hj⟩
      · rw [hyy', dist_self] at h
        exact absurd h (by norm_num)
      · rw [hyy', dist_self] at hj
        exact absurd hj (not_le.2 (lt_min (hy j).1 (sub_pos.2 (hy j).2)))
    -- a.e. point of `F̆_q` lies in `M`: there `θ ⟨dx^{ι_q}, ξ⟩ 1_M = β_q ≠ 0`
    clear cmcdtfr_face_geometry
    have hae : ∀ᵐ x ∂(μHE[k].restrict Rq.carrier), x ∈ R.carrier := by
      filter_upwards [ae_restrict_of_ae hR, ae_restrict_mem Rq.measurableSet_carrier] with x hx hxq
      by_contra hxM
      have h := hx θ
      rw [indicator_of_notMem hxM, Finset.sum_eq_single q (fun p hp hpq => by
          rw [indicator_of_notMem (hdisj p hp hpq x hxq), mul_zero]) (fun h => absurd hq h)] at h
      rw [hRqc] at hxq
      rw [indicator_of_mem hxq, hθ1, mul_one] at h
      exact hβq (Int.cast_eq_zero.1 h.symm)
    -- `μ_R(ℝᴾ) ≥ μ_R(F̆_q) = ∫_{F̆_q} θ 1_M dHᵏ ≥ Hᵏ(F̆_q) = 1`
    calc (1 : ℝ≥0∞) = ∫⁻ _ in Rq.carrier, 1 ∂μHE[k] := by rw [setLIntegral_one, hRq1]
      _ ≤ ∫⁻ x in Rq.carrier, R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x ∂μHE[k] := by
          refine lintegral_mono_ae (hae.mono fun x hxM => ?_)
          rw [indicator_of_mem hxM]
          exact Nat.one_le_cast.2 (R.mult_pos x hxM)
      _ = R.measure Rq.carrier := by
          rw [lintegral_indicator R.measurableSet_carrier, IMRep.measure,
            withDensity_apply _ Rq.measurableSet_carrier,
            Measure.restrict_restrict R.measurableSet_carrier,
            Measure.restrict_restrict Rq.measurableSet_carrier, inter_comm]
      _ ≤ R.measure univ := measure_mono (subset_univ _)
  clear cmr_cc_det_covector_basis_kronecker cmr_cc_det_covector_exists dfmf_face_imrep
  -- the assembly (Simon Ch. 6, 5.1, displays (26)–(37))
  intro P m
  -- support and mass calculus for currents in `ℝᴾ`: `spt(A − B) ⊆ spt A ∪ spt B`,
  -- `spt ∂A ⊆ spt A` and `M(A − B) ≤ M(A) + M(B)`
  have hspt_sub : ∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m,
      (A - B).support ⊆ A.support ∪ B.support := by
    intro A B x hx
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
  have hmass_sub : ∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) m,
      (A - B).mass ≤ A.mass + B.mass := by
    intro A B
    refine sSup_le ?_
    rintro _ ⟨ω, hω, rfl⟩
    have h2 : ENNReal.ofReal (B (-ω)) ≤ B.mass := B.le_massOn
      ⟨subset_univ _, fun x => (covectorEuclideanNorm_neg _).trans_le (hω.2 x)⟩
    rw [map_neg B.toCurrent ω] at h2
    exact (ENNReal.ofReal_le_ofReal (sub_eq_add_neg _ _).le).trans
      (ENNReal.ofReal_add_le.trans (add_le_add (A.le_massOn hω) h2))
  -- `c_B` from the cube BV median lemma and `c := max(2, 1 + c_B)`
  obtain ⟨cB, hcB, hmedian⟩ := Submission.dtc_bc_tc_cl_dfm_cube_bv_median m
  refine ⟨Real.toNNReal (max 2 (1 + cB)),
    Real.one_le_toNNReal.2 (le_max_of_le_left one_le_two), fun K Λ hK => ?_⟩
  -- `𝒬₀`: the integer chains `Σ β_F [[F]]` on faces meeting `K` with `Σ|β_F| ≤ 2Λ`
  refine ⟨_, cmcdtfr_finite_family P (m + 1) K (2 * (Λ : ℝ)) hK, ?_⟩
  intro Q₀ hQ₀ hQ₀K hQ₀L hQ₀Λ hQ₀b
  -- `Q₀ = Σ_F ũ_F [[F̆]]` over the open faces `F̆` meeting `spt Q₀`
  obtain ⟨s, u, hs, huZ, huI, hSu, huspt, hQ₀rep⟩ :=
    cmcdtfr_skeleton_decomposition P m K Q₀ hK hQ₀ hQ₀K hQ₀L
  -- the variations `V_F` of the `ũ_F`, with `Σ_F V_F ≤ M(∂Q₀)`
  obtain ⟨V, hV0, hSV, hVbd, hVspt⟩ :=
    cmcdtfr_boundary_variation P m s u Q₀ hs huI hQ₀rep hQ₀b
  -- integer medians `β_F` of the `ũ_F` (`cube_bv_median`)
  choose! β hβ using fun p (hp : p ∈ s) => hmedian (u p) (V p) (huZ p hp) (huI p hp) (hVbd p hp)
  -- the face currents with densities `β_F` (this is `Pc`), `ũ_F` and `ũ_F − β_F`
  have hcube := cmcdtfrfg_cube_volume (m + 1)
  have hβI : ∀ p ∈ s, IntegrableOn (fun _ : Euclid (m + 1) => (β p : ℝ))
      {y | ∀ i, 0 < y i ∧ y i < 1} (volume : Measure (Euclid (m + 1))) := fun p _ =>
    integrableOn_const (hcube.trans_ne ENNReal.one_ne_top) enorm_ne_top
  -- `Pc = Σ_F β_F [[F]]`: the current of the integer multiplicity triple of `Σ_F β_F [[F]]`
  obtain ⟨RP, hRPact, hRPind⟩ := dfmf_chain_imrep P (m + 1) s β hs
  obtain ⟨Pc, hPc⟩ := Submission.dtc_imrep_current P (m + 1) univ RP
  have hPcrep := fun ω => (hPc ω).trans (hRPact ω)
  -- the face currents with densities `β_F`, `ũ_F` and `ũ_F − β_F`
  have hβD := cmcdtfr_face_integral_current P m s (fun p _ => (β p : ℝ)) hs hβI
  have huω := (cmcdtfr_face_integral_current P m s u hs huI).1
  have hdD := (cmcdtfr_face_integral_current P m s
    (fun p y => u p y - (β p : ℝ)) hs fun p hp => (huI p hp).sub (hβI p hp)).2
  -- `Pc = 0`, or some `β_F ≠ 0` and `M(Pc) = μ_RP(ℝᴾ) ≥ 1` by (MR) (`dfmf_chain_mass_ge`)
  have hPc01 : Pc = 0 ∨ 1 ≤ Pc.mass := by
    by_cases h : ∃ q ∈ s, β q ≠ 0
    · obtain ⟨q, hq, hβq⟩ := h
      exact Or.inr ((dfmf_chain_mass_ge P (m + 1) s β RP hs hRPind q hq hβq).trans_eq
        (hMR P (m + 1) univ Pc RP isOpen_univ hPc univ isOpen_univ).symm)
    · refine Or.inl (GeometricCurrentOn.ext fun ω => ?_)
      rw [hPcrep ω, GeometricCurrentOn.zero_apply]
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [show β p = 0 from not_not.1 fun hβ => h ⟨p, hp, hβ⟩, Int.cast_zero, zero_mul]
  -- integrality of `∂Pc` (cubical Stokes)
  obtain ⟨s', β', hs', hPcbrep⟩ := cmcdtfr_chain_boundary P m s β Pc hs hPcrep
  obtain ⟨RB, hRBact, -⟩ := dfmf_chain_imrep P m s' β' hs'
  have hPcbIM : IsIntegerMultiplicity Pc.boundary :=
    ⟨RB, fun γ => (hPcbrep γ).trans (hRBact γ).symm⟩
  -- mass and support bounds for `Pc` and `Q₀ − Pc` from their face densities
  have hPcD := hβD.2 Pc fun ω =>
    (hPcrep ω).trans (Finset.sum_congr rfl fun p _ => (integral_const_mul _ _).symm)
  -- `M(Pc) ≤ Σ_F ∫_{Q₁} |β_F| = Σ_F |β_F|`
  have hPcmass : Pc.mass ≤ ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := by
    refine hPcD.1.trans_eq (congrArg ENNReal.ofReal (Finset.sum_congr rfl fun p _ => ?_))
    rw [setIntegral_const, measureReal_def, hcube, ENNReal.toReal_one, one_smul]
  -- `Q₀ − Pc = Σ_F (ũ_F − β_F) [[F̆]]`
  have hdD' := hdD (Q₀ - Pc) fun ω => by
    show Q₀ ω - Pc ω = _
    rw [hQ₀rep ω, hPcrep ω, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← integral_const_mul, ← integral_sub (huω ω p hp) (hβD.1 ω p hp)]
    exact integral_congr_ae (ae_of_all _ fun y => (sub_mul _ _ _).symm)
  have hdb := hdD'.2.1 (fun p => cB * V p) fun p hp G hG hG1 => (hβ p hp).2.2 G hG hG1
  -- `Σ|β_F| ≤ 2 Σ_F ∫|ũ_F| ≤ 2Λ`, `Σ_F ∫|ũ_F − β_F| ≤ c_B Σ_F V_F`
  have hβsum : ∑ p ∈ s, |(β p : ℝ)| ≤
      2 * ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |u p y| := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hβ p hp).2.1
  have hSuΛ : ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1}, |u p y| ≤
      (Λ : ℝ) := by
    have h := hSu.trans hQ₀Λ
    rw [← ENNReal.ofReal_coe_nnreal] at h
    exact (ENNReal.ofReal_le_ofReal_iff Λ.coe_nonneg).1 h
  have hdsum : ∑ p ∈ s, ∫ y : Euclid (m + 1) in {y | ∀ i, 0 < y i ∧ y i < 1},
      |u p y - (β p : ℝ)| ≤ cB * ∑ p ∈ s, V p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p hp => (hβ p hp).1
  have hdb' : (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal cB * Q₀.boundary.mass := by
    calc (Q₀ - Pc).boundary.mass ≤ ENNReal.ofReal (∑ p ∈ s, cB * V p) := hdb
      _ = ENNReal.ofReal cB * ENNReal.ofReal (∑ p ∈ s, V p) := by
          rw [← Finset.mul_sum, ENNReal.ofReal_mul hcB.le]
      _ ≤ ENNReal.ofReal cB * Q₀.boundary.mass := mul_le_mul' le_rfl hSV
  -- `∂Pc = ∂Q₀ − ∂(Q₀ − Pc)`
  have hPcb_eq : Pc.boundary = Q₀.boundary - (Q₀ - Pc).boundary :=
    GeometricCurrentOn.ext fun γ => (sub_sub_cancel _ _).symm
  -- supports: a face carrying `Pc` meets `spt Q₀`, a face carrying `Q₀ − Pc` meets `spt ∂Q₀`
  -- (there `V_F ≠ 0`), and a face has diameter `≤ √P`
  have hdiam := fun p (hp : p ∈ s) =>
    ((cmcdtfr_face_geometry P (m + 1)).2 p p (hs p hp) (hs p hp)).2.1
  have hPcsupp : Pc.support ⊆ cthickening (Real.sqrt P) Q₀.support := by
    intro x hx
    obtain ⟨p, hp, -, y, hy, rfl⟩ := hPcD.2.2 x hx
    obtain ⟨y', hy', hy'Q⟩ := huspt p hp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  have hdsupp : (Q₀ - Pc).support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
    intro x hx
    obtain ⟨p, hp, hne, y, hy, rfl⟩ := hdD'.2.2 x hx
    have hVp : V p ≠ 0 := fun h0 => hne (le_antisymm ((hβ p hp).1.trans_eq
      (by rw [h0, mul_zero])) (integral_nonneg fun y => abs_nonneg _))
    obtain ⟨y', hy', hy'Q⟩ := hVspt p hp hVp
    exact mem_cthickening_of_dist_le _ _ _ _ hy'Q (hdiam p hp y y' hy hy')
  have hPcbsupp : Pc.boundary.support ⊆ cthickening (Real.sqrt P) Q₀.boundary.support := by
    intro x hx
    rw [hPcb_eq] at hx
    rcases hspt_sub _ _ hx with h | h
    · exact self_subset_cthickening _ h
    · exact hdsupp (dfmf_support_boundary_subset P m _ h)
  refine ⟨Pc, ?_, ⟨RP, hPc⟩, hPcbIM, hPc01, ?_, ?_, ?_, hPcsupp, union_subset hdsupp hPcbsupp⟩
  · -- `Pc ∈ 𝒬₀`
    rw [Set.mem_ofPred_eq]
    refine ⟨s, β, hs, fun p hp => ?_, hβsum.trans (mul_le_mul_of_nonneg_left hSuΛ zero_le_two),
      hPcrep⟩
    obtain ⟨y, hy, hyQ⟩ := huspt p hp
    exact ⟨y, hy, hQ₀K hyQ⟩
  · -- `M(Pc) ≤ Σ|β_F| ≤ 2M(Q₀)`
    show Pc.mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.mass
    calc Pc.mass ≤ ENNReal.ofReal (∑ p ∈ s, |(β p : ℝ)|) := hPcmass
      _ ≤ ENNReal.ofReal (2 * _) := ENNReal.ofReal_le_ofReal hβsum
      _ = ENNReal.ofReal 2 * ENNReal.ofReal _ := ENNReal.ofReal_mul zero_le_two
      _ ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) hSu
  · -- `M(∂Pc) ≤ M(∂Q₀) + M(∂(Q₀ − Pc)) ≤ (1 + c_B)M(∂Q₀)`
    show Pc.boundary.mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass
    rw [hPcb_eq]
    calc _ ≤ Q₀.boundary.mass + ENNReal.ofReal cB * Q₀.boundary.mass :=
          (hmass_sub _ _).trans (add_le_add le_rfl hdb')
      _ = ENNReal.ofReal (1 + cB) * Q₀.boundary.mass := by
          rw [ENNReal.ofReal_add zero_le_one hcB.le, ENNReal.ofReal_one, add_mul, one_mul]
      _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  · -- `M(Q₀ − Pc) ≤ Σ_F ∫|ũ_F − β_F| ≤ c_B M(∂Q₀)`
    show (Q₀ - Pc).mass ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass
    calc (Q₀ - Pc).mass ≤ ENNReal.ofReal _ := hdD'.1
      _ ≤ ENNReal.ofReal (cB * ∑ p ∈ s, V p) := ENNReal.ofReal_le_ofReal hdsum
      _ = ENNReal.ofReal cB * ENNReal.ofReal (∑ p ∈ s, V p) := ENNReal.ofReal_mul hcB.le
      _ ≤ ENNReal.ofReal (max 2 (1 + cB)) * Q₀.boundary.mass :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal
            ((le_add_of_nonneg_left zero_le_one).trans (le_max_right _ _))) hSV

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
