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

/-- **Simon, proof of A.4** (the rescaled secants): if `S ∩ B_σ(0)` is infinite for some `σ < 1`,
there are `x` with `|x| < 1`, scales `λ_k ↓ 0` with `λ_k < 1` and `|x| ≤ 1 − λ_k`, and points
`z_k → z` with `|z_k| = |z| = 1/2` and `x + λ_k z_k ∈ S`.  Distinct points of `S ∩ B_σ(0)`
subconverge to some `x ∈ B̄_σ(0)`; a tail `q_k ∈ S \ {x}` still tends to `x`, so the scales
`λ = 2|q − x| > 0` tend to `0` and are made strictly decreasing and `≤ (1 − |x|)/2` along
inductively chosen indices; the secants `(q − x)/λ` lie on the compact sphere `|w| = 1/2`, so a
further subsequence converges. -/
theorem Submission.adr_secant_rescaling_of_infinite : ∀ (P : ℕ) (S : Set (Euclid P)) (σ : ℝ), σ < 1 → (S ∩ ball (0 : Euclid P) σ).Infinite → ∃ (x : Euclid P) (lams : ℕ → ℝ) (zs : ℕ → Euclid P) (z : Euclid P), ‖x‖ < 1 ∧ (∀ k, 0 < lams k) ∧ StrictAnti lams ∧ Tendsto lams atTop (𝓝 0) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ (∀ k, x + lams k • zs k ∈ S) ∧ (∀ k, ‖zs k‖ = 1 / 2) ∧ Tendsto zs atTop (𝓝 z) ∧ ‖z‖ = 1 / 2 := by
  intro P S σ hσ hinf
  -- pairwise distinct points `p k ∈ S ∩ B_σ(0)`
  let e := Set.Infinite.natEmbedding _ hinf
  let p : ℕ → Euclid P := fun k => (e k : Euclid P)
  have hp : Injective p := Subtype.val_injective.comp e.injective
  -- a subsequence `p ∘ m` converges to some `x ∈ B̄_σ(0)`, so `|x| ≤ σ < 1`
  obtain ⟨x, hxσ, m, hm, hpx⟩ := (isCompact_closedBall (0 : Euclid P) σ).tendsto_subseq
    fun k => ball_subset_closedBall (e k).2.2
  have hx : ‖x‖ < 1 := (mem_closedBall_zero_iff.mp hxσ).trans_lt hσ
  -- by injectivity at most one `p (m j)` equals `x`, so a tail `q k = p (m (k + j₁))` avoids `x`
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, ∀ j ≥ j₁, p (m j) ≠ x := by
    by_cases h : ∃ j₀, p (m j₀) = x
    · obtain ⟨j₀, hj₀⟩ := h
      exact ⟨j₀ + 1, fun j hj hjx => (hm (Nat.lt_of_succ_le hj)).ne' (hp (hjx.trans hj₀.symm))⟩
    · push Not at h
      exact ⟨0, fun j _ => h j⟩
  let q : ℕ → Euclid P := fun k => p (m (k + j₁))
  have hqS : ∀ k, q k ∈ S := fun k => (e (m (k + j₁))).2.1
  have hqx : ∀ k, ‖q k - x‖ ≠ 0 := fun k =>
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hj₁ _ (Nat.le_add_left _ _)))
  have hq : Tendsto q atTop (𝓝 x) := hpx.comp (tendsto_add_atTop_nat j₁)
  -- the scales `a k = 2|q k − x|` are positive and tend to `0`
  let a : ℕ → ℝ := fun k => 2 * ‖q k - x‖
  have ha : ∀ k, 0 < a k := fun k => mul_pos two_pos ((norm_nonneg _).lt_of_ne' (hqx k))
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have h := (tendsto_iff_norm_sub_tendsto_zero.mp hq).const_mul 2
    rwa [mul_zero] at h
  -- indices `ks j` with `a (ks 0) ≤ (1 − |x|)/2` along which `a` strictly decreases
  obtain ⟨k₀, hk₀⟩ := (ha0.eventually (ge_mem_nhds (half_pos (sub_pos.mpr hx)))).exists
  have hnext : ∀ k, ∃ k', k < k' ∧ a k' < a k := fun k =>
    ((eventually_gt_atTop k).and (ha0.eventually (gt_mem_nhds (ha k)))).exists
  choose nxt hnxt using hnext
  let ks : ℕ → ℕ := fun j => Nat.rec (motive := fun _ => ℕ) k₀ (fun _ kj => nxt kj) j
  have hks : StrictMono ks := strictMono_nat_of_lt_succ fun j => (hnxt (ks j)).1
  have haks : StrictAnti (a ∘ ks) := strictAnti_nat_of_succ_lt fun j => (hnxt (ks j)).2
  have haks_le : ∀ j, a (ks j) ≤ (1 - ‖x‖) / 2 := fun j =>
    (haks.antitone (Nat.zero_le j)).trans hk₀
  -- the rescaled secants `w j = (q (ks j) − x)/a (ks j)` lie on the sphere `|w| = 1/2`
  let w : ℕ → Euclid P := fun j => (a (ks j))⁻¹ • (q (ks j) - x)
  have hw : ∀ j, ‖w j‖ = 1 / 2 := fun j => by
    change ‖(2 * ‖q (ks j) - x‖)⁻¹ • (q (ks j) - x)‖ = 1 / 2
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (ha _).le, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hqx _), mul_one, one_div]
  obtain ⟨z, hz, ψ, hψ, hwz⟩ := (isCompact_sphere (0 : Euclid P) (1 / 2)).tendsto_subseq
    fun j => mem_sphere_zero_iff_norm.mpr (hw j)
  refine ⟨x, fun i => a (ks (ψ i)), fun i => w (ψ i), z, hx, fun i => ha _,
    haks.comp_strictMono hψ, ha0.comp (hks.comp hψ).tendsto_atTop, fun i => ?_, fun i => ?_,
    fun i => ?_, fun i => hw _, hwz, mem_sphere_zero_iff_norm.mp hz⟩
  · linarith [haks_le (ψ i), norm_nonneg x]
  · linarith [haks_le (ψ i)]
  · change x + a (ks (ψ i)) • (a (ks (ψ i)))⁻¹ • (q (ks (ψ i)) - x) ∈ S
    rw [smul_inv_smul₀ (ha _).ne', add_sub_cancel]
    exact hqS _
/-- **Radial segment** (Simon, proof of A.4: `H¹(sing ψ ∩ B_1(0)) > 0`).  If `S` contains the
radial segment `{t z : 0 < t ≤ 1}`, where `z ≠ 0` and `|z| < 1`, then `μH[1](S ∩ B_1(0)) > 0`:
the closed segment `[z / 2, z]` lies in `S ∩ B_1(0)`, its endpoints differ, and its
`μH[1]`-measure is the distance between them (`hausdorffMeasure_segment`). -/
theorem Submission.adr_radial_segment_hausdorff_pos : ∀ (P : ℕ) (S : Set (Euclid P)) (z : Euclid P), z ≠ 0 → ‖z‖ < 1 → (∀ t : ℝ, 0 < t → t ≤ 1 → t • z ∈ S) → 0 < μH[1] (S ∩ ball (0 : Euclid P) 1) := by
  intro P S z hz hz1 hS
  -- a point `α • (z / 2) + β • z` of `[z / 2, z]` is `t • z` with `t = α / 2 + β ∈ (0, 1]`, so it
  -- lies in `S`, and `|t z| ≤ |z| < 1`
  have hsub : segment ℝ ((1 / 2 : ℝ) • z) z ⊆ S ∩ ball (0 : Euclid P) 1 := by
    rintro w ⟨α, β, hα, hβ, hαβ, rfl⟩
    have hw : α • (1 / 2 : ℝ) • z + β • z = (α / 2 + β) • z := by
      rw [smul_smul, ← add_smul, mul_one_div]
    have ht0 : 0 < α / 2 + β := by linarith
    have ht1 : α / 2 + β ≤ 1 := by linarith
    rw [hw]
    refine ⟨hS _ ht0 ht1, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg ht0.le]
    calc (α / 2 + β) * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 1 := by rwa [one_mul]
  -- `z / 2 ≠ z`, since otherwise `(1 / 2 - 1) • z = 0` forces `z = 0`
  have hne : (1 / 2 : ℝ) • z ≠ z := by
    intro h
    have h' : ((1 / 2 : ℝ) - 1) • z = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact hz ((smul_eq_zero.mp h').resolve_left (by norm_num))
  calc (0 : ℝ≥0∞) < edist ((1 / 2 : ℝ) • z) z := edist_pos.mpr hne
    _ = μH[1] (segment ℝ ((1 / 2 : ℝ) • z) z) := (hausdorffMeasure_segment _ _).symm
    _ ≤ μH[1] (S ∩ ball (0 : Euclid P) 1) := measure_mono hsub
/-- **Lemma T** (Simon, proof of A.4: limits of singular points are singular).  Let `F` satisfy
A.3c (`sing φ` closed) and A.3(3) (upper semicontinuity of `sing` under weak convergence).  If
`φ_k ∈ F` converge weakly to `ψ ∈ F`, `z_k ∈ B_1(0) ∩ sing φ_k` and `z_k → z`, then `z ∈ sing ψ`:
A.3(3) with `ε / 2` puts each `z_k` with `k` large within `ε / 2` of `sing ψ`, so `z` lies within
`ε` of `sing ψ` for every `ε > 0`, and `sing ψ` is closed. -/
theorem Submission.adr_sing_mem_of_tendsto : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ψ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) → ∀ (zs : ℕ → Euclid P) (z : Euclid P), (∀ k, zs k ∈ ball (0 : Euclid P) 1 ∩ sing (φs k)) → Tendsto zs atTop (𝓝 z) → z ∈ sing ψ := by
  intro P n Q F sing hclosed husc ψ hψ φs hφs hweak zs z hzs hz
  rw [← (hclosed ψ hψ).closure_eq, Metric.mem_closure_iff]
  intro ε hε
  -- A.3(3) with `ε / 2` puts `z_k` within `ε / 2` of `sing ψ` for `k ≥ k₀`
  obtain ⟨k₀, hk₀⟩ := husc ψ hψ φs hφs hweak (ε / 2) (half_pos hε)
  -- `z_k → z` puts `z_k` within `ε / 2` of `z` for `k ≥ k₁`
  obtain ⟨k₁, hk₁⟩ := Metric.tendsto_atTop.mp hz (ε / 2) (half_pos hε)
  obtain ⟨v, hv, hzv⟩ := hk₀ (max k₀ k₁) (le_max_left _ _) (hzs (max k₀ k₁))
  have hz' : dist z (zs (max k₀ k₁)) < ε / 2 := by
    rw [dist_comm]
    exact hk₁ (max k₀ k₁) (le_max_right _ _)
  exact ⟨v, hv, (dist_triangle z (zs (max k₀ k₁)) v).trans_lt
    ((add_lt_add hz' hzv).trans_eq (add_halves ε))⟩
/-- **Simon, proof of A.4** (the uses of A.3(2)): a closed `S ⊆ ℝᴾ` with `{x : y + λx ∈ S} = S`
whenever `y ∈ L`, `0 < λ < 1`, `|y| ≤ 1 − λ` satisfies `y + λz ∈ S ⇔ z ∈ S` for all `y ∈ L`,
`λ > 0`, and contains `L` if it is nonempty.  The admissible maps `z ↦ y + λz` give every
dilation `z ↦ cz` (`c > 1` by inverting `c⁻¹`), hence every short translation `z ↦ a + z`,
`|a| ≤ 1/2` (composing `z ↦ a + z/2` with `z ↦ 2z`), hence every translation along `L`
(conjugating a short one by a dilation); letting `λ ↓ 0` in `y + λz ∈ S` gives `y ∈ S̄ = S`. -/
theorem Submission.adr_affine_invariant_closed_set : ∀ (P : ℕ) (S : Set (Euclid P)) (L : Submodule ℝ (Euclid P)), IsClosed S → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => y + lam • x) ⁻¹' S = S) → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ z, y + lam • z ∈ S ↔ z ∈ S) ∧ (S.Nonempty → (L : Set (Euclid P)) ⊆ S) := by
  intro P S L hS hinv
  -- the hypothesis, pointwise
  have hG : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam →
      ∀ z, y + lam • z ∈ S ↔ z ∈ S := fun y hy lam h0 h1 hy' z =>
    Set.ext_iff.mp (hinv y hy lam h0 h1 hy') z
  -- every dilation `z ↦ c z`, `c > 0`
  have hD : ∀ c : ℝ, 0 < c → ∀ z : Euclid P, c • z ∈ S ↔ z ∈ S := by
    have hD0 : ∀ c : ℝ, 0 < c → c < 1 → ∀ z : Euclid P, c • z ∈ S ↔ z ∈ S := by
      intro c hc hc1 z
      have h := hG 0 L.zero_mem c hc hc1 (by rw [norm_zero]; linarith) z
      rwa [zero_add] at h
    intro c hc z
    rcases lt_trichotomy c 1 with hc1 | rfl | hc1
    · exact hD0 c hc hc1 z
    · rw [one_smul]
    · have h := hD0 c⁻¹ (inv_pos.mpr hc) (inv_lt_one_of_one_lt₀ hc1) (c • z)
      rw [inv_smul_smul₀ hc.ne'] at h
      exact h.symm
  -- short translations `z ↦ a + z`, `a ∈ L`, `‖a‖ ≤ 1/2`
  have hT0 : ∀ a ∈ L, ‖a‖ ≤ 1 / 2 → ∀ z : Euclid P, a + z ∈ S ↔ z ∈ S := by
    intro a ha ha' z
    have h := hG a ha (1 / 2) (by norm_num) (by norm_num) (by linarith) ((2 : ℝ) • z)
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h
    exact h.trans (hD 2 two_pos z)
  -- every translation along `L`: a short one conjugated by a dilation
  have hT : ∀ y ∈ L, ∀ z : Euclid P, y + z ∈ S ↔ z ∈ S := by
    intro y hy z
    have hc : (0 : ℝ) < (2 * ‖y‖ + 1)⁻¹ := by positivity
    have hcy : ‖(2 * ‖y‖ + 1)⁻¹ • y‖ ≤ 1 / 2 := by
      rw [norm_smul, Real.norm_of_nonneg hc.le, ← div_eq_inv_mul, div_le_iff₀ (by positivity)]
      linarith
    rw [← hD _ hc (y + z), smul_add, hT0 _ (L.smul_mem _ hy) hcy, hD _ hc z]
  -- part (i)
  have hi : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ z, y + lam • z ∈ S ↔ z ∈ S :=
    fun y hy lam hlam z => (hT y hy (lam • z)).trans (hD lam hlam z)
  refine ⟨hi, ?_⟩
  -- part (ii): let `λ ↓ 0` in `y + λ z ∈ S`
  rintro ⟨z, hz⟩ y hy
  have hcont : Continuous fun lam : ℝ => y + lam • z := by fun_prop
  have hlim : Tendsto (fun lam : ℝ => y + lam • z) (𝓝[>] 0) (𝓝 y) :=
    (hcont.tendsto' 0 y (by simp)).mono_left nhdsWithin_le_nhds
  exact hS.mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun lam hlam => (hi y hy lam hlam z).mpr hz)
/-- **Simon, Remark A.5** (invariance forces a plane indicator).  If `ψ ∈ L¹_loc(μH[n])` on `ℝᴾ`
satisfies `ψ(y + λx) = ψ(x)` for all `y ∈ L`, `λ > 0`, where `dim L ≥ n`, then
`ψ = ψ(0) 1_{L'}` for an `n`-dimensional subspace `L'` (taken inside `L`).  Off `L'`, at `x ∉ L'`,
`ψ ≡ ψ(x)` on the image of a small closed ball around `(0, 1)` under the injective linear map
`L' × ℝ → ℝᴾ`, `(y, t) ↦ y + t x`; this compact piece of the `(n + 1)`-plane `L' + ℝx` has positive
`μH[n + 1]` measure, hence infinite `μH[n]` measure, so local integrability forces `ψ(x) = 0`. -/
theorem Submission.adr_invariant_eq_indicator : ∀ (P n Q : ℕ) (ψ : Euclid P → Euclid Q) (L : Submodule ℝ (Euclid P)), LocallyIntegrable ψ μH[(n : ℝ)] → n ≤ Module.finrank ℝ L → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → ∃ L' : Submodule ℝ (Euclid P), Module.finrank ℝ L' = n ∧ ψ = Set.indicator (L' : Set (Euclid P)) (fun _ => ψ 0) := by
  intro P n Q ψ L hψ hn hinv
  -- an `n`-dimensional subspace `L' ≤ L`
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank hn
  have hb : LinearIndependent ℝ (L.subtype ∘ f) := hf.map' L.subtype L.ker_subtype
  obtain ⟨L', hL'⟩ : ∃ L' : Submodule ℝ (Euclid P), L' = Submodule.span ℝ (range (L.subtype ∘ f)) :=
    ⟨_, rfl⟩
  have hL'L : L' ≤ L := by
    rw [hL', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).2
  have hL'rank : Module.finrank ℝ L' = n := by
    rw [hL', finrank_span_eq_card hb, Fintype.card_fin]
  refine ⟨L', hL'rank, ?_⟩
  funext v
  by_cases hv : v ∈ L'
  · rw [Set.indicator_of_mem hv]
    simpa using hinv v (hL'L hv) 1 one_pos 0
  · rw [Set.indicator_of_notMem hv]
    -- the injective linear map `g (y, t) = y + t • v` on `L' × ℝ`
    let g : (L' × ℝ) →ₗ[ℝ] Euclid P :=
      L'.subtype.coprod (LinearMap.toSpanSingleton ℝ (Euclid P) v)
    have hg : ∀ p : L' × ℝ, g p = (p.1 : Euclid P) + p.2 • v := fun p => rfl
    have hker : LinearMap.ker g = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨y, t⟩ h
      rw [hg] at h
      by_cases ht : t = 0
      · subst ht
        simp only [zero_smul, add_zero, ZeroMemClass.coe_eq_zero] at h
        simp [h]
      · exfalso
        apply hv
        have h' : t • v = -(y : Euclid P) := eq_neg_of_add_eq_zero_right h
        have : v = t⁻¹ • -(y : Euclid P) := by rw [← h', inv_smul_smul₀ ht]
        rw [this]
        exact L'.smul_mem _ (L'.neg_mem y.2)
    obtain ⟨K, -, hK⟩ := g.exists_antilipschitzWith hker
    have hgc : Continuous g := g.continuous_of_finiteDimensional
    -- local integrability at `v`
    obtain ⟨s, hs, hint⟩ := hψ v
    obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
    have hg0 : g ((0 : L'), (1 : ℝ)) = v := by simp [hg]
    have hT : g ⁻¹' ball v r ∩ {p : L' × ℝ | 0 < p.2} ∈ 𝓝 ((0 : L'), (1 : ℝ)) := by
      refine Filter.inter_mem ?_ ?_
      · apply hgc.continuousAt.preimage_mem_nhds
        rw [hg0]
        exact ball_mem_nhds v hr
      · exact (isOpen_lt continuous_const continuous_snd).mem_nhds (by simp)
    obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.mp hT
    have hUT : closedBall ((0 : L'), (1 : ℝ)) (ε / 2) ⊆ g ⁻¹' ball v r ∩ {p : L' × ℝ | 0 < p.2} :=
      (closedBall_subset_ball (by linarith)).trans hεT
    have hSc : IsCompact (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) :=
      (isCompact_closedBall _ _).image hgc
    have hSs : g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2) ⊆ s := by
      rintro _ ⟨p, hp, rfl⟩
      exact hrs (hUT hp).1
    have hSψ : EqOn ψ (fun _ => ψ v) (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) := by
      rintro _ ⟨p, hp, rfl⟩
      show ψ (g p) = ψ v
      rw [hg]
      exact hinv p.1 (hL'L p.1.2) p.2 (hUT hp).2 v
    -- the `(n + 1)`-dimensional piece has infinite `μH[n]` measure
    have hU_pos : 0 < μH[(Module.finrank ℝ (L' × ℝ) : ℝ)] (closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) :=
      Metric.measure_closedBall_pos _ _ (by linarith)
    have hrank : (Module.finrank ℝ (L' × ℝ) : ℝ) = (n : ℝ) + 1 := by
      rw [Module.finrank_prod, Module.finrank_self, hL'rank]
      push_cast
      ring
    rw [hrank] at hU_pos
    have hS_pos : μH[(n : ℝ) + 1] (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) ≠ 0 := by
      intro h0
      have := hK.le_hausdorffMeasure_image (d := (n : ℝ) + 1) (by positivity)
        (closedBall ((0 : L'), (1 : ℝ)) (ε / 2))
      rw [h0, mul_zero] at this
      exact hU_pos.ne' (nonpos_iff_eq_zero.mp this)
    have hS_top : μH[(n : ℝ)] (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) = ∞ :=
      (Measure.hausdorffMeasure_zero_or_top (lt_add_one (n : ℝ)) _).resolve_left hS_pos
    -- a nonzero constant is not integrable on a set of infinite measure
    have h1 : IntegrableOn (fun _ => ψ v) (g '' closedBall ((0 : L'), (1 : ℝ)) (ε / 2)) μH[(n : ℝ)] :=
      (hint.mono_set hSs).congr_fun hSψ hSc.isClosed.measurableSet
    rw [integrableOn_const_iff] at h1
    rcases h1 with h1 | h1
    · simpa using h1
    · rw [hS_top] at h1
      exact absurd h1 (lt_irrefl _)
/-- **Affine change of variables for `μH[n]`-integrals** (Simon's rescalings
`φ_{x,λ}(z) = φ(x + λz)`, Appendix A).  For `c > 0` the map `x ↦ c • x` pushes `μH[n]` forward to
`c⁻ⁿ μH[n]` (Hausdorff scaling law) and `μH[n]` is translation invariant, so
`∫ h(y + c x) dμH[n](x) = c⁻ⁿ ∫ h dμH[n]` for every `h`; both sides vanish when `h` is not
integrable. -/
theorem Submission.adr_hausdorff_integral_comp_affine : ∀ (P n Q : ℕ) (h : Euclid P → Euclid Q) (y : Euclid P) (c : ℝ), 0 < c → ∫ x, h (y + c • x) ∂μH[(n : ℝ)] = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
  intro P n Q h y c hc
  -- `x ↦ c • x` is a homeomorphism, hence a measurable embedding
  have hemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- push-forward of `μH[n]` under `x ↦ c • x` (the homothety with centre `0` and ratio `c`)
  have hmap : Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)] =
      ‖c‖₊⁻¹ ^ (n : ℝ) • μH[(n : ℝ)] := by
    have := map_homothety_hausdorffMeasure (Nat.cast_nonneg n) (0 : Euclid P) hc.ne'
    convert this using 2
    funext x
    simp [AffineMap.homothety_apply]
  calc ∫ x, h (y + c • x) ∂μH[(n : ℝ)]
      = ∫ w, h (y + w) ∂(Measure.map (fun x : Euclid P => c • x) μH[(n : ℝ)]) :=
        (hemb.integral_map (fun w => h (y + w))).symm
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h (y + w) ∂μH[(n : ℝ)] := by
        rw [hmap, integral_smul_nnreal_measure]
    _ = (‖c‖₊⁻¹ ^ (n : ℝ)) • ∫ w, h w ∂μH[(n : ℝ)] := by
        rw [integral_add_left_eq_self]
    _ = (c ^ n)⁻¹ • ∫ x, h x ∂μH[(n : ℝ)] := by
        rw [NNReal.smul_def]
        congr 1
        simp [Real.norm_of_nonneg hc.le, inv_pow]
/-- **Uniform bound for weakly bounded sequences** (Simon, Appendix A: needed tacitly by the weak
limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  The bounded continuous functions
vanishing off the compact set `K` form a closed subspace `X` of `Euclid P →ᵇ ℝ`, hence a Banach
space.  On it, `Λₖ u = ∫ u • gₖ dμ` are continuous linear maps (`‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`),
pointwise bounded by hypothesis, so the uniform boundedness principle, proved here from the Baire
category theorem, gives `‖Λₖ‖ ≤ M` for all `k`. -/
theorem Submission.adr_uniform_bound_of_weak_bounded : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∃ C, ∀ k, ‖∫ x, f x • gs k x ∂μ‖ ≤ C) → IsCompact K → ∃ M, ∀ (k : ℕ) (h : Euclid P → ℝ) (C : ℝ), Continuous h → (∀ x ∉ K, h x = 0) → (∀ x, |h x| ≤ C) → ‖∫ x, h x • gs k x ∂μ‖ ≤ M * C := by
  intro P Q μ gs K hloc hbdd hK
  -- the subspace `X` of bounded continuous functions vanishing off `K`
  let X : Submodule ℝ (BoundedContinuousFunction (Euclid P) ℝ) :=
    { carrier := {u | ∀ x ∉ K, u x = 0}
      add_mem' := fun {u v} hu hv x hx => by simp [hu x hx, hv x hx]
      zero_mem' := fun x _ => rfl
      smul_mem' := fun c u hu x hx => by simp [hu x hx] }
  -- `X` is closed, hence complete
  have hXclosed : IsClosed (X : Set (BoundedContinuousFunction (Euclid P) ℝ)) := by
    change IsClosed {u : BoundedContinuousFunction (Euclid P) ℝ | ∀ x ∉ K, u x = 0}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe)
        continuous_const
  let _ : SeminormedAddCommGroup X := Submodule.seminormedAddCommGroup X
  let _ : NormedSpace ℝ X := Submodule.normedSpace X
  have : CompleteSpace X := hXclosed.completeSpace_coe
  -- every `u ∈ X` has compact support, so `u • gₖ` is integrable
  have hcs : ∀ u : X,
      HasCompactSupport ((u : BoundedContinuousFunction (Euclid P) ℝ) : Euclid P → ℝ) :=
    fun u => HasCompactSupport.intro hK u.2
  have hint : ∀ k (u : X),
      Integrable (fun x => (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x) μ :=
    fun k u => (hloc k).integrable_smul_left_of_hasCompactSupport
      (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
  -- `‖Λₖ u‖ ≤ (∫_K ‖gₖ‖ dμ) ‖u‖`
  have hbound : ∀ k (u : X), ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖ ≤
      (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
    intro k u
    have hgK : IntegrableOn (gs k) K μ := (hloc k).integrableOn_isCompact hK
    calc ‖∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ‖
        ≤ ∫ x, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ = ∫ x in K, ‖(u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x‖ ∂μ := by
          refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
          simp [u.2 x hx]
      _ ≤ ∫ x in K, ‖u‖ * ‖gs k x‖ ∂μ := by
          refine setIntegral_mono_on (hint k u).norm.integrableOn
            (hgK.norm.const_mul _) hK.measurableSet fun x _ => ?_
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_right
            (BoundedContinuousFunction.norm_coe_le_norm
              (u : BoundedContinuousFunction (Euclid P) ℝ) x)
            (norm_nonneg _)
      _ = (∫ x in K, ‖gs k x‖ ∂μ) * ‖u‖ := by
          rw [integral_const_mul, mul_comm]
  -- the continuous linear maps `Λₖ : X → ℝ^Q`
  let L : ℕ → X →ₗ[ℝ] Euclid Q := fun k =>
    { toFun := fun u => ∫ x, (u : BoundedContinuousFunction (Euclid P) ℝ) x • gs k x ∂μ
      map_add' := fun u v => by
        simp only [Submodule.coe_add, BoundedContinuousFunction.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint k u) (hint k v)
      map_smul' := fun c u => by
        simp only [SetLike.val_smul, BoundedContinuousFunction.coe_smul, smul_eq_mul,
          RingHom.id_apply, mul_smul]
        exact integral_smul c _ }
  let Λ : ℕ → X →L[ℝ] Euclid Q := fun k =>
    LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := X) (F := Euclid Q) (L k)
      (∫ x in K, ‖gs k x‖ ∂μ) (hbound k)
  -- pointwise boundedness: the hypothesis applied to `u ∈ X`
  have hpt : ∀ u : X, ∃ C, ∀ k, ‖Λ k u‖ ≤ C := fun u => by
    obtain ⟨C, hC⟩ := hbdd _ (u : BoundedContinuousFunction (Euclid P) ℝ).continuous (hcs u)
    exact ⟨C, fun k => hC k⟩
  -- uniform boundedness principle (Banach–Steinhaus) from the Baire category theorem
  obtain ⟨M', hM'⟩ : ∃ M', ∀ k, ‖Λ k‖ ≤ M' := by
    let e : ℕ → Set X := fun n => ⋂ k : ℕ, {u : X | ‖Λ k u‖ ≤ n}
    have hc : ∀ n, IsClosed (e n) := fun n =>
      isClosed_iInter fun k => isClosed_le (Λ k).continuous.norm continuous_const
    have hU : ⋃ n, e n = univ := by
      refine eq_univ_of_forall fun u => ?_
      obtain ⟨C, hC⟩ := hpt u
      obtain ⟨m, hm⟩ := exists_nat_ge C
      exact mem_iUnion.2 ⟨m, mem_iInter.2 fun k => (hC k).trans hm⟩
    obtain ⟨m, u₀, hu₀⟩ := nonempty_interior_of_iUnion_of_closed hc hU
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior u₀ hu₀
    have hm : ∀ v ∈ Metric.ball u₀ ε, ∀ k, ‖Λ k v‖ ≤ m := fun v hv k =>
      mem_iInter.1 (interior_subset (hball hv)) k
    refine ⟨(m + m : ℝ) / (ε / 2), fun k =>
      ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hε (by positivity) (by norm_num)
        fun v hv1 _ => ?_⟩
    have hv1' : ε / 2 ≤ ‖v‖ := by simpa using hv1
    calc ‖Λ k v‖ = ‖Λ k (v + u₀) - Λ k u₀‖ := by rw [map_add, add_sub_cancel_right]
      _ ≤ ‖Λ k (v + u₀)‖ + ‖Λ k u₀‖ := norm_sub_le _ _
      _ ≤ m + m := add_le_add
          (hm _ (by rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right]) k)
          (hm _ (Metric.mem_ball_self hε) k)
      _ ≤ (m + m : ℝ) / (ε / 2) * ‖v‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hv1' (by positivity)
  -- conclusion with `M = max M' 0`: a continuous `h` vanishing off `K` with `|h| ≤ C` is an
  -- element of `X` of norm `≤ C`
  refine ⟨max M' 0, fun k h C hcont hK0 hC => ?_⟩
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  let hb : BoundedContinuousFunction (Euclid P) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨h, hcont⟩ (2 * C) (fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      calc |h x - h y| ≤ |h x| + |h y| := abs_sub _ _
        _ ≤ 2 * C := by linarith [hC x, hC y])
  have hbX : hb ∈ X := fun x hx => hK0 x hx
  have hnorm : ‖(⟨hb, hbX⟩ : X)‖ ≤ C := by
    change ‖hb‖ ≤ C
    exact (BoundedContinuousFunction.norm_le hC0).2 fun x => by simpa [hb] using hC x
  calc ‖∫ x, h x • gs k x ∂μ‖ = ‖Λ k ⟨hb, hbX⟩‖ := rfl
    _ ≤ M' * ‖(⟨hb, hbX⟩ : X)‖ := (Λ k).le_of_opNorm_le (hM' k) _
    _ ≤ max M' 0 * C := mul_le_mul (le_max_left _ _) hnorm (norm_nonneg _) (le_max_right _ _)

/-- **Weak convergence against moving test functions** (Simon, Appendix A: "all limits in the
weak sense", the limits `ψ_{y,1} = lim φ_{y+x,λⱼ}` in the proof of A.4, p. 228).  If
`∫ f • gₖ dμ → ∫ f • g dμ` for every continuous compactly supported `f`, and continuous `hₖ → h`
uniformly, with `h` and eventually every `hₖ` vanishing off a fixed compact `K`, then
`∫ hₖ • gₖ dμ → ∫ h • g dμ`: by `Submission.adr_uniform_bound_of_weak_bounded`,
`‖∫ (hₖ - h) • gₖ dμ‖ ≤ M ‖hₖ - h‖_∞ → 0`, and `∫ h • gₖ dμ → ∫ h • g dμ` by hypothesis. -/
theorem Submission.adr_weak_tendsto_of_tendstoUniformly : ∀ (P Q : ℕ) (μ : Measure (Euclid P)) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (hs : ℕ → Euclid P → ℝ) (h : Euclid P → ℝ) (K : Set (Euclid P)), (∀ k, LocallyIntegrable (gs k) μ) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μ) atTop (𝓝 (∫ x, f x • g x ∂μ))) → IsCompact K → (∀ k, Continuous (hs k)) → Continuous h → (∀ᶠ k in atTop, ∀ x ∉ K, hs k x = 0) → (∀ x ∉ K, h x = 0) → TendstoUniformly hs h atTop → Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ) atTop (𝓝 (∫ x, h x • g x ∂μ)) := by
  intro P Q μ gs g hs h K hloc hweak hK hcont hc hsK hK0 hunif
  -- convergent sequences are bounded, so the uniform bound applies on `K`
  obtain ⟨M, hM⟩ := Submission.adr_uniform_bound_of_weak_bounded P Q μ gs K hloc
    (fun f hf hfc => by
      obtain ⟨C, hC⟩ :=
        isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ (hweak f hf hfc))
      exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩) hK
  -- `h` vanishes off the compact `K`, so it is an admissible test function
  have hhc : HasCompactSupport h := HasCompactSupport.intro hK hK0
  -- `∫ hₖ • gₖ dμ - ∫ h • gₖ dμ = ∫ (hₖ - h) • gₖ dμ → 0`
  have hdiff : Tendsto (fun k => ∫ x, hs k x • gs k x ∂μ - ∫ x, h x • gs k x ∂μ) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have hδ : 0 < ε / (2 * (|M| + 1)) := by positivity
    filter_upwards [hsK, Metric.tendstoUniformly_iff.1 hunif _ hδ] with k hk0 hk1
    rw [dist_zero_right, ← integral_sub
      ((hloc k).integrable_smul_left_of_hasCompactSupport (hcont k) (HasCompactSupport.intro hK hk0))
      ((hloc k).integrable_smul_left_of_hasCompactSupport hc hhc)]
    simp_rw [← sub_smul]
    calc ‖∫ x, (hs k x - h x) • gs k x ∂μ‖ ≤ M * (ε / (2 * (|M| + 1))) :=
          hM k (fun x => hs k x - h x) _ ((hcont k).sub hc)
            (fun x hx => by simp [hk0 x hx, hK0 x hx])
            (fun x => by simpa [Real.dist_eq, abs_sub_comm] using (hk1 x).le)
      _ ≤ |M| * (ε / (2 * (|M| + 1))) := mul_le_mul_of_nonneg_right (le_abs_self M) hδ.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith [mul_nonneg (abs_nonneg M) hε.le]
  simpa using hdiff.add (hweak h hc hhc)
/-- **Rescaled translates converge uniformly** (Simon, Appendix A, the weak limits
`ψ = lim φ_{x+λⱼβx,λⱼ}`; step 3 of the proof of `adr_weak_tendsto_comp_affine`).  If `f` is
continuous with compact support and `c_k → 1`, then `f(c_k⁻¹(w − y)) → f(w − y)` uniformly in `w`,
and `f(· − y)` and, for large `k`, `f(c_k⁻¹(· − y))` vanish off one compact ball `K = B̄_{2R}(y)`,
where `R ≥ 1` and `f = 0` off `B̄_R(0)`.  No sign of `c_k` is assumed: eventually `1/2 < c_k < 2`. -/
theorem Submission.adr_rescaled_translate_tendstoUniformly : ∀ (P : ℕ) (f : Euclid P → ℝ) (y : Euclid P) (mus : ℕ → ℝ), Continuous f → HasCompactSupport f → Tendsto mus atTop (𝓝 1) → ∃ K : Set (Euclid P), IsCompact K ∧ (∀ w ∉ K, f (w - y) = 0) ∧ (∀ᶠ k in atTop, ∀ w ∉ K, f ((mus k)⁻¹ • (w - y)) = 0) ∧ TendstoUniformly (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) atTop := by
  intro P f y mus hf hfc hmus
  -- step 1: `tsupport f ⊆ B̄_{R₀}(0)`; with `R := max R₀ 1 ≥ 1`, `f x = 0` whenever `‖x‖ > R`
  obtain ⟨R₀, hR₀⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hzero : ∀ x : Euclid P, R < ‖x‖ → f x = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    have h := hR₀ hxs
    rw [mem_closedBall_zero_iff] at h
    linarith [le_max_left R₀ 1]
  have h2R : 0 < 2 * R := by linarith
  -- step 2: `K := B̄_{2R}(y)`; `f (w - y) = 0` off `K`
  have hK : ∀ w ∉ closedBall y (2 * R), f (w - y) = 0 := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    exact hzero _ (by linarith)
  -- step 3: eventually `1 / 2 < c_k < 2`, so `‖c_k⁻¹ (w - y)‖ > 2R / 2 = R` and
  -- `f (c_k⁻¹ (w - y)) = 0` off `K`
  have hKk : ∀ᶠ k in atTop, ∀ w ∉ closedBall y (2 * R), f ((mus k)⁻¹ • (w - y)) = 0 := by
    filter_upwards [hmus (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2))] with k hk w hw
    rw [mem_closedBall, dist_eq_norm, not_le] at hw
    have hpos : 0 < mus k := by linarith [hk.1]
    apply hzero
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, inv_mul_eq_div, lt_div_iff₀ hpos]
    nlinarith [hk.2]
  refine ⟨closedBall y (2 * R), isCompact_closedBall y (2 * R), hK, hKk, ?_⟩
  -- step 4: `f` is uniformly continuous; on `K` the argument moves by
  -- `|1 - c_k⁻¹| ‖w - y‖ ≤ |c_k⁻¹ - 1| 2R → 0`, and off `K` both values vanish
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hfδ⟩ :=
    Metric.uniformContinuous_iff.mp (hfc.uniformContinuous_of_continuous hf) ε hε
  have hinv : Tendsto (fun k => (mus k)⁻¹) atTop (𝓝 1) := by
    simpa only [inv_one] using hmus.inv₀ one_ne_zero
  filter_upwards [hKk, Metric.tendsto_nhds.mp hinv (δ / (2 * R)) (div_pos hδ h2R)]
    with k hk hk' w
  show dist (f (w - y)) (f ((mus k)⁻¹ • (w - y))) < ε
  by_cases hw : w ∈ closedBall y (2 * R)
  · apply hfδ
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [Real.dist_eq, abs_sub_comm] at hk'
    have hsub : (w - y) - (mus k)⁻¹ • (w - y) = (1 - (mus k)⁻¹) • (w - y) := by
      rw [sub_smul, one_smul]
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs]
    calc |1 - (mus k)⁻¹| * ‖w - y‖ ≤ |1 - (mus k)⁻¹| * (2 * R) :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ < δ / (2 * R) * (2 * R) := mul_lt_mul_of_pos_right hk' h2R
      _ = δ := div_mul_cancel₀ δ h2R.ne'
  · rw [hK w hw, hk w hw, dist_self]
    exact hε

/-- **Simon, proof of A.4 (chapter-A.txt lines 125–133): weak limits of rescalings.**  If
`gₖ ⇀ g` in the weak sense of Appendix A (lines 13–15: tested against `C⁰_c(ℝᴾ)`), each `gₖ`
locally `μH[n]`-integrable, and `cₖ > 0`, `cₖ → 1`, then `gₖ(y + cₖ ·) ⇀ g(y + ·)`.  The change of
variables `w = y + cₖ x` (`adr_hausdorff_integral_comp_affine`) gives
`∫ f(x) gₖ(y + cₖ x) dμ = (cₖⁿ)⁻¹ ∫ fₖ gₖ dμ` with `fₖ = f(cₖ⁻¹ • (· - y))`.  The `fₖ` converge
uniformly to `f(· - y)` with supports eventually in a fixed compact set
(`adr_rescaled_translate_tendstoUniformly`), so the Banach–Steinhaus bound behind
`adr_weak_tendsto_of_tendstoUniformly` gives `∫ fₖ gₖ dμ → ∫ f(· - y) g dμ`. -/
theorem Submission.adr_weak_tendsto_comp_affine : ∀ (P n Q : ℕ) (gs : ℕ → Euclid P → Euclid Q) (g : Euclid P → Euclid Q) (y : Euclid P) (mus : ℕ → ℝ), (∀ k, LocallyIntegrable (gs k) μH[(n : ℝ)]) → (∀ k, 0 < mus k) → Tendsto mus atTop (𝓝 1) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g x ∂μH[(n : ℝ)]))) → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • g (y + x) ∂μH[(n : ℝ)])) := by
  intro P n Q gs g y mus hloc hpos hmus hweak f hf hfc
  -- `fₖ = f (cₖ⁻¹ • (· - y)) → f (· - y)` uniformly, all eventually vanishing off a compact `K`
  obtain ⟨K, hK, h0, hk0, hunif⟩ :=
    Submission.adr_rescaled_translate_tendstoUniformly P f y mus hf hfc hmus
  -- change of variables `w = y + cₖ • x`, and `w = y + x` in the limit
  have hL : ∀ k, ∫ x, f x • gs k (y + mus k • x) ∂μH[(n : ℝ)] =
      ((mus k) ^ n)⁻¹ • ∫ w, f ((mus k)⁻¹ • (w - y)) • gs k w ∂μH[(n : ℝ)] := by
    intro k
    rw [← Submission.adr_hausdorff_integral_comp_affine P n Q
      (fun w => f ((mus k)⁻¹ • (w - y)) • gs k w) y (mus k) (hpos k)]
    simp only [add_sub_cancel_left, inv_smul_smul₀ (hpos k).ne']
  have hR : ∫ x, f x • g (y + x) ∂μH[(n : ℝ)] = ∫ w, f (w - y) • g w ∂μH[(n : ℝ)] := by
    simpa only [one_smul, add_sub_cancel_left, one_pow, inv_one] using
      Submission.adr_hausdorff_integral_comp_affine P n Q (fun w => f (w - y) • g w) y 1 one_pos
  -- weak convergence against the moving test functions `fₖ`
  have hmain := Submission.adr_weak_tendsto_of_tendstoUniformly P Q μH[(n : ℝ)] gs g
    (fun k w => f ((mus k)⁻¹ • (w - y))) (fun w => f (w - y)) K hloc hweak hK
    (fun k => by fun_prop) (by fun_prop) hk0 h0 hunif
  -- the Jacobian factors `(cₖⁿ)⁻¹ → 1`
  have hc : Tendsto (fun k => ((mus k) ^ n)⁻¹) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, inv_one] using (hmus.pow n).inv₀ (pow_ne_zero n one_ne_zero)
  have hlim := hc.smul hmain
  rw [one_smul] at hlim
  rw [hR]
  exact hlim.congr fun k => (hL k).symm

/-- **Simon, proof of A.4, Lemma I** (chapter-A.txt lines 125–134: `ψ_{y,1} = ψ` for `y ∈ S` and
`ψ_{βx,1} = ψ` for `β ∈ ℝ`).  If `φ ∈ F` is invariant under the subspace `S` and its blow-ups
`φ_{x,λₖ} ∈ F` converge weakly to a homogeneous `ψ ∈ F`, then `ψ` is invariant under `S + ℝx`.
Weak limits in `F` are unique (fundamental lemma and (H0)), every translate `ψ(w + ·)` lies in `F`
((A.1) with `θ = 1/(2 + |w|)` and homogeneity), and `ψ(w + ·) = ψ` as soon as
`φ_{x,λₖ}(w + ·) = φ_{x,λₖ}(cₖ ·)` for large `k`, with `cₖ > 0`, `cₖ → 1`
(`adr_weak_tendsto_comp_affine` twice).  This holds for `w ∈ S` with `cₖ = 1`, and for `w = βx`
with `cₖ = 1/(1 + βλₖ)` by the homogeneity of `φ`. -/
theorem Submission.adr_tangent_invariance : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → ∀ φ ∈ F, ∀ S : Submodule ℝ (Euclid P), (∀ y ∈ S, ∀ lam : ℝ, 0 < lam → ∀ x, φ (y + lam • x) = φ x) → ∀ (x : Euclid P) (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) → Tendsto lams atTop (𝓝 0) → (∀ k, (fun z => φ (x + lams k • z)) ∈ F) → ψ ∈ F → (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) → ∀ y ∈ S ⊔ Submodule.span ℝ {x}, ∀ lam : ℝ, 0 < lam → ∀ z, ψ (y + lam • z) = ψ z := by
  intro P n Q F H0 H1 A1 φ hφ S hS x lams ψ hlams_pos hlams hFk hψ hψhom hconv
  -- weak limits in `F` are unique
  have uniq : ∀ g ∈ F, (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
      ∫ z, f z • g z ∂μH[(n : ℝ)] = ∫ z, f z • ψ z ∂μH[(n : ℝ)]) → g = ψ := by
    intro g hg hint
    exact H0 g hg ψ hψ (ae_eq_of_integral_contDiff_smul_eq (H1 g hg) (H1 ψ hψ)
      fun f hf hfs => hint f hf.continuous hfs)
  -- every translate `ψ (w + ·) = ψ (θ • w + θ • ·)`, `θ = 1 / (2 + ‖w‖)`, lies in `F` by (A.1)
  have transl : ∀ w : Euclid P, (fun z => ψ (w + z)) ∈ F := by
    intro w
    have h2 : 0 < 2 + ‖w‖ := by positivity
    set θ : ℝ := 1 / (2 + ‖w‖) with hθ
    have hθpos : 0 < θ := by positivity
    have hθlt : θ < 1 := by
      rw [hθ, div_lt_one h2]
      linarith [norm_nonneg w]
    have hθw : ‖θ • w‖ ≤ 1 - θ := by
      rw [norm_smul, Real.norm_of_nonneg hθpos.le, hθ, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ h2, sub_mul, div_mul_cancel₀ _ h2.ne']
      linarith
    convert A1 ψ hψ (θ • w) θ hθpos hθlt hθw using 1
    funext z
    rw [← smul_add, hψhom θ hθpos]
  -- if `φ (x + λₖ • (w + ·)) = φ (x + λₖ • (cₖ • ·))` for large `k`, `cₖ → 1`, then `ψ (w + ·) = ψ`
  have key : ∀ (w : Euclid P) (c : ℕ → ℝ), (∀ k, 0 < c k) → Tendsto c atTop (𝓝 1) →
      (∀ᶠ k in atTop, ∀ z, φ (x + lams k • (w + z)) = φ (x + lams k • (c k • z))) →
      ∀ z, ψ (w + z) = ψ z := by
    intro w c hcpos hc hev
    have hloc : ∀ k, LocallyIntegrable (fun z => φ (x + lams k • z)) μH[(n : ℝ)] :=
      fun k => H1 _ (hFk k)
    have hint : ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f →
        ∫ z, f z • ψ (w + z) ∂μH[(n : ℝ)] = ∫ z, f z • ψ z ∂μH[(n : ℝ)] := by
      intro f hf hfs
      have h1 := Submission.adr_weak_tendsto_comp_affine P n Q (fun k z => φ (x + lams k • z)) ψ
        w (fun _ => 1) hloc (fun _ => one_pos) tendsto_const_nhds hconv f hf hfs
      have h2 := Submission.adr_weak_tendsto_comp_affine P n Q (fun k z => φ (x + lams k • z)) ψ
        0 c hloc hcpos hc hconv f hf hfs
      simp only [one_smul, zero_add] at h1 h2
      refine tendsto_nhds_unique (h1.congr' ?_) h2
      filter_upwards [hev] with k hk
      simp only [hk]
    exact congrFun (uniq _ (transl w) hint)
  -- translations in `S`: `φ (x + λₖ • (s + z)) = φ (λₖ • s + 1 • (x + λₖ • z))`
  have hSinv : ∀ s ∈ S, ∀ z, ψ (s + z) = ψ z := by
    intro s hs
    refine key s (fun _ => 1) (fun _ => one_pos) tendsto_const_nhds
      (Eventually.of_forall fun k z => ?_)
    have := hS (lams k • s) (S.smul_mem _ hs) 1 one_pos (x + lams k • z)
    rw [one_smul] at this ⊢
    rw [← this]
    congr 1
    module
  -- translations along `x`: `φ (x + λₖ • (β • x + z)) = φ (aₖ • (x + λₖ • (aₖ⁻¹ • z)))`,
  -- `aₖ = 1 + β λₖ > 0` for large `k`
  have hxinv : ∀ β : ℝ, ∀ z, ψ (β • x + z) = ψ z := by
    intro β
    have ha : Tendsto (fun k => 1 + β * lams k) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hlams.const_mul β)
    have hev : ∀ᶠ k in atTop, 0 < 1 + β * lams k := ha.eventually (eventually_gt_nhds one_pos)
    let c : ℕ → ℝ := fun k => if 0 < 1 + β * lams k then (1 + β * lams k)⁻¹ else 1
    have hc : ∀ᶠ k in atTop, c k = (1 + β * lams k)⁻¹ := by
      filter_upwards [hev] with k hk
      simp only [c, hk, ite_true]
    refine key (β • x) c (fun k => ?_) ?_ ?_
    · by_cases h : 0 < 1 + β * lams k
      · simp only [c, h, ite_true]
        positivity
      · simp only [c, h, ite_false]
        exact one_pos
    · refine (tendsto_congr' hc).2 ?_
      simpa using ha.inv₀ one_ne_zero
    · filter_upwards [hev, hc] with k hk hck z
      rw [hck]
      have := hS 0 S.zero_mem (1 + β * lams k) hk (x + lams k • ((1 + β * lams k)⁻¹ • z))
      rw [zero_add] at this
      rw [← this]
      congr 1
      rw [smul_add (1 + β * lams k), smul_comm (1 + β * lams k) (lams k),
        smul_inv_smul₀ hk.ne']
      module
  intro y hy lam hlam z
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.mp ht
  rw [add_assoc, hSinv s hs, hxinv β, hψhom lam hlam]
/-- **Simon A.4** (proof of (1), the radii `λₖ ↓ 0`): if every `δ > 0` admits some `ρ ∈ (0, δ)`
with `Q ρ`, then there are `ρₖ ∈ (0, δ₀)` with `Q ρₖ`, strictly decreasing to `0`.  Choose
`g(δ) ∈ (0, δ)` with `Q (g δ)` for each `δ > 0` and set `ρ₀ = g(δ₀)`,
`ρₖ₊₁ = g(min ρₖ (1/(k+1)))`; then `0 < ρₖ₊₁ < min ρₖ (1/(k+1))`. -/
theorem Submission.adr_exists_strictAnti_radii : ∀ (Q : ℝ → Prop) (δ₀ : ℝ), 0 < δ₀ → (∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ Q ρ) → ∃ ρs : ℕ → ℝ, (∀ k, 0 < ρs k) ∧ (∀ k, ρs k < δ₀) ∧ StrictAnti ρs ∧ Tendsto ρs atTop (𝓝 0) ∧ ∀ k, Q (ρs k) := by
  intro Q δ₀ hδ₀ hQ
  -- `g δ ∈ (0, δ)` with `Q (g δ)` for every `δ > 0`
  choose! g hg0 hgδ hgQ using hQ
  -- `ρ₀ = g δ₀`, `ρₖ₊₁ = g (min ρₖ (1/(k+1)))`
  let ρs : ℕ → ℝ := fun k =>
    Nat.rec (motive := fun _ => ℝ) (g δ₀) (fun k ρ => g (min ρ (1 / ((k : ℝ) + 1)))) k
  have hsucc : ∀ k, ρs (k + 1) = g (min (ρs k) (1 / ((k : ℝ) + 1))) := fun _ => rfl
  have hpos : ∀ k, 0 < ρs k := by
    intro k
    induction k with
    | zero => exact hg0 δ₀ hδ₀
    | succ k ih =>
      rw [hsucc]
      exact hg0 _ (lt_min ih Nat.one_div_pos_of_nat)
  have hmin : ∀ k, 0 < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k =>
    lt_min (hpos k) Nat.one_div_pos_of_nat
  have hlt : ∀ k, ρs (k + 1) < min (ρs k) (1 / ((k : ℝ) + 1)) := fun k => by
    rw [hsucc]
    exact hgδ _ (hmin k)
  have hanti : StrictAnti ρs :=
    strictAnti_nat_of_succ_lt fun k => (hlt k).trans_le (min_le_left _ _)
  refine ⟨ρs, hpos, fun k => (hanti.antitone k.zero_le).trans_lt (hgδ δ₀ hδ₀), hanti, ?_, ?_⟩
  · -- squeeze `0 < ρₖ₊₁ < 1/(k+1)`
    refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat (fun k => (hpos (k + 1)).le)
      fun k => ((hlt k).trans_le (min_le_right _ _)).le)
  · intro k
    cases k with
    | zero => exact hgQ δ₀ hδ₀
    | succ k =>
      rw [hsucc]
      exact hgQ _ (hmin k)
/-- **An `H^ℓ`-null set has open covers of arbitrarily small `ℓ`-dimensional cost**: the open
balls covering `sing ψ` with `∑ⱼ ω_ℓ ρⱼ^ℓ < ε` in the proof of Simon A.4 (chapter-A.txt
lines 88–97), with thickenings in place of balls.  The scale-`1` term of `hausdorffMeasure_apply`
gives a cover `E ⊆ ⋃ₙ tₙ` with `diam tₙ ≤ 1` and `∑ₙ c(tₙ) < ε / 2`, where `c(t) = (diam t)^ℓ`
for `t ≠ ∅` and `c(∅) = 0`.  With slack `δₙ > 0`, `∑ₙ δₙ < ε / 2`, each `tₙ` is replaced by its
open `rₙ`-thickening, `rₙ > 0` so small that `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`. -/
theorem Submission.adr_null_open_cover : ∀ (P : ℕ) (ℓ : ℝ) (E : Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → μH[ℓ] E = 0 → 0 < ε → ∃ U : ℕ → Set (Euclid P), (∀ j, IsOpen (U j)) ∧ E ⊆ ⋃ j, U j ∧ ∑' j, Metric.ediam (U j) ^ ℓ < ε := by
  intro P ℓ E ε hℓ hE hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  -- the scale-`1` term of the formula for `μH[ℓ] E = 0` gives a cheap cover `t`
  obtain ⟨t, hEt, ht1, ht⟩ : ∃ t : ℕ → Set (Euclid P), E ⊆ ⋃ n, t n ∧
      (∀ n, ediam (t n) ≤ 1) ∧ ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ < ε / 2 := by
    have h1 : (⨅ (t : ℕ → Set (Euclid P)) (_ : E ⊆ ⋃ n, t n) (_ : ∀ n, ediam (t n) ≤ 1),
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) < ε / 2 := by
      refine lt_of_le_of_lt ?_ hε2
      rw [← hE, Measure.hausdorffMeasure_apply]
      exact le_iSup₂_of_le (1 : ℝ≥0∞) one_pos le_rfl
    simpa only [iInf_lt_iff, exists_prop] using h1
  -- slack `δₙ > 0` with `∑ₙ δₙ < ε / 2`
  obtain ⟨δ, hδ, hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε2.ne' ℕ
  -- radii `rₙ > 0` with `(diam tₙ + 2rₙ)^ℓ < (diam tₙ)^ℓ + δₙ`, by continuity at `0`
  have hr : ∀ n, ∃ r : NNReal, 0 < r ∧
      (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n := by
    intro n
    have hcont : Continuous fun r : NNReal => (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ := by
      fun_prop (disch := norm_num)
    have hfin : ediam (t n) ^ ℓ ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hℓ.le ((ht1 n).trans_lt ENNReal.one_lt_top).ne
    have hev : ∀ᶠ r : NNReal in 𝓝 0,
        (ediam (t n) + 2 * (r : ℝ≥0∞)) ^ ℓ < ediam (t n) ^ ℓ + δ n :=
      (isOpen_lt hcont continuous_const).mem_nhds
        (by simpa using ENNReal.lt_add_right hfin (hδ n).ne')
    exact (Filter.Eventually.and self_mem_nhdsWithin
      (hev.filter_mono nhdsWithin_le_nhds) : ∀ᶠ r : NNReal in 𝓝[>] 0, 0 < r ∧ _).exists
  choose r hr0 hr using hr
  -- `Uₙ` is the open `rₙ`-thickening of `tₙ`; `diam Uₙ ≤ diam tₙ + 2rₙ`
  refine ⟨fun n => thickening (r n) (t n), fun n => isOpen_thickening, ?_, ?_⟩
  · exact hEt.trans (iUnion_mono fun n => self_subset_thickening (NNReal.coe_pos.mpr (hr0 n)) _)
  calc ∑' n, ediam (thickening (r n) (t n)) ^ ℓ
      ≤ ∑' n, ((⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + δ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rcases (t n).eq_empty_or_nonempty with h | h
        · simp [h, ENNReal.zero_rpow_of_pos hℓ]
        · rw [iSup_pos h]
          exact (ENNReal.rpow_le_rpow (ediam_thickening_le (r n)) hℓ.le).trans (hr n).le
    _ = ∑' n, (⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ) + ∑' n, δ n := ENNReal.tsum_add
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add ht hδsum
    _ = ε := ENNReal.add_halves ε

/-- **A small-cost cover of a null closed set eventually covers nearby sets in `B_{1/2}(0)`**:
Simon's "`K ≡ B̄₁(0) \ ∪ⱼ B_{ρⱼ}(xⱼ)` is a compact set with positive distance from `sing ψ`.
Hence by assumption A.3(3) we have `sing φ_{x,λₖ'} ∩ B₁(0) ⊆ ∪ⱼ B_{ρⱼ}(xⱼ)` for all sufficiently
large `k`" in the proof of A.4 (chapter-A.txt lines 97–101), for `S ∩ B̄_{1/2}(0)` only.
`adr_null_open_cover` covers the null set `E = S ∩ B̄_{1/2}(0)` by open `Uⱼ`.  The compact
`K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` misses the closed `S`, so some thickening `thickening η K` misses `S`;
the hypothesis at this `η` puts `B_{1/2}(0) ∩ Tₖ` (`k ≥ k₀`) within `η` of `S`, hence off `K`. -/
theorem Submission.adr_eventually_subset_small_cover : ∀ (P : ℕ) (ℓ : ℝ) (S : Set (Euclid P)) (Ts : ℕ → Set (Euclid P)) (ε : ℝ≥0∞), 0 < ℓ → IsClosed S → μH[ℓ] (S ∩ ball (0 : Euclid P) 1) = 0 → 0 < ε → (∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ Ts k ⊆ {x | ∃ z ∈ S, dist x z < η}) → ∃ (U : ℕ → Set (Euclid P)) (k₀ : ℕ), ∑' j, Metric.ediam (U j) ^ ℓ < ε ∧ ∀ k ≥ k₀, ball (0 : Euclid P) (1 / 2) ∩ Ts k ⊆ ⋃ j, U j := by
  intro P ℓ S Ts ε hℓ hS hS1 hε hT
  -- `E = S ∩ B̄_{1/2}(0) ⊆ S ∩ B₁(0)` is `μH[ℓ]`-null, so it has an open cover of cost `< ε`
  have hE : μH[ℓ] (S ∩ closedBall (0 : Euclid P) (1 / 2)) = 0 :=
    measure_mono_null (inter_subset_inter_right S (closedBall_subset_ball (by norm_num))) hS1
  obtain ⟨U, hUo, hEU, hU⟩ := Submission.adr_null_open_cover P ℓ _ ε hℓ hE hε
  -- `K = B̄_{1/2}(0) \ ⋃ⱼ Uⱼ` is compact and misses the closed set `S`
  have hK : IsCompact (closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j) :=
    (isCompact_closedBall _ _).diff (isOpen_iUnion hUo)
  have hKS : closedBall (0 : Euclid P) (1 / 2) \ ⋃ j, U j ⊆ Sᶜ := fun w hw hwS =>
    hw.2 (hEU ⟨hwS, hw.1⟩)
  -- a uniform gap: `thickening η K` misses `S`
  obtain ⟨η, hη, hηK⟩ := hK.exists_thickening_subset_open hS.isOpen_compl hKS
  obtain ⟨k₀, hk₀⟩ := hT η hη
  refine ⟨U, k₀, hU, fun k hk w hw => ?_⟩
  by_contra hwU
  obtain ⟨z, hzS, hwz⟩ := hk₀ k hk ⟨ball_subset_ball (by norm_num) hw.1, hw.2⟩
  exact hηK (mem_thickening_iff.mpr ⟨w, ⟨ball_subset_closedBall hw.1, hwU⟩, by rwa [dist_comm]⟩)
    hzS
/-- **Simon A.4** (proof of (1), the rescaling step, with blow-up scale `λ = 2ρ`): if every cover
`{Cⱼ}` of `A ∩ B_ρ(x)` has `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` and the `Uⱼ` cover every `z` with `|z| < 1/2`
and `x + 2ρz ∈ A`, then `Σⱼ (diam Uⱼ)^ℓ ≥ 2^{−ℓ}/8`.  The sets `Cⱼ = x + 2ρ·Uⱼ` cover
`A ∩ B_ρ(x)` and have `diam Cⱼ = 2ρ diam Uⱼ`, so a smaller sum would give
`ρ^ℓ ≤ 2·2^ℓρ^ℓ Σⱼ (diam Uⱼ)^ℓ < ρ^ℓ/4`. -/
theorem Submission.adr_rescaled_content_lower_bound : ∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)) (x : Euclid P) (ρ : ℝ) (U : ℕ → Set (Euclid P)), 0 < ℓ → 0 < ρ → (∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ) → (∀ z : Euclid P, x + (2 * ρ) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j) → (2 : ℝ≥0∞) ^ (-ℓ) / 8 ≤ ∑' j, Metric.ediam (U j) ^ ℓ := by
  intro P ℓ A x ρ U hℓ hρ hD hU
  have hlam : 0 < 2 * ρ := by positivity
  -- `Cⱼ = g(Uⱼ)` with `g(z) = x + 2ρz` cover `A ∩ B_ρ(x)`: `w = g(z)` for `z = (2ρ)⁻¹(w − x)`,
  -- and `|z| = |w − x|/(2ρ) < 1/2`
  have hcover : A ∩ ball x ρ ⊆ ⋃ j, (fun z => x + (2 * ρ) • z) '' U j := by
    rintro w ⟨hwA, hwB⟩
    have hgz : x + (2 * ρ) • ((2 * ρ)⁻¹ • (w - x)) = w := by
      rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, add_sub_cancel]
    have hzn : ‖(2 * ρ)⁻¹ • (w - x)‖ < 1 / 2 := by
      rw [mem_ball, dist_eq_norm] at hwB
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hlam.le, inv_mul_lt_iff₀ hlam]
      linarith
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hU _ (by rw [hgz]; exact hwA) hzn)
    exact mem_iUnion.mpr ⟨j, _, hj, hgz⟩
  -- `diam Cⱼ = 2ρ diam Uⱼ`: `g` is the dilation by `2ρ` followed by a translation
  have hdiam : ∀ j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) =
      ENNReal.ofReal (2 * ρ) * Metric.ediam (U j) := by
    intro j
    rw [show (fun z => x + (2 * ρ) • z) '' U j = (fun y => x + y) '' ((fun z => (2 * ρ) • z) '' U j)
        from (Set.image_image (fun y => x + y) (fun z => (2 * ρ) • z) (U j)).symm,
      (isometry_add_left x).ediam_image, Set.image_smul, ediam_smul₀, ENNReal.smul_def, smul_eq_mul,
      ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hlam.le]
  -- hence `Σⱼ (diam Cⱼ)^ℓ = 2^ℓ ρ^ℓ Σⱼ (diam Uⱼ)^ℓ`
  have hsum : ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ =
      2 ^ ℓ * ENNReal.ofReal ρ ^ ℓ * ∑' j, Metric.ediam (U j) ^ ℓ := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hdiam j, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat,
      ENNReal.mul_rpow_of_nonneg _ _ hℓ.le, ENNReal.mul_rpow_of_nonneg _ _ hℓ.le]
  have key :
      ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam ((fun z => x + (2 * ρ) • z) '' U j) ^ ℓ :=
    hD _ hcover
  rw [hsum] at key
  -- if `σ < 2^{−ℓ}/8` then `r ≤ 2·2^ℓ r σ < 2·2^ℓ r 2^{−ℓ}/8 = r/4 ≤ r`, where `r = ρ^ℓ ∈ (0, ∞)`
  rw [ENNReal.rpow_neg]
  refine not_lt.mp fun hlt => ?_
  set σ := ∑' j, Metric.ediam (U j) ^ ℓ
  set r := ENNReal.ofReal ρ ^ ℓ
  set t := (2 : ℝ≥0∞) ^ ℓ
  have hr0 : r ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hρ) ENNReal.ofReal_ne_top).ne'
  have hrT : r ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le ENNReal.ofReal_ne_top
  have ht0 : t ≠ 0 := (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
  have htT : t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hℓ.le (by norm_num)
  have hcalc : 2 * t * r * (t⁻¹ / 8) = r / 4 := by
    have h8 : (8 : ℝ≥0∞)⁻¹ = 2⁻¹ * 4⁻¹ := by
      rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
      norm_num
    rw [div_eq_mul_inv, div_eq_mul_inv, h8]
    calc 2 * t * r * (t⁻¹ * (2⁻¹ * 4⁻¹))
        = (2 * 2⁻¹) * (t * t⁻¹) * (r * 4⁻¹) := by ring
      _ = r * 4⁻¹ := by
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), ENNReal.mul_inv_cancel ht0 htT,
          one_mul, one_mul]
  have hfac0 : 2 * t * r ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) ht0) hr0
  have hfacT : 2 * t * r ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) htT) hrT
  have hrr : r < r :=
    calc r ≤ 2 * (t * r * σ) := key
      _ = 2 * t * r * σ := by ring
      _ < 2 * t * r * (t⁻¹ / 8) := ENNReal.mul_lt_mul_right hfac0 hfacT hlt
      _ = r / 4 := hcalc
      _ ≤ r := ENNReal.div_le_of_le_mul (le_mul_of_one_le_right' (by norm_num))
  exact lt_irrefl r hrr
/-- **Simon Ch. 1, 3.26(2)** (cover form, unnormalized): for `ℓ > 0` and `A ⊆ ℝᴾ`, at `μH[ℓ]`-a.e.
`x ∈ A` there are arbitrarily small `ρ` with `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` for every countable cover
`{Cⱼ}` of `A ∩ B_ρ(x)`.  Let `η(E) = inf Σⱼ (diam Cⱼ)^ℓ` over countable covers of `E` (the content
`H^ℓ_∞`).  The exceptional points lie in countably many sets `B ⊆ A` of diameter `< R` with
`2η(A ∩ B_ρ(x)) ≤ ρ^ℓ` for `x ∈ B`, `0 < ρ < R`.  If `C` meets such a `B` at `x`, then
`C ∩ B ⊆ A ∩ B_ρ(x)` for every `ρ > diam(C ∩ B)`, so `2η(C ∩ B) ≤ (diam C)^ℓ`; hence
`η(B) ≤ η(B)/2`, `η(B) = 0`, and `μH[ℓ](B) = 0` because covers of small sum have small diameters.
Measurability and boundedness of `A` are not used. -/
theorem Submission.adr_content_density : ∀ (P : ℕ) (ℓ : ℝ) (A : Set (Euclid P)), 0 < ℓ → MeasurableSet A → Bornology.IsBounded A → μH[ℓ] {x | x ∈ A ∧ ¬ ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ ∀ C : ℕ → Set (Euclid P), A ∩ ball x ρ ⊆ ⋃ j, C j → ENNReal.ofReal ρ ^ ℓ ≤ 2 * ∑' j, Metric.ediam (C j) ^ ℓ} = 0 := by
  intro P ℓ A hℓ _ _
  -- `η` is the content `H^ℓ_∞`
  set η : OuterMeasure (Euclid P) := OuterMeasure.boundedBy fun C => ediam C ^ ℓ with hη
  -- content-null sets are `μH[ℓ]`-null: a cover with `Σⱼ (diam Cⱼ)^ℓ < min ε r^ℓ` has all
  -- diameters `≤ r`
  have hnull : ∀ B : Set (Euclid P), η B = 0 → μH[ℓ] B = 0 := by
    intro B hB
    refine le_antisymm ?_ bot_le
    rw [Measure.hausdorffMeasure_apply]
    refine iSup₂_le fun r hr => ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hlt : η B < min (ε : ℝ≥0∞) (r ^ ℓ) := by
      rw [hB]
      exact lt_min (by exact_mod_cast hε) (ENNReal.rpow_pos_of_nonneg hr hℓ.le)
    rw [hη, OuterMeasure.boundedBy_apply] at hlt
    obtain ⟨t, ht, hsum⟩ : ∃ t : ℕ → Set (Euclid P), B ⊆ ⋃ n, t n ∧
        ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ ℓ < min (ε : ℝ≥0∞) (r ^ ℓ) := by
      simpa only [iInf_lt_iff, exists_prop] using hlt
    refine iInf₂_le_of_le t ht (iInf_le_of_le (fun n => ?_) ?_)
    · rcases (t n).eq_empty_or_nonempty with hn | hn
      · simp [hn]
      · refine ((ENNReal.rpow_lt_rpow_iff hℓ).1 ?_).le
        exact ((le_iSup (fun _ : (t n).Nonempty => ediam (t n) ^ ℓ) hn).trans
          (ENNReal.le_tsum (f := fun k => ⨆ _ : (t k).Nonempty, ediam (t k) ^ ℓ) n)).trans_lt
          (hsum.trans_le (min_le_right _ _))
    · rw [zero_add]
      exact (hsum.trans_le (min_le_left _ _)).le
  -- the contraction `η(B) ≤ η(B)/2` on a set `B ⊆ A` of diameter `< R`
  have hcontr : ∀ (R : ℝ) (B : Set (Euclid P)), 0 < R → B ⊆ A → ediam B < ENNReal.ofReal R →
      (∀ x ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < R → 2 * η (A ∩ ball x ρ) ≤ ENNReal.ofReal ρ ^ ℓ) →
      η B = 0 := by
    intro R B hR hBA hBR hball
    have hkey : ∀ C : Set (Euclid P), 2 * η (C ∩ B) ≤ ediam C ^ ℓ := by
      intro C
      rcases (C ∩ B).eq_empty_or_nonempty with hCB | ⟨x, hxC, hxB⟩
      · rw [hCB, measure_empty, mul_zero]
        exact bot_le
      have hDR : ediam (C ∩ B) < ENNReal.ofReal R :=
        (ediam_mono inter_subset_right).trans_lt hBR
      have hd : ENNReal.ofReal (ediam (C ∩ B)).toReal = ediam (C ∩ B) :=
        ENNReal.ofReal_toReal hDR.ne_top
      have hdR : (ediam (C ∩ B)).toReal < R := by
        rwa [← hd, ENNReal.ofReal_lt_ofReal_iff hR] at hDR
      have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal ρ ^ ℓ) (𝓝[>] (ediam (C ∩ B)).toReal)
          (𝓝 (ENNReal.ofReal (ediam (C ∩ B)).toReal ^ ℓ)) :=
        ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto _).mono_left
          nhdsWithin_le_nhds
      -- `C ∩ B ⊆ A ∩ B_ρ(x)` for `diam(C ∩ B) < ρ < R`; let `ρ ↓ diam(C ∩ B)`
      calc 2 * η (C ∩ B) ≤ ENNReal.ofReal (ediam (C ∩ B)).toReal ^ ℓ := by
            refine ge_of_tendsto hlim ?_
            filter_upwards [Ioo_mem_nhdsGT hdR] with ρ hρ
            have hρ0 : 0 < ρ := ENNReal.toReal_nonneg.trans_lt hρ.1
            have hsub : C ∩ B ⊆ A ∩ ball x ρ := by
              intro y hy
              refine ⟨hBA hy.2, ?_⟩
              have hyx : edist y x ≤ ediam (C ∩ B) := edist_le_ediam_of_mem hy ⟨hxC, hxB⟩
              rw [edist_dist, ← hd, ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg] at hyx
              exact mem_ball.2 (hyx.trans_lt hρ.1)
            calc 2 * η (C ∩ B) ≤ 2 * η (A ∩ ball x ρ) := by gcongr
              _ ≤ ENNReal.ofReal ρ ^ ℓ := hball x hxB ρ hρ0 hρ.2
        _ = ediam (C ∩ B) ^ ℓ := by rw [hd]
        _ ≤ ediam C ^ ℓ := ENNReal.rpow_le_rpow (ediam_mono inter_subset_left) hℓ.le
    have hle : OuterMeasure.restrict B η ≤ (2 : ℝ≥0∞)⁻¹ • η := by
      have h2 : (2 : ℝ≥0∞)⁻¹ • η =
          OuterMeasure.boundedBy ((2 : ℝ≥0∞)⁻¹ • fun C : Set (Euclid P) => ediam C ^ ℓ) :=
        OuterMeasure.smul_boundedBy (ENNReal.inv_ne_top.2 two_ne_zero)
      rw [h2]
      refine OuterMeasure.le_boundedBy.2 fun C => ?_
      rw [OuterMeasure.restrict_apply, Pi.smul_apply, smul_eq_mul,
        ← ENNReal.mul_le_iff_le_inv two_ne_zero ENNReal.ofNat_ne_top]
      exact hkey C
    have hBB : η B ≤ (2 : ℝ≥0∞)⁻¹ * η B := by
      simpa only [OuterMeasure.restrict_apply, inter_self, smul_apply, smul_eq_mul] using hle B
    have hfin : η B ≠ ∞ :=
      ((OuterMeasure.boundedBy_le B).trans_lt (ENNReal.rpow_lt_top_of_nonneg hℓ.le
        (hBR.trans ENNReal.ofReal_lt_top).ne)).ne
    rw [← ENNReal.mul_le_iff_le_inv two_ne_zero ENNReal.ofNat_ne_top, two_mul] at hBB
    exact nonpos_iff_eq_zero.1
      ((ENNReal.add_le_add_iff_left hfin).1 (hBB.trans_eq (add_zero _).symm))
  -- the exceptional set lies in the sets `N m ∩ B(u j, 1/(4(m + 1)))`, `u` dense
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Euclid P)
  let N : ℕ → Set (Euclid P) := fun m => {x | x ∈ A ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
    2 * η (A ∩ ball x ρ) ≤ ENNReal.ofReal ρ ^ ℓ}
  refine measure_mono_null (t := ⋃ m : ℕ, ⋃ j : ℕ,
    N m ∩ eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1))))) ?_ ?_
  · rintro x ⟨hxA, hx⟩
    push Not at hx
    obtain ⟨δ, hδ, hδx⟩ := hx
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    obtain ⟨j, hj⟩ := hu.exists_dist_lt x (show (0 : ℝ) < 1 / (4 * (m + 1)) by positivity)
    refine mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨j, ⟨hxA, fun ρ hρ hρm => ?_⟩, ?_⟩⟩
    · obtain ⟨C, hC, hCsum⟩ := hδx ρ hρ (hρm.trans hm)
      calc 2 * η (A ∩ ball x ρ) ≤ 2 * ∑' j, ediam (C j) ^ ℓ := by
            gcongr
            exact (measure_mono hC).trans ((measure_iUnion_le C).trans
              (ENNReal.tsum_le_tsum fun j => OuterMeasure.boundedBy_le _))
        _ ≤ ENNReal.ofReal ρ ^ ℓ := hCsum.le
    · rw [mem_eball, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hj
  · refine measure_iUnion_null fun m => measure_iUnion_null fun j => hnull _ ?_
    refine hcontr (1 / (m + 1)) _ (by positivity) (fun x hx => hx.1.1) ?_ (fun x hx => hx.1.2)
    calc ediam (N m ∩ eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1)))))
        ≤ ediam (eball (u j) (ENNReal.ofReal (1 / (4 * (m + 1))))) :=
          ediam_mono inter_subset_right
      _ ≤ 2 * ENNReal.ofReal (1 / (4 * (m + 1))) := ediam_eball_le
      _ < ENNReal.ofReal (1 / (m + 1)) := by
        rw [two_mul, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_lt_ofReal_iff (by positivity)]
        field_simp
        linarith

/-- **Simon A.4**, proof of (1) (chapter-A.txt lines 58–112): for `μH[ℓ]`-a.e.
`x ∈ A = sing φ ∩ B₁(0)` some blow-up `φ_{x,λₖ} ⇀ ψ ∈ F` has `ψ` homogeneous of degree zero and
`μH[ℓ](sing ψ ∩ B₁(0)) > 0`.  `A` is closed ∩ open (A.3c), so by `adr_content_density` it
suffices to treat `x ∈ A` with the cover inequality `ρ^ℓ ≤ 2 Σⱼ (diam Cⱼ)^ℓ` at arbitrarily
small `ρ`.  `adr_exists_strictAnti_radii` gives such `ρₖ ↓ 0` with `ρₖ < (1 − |x|)/4`, and A.2 for
the scales `2ρₖ` gives `sub` and `ψ` with `φ_{x,λₖ} ⇀ ψ`, `λₖ = 2ρ_{sub(k)}`.  If
`μH[ℓ](sing ψ ∩ B₁(0)) = 0`, then A.1 and A.3(3) feed `adr_eventually_subset_small_cover`:
`B_{1/2}(0) ∩ sing φ_{x,λₖ} ⊆ ⋃ⱼ Uⱼ` for `k ≥ k₀`, with `Σⱼ (diam Uⱼ)^ℓ < 2^{−ℓ}/8`.  By A.3(2)
this is hypothesis (ii) of `adr_rescaled_content_lower_bound` at `ρ = ρ_{sub(k₀)}`, whose
conclusion `Σⱼ (diam Uⱼ)^ℓ ≥ 2^{−ℓ}/8` is a contradiction. -/
theorem Submission.adr_tangent_keeps_measure : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ ℓ : ℝ, 0 < ℓ → ∀ φ ∈ F, μH[ℓ] {x | x ∈ sing φ ∩ ball (0 : Euclid P) 1 ∧ ¬ ∃ (lams : ℕ → ℝ) (ψ : Euclid P → Euclid Q), (∀ k, 0 < lams k) ∧ (∀ k, lams k < 1) ∧ (∀ k, ‖x‖ ≤ 1 - lams k) ∧ Tendsto lams atTop (𝓝 0) ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z, f z • φ (x + lams k • z) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ z, f z • ψ z ∂μH[(n : ℝ)]))) ∧ (∀ lam : ℝ, 0 < lam → ∀ z, ψ (lam • z) = ψ z) ∧ 0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1)} = 0 := by
  intro P n Q F sing hF hblow hclosed hsing hconv ℓ hℓ φ hφ
  set A := sing φ ∩ ball (0 : Euclid P) 1
  -- off a `μH[ℓ]`-null set, `x ∈ A` has the cover inequality at arbitrarily small radii
  refine measure_mono_null ?_ (Submission.adr_content_density P ℓ A hℓ
    ((hclosed φ hφ).measurableSet.inter measurableSet_ball) (isBounded_ball.subset inter_subset_right))
  rintro x ⟨hxA, hx⟩
  refine ⟨hxA, fun hD => hx ?_⟩
  have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hxA.2
  -- radii `ρₖ ↓ 0`, `ρₖ < (1 − |x|)/4`, each with the cover inequality
  obtain ⟨ρs, hρ0, hρlt, hρanti, hρlim, hρD⟩ :=
    Submission.adr_exists_strictAnti_radii _ ((1 - ‖x‖) / 4) (by linarith) hD
  -- A.2 at `y = x` for the scales `2ρₖ`; the blow-up scales are `λₖ = 2ρ_{sub(k)}`
  have h2lim : Tendsto (fun k => 2 * ρs k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hρlim.const_mul 2
  obtain ⟨sub, ψ, hsub, hψF, hψ, hψhom⟩ := hblow φ hφ x hx1 (fun k => 2 * ρs k)
    (fun k => mul_pos two_pos (hρ0 k))
    (fun a b hab => by
      show 2 * ρs b < 2 * ρs a
      linarith [hρanti hab])
    h2lim
  have hlam0 : ∀ k, 0 < 2 * ρs (sub k) := fun k => mul_pos two_pos (hρ0 (sub k))
  have hlam1 : ∀ k, 2 * ρs (sub k) < 1 := fun k => by
    linarith [hρlt (sub k), norm_nonneg x]
  have hlamx : ∀ k, ‖x‖ ≤ 1 - 2 * ρs (sub k) := fun k => by
    linarith [hρlt (sub k)]
  have hlamlim : Tendsto (fun k => 2 * ρs (sub k)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (hρlim.comp hsub.tendsto_atTop).const_mul 2
  refine ⟨fun k => 2 * ρs (sub k), ψ, hlam0, hlam1, hlamx, hlamlim, hψF, hψ, hψhom, ?_⟩
  -- if `μH[ℓ](sing ψ ∩ B₁(0)) = 0`, a cheap cover of `sing ψ` contradicts the cover inequality
  refine pos_iff_ne_zero.2 fun hψ0 => ?_
  have hε : (0 : ℝ≥0∞) < (2 : ℝ≥0∞) ^ (-ℓ) / 8 :=
    ENNReal.div_pos (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne' (by norm_num)
  obtain ⟨U, k₀, hU, hUcov⟩ := Submission.adr_eventually_subset_small_cover P ℓ (sing ψ)
    (fun k => sing fun z => φ (x + (2 * ρs (sub k)) • z)) ((2 : ℝ≥0∞) ^ (-ℓ) / 8) hℓ
    (hclosed ψ hψF) hψ0 hε
    (hconv ψ hψF (fun k z => φ (x + (2 * ρs (sub k)) • z))
      (fun k => hF φ hφ x (2 * ρs (sub k)) (hlam0 k) (hlam1 k) (hlamx k)) hψ)
  -- by A.3(2), `x + λ_{k₀} z ∈ A` with `|z| < 1/2` puts `z` in `B_{1/2}(0) ∩ sing φ_{x,λ_{k₀}}`
  have hcov : ∀ z : Euclid P, x + (2 * ρs (sub k₀)) • z ∈ A → ‖z‖ < 1 / 2 → z ∈ ⋃ j, U j := by
    intro z hzA hz
    refine hUcov k₀ le_rfl ⟨mem_ball_zero_iff.mpr hz, ?_⟩
    show z ∈ sing fun w => φ (x + (2 * ρs (sub k₀)) • w)
    rw [hsing φ hφ x (2 * ρs (sub k₀)) (hlam0 k₀) (hlam1 k₀) (hlamx k₀)]
    exact hzA.1
  exact absurd hU (not_lt.2 (Submission.adr_rescaled_content_lower_bound P ℓ A x (ρs (sub k₀)) U
    hℓ (hρ0 _) (hρD _) hcov))

/-- **Simon, proof of Theorem A.4: the induction on the invariance dimension** (step 7 of the
dimension reduction argument).  If every `L`-invariant `ψ ∈ F` with `sing ψ ≠ ∅` has `dim L ≤ d`,
then `μH[d + α](sing φ ∩ B₁(0)) = 0` for every `φ ∈ F` and `α > 0`.  Otherwise, with `ℓ = d + α`,
induction on `j ≤ d + 1` produces `ψⱼ ∈ F`, invariant under a subspace `Sⱼ` of dimension `≥ j`, with
`μH[ℓ](sing ψⱼ ∩ B₁(0)) > 0`: `adr_tangent_keeps_measure` gives a homogeneous (`{0}`-invariant)
`ψ₀`, and in the step `dim Sⱼ ≤ d < ℓ` makes `Sⱼ` `μH[ℓ]`-null, so a good point `x ∉ Sⱼ` of
`adr_tangent_keeps_measure` exists, whose tangent function is `(Sⱼ + ℝx)`-invariant by
`adr_tangent_invariance`.  Then `ψ_{d+1}` contradicts the bound on `d`. -/
theorem Submission.adr_dimension_bound : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ d : ℕ, (∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P), (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty → Module.finrank ℝ L ≤ d) → ∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0 := by
  intro P n Q F sing hF0 hF1 hA1 hA2 hA3c hA32 hA33 d hd φ hφ α hα
  suffices h : ∀ ℓ : ℝ, (d : ℝ) < ℓ → μH[ℓ] (sing φ ∩ ball (0 : Euclid P) 1) = 0 from
    h _ (lt_add_of_pos_right _ hα)
  intro ℓ hdℓ
  have hℓ : 0 < ℓ := (Nat.cast_nonneg d).trans_lt hdℓ
  -- Step 1: a linear subspace of dimension `≤ d` is `μH[ℓ]`-null
  have hnull : ∀ S : Submodule ℝ (Euclid P), Module.finrank ℝ S ≤ d →
      μH[ℓ] (S : Set (Euclid P)) = 0 := by
    intro S hS
    have hSℓ : (Module.finrank ℝ S : ℝ) < ℓ := lt_of_le_of_lt (by exact_mod_cast hS) hdℓ
    -- `μH[dim S]` is an additive Haar measure on `S`, finite on balls, so `μH[ℓ]` vanishes there
    have hball : ∀ r : ℕ, μH[ℓ] (closedBall (0 : S) r) = 0 := fun r =>
      (Measure.hausdorffMeasure_zero_or_top hSℓ _).resolve_right
        (isCompact_closedBall (0 : S) r).measure_lt_top.ne
    have huniv : μH[ℓ] (univ : Set S) = 0 := by
      refine measure_mono_null (fun y _ => ?_) (measure_iUnion_null hball)
      obtain ⟨r, hr⟩ := exists_nat_ge ‖y‖
      exact mem_iUnion.mpr ⟨r, mem_closedBall_zero_iff.mpr hr⟩
    -- transport along the isometric inclusion `S → ℝᴾ`
    calc μH[ℓ] (S : Set (Euclid P)) = μH[ℓ] (S.subtypeₗᵢ '' univ) := by simp
      _ = μH[ℓ] (univ : Set S) := S.subtypeₗᵢ.isometry.hausdorffMeasure_image (Or.inl hℓ.le) _
      _ = 0 := huniv
  -- a set of positive measure has a point off a null set `N` with a property `p` failing only on
  -- a null set
  have hgood : ∀ (A N : Set (Euclid P)) (p : Euclid P → Prop), 0 < μH[ℓ] A →
      μH[ℓ] {x | x ∈ A ∧ ¬ p x} = 0 → μH[ℓ] N = 0 → ∃ x ∈ A, x ∉ N ∧ p x := by
    intro A N p hA hbad hN
    by_contra hcon
    refine hA.ne' (measure_mono_null (fun x hx => ?_) (measure_union_null hbad hN))
    by_cases hxN : x ∈ N
    · exact Or.inr hxN
    · exact Or.inl ⟨hx, fun h => hcon ⟨x, hx, hxN, h⟩⟩
  have hne : ∀ ψ : Euclid P → Euclid Q, 0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1) →
      (sing ψ).Nonempty := fun ψ h => (nonempty_of_measure_ne_zero h.ne').left
  by_contra h0
  have hpos : 0 < μH[ℓ] (sing φ ∩ ball (0 : Euclid P) 1) := pos_iff_ne_zero.mpr h0
  -- Step 2: the claim `C(j)`, with `dim Sⱼ ≥ j`
  have key : ∀ j : ℕ, ∃ ψ ∈ F, ∃ S : Submodule ℝ (Euclid P), j ≤ Module.finrank ℝ S ∧
      (∀ y ∈ S, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧
      0 < μH[ℓ] (sing ψ ∩ ball (0 : Euclid P) 1) := by
    intro j
    induction j with
    | zero =>
      -- Step 3: a homogeneous tangent function of positive measure; homogeneity is
      -- `{0}`-invariance
      obtain ⟨x, -, -, lams, ψ, -, -, -, -, hψF, -, hψhom, hψpos⟩ :=
        hgood _ ∅ _ hpos (Submission.adr_tangent_keeps_measure P n Q F sing hA1 hA2 hA3c hA32 hA33
          ℓ hℓ φ hφ) measure_empty
      refine ⟨ψ, hψF, ⊥, Nat.zero_le _, fun y hy lam hlam z => ?_, hψpos⟩
      rw [(Submodule.mem_bot ℝ).mp hy, zero_add]
      exact hψhom lam hlam z
    | succ j ih =>
      -- Step 4: blow up `ψⱼ` at a good point `x ∉ Sⱼ`
      obtain ⟨ψ, hψF, S, hjS, hSinv, hψpos⟩ := ih
      have hSd : Module.finrank ℝ S ≤ d := hd ψ hψF S hSinv (hne ψ hψpos)
      obtain ⟨x, -, hxS, lams, ψ', hlam0, hlam1, hlamx, hlim, hψ'F, hconv, hψ'hom, hψ'pos⟩ :=
        hgood _ _ _ hψpos (Submission.adr_tangent_keeps_measure P n Q F sing hA1 hA2 hA3c hA32
          hA33 ℓ hℓ ψ hψF) (hnull S hSd)
      refine ⟨ψ', hψ'F, S ⊔ Submodule.span ℝ {x}, ?_,
        Submission.adr_tangent_invariance P n Q F hF0 hF1 hA1 ψ hψF S hSinv x lams ψ' hlam0 hlim
          (fun k => hA1 ψ hψF x (lams k) (hlam0 k) (hlam1 k) (hlamx k)) hψ'F hψ'hom hconv,
        hψ'pos⟩
      rw [Submodule.finrank_sup_span_singleton hxS]
      omega
  -- Step 5: `C(d + 1)` contradicts the bound on `d`
  obtain ⟨ψ, hψF, S, hS, hSinv, hψpos⟩ := key (d + 1)
  have := hd ψ hψF S hSinv (hne ψ hψpos)
  omega

/-- **Simon, proof of A.4 (p. 228), `sing ψ = T`.**  Let `d` bound `dim L` for every subspace `L`
such that some `ψ ∈ F` with `sing ψ ≠ ∅` satisfies `ψ(y + λx) = ψ(x)` for `y ∈ L`, `λ > 0`.  If
`φ ∈ F` with `sing φ ≠ ∅` is invariant in this sense under a `d`-dimensional `L`, then
`sing φ = L`: `L ⊆ sing φ` by A.3(2), and a singular point outside `L`, rescaled to `x` with
`‖x‖ = 1/2`, would give by A.2 a tangent function at `x` that is singular at `0` (A.3(3)) and
invariant under the `(d + 1)`-dimensional `L + ℝx`. -/
theorem Submission.adr_extremal_sing_eq : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → ∀ d : ℕ, (∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P), (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty → Module.finrank ℝ L ≤ d) → ∀ φ ∈ F, ∀ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d → (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, φ (y + lam • x) = φ x) → (sing φ).Nonempty → sing φ = (L : Set (Euclid P)) := by
  intro P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd φ hφ L hLdim hLinv hne
  -- Lemma S: `y + λ ·` (`y ∈ L`, `λ > 0`) preserves `sing φ`, and `L ⊆ sing φ`
  have hpre : ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam →
      (fun x => y + lam • x) ⁻¹' sing φ = sing φ := by
    intro y hy lam hlam hlam1 hy1
    rw [← hA32 φ hφ y lam hlam hlam1 hy1, funext fun x => hLinv y hy lam hlam x]
  obtain ⟨hinv, hLsub⟩ :=
    Submission.adr_affine_invariant_closed_set P (sing φ) L (hclosed φ hφ) hpre
  refine Set.Subset.antisymm (fun z hz => ?_) (hLsub hne)
  by_contra hzL
  -- rescale a singular point `z ∉ L` to `x ∈ sing φ ∖ L` with `‖x‖ = 1/2`
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 fun h => hzL (h ▸ L.zero_mem)
  set c : ℝ := 1 / (2 * ‖z‖) with hc
  have hc0 : 0 < c := by positivity
  set x : Euclid P := c • z with hx
  have hxs : x ∈ sing φ := by simpa using (hinv 0 L.zero_mem c hc0 z).2 hz
  have hxn : ‖x‖ = 1 / 2 := by
    rw [hx, norm_smul, Real.norm_of_nonneg hc0.le, hc]
    field_simp
  have hxL : x ∉ L := fun h => hzL <| by
    simpa [hx, smul_smul, inv_mul_cancel₀ hc0.ne'] using L.smul_mem c⁻¹ h
  -- A.2 at `x` along `Λ k = (1/2)/(k + 2) ≤ 1/4`: a homogeneous tangent function `ψ`
  set Λ : ℕ → ℝ := fun k => (1 / 2) / ((k : ℝ) + 2) with hΛ
  have hΛpos : ∀ k, 0 < Λ k := fun k => by positivity
  have hΛanti : StrictAnti Λ := fun a b hab =>
    div_lt_div_of_pos_left (by norm_num) (by positivity)
      (by simpa using (Nat.cast_lt.2 hab : (a : ℝ) < b))
  have hΛlim : Tendsto Λ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hΛle : ∀ k, Λ k ≤ 1 / 4 := fun k => by
    rw [hΛ, div_le_iff₀ (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  obtain ⟨sub, ψ, hsub, hψ, hconv, hhom⟩ :=
    hA2 φ hφ x (by rw [hxn]; norm_num) Λ hΛpos hΛanti hΛlim
  have hk : ∀ k, 0 < Λ (sub k) ∧ Λ (sub k) < 1 ∧ ‖x‖ ≤ 1 - Λ (sub k) := fun k =>
    ⟨hΛpos _, by linarith [hΛle (sub k)], by linarith [hΛle (sub k)]⟩
  have hφk : ∀ k, (fun z => φ (x + Λ (sub k) • z)) ∈ F := fun k =>
    hA1 φ hφ x _ (hk k).1 (hk k).2.1 (hk k).2.2
  -- Lemma T: `0 ∈ sing ψ`, since `0 ∈ B₁(0) ∩ sing φ_{x,λ_k}` by A.3(2)
  have hψs : (0 : Euclid P) ∈ sing ψ :=
    Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
      (fun k z => φ (x + Λ (sub k) • z)) hφk hconv (fun _ => 0) 0
      (fun k => ⟨mem_ball_self one_pos, by
        rw [hA32 φ hφ x _ (hk k).1 (hk k).2.1 (hk k).2.2, Set.mem_preimage, smul_zero, add_zero]
        exact hxs⟩)
      tendsto_const_nhds
  -- Lemma I: `ψ` is invariant under `L + ℝx`, of dimension `d + 1`, contradicting the bound `d`
  have hdim := hd ψ hψ (L ⊔ Submodule.span ℝ {x})
    (Submission.adr_tangent_invariance P n Q F hH0 hH1 hA1 φ hφ L hLinv x (fun k => Λ (sub k)) ψ
      (fun k => (hk k).1) (hΛlim.comp hsub.tendsto_atTop) hφk hψ hhom hconv) ⟨0, hψs⟩
  rw [Submodule.finrank_sup_span_singleton hxL, hLdim] at hdim
  omega

/-- **Simon A.4, last claim (p. 228).**  If `sing φ ∩ B₁(0)` is `μH[1]`-null for every `φ ∈ F`
(the case `d = 0`), then `sing φ ∩ B_σ(0)` is finite for `σ < 1`.  Otherwise
`adr_secant_rescaling_of_infinite` gives `x`, `|x| < 1`, admissible scales `λₖ ↓ 0` and points
`zₖ → z`, `|zₖ| = |z| = 1/2`, with `x + λₖzₖ ∈ sing φ`.  A.2 gives a homogeneous `ψ ∈ F` with
`φ_{x,λₖ'} ⇀ ψ`; by A.1 and A.3(2), `zₖ' ∈ B₁(0) ∩ sing φ_{x,λₖ'}`, so `z ∈ sing ψ`
(`adr_sing_mem_of_tendsto`).  Homogeneity and A.3(2) make the closed set `sing ψ` invariant
under the dilations `w ↦ λw` (`adr_affine_invariant_closed_set` with `L = {0}`), so it contains
the segment `(0, z]` and `μH[1](sing ψ ∩ B₁(0)) > 0` (`adr_radial_segment_hausdorff_pos`),
contradicting the hypothesis for `ψ`. -/
theorem Submission.adr_finite_of_dim_zero : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, μH[1] (sing φ ∩ ball (0 : Euclid P) 1) = 0) → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite := by
  intro P n Q F sing hA1 hA2 hclosed hA32 hA33 hnull φ hφ σ hσ
  refine Set.not_infinite.1 fun hinf => ?_
  -- an accumulation point `x` of `sing φ`, admissible scales and rescaled singular points
  obtain ⟨x, lams, zs, z, hx, hpos, hanti, hlim, hlt, hle, hmem, hzs, hzlim, hz⟩ :=
    Submission.adr_secant_rescaling_of_infinite P (sing φ) σ hσ hinf
  -- A.2: a homogeneous tangent function `ψ` of `φ` at `x`
  obtain ⟨sub, ψ, hsub, hψ, hconv, hhom⟩ := hA2 φ hφ x hx lams hpos hanti hlim
  -- A.1 and A.3(2): `zₖ'` is a singular point of the blow-up `φ_{x,λₖ'}` in `B₁(0)`
  have hzsing : ∀ k, zs (sub k) ∈ ball (0 : Euclid P) 1 ∩
      sing (fun w => φ (x + lams (sub k) • w)) := fun k =>
    ⟨by rw [mem_ball_zero_iff, hzs]; norm_num, by
      rw [hA32 φ hφ x (lams (sub k)) (hpos _) (hlt _) (hle _)]
      exact hmem (sub k)⟩
  -- Lemma T: `z ∈ sing ψ`
  have hzψ : z ∈ sing ψ :=
    Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
      (fun k w => φ (x + lams (sub k) • w))
      (fun k => hA1 φ hφ x (lams (sub k)) (hpos _) (hlt _) (hle _)) hconv
      (fun k => zs (sub k)) z hzsing (hzlim.comp hsub.tendsto_atTop)
  -- Lemma S with `L = {0}`: `t • w ∈ sing ψ ↔ w ∈ sing ψ` for `t > 0`
  have hray := (Submission.adr_affine_invariant_closed_set P (sing ψ) ⊥ (hclosed ψ hψ)
    fun y hy lam hlam hlam1 hy1 => by
      obtain rfl := (Submodule.mem_bot ℝ).1 hy
      have hdil : (fun w => ψ (0 + lam • w)) = ψ := funext fun w => by
        rw [zero_add]
        exact hhom lam hlam w
      have h := hA32 ψ hψ 0 lam hlam hlam1 hy1
      rw [hdil] at h
      exact h.symm).1 0 (Submodule.zero_mem ⊥)
  -- the segment `(0, z]` lies in `sing ψ`, so `sing ψ ∩ B₁(0)` is not `μH[1]`-null
  have hz0 : z ≠ 0 := by
    rintro rfl
    norm_num at hz
  have hseg := Submission.adr_radial_segment_hausdorff_pos P (sing ψ) z hz0
    (by rw [hz]; norm_num) fun t ht _ => by simpa using (hray t ht z).2 hzψ
  exact hseg.ne' (hnull ψ hψ)

/-- **Simon A.4 (Theorem, pp. 226–228)**, with the additional hypothesis (H0) that members of `F`
agreeing `μH[n]`-a.e. are equal.  Let `d` be the largest dimension of a subspace `L` such that some
`ψ ∈ F` with `sing ψ ≠ ∅` satisfies `ψ(y + λx) = ψ(x)` for all `y ∈ L`, `λ > 0`.  A tangent
function at a singular point in `B₁(0)` (A.2, A.3(2), A.3(3)) shows that `L = {0}` qualifies, and
Remark A.5 with A.3(1) gives `d ≤ n − 1`.  The dimension bound, `sing ψ = L` for an extremal `ψ`
and finiteness when `d = 0` are `adr_dimension_bound`, `adr_extremal_sing_eq` and
`adr_finite_of_dim_zero`. -/
theorem Submission.abstract_dimension_reduction : ∀ (P n Q : ℕ) (F : Set (Euclid P → Euclid Q)) (sing : (Euclid P → Euclid Q) → Set (Euclid P)), (∀ φ ∈ F, ∀ ψ ∈ F, (∀ᵐ x ∂μH[(n : ℝ)], φ x = ψ x) → φ = ψ) → (∀ φ ∈ F, LocallyIntegrable φ μH[(n : ℝ)]) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → (fun x => φ (y + lam • x)) ∈ F) → (∀ φ ∈ F, ∀ y : Euclid P, ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ k, 0 < lams k) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ψ : Euclid P → Euclid Q), StrictMono sub ∧ ψ ∈ F ∧ (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φ (y + lams (sub k) • x) ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • ψ x ∂μH[(n : ℝ)]))) ∧ ∀ lam : ℝ, 0 < lam → ∀ x, ψ (lam • x) = ψ x) → (∀ φ ∈ F, IsClosed (sing φ)) → (∀ φ ∈ F, ∀ (L : Submodule ℝ (Euclid P)) (c : Euclid Q), Module.finrank ℝ L = n → φ = Set.indicator (L : Set (Euclid P)) (fun _ => c) → sing φ = ∅) → (∀ φ ∈ F, ∀ (y : Euclid P) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → sing (fun x => φ (y + lam • x)) = (fun x => y + lam • x) ⁻¹' sing φ) → (∀ φ ∈ F, ∀ φs : ℕ → Euclid P → Euclid Q, (∀ k, φs k ∈ F) → (∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ x, f x • φs k x ∂μH[(n : ℝ)]) atTop (𝓝 (∫ x, f x • φ x ∂μH[(n : ℝ)]))) → ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k ≥ k₀, ball (0 : Euclid P) 1 ∩ sing (φs k) ⊆ {x | ∃ z ∈ sing φ, dist x z < ε}) → (∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅) ∨ ∃ d : ℕ, d + 1 ≤ n ∧ (∀ φ ∈ F, ∀ α : ℝ, 0 < α → μH[(d : ℝ) + α] (sing φ ∩ ball (0 : Euclid P) 1) = 0) ∧ (∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P), Module.finrank ℝ L = d ∧ sing ψ = (L : Set (Euclid P)) ∧ ∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (d = 0 → ∀ φ ∈ F, ∀ σ : ℝ, σ < 1 → (sing φ ∩ ball (0 : Euclid P) σ).Finite) := by
  intro P n Q F sing hH0 hH1 hA1 hA2 hclosed hplane hA32 hA33
  by_cases hI : ∀ φ ∈ F, ball (0 : Euclid P) 1 ∩ sing φ = ∅
  · exact Or.inl hI
  refine Or.inr ?_
  obtain ⟨φ₀, hφ₀, x₀, hx₀, hx₀s⟩ : ∃ φ ∈ F, (ball (0 : Euclid P) 1 ∩ sing φ).Nonempty := by
    by_contra h
    exact hI fun φ hφ => Set.not_nonempty_iff_eq_empty.1 fun hne => h ⟨φ, hφ, hne⟩
  -- `D`: dimensions of subspaces leaving invariant a member of `F` with nonempty singular set
  obtain ⟨D, hD⟩ : ∃ D : Set ℕ, ∀ m, m ∈ D ↔ ∃ ψ ∈ F, ∃ L : Submodule ℝ (Euclid P),
      (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) ∧ (sing ψ).Nonempty ∧
        Module.finrank ℝ L = m :=
    ⟨_, fun _ => Iff.rfl⟩
  -- Remark A.5 and A.3(1): `D` lies below `n`
  have hDlt : ∀ m ∈ D, m < n := by
    intro m hm
    obtain ⟨ψ, hψ, L, hinv, hne, rfl⟩ := (hD m).1 hm
    by_contra hle
    obtain ⟨L', hL', hψL'⟩ :=
      Submission.adr_invariant_eq_indicator P n Q ψ L (hH1 ψ hψ) (not_lt.1 hle) hinv
    exact hne.ne_empty (hplane ψ hψ L' (ψ 0) hL' hψL')
  -- A.2, A.3(2) and Lemma T: a homogeneous tangent function at `x₀` is singular at `0`
  have hD0 : 0 ∈ D := by
    have hx₀n : ‖x₀‖ < 1 := mem_ball_zero_iff.1 hx₀
    have hr : 0 < 1 - ‖x₀‖ := sub_pos.2 hx₀n
    set lams : ℕ → ℝ := fun k => (1 - ‖x₀‖) / ((k : ℝ) + 2)
    have hpos : ∀ k, 0 < lams k := fun k => div_pos hr (by positivity)
    have hsmall : ∀ k, lams k < 1 - ‖x₀‖ := fun k =>
      div_lt_self hr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hanti : StrictAnti lams := fun a b hab =>
      div_lt_div_of_pos_left hr (by positivity) (by linarith [(Nat.cast_lt.2 hab : (a : ℝ) < b)])
    have hlim : Tendsto lams atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    obtain ⟨sub, ψ, -, hψ, hconv, hhom⟩ := hA2 φ₀ hφ₀ x₀ hx₀n lams hpos hanti hlim
    have hk : ∀ k, 0 < lams (sub k) ∧ lams (sub k) < 1 ∧ ‖x₀‖ ≤ 1 - lams (sub k) := fun k =>
      ⟨hpos _, by linarith [hsmall (sub k), norm_nonneg x₀], by linarith [hsmall (sub k)]⟩
    have hsing0 : (0 : Euclid P) ∈ sing ψ :=
      Submission.adr_sing_mem_of_tendsto P n Q F sing hclosed hA33 ψ hψ
        (fun k x => φ₀ (x₀ + lams (sub k) • x))
        (fun k => hA1 φ₀ hφ₀ x₀ _ (hk k).1 (hk k).2.1 (hk k).2.2) hconv (fun _ => 0) 0
        (fun k => ⟨mem_ball_self one_pos, by
          rw [hA32 φ₀ hφ₀ x₀ _ (hk k).1 (hk k).2.1 (hk k).2.2, Set.mem_preimage, smul_zero,
            add_zero]
          exact hx₀s⟩)
        tendsto_const_nhds
    refine (hD 0).2 ⟨ψ, hψ, ⊥, fun y hy lam hlam x => ?_, ⟨0, hsing0⟩, finrank_bot ℝ (Euclid P)⟩
    rw [(Submodule.mem_bot ℝ).1 hy, zero_add]
    exact hhom lam hlam x
  -- `d := max D`
  obtain ⟨d, hdD, hdmax⟩ : ∃ d ∈ D, ∀ m ∈ D, m ≤ d :=
    have hbdd : BddAbove D := ⟨n, fun m hm => (hDlt m hm).le⟩
    ⟨sSup D, Nat.sSup_mem ⟨0, hD0⟩ hbdd, fun m hm => le_csSup hbdd hm⟩
  have hd : ∀ ψ ∈ F, ∀ L : Submodule ℝ (Euclid P),
      (∀ y ∈ L, ∀ lam : ℝ, 0 < lam → ∀ x, ψ (y + lam • x) = ψ x) → (sing ψ).Nonempty →
        Module.finrank ℝ L ≤ d :=
    fun ψ hψ L hinv hne => hdmax _ ((hD _).2 ⟨ψ, hψ, L, hinv, hne, rfl⟩)
  have hdim := Submission.adr_dimension_bound P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd
  obtain ⟨ψ, hψ, L, hinv, hne, hL⟩ := (hD d).1 hdD
  refine ⟨d, hDlt d hdD, hdim, ⟨ψ, hψ, L, hL, ?_, hinv⟩, fun hd0 => ?_⟩
  · exact Submission.adr_extremal_sing_eq P n Q F sing hH0 hH1 hA1 hA2 hclosed hA32 hA33 d hd
      ψ hψ L hL hinv hne
  · subst hd0
    refine Submission.adr_finite_of_dim_zero P n Q F sing hA1 hA2 hclosed hA32 hA33
      fun φ hφ => ?_
    have h1 := hdim φ hφ 1 one_pos
    rwa [Nat.cast_zero, zero_add] at h1

/-- **Simon 7.3.3**, step 1 of the class reduction (Remark 3.4, proof of 3.3(2)): for any measure
`μ` on `ℝᴾ` the upper density `limsup_{ρ↓0} μ(B_ρ(x))/(ωₙρⁿ)` is Borel in `x`.  `x ↦ μ(B_ρ(x))`
is lower semicontinuous by continuity from below on the balls `B_{ρ−1/(m+1)}(x) ↑ B_ρ(x)`;
dividing by `ωₙρⁿ ≠ 0` and taking suprema over `ρ ∈ (0, 1/(m+1))` keeps lower semicontinuity,
and the `limsup` along `𝓝[>] 0` is the infimum over `m ∈ ℕ` of these suprema. -/
theorem Submission.idtp_fons_cr_density_measurable : ∀ (P n : ℕ) (μ : Measure (Euclid P)), Measurable (fun x : Euclid P => (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) := by
  intro P n μ
  -- `x ↦ μ(B_ρ(x))` is lower semicontinuous: `B_ρ(x)` is the increasing union of the balls
  -- `B_{ρ - 1/(m+1)}(x)`, each contained in `B_ρ(x')` for `|x' - x| < 1/(m+1)`
  have hball : ∀ ρ : ℝ, LowerSemicontinuous fun x : Euclid P => μ (ball x ρ) := by
    intro ρ x t ht
    have hU : ⋃ m : ℕ, ball x (ρ - 1 / ((m : ℝ) + 1)) = ball x ρ := by
      ext z
      simp only [mem_iUnion, mem_ball]
      constructor
      · rintro ⟨m, hm⟩
        linarith [Nat.one_div_pos_of_nat (α := ℝ) (n := m)]
      · intro hz
        obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
        exact ⟨m, by linarith⟩
    have hmono : Monotone fun m : ℕ => ball x (ρ - 1 / ((m : ℝ) + 1)) := fun a b hab =>
      ball_subset_ball (sub_le_sub_left (Nat.one_div_le_one_div hab) ρ)
    have ht' : t < μ (⋃ m : ℕ, ball x (ρ - 1 / ((m : ℝ) + 1))) := by
      rw [hU]
      exact ht
    obtain ⟨m, hm⟩ := ((tendsto_measure_iUnion_atTop (μ := μ) hmono).eventually
      (lt_mem_nhds ht')).exists
    filter_upwards [ball_mem_nhds x (Nat.one_div_pos_of_nat (α := ℝ) (n := m))] with x' hx'
    refine hm.trans_le (measure_mono (ball_subset_ball' ?_))
    rw [mem_ball, dist_comm] at hx'
    linarith
  -- dividing by `ωₙρⁿ ≠ 0` preserves lower semicontinuity
  have hω : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hg : ∀ ρ : ℝ, 0 < ρ → LowerSemicontinuous fun x : Euclid P =>
      μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) := fun ρ hρ =>
    (ENNReal.continuous_div_const _ (mul_ne_zero hω (ENNReal.ofReal_pos.2 (pow_pos hρ n)).ne')
      ).comp_lowerSemicontinuous (hball ρ) fun a b hab => ENNReal.div_le_div_right hab _
  -- the `limsup` along `𝓝[>] 0` is the countable infimum over the basis `(0, 1/(m+1))`
  have hbasis := nhdsWithin_hasBasis (nhds_basis_ball_inv_nat_succ (x := (0 : ℝ))) (Ioi 0)
  simp_rw [hbasis.limsup_eq_iInf_iSup]
  exact Measurable.ennreal_toReal (Measurable.iInf fun m => Measurable.iInf fun _ =>
    (lowerSemicontinuous_biSup fun ρ hρ => hg ρ hρ.2).measurable)
/-- **Simon 7.3.3, proof of 3.3(2)**, rescaling (chapter-07.txt lines 512–583, with Remark 3.4,
lines 380–398): for `t > 0` let `μ^{y,t} = t⁻ⁿ (η_{y,t})_# μ`.  As
`η_{y,t}⁻¹(B_ρ(w)) = B_{tρ}(y + tw)`, `μ^{y,t}(B_ρ(w)) = t⁻ⁿ μ(B_{tρ}(y + tw))`, so the density
ratio of `μ^{y,t}` at `(w, ρ)` is that of `μ` at `(y + tw, tρ)`; since `ρ ↦ tρ` maps `𝓝[>] 0`
onto itself the upper densities agree, and since `t⁻ⁿ ≠ 0` every ball about `w` has positive
`μ^{y,t}`-measure iff every ball about `y + tw` has positive `μ`-measure. -/
theorem Submission.idtp_fons_cr_density_rescale : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (y : Euclid P) (t : ℝ), 0 < t → (∀ w : Euclid P, limsup (fun ρ : ℝ => (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => μ (ball (y + t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)) ∧ ∀ w : Euclid P, (∀ ε : ℝ, 0 < ε → (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ε) ≠ 0) ↔ ∀ ε : ℝ, 0 < ε → μ (ball (y + t • w) ε) ≠ 0 := by
  intro P n μ y t ht
  -- `η_{y,t}⁻¹(B_ρ(w)) = B_{tρ}(y + tw)`, so `μ^{y,t}(B_ρ(w)) = t⁻ⁿ μ(B_{tρ}(y + tw))`
  have hball : ∀ (w : Euclid P) (ρ : ℝ), (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t))
      (ball w ρ) = ENNReal.ofReal (t⁻¹ ^ n) * μ (ball (y + t • w) (t * ρ)) := by
    intro w ρ
    have hmeas : Measurable (dilation y t) :=
      (continuous_const.add (dilationCLM P t).continuous).measurable
    have hpre : dilation y t ⁻¹' ball w ρ = ball (y + t • w) (t * ρ) := by
      ext z
      have hz : dilation y t z - w = t⁻¹ • (z - (y + t • w)) := by
        change -(t⁻¹ • y) + t⁻¹ • z - w = _
        rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
        abel
      rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hz, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.2 ht.le), inv_mul_lt_iff₀ ht]
    rw [Measure.smul_apply, Measure.map_apply hmeas measurableSet_ball, hpre, smul_eq_mul]
  refine ⟨fun w => ?_, fun w => ?_⟩
  · -- the density ratio of `μ^{y,t}` at `(w, ρ)` is that of `μ` at `(y + tw, tρ)`
    set H : ℝ → ℝ≥0∞ := fun r => μ (ball (y + t • w) r) / (unitBallVolume n * ENNReal.ofReal (r ^ n))
    have hk0 : ENNReal.ofReal (t ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos ht n)).ne'
    have hfun : (fun ρ : ℝ => (ENNReal.ofReal (t⁻¹ ^ n) • μ.map (dilation y t)) (ball w ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) = H ∘ (t * ·) := by
      funext ρ
      rw [comp_apply, hball]
      simp only [H, mul_pow, ENNReal.ofReal_mul (pow_nonneg ht.le n), inv_pow,
        ENNReal.ofReal_inv_of_pos (pow_pos ht n), div_eq_mul_inv]
      rw [mul_left_comm (unitBallVolume n), ENNReal.mul_inv (Or.inl hk0) (Or.inl ENNReal.ofReal_ne_top)]
      ring
    -- `ρ ↦ tρ` maps `𝓝[>] 0` onto itself
    have hmap : map (t * ·) (𝓝[>] (0 : ℝ)) = 𝓝[>] 0 := by
      conv_lhs => rw [← comap_mulLeft_nhdsGT_zero ht]
      exact map_comap_of_surjective (mul_left_surjective₀ ht.ne') _
    rw [hfun, limsup_comp, hmap]
  · -- `t⁻ⁿ ≠ 0` and `ε ↦ tε` is a bijection of `(0, ∞)`
    have hc : ENNReal.ofReal (t⁻¹ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.2 ht) n)).ne'
    simp only [hball, ne_eq, mul_eq_zero, hc, false_or]
    constructor
    · intro h δ hδ
      have := h (δ / t) (div_pos hδ ht)
      rwa [mul_div_cancel₀ δ ht.ne'] at this
    · intro h ε hε
      exact h (t * ε) (mul_pos ht hε)
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
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- **Approximate tangent spaces under dilation** (Simon Ch. 3, 1.4).  For `c > 0` the blow-ups
of `c⁻¹M = {x : cx ∈ M}` at `z` are blow-ups of `M` at `cz`: `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)`, as
`(cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z)`.  Since `cr ↓ 0` as `r ↓ 0`, the limits defining `Q` as the
approximate tangent space of `M` at `cz` give the limits for `c⁻¹M` at `z`. -/
theorem Submission.approx_tangent_space_smul_preimage : ∀ (P n : ℕ) (M : Set (Euclid P)) (c : ℝ) (z : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < c → HasApproximateTangentSpaceAt n M (c • z) Q → HasApproximateTangentSpaceAt n ((fun x => c • x) ⁻¹' M) z Q := by
  intro P n M c z Q hc hT
  have hc0 : c ≠ 0 := hc.ne'
  -- `η_{cz,cr}(m) = (cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z) = η_{z,r}(c⁻¹m)`
  have hη : ∀ (r : ℝ) (m : Euclid P), Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) m =
      Poincare.SimonGMT.Chapter03.blowUpMap z r (c⁻¹ • m) := by
    intro r m
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, Poincare.SimonGMT.Chapter03.blowUpMap, mul_inv_rev,
      ← smul_smul, smul_sub c⁻¹, inv_smul_smul₀ hc0]
  -- `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)` for every `r`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap z r '' ((fun x => c • x) ⁻¹' M) =
      Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) '' M := by
    intro r
    ext y
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨c • m', hm', by rw [hη, inv_smul_smul₀ hc0]⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c⁻¹ • m, ?_, (hη r m).symm⟩
      show c • c⁻¹ • m ∈ M
      rwa [smul_inv_smul₀ hc0]
  -- `r ↦ cr` tends to `0` within `(0, ∞)`: it is continuous, vanishes at `0` and is positive
  -- for `r > 0`
  have hφ : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := (continuous_const_mul c).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  -- the limit at `cz` along `cr ↓ 0` is the limit at `z` along `r ↓ 0`
  refine ⟨hT.1, fun f => ((hT.2 f).comp hφ).congr fun r => ?_⟩
  rw [Function.comp_apply, hset r]

/-- **Dilating an integer multiplicity triple** (Simon Ch. 6, 3.1 and 2.23).  For `c > 0` and
`T x = c • x`, the triple `(T⁻¹M, θ ∘ T, ξ ∘ T)` is again integer multiplicity in `ℝᴾ`.  By the
change of variables `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M`, null sets, local integrability and
`Hⁿ⌞M`-a.e. statements transfer through the measurable embedding `T`; the maps `c⁻¹ • Fⱼ`
parametrize `T⁻¹M`, and approximate tangent spaces are dilation invariant. -/
theorem Submission.imrep_univ_smul_rescale_exists : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x) := by
  intro P n R c hc
  have hc0 : c ≠ 0 := hc.ne'
  -- `T x = c • x` is a homeomorphism of `ℝᴾ`, hence measurable and a measurable embedding
  have hT : Measurable (fun x : Euclid P => c • x) := measurable_const_smul c
  have hTemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc0).measurableEmbedding
  -- (CV): `T_#(Hⁿ⌞T⁻¹S) = c⁻ⁿ Hⁿ⌞S` and the lower-integral change of variables, for every `S`
  have hCV := Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
  -- (∗) `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M` for `M = R.carrier`
  have hstar := (hCV R.carrier).1
  refine ⟨{ carrier := (fun x : Euclid P => c • x) ⁻¹' R.carrier
            mult := fun x => R.mult (c • x)
            orient := fun x => R.orient (c • x)
            measurableSet_carrier := hT R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp hT
            mult_pos := fun x hx => R.mult_pos (c • x) hx
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl⟩
  · -- rectifiability: `T⁻¹M ⊆ T⁻¹M₀ ∪ ⋃ⱼ range (c⁻¹ • Fⱼ)` with `Hⁿ(T⁻¹M₀) = 0`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun x : Euclid P => c • x) ⁻¹' M₀, ?_, fun j w => c⁻¹ • F j w, fun j => ?_, ?_⟩
    · -- evaluate `T_#(Hⁿ⌞T⁻¹M₀) = c⁻ⁿ Hⁿ⌞M₀` on `univ`
      have h := congrArg (fun μ : Measure (Euclid P) => μ univ) (hCV M₀).1
      simp only at h
      rwa [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.smul_apply, Measure.restrict_apply_univ, hM₀, smul_zero] at h
    · -- `c⁻¹ • Fⱼ` is `‖c⁻¹‖₊ Kⱼ`-Lipschitz
      obtain ⟨K, hK⟩ := hF j
      exact ⟨‖c⁻¹‖₊ * K, (lipschitzWith_smul c⁻¹).comp hK⟩
    · -- if `c • z = Fⱼ w` then `z = c⁻¹ • Fⱼ w`
      intro z hz
      rcases hcover hz with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, w, by simp only [hw, inv_smul_smul₀ hc0]⟩)
  · -- local integrability: `T⁻¹M ∩ K = T⁻¹(M ∩ T(K))` with `T(K)` compact
    intro K hK _
    have hTK : IsCompact ((fun x : Euclid P => c • x) '' K) := hK.image (continuous_const_smul c)
    have hset : (fun x : Euclid P => c • x) ⁻¹' R.carrier ∩ K =
        (fun x : Euclid P => c • x) ⁻¹' (R.carrier ∩ (fun x : Euclid P => c • x) '' K) := by
      rw [preimage_inter, hTemb.injective.preimage_image]
    rw [hset, (hCV (R.carrier ∩ (fun x : Euclid P => c • x) '' K)).2.1 fun y => (R.mult y : ℝ≥0∞)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (R.locallyIntegrable_mult _ hTK (subset_univ _))
  · -- `ξ` is a.e.-strongly measurable for `c⁻ⁿ Hⁿ⌞M = T_#(Hⁿ⌞T⁻¹M)`; compose with `T`
    have h := R.aestronglyMeasurable_orient.smul_measure (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar] at h
    exact h.comp_aemeasurable hT.aemeasurable
  · -- the orientation statement holds `T_#(Hⁿ⌞T⁻¹M)`-a.e., i.e. at `c • z` for a.e. `z ∈ T⁻¹M`;
    -- there `Q` is also the approximate tangent space of `T⁻¹M` at `z`
    have h := Measure.ae_smul_measure R.orients (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar, hTemb.ae_map_iff] at h
    filter_upwards [h] with z ⟨Q, hQ, hξ⟩
    exact ⟨Q, Submission.approx_tangent_space_smul_preimage P n R.carrier c z Q hc hQ, hξ⟩
/-- **A cone takes equal values on dilated test forms** (Simon 7.3.1(2), via 6.2.23).
If `C ∈ 𝒟ₙ(ℝᴾ)` is a cone, `λ > 0` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)` defines a test
form with `C(ω') = C(ω)`.  As `η_{0,λ}(ℝᴾ) = ℝᴾ`, the cone property `η_{0,λ#}C = C` reads
`C(η_{0,λ}^# ω) = C(ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.cone_current_apply_dilation_pullback : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsConeCurrent C → ∀ lam : ℝ, 0 < lam → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) ∧ C ω' = C ω := by
  intro P n C hC lam hlam ω
  -- Step 1: the cone property `η_{0,λ#}C(ω) = C(ω)`.
  have hcone := hC lam hlam ω
  -- Step 2: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h] at hcone
  -- Steps 3–4: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω')` for the affine pullback `ω'` of `ω`,
  -- so `C(ω') = C(ω)`.
  refine ⟨_, fun y => ?_, hcone⟩
  -- Step 5: `ω'(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Action and weight of a dilated triple** (Simon 6.3.1 (‡) and Ch. 4, 1.1, under
`x ↦ cx`; used for the cone `C` of 7.3.1(2)).  If `c > 0` and `R' = (M', θ', ξ')` is
`R = (M, θ, ξ)` pulled back by `x ↦ cx`, i.e. `M' = {x : cx ∈ M}`, `θ'(x) = θ(cx)` and
`ξ'(x) = ξ(cx)`, then `τ(R')(ω) = τ(R)(ω_c)` with `ω_c(y) = c⁻ⁿ ω(c⁻¹y)` for every `n`-form `ω`,
and `μ_{R'}(A) = c⁻ⁿ μ_R(cA)` for every Borel `A`.  Both follow from the change of variables
`∫_{M'} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ`. -/
theorem Submission.imrep_smul_rescale_action_measure : ∀ (P n : ℕ) (R R' : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → R'.carrier = (fun x => c • x) ⁻¹' R.carrier → (∀ x, R'.mult x = R.mult (c • x)) → (∀ x, R'.orient x = R.orient (c • x)) → (∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action (fun y => (c⁻¹ ^ n) • ω (c⁻¹ • y))) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R'.measure A = ENNReal.ofReal (c⁻¹ ^ n) * R.measure ((fun x => c • x) '' A) := by
  intro P n R R' c hc hcar hmult horient
  -- `T x = cx` is a measurable embedding with `c⁻¹ (cz) = z`.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    measurableEmbedding_const_smul₀ hc.ne'
  have hinv : ∀ z : Euclid P, c⁻¹ • c • z = z := fun z => by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- Step 1: `R'.action ω = ∫_{T⁻¹M} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ` for
    -- `g(y) = θ(y) ξ(y)(ω(c⁻¹y))`.
    have hcv := (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      R.carrier).2.2 fun y => (R.mult y : ℝ) * R.orient y (ω (c⁻¹ • y))
    simp only [hinv] at hcv
    unfold IMRep.action
    rw [hcar]
    simp only [hmult, horient]
    -- Step 2: move `c⁻ⁿ` inside the integral and use the linearity of `ξ(y)`.
    rw [hcv, ← integral_const_mul]
    congr 1
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  · -- Step 3: `R'.measure A = ∫⁻_{A ∩ M'} θ(c·) dHⁿ`, and `A ∩ M' = T⁻¹(cA ∩ M)`.
    have hTA : MeasurableSet ((fun x : Euclid P => c • x) '' A) := hT.measurableSet_image.2 hA
    have hset : A ∩ R'.carrier =
        (fun x : Euclid P => c • x) ⁻¹' ((fun x : Euclid P => c • x) '' A ∩ R.carrier) := by
      rw [preimage_inter, preimage_image_eq _ hT.injective, hcar]
    unfold IMRep.measure
    rw [withDensity_apply _ hA, withDensity_apply _ hTA, Measure.restrict_restrict hA,
      Measure.restrict_restrict hTA, hset]
    simp only [hmult]
    -- Step 4: the lower-integral change of variables on `cA ∩ M`.
    exact (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      ((fun x : Euclid P => c • x) '' A ∩ R.carrier)).2.1 fun y => (R.mult y : ℝ≥0∞)
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl
/-- **Every current in `η(U)` is a blow-up**, `η = η_{x,λ}`, `λ > 0` (Simon Ch. 6, 2.23 and 3.9
for `η⁻¹`; used for the minimality of `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt
lines 326–338): every `S' ∈ 𝒟ₙ(η(U))` is `η_{x,λ#}S''` for some `S'' ∈ 𝒟ₙ(U)`, integer
multiplicity whenever `S'` is.  `κ = η_{−λ⁻¹x,λ⁻¹}` inverts `η`, so `κ(η(U)) = U`, and `S''` is
`κ_#S'` restricted to `U`: `dtc_blowUp_testForm_corr` for `η` and for `κ` gives
`η_#S''(ω) = λ⁻ⁿ κ_#S'(ω ∘ η) = λ⁻ⁿ λⁿ S'(ω)`, and a representation of `κ_#S'` in
`κ(η(U)) = U` (`dtc_blowUp_imrep`) represents `S''`. -/
theorem Submission.dtc_blowUp_preimage : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (S' : GeometricCurrentOn (dilation x lam '' U) n), ∃ S'' : GeometricCurrentOn U n, blowUp S'' x lam hlam.ne' = S' ∧ (IsIntegerMultiplicity S' → IsIntegerMultiplicity S'') := by
  intro P n U x lam hlam S'
  have hlam' : 0 < lam⁻¹ := inv_pos.mpr hlam
  -- `κ = η_{−λ⁻¹x,λ⁻¹}`, `κ(z) = x + λz`, is a two-sided inverse of `η = η_{x,λ}`
  have hκη : ∀ y, dilation (-(lam⁻¹ • x)) lam⁻¹ (dilation x lam y) = y := fun y => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hηκ : ∀ z, dilation x lam (dilation (-(lam⁻¹ • x)) lam⁻¹ z) = z := fun z => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hdom : dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) = U := by
    rw [image_image]
    simp only [hκη, image_id']
  have hUV : U ⊆ dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) := hdom.superset
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hblow' := (Submission.dtc_blowUp_testForm_corr P n (dilation x lam '' U)
    (-(lam⁻¹ • x)) lam⁻¹ hlam').2.2
  -- `S'' := κ_#S'`, restricted from `κ(η(U)) = U` to `U`
  refine ⟨(blowUp S' (-(lam⁻¹ • x)) lam⁻¹ hlam'.ne').restrictDomain hUV, ?_, ?_⟩
  · -- `η_#S''(ω) = λ⁻ⁿ S''(ω ∘ η)` and `κ_#S'(ω ∘ η) = λⁿ S'(ω)`, as `ω ∘ η ∘ κ = ω`
    ext ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow _ ω ω' hω', GeometricCurrentOn.restrictDomain_apply,
      hblow' S' (testFormOnInclusion hUV n ω') ω fun z => by
        rw [testFormOnInclusion_coe, hω', hηκ],
      ← mul_assoc, ← mul_pow, inv_inv, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]
  · -- a representation of `κ_#S'` in `κ(η(U)) = U` is one in `U`, and it represents `S''`
    rintro ⟨R₁, hR₁⟩
    obtain ⟨R₂, hR₂, -⟩ := Submission.dtc_blowUp_imrep P n (dilation x lam '' U) S'
      (-(lam⁻¹ • x)) lam⁻¹ hlam' R₁ hR₁
    exact ⟨{ R₂ with
        carrier_subset := R₂.carrier_subset.trans hdom.subset
        locallyIntegrable_mult := fun K hK hKU =>
          R₂.locallyIntegrable_mult K hK (hKU.trans hUV) },
      fun ω => hR₂ (testFormOnInclusion hUV n ω)⟩

/-- **Blow-ups preserve minimality** (Simon 7.1.1, chapter-07.txt lines 12–18, for `η = η_{x,λ}`,
`λ > 0`; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337): if `T` is
minimizing in `A`, then `η_#T` is minimizing in `η(A)`.

`η_#T` is integer multiplicity (`dtc_blowUp_imrep`).  A competitor `S'` for `η_#T` on
`W' ⊂⊂ η(U)` is `η_#S''` with `S''` integer multiplicity (`dtc_blowUp_preimage`), and `S''` is a
competitor for `T` on `W = η⁻¹(W') ⊂⊂ U`: `∂S'' = ∂T` and
`spt(S'' − T) = η⁻¹(spt(S' − η_#T)) ⊆ A ∩ W` (`dtc_blowUp_algebra`).  So
`M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')` (`dtc_blowUp_massOn_image`). -/
theorem Submission.dtc_blowUp_isMinimizingIn : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A) := by
  intro P n U A T x lam hlam hT
  obtain ⟨⟨R, hR⟩, hmin⟩ := hT
  obtain ⟨hsub, hinj, hspt, hbdry⟩ := Submission.dtc_blowUp_algebra P U x lam hlam
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨?_, fun W' S' hW'o hW'c hS'im hS'bd hS'c hS'A => ?_⟩
  · -- `η_#T` is integer multiplicity
    obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P n U T x lam hlam R hR
    exact ⟨R', hR'⟩
  -- `S' = η_#S''` with `S''` integer multiplicity
  obtain ⟨S'', rfl, hS''im⟩ := Submission.dtc_blowUp_preimage P n U x lam hlam S'
  -- `W = η⁻¹(W')` is open and `W ⊂⊂ U`, since `closure W = η⁻¹(closure W')` and `η⁻¹(η(U)) = U`
  have hWo : IsOpen (dilation x lam ⁻¹' W') := by
    rw [← he]
    exact hW'o.preimage e.continuous
  have hWc : CompactlyContained (dilation x lam ⁻¹' W') U := by
    obtain ⟨hc, hsub'⟩ := hW'c
    rw [← he] at hsub' ⊢
    refine ⟨?_, ?_⟩ <;> rw [← e.preimage_closure]
    · exact e.isCompact_preimage.2 hc
    · exact (preimage_mono hsub').trans (e.preimage_image U).subset
  -- `∂S'' = ∂T`: `η_#(∂S'') = ∂S' = ∂(η_#T) = η_#(∂T)` and `η_#` is injective
  have hbd : SameBoundary S'' T := by
    cases n with
    | zero => trivial
    | succ m =>
      show S''.boundary = T.boundary
      apply hinj
      rw [← hbdry, ← hbdry]
      exact hS'bd
  -- `spt(S' − η_#T) = η(spt(S'' − T))`, so `spt(S'' − T)` is compact and lies in `A ∩ W`
  have hspt' : (blowUp S'' x lam hlam.ne' - blowUp T x lam hlam.ne').support =
      dilation x lam '' (S'' - T).support := by
    rw [← hsub, hspt]
  rw [hspt', ← he] at hS'c hS'A
  have hc : IsCompact (S'' - T).support := e.isCompact_image.1 hS'c
  have hA : (S'' - T).support ⊆ A ∩ dilation x lam ⁻¹' W' := by
    intro y hy
    obtain ⟨⟨a, ha, hay⟩, hyW'⟩ := hS'A (mem_image_of_mem e hy)
    rw [← he]
    exact ⟨e.injective hay ▸ ha, hyW'⟩
  -- `M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')`, as `η(W) = W'`
  have hle := hmin _ S'' hWo hWc (hS''im hS'im) hbd hc hA
  have hW' : dilation x lam '' (dilation x lam ⁻¹' W') = W' := by
    rw [← he]
    exact e.image_preimage W'
  have hmT := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W')
  have hmS := Submission.dtc_blowUp_massOn_image P n U S'' x lam hlam (dilation x lam ⁻¹' W')
  rw [hW'] at hmT hmS
  rw [hmT, hmS]
  gcongr

/-- **Scaling of blow-ups** `η_{x,λ#}T`, `η = η_{x,λ}`, `λ > 0` (proof of Simon 7.3.1,
chapter-07.txt lines 326–338; push-forward 6.2.23 and 6.3.3–6.3.9): (1) the mass scaling
`M_{η(W)}(η_#T) = λ⁻ⁿ M_W(T)` of (1) there (`dtc_blowUp_massOn_image`); (2) a representation
`(M, θ, ξ)` of `T` pushes forward to one of `η_#T` with `μ_{η_#T}(B) = λ⁻ⁿ μ_T(η⁻¹(B))`
(`dtc_blowUp_imrep`); (3) `η_#T` is minimizing in `η(A)` if `T` is minimizing in `A`
(`dtc_blowUp_isMinimizingIn`).  The hypotheses `U` open and `n > 0` are not needed. -/
theorem Submission.dtc_blowUp_scaling : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsOpen U → 0 < n → (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W) ∧ (∀ R : IMRep U n, R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) ∧ (IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)) := by
  intro P n U A T x lam hlam _ _
  exact ⟨Submission.dtc_blowUp_massOn_image P n U T x lam hlam,
    Submission.dtc_blowUp_imrep P n U T x lam hlam,
    Submission.dtc_blowUp_isMinimizingIn P n U A T x lam hlam⟩
/-- **The weight of a cone is homogeneous of degree `n`** (proof of Simon 7.4.5,
chapter-07.txt lines 697–699, "by virtue of the fact that `C` is a cone").  If the cone `C` is
represented by `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` and `λ > 0`, then `μ(λA) = λⁿ μ(A)` for
every Borel `A`.  The dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, and
`R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·)) = C(λ⁻ⁿ ω(λ⁻¹·)) = C(ω)` as `η_{0,λ#}C = C`, so `R_λ` represents `C`.
By the uniqueness of the weight (Simon Ch. 6, 3.2(3)), `μ(A) = μ_{R_λ}(A) = λ⁻ⁿ μ(λA)`. -/
theorem Submission.cone_current_imrep_measure_smul_image : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n C R hC hR lam hlam A hA
  -- Step 1: the dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, with
  -- `R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·))` for every form `ω` and `μ_{R_λ}(A) = λ⁻ⁿ μ(λA)` for Borel `A`
  obtain ⟨Rl, hcar, hmult, horient⟩ := Submission.imrep_univ_smul_rescale_exists P n R lam hlam
  obtain ⟨haction, hmeasure⟩ :=
    Submission.imrep_smul_rescale_action_measure P n R Rl lam hlam hcar hmult horient
  -- Step 2: `R_λ` represents `C`: `C(ω) = C(ω') = R(ω') = R_λ(ω)` for `ω' = λ⁻ⁿ ω(λ⁻¹·)`
  have hRl : Rl.Represents C := by
    intro ω
    obtain ⟨ω', hω', hCω'⟩ := Submission.cone_current_apply_dilation_pullback P n C hC lam hlam ω
    rw [← hCω', hR ω', haction]
    congr 1
    funext y
    exact hω' y
  -- Step 3: the weight does not depend on the representation, so `μ_{R_λ} = μ` and
  -- `μ(A) = λ⁻ⁿ μ(λA)`
  have hA' := hmeasure A hA
  rw [Submission.imrep_measure_eq_of_represents_same_current P n univ C Rl R isOpen_univ hRl hR]
    at hA'
  -- Step 4: multiply by `λⁿ`, using `λⁿ λ⁻ⁿ = 1`
  have hpow : ENNReal.ofReal (lam ^ n) * ENNReal.ofReal (lam⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
      ENNReal.ofReal_one]
  rw [hA', ← mul_assoc, hpow, one_mul]
/-- **Blow-up domains eventually contain bounded sets** (Simon 7.3.3(2), proof: the domain
claims for `η_{x,σᵢ#}T`).  If `U` is open, `x ∈ U`, `λᵢ > 0` and `λᵢ → 0`, then every bounded `K`
lies in `η_{x,λᵢ}(U)` for all large `i`: with `B_δ(x) ⊆ U` and `K ⊆ B̄_r(0)`, eventually
`λᵢ(|r| + 1) < δ`, and then each `w ∈ K` is `η_{x,λᵢ}(x + λᵢw)` with `x + λᵢw ∈ B_δ(x)`. -/
theorem Submission.idtp_tpf_blowUp_domain_eventually : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lams : ℕ → ℝ), IsOpen U → x ∈ U → (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → ∀ K : Set (Euclid P), Bornology.IsBounded K → ∀ᶠ i in atTop, K ⊆ dilation x (lams i) '' U := by
  intro P U x lams hU hx hpos hlim K hK
  -- `B_δ(x) ⊆ U` and `K ⊆ B̄_r(0)`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  -- `λᵢ(|r| + 1) → 0 < δ`, so `λᵢ(|r| + 1) < δ` for all large `i`
  have hlim' : Tendsto (fun i => lams i * (|r| + 1)) atTop (𝓝 0) := by
    simpa using hlim.mul_const (|r| + 1)
  filter_upwards [hlim'.eventually (gt_mem_nhds hδ)] with i hi w hw
  -- `y = x + λᵢw` lies in `B_δ(x) ⊆ U`, and `η_{x,λᵢ}(y) = w`
  refine ⟨x + lams i • w, hball ?_, ?_⟩
  · have hw : ‖w‖ ≤ |r| + 1 := by
      linarith [mem_closedBall_zero_iff.mp (hr hw), le_abs_self r]
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hpos i).le]
    exact (mul_le_mul_of_nonneg_left hw (hpos i).le).trans_lt hi
  · simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_add,
      smul_smul, inv_mul_cancel₀ (hpos i).ne', one_smul, neg_add_cancel_left]

/-- **Weak limits of blow-ups of a cycle are cycles** (`∂C = 0` for the blow-up limit `C` in the
proof of Simon 7.3.3(2), chapter-07.txt line 512 ff.; cf. the proof of 7.3.1, lines 335–336,
where `∂η_{x,λⱼ#}T = 0` in `B_{MR}(0)` for large `j`, and Ch. 6, 2.13 and 2.24(1)).  If
`∂T = 0` in `U`, `λᵢ > 0`, `λᵢ → 0` and `η_{x,λᵢ#}T ⇀ C` in `ℝᴾ`, then `∂C = 0`: for
`ω ∈ 𝒟ᵐ(ℝᴾ)`, the compact set `spt ω ⊇ spt dω` lies in `η_{x,λᵢ}(U)` for all large `i`
(`idtp_tpf_blowUp_domain_eventually`), and there
`η_{x,λᵢ#}T(dω) = ∂(η_{x,λᵢ#}T)(ω) = η_{x,λᵢ#}(∂T)(ω) = 0`; hence
`∂C(ω) = C(dω) = limᵢ η_{x,λᵢ#}T(dω) = 0`. -/
theorem Submission.idtp_tpf_blowUp_limit_boundaryVanishes : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → BoundaryVanishes T → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T x (lams i) (hlams i).ne') C → BoundaryVanishes C := by
  intro P n U T x lams hlams C hU hx hT hlim hconv
  cases n with
  | zero => trivial
  | succ m =>
    -- step 1: `∂T = 0`, and it suffices that `∂C(ω) = C(dω) = 0` for every `ω ∈ 𝒟ᵐ(ℝᴾ)`
    change T.boundary = 0 at hT
    change C.boundary = 0
    ext ω
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply]
    -- step 2: the compact set `spt ω` lies in `η_{x,λᵢ}(U)` for all large `i`
    have hev := Submission.idtp_tpf_blowUp_domain_eventually P U x lams hU hx hlams hlim
      (tsupport (ω : DifferentialForm (Euclid P) m)) ω.property.1.2.isCompact.isBounded
    -- steps 3–4: for such `i`, `η_{x,λᵢ#}T(dω) = ∂(η_{x,λᵢ#}T)(ω) = η_{x,λᵢ#}(∂T)(ω) = 0`
    have hzero : ∀ᶠ i in atTop, currentEval (blowUp T x (lams i) (hlams i).ne')
        (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) = 0 := by
      filter_upwards [hev] with i hi
      -- `∂` commutes with the affine push-forward `η_{x,λᵢ#}` (Simon 6.2.24(1)) ...
      have hB : (blowUp T x (lams i) (hlams i).ne').boundary =
          blowUp T.boundary x (lams i) (hlams i).ne' := by
        unfold blowUp
        rw [GeometricCurrentOn.boundary_affinePushforward]
        rfl
      -- ... and the blow-up of the zero current is zero
      have h0 : blowUp (0 : GeometricCurrentOn U m) x (lams i) (hlams i).ne' = 0 := by
        ext η
        unfold blowUp
        rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
          GeometricCurrentOn.zero_apply, GeometricCurrentOn.zero_apply]
      -- `ω` is a test form in `η_{x,λᵢ}(U)`, and `currentEval` evaluates the blow-up on `dω`
      let ωi : TestFormOn (dilation x (lams i) '' U) m := ⟨ω, ω.property.1, hi⟩
      have hd : IsTestForm (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) ∧
          tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) ⊆
            dilation x (lams i) '' U :=
        ⟨exteriorDerivative_isTestForm ω.property.1,
          (tsupport_exteriorDerivative_subset _).trans hi⟩
      rw [currentEval, dite_eq_left hd]
      change (blowUp T x (lams i) (hlams i).ne').boundary ωi = 0
      rw [hB, hT, h0, GeometricCurrentOn.zero_apply]
    -- step 5: `C(dω)` is the limit of a sequence that is eventually `0`
    exact tendsto_nhds_unique (hconv (exteriorDerivativeTestOn univ m ω))
      (tendsto_const_nhds.congr' (hzero.mono fun i hi => hi.symm))

/-- **The ambient space and the calculus of the dilations** `η_{a,s}(v) = s⁻¹(v − a)`, `s > 0`,
and of the rescaled measures `ν^{a,s} = s⁻ⁿ η_{a,s#}ν` (used tacitly by Simon in the proof of
7.3.3(1), cf. (10) there, chapter-07.txt line 472): (1) `ℝᴾ` is an embedded `C²` submanifold of
itself (Simon Ch. 2, (4.1), with `ψ = id`); (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`;
(3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`; (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`;
(5) `η_{a,s}(ℝᴾ) = ℝᴾ` and `η_{a,s}` is open; (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`;
(7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`; (8) `ν^{0,1} = ν` and `η_{0,1}(A) = A`;
(9) `s⁻ⁿ η_{a,s#}(ν⌞B) = ν^{a,s}⌞η_{a,s}(B)` for Borel `B`.  All of this follows from `η_{a,s}`
being the affine homeomorphism `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`. -/
theorem Submission.idtp_fons_cc_ambient_calculus : (∀ P : ℕ, IsEmbeddedSubmanifold 2 P (univ : Set (Euclid P))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (A : Set (Euclid P)), 0 < s → MeasurableSet A → (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)) A = ENNReal.ofReal (s⁻¹ ^ n) * ν (dilation a s ⁻¹' A)) ∧ (∀ (P : ℕ) (a w : Euclid P) (s ρ : ℝ), 0 < s → dilation a s ⁻¹' ball w ρ = ball (a + s • w) (s * ρ)) ∧ (∀ (P : ℕ) (a c : Euclid P) (s ρ : ℝ), 0 < s → dilation a s '' ball c ρ = ball (dilation a s c) (ρ / s)) ∧ (∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s → dilation a s '' univ = univ ∧ ∀ A : Set (Euclid P), IsOpen A → IsOpen (dilation a s '' A)) ∧ (∀ (P : ℕ) (a y : Euclid P) (s t : ℝ) (A : Set (Euclid P)), 0 < s → 0 < t → dilation y t '' (dilation a s '' A) = dilation (a + s • y) (s * t) '' A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t → ENNReal.ofReal (t⁻¹ ^ n) • (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).map (dilation y t) = ENNReal.ofReal ((s * t)⁻¹ ^ n) • ν.map (dilation (a + s • y) (s * t))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)), ENNReal.ofReal ((1 : ℝ)⁻¹ ^ n) • ν.map (dilation 0 1) = ν ∧ ∀ A : Set (Euclid P), dilation (0 : Euclid P) 1 '' A = A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (B : Set (Euclid P)), 0 < s → MeasurableSet B → ENNReal.ofReal (s⁻¹ ^ n) • (ν.restrict B).map (dilation a s) = (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).restrict (dilation a s '' B)) := by
  -- Step 0: `η_{a,s}(v) = s⁻¹(v − a)`; for `s > 0` it is the affine homeomorphism
  -- `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`, hence measurable, injective and open
  have hdil : ∀ (P : ℕ) (a : Euclid P) (s : ℝ) (v : Euclid P), dilation a s v = s⁻¹ • (v - a) := by
    intro P a s v
    show -(s⁻¹ • a) + s⁻¹ • v = s⁻¹ • (v - a)
    rw [smul_sub, neg_add_eq_sub]
  have hmeas : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), Measurable (dilation a s) := fun P a s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  have hhomeo : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s →
      ∃ h : Euclid P ≃ₜ Euclid P, ⇑h = dilation a s := by
    intro P a s hs
    refine ⟨(Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs.ne')).trans
      (Homeomorph.addLeft (-(s⁻¹ • a))), ?_⟩
    funext v
    simp [dilation, dilationCLM]
  -- Step 6 (pointwise): `η_{y,t} ∘ η_{a,s} = η_{a+sy,st}`, as `(st)⁻¹ = t⁻¹s⁻¹`
  have hcomp : ∀ (P : ℕ) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t →
      dilation y t ∘ dilation a s = dilation (a + s • y) (s * t) := by
    intro P a y s t hs ht
    funext v
    rw [Function.comp_apply, hdil, hdil, hdil, mul_inv_rev, mul_smul, sub_add_eq_sub_sub,
      smul_sub s⁻¹ (v - a) (s • y), inv_smul_smul₀ hs.ne']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `ℝᴾ` is a `C²` submanifold of itself: `V = W = ℝᴾ`, `ψ = id`
    intro P y _
    refine ⟨univ, univ, id, isOpen_univ, isOpen_univ, mem_univ y, contDiffOn_id, injOn_id univ,
      by simp, fun K _ hK => by simpa using hK, fun z _ => ?_⟩
    rw [fderiv_id, ContinuousLinearMap.coe_id']
    exact injective_id
  · -- (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`
    intro P n ν a s A _ hA
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hmeas P a s) hA]
  · -- (3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`, as `η_{a,s}(v) − w = s⁻¹(v − (a + sw))`
    intro P a w s ρ hs
    ext v
    have hv : dilation a s v - w = s⁻¹ • (v - (a + s • w)) := by
      rw [hdil, sub_add_eq_sub_sub, smul_sub s⁻¹ (v - a) (s • w), inv_smul_smul₀ hs.ne']
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hv, norm_smul, norm_inv,
      Real.norm_of_nonneg hs.le, inv_mul_lt_iff₀ hs]
  · -- (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`: the image under `η_{a,s}` is the preimage
    -- under its inverse `u ↦ a + su`, and `a + su − c = s(u − η_{a,s}(c))`
    intro P a c s ρ hs
    rw [image_eq_preimage_of_inverse (f := dilation a s) (g := fun u => a + s • u)
      (fun v => show a + s • dilation a s v = v by rw [hdil, smul_inv_smul₀ hs.ne', add_sub_cancel])
      (fun u => show dilation a s (a + s • u) = u by
        rw [hdil, add_sub_cancel_left, inv_smul_smul₀ hs.ne'])]
    ext u
    have hu : a + s • u - c = s • (u - dilation a s c) := by
      rw [hdil, smul_sub, smul_inv_smul₀ hs.ne']
      abel
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hu, norm_smul,
      Real.norm_of_nonneg hs.le, lt_div_iff₀ hs, mul_comm]
  · -- (5) `η_{a,s}` is a homeomorphism: surjective and open
    intro P a s hs
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    rw [← hh]
    exact ⟨image_univ_of_surjective h.surjective, fun A hA => h.isOpenMap A hA⟩
  · -- (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`
    intro P a y s t A hs ht
    rw [← image_comp, hcomp P a y s t hs ht]
  · -- (7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`: `map_smul`, `map_map` and `t⁻ⁿs⁻ⁿ = (st)⁻ⁿ`
    intro P n ν a y s t hs ht
    rw [Measure.map_smul _ (hmeas P y t).aemeasurable, Measure.map_map (hmeas P y t) (hmeas P a s),
      hcomp P a y s t hs ht, smul_smul, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 ht.le) n),
      ← mul_pow, mul_inv_rev]
  · -- (8) `η_{0,1} = id`
    intro P n ν
    have h01 : dilation (0 : Euclid P) 1 = id := by
      funext v
      rw [hdil, inv_one, one_smul, sub_zero, id]
    refine ⟨?_, fun A => ?_⟩
    · rw [h01, Measure.map_id, inv_one, one_pow, ENNReal.ofReal_one, one_smul]
    · rw [h01, image_id]
  · -- (9) restriction commutes with the push-forward by the measurable embedding `η_{a,s}`,
    -- and `η_{a,s}⁻¹(η_{a,s}(B)) = B` by injectivity
    intro P n ν a s B hs _
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    have hemb : MeasurableEmbedding (dilation a s) := hh ▸ h.measurableEmbedding
    rw [Measure.restrict_smul, hemb.restrict_map, hemb.injective.preimage_image]

/-- **Homogeneous measures have dilation-invariant upper density ratios** (the weight of a
tangent cone in the proof of Simon 7.3.3, homogeneous of degree `n` by
`cone_current_imrep_measure_smul_image` since `η_{0,λ#}C = C`, 7.3.1(2)).  If `ν(λA) = λⁿ ν(A)`
for every `λ > 0` and Borel `A`, then for `t > 0` the ratios `r_ν(y, ρ) = ν(B_ρ(y))/(ωₙρⁿ)` (in
`[0, ∞]`, no finiteness of `ωₙ` used) satisfy `limsup_{ρ↓0} r_ν(tw, ρ) = limsup_{ρ↓0} r_ν(w, ρ)`:
`B_ρ(tw) = t B_{ρ/t}(w)` and `ωₙρⁿ = tⁿ ωₙ(ρ/t)ⁿ`, so cancelling the finite nonzero factor `tⁿ`
gives `r_ν(tw, ρ) = r_ν(w, ρ/t)` for `ρ > 0`, and `ρ ↦ ρ/t` maps `𝓝[>] 0` onto itself. -/
theorem Submission.idtp_fons_cc_tm_density_homogeneous : ∀ (P n : ℕ) (ν : Measure (Euclid P)), (∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → ν ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * ν A) → ∀ t : ℝ, 0 < t → ∀ w : Euclid P, limsup (fun ρ : ℝ => ν (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) = limsup (fun ρ : ℝ => ν (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) := by
  intro P n ν hν t ht w
  -- steps 1–4: `r_ν(tw, ρ) = r_ν(w, ρ/t)` for every `ρ > 0`
  have hratio : ∀ ρ : ℝ, 0 < ρ →
      ν (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)) =
        ν (ball w (ρ / t)) / (unitBallVolume n * ENNReal.ofReal ((ρ / t) ^ n)) := by
    intro ρ _
    -- step 1: `B_ρ(tw) = t • B_{ρ/t}(w)`, as `‖t‖ (ρ/t) = ρ`
    have hball : ball (t • w) ρ = (fun x => t • x) '' ball w (ρ / t) := by
      rw [image_smul, smul_ball ht.ne', Real.norm_of_nonneg ht.le, mul_div_cancel₀ ρ ht.ne']
    -- step 3: `ωₙρⁿ = tⁿ (ωₙ(ρ/t)ⁿ)`, as `ρⁿ = tⁿ(ρ/t)ⁿ`
    have hden : unitBallVolume n * ENNReal.ofReal (ρ ^ n) =
        ENNReal.ofReal (t ^ n) * (unitBallVolume n * ENNReal.ofReal ((ρ / t) ^ n)) := by
      rw [mul_left_comm, ← ENNReal.ofReal_mul (pow_nonneg ht.le n), ← mul_pow,
        mul_div_cancel₀ ρ ht.ne']
    -- steps 2 and 4: `ν(B_ρ(tw)) = tⁿ ν(B_{ρ/t}(w))`, and cancel the finite nonzero `tⁿ`
    rw [hball, hν t ht _ measurableSet_ball, hden,
      ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos ht n)).ne' ENNReal.ofReal_ne_top]
  -- step 7: `ρ ↦ ρ/t` maps `𝓝[>] 0` onto itself, its inverse being `ρ ↦ tρ`
  have hmap : map (fun ρ : ℝ => ρ / t) (𝓝[>] 0) = 𝓝[>] 0 := by
    rw [map_eq_comap_of_inverse (m := fun ρ : ℝ => ρ / t) (n := fun ρ : ℝ => t * ρ)
      (funext fun ρ => mul_div_cancel_left₀ ρ ht.ne') (funext fun ρ => mul_div_cancel₀ ρ ht.ne'),
      comap_mulLeft_nhdsGT_zero ht]
  -- steps 5, 6 and 8: eventual equality along `𝓝[>] 0`, then change variables `ρ ↦ ρ/t`
  calc limsup (fun ρ : ℝ => ν (ball (t • w) ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
        (𝓝[>] 0)
      = limsup ((fun ρ : ℝ => ν (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) ∘
          fun ρ => ρ / t) (𝓝[>] 0) :=
        limsup_congr (eventually_nhdsWithin_of_forall fun ρ hρ => hratio ρ hρ)
    _ = limsup (fun ρ : ℝ => ν (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
          (map (fun ρ => ρ / t) (𝓝[>] 0)) := limsup_comp _ _ _
    _ = limsup (fun ρ : ℝ => ν (ball w ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
          (𝓝[>] 0) := by rw [hmap]
/-- **Normalization** (Simon 7.3.3, proof of 3.3(2); Remark 3.4): `μHE[n] = a • μH[n]` with
`a = addHaarScalarFactor(volume, μH[n]) ≠ 0` depending only on `n`, so `c = a⁻¹`.  If
`μ = μHE[n]⌞g` is finite on compact sets, then `∫⁻_K g dμH[n] = a⁻¹ μ(K) < ∞` for compact `K`,
so `g • e` is locally `μH[n]`-integrable, and
`∫ f (g • e) dμH[n] = (∫ f g dμH[n]) • e = (a⁻¹ ∫ f g dμHE[n]) • e = (a⁻¹ ∫ f dμ) • e`. -/
theorem Submission.idtp_fons_cr_density_normalization : ∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ ∀ (Q : ℕ) (μ : Measure (Euclid P)) (g : Euclid P → ℝ) (e : Euclid Q), Measurable g → (∀ x, 0 ≤ g x) → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → μ = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal (g x)) → LocallyIntegrable (fun x => g x • e) μH[(n : ℝ)] ∧ ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → ∫ x, f x • (g x • e) ∂μH[(n : ℝ)] = (c * ∫ x, f x ∂μ) • e := by
  intro P n
  -- `μHE[n] = a • μH[n]`, where `a ≠ 0` depends only on `n`
  obtain ⟨a, ha0, hE⟩ : ∃ a : NNReal, a ≠ 0 ∧
      (μHE[n] : Measure (Euclid P)) = a • μH[(n : ℝ)] :=
    ⟨_, Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero n,
      Measure.euclideanHausdorffMeasure_def n⟩
  refine ⟨(a : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ha0)), ?_⟩
  intro Q μ g e hg hg0 hμK hμ
  -- `μ = a • μH[n]⌞g`
  have hμ' : μ = (a : ℝ≥0∞) • (μH[(n : ℝ)] : Measure (Euclid P)).withDensity
      (fun x => ENNReal.ofReal (g x)) := by
    rw [hμ, hE, ← withDensity_smul_measure]
    rfl
  refine ⟨?_, fun f hf hfc => ?_⟩
  · -- local integrability: `∫⁻_K g dμH[n] = a⁻¹ μ(K) < ∞` for compact `K`
    rw [locallyIntegrable_iff]
    intro K hK
    refine Integrable.smul_const ⟨hg.aestronglyMeasurable, ?_⟩ e
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0), ← withDensity_apply _ hK.measurableSet]
    have hK' := hμK K hK
    rw [hμ', Measure.smul_apply, smul_eq_mul] at hK'
    exact ENNReal.lt_top_of_mul_ne_top_right hK' (by exact_mod_cast ha0)
  · -- pull out `e`, then pass from `μH[n]` to `μHE[n] = a • μH[n]` and to `μ = μHE[n]⌞g`
    have h1 : ∀ x, f x • (g x • e) = (f x * g x) • e := fun x => smul_smul _ _ _
    simp_rw [h1]
    rw [integral_smul_const]
    congr 1
    have h2 : ∫ x, f x ∂μ = (a : ℝ) * ∫ x, f x * g x ∂μH[(n : ℝ)] := by
      rw [hμ, hE, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top), integral_smul_nnreal_measure,
        NNReal.smul_def, smul_eq_mul]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [ENNReal.toReal_ofReal (hg0 x), smul_eq_mul, mul_comm]
    rw [h2, ← mul_assoc, inv_mul_cancel₀ (NNReal.coe_ne_zero.2 ha0), one_mul]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
