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

/-- **The approximate tangent projection is `μ_V`-measurable** (Simon Ch. 3, 1.4 and 1.5(1);
Ch. 6, 3.1).  For `R = (M, θ, ξ)` with weight `μ_V = θ Hⁿ⌞M`, `x ↦ p_{TₓM}` is `μ_V`-a.e. strongly
measurable.  Since `μ_V ≪ Hⁿ⌞M`, it suffices to prove this for `Hⁿ⌞M`.  By uniqueness of
approximate tangent planes, `TₓM` is `Hⁿ⌞M`-a.e. the plane oriented by `ξ(x)`.  A unit simple
`n`-vector `ζ = ±τ₁ ∧ ⋯ ∧ τₙ` determines its plane: if also `ζ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` and
`y ⊥ span τ'`, the `n`-covector `α(u) = det(⟨cₖ, uⱼ⟩)`, where `c` is `τ` with `τᵢ` replaced by `y`,
gives `±⟨y, τᵢ⟩ = ±α(τ) = ζ(α) = ±α(τ') = 0`, so `τᵢ ∈ span τ'`.  Hence `p_{TₓM} = G(ξ(x))` a.e.,
where `G(ζ)` is the projection onto the plane of `ζ` (`0` if there is none).  `G` is Borel:
`Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` is continuous on the compact set `Ω` of orthonormal frames and signs, and
`G(Φ(τ, s)) = Σₖ ⟨τₖ, ·⟩ τₖ` is continuous, so for closed `t`,
`G⁻¹(t) = Φ(Ω ∩ (G ∘ Φ)⁻¹(t)) ∪ (Φ(Ω)ᶜ ∩ {0 ∈ t})` is Borel. -/
theorem Submission.dorag_approxTangent_starProjection_aesm : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R
  classical
  -- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to prove measurability for `Hⁿ⌞M`
  refine AEStronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (μHE[n].restrict R.carrier) fun x => (R.mult x : ℝ≥0∞)) ?_
  -- `ev τ = (α ↦ α(τ₁, …, τₙ))`, a continuous alternating map of `τ`
  let ev : Euclid P [⋀^Fin n]→L[ℝ] MultiVector P n :=
    (ContinuousLinearMap.id ℝ (Covector (Euclid P) n)).flipAlternating
  have hev : ∀ (τ : Fin n → Euclid P) (α : Covector (Euclid P) n), ev τ α = α τ :=
    fun τ α => rfl
  -- `Φ(τ, s) = s τ₁ ∧ ⋯ ∧ τₙ` on the compact set `Ω` of orthonormal frames and signs `s = ±1`
  let Φ : (Fin n → Euclid P) × ℝ → MultiVector P n := fun ω => ω.2 • ev ω.1
  have hΦc : Continuous Φ := continuous_snd.smul (ev.coe_continuous.comp continuous_fst)
  let Ω : Set ((Fin n → Euclid P) × ℝ) := {τ | Orthonormal ℝ τ} ×ˢ {1, -1}
  have hΩ : IsCompact Ω := by
    refine IsCompact.prod (isCompact_of_isClosed_isBounded ?_ ?_) (Set.toFinite _).isCompact
    · have hset : {τ : Fin n → Euclid P | Orthonormal ℝ τ} =
          ⋂ i, ⋂ j, {τ | inner ℝ (τ i) (τ j) = if i = j then (1 : ℝ) else 0} := by
        ext τ
        simp [orthonormal_iff_ite]
      rw [hset]
      exact isClosed_iInter fun i => isClosed_iInter fun j =>
        isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
    · refine (isBounded_iff_subset_closedBall 0).mpr ⟨1, fun τ hτ => ?_⟩
      rw [mem_closedBall_zero_iff]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => (hτ.1 i).le
  -- `ζ` orients `Q` iff `ζ = Φ(τ, s)` for a point `(τ, s)` of `Ω` with `span τ = Q`
  have horient : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q ↔ ∃ ω ∈ Ω, Φ ω = ζ ∧ Submodule.span ℝ (range ω.1) = Q := by
    intro ζ Q
    constructor
    · rintro ⟨τ, hτ, hQ, h | h⟩
      · refine ⟨(τ, 1), ⟨hτ, Or.inl rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
      · refine ⟨(τ, -1), ⟨hτ, Or.inr rfl⟩, ?_, hQ⟩
        ext α
        simp [Φ, hev, h]
    · rintro ⟨⟨τ, s⟩, ⟨hτ, hs⟩, rfl, hQ⟩
      refine ⟨τ, hτ, hQ, ?_⟩
      rcases hs with rfl | rfl
      · left
        intro α
        simp [Φ, hev]
      · right
        intro α
        simp [Φ, hev]
  -- the `n`-covector `u ↦ det(⟨cₖ, uⱼ⟩)ₖⱼ`
  have hdet : ∀ c : Fin n → Euclid P, ∃ α : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, α u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
    intro c
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) := LinearMap.pi fun k => (innerSL ℝ (c k)).toLinearMap
    let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hA : ∀ u : Fin n → Euclid P, A u = (Matrix.of fun k j => inner ℝ (c k) (u j)).det := by
      intro u
      rw [← Matrix.det_transpose]
      rfl
    have hAc : Continuous fun u : Fin n → Euclid P => A u := by
      simp only [hA]
      exact Continuous.matrix_det (continuous_matrix fun k j => by
        simp only [Matrix.of_apply]
        exact continuous_const.inner (continuous_apply j))
    exact ⟨{ A with cont := hAc }, hA⟩
  -- a unit simple `n`-vector determines its plane: if `ζ` orients `span τ` and `span τ'`, then
  -- each `τᵢ` is orthogonal to `(span τ')ᗮ`
  have hle : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q ≤ Q' := by
    rintro ζ Q Q' ⟨τ, hτ, rfl, hζ⟩ ⟨τ', hτ', rfl, hζ'⟩
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.orthogonal_orthogonal (Submodule.span ℝ (range τ')),
      Submodule.mem_orthogonal]
    intro y hy
    obtain ⟨α, hα⟩ := hdet (Function.update τ i y)
    -- `α(τ)` is the determinant of the identity matrix with row `i` replaced by `(⟨y, τⱼ⟩)ⱼ`
    have h1 : α τ = inner ℝ y (τ i) := by
      rw [hα]
      have hM : (Matrix.of fun k j => inner ℝ (Function.update τ i y k) (τ j)) =
          (1 : Matrix (Fin n) (Fin n) ℝ).updateRow i (fun j => inner ℝ y (τ j)) := by
        ext k j
        by_cases hk : k = i
        · subst hk
          simp
        · simp [hk, Matrix.one_apply, orthonormal_iff_ite.mp hτ k j]
      rw [hM, ← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
        ← Matrix.cramer_apply, Matrix.cramer_one]
      rfl
    -- row `i` of the matrix of `α(τ')` is `(⟨y, τ'ⱼ⟩)ⱼ = 0`
    have h2 : α τ' = 0 := by
      rw [hα]
      refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
      simp only [Matrix.of_apply, Function.update_self]
      rw [real_inner_comm]
      exact hy _ (Submodule.subset_span ⟨j, rfl⟩)
    have h3 : ζ α = 0 := by
      rcases hζ' with h | h <;> simp [h, h2]
    rcases hζ with h | h
    · rw [← h1, ← h, h3]
    · have h4 := h α
      rw [h3] at h4
      rw [← h1]
      linarith
  have huniq : ∀ (ζ : MultiVector P n) (Q Q' : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → IsUnitOrientationOf ζ Q' → Q = Q' :=
    fun ζ Q Q' h h' => le_antisymm (hle ζ Q Q' h h') (hle ζ Q' Q h' h)
  -- the projection onto the span of an orthonormal frame `τ` is `Σₖ ⟨τₖ, ·⟩ τₖ`, continuous in `τ`
  let F : (Fin n → Euclid P) × ℝ → (Euclid P →L[ℝ] Euclid P) :=
    fun ω => ∑ k, (innerSL ℝ (ω.1 k)).smulRight (ω.1 k)
  have hFapply : ∀ ω v, F ω v = ∑ k, inner ℝ (ω.1 k) v • ω.1 k := by
    intro ω v
    simp [F]
  have hFc : Continuous F := by
    refine continuous_clm_apply.mpr fun v => ?_
    simp only [hFapply]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  have hFproj : ∀ ω ∈ Ω, (Submodule.span ℝ (range ω.1)).starProjection = F ω := by
    rintro ⟨τ, s⟩ ⟨hτ, -⟩
    refine ContinuousLinearMap.ext fun v => ?_
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hFapply]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    · intro w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨j, rfl⟩
        rw [hFapply, inner_sub_left, sum_inner]
        simp [inner_smul_left, orthonormal_iff_ite.mp hτ, real_inner_comm]
      · simp
      · intro x y _ _ hx hy
        rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx
        rw [inner_smul_right, hx, mul_zero]
  -- `G ζ` is the projection onto the plane oriented by `ζ` (`0` if there is none)
  let G : MultiVector P n → (Euclid P →L[ℝ] Euclid P) := fun ζ =>
    if h : ∃ Q, IsUnitOrientationOf ζ Q then h.choose.starProjection else 0
  have hGQ : ∀ (ζ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf ζ Q → G ζ = Q.starProjection := by
    intro ζ Q hQ
    have hex : ∃ Q, IsUnitOrientationOf ζ Q := ⟨Q, hQ⟩
    simp only [G, dite_eq_left hex]
    rw [huniq _ _ _ hex.choose_spec hQ]
  have hGΦ : ∀ ω ∈ Ω, G (Φ ω) = F ω := fun ω hω => by
    rw [hGQ _ _ ((horient _ _).mpr ⟨ω, hω, rfl, rfl⟩), hFproj ω hω]
  -- `G` is Borel: for closed `t`, `G⁻¹(t)` is the compact set `Φ(Ω ∩ F⁻¹(t))` together with the
  -- complement of the compact set `Φ(Ω)` (if `0 ∈ t`)
  have hG : Measurable G := by
    refine measurable_of_isClosed fun t ht => ?_
    have hset : G ⁻¹' t = Φ '' (Ω ∩ F ⁻¹' t) ∪
        ((Φ '' Ω)ᶜ ∩ {_ζ | (0 : Euclid P →L[ℝ] Euclid P) ∈ t}) := by
      ext ζ
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_image, Set.mem_inter_iff,
        Set.mem_compl_iff]
      by_cases h : ∃ Q, IsUnitOrientationOf ζ Q
      · obtain ⟨Q, hQ⟩ := h
        obtain ⟨ω, hω, hΦω, -⟩ := (horient ζ Q).mp hQ
        have hGζ : G ζ = F ω := by
          rw [← hΦω]
          exact hGΦ ω hω
        constructor
        · intro hζt
          exact Or.inl ⟨ω, ⟨hω, by rwa [← hGζ]⟩, hΦω⟩
        · rintro (⟨ω', ⟨hω', hω't⟩, hΦω'⟩ | ⟨hn, -⟩)
          · rw [← hΦω', hGΦ ω' hω']
            exact hω't
          · exact absurd ⟨ω, hω, hΦω⟩ hn
      · have hGζ : G ζ = 0 := dite_eq_right h
        have hn : ¬∃ ω, ω ∈ Ω ∧ Φ ω = ζ := fun ⟨ω, hω, hΦω⟩ =>
          h ⟨_, (horient ζ _).mpr ⟨ω, hω, hΦω, rfl⟩⟩
        rw [hGζ]
        constructor
        · intro h0
          exact Or.inr ⟨hn, h0⟩
        · rintro (⟨ω', ⟨hω', -⟩, hΦω'⟩ | ⟨-, h0⟩)
          · exact absurd ⟨ω', hω', hΦω'⟩ hn
          · exact h0
    rw [hset]
    exact ((hΩ.inter_right (ht.preimage hFc)).image hΦc).isClosed.measurableSet.union
      ((hΩ.image hΦc).isClosed.measurableSet.compl.inter (MeasurableSet.const _))
  -- `Hⁿ⌞M`-a.e. `TₓM` is the plane oriented by `ξ(x)` (uniqueness of approximate tangent planes),
  -- so `p_{TₓM} = G(ξ(x))`
  have hae : (fun x => (approxTangentPlane n R.carrier x).starProjection)
      =ᵐ[μHE[n].restrict R.carrier] G ∘ R.orient := by
    filter_upwards [R.orients] with x ⟨Q, hQ, hor⟩
    have hex : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    have h1 : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    rw [Function.comp_apply, hGQ _ _ hor, h1]
  -- `G ∘ ξ` is a.e. measurable, with values in the finite-dimensional space `End(ℝᴾ)`
  have : TopologicalSpace.PseudoMetrizableSpace (MultiVector P n) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (inferInstance : PseudoEMetricSpace (MultiVector P n))
  exact ((hG.comp_aemeasurable R.aestronglyMeasurable_orient.aemeasurable).aestronglyMeasurable
    ).congr hae.symm

/-- Facts about `D = δ^{1/(2n+2)}` used in the tilt-excess decay step: if `δ ≤ min(1, η^{2n+2})`
then `0 < D ≤ η`, `δ ≤ D` and `√δ ≤ D`. -/
theorem Submission.dorag_tesDecay_rpow (n : ℕ) (δ η : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η)
    (hδη : δ ≤ η ^ (2 * n + 2)) :
    0 < δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ∧ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ≤ η ∧
      δ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) ∧ Real.sqrt δ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) := by
  have hα : (1 : ℝ) / (2 * (n : ℝ) + 2) = (((2 * n + 2 : ℕ) : ℝ))⁻¹ := by
    push_cast
    ring
  have hαpos : 0 < (1 : ℝ) / (2 * (n : ℝ) + 2) := by positivity
  have hα2 : (1 : ℝ) / (2 * (n : ℝ) + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨Real.rpow_pos_of_pos hδ _, ?_, ?_, ?_⟩
  · calc δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2))
        ≤ (η ^ (2 * n + 2)) ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) :=
          Real.rpow_le_rpow hδ.le hδη hαpos.le
      _ = η := by rw [hα, Real.pow_rpow_inv_natCast hη.le (by omega)]
  · calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
      _ ≤ δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) :=
          Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  · rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hα2

/-- The height bound produced by the plane reduction of Step 1:
`2C₃Dσ + (4a/M)^{1/2}σ = C₁₁Dσ` for `a = C₃D²σⁿ`, `M = ω_nσⁿ/2`. -/
theorem Submission.dorag_tesDecay_height_const (n : ℕ) (C₃ ω D σ : ℝ) (hC₃ : 0 ≤ C₃) (hω : 0 < ω)
    (hD : 0 ≤ D) (hσ : 0 < σ) :
    C₃ * D * (2 * σ) + Real.sqrt (4 * (C₃ * D ^ 2 * σ ^ n) / (ω * σ ^ n / 2)) * σ =
      (2 * C₃ + Real.sqrt (8 * C₃ / ω)) * D * σ := by
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have h1 : 4 * (C₃ * D ^ 2 * σ ^ n) / (ω * σ ^ n / 2) = 8 * C₃ / ω * D ^ 2 := by
    field_simp
    ring
  rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
  ring

/-- A finite `[0, ∞]` quantity bounded by `ofReal a` is `ofReal I` for a real `0 ≤ I ≤ a`. -/
theorem Submission.dorag_tesDecay_real_of_le {J : ℝ≥0∞} {a : ℝ} (ha : 0 ≤ a)
    (h : J ≤ ENNReal.ofReal a) : ∃ I : ℝ, 0 ≤ I ∧ ENNReal.ofReal I = J ∧ I ≤ a :=
  ⟨J.toReal, ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h),
    ENNReal.toReal_le_of_le_ofReal ha h⟩

/-- Step 1, the normalised excess `E₀ = max(σ⁻ⁿI, κ²σ²/δ)` (`I = ∫_{B_σ(ξ)}|p_x − p_{T'}|² dμ`):
`I ≤ σⁿE₀`, `κ²σ² ≤ δE₀`, `E₀ ≤ C₃D²` (as `κσ ≤ δ²`) and `κσ ≤ D E₀^{1/2}` (as `δ^{1/2} ≤ D`). -/
theorem Submission.dorag_tesDecay_excess_facts (n : ℕ) (C₃ D δ E₀ I κ ρ σ : ℝ) (hδ : 0 < δ)
    (hδ8 : δ ≤ 1 / 8) (hσ : 0 < σ) (hσδρ : σ ≤ δ * ρ) (hκ : 0 ≤ κ) (hκρ : κ * ρ ≤ δ)
    (hC₃ : 1 ≤ C₃) (hδD : δ ≤ D) (hsδD : Real.sqrt δ ≤ D)
    (hIa : I ≤ C₃ * D ^ 2 * σ ^ n) (hE₀def : E₀ = max (1 / σ ^ n * I) (κ ^ 2 * σ ^ 2 / δ)) :
    0 ≤ E₀ ∧ I ≤ σ ^ n * E₀ ∧ κ ^ 2 * σ ^ 2 ≤ δ * E₀ ∧ E₀ ≤ C₃ * D ^ 2 ∧
      κ * σ ≤ D * Real.sqrt E₀ := by
  have hE₀1 : 1 / σ ^ n * I ≤ E₀ := hE₀def ▸ le_max_left _ _
  have hE₀2 : κ ^ 2 * σ ^ 2 / δ ≤ E₀ := hE₀def ▸ le_max_right _ _
  have hσn : 0 < σ ^ n := pow_pos hσ n
  have hκE : κ ^ 2 * σ ^ 2 ≤ δ * E₀ := by
    calc κ ^ 2 * σ ^ 2 = δ * (κ ^ 2 * σ ^ 2 / δ) := by field_simp
      _ ≤ δ * E₀ := by gcongr
  refine ⟨le_trans (by positivity) hE₀2, ?_, hκE, ?_, ?_⟩
  · calc I = σ ^ n * (1 / σ ^ n * I) := by field_simp
      _ ≤ σ ^ n * E₀ := by gcongr
  · rw [hE₀def]
    apply max_le
    · calc 1 / σ ^ n * I ≤ 1 / σ ^ n * (C₃ * D ^ 2 * σ ^ n) := by gcongr
        _ = C₃ * D ^ 2 := by field_simp
    · have hκσ : κ * σ ≤ δ * δ := by
        calc κ * σ ≤ κ * (δ * ρ) := by gcongr
          _ = δ * (κ * ρ) := by ring
          _ ≤ δ * δ := by gcongr
      have h1 : κ ^ 2 * σ ^ 2 ≤ δ ^ 4 := by
        calc κ ^ 2 * σ ^ 2 = (κ * σ) ^ 2 := by ring
          _ ≤ (δ * δ) ^ 2 := pow_le_pow_left₀ (mul_nonneg hκ hσ.le) hκσ 2
          _ = δ ^ 4 := by ring
      have h3 : δ ^ 3 ≤ D ^ 2 := by
        calc δ ^ 3 ≤ δ ^ 2 := pow_le_pow_of_le_one hδ.le (by linarith) (by norm_num)
          _ ≤ D ^ 2 := pow_le_pow_left₀ hδ.le hδD 2
      rw [div_le_iff₀ hδ]
      calc κ ^ 2 * σ ^ 2 ≤ δ ^ 4 := h1
        _ = δ ^ 3 * δ := by ring
        _ ≤ D ^ 2 * δ := by gcongr
        _ = 1 * (D ^ 2 * δ) := by ring
        _ ≤ C₃ * (D ^ 2 * δ) := by gcongr
        _ = C₃ * D ^ 2 * δ := by ring
  · rw [← Real.sqrt_sq (mul_nonneg hκ hσ.le)]
    calc Real.sqrt ((κ * σ) ^ 2) ≤ Real.sqrt (δ * E₀) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact hκE)
      _ = Real.sqrt δ * Real.sqrt E₀ := Real.sqrt_mul hδ.le _
      _ ≤ D * Real.sqrt E₀ := by gcongr

/-- Step 11: `θE₀ = θE_*(ξ, σ, T')` is at most `θE_*(ξ, σ, T)` when `E(ξ, σ, T') ≤ E(ξ, σ, T)`. -/
theorem Submission.dorag_tesDecay_rhs (θ E₀ a b I : ℝ) (J : ℝ≥0∞) (hθ : 0 ≤ θ) (ha : 0 ≤ a)
    (hE₀ : E₀ = max (a * I) b) (hI : ENNReal.ofReal I ≤ J) :
    ENNReal.ofReal (θ * E₀) ≤ ENNReal.ofReal θ * max (ENNReal.ofReal a * J) (ENNReal.ofReal b) := by
  rw [ENNReal.ofReal_mul hθ, hE₀, ENNReal.ofReal_max, ENNReal.ofReal_mul ha]
  gcongr

/-- `μ_V = θ Hⁿ⌞M ≪ Hⁿ⌞M`: an `Hⁿ⌞(M ∩ W)`-a.e. property holds `μ_V`-a.e. on `W`. -/
theorem Submission.dorag_tesDecay_ae_of_carrier {P n : ℕ} {U W : Set (Euclid P)} (R : IMRep U n)
    (hW : MeasurableSet W) {p : Euclid P → Prop}
    (h : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), p x) : ∀ᵐ x ∂R.measure, x ∈ W → p x := by
  have h1 : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ W → p x := by
    rw [← ae_restrict_iff' hW, Measure.restrict_restrict hW, Set.inter_comm]
    exact h
  exact (withDensity_absolutelyContinuous _ _).ae_le h1

/-- The energy normalisation of Step 7: `s⁻²(2 + C₇)I ≤ (σ/8)ⁿ` for `s² = (2 + C₇)8ⁿE₀`. -/
theorem Submission.dorag_tesDecay_energy_real (n : ℕ) (C₇ E₀ I σ : ℝ) (hC₇ : 0 < C₇) (hE₀ : 0 < E₀)
    (hσ : 0 < σ) (hIle : I ≤ σ ^ n * E₀) :
    (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ ^ 2 * (2 * I + C₇ * I) ≤ (σ / 4 / 2) ^ n := by
  have hpos : 0 < (2 + C₇) * 8 ^ n * E₀ := by positivity
  rw [inv_pow, Real.sq_sqrt hpos.le]
  have h8 : (σ / 4 / 2) ^ n = σ ^ n / 8 ^ n := by
    rw [show σ / 4 / 2 = σ / 8 by ring, div_pow]
  rw [h8, inv_mul_le_iff₀ hpos]
  have h8pos : (0 : ℝ) < 8 ^ n := by positivity
  calc 2 * I + C₇ * I = (2 + C₇) * I := by ring
    _ ≤ (2 + C₇) * (σ ^ n * E₀) := by gcongr
    _ = (2 + C₇) * 8 ^ n * E₀ * (σ ^ n / 8 ^ n) := by field_simp

/-- The weak-form normalisation of Step 7 (Simon (15)–(17)): the right side of the weak equation
for `fʲ`, divided by `s = ((2 + C₇)8ⁿE₀)^{1/2}`, is at most `δ_h(σ/8)ⁿG`. -/
theorem Submission.dorag_tesDecay_weak_real (n k : ℕ) (C₃ C₇ ω D δh E₀ I κ σ G : ℝ)
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hω : 0 < ω) (hD : 0 ≤ D) (hE₀ : 0 < E₀) (hσ : 0 < σ)
    (hG : 0 ≤ G) (hIle : I ≤ σ ^ n * E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2)
    (hκσ : κ * σ ≤ D * Real.sqrt E₀)
    (hδh : 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1)) /
      Real.sqrt ((2 + C₇) * 8 ^ n) * D ≤ δh) :
    (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ *
        (G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n))) ≤
      δh * (σ / 4 / 2) ^ n * G := by
  set r := Real.sqrt E₀ with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hE₀
  have hrr : r * r = E₀ := Real.mul_self_sqrt hE₀.le
  have hC₁₃ : 0 < (2 + C₇) * 8 ^ n := by positivity
  have hsC : 0 < Real.sqrt ((2 + C₇) * 8 ^ n) := Real.sqrt_pos.mpr hC₁₃
  have hs : Real.sqrt ((2 + C₇) * 8 ^ n * E₀) = Real.sqrt ((2 + C₇) * 8 ^ n) * r := by
    rw [Real.sqrt_mul hC₁₃.le]
  have hsC₃ : 1 ≤ Real.sqrt C₃ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hC₃
  -- `√E₀ ≤ √C₃ D`
  have hrD : r ≤ Real.sqrt C₃ * D := by
    rw [hr, ← Real.sqrt_sq hD, ← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hE₀le
  -- `I ≤ σⁿ √E₀ √C₃ D`
  have hI' : I ≤ σ ^ n * r * (Real.sqrt C₃ * D) := by
    calc I ≤ σ ^ n * E₀ := hIle
      _ = σ ^ n * r * r := by rw [← hrr]; ring
      _ ≤ σ ^ n * r * (Real.sqrt C₃ * D) := by gcongr
  set B := (2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1) with hB
  have hX : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n) ≤
      σ ^ n * r * D * B := by
    have h1 : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) ≤
        (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * (σ ^ n * r * (Real.sqrt C₃ * D)) := by
      have : (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) =
          (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * I := by
        ring
      rw [this]
      gcongr
    have h2 : κ * (σ / 4) * (2 * ω * (σ / 4) ^ n) = (κ * σ) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by
      rw [div_pow, pow_succ]
      field_simp
    have h3 : (κ * σ) * (2 * ω * σ ^ n / 4 ^ (n + 1)) ≤ (D * r) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by
      gcongr
    calc (2 + 2 ^ (n + 1) * (k : ℝ)) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)
        ≤ (2 + 2 ^ (n + 1) * (k : ℝ)) * (1 + C₇) * (σ ^ n * r * (Real.sqrt C₃ * D)) +
            (D * r) * (2 * ω * σ ^ n / 4 ^ (n + 1)) := by rw [h2]; exact add_le_add h1 h3
      _ = σ ^ n * r * D * B := by rw [hB]; ring
  have h8 : (σ / 4 / 2) ^ n = σ ^ n / 8 ^ n := by
    rw [show σ / 4 / 2 = σ / 8 by ring, div_pow]
  have hB0 : 0 ≤ B := by positivity
  calc (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ *
        (G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)))
      ≤ (Real.sqrt ((2 + C₇) * 8 ^ n * E₀))⁻¹ * (G * (σ ^ n * r * D * B)) := by gcongr
    _ = (8 ^ n * B / Real.sqrt ((2 + C₇) * 8 ^ n) * D) * (σ / 4 / 2) ^ n * G := by
      rw [hs, h8]
      field_simp
    _ ≤ δh * (σ / 4 / 2) ^ n * G := by gcongr

/-- Step 7 (Simon (17)–(18)): for each component `fʲ` of the Lipschitz approximation, the
harmonic approximation lemma applied to `w = s⁻¹fʲ` on `Bⁿ_{σ/8}` gives an affine
`a + b` with `‖b‖ ≤ C_H`, `|a| ≤ C_H s⁻¹C₇Dσω^{1/2} + C_Hε'^{1/2}σ/8` and the `L²` decay
on `Bⁿ_{θ'σ/8}`. -/
theorem Submission.dorag_tesDecay_harmonic_step (n k : ℕ) (f : Euclid n → Euclid k)
    (C₃ C₇ CH ω D δh ε' E₀ I κ σ s θ' : ℝ)
    (hHA' : ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w →
      ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n →
      (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
        |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) →
      ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
        |a| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) +
          CH * Real.sqrt ε' * R₀ ∧
        ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤
          CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2))
    (hGE : ∀ j : Fin k, ∫ v in ball (0 : Euclid n) (σ / 4 / 2),
      ‖fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ 2 * I + C₇ * I)
    (hGW : ∀ (j : Fin k) (ζ : Euclid n → ℝ) (G : ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Euclid n) (σ / 4 / 2) → (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
      |∫ v in ball (0 : Euclid n) (σ / 4 / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤
        G * ((2 + 2 ^ (n + 1) * k) * (I + C₇ * I) + κ * (σ / 4) * (2 * ω * (σ / 4) ^ n)))
    (hf1 : ∀ v w, ‖f v - f w‖ ≤ ‖v - w‖) (hfb : ∀ v, ‖f v‖ ≤ C₇ * D * σ)
    (hsdef : s = Real.sqrt ((2 + C₇) * 8 ^ n * E₀))
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hCH : 0 < CH) (hω : 0 < ω) (hD : 0 ≤ D) (hE₀ : 0 < E₀)
    (hσ : 0 < σ) (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4)
    (hIE : I ≤ σ ^ n * E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2) (hκσE : κ * σ ≤ D * Real.sqrt E₀)
    (hD14 : 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ + 2 * ω / 4 ^ (n + 1)) /
      Real.sqrt ((2 + C₇) * 8 ^ n) * D ≤ δh)
    (hvol : volume.real (ball (0 : Euclid n) (σ / 4 / 2)) = (σ / 4 / 2) ^ n * ω) :
    ∀ j : Fin k, ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
      |a| ≤ CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2) ∧
      ∫ v in ball (0 : Euclid n) (θ' * (σ / 4 / 2)),
          (s⁻¹ * EuclideanSpace.proj j (f v) - a - b v) ^ 2 ≤
        CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * (σ / 4 / 2)) ^ (n + 2) := by
  intro j
  have hs : 0 < s := hsdef ▸ Real.sqrt_pos.mpr (by positivity)
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hR₀ : 0 < σ / 4 / 2 := by positivity
  have hderiv : ∀ v, fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v =
      s⁻¹ • fderiv ℝ (fun v => EuclideanSpace.proj j (f v)) v := by
    intro v
    have : (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) =
        s⁻¹ • fun v => EuclideanSpace.proj j (f v) := rfl
    rw [this, fderiv_const_smul_field]
    rfl
  have hproj : ∀ y : Euclid k, |EuclideanSpace.proj j y| ≤ ‖y‖ := fun y => by
    simpa using PiLp.norm_apply_le y j
  -- `w = s⁻¹fʲ` is `s⁻¹`-Lipschitz
  have hwLip : LipschitzWith (Real.toNNReal s⁻¹) (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) := by
    refine LipschitzWith.of_dist_le_mul fun v w => ?_
    rw [Real.coe_toNNReal _ hsi.le, Real.dist_eq, dist_eq_norm, ← mul_sub, ← map_sub, abs_mul,
      abs_of_pos hsi]
    gcongr
    exact (hproj _).trans (hf1 v w)
  -- the energy of `w` on `Bⁿ_{σ/8}` is at most `(σ/8)ⁿ`
  have hwE : ∫ v in ball (0 : Euclid n) (σ / 4 / 2),
      ‖fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v‖ ^ 2 ≤ (σ / 4 / 2) ^ n := by
    simp_rw [hderiv, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos hsi]
    rw [integral_const_mul]
    refine le_trans ?_ (Submission.dorag_tesDecay_energy_real n C₇ E₀ I σ hC₇ hE₀ hσ hIE)
    rw [← hsdef]
    exact mul_le_mul_of_nonneg_left (hGE j) (by positivity)
  -- `w` is weakly `δ_h`-harmonic on `Bⁿ_{σ/8}`
  have hwW : ∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball (0 : Euclid n) (σ / 4 / 2) → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
      |∫ v in ball (0 : Euclid n) (σ / 4 / 2), ∑ i : Fin n,
        fderiv ℝ (fun v => s⁻¹ * EuclideanSpace.proj j (f v)) v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * (σ / 4 / 2) ^ n * G := by
    intro ζ hζ hζc hζs G hG
    have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG 0)
    have h1 := hGW j ζ G hζ hζc hζs hG
    simp_rw [hderiv, smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [integral_const_mul, abs_mul, abs_of_pos hsi]
    refine le_trans (mul_le_mul_of_nonneg_left h1 hsi.le) ?_
    rw [hsdef]
    exact (Submission.dorag_tesDecay_weak_real n k C₃ C₇ ω D δh E₀ I κ σ G hC₃ hC₇ hω hD hE₀
      hσ hG0 hIE hE₀le hκσE hD14).trans_eq (mul_assoc _ _ _)
  obtain ⟨a, b, hb, ha, hab⟩ := hHA' (σ / 4 / 2) (fun v => s⁻¹ * EuclideanSpace.proj j (f v))
    (Real.toNNReal s⁻¹) hR₀ hwLip hwE hwW
  refine ⟨a, b, hb, ha.trans ?_, hab θ' hθ' hθ'4⟩
  -- `|a| ≤ A`, from `|w| ≤ s⁻¹C₇Dσ` on `Bⁿ_{σ/8}`
  gcongr
  have hw2 : ∫ v in ball (0 : Euclid n) (σ / 4 / 2), (s⁻¹ * EuclideanSpace.proj j (f v)) ^ 2 ≤
      (s⁻¹ * (C₇ * D * σ)) ^ 2 * ((σ / 4 / 2) ^ n * ω) := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← hvol]
    refine norm_setIntegral_le_of_norm_le_const measure_ball_lt_top fun v _ => ?_
    rw [Real.norm_eq_abs, abs_pow, abs_mul, abs_of_pos hsi]
    gcongr
    exact (hproj _).trans (hfb v)
  calc Real.sqrt ((∫ v in ball (0 : Euclid n) (σ / 4 / 2),
        (s⁻¹ * EuclideanSpace.proj j (f v)) ^ 2) / (σ / 4 / 2) ^ n)
      ≤ Real.sqrt ((s⁻¹ * (C₇ * D * σ)) ^ 2 * ω) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ (by positivity)]
        exact hw2.trans_eq (by ring)
    _ = s⁻¹ * (C₇ * D * σ) * Real.sqrt ω := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- Bounds on the affine data `c, Λ` of Step 8 (Simon (18)): `|c| ≤ C₁₅DR₀` and
`‖Λ‖ ≤ kC_H(C₁₃C₃)^{1/2}D`, `R₀ = σ/8`. -/
theorem Submission.dorag_tesDecay_affine_consts (k : ℕ) (C₃ C₁₃ C₇ CH ω D E₀ ε' σ s A c Λ : ℝ)
    (hs : s = Real.sqrt (C₁₃ * E₀)) (hE₀ : 0 < E₀) (hE₀le : E₀ ≤ C₃ * D ^ 2) (hC₃ : 0 ≤ C₃)
    (hC₁₃ : 0 < C₁₃) (hD : 0 ≤ D) (hε'1 : ε' ≤ 1) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hω : 0 < ω)
    (hσ : 0 < σ)
    (hA : A = CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2))
    (hc : c ≤ k * s * A) (hΛ : Λ ≤ k * s * CH) :
    c ≤ (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) * D * (σ / 4 / 2) ∧
      Λ ≤ k * CH * Real.sqrt (C₁₃ * C₃) * D := by
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (mul_pos hC₁₃ hE₀)
  have hsle : s ≤ Real.sqrt (C₁₃ * C₃) * D := by
    rw [hs, ← Real.sqrt_sq hD, ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by rw [mul_assoc]; gcongr)
  have hε's : Real.sqrt ε' ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hε'1
  have hkA : (k : ℝ) * s * A ≤
      k * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) * D * (σ / 4 / 2) := by
    have h1 : (k : ℝ) * s * A =
        k * (CH * (C₇ * D * σ) * Real.sqrt ω + s * (CH * Real.sqrt ε' * (σ / 4 / 2))) := by
      rw [hA]
      field_simp
    rw [h1]
    have h3 : (k : ℝ) * (CH * (C₇ * D * σ) * Real.sqrt ω + s * (CH * Real.sqrt ε' * (σ / 4 / 2))) ≤
        k * (CH * (C₇ * D * σ) * Real.sqrt ω +
          (Real.sqrt (C₁₃ * C₃) * D) * (CH * 1 * (σ / 4 / 2))) := by
      gcongr
    refine h3.trans (le_of_eq ?_)
    ring
  constructor
  · refine hc.trans (hkA.trans ?_)
    gcongr
    linarith
  · refine hΛ.trans ?_
    calc (k : ℝ) * s * CH ≤ k * (Real.sqrt (C₁₃ * C₃) * D) * CH := by gcongr
      _ = k * CH * Real.sqrt (C₁₃ * C₃) * D := by ring

/-- The final real inequality of Steps 9–10 (Simon (20)–(23)), with `R₀ = σ/8`, `t = θ'R₀`:
`(θ₀σ)^{-n}C_T(t^{-2}((1 + n2ⁿ)ks²Q + K²C₇I) + κ²t²·2ωtⁿ) ≤ θ₀E₀`, `θ₀ = θ'/32`. -/
theorem Submission.dorag_tesDecay_final_real (n k : ℕ)
    (CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ R₀ t κ : ℝ)
    (hCT : 0 < CT) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hC₁₃ : 0 < C₁₃) (hω : 0 < ω)
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hε' : 0 ≤ ε') (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀)
    (hR₀ : 0 < R₀) (hσ : σ = 8 * R₀) (ht : t = θ' * R₀) (hs : s ^ 2 = C₁₃ * E₀)
    (hQ : Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2))
    (hK : 0 ≤ K) (hKle : K ≤ C₁₇ * D * R₀) (hI : 0 ≤ I) (hIle : I ≤ σ ^ n * E₀)
    (hκ : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hC₁₆ : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n +
      2 * ω))
    (h1 : C₁₆ * θ' ^ 2 ≤ θ' / 128) (h2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128)
    (h3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128) (h4 : C₁₆ * δ ≤ θ' / 128) :
    1 / (θ' / 32 * σ) ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q) +
      K ^ 2 * (C₇ * I)) + κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) ≤ θ' / 32 * E₀ := by
  subst hσ ht
  set t := θ' * R₀ with ht
  have htpos : 0 < t := mul_pos hθ' hR₀
  have hθ'pos : 0 < θ' ^ (n + 2) := pow_pos hθ' _
  have hpre : 1 / (θ' / 32 * (8 * R₀)) ^ n = 4 ^ n / t ^ n := by
    rw [show θ' / 32 * (8 * R₀) = t / 4 by rw [ht]; ring, div_pow]
    field_simp
  have htn : 0 < t ^ n := pow_pos htpos n
  set a := ε' / θ' ^ (n + 2) with ha
  set b := D ^ 2 / θ' ^ (n + 2) with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  -- the three terms
  have hT1 : 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q)))) =
      4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) * (a + θ' ^ 2) * E₀ := by
    rw [hs, hQ]
    field_simp
    ring
  have hT2 : 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I)))) ≤
      4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ := by
    have hK2 : K ^ 2 ≤ (C₁₇ * D * R₀) ^ 2 := pow_le_pow_left₀ hK hKle 2
    calc 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I))))
        ≤ 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((C₁₇ * D * R₀) ^ 2 * (C₇ * ((8 * R₀) ^ n * E₀))))) := by
          gcongr
      _ = 4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ := by
          rw [hb, ht]
          field_simp
          ring
  have hT3 : 4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) ≤
      4 ^ n * CT * (2 * ω) * δ * E₀ := by
    have htσ : t ^ 2 ≤ (8 * R₀) ^ 2 := by
      have : t ≤ 8 * R₀ := by rw [ht]; nlinarith
      exact pow_le_pow_left₀ htpos.le this 2
    have hκt : κ ^ 2 * t ^ 2 ≤ δ * E₀ := le_trans (by gcongr) hκ
    calc 4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))
        = 4 ^ n * CT * (2 * ω) * (κ ^ 2 * t ^ 2) := by field_simp
      _ ≤ 4 ^ n * CT * (2 * ω) * (δ * E₀) := by gcongr
      _ = 4 ^ n * CT * (2 * ω) * δ * E₀ := by ring
  -- coefficient comparisons with `C₁₆`
  have hc1 : 4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) ≤ C₁₆ := by
    rw [hC₁₆]
    have : (1 + n * 2 ^ n) * (k : ℝ) * CH * C₁₃ ≤
        (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω := by
      have h0 : (0 : ℝ) ≤ C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω := by positivity
      have h1' : (1 + n * 2 ^ n) * (k : ℝ) * CH * C₁₃ ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by
        gcongr
        linarith
      linarith
    gcongr
  have hc2 : 4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) ≤ C₁₆ := by
    rw [hC₁₆]
    gcongr
    have : (0 : ℝ) ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by positivity
    linarith
  have hc3 : 4 ^ n * CT * (2 * ω) ≤ C₁₆ := by
    rw [hC₁₆]
    gcongr
    have : (0 : ℝ) ≤ (1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ := by positivity
    have : (0 : ℝ) ≤ C₁₇ ^ 2 * C₇ * 8 ^ n := by positivity
    linarith
  rw [hpre]
  calc 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q) + K ^ 2 * (C₇ * I)) +
        κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))
      = 4 ^ n / t ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) * (k * s ^ 2 * Q)))) +
          4 ^ n / t ^ n * (CT * (1 / t ^ 2 * (K ^ 2 * (C₇ * I)))) +
          4 ^ n / t ^ n * (CT * (κ ^ 2 * t ^ 2 * (2 * ω * t ^ n))) := by ring
    _ ≤ 4 ^ n * CT * ((1 + n * 2 ^ n) * k * CH * C₁₃) * (a + θ' ^ 2) * E₀ +
          4 ^ n * CT * (C₁₇ ^ 2 * C₇ * 8 ^ n) * b * E₀ + 4 ^ n * CT * (2 * ω) * δ * E₀ := by
          rw [hT1]
          exact add_le_add (add_le_add le_rfl hT2) hT3
    _ ≤ C₁₆ * (a + θ' ^ 2) * E₀ + C₁₆ * b * E₀ + C₁₆ * δ * E₀ := by
          gcongr
    _ = (C₁₆ * a + C₁₆ * θ' ^ 2 + C₁₆ * b + C₁₆ * δ) * E₀ := by ring
    _ ≤ (θ' / 128 + θ' / 128 + θ' / 128 + θ' / 128) * E₀ := by gcongr
    _ = θ' / 32 * E₀ := by ring

/-- Steps 9–10, `ENNReal` form: the chain of the tilt-height, graph-height, affine-assembly and
density estimates gives `(θ₀σ)^{-n}∫_{B_{θ₀σ}(ξ)}|p_x − p_S|² dμ ≤ θ₀E₀`. -/
theorem Submission.dorag_tesDecay_conclude (n k : ℕ) (X J L MF Mt : ℝ≥0∞)
    (CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ R₀ t κ : ℝ)
    (hX : X ≤ ENNReal.ofReal CT * (ENNReal.ofReal (1 / t ^ 2) * J +
      ENNReal.ofReal (κ ^ 2 * t ^ 2) * Mt))
    (hJ : J ≤ ENNReal.ofReal (1 + n * 2 ^ n) * L + ENNReal.ofReal (K ^ 2) * MF)
    (hL : L ≤ ENNReal.ofReal (k * s ^ 2 * Q)) (hMF : MF ≤ ENNReal.ofReal (C₇ * I))
    (hMt : Mt ≤ ENNReal.ofReal (2 * ω * t ^ n))
    (hCT : 0 < CT) (hCH : 0 < CH) (hC₇ : 0 < C₇) (hC₁₃ : 0 < C₁₃) (hω : 0 < ω)
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hε' : 0 ≤ ε') (hδ : 0 ≤ δ) (hE₀ : 0 ≤ E₀)
    (hR₀ : 0 < R₀) (hσ : σ = 8 * R₀) (ht : t = θ' * R₀) (hs : s ^ 2 = C₁₃ * E₀)
    (hQ : Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2))
    (hK : 0 ≤ K) (hKle : K ≤ C₁₇ * D * R₀) (hI : 0 ≤ I) (hIle : I ≤ σ ^ n * E₀)
    (hκ : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hC₁₆ : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ + C₁₇ ^ 2 * C₇ * 8 ^ n +
      2 * ω))
    (h1 : C₁₆ * θ' ^ 2 ≤ θ' / 128) (h2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128)
    (h3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128) (h4 : C₁₆ * δ ≤ θ' / 128) :
    ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * X ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
  have htpos : 0 < t := ht ▸ mul_pos hθ' hR₀
  have hσpos : 0 < σ := by rw [hσ]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  calc ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * X
      ≤ ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * (ENNReal.ofReal CT * (ENNReal.ofReal (1 / t ^ 2) *
        (ENNReal.ofReal (1 + n * 2 ^ n) * ENNReal.ofReal (k * s ^ 2 * Q) +
          ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C₇ * I)) +
        ENNReal.ofReal (κ ^ 2 * t ^ 2) * ENNReal.ofReal (2 * ω * t ^ n))) := by
        gcongr
        refine hX.trans ?_
        gcongr
        refine hJ.trans ?_
        gcongr
    _ = ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n * (CT * (1 / t ^ 2 * ((1 + n * 2 ^ n) *
          (k * s ^ 2 * Q) + K ^ 2 * (C₇ * I)) + κ ^ 2 * t ^ 2 * (2 * ω * t ^ n)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (θ' / 32 * E₀) :=
        ENNReal.ofReal_le_ofReal (Submission.dorag_tesDecay_final_real n k CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ'
          ε' D δ E₀ I s Q K σ R₀ t κ hCT hCH hC₇ hC₁₃ hω hθ' hθ'4 hε' hδ hE₀ hR₀ hσ ht hs hQ hK
          hKle hI hIle hκ hC₁₆ h1 h2 h3 h4)

/-- Steps 3–9 of the tilt-excess decay (Simon Ch. 5, proof of 4.5, (5)–(22)).  Let `f` be the
`1`-Lipschitz approximation over the plane `T'` (tilt `I ≤ σⁿE₀` and height `≤ C₁₁Dσ` on `B_σ(ξ)`)
with the estimate (4′) for the non-graph part.  Then (Steps 3–6) every component `fʲ` has energy
`≤ (2 + C₇)I` and is weakly harmonic up to an error, on `Bⁿ_{σ/8}`; (Step 7) the harmonic
approximation lemma applies to `(C₁₃E₀)^{-1/2}fʲ`; (Step 8) the components assemble to an affine
map `c + Λ`; (Step 9) the height about `S = graph Λ` at `τ = ξ + ι'c` is controlled, and the
tilt-height estimate at `(τ, θ'σ/8)` gives `(θ₀σ)^{-n}∫_{B_{θ₀σ}(ξ)}|p_x − p_S|² dμ ≤ θ₀E₀`,
`θ₀ = θ'/32`. -/
theorem Submission.dorag_tesDecay_core (n k : ℕ) (hn : 0 < n) (U W : Set (Euclid (n + k)))
    (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ : ℝ) (ξ : Euclid (n + k)) (σ : ℝ)
    (T' : Submodule ℝ (Euclid (n + k))) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k))
    (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k)
    (C₃ C₇ C₁₁ C₁₃ C₁₄ C₁₅ C₁₆ C₁₇ CT CH ω θ' ε' δh D δ E₀ I : ℝ)
    (hW : IsOpen W) (hWU : W ⊆ U) (hH : AEStronglyMeasurable H R.measure)
    (hHκ : ∀ x, ‖H x‖ ≤ κ)
    (hMC : ∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X →
      tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure)
    (hTH : ∀ (ξ : Euclid (n + k)) (r : ℝ) (S : Submodule ℝ (Euclid (n + k))), 0 < r →
      closedBall ξ r ⊆ W → Module.finrank ℝ S = n →
      ∫⁻ x in closedBall ξ (r / 2), ENNReal.ofReal (∑ i : Fin (n + k),
        ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤
        ENNReal.ofReal CT * (ENNReal.ofReal (1 / r ^ 2) * ∫⁻ x in closedBall ξ r,
          ENNReal.ofReal (‖(x - ξ) - S.starProjection (x - ξ)‖ ^ 2) ∂R.measure +
          ENNReal.ofReal (κ ^ 2 * r ^ 2) * R.measure (closedBall ξ r)))
    (hHA' : ∀ (R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w →
      ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n →
      (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) →
        |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δh * R₀ ^ n * G) →
      ∃ (a : ℝ) (b : Euclid n →L[ℝ] ℝ), ‖b‖ ≤ CH ∧
        |a| ≤ CH * Real.sqrt ((∫ v in ball (0 : Euclid n) R₀, w v ^ 2) / R₀ ^ n) +
          CH * Real.sqrt ε' * R₀ ∧
        ∀ θ' : ℝ, 0 < θ' → θ' ≤ 1 / 4 → ∫ v in ball (0 : Euclid n) (θ' * R₀), (w v - a - b v) ^ 2 ≤
          CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * (θ' * R₀) ^ (n + 2))
    (hσ : 0 < σ) (hBW : closedBall ξ σ ⊆ W)
    (hμ : ∀ y ∈ closedBall ξ σ, ∀ t : ℝ, 0 < t → t ≤ σ →
      R.measure (closedBall y t) ≤ ENNReal.ofReal (2 * ω * t ^ n))
    (hmult : ∀ᵐ x ∂R.measure, x ∈ closedBall ξ σ → R.mult x = 1)
    (hT'n : Module.finrank ℝ T' = n)
    (hT'h : ∀ x ∈ R.measure.support ∩ closedBall ξ σ,
      ‖(x - ξ) - T'.starProjection (x - ξ)‖ ≤ C₁₁ * D * σ)
    (hItilt : ∫⁻ x in closedBall ξ (σ / 4), ENNReal.ofReal (∑ i : Fin (n + k),
      ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) -
        T'.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal I)
    (hιι' : ∀ v w, inner ℝ (ι v) (ι' w) = 0) (hιT : ∀ v, ι v ∈ T')
    (hfL : ∀ v w, ‖f v - f w‖ ≤ 1 * ‖v - w‖) (hfb : ∀ v, ‖f v‖ ≤ C₇ * D * σ)
    (h5A : R.measure (closedBall ξ (σ / 2) \ range (fun v => ξ + ι v + ι' (f v))) +
      μHE[n] ((range (fun v => ξ + ι v + ι' (f v)) \ R.measure.support) ∩ closedBall ξ (σ / 4)) ≤
        ENNReal.ofReal (C₇ * I))
    (hωeq : unitBallVolume n = ENNReal.ofReal ω)
    (hC₃ : 1 ≤ C₃) (hC₇ : 0 < C₇) (hC₁₁ : 0 < C₁₁) (hCT : 0 < CT) (hCH : 0 < CH) (hω : 0 < ω)
    (hC₁₃def : C₁₃ = (2 + C₇) * 8 ^ n)
    (hC₁₄def : C₁₄ = 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ +
      2 * ω / 4 ^ (n + 1)) / Real.sqrt ((2 + C₇) * 8 ^ n))
    (hC₁₅def : C₁₅ = (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)))
    (hC₁₇def : C₁₇ = 8 * C₁₁ + C₁₅ + k * CH * Real.sqrt (C₁₃ * C₃))
    (hC₁₆def : C₁₆ = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ +
      C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω))
    (hθ' : 0 < θ') (hθ'4 : θ' ≤ 1 / 4) (hθ'C : θ' * C₁₆ ≤ 1 / 128) (hε' : 0 < ε')
    (hε'1 : ε' ≤ 1) (hε'C : ε' * C₁₆ ≤ θ' ^ (n + 3) / 128)
    (hD : 0 < D) (hD1 : D ≤ 1) (hD7 : D * C₇ ≤ 1 / 16) (hD11 : D * C₁₁ ≤ 1 / 16)
    (hD14 : D * C₁₄ ≤ δh) (hD15 : D * C₁₅ ≤ θ' / 4) (hD16a : D * C₁₆ ≤ θ' ^ (n + 3) / 128)
    (hD16b : D * C₁₆ ≤ θ' / 128) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hI0 : 0 ≤ I) (hE₀p : 0 < E₀) (hIE : I ≤ σ ^ n * E₀) (hκE : κ ^ 2 * σ ^ 2 ≤ δ * E₀)
    (hE₀le : E₀ ≤ C₃ * D ^ 2) (hκσE : κ * σ ≤ D * Real.sqrt E₀) :
    ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧
      ENNReal.ofReal (1 / (θ' / 32 * σ) ^ n) * ∫⁻ x in closedBall ξ (θ' / 32 * σ),
        ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection
          (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
          ∂R.measure ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
  have hC₁₃ : 0 < C₁₃ := by rw [hC₁₃def]; positivity
  have hC₁₆ : 0 < C₁₆ := by rw [hC₁₆def]; positivity
  have hE₀0 : 0 ≤ E₀ := hE₀p.le
  have hAESM := Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R
  have hnull := Submission.dorag_support_sdiff_carrier_null n k hn U W R H κ hW hWU hH hHκ hMC
  have hf1 : ∀ v w, ‖f v - f w‖ ≤ ‖v - w‖ := fun v w => by simpa using hfL v w
  have hfLip : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun v w => by
    simpa [dist_eq_norm] using hfL v w
  /- Steps 3–6: energy bound and weak harmonic equation for `fʲ` on `Bⁿ_{σ/8}`. -/
  have hGT := Submission.dorag_tesDecay_ae_of_carrier R hW.measurableSet
    (Submission.dorag_lipschitz_graph_approxTangent n k hn U W R ι ι' ξ f 1 hW hWU hιι' hfLip)
  have hσ4 : σ / 4 ≤ σ := by linarith only [hσ]
  have hsmall : ∀ C : ℝ, D * C ≤ 1 / 16 → C * D * σ ≤ σ / 4 / 4 := fun C hC => by
    calc C * D * σ = (D * C) * σ := by ring
      _ ≤ 1 / 16 * σ := by gcongr
      _ = σ / 4 / 4 := by ring
  have hμσ4 : R.measure (closedBall ξ (σ / 4)) ≤ ENNReal.ofReal (2 * ω * (σ / 4) ^ n) :=
    hμ ξ (mem_closedBall_self hσ.le) (σ / 4) (by positivity) hσ4
  obtain ⟨hGE, hGW⟩ := Submission.dorag_tes_graph_weak_harmonic n k hn U W R H κ ξ (σ / 4) I (C₇ * I)
    (2 * ω * (σ / 4) ^ n) T' ι ι' f hW hWU hH hHκ hMC hAESM (by positivity)
    ((closedBall_subset_closedBall hσ4).trans hBW) hI0 (by positivity) (by positivity) hT'n hιι' hιT
    hf1 (fun v => (hfb v).trans (hsmall C₇ hD7))
    (fun x hx => (hT'h x ⟨hx.1, closedBall_subset_closedBall hσ4 hx.2⟩).trans (hsmall C₁₁ hD11))
    (by
      filter_upwards [hGT] with x hx hxB using hx (hBW (closedBall_subset_closedBall hσ4 hxB)))
    (by filter_upwards [hmult] with x hx hxB using hx (closedBall_subset_closedBall hσ4 hxB))
    hnull hItilt
    ((add_le_add (measure_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall
      (by linarith only [hσ] : σ / 4 ≤ σ / 2)))) le_rfl).trans h5A)
    hμσ4
  /- Step 7: harmonic approximation of `w = s⁻¹fʲ`, `s = (C₁₃E₀)^{1/2}`, on `Bⁿ_{R₀}`, `R₀ = σ/8`. -/
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (C₁₃ * E₀) := ⟨_, rfl⟩
  have hs : 0 < s := hsdef ▸ Real.sqrt_pos.mpr (mul_pos hC₁₃ hE₀p)
  have hs2 : s ^ 2 = C₁₃ * E₀ := by rw [hsdef, Real.sq_sqrt (by positivity)]
  have hsi : 0 < s⁻¹ := inv_pos.mpr hs
  have hR₀ : 0 < σ / 4 / 2 := by positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = θ' * (σ / 4 / 2) := ⟨_, rfl⟩
  have ht : 0 < t := htdef ▸ mul_pos hθ' hR₀
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = CH * (s⁻¹ * (C₇ * D * σ) * Real.sqrt ω) + CH * Real.sqrt ε' * (σ / 4 / 2) := ⟨_, rfl⟩
  have hvol : volume.real (ball (0 : Euclid n) (σ / 4 / 2)) = (σ / 4 / 2) ^ n * ω := by
    rw [Measure.real, Measure.addHaar_ball_of_pos volume 0 hR₀, finrank_euclideanSpace_fin]
    change (ENNReal.ofReal ((σ / 4 / 2) ^ n) * unitBallVolume n).toReal = _
    rw [hωeq, ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have hwj := Submission.dorag_tesDecay_harmonic_step n k f C₃ C₇ CH ω D δh ε' E₀ I κ σ s θ' hHA'
    hGE hGW hf1 hfb (by rw [hsdef, hC₁₃def]) hC₃ hC₇ hCH hω hD.le hE₀p hσ hθ' hθ'4 hIE hE₀le hκσE
    (by rw [← hC₁₄def, mul_comm]; exact hD14) hvol
  clear hHA' hGE hGW
  rw [← hAdef, ← htdef] at hwj
  /- Step 8: the affine map `c + Λ`. -/
  obtain ⟨c, Λ, hc, hΛ, hfcΛ⟩ := Submission.dorag_tes_componentwise_affine_assembly n k f s A CH
    (CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2)) t hfLip.continuous hs hwj
  obtain ⟨hc', hΛ'⟩ := Submission.dorag_tesDecay_affine_consts k C₃ C₁₃ C₇ CH ω D E₀ ε' σ s A ‖c‖ ‖Λ‖
    hsdef hE₀p hE₀le (by linarith only [hC₃]) hC₁₃ hD.le hε'1 hCH hC₇ hω hσ hAdef hc hΛ
  rw [← hC₁₅def] at hc'
  /- Step 9: height about `S = graph Λ` at `τ = ξ + ι'c`, then tilt via the tilt-height estimate. -/
  have hcR : ‖c‖ ≤ t / 4 := by
    calc ‖c‖ ≤ C₁₅ * D * (σ / 4 / 2) := hc'
      _ = (D * C₁₅) * (σ / 4 / 2) := by ring
      _ ≤ θ' / 4 * (σ / 4 / 2) := by gcongr
      _ = t / 4 := by rw [htdef]; ring
  have hτξ : dist (ξ + ι' c) ξ = ‖c‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, LinearIsometry.norm_map]
  have htσ : t ≤ σ / 32 := by
    calc t = θ' * (σ / 4 / 2) := htdef
      _ ≤ 1 / 4 * (σ / 4 / 2) := by gcongr
      _ = σ / 32 := by ring
  have hBt2 : closedBall (ξ + ι' c) t ⊆ closedBall ξ (σ / 2) :=
    closedBall_subset_closedBall' (by rw [hτξ]; linarith only [hcR, htσ, ht, hσ])
  have hBtσ : closedBall (ξ + ι' c) t ⊆ closedBall ξ σ :=
    hBt2.trans (closedBall_subset_closedBall (by linarith only [hσ]))
  obtain ⟨hSn, hSh⟩ := Submission.dorag_tes_graph_affine_height n k hn U R ξ T' ι ι' f c Λ t
    (C₁₁ * D * σ) ht (by positivity) hT'n hιι' hιT hf1
    (by filter_upwards [hmult] with x hx hxB using hx (hBtσ hxB))
    (fun x hx => hT'h x ⟨hx.1, hBtσ hx.2⟩)
  have hTHS := hTH (ξ + ι' c) t _ ht (hBtσ.trans hBW) hSn
  have hμt : R.measure (closedBall (ξ + ι' c) t) ≤ ENNReal.ofReal (2 * ω * t ^ n) :=
    hμ (ξ + ι' c) (hBtσ (mem_closedBall_self ht.le)) t ht (htσ.trans (by linarith only [hσ]))
  have hμtF : R.measure (closedBall (ξ + ι' c) t \ range fun v => ξ + ι v + ι' (f v)) ≤
      ENNReal.ofReal (C₇ * I) :=
    (measure_mono (sdiff_subset_sdiff_left hBt2)).trans (le_self_add.trans h5A)
  have hθσ : θ' / 32 * σ = t / 4 := by rw [htdef]; ring
  have hBsub : closedBall ξ (θ' / 32 * σ) ⊆ closedBall (ξ + ι' c) (t / 2) :=
    closedBall_subset_closedBall' (by rw [hθσ, dist_comm, hτξ]; linarith only [hcR])
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = C₁₁ * D * σ + ‖c‖ + ‖Λ‖ * t := ⟨_, rfl⟩
  rw [← hKdef] at hSh
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  have hKle : K ≤ C₁₇ * D * (σ / 4 / 2) := by
    have htR : t ≤ σ / 4 / 2 := by
      rw [htdef]
      exact mul_le_of_le_one_left hR₀.le (by linarith only [hθ'4])
    calc K = C₁₁ * D * σ + ‖c‖ + ‖Λ‖ * t := hKdef
      _ ≤ C₁₁ * D * σ + C₁₅ * D * (σ / 4 / 2) +
          (k * CH * Real.sqrt (C₁₃ * C₃) * D) * (σ / 4 / 2) := by gcongr
      _ = C₁₇ * D * (σ / 4 / 2) := by rw [hC₁₇def]; ring
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = CH * (ε' / θ' ^ (n + 2) + θ' ^ 2) * t ^ (n + 2) := ⟨_, rfl⟩
  rw [← hQdef] at hfcΛ
  refine ⟨_, hSn, ?_⟩
  -- Step 10: the choice of `θ'`, `ε'` and `δ₂`
  have hc1 : C₁₆ * θ' ^ 2 ≤ θ' / 128 := by
    calc C₁₆ * θ' ^ 2 = (θ' * C₁₆) * θ' := by ring
      _ ≤ 1 / 128 * θ' := by gcongr
      _ = θ' / 128 := by ring
  have hc2 : C₁₆ * (ε' / θ' ^ (n + 2)) ≤ θ' / 128 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    calc C₁₆ * ε' = ε' * C₁₆ := by ring
      _ ≤ θ' ^ (n + 3) / 128 := hε'C
      _ = θ' / 128 * θ' ^ (n + 2) := by ring
  have hc3 : C₁₆ * (D ^ 2 / θ' ^ (n + 2)) ≤ θ' / 128 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    calc C₁₆ * D ^ 2 = (D * C₁₆) * D := by ring
      _ ≤ θ' ^ (n + 3) / 128 * 1 := by gcongr
      _ = θ' / 128 * θ' ^ (n + 2) := by ring
  have hc4 : C₁₆ * δ ≤ θ' / 128 := by
    calc C₁₆ * δ ≤ C₁₆ * D := by gcongr
      _ = D * C₁₆ := by ring
      _ ≤ θ' / 128 := hD16b
  exact Submission.dorag_tesDecay_conclude n k _ _ _ _ _ CT CH C₇ C₁₃ C₁₇ C₁₆ ω θ' ε' D δ E₀ I s Q K σ
    (σ / 4 / 2) t κ ((lintegral_mono_set hBsub).trans hTHS) hSh hfcΛ hμtF hμt hCT hCH hC₇ hC₁₃ hω
    hθ' hθ'4 hε'.le hδ.le hE₀0 hR₀ (by ring) htdef hs2 hQdef hK0 hKle hI0 hIE hκE hC₁₆def hc1 hc2 hc3
    hc4

/-- **Tilt-excess decay, one step** (Simon Ch. 5, Theorem 4.5 with `p = 2n`, bounded `H`; parent
proof Part 7, Claim 7A, Steps 0–11).  There are `θ₀ ∈ (0, 1/4]` and `δ₂ ∈ (0, 1/8]` such that under
(SA_δ), `δ ≤ δ₂`, for every `ξ ∈ spt μ ∩ B_{δρ}(z)`, `σ ∈ (0, δρ]` and `n`-plane `T` there is an
`n`-plane `S` with `E_*(ξ, θ₀σ, S) ≤ θ₀E_*(ξ, σ, T)`.
Step 1 replaces `T` by a plane `T'` with `E(ξ, σ, T') ≤ C₃δ^{2α}` and height `≤ C₁₁δ^ασ`
(affine approximation and plane reduction).  Step 2 is the Lipschitz approximation `f` over `T'`;
Steps 3–6 give the energy bound and the weak harmonic equation for `fʲ` on `Bⁿ_{σ/8}`; Step 7 is
the harmonic approximation of `(C₁₃E₀)^{-1/2}fʲ`; Step 8 assembles the affine map `c + Λ`; Step 9
bounds the height about `S = graph Λ` at `τ = ξ + ι'c` and converts it to tilt; Step 10 fixes
`θ' = 32θ₀`, `ε'` and `δ₂` in this order. -/
theorem Submission.dorag_tilt_excess_one_step_decay : ∀ (n k : ℕ), 0 < n → ∃ θ₀ δ₂ : ℝ, 0 < θ₀ ∧ θ₀ ≤ 1 / 4 ∧ 0 < δ₂ ∧ δ₂ ≤ 1 / 8 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₂ → ∀ (U W : Set (Euclid (n + k))) (R : IMRep U n) (H : Euclid (n + k) → Euclid (n + k)) (κ ρ : ℝ) (z : Euclid (n + k)), IsOpen W → W ⊆ U → 0 < ρ → closedBall z ρ ⊆ W → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid (n + k) → Euclid (n + k), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ W → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → z ∈ R.measure.support → R.measure (closedBall z ρ) ≤ ENNReal.ofReal (1 + δ) * unitBallVolume n * ENNReal.ofReal (ρ ^ n) → κ * ρ ≤ δ → ∀ ξ ∈ R.measure.support ∩ closedBall z (δ * ρ), ∀ (σ : ℝ) (T : Submodule ℝ (Euclid (n + k))), 0 < σ → σ ≤ δ * ρ → Module.finrank ℝ T = n → ∃ S : Submodule ℝ (Euclid (n + k)), Module.finrank ℝ S = n ∧ max (ENNReal.ofReal (1 / (θ₀ * σ) ^ n) * ∫⁻ x in closedBall ξ (θ₀ * σ), ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * (θ₀ * σ) ^ 2 / δ)) ≤ ENNReal.ofReal θ₀ * max (ENNReal.ofReal (1 / σ ^ n) * ∫⁻ x in closedBall ξ σ, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - T.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure) (ENNReal.ofReal (κ ^ 2 * σ ^ 2 / δ)) := by
  intro n k hn
  /- Step 0: the constants.  Sibling constants first. -/
  obtain ⟨δ₁, C₂, hδ₁, hδ₁8, -, hDB⟩ := Submission.dorag_standing_density_bounds n k hn
  obtain ⟨δ₃, C₃, hδ₃, hδ₃8, hC₃, hAA⟩ := Submission.dorag_affine_approximation n k hn
  obtain ⟨CT, hCT, hTH⟩ := Submission.dorag_tilt_height_estimate n k
  obtain ⟨CH, hCH, hHA⟩ := Submission.dorag_harmonic_affine_approximation n hn
  -- `ω = ω_n ∈ (0, ∞)`
  have hωfin : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  obtain ⟨ω, hωdef⟩ : ∃ ω : ℝ, ω = (unitBallVolume n).toReal := ⟨_, rfl⟩
  have hω : 0 < ω := hωdef ▸ ENNReal.toReal_pos hω0 hωfin
  have hωeq : unitBallVolume n = ENNReal.ofReal ω := by rw [hωdef, ENNReal.ofReal_toReal hωfin]
  have h2ω : ∀ x : ℝ, 0 ≤ x → 2 * unitBallVolume n * ENNReal.ofReal x = ENNReal.ofReal (2 * ω * x) := by
    intro x hx
    rw [hωeq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  -- `C₁₁ = 2C₃ + (8C₃/ω)^{1/2}` and the Lipschitz approximation constants for `C₆ = C₁₁`
  obtain ⟨C₁₁, hC₁₁def⟩ : ∃ C : ℝ, C = 2 * C₃ + Real.sqrt (8 * C₃ / ω) := ⟨_, rfl⟩
  have hC₃C₁₁ : C₃ ≤ C₁₁ := by
    rw [hC₁₁def]
    have := Real.sqrt_nonneg (8 * C₃ / ω)
    linarith only [this, hC₃]
  have hC₁₁ : 1 ≤ C₁₁ := hC₃.trans hC₃C₁₁
  have hC₁₁0 : 0 < C₁₁ := by linarith only [hC₁₁]
  obtain ⟨δ₅, β, β', C₇, hδ₅, -, hβ', hβ'β, -, hC₇, hLA⟩ :=
    Submission.dorag_lipschitz_approximation n k hn C₁₁ hC₁₁
  have hβ : 0 < β := hβ'.trans_le hβ'β
  -- `C₁₃, …, C₁₆` (Steps 6–9)
  obtain ⟨C₁₃, hC₁₃def⟩ : ∃ C : ℝ, C = (2 + C₇) * 8 ^ n := ⟨_, rfl⟩
  obtain ⟨C₁₄, hC₁₄def⟩ : ∃ C : ℝ, C = 8 ^ n * ((2 + 2 ^ (n + 1) * k) * (1 + C₇) * Real.sqrt C₃ +
      2 * ω / 4 ^ (n + 1)) / Real.sqrt ((2 + C₇) * 8 ^ n) := ⟨_, rfl⟩
  obtain ⟨C₁₅, hC₁₅def⟩ : ∃ C : ℝ,
      C = (k + 1) * CH * (8 * C₇ * Real.sqrt ω + Real.sqrt (C₁₃ * C₃)) := ⟨_, rfl⟩
  obtain ⟨C₁₇, hC₁₇def⟩ : ∃ C : ℝ, C = 8 * C₁₁ + C₁₅ + k * CH * Real.sqrt (C₁₃ * C₃) := ⟨_, rfl⟩
  obtain ⟨C₁₆, hC₁₆def⟩ : ∃ C : ℝ, C = 4 ^ n * CT * ((1 + n * 2 ^ n) * (k + 1) * CH * C₁₃ +
      C₁₇ ^ 2 * C₇ * 8 ^ n + 2 * ω) := ⟨_, rfl⟩
  have hC₁₃ : 0 < C₁₃ := by rw [hC₁₃def]; positivity
  have hC₁₄ : 0 < C₁₄ := by rw [hC₁₄def]; positivity
  have hC₁₅ : 0 < C₁₅ := by rw [hC₁₅def]; positivity
  have hC₁₆ : 0 < C₁₆ := by rw [hC₁₆def]; positivity
  -- Step 10: `θ'` with `C₁₆θ'² ≤ θ'/128`, then `ε'` with `C₁₆θ'^{-n-2}ε' ≤ θ'/128`
  obtain ⟨θ', hθ'def⟩ : ∃ θ : ℝ, θ = min (1 / 4) (1 / 128 / C₁₆) := ⟨_, rfl⟩
  have hθ' : 0 < θ' := by rw [hθ'def]; positivity
  have hθ'4 : θ' ≤ 1 / 4 := hθ'def ▸ min_le_left _ _
  have hθ'C : θ' * C₁₆ ≤ 1 / 128 :=
    (le_div_iff₀ hC₁₆).mp (hθ'def ▸ min_le_right _ _)
  obtain ⟨ε', hε'def⟩ : ∃ ε : ℝ, ε = min 1 (θ' ^ (n + 3) / 128 / C₁₆) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by rw [hε'def]; positivity
  have hε'1 : ε' ≤ 1 := hε'def ▸ min_le_left _ _
  have hε'C : ε' * C₁₆ ≤ θ' ^ (n + 3) / 128 :=
    (le_div_iff₀ hC₁₆).mp (hε'def ▸ min_le_right _ _)
  obtain ⟨δh, hδh, hHA'⟩ := hHA ε' hε'
  -- the smallness threshold for `D = δ^{1/(2n+2)}`, and `δ₂`
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (min (min β (1 / 16 / C₁₁)) (min (1 / 16 / C₇) (δh / C₁₄)))
      (min (min (θ' / 4 / C₁₅) (θ' ^ (n + 3) / 128 / C₁₆)) (min (θ' / 128 / C₁₆) 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hηs : η ≤ β ∧ η ≤ 1 / 16 / C₁₁ ∧ η ≤ 1 / 16 / C₇ ∧ η ≤ δh / C₁₄ ∧ η ≤ θ' / 4 / C₁₅ ∧
      η ≤ θ' ^ (n + 3) / 128 / C₁₆ ∧ η ≤ θ' / 128 / C₁₆ ∧ η ≤ 1 := by
    rw [hηdef]
    simp only [min_le_iff, le_refl, true_or, or_true, and_self]
  obtain ⟨hηβ, hη11, hη7, hη14, hη15, hη16a, hη16b, hη1⟩ := hηs
  obtain ⟨δ₂, hδ₂def⟩ : ∃ d : ℝ, d = min (min (min (min (1 / 8) δ₁) δ₃) δ₅) (η ^ (2 * n + 2)) :=
    ⟨_, rfl⟩
  have hδ₂ : 0 < δ₂ := by rw [hδ₂def]; positivity
  have hδ₂8 : δ₂ ≤ 1 / 8 := by
    rw [hδ₂def]
    exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans
      (min_le_left _ _)))
  refine ⟨θ' / 32, δ₂, by positivity, by linarith only [hθ'4], hδ₂, hδ₂8, ?_⟩
  intro δ hδ hδδ₂ U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ ξ hξ σ T hσ hσδρ hT
  have hδs : δ ≤ 1 / 8 ∧ δ ≤ δ₁ ∧ δ ≤ δ₃ ∧ δ ≤ δ₅ ∧ δ ≤ η ^ (2 * n + 2) := by
    rw [hδ₂def] at hδδ₂
    simp only [le_min_iff] at hδδ₂
    tauto
  obtain ⟨hδ8, hδ₁', hδ₃', hδ₅', hδη⟩ := hδs
  -- `D = δ^α`, `α = 1/(2n+2)`
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = δ ^ ((1 : ℝ) / (2 * (n : ℝ) + 2)) := ⟨_, rfl⟩
  obtain ⟨hD, hDη, hδD, hsδD⟩ :=
    Submission.dorag_tesDecay_rpow n δ η hδ (by linarith only [hδ8]) hη hδη
  rw [← hDdef] at hD hDη hδD hsδD
  have hDβ : D ≤ β := hDη.trans hηβ
  have hD11 : D * C₁₁ ≤ 1 / 16 := (le_div_iff₀ hC₁₁0).mp (hDη.trans hη11)
  have hD7 : D * C₇ ≤ 1 / 16 := (le_div_iff₀ hC₇).mp (hDη.trans hη7)
  have hD14 : D * C₁₄ ≤ δh := (le_div_iff₀ hC₁₄).mp (hDη.trans hη14)
  have hD15 : D * C₁₅ ≤ θ' / 4 := (le_div_iff₀ hC₁₅).mp (hDη.trans hη15)
  have hD16a : D * C₁₆ ≤ θ' ^ (n + 3) / 128 := (le_div_iff₀ hC₁₆).mp (hDη.trans hη16a)
  have hD16b : D * C₁₆ ≤ θ' / 128 := (le_div_iff₀ hC₁₆).mp (hDη.trans hη16b)
  have hD1 : D ≤ 1 := hDη.trans hη1
  -- elementary facts about the data
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hξz : dist ξ z ≤ δ * ρ := mem_closedBall.mp hξ.2
  have hδρ : 0 < δ * ρ := mul_pos hδ hρ
  have hδρ8 : δ * ρ ≤ ρ / 8 := by
    calc δ * ρ ≤ 1 / 8 * ρ := mul_le_mul_of_nonneg_right hδ8 hρ.le
      _ = ρ / 8 := by ring
  have hBz : closedBall ξ σ ⊆ closedBall z (4 * δ * ρ) :=
    closedBall_subset_closedBall' (by linarith only [hσδρ, hξz, hδρ])
  have hBW : closedBall ξ σ ⊆ W :=
    (closedBall_subset_closedBall' (by linarith only [hσδρ, hξz, hδρ8, hρ])).trans hzρ
  have hσρ : σ ≤ (1 - 4 * δ) * ρ := by linarith only [hσδρ, hδρ8, hρ]
  obtain ⟨hDBa, hDBb, -, hDBd⟩ :=
    hDB δ hδ hδ₁' U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ
  clear hDB
  have hAESM := Submission.dorag_approxTangent_starProjection_aesm (n + k) n U R
  /- Step 1: affine approximation at `(ξ, 2σ)` and reduction to a plane `T'` with small tilt and
  height. -/
  obtain ⟨T₁, hT₁n, hT₁h, hT₁t⟩ := hAA δ hδ hδ₃' U W R H κ ρ z hW hWU hρ hzρ hH hHκ hMC hz hdens hκρ ξ
    ⟨hξ.1, mem_closedBall.mpr (by linarith only [hξz, hδρ])⟩ (2 * σ) (by linarith only [hσ])
    (by linarith only [hσδρ])
  clear hAA
  rw [← hDdef] at hT₁h hT₁t
  rw [show 2 * σ / 2 = σ by ring] at hT₁t
  have hμσ : ENNReal.ofReal (ω * σ ^ n / 2) ≤ R.measure (closedBall ξ σ) := by
    have h := hDBb ξ ⟨hξ.1, hBz (mem_closedBall_self hσ.le)⟩ σ hσ hσρ
    rw [hωeq, ← ENNReal.ofReal_mul hω.le] at h
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_of_le_mul (h.trans_eq (mul_comm _ _))
  obtain ⟨T', hT'TT, hT'a, hT'T, hT'h⟩ := Submission.dorag_tes_plane_reduction (n + k) R.measure
    (approxTangentPlane n R.carrier) ξ σ (C₃ * D ^ 2 * σ ^ n) (ω * σ ^ n / 2) (C₃ * D * (2 * σ)) T T₁
    hσ (by positivity) (by positivity) hAESM hμσ hT₁t
    (fun x hx => hT₁h x ⟨hx.1, closedBall_subset_closedBall (by linarith only [hσ]) hx.2⟩)
  rw [Submission.dorag_tesDecay_height_const n C₃ ω D σ (by linarith only [hC₃]) hω hD.le hσ,
    ← hC₁₁def]
    at hT'h
  have hT'n : Module.finrank ℝ T' = n := by
    rcases hT'TT with rfl | rfl <;> assumption
  -- `I = ∫_{B_σ(ξ)} |p_x − p_{T'}|² dμ` and `E₀ = E_*(ξ, σ, T')`
  obtain ⟨I, hI0, hIeq, hIa⟩ := Submission.dorag_tesDecay_real_of_le (by positivity) hT'a
  rw [← hIeq] at hT'T
  obtain ⟨E₀, hE₀def⟩ : ∃ E : ℝ, E = max (1 / σ ^ n * I) (κ ^ 2 * σ ^ 2 / δ) := ⟨_, rfl⟩
  obtain ⟨hE₀0, hIE, hκE, hE₀le, hκσE⟩ := Submission.dorag_tesDecay_excess_facts n C₃ D δ E₀ I κ ρ σ
    hδ hδ8 hσ hσδρ hκ hκρ hC₃ hδD hsδD hIa hE₀def
  have hE₀2 : κ ^ 2 * σ ^ 2 / δ ≤ E₀ := hE₀def ▸ le_max_right _ _
  -- it suffices to prove `E_*(ξ, θ₀σ, S) ≤ θ₀E₀`
  have hRHS := Submission.dorag_tesDecay_rhs (θ' / 32) E₀ (1 / σ ^ n) (κ ^ 2 * σ ^ 2 / δ) I _
    (by positivity) (by positivity) hE₀def hT'T
  have hθ32 : θ' / 32 ≤ 1 := by linarith only [hθ'4]
  have hsecond : ENNReal.ofReal (κ ^ 2 * (θ' / 32 * σ) ^ 2 / δ) ≤ ENNReal.ofReal (θ' / 32 * E₀) := by
    apply ENNReal.ofReal_le_ofReal
    rw [show κ ^ 2 * (θ' / 32 * σ) ^ 2 / δ = (θ' / 32) ^ 2 * (κ ^ 2 * σ ^ 2 / δ) by ring]
    calc (θ' / 32) ^ 2 * (κ ^ 2 * σ ^ 2 / δ) ≤ (θ' / 32) ^ 2 * E₀ := by gcongr
      _ ≤ θ' / 32 * E₀ := by
        gcongr
        rw [sq]
        exact mul_le_of_le_one_left (by positivity) hθ32
  rcases hE₀0.eq_or_lt with hE₀z | hE₀p
  · /- `E₀ = 0`: `S = T'` works. -/
    have hIz : I = 0 := by
      have := hIE
      rw [← hE₀z, mul_zero] at this
      exact le_antisymm this hI0
    refine ⟨T', hT'n, le_trans (max_le ?_ hsecond) hRHS⟩
    refine (mul_le_mul_right (lintegral_mono_set (closedBall_subset_closedBall
      (mul_le_of_le_one_left hσ.le hθ32))) _).trans ?_
    rw [← hIeq, hIz, ENNReal.ofReal_zero, mul_zero]
    exact zero_le
  /- `E₀ > 0`.  Step 2: Lipschitz approximation over `T'` with `L = 1`. -/
  obtain ⟨ι, ι', f, hιι', hιT, hfL, hfb, h5A, -⟩ := hLA δ hδ hδ₅' U W R H κ ρ z hW hWU hρ hzρ hH hHκ
    hMC hz hdens hκρ ξ hξ σ 1 T' hσ hσδρ hT'n one_pos le_rfl (by rw [← hDdef, mul_one]; exact hDβ)
    (by rw [← hDdef, ← hIeq]; exact ENNReal.ofReal_le_ofReal (hIa.trans (by gcongr)))
    (by rw [← hDdef]; exact hT'h)
  clear hLA
  rw [← hDdef] at hfb
  rw [one_pow, div_one, ← hIeq, ← ENNReal.ofReal_mul hC₇.le] at h5A
  /- Steps 3–9: the core estimate. -/
  obtain ⟨S, hSn, hS⟩ := Submission.dorag_tesDecay_core n k hn U W R H κ ξ σ T' ι ι' f C₃ C₇ C₁₁ C₁₃
    C₁₄ C₁₅ C₁₆ C₁₇ CT CH ω θ' ε' δh D δ E₀ I hW hWU hH hHκ hMC
    (fun ξ' r S' => hTH U W R H κ ξ' r S' hW hWU hH hHκ hMC) hHA' hσ hBW
    (fun y hy t ht htσ => (hDBa y (hBz hy) t ht (htσ.trans hσρ)).trans_eq (h2ω _ (by positivity)))
    (by filter_upwards [hDBd] with x hx hxB using hx (hBz hxB)) hT'n hT'h
    (by rw [hIeq]; exact lintegral_mono_set (closedBall_subset_closedBall (by linarith only [hσ])))
    hιι' hιT hfL hfb h5A hωeq hC₃ hC₇ hC₁₁0 hCT hCH hω hC₁₃def hC₁₄def hC₁₅def hC₁₇def hC₁₆def hθ'
    hθ'4 hθ'C hε' hε'1 hε'C hD hD1 hD7 hD11 hD14 hD15 hD16a hD16b hδ hδD hI0 hE₀p hIE hκE hE₀le hκσE
  exact ⟨S, hSn, le_trans (max_le hS hsecond) hRHS⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
