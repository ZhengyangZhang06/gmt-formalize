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

/-- **Integration by parts for a Lipschitz function against a `C²` test function on a ball**
(Step 0 of the harmonic approximation lemma: the integration by parts in Simon Ch. 5, Lemma 3.1,
made explicit for Lipschitz `u` via Rademacher's theorem).  Both integrands vanish off
`tsupport ζ ⊆ B_R`, so the ball integrals are integrals over `ℝⁿ`.  In each direction `v`,
`g = Dζ(·)v` is `C¹` with compact support, hence Lipschitz, and Mathlib's
`LipschitzWith.integral_lineDeriv_mul_eq` gives `∫ ∂ᵥu · g = ∫ ∂₋ᵥg · u`; by Rademacher's theorem
`∂ᵥu = Du(·)v` a.e., and `∂₋ᵥg = −D²ζ(·)(v, v)`.  Summing over `v = eᵢ` (every term is integrable)
gives the identity. -/
theorem Submission.dorag_haa_lipschitz_ibp : ∀ (n : ℕ) (R : ℝ) (u ζ : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ y (EuclideanSpace.single i (1 : ℝ)) = -∫ y in ball (0 : Euclid n) R, u y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n R u ζ L hu hζ hcs hsub
  -- both integrands vanish off `tsupport ζ ⊆ B_R`, since `Dζ` and `D²ζ` do
  have hD1 : ∀ y, y ∉ tsupport ζ → fderiv ℝ ζ y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hy (support_fderiv_subset ℝ h)
  have hD2 : ∀ y, y ∉ tsupport ζ → iteratedFDeriv ℝ 2 ζ y = 0 := fun y hy =>
    Function.notMem_support.mp fun h => hy (support_iteratedFDeriv_subset 2 h)
  have hout : ∀ y, y ∉ ball (0 : Euclid n) R → y ∉ tsupport ζ := fun y hy h => hy (hsub h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hD1 y (hout y hy)],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hD2 y (hout y hy)]]
  -- `Dζ` is `C¹`
  have hζ1 : ContDiff ℝ 1 (fderiv ℝ ζ) := hζ.fderiv_right one_add_one_eq_two.le
  -- integrability of the terms
  have hint1 : ∀ v : Euclid n, Integrable (fun y => fderiv ℝ u y v * fderiv ℝ ζ y v) := by
    intro v
    have hg : Integrable (fun y => fderiv ℝ ζ y v) :=
      (hζ1.continuous.clm_apply continuous_const).integrable_of_hasCompactSupport
        (hcs.fderiv_apply ℝ v)
    refine hg.bdd_mul (c := L * ‖v‖) (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖fderiv ℝ u y v‖ ≤ ‖fderiv ℝ u y‖ * ‖v‖ := (fderiv ℝ u y).le_opNorm v
      _ ≤ L * ‖v‖ := by gcongr; exact norm_fderiv_le_of_lipschitz ℝ hu
  have hint2 : ∀ v : Euclid n, Integrable (fun y => u y * iteratedFDeriv ℝ 2 ζ y ![v, v]) := by
    intro v
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hu.continuous.mul ((hζ.continuous_iteratedFDeriv le_rfl).eval_const _)
    · refine hcs.mono' (Function.support_subset_iff'.mpr fun y hy => ?_)
      simp [hD2 y hy]
  -- the identity in each direction `v`
  have key : ∀ v : Euclid n,
      ∫ y, fderiv ℝ u y v * fderiv ℝ ζ y v = -∫ y, u y * iteratedFDeriv ℝ 2 ζ y ![v, v] := by
    intro v
    have hg1 : ContDiff ℝ 1 (fun y => fderiv ℝ ζ y v) := hζ1.clm_apply contDiff_const
    have hgcs : HasCompactSupport (fun y => fderiv ℝ ζ y v) := hcs.fderiv_apply ℝ v
    obtain ⟨C, hgC⟩ := hg1.lipschitzWith_of_hasCompactSupport hgcs one_ne_zero
    have ibp := hu.integral_lineDeriv_mul_eq hgC hgcs v (μ := volume)
    have lhs : ∫ y, fderiv ℝ u y v * fderiv ℝ ζ y v = ∫ y, lineDeriv ℝ u y v * fderiv ℝ ζ y v := by
      refine integral_congr_ae ?_
      filter_upwards [hu.ae_differentiableAt (μ := volume)] with y hy
      rw [hy.lineDeriv_eq_fderiv]
    have rhs : ∀ y, lineDeriv ℝ (fun y => fderiv ℝ ζ y v) y (-v) * u y =
        -(u y * iteratedFDeriv ℝ 2 ζ y ![v, v]) := by
      intro y
      have hd2 : DifferentiableAt ℝ (fderiv ℝ ζ) y := hζ1.differentiable one_ne_zero y
      rw [(hg1.differentiable one_ne_zero y).lineDeriv_eq_fderiv,
        fderiv_clm_apply hd2 (differentiableAt_const v), iteratedFDeriv_two_apply]
      simp
      ring
    rw [lhs, ibp, ← integral_neg]
    congr 1
    funext y
    exact rhs y
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 _, integral_finsetSum _ fun i _ => hint2 _,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key _
namespace Submission

/-- Strong `L²(B_R)` convergence `fⱼ → W` gives `∫_{B_R} fⱼ g → ∫_{B_R} W g` for every
`g ∈ L²(B_R)`: by Cauchy–Schwarz (Hölder with `p = q = 2`),
`|∫ fⱼ g − ∫ W g| ≤ ∫ |fⱼ − W| |g| ≤ (∫ (fⱼ − W)²)^{1/2} (∫ g²)^{1/2} → 0`. -/
theorem dorag_haa_l2_pairing_tendsto : ∀ (n : ℕ) (R : ℝ) (f : ℕ → Euclid n → ℝ) (W g : Euclid n → ℝ), (∀ j, MemLp (f j) 2 (volume.restrict (ball (0 : Euclid n) R))) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → MemLp g 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) atTop (𝓝 0) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, f j x * g x) atTop (𝓝 (∫ x in ball (0 : Euclid n) R, W x * g x)) := by
  intro n R f W g hf hW hg hlim
  -- Cauchy–Schwarz: `|∫ fⱼ g − ∫ W g| ≤ √(∫ (fⱼ − W)²) · √(∫ g²)`.
  have hbound : ∀ j, ‖(∫ x in ball (0 : Euclid n) R, f j x * g x) -
      ∫ x in ball (0 : Euclid n) R, W x * g x‖ ≤
      √(∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) *
        √(∫ x in ball (0 : Euclid n) R, g x ^ 2) := by
    intro j
    have hd : MemLp (fun x => f j x - W x) (ENNReal.ofReal 2)
        (volume.restrict (ball (0 : Euclid n) R)) := by
      rw [ENNReal.ofReal_ofNat]; exact (hf j).sub hW
    have hg' : MemLp g (ENNReal.ofReal 2) (volume.restrict (ball (0 : Euclid n) R)) := by
      rw [ENNReal.ofReal_ofNat]; exact hg
    -- Products of two `L²` functions are integrable (Hölder `2, 2, 1`).
    have hi₁ : Integrable (fun x => f j x * g x) (volume.restrict (ball (0 : Euclid n) R)) :=
      (hf j).integrable_mul hg
    have hi₂ : Integrable (fun x => W x * g x) (volume.restrict (ball (0 : Euclid n) R)) :=
      hW.integrable_mul hg
    rw [← integral_sub hi₁ hi₂, Real.norm_eq_abs]
    calc |∫ x in ball (0 : Euclid n) R, (f j x * g x - W x * g x)|
        ≤ ∫ x in ball (0 : Euclid n) R, |f j x * g x - W x * g x| := abs_integral_le_integral_abs
      _ = ∫ x in ball (0 : Euclid n) R, ‖f j x - W x‖ * ‖g x‖ := by
          congr 1; funext x; rw [← sub_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (∫ x in ball (0 : Euclid n) R, ‖f j x - W x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
            (∫ x in ball (0 : Euclid n) R, ‖g x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
          integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hd hg'
      _ = _ := by simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs, ← Real.sqrt_eq_rpow]
  -- The bound tends to `√0 · √(∫ g²) = 0`; squeeze.
  have hsq : Tendsto (fun j => √(∫ x in ball (0 : Euclid n) R, (f j x - W x) ^ 2) *
      √(∫ x in ball (0 : Euclid n) R, g x ^ 2)) atTop (𝓝 0) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).comp hlim).mul_const
      (√(∫ x in ball (0 : Euclid n) R, g x ^ 2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun j => norm_nonneg _) hbound hsq

end Submission

/-- **`L²` limits of almost-harmonic Lipschitz functions are weakly harmonic** (step A3 of the
harmonic approximation, Simon Ch. 5, proof of Lemma 3.1, p. 114; chapter-05.txt lines 632–639,
replacing "by the weak convergence of `∇f_{k'}` to `∇w` and by (1)").  Write `B = B̆_R(0)`,
`eᵢ = EuclideanSpace.single i 1` and `Δζ = Σᵢ D²ζ(eᵢ, eᵢ)`.  For `vⱼ = uⱼ − cⱼ`, which is
Lipschitz with `Dvⱼ = Duⱼ`, `dorag_haa_lipschitz_ibp` gives `∫_B vⱼ Δζ = −∫_B Σᵢ Duⱼ eᵢ · Dζ eᵢ`,
so the hypothesis with `G = sup ‖Dζ‖` gives `|∫_B vⱼ Δζ| ≤ δⱼ G → 0`.  As `vⱼ → W` in `L²(B)`,
`dorag_haa_l2_pairing_tendsto` gives `∫_B vⱼ Δζ → ∫_B W Δζ`, which is therefore `0`. -/
theorem Submission.dorag_haa_weakly_harmonic_limit : ∀ (n : ℕ) (R : ℝ) (u : ℕ → Euclid n → ℝ) (c δ : ℕ → ℝ) (W : Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → Tendsto δ atTop (𝓝 0) → MemLp W 2 (volume.restrict (ball (0 : Euclid n) R)) → Tendsto (fun j => ∫ x in ball (0 : Euclid n) R, (u j x - c j - W x) ^ 2) atTop (𝓝 0) → (∀ (j : ℕ) (ζ : Euclid n → ℝ), ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ (u j) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ j * G) → ∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n R u c δ W hu hδ hW hconv hweak ζ hζ hζc hζB
  -- Step 1: `Δζ` is continuous, `ζ` being `C²`
  have hΔ : Continuous fun y => ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] :=
    continuous_finsetSum _ fun i _ =>
      (hζ.continuous_iteratedFDeriv (m := 2) le_rfl).eval_const _
  -- Step 2: continuous functions are bounded on `B ⊆ closedBall 0 R`, hence in `L²(B)`
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_ne_top
  have hL2 : ∀ f : Euclid n → ℝ, Continuous f →
      MemLp f 2 (volume.restrict (ball (0 : Euclid n) R)) := by
    intro f hf
    obtain ⟨K, hK⟩ :=
      (isCompact_closedBall (0 : Euclid n) R).exists_bound_of_continuousOn hf.continuousOn
    exact MemLp.of_bound hf.aestronglyMeasurable K
      (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hK x (ball_subset_closedBall hx))
  -- Step 3: `‖Dζ‖ ≤ G`, `Dζ` being continuous with compact support
  obtain ⟨G, hG⟩ := (hζc.fderiv ℝ).exists_bound_of_continuous (hζ.continuous_fderiv two_ne_zero)
  -- Step 4: integration by parts for `vⱼ = uⱼ − cⱼ` (`Dvⱼ = Duⱼ`) and the hypothesis give
  -- `|∫_B vⱼ Δζ| = |∫_B Σᵢ Duⱼ eᵢ · Dζ eᵢ| ≤ δⱼ G`
  have hbound : ∀ j, |∫ y in ball (0 : Euclid n) R, (u j y - c j) * ∑ i : Fin n,
      iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]|
      ≤ δ j * G := by
    intro j
    obtain ⟨L, hL⟩ := hu j
    have hibp := Submission.dorag_haa_lipschitz_ibp n R (fun y => u j y - c j) ζ (L + 0)
      (hL.sub (LipschitzWith.const (c j))) hζ hζc hζB
    simp only [fderiv_sub_const] at hibp
    have h := hweak j ζ (hζ.of_le one_le_two) hζc hζB G hG
    rwa [hibp, abs_neg] at h
  -- Step 5: hence `∫_B vⱼ Δζ → 0`, as `δⱼ G → 0`
  have h0 : Tendsto (fun j => ∫ y in ball (0 : Euclid n) R, (u j y - c j) * ∑ i : Fin n,
      iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)])
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun j => (Real.norm_eq_abs _).le.trans (hbound j)) ?_
    simpa using hδ.mul_const G
  -- Step 6: `vⱼ → W` in `L²(B)` and `Δζ ∈ L²(B)`, so `∫_B vⱼ Δζ → ∫_B W Δζ`
  have hlim := Submission.dorag_haa_l2_pairing_tendsto n R (fun j y => u j y - c j) W _
    (fun j => hL2 _ (by
      obtain ⟨L, hL⟩ := hu j
      exact hL.continuous.sub continuous_const))
    hW (hL2 _ hΔ) hconv
  -- Step 7: limits in `ℝ` are unique
  exact tendsto_nhds_unique hlim h0
/-- **Change of variables `x = r • y` between `B₁(0)` and `B_r(0)`** (step B1 of the harmonic
approximation lemma, with `r` for `R₀`).  For `r > 0` and an arbitrary `F : ℝⁿ → ℝ`,
`y ↦ F (r • y)` is integrable on `B₁(0)` iff `F` is integrable on `B_r(0)`, and
`∫_{B₁(0)} F (r • y) dy = r⁻ⁿ ∫_{B_r(0)} F`.  The identity is Mathlib's Haar-measure change of
variables with `r • B₁(0) = B_r(0)` and `finrank ℝ ℝⁿ = n`; it needs no integrability, a
non-integrable function having integral `0` on both sides.  Integrability passes to the indicators
of the two balls, which correspond under `y ↦ r • y`. -/
theorem Submission.dorag_haa_ball_rescale_integral : ∀ (n : ℕ) (F : Euclid n → ℝ) (r : ℝ), 0 < r → (IntegrableOn (fun y => F (r • y)) (ball (0 : Euclid n) 1) ↔ IntegrableOn F (ball (0 : Euclid n) r)) ∧ ∫ y in ball (0 : Euclid n) 1, F (r • y) = (r ^ n)⁻¹ * ∫ x in ball (0 : Euclid n) r, F x := by
  intro n F r hr
  -- `r • y ∈ B_r ↔ y ∈ B_1`, since `‖r • y‖ = r ‖y‖`
  have hmem : ∀ y : Euclid n, r • y ∈ ball (0 : Euclid n) r ↔ y ∈ ball (0 : Euclid n) 1 := by
    intro y
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_iff_lt_one_right hr
  refine ⟨?_, ?_⟩
  · -- integrability: pass to indicators and use `integrable_comp_smul_iff`
    have hind : (ball (0 : Euclid n) 1).indicator (fun y => F (r • y)) =
        fun y => (ball (0 : Euclid n) r).indicator F (r • y) := by
      ext y
      by_cases hy : y ∈ ball (0 : Euclid n) 1
      · rw [indicator_of_mem hy, indicator_of_mem ((hmem y).2 hy)]
      · rw [indicator_of_notMem hy, indicator_of_notMem (mt (hmem y).1 hy)]
    rw [← integrable_indicator_iff measurableSet_ball, ← integrable_indicator_iff measurableSet_ball,
      hind]
    exact integrable_comp_smul_iff volume _ hr.ne'
  · -- the change of variables `x = r • y`, with `r • B_1 = B_r`
    rw [Measure.setIntegral_comp_smul_of_pos volume F (ball 0 1) hr, smul_unitBall_of_pos hr,
      finrank_euclideanSpace_fin, smul_eq_mul]

/-- Rescaling to the unit ball in the harmonic approximation lemma (Simon Ch. 5, Lemma 3.1, steps
B1–B2 of the scaling): if `w` is `Lw`-Lipschitz, `∫_{B_{R₀}} ‖Dw‖² ≤ R₀ⁿ` and
`|∫_{B_{R₀}} Dw · Dζ| ≤ δ R₀ⁿ G` for `ζ ∈ C¹_c(B_{R₀})` with `‖Dζ‖ ≤ G`, then
`w₁(y) = R₀⁻¹ w(R₀ y)` is `Lw`-Lipschitz, `∫_{B_1} ‖Dw₁‖² ≤ 1` and `|∫_{B_1} Dw₁ · Dζ₁| ≤ δ G` for
`ζ₁ ∈ C¹_c(B_1)` with `‖Dζ₁‖ ≤ G`.  `D(y ↦ c⁻¹ f(c y))(x) = Df(c x)` for `c ≠ 0`, with no
differentiability hypothesis; `ζ₁` is tested through `ζ(x) = R₀ ζ₁(R₀⁻¹ x)`, for which
`Dζ(x) = Dζ₁(R₀⁻¹ x)`, and `dorag_haa_ball_rescale_integral` turns each integral over `B_1` into
`R₀⁻ⁿ` times the integral over `B_{R₀}`. -/
theorem Submission.dorag_haa_rescale_hypotheses : ∀ (n : ℕ) (δ R₀ : ℝ) (w : Euclid n → ℝ) (Lw : NNReal), 0 < R₀ → LipschitzWith Lw w → ∫ v in ball (0 : Euclid n) R₀, ‖fderiv ℝ w v‖ ^ 2 ≤ R₀ ^ n → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R₀ → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) R₀, ∑ i : Fin n, fderiv ℝ w v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * R₀ ^ n * G) → LipschitzWith Lw (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) ∧ ∫ v in ball (0 : Euclid n) 1, ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2 ≤ 1 ∧ ∀ ζ : Euclid n → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) 1 → ∀ G : ℝ, (∀ v, ‖fderiv ℝ ζ v‖ ≤ G) → |∫ v in ball (0 : Euclid n) 1, ∑ i : Fin n, fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ ζ v (EuclideanSpace.single i (1 : ℝ))| ≤ δ * G := by
  intro n δ R₀ w Lw hR₀ hw hE hW
  have hR₀ne : R₀ ≠ 0 := hR₀.ne'
  have hRn : 0 < R₀ ^ n := pow_pos hR₀ n
  -- Step 0: `D(y ↦ c⁻¹ f(c y))(x) = Df(c x)` for `c ≠ 0`, with no differentiability hypothesis
  have hscale : ∀ (f : Euclid n → ℝ) (c : ℝ), c ≠ 0 → ∀ x : Euclid n,
      fderiv ℝ (fun y : Euclid n => c⁻¹ * f (c • y)) x = fderiv ℝ f (c • x) := by
    intro f c hc x
    have h1 : (fun y : Euclid n => c⁻¹ * f (c • y)) = c⁻¹ • fun y : Euclid n => f (c • y) := by
      funext y
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, inv_smul_smul₀ hc]
  -- Step 1 (a): `w₁` is `Lw`-Lipschitz
  have ha : LipschitzWith Lw (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h := hw.dist_le_mul (R₀ • x) (R₀ • y)
    rw [dist_smul₀, Real.norm_of_nonneg hR₀.le] at h
    calc dist (R₀⁻¹ * w (R₀ • x)) (R₀⁻¹ * w (R₀ • y))
        = R₀⁻¹ * dist (w (R₀ • x)) (w (R₀ • y)) := by
          rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hR₀)]
      _ ≤ R₀⁻¹ * (Lw * (R₀ * dist x y)) := by gcongr
      _ = Lw * dist x y := by field_simp
  -- Step 2 (b): `∫_{B_1} ‖Dw₁‖² = R₀⁻ⁿ ∫_{B_{R₀}} ‖Dw‖² ≤ 1`
  have hb : ∫ v in ball (0 : Euclid n) 1,
      ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2 ≤ 1 := by
    have e : (fun v => ‖fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v‖ ^ 2) =
        fun v => ‖fderiv ℝ w (R₀ • v)‖ ^ 2 := funext fun v => by rw [hscale w R₀ hR₀ne v]
    rw [e, (Submission.dorag_haa_ball_rescale_integral n (fun x => ‖fderiv ℝ w x‖ ^ 2) R₀ hR₀).2,
      inv_mul_le_iff₀ hRn, mul_one]
    exact hE
  refine ⟨ha, hb, ?_⟩
  -- Step 3 (c): test with `ζ(x) = R₀ ζ₁(R₀⁻¹ x)` on `B_{R₀}`
  intro ζ₁ hζ₁ hcs₁ hts₁ G hG
  set ζ : Euclid n → ℝ := fun x => R₀ * ζ₁ (R₀⁻¹ • x)
  -- 3a: `ζ` is `C¹`
  have hζC : ContDiff ℝ 1 ζ := contDiff_const.mul (hζ₁.comp (contDiff_const_smul R₀⁻¹))
  -- 3b: `ζ` has compact support
  have hζcs : HasCompactSupport ζ := (hcs₁.comp_smul (inv_ne_zero hR₀ne)).mul_left
  -- 3c: `tsupport ζ ⊆ B_{R₀}`
  have hζts : tsupport ζ ⊆ ball (0 : Euclid n) R₀ := by
    intro x hx
    have hx1 : x ∈ tsupport fun x : Euclid n => ζ₁ (R₀⁻¹ • x) := tsupport_mul_subset_right hx
    have hx2 : R₀⁻¹ • x ∈ tsupport ζ₁ :=
      tsupport_comp_subset_preimage ζ₁ (continuous_const_smul R₀⁻¹) hx1
    have hx3 := hts₁ hx2
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR₀.le),
      inv_mul_lt_iff₀ hR₀, mul_one] at hx3
    exact mem_ball_zero_iff.2 hx3
  -- 3d: `Dζ(x) = Dζ₁(R₀⁻¹ x)`, so `‖Dζ‖ ≤ G`
  have hDζ : ∀ x, fderiv ℝ ζ x = fderiv ℝ ζ₁ (R₀⁻¹ • x) := by
    intro x
    have h := hscale ζ₁ R₀⁻¹ (inv_ne_zero hR₀ne) x
    rwa [inv_inv] at h
  have hGζ : ∀ v, ‖fderiv ℝ ζ v‖ ≤ G := fun v => by rw [hDζ]; exact hG _
  -- 3e: the hypothesis applies to `(ζ, G)`
  have hbound := hW ζ hζC hζcs hζts G hGζ
  -- 3f: `F(R₀ v) = Σᵢ Dw₁(v)eᵢ · Dζ₁(v)eᵢ` for `F = Σᵢ Dw eᵢ · Dζ eᵢ`; rescale `∫_{B_1}`
  have hF : (fun v : Euclid n => ∑ i : Fin n,
      fderiv ℝ (fun y : Euclid n => R₀⁻¹ * w (R₀ • y)) v (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ₁ v (EuclideanSpace.single i (1 : ℝ))) =
      fun v => ∑ i : Fin n, fderiv ℝ w (R₀ • v) (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ (R₀ • v) (EuclideanSpace.single i (1 : ℝ)) := by
    funext v
    simp only [hscale w R₀ hR₀ne v, hDζ, inv_smul_smul₀ hR₀ne]
  rw [hF, (Submission.dorag_haa_ball_rescale_integral n (fun x => ∑ i : Fin n,
      fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))) R₀ hR₀).2,
    abs_mul, abs_of_pos (inv_pos.2 hRn)]
  -- 3g: `R₀⁻ⁿ |∫_{B_{R₀}} F| ≤ R₀⁻ⁿ δ R₀ⁿ G = δ G`
  calc (R₀ ^ n)⁻¹ * |∫ x in ball (0 : Euclid n) R₀, ∑ i : Fin n,
        fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ ζ x (EuclideanSpace.single i (1 : ℝ))|
      ≤ (R₀ ^ n)⁻¹ * (δ * R₀ ^ n * G) := by gcongr
    _ = δ * G := by field_simp
/-- **Rescaling a unit-scale harmonic approximant to scale `R₀`** (step B3 of the harmonic
approximation lemma).  Let `h₁` be smooth and harmonic on `B₁(0)`, with `∫_{B₁} |Dh₁|² ≤ 1` and
`∫_{B₁} (h₁ − w₁)² ≤ ε` for `w₁(y) = R₀⁻¹ w(R₀ y)`.  Then `h(x) = R₀ h₁(R₀⁻¹ x)` is smooth and
harmonic on `B_{R₀}(0)`, with `∫_{B_{R₀}} |Dh|² ≤ R₀ⁿ` and `∫_{B_{R₀}} (h − w)² ≤ ε R₀ⁿ⁺²`.
Since `x ↦ R₀⁻¹ x` is a linear isomorphism mapping `B_{R₀}(0)` into `B₁(0)`, the identities
`Dh(x) = Dh₁(R₀⁻¹ x)` and `D²h(y) = R₀⁻¹ D²h₁(R₀⁻¹ y)` hold at every point.  Both integrals
transform by the change of variables `x = R₀ y`, under which `|Dh|²(R₀ y) = |Dh₁|²(y)` and
`(h − w)²(R₀ y) = R₀² (h₁ − w₁)²(y)`. -/
theorem Submission.dorag_haa_rescale_conclusion : ∀ (n : ℕ) (ε R₀ : ℝ) (w h₁ : Euclid n → ℝ), 0 < R₀ → (∀ m : ℕ, ContDiffOn ℝ m h₁ (ball (0 : Euclid n) 1)) → (∀ y ∈ ball (0 : Euclid n) 1, ∑ i : Fin n, iteratedFDeriv ℝ 2 h₁ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun y => ‖fderiv ℝ h₁ y‖ ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, ‖fderiv ℝ h₁ y‖ ^ 2 ≤ 1 → IntegrableOn (fun y => (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2) (ball (0 : Euclid n) 1) → ∫ y in ball (0 : Euclid n) 1, (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2 ≤ ε → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R₀)) ∧ (∀ y ∈ ball (0 : Euclid n) R₀, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2 ≤ R₀ ^ n ∧ IntegrableOn (fun y => (h y - w y) ^ 2) (ball (0 : Euclid n) R₀) ∧ ∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2 ≤ ε * R₀ ^ (n + 2) := by
  intro n ε R₀ w h₁ hR₀ hsmooth hlap hint₁ hle₁ hint₂ hle₂
  have hR₀ne : R₀ ≠ 0 := hR₀.ne'
  have hR₀n : 0 < R₀ ^ n := pow_pos hR₀ n
  -- the rescaled function `h(x) = R₀ h₁(R₀⁻¹ x)`
  obtain ⟨h, hh⟩ : ∃ h : Euclid n → ℝ, ∀ x, h x = R₀ * h₁ (R₀⁻¹ • x) := ⟨_, fun _ => rfl⟩
  -- step 0: `x ↦ R₀⁻¹ x` maps `B_{R₀}(0)` into `B₁(0)`
  have hmaps : MapsTo (fun x : Euclid n => R₀⁻¹ • x) (ball (0 : Euclid n) R₀)
      (ball (0 : Euclid n) 1) := by
    intro x hx
    rw [mem_ball_zero_iff] at hx
    show R₀⁻¹ • x ∈ ball (0 : Euclid n) 1
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR₀.le),
      inv_mul_lt_iff₀ hR₀, mul_one]
    exact hx
  -- step 2: `Dh(x) = R₀ R₀⁻¹ Dh₁(R₀⁻¹ x) = Dh₁(R₀⁻¹ x)` at every `x`
  have hDh : fderiv ℝ h = fun x => fderiv ℝ h₁ (R₀⁻¹ • x) := by
    have hfun : h = R₀ • fun x => h₁ (R₀⁻¹ • x) := funext hh
    funext x
    rw [hfun, fderiv_const_smul_field, Pi.smul_apply, fderiv_comp_smul, smul_smul,
      mul_inv_cancel₀ hR₀ne, one_smul]
  -- step 3: `D²h(y)(a, b) = R₀⁻¹ D²h₁(R₀⁻¹ y)(a, b)` at every `y`
  have hD2h : ∀ y a b : Euclid n, iteratedFDeriv ℝ 2 h y ![a, b] =
      R₀⁻¹ * iteratedFDeriv ℝ 2 h₁ (R₀⁻¹ • y) ![a, b] := by
    intro y a b
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hDh, fderiv_comp_smul]
    rfl
  -- steps 4–5: the change of variables `x = R₀ y`, with `|Dh|²(R₀ y) = |Dh₁|²(y)` and
  -- `(h − w)²(R₀ y) = R₀² (h₁ − w₁)²(y)`
  have hF₁ : ∀ y : Euclid n, ‖fderiv ℝ h (R₀ • y)‖ ^ 2 = ‖fderiv ℝ h₁ y‖ ^ 2 := by
    intro y
    simp only [hDh, inv_smul_smul₀ hR₀ne]
  have hF₂ : ∀ y : Euclid n,
      (h (R₀ • y) - w (R₀ • y)) ^ 2 = R₀ ^ 2 * (h₁ y - R₀⁻¹ * w (R₀ • y)) ^ 2 := by
    intro y
    rw [hh, inv_smul_smul₀ hR₀ne, ← mul_pow, mul_sub, mul_inv_cancel_left₀ hR₀ne]
  obtain ⟨hiff₁, heq₁⟩ :=
    Submission.dorag_haa_ball_rescale_integral n (fun x => ‖fderiv ℝ h x‖ ^ 2) R₀ hR₀
  obtain ⟨hiff₂, heq₂⟩ :=
    Submission.dorag_haa_ball_rescale_integral n (fun x => (h x - w x) ^ 2) R₀ hR₀
  simp only [hF₁] at hiff₁ heq₁
  simp only [hF₂, integral_const_mul] at hiff₂ heq₂
  refine ⟨h, fun m => ?_, fun y hy => ?_, hiff₁.1 hint₁, ?_, hiff₂.1 (hint₂.const_mul _), ?_⟩
  · -- step 1: `h = R₀ · (h₁ ∘ R₀⁻¹ ·)` is `Cᵐ` on `B_{R₀}(0)`
    exact (contDiffOn_const.mul ((hsmooth m).comp (contDiff_const_smul R₀⁻¹).contDiffOn
      hmaps)).congr fun x _ => hh x
  · -- step 3: `Δh(y) = R₀⁻¹ Δh₁(R₀⁻¹ y) = 0`, as `R₀⁻¹ y ∈ B₁(0)`
    simp_rw [hD2h]
    rw [← Finset.mul_sum, hlap (R₀⁻¹ • y) (hmaps hy), mul_zero]
  · -- step 4: `∫_{B_{R₀}} |Dh|² = R₀ⁿ ∫_{B₁} |Dh₁|² ≤ R₀ⁿ`
    rw [← mul_inv_cancel_left₀ hR₀n.ne' (∫ y in ball (0 : Euclid n) R₀, ‖fderiv ℝ h y‖ ^ 2),
      ← heq₁]
    exact (mul_le_mul_of_nonneg_left hle₁ hR₀n.le).trans_eq (mul_one _)
  · -- step 5: `∫_{B_{R₀}} (h − w)² = R₀ⁿ R₀² ∫_{B₁} (h₁ − w₁)² ≤ ε R₀ⁿ⁺²`
    rw [← mul_inv_cancel_left₀ hR₀n.ne' (∫ y in ball (0 : Euclid n) R₀, (h y - w y) ^ 2),
      ← heq₂, pow_add, mul_comm ε, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hle₂ (mul_pos hR₀n (pow_pos hR₀ 2)).le
/-- **FTC along a segment for a Lipschitz function** (step 1 of the Poincaré inequality on the unit
ball invoked in the proof of Simon Ch. 5, Lemma 3.1; Gilbarg–Trudinger, Lemma 7.16).  The
restriction `φ(t) = u((1 − t)y + tx)` is Lipschitz, so `∫₀¹ φ' = φ(1) − φ(0) = u(x) − u(y)`: the
difference quotients `∫₀¹ (φ(s + t) − φ(s))/t ds` tend, as `t → 0⁺`, to `φ(1) − φ(0)` by continuity
of `φ` and to `∫₀¹ φ'` by dominated convergence.  Wherever `u` is differentiable at `(1 − t)y + tx`
the chain rule gives `φ'(t) = Du((1 − t)y + tx)(x − y)`, and this holds for a.e. `t ∈ (0, 1]`. -/
theorem Submission.dorag_ha_pb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (x y : Euclid n), LipschitzWith L u → (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), DifferentiableAt ℝ u ((1 - t) • y + t • x)) → u x - u y = ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • y + t • x) (x - y) := by
  intro n u L x y hu hdiff
  -- Step 1: `γ(t) = (1 − t)y + tx` is `‖x − y‖`-Lipschitz, so `φ = u ∘ γ` is Lipschitz
  have hγ : LipschitzWith ‖x - y‖₊ (fun t : ℝ => (1 - t) • y + t • x) := by
    refine LipschitzWith.of_dist_le_mul fun s t => le_of_eq ?_
    have h : (1 - s) • y + s • x - ((1 - t) • y + t • x) = (s - t) • (x - y) := by module
    rw [dist_eq_norm, h, norm_smul, Real.norm_eq_abs, ← Real.dist_eq, coe_nnnorm, mul_comm]
  -- Step 2: `∫₀¹ φ' = φ(1) − φ(0)` for every Lipschitz `φ : ℝ → ℝ`, with `φ' = lineDeriv ℝ φ · 1`
  have ftc : ∀ (φ : ℝ → ℝ) (K : NNReal), LipschitzWith K φ →
      ∫ s in (0 : ℝ)..1, lineDeriv ℝ φ s 1 = φ 1 - φ 0 := by
    intro φ K hφ
    have hφc : Continuous φ := hφ.continuous
    have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b :=
      fun a b => hφc.intervalIntegrable a b
    -- with `Φ(c) = ∫₀ᶜ φ`, `∫₀¹ (φ(s + t) − φ(s))/t ds = (Φ(1 + t) − Φ(1))/t − (Φ(t) − Φ(0))/t`,
    -- which tends to `φ(1) − φ(0)` as `t → 0⁺` since `Φ' = φ`
    have hlim : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..1, t⁻¹ • (φ (s + t • 1) - φ s)) (𝓝[>] 0)
        (𝓝 (φ 1 - φ 0)) := by
      have hΦ : ∀ b, HasDerivAt (fun c => ∫ s in (0 : ℝ)..c, φ s) (φ b) b :=
        fun b => (hφc.integral_hasStrictDerivAt 0 b).hasDerivAt
      refine ((hΦ 1).tendsto_slope_zero_right.sub (hΦ 0).tendsto_slope_zero_right).congr
        fun t => ?_
      have hshift : ∫ s in (0 : ℝ)..1, φ (s + t) =
          (∫ s in (0 : ℝ)..1 + t, φ s) - ∫ s in (0 : ℝ)..0 + t, φ s := by
        rw [intervalIntegral.integral_comp_add_right,
          intervalIntegral.integral_interval_sub_left (hint _ _) (hint _ _)]
      simp only [smul_eq_mul, mul_one]
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          ((by fun_prop : Continuous fun s => φ (s + t)).intervalIntegrable 0 1) (hint 0 1),
        hshift, intervalIntegral.integral_same]
      ring
    -- by dominated convergence (Rademacher, against the weight `1_{(0, 1]}`) the same quotients
    -- tend to `∫₀¹ φ'`
    have hg : Integrable ((Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℝ)) volume := by
      rw [integrable_indicator_iff measurableSet_Ioc]
      exact integrableOn_const measure_Ioc_lt_top.ne
    have hind : ∀ h : ℝ → ℝ, ∫ s, h s * (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) s =
        ∫ s in (0 : ℝ)..1, h s := by
      intro h
      rw [intervalIntegral.integral_of_le zero_le_one, ← integral_indicator measurableSet_Ioc]
      congr 1
      ext s
      by_cases hs : s ∈ Ioc (0 : ℝ) 1 <;> simp [hs]
    have hdom := hφ.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hg (1 : ℝ)
    simp only [hind] at hdom
    exact tendsto_nhds_unique hdom hlim
  -- `φ(1) = u(x)` and `φ(0) = u(y)`
  have key := ftc _ _ (hu.comp hγ)
  simp only [Function.comp_apply, sub_self, zero_smul, one_smul, zero_add, sub_zero,
    add_zero] at key
  rw [← key]
  -- Step 3: `γ' = x − y`, so `φ'(t) = Du(γ(t))(x − y)` wherever `u` is differentiable at `γ(t)`
  have hγ' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t) • y + t • x) (x - y) t := by
    intro t
    have h := (((hasDerivAt_id' t).const_sub 1).smul_const y).add ((hasDerivAt_id' t).smul_const x)
    convert h using 1
    rw [neg_one_smul, one_smul, neg_add_eq_sub]
  -- Step 4: that is the case for a.e. `t ∈ Ι 0 1 = (0, 1] ⊆ [0, 1]`
  apply intervalIntegral.integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Icc] at hdiff
  filter_upwards [hdiff] with t ht hmem
  rw [uIoc_of_le zero_le_one] at hmem
  have hd := (ht (Ioc_subset_Icc_self hmem)).hasFDerivAt.comp_hasDerivAt t (hγ' t)
  exact (hd.hasFDerivAt.hasLineDerivAt 1).lineDeriv.trans (by simp)
/-- Almost every segment meets a Lebesgue-null set `N ⊆ ℝⁿ` in a null set of parameters: for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, `(1 - t) y + t x ∉ N` for `L¹`-a.e. `t ∈ [0, 1]`.  Every `t`-slice
`{(x, y) : (1 - t) y + t x ∈ N}` is `Lⁿ ⊗ Lⁿ`-null: it is `ℝⁿ × N` for `t = 0`, and for `t ≠ 0`
each `x`-section is the preimage of a translate of `N` under `x ↦ t x`.  By Tonelli the set
`{((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ L¹⌞[0, 1]`, so almost all of its
sections in `t` are null. -/
theorem Submission.dorag_ha_pb_segment_null : ∀ (n : ℕ) (N : Set (Euclid n)), MeasurableSet N → volume N = 0 → ∀ᵐ p : Euclid n × Euclid n, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), (1 - t) • p.2 + t • p.1 ∉ N := by
  intro n N hNm hN0
  -- every `t`-slice `{(x, y) : (1 - t) y + t x ∈ N}` is null for `volume = Lⁿ ⊗ Lⁿ`
  have hslice : ∀ t : ℝ, (volume : Measure (Euclid n × Euclid n))
      {p | (1 - t) • p.2 + t • p.1 ∈ N} = 0 := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · -- `t = 0`: the slice is `ℝⁿ × N`, of measure `Lⁿ(ℝⁿ) · 0 = 0`
      have h0 : {p : Euclid n × Euclid n | (1 - 0 : ℝ) • p.2 + (0 : ℝ) • p.1 ∈ N} = univ ×ˢ N := by
        ext p
        simp
      rw [h0, Measure.volume_eq_prod, Measure.prod_prod, hN0, mul_zero]
    · -- `t ≠ 0`: for each `y`, the `x`-section is the preimage of a translate of `N` under `x ↦ t x`
      have hm : MeasurableSet {p : Euclid n × Euclid n | (1 - t) • p.2 + t • p.1 ∈ N} :=
        hNm.preimage (by fun_prop)
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hm]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      change (volume : Measure (Euclid n)) ((t • ·) ⁻¹' ((fun z => (1 - t) • y + z) ⁻¹' N)) = 0
      rw [Measure.addHaar_preimage_smul volume ht, measure_preimage_add, hN0, mul_zero]
  -- Tonelli: `E = {((x, y), t) : (1 - t) y + t x ∈ N}` is null for `(Lⁿ ⊗ Lⁿ) ⊗ ν`
  have hEm : MeasurableSet {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} :=
    hNm.preimage (by fun_prop)
  have hE : ((volume : Measure (Euclid n × Euclid n)).prod (volume.restrict (Icc (0 : ℝ) 1)))
      {q : (Euclid n × Euclid n) × ℝ | (1 - q.2) • q.1.2 + q.2 • q.1.1 ∈ N} = 0 := by
    rw [Measure.prod_apply_symm hEm]
    exact (lintegral_congr fun t => hslice t).trans lintegral_zero
  -- sections in `t`: for a.e. `(x, y)`, `ν`-a.e. `t` has `(1 - t) y + t x ∉ N`
  refine Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume.restrict (Icc (0 : ℝ) 1))
    (p := fun q : (Euclid n × Euclid n) × ℝ => (1 - q.2) • q.1.2 + q.2 • q.1.1 ∉ N) ?_
  rw [ae_iff]
  simpa using hE
/-- Cauchy–Schwarz for the integral over a finite measure space, `(∫ h dμ)² ≤ μ(α) ∫ h² dμ` for
`h ∈ L²(μ)`: used twice in the Poincaré inequality on a ball that Simon's proof of Ch. 5,
Lemma 3.1 cites ("by the Poincaré inequality (see e.g. [GT01])").  `h ∈ L¹` (`L² ⊆ L¹` on a finite
measure space) and `h² = ‖h‖² ∈ L¹`.  If `m = μ(α) = 0` then `μ = 0` and both sides vanish;
otherwise, with `c = ∫ h dμ`, `0 ≤ ∫ (h − c/m)² dμ = ∫ h² dμ − c²/m`, and multiplying by `m > 0`
gives the claim. -/
theorem Submission.dorag_ha_pb_sq_integral_le : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ), μ univ ≠ ∞ → MemLp h 2 μ → (∫ x, h x ∂μ) ^ 2 ≤ (μ univ).toReal * ∫ x, h x ^ 2 ∂μ := by
  intro α _ μ h hμ hh
  -- Step 1: `μ` is finite; `h ∈ L¹` (`L² ⊆ L¹` on a finite measure space) and `h² = ‖h‖² ∈ L¹`
  have : IsFiniteMeasure μ := ⟨lt_top_iff_ne_top.2 hμ⟩
  have hint : Integrable h μ := hh.integrable one_le_two
  have hint2 : Integrable (fun x => h x ^ 2) μ := by
    simpa [Real.norm_eq_abs, sq_abs] using hh.integrable_norm_pow (p := 2) two_ne_zero
  rcases (ENNReal.toReal_nonneg (a := μ univ)).eq_or_lt with hm0 | hmpos
  · -- Step 2: `μ(α) = 0`, so `μ = 0` and both sides vanish
    have hμ0 : μ = 0 := Measure.measure_univ_eq_zero.1 <|
      ((ENNReal.toReal_eq_zero_iff _).1 hm0.symm).resolve_right hμ
    simp [hμ0]
  · -- Step 3: `m = μ(α) > 0`, `c = ∫ h dμ`; `0 ≤ ∫ (h - c/m)² dμ = ∫ h² dμ - c²/m`
    set m := (μ univ).toReal with hm
    set c := ∫ x, h x ∂μ with hc
    have hint1 : Integrable (fun x => h x ^ 2 - 2 * (c / m) * h x) μ :=
      hint2.sub (hint.const_mul _)
    have hexp : ∫ x, (h x - c / m) ^ 2 ∂μ = ∫ x, h x ^ 2 ∂μ - c ^ 2 / m := by
      have e : ∀ x, (h x - c / m) ^ 2 = h x ^ 2 - 2 * (c / m) * h x + (c / m) ^ 2 :=
        fun x => by ring
      simp_rw [e]
      rw [integral_add hint1 (integrable_const _), integral_sub hint2 (hint.const_mul _),
        integral_const_mul, integral_const, smul_eq_mul, ← hc, measureReal_def, ← hm]
      field_simp
      ring
    have hnn : 0 ≤ ∫ x, (h x - c / m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    -- Step 4: `c²/m ≤ ∫ h² dμ`; multiply by `m > 0`
    rw [hexp, sub_nonneg, div_le_iff₀ hmpos] at hnn
    linarith

/-- **Segment bound for a Lipschitz function at almost every pair** (steps 0, 2 and 3 of the
Poincaré inequality on the ball, written out for all pairs `(x, y)`).  By Rademacher the set `N`
where `u` is not differentiable is Borel and `Lⁿ`-null, so `segment_null` gives, for
`Lⁿ ⊗ Lⁿ`-a.e. `(x, y)`, differentiability of `u` at `γ(t) = (1 − t)y + tx` for a.e.
`t ∈ [0, 1]`.  For such a pair `segment_ftc` gives `u(x) − u(y) = ∫₀¹ Du(γ(t))(x − y) dt`, hence
`|u(x) − u(y)| ≤ ∫₀¹ g` with `g(t) = ‖Du(γ(t))‖‖x − y‖ ≤ L‖x − y‖`, and `sq_integral_le` for
`L¹⌞(0, 1]` (total mass `1`) gives `(∫₀¹ g)² ≤ ∫₀¹ g² = ‖x − y‖² ∫₀¹ ‖Du(γ(t))‖² dt`. -/
theorem Submission.dorag_ha_pb_pair_sq_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ p : Euclid n × Euclid n, (u p.1 - u p.2) ^ 2 ≤ ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
  intro n u L hu
  -- Step 1: the non-differentiability set of `u` is Borel and `Lⁿ`-null (Rademacher).
  have hNmeas : MeasurableSet {z : Euclid n | ¬DifferentiableAt ℝ u z} :=
    (measurableSet_of_differentiableAt ℝ u).compl
  have hNnull : volume {z : Euclid n | ¬DifferentiableAt ℝ u z} = 0 :=
    ae_iff.mp hu.ae_differentiableAt
  -- Step 2: for a.e. pair, `u` is differentiable at a.e. point of the segment.
  filter_upwards [Submission.dorag_ha_pb_segment_null n _ hNmeas hNnull] with p hp
  have hdiff : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      DifferentiableAt ℝ u ((1 - t) • p.2 + t • p.1) := by
    filter_upwards [hp] with t ht
    simpa only [mem_ofPred_eq, not_not] using ht
  -- Step 3: the fundamental theorem of calculus along the segment.
  have hftc : u p.1 - u p.2 =
      ∫ t in (0 : ℝ)..1, fderiv ℝ u ((1 - t) • p.2 + t • p.1) (p.1 - p.2) :=
    Submission.dorag_ha_pb_segment_ftc n u L p.1 p.2 hu hdiff
  -- Step 4: `|u x - u y| ≤ ∫₀¹ g` with `g t = ‖Du(γ t)‖ ‖x - y‖`, a bounded measurable function.
  have hDmeas : Measurable fun t : ℝ => fderiv ℝ u ((1 - t) • p.2 + t • p.1) :=
    (measurable_fderiv ℝ u).comp
      (by fun_prop : Continuous fun t : ℝ => (1 - t) • p.2 + t • p.1).measurable
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ,
      g = fun t => ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ * ‖p.1 - p.2‖ := ⟨_, rfl⟩
  have hgmeas : Measurable g := by
    rw [hg]
    exact hDmeas.norm.mul_const _
  have hgbound : ∀ t, ‖g t‖ ≤ L * ‖p.1 - p.2‖ := by
    intro t
    simp only [hg, norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _)
  have hgint : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_const (c := (L : ℝ) * ‖p.1 - p.2‖)).mono_fun'
      hgmeas.aestronglyMeasurable (ae_of_all _ hgbound)
  have hfirst : |u p.1 - u p.2| ≤ ∫ t in (0 : ℝ)..1, g t := by
    rw [hftc, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (ae_of_all _ fun t _ => ?_) hgint
    simp only [hg]
    exact (fderiv ℝ u ((1 - t) • p.2 + t • p.1)).le_opNorm (p.1 - p.2)
  -- Step 5: Cauchy–Schwarz (`sq_integral_le`) on `(0, 1]`, which has total mass `1`.
  have hμ : volume.restrict (Ioc (0 : ℝ) 1) univ = 1 := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp
  have hmem : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound hgmeas.aestronglyMeasurable _ (ae_of_all _ hgbound)
  have hcs : (∫ t in (0 : ℝ)..1, g t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := by
    have h := Submission.dorag_ha_pb_sq_integral_le (volume.restrict (Ioc (0 : ℝ) 1)) g
      (by rw [hμ]; exact ENNReal.one_ne_top) hmem
    rw [hμ, ENNReal.toReal_one, one_mul] at h
    rwa [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  -- Step 6: combine, and pull the constant `‖x - y‖²` out of the integral.
  calc (u p.1 - u p.2) ^ 2 = |u p.1 - u p.2| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ t in (0 : ℝ)..1, g t) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hfirst 2
    _ ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 := hcs
    _ = ‖p.1 - p.2‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • p.2 + t • p.1)‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext t
      simp only [hg]
      ring
/-- **Slice bound on the unit ball.**  For measurable `g ≥ 0` and `t ∈ [0, 1]`,
`∫_B ∫_B g((1 − t)y + tx) dy dx ≤ 2ⁿ Lⁿ(B) ∫_B g`, `B = B₁(0) ⊂ ℝⁿ`.  If `s ≥ 1/2` and
`c + sB ⊆ B`, the Haar scaling `v ↦ sv` and translation invariance give
`∫_B g(c + sv) dv ≤ ∫ (1_B g)(c + sv) dv = s⁻ⁿ ∫_B g ≤ 2ⁿ ∫_B g`.  By convexity of `B`, this applies
in `y` (`c = tx`, `s = 1 − t`) when `t ≤ 1/2`, and in `x` after Tonelli (`c = (1 − t)y`, `s = t`)
when `t ≥ 1/2`; integrating the constant bound over `B` gives the claim. -/
theorem Submission.dorag_ha_pb_slice_bound : ∀ (n : ℕ) (g : Euclid n → ℝ≥0∞), Measurable g → ∀ t ∈ Icc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) ≤ 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
  intro n g hg t ht
  obtain ⟨ht0, ht1⟩ := ht
  -- One-variable bound: if `s ≥ 1/2` and `c + s • B ⊆ B`, then `∫_B g(c + s v) dv ≤ 2ⁿ ∫_B g`.
  have key : ∀ (c : Euclid n) (s : ℝ), 1 / 2 ≤ s →
      (∀ v ∈ ball (0 : Euclid n) 1, c + s • v ∈ ball (0 : Euclid n) 1) →
      ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v) ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    intro c s hs hcs
    have hs0 : 0 < s := by linarith
    obtain ⟨F, hFdef⟩ : ∃ F : Euclid n → ℝ≥0∞, F = (ball (0 : Euclid n) 1).indicator g := ⟨_, rfl⟩
    have hF : Measurable F := hFdef ▸ hg.indicator measurableSet_ball
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
    calc ∫⁻ v in ball (0 : Euclid n) 1, g (c + s • v)
        = ∫⁻ v in ball (0 : Euclid n) 1, F (c + s • v) := by
          refine setLIntegral_congr_fun measurableSet_ball fun v hv => ?_
          rw [hFdef, Set.indicator_of_mem (hcs v hv)]
      _ ≤ ∫⁻ v, F (c + s • v) := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal |(s ^ n)⁻¹| * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [hcv, hFdef, lintegral_indicator measurableSet_ball]
      _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
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
    calc ∫⁻ y in ball (0 : Euclid n) 1, ∫⁻ x in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
          refine key ((1 - t) • y) t h fun v hv => ?_
          exact convex_ball (0 : Euclid n) 1 hy hv (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring
  · -- `t ≤ 1/2`: change variables in `y` with `c = t • x`, `s = 1 - t`
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
        ≤ ∫⁻ _ in ball (0 : Euclid n) 1, 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
          calc ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)
              = ∫⁻ y in ball (0 : Euclid n) 1, g (t • x + (1 - t) • y) :=
                lintegral_congr fun y => by rw [add_comm]
            _ ≤ 2 ^ n * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
                refine key (t • x) (1 - t) (by linarith) fun v hv => ?_
                rw [add_comm]
                exact convex_ball (0 : Euclid n) 1 hv hx (by linarith) ht0 (by ring)
      _ = 2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const]
          ring

/-- **Poincaré inequality on the unit ball, double-integral step** (the convex-domain argument of
Gilbarg–Trudinger, Lemma 7.16, cited in Simon's proof of Lemma 5.3.1).  For Lipschitz `u` on
`ℝⁿ` and `B = B₁(0)`, `∫_B ∫_B (u(x) - u(y))² ≤ 2ⁿ⁺² ωₙ ∫_B ‖Du‖²`.  For a.e. `x, y ∈ B`,
`dorag_ha_pb_pair_sq_bound` and `‖x - y‖ < 2` give
`(u(x) - u(y))² ≤ 4 ∫₀¹ ‖Du((1 - t)y + tx)‖² dt`.  Integrate over `B × B` and move the
`t`-integral outside (Tonelli); then `dorag_ha_pb_slice_bound` bounds each slice by
`2ⁿ ωₙ ∫_B ‖Du‖²`.  As `‖Du‖ ≤ Lip(u)`, the bound is finite, so it passes from `ℝ≥0∞` to `ℝ`. -/
theorem Submission.dorag_ha_pb_double_integral_bound : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 ≤ 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal * ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
  intro n u L hu
  have hpair := Submission.dorag_ha_pb_pair_sq_bound n u L hu
  have hslice := Submission.dorag_ha_pb_slice_bound n
  have hcont : Continuous u := hu.continuous
  -- Step 1: `g = ofReal ‖Du‖²` is measurable, and `∫_B g < ∞` since `‖Du‖ ≤ L`
  have hD : Measurable fun z => ‖fderiv ℝ u z‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid n → ℝ≥0∞, g = fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) :=
    ⟨_, rfl⟩
  have hgx : ∀ z, g z = ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) := fun z => congrFun hg_def z
  have hg : Measurable g := hg_def ▸ hD.ennreal_ofReal
  have hJ : ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ := by
    have h1 : ∫⁻ z in ball (0 : Euclid n) 1, g z ≤
        ∫⁻ _ in ball (0 : Euclid n) 1, ENNReal.ofReal ((L : ℝ) ^ 2) :=
      lintegral_mono fun z => by
        rw [hgx]
        gcongr
        exact norm_fderiv_le_of_lipschitz ℝ hu
    rw [setLIntegral_const] at h1
    exact (h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)).ne
  -- Step 2: for a.e. `x, y ∈ B`, `(u x - u y)² ≤ 4 ∫_(0,1] ‖Du((1 - t) y + t x)‖² dt`
  have hae : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) 1)),
      ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid n) 1)),
        ENNReal.ofReal ((u x - u y) ^ 2) ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
    filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hpair),
      ae_restrict_mem measurableSet_ball] with x hx hxB
    filter_upwards [ae_restrict_of_ae hx, ae_restrict_mem measurableSet_ball] with y hy hyB
    rw [mem_ball_zero_iff] at hxB hyB
    set G := ∫ t in (0 : ℝ)..1, ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2 with hG_def
    have hG : 0 ≤ G := intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have hxy : ‖x - y‖ ^ 2 ≤ 4 := by
      have h2 : ‖x - y‖ < 2 := by linarith [norm_sub_le x y]
      nlinarith [norm_nonneg (x - y)]
    have h4 : (u x - u y) ^ 2 ≤ 4 * G := hy.trans (mul_le_mul_of_nonneg_right hxy hG)
    -- `G` is the integral over `(0, 1]` of a nonnegative function
    have hmt : AEStronglyMeasurable (fun t : ℝ => ‖fderiv ℝ u ((1 - t) • y + t • x)‖ ^ 2)
        (volume.restrict (Ioc 0 1)) := by
      have h : Continuous fun t : ℝ => (1 - t) • y + t • x := by fun_prop
      exact (hD.comp h.measurable).aestronglyMeasurable
    have hGle : ENNReal.ofReal G ≤ ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by
      rw [hG_def, intervalIntegral.integral_of_le zero_le_one,
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t => sq_nonneg _) hmt]
      simp only [hgx]
      exact ENNReal.ofReal_toReal_le
    calc ENNReal.ofReal ((u x - u y) ^ 2) ≤ ENNReal.ofReal (4 * G) := ENNReal.ofReal_le_ofReal h4
      _ = 4 * ENNReal.ofReal G := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      _ ≤ 4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) := by gcongr
  -- Step 3: integrate over `B × B`, move the `t`-integral outside (Tonelli), apply the slice bound
  have hmeas_yt : ∀ x : Euclid n,
      Measurable (uncurry fun (y : Euclid n) (t : ℝ) => g ((1 - t) • y + t • x)) := fun x =>
    hg.comp (by fun_prop : Continuous fun p : Euclid n × ℝ => (1 - p.2) • p.1 + p.2 • x).measurable
  have hmeas_xt : Measurable (uncurry fun (x : Euclid n) (t : ℝ) =>
      ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x)) :=
    Measurable.lintegral_prod_right'
      (f := fun q : (Euclid n × ℝ) × Euclid n => g ((1 - q.1.2) • q.2 + q.1.2 • q.1.1))
      (hg.comp (by fun_prop : Continuous fun q : (Euclid n × ℝ) × Euclid n =>
        (1 - q.1.2) • q.2 + q.1.2 • q.1.1).measurable)
  have hswap : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        g ((1 - t) • y + t • x) := by
    calc _ = ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          g ((1 - t) • y + t • x) :=
          lintegral_congr fun x => lintegral_lintegral_swap (hmeas_yt x).aemeasurable
      _ = _ := lintegral_lintegral_swap hmeas_xt.aemeasurable
  have hI : ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
        ENNReal.ofReal ((u x - u y) ^ 2) ≤
      2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
    calc ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          ENNReal.ofReal ((u x - u y) ^ 2)
        ≤ ∫⁻ x in ball (0 : Euclid n) 1, ∫⁻ y in ball (0 : Euclid n) 1,
          4 * ∫⁻ t in Ioc (0 : ℝ) 1, g ((1 - t) • y + t • x) :=
          lintegral_mono_ae (hae.mono fun x hx => lintegral_mono_ae hx)
      _ = 4 * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1,
          ∫⁻ y in ball (0 : Euclid n) 1, g ((1 - t) • y + t • x) := by
          simp only [lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)]
          rw [hswap]
      _ ≤ 4 * ∫⁻ _ in Ioc (0 : ℝ) 1,
          2 ^ n * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          gcongr 4 * ?_
          exact setLIntegral_mono' measurableSet_Ioc fun t ht =>
            hslice g hg t (Ioc_subset_Icc_self ht)
      _ = 2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) * ∫⁻ z in ball (0 : Euclid n) 1, g z := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, pow_add]
          ring
  -- Step 4: back to Bochner integrals; the bound is finite since `∫_B g < ∞`
  have hK : Measurable fun x : Euclid n =>
      ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2) := by
    have h : Continuous fun p : Euclid n × Euclid n => (u p.1 - u p.2) ^ 2 := by fun_prop
    exact Measurable.lintegral_prod_right'
      (f := fun p : Euclid n × Euclid n => ENNReal.ofReal ((u p.1 - u p.2) ^ 2))
      h.measurable.ennreal_ofReal
  have hinner : ∀ x : Euclid n, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2 =
      (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := fun x =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
      (by fun_prop : Continuous fun y => (u x - u y) ^ 2).aestronglyMeasurable
  have hrhs : ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 =
      (∫⁻ z in ball (0 : Euclid n) 1, g z).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _)
      hD.aestronglyMeasurable]
    simp only [hgx]
  have hfin : (2 : ℝ≥0∞) ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
      ∫⁻ z in ball (0 : Euclid n) 1, g z ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      measure_ball_lt_top.ne) hJ
  calc ∫ x in ball (0 : Euclid n) 1, ∫ y in ball (0 : Euclid n) 1, (u x - u y) ^ 2
      = ∫ x in ball (0 : Euclid n) 1,
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal := by
        simp only [hinner]
    _ = (∫⁻ x in ball (0 : Euclid n) 1, ENNReal.ofReal
          (∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal ((u x - u y) ^ 2)).toReal).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => ENNReal.toReal_nonneg)
          hK.ennreal_toReal.aestronglyMeasurable
    _ ≤ (2 ^ (n + 2) * volume (ball (0 : Euclid n) 1) *
          ∫⁻ z in ball (0 : Euclid n) 1, g z).toReal :=
        ENNReal.toReal_mono hfin ((lintegral_mono fun x => ENNReal.ofReal_toReal_le).trans hI)
    _ = 2 ^ (n + 2) * (volume (ball (0 : Euclid n) 1)).toReal *
          ∫ z in ball (0 : Euclid n) 1, ‖fderiv ℝ u z‖ ^ 2 := by
        rw [hrhs, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- **Poincaré inequality on a ball** (Simon Ch. 5, proof of Lemma 3.1; Gilbarg–Trudinger,
Lemma 7.16), the averaging step, for any `s ⊆ ℝⁿ` with `ω = Lⁿ(s) < ∞` and `f ∈ L²(s)`:
`∫_s (f − f̄)² ≤ ω⁻¹ ∫_s ∫_s (f(x) − f(y))² dy dx`, `f̄ = ω⁻¹ ∫_s f` (both sides vanish if
`ω = 0`).  For each `x`, `f(x) − f̄ = ω⁻¹ ∫_s (f(x) − f(y)) dy`, so Cauchy–Schwarz
(`dorag_ha_pb_sq_integral_le`) gives `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`.  This is
integrated over `s`; the right side is integrable since `(f(x) − f(y))² ≤ 2f(x)² + 2f(y)²`. -/
theorem Submission.dorag_ha_pb_variance_bound : ∀ (n : ℕ) (s : Set (Euclid n)) (f : Euclid n → ℝ), volume s ≠ ∞ → MemLp f 2 (volume.restrict s) → ∫ x in s, (f x - (∫ y in s, f y) / (volume s).toReal) ^ 2 ≤ ((volume s).toReal)⁻¹ * ∫ x in s, ∫ y in s, (f x - f y) ^ 2 := by
  intro n s f hs hf
  set μ : Measure (Euclid n) := volume.restrict s
  set ω : ℝ := (volume s).toReal
  -- Step 1: `μ` is finite with `μ(ℝⁿ).toReal = ω`, and `f, f² ∈ L¹(μ)`
  have hμuniv : μ univ = volume s := Measure.restrict_apply_univ s
  have hμfin : μ univ ≠ ∞ := hμuniv ▸ hs
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 hs
  have hf1 : Integrable f μ := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hf.integrable_norm_pow two_ne_zero
  -- Step 2: if `ω = 0` then `μ = 0` and both sides vanish
  rcases eq_or_ne ω 0 with hω0 | hω0
  · have hμ0 : μ = 0 :=
      Measure.restrict_eq_zero.2 (((ENNReal.toReal_eq_zero_iff _).1 hω0).resolve_right hs)
    rw [hω0, inv_zero, zero_mul, hμ0, integral_zero_measure]
  -- Step 3: the pointwise bound `(f(x) − f̄)² ≤ ω⁻¹ ∫_s (f(x) − f(y))² dy`
  have hpt : ∀ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ≤ ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by
    intro x
    have hmem : MemLp (fun y => f x - f y) 2 μ := (memLp_const (f x)).sub hf
    have hCS := Submission.dorag_ha_pb_sq_integral_le μ (fun y => f x - f y) hμfin hmem
    rw [hμuniv] at hCS
    have hI : ∫ y, (f x - f y) ∂μ = ω * f x - ∫ y, f y ∂μ := by
      rw [integral_sub (integrable_const (f x)) hf1, integral_const, smul_eq_mul, measureReal_def,
        hμuniv]
    have hdiff : f x - (∫ y, f y ∂μ) / ω = ω⁻¹ * ∫ y, (f x - f y) ∂μ := by
      rw [hI]
      field_simp
    rw [hdiff, mul_pow]
    calc (ω⁻¹) ^ 2 * (∫ y, (f x - f y) ∂μ) ^ 2
        ≤ (ω⁻¹) ^ 2 * (ω * ∫ y, (f x - f y) ^ 2 ∂μ) := by gcongr
      _ = ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ := by field_simp
  -- Step 4: `(x, y) ↦ (f(x) − f(y))²` is `μ ⊗ μ`-integrable, being `≤ 2f(x)² + 2f(y)²`
  have hprod : Integrable (fun p : Euclid n × Euclid n => (f p.1 - f p.2) ^ 2) (μ.prod μ) := by
    have hm := hf.aestronglyMeasurable
    refine Integrable.mono' (((hf2.comp_fst μ).const_mul 2).add ((hf2.comp_snd μ).const_mul 2))
      ((hm.comp_fst.sub hm.comp_snd).pow 2) (ae_of_all _ fun p => ?_)
    show ‖(f p.1 - f p.2) ^ 2‖ ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (f p.1 + f p.2)]
  have hinner : Integrable (fun x => ∫ y, (f x - f y) ^ 2 ∂μ) μ := hprod.integral_prod_left
  -- Step 5: integrate the pointwise bound over `s`
  calc ∫ x, (f x - (∫ y, f y ∂μ) / ω) ^ 2 ∂μ
      ≤ ∫ x, ω⁻¹ * ∫ y, (f x - f y) ^ 2 ∂μ ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hinner.const_mul ω⁻¹)
          (ae_of_all _ hpt)
    _ = ω⁻¹ * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := integral_const_mul _ _

/-- **Poincaré inequality on the unit ball** for Lipschitz `u : ℝⁿ → ℝ` (the inequality cited in
Simon's proof of 5.3.1, "by the Poincaré inequality (see e.g. [GT01])"; Gilbarg–Trudinger,
Lemma 7.16 and (7.45)).  With `B = B̆₁(0)`, `ω = Lⁿ(B) ∈ (0, ∞)` and `ū = ω⁻¹∫_B u`,
`∫_B (u − ū)² ≤ ω⁻¹∫_B∫_B (u(x) − u(y))² dy dx ≤ ω⁻¹ · 2ⁿ⁺²ω∫_B ‖Du‖² = 2ⁿ⁺²∫_B ‖Du‖²`:
the first step is the variance bound (`u ∈ L²(B)`, being continuous with `|u| ≤ |u(0)| + L` on
`B`), the second the double-integral bound (FTC along segments and the affine change of
variables).  So `C_P = 2ⁿ⁺²`. -/
theorem Submission.dorag_ha_poincare_ball : ∀ n : ℕ, 0 < n → ∃ CP : ℝ, 0 < CP ∧ ∀ (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∫ x in ball (0 : Euclid n) 1, (u x - (∫ y in ball (0 : Euclid n) 1, u y) / (volume (ball (0 : Euclid n) 1)).toReal) ^ 2 ≤ CP * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n _
  refine ⟨2 ^ (n + 2), by positivity, fun u L hu => ?_⟩
  -- `ω = Lⁿ(B) ∈ (0, ∞)`
  have hBfin : volume (ball (0 : Euclid n) 1) ≠ ∞ := measure_ball_lt_top.ne
  have hω : 0 < (volume (ball (0 : Euclid n) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume (0 : Euclid n) one_pos).ne' hBfin
  -- `u ∈ L²(B)`: `u` is continuous and `‖u x‖ ≤ ‖u 0‖ + L` on `B`
  have hmem : MemLp u 2 (volume.restrict (ball (0 : Euclid n) 1)) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
      isFiniteMeasure_restrict.mpr hBfin
    refine MemLp.of_bound hu.continuous.aestronglyMeasurable (‖u 0‖ + L) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    have hux : dist (u x) (u 0) ≤ L * 1 := hu.dist_le_mul_of_le (mem_ball.mp hx).le
    calc ‖u x‖ = dist (u x) 0 := (dist_zero_right _).symm
      _ ≤ dist (u x) (u 0) + dist (u 0) 0 := dist_triangle _ _ _
      _ ≤ ‖u 0‖ + L := by rw [dist_zero_right]; linarith
  -- the variance bound, then the double-integral bound multiplied by `ω⁻¹ ≥ 0`
  calc _ ≤ _ := Submission.dorag_ha_pb_variance_bound n (ball (0 : Euclid n) 1) u hBfin hmem
    _ ≤ _ := mul_le_mul_of_nonneg_left
          (Submission.dorag_ha_pb_double_integral_bound n u L hu) (inv_nonneg.mpr hω.le)
    _ = _ := by rw [mul_comm (2 ^ (n + 2) : ℝ), mul_assoc, inv_mul_cancel_left₀ hω.ne']
namespace Submission

/-- Fundamental theorem of calculus for a Lipschitz `u` along the line `τ ↦ p + τ v`: if `u` is
differentiable at `p + τ v` for a.e. `τ ∈ [a, b]`, then
`u(p + b v) − u(p + a v) = ∫_a^b Du(p + τ v) v dτ`.  The difference quotients of
`φ(τ) = u(p + τ v)` are bounded by `L ‖v‖`, so dominated convergence takes their integrals to
`∫_a^b Du(p + τ v) v`; the same integrals are boundary averages of `φ`, which tend to
`φ(b) − φ(a)`. -/
theorem dorag_ha_rb_line_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (p v : Euclid n) (a b : ℝ), LipschitzWith L u → (∀ᵐ τ : ℝ, τ ∈ Set.uIcc a b → DifferentiableAt ℝ u (p + τ • v)) → u (p + b • v) - u (p + a • v) = ∫ τ in a..b, fderiv ℝ u (p + τ • v) v := by
  intro n u L p v a b hu hdiff
  -- `φ τ = u (p + τ • v)` is continuous and `L ‖v‖`-Lipschitz
  set φ : ℝ → ℝ := fun τ => u (p + τ • v) with hφ
  have hφcont : Continuous φ :=
    hu.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hφlip : ∀ s t : ℝ, |φ s - φ t| ≤ L * ‖v‖ * |s - t| := by
    intro s t
    have h := hu.dist_le_mul (p + s • v) (p + t • v)
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
      Real.norm_eq_abs] at h
    calc |φ s - φ t| ≤ L * (|s - t| * ‖v‖) := h
      _ = L * ‖v‖ * |s - t| := by ring
  -- chain rule along the line
  have hderiv : ∀ τ : ℝ, DifferentiableAt ℝ u (p + τ • v) →
      HasDerivAt φ (fderiv ℝ u (p + τ • v) v) τ := by
    intro τ hτ
    have hγ : HasDerivAt (fun t : ℝ => p + t • v) v τ := by
      simpa using ((hasDerivAt_id τ).smul_const v).const_add p
    exact hτ.hasFDerivAt.comp_hasDerivAt τ hγ
  -- dominated convergence for the difference quotients
  have hlim1 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (∫ τ in a..b, fderiv ℝ u (p + τ • v) v)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (L : ℝ) * ‖v‖) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards with h
      exact (((hφcont.comp (continuous_id.add continuous_const)).sub hφcont).const_smul
        h⁻¹).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with h hh
      filter_upwards with τ _
      have hh' : (0 : ℝ) < h := hh
      rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hh']
      have := hφlip (τ + h) τ
      rw [add_sub_cancel_left, abs_of_pos hh'] at this
      calc h⁻¹ * |φ (τ + h) - φ τ| ≤ h⁻¹ * (L * ‖v‖ * h) :=
            mul_le_mul_of_nonneg_left this (inv_nonneg.2 hh'.le)
        _ = L * ‖v‖ := by field_simp
    · filter_upwards [hdiff] with τ hτ hτ'
      exact (hderiv τ (hτ (uIoc_subset_uIcc hτ'))).tendsto_slope_zero_right
  -- the difference quotients integrate to boundary averages
  set F : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..x, φ τ with hF
  have hFint : ∀ s t : ℝ, ∫ τ in s..t, φ τ = F t - F s := by
    intro s t
    exact (intervalIntegral.integral_interval_sub_left (hφcont.intervalIntegrable _ _)
      (hφcont.intervalIntegrable _ _)).symm
  have hkey : ∀ h : ℝ, ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)
      = h⁻¹ • (F (b + h) - F b) - h⁻¹ • (F (a + h) - F a) := by
    intro h
    have hi : IntervalIntegrable (fun τ => φ (τ + h)) volume a b :=
      (hφcont.comp (continuous_id.add continuous_const)).intervalIntegrable a b
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub hi
      (hφcont.intervalIntegrable a b), intervalIntegral.integral_comp_add_right (fun τ => φ τ) h,
      hFint, hFint]
    simp only [smul_eq_mul]
    ring
  have hFd : ∀ x : ℝ, HasDerivAt F (φ x) x := fun x =>
    (hφcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hlim2 : Tendsto (fun h : ℝ => ∫ τ in a..b, h⁻¹ • (φ (τ + h) - φ τ)) (𝓝[>] 0)
      (𝓝 (φ b - φ a)) := by
    simp_rw [hkey]
    exact (hFd b).tendsto_slope_zero_right.sub (hFd a).tendsto_slope_zero_right
  exact tendsto_nhds_unique hlim2 hlim1


end Submission

/-- **FTC along translates of a Lipschitz function, for a.e. base point.**  If `u : ℝⁿ → ℝ` is
`L`-Lipschitz and `z ∈ ℝⁿ`, then `u(p + z) − u(p) = ∫₀¹ Du(p + τz)z dτ` for a.e. `p ∈ ℝⁿ`.  By
Rademacher's theorem the measurable set `D` of differentiability points of `u` is conull, so by
translation invariance `p + τz ∈ D` for a.e. `p`, for every `τ`.  Fubini for the null set of the
measurable set `{(p, τ) : p + τz ∈ D}` then gives, for a.e. `p`, `p + τz ∈ D` for a.e. `τ`: the
hypothesis of the line FTC `Submission.dorag_ha_rb_line_ftc` with `v = z`, `a = 0`, `b = 1`. -/
theorem Submission.dorag_ha_rb_segment_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (z : Euclid n), LipschitzWith L u → ∀ᵐ p : Euclid n, u (p + z) - u p = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (p + τ • z) z := by
  intro n u L z hu
  -- step 1: the set `D` of differentiability points of `u` is measurable and conull (Rademacher)
  have hD : MeasurableSet {y : Euclid n | DifferentiableAt ℝ u y} :=
    measurableSet_of_differentiableAt ℝ u
  have hae : ∀ᵐ y : Euclid n, DifferentiableAt ℝ u y := hu.ae_differentiableAt
  -- step 2: for every `τ`, `p ↦ p + τz` preserves Lebesgue measure, so `p + τz ∈ D` for a.e. `p`
  have hτ : ∀ τ : ℝ, ∀ᵐ p : Euclid n, DifferentiableAt ℝ u (p + τ • z) := fun τ =>
    (measurePreserving_add_right volume (τ • z)).quasiMeasurePreserving.ae hae
  -- step 3: `{(p, τ) : p + τz ∈ D}` is measurable, so Fubini lets us swap the a.e. quantifiers
  have hmeas : MeasurableSet {q : Euclid n × ℝ | DifferentiableAt ℝ u (q.1 + q.2 • z)} :=
    hD.preimage (measurable_fst.add (measurable_snd.smul_const z))
  have hp : ∀ᵐ p : Euclid n, ∀ᵐ τ : ℝ, DifferentiableAt ℝ u (p + τ • z) :=
    (Measure.ae_ae_comm (p := fun p τ => DifferentiableAt ℝ u (p + τ • z)) hmeas).2
      (Eventually.of_forall hτ)
  -- step 4: the line FTC with `v = z`, `a = 0`, `b = 1`, and `1 • z = z`, `p + 0 • z = p`
  filter_upwards [hp] with p hp
  have h := Submission.dorag_ha_rb_line_ftc n u L p z 0 1 hu (hp.mono fun τ hτ _ => hτ)
  rwa [one_smul, zero_smul, add_zero] at h
/-- FTC along rays through the origin: for an `L`-Lipschitz `u` and a.e. `x`,
`u(x) − u(tx) = ∫_t^1 Du(σx)x dσ` for every `t`.  By Rademacher the differentiability set `D` of
`u` is measurable and conull.  For `σ ≠ 0` the dilation `x ↦ σx` pulls null sets back to null sets
(Haar scaling), so a.e. `x` has `σx ∈ D`; `σ = 0` is a null exception in `ℝ`.  Swapping the two
a.e. quantifiers (`Measure.ae_ae_comm`, `{(σ, x) : σx ∈ D}` being measurable) gives a.e. `x` with
`σx ∈ D` for a.e. `σ`, and for such `x` the line FTC `Submission.dorag_ha_rb_line_ftc` with
`p = 0`, `v = x` applies for every `t`. -/
theorem Submission.dorag_ha_rb_ray_ftc : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal), LipschitzWith L u → ∀ᵐ x : Euclid n, ∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x := by
  intro n u L hu
  -- for `σ ≠ 0`, a.e. `x` has `σ • x` in the (conull) differentiability set
  have hσ : ∀ᵐ σ : ℝ, ∀ᵐ x : Euclid n, DifferentiableAt ℝ u (σ • x) := by
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with σ hσ
    exact (Measure.quasiMeasurePreserving_smul volume hσ).ae hu.ae_differentiableAt
  -- swap the quantifiers: `{(σ, x) | DifferentiableAt ℝ u (σ • x)}` is measurable
  have hx : ∀ᵐ x : Euclid n, ∀ᵐ σ : ℝ, DifferentiableAt ℝ u (σ • x) :=
    (Measure.ae_ae_comm (p := fun (σ : ℝ) (x : Euclid n) => DifferentiableAt ℝ u (σ • x))
      ((continuous_smul (M := ℝ) (X := Euclid n)).measurable
        (measurableSet_of_differentiableAt ℝ u))).1 hσ
  filter_upwards [hx] with x hx t
  have h := Submission.dorag_ha_rb_line_ftc n u L 0 x t 1 hu (by
    filter_upwards [hx] with σ hσ _
    rwa [zero_add])
  simpa only [zero_add, one_smul] using h

namespace Submission

/-- Dilation averaging on the boundary annulus `A_s = B₁(0) \ B_{1-s}(0)`: for measurable
`F ≥ 0` integrable on `B₁(0)` and `0 < s ≤ 1/2`,
`∫_{A_s} ∫_{1/2}^1 F(t x) dt dx ≤ 2^(n+1) s ∫_{B₁(0)} F`.  In lower integrals: Tonelli, the
substitution `y = t x` (Jacobian `t⁻ⁿ ≤ 2ⁿ`), Tonelli again, and for each `y` the admissible
`t` lie in `(‖y‖, ‖y‖ / (1 - s)]`, of length `≤ 2 s`, and only when `‖y‖ < 1`. -/
theorem dorag_ha_rb_dilation_average : ∀ (n : ℕ) (F : Euclid n → ℝ) (s : ℝ), Measurable F → (∀ y, 0 ≤ F y) → IntegrableOn F (ball (0 : Euclid n) 1) → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), (∫ t in (1 / 2 : ℝ)..1, F (t • x)) ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y := by
  intro n F s hF hF0 hFi hs hs2
  have hC0 : 0 ≤ 2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (integral_nonneg hF0)
  rw [← ENNReal.ofReal_le_ofReal_iff hC0]
  -- `ofReal` of a Bochner integral is at most the lower integral of `ofReal`
  have step1 : ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
    calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
        ≤ ‖∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          (∫ t in (1 / 2 : ℝ)..1, F (t • x))‖ₑ := by
          rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ‖∫ t in (1 / 2 : ℝ)..1, F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
          refine lintegral_mono fun x => ?_
          rw [intervalIntegral.integral_of_le (by norm_num)]
          calc ‖∫ t in Ioc (1 / 2 : ℝ) 1, F (t • x)‖ₑ
              ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ‖F (t • x)‖ₑ := enorm_integral_le_lintegral_enorm _
            _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := by
              congr 1; ext t; exact Real.enorm_eq_ofReal (hF0 _)
  -- Tonelli
  have hmeas : Measurable (fun p : Euclid n × ℝ => ENNReal.ofReal (F (p.2 • p.1))) :=
    (hF.comp (measurable_snd.smul measurable_fst)).ennreal_ofReal
  have step2 : ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x))
      = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) :=
    lintegral_lintegral_swap hmeas.aemeasurable
  -- the region `{(t, y) : t (1 - s) ≤ ‖y‖ < t}` and the integrand on it
  obtain ⟨T, hT⟩ : ∃ T : Set (ℝ × Euclid n), T = {p | p.1 * (1 - s) ≤ ‖p.2‖ ∧ ‖p.2‖ < p.1} :=
    ⟨_, rfl⟩
  have hTm : MeasurableSet T := hT ▸
    (measurableSet_le (measurable_fst.mul_const _) measurable_snd.norm).inter
      (measurableSet_lt measurable_snd.norm measurable_fst)
  obtain ⟨H, hH⟩ : ∃ H : ℝ × Euclid n → ℝ≥0∞, H = T.indicator (fun p => ENNReal.ofReal (F p.2)) :=
    ⟨_, rfl⟩
  have hHm : Measurable H := hH ▸ (hF.comp measurable_snd).ennreal_ofReal.indicator hTm
  -- change of variables `y = t x`
  have step3 : ∀ t ∈ Ioc (1 / 2 : ℝ) 1,
      ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by
    intro t ht
    have ht0 : 0 < t := lt_trans (by norm_num) ht.1
    have hmem : ∀ x : Euclid n,
        x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s) ↔ (t, t • x) ∈ T := by
      intro x
      rw [hT]
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht0, not_lt]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨mul_le_mul_of_nonneg_left h2 ht0.le, mul_lt_of_lt_one_right ht0 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_mul_lt_mul_left (by linarith) ht0.le, le_of_mul_le_mul_left h1 ht0⟩
    have hind : (ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)).indicator
        (fun x => ENNReal.ofReal (F (t • x))) = fun x => H (t, t • x) := by
      ext x
      rw [hH]
      by_cases hx : x ∈ ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s)
      · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).1 hx)]
      · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).2 h))]
    have hHt : Measurable fun y : Euclid n => H (t, y) := hHm.comp measurable_prodMk_left
    have hjac : ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| ≤ ENNReal.ofReal (2 ^ n) := by
      apply ENNReal.ofReal_le_ofReal
      rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity), ← inv_pow]
      have : t⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ ht0 (by norm_num)]; linarith [ht.1]
      exact pow_le_pow_left₀ (by positivity) this n
    calc ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), ENNReal.ofReal (F (t • x))
        = ∫⁻ x, H (t, t • x) := by
          rw [← lintegral_indicator (measurableSet_ball.diff measurableSet_ball), hind]
      _ = ∫⁻ y, H (t, y) ∂(Measure.map (t • ·) volume) :=
          (lintegral_map hHt (measurable_const_smul t)).symm
      _ = ENNReal.ofReal |(t ^ Module.finrank ℝ (Euclid n))⁻¹| * ∫⁻ y, H (t, y) := by
          rw [Measure.map_addHaar_smul volume ht0.ne', lintegral_smul_measure, smul_eq_mul]
      _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) := by gcongr
  have step4 : ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x))
      ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
    calc ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
          ENNReal.ofReal (F (t • x))
        ≤ ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (2 ^ n) * ∫⁻ y, H (t, y) :=
          setLIntegral_mono' measurableSet_Ioc step3
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ y, H (t, y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := by
          rw [lintegral_lintegral_swap (f := fun t y => H (t, y)) hHm.aemeasurable]
  -- length of the admissible parameter interval
  have step5 : ∀ y : Euclid n, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := by
    intro y
    have hSm : MeasurableSet {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} :=
      (measurableSet_le (measurable_id.mul_const _) measurable_const).inter
        (measurableSet_lt measurable_const measurable_id)
    have hHy : (fun t => H (t, y)) = {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t}.indicator
        (fun _ => ENNReal.ofReal (F y)) := by
      ext t
      rw [hH, hT]
      simp only [indicator, mem_ofPred_eq]
    rw [hHy, lintegral_indicator_const hSm, Measure.restrict_apply hSm]
    by_cases hy : ‖y‖ < 1
    · rw [indicator_of_mem (mem_ball_zero_iff.2 hy), mul_comm]
      gcongr
      have h1s : 0 < 1 - s := by linarith
      calc volume ({t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1)
          ≤ volume (Ioc ‖y‖ (‖y‖ / (1 - s))) := by
            apply measure_mono
            rintro t ⟨⟨h1, h2⟩, -⟩
            exact ⟨h2, (le_div_iff₀ h1s).2 h1⟩
        _ = ENNReal.ofReal (‖y‖ / (1 - s) - ‖y‖) := Real.volume_Ioc
        _ ≤ ENNReal.ofReal (2 * s) := by
            apply ENNReal.ofReal_le_ofReal
            rw [sub_le_iff_le_add, div_le_iff₀ h1s]
            nlinarith [mul_pos hs (show 0 < 2 - 2 * s - ‖y‖ by linarith)]
    · rw [indicator_of_notMem (by simpa using hy)]
      have hempty : {t : ℝ | t * (1 - s) ≤ ‖y‖ ∧ ‖y‖ < t} ∩ Ioc (1 / 2 : ℝ) 1 = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioc, mem_empty_iff_false, iff_false]
        rintro ⟨⟨-, h2⟩, -, h4⟩
        exact hy (h2.trans_le h4)
      rw [hempty, measure_empty, mul_zero]
  have step6 : ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
      ≤ ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) := by
    calc ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y)
        ≤ ∫⁻ y, (ball (0 : Euclid n) 1).indicator
          (fun y => ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y)) y := lintegral_mono step5
      _ = ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (2 * s) * ENNReal.ofReal (F y) :=
          lintegral_indicator measurableSet_ball _
      _ = ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hBeq : ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)
      = ENNReal.ofReal (∫ y in ball (0 : Euclid n) 1, F y) :=
    (ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ hF0)).symm
  calc ENNReal.ofReal (∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        (∫ t in (1 / 2 : ℝ)..1, F (t • x)))
      ≤ ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ENNReal.ofReal (F (t • x)) := step1
    _ = ∫⁻ t in Ioc (1 / 2 : ℝ) 1, ∫⁻ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s),
        ENNReal.ofReal (F (t • x)) := step2
    _ ≤ ENNReal.ofReal (2 ^ n) * ∫⁻ y, ∫⁻ t in Ioc (1 / 2 : ℝ) 1, H (t, y) := step4
    _ ≤ ENNReal.ofReal (2 ^ n) *
        (ENNReal.ofReal (2 * s) * ∫⁻ y in ball (0 : Euclid n) 1, ENNReal.ofReal (F y)) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ (n + 1) * s * ∫ y in ball (0 : Euclid n) 1, F y) := by
        rw [hBeq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Submission

/-- **`L²` translation estimate** (cf. Gilbarg–Trudinger, Lemma 7.23; Evans, §5.8.2, Theorem 3),
for Rellich's theorem in the proof of the harmonic approximation lemma (Simon Ch. 5, 3.1, p. 114:
"by Rellich's theorem (see [GT01])").  If `u` is Lipschitz on `ℝⁿ` and `r + ‖w‖ ≤ R`, then
`∫_{B_r} (u(x) − u(x − w))² ≤ ‖w‖² ∫_{B_R} ‖Du‖²`: for a.e. `x`,
`u(x) − u(x − w) = ∫₀¹ Du(x − w + τw)w dτ`; Cauchy–Schwarz on `(0, 1]` bounds its square by
`‖w‖² ∫₀¹ ‖Du(x − w + τw)‖² dτ`; for `x ∈ B_r` the segment lies in `B_R`; integrating over `B_r`,
Fubini and translation invariance of Lebesgue measure give the bound. -/
theorem Submission.dorag_ha_rb_translation_l2 : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (w : Euclid n) (r R : ℝ), LipschitzWith L u → r + ‖w‖ ≤ R → ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2 ≤ ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u L w r R hu hrR
  -- Step 1: `G_R = 1_{B_R} ‖Du‖²`: measurable, `0 ≤ G_R ≤ L²`, integrable, `∫ G_R = ∫_{B_R} ‖Du‖²`
  obtain ⟨GR, hGR⟩ : ∃ GR : Euclid n → ℝ,
      GR = (ball (0 : Euclid n) R).indicator fun y => ‖fderiv ℝ u y‖ ^ 2 := ⟨_, rfl⟩
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hG_meas : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := (measurable_fderiv ℝ u).norm.pow_const 2
  have hG_le : ∀ y, ‖fderiv ℝ u y‖ ^ 2 ≤ (L : ℝ) ^ 2 := fun y =>
    pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  have hGR_meas : Measurable GR := by
    rw [hGR]; exact hG_meas.indicator measurableSet_ball
  have hGR_nonneg : ∀ y, 0 ≤ GR y := fun y => by
    rw [hGR]; exact indicator_nonneg (fun y _ => sq_nonneg _) y
  have hGR_le : ∀ y, GR y ≤ (L : ℝ) ^ 2 := fun y => by
    by_cases hy : y ∈ ball (0 : Euclid n) R
    · rw [hGR, indicator_of_mem hy]; exact hG_le y
    · rw [hGR, indicator_of_notMem hy]; positivity
  have hGR_int : Integrable GR := by
    rw [hGR, integrable_indicator_iff measurableSet_ball]
    refine IntegrableOn.of_bound measure_ball_lt_top hG_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hG_le y
  have hGR_eq : ∫ y, GR y = ∫ y in ball (0 : Euclid n) R, ‖fderiv ℝ u y‖ ^ 2 := by
    rw [hGR]; exact integral_indicator measurableSet_ball
  -- Step 2: the segment FTC transported by `x ↦ x − w`: for a.e. `x`,
  -- `u x − u (x − w) = ∫_{(0, 1]} Du(x − w + τw)w dτ`
  have hftc : ∀ᵐ x : Euclid n, u x - u (x - w) =
      ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w := by
    filter_upwards [(measurePreserving_sub_right volume w).quasiMeasurePreserving.ae
      (Submission.dorag_ha_rb_segment_ftc n u L w hu)] with x hx
    have hx' : u (x - w + w) - u (x - w) = ∫ τ in (0 : ℝ)..1, fderiv ℝ u (x - w + τ • w) w := hx
    rwa [sub_add_cancel, intervalIntegral.integral_of_le zero_le_one] at hx'
  -- Step 3: Cauchy–Schwarz on `(0, 1]`, via `0 ≤ ∫ (h − c)² = ∫ h² − c²` for `c = ∫ h`
  have hvol : volume.real (Ioc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  have hCS : ∀ h : ℝ → ℝ, IntegrableOn h (Ioc (0 : ℝ) 1) →
      IntegrableOn (fun τ => h τ ^ 2) (Ioc (0 : ℝ) 1) →
      (∫ τ in Ioc (0 : ℝ) 1, h τ) ^ 2 ≤ ∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2 := by
    intro h hi hi2
    set c := ∫ τ in Ioc (0 : ℝ) 1, h τ with hc
    have i1 : Integrable (fun τ => 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.const_mul hi _
    have i2 : Integrable (fun τ => h τ ^ 2 - 2 * c * h τ) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      Integrable.sub hi2 i1
    have hexp : ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 = (∫ τ in Ioc (0 : ℝ) 1, h τ ^ 2) - c ^ 2 := by
      have e : (fun τ => (h τ - c) ^ 2) = fun τ => (h τ ^ 2 - 2 * c * h τ) + c ^ 2 := by
        funext τ; ring
      rw [e, integral_add i2 (integrable_const _), integral_sub hi2 i1, integral_const_mul,
        setIntegral_const, hvol, one_smul, ← hc]
      ring
    have h0 : 0 ≤ ∫ τ in Ioc (0 : ℝ) 1, (h τ - c) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioc fun τ _ => sq_nonneg _
    linarith
  -- pointwise bounds `|Du(y)w| ≤ ‖Du(y)‖‖w‖` and `(Du(y)w)² ≤ ‖w‖² ‖Du(y)‖²`
  have hDuw : ∀ y, |fderiv ℝ u y w| ≤ ‖fderiv ℝ u y‖ * ‖w‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact (fderiv ℝ u y).le_opNorm w
  have hsq : ∀ y, fderiv ℝ u y w ^ 2 ≤ ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := fun y => by
    calc fderiv ℝ u y w ^ 2 = |fderiv ℝ u y w| ^ 2 := (sq_abs _).symm
      _ ≤ (‖fderiv ℝ u y‖ * ‖w‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hDuw y) 2
      _ = ‖w‖ ^ 2 * ‖fderiv ℝ u y‖ ^ 2 := by ring
  -- Step 4: for `x ∈ B_r` and `τ ∈ (0, 1]`, `x − w + τw = x − (1 − τ)w ∈ B_R`
  have hseg : ∀ x ∈ ball (0 : Euclid n) r, ∀ τ ∈ Ioc (0 : ℝ) 1,
      x - w + τ • w ∈ ball (0 : Euclid n) R := by
    intro x hx τ hτ
    rw [mem_ball_zero_iff] at hx ⊢
    have e : x - w + τ • w = x - (1 - τ) • w := by rw [sub_smul, one_smul]; abel
    have h1 : (1 - τ) * ‖w‖ ≤ ‖w‖ :=
      mul_le_of_le_one_left (norm_nonneg w) (by linarith [hτ.1])
    rw [e]
    calc ‖x - (1 - τ) • w‖ ≤ ‖x‖ + ‖(1 - τ) • w‖ := norm_sub_le _ _
      _ = ‖x‖ + (1 - τ) * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 hτ.2)]
      _ < r + ‖w‖ := by linarith
      _ ≤ R := hrR
  -- the integrand `F(x, τ) = G_R(x − w + τw)` on `B_r × (0, 1]`
  have hF_meas : Measurable fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w) :=
    hGR_meas.comp ((measurable_fst.sub_const w).add (measurable_snd.smul_const w))
  have hint01 : ∀ x : Euclid n, IntegrableOn (fun τ : ℝ => GR (x - w + τ • w)) (Ioc (0 : ℝ) 1) :=
    fun x => IntegrableOn.of_bound measure_Ioc_lt_top
      (hGR_meas.comp ((measurable_id.smul_const w).const_add (x - w))).aestronglyMeasurable
      ((L : ℝ) ^ 2) (ae_of_all _ fun τ => by
        rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  -- Steps 3 and 4: for a.e. `x ∈ B_r`, `(u x − u (x − w))² ≤ ‖w‖² ∫_{(0, 1]} F(x, τ) dτ`
  have hpt : ∀ᵐ x ∂(volume.restrict (ball (0 : Euclid n) r)), (u x - u (x - w)) ^ 2 ≤
      ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hftc] with x hx hxr
    have hm : Measurable fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w :=
      (measurable_fderiv_apply_const ℝ u w).comp ((measurable_id.smul_const w).const_add (x - w))
    have hi : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable ((L : ℝ) * ‖w‖)
        (ae_of_all _ fun τ => (Real.norm_eq_abs _).le.trans ((hDuw _).trans
          (mul_le_mul_of_nonneg_right (hDu _) (norm_nonneg w))))
    have hi2 : IntegrableOn (fun τ : ℝ => fderiv ℝ u (x - w + τ • w) w ^ 2) (Ioc (0 : ℝ) 1) :=
      IntegrableOn.of_bound measure_Ioc_lt_top (hm.pow_const 2).aestronglyMeasurable
        (‖w‖ ^ 2 * (L : ℝ) ^ 2) (ae_of_all _ fun τ => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          exact (hsq _).trans (mul_le_mul_of_nonneg_left (hG_le _) (sq_nonneg _)))
    rw [hx]
    calc (∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w) ^ 2
        ≤ ∫ τ in Ioc (0 : ℝ) 1, fderiv ℝ u (x - w + τ • w) w ^ 2 := hCS _ hi hi2
      _ ≤ ∫ τ in Ioc (0 : ℝ) 1, ‖w‖ ^ 2 * GR (x - w + τ • w) := by
          refine setIntegral_mono_on hi2 (Integrable.const_mul (hint01 x) _) measurableSet_Ioc
            fun τ hτ => ?_
          rw [hGR, indicator_of_mem (hseg x hxr τ hτ)]
          exact hsq _
      _ = ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) := integral_const_mul _ _
  -- Step 5: `F` is bounded on the finite measure space `B_r × (0, 1]`, hence integrable
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hF_int : Integrable (fun p : Euclid n × ℝ => GR (p.1 - w + p.2 • w))
      ((volume.restrict (ball (0 : Euclid n) r)).prod (volume.restrict (Ioc (0 : ℝ) 1))) :=
    Integrable.of_bound hF_meas.aestronglyMeasurable ((L : ℝ) ^ 2)
      (ae_of_all _ fun p => by rw [Real.norm_of_nonneg (hGR_nonneg _)]; exact hGR_le _)
  have hΦ_int : Integrable (fun x => ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w))
      (volume.restrict (ball (0 : Euclid n) r)) := hF_int.integral_prod_left
  -- Step 6: Fubini and translation invariance: `∫_{B_r} ∫_{(0, 1]} F ≤ ∫ G_R`
  have hΦ_le : ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) ≤
      ∫ y, GR y := by
    rw [integral_integral_swap (f := fun x τ => GR (x - w + τ • w)) hF_int]
    calc ∫ τ in Ioc (0 : ℝ) 1, ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w)
        ≤ ∫ τ in Ioc (0 : ℝ) 1, ∫ y, GR y := by
          refine integral_mono_of_nonneg
            (ae_of_all _ fun τ => integral_nonneg fun x => hGR_nonneg _) (integrable_const _)
            (ae_of_all _ fun τ => ?_)
          have e : (fun x => GR (x - w + τ • w)) = fun x => GR (x + (τ • w - w)) := by
            funext x; congr 1; abel
          calc ∫ x in ball (0 : Euclid n) r, GR (x - w + τ • w) ≤ ∫ x, GR (x - w + τ • w) :=
                setIntegral_le_integral (by rw [e]; exact hGR_int.comp_add_right _)
                  (ae_of_all _ fun x => hGR_nonneg _)
            _ = ∫ y, GR y := by rw [e, integral_add_right_eq_self]
      _ = ∫ y, GR y := by rw [setIntegral_const, hvol, one_smul]
  -- Step 7: combine
  calc ∫ x in ball (0 : Euclid n) r, (u x - u (x - w)) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) r, ‖w‖ ^ 2 * ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) (hΦ_int.const_mul _) hpt
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) r, ∫ τ in Ioc (0 : ℝ) 1, GR (x - w + τ • w) :=
        integral_const_mul _ _
    _ ≤ ‖w‖ ^ 2 * ∫ y, GR y := mul_le_mul_of_nonneg_left hΦ_le (sq_nonneg _)
    _ = ‖w‖ ^ 2 * ∫ x in ball (0 : Euclid n) R, ‖fderiv ℝ u x‖ ^ 2 := by rw [hGR_eq]

/-- Step 3 (boundary layer) of the Rellich compactness argument on the unit ball, used for the
harmonic approximation in Allard's theorem (Simon 7.4.3): for `L`-Lipschitz `u : ℝⁿ → ℝ` and
`0 < s ≤ 1/2`, the annulus `A_s = B₁ \ B_{1-s}` satisfies
`∫_{A_s} u² ≤ 2^{n+3} s (∫_{B₁} u² + ∫_{B₁} ‖Du‖²)`.  Along a.e. ray
`u(x) - u(tx) = ∫_t^1 Du(σx)x dσ` (`Submission.dorag_ha_rb_ray_ftc`), so Cauchy–Schwarz on
`[1/2, 1]` gives `u(x)² ≤ 4 ∫_{1/2}^1 u(tx)² dt + ∫_{1/2}^1 ‖Du(tx)‖² dt` for `x ∈ B₁`;
integrate over `A_s` and average over dilations (`Submission.dorag_ha_rb_dilation_average`). -/
theorem Submission.dorag_ha_rb_boundary_layer : ∀ (n : ℕ) (u : Euclid n → ℝ) (L : NNReal) (s : ℝ), LipschitzWith L u → 0 < s → s ≤ 1 / 2 → ∫ x in ball (0 : Euclid n) 1 \ ball (0 : Euclid n) (1 - s), u x ^ 2 ≤ 2 ^ (n + 3) * s * ((∫ x in ball (0 : Euclid n) 1, u x ^ 2) + ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) := by
  intro n u L s hu hs hs2
  set B : Set (Euclid n) := ball (0 : Euclid n) 1
  set A : Set (Euclid n) := B \ ball (0 : Euclid n) (1 - s)
  have hBm : MeasurableSet B := measurableSet_ball
  have hAm : MeasurableSet A := hBm.diff measurableSet_ball
  have hBfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hcont : Continuous u := hu.continuous
  have hhalf : (1 / 2 : ℝ) ≤ 1 := by norm_num
  -- `‖Du‖ ≤ L` everywhere and `|u| ≤ |u 0| + L` on the closed unit ball
  have hDu : ∀ y, ‖fderiv ℝ u y‖ ≤ L := fun y => norm_fderiv_le_of_lipschitz ℝ hu
  have hu_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → |u y| ≤ |u 0| + L := by
    intro y hy
    have h1 : dist (u y) (u 0) ≤ L * dist y 0 := hu.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right] at h1
    have h2 : (L : ℝ) * ‖y‖ ≤ L := mul_le_of_le_one_right L.coe_nonneg hy
    have h3 := abs_sub_abs_le_abs_sub (u y) (u 0)
    linarith
  have hsq_bd : ∀ y : Euclid n, ‖y‖ ≤ 1 → ‖u y ^ 2‖ ≤ (|u 0| + L) ^ 2 := fun y hy => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hu_bd y hy) 2
  have hDsq_bd : ∀ y : Euclid n, ‖‖fderiv ℝ u y‖ ^ 2‖ ≤ (L : ℝ) ^ 2 := fun y => by
    rw [Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hDu y) 2
  -- a bounded measurable function is interval integrable
  have hii : ∀ (f : ℝ → ℝ) (C : ℝ) (a b : ℝ), Measurable f → (∀ σ, ‖f σ‖ ≤ C) →
      IntervalIntegrable f volume a b := fun f C a b hf hC =>
    (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
      (Eventually.of_forall hC)
  -- `u²` and `‖Du‖²` are measurable, nonnegative and integrable on `B`
  have hmF₁ : Measurable fun y => u y ^ 2 := (hcont.pow 2).measurable
  have hmF₂ : Measurable fun y => ‖fderiv ℝ u y‖ ^ 2 := by fun_prop
  have hiF₁ : IntegrableOn (fun y => u y ^ 2) B := by
    refine Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2) hBfin
      hmF₁.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hBm] with y hy
    exact hsq_bd y (mem_ball_zero_iff.mp hy).le
  have hiF₂ : IntegrableOn (fun y => ‖fderiv ℝ u y‖ ^ 2) B :=
    Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2) hBfin hmF₂.aestronglyMeasurable
      (Eventually.of_forall hDsq_bd)
  -- the dilation averages `I₁(x) = ∫_{1/2}^1 u(tx)² dt` and `J(x) = ∫_{1/2}^1 ‖Du(tx)‖² dt`
  set I₁ : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2
  set J : Euclid n → ℝ := fun x => ∫ t in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (t • x)‖ ^ 2
  -- the pointwise estimate on a ray along which the fundamental theorem of calculus holds
  have key : ∀ x : Euclid n, ‖x‖ ≤ 1 →
      (∀ t : ℝ, u x - u (t • x) = ∫ σ in t..1, fderiv ℝ u (σ • x) x) →
      u x ^ 2 ≤ 4 * I₁ x + J x := by
    intro x hx hray
    have hgm : Measurable fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ := by fun_prop
    have hgi : ∀ a b : ℝ, IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖) volume a b :=
      fun a b => hii _ L a b hgm fun σ => by rw [norm_norm]; exact hDu _
    have hg2i : IntervalIntegrable (fun σ : ℝ => ‖fderiv ℝ u (σ • x)‖ ^ 2) volume (1 / 2) 1 :=
      hii _ ((L : ℝ) ^ 2) _ _ (hgm.pow_const 2) fun σ => hDsq_bd _
    set γ : ℝ := ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ with hγ
    -- (a) `|u(x) - u(tx)| ≤ ∫_t^1 ‖Du(σx)‖ dσ ≤ γ` for `t ∈ [1/2, 1]`
    have ha : ∀ t ∈ Icc (1 / 2 : ℝ) 1, |u x - u (t • x)| ≤ γ := by
      intro t ht
      rw [hray t, ← Real.norm_eq_abs]
      calc ‖∫ σ in t..1, fderiv ℝ u (σ • x) x‖
          ≤ ∫ σ in t..1, ‖fderiv ℝ u (σ • x)‖ :=
            intervalIntegral.norm_integral_le_of_norm_le ht.2
              (Eventually.of_forall fun σ _ => ((fderiv ℝ u (σ • x)).le_opNorm x).trans
                (mul_le_of_le_one_right (norm_nonneg _) hx)) (hgi t 1)
        _ ≤ γ := intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
              (Eventually.of_forall fun σ => norm_nonneg _) (hgi _ _)
    -- (b) `u(x)² ≤ 2u(tx)² + 2γ²`
    have hb : ∀ t ∈ Icc (1 / 2 : ℝ) 1, u x ^ 2 ≤ 2 * u (t • x) ^ 2 + 2 * γ ^ 2 := by
      intro t ht
      have h1 := abs_le.mp (ha t ht)
      have h2 : (u x - u (t • x)) ^ 2 ≤ γ ^ 2 := sq_le_sq' h1.1 h1.2
      linarith [sq_nonneg (2 * u (t • x) - u x)]
    -- (c) Cauchy–Schwarz on `[1/2, 1]`: integrating `4γ‖Du(σx)‖ ≤ ‖Du(σx)‖² + 4γ²` gives
    -- `4γ² ≤ J(x) + 2γ²`
    have hc : 2 * γ ^ 2 ≤ J x := by
      have h1 : ∫ σ in (1 / 2 : ℝ)..1, 4 * γ * ‖fderiv ℝ u (σ • x)‖ ≤
          ∫ σ in (1 / 2 : ℝ)..1, (‖fderiv ℝ u (σ • x)‖ ^ 2 + 4 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf ((hgi _ _).const_mul _)
          (hg2i.add intervalIntegrable_const)
          fun σ _ => by linarith [sq_nonneg (‖fderiv ℝ u (σ • x)‖ - 2 * γ)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hg2i
        intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, ← hγ] at h1
      have hJx : J x = ∫ σ in (1 / 2 : ℝ)..1, ‖fderiv ℝ u (σ • x)‖ ^ 2 := rfl
      linarith
    -- (d) averaging (b) over `t ∈ [1/2, 1]` gives `u(x)² ≤ 4I₁(x) + 2γ²`
    have hd : (1 - 1 / 2 : ℝ) * u x ^ 2 ≤ 2 * I₁ x + (1 - 1 / 2) * (2 * γ ^ 2) := by
      have hcu : Continuous fun t : ℝ => u (t • x) ^ 2 := by fun_prop
      have h1 : ∫ t in (1 / 2 : ℝ)..1, u x ^ 2 ≤
          ∫ t in (1 / 2 : ℝ)..1, (2 * u (t • x) ^ 2 + 2 * γ ^ 2) :=
        intervalIntegral.integral_mono_on hhalf intervalIntegrable_const
          (((hcu.intervalIntegrable _ _).const_mul 2).add intervalIntegrable_const) hb
      rw [intervalIntegral.integral_const, intervalIntegral.integral_add
        ((hcu.intervalIntegrable _ _).const_mul 2) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul,
        smul_eq_mul] at h1
      have hI₁x : I₁ x = ∫ t in (1 / 2 : ℝ)..1, u (t • x) ^ 2 := rfl
      linarith
    linarith
  -- `I₁` and `J` are strongly measurable (Fubini) and bounded on `B`, hence integrable on `A`
  have hI₁m : StronglyMeasurable I₁ := by
    have h : Measurable fun p : Euclid n × ℝ => u (p.2 • p.1) ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hJm : StronglyMeasurable J := by
    have h : Measurable fun p : Euclid n × ℝ => ‖fderiv ℝ u (p.2 • p.1)‖ ^ 2 := by fun_prop
    convert h.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (1 / 2 : ℝ) 1))
      using 1
    funext x
    exact intervalIntegral.integral_of_le hhalf
  have hI₁A : IntegrableOn I₁ A := by
    refine (Measure.integrableOn_of_bounded (M := (|u 0| + L) ^ 2 * |1 - 1 / 2|) hBfin
      hI₁m.aestronglyMeasurable ?_).mono_set sdiff_subset
    filter_upwards [ae_restrict_mem hBm] with x hx
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hsq_bd _ ?_
    rw [uIoc_of_le hhalf] at ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ht.1])]
    have hx1 : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
    nlinarith [ht.2, norm_nonneg x]
  have hJA : IntegrableOn J A :=
    (Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2 * |1 - 1 / 2|) hBfin
      hJm.aestronglyMeasurable (Eventually.of_forall fun x =>
        intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => hDsq_bd _)).mono_set
      sdiff_subset
  -- integrate the pointwise estimate over `A`
  have hae : ∀ᵐ x ∂(volume.restrict A), u x ^ 2 ≤ 4 * I₁ x + J x := by
    filter_upwards [ae_restrict_mem hAm,
      ae_restrict_of_ae (Submission.dorag_ha_rb_ray_ftc n u L hu)] with x hxA hray
    exact key x (mem_ball_zero_iff.mp hxA.1).le hray
  have hmain : ∫ x in A, u x ^ 2 ≤ ∫ x in A, (4 * I₁ x + J x) :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg (u x))
      ((hI₁A.const_mul 4).add hJA) hae
  rw [integral_add (hI₁A.const_mul 4) hJA, integral_const_mul] at hmain
  -- average over dilations, then `4 · 2^{n+1} = 2^{n+3}`
  have hdil₁ : ∫ x in A, I₁ x ≤ 2 ^ (n + 1) * s * ∫ y in B, u y ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => u y ^ 2) s hmF₁ (fun y => sq_nonneg _)
      hiF₁ hs hs2
  have hdil₂ : ∫ x in A, J x ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    Submission.dorag_ha_rb_dilation_average n (fun y => ‖fderiv ℝ u y‖ ^ 2) s hmF₂
      (fun y => sq_nonneg _) hiF₂ hs hs2
  have hJB : 0 ≤ 2 ^ (n + 1) * s * ∫ y in B, ‖fderiv ℝ u y‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hs.le) (setIntegral_nonneg hBm fun y _ => sq_nonneg _)
  have h2 : (2 : ℝ) ^ (n + 3) = 4 * 2 ^ (n + 1) := by ring
  rw [h2]
  linarith
/-- **Interior `L²` error of a mollification** (step (2a) of the Rellich ball argument): if
`u : ℝⁿ → ℝ` is Lipschitz, `ρ ≥ 0` is continuous, vanishes where `‖z‖ ≥ 1` and has `∫ ρ = 1`,
and `0 < ε ≤ s`, then `v(x) = ∫ u(x − εz) ρ(z) dz` satisfies
`∫_{B_{1−s}} (u − v)² ≤ ε² ∫_{B_1} ‖Du‖²`.  Weighted Jensen gives
`(u(x) − v(x))² ≤ ∫ (u(x) − u(x − εz))² ρ(z) dz`; the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
so Fubini swaps the integrals, and `Submission.dorag_ha_rb_translation_l2` (`r = 1 − s`, `R = 1`,
`w = εz`, `‖εz‖ ≤ ε ≤ s` where `ρ(z) ≠ 0`) bounds each inner integral by `ε² ∫_{B_1} ‖Du‖²`. -/
theorem Submission.dorag_ha_rb_mollify_l2 : ∀ (n : ℕ) (u ρ : Euclid n → ℝ) (L : NNReal) (ε s : ℝ), LipschitzWith L u → Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → 0 < ε → ε ≤ s → ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
  intro n u ρ L ε s hu hρc hρ0 hρ1 hρint hε hεs
  have huc : Continuous u := hu.continuous
  -- step 1: `ρ` vanishes off `closedBall 0 1`, so `g ρ` is integrable for every continuous `g`
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz =>
      hρ1 z (not_le.mp (by simpa using hz)).le
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  have hgρ : ∀ g : Euclid n → ℝ, Continuous g → Integrable fun z => g z * ρ z := fun g hg =>
    (hg.mul hρc).integrable_of_hasCompactSupport (hρcs.mul_left (f := g))
  -- step 2: `u(x) − v(x) = ∫ (u(x) − u(x − εz)) ρ(z) dz`, as `∫ ρ = 1`
  have hrep : ∀ x, u x - ∫ z, u (x - ε • z) * ρ z = ∫ z, (u x - u (x - ε • z)) * ρ z := by
    intro x
    simp_rw [sub_mul]
    rw [integral_sub (hρi.const_mul (u x)) (hgρ (fun z => u (x - ε • z)) (by fun_prop)),
      integral_const_mul, hρint, mul_one]
  -- step 3: weighted Jensen, `(∫ g ρ)² ≤ ∫ g² ρ`, from `0 ≤ ∫ (g − c)² ρ = ∫ g² ρ − c²`
  have hjensen : ∀ g : Euclid n → ℝ, Continuous g →
      (∫ z, g z * ρ z) ^ 2 ≤ ∫ z, g z ^ 2 * ρ z := by
    intro g hg
    obtain ⟨c, hc⟩ : ∃ c, ∫ z, g z * ρ z = c := ⟨_, rfl⟩
    have h0 : 0 ≤ ∫ z, (g z - c) ^ 2 * ρ z :=
      integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hρ0 z)
    have e : (fun z => (g z - c) ^ 2 * ρ z) =
        fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) + c ^ 2 * ρ z := by
      funext z
      ring
    have i1 : Integrable fun z => g z ^ 2 * ρ z := hgρ (fun z => g z ^ 2) (hg.pow 2)
    have i2 : Integrable fun z => 2 * c * (g z * ρ z) := (hgρ g hg).const_mul (2 * c)
    have i3 : Integrable fun z => g z ^ 2 * ρ z - 2 * c * (g z * ρ z) := i1.sub i2
    rw [e, integral_add i3 (hρi.const_mul (c ^ 2)), integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hc, hρint] at h0
    rw [hc]
    nlinarith
  -- step 4: `|u(x) − u(x − εz)| ≤ Lε‖z‖`, so the integrand is dominated by `(Lε‖z‖)² ρ(z)`,
  -- which is integrable on `B_{1−s} × ℝⁿ`
  have hlip : ∀ x z : Euclid n, |u x - u (x - ε • z)| ≤ L * (ε * ‖z‖) := by
    intro x z
    have h := hu.dist_le_mul x (x - ε • z)
    rwa [Real.dist_eq, dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_of_nonneg hε.le] at h
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) (1 - s))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : Integrable (uncurry fun x z => (u x - u (x - ε • z)) ^ 2 * ρ z)
      ((volume.restrict (ball (0 : Euclid n) (1 - s))).prod volume) := by
    refine ((hgρ (fun z => (L * (ε * ‖z‖)) ^ 2) (by fun_prop)).comp_snd
      (volume.restrict (ball (0 : Euclid n) (1 - s)))).mono'
      (show Continuous fun p : Euclid n × Euclid n => (u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2
        by fun_prop).aestronglyMeasurable (ae_of_all _ fun p => ?_)
    show ‖(u p.1 - u (p.1 - ε • p.2)) ^ 2 * ρ p.2‖ ≤ (L * (ε * ‖p.2‖)) ^ 2 * ρ p.2
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ0 _))]
    exact mul_le_mul_of_nonneg_right (sq_le_sq.2 ((hlip _ _).trans (le_abs_self _))) (hρ0 _)
  -- step 5: Jensen pointwise, then Fubini; step 6: the translation estimate for `‖z‖ < 1`
  -- (`ρ(z) = 0` otherwise); step 7: `∫ ρ = 1`
  calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2
      ≤ ∫ x in ball (0 : Euclid n) (1 - s), ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          hint.integral_prod_left (ae_of_all _ fun x => ?_)
        show (u x - ∫ z, u (x - ε • z) * ρ z) ^ 2 ≤ ∫ z, (u x - u (x - ε • z)) ^ 2 * ρ z
        rw [hrep x]
        exact hjensen (fun z => u x - u (x - ε • z)) (by fun_prop)
    _ = ∫ z, ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z :=
        integral_integral_swap hint
    _ ≤ ∫ z, ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z := by
        refine integral_mono hint.integral_prod_right (hρi.const_mul _) fun z => ?_
        show ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2 * ρ z ≤
          ε ^ 2 * (∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2) * ρ z
        rw [integral_mul_const]
        rcases le_or_gt 1 ‖z‖ with hz | hz
        · simp [hρ1 z hz]
        have hw : ‖ε • z‖ ≤ ε := by
          rw [norm_smul, Real.norm_of_nonneg hε.le]
          exact mul_le_of_le_one_right hε.le hz.le
        refine mul_le_mul_of_nonneg_right ?_ (hρ0 z)
        calc ∫ x in ball (0 : Euclid n) (1 - s), (u x - u (x - ε • z)) ^ 2
            ≤ ‖ε • z‖ ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              Submission.dorag_ha_rb_translation_l2 n u L (ε • z) (1 - s) 1 hu (by linarith)
          _ ≤ ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hw 2)
                (integral_nonneg fun x => sq_nonneg _)
    _ = ε ^ 2 * ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ u x‖ ^ 2 := by
        rw [integral_const_mul, hρint, mul_one]
/-- **Uniform bounds for mollifications** (Rellich compactness step of the harmonic approximation
lemma, Simon 5.3.1–5.3.4).  Let `ρ` be continuous, zero for `‖z‖ ≥ 1`, bounded by `C` and
`C`-Lipschitz, `0 < ε ≤ s / 2`, and `v(x) = ∫ u(x − εz)ρ(z) dz`.  On `K = closedBall(0, 1 − s)`
we have `|v| ≤ ε⁻ⁿC∫_{B₁(0)}|u|` and `v` is `ε⁻⁽ⁿ⁺¹⁾C∫_{B₁(0)}|u|`-Lipschitz.  Substituting
`y = x − εz` gives `v(x) = ε⁻ⁿ∫ u(y)ρ(ε⁻¹(x − y)) dy`, and for `x ∈ K`, `‖y‖ ≥ 1` we have
`‖x − y‖ ≥ s ≥ ε`, so the integrand vanishes off `B₁(0)`; the bounds follow from `|ρ| ≤ C` and
`|ρ(ε⁻¹(x − y)) − ρ(ε⁻¹(x' − y))| ≤ Cε⁻¹‖x − x'‖`. -/
theorem Submission.dorag_ha_rb_mollify_bounds : ∀ (n : ℕ) (u ρ : Euclid n → ℝ) (C ε s : ℝ), Continuous u → Continuous ρ → (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) → (∀ z, |ρ z| ≤ C) → (∀ z z', |ρ z - ρ z'| ≤ C * ‖z - z'‖) → 0 < ε → ε ≤ s / 2 → (∀ x ∈ closedBall (0 : Euclid n) (1 - s), |∫ z, u (x - ε • z) * ρ z| ≤ (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u y|) ∧ ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ x' ∈ closedBall (0 : Euclid n) (1 - s), |(∫ z, u (x - ε • z) * ρ z) - ∫ z, u (x' - ε • z) * ρ z| ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u y| := by
  intro n u ρ C ε s hu hρ hsupp hbd hlip hε hεs
  have hεn : 0 < (ε ^ n)⁻¹ := inv_pos.mpr (pow_pos hε n)
  -- (1) support: for `x ∈ K` and `y ∉ B₁(0)`, `‖ε⁻¹(x − y)‖ ≥ 1`, so `ρ(ε⁻¹(x − y)) = 0`
  have hzero : ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ y ∉ ball (0 : Euclid n) 1,
      ρ (ε⁻¹ • (x - y)) = 0 := by
    intro x hx y hy
    rw [mem_closedBall_zero_iff] at hx
    rw [mem_ball_zero_iff, not_lt] at hy
    apply hsupp
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le), one_le_inv_mul₀ hε]
    calc ε ≤ ‖y‖ - ‖x‖ := by linarith
      _ ≤ ‖y - x‖ := norm_sub_norm_le _ _
      _ = ‖x - y‖ := norm_sub_rev _ _
  -- (2) continuous functions are integrable on `B₁(0)`
  have hint : ∀ f : Euclid n → ℝ, Continuous f → IntegrableOn f (ball (0 : Euclid n) 1) :=
    fun f hf => (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  have hcf : ∀ x : Euclid n, Continuous fun y => u y * ρ (ε⁻¹ • (x - y)) := fun x =>
    hu.mul (hρ.comp ((continuous_const.sub continuous_id).const_smul ε⁻¹))
  -- (3) change of variables `y = x − εz`: `v(x) = ε⁻ⁿ∫_{B₁(0)} u(y)ρ(ε⁻¹(x − y)) dy`
  have hcov : ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∫ z, u (x - ε • z) * ρ z =
      (ε ^ n)⁻¹ * ∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y)) := by
    intro x hx
    have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euclid n))
      (fun w => u (x - w) * ρ (ε⁻¹ • w)) ε (hR := hε.le)
    simp only [inv_smul_smul₀ hε.ne', finrank_euclideanSpace_fin, smul_eq_mul] at h1
    rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [hzero x hx y hy, mul_zero]]
    congr 1
    simpa only [sub_sub_cancel] using
      integral_sub_left_eq_self (fun y => u y * ρ (ε⁻¹ • (x - y))) volume x
  refine ⟨fun x hx => ?_, fun x hx x' hx' => ?_⟩
  -- (4) sup bound from `|ρ| ≤ C`
  · have hb : |∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))| ≤
        ∫ y in ball (0 : Euclid n) 1, |u y| * C := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hint _ hu.abs).mul_const C)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hbd _) (abs_nonneg _)
    rw [integral_mul_const] at hb
    rw [hcov x hx, abs_mul, abs_of_pos hεn]
    calc (ε ^ n)⁻¹ * |∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))|
        ≤ (ε ^ n)⁻¹ * ((∫ y in ball (0 : Euclid n) 1, |u y|) * C) :=
          mul_le_mul_of_nonneg_left hb hεn.le
      _ = (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u y| := by ring
  -- (5) Lipschitz bound from `|ρ(ε⁻¹(x − y)) − ρ(ε⁻¹(x' − y))| ≤ Cε⁻¹‖x − x'‖`
  · have hb : |∫ y in ball (0 : Euclid n) 1,
          (u y * ρ (ε⁻¹ • (x - y)) - u y * ρ (ε⁻¹ • (x' - y)))| ≤
        ∫ y in ball (0 : Euclid n) 1, |u y| * (C * ε⁻¹ * ‖x - x'‖) := by
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le ((hint _ hu.abs).mul_const _)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      calc |ρ (ε⁻¹ • (x - y)) - ρ (ε⁻¹ • (x' - y))|
          ≤ C * ‖ε⁻¹ • (x - y) - ε⁻¹ • (x' - y)‖ := hlip _ _
        _ = C * ε⁻¹ * ‖x - x'‖ := by
          rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul,
            Real.norm_of_nonneg (inv_nonneg.mpr hε.le), mul_assoc]
    rw [integral_mul_const, integral_sub (hint _ (hcf x)) (hint _ (hcf x'))] at hb
    rw [hcov x hx, hcov x' hx', ← mul_sub, abs_mul, abs_of_pos hεn]
    calc (ε ^ n)⁻¹ * |(∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x - y))) -
          ∫ y in ball (0 : Euclid n) 1, u y * ρ (ε⁻¹ • (x' - y))|
        ≤ (ε ^ n)⁻¹ * ((∫ y in ball (0 : Euclid n) 1, |u y|) * (C * ε⁻¹ * ‖x - x'‖)) :=
          mul_le_mul_of_nonneg_left hb hεn.le
      _ = (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u y| := by
          rw [pow_succ, mul_inv]
          ring
/-- **Mollifier kernel** for the Rellich compactness step of the harmonic approximation lemma
(Simon 5.3.1–5.3.4): a continuous probability density `ρ ≥ 0` on `ℝⁿ`, vanishing for `‖z‖ ≥ 1`,
bounded by `C` and `C`-Lipschitz.  Take the tent `ρ₀(z) = (1 − ‖z‖)₊`, which is continuous, `0 ≤ ρ₀ ≤ 1`, zero off
`B_1(0)` and `1`-Lipschitz; `c₀ = ∫ ρ₀ > 0` since `ρ₀` is compactly supported, nonnegative and
`ρ₀(0) = 1`; then `ρ = c₀⁻¹ρ₀` and `C = c₀⁻¹`. -/
theorem Submission.dorag_ha_rb_kernel : ∀ (n : ℕ), ∃ (ρ : Euclid n → ℝ) (C : ℝ), Continuous ρ ∧ (∀ z, 0 ≤ ρ z) ∧ (∀ z : Euclid n, 1 ≤ ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 ∧ (∀ z, |ρ z| ≤ C) ∧ ∀ z z', |ρ z - ρ z'| ≤ C * ‖z - z'‖ := by
  intro n
  -- the tent `ρ₀(z) = (1 − ‖z‖)₊`: continuous, `0 ≤ ρ₀ ≤ 1`, zero off `B_1(0)`, `1`-Lipschitz
  set ρ₀ : Euclid n → ℝ := fun z => max (1 - ‖z‖) 0 with hρ₀
  have hcont : Continuous ρ₀ := (continuous_const.sub continuous_norm).max continuous_const
  have hnonneg : ∀ z, 0 ≤ ρ₀ z := fun z => le_max_right _ _
  have hle : ∀ z, ρ₀ z ≤ 1 := fun z => max_le (by linarith [norm_nonneg z]) zero_le_one
  have hvanish : ∀ z : Euclid n, 1 ≤ ‖z‖ → ρ₀ z = 0 := fun z hz => max_eq_right (by linarith)
  have hlip : ∀ z z', |ρ₀ z - ρ₀ z'| ≤ ‖z - z'‖ := fun z z' =>
    calc |ρ₀ z - ρ₀ z'| ≤ |(1 - ‖z‖) - (1 - ‖z'‖)| := abs_max_sub_max_le_abs _ _ _
      _ = |‖z'‖ - ‖z‖| := by ring_nf
      _ ≤ ‖z' - z‖ := abs_norm_sub_norm_le _ _
      _ = ‖z - z'‖ := norm_sub_rev _ _
  -- `c₀ = ∫ ρ₀ > 0`: `ρ₀` is continuous, compactly supported, nonnegative and `ρ₀(0) = 1`
  have hsupp : HasCompactSupport ρ₀ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz =>
      hvanish z (by simpa using (not_le.mp (by simpa using hz)).le)
  have hpos : 0 < ∫ z, ρ₀ z :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg (x := 0) (by simp [hρ₀])
  -- `ρ = c₀⁻¹ ρ₀` and `C = c₀⁻¹`
  have hC : 0 ≤ (∫ z, ρ₀ z)⁻¹ := inv_nonneg.mpr hpos.le
  refine ⟨fun z => (∫ z, ρ₀ z)⁻¹ * ρ₀ z, (∫ z, ρ₀ z)⁻¹, continuous_const.mul hcont,
    fun z => mul_nonneg hC (hnonneg z), fun z hz => by simp [hvanish z hz], ?_, fun z => ?_,
    fun z z' => ?_⟩
  · rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'
  · rw [abs_of_nonneg (mul_nonneg hC (hnonneg z))]
    exact mul_le_of_le_one_right hC (hle z)
  · rw [← mul_sub, abs_mul, abs_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left (hlip z z') hC
/-- **Finite sup-norm nets** (the total-boundedness half of Arzelà–Ascoli, i.e. the Arzelà–Ascoli
step of the Rellich compactness argument behind the harmonic approximation lemma, Simon Ch. 5).
If the `g j` are bounded by `C` and `C`-Lipschitz on the compact set `K`, then for every `δ > 0`
there is a finite set `S` of indices such that every `g j` is `δ`-close on `K` to some `g k`,
`k ∈ S`.  With `C' = max C 0 + 1` and `r = δ / (3C')`, cover `K` by finitely many `r`-balls
centred in `T ⊆ K`; the vectors `(g j y)_{y ∈ T}` lie in a compact ball of `T → ℝ`, so finitely
many of them form a `δ/3`-net; then `|g j x − g k x| ≤ C'r + δ/3 + C'r = δ`. -/
theorem Submission.dorag_ha_rb_sup_net : ∀ (n : ℕ) (K : Set (Euclid n)) (g : ℕ → Euclid n → ℝ) (C : ℝ), IsCompact K → (∀ j, ∀ x ∈ K, |g j x| ≤ C) → (∀ j, ∀ x ∈ K, ∀ y ∈ K, |g j x - g j y| ≤ C * ‖x - y‖) → ∀ δ : ℝ, 0 < δ → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∀ x ∈ K, |g j x - g k x| ≤ δ := by
  intro n K g C hK hbd hlip δ hδ
  -- Step 1: `C' = max C 0 + 1`, `r = δ / (3C')`, and finitely many `r`-balls centred in `T ⊆ K`
  -- cover `K`
  obtain ⟨C', hC'pos, hCC'⟩ : ∃ C' : ℝ, 0 < C' ∧ C ≤ C' :=
    ⟨max C 0 + 1, by linarith [le_max_right C 0], by linarith [le_max_left C 0]⟩
  have hr : 0 < δ / (3 * C') := div_pos hδ (mul_pos three_pos hC'pos)
  have hC'r : C' * (δ / (3 * C')) = δ / 3 := by
    field_simp
  obtain ⟨T, hTK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (δ / (3 * C'))) (fun x _ => ball_mem_nhds x hr)
  -- Step 2: the evaluation vectors `Φ j = (g j y)_{y ∈ T}` lie in a compact ball of `T → ℝ`
  let Φ : ℕ → T → ℝ := fun j y => g j y
  have hrange : range Φ ⊆ closedBall 0 C' := by
    rintro _ ⟨j, rfl⟩
    rw [mem_closedBall, dist_pi_le_iff hC'pos.le]
    intro y
    rw [Pi.zero_apply, Real.dist_eq, sub_zero]
    exact (hbd j y (hTK y y.2)).trans hCC'
  have htb : TotallyBounded (range Φ) :=
    (isCompact_closedBall (0 : T → ℝ) C').totallyBounded.subset hrange
  -- Step 3: a finite `δ/3`-net `t ⊆ range Φ`; each `q ∈ t` is `Φ (invFun Φ q)`
  obtain ⟨t, htΦ, htfin, htcover⟩ :=
    finite_approx_of_totallyBounded htb (δ / 3) (div_pos hδ three_pos)
  refine ⟨htfin.toFinset.image (Function.invFun Φ), fun j => ?_⟩
  -- Step 4: `Φ j` is `δ/3`-close to some `q = Φ k ∈ t`, so `|g j - g k| < δ/3` on `T`
  obtain ⟨q, hqt, hjq⟩ := mem_iUnion₂.1 (htcover (mem_range_self j))
  refine ⟨Function.invFun Φ q, Finset.mem_image_of_mem _ (htfin.mem_toFinset.2 hqt), ?_⟩
  have hkq : Φ (Function.invFun Φ q) = q := Function.invFun_eq (htΦ hqt)
  have hT : ∀ y ∈ T, |g j y - g (Function.invFun Φ q) y| < δ / 3 := fun y hy =>
    calc |g j y - g (Function.invFun Φ q) y|
        = dist (Φ j ⟨y, hy⟩) (Φ (Function.invFun Φ q) ⟨y, hy⟩) := rfl
      _ ≤ dist (Φ j) (Φ (Function.invFun Φ q)) :=
        dist_le_pi_dist (Φ j) (Φ (Function.invFun Φ q)) ⟨y, hy⟩
      _ = dist (Φ j) q := by rw [hkq]
      _ < δ / 3 := hjq
  -- Step 5: the three-term estimate through a centre `y ∈ T` with `‖x - y‖ < r`
  intro x hx
  obtain ⟨y, hyT, hxy⟩ := mem_iUnion₂.1 (hcover hx)
  have hyK : y ∈ K := hTK y hyT
  have hxy' : ‖x - y‖ < δ / (3 * C') := by
    rw [← dist_eq_norm]
    exact hxy
  have hCr : C * ‖x - y‖ ≤ δ / 3 :=
    calc C * ‖x - y‖ ≤ C' * ‖x - y‖ := mul_le_mul_of_nonneg_right hCC' (norm_nonneg _)
      _ ≤ C' * (δ / (3 * C')) := mul_le_mul_of_nonneg_left hxy'.le hC'pos.le
      _ = δ / 3 := hC'r
  have h1 := hlip j x hx y hyK
  have h2 := hT y hyT
  have h3 := hlip (Function.invFun Φ q) y hyK x hx
  rw [norm_sub_rev] at h3
  calc |g j x - g (Function.invFun Φ q) x|
      ≤ |g j x - g j y| + |g j y - g (Function.invFun Φ q) x| := abs_sub_le _ _ _
    _ ≤ |g j x - g j y| +
          (|g j y - g (Function.invFun Φ q) y| +
            |g (Function.invFun Φ q) y - g (Function.invFun Φ q) x|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ δ := by linarith
/-- **Rellich on `B̆₁(0)`, total boundedness** (parent proof, step 4).  Let the `uⱼ` be Lipschitz
on `ℝⁿ` with `∫_B uⱼ² ≤ M` and `∫_B ‖Duⱼ‖² ≤ M`, `B = B̆₁(0)`.  Then for every `η > 0` finitely
many `uₖ` form an `η`-net for `∫_B (uⱼ − uₖ)²`.  Choose `s`, `ε ≤ s/2`, `δ` with `2^{n+6}sM`,
`6ε²M`, `3δ²Lⁿ(B) ≤ η/3` and mollify, `vⱼ(x) = ∫ uⱼ(x − εz)ρ(z) dz` with the kernel of
`dorag_ha_rb_kernel`.  As `∫_B |uⱼ| ≤ (Lⁿ(B) + M)/2` (`|a| ≤ (1 + a²)/2`), the `vⱼ` are uniformly
bounded and uniformly Lipschitz on `B_{1−s}(0)` (`dorag_ha_rb_mollify_bounds`), so finitely many
`vₖ` are a `δ`-net in the sup norm there (`dorag_ha_rb_sup_net`).  On `B \ B̆_{1−s}(0)` use
`(a − b)² ≤ 2a² + 2b²` and `dorag_ha_rb_boundary_layer`; on `B̆_{1−s}(0)` use
`(a + b + c)² ≤ 3(a² + b² + c²)` and `dorag_ha_rb_mollify_l2`. -/
theorem Submission.dorag_ha_rb_total_bounded : ∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x in ball (0 : Euclid n) 1, (u j x - u k x) ^ 2 ≤ η := by
  intro n M u hLip hu hDu η hη
  choose L hL using hLip
  have hc : ∀ j, Continuous (u j) := fun j => (hL j).continuous
  -- a function continuous on `B_r(0)` is integrable on `B̆_r(0)`
  have hint : ∀ (f : Euclid n → ℝ) (r : ℝ), ContinuousOn f (closedBall 0 r) →
      IntegrableOn f (ball 0 r) := fun f r hf =>
    (hf.integrableOn_compact (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hM : 0 ≤ M := (integral_nonneg fun x => sq_nonneg (u 0 x)).trans (hu 0)
  obtain ⟨ω, hω⟩ : ∃ ω : ℝ, ω = volume.real (ball (0 : Euclid n) 1) := ⟨_, rfl⟩
  have hω0 : 0 ≤ ω := by rw [hω]; exact measureReal_nonneg
  -- Step 1: the constants `s`, `ε ≤ s/2` and `δ`
  obtain ⟨s, hs0, hs1, hsη⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ s * (3 * 2 ^ (n + 6) * (M + 1)) ≤ η :=
    ⟨min (1 / 2) (η / (3 * 2 ^ (n + 6) * (M + 1))), lt_min (by norm_num) (by positivity),
      min_le_left _ _, (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  obtain ⟨ε, hε0, hεs2, hεη⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ s / 2 ∧ ε * (18 * (M + 1)) ≤ η :=
    ⟨min (s / 2) (η / (18 * (M + 1))), lt_min (by positivity) (by positivity), min_le_left _ _,
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  obtain ⟨δ, hδ0, hδ1, hδη⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ δ * (9 * (ω + 1)) ≤ η :=
    ⟨min 1 (η / (9 * (ω + 1))), lt_min one_pos (by positivity), min_le_left _ _,
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)⟩
  have hεs : ε ≤ s := by linarith
  have hε2 : ε ^ 2 ≤ ε := by rw [sq]; exact mul_le_of_le_one_left hε0.le (by linarith)
  have hδ2 : δ ^ 2 ≤ δ := by rw [sq]; exact mul_le_of_le_one_left hδ0.le hδ1
  -- Step 2: the mollifications `vⱼ(x) = ∫ uⱼ(x − εz)ρ(z) dz`
  obtain ⟨ρ, C, hρc, hρ0, hρ1, hρint, hρC, hρL⟩ := Submission.dorag_ha_rb_kernel n
  have hC : 0 ≤ C := (abs_nonneg _).trans (hρC 0)
  set v : ℕ → Euclid n → ℝ := fun j x => ∫ z, u j (x - ε • z) * ρ z
  -- Step 3: `∫_B |uⱼ| ≤ (Lⁿ(B) + M)/2`
  have hL1 : ∀ j, ∫ x in ball (0 : Euclid n) 1, |u j x| ≤ (ω + M) / 2 := by
    intro j
    have i1 : IntegrableOn (fun _ => (1 / 2 : ℝ)) (ball (0 : Euclid n) 1) := integrableOn_const
    have i2 : IntegrableOn (fun x => u j x ^ 2 / 2) (ball (0 : Euclid n) 1) :=
      (hint _ 1 ((hc j).pow 2).continuousOn).div_const 2
    have i12 : IntegrableOn (fun x => 1 / 2 + u j x ^ 2 / 2) (ball (0 : Euclid n) 1) := i1.add i2
    calc ∫ x in ball (0 : Euclid n) 1, |u j x|
        ≤ ∫ x in ball (0 : Euclid n) 1, (1 / 2 + u j x ^ 2 / 2) :=
          setIntegral_mono_on (hint _ 1 (hc j).abs.continuousOn) i12 measurableSet_ball
            fun x _ => by linarith [sq_abs (u j x), sq_nonneg (|u j x| - 1)]
      _ = ω / 2 + (∫ x in ball (0 : Euclid n) 1, u j x ^ 2) / 2 := by
          rw [integral_add i1 i2, setIntegral_const, integral_div, smul_eq_mul, hω]
          ring
      _ ≤ (ω + M) / 2 := by linarith [hu j]
  -- Step 4: the `vⱼ` are uniformly bounded and uniformly Lipschitz on `B_{1−s}(0)`
  set D : ℝ := (ε ^ n)⁻¹ * C * ((ω + M) / 2) + (ε ^ (n + 1))⁻¹ * C * ((ω + M) / 2)
  have hvb : ∀ j, ∀ x ∈ closedBall (0 : Euclid n) (1 - s), |v j x| ≤ D := by
    intro j x hx
    calc |v j x| ≤ (ε ^ n)⁻¹ * C * ∫ y in ball (0 : Euclid n) 1, |u j y| :=
          (Submission.dorag_ha_rb_mollify_bounds n (u j) ρ C ε s (hc j) hρc hρ1 hρC hρL hε0
            hεs2).1 x hx
      _ ≤ (ε ^ n)⁻¹ * C * ((ω + M) / 2) := mul_le_mul_of_nonneg_left (hL1 j) (by positivity)
      _ ≤ D := le_add_of_nonneg_right (by positivity)
  have hvl : ∀ j, ∀ x ∈ closedBall (0 : Euclid n) (1 - s), ∀ x' ∈ closedBall (0 : Euclid n) (1 - s),
      |v j x - v j x'| ≤ D * ‖x - x'‖ := by
    intro j x hx x' hx'
    calc |v j x - v j x'|
        ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ∫ y in ball (0 : Euclid n) 1, |u j y| :=
          (Submission.dorag_ha_rb_mollify_bounds n (u j) ρ C ε s (hc j) hρc hρ1 hρC hρL hε0
            hεs2).2 x hx x' hx'
      _ ≤ (ε ^ (n + 1))⁻¹ * C * ‖x - x'‖ * ((ω + M) / 2) :=
          mul_le_mul_of_nonneg_left (hL1 j) (by positivity)
      _ = (ε ^ (n + 1))⁻¹ * C * ((ω + M) / 2) * ‖x - x'‖ := by ring
      _ ≤ D * ‖x - x'‖ :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (norm_nonneg _)
  have hvc : ∀ j, ContinuousOn (v j) (closedBall (0 : Euclid n) (1 - s)) := by
    intro j
    refine (LipschitzOnWith.of_dist_le' (f := v j) (s := closedBall (0 : Euclid n) (1 - s))
      (K := D) fun x hx x' hx' => ?_).continuousOn
    rw [Real.dist_eq, dist_eq_norm]
    exact hvl j x hx x' hx'
  -- Step 5: finitely many `vₖ` form a `δ`-net in the sup norm on `B_{1−s}(0)`
  obtain ⟨S, hS⟩ := Submission.dorag_ha_rb_sup_net n (closedBall (0 : Euclid n) (1 - s)) v D
    (isCompact_closedBall 0 (1 - s)) hvb hvl δ hδ0
  refine ⟨S, fun j => ?_⟩
  obtain ⟨k, hkS, hjk⟩ := hS j
  refine ⟨k, hkS, ?_⟩
  -- Step 6: split `B` into `B̆_{1−s}(0)` and the annulus `B \ B̆_{1−s}(0)`
  have hsub : ball (0 : Euclid n) (1 - s) ⊆ ball 0 1 := ball_subset_ball (by linarith)
  have ijk : IntegrableOn (fun x => (u j x - u k x) ^ 2) (ball (0 : Euclid n) 1) :=
    hint _ 1 (((hc j).sub (hc k)).pow 2).continuousOn
  have hsplit := setIntegral_sdiff measurableSet_ball ijk hsub
  -- Step 7: the annulus, by `dorag_ha_rb_boundary_layer`
  have hann : ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (u j x - u k x) ^ 2 ≤ η / 3 := by
    have iA : ∀ i, IntegrableOn (fun x => 2 * u i x ^ 2) (ball (0 : Euclid n) 1 \ ball 0 (1 - s)) :=
      fun i => ((hint _ 1 ((hc i).pow 2).continuousOn).mono_set sdiff_subset).const_mul 2
    have iAA : IntegrableOn (fun x => 2 * u j x ^ 2 + 2 * u k x ^ 2)
        (ball (0 : Euclid n) 1 \ ball 0 (1 - s)) := (iA j).add (iA k)
    have hbl : ∀ i, ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u i x ^ 2 ≤
        2 ^ (n + 3) * s * (M + M) := fun i =>
      (Submission.dorag_ha_rb_boundary_layer n (u i) (L i) s (hL i) hs0 hs1).trans
        (mul_le_mul_of_nonneg_left (add_le_add (hu i) (hDu i)) (by positivity))
    calc ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (u j x - u k x) ^ 2
        ≤ ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), (2 * u j x ^ 2 + 2 * u k x ^ 2) :=
          setIntegral_mono_on (ijk.mono_set sdiff_subset) iAA
            (measurableSet_ball.diff measurableSet_ball) fun x _ => by
              linarith [sq_nonneg (u j x + u k x)]
      _ = 2 * (∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u j x ^ 2) +
            2 * ∫ x in ball (0 : Euclid n) 1 \ ball 0 (1 - s), u k x ^ 2 := by
          rw [integral_add (iA j) (iA k), integral_const_mul, integral_const_mul]
      _ ≤ 2 * (2 ^ (n + 3) * s * (M + M)) + 2 * (2 ^ (n + 3) * s * (M + M)) := by
          linarith [hbl j, hbl k]
      _ = 2 ^ (n + 6) * s * M := by ring
      _ ≤ η / 3 := by
          have : 0 < 2 ^ (n + 6) * s := by positivity
          linarith
  -- Step 8: the interior, by `dorag_ha_rb_mollify_l2` and the sup-net
  have hin : ∫ x in ball (0 : Euclid n) (1 - s), (u j x - u k x) ^ 2 ≤ 2 * η / 3 := by
    have i1 : ∀ i, IntegrableOn (fun x => 3 * (u i x - v i x) ^ 2) (ball (0 : Euclid n) (1 - s)) :=
      fun i => (hint _ _ (((hc i).continuousOn.sub (hvc i)).pow 2)).const_mul 3
    have i2 : IntegrableOn (fun _ => 3 * δ ^ 2) (ball (0 : Euclid n) (1 - s)) := integrableOn_const
    have i12 : IntegrableOn (fun x => 3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2)
        (ball (0 : Euclid n) (1 - s)) := (i1 j).add i2
    have i123 : IntegrableOn
        (fun x => 3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2 + 3 * (u k x - v k x) ^ 2)
        (ball (0 : Euclid n) (1 - s)) := i12.add (i1 k)
    have hl2 : ∀ i, ∫ x in ball (0 : Euclid n) (1 - s), (u i x - v i x) ^ 2 ≤ ε ^ 2 * M := fun i =>
      (Submission.dorag_ha_rb_mollify_l2 n (u i) ρ (L i) ε s (hL i) hρc hρ0 hρ1 hρint hε0
        hεs).trans (mul_le_mul_of_nonneg_left (hDu i) (sq_nonneg ε))
    have hvol : volume.real (ball (0 : Euclid n) (1 - s)) ≤ ω := by
      rw [hω]; exact measureReal_mono hsub
    calc ∫ x in ball (0 : Euclid n) (1 - s), (u j x - u k x) ^ 2
        ≤ ∫ x in ball (0 : Euclid n) (1 - s),
            (3 * (u j x - v j x) ^ 2 + 3 * δ ^ 2 + 3 * (u k x - v k x) ^ 2) := by
          refine setIntegral_mono_on (ijk.mono_set hsub) i123 measurableSet_ball fun x hx => ?_
          have h1 := abs_le.mp (hjk x (ball_subset_closedBall hx))
          have h2 : (v j x - v k x) ^ 2 ≤ δ ^ 2 := sq_le_sq' h1.1 h1.2
          linarith [sq_nonneg (u j x - v j x - (v j x - v k x)),
            sq_nonneg (v j x - v k x - (v k x - u k x)),
            sq_nonneg (u j x - v j x - (v k x - u k x))]
      _ = 3 * (∫ x in ball (0 : Euclid n) (1 - s), (u j x - v j x) ^ 2) +
            3 * δ ^ 2 * volume.real (ball (0 : Euclid n) (1 - s)) +
            3 * ∫ x in ball (0 : Euclid n) (1 - s), (u k x - v k x) ^ 2 := by
          rw [integral_add i12 (i1 k), integral_add (i1 j) i2, setIntegral_const,
            integral_const_mul, integral_const_mul, smul_eq_mul]
          ring
      _ ≤ 3 * (ε ^ 2 * M) + 3 * δ ^ 2 * ω + 3 * (ε ^ 2 * M) := by
          have := mul_le_mul_of_nonneg_left hvol (by positivity : (0 : ℝ) ≤ 3 * δ ^ 2)
          linarith [hl2 j, hl2 k]
      _ ≤ 2 * η / 3 := by
          linarith [mul_le_mul_of_nonneg_right hε2 hM, mul_le_mul_of_nonneg_right hδ2 hω0]
  linarith
/-- Extraction step of the Rellich argument (step 5 of its proof).  If `f j ∈ L²(μ)` and for every
`η > 0` finitely many `f k` form an `η`-net for `∫ (f j - f k) ^ 2`, then a subsequence converges
in `L²(μ)`: the classes of the `f j` form a totally bounded set in the complete space `L²(μ)`. -/
theorem Submission.dorag_ha_rb_l2_subseq : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : ℕ → α → ℝ), (∀ j, MemLp (f j) 2 μ) → (∀ η : ℝ, 0 < η → ∃ S : Finset ℕ, ∀ j, ∃ k ∈ S, ∫ x, (f j x - f k x) ^ 2 ∂μ ≤ η) → ∃ (φ : ℕ → ℕ) (W : α → ℝ), StrictMono φ ∧ MemLp W 2 μ ∧ Tendsto (fun j => ∫ x, (f (φ j) x - W x) ^ 2 ∂μ) atTop (𝓝 0) := by
  intro α _ μ f hf hnet
  -- Step 2: for `h ∈ L²`, `‖toLp h‖ ^ 2 = ∫ h ^ 2`
  have hnorm : ∀ (h : α → ℝ) (hh : MemLp h 2 μ), ‖hh.toLp h‖ ^ 2 = ∫ x, h x ^ 2 ∂μ := by
    intro h hh
    have h0 : 0 ≤ ∫ x, h x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (h x)
    rw [Lp.norm_toLp, hh.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast, ← Real.rpow_mul h0]
    norm_num
  -- Step 1: the classes `F j ∈ L²`, with `dist (F j) (F k) ^ 2 = ∫ (f j - f k) ^ 2`
  set F : ℕ → Lp ℝ 2 μ := fun j => (hf j).toLp (f j) with hF
  have hdist : ∀ j k, dist (F j) (F k) ^ 2 = ∫ x, (f j x - f k x) ^ 2 ∂μ := by
    intro j k
    rw [dist_eq_norm, hF, ← MemLp.toLp_sub (hf j) (hf k)]
    exact hnorm _ _
  -- Step 3: the hypothesis with `η = ε ^ 2 / 2` gives a finite `ε`-net of `range F`
  have htb : TotallyBounded (range F) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨S, hS⟩ := hnet (ε ^ 2 / 2) (by positivity)
    refine ⟨F '' (S : Set ℕ), S.finite_toSet.image F, ?_⟩
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk, hjk⟩ := hS j
    refine mem_iUnion₂.2 ⟨F k, mem_image_of_mem F hk, ?_⟩
    rw [mem_ball]
    refine lt_of_pow_lt_pow_left₀ 2 hε.le ?_
    rw [hdist]
    have : 0 < ε ^ 2 := by positivity
    linarith
  -- Steps 4–5: `closure (range F)` is compact in the complete space `L²`, so a subsequence
  -- `F ∘ φ` converges to some `G`
  obtain ⟨G, -, φ, hφ, hlim⟩ :=
    (htb.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
      (x := F) fun j => subset_closure (mem_range_self j)
  -- Step 6: `W = ⇑G`, and `∫ (f (φ j) - W) ^ 2 = ‖F (φ j) - G‖ ^ 2 → 0`
  refine ⟨φ, G, hφ, Lp.memLp G, ?_⟩
  have heq : ∀ j, ‖F (φ j) - G‖ ^ 2 = ∫ x, (f (φ j) x - G x) ^ 2 ∂μ := by
    intro j
    have := hnorm _ ((hf (φ j)).sub (Lp.memLp G))
    rw [MemLp.toLp_sub (hf (φ j)) (Lp.memLp G), Lp.toLp_coeFn] at this
    exact this
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).pow 2
  rw [zero_pow two_ne_zero] at h2
  exact h2.congr heq

/-- **Rellich compactness in `L²(B̆₁(0))` for Lipschitz functions** (Gilbarg–Trudinger Thm 7.22,
Evans §5.7 Thm 1; used in Simon Ch. 5, Lemma 3.1).  If the `uⱼ : ℝⁿ → ℝ` are Lipschitz with
`∫_B uⱼ² ≤ M` and `∫_B ‖Duⱼ‖² ≤ M`, `B = B̆₁(0)`, then a subsequence converges in `L²(B)` to some
`W ∈ L²(B)`.  Each `uⱼ` is continuous and bounded on `B`, which has finite measure, so
`uⱼ ∈ L²(B)`.  `dorag_ha_rb_total_bounded` gives finite `L²(B)`-nets of `(uⱼ)` of every radius,
and `dorag_ha_rb_l2_subseq` extracts the convergent subsequence in the complete space `L²(B)`.
The hypothesis `n ≥ 1` is not needed. -/
theorem Submission.dorag_ha_rellich_ball : ∀ (n : ℕ) (M : ℝ) (u : ℕ → Euclid n → ℝ), 0 < n → (∀ j, ∃ L : NNReal, LipschitzWith L (u j)) → (∀ j, ∫ x in ball (0 : Euclid n) 1, u j x ^ 2 ≤ M) → (∀ j, ∫ x in ball (0 : Euclid n) 1, ‖fderiv ℝ (u j) x‖ ^ 2 ≤ M) → ∃ (φ : ℕ → ℕ) (W : Euclid n → ℝ), StrictMono φ ∧ MemLp W 2 (volume.restrict (ball (0 : Euclid n) 1)) ∧ Tendsto (fun j => ∫ x in ball (0 : Euclid n) 1, (u (φ j) x - W x) ^ 2) atTop (𝓝 0) := by
  intro n M u _hn hLip hu hDu
  -- step 1: `B̆₁(0)` has finite Lebesgue measure
  have : IsFiniteMeasure (volume.restrict (ball (0 : Euclid n) 1)) :=
    isFiniteMeasure_restrict.2 measure_ball_ne_top
  -- step 2: an `L`-Lipschitz `uⱼ` is continuous with `|uⱼ| ≤ |uⱼ(0)| + L` on `B̆₁(0)`, so `uⱼ ∈ L²`
  have hmem : ∀ j, MemLp (u j) 2 (volume.restrict (ball (0 : Euclid n) 1)) := by
    intro j
    obtain ⟨L, hL⟩ := hLip j
    refine MemLp.of_bound hL.continuous.aestronglyMeasurable (|u j 0| + L) ?_
    refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
    have h1 : |u j x - u j 0| ≤ L * ‖x‖ := by
      simpa only [Real.dist_eq, dist_zero_right] using hL.dist_le_mul x 0
    have h2 : (L : ℝ) * ‖x‖ ≤ L := mul_le_of_le_one_right L.coe_nonneg (mem_ball_zero_iff.1 hx).le
    rw [Real.norm_eq_abs]
    linarith [abs_sub_abs_le_abs_sub (u j x) (u j 0)]
  -- step 3: finite `L²(B̆₁(0))`-nets of `(uⱼ)` and extraction of a convergent subsequence
  exact Submission.dorag_ha_rb_l2_subseq (Euclid n) (volume.restrict (ball (0 : Euclid n) 1)) u
    hmem (Submission.dorag_ha_rb_total_bounded n M u hLip hu hDu)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
