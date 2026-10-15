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

/-- The flat current `c[[Q']]`, `Q' = span τ` (Simon 6.2.2 for a plane, as in the proof of 7.3.3):
`R = (Q', |c|, sgn c · τ₁ ∧ ⋯ ∧ τₙ)` is an integer multiplicity triple in `ℝᴾ` with
`τ(R)(ω) = c ∫_{Q'} ω(τ) dHⁿ` and `μ_R = |c| Hⁿ⌞Q'`.  `Q'` is an `n`-plane (`τ` is linearly
independent), closed, the range of a linear isometry `ℝⁿ → ℝᴾ` (so countably `n`-rectifiable),
locally `Hⁿ`-finite, and is its own approximate tangent space at each of its points. -/
theorem Submission.idtp_cse_etp_plane_imrep : ∀ (P n : ℕ) (τ : Fin n → Euclid P) (c : ℤ), Orthonormal ℝ τ → c ≠ 0 → ∃ R : IMRep (univ : Set (Euclid P)) n, (∀ ω : DifferentialForm (Euclid P) n, R.action ω = (c : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), ω x τ ∂μHE[n]) ∧ R.measure = (c.natAbs : ℝ≥0∞) • (μHE[n] : Measure (Euclid P)).restrict (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) := by
  intro P n τ c hτ hc
  -- the plane `Q = span τ` has dimension `n` and is closed, hence Borel
  have hQrank : Module.finrank ℝ (Submodule.span ℝ (Set.range τ)) = n := by
    rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hQmeas : MeasurableSet (Submodule.span ℝ (Set.range τ) : Set (Euclid P)) :=
    (Submodule.span ℝ (Set.range τ)).closed_of_finiteDimensional.measurableSet
  set Q := Submodule.span ℝ (Set.range τ)
  -- `Q` is the range of a linear isometry `ℝⁿ → ℝᴾ`, hence countably `n`-rectifiable
  have hrect : CountablyRectifiable n (Q : Set (Euclid P)) := by
    let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] Q :=
      ((stdOrthonormalBasis ℝ Q).reindex (finCongr hQrank)).repr.symm
    have hrange : Set.range (Q.subtypeₗᵢ.comp e.toLinearIsometry) = (Q : Set (Euclid P)) := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact (e v).2
      · intro hy
        exact ⟨e.symm ⟨y, hy⟩, by simp⟩
    rw [← hrange]
    exact Poincare.SimonGMT.Chapter03.countablyRectifiable_range
      (Q.subtypeₗᵢ.comp e.toLinearIsometry).lipschitzWith
  -- the orientation `sgn c · τ₁ ∧ ⋯ ∧ τₙ`, i.e. `α ↦ sgn c · α(τ)`
  let ξ : MultiVector P n := ((Int.sign c : ℤ) : ℝ) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ τ
  have hξ : ∀ α : Covector (Euclid P) n, ξ α = ((Int.sign c : ℤ) : ℝ) * α τ := fun α => rfl
  have hcs : ((c.natAbs : ℕ) : ℝ) * ((Int.sign c : ℤ) : ℝ) = (c : ℝ) := by
    have h : ((c.sign * (c.natAbs : ℤ) : ℤ) : ℝ) = (c : ℝ) := by rw [Int.sign_mul_natAbs]
    rw [Int.cast_mul, Int.cast_natCast, mul_comm] at h
    exact h
  refine ⟨{ carrier := (Q : Set (Euclid P))
            mult := fun _ => c.natAbs
            orient := fun _ => ξ
            measurableSet_carrier := hQmeas
            carrier_subset := subset_univ _
            rectifiable := hrect
            measurable_mult := measurable_const
            mult_pos := fun _ _ => Int.natAbs_pos.mpr hc
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := aestronglyMeasurable_const
            orients := ?_ }, ?_, ?_⟩
  · -- local finiteness: `Hⁿ⌞Q` is finite on compact sets
    intro K hK _
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) hQrank
    have hfin : (μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P)) K < ∞ :=
      hK.measure_lt_top
    rw [Measure.restrict_apply' hQmeas, Set.inter_comm] at hfin
    simp only [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin.ne
  · -- every point of `Q` has approximate tangent space `Q`, oriented by `±τ`
    filter_upwards [Poincare.SimonGMT.Chapter03.ae_hasApproximateTangentSpaceAt_submodule
      (E := Euclid P) hQrank] with x hx
    refine ⟨Q, hx, τ, hτ, rfl, ?_⟩
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · right
      intro α
      show ξ α = -α τ
      rw [hξ, Int.sign_eq_neg_one_of_neg hneg]
      push_cast
      ring
    · left
      intro α
      show ξ α = α τ
      rw [hξ, Int.sign_eq_one_of_pos hpos]
      push_cast
      ring
  · -- the action: `|c| · sgn c = c`
    intro ω
    show ∫ x in (Q : Set (Euclid P)), ((c.natAbs : ℕ) : ℝ) * ξ (ω x) ∂μHE[n] = _
    rw [← integral_const_mul]
    congr 1
    funext x
    rw [hξ, ← mul_assoc, hcs]
  · -- the measure: a constant density
    show ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).withDensity
      (fun _ => ((c.natAbs : ℕ) : ℝ≥0∞)) = _
    exact withDensity_const _

/-- **Mass measures of blow-ups converging to `c[[Q']]`** (proof of Simon 7.3.3(1), edge of a
planar sector of a 2-dimensional minimizing cone, chapter-07.txt lines 497–510; `μ_{Tⱼ} → μ_T` as
in 7.2.4 and Remark 7.2.5(1), lines 160–165; blow-up scaling as in the proof of 7.3.1, lines
329–337).  Let `τ` be orthonormal, `Q' = span τ`, `C' = c[[Q']]` with `c ≠ 0`, and let the mass
measures of `η_{a,λⱼ#}C` converge to that of `C'`.  Then for every representation `R` of `C` and
every `g ∈ C_c(ℝᴾ)`, `λⱼ⁻ⁿ ∫ g ∘ η_{a,λⱼ} dμ_R → |c| ∫_{Q'} g dHⁿ`.  `C'` has a representation
with `μ_{C'} = |c| Hⁿ⌞Q'` (`idtp_cse_etp_plane_imrep`).  For `λ > 0` and `η = η_{a,λ}`,
`(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents `η_{a,λ#}C`, with measure `λ⁻ⁿ η_#μ_R`, by the argument of
`dtc_blowUp_imrep`: `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`, `η` preserves approximate tangent spaces, and
`η_{a,λ#}C(ω) = λ⁻ⁿ C(ω ∘ η)`.  Hence `∫ g dμ_{η_{a,λⱼ#}C} = λⱼ⁻ⁿ ∫ g ∘ η_{a,λⱼ} dμ_R`. -/
theorem Submission.idtp_cse_etp_blowup_vague_limit : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (a : Euclid P) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j) (C' : GeometricCurrentOn (univ : Set (Euclid P)) n) (τ : Fin n → Euclid P) (c : ℤ), Orthonormal ℝ τ → c ≠ 0 → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, C' ω = (c : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), (ω : DifferentialForm (Euclid P) n) x τ ∂μHE[n]) → MassMeasuresConverge (fun j => blowUp C a (lams j) (hlams j).ne') C' → ∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents C → ∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ n * ∫ x, g (dilation a (lams j) x) ∂R.measure) atTop (𝓝 ((c.natAbs : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x ∂μHE[n])) := by
  intro P n C a lams hlams C' τ c hτ hc hC' hconv R hR g hg hgc
  -- Step 1: `C' = c[[Q']]` is represented by `R'` with `μ_{R'} = |c| Hⁿ⌞Q'`, so
  -- `∫ g dμ_{R'} = |c| ∫_{Q'} g dHⁿ`
  obtain ⟨R', hR'act, hR'meas⟩ := Submission.idtp_cse_etp_plane_imrep P n τ c hτ hc
  have hR'rep : R'.Represents C' := fun ω => by rw [hC' ω, hR'act]
  have hlim : ∫ x, g x ∂R'.measure =
      (c.natAbs : ℝ) * ∫ x in (Submodule.span ℝ (Set.range τ) : Set (Euclid P)), g x ∂μHE[n] := by
    rw [hR'meas, integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul]
  -- Step 2: for `λ > 0`, `η_{a,λ#}C` is represented by `(η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)`, `η = η_{a,λ}`,
  -- whose measure is `B ↦ λ⁻ⁿ μ_R(η⁻¹(B))`
  have hblow : ∀ (lam : ℝ) (hlam : 0 < lam), ∃ R₁ : IMRep (dilation a lam '' univ) n,
      R₁.Represents (blowUp C a lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s →
        R₁.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation a lam ⁻¹' s) := by
    intro lam hlam
    have hne : lam ≠ 0 := hlam.ne'
    -- `η` is an affine homeomorphism with inverse `z ↦ a + λz`
    have hη : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
        (Homeomorph.addLeft (-(lam⁻¹ • a)))) : Euclid P → Euclid P) = dilation a lam := by
      funext y
      simp [dilation, dilationCLM]
    have hme : MeasurableEmbedding (dilation a lam) := by
      rw [← hη]
      exact Homeomorph.measurableEmbedding _
    have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation a lam) :=
      contDiff_const.add (dilationCLM P lam).contDiff
    have hιη : ∀ y, a + lam • dilation a lam y = y := fun y => by
      simp [dilation, dilationCLM, smul_add, smul_smul, hne]
    -- `Hⁿ(η_{x,r}(s)) = r⁻ⁿ Hⁿ(s)` for `r > 0`: `η_{x,r}(s)` is the translate of `r⁻¹s`
    have himage : ∀ (x : Euclid P) (r : ℝ), 0 < r → ∀ s : Set (Euclid P),
        μHE[n] (dilation x r '' s) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] s := by
      intro x r hr s
      have hs : dilation x r '' s = (fun z => -(r⁻¹ • x) + z) '' ((fun y => r⁻¹ • y) '' s) := by
        rw [Set.image_image]
        rfl
      rw [hs, (isometry_add_left (-(r⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
        Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne') s, ENNReal.smul_def,
        smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
      congr 2
      simp [abs_of_pos hr]
    -- `η_#Hⁿ = λⁿ Hⁿ`, as `η⁻¹(B) = η_{−λ⁻¹a,λ⁻¹}(B)`
    have hmap : Measure.map (dilation a lam) (μHE[n] : Measure (Euclid P)) =
        ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
      ext B hB
      have hpre : dilation a lam ⁻¹' B = dilation (-(lam⁻¹ • a)) lam⁻¹ '' B :=
        (congrFun (Set.image_eq_preimage_of_inverse
          (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hne])
          (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hne])) B).symm
      rw [Measure.map_apply hme.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
        Measure.smul_apply, smul_eq_mul]
    have hκ0 : 0 ≤ lam⁻¹ ^ n := by positivity
    set κ : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hκ
    -- `Hⁿ⌞η(s) = κ η_#(Hⁿ⌞s)`, `κ = λ⁻ⁿ`, hence change of variables along `η`
    have hkey : ∀ s : Set (Euclid P),
        μHE[n].restrict (dilation a lam '' s) = κ • (μHE[n].restrict s).map (dilation a lam) := by
      intro s
      have h1 : (μHE[n].restrict s).map (dilation a lam) =
          ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation a lam '' s) := by
        rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
          hme.injective.preimage_image]
      rw [h1, smul_smul, hκ, ← ENNReal.ofReal_mul hκ0, ← mul_pow, inv_mul_cancel₀ hne,
        one_pow, ENNReal.ofReal_one, one_smul]
    have hlint : ∀ (s : Set (Euclid P)) (f : Euclid P → ℝ≥0∞),
        ∫⁻ z in dilation a lam '' s, f z ∂μHE[n] =
          κ * ∫⁻ y in s, f (dilation a lam y) ∂μHE[n] := by
      intro s f
      rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
    have hint : ∀ (s : Set (Euclid P)) (f : Euclid P → ℝ),
        ∫ z in dilation a lam '' s, f z ∂μHE[n] =
          lam⁻¹ ^ n * ∫ y in s, f (dilation a lam y) ∂μHE[n] := by
      intro s f
      rw [hkey s, integral_smul_measure, hme.integral_map, hκ, ENNReal.toReal_ofReal hκ0,
        smul_eq_mul]
    -- `T_{η(y)}η(M) = T_yM`: `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into
    -- `r ↓ 0`
    have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
        HasApproximateTangentSpaceAt n R.carrier y Q →
          HasApproximateTangentSpaceAt n (dilation a lam '' R.carrier) (dilation a lam y) Q := by
      intro y Q hT
      refine ⟨hT.1, fun f => ?_⟩
      have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation a lam y) r ''
          (dilation a lam '' R.carrier) =
            Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' R.carrier := by
        intro r
        rw [image_image]
        congr 1
        funext w
        simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
          smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
        rw [← smul_sub, smul_smul, mul_inv, mul_comm]
      simp_rw [hset]
      have hscale : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
        · filter_upwards [self_mem_nhdsWithin] with r hr
          exact mul_pos hlam hr
      exact (hT.2 f).comp hscale
    -- `ω ↦ ω ∘ η` maps `𝒟ⁿ(η(ℝᴾ))` to `𝒟ⁿ(ℝᴾ)`
    have hpull : ∀ ω : TestFormOn (dilation a lam '' univ) n,
        ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, ∀ y, (ω' : DifferentialForm (Euclid P) n) y =
          (ω : DifferentialForm (Euclid P) n) (dilation a lam y) := by
      intro ω
      obtain ⟨⟨hsmooth, hcompact⟩, -⟩ := ω.property
      refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation a lam y), ?_⟩, fun y => rfl⟩
      change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation a lam y)) ∧
        tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation a lam y)) ⊆ univ
      refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, subset_univ _⟩
      have h := hcompact.comp_homeomorph ((Homeomorph.smulOfNeZero lam⁻¹
        (inv_ne_zero hne)).trans (Homeomorph.addLeft (-(lam⁻¹ • a))))
      rwa [hη] at h
    -- `η_{a,λ#}C(ω) = C(η^#ω) = λ⁻ⁿ C(ω ∘ η)`, since `(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id)`
    have hpush : ∀ (ω : TestFormOn (dilation a lam '' univ) n)
        (ω' : TestFormOn (univ : Set (Euclid P)) n),
        (∀ y, (ω' : DifferentialForm (Euclid P) n) y =
          (ω : DifferentialForm (Euclid P) n) (dilation a lam y)) →
        blowUp C a lam hne ω = lam⁻¹ ^ n * C ω' := by
      intro ω ω' hω
      unfold blowUp
      rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
        show lam⁻¹ ^ n * C ω' = C (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
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
        Fintype.card_fin, show -(lam⁻¹ • a) + dilationCLM P lam y = dilation a lam y from rfl,
        ← hω y]
      simp
    refine ⟨{ carrier := dilation a lam '' R.carrier
              mult := fun z => R.mult (a + lam • z)
              orient := fun z => R.orient (a + lam • z)
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
      refine ⟨dilation a lam '' M₀, by rw [himage a lam hlam, hM₀, mul_zero],
        fun j => dilation a lam ∘ F j, fun j => ?_, ?_⟩
      · obtain ⟨K, hK⟩ := hF j
        exact ⟨_, ((isometry_add_left (-(lam⁻¹ • a))).lipschitzWith.comp
          (dilationCLM P lam).lipschitzWith).comp hK⟩
      · rintro _ ⟨y, hy, rfl⟩
        rcases hcover hy with h0 | h1
        · exact Or.inl ⟨y, h0, rfl⟩
        · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
          exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
    · rintro _ ⟨y, hy, rfl⟩
      show 0 < R.mult (a + lam • dilation a lam y)
      rw [hιη]
      exact R.mult_pos y hy
    · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is compact
      intro K hK _
      rw [← image_inter_preimage, hlint]
      simp only [hιη]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (R.locallyIntegrable_mult _ ?_ (subset_univ _))
      rw [← hη]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [hkey]
      refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure κ
      simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
    · rw [hkey]
      refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) κ
      obtain ⟨Q, hQ, hξ⟩ := hy
      exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
    · -- `η_{a,λ#}C(ω) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ ∘ η⁻¹ ⟨ω, ξ ∘ η⁻¹⟩ dHⁿ`
      intro ω
      obtain ⟨ω', hω'⟩ := hpull ω
      rw [hpush ω ω' hω', hR ω']
      simp only [IMRep.action]
      rw [hint]
      congr 1
      refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
      simp [hιη, hω']
    · -- `∫_B θ ∘ η⁻¹ d(Hⁿ⌞η(M)) = κ ∫_{η⁻¹(B)} θ d(Hⁿ⌞M)`
      intro s hs
      simp only [IMRep.measure]
      rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
        Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
      simp [hιη]
  choose Rs hRs hRsmeas using fun j => hblow (lams j) (hlams j)
  -- Step 3: `μ_{R_j} = λⱼ⁻ⁿ (η_j)_#μ_R`, so `∫ g dμ_{R_j} = λⱼ⁻ⁿ ∫ g ∘ η_j dμ_R` (no
  -- integrability needed)
  have hcont : ∀ j, Continuous (dilation a (lams j)) := fun j => by
    unfold dilation
    fun_prop
  have hmeasEq : ∀ j, (Rs j).measure =
      ENNReal.ofReal ((lams j)⁻¹ ^ n) • R.measure.map (dilation a (lams j)) := by
    intro j
    ext s hs
    rw [hRsmeas j s hs, Measure.smul_apply, Measure.map_apply (hcont j).measurable hs, smul_eq_mul]
  have hint : ∀ j, ∫ x, g x ∂(Rs j).measure =
      (lams j)⁻¹ ^ n * ∫ x, g (dilation a (lams j) x) ∂R.measure := by
    intro j
    rw [hmeasEq j, integral_smul_measure,
      integral_map (hcont j).measurable.aemeasurable hg.aestronglyMeasurable,
      ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr (hlams j).le) n), smul_eq_mul]
  -- Step 4: test `μ_{η_{a,λⱼ#}C} → μ_{C'}` against `g`
  have h := hconv Rs hRs R' hR'rep g hg hgc (subset_univ _)
  rw [hlim] at h
  simpa only [hint] using h
/-- **Two orthonormal frames of one `2`-plane** (used in the proof of Simon 7.3.3).  If
`a, e ∈ Q` (`dim Q = 2`) are orthonormal and lie in the span of the orthonormal pair `τ`, then
`span τ = Q` (`span {a, e}` is a `2`-plane inside both), and `α(τ) = ε α(a, e)`, `ε = ±1`, for
every `2`-covector `α`: writing `a = c₀τ₀ + c₁τ₁`, `e = d₀τ₀ + d₁τ₁`, bilinearity and alternation
give `α(a, e) = D α(τ)` with `D = c₀d₁ − c₁d₀`, and `D² = 1` by Lagrange's identity. -/
theorem Submission.idtp_cse_etp_plane_frame_sign : ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)) (a e : Euclid P) (τ : Fin 2 → Euclid P), Module.finrank ℝ Q = 2 → a ∈ Q → e ∈ Q → ‖a‖ = 1 → ‖e‖ = 1 → inner ℝ a e = 0 → Orthonormal ℝ τ → a ∈ Submodule.span ℝ (Set.range τ) → e ∈ Submodule.span ℝ (Set.range τ) → Submodule.span ℝ (Set.range τ) = Q ∧ ∃ ε : ℤ, ε.natAbs = 1 ∧ ∀ α : Covector (Euclid P) 2, α τ = (ε : ℝ) * α ![a, e] := by
  intro P Q a e τ hQ haQ heQ ha he hae hτ haτ heτ
  -- `![a, e]` is orthonormal, so `W = span {a, e}` is a plane inside both `Q` and `span τ`
  have hae' : Orthonormal ℝ ![a, e] := by
    refine ⟨Fin.forall_fin_two.mpr ⟨ha, he⟩, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa using hae
    · simpa [real_inner_comm] using hae
    · exact absurd rfl hij
  have hWdim : Module.finrank ℝ (Submodule.span ℝ (Set.range ![a, e])) = 2 := by
    rw [finrank_span_eq_card hae'.linearIndependent, Fintype.card_fin]
  have hτdim : Module.finrank ℝ (Submodule.span ℝ (Set.range τ)) = 2 := by
    rw [finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
  have hWτ : Submodule.span ℝ (Set.range ![a, e]) = Submodule.span ℝ (Set.range τ) :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.range_subset_iff.mpr (Fin.forall_fin_two.mpr ⟨haτ, heτ⟩)))
      (by rw [hWdim, hτdim])
  have hWQ : Submodule.span ℝ (Set.range ![a, e]) = Q :=
    Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_le.mpr (Set.range_subset_iff.mpr (Fin.forall_fin_two.mpr ⟨haQ, heQ⟩)))
      (by rw [hWdim, hQ])
  refine ⟨hWτ.symm.trans hWQ, ?_⟩
  -- coordinates `a = c₀τ₀ + c₁τ₁`, `e = d₀τ₀ + d₁τ₁`
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp haτ
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp heτ
  have hi : ∀ u v : Fin 2 → ℝ,
      inner ℝ (∑ i, u i • τ i) (∑ i, v i • τ i) = u 0 * v 0 + u 1 * v 1 := by
    intro u v
    rw [hτ.inner_sum u v Finset.univ, Fin.sum_univ_two]
    simp
  have h1 := hi c c
  rw [hc, real_inner_self_eq_norm_sq, ha] at h1
  have h2 := hi d d
  rw [hd, real_inner_self_eq_norm_sq, he] at h2
  have h3 := hi c d
  rw [hc, hd, hae] at h3
  -- Lagrange's identity: the determinant `D = c₀d₁ − c₁d₀` has `D² = 1`
  have hD : (c 0 * d 1 - c 1 * d 0) * (c 0 * d 1 - c 1 * d 0) = 1 := by
    linear_combination (-(d 0 * d 0 + d 1 * d 1)) * h1 - h2 + (c 0 * d 0 + c 1 * d 1) * h3
  -- bilinearity and alternation of a `2`-covector: `α(a, e) = D α(τ)`
  have hα : ∀ α : Covector (Euclid P) 2, α ![a, e] = (c 0 * d 1 - c 1 * d 0) * α τ := by
    intro α
    have hu0 : ∀ x y w : Euclid P, update ![x, y] 0 w = ![w, y] := by
      intro x y w; funext i; fin_cases i <;> rfl
    have hu1 : ∀ x y w : Euclid P, update ![x, y] 1 w = ![x, w] := by
      intro x y w; funext i; fin_cases i <;> rfl
    have add0 : ∀ x y z : Euclid P, α ![x + y, z] = α ![x, z] + α ![y, z] := by
      intro x y z
      have h := α.map_update_add ![x, z] 0 x y
      rwa [hu0, hu0, hu0] at h
    have add1 : ∀ x y z : Euclid P, α ![x, y + z] = α ![x, y] + α ![x, z] := by
      intro x y z
      have h := α.map_update_add ![x, y] 1 y z
      rwa [hu1, hu1, hu1] at h
    have smul0 : ∀ (r : ℝ) (x z : Euclid P), α ![r • x, z] = r * α ![x, z] := by
      intro r x z
      have h := α.map_update_smul ![x, z] 0 r x
      rwa [hu0, hu0, smul_eq_mul] at h
    have smul1 : ∀ (r : ℝ) (x z : Euclid P), α ![x, r • z] = r * α ![x, z] := by
      intro r x z
      have h := α.map_update_smul ![x, z] 1 r z
      rwa [hu1, hu1, smul_eq_mul] at h
    have diag : ∀ x : Euclid P, α ![x, x] = 0 := fun x =>
      α.map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)
    have anti : ∀ x y : Euclid P, α ![y, x] = -α ![x, y] := by
      intro x y
      have h := diag (x + y)
      rw [add0, add1, add1, diag, diag] at h
      linarith
    rw [← hc, ← hd, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [add0, add1, smul0, smul1, diag]
    rw [anti (τ 0) (τ 1),
      show (![τ 0, τ 1] : Fin 2 → Euclid P) = τ by funext i; fin_cases i <;> rfl]
    ring
  have key : ∀ α : Covector (Euclid P) 2, α τ = (c 0 * d 1 - c 1 * d 0) * α ![a, e] := by
    intro α
    rw [hα α, ← mul_assoc, hD, one_mul]
  rcases mul_self_eq_one_iff.mp hD with h | h
  · exact ⟨1, rfl, fun α => by rw [key α, h]; norm_num⟩
  · exact ⟨-1, rfl, fun α => by rw [key α, h]; norm_num⟩
/-- **Rescaled points with a uniform lower mass bound lie in the limit set** (the common core of
steps 2(d) and 3 of the edge tangent-plane argument in the cone-sector endpoint density proof for
Simon 7.3.3).  Let `μ` be finite on compact subsets of `ℝᴾ`, `S ⊆ ℝᴾ` closed, `λⱼ > 0` and
`wⱼ → w`.  Suppose `λⱼ⁻² ∫ g ∘ η_{a,λⱼ} dμ → m ∫_S g dH²` for every continuous compactly
supported `g`, and for each `r > 0` eventually `ω₂ (λⱼ r)² ≤ μ(B_{λⱼ r}(a + λⱼ wⱼ))`.  Then
`w ∈ S`.  Otherwise some `B_ρ(w)` misses `S`; with `r = ρ/4`, the bump
`g = min(1, max(0, 2 - |z - w|/(2r)))` vanishes on `S`, so the rescaled integrals tend to `0`.
But once `|wⱼ - w| < r`, `η_{a,λⱼ}` maps `B_{λⱼ r}(a + λⱼ wⱼ)` into `B̄_{2r}(w)`, where `g = 1`,
so `λⱼ⁻² ∫ g ∘ η_{a,λⱼ} dμ ≥ λⱼ⁻² μ(B_{λⱼ r}(a + λⱼ wⱼ)) ≥ ω₂ r² > 0` eventually. -/
theorem Submission.idtp_cse_etp_rescaled_limit_mem : ∀ (P : ℕ) (μ : Measure (Euclid P)) (S : Set (Euclid P)) (a w : Euclid P) (m : ℝ) (lams : ℕ → ℝ) (ws : ℕ → Euclid P), IsClosed S → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → (∀ j, 0 < lams j) → Tendsto ws atTop (𝓝 w) → (∀ g : Euclid P → ℝ, Continuous g → HasCompactSupport g → Tendsto (fun j => (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ) atTop (𝓝 (m * ∫ x in S, g x ∂μHE[2]))) → (∀ r : ℝ, 0 < r → ∀ᶠ j in atTop, unitBallVolume 2 * ENNReal.ofReal ((lams j * r) ^ 2) ≤ μ (ball (a + lams j • ws j) (lams j * r))) → w ∈ S := by
  intro P μ S a w m lams ws hS hμ hlam hws hV hL
  by_contra hw
  -- step 2: a ball `B_ρ(w)` misses `S`; `r = ρ / 4`
  obtain ⟨ρ, hρ, hρS⟩ := Metric.isOpen_iff.1 hS.isOpen_compl w hw
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / 4 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  -- the bump `g`: `g = 1` on `closedBall w (2r)`, `g = 0` off `ball w ρ`, `g ≥ 0`
  obtain ⟨g, hg_def⟩ : ∃ g : Euclid P → ℝ, g = fun z => min 1 (max 0 (2 - dist z w / (2 * r))) :=
    ⟨_, rfl⟩
  have hg_cont : Continuous g := by rw [hg_def]; fun_prop
  have hg_nonneg : ∀ z, 0 ≤ g z := fun z => by
    rw [hg_def]
    exact le_min zero_le_one (le_max_left _ _)
  have hg_one : ∀ z, dist z w ≤ 2 * r → g z = 1 := by
    intro z hz
    have h : 1 ≤ 2 - dist z w / (2 * r) := by
      have : dist z w / (2 * r) ≤ 1 := (div_le_one₀ (by positivity)).2 hz
      linarith
    rw [hg_def]
    exact min_eq_left (h.trans (le_max_right _ _))
  have hg_zero : ∀ z, ρ ≤ dist z w → g z = 0 := by
    intro z hz
    have h : 2 - dist z w / (2 * r) ≤ 0 := by
      have : 2 ≤ dist z w / (2 * r) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      linarith
    rw [hg_def]
    simp only [max_eq_left h, min_eq_right zero_le_one]
  have hg_supp : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall w ρ) fun z hz =>
      hg_zero z (not_le.1 (by simpa only [Metric.mem_closedBall] using hz)).le
  -- `g = 0` on `S`, so `∫_S g dH² = 0` and the rescaled integrals tend to `0`
  have hgS : ∫ x in S, g x ∂μHE[2] = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      hg_zero x (not_lt.1 fun h => hρS (Metric.mem_ball.2 h) hx)
  have hlim := hV g hg_cont hg_supp
  rw [hgS, mul_zero] at hlim
  -- step 1: `κ = ω₂ ∈ (0, ∞)`
  have hκ : 0 < (unitBallVolume 2).toReal := by
    have h0 : (0 : ℝ≥0∞) < volume (ball (0 : Euclid 2) 1) := measure_ball_pos _ _ one_pos
    have h1 : volume (ball (0 : Euclid 2) 1) < ∞ := measure_ball_lt_top
    exact ENNReal.toReal_pos h0.ne' h1.ne
  -- `ηⱼ = dilation a λⱼ` scales distances by `λⱼ⁻¹`
  have hdil : ∀ l : ℝ, 0 < l → ∀ x v : Euclid P,
      dist (dilation a l x) v = l⁻¹ * dist x (a + l • v) := by
    intro l hl x v
    have h : dilation a l x - v = l⁻¹ • (x - (a + l • v)) := by
      simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply]
      rw [smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hl.ne', one_smul]
      abel
    rw [dist_eq_norm, h, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hl.le), ← dist_eq_norm]
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => lt_top_iff_ne_top.2 (hμ K hK)⟩
  -- steps 3–4: `κ r² ≤ λⱼ⁻² ∫ g ∘ ηⱼ dμ` for all large `j`
  have hlow : ∀ᶠ j in atTop,
      (unitBallVolume 2).toReal * r ^ 2 ≤ (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ := by
    filter_upwards [hL r hr, Metric.tendsto_nhds.1 hws r hr] with j hj hwj
    have hl := hlam j
    have hBfin : μ (ball (a + lams j • ws j) (lams j * r)) ≠ ∞ := measure_ball_lt_top.ne
    -- `1_{Bⱼ} ≤ g ∘ ηⱼ` for `Bⱼ = B_{λⱼ r}(a + λⱼ wⱼ)`, as `ηⱼ(Bⱼ) ⊆ closedBall w (2r)`
    have hle : (ball (a + lams j • ws j) (lams j * r)).indicator (1 : Euclid P → ℝ) ≤
        fun x => g (dilation a (lams j) x) := by
      refine fun x => ?_
      by_cases hx : x ∈ ball (a + lams j • ws j) (lams j * r)
      · rw [Set.indicator_of_mem hx, Pi.one_apply]
        refine (hg_one _ ?_).ge
        have h1 : dist (dilation a (lams j) x) (ws j) < r := by
          rw [hdil _ hl, inv_mul_lt_iff₀ hl]
          exact Metric.mem_ball.1 hx
        linarith [dist_triangle (dilation a (lams j) x) (ws j) w]
      · rw [Set.indicator_of_notMem hx]
        exact hg_nonneg _
    -- step 3: both sides are `μ`-integrable (`μ` is finite on compact sets)
    have hcomp : HasCompactSupport fun x => g (dilation a (lams j) x) :=
      HasCompactSupport.intro (isCompact_closedBall (a + lams j • w) (lams j * ρ)) fun x hx => by
        refine hg_zero _ ?_
        rw [hdil _ hl, le_inv_mul_iff₀ hl]
        exact (not_le.1 (by simpa only [Metric.mem_closedBall] using hx)).le
    have hηc : Continuous (dilation a (lams j)) :=
      continuous_const.add (dilationCLM P (lams j)).continuous
    have hint_g : Integrable (fun x => g (dilation a (lams j) x)) μ :=
      (hg_cont.comp hηc).integrable_of_hasCompactSupport hcomp
    have hint_B : Integrable
        ((ball (a + lams j • ws j) (lams j * r)).indicator (1 : Euclid P → ℝ)) μ :=
      (integrableOn_const (C := (1 : ℝ)) hBfin).integrable_indicator measurableSet_ball
    -- `κ (λⱼ r)² ≤ μ(Bⱼ) ≤ ∫ g ∘ ηⱼ dμ`
    have h1 := integral_mono hint_B hint_g hle
    rw [integral_indicator_one measurableSet_ball, measureReal_def] at h1
    have h2 := ENNReal.toReal_mono hBfin hj
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at h2
    have hinv : (lams j)⁻¹ ^ 2 * lams j ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]
    calc (unitBallVolume 2).toReal * r ^ 2
        = (lams j)⁻¹ ^ 2 * ((unitBallVolume 2).toReal * (lams j * r) ^ 2) := by
          linear_combination (-((unitBallVolume 2).toReal * r ^ 2)) * hinv
      _ ≤ (lams j)⁻¹ ^ 2 * ∫ x, g (dilation a (lams j) x) ∂μ := by
          gcongr
          exact h2.trans h1
  -- step 5: `0 < κ r² ≤ lim λⱼ⁻² ∫ g ∘ ηⱼ dμ = 0`, a contradiction
  have h := ge_of_tendsto hlim hlow
  have hpos : 0 < (unitBallVolume 2).toReal * r ^ 2 := mul_pos hκ (pow_pos hr 2)
  linarith

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
