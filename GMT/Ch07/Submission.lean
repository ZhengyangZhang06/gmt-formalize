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

/-- **Simon Ch. 2, 5.9; Ch. 4, 2.7**: the tangential divergence of the normal part of `X`.  If
`Q ≤ S`, `pr(x) = P_S`, `pr` and `X` are differentiable at `x` and `Y = X − pr·X` near `x`, then
`trace(p_Q ∘ DY(x)) = −X(x) · Σⱼ (Dpr(x)(p_Q eⱼ))^* (p_Q eⱼ)`: by the product rule
`DY(x) = DX(x) − P_S DX(x) − (Dpr(x)·)X(x)`, `trace(p_Q ∘ C) = Σⱼ ⟨p_Q eⱼ, C (p_Q eⱼ)⟩`, and `P_S`
fixes `p_Q eⱼ ∈ Q ⊆ S`. -/
theorem Submission.mcs_trace_normal_part_eq_neg_inner : ∀ (P : ℕ) (Q S : Submodule ℝ (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X Y : Euclid P → Euclid P) (x : Euclid P), Q ≤ S → pr x = S.starProjection → DifferentiableAt ℝ pr x → DifferentiableAt ℝ X x → Y =ᶠ[𝓝 x] (fun y => X y - pr y (X y)) → LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ (fderiv ℝ Y x).toLinearMap) = -inner ℝ (X x) (∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (Q.starProjection (EuclideanSpace.single j 1))) (Q.starProjection (EuclideanSpace.single j 1))) := by
  intro P Q S pr X Y x hQS hprx hpr hX hY
  -- Step 1: `DY(x)h = DX(x)h − P_S(DX(x)h) − (Dpr(x)h)(X(x))`
  have hDY : ∀ h, fderiv ℝ Y x h =
      fderiv ℝ X x h - S.starProjection (fderiv ℝ X x h) - fderiv ℝ pr x h (X x) := by
    intro h
    rw [hY.fderiv_eq, fderiv_fun_sub hX (hpr.clm_apply hX), fderiv_clm_apply hpr hX, hprx]
    simp only [sub_add_eq_sub_sub, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
  -- Step 2: `trace(p ∘ C) = Σⱼ ⟨p eⱼ, C (p eⱼ)⟩`
  have htr : ∀ C : Euclid P →L[ℝ] Euclid P,
      LinearMap.trace ℝ (Euclid P) (Q.starProjection.toLinearMap ∘ₗ C.toLinearMap) =
        ∑ j : Fin P, inner ℝ (Q.starProjection (EuclideanSpace.single j 1))
          (C (Q.starProjection (EuclideanSpace.single j 1))) := by
    intro C
    have hpp : Q.starProjection.toLinearMap ∘ₗ C.toLinearMap =
        Q.starProjection.toLinearMap ∘ₗ (Q.starProjection.toLinearMap ∘ₗ C.toLinearMap) := by
      refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      exact (Submodule.starProjection_eq_self_iff.mpr (Q.starProjection_apply_mem (C w))).symm
    rw [hpp, LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    exact (Submodule.inner_starProjection_left_eq_right Q _ _).symm
  -- Steps 3 and 4: each term is `−⟨X(x), (Dpr(x)u)^* u⟩`, `u = p eⱼ ∈ Q ⊆ S`
  rw [htr, inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  set u := Q.starProjection (EuclideanSpace.single j 1)
  have huS : S.starProjection u = u :=
    Submodule.starProjection_eq_self_iff.mpr (hQS (Submodule.starProjection_apply_mem _ _))
  rw [hDY, inner_sub_right, inner_sub_right, ← Submodule.inner_starProjection_left_eq_right, huS,
    sub_self, zero_sub, ← ContinuousLinearMap.adjoint_inner_left (fderiv ℝ pr x u) (X x) u,
    real_inner_comm]
/-- **Simon Ch. 4, 2.7** (the tangential part `Xᵀ = χ · pr · X`): let `U, O ⊆ ℝᴾ` be open,
`N ⊆ O` with `(N̄ \ N) ∩ U = ∅`, `pr` of class `C¹` on `O` and `X ∈ C¹_c(U; ℝᴾ)`.  Then some
`Xᵀ ∈ C¹_c(U; ℝᴾ)` equals `y ↦ pr(y) X(y)` near every point of `N`.  The compact set
`K = spt X ∩ N̄` lies in `N` (as `(N̄ \ N) ∩ U = ∅`), hence in `O ∩ U`; take a `C¹` cutoff `χ` with
compact support in `O ∩ U` and `χ = 1` near `K`.  Near `x ∈ N`, `χ = 1` if `x ∈ spt X`, and
`X = 0` otherwise. -/
theorem Submission.mcs_exists_c1_field_eq_proj_near : ∀ (P : ℕ) (U N O : Set (Euclid P)) (pr : Euclid P → (Euclid P →L[ℝ] Euclid P)) (X : Euclid P → Euclid P), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∃ XT : Euclid P → Euclid P, ContDiff ℝ 1 XT ∧ HasCompactSupport XT ∧ tsupport XT ⊆ U ∧ ∀ x ∈ N, XT =ᶠ[𝓝 x] (fun y => pr y (X y)) := by
  intro P U N O pr X hU hO hNO hpr hN hX hXc hXU
  -- Step 1: `K = spt X ∩ N̄` is compact and `K ⊆ N`, hence `K ⊆ W = O ∩ U`
  have hKc : IsCompact (tsupport X ∩ closure N) := hXc.isCompact.inter_right isClosed_closure
  have hKW : tsupport X ∩ closure N ⊆ O ∩ U := by
    rintro z ⟨hzX, hzN⟩
    have hz : z ∈ N := by
      by_contra hz
      exact eq_empty_iff_forall_notMem.1 hN z ⟨⟨hzN, hz⟩, hXU hzX⟩
    exact ⟨hNO hz, hXU hzX⟩
  -- Step 2: a `C¹` cutoff `χ` with `spt χ = V̄ ⊆ W` compact and `χ = 1` on `L`, `K ⊆ int L`
  obtain ⟨L, hLc, hLcl, hKL, hLW⟩ := exists_compact_closed_between hKc (hO.inter hU) hKW
  obtain ⟨V, hVo, hLV, hVW, hVc⟩ :=
    exists_open_between_and_isCompact_closure hLc (hO.inter hU) hLW
  obtain ⟨χ, hχ, -, hχV, hχL⟩ := exists_contDiff_support_eq_eq_one_iff (n := 1) hVo hLcl hLV
  have hχ1 : ContDiff ℝ 1 χ := by exact_mod_cast hχ
  have hχt : tsupport χ = closure V := by rw [tsupport, hχV]
  -- Step 3: `Xᵀ = χ · pr · X`
  refine ⟨fun y => χ y • pr y (X y), ?_, ?_, ?_, ?_⟩
  -- Step 4: `Xᵀ` is `C¹`: product rule at points of `O`; `Xᵀ = 0` near `y ∉ O`, as `spt χ ⊆ O`
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · exact hχ1.contDiffAt.smul ((hpr.contDiffAt (hO.mem_nhds hy)).clm_apply hX.contDiffAt)
    · have hyχ : χ =ᶠ[𝓝 y] 0 := by
        rw [← notMem_tsupport_iff_eventuallyEq, hχt]
        exact fun h => hy (hVW h).1
      refine (contDiffAt_const (c := (0 : Euclid P))).congr_of_eventuallyEq ?_
      filter_upwards [hyχ] with z hz
      simp [hz]
  -- Step 5: `Xᵀ` vanishes off the compact set `V̄`, and `spt Xᵀ ⊆ spt χ = V̄ ⊆ W ⊆ U`
  · refine HasCompactSupport.intro' hVc isClosed_closure fun y hy => ?_
    have hχy : χ y = 0 := by
      rw [← notMem_support, hχV]
      exact fun h => hy (subset_closure h)
    simp [hχy]
  · refine (tsupport_smul_subset_left χ fun y => pr y (X y)).trans ?_
    rw [hχt]
    exact fun z hz => (hVW hz).2
  -- Step 6: `Xᵀ = pr · X` near `x ∈ N`: `χ = 1` near `x` if `x ∈ spt X`, else `X = 0` near `x`
  · intro x hx
    by_cases hxX : x ∈ tsupport X
    · filter_upwards [isOpen_interior.mem_nhds (hKL ⟨hxX, subset_closure hx⟩)] with y hy
      rw [(hχL y).1 (interior_subset hy), one_smul]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxX] with y hy
      simp [hy]
/-- **Simon Ch. 4, 2.2–2.3** (additivity of the first variation of `V = v(M, θ)`): if
`x ↦ p_{TₓM}` is `Hⁿ⌞M`-measurable and `X, Y ∈ C¹_c(U; ℝᴾ)`, then `δV(X + Y) = δV(X) + δV(Y)`.
For `Z ∈ C¹_c(U; ℝᴾ)`, `θ div_M Z` is `Hⁿ⌞M`-integrable: `div_M Z(x) = tr(pₓ ∘ DZ(x))` is
measurable, `|div_M Z| ≤ ‖tr‖ sup ‖DZ‖` on `spt Z` and `div_M Z = 0` off `spt Z`, and `θ` is
integrable on the compact `spt Z ⊆ U`.  Pointwise `D(X + Y) = DX + DY` and the trace is linear, so
`div_M (X + Y) = div_M X + div_M Y`; integrate. -/
theorem Submission.mcs_firstVariation_add : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X Y : Euclid P → Euclid P), AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) (μHE[n].restrict R.carrier) → ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ContDiff ℝ 1 Y → HasCompactSupport Y → tsupport Y ⊆ U → R.firstVariation (X + Y) = R.firstVariation X + R.firstVariation Y := by
  intro P n U R X Y hp hX hXc hXU hY hYc hYU
  -- Step 1: the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and
  -- `div_M Z(x) = tr(pₓ ∘ DZ(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ (Z : Euclid P → Euclid P) (x : Euclid P), tangentialDivergence n R.carrier Z x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ Z x) := fun _ _ => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθ' : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  -- Step 2: `θ div_M Z` is `Hⁿ⌞M`-integrable for `Z ∈ C¹_c(U; ℝᴾ)`
  have hint : ∀ Z : Euclid P → Euclid P, ContDiff ℝ 1 Z → HasCompactSupport Z → tsupport Z ⊆ U →
      Integrable (fun x => (R.mult x : ℝ) * tangentialDivergence n R.carrier Z x)
        (μHE[n].restrict R.carrier) := by
    intro Z hZ hZc hZU
    have hD : Continuous (fderiv ℝ Z) := hZ.continuous_fderiv one_ne_zero
    -- Step 2(a): `div_M Z` is a.e. strongly measurable (`p` measurable, `DZ` continuous)
    have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier Z x)
        (μHE[n].restrict R.carrier) :=
      (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
        (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp hD.aestronglyMeasurable
    -- Step 2(b): `|θ div_M Z| ≤ ‖tr‖ C θ 1_K`, `K = spt Z`, `C = sup ‖DZ‖`
    obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hZc.fderiv ℝ)
    have hKm : MeasurableSet (tsupport Z) := (isClosed_tsupport Z).measurableSet
    have hbound : ∀ x, ‖(R.mult x : ℝ) * tangentialDivergence n R.carrier Z x‖ ≤
        (tsupport Z).indicator (fun x => ‖tr‖ * C * (R.mult x : ℝ)) x := by
      intro x
      rw [norm_mul, Real.norm_natCast, hdiv]
      by_cases hxK : x ∈ tsupport Z
      · rw [Set.indicator_of_mem hxK, mul_comm (R.mult x : ℝ)]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _)
          zero_le_one
      · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
          ContinuousLinearMap.comp_zero, map_zero, norm_zero, mul_zero]
    -- Step 2(c): `θ` is `Hⁿ⌞M`-integrable on `K`, since `∫_{M ∩ K} θ dHⁿ < ∞`
    have hθK : IntegrableOn (fun x => (R.mult x : ℝ)) (tsupport Z) (μHE[n].restrict R.carrier) := by
      rw [IntegrableOn, Measure.restrict_restrict hKm, Set.inter_comm]
      simpa using integrable_toReal_of_lintegral_ne_top hθ'.aemeasurable
        (R.locallyIntegrable_mult _ hZc hZU)
    exact ((integrable_indicator_iff hKm).2 (Integrable.const_mul hθK (‖tr‖ * C))).mono'
      (hθ.aestronglyMeasurable.mul hmeas) (ae_of_all _ hbound)
  -- Step 3: `div_M (X + Y) = div_M X + div_M Y` pointwise
  have hadd : ∀ x, tangentialDivergence n R.carrier (X + Y) x =
      tangentialDivergence n R.carrier X x + tangentialDivergence n R.carrier Y x := by
    intro x
    rw [hdiv, hdiv, hdiv, fderiv_add (hX.differentiable one_ne_zero x)
      (hY.differentiable one_ne_zero x), ContinuousLinearMap.comp_add, map_add]
  -- Step 4: integrate, by `integral_add`
  simp only [IMRep.firstVariation, hadd, mul_add]
  exact integral_add (hint X hX hXc hXU) (hint Y hY hYc hYU)
/-- **Simon Ch. 4, 3.14–3.15**: the mean curvature field `H(x) = Σⱼ (Dpr(x)[p(x)eⱼ])^*(p(x)eⱼ)`
on `N ∩ U`, `H = 0` elsewhere, is `μ`-a.e. strongly measurable and bounded on compact `K ⊆ U`.
`N ∩ U = N̄ ∩ U` is Borel, `x ↦ (Dpr(x), p(x))` is a.e. strongly measurable and
`(B, q) ↦ Σⱼ (B(qeⱼ))^*(qeⱼ)` is continuous; for compact `K ⊆ U`, `K ∩ N̄ ⊆ N ⊆ O` is compact and
`Dpr` is continuous on the open `O`, so `‖H‖ ≤ P max(sup_{K ∩ N̄} ‖Dpr‖, 0)` on `K`. -/
theorem Submission.mcs_exists_meanCurvature_field : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U N O : Set (Euclid P)) (pr p : Euclid P → (Euclid P →L[ℝ] Euclid P)), IsOpen U → IsOpen O → N ⊆ O → ContDiffOn ℝ 1 pr O → (closure N \ N) ∩ U = ∅ → AEStronglyMeasurable p μ → (∀ x, ‖p x‖ ≤ 1) → ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H μ ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, ∀ x ∈ K, ‖H x‖ ≤ Λ) ∧ ∀ x ∈ N ∩ U, H x = ∑ j : Fin P, ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1)) := by
  intro P μ U N O pr p hU hO hNO hpr hNU hp hp1
  -- `F(B, q) = Σⱼ (B(qeⱼ))^*(qeⱼ)`, `eⱼ` the standard basis of `ℝᴾ`, is continuous
  let F : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) × (Euclid P →L[ℝ] Euclid P) → Euclid P :=
    fun q => ∑ j : Fin P, ContinuousLinearMap.adjoint (q.1 (q.2 (EuclideanSpace.single j 1)))
      (q.2 (EuclideanSpace.single j 1))
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun j _ => ?_
    have hq : Continuous fun q : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) ×
        (Euclid P →L[ℝ] Euclid P) => q.2 (EuclideanSpace.single j 1) :=
      continuous_snd.clm_apply continuous_const
    exact (ContinuousLinearMap.adjoint.continuous.comp (continuous_fst.clm_apply hq)).clm_apply hq
  -- `N ∩ U = N̄ ∩ U` is Borel
  have hG : N ∩ U = closure N ∩ U := by
    refine Subset.antisymm (inter_subset_inter_left _ subset_closure) fun z hz => ⟨?_, hz.2⟩
    by_contra hzN
    have hz' : z ∈ (closure N \ N) ∩ U := ⟨⟨hz.1, hzN⟩, hz.2⟩
    rw [hNU] at hz'
    exact hz'
  have hGm : MeasurableSet (N ∩ U) := by
    rw [hG]
    exact isClosed_closure.measurableSet.inter hU.measurableSet
  -- `H = 1_{N ∩ U} F(Dpr, p)`
  refine ⟨(N ∩ U).indicator fun x => F (fderiv ℝ pr x, p x), ?_, ?_,
    fun x hx => indicator_of_mem hx _⟩
  · exact (hF.comp_aestronglyMeasurable
      ((measurable_fderiv ℝ pr).aestronglyMeasurable.prodMk hp)).indicator hGm
  -- `‖Dpr‖ ≤ C` on the compact `K ∩ N̄ ⊆ N ⊆ O`, so `‖H‖ ≤ P max(C, 0)` on `K`
  intro K hK hKU
  have hKN : K ∩ closure N ⊆ N ∩ U := fun x hx => by
    rw [hG]
    exact ⟨hx.2, hKU hx.1⟩
  obtain ⟨C, hC⟩ := (hK.inter_right isClosed_closure).exists_bound_of_continuousOn
    ((hpr.continuousOn_fderiv_of_isOpen hO le_rfl).mono fun x hx => hNO (hKN hx).1)
  refine ⟨P * max C 0, fun x hxK => ?_⟩
  by_cases hx : x ∈ N ∩ U
  · rw [indicator_of_mem hx]
    have hDx : ‖fderiv ℝ pr x‖ ≤ max C 0 :=
      (hC x ⟨hxK, subset_closure hx.1⟩).trans (le_max_left _ _)
    have hj : ∀ j : Fin P, ‖ContinuousLinearMap.adjoint
        (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1))‖ ≤
        max C 0 := by
      intro j
      have hu : ‖p x (EuclideanSpace.single j 1)‖ ≤ 1 :=
        calc ‖p x (EuclideanSpace.single j 1)‖
            ≤ ‖p x‖ * ‖(EuclideanSpace.single j 1 : Euclid P)‖ := (p x).le_opNorm _
          _ = ‖p x‖ := by simp
          _ ≤ 1 := hp1 x
      calc ‖ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1)))
              (p x (EuclideanSpace.single j 1))‖
          ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ pr x (p x (EuclideanSpace.single j 1)))‖ *
              ‖p x (EuclideanSpace.single j 1)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ pr x (p x (EuclideanSpace.single j 1))‖ *
              ‖p x (EuclideanSpace.single j 1)‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ ‖fderiv ℝ pr x‖ * ‖p x (EuclideanSpace.single j 1)‖ *
              ‖p x (EuclideanSpace.single j 1)‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ max C 0 * 1 * 1 := by gcongr
        _ = max C 0 := by ring
    calc ‖F (fderiv ℝ pr x, p x)‖
        ≤ ∑ j : Fin P, ‖ContinuousLinearMap.adjoint
            (fderiv ℝ pr x (p x (EuclideanSpace.single j 1))) (p x (EuclideanSpace.single j 1))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _j : Fin P, max C 0 := Finset.sum_le_sum fun j _ => hj j
      _ = P * max C 0 := by simp
  · rw [indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
