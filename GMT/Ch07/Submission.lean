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

/-- **The coordinate covector `eⱼ ⌟ δ` on `ℝ^{m+1}`** (step 2 of the boundary weak-derivative
computation in the graph-cycle regularity step of Simon 7.4.3).  For `j ∈ Fin (m + 1)` there is a
continuous alternating `m`-form `β` on `ℝ^{m+1}` with `β(e₀, …, êᵢ, …, e_m) = (−1)ʲ` if `i = j`
and `0` otherwise: `β(w₁, …, w_m) = δ(eⱼ, w₁, …, w_m)` for the standard determinant form `δ`. -/
theorem Submission.dgcr_bwd_coordinate_covector : ∀ (m : ℕ) (j : Fin (m + 1)), ∃ β : Covector (Euclid (m + 1)) m, ∀ i : Fin (m + 1), β (i.removeNth (fun l : Fin (m + 1) => EuclideanSpace.single l (1 : ℝ))) = if i = j then (-1 : ℝ) ^ (j : ℕ) else 0 := by
  intro m j
  classical
  -- The standard basis `b l = e_l` and its determinant `δ₀ c = det (c l r)_{r,l}`.
  let b : Module.Basis (Fin (m + 1)) ℝ (Euclid (m + 1)) :=
    (EuclideanSpace.basisFun (Fin (m + 1)) ℝ).toBasis
  have hb : (b : Fin (m + 1) → Euclid (m + 1)) = fun l => EuclideanSpace.single l (1 : ℝ) := by
    funext l; simp [b]
  have hdet : ∀ c : Fin (m + 1) → Euclid (m + 1), b.det c = (Matrix.of fun r l => c l r).det := by
    intro c
    rw [Module.Basis.det_apply]
    congr 1
  -- `δ₀` is continuous (entrywise continuous matrix, then `det`), so it is a covector `δ`.
  have hcont : Continuous (fun c : Fin (m + 1) → Euclid (m + 1) => b.det c) := by
    simp only [hdet]
    apply Continuous.matrix_det
    refine continuous_matrix fun r l => ?_
    exact (EuclideanSpace.proj r).continuous.comp (continuous_apply l)
  let δ : Covector (Euclid (m + 1)) (m + 1) := { b.det with cont := hcont }
  have hδ : ∀ c, δ c = b.det c := fun c => rfl
  -- `β = δ.curryLeft (b j)`, i.e. `β w = δ (b j, w₁, …, w_m)`.
  refine ⟨δ.curryLeft (b j), fun i => ?_⟩
  rw [ContinuousAlternatingMap.curryLeft_apply_apply, hδ, ← hb]
  split_ifs with hij
  · -- `i = j`: `(b i, removeNth i b) = b ∘ (cycleRange i)⁻¹`, of sign `(−1)ⁱ`.
    subst hij
    have hc : (Matrix.vecCons (b i) (i.removeNth ⇑b) : Fin (m + 1) → Euclid (m + 1)) =
        ⇑b ∘ ⇑(Equiv.symm i.cycleRange) :=
      Fin.cons_removeNth_eq_comp_cycleRange_symm (⇑b) i
    rw [hc, AlternatingMap.map_perm, Module.Basis.det_self, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp [Units.smul_def]
  · -- `i ≠ j`: `e_j` occurs at positions `0` and `l.succ`, where `i.succAbove l = j`.
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (Ne.symm hij)
    apply AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := l.succ)
    · simp [Fin.removeNth_apply, hl]
    · exact (Fin.succ_ne_zero l).symm
/-- Translations are continuous in measure on balls: for measurable `F ⊆ ℝᵐ`,
`Lᵐ(((F − z) Δ F) ∩ B_R(0)) → 0` as `z → 0`, where `F − z = {v : v + z ∈ F}`.  Inner and outer
regularity give `K ⊆ A = F ∩ B_{R+1}(0) ⊆ O`, `K` compact, `O` open, with `Lᵐ(A \ K)` and
`Lᵐ(O \ A)` below `ε / 4`, and some `δ > 0` with the `δ`-thickening of `K` inside `O`.  For
`|z| < min(δ, 1)` the set lies in `((A \ K) − z) ∪ (O \ A) ∪ (A \ K) ∪ ((O \ A) − z)`, whose
measure is at most `ε` by translation invariance. -/
theorem Submission.codim1_zsl_pc_translate_tendsto_zero : ∀ (m : ℕ) (F : Set (Euclid m)) (R : ℝ), MeasurableSet F → Tendsto (fun z : Euclid m => volume (symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R)) (𝓝 0) (𝓝 0) := by
  intro m F R hF
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε4 : ε / 2 / 2 ≠ 0 := (ENNReal.half_pos (ENNReal.half_pos hε.ne').ne').ne'
  -- the bounded piece `A = F ∩ B(0, R+1)` of `F`
  obtain ⟨A, hA⟩ : ∃ A : Set (Euclid m), A = F ∩ ball (0 : Euclid m) (R + 1) := ⟨_, rfl⟩
  have hmem : ∀ v : Euclid m, v ∈ A ↔ v ∈ F ∧ ‖v‖ < R + 1 := by
    intro v
    rw [hA, Set.mem_inter_iff, mem_ball_zero_iff]
  have hAmeas : MeasurableSet A := by
    rw [hA]
    exact hF.inter measurableSet_ball
  have hAfin : volume A ≠ ∞ := by
    rw [hA]
    exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) measure_ball_lt_top)
  -- inner and outer regularity: `K ⊆ A ⊆ O`, `K` compact, `O` open
  obtain ⟨K, hKA, hKc, hK⟩ := hAmeas.exists_isCompact_sdiff_lt hAfin hε4
  obtain ⟨O, hAO, hOo, -, hO⟩ := hAmeas.exists_isOpen_sdiff_lt hAfin hε4
  -- a uniform margin: `thickening δ K ⊆ O`
  obtain ⟨δ, hδ, hδO⟩ := hKc.exists_thickening_subset_open hOo (hKA.trans hAO)
  filter_upwards [ball_mem_nhds (0 : Euclid m) (lt_min hδ one_pos)] with z hz
  rw [mem_ball_zero_iff] at hz
  have hzδ : ‖z‖ < δ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz (min_le_right _ _)
  have hsub : symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R ⊆
      ((fun v => v + z) ⁻¹' (A \ K) ∪ (O \ A)) ∪ ((A \ K) ∪ (fun v => v + z) ⁻¹' (O \ A)) := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [mem_ball_zero_iff] at hv2
    have hvA : ‖v‖ < R + 1 := by linarith
    have hvzA : ‖v + z‖ < R + 1 :=
      calc ‖v + z‖ ≤ ‖v‖ + ‖z‖ := norm_add_le _ _
        _ < R + 1 := by linarith
    rcases Set.mem_symmDiff.1 hv1 with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · -- `v + z ∈ F`, `v ∉ F`
      rw [mem_preimage] at ha
      left
      by_cases hK' : v + z ∈ K
      · right
        refine ⟨hδO (mem_thickening_iff.2 ⟨v + z, hK', ?_⟩), fun h => hb ((hmem v).1 h).1⟩
        rw [dist_self_add_right]
        exact hzδ
      · left
        exact ⟨(hmem (v + z)).2 ⟨ha, hvzA⟩, hK'⟩
    · -- `v ∈ F`, `v + z ∉ F`
      rw [mem_preimage] at hb
      right
      by_cases hK' : v ∈ K
      · right
        refine ⟨hδO (mem_thickening_iff.2 ⟨v, hK', ?_⟩), fun h => hb ((hmem (v + z)).1 h).1⟩
        rw [dist_self_add_left]
        exact hzδ
      · left
        exact ⟨(hmem v).2 ⟨ha, hvA⟩, hK'⟩
  calc volume (symmDiff ((fun v => v + z) ⁻¹' F) F ∩ ball (0 : Euclid m) R)
      ≤ volume (((fun v => v + z) ⁻¹' (A \ K) ∪ (O \ A)) ∪
          ((A \ K) ∪ (fun v => v + z) ⁻¹' (O \ A))) := measure_mono hsub
    _ ≤ (volume ((fun v => v + z) ⁻¹' (A \ K)) + volume (O \ A)) +
          (volume (A \ K) + volume ((fun v => v + z) ⁻¹' (O \ A))) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) (measure_union_le _ _))
    _ = (volume (A \ K) + volume (O \ A)) + (volume (A \ K) + volume (O \ A)) := by
        rw [measure_preimage_add_right (volume : Measure (Euclid m)) z (A \ K),
          measure_preimage_add_right (volume : Measure (Euclid m)) z (O \ A)]
    _ ≤ (ε / 2 / 2 + ε / 2 / 2) + (ε / 2 / 2 + ε / 2 / 2) :=
        add_le_add (add_le_add hK.le hO.le) (add_le_add hK.le hO.le)
    _ = ε := by rw [ENNReal.add_halves, ENNReal.add_halves]

/-- Mollifying `u = 1_F` with any continuous `ρ ≥ 0`, `∫ρ = 1`, `spt ρ ⊆ B̄_δ(0)`, moves it by at
most `η` in `L¹(B_R(0))` once `δ` is small (Simon 2.5).  By `∫ρ = 1`,
`|ρ * u(v) - u(v)| ≤ ∫ρ(z)|u(v - z) - u(v)| dz`; Tonelli bounds `∫_{B_R}|ρ * u - u|` by
`∫ρ(z) L^m(((F + z) Δ F) ∩ B_R) dz`, and `codim1_zsl_pc_translate_tendsto_zero` makes the
translation defect `≤ η` for `|z| ≤ δ`. -/
theorem Submission.codim1_zsl_pc_mollify_indicator_l1 : ∀ (m : ℕ) (F : Set (Euclid m)) (R η : ℝ), MeasurableSet F → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : Euclid m → ℝ, Continuous ρ → (∀ z, 0 ≤ ρ z) → (∀ z, δ < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤ ENNReal.ofReal η := by
  intro m F R η hF hη
  -- `δ = ε/2`, where the translation defect is `< η` on `B_ε(0)`.
  have hev : ∀ᶠ y in 𝓝 (0 : Euclid m),
      volume (symmDiff ((fun v => v + y) ⁻¹' F) F ∩ ball (0 : Euclid m) R) < ENNReal.ofReal η :=
    (Submission.codim1_zsl_pc_translate_tendsto_zero m F R hF).eventually
      (eventually_lt_nhds (ENNReal.ofReal_pos.2 hη))
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro ρ hρc hρ0 hρsupp hρ1
  -- Facts about the indicator `u = 1_F`, which is then made opaque.
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hu_bd : ∀ x, ‖F.indicator (fun _ => (1 : ℝ)) x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  have hu_sd : ∀ v y : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) (v + y) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
        = (symmDiff ((fun w => w + y) ⁻¹' F) F).indicator 1 v := by
    intro v y
    by_cases h1 : v + y ∈ F <;> by_cases h2 : v ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  generalize F.indicator (fun _ => (1 : ℝ)) = u at hu_meas hu_bd hu_sd ⊢
  -- `ρ` is integrable (compact support), hence so is each convolution integrand.
  have hρ_cs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) (ε / 2)) fun x hx => ?_
    apply hρsupp
    simpa using hx
  have hρ_int : Integrable ρ := hρc.integrable_of_hasCompactSupport hρ_cs
  have hρ_meas : Measurable ρ := hρc.measurable
  have hint : ∀ v, Integrable (fun z => ρ z * u (v - z)) := by
    intro v
    refine hρ_int.mono
      (by exact (hρ_meas.mul (hu_meas.comp (measurable_const_sub v))).aestronglyMeasurable)
      (ae_of_all _ fun z => ?_)
    rw [norm_mul]
    calc ‖ρ z‖ * ‖u (v - z)‖ ≤ ‖ρ z‖ * 1 := by gcongr; exact hu_bd _
      _ = ‖ρ z‖ := mul_one _
  -- Pointwise bound, using `∫ ρ = 1`.
  have hpt : ∀ v, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ ≤ ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ := by
    intro v
    have h1 : (∫ z, ρ z * u (v - z)) - u v = ∫ z, (ρ z * u (v - z) - ρ z * u v) := by
      rw [integral_sub (hint v) (hρ_int.mul_const (u v)), integral_mul_const (u v) ρ, hρ1,
        one_mul]
    rw [h1]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun z => ?_
    rw [← mul_sub, enorm_mul]
  -- The inner integral is the translation defect of `codim1_zsl_pc_translate_tendsto_zero`.
  have hΦ : ∀ z, ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ
      = volume (symmDiff ((fun v => v + -z) ⁻¹' F) F ∩ ball (0 : Euclid m) R) := by
    intro z
    have hS : MeasurableSet (symmDiff ((fun v => v + -z) ⁻¹' F) F) :=
      (hF.preimage (measurable_add_const _)).symmDiff hF
    rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
    refine lintegral_congr fun v => ?_
    rw [sub_eq_add_neg v z]
    exact hu_sd v (-z)
  have hmeas : Measurable (Function.uncurry fun (v z : Euclid m) =>
      ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m => ‖ρ p.2‖ₑ * ‖u (p.1 - p.2) - u p.1‖ₑ :=
      (hρ_meas.comp measurable_snd).enorm.mul
        ((hu_meas.comp (measurable_fst.sub measurable_snd)).sub
          (hu_meas.comp measurable_fst)).enorm
    exact this
  -- Tonelli, then `Φ(-z) ≤ η` wherever `ρ z ≠ 0`, and `∫⁻ ‖ρ‖ₑ = ofReal (∫ ρ) = 1`.
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖(∫ z, ρ z * u (v - z)) - u v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ∫⁻ z, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_mono fun v => hpt v
    _ = ∫⁻ z, ∫⁻ v in ball (0 : Euclid m) R, ‖ρ z‖ₑ * ‖u (v - z) - u v‖ₑ :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ z, ‖ρ z‖ₑ * ∫⁻ v in ball (0 : Euclid m) R, ‖u (v - z) - u v‖ₑ := by
        refine lintegral_congr fun z => ?_
        exact lintegral_const_mul _ (by fun_prop)
    _ ≤ ∫⁻ z, ‖ρ z‖ₑ * ENNReal.ofReal η := by
        refine lintegral_mono fun z => ?_
        by_cases hz : ρ z = 0
        · simp [hz]
        · have hz' : ‖z‖ ≤ ε / 2 := by
            by_contra h
            exact hz (hρsupp z (not_le.1 h))
          gcongr
          rw [hΦ z]
          refine (hεP ?_).le
          rw [dist_zero_right, norm_neg]
          linarith
    _ = (∫⁻ z, ‖ρ z‖ₑ) * ENNReal.ofReal η := lintegral_mul_const _ (by fun_prop)
    _ = ENNReal.ofReal η := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hρ_int]
        have : (fun x => ‖ρ x‖) = ρ := funext fun x => Real.norm_of_nonneg (hρ0 x)
        rw [this, hρ1, ENNReal.ofReal_one, one_mul]
/-- `L¹` translation estimate for a `C¹` function `f : ℝᵐ → ℝ`:
`∫_{B_R(0)} |f(v + h) − f(v)| dv ≤ |h| ∫_{B_{R+|h|}(0)} ‖Df(w)‖ dw`.  By the fundamental theorem
of calculus along `t ↦ v + t h`, `|f(v + h) − f(v)| ≤ |h| ∫₀¹ ‖Df(v + t h)‖ dt`; integrate over
`B_R(0)`, exchange the order of integration (Tonelli) and use, for `t ∈ (0, 1]`, the inclusion
`B_R(0) + t h ⊆ B_{R+|h|}(0)` and the translation invariance of Lebesgue measure. -/
theorem Submission.codim1_zsl_pc_smooth_translate_l1 : ∀ (m : ℕ) (f : Euclid m → ℝ) (h : Euclid m) (R : ℝ), ContDiff ℝ 1 f → ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ ≤ ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
  intro m f h R hf
  have hcont : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hGc : Continuous (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hcont.enorm
  have hGm : Measurable (fun w : Euclid m => ‖fderiv ℝ f w‖ₑ) := hGc.measurable
  have hshift : Continuous (fun p : Euclid m × ℝ => p.1 + p.2 • h) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hmeas2 : Measurable (uncurry fun (v : Euclid m) (t : ℝ) => ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    (hGc.comp hshift).measurable
  -- Steps 1–2: pointwise bound via the fundamental theorem of calculus along `t ↦ v + t • h`
  have key : ∀ v : Euclid m, ‖f (v + h) - f v‖ₑ ≤
      ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := by
    intro v
    have hseg : Continuous (fun t : ℝ => v + t • h) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (v + s • h))
        (fderiv ℝ f (v + t • h) h) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => v + s • h) h t :=
        (((hasDerivAt_id' t).smul_const h).const_add v).congr_deriv (one_smul ℝ h)
      exact (hdiff (v + t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have hc1 : Continuous (fun t : ℝ => fderiv ℝ f (v + t • h) h) :=
      (hcont.comp hseg).clm_apply continuous_const
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hc1.intervalIntegrable 0 1)
    simp only [one_smul, zero_smul, add_zero] at hFTC
    rw [← hFTC, intervalIntegral.integral_of_le zero_le_one]
    calc ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ f (v + t • h) h‖ₑ
        ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h) h‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_mono fun t =>
            (ContinuousLinearMap.le_opENorm (fderiv ℝ f (v + t • h)) h).trans_eq (mul_comm _ _)
      _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ :=
          lintegral_const_mul _ (hGc.comp hseg).measurable
  have hmeasv : Measurable
      (fun v : Euclid m => ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ) :=
    hmeas2.lintegral_prod_right
  -- Step 4: translation invariance of Lebesgue measure and inclusion of balls
  have hball : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ ≤
      ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
    intro t ht
    have ht' : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1.le]
      exact mul_le_of_le_one_left (norm_nonneg h) ht.2
    have hsub : ball (0 : Euclid m) R ⊆
        (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖) := by
      intro v hv
      rw [mem_preimage, mem_ball_zero_iff]
      exact (norm_add_le _ _).trans_lt (add_lt_add_of_lt_of_le (mem_ball_zero_iff.mp hv) ht')
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ
        ≤ ∫⁻ v in (fun v => v + t • h) ⁻¹' ball (0 : Euclid m) (R + ‖h‖),
            ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
          (measurePreserving_add_right volume (t • h)).setLIntegral_comp_preimage
            measurableSet_ball hGm
  -- Steps 3 and 5: integrate, exchange the order of integration (Tonelli), and conclude
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R,
          ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_mono key
    _ = ‖h‖ₑ * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ f (v + t • h)‖ₑ := lintegral_const_mul _ hmeasv
    _ = ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ v in ball (0 : Euclid m) R, ‖fderiv ℝ f (v + t • h)‖ₑ :=
        congrArg (‖h‖ₑ * ·) (lintegral_lintegral_swap hmeas2.aemeasurable)
    _ ≤ ‖h‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1,
          ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ :=
        mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hball) _
    _ = ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
/-- Integration by parts for a Lipschitz `u` against `C¹` fields `Φᵢ` with compact support in
`B = B_R(0)`: `∫_B Σᵢ Du(x)eᵢ Φᵢ(x) dx = −∫_B u(x) Σᵢ DΦᵢ(x)eᵢ dx`.  Each `Φᵢ` is Lipschitz, so
Lipschitz integration by parts in direction `eᵢ` (`LipschitzWith.integral_lineDeriv_mul_eq`) applies
on `ℝⁿ`; by Rademacher, `lineDeriv u x eᵢ = Du(x)eᵢ` for a.e. `x`.  Both integrands are integrable
(`Du` is bounded by the Lipschitz constant) and vanish off `B`, so summing over `i` concludes. -/
theorem Submission.dorag_ha_lsc_ibp_lipschitz : ∀ (n : ℕ) (R : ℝ) (u : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), (∃ L : NNReal, LipschitzWith L u) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R u Φ ⟨L, hu⟩ hΦ hΦc hΦs
  set e : Fin n → Euclid n := fun i => EuclideanSpace.single i (1 : ℝ)
  have hΦL : ∀ i, ∃ C, LipschitzWith C (Φ i) := fun i =>
    ContDiff.lipschitzWith_of_hasCompactSupport (hΦc i) (hΦ i) one_ne_zero
  choose C hC using hΦL
  -- integrability of the two families of integrands
  have hint1 : ∀ i, Integrable (fun x => fderiv ℝ u x (e i) * Φ i x) := by
    intro i
    refine Integrable.bdd_mul (c := L * ‖e i‖)
      ((hΦ i).continuous.integrable_of_hasCompactSupport (hΦc i))
      (measurable_fderiv_apply_const ℝ u (e i)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    exact ((fderiv ℝ u x).le_opNorm (e i)).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg _))
  have hcontd : ∀ i, Continuous fun x => fderiv ℝ (Φ i) x (e i) := fun i =>
    ((hΦ i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint2 : ∀ i, Integrable (fun x => u x * fderiv ℝ (Φ i) x (e i)) := by
    intro i
    refine (hu.continuous.mul (hcontd i)).integrable_of_hasCompactSupport ?_
    exact ((hΦc i).fderiv_apply (𝕜 := ℝ) (e i)).mul_left
  -- per-coordinate identity on the whole space
  have key : ∀ i, ∫ x, fderiv ℝ u x (e i) * Φ i x = -∫ x, u x * fderiv ℝ (Φ i) x (e i) := by
    intro i
    have h1 :=
      hu.integral_lineDeriv_mul_eq (μ := (volume : Measure (Euclid n))) (hC i) (hΦc i) (e i)
    have h2 : (fun x => lineDeriv ℝ u x (e i) * Φ i x) =ᵐ[volume]
        fun x => fderiv ℝ u x (e i) * Φ i x := by
      filter_upwards [hu.ae_differentiableAt] with x hx
      rw [hx.lineDeriv_eq_fderiv]
    have h3 : (fun x => lineDeriv ℝ (Φ i) x (-e i) * u x) =
        fun x => -(u x * fderiv ℝ (Φ i) x (e i)) := by
      funext x
      rw [(((hΦ i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
      ring
    rw [integral_congr_ae h2, h3, integral_neg] at h1
    exact h1
  -- integrands vanish off the ball
  have hzero1 : ∀ x, x ∉ ball (0 : Euclid n) R →
      ∑ i : Fin n, fderiv ℝ u x (e i) * Φ i x = 0 := by
    intro x hx
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
  have hzero2 : ∀ x, x ∉ ball (0 : Euclid n) R →
      u x * ∑ i : Fin n, fderiv ℝ (Φ i) x (e i) = 0 := by
    intro x hx
    rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
    have : x ∉ tsupport (Φ i) := fun h => hx (hΦs i h)
    rw [fderiv_of_notMem_tsupport ℝ this]; rfl
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint1 i, integral_finsetSum _ fun i _ => hint2 i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => key i

namespace Submission

/-- Integration by parts on `B = B_R(0)` for `h` that is only `C¹` on `B`, against `C¹` fields
`Φᵢ` with compact support in `B`: `∫_B Σᵢ Dᵢh Φᵢ = -∫_B h Σᵢ DᵢΦᵢ`.  The supports of the `Φᵢ` lie
in some `B_{r₁}(0)`, `r₁ < R`.  A bump `χ` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ ⊆ B` makes
`h̃ = χh` a compactly supported `C¹`, hence Lipschitz, function, so `dorag_ha_lsc_ibp_lipschitz`
applies to `h̃`; both integrands only see `B_{r₁}(0)`, where `h̃ = h`. -/
theorem dorag_ha_lsc_ibp_c1_ball : ∀ (n : ℕ) (R : ℝ) (h : Euclid n → ℝ) (Φ : Fin n → Euclid n → ℝ), ContDiffOn ℝ 1 h (ball (0 : Euclid n) R) → (∀ i, ContDiff ℝ 1 (Φ i)) → (∀ i, HasCompactSupport (Φ i)) → (∀ i, tsupport (Φ i) ⊆ ball (0 : Euclid n) R) → ∫ x in ball (0 : Euclid n) R, ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x = -∫ x in ball (0 : Euclid n) R, h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
  intro n R h Φ hh hΦ hΦc hΦs
  -- `R ≤ 0`: the ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · rw [ball_eq_empty.2 hR]; simp
  -- The supports of the `Φᵢ` lie in a smaller ball `B_{r₁}(0)`, `0 < r₁ < R`.
  set K := ⋃ i, tsupport (Φ i)
  have hKc : IsClosed K := isClosed_iUnion_of_finite fun i => isClosed_tsupport _
  have hKB : K ⊆ ball 0 R := iUnion_subset hΦs
  obtain ⟨r₁, ⟨hr₁0, hr₁R⟩, hK₁⟩ := exists_pos_lt_subset_ball hR hKc hKB
  -- `h̃ = χh` with `χ = 1` on `B̄_{r₁}(0)` and `spt χ = B̄_{(r₁+R)/2}(0) ⊆ B` is `C¹_c`.
  let χ : ContDiffBump (0 : Euclid n) := ⟨r₁, (r₁ + R) / 2, hr₁0, by linarith⟩
  set ht : Euclid n → ℝ := fun x => χ x * h x
  have hχsupp : tsupport χ ⊆ ball 0 R := by
    rw [χ.tsupport_eq]; exact closedBall_subset_ball (show (r₁ + R) / 2 < R by linarith)
  have htC : ContDiff ℝ 1 ht := by
    rw [contDiff_iff_contDiffAt]; intro x
    by_cases hx : x ∈ ball (0 : Euclid n) R
    · exact ((χ.contDiff.contDiffOn).mul hh).contDiffAt (isOpen_ball.mem_nhds hx)
    · have hxχ : x ∉ tsupport χ := fun h' => hx (hχsupp h')
      have hev : ht =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxχ] with y hy
        simp [ht, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have htc : HasCompactSupport ht := χ.hasCompactSupport.mul_right
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport htc htC one_ne_zero
  have key := Submission.dorag_ha_lsc_ibp_lipschitz n R ht Φ ⟨C, hC⟩ hΦ hΦc hΦs
  -- On `B_{r₁}(0)`, `h̃ = h` near each point; off it, every `Φᵢ` and `DΦᵢ` vanishes.
  have hone : ∀ y ∈ ball (0 : Euclid n) r₁, ht y = h y := by
    intro y hy
    simp [ht, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have hEq : ∀ x ∈ ball (0 : Euclid n) r₁, ht =ᶠ[𝓝 x] h := by
    intro x hx
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy using hone y hy
  have hout : ∀ x, x ∉ ball (0 : Euclid n) r₁ → ∀ i, x ∉ tsupport (Φ i) :=
    fun x hx i h' => hx (hK₁ (mem_iUnion.2 ⟨i, h'⟩))
  have h1 : ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ h x (EuclideanSpace.single i (1 : ℝ)) * Φ i x =
      ∫ x in ball (0 : Euclid n) R,
        ∑ i : Fin n, fderiv ℝ ht x (EuclideanSpace.single i (1 : ℝ)) * Φ i x := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [(hEq x hx).fderiv_eq]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [image_eq_zero_of_notMem_tsupport (hout x hx i)]
  have h2 : ∫ x in ball (0 : Euclid n) R,
        h x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) =
      ∫ x in ball (0 : Euclid n) R,
        ht x * ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_ball fun x _ => ?_
    by_cases hx : x ∈ ball (0 : Euclid n) r₁
    · simp only [hone x hx]
    · have : ∑ i : Fin n, fderiv ℝ (Φ i) x (EuclideanSpace.single i (1 : ℝ)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [fderiv_of_notMem_tsupport ℝ (hout x hx i)]; rfl
      simp only [this, mul_zero]
  rw [h1, h2, key]

/-- Duality bound for the variation of a smooth `g` (Simon Ch. 2, 2.5 (4)): if `∫ g div ψ ≤ c`
for every `C^∞` field `ψ` with compact support in `B = B_r(0)` and `|ψ| ≤ 1`, then
`∫_B |Dg| ≤ c`.  Applied to the coordinates `ψᵢ`, `dorag_ha_lsc_ibp_c1_ball` gives
`∫ g div ψ = -∫_B Σᵢ Dg(eᵢ) ψᵢ`.  With the gradient `G = ∇g`, `θₖ = 1/(k+1)` and bumps `χₖ`
with `χₖ = 1` on `B̄_{r(1-θₖ/2)}(0)` and `spt χₖ ⊆ B`, the fields
`ψₖ = -χₖ G/√(|G|² + θₖ²)` are admissible, so `∫_B χₖ |G|²/√(|G|² + θₖ²) ≤ c`.  The integrands
tend to `|G| = |Dg|` on `B`, and Fatou's lemma concludes. -/
theorem codim1_zsl_pc_smooth_grad_bound : ∀ (m : ℕ) (g : Euclid m → ℝ) (r c : ℝ), ContDiff ℝ (⊤ : ℕ∞) g → (∀ ψ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap ≤ c) → ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ g v‖ₑ ≤ ENNReal.ofReal c := by
  intro m g r c hg hψ
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]; simp
  set B := ball (0 : Euclid m) r with hB
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
  -- Step 1: integration by parts in trace form, from `dorag_ha_lsc_ibp_c1_ball`.
  have ibp : ∀ ψ : Euclid m → Euclid m, ContDiff ℝ 1 ψ → HasCompactSupport ψ → tsupport ψ ⊆ B →
      ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = -∫ v in B, ∑ i : Fin m, fderiv ℝ g v (EuclideanSpace.single i (1:ℝ)) * ψ v i := by
    intro ψ hψ1 hψc hψB
    have key := Submission.dorag_ha_lsc_ibp_c1_ball m r g (fun i x => ψ x i)
      (hg.of_le h1).contDiffOn (fun i => (contDiff_piLp 2).1 hψ1 i)
      (fun i => hψc.comp_left (g := fun w : Euclid m => w i) (by simp))
      (fun i => (tsupport_comp_subset (g := fun w : Euclid m => w i) (by simp) ψ).trans hψB)
    have hd : ∀ v (i : Fin m), fderiv ℝ (fun x => ψ x i) v
        = (PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp (fderiv ℝ ψ v) := fun v i => by
      have h := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (ψ v) i).comp v
        ((hψ1.differentiable one_ne_zero) v).hasFDerivAt
      exact h.fderiv
    have htr : ∀ v, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap
        = ∑ i : Fin m, fderiv ℝ (fun x => ψ x i) v (EuclideanSpace.single i 1) := by
      intro v
      rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin m) ℝ)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hd]
      simp [EuclideanSpace.inner_single_left]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) ?_]
    · simp_rw [htr]
      simp only [] at key
      rw [key, neg_neg]
    · intro v hv
      have : fderiv ℝ ψ v = 0 := by
        by_contra hne
        exact hv (hψB (support_fderiv_subset ℝ hne))
      simp [this]
  -- Step 2: the gradient field `G = ∇g`.
  set L := fderiv ℝ g with hLdef
  have hL : ContDiff ℝ (⊤ : ℕ∞) L := (contDiff_infty_iff_fderiv.1 hg).2
  set G : Euclid m → Euclid m := fun v => (InnerProductSpace.toDual ℝ (Euclid m)).symm (L v)
    with hGdef
  have hGi : ∀ v (i : Fin m), G v i = L v (EuclideanSpace.single i 1) := by
    intro v i
    have := EuclideanSpace.inner_single_left i (1:ℝ) (G v)
    rw [real_inner_comm, hGdef, InnerProductSpace.toDual_symm_apply] at this
    simpa using this.symm
  have hGn : ∀ v, ‖G v‖ = ‖L v‖ := fun v => LinearIsometryEquiv.norm_map _ _
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_piLp 2]
    intro i
    have : (fun x => G x i) = fun x => L x (EuclideanSpace.single i 1) := funext fun x => hGi x i
    rw [this]
    exact hL.clm_apply contDiff_const
  have hsum : ∀ v, ∑ i : Fin m, L v (EuclideanSpace.single i 1) * G v i = ‖G v‖ ^ 2 := by
    intro v
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hGi, Real.norm_eq_abs, sq_abs, sq]
  -- Step 3: parameters `θₖ`, bump cut-offs `χₖ` and test fields `ψₖ`.
  set θ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hθdef
  have hθpos : ∀ k, 0 < θ k := fun k => by positivity
  have hθle : ∀ k, θ k ≤ 1 := fun k => by
    rw [hθdef, div_le_one (by positivity)]
    have := (Nat.cast_nonneg k : (0:ℝ) ≤ k)
    linarith
  have hθlim : Tendsto θ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set ri : ℕ → ℝ := fun k => r * (1 - θ k / 2) with hridef
  set ro : ℕ → ℝ := fun k => r * (1 - θ k / 4) with hrodef
  have hri : ∀ k, 0 < ri k := fun k => mul_pos hr (by linarith [hθle k])
  have hrio : ∀ k, ri k < ro k := fun k => mul_lt_mul_of_pos_left (by linarith [hθpos k]) hr
  have hro : ∀ k, ro k < r := fun k => mul_lt_of_lt_one_right hr (by linarith [hθpos k])
  let χ : ℕ → ContDiffBump (0 : Euclid m) := fun k => ⟨ri k, ro k, hri k, hrio k⟩
  have hχ1 : ∀ v ∈ B, ∀ᶠ k in atTop, χ k v = 1 := by
    intro v hv
    have hlim : Tendsto ri atTop (𝓝 r) := by
      have := (tendsto_const_nhds (x := r)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub (hθlim.div_const 2))
      simpa using this
    have hv' : ‖v‖ < r := by simpa [hB] using hv
    filter_upwards [hlim.eventually_const_lt hv'] with k hk
    exact (χ k).one_of_mem_closedBall (by rw [mem_closedBall_zero_iff]; exact hk.le)
  set s : ℕ → Euclid m → ℝ := fun k v => √(‖G v‖ ^ 2 + θ k ^ 2) with hsdef
  have hspos : ∀ k v, 0 < s k v := fun k v => Real.sqrt_pos.2 (by have := hθpos k; positivity)
  have hGs : ∀ k v, ‖G v‖ ≤ s k v := fun k v =>
    Real.le_sqrt_of_sq_le (by have := hθpos k; nlinarith)
  have hsc : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (s k) := fun k =>
    ((hG.norm_sq ℝ).add contDiff_const).sqrt (fun v => by have := hθpos k; positivity)
  set ψ : ℕ → Euclid m → Euclid m := fun k v => (-(χ k v / s k v)) • G v with hψdef
  set f : ℕ → Euclid m → ℝ := fun k v => χ k v * (‖G v‖ ^ 2 / s k v) with hfdef
  have hψs : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k) := fun k =>
    (((χ k).contDiff.div (hsc k) (fun v => (hspos k v).ne')).neg).smul hG
  have hψsupp : ∀ k, tsupport (ψ k) ⊆ closedBall 0 (ro k) := by
    intro k
    rw [← (χ k).tsupport_eq]
    apply closure_mono
    intro v hv
    rw [Function.mem_support] at hv ⊢
    intro h0
    apply hv
    simp [hψdef, h0]
  have hψB : ∀ k, tsupport (ψ k) ⊆ B := fun k => (hψsupp k).trans (closedBall_subset_ball (hro k))
  have hψc : ∀ k, HasCompactSupport (ψ k) := fun k =>
    (isCompact_closedBall 0 (ro k)).of_isClosed_subset (isClosed_tsupport _) (hψsupp k)
  have hψn : ∀ k v, ‖ψ k v‖ ≤ 1 := by
    intro k v
    have hχ0 := (χ k).nonneg (x := v)
    have hχ1' := (χ k).le_one (x := v)
    simp only [hψdef, norm_smul, norm_neg, norm_div, Real.norm_eq_abs, abs_of_nonneg hχ0,
      abs_of_pos (hspos k v)]
    rw [div_mul_eq_mul_div, div_le_one (hspos k v)]
    calc χ k v * ‖G v‖ ≤ 1 * s k v := mul_le_mul hχ1' (hGs k v) (norm_nonneg _) zero_le_one
      _ = s k v := one_mul _
  -- Step 4: `∫ g div ψₖ = ∫_B fₖ ≤ c`.
  have hint_eq : ∀ k, ∫ v, g v * LinearMap.trace ℝ (Euclid m) (fderiv ℝ (ψ k) v).toLinearMap
      = ∫ v in B, f k v := by
    intro k
    rw [ibp (ψ k) ((hψs k).of_le h1) (hψc k) (hψB k), ← integral_neg]
    congr 1
    funext v
    have : ∀ i : Fin m, L v (EuclideanSpace.single i 1) * (ψ k v) i
        = -(χ k v / s k v) * (L v (EuclideanSpace.single i 1) * G v i) := fun i => by
      simp only [hψdef, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [this, ← Finset.mul_sum, hsum, hfdef]
    ring
  have hle : ∀ k, ∫ v in B, f k v ≤ c := fun k =>
    (hint_eq k) ▸ hψ (ψ k) (hψs k) (hψc k) (hψB k) (hψn k)
  have hfc : ∀ k, Continuous (f k) := fun k =>
    (χ k).continuous.mul (((continuous_norm.comp hG.continuous).pow 2).div (hsc k).continuous
      (fun v => (hspos k v).ne'))
  have hfnn : ∀ k v, 0 ≤ f k v := fun k v =>
    mul_nonneg (χ k).nonneg (div_nonneg (sq_nonneg _) (hspos k v).le)
  have hfi : ∀ k, IntegrableOn (f k) B := fun k =>
    ((hfc k).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Euclid m) r)).mono_set
      ball_subset_closedBall
  have hbound : ∀ k, ∫⁻ v in B, ENNReal.ofReal (f k v) ≤ ENNReal.ofReal c := by
    intro k
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (ae_of_all _ (hfnn k))]
    exact ENNReal.ofReal_le_ofReal (hle k)
  -- Step 5: `fₖ → ‖Dg‖` on `B`, and Fatou's lemma.
  have htend : ∀ v ∈ B, Tendsto (fun k => ENNReal.ofReal (f k v)) atTop
      (𝓝 (ENNReal.ofReal ‖G v‖)) := by
    intro v hv
    apply ENNReal.tendsto_ofReal
    have hχt : Tendsto (fun k => χ k v) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [hχ1 v hv] with k hk; exact hk.symm)
    have hq : Tendsto (fun k => ‖G v‖ ^ 2 / s k v) atTop (𝓝 ‖G v‖) := by
      rcases eq_or_ne ‖G v‖ 0 with h0 | h0
      · simp [h0]
      · have hs : Tendsto (fun k => s k v) atTop (𝓝 (√(‖G v‖ ^ 2 + 0 ^ 2))) :=
          (tendsto_const_nhds.add (hθlim.pow 2)).sqrt
        have hne : √(‖G v‖ ^ 2 + 0 ^ 2) ≠ 0 := by
          rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]; exact h0
        have := (tendsto_const_nhds (x := ‖G v‖ ^ 2)).div hs hne
        convert this using 2
        rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq (norm_nonneg _), sq, mul_self_div_self]
    have := hχt.mul hq
    rw [one_mul] at this
    exact this
  calc ∫⁻ v in B, ‖L v‖ₑ = ∫⁻ v in B, liminf (fun k => ENNReal.ofReal (f k v)) atTop := by
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        rw [(htend v hv).liminf_eq, hGn, ofReal_norm]
    _ ≤ liminf (fun k => ∫⁻ v in B, ENNReal.ofReal (f k v)) atTop :=
        lintegral_liminf_le (fun k => (hfc k).measurable.ennreal_ofReal)
    _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hbound)

end Submission
/-- Mollifying a test field (Simon Ch. 2, 2.5): with the reflected kernel `ρ̌(z) = ρ(-z)`, the
field `ψ' = ρ̌ ⋆ ψ` is `C^∞`, has compact support in `B_{r+ε}(0)` (`spt ψ ⊆ B_{r₁}(0)`, `r₁ < r`,
and `spt ρ̌ ⊆ B̄_ε(0)`) and satisfies `|ψ'| ≤ ∫ρ̌ = 1`.  Differentiating under the convolution and
commuting the trace with the integral gives `div ψ'(w) = ∫ ρ(z) div ψ(w + z) dz`; Fubini and the
measure-preserving shear `(v, z) ↦ (v + z, z)` then turn `∫ (ρ ⋆ 1_F) div ψ` into `∫_F div ψ'`. -/
theorem Submission.codim1_zsl_pc_mollify_test_field : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (ψ : Euclid m → Euclid m) (r ε : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball (0 : Euclid m) r → (∀ v, ‖ψ v‖ ≤ 1) → ∃ ψ' : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ HasCompactSupport ψ' ∧ tsupport ψ' ⊆ ball (0 : Euclid m) (r + ε) ∧ (∀ v, ‖ψ' v‖ ≤ 1) ∧ ∫ v, (∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap = ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap := by
  intro m F ρ ψ r ε hF hρ hρ0 hρε hρ1 hψ hψcs hψr hψ1
  -- basic facts about `ρ` and its reflection `ρ'`
  have hρc : Continuous ρ := hρ.continuous
  have hρcs : HasCompactSupport ρ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε z (by simpa using hz))
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρcs
  set ρ' : Euclid m → ℝ := fun z => ρ (-z) with hρ'_def
  have hρ'c : Continuous ρ' := hρc.comp continuous_neg
  have hρ'cs : HasCompactSupport ρ' :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε)
      (fun z hz => hρε (-z) (by simpa using hz))
  have hρ'smooth : ContDiff ℝ (⊤ : ℕ∞) ρ' := hρ.comp contDiff_neg
  have hρ'i : Integrable ρ' := hρ'c.integrable_of_hasCompactSupport hρ'cs
  have hρ'1 : ∫ z, ρ' z = 1 := by
    rw [show (∫ z, ρ' z) = ∫ z, ρ (-z) from rfl, integral_neg_eq_self ρ volume]
    exact hρ1
  -- the trace as a continuous linear map
  obtain ⟨Tr, hTr⟩ : ∃ Tr : (Euclid m →L[ℝ] Euclid m) →L[ℝ] ℝ, ∀ A : Euclid m →L[ℝ] Euclid m,
      Tr A = LinearMap.trace ℝ (Euclid m) A.toLinearMap :=
    ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ (Euclid m)) ∘ₗ (ContinuousLinearMap.coeLM ℝ)), fun A => rfl⟩
  -- the mollified field `ψ' = ρ' ⋆ ψ`
  set L : ℝ →L[ℝ] Euclid m →L[ℝ] Euclid m := ContinuousLinearMap.lsmul ℝ ℝ with hL
  set ψ' : Euclid m → Euclid m := convolution ρ' ψ L volume with hψ'_def
  have hψ'apply : ∀ w, ψ' w = ∫ t, ρ' t • ψ (w - t) := by
    intro w
    rw [hψ'_def, convolution_def]
    simp [L]
  -- support
  obtain ⟨r₁, hr₁r, hr₁⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψr
  have hsupp : support ψ' ⊆ closedBall 0 (r₁ + ε) := by
    intro w hw
    rw [Function.mem_support, hψ'apply] at hw
    by_contra hcon
    apply hw
    have hzero : ∀ t, ρ' t • ψ (w - t) = 0 := by
      intro t
      by_cases h1 : ρ' t = 0
      · simp [h1]
      by_cases h2 : ψ (w - t) = 0
      · simp [h2]
      exfalso
      apply hcon
      have ht : ‖t‖ ≤ ε := by
        by_contra h
        push Not at h
        exact h1 (hρε (-t) (by rwa [norm_neg]))
      have hwt : w - t ∈ ball (0 : Euclid m) r₁ := hr₁ (subset_tsupport ψ h2)
      rw [mem_ball_zero_iff] at hwt
      rw [mem_closedBall_zero_iff]
      calc ‖w‖ = ‖(w - t) + t‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - t‖ + ‖t‖ := norm_add_le _ _
        _ ≤ r₁ + ε := by linarith
    simp [hzero]
  have htsupp : tsupport ψ' ⊆ closedBall 0 (r₁ + ε) := closure_minimal hsupp isClosed_closedBall
  -- derivative of `ψ'` and its trace
  have hderiv : ∀ w, fderiv ℝ ψ' w =
      convolution ρ' (fderiv ℝ ψ) (ContinuousLinearMap.precompR (Euclid m) L) volume w := fun w =>
    (hψcs.hasFDerivAt_convolution_right L hρ'i.locallyIntegrable
      (hψ.of_le (by exact_mod_cast le_top)) w).fderiv
  have hG' : ∀ w, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
      ∫ z, ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap := by
    intro w
    have hint : Integrable (fun t => ρ' t • fderiv ℝ ψ (w - t)) :=
      (hψcs.fderiv (𝕜 := ℝ)).convolutionExists_right (ContinuousLinearMap.precompR (Euclid m) L)
        hρ'i.locallyIntegrable (hψ.continuous_fderiv (by simp)) w
    have h1 : fderiv ℝ ψ' w = ∫ t, ρ' t • fderiv ℝ ψ (w - t) := by
      rw [hderiv w, convolution_def]
      congr 1
    rw [← hTr, h1, ← ContinuousLinearMap.integral_comp_comm Tr hint,
      ← integral_neg_eq_self
        (fun z => ρ z * LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ (w + z)).toLinearMap) volume]
    congr 1
    funext t
    rw [map_smul, smul_eq_mul, hTr, ← sub_eq_add_neg]
  refine ⟨ψ', ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ'cs.contDiff_convolution_left L hρ'smooth hψ.continuous.locallyIntegrable
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp
  · exact htsupp.trans (closedBall_subset_ball (by linarith))
  · intro v
    rw [hψ'apply]
    refine (norm_integral_le_of_norm_le hρ'i (ae_of_all _ fun t => ?_)).trans hρ'1.le
    rw [norm_smul, Real.norm_of_nonneg (hρ0 _)]
    exact mul_le_of_le_one_right (hρ0 _) (hψ1 _)
  · -- Fubini
    set u : Euclid m → ℝ := F.indicator (fun _ => (1 : ℝ)) with hu
    set G : Euclid m → ℝ :=
      fun v => LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ v).toLinearMap with hG
    have hGeq : G = Tr ∘ fderiv ℝ ψ := by
      funext v
      simp only [G, Function.comp_apply, hTr]
    have hGc : Continuous G := by
      rw [hGeq]; exact Tr.continuous.comp (hψ.continuous_fderiv (by simp))
    have hGcs : HasCompactSupport G := by
      rw [hGeq]; exact (hψcs.fderiv (𝕜 := ℝ)).comp_left (map_zero Tr)
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGcs
    have hum : Measurable u := measurable_const.indicator hF
    have hu01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1 := fun x => by
      by_cases hx : x ∈ F <;> simp [u, hx]
    set g : Euclid m × Euclid m → ℝ := fun p => ρ p.2 * u (p.1 - p.2) * G p.1 with hg
    have hgm : Measurable g :=
      ((hρc.measurable.comp measurable_snd).mul
        (hum.comp (measurable_fst.sub measurable_snd))).mul (hGc.measurable.comp measurable_fst)
    have hgi : Integrable g (volume.prod volume) := by
      refine Integrable.mono' (hGi.norm.mul_prod hρi) hgm.aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      have h1 := hu01 (p.1 - p.2)
      have h2 := hρ0 p.2
      simp only [g, Real.norm_eq_abs, abs_mul, abs_of_nonneg h2, abs_of_nonneg h1.1]
      nlinarith [mul_nonneg (mul_nonneg h2 (abs_nonneg (G p.1))) (sub_nonneg.mpr h1.2)]
    have hT : MeasurePreserving (fun p : Euclid m × Euclid m => (p.1 + p.2, p.2))
        (volume.prod volume) (volume.prod volume) := measurePreserving_add_prod volume volume
    have hgTi : Integrable (fun p : Euclid m × Euclid m => g (p.1 + p.2, p.2))
        (volume.prod volume) :=
      (hT.integrable_comp hgm.aestronglyMeasurable).mpr hgi
    have hgT : ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) =
        ∫ p, g p ∂(volume.prod volume) := by
      have := integral_map (μ := volume.prod volume) hT.measurable.aemeasurable
        (f := g) (by rw [hT.map_eq]; exact hgm.aestronglyMeasurable)
      rw [hT.map_eq] at this
      exact this.symm
    have hLHS : ∫ v, (∫ z, ρ z * u (v - z)) * G v = ∫ p, g p ∂(volume.prod volume) := by
      rw [integral_prod g hgi]
      congr 1
      funext v
      rw [← integral_mul_const]
    have hRHS : ∫ w in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ ψ' w).toLinearMap =
        ∫ p, g (p.1 + p.2, p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hgTi, ← integral_indicator hF]
      congr 1
      funext w
      have h1 : ∀ z, g (w + z, z) = u w * (ρ z * G (w + z)) := fun z => by
        simp only [g, add_sub_cancel_right]
        ring
      dsimp only
      simp only [h1]
      rw [integral_const_mul, ← hG' w]
      by_cases hw : w ∈ F <;> simp [u, hw]
    exact hLHS.trans (hgT.symm.trans hRHS.symm)

/-- Gradient bound for a mollified indicator (Simon Ch. 2, 2.5; step 3 of the perimeter
compactness used for the zero-scale limit planes of 7.5).  Let `ρ ≥ 0` be `C^∞` with `∫ ρ = 1` and
`ρ = 0` off `B̄_ε(0)`, and let `∫_F div φ ≤ c` for every `C^∞` field `φ` with compact support in
`B_{r+ε}(0)` and `|φ| ≤ 1`.  Then `f = ρ ⋆ 1_F` is `C^∞` and `∫_{B_r(0)} |Df| ≤ c`.  As `ρ` has
compact support and `1_F` is locally integrable, `f` is `C^∞`
(`HasCompactSupport.contDiff_convolution_left`).  For a test field `ψ` in `B_r(0)` with
`|ψ| ≤ 1`, `codim1_zsl_pc_mollify_test_field` gives a test field `ψ'` in `B_{r+ε}(0)` with
`|ψ'| ≤ 1` and `∫ f div ψ = ∫_F div ψ' ≤ c`, and `codim1_zsl_pc_smooth_grad_bound` turns these
bounds into `∫_{B_r(0)} |Df| ≤ c`. -/
theorem Submission.codim1_zsl_pc_mollify_grad_bound : ∀ (m : ℕ) (F : Set (Euclid m)) (ρ : Euclid m → ℝ) (r ε c : ℝ), MeasurableSet F → ContDiff ℝ (⊤ : ℕ∞) ρ → (∀ z, 0 ≤ ρ z) → (∀ z, ε < ‖z‖ → ρ z = 0) → ∫ z, ρ z = 1 → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (r + ε) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) ∧ ∫⁻ v in ball (0 : Euclid m) r, ‖fderiv ℝ (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) v‖ₑ ≤ ENNReal.ofReal c := by
  intro m F ρ r ε c hF hρ hρ0 hρs hρ1 hP
  -- `f = ρ ⋆ 1_F` is `C^∞`: `ρ` is `C^∞` with support in `B̄_ε(0)`, `1_F` is locally integrable
  have hρc : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid m) ε) fun z hz => hρs z ?_
    simpa [mem_closedBall, dist_zero_right, not_le] using hz
  have hli : LocallyIntegrable (F.indicator (fun _ => (1 : ℝ))) volume :=
    (locallyIntegrable_const (1 : ℝ)).indicator hF
  have hconv : (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z))
      = convolution ρ (F.indicator (fun _ => (1 : ℝ))) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext v
    simp [convolution_def, smul_eq_mul]
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun v => ∫ z, ρ z * F.indicator (fun _ => (1 : ℝ)) (v - z)) := by
    rw [hconv]
    exact hρc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hρ hli
  refine ⟨hsmooth, Submission.codim1_zsl_pc_smooth_grad_bound m _ r c hsmooth ?_⟩
  -- a test field `ψ` in `B_r(0)` against `f` is a test field `ψ'` in `B_{r+ε}(0)` against `1_F`
  intro ψ hψ hψc hψs hψ1
  obtain ⟨ψ', hψ', hψ'c, hψ's, hψ'1, heq⟩ :=
    Submission.codim1_zsl_pc_mollify_test_field m F ρ ψ r ε hF hρ hρ0 hρs hρ1 hψ hψc hψs hψ1
  rw [heq]
  exact hP ψ' hψ' hψ'c hψ's hψ'1

/-- Translation estimate for sets of locally finite perimeter: if `∫_F div φ ≤ c` for all smooth
fields `φ` with `|φ| ≤ 1` and compact support in `B_{R+2}(0)`, then
`L^m(((F − h) Δ F) ∩ B_R(0)) ≤ c|h|` for `|h| ≤ 1`.  The left side is
`∫_{B_R}|1_F(v + h) − 1_F(v)| dv`, and `c ≥ 0` (test with `φ = 0`).  Given `η > 0`,
`codim1_zsl_pc_mollify_indicator_l1` gives a radius `δ`; a normalized bump `ρ` of radius
`s = min(δ, 1/2)` mollifies `1_F` to a smooth `f` with `∫_{B_{R+1}}‖Df‖ ≤ c`
(`codim1_zsl_pc_mollify_grad_bound`, since `B_{R+1+s} ⊆ B_{R+2}`) and `∫_{B_{R+1}}|f − 1_F| ≤ η`.
By `codim1_zsl_pc_smooth_translate_l1`, `∫_{B_R}|f(v + h) − f(v)| ≤ c|h|`; the triangle inequality
and translation invariance of `L^m` bound the left side by `c|h| + 2η`. -/
theorem Submission.codim1_zsl_pc_translation_estimate : ∀ (m : ℕ) (F : Set (Euclid m)) (R c : ℝ), MeasurableSet F → (∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball (0 : Euclid m) (R + 2) → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (c * ‖h‖) := by
  intro m F R c hF hc h hh
  -- `0 ≤ c`, by testing the hypothesis with `φ = 0`.
  have hc0 : 0 ≤ c := by
    have h0 := hc (fun _ => (0 : Euclid m)) contDiff_const HasCompactSupport.zero
      (by simp [tsupport]) (by simp)
    simpa using h0
  -- The measure of the symmetric difference as an `L¹` norm of indicators.
  have hχm : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hS : MeasurableSet (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
    (measurable_add_const h hF).symmDiff hF
  have hL : volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R)
      = ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
    rw [← Measure.restrict_apply hS, ← lintegral_indicator_one hS]
    refine lintegral_congr (fun v => ?_)
    by_cases h1 : v + h ∈ F <;> by_cases h2 : v ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  rw [hL]
  -- An `ε` of room: it suffices to prove the bound up to `ε = η + η`.
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε _ => ?_)
  obtain ⟨η, hη, hηε⟩ : ∃ η : ℝ, 0 < η ∧ η + η = (ε : ℝ) :=
    ⟨(ε : ℝ) / 2, half_pos (by exact_mod_cast hε), add_halves _⟩
  -- The `L¹`-approximation radius `δ` on `B_{R+1}`, and the mollifier radius `s ≤ min(δ, 1/2)`.
  obtain ⟨δ, hδ, hmoll⟩ := Submission.codim1_zsl_pc_mollify_indicator_l1 m F (R + 1) η hF hη
  obtain ⟨s, hs, hsδ, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ δ ∧ s ≤ 1 / 2 :=
    ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_left _ _, min_le_right _ _⟩
  -- A smooth mollifier supported in `closedBall 0 s`: a normalized bump function.
  obtain ⟨ρ, hρ_smooth, hρ_nn, hρ_supp, hρ_int⟩ : ∃ ρ : Euclid m → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ (∀ z, 0 ≤ ρ z) ∧ (∀ z, s < ‖z‖ → ρ z = 0) ∧ ∫ z, ρ z = 1 := by
    obtain ⟨b, hb_out⟩ : ∃ b : ContDiffBump (0 : Euclid m), b.rOut = s :=
      ⟨⟨s / 2, s, half_pos hs, half_lt_self hs⟩, rfl⟩
    have hbi : Integrable b := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    have hbpos : 0 < ∫ x, b x := by
      rw [integral_pos_iff_support_of_nonneg (fun x => b.nonneg' x) hbi, b.support_eq, hb_out]
      exact measure_ball_pos volume 0 hs
    refine ⟨fun x => (∫ y, b y)⁻¹ * b x, contDiff_const.mul b.contDiff,
      fun z => mul_nonneg (inv_nonneg.mpr hbpos.le) (b.nonneg' z), fun z hz => ?_, ?_⟩
    · have hz0 : b z = 0 := b.zero_of_le_dist (by rw [dist_zero_right, hb_out]; exact hz.le)
      simp [hz0]
    · show ∫ z, (∫ y, b y)⁻¹ * b z = 1
      rw [integral_const_mul]
      exact inv_mul_cancel₀ hbpos.ne'
  have hρ_supp' : ∀ z, δ < ‖z‖ → ρ z = 0 := fun z hz => hρ_supp z (lt_of_le_of_lt hsδ hz)
  -- The mollified indicator `f`: smooth, `∫_{B_{R+1}} ‖Df‖ ≤ c`, and `L¹`-close to `1_F`.
  obtain ⟨f, hf_smooth, hf_grad, hE⟩ : ∃ f : Euclid m → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∫⁻ v in ball (0 : Euclid m) (R + 1), ‖fderiv ℝ f v‖ₑ ≤ ENNReal.ofReal c ∧
      ∫⁻ v in ball (0 : Euclid m) (R + 1), ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
        ≤ ENNReal.ofReal η := by
    obtain ⟨h1, h2⟩ := Submission.codim1_zsl_pc_mollify_grad_bound m F ρ (R + 1) s c hF
      hρ_smooth hρ_nn hρ_supp hρ_int (fun φ hφ1 hφ2 hφ3 hφ4 =>
        hc φ hφ1 hφ2 (hφ3.trans (ball_subset_ball (by linarith))) hφ4)
    exact ⟨_, h1, h2, hmoll ρ hρ_smooth.continuous hρ_nn hρ_supp' hρ_int⟩
  have hfm : Measurable f := hf_smooth.continuous.measurable
  -- The translation estimate for the smooth function `f`.
  have htr := Submission.codim1_zsl_pc_smooth_translate_l1 m f h R
    (hf_smooth.of_le (by exact_mod_cast le_top))
  have hT : ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ ≤ ENNReal.ofReal (c * ‖h‖) := by
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ
        ≤ ‖h‖ₑ * ∫⁻ w in ball (0 : Euclid m) (R + ‖h‖), ‖fderiv ℝ f w‖ₑ := htr
      _ ≤ ‖h‖ₑ * ENNReal.ofReal c := by
        gcongr
        exact (lintegral_mono_set (ball_subset_ball (by linarith))).trans hf_grad
      _ = ENNReal.ofReal (c * ‖h‖) := by
        rw [ENNReal.ofReal_mul hc0, ofReal_norm, mul_comm]
  -- The two `L¹` error terms, at `v + h` and at `v`.
  have hsub : ball (0 : Euclid m) R ⊆ (fun x => x + h) ⁻¹' ball (0 : Euclid m) (R + 1) := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    show v + h ∈ ball (0 : Euclid m) (R + 1)
    rw [mem_ball_zero_iff]
    calc ‖v + h‖ ≤ ‖v‖ + ‖h‖ := norm_add_le _ _
      _ < R + 1 := by linarith
  have h9b : ∫⁻ v in ball (0 : Euclid m) R,
      ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤ ENNReal.ofReal η := by
    calc ∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        ≤ ∫⁻ v in (fun x => x + h) ⁻¹' ball (0 : Euclid m) (R + 1),
            ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := lintegral_mono_set hsub
      _ = ∫⁻ w in ball (0 : Euclid m) (R + 1), ‖f w - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
          (measurePreserving_add_right volume h).setLIntegral_comp_preimage_emb
            (measurableEmbedding_addRight h)
            (fun w => ‖f w - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) _
      _ ≤ ENNReal.ofReal η := hE
  have h9a : ∫⁻ v in ball (0 : Euclid m) R, ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
      ≤ ENNReal.ofReal η :=
    (lintegral_mono_set (ball_subset_ball (by linarith))).trans hE
  -- Pointwise triangle inequality.
  have hpt : ∀ v, ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ ≤
      ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ + ‖f (v + h) - f v‖ₑ
        + ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
    intro v
    have e : F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v
        = -(f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)) + (f (v + h) - f v)
          + (f v - F.indicator (fun _ => (1 : ℝ)) v) := by ring
    rw [e, ← enorm_neg (f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h))]
    exact enorm_add₃_le
  have hg3m : Measurable (fun v => ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ) :=
    (hfm.sub hχm).enorm
  have hg2m : Measurable (fun v => ‖f (v + h) - f v‖ₑ) :=
    ((hfm.comp (measurable_add_const h)).sub hfm).enorm
  -- Conclusion: the left side is at most `η + c|h| + η`.
  calc ∫⁻ v in ball (0 : Euclid m) R,
        ‖F.indicator (fun _ => (1 : ℝ)) (v + h) - F.indicator (fun _ => (1 : ℝ)) v‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R,
          (‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ + ‖f (v + h) - f v‖ₑ
            + ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ) := lintegral_mono hpt
    _ = (∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ)
          + (∫⁻ v in ball (0 : Euclid m) R, ‖f (v + h) - f v‖ₑ)
          + ∫⁻ v in ball (0 : Euclid m) R, ‖f v - F.indicator (fun _ => (1 : ℝ)) v‖ₑ := by
        rw [lintegral_add_right _ hg3m, lintegral_add_right _ hg2m]
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (c * ‖h‖) + ENNReal.ofReal η :=
        add_le_add (add_le_add h9b hT) h9a
    _ = ENNReal.ofReal (c * ‖h‖) + (ENNReal.ofReal η + ENNReal.ofReal η) := by ring
    _ = ENNReal.ofReal (c * ‖h‖) + ε := by
        rw [← ENNReal.ofReal_add hη.le hη.le, hηε, ENNReal.ofReal_coe_nnreal]
/-- **Cube averages under a translation estimate** (Kolmogorov–Riesz averaging step): if
`Lᵐ(((F − h) Δ F) ∩ B_R(0)) ≤ C|h|` for `|h| ≤ 1`, then `1_F` is `KCδ`-close in `L¹(B_R(0))` to its
averages over the grid cubes `Q_δ(v)` of side `δ`, `δ√m ≤ 1`.  `Q_δ(v)` is a box of volume `δᵐ`
inside `B̄_{√m δ}(v)`, so `|1_F(v) − a(v)| ≤ δ⁻ᵐ ∫_{|h| ≤ √m δ} |1_F(v) − 1_F(v + h)| dh`; Tonelli
over `v ∈ B_R(0)` and `Lᵐ(B̄_{√m δ}(0)) = (√m δ)ᵐ Lᵐ(B₁(0))` give `K = (√m)^{m+1} Lᵐ(B₁(0))`. -/
theorem Submission.codim1_zsl_pc_cube_average_bound : ∀ (m : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : Set (Euclid m)) (R C δ : ℝ), MeasurableSet F → 0 ≤ C → 0 < δ → δ * Real.sqrt m ≤ 1 → (∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ ≤ ENNReal.ofReal (K * C * δ) := by
  intro m
  refine ⟨Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal, by positivity, ?_⟩
  intro F R C δ hF hC hδ hδm hsd
  have hu_meas : Measurable (F.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hF
  have hs0 : 0 ≤ Real.sqrt m * δ := by positivity
  have hs1 : Real.sqrt m * δ ≤ 1 := by rw [mul_comm]; exact hδm
  have hδm0 : 0 < δ ^ m := pow_pos hδ m
  -- Step 1: the cube `Q v` is (the preimage of) a half-open box of side `δ`
  have hQbox : ∀ v : Euclid m, {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} =
      (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) := by
    intro v
    ext w
    simp only [Set.mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico]
    refine forall_congr' fun j => ?_
    rw [Int.floor_eq_iff, le_div_iff₀ hδ, div_lt_iff₀ hδ]
  have hbox_meas : ∀ v : Euclid m,
      MeasurableSet (Set.pi univ fun j => Ico ((⌊v j / δ⌋ : ℝ) * δ) (((⌊v j / δ⌋ : ℝ) + 1) * δ)) :=
    fun v => MeasurableSet.univ_pi fun j => measurableSet_Ico
  have hQvol : ∀ v : Euclid m,
      volume {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} = ENNReal.ofReal (δ ^ m) := by
    intro v
    rw [hQbox v, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (hbox_meas v).nullMeasurableSet, Real.volume_pi_Ico]
    have : ∀ j : Fin m, ((⌊v j / δ⌋ : ℝ) + 1) * δ - (⌊v j / δ⌋ : ℝ) * δ = δ := fun j => by ring
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.ofReal_pow hδ.le]
  -- Step 2: the cube lies in the closed ball of radius `√m δ` about `v`
  have hQball : ∀ v : Euclid m,
      {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋} ⊆ closedBall v (Real.sqrt m * δ) := by
    intro v w hw
    rw [hQbox v] at hw
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_implies, mem_Ico] at hw
    rw [mem_closedBall, EuclideanSpace.dist_eq]
    have hcoord : ∀ j, dist (w j) (v j) ^ 2 ≤ δ ^ 2 := by
      intro j
      have hwj := hw j
      have h1 := Int.floor_le (v j / δ)
      have h2 := Int.lt_floor_add_one (v j / δ)
      rw [le_div_iff₀ hδ] at h1
      rw [div_lt_iff₀ hδ] at h2
      have hab : |w j - v j| ≤ δ := by
        rw [abs_le]; constructor <;> nlinarith [hwj.1, hwj.2]
      rw [Real.dist_eq]
      exact pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc Real.sqrt (∑ j, dist (w j) (v j) ^ 2) ≤ Real.sqrt (∑ _j : Fin m, δ ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => hcoord j)
      _ = Real.sqrt m * δ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg m), Real.sqrt_sq hδ.le]
  -- Step 3: pointwise bound by an average of differences over the closed ball
  have hpt : ∀ (v : Euclid m) (Q : Set (Euclid m)), volume Q = ENNReal.ofReal (δ ^ m) →
      Q ⊆ closedBall v (Real.sqrt m * δ) →
      ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
    intro v Q hQv hQb
    have hQfin : volume Q ≠ ∞ := by rw [hQv]; exact ENNReal.ofReal_ne_top
    have : IsFiniteMeasure (volume.restrict Q) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hQfin.lt_top⟩
    have hint_c : Integrable (fun _ : Euclid m => F.indicator (fun _ => (1 : ℝ)) v)
        (volume.restrict Q) := integrable_const _
    have hint_u : Integrable (F.indicator (fun _ => (1 : ℝ))) (volume.restrict Q) :=
      (integrable_const (1 : ℝ)).indicator hF
    have h1 : ∫ w in Q, F.indicator (fun _ => (1 : ℝ)) w = (volume (F ∩ Q)).toReal := by
      rw [integral_indicator_const (1 : ℝ) hF, smul_eq_mul, mul_one,
        measureReal_restrict_apply hF, measureReal_def]
    have h2 : F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m =
        (δ ^ m)⁻¹ * ∫ w in Q, (F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w) := by
      rw [integral_sub hint_c hint_u, setIntegral_const, h1, measureReal_def, hQv,
        ENNReal.toReal_ofReal hδm0.le, smul_eq_mul, mul_sub, ← mul_assoc,
        inv_mul_cancel₀ hδm0.ne', one_mul, div_eq_inv_mul]
    have h3 : ‖F.indicator (fun _ => (1 : ℝ)) v - (volume (F ∩ Q)).toReal / δ ^ m‖ₑ ≤
        ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ := by
      rw [h2, enorm_mul, Real.enorm_eq_ofReal (inv_nonneg.2 hδm0.le)]
      exact mul_le_mul' le_rfl (enorm_integral_le_lintegral_enorm _)
    have h4 : ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ ≤
        ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
      calc ∫⁻ w in Q, ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ
          ≤ ∫⁻ w in closedBall v (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ :=
            lintegral_mono_set hQb
        _ = ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
          rw [← lintegral_indicator measurableSet_closedBall,
            ← lintegral_indicator measurableSet_closedBall,
            ← lintegral_add_left_eq_self ((closedBall v (Real.sqrt m * δ)).indicator fun w =>
              ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) w‖ₑ) v]
          refine lintegral_congr fun h => ?_
          have hmem : v + h ∈ closedBall v (Real.sqrt m * δ) ↔
              h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ) := by
            rw [mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm, add_sub_cancel_left,
              sub_zero]
          by_cases hh : h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ)
          · rw [indicator_of_mem (hmem.2 hh), indicator_of_mem hh]
          · rw [indicator_of_notMem (mt hmem.1 hh), indicator_of_notMem hh]
    exact h3.trans (mul_le_mul' le_rfl h4)
  -- Step 4: integrate, swap the order of integration, and use the hypothesis
  have hind : ∀ v h : Euclid m,
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ =
        (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v := by
    intro v h
    by_cases h1 : v ∈ F <;> by_cases h2 : v + h ∈ F <;>
      simp [h1, h2, Set.mem_symmDiff]
  have hinner : ∀ h ∈ closedBall (0 : Euclid m) (Real.sqrt m * δ),
      ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ ≤
        ENNReal.ofReal (C * (Real.sqrt m * δ)) := by
    intro h hh
    have hh' : ‖h‖ ≤ Real.sqrt m * δ := mem_closedBall_zero_iff.1 hh
    calc ∫⁻ v in ball (0 : Euclid m) R,
          ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ
        = ∫⁻ v in ball (0 : Euclid m) R, (symmDiff ((fun v => v + h) ⁻¹' F) F).indicator 1 v :=
          lintegral_congr fun v => hind v h
      _ ≤ (volume.restrict (ball (0 : Euclid m) R)) (symmDiff ((fun v => v + h) ⁻¹' F) F) :=
          lintegral_indicator_one_le _
      _ = volume (symmDiff ((fun v => v + h) ⁻¹' F) F ∩ ball (0 : Euclid m) R) :=
          Measure.restrict_apply' measurableSet_ball
      _ ≤ ENNReal.ofReal (C * ‖h‖) := hsd h (hh'.trans hs1)
      _ ≤ ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh' hC)
  have hmeas2 : Measurable (uncurry fun (v h : Euclid m) =>
      ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ) := by
    have : Measurable fun p : Euclid m × Euclid m =>
        F.indicator (fun _ => (1 : ℝ)) p.1 - F.indicator (fun _ => (1 : ℝ)) (p.1 + p.2) :=
      (hu_meas.comp measurable_fst).sub (hu_meas.comp (measurable_fst.add measurable_snd))
    exact this.enorm
  have hV1fin : volume (ball (0 : Euclid m) 1) ≠ ∞ := measure_ball_lt_top.ne
  calc ∫⁻ v in ball (0 : Euclid m) R, ‖F.indicator (fun _ => (1 : ℝ)) v -
        (volume (F ∩ {w : Euclid m | ∀ j, ⌊w j / δ⌋ = ⌊v j / δ⌋})).toReal / δ ^ m‖ₑ
      ≤ ∫⁻ v in ball (0 : Euclid m) R, ENNReal.ofReal ((δ ^ m)⁻¹) *
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_mono fun v => hpt v _ (hQvol v) (hQball v)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ v in ball (0 : Euclid m) R,
          ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ∫⁻ v in ball (0 : Euclid m) R,
            ‖F.indicator (fun _ => (1 : ℝ)) v - F.indicator (fun _ => (1 : ℝ)) (v + h)‖ₑ := by
        rw [lintegral_lintegral_swap (μ := volume.restrict (ball (0 : Euclid m) R))
          (ν := volume.restrict (closedBall (0 : Euclid m) (Real.sqrt m * δ)))
          hmeas2.aemeasurable]
    _ ≤ ENNReal.ofReal ((δ ^ m)⁻¹) * ∫⁻ h in closedBall (0 : Euclid m) (Real.sqrt m * δ),
          ENNReal.ofReal (C * (Real.sqrt m * δ)) :=
        mul_le_mul' le_rfl (setLIntegral_mono measurable_const hinner)
    _ = ENNReal.ofReal ((δ ^ m)⁻¹) * (ENNReal.ofReal (C * (Real.sqrt m * δ)) *
          (ENNReal.ofReal ((Real.sqrt m * δ) ^ m) * volume (ball (0 : Euclid m) 1))) := by
        rw [setLIntegral_const, Measure.addHaar_closedBall _ _ hs0, finrank_euclideanSpace_fin]
    _ = ENNReal.ofReal (Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ) := by
        have e1 : Real.sqrt m ^ (m + 1) * (volume (ball (0 : Euclid m) 1)).toReal * C * δ =
            ((δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m) *
              (volume (ball (0 : Euclid m) 1)).toReal := by
          rw [mul_pow]
          field_simp
          ring
        rw [e1, ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ)) * (Real.sqrt m * δ) ^ m)
            (by positivity), ENNReal.ofReal_toReal hV1fin,
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹ * (C * (Real.sqrt m * δ))) (by positivity),
          ENNReal.ofReal_mul (p := (δ ^ m)⁻¹) (by positivity)]
        ring
/-- Common convergent subsequence for countably many bounded real sequences.  The points
`xᵢ = (b_k(i))_k` lie in the product `Π_k [-M_k, M_k]`, which is compact (Tychonoff,
`isCompact_univ_pi`); `ℝ^ι` is first countable since `ι` is countable, so `IsCompact.tendsto_subseq`
gives a strictly increasing `σ` and a limit `a` with `x_{σ(i)} → a`.  Evaluation at `k` is
continuous, hence `b_k(σ(i)) → a(k)` for every `k`. -/
theorem Submission.codim1_zsl_pc_diagonal_subseq : ∀ (ι : Type) [Countable ι] (b : ι → ℕ → ℝ) (M : ι → ℝ), (∀ k i, |b k i| ≤ M k) → ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∀ k, ∃ L : ℝ, Tendsto (fun i => b k (σ i)) atTop (𝓝 L) := by
  intro ι _ b M hb
  have hS : IsCompact (Set.pi univ (fun k => Icc (-M k) (M k))) :=
    isCompact_univ_pi (fun k => isCompact_Icc)
  have hx : ∀ i, (fun k => b k i) ∈ Set.pi univ (fun k => Icc (-M k) (M k)) := by
    intro i
    rw [Set.mem_univ_pi]
    intro k
    exact Set.mem_Icc.mpr (abs_le.mp (hb k i))
  obtain ⟨a, -, σ, hσ, hlim⟩ := hS.tendsto_subseq hx
  exact ⟨σ, hσ, fun k => ⟨a k, ((continuous_apply k).tendsto a).comp hlim⟩⟩
/-- Sets that are Cauchy in measure on every ball have a subsequence converging in measure on
every ball to a measurable set.  With `N_l` chosen for `R = l + 1`, `η = 2⁻ˡ`, the subsequence
`σ(l) = l + Σ_{k ≤ l} N_k` makes `E_l = (F_{σ(l+1)} Δ F_{σ(l)}) ∩ B_{l+1}(0)` summable in measure,
so by Borel–Cantelli (`ae_eventually_notMem`) a.e. `v` lies in only finitely many `E_l`.  For such
`v`, membership in `F_{σ(l)}` is eventually constant and equals membership in the liminf
`F' = ⋃_{l₀} ⋂_{l ≥ l₀} F_{σ(l)}`.  Continuity from above (`tendsto_measure_iInter_atTop`) on the
finite-measure ball `B_R(0)`, applied to `⋃_{l ≥ l₀} (F_{σ(l)} Δ F') ∩ B_R(0)`, concludes. -/
theorem Submission.codim1_zsl_pc_cauchy_limit_set : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j → volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hF hC
  -- Fast subsequence: `N l` works for `R = l + 1`, `η = 2⁻ˡ`, and `N l ≤ σ l'` for `l ≤ l'`.
  have hN : ∀ l : ℕ, ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F i) (F j) ∩ ball (0 : Euclid m) ((l : ℝ) + 1)) ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ l) :=
    fun l => hC ((l : ℝ) + 1) (by positivity) ((1 / 2 : ℝ) ^ l) (by positivity)
  choose N hN using hN
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, ∀ l, σ l = l + ∑ k ∈ Finset.range (l + 1), N k :=
    ⟨_, fun _ => rfl⟩
  have hσmono : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro l
    simp only [hσ, Finset.sum_range_succ]
    omega
  have hσge : ∀ l l', l ≤ l' → N l ≤ σ l' := by
    intro l l' h
    have h1 : N l ≤ ∑ k ∈ Finset.range (l' + 1), N k :=
      Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    rw [hσ]
    omega
  -- The limit set: the points lying in `F (σ l)` for all large `l`.
  obtain ⟨F', hF'eq⟩ : ∃ F' : Set (Euclid m), F' = ⋃ l₀ : ℕ, ⋂ l : ℕ, ⋂ (_ : l₀ ≤ l), F (σ l) :=
    ⟨_, rfl⟩
  have hF'meas : MeasurableSet F' := by
    rw [hF'eq]
    exact MeasurableSet.iUnion fun l₀ => MeasurableSet.iInter fun l =>
      MeasurableSet.iInter fun _ => hF _
  have hF'mem : ∀ v, v ∈ F' ↔ ∃ l₀, ∀ l, l₀ ≤ l → v ∈ F (σ l) := by
    intro v
    rw [hF'eq]
    simp only [mem_iUnion, mem_iInter]
  -- The transition sets `E l` have summable measures.
  obtain ⟨E, hE⟩ : ∃ E : ℕ → Set (Euclid m), ∀ l,
      E l = symmDiff (F (σ (l + 1))) (F (σ l)) ∩ ball (0 : Euclid m) ((l : ℝ) + 1) :=
    ⟨_, fun _ => rfl⟩
  have hEle : ∀ l, volume (E l) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ l) := by
    intro l
    rw [hE]
    exact hN l _ _ (hσge l (l + 1) (Nat.le_succ l)) (hσge l l le_rfl)
  have hsum : ∑' l, volume (E l) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEle)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  -- Borel–Cantelli: a.e. `v` is eventually outside `F (σ l) Δ F'`.
  have hae : ∀ᵐ v ∂(volume : Measure (Euclid m)),
      ∀ᶠ l in atTop, v ∉ symmDiff (F (σ l)) F' := by
    filter_upwards [ae_eventually_notMem hsum] with v hv
    have hball : ∀ᶠ l : ℕ in atTop, v ∈ ball (0 : Euclid m) ((l : ℝ) + 1) := by
      obtain ⟨n, hn⟩ := exists_nat_gt ‖v‖
      filter_upwards [eventually_ge_atTop n] with l hl
      rw [mem_ball_zero_iff]
      have : (n : ℝ) ≤ l := Nat.cast_le.mpr hl
      linarith
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp (hv.and hball)
    have hstep : ∀ l, l₁ ≤ l → (v ∈ F (σ (l + 1)) ↔ v ∈ F (σ l)) := by
      intro l hl
      obtain ⟨h1, h2⟩ := hl₁ l hl
      rw [hE] at h1
      have h3 : v ∉ symmDiff (F (σ (l + 1))) (F (σ l)) := fun h => h1 (Set.mem_inter h h2)
      rw [Set.mem_symmDiff] at h3
      tauto
    have hconst : ∀ l, l₁ ≤ l → (v ∈ F (σ l) ↔ v ∈ F (σ l₁)) := by
      intro l hl
      induction l, hl using Nat.le_induction with
      | base => exact Iff.rfl
      | succ l hl ih => exact (hstep l hl).trans ih
    have hF'iff : v ∈ F' ↔ v ∈ F (σ l₁) := by
      rw [hF'mem]
      constructor
      · rintro ⟨l₀, hl₀⟩
        exact (hconst (max l₀ l₁) (le_max_right _ _)).mp (hl₀ _ (le_max_left _ _))
      · intro h
        exact ⟨l₁, fun l hl => (hconst l hl).mpr h⟩
    filter_upwards [eventually_ge_atTop l₁] with l hl
    rw [Set.mem_symmDiff]
    have := hconst l hl
    tauto
  refine ⟨σ, F', hσmono, hF'meas, fun R => ?_⟩
  -- Continuity from above for the tails `G l₀` inside the finite-measure ball `B_R(0)`.
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Set (Euclid m), ∀ l₀,
      G l₀ = ⋃ l : ℕ, ⋃ (_ : l₀ ≤ l), symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R :=
    ⟨_, fun _ => rfl⟩
  have hGmem : ∀ l₀ v, v ∈ G l₀ ↔ ∃ l, l₀ ≤ l ∧ v ∈ symmDiff (F (σ l)) F' ∩ ball (0 : Euclid m) R := by
    intro l₀ v
    rw [hG]
    simp only [mem_iUnion, exists_prop]
  have hGmeas : ∀ l₀, NullMeasurableSet (G l₀) volume := by
    intro l₀
    rw [hG]
    exact (MeasurableSet.iUnion fun l => MeasurableSet.iUnion fun _ =>
      ((hF _).symmDiff hF'meas).inter measurableSet_ball).nullMeasurableSet
  have hGanti : Antitone G := by
    intro a b hab v hv
    rw [hGmem] at hv ⊢
    obtain ⟨l, hl, hv⟩ := hv
    exact ⟨l, hab.trans hl, hv⟩
  have hGfin : ∃ i, volume (G i) ≠ ∞ := by
    refine ⟨0, ne_top_of_le_ne_top
      (measure_ball_lt_top (μ := volume) (x := (0 : Euclid m)) (r := R)).ne (measure_mono ?_)⟩
    intro v hv
    rw [hGmem] at hv
    obtain ⟨l, _, hv⟩ := hv
    exact hv.2
  have hGnull : volume (⋂ l₀, G l₀) = 0 := by
    refine measure_mono_null ?_ (ae_iff.mp hae)
    intro v hv
    rw [mem_iInter] at hv
    intro hev
    obtain ⟨l₁, hl₁⟩ := eventually_atTop.mp hev
    obtain ⟨l, hl, hvl⟩ := (hGmem l₁ v).mp (hv l₁)
    exact hl₁ l hl hvl.1
  have hGlim := tendsto_measure_iInter_atTop hGmeas hGanti hGfin
  rw [hGnull] at hGlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGlim (fun _ => zero_le) ?_
  intro l
  exact measure_mono (fun v hv => (hGmem l v).mpr ⟨l, le_rfl, hv⟩)

/-- Compactness from a uniform translation estimate: the precompactness part of Simon Ch. 2, 2.6,
proved with cube averages (Hanche-Olsen–Holden, Expo. Math. 28 (2010), Theorem 5).  The averages
`b_{(l,z)}(i) = Lᵐ(Fᵢ ∩ Q_{l,z})/δₗᵐ ∈ [0, 1]` over the grid cubes `Q_{l,z}` of side
`δₗ = 1/((l+1)(m+1))` all converge along one diagonal subsequence `σ₀`.  On `B_R`, the cube
average bound (`2KCδₗ`) and dominated convergence for the step functions make `F_{σ₀ i}` Cauchy
in measure, and `codim1_zsl_pc_cauchy_limit_set` extracts a further subsequence and the limit. -/
theorem Submission.codim1_zsl_pc_compact_of_translation : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ C : ℝ, ∀ᶠ i in atTop, ∀ h : Euclid m, ‖h‖ ≤ 1 → volume (symmDiff ((fun v => v + h) ⁻¹' F i) (F i) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal (C * ‖h‖)) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball (0 : Euclid m) R)) atTop (𝓝 0) := by
  intro m F hFm hT
  obtain ⟨K, hK0, hK⟩ := Submission.codim1_zsl_pc_cube_average_bound m
  -- Step 1: the scales `δ l`
  obtain ⟨δ, hδpos, hδsqrt, hδlim⟩ : ∃ δ : ℕ → ℝ, (∀ l, 0 < δ l) ∧ (∀ l, δ l * Real.sqrt m ≤ 1) ∧
      Tendsto δ atTop (𝓝 0) := by
    have hm1 : (0:ℝ) < (m:ℝ) + 1 := by positivity
    have hsq : Real.sqrt m ≤ (m:ℝ) + 1 := by
      have h1 : (m:ℝ) ≤ ((m:ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
      calc Real.sqrt m ≤ Real.sqrt (((m:ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt h1
        _ = (m:ℝ) + 1 := Real.sqrt_sq hm1.le
    refine ⟨fun l => 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1), fun l => by positivity, fun l => ?_, ?_⟩
    · have hl1 : (0:ℝ) < (l:ℝ) + 1 := by positivity
      calc 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * Real.sqrt m
          ≤ 1 / ((l:ℝ) + 1) / ((m:ℝ) + 1) * ((m:ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = 1 / ((l:ℝ) + 1) := div_mul_cancel₀ _ hm1.ne'
        _ ≤ 1 := by
            rw [div_le_one hl1]
            linarith [(Nat.cast_nonneg l : (0:ℝ) ≤ l)]
    · have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const ((m:ℝ) + 1)
      rwa [zero_div] at h
  -- Step 2: grid cubes and cube averages
  set Q : ℕ → (Fin m → ℤ) → Set (Euclid m) := fun l z => {w : Euclid m | ∀ j, ⌊w j / δ l⌋ = z j}
    with hQ
  have hQvol : ∀ l (z : Fin m → ℤ), volume (Q l z) ≤ ENNReal.ofReal (δ l ^ m) := by
    intro l z
    have hQeq : Q l z = (WithLp.ofLp : Euclid m → (Fin m → ℝ)) ⁻¹'
        (Set.pi univ fun j => Ico ((z j : ℝ) * δ l) (((z j : ℝ) + 1) * δ l)) := by
      ext w
      simp only [hQ, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
        Set.mem_Ico]
      refine forall_congr' fun j => ?_
      rw [Int.floor_eq_iff, le_div_iff₀ (hδpos l), div_lt_iff₀ (hδpos l)]
    rw [hQeq, (PiLp.volume_preserving_ofLp (Fin m)).measure_preimage
      (MeasurableSet.univ_pi fun j => measurableSet_Ico).nullMeasurableSet, Real.volume_pi_Ico]
    have hsub : ∀ j : Fin m, ((z j : ℝ) + 1) * δ l - (z j : ℝ) * δ l = δ l := fun j => by ring
    simp only [hsub, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (hδpos l).le m).ge
  set b : ℕ × (Fin m → ℤ) → ℕ → ℝ := fun k i => (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m
    with hb
  have hb01 : ∀ k i, 0 ≤ b k i ∧ b k i ≤ 1 := by
    intro k i
    have hpos : 0 < δ k.1 ^ m := pow_pos (hδpos k.1) m
    show 0 ≤ (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ∧
      (volume (F i ∩ Q k.1 k.2)).toReal / δ k.1 ^ m ≤ 1
    refine ⟨div_nonneg ENNReal.toReal_nonneg hpos.le, ?_⟩
    rw [div_le_one hpos]
    exact ENNReal.toReal_le_of_le_ofReal hpos.le
      ((measure_mono inter_subset_right).trans (hQvol k.1 k.2))
  -- Step 3: diagonal subsequence
  obtain ⟨σ₀, hσ₀, hL⟩ := Submission.codim1_zsl_pc_diagonal_subseq (ℕ × (Fin m → ℤ)) b
    (fun _ => 1) (fun k i => (abs_le.2 ⟨by linarith [(hb01 k i).1], (hb01 k i).2⟩ : |b k i| ≤ 1))
  choose L hL using hL
  have hL01 : ∀ k, 0 ≤ L k ∧ L k ≤ 1 := fun k =>
    ⟨ge_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).1),
      le_of_tendsto' (hL k) (fun i => (hb01 k (σ₀ i)).2)⟩
  -- measurability of the floor map and of coordinates
  have hfloor : Measurable (Int.floor : ℝ → ℤ) :=
    measurable_to_countable' fun n => by
      rw [Int.preimage_floor_singleton]
      exact measurableSet_Ico
  have hcoord : ∀ j : Fin m, Measurable (fun v : Euclid m => v j) := fun j =>
    (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 (Fin m → ℝ))
  -- Step 4: the subsequence is Cauchy in `L¹_loc`
  have hCauchy : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ i j : ℕ, N ≤ i → N ≤ j →
      volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R) ≤ ENNReal.ofReal η := by
    intro R hR η hη
    obtain ⟨C, hC⟩ := hT R hR
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 hC
    have hC'0 : (0:ℝ) ≤ max C 0 := le_max_right _ _
    have htrans : ∀ i, i₀ ≤ i → ∀ h : Euclid m, ‖h‖ ≤ 1 →
        volume (symmDiff ((fun v => v + h) ⁻¹' F (σ₀ i)) (F (σ₀ i)) ∩ ball (0 : Euclid m) R) ≤
          ENNReal.ofReal (max C 0 * ‖h‖) := by
      intro i hi h hh
      exact (hi₀ (σ₀ i) (le_trans hi (hσ₀.id_le i)) h hh).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
    have hKC : 0 ≤ K * max C 0 := mul_nonneg hK0 hC'0
    have hlim0 : Tendsto (fun l => K * max C 0 * δ l) atTop (𝓝 0) := by
      have h := hδlim.const_mul (K * max C 0)
      rwa [mul_zero] at h
    obtain ⟨l, hl⟩ := (hlim0.eventually (gt_mem_nhds (show (0:ℝ) < η / 4 by positivity))).exists
    have hKCδ : 0 ≤ K * max C 0 * δ l := mul_nonneg hKC (hδpos l).le
    set kf : Euclid m → (Fin m → ℤ) := fun v j => ⌊v j / δ l⌋ with hkf
    have hkf_meas : Measurable kf := by
      rw [measurable_pi_iff]
      intro j
      exact hfloor.comp ((hcoord j).div_const (δ l))
    have hmeasA : ∀ i, Measurable (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) := fun i =>
      (measurable_of_countable (fun z : Fin m → ℤ => ‖b (l, z) (σ₀ i) - L (l, z)‖ₑ)).comp hkf_meas
    have hmeasU : ∀ i, Measurable
        (fun v => ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ) := fun i =>
      ((measurable_const.indicator (hFm (σ₀ i))).sub
        ((measurable_of_countable (fun z : Fin m → ℤ => b (l, z) (σ₀ i))).comp hkf_meas)).enorm
    have hDCT : Tendsto (fun i => ∫⁻ v in ball (0 : Euclid m) R,
        ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
      have hbound : ∀ i, (fun v => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
          ≤ᵐ[volume.restrict (ball (0 : Euclid m) R)] (fun _ => (1 : ℝ≥0∞)) := by
        intro i
        refine ae_of_all _ (fun v => ?_)
        have h1 := hb01 (l, kf v) (σ₀ i)
        have h2 := hL01 (l, kf v)
        show ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤ 1
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_one.2
          (abs_le.2 ⟨by linarith [h1.1, h1.2, h2.1, h2.2], by linarith [h1.1, h1.2, h2.1, h2.2]⟩)
      have hfin : ∫⁻ _, (1 : ℝ≥0∞) ∂(volume.restrict (ball (0 : Euclid m) R)) ≠ ∞ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, one_mul]
        exact measure_ball_lt_top.ne
      have hlim : ∀ᵐ v ∂(volume.restrict (ball (0 : Euclid m) R)),
          Tendsto (fun i => ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ) atTop (𝓝 0) := by
        refine ae_of_all _ (fun v => ?_)
        have h := ((hL (l, kf v)).sub_const (L (l, kf v))).enorm
        rwa [sub_self, enorm_zero] at h
      have h := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hmeasA hbound
        hfin hlim
      rwa [lintegral_zero] at h
    obtain ⟨i₁, hi₁⟩ := ENNReal.tendsto_atTop_zero.1 hDCT (ENNReal.ofReal (η / 8))
      (ENNReal.ofReal_pos.2 (by positivity))
    refine ⟨max i₀ i₁, fun i j hi hj => ?_⟩
    have hi0 : i₀ ≤ i := le_trans (le_max_left _ _) hi
    have hj0 : i₀ ≤ j := le_trans (le_max_left _ _) hj
    have hi1 : i₁ ≤ i := le_trans (le_max_right _ _) hi
    have hj1 : i₁ ≤ j := le_trans (le_max_right _ _) hj
    have cube_i : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ i)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans i hi0)
    have cube_j : ∫⁻ v in ball (0 : Euclid m) R,
        ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ ≤
          ENNReal.ofReal (K * max C 0 * δ l) :=
      hK (F (σ₀ j)) R (max C 0) (δ l) (hFm _) hC'0 (hδpos l) (hδsqrt l) (htrans j hj0)
    have dct_i : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ i hi1
    have dct_j : ∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ ≤
        ENNReal.ofReal (η / 8) := hi₁ j hj1
    have tri : ∀ a b c d e : ℝ, ‖a - e‖ₑ ≤ ‖a - b‖ₑ + ‖b - c‖ₑ + ‖d - c‖ₑ + ‖e - d‖ₑ := by
      intro a b c d e
      have h1 : a - e = (a - b) + (b - c) - (d - c) - (e - d) := by ring
      rw [h1]
      exact enorm_sub_le.trans (add_le_add (enorm_sub_le.trans (add_le_add (enorm_add_le _ _)
        le_rfl)) le_rfl)
    have hS : MeasurableSet (symmDiff (F (σ₀ i)) (F (σ₀ j))) := (hFm _).symmDiff (hFm _)
    have hpt : ∀ v, (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v ≤
        ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
          + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
          + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ := by
      intro v
      refine le_trans ?_ (tri _ _ _ _ _)
      by_cases h1 : v ∈ F (σ₀ i) <;> by_cases h2 : v ∈ F (σ₀ j) <;>
        simp [Set.mem_symmDiff, h1, h2]
    calc volume (symmDiff (F (σ₀ i)) (F (σ₀ j)) ∩ ball (0 : Euclid m) R)
        = ∫⁻ v in ball (0 : Euclid m) R,
            (symmDiff (F (σ₀ i)) (F (σ₀ j))).indicator (1 : Euclid m → ℝ≥0∞) v := by
          rw [lintegral_indicator_one hS, Measure.restrict_apply hS]
      _ ≤ ∫⁻ v in ball (0 : Euclid m) R,
            (‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ
              + ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ + ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ
              + ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) :=
          lintegral_mono hpt
      _ = (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ i)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ i)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ i) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R, ‖b (l, kf v) (σ₀ j) - L (l, kf v)‖ₑ)
            + (∫⁻ v in ball (0 : Euclid m) R,
              ‖(F (σ₀ j)).indicator (fun _ => (1:ℝ)) v - b (l, kf v) (σ₀ j)‖ₑ) := by
          rw [lintegral_add_right _ (hmeasU j), lintegral_add_right _ (hmeasA j),
            lintegral_add_right _ (hmeasA i)]
      _ ≤ ENNReal.ofReal (K * max C 0 * δ l) + ENNReal.ofReal (η / 8) + ENNReal.ofReal (η / 8)
            + ENNReal.ofReal (K * max C 0 * δ l) :=
          add_le_add (add_le_add (add_le_add cube_i dct_i) dct_j) cube_j
      _ ≤ ENNReal.ofReal η := by
          have e2 : (0:ℝ) ≤ η / 8 := by positivity
          rw [← ENNReal.ofReal_add hKCδ e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8) e2,
            ← ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ K * max C 0 * δ l + η / 8 + η / 8) hKCδ]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  -- Step 5: extract a convergent subsequence
  obtain ⟨σ₁, F', hσ₁, hF', hlim⟩ :=
    Submission.codim1_zsl_pc_cauchy_limit_set m (fun i => F (σ₀ i)) (fun i => hFm _) hCauchy
  exact ⟨σ₀ ∘ σ₁, F', hσ₀.comp hσ₁, hF', hlim⟩
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

/-- **Compactness for sets of locally bounded perimeter** (Simon Ch. 2, 2.6, for the indicators
`uᵢ = 1_{Fᵢ}`).  If for each `R > 0` the perimeters of the `Fᵢ` in `B_R(0)` are eventually at most
`c(R)` (`∫_{Fᵢ} div φ ≤ c(R)` for smooth `φ` with `spt φ ⊆ B_R(0)` and `|φ| ≤ 1`), then a
subsequence converges in `L¹_loc`: `L^m((F_{σ i} Δ F') ∩ B_R(0)) → 0` for every `R`.
For `R > 0` and `i ≥ i_{R+2}`, `codim1_zsl_pc_translation_estimate` (steps 1–4: mollify, integrate
by parts, use the fundamental theorem of calculus, let `ε → 0`) turns the bound `c(R + 2)` into
`L^m(((Fᵢ − h) Δ Fᵢ) ∩ B_R(0)) ≤ c(R + 2)|h|` for `|h| ≤ 1`.  From this uniform local translation
estimate, `codim1_zsl_pc_compact_of_translation` (steps 5–8: cube averages, a diagonal
subsequence, a fast Cauchy subsequence and its `liminf` set) gives `σ` and `F'`. -/
theorem Submission.codim1_zsl_perimeter_compactness : ∀ (m : ℕ) (F : ℕ → Set (Euclid m)), (∀ i, MeasurableSet (F i)) → (∀ R : ℝ, 0 < R → ∃ c : ℝ, ∀ᶠ i in atTop, ∀ φ : Euclid m → Euclid m, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ ball 0 R → (∀ v, ‖φ v‖ ≤ 1) → ∫ v in F i, LinearMap.trace ℝ (Euclid m) (fderiv ℝ φ v).toLinearMap ≤ c) → ∃ (σ : ℕ → ℕ) (F' : Set (Euclid m)), StrictMono σ ∧ MeasurableSet F' ∧ ∀ R : ℝ, Tendsto (fun i => volume (symmDiff (F (σ i)) F' ∩ ball 0 R)) atTop (𝓝 0) := by
  intro m F hF hP
  -- Steps 5–8: a uniform local translation estimate gives `σ` and `F'`.
  refine Submission.codim1_zsl_pc_compact_of_translation m F hF fun R hR => ?_
  -- Steps 1–4: for `i ≥ i_{R+2}`, the perimeter bound `c(R + 2)` gives the estimate with `C = c`.
  obtain ⟨c, hc⟩ := hP (R + 2) (by linarith)
  exact ⟨c, hc.mono fun i hi =>
    Submission.codim1_zsl_pc_translation_estimate m (F i) R c (hF i) hi⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

theorem Submission.dgcr_bwd_graph_pullback_extDeriv : ∀ (m k : ℕ) (ι : Euclid (m + 1) →ₗᵢ[ℝ] Euclid (m + 1 + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (m + 1 + k)) (u : Euclid (m + 1) → Euclid k) (z : Euclid (m + 1 + k)) (ψ : DifferentialForm (Euclid (m + 1)) m) (v : Euclid (m + 1)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → IsSmoothForm ψ → DifferentiableAt ℝ u v → exteriorDerivative (affinePullbackForm (ContinuousLinearMap.adjoint ι.toContinuousLinearMap) (-(ContinuousLinearMap.adjoint ι.toContinuousLinearMap z)) ψ) (z + ι v + ι' (u v)) (fun i => fderiv ℝ (fun v => z + ι v + ι' (u v)) v (EuclideanSpace.single i (1 : ℝ))) = exteriorDerivative ψ v (fun i => EuclideanSpace.single i (1 : ℝ)) := by
  intro m k ι ι' u z ψ v hperp hψ hu
  -- `L := ι*` is a left inverse of `ι` and annihilates the orthogonal factor `ι'`.
  have hLι : ∀ v', ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι v') = v' := by
    intro v'
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact ι.inner_map_map v' y
  have hLι' : ∀ w, ContinuousLinearMap.adjoint ι.toContinuousLinearMap (ι' w) = 0 := by
    intro w
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_left, inner_zero_left, real_inner_comm]
    exact hperp y w
  -- Chain rule for the graph map `Φ v = z + ι v + ι' (u v)`.
  have hD : fderiv ℝ (fun v => z + ι v + ι' (u v)) v =
      ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp (fderiv ℝ u v) := by
    have hι : HasFDerivAt (fun v => ι v) ι.toContinuousLinearMap v :=
      ι.toContinuousLinearMap.hasFDerivAt
    have hι' : HasFDerivAt (fun v => ι' (u v)) (ι'.toContinuousLinearMap.comp (fderiv ℝ u v)) v :=
      ι'.toContinuousLinearMap.hasFDerivAt.comp v hu.hasFDerivAt
    have h1 := ((hasFDerivAt_const z v).add hι).add hι'
    rw [zero_add] at h1
    exact h1.fderiv
  -- `d` commutes with the affine pull-back; the base point is `v` and the frame is `eᵢ`.
  rw [exteriorDerivative_affinePullbackForm _ _ hψ]
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  · simp [map_add, hLι, hLι']
  · funext i
    simp [hD, hLι, hLι']

end GMT.Ch07
