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

/-- **The chosen approximate tangent plane** (Simon Ch. 3, Remark 1.5(1), used for 7.1.2).  If `Q`
is an approximate tangent space of `M` at `x` (Ch. 3, 1.4), then `approxTangentPlane n M x = Q`:
`Q` witnesses the existential in its definition, so it returns the chosen plane, which is an
approximate tangent space of `M` at `x` and hence equals `Q` by uniqueness. -/
theorem Submission.dpf_itt_approxTangentPlane_eq : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), HasApproximateTangentSpaceAt n M x Q → approxTangentPlane n M x = Q := by
  intro P n M x Q hQ
  have h : ∃ Q', HasApproximateTangentSpaceAt n M x Q' := ⟨Q, hQ⟩
  unfold approxTangentPlane
  rw [dite_eq_left h]
  exact h.choose_spec.unique hQ
/-- Step 3(i) of the Jacobian identity for the orientation of a `C¹` graph (Simon 7.4.3, via
Allard's theorem; `n`-covectors as in Ch. 6, §1): if `τ` is an orthonormal `n`-frame and every
`bⱼ` lies in `L = span τ`, then `α(b₁, …, bₙ) = det(⟨τᵢ, bⱼ⟩) α(τ₁, …, τₙ)` for every
`n`-covector `α`.  The restriction of `α` to `L` is `α(τ) det_τ`, and the coordinates of `bⱼ` in
the basis `τ` of `L` are `⟨τᵢ, bⱼ⟩`. -/
theorem Submission.dgoj_covector_eq_det_mul_of_mem_span : ∀ (P n : ℕ) (τ b : Fin n → Euclid P), Orthonormal ℝ τ → (∀ j, b j ∈ Submodule.span ℝ (Set.range τ)) → ∀ α : Covector (Euclid P) n, α b = (Matrix.of fun i j => inner ℝ (τ i) (b j)).det * α τ := by
  intro P n τ b hτ hb α
  set L := Submodule.span ℝ (Set.range τ)
  -- `τ` is a basis `e` of `L`
  let e : Module.Basis (Fin n) ℝ L := Module.Basis.span hτ.linearIndependent
  have he : ∀ i, (e i : Euclid P) = τ i := fun i => by
    rw [Module.Basis.span_apply hτ.linearIndependent i]
  -- the restriction `α_L` of `α` to `L`
  let αL : L [⋀^Fin n]→ₗ[ℝ] ℝ := α.toAlternatingMap.compLinearMap L.subtype
  let b' : Fin n → L := fun j => ⟨b j, hb j⟩
  have h1 : α b = αL b' := rfl
  have h2 : α τ = αL e := by
    show α τ = α (fun i => (e i : Euclid P))
    congr 1
    funext i
    exact (he i).symm
  -- coordinates of `b'` in `e` are the inner products with `τ`
  have hrepr : ∀ i j, e.repr (b' j) i = inner ℝ (τ i) (b j) := by
    intro i j
    have hs : (b j : Euclid P) = ∑ l, e.repr (b' j) l • τ l := by
      have := congrArg (Subtype.val) (e.sum_repr (b' j))
      simp only [Submodule.coe_sum, Submodule.coe_smul, he] at this
      exact this.symm
    rw [hs, hτ.inner_right_fintype]
  have hmat : e.toMatrix b' = Matrix.of fun i j => inner ℝ (τ i) (b j) := by
    ext i j
    rw [Module.Basis.toMatrix_apply, hrepr, Matrix.of_apply]
  -- `α_L = α_L(e) • det_e`
  have h3 : αL b' = αL e * e.det b' := by
    conv_lhs => rw [AlternatingMap.eq_smul_basis_det e αL]
    rfl
  rw [h1, h2, h3, Module.Basis.det_apply, hmat, mul_comm]
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
/-- **Simon Ch. 6, 1.2 (p. 132)**: `Λⁿ(ℝᴾ)` is finite-dimensional.  An `n`-covector `α` is
determined by its values `α(e_{I(1)}, …, e_{I(n)})` on tuples of standard basis vectors
(alternating maps agreeing on distinct basis vectors are equal), so
`Φ α = (α(e ∘ I))_{I : Fin n → Fin P}` is an injective linear map into the finite-dimensional
space `ℝ^(Fin n → Fin P)`. -/
theorem Submission.lcn_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `Φ α = (α(e ∘ I))_I`, linear since addition and scaling of covectors are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α I => α fun i => e (I i)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  -- `Φ α = Φ β` makes `α` and `β` agree on distinct basis vectors, hence everywhere
  refine FiniteDimensional.of_injective Φ fun α β h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- Simon 6.3.1: `Hⁿ`-a.e. on `M` the orientation `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` of an integer
multiplicity triple is a unit simple `n`-vector (`τ` orthonormal), so every `n`-covector `β`
satisfies `|⟨β, ξ(x)⟩| = |β(τ₁, …, τₙ)| ≤ ‖β‖ ∏ᵢ ‖τᵢ‖ = ‖β‖` (operator norm). -/
theorem Submission.dpf_pfc_imrep_orient_abs_apply_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ β : Covector (Euclid P) n, |R.orient x β| ≤ ‖β‖ := by
  intro P n U R
  filter_upwards [R.orients] with x hx β
  -- `ξ(x)` is `±` evaluation at an orthonormal frame `τ`
  obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
  have hβ : |β τ| ≤ ‖β‖ :=
    calc |β τ| = ‖β τ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖β‖ * ∏ i, ‖τ i‖ := β.le_opNorm τ
      _ = ‖β‖ := by rw [Finset.prod_eq_one fun i _ => hτ.1 i, mul_one]
  rcases hξ with h | h
  · rw [h β]
    exact hβ
  · rw [h β, abs_neg]
    exact hβ

/-- **Pairing bound for `τ(M, θ, ξ)`** (the estimate behind Simon 6.2.24(2)).  If `F` is
`Hⁿ⌞M`-a.e. strongly measurable, vanishes off the compact `C ⊆ U` and `‖F‖ ≤ B`, then
`θ ⟨F, ξ⟩` is `Hⁿ⌞M`-integrable and `|∫_M θ ⟨F, ξ⟩ dHⁿ| ≤ B ∫_{M ∩ C} θ dHⁿ`.  By
`dpf_pfc_imrep_orient_abs_apply_le`, `|θ ⟨F, ξ⟩| ≤ B θ 1_C` a.e., and `θ 1_C` is integrable by
the local integrability of `θ`. -/
theorem Submission.dpf_pfc_imrep_pairing_integrable_abs_le : ∀ (P n : ℕ) (U C : Set (Euclid P)) (R : IMRep U n) (F : Euclid P → Covector (Euclid P) n) (B : ℝ), IsCompact C → C ⊆ U → AEStronglyMeasurable F (μHE[n].restrict R.carrier) → (∀ x, x ∉ C → F x = 0) → (∀ x, ‖F x‖ ≤ B) → Integrable (fun x => (R.mult x : ℝ) * R.orient x (F x)) (μHE[n].restrict R.carrier) ∧ |∫ x in R.carrier, (R.mult x : ℝ) * R.orient x (F x) ∂μHE[n]| ≤ B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U C R F B hC hCU hF hF0 hFB
  -- Step 1: `C` is measurable; step 2: `θ` is measurable
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult
  -- Step 3: `μ.restrict C = Hⁿ⌞(M ∩ C)`
  have hres : (μHE[n].restrict R.carrier).restrict C = μHE[n].restrict (R.carrier ∩ C) := by
    rw [Measure.restrict_restrict hCm, inter_comm]
  -- Step 4: `θ` is integrable on `C`, so `g = B · 1_C θ` is integrable
  have hθC : IntegrableOn (fun x => (R.mult x : ℝ)) C (μHE[n].restrict R.carrier) := by
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, hres]
    simpa using (R.locallyIntegrable_mult C hC hCU).lt_top
  have hg : Integrable (fun x => B * C.indicator (fun y => (R.mult y : ℝ)) x)
      (μHE[n].restrict R.carrier) :=
    ((integrable_indicator_iff hCm).2 hθC).const_mul B
  -- Step 5: `h = θ · ξ(F)` is a.e. strongly measurable
  have hh : AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (F x))
      (μHE[n].restrict R.carrier) :=
    hθm.aestronglyMeasurable.mul ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂
      R.aestronglyMeasurable_orient hF)
  -- Step 6: `|h| ≤ g` a.e., by `orient_bound`
  have hdom : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x (F x)‖ ≤ B * C.indicator (fun y => (R.mult y : ℝ)) x := by
    filter_upwards [Submission.dpf_pfc_imrep_orient_abs_apply_le P n U R] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_comm B]
      exact mul_le_mul_of_nonneg_left ((hx (F x)).trans (hFB x)) (Nat.cast_nonneg _)
    · simp [indicator_of_notMem hxC, hF0 x hxC]
  -- Step 7: integrability
  refine ⟨hg.mono' hh hdom, ?_⟩
  -- Step 8: `∫ g dμ = B · (∫⁻_{M ∩ C} θ dHⁿ).toReal`
  have hgval : ∫ x, B * C.indicator (fun y => (R.mult y : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      B * (∫⁻ x in R.carrier ∩ C, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_const_mul, integral_indicator hCm, hres,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => Nat.cast_nonneg _)
        hθm.aestronglyMeasurable]
    simp
  -- Step 9: `|∫ h dμ| ≤ ∫ g dμ`
  rw [← Real.norm_eq_abs, ← hgval]
  exact norm_integral_le_of_norm_le hg hdom
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

set_option maxHeartbeats 800000 in
/-- **Splitting off the spine: `S = [[L]] × S₀`** (Simon 7.3.5, chapter-07.txt lines 410–418; the
book leaves the proof to the reader).  Let `S = τ(M, θ, ξ)` be invariant under translations by the
`d`-dimensional subspace `L` (`1 ≤ d < n`), with `L ⊆ TₓM` for `μ_S`-a.e. `x`.  Then
`μ_S = ∫_L μ_{S₀}(· − t) dHᵈ(t)` and `S(ω) = ∫_L S₀(♭ω(t + ·)) dHᵈ(t)` for an integer multiplicity
`S₀ ∈ 𝒟_{n−d}(ℝᴾ)` carried by `Lᗮ`, `♭` being the interior product with `f₁ ∧ ⋯ ∧ f_d`.
At a.e. `x ∈ M`, `ξ = ±f ∧ g` with `g` an orthonormal basis of `TₓM ∩ Lᗮ`, so `ξ(α) = ζ(♭α)` for the
Borel `ζ = ξ ∘ (f* ∧ ·)`.  By the coarea formula `dimred_cs_sos_spine_coarea`, a.e. slice
`M_t = M ∩ p⁻¹(t)` carries the integer multiplicity triple `(M_t, θ, ζ)`, and `μ_S`, `S` disintegrate
over the slices.  Translation invariance and the uniqueness of `1_M θ ξ` make `1_M θ ξ` invariant
under translations by `L`, `Hⁿ`-a.e.; Tonelli on `(Hⁿ⌞M) × (Hᵈ⌞L)` and `(Hᵐ⌞M_{t₀}) × (Hᵈ⌞L)` shows
that a.e. slice is the translate of a base slice `M_{t₀}`, and `S₀` is `M_{t₀}` translated to `Lᗮ`. -/
theorem Submission.dimred_cs_sos_product_decomposition : ∀ (P n : ℕ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n) (L : Submodule ℝ (Euclid P)) (f : Fin (Module.finrank ℝ L) → Euclid P) (hd : Module.finrank ℝ L < n), 0 < Module.finrank ℝ L → Orthonormal ℝ f → (∀ i, f i ∈ L) → (∀ v ∈ L, ∀ ω : TestFormOn (univ : Set (Euclid P)) n, currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) = S ω) → R.Represents S → (∀ᵐ x ∂R.measure, ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v) → ∃ (S₀ : GeometricCurrentOn (univ : Set (Euclid P)) (n - Module.finrank ℝ L)) (R₀ : IMRep (univ : Set (Euclid P)) (n - Module.finrank ℝ L)), R₀.Represents S₀ ∧ S₀.support ⊆ (Lᗮ : Set (Euclid P)) ∧ R₀.measure (Lᗮ : Set (Euclid P))ᶜ = 0 ∧ (∀ A : Set (Euclid P), MeasurableSet A → R.measure A = ∫⁻ t in (L : Set (Euclid P)), R₀.measure ((fun y => t + y) ⁻¹' A) ∂μHE[Module.finrank ℝ L]) ∧ ∀ flat : Covector (Euclid P) n → Covector (Euclid P) (n - Module.finrank ℝ L), (∀ (α : Covector (Euclid P) n) (v : Fin (n - Module.finrank ℝ L) → Euclid P), flat α v = α (Fin.append f v ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, S ω = ∫ t in (L : Set (Euclid P)), currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∂μHE[Module.finrank ℝ L] := by
  have hcoarea := @Submission.dimred_cs_sos_spine_coarea
  intro P n S R L
  set d := Module.finrank ℝ L with hd_def
  intro f hd hdpos hf hfL hinv hrep htan
  set m := n - d with hm_def
  /- ### Generalities -/
  have hLm : MeasurableSet (L : Set (Euclid P)) := L.closed_of_finiteDimensional.measurableSet
  have hpfix : ∀ t ∈ L, L.starProjection t = t := fun t ht =>
    Submodule.starProjection_eq_self_iff.2 ht
  have hθm : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hθr : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- an integer multiplicity carrier has locally finite measure
  have hfinK : ∀ (k : ℕ) (R' : IMRep (univ : Set (Euclid P)) k) (K : Set (Euclid P)),
      IsCompact K → μHE[k] (R'.carrier ∩ K) ≠ ∞ := by
    intro k R' K hK
    refine ne_top_of_le_ne_top (R'.locallyIntegrable_mult K hK (subset_univ _)) ?_
    rw [← setLIntegral_one]
    refine setLIntegral_mono (measurable_from_nat.comp R'.measurable_mult) fun x hx => ?_
    exact_mod_cast (show 1 ≤ R'.mult x from R'.mult_pos x hx.1)
  have hsf : ∀ (k : ℕ) (R' : IMRep (univ : Set (Euclid P)) k),
      SigmaFinite (μHE[k].restrict R'.carrier) := by
    intro k R'
    have : IsLocallyFiniteMeasure (μHE[k].restrict R'.carrier) :=
      ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos, by
        rw [Measure.restrict_apply measurableSet_closedBall, inter_comm]
        exact lt_top_iff_ne_top.2 (hfinK k R' _ (isCompact_closedBall x 1))⟩⟩
    infer_instance
  -- `Hᵈ⌞L` is σ-finite, nonzero and invariant under translations by `L`
  have hLsf : SigmaFinite (μHE[d].restrict (L : Set (Euclid P))) := by
    have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) (n := d) (P := L) rfl
    infer_instance
  have hLne : (μHE[d].restrict (L : Set (Euclid P))) ≠ 0 := by
    intro h0
    have hsupp := Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule
      (E := Euclid P) (n := d) (P := L) rfl
    rw [h0, Measure.support_zero] at hsupp
    have h0L : (0 : Euclid P) ∈ (L : Set (Euclid P)) := L.zero_mem
    rw [← hsupp] at h0L
    exact h0L
  have : (ae (μHE[d].restrict (L : Set (Euclid P)))).NeBot := ae_neBot.2 hLne
  have hLtrans : ∀ s ∈ L, MeasurePreserving (fun t => t + s)
      (μHE[d].restrict (L : Set (Euclid P))) (μHE[d].restrict (L : Set (Euclid P))) := by
    intro s hs
    have hmp : MeasurePreserving (fun t : Euclid P => t + s) μHE[d] μHE[d] :=
      (IsometryEquiv.addRight s).measurePreserving_euclideanHausdorffMeasure d
    have hme : MeasurableEmbedding (fun t : Euclid P => t + s) :=
      (MeasurableEquiv.addRight s).measurableEmbedding
    have h := hmp.restrict_preimage_emb hme (L : Set (Euclid P))
    have hpre : (fun t => t + s) ⁻¹' (L : Set (Euclid P)) = L := by
      ext t
      simp only [mem_preimage, SetLike.mem_coe]
      exact L.add_mem_iff_left hs
    rwa [hpre] at h
  /- ### Translating an integer multiplicity triple -/
  have htransl : ∀ (k : ℕ) (R' : IMRep (univ : Set (Euclid P)) k) (c : Euclid P),
      StronglyMeasurable R'.orient →
      ∃ R'' : IMRep (univ : Set (Euclid P)) k,
        R''.carrier = (fun z => z - c) ⁻¹' R'.carrier ∧
        (∀ z, R''.mult z = R'.mult (z - c)) ∧ (∀ z, R''.orient z = R'.orient (z - c)) ∧
        (∀ γ : DifferentialForm (Euclid P) k, R''.action γ = R'.action (fun y => γ (y + c))) ∧
        (∀ A : Set (Euclid P), MeasurableSet A →
          R''.measure A = R'.measure ((fun y => y + c) ⁻¹' A)) := by
    intro k R' c hor
    have hmp : MeasurePreserving (fun z : Euclid P => z - c) μHE[k] μHE[k] :=
      (IsometryEquiv.subRight c).measurePreserving_euclideanHausdorffMeasure k
    have hme : MeasurableEmbedding (fun z : Euclid P => z - c) :=
      (MeasurableEquiv.subRight c).measurableEmbedding
    have hCm : MeasurableSet ((fun z : Euclid P => z - c) ⁻¹' R'.carrier) :=
      R'.measurableSet_carrier.preimage (measurable_sub_const c)
    refine ⟨{ carrier := (fun z : Euclid P => z - c) ⁻¹' R'.carrier
              mult := fun z => R'.mult (z - c)
              orient := fun z => R'.orient (z - c)
              measurableSet_carrier := hCm
              carrier_subset := subset_univ _
              rectifiable := ?_
              measurable_mult := R'.measurable_mult.comp (measurable_sub_const c)
              mult_pos := fun z hz => R'.mult_pos _ hz
              locallyIntegrable_mult := ?_
              aestronglyMeasurable_orient :=
                (hor.comp_measurable (measurable_sub_const c)).aestronglyMeasurable
              orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl, fun γ => ?_, fun A hA => ?_⟩
    · obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R'.rectifiable
      refine ⟨(fun z => z - c) ⁻¹' M₀, ?_, fun j y => F j y + c, fun j => ?_, ?_⟩
      · rw [hmp.measure_preimage_emb hme]
        exact hM₀
      · obtain ⟨K, hK⟩ := hF j
        exact ⟨K, LipschitzWith.of_dist_le_mul fun y y' => by
          rw [dist_add_right]; exact hK.dist_le_mul y y'⟩
      · intro z hz
        rcases hcover hz with h | h
        · exact Or.inl h
        · right
          obtain ⟨j, y, hy⟩ := mem_iUnion.1 h
          exact mem_iUnion.2 ⟨j, y, by simp [hy]⟩
    · intro K hK _
      have hK' : IsCompact ((fun y => y + c) ⁻¹' K) :=
        (Homeomorph.addRight c).isCompact_preimage.2 hK
      have h := R'.locallyIntegrable_mult _ hK' (subset_univ _)
      have heq : (fun z : Euclid P => z - c) ⁻¹' R'.carrier ∩ K =
          (fun z => z - c) ⁻¹' (R'.carrier ∩ (fun y => y + c) ⁻¹' K) := by
        ext z
        simp
      rw [heq, hmp.setLIntegral_comp_preimage_emb hme (fun y => (R'.mult y : ℝ≥0∞))]
      exact h
    · have hmp' : MeasurePreserving (fun z => z - c)
          (μHE[k].restrict ((fun z : Euclid P => z - c) ⁻¹' R'.carrier))
          (μHE[k].restrict R'.carrier) := hmp.restrict_preimage_emb hme R'.carrier
      filter_upwards [hmp'.quasiMeasurePreserving.ae R'.orients] with x hx
      obtain ⟨Q, hQ, hQo⟩ := hx
      refine ⟨Q, ⟨hQ.1, fun g => ?_⟩, hQo⟩
      have himg : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap x r ''
            ((fun z : Euclid P => z - c) ⁻¹' R'.carrier) =
          Poincare.SimonGMT.Chapter03.blowUpMap (x - c) r '' R'.carrier := by
        intro r
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y - c, hy, ?_⟩
          simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
          congr 1
          abel
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y + c, by simpa using hy, ?_⟩
          simp only [Poincare.SimonGMT.Chapter03.blowUpMap]
          congr 1
          abel
      simp_rw [himg]
      exact hQ.2 g
    · show ∫ x in (fun z : Euclid P => z - c) ⁻¹' R'.carrier,
          (R'.mult (x - c) : ℝ) * R'.orient (x - c) (γ x) ∂μHE[k] =
        ∫ y in R'.carrier, (R'.mult y : ℝ) * R'.orient y (γ (y + c)) ∂μHE[k]
      rw [← hmp.setIntegral_preimage_emb hme
        (fun y => (R'.mult y : ℝ) * R'.orient y (γ (y + c))) R'.carrier]
      simp only [sub_add_cancel]
    · show ((μHE[k].restrict ((fun z : Euclid P => z - c) ⁻¹' R'.carrier)).withDensity
          fun x => (R'.mult (x - c) : ℝ≥0∞)) A =
        ((μHE[k].restrict R'.carrier).withDensity fun x => (R'.mult x : ℝ≥0∞))
          ((fun y => y + c) ⁻¹' A)
      rw [withDensity_apply _ hA, withDensity_apply _ (hA.preimage (measurable_add_const c)),
        Measure.restrict_restrict hA,
        Measure.restrict_restrict (hA.preimage (measurable_add_const c))]
      have heq : A ∩ (fun z : Euclid P => z - c) ⁻¹' R'.carrier =
          (fun z => z - c) ⁻¹' ((fun y => y + c) ⁻¹' A ∩ R'.carrier) := by
        ext z
        simp
      rw [heq, hmp.setLIntegral_comp_preimage_emb hme (fun y => (R'.mult y : ℝ≥0∞))]
  /- ### Equal weighted orientations give equal actions -/
  have hact_eq : ∀ (k : ℕ) (R₁ R₂ : IMRep (univ : Set (Euclid P)) k),
      (∀ᵐ z ∂(μHE[k].restrict (R₁.carrier ∪ R₂.carrier)),
        R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) z =
          R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) z) →
      ∀ γ : DifferentialForm (Euclid P) k, R₁.action γ = R₂.action γ := by
    intro k R₁ R₂ h γ
    have key : ∀ R₃ : IMRep (univ : Set (Euclid P)) k, R₃.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        R₃.action γ = ∫ z in R₁.carrier ∪ R₂.carrier,
          R₃.carrier.indicator (fun y => (R₃.mult y : ℝ) • R₃.orient y) z (γ z) ∂μHE[k] := by
      intro R₃ hR₃
      have hpt : ∀ z, R₃.carrier.indicator (fun y => (R₃.mult y : ℝ) • R₃.orient y) z (γ z) =
          R₃.carrier.indicator (fun y => (R₃.mult y : ℝ) * R₃.orient y (γ y)) z := by
        intro z
        by_cases hz : z ∈ R₃.carrier
        · simp [hz]
        · simp [hz]
      simp_rw [hpt]
      rw [integral_indicator R₃.measurableSet_carrier,
        Measure.restrict_restrict R₃.measurableSet_carrier, inter_eq_left.2 hR₃]
      rfl
    rw [key R₁ subset_union_left, key R₂ subset_union_right]
    apply integral_congr_ae
    filter_upwards [h] with z hz
    rw [hz]
  /- ### The Borel version of the orientation -/
  obtain ⟨ξ', hξ'sm, hξ'ae⟩ : ∃ ξ' : Euclid P → MultiVector P n, StronglyMeasurable ξ' ∧
      R.orient =ᵐ[μHE[n].restrict R.carrier] ξ' :=
    ⟨_, R.aestronglyMeasurable_orient.stronglyMeasurable_mk,
      R.aestronglyMeasurable_orient.ae_eq_mk⟩
  obtain ⟨R', hR'C, hR'θ, hR'ξ⟩ : ∃ R' : IMRep (univ : Set (Euclid P)) n,
      R'.carrier = R.carrier ∧ R'.mult = R.mult ∧ R'.orient = ξ' :=
    ⟨{ carrier := R.carrier
       mult := R.mult
       orient := ξ'
       measurableSet_carrier := R.measurableSet_carrier
       carrier_subset := R.carrier_subset
       rectifiable := R.rectifiable
       measurable_mult := R.measurable_mult
       mult_pos := R.mult_pos
       locallyIntegrable_mult := R.locallyIntegrable_mult
       aestronglyMeasurable_orient := hξ'sm.aestronglyMeasurable
       orients := by
         filter_upwards [R.orients, hξ'ae] with x hx hxe
         rw [← hxe]
         exact hx }, rfl, rfl, rfl⟩
  have hR'rep : R'.Represents S := by
    intro ω
    rw [hrep ω]
    simp only [IMRep.action, hR'C, hR'θ, hR'ξ]
    apply integral_congr_ae
    filter_upwards [hξ'ae] with x hx
    rw [hx]
  /- ### Translation invariance of `S` -/
  have hShift : ∀ v ∈ L, ∀ (ω : TestFormOn (univ : Set (Euclid P)) n)
      (hω' : (fun x => (ω : DifferentialForm (Euclid P) n) (x + v)) ∈
        testFormOnSubmodule (E := Euclid P) (univ : Set (Euclid P)) n),
      S ⟨fun x => (ω : DifferentialForm (Euclid P) n) (x + v), hω'⟩ = S ω := by
    intro v hv ω hω'
    rw [← hinv v hv ω]
    have hsupp : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
        tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (-v) 1 '' univ := by
      refine ⟨ω.property.1, fun x _ => ⟨x - v, trivial, ?_⟩⟩
      simp [dilation, dilationCLM]
    have hval : currentEval (blowUp S (-v) 1 one_ne_zero) (ω : DifferentialForm (Euclid P) n) =
        S ⟨fun x => (ω : DifferentialForm (Euclid P) n) (x + v), hω'⟩ := by
      unfold currentEval
      rw [dite_eq_left hsupp]
      show S _ = S _
      congr 1
      apply Subtype.ext
      funext x
      show ((ω : DifferentialForm (Euclid P) n) (-((1 : ℝ)⁻¹ • -v) + dilationCLM P 1 x)).compContinuousLinearMap
          (dilationCLM P 1) = (ω : DifferentialForm (Euclid P) n) (x + v)
      have h1 : dilationCLM P 1 = ContinuousLinearMap.id ℝ (Euclid P) := by
        ext y
        simp [dilationCLM]
      rw [h1]
      ext w
      simp [add_comm]
    exact hval.symm
  /- ### The weighted orientation `Γ = 1_M θ ξ'` is invariant under translations by `L` -/
  set Γ : Euclid P → MultiVector P n := R.carrier.indicator (fun y => (R.mult y : ℝ) • ξ' y)
    with hΓ_def
  have hΓsm : StronglyMeasurable Γ :=
    (hθr.stronglyMeasurable.smul hξ'sm).indicator R.measurableSet_carrier
  have hΓinv : ∀ v ∈ L, μHE[n] {z | Γ (z + v) ≠ Γ z} = 0 := by
    intro v hv
    have hR'sm : StronglyMeasurable R'.orient := by rw [hR'ξ]; exact hξ'sm
    obtain ⟨Rv, hRvC, hRvθ, hRvξ, hRvact, -⟩ := htransl n R' v hR'sm
    have hRvrep : Rv.Represents S := by
      intro ω
      have hω' : (fun x => (ω : DifferentialForm (Euclid P) n) (x + v)) ∈
          testFormOnSubmodule (E := Euclid P) (univ : Set (Euclid P)) n :=
        ⟨⟨ω.property.1.1.comp (contDiff_id.add contDiff_const),
          ω.property.1.2.comp_homeomorph (Homeomorph.addRight v)⟩, subset_univ _⟩
      rw [hRvact, ← hShift v hv ω hω', hR'rep ⟨_, hω'⟩]
    have h := Submission.imrep_weighted_orient_indicator_ae_eq P n univ S R' Rv isOpen_univ
      hR'rep hRvrep
    have hRvΓ : ∀ z, Rv.carrier.indicator (fun y => (Rv.mult y : ℝ) • Rv.orient y) z =
        Γ (z - v) := by
      intro z
      classical
      simp only [hΓ_def, Set.indicator_apply, hRvC, mem_preimage, hRvθ, hRvξ, hR'C, hR'θ, hR'ξ]
    have hR'Γ : ∀ z, R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) z = Γ z := by
      intro z
      simp only [hΓ_def, hR'C, hR'θ, hR'ξ]
    have h2 : ∀ᵐ z ∂μHE[n], Γ z = Γ (z - v) := by
      rw [ae_restrict_iff' (R'.measurableSet_carrier.union Rv.measurableSet_carrier)] at h
      filter_upwards [h] with z hz
      by_cases hz' : z ∈ R'.carrier ∪ Rv.carrier
      · have := hz hz'
        rwa [hR'Γ, hRvΓ] at this
      · rw [mem_union, not_or] at hz'
        rw [← hR'Γ, ← hRvΓ, indicator_of_notMem hz'.1, indicator_of_notMem hz'.2]
    have h3 : μHE[n] {w | Γ w ≠ Γ (w - v)} = 0 := by
      rw [ae_iff] at h2
      simpa using h2
    have hmp : MeasurePreserving (fun z : Euclid P => z + v) μHE[n] μHE[n] :=
      (IsometryEquiv.addRight v).measurePreserving_euclideanHausdorffMeasure n
    have hme : MeasurableEmbedding (fun z : Euclid P => z + v) :=
      (MeasurableEquiv.addRight v).measurableEmbedding
    have hset : {z | Γ (z + v) ≠ Γ z} = (fun z => z + v) ⁻¹' {w | Γ w ≠ Γ (w - v)} := by
      ext z
      simp
    rw [hset, hmp.measure_preimage_emb hme]
    exact h3
  /- ### Good points of `M` -/
  have hgood : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ξ' x = R.orient x ∧
      ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q ∧
        IsUnitOrientationOf (R.orient x) Q ∧ L ≤ Q := by
    have htan' : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
        ∀ v ∈ L, (approxTangentPlane n R.carrier x).starProjection v = v := by
      have h := htan
      rw [IMRep.measure, ae_withDensity_iff hθm] at h
      filter_upwards [h, ae_restrict_mem R.measurableSet_carrier] with x hx hxM
      exact hx (by exact_mod_cast (R.mult_pos x hxM).ne')
    filter_upwards [htan', R.orients, hξ'ae] with x hx hor hxe
    obtain ⟨Q, hQ, hQo⟩ := hor
    refine ⟨hxe.symm, Q, hQ, hQo, fun v hv => ?_⟩
    have := hx v hv
    rw [Submission.dpf_itt_approxTangentPlane_eq P n R.carrier x Q hQ] at this
    exact Submodule.starProjection_eq_self_iff.1 this
  /- ### The coarea formula for the slices `M ∩ p⁻¹(t)` -/
  have hMtan : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n R.carrier x Q ∧ L ≤ Q := by
    filter_upwards [hgood] with x hx
    obtain ⟨-, Q, hQ, -, hLQ⟩ := hx
    exact ⟨Q, hQ, hLQ⟩
  obtain ⟨hC3, hC1⟩ := hcoarea P n L R.carrier hd R.measurableSet_carrier R.rectifiable
    (hfinK n R) hMtan
  -- `Hⁿ⌞M`-a.e. properties hold `Hᵐ⌞M_t`-a.e. for a.e. `t`
  have htransfer : ∀ (Pr : Euclid P → Prop), (∀ᵐ x ∂(μHE[n].restrict R.carrier), Pr x) →
      ∀ᵐ t ∂(μHE[d].restrict (L : Set (Euclid P))),
        ∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})), Pr x := by
    intro Pr hPr
    rw [ae_iff] at hPr
    obtain ⟨N, hsN, hNm, hN0⟩ := exists_measurable_superset_of_null hPr
    obtain ⟨h1m, h1⟩ := hC1 (N.indicator 1) (measurable_one.indicator hNm)
    have h2 : ∫⁻ x in R.carrier, N.indicator 1 x ∂μHE[n] = 0 := by
      rw [lintegral_indicator_one hNm]
      exact hN0
    rw [h1] at h2
    filter_upwards [(lintegral_eq_zero_iff' h1m).1 h2] with t ht
    have ht' : (μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})) N = 0 := by
      rw [← lintegral_indicator_one hNm]
      exact ht
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hsN hx) ht'
  -- local finiteness of `θ` on a.e. slice
  have hfint : ∀ᵐ t ∂(μHE[d].restrict (L : Set (Euclid P))), ∀ j : ℕ,
      ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t} ∩ closedBall 0 j,
        (R.mult x : ℝ≥0∞) ∂μHE[m] ≠ ∞ := by
    rw [ae_all_iff]
    intro j
    obtain ⟨h1m, h1⟩ := hC1 ((closedBall (0 : Euclid P) j).indicator fun x => (R.mult x : ℝ≥0∞))
      (hθm.indicator measurableSet_closedBall)
    have hfin : ∫⁻ x in R.carrier, (closedBall (0 : Euclid P) j).indicator
        (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] ≠ ∞ := by
      rw [lintegral_indicator measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
      exact R.locallyIntegrable_mult _ (isCompact_closedBall 0 j) (subset_univ _)
    rw [h1] at hfin
    filter_upwards [ae_lt_top' h1m hfin] with t ht
    rw [lintegral_indicator measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm] at ht
    exact ht.ne
  have hgoodt := htransfer _ hgood
  have hslice_ae : ∀ᵐ t ∂(μHE[d].restrict (L : Set (Euclid P))), t ∈ L ∧
      CountablyRectifiable m (R.carrier ∩ {x | L.starProjection x = t}) ∧
      (∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})),
        ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt m (R.carrier ∩ {x | L.starProjection x = t}) x
            (Q ⊓ Lᗮ)) ∧
      (∀ j : ℕ, ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t} ∩ closedBall 0 j,
        (R.mult x : ℝ≥0∞) ∂μHE[m] ≠ ∞) ∧
      (∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})), ξ' x = R.orient x ∧
        ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q ∧
          IsUnitOrientationOf (R.orient x) Q ∧ L ≤ Q) := by
    filter_upwards [ae_restrict_mem hLm, hC3, hfint, hgoodt] with t htL ht3 htf htg
    exact ⟨htL, ht3.1, ht3.2, htf, htg⟩
  /- ### The lift `Λᵐ → Λⁿ`, `β ↦ f₁* ∧ ⋯ ∧ f_d* ∧ β` -/
  obtain ⟨lift, hlift⟩ : ∃ lift : Covector (Euclid P) m →L[ℝ] Covector (Euclid P) n,
      ∀ (β : Covector (Euclid P) m) (w : Fin m → Euclid P),
        (∀ j, w j ∈ Lᗮ) → lift β (Fin.append f w ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm) =
          β w := by
    have hΛ : ∀ k : ℕ, (hkd : k ≤ d) → ∀ N : ℕ, (hNk : N = m + k) →
        ∃ Λ : Covector (Euclid P) m →ₗ[ℝ] Covector (Euclid P) N,
          ∀ (β : Covector (Euclid P) m) (v : Fin N → Euclid P),
            (∀ (a : ℕ) (ha : a < k), v ⟨a, by omega⟩ = f ⟨d - k + a, by omega⟩) →
            (∀ (j : ℕ) (hj : j < m), v ⟨k + j, by omega⟩ ∈ Lᗮ) →
            Λ β v = β (fun j => v ⟨k + j, by omega⟩) := by
      intro k
      induction k with
      | zero =>
        intro _ N hN
        subst hN
        refine ⟨LinearMap.id, fun β v _ _ => ?_⟩
        congr 1
        funext j
        congr 1
        ext
        simp
      | succ k ih =>
        intro hk N hN
        subst hN
        obtain ⟨Λ, hΛ⟩ := ih (by omega) (m + k) rfl
        set u := f ⟨d - (k + 1), by omega⟩ with hu
        refine ⟨((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Euclid P) ℝ).comp
          (ContinuousLinearMap.smulRightL ℝ (Euclid P) (Covector (Euclid P) (m + k))
            (innerSL ℝ u))).toLinearMap ∘ₗ Λ, ?_⟩
        intro β v hv1 hv2
        simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
          ContinuousLinearMap.comp_apply,
          ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
          ContinuousAlternatingMap.alternatizeUncurryFin_apply,
          ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
          innerSL_apply_apply]
        rw [Fin.sum_univ_succ]
        have hv0 : v 0 = u := by
          have := hv1 0 (by omega)
          rw [hu]
          convert this using 2
          ext
          simp
        have huu : inner ℝ u u = 1 := by
          rw [real_inner_self_eq_norm_sq, hu, hf.1]
          norm_num
        have hrest : ∀ i : Fin (m + k), inner ℝ u (v i.succ) = 0 := by
          intro i
          by_cases hik : (i : ℕ) < k
          · have := hv1 ((i : ℕ) + 1) (by omega)
            have hvi : v i.succ = f ⟨d - (k + 1) + ((i : ℕ) + 1), by omega⟩ := by
              rw [← this]
              congr 1
            rw [hvi, hu]
            apply hf.2
            intro h
            rw [Fin.mk.injEq] at h
            omega
          · have := hv2 ((i : ℕ) - k) (by omega)
            have hvi : v i.succ = v ⟨k + 1 + ((i : ℕ) - k), by omega⟩ := by
              congr 1
              ext
              simp
              omega
            rw [hvi]
            exact Submodule.inner_right_of_mem_orthogonal (hfL _) this
        simp only [hrest, zero_smul, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, smul_zero,
          Finset.sum_const_zero, add_zero, hv0, huu, one_smul, Fin.val_zero, pow_zero,
          Fin.removeNth_zero]
        rw [hΛ β (Fin.tail v)]
        · congr 1
          funext j
          simp only [Fin.tail]
          congr 1
          ext
          simp
          omega
        · intro a ha
          have := hv1 (a + 1) (by omega)
          simp only [Fin.tail]
          convert this using 2
          · ext; simp
          · ext; simp; omega
        · intro j hj
          have := hv2 j hj
          simp only [Fin.tail]
          convert this using 2
          ext; simp; omega
    have := Submission.lcn_covector_finiteDimensional P m
    obtain ⟨Λ, hΛ⟩ := hΛ d le_rfl n (by omega)
    refine ⟨LinearMap.toContinuousLinearMap Λ, fun β w hw => ?_⟩
    rw [LinearMap.coe_toContinuousLinearMap', hΛ]
    · congr 1
      funext j
      simp only [Function.comp_apply]
      have : (Fin.cast (Nat.add_sub_of_le hd.le).symm ⟨d + (j : ℕ), by omega⟩ : Fin (d + m)) =
          Fin.natAdd d j := by
        ext; simp
      rw [this, Fin.append_right]
    · intro a ha
      simp only [Function.comp_apply]
      have : (Fin.cast (Nat.add_sub_of_le hd.le).symm ⟨a, by omega⟩ : Fin (d + m)) =
          Fin.castAdd m ⟨a, ha⟩ := by
        ext; simp
      rw [this, Fin.append_left]
      congr 1
      ext
      simp
    · intro j hj
      simp only [Function.comp_apply]
      have : (Fin.cast (Nat.add_sub_of_le hd.le).symm ⟨d + j, by omega⟩ : Fin (d + m)) =
          Fin.natAdd d ⟨j, hj⟩ := by
        ext; simp
      rw [this, Fin.append_right]
      exact hw _
  /- ### Linear algebra at a good point: `ξ = ±f₁ ∧ ⋯ ∧ f_d ∧ g₁ ∧ ⋯ ∧ g_m` -/
  have hstruct : ∀ (Ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf Ξ Q → L ≤ Q →
      ∃ g : Fin m → Euclid P, Orthonormal ℝ g ∧
        Submodule.span ℝ (range g) = Q ⊓ Lᗮ ∧ (∀ j, g j ∈ Lᗮ) ∧
        ((∀ α : Covector (Euclid P) n,
            Ξ α = α (Fin.append f g ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm)) ∨
          (∀ α : Covector (Euclid P) n,
            Ξ α = -α (Fin.append f g ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm))) := by
    intro Ξ Q hΞ hLQ
    obtain ⟨τ, hτ, hspan, hΞτ⟩ := hΞ
    have hQn : Module.finrank ℝ Q = n := by
      rw [← hspan, finrank_span_eq_card hτ.linearIndependent, Fintype.card_fin]
    have hKm : Module.finrank ℝ (Q ⊓ Lᗮ : Submodule ℝ (Euclid P)) = m := by
      have h := Submodule.finrank_add_inf_finrank_orthogonal hLQ
      rw [inf_comm] at h
      omega
    obtain ⟨g, hg, hgK, hgspan⟩ : ∃ g : Fin m → Euclid P, Orthonormal ℝ g ∧
        (∀ j, g j ∈ Q ⊓ Lᗮ) ∧ Submodule.span ℝ (range g) = Q ⊓ Lᗮ := by
      let b : OrthonormalBasis (Fin m) ℝ (Q ⊓ Lᗮ : Submodule ℝ (Euclid P)) :=
        (stdOrthonormalBasis ℝ (Q ⊓ Lᗮ : Submodule ℝ (Euclid P))).reindex (finCongr hKm)
      refine ⟨fun j => (b j : Euclid P), b.orthonormal.comp_linearIsometry
        (Q ⊓ Lᗮ : Submodule ℝ (Euclid P)).subtypeₗᵢ, fun j => (b j).2, ?_⟩
      have hr : range (fun j => (b j : Euclid P)) =
          (Q ⊓ Lᗮ : Submodule ℝ (Euclid P)).subtype '' range b := by
        ext x
        simp
      rw [hr, Submodule.span_image, ← b.coe_toBasis, b.toBasis.span_eq, Submodule.map_top,
        Submodule.range_subtype]
    refine ⟨g, hg, hgspan, fun j => (hgK j).2, ?_⟩
    set φ : Fin n → Euclid P := Fin.append f g ∘ Fin.cast (Nat.add_sub_of_le hd.le).symm
      with hφ_def
    have hfg : Orthonormal ℝ (Fin.append f g) := by
      classical
      rw [orthonormal_iff_ite]
      intro i j
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        refine Fin.addCases (fun a' => ?_) (fun a' => ?_) j
      · simp only [Fin.append_left]
        rw [orthonormal_iff_ite.1 hf]
        simp [Fin.castAdd_inj]
      · simp only [Fin.append_left, Fin.append_right]
        rw [Submodule.inner_right_of_mem_orthogonal (hfL a) (hgK a').2, ite_eq_right]
        intro h
        have h' := congrArg Fin.val h
        rw [Fin.val_castAdd, Fin.val_natAdd] at h'
        have := a.isLt
        omega
      · simp only [Fin.append_left, Fin.append_right]
        rw [Submodule.inner_left_of_mem_orthogonal (hfL a') (hgK a).2, ite_eq_right]
        intro h
        have h' := congrArg Fin.val h
        rw [Fin.val_castAdd, Fin.val_natAdd] at h'
        have := a'.isLt
        omega
      · simp only [Fin.append_right]
        rw [orthonormal_iff_ite.1 hg]
        simp [Fin.natAdd_inj]
    have hφ : Orthonormal ℝ φ := hfg.comp _ (Fin.cast_injective _)
    have hφQ : ∀ i, φ i ∈ Q := by
      intro i
      simp only [hφ_def, Function.comp_apply]
      generalize Fin.cast (Nat.add_sub_of_le hd.le).symm i = j
      refine Fin.addCases (fun a => ?_) (fun a => ?_) j
      · rw [Fin.append_left]
        exact hLQ (hfL a)
      · rw [Fin.append_right]
        exact (hgK a).1
    have hφspan : Submodule.span ℝ (range φ) = Q := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hφQ i
      · rw [finrank_span_eq_card hφ.linearIndependent, Fintype.card_fin, hQn]
    have hτQ : ∀ j, τ j ∈ Q := fun j => hspan ▸ Submodule.subset_span (mem_range_self j)
    set c := (Matrix.of fun i j => inner ℝ (φ i) (τ j)).det with hc
    have h1 : ∀ α : Covector (Euclid P) n, α τ = c * α φ := fun α =>
      Submission.dgoj_covector_eq_det_mul_of_mem_span P n φ τ hφ
        (fun j => hφspan.symm ▸ hτQ j) α
    have h2 : ∀ α : Covector (Euclid P) n, α φ = c * α τ := by
      intro α
      have := Submission.dgoj_covector_eq_det_mul_of_mem_span P n τ φ hτ
        (fun j => hspan.symm ▸ hφQ j) α
      rw [this]
      congr 1
      rw [hc, ← Matrix.det_transpose]
      congr 1
      ext i j
      simp [real_inner_comm]
    obtain ⟨α₀, hα₀, -⟩ := Submission.unit_orientations_common_unit_covector P n Q Ξ Ξ
      ⟨τ, hτ, hspan, hΞτ⟩ ⟨τ, hτ, hspan, hΞτ⟩
    have hατ : α₀ τ ≠ 0 := by
      intro h0
      rcases hΞτ with h | h
      · rw [h α₀, h0] at hα₀; simp at hα₀
      · rw [h α₀, h0] at hα₀; simp at hα₀
    have hcc : c * c = 1 := by
      have := h1 α₀
      rw [h2 α₀, ← mul_assoc] at this
      have h' : (c * c - 1) * α₀ τ = 0 := by linarith
      rcases mul_eq_zero.1 h' with h | h
      · linarith
      · exact absurd h hατ
    have hc1 : c = 1 ∨ c = -1 := by
      have : (c - 1) * (c + 1) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases hΞτ with h | h <;> rcases hc1 with hc' | hc'
    · left; intro α; rw [h, h1, hc', one_mul]
    · right; intro α; rw [h, h1, hc', neg_one_mul]
    · right; intro α; rw [h, h1, hc', one_mul]
    · left; intro α; rw [h, h1, hc', neg_one_mul, neg_neg]
  -- the orientation of the slices, `ζ = ξ' ∘ lift`
  obtain ⟨ζ, hζsm, hζ_def⟩ : ∃ ζ : Euclid P → MultiVector P m, StronglyMeasurable ζ ∧
      ∀ x, ζ x = (ξ' x).comp lift :=
    ⟨fun x => (ξ' x).comp lift,
      (continuous_id.clm_comp continuous_const).comp_stronglyMeasurable hξ'sm, fun _ => rfl⟩
  have hζunit : ∀ (Ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
      IsUnitOrientationOf Ξ Q → L ≤ Q → IsUnitOrientationOf (Ξ.comp lift) (Q ⊓ Lᗮ) := by
    intro Ξ Q hΞ hLQ
    obtain ⟨g, hg, hgspan, hgL, hsign⟩ := hstruct Ξ Q hΞ hLQ
    refine ⟨g, hg, hgspan, ?_⟩
    rcases hsign with h | h
    · left
      intro β
      rw [ContinuousLinearMap.comp_apply, h, hlift β g hgL]
    · right
      intro β
      rw [ContinuousLinearMap.comp_apply, h, hlift β g hgL]
  /- ### The slices are integer multiplicity triples -/
  have hsliceRep : ∀ t, (t ∈ L ∧
      CountablyRectifiable m (R.carrier ∩ {x | L.starProjection x = t}) ∧
      (∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})),
        ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q →
          HasApproximateTangentSpaceAt m (R.carrier ∩ {x | L.starProjection x = t}) x
            (Q ⊓ Lᗮ)) ∧
      (∀ j : ℕ, ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t} ∩ closedBall 0 j,
        (R.mult x : ℝ≥0∞) ∂μHE[m] ≠ ∞) ∧
      (∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})), ξ' x = R.orient x ∧
        ∃ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q ∧
          IsUnitOrientationOf (R.orient x) Q ∧ L ≤ Q)) →
      ∃ Rt : IMRep (univ : Set (Euclid P)) m,
        Rt.carrier = R.carrier ∩ {x | L.starProjection x = t} ∧ Rt.mult = R.mult ∧
          Rt.orient = ζ := by
    rintro t ⟨-, hrect, htan3, hfin, hgd⟩
    refine ⟨{ carrier := R.carrier ∩ {x | L.starProjection x = t}
              mult := R.mult
              orient := ζ
              measurableSet_carrier := R.measurableSet_carrier.inter
                (isClosed_eq L.starProjection.continuous continuous_const).measurableSet
              carrier_subset := subset_univ _
              rectifiable := hrect
              measurable_mult := R.measurable_mult
              mult_pos := fun x hx => R.mult_pos x hx.1
              locallyIntegrable_mult := ?_
              aestronglyMeasurable_orient := hζsm.aestronglyMeasurable
              orients := ?_ }, rfl, rfl, rfl⟩
    · intro K hK _
      obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
      obtain ⟨j, hj⟩ := exists_nat_ge r
      refine ne_top_of_le_ne_top (hfin j) (lintegral_mono_set ?_)
      exact inter_subset_inter_right _ (hr.trans (closedBall_subset_closedBall hj))
    · filter_upwards [htan3, hgd] with x hx hxg
      obtain ⟨hxe, Q, hQ, hQo, hLQ⟩ := hxg
      refine ⟨Q ⊓ Lᗮ, hx Q hQ, ?_⟩
      rw [hζ_def, hxe]
      exact hζunit _ Q hQo hLQ
  /- ### Tonelli: `Γ` is `L`-invariant along almost every slice -/
  have hMsf : SigmaFinite (μHE[n].restrict R.carrier) := hsf n R
  have hneq : ∀ F G : Euclid P × Euclid P → MultiVector P n, StronglyMeasurable F →
      StronglyMeasurable G → MeasurableSet {q | F q ≠ G q} := by
    intro F G hF hG
    have := Submission.lcn_covector_finiteDimensional P n
    let b := Module.finBasis ℝ (Covector (Euclid P) n)
    have hset : {q | F q ≠ G q} = ⋃ i, {q | F q (b i) ≠ G q (b i)} := by
      ext q
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · intro h
        by_contra h'
        push Not at h'
        exact h (ContinuousLinearMap.coe_injective (b.ext h'))
      · rintro ⟨i, hi⟩ h
        exact hi (by rw [h])
    rw [hset]
    refine MeasurableSet.iUnion fun i => ?_
    have hev : Continuous fun Ξ : MultiVector P n => Ξ (b i) :=
      (ContinuousLinearMap.apply ℝ ℝ (b i)).continuous
    exact (measurableSet_eq_fun (hev.comp_stronglyMeasurable hF).measurable
      (hev.comp_stronglyMeasurable hG).measurable).compl
  have hEm : MeasurableSet {q : Euclid P × Euclid P | Γ (q.1 + q.2) ≠ Γ q.1} :=
    hneq _ _ (hΓsm.comp_measurable measurable_add) (hΓsm.comp_measurable measurable_fst)
  have hMtm : ∀ s : Euclid P, MeasurableSet (R.carrier ∩ {x | L.starProjection x = s}) :=
    fun s => R.measurableSet_carrier.inter
      (isClosed_eq L.starProjection.continuous continuous_const).measurableSet
  have hpL : ∀ x : Euclid P, L.starProjection x ∈ L := fun x => L.starProjection_apply_mem x
  -- for a.e. `z ∈ M`, `Γ(z + v) = Γ(z)` for a.e. `v ∈ L`
  have hN2 : ∀ᵐ z ∂(μHE[n].restrict R.carrier),
      μHE[d].restrict (L : Set (Euclid P)) {v | Γ (z + v) ≠ Γ z} = 0 := by
    have hprod : ((μHE[n].restrict R.carrier).prod (μHE[d].restrict (L : Set (Euclid P))))
        {q : Euclid P × Euclid P | Γ (q.1 + q.2) ≠ Γ q.1} = 0 := by
      rw [Measure.prod_apply_symm hEm]
      have h0 : (fun v => (μHE[n].restrict R.carrier)
          ((fun x => (x, v)) ⁻¹' {q : Euclid P × Euclid P | Γ (q.1 + q.2) ≠ Γ q.1})) =ᵐ[
            μHE[d].restrict (L : Set (Euclid P))] 0 := by
        filter_upwards [ae_restrict_mem hLm] with v hv
        exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans (hΓinv v hv).le)
      rw [lintegral_congr_ae h0]
      simp
    have h0 := (Measure.measure_prod_null hEm).1 hprod
    filter_upwards [h0] with z hz
    exact hz
  -- for a.e. `s ∈ L`, `Γ(q z + s) = Γ(z)` for a.e. `z ∈ M`
  have hN3 : ∀ᵐ s ∂(μHE[d].restrict (L : Set (Euclid P))),
      ∀ᵐ z ∂(μHE[n].restrict R.carrier), Γ (z - L.starProjection z + s) = Γ z := by
    have hE'm : MeasurableSet
        {q : Euclid P × Euclid P | Γ (q.1 - L.starProjection q.1 + q.2) ≠ Γ q.1} :=
      hneq _ _ (hΓsm.comp_measurable ((measurable_fst.sub
        (L.starProjection.measurable.comp measurable_fst)).add measurable_snd))
        (hΓsm.comp_measurable measurable_fst)
    have hprod : ((μHE[n].restrict R.carrier).prod (μHE[d].restrict (L : Set (Euclid P))))
        {q : Euclid P × Euclid P | Γ (q.1 - L.starProjection q.1 + q.2) ≠ Γ q.1} = 0 := by
      rw [Measure.measure_prod_null hE'm]
      filter_upwards [hN2] with z hz
      have hmp := hLtrans (-(L.starProjection z)) (L.neg_mem (hpL z))
      have hset : Prod.mk z ⁻¹'
          {q : Euclid P × Euclid P | Γ (q.1 - L.starProjection q.1 + q.2) ≠ Γ q.1} =
          (fun t => t + -(L.starProjection z)) ⁻¹' {v | Γ (z + v) ≠ Γ z} := by
        ext s
        simp only [mem_preimage, mem_ofPred_eq]
        rw [show z - L.starProjection z + s = z + (s + -L.starProjection z) by abel]
      show μHE[d].restrict (L : Set (Euclid P)) (Prod.mk z ⁻¹'
          {q : Euclid P × Euclid P | Γ (q.1 - L.starProjection q.1 + q.2) ≠ Γ q.1}) = 0
      rw [hset, hmp.measure_preimage_emb (MeasurableEquiv.addRight _).measurableEmbedding]
      exact hz
    rw [Measure.prod_apply_symm hE'm] at hprod
    have h0 := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hE'm)).1 hprod
    filter_upwards [h0] with s hs
    rw [ae_iff]
    exact hs
  /- ### The base slice `t₀` -/
  obtain ⟨t₀, ⟨ht₀, ht₀N4⟩, ht₀N3⟩ := ((hslice_ae.and (htransfer _ hN2)).and hN3).exists
  have ht₀L : t₀ ∈ L := ht₀.1
  obtain ⟨Rt₀, hRt₀C, hRt₀θ, hRt₀ξ⟩ := hsliceRep t₀ ht₀
  have hRt₀sm : StronglyMeasurable Rt₀.orient := by rw [hRt₀ξ]; exact hζsm
  obtain ⟨R₀, hR₀C, hR₀θ, hR₀ξ, hR₀act, hR₀meas⟩ := htransl m Rt₀ (-t₀) hRt₀sm
  obtain ⟨S₀, hS₀⟩ := Submission.dtc_imrep_current P m univ R₀
  have hR₀L : R₀.carrier ⊆ (Lᗮ : Set (Euclid P)) := by
    intro z hz
    rw [hR₀C, mem_preimage, hRt₀C] at hz
    have h := hz.2
    simp only [mem_ofPred_eq, sub_neg_eq_add, map_add, hpfix t₀ ht₀L] at h
    have h' : L.starProjection z = 0 := by simpa using h
    exact (Submodule.starProjection_apply_eq_zero_iff L).1 h'
  -- along `M_{t₀}`, `Γ(x + v) = Γ(x)` for a.e. `v ∈ L`
  have : SigmaFinite (μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t₀})) := by
    rw [← hRt₀C]; exact hsf m Rt₀
  have hF1 : ∀ᵐ v ∂(μHE[d].restrict (L : Set (Euclid P))),
      ∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t₀})), Γ (x + v) = Γ x := by
    have hprod : ((μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t₀})).prod
        (μHE[d].restrict (L : Set (Euclid P))))
        {q : Euclid P × Euclid P | Γ (q.1 + q.2) ≠ Γ q.1} = 0 := by
      rw [Measure.measure_prod_null hEm]
      filter_upwards [ht₀N4] with x hx
      exact hx
    rw [Measure.prod_apply_symm hEm] at hprod
    have h0 := (lintegral_eq_zero_iff (measurable_measure_prodMk_right hEm)).1 hprod
    filter_upwards [h0] with v hv
    rw [ae_iff]
    exact hv
  have hF1' : ∀ᵐ t ∂(μHE[d].restrict (L : Set (Euclid P))),
      ∀ᵐ x ∂(μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t₀})),
        Γ (x + (t - t₀)) = Γ x := by
    have h := (hLtrans (-t₀) (L.neg_mem ht₀L)).quasiMeasurePreserving.ae hF1
    filter_upwards [h] with t ht
    simpa [sub_eq_add_neg] using ht
  have hF2 := htransfer _ ht₀N3
  /- ### Almost every slice is the translate of the base slice -/
  have hstar : ∀ᵐ t ∂(μHE[d].restrict (L : Set (Euclid P))),
      ∃ Rt : IMRep (univ : Set (Euclid P)) m,
        Rt.carrier = R.carrier ∩ {x | L.starProjection x = t} ∧ Rt.mult = R.mult ∧
          Rt.orient = ζ ∧
          (∀ γ : DifferentialForm (Euclid P) m, Rt.action γ = R₀.action (fun y => γ (y + t))) ∧
          (∀ A : Set (Euclid P), MeasurableSet A →
            Rt.measure A = R₀.measure ((fun y => y + t) ⁻¹' A)) := by
    filter_upwards [hslice_ae, hF1', hF2] with t ht hF1t hF2t
    have htL : t ∈ L := ht.1
    obtain ⟨Rt, hRtC, hRtθ, hRtξ⟩ := hsliceRep t ht
    obtain ⟨Rtt, hRttC, hRttθ, hRttξ, hRttact, hRttmeas⟩ := htransl m Rt₀ (t - t₀) hRt₀sm
    have hpt1 : ∀ z, Rt.carrier.indicator (fun y => (Rt.mult y : ℝ) • Rt.orient y) z =
        if L.starProjection z = t then (Γ z).comp lift else 0 := by
      intro z
      rw [hRtC, hRtθ, hRtξ]
      by_cases hzt : L.starProjection z = t
      · rw [ite_eq_left hzt]
        by_cases hzM : z ∈ R.carrier
        · rw [indicator_of_mem (show z ∈ R.carrier ∩ {x | L.starProjection x = t} from ⟨hzM, hzt⟩),
            hΓ_def, indicator_of_mem hzM, hζ_def, ContinuousLinearMap.smul_comp]
        · rw [indicator_of_notMem (fun h => hzM h.1), hΓ_def, indicator_of_notMem hzM,
            ContinuousLinearMap.zero_comp]
      · rw [ite_eq_right hzt, indicator_of_notMem (fun h => hzt h.2)]
    have hpw : ∀ z, L.starProjection (z - (t - t₀)) = L.starProjection z - t + t₀ := by
      intro z
      rw [map_sub, map_sub, hpfix t htL, hpfix t₀ ht₀L]
      abel
    have hpt2 : ∀ z, Rtt.carrier.indicator (fun y => (Rtt.mult y : ℝ) • Rtt.orient y) z =
        if L.starProjection z = t then (Γ (z - (t - t₀))).comp lift else 0 := by
      intro z
      have hiff : L.starProjection (z - (t - t₀)) = t₀ ↔ L.starProjection z = t := by
        rw [hpw]
        constructor
        · intro h
          have h' : L.starProjection z - t = 0 := by
            have := congrArg (fun y => y - t₀) h
            simpa using this
          exact sub_eq_zero.1 h'
        · intro h
          rw [h]
          abel
      have hmem : z ∈ Rtt.carrier ↔ (z - (t - t₀) ∈ R.carrier ∧ L.starProjection z = t) := by
        rw [hRttC, mem_preimage, hRt₀C, mem_inter_iff, mem_ofPred_eq, hiff]
      by_cases hzt : L.starProjection z = t
      · rw [ite_eq_left hzt]
        by_cases hzM : z - (t - t₀) ∈ R.carrier
        · rw [indicator_of_mem (hmem.2 ⟨hzM, hzt⟩), hΓ_def, indicator_of_mem hzM,
            hRttθ, hRttξ, hRt₀θ, hRt₀ξ, hζ_def, ContinuousLinearMap.smul_comp]
        · rw [indicator_of_notMem (fun h => hzM (hmem.1 h).1), hΓ_def, indicator_of_notMem hzM,
            ContinuousLinearMap.zero_comp]
      · rw [ite_eq_right hzt, indicator_of_notMem (fun h => hzt (hmem.1 h).2)]
    have hdens : ∀ᵐ z ∂(μHE[m].restrict (Rt.carrier ∪ Rtt.carrier)),
        Rt.carrier.indicator (fun y => (Rt.mult y : ℝ) • Rt.orient y) z =
          Rtt.carrier.indicator (fun y => (Rtt.mult y : ℝ) • Rtt.orient y) z := by
      rw [ae_restrict_union_iff]
      constructor
      · have hF2t' : ∀ᵐ z ∂(μHE[m].restrict Rt.carrier),
            Γ (z - L.starProjection z + t₀) = Γ z := by
          rw [hRtC]
          exact hF2t
        filter_upwards [hF2t', ae_restrict_mem Rt.measurableSet_carrier] with z hz hzM
        rw [hRtC] at hzM
        have hzt : L.starProjection z = t := hzM.2
        rw [hpt1, hpt2, ite_eq_left hzt, ite_eq_left hzt,
          show z - (t - t₀) = z - L.starProjection z + t₀ by rw [hzt]; abel, hz]
      · have hmp : MeasurePreserving (fun z => z - (t - t₀)) (μHE[m].restrict Rtt.carrier)
            (μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t₀})) := by
          rw [hRttC, hRt₀C]
          exact ((IsometryEquiv.subRight (t - t₀)).measurePreserving_euclideanHausdorffMeasure
            m).restrict_preimage_emb (MeasurableEquiv.subRight (t - t₀)).measurableEmbedding _
        filter_upwards [hmp.quasiMeasurePreserving.ae hF1t] with z hz
        rw [sub_add_cancel] at hz
        rw [hpt1, hpt2]
        split_ifs
        · rw [hz]
        · rfl
    have hact := hact_eq m Rt Rtt hdens
    obtain ⟨Tt, hTt⟩ := Submission.dtc_imrep_current P m univ Rt
    have hTt' : Rtt.Represents Tt := fun γ => (hTt γ).trans (hact _)
    have hmeas := Submission.imrep_measure_eq_of_represents_same_current P m univ Tt Rt Rtt
      isOpen_univ hTt hTt'
    refine ⟨Rt, hRtC, hRtθ, hRtξ, fun γ => ?_, fun A hA => ?_⟩
    · rw [hact γ, hRttact γ, hR₀act]
      congr 1
      funext y
      show γ (y + (t - t₀)) = γ (y + -t₀ + t)
      congr 1
      abel
    · rw [hmeas, hRttmeas A hA, hR₀meas _ (hA.preimage (measurable_add_const t))]
      congr 1
      ext y
      simp only [mem_preimage]
      rw [show y + -t₀ + t = y + (t - t₀) by abel]
  /- ### The signed coarea formula -/
  have hsigned : ∀ h : Euclid P → ℝ, Measurable h → Integrable h (μHE[n].restrict R.carrier) →
      ∫ x in R.carrier, h x ∂μHE[n] = ∫ t in (L : Set (Euclid P)),
        (∫ x in R.carrier ∩ {x | L.starProjection x = t}, h x ∂μHE[m]) ∂μHE[d] := by
    intro h hm hi
    have henorm : ∀ x, ‖h x‖ₑ ≤ ENNReal.ofReal (h x) + ENNReal.ofReal (-h x) := by
      intro x
      rcases le_total 0 (h x) with hx | hx
      · rw [Real.enorm_eq_ofReal hx]; exact le_self_add
      · rw [← enorm_neg, Real.enorm_eq_ofReal (neg_nonneg.2 hx)]; exact le_add_self
    obtain ⟨hpm, hp⟩ := hC1 (fun x => ENNReal.ofReal (h x)) hm.ennreal_ofReal
    obtain ⟨hnm, hn⟩ := hC1 (fun x => ENNReal.ofReal (-h x)) hm.neg.ennreal_ofReal
    have hpfin : ∫⁻ x in R.carrier, ENNReal.ofReal (h x) ∂μHE[n] ≠ ∞ :=
      ((lintegral_ofReal_le_lintegral_enorm h).trans_lt hi.2).ne
    have hnfin : ∫⁻ x in R.carrier, ENNReal.ofReal (-h x) ∂μHE[n] ≠ ∞ :=
      ((lintegral_ofReal_le_lintegral_enorm (fun x => -h x)).trans_lt hi.neg.2).ne
    rw [hp] at hpfin
    rw [hn] at hnfin
    have hpae := ae_lt_top' hpm hpfin
    have hnae := ae_lt_top' hnm hnfin
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, hp, hn,
      ← integral_toReal hpm hpae, ← integral_toReal hnm hnae,
      ← integral_sub (integrable_toReal_of_lintegral_ne_top hpm hpfin)
        (integrable_toReal_of_lintegral_ne_top hnm hnfin)]
    apply integral_congr_ae
    filter_upwards [hpae, hnae] with t htp htn
    have hit : Integrable h (μHE[m].restrict (R.carrier ∩ {x | L.starProjection x = t})) := by
      refine ⟨hm.aestronglyMeasurable, ?_⟩
      show ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t}, ‖h x‖ₑ ∂μHE[m] < ∞
      calc ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t}, ‖h x‖ₑ ∂μHE[m]
          ≤ ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t},
              (ENNReal.ofReal (h x) + ENNReal.ofReal (-h x)) ∂μHE[m] := lintegral_mono henorm
        _ = ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t}, ENNReal.ofReal (h x) ∂μHE[m] +
              ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t}, ENNReal.ofReal (-h x) ∂μHE[m] :=
            lintegral_add_left hm.ennreal_ofReal _
        _ < ∞ := ENNReal.add_lt_top.2 ⟨htp, htn⟩
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hit]
  /- ### Conclusions -/
  refine ⟨S₀, R₀, hS₀, ?_, ?_, ?_, ?_⟩
  · -- `spt S₀ ⊆ Lᗮ`
    intro x hx
    by_contra hxL
    have hopen : IsOpen ((Lᗮ : Set (Euclid P))ᶜ) := (Submodule.isClosed_orthogonal L).isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen x hxL
    apply hx.2
    refine mem_sUnion.2 ⟨ball x r, ⟨isOpen_ball, ?_, subset_univ _, ?_⟩, mem_ball_self hr⟩
    · exact (isCompact_closedBall x r).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · intro γ hγ
      rw [hS₀ γ]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro y hy
      have hyγ : y ∉ tsupport (γ : DifferentialForm (Euclid P) m) :=
        fun h => hball (hγ h) (hR₀L hy)
      rw [image_eq_zero_of_notMem_tsupport hyγ, map_zero, mul_zero]
  · -- `μ₀(ℝᴾ ∖ Lᗮ) = 0`
    have h0 : (μHE[m].restrict R₀.carrier) ((Lᗮ : Set (Euclid P))ᶜ) = 0 := by
      rw [Measure.restrict_apply (Submodule.isClosed_orthogonal L).measurableSet.compl]
      convert measure_empty (μ := (μHE[m] : Measure (Euclid P)))
      ext z
      simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hz hzR
      exact hz (hR₀L hzR)
    exact withDensity_absolutelyContinuous _ _ h0
  · -- `μ(A) = ∫_L μ₀(A - t) dt`
    intro A hA
    have h1 : R.measure A =
        ∫⁻ x in R.carrier, A.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
      rw [IMRep.measure, withDensity_apply _ hA, lintegral_indicator hA]
    rw [h1, (hC1 _ (hθm.indicator hA)).2]
    apply lintegral_congr_ae
    filter_upwards [hstar] with t ht
    obtain ⟨Rt, hRtC, hRtθ, -, -, hRtmeas⟩ := ht
    have h2 : ∫⁻ x in R.carrier ∩ {x | L.starProjection x = t},
        A.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[m] = Rt.measure A := by
      rw [IMRep.measure, withDensity_apply _ hA, hRtC, hRtθ, lintegral_indicator hA]
    rw [h2, hRtmeas A hA,
      show (fun y : Euclid P => y + t) = (fun y => t + y) from funext fun y => add_comm y t]
  · -- the product formula
    intro flat hflat ω
    have hflat_add : ∀ α β, flat (α + β) = flat α + flat β := fun α β => by
      ext v
      simp only [hflat, ContinuousAlternatingMap.add_apply]
    have hflat_smul : ∀ (c : ℝ) α, flat (c • α) = c • flat α := fun c α => by
      ext v
      simp only [hflat, ContinuousAlternatingMap.smul_apply]
    have := Submission.lcn_covector_finiteDimensional P n
    obtain ⟨flatL, hflatL⟩ : ∃ flatL : Covector (Euclid P) n →L[ℝ] Covector (Euclid P) m,
        ∀ α, flatL α = flat α :=
      ⟨LinearMap.toContinuousLinearMap ⟨⟨flat, hflat_add⟩, hflat_smul⟩, fun _ => rfl⟩
    -- at a good point, `ξ(α) = ζ(♭α)`
    have hflatgood : ∀ (Ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)),
        IsUnitOrientationOf Ξ Q → L ≤ Q → ∀ α, Ξ α = (Ξ.comp lift) (flat α) := by
      intro Ξ Q hΞ hLQ α
      obtain ⟨g, -, -, hgL, hsign⟩ := hstruct Ξ Q hΞ hLQ
      rw [ContinuousLinearMap.comp_apply]
      rcases hsign with h | h
      · rw [h, h, hlift _ g hgL, hflat]
      · rw [h, h, hlift _ g hgL, hflat]
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := hωc.bounded_above_of_compact_support ω.property.1.2
    have hint0 : Integrable (fun x => (R.mult x : ℝ) *
        R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) :=
      (Submission.dpf_pfc_imrep_pairing_integrable_abs_le P n univ
        (tsupport (ω : DifferentialForm (Euclid P) n)) R ω C ω.property.1.2 (subset_univ _)
        hωc.aestronglyMeasurable (fun x hx => image_eq_zero_of_notMem_tsupport hx) hC).1
    have hae : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
        (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) =
          (R.mult x : ℝ) * ζ x (flat ((ω : DifferentialForm (Euclid P) n) x)) := by
      filter_upwards [hgood] with x hx
      obtain ⟨hxe, Q, -, hQo, hLQ⟩ := hx
      rw [hζ_def, hxe, ← hflatgood _ Q hQo hLQ]
    have hmeas_h : Measurable fun x =>
        (R.mult x : ℝ) * ζ x (flat ((ω : DifferentialForm (Euclid P) n) x)) := by
      have h1 : StronglyMeasurable fun x =>
          ζ x (flatL ((ω : DifferentialForm (Euclid P) n) x)) :=
        (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
          (hζsm.prodMk (flatL.continuous.comp hωc).stronglyMeasurable)
      simp only [hflatL] at h1
      exact hθr.mul h1.measurable
    have hint : Integrable (fun x => (R.mult x : ℝ) *
        ζ x (flat ((ω : DifferentialForm (Euclid P) n) x))) (μHE[n].restrict R.carrier) :=
      hint0.congr hae
    rw [hrep ω]
    show ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
      ∂μHE[n] = _
    rw [integral_congr_ae hae, hsigned _ hmeas_h hint]
    apply integral_congr_ae
    filter_upwards [hstar] with t ht
    obtain ⟨Rt, hRtC, hRtθ, hRtξ, hRtact, -⟩ := ht
    have hγ : IsTestForm (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ∧
        tsupport (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) ⊆ univ := by
      refine ⟨⟨?_, ?_⟩, subset_univ _⟩
      · have : (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) =
            fun y => flatL ((ω : DifferentialForm (Euclid P) n) (t + y)) :=
          funext fun y => (hflatL _).symm
        rw [this]
        exact flatL.contDiff.comp (ω.property.1.1.comp (contDiff_const.add contDiff_id))
      · have : (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) =
            flatL ∘ ((ω : DifferentialForm (Euclid P) n) ∘ (Homeomorph.addLeft t)) :=
          funext fun y => (hflatL _).symm
        rw [this]
        exact (ω.property.1.2.comp_homeomorph (Homeomorph.addLeft t)).comp_left (map_zero flatL)
    have hce : currentEval S₀ (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y))) =
        S₀ ⟨_, hγ⟩ := by
      unfold currentEval
      rw [dite_eq_left hγ]
    have hRtact' : Rt.action (fun x => flat ((ω : DifferentialForm (Euclid P) n) x)) =
        ∫ x in R.carrier ∩ {x | L.starProjection x = t},
          (R.mult x : ℝ) * ζ x (flat ((ω : DifferentialForm (Euclid P) n) x)) ∂μHE[m] := by
      simp only [IMRep.action, hRtC, hRtθ, hRtξ]
    rw [hce, hS₀ ⟨_, hγ⟩, ← hRtact', hRtact]
    show R₀.action (fun y => flat ((ω : DifferentialForm (Euclid P) n) (y + t))) =
      R₀.action (fun y => flat ((ω : DifferentialForm (Euclid P) n) (t + y)))
    simp only [add_comm]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
