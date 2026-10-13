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
/-- **Simon 6.1.15, 6.3.4–3.5** (Euclidean coefficient norm versus Gram determinants):
(1) `|α(v₁, …, vₙ)| ≤ |α|_E · det(⟨vᵢ, vⱼ⟩)^{1/2}` for every `n`-covector `α` on `ℝᴾ`;
(2) every orthonormal `τ₁, …, τₙ` admits an `n`-covector `α` with `|α|_E ≤ 1` and `α(τ) = 1`.
Expand `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I` (multilinearity, alternation,
Leibniz).  For the determinant covector `u ↦ det(⟨uₐ, v_b⟩)` this is Cauchy–Binet,
`det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`; then (1) is Cauchy–Schwarz over the `I`, and (2) holds for the
determinant covector of `τ`. -/
theorem Submission.covectorEuclideanNorm_gram_bounds : ∀ (P n : ℕ), (∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P), |α v| ≤ covectorEuclideanNorm α * Real.sqrt (Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)))) ∧ ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ → ∃ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ 1 ∧ α τ = 1 := by
  intro P n
  classical
  set e := EuclideanSpace.basisFun (Fin P) ℝ with he
  -- `α(v) = Σ_I α(e_I) det V_I` over strictly increasing `I`, with `(V_I)ₐⱼ = ⟨e_{I a}, vⱼ⟩`
  have hexp : ∀ (α : Covector (Euclid P) n) (v : Fin n → Euclid P),
      α v = ∑ I : Fin n → Fin P, if StrictMono I then
        α (fun i => e (I i)) * Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 := by
    intro α v
    set c : Fin n → Fin P → ℝ := fun j k => inner ℝ (e k) (v j) with hc
    have hv : v = fun j => ∑ k, c j k • e k := funext fun j => (e.sum_repr' (v j)).symm
    -- multilinearity: `α(v) = Σ_f (∏ⱼ vⱼ(f j)) α(e_f)`
    have h2 : α v = ∑ f : Fin n → Fin P, (∏ j, c j (f j)) * α (fun j => e (f j)) := by
      conv_lhs => rw [hv]
      rw [α.map_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← smul_eq_mul, ← α.map_smul_univ]
    -- alternation: non-injective `f` contribute `0`
    have h3 : ∀ f : Fin n → Fin P, ¬ Injective f → α (fun j => e (f j)) = 0 := fun f hf =>
      α.map_eq_zero_of_not_injective _ (fun h => hf (Injective.of_comp (f := ⇑e) h))
    rw [h2, ← Finset.sum_filter_of_ne (p := Injective) (fun f _ hne => by
      by_contra hf
      exact hne (by rw [h3 f hf, mul_zero]))]
    rw [← Finset.sum_filter]
    simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
    rw [← Finset.sum_product']
    symm
    -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `f`; `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
    refine Finset.sum_bij (fun p _ => fun j => p.1 (p.2 j)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp.1.injective.comp p.2.injective
    · intro p hp q hq hpq
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
      have hrange : Set.range p.1 = Set.range q.1 := by
        have h1 : Set.range (fun j => p.1 (p.2 j)) = Set.range p.1 := (EquivLike.range_comp p.1 p.2)
        have h2 : Set.range (fun j => q.1 (q.2 j)) = Set.range q.1 := (EquivLike.range_comp q.1 q.2)
        rw [← h1, ← h2, hpq]
      have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
      have hσ : p.2 = q.2 := by
        ext j
        have := congr_fun hpq j
        rw [hI] at this
        exact congrArg Fin.val (hq.injective this)
      exact Prod.ext hI hσ
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      refine ⟨(f ∘ Tuple.sort f, (Tuple.sort f)⁻¹), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        exact (Tuple.monotone_sort f).strictMono_of_injective (hf.comp (Tuple.sort f).injective)
      · funext j
        simp
    · intro p hp
      have hperm : α (fun j => e (p.1 (p.2 j))) = Equiv.Perm.sign p.2 • α (fun j => e (p.1 j)) :=
        α.toAlternatingMap.map_perm (fun j => e (p.1 j)) p.2
      rw [hperm]
      simp only [hc, Units.smul_def, zsmul_eq_mul]
      ring
  -- the determinant covector `u ↦ det(⟨uₐ, τ_b⟩)`
  have hdet : ∀ τ : Fin n → Euclid P, ∃ β : Covector (Euclid P) n,
      ∀ u : Fin n → Euclid P, β u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
    intro τ
    let L : Euclid P →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi fun b => (innerSL ℝ (τ b) : Euclid P →L[ℝ] ℝ).toLinearMap
    let f : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := Matrix.detRowAlternating.compLinearMap L
    have hf : ∀ u, f u = Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      intro u
      show Matrix.det (Matrix.of fun a b => L (u a) b) = _
      congr 1
      ext a b
      simp [L, real_inner_comm]
    have hcont : Continuous fun u : Fin n → Euclid P =>
        Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := by
      apply Continuous.matrix_det
      apply continuous_matrix
      intro a b
      exact Continuous.inner (f := fun u : Fin n → Euclid P => u a) (g := fun _ => τ b)
        (continuous_apply a) continuous_const
    refine ⟨{ f with cont := ?_ }, fun u => hf u⟩
    have : (f : (Fin n → Euclid P) → ℝ) =
        fun u => Matrix.det (Matrix.of fun a b => inner ℝ (u a) (τ b)) := funext hf
    simpa [this] using hcont
  -- Cauchy–Binet: `det(⟨vᵢ, vⱼ⟩) = Σ_I (det V_I)²`, the expansion of the determinant covector of `v`
  have hcb : ∀ v : Fin n → Euclid P, Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) =
      ∑ I : Fin n → Fin P, if StrictMono I then
        Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) ^ 2 else 0 := by
    intro v
    obtain ⟨β, hβ⟩ := hdet v
    rw [← hβ v, hexp β v]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [hβ, pow_two]
    · rfl
  refine ⟨fun α v => ?_, fun τ hτ => ?_⟩
  · -- (1): Cauchy–Schwarz for `Σ_I α(e_I) det V_I`
    set a : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then α (fun i => e (I i)) else 0
      with ha
    set d : (Fin n → Fin P) → ℝ := fun I => if StrictMono I then
      Matrix.det (Matrix.of fun a j => inner ℝ (e (I a)) (v j)) else 0 with hd
    have hv : α v = ∑ I, a I * d I := by
      rw [hexp α v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha, hd]
      split_ifs <;> simp
    have hnorm : covectorEuclideanNorm α = Real.sqrt (∑ I, a I ^ 2) := by
      unfold covectorEuclideanNorm
      rw [← he]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [ha]
      split_ifs <;> simp
    have hgram : Matrix.det (Matrix.of fun i j => inner ℝ (v i) (v j)) = ∑ I, d I ^ 2 := by
      rw [hcb v]
      refine Finset.sum_congr rfl fun I _ => ?_
      simp only [hd]
      split_ifs <;> simp
    rw [hv, hnorm, hgram, abs_le]
    constructor
    · have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun I => -a I) d
      simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a d
  · -- (2): the determinant covector `β` of `τ` has `β(τ) = det 1 = 1` and
    -- `|β|_E² = Σ_I β(e_I)² = det(⟨τᵢ, τⱼ⟩) = 1`
    obtain ⟨β, hβ⟩ := hdet τ
    have hone : (Matrix.of fun a b => inner ℝ (τ a) (τ b) : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      ext a b
      rw [Matrix.of_apply, Matrix.one_apply]
      exact (orthonormal_iff_ite.mp hτ) a b
    have hβτ : β τ = 1 := by rw [hβ, hone, Matrix.det_one]
    refine ⟨β, ?_, hβτ⟩
    have hsum : (∑ I : Fin n → Fin P, if StrictMono I then (β (fun i => e (I i))) ^ 2 else 0) = 1 := by
      have := hcb τ
      rw [hone, Matrix.det_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun I _ => ?_
      split_ifs
      · rw [hβ]
      · rfl
    unfold covectorEuclideanNorm
    rw [← he, hsum, Real.sqrt_one]
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- `t ↦ p + t v` is an isometry `ℝ → ℝᴾ` for a unit vector `v`. -/
theorem Submission.odc_line_isometry {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) :
    Isometry (fun t : ℝ => p + t • v) := by
  refine Isometry.of_dist_eq fun s t => ?_
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq,
    Real.norm_eq_abs]

theorem Submission.odc_line_measurableEmbedding {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) :
    MeasurableEmbedding (fun t : ℝ => p + t • v) :=
  (Submission.odc_line_isometry p v hv).isClosedEmbedding.measurableEmbedding

/-- `μHE[1] = volume` on `ℝ`. -/
theorem Submission.odc_muHE_one_real : (μHE[1] : Measure ℝ) = volume := by
  have h := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  rwa [Module.finrank_self] at h

theorem Submission.odc_line_map {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) :
    Measure.map (fun t : ℝ => p + t • v) volume =
      (μHE[1] : Measure (Euclid P)).restrict (range fun t : ℝ => p + t • v) := by
  rw [← Submission.odc_muHE_one_real]
  exact (Submission.odc_line_isometry p v hv).map_euclideanHausdorffMeasure

/-- `H¹⌞γ(I) = γ_#(ℒ¹⌞I)` for `γ(t) = p + t v`. -/
theorem Submission.odc_line_restrict {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) (I : Set ℝ) :
    (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => p + t • v) '' I) =
      Measure.map (fun t : ℝ => p + t • v) (volume.restrict I) := by
  have hγ := Submission.odc_line_measurableEmbedding p v hv
  have hinj := (Submission.odc_line_isometry p v hv).injective
  rw [← Measure.restrict_restrict_of_subset (image_subset_range _ _),
    ← Submission.odc_line_map p v hv, hγ.restrict_map, preimage_image_eq _ hinj]

theorem Submission.odc_line_measure_image {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) (I : Set ℝ) :
    (μHE[1] : Measure (Euclid P)) ((fun t : ℝ => p + t • v) '' I) = volume I := by
  rw [(Submission.odc_line_isometry p v hv).euclideanHausdorffMeasure_image,
    Submission.odc_muHE_one_real]

theorem Submission.odc_line_integral {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) (I : Set ℝ)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (F : Euclid P → G) :
    ∫ x in (fun t : ℝ => p + t • v) '' I, F x ∂μHE[1] = ∫ t in I, F (p + t • v) := by
  rw [Submission.odc_line_restrict p v hv I,
    (Submission.odc_line_measurableEmbedding p v hv).integral_map]

theorem Submission.odc_line_lintegral {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1) (I : Set ℝ)
    (F : Euclid P → ℝ≥0∞) :
    ∫⁻ x in (fun t : ℝ => p + t • v) '' I, F x ∂μHE[1] = ∫⁻ t in I, F (p + t • v) := by
  rw [Submission.odc_line_restrict p v hv I,
    (Submission.odc_line_measurableEmbedding p v hv).lintegral_map]

theorem Submission.odc_line_measurableSet_image {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1)
    {I : Set ℝ} (hI : MeasurableSet I) :
    MeasurableSet ((fun t : ℝ => p + t • v) '' I) :=
  (Submission.odc_line_measurableEmbedding p v hv).measurableSet_image.2 hI

/-- A function locally integrable on `Ioi 0` times a continuous compactly supported function with
support in `Ioi 0` is integrable. -/
theorem Submission.odc_dubois_integrable {g ψ : ℝ → ℝ} (hg : LocallyIntegrableOn g (Ioi 0))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioi 0) :
    Integrable (fun t => g t * ψ t) := by
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
  · exact (hg.integrableOn_compact_subset hψs hψc).mul_continuousOn hψ.continuousOn hψc
  · exact (support_mul_subset_right _ _).trans (subset_tsupport ψ)

/-- A smooth compactly supported function with support in `Ioi 0` and zero integral is the
derivative of a smooth compactly supported function with support in `Ioi 0`. -/
theorem Submission.odc_dubois_primitive {f : ℝ → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hfc : HasCompactSupport f) (hfs : tsupport f ⊆ Ioi 0) (hf0 : ∫ t, f t = 0) :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      tsupport Ψ ⊆ Ioi 0 ∧ deriv Ψ = f := by
  obtain ⟨α, hα, hαf⟩ := hfc.isCompact.exists_forall_le' continuousOn_id fun x hx => hfs hx
  obtain ⟨β, hβ⟩ := hfc.isCompact.bddAbove
  have hderiv : ∀ t, HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, f x) (f t) t :=
    fun t => (hf.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd : deriv (fun u => ∫ x in (0 : ℝ)..u, f x) = f := funext fun t => (hderiv t).deriv
  -- the primitive vanishes outside `[α, β]`
  have hvan : ∀ t ∉ Icc α β, ∫ x in (0 : ℝ)..t, f x = 0 := by
    intro t ht
    by_cases htα : t < α
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
      intro x hx
      refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
      rw [uIcc, mem_Icc] at hx
      exact (hαf x hxs).not_gt (hx.2.trans_lt (max_lt hα htα))
    · have hβt : β < t := not_le.1 fun h' => ht ⟨not_lt.1 htα, h'⟩
      rw [intervalIntegral.integral_of_le (hα.le.trans (not_lt.1 htα)),
        setIntegral_eq_integral_of_forall_compl_eq_zero, hf0]
      intro x hx
      exact image_eq_zero_of_notMem_tsupport fun hxs => hx ⟨hfs hxs, (hβ hxs).trans hβt.le⟩
  refine ⟨fun u => ∫ x in (0 : ℝ)..u, f x, ?_, HasCompactSupport.intro isCompact_Icc hvan,
    ?_, hd⟩
  · exact contDiff_infty_iff_deriv.2 ⟨fun t => (hderiv t).differentiableAt, by rwa [hd]⟩
  · exact (closure_minimal (support_subset_iff'.2 hvan) isClosed_Icc).trans
      fun x hx => hα.trans_le hx.1

/-- One-dimensional constancy (du Bois-Reymond). -/
theorem Submission.odc_du_bois_reymond (g : ℝ → ℝ) (hg : LocallyIntegrableOn g (Ioi 0))
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 0 → ∫ t in Ioi (0 : ℝ), g t * deriv φ t = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g t = c := by
  -- a fixed bump function `b` supported in `[1/2, 3/2]`
  obtain ⟨b, hb⟩ : ∃ b : ContDiffBump (1 : ℝ), b.rOut = 1 / 2 :=
    ⟨⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩, rfl⟩
  have hbs : tsupport b ⊆ Ioi 0 := by
    rw [b.tsupport_eq, hb, Real.closedBall_eq_Icc]
    exact fun x hx => show (0 : ℝ) < x by linarith [hx.1]
  have hI : 0 < ∫ t, b t :=
    b.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
      b.hasCompactSupport (fun x => b.nonneg' x) (x := 1)
      (by rw [b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)]; exact one_ne_zero)
  have hbi := b.continuous.integrable_of_hasCompactSupport (μ := volume) b.hasCompactSupport
  have hgb := Submission.odc_dubois_integrable hg b.continuous b.hasCompactSupport hbs
  -- `g` annihilates test functions of zero integral
  have key : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioi 0 → ∫ t, φ t = 0 → ∫ t, g t * φ t = 0 := by
    intro φ hφ hφc hφs hφ0
    obtain ⟨Ψ, hΨ, hΨc, hΨs, rfl⟩ := Submission.odc_dubois_primitive hφ hφc hφs hφ0
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
    · exact h Ψ hΨ hΨc hΨs
    · intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hφs h')), mul_zero]
  refine ⟨(∫ t, g t * b t) / ∫ t, b t, ?_⟩
  have hU := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun t => g t - (∫ t, g t * b t) / ∫ t, b t) (hg.sub (locallyIntegrableOn_const _)) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (hU.mono fun t ht ht' => sub_eq_zero.1 (ht ht'))
  intro ψ hψ hψc hψs
  have hψi := hψ.continuous.integrable_of_hasCompactSupport (μ := volume) hψc
  have hgψ := Submission.odc_dubois_integrable hg hψ.continuous hψc hψs
  set a := (∫ t, ψ t) / ∫ t, b t with ha
  have hs : tsupport (fun t => ψ t - a * b t) ⊆ Ioi 0 := by
    refine (closure_minimal (support_subset_iff'.2 fun x hx => ?_)
      ((isClosed_tsupport ψ).union (isClosed_tsupport b))).trans (union_subset hψs hbs)
    simp only [mem_union, not_or] at hx
    simp [image_eq_zero_of_notMem_tsupport hx.1, image_eq_zero_of_notMem_tsupport hx.2]
  have H : ∫ t, g t * (ψ t - a * b t) = 0 :=
    key _ (hψ.sub (contDiff_const.mul b.contDiff)) (hψc.sub b.hasCompactSupport.mul_left) hs
      (by rw [integral_sub hψi (hbi.const_mul a), integral_const_mul, ha,
        div_mul_cancel₀ _ hI.ne', sub_self])
  have e1 : (fun t => g t * (ψ t - a * b t)) = fun t => g t * ψ t - a * (g t * b t) := by
    funext t; ring
  have e2 : (fun t => ψ t • (g t - (∫ t, g t * b t) / ∫ t, b t)) =
      fun t => g t * ψ t - (∫ t, g t * b t) / (∫ t, b t) * ψ t := by
    funext t; rw [smul_eq_mul]; ring
  rw [e1, integral_sub hgψ (hgb.const_mul a), integral_const_mul] at H
  rw [e2, integral_sub hgψ (hψi.const_mul _), integral_const_mul, ← H, ha]
  ring

/-- Scaling a ball by a factor `c > 0` multiplies its measure by `c`. -/
theorem Submission.odc_finiterays_ball_smul {P : ℕ} (μ : Measure (Euclid P))
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W)
    {c : ℝ} (hc : 0 < c) (x : Euclid P) (r : ℝ) :
    μ (ball (c • x) (c * r)) = ENNReal.ofReal c * μ (ball x r) := by
  rw [← hscale c hc _ isOpen_ball, image_smul, smul_ball hc.ne', Real.norm_of_nonneg hc.le]

/-- For an open cone `K`, `μ (K ∩ B_r(0)) = r μ (K ∩ B_1(0))`. -/
theorem Submission.odc_finiterays_cone_inter_ball {P : ℕ} (μ : Measure (Euclid P))
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W)
    {K : Set (Euclid P)} (hK : IsOpen K) (hcone : ∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K)
    {r : ℝ} (hr : 0 < r) :
    μ (K ∩ ball 0 r) = ENNReal.ofReal r * μ (K ∩ ball 0 1) := by
  rw [← hscale r hr _ (hK.inter isOpen_ball)]
  congr 1
  ext y
  constructor
  · rintro ⟨hyK, hyr⟩
    refine ⟨r⁻¹ • y, ⟨hcone _ (inv_pos.2 hr) y hyK, ?_⟩, smul_inv_smul₀ hr.ne' y⟩
    rw [mem_ball_zero_iff] at hyr ⊢
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hr).le, inv_mul_lt_iff₀ hr, mul_one]
    exact hyr
  · rintro ⟨x, ⟨hxK, hx1⟩, rfl⟩
    refine ⟨hcone r hr x hxK, ?_⟩
    rw [mem_ball_zero_iff] at hx1 ⊢
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_lt_of_lt_one_right hr hx1

/-- Cones of aperture `ρ ≤ 1` around the rays through `2ρ`-separated unit vectors are
disjoint. -/
theorem Submission.odc_finiterays_cone_disjoint {P : ℕ} {σ σ' x : Euclid P} {ρ t s : ℝ}
    (hσ : ‖σ‖ = 1) (hσ' : ‖σ'‖ = 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hsep : 2 * ρ ≤ ‖σ - σ'‖)
    (ht : 0 < t) (hs : 0 < s) (hx : ‖x - t • σ‖ < t * ρ) (hx' : ‖x - s • σ'‖ < s * ρ) :
    False := by
  have h1 : ‖t • σ - s • σ'‖ < (t + s) * ρ :=
    calc ‖t • σ - s • σ'‖ = ‖(x - s • σ') - (x - t • σ)‖ := by congr 1; abel
      _ ≤ ‖x - s • σ'‖ + ‖x - t • σ‖ := norm_sub_le _ _
      _ < s * ρ + t * ρ := add_lt_add hx' hx
      _ = (t + s) * ρ := by ring
  have h2 : ‖t • σ - s • σ'‖ ^ 2 = (t - s) ^ 2 + t * s * ‖σ - σ'‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, hσ, hσ', Real.norm_of_nonneg ht.le, Real.norm_of_nonneg hs.le]
    simp only [conj_trivial]
    ring
  have e1 : (t - s) ^ 2 * ρ ^ 2 ≤ (t - s) ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg _) (by nlinarith)
  have e2 : t * s * (4 * ρ ^ 2) ≤ t * s * ‖σ - σ'‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  nlinarith [norm_nonneg (t • σ - s • σ')]

/-- If `ρ ≤ μ (B_ρ(σ))` for a unit vector `σ` and `0 < ρ < 1`, then the cone of aperture `ρ`
around the ray through `σ` has measure at least `1/2` in the unit ball. -/
theorem Submission.odc_finiterays_one_le_two_mul {P : ℕ} (μ : Measure (Euclid P))
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W)
    (hfin : μ (ball 0 1) ≠ ∞) {σ : Euclid P} (hσ : ‖σ‖ = 1) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hdens : ENNReal.ofReal ρ ≤ μ (ball σ ρ)) :
    1 ≤ 2 * μ ((⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) ∩ ball 0 1) := by
  set K := ⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)
  have hK : IsOpen K := isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_ball
  have hcone : ∀ c : ℝ, 0 < c → ∀ x ∈ K, c • x ∈ K := by
    intro c hc x hx
    obtain ⟨t, ht, hx⟩ := mem_iUnion₂.1 hx
    refine mem_iUnion₂.2 ⟨c * t, mul_pos hc ht, ?_⟩
    rw [mem_ball, mul_smul, dist_smul₀, Real.norm_of_nonneg hc.le, mul_assoc]
    exact mul_lt_mul_of_pos_left hx hc
  have hscaleK := fun r (hr : 0 < r) =>
    Submission.odc_finiterays_cone_inter_ball μ hscale hK hcone hr
  -- `B_ρ(σ)` and `K ∩ B_{1-ρ}(0)` are disjoint subsets of `K ∩ B_{1+ρ}(0)`
  have hsub : ball σ ρ ∪ (K ∩ ball 0 (1 - ρ)) ⊆ K ∩ ball 0 (1 + ρ) := by
    refine union_subset (fun x hx => ⟨mem_iUnion₂.2 ⟨1, one_pos, by simpa using hx⟩, ?_⟩)
      (inter_subset_inter_right _ (ball_subset_ball (by linarith)))
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    calc ‖x‖ = ‖(x - σ) + σ‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - σ‖ + ‖σ‖ := norm_add_le _ _
      _ < 1 + ρ := by rw [hσ]; linarith
  have hdisj : Disjoint (ball σ ρ) (K ∩ ball 0 (1 - ρ)) := by
    refine disjoint_left.2 fun x hx hx' => ?_
    rw [mem_ball, dist_eq_norm] at hx
    have h1 := mem_ball_zero_iff.1 hx'.2
    have h2 : ‖σ‖ ≤ ‖x - σ‖ + ‖x‖ := by
      rw [norm_sub_rev]
      calc ‖σ‖ = ‖(σ - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖σ - x‖ + ‖x‖ := norm_add_le _ _
    rw [hσ] at h2
    linarith
  have key := measure_mono (μ := μ) hsub
  rw [measure_union hdisj (hK.inter isOpen_ball).measurableSet, hscaleK (1 - ρ) (by linarith),
    hscaleK (1 + ρ) (by linarith)] at key
  have key' := (add_le_add hdens le_rfl).trans key
  have ha : μ (K ∩ ball 0 1) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono inter_subset_right)
  rw [← ENNReal.ofReal_toReal ha] at key' ⊢
  set a := (μ (K ∩ ball 0 1)).toReal
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_add hρ0.le (by nlinarith), ENNReal.ofReal_le_ofReal_iff (by positivity)]
    at key'
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Any finite set of unit vectors in the support of `μ` has at most `2 μ(B_1(0))` elements. -/
theorem Submission.odc_finiterays_card_le {P : ℕ} (μ : Measure (Euclid P))
    (hfin : μ (ball 0 1) ≠ ∞)
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W)
    (hdens : ∀ x : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ μ (ball x ρ))
    (T : Finset (Euclid P)) (hT : ∀ σ ∈ T, ‖σ‖ = 1 ∧ ∀ ε : ℝ, 0 < ε → μ (ball σ ε) ≠ 0) :
    (T.card : ℝ≥0∞) ≤ 2 * μ (ball 0 1) := by
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ σ ∈ T, ENNReal.ofReal ρ ≤ μ (ball σ ρ) :=
    (eventually_all_finset T).2 fun σ hσ => hdens σ (hT σ hσ).2
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ σ ∈ T, ∀ σ' ∈ T, σ ≠ σ' → 2 * ρ ≤ ‖σ - σ'‖ := by
    refine (eventually_all_finset T).2 fun σ _ => (eventually_all_finset T).2 fun σ' _ => ?_
    rcases eq_or_ne σ σ' with h | h
    · exact Eventually.of_forall fun _ h' => absurd h h'
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (norm_pos_iff.2 (sub_ne_zero.2 h)))]
        with ρ hρ _
      linarith [hρ.2]
  obtain ⟨ρ, h1ρ, h2ρ, hρ⟩ := (h1.and (h2.and (Ioo_mem_nhdsGT zero_lt_one))).exists
  set K : Euclid P → Set (Euclid P) :=
    fun σ => (⋃ (t : ℝ) (_ : 0 < t), ball (t • σ) (t * ρ)) ∩ ball 0 1
  have hdisj : (T : Set (Euclid P)).PairwiseDisjoint K := by
    intro σ hσ σ' hσ' hne
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.1 hx.1
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.1 hx'.1
    rw [mem_ball, dist_eq_norm] at hxt hxs
    exact Submission.odc_finiterays_cone_disjoint (hT σ hσ).1 (hT σ' hσ').1 hρ.1 hρ.2.le
      (h2ρ σ hσ σ' hσ' hne) ht hs hxt hxs
  have hmeas : ∀ σ ∈ T, MeasurableSet (K σ) := fun σ _ =>
    ((isOpen_iUnion fun t => isOpen_iUnion fun _ => isOpen_ball).inter isOpen_ball).measurableSet
  calc (T.card : ℝ≥0∞) = ∑ σ ∈ T, 1 := by simp
    _ ≤ ∑ σ ∈ T, 2 * μ (K σ) := Finset.sum_le_sum fun σ hσ =>
        Submission.odc_finiterays_one_le_two_mul μ hscale hfin (hT σ hσ).1 hρ.1 hρ.2 (h1ρ σ hσ)
    _ = 2 * μ (⋃ σ ∈ T, K σ) := by rw [measure_biUnion_finset hdisj hmeas, Finset.mul_sum]
    _ ≤ 2 * μ (ball 0 1) := by
        gcongr
        exact iUnion₂_subset fun σ _ => inter_subset_right

/-- A 1-homogeneous measure that is finite on the unit ball has no atom at the origin. -/
theorem Submission.odc_finiterays_measure_zero {P : ℕ} (μ : Measure (Euclid P))
    (hfin : μ (ball 0 1) ≠ ∞)
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W) :
    μ {0} = 0 := by
  have h : Tendsto (fun r : ℝ => ENNReal.ofReal r * μ (ball 0 1)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r) (𝓝[>] 0) (𝓝 0) := by
      simpa using (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ)))).mono_left
        nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h0 (Or.inr hfin)
  refine le_zero_iff.1 (ge_of_tendsto h ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  have := Submission.odc_finiterays_ball_smul μ hscale hr 0 1
  rw [smul_zero, mul_one] at this
  rw [← this]
  exact measure_mono (singleton_subset_iff.2 (mem_ball_self hr))

/-- A 1-homogeneous locally finite measure with density bounded below on its support lives on
finitely many open rays. -/
theorem Submission.odc_finite_rays {P : ℕ} (μ : Measure (Euclid P))
    (hfin : ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞)
    (hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      μ ((fun x => lam • x) '' W) = ENNReal.ofReal lam * μ W)
    (hdens : ∀ x : Euclid P, (∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0) →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ μ (ball x ρ)) :
    ∃ F : Finset (Euclid P), (∀ e ∈ F, ‖e‖ = 1) ∧
      μ ((⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0 := by
  have hB : μ (ball (0 : Euclid P) 1) ≠ ∞ :=
    ne_top_of_le_ne_top (hfin _ (isCompact_closedBall 0 1)) (measure_mono ball_subset_closedBall)
  set S := {x : Euclid P | ∀ ε : ℝ, 0 < ε → μ (ball x ε) ≠ 0}
  -- the unit vectors in the support of `μ` form a finite set
  have hU : {σ : Euclid P | ‖σ‖ = 1 ∧ σ ∈ S}.Finite := by
    by_contra h
    have h2 : (2 : ℝ≥0∞) * μ (ball 0 1) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hB
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h2
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq h n
    have := Submission.odc_finiterays_card_le μ hB hscale hdens T fun σ hσ => hTsub hσ
    rw [hTcard] at this
    exact lt_irrefl _ (this.trans_lt hn)
  refine ⟨hU.toFinset, fun e he => (hU.mem_toFinset.1 he).1, ?_⟩
  -- the complement of the rays lies in `{0} ∪ Sᶜ`
  have hsub : (⋃ e ∈ hU.toFinset, (fun t : ℝ => t • e) '' Ioi 0)ᶜ ⊆ {0} ∪ Sᶜ := by
    intro x hx
    by_contra hx'
    simp only [mem_union, mem_singleton_iff, mem_compl_iff, not_or, not_not] at hx'
    obtain ⟨hx0, hxS⟩ := hx'
    have hn : 0 < ‖x‖ := norm_pos_iff.2 hx0
    refine hx (mem_iUnion₂.2 ⟨‖x‖⁻¹ • x, hU.mem_toFinset.2 ⟨?_, ?_⟩, ‖x‖, hn, ?_⟩)
    · rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hn).le, inv_mul_cancel₀ hn.ne']
    · intro ε hε
      have := Submission.odc_finiterays_ball_smul μ hscale (inv_pos.2 hn) x (‖x‖ * ε)
      rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] at this
      rw [this]
      exact mul_ne_zero (ENNReal.ofReal_pos.2 (inv_pos.2 hn)).ne' (hxS _ (mul_pos hn hε))
    · exact smul_inv_smul₀ hn.ne' x
  refine measure_mono_null hsub
    (measure_union_null (Submission.odc_finiterays_measure_zero μ hB hscale) ?_)
  refine measure_null_of_locally_null _ fun x hx => ?_
  simp only [S, mem_compl_iff, mem_ofPred_eq, not_forall, not_not, exists_prop] at hx
  obtain ⟨ε, hε, h0⟩ := hx
  exact ⟨ball x ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hε), h0⟩

/-- For `r ≠ 0`, the blow-up `η_{x,r}(M)` is the preimage of `M` under `y ↦ x + r y`. -/
theorem Submission.odc_tangent_blowUp_image_eq {P : ℕ} (M : Set (Euclid P)) (x : Euclid P)
    {r : ℝ} (hr : r ≠ 0) :
    Poincare.SimonGMT.Chapter03.blowUpMap x r '' M = (fun y => x + r • y) ⁻¹' M := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr] using hz
  · intro hy
    exact ⟨_, hy, by simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, hr]⟩

/-- Blow-ups preserve `H¹`-null sets. -/
theorem Submission.odc_tangent_blowUp_null {P : ℕ} {N : Set (Euclid P)}
    (hN : (μHE[1] : Measure (Euclid P)) N = 0) (x : Euclid P) (r : ℝ) :
    (μHE[1] : Measure (Euclid P)) (Poincare.SimonGMT.Chapter03.blowUpMap x r '' N) = 0 := by
  have hlip : LipschitzWith ‖r⁻¹‖₊ (Poincare.SimonGMT.Chapter03.blowUpMap x r) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dist_smul₀, dist_sub_right, coe_nnnorm,
        le_refl]
  refine nonpos_iff_eq_zero.1 ?_
  calc _ ≤ (‖r⁻¹‖₊ : ℝ≥0∞) ^ 1 * μHE[1] N :=
        Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn 1
          hlip.lipschitzOnWith
    _ = 0 := by rw [hN, mul_zero]

/-- `x + ρ y` lies on the line through `x` in direction `v` iff `y ∈ span {v}` (`ρ ≠ 0`). -/
theorem Submission.odc_tangent_mem_range_iff {P : ℕ} (x v y : Euclid P) {ρ : ℝ} (hρ : ρ ≠ 0) :
    x + ρ • y ∈ range (fun s : ℝ => x + s • v) ↔ y ∈ Submodule.span ℝ {v} := by
  simp only [mem_range, add_right_inj, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨ρ⁻¹ * s, by rw [mul_smul, hs, smul_smul, inv_mul_cancel₀ hρ, one_smul]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨ρ * a, mul_smul _ _ _⟩

/-- A set that coincides near `x` with the line through `x` in direction `v` has that line
as approximate tangent space at `x`. -/
theorem Submission.odc_approxTangent_of_locally_line {P : ℕ} (M : Set (Euclid P))
    (hM : MeasurableSet M) (x v : Euclid P) (hv : v ≠ 0) (r : ℝ) (hr : 0 < r)
    (hloc : M ∩ ball x r = range (fun s : ℝ => x + s • v) ∩ ball x r) :
    HasApproximateTangentSpaceAt 1 M x (Submodule.span ℝ {v}) := by
  refine ⟨finrank_span_singleton hv, fun f => ?_⟩
  obtain ⟨R, hR0, hR⟩ :=
    f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 (0 : Euclid P)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr hR0)] with ρ ⟨hρ0, hρ⟩
  rw [lt_div_iff₀ hR0] at hρ
  -- for small `ρ`, the blow-up and the line agree on `closedBall 0 R ⊇ spt f`
  rw [Submission.odc_tangent_blowUp_image_eq M x hρ0.ne',
    ← integral_indicator (hM.preimage (by fun_prop)),
    ← integral_indicator (Submodule.closed_of_finiteDimensional _).measurableSet]
  congr 1
  ext y
  by_cases hy : y ∈ tsupport f
  · have hball : x + ρ • y ∈ ball x r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 (hR hy)) hρ0.le).trans_lt hρ
    have hiff : y ∈ (fun y => x + ρ • y) ⁻¹' M ↔ y ∈ Submodule.span ℝ {v} := by
      rw [mem_preimage, ← Submission.odc_tangent_mem_range_iff x v y hρ0.ne']
      simpa [hball] using Set.ext_iff.1 hloc (x + ρ • y)
    by_cases hyL : y ∈ Submodule.span ℝ {v}
    · rw [indicator_of_mem hyL, indicator_of_mem (hiff.2 hyL)]
    · rw [indicator_of_notMem hyL, indicator_of_notMem (mt hiff.1 hyL)]
  · have h0 : f y = 0 := image_eq_zero_of_notMem_tsupport hy
    rw [indicator_apply_eq_zero.2 fun _ => h0, indicator_apply_eq_zero.2 fun _ => h0]

/-- If near `x` the set `M` lies in the line through `x` in direction `v` up to an
`H¹`-null set, then any approximate tangent space of `M` at `x` is that line. -/
theorem Submission.odc_approxTangent_eq_of_subset {P : ℕ} (M N : Set (Euclid P))
    (x v : Euclid P) (hv : ‖v‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hN : (μHE[1] : Measure (Euclid P)) N = 0)
    (hloc : M ∩ ball x δ ⊆ range (fun s : ℝ => x + s • v) ∪ N)
    (Q : Submodule ℝ (Euclid P)) (hQ : HasApproximateTangentSpaceAt 1 M x Q) :
    Q = Submodule.span ℝ {v} := by
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hQ.1, finrank_span_singleton hv0])
  by_contra hQL
  -- a unit vector `u ∈ Q \ span {v}`; then `Q = ℝ u`
  obtain ⟨u, huQ, huL, hu⟩ : ∃ u ∈ Q, u ∉ Submodule.span ℝ {v} ∧ ‖u‖ = 1 := by
    obtain ⟨u, huQ, huL⟩ := IsConcreteLE.not_le_iff_exists.1 hQL
    have hu : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 fun h => huL (h ▸ Submodule.zero_mem _)
    refine ⟨‖u‖⁻¹ • u, Q.smul_mem _ huQ, fun h => huL ?_, ?_⟩
    · simpa [smul_smul, mul_inv_cancel₀ hu] using (Submodule.span ℝ {v}).smul_mem ‖u‖ h
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu]
  have hQu : (Q : Set (Euclid P)) = (fun t : ℝ => (0 : Euclid P) + t • u) '' univ := by
    have hspan : Submodule.span ℝ {u} = Q :=
      Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 huQ)
        (by rw [hQ.1, finrank_span_singleton (by rintro h; simp [h] at hu)])
    ext y
    rw [← hspan, image_univ, SetLike.mem_coe, Submodule.mem_span_singleton]
    simp only [mem_range, zero_add]
  -- `d = dist(u, span {v}) > 0` and the bump `f` of height `d / 2` at `u`
  set d := infDist u (Submodule.span ℝ {v} : Set (Euclid P))
  have hd : 0 < d := ((Submodule.closed_of_finiteDimensional _).notMem_iff_infDist_pos
    ⟨0, Submodule.zero_mem _⟩).1 huL
  obtain ⟨f, hf⟩ : ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∀ y, f y = max 0 (d / 2 - ‖y - u‖) :=
    ⟨⟨⟨fun y => max 0 (d / 2 - ‖y - u‖), by fun_prop⟩,
      HasCompactSupport.intro (isCompact_closedBall u (d / 2)) fun y hy => max_eq_left (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy; linarith)⟩, fun y => rfl⟩
  -- the limit `∫_Q f` is positive
  have hpos : 0 < ∫ y in (Q : Set (Euclid P)), f y ∂μHE[1] := by
    rw [hQu, Submission.odc_line_integral 0 u hu univ, Measure.restrict_univ]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (by fun_prop)
      (f.hasCompactSupport.comp_isClosedEmbedding
        (Submission.odc_line_isometry 0 u hu).isClosedEmbedding) (fun t => by simp [hf]) ?_
    rw [hf, zero_add, one_smul, sub_self, norm_zero, sub_zero]
    exact (lt_max_of_lt_right (half_pos hd)).ne'
  -- but the blown-up integrals eventually vanish: off a null set, `f = 0` on the blow-up
  have hzero : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x ρ '' M, f y ∂μHE[1] = 0 := by
    have h1d : (0 : ℝ) < 1 + d := by linarith
    filter_upwards [Ioo_mem_nhdsGT (div_pos hδ h1d)] with ρ ⟨hρ0, hρ⟩
    rw [lt_div_iff₀ h1d] at hρ
    refine setIntegral_eq_zero_of_ae_eq_zero (ae_iff.2 (measure_mono_null (fun y hy => ?_)
      (Submission.odc_tangent_blowUp_null hN x ρ)))
    simp only [mem_ofPred_eq, not_imp] at hy
    rw [Submission.odc_tangent_blowUp_image_eq _ x hρ0.ne'] at hy ⊢
    obtain ⟨hyM, hfy⟩ := hy
    have hyu : ‖y - u‖ < d / 2 := by
      by_contra h
      exact hfy (by rw [hf]; exact max_eq_left (by linarith [not_lt.1 h]))
    have hball : x + ρ • y ∈ ball x δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
      nlinarith [norm_sub_norm_le y u, norm_nonneg y]
    rcases hloc ⟨hyM, hball⟩ with hyl | hyN
    · have := infDist_le_dist_of_mem (x := u)
        ((Submission.odc_tangent_mem_range_iff x v y hρ0.ne').1 hyl)
      rw [dist_comm, dist_eq_norm] at this
      linarith
    · exact hyN
  exact hpos.ne' (tendsto_nhds_unique (hQ.2 f)
    (tendsto_const_nhds.congr' (hzero.mono fun ρ h => h.symm)))

/-- Test forms converging to `0` in `𝒟ⁿ(U)` converge to `0` uniformly on the whole space. -/
theorem Submission.odc_polycurrent_tendstoUniformly {P n : ℕ} {U : Set (Euclid P)}
    {ωs : ℕ → TestFormOn U n} (h : TestFormOnConverges ωs 0) :
    TendstoUniformly (fun j => (ωs j : DifferentialForm (Euclid P) n)) 0 atTop := by
  obtain ⟨K, -, -, hsupp, -, hderiv⟩ := h
  refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ K
  · simpa [iteratedFDeriv_zero_eq_comp] using hj x hx
  · simpa [image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')] using hε

/-- Integration of `1`-forms along `t ↦ p + t v`, `t ∈ I` (`‖v‖ = 1`), is a current. -/
theorem Submission.odc_polycurrent_line {P : ℕ} (p v : Euclid P) (I : Set ℝ) (hv : ‖v‖ = 1) :
    ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1,
      ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        X ω = ∫ t in I, (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => v) := by
  have hγ := Submission.odc_line_isometry p v hv
  have hint (ω : TestFormOn (univ : Set (Euclid P)) 1) :
      Integrable fun t : ℝ => (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => v) :=
    ((continuous_eval_const (F := Covector (Euclid P) 1) fun _ : Fin 1 => v).comp
      (ω.2.1.1.continuous.comp hγ.continuous)).integrable_of_hasCompactSupport
      ((ω.2.1.2.comp_isClosedEmbedding hγ.isClosedEmbedding).comp_left
        (g := fun α : Covector (Euclid P) 1 => α fun _ => v) rfl)
  refine ⟨⟨{ toFun := fun ω =>
               ∫ t in I, (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => v)
             map_add' := fun ω η => ?_
             map_smul' := fun c ω => ?_ }, fun ωs h => ?_⟩, fun ω => rfl⟩
  · simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
    exact integral_add (hint ω).restrict (hint η).restrict
  · simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    exact integral_const_mul c _
  · -- dominated convergence, with the indicator of the compact set `γ⁻¹ K` as dominating function
    have hu := Submission.odc_polycurrent_tendstoUniformly h
    obtain ⟨K, hK, -, hsupp, -, -⟩ := h
    have hS : IsCompact ((fun t : ℝ => p + t • v) ⁻¹' K) :=
      hγ.isClosedEmbedding.isCompact_preimage hK
    have key := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict I)
      (F := fun j t => (ωs j : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => v))
      (f := fun _ => 0) (((fun t : ℝ => p + t • v) ⁻¹' K).indicator fun _ => 1)
      (Eventually.of_forall fun j => (hint (ωs j)).aestronglyMeasurable.restrict) ?_
      ((integrableOn_const (C := (1 : ℝ)) hS.measure_lt_top.ne).integrable_indicator
        hS.isClosed.measurableSet).restrict
      (Eventually.of_forall fun t => by
        simpa [Function.comp_def] using ((continuous_eval_const (F := Covector (Euclid P) 1)
          fun _ : Fin 1 => v).tendsto 0).comp (hu.tendsto_at (p + t • v)))
    · simpa using key
    · filter_upwards [Metric.tendstoUniformly_iff.1 hu 1 one_pos] with j hj
      refine Eventually.of_forall fun t => ?_
      by_cases ht : p + t • v ∈ K
      · rw [indicator_of_mem (show t ∈ (fun t : ℝ => p + t • v) ⁻¹' K from ht)]
        calc _ ≤ ‖(ωs j : DifferentialForm (Euclid P) 1) (p + t • v)‖ * ∏ _i : Fin 1, ‖v‖ :=
              ContinuousAlternatingMap.le_opNorm _ _
          _ ≤ 1 := by simpa [hv] using (hj (p + t • v)).le
      · rw [indicator_of_notMem (show t ∉ (fun t : ℝ => p + t • v) ⁻¹' K from ht),
          image_eq_zero_of_notMem_tsupport fun h' => ht (hsupp j h')]
        simp

/-- Finitely many weighted oriented line pieces define a current. -/
theorem Submission.odc_polygonal_current {P : ℕ} {ι : Type} [Fintype ι] (p v : ι → Euclid P)
    (I : ι → Set ℝ) (c : ι → ℝ) (hv : ∀ k, ‖v k‖ = 1) :
    ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1,
      ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        X ω = ∑ k, c k * ∫ t in I k,
          (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k) := by
  choose X hX using fun k => Submission.odc_polycurrent_line (p k) (v k) (I k) (hv k)
  refine ⟨⟨∑ k, c k • (X k).toCurrent, fun ωs h => ?_⟩, fun ω => ?_⟩
  · simpa using tendsto_finsetSum Finset.univ fun k _ => ((X k).continuous' ωs h).const_mul (c k)
  · simp [← hX]

/-- A smooth compactly supported function is a test `0`-form whose exterior derivative is its
differential. -/
theorem Submission.odc_zero_testForm {P : ℕ} (f : Euclid P → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ φ : TestFormOn (univ : Set (Euclid P)) 0, ∀ x v : Euclid P,
      ((exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 φ :
          TestFormOn (univ : Set (Euclid P)) 1) : DifferentialForm (Euclid P) 1) x (fun _ => v) =
        fderiv ℝ f x v := by
  refine ⟨⟨fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (f x),
    ⟨(ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)).contDiff.comp hf,
      hfc.comp_left (map_zero (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ (Euclid P) ℝ (Fin 0)))⟩,
    subset_univ _⟩, fun x v => ?_⟩
  show extDeriv (fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (Euclid P) (Fin 0) (f x)) x
    (fun _ => v) = _
  rw [extDeriv_constOfIsEmpty]
  rfl

/-- On `ℝ⁰` every `1`-current vanishes: all `1`-covectors on the zero space are zero. -/
theorem Submission.odc_dim_zero_vanish (C : GeometricCurrentOn (univ : Set (Euclid 0)) 1) :
    ∀ ω : TestFormOn (univ : Set (Euclid 0)) 1, C ω = 0 := by
  intro ω
  have hω : ω = 0 := Subtype.ext <| funext fun x => ContinuousAlternatingMap.ext fun m => by
    rw [Subsingleton.elim m 0]
    simp
  rw [hω]
  exact map_zero C.toCurrent

/-- `λ M_W(C) ≤ M_{λW}(C)` for a `1`-dimensional cone `C`: if `ω` is admissible for `W`, the
dilated form `y ↦ ω(λ⁻¹y) = λ ω'(y)` is admissible for `λW` and `C(λω') = λ C(ω)`. -/
theorem Submission.odc_conemass_le_massOn_smul {P : ℕ}
    (C : GeometricCurrentOn (univ : Set (Euclid P)) 1) (hC : IsConeCurrent C) (lam : ℝ)
    (hlam : 0 < lam) (W : Set (Euclid P)) :
    ENNReal.ofReal lam * C.massOn W ≤ C.massOn ((fun x => lam • x) '' W) := by
  rw [GeometricCurrentOn.massOn, ENNReal.mul_sSup]
  refine iSup₂_le ?_
  rintro _ ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  obtain ⟨ω', hω', hC'⟩ := Submission.cone_current_apply_dilation_pullback P 1 C hC lam hlam ω
  have hη : ((lam • ω' : TestFormOn (univ : Set (Euclid P)) 1) : DifferentialForm (Euclid P) 1) =
      (ω : DifferentialForm (Euclid P) 1) ∘ fun y => lam⁻¹ • y := funext fun y => by
    rw [Submodule.coe_smul, Pi.smul_apply, hω', pow_one, smul_smul, mul_inv_cancel₀ hlam.ne',
      one_smul, comp_apply]
  have hadm : lam • ω' ∈ massAdmissibleOn univ 1 ((fun x => lam • x) '' W) := by
    refine ⟨?_, fun y => by rw [hη]; exact hω1 _⟩
    rw [hη]
    refine (tsupport_comp_subset_preimage _ (continuous_const_smul _)).trans fun y hy => ?_
    exact ⟨lam⁻¹ • y, hωW hy, by simp [smul_smul, mul_inv_cancel₀ hlam.ne']⟩
  calc ENNReal.ofReal lam * ENNReal.ofReal (C ω) = ENNReal.ofReal (C (lam • ω')) := by
        rw [map_smul, smul_eq_mul, ENNReal.ofReal_mul hlam.le, hC']
    _ ≤ _ := C.le_massOn hadm

/-- The local mass of a `1`-dimensional cone current is `1`-homogeneous. -/
theorem Submission.odc_cone_massOn_smul {P : ℕ} (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (hC : IsConeCurrent C) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)) :
    C.massOn ((fun x => lam • x) '' W) = ENNReal.ofReal lam * C.massOn W := by
  refine le_antisymm ?_ (Submission.odc_conemass_le_massOn_smul C hC lam hlam W)
  have h := Submission.odc_conemass_le_massOn_smul C hC lam⁻¹ (inv_pos.2 hlam)
    ((fun x => lam • x) '' W)
  simp only [image_image, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul, image_id'] at h
  calc C.massOn ((fun x => lam • x) '' W)
      = ENNReal.ofReal lam * (ENNReal.ofReal lam⁻¹ * C.massOn ((fun x => lam • x) '' W)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal lam * C.massOn W := by gcongr

/-- `ω₁ = 2`. -/
theorem Submission.odc_unitBallVolume_one : unitBallVolume 1 = 2 := by
  set e : Euclid 1 := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  have hx : ∀ x : Euclid 1, x = x 0 • e := fun x => by
    ext i
    rw [Subsingleton.elim i 0]
    simp [e]
  -- the unit ball of `ℝ¹` is the image of `(-1, 1)` under the isometry `t ↦ t e`
  have hball : ball (0 : Euclid 1) 1 = (fun t : ℝ => (0 : Euclid 1) + t • e) '' Ioo (-1) 1 := by
    ext x
    simp only [mem_ball_zero_iff, mem_image, mem_Ioo, zero_add]
    constructor
    · intro h
      refine ⟨x 0, ?_, (hx x).symm⟩
      rw [hx x, norm_smul, he, mul_one, Real.norm_eq_abs] at h
      exact abs_lt.1 h
    · rintro ⟨t, ht, rfl⟩
      rw [norm_smul, he, mul_one, Real.norm_eq_abs]
      exact abs_lt.2 ht
  rw [unitBallVolume, ← EuclideanSpace.euclideanHausdorffMeasure_eq_volume 1, hball,
    Submission.odc_line_measure_image 0 e he, Real.volume_Ioo]
  norm_num

/-- The mass measure of an integer multiplicity representation is finite on compact sets. -/
theorem Submission.odc_imrep_measure_compact_ne_top {P n : ℕ}
    (R : IMRep (univ : Set (Euclid P)) n) (K : Set (Euclid P)) (hK : IsCompact K) :
    R.measure K ≠ ∞ := by
  rw [IMRep.measure, withDensity_apply _ hK.isClosed.measurableSet,
    Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
  exact R.locallyIntegrable_mult K hK (subset_univ K)

/-- Lower mass bound at support points of a minimizing `1`-current without boundary in `ℝᴾ`,
from the monotonicity formula (density `≥ 1`) and `ω₁ = 2`. -/
theorem Submission.odc_density_lower {P : ℕ} (hP : 1 ≤ P)
    (C : GeometricCurrentOn (univ : Set (Euclid P)) 1) (hmin : IsMinimizingIn C univ)
    (hb : BoundaryVanishes C) (R : IMRep (univ : Set (Euclid P)) 1) (hR : R.Represents C)
    (x : Euclid P) (hx : ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0) :
    ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ENNReal.ofReal ρ ≤ R.measure (ball x ρ) := by
  have hN : IsEmbeddedSubmanifold 2 P (univ : Set (Euclid P)) := fun y _ =>
    ⟨univ, univ, id, isOpen_univ, isOpen_univ, mem_univ y, contDiffOn_id, injOn_id _,
      by simp, fun K _ hK => by simpa using hK, fun z _ => by
        rw [fderiv_id, ContinuousLinearMap.coe_id']; exact injective_id⟩
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, hge⟩ := Submission.dimred_minimizing_monotonicity P 1 P univ univ C
    le_rfl hP le_rfl isOpen_univ hN (by simp) (by rwa [inter_self]) (by simp) hb
  obtain ⟨hmass, hsupp, -⟩ := Submission.dimred_im_mass_measure P 1 univ C R isOpen_univ hR
  have hΘx := hΘ x (mem_univ x)
  -- the density at `x ∈ spt C` is `≥ 1 > 1/2`, so eventually `μ(B_ρ(x)) / (2ρ) > 1/2`
  have h1 : (2⁻¹ : ℝ≥0∞) < ENNReal.ofReal (Θ x) :=
    (ENNReal.inv_lt_one.2 ENNReal.one_lt_two).trans_le
      (ENNReal.one_le_ofReal.2 (hge x ((hsupp x (mem_univ x)).2 hx) _ hΘx))
  filter_upwards [hΘx.2.eventually_const_lt h1, self_mem_nhdsWithin] with ρ hρ hρ0
  rw [Submission.odc_unitBallVolume_one, pow_one, hmass _ isOpen_ball (subset_univ _),
    ENNReal.lt_div_iff_mul_lt (Or.inl (mul_ne_zero two_ne_zero (ENNReal.ofReal_pos.2 hρ0).ne'))
      (Or.inl (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)), ← mul_assoc,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul] at hρ
  exact hρ.le

/-- A set on which the mass measure vanishes meets the carrier in an `Hⁿ`-null set
(the multiplicity is `≥ 1` on the carrier). -/
theorem Submission.odc_carrier_inter_null {P n : ℕ} (R : IMRep (univ : Set (Euclid P)) n)
    (Z : Set (Euclid P)) (hZ : MeasurableSet Z) (h : R.measure Z = 0) :
    (μHE[n] : Measure (Euclid P)) (R.carrier ∩ Z) = 0 := by
  rw [IMRep.measure, withDensity_apply _ hZ] at h
  rw [inter_comm, ← Measure.restrict_apply hZ, ← setLIntegral_one, ← nonpos_iff_eq_zero, ← h]
  refine lintegral_mono_ae (ae_restrict_of_ae ((ae_restrict_mem R.measurableSet_carrier).mono
    fun x hx => ?_))
  exact_mod_cast R.mult_pos x hx

/-- Orientation of a `1`-dimensional representation carried by finitely many rays: on
`ray(e)` the orientation is `±e` almost everywhere. -/
theorem Submission.odc_orient_on_ray {P : ℕ} (R : IMRep (univ : Set (Euclid P)) 1)
    (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1)
    (hnull : (μHE[1] : Measure (Euclid P))
      (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0)
    (e : Euclid P) (he : e ∈ F) :
    ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict
        (R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0)),
      R.orient x = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => e) ∨
      R.orient x = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => e) := by
  have hray : MeasurableSet ((fun t : ℝ => t • e) '' Ioi 0) := by
    have h := Submission.odc_line_measurableSet_image 0 e (hF e he)
      (measurableSet_Ioi (a := (0 : ℝ)))
    simp only [zero_add] at h
    exact h
  filter_upwards [ae_restrict_mem (R.measurableSet_carrier.inter hray),
    ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients] with x hx hxQ
  obtain ⟨hxC, t₀, ht₀ : 0 < t₀, hxe⟩ := hx
  obtain ⟨Q, hQ, hQo⟩ := hxQ
  simp only at hxe
  subst hxe
  -- the other closed rays form a closed set `K` not containing `t₀ • e`
  set K := ⋃ e' ∈ F.erase e, (fun s : ℝ => s • e') '' Ici 0
  have hK : IsClosed K := by
    refine isClosed_biUnion_finset fun e' he' => ?_
    have h := (Submission.odc_line_isometry 0 e'
      (hF e' (Finset.mem_of_mem_erase he'))).isClosedEmbedding.isClosedMap _
      (isClosed_Ici (a := (0 : ℝ)))
    simp only [zero_add] at h
    exact h
  have hxK : t₀ • e ∉ K := by
    intro hxK
    obtain ⟨e', he', s, hs : 0 ≤ s, hse⟩ := mem_iUnion₂.1 hxK
    obtain ⟨hne, he'F⟩ := Finset.mem_erase.1 he'
    simp only at hse
    have hst : s = t₀ := by
      simpa [norm_smul, hF e he, hF e' he'F, abs_of_nonneg hs, abs_of_pos ht₀]
        using congrArg norm hse
    subst hst
    exact hne (smul_right_injective _ ht₀.ne' hse)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl _ hxK
  -- near `t₀ • e` the carrier lies on the line `ℝ e` up to the null set `N`
  set N := R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ
  have hloc : R.carrier ∩ ball (t₀ • e) δ ⊆ range (fun s : ℝ => t₀ • e + s • e) ∪ N := by
    rintro y ⟨hyC, hyB⟩
    by_cases hy : y ∈ ⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0
    · left
      obtain ⟨e'', he'', t, ht : 0 < t, hte⟩ := mem_iUnion₂.1 hy
      simp only at hte
      subst hte
      obtain rfl : e'' = e := by
        by_contra hne
        exact hball hyB (mem_iUnion₂.2 ⟨e'', Finset.mem_erase.2 ⟨hne, he''⟩, t, ht.le, rfl⟩)
      exact ⟨t - t₀, by simp only [← add_smul, add_sub_cancel]⟩
    · exact Or.inr ⟨hyC, hy⟩
  obtain rfl := Submission.odc_approxTangent_eq_of_subset R.carrier N (t₀ • e) e (hF e he) δ hδ
    hnull hloc Q hQ
  -- `e` itself is a unit orientation of `span {e}`
  exact Submission.rsdic_unitOrientation_eq_or_eq_neg P 1 _ _ _
    ⟨fun _ : Fin 1 => e, ⟨fun _ => hF e he, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩,
      by rw [range_const], Or.inl fun α => rfl⟩ hQo

/-- A line piece `γ(I)` is countably `1`-rectifiable. -/
theorem Submission.odc_polyimrep_rectifiable {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1)
    (I : Set ℝ) : CountablyRectifiable 1 ((fun t : ℝ => p + t • v) '' I) := by
  refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_range
    ((Submission.odc_line_isometry p v hv).lipschitzWith.comp
      (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).lipschitzWith)).mono ?_
  rintro _ ⟨t, -, rfl⟩
  exact ⟨EuclideanSpace.single 0 t, by simp⟩

/-- `H¹(γ(I) ∩ A) = ℒ¹(I ∩ γ⁻¹(A))` for the isometric line `γ(t) = p + t v`. -/
theorem Submission.odc_polyimrep_measure_inter {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1)
    (I : Set ℝ) (A : Set (Euclid P)) :
    (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p + t • v) '' I) ∩ A) =
      volume (I ∩ (fun t : ℝ => p + t • v) ⁻¹' A) := by
  rw [← image_inter_preimage, Submission.odc_line_measure_image p v hv]

/-- A line piece has locally finite `H¹`-measure. -/
theorem Submission.odc_polyimrep_measure_inter_ne_top {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1)
    (I : Set ℝ) {K : Set (Euclid P)} (hK : IsCompact K) :
    (μHE[1] : Measure (Euclid P)) (((fun t : ℝ => p + t • v) '' I) ∩ K) ≠ ∞ := by
  have hK' := (Submission.odc_line_isometry p v hv).isClosedEmbedding.isCompact_preimage hK
  rw [Submission.odc_polyimrep_measure_inter p v hv]
  exact ne_top_of_le_ne_top hK'.measure_lt_top.ne (measure_mono inter_subset_right)

/-- Continuous compactly supported functions are `H¹`-integrable on line pieces. -/
theorem Submission.odc_polyimrep_integrableOn {P : ℕ} (p v : Euclid P) (hv : ‖v‖ = 1)
    (I : Set ℝ) {g : Euclid P → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    IntegrableOn g ((fun t : ℝ => p + t • v) '' I) μHE[1] := by
  have hγ := Submission.odc_line_isometry p v hv
  rw [IntegrableOn, Submission.odc_line_restrict p v hv I,
    (Submission.odc_line_measurableEmbedding p v hv).integrable_map_iff]
  exact ((hg.comp hγ.continuous).integrable_of_hasCompactSupport
    (hgc.comp_isClosedEmbedding hγ.isClosedEmbedding)).integrableOn

/-- `±v` (as the `1`-vector `α ↦ ±α(v)`) is a unit orientation of `span {v}`. -/
theorem Submission.odc_polyimrep_unitOrientation {P : ℕ} (v : Euclid P) (hv : ‖v‖ = 1)
    {a : ℝ} (ha : a ≠ 0) :
    IsUnitOrientationOf
      ((a / |a|) • ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v))
      (Submodule.span ℝ {v}) := by
  refine ⟨fun _ => v, ⟨fun _ => hv, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩,
    by rw [range_const], ?_⟩
  rcases ha.lt_or_gt with h | h
  · exact Or.inr fun α => by simp [abs_of_neg h, div_neg, div_self ha]
  · exact Or.inl fun α => by simp [abs_of_pos h, div_self ha]

/-- `t ∑ₖ (aₖ / t) bₖ = ∑ₖ aₖ bₖ` provided all `aₖ` vanish when `t = 0`. -/
theorem Submission.odc_polyimrep_mul_sum_div {ι : Type} [Fintype ι] (t : ℝ) (a b : ι → ℝ)
    (h : t = 0 → ∀ k, a k = 0) : t * ∑ k, a k / t * b k = ∑ k, a k * b k := by
  rcases eq_or_ne t 0 with ht | ht
  · simp [ht, h ht]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by field_simp

/-- `∫_B ∑ₖ nₖ 𝟙_{Sₖ} dμ = ∑ₖ nₖ μ(Sₖ ∩ B)`. -/
theorem Submission.odc_polyimrep_lintegral_sum {E : Type*} [MeasurableSpace E] {ι : Type}
    [Fintype ι] (μ : Measure E) (S : ι → Set E) (hS : ∀ k, MeasurableSet (S k)) (n : ι → ℕ)
    (B : Set E) :
    ∫⁻ x in B, ((∑ k, (S k).indicator (fun _ => n k) x : ℕ) : ℝ≥0∞) ∂μ =
      ∑ k, (n k : ℝ≥0∞) * μ (S k ∩ B) := by
  have h : ∀ x, ((∑ k, (S k).indicator (fun _ => n k) x : ℕ) : ℝ≥0∞) =
      ∑ k, (S k).indicator (fun _ => (n k : ℝ≥0∞)) x := fun x => by
    push_cast
    exact Finset.sum_congr rfl fun k _ => by by_cases hx : x ∈ S k <;> simp [hx]
  simp_rw [h]
  rw [lintegral_finsetSum _ fun k _ => measurable_const.indicator (hS k)]
  exact Finset.sum_congr rfl fun k _ => by
    rw [lintegral_indicator_const (hS k), Measure.restrict_apply (hS k)]

/-- `∫_M ∑ₖ cₖ 𝟙_{Sₖ} gₖ dμ = ∑ₖ cₖ ∫_{Sₖ} gₖ dμ` when `Sₖ ⊆ M` for `cₖ ≠ 0`. -/
theorem Submission.odc_polyimrep_integral_sum {E : Type*} [MeasurableSpace E] {ι : Type}
    [Fintype ι] (μ : Measure E) (S : ι → Set E) (hS : ∀ k, MeasurableSet (S k)) (M : Set E)
    (c : ι → ℝ) (hSM : ∀ k, c k ≠ 0 → S k ⊆ M) (g : ι → E → ℝ)
    (hg : ∀ k, IntegrableOn (g k) (S k) μ) :
    ∫ x in M, ∑ k, (S k).indicator (fun _ => c k) x * g k x ∂μ =
      ∑ k, c k * ∫ x in S k, g k x ∂μ := by
  have h : ∀ k, (fun x => (S k).indicator (fun _ => c k) x * g k x) =
      (S k).indicator (fun x => c k * g k x) := fun k => funext fun x => by
    by_cases hx : x ∈ S k <;> simp [hx]
  rw [integral_finsetSum _ fun k _ => ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [h, integral_indicator (hS k), Measure.restrict_restrict (hS k), integral_const_mul]
    rcases eq_or_ne (c k) 0 with hc | hc
    · simp [hc]
    · rw [inter_eq_left.2 (hSM k hc)]
  · rw [h, integrable_indicator_iff (hS k), IntegrableOn, Measure.restrict_restrict (hS k)]
    exact IntegrableOn.mono_set ((hg k).const_mul (c k)) inter_subset_left

/-- At a point of the `k`-th piece away from the closures of the other pieces, a union of
pieces containing the `k`-th one has the line `span {vₖ}` as approximate tangent space. -/
theorem Submission.odc_polyimrep_tangent {P : ℕ} {ι : Type} [Finite ι] (p v : ι → Euclid P)
    (I : ι → Set ℝ) (hv : ∀ k, ‖v k‖ = 1) (hI : ∀ k, IsOpen (I k)) {M : Set (Euclid P)}
    (hM : MeasurableSet M) (hMS : M ⊆ ⋃ j, (fun t : ℝ => p j + t • v j) '' I j) {k : ι}
    (hkM : (fun t : ℝ => p k + t • v k) '' I k ⊆ M) {x : Euclid P}
    (hx : x ∈ (fun t : ℝ => p k + t • v k) '' I k)
    (hxj : ∀ j, j ≠ k → x ∉ closure ((fun t : ℝ => p j + t • v j) '' I j)) :
    HasApproximateTangentSpaceAt 1 M x (Submodule.span ℝ {v k}) := by
  obtain ⟨t₀, ht₀, rfl⟩ := hx
  obtain ⟨ε, hε, hεI⟩ := Metric.isOpen_iff.1 (hI k) t₀ ht₀
  have hev : ∀ᶠ y in 𝓝 (p k + t₀ • v k), ∀ j, j ≠ k →
      y ∉ (fun t : ℝ => p j + t • v j) '' I j := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hjk : j = k
    · exact Filter.Eventually.of_forall fun _ h => absurd hjk h
    · exact (Filter.not_frequently.1 (mt mem_closure_iff_frequently.2 (hxj j hjk))).mono
        fun _ hy _ => hy
  obtain ⟨δ, hδ, hδS⟩ := Metric.eventually_nhds_iff.1 hev
  -- near `x`, `M` coincides with the `k`-th line
  refine Submission.odc_approxTangent_of_locally_line M hM _ (v k)
    (norm_ne_zero_iff.1 (by simp [hv k])) (min ε δ) (lt_min hε hδ) ?_
  ext y
  simp only [mem_inter_iff, mem_ball, mem_range]
  constructor
  · rintro ⟨hyM, hy⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hMS hyM)
    obtain rfl : j = k := by
      by_contra hjk
      exact hδS (hy.trans_le (min_le_right _ _)) j hjk hj
    obtain ⟨t, -, rfl⟩ := hj
    exact ⟨⟨t - t₀, by simp only; rw [sub_smul]; abel⟩, hy⟩
  · rintro ⟨⟨s, rfl⟩, hy⟩
    refine ⟨hkM ⟨t₀ + s, hεI ?_, by simp only; rw [add_smul, add_assoc]⟩, hy⟩
    have h1 : dist (p k + t₀ • v k + s • v k) (p k + t₀ • v k) = |s| := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv k, mul_one, Real.norm_eq_abs]
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left, ← h1]
    exact hy.trans_le (min_le_left _ _)

/-- An open ray from the origin misses the closure of any other unit ray. -/
theorem Submission.odc_polyimrep_ray_inter_closure {P : ℕ} {e e' : Euclid P} (he : ‖e‖ = 1)
    (he' : ‖e'‖ = 1) (hne : e ≠ e') :
    ((fun t : ℝ => (0 : Euclid P) + t • e) '' Ioi 0) ∩
      closure ((fun t : ℝ => (0 : Euclid P) + t • e') '' Ioi 0) = ∅ := by
  have hcl : closure ((fun t : ℝ => (0 : Euclid P) + t • e') '' Ioi 0) ⊆
      (fun t : ℝ => (0 : Euclid P) + t • e') '' Ici 0 :=
    closure_minimal (image_mono Ioi_subset_Ici_self)
      ((Submission.odc_line_isometry 0 e' he').isClosedEmbedding.isClosedMap _ isClosed_Ici)
  refine eq_empty_iff_forall_notMem.2 fun x ⟨⟨t, ht, hx⟩, hx'⟩ => ?_
  obtain ⟨s, hs, rfl⟩ := hcl hx'
  simp only [zero_add] at hx
  have hts : t = s := by
    have h := congrArg norm hx
    rwa [norm_smul, norm_smul, he, he', mul_one, mul_one, Real.norm_of_nonneg (le_of_lt ht),
      Real.norm_of_nonneg hs] at h
  subst hts
  exact hne (smul_right_injective _ (ne_of_gt ht) hx)

/-- Finitely many weighted oriented open line pieces with `H¹`-null mutual overlaps form an
integer multiplicity representation. -/
theorem Submission.odc_polygonal_imrep {P : ℕ} {ι : Type} [Fintype ι] (p v : ι → Euclid P)
    (I : ι → Set ℝ) (c : ι → ℤ) (hv : ∀ k, ‖v k‖ = 1) (hI : ∀ k, IsOpen (I k))
    (hdisj : ∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P))
      (((fun t : ℝ => p j + t • v j) '' I j) ∩
        closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0) :
    ∃ R : IMRep (univ : Set (Euclid P)) 1,
      (∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        R.action (ω : DifferentialForm (Euclid P) 1) =
          ∑ k, (c k : ℝ) * ∫ t in I k,
            (ω : DifferentialForm (Euclid P) 1) (p k + t • v k) (fun _ => v k)) ∧
      ∀ A : Set (Euclid P), MeasurableSet A →
        R.measure A = ∑ k, ENNReal.ofReal |(c k : ℝ)| *
          volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' A) := by
  -- the pieces `Sₖ = γₖ(Iₖ)`, the carrier `M`, the multiplicity `θ` and the orientation `ξ`
  obtain ⟨S, hSdef⟩ : ∃ S : ι → Set (Euclid P),
      ∀ k, S k = (fun t : ℝ => p k + t • v k) '' I k := ⟨_, fun _ => rfl⟩
  have hS : ∀ k, MeasurableSet (S k) := fun k => by
    rw [hSdef]
    exact Submission.odc_line_measurableSet_image _ _ (hv k) (hI k).measurableSet
  obtain ⟨M, hMdef⟩ : ∃ M : Set (Euclid P), M = ⋃ k, ⋃ (_ : c k ≠ 0), S k := ⟨_, rfl⟩
  have hmemM : ∀ x, x ∈ M ↔ ∃ k, c k ≠ 0 ∧ x ∈ S k := fun x => by simp [hMdef]
  have hM : MeasurableSet M :=
    hMdef ▸ MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hS k
  have hSM : ∀ k, c k ≠ 0 → S k ⊆ M := fun k hk x hx => (hmemM x).2 ⟨k, hk, hx⟩
  obtain ⟨θ, hθdef⟩ : ∃ θ : Euclid P → ℕ,
      θ = fun x => ∑ k, (S k).indicator (fun _ => (c k).natAbs) x := ⟨_, rfl⟩
  have hθmeas : Measurable θ :=
    hθdef ▸ Finset.measurable_sum _ fun k _ => measurable_const.indicator (hS k)
  have hθlint : ∀ B, ∫⁻ x in B, (θ x : ℝ≥0∞) ∂μHE[1] =
      ∑ k, ((c k).natAbs : ℝ≥0∞) * μHE[1] (S k ∩ B) := fun B => by
    rw [hθdef]
    exact Submission.odc_polyimrep_lintegral_sum _ S hS _ B
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Euclid P → MultiVector P 1, ξ = fun x =>
      ∑ k, ((S k).indicator (fun _ => (c k : ℝ)) x / θ x) •
        ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := ⟨_, rfl⟩
  have hθξ : ∀ x (α : Covector (Euclid P) 1), (θ x : ℝ) * ξ x α =
      ∑ k, (S k).indicator (fun _ => (c k : ℝ)) x * α (fun _ => v k) := by
    intro x α
    have h0 : (θ x : ℝ) = 0 → ∀ k, (S k).indicator (fun _ => (c k : ℝ)) x = 0 := by
      intro h k
      rw [Nat.cast_eq_zero, hθdef] at h
      have hk := Finset.sum_eq_zero_iff.1 h k (Finset.mem_univ k)
      rw [indicator_apply_eq_zero] at hk ⊢
      exact fun hx => by simp [Int.natAbs_eq_zero.1 (hk hx)]
    rw [hξdef]
    simp only [sum_apply, smul_apply, smul_eq_mul, ContinuousAlternatingMap.apply_apply]
    exact Submission.odc_polyimrep_mul_sum_div _ _ _ h0
  have hξmeas : StronglyMeasurable ξ := by
    -- instance search does not find `ContinuousAdd` for this space of continuous linear maps
    have : ContinuousAdd (MultiVector P 1) :=
      (inferInstance : IsTopologicalAddGroup (MultiVector P 1)).toContinuousAdd
    rw [hξdef]
    exact Finset.stronglyMeasurable_fun_sum _ fun k _ =>
      (((measurable_const.indicator (hS k)).div
        (measurable_from_nat.comp hθmeas)).stronglyMeasurable).smul_const _
  let R : IMRep (univ : Set (Euclid P)) 1 :=
    { carrier := M
      mult := θ
      orient := ξ
      measurableSet_carrier := hM
      carrier_subset := subset_univ M
      rectifiable := by
        refine (Poincare.SimonGMT.Chapter03.countablyRectifiable_sUnion (countable_range S)
          (forall_mem_range.2 fun k => ?_)).mono ?_
        · rw [hSdef]
          exact Submission.odc_polyimrep_rectifiable _ _ (hv k) _
        · intro x hx
          obtain ⟨k, -, hxk⟩ := (hmemM x).1 hx
          exact ⟨S k, mem_range_self k, hxk⟩
      measurable_mult := hθmeas
      mult_pos := fun x hx => by
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hx
        rw [hθdef]
        refine (Int.natAbs_pos.2 hk).trans_le ?_
        calc (c k).natAbs = (S k).indicator (fun _ => (c k).natAbs) x :=
              (indicator_of_mem hxk fun _ => (c k).natAbs).symm
          _ ≤ _ := Finset.single_le_sum (f := fun j => (S j).indicator (fun _ => (c j).natAbs) x)
              (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
      locallyIntegrable_mult := fun K hK _ => by
        rw [hθlint]
        refine ENNReal.sum_ne_top.2 fun k _ => ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ?_
        refine ne_top_of_le_ne_top ?_ (measure_mono (inter_subset_inter_right _ inter_subset_right))
        rw [hSdef]
        exact Submission.odc_polyimrep_measure_inter_ne_top _ _ (hv k) _ hK
      aestronglyMeasurable_orient := hξmeas.aestronglyMeasurable
      orients := by
        -- off the null set of overlaps, `M` is locally a single oriented line
        have hB : (μHE[1] : Measure (Euclid P))
            (⋃ j, ⋃ k, ⋃ (_ : j ≠ k), S j ∩ closure (S k)) = 0 :=
          measure_iUnion_null fun j => measure_iUnion_null fun k => measure_iUnion_null fun h => by
            rw [hSdef, hSdef]
            exact hdisj j k h
        filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hB), ae_restrict_mem hM]
          with x hxB hxM
        obtain ⟨k, hk, hxk⟩ := (hmemM x).1 hxM
        have hxj : ∀ j, j ≠ k → x ∉ closure (S j) := fun j hjk h =>
          hxB (mem_iUnion.2 ⟨k, mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk.symm, hxk, h⟩⟩⟩)
        have hθx : θ x = (c k).natAbs := by
          rw [hθdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => indicator_of_notMem
              (fun h => hxj j hjk (subset_closure h)) _) (fun h => (h (Finset.mem_univ k)).elim),
            indicator_of_mem hxk]
        have hξx : ξ x = ((c k : ℝ) / |(c k : ℝ)|) •
            ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ : Fin 1 => v k) := by
          rw [hξdef]
          dsimp only
          rw [Finset.sum_eq_single k (fun j _ hjk => by
              rw [indicator_of_notMem (fun h => hxj j hjk (subset_closure h)), zero_div, zero_smul])
            (fun h => (h (Finset.mem_univ k)).elim), indicator_of_mem hxk, hθx, Nat.cast_natAbs,
            Int.cast_abs]
        refine ⟨Submodule.span ℝ {v k}, ?_, ?_⟩
        · have hMS : M ⊆ ⋃ j, (fun t : ℝ => p j + t • v j) '' I j := fun y hy => by
            obtain ⟨j, -, hyj⟩ := (hmemM y).1 hy
            exact mem_iUnion.2 ⟨j, by rwa [← hSdef]⟩
          refine Submission.odc_polyimrep_tangent p v I hv hI hM hMS
            (by rw [← hSdef]; exact hSM k hk) (by rw [← hSdef]; exact hxk) fun j hjk => ?_
          rw [← hSdef]
          exact hxj j hjk
        · rw [hξx]
          exact Submission.odc_polyimrep_unitOrientation (v k) (hv k) (Int.cast_ne_zero.2 hk) }
  refine ⟨R, fun ω => ?_, fun A hA => ?_⟩
  · obtain ⟨⟨hωs, hωc⟩, -⟩ := ω.2
    show ∫ x in M, (θ x : ℝ) * ξ x ((ω : DifferentialForm (Euclid P) 1) x) ∂μHE[1] = _
    simp_rw [hθξ]
    rw [Submission.odc_polyimrep_integral_sum _ S hS M _
      (fun k hk => hSM k (Int.cast_ne_zero.1 hk)) _ fun k => ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hSdef, Submission.odc_line_integral (p k) (v k) (hv k)]
    · rw [hSdef]
      exact Submission.odc_polyimrep_integrableOn _ _ (hv k) _
        ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun _ : Fin 1 => v k).continuous.comp
          (ContDiff.continuous hωs))
        (hωc.comp_left (g := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun _ : Fin 1 => v k)
          (map_zero _))
  · show ((μHE[1].restrict M).withDensity fun x => (θ x : ℝ≥0∞)) A = _
    rw [withDensity_apply _ hA, Measure.restrict_restrict hA, hθlint]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Int.cast_abs, ← Nat.cast_natAbs, ENNReal.ofReal_natCast]
    rcases eq_or_ne (c k) 0 with hk | hk
    · simp [hk]
    · rw [← inter_assoc, inter_eq_left.2 (inter_subset_left.trans (hSM k hk)), hSdef,
        Submission.odc_polyimrep_measure_inter _ _ (hv k)]

/-- A current given by integer multiplicities on finitely many rays is integer multiplicity,
with mass measure `∑ |m e| H¹⌞ray(e)`. -/
theorem Submission.odc_ray_current_imrep {P : ℕ}
    (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1) (m : Euclid P → ℤ)
    (hC : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
        (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) :
    ∃ R : IMRep (univ : Set (Euclid P)) 1, R.Represents C ∧
      ∀ A : Set (Euclid P), MeasurableSet A →
        R.measure A = ∑ e ∈ F, ENNReal.ofReal |(m e : ℝ)| *
          volume (Ioi (0 : ℝ) ∩ (fun t : ℝ => t • e) ⁻¹' A) := by
  obtain ⟨R, hact, hmeas⟩ := Submission.odc_polygonal_imrep (ι := F) (fun _ => 0)
    (fun e => (e : Euclid P)) (fun _ => Ioi 0) (fun e => m e) (fun e => hF e e.2)
    (fun _ => isOpen_Ioi) fun j k hjk => by
      rw [Submission.odc_polyimrep_ray_inter_closure (hF j j.2) (hF k k.2)
        fun h => hjk (Subtype.ext h)]
      exact measure_empty
  refine ⟨R, fun ω => ?_, fun A hA => ?_⟩
  · rw [hC ω, hact ω, ← Finset.sum_coe_sort F]
    simp only [zero_add]
  · rw [hmeas A hA, ← Finset.sum_coe_sort F]
    simp only [zero_add]

/-- Chain rule along a line: `d/ds f (s • e) = Df(s • e) e`. -/
theorem Submission.odc_constancy_deriv_ray {P : ℕ} {f : Euclid P → ℝ} (hf : Differentiable ℝ f)
    (e : Euclid P) (t : ℝ) : deriv (fun s : ℝ => f (s • e)) t = fderiv ℝ f (t • e) e := by
  have h := (hf (t • e)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id' t).smul_const e)
  rw [one_smul] at h
  exact h.deriv

/-- Testing a boundaryless current given by densities along rays against the differential of a
smooth compactly supported function. -/
theorem Submission.odc_constancy_exact {P : ℕ} (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (hC : C.boundary = 0) (F : Finset (Euclid P)) (G : Euclid P → ℝ → ℝ)
    (hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ),
        G e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e))
    {f : Euclid P → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) :
    ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), G e t * deriv (fun s : ℝ => f (s • e)) t = 0 := by
  obtain ⟨φ, hφ⟩ := Submission.odc_zero_testForm f hf hfc
  have h0 : C.boundary φ = 0 := by rw [hC]; rfl
  rw [GeometricCurrentOn.boundary_apply, hrep] at h0
  simp only [hφ] at h0
  simp only [Submission.odc_constancy_deriv_ray (hf.differentiable (by simp))]
  exact h0

/-- `∫₀^∞ (d/dt) f (t • e) dt = -f 0` for a smooth compactly supported `f` and a unit vector
`e`. -/
theorem Submission.odc_constancy_integral_deriv {P : ℕ} {f : Euclid P → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) {e : Euclid P}
    (he : ‖e‖ = 1) :
    ∫ t in Ioi (0 : ℝ), deriv (fun s : ℝ => f (s • e)) t = -f 0 := by
  have hiso : Isometry fun s : ℝ => s • e := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.dist_eq, Real.norm_eq_abs]
  have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun s : ℝ => f (s • e) :=
    hf.comp (contDiff_id.smul contDiff_const)
  have hhc : HasCompactSupport fun s : ℝ => f (s • e) :=
    hfc.comp_isClosedEmbedding hiso.isClosedEmbedding
  have h1 : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hh.continuous.continuousWithinAt
    (fun x _ => ((hh.differentiable (by simp)) x).hasDerivAt)
    ((hh.continuous_deriv h1).integrable_of_hasCompactSupport hhc.deriv).integrableOn
    (hhc.is_zero_at_infty.mono_left atTop_le_cocompact)]
  simp

/-- A smooth compactly supported function equal to `ψ` along the line `ℝ e₀` and vanishing on
the open rays `ℝ₊ e` of the other unit vectors `e ∈ F`. -/
theorem Submission.odc_constancy_cutoff {P : ℕ} (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1)
    {e₀ : Euclid P} (he₀ : ‖e₀‖ = 1) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioi 0) :
    ∃ f : Euclid P → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ HasCompactSupport f ∧
      (∀ s : ℝ, f (s • e₀) = ψ s) ∧ ∀ e ∈ F, e ≠ e₀ → ∀ t : ℝ, 0 < t → f (t • e) = 0 := by
  -- `α ≤ s ≤ β` on the support of `ψ`, with `0 < α`
  obtain ⟨α, hα, hαψ⟩ := hψc.isCompact.exists_forall_le' continuousOn_id fun b hb => hψs hb
  obtain ⟨β, hβψ⟩ := hψc.isCompact.bddAbove
  have hψαβ : ∀ s, ψ s ≠ 0 → α ≤ s ∧ s ≤ β := fun s hs =>
    ⟨hαψ s (subset_tsupport ψ hs), hβψ (subset_tsupport ψ hs)⟩
  -- the width `κ` of the cylinder around `ℝ e₀` misses the rays of the other `e ∈ F`
  obtain ⟨κ, hκ0, hκ⟩ : ∃ κ : ℝ, 0 < κ ∧ ∀ e ∈ F, inner ℝ e e₀ ^ 2 < 1 →
      κ < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := by
    have : ∀ᶠ κ in 𝓝[>] (0 : ℝ), 0 < κ ∧ ∀ e ∈ F, inner ℝ e e₀ ^ 2 < 1 →
        κ < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := by
      refine eventually_mem_nhdsWithin.and ((eventually_all_finset F).2 fun e _ => ?_)
      by_cases h : inner ℝ e e₀ ^ 2 < 1
      · have hpos : 0 < α ^ 2 * (1 - inner ℝ e e₀ ^ 2) := mul_pos (pow_pos hα 2) (sub_pos.2 h)
        exact (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpos)).mono
          fun κ hκ _ => hκ
      · exact Eventually.of_forall fun κ h' => absurd h' h
    exact this.exists
  obtain ⟨χ, hχ, hχ0, hχκ⟩ : ∃ χ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ χ 0 = 1 ∧
      ∀ s, κ ≤ s → χ s = 0 := by
    let b : ContDiffBump (0 : ℝ) := ⟨κ / 2, κ, half_pos hκ0, half_lt_self hκ0⟩
    refine ⟨b, b.contDiff, b.one_of_mem_closedBall (mem_closedBall_self (half_pos hκ0).le),
      fun s hs => b.zero_of_le_dist ?_⟩
    rw [Real.dist_eq, sub_zero]
    exact hs.trans (le_abs_self s)
  have hin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : Euclid P => inner ℝ x e₀ :=
    contDiff_id.inner ℝ contDiff_const
  refine ⟨fun x => ψ (inner ℝ x e₀) * χ (‖x‖ ^ 2 - inner ℝ x e₀ ^ 2),
    (hψ.comp hin).mul (hχ.comp ((contDiff_norm_sq ℝ).sub (hin.pow 2))), ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro (K := closedBall 0 (β ^ 2 + κ + 1)) (isCompact_closedBall _ _)
      fun x hx => ?_
    by_contra hne
    have hψx : ψ (inner ℝ x e₀) ≠ 0 := left_ne_zero_of_mul hne
    have hχx : χ (‖x‖ ^ 2 - inner ℝ x e₀ ^ 2) ≠ 0 := right_ne_zero_of_mul hne
    obtain ⟨h1, h2⟩ := hψαβ _ hψx
    have h3 : ‖x‖ ^ 2 - inner ℝ x e₀ ^ 2 < κ := not_le.1 fun h => hχx (hχκ _ h)
    have h4 : inner ℝ x e₀ ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ (hα.le.trans h1) h2 2
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    nlinarith [norm_nonneg x, sq_nonneg β]
  · intro s
    have h1 : inner ℝ (s • e₀) e₀ = s := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he₀, one_pow, mul_one]
    have h2 : ‖s • e₀‖ ^ 2 = s ^ 2 := by
      rw [norm_smul, he₀, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [h1, h2, sub_self, hχ0, mul_one]
  · intro e he hne t ht
    have he1 := hF e he
    have h1 : inner ℝ (t • e) e₀ = t * inner ℝ e e₀ := real_inner_smul_left _ _ _
    have h2 : ‖t • e‖ ^ 2 = t ^ 2 := by
      rw [norm_smul, he1, mul_one, Real.norm_eq_abs, sq_abs]
    simp only [h1, h2]
    by_cases hψt : ψ (t * inner ℝ e e₀) = 0
    · rw [hψt, zero_mul]
    · have hαt := (hψαβ _ hψt).1
      have hc0 : 0 < inner ℝ e e₀ := pos_of_mul_pos_right (hα.trans_le hαt) ht.le
      have hc1 : inner ℝ e e₀ < 1 := by
        have h := norm_sub_sq_real e e₀
        have hpos : 0 < ‖e - e₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
        rw [he1, he₀] at h
        nlinarith
      have hc2 : inner ℝ e e₀ ^ 2 < 1 := by nlinarith
      have hκ' := hκ e he hc2
      have htα : α ≤ t := by nlinarith
      have hα2 : α ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hα.le htα 2
      rw [hχκ _ (by nlinarith [mul_le_mul_of_nonneg_right hα2 (sub_pos.2 hc2).le]), mul_zero]

/-- Constancy along the rays: a `1`-cycle given by integer densities along finitely many rays
has constant integer multiplicities `m e` with `∑ m e = 0`. -/
theorem Submission.odc_ray_constancy {P : ℕ} (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (hC : C.boundary = 0) (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1)
    (g : Euclid P → ℝ → ℝ) (hg : ∀ e ∈ F, LocallyIntegrableOn (g e) (Ioi 0))
    (hgZ : ∀ e ∈ F, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g e t = k)
    (hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, ∫ t in Ioi (0 : ℝ),
        g e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) :
    ∃ m : Euclid P → ℤ, ∑ e ∈ F, m e = 0 ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
          (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  classical
  -- (1) the density is a.e. an integer constant along each ray
  have hconst : ∀ e₀ ∈ F, ∃ k : ℤ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g e₀ t = k := by
    intro e₀ he₀
    obtain ⟨c, hc⟩ := Submission.odc_du_bois_reymond (g e₀) (hg e₀ he₀) fun ψ hψ hψc hψs => by
      obtain ⟨f, hf, hfc, hfe₀, hf0⟩ :=
        Submission.odc_constancy_cutoff F hF (hF e₀ he₀) hψ hψc hψs
      have h := Submission.odc_constancy_exact C hC F g hrep hf hfc
      rw [Finset.sum_eq_single_of_mem e₀ he₀ fun e he hne =>
        setIntegral_eq_zero_of_forall_eq_zero fun t (ht : 0 < t) => by
          have : (fun s : ℝ => f (s • e)) =ᶠ[𝓝 t] fun _ => 0 :=
            eventually_of_mem (Ioi_mem_nhds ht) fun s hs => hf0 e he hne s hs
          rw [this.deriv_eq, deriv_const, mul_zero]] at h
      have hψ' : (fun s : ℝ => f (s • e₀)) = ψ := funext hfe₀
      rwa [hψ'] at h
    have : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot := ae_restrict_neBot.2 (by simp)
    obtain ⟨t, ht, k, hk⟩ := (hc.and (hgZ e₀ he₀)).exists
    exact ⟨k, hc.mono fun s hs => hs.trans (ht.symm.trans hk)⟩
  have hm : ∀ e, ∃ k : ℤ, e ∈ F → ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), g e t = k := by
    intro e
    by_cases he : e ∈ F
    · obtain ⟨k, hk⟩ := hconst e he
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose m hm using hm
  -- (2) the representation with the constant multiplicities
  have hrep' : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
        (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
    intro ω
    rw [hrep ω]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [← integral_const_mul]
    exact integral_congr_ae ((hm e he).mono fun t ht => by simp only [ht])
  refine ⟨m, ?_, hrep'⟩
  -- (3) Kirchhoff's law at the origin, tested against a bump function
  let b : ContDiffBump (0 : Euclid P) := ⟨1, 2, one_pos, one_lt_two⟩
  have hK : ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), (m e : ℝ) * deriv (fun s : ℝ => b (s • e)) t = 0 :=
    Submission.odc_constancy_exact C hC F (fun e _ => (m e : ℝ))
      (fun ω => by rw [hrep' ω]; simp only [integral_const_mul]) b.contDiff b.hasCompactSupport
  have hsum : ∑ e ∈ F, ∫ t in Ioi (0 : ℝ), (m e : ℝ) * deriv (fun s : ℝ => b (s • e)) t =
      -∑ e ∈ F, (m e : ℝ) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [integral_const_mul, Submission.odc_constancy_integral_deriv b.contDiff
      b.hasCompactSupport (hF e he), b.one_of_mem_closedBall (mem_closedBall_self zero_le_one),
      mul_neg_one]
  rw [hsum, neg_eq_zero] at hK
  exact_mod_cast hK

/-- The ray map `t ↦ t • e` of a unit vector is a measurable embedding. -/
theorem Submission.odc_rays_measurableEmbedding {P : ℕ} {e : Euclid P} (he : ‖e‖ = 1) :
    MeasurableEmbedding (fun t : ℝ => t • e) := by
  simpa only [zero_add] using Submission.odc_line_measurableEmbedding 0 e he

/-- `H¹⌞{t e : t ∈ I} = (t ↦ t e)_# (ℒ¹⌞I)` for a unit vector `e`. -/
theorem Submission.odc_rays_restrict {P : ℕ} {e : Euclid P} (he : ‖e‖ = 1) (I : Set ℝ) :
    (μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' I) =
      Measure.map (fun t : ℝ => t • e) (volume.restrict I) := by
  simpa only [zero_add] using Submission.odc_line_restrict 0 e he I

/-- Open rays spanned by distinct unit vectors are disjoint. -/
theorem Submission.odc_rays_disjoint {P : ℕ} {e e' : Euclid P} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (hne : e ≠ e') :
    Disjoint ((fun t : ℝ => t • e) '' Ioi 0) ((fun t : ℝ => t • e') '' Ioi 0) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t, ht, rfl⟩ ⟨s, hs, hst⟩
  have ht' : (0 : ℝ) < t := ht
  have hs' : (0 : ℝ) < s := hs
  dsimp only at hst
  -- comparing norms gives `s = t`, and then `e' = e`
  have hts : s = t := by
    simpa [norm_smul, he, he', abs_of_pos ht', abs_of_pos hs'] using congrArg norm hst
  subst hts
  exact hne (smul_right_injective (Euclid P) hs'.ne' hst).symm

/-- If `ξ = ±e` for a unit vector `e`, then `ξ(e♭) = ±1` and `ξ(α) = ξ(e♭) α(e)`, where
`e♭ = ⟪e, ·⟫`. -/
theorem Submission.odc_rays_orient {P : ℕ} {e : Euclid P} (he : ‖e‖ = 1) {ξ : MultiVector P 1}
    (hξ : ξ = ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => e) ∨
      ξ = -ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => e)) :
    (ξ (ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e)) = 1 ∨
      ξ (ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e)) = -1) ∧
    ∀ α : Covector (Euclid P) 1, ξ α =
      ξ (ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e)) *
        α (fun _ => e) := by
  have h1 : ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e)
      (fun _ => e) = 1 := by
    simp [he]
  rcases hξ with rfl | rfl <;> simp [h1]

/-- A unit orientation has norm `≤ 1`, so `‖ξ‖ ≤ 1` almost everywhere on the carrier. -/
theorem Submission.odc_rays_norm_orient_le {P n : ℕ} {U : Set (Euclid P)} (R : IMRep U n) :
    ∀ᵐ x ∂((μHE[n] : Measure (Euclid P)).restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
  filter_upwards [R.orients] with x hx
  obtain ⟨Q, -, hQ⟩ := hx
  exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2

/-- `θ ξ(Φ)` is integrable on the part of the carrier in a compact set, for bounded measurable
`Φ`. -/
theorem Submission.odc_rays_integrableOn {P n : ℕ} (R : IMRep (univ : Set (Euclid P)) n)
    {K : Set (Euclid P)} (hK : IsCompact K) {Φ : Euclid P → Covector (Euclid P) n}
    (hΦ : AEStronglyMeasurable Φ ((μHE[n] : Measure (Euclid P)).restrict R.carrier)) {C : ℝ}
    (hC : ∀ x, ‖Φ x‖ ≤ C) :
    IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x (Φ x)) (R.carrier ∩ K) μHE[n] := by
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- the dominating function `C θ` is integrable since `θ` is locally `H¹`-integrable
  have hint : IntegrableOn (fun x => C * (R.mult x : ℝ)) (R.carrier ∩ K) μHE[n] := by
    refine Integrable.const_mul ?_ C
    simpa using integrable_toReal_of_lintegral_ne_top
      (measurable_from_nat.comp R.measurable_mult).aemeasurable
      (R.locallyIntegrable_mult K hK (subset_univ K))
  refine hint.mono' (hθ.aestronglyMeasurable.mul ?_) ?_
  · exact (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      R.aestronglyMeasurable_orient hΦ).mono_measure
      (Measure.restrict_mono inter_subset_left le_rfl)
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left
      (Submission.odc_rays_norm_orient_le R)] with x hx
    rw [norm_mul, Real.norm_natCast, mul_comm C]
    gcongr
    calc ‖R.orient x (Φ x)‖ ≤ ‖R.orient x‖ * ‖Φ x‖ := (R.orient x).le_opNorm _
      _ ≤ 1 * C := mul_le_mul hx (hC x) (norm_nonneg _) zero_le_one
      _ = C := one_mul C

/-- `θ ξ(ω)` is integrable on the carrier for a test form `ω`. -/
theorem Submission.odc_rays_integrableOn_form {P n : ℕ} (R : IMRep (univ : Set (Euclid P)) n)
    (ω : TestFormOn (univ : Set (Euclid P)) n) :
    IntegrableOn (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
      R.carrier μHE[n] := by
  obtain ⟨⟨hsm, hcs⟩, -⟩ := ω.2
  have hcont : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsm
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcs
  refine (Submission.odc_rays_integrableOn R hcs.isCompact hcont.aestronglyMeasurable
    hC).of_forall_sdiff_eq_zero R.measurableSet_carrier ?_
  rintro x ⟨hxM, hx⟩
  rw [image_eq_zero_of_notMem_tsupport fun h => hx ⟨hxM, h⟩, map_zero, mul_zero]

/-- Along the ray map `t ↦ t • e`, the density `θ ξ(β)` (extended by `0` off the carrier) is
locally integrable. -/
theorem Submission.odc_rays_locallyIntegrable {P : ℕ} (R : IMRep (univ : Set (Euclid P)) 1)
    {e : Euclid P} (he : ‖e‖ = 1) (β : Covector (Euclid P) 1) :
    LocallyIntegrable (fun t : ℝ =>
      R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e)) := by
  refine locallyIntegrable_iff.2 fun k hk => ?_
  have h := Submission.odc_rays_integrableOn R (hk.image (f := fun t : ℝ => t • e) (by fun_prop))
    (Φ := fun _ => β) aestronglyMeasurable_const (fun _ => le_rfl)
  have h2 : Integrable (R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β))
      ((μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' k)) := by
    refine (integrable_indicator_iff R.measurableSet_carrier).2 ?_
    rw [IntegrableOn, Measure.restrict_restrict R.measurableSet_carrier]
    exact h
  rwa [Submission.odc_rays_restrict he k,
    (Submission.odc_rays_measurableEmbedding he).integrable_map_iff] at h2

/-- If `ξ(β) = ±1` a.e. on the carrier along the ray of `e`, the density `θ ξ(β)` is a.e.
integer valued along the ray. -/
theorem Submission.odc_rays_int {P : ℕ} (R : IMRep (univ : Set (Euclid P)) 1)
    {e : Euclid P} (he : ‖e‖ = 1) {β : Covector (Euclid P) 1}
    (hβ : ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' Ioi 0)),
      x ∈ R.carrier → R.orient x β = 1 ∨ R.orient x β = -1) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ,
      R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e) = k := by
  rw [Submission.odc_rays_restrict he, (Submission.odc_rays_measurableEmbedding he).ae_map_iff]
    at hβ
  filter_upwards [hβ] with t ht
  by_cases hM : t • e ∈ R.carrier
  · rw [indicator_of_mem hM]
    rcases ht hM with h | h
    · exact ⟨R.mult (t • e), by rw [h, mul_one]; norm_cast⟩
    · exact ⟨-(R.mult (t • e) : ℤ), by rw [h, mul_neg_one]; push_cast; ring⟩
  · exact ⟨0, by rw [indicator_of_notMem hM]; simp⟩

/-- If `ξ(α) = ξ(β) α(e)` a.e. on the carrier along the ray of `e`, the action on that part of
the carrier is an integral along the ray. -/
theorem Submission.odc_rays_integral {P : ℕ} (R : IMRep (univ : Set (Euclid P)) 1)
    {e : Euclid P} (he : ‖e‖ = 1) {β : Covector (Euclid P) 1}
    (hβ : ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict ((fun t : ℝ => t • e) '' Ioi 0)),
      x ∈ R.carrier → ∀ α : Covector (Euclid P) 1, R.orient x α = R.orient x β * α (fun _ => e))
    (ω : DifferentialForm (Euclid P) 1) :
    ∫ x in R.carrier ∩ (fun t : ℝ => t • e) '' Ioi 0, (R.mult x : ℝ) * R.orient x (ω x)
        ∂μHE[1] =
      ∫ t in Ioi (0 : ℝ),
        R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x β) (t • e) *
          ω (t • e) (fun _ => e) := by
  rw [← Measure.restrict_restrict R.measurableSet_carrier,
    ← integral_indicator R.measurableSet_carrier,
    integral_congr_ae (g := fun x => R.carrier.indicator
      (fun x => (R.mult x : ℝ) * R.orient x β) x * ω x (fun _ => e)) ?_,
    Submission.odc_rays_restrict he, (Submission.odc_rays_measurableEmbedding he).integral_map]
  filter_upwards [hβ] with x hx
  by_cases hM : x ∈ R.carrier
  · simp only [indicator_of_mem hM, hx hM (ω x), mul_assoc]
  · simp only [indicator_of_notMem hM, zero_mul]

/-- The action of a `1`-dimensional representation carried by finitely many rays, written with
integer densities `g e` along the rays. -/
theorem Submission.odc_action_rays {P : ℕ} (R : IMRep (univ : Set (Euclid P)) 1)
    (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1)
    (hnull : (μHE[1] : Measure (Euclid P))
      (R.carrier ∩ (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0)ᶜ) = 0) :
    ∃ g : Euclid P → ℝ → ℝ,
      (∀ e ∈ F, LocallyIntegrableOn (g e) (Ioi 0)) ∧
      (∀ e ∈ F, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∃ k : ℤ, g e t = k) ∧
      ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        R.action (ω : DifferentialForm (Euclid P) 1) =
          ∑ e ∈ F, ∫ t in Ioi (0 : ℝ),
            g e t * (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  have hM := R.measurableSet_carrier
  set β : Euclid P → Covector (Euclid P) 1 := fun e =>
    ContinuousAlternatingMap.ofSubsingleton ℝ (Euclid P) ℝ (0 : Fin 1) (innerSL ℝ e)
  -- on the ray of `e ∈ F`, `ξ = ±e` a.e. on the carrier
  have hor : ∀ e ∈ F, ∀ᵐ x ∂((μHE[1] : Measure (Euclid P)).restrict
      ((fun t : ℝ => t • e) '' Ioi 0)), x ∈ R.carrier →
      (R.orient x (β e) = 1 ∨ R.orient x (β e) = -1) ∧
        ∀ α : Covector (Euclid P) 1, R.orient x α = R.orient x (β e) * α (fun _ => e) := by
    intro e he
    have h := Submission.odc_orient_on_ray R F hF hnull e he
    rw [← Measure.restrict_restrict hM, ae_restrict_iff' hM] at h
    filter_upwards [h] with x hx hxM
    exact Submission.odc_rays_orient (hF e he) (hx hxM)
  refine ⟨fun e t => R.carrier.indicator (fun x => (R.mult x : ℝ) * R.orient x (β e)) (t • e),
    fun e he => (Submission.odc_rays_locallyIntegrable R (hF e he) _).locallyIntegrableOn _,
    fun e he => Submission.odc_rays_int R (hF e he) ((hor e he).mono fun x hx hxM => (hx hxM).1),
    fun ω => ?_⟩
  rw [← Finset.sum_congr rfl fun e he => Submission.odc_rays_integral R (hF e he)
    ((hor e he).mono fun x hx hxM => (hx hxM).2) ω]
  -- split the carrier into its parts on the disjoint rays, up to the null set off the rays
  rw [← integral_biUnion_finset F (fun e he => hM.inter
      ((Submission.odc_rays_measurableEmbedding (hF e he)).measurableSet_image.2 measurableSet_Ioi))
    ?_ fun e _ => (Submission.odc_rays_integrableOn_form R ω).mono_set inter_subset_left]
  · refine setIntegral_congr_set (ae_eq_set.2 ⟨measure_mono_null ?_ hnull, ?_⟩)
    · rintro x ⟨hxM, hx⟩
      refine ⟨hxM, fun hx' => hx ?_⟩
      simp only [mem_iUnion] at hx' ⊢
      obtain ⟨e, he, hxe⟩ := hx'
      exact ⟨e, he, hxM, hxe⟩
    · rw [sdiff_eq_empty.2 (iUnion₂_subset fun e _ => inter_subset_left), measure_empty]
  · intro e he e' he' hne
    exact (Submission.odc_rays_disjoint (hF e he) (hF e' he') hne).mono inter_subset_right
      inter_subset_right

/-- Along a unit-speed line, the value of a test `1`-form on a fixed vector is integrable. -/
theorem Submission.odc_antipodal_integrableOn {P : ℕ} (ω : TestFormOn (univ : Set (Euclid P)) 1)
    (p v w : Euclid P) (hv : ‖v‖ = 1) (s : Set ℝ) :
    IntegrableOn (fun t : ℝ => (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => w)) s := by
  have hω := ω.property.1
  have hγ := (Submission.odc_line_isometry p v hv).isClosedEmbedding
  have hcont : Continuous fun t : ℝ =>
      (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => w) :=
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => w)).continuous.comp
      (hω.1.continuous.comp hγ.continuous)
  have hsupp : HasCompactSupport fun t : ℝ =>
      (ω : DifferentialForm (Euclid P) 1) (p + t • v) (fun _ => w) :=
    (hω.2.comp_isClosedEmbedding hγ).comp_left
      (g := ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ (fun _ => w)) (map_zero _)
  exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn

/-- Splitting a ray integral at `t = 1`. -/
theorem Submission.odc_antipodal_integral_split {P : ℕ} (ω : TestFormOn (univ : Set (Euclid P)) 1)
    {e : Euclid P} (he : ‖e‖ = 1) :
    ∫ t in Ioi (0 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) =
      (∫ t in Ioo (0 : ℝ) 1, (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) +
        ∫ t in Ioi (1 : ℝ), (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
  have hint : ∀ s, IntegrableOn
      (fun t : ℝ => (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) s := by
    intro s
    simpa using Submission.odc_antipodal_integrableOn ω 0 e e he s
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hint _) (hint _),
    integral_Ioc_eq_integral_Ioo]

/-- Fundamental theorem of calculus for the exterior derivative of a test `0`-form along a
segment. -/
theorem Submission.odc_antipodal_ftc {P : ℕ} (φ : TestFormOn (univ : Set (Euclid P)) 0)
    (p w : Euclid P) {L : ℝ} (hL : 0 ≤ L) :
    ∫ t in Ioo (0 : ℝ) L, ((exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 φ :
        TestFormOn (univ : Set (Euclid P)) 1) : DifferentialForm (Euclid P) 1)
          (p + t • w) (fun _ => w) =
      (φ : DifferentialForm (Euclid P) 0) (p + L • w) ![] -
        (φ : DifferentialForm (Euclid P) 0) p ![] := by
  set f : Euclid P → ℝ := fun y => (φ : DifferentialForm (Euclid P) 0) y ![] with hf_def
  have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : DifferentialForm (Euclid P) 0) :=
    φ.property.1.1
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f :=
    (ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ ![]).contDiff.comp hφ
  have hd : ∀ y v : Euclid P, ((exteriorDerivativeTestOn (univ : Set (Euclid P)) 0 φ :
      TestFormOn (univ : Set (Euclid P)) 1) : DifferentialForm (Euclid P) 1) y (fun _ => v) =
        fderiv ℝ f y v := by
    intro y v
    change exteriorDerivative (φ : DifferentialForm (Euclid P) 0) y (fun _ => v) = _
    rw [exteriorDerivative_apply (hφ.differentiable (by simp)).differentiableAt,
      Fin.sum_univ_succ]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, Fin.val_zero, pow_zero, one_smul,
      hf_def]
    congr
    funext x
    exact congrArg _ (Subsingleton.elim _ _)
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t => f (p + t • w)) (fderiv ℝ f (p + t • w) w) t := by
    intro t
    have hγ : HasDerivAt (fun t : ℝ => p + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add p
    exact (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hγ
  have hcont : Continuous fun t : ℝ => fderiv ℝ f (p + t • w) w :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  simp_rw [hd]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable _ _)]
  simp [f]

/-- Subsingletons are `H¹`-null. -/
theorem Submission.odc_antipodal_null_of_subsingleton {P : ℕ} {w : Euclid P} (hw : ‖w‖ = 1)
    {s : Set (Euclid P)} (hs : s.Subsingleton) : (μHE[1] : Measure (Euclid P)) s = 0 := by
  rcases hs.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact measure_empty
  · have := Submission.odc_line_measure_image x w hw {0}
    rwa [image_singleton, zero_smul, add_zero, Real.volume_singleton] at this

/-- Two points `t e = s e'` of rays of unit vectors, with `t > 0`, coincide parametrically. -/
theorem Submission.odc_antipodal_ray_eq {P : ℕ} {e e' : Euclid P} (he : ‖e‖ = 1)
    (he' : ‖e'‖ = 1) {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) (h : t • e = s • e') :
    t = s ∧ e = e' := by
  have hts : t = s := by
    have := congrArg norm h
    rwa [norm_smul, norm_smul, he, he', mul_one, mul_one, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg hs] at this
  subst hts
  exact ⟨rfl, smul_right_injective _ ht.ne' h⟩

/-- Two unit vectors `a ≠ ±b` do not lie on a common line through `0`. -/
theorem Submission.odc_antipodal_not_collinear {P : ℕ} {a b e : Euclid P} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hab : a ≠ b) (hab' : b ≠ -a) (hae : a ∈ Submodule.span ℝ {e})
    (hbe : b ∈ Submodule.span ℝ {e}) : False := by
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hae
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hbe
  rw [norm_smul, Real.norm_eq_abs] at ha hb
  have he : ‖e‖ ≠ 0 := by
    rintro h
    rw [h, mul_zero] at ha
    exact zero_ne_one ha
  rcases abs_eq_abs.1 (mul_right_cancel₀ he (ha.trans hb.symm)) with h | h
  · exact hab (by rw [h])
  · exact hab' (by rw [h, neg_smul, neg_neg])

/-- The line through `b` and `a = b + ℓ u` meets every line through `0` at most once. -/
theorem Submission.odc_antipodal_line_meet {P : ℕ} {a b u e : Euclid P} {ℓ : ℝ}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) (hab' : b ≠ -a) (hbu : b + ℓ • u = a)
    {s₁ s₂ t₁ t₂ : ℝ} (h₁ : b + s₁ • u = t₁ • e) (h₂ : b + s₂ • u = t₂ • e) : s₁ = s₂ := by
  by_contra hs
  have he : ∀ r : ℝ, r • e ∈ Submodule.span ℝ {e} := fun r =>
    Submodule.smul_mem _ r (Submodule.mem_span_singleton_self e)
  have hu : u ∈ Submodule.span ℝ {e} := by
    have h : (s₁ - s₂) • u = (t₁ - t₂) • e := by
      rw [sub_smul, sub_smul, ← h₁, ← h₂]; abel
    exact (Submodule.smul_mem_iff _ (sub_ne_zero.2 hs)).1 (h ▸ he _)
  have hb' : b ∈ Submodule.span ℝ {e} := by
    have h : b = t₁ • e - s₁ • u := by rw [← h₁]; abel
    rw [h]
    exact sub_mem (he _) (Submodule.smul_mem _ _ hu)
  exact Submission.odc_antipodal_not_collinear ha hb hab hab'
    (hbu ▸ add_mem hb' (Submodule.smul_mem _ _ hu)) hb'

/-- Two pieces of rays from `0` of unit vectors, parametrized by `A ⊆ (0, ∞)` and `B ⊆ [0, ∞)`,
meet at most once, and not at all if the directions agree and `A`, `B` are disjoint. -/
theorem Submission.odc_antipodal_ray_inter {P : ℕ} {e e' : Euclid P} (he : ‖e‖ = 1)
    (he' : ‖e'‖ = 1) {A B : Set ℝ} (hA : A ⊆ Ioi 0) (hB : B ⊆ Ici 0)
    (h : e = e' → Disjoint A B) :
    ((fun t : ℝ => (0 : Euclid P) + t • e) '' A ∩
      (fun t : ℝ => (0 : Euclid P) + t • e') '' B).Subsingleton := by
  rintro _ ⟨⟨t, ht, rfl⟩, ⟨s, hs, hst⟩⟩
  simp only [zero_add] at hst
  obtain ⟨rfl, rfl⟩ := Submission.odc_antipodal_ray_eq he he' (hA ht) (hB hs) hst.symm
  exact (Set.disjoint_left.1 (h rfl) ht hs).elim

/-- The chord meets a line through `0` at most once. -/
theorem Submission.odc_antipodal_chord_inter {P : ℕ} {b u e : Euclid P}
    (hline : ∀ s₁ s₂ t₁ t₂ : ℝ, b + s₁ • u = t₁ • e → b + s₂ • u = t₂ • e → s₁ = s₂)
    (A B : Set ℝ) :
    ((fun s : ℝ => b + s • u) '' A ∩ (fun t : ℝ => (0 : Euclid P) + t • e) '' B).Subsingleton := by
  rintro _ ⟨⟨s₁, -, rfl⟩, ⟨t₁, -, h₁⟩⟩ _ ⟨⟨s₂, -, rfl⟩, ⟨t₂, -, h₂⟩⟩
  simp only [zero_add] at h₁ h₂
  obtain rfl := hline s₁ s₂ t₁ t₂ h₁.symm h₂.symm
  rfl

/-- `∑ |fᵢ| ℒ¹(x, y) = (∑ |fᵢ|)(y - x)`. -/
theorem Submission.odc_antipodal_sum_volume {α : Type*} (s : Finset α) (f : α → ℝ) (x y : ℝ) :
    ∑ i ∈ s, ENNReal.ofReal |f i| * volume (Ioo x y) =
      ENNReal.ofReal ((∑ i ∈ s, |f i|) * (y - x)) := by
  rw [Real.volume_Ioo, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg (f i),
    ← ENNReal.ofReal_mul (Finset.sum_nonneg fun i _ => abs_nonneg (f i))]

/-- Mass of a weighted ray current in `B₂(0)`. -/
theorem Submission.odc_antipodal_mass_rays {P : ℕ}
    (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1) (m : Euclid P → ℤ)
    (hC : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
        (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) :
    ENNReal.ofReal ((∑ e ∈ F, |(m e : ℝ)|) * 2) ≤ C.massOn (ball 0 2) := by
  obtain ⟨R, hR, hRm⟩ := Submission.odc_ray_current_imrep C F hF m hC
  rw [(Submission.dimred_im_mass_measure P 1 univ C R isOpen_univ hR).1 _ isOpen_ball
      (subset_univ _), hRm _ measurableSet_ball]
  calc ENNReal.ofReal ((∑ e ∈ F, |(m e : ℝ)|) * 2)
      = ∑ e ∈ F, ENNReal.ofReal |(m e : ℝ)| * volume (Ioo (0 : ℝ) 2) := by
        rw [Submission.odc_antipodal_sum_volume, sub_zero]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun e he => mul_le_mul_right (measure_mono ?_) _
        intro t ht
        refine ⟨ht.1, ?_⟩
        rw [mem_preimage, mem_ball, dist_zero_right, norm_smul, hF e he, mul_one,
          Real.norm_of_nonneg ht.1.le]
        exact ht.2

/-- The competitor: weighted outer rays `(1, ∞) e`, inner segments `(0, 1) e` (`e ∈ F`) and a chord
`b + s u`, `0 < s < ℓ`, form an integer multiplicity current whose mass in `B₂(0)` is at most
`∑ |mo e| + ∑ |mi e| + ℓ`. -/
theorem Submission.odc_antipodal_competitor {P : ℕ} (F : Finset (Euclid P))
    (hF : ∀ e ∈ F, ‖e‖ = 1) (mo mi : Euclid P → ℤ) (b u : Euclid P) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hu : ‖u‖ = 1)
    (hline : ∀ e : Euclid P, ∀ s₁ s₂ t₁ t₂ : ℝ,
      b + s₁ • u = t₁ • e → b + s₂ • u = t₂ • e → s₁ = s₂) :
    ∃ X : GeometricCurrentOn (univ : Set (Euclid P)) 1, IsIntegerMultiplicity X ∧
      (∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
        X ω = ∑ e ∈ F, (mo e : ℝ) * (∫ t in Ioi (1 : ℝ),
            (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) +
          ∑ e ∈ F, (mi e : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
            (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) +
          ∫ s in Ioo (0 : ℝ) ℓ, (ω : DifferentialForm (Euclid P) 1) (b + s • u) (fun _ => u)) ∧
      X.massOn (ball 0 2) ≤
        ENNReal.ofReal (∑ e ∈ F, |(mo e : ℝ)| + ∑ e ∈ F, |(mi e : ℝ)| + ℓ) := by
  classical
  set p : ↥F ⊕ ↥F ⊕ Unit → Euclid P :=
    Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => b) with hp
  set v : ↥F ⊕ ↥F ⊕ Unit → Euclid P :=
    Sum.elim (fun e => (e : Euclid P)) (Sum.elim (fun e => (e : Euclid P)) fun _ => u) with hv'
  set I : ↥F ⊕ ↥F ⊕ Unit → Set ℝ :=
    Sum.elim (fun _ => Ioi 1) (Sum.elim (fun _ => Ioo 0 1) fun _ => Ioo 0 ℓ) with hI
  set c : ↥F ⊕ ↥F ⊕ Unit → ℤ := Sum.elim (fun e => mo e) (Sum.elim (fun e => mi e) fun _ => 1)
    with hc
  have hv : ∀ k, ‖v k‖ = 1 := by
    rintro (e | e | _)
    exacts [hF e e.2, hF e e.2, hu]
  have hIo : ∀ k, IsOpen (I k) := by
    rintro (e | e | _)
    exacts [isOpen_Ioi, isOpen_Ioo, isOpen_Ioo]
  have hdisj : ∀ j k, j ≠ k → (μHE[1] : Measure (Euclid P))
      (((fun t : ℝ => p j + t • v j) '' I j) ∩
        closure ((fun t : ℝ => p k + t • v k) '' I k)) = 0 := by
    intro j k hjk
    rw [(Submission.odc_line_isometry (p k) (v k) (hv k)).isClosedEmbedding.closure_image_eq]
    apply Submission.odc_antipodal_null_of_subsingleton hu
    have hA₁ : Ioi (1 : ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
    have hA₂ : Ioo (0 : ℝ) 1 ⊆ Ioi 0 := Ioo_subset_Ioi_self
    have hB₁ : closure (Ioi (1 : ℝ)) ⊆ Ici 0 := by
      rw [closure_Ioi]; exact Ici_subset_Ici.2 zero_le_one
    have hB₂ : closure (Ioo (0 : ℝ) 1) ⊆ Ici 0 := by
      rw [closure_Ioo zero_ne_one]; exact Icc_subset_Ici_self
    have hd₁ : Disjoint (Ioi (1 : ℝ)) (closure (Ioo 0 1)) := by
      rw [closure_Ioo zero_ne_one]
      exact Set.disjoint_left.2 fun t ht ht' => absurd ht'.2 (not_le.2 ht)
    have hd₂ : Disjoint (Ioo (0 : ℝ) 1) (closure (Ioi 1)) := by
      rw [closure_Ioi]
      exact Set.disjoint_left.2 fun t ht ht' => absurd ht.2 (not_lt.2 ht')
    have hne : ∀ e e' : ↥F, (e : Euclid P) = e' → e = e' := fun e e' h => Subtype.ext h
    rcases j with e | e | _ <;> rcases k with e' | e' | _
    · exact Submission.odc_antipodal_ray_inter (hF e e.2) (hF e' e'.2) hA₁ hB₁
        fun h => absurd (congrArg Sum.inl (hne e e' h)) hjk
    · exact Submission.odc_antipodal_ray_inter (hF e e.2) (hF e' e'.2) hA₁ hB₂ fun _ => hd₁
    · rw [inter_comm]
      exact Submission.odc_antipodal_chord_inter (hline e) _ _
    · exact Submission.odc_antipodal_ray_inter (hF e e.2) (hF e' e'.2) hA₂ hB₁ fun _ => hd₂
    · exact Submission.odc_antipodal_ray_inter (hF e e.2) (hF e' e'.2) hA₂ hB₂
        fun h => absurd (congrArg (Sum.inr ∘ Sum.inl) (hne e e' h)) hjk
    · rw [inter_comm]
      exact Submission.odc_antipodal_chord_inter (hline e) _ _
    · exact Submission.odc_antipodal_chord_inter (hline e') _ _
    · exact Submission.odc_antipodal_chord_inter (hline e') _ _
    · exact absurd rfl hjk
  obtain ⟨X, hX⟩ := Submission.odc_polygonal_current p v I (fun k => (c k : ℝ)) hv
  obtain ⟨R, hRa, hRm⟩ := Submission.odc_polygonal_imrep p v I c hv hIo hdisj
  have hR : R.Represents X := fun ω => (hX ω).trans (hRa ω).symm
  refine ⟨X, ⟨R, hR⟩, fun ω => ?_, ?_⟩
  · rw [hX ω]
    simp only [Fintype.sum_sum_type, hp, hv', hI, hc, Sum.elim_inl, Sum.elim_inr, zero_add,
      Fintype.sum_unique, Int.cast_one, one_mul, add_assoc]
    rw [← Finset.sum_coe_sort F, ← Finset.sum_coe_sort F]
  · rw [(Submission.dimred_im_mass_measure P 1 univ X R isOpen_univ hR).1 _ isOpen_ball
        (subset_univ _), hRm _ measurableSet_ball]
    calc ∑ k, ENNReal.ofReal |(c k : ℝ)| *
          volume (I k ∩ (fun t : ℝ => p k + t • v k) ⁻¹' ball 0 2)
        ≤ ∑ k, ENNReal.ofReal |(c k : ℝ)| *
          volume ((Sum.elim (fun _ => Ioo (1 : ℝ) 2) (Sum.elim (fun _ => Ioo (0 : ℝ) 1)
            fun _ => Ioo (0 : ℝ) ℓ) : ↥F ⊕ ↥F ⊕ Unit → Set ℝ) k) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_right (measure_mono ?_) _
          rcases k with e | e | _
          · rintro t ⟨ht₁, ht₂⟩
            simp only [hp, hv', hI, Sum.elim_inl, mem_preimage, mem_ball, dist_zero_right,
              zero_add, norm_smul, hF e e.2, mul_one, Real.norm_eq_abs, mem_Ioi] at ht₁ ht₂
            exact ⟨ht₁, (le_abs_self t).trans_lt ht₂⟩
          · exact inter_subset_left
          · exact inter_subset_left
      _ = ∑ e ∈ F, ENNReal.ofReal |(mo e : ℝ)| * volume (Ioo (1 : ℝ) 2) +
            (∑ e ∈ F, ENNReal.ofReal |(mi e : ℝ)| * volume (Ioo (0 : ℝ) 1) +
              volume (Ioo (0 : ℝ) ℓ)) := by
          simp only [Fintype.sum_sum_type, hc, Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique,
            Int.cast_one, abs_one, ENNReal.ofReal_one, one_mul]
          rw [← Finset.sum_coe_sort F, ← Finset.sum_coe_sort F]
      _ = ENNReal.ofReal (∑ e ∈ F, |(mo e : ℝ)| + ∑ e ∈ F, |(mi e : ℝ)| + ℓ) := by
          have h₁ : 0 ≤ ∑ e ∈ F, |(mo e : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have h₂ : 0 ≤ ∑ e ∈ F, |(mi e : ℝ)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          rw [Submission.odc_antipodal_sum_volume, Submission.odc_antipodal_sum_volume,
            Real.volume_Ioo, ENNReal.ofReal_add (add_nonneg h₁ h₂) hℓ, ENNReal.ofReal_add h₁ h₂]
          norm_num [add_assoc]

/-- In a minimizing `1`-current made of weighted rays, every ray of positive multiplicity is
antipodal to every ray of negative multiplicity. -/
theorem Submission.odc_antipodal {P : ℕ} (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (hmin : IsMinimizingIn C univ) (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1)
    (m : Euclid P → ℤ)
    (hC : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
        (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e))
    (a b : Euclid P) (ha : a ∈ F) (hb : b ∈ F) (hma : 0 < m a) (hmb : m b < 0) :
    b = -a := by
  classical
  by_contra hne
  have ha₁ := hF a ha
  have hb₁ := hF b hb
  have hab : a ≠ b := by
    rintro rfl
    exact lt_asymm hma hmb
  -- the chord `s ↦ b + s u`, `0 ≤ s ≤ ℓ`, from `b` to `a`
  set ℓ : ℝ := ‖a - b‖ with hℓ_def
  have hℓ : 0 < ℓ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  set u : Euclid P := ℓ⁻¹ • (a - b) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hℓ.ne']
  have hbu : b + ℓ • u = a := by
    rw [hu_def, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul, add_sub_cancel]
  have hseg : ∀ s ∈ Icc (0 : ℝ) ℓ, ‖b + s • u‖ ≤ 1 := by
    intro s hs
    have h₀ : 0 ≤ s / ℓ := div_nonneg hs.1 hℓ.le
    have h₁ : s / ℓ ≤ 1 := (div_le_one hℓ).2 hs.2
    have h : b + s • u = (1 - s / ℓ) • b + (s / ℓ) • a := by
      rw [hu_def]
      module
    rw [h]
    calc ‖(1 - s / ℓ) • b + (s / ℓ) • a‖ ≤ ‖(1 - s / ℓ) • b‖ + ‖(s / ℓ) • a‖ := norm_add_le _ _
      _ = 1 := by
        rw [norm_smul, norm_smul, ha₁, hb₁, Real.norm_of_nonneg (by linarith),
          Real.norm_of_nonneg h₀]
        ring
  -- the competitor `X`: one unit of multiplicity of `[0, a]` and `[0, b]` moves to the chord
  set mi : Euclid P → ℤ := fun e => m e - (if e = a then 1 else 0) + (if e = b then 1 else 0)
    with hmi
  obtain ⟨X, hXIM, hXω, hXm⟩ := Submission.odc_antipodal_competitor F hF m mi b u hℓ.le hu
    fun e s₁ s₂ t₁ t₂ h₁ h₂ => Submission.odc_antipodal_line_meet ha₁ hb₁ hab hne hbu h₁ h₂
  -- `X - C = [[b, a]] - [[0, a]] + [[0, b]]`
  have hdiff : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, X ω - C ω =
      -(∫ t in Ioo (0 : ℝ) 1, (ω : DifferentialForm (Euclid P) 1) (t • a) (fun _ => a)) +
        (∫ t in Ioo (0 : ℝ) 1, (ω : DifferentialForm (Euclid P) 1) (t • b) (fun _ => b)) +
        ∫ s in Ioo (0 : ℝ) ℓ, (ω : DifferentialForm (Euclid P) 1) (b + s • u) (fun _ => u) := by
    intro ω
    have hsplit : C ω = ∑ e ∈ F, (m e : ℝ) * (∫ t in Ioo (0 : ℝ) 1,
          (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e)) +
        ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (1 : ℝ),
          (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) := by
      rw [hC ω, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun e he => by
        rw [Submission.odc_antipodal_integral_split ω (hF e he), mul_add]
    rw [hXω ω, hsplit]
    simp only [hmi, Int.cast_add, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
      add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_eq', ite_eq_left ha, ite_eq_left hb]
    ring
  -- `∂X = ∂C`
  have hbd : SameBoundary X C := by
    show X.boundary = C.boundary
    ext φ
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.boundary_apply, ← sub_eq_zero,
      hdiff]
    have h₁ := Submission.odc_antipodal_ftc φ 0 a zero_le_one
    have h₂ := Submission.odc_antipodal_ftc φ 0 b zero_le_one
    simp only [zero_add, one_smul] at h₁ h₂
    rw [h₁, h₂, Submission.odc_antipodal_ftc φ b u hℓ.le, hbu]
    ring
  -- `spt (X - C) ⊆ B̄₁(0)`
  have hvan : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      (∀ y : Euclid P, ‖y‖ ≤ 1 → (ω : DifferentialForm (Euclid P) 1) y = 0) →
        X ω - C ω = 0 := by
    intro ω hω
    have h₀ : ∀ w y : Euclid P, ‖y‖ ≤ 1 →
        (ω : DifferentialForm (Euclid P) 1) y (fun _ => w) = 0 :=
      fun w y hy => by rw [hω y hy, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
    have hray : ∀ e : Euclid P, ‖e‖ = 1 →
        ∫ t in Ioo (0 : ℝ) 1, (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e) = 0 :=
      fun e he => setIntegral_eq_zero_of_forall_eq_zero fun t ht => h₀ e _ (by
        rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht.1.le]
        exact ht.2.le)
    rw [hdiff ω, hray a ha₁, hray b hb₁, setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
      h₀ u _ (hseg s (Ioo_subset_Icc_self hs))]
    ring
  have hsupp : (X - C).support ⊆ closedBall 0 1 := by
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    by_contra hx₁
    rw [not_le] at hx₁
    refine hx.2 (mem_sUnion.2 ⟨ball x ((‖x‖ - 1) / 2), ?_, mem_ball_self (by linarith)⟩)
    refine ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _, fun ω hω =>
      hvan ω fun y hy => image_eq_zero_of_notMem_tsupport fun hy' => ?_⟩
    have h₁ := hω hy'
    rw [mem_ball, dist_eq_norm] at h₁
    have h₂ := norm_sub_norm_le x y
    rw [norm_sub_rev] at h₂
    linarith
  have hcpt : IsCompact (X - C).support := by
    refine (isCompact_closedBall 0 1).of_isClosed_subset ?_ hsupp
    rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff]
    exact (X - C).isOpen_zeroRegion.isClosed_compl
  -- minimality in `B₂(0)`: `2 ∑ |m e| ≤ ∑ |m e| + ∑ |mi e| + ℓ`
  have hle := hmin.2 (ball 0 2) X isOpen_ball ⟨isBounded_ball.isCompact_closure, subset_univ _⟩
    hXIM hbd hcpt
    (subset_inter (subset_univ _) (hsupp.trans (closedBall_subset_ball (by norm_num))))
  have key := (ENNReal.ofReal_le_ofReal_iff (add_nonneg (add_nonneg
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      hℓ.le)).1 ((Submission.odc_antipodal_mass_rays C F hF m hC).trans (hle.trans hXm))
  -- `∑ |mi e| = ∑ |m e| - 2`
  have hma' : (1 : ℝ) ≤ m a := by exact_mod_cast hma
  have hmb' : (m b : ℝ) ≤ -1 := by exact_mod_cast (show m b ≤ -1 by omega)
  have habs : ∀ e, |(mi e : ℝ)| =
      |(m e : ℝ)| - (if e = a then 1 else 0) - (if e = b then 1 else 0) := by
    intro e
    by_cases hea : e = a
    · rw [hea]
      simp only [hmi, ite_true, ite_eq_right hab]
      push_cast
      rw [abs_of_nonneg (by linarith), abs_of_pos (by linarith)]
      ring
    · by_cases heb : e = b
      · rw [heb]
        simp only [hmi, ite_true, ite_eq_right hab.symm]
        push_cast
        rw [abs_of_nonpos (by linarith), abs_of_neg (by linarith)]
        ring
      · simp only [hmi, ite_eq_right hea, ite_eq_right heb, sub_zero, add_zero]
  have hsum : ∑ e ∈ F, |(mi e : ℝ)| = ∑ e ∈ F, |(m e : ℝ)| - 2 := by
    rw [Finset.sum_congr rfl fun e _ => habs e, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ite_eq_left ha, ite_eq_left hb]
    ring
  rw [hsum] at key
  -- hence `‖a - b‖ ≥ 2`, and `b = -a` by the parallelogram law
  have hℓ₂ : 2 ≤ ℓ := by linarith
  have hpar := parallelogram_law_with_norm ℝ a b
  rw [ha₁, hb₁, ← hℓ_def] at hpar
  have h₀ : ‖a + b‖ ^ 2 ≤ 0 := by nlinarith
  exact hne (eq_neg_of_add_eq_zero_right
    (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 (le_antisymm h₀ (sq_nonneg _)))))

/-- A current vanishing on all test forms has zero local mass. -/
theorem Submission.odc_conclusion_massOn_eq_zero {P n : ℕ} {U : Set (Euclid P)}
    (C : GeometricCurrentOn U n) (h : ∀ ω : TestFormOn U n, C ω = 0) (W : Set (Euclid P)) :
    C.massOn W = 0 := by
  refine le_antisymm (sSup_le ?_) zero_le
  rintro _ ⟨ω, -, rfl⟩
  simp [h ω]

/-- The two half-lines of `ℝ` cut out of an interval centred at `±s` have total length `2ρ`. -/
theorem Submission.odc_conclusion_volume_halves (s ρ : ℝ) :
    volume (Ioi (0 : ℝ) ∩ ball s ρ) + volume (Ioi (0 : ℝ) ∩ ball (-s) ρ) =
      ENNReal.ofReal (2 * ρ) := by
  have h1 : Ioi (0 : ℝ) ∩ ball (-s) ρ = Neg.neg ⁻¹' (Iic 0 ∩ ball s ρ) \ {0} := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_ball, Real.dist_eq, Set.mem_sdiff, mem_preimage, mem_Iic,
      mem_singleton_iff]
    constructor
    · rintro ⟨ht, hts⟩
      refine ⟨⟨by linarith, ?_⟩, ht.ne'⟩
      rwa [show -t - s = -(t - -s) by ring, abs_neg]
    · rintro ⟨⟨ht, hts⟩, ht0⟩
      refine ⟨lt_of_le_of_ne (by linarith) (Ne.symm ht0), ?_⟩
      rwa [show -t - s = -(t - -s) by ring, abs_neg] at hts
  rw [h1, measure_sdiff_null (measure_singleton 0), Measure.measure_preimage_neg, inter_comm,
    inter_comm (Iic 0), ← compl_Ioi, ← Set.sdiff_eq, measure_inter_add_sdiff _ measurableSet_Ioi,
    Real.volume_ball]

/-- The zero current satisfies the conclusion with `e = 0`, `m = 0`. -/
theorem Submission.odc_zero_current_conclusion {P : ℕ}
    (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (h : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1, C ω = 0) :
    ∃ (e : Euclid P) (m : ℕ), (0 < m → ‖e‖ = 1) ∧
      C.support ⊆ (Submodule.span ℝ {e} : Set (Euclid P)) ∧
      ∀ y ∈ Submodule.span ℝ {e}, HasMassDensity C y m := by
  refine ⟨0, 0, fun h0 => absurd h0 (lt_irrefl 0), fun x hx => absurd ?_ hx.2,
    fun y _ => ⟨Nat.cast_nonneg _, ?_⟩⟩
  · exact mem_sUnion.2 ⟨ball x 1, ⟨isOpen_ball, isBounded_ball.isCompact_closure, subset_univ _,
      fun ω _ => h ω⟩, mem_ball_self one_pos⟩
  · simp only [Submission.odc_conclusion_massOn_eq_zero C h, ENNReal.zero_div, Nat.cast_zero,
      ENNReal.ofReal_zero]
    exact tendsto_const_nhds

/-- A multiplicity-`k` oriented line `k[[ℝa]] = k[[ray a]] - k[[ray(-a)]]` is supported in `ℝa` and
has density `k` at every point of `ℝa`. -/
theorem Submission.odc_line_conclusion {P : ℕ} (C : GeometricCurrentOn (univ : Set (Euclid P)) 1)
    (F : Finset (Euclid P)) (hF : ∀ e ∈ F, ‖e‖ = 1) (m : Euclid P → ℤ)
    (hC : ∀ ω : TestFormOn (univ : Set (Euclid P)) 1,
      C ω = ∑ e ∈ F, (m e : ℝ) * ∫ t in Ioi (0 : ℝ),
        (ω : DifferentialForm (Euclid P) 1) (t • e) (fun _ => e))
    (a : Euclid P) (ha : a ∈ F) (hna : -a ∈ F)
    (hsupp : ∀ e ∈ F, m e ≠ 0 → e = a ∨ e = -a) (k : ℕ) (hk : m a = k) (hk' : m (-a) = -k) :
    C.support ⊆ (Submodule.span ℝ {a} : Set (Euclid P)) ∧
      ∀ y ∈ Submodule.span ℝ {a}, HasMassDensity C y k := by
  obtain ⟨R, hR, hRm⟩ := Submission.odc_ray_current_imrep C F hF m hC
  obtain ⟨hmass, hspt, -⟩ := Submission.dimred_im_mass_measure P 1 univ C R isOpen_univ hR
  have ha1 : ‖a‖ = 1 := hF a ha
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_contra hxa
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
      (Submodule.closed_of_finiteDimensional (Submodule.span ℝ {a})).isOpen_compl x hxa
    refine (hspt x (mem_univ x)).1 hx ε hε ?_
    rw [hRm _ measurableSet_ball]
    refine Finset.sum_eq_zero fun e he => ?_
    by_cases hme : m e = 0
    · simp [hme]
    · have : (fun t : ℝ => t • e) ⁻¹' ball x ε = ∅ := by
        refine eq_empty_of_forall_notMem fun t ht => hball ht ?_
        rcases hsupp e he hme with rfl | rfl
        · exact Submodule.smul_mem _ t (Submodule.mem_span_singleton_self _)
        · exact Submodule.smul_mem _ t (Submodule.neg_mem _ (Submodule.mem_span_singleton_self _))
      simp [this]
  · obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hne : a ≠ -a := fun h => by
      have h2 : (2 : ℝ) • a = 0 := by rw [two_smul]; exact eq_neg_iff_add_eq_zero.1 h
      rcases smul_eq_zero.1 h2 with h2 | h2
      · norm_num at h2
      · simp [h2] at ha1
    have key : ∀ ρ : ℝ, C.massOn (ball (s • a) ρ) = k * ENNReal.ofReal (2 * ρ) := by
      intro ρ
      have h1 : (fun t : ℝ => t • a) ⁻¹' ball (s • a) ρ = ball s ρ := by
        ext t
        simp [dist_eq_norm, ← sub_smul, norm_smul, ha1]
      have h2 : (fun t : ℝ => t • -a) ⁻¹' ball (s • a) ρ = ball (-s) ρ := by
        ext t
        rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, smul_neg, ← neg_add', ← add_smul,
          norm_neg, norm_smul, ha1, mul_one, Real.dist_eq, sub_neg_eq_add, Real.norm_eq_abs]
      have hk1 : ENNReal.ofReal |((m a : ℤ) : ℝ)| = k := by simp [hk]
      have hk2 : ENNReal.ofReal |((m (-a) : ℤ) : ℝ)| = k := by simp [hk']
      rw [hmass _ isOpen_ball (subset_univ _), hRm _ measurableSet_ball,
        Finset.sum_eq_add_of_mem a (-a) ha hna hne, h1, h2, hk1, hk2, ← mul_add,
        Submission.odc_conclusion_volume_halves]
      intro c hc hca
      simp [show m c = 0 from by_contra fun hmc => (hsupp c hc hmc).elim hca.1 hca.2]
    refine ⟨Nat.cast_nonneg k, (tendsto_congr' ?_).2 tendsto_const_nhds⟩
    filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
    rw [key ρ, Submission.odc_unitBallVolume_one, pow_one, ENNReal.ofReal_mul zero_le_two,
      ENNReal.ofReal_ofNat, ENNReal.mul_div_cancel_right, ENNReal.ofReal_natCast]
    · simp [hρ]
    · simp [ENNReal.mul_eq_top]

/-- **Simon 7.3.3(2), formula (10)**: a `1`-dimensional minimizing cone `C` in `ℝᴾ` with
`∂C = 0` is `m[[ℝe]]` for a unit vector `e` (or `C = 0`, `m = 0`); in particular
`spt C ⊆ ℝe` and `Θ¹(μ_C, y) = m` for every `y ∈ ℝe`.
Steps: `μ_C` is `1`-homogeneous with density `≥ 1` on `spt C` (monotonicity), so it lives on
finitely many rays; constancy along the rays gives `C = ∑ mₑ[[ray e]]` with `∑ mₑ = 0`;
rerouting one unit of multiplicity of a positive and of a negative ray through the chord between
them shows by minimality that the two rays are antipodal. -/
theorem Submission.dimred_one_dim_minimizing_cone : ∀ (P : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) 1), IsMinimizingIn C univ → BoundaryVanishes C → IsConeCurrent C → ∃ (e : Euclid P) (m : ℕ), (0 < m → ‖e‖ = 1) ∧ C.support ⊆ (Submodule.span ℝ {e} : Set (Euclid P)) ∧ ∀ y ∈ Submodule.span ℝ {e}, HasMassDensity C y m := by
  intro P C hmin hbdry hcone
  -- `P = 0`: every `1`-current on `ℝ⁰` vanishes
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · exact Submission.odc_zero_current_conclusion C (Submission.odc_dim_zero_vanish C)
  -- the mass measure `μ = μ_C` of a representation `R` of `C`
  obtain ⟨R, hR⟩ := hmin.1
  have hmass := (Submission.dimred_im_mass_measure P 1 univ C R isOpen_univ hR).1
  -- `μ(λW) = λμ(W)` for open `W` (cone property)
  have hscale : ∀ lam : ℝ, 0 < lam → ∀ W : Set (Euclid P), IsOpen W →
      R.measure ((fun x => lam • x) '' W) = ENNReal.ofReal lam * R.measure W := by
    intro lam hlam W hW
    have hW' : IsOpen ((fun x => lam • x) '' W) := isOpenMap_smul₀ hlam.ne' W hW
    rw [← hmass _ hW' (subset_univ _), ← hmass W hW (subset_univ _)]
    exact Submission.odc_cone_massOn_smul C hcone lam hlam W
  -- `μ` lives on finitely many rays
  obtain ⟨F, hF, hZ⟩ := Submission.odc_finite_rays R.measure
    (Submission.odc_imrep_measure_compact_ne_top R) hscale
    (Submission.odc_density_lower hP C hmin hbdry R hR)
  have hrays : MeasurableSet (⋃ e ∈ F, (fun t : ℝ => t • e) '' Ioi 0) := by
    refine Finset.measurableSet_biUnion F fun e he => ?_
    simpa only [zero_add] using
      Submission.odc_line_measurableSet_image 0 e (hF e he) measurableSet_Ioi
  have hnull := Submission.odc_carrier_inter_null R _ hrays.compl hZ
  -- constant integer multiplicities `m e` along the rays, with `∑ m e = 0`
  obtain ⟨g, hgi, hgZ, hrep⟩ := Submission.odc_action_rays R F hF hnull
  obtain ⟨m, hsum, hCm⟩ := Submission.odc_ray_constancy C hbdry F hF g hgi hgZ
    fun ω => (hR ω).trans (hrep ω)
  by_cases hzero : ∀ e ∈ F, m e = 0
  · refine Submission.odc_zero_current_conclusion C fun ω => ?_
    rw [hCm ω]
    exact Finset.sum_eq_zero fun e he => by simp [hzero e he]
  simp only [not_forall] at hzero
  obtain ⟨e₀, he₀, hme₀⟩ := hzero
  -- there are rays of positive and of negative multiplicity
  have hpos : ∃ a ∈ F, 0 < m a := by
    by_contra! h
    have h₀ : 0 < -m e₀ := by have := h e₀ he₀; omega
    have : 0 < ∑ e ∈ F, -m e :=
      Finset.sum_pos' (fun e he => by have := h e he; omega) ⟨e₀, he₀, h₀⟩
    rw [Finset.sum_neg_distrib, hsum] at this
    exact lt_irrefl _ this
  have hneg : ∃ b ∈ F, m b < 0 := by
    by_contra! h
    have h₀ : 0 < m e₀ := by have := h e₀ he₀; omega
    have : 0 < ∑ e ∈ F, m e := Finset.sum_pos' h ⟨e₀, he₀, h₀⟩
    rw [hsum] at this
    exact lt_irrefl _ this
  obtain ⟨a, ha, hma⟩ := hpos
  obtain ⟨b, hb, hmb⟩ := hneg
  -- minimality: every positive ray is antipodal to every negative ray
  have hanti := Submission.odc_antipodal C hmin F hF m hCm
  obtain rfl : b = -a := hanti a b ha hb hma hmb
  have hsupp : ∀ e ∈ F, m e ≠ 0 → e = a ∨ e = -a := by
    intro e he hme
    rcases lt_or_gt_of_ne hme with h | h
    · exact Or.inr (hanti a e ha he hma h)
    · exact Or.inl (neg_injective (hanti e (-a) he hb h hmb)).symm
  -- `∑ m e = m a + m (-a)`, so `m (-a) = -m a`
  have ha0 : a ≠ -a := by
    intro h
    have : a = 0 := by
      have h2 : (2 : ℝ) • a = 0 := by rw [two_smul]; nth_rewrite 2 [h]; exact add_neg_cancel a
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    have h1 := hF a ha
    rw [this, norm_zero] at h1
    exact zero_ne_one h1
  have hsum2 : ∑ e ∈ F, m e = m a + m (-a) :=
    Finset.sum_eq_add a (-a) ha0
      (fun e he hne => by
        by_contra hme
        rcases hsupp e he hme with h | h
        · exact hne.1 h
        · exact hne.2 h)
      (fun h => absurd ha h) (fun h => absurd hb h)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, m a = k := ⟨(m a).toNat, (Int.toNat_of_nonneg hma.le).symm⟩
  have hk' : m (-a) = -k := by omega
  obtain ⟨hs, hd⟩ := Submission.odc_line_conclusion C F hF m hCm a ha hb hsupp k hk hk'
  exact ⟨a, k, fun _ => hF a ha, hs, hd⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
