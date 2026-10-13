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

/-- **`∫_Q g dHⁿ > 0` for a nonnegative `C_c` function `g` with `g(w) > 0` at a point `w` of an
`n`-plane `Q`** (step 4 of the proof that approximate tangent planes of a submanifold lie in its
tangent spaces; Simon Ch. 3, 1.4).  `Hⁿ⌞Q` is regular with support `Q` (SimonGMT Ch. 3), so `g` is
`Hⁿ⌞Q`-integrable and the open set `{g ≠ 0} ∋ w` has positive `Hⁿ⌞Q`-measure. -/
theorem Submission.dsmc_att_setIntegral_submodule_pos : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (g : Euclid P → ℝ) (w : Euclid P), Module.finrank ℝ Q = n → Continuous g → HasCompactSupport g → (∀ y, 0 ≤ g y) → w ∈ Q → 0 < g w → 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] := by
  intro P n Q g w hQ hg hgc hg0 hw hgw
  -- `Hⁿ⌞Q` is regular, hence finite on compact sets, so the `C_c` function `g` is integrable.
  have := Poincare.SimonGMT.Chapter03.regular_euclideanHausdorffMeasure_restrict_submodule hQ
  rw [integral_pos_iff_support_of_nonneg hg0 (hg.integrable_of_hasCompactSupport hgc)]
  -- `w ∈ Q = spt(Hⁿ⌞Q)` and `{g ≠ 0}` is an open neighbourhood of `w`.
  have hwμ : w ∈ ((μHE[n] : Measure (Euclid P)).restrict (Q : Set (Euclid P))).support := by
    rwa [Poincare.SimonGMT.Chapter03.support_euclideanHausdorffMeasure_restrict_submodule hQ]
  exact (Measure.mem_support_iff_forall _).1 hwμ _ (hg.isOpen_support.mem_nhds hgw.ne')
/-- Blow-up maps preserve `Hⁿ`-null sets: if `λ ≠ 0` and `Hⁿ(E) = 0`, then `Hⁿ(η_{x,λ}(E)) = 0`.
Since `η_{x,λ}(E) = λ⁻¹ · (E − x)`, the translation `y ↦ y − x` is an isometry (so
`Hⁿ(E − x) = Hⁿ(E) = 0`) and the dilation by `λ⁻¹ ≠ 0` multiplies `Hⁿ` by `|λ⁻¹|ⁿ`. -/
theorem Submission.dsmc_att_blowUpMap_image_null : ∀ (P n : ℕ) (E : Set (Euclid P)) (x : Euclid P) (lam : ℝ), lam ≠ 0 → μHE[n] E = 0 → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E) = 0 := by
  intro P n E x lam hlam hE
  -- Step 1: `η_{x,λ}(E) = λ⁻¹ · τ(E)`, where `τ y = y − x`
  have himage : Poincare.SimonGMT.Chapter03.blowUpMap x lam '' E =
      (fun z : Euclid P => lam⁻¹ • z) '' ((fun y : Euclid P => y - x) '' E) := by
    rw [Set.image_image]
    rfl
  -- Step 2: `τ` is an isometry, so `Hⁿ(τ(E)) = Hⁿ(E) = 0`
  have hτ : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
  have htrans : μHE[n] ((fun y : Euclid P => y - x) '' E) = 0 := by
    rw [hτ.euclideanHausdorffMeasure_image, hE]
  -- Steps 3–4: `Hⁿ(λ⁻¹ · τ(E)) = ‖λ⁻¹‖₊ⁿ • Hⁿ(τ(E)) = 0`
  rw [himage, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam), htrans,
    smul_zero]

/-- **Blow-ups of `M ∩ N` approach every vector of an approximate tangent space** (Simon Ch. 3,
Definition 1.4, chapter-03.txt lines 77–83, tested as in Remark 1.5(3), lines 90–92).  If
`Hⁿ(M \ N) = 0`, `Q` is an approximate tangent space of `M` at `x`, `w ∈ Q` and `s > 0`, then for
all small `λ > 0` some `y ∈ M ∩ N` has `|λ⁻¹(y − x) − w| < s`.  The tent `f = max(0, s − |· − w|)`
lies in `C_c`, vanishes off `B_s(w)` and has `∫_Q f dHⁿ > 0`, so `∫_{η_{x,λ}(M)} f dHⁿ > 0` for
small `λ`; hence `Hⁿ(η_{x,λ}(M) ∩ B_s(w)) ≠ 0`, and since `η_{x,λ}(M \ N)` is `Hⁿ`-null,
`η_{x,λ}(M ∩ N)` meets `B_s(w)`. -/
theorem Submission.dsmc_att_blowUp_points_of_approxTangent : ∀ (P n : ℕ) (M N : Set (Euclid P)) (x w : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → w ∈ Q → ∀ s : ℝ, 0 < s → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ y ∈ M ∩ N, ‖lam⁻¹ • (y - x) - w‖ < s := by
  intro P n M N x w Q hMN hQ hw s hs
  -- the tent `g = max(0, s − |· − w|)`: continuous, `g ≥ 0`, `g(w) = s` and `{g ≠ 0} ⊆ B_s(w)`
  set g : Euclid P → ℝ := fun y => max 0 (s - ‖y - w‖)
  have hg_cont : Continuous g :=
    continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).norm)
  have hg_nonneg : ∀ y, 0 ≤ g y := fun y => le_max_left _ _
  have hg_ball : ∀ y, g y ≠ 0 → y ∈ ball w s := by
    intro y hy
    rw [mem_ball, dist_eq_norm]
    by_contra h
    exact hy (max_eq_left (by linarith [not_lt.mp h]))
  have hg_supp : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_closedBall w s) fun y hy =>
      not_not.mp fun h => hy (ball_subset_closedBall (hg_ball y h))
  let f : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨g, hg_cont⟩, hg_supp⟩
  -- `∫_Q f dHⁿ > 0`, hence `∫_{η_{x,λ}(M)} f dHⁿ > 0` for every `λ ∈ (0, λ₀)`
  have hI : 0 < ∫ y in (Q : Set (Euclid P)), g y ∂μHE[n] :=
    Submission.dsmc_att_setIntegral_submodule_pos P n Q g w hQ.1 hg_cont hg_supp hg_nonneg hw
      (by simp [g, hs])
  obtain ⟨lam₀, hlam₀, hpos⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp ((hQ.2 f).eventually (lt_mem_nhds hI))
  refine ⟨lam₀, hlam₀, fun lam hlam hlam₀' => ?_⟩
  set η := Poincare.SimonGMT.Chapter03.blowUpMap x lam with hη
  -- a positive integral of `f` over `η(M)` forces `Hⁿ(η(M) ∩ B_s(w)) ≠ 0`
  have hball : μHE[n] (η '' M ∩ ball w s) ≠ 0 := by
    intro h0
    have hF : 0 < ∫ y in η '' M, f y ∂μHE[n] := hpos ⟨hlam, hlam₀'⟩
    have hF0 : ∫ y in η '' M, f y ∂μHE[n] = 0 := by
      apply integral_eq_zero_of_ae
      rw [EventuallyEq, ae_iff]
      refine measure_mono_null (fun y hy => hg_ball y hy) ?_
      rw [Measure.restrict_apply measurableSet_ball, inter_comm]
      exact h0
    exact hF.ne' hF0
  -- `η(M \ N)` is `Hⁿ`-null and `η(M) ∩ B_s(w) ⊆ (η(M ∩ N) ∩ B_s(w)) ∪ η(M \ N)`
  have hnull : μHE[n] (η '' (M \ N)) = 0 :=
    Submission.dsmc_att_blowUpMap_image_null P n (M \ N) x lam hlam.ne' hMN
  have hcov : η '' M ∩ ball w s ⊆ (η '' (M ∩ N) ∩ ball w s) ∪ η '' (M \ N) := by
    rintro z ⟨⟨y, hyM, rfl⟩, hz⟩
    by_cases hyN : y ∈ N
    · exact Or.inl ⟨⟨y, ⟨hyM, hyN⟩, rfl⟩, hz⟩
    · exact Or.inr ⟨y, ⟨hyM, hyN⟩, rfl⟩
  have hne : μHE[n] (η '' (M ∩ N) ∩ ball w s) ≠ 0 := fun h0 =>
    hball (measure_mono_null hcov (measure_union_null h0 hnull))
  -- so `η(M ∩ N)` meets `B_s(w)`
  obtain ⟨z, ⟨y, hy, rfl⟩, hz⟩ := nonempty_of_measure_ne_zero hne
  refine ⟨y, hy, ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  simpa [hη, Poincare.SimonGMT.Chapter03.blowUpMap] using hz
/-- **Simon Ch. 3, 1.4–1.5** (last step of `TₓM ⊆ TₓN`): rescaled-secant limits lie in the
range of the secant-approximating map.  If every `y ∈ N` near `x` has `|y − x − Aa| ≤ ε|y − x|`
for some `a` (any `ε > 0`), and for every `s > 0` and all small `λ > 0` some `y ∈ N` has
`|λ⁻¹(y − x) − w| < s`, then `w ∈ L = A(ℝᵈ)`.  `L` is a finite-dimensional, hence closed,
subspace; for `η = 2s`, `K ≥ |w| + s` and `εK < s`, a blow-up point `y` at a scale `λ < δ/K`
has `|y − x| < λK < δ`, and its secant approximant `Aa` gives `A(λ⁻¹a) ∈ L` within
`s + εK < η` of `w`. -/
theorem Submission.dsmc_att_mem_range_of_secant_blowUp : ∀ (P d : ℕ) (N : Set (Euclid P)) (x w : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y x < δ → ∃ a : Euclid d, ‖y - x - A a‖ ≤ ε * ‖y - x‖) → (∀ s : ℝ, 0 < s → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ → ∃ y ∈ N, ‖lam⁻¹ • (y - x) - w‖ < s) → w ∈ Set.range A := by
  intro P d N x w A hsec hblow
  -- `L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace: approximate `w` within `η`
  have hL : IsClosed (Set.range A) := by
    rw [← ContinuousLinearMap.coe_coe, ← LinearMap.coe_range]
    exact Submodule.closed_of_finiteDimensional _
  rw [← hL.closure_eq, Metric.mem_closure_iff]
  intro η hη
  -- `η = s + s`, `K ≥ |w| + s` and `εK < s`
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ s + s = η := ⟨η / 2, half_pos hη, add_halves η⟩
  obtain ⟨K, hK, hwK⟩ : ∃ K : ℝ, 0 < K ∧ ‖w‖ + s ≤ K := ⟨‖w‖ + s, by positivity, le_rfl⟩
  obtain ⟨ε, hε, hεK⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * K < s := ⟨s / (K + 1), by positivity, by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith⟩
  obtain ⟨δ, hδ, hδsec⟩ := hsec ε hε
  obtain ⟨lam₀, hlam₀, hlam⟩ := hblow s hs
  -- the scale `λ = min(λ₀, δ/K)/2` lies in `(0, λ₀)` and has `λK < δ`
  have hm : 0 < min lam₀ (δ / K) := lt_min hlam₀ (div_pos hδ hK)
  obtain ⟨lam, hlam_pos, hlam_lt, hlamK⟩ : ∃ lam : ℝ, 0 < lam ∧ lam < lam₀ ∧ lam * K < δ :=
    ⟨min lam₀ (δ / K) / 2, half_pos hm, (half_lt_self hm).trans_le (min_le_left _ _),
      (lt_div_iff₀ hK).mp ((half_lt_self hm).trans_le (min_le_right _ _))⟩
  -- a blow-up point `y ∈ N` has `λ⁻¹|y − x| < |w| + s ≤ K`, so `|y − x| < λK < δ`
  obtain ⟨y, hyN, hy⟩ := hlam lam hlam_pos hlam_lt
  have hlam_inv : 0 ≤ lam⁻¹ := inv_nonneg.mpr hlam_pos.le
  have hyK : lam⁻¹ * ‖y - x‖ < K := by
    rw [← norm_smul_of_nonneg hlam_inv]
    linarith [norm_sub_norm_le (lam⁻¹ • (y - x)) w]
  have hyδ : dist y x < δ := by
    rw [dist_eq_norm]
    linarith [(inv_mul_lt_iff₀ hlam_pos).mp hyK]
  -- its secant approximant `Aa` gives `ℓ = A(λ⁻¹a) ∈ L` with `|λ⁻¹(y − x) − ℓ| < εK < s`
  obtain ⟨a, ha⟩ := hδsec y hyN hyδ
  have hℓ : dist (lam⁻¹ • (y - x)) (A (lam⁻¹ • a)) < s := by
    rw [dist_eq_norm, map_smul, ← smul_sub, norm_smul_of_nonneg hlam_inv]
    calc lam⁻¹ * ‖y - x - A a‖ ≤ lam⁻¹ * (ε * ‖y - x‖) := by gcongr
      _ = ε * (lam⁻¹ * ‖y - x‖) := by ring
      _ < ε * K := by gcongr
      _ < s := hεK
  -- the triangle inequality gives `|w − ℓ| < s + s = η`
  have hw : dist w (lam⁻¹ • (y - x)) < s := by rwa [dist_comm, dist_eq_norm]
  exact ⟨A (lam⁻¹ • a), ⟨lam⁻¹ • a, rfl⟩,
    (dist_triangle w (lam⁻¹ • (y - x)) _).trans_lt (add_lt_add hw hℓ)⟩
/-- Continuity of the inverse of a proper injective chart at a point (Simon Ch. 2, (4.1)–(4.2)):
if `ψ` is continuous and injective on `V`, `ψ(V) ⊆ W`, and `V ∩ ψ⁻¹(K)` is compact for every
compact `K ⊆ W`, then `ψ(v') → ψ(v)` with `v' ∈ V` forces `v' → v`.  Otherwise there are `vⱼ ∈ V`
with `ψ(vⱼ) → ψ(v)` and `|vⱼ - v| ≥ ε`; they lie in the compact set `V ∩ ψ⁻¹({ψ(v)} ∪ {ψ(vⱼ)})`,
and a limit `w ∈ V` of a subsequence has `ψ(w) = ψ(v)`, so `w = v`, a contradiction. -/
theorem Submission.dsmc_chart_inverse_continuity : ∀ (P d : ℕ) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), ContinuousOn ψ V → InjOn ψ V → ψ '' V ⊆ W → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → ∀ v ∈ V, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε := by
  intro P d V W ψ hψ hinj hVW hproper v hv ε hε
  by_contra! hfar
  -- `δ = 1/(j+1)` fails: `vⱼ ∈ V`, `|ψ(vⱼ) - ψ(v)| < 1/(j+1)` and `|vⱼ - v| ≥ ε`
  choose u huV hu_near hu_far using fun j : ℕ => hfar (1 / ((j : ℝ) + 1)) Nat.one_div_pos_of_nat
  have hlim : Tendsto (fun j => ψ (u j)) atTop (𝓝 (ψ v)) :=
    tendsto_iff_dist_tendsto_zero.2 <| squeeze_zero (fun j => dist_nonneg)
      (fun j => (hu_near j).le) tendsto_one_div_add_atTop_nhds_zero_nat
  -- `K = {ψ(v)} ∪ {ψ(vⱼ)}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K)` is compact
  have hKW : insert (ψ v) (range fun j => ψ (u j)) ⊆ W := by
    rintro _ (rfl | ⟨j, rfl⟩)
    exacts [hVW (mem_image_of_mem ψ hv), hVW (mem_image_of_mem ψ (huV j))]
  obtain ⟨w, ⟨hwV, -⟩, φ, hφ, huw⟩ := (hproper _ hKW hlim.isCompact_insert_range).tendsto_subseq
    (x := u) fun j => ⟨huV j, Or.inr ⟨j, rfl⟩⟩
  -- `ψ(v_{φ(i)})` tends to `ψ(w)` (continuity on `V`) and to `ψ(v)`, so `w = v`
  have hw : w = v := hinj hwV hv <| tendsto_nhds_unique
    ((hψ w hwV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨huw, .of_forall fun i => huV (φ i)⟩))
    (hlim.comp hφ.tendsto_atTop)
  rw [hw] at huw
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 huw ε hε
  exact absurd (hu_far (φ N)) (not_le.2 (hN N le_rfl))
/-- **Secant estimate at a chart point** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ(V) = W ∩ N`
with `W` open, `v ∈ V`, `Dψ(v) = A` injective, and let `ψ⁻¹` be continuous at `ψ(v)` on `ψ(V)`.
Then every `y ∈ N` near `ψ(v)` has some `a` with `|y − ψ(v) − Aa| ≤ ε|y − ψ(v)|`.

`A` is anti-Lipschitz, `|a| ≤ K|Aa|`.  With `η = min(1, ε)/(2K)`, differentiability gives
`|ψ(v') − ψ(v) − A(v' − v)| ≤ η|v' − v|` for `|v' − v| < ρ`, hence `|v' − v| ≤ 2K|ψ(v') − ψ(v)|`.
If `y ∈ N` and `|y − ψ(v)| < min(δ₁, δ₂)`, where `B_{δ₂}(ψ(v)) ⊆ W` and `δ₁` is the
inverse-continuity radius for `ρ`, then `y = ψ(v')` with `v' ∈ V`, `|v' − v| < ρ`, and
`a = v' − v` works. -/
theorem Submission.dsmc_chart_secant_estimate : ∀ (P d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P) (A : Euclid d →L[ℝ] Euclid P) (v : Euclid d), IsOpen W → ψ '' V = W ∩ N → v ∈ V → HasFDerivAt ψ A v → Injective A → (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - A a‖ ≤ ε * ‖y - ψ v‖ := by
  intro P d N V W ψ A v hW hψV hv hA hinj hinv ε hε
  -- `A` is anti-Lipschitz: `‖a‖ ≤ K ‖A a‖`
  obtain ⟨K, hK, hKA⟩ := (A : Euclid d →ₗ[ℝ] Euclid P).injective_iff_antilipschitz.1 hinj
  have hbound : ∀ a : Euclid d, ‖a‖ ≤ K * ‖A a‖ := A.bound_of_antilipschitz hKA
  have hK0 : (0 : ℝ) < K := hK
  -- differentiability at `v` with `η = min 1 ε / (2K)`
  set η : ℝ := min 1 ε / (2 * K) with hη_eq
  have hmin : 0 < min 1 ε := lt_min one_pos hε
  have hη : 0 < η := div_pos hmin (by positivity)
  have hKη : K * η = min 1 ε / 2 := by
    rw [hη_eq]
    field_simp
  obtain ⟨ρ, hρ, hdiff⟩ := Metric.eventually_nhds_iff.1 (hA.isLittleO.bound hη)
  -- inverse continuity at radius `ρ`, and `B_{δ₂}(ψ v) ⊆ W`
  obtain ⟨δ₁, hδ₁, hδ₁V⟩ := hinv ρ hρ
  have hψv : ψ v ∈ W ∩ N := hψV ▸ mem_image_of_mem ψ hv
  obtain ⟨δ₂, hδ₂, hδ₂W⟩ := Metric.isOpen_iff.1 hW (ψ v) hψv.1
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
  -- `y = ψ v'` with `v' ∈ V` and `‖v' - v‖ < ρ`
  have hyW : y ∈ W := hδ₂W (mem_ball.2 (hyd.trans_le (min_le_right _ _)))
  obtain ⟨v', hv'V, rfl⟩ : y ∈ ψ '' V := hψV ▸ ⟨hyW, hy⟩
  have hv'ρ : dist v' v < ρ := hδ₁V v' hv'V (hyd.trans_le (min_le_left _ _))
  have hest : ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hdiff hv'ρ
  refine ⟨v' - v, ?_⟩
  -- `‖v' - v‖ ≤ 2K ‖ψ v' - ψ v‖`
  have hlow : ‖v' - v‖ ≤ 2 * K * ‖ψ v' - ψ v‖ := by
    have htri : ‖A (v' - v)‖ ≤ ‖ψ v' - ψ v‖ + ‖ψ v' - ψ v - A (v' - v)‖ :=
      norm_le_norm_add_norm_sub _ _
    have h2 : (K : ℝ) * ‖A (v' - v)‖ ≤ K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by
      calc (K : ℝ) * ‖A (v' - v)‖ ≤ K * (‖ψ v' - ψ v‖ + η * ‖v' - v‖) :=
            mul_le_mul_of_nonneg_left (htri.trans (add_le_add le_rfl hest)) hK0.le
        _ = K * ‖ψ v' - ψ v‖ + K * η * ‖v' - v‖ := by ring
    rw [hKη] at h2
    have h3 : min 1 ε / 2 * ‖v' - v‖ ≤ 1 / 2 * ‖v' - v‖ :=
      mul_le_mul_of_nonneg_right (by linarith [min_le_left 1 ε]) (norm_nonneg _)
    linarith [hbound (v' - v)]
  calc ‖ψ v' - ψ v - A (v' - v)‖ ≤ η * ‖v' - v‖ := hest
    _ ≤ η * (2 * K * ‖ψ v' - ψ v‖) := mul_le_mul_of_nonneg_left hlow hη.le
    _ = 2 * (K * η) * ‖ψ v' - ψ v‖ := by ring
    _ = min 1 ε * ‖ψ v' - ψ v‖ := by rw [hKη]; ring
    _ ≤ ε * ‖ψ v' - ψ v‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
/-- **Simon Ch. 2, §4, (4.3)**, the inclusion `T_qN ⊆ A(ℝᵈ)`.  Suppose that for each `ε > 0`
every `y ∈ N` close to `q` has some `a ∈ ℝᵈ` with `|y − q − Aa| ≤ ε|y − q|`, and let `w = γ'(0)`.
`L = A(ℝᵈ)` is a finite-dimensional, hence closed, subspace.  The difference quotients
`s(t) = t⁻¹(γ(t) − q)` satisfy `dist(s(t), L) ≤ ε|s(t)|` for small `t`, and `s(t) → w`, so
`dist(w, L) ≤ ε|w|` for every `ε > 0`.  Thus `dist(w, L) = 0` and `w ∈ L`. -/
theorem Submission.dsmc_tangentSpace_subset_range_of_secant : ∀ (P d : ℕ) (N : Set (Euclid P)) (q : Euclid P) (A : Euclid d →L[ℝ] Euclid P), (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y q < δ → ∃ a : Euclid d, ‖y - q - A a‖ ≤ ε * ‖y - q‖) → tangentSpace N q ⊆ Set.range A := by
  intro P d N q A hsec w hw
  obtain ⟨γ, -, hγN, hγ0, hγw⟩ := hw
  -- Step 1: `L = A(ℝᵈ)` is a closed (finite-dimensional) and nonempty subset of `ℝᴾ`
  have hLc : IsClosed (Set.range A) :=
    (LinearMap.range (A : Euclid d →ₗ[ℝ] Euclid P)).closed_of_finiteDimensional
  have hLne : (Set.range A).Nonempty := Set.range_nonempty A
  -- Step 2: the difference quotients `s(t) = t⁻¹ (γ(t) − q)` tend to `w` as `t → 0`, `t ≠ 0`
  have hs : Tendsto (slope γ 0) (𝓝[≠] 0) (𝓝 w) := hγw.tendsto_slope
  -- Steps 3–5: `dist(w, L) ≤ ε |w|` for every `ε > 0`
  have key : ∀ ε : ℝ, 0 < ε → infDist w (Set.range A) ≤ ε * ‖w‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hN⟩ := hsec ε hε
    -- `γ(t) ∈ N` and `|γ(t) − q| < δ` for `t` near `0`
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ ball q δ := by
      have hγc := hγw.continuousAt.tendsto
      rw [hγ0] at hγc
      exact hγc (ball_mem_nhds q hδ)
    have hIoo : ∀ᶠ t in 𝓝 (0 : ℝ), t ∈ Ioo (-1 : ℝ) 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
    -- the secant estimate at `y = γ(t)`, divided by `|t|`
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        infDist (slope γ 0 t) (Set.range A) ≤ ε * ‖slope γ 0 t‖ := by
      filter_upwards [nhdsWithin_le_nhds (hball.and hIoo)] with t ht
      obtain ⟨a, ha⟩ := hN (γ t) (hγN ht.2) (mem_ball.mp ht.1)
      have hst : slope γ 0 t = t⁻¹ • (γ t - q) := by
        rw [slope_def_module, sub_zero, hγ0]
      calc infDist (slope γ 0 t) (Set.range A) ≤ dist (slope γ 0 t) (A (t⁻¹ • a)) :=
            infDist_le_dist_of_mem (Set.mem_range_self _)
        _ = ‖t⁻¹‖ * ‖γ t - q - A a‖ := by
            rw [dist_eq_norm, hst, map_smul, ← smul_sub, norm_smul]
        _ ≤ ‖t⁻¹‖ * (ε * ‖γ t - q‖) := by gcongr
        _ = ε * ‖slope γ 0 t‖ := by
            rw [hst, norm_smul]
            ring
    -- pass to the limit `t → 0`
    exact le_of_tendsto_of_tendsto (((continuous_infDist_pt (Set.range A)).tendsto w).comp hs)
      (hs.norm.const_mul ε) hev
  -- Step 6: letting `ε → 0`, `dist(w, L) ≤ 0`
  have h0 : infDist w (Set.range A) ≤ 0 := by
    have hlim : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun ε : ℝ => ε * ‖w‖) (𝓝 0) (𝓝 (0 * ‖w‖)) := tendsto_id.mul_const ‖w‖
      rw [zero_mul] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε => key ε hε)
  -- Step 7: `L` is closed, so `dist(w, L) = 0` gives `w ∈ L`
  exact (hLc.mem_iff_infDist_zero hLne).mpr (le_antisymm h0 infDist_nonneg)
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ` is `Cʳ` (`r ≥ 1`) on an open `V ⊆ ℝᵈ` and `ψ(V) ⊆ N`,
then every `Dψ(v) a`, `v ∈ V`, is the velocity at `0` of a `C¹` curve in `N` through `ψ(v)`, i.e.
`Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N`.  For `a = 0` take the constant curve.  Otherwise, with
`B_{ρ₀}(v) ⊆ V`, `c = ρ₀ / |a|` and `h(t) = t / (1 + t² / c²)` (smooth, `h(0) = 0`, `h'(0) = 1`,
`|h| ≤ c / 2`), the curve `γ(t) = ψ(v + h(t) a)` stays in `ψ(V)` and has velocity `Dψ(v) a`. -/
theorem Submission.dsmc_chart_range_subset_tangentSpace : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → ContDiffOn ℝ r ψ V → ψ '' V ⊆ N → ∀ v ∈ V, Set.range (fderiv ℝ ψ v) ⊆ tangentSpace N (ψ v) := by
  rintro P r d N V ψ hr hV hψ hN v hv _ ⟨a, rfl⟩
  -- `ψ` is `C¹` on `V`, hence differentiable at the interior point `v`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  by_cases ha : a = 0
  · -- `a = 0`: the constant curve `ψ(v)` has velocity `0 = Dψ(v) 0`
    subst ha
    refine ⟨fun _ => ψ v, contDiffOn_const, fun _ _ => hN (mem_image_of_mem ψ hv), rfl, ?_⟩
    simpa using hasDerivAt_const (0 : ℝ) (ψ v)
  · -- `a ≠ 0`: `β(t) = v + h(t) a` with `h(t) = t / (1 + t² / c²)`, `c = ρ₀ / |a|`
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hV v hv
    have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    set c : ℝ := ρ₀ / ‖a‖ with hc_def
    have hc : 0 < c := div_pos hρ₀ ha'
    have hden : ∀ t : ℝ, 0 < 1 + t ^ 2 / c ^ 2 := fun t => by positivity
    set h : ℝ → ℝ := fun t => t / (1 + t ^ 2 / c ^ 2) with hh_def
    -- (a) `h` is smooth
    have h_cd : ContDiff ℝ 1 h :=
      contDiff_id.div (contDiff_const.add ((contDiff_id.pow 2).div_const _)) fun t => (hden t).ne'
    -- (b) `h'(0) = 1`
    have h_deriv : HasDerivAt h 1 0 := by
      have := hasDerivAt_id' (x := (0 : ℝ)) |>.fun_div
        (((hasDerivAt_id' (x := (0 : ℝ))).fun_pow 2).div_const (c ^ 2) |>.const_add 1) (hden 0).ne'
      convert this using 1
      simp
    -- (c) `|h(t)| ≤ c / 2`, since `2 c |t| ≤ c² + t²`
    have h_bd : ∀ t, |h t| ≤ c / 2 := by
      intro t
      rw [hh_def, abs_div, abs_of_pos (hden t), div_le_iff₀ (hden t)]
      have h1 : c / 2 * (1 + t ^ 2 / c ^ 2) = (c ^ 2 + |t| ^ 2) / (2 * c) := by
        rw [sq_abs]; field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c - |t|)]
    -- `β` stays in `B_{ρ₀}(v) ⊆ V`, `β(0) = v` and `β'(0) = a`
    set β : ℝ → Euclid d := fun t => v + h t • a with hβ_def
    have hβV : ∀ t, β t ∈ V := fun t => hball <| by
      rw [Metric.mem_ball, dist_eq_norm, hβ_def]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |h t| * ‖a‖ ≤ c / 2 * ‖a‖ := by gcongr; exact h_bd t
        _ = ρ₀ / 2 := by rw [hc_def]; field_simp
        _ < ρ₀ := by linarith
    have hβ0 : β 0 = v := by simp [hβ_def, hh_def]
    have hβ_cd : ContDiff ℝ 1 β := contDiff_const.add (h_cd.smul contDiff_const)
    have hβ_deriv : HasDerivAt β a 0 := by
      have := HasDerivAt.const_add v (h_deriv.smul_const a)
      rwa [one_smul] at this
    -- `γ = ψ ∘ β` is `C¹` on `(-1, 1)`, lies in `ψ(V) ⊆ N`, and `γ'(0) = Dψ(v) a`
    refine ⟨ψ ∘ β, hψ1.comp hβ_cd.contDiffOn fun t _ => hβV t,
      fun t _ => hN (mem_image_of_mem ψ (hβV t)), by simp [hβ0], ?_⟩
    exact hψv.comp_hasDerivAt_of_eq 0 hβ_deriv hβ0.symm

/-- **Chart lemma** (Simon Ch. 2, §4, (4.1)–(4.3)).  Let `ψ` be a chart of `N` as in
`IsEmbeddedSubmanifold`: `Cʳ` (`r ≥ 1`) and injective on the open `V`, `ψ(V) = W ∩ N`, proper,
with `Dψ` injective on `V`.  For `v ∈ V`, `q = ψ(v)` and `A = Dψ(v)`: (i) `T_qN = A(ℝᵈ)`;
(ii) `ψ⁻¹` is continuous at `q`; (iii) every `y ∈ N` near `q` has `|y − q − Aa| ≤ ε|y − q|` for
some `a`.  (ii) is `dsmc_chart_inverse_continuity` (properness and injectivity), (iii) is
`dsmc_chart_secant_estimate` (differentiability at `v`, injectivity of `A` and (ii)), and (i)
combines `dsmc_tangentSpace_subset_range_of_secant` (by (iii), curve velocities lie in the closed
subspace `A(ℝᵈ)`) with `dsmc_chart_range_subset_tangentSpace` (the curves `t ↦ ψ(v + h(t)a)`). -/
theorem Submission.dsmc_chart_tangentSpace_eq_range : ∀ (P r d : ℕ) (N : Set (Euclid P)) (V : Set (Euclid d)) (W : Set (Euclid P)) (ψ : Euclid d → Euclid P), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → ∀ v ∈ V, tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ N, dist y (ψ v) < δ → ∃ a : Euclid d, ‖y - ψ v - fderiv ℝ ψ v a‖ ≤ ε * ‖y - ψ v‖) := by
  intro P r d N V W ψ hr hV hW hψ hinj himg hprop hDψ v hv
  -- (ii): properness and injectivity of `ψ` on `V` make `ψ⁻¹` continuous at `ψ v`
  have hii : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ v' ∈ V, dist (ψ v') (ψ v) < δ → dist v' v < ε :=
    Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj
      (himg.subset.trans inter_subset_left) hprop v hv
  -- `ψ` is `C¹` on the open set `V ∋ v`, so `A = fderiv ℝ ψ v` is its derivative at `v`
  have hA : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    (hψ.differentiableOn (by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr)).hasFDerivAt
      (hV.mem_nhds hv)
  -- (iii): the secant estimate at `ψ v`, from `hA`, injectivity of `A` and (ii)
  have hiii := Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW himg hv hA
    (hDψ v hv) hii
  -- (i): `T_{ψ v}N ⊆ A(ℝᵈ)` by (iii); `A(ℝᵈ) ⊆ T_{ψ v}N` since `ψ '' V ⊆ N`
  exact ⟨Set.Subset.antisymm
      (Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v) hiii)
      (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ
        (himg.subset.trans inter_subset_right) v hv),
    hii, hiii⟩

/-- **A `C¹` field of tangent projections near a point of a `C²` submanifold** (Simon Ch. 4,
2.5–2.7; Ch. 2, 5.9).  Near `y₀ ∈ N ∩ U` there is a `C¹` field `Pt` of self-adjoint operators with
`‖DPt‖ ≤ β` on `B_{2r}(y₀)` such that `Pt(q)` is the orthogonal projection onto `T_qN` for every
`q ∈ N ∩ B_{3r}(y₀)`.  Instead of the nearest-point projection of a tubular neighbourhood we use a
`C¹` retraction parameter built from a `C²` chart `ψ : V → W`, `ψ(v₀) = y₀`: `Pt(y) = G(Dψ(σ(y)))`,
where `G(B) = B (B*B)⁻¹ B*` is the orthogonal projection onto `range B` and `σ = λ ∘ L` with `L` a
linear left inverse of `Dψ(v₀)` and `λ` a local inverse of `L ∘ ψ` (inverse function theorem), so
that `σ(ψ(z)) = z` near `v₀`.  `dsmc_chart_tangentSpace_eq_range` gives `T_{ψ(z)}N = range Dψ(z)`
and the continuity of `ψ⁻¹` at `y₀`; `β` bounds `‖DPt‖` on the compact `B̄_{2r}(y₀)`. -/
theorem Submission.dsmc_tangent_projection_field : ∀ (P d : ℕ) (U N : Set (Euclid P)) (y₀ : Euclid P), IsOpen U → IsEmbeddedSubmanifold 2 d N → y₀ ∈ N ∩ U → ∃ (r β : ℝ) (Pt : Euclid P → (Euclid P →L[ℝ] Euclid P)), 0 < r ∧ 0 ≤ β ∧ closedBall y₀ (3 * r) ⊆ U ∧ ContDiffOn ℝ 1 Pt (ball y₀ (3 * r)) ∧ (∀ y ∈ ball y₀ (3 * r), ∀ u w : Euclid P, inner ℝ (Pt y u) w = inner ℝ u (Pt y w)) ∧ (∀ y ∈ ball y₀ (2 * r), ‖fderiv ℝ Pt y‖ ≤ β) ∧ (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u : Euclid P, Pt q u ∈ tangentSpace N q) ∧ (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u ∈ tangentSpace N q, Pt q u = u) := by
  intro P d U N y₀ hU hN hy₀
  -- Step 1: a `C²` chart `ψ : V → W` with `y₀ = ψ(v₀)`; `T_{ψ(z)}N = range Dψ(z)` and `ψ⁻¹` is
  -- continuous at `y₀` (chart lemma); `z ↦ Dψ(z)` is `C¹` on `V`
  obtain ⟨hy₀N, hy₀U⟩ := hy₀
  obtain ⟨V, W, ψ, hV, hW, hy₀W, hψ, hinj, himg, hprop, hDψ⟩ := hN y₀ hy₀N
  obtain ⟨v₀, hv₀V, rfl⟩ : y₀ ∈ ψ '' V := by rw [himg]; exact ⟨hy₀W, hy₀N⟩
  have hchart := Submission.dsmc_chart_tangentSpace_eq_range P 2 d N V W ψ (by norm_num) hV hW hψ
    hinj himg hprop hDψ
  have hA : ContDiffOn ℝ 1 (fun z => fderiv ℝ ψ z) V := hψ.fderiv_of_isOpen hV (by norm_num)
  -- Step 2: for injective `B`, `G(B) = B (B*B)⁻¹ B*` is `C¹` near `B`, self-adjoint, maps into
  -- `range B` and fixes `range B` pointwise
  obtain ⟨G, hG⟩ : ∃ G : (Euclid d →L[ℝ] Euclid P) → (Euclid P →L[ℝ] Euclid P),
      ∀ B : Euclid d →L[ℝ] Euclid P, Injective B → ContDiffAt ℝ 1 G B ∧
        (∀ u w : Euclid P, inner ℝ (G B u) w = inner ℝ u (G B w)) ∧
        (∀ u : Euclid P, G B u ∈ Set.range B) ∧ ∀ a : Euclid d, G B (B a) = B a := by
    -- the real adjoint `B ↦ B*` as a continuous linear map
    let adjL : (Euclid d →L[ℝ] Euclid P) →L[ℝ] (Euclid P →L[ℝ] Euclid d) :=
      { toFun := fun B => ContinuousLinearMap.adjoint B
        map_add' := fun B C => by simp
        map_smul' := fun c B => by simp
        cont := ContinuousLinearMap.adjoint.continuous }
    have hadj : ∀ B, adjL B = ContinuousLinearMap.adjoint B := fun B => rfl
    refine ⟨fun B => B ∘L (Ring.inverse (adjL B ∘L B) ∘L adjL B), fun B hB => ?_⟩
    -- `C = B*B` is self-adjoint with `⟨C a, a⟩ = ‖B a‖²`, hence injective and a unit
    set C : Euclid d →L[ℝ] Euclid d := adjL B ∘L B with hC_def
    have hCsymm : ∀ x y : Euclid d, inner ℝ (C x) y = inner ℝ x (C y) := by
      intro x y
      simp only [hC_def, ContinuousLinearMap.comp_apply, hadj]
      rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    have hCinj : Injective C := by
      intro x y hxy
      have h0 : C (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have h1 : inner ℝ (C (x - y)) (x - y) = ‖B (x - y)‖ ^ 2 := by
        simp only [hC_def, ContinuousLinearMap.comp_apply, hadj]
        rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
      rw [h0, inner_zero_left] at h1
      have h2 : B (x - y) = 0 := by
        have : ‖B (x - y)‖ = 0 := by nlinarith [norm_nonneg (B (x - y))]
        exact norm_eq_zero.1 this
      exact sub_eq_zero.1 (hB (by rw [h2, map_zero]))
    have hCunit : IsUnit C := by
      rw [ContinuousLinearMap.isUnit_iff_bijective]
      exact ⟨hCinj, LinearMap.injective_iff_surjective.1 hCinj⟩
    -- `C⁻¹` is a two-sided inverse of `C`, and self-adjoint
    set Ci := Ring.inverse C
    have hCiC : ∀ x, Ci (C x) = x := fun x => by
      have := Ring.inverse_mul_cancel C hCunit
      simpa using congrArg (fun T : Euclid d →L[ℝ] Euclid d => T x) this
    have hCCi : ∀ x, C (Ci x) = x := fun x => by
      have := Ring.mul_inverse_cancel C hCunit
      simpa using congrArg (fun T : Euclid d →L[ℝ] Euclid d => T x) this
    have hCisymm : ∀ x y : Euclid d, inner ℝ (Ci x) y = inner ℝ x (Ci y) := by
      intro x y
      calc inner ℝ (Ci x) y = inner ℝ (Ci x) (C (Ci y)) := by rw [hCCi]
        _ = inner ℝ (C (Ci x)) (Ci y) := (hCsymm _ _).symm
        _ = inner ℝ x (Ci y) := by rw [hCCi]
    refine ⟨?_, ?_, fun u => ⟨_, rfl⟩, ?_⟩
    · -- `B' ↦ B'*B'` is smooth and `Ring.inverse` is smooth at the unit `C`
      obtain ⟨u, hu⟩ := hCunit
      have hinv : ContDiffAt ℝ 1
          (fun B' : Euclid d →L[ℝ] Euclid P => Ring.inverse (adjL B' ∘L B')) B := by
        have h1 : ContDiffAt ℝ 1 (fun B' : Euclid d →L[ℝ] Euclid P => adjL B' ∘L B') B :=
          adjL.contDiff.contDiffAt.clm_comp contDiffAt_id
        have h2 : ContDiffAt ℝ 1 Ring.inverse (adjL B ∘L B) := by
          have := contDiffAt_ringInverse ℝ (n := 1) u
          rw [hu] at this
          exact this
        exact ContDiffAt.comp (g := Ring.inverse)
          (f := fun B' : Euclid d →L[ℝ] Euclid P => adjL B' ∘L B') B h2 h1
      exact contDiffAt_id.clm_comp (hinv.clm_comp adjL.contDiff.contDiffAt)
    · intro u w
      simp only [ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_right, ← hadj, hCisymm,
        hadj, ContinuousLinearMap.adjoint_inner_left]
      rfl
    · intro a
      simp only [ContinuousLinearMap.comp_apply]
      have : adjL B (B a) = C a := rfl
      rw [this, hCiC]
  -- Steps 3–4: a `C¹` map `σ` on an open `O ∋ y₀`, with values in `V`, such that `σ(ψ(z)) = z`
  -- for `z` in an open `O₁ ∋ v₀`.  A continuous linear left inverse `L` of `A = Dψ(v₀)` plays
  -- the role of the projection onto `T_{y₀}N = range A` (e.g. `L = A⁻¹ ∘ p_{range A}`), so
  -- `f = L ∘ ψ` has `Df(v₀) = id`; `λ` is the local inverse of `f` given by the inverse function
  -- theorem, restricted to an open set on which it is `C¹` and maps into `V`, and `σ = λ ∘ L`.
  obtain ⟨O, O₁, σ, hO, hO₁, hv₀O₁, hσ, hσV, hσψ⟩ : ∃ (O : Set (Euclid P)) (O₁ : Set (Euclid d))
      (σ : Euclid P → Euclid d), IsOpen O ∧ IsOpen O₁ ∧ v₀ ∈ O₁ ∧ ContDiffOn ℝ 1 σ O ∧
        MapsTo σ O V ∧ ∀ z ∈ O₁, ψ z ∈ O ∧ σ (ψ z) = z := by
    set A := fderiv ℝ ψ v₀
    obtain ⟨L₀, hL₀⟩ := LinearMap.exists_leftInverse_of_injective (A : Euclid d →ₗ[ℝ] Euclid P)
      (LinearMap.ker_eq_bot.2 (hDψ v₀ hv₀V))
    let L : Euclid P →L[ℝ] Euclid d := LinearMap.toContinuousLinearMap L₀
    have hLA : ∀ a, L (A a) = a := fun a => by
      have := LinearMap.congr_fun hL₀ a
      simpa [L] using this
    set f : Euclid d → Euclid d := fun z => L (ψ z)
    have hψat : ContDiffAt ℝ 1 ψ v₀ := (hψ.contDiffAt (hV.mem_nhds hv₀V)).of_le (by norm_num)
    have hfat : ContDiffAt ℝ 1 f v₀ := L.contDiff.contDiffAt.comp v₀ hψat
    have hderiv0 : HasFDerivAt f (L ∘L A) v₀ :=
      L.hasFDerivAt.comp v₀ (hψat.differentiableAt (by norm_num)).hasFDerivAt
    have hLA' : L ∘L A =
        ((ContinuousLinearEquiv.refl ℝ (Euclid d) : Euclid d ≃L[ℝ] Euclid d) :
          Euclid d →L[ℝ] Euclid d) := by
      ext1 a
      simp [hLA]
    have hderiv : HasFDerivAt f
        ((ContinuousLinearEquiv.refl ℝ (Euclid d) : Euclid d ≃L[ℝ] Euclid d) :
          Euclid d →L[ℝ] Euclid d) v₀ :=
      hLA' ▸ hderiv0
    have hstrict : HasStrictFDerivAt f
        ((ContinuousLinearEquiv.refl ℝ (Euclid d) : Euclid d ≃L[ℝ] Euclid d) :
          Euclid d →L[ℝ] Euclid d) v₀ :=
      hfat.hasStrictFDerivAt' hderiv one_ne_zero
    -- the inverse function theorem: a partial homeomorphism `e = f` near `v₀`
    set e := HasStrictFDerivAt.toOpenPartialHomeomorph f hstrict
    have he_coe : (e : Euclid d → Euclid d) = f := rfl
    have hv₀src : v₀ ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
    have hfv₀tgt : f v₀ ∈ e.target := hstrict.image_mem_toOpenPartialHomeomorph_target
    have hsymm_v₀ : e.symm (f v₀) = v₀ := e.left_inv hv₀src
    have hsymm : ContDiffAt ℝ 1 e.symm (f v₀) := by
      refine e.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ (Euclid d)) hfv₀tgt ?_ ?_
      · rw [hsymm_v₀]; exact hderiv
      · rw [hsymm_v₀]; exact hfat
    -- `O₂ ∋ f(v₀)` open, inside the target, on which `e⁻¹` is `C¹` with values in `V`
    have hev : ∀ᶠ w in 𝓝 (f v₀), ContDiffAt ℝ 1 e.symm w := hsymm.eventually (by simp)
    have hpre : e.symm ⁻¹' V ∈ 𝓝 (f v₀) :=
      (e.continuousAt_symm hfv₀tgt).preimage_mem_nhds (by rw [hsymm_v₀]; exact hV.mem_nhds hv₀V)
    have hnhds : e.target ∩ (e.symm ⁻¹' V ∩ {w | ContDiffAt ℝ 1 e.symm w}) ∈ 𝓝 (f v₀) :=
      Filter.inter_mem (e.open_target.mem_nhds hfv₀tgt) (Filter.inter_mem hpre hev)
    obtain ⟨O₂, hO₂sub, hO₂open, hfv₀O₂⟩ := _root_.mem_nhds_iff.1 hnhds
    -- `O = L⁻¹(O₂)`, `O₁ = e.source ∩ f⁻¹(O₂)`, `σ = e⁻¹ ∘ L`
    refine ⟨L ⁻¹' O₂, e.source ∩ f ⁻¹' O₂, fun y => e.symm (L y), hO₂open.preimage L.continuous,
      ?_, ⟨hv₀src, hfv₀O₂⟩, ?_, fun y hy => (hO₂sub hy).2.1, ?_⟩
    · have : ContinuousOn f e.source := by rw [← he_coe]; exact e.continuousOn
      exact this.isOpen_inter_preimage e.open_source hO₂open
    · intro y hy
      have h1 : ContDiffAt ℝ 1 e.symm (L y) := (hO₂sub hy).2.2
      exact (h1.comp y L.contDiff.contDiffAt).contDiffWithinAt
    · rintro z ⟨hzsrc, hzO₂⟩
      refine ⟨hzO₂, ?_⟩
      show e.symm (f z) = z
      rw [← he_coe]
      exact e.left_inv hzsrc
  -- Step 5: `Pt(y) = G(Dψ(σ(y)))` is `C¹` on `O`
  set Pt : Euclid P → (Euclid P →L[ℝ] Euclid P) := fun y => G (fderiv ℝ ψ (σ y))
  have hPtO : ContDiffOn ℝ 1 Pt O := fun y hy =>
    (hG _ (hDψ _ (hσV hy))).1.comp_contDiffWithinAt y ((hA (σ y) (hσV hy)).comp y (hσ y hy) hσV)
  -- Step 6: `B_{ε₁}(v₀) ⊆ O₁`; `z ∈ V`, `|ψ(z) − y₀| < δ₁` give `|z − v₀| < ε₁`; choose `r > 0`
  -- with `3r ≤ δ₁` and `B̄_{3r}(y₀) ⊆ U ∩ W ∩ O`
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.1 hO₁ v₀ hv₀O₁
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := (hchart v₀ hv₀V).2.1 ε₁ hε₁
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 ((hU.inter hW).inter hO) (ψ v₀)
    ⟨⟨hy₀U, hy₀W⟩, (hσψ v₀ hv₀O₁).1⟩
  set r := min (ρ / 6) (δ₁ / 3)
  have hr : 0 < r := lt_min (by linarith) (by linarith)
  have h3r : 3 * r < ρ := by have := min_le_left (ρ / 6) (δ₁ / 3); linarith
  have h3rδ : 3 * r ≤ δ₁ := by have := min_le_right (ρ / 6) (δ₁ / 3); linarith
  have hcl : closedBall (ψ v₀) (3 * r) ⊆ U ∩ W ∩ O := (closedBall_subset_ball h3r).trans hρsub
  have hballO : ball (ψ v₀) (3 * r) ⊆ O :=
    ball_subset_closedBall.trans (hcl.trans inter_subset_right)
  have hPt3 : ContDiffOn ℝ 1 Pt (ball (ψ v₀) (3 * r)) := hPtO.mono hballO
  -- Step 7: `DPt` is continuous on `B_{3r}(y₀)`, hence bounded on the compact `B̄_{2r}(y₀)`
  have hcont2 : ContinuousOn (fderiv ℝ Pt) (closedBall (ψ v₀) (2 * r)) :=
    (hPt3.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono
      (closedBall_subset_ball (show 2 * r < 3 * r by linarith))
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (E := Euclid P →L[ℝ] Euclid P →L[ℝ] Euclid P) (isCompact_closedBall (ψ v₀) (2 * r)) hcont2
  -- Step 8: `q ∈ N ∩ B_{3r}(y₀)` is `ψ(z)` with `z ∈ O₁`, so `Pt(q) = G(Dψ(z))` and
  -- `T_qN = range Dψ(z)`
  have hNq : ∀ q ∈ N ∩ ball (ψ v₀) (3 * r), ∃ z ∈ V,
      Pt q = G (fderiv ℝ ψ z) ∧ tangentSpace N q = Set.range (fderiv ℝ ψ z) := by
    rintro q ⟨hqN, hqB⟩
    obtain ⟨z, hzV, rfl⟩ : q ∈ ψ '' V := by
      rw [himg]; exact ⟨(hcl (ball_subset_closedBall hqB)).1.2, hqN⟩
    have hzO₁ : z ∈ O₁ := hball (mem_ball.2 (hδ₁' z hzV (lt_of_lt_of_le (mem_ball.1 hqB) h3rδ)))
    refine ⟨z, hzV, ?_, (hchart z hzV).1⟩
    show G (fderiv ℝ ψ (σ (ψ z))) = G (fderiv ℝ ψ z)
    rw [(hσψ z hzO₁).2]
  -- Step 9: assemble, with `β = max C 0`
  refine ⟨r, max C 0, Pt, hr, le_max_right _ _, fun y hy => (hcl hy).1.1, hPt3,
    fun y hy u w => (hG _ (hDψ _ (hσV (hballO hy)))).2.1 u w,
    fun y hy => (hC y (ball_subset_closedBall hy)).trans (le_max_left _ _), ?_, ?_⟩
  · intro q hq u
    obtain ⟨z, hzV, hPtq, hTq⟩ := hNq q hq
    rw [hPtq, hTq]
    exact (hG _ (hDψ z hzV)).2.2.1 u
  · intro q hq u hu
    obtain ⟨z, hzV, hPtq, hTq⟩ := hNq q hq
    rw [hTq] at hu
    obtain ⟨a, rfl⟩ := hu
    rw [hPtq]
    exact (hG _ (hDψ z hzV)).2.2.2 a
/-- **Approximate tangent planes of a set carried by a `Cʳ` submanifold lie in its tangent
spaces** (Simon Ch. 3, 1.4–1.5, chapter-03.txt lines 75–90; Ch. 2, 4.1 and 4.3, chapter-02.txt
lines 850–871).  Let `N` be an embedded `Cʳ` `d`-submanifold of `ℝᴾ`, `r ≥ 1`, let `x ∈ N`, let
`Hⁿ(M \ N) = 0` and let `Q` be an approximate tangent space of `M` at `x`.  Then `Q ⊆ T_xN`.
A chart `ψ` of `N` with `x = ψ(v₀)` gives `T_xN = Dψ(v₀)(ℝᵈ)` and the secant estimate
`|y − x − Dψ(v₀)a| ≤ ε|y − x|` for `y ∈ N` near `x`.  Every `w ∈ Q` is, at every small scale `λ`,
within `s` of a rescaled secant `λ⁻¹(y − x)` with `y ∈ M ∩ N`; hence `w ∈ Dψ(v₀)(ℝᵈ)`. -/
theorem Submission.dsmc_approxTangentPlane_subset_tangentSpace : ∀ (P n r d : ℕ) (M N : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), 1 ≤ r → IsEmbeddedSubmanifold r d N → x ∈ N → μHE[n] (M \ N) = 0 → HasApproximateTangentSpaceAt n M x Q → (Q : Set (Euclid P)) ⊆ tangentSpace N x := by
  intro P n r d M N x Q hr hN hxN hMN hQ
  -- a chart `ψ : V → W` of `N` at `x`; `x ∈ W ∩ N = ψ(V)`, so `x = ψ(v₀)` with `v₀ ∈ V`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, himg, hprop, hrank⟩ := hN x hxN
  obtain ⟨v₀, hv₀, rfl⟩ : x ∈ ψ '' V := by
    rw [himg]
    exact ⟨hxW, hxN⟩
  -- `T_xN = Dψ(v₀)(ℝᵈ)`, and `N` satisfies the secant estimate at `x` for `Dψ(v₀)`
  obtain ⟨hT, -, hsec⟩ := Submission.dsmc_chart_tangentSpace_eq_range P r d N V W ψ hr hV hW hψ
    hinj himg hprop hrank v₀ hv₀
  intro w hw
  rw [hT]
  -- the blow-up points `y ∈ M ∩ N` with `|λ⁻¹(y − x) − w| < s`, `0 < λ < λ₀`, lie in `N`
  refine Submission.dsmc_att_mem_range_of_secant_blowUp P d N (ψ v₀) w (fderiv ℝ ψ v₀) hsec
    fun s hs => ?_
  obtain ⟨lam₀, hlam₀, hpts⟩ :=
    Submission.dsmc_att_blowUp_points_of_approxTangent P n M N (ψ v₀) w Q hMN hQ hw s hs
  refine ⟨lam₀, hlam₀, fun lam hlam hlt => ?_⟩
  obtain ⟨y, hy, hyw⟩ := hpts lam hlam hlt
  exact ⟨y, hy.2, hyw⟩
/-- **Cut-off quadratic moments over `n`-planes** (the constant `cₙ` of the measurability proof
for the approximate tangent planes of Simon Ch. 3, 1.4).  For `n ≥ 1` one constant `c > 0`,
depending only on `n`, gives `∫_Q max(1 − |y|², 0)⟨u, y⟩² dHⁿ(y) = c|p_Q u|²` for every `P`,
every `n`-dimensional subspace `Q ⊆ ℝᴾ` and every `u ∈ ℝᴾ`.  On `ℝⁿ` put
`q(w) = ∫ max(1 − |z|², 0)⟨w, z⟩² dHⁿ(z)` and `c = q(e)`, `|e| = 1`: linear isometries preserve
`Hⁿ`, so `q` is invariant under them, `q(tw) = t²q(w)`, and a reflection maps `|w|e` to `w`,
whence `q(w) = c|w|²`; `c > 0` since the integrand is continuous, `≥ 0`, compactly supported and
`3/16` at `e/2`.  An isometry `ι = L⁻¹ : ℝⁿ → Q ⊆ ℝᴾ` carries `Hⁿ` to `Hⁿ⌞Q`, and
`⟨u, ι z⟩ = ⟨L(p_Q u), z⟩`, so the integral is `q(L(p_Q u)) = c|p_Q u|²`. -/
theorem Submission.exists_plane_cutoff_quadratic_moment_eq : ∀ n : ℕ, 0 < n → ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ) (Q : Submodule ℝ (Euclid P)), Module.finrank ℝ Q = n → ∀ u : Euclid P, ∫ y in (Q : Set (Euclid P)), max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2 ∂μHE[n] = c * ‖Q.starProjection u‖ ^ 2 := by
  intro n hn
  -- The moment `q(w)` on the model plane `ℝⁿ`; the constant is `c = q(e)` for a unit vector `e`.
  obtain ⟨q, hq_def⟩ : ∃ q : Euclid n → ℝ,
      ∀ w, q w = ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ w z ^ 2 ∂μHE[n] :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Euclid n, ‖e‖ = 1 := ⟨EuclideanSpace.single ⟨0, hn⟩ 1, by simp⟩
  -- `q(Rw) = q(w)` for a linear isometry `R`: substitute `z = Rz'`, `R` preserves `Hⁿ`.
  have hq_iso : ∀ (R : Euclid n ≃ₗᵢ[ℝ] Euclid n) (w : Euclid n), q (R w) = q w := by
    intro R w
    have key : ∫ z, max (1 - ‖R z‖ ^ 2) 0 * inner ℝ (R w) (R z) ^ 2 ∂μHE[n] =
        ∫ z, max (1 - ‖z‖ ^ 2) 0 * inner ℝ (R w) z ^ 2 ∂μHE[n] :=
      (R.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure n).integral_comp
        R.toHomeomorph.measurableEmbedding (fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ (R w) y ^ 2)
    simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map] at key
    rw [hq_def, hq_def, ← key]
  have hq_smul : ∀ (t : ℝ) (w : Euclid n), q (t • w) = t ^ 2 * q w := by
    intro t w
    rw [hq_def, hq_def, ← integral_const_mul]
    congr 1
    funext z
    rw [real_inner_smul_left]
    ring
  -- `q(w) = c|w|²`: the reflection in `(|w|e − w)ᗮ` maps `|w|e` to `w`.
  have hq : ∀ w : Euclid n, q w = q e * ‖w‖ ^ 2 := by
    intro w
    have h1 : ‖‖w‖ • e‖ = ‖w‖ := by rw [norm_smul, he, mul_one, norm_norm]
    obtain ⟨R, hR⟩ : ∃ R : Euclid n ≃ₗᵢ[ℝ] Euclid n, R (‖w‖ • e) = w :=
      ⟨_, Submodule.reflection_sub h1⟩
    calc q w = q (R (‖w‖ • e)) := by rw [hR]
      _ = q (‖w‖ • e) := hq_iso R _
      _ = q e * ‖w‖ ^ 2 := by rw [hq_smul, mul_comm]
  -- `c > 0`: on `ℝⁿ`, `Hⁿ` is Lebesgue measure, and the integrand is `3/16` at `e/2`.
  have hc : 0 < q e := by
    have hcont : Continuous fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      fun_prop
    have hsupp : HasCompactSupport fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun z hz => ?_
      have h1 : 1 < ‖z‖ := by simpa using hz
      have h2 : 1 - ‖z‖ ^ 2 ≤ 0 := by nlinarith
      simp [max_eq_right h2]
    have hnonneg : 0 ≤ fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2 :=
      fun z => mul_nonneg (le_max_right _ _) (sq_nonneg _)
    have hx : (fun z : Euclid n => max (1 - ‖z‖ ^ 2) 0 * inner ℝ e z ^ 2) ((1 / 2 : ℝ) • e) ≠ 0 := by
      simp only [norm_smul, he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      norm_num
    rw [hq_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp hnonneg hx
  refine ⟨q e, hc, fun P Q hQ u => ?_⟩
  -- An orthonormal basis of `Q` indexed by `Fin n` gives `L : Q ≃ ℝⁿ`; `ι = L⁻¹` is an isometry
  -- of `ℝⁿ` onto `Q ⊆ ℝᴾ`, so `ι_# Hⁿ = Hⁿ⌞Q`.
  obtain ⟨L, -⟩ : ∃ L : Q ≃ₗᵢ[ℝ] Euclid n, True :=
    ⟨((stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)).repr, trivial⟩
  have hι : Isometry fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    isometry_subtype_coe.comp L.symm.isometry
  have hrange : Set.range (fun z : Euclid n => ((L.symm z : Q) : Euclid P)) =
      (Q : Set (Euclid P)) := by
    ext y
    refine ⟨?_, fun hy => ⟨L ⟨y, hy⟩, by simp⟩⟩
    rintro ⟨z, rfl⟩
    exact (L.symm z).2
  have hemb : MeasurableEmbedding fun z : Euclid n => ((L.symm z : Q) : Euclid P) :=
    hι.isClosedEmbedding.measurableEmbedding
  have hnorm : ∀ z : Euclid n, ‖((L.symm z : Q) : Euclid P)‖ = ‖z‖ := fun z => L.symm.norm_map z
  -- `⟨u, ι z⟩ = ⟨p_Q u, ι z⟩ = ⟨L(p_Q u), z⟩`.
  have hinner : ∀ z : Euclid n, inner ℝ u ((L.symm z : Q) : Euclid P) =
      inner ℝ (L (Q.orthogonalProjectionOnto u)) z := by
    intro z
    rw [LinearIsometryEquiv.inner_map_eq_flip,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [← hrange, ← hι.map_euclideanHausdorffMeasure, hemb.integral_map]
  simp only [hnorm, hinner]
  rw [← hq_def, hq, LinearIsometryEquiv.norm_map, Submodule.starProjection_apply]
  rfl
/-- A field of orthogonal projections `p_x = (K x).starProjection` is a.e.-measurable (Borel
σ-algebra of the operator-norm topology) when each quadratic form `x ↦ |p_x u|²` is.  As `p_x` is
self-adjoint and idempotent, `⟪p_x u, w⟫ = (|p_x(u + w)|² − |p_x(u − w)|²)/4`, so the matrix
coefficients `⟪p_x e_a, e_b⟫` are a.e.-measurable, and `p_x = Σ_{a,b} ⟪p_x e_a, e_b⟫ ⟪e_a, ·⟫ e_b`
is a continuous linear function of them. -/
theorem Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq : ∀ (P : ℕ) (μ : Measure (Euclid P)) (K : Euclid P → Submodule ℝ (Euclid P)), (∀ u : Euclid P, AEMeasurable (fun x => ‖(K x).starProjection u‖ ^ 2) μ) → AEMeasurable (fun x => (K x).starProjection) μ := by
  intro P μ K h
  -- by polarization every coefficient `x ↦ ⟪p_x u, w⟫` is a.e.-measurable
  have hcoef : ∀ u w : Euclid P,
      AEMeasurable (fun x => inner ℝ ((K x).starProjection u) w) μ := by
    intro u w
    have key : ∀ x, inner ℝ ((K x).starProjection u) w =
        (‖(K x).starProjection (u + w)‖ ^ 2 - ‖(K x).starProjection (u - w)‖ ^ 2) / 4 := by
      intro x
      have hsym : inner ℝ ((K x).starProjection u) w =
          inner ℝ ((K x).starProjection u) ((K x).starProjection w) := by
        rw [Submodule.inner_starProjection_left_eq_right,
          Submodule.inner_starProjection_left_eq_right,
          Submodule.starProjection_eq_self_iff.2 ((K x).starProjection_apply_mem w)]
      rw [hsym, map_add, map_sub, norm_add_sq_real, norm_sub_sq_real]
      ring
    simp_rw [key]
    exact ((h (u + w)).sub (h (u - w))).div_const 4
  -- `p_x = Λ (g x)`, `Λ m = ∑ m_{ab} ⟪e_a, ·⟫ e_b`, `g x = (⟪p_x e_a, e_b⟫)_{ab}`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Λ : (Fin P × Fin P → ℝ) → (Euclid P →L[ℝ] Euclid P) := fun m =>
    ∑ ab, m ab • (innerSL ℝ (e ab.1)).smulRight (e ab.2)
  have heq : (fun x => (K x).starProjection) =
      fun x => Λ fun ab => inner ℝ ((K x).starProjection (e ab.1)) (e ab.2) := by
    funext x
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [Λ, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Fintype.sum_prod_type]
    calc (K x).starProjection v = (K x).starProjection (∑ a, inner ℝ (e a) v • e a) := by
          rw [e.sum_repr']
      _ = ∑ a, inner ℝ (e a) v • (K x).starProjection (e a) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, inner ℝ (e a) v • ∑ b, inner ℝ (e b) ((K x).starProjection (e a)) • e b := by
          simp only [e.sum_repr']
      _ = _ := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [real_inner_comm (e b), smul_smul, smul_smul, mul_comm]
  -- `Λ` is continuous and `g` is a.e.-measurable coordinatewise
  have hΛ : Continuous Λ :=
    continuous_finsetSum _ fun ab _ => (continuous_apply ab).smul continuous_const
  rw [heq]
  exact hΛ.measurable.comp_aemeasurable (AEMeasurable.of_eval fun ab => hcoef _ _)
/-- For an integer multiplicity triple `R = (M, θ, ξ)` in an open set `U`, `Hⁿ⌞M` is σ-finite.
The open set `U ⊆ ℝᴾ` is σ-compact, `U = ⋃ⱼ Kⱼ` with `Kⱼ` compact.  As `θ ≥ 1` on `M`,
`Hⁿ(M ∩ Kⱼ) ≤ ∫_{M ∩ Kⱼ} θ dHⁿ < ∞`, and `M ⊆ ⋃ⱼ (M ∩ Kⱼ)`. -/
theorem Submission.dsmc_imrep_carrier_sigmaFinite : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → SigmaFinite (μHE[n].restrict R.carrier) := by
  intro P n U R hU
  -- `U` is locally compact and second countable, hence σ-compact
  obtain ⟨K, hKc, hKU⟩ : IsSigmaCompact U := by
    have := hU.locallyCompactSpace
    exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  -- `Hⁿ(M ∩ Kⱼ) ≤ ∫_{M ∩ Kⱼ} θ dHⁿ < ∞`, since `θ ≥ 1` on `M`
  have hfin : ∀ j, μHE[n] (R.carrier ∩ K j) < ∞ := by
    intro j
    calc μHE[n] (R.carrier ∩ K j) = ∫⁻ _ in R.carrier ∩ K j, 1 ∂μHE[n] :=
          (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in R.carrier ∩ K j, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' (R.measurableSet_carrier.inter (hKc j).isClosed.measurableSet)
            fun x hx => Nat.one_le_cast.mpr (R.mult_pos x hx.1)
      _ < ∞ := (R.locallyIntegrable_mult (K j) (hKc j)
          ((subset_iUnion K j).trans hKU.subset)).lt_top
  -- `M ⊆ U = ⋃ⱼ Kⱼ`, so the sets `M ∩ Kⱼ` cover `M`
  refine Poincare.SimonGMT.Chapter03.sigmaFinite_restrict_of_hausdorff_finite_cover
    (fun j => R.carrier ∩ K j) ?_ hfin
  rw [← inter_iUnion, hKU]
  exact fun x hx => ⟨hx, R.carrier_subset hx⟩
/-- The blow-up integrals `x ↦ ∫_{η_{x,r}(M)} f dHⁿ` of a continuous `f ≥ 0` are Borel
measurable when `Hⁿ⌞M` is s-finite; `M` need not be measurable.  As `η_{x,r}` is a translation
followed by the dilation by `r⁻¹`, `Hⁿ(η_{x,r}(s)) = r⁻ⁿ Hⁿ(s)` for every set `s`, so
`Hⁿ⌞η_{x,r}(M) = r⁻ⁿ (η_{x,r})_#(Hⁿ⌞M)` (on Borel `B`, `η(M) ∩ B = η(M ∩ η⁻¹B)`).  Hence the
integral is `(r⁻ⁿ ∫ f(r⁻¹(y − x)) d(Hⁿ⌞M)(y)).toReal`, measurable in `x` by Tonelli for the
s-finite `Hⁿ⌞M`. -/
theorem Submission.dsmc_measurable_blowUp_image_setIntegral : ∀ (P n : ℕ) (M : Set (Euclid P)), SFinite (μHE[n].restrict M) → ∀ f : Euclid P → ℝ, Continuous f → (∀ y, 0 ≤ f y) → ∀ r : ℝ, 0 < r → Measurable (fun x : Euclid P => ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) := by
  intro P n M hM f hf hf0 r hr
  set η : Euclid P → Euclid P → Euclid P := fun x => Poincare.SimonGMT.Chapter03.blowUpMap x r
    with hη
  -- `(x, y) ↦ η_x(y) = r⁻¹(y − x)` is continuous
  have hηc : Continuous fun p : Euclid P × Euclid P => η p.1 p.2 := by
    simp only [hη, Poincare.SimonGMT.Chapter03.blowUpMap]
    fun_prop
  have hηm : ∀ x, Measurable (η x) := fun x =>
    (hηc.comp (Continuous.prodMk continuous_const continuous_id)).measurable
  -- `Hⁿ(η_x(s)) = r⁻ⁿ Hⁿ(s)` for every set `s`
  have hscale : ∀ x (s : Set (Euclid P)), μHE[n] (η x '' s) = ‖r⁻¹‖₊ ^ n • μHE[n] s := by
    intro x s
    have himg : η x '' s = (fun y => r⁻¹ • y) '' (IsometryEquiv.subRight x '' s) := by
      rw [Set.image_image]
      rfl
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      (IsometryEquiv.subRight x).isometry.euclideanHausdorffMeasure_image]
  -- `Hⁿ⌞η_x(M) = r⁻ⁿ (η_x)_#(Hⁿ⌞M)`, checked on Borel sets
  have hrestr : ∀ x, μHE[n].restrict (η x '' M) =
      ‖r⁻¹‖₊ ^ n • (μHE[n].restrict M).map (η x) := by
    intro x
    ext B hB
    rw [Measure.restrict_apply hB, Measure.smul_apply, Measure.map_apply (hηm x) hB,
      Measure.restrict_apply (hηm x hB), Set.inter_comm, ← Set.image_inter_preimage, hscale,
      Set.inter_comm]
  -- `∫_{η_x(M)} f dHⁿ = (r⁻ⁿ ∫ f ∘ η_x d(Hⁿ⌞M)).toReal`, also when `f` is not integrable
  have hint : ∀ x, ∫ y in η x '' M, f y ∂μHE[n] =
      (‖r⁻¹‖₊ ^ n • ∫⁻ y, ENNReal.ofReal (f (η x y)) ∂(μHE[n].restrict M)).toReal := by
    intro x
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hf.aestronglyMeasurable,
      hrestr, lintegral_smul_measure, lintegral_map hf.measurable.ennreal_ofReal (hηm x)]
  -- Tonelli for the s-finite measure `Hⁿ⌞M`
  show Measurable fun x => ∫ y in η x '' M, f y ∂μHE[n]
  simp_rw [hint]
  exact ((Measurable.lintegral_prod_right'
    (f := fun p : Euclid P × Euclid P => ENNReal.ofReal (f (η p.1 p.2)))
    (ENNReal.continuous_ofReal.comp (hf.comp hηc)).measurable).const_smul _).ennreal_toReal

/-- **The approximate tangent projections of an integer multiplicity triple are measurable**
(Simon Ch. 3, 1.4; Ch. 4, 2.3).  For `R = (M, θ, ξ)` in an open `U ⊆ ℝᴾ`, `x ↦ p_{TₓM}` is
a.e.-measurable for `μ_R = θHⁿ⌞M`.  As `μ_R ≪ ν = Hⁿ⌞M`, it suffices to treat `ν`, which is
σ-finite.  If `n = 0`, every candidate plane is `{0}`.  If `n ≥ 1`, `TₓM` is an approximate tangent
plane at `ν`-a.e. `x`, so for `f_u(y) = max(1 − |y|², 0)⟨u, y⟩²` the blow-up integrals
`∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ`, which are Borel in `x`, converge `ν`-a.e. to
`∫_{TₓM} f_u dHⁿ = c|p_x u|²`.  Hence each `x ↦ |p_x u|²`, and so `x ↦ p_x`, is
`ν`-a.e.-measurable. -/
theorem Submission.dsmc_approxTangentPlane_starProjection_aemeasurable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), IsOpen U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure := by
  intro P n U R hU
  -- `μ_R = θHⁿ⌞M ≪ Hⁿ⌞M`, so it suffices to work with `ν = Hⁿ⌞M`
  refine AEMeasurable.mono_ac ?_ (withDensity_absolutelyContinuous _ _)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- `n = 0`: every candidate plane is `0`-dimensional, so `p_x = 0` for every `x`
    have h0 : ∀ x, (approxTangentPlane 0 R.carrier x).starProjection = 0 := by
      intro x
      have hK : approxTangentPlane 0 R.carrier x = ⊥ := by
        rw [approxTangentPlane]
        split_ifs with h
        · exact Submodule.finrank_eq_zero.1 h.choose_spec.1
        · rfl
      refine ContinuousLinearMap.ext fun v => ?_
      exact (Submodule.mem_bot ℝ).1
        (hK.le ((approxTangentPlane 0 R.carrier x).starProjection_apply_mem v))
    simp only [h0]
    exact aemeasurable_const
  have : SigmaFinite ((μHE[n] : Measure (Euclid P)).restrict R.carrier) :=
    Submission.dsmc_imrep_carrier_sigmaFinite P n U R hU
  obtain ⟨c, hc, hcQ⟩ := Submission.exists_plane_cutoff_quadratic_moment_eq n hn
  -- `TₓM` is an approximate tangent plane of `M` at `ν`-a.e. `x`
  have hT : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      HasApproximateTangentSpaceAt n R.carrier x (approxTangentPlane n R.carrier x) := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, hQ, -⟩ := hx
    have h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q := ⟨Q, hQ⟩
    rw [approxTangentPlane, dite_eq_left h]
    exact h.choose_spec
  refine Submission.aemeasurable_starProjection_of_aemeasurable_norm_sq P _ _ fun u => ?_
  -- the test function `f_u(y) = max(1 − |y|², 0)⟨u, y⟩² ∈ C_c(ℝᴾ)`
  let f : Euclid P → ℝ := fun y => max (1 - ‖y‖ ^ 2) 0 * inner ℝ u y ^ 2
  have hf : Continuous f := by fun_prop
  have hf0 : ∀ y, 0 ≤ f y := fun y => mul_nonneg (le_max_right _ _) (sq_nonneg _)
  have hfc : HasCompactSupport f := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) 1) fun y hy => ?_
    have h1 : 1 < ‖y‖ := by simpa using hy
    have h2 : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith
    simp [f, max_eq_right h2]
  let F : CompactlySupportedContinuousMap (Euclid P) ℝ := ⟨⟨f, hf⟩, hfc⟩
  -- the scales `1/(k+1) ↓ 0`
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => mem_Ioi.2 (by positivity)⟩
  -- the blow-up integrals `Φₖ(x) = ∫_{η_{x,1/(k+1)}(M)} f_u dHⁿ` are Borel functions of `x`
  let Φ : ℕ → Euclid P → ℝ := fun k x =>
    ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x (1 / ((k : ℝ) + 1)) '' R.carrier, f y ∂μHE[n]
  have hΦ : ∀ k, Measurable (Φ k) := fun k =>
    Submission.dsmc_measurable_blowUp_image_setIntegral P n R.carrier inferInstance f hf hf0 _
      (by positivity)
  -- at `ν`-a.e. `x` they converge to `∫_{TₓM} f_u dHⁿ = c|p_x u|²`
  have hlim : ∀ᵐ x ∂(μHE[n].restrict R.carrier), Tendsto (fun k => Φ k x) atTop
      (𝓝 (c * ‖(approxTangentPlane n R.carrier x).starProjection u‖ ^ 2)) := by
    filter_upwards [hT] with x hx
    rw [← hcQ P _ hx.1 u]
    exact (hx.2 F).comp hr
  refine ((aemeasurable_of_tendsto_metrizable_ae' (fun k => (hΦ k).aemeasurable) hlim).const_mul
    c⁻¹).congr (Eventually.of_forall fun x => ?_)
  exact inv_mul_cancel_left₀ hc.ne' _
/-- **Integrating factor for the monotonicity identity** (Simon Ch. 4, 3.16–3.17).  If `I` is
continuous on `(0, r]`, has derivative `I'` on `(0, r)` and `n I(s) − s I'(s) ≤ κ s I(s)` there,
then `s ↦ e^{κs} s⁻ⁿ I(s)` is nondecreasing on `(0, r]`.  On `(0, r]` this function equals
`G(s) = exp(κs − n log s) I(s)`, and `G'(s) = exp(κs − n log s) s⁻¹ (κ s I(s) − (n I(s) − s I'(s)))
≥ 0` on `(0, r)`, so the mean value theorem applies. -/
theorem Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq : ∀ (n : ℕ) (κ r : ℝ) (I I' : ℝ → ℝ), ContinuousOn I (Ioc 0 r) → (∀ s ∈ Ioo 0 r, HasDerivAt I (I' s) s) → (∀ s ∈ Ioo 0 r, (n : ℝ) * I s - s * I' s ≤ κ * s * I s) → MonotoneOn (fun s => Real.exp (κ * s) / s ^ n * I s) (Ioc 0 r) := by
  intro n κ r I I' hIc hId hineq
  -- on `(0, r]`, `e^{κs}/sⁿ · I(s) = G(s) := exp(κs − n log s) · I(s)`
  refine MonotoneOn.congr (f₁ := fun s => Real.exp (κ * s - n * Real.log s) * I s) ?_ ?_
  swap
  · intro s hs
    simp only [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hs.1]
  -- `G` is continuous on `(0, r]`
  have hGc : ContinuousOn (fun s => Real.exp (κ * s - n * Real.log s) * I s) (Ioc 0 r) := by
    refine ContinuousOn.mul (Real.continuous_exp.comp_continuousOn ?_) hIc
    exact (continuousOn_const.mul continuousOn_id).sub
      (continuousOn_const.mul (Real.continuousOn_log.mono fun s hs => hs.1.ne'))
  -- `G' = exp(κs − n log s) · ((κ − n/s) I + I') ≥ 0` on `(0, r)`; mean value theorem
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 r) hGc
    (f' := fun s => Real.exp (κ * s - n * Real.log s) * ((κ - n * s⁻¹) * I s + I' s)) ?_ ?_
  · intro s hs
    rw [interior_Ioc] at hs
    have h1 : HasDerivAt (fun s => κ * s - n * Real.log s) (κ * 1 - n * s⁻¹) s :=
      ((hasDerivAt_id' s).const_mul κ).sub ((Real.hasDerivAt_log hs.1.ne').const_mul (n : ℝ))
    exact ((h1.exp.mul (hId s hs)).congr_deriv (by ring)).hasDerivWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    have key : (κ - n * s⁻¹) * I s + I' s = s⁻¹ * (κ * s * I s - (n * I s - s * I' s)) := by
      linear_combination (-(κ * I s + I' s)) * mul_inv_cancel₀ hs.1.ne'
    rw [key]
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (inv_nonneg.mpr hs.1.le) (sub_nonneg.mpr (hineq s hs)))
/-- **Differentiation of radial cutoff integrals** (Simon Ch. 4, 3.3–3.4, where
`I(ρ) = ∫ φ(r/ρ) dμ` is differentiated in `ρ`; here the cutoff is written in the squared ratio
`|x - z|²/t²`).  If `μ(B_r(z)) < ∞` and `η` is `C¹` with `η = 0` on `[1, ∞)`, then
`I(t) = ∫ η(|x - z|²/t²) dμ` is continuous on `(0, r]` and, for `0 < s < r`,
`I'(s) = -(∫ 2 (|x - z|²/s²) η'(|x - z|²/s²) dμ)/s` (dominated convergence and differentiation
under the integral sign). -/
theorem Submission.dsmc_em_cutoff_integral_hasDerivAt : ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), μ (ball z r) < ∞ → ContDiff ℝ 1 η → (∀ u, 1 ≤ u → η u = 0) → ContinuousOn (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (Ioc 0 r) ∧ ∀ s ∈ Ioo 0 r, HasDerivAt (fun t => ∫ x, η (‖x - z‖ ^ 2 / t ^ 2) ∂μ) (-(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s) s := by
  intro P μ z r η hμ hη hη1
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  -- `η' = deriv η` vanishes on `(1, ∞)` (where `η` is locally zero), hence on `[1, ∞)`.
  have hη'1 : ∀ u, 1 ≤ u → deriv η u = 0 := by
    have hIoi : Ioi (1 : ℝ) ⊆ {u | deriv η u = 0} := fun u hu => by
      have hloc : η =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hu] with v hv
        exact hη1 v (le_of_lt hv)
      show deriv η u = 0
      rw [hloc.deriv_eq, deriv_const]
    have hIci : Ici (1 : ℝ) ⊆ {u | deriv η u = 0} := by
      rw [← closure_Ioi]
      exact closure_minimal hIoi (isClosed_eq hη'c continuous_const)
    exact fun u hu => hIci hu
  -- Bounds on `[0, 1]` for `η` and for `u ↦ 2 u η'(u)`.
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hηc.continuousOn
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    (f := fun u : ℝ => 2 * u * deriv η u) (by fun_prop)
  have hg1 : ∀ u, 1 ≤ u → 2 * u * deriv η u = 0 := fun u hu => by
    rw [hη'1 u hu, mul_zero]
  -- For `0 < t ≤ r`, `g(|x - z|²/t²)` vanishes off `B_t(z) ⊆ B_r(z)` and is dominated there.
  have hdom : ∀ (g : ℝ → ℝ) (B : ℝ), (∀ u, 1 ≤ u → g u = 0) → (∀ u ∈ Icc (0 : ℝ) 1, ‖g u‖ ≤ B) →
      ∀ t, 0 < t → t ≤ r → ∀ x : Euclid P,
        ‖g (‖x - z‖ ^ 2 / t ^ 2)‖ ≤ (ball z r).indicator (fun _ => B) x := by
    intro g B hg0 hgB t ht htr x
    have hB : 0 ≤ B := (norm_nonneg _).trans (hgB 0 ⟨le_rfl, zero_le_one⟩)
    by_cases hx : ‖x - z‖ < t
    · have hxr : x ∈ ball z r := by
        rw [mem_ball, dist_eq_norm]
        exact hx.trans_le htr
      rw [indicator_of_mem hxr]
      apply hgB
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    · rw [not_lt] at hx
      rw [hg0 _ ?_, norm_zero]
      · exact indicator_nonneg (fun _ _ => hB) x
      · rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ ht.le hx 2
  have hint : ∀ c : ℝ, Integrable ((ball z r).indicator (fun _ => c)) μ := fun c =>
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  have hcont : ∀ t : ℝ, Continuous fun x : Euclid P => η (‖x - z‖ ^ 2 / t ^ 2) := fun t => by
    fun_prop
  -- Pointwise derivative in `t ≠ 0`.
  have hderiv : ∀ x : Euclid P, ∀ t : ℝ, t ≠ 0 →
      HasDerivAt (fun t => η (‖x - z‖ ^ 2 / t ^ 2))
        (-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t) t := by
    intro x t ht
    have h1 := (hasDerivAt_const t (‖x - z‖ ^ 2)).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht)
    have h2 := (hη.differentiable one_ne_zero (‖x - z‖ ^ 2 / t ^ 2)).hasDerivAt.comp t h1
    refine h2.congr_deriv ?_
    field_simp
    ring
  refine ⟨?_, fun s hs => ?_⟩
  · -- (i) continuity on `(0, r]` by dominated convergence
    refine continuousOn_of_dominated (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (bound := (ball z r).indicator (fun _ => C)) (fun t _ => (hcont t).aestronglyMeasurable)
      (fun t ht => Eventually.of_forall (hdom η C hη1 hC t ht.1 ht.2)) (hint C)
      (Eventually.of_forall fun x t ht => (hderiv x t ht.1.ne').continuousAt.continuousWithinAt)
  · -- (ii) differentiation under the integral sign on `(s/2, r)`
    have hs0 : 0 < s := hs.1
    have hb : ∀ x : Euclid P, ∀ t ∈ Ioo (s / 2) r,
        ‖-(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t‖ ≤
          (ball z r).indicator (fun _ => K) x / (s / 2) := by
      intro x t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h1 : ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ ≤
          (ball z r).indicator (fun _ => K) x :=
        hdom (fun u => 2 * u * deriv η u) K hg1 hK t ht0 ht.2.le x
      have h2 : 0 ≤ (ball z r).indicator (fun _ => K) x := (norm_nonneg _).trans h1
      rw [norm_div, norm_neg, Real.norm_of_nonneg ht0.le]
      calc ‖2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)‖ / t
          ≤ (ball z r).indicator (fun _ => K) x / t := by gcongr
        _ ≤ (ball z r).indicator (fun _ => K) x / (s / 2) := by
          gcongr
          exact ht.1.le
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := s)
      (F := fun t x => η (‖x - z‖ ^ 2 / t ^ 2))
      (F' := fun t x => -(2 * (‖x - z‖ ^ 2 / t ^ 2) * deriv η (‖x - z‖ ^ 2 / t ^ 2)) / t)
      (bound := fun x => (ball z r).indicator (fun _ => K) x / (s / 2))
      (Ioo_mem_nhds (by linarith) hs.2)
      (Eventually.of_forall fun t => (hcont t).aestronglyMeasurable)
      ((hint C).mono' (hcont s).aestronglyMeasurable
        (Eventually.of_forall (hdom η C hη1 hC s hs0 hs.2.le)))
      (by fun_prop : Continuous fun x : Euclid P =>
        -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s).aestronglyMeasurable
      (Eventually.of_forall hb) ((hint K).div_const (s / 2))
      (Eventually.of_forall fun x t ht => hderiv x t (by linarith [ht.1] : 0 < t).ne')
    have hval : ∫ x, -(2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) / s ∂μ =
        -(∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ) / s := by
      rw [integral_div, integral_neg]
    rw [← hval]
    exact key.2
/-- **Radial first-variation inequality** (Simon Ch. 4, 3.2–3.3 with the bounded generalized mean
curvature of 3.14–3.16).  Test the first variation of `v(M, θ)` with the radial field
`X(x) = η(u(x)) (x - z)`, `u(x) = ‖x - z‖² / s²`, where `η ≥ 0` is `C¹`, nonincreasing and vanishes
on `[1, ∞)`.  Then `μ`-a.e. `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)`, and
`|X · H| ≤ κ s η(u)`, so `n ∫ η(u) dμ + ∫ 2 u η'(u) dμ ≤ ∫ div_M X dμ = -∫ X · H dμ ≤ κ s ∫ η(u) dμ`. -/
theorem Submission.dsmc_em_cutoff_first_variation_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ) (η : ℝ → ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ContDiff ℝ 1 η → (∀ u, 0 ≤ η u) → (∀ u, deriv η u ≤ 0) → (∀ u, 1 ≤ u → η u = 0) → ∀ s : ℝ, 0 < s → s < r → (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure + ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂R.measure := by
  intro P n U R H κ z r η hzU hPm hHκ hfv hη hη0 hη'0 hη1 s hs hsr
  classical
  set μ : Measure (Euclid P) := R.measure with hμ
  /- Step 0.  `κ ≥ 0`; `μ(B̄_s(z)) < ∞`; `η' = deriv η` is continuous and vanishes on `(1, ∞)`;
  `η` and `η'` are bounded on `[0, 1]`. -/
  have hκ0 : 0 ≤ κ := (norm_nonneg _).trans (hHκ 0)
  have hBc : IsCompact (closedBall z s) := isCompact_closedBall z s
  have hBm : MeasurableSet (closedBall z s) := measurableSet_closedBall
  have hBU : closedBall z s ⊆ U := (closedBall_subset_closedBall hsr.le).trans hzU
  have hBr : closedBall z s ⊆ ball z r := closedBall_subset_ball hsr
  have hμB : μ (closedBall z s) < ∞ := by
    rw [hμ, IMRep.measure, withDensity_apply _ hBm, Measure.restrict_restrict hBm, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ hBc hBU)
  have hind : ∀ c : ℝ, Integrable ((closedBall z s).indicator fun _ => c) μ := fun c =>
    (integrable_indicator_iff hBm).mpr (integrableOn_const hμB.ne)
  have hηd : ∀ u, HasDerivAt η (deriv η u) u := fun u =>
    ((hη.differentiable (by norm_num)) u).hasDerivAt
  have hηc : Continuous η := hη.continuous
  have hη'c : Continuous (deriv η) := hη.continuous_deriv le_rfl
  have hη'1 : ∀ u, 1 < u → deriv η u = 0 := by
    intro u hu
    have : η =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hu] with v hv
      exact hη1 v hv.le
    rw [this.deriv_eq]
    simp
  obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Icc (0 : ℝ) 1, ‖η u‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hηc.continuousOn
  obtain ⟨M, hM⟩ : ∃ M, ∀ u ∈ Icc (0 : ℝ) 1, ‖deriv η u‖ ≤ M :=
    isCompact_Icc.exists_bound_of_continuousOn hη'c.continuousOn
  -- the radius ratio `u(x) = ‖x - z‖² / s²`
  have hucont : Continuous fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2 := by fun_prop
  have hu0 : ∀ x : Euclid P, 0 ≤ ‖x - z‖ ^ 2 / s ^ 2 := fun x => by positivity
  have hu_le : ∀ x ∈ closedBall z s, ‖x - z‖ ^ 2 / s ^ 2 ≤ 1 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [div_le_one (pow_pos hs 2)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hu_gt : ∀ x, x ∉ closedBall z s → 1 < ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    rw [one_lt_div (pow_pos hs 2)]
    exact pow_lt_pow_left₀ hx hs.le two_ne_zero
  -- the two integrands vanish off `B̄_s(z)` and are bounded on it
  have hFint : Integrable (fun x => η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind C) (hηc.comp hucont).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · rw [indicator_of_mem hx]
      exact hC _ ⟨hu0 x, hu_le x hx⟩
    · rw [indicator_of_notMem hx, hη1 _ (hu_gt x hx).le, norm_zero]
  have hGint : Integrable
      (fun x => 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) μ := by
    refine Integrable.mono' (hind (2 * M))
      ((continuous_const.mul hucont).mul (hη'c.comp hucont)).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ closedBall z s
    · have h1 := hu_le x hx
      have h2 := hM _ ⟨hu0 x, h1⟩
      rw [Real.norm_eq_abs] at h2
      rw [indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_mul, abs_two,
        abs_of_nonneg (hu0 x)]
      calc 2 * (‖x - z‖ ^ 2 / s ^ 2) * |deriv η (‖x - z‖ ^ 2 / s ^ 2)| ≤ 2 * 1 * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 zero_le_two) h2 (abs_nonneg _)
              (by norm_num)
        _ = 2 * M := by ring
    · rw [indicator_of_notMem hx, hη'1 _ (hu_gt x hx), mul_zero, norm_zero]
  /- Step 1.  The radial field `X(x) = η(u(x)) (x - z)` is `C¹`, with
  `DX(x) v = η(u) v + η'(u) (2/s²) ⟪x - z, v⟫ (x - z)` and `tsupport X ⊆ B̄_s(z) ⊆ B_r(z)`. -/
  let X : Euclid P → Euclid P := fun x => η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)
  have hXd : ∀ x, HasFDerivAt X
      (η (‖x - z‖ ^ 2 / s ^ 2) • ContinuousLinearMap.id ℝ (Euclid P) +
        ((deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2)) • innerSL ℝ (x - z)).smulRight
          (x - z)) x := by
    intro x
    have h1 : HasFDerivAt (fun x : Euclid P => x - z) (ContinuousLinearMap.id ℝ _) x :=
      (hasFDerivAt_id x).sub_const z
    have h3 : HasFDerivAt (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2)
        ((s ^ 2)⁻¹ • (2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (Euclid P)))) x := by
      simpa only [div_eq_mul_inv] using HasFDerivAt.mul_const h1.norm_sq (s ^ 2)⁻¹
    have h5 := ((hηd (‖x - z‖ ^ 2 / s ^ 2)).comp_hasFDerivAt x h3).smul h1
    refine HasFDerivAt.congr_fderiv (f := X) h5 (ContinuousLinearMap.ext fun v => ?_)
    simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      ContinuousLinearMap.comp_apply, Function.comp_apply, smul_eq_mul]
    congr 2
    rw [nsmul_eq_mul]
    push_cast
    ring
  have hXcd : ContDiff ℝ 1 X := by
    have h1 : ContDiff ℝ 1 (fun x : Euclid P => ‖x - z‖ ^ 2 / s ^ 2) :=
      ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).div_const _
    exact (hη.comp h1).smul (contDiff_id.sub contDiff_const)
  have hXzero : ∀ x, x ∉ closedBall z s → X x = 0 := by
    intro x hx
    show η (‖x - z‖ ^ 2 / s ^ 2) • (x - z) = 0
    rw [hη1 _ (hu_gt x hx).le, zero_smul]
  have hXts : tsupport X ⊆ closedBall z s := by
    refine closure_minimal (fun x hx => ?_) isClosed_closedBall
    by_contra h
    exact hx (hXzero x h)
  have hXcs : HasCompactSupport X := HasCompactSupport.intro hBc hXzero
  /- Step 2.  `μ`-a.e. the tangent projection is `∑ᵢ τᵢ ⟪τᵢ, ·⟫` for an orthonormal family `τ`
  of size `n` (`R.orients` and uniqueness of approximate tangent spaces). -/
  have hproj : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      (Submodule.span ℝ (range τ)).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    intro τ hτ
    let b0 := Module.Basis.span hτ.linearIndependent
    have hb0 : ∀ i, (b0 i : Euclid P) = τ i := fun i =>
      congrArg Subtype.val (Module.Basis.span_apply hτ.linearIndependent i)
    have hb0o : Orthonormal ℝ b0 := by
      have e : (Submodule.span ℝ (range τ)).subtypeₗᵢ ∘ b0 = τ := funext hb0
      rw [← (Submodule.span ℝ (range τ)).subtypeₗᵢ.orthonormal_comp_iff, e]
      exact hτ
    rw [OrthonormalBasis.starProjection_eq_sum_rankOne (b0.toOrthonormalBasis hb0o),
      Module.Basis.coe_toOrthonormalBasis]
    simp only [hb0]
  have hμac : μ ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hPae : ∀ᵐ x ∂μ, ∃ τ : Fin n → Euclid P, Orthonormal ℝ τ ∧
      (approxTangentPlane n R.carrier x).starProjection =
        ∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) := by
    refine hμac.ae_le ?_
    filter_upwards [R.orients] with x ⟨Q, hQ, τ, hτ, hspan, _⟩
    have hex : ∃ Q', HasApproximateTangentSpaceAt n R.carrier x Q' := ⟨Q, hQ⟩
    have happrox : approxTangentPlane n R.carrier x = Q := by
      rw [approxTangentPlane, dite_eq_left hex]
      exact hex.choose_spec.unique hQ
    exact ⟨τ, hτ, by rw [happrox, ← hspan, hproj τ hτ]⟩
  /- Step 3.  `div_M X = n η(u) + η'(u) (2/s²) ∑ᵢ ⟪τᵢ, x - z⟫²`, and by Bessel's inequality and
  `η' ≤ 0`, `n η(u) + 2 u η'(u) ≤ div_M X ≤ n η(u)` `μ`-a.e. -/
  let d : Euclid P → ℝ := fun x => tangentialDivergence n R.carrier X x
  -- `trace ((∑ τᵢ ⊗ τᵢ) ∘ L) = ∑ ⟪τᵢ, L τᵢ⟫`
  have htr : ∀ (τ : Fin n → Euclid P) (L : Euclid P →L[ℝ] Euclid P),
      LinearMap.trace ℝ (Euclid P) ((∑ i, InnerProductSpace.rankOne ℝ (τ i) (τ i) :
        Euclid P →L[ℝ] Euclid P).toLinearMap ∘ₗ L.toLinearMap) =
        ∑ i, inner ℝ (τ i) (L (τ i)) := by
    intro τ L
    rw [← ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.finsetSum_comp,
      ContinuousLinearMap.toLinearMap_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp, InnerProductSpace.comp_rankOne,
      InnerProductSpace.trace_rankOne]
  -- Bessel's inequality
  have hbessel : ∀ (τ : Fin n → Euclid P), Orthonormal ℝ τ → ∀ v : Euclid P,
      ∑ i, inner ℝ (τ i) v ^ 2 ≤ ‖v‖ ^ 2 := by
    intro τ hτ v
    have := hτ.sum_inner_products_le (s := Finset.univ) (x := v)
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hdae : ∀ᵐ x ∂μ,
      n * η (‖x - z‖ ^ 2 / s ^ 2) + 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ≤
        d x ∧ d x ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) := by
    filter_upwards [hPae] with x ⟨τ, hτ, hPx⟩
    have h1 : ∀ i, inner ℝ (τ i) (τ i) = (1 : ℝ) := fun i => by
      rw [real_inner_self_eq_norm_sq, hτ.1 i, one_pow]
    have e : d x = n * η (‖x - z‖ ^ 2 / s ^ 2) + deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) *
        ∑ i, inner ℝ (τ i) (x - z) ^ 2 := by
      show tangentialDivergence n R.carrier X x = _
      unfold tangentialDivergence
      rw [hPx, (hXd x).fderiv, htr]
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, inner_add_right,
        inner_smul_right, h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm (x - z) (τ i)]
      ring
    have hb := hbessel τ hτ (x - z)
    have hS0 : 0 ≤ ∑ i, inner ℝ (τ i) (x - z) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hk : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hη'0 _) (div_nonneg zero_le_two (sq_nonneg s))
    have h2 := mul_le_mul_of_nonpos_left hb hk
    have h3 := mul_nonpos_of_nonpos_of_nonneg hk hS0
    have e2 : deriv η (‖x - z‖ ^ 2 / s ^ 2) * (2 / s ^ 2) * ‖x - z‖ ^ 2 =
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) := by ring
    rw [e]
    exact ⟨e2 ▸ add_le_add le_rfl h2, add_le_of_nonpos_right h3⟩
  /- Step 4.  `div_M X` is `μ`-integrable: it is `AEStronglyMeasurable` (the tangent projection
  is `μ`-measurable, `DX` is continuous, `(A, B) ↦ trace (A ∘ B)` is continuous) and
  `|div_M X| ≤ n η(u) + |2 u η'(u)|` `μ`-a.e. -/
  have hTc : Continuous fun p : (Euclid P →L[ℝ] Euclid P) × (Euclid P →L[ℝ] Euclid P) =>
      LinearMap.trace ℝ (Euclid P) (p.1.toLinearMap ∘ₗ p.2.toLinearMap) := by
    have h1 : Continuous fun A : Euclid P →L[ℝ] Euclid P =>
        LinearMap.trace ℝ (Euclid P) A.toLinearMap :=
      ((LinearMap.trace ℝ (Euclid P)).comp
        (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
    exact h1.comp (continuous_fst.clm_comp continuous_snd)
  have hPmeas : AEStronglyMeasurable
      (fun x => (approxTangentPlane n R.carrier x).starProjection) μ := hPm.aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable d μ := by
    have h3 := hTc.comp_aestronglyMeasurable
      (hPmeas.prodMk (hXcd.continuous_fderiv one_ne_zero).aestronglyMeasurable)
    show AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) μ
    unfold tangentialDivergence
    exact h3
  have hdint : Integrable d μ := by
    refine Integrable.mono' ((hFint.const_mul n).add hGint.abs) hdmeas ?_
    filter_upwards [hdae] with x hx
    have h0 : 0 ≤ (n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) := mul_nonneg (Nat.cast_nonneg n) (hη0 _)
    have hG1 := neg_abs_le (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    have hG2 := abs_nonneg (2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2))
    show ‖d x‖ ≤ n * η (‖x - z‖ ^ 2 / s ^ 2) +
      |2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)|
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  /- Step 5.  `∫ f dμ = ∫_M θ f dHⁿ`, so `∫ div_M X dμ = R.firstVariation X`. -/
  have hμint : ∀ f : Euclid P → ℝ,
      ∫ x, f x ∂μ = ∫ x in R.carrier, (R.mult x : ℝ) * f x ∂μHE[n] := by
    intro f
    have hθ : (fun x => (R.mult x : ℝ≥0∞)) = fun x => ((R.mult x : NNReal) : ℝ≥0∞) := by
      funext x
      simp
    have hθm : Measurable fun x => (R.mult x : NNReal) :=
      measurable_from_top.comp R.measurable_mult
    rw [hμ, IMRep.measure, hθ, integral_withDensity_eq_integral_smul hθm]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [NNReal.smul_def]
  /- Step 6.  Integrate: `n ∫ η(u) + ∫ 2 u η'(u) ≤ ∫ div_M X = -∫ X · H ≤ κ s ∫ η(u)`, using
  `|X · H| ≤ ‖X‖ κ ≤ κ s η(u)` (`X = 0` off `B̄_s(z)`). -/
  have e1 : (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
      ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ =
      ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ := by
    rw [integral_add (hFint.const_mul _) hGint, integral_const_mul]
  have e3 : ∫ x, ((n : ℝ) * η (‖x - z‖ ^ 2 / s ^ 2) +
        2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2)) ∂μ ≤ ∫ x, d x ∂μ := by
    refine integral_mono_ae ((hFint.const_mul _).add hGint) hdint ?_
    filter_upwards [hdae] with x hx
    exact hx.1
  have e4 : ∫ x, d x ∂μ = -∫ x, inner ℝ (X x) (H x) ∂μ := by
    rw [hμint]
    exact hfv X hXcd hXcs (hXts.trans hBr)
  have e5 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ κ * s * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
    have h1 : -∫ x, inner ℝ (X x) (H x) ∂μ ≤ ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ := by
      refine (neg_le_abs _).trans ?_
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    have h2 : ∫ x, ‖inner ℝ (X x) (H x)‖ ∂μ ≤ ∫ x, κ * s * η (‖x - z‖ ^ 2 / s ^ 2) ∂μ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _) (hFint.const_mul _)
        (ae_of_all _ fun x => ?_)
      show ‖inner ℝ (X x) (H x)‖ ≤ κ * s * η (‖x - z‖ ^ 2 / s ^ 2)
      by_cases hx : x ∈ closedBall z s
      · have hXn : ‖X x‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s := by
          show ‖η (‖x - z‖ ^ 2 / s ^ 2) • (x - z)‖ ≤ η (‖x - z‖ ^ 2 / s ^ 2) * s
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη0 _)]
          exact mul_le_mul_of_nonneg_left (by rwa [mem_closedBall, dist_eq_norm] at hx) (hη0 _)
        calc ‖inner ℝ (X x) (H x)‖ ≤ ‖X x‖ * ‖H x‖ := norm_inner_le_norm _ _
          _ ≤ (η (‖x - z‖ ^ 2 / s ^ 2) * s) * κ :=
            mul_le_mul hXn (hHκ x) (norm_nonneg _) (mul_nonneg (hη0 _) hs.le)
          _ = κ * s * η (‖x - z‖ ^ 2 / s ^ 2) := by ring
      · rw [hXzero x hx, inner_zero_left, norm_zero]
        exact mul_nonneg (mul_nonneg hκ0 hs.le) (hη0 _)
    rw [integral_const_mul] at h2
    exact h1.trans h2
  calc (n : ℝ) * ∫ x, η (‖x - z‖ ^ 2 / s ^ 2) ∂μ +
        ∫ x, 2 * (‖x - z‖ ^ 2 / s ^ 2) * deriv η (‖x - z‖ ^ 2 / s ^ 2) ∂μ = _ := e1
    _ ≤ _ := e3
    _ = _ := e4
    _ ≤ _ := e5
/-- **Radial cutoffs for the monotonicity formula** (Simon Ch. 4, 3.1–3.4).  With
`g = Real.smoothTransition` and `ηⱼ(u) = g((j + 2)(1 − u))`, every `ηⱼ` is `C¹`, nonnegative and
nonincreasing, vanishes for `u ≥ 1`, and `ηⱼ(|x − z|²/s²)` increases to the indicator of the
open ball `B_s(z)`; by dominated convergence `∫ ηⱼ(|x − z|²/s²) dμ → μ(B_s(z))` whenever
`μ(B_s(z)) < ∞`. -/
theorem Submission.dsmc_em_cutoff_tendsto_ball : ∃ η : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (η j)) ∧ (∀ j u, 0 ≤ η j u) ∧ (∀ j u, deriv (η j) u ≤ 0) ∧ (∀ j u, 1 ≤ u → η j u = 0) ∧ ∀ (P : ℕ) (μ : Measure (Euclid P)) (z : Euclid P) (s : ℝ), 0 < s → μ (ball z s) < ∞ → Tendsto (fun j => ∫ x, η j (‖x - z‖ ^ 2 / s ^ 2) ∂μ) atTop (𝓝 (μ.real (ball z s))) := by
  -- Steps 1–5: `ηⱼ(u) = g((j + 2)(1 − u))` is `C¹`, `≥ 0`, antitone, and `0` for `u ≥ 1`.
  have hanti : ∀ j : ℕ, Antitone fun u : ℝ => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) := by
    intro j a b hab
    apply Real.smoothTransition.monotone
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  have hzero : ∀ (j : ℕ) (u : ℝ), 1 ≤ u →
      Real.smoothTransition (((j : ℝ) + 2) * (1 - u)) = 0 := by
    intro j u hu
    apply Real.smoothTransition.zero_of_nonpos
    have hj : (0 : ℝ) ≤ (j : ℝ) + 2 := by positivity
    nlinarith
  refine ⟨fun j u => Real.smoothTransition (((j : ℝ) + 2) * (1 - u)), fun j => ?_,
    fun j u => Real.smoothTransition.nonneg _, fun j u => (hanti j).deriv_nonpos, hzero, ?_⟩
  · exact Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))
  -- Step 6: dominated convergence with the bound `1_{B_s(z)}`.
  intro P μ z s hs hμ
  have hs2 : 0 < s ^ 2 := by positivity
  -- `|x − z|²/s² < 1` exactly on the open ball
  have hlt : ∀ x : Euclid P, x ∈ ball z s → ‖x - z‖ ^ 2 / s ^ 2 < 1 := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    rw [div_lt_one hs2]
    exact pow_lt_pow_left₀ hx (norm_nonneg _) two_ne_zero
  have hge : ∀ x : Euclid P, x ∉ ball z s → 1 ≤ ‖x - z‖ ^ 2 / s ^ 2 := by
    intro x hx
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    rw [one_le_div hs2]
    exact pow_le_pow_left₀ hs.le hx 2
  have hint : Integrable ((ball z s).indicator (1 : Euclid P → ℝ)) μ :=
    (integrable_indicator_iff measurableSet_ball).2 (integrableOn_const hμ.ne)
  rw [← integral_indicator_one measurableSet_ball]
  refine tendsto_integral_of_dominated_convergence ((ball z s).indicator 1)
    (F := fun (j : ℕ) (x : Euclid P) =>
      Real.smoothTransition (((j : ℝ) + 2) * (1 - ‖x - z‖ ^ 2 / s ^ 2)))
    (fun j => ?_) hint (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · -- (a) each integrand is continuous
    exact (Real.smoothTransition.continuous.comp (by fun_prop)).aestronglyMeasurable
  · -- (a) `|ηⱼ(u(x))| ≤ 1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply, Real.norm_eq_abs,
        abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    · rw [indicator_of_notMem hx, hzero j _ (hge x hx), norm_zero]
  · -- (b) pointwise convergence to `1_{B_s(z)}(x)`
    by_cases hx : x ∈ ball z s
    · rw [indicator_of_mem hx, Pi.one_apply]
      have hpos : 0 < 1 - ‖x - z‖ ^ 2 / s ^ 2 := sub_pos.2 (hlt x hx)
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / (1 - ‖x - z‖ ^ 2 / s ^ 2))
      rw [div_le_iff₀ hpos] at hN
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun j hj => ?_⟩)
      have hj : (N : ℝ) ≤ j := by exact_mod_cast hj
      refine (Real.smoothTransition.one_of_one_le ?_).symm
      nlinarith
    · rw [indicator_of_notMem hx]
      exact tendsto_const_nhds.congr fun j => (hzero j _ (hge x hx)).symm

/-- **Monotonicity of `e^{κρ} ρ⁻ⁿ μ_R(B_ρ(z))` under bounded generalized mean curvature**
(Simon Ch. 4, 3.14–3.17).  If `δV(X) = -∫ X · H dμ_R` for `C¹` fields `X` supported in `B_r(z)`,
`B̄_r(z) ⊆ U` and `|H| ≤ κ`, then `e^{κs} s⁻ⁿ μ_R(B_s(z))` is nondecreasing on `(0, r]`.  For each
radial cutoff `ηⱼ`, `I(s) = ∫ ηⱼ(|x - z|²/s²) dμ_R` satisfies `n I - s I' ≤ κ s I` on `(0, r)`, so
`e^{κs} s⁻ⁿ I(s)` is nondecreasing; letting `j → ∞` gives `I(s) → μ_R(B_s(z))`. -/
theorem Submission.dsmc_exp_ball_mass_monotone : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (H : Euclid P → Euclid P) (κ : ℝ) (z : Euclid P) (r : ℝ), closedBall z r ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → AEStronglyMeasurable H R.measure → (∀ x, ‖H x‖ ≤ κ) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball z r → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure) → ∀ σ ρ : ℝ, 0 < σ → σ ≤ ρ → ρ ≤ r → ENNReal.ofReal (Real.exp (κ * σ) / σ ^ n) * R.measure (ball z σ) ≤ ENNReal.ofReal (Real.exp (κ * ρ) / ρ ^ n) * R.measure (ball z ρ) := by
  intro P n U R H κ z r hzU hPm _ hHκ hfv σ ρ hσ hσρ hρr
  have hρ : 0 < ρ := hσ.trans_le hσρ
  -- (a) `μ(B̄_r(z)) < ∞` (`R.locallyIntegrable_mult`), so `μ(B_t(z)) < ∞` for `t ≤ r`
  have hμB : R.measure (closedBall z r) < ∞ := by
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult _ (isCompact_closedBall z r) hzU)
  have hμt : ∀ t, t ≤ r → R.measure (ball z t) < ∞ := fun t ht =>
    (measure_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall ht))).trans_lt hμB
  -- (b) for each cutoff `ηⱼ`, `e^{κs} s⁻ⁿ ∫ ηⱼ(|x - z|²/s²) dμ` is nondecreasing on `(0, r]`
  obtain ⟨η, hηC, hη0, hη'0, hη1, hlim⟩ := Submission.dsmc_em_cutoff_tendsto_ball
  have hj : ∀ j, Real.exp (κ * σ) / σ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / σ ^ 2) ∂R.measure ≤
      Real.exp (κ * ρ) / ρ ^ n * ∫ x, η j (‖x - z‖ ^ 2 / ρ ^ 2) ∂R.measure := by
    intro j
    obtain ⟨hcont, hderiv⟩ := Submission.dsmc_em_cutoff_integral_hasDerivAt P R.measure z r (η j)
      (hμt r le_rfl) (hηC j) (hη1 j)
    refine Submission.dsmc_em_exp_monotoneOn_of_deriv_ineq n κ r _ _ hcont hderiv (fun s hs => ?_)
      ⟨hσ, hσρ.trans hρr⟩ ⟨hρ, hρr⟩ hσρ
    -- `n I(s) - s I'(s) = n I(s) + ∫ 2 u η'(u) dμ ≤ κ s I(s)`
    have h := Submission.dsmc_em_cutoff_first_variation_le P n U R H κ z r (η j) hzU hPm hHκ hfv
      (hηC j) (hη0 j) (hη'0 j) (hη1 j) s hs.1 hs.2
    rw [mul_div_cancel₀ _ hs.1.ne', sub_neg_eq_add]
    exact h
  -- (c) let `j → ∞`: the integrals tend to `μ(B_σ(z))` and `μ(B_ρ(z))`
  have hreal : Real.exp (κ * σ) / σ ^ n * R.measure.real (ball z σ) ≤
      Real.exp (κ * ρ) / ρ ^ n * R.measure.real (ball z ρ) :=
    le_of_tendsto_of_tendsto'
      ((hlim P R.measure z σ hσ (hμt σ (hσρ.trans hρr))).const_mul _)
      ((hlim P R.measure z ρ hρ (hμt ρ hρr)).const_mul _) hj
  -- (d) transfer to `[0, ∞]`
  rw [← ofReal_measureReal (hμt σ (hσρ.trans hρr)).ne, ← ofReal_measureReal (hμt ρ hρr).ne,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- **Simon Ch. 4, 2.2 and 4.1.1**: for `R = (M, θ, ξ)` and `X ∈ C¹_c(U; ℝᴾ)` with `x ↦ p_{TₓM}`
`μ_R`-measurable, `div_M X` is `μ_R`-integrable and `δV(X) = ∫_M θ div_M X dHⁿ = ∫ div_M X dμ_R`,
`μ_R = θ Hⁿ⌞M`.  `div_M X(x) = tr(p_{TₓM} ∘ DX(x))` is bounded by `‖tr‖ ‖DX(x)‖`, and it vanishes
off the compact `spt X ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dsmc_firstVariation_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (X : Euclid P → Euclid P), ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure ∧ R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := by
  intro P n U R X hX hcpt hU hp
  -- the trace is a continuous linear functional on `L(ℝᴾ, ℝᴾ)`, and `div_M X(x) = tr(p_x ∘ DX(x))`
  let tr : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (Euclid P)).comp (ContinuousLinearMap.coeLM ℝ))
  have hdiv : ∀ x, tangentialDivergence n R.carrier X x =
      tr ((approxTangentPlane n R.carrier x).starProjection ∘L fderiv ℝ X x) := fun x => rfl
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hD : Continuous (fderiv ℝ X) := hX.continuous_fderiv one_ne_zero
  -- `div_M X` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    (tr.continuous.comp isBoundedBilinearMap_comp.continuous).comp_aestronglyMeasurable₂
      (g := fun p D : Euclid P →L[ℝ] Euclid P => tr (p ∘L D)) hp.aestronglyMeasurable
      hD.aestronglyMeasurable
  -- `|div_M X(x)| ≤ ‖tr‖ C 1_K(x)`, `K = spt X`, `C = sup ‖DX‖`
  obtain ⟨C, hC⟩ := hD.bounded_above_of_compact_support (hcpt.fderiv ℝ)
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hbound : ∀ x, ‖tangentialDivergence n R.carrier X x‖ ≤
      (tsupport X).indicator (fun _ => ‖tr‖ * C) x := by
    intro x
    rw [hdiv]
    by_cases hxK : x ∈ tsupport X
    · rw [Set.indicator_of_mem hxK]
      refine (tr.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg tr))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      simpa using mul_le_mul (Submodule.starProjection_norm_le _) (hC x) (norm_nonneg _) zero_le_one
    · rw [Set.indicator_of_notMem hxK, fderiv_of_notMem_tsupport ℝ hxK,
        ContinuousLinearMap.comp_zero, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport X) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport X) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => tangentialDivergence n R.carrier X x) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.firstVariation]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **First variation of a varifold stationary in `U ∩ N`** (Simon Ch. 4, 2.5–2.7; Ch. 2,
5.9–5.10).  Let `Pt` be a `C¹` field of self-adjoint operators on `B_{3r}(y₀)` such that, at
`q ∈ N`, `Pt(q)` maps into `T_qN` and fixes `T_qN`, with `‖DPt‖ ≤ β` on `B_{2r}(y₀)`.  If
`V = v(M, θ)` is stationary in `U ∩ N` and `TₓM ⊆ TₓN` for `μ_V`-a.e. `x`, then
`H(x) = Σₐ (DPt(x)(pₓeₐ))eₐ = Σᵢ (DPt(x)τᵢ)τᵢ` (`τ` an orthonormal basis of `TₓM`) on `B_{2r}(y₀)`,
`H = 0` elsewhere, has `‖H‖ ≤ nβ` and `δV(X) = −∫ X · H dμ_V` for `X ∈ C¹_c(B_{2r}(y₀); ℝᴾ)`:
`Xᵀ = Pt·X` is tangent to `N`, so `δV(Xᵀ) = 0`, and `div_M (X − Xᵀ) = −X · H` a.e. by the product
rule, `Pt(x)τᵢ = τᵢ` and the self-adjointness of `Pt(x)` and of `DPt(x)u`. -/
theorem Submission.dsmc_firstVariation_eq_neg_meanCurvature : ∀ (P n : ℕ) (U N : Set (Euclid P)) (R : IMRep U n) (Pt : Euclid P → (Euclid P →L[ℝ] Euclid P)) (y₀ : Euclid P) (r β : ℝ), 0 ≤ β → ball y₀ (3 * r) ⊆ U → ContDiffOn ℝ 1 Pt (ball y₀ (3 * r)) → (∀ y ∈ ball y₀ (3 * r), ∀ u w : Euclid P, inner ℝ (Pt y u) w = inner ℝ u (Pt y w)) → (∀ y ∈ ball y₀ (2 * r), ‖fderiv ℝ Pt y‖ ≤ β) → (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u : Euclid P, Pt q u ∈ tangentSpace N q) → (∀ q ∈ N ∩ ball y₀ (3 * r), ∀ u ∈ tangentSpace N q, Pt q u = u) → (∀ᵐ x ∂R.measure, x ∈ N) → (∀ᵐ x ∂R.measure, x ∈ ball y₀ (3 * r) → (approxTangentPlane n R.carrier x : Set (Euclid P)) ⊆ tangentSpace N x) → AEMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → R.IsStationaryAlong N → ∃ H : Euclid P → Euclid P, AEStronglyMeasurable H R.measure ∧ (∀ x, ‖H x‖ ≤ (n : ℝ) * β) ∧ ∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ ball y₀ (2 * r) → R.firstVariation X = -∫ x, inner ℝ (X x) (H x) ∂R.measure := by
  intro P n U N R Pt y₀ r β hβ hball hPt hsym hDPt hPtT hPtfix hN hTN hpm hstat
  -- notation: `e` is the standard orthonormal basis of `ℝᴾ` and `Φ(B, p) = Σₐ (B (p eₐ)) eₐ`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let Φ : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) → (Euclid P →L[ℝ] Euclid P) → Euclid P :=
    fun B p => ∑ a, B (p (e a)) (e a)
  -- Step 1(a): `dim TₓM ≤ n`, `TₓM` being an approximate tangent space or `{0}`
  have hrank : ∀ x, Module.finrank ℝ (approxTangentPlane n R.carrier x) ≤ n := by
    intro x
    by_cases h : ∃ Q, HasApproximateTangentSpaceAt n R.carrier x Q
    · have hT : approxTangentPlane n R.carrier x = h.choose := by
        unfold approxTangentPlane
        rw [dite_eq_left h]
      rw [hT]
      exact h.choose_spec.finrank_eq.le
    · have hT : approxTangentPlane n R.carrier x = ⊥ := by
        unfold approxTangentPlane
        rw [dite_eq_right h]
      rw [hT]
      simp
  -- Step 1(b): `trace(p_K ∘ D) = Σᵢ ⟨τᵢ, Dτᵢ⟩` for an orthonormal basis `τ` of `K`
  have htr : ∀ (K : Submodule ℝ (Euclid P)) (m : ℕ) (τ : OrthonormalBasis (Fin m) ℝ K)
      (D : Euclid P →L[ℝ] Euclid P),
      LinearMap.trace ℝ (Euclid P) (K.starProjection.toLinearMap ∘ₗ D.toLinearMap) =
        ∑ i, inner ℝ (τ i : Euclid P) (D (τ i)) := by
    intro K m τ D
    rw [Submodule.starProjection, ContinuousLinearMap.toLinearMap_comp, LinearMap.comp_assoc,
      LinearMap.trace_comp_comm', LinearMap.trace_eq_sum_inner _ τ]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  -- Step 1(c): `Φ(B, p_K) = Σᵢ (Bτᵢ)τᵢ` for an orthonormal basis `τ` of `K`
  have hcontr : ∀ (K : Submodule ℝ (Euclid P)) (m : ℕ) (τ : OrthonormalBasis (Fin m) ℝ K)
      (B : Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)),
      Φ B K.starProjection = ∑ i, B (τ i : Euclid P) (τ i : Euclid P) := by
    intro K m τ B
    have hp : ∀ v, K.starProjection v = ∑ i, inner ℝ (τ i : Euclid P) v • (τ i : Euclid P) := by
      intro v
      rw [Submodule.starProjection_apply, τ.orthogonalProjectionOnto_apply_eq_sum]
      simp
    have he : ∀ i, ∑ a, inner ℝ (τ i : Euclid P) (e a) • e a = (τ i : Euclid P) := by
      intro i
      simpa [real_inner_comm] using e.sum_repr' (τ i : Euclid P)
    simp only [Φ, hp, map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
      Pi.smul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc ∑ a, inner ℝ (τ i : Euclid P) (e a) • B (τ i : Euclid P) (e a)
        = B (τ i : Euclid P) (∑ a, inner ℝ (τ i : Euclid P) (e a) • e a) := by
          rw [map_sum]
          simp [map_smul]
      _ = B (τ i : Euclid P) (τ i : Euclid P) := by rw [he i]
  -- `B_{2r}(y₀) ⊆ B_{3r}(y₀)` for every `r` (both are empty if `r ≤ 0`)
  have h23 : ball y₀ (2 * r) ⊆ ball y₀ (3 * r) := by
    rcases le_or_gt r 0 with hr | hr
    · rw [ball_eq_empty.mpr (by linarith)]
      exact empty_subset _
    · exact ball_subset_ball (by linarith)
  -- `Pt` is differentiable on the open ball `B_{3r}(y₀)`
  have hPtd : ∀ x ∈ ball y₀ (3 * r), DifferentiableAt ℝ Pt x := fun x hx =>
    (hPt.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hx)
  -- Step 1(d): `DPt(x)u` is self-adjoint for `x ∈ B_{3r}(y₀)`: differentiate
  -- `y ↦ ⟨b, Pt(y)a⟩ − ⟨a, Pt(y)b⟩`, which vanishes near `x`
  have hDsym : ∀ x ∈ ball y₀ (3 * r), ∀ u a b : Euclid P,
      inner ℝ (fderiv ℝ Pt x u a) b = inner ℝ a (fderiv ℝ Pt x u b) := by
    intro x hx u a b
    let ℓ : (Euclid P →L[ℝ] Euclid P) →L[ℝ] ℝ :=
      (innerSL ℝ b).comp (ContinuousLinearMap.apply ℝ (Euclid P) a) -
        (innerSL ℝ a).comp (ContinuousLinearMap.apply ℝ (Euclid P) b)
    have hℓ : ∀ L : Euclid P →L[ℝ] Euclid P, ℓ L = inner ℝ b (L a) - inner ℝ a (L b) := by
      intro L; rfl
    have hev : (fun y => ℓ (Pt y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [hℓ, real_inner_comm, hsym y hy, sub_self]
    have h1 : HasFDerivAt (fun y => ℓ (Pt y)) (ℓ.comp (fderiv ℝ Pt x)) x :=
      ℓ.hasFDerivAt.comp x (hPtd x hx).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ℓ (Pt y)) (0 : Euclid P →L[ℝ] ℝ) x :=
      (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hev
    have h3 := congrArg (fun L => L u) (h1.unique h2)
    simp only [ContinuousLinearMap.comp_apply, zero_apply, hℓ] at h3
    rw [real_inner_comm]
    linarith
  -- Step 2: `H = 1_{B_{2r}(y₀)} · Φ(DPt(x), pₓ)`
  refine ⟨(ball y₀ (2 * r)).indicator
    (fun x => Φ (fderiv ℝ Pt x) (approxTangentPlane n R.carrier x).starProjection), ?_, ?_, ?_⟩
  · -- Step 2(b): `x ↦ DPt(x)` is Borel, `x ↦ pₓ` is `μ_V`-measurable and `Φ` is continuous
    have hΦc : Continuous (fun q : (Euclid P →L[ℝ] (Euclid P →L[ℝ] Euclid P)) ×
        (Euclid P →L[ℝ] Euclid P) => Φ q.1 q.2) := by
      simp only [Φ]
      fun_prop
    have h1 : AEMeasurable
        (fun x => Φ (fderiv ℝ Pt x) (approxTangentPlane n R.carrier x).starProjection) R.measure :=
      hΦc.aemeasurable2 (measurable_fderiv ℝ Pt).aemeasurable hpm
    exact (h1.indicator measurableSet_ball).aestronglyMeasurable
  · -- Step 2(a): `‖H(x)‖ ≤ Σᵢ ‖DPt(x)‖ |τᵢ|² ≤ nβ`
    intro x
    by_cases hx : x ∈ ball y₀ (2 * r)
    · set τ := stdOrthonormalBasis ℝ (approxTangentPlane n R.carrier x)
      rw [indicator_of_mem hx, hcontr _ _ τ]
      have hτ : ∀ i, ‖(τ i : Euclid P)‖ = 1 := fun i => by
        rw [Submodule.norm_coe]
        exact τ.orthonormal.norm_eq_one i
      calc ‖∑ i, fderiv ℝ Pt x (τ i : Euclid P) (τ i : Euclid P)‖
          ≤ ∑ i, ‖fderiv ℝ Pt x (τ i : Euclid P) (τ i : Euclid P)‖ := norm_sum_le _ _
        _ ≤ ∑ _i, ‖fderiv ℝ Pt x‖ := by
            gcongr with i
            calc ‖fderiv ℝ Pt x (τ i : Euclid P) (τ i : Euclid P)‖
                ≤ ‖fderiv ℝ Pt x (τ i : Euclid P)‖ * ‖(τ i : Euclid P)‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ ‖fderiv ℝ Pt x‖ * ‖(τ i : Euclid P)‖ * ‖(τ i : Euclid P)‖ := by
                  gcongr
                  exact ContinuousLinearMap.le_opNorm _ _
              _ = ‖fderiv ℝ Pt x‖ := by rw [hτ, mul_one, mul_one]
        _ = (Module.finrank ℝ (approxTangentPlane n R.carrier x) : ℝ) * ‖fderiv ℝ Pt x‖ := by
            simp
        _ ≤ (n : ℝ) * β := by
            gcongr
            · exact_mod_cast hrank x
            · exact hDPt x hx
    · rw [indicator_of_notMem hx, norm_zero]
      positivity
  -- Steps 3–6, for a fixed `X ∈ C¹_c(B_{2r}(y₀); ℝᴾ)`
  intro X hX hXc hXs
  have hXzero : ∀ x, x ∉ tsupport X → X =ᶠ[𝓝 x] 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp hx
  -- Step 3(a): `Xᵀ = Pt·X` is `C¹`: on `B_{3r}(y₀)` by the product rule, elsewhere it vanishes
  -- near the point
  have hXTc : ContDiff ℝ 1 (fun x => Pt x (X x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball y₀ (3 * r)
    · exact (hPt.contDiffAt (isOpen_ball.mem_nhds hx)).clm_apply hX.contDiffAt
    · have hxK : x ∉ tsupport X := fun h => hx (h23 (hXs h))
      have hev : (fun x => Pt x (X x)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hXzero x hxK] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  -- Step 3(b): `spt Xᵀ ⊆ spt X`, a compact subset of `U`
  have hXTsupp : tsupport (fun x => Pt x (X x)) ⊆ tsupport X := by
    apply closure_mono
    intro x hx
    by_contra h
    apply hx
    simp [Function.notMem_support.mp h]
  have hXTc' : HasCompactSupport (fun x => Pt x (X x)) :=
    hXc.mono' ((subset_tsupport _).trans hXTsupp)
  have hXsU : tsupport X ⊆ U := hXs.trans (h23.trans hball)
  have hXTsU : tsupport (fun x => Pt x (X x)) ⊆ U := hXTsupp.trans hXsU
  -- Step 3(c): `Xᵀ(x) ∈ TₓN` on `N ∩ U` (off `B_{3r}(y₀)`, `Xᵀ(x) = 0`, the velocity of a
  -- constant curve)
  have hXTtan : ∀ x ∈ N ∩ U, (fun x => Pt x (X x)) x ∈ tangentSpace N x := by
    rintro x ⟨hxN, -⟩
    by_cases hx : x ∈ ball y₀ (3 * r)
    · exact hPtT x ⟨hxN, hx⟩ (X x)
    · have hxK : x ∉ tsupport X := fun h => hx (h23 (hXs h))
      have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp only [hX0, map_zero]
      exact ⟨fun _ => x, contDiffOn_const, fun _ _ => hxN, rfl, hasDerivAt_const _ _⟩
  -- Step 3(d): stationarity in `U ∩ N` gives `δV(Xᵀ) = 0`
  have hδXT : R.firstVariation (fun x => Pt x (X x)) = 0 := hstat _ hXTc hXTc' hXTsU hXTtan
  -- Step 4: integral form of `δV(X)` and `δV(Xᵀ)` (sibling `first_variation_integral`), and
  -- `div_M X = div_M Xᵀ + div_M Y` with `Y = X − Xᵀ`
  obtain ⟨hiX, hδX⟩ := Submission.dsmc_firstVariation_eq_integral P n U R X hX hXc hXsU hpm
  obtain ⟨hiXT, hδXT'⟩ :=
    Submission.dsmc_firstVariation_eq_integral P n U R _ hXTc hXTc' hXTsU hpm
  have hdivY : ∀ x, tangentialDivergence n R.carrier (fun y => X y - Pt y (X y)) x =
      tangentialDivergence n R.carrier X x -
        tangentialDivergence n R.carrier (fun x => Pt x (X x)) x := by
    intro x
    have hD : fderiv ℝ (fun y => X y - Pt y (X y)) x =
        fderiv ℝ X x - fderiv ℝ (fun x => Pt x (X x)) x :=
      fderiv_sub (hX.differentiable one_ne_zero x) (hXTc.differentiable one_ne_zero x)
    simp only [tangentialDivergence, hD, ContinuousLinearMap.toLinearMap_sub, LinearMap.comp_sub,
      map_sub]
  -- Step 5: `div_M Y = −⟨X, H⟩` at `μ_V`-a.e. `x`
  have hae : (fun x => tangentialDivergence n R.carrier (fun y => X y - Pt y (X y)) x)
      =ᵐ[R.measure] fun x => -inner ℝ (X x) ((ball y₀ (2 * r)).indicator
        (fun x => Φ (fderiv ℝ Pt x) (approxTangentPlane n R.carrier x).starProjection) x) := by
    filter_upwards [hN, hTN] with x hxN hxT
    by_cases hxK : x ∈ tsupport X
    · -- Step 5(b)–(d): `DY(x)u = DX(x)u − Pt(x)DX(x)u − (DPt(x)u)X(x)`, and for an orthonormal
      -- basis `τ` of `TₓM ⊆ TₓN`: `⟨τᵢ, Pt(x)DX(x)τᵢ⟩ = ⟨τᵢ, DX(x)τᵢ⟩` and
      -- `⟨τᵢ, (DPt(x)τᵢ)X(x)⟩ = ⟨(DPt(x)τᵢ)τᵢ, X(x)⟩`
      have hx2 : x ∈ ball y₀ (2 * r) := hXs hxK
      have hx3 : x ∈ ball y₀ (3 * r) := h23 hx2
      set τ := stdOrthonormalBasis ℝ (approxTangentPlane n R.carrier x)
      have hfix : ∀ v ∈ approxTangentPlane n R.carrier x, Pt x v = v := fun v hv =>
        hPtfix x ⟨hxN, hx3⟩ v (hxT hx3 hv)
      have hXd : DifferentiableAt ℝ X x := hX.differentiable one_ne_zero x
      have hXTd : DifferentiableAt ℝ (fun y => Pt y (X y)) x := (hPtd x hx3).clm_apply hXd
      have hD : fderiv ℝ (fun y => X y - Pt y (X y)) x =
          fderiv ℝ X x - ((Pt x).comp (fderiv ℝ X x) + (fderiv ℝ Pt x).flip (X x)) := by
        rw [fderiv_fun_sub hXd hXTd, fderiv_clm_apply (hPtd x hx3) hXd]
      rw [indicator_of_mem hx2, hcontr _ _ τ]
      simp only [tangentialDivergence]
      rw [htr _ _ τ, hD, inner_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfixi : Pt x (τ i : Euclid P) = τ i := hfix _ (τ i).2
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.flip_apply, inner_sub_right, inner_add_right]
      rw [← hsym x hx3, hfixi, ← hDsym x hx3, real_inner_comm (X x)]
      ring
    · -- Step 5(a): off `spt X`, `Y` vanishes near `x`
      have hev : (fun y => X y - Pt y (X y)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hXzero x hxK] with y hy
        simp [hy]
      have hX0 : X x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp only [tangentialDivergence, hev.fderiv_eq, hX0, inner_zero_left, neg_zero]
      simp
  -- Step 6: `δV(X) = ∫ div_M Xᵀ + ∫ div_M Y = ∫ div_M Y = −∫ ⟨X, H⟩`
  calc R.firstVariation X = ∫ x, tangentialDivergence n R.carrier X x ∂R.measure := hδX
    _ = ∫ x, tangentialDivergence n R.carrier (fun y => X y - Pt y (X y)) x ∂R.measure := by
        simp_rw [hdivY]
        rw [integral_sub hiX hiXT, ← hδXT', hδXT, sub_zero]
    _ = _ := integral_congr_ae hae
    _ = _ := integral_neg _

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
