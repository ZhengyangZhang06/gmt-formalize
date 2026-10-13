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

/-- A test form has bounded Euclidean coefficient norm: for `ω ∈ 𝒟ᵏ(U)` there is `M ≥ 0` with
`|ω(x)| ≤ M` for every `x` (Simon (6.1.15), `|ω|_U < ∞`).  The coefficient norm `|ω(x)|` is
continuous, as a square root of a finite sum of squares of evaluations of `ω(x)`, and vanishes
off `spt ω`, so it is continuous with compact support, hence bounded. -/
theorem Submission.cbr_rlim_coeffNorm_bound : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M := by
  intro P k U ω
  obtain ⟨w, ⟨hws, hwcs⟩, -⟩ := ω
  change ∃ M : ℝ, 0 ≤ M ∧ ∀ x, covectorEuclideanNorm (w x) ≤ M
  have hwc : Continuous w := hws.continuous
  -- `x ↦ |w(x)|` is continuous
  have hnc : Continuous fun x => covectorEuclideanNorm (w x) := by
    unfold covectorEuclideanNorm
    refine Continuous.sqrt (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact ((ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ _).continuous.comp hwc).pow 2
    · exact continuous_const
  -- and vanishes off `spt w`, so it has compact support
  have hcs : HasCompactSupport fun x => covectorEuclideanNorm (w x) := by
    refine HasCompactSupport.intro hwcs fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport hx, covectorEuclideanNorm_zero]
  -- hence it is bounded by some `M`, and by `max M 0`
  obtain ⟨M, hM⟩ := hnc.bounded_above_of_compact_support hcs
  exact ⟨max M 0, le_max_right _ _,
    fun x => ((Real.le_norm_self _).trans (hM x)).trans (le_max_left _ _)⟩
/-- **Smooth one-sided cut-off of a test form** (the `C^∞` version of the Lipschitz cut-off
`γ_ε ∘ f` in the proof of Simon 6.4.5(2)): for continuous `f`, `t` and `ε > 0` there is `χ` with
`0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t - ε}` and `χ = 0` on `{f ≥ t}` such that `χ ω` is again a test
form in `U`.  The smooth Urysohn lemma for the closed set `{f ≤ t - ε}` inside the open set
`{f < t}` gives `χ`, and `χ ω` is smooth with `tsupport (χ ω) ⊆ tsupport ω ⊆ U` compact. -/
theorem Submission.cbr_rlim_smooth_cutoff : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k) (f : Euclid P → ℝ) (t ε : ℝ), Continuous f → 0 < ε → ∃ (χ : Euclid P → ℝ) (η : TestFormOn U k), (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ x, f x ≤ t - ε → χ x = 1) ∧ (∀ x, t ≤ f x → χ x = 0) := by
  intro P k U ω f t ε hf hε
  -- steps 1-2: a `C^∞` Urysohn function for the closed `{f ≤ t - ε}` inside the open `{f < t}`
  have hsub : {x | f x ≤ t - ε} ⊆ {x | f x < t} := fun x (hx : f x ≤ t - ε) =>
    show f x < t by linarith
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_lt hf continuous_const) (isClosed_le hf continuous_const) hsub
  -- step 3: `χ • ω` is smooth, compactly supported, with `tsupport (χ • ω) ⊆ tsupport ω ⊆ U`
  obtain ⟨⟨hω, hωc⟩, hωU⟩ := ω.2
  have hv : χ • (ω : DifferentialForm (Euclid P) k) ∈ testFormOnSubmodule U k :=
    ⟨⟨hχ.smul hω, hωc.smul_left⟩, (tsupport_smul_subset_right χ _).trans hωU⟩
  -- steps 4-5: `0 ≤ χ ≤ 1` from `range χ ⊆ [0, 1]`, and `χ = 1` exactly on `{f ≤ t - ε}`
  refine ⟨χ, ⟨_, hv⟩, fun x => rfl, fun x => hχr (mem_range_self x), fun x hx => (hχ1 x).1 hx,
    fun x hx => notMem_support.1 fun hx' => ?_⟩
  -- step 6: `t ≤ f x` puts `x` outside `support χ = {f < t}`
  rw [hχs] at hx'
  exact (not_lt.2 hx) hx'
/-- Cut-off error estimate for an admissible pair `(μ, ξ)` (`|ξ(x)(α)| ≤ |α|_E` for `μ`-a.e. `x`):
if `|ω|_E ≤ M`, `η = χ ω` with `0 ≤ χ ≤ 1`, `χ = 1` on `{f ≤ t − ε}` and `χ = 0` on `{f ≥ t}` (as
for the cut-off `γ_ε ∘ f` in the proof of Simon Ch. 6, 4.5(2)), then `∫_{f<t} ξ(ω) dμ` and
`∫ ξ(η) dμ` differ by at most `M μ(spt ω ∩ {t − ε < f < t})`.  Both integrands are bounded by
`M 1_{spt ω}`, and `1_{f<t} ξ(ω) − ξ(η) = (1_{f<t} − χ) ξ(ω)` vanishes off
`spt ω ∩ {t − ε < f < t}`. -/
theorem Submission.cbr_rlim_cutoff_error_le : ∀ (P k : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (ω η : TestFormOn U k) (χ f : Euclid P → ℝ) (t ε M : ℝ), Continuous f → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ M) → (∀ x, (η : DifferentialForm (Euclid P) k) x = χ x • (ω : DifferentialForm (Euclid P) k) x) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) → (∀ x, f x ≤ t - ε → χ x = 1) → (∀ x, t ≤ f x → χ x = 0) → |(∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) - ∫ x, ξ x ((η : DifferentialForm (Euclid P) k) x) ∂μ| ≤ M * (μ (tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t})).toReal := by
  intro P k U μ ξ ω η χ f t ε M hf hμ hξm hξ hωM hη hχ hχ1 hχ0
  obtain ⟨⟨hωs, hωc⟩, hωU⟩ := ω.2
  have hηs := η.2.1.1
  set w : DifferentialForm (Euclid P) k := (ω : DifferentialForm (Euclid P) k)
  set v : DifferentialForm (Euclid P) k := (η : DifferentialForm (Euclid P) k)
  set C := tsupport w
  set S := {x | f x < t}
  set B := {x | t - ε < f x ∧ f x < t}
  -- Step 1: `M ≥ 0`.
  have hM : 0 ≤ M := (covectorEuclideanNorm_nonneg _).trans (hωM 0)
  -- Step 2: measurability and finiteness.
  have hCm : MeasurableSet C := (isClosed_tsupport w).measurableSet
  have hSm : MeasurableSet S := measurableSet_lt hf.measurable measurable_const
  have hBm : MeasurableSet B :=
    (measurableSet_lt measurable_const hf.measurable).inter
      (measurableSet_lt hf.measurable measurable_const)
  have hCf : μ C < ∞ := hμ C hωc hωU
  have hCBf : μ (C ∩ B) < ∞ := (measure_mono inter_subset_left).trans_lt hCf
  -- Step 3: `g = ξ(w)` and `h = ξ(v)` are a.e. strongly measurable.
  have hgm : AEStronglyMeasurable (fun x => ξ x (w x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hωs).aestronglyMeasurable
  have hhm : AEStronglyMeasurable (fun x => ξ x (v x)) μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂ hξm
      (ContDiff.continuous hηs).aestronglyMeasurable
  -- Step 4: `|g| ≤ M` a.e., `g = 0` off `C`, so `g` is integrable.
  have hg0 : ∀ x, x ∉ C → ξ x (w x) = 0 := fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, map_zero]
  have hgM : ∀ᵐ x ∂μ, |ξ x (w x)| ≤ M := by
    filter_upwards [hξ] with x hx
    exact (hx _).trans (hωM x)
  have hCi : Integrable (C.indicator fun _ => M) μ :=
    (integrable_indicator_iff hCm).2 (integrableOn_const hCf.ne)
  have hgi : Integrable (fun x => ξ x (w x)) μ := by
    refine hCi.mono' hgm ?_
    filter_upwards [hgM] with x hx
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC, Real.norm_eq_abs]
      exact hx
    · rw [indicator_of_notMem hxC, hg0 x hxC, norm_zero]
  -- Step 5: `h = χ g`, so `h` is integrable.
  have hhg : ∀ x, ξ x (v x) = χ x * ξ x (w x) := fun x => by
    rw [hη x, map_smul, smul_eq_mul]
  have hhi : Integrable (fun x => ξ x (v x)) μ := by
    refine hgi.mono hhm (Eventually.of_forall fun x => ?_)
    rw [hhg x, norm_mul, Real.norm_eq_abs (χ x), abs_of_nonneg (hχ x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hχ x).2
  -- Step 6: rewrite the difference as one integral.
  rw [← integral_indicator hSm, ← integral_sub (hgi.indicator hSm) hhi]
  -- Step 7: pointwise bound by `M 1_{C ∩ B}`.
  have hbd : ∀ᵐ x ∂μ, ‖S.indicator (fun x => ξ x (w x)) x - ξ x (v x)‖ ≤
      (C ∩ B).indicator (fun _ => M) x := by
    filter_upwards [hgM] with x hx
    have hnn : 0 ≤ (C ∩ B).indicator (fun _ => M) x := indicator_nonneg (fun _ _ => hM) x
    rw [hhg x]
    by_cases hxS : f x < t
    · rw [indicator_of_mem (show x ∈ S from hxS)]
      by_cases hxε : f x ≤ t - ε
      · rw [hχ1 x hxε, one_mul, sub_self, norm_zero]
        exact hnn
      · by_cases hxC : x ∈ C
        · rw [indicator_of_mem (show x ∈ C ∩ B from ⟨hxC, not_le.1 hxε, hxS⟩)]
          rw [← one_sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.2 (hχ x).2)]
          exact (mul_le_of_le_one_left (abs_nonneg _) (sub_le_self 1 (hχ x).1)).trans hx
        · rw [hg0 x hxC, mul_zero, sub_zero, norm_zero]
          exact hnn
    · rw [indicator_of_notMem (show x ∉ S from hxS), hχ0 x (not_lt.1 hxS), zero_mul, sub_zero,
        norm_zero]
      exact hnn
  -- Step 8: integrate the majorant.
  have hmi : Integrable ((C ∩ B).indicator fun _ => M) μ :=
    (integrable_indicator_iff (hCm.inter hBm)).2 (integrableOn_const hCBf.ne)
  calc |∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ|
      = ‖∫ x, S.indicator (fun x => ξ x (w x)) x - ξ x (v x) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, (C ∩ B).indicator (fun _ => M) x ∂μ := norm_integral_le_of_norm_le hmi hbd
    _ = M * (μ (C ∩ B)).toReal := by
      rw [integral_indicator_const M (hCm.inter hBm), smul_eq_mul, measureReal_def, mul_comm]
/-- A thin level band of small measure: if `C` is measurable with `μ(C), ν(C) < ∞`, `f` is
continuous, `μ{f = t} = 0` and `δ > 0`, then some `ε > 0` has `μ(C ∩ {t − ε ≤ f ≤ t}) < δ` and
`ν(C ∩ {t − ε < f < t}) < δ`.  The closed bands of width `1/(n+1)` decrease into the `μ`-null set
`{f = t}` and the open ones decrease to `∅`, so by continuity from above both measures tend
to `0`. -/
theorem Submission.cbr_rlim_thin_band : ∀ (P : ℕ) (μ ν : Measure (Euclid P)) (C : Set (Euclid P)) (f : Euclid P → ℝ) (t δ : ℝ), MeasurableSet C → μ C < ∞ → ν C < ∞ → Continuous f → μ {x | f x = t} = 0 → 0 < δ → ∃ ε : ℝ, 0 < ε ∧ μ (C ∩ {x | t - ε ≤ f x ∧ f x ≤ t}) < ENNReal.ofReal δ ∧ ν (C ∩ {x | t - ε < f x ∧ f x < t}) < ENNReal.ofReal δ := by
  intro P μ ν C f t δ hC hμC hνC hf hμt hδ
  have hfm : Measurable f := hf.measurable
  -- the widths `1 / (n + 1)` decrease, so the closed and the open bands decrease in `n`
  have hr : Antitone fun n : ℕ => 1 / ((n : ℝ) + 1) := fun _ _ h => Nat.one_div_le_one_div h
  have hAm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans hx.2.1, hx.2.2⟩
  have hBm : Antitone fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t} :=
    fun _ _ h x hx => ⟨hx.1, (sub_le_sub_left (hr h) t).trans_lt hx.2.1, hx.2.2⟩
  -- the closed bands shrink into the `μ`-null level set `{f = t}`
  have hA0 : μ (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) hμt
    rw [mem_iInter] at hx
    refine le_antisymm (hx 0).2.2 (le_of_not_gt fun hlt => ?_)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
    linarith [(hx n).2.1]
  -- the open bands shrink to the empty set
  have hB0 : ν (⋂ n : ℕ, C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t}) = 0 := by
    refine measure_mono_null (fun x hx => ?_) measure_empty
    rw [mem_iInter] at hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hx 0).2.2)
    exact absurd (hx n).2.1 (by linarith)
  -- continuity from above (the first bands have finite measure): eventually both band
  -- measures are below `δ`
  have hδ' : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  have hA := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) ≤ f x ∧ f x ≤ t})
    (fun _ => (hC.inter ((measurableSet_le measurable_const hfm).inter
      (measurableSet_le hfm measurable_const))).nullMeasurableSet) hAm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hμC).ne⟩).eventually_lt_const
    (hA0.trans_lt hδ')
  have hB := (tendsto_measure_iInter_atTop
    (s := fun n : ℕ => C ∩ {x | t - 1 / ((n : ℝ) + 1) < f x ∧ f x < t})
    (fun _ => (hC.inter ((measurableSet_lt measurable_const hfm).inter
      (measurableSet_lt hfm measurable_const))).nullMeasurableSet) hBm
    ⟨0, ((measure_mono inter_subset_left).trans_lt hνC).ne⟩).eventually_lt_const
    (hB0.trans_lt hδ')
  obtain ⟨N, hN⟩ := (hA.and hB).exists
  exact ⟨1 / ((N : ℝ) + 1), Nat.one_div_pos_of_nat, hN.1, hN.2⟩
/-- **Restriction to a sublevel set passes to weak limits** (the step of Simon Ch. 6, Remark
8.3(1), `T_j ⌞ {f < t} ⇀ T ⌞ {f < t}`, justified there "by an argument like that in 6.7(2) of
Ch. 2"): if `X_j ⇀ X` are represented by admissible pairs `(μ_j, ξ_j)`, `(μ_X, ξ_X)`, the
`μ_j` are dominated in the limit by `μ` on compact subsets of `U`, and `μ{f = t} = 0`, then
`∫_{f<t} ξ_j(ω) dμ_j → ∫_{f<t} ξ_X(ω) dμ_X` for every test form `ω`.  This is an `ε/3`
argument: with `|ω|_E ≤ M`, a thin band `{t − ε ≤ f ≤ t}` of `μ`- and `μ_X`-measure `< δ` on
`spt ω`, and the smooth cut-off `η = χ ω`, both restricted integrals are within `M δ` of
`X_j(η)` resp. `X(η)` (eventually in `j`, by the `limsup` bound on the compact band), and
`X_j(η) → X(η)`. -/
theorem Submission.cbr_sublevel_restriction_tendsto : ∀ (P k : ℕ) (U : Set (Euclid P)) (Xs : ℕ → GeometricCurrentOn U k) (X : GeometricCurrentOn U k) (μs : ℕ → Measure (Euclid P)) (ξs : ℕ → Euclid P → MultiVector P k) (μX μ : Measure (Euclid P)) (ξX : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (t : ℝ), IsOpen U → Continuous f → WeaklyConvergesOn Xs X → (∀ j, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μs j K < ∞) → (∀ j, AEStronglyMeasurable (ξs j) (μs j)) → (∀ j, ∀ᵐ x ∂(μs j), ∀ α : Covector (Euclid P) k, |ξs j x α| ≤ covectorEuclideanNorm α) → (∀ j, ∀ ω : TestFormOn U k, Xs j ω = ∫ x, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μX K < ∞) → AEStronglyMeasurable ξX μX → (∀ᵐ x ∂μX, ∀ α : Covector (Euclid P) k, |ξX x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U k, X ω = ∫ x, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → limsup (fun j => μs j K) atTop ≤ μ K) → μ {x | f x = t} = 0 → ∀ ω : TestFormOn U k, Tendsto (fun j => ∫ x in {x | f x < t}, ξs j x ((ω : DifferentialForm (Euclid P) k) x) ∂(μs j)) atTop (𝓝 (∫ x in {x | f x < t}, ξX x ((ω : DifferentialForm (Euclid P) k) x) ∂μX)) := by
  intro P k U Xs X μs ξs μX μ ξX f t _ hf hconv hμs hξsm hξs hXs hμX hξXm hξX hX hμ hlim hμt ω
  obtain ⟨-, hωc⟩ := ω.2.1
  have hωU := ω.2.2
  -- step 1: `|ω|_E ≤ M` everywhere
  obtain ⟨M, hM, hωM⟩ := Submission.cbr_rlim_coeffNorm_bound P k U ω
  rw [Metric.tendsto_nhds]
  intro e he
  -- step 6: a band of width `ε` with `μ`- and `μ_X`-measure `< δ` on `spt ω`
  have hδ : 0 < e / (3 * (M + 1)) := div_pos he (by positivity)
  have hMδ : M * (e / (3 * (M + 1))) ≤ e / 3 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨ε, hε, hband, hbandX⟩ := Submission.cbr_rlim_thin_band P μ μX
    (tsupport (ω : DifferentialForm (Euclid P) k)) f t (e / (3 * (M + 1)))
    (isClosed_tsupport _).measurableSet (hμ _ hωc hωU) (hμX _ hωc hωU) hf hμt hδ
  -- steps 3-4: the cut-off test form `η = χ ω`
  obtain ⟨χ, η, hη, hχ, hχ1, hχ0⟩ := Submission.cbr_rlim_smooth_cutoff P k U ω f t ε hf hε
  -- step 7: the closed band is a compact subset of `U`, so eventually `μ_j(band) < δ`
  have hKc : IsCompact (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε ≤ f x ∧ f x ≤ t}) :=
    IsCompact.inter_right hωc ((isClosed_le continuous_const hf).inter
      (isClosed_le hf continuous_const))
  have hev := eventually_lt_of_limsup_lt
    ((hlim _ hKc (inter_subset_left.trans hωU)).trans_lt hband)
  filter_upwards [hev, (hconv η).eventually (Metric.ball_mem_nhds (X η) (by positivity : 0 < e / 3))]
    with j hj hjη
  -- step 5: the cut-off errors for `(μ_j, ξ_j)` and `(μ_X, ξ_X)`, each at most `M δ ≤ e / 3`
  have hej := Submission.cbr_rlim_cutoff_error_le P k U (μs j) (ξs j) ω η χ f t ε M hf (hμs j)
    (hξsm j) (hξs j) hωM hη hχ hχ1 hχ0
  have heX := Submission.cbr_rlim_cutoff_error_le P k U μX ξX ω η χ f t ε M hf hμX hξXm hξX hωM
    hη hχ hχ1 hχ0
  have hsub : tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε < f x ∧ f x < t} ⊆
      tsupport (ω : DifferentialForm (Euclid P) k) ∩ {x | t - ε ≤ f x ∧ f x ≤ t} :=
    fun x hx => ⟨hx.1, hx.2.1.le, hx.2.2.le⟩
  have hbj : M * (μs j (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal
      ((measure_mono hsub).trans_lt hj)).le hM).trans hMδ
  have hbX : M * (μX (tsupport (ω : DifferentialForm (Euclid P) k) ∩
      {x | t - ε < f x ∧ f x < t})).toReal ≤ e / 3 :=
    (mul_le_mul_of_nonneg_left (ENNReal.toReal_lt_of_lt_ofReal hbandX).le hM).trans hMδ
  have h1 := abs_le.1 (hej.trans hbj)
  have h3 := abs_le.1 (heX.trans hbX)
  have h2 := abs_lt.1 (show |Xs j η - X η| < e / 3 from Metric.mem_ball.1 hjη)
  rw [hXs j η, hX η] at h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
