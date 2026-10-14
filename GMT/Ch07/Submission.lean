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

/-- Stationarity of a `C¹` graph gives the weak minimal surface system `Δu = div G(Du)`
(Simon Ch. 5, §1, (1.3); first variation Ch. 4, 2.2–2.6; area formula Ch. 2, §3). -/
theorem Submission.codim1_hcp_sr_stationary_mss : ∀ (m k : ℕ), 1 ≤ m → ∃ G : (Euclid m →L[ℝ] Euclid k) → (Euclid m →L[ℝ] Euclid k), ContDiff ℝ (⊤ : ℕ∞) G ∧ G 0 = 0 ∧ fderiv ℝ G 0 = 0 ∧ ∀ (P : ℕ) (U M : Set (Euclid P)) (y : Euclid P) (ι : Euclid m →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (s t : ℝ) (u : Euclid m → Euclid k), (∀ a b, inner ℝ (ι a) (ι' b) = 0) → (∀ z : Euclid P, ∃ a b, z = ι a + ι' b) → 0 < s → 0 < t → IsOpen U → {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (k)) t, z = y + ι a + ι' b} ⊆ U → ContDiffOn ℝ 1 u (ball 0 s) → (∀ a ∈ ball (0 : Euclid m) s, ‖u a‖ < t) → M ∩ {z : Euclid P | ∃ a ∈ ball (0 : Euclid m) s, ∃ b ∈ ball (0 : Euclid (k)) t, z = y + ι a + ι' b} = (fun a => y + ι a + ι' (u a)) '' ball 0 s → (∀ a ∈ ball (0 : Euclid m) s, tangentSpace M (y + ι a + ι' (u a)) = Set.range (fderiv ℝ (fun a => y + ι a + ι' (u a)) a)) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid m) s → ∫ x in ball (0 : Euclid m) s, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball (0 : Euclid m) s, ∑ j : Fin m, inner ℝ (G (fderiv ℝ u x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) := by
  have hAll : ∀ {E K : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup K] [InnerProductSpace ℝ K]
      [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K],
      ∃ G : (E →L[ℝ] K) → (E →L[ℝ] K), ContDiff ℝ (⊤ : ℕ∞) G ∧ G 0 = 0 ∧ fderiv ℝ G 0 = 0 ∧
      ∀ {Pz : Type} [NormedAddCommGroup Pz] [InnerProductSpace ℝ Pz] [FiniteDimensional ℝ Pz]
        [MeasurableSpace Pz] [BorelSpace Pz] {ι₀ : Type} [Fintype ι₀]
        (bE : OrthonormalBasis ι₀ ℝ E) (e : ι₀ → E), (∀ j, bE j = e j) →
        ∀ n : ℕ, Module.finrank ℝ E = n → ∀ ν : Measure E, ν = μHE[n] →
        ∀ (U M : Set Pz) (T : Pz → Set Pz) (y : Pz) (ι : E →ₗᵢ[ℝ] Pz) (ι' : K →ₗᵢ[ℝ] Pz) (s t : ℝ)
          (u : E → K),
        (∀ a b, inner ℝ (ι a) (ι' b) = 0) → (∀ z : Pz, ∃ a b, z = ι a + ι' b) → 0 < s → 0 < t →
        {z : Pz | ∃ a ∈ ball (0 : E) s, ∃ b ∈ ball (0 : K) t, z = y + ι a + ι' b} ⊆ U →
        ContDiffOn ℝ 1 u (ball 0 s) → (∀ a ∈ ball (0 : E) s, ‖u a‖ < t) →
        M ∩ {z : Pz | ∃ a ∈ ball (0 : E) s, ∃ b ∈ ball (0 : K) t, z = y + ι a + ι' b} =
          (fun a => y + ι a + ι' (u a)) '' ball 0 s →
        (∀ a ∈ ball (0 : E) s,
          T (y + ι a + ι' (u a)) = Set.range (fderiv ℝ (fun a => y + ι a + ι' (u a)) a)) →
        (∀ X : Pz → Pz, ContDiff ℝ 1 X → HasCompactSupport X → tsupport X ⊆ U →
          ∫ x in M, LinearMap.trace ℝ Pz ((Submodule.span ℝ (T x)).starProjection.toLinearMap ∘ₗ
            (fderiv ℝ X x).toLinearMap) ∂μHE[n] = 0) →
        ∀ ζ : E → K, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : E) s →
        ∫ x in ball (0 : E) s, ∑ j, inner ℝ (fderiv ℝ u x (e j)) (fderiv ℝ ζ x (e j)) ∂ν =
          ∫ x in ball (0 : E) s, ∑ j, inner ℝ (G (fderiv ℝ u x) (e j)) (fderiv ℝ ζ x (e j)) ∂ν := by
    intro E K _ _ _ _ _ _ _ _ _ _
    -- `g p = 1 + p* p`, `R p = (g p)⁻¹`, `J p = √det (g p)`, `G p = p ∘ (1 - J p R p)`
    have hadj : IsBoundedLinearMap ℝ (fun p : E →L[ℝ] K => ContinuousLinearMap.adjoint p) :=
      ⟨⟨fun p q => LinearIsometryEquiv.map_add _ p q, fun c p => by
        rw [LinearIsometryEquiv.map_smulₛₗ, starRingEnd_apply, star_trivial]⟩,
        ⟨1, one_pos, fun p => by rw [LinearIsometryEquiv.norm_map, one_mul]⟩⟩
    obtain ⟨g, hg⟩ : ∃ g : (E →L[ℝ] K) → (E →L[ℝ] E),
        g = fun p => 1 + ContinuousLinearMap.adjoint p ∘L p := ⟨_, rfl⟩
    have hgp : ∀ p, g p = 1 + ContinuousLinearMap.adjoint p ∘L p := fun p => by rw [hg]
    have g_smooth : ContDiff ℝ (⊤ : ℕ∞) g := by
      rw [hg]; exact contDiff_const.add (hadj.contDiff.clm_comp contDiff_id)
    have det_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun T : E →L[ℝ] E => T.det) := by
      let b := Module.finBasis ℝ E
      have h : (fun T : E →L[ℝ] E => T.det) = fun T => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, b.coord (σ i) (T (b i)) := by
        funext T
        rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Units.smul_def, zsmul_eq_mul]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [LinearMap.toMatrix_apply, Module.Basis.coord_apply]
        rfl
      rw [h]
      refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
      exact ((LinearMap.toContinuousLinearMap (b.coord (σ i))).comp
        (ContinuousLinearMap.apply ℝ E (b i))).contDiff
    have g_unit : ∀ p, IsUnit (g p) := by
      intro p
      have hinj : Function.Injective (g p) := by
        intro v w hvw
        have h2 : inner ℝ (g p (v - w)) (v - w) = inner ℝ (v - w) (v - w) +
            inner ℝ (p (v - w)) (p (v - w)) := by
          rw [hgp, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
            ContinuousLinearMap.comp_apply, inner_add_left, ContinuousLinearMap.adjoint_inner_left]
        rw [ContinuousLinearMap.map_sub, hvw, sub_self, inner_zero_left, real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq] at h2
        have h3 : ‖v - w‖ ^ 2 = 0 :=
          le_antisymm (le_of_add_le_of_nonneg_left h2.symm.le (sq_nonneg _)) (sq_nonneg _)
        exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))
      let e := LinearEquiv.ofInjectiveEndo (g p : E →ₗ[ℝ] E) hinj
      refine ⟨⟨g p, LinearMap.toContinuousLinearMap e.symm.toLinearMap, ?_, ?_⟩, rfl⟩
      · ext1 x
        exact e.apply_symm_apply x
      · ext1 x
        exact e.symm_apply_apply x
    obtain ⟨J, hJ⟩ : ∃ J : (E →L[ℝ] K) → ℝ, J = fun p => Real.sqrt (g p).det := ⟨_, rfl⟩
    have J_smooth : ContDiff ℝ (⊤ : ℕ∞) J := by
      rw [contDiff_iff_contDiffAt]
      intro p
      rw [hJ]
      exact (Real.contDiffAt_sqrt (((g_unit p).map ContinuousLinearMap.toLinearMapRingHom).map
        LinearMap.det).ne_zero).comp p (det_smooth.comp g_smooth).contDiffAt
    obtain ⟨R, hR⟩ : ∃ R : (E →L[ℝ] K) → (E →L[ℝ] E), R = fun p => Ring.inverse (g p) := ⟨_, rfl⟩
    have R_smooth : ContDiff ℝ (⊤ : ℕ∞) R := by
      rw [contDiff_iff_contDiffAt]
      intro p
      have h1 := contDiffAt_ringInverse ℝ (n := (⊤ : ℕ∞)) (g_unit p).unit
      rw [IsUnit.unit_spec] at h1
      rw [hR]
      exact h1.comp p g_smooth.contDiffAt
    have hgR : ∀ p, (1 + ContinuousLinearMap.adjoint p ∘L p) ∘L R p = 1 := fun p => by
      rw [← hgp, hR]; exact Ring.mul_inverse_cancel _ (g_unit p)
    have hRadj : ∀ p, ContinuousLinearMap.adjoint (R p) = R p := fun p => by
      have hsa : IsSelfAdjoint (g p) := by
        rw [hgp]
        exact (IsSelfAdjoint.one _).add (ContinuousLinearMap.isSelfAdjoint_iff'.2
          (by rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]))
      rw [hR]
      exact ContinuousLinearMap.isSelfAdjoint_iff'.mp ((isSelfAdjoint_ringInverse_iff (g_unit p)).2 hsa)
    have hJdef : ∀ p, J p = Real.sqrt (1 + ContinuousLinearMap.adjoint p ∘L p).det := fun p => by
      rw [hJ]
      show Real.sqrt (g p).det = _
      rw [hgp]
    have hJc : Continuous J := J_smooth.continuous
    have hRc : Continuous R := R_smooth.continuous
    obtain ⟨G, hG⟩ : ∃ G : (E →L[ℝ] K) → (E →L[ℝ] K), G = fun p => p.comp (1 - J p • R p) :=
      ⟨_, rfl⟩
    have hGeq : ∀ p, G p = p.comp (1 - J p • R p) := fun p => by rw [hG]
    have K_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun p => 1 - J p • R p) :=
      contDiff_const.sub (J_smooth.smul R_smooth)
    have K0 : 1 - J 0 • R 0 = 0 := by
      have g0 : g 0 = 1 := by rw [hgp, ContinuousLinearMap.comp_zero, add_zero]
      have hJ0 : J 0 = 1 := by
        rw [hJ]
        show Real.sqrt (LinearMap.det ((g 0 : E →L[ℝ] E) : E →ₗ[ℝ] E)) = 1
        rw [g0, ContinuousLinearMap.toLinearMap_one, map_one, Real.sqrt_one]
      rw [hJ0, hR]
      show 1 - (1 : ℝ) • Ring.inverse (g 0) = 0
      rw [g0, Ring.inverse_one, one_smul, sub_self]
    have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by rw [hG]; exact contDiff_id.clm_comp K_smooth
    have hG0 : G 0 = 0 := by rw [hGeq, ContinuousLinearMap.zero_comp]
    have hGd : fderiv ℝ G 0 = 0 := by
      refine HasFDerivAt.fderiv ?_
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
      obtain ⟨δ, hδ, hK⟩ := Metric.continuous_iff.1 K_smooth.continuous 0 c hc
      filter_upwards [Metric.ball_mem_nhds (0 : E →L[ℝ] K) hδ] with h hh
      have hK' := hK h hh
      rw [K0, dist_zero_right] at hK'
      rw [zero_add, hG0, sub_zero, ContinuousLinearMap.zero_apply, sub_zero, hGeq, mul_comm]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hK'.le (norm_nonneg _))
    refine ⟨G, hGs, hG0, hGd, ?_⟩
    intro Pz _ _ _ _ _ ι₀ _ bE e he n hn ν hν U M T y ι ι' s t u
      hperp hspan hs ht hZU hu hut hMZ htan hstat ζ hζ hζc hζs
    subst hn hν
    -- the coordinate projections `π = ι*`, `π' = ι'*`
    obtain ⟨π, hπ⟩ : ∃ π : Pz →L[ℝ] E, π = ContinuousLinearMap.adjoint ι.toContinuousLinearMap :=
      ⟨_, rfl⟩
    obtain ⟨π', hπ'⟩ : ∃ π' : Pz →L[ℝ] K, π' = ContinuousLinearMap.adjoint ι'.toContinuousLinearMap :=
      ⟨_, rfl⟩
    have hπι : ∀ a, π (ι a) = a := fun a => by
      rw [hπ]; exact congrArg (fun T' : E →L[ℝ] E => T' a) (LinearIsometry.adjoint_comp_self ι)
    have hπ'ι' : ∀ b, π' (ι' b) = b := fun b => by
      rw [hπ']; exact congrArg (fun T' : K →L[ℝ] K => T' b) (LinearIsometry.adjoint_comp_self ι')
    have hπι' : ∀ b, π (ι' b) = 0 := fun b => by
      refine ext_inner_left ℝ fun a => ?_
      rw [hπ, ContinuousLinearMap.adjoint_inner_right, inner_zero_right]
      exact hperp a b
    have hπ'ι : ∀ a, π' (ι a) = 0 := fun a => by
      refine ext_inner_left ℝ fun b => ?_
      rw [hπ', ContinuousLinearMap.adjoint_inner_right, inner_zero_right, real_inner_comm]
      exact hperp a b
    have hdecomp : ∀ z, z = ι (π z) + ι' (π' z) := by
      intro z
      obtain ⟨a, b, rfl⟩ := hspan z
      rw [map_add π, map_add π', hπι, hπι', hπ'ι, hπ'ι', add_zero, zero_add]
    -- the graph map `F a = y + ι a + ι' (u a)`, the ball `B` and the cylinder `Z`
    obtain ⟨F, hF⟩ : ∃ F : E → Pz, F = fun a => y + ι a + ι' (u a) := ⟨_, rfl⟩
    have hFa : ∀ a, F a = y + ι a + ι' (u a) := fun a => by rw [hF]
    have hπF : ∀ a, π (F a - y) = a := fun a => by
      rw [hFa, add_assoc, add_sub_cancel_left, map_add, hπι, hπι', add_zero]
    have hπ'F : ∀ a, π' (F a - y) = u a := fun a => by
      rw [hFa, add_assoc, add_sub_cancel_left, map_add, hπ'ι, hπ'ι', zero_add]
    have hFinj : Injective F := fun a b h => by rw [← hπF a, ← hπF b, h]
    obtain ⟨B, hB⟩ : ∃ B : Set E, B = ball 0 s := ⟨_, rfl⟩
    rw [← hB] at hu hut hZU hMZ htan hζs ⊢
    have hBopen : IsOpen B := hB ▸ isOpen_ball
    have hBmeas : MeasurableSet B := hBopen.measurableSet
    obtain ⟨Z, hZdef⟩ : ∃ Z : Set Pz,
        Z = {z : Pz | ∃ a ∈ B, ∃ b ∈ ball (0 : K) t, z = y + ι a + ι' b} := ⟨_, rfl⟩
    rw [← hZdef] at hZU hMZ
    rw [← hF] at hMZ
    have hZ' : ∀ z, z ∈ Z ↔ π (z - y) ∈ B ∧ π' (z - y) ∈ ball (0 : K) t := by
      intro z
      rw [hZdef]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rw [add_assoc, add_sub_cancel_left, map_add π, map_add π', hπι, hπι', hπ'ι, hπ'ι',
          add_zero, zero_add]
        exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        refine ⟨π (z - y), ha, π' (z - y), hb, ?_⟩
        rw [add_assoc, ← hdecomp, add_sub_cancel]
    have hZopen : IsOpen Z := by
      have : Z = (fun z => π (z - y)) ⁻¹' B ∩ (fun z => π' (z - y)) ⁻¹' ball (0 : K) t :=
        Set.ext hZ'
      rw [this]
      exact (hBopen.preimage (π.continuous.comp (continuous_id.sub continuous_const))).inter
        (isOpen_ball.preimage (π'.continuous.comp (continuous_id.sub continuous_const)))
    -- derivative of `F`: `L p = ι + ι' ∘ p` at `p = Du(a)`
    obtain ⟨L, hL⟩ : ∃ L : (E →L[ℝ] K) → (E →L[ℝ] Pz),
        L = fun p => ι.toContinuousLinearMap + ι'.toContinuousLinearMap.comp p := ⟨_, rfl⟩
    have hFderiv : ∀ a ∈ B, HasFDerivAt F (L (fderiv ℝ u a)) a := by
      intro a ha
      have hua : HasFDerivAt u (fderiv ℝ u a) a :=
        ((hu.differentiableOn one_ne_zero a ha).differentiableAt (hBopen.mem_nhds ha)).hasFDerivAt
      rw [hF, hL]
      exact (((hasFDerivAt_const y a).add ι.toContinuousLinearMap.hasFDerivAt).add
        (ι'.toContinuousLinearMap.hasFDerivAt.comp a hua)).congr_fderiv (by rw [zero_add])
    have hDF : ∀ a ∈ B, fderiv ℝ F a = L (fderiv ℝ u a) := fun a ha => (hFderiv a ha).fderiv
    have htan' : ∀ a ∈ B, T (F a) = Set.range (L (fderiv ℝ u a)) := by
      intro a ha
      rw [← hDF a ha, hFa, hF]
      exact htan a ha
    -- Gram identity `(L p)* L p = 1 + p* p`, and consequences
    have hgram : ∀ p, ContinuousLinearMap.adjoint (L p) ∘L L p =
        1 + ContinuousLinearMap.adjoint p ∘L p := by
      intro p
      refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply,
        inner_add_left, ContinuousLinearMap.adjoint_inner_left, hL]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap]
      rw [inner_add_left, inner_add_right, inner_add_right, LinearIsometry.inner_map_map,
        LinearIsometry.inner_map_map, hperp, real_inner_comm (ι w), hperp, add_zero, zero_add]
    have hnormsq : ∀ p (x : E), ‖L p x‖ ^ 2 = ‖x‖ ^ 2 + ‖p x‖ ^ 2 := by
      intro p x
      rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.comp_apply, hgram p, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.one_apply, ContinuousLinearMap.comp_apply, inner_add_left,
        ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq]
    have hanti : ∀ p (x : E), ‖x‖ ≤ ‖L p x‖ := fun p x =>
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (by rw [hnormsq]; exact le_add_of_nonneg_right (sq_nonneg _))
    have hLnorm : ∀ p p', ‖L p' - L p‖ = ‖p' - p‖ := by
      intro p p'
      have : L p' - L p = ι'.toContinuousLinearMap.comp (p' - p) := by
        rw [hL, ContinuousLinearMap.comp_sub, add_sub_add_left_eq_sub]
      rw [this, LinearIsometry.norm_toContinuousLinearMap_comp]
    have hLinj : ∀ p, Injective (L p) := fun p x x' h => by
      have := hanti p (x - x')
      rw [map_sub, h, sub_self, norm_zero] at this
      exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    -- the linear area formula (Simon (3.1)) for injective `A : E → Pz`
    have hLAF : ∀ A : E →L[ℝ] Pz, Injective A → ∀ S : Set E,
        μHE[Module.finrank ℝ E] (A '' S) =
          ENNReal.ofReal (Real.sqrt (ContinuousLinearMap.adjoint A ∘L A).det) *
            μHE[Module.finrank ℝ E] S ∧ 0 < (ContinuousLinearMap.adjoint A ∘L A).det := by
      intro A hA S
      clear * - hA
      set V := LinearMap.range (A : E →ₗ[ℝ] Pz) with hVdef
      have hV : Module.finrank ℝ V = Module.finrank ℝ E := by
        rw [hVdef, LinearMap.finrank_range_of_inj hA]
      let e : V ≃ₗᵢ[ℝ] E := ((stdOrthonormalBasis ℝ V).reindex (finCongr hV)).equiv
        (stdOrthonormalBasis ℝ E) (Equiv.refl _)
      let M₀ : E →ₗ[ℝ] E := e.toLinearMap ∘ₗ (A : E →ₗ[ℝ] Pz).rangeRestrict
      let ψ : E →ₗᵢ[ℝ] Pz := V.subtypeₗᵢ.comp e.symm.toLinearIsometry
      have hψM : ∀ x, ψ (M₀ x) = A x := by
        intro x
        show ((e.symm (e ((A : E →ₗ[ℝ] Pz).rangeRestrict x)) : V) : Pz) = A x
        rw [LinearIsometryEquiv.symm_apply_apply]
        rfl
      have himg : A '' S = ψ '' (M₀ '' S) := by
        rw [image_image]
        simp only [hψM]
      have hadjdet : LinearMap.det (LinearMap.adjoint M₀) = LinearMap.det M₀ := by
        let v := stdOrthonormalBasis ℝ E
        rw [← LinearMap.det_toMatrix v.toBasis, ← LinearMap.det_toMatrix v.toBasis,
          LinearMap.toMatrix_adjoint v v, Matrix.det_conjTranspose, star_trivial]
      have h1 : ContinuousLinearMap.adjoint A ∘L A = ContinuousLinearMap.adjoint
          (LinearMap.toContinuousLinearMap M₀) ∘L LinearMap.toContinuousLinearMap M₀ := by
        refine ContinuousLinearMap.ext fun v => ext_inner_right ℝ fun w => ?_
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
          ← hψM v, ← hψM w, LinearIsometry.inner_map_map]
        rfl
      have hdetsq : (ContinuousLinearMap.adjoint A ∘L A).det = (LinearMap.det M₀) ^ 2 := by
        have h2 : ((ContinuousLinearMap.adjoint A ∘L A : E →L[ℝ] E) : E →ₗ[ℝ] E) =
            LinearMap.adjoint M₀ ∘ₗ M₀ := by
          rw [h1]; rfl
        show LinearMap.det ((ContinuousLinearMap.adjoint A ∘L A : E →L[ℝ] E) : E →ₗ[ℝ] E) = _
        rw [h2, LinearMap.det_comp, hadjdet, sq]
      have hdet0 : LinearMap.det M₀ ≠ 0 := by
        have hinj : Injective M₀ := by
          intro x y hxy
          apply hA
          rw [← hψM x, ← hψM y, hxy]
        exact ((LinearMap.isUnit_iff_ker_eq_bot M₀).mpr (LinearMap.ker_eq_bot.mpr hinj)).map
          LinearMap.det |>.ne_zero
      refine ⟨?_, by rw [hdetsq]; positivity⟩
      rw [himg, ψ.isometry.euclideanHausdorffMeasure_image,
        MeasureTheory.Measure.addHaar_image_linearMap, hdetsq, Real.sqrt_sq_eq_abs]
    have hJpos : ∀ p, 0 < J p := fun p => by
      rw [hJdef, ← hgram p]; exact Real.sqrt_pos.2 (hLAF (L p) (hLinj p) ∅).2
    have hLAF' : ∀ p (S : Set E), μHE[Module.finrank ℝ E] (L p '' S) =
        ENNReal.ofReal (J p) * μHE[Module.finrank ℝ E] S := fun p S => by
      rw [hJdef, ← hgram p]; exact (hLAF (L p) (hLinj p) S).1
    have hFinjB : InjOn F B := hFinj.injOn
    -- the area formula (Simon (3.2)) for the injective `C¹` graph map `F`
    have AF1 : ∀ E₀ ⊆ B, MeasurableSet E₀ → μHE[Module.finrank ℝ E] (F '' E₀) =
        ∫⁻ a in E₀, ENNReal.ofReal (J (fderiv ℝ u a)) ∂(μHE[Module.finrank ℝ E] : Measure E) := by
      clear * - hJc hJpos hLnorm hLAF' hanti hFderiv hFinjB
      intro E₀ hEB hE
      -- comparison of pairwise distances gives comparison of image measures
      have hdist : ∀ (f g : E → Pz) (s : Set E) (K : NNReal), InjOn g s →
          (∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist (g x) (g y)) →
          μHE[(Module.finrank ℝ E)] (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ E) * μHE[(Module.finrank ℝ E)] (g '' s) := by
        intro f g s K hg hfg
        let h : Pz → Pz := f ∘ invFunOn g s
        have hh : LipschitzOnWith K h (g '' s) := by
          rw [lipschitzOnWith_iff_dist_le_mul]
          rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
          simpa only [h, comp_apply, hg.leftInvOn_invFunOn hx, hg.leftInvOn_invFunOn hy] using
            hfg x hx y hy
        have himage : h '' (g '' s) = f '' s := by
          rw [show h = f ∘ invFunOn g s from rfl, image_comp, hg.invFunOn_image Subset.rfl]
        simpa only [himage] using
          Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn (Module.finrank ℝ E) hh
      have hLinj : ∀ p, Injective (L p) := by
        intro p x y hxy
        have := hanti p (x - y)
        rw [map_sub, hxy, sub_self, norm_zero] at this
        exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
      -- the sharp upper estimate on a piece
      have hupper : ∀ p (s : Set E) (δ : NNReal), ApproximatesLinearOn F (L p) s δ →
          μHE[(Module.finrank ℝ E)] (F '' s) ≤ ((1 + δ : NNReal) : ℝ≥0∞) ^ (Module.finrank ℝ E) * (ENNReal.ofReal (J p) * (μHE[Module.finrank ℝ E] : Measure E) s) := by
        intro p s δ hf
        rw [← hLAF' p s]
        refine hdist F (L p) s (1 + δ) (hLinj p).injOn (fun x hx y hy => ?_)
        have hb : ‖x - y‖ ≤ ‖L p x - L p y‖ := by simpa [map_sub] using hanti p (x - y)
        have herr : ‖F x - F y - (L p x - L p y)‖ ≤ δ * ‖L p x - L p y‖ := by
          calc _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
            _ ≤ δ * ‖L p x - L p y‖ := mul_le_mul_of_nonneg_left hb δ.2
        simp only [dist_eq_norm, NNReal.coe_add, NNReal.coe_one]
        calc ‖F x - F y‖ ≤ ‖F x - F y - (L p x - L p y)‖ + ‖L p x - L p y‖ := norm_le_norm_sub_add _ _
          _ ≤ δ * ‖L p x - L p y‖ + ‖L p x - L p y‖ := add_le_add herr le_rfl
          _ = (1 + δ) * ‖L p x - L p y‖ := by ring
      -- the sharp lower estimate on a piece
      have hlower : ∀ p (s : Set E) (δ : NNReal), ApproximatesLinearOn F (L p) s δ → δ < 1 →
          ENNReal.ofReal (J p) * (μHE[Module.finrank ℝ E] : Measure E) s ≤ (((1 - δ)⁻¹ : NNReal) : ℝ≥0∞) ^ (Module.finrank ℝ E) * μHE[(Module.finrank ℝ E)] (F '' s) := by
        intro p s δ hf hδ
        have hδR : (δ : ℝ) < 1 := hδ
        have hd : ∀ x ∈ s, ∀ y ∈ s, dist (L p x) (L p y) ≤ ((1 - δ)⁻¹ : NNReal) * dist (F x) (F y) := by
          intro x hx y hy
          have hb : ‖x - y‖ ≤ ‖L p x - L p y‖ := by simpa [map_sub] using hanti p (x - y)
          have herr : ‖F x - F y - (L p x - L p y)‖ ≤ δ * ‖L p x - L p y‖ := by
            calc _ ≤ δ * ‖x - y‖ := by simpa only [map_sub] using hf x hx y hy
              _ ≤ δ * ‖L p x - L p y‖ := mul_le_mul_of_nonneg_left hb δ.2
          have htri : ‖L p x - L p y‖ ≤ ‖F x - F y‖ + ‖F x - F y - (L p x - L p y)‖ := by
            simpa only [norm_sub_rev, add_comm] using norm_le_norm_sub_add (L p x - L p y) (F x - F y)
          simp only [dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hδ.le, NNReal.coe_one, inv_mul_eq_div]
          rw [le_div_iff₀ (sub_pos.mpr hδR)]
          linarith
        have hFinjB' : InjOn F s := by
          intro x hx y hy hxy
          apply hLinj p
          apply dist_le_zero.mp
          simpa only [hxy, dist_self, mul_zero] using hd x hx y hy
        rw [← hLAF' p s]
        exact hdist (L p) F s _ hFinjB' hd
      -- derivative control at density points of a piece
      have hdens : ∀ (s : Set E) (A : E →L[ℝ] Pz) (δ : NNReal),
          ApproximatesLinearOn F A s δ → MeasurableSet s → s ⊆ B →
          ∀ᵐ x ∂((μHE[Module.finrank ℝ E] : Measure E).restrict s), ‖L (fderiv ℝ u x) - A‖₊ ≤ δ := by
        intro s A δ hf hs hsB
        have hf' : ∀ x ∈ s, HasFDerivWithinAt F (L (fderiv ℝ u x)) s x :=
          fun x hx => (hFderiv x (hsB hx)).hasFDerivWithinAt
        filter_upwards [Besicovitch.ae_tendsto_measure_inter_div (μHE[Module.finrank ℝ E] : Measure E) s,
          ae_restrict_mem hs]
        intro x hx xs
        apply ContinuousLinearMap.opNorm_le_bound _ δ.2 fun z => ?_
        suffices H : ∀ ε, 0 < ε → ‖(L (fderiv ℝ u x) - A) z‖ ≤ (δ + ε) * (‖z‖ + ε) + ‖L (fderiv ℝ u x) - A‖ * ε by
          have :
              Tendsto (fun ε : ℝ => ((δ : ℝ) + ε) * (‖z‖ + ε) + ‖L (fderiv ℝ u x) - A‖ * ε) (𝓝[>] 0)
                (𝓝 ((δ + 0) * (‖z‖ + 0) + ‖L (fderiv ℝ u x) - A‖ * 0)) :=
            Tendsto.mono_left (Continuous.tendsto (((continuous_const.add continuous_id).mul
              (continuous_const.add continuous_id)).add (continuous_const.mul continuous_id)) 0)
              nhdsWithin_le_nhds
          simp only [add_zero, mul_zero] at this
          apply le_of_tendsto_of_tendsto tendsto_const_nhds this
          filter_upwards [self_mem_nhdsWithin]
          exact H
        intro ε εpos
        open scoped Pointwise in
        have B₁ : ∀ᶠ r in 𝓝[>] (0 : ℝ), (s ∩ ({x} + r • closedBall z ε)).Nonempty :=
          MeasureTheory.Measure.eventually_nonempty_inter_smul_of_density_one (μHE[Module.finrank ℝ E] : Measure E) s x hx _
            measurableSet_closedBall (measure_closedBall_pos (μHE[Module.finrank ℝ E] : Measure E) z εpos).ne'
        obtain ⟨ρ, ρpos, hρ⟩ :
            ∃ ρ > 0, ball x ρ ∩ s ⊆ {y : E | ‖F y - F x - (L (fderiv ℝ u x)) (y - x)‖ ≤ ε * ‖y - x‖} :=
          mem_nhdsWithin_iff.1 (Asymptotics.isLittleO_iff.mp (hf' x xs).isLittleO εpos)
        open scoped Pointwise in
        have B₂ : ∀ᶠ r in 𝓝[>] (0 : ℝ), {x} + r • closedBall z ε ⊆ ball x ρ := by
          apply nhdsWithin_le_nhds
          exact eventually_singleton_add_smul_subset isBounded_closedBall (ball_mem_nhds x ρpos)
        open scoped Pointwise in
        obtain ⟨r, ⟨y, ⟨ys, hy⟩⟩, rρ, rpos⟩ :
            ∃ r : ℝ, (s ∩ ({x} + r • closedBall z ε)).Nonempty ∧
              {x} + r • closedBall z ε ⊆ ball x ρ ∧ 0 < r :=
          (B₁.and (B₂.and self_mem_nhdsWithin)).exists
        open scoped Pointwise in
        obtain ⟨a, az, ya⟩ : ∃ a, a ∈ closedBall z ε ∧ y = x + r • a := by
          simp only [mem_smul_set, image_add_left, mem_preimage, singleton_add] at hy
          rcases hy with ⟨a, az, ha⟩
          exact ⟨a, az, by simp only [ha, add_neg_cancel_left]⟩
        have norm_a : ‖a‖ ≤ ‖z‖ + ε :=
          calc
            ‖a‖ = ‖z + (a - z)‖ := by simp only [add_sub_cancel]
            _ ≤ ‖z‖ + ‖a - z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + ε := by grw [mem_closedBall_iff_norm.1 az]
        have I : r * ‖(L (fderiv ℝ u x) - A) a‖ ≤ r * (δ + ε) * (‖z‖ + ε) :=
          calc
            r * ‖(L (fderiv ℝ u x) - A) a‖ = ‖(L (fderiv ℝ u x) - A) (r • a)‖ := by
              simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
            _ = ‖F y - F x - A (y - x) - (F y - F x - (L (fderiv ℝ u x)) (y - x))‖ := by
              simp only [ya, add_sub_cancel_left, sub_sub_sub_cancel_left, FunLike.coe_sub,
                Pi.sub_apply, map_smul, smul_sub]
            _ ≤ ‖F y - F x - A (y - x)‖ + ‖F y - F x - (L (fderiv ℝ u x)) (y - x)‖ := norm_sub_le _ _
            _ ≤ δ * ‖y - x‖ + ε * ‖y - x‖ := (add_le_add (hf _ ys _ xs) (hρ ⟨rρ hy, ys⟩))
            _ = r * (δ + ε) * ‖a‖ := by
              simp only [ya, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg rpos.le]
              ring
            _ ≤ r * (δ + ε) * (‖z‖ + ε) := by gcongr
        calc
          ‖(L (fderiv ℝ u x) - A) z‖ = ‖(L (fderiv ℝ u x) - A) a + (L (fderiv ℝ u x) - A) (z - a)‖ := by
            congr 1
            simp only [FunLike.coe_sub, map_sub, Pi.sub_apply]
            abel
          _ ≤ ‖(L (fderiv ℝ u x) - A) a‖ + ‖(L (fderiv ℝ u x) - A) (z - a)‖ := norm_add_le _ _
          _ ≤ (δ + ε) * (‖z‖ + ε) + ‖L (fderiv ℝ u x) - A‖ * ‖z - a‖ := by
            apply add_le_add
            · rw [mul_assoc] at I; exact (mul_le_mul_iff_right₀ rpos).1 I
            · apply ContinuousLinearMap.le_opNorm
          _ ≤ (δ + ε) * (‖z‖ + ε) + ‖L (fderiv ℝ u x) - A‖ * ε := by
            rw [mem_closedBall_iff_norm'] at az
            gcongr
      rcases eq_empty_or_nonempty E₀ with rfl | hEne
      · simp
      have hf' : ∀ x ∈ E₀, HasFDerivWithinAt F (L (fderiv ℝ u x)) E₀ x :=
        fun x hx => (hFderiv x (hEB hx)).hasFDerivWithinAt
      have hLinjp : ∀ p p', L p = L p' → p = p' := by
        intro p p' h
        have := hLnorm p p'
        rw [h, sub_self, norm_zero] at this
        exact (sub_eq_zero.mp (norm_eq_zero.mp this.symm)).symm
      have hcomp : ∀ q : NNReal, 1 < q →
          μHE[(Module.finrank ℝ E)] (F '' E₀) ≤ (q : ℝ≥0∞) ^ 2 * ∫⁻ a in E₀, ENNReal.ofReal (J (fderiv ℝ u a)) ∂(μHE[Module.finrank ℝ E] : Measure E) ∧
          (∫⁻ a in E₀, ENNReal.ofReal (J (fderiv ℝ u a)) ∂(μHE[Module.finrank ℝ E] : Measure E)) ≤ (q : ℝ≥0∞) ^ 2 * μHE[(Module.finrank ℝ E)] (F '' E₀) := by
        intro q hq
        have hchoice : ∀ A : E →L[ℝ] Pz, ∃ δ : NNReal, 0 < δ ∧ ∀ p, A = L p →
            (∀ p', ‖p' - p‖ ≤ δ → ENNReal.ofReal (J p') ≤ q * ENNReal.ofReal (J p) ∧
                ENNReal.ofReal (J p) ≤ q * ENNReal.ofReal (J p')) ∧
            (∀ s, ApproximatesLinearOn F A s δ →
                μHE[(Module.finrank ℝ E)] (F '' s) ≤ q * (ENNReal.ofReal (J p) * (μHE[Module.finrank ℝ E] : Measure E) s) ∧
                ENNReal.ofReal (J p) * (μHE[Module.finrank ℝ E] : Measure E) s ≤ q * μHE[(Module.finrank ℝ E)] (F '' s)) := by
          intro A
          by_cases hA : ∃ p, A = L p
          · obtain ⟨p, rfl⟩ := hA
            have hqR : (1 : ℝ) < q := hq
            have hJp := hJpos p
            have hmul : J p < (q : ℝ) * J p := lt_mul_of_one_lt_left hJp hqR
            have hnear : ∀ᶠ p' in 𝓝 p, J p' < (q : ℝ) * J p ∧ J p < (q : ℝ) * J p' :=
              (hJc.continuousAt.eventually_lt continuousAt_const hmul).and
                (continuousAt_const.eventually_lt (continuousAt_const.mul hJc.continuousAt) hmul)
            obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
            have hsmall : ∀ᶠ δ : NNReal in 𝓝 0, δ < 1 := eventually_lt_nhds zero_lt_one
            have hup : ∀ᶠ δ : NNReal in 𝓝 0, (1 + δ) ^ (Module.finrank ℝ E) < q :=
              ((continuousAt_const.add continuousAt_id).pow _).eventually_lt continuousAt_const
                (by simpa using hq)
            have hlow : ∀ᶠ δ : NNReal in 𝓝 0, ((1 - δ)⁻¹) ^ (Module.finrank ℝ E) < q := by
              apply ContinuousAt.eventually_lt _ continuousAt_const (by simpa using hq)
              apply ContinuousAt.pow
              apply ContinuousAt.inv₀
              · exact continuousAt_const.sub continuousAt_id
              · simp
            have hεδ : ∀ᶠ δ : NNReal in 𝓝 0, (δ : ℝ) < ε :=
              NNReal.continuous_coe.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
            have hevent : ∀ᶠ δ : NNReal in 𝓝[>] 0,
                0 < δ ∧ δ < 1 ∧ (1 + δ) ^ (Module.finrank ℝ E) < q ∧ ((1 - δ)⁻¹) ^ (Module.finrank ℝ E) < q ∧ (δ : ℝ) < ε := by
              filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
                hup.filter_mono nhdsWithin_le_nhds, hlow.filter_mono nhdsWithin_le_nhds,
                hεδ.filter_mono nhdsWithin_le_nhds] with δ h1 h2 h3 h4 h5
              exact ⟨h1, h2, h3, h4, h5⟩
            obtain ⟨δ, hδ0, hδ1, hδup, hδlow, hδε⟩ := hevent.exists
            refine ⟨δ, hδ0, fun p₀ hp₀ => ?_⟩
            obtain rfl := hLinjp p p₀ hp₀
            refine ⟨fun p' hp' => ?_, fun s hs => ⟨?_, ?_⟩⟩
            · have hd : dist p' p < ε := by rw [dist_eq_norm]; exact hp'.trans_lt hδε
              obtain ⟨h1, h2⟩ := hnear hd
              constructor
              · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
                exact ENNReal.ofReal_le_ofReal h1.le
              · rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg q)]
                exact ENNReal.ofReal_le_ofReal h2.le
            · refine (hupper p s δ hs).trans ?_
              gcongr
              exact_mod_cast hδup.le
            · refine (hlower p s δ hs hδ1).trans ?_
              gcongr
              exact_mod_cast hδlow.le
          · exact ⟨1, one_pos, fun p hp => (hA ⟨p, hp⟩).elim⟩
        choose δ hδpos hδ using hchoice
        obtain ⟨t, A, hdisj, ht, hcover, happrox, hactual⟩ :=
          exists_partition_approximatesLinearOn_of_hasFDerivWithinAt F E₀ (fun x => L (fderiv ℝ u x)) hf' δ
            (fun A => (hδpos A).ne')
        have hpn : ∀ n, ∃ p, A n = L p := fun n => by
          obtain ⟨y, _, hy⟩ := hactual hEne n
          exact ⟨fderiv ℝ u y, hy⟩
        choose pn hpn using hpn
        have hseq : E₀ = ⋃ i, E₀ ∩ t i := by
          rw [← inter_iUnion]
          exact Subset.antisymm (subset_inter Subset.rfl hcover) inter_subset_left
        have hsumimage : μHE[(Module.finrank ℝ E)] (F '' E₀) = ∑' i, μHE[(Module.finrank ℝ E)] (F '' (E₀ ∩ t i)) := by
          conv_lhs => rw [hseq, image_iUnion]
          apply measure_iUnion
          · intro i j hij
            exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hdisj hij))
              (hFinjB.mono hEB) inter_subset_left inter_subset_left
          · intro i
            apply (hE.inter (ht i)).image_of_continuousOn_injOn
            · exact fun x hx => (hFderiv x (hEB hx.1)).continuousAt.continuousWithinAt
            · exact (hFinjB.mono hEB).mono inter_subset_left
        have hsumintegral : (∫⁻ x in E₀, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E)) =
            ∑' i, ∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E) := by
          conv_lhs => rw [hseq]
          exact lintegral_iUnion (fun i => hE.inter (ht i))
            (pairwise_disjoint_mono hdisj (fun _ => inter_subset_right)) _
        have hpiece : ∀ i, μHE[(Module.finrank ℝ E)] (F '' (E₀ ∩ t i)) ≤
              (q : ℝ≥0∞) ^ 2 * ∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E) ∧
            (∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E)) ≤
              (q : ℝ≥0∞) ^ 2 * μHE[(Module.finrank ℝ E)] (F '' (E₀ ∩ t i)) := by
          intro i
          obtain ⟨hJ, harea⟩ := hδ (A i) (pn i) (hpn i)
          obtain ⟨harea_upper, harea_lower⟩ := harea (E₀ ∩ t i) (happrox i)
          have hderiv := hdens (E₀ ∩ t i) (A i) (δ (A i)) (happrox i) (hE.inter (ht i))
            (inter_subset_left.trans hEB)
          have hderiv' : ∀ᵐ x ∂((μHE[Module.finrank ℝ E] : Measure E).restrict (E₀ ∩ t i)), ‖fderiv ℝ u x - pn i‖ ≤ δ (A i) := by
            filter_upwards [hderiv] with x hx
            have hx' : ‖L (fderiv ℝ u x) - L (pn i)‖₊ ≤ δ (A i) := by rw [← hpn i]; exact hx
            rw [← hLnorm (pn i) (fderiv ℝ u x)]
            exact_mod_cast hx'
          have hJupper : (∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E)) ≤
              q * (ENNReal.ofReal (J (pn i)) * (μHE[Module.finrank ℝ E] : Measure E) (E₀ ∩ t i)) := by
            calc _ ≤ ∫⁻ _ in E₀ ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (pn i)) ∂(μHE[Module.finrank ℝ E] : Measure E) := by
                  apply lintegral_mono_ae
                  filter_upwards [hderiv'] with x hx
                  exact (hJ (fderiv ℝ u x) hx).1
              _ = _ := by rw [setLIntegral_const, mul_assoc]
          have hJlower : ENNReal.ofReal (J (pn i)) * (μHE[Module.finrank ℝ E] : Measure E) (E₀ ∩ t i) ≤
              q * ∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E) := by
            calc _ = ∫⁻ _ in E₀ ∩ t i, ENNReal.ofReal (J (pn i)) ∂(μHE[Module.finrank ℝ E] : Measure E) := (setLIntegral_const _ _).symm
              _ ≤ ∫⁻ x in E₀ ∩ t i, (q : ℝ≥0∞) * ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E) := by
                  apply lintegral_mono_ae
                  filter_upwards [hderiv'] with x hx
                  exact (hJ (fderiv ℝ u x) hx).2
              _ = _ := lintegral_const_mul' _ _ ENNReal.coe_ne_top
          constructor
          · calc _ ≤ q * (ENNReal.ofReal (J (pn i)) * (μHE[Module.finrank ℝ E] : Measure E) (E₀ ∩ t i)) := harea_upper
              _ ≤ q * (q * ∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E)) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
          · calc _ ≤ q * (ENNReal.ofReal (J (pn i)) * (μHE[Module.finrank ℝ E] : Measure E) (E₀ ∩ t i)) := hJupper
              _ ≤ q * (q * μHE[(Module.finrank ℝ E)] (F '' (E₀ ∩ t i))) := by gcongr
              _ = _ := by rw [pow_two, mul_assoc]
        rw [hsumimage, hsumintegral]
        constructor
        · calc _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * ∫⁻ x in E₀ ∩ t i, ENNReal.ofReal (J (fderiv ℝ u x)) ∂(μHE[Module.finrank ℝ E] : Measure E) :=
                ENNReal.tsum_le_tsum (fun i => (hpiece i).1)
            _ = _ := ENNReal.tsum_mul_left
        · calc _ ≤ ∑' i, (q : ℝ≥0∞) ^ 2 * μHE[(Module.finrank ℝ E)] (F '' (E₀ ∩ t i)) :=
                ENNReal.tsum_le_tsum (fun i => (hpiece i).2)
            _ = _ := ENNReal.tsum_mul_left
      have hlimit (a : ℝ≥0∞) : Tendsto (fun q : NNReal => (q : ℝ≥0∞) ^ 2 * a) (𝓝[>] 1) (𝓝 a) := by
        have hcoe : Tendsto (fun q : NNReal => (q : ℝ≥0∞)) (𝓝[>] 1) (𝓝 1) :=
          (ENNReal.tendsto_coe.2 tendsto_id).mono_left nhdsWithin_le_nhds
        simpa only [one_pow, one_mul] using
          ENNReal.Tendsto.mul_const (ENNReal.Tendsto.pow (n := 2) hcoe) (Or.inl (by simp))
      apply le_antisymm
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).1
      · apply ge_of_tendsto (hlimit _)
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hcomp q hq).2
    -- `Hᵐ ⌞ F(B)` is the push-forward of `J(Du) dHᵐ ⌞ B`
    obtain ⟨ρ, hρ⟩ : ∃ ρ : E → ℝ≥0∞, ρ = fun a => ENNReal.ofReal (J (fderiv ℝ u a)) := ⟨_, rfl⟩
    have hρmeas : Measurable ρ := by
      rw [hρ]; exact ENNReal.measurable_ofReal.comp (hJc.measurable.comp (measurable_fderiv ℝ u))
    have hFcont : ContinuousOn F B := fun a ha => (hFderiv a ha).continuousAt.continuousWithinAt
    have hFae : AEMeasurable F (((μHE[Module.finrank ℝ E] : Measure E).restrict B).withDensity ρ) :=
      (hFcont.aemeasurable hBmeas).mono_ac (withDensity_absolutelyContinuous _ _)
    have hFBmeas : MeasurableSet (F '' B) := hBmeas.image_of_continuousOn_injOn hFcont hFinj.injOn
    have AF2 : (μHE[Module.finrank ℝ E] : Measure Pz).restrict (F '' B) =
        Measure.map F (((μHE[Module.finrank ℝ E] : Measure E).restrict B).withDensity ρ) := by
      ext A hA
      have hEmeas : MeasurableSet (F ⁻¹' A ∩ B) := by
        classical
        have hpw : Measurable (B.piecewise F (fun _ => 0)) :=
          hFcont.measurable_piecewise continuousOn_const hBmeas
        have : F ⁻¹' A ∩ B = B.piecewise F (fun _ => 0) ⁻¹' A ∩ B := by
          ext a
          simp only [mem_inter_iff, mem_preimage]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ h2], h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨by rwa [Set.piecewise_eq_of_mem _ _ _ h2] at h1, h2⟩
        rw [this]
        exact (hpw hA).inter hBmeas
      rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable hFae hA,
        withDensity_apply' _ _, Measure.restrict_restrict' hBmeas, inter_comm,
        ← image_inter_preimage, inter_comm, AF1 _ inter_subset_right hEmeas, hρ]
    -- a bound `t₀ < t` for `‖u‖` on `spt ζ`, and the cut-off `ψ`
    obtain ⟨t₀, ht₀0, ht₀t, ht₀⟩ : ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < t ∧ ∀ a ∈ tsupport ζ, ‖u a‖ ≤ t₀ := by
      rcases (tsupport ζ).eq_empty_or_nonempty with h | h
      · exact ⟨0, le_rfl, ht, fun a ha => by rw [h] at ha; exact (Set.notMem_empty a ha).elim⟩
      · obtain ⟨a₀, ha₀, hmax⟩ := hζc.isCompact.exists_isMaxOn h
          ((continuous_norm.comp_continuousOn hu.continuousOn).mono hζs)
        exact ⟨‖u a₀‖, norm_nonneg _, hut a₀ (hζs ha₀), fun a ha => isMaxOn_iff.mp hmax a ha⟩
    obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, t₁ = (t₀ + t) / 2 := ⟨_, rfl⟩
    have ht₀₁ : t₀ < t₁ := ht₁ ▸ left_lt_add_div_two.2 ht₀t
    have ht₁t : t₁ < t := ht₁ ▸ add_div_two_lt_right.2 ht₀t
    have ht₁0 : 0 < t₁ := ht₀0.trans_lt ht₀₁
    have hden : 0 < t₁ ^ 2 - t₀ ^ 2 := sub_pos.2 (pow_lt_pow_left₀ ht₀₁ ht₀0 two_ne_zero)
    obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun r => Real.smoothTransition ((t₁ ^ 2 - r) / (t₁ ^ 2 - t₀ ^ 2)) :=
      ⟨_, rfl⟩
    have hψ1 : ∀ r, r ≤ t₀ ^ 2 → ψ r = 1 := fun r hr => by
      rw [hψ]; exact Real.smoothTransition.one_of_one_le ((one_le_div hden).2 (sub_le_sub_left hr _))
    have hψ0 : ∀ r, t₁ ^ 2 ≤ r → ψ r = 0 := fun r hr => by
      rw [hψ]
      exact Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hr) hden.le)
    -- the test field `X z = ψ(‖π'(z - y)‖²) ι'ζ(π(z - y))`
    obtain ⟨X, hX⟩ : ∃ X : Pz → Pz, X = fun z => ψ (‖π' (z - y)‖ ^ 2) • ι' (ζ (π (z - y))) :=
      ⟨_, rfl⟩
    have hXsmooth : ContDiff ℝ 1 X := by
      have h1 : ContDiff ℝ 1 (fun z : Pz => π' (z - y)) :=
        π'.contDiff.comp (contDiff_id.sub contDiff_const)
      have h2 : ContDiff ℝ 1 (fun z : Pz => π (z - y)) :=
        π.contDiff.comp (contDiff_id.sub contDiff_const)
      rw [hX, hψ]
      exact (Real.smoothTransition.contDiff.comp
        ((contDiff_const.sub ((contDiff_norm_sq ℝ).comp h1)).div_const _)).smul
        (ι'.toContinuousLinearMap.contDiff.comp (hζ.comp h2))
    obtain ⟨SX, hSX⟩ : ∃ SX : Set Pz, SX = {z : Pz | π (z - y) ∈ tsupport ζ ∧ ‖π' (z - y)‖ ≤ t₁} :=
      ⟨_, rfl⟩
    have hSXclosed : IsClosed SX := by
      rw [hSX]
      exact ((isClosed_tsupport ζ).preimage (π.continuous.comp (continuous_id.sub continuous_const))).inter
        (isClosed_le (continuous_norm.comp (π'.continuous.comp (continuous_id.sub continuous_const)))
          continuous_const)
    have hsuppX : support X ⊆ SX := by
      intro z hz
      have hz' : ψ (‖π' (z - y)‖ ^ 2) • ι' (ζ (π (z - y))) ≠ 0 := by
        rw [mem_support, hX] at hz; exact hz
      have h1 : ψ (‖π' (z - y)‖ ^ 2) ≠ 0 := fun h => hz' (by rw [h, zero_smul])
      have h2 : ζ (π (z - y)) ≠ 0 := fun h => hz' (by rw [h, map_zero, smul_zero])
      rw [hSX]
      refine ⟨subset_tsupport _ h2, not_lt.mp fun hlt => h1 (hψ0 _ ?_)⟩
      exact pow_le_pow_left₀ ht₁0.le hlt.le 2
    have htsX : tsupport X ⊆ SX := closure_minimal hsuppX hSXclosed
    have hSXZ : SX ⊆ Z := by
      intro z hz
      rw [hSX] at hz
      exact (hZ' z).2 ⟨hζs hz.1, mem_ball_zero_iff.2 (hz.2.trans_lt ht₁t)⟩
    have hSXcpt : IsCompact SX := by
      refine isCompact_of_isClosed_isBounded hSXclosed ((Metric.isBounded_closedBall (x := y)
        (r := s + t₁)).subset fun z hz => ?_)
      rw [hSX] at hz
      rw [mem_closedBall, dist_eq_norm]
      have h1 : ‖π (z - y)‖ < s := by
        have := hζs hz.1
        rw [hB, mem_ball_zero_iff] at this
        exact this
      calc ‖z - y‖ = ‖ι (π (z - y)) + ι' (π' (z - y))‖ := by rw [← hdecomp]
        _ ≤ ‖ι (π (z - y))‖ + ‖ι' (π' (z - y))‖ := norm_add_le _ _
        _ = ‖π (z - y)‖ + ‖π' (z - y)‖ := by rw [LinearIsometry.norm_map, LinearIsometry.norm_map]
        _ ≤ s + t₁ := add_le_add h1.le hz.2
    have hXcs : HasCompactSupport X := hSXcpt.of_isClosed_subset (isClosed_tsupport X) htsX
    have hXF : ∀ a ∈ B, X (F a) = ι' (ζ a) := by
      intro a ha
      rw [hX]
      show ψ (‖π' (F a - y)‖ ^ 2) • ι' (ζ (π (F a - y))) = ι' (ζ a)
      rw [hπF, hπ'F]
      by_cases hat : a ∈ tsupport ζ
      · rw [hψ1 _ (pow_le_pow_left₀ (norm_nonneg _) (ht₀ a hat) 2), one_smul]
      · rw [image_eq_zero_of_notMem_tsupport hat, map_zero, smul_zero]
    -- the integrand `f = div_M X`
    obtain ⟨f, hf⟩ : ∃ f : Pz → ℝ, f = fun x => LinearMap.trace ℝ Pz
        ((Submodule.span ℝ (T x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) :=
      ⟨_, rfl⟩
    have hstat' : ∫ x in M, f x ∂μHE[Module.finrank ℝ E] = 0 := by
      rw [hf]; exact hstat X hXsmooth hXcs (htsX.trans (hSXZ.trans hZU))
    have hf0 : ∀ x ∉ Z, f x = 0 := by
      intro x hx
      have hD : fderiv ℝ X x = 0 := by
        by_contra h
        exact hx (hSXZ (htsX (support_fderiv_subset ℝ h)))
      rw [hf]
      simp only [hD, ContinuousLinearMap.toLinearMap_zero, LinearMap.comp_zero, map_zero]
    have hstep1 : ∫ x in M, f x ∂μHE[Module.finrank ℝ E] =
        ∫ x in F '' B, f x ∂μHE[Module.finrank ℝ E] := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hf0,
        Measure.restrict_restrict hZopen.measurableSet, inter_comm, hMZ]
    -- the two integrands
    obtain ⟨φ₁, hφ₁⟩ : ∃ φ₁ : E → ℝ,
        φ₁ = fun x => ∑ j, inner ℝ (fderiv ℝ u x (bE j)) (fderiv ℝ ζ x (bE j)) := ⟨_, rfl⟩
    obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : E → ℝ, φ₂ = fun x => ∑ j, inner ℝ ((fderiv ℝ u x).comp
        (1 - J (fderiv ℝ u x) • R (fderiv ℝ u x)) (bE j)) (fderiv ℝ ζ x (bE j)) := ⟨_, rfl⟩
    -- `J(Du) div_M X ∘ F = ⟨Du - G(Du), Dζ⟩` on the ball
    have hfF : ∀ a ∈ B, J (fderiv ℝ u a) * f (F a) = φ₁ a - φ₂ a := by
      intro a ha
      obtain ⟨p, hp⟩ : ∃ p, p = fderiv ℝ u a := ⟨_, rfl⟩
      obtain ⟨W, hW⟩ : ∃ W, W = fderiv ℝ ζ a := ⟨_, rfl⟩
      have hgR' : ∀ z, (1 + ContinuousLinearMap.adjoint p ∘L p) (R p z) = z := fun z =>
        congrArg (fun T' : E →L[ℝ] E => T' z) (hgR p)
      have hRsa : ∀ v w : E, inner ℝ (R p v) w = inner ℝ v (R p w) := fun v w => by
        rw [← ContinuousLinearMap.adjoint_inner_right, hRadj]
      have hAAR : ∀ w, ContinuousLinearMap.adjoint (L p) (L p (R p w)) = w := fun w => by
        have h := congrArg (fun T' : E →L[ℝ] E => T' (R p w)) (hgram p)
        exact h.trans (hgR' w)
      have hspan_eq : Submodule.span ℝ (T (F a)) =
          LinearMap.range ((L p : E →L[ℝ] Pz) : E →ₗ[ℝ] Pz) := by
        have hset : (LinearMap.range ((L p : E →L[ℝ] Pz) : E →ₗ[ℝ] Pz) : Set Pz) =
            Set.range (L p) := by
          rw [LinearMap.coe_range, ContinuousLinearMap.coe_coe]
        rw [htan' a ha, ← hp, ← hset, Submodule.span_eq]
      have hproj : ∀ z, (Submodule.span ℝ (T (F a))).starProjection z =
          L p (R p (ContinuousLinearMap.adjoint (L p) z)) := by
        intro z
        refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
        · rw [hspan_eq]; exact ⟨_, rfl⟩
        · rw [hspan_eq] at hw
          obtain ⟨x, rfl⟩ := hw
          rw [ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.adjoint_inner_left, map_sub, hAAR,
            sub_self, inner_zero_left]
      have hchain : ∀ x, fderiv ℝ X (F a) (L p x) = ι' (W x) := by
        have h1 : fderiv ℝ (X ∘ F) a = fderiv ℝ X (F a) ∘L fderiv ℝ F a :=
          fderiv_comp a (hXsmooth.differentiable one_ne_zero (F a)) (hFderiv a ha).differentiableAt
        have h2 : fderiv ℝ (X ∘ F) a = fderiv ℝ (fun b => ι'.toContinuousLinearMap (ζ b)) a := by
          apply Filter.EventuallyEq.fderiv_eq
          filter_upwards [hBopen.mem_nhds ha] with b hb
          exact hXF b hb
        have h3 : fderiv ℝ (fun b => ι'.toContinuousLinearMap (ζ b)) a =
            ι'.toContinuousLinearMap ∘L W := by
          rw [hW]
          exact (ι'.toContinuousLinearMap.hasFDerivAt.comp a
            (hζ.differentiable one_ne_zero a).hasFDerivAt).fderiv
        rw [hDF a ha, ← hp, h2, h3] at h1
        intro x
        exact (congrArg (fun T' : E →L[ℝ] Pz => T' x) h1).symm
      have hAι' : ∀ b, ContinuousLinearMap.adjoint (L p) (ι' b) = ContinuousLinearMap.adjoint p b := by
        intro b
        refine ext_inner_right ℝ fun v => ?_
        rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hL]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          LinearIsometry.coe_toContinuousLinearMap]
        rw [inner_add_right, real_inner_comm (ι v) (ι' b), hperp, zero_add,
          LinearIsometry.inner_map_map]
      have htr : f (F a) = ∑ j, inner ℝ (p (R p (bE j))) (W (bE j)) := by
        have e1 : (Submodule.span ℝ (T (F a))).starProjection.toLinearMap ∘ₗ
            (fderiv ℝ X (F a)).toLinearMap = (L p).toLinearMap ∘ₗ
            ((R p).toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (L p)).toLinearMap ∘ₗ
              (fderiv ℝ X (F a)).toLinearMap) := LinearMap.ext fun z => hproj _
        have e2 : ((R p).toLinearMap ∘ₗ (ContinuousLinearMap.adjoint (L p)).toLinearMap ∘ₗ
              (fderiv ℝ X (F a)).toLinearMap) ∘ₗ (L p).toLinearMap =
            (R p).toLinearMap ∘ₗ (ContinuousLinearMap.adjoint p).toLinearMap ∘ₗ W.toLinearMap :=
          LinearMap.ext fun x => by
            show R p (ContinuousLinearMap.adjoint (L p) (fderiv ℝ X (F a) (L p x))) = _
            rw [hchain, hAι']; rfl
        rw [hf]
        show LinearMap.trace ℝ Pz ((Submodule.span ℝ (T (F a))).starProjection.toLinearMap ∘ₗ
          (fderiv ℝ X (F a)).toLinearMap) = _
        rw [e1, LinearMap.trace_comp_comm', e2, LinearMap.trace_eq_sum_inner _ bE]
        refine Finset.sum_congr rfl fun j _ => ?_
        show inner ℝ (bE j) (R p (ContinuousLinearMap.adjoint p (W (bE j)))) = _
        rw [← hRsa, ContinuousLinearMap.adjoint_inner_right]
      have hφ₁a : φ₁ a = ∑ j, inner ℝ (p (bE j)) (W (bE j)) := by rw [hφ₁, hp, hW]
      have hφ₂a : φ₂ a = ∑ j, inner ℝ ((p.comp (1 - J p • R p)) (bE j)) (W (bE j)) := by
        rw [hφ₂, hp, hW]
      rw [htr, hφ₁a, hφ₂a, ← hp, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← inner_sub_left, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply, map_sub, sub_sub_cancel,
        map_smul, real_inner_smul_left]
    -- pull the integral back to the ball with the area formula
    have hDucont : ContinuousOn (fderiv ℝ u) B := hu.continuousOn_fderiv_of_isOpen hBopen le_rfl
    have hDumeas : Measurable (fderiv ℝ u) := measurable_fderiv ℝ u
    have hDζc : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
    have hGc : Continuous (fun q : E →L[ℝ] K => q.comp (1 - J q • R q)) :=
      continuous_id.clm_comp (continuous_const.sub (hJc.smul hRc))
    have hφ₁meas : Measurable φ₁ := by
      rw [hφ₁]
      exact Finset.measurable_sum _ fun j _ => continuous_inner.measurable.comp
        (((ContinuousLinearMap.apply ℝ K (bE j)).continuous.measurable.comp hDumeas).prodMk
          ((ContinuousLinearMap.apply ℝ K (bE j)).continuous.measurable.comp hDζc.measurable))
    have hφ₂meas : Measurable φ₂ := by
      rw [hφ₂]
      exact Finset.measurable_sum _ fun j _ => continuous_inner.measurable.comp
        (((ContinuousLinearMap.apply ℝ K (bE j)).continuous.measurable.comp
          (hGc.measurable.comp hDumeas)).prodMk
          ((ContinuousLinearMap.apply ℝ K (bE j)).continuous.measurable.comp hDζc.measurable))
    obtain ⟨g', hg'⟩ : ∃ g' : Pz → ℝ, g' = fun x =>
        (φ₁ (π (x - y)) - φ₂ (π (x - y))) / J (fderiv ℝ u (π (x - y))) := ⟨_, rfl⟩
    have hπy : Measurable (fun x : Pz => π (x - y)) :=
      π.continuous.measurable.comp (measurable_id.sub_const y)
    have hg'meas : Measurable g' := by
      rw [hg']
      exact ((hφ₁meas.comp hπy).sub (hφ₂meas.comp hπy)).div
        (hJc.measurable.comp (hDumeas.comp hπy))
    have hfg' : EqOn f g' (F '' B) := by
      rintro _ ⟨a, ha, rfl⟩
      rw [hg']
      show f (F a) = (φ₁ (π (F a - y)) - φ₂ (π (F a - y))) / J (fderiv ℝ u (π (F a - y)))
      rw [hπF, ← hfF a ha, mul_div_cancel_left₀ _ (hJpos _).ne']
    have hstep2 : ∫ x in F '' B, f x ∂μHE[Module.finrank ℝ E] =
        ∫ a in B, (φ₁ a - φ₂ a) ∂μHE[Module.finrank ℝ E] := by
      rw [setIntegral_congr_fun hFBmeas hfg', AF2, integral_map hFae hg'meas.aestronglyMeasurable,
        integral_withDensity_eq_integral_toReal_smul hρmeas
          (Eventually.of_forall fun a => by rw [hρ]; exact ENNReal.ofReal_lt_top)]
      refine setIntegral_congr_fun hBmeas fun a ha => ?_
      rw [hρ, hg']
      show (ENNReal.ofReal (J (fderiv ℝ u a))).toReal • ((φ₁ (π (F a - y)) - φ₂ (π (F a - y))) /
        J (fderiv ℝ u (π (F a - y)))) = φ₁ a - φ₂ a
      rw [hπF, ENNReal.toReal_ofReal (hJpos _).le, smul_eq_mul, mul_div_assoc',
        mul_div_cancel_left₀ _ (hJpos _).ne']
    -- both integrands are integrable on the ball: continuous, supported in `spt ζ ⊆ B`
    have hDζ0 : ∀ x ∉ tsupport ζ, fderiv ℝ ζ x = 0 := fun x hx => by
      by_contra h; exact hx (support_fderiv_subset ℝ h)
    have hint : ∀ φ : E → ℝ, ContinuousOn φ B → (∀ x ∉ tsupport ζ, φ x = 0) →
        IntegrableOn φ B μHE[Module.finrank ℝ E] := fun φ hφ h0 =>
      ((hφ.mono hζs).integrableOn_compact hζc.isCompact).of_forall_sdiff_eq_zero hBmeas
        (fun x hx => h0 x hx.2)
    have hφ₁int : IntegrableOn φ₁ B μHE[Module.finrank ℝ E] := by
      refine hint φ₁ ?_ fun x hx => ?_
      · rw [hφ₁]
        exact continuousOn_finset_sum _ fun j _ => (hDucont.clm_apply continuousOn_const).inner
          (hDζc.continuousOn.clm_apply continuousOn_const)
      · rw [hφ₁]
        exact Finset.sum_eq_zero fun j _ => by
          rw [hDζ0 x hx, ContinuousLinearMap.zero_apply, inner_zero_right]
    have hφ₂int : IntegrableOn φ₂ B μHE[Module.finrank ℝ E] := by
      refine hint φ₂ ?_ fun x hx => ?_
      · rw [hφ₂]
        exact continuousOn_finset_sum _ fun j _ =>
          ((hGc.comp_continuousOn hDucont).clm_apply continuousOn_const).inner
          (hDζc.continuousOn.clm_apply continuousOn_const)
      · rw [hφ₂]
        exact Finset.sum_eq_zero fun j _ => by
          rw [hDζ0 x hx, ContinuousLinearMap.zero_apply, inner_zero_right]
    have key : ∫ x in B, φ₁ x ∂μHE[Module.finrank ℝ E] -
        ∫ x in B, φ₂ x ∂μHE[Module.finrank ℝ E] = 0 := by
      rw [← integral_sub hφ₁int hφ₂int, ← hstep2, ← hstep1, hstat']
    rw [hφ₁, hφ₂] at key
    simp only [← he, hGeq]
    exact sub_eq_zero.mp key
  intro m k _
  obtain ⟨G, hG1, hG2, hG3, hG4⟩ := hAll (E := Euclid m) (K := Euclid k)
  exact ⟨G, hG1, hG2, hG3, fun P U M y ι ι' s t u hperp hspan hs ht _ hZU hu hut hMZ htan _ hstat ζ hζ
    hζc hζs => hG4 (EuclideanSpace.basisFun (Fin m) ℝ) (fun j => EuclideanSpace.single j 1)
      (EuclideanSpace.basisFun_apply (Fin m) ℝ) m finrank_euclideanSpace_fin volume
      (EuclideanSpace.euclideanHausdorffMeasure_eq_volume m).symm U M (tangentSpace M) y ι ι' s t u
      hperp hspan hs ht hZU hu hut hMZ htan hstat ζ hζ hζc hζs⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
