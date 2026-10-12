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

/-- **Graph push-forward bound** (the inequality half of the area formula used in the graph-`C¹`
argument).  Let `Φ(v) = z + ι v + ι'(f v)` with `ι`, `ι'` isometric embeddings with orthogonal
ranges and `f` continuous, and suppose `Φ(A) ⊆ spt μ ∩ W`, where `Hⁿ((spt μ ∩ W) ∖ M) = 0` and
`μ = θ Hⁿ⌞M`.  Then `Φ_#(Lⁿ⌞A) ≤ μ⌞Φ(A)`: `π(x) = ι*(x − z)` is a `1`-Lipschitz left inverse of
`Φ`, so `Lⁿ(Z) = Hⁿ(π(Φ(Z))) ≤ Hⁿ(Φ(Z))`, and `Hⁿ ≤ μ` on subsets of `spt μ ∩ W` because
`(spt μ ∩ W) ∖ M` is `Hⁿ`-null and `θ ≥ 1` on `M`. -/
theorem Submission.dorag_gc_graph_map_volume_le_measure : ∀ (n k P : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (ι : Euclid n →ₗᵢ[ℝ] Euclid P) (ι' : Euclid k →ₗᵢ[ℝ] Euclid P) (f : Euclid n → Euclid k) (z : Euclid P) (A : Set (Euclid n)), (∀ v w, inner ℝ (ι v) (ι' w) = 0) → Continuous f → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ v ∈ A, z + ι v + ι' (f v) ∈ R.measure.support ∩ W) → Measure.map (fun v => z + ι v + ι' (f v)) (volume.restrict A) ≤ R.measure.restrict ((fun v => z + ι v + ι' (f v)) '' A) := by
  intro n k P U W R ι ι' f z A horth hf hnull hA
  set Φ : Euclid n → Euclid P := fun v => z + ι v + ι' (f v) with hΦ
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    exact (continuous_const.add ι.continuous).add (ι'.continuous.comp hf)
  -- 1. a 1-Lipschitz left inverse `π(x) = ι*(x − z)` of `Φ`
  set π : Euclid P → Euclid n := fun x => (ι.toContinuousLinearMap.adjoint) (x - z) with hπ
  have hπΦ : ∀ v, π (Φ v) = v := by
    intro v
    apply ext_inner_left ℝ
    intro u
    have hsub : z + ι v + ι' (f v) - z = ι v + ι' (f v) := by abel
    simp only [hπ, hΦ, ContinuousLinearMap.adjoint_inner_right,
      LinearIsometry.coe_toContinuousLinearMap, hsub, inner_add_right, LinearIsometry.inner_map_map]
    rw [horth u (f v), add_zero]
  have hπlip : LipschitzWith 1 π := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [hπ, dist_eq_norm, NNReal.coe_one, one_mul]
    rw [← map_sub, sub_sub_sub_cancel_right]
    calc ‖(ι.toContinuousLinearMap.adjoint) (x - y)‖
        ≤ ‖ι.toContinuousLinearMap.adjoint‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x - y‖ := by
          gcongr
          rw [LinearIsometryEquiv.norm_map]
          exact ι.norm_toContinuousLinearMap_le
      _ = ‖x - y‖ := one_mul _
  -- 2. `Lⁿ(Z) ≤ Hⁿ(Φ(Z))`, since `π(Φ(Z)) = Z` and `Hⁿ = Lⁿ` on `ℝⁿ`
  have hvol : ∀ Z : Set (Euclid n), volume Z ≤ μHE[n] (Φ '' Z) := by
    intro Z
    have h1 : π '' (Φ '' Z) = Z := by
      rw [image_image]; simp [hπΦ]
    have h2 := Poincare.SimonGMT.Chapter02.euclideanHausdorffMeasure_image_le_of_lipschitzOn n
      (hπlip.lipschitzOnWith (s := Φ '' Z))
    rw [h1] at h2
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume n]
    simpa using h2
  -- 3. `Hⁿ(T) ≤ μ(T)` for `T ⊆ spt μ ∩ W`, through a measurable hull of `T`
  have hHle : ∀ T ⊆ R.measure.support ∩ W, μHE[n] T ≤ R.measure T := by
    intro T hT
    set T' := toMeasurable R.measure T with hT'
    have hT'm : MeasurableSet T' := measurableSet_toMeasurable _ _
    calc μHE[n] T ≤ μHE[n] ((T' ∩ R.carrier) ∪ ((R.measure.support ∩ W) \ R.carrier)) := by
          apply measure_mono
          intro x hx
          by_cases hxM : x ∈ R.carrier
          · exact Or.inl ⟨subset_toMeasurable _ _ hx, hxM⟩
          · exact Or.inr ⟨hT hx, hxM⟩
      _ ≤ μHE[n] (T' ∩ R.carrier) + μHE[n] ((R.measure.support ∩ W) \ R.carrier) :=
          measure_union_le _ _
      _ = μHE[n] (T' ∩ R.carrier) := by rw [hnull, add_zero]
      _ ≤ R.measure T' := by
          unfold IMRep.measure
          rw [withDensity_apply _ hT'm, Measure.restrict_restrict hT'm]
          calc μHE[n] (T' ∩ R.carrier) = ∫⁻ _ in T' ∩ R.carrier, (1 : ℝ≥0∞) ∂μHE[n] := by
                simp
            _ ≤ ∫⁻ x in T' ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
                apply setLIntegral_mono' (hT'm.inter R.measurableSet_carrier)
                intro x hx
                exact_mod_cast R.mult_pos x hx.2
      _ = R.measure T := measure_toMeasurable _
  -- 4. test on measurable `Y`: `Lⁿ(Φ⁻¹(Y) ∩ A) ≤ μ(Φ(Φ⁻¹(Y) ∩ A)) ≤ μ(Y ∩ Φ(A))`
  rw [Measure.le_iff]
  intro Y hY
  rw [Measure.map_apply hΦc.measurable hY, Measure.restrict_apply (hΦc.measurable hY),
    Measure.restrict_apply hY]
  calc volume (Φ ⁻¹' Y ∩ A) ≤ μHE[n] (Φ '' (Φ ⁻¹' Y ∩ A)) := hvol _
    _ ≤ R.measure (Φ '' (Φ ⁻¹' Y ∩ A)) := hHle _ (by
        rintro _ ⟨v, hv, rfl⟩; exact hA v hv.2)
    _ ≤ R.measure (Y ∩ Φ '' A) := measure_mono (by
        rintro _ ⟨v, hv, rfl⟩; exact ⟨hv.1, v, hv.2, rfl⟩)
theorem Submission.dorag_gc_decay_plane_eq_approxTangent : ∀ (P n : ℕ) (U W : Set (Euclid P)) (R : IMRep U n) (κ : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → ∀ᵐ x ∂R.measure, x ∈ W → ∀ (S : Submodule ℝ (Euclid P)) (s₀ K : ℝ), 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ y in closedBall x s, ENNReal.ofReal (∑ i : Fin P, ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → S = approxTangentPlane n R.carrier x := by
  -- generic facts, proved in a small context
  have aux_vec : ∀ (m : ℕ) (a b c : Euclid m), ‖a - b‖ ^ 2 ≤ 2 * ‖c - a‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
    intro m a b c
    have htri : ‖a - b‖ ≤ ‖c - a‖ + ‖c - b‖ := by
      calc ‖a - b‖ = ‖(c - b) - (c - a)‖ := by congr 1; abel
        _ ≤ ‖c - b‖ + ‖c - a‖ := norm_sub_le _ _
        _ = ‖c - a‖ + ‖c - b‖ := add_comm _ _
    nlinarith [norm_nonneg (a - b), norm_nonneg (c - a), norm_nonneg (c - b),
      sq_nonneg (‖c - a‖ - ‖c - b‖)]
  have aux_expand : ∀ (m : ℕ) (x : Euclid m), x = ∑ i : Fin m, x i • EuclideanSpace.single i (1 : ℝ) := by
    intro m x
    ext j; simp [Pi.single_apply]
  have aux_HS : ∀ (m : ℕ) (A : Euclid m →L[ℝ] Euclid m), ‖A‖ ≤ 2 →
      ∑ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * m * ‖A‖ := by
    intro m A hA
    have h1 : ∀ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ 2 * ‖A‖ := by
      intro i
      have hle : ‖A (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖A‖ := by
        simpa using A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
      have h0 := norm_nonneg (A (EuclideanSpace.single i (1 : ℝ)))
      nlinarith [norm_nonneg A]
    calc ∑ i : Fin m, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 ≤ ∑ _i : Fin m, 2 * ‖A‖ :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * m * ‖A‖ := by simp; ring
  intro P n U W R κ hW hWU hP hdens
  -- notation for the tangent projection field
  obtain ⟨p, hpdef⟩ : ∃ p : Euclid P → (Euclid P →L[ℝ] Euclid P),
      p = fun x => (approxTangentPlane n R.carrier x).starProjection := ⟨_, rfl⟩
  have hpx : ∀ x, p x = (approxTangentPlane n R.carrier x).starProjection := fun x => by rw [hpdef]
  have hpP : AEStronglyMeasurable p R.measure := by rw [hpdef]; exact hP
  have hpn : ∀ x, ‖p x‖ ≤ 1 := fun x => by rw [hpx]; exact Submodule.starProjection_norm_le _
  -- finiteness of μ on compact subsets of U
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    unfold IMRep.measure
    rw [withDensity_apply _ hK.measurableSet, Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  -- Step 1: Lebesgue points of p at μ-a.e. point of W
  have hleb : ∀ᵐ x ∂R.measure, x ∈ W → Tendsto (fun r => (∫⁻ y in closedBall x r, ‖p y - p x‖ₑ ∂R.measure) /
      R.measure (closedBall x r)) (𝓝[>] 0) (𝓝 0) := by
    have hr : ∀ x : W, ∃ r : ℝ, 0 < r ∧ closedBall (x : Euclid P) r ⊆ W := by
      intro x
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x x.2
      exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
    choose r hr0 hrW using hr
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : W => ball (x : Euclid P) (r x / 2)) (fun _ => isOpen_ball)
    have hloc : ∀ i : W, ∀ᵐ x ∂R.measure, x ∈ ball (i : Euclid P) (r i / 2) →
        Tendsto (fun ρ => (∫⁻ y in closedBall x ρ, ‖p y - p x‖ₑ ∂R.measure) /
          R.measure (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) := by
      intro i
      have hBfin : R.measure (ball (i : Euclid P) (r i / 2)) ≠ ∞ :=
        (lt_of_le_of_lt (measure_mono (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith [hr0 i]))))
          (hfin _ (isCompact_closedBall _ _) ((hrW i).trans hWU))).ne
      have : IsFiniteMeasure (R.measure.restrict (ball (i : Euclid P) (r i / 2))) :=
        isFiniteMeasure_restrict.2 hBfin
      have hint : LocallyIntegrable p (R.measure.restrict (ball (i : Euclid P) (r i / 2))) :=
        (Integrable.of_bound hpP.restrict 1 (Eventually.of_forall hpn)).locallyIntegrable
      have h1 := (Besicovitch.vitaliFamily
        (R.measure.restrict (ball (i : Euclid P) (r i / 2)))).ae_tendsto_lintegral_enorm_sub_div hint
      rw [ae_restrict_iff' measurableSet_ball] at h1
      filter_upwards [h1] with x hx hxB
      have h2 := (hx hxB).comp (Besicovitch.tendsto_filterAt _ x)
      refine h2.congr' ?_
      have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), closedBall x ρ ⊆ ball (i : Euclid P) (r i / 2) := by
        have hd : 0 < r i / 2 - dist x i := by
          rw [mem_ball] at hxB; linarith
        filter_upwards [Ioo_mem_nhdsGT hd] with ρ hρ
        exact closedBall_subset_ball' (by linarith [hρ.2])
      filter_upwards [hev] with ρ hρ
      simp only [Function.comp]
      rw [Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.2 hρ,
        Measure.restrict_apply measurableSet_closedBall, inter_eq_left.2 hρ]
    have hall : ∀ᵐ x ∂R.measure, ∀ i ∈ T, x ∈ ball (i : Euclid P) (r i / 2) →
        Tendsto (fun ρ => (∫⁻ y in closedBall x ρ, ‖p y - p x‖ₑ ∂R.measure) /
          R.measure (closedBall x ρ)) (𝓝[>] 0) (𝓝 0) :=
      (ae_ball_iff hTc).2 fun i _ => hloc i
    filter_upwards [hall] with x hx hxW
    have hxU : x ∈ ⋃ i ∈ T, ball (i : Euclid P) (r i / 2) := by
      rw [hTU]; exact mem_iUnion.2 ⟨⟨x, hxW⟩, mem_ball_self (half_pos (hr0 _))⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 hxU
    exact hx i hi hxi
  -- Step 2: the pointwise argument at good points
  have hsupp : ∀ᵐ x ∂R.measure, x ∈ R.measure.support :=
    measure_eq_zero_iff_ae_notMem.1 Measure.measure_compl_support |>.mono fun x hx => by
      simpa using hx
  have hωpos : (0 : ℝ≥0∞) < unitBallVolume n := measure_ball_pos _ _ one_pos
  have hωfin : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  filter_upwards [hleb, hsupp] with x hxleb hxs hxW S s₀ K hs₀ hdec
  obtain ⟨t₀, ht₀, hball₀⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ closedBall x t₀ ⊆ W := by
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW x hxW
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  set Δ : ℝ := ∑ i : Fin P, ‖p x (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
    with hΔ
  have hΔ0 : 0 ≤ Δ := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmeasI : AEMeasurable (fun y => ‖p y - p x‖ₑ) R.measure :=
    (hpP.sub aestronglyMeasurable_const).enorm
  -- the key inequality for small s
  have hkey : ∀ s : ℝ, 0 < s → s ≤ min s₀ t₀ →
      ENNReal.ofReal Δ ≤ (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s)) + 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n) := by
    intro s hs hsle
    have hss₀ : s ≤ s₀ := hsle.trans (min_le_left _ _)
    have hst₀ : s ≤ t₀ := hsle.trans (min_le_right _ _)
    have hsubW : closedBall x s ⊆ W := (closedBall_subset_closedBall hst₀).trans hball₀
    have hμpos : 0 < R.measure (closedBall x s) :=
      (Measure.mem_support_iff_forall x).1 hxs _ (closedBall_mem_nhds x hs)
    have hμfin : R.measure (closedBall x s) ≠ ∞ :=
      (hfin _ (isCompact_closedBall _ _) (hsubW.trans hWU)).ne
    -- pointwise bound
    have hpt : ∀ y, ENNReal.ofReal Δ ≤ (4 * P) * ‖p y - p x‖ₑ + 2 * ENNReal.ofReal (∑ i : Fin P,
        ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
          S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
      intro y
      have hA : ‖p y - p x‖ ≤ 2 := by
        calc ‖p y - p x‖ ≤ ‖p y‖ + ‖p x‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := add_le_add (hpn y) (hpn x)
          _ = 2 := by norm_num
      have hHS := aux_HS P (p y - p x) hA
      have hreal : Δ ≤ 2 * (∑ i : Fin P, ‖(p y - p x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) +
          2 * (∑ i : Fin P, ‖p y (EuclideanSpace.single i (1 : ℝ)) -
            S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
        rw [hΔ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by
          simpa only [sub_apply] using aux_vec P (p x (EuclideanSpace.single i 1))
            (S.starProjection (EuclideanSpace.single i 1)) (p y (EuclideanSpace.single i 1))
      have hreal2 : Δ ≤ 4 * P * ‖p y - p x‖ + 2 * (∑ i : Fin P, ‖p y (EuclideanSpace.single i (1 : ℝ)) -
            S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) := by
        nlinarith [hreal, hHS]
      calc ENNReal.ofReal Δ ≤ ENNReal.ofReal (4 * P * ‖p y - p x‖ + 2 * (∑ i : Fin P,
            ‖p y (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal hreal2
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by norm_num), ofReal_norm, hpx y]
            simp
    have hint : R.measure (closedBall x s) * ENNReal.ofReal Δ ≤
        (4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ENNReal.ofReal (K * s ^ (n + 1)) := by
      rw [mul_comm, ← setLIntegral_const]
      calc _ ≤ ∫⁻ y in closedBall x s, ((4 * P) * ‖p y - p x‖ₑ + 2 * ENNReal.ofReal (∑ i : Fin P,
            ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)) ∂R.measure := lintegral_mono hpt
        _ = (4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ∫⁻ y in closedBall x s,
            ENNReal.ofReal (∑ i : Fin P,
            ‖(approxTangentPlane n R.carrier y).starProjection (EuclideanSpace.single i (1 : ℝ)) -
              S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure := by
            rw [lintegral_add_left' ((hmeasI.restrict).const_mul _),
              lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top P)),
              lintegral_const_mul' _ _ (by simp)]
        _ ≤ _ := by gcongr; exact hdec s hs hss₀
    -- lower density
    have hlow := hdens x hxs s hs hsubW
    have hdiv : ENNReal.ofReal (K * s ^ (n + 1)) / R.measure (closedBall x s) ≤
        ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n := by
      rw [ENNReal.div_le_iff hμpos.ne' hμfin]
      calc ENNReal.ofReal (K * s ^ (n + 1)) ≤ ENNReal.ofReal (max K 0 * s ^ (n + 1)) :=
            ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _)
        _ = ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n * unitBallVolume n /
              ENNReal.ofReal (Real.exp (κ * s) / s ^ n) := by
            rw [ENNReal.div_mul_cancel hωpos.ne' hωfin, ← ENNReal.ofReal_div_of_pos (by positivity)]
            congr 1
            field_simp
            ring
        _ ≤ ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n * R.measure (closedBall x s) := by
            rw [mul_div_assoc]
            gcongr
            rw [ENNReal.div_le_iff (by positivity) ENNReal.ofReal_ne_top, mul_comm]
            exact hlow
    calc ENNReal.ofReal Δ = R.measure (closedBall x s) * ENNReal.ofReal Δ / R.measure (closedBall x s) := by
          rw [mul_comm, ENNReal.mul_div_cancel_right hμpos.ne' hμfin]
      _ ≤ ((4 * P) * (∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) + 2 * ENNReal.ofReal (K * s ^ (n + 1))) /
            R.measure (closedBall x s) := by gcongr
      _ = (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) / R.measure (closedBall x s)) +
            2 * (ENNReal.ofReal (K * s ^ (n + 1)) / R.measure (closedBall x s)) := by
          rw [ENNReal.add_div, mul_div_assoc, mul_div_assoc]
      _ ≤ _ := by gcongr
  -- passing to the limit
  have hlim : Tendsto (fun s => (4 * P) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s)) + 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s => (4 * (P : ℝ≥0∞)) * ((∫⁻ y in closedBall x s, ‖p y - p x‖ₑ ∂R.measure) /
        R.measure (closedBall x s))) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (hxleb hxW)
        (Or.inr (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top P)))
    have h2 : Tendsto (fun s : ℝ => 2 * (ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s))) / unitBallVolume n))
        (𝓝[>] 0) (𝓝 0) := by
      have h3 : Tendsto (fun s : ℝ => ENNReal.ofReal (max K 0 * (s * Real.exp (κ * s)))) (𝓝[>] 0) (𝓝 0) := by
        have : Tendsto (fun s : ℝ => max K 0 * (s * Real.exp (κ * s))) (𝓝 0) (𝓝 0) := by
          have hc : Continuous (fun s : ℝ => max K 0 * (s * Real.exp (κ * s))) := by fun_prop
          simpa using hc.tendsto 0
        simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
      simpa using ENNReal.Tendsto.const_mul (ENNReal.Tendsto.div_const h3 (Or.inr hωpos.ne')) (Or.inr (by simp))
    simpa using h1.add h2
  have hΔle : ENNReal.ofReal Δ ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hs₀ ht₀)] with s hs
    exact hkey s hs.1 hs.2.le
  have hΔz : Δ = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 (le_antisymm hΔle bot_le)) hΔ0
  have hcomp : ∀ i : Fin P, p x (EuclideanSpace.single i (1 : ℝ)) = S.starProjection (EuclideanSpace.single i (1 : ℝ)) := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).1 hΔz i (Finset.mem_univ _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this))
  have hpeq : ∀ v, p x v = S.starProjection v := by
    intro v
    rw [aux_expand P v, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, hcomp i]
  ext v
  rw [← Submodule.starProjection_eq_self_iff (K := S), ← Submodule.starProjection_eq_self_iff
    (K := approxTangentPlane n R.carrier x), ← hpx x, hpeq v]

theorem Submission.dorag_gc_graph_tangent_ae : ∀ (n k : ℕ) (U W : Set (Euclid (n + k))) (R : IMRep U n) (κ : ℝ) (ι : Euclid n →ₗᵢ[ℝ] Euclid (n + k)) (ι' : Euclid k →ₗᵢ[ℝ] Euclid (n + k)) (f : Euclid n → Euclid k) (z : Euclid (n + k)) (a : ℝ), IsOpen W → W ⊆ U → AEStronglyMeasurable (fun x => (approxTangentPlane n R.carrier x).starProjection) R.measure → (∀ y ∈ R.measure.support, ∀ t : ℝ, 0 < t → closedBall y t ⊆ W → unitBallVolume n ≤ ENNReal.ofReal (Real.exp (κ * t) / t ^ n) * R.measure (closedBall y t)) → μHE[n] ((R.measure.support ∩ W) \ R.carrier) = 0 → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ W)), ∀ v : Euclid n, x = z + ι v + ι' (f v) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap)) → (∀ v w, inner ℝ (ι v) (ι' w) = 0) → (∀ v w, ‖f v - f w‖ ≤ 1 / 4 * ‖v - w‖) → f 0 = 0 → 0 < a → closedBall z a ⊆ W → R.measure.support ∩ closedBall z a = range (fun v => z + ι v + ι' (f v)) ∩ closedBall z a → ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (4 * a / 5) → DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier (z + ι v + ι' (f v)) = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) ∧ ∀ (S : Submodule ℝ (Euclid (n + k))) (s₀ K : ℝ), 0 < s₀ → (∀ s : ℝ, 0 < s → s ≤ s₀ → ∫⁻ x in closedBall (z + ι v + ι' (f v)) s, ENNReal.ofReal (∑ i : Fin (n + k), ‖(approxTangentPlane n R.carrier x).starProjection (EuclideanSpace.single i (1 : ℝ)) - S.starProjection (EuclideanSpace.single i (1 : ℝ))‖ ^ 2) ∂R.measure ≤ ENNReal.ofReal (K * s ^ (n + 1))) → S = LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
  intro n k U W R κ ι ι' f z a hW hWU hP hdens hnull htan horth hfL hf0 ha hball hspt
  set Φ : Euclid n → Euclid (n + k) := fun v => z + ι v + ι' (f v) with hΦ
  -- Step 1 (geometry): `f` is `¼`-Lipschitz, so `f` and `Φ` are continuous, and for `|v| < 4a/5`,
  -- `|Φ(v) − z|² = |v|² + |f(v)|² ≤ (17/16)|v|² < a²`, so `Φ(v) ∈ spt μ ∩ B_a(z) ⊆ spt μ ∩ W`.
  have hLip : LipschitzWith (1 / 4 : NNReal) f :=
    LipschitzWith.of_dist_le_mul fun v w => by simpa [dist_eq_norm] using hfL v w
  have hfc : Continuous f := hLip.continuous
  have hΦc : Continuous Φ := by
    simp only [hΦ]
    fun_prop
  have hgeo : ∀ v ∈ ball (0 : Euclid n) (4 * a / 5), Φ v ∈ R.measure.support ∩ W := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    have hfv : ‖f v‖ ≤ 1 / 4 * ‖v‖ := by simpa [hf0] using hfL v 0
    have hsq : ‖Φ v - z‖ ^ 2 = ‖v‖ ^ 2 + ‖f v‖ ^ 2 := by
      have hΦz : Φ v - z = ι v + ι' (f v) := by
        simp only [hΦ]
        abel
      rw [hΦz, norm_add_sq_real, horth, LinearIsometry.norm_map, LinearIsometry.norm_map]
      ring
    have h1 : ‖f v‖ ^ 2 ≤ (1 / 4 * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hfv 2
    have h2 : ‖v‖ ^ 2 ≤ (4 * a / 5) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv.le 2
    have hle : ‖Φ v - z‖ ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    have hmem : Φ v ∈ range Φ ∩ closedBall z a :=
      ⟨mem_range_self v, mem_closedBall_iff_norm.2 (abs_le_of_sq_le_sq' hle ha.le).2⟩
    rw [← hspt] at hmem
    exact ⟨hmem.1, hball hmem.2⟩
  -- Step 2 (transfer): graph_pushforward gives `Φ_#(Lⁿ⌞B̆_{4a/5}(0)) ≤ μ⌞Φ(B̆_{4a/5}(0)) ≤ μ`, so a
  -- property of `μ`-a.e. `x` holds at `Φ(v)` for `Lⁿ`-a.e. `v ∈ B̆_{4a/5}(0)`.
  have hmap := Submission.dorag_gc_graph_map_volume_le_measure n k (n + k) U W R ι ι' f z
    (ball (0 : Euclid n) (4 * a / 5)) horth hfc hnull hgeo
  have htransfer : ∀ Q : Euclid (n + k) → Prop, (∀ᵐ x ∂R.measure, Q x) →
      ∀ᵐ v ∂volume, v ∈ ball (0 : Euclid n) (4 * a / 5) → Q (Φ v) := by
    intro Q hQ
    have hQ' : ∀ᵐ x ∂(Measure.map Φ (volume.restrict (ball (0 : Euclid n) (4 * a / 5)))), Q x :=
      ae_mono (hmap.trans Measure.restrict_le_self) hQ
    exact (ae_restrict_iff' measurableSet_ball).1 (ae_of_ae_map hΦc.measurable.aemeasurable hQ')
  -- Step 3 (`htan` for `μ`): `μ⌞W = (Hⁿ⌞(M ∩ W)).withDensity θ ≪ Hⁿ⌞(M ∩ W)`.
  have htanμ : ∀ᵐ x ∂R.measure, x ∈ W → ∀ v : Euclid n, x = z + ι v + ι' (f v) →
      DifferentiableAt ℝ f v ∧ approxTangentPlane n R.carrier x =
        LinearMap.range (ι.toLinearMap + ι'.toLinearMap ∘ₗ (fderiv ℝ f v).toLinearMap) := by
    have hac : R.measure.restrict W ≪ μHE[n].restrict (R.carrier ∩ W) := by
      unfold IMRep.measure
      rw [restrict_withDensity hW.measurableSet, Measure.restrict_restrict hW.measurableSet,
        inter_comm]
      exact withDensity_absolutelyContinuous _ _
    exact (ae_restrict_iff' hW.measurableSet).1 (hac.ae_le htan)
  -- Step 4 (decay planes): by decay_plane, at `μ`-a.e. `x ∈ W` every plane `S` with a tilt-excess
  -- decay bound at `x` is `TₓM`.
  have hdecay := Submission.dorag_gc_decay_plane_eq_approxTangent (n + k) n U W R κ hW hWU hP
    hdens
  -- Step 5: combine Steps 3 and 4 at `x = Φ(v) ∈ W`, with the witness `v`.
  filter_upwards [htransfer _ (htanμ.and hdecay)] with v hv hvB
  obtain ⟨htv, hdv⟩ := hv hvB
  have hΦW : Φ v ∈ W := (hgeo v hvB).2
  obtain ⟨hdiff, hT⟩ := htv hΦW v rfl
  exact ⟨hdiff, hT, fun S s₀ K hs₀ hS => (hdv hΦW S s₀ K hs₀ hS).trans hT⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
