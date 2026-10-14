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

/-- The zero current `0 ∈ 𝒟ₙ(U)` is integer multiplicity (Simon 6.3.1): the triple with empty
carrier, multiplicity `0` and orientation `0` represents it, since `Hⁿ⌞∅ = 0`. -/
theorem Submission.cmcsd_zero_isIntegerMultiplicity : ∀ (P n : ℕ) (U : Set (Euclid P)), IsIntegerMultiplicity (0 : GeometricCurrentOn U n) := by
  intro P n U
  refine ⟨{ carrier := ∅
            mult := fun _ => 0
            orient := fun _ => 0
            measurableSet_carrier := MeasurableSet.empty
            carrier_subset := empty_subset U
            rectifiable :=
              Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
            measurable_mult := measurable_const
            mult_pos := fun x hx => by simp at hx
            locallyIntegrable_mult := fun K _ _ => by simp
            aestronglyMeasurable_orient := aestronglyMeasurable_const
            orients := by simp }, ?_⟩
  intro ω
  simp [IMRep.action]
/-- **The mass measure is null off the support** (Simon 6.2.5, 6.2.11; step (1d) of the shell
decomposition in the proof of the deformation theorem, Simon Ch. 6, 5.1).  If currents vanish
on forms supported off their support and `μ(W) = M_W(X)` for every open `W`, then
`μ(ℝᴾ \ spt X) = 0`: the complement of `spt X` is the open zero region `Z` of `X`, and every
form admissible for `M_Z(X)` is supported off `spt X`, so `M_Z(X) = 0`. -/
theorem Submission.cmcsd_sh_measure_compl_support_eq_zero : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)), (∀ W : Set (Euclid P), IsOpen W → X.massOn W = μ W) → μ X.supportᶜ = 0 := by
  intro hVO P k X μ hμ
  -- (1) `(spt X)ᶜ = (ℝᴾ \ Z)ᶜ = Z`, the open zero region of `X`
  have hcompl : X.supportᶜ = X.zeroRegion := by
    rw [GeometricCurrentOn.support, ← compl_eq_univ_sdiff, compl_compl]
  -- (2) `μ((spt X)ᶜ) = μ(Z) = M_Z(X)`
  rw [hcompl, ← hμ _ X.isOpen_zeroRegion]
  -- (3)–(4) every form admissible for `M_Z(X)` is supported off `spt X`, so `X` kills it
  refine le_antisymm (sSup_le ?_) zero_le
  rintro r ⟨ω, hω, rfl⟩
  show ENNReal.ofReal (X ω) ≤ 0
  rw [hVO P k univ X ω (Disjoint.mono_left hω.1 Set.disjoint_sdiff_right), ENNReal.ofReal_zero]
/-- **Restriction of an integer multiplicity representation** (Simon Ch. 6, 3.1).  For
`R = (M, θ, ξ)` with weight `μ_R = θ Hⁿ⌞M`: (a) `μ_R ≪ Hⁿ⌞M`; (b) `ξ` is `μ_R`-a.e. strongly
measurable; (c) for Borel `E` and `R' = (M ∩ E, θ, ξ)`, `μ_{R'} = μ_R⌞E` and
`R'(ω) = ∫_E ⟨ω, ξ⟩ dμ_R` for every `n`-form `ω`. -/
theorem Submission.lcmp_imRep_measure_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), R.measure ≪ μHE[n].restrict R.carrier ∧ AEStronglyMeasurable R.orient R.measure ∧ ∀ (E : Set (Euclid P)) (R' : IMRep U n), MeasurableSet E → R'.carrier = R.carrier ∩ E → R'.mult = R.mult → R'.orient = R.orient → R'.measure = R.measure.restrict E ∧ ∀ ω : DifferentialForm (Euclid P) n, R'.action ω = ∫ x in E, R.orient x (ω x) ∂R.measure := by
  intro P n U R
  -- (a) a measure with a density is absolutely continuous; (b) so `ξ` is `μ_R`-measurable
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  refine ⟨hac, R.aestronglyMeasurable_orient.mono_ac hac, ?_⟩
  intro E R' hE hc hm ho
  -- (c), weights: `((Hⁿ⌞M).withDensity θ)⌞E = (Hⁿ⌞(E ∩ M)).withDensity θ = μ_{R'}`
  have hmeasEq : R'.measure = R.measure.restrict E := by
    unfold IMRep.measure
    rw [restrict_withDensity hE, Measure.restrict_restrict hE, hc, hm, inter_comm]
  refine ⟨hmeasEq, fun ω => ?_⟩
  -- (c), actions: `∫ h d(λ.withDensity θ) = ∫ θ h dλ` for the Borel density `θ : ℝᴾ → [0, ∞)`
  have hmult : (fun x => (R'.mult x : ℝ≥0∞)) = fun x => (((R'.mult x : NNReal)) : ℝ≥0∞) := by
    funext x
    simp
  have hmeas : Measurable fun x => ((R'.mult x : ℕ) : NNReal) :=
    (measurable_from_nat (f := fun k : ℕ => (k : NNReal))).comp R'.measurable_mult
  rw [← hmeasEq]
  unfold IMRep.action IMRep.measure
  rw [hmult, integral_withDensity_eq_integral_smul hmeas]
  congr 1
  funext x
  rw [ho, NNReal.smul_def, smul_eq_mul]
  norm_cast

/-- **Mass measure of an integer multiplicity current** (Simon Ch. 6, 3.1–3.2; proof of 6.5.1,
(8)–(10)).  If `T = τ(M, θ, ξ)` in `ℝᴾ` has `M(T) < ∞`, then `μ_T = θ Hⁿ⌞M` and `ξ` satisfy:
`μ_T` is finite (`μ_T(ℝᴾ) = M(T)`), `ξ` is `μ_T`-measurable with `|⟨α, ξ⟩| ≤ |α|` `μ_T`-a.e.,
`T(ω) = ∫ ⟨ω, ξ⟩ dμ_T`, `M_W(T) = μ_T(W)` for open `W`, `μ_T(ℝᴾ \ spt T) = 0`, and for Borel
`E` every `X = T⌞E` is integer multiplicity, being represented by `(M ∩ E, θ, ξ)`. -/
theorem Submission.cmcsd_sh_im_mass_measure : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → ∀ (P n : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) n), IsIntegerMultiplicity T → T.mass < ∞ → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), IsFiniteMeasure μ ∧ AEStronglyMeasurable ξ μ ∧ (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ μ T.supportᶜ = 0 ∧ (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), MeasurableSet E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → IsIntegerMultiplicity X) := by
  intro hVO hMR hIMC P n T hT hmass
  -- `T = τ(M, θ, ξ)`; take `μ = μ_T = θ Hⁿ⌞M` and the orientation `ξ`
  obtain ⟨R, hR⟩ := hT
  obtain ⟨hac, hξm, hrestr⟩ := Submission.lcmp_imRep_measure_restrict P n univ R
  -- `M_W(T) = μ_T(W)` for open `W`
  have hW : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W :=
    hMR P n univ T R isOpen_univ hR
  refine ⟨R.measure, R.orient, ⟨?_⟩, hξm, hac.ae_le (hIMC.2.2.2 P n univ R), fun ω => ?_, hW,
    Submission.cmcsd_sh_measure_compl_support_eq_zero hVO P n T R.measure hW,
    fun E X hE hX => ?_⟩
  · -- `μ_T(ℝᴾ) = M(T) < ∞`
    rw [← hW univ isOpen_univ]
    exact hmass
  · -- `T(ω) = τ(M, θ, ξ)(ω) = ∫_{ℝᴾ} ⟨ω, ξ⟩ dμ_T`
    rw [hR ω, (hrestr univ R MeasurableSet.univ (inter_univ _).symm rfl rfl).2, setIntegral_univ]
  · -- `X = τ(M ∩ E, θ, ξ)`
    obtain ⟨_, R', _, hc, hm, ho⟩ := hIMC.2.1 P n univ R E isOpen_univ hE
    exact ⟨R', fun ω => by rw [hX ω, (hrestr E R' hE hc hm ho).2]⟩

/-- **Mass measure of a current of finite mass** (Simon Ch. 6, (2.7)–(2.8); the measures of the
proof of the deformation theorem 5.1): if `X ∈ 𝒟_k(ℝᴾ)` has `M(X) < ∞`, then
`X(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)` for a finite measure `μ` with `M_W(X) = μ(W)` for every open `W`
and `μ(ℝᴾ \ spt X) = 0`, and a `μ`-a.e. strongly measurable `ξ` with `|⟨α, ξ(x)⟩| ≤ |α|`.
Since `M_W(X) ≤ M(X) < ∞`, the representation (REP) applies in `U = ℝᴾ`;
`μ(ℝᴾ) = M_{ℝᴾ}(X) = M(X) < ∞`, and `μ` is null off `spt X` by
`cmcsd_sh_measure_compl_support_eq_zero`. -/
theorem Submission.cmcsd_sh_finite_mass_measure : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k), X.mass < ∞ → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k), IsFiniteMeasure μ ∧ AEStronglyMeasurable ξ μ ∧ (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ W : Set (Euclid P), IsOpen W → X.massOn W = μ W) ∧ μ X.supportᶜ = 0 := by
  intro hVO hREP P k X hX
  -- Step 1: `M_W(X) ≤ M(X) < ∞` for every `W`, so (REP) applies in `U = ℝᴾ`
  have hfin : ∀ W : Set (Euclid P), IsOpen W → CompactlyContained W univ → X.massOn W < ∞ :=
    fun W _ _ => (X.massOn_mono (subset_univ W)).trans_lt hX
  -- Step 2: `X(ω) = ∫ ⟨ω, ξ⟩ dμ` with `|⟨α, ξ(x)⟩| ≤ |α|` and `M_W(X) = μ(W)` for open `W`
  obtain ⟨μ, ξ, -, -, hmass, hξm, hξ, hrep, -⟩ := hREP P k univ X isOpen_univ hfin
  -- Step 3: `μ(ℝᴾ) = M(X) < ∞`
  have hμ : IsFiniteMeasure μ := ⟨by rw [← hmass univ isOpen_univ]; exact hX⟩
  -- Steps 4–5: the bound holds everywhere, hence `μ`-a.e.; `μ` is null off `spt X`
  exact ⟨μ, ξ, hμ, hξm, ae_of_all μ hξ, hrep, hmass,
    Submission.cmcsd_sh_measure_compl_support_eq_zero hVO P k X μ hmass⟩
/-- **Simon 6.2.5** (evaluation bound by local mass): if `M_W(T) < ∞`, `spt ω ⊆ W` and
`|ω(x)| ≤ r` for every `x`, then `|T(ω)| ≤ r · M_W(T)`.  The Euclidean coefficient norm is
homogeneous, `|cα| = |c| |α|`, so for `s > 0` with `r ≤ s` both forms `±s⁻¹ω` are admissible for
`M_W(T)`; hence `|T(ω)| ≤ s · M_W(T)`, and `s ↓ r` gives the claim. -/
theorem Submission.cmr_abs_apply_le_massOn : ∀ (P n : ℕ) (U W : Set (Euclid P)) (T : GeometricCurrentOn U n) (ω : TestFormOn U n) (r : ℝ), T.massOn W ≠ ∞ → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ r) → |T ω| ≤ r * (T.massOn W).toReal := by
  intro P n U W T ω r hM hW hr
  -- homogeneity of the Euclidean coefficient norm
  have hsmul : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  have hr0 : 0 ≤ r := (covectorEuclideanNorm_nonneg _).trans (hr 0)
  -- `|T(ω)| ≤ s M_W(T)` for `0 < s`, `r ≤ s`: every `c • ω` with `|c| ≤ s⁻¹` is admissible
  have hbound : ∀ s : ℝ, 0 < s → r ≤ s → |T ω| ≤ s * (T.massOn W).toReal := by
    intro s hs hrs
    have hadm : ∀ c : ℝ, |c| ≤ s⁻¹ → c * T ω ≤ (T.massOn W).toReal := by
      intro c hc
      have hmem : c • ω ∈ massAdmissibleOn U n W := by
        refine ⟨(tsupport_smul_subset_right (fun _ => c) _).trans hW, fun x => ?_⟩
        show covectorEuclideanNorm (c • (ω : DifferentialForm (Euclid P) n) x) ≤ 1
        rw [hsmul]
        calc |c| * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ s⁻¹ * s :=
              mul_le_mul hc ((hr x).trans hrs) (covectorEuclideanNorm_nonneg _)
                (inv_nonneg.2 hs.le)
          _ = 1 := inv_mul_cancel₀ hs.ne'
      have h := (ENNReal.ofReal_le_iff_le_toReal hM).1 (T.le_massOn hmem)
      rwa [show T (c • ω) = c * T ω from T.toCurrent.map_smul c ω] at h
    have h1 := hadm s⁻¹ (abs_of_pos (inv_pos.2 hs)).le
    have h2 := hadm (-s⁻¹) (by rw [abs_neg, abs_of_pos (inv_pos.2 hs)])
    rw [neg_mul, ← mul_neg] at h2
    rw [abs_le]
    exact ⟨neg_le.1 ((inv_mul_le_iff₀ hs).1 h2), (inv_mul_le_iff₀ hs).1 h1⟩
  -- let `s ↓ r`
  have hlim : Tendsto (fun s : ℝ => s * (T.massOn W).toReal) (𝓝[>] r)
      (𝓝 (r * (T.massOn W).toReal)) :=
    ((continuous_mul_const _).tendsto r).mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs => hbound s (hr0.trans_lt hs) (le_of_lt hs))

/-- **Shell decomposition** (Simon Ch. 6, proof of the Deformation Theorem 5.1, (8) and
(17)–(19)).  Let `X(ω) = ∫ ⟨ω, ξ⟩ dμ` with `μ` finite and carried by `spt X`, `|ξ| ≤ 1` `μ`-a.e.,
let `Aⱼ = X⌞{d < rⱼ}` for a continuous `d` and a strictly decreasing `r` with `μ{d < rⱼ} → 0`, and
let `Y₀ = X − A₀`, `Yⱼ₊₁ = Aⱼ − Aⱼ₊₁`.  Then `Yⱼ` is `X` restricted to the shell
`{rⱼ ≤ d < rⱼ₋₁}` (`r₋₁ = ∞`), `Σⱼ Yⱼ(ω) = X(ω)`, `spt Yⱼ ⊆ spt X ∩ {rⱼ ≤ d}`, `spt Aⱼ ⊆ spt X`,
`M(Y₀) ≤ μ(ℝᴾ)` and `M(Yⱼ₊₁) ≤ μ{d < rⱼ}`; the support calculus and the mass bound
`M_V(X) ≤ μ(E ∩ V)` for currents represented by `μ⌞E` are hypotheses.  The shells are disjoint,
so `Σⱼ μ(shellⱼ) ≤ μ(ℝᴾ) < ∞`, and by 6.2.5 `|Yⱼ(ω)| ≤ sup|ω| · μ(shellⱼ)`; the partial sums are
`X(ω) − A_N(ω)` with `|A_N(ω)| ≤ sup|ω| · μ{d < r_N} → 0`. -/
theorem Submission.cmcsd_sh_shell_series : (∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support)) → (∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V)) → ∀ (P k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid P)) k) (A Y : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) k) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P k) (d : Euclid P → ℝ) (r : ℕ → ℝ), IsFiniteMeasure μ → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) k, |ξ x α| ≤ covectorEuclideanNorm α) → μ X.supportᶜ = 0 → Continuous d → StrictAnti r → Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, X ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), A j ω = ∫ x in {x | d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = X ω - A 0 ω) → (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = A j ω - A (j + 1) ω) → (∀ ω : TestFormOn (univ : Set (Euclid P)) k, Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k), Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω)) ∧ (∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (A j).support ⊆ X.support) ∧ (Y 0).mass ≤ μ univ ∧ (∀ j, (Y (j + 1)).mass ≤ μ {x | d x < r j}) := by
  intro hS hML P k X A Y μ ξ d r hμ hξm hξb hnull hd hr htend hX hA hY0 hYs
  have hdm : Measurable d := hd.measurable
  -- the integrand `x ↦ ξ x (ω x)` is bounded, a.e. strongly measurable and integrable
  have hcont : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Continuous (ω : DifferentialForm (Euclid P) k) := fun ω => ω.property.1.1.continuous
  have hnormcont : Continuous (fun α : Covector (Euclid P) k => covectorEuclideanNorm α) := by
    unfold covectorEuclideanNorm
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ =>
      continuous_if_const _ (fun _ => (continuous_eval_const _).pow 2) fun _ => continuous_const)
  have hbound : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, ∃ c : ℝ,
      ∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c := by
    intro ω
    obtain ⟨c, hc⟩ := (hnormcont.comp (hcont ω)).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P k))
    exact ⟨c, fun x => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hc x)⟩
  have hfm : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      AEStronglyMeasurable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω =>
    Continuous.comp_aestronglyMeasurable₂
      (g := fun (L : MultiVector P k) (α : Covector (Euclid P) k) => L α)
      isBoundedBilinearMap_apply.continuous hξm (hcont ω).aestronglyMeasurable
  have hfi : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Integrable (fun x => ξ x ((ω : DifferentialForm (Euclid P) k) x)) μ := fun ω => by
    obtain ⟨c, hc⟩ := hbound ω
    exact Integrable.of_bound (hfm ω) c
      (hξb.mono fun x hx => by rw [Real.norm_eq_abs]; exact (hx _).trans (hc x))
  -- the shell integrals
  have hlt : ∀ j, MeasurableSet {x | d x < r j} := fun j => measurableSet_lt hdm measurable_const
  have hge : ∀ j, MeasurableSet {x | r j ≤ d x} := fun j => measurableSet_le measurable_const hdm
  have hY0' : ∀ ω : TestFormOn (univ : Set (Euclid P)) k,
      Y 0 ω = ∫ x in {x | r 0 ≤ d x}, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro ω
    rw [hY0, hX, hA, ← integral_add_compl (hlt 0) (hfi ω)]
    have h : {x | d x < r 0}ᶜ = {x | r 0 ≤ d x} := by ext x; simp
    rw [h]; ring
  have hYs' : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y (j + 1) ω = ∫ x in {x | r (j + 1) ≤ d x ∧ d x < r j},
        ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    have hsub : {x | d x < r (j + 1)} ⊆ {x | d x < r j} :=
      fun x hx => lt_trans hx (hr (Nat.lt_succ_self j))
    have hset : {x | d x < r j} \ {x | d x < r (j + 1)} = {x | r (j + 1) ≤ d x ∧ d x < r j} :=
      Set.ext fun _ => ⟨fun h => ⟨not_lt.1 h.2, h.1⟩, fun h => ⟨h.2, not_lt.2 h.1⟩⟩
    rw [hYs, hA, hA, ← setIntegral_sdiff (hlt (j + 1)) (hfi ω).integrableOn hsub, hset]
  -- the shells as one family
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → Set (Euclid P), E 0 = {x | r 0 ≤ d x} ∧
      ∀ i, E (i + 1) = {x | r (i + 1) ≤ d x ∧ d x < r i} :=
    ⟨fun j => match j with
      | 0 => {x | r 0 ≤ d x}
      | i + 1 => {x | r (i + 1) ≤ d x ∧ d x < r i}, rfl, fun _ => rfl⟩
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    cases j with
    | zero => rw [hE0]; exact hge 0
    | succ i => rw [hEs]; exact (hge (i + 1)).inter (hlt i)
  have hEge : ∀ j, E j ⊆ {x | r j ≤ d x} := by
    intro j
    cases j with
    | zero => rw [hE0]
    | succ i => rw [hEs]; exact fun x hx => hx.1
  have hElt : ∀ i j, i < j → E j ⊆ {x | d x < r i} := by
    intro i j hij
    cases j with
    | zero => omega
    | succ j =>
      rw [hEs]
      exact fun x hx => lt_of_lt_of_le hx.2 (hr.antitone (by omega))
  have hdisj : Pairwise (Disjoint on E) := by
    intro i j hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r i ≤ d x from hEge i hxi) (not_le.2 (hElt i j h hxj))
    · exact Set.disjoint_left.2 fun x hxi hxj =>
        absurd (show r j ≤ d x from hEge j hxj) (not_le.2 (hElt j i h hxi))
  have hYE : ∀ (j : ℕ) (ω : TestFormOn (univ : Set (Euclid P)) k),
      Y j ω = ∫ x in E j, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ := by
    intro j ω
    cases j with
    | zero => rw [hE0]; exact hY0' ω
    | succ i => rw [hEs]; exact hYs' i ω
  -- masses of the shells and of the `Aⱼ`
  have hmassY : ∀ j, (Y j).massOn univ ≤ μ (E j) := fun j =>
    (hML P k univ (Y j) μ ξ (E j) univ hξb (hYE j)).trans (measure_mono inter_subset_left)
  have hmassA : ∀ j, (A j).massOn univ ≤ μ {x | d x < r j} := fun j =>
    (hML P k univ (A j) μ ξ _ univ hξb (hA j)).trans (measure_mono inter_subset_left)
  -- evaluation bound by mass (Simon 6.2.5)
  have hEB : ∀ (Z : GeometricCurrentOn (univ : Set (Euclid P)) k) (S : Set (Euclid P))
      (ω : TestFormOn (univ : Set (Euclid P)) k) (c : ℝ),
      (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x) ≤ c) →
      Z.massOn univ ≤ μ S → |Z ω| ≤ c * (μ S).toReal := by
    intro Z S ω c hc hZ
    have hne : Z.massOn univ ≠ ∞ := (hZ.trans_lt (measure_lt_top μ S)).ne
    have h0c : 0 ≤ c := (covectorEuclideanNorm_nonneg _).trans (hc 0)
    calc |Z ω| ≤ c * (Z.massOn univ).toReal :=
          Submission.cmr_abs_apply_le_massOn P k univ univ Z ω c hne (subset_univ _) hc
      _ ≤ c * (μ S).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ S) hZ) h0c
  -- the partial sums telescope to `X(ω) − A_N(ω)`, and `A_N(ω) → 0`
  have hpart : ∀ (ω : TestFormOn (univ : Set (Euclid P)) k) (N : ℕ),
      ∑ j ∈ Finset.range (N + 1), Y j ω = X ω - A N ω := by
    intro ω N
    induction N with
    | zero => simp [hY0]
    | succ N ih => rw [Finset.sum_range_succ, ih, hYs]; ring
  have hsum : ∀ ω : TestFormOn (univ : Set (Euclid P)) k, HasSum (fun j => Y j ω) (X ω) := by
    intro ω
    obtain ⟨c, hc⟩ := hbound ω
    have hsumE : ∑' j, μ (E j) ≠ ∞ := by
      rw [← measure_iUnion hdisj hEm]; exact measure_ne_top μ _
    have hsummable : Summable (fun j => Y j ω) := by
      refine Summable.of_norm_bounded ((ENNReal.summable_toReal hsumE).mul_left c) (fun j => ?_)
      rw [Real.norm_eq_abs]; exact hEB (Y j) (E j) ω c hc (hmassY j)
    rw [hsummable.hasSum_iff_tendsto_nat, ← tendsto_add_atTop_iff_nat 1]
    simp only [hpart]
    have hbd : ∀ n, ‖A n ω‖ ≤ c * (μ {x | d x < r n}).toReal := fun n => by
      rw [Real.norm_eq_abs]; exact hEB (A n) _ ω c hc (hmassA n)
    have hto : Tendsto (fun n => c * (μ {x | d x < r n}).toReal) atTop (𝓝 0) := by
      have h := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend).const_mul c
      simpa using h
    simpa using tendsto_const_nhds.sub (squeeze_zero_norm hbd hto)
  -- supports: `μ` is carried by `spt X`
  have hae : ∀ᵐ x ∂μ, x ∈ X.support := by
    have h := measure_eq_zero_iff_ae_notMem.1 hnull
    exact h.mono fun x hx => by simpa using hx
  have hvanish : ∀ (S F : Set (Euclid P)) (ω : TestFormOn (univ : Set (Euclid P)) k),
      MeasurableSet S → S ⊆ F →
      Disjoint (tsupport (ω : DifferentialForm (Euclid P) k)) (X.support ∩ F) →
      ∫ x in S, ξ x ((ω : DifferentialForm (Euclid P) k) x) ∂μ = 0 := by
    intro S F ω hSm hSF hdisj
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hae] with x hxS hxX
    have hx : x ∉ tsupport (ω : DifferentialForm (Euclid P) k) :=
      fun h => Set.disjoint_left.1 hdisj h ⟨hxX, hSF hxS⟩
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hsptY : ∀ j, (Y j).support ⊆ X.support ∩ {x | r j ≤ d x} := by
    intro j
    refine (hS P k).1 _ _ (((hS P k).2.1 X).inter (isClosed_le continuous_const hd))
      (fun ω hω => ?_)
    rw [hYE j]
    exact hvanish (E j) _ ω (hEm j) (hEge j) hω
  have hsptA : ∀ j, (A j).support ⊆ X.support := by
    intro j
    refine (hS P k).1 _ _ ((hS P k).2.1 X) (fun ω hω => ?_)
    rw [hA j]
    exact hvanish _ univ ω (hlt j) (subset_univ _) (by rwa [inter_univ])
  refine ⟨hY0', hYs', hsum, hsptY, hsptA, (hmassY 0).trans (measure_mono (subset_univ _)),
    fun j => (hmassY (j + 1)).trans (measure_mono ?_)⟩
  rw [hEs]
  exact fun x hx => hx.2
/-- **Good slicing radii in the dyadic shells** (Simon Ch. 6, proof of 5.1: display (10) and the
choice `ρ_j ∈ (2^{-j-1}, 2^{-j})`).  Given the good-radius lemma (GR) and, for `0 < r ≤ 1/4`,
`μ{d < r} ≤ C r^{m+2} M` and `μ'{d < r} ≤ C r^{m+2} M'`, there are strictly decreasing radii
`r_j ∈ ((1/2)^{j+3}, (1/2)^{j+2})` with `μ{d < r_j} ≤ C (1/2)^{(j+2)(m+2)} M` (likewise for `μ'`),
both tending to `0`, `liminf_{h↓0} h⁻¹ μ{r_j - h < d < r_j} ≤ 4C (1/2)^{(j+2)(m+1)} M` and
`liminf_{h↓0} h⁻¹ μ'{r_j - h < d < r_j} < ∞`. -/
theorem Submission.cmcsd_sh_dyadic_good_radii : (∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞) → ∀ (P m : ℕ) (μ μ' : Measure (Euclid P)) (d : Euclid P → ℝ) (C : NNReal) (M M' : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable d → M ≠ ∞ → M' ≠ ∞ → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → μ {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M ∧ μ' {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * M') → ∃ r : ℕ → ℝ, (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ StrictAnti r ∧ (∀ j, μ {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M ∧ μ' {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M') ∧ Tendsto (fun j => μ {x | d x < r j}) atTop (𝓝 0) ∧ Tendsto (fun j => μ' {x | d x < r j}) atTop (𝓝 0) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * M) ∧ (∀ j, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r j - h < d x ∧ d x < r j}) (𝓝[>] 0) < ∞) := by
  intro GR P m μ μ' d C M M' hμ hμ' hd hM hM' hdens
  -- Step 1: `ρ_j = (1/2)^(j+2) ∈ (0, 1/4]` and `ρ_j / 2 = (1/2)^(j+3)`
  have hρpos : ∀ j : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (j + 2) := fun j => by positivity
  have hρle : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 2) ≤ 1 / 4 := fun j =>
    calc (1 / 2 : ℝ) ^ (j + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have hhalf : ∀ j : ℕ, (1 / 2 : ℝ) ^ (j + 2) / 2 = (1 / 2 : ℝ) ^ (j + 3) := fun j => by ring
  -- Step 2: (GR) at `ρ_j` with `B_j = C ρ_j^{m+2} M`, chosen for every `j`
  have hgood : ∀ j : ℕ, ∃ r ∈ Ioo ((1 / 2 : ℝ) ^ (j + 2) / 2) ((1 / 2 : ℝ) ^ (j + 2)),
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < d x ∧ d x < r}) (𝓝[>] 0) ≤
        ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
          (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * M) ∧
      liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < d x ∧ d x < r}) (𝓝[>] 0) < ∞ :=
    fun j => GR P μ μ' d _ _ hμ hμ' hd (hρpos j) (hdens _ (hρpos j) (hρle j)).1
  choose r hr hrμ hrμ' using hgood
  have hlow : ∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j := fun j => hhalf j ▸ (hr j).1
  -- Step 3: `r_{j+1} < (1/2)^(j+3) < r_j`
  have hanti : StrictAnti r := strictAnti_nat_of_succ_lt fun j =>
    calc r (j + 1) < (1 / 2 : ℝ) ^ (j + 1 + 2) := (hr (j + 1)).2
      _ = (1 / 2 : ℝ) ^ (j + 3) := by ring
      _ < r j := hlow j
  -- Step 4: `{d < r_j} ⊆ {d < ρ_j}` and `ρ_j^{m+2} = (1/2)^((j+2)(m+2))`
  have hmass : ∀ j,
      μ {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M ∧
        μ' {x | d x < r j} ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M' := by
    intro j
    have hsub : {x | d x < r j} ⊆ {x | d x < (1 / 2 : ℝ) ^ (j + 2)} :=
      fun x (hx : d x < r j) => hx.trans (hr j).2
    rw [pow_mul]
    exact ⟨(measure_mono hsub).trans (hdens _ (hρpos j) (hρle j)).1,
      (measure_mono hsub).trans (hdens _ (hρpos j) (hρle j)).2⟩
  -- Step 5: `C (1/2)^((j+2)(m+2)) M₀ → 0` for `M₀ ≠ ∞`
  have hexp : Tendsto (fun j : ℕ => (j + 2) * (m + 2)) atTop atTop :=
    tendsto_atTop_mono
      (fun j => (Nat.le_add_right j 2).trans (Nat.le_mul_of_pos_right _ (by omega))) tendsto_id
  have hgeom : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hexp
  have hbound : ∀ M₀ : ℝ≥0∞, M₀ ≠ ∞ → Tendsto (fun j : ℕ =>
      (C : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * M₀) atTop (𝓝 0) := by
    intro M₀ hM₀
    have h1 := ENNReal.tendsto_ofReal hgeom
    rw [ENNReal.ofReal_zero] at h1
    simpa using ENNReal.Tendsto.mul_const
      (ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.coe_ne_top)) (Or.inr hM₀)
  -- Step 6: `ofReal (4/ρ) · C ρ^{m+2} M = 4 C ρ^{m+1} M` and `ρ_j^{m+1} = (1/2)^((j+2)(m+1))`
  have hslice : ∀ j : ℕ, ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
      (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * M) =
      4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * M := by
    intro j
    have h4 : 4 / (1 / 2 : ℝ) ^ (j + 2) * ((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2) =
        4 * ((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 1) := by
      field_simp
      ring
    have h1 : ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
        ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) =
        4 * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) := by
      rw [← ENNReal.ofReal_mul (by positivity), h4, ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_ofNat, pow_mul]
    calc ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
          (C * ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2)) * M)
        = C * (ENNReal.ofReal (4 / (1 / 2 : ℝ) ^ (j + 2)) *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ (j + 2)) ^ (m + 2))) * M := by ring
      _ = 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * M := by rw [h1]; ring
  exact ⟨r, fun j => ⟨hlow j, (hr j).2⟩, hanti, hmass,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbound M hM)
      (fun _ => zero_le) fun j => (hmass j).1,
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hbound M' hM')
      (fun _ => zero_le) fun j => (hmass j).2,
    fun j => (hrμ j).trans_eq (hslice j), hrμ'⟩
/-- **Boundary mass of a slice of a boundary current** (Simon Ch. 6, proof of 5.1, (8)–(10)).
Assume the slicing bounds (SL) of `cmc_slice_mass_bounds`.  If `∂T(η) = ∫ ⟨η, ξ⟩ dμ` and
`B(η) = ∫_{f<t} ⟨η, ξ⟩ dμ` for an `L`-Lipschitz `f`, then
`M_W(∂B) ≤ L · liminf_{h ↓ 0} h⁻¹ μ(W ∩ {t − h < f < t})` (trivially if `B` has degree `0`):
(SL) applied to `∂T`, whose boundary `∂∂T = 0` is represented by the zero measure. -/
theorem Submission.cmcsd_sh_slice_boundaryMassOn_le : (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (m + 1)) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P m) (f : Euclid P → ℝ) (L : NNReal) (t : ℝ) (B : GeometricCurrentOn U m) (W : Set (Euclid P)), IsOpen U → IsOpen W → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) m, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ η : TestFormOn U m, T.boundary η = ∫ x, ξ x ((η : DifferentialForm (Euclid P) m) x) ∂μ) → LipschitzWith L f → (∀ η : TestFormOn U m, B η = ∫ x in {x | f x < t}, ξ x ((η : DifferentialForm (Euclid P) m) x) ∂μ) → boundaryMassOn B W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0) := by
  intro SL P m
  cases m with
  | zero =>
    -- degree `0`: `boundaryMassOn B W = 0`
    intros
    exact zero_le
  | succ k =>
    intro U T μ ξ f L t B W hU hW hμ hξm hξb hT hf hB
    -- (SL) for `∂T` with `(μ, ξ)`, and the zero measure and orientation for `∂∂T = 0`
    obtain ⟨A, B', hA, hB', -, hSL4, -⟩ :=
      SL P k U T.boundary μ 0 ξ 0 f L hU hμ (fun _ _ _ => by simp) hξm
        (aestronglyMeasurable_zero_measure _) hξb (by simp) hT (fun η => by simp) hf
    -- (SL1), (SL2): `A_t = B` and `B'_t = 0`, so `∂A_t − B'_t = ∂B`
    have hAt : A t = B := GeometricCurrentOn.ext fun ω => (hA t ω).trans (hB ω).symm
    have hBt : B' t = 0 := GeometricCurrentOn.ext fun η => by simp [hB' t η]
    have hsub : (A t).boundary - B' t = B.boundary := by
      ext η
      change (A t).boundary η - B' t η = B.boundary η
      rw [hAt, hBt, GeometricCurrentOn.zero_apply, sub_zero]
    -- (SL4) on the open set `W`
    change B.boundary.massOn W ≤ _
    rw [← hsub]
    exact hSL4 W t hW
/-- **Mass of a difference** (Simon (6.2.5), chapter-06.txt line 231; this subadditivity makes the
flat distances `d_W` of 7.1 (lines 2018–2022) pseudometrics and is used in the proof of 7.2):
`M_G(A − B) ≤ M_G(A) + M_G(B)` for every set `G`.  If `ω` is admissible for `M_G` then so is `−ω`
(same support, same coefficient norm), and `(A − B)(ω) = A(ω) + B(−ω)`, so
`ofReal ((A − B)(ω)) ≤ ofReal (A(ω)) + ofReal (B(−ω)) ≤ M_G(A) + M_G(B)`. -/
theorem Submission.cmc_fc_cs_massOn_sub_le : ∀ (P n : ℕ) (U G : Set (Euclid P)) (A B : GeometricCurrentOn U n), (A - B).massOn G ≤ A.massOn G + B.massOn G := by
  intro P n U G A B
  -- Step 1: it suffices to bound `ofReal ((A − B)(ω))` for each admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  -- Step 2: `−ω` is admissible: same support, same coefficient norm
  have hneg : -ω ∈ massAdmissibleOn U n G := by
    refine ⟨?_, fun x => ?_⟩
    · rw [Submodule.coe_neg, tsupport_neg]
      exact hω.1
    · rw [Submodule.coe_neg, Pi.neg_apply, covectorEuclideanNorm_neg]
      exact hω.2 x
  -- Step 3: `(A − B)(ω) = A(ω) − B(ω) = A(ω) + B(−ω)`, by linearity of `B`
  have hsplit : (A - B) ω = A ω + B (-ω) := by
    have hB : B (-ω) = -B ω := B.toCurrent.map_neg ω
    change A ω - B ω = A ω + B (-ω)
    rw [hB, sub_eq_add_neg]
  -- Steps 4–5: `ofReal` is subadditive, and each term is bounded by the corresponding mass
  calc ENNReal.ofReal ((A - B) ω) = ENNReal.ofReal (A ω + B (-ω)) := by rw [hsplit]
    _ ≤ ENNReal.ofReal (A ω) + ENNReal.ofReal (B (-ω)) := ENNReal.ofReal_add_le
    _ ≤ A.massOn G + B.massOn G := add_le_add (A.le_massOn hω) (B.le_massOn hneg)

/-- **Boundary mass of differences and of boundaries** (Simon (6.2.3), (6.2.5), chapter-06.txt
lines 216–220 and 231), for `boundaryMassOn T G = M_G(∂T)` (`0` in degree `0`) and every set `G`:
`M_G(∂(X − Y)) ≤ M_G(∂X) + M_G(∂Y)` and `M_G(∂∂X) = 0`.  In positive degree
`∂(X − Y) = ∂X − ∂Y`, so the first claim is `M_G(A − B) ≤ M_G(A) + M_G(B)`; the second is
`∂²X = 0` together with `M_G(0) = 0`. -/
theorem Submission.cmcsd_sh_boundaryMassOn_calculus : ∀ (P m : ℕ) (U G : Set (Euclid P)), (∀ X Y : GeometricCurrentOn U m, boundaryMassOn (X - Y) G ≤ boundaryMassOn X G + boundaryMassOn Y G) ∧ ∀ X : GeometricCurrentOn U (m + 1), boundaryMassOn X.boundary G = 0 := by
  intro P m U G
  -- Step 1: `M_G(0) = 0` in every degree, since `0(ω) = 0` for every admissible `ω`
  have hzero : ∀ k : ℕ, (0 : GeometricCurrentOn U k).massOn G = 0 := by
    intro k
    refine le_antisymm (sSup_le ?_) zero_le
    rintro _ ⟨ω, -, rfl⟩
    exact ENNReal.ofReal_zero.le
  cases m with
  | zero =>
    -- Step 2: in degree `0`, `boundaryMassOn` is `0` by definition
    exact ⟨fun X Y => zero_le, fun X => rfl⟩
  | succ k =>
    refine ⟨fun X Y => ?_, fun X => ?_⟩
    · -- Step 3: `∂(X − Y) = ∂X − ∂Y` (definitional), then subadditivity of `M_G`
      have hsub : (X - Y).boundary = X.boundary - Y.boundary :=
        GeometricCurrentOn.ext fun η => rfl
      change (X - Y).boundary.massOn G ≤ X.boundary.massOn G + Y.boundary.massOn G
      rw [hsub]
      exact Submission.cmc_fc_cs_massOn_sub_le P k U G X.boundary Y.boundary
    · -- Step 4: `∂∂X = 0`, so `boundaryMassOn (∂X) G = M_G(0) = 0`
      change X.boundary.boundary.massOn G = 0
      rw [GeometricCurrentOn.boundary_boundary]
      exact hzero k
/-- **Support calculus** for currents in `ℝᴾ` (Simon 6.2.11): (i) if `E` is closed and `X(ω) = 0`
whenever `spt ω ∩ E = ∅`, then `spt X ⊆ E`; (ii) `spt X` is closed; (iii)
`spt(A − B) ⊆ spt A ∪ spt B`; (iv) `spt 0 = ∅`; (v) `spt ∂A ⊆ spt A`.  A point lies off `spt X`
iff it has an open neighbourhood with compact closure on which `X` vanishes.  Small balls are such
neighbourhoods in the proper space `ℝᴾ`; zero neighbourhoods of `A` and `B` intersect to one of
`A − B`; and since `spt dη ⊆ spt η`, a zero neighbourhood of `A` is one of `∂A`. -/
theorem Submission.cmcsd_support_calculus : ∀ (P n : ℕ), (∀ (E : Set (Euclid P)) (X : GeometricCurrentOn (univ : Set (Euclid P)) n), IsClosed E → (∀ ω : TestFormOn (univ : Set (Euclid P)) n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) E → X ω = 0) → X.support ⊆ E) ∧ (∀ X : GeometricCurrentOn (univ : Set (Euclid P)) n, IsClosed X.support) ∧ (∀ A B : GeometricCurrentOn (univ : Set (Euclid P)) n, (A - B).support ⊆ A.support ∪ B.support) ∧ (0 : GeometricCurrentOn (univ : Set (Euclid P)) n).support = ∅ ∧ (∀ A : GeometricCurrentOn (univ : Set (Euclid P)) (n + 1), A.boundary.support ⊆ A.support) := by
  intro P n
  -- `B_ε(x)` is open, and its closure lies in the compact `closedBall x ε` (`ℝᴾ` is proper)
  have hball : ∀ (x : Euclid P) (ε : ℝ), IsOpen (ball x ε) ∧ IsCompact (closure (ball x ε)) ∧
      closure (ball x ε) ⊆ univ := fun x ε =>
    ⟨isOpen_ball, (isCompact_closedBall x ε).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall, subset_univ _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (i) for `x ∉ E`, a ball around `x` inside the open set `Eᶜ` is a zero neighbourhood of `x`
    intro E X hE hX x hx
    by_contra hxE
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
    refine hx.2 (mem_sUnion_of_mem (mem_ball_self hε)
      ⟨(hball x ε).1, (hball x ε).2.1, (hball x ε).2.2, fun ω hω => hX ω ?_⟩)
    exact subset_compl_iff_disjoint_right.mp (hω.trans hεE)
  · -- (ii) `spt X = univ \ X.zeroRegion`, and the zero region is open
    intro X
    exact isClosed_univ.sdiff X.isOpen_zeroRegion
  · -- (iii) the intersection of zero neighbourhoods of `A` and `B` is one of `A − B`
    intro A B x hx
    by_contra hAB
    have hxA : x ∈ A.zeroRegion := by
      by_contra h
      exact hAB (mem_union_left _ ⟨mem_univ x, h⟩)
    have hxB : x ∈ B.zeroRegion := by
      by_contra h
      exact hAB (mem_union_right _ ⟨mem_univ x, h⟩)
    obtain ⟨WA, ⟨hWAo, hWAc, -, hWAv⟩, hxWA⟩ := mem_sUnion.mp hxA
    obtain ⟨WB, ⟨hWBo, -, -, hWBv⟩, hxWB⟩ := mem_sUnion.mp hxB
    refine hx.2 (mem_sUnion_of_mem (⟨hxWA, hxWB⟩ : x ∈ WA ∩ WB) ⟨hWAo.inter hWBo,
      hWAc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left), subset_univ _,
      fun ω hω => ?_⟩)
    change A ω - B ω = 0
    rw [hWAv ω (hω.trans inter_subset_left), hWBv ω (hω.trans inter_subset_right), sub_zero]
  · -- (iv) every ball is a zero neighbourhood of the zero current
    exact eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (mem_sUnion_of_mem
      (mem_ball_self one_pos) ⟨(hball x 1).1, (hball x 1).2.1, (hball x 1).2.2,
        fun ω _ => GeometricCurrentOn.zero_apply ω⟩)
  · -- (v) `∂A(η) = A(dη)` with `spt dη ⊆ spt η`: a zero neighbourhood of `A` is one of `∂A`
    intro A x hx
    refine ⟨mem_univ x, fun hxA => hx.2 ?_⟩
    obtain ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hxW⟩ := mem_sUnion.mp hxA
    refine mem_sUnion_of_mem hxW ⟨hWo, hWc, hWU, fun η hη => ?_⟩
    rw [GeometricCurrentOn.boundary_apply]
    exact hWv _ ((tsupport_exteriorDerivative_subset (η : DifferentialForm (Euclid P) n)).trans hη)
/-- **Simon (6.2.5)** for a current given by integration against a multivector field of norm at
most one: if `X(ω) = ∫_E ⟨ω(x), ξ(x)⟩ dμ(x)` for every `ω ∈ 𝒟^d(U)` and
`|⟨α, ξ(x)⟩| ≤ |α|` for `μ`-a.e. `x`, then `M_V(X) ≤ μ(E ∩ V)` for every set `V` (the estimates
`M(W_j) ≤ μ_T(E_j)`, `M(D_j) ≤ μ_∂(E_j)` of the deformation step).  For `ω` admissible for
`M_V(X)`, `|⟨ω(x), ξ(x)⟩|` is at most `1` on `spt ω ⊆ V` and vanishes off `spt ω`, so
`X(ω) ≤ ∫_E |⟨ω, ξ⟩| dμ ≤ μ(spt ω ∩ E) ≤ μ(E ∩ V)`. -/
theorem Submission.cmcsd_massOn_le_measure_inter : ∀ (P d : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U d) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P d) (E V : Set (Euclid P)), (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) d, |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U d, X ω = ∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) → X.massOn V ≤ μ (E ∩ V) := by
  intro P d U X μ ξ E V hξ hX
  -- Step 1: it suffices to bound `ofReal (X ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro _ ⟨ω, hω, rfl⟩
  have hS : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) d)) :=
    (isClosed_tsupport _).measurableSet
  -- Step 2: `|⟨ω(x), ξ(x)⟩| ≤ 1` on `spt ω` and `= 0` off `spt ω`, for `μ`-a.e. `x`
  have hpt : ∀ᵐ x ∂μ.restrict E, ‖ξ x ((ω : DifferentialForm (Euclid P) d) x)‖ₑ ≤
      (tsupport (ω : DifferentialForm (Euclid P) d)).indicator 1 x := by
    refine ae_restrict_of_ae (hξ.mono fun x hx => ?_)
    by_cases hx' : x ∈ tsupport (ω : DifferentialForm (Euclid P) d)
    · rw [indicator_of_mem hx', Pi.one_apply, Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.2 ((hx _).trans (hω.2 x))
    · rw [image_eq_zero_of_notMem_tsupport hx', map_zero, enorm_zero]
      exact zero_le
  -- Step 3: `ofReal X(ω) ≤ ‖∫_E ⟨ω, ξ⟩ dμ‖ₑ ≤ ∫⁻_E ‖⟨ω, ξ⟩‖ₑ dμ ≤ μ(spt ω ∩ E) ≤ μ(E ∩ V)`
  calc ENNReal.ofReal (X ω)
      = ENNReal.ofReal (∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ) := by
        rw [hX]
    _ ≤ ‖∫ x in E, ξ x ((ω : DifferentialForm (Euclid P) d) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in E, ‖ξ x ((ω : DifferentialForm (Euclid P) d) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in E, (tsupport (ω : DifferentialForm (Euclid P) d)).indicator 1 x ∂μ :=
        lintegral_mono_ae hpt
    _ = μ (tsupport (ω : DifferentialForm (Euclid P) d) ∩ E) := by
        rw [lintegral_indicator_one hS, Measure.restrict_apply hS]
    _ ≤ μ (E ∩ V) := measure_mono fun x hx => ⟨hx.2, hω.1 hx.1⟩
/-- **Left slopes at a point of differentiability** (Simon Ch. 6, 4.9 and (2) in the proof of
8.2).  If `F : ℝ → ℝ` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * ofReal (F(t) - F(t - h)) ≤ ofReal (F′(t))`.  The left difference
quotients `h⁻¹ (F(t) - F(t - h))` tend to `F′(t)` as `h ↓ 0`; for `h > 0` the product above is
`ofReal` of the quotient, so it tends to `ofReal (F′(t))`, and along `𝓝[>] 0` the liminf of a
convergent function is its limit.  Monotonicity of `F` is not needed. -/
theorem Submission.cbr_smm_liminf_left_slope_le_deriv : ∀ (F : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ F t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h))) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv F t) := by
  intro F t hF
  -- `h ↦ -h` maps `𝓝[>] 0` into `𝓝[<] 0`, turning left slopes into the quotients above
  have hneg : Tendsto (fun h : ℝ => -h) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
  have hlim : Tendsto (fun h : ℝ => h⁻¹ * (F t - F (t - h))) (𝓝[>] 0) (𝓝 (deriv F t)) := by
    refine (hF.hasDerivAt.tendsto_slope_zero_left.comp hneg).congr fun h => ?_
    simp only [Function.comp_apply, smul_eq_mul]
    rw [← sub_eq_add_neg, inv_neg]
    ring
  -- for `h > 0`, `ofReal h⁻¹ * ofReal (F t - F (t - h)) = ofReal (h⁻¹ * (F t - F (t - h)))`
  have hlim' : Tendsto (fun h : ℝ => ENNReal.ofReal h⁻¹ * ENNReal.ofReal (F t - F (t - h)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (deriv F t))) := by
    refine (ENNReal.tendsto_ofReal hlim).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    exact ENNReal.ofReal_mul (inv_nonneg.2 hh.le)
  exact hlim'.liminf_eq.le
/-- **Lebesgue's inequality for monotone functions** (Simon Ch. 6, remark before 4.10): if `F` is
nondecreasing, then `∫⁻_{(a,b)} F′ ≤ F(b) − F(a)`.  Let `G = F(·⁺)` be the Stieltjes function of
`F`, with measure `μ_G`; then `μ_G (a, b) = G(b⁻) − G(a) ≤ F(b) − F(a)`.  By Lebesgue's theorem
(`Monotone.ae_hasDerivAt`), `F′ = dμ_G/dt` a.e., and `∫⁻_{(a,b)} dμ_G/dt ≤ μ_G (a, b)` since
`(dμ_G/dt) dt ≤ μ_G` (Lebesgue decomposition). -/
theorem Submission.cmcs_smi_lintegral_ofReal_deriv_le : ∀ (F : ℝ → ℝ) (a b : ℝ), Monotone F → ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t) ≤ ENNReal.ofReal (F b - F a) := by
  intro F a b hF
  set G := hF.stieltjesFunction
  -- `F(a) ≤ F(a⁺) = G(a)`, and `G(b⁻) ≤ F(b)` because `G(y) = F(y⁺) ≤ F(b)` for `y < b`
  have hGa : F a ≤ G a := hF.le_rightLim le_rfl
  have hGb : leftLim G b ≤ F b := by
    refine le_of_tendsto (G.mono.tendsto_leftLim b) ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y < b)
    exact hF.rightLim_le hy
  calc ∫⁻ t in Ioo a b, ENNReal.ofReal (deriv F t)
      ≤ ∫⁻ t in Ioo a b, G.measure.rnDeriv volume t := by
        -- a.e. `F′(t) = (dμ_G/dt)(t).toReal`
        refine lintegral_mono_ae (ae_restrict_of_ae ?_)
        filter_upwards [hF.ae_hasDerivAt] with t ht
        rw [ht.deriv]
        exact ENNReal.ofReal_toReal_le
    _ ≤ volume.withDensity (G.measure.rnDeriv volume) (Ioo a b) := withDensity_apply_le _ _
    _ ≤ G.measure (Ioo a b) := Measure.le_iff'.1 (Measure.withDensity_rnDeriv_le _ _) _
    _ = ENNReal.ofReal (leftLim G b - G a) := G.measure_Ioo
    _ ≤ ENNReal.ofReal (F b - F a) := ENNReal.ofReal_le_ofReal (by linarith)

/-- **Left slice density at a point of differentiability of the distribution function** (Simon
Ch. 6, remark after 4.9 and (10) in the proof of 5.1).  For a finite measure `μ`, a measurable
`f` and `F(s) = (μ {f < s}).toReal`: if `F` is differentiable at `t`, then
`liminf_{h → 0+} ofReal (h⁻¹) * μ {t - h < f < t} ≤ ofReal (F′(t))`.  For `h > 0`,
`{t - h < f < t} ⊆ {f < t} \ {f < t - h}`, whose measure is `ofReal (F(t) - F(t - h))` since `μ`
is finite; so the claim follows from `Submission.cbr_smm_liminf_left_slope_le_deriv`. -/
theorem Submission.cmcsd_gr_liminf_slice_le_deriv : ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (t : ℝ), IsFiniteMeasure μ → Measurable f → DifferentiableAt ℝ (fun s : ℝ => (μ {x | f x < s}).toReal) t → liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | t - h < f x ∧ f x < t}) (𝓝[>] 0) ≤ ENNReal.ofReal (deriv (fun s : ℝ => (μ {x | f x < s}).toReal) t) := by
  intro α _ μ f t _ hf hF
  -- `μ` is finite, so `μ {f < s} = ofReal F(s)` with `F(s) = (μ {f < s}).toReal ≥ 0`
  have hA : ∀ s : ℝ, μ {x | f x < s} = ENNReal.ofReal (μ {x | f x < s}).toReal := fun s =>
    (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  -- for `h > 0`, `{t - h < f < t} ⊆ {f < t} \ {f < t - h}`, of measure `ofReal (F(t) - F(t - h))`
  have hslice : ∀ h : ℝ, 0 < h → ENNReal.ofReal h⁻¹ * μ {x | t - h < f x ∧ f x < t} ≤
      ENNReal.ofReal h⁻¹ *
        ENNReal.ofReal ((μ {x | f x < t}).toReal - (μ {x | f x < t - h}).toReal) := by
    intro h hh
    gcongr
    calc μ {x | t - h < f x ∧ f x < t}
        ≤ μ ({x | f x < t} \ {x | f x < t - h}) :=
          measure_mono fun x hx => ⟨hx.2, fun hx' => lt_asymm hx.1 hx'⟩
      _ = μ {x | f x < t} - μ {x | f x < t - h} :=
          measure_sdiff (fun x (hx : f x < t - h) => hx.trans (by linarith))
            (measurableSet_lt hf measurable_const).nullMeasurableSet (measure_ne_top μ _)
      _ = ENNReal.ofReal ((μ {x | f x < t}).toReal - (μ {x | f x < t - h}).toReal) := by
          rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ← hA, ← hA]
  -- compare the liminfs along `𝓝[>] 0`, then use the left slopes of `F` at `t`
  calc liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | t - h < f x ∧ f x < t}) (𝓝[>] 0)
      ≤ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ *
          ENNReal.ofReal ((μ {x | f x < t}).toReal - (μ {x | f x < t - h}).toReal)) (𝓝[>] 0) :=
        liminf_le_liminf (eventually_nhdsWithin_of_forall hslice)
    _ ≤ ENNReal.ofReal (deriv (fun s : ℝ => (μ {x | f x < s}).toReal) t) :=
        Submission.cbr_smm_liminf_left_slope_le_deriv (fun s => (μ {x | f x < s}).toReal) t hF
/-- **Markov choice of a radius off a null set** (Simon Ch. 6, proof of 5.1 (10)): if `F` is
nondecreasing, `ρ > 0` and `F(ρ) − F(ρ/2) ≤ B`, then outside any Lebesgue-null set `N` there is
`r ∈ (ρ/2, ρ)` with `F′(r) ≤ (4/ρ) B`.  By Lebesgue's inequality `∫⁻_{(ρ/2,ρ)} F′ ≤ B`, so by
Markov's inequality `{t ∈ (ρ/2, ρ) : F′(t) > (4/ρ) B}` has measure `≤ ρ/4 < ρ/2`; hence
`S = {t ∈ (ρ/2, ρ) : F′(t) ≤ (4/ρ) B}` has positive measure and meets the complement of `N`. -/
theorem Submission.cmcsd_gr_exists_deriv_le_off_null : ∀ (F : ℝ → ℝ) (ρ : ℝ) (B : ℝ≥0∞) (N : Set ℝ), Monotone F → 0 < ρ → ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ B → (volume : Measure ℝ) N = 0 → ∃ r ∈ Ioo (ρ / 2) ρ, r ∉ N ∧ ENNReal.ofReal (deriv F r) ≤ ENNReal.ofReal (4 / ρ) * B := by
  intro F ρ B N hF hρ hB hN
  -- `g = ofReal ∘ F′`, `c = (4/ρ) B`, `I = (ρ/2, ρ)`, `S = {t ∈ I : g t ≤ c}`
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (deriv F t)
  set c := ENNReal.ofReal (4 / ρ) * B with hc
  set I := Ioo (ρ / 2) ρ with hI
  set S := {t ∈ I | g t ≤ c}
  have hI_meas : MeasurableSet I := measurableSet_Ioo
  have hI_vol : volume I = ENNReal.ofReal (ρ / 2) := by
    rw [hI, Real.volume_Ioo]
    congr 1
    ring
  have hI_pos : 0 < volume I := by
    rw [hI_vol]
    exact ENNReal.ofReal_pos.2 (half_pos hρ)
  have h4 : ENNReal.ofReal (4 / ρ) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hg : Measurable g := (measurable_deriv F).ennreal_ofReal
  -- Lebesgue's inequality: `∫⁻_I g ≤ F(ρ) − F(ρ/2) ≤ B`
  have hint : ∫⁻ t in I, g t ≤ B :=
    (Submission.cmcs_smi_lintegral_ofReal_deriv_le F (ρ / 2) ρ hF).trans hB
  have hcover : volume I ≤ volume S + volume (I \ S) :=
    calc volume I ≤ volume (S ∪ (I \ S)) := measure_mono fun t ht => by
          by_cases h : t ∈ S
          · exact Or.inl h
          · exact Or.inr ⟨ht, h⟩
      _ ≤ volume S + volume (I \ S) := measure_union_le S (I \ S)
  have hS_pos : 0 < volume S := by
    rcases eq_or_ne B ∞ with hBt | hBt
    · -- `c = ∞`, so `S = I`
      have hS_eq : S = I := by
        refine Subset.antisymm (fun t ht => ht.1) fun t ht => ⟨ht, ?_⟩
        rw [hc, hBt, ENNReal.mul_top h4]
        exact le_top
      rw [hS_eq]
      exact hI_pos
    rcases eq_or_ne B 0 with hB0 | hB0
    · -- `∫⁻_I g = 0`, so `g = 0` a.e. on `I` and `I \ S` is null
      have hae : g =ᵐ[volume.restrict I] 0 :=
        (lintegral_eq_zero_iff hg).1 (le_antisymm (hint.trans hB0.le) zero_le)
      rw [Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hI_meas] at hae
      have hnull : volume (I \ S) = 0 := by
        refine measure_mono_null (fun t ht => ?_) hae
        refine ⟨fun h => ht.2 ⟨ht.1, ?_⟩, ht.1⟩
        rw [h]
        exact zero_le
      rw [hnull, add_zero] at hcover
      exact hI_pos.trans_le hcover
    · -- Markov: `c · |E| ≤ B` for `E = {c ≤ g} ∩ I`, so `|I \ S| ≤ |E| ≤ ρ/4 < ρ/2 = |I|`
      have hmarkov := mul_meas_ge_le_lintegral₀ (μ := volume.restrict I) hg.aemeasurable c
      rw [Measure.restrict_apply' hI_meas] at hmarkov
      have hE : volume ({t | c ≤ g t} ∩ I) ≤ ENNReal.ofReal (ρ / 4) := by
        have h1 : B * (ENNReal.ofReal (4 / ρ) * volume ({t | c ≤ g t} ∩ I)) ≤ B * 1 :=
          calc B * (ENNReal.ofReal (4 / ρ) * volume ({t | c ≤ g t} ∩ I))
              = c * volume ({t | c ≤ g t} ∩ I) := by rw [hc]; ring
            _ ≤ ∫⁻ t in I, g t := hmarkov
            _ ≤ B := hint
            _ = B * 1 := (mul_one B).symm
        rw [ENNReal.mul_le_mul_iff_right hB0 hBt, mul_comm, ← ENNReal.le_inv_iff_mul_le,
          ← ENNReal.ofReal_inv_of_pos (by positivity), inv_div] at h1
        exact h1
      have hsub : I \ S ⊆ {t | c ≤ g t} ∩ I := fun t ht =>
        ⟨(not_le.1 fun h => ht.2 ⟨ht.1, h⟩).le, ht.1⟩
      have hdiff : volume (I \ S) ≤ ENNReal.ofReal (ρ / 4) := (measure_mono hsub).trans hE
      refine pos_iff_ne_zero.2 fun h0 => ?_
      have hle := hcover.trans (add_le_add h0.le hdiff)
      rw [zero_add, hI_vol, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
      linarith
  -- `S \ N` has the measure of `S`, so it is nonempty
  have hSN : volume (S \ N) ≠ 0 := by
    rw [measure_sdiff_null hN]
    exact hS_pos.ne'
  obtain ⟨r, ⟨hrI, hrc⟩, hrN⟩ := nonempty_of_measure_ne_zero hSN
  exact ⟨r, hrI, hrN, hrc⟩

/-- **Choice of a good slicing radius** (Simon Ch. 6, proof of 5.1, (8)–(10)).  If `μ`, `μ'` are
finite and `μ {f < ρ} ≤ B`, some `r ∈ (ρ/2, ρ)` has
`liminf_{h → 0+} h⁻¹ μ {r - h < f < r} ≤ (4/ρ) B` and `liminf_{h → 0+} h⁻¹ μ' {r - h < f < r} < ∞`.
The distribution functions `F(t) = μ {f < t}` and `G(t) = μ' {f < t}` are monotone, hence
differentiable off a Lebesgue null set `N`.  As `F(ρ) - F(ρ/2) ≤ F(ρ) ≤ B`, a Markov argument on
`(ρ/2, ρ)` gives `r ∉ N` with `F′(r) ≤ (4/ρ) B`; at such `r` the liminfs are at most `F′(r)` and
`G′(r) < ∞`. -/
theorem Submission.cmcsd_good_radius : ∀ (P : ℕ) (μ μ' : Measure (Euclid P)) (f : Euclid P → ℝ) (ρ : ℝ) (B : ℝ≥0∞), IsFiniteMeasure μ → IsFiniteMeasure μ' → Measurable f → 0 < ρ → μ {x | f x < ρ} ≤ B → ∃ r ∈ Ioo (ρ / 2) ρ, liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) ≤ ENNReal.ofReal (4 / ρ) * B ∧ liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ' {x | r - h < f x ∧ f x < r}) (𝓝[>] 0) < ∞ := by
  intro P μ μ' f ρ B hμ hμ' hf hρ hB
  set F : ℝ → ℝ := fun s => (μ {x | f x < s}).toReal
  set G : ℝ → ℝ := fun s => (μ' {x | f x < s}).toReal
  have hFm : Monotone F := fun s t hst =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x (hx : f x < s) => hx.trans_le hst)
  have hGm : Monotone G := fun s t hst =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun x (hx : f x < s) => hx.trans_le hst)
  -- Lebesgue: `F` and `G` are differentiable off a null set `N`
  set N : Set ℝ := {t | ¬(DifferentiableAt ℝ F t ∧ DifferentiableAt ℝ G t)}
  have hN : (volume : Measure ℝ) N = 0 :=
    ae_iff.1 (hFm.ae_differentiableAt.and hGm.ae_differentiableAt)
  have hFB : ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ B :=
    calc ENNReal.ofReal (F ρ - F (ρ / 2)) ≤ ENNReal.ofReal (F ρ) :=
          ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)
      _ = μ {x | f x < ρ} := ENNReal.ofReal_toReal (measure_ne_top _ _)
      _ ≤ B := hB
  -- Markov on `(ρ/2, ρ)`: some `r ∉ N` has `F′(r) ≤ (4/ρ) B`
  obtain ⟨r, hr, hrN, hrF⟩ := Submission.cmcsd_gr_exists_deriv_le_off_null F ρ B N hFm hρ hFB hN
  have hrd : DifferentiableAt ℝ F r ∧ DifferentiableAt ℝ G r := not_not.1 hrN
  refine ⟨r, hr, ?_, ?_⟩
  · exact (Submission.cmcsd_gr_liminf_slice_le_deriv (Euclid P) μ f r hμ hf hrd.1).trans hrF
  · exact (Submission.cmcsd_gr_liminf_slice_le_deriv (Euclid P) μ' f r hμ' hf hrd.2).trans_lt
      ENNReal.ofReal_lt_top
/-- **Componentwise McShane extension into `ℝᴾ`.**  If `ψ : ℝᴾ → ℝᴾ` is `K`-Lipschitz on `S`, then
some `φ : ℝᴾ → ℝᴾ` is `√P·K`-Lipschitz on `ℝᴾ` and agrees with `ψ` on `S`: each coordinate
`x ↦ ψ(x)ᵢ` is extended by McShane (`LipschitzOnWith.extend_real`). -/
theorem Submission.cmcsd_lipschitz_extension : ∀ (P : ℕ) (S : Set (Euclid P)) (ψ : Euclid P → Euclid P) (K : NNReal), LipschitzOnWith K ψ S → ∃ φ : Euclid P → Euclid P, LipschitzWith (NNReal.sqrt P * K) φ ∧ EqOn φ ψ S := by
  intro P S ψ K hψ
  -- (1) each coordinate `ψᵢ = (ψ ·) i` is `K`-Lipschitz on `S`: `|vᵢ| ≤ ‖v‖`
  have hcoord : ∀ i : Fin P, LipschitzOnWith K (fun x => ψ x i) S := fun i =>
    LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
      (PiLp.dist_apply_le (ψ x) (ψ y) i).trans (hψ.dist_le_mul x hx y hy)
  -- (2) McShane: a `K`-Lipschitz `gᵢ : ℝᴾ → ℝ` with `gᵢ = ψᵢ` on `S`, for every `i`
  choose g hg using fun i => (hcoord i).extend_real
  -- (3) `φ(x) = (gᵢ(x))ᵢ`
  refine ⟨fun x => WithLp.toLp 2 fun i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_,
    fun x hx => ?_⟩
  · -- (4) `dist(φ x, φ y)² = ∑ᵢ (gᵢ x − gᵢ y)² ≤ P K² dist(x, y)²`
    have hsum : ∑ i : Fin P, dist (g i x) (g i y) ^ 2 ≤ (P : ℝ) * ((K : ℝ) * dist x y) ^ 2 := by
      calc ∑ i : Fin P, dist (g i x) (g i y) ^ 2 ≤ ∑ _i : Fin P, ((K : ℝ) * dist x y) ^ 2 := by
            gcongr with i
            exact (hg i).1.dist_le_mul x y
        _ = (P : ℝ) * ((K : ℝ) * dist x y) ^ 2 := by simp
    rw [EuclideanSpace.dist_eq]
    calc √(∑ i : Fin P, dist (g i x) (g i y) ^ 2)
        ≤ √((P : ℝ) * ((K : ℝ) * dist x y) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = ↑(NNReal.sqrt P * K) * dist x y := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
          simp [mul_assoc]
  · -- (5) `φ = ψ` on `S`, coordinatewise
    ext i
    exact ((hg i).2 hx).symm
/-- **Dyadic series estimates** for the deformation theorem (Simon Ch. 6, proof of 5.1).  If
`Λⱼ ≤ c₄ 2ʲ`, then: (1) for `p ≤ q`, `a₀ ≤ A` and `a_{j+1} ≤ C 2^{−(j+2)(q+1)} A`,
`∑ⱼ (2Λⱼ)ᵖ aⱼ ≤ (2c₄)ᵖ (1 + C) A`; (2) for finite `K`, `A` and `zⱼ ≤ K 2^{−(j+2)(p+1)} A`,
`(2Λⱼ)ᵖ zⱼ → 0`. -/
theorem Submission.cmcsd_dyadic_series_bounds : ∀ (c₄ : NNReal) (Λ : ℕ → NNReal), (∀ j, (Λ j : ℝ) ≤ c₄ * 2 ^ j) → (∀ (C : NNReal) (A : ℝ≥0∞) (p q : ℕ) (a : ℕ → ℝ≥0∞), p ≤ q → a 0 ≤ A → (∀ j, a (j + 1) ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (q + 1))) * A) → ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ p * a j ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * (1 + C) * A) ∧ (∀ (K A : ℝ≥0∞) (p : ℕ) (z : ℕ → ℝ≥0∞), K ≠ ∞ → A ≠ ∞ → (∀ j, z j ≤ K * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (p + 1))) * A) → Tendsto (fun j => (2 * (Λ j : ℝ≥0∞)) ^ p * z j) atTop (𝓝 0)) := by
  intro c₄ Λ hΛ
  -- `ofReal ((1/2)^e) = ι^e` with `ι = 2⁻¹`, and `2^m · ι^m = 1`
  have hhalf : ∀ e : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ e) = (2⁻¹ : ℝ≥0∞) ^ e := by
    intro e
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div,
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
  have hcancel : ∀ m : ℕ, (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ m = 1 := by
    intro m
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hι1 : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.one_half_lt_one.le
  -- `2^m · ι^e ≤ ι^r` whenever `m + r ≤ e`
  have hshift : ∀ m r e : ℕ, m + r ≤ e →
      (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ e ≤ (2⁻¹ : ℝ≥0∞) ^ r := by
    intro m r e hle
    calc (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ e ≤ (2 : ℝ≥0∞) ^ m * (2⁻¹ : ℝ≥0∞) ^ (m + r) :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hι1 hle)
      _ = (2⁻¹ : ℝ≥0∞) ^ r := by rw [pow_add, ← mul_assoc, hcancel, one_mul]
  -- Step 0: `(2Λ_j)^p ≤ (2c₄)^p · 2^{jp}`
  have hw : ∀ p j : ℕ, (2 * (Λ j : ℝ≥0∞)) ^ p ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) := by
    intro p j
    have h1 : Λ j ≤ c₄ * 2 ^ j := by exact_mod_cast hΛ j
    have h2 : (Λ j : ℝ≥0∞) ≤ (c₄ : ℝ≥0∞) * 2 ^ j := by exact_mod_cast h1
    calc (2 * (Λ j : ℝ≥0∞)) ^ p ≤ (2 * ((c₄ : ℝ≥0∞) * 2 ^ j)) ^ p := by gcongr
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) := by rw [← mul_assoc, mul_pow, ← pow_mul]
  refine ⟨?_, ?_⟩
  · intro C A p q a hpq ha0 ha
    -- Step 1: the first term
    have h0 : (2 * (Λ 0 : ℝ≥0∞)) ^ p * a 0 ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A := by
      calc (2 * (Λ 0 : ℝ≥0∞)) ^ p * a 0 ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (0 * p) * A :=
            mul_le_mul' (hw p 0) ha0
        _ = (2 * (c₄ : ℝ≥0∞)) ^ p * A := by simp
    -- Step 2: the later terms, `(2Λ_{j+1})^p a_{j+1} ≤ (2c₄)^p C A ι^{j+2}`
    have hs : ∀ j, (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1) ≤
        (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) := by
      intro j
      have he : (j + 1) * p + (j + 2) ≤ (j + 2) * (q + 1) := by
        nlinarith [Nat.mul_le_mul_left (j + 2) hpq]
      calc (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1)
          ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ ((j + 1) * p) *
              (C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (q + 1))) * A) :=
            mul_le_mul' (hw p (j + 1)) (ha j)
        _ = (2 * (c₄ : ℝ≥0∞)) ^ p * C * A *
              ((2 : ℝ≥0∞) ^ ((j + 1) * p) * (2⁻¹ : ℝ≥0∞) ^ ((j + 2) * (q + 1))) := by
            rw [hhalf]; ring
        _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) :=
            mul_le_mul' le_rfl (hshift _ _ _ he)
    -- Step 3: `Σ_j ι^{j+2} ≤ Σ_j ι^{j+1} = ι (1 - ι)⁻¹ = 1`, and summation
    have hgeom : ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2) ≤ 1 := by
      calc ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2) ≤ ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 1) :=
            ENNReal.tsum_le_tsum fun j => pow_le_pow_right_of_le_one' hι1 (Nat.le_succ _)
        _ = 1 := by
            rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
            exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
    calc ∑' j, (2 * (Λ j : ℝ≥0∞)) ^ p * a j
        = (2 * (Λ 0 : ℝ≥0∞)) ^ p * a 0 + ∑' j, (2 * (Λ (j + 1) : ℝ≥0∞)) ^ p * a (j + 1) :=
          tsum_eq_zero_add' ENNReal.summable
      _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A +
            ∑' j : ℕ, (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * (2⁻¹ : ℝ≥0∞) ^ (j + 2) :=
          add_le_add h0 (ENNReal.tsum_le_tsum hs)
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * A +
            (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ (j + 2) := by
          rw [ENNReal.tsum_mul_left]
      _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * A + (2 * (c₄ : ℝ≥0∞)) ^ p * C * A * 1 := by gcongr
      _ = (2 * (c₄ : ℝ≥0∞)) ^ p * (1 + C) * A := by ring
  · intro K A p z hK hA hz
    -- Step 4: `(2Λ_j)^p z_j ≤ κ ι^j` with `κ = (2c₄)^p K A < ∞`, and `κ ι^j → 0`
    have hκ : (2 * (c₄ : ℝ≥0∞)) ^ p * K * A ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)) hK) hA
    have hb : ∀ j, (2 * (Λ j : ℝ≥0∞)) ^ p * z j ≤
        (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j := by
      intro j
      have he : j * p + j ≤ (j + 2) * (p + 1) := by nlinarith
      calc (2 * (Λ j : ℝ≥0∞)) ^ p * z j
          ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * 2 ^ (j * p) *
              (K * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (p + 1))) * A) :=
            mul_le_mul' (hw p j) (hz j)
        _ = (2 * (c₄ : ℝ≥0∞)) ^ p * K * A *
              ((2 : ℝ≥0∞) ^ (j * p) * (2⁻¹ : ℝ≥0∞) ^ ((j + 2) * (p + 1))) := by
            rw [hhalf]; ring
        _ ≤ (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j :=
            mul_le_mul' le_rfl (hshift _ _ _ he)
    have hlim : Tendsto (fun j : ℕ => (2 * (c₄ : ℝ≥0∞)) ^ p * K * A * (2⁻¹ : ℝ≥0∞) ^ j)
        atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ENNReal.one_half_lt_one)
        (Or.inr hκ)
      rwa [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hb

/-- **Dyadic shell decomposition** of an integer multiplicity current around the dual skeleton
(Simon Ch. 6, proof of 5.1, displays (8)–(10) and the shells of E3).  For `T ∈ 𝒟_{m+1}(ℝᴾ)`
integer multiplicity with compact support and `M(T), M(∂T) < ∞`, a `1`-Lipschitz `d` and the
density bounds `M_{d<r}(T) ≤ C r^{m+2} M(T)`, `M_{d<r}(∂T) ≤ C r^{m+2} M(∂T)` (`0 < r ≤ 1/4`):
slice `T` by `d` (`A_t = T⌞{d < t}`, `B_t = (∂T)⌞{d < t}`), choose good radii
`r_j ∈ ((1/2)^{j+3}, (1/2)^{j+2})`, and put `W_0 = T − A_{r_0}`, `W_{j+1} = A_{r_j} − A_{r_{j+1}}`,
`D_j` likewise from `∂T` and `B`, `Z_j = ∂A_{r_j} − B_{r_j}`.  Then `Σ_j W_j = T`,
`∂W_0 = D_0 − Z_0`, `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`, the `W_j` are integer multiplicity, and
the supports and masses are controlled shell by shell. -/
theorem Submission.cmcsd_shell_decomposition : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ((∀ (P n : ℕ) (U M M' : Set (Euclid P)), IsOpen U → MeasurableSet M → MeasurableSet M' → M ⊆ M' → M' ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (M' ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict M), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (E : Set (Euclid P)), IsOpen U → MeasurableSet E → ∃ (A : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents A ∧ R'.carrier = R.carrier ∩ E ∧ R'.mult = R.mult ∧ R'.orient = R.orient) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (A B : GeometricCurrentOn U n), IsOpen U → IsIntegerMultiplicity A → IsIntegerMultiplicity B → IsIntegerMultiplicity (A - B)) ∧ (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α)) → (∀ (P k : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U (k + 1)) (μ μ' : Measure (Euclid P)) (ξ : Euclid P → MultiVector P (k + 1)) (ξ' : Euclid P → MultiVector P k) (f : Euclid P → ℝ) (L : NNReal), IsOpen U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ' K < ∞) → AEStronglyMeasurable ξ μ → AEStronglyMeasurable ξ' μ' → (∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) (k + 1), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ᵐ x ∂μ', ∀ α : Covector (Euclid P) k, |ξ' x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U (k + 1), T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) → (∀ η : TestFormOn U k, T.boundary η = ∫ x, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') → LipschitzWith L f → ∃ (A : ℝ → GeometricCurrentOn U (k + 1)) (B : ℝ → GeometricCurrentOn U k), (∀ (t : ℝ) (ω : TestFormOn U (k + 1)), A t ω = ∫ x in {x | f x < t}, ξ x ((ω : DifferentialForm (Euclid P) (k + 1)) x) ∂μ) ∧ (∀ (t : ℝ) (η : TestFormOn U k), B t η = ∫ x in {x | f x < t}, ξ' x ((η : DifferentialForm (Euclid P) k) x) ∂μ') ∧ (∀ (t : ℝ) (η : TestFormOn U k), Disjoint (tsupport (η : DifferentialForm (Euclid P) k)) {x | f x = t} → (A t).boundary η = B t η) ∧ (∀ (W : Set (Euclid P)) (t : ℝ), IsOpen W → ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * liminf (fun h : ℝ => ENNReal.ofReal h⁻¹ * μ (W ∩ {x | t - h < f x ∧ f x < t})) (𝓝[>] 0)) ∧ (∀ (W : Set (Euclid P)) (a b : ℝ), IsOpen W → ∫⁻ t in Ioo a b, ((A t).boundary - B t).massOn W ≤ (L : ℝ≥0∞) * μ (W ∩ {x | a < f x ∧ f x < b}))) → ∀ (P m : ℕ) (T : GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (d : Euclid P → ℝ) (C : NNReal), IsIntegerMultiplicity T → IsCompact T.support → T.mass < ∞ → T.boundary.mass < ∞ → LipschitzWith 1 d → (∀ r : ℝ, 0 < r → r ≤ 1 / 4 → T.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.mass ∧ T.boundary.massOn {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.boundary.mass) → ∃ (r : ℕ → ℝ) (W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1)) (D Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ j, (1 / 2 : ℝ) ^ (j + 3) < r j ∧ r j < (1 / 2 : ℝ) ^ (j + 2)) ∧ (∀ ω : TestFormOn (univ : Set (Euclid P)) (m + 1), HasSum (fun j => W j ω) (T ω)) ∧ (W 0).boundary = D 0 - Z 0 ∧ (∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j)) ∧ (∀ j, IsIntegerMultiplicity (W j)) ∧ (∀ j, IsCompact (W j).support ∧ (W j).mass < ∞ ∧ (W j).boundary.mass < ∞) ∧ (∀ j, IsCompact (D j).support ∧ (D j).mass < ∞ ∧ boundaryMassOn (D j) univ < ∞) ∧ (∀ j, IsCompact (Z j).support ∧ (Z j).mass < ∞ ∧ boundaryMassOn (Z j) univ < ∞) ∧ (∀ j, (W j).support ⊆ T.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (D j).support ⊆ T.boundary.support ∩ {x | r j ≤ d x}) ∧ (∀ j, (Z j).support ⊆ T.support ∩ {x | d x = r j}) ∧ (W 0).mass ≤ T.mass ∧ (∀ j, (W (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.mass) ∧ (D 0).mass ≤ T.boundary.mass ∧ (∀ j, (D (j + 1)).mass ≤ C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 2))) * T.boundary.mass) ∧ (∀ j, (Z j).mass ≤ 4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * T.mass) := by
  intro hVO hMR hREP hIMC hSL P m T d C hTim hTspt hTmass hbTmass hd hdens
  have hsub : ∀ {k : ℕ} (X Y : GeometricCurrentOn (univ : Set (Euclid P)) k)
      (ω : TestFormOn (univ : Set (Euclid P)) k), (X - Y) ω = X ω - Y ω := fun _ _ _ => rfl
  have hS := Submission.cmcsd_support_calculus
  have hMS := Submission.cmc_fc_cs_massOn_sub_le
  -- Step 1: the mass measure `μ_T` of `T`, with integrality of its Borel restrictions
  obtain ⟨μ, ξ, hμfin, hξm, hξb, hTrep, hTmassOn, hTnull, hIMrestr⟩ :=
    Submission.cmcsd_sh_im_mass_measure hVO hMR hIMC P (m + 1) T hTim hTmass
  -- Step 2: a finite measure `μ_∂` representing `∂T`, carried by `spt ∂T`
  obtain ⟨μ', ξ', hμ'fin, hξ'm, hξ'b, hbrep, hbmassOn, hbnull⟩ :=
    Submission.cmcsd_sh_finite_mass_measure hVO hREP P m T.boundary hbTmass
  have hdc : Continuous d := hd.continuous
  have hdm : Measurable d := hdc.measurable
  -- Step 4: slice `T` by `d`: `A_t = T⌞{d < t}`, `B_t = (∂T)⌞{d < t}`
  obtain ⟨A, B, hA, hB, hAB, hZmass, -⟩ := hSL P m univ T μ μ' ξ ξ' d 1 isOpen_univ
    (fun K _ _ => measure_lt_top μ K) (fun K _ _ => measure_lt_top μ' K) hξm hξ'm hξb hξ'b
    hTrep hbrep hd
  -- Step 5: good radii `r_j ∈ ((1/2)^{j+3}, (1/2)^{j+2})`; `{d < r}` is open, so the density
  -- bounds for `M_{d<r}(T)`, `M_{d<r}(∂T)` are bounds for `μ_T{d < r}`, `μ_∂{d < r}`
  have hdens' : ∀ r : ℝ, 0 < r → r ≤ 1 / 4 →
      μ {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.mass ∧
        μ' {x | d x < r} ≤ C * ENNReal.ofReal (r ^ (m + 2)) * T.boundary.mass := by
    intro r hr hr'
    have hopen : IsOpen {x | d x < r} := isOpen_lt hdc continuous_const
    rw [← hTmassOn _ hopen, ← hbmassOn _ hopen]
    exact hdens r hr hr'
  obtain ⟨r, hrb, hranti, hrμ, hrtend, hrtend', hrlim, hrlim'⟩ :=
    Submission.cmcsd_sh_dyadic_good_radii Submission.cmcsd_good_radius P m μ μ' d C T.mass
      T.boundary.mass hμfin hμ'fin hdm hTmass.ne hbTmass.ne hdens'
  -- Step 6: `W_0 = T − A_{r_0}`, `W_{j+1} = A_{r_j} − A_{r_{j+1}}`, `D_j` likewise from `∂T` and
  -- `B`, and `Z_j = ∂A_{r_j} − B_{r_j}`
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) (m + 1),
      W 0 = T - A (r 0) ∧ ∀ j, W (j + 1) = A (r j) - A (r (j + 1)) :=
    ⟨fun j => match j with
      | 0 => T - A (r 0)
      | j + 1 => A (r j) - A (r (j + 1)), rfl, fun _ => rfl⟩
  obtain ⟨D, hD0, hDs⟩ : ∃ D : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m,
      D 0 = T.boundary - B (r 0) ∧ ∀ j, D (j + 1) = B (r j) - B (r (j + 1)) :=
    ⟨fun j => match j with
      | 0 => T.boundary - B (r 0)
      | j + 1 => B (r j) - B (r (j + 1)), rfl, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ → GeometricCurrentOn (univ : Set (Euclid P)) m,
      ∀ j, Z j = (A (r j)).boundary - B (r j) := ⟨_, fun _ => rfl⟩
  -- Steps 7, 10a/b, 11a/b, 13: the shells of `T` and of `∂T` (shell series, applied twice)
  obtain ⟨hW0int, hWsint, hWsum, hWspt, hAspt, hW0m, hWsm⟩ :=
    Submission.cmcsd_sh_shell_series hS Submission.cmcsd_massOn_le_measure_inter P (m + 1) T
      (fun j => A (r j)) W μ ξ d r hμfin hξm hξb hTnull hdc hranti hrtend hTrep
      (fun j ω => hA (r j) ω) (fun ω => by rw [hW0]; rfl) (fun j ω => by rw [hWs]; rfl)
  obtain ⟨-, -, -, hDspt, hBspt, hD0m, hDsm⟩ :=
    Submission.cmcsd_sh_shell_series hS Submission.cmcsd_massOn_le_measure_inter P m T.boundary
      (fun j => B (r j)) D μ' ξ' d r hμ'fin hξ'm hξ'b hbnull hdc hranti hrtend' hbrep
      (fun j ω => hB (r j) ω) (fun ω => by rw [hD0]; rfl) (fun j ω => by rw [hDs]; rfl)
  -- Step 9: `∂W_0 = D_0 − Z_0` and `∂W_{j+1} = D_{j+1} − (Z_{j+1} − Z_j)`, value by value
  have hbd0 : (W 0).boundary = D 0 - Z 0 := by
    rw [hW0, hD0, hZ]
    ext η
    simp only [hsub, GeometricCurrentOn.boundary_apply]
    ring
  have hbds : ∀ j, (W (j + 1)).boundary = D (j + 1) - (Z (j + 1) - Z j) := by
    intro j
    rw [hWs, hDs, hZ, hZ]
    ext η
    simp only [hsub, GeometricCurrentOn.boundary_apply]
    ring
  -- Step 11: masses; `M(Z_j) ≤ liminf_{h↓0} h⁻¹ μ_T{r_j − h < d < r_j}` by the slicing estimate
  have hTmu : μ univ = T.mass := (hTmassOn univ isOpen_univ).symm
  have hbmu : μ' univ = T.boundary.mass := (hbmassOn univ isOpen_univ).symm
  have hfin : ∀ (K : ℝ) (M : ℝ≥0∞), M < ∞ → (C : ℝ≥0∞) * ENNReal.ofReal K * M < ∞ :=
    fun K M hM => ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top) hM
  have hZb : ∀ j, (Z j).mass ≤
      4 * C * ENNReal.ofReal ((1 / 2 : ℝ) ^ ((j + 2) * (m + 1))) * T.mass := by
    intro j
    rw [hZ]
    have h := hZmass univ (r j) isOpen_univ
    simp only [univ_inter, ENNReal.coe_one, one_mul] at h
    exact h.trans (hrlim j)
  have hZfin : ∀ j, (Z j).mass < ∞ := fun j =>
    (hZb j).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      ENNReal.ofNat_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top) hTmass)
  have hWfin : ∀ j, (W j).mass < ∞ := by
    intro j
    cases j with
    | zero => exact hW0m.trans_lt (hTmu ▸ hTmass)
    | succ j => exact (hWsm j).trans_lt ((hrμ j).1.trans_lt (hfin _ _ hTmass))
  have hDfin : ∀ j, (D j).mass < ∞ := by
    intro j
    cases j with
    | zero => exact hD0m.trans_lt (hbmu ▸ hbTmass)
    | succ j => exact (hDsm j).trans_lt ((hrμ j).2.trans_lt (hfin _ _ hbTmass))
  -- Step 12a: `M(∂W_j) < ∞` from the boundary relations and `M(X − Y) ≤ M(X) + M(Y)`
  have hWbfin : ∀ j, (W j).boundary.mass < ∞ := by
    intro j
    cases j with
    | zero =>
      rw [hbd0]
      exact (hMS P m univ univ (D 0) (Z 0)).trans_lt (ENNReal.add_lt_top.2 ⟨hDfin 0, hZfin 0⟩)
    | succ j =>
      rw [hbds j]
      refine (hMS P m univ univ (D (j + 1)) (Z (j + 1) - Z j)).trans_lt
        (ENNReal.add_lt_top.2 ⟨hDfin (j + 1), ?_⟩)
      exact (hMS P m univ univ (Z (j + 1)) (Z j)).trans_lt
        (ENNReal.add_lt_top.2 ⟨hZfin (j + 1), hZfin j⟩)
  -- Step 12b: `M(∂B_{r_j}) < ∞` (second slicing, of `∂T`), and `∂∂ = 0`
  have hBbd : ∀ j, boundaryMassOn (B (r j)) univ < ∞ := by
    intro j
    have h := Submission.cmcsd_sh_slice_boundaryMassOn_le hSL P m univ T μ' ξ' d 1 (r j)
      (B (r j)) univ isOpen_univ isOpen_univ (fun K _ _ => measure_lt_top μ' K) hξ'm hξ'b hbrep
      hd (hB (r j))
    simp only [univ_inter, ENNReal.coe_one, one_mul] at h
    exact h.trans_lt (hrlim' j)
  have hcalc := Submission.cmcsd_sh_boundaryMassOn_calculus P m univ univ
  have hDbfin : ∀ j, boundaryMassOn (D j) univ < ∞ := by
    intro j
    cases j with
    | zero =>
      rw [hD0]
      refine (hcalc.1 _ _).trans_lt ?_
      rw [hcalc.2 T, zero_add]
      exact hBbd 0
    | succ j =>
      rw [hDs j]
      exact (hcalc.1 _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hBbd j, hBbd (j + 1)⟩)
  have hZbfin : ∀ j, boundaryMassOn (Z j) univ < ∞ := by
    intro j
    rw [hZ j]
    refine (hcalc.1 _ _).trans_lt ?_
    rw [hcalc.2 (A (r j)), zero_add]
    exact hBbd j
  -- Step 10c: `spt Z_j ⊆ spt T` (supports of `A_{r_j}`, `B_{r_j}`) and `spt Z_j ⊆ {d = r_j}`
  -- (`∂A_{r_j} = B_{r_j}` off `{d = r_j}`)
  have hbT : T.boundary.support ⊆ T.support := (hS P m).2.2.2.2 T
  have hZspt : ∀ j, (Z j).support ⊆ T.support ∩ {x | d x = r j} := by
    intro j
    rw [hZ j]
    apply subset_inter
    · refine ((hS P m).2.2.1 _ _).trans (union_subset ?_ ?_)
      · exact ((hS P m).2.2.2.2 (A (r j))).trans (hAspt j)
      · exact (hBspt j).trans hbT
    · refine (hS P m).1 _ _ (isClosed_eq hdc continuous_const) (fun η hη => ?_)
      rw [hsub, hAB (r j) η hη, sub_self]
  -- Step 10d: closed subsets of the compact `spt T` are compact
  have hcpt : ∀ {k : ℕ} (X : GeometricCurrentOn (univ : Set (Euclid P)) k),
      X.support ⊆ T.support → IsCompact X.support :=
    fun X h => hTspt.of_isClosed_subset ((hS P _).2.1 X) h
  -- Step 14: conclusion
  refine ⟨r, W, D, Z, hrb, hWsum, hbd0, hbds, ?_,
    fun j => ⟨hcpt _ ((hWspt j).trans inter_subset_left), hWfin j, hWbfin j⟩,
    fun j => ⟨hcpt _ (((hDspt j).trans inter_subset_left).trans hbT), hDfin j, hDbfin j⟩,
    fun j => ⟨hcpt _ ((hZspt j).trans inter_subset_left), hZfin j, hZbfin j⟩,
    hWspt, hDspt, hZspt, hW0m.trans hTmu.le, fun j => (hWsm j).trans (hrμ j).1,
    hD0m.trans hbmu.le, fun j => (hDsm j).trans (hrμ j).2, hZb⟩
  -- Step 8: the shells `W_j = T⌞E_j` over Borel `E_j` are integer multiplicity
  intro j
  cases j with
  | zero => exact hIMrestr _ (W 0) (measurableSet_le measurable_const hdm) hW0int
  | succ j =>
    exact hIMrestr _ (W (j + 1))
      ((measurableSet_le measurable_const hdm).inter (measurableSet_lt hdm measurable_const))
      (hWsint j)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
