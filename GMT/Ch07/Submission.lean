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

/-- **Radial mollifier** (step 0 of the Weyl lemma used in Simon Ch. 5, proof of Lemma 3.1; cf. the
standard mollifier of Evans, *PDE*, App. C.5).  With `θ = Real.smoothTransition`,
`k(y) = θ(1 − ‖y‖²)` is continuous, nonnegative, vanishes off `B̄₁(0)` and has `k(0) = 1`, so
`c = ∫ k > 0`.  Then `C = c⁻¹` and `g ε t = θ(1 − t/ε²)/(c εⁿ)` work: `g ε` is continuous, vanishes
for `t ≥ ε²`, satisfies `0 ≤ g ε t ≤ C/εⁿ`, `y ↦ g ε (‖y‖²)` is `C^∞`, and the substitution
`y = εu` gives `∫ θ(1 − ‖y‖²/ε²) dy = εⁿ c`, so `∫ g ε (‖y‖²) dy = 1`. -/
theorem Submission.dorag_ha_weyl_radial_mollifier : ∀ n : ℕ, 0 < n → ∃ C : ℝ, ∃ g : ℝ → ℝ → ℝ, ∀ ε : ℝ, 0 < ε → Continuous (g ε) ∧ (∀ t : ℝ, ε ^ 2 ≤ t → g ε t = 0) ∧ (∀ t : ℝ, |g ε t| ≤ C / ε ^ n) ∧ (∀ m : ℕ, ContDiff ℝ m (fun y : Euclid n => g ε (‖y‖ ^ 2))) ∧ ∫ y : Euclid n, g ε (‖y‖ ^ 2) = 1 := by
  intro n _hn
  -- the unscaled bump `k y = θ (1 - ‖y‖²)`, `θ = Real.smoothTransition`
  obtain ⟨k, hk⟩ : ∃ k : Euclid n → ℝ, ∀ y, k y = Real.smoothTransition (1 - ‖y‖ ^ 2) :=
    ⟨_, fun _ => rfl⟩
  have hk_cont : Continuous k := by
    rw [show k = fun y => Real.smoothTransition (1 - ‖y‖ ^ 2) from funext hk]
    exact Real.smoothTransition.continuous.comp (continuous_const.sub (continuous_norm.pow 2))
  have hk_supp : HasCompactSupport k := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) 1) fun y hy => ?_
    have h1 : 1 < ‖y‖ := by simpa using hy
    rw [hk]
    exact Real.smoothTransition.zero_of_nonpos (by nlinarith)
  have hk_nonneg : 0 ≤ k := fun y => by rw [hk]; exact Real.smoothTransition.nonneg _
  have hk0 : k 0 ≠ 0 := by rw [hk]; simp
  have hcpos : 0 < ∫ y, k y :=
    hk_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hk_supp hk_nonneg hk0
  -- change of variables `y = ε u`
  have hscale : ∀ ε : ℝ, 0 < ε →
      ∫ y : Euclid n, Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) = ε ^ n * ∫ y, k y := by
    intro ε hε
    have h := Measure.integral_comp_inv_smul_of_nonneg volume k hε.le
    rw [finrank_euclideanSpace_fin, smul_eq_mul] at h
    rw [← h]
    congr 1
    ext y
    rw [hk, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, mul_pow, inv_pow, inv_mul_eq_div]
  generalize ∫ y, k y = c at hcpos hscale
  refine ⟨c⁻¹, fun ε t => Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n), fun ε hε => ?_⟩
  have hεn : 0 < ε ^ n := pow_pos hε n
  have hden : 0 < c * ε ^ n := mul_pos hcpos hεn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) continuity
    exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub (continuous_id.div_const _))).div_const _
  · -- (b) vanishing for `t ≥ ε²`
    intro t ht
    have h1 : 1 ≤ t / ε ^ 2 := (one_le_div (pow_pos hε 2)).mpr ht
    show Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n) = 0
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]
  · -- (c) sup bound
    intro t
    show |Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n)| ≤ c⁻¹ / ε ^ n
    rw [abs_of_nonneg (div_nonneg (Real.smoothTransition.nonneg _) hden.le)]
    calc Real.smoothTransition (1 - t / ε ^ 2) / (c * ε ^ n) ≤ 1 / (c * ε ^ n) :=
          div_le_div_of_nonneg_right (Real.smoothTransition.le_one _) hden.le
      _ = c⁻¹ / ε ^ n := by rw [one_div, mul_inv, div_eq_mul_inv]
  · -- (d) smoothness
    intro m
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y : Euclid n =>
        Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) / (c * ε ^ n) :=
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))).div_const _
    exact contDiff_infty.mp h m
  · -- (e) normalization
    show ∫ y : Euclid n, Real.smoothTransition (1 - ‖y‖ ^ 2 / ε ^ 2) / (c * ε ^ n) = 1
    rw [integral_div, hscale ε hε, mul_comm]
    exact div_self hden.ne'
namespace Submission

/-- Weyl's lemma, convolution step: for locally integrable `f` and `φ` smooth with compact
support, `F(x) = ∫ f(y) φ(x − y) dy` is `C^m` for every `m` and `ΔF(x) = ∫ f(y) Δφ(x − y) dy`,
`Δψ(z) = Σᵢ D²ψ(z)(eᵢ, eᵢ)` (Evans, PDE, App. C, Thm 7(i)).  `F = f ⋆[L] φ` for multiplication
`L`; differentiating under the integral twice gives `D(DF) = f ⋆ D²φ`, and evaluation at
`(v, w)` commutes with the integral (`convolution_precompR_apply`). -/
theorem dorag_ha_weyl_conv_laplacian : ∀ (n : ℕ) (f φ : Euclid n → ℝ), LocallyIntegrable f → (∀ m : ℕ, ContDiff ℝ m φ) → HasCompactSupport φ → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, f y * φ (x - y))) ∧ ∀ x : Euclid n, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, f y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = ∫ y, f y * ∑ i : Fin n, iteratedFDeriv ℝ 2 φ (x - y) ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n f φ hf hφ hφc
  -- `F = f ⋆[L] φ` for the multiplication bilinear map `L a b = a * b`.
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ with hL
  have hF : (fun x => ∫ y, f y * φ (x - y)) = convolution f φ L volume := by
    funext x
    rw [hL, convolution_mul]
  have hφ1 : ContDiff ℝ 1 φ := by exact_mod_cast hφ 1
  have hφ2 : ContDiff ℝ 2 φ := by exact_mod_cast hφ 2
  have hdφ : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right one_add_one_eq_two.le
  refine ⟨fun m => ?_, fun x => ?_⟩
  · rw [hF]
    exact hφc.contDiff_convolution_right L hf (hφ m)
  -- `DF = f ⋆[L.precompR] Dφ` and `D(DF)(x) v w = ∫ f(y) D²φ(x − y) v w dy`.
  have hD : fderiv ℝ (convolution f φ L volume) =
      convolution f (fderiv ℝ φ) (L.precompR (Euclid n)) volume := by
    ext1 x₀
    exact (hφc.hasFDerivAt_convolution_right L hf hφ1 x₀).fderiv
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := hdφ.continuous_fderiv one_ne_zero
  have hs2 : HasCompactSupport (fderiv ℝ (fderiv ℝ φ)) := (hφc.fderiv ℝ).fderiv ℝ
  have hD2 : ∀ v w : Euclid n, fderiv ℝ (fderiv ℝ (convolution f φ L volume)) x v w =
      ∫ y, f y * fderiv ℝ (fderiv ℝ φ) (x - y) v w := by
    intro v w
    have hc3 : Continuous fun a => fderiv ℝ (fderiv ℝ φ) a v := hc2.clm_apply continuous_const
    have hs3 : HasCompactSupport fun a => fderiv ℝ (fderiv ℝ φ) a v :=
      hs2.comp_left (g := fun A : Euclid n →L[ℝ] Euclid n →L[ℝ] ℝ => A v) rfl
    rw [hD, ((hφc.fderiv ℝ).hasFDerivAt_convolution_right (L.precompR (Euclid n)) hf hdφ x).fderiv,
      convolution_precompR_apply (L.precompR (Euclid n)) hf hs2 hc2 x v,
      convolution_precompR_apply L hf hs3 hc3 x w, hL, convolution_mul]
  -- Each integrand `f(y) D²φ(x − y) v w` is integrable, so the sum over `i` commutes with `∫`.
  have hint : ∀ v w : Euclid n, Integrable fun y => f y * fderiv ℝ (fderiv ℝ φ) (x - y) v w := by
    intro v w
    have hc4 : Continuous fun a => fderiv ℝ (fderiv ℝ φ) a v w :=
      (hc2.clm_apply continuous_const).clm_apply continuous_const
    have hs4 : HasCompactSupport fun a => fderiv ℝ (fderiv ℝ φ) a v w :=
      hs2.comp_left (g := fun A : Euclid n →L[ℝ] Euclid n →L[ℝ] ℝ => A v w) rfl
    exact hs4.convolutionExists_right L hf hc4 x
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hF]
  simp_rw [hD2, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint _ _]
/-- Weyl's lemma, mollification step: if `W ∈ L¹(B)`, `B = B_R(0)`, is weakly harmonic in `B`
and `φ` is smooth and vanishes for `‖y‖ ≥ ε`, then `F = (1_B W) ⋆ φ` is `C^m` for every `m` and
`ΔF = 0` on `B_{R−ε}(0)`.  By `dorag_ha_weyl_conv_laplacian`, `ΔF(x) = ∫ (1_B W)(y) Δφ(x − y) dy`;
for `‖x‖ < R − ε` the test function `ζ(y) = φ(x − y)` has `spt ζ ⊆ B̄_ε(x) ⊆ B` and
`Δζ(y) = Δφ(x − y)`, so this is `∫_B W Δζ = 0`. -/
theorem dorag_ha_weyl_mollify_harmonic : ∀ (n : ℕ) (R ε : ℝ) (W φ : Euclid n → ℝ), 0 < ε → IntegrableOn W (ball (0 : Euclid n) R) → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiff ℝ m φ) → (∀ y : Euclid n, ε ≤ ‖y‖ → φ y = 0) → (∀ m : ℕ, ContDiff ℝ m (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y))) ∧ ∀ x ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun x => ∫ y, (ball (0 : Euclid n) R).indicator W y * φ (x - y)) x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n R ε W φ hε hW hharm hφ hφ0
  -- `1_B W` is integrable, and `φ` vanishes off the compact ball `B̄_ε(0)`.
  have hWB : Integrable ((ball (0 : Euclid n) R).indicator W) :=
    hW.integrable_indicator measurableSet_ball
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) ε) fun y hy =>
      hφ0 y (by rw [mem_closedBall, dist_zero_right, not_le] at hy; exact hy.le)
  obtain ⟨hsmooth, hlap⟩ := Submission.dorag_ha_weyl_conv_laplacian n
    ((ball (0 : Euclid n) R).indicator W) φ hWB.locallyIntegrable hφ hφc
  refine ⟨hsmooth, fun x hx => ?_⟩
  rw [hlap x]
  -- The test function `ζ(y) = φ(x − y)`, supported in `B̄_ε(x) ⊆ B`.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Euclid n → ℝ, ζ = fun y => φ (x - y) := ⟨_, rfl⟩
  have hζ2 : ContDiff ℝ 2 ζ := by
    rw [hζ]
    exact (hφ 2).comp (contDiff_const.sub contDiff_id)
  have hζspt : tsupport ζ ⊆ closedBall x ε := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_comm, dist_eq_norm]
    by_contra h
    exact hy (by rw [hζ]; exact hφ0 _ (not_le.1 h).le)
  have hball : closedBall x ε ⊆ ball (0 : Euclid n) R := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball] at hx ⊢
    linarith [dist_triangle y x 0]
  -- `D²ζ(y)(v, v) = D²φ(x − y)(v, v)`: write `ζ = φ(x + ·) ∘ (−id)`.
  have hD2 : ∀ y v : Euclid n,
      iteratedFDeriv ℝ 2 ζ y ![v, v] = iteratedFDeriv ℝ 2 φ (x - y) ![v, v] := by
    intro y v
    have hψ : ContDiff ℝ (2 : ℕ) fun z => φ (x + z) :=
      (hφ 2).comp (contDiff_const.add contDiff_id)
    have hζψ : ζ = (fun z => φ (x + z)) ∘ ⇑(-ContinuousLinearMap.id ℝ (Euclid n)) := by
      rw [hζ]
      funext z
      simp [sub_eq_add_neg]
    rw [hζψ, ContinuousLinearMap.iteratedFDeriv_comp_right _ hψ y le_rfl,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_comp_add_left,
      iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp [sub_eq_add_neg]
  -- `∫ 1_B W Δφ(x − ·) = ∫_B W Δζ = 0` by weak harmonicity.
  have hζW := hharm ζ hζ2
    ((isCompact_closedBall x ε).of_isClosed_subset (isClosed_tsupport ζ) hζspt) (hζspt.trans hball)
  rw [← integral_indicator measurableSet_ball] at hζW
  simpa only [Set.indicator_mul_left, hD2] using hζW

end Submission
/-- **Fubini symmetry of iterated convolutions** (step 4 of the proof of Weyl's lemma, which gives
"Thus w is harmonic in B" in the proof of Simon Ch. 5, Lemma 3.1): for `f ∈ L¹(ℝⁿ)` and continuous
compactly supported kernels `φ, ψ`, `((f ⋆ φ) ⋆ ψ)(x) = ((f ⋆ ψ) ⋆ φ)(x)`.  For continuous
compactly supported `a, b` the kernel `f(y) a(x − z − y) b(z)` is integrable on `ℝⁿ × ℝⁿ`
(dominated by `sup |a| · |b(z)| · |f(y)|`), so Fubini and the substitution `z ↦ (x − y) − z` give
`∫_z (∫_y f(y) a(x − z − y)) b(z) = ∫_y f(y) ∫_z a(z) b(x − y − z)`; the inner kernel integrals
for `(a, b) = (φ, ψ)` and `(ψ, φ)` agree by the same substitution. -/
theorem Submission.dorag_ha_weyl_conv_swap : ∀ (n : ℕ) (f φ ψ : Euclid n → ℝ) (x : Euclid n), Integrable f → Continuous φ → HasCompactSupport φ → Continuous ψ → HasCompactSupport ψ → ∫ z, (∫ y, f y * φ (x - z - y)) * ψ z = ∫ z, (∫ y, f y * ψ (x - z - y)) * φ z := by
  intro n f φ ψ x hf hφ hφs hψ hψs
  -- reflection invariance: `∫ a(w − z) b(z) dz = ∫ a(z) b(w − z) dz`, via `z ↦ w − z`
  have refl : ∀ (a b : Euclid n → ℝ) (w : Euclid n),
      ∫ z, a (w - z) * b z = ∫ z, a z * b (w - z) := by
    intro a b w
    rw [← integral_sub_left_eq_self (fun z => a z * b (w - z)) volume w]
    simp only [sub_sub_cancel]
  -- (★): for continuous compactly supported `a, b`,
  -- `∫_z (∫_y f(y) a(x − z − y)) b(z) = ∫_y f(y) ∫_z a(z) b(x − y − z)`
  have gen : ∀ a b : Euclid n → ℝ, Continuous a → HasCompactSupport a → Continuous b →
      HasCompactSupport b →
      ∫ z, (∫ y, f y * a (x - z - y)) * b z = ∫ y, f y * ∫ z, a z * b (x - y - z) := by
    intro a b ha has hb hbs
    obtain ⟨M, hM⟩ := has.exists_bound_of_continuous ha
    have hbi : Integrable b := hb.integrable_of_hasCompactSupport hbs
    -- `K(z, y) = f(y) a(x − z − y) b(z)` is integrable on `ℝⁿ × ℝⁿ`, being a.e.-strongly
    -- measurable and dominated by `M |b(z)| |f(y)|`
    have hK : Integrable (uncurry fun z y => f y * a (x - z - y) * b z)
        (volume.prod (volume : Measure (Euclid n))) := by
      refine ((hbi.norm.mul_prod hf.norm).const_mul M).mono' ?_ (Eventually.of_forall fun p => ?_)
      · have ha' : Continuous fun p : Euclid n × Euclid n => a (x - p.1 - p.2) := by fun_prop
        have hb' : Continuous fun p : Euclid n × Euclid n => b p.1 := by fun_prop
        exact (hf.aestronglyMeasurable.comp_snd.mul ha'.aestronglyMeasurable).mul
          hb'.aestronglyMeasurable
      · simp only [uncurry, norm_mul]
        calc ‖f p.2‖ * ‖a (x - p.1 - p.2)‖ * ‖b p.1‖ ≤ ‖f p.2‖ * M * ‖b p.1‖ := by
              gcongr
              exact hM _
          _ = M * (‖b p.1‖ * ‖f p.2‖) := by ring
    calc ∫ z, (∫ y, f y * a (x - z - y)) * b z
        = ∫ z, ∫ y, f y * a (x - z - y) * b z := by
          simp only [integral_mul_const]
      _ = ∫ y, ∫ z, f y * a (x - z - y) * b z := integral_integral_swap hK
      _ = ∫ y, f y * ∫ z, a z * b (x - y - z) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only [sub_right_comm x _ y, mul_assoc, integral_const_mul, refl a b (x - y)]
  rw [gen φ ψ hφ hφs hψ hψs, gen ψ φ hψ hψs hφ hφs]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [← refl ψ φ (x - y), mul_comm]
/-- Patching step of Weyl's lemma (step 5 of its proof).  If each `F ε` is smooth and harmonic on
`B_{R-ε}(0)` and `F ε x = F δ x` whenever `‖x‖ + ε + δ < R`, then `h(x) = F ((R - ‖x‖) / 3) x` is
smooth and harmonic on `B_R(0)`, and `F ε x = h x` for all small `ε > 0`.  The point is that on
`B_r(0)`, `r < R`, `h` coincides with the single function `F ((R - r) / 3)`. -/
theorem Submission.dorag_ha_weyl_glue : ∀ (n : ℕ) (R : ℝ) (F : ℝ → Euclid n → ℝ), 0 < R → (∀ ε : ℝ, 0 < ε → ε < R → ∀ m : ℕ, ContDiffOn ℝ m (F ε) (ball (0 : Euclid n) (R - ε))) → (∀ ε : ℝ, 0 < ε → ε < R → ∀ y ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (F ε) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ (ε δ : ℝ) (x : Euclid n), 0 < ε → 0 < δ → ‖x‖ + ε + δ < R → F ε x = F δ x) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) ∧ (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ ∀ x ∈ ball (0 : Euclid n) R, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F ε x = h x := by
  intro n R F hR hsmooth hharm hcons
  -- Step 2: for `r < R`, `F ((R - r) / 3) = h` on `B_r(0)`, by (iii) with `ε = (R - r) / 3` and
  -- `δ = (R - ‖x‖) / 3`, as `‖x‖ + ε + δ < (2R + r) / 3 < R`
  have key : ∀ r : ℝ, r < R → ∀ x : Euclid n, ‖x‖ < r →
      F ((R - r) / 3) x = F ((R - ‖x‖) / 3) x := fun r hr x hx =>
    hcons ((R - r) / 3) ((R - ‖x‖) / 3) x (by linarith) (by linarith) (by linarith)
  -- each `x ∈ B_R(0)` lies in a smaller ball `B_r(0)`, `r < R` (take `r = (‖x‖ + R) / 2`)
  have mid : ∀ x ∈ ball (0 : Euclid n) R, ∃ r, ‖x‖ < r ∧ r < R := fun x hx =>
    ⟨(‖x‖ + R) / 2, by linarith [mem_ball_zero_iff.1 hx], by linarith [mem_ball_zero_iff.1 hx]⟩
  refine ⟨fun x => F ((R - ‖x‖) / 3) x, fun m => ?_, fun y hy => ?_, fun x hx => ?_⟩
  · -- Step 3: on `B_R(0) ∩ B_r(0)`, `h` is the `C^m` function `F ((R - r) / 3)`, as
    -- `B_r(0) ⊆ B_{R - (R - r) / 3}(0)`; `C^m` is a local property
    refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
    obtain ⟨r, hxr, hrR⟩ := mid x hx
    refine ⟨ball 0 r, isOpen_ball, mem_ball_zero_iff.2 hxr, ?_⟩
    have hF : ContDiffOn ℝ m (F ((R - r) / 3)) (ball 0 R ∩ ball 0 r) :=
      (hsmooth ((R - r) / 3) (by linarith) (by linarith [norm_nonneg x]) m).mono fun z hz =>
        mem_ball_zero_iff.2 (by linarith [mem_ball_zero_iff.1 hz.2])
    exact hF.congr fun z hz => (key r hrR z (mem_ball_zero_iff.1 hz.2)).symm
  · -- Step 4: `h = F ((R - r) / 3)` near `y`, so both have the same second derivative at `y`,
    -- and (ii) applies to `F ((R - r) / 3)` at `y ∈ B_r(0) ⊆ B_{R - (R - r) / 3}(0)`
    obtain ⟨r, hyr, hrR⟩ := mid y hy
    have heq : (fun x => F ((R - ‖x‖) / 3) x) =ᶠ[𝓝 y] F ((R - r) / 3) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hyr)] with z hz
      exact (key r hrR z (mem_ball_zero_iff.1 hz)).symm
    rw [(heq.iteratedFDeriv ℝ 2).eq_of_nhds]
    exact hharm ((R - r) / 3) (by linarith) (by linarith [norm_nonneg y]) y
      (mem_ball_zero_iff.2 (by linarith))
  · -- Step 5: for `0 < ε < 2 (R - ‖x‖) / 3`, (iii) with `δ = (R - ‖x‖) / 3` gives `F ε x = h x`
    have hxR := mem_ball_zero_iff.1 hx
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 * (R - ‖x‖) / 3 by linarith)] with ε hε
    exact hcons ε ((R - ‖x‖) / 3) x hε.1 (by linarith) (by linarith [hε.2])
/-- **Weyl's lemma, a.e. convergence of approximate identities** (Lebesgue differentiation; cf.
Evans, *PDE*, App. C, Thm. 7(ii)).  If `f ∈ L¹(ℝⁿ)` and for every `ε > 0` the kernel `φ ε` is
continuous, vanishes on `{|y| ≥ ε}`, satisfies `|φ ε| ≤ C ε⁻ⁿ` and has integral `1`, then
`∫ f(y) φ ε(x − y) dy → f(x)` as `ε → 0⁺` for `Lⁿ`-a.e. `x`.  At a Lebesgue point `x₀` the
kernels `y ↦ φ ε(x₀ − y)` have integral `1`, support in `B_ε(x₀)` and sup `≤ C c₁ / Lⁿ(B_ε(x₀))`,
`c₁ = Lⁿ(B₁(0))`, so `|∫ f φ ε(x₀ − ·) − f(x₀)| ≤ C c₁ ⨍_{B_ε(x₀)} |f − f(x₀)| → 0`. -/
theorem Submission.dorag_ha_weyl_ae_tendsto : ∀ (n : ℕ) (f : Euclid n → ℝ) (C : ℝ) (φ : ℝ → Euclid n → ℝ), 0 < n → Integrable f → (∀ ε : ℝ, 0 < ε → Continuous (φ ε)) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, ε ≤ ‖y‖ → φ ε y = 0) → (∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, |φ ε y| ≤ C / ε ^ n) → (∀ ε : ℝ, 0 < ε → ∫ y, φ ε y = 1) → ∀ᵐ x ∂(volume : Measure (Euclid n)), Tendsto (fun ε => ∫ y, f y * φ ε (x - y)) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  intro n f C φ _hn hf _hcont hsupp hbound hint
  -- Lebesgue differentiation: `⨍_{B_r(x₀)} |f - f x₀| → 0` as `r → 0⁺` for a.e. `x₀`
  filter_upwards [VitaliFamily.ae_tendsto_average_norm_sub
    (Besicovitch.vitaliFamily (volume : Measure (Euclid n))) hf.locallyIntegrable] with x₀ h₀
  -- `c₁ = Lⁿ(B₁(0)) > 0`, and `Lⁿ(B_ε(x₀)) = εⁿ c₁`
  have hc₁ : 0 < (volume : Measure (Euclid n)).real (closedBall 0 1) :=
    ENNReal.toReal_pos (measure_closedBall_pos _ _ one_pos).ne' measure_closedBall_lt_top.ne
  -- `y ↦ φ ε (x₀ - y)` has integral `1`, support in `B_ε(x₀)` and sup `≤ C c₁ / Lⁿ(B_ε(x₀))`
  have key : Tendsto (fun ε => ∫ y, φ ε (x₀ - y) • f y) (𝓝[>] (0 : ℝ)) (𝓝 (f x₀)) := by
    apply tendsto_integral_smul_of_tendsto_average_norm_sub
      (C * (volume : Measure (Euclid n)).real (closedBall 0 1))
      (h₀.comp (Besicovitch.tendsto_filterAt _ x₀))
    · exact Eventually.of_forall fun _ => hf.integrableOn
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      rw [integral_sub_left_eq_self (φ ε) volume x₀, hint ε hε]
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) y hy
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev]
      by_contra! h
      exact hy (hsupp ε hε _ h.le)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) y
      rw [Measure.addHaar_real_closedBall' _ x₀ hε.le, finrank_euclideanSpace_fin,
        mul_div_mul_right _ _ hc₁.ne']
      exact hbound ε hε (x₀ - y)
  refine key.congr fun ε => ?_
  simp_rw [smul_eq_mul, mul_comm]
/-- **Simon, Ch. 5, 3.3** ("applying this with `D_j u` in place of `u`"): a directional derivative
`u_e = Dh(·) e` of a smooth harmonic `h` on an open `U ⊆ ℝⁿ` is smooth and harmonic on `U`.  With
`G = D²h` and `H = D³h`: near `y ∈ U`, `Du_e(z) b = G z b e`, so `D²u_e(y)(a, b) = H y a b e`;
symmetry of `D²h` on `U` and of `D²(Dh)` at `y` give `H y eᵢ eᵢ e = H y e eᵢ eᵢ`, and
`∑ᵢ H y e eᵢ eᵢ` is the `e`-derivative at `y` of `z ↦ Δh(z)`, which vanishes near `y`. -/
theorem Submission.dorag_ha_ie_fderiv_apply_harmonic : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (e : Euclid n), IsOpen U → (∀ m : ℕ, ContDiffOn ℝ m h U) → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → (∀ m : ℕ, ContDiffOn ℝ m (fun y => fderiv ℝ h y e) U) ∧ ∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 (fun z => fderiv ℝ h z e) y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
  intro n U h e hU hh hΔ
  -- (i): `Dh` is `Cᵐ` on the open set `U`, and so is its evaluation at `e`
  have hu : ∀ m : ℕ, ContDiffOn ℝ m (fun y => fderiv ℝ h y e) U := fun m =>
    ((hh (m + 1)).fderiv_of_isOpen (m := m) hU (by push_cast; exact le_rfl)).clm_apply
      contDiffOn_const
  refine ⟨hu, fun y hy => ?_⟩
  -- `h` is `C³` at every point of `U`, so `F = Dh` is differentiable on `U`
  have h3 : ∀ z ∈ U, ContDiffAt ℝ 3 h z := fun z hz => (hh 3).contDiffAt (hU.mem_nhds hz)
  have hFd : ∀ z ∈ U, DifferentiableAt ℝ (fderiv ℝ h) z := fun z hz =>
    ((h3 z hz).fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  -- the derivative of `z ↦ c z v` at `z` is `a ↦ Dc(z) a v`
  have ev : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      (c : Euclid n → Euclid n →L[ℝ] W) (v z a : Euclid n), DifferentiableAt ℝ c z →
      fderiv ℝ (fun z' => c z' v) z a = fderiv ℝ c z a v := by
    intro W _ _ c v z a hc
    rw [fderiv_clm_apply hc (differentiableAt_const v)]
    simp
  -- `F` is `C²` at `y`, so `G = D²h` is differentiable at `y`
  have hF2 : ContDiffAt ℝ 2 (fderiv ℝ h) y := (h3 y hy).fderiv_right (by norm_num)
  have hGd : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ h)) y :=
    (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hGbd : ∀ b, DifferentiableAt ℝ (fun z => fderiv ℝ (fderiv ℝ h) z b) y := fun b =>
    hGd.clm_apply (differentiableAt_const b)
  -- (∗): `D(z ↦ G z b c)(y) a = H y a b c`
  have hstar : ∀ a b c, fderiv ℝ (fun z => fderiv ℝ (fderiv ℝ h) z b c) y a =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b c := by
    intro a b c
    rw [ev (fun z => fderiv ℝ (fderiv ℝ h) z b) c y a (hGbd b), ev _ b y a hGd]
  -- `D²u_e(y)(a, b) = H y a b e`
  have hud : DifferentiableAt ℝ (fderiv ℝ (fun z => fderiv ℝ h z e)) y :=
    (((hu 2).contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hu2 : ∀ a b, iteratedFDeriv ℝ 2 (fun z => fderiv ℝ h z e) y ![a, b] =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b e := by
    intro a b
    have hloc : (fun z => fderiv ℝ (fun z => fderiv ℝ h z e) z b) =ᶠ[𝓝 y]
        fun z => fderiv ℝ (fderiv ℝ h) z b e := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ev (fderiv ℝ h) e z b (hFd z hz)
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ev _ b y a hud, hloc.fderiv_eq, hstar]
  -- symmetry of `D²(Dh)` at `y`: `H y a b = H y b a`
  have hsym1 : ∀ a b, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y b a := fun a b =>
    (hF2.isSymmSndFDerivAt (by norm_num)).eq a b
  -- symmetry of `D²h` on `U`, differentiated at `y`: `H y a b c = H y a c b`
  have hsym2 : ∀ a b c, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y a c b := by
    intro a b c
    have hloc : (fun z => fderiv ℝ (fderiv ℝ h) z b c) =ᶠ[𝓝 y]
        fun z => fderiv ℝ (fderiv ℝ h) z c b := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ((h3 z hz).isSymmSndFDerivAt (by norm_num)).eq b c
    rw [← hstar a b c, ← hstar a c b, hloc.fderiv_eq]
  -- the `e`-derivative of `z ↦ Δh(z) = ∑ᵢ G z eᵢ eᵢ`, which vanishes near `y`
  have hL : ∑ i : Fin n, fderiv ℝ (fderiv ℝ (fderiv ℝ h)) y e (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) = 0 := by
    have hloc : (fun z => ∑ i : Fin n, fderiv ℝ (fderiv ℝ h) z (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
        hΔ z hz
    have h0 := congrArg (fun φ : Euclid n →L[ℝ] ℝ => φ e) (hloc.fderiv_eq (𝕜 := ℝ))
    simp only [fderiv_const_apply, zero_apply] at h0
    rw [fderiv_fun_sum fun i _ => (hGbd _).clm_apply (differentiableAt_const _),
      sum_apply] at h0
    rw [← h0]
    exact Finset.sum_congr rfl fun i _ => (hstar e _ _).symm
  rw [← hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hu2, hsym2 _ _ e, hsym1 _ e]
/-- If `f` is continuous on `closedBall y ρ` and equals its own ball mean at `y`,
`∫_{B_ρ(y)} f = V f(y)` with `V = Lⁿ(B_ρ(y))`, then `f(y)² V ≤ ∫_{B_ρ(y)} f²` (Simon Ch. 5, 3.2
with `q = 0`): `0 ≤ ∫_{B_ρ(y)} (f − f(y))² = ∫_{B_ρ(y)} f² − 2f(y) ∫_{B_ρ(y)} f + f(y)² V
= ∫_{B_ρ(y)} f² − f(y)² V`. -/
theorem Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value : ∀ (n : ℕ) (f : Euclid n → ℝ) (y : Euclid n) (ρ : ℝ), 0 < ρ → ContinuousOn f (closedBall y ρ) → ∫ z in ball y ρ, f z = (volume (ball y ρ)).toReal * f y → f y ^ 2 * (volume (ball y ρ)).toReal ≤ ∫ z in ball y ρ, f z ^ 2 := by
  intro n f y ρ _ hf hmean
  -- `f` and `f²` are continuous on the compact closed ball, hence integrable on the ball
  have hfi : IntegrableOn f (ball y ρ) :=
    (hf.integrableOn_compact (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
  have hf2i : IntegrableOn (fun z => f z ^ 2) (ball y ρ) :=
    ((hf.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set ball_subset_closedBall
  have hci : IntegrableOn (fun _ => f y ^ 2) (ball y ρ) := integrableOn_const measure_ball_lt_top.ne
  have hnonneg : 0 ≤ ∫ z in ball y ρ, (f z - f y) ^ 2 :=
    setIntegral_nonneg measurableSet_ball fun z _ => sq_nonneg _
  -- expand the square: `∫ (f − f(y))² = ∫ f² − 2f(y) ∫ f + f(y)² V`
  have hexp : ∫ z in ball y ρ, (f z - f y) ^ 2 = (∫ z in ball y ρ, f z ^ 2) -
      2 * f y * (∫ z in ball y ρ, f z) + f y ^ 2 * (volume (ball y ρ)).toReal := by
    have hi : IntegrableOn (fun z => f z ^ 2 - 2 * f y * f z) (ball y ρ) :=
      hf2i.sub (hfi.const_mul _)
    calc ∫ z in ball y ρ, (f z - f y) ^ 2
        = ∫ z in ball y ρ, ((f z ^ 2 - 2 * f y * f z) + f y ^ 2) := by
          congr 1; funext z; ring
      _ = (∫ z in ball y ρ, f z ^ 2) - 2 * f y * (∫ z in ball y ρ, f z) +
            f y ^ 2 * (volume (ball y ρ)).toReal := by
          rw [integral_add hi hci, integral_sub hf2i (hfi.const_mul _), integral_const_mul,
            setIntegral_const, smul_eq_mul, measureReal_def, mul_comm (volume (ball y ρ)).toReal]
  -- insert `∫ f = V f(y)`
  rw [hexp, hmean] at hnonneg
  linarith

/-- **Operator-norm `L²` bound from the ball mean value identity** (the gradient case of the
interior estimates for harmonic functions, Simon Ch. 5, 3.2–3.3; chapter-05.txt lines 643–653).
Let `g : ℝⁿ → (ℝⁿ)*` be continuous on `closedBall y ρ`, `ρ > 0`, with `V = |B_ρ(y)|` and
`I = ∫_{B_ρ(y)} ‖g‖²`.  If every component `z ↦ g z e` has ball average `g y e`, then
`Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value` and `|g z e| ≤ ‖g z‖ ‖e‖` give
`(g y e)² V ≤ ∫_{B_ρ(y)} (g z e)² ≤ ‖e‖² I`, i.e. `|g y e| ≤ √(I/V) ‖e‖` for every `e`.  Hence
`‖g y‖ ≤ √(I/V)` (`opNorm_le_bound`) and `‖g y‖² V ≤ I`. -/
theorem Submission.dorag_ha_ie_opNorm_sq_mul_volume_le_of_mean_value : ∀ (n : ℕ) (g : Euclid n → (Euclid n →L[ℝ] ℝ)) (y : Euclid n) (ρ : ℝ), 0 < ρ → ContinuousOn g (closedBall y ρ) → (∀ e : Euclid n, ∫ z in ball y ρ, g z e = (volume (ball y ρ)).toReal * g y e) → ‖g y‖ ^ 2 * (volume (ball y ρ)).toReal ≤ ∫ z in ball y ρ, ‖g z‖ ^ 2 := by
  intro n g y ρ hρ hg hmv
  set V := (volume (ball y ρ)).toReal
  set I := ∫ z in ball y ρ, ‖g z‖ ^ 2
  -- `V > 0`, and `‖g‖²` is integrable on the ball (continuous on the compact closed ball).
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume y hρ).ne' measure_ball_lt_top.ne
  have hgn : IntegrableOn (fun z => ‖g z‖ ^ 2) (ball y ρ) :=
    ((hg.norm.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set
      ball_subset_closedBall
  have hI : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun z _ => sq_nonneg _
  -- Each component: `(g y e)² V ≤ ∫_{B_ρ(y)} (g z e)² ≤ ‖e‖² I`.
  have hcomp : ∀ e : Euclid n, g y e ^ 2 * V ≤ ‖e‖ ^ 2 * I := by
    intro e
    have hfe : ContinuousOn (fun z => g z e) (closedBall y ρ) := hg.clm_apply continuousOn_const
    have hfe2 : IntegrableOn (fun z => g z e ^ 2) (ball y ρ) :=
      ((hfe.pow 2).integrableOn_compact (isCompact_closedBall y ρ)).mono_set
        ball_subset_closedBall
    have hpt : ∀ z, g z e ^ 2 ≤ ‖e‖ ^ 2 * ‖g z‖ ^ 2 := fun z => by
      have h : |g z e| ≤ ‖g z‖ * ‖e‖ := by
        simpa only [Real.norm_eq_abs] using (g z).le_opNorm e
      calc g z e ^ 2 = |g z e| ^ 2 := (sq_abs _).symm
        _ ≤ (‖g z‖ * ‖e‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
        _ = ‖e‖ ^ 2 * ‖g z‖ ^ 2 := by ring
    calc g y e ^ 2 * V ≤ ∫ z in ball y ρ, g z e ^ 2 :=
          Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value n (fun z => g z e) y ρ hρ hfe
            (hmv e)
      _ ≤ ∫ z in ball y ρ, ‖e‖ ^ 2 * ‖g z‖ ^ 2 := setIntegral_mono hfe2 (hgn.const_mul _) hpt
      _ = ‖e‖ ^ 2 * I := integral_const_mul _ _
  -- Hence `|g y e| ≤ √(I/V) ‖e‖` for every `e`, so `‖g y‖ ≤ √(I/V)`.
  have hIV : 0 ≤ I / V := div_nonneg hI hV.le
  have hop : ‖g y‖ ≤ √(I / V) := by
    refine (g y).opNorm_le_bound (Real.sqrt_nonneg _) fun e => ?_
    have h : g y e ^ 2 ≤ ‖e‖ ^ 2 * (I / V) := by
      rw [mul_div_assoc', le_div_iff₀ hV]
      exact hcomp e
    calc ‖g y e‖ = √(g y e ^ 2) := by rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]
      _ ≤ √(‖e‖ ^ 2 * (I / V)) := Real.sqrt_le_sqrt h
      _ = √(I / V) * ‖e‖ := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm]
  -- Square and multiply by `V > 0`.
  calc ‖g y‖ ^ 2 * V ≤ √(I / V) ^ 2 * V :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hop 2) hV.le
    _ = I := by rw [Real.sq_sqrt hIV, div_mul_cancel₀ I hV.ne']
/-- Shifted-ball comparison: if `‖w‖ ≤ ρ` and `|u| ≤ K` on `B_{ρ+‖w‖}(x)`, then the integrals of
`u` over `B_ρ(x + w)` and `B_ρ(x)` differ by at most `K ωₙ ((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`.  Both balls
lie in `B_{ρ+‖w‖}(x)`; the difference of the integrals is `∫_{S₁} u − ∫_{S₂} u` with
`S₁ = B_ρ(x + w) \ B_ρ(x)`, `S₂ = B_ρ(x) \ B_ρ(x + w)`, and the disjoint sets `S₁`, `S₂` lie in the
annulus `B_{ρ+‖w‖}(x) \ B_{ρ−‖w‖}(x)`, of measure `ωₙ ((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`. -/
theorem Submission.dorag_ha_ie_shifted_ball_integral_sub_le : ∀ (n : ℕ) (u : Euclid n → ℝ) (x w : Euclid n) (ρ K : ℝ), 0 < n → ‖w‖ ≤ ρ → 0 ≤ K → IntegrableOn u (ball x (ρ + ‖w‖)) → (∀ z ∈ ball x (ρ + ‖w‖), |u z| ≤ K) → |(∫ y in ball (x + w) ρ, u y) - ∫ y in ball x ρ, u y| ≤ K * (volume (ball (0 : Euclid n) 1)).toReal * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by
  intro n u x w ρ K hn hwρ hK hint hbound
  have hs0 : 0 ≤ ‖w‖ := norm_nonneg w
  -- Step 1: both balls lie in `B_{ρ+‖w‖}(x)`
  have hdist : ∀ z : Euclid n, ‖z - x‖ ≤ ‖z - (x + w)‖ + ‖w‖ := fun z => by
    calc ‖z - x‖ = ‖(z - (x + w)) + w‖ := by congr 1; abel
      _ ≤ ‖z - (x + w)‖ + ‖w‖ := norm_add_le _ _
  have hdist' : ∀ z : Euclid n, ‖z - (x + w)‖ ≤ ‖z - x‖ + ‖w‖ := fun z => by
    calc ‖z - (x + w)‖ = ‖(z - x) + -w‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖-w‖ := norm_add_le _ _
      _ = ‖z - x‖ + ‖w‖ := by rw [norm_neg]
  have h₁ : ball (x + w) ρ ⊆ ball x (ρ + ‖w‖) := by
    intro z hz
    rw [mem_ball_iff_norm] at hz ⊢
    linarith [hdist z]
  have h₀ : ball x ρ ⊆ ball x (ρ + ‖w‖) := ball_subset_ball (by linarith)
  -- Step 2: split each ball along the other
  have e₁ := integral_inter_add_sdiff (μ := volume) (t := ball x ρ) measurableSet_ball
    (hint.mono_set h₁)
  have e₀ := integral_inter_add_sdiff (μ := volume) (t := ball (x + w) ρ) measurableSet_ball
    (hint.mono_set h₀)
  rw [inter_comm] at e₀
  rw [← e₁, ← e₀, add_sub_add_left_eq_sub]
  -- Step 3: bound each piece by `K` times its measure
  have hS₁ : ball (x + w) ρ \ ball x ρ ⊆ ball x (ρ + ‖w‖) := sdiff_subset.trans h₁
  have hS₂ : ball x ρ \ ball (x + w) ρ ⊆ ball x (ρ + ‖w‖) := sdiff_subset.trans h₀
  have hpiece : ∀ S ⊆ ball x (ρ + ‖w‖), |∫ y in S, u y| ≤ K * volume.real S := by
    intro S hS
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := u)
      ((measure_mono hS).trans_lt measure_ball_lt_top) (fun z hz => by
        rw [Real.norm_eq_abs]; exact hbound z (hS hz))
    rwa [Real.norm_eq_abs] at this
  -- Step 4: the two pieces are disjoint and lie in the annulus `B_{ρ+‖w‖}(x) \ B_{ρ−‖w‖}(x)`
  have hdisj : Disjoint (ball (x + w) ρ \ ball x ρ) (ball x ρ \ ball (x + w) ρ) :=
    disjoint_sdiff_sdiff
  have hin : Disjoint ((ball (x + w) ρ \ ball x ρ) ∪ (ball x ρ \ ball (x + w) ρ))
      (ball x (ρ - ‖w‖)) := by
    rw [Set.disjoint_left]
    rintro z (⟨_, hz0⟩ | ⟨_, hz1⟩) hzin
    · exact hz0 (ball_subset_ball (by linarith) hzin)
    · apply hz1
      rw [mem_ball_iff_norm] at hzin ⊢
      linarith [hdist' z]
  have hU : (ball (x + w) ρ \ ball x ρ) ∪ (ball x ρ \ ball (x + w) ρ) ∪ ball x (ρ - ‖w‖) ⊆
      ball x (ρ + ‖w‖) :=
    union_subset (union_subset hS₁ hS₂) (ball_subset_ball (by linarith))
  have hmeas : volume.real (ball (x + w) ρ \ ball x ρ) + volume.real (ball x ρ \ ball (x + w) ρ) +
      volume.real (ball x (ρ - ‖w‖)) ≤ volume.real (ball x (ρ + ‖w‖)) := by
    rw [← measureReal_union hdisj (measurableSet_ball.diff measurableSet_ball)
      (measure_ne_top_of_subset hS₁ measure_ball_lt_top.ne)
      (measure_ne_top_of_subset hS₂ measure_ball_lt_top.ne),
      ← measureReal_union hin measurableSet_ball
      (measure_ne_top_of_subset (union_subset hS₁ hS₂) measure_ball_lt_top.ne)
      measure_ball_lt_top.ne]
    exact measureReal_mono hU measure_ball_lt_top.ne
  -- Step 5: measure of balls, `Lⁿ(B_r(x)) = ωₙ rⁿ` for `r ≥ 0`
  have : Nontrivial (Euclid n) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hn)
  have hball : ∀ r : ℝ, 0 ≤ r →
      volume.real (ball x r) = r ^ n * (volume (ball (0 : Euclid n) 1)).toReal := by
    intro r hr
    rw [measureReal_def, Measure.addHaar_ball volume x hr, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr n)]
  rw [hball (ρ + ‖w‖) (by linarith), hball (ρ - ‖w‖) (by linarith)] at hmeas
  -- Step 6: conclusion
  calc |(∫ y in ball (x + w) ρ \ ball x ρ, u y) - ∫ y in ball x ρ \ ball (x + w) ρ, u y|
      ≤ |∫ y in ball (x + w) ρ \ ball x ρ, u y| + |∫ y in ball x ρ \ ball (x + w) ρ, u y| :=
        abs_sub _ _
    _ ≤ K * volume.real (ball (x + w) ρ \ ball x ρ) +
        K * volume.real (ball x ρ \ ball (x + w) ρ) := add_le_add (hpiece _ hS₁) (hpiece _ hS₂)
    _ = K * (volume.real (ball (x + w) ρ \ ball x ρ) +
        volume.real (ball x ρ \ ball (x + w) ρ)) := by ring
    _ ≤ K * ((ρ + ‖w‖) ^ n * (volume (ball (0 : Euclid n) 1)).toReal -
        (ρ - ‖w‖) ^ n * (volume (ball (0 : Euclid n) 1)).toReal) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = K * (volume (ball (0 : Euclid n) 1)).toReal * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by ring

/-- **Interior gradient bound from the ball mean value identity** (Simon Ch. 5, estimates
3.2–3.4, derived by comparing ball means over shifted balls).  Let `ω = Lⁿ(B̆₁(0))`, so
`Lⁿ(B̆_ρ(z)) = ωρⁿ`.  For `‖w‖ ≤ ρ/2` the mean value identity at `x + w` and at `x`, together
with `Submission.dorag_ha_ie_shifted_ball_integral_sub_le`, give
`ρⁿ|u(x + w) − u(x)| ≤ K((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)`, and `abs_pow_sub_pow_le` bounds the right
side by `2‖w‖nK(ρ + η)ⁿ⁻¹` when `‖w‖ ≤ η`.  Hence `‖Du(x)‖ ≤ 2nK(ρ + η)ⁿ⁻¹/ρⁿ` for
`0 < η ≤ ρ/2` (`HasFDerivAt.le_of_lip'`), and letting `η → 0⁺` gives `‖Du(x)‖ ≤ 2nK/ρ`. -/
theorem Submission.dorag_ha_ie_norm_fderiv_le_of_mean_value : ∀ (n : ℕ) (u : Euclid n → ℝ) (x : Euclid n) (ρ K : ℝ), 0 < n → 0 < ρ → DifferentiableAt ℝ u x → ContinuousOn u (closedBall x (3 * ρ / 2)) → (∀ z ∈ closedBall x (3 * ρ / 2), |u z| ≤ K) → (∀ z ∈ closedBall x (ρ / 2), ∫ y in ball z ρ, u y = (volume (ball z ρ)).toReal * u z) → ‖fderiv ℝ u x‖ ≤ 2 * (n : ℝ) * K / ρ := by
  intro n u x ρ K hn hρ hdiff hcont hbound hmv
  -- Step 1: `Lⁿ(B̆_ρ(z)) = ρⁿω` with `ω > 0`, and `K ≥ |u(x)| ≥ 0`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, (volume (ball (0 : Euclid n) 1)).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := by
    rw [← hω_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hvol : ∀ z : Euclid n, (volume (ball z ρ)).toReal = ρ ^ n * ω := by
    intro z
    rw [Measure.addHaar_ball_of_pos volume z hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hρ.le n), hω_def]
  have hx : x ∈ closedBall x (ρ / 2) := mem_closedBall_self (by positivity)
  have hK : 0 ≤ K := (abs_nonneg _).trans (hbound x (mem_closedBall_self (by positivity)))
  -- Step 2: `ρⁿ|u(x + w) − u(x)| ≤ K((ρ + ‖w‖)ⁿ − (ρ − ‖w‖)ⁿ)` for `‖w‖ ≤ ρ/2`
  have hshift : ∀ w : Euclid n, ‖w‖ ≤ ρ / 2 →
      ρ ^ n * |u (x + w) - u x| ≤ K * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := by
    intro w hw
    have hsub : ball x (ρ + ‖w‖) ⊆ closedBall x (3 * ρ / 2) :=
      ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
    have hint : IntegrableOn u (ball x (ρ + ‖w‖)) :=
      (hcont.integrableOn_compact (isCompact_closedBall x _)).mono_set hsub
    have hcmp := Submission.dorag_ha_ie_shifted_ball_integral_sub_le n u x w ρ K hn
      (by linarith) hK hint fun z hz => hbound z (hsub hz)
    have hxw : x + w ∈ closedBall x (ρ / 2) := by
      rwa [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    have hdiffint : (∫ y in ball (x + w) ρ, u y) - ∫ y in ball x ρ, u y
        = ω * (ρ ^ n * (u (x + w) - u x)) := by
      rw [hmv (x + w) hxw, hmv x hx, hvol, hvol]
      ring
    rw [hdiffint, abs_mul, abs_mul, abs_of_pos hω, abs_of_pos (pow_pos hρ n), hω_def] at hcmp
    refine le_of_mul_le_mul_left ?_ hω
    calc ω * (ρ ^ n * |u (x + w) - u x|) ≤ K * ω * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n) := hcmp
      _ = ω * (K * ((ρ + ‖w‖) ^ n - (ρ - ‖w‖) ^ n)) := by ring
  -- Step 3: `(ρ + s)ⁿ − (ρ − s)ⁿ ≤ 2sn(ρ + η)ⁿ⁻¹` for `0 ≤ s ≤ ρ`, `s ≤ η`
  have hpow : ∀ s η : ℝ, 0 ≤ s → s ≤ ρ → s ≤ η →
      (ρ + s) ^ n - (ρ - s) ^ n ≤ 2 * s * n * (ρ + η) ^ (n - 1) := by
    intro s η hs hsρ hsη
    have h := abs_pow_sub_pow_le (ρ + s) (ρ - s) n
    rw [show ρ + s - (ρ - s) = 2 * s by ring, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * s),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ + s), abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ - s),
      max_eq_left (by linarith : ρ - s ≤ ρ + s)] at h
    calc (ρ + s) ^ n - (ρ - s) ^ n ≤ |(ρ + s) ^ n - (ρ - s) ^ n| := le_abs_self _
      _ ≤ 2 * s * n * (ρ + s) ^ (n - 1) := h
      _ ≤ 2 * s * n * (ρ + η) ^ (n - 1) := by gcongr
  -- Step 4: `‖Du(x)‖ ≤ C_η := 2nK(ρ + η)ⁿ⁻¹/ρⁿ` for `0 < η ≤ ρ/2`
  have hstep : ∀ η : ℝ, 0 < η → η ≤ ρ / 2 →
      ‖fderiv ℝ u x‖ ≤ 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n := by
    intro η hη hηρ
    refine hdiff.hasFDerivAt.le_of_lip' (by positivity) ?_
    filter_upwards [ball_mem_nhds x hη] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h₁ := hshift (y - x) (by linarith)
    rw [add_sub_cancel] at h₁
    have h₂ := hpow ‖y - x‖ η (norm_nonneg _) (by linarith) hy.le
    rw [Real.norm_eq_abs, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hρ n)]
    calc |u y - u x| * ρ ^ n = ρ ^ n * |u y - u x| := mul_comm _ _
      _ ≤ K * ((ρ + ‖y - x‖) ^ n - (ρ - ‖y - x‖) ^ n) := h₁
      _ ≤ K * (2 * ‖y - x‖ * n * (ρ + η) ^ (n - 1)) := mul_le_mul_of_nonneg_left h₂ hK
      _ = 2 * n * K * (ρ + η) ^ (n - 1) * ‖y - x‖ := by ring
  -- Step 5: let `η → 0⁺`; `C_η → 2nKρⁿ⁻¹/ρⁿ = 2nK/ρ`
  have hlim : Tendsto (fun η : ℝ => 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n) (𝓝[>] 0)
      (𝓝 (2 * n * K * (ρ + 0) ^ (n - 1) / ρ ^ n)) := by
    have hC : Continuous fun η : ℝ => 2 * n * K * (ρ + η) ^ (n - 1) / ρ ^ n := by fun_prop
    exact (hC.tendsto 0).mono_left nhdsWithin_le_nhds
  have hval : 2 * n * K * (ρ + 0) ^ (n - 1) / ρ ^ n = 2 * n * K / ρ := by
    have hpn : ρ ^ n = ρ * ρ ^ (n - 1) := by rw [← pow_succ', Nat.sub_add_cancel hn]
    rw [add_zero, hpn, mul_div_mul_right _ _ (pow_ne_zero _ hρ.ne')]
  rw [← hval]
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (half_pos hρ)] with η hη
  exact hstep η hη.1 hη.2.le
/-- **Order-2 Taylor bound along a segment** (Simon Ch. 5, 3.4, p. 115: "an order 2 Taylor series
expansion for `u`").  If `h` is `C²` on `B_R(0)`, `‖v‖ < R` and `|D²h(τv)(v, v)| ≤ S` for
`τ ∈ [0, 1]`, then `|h(v) − h(0) − Dh(0)v| ≤ S/2`: with `φ(τ) = h(τv)` and `φ₁(τ) = Dh(τv)v`, the
mean value inequality gives `|φ₁(τ) − φ₁(0)| ≤ Sτ`, and comparing `ψ(τ) = φ(τ) − φ(0) − τφ₁(0)`
with `Sτ²/2` gives `|ψ(1)| ≤ S/2`. -/
theorem Submission.dorag_ha_ie_taylor_two_le : ∀ (n : ℕ) (h : Euclid n → ℝ) (R S : ℝ) (v : Euclid n), ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) → ‖v‖ < R → (∀ τ ∈ Icc (0 : ℝ) 1, |iteratedFDeriv ℝ 2 h (τ • v) ![v, v]| ≤ S) → |h v - h 0 - fderiv ℝ h 0 v| ≤ S / 2 := by
  intro n h R S v hh hv hS
  -- Step 1: the segment `τ ↦ τ • v`, `τ ∈ [0, 1]`, lies in the open ball
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, τ • v ∈ ball (0 : Euclid n) R := by
    intro τ hτ
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hτ.1]
    exact (mul_le_of_le_one_left (norm_nonneg v) hτ.2).trans_lt hv
  -- Step 2: `h` and `Dh` are differentiable on the open ball
  have hD1 : ∀ p ∈ ball (0 : Euclid n) R, HasFDerivAt h (fderiv ℝ h p) p := fun p hp =>
    ((hh.differentiableOn two_ne_zero).differentiableAt (isOpen_ball.mem_nhds hp)).hasFDerivAt
  have hD2 : ∀ p ∈ ball (0 : Euclid n) R,
      HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) p) p := fun p hp =>
    (((hh.fderiv_of_isOpen isOpen_ball (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
      one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hp)).hasFDerivAt
  -- Step 3: `φ τ = h (τ • v)` has derivative `φ₁ τ = Dh (τ • v) v`, and `φ₁` has derivative
  -- `D²h (τ • v) (v, v)`
  have hline : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => t • v) v τ := fun τ => by
    simpa using (hasDerivAt_id τ).smul_const v
  have hφ : ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (t • v)) (fderiv ℝ h (τ • v) v) τ := fun τ hτ =>
    (hD1 _ (hmem τ hτ)).comp_hasDerivAt τ (hline τ)
  have hφ₁ : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => fderiv ℝ h (t • v) v)
      (iteratedFDeriv ℝ 2 h (τ • v) ![v, v]) τ := fun τ hτ => by
    have h1 : HasDerivAt (fderiv ℝ h ∘ fun t : ℝ => t • v)
        (fderiv ℝ (fderiv ℝ h) (τ • v) v) τ :=
      (hD2 _ (hmem τ hτ)).comp_hasDerivAt τ (hline τ)
    rw [iteratedFDeriv_two_apply]
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt τ h1
  -- Step 4: mean value inequality, `|φ₁ τ - φ₁ 0| ≤ S τ` on `[0, 1]`
  have hmvt : ∀ τ ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ h (τ • v) v - fderiv ℝ h 0 v‖ ≤ S * τ := by
    have := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun τ hτ => (hφ₁ τ hτ).hasDerivWithinAt) (fun τ hτ => hS τ (Ico_subset_Icc_self hτ))
    simpa using this
  -- Step 5: compare `ψ τ = φ τ - φ 0 - τ φ₁ 0` with `S τ² / 2`
  have hψ : ∀ τ ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => h (t • v) - h 0 - t * fderiv ℝ h 0 v)
        (fderiv ℝ h (τ • v) v - fderiv ℝ h 0 v) τ := fun τ hτ => by
    simpa using
      ((hφ τ hτ).sub_const (h 0)).fun_sub ((hasDerivAt_id τ).mul_const (fderiv ℝ h 0 v))
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => S * t ^ 2 / 2) (S * x) x := fun x => by
    convert ((hasDerivAt_pow 2 x).const_mul S).div_const 2 using 1
    ring
  have hcmp := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun τ hτ => (hψ τ hτ).continuousAt.continuousWithinAt)
    (fun τ hτ => (hψ τ (Ico_subset_Icc_self hτ)).hasDerivWithinAt)
    (by simp) hB (fun τ hτ => hmvt τ (Ico_subset_Icc_self hτ))
    (right_mem_Icc.2 zero_le_one)
  -- Step 6: at `τ = 1`, `ψ 1 = h v - h 0 - Dh 0 v`
  simpa using hcmp
/-- The radial potential of the mean value property (Simon Ch. 5, 3.2–3.4).  For continuous `g`
vanishing on `[r², ∞)`, `Ψ(y) = P(|y|²)` with `P(t) = ½∫_{r²}^t g` is `C¹` with
`DΨ(y)v = P'(|y|²)·2⟨y, v⟩ = g(|y|²)⟨y, v⟩` (FTC and the chain rule), and `Ψ(y) = 0` for
`|y| ≥ r`, so `tsupport Ψ ⊆ closedBall 0 r`, which is compact. -/
theorem Submission.dorag_ha_mv_radial_potential : ∀ (n : ℕ) (r : ℝ) (g : ℝ → ℝ), 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∃ Ψ : Euclid n → ℝ, ContDiff ℝ 1 Ψ ∧ HasCompactSupport Ψ ∧ tsupport Ψ ⊆ closedBall 0 r ∧ ∀ y v : Euclid n, fderiv ℝ Ψ y v = g (‖y‖ ^ 2) * inner ℝ y v := by
  intro n r g hr hg hgr
  set P : ℝ → ℝ := fun t => (1/2 : ℝ) * ∫ τ in r ^ 2..t, g τ with hP
  have hPd : ∀ t, HasDerivAt P ((1/2 : ℝ) * g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt (r ^ 2) t).hasDerivAt).const_mul (1/2 : ℝ)
  have hPC : ContDiff ℝ 1 P := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hPd t).differentiableAt, ?_⟩
    have : deriv P = fun t => (1/2 : ℝ) * g t := funext fun t => (hPd t).deriv
    rw [this]; exact continuous_const.mul hg
  have hP0 : ∀ t, r ^ 2 ≤ t → P t = 0 := by
    intro t ht
    simp only [hP]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro τ hτ
      rw [uIcc_of_le ht] at hτ
      exact hgr τ hτ.1
  have hsupp : tsupport (fun y : Euclid n => P (‖y‖ ^ 2)) ⊆ closedBall 0 r := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    rw [mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    exact hy (hP0 _ (pow_le_pow_left₀ hr.le hlt.le 2))
  refine ⟨fun y => P (‖y‖ ^ 2), hPC.comp (contDiff_norm_sq ℝ), ?_, hsupp, ?_⟩
  · exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 r) (isClosed_tsupport _) hsupp
  · intro y v
    have hd : HasFDerivAt (fun y : Euclid n => P (‖y‖ ^ 2))
        (((1/2 : ℝ) * g (‖y‖ ^ 2)) • (2 • innerSL ℝ y)) y :=
      (hPd _).comp_hasFDerivAt y (hasStrictFDerivAt_norm_sq y).hasFDerivAt
    rw [hd.fderiv]
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
    ring
/-- **Green's first identity** for a compactly supported `C¹` function `Ψ` against a function `G`
that is `C²` on an open set `V ⊇ tsupport Ψ` (step 4 of the mean value argument):
`∫ ∑ᵢ DΨ(y)eᵢ · DG(y)eᵢ dy = -∫ Ψ(y) ∑ᵢ D²G(y)(eᵢ, eᵢ) dy`.

For each direction `v = eᵢ`, the product `h = Ψ · DG(·)v` is differentiable everywhere (it vanishes
near every point off `K = tsupport Ψ ⊆ V`), and `y ↦ Dh(y)v = DΨ(y)v · DG(y)v + Ψ(y) D²G(y)(v, v)`
is continuous with compact support.  By translation invariance `t ↦ ∫ h(y + tv) dy` is constant,
and differentiating under the integral at `t = 0` gives `∫ Dh(y)v dy = 0`.  Summing over `i`, with
every summand integrable, gives the identity. -/
theorem Submission.dorag_ha_mv_green_identity : ∀ (n : ℕ) (V : Set (Euclid n)) (G Ψ : Euclid n → ℝ), IsOpen V → ContDiffOn ℝ 2 G V → ContDiff ℝ 1 Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ V → ∫ y : Euclid n, ∑ i : Fin n, fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) * fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) = -∫ y : Euclid n, Ψ y * ∑ i : Fin n, iteratedFDeriv ℝ 2 G y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
  intro n V G Ψ hV hG hΨ hΨc hΨV
  -- Step 1: `DG` is `C¹` on the open set `V`
  have hG1 : ContDiffOn ℝ 1 (fderiv ℝ G) V := hG.fderiv_of_isOpen hV (by norm_num)
  have hGd : ∀ y ∈ V, DifferentiableAt ℝ (fderiv ℝ G) y := fun y hy =>
    (hG1.differentiableOn one_ne_zero y hy).differentiableAt (hV.mem_nhds hy)
  have hG1c : ContinuousOn (fderiv ℝ G) V := hG1.continuousOn
  have hG2c : ContinuousOn (fderiv ℝ (fderiv ℝ G)) V :=
    hG1.continuousOn_fderiv_of_isOpen hV le_rfl
  -- Step 2: `Ψ` and `DΨ` vanish off `K = tsupport Ψ`
  have hΨ0 : ∀ y, y ∉ tsupport Ψ → Ψ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdΨ0 : ∀ y, y ∉ tsupport Ψ → fderiv ℝ Ψ y = 0 := fun y hy => by
    by_contra h'
    exact hy (support_fderiv_subset ℝ h')
  have hdΨc : Continuous (fderiv ℝ Ψ) := hΨ.continuous_fderiv one_ne_zero
  have hKo : ∀ y, y ∉ tsupport Ψ → (tsupport Ψ)ᶜ ∈ 𝓝 y := fun y hy =>
    (isClosed_tsupport Ψ).isOpen_compl.mem_nhds hy
  -- Step 3: continuous on `V` and zero off `K` gives continuous with compact support
  have glue : ∀ f : Euclid n → ℝ, ContinuousOn f V → (∀ y, y ∉ tsupport Ψ → f y = 0) →
      Continuous f ∧ HasCompactSupport f := by
    intro f hf h0
    refine ⟨continuous_iff_continuousAt.2 fun y => ?_, ?_⟩
    · by_cases hy : y ∈ V
      · exact hf.continuousAt (hV.mem_nhds hy)
      · have hy' : y ∉ tsupport Ψ := fun h => hy (hΨV h)
        have hfy : f =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [hKo y hy'] with z hz
          exact h0 z hz
        exact continuousAt_const.congr hfy.symm
    · refine IsCompact.of_isClosed_subset hΨc (isClosed_tsupport _) ?_
      refine closure_minimal (fun y hy => ?_) (isClosed_tsupport Ψ)
      by_contra h
      exact hy (h0 y h)
  -- the derivative along `v` of a compactly supported function has integral zero
  have core : ∀ (h k : Euclid n → ℝ) (v : Euclid n), Continuous h → HasCompactSupport h →
      Continuous k → HasCompactSupport k →
      (∀ (y : Euclid n) (t : ℝ), HasDerivAt (fun s : ℝ => h (y + s • v)) (k (y + t • v)) t) →
      ∫ y, k y = 0 := by
    intro h k v hh hhc hk hkc hd
    obtain ⟨C, hC⟩ := hk.bounded_above_of_compact_support hkc
    have hSc : IsCompact (cthickening ‖v‖ (tsupport k)) := IsCompact.cthickening hkc
    have hbound : ∀ (y : Euclid n) (t : ℝ), t ∈ ball (0 : ℝ) 1 →
        ‖k (y + t • v)‖ ≤ (cthickening ‖v‖ (tsupport k)).indicator (fun _ => C) y := by
      intro y t ht
      by_cases hy : y ∈ cthickening ‖v‖ (tsupport k)
      · rw [indicator_of_mem hy]
        exact hC _
      · rw [indicator_of_notMem hy]
        have hk0 : k (y + t • v) = 0 := by
          by_contra hne
          apply hy
          refine mem_cthickening_of_dist_le y (y + t • v) ‖v‖ (tsupport k)
            (subset_tsupport k hne) ?_
          have ht1 : ‖t‖ < 1 := by simpa using ht
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul]
          nlinarith [norm_nonneg v, norm_nonneg t]
        simp [hk0]
    have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun (t : ℝ) (y : Euclid n) => h (y + t • v))
      (F' := fun (t : ℝ) (y : Euclid n) => k (y + t • v))
      (x₀ := 0) (bound := (cthickening ‖v‖ (tsupport k)).indicator (fun _ => C))
      (ball_mem_nhds 0 one_pos)
      (Eventually.of_forall fun t =>
        (hh.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (by simpa using hh.integrable_of_hasCompactSupport hhc)
      ((hk.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (ae_of_all _ fun y t ht => hbound y t ht)
      ((integrableOn_const hSc.measure_lt_top.ne).integrable_indicator
        isClosed_cthickening.measurableSet)
      (ae_of_all _ fun y t _ => hd y t)).2
    have hconst : (fun t : ℝ => ∫ y, h (y + t • v)) = fun _ => ∫ y, h y := by
      funext t
      exact integral_add_right_eq_self (fun y => h y) (t • v)
    rw [hconst] at hderiv
    simpa using hderiv.unique (hasDerivAt_const (0 : ℝ) (∫ y, h y))
  -- Steps 4–6: one coordinate direction
  have key : ∀ i : Fin n,
      Integrable (fun y => fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) *
        fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ))) ∧
      Integrable (fun y => Ψ y * iteratedFDeriv ℝ 2 G y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) ∧
      ∫ y, fderiv ℝ Ψ y (EuclideanSpace.single i (1 : ℝ)) *
          fderiv ℝ G y (EuclideanSpace.single i (1 : ℝ)) =
        -∫ y, Ψ y * iteratedFDeriv ℝ 2 G y
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] := by
    intro i
    set v : Euclid n := EuclideanSpace.single i (1 : ℝ)
    have h2 : (fun y => Ψ y * iteratedFDeriv ℝ 2 G y ![v, v]) =
        fun y => Ψ y * fderiv ℝ (fderiv ℝ G) y v v := by
      funext y
      simp [iteratedFDeriv_two_apply]
    rw [h2]
    have hgc : ContinuousOn (fun y => fderiv ℝ G y v) V :=
      (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn hG1c
    have hg2c : ContinuousOn (fun y => fderiv ℝ (fderiv ℝ G) y v v) V :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (ContinuousLinearMap.apply ℝ (Euclid n →L[ℝ] ℝ) v).continuous).comp_continuousOn hG2c
    obtain ⟨hAc, hAs⟩ := glue (fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v)
      ((hdΨc.clm_apply continuous_const).continuousOn.mul hgc)
      (fun y hy => by simp [hdΨ0 y hy])
    obtain ⟨hBc, hBs⟩ := glue (fun y => Ψ y * fderiv ℝ (fderiv ℝ G) y v v)
      (hΨ.continuous.continuousOn.mul hg2c) (fun y hy => by simp [hΨ0 y hy])
    obtain ⟨hhc, hhs⟩ := glue (fun y => Ψ y * fderiv ℝ G y v)
      (hΨ.continuous.continuousOn.mul hgc) (fun y hy => by simp [hΨ0 y hy])
    -- the product `Ψ · DG(·)v` is differentiable everywhere
    have hF : ∀ z, HasFDerivAt (fun y => Ψ y * fderiv ℝ G y v)
        (Ψ z • ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ G) z)) +
          fderiv ℝ G z v • fderiv ℝ Ψ z) z := by
      intro z
      by_cases hz : z ∈ V
      · exact (hΨ.differentiable one_ne_zero z).hasFDerivAt.mul
          ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp z (hGd z hz).hasFDerivAt)
      · have hz' : z ∉ tsupport Ψ := fun h => hz (hΨV h)
        rw [hΨ0 z hz', hdΨ0 z hz', zero_smul, smul_zero, add_zero]
        refine (hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq ?_
        filter_upwards [hKo z hz'] with y hy
        simp [hΨ0 y hy]
    have hd : ∀ (y : Euclid n) (t : ℝ),
        HasDerivAt (fun s : ℝ => Ψ (y + s • v) * fderiv ℝ G (y + s • v) v)
          ((fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v + Ψ y * fderiv ℝ (fderiv ℝ G) y v v)
            (y + t • v)) t := by
      intro y t
      have hp : HasDerivAt (fun s : ℝ => y + s • v) v t := by
        simpa using ((hasDerivAt_id t).smul_const v).const_add y
      refine ((hF (y + t • v)).comp_hasDerivAt t hp).congr_deriv ?_
      simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.apply_apply, smul_eq_mul]
      ring
    have hA := hAc.integrable_of_hasCompactSupport (μ := volume) hAs
    have hB := hBc.integrable_of_hasCompactSupport (μ := volume) hBs
    have h0 := core (fun y => Ψ y * fderiv ℝ G y v)
      (fun y => fderiv ℝ Ψ y v * fderiv ℝ G y v + Ψ y * fderiv ℝ (fderiv ℝ G) y v v) v
      hhc hhs (hAc.add hBc) (hAs.add hBs) hd
    rw [integral_add hA hB] at h0
    exact ⟨hA, hB, by linarith⟩
  -- Step 7: sum over the coordinate directions
  rw [integral_finsetSum _ (fun i _ => (key i).1)]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => (key i).2.1), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => (key i).2.2
/-- **Derivatives of `z ↦ h(x − s z)`** (the chain-rule step in the proof of the mean-value
property of harmonic functions, cited in Simon Ch. 5 before 3.2; chapter-05.txt lines 643–644).
For an arbitrary `h : ℝⁿ → ℝ` and `G(z) = h(x − s z)`: `DG(y) a = −s·Dh(x − s y) a` and
`D²G(y)(a, b) = s²·D²h(x − s y)(a, b)`, with Mathlib's total derivatives (`0` where undefined).
If `s = 0`, `G` is constant.  Otherwise `G = h(x + ·) ∘ L` for the continuous linear equivalence
`L z = (−s) z`, and `fderiv`, `iteratedFDeriv` commute with `∘ L` and with translations for every
function. -/
theorem Submission.dorag_ha_mv_affine_comp_deriv : ∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (s : ℝ) (y a b : Euclid n), fderiv ℝ (fun z : Euclid n => h (x - s • z)) y a = -(s * fderiv ℝ h (x - s • y) a) ∧ iteratedFDeriv ℝ 2 (fun z : Euclid n => h (x - s • z)) y ![a, b] = s ^ 2 * iteratedFDeriv ℝ 2 h (x - s • y) ![a, b] := by
  intro n h x s y a b
  rcases eq_or_ne s 0 with rfl | hs
  -- `s = 0`: `G` is the constant `h x`, so both sides vanish.
  · simp only [zero_smul, sub_zero, zero_mul, neg_zero]
    rw [iteratedFDeriv_const_of_ne (by norm_num)]
    simp
  -- `s ≠ 0`: `G = h (x + ·) ∘ L` with `L z = (-s) • z`.
  · let L : Euclid n ≃L[ℝ] Euclid n :=
      ContinuousLinearEquiv.smulLeft (Units.mk0 (-s) (neg_ne_zero.2 hs))
    have hL : ∀ z, L z = (-s) • z := fun z => rfl
    have hfun : (fun z : Euclid n => h (x - s • z)) = (fun w => h (x + w)) ∘ L := by
      funext z; simp [hL, sub_eq_add_neg, neg_smul]
    constructor
    -- `DG(y) a = Dh(x + L y)(L a)`, and `L a = (-s) • a`.
    · rw [hfun, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_left]
      simp [hL, sub_eq_add_neg, neg_smul, map_smul]
    -- `D²G(y)(a, b) = D²h(x + L y)(L a, L b) = (-s) * (-s) * D²h(x - s • y)(a, b)`.
    · rw [hfun]
      have hcomp := L.iteratedFDerivWithin_comp_right (fun w => h (x + w)) uniqueDiffOn_univ
        (mem_univ (L y)) 2
      rw [preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at hcomp
      rw [hcomp, ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_comp_add_left]
      have hv : (fun i : Fin 2 => (L : Euclid n →L[ℝ] Euclid n) (![a, b] i)) =
          fun i => (-s) • ![a, b] i := by
        funext i; exact hL _
      rw [hv, ContinuousMultilinearMap.map_smul_univ]
      simp [hL, sub_eq_add_neg, neg_smul, sq]
/-- **Differentiation under the integral sign** for `M(σ) = ∫ h(x − σy) g(|y|²) dy`, the step
`M'(s) = −∫ Dh(x − sy)(y) g(|y|²) dy` in the proof of the mean value property of harmonic
functions.  Here `h` is `C¹` on the open set `U ⊇ B̄_R(x)`, `r > 0`, `g` is continuous with
`g(t) = 0` for `t ≥ r²`, and `|s| r < R`.  For `|σ − s| < δ = (R − |s|r)/(2r)` and `|y| ≤ r`,
`x − σy ∈ B̄_{R₁}(x) ⊆ U` with `R₁ = (|s| + δ) r < R`; the integrand and its `σ`-derivative
`−Dh(x − σy)(y) g(|y|²)` vanish for `|y| ≥ r`, and the derivative is bounded by
`A₁ r γ 1_{B̄_r(0)}` with `A₁ = max_{B̄_{R₁}(x)} ‖Dh‖` and `γ = max_{[0,r²]} |g|`, so
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies. -/
theorem Submission.dorag_ha_mv_deriv_under_integral : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ) (x : Euclid n) (r R : ℝ) (g : ℝ → ℝ), IsOpen U → ContDiffOn ℝ 1 h U → closedBall x R ⊆ U → 0 < r → Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, |s| * r < R → HasDerivAt (fun σ : ℝ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2)) (-∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)) s := by
  intro n U h x r R g hU hh hRU hr hg hgr s hs
  -- the neighbourhood `ball s δ` of `s` and the radius `R₁ = (|s| + δ) r < R`
  set δ : ℝ := (R - |s| * r) / (2 * r) with hδ
  have hδpos : 0 < δ := div_pos (by linarith) (by positivity)
  set R₁ : ℝ := (|s| + δ) * r with hR₁
  have hR₁R : R₁ < R := by
    have : R₁ = |s| * r + (R - |s| * r) / 2 := by
      simp only [hR₁, hδ]; field_simp
    rw [this]; linarith
  -- `g(|y|²) = 0` for `|y| ≥ r`, and `|(x − σy) − x| = |σ| |y|`
  have hgz : ∀ y : Euclid n, r ≤ ‖y‖ → g (‖y‖ ^ 2) = 0 := fun y hy =>
    hgr _ (pow_le_pow_left₀ hr.le hy 2)
  have hnorm : ∀ (σ : ℝ) (y : Euclid n), ‖x - σ • y - x‖ = |σ| * ‖y‖ := by
    intro σ y; rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
  -- for `|y| ≤ r`: `x − σy ∈ U` if `|σ| r < R`, and `x − σy ∈ B̄_{R₁}(x)` if `σ ∈ ball s δ`
  have hmemU : ∀ σ : ℝ, |σ| * r < R → ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ U := by
    intro σ hσ y hy
    apply hRU
    rw [mem_closedBall, dist_eq_norm, hnorm]
    nlinarith [abs_nonneg σ]
  have hball : ∀ σ ∈ ball s δ, |σ| < |s| + δ := by
    intro σ hσ
    rw [mem_ball, Real.dist_eq] at hσ
    have := abs_sub_abs_le_abs_sub σ s
    linarith
  have hball' : ∀ σ ∈ ball s δ, |σ| * r < R := by
    intro σ hσ
    have := hball σ hσ
    have : |σ| * r < (|s| + δ) * r := mul_lt_mul_of_pos_right this hr
    linarith
  have hmemK : ∀ σ ∈ ball s δ, ∀ y : Euclid n, ‖y‖ ≤ r → x - σ • y ∈ closedBall x R₁ := by
    intro σ hσ y hy
    rw [mem_closedBall, dist_eq_norm, hnorm]
    have := hball σ hσ
    calc |σ| * ‖y‖ ≤ (|s| + δ) * r := by
          apply mul_le_mul this.le hy (norm_nonneg _) (by positivity)
      _ = R₁ := rfl
  -- `h` is continuous and differentiable at every point of `U`, and `Dh` is continuous on `U`
  have hhc : ∀ z ∈ U, ContinuousAt h z := fun z hz =>
    hh.continuousOn.continuousAt (hU.mem_nhds hz)
  have hdc : ContinuousOn (fderiv ℝ h) U := hh.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ h z := fun z hz =>
    (hh.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)
  -- bounds `A₁` for `‖Dh‖` on the compact `B̄_{R₁}(x)` and `γ` for `|g(|y|²)|`
  obtain ⟨A₁, hA₁⟩ := (isCompact_closedBall x R₁).exists_bound_of_continuousOn
    (hdc.mono ((closedBall_subset_closedBall hR₁R.le).trans hRU))
  obtain ⟨γ, hγ⟩ := (isCompact_Icc (a := (0:ℝ)) (b := r ^ 2)).exists_bound_of_continuousOn
    hg.continuousOn
  have hgγ : ∀ y : Euclid n, ‖g (‖y‖ ^ 2)‖ ≤ γ := by
    intro y
    by_cases hy : ‖y‖ ≤ r
    · exact hγ _ ⟨by positivity, pow_le_pow_left₀ (norm_nonneg _) hy 2⟩
    · rw [hgz y (le_of_not_ge hy), norm_zero]
      exact (norm_nonneg _).trans (hγ 0 ⟨le_rfl, by positivity⟩)
  -- continuity in `y` of the integrand for `|σ| r < R`, and of its `σ`-derivative at `s`
  have hFcont : ∀ σ : ℝ, |σ| * r < R →
      Continuous (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ hσ
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => h (x - σ • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - σ • y) (hhc _ (hmemU σ hσ y₀ hy₀)) (by fun_prop)
      exact h1.mul (by fun_prop)
    · push Not at hy₀
      have : (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) =ᶠ[𝓝 y₀] fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero]
      exact continuousAt_const.congr this.symm
  have hF'cont : Continuous (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) := by
    rw [continuous_iff_continuousAt]
    intro y₀
    by_cases hy₀ : ‖y₀‖ ≤ r
    · have h1 : ContinuousAt (fun y : Euclid n => fderiv ℝ h (x - s • y)) y₀ :=
        ContinuousAt.comp (f := fun y : Euclid n => x - s • y)
          (hdc.continuousAt (hU.mem_nhds (hmemU s hs y₀ hy₀))) (by fun_prop)
      exact ((h1.clm_apply continuousAt_id).mul (by fun_prop)).neg
    · push Not at hy₀
      have : (fun y : Euclid n => -(fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2))) =ᶠ[𝓝 y₀]
          fun _ => 0 := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy₀] with y hy
        rw [hgz y (le_of_lt hy), mul_zero, neg_zero]
      exact continuousAt_const.congr this.symm
  -- the integrand vanishes off `B̄_r(0)`
  have hsupp : ∀ σ : ℝ, HasCompactSupport (fun y : Euclid n => h (x - σ • y) * g (‖y‖ ^ 2)) := by
    intro σ
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid n) r) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    rw [hgz y hy.le, mul_zero]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun σ (y : Euclid n) => h (x - σ • y) * g (‖y‖ ^ 2))
    (F' := fun σ (y : Euclid n) => -(fderiv ℝ h (x - σ • y) y * g (‖y‖ ^ 2)))
    (x₀ := s) (bound := (closedBall (0 : Euclid n) r).indicator fun _ => A₁ * r * γ)
    (ball_mem_nhds s hδpos)
    (eventually_of_mem (ball_mem_nhds s hδpos) fun σ hσ =>
      (hFcont σ (hball' σ hσ)).aestronglyMeasurable)
    ((hFcont s hs).integrable_of_hasCompactSupport (hsupp s))
    hF'cont.aestronglyMeasurable
    -- domination: `|Dh(x − σy)(y) g(|y|²)| ≤ A₁ r γ` for `|y| ≤ r`, and `0` otherwise
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem (by rwa [mem_closedBall, dist_zero_right])]
        rw [norm_neg, norm_mul]
        have h1 : ‖fderiv ℝ h (x - σ • y) y‖ ≤ A₁ * r :=
          ((fderiv ℝ h (x - σ • y)).le_opNorm y).trans
            (mul_le_mul (hA₁ _ (hmemK σ hσ y hy)) hy (norm_nonneg _)
              ((norm_nonneg _).trans (hA₁ _ (hmemK σ hσ y hy))))
        exact mul_le_mul h1 (hgγ y) (norm_nonneg _) (by nlinarith [norm_nonneg (fderiv ℝ h (x - σ • y) y)])
      · rw [hgz y (le_of_not_ge hy), mul_zero, neg_zero, norm_zero]
        rw [indicator_of_notMem (by rwa [mem_closedBall, dist_zero_right])])
    ((integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne).integrable_indicator
      measurableSet_closedBall)
    -- pointwise derivative: the chain rule for `|y| < r`, the zero function for `|y| ≥ r`
    (Eventually.of_forall fun y σ hσ => by
      by_cases hy : ‖y‖ < r
      · have hd := (hdiff _ (hmemU σ (hball' σ hσ) y hy.le)).hasFDerivAt
        have hγ' : HasDerivAt (fun σ : ℝ => x - σ • y) (-y) σ := by
          simpa using (hasDerivAt_id σ).smul_const y |>.const_sub x
        have := (hd.comp_hasDerivAt σ hγ').mul_const (g (‖y‖ ^ 2))
        simpa [map_neg, neg_mul] using this
      · push Not at hy
        have h0 : (fun σ : ℝ => h (x - σ • y) * g (‖y‖ ^ 2)) = fun _ => 0 := by
          funext σ; rw [hgz y hy, mul_zero]
        rw [h0, hgz y hy, mul_zero, neg_zero]
        exact hasDerivAt_const σ 0)
  simpa [integral_neg] using key.2

/-- **Vanishing flux in the mean value property** (step 4 of the mean value proof, `M'(s) = 0`).
Let `h` be `C²` and harmonic on the open set `U ⊇ B̄_R(x)`, `0 < r < R`, `g` continuous with
`g(t) = 0` for `t ≥ r²`, and `0 < s ≤ 1`.  Take the radial potential `Ψ` (`spt Ψ ⊆ B̄_r(0)`,
`DΨ(y)v = g(|y|²) y · v`) and `G(z) = h(x − s z)`, `C²` on `B_R(0)`.  Green's identity gives
`∫ DΨ · DG = −∫ Ψ ΔG = 0`, since `ΔG(y) = s² Δh(x − s y) = 0` on `B_R(0)` and `Ψ = 0` off it;
as `DG(y) = −s Dh(x − s y)`, the left side is `−s ∫ Dh(x − s y)(y) g(|y|²) dy`. -/
theorem Submission.dorag_ha_mv_flux_zero : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ), IsOpen U → ContDiffOn ℝ 2 h U → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∀ (x : Euclid n) (r R : ℝ), 0 < r → r < R → closedBall x R ⊆ U → ∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∀ s : ℝ, 0 < s → s ≤ 1 → ∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2) = 0 := by
  intro n U h hU hh hΔ x r R hr hrR hRU g hg hgr s hs0 hs1
  -- the radial potential: `Ψ ∈ C¹_c`, `spt Ψ ⊆ B̄_r(0)`, `DΨ(y)v = g(|y|²) y · v`
  obtain ⟨Ψ, hΨC, hΨc, hΨsupp, hΨd⟩ := Submission.dorag_ha_mv_radial_potential n r g hr hg hgr
  -- `G(z) = h(x − s z)` is `C²` on `V = B_R(0)`, which `z ↦ x − s z` maps into `B̄_R(x) ⊆ U`
  set G : Euclid n → ℝ := fun z => h (x - s • z) with hG
  have hVmaps : ∀ z ∈ ball (0 : Euclid n) R, x - s • z ∈ U := by
    intro z hz
    apply hRU
    rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs0]
    rw [mem_ball, dist_zero_right] at hz
    nlinarith [norm_nonneg z]
  have hGC : ContDiffOn ℝ 2 G (ball (0 : Euclid n) R) := by
    have hA : ContDiff ℝ 2 (fun z : Euclid n => x - s • z) :=
      contDiff_const.sub (contDiff_id.const_smul s)
    exact hh.comp hA.contDiffOn (fun z hz => hVmaps z hz)
  have hsuppV : tsupport Ψ ⊆ ball (0 : Euclid n) R := hΨsupp.trans (closedBall_subset_ball hrR)
  -- Green's identity: `∫ Σᵢ DΨ eᵢ · DG eᵢ = −∫ Ψ ΔG`
  have hgreen := Submission.dorag_ha_mv_green_identity n (ball (0 : Euclid n) R) G Ψ isOpen_ball
    hGC hΨC hΨc hsuppV
  -- `Ψ ΔG = 0`: on `V`, `ΔG(z) = s² Δh(x − s z) = 0`; off `V`, `Ψ(z) = 0`
  have hRHS : ∀ z, Ψ z * ∑ i : Fin n, iteratedFDeriv ℝ 2 G z
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
    intro z
    by_cases hz : z ∈ ball (0 : Euclid n) R
    · have hsum : ∑ i : Fin n, iteratedFDeriv ℝ 2 G z
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
        simp_rw [hG, (Submission.dorag_ha_mv_affine_comp_deriv n h x s z _ _).2]
        rw [← Finset.mul_sum, hΔ _ (hVmaps z hz), mul_zero]
      rw [hsum, mul_zero]
    · have : Ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hz (hsuppV h'))
      rw [this, zero_mul]
  -- `Σᵢ (z · eᵢ) L eᵢ = L z` for linear `L`
  have hexp : ∀ (L : Euclid n →L[ℝ] ℝ) (z : Euclid n),
      ∑ i : Fin n, inner ℝ z (EuclideanSpace.single i (1 : ℝ)) * L (EuclideanSpace.single i 1) =
        L z := by
    intro L z
    conv_rhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [EuclideanSpace.inner_single_right, map_smul]
  -- `Σᵢ DΨ(z)eᵢ · DG(z)eᵢ = −s Dh(x − s z)(z) g(|z|²)`, as `DG(z) = −s Dh(x − s z)`
  have hLHS : ∀ z, ∑ i : Fin n, fderiv ℝ Ψ z (EuclideanSpace.single i (1 : ℝ)) *
      fderiv ℝ G z (EuclideanSpace.single i (1 : ℝ)) =
      -s * (fderiv ℝ h (x - s • z) z * g (‖z‖ ^ 2)) := by
    intro z
    have hGd : ∀ a, fderiv ℝ G z a = -(s * fderiv ℝ h (x - s • z) a) := fun a =>
      (Submission.dorag_ha_mv_affine_comp_deriv n h x s z a a).1
    simp_rw [hΨd, hGd]
    rw [← hexp (fderiv ℝ h (x - s • z)) z, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- so `−s ∫ Dh(x − s y)(y) g(|y|²) dy = 0`, and `s ≠ 0`
  simp_rw [hLHS, hRHS, integral_zero, neg_zero, integral_const_mul] at hgreen
  exact (mul_eq_zero.1 hgreen).resolve_left (neg_ne_zero.2 hs0.ne')
/-- **Ball mean value from the radial kernel identity.**  Let `r > 0`, let `h` be continuous on
`B̄_r(x)`, and suppose `∫ h(x - y) g(|y|²) dy = h(x) ∫ g(|y|²) dy` for every continuous `g`
vanishing on `[r², ∞)`.  Then `∫_{B_r(x)} h = |B_r(x)| h(x)`.  The proof applies the identity to
`g_k(t) = min{1, max{0, (k + 1)(r² - t)}}`, which tend pointwise to `1_{[0, r²)}`.  Dominated
convergence passes to the limit, with bounds `A₀ 1_{B̄_r(0)}` and `1_{B̄_r(0)}`.  The reflection
`y ↦ x - y` then turns `B_r(0)` into `B_r(x)`. -/
theorem Submission.dorag_ha_mv_ball_of_kernel : ∀ (n : ℕ) (h : Euclid n → ℝ) (x : Euclid n) (r : ℝ), 0 < r → ContinuousOn h (closedBall x r) → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) → ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x := by
  intro n h x r hr hhc hker
  -- the profiles `g_k`: continuous, `0 ≤ g_k ≤ 1`, zero on `[r², ∞)`
  set gk : ℕ → ℝ → ℝ := fun k t => min 1 (max 0 (((k : ℝ) + 1) * (r ^ 2 - t))) with hgk
  have gk_cont : ∀ k, Continuous (gk k) := fun k => by
    simp only [hgk]; fun_prop
  have gk_zero : ∀ k t, r ^ 2 ≤ t → gk k t = 0 := by
    intro k t ht
    simp only [hgk]
    have : ((k : ℝ) + 1) * (r ^ 2 - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    rw [max_eq_left this, min_eq_right zero_le_one]
  have gk_nonneg : ∀ k t, 0 ≤ gk k t := fun k t => le_min zero_le_one (le_max_left _ _)
  have gk_le : ∀ k t, gk k t ≤ 1 := fun k t => min_le_left _ _
  have gkz : ∀ k (y : Euclid n), r ≤ ‖y‖ → gk k (‖y‖ ^ 2) = 0 := fun k y hy =>
    gk_zero k _ (pow_le_pow_left₀ hr.le hy 2)
  have gk_cont' : ∀ k, Continuous fun y : Euclid n => gk k (‖y‖ ^ 2) := fun k =>
    (gk_cont k).comp (by fun_prop : Continuous fun y : Euclid n => ‖y‖ ^ 2)
  -- `g_k(|y|²) → 1_{B_r(0)}(y)`: eventually `1` inside the ball, always `0` outside
  have gk_lim : ∀ y : Euclid n, Tendsto (fun k => gk k (‖y‖ ^ 2)) atTop
      (𝓝 ((ball (0 : Euclid n) r).indicator 1 y)) := by
    intro y
    by_cases hy : ‖y‖ < r
    · rw [indicator_of_mem (by rwa [mem_ball, dist_zero_right]), Pi.one_apply]
      have hpos : 0 < r ^ 2 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
      obtain ⟨K, hK⟩ := exists_nat_ge (1 / (r ^ 2 - ‖y‖ ^ 2))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop K] with k hk
      simp only [hgk]
      have hKk : (K : ℝ) ≤ k := by exact_mod_cast hk
      rw [div_le_iff₀ hpos] at hK
      have : 1 ≤ ((k : ℝ) + 1) * (r ^ 2 - ‖y‖ ^ 2) := by nlinarith
      rw [max_eq_right (by linarith), min_eq_left this]
    · push Not at hy
      rw [indicator_of_notMem (by rwa [mem_ball, dist_zero_right, not_lt])]
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun k => (gkz k y hy).symm)
  -- `|h| ≤ A₀` on the compact ball `B̄_r(x)`, which contains `x - y` for `|y| ≤ r`
  obtain ⟨A₀, hA₀⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hhc
  have hmem : ∀ y : Euclid n, ‖y‖ ≤ r → x - y ∈ closedBall x r := by
    intro y hy; rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hy
  have hcb : ∀ y : Euclid n, y ∈ closedBall (0 : Euclid n) r ↔ ‖y‖ ≤ r := fun y => by
    rw [mem_closedBall, dist_zero_right]
  -- the integrands vanish off `B̄_r(0)` and are continuous on it
  have hF_meas : ∀ k,
      AEStronglyMeasurable (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) volume := by
    intro k
    have : (fun y : Euclid n => h (x - y) * gk k (‖y‖ ^ 2)) =
        (closedBall (0 : Euclid n) r).indicator (fun y => h (x - y) * gk k (‖y‖ ^ 2)) := by
      funext y
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy)]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero]
    rw [this, aestronglyMeasurable_indicator_iff measurableSet_closedBall]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_closedBall
    refine ContinuousOn.mul ?_ (gk_cont' k).continuousOn
    exact hhc.comp (by fun_prop : Continuous fun y : Euclid n => x - y).continuousOn
      (fun y hy => hmem y ((hcb y).1 hy))
  have hbint : ∀ c : ℝ, Integrable ((closedBall (0 : Euclid n) r).indicator fun _ => c) := fun c =>
    IntegrableOn.integrable_indicator
      (integrableOn_const (measure_closedBall_lt_top (x := (0 : Euclid n)) (r := r)).ne)
      measurableSet_closedBall
  -- dominated convergence for both sides of the kernel identity
  have lim1 : Tendsto (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => A₀) hF_meas (hbint A₀) ?_ ?_
    · intro k
      refine Eventually.of_forall fun y => ?_
      by_cases hy : ‖y‖ ≤ r
      · rw [indicator_of_mem ((hcb y).2 hy), norm_mul]
        have h1 := hA₀ _ (hmem y hy)
        have h2 : ‖gk k (‖y‖ ^ 2)‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]; exact gk_le _ _
        nlinarith [norm_nonneg (h (x - y)), norm_nonneg (gk k (‖y‖ ^ 2))]
      · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), mul_zero,
          norm_zero]
    · exact Eventually.of_forall fun y => (gk_lim y).const_mul (h (x - y))
  have lim2 : Tendsto (fun k => ∫ y : Euclid n, gk k (‖y‖ ^ 2)) atTop
      (𝓝 (∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y)) := by
    refine tendsto_integral_of_dominated_convergence
      ((closedBall (0 : Euclid n) r).indicator fun _ => 1)
      (fun k => (gk_cont' k).aestronglyMeasurable)
      (hbint 1) ?_ (Eventually.of_forall gk_lim)
    intro k
    refine Eventually.of_forall fun y => ?_
    by_cases hy : ‖y‖ ≤ r
    · rw [indicator_of_mem ((hcb y).2 hy), Real.norm_eq_abs, abs_of_nonneg (gk_nonneg _ _)]
      exact gk_le _ _
    · rw [indicator_of_notMem (fun h' => hy ((hcb y).1 h')), gkz k y (le_of_not_ge hy), norm_zero]
  -- the hypothesis identifies the two sequences, so the limits agree
  have heq : (fun k => ∫ y : Euclid n, h (x - y) * gk k (‖y‖ ^ 2)) =
      fun k => h x * ∫ y : Euclid n, gk k (‖y‖ ^ 2) :=
    funext fun k => hker (gk k) (gk_cont k) (gk_zero k)
  rw [heq] at lim1
  have hlim := tendsto_nhds_unique lim1 (lim2.const_mul (h x))
  -- left limit: the reflection `y ↦ x - y` preserves volume and maps `B_r(0)` onto `B_r(x)`
  have e1 : ∫ y : Euclid n, h (x - y) * (ball (0 : Euclid n) r).indicator 1 y =
      ∫ y in ball x r, h y := by
    have : (fun y : Euclid n => h (x - y) * (ball (0 : Euclid n) r).indicator 1 y) =
        (ball (0 : Euclid n) r).indicator (fun y => h (x - y)) := by
      funext y; by_cases hy : y ∈ ball (0 : Euclid n) r <;> simp [hy]
    rw [this, integral_indicator measurableSet_ball]
    have hmp : MeasurePreserving (fun y : Euclid n => x - y) volume volume :=
      Measure.measurePreserving_sub_left volume x
    have hpre : (fun y : Euclid n => x - y) ⁻¹' (ball x r) = ball 0 r := by
      ext y; simp [mem_ball, dist_eq_norm]
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb (MeasurableEquiv.subLeft x).measurableEmbedding h (ball x r)
  -- right limit: `∫ 1_{B_r(0)} = |B_r(0)| = |B_r(x)|` by translation invariance
  have e2 : ∫ y : Euclid n, (ball (0 : Euclid n) r).indicator 1 y = (volume (ball x r)).toReal := by
    rw [integral_indicator_one measurableSet_ball, Measure.addHaar_ball_center volume x r]
    rfl
  rw [← e1, hlim, e2, mul_comm]

/-- **Mean value property of harmonic functions** (Simon Ch. 5, 3.2–3.4; Evans, PDE, §2.2.2).
Let `h` be `C²` on the open set `U ⊇ B̄_r(x)`, `r > 0`, with `Σᵢ D²h(eᵢ, eᵢ) = 0` on `U`.  Then
(i) `∫ h(x - y) g(|y|²) dy = h(x) ∫ g(|y|²) dy` for every continuous `g` vanishing on `[r², ∞)`,
and (ii) `∫_{B_r(x)} h = |B_r(x)| h(x)`.  For (i), choose `η > 0` with `B̄_{η + r}(x) ⊆ U`.  Then
`M(σ) = ∫ h(x - σy) g(|y|²) dy` has derivative `M'(s) = -∫ Dh(x - sy)(y) g(|y|²) dy` for
`s ∈ [0, 1]`, and `M'` vanishes on `(0, 1)` (zero flux).  The mean value theorem gives
`M(1) = M(0) = h(x) ∫ g(|y|²) dy`.  Part (ii) follows from (i) by approximating `1_{[0, r²)}`. -/
theorem Submission.dorag_ha_mean_value : ∀ (n : ℕ) (U : Set (Euclid n)) (h : Euclid n → ℝ), 0 < n → IsOpen U → ContDiffOn ℝ 2 h U → (∀ y ∈ U, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∀ (x : Euclid n) (r : ℝ), 0 < r → closedBall x r ⊆ U → (∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) → ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2)) ∧ ∫ y in ball x r, h y = (volume (ball x r)).toReal * h x := by
  intro n U h _hn hU hh hΔ x r hr hxr
  -- room around the ball: `B̄_{η + r}(x) ⊆ U` for some `η > 0`
  obtain ⟨η, hη, hηU⟩ := (isCompact_closedBall x r).exists_cthickening_subset_open hU hxr
  rw [cthickening_closedBall hη.le hr.le] at hηU
  have hrR : r < η + r := by linarith
  -- (i): `M(σ) = ∫ h(x - σy) g(|y|²) dy` is constant on `[0, 1]`
  have hker : ∀ g : ℝ → ℝ, Continuous g → (∀ t : ℝ, r ^ 2 ≤ t → g t = 0) →
      ∫ y : Euclid n, h (x - y) * g (‖y‖ ^ 2) = h x * ∫ y : Euclid n, g (‖y‖ ^ 2) := by
    intro g hg hgr
    set M : ℝ → ℝ := fun σ => ∫ y : Euclid n, h (x - σ • y) * g (‖y‖ ^ 2) with hM
    set M' : ℝ → ℝ := fun s => -∫ y : Euclid n, fderiv ℝ h (x - s • y) y * g (‖y‖ ^ 2)
      with hM'
    -- differentiation under the integral sign, valid while `|s| r < η + r`
    have hderiv : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt M (M' s) s := by
      intro s hs
      refine Submission.dorag_ha_mv_deriv_under_integral n U h x r (η + r) g hU
        (hh.of_le (by norm_num)) hηU hr hg hgr s ?_
      rw [abs_of_nonneg hs.1]
      nlinarith [hs.2]
    -- zero flux: `M' = 0` on `(0, 1)`
    have hzero : ∀ s ∈ Ioo (0 : ℝ) 1, M' s = 0 := by
      intro s hs
      simp only [hM']
      rw [Submission.dorag_ha_mv_flux_zero n U h hU hh hΔ x r (η + r) hr hrR hηU g hg hgr s hs.1
        hs.2.le, neg_zero]
    -- the mean value theorem on `[0, 1]` gives `M(1) = M(0)`
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope M M' (by norm_num : (0 : ℝ) < 1)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => hderiv s (Ioo_subset_Icc_self hs))
    rw [hzero c hc, sub_zero, div_one, eq_comm, sub_eq_zero] at hc'
    simp only [hM, one_smul, zero_smul, sub_zero] at hc'
    rw [hc', integral_const_mul]
  -- (ii): the ball average, from the kernel identity (i)
  exact ⟨hker, Submission.dorag_ha_mv_ball_of_kernel n h x r hr (hh.continuousOn.mono hxr) hker⟩

/-- **Weyl's lemma** (used without proof in Simon Ch. 5, Lemma 3.1: "thus `w` is harmonic in
`B`").  If `W` is integrable on `B = B̆_R(0)` and weakly harmonic there (`∫_B W Δζ = 0` for every
`C²` function `ζ` with compact support in `B`), then `W` agrees a.e. on `B` with a function `h`
that is `C^m` on `B` for every `m` and harmonic in `B`.  Mollify `W̃ = 1_B W` with the radial
kernels `φ_ε(y) = g_ε(|y|²)`: `F_ε = φ_ε ⋆ W̃` is smooth and harmonic on `B̆_{R−ε}(0)`, the mean
value property and `φ_ε ⋆ φ_δ = φ_δ ⋆ φ_ε` give `F_ε = F_δ` on `B̆_{R−ε−δ}(0)`, the `F_ε` patch to
`h`, and `F_ε → W̃` a.e. by Lebesgue differentiation. -/
theorem Submission.dorag_ha_weyl_lemma : ∀ (n : ℕ) (R : ℝ) (W : Euclid n → ℝ), 0 < n → 0 < R → IntegrableOn W (ball (0 : Euclid n) R) → (∀ ζ : Euclid n → ℝ, ContDiff ℝ 2 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid n) R → ∫ y in ball (0 : Euclid n) R, W y * ∑ i : Fin n, iteratedFDeriv ℝ 2 ζ y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → ∃ h : Euclid n → ℝ, (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) ∧ (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid n) R)), h y = W y := by
  intro n R W hn hR hW hweak
  -- the radial mollifiers `φ_ε(y) = g ε (|y|²)`: smooth, `spt φ_ε ⊆ B̄_ε(0)`, `∫ φ_ε = 1`
  obtain ⟨C, g, hg⟩ := Submission.dorag_ha_weyl_radial_mollifier n hn
  have hφ0 : ∀ ε : ℝ, 0 < ε → ∀ y : Euclid n, ε ≤ ‖y‖ → g ε (‖y‖ ^ 2) = 0 := fun ε hε y hy =>
    (hg ε hε).2.1 _ (pow_le_pow_left₀ hε.le hy 2)
  have hφc : ∀ ε : ℝ, 0 < ε → Continuous fun y : Euclid n => g ε (‖y‖ ^ 2) := fun ε hε =>
    ((hg ε hε).2.2.2.1 0).continuous
  have hφs : ∀ ε : ℝ, 0 < ε → HasCompactSupport fun y : Euclid n => g ε (‖y‖ ^ 2) :=
    fun ε hε => HasCompactSupport.intro (isCompact_closedBall 0 ε) fun y hy =>
      hφ0 ε hε y (not_le.1 (mt mem_closedBall_zero_iff.2 hy)).le
  -- the mollifications `F ε = φ_ε ⋆ W̃` of `W̃ = 1_B W ∈ L¹(ℝⁿ)`
  have hWt : Integrable ((ball (0 : Euclid n) R).indicator W) :=
    hW.integrable_indicator measurableSet_ball
  set F : ℝ → Euclid n → ℝ :=
    fun ε x => ∫ y, (ball (0 : Euclid n) R).indicator W y * g ε (‖x - y‖ ^ 2)
  -- `F ε` is smooth, and harmonic on `B̆_{R−ε}(0)`
  have hmoll : ∀ ε : ℝ, 0 < ε → (∀ m : ℕ, ContDiff ℝ m (F ε)) ∧
      ∀ x ∈ ball (0 : Euclid n) (R - ε), ∑ i : Fin n, iteratedFDeriv ℝ 2 (F ε) x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := fun ε hε =>
    Submission.dorag_ha_weyl_mollify_harmonic n R ε W (fun y => g ε (‖y‖ ^ 2)) hε hW hweak
      (hg ε hε).2.2.2.1 (hφ0 ε hε)
  -- mean value property of the harmonic `F a`: `∫ F a (x − z) φ_b(z) dz = F a x`
  have hmv : ∀ a b : ℝ, 0 < a → 0 < b → ∀ x : Euclid n, ‖x‖ + a + b < R →
      ∫ z, F a (x - z) * g b (‖z‖ ^ 2) = F a x := by
    intro a b ha hb x hx
    have hsub : closedBall x b ⊆ ball (0 : Euclid n) (R - a) :=
      closedBall_subset_ball' (by rw [dist_zero_right]; linarith)
    rw [(Submission.dorag_ha_mean_value n _ (F a) hn isOpen_ball ((hmoll a ha).1 2).contDiffOn
      (hmoll a ha).2 x b hb hsub).1 (g b) (hg b hb).1 (hg b hb).2.1, (hg b hb).2.2.2.2, mul_one]
  -- hence `F ε = F δ` on `B̆_{R−ε−δ}(0)`, since `(F ε ⋆ φ_δ)(x)` is symmetric in `ε, δ`
  have hcons : ∀ (ε δ : ℝ) (x : Euclid n), 0 < ε → 0 < δ → ‖x‖ + ε + δ < R → F ε x = F δ x := by
    intro ε δ x hε hδ hx
    rw [← hmv ε δ hε hδ x hx, ← hmv δ ε hδ hε x (by linarith)]
    exact Submission.dorag_ha_weyl_conv_swap n ((ball (0 : Euclid n) R).indicator W)
      (fun y => g ε (‖y‖ ^ 2)) (fun y => g δ (‖y‖ ^ 2)) x hWt (hφc ε hε) (hφs ε hε) (hφc δ hδ)
      (hφs δ hδ)
  -- patch the `F ε` into `h`
  obtain ⟨h, hh, hΔh, hFh⟩ := Submission.dorag_ha_weyl_glue n R F hR
    (fun ε hε _ m => ((hmoll ε hε).1 m).contDiffOn) (fun ε hε _ => (hmoll ε hε).2) hcons
  refine ⟨h, hh, hΔh, ?_⟩
  -- `F ε → W̃` a.e. (Lebesgue differentiation), and on `B` also `F ε x = h x` for small `ε`
  have hlim := Submission.dorag_ha_weyl_ae_tendsto n _ C (fun ε y => g ε (‖y‖ ^ 2)) hn hWt hφc
    hφ0 (fun ε hε y => (hg ε hε).2.2.1 _) fun ε hε => (hg ε hε).2.2.2.2
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hlim] with x hx hxB
  have hxh : Tendsto (fun ε => F ε x) (𝓝[>] 0) (𝓝 (h x)) :=
    tendsto_const_nhds.congr' ((hFh x hxB).mono fun ε hε => hε.symm)
  rw [tendsto_nhds_unique hxh hx, indicator_of_mem hxB]

/-- **Harmonic replacement with energy bound** (the harmonic comparison step of Campanato's approach
to Schauder estimates, Giaquinta–Martinazzi, *An Introduction to the Regularity Theory for Elliptic
Systems*, §5.4.1; used for the smooth regularity of codimension one hypercones).  Let `w` be `C¹`
and `F` continuous on `B_{R'}(x₀)`, `R < R'`, with `Δw = div F` weakly in `B = B_R(x₀)`.  Then
there is `h`, `C^n` and harmonic in `B`, with `∫_B |Dw - Dh|² ≤ ∫_B |F - c|²` for every constant
`c`.  In `H = L²(B; ℝᵏ)ᵐ` let `z` be the projection of `Dw` onto the closure of
`{Dζ : ζ ∈ C¹_c(B)}`; `Dw - DF` and the constants are orthogonal to it, so `z` is also the
projection of `DF - c` and `‖z‖ ≤ ‖F - c‖`.  By Poincaré's inequality `ζₙ → ψ` in `L²(B)` when
`Dζₙ → z`; `w - ψ` is weakly harmonic, hence equals a smooth harmonic `h` a.e. (Weyl's lemma,
componentwise), and `Dw - Dh = z` a.e. (fundamental lemma of the calculus of variations). -/
theorem Submission.codim1_hcp_sr_harmonic_replacement : ∀ (m k : ℕ), 1 ≤ m → ∀ (x₀ : Euclid m) (R R' : ℝ) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), 0 < R → R < R' → ContDiffOn ℝ 1 w (ball x₀ R') → ContinuousOn F (ball x₀ R') → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → ∃ h : Euclid m → Euclid k, (∀ n : ℕ, ContDiffOn ℝ n h (ball x₀ R)) ∧ (∀ x ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2 h x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧ IntegrableOn (fun x => ∑ j : Fin m, ‖(fderiv ℝ w x - fderiv ℝ h x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) ∧ ∀ c : Euclid m →L[ℝ] Euclid k, ∫ x in ball x₀ R, ∑ j : Fin m, ‖(fderiv ℝ w x - fderiv ℝ h x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ ∫ x in ball x₀ R, ∑ j : Fin m, ‖(F x - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  intro m k hm x₀ R R' w F hR hRR' hw hF hweak
  -- Step 0: `B = B_R(x₀)` and `μ = 𝓛ᵐ⌞B`, a finite measure
  set μ : Measure (Euclid m) := volume.restrict (ball x₀ R) with hμ
  have hfin : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hBB' : ball x₀ R ⊆ ball x₀ R' := ball_subset_ball hRR'.le
  have hcB' : closedBall x₀ R ⊆ ball x₀ R' := closedBall_subset_ball hRR'
  /- Step 1: the Hilbert space `H₀ = L²(B; ℝᵏ)`, with `⟨f, g⟩ = ∫_B f·g`, and the gradient space
  `H = H₀ᵐ` (`PiLp 2`), with `⟨u, v⟩ = Σⱼ ⟨uⱼ, vⱼ⟩` -/
  have hsq : ∀ f : Euclid m → Euclid k, MemLp f 2 μ → Integrable (fun x => ‖f x‖ ^ 2) μ := by
    intro f hf
    simpa using hf.integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
  have hinner : ∀ f g : Euclid m → Euclid k, MemLp f 2 μ → MemLp g 2 μ →
      Integrable (fun x => inner ℝ (f x) (g x)) μ := by
    intro f g hf hg
    refine Integrable.mono' ((hsq f hf).add (hsq g hg))
      (continuous_inner.comp_aestronglyMeasurable₂ hf.aestronglyMeasurable
        hg.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have h1 := norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)
    have h2 := two_mul_le_add_sq ‖f x‖ ‖g x‖
    have h3 := mul_nonneg (norm_nonneg (f x)) (norm_nonneg (g x))
    simp only [Pi.add_apply]
    linarith only [h1, h2, h3]
  have hnorm : ∀ f : Lp (Euclid k) 2 μ, ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    intro f
    rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofReal (by positivity)]
    have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_inv_natCast_pow (integral_nonneg fun x => by positivity) two_ne_zero]
    simp
  let ip : InnerProductSpace ℝ (Lp (Euclid k) 2 μ) :=
    { inner := fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ
      norm_sq_eq_re_inner := fun f => by
        simp only [RCLike.re_to_real, real_inner_self_eq_norm_sq]
        exact hnorm f
      conj_inner_symm := fun f g => by
        simp only [conj_trivial]
        exact integral_congr_ae (ae_of_all _ fun x => real_inner_comm _ _)
      add_left := fun f g h => by
        rw [← integral_add (hinner _ _ (Lp.memLp f) (Lp.memLp h))
          (hinner _ _ (Lp.memLp g) (Lp.memLp h))]
        refine integral_congr_ae ((Lp.coeFn_add f g).mono fun x hx => ?_)
        simp only [hx, Pi.add_apply, inner_add_left]
      smul_left := fun f g r => by
        simp only [conj_trivial]
        rw [← integral_const_mul]
        refine integral_congr_ae ((Lp.coeFn_smul r f).mono fun x hx => ?_)
        simp only [hx, Pi.smul_apply, real_inner_smul_left] }
  have hip : ∀ f g : Lp (Euclid k) 2 μ, inner ℝ f g = ∫ x, inner ℝ (f x) (g x) ∂μ :=
    fun f g => rfl
  obtain ⟨toH₀, htoH₀⟩ : ∃ T : (Euclid m → Euclid k) → Lp (Euclid k) 2 μ,
      ∀ f (hf : MemLp f 2 μ), T f = hf.toLp f := by
    classical
    exact ⟨fun f => if hf : MemLp f 2 μ then hf.toLp f else 0, fun f hf => by simp [hf]⟩
  set H := PiLp 2 (fun _ : Fin m => Lp (Euclid k) 2 μ) with hH
  let toH : (Fin m → Euclid m → Euclid k) → H := fun u => WithLp.toLp 2 fun j => toH₀ (u j)
  have hcoe : ∀ f, MemLp f 2 μ → toH₀ f =ᵐ[μ] f := fun f hf => by
    rw [htoH₀ f hf]
    exact hf.coeFn_toLp
  have hsub0 : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → toH₀ (f - g) = toH₀ f - toH₀ g :=
    fun f g hf hg => by rw [htoH₀ _ (hf.sub hg), htoH₀ f hf, htoH₀ g hg, MemLp.toLp_sub]
  have hadd0 : ∀ f g, MemLp f 2 μ → MemLp g 2 μ → toH₀ (f + g) = toH₀ f + toH₀ g :=
    fun f g hf hg => by rw [htoH₀ _ (hf.add hg), htoH₀ f hf, htoH₀ g hg, MemLp.toLp_add]
  have hsmul0 : ∀ (c : ℝ) f, MemLp f 2 μ → toH₀ (c • f) = c • toH₀ f :=
    fun c f hf => by rw [htoH₀ _ (hf.const_smul c), htoH₀ f hf, MemLp.toLp_const_smul]
  have hzero0 : toH₀ 0 = 0 := by rw [htoH₀ 0 MemLp.zero, MemLp.toLp_zero]
  have hip0 : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
      inner ℝ (toH₀ f) (toH₀ g) = ∫ x, inner ℝ (f x) (g x) ∂μ := fun f g hf hg => by
    rw [hip]
    refine integral_congr_ae ?_
    filter_upwards [hcoe f hf, hcoe g hg] with x h1 h2
    rw [h1, h2]
  have hnorm0 : ∀ f, MemLp f 2 μ → ‖toH₀ f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := fun f hf => by
    rw [hnorm]
    refine integral_congr_ae ?_
    filter_upwards [hcoe f hf] with x h1
    rw [h1]
  have hipH : ∀ u v : Fin m → Euclid m → Euclid k, (∀ j, MemLp (u j) 2 μ) →
      (∀ j, MemLp (v j) 2 μ) →
      inner ℝ (toH u) (toH v) = ∫ x, ∑ j, inner ℝ (u j x) (v j x) ∂μ := fun u v hu hv => by
    rw [PiLp.inner_apply, integral_finsetSum _ fun j _ => hinner _ _ (hu j) (hv j)]
    exact Finset.sum_congr rfl fun j _ => hip0 _ _ (hu j) (hv j)
  have hnormH : ∀ u : Fin m → Euclid m → Euclid k, (∀ j, MemLp (u j) 2 μ) →
      ‖toH u‖ ^ 2 = ∫ x, ∑ j, ‖u j x‖ ^ 2 ∂μ := fun u hu => by
    rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun j _ => hsq _ (hu j)]
    exact Finset.sum_congr rfl fun j _ => hnorm0 _ (hu j)
  have hsubH : ∀ u v : Fin m → Euclid m → Euclid k, (∀ j, MemLp (u j) 2 μ) →
      (∀ j, MemLp (v j) 2 μ) → toH (u - v) = toH u - toH v := fun u v hu hv => by
    ext j : 1
    exact hsub0 _ _ (hu j) (hv j)
  have haddH : ∀ u v : Fin m → Euclid m → Euclid k, (∀ j, MemLp (u j) 2 μ) →
      (∀ j, MemLp (v j) 2 μ) → toH (u + v) = toH u + toH v := fun u v hu hv => by
    ext j : 1
    exact hadd0 _ _ (hu j) (hv j)
  have hsmulH : ∀ (c : ℝ) (u : Fin m → Euclid m → Euclid k), (∀ j, MemLp (u j) 2 μ) →
      toH (c • u) = c • toH u := fun c u hu => by
    ext j : 1
    exact hsmul0 c _ (hu j)
  have hzeroH : toH 0 = 0 := by
    ext j : 1
    exact hzero0
  -- functions continuous on `B̄` are in `L²(B)`
  have hML : ∀ f : Euclid m → Euclid k, ContinuousOn f (closedBall x₀ R) → MemLp f 2 μ := by
    intro f hf
    obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn hf
    exact MemLp.of_bound ((hf.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball)
      C (ae_restrict_of_forall_mem measurableSet_ball fun x hx => hC x (ball_subset_closedBall hx))
  /- Step 2: calculus.  A function continuous on an open `U` and vanishing off a compact `K ⊆ U` is
  integrable; `∫ ∂ⱼg = 0` for `g ∈ C¹_c` (Green's identity with the linear `G = ⟨eⱼ, ·⟩`); and
  integration by parts `∫ ⟨∂ⱼΦ, f⟩ = -∫ ⟨Φ, ∂ⱼf⟩` for `Φ ∈ C¹_c(U)`, `f ∈ C¹(U)`. -/
  have hint : ∀ (U K : Set (Euclid m)) (q : Euclid m → ℝ), IsCompact K → K ⊆ U →
      ContinuousOn q U → (∀ x, x ∉ K → q x = 0) → Integrable q := by
    intro U K q hK hKU hq hq0
    rw [← integrableOn_iff_integrable_of_support_subset (s := K) fun x hx => by
      by_contra h
      exact hx (hq0 x h)]
    exact (hq.mono hKU).integrableOn_compact hK
  have hZ : ∀ (g : Euclid m → ℝ), ContDiff ℝ 1 g → HasCompactSupport g → ∀ j : Fin m,
      ∫ x, fderiv ℝ g x (EuclideanSpace.single j (1 : ℝ)) = 0 := by
    intro g hg hgc j
    obtain ⟨L, hL⟩ : ∃ L : Euclid m →L[ℝ] ℝ, L = innerSL ℝ (EuclideanSpace.single j (1 : ℝ)) :=
      ⟨_, rfl⟩
    have hG := Submission.dorag_ha_mv_green_identity m univ (⇑L) g isOpen_univ
      L.contDiff.contDiffOn hg hgc (subset_univ _)
    have hD : fderiv ℝ (⇑L) = fun _ => L := funext fun _ => L.fderiv
    have h1 : ∀ i : Fin m, L (EuclideanSpace.single i (1 : ℝ)) = if j = i then 1 else 0 :=
        fun i => by
      rw [hL, innerSL_apply_apply, EuclideanSpace.inner_single_left, PiLp.single_apply, map_one,
        one_mul]
    simp only [hD, iteratedFDeriv_two_apply, h1, fderiv_fun_const, Pi.zero_apply, zero_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Finset.sum_const_zero, integral_zero, neg_zero] at hG
    exact hG
  have hIBP : ∀ (U : Set (Euclid m)) (f Φ : Euclid m → Euclid k), IsOpen U → ContDiffOn ℝ 1 f U →
      ContDiff ℝ 1 Φ → HasCompactSupport Φ → tsupport Φ ⊆ U → ∀ j : Fin m,
      ∫ x, inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single j (1 : ℝ))) (f x) =
        -∫ x, inner ℝ (Φ x) (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) := by
    intro U f Φ hU hf hΦ hΦc hΦU j
    have hΦ0 : ∀ x, x ∉ tsupport Φ → Φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hdΦ0 : ∀ x, x ∉ tsupport Φ → fderiv ℝ Φ x = 0 := fun x hx => by
      by_contra h'
      exact hx (support_fderiv_subset ℝ h')
    have hg0 : ∀ x, x ∉ tsupport Φ → (fun x => inner ℝ (Φ x) (f x)) =ᶠ[𝓝 x] fun _ => 0 :=
      fun x hx => by
        filter_upwards [(isClosed_tsupport Φ).isOpen_compl.mem_nhds hx] with y hy
        rw [hΦ0 y hy, inner_zero_left]
    -- the product `g = ⟨Φ, f⟩` is `C¹` with compact support, `∂ⱼg = ⟨∂ⱼΦ, f⟩ + ⟨Φ, ∂ⱼf⟩`
    have hgd : ∀ x, fderiv ℝ (fun x => inner ℝ (Φ x) (f x)) x (EuclideanSpace.single j (1 : ℝ)) =
        inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single j (1 : ℝ))) (f x) +
          inner ℝ (Φ x) (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) := by
      intro x
      by_cases hx : x ∈ U
      · rw [((hΦ.differentiable one_ne_zero x).hasFDerivAt.inner ℝ
          ((hf.differentiableOn one_ne_zero x hx).differentiableAt
            (hU.mem_nhds hx)).hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, add_comm]
      · have hx' : x ∉ tsupport Φ := fun h => hx (hΦU h)
        rw [(hg0 x hx').fderiv_eq, hΦ0 x hx', hdΦ0 x hx', fderiv_fun_const, Pi.zero_apply,
          zero_apply, zero_apply, inner_zero_left, inner_zero_left, add_zero]
    have hgC : ContDiff ℝ 1 fun x => inner ℝ (Φ x) (f x) := by
      rw [contDiff_iff_contDiffAt]
      intro x
      by_cases hx : x ∈ U
      · exact hΦ.contDiffAt.inner ℝ (hf.contDiffAt (hU.mem_nhds hx))
      · exact contDiffAt_const.congr_of_eventuallyEq (hg0 x fun h => hx (hΦU h))
    have hgc : HasCompactSupport fun x => inner ℝ (Φ x) (f x) := hΦc.mono' fun x hx => by
      by_contra h
      exact hx (by simp only [hΦ0 x h, inner_zero_left])
    have hA := hint U _ (fun x => inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single j (1 : ℝ))) (f x))
      hΦc hΦU (((hΦ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn.inner
        hf.continuousOn) fun x hx => by rw [hdΦ0 x hx, zero_apply, inner_zero_left]
    have hB := hint U _ (fun x => inner ℝ (Φ x) (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))))
      hΦc hΦU (hΦ.continuous.continuousOn.inner
        ((hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)) fun x hx => by
        rw [hΦ0 x hx, inner_zero_left]
    have h0 := hZ _ hgC hgc j
    rw [integral_congr_ae (ae_of_all _ hgd), integral_add hA hB] at h0
    exact eq_neg_of_add_eq_zero_left h0
  -- the same identity with both integrals over `B`, when `spt Φ ⊆ B ⊆ U`
  have hIBPB : ∀ (U : Set (Euclid m)) (f Φ : Euclid m → Euclid k), IsOpen U → ball x₀ R ⊆ U →
      ContDiffOn ℝ 1 f U → ContDiff ℝ 1 Φ → HasCompactSupport Φ → tsupport Φ ⊆ ball x₀ R →
      ∀ j : Fin m, ∫ x, inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single j (1 : ℝ))) (f x) ∂μ =
        -∫ x, inner ℝ (Φ x) (fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ∂μ := by
    intro U f Φ hU hBU hf hΦ hΦc hΦB j
    have hΦ0 : ∀ x, x ∉ tsupport Φ → Φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
    have hdΦ0 : ∀ x, x ∉ tsupport Φ → fderiv ℝ Φ x = 0 := fun x hx => by
      by_contra h'
      exact hx (support_fderiv_subset ℝ h')
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [hdΦ0 x fun h => hx (hΦB h)],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [hΦ0 x fun h => hx (hΦB h)]]
    exact hIBP U f Φ hU hf hΦ hΦc (hΦB.trans hBU) j
  -- Step 3: Poincaré inequality `∫_B |ζ|² ≤ 4R² ∫_B |Dζ|²` for `ζ ∈ C¹_c(B)`
  have hpoinc : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
      tsupport ζ ⊆ ball x₀ R → ∫ x, ‖ζ x‖ ^ 2 ∂μ ≤
        4 * R ^ 2 * ∫ x, ∑ j : Fin m, ‖fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ∂μ := by
    intro ζ hζ hζc hζB
    -- one direction `e = e_{j₀}` suffices; `c(y) = ⟨e, y - x₀⟩` has `|c| < R` on `B`
    have j₀ : Fin m := ⟨0, hm⟩
    have hcd : ∀ y, HasFDerivAt (fun y => inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀))
        ((innerSL ℝ (EuclideanSpace.single j₀ (1 : ℝ))).comp (ContinuousLinearMap.id ℝ _)) y :=
      fun y => (innerSL ℝ _).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)
    have hdζ : ∀ y, HasFDerivAt ζ (fderiv ℝ ζ y) y := fun y =>
      (hζ.differentiable one_ne_zero y).hasFDerivAt
    -- `∂ₑ(c ζ) = c ∂ₑζ + ζ`
    have hfd : ∀ y, fderiv ℝ (fun y => inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀) • ζ y) y
        (EuclideanSpace.single j₀ (1 : ℝ)) = inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀) •
          fderiv ℝ ζ y (EuclideanSpace.single j₀ (1 : ℝ)) + ζ y := fun y => by
      have h : HasFDerivAt
          (fun y => inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀) • ζ y) _ y :=
        (hcd y).smul (hdζ y)
      rw [h.fderiv]
      simp [EuclideanSpace.inner_single_left]
    have hfC : ContDiff ℝ 1 fun y => inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀) • ζ y :=
      (contDiff_const.inner ℝ (contDiff_id.sub contDiff_const)).smul hζ
    have hI := hIBPB univ _ ζ isOpen_univ (subset_univ _) hfC.contDiffOn hζ hζc hζB j₀
    simp only [hfd] at hI
    -- the pointwise bound `|ζ|²/2 ≤ ⟨∂ζ, cζ⟩ + ⟨ζ, c∂ζ + ζ⟩ + 2R²|∂ζ|²` on `B`
    have hcont : Continuous fun y => inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (y - x₀) :=
      continuous_const.inner (continuous_id.sub continuous_const)
    have hdc : Continuous fun y => fderiv ℝ ζ y (EuclideanSpace.single j₀ (1 : ℝ)) :=
      (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hM1 := hML _ hζ.continuous.continuousOn
    have hM2 := hML _ hdc.continuousOn
    have hA : Integrable (fun x => inner ℝ (fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)))
        (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) • ζ x)) μ :=
      hinner _ _ hM2 (hML _ (hcont.smul hζ.continuous).continuousOn)
    have hB : Integrable (fun x => inner ℝ (ζ x)
        (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) •
          fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)) + ζ x)) μ :=
      hinner _ _ hM1 (hML _ ((hcont.smul hdc).add hζ.continuous).continuousOn)
    have hS : Integrable (fun x => ∑ j : Fin m,
        ‖fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) μ :=
      integrable_finsetSum _ fun j _ => hsq _ (hML _ ((hζ.continuous_fderiv one_ne_zero).clm_apply
        continuous_const).continuousOn)
    have hpt : ∀ᵐ x ∂μ, ‖ζ x‖ ^ 2 / 2 ≤
        (inner ℝ (fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)))
          (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) • ζ x) +
        inner ℝ (ζ x) (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) •
          fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)) + ζ x)) +
        2 * R ^ 2 * ‖fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ))‖ ^ 2 := by
      rw [hμ]
      refine ae_restrict_of_forall_mem measurableSet_ball fun x hx => ?_
      have hc : |inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀)| ≤ R :=
        (abs_real_inner_le_norm _ _).trans (by
          rw [PiLp.norm_single, norm_one, one_mul, ← dist_eq_norm]
          exact (mem_ball.1 hx).le)
      have hp := abs_real_inner_le_norm (ζ x) (fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)))
      have h1 := (abs_le.1 ((abs_mul _ _).trans_le (mul_le_mul hc hp (abs_nonneg _) hR.le))).1
      rw [real_inner_smul_right, inner_add_right, real_inner_smul_right,
        real_inner_comm (ζ x), real_inner_self_eq_norm_sq]
      linear_combination (1 / 2 : ℝ) * sq_nonneg (‖ζ x‖ - 2 * R *
        ‖fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ))‖) + 2 * h1
    have hAB : Integrable (fun x => inner ℝ (fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)))
          (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) • ζ x) +
        inner ℝ (ζ x) (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) •
          fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)) + ζ x)) μ := hA.add hB
    have hC : Integrable (fun x => 2 * R ^ 2 *
        ‖fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ))‖ ^ 2) μ := (hsq _ hM2).const_mul _
    have hmono : ∫ x, ‖ζ x‖ ^ 2 / 2 ∂μ ≤
        ∫ x, ((inner ℝ (fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)))
          (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) • ζ x) +
        inner ℝ (ζ x) (inner ℝ (EuclideanSpace.single j₀ (1 : ℝ)) (x - x₀) •
          fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ)) + ζ x)) +
        2 * R ^ 2 * ‖fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ))‖ ^ 2) ∂μ :=
      integral_mono_ae ((hsq _ hM1).div_const 2) (hAB.add hC) hpt
    rw [integral_div, integral_add hAB hC, integral_add hA hB, hI, integral_const_mul] at hmono
    have hj : ∫ x, ‖fderiv ℝ ζ x (EuclideanSpace.single j₀ (1 : ℝ))‖ ^ 2 ∂μ ≤
        ∫ x, ∑ j : Fin m, ‖fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ∂μ :=
      integral_mono (hsq _ hM2) hS fun x => Finset.single_le_sum
        (f := fun j => ‖fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ j₀)
    nlinarith only [hmono, hj, sq_nonneg R]
  /- Step 4: the subspace `S = {Dζ : ζ ∈ C¹_c(B)}` of `H`, its closure `K`, and `z = Π_K Dw`.
  Since `Dw - DF ⊥ S` (the weak equation) and constants are `⊥ S`, `z = Π_K (DF - c)`. -/
  have hDwc : ∀ j : Fin m, ContinuousOn (fun x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ)))
      (ball x₀ R') :=
    fun j => (hw.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
  have hMw : MemLp w 2 μ := hML w (hw.continuousOn.mono hcB')
  have hMDw : ∀ j : Fin m, MemLp (fun x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) 2 μ :=
    fun j => hML _ ((hDwc j).mono hcB')
  have hMF : ∀ j : Fin m, MemLp (fun x => F x (EuclideanSpace.single j (1 : ℝ))) 2 μ :=
    fun j => hML _ ((hF.clm_apply continuousOn_const).mono hcB')
  have hMζ : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → MemLp ζ 2 μ ∧
      ∀ j : Fin m, MemLp (fun x => fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) 2 μ :=
    fun ζ hζ => ⟨hML _ hζ.continuous.continuousOn, fun j => hML _
      ((hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn⟩
  let S : Submodule ℝ H :=
    { carrier := {u | ∃ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧
        tsupport ζ ⊆ ball x₀ R ∧ u = toH fun j x => fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))}
      add_mem' := by
        rintro _ _ ⟨ζ₁, h1, hc1, hs1, rfl⟩ ⟨ζ₂, h2, hc2, hs2, rfl⟩
        refine ⟨ζ₁ + ζ₂, h1.add h2, hc1.add hc2,
          (tsupport_add _ _).trans (union_subset hs1 hs2), ?_⟩
        rw [← haddH _ _ (hMζ ζ₁ h1).2 (hMζ ζ₂ h2).2]
        congr 1
        funext j x
        rw [fderiv_add (h1.differentiable one_ne_zero x) (h2.differentiable one_ne_zero x)]
        rfl
      zero_mem' := ⟨0, contDiff_const, HasCompactSupport.zero, by simp, by
        rw [← hzeroH]
        congr 1
        funext j x
        simp⟩
      smul_mem' := by
        rintro c _ ⟨ζ, h1, hc1, hs1, rfl⟩
        refine ⟨c • ζ, h1.const_smul c, hc1.smul_left (f := fun _ => c),
          (tsupport_smul_subset_right (fun _ => c) ζ).trans hs1, ?_⟩
        rw [← hsmulH c _ (hMζ ζ h1).2]
        congr 1
        funext j x
        rw [fderiv_const_smul (h1.differentiable one_ne_zero x)]
        rfl }
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℝ H, K = S.topologicalClosure := ⟨_, rfl⟩
  have hKc : CompleteSpace K := by
    rw [hK]
    exact completeSpace_coe_iff_isComplete.2 S.isClosed_topologicalClosure.isComplete
  have hSK : ∀ s ∈ S, s ∈ K := fun s hs => hK ▸ S.le_topologicalClosure hs
  obtain ⟨z, hz⟩ : ∃ z : H, z = K.starProjection
      (toH fun j x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) := ⟨_, rfl⟩
  have hzK : z ∈ K := hz ▸ K.starProjection_apply_mem _
  have hO1 : ∀ s ∈ K, inner ℝ ((toH fun j x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) - z)
      s = 0 := fun s hs => hz ▸ K.starProjection_inner_eq_zero _ s hs
  have hCL : ∀ u : H, (∀ s ∈ S, inner ℝ u s = 0) → ∀ s ∈ K, inner ℝ u s = 0 := by
    intro u hu s hs
    have hsub : (K : Set H) ⊆ {s | inner ℝ u s = 0} := by
      rw [hK, Submodule.topologicalClosure_coe]
      exact closure_minimal hu (isClosed_eq (continuous_const.inner continuous_id) continuous_const)
    exact hsub hs
  have hO2 : ∀ s ∈ S, inner ℝ ((toH fun j x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) -
      toH fun j x => F x (EuclideanSpace.single j (1 : ℝ))) s = 0 := by
    rintro _ ⟨ζ, h1, hc1, hs1, rfl⟩
    rw [inner_sub_left, hipH _ _ hMDw (hMζ ζ h1).2, hipH _ _ hMF (hMζ ζ h1).2, hweak ζ h1 hc1 hs1,
      sub_self]
  have hO3 : ∀ c : Euclid m →L[ℝ] Euclid k, ∀ s ∈ S,
      inner ℝ (toH fun j _ => c (EuclideanSpace.single j (1 : ℝ))) s = 0 := by
    rintro c _ ⟨ζ, h1, hc1, hs1, rfl⟩
    rw [hipH _ _ (fun j => memLp_const _) (hMζ ζ h1).2,
      integral_finsetSum _ fun j _ => hinner _ _ (memLp_const _) ((hMζ ζ h1).2 j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := hIBPB univ (fun _ => c (EuclideanSpace.single j (1 : ℝ))) ζ isOpen_univ
      (subset_univ _) contDiffOn_const h1 hc1 hs1 j
    simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, inner_zero_right, integral_zero,
      neg_zero] at h0
    rw [← h0]
    exact integral_congr_ae (ae_of_all _ fun x => real_inner_comm _ _)
  have hzle : ∀ c : Euclid m →L[ℝ] Euclid k,
      ‖z‖ ^ 2 ≤ ∫ x, ∑ j : Fin m, ‖(F x - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ∂μ := by
    intro c
    have hMc : ∀ j : Fin m, MemLp (fun _ : Euclid m => c (EuclideanSpace.single j (1 : ℝ))) 2 μ :=
      fun j => memLp_const _
    have hproj : K.starProjection ((toH fun j x => F x (EuclideanSpace.single j (1 : ℝ))) -
        toH fun j _ => c (EuclideanSpace.single j (1 : ℝ))) = z := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hzK fun s hs => ?_
      rw [show (toH fun j x => F x (EuclideanSpace.single j (1 : ℝ))) -
          (toH fun j _ => c (EuclideanSpace.single j (1 : ℝ))) - z =
          ((toH fun j x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) - z) -
          ((toH fun j x => fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) -
            toH fun j x => F x (EuclideanSpace.single j (1 : ℝ))) -
          toH fun j _ => c (EuclideanSpace.single j (1 : ℝ)) by abel,
        inner_sub_left, inner_sub_left, hO1 s hs, hCL _ hO2 s hs, hCL _ (hO3 c) s hs, sub_zero,
        sub_zero]
    have h1 : ‖z‖ ≤ ‖(toH fun j x => F x (EuclideanSpace.single j (1 : ℝ))) -
        toH fun j _ => c (EuclideanSpace.single j (1 : ℝ))‖ := by
      rw [← hproj]
      exact K.norm_starProjection_apply_le _
    have hM : ∀ j : Fin m, MemLp (((fun j x => F x (EuclideanSpace.single j (1 : ℝ))) -
        fun j _ => c (EuclideanSpace.single j (1 : ℝ)) : Fin m → Euclid m → Euclid k) j) 2 μ :=
      fun j => (hMF j).sub (hMc j)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [← hsubH _ _ hMF hMc, hnormH _ hM] at h2
    exact h2.trans_eq (integral_congr_ae (ae_of_all _ fun x => rfl))
  /- Step 5: a potential for `z`.  Choose `ζₙ ∈ C¹_c(B)` with `Dζₙ → z` in `H`; by Poincaré
  `(ζₙ)` is Cauchy in `H₀`, with limit `ψ`. -/
  have hzcl : z ∈ closure (S : Set H) := by
    rw [← Submodule.topologicalClosure_coe, ← hK]
    exact hzK
  obtain ⟨Q, hQS, hQ⟩ := mem_closure_iff_seq_limit.1 hzcl
  have hQS' : ∀ n, ∃ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ ball x₀ R ∧
        Q n = toH fun j x => fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)) :=
    hQS
  choose ζ hζC hζc hζB hζQ using hQS'
  have hPQ : ∀ n l, ‖toH₀ (ζ n) - toH₀ (ζ l)‖ ≤ 2 * R * ‖Q n - Q l‖ := by
    intro n l
    have hC : ContDiff ℝ 1 (ζ n - ζ l) := (hζC n).sub (hζC l)
    have hdiff : (fun j x => fderiv ℝ (ζ n - ζ l) x (EuclideanSpace.single j (1 : ℝ))) =
        (fun j x => fderiv ℝ (ζ n) x (EuclideanSpace.single j (1 : ℝ))) -
          fun j x => fderiv ℝ (ζ l) x (EuclideanSpace.single j (1 : ℝ)) := by
      funext j x
      rw [fderiv_sub ((hζC n).differentiable one_ne_zero x) ((hζC l).differentiable one_ne_zero x)]
      rfl
    have h1 := hpoinc (ζ n - ζ l) hC ((hζc n).sub (hζc l))
      ((tsupport_sub _ _).trans (union_subset (hζB n) (hζB l)))
    rw [← hnorm0 _ (hMζ _ hC).1, ← hnormH _ (hMζ _ hC).2, hsub0 _ _ (hMζ _ (hζC n)).1
      (hMζ _ (hζC l)).1, hdiff, hsubH _ _ (hMζ _ (hζC n)).2 (hMζ _ (hζC l)).2, ← hζQ n,
      ← hζQ l] at h1
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow, mul_pow]
    linarith only [h1]
  have hPc : CauchySeq fun n => toH₀ (ζ n) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hQ.cauchySeq (ε / (2 * R)) (by positivity)
    refine ⟨N, fun n hn l hl => ?_⟩
    rw [dist_eq_norm]
    refine (hPQ n l).trans_lt ?_
    have h2R : (0 : ℝ) < 2 * R := by positivity
    calc 2 * R * ‖Q n - Q l‖ < 2 * R * (ε / (2 * R)) :=
          mul_lt_mul_of_pos_left (by rw [← dist_eq_norm]; exact hN n hn l hl) h2R
      _ = ε := mul_div_cancel₀ ε h2R.ne'
  obtain ⟨ψ, hψ⟩ := cauchySeq_tendsto_of_complete hPc
  -- passing to the limit in `∫_B ⟨f, ζₙ⟩` and `∫_B ⟨f, ∂ⱼζₙ⟩`
  have hlimψ : ∀ f : Euclid m → Euclid k, MemLp f 2 μ → Tendsto
      (fun n => ∫ x, inner ℝ (f x) (ζ n x) ∂μ) atTop (𝓝 (∫ x, inner ℝ (f x) (ψ x) ∂μ)) := by
    intro f hf
    have e2 : inner ℝ (toH₀ f) ψ = ∫ x, inner ℝ (f x) (ψ x) ∂μ := by
      rw [hip]
      refine integral_congr_ae ?_
      filter_upwards [hcoe f hf] with x hx
      rw [hx]
    rw [← e2]
    exact ((tendsto_const_nhds (x := toH₀ f)).inner (𝕜 := ℝ) hψ).congr fun n =>
      hip0 _ _ hf (hMζ _ (hζC n)).1
  have hlimz : ∀ (j : Fin m) (f : Euclid m → Euclid k), MemLp f 2 μ → Tendsto
      (fun n => ∫ x, inner ℝ (f x) (fderiv ℝ (ζ n) x (EuclideanSpace.single j (1 : ℝ))) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (f x) (z j x) ∂μ)) := by
    intro j f hf
    have e2 : inner ℝ (toH₀ f) (z j) = ∫ x, inner ℝ (f x) (z j x) ∂μ := by
      rw [hip]
      refine integral_congr_ae ?_
      filter_upwards [hcoe f hf] with x hx
      rw [hx]
    rw [← e2]
    refine ((tendsto_const_nhds (x := toH₀ f)).inner (𝕜 := ℝ)
      (((PiLp.continuous_apply 2 _ j).tendsto z).comp hQ)).congr fun n => ?_
    simp only [Function.comp_apply, hζQ n]
    exact hip0 _ _ hf ((hMζ _ (hζC n)).2 j)
  /- Step 6: `w - ψ` is weakly harmonic: for `η ∈ C²_c(B)` and `a = eκ`,
  `∫_B ⟨a, w - ψ⟩ Δη = -⟨D(η a), Dw - z⟩ = 0`. -/
  have hLAP : ∀ (U : Set (Euclid m)) (f : Euclid m → Euclid k) (η : Euclid m → ℝ) (a : Euclid k),
      IsOpen U → ball x₀ R ⊆ U → ContDiffOn ℝ 1 f U → MemLp f 2 μ → ContDiff ℝ 2 η →
      HasCompactSupport η → tsupport η ⊆ ball x₀ R →
      ∫ x, inner ℝ ((∑ i : Fin m, iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) • a) (f x) ∂μ =
        -∑ l : Fin m, ∫ x, inner ℝ (fderiv ℝ (fun y => η y • a) x (EuclideanSpace.single l (1 : ℝ)))
          (fderiv ℝ f x (EuclideanSpace.single l (1 : ℝ))) ∂μ := by
    intro U f η a hU hBU hf hMf hη hηc hηB
    have hη1 : ContDiff ℝ 1 (fderiv ℝ η) := hη.fderiv_right (by norm_num)
    have hl : ∀ l : Fin m, ∫ x, inner ℝ (iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single l (1 : ℝ), EuclideanSpace.single l (1 : ℝ)] • a) (f x) ∂μ =
        -∫ x, inner ℝ (fderiv ℝ (fun y => η y • a) x (EuclideanSpace.single l (1 : ℝ)))
          (fderiv ℝ f x (EuclideanSpace.single l (1 : ℝ))) ∂μ := by
      intro l
      have hΦc : HasCompactSupport (fun y => fderiv ℝ η y (EuclideanSpace.single l (1 : ℝ)) • a) :=
        (hηc.fderiv ℝ).comp_left (g := fun L : Euclid m →L[ℝ] ℝ =>
          L (EuclideanSpace.single l (1 : ℝ)) • a) (by simp)
      have hΦB : tsupport (fun y => fderiv ℝ η y (EuclideanSpace.single l (1 : ℝ)) • a) ⊆
          ball x₀ R :=
        ((tsupport_comp_subset (g := fun L : Euclid m →L[ℝ] ℝ =>
          L (EuclideanSpace.single l (1 : ℝ)) • a) (by simp) (fderiv ℝ η)).trans
          (tsupport_fderiv_subset ℝ)).trans hηB
      have h0 := hIBPB U f (fun y => fderiv ℝ η y (EuclideanSpace.single l (1 : ℝ)) • a) hU hBU hf
        ((hη1.clm_apply contDiff_const).smul contDiff_const) hΦc hΦB l
      have hd2 : ∀ x, fderiv ℝ (fun y => fderiv ℝ η y (EuclideanSpace.single l (1 : ℝ)) • a) x
          (EuclideanSpace.single l (1 : ℝ)) = iteratedFDeriv ℝ 2 η x
            ![EuclideanSpace.single l (1 : ℝ), EuclideanSpace.single l (1 : ℝ)] • a := fun x => by
        rw [fderiv_smul_const ((hη1.differentiable one_ne_zero x).clm_apply
          (differentiableAt_const _)), iteratedFDeriv_two_apply,
          fderiv_clm_apply (hη1.differentiable one_ne_zero x) (differentiableAt_const _)]
        simp
      have hd1 : ∀ x, fderiv ℝ (fun y => η y • a) x (EuclideanSpace.single l (1 : ℝ)) =
          fderiv ℝ η x (EuclideanSpace.single l (1 : ℝ)) • a := fun x => by
        rw [fderiv_smul_const (hη.differentiable (by norm_num) x)]
        rfl
      simp only [hd2] at h0
      simp only [hd1]
      exact h0
    have hMl : ∀ l : Fin m, MemLp (fun x => iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single l (1 : ℝ), EuclideanSpace.single l (1 : ℝ)] • a) 2 μ := fun l =>
      hML _ ((((continuous_eval_const _).comp (hη.continuous_iteratedFDeriv (m := 2)
        (by norm_num))).smul continuous_const).continuousOn)
    simp only [Finset.sum_smul, sum_inner]
    rw [integral_finsetSum _ fun l _ => hinner _ _ (hMl l) hMf, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => hl l
  have hharm : ∀ (κ : Fin k) (η : Euclid m → ℝ), ContDiff ℝ 2 η → HasCompactSupport η →
      tsupport η ⊆ ball x₀ R → ∫ x, (w x - ψ x) κ * ∑ i : Fin m, iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] ∂μ = 0 := by
    intro κ η hη hηc hηB
    obtain ⟨a, ha⟩ : ∃ a : Euclid k, a = EuclideanSpace.single κ (1 : ℝ) := ⟨_, rfl⟩
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid m → Euclid k, Φ = fun y => η y • a := ⟨_, rfl⟩
    have hΦC : ContDiff ℝ 1 Φ := hΦ ▸ (hη.of_le (by norm_num)).smul contDiff_const
    have hΦK : (toH fun l x => fderiv ℝ Φ x (EuclideanSpace.single l (1 : ℝ))) ∈ K :=
      hSK _ ⟨Φ, hΦC, hΦ ▸ hηc.smul_right, hΦ ▸ (tsupport_smul_subset_left _ _).trans hηB, rfl⟩
    have hcD2 : ∀ v, Continuous fun x => iteratedFDeriv ℝ 2 η x v := fun v =>
      (continuous_eval_const v).comp (hη.continuous_iteratedFDeriv (m := 2) (by norm_num))
    have hMΔ : MemLp (fun x => (∑ i : Fin m, iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) • a) 2 μ :=
      hML _ (((continuous_finsetSum _ fun i _ => hcD2 _).smul continuous_const).continuousOn)
    have hipΦ : ∀ v : Fin m → Euclid m → Euclid k, (∀ l, MemLp (v l) 2 μ) →
        inner ℝ (toH fun l x => fderiv ℝ Φ x (EuclideanSpace.single l (1 : ℝ))) (toH v) =
          ∑ l : Fin m, ∫ x, inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single l (1 : ℝ))) (v l x) ∂μ :=
      fun v hv => by
        rw [PiLp.inner_apply]
        exact Finset.sum_congr rfl fun l _ => hip0 _ _ ((hMζ Φ hΦC).2 l) (hv l)
    -- the `w` part
    have hw' := hLAP (ball x₀ R') w η a isOpen_ball hBB' hw hMw hη hηc hηB
    rw [← hΦ] at hw'
    -- the `ψ` part, as the limit of the `ζₙ` parts
    have hψ' : ∫ x, inner ℝ ((∑ i : Fin m, iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) • a) (ψ x) ∂μ =
        -inner ℝ (toH fun l x => fderiv ℝ Φ x (EuclideanSpace.single l (1 : ℝ))) z := by
      refine tendsto_nhds_unique (hlimψ _ hMΔ) ?_
      refine ((tendsto_const_nhds.inner (𝕜 := ℝ) hQ).neg).congr fun n => ?_
      rw [hLAP univ (ζ n) η a isOpen_univ (subset_univ _) (hζC n).contDiffOn (hMζ _ (hζC n)).1 hη
        hηc hηB, ← hΦ, hζQ n, hipΦ _ (hMζ _ (hζC n)).2]
    have e1 : ∀ x, (w x - ψ x) κ * ∑ i : Fin m, iteratedFDeriv ℝ 2 η x
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] =
        inner ℝ ((∑ i : Fin m, iteratedFDeriv ℝ 2 η x
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) • a) (w x) -
        inner ℝ ((∑ i : Fin m, iteratedFDeriv ℝ 2 η x
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]) • a) (ψ x) := by
      intro x
      rw [← inner_sub_right, real_inner_smul_left, ha, EuclideanSpace.inner_single_left, mul_comm]
      simp
    rw [integral_congr_ae (ae_of_all _ e1), integral_sub (hinner _ _ hMΔ hMw)
      (hinner _ _ hMΔ (Lp.memLp ψ)), hw', hψ']
    have hO := hO1 _ hΦK
    rw [inner_sub_left, real_inner_comm _ (toH _), real_inner_comm _ z, hipΦ _ hMDw] at hO
    linarith only [hO]
  /- Step 7: Weyl's lemma, componentwise, after translating `B` to `B_R(0)`. -/
  have hT : MeasurePreserving (fun y : Euclid m => y + x₀) (volume.restrict (ball 0 R)) μ := by
    have h := (measurePreserving_add_right (volume : Measure (Euclid m)) x₀).restrict_preimage
      (measurableSet_ball (x := x₀) (ε := R))
    rwa [preimage_add_right_ball, sub_self] at h
  have hTe : MeasurableEmbedding (fun y : Euclid m => y + x₀) :=
    (MeasurableEquiv.addRight x₀).measurableEmbedding
  have hweyl : ∀ κ : Fin k, ∃ g : Euclid m → ℝ, (∀ n : ℕ, ContDiffOn ℝ n g (ball 0 R)) ∧
      (∀ y ∈ ball (0 : Euclid m) R, ∑ i : Fin m, iteratedFDeriv ℝ 2 g y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) ∧
      ∀ᵐ x ∂μ, g (x - x₀) = (w x - ψ x) κ := by
    intro κ
    have hvint : Integrable (fun x => (w x - ψ x) κ) μ :=
      (EuclideanSpace.proj (𝕜 := ℝ) κ).integrable_comp
        ((hMw.integrable one_le_two).sub ((Lp.memLp ψ).integrable one_le_two))
    obtain ⟨g, hg1, hg2, hg3⟩ := Submission.dorag_ha_weyl_lemma m R
      (fun y => (w (y + x₀) - ψ (y + x₀)) κ) (by omega) hR ((hT.integrable_comp_emb hTe).2 hvint)
      fun ζ' hζ' hζ'c hζ'B => by
        have hηB : tsupport (fun x => ζ' (x - x₀)) ⊆ ball x₀ R := fun x hx => by
          have h1 : x - x₀ ∈ ball (0 : Euclid m) R :=
            hζ'B ((tsupport_comp_eq_preimage ζ' (Homeomorph.subRight x₀)).subset hx)
          rwa [mem_ball, dist_zero_right, ← dist_eq_norm] at h1
        have h0 := hharm κ (fun x => ζ' (x - x₀)) (hζ'.comp (contDiff_id.sub contDiff_const))
          (hζ'c.comp_homeomorph (Homeomorph.subRight x₀)) hηB
        rw [← hT.integral_comp hTe] at h0
        simpa only [iteratedFDeriv_comp_sub, add_sub_cancel_right] using h0
    refine ⟨g, hg1, hg2, ?_⟩
    have h3 : ∀ᵐ y ∂(volume.restrict (ball (0 : Euclid m) R)),
        g (y + x₀ - x₀) = (w (y + x₀) - ψ (y + x₀)) κ := by
      filter_upwards [hg3] with y hy
      rw [add_sub_cancel_right, hy]
    have h4 := (hTe.ae_map_iff (p := fun x => g (x - x₀) = (w x - ψ x) κ)).2 h3
    rwa [hT.map_eq] at h4
  choose g hg1 hg2 hg3 using hweyl
  -- Step 8: `h = Σ_κ g_κ(· - x₀) eκ` is smooth and harmonic on `B`, and `h = w - ψ` a.e. on `B`
  have hmaps : MapsTo (fun x : Euclid m => x - x₀) (ball x₀ R) (ball 0 R) := fun x hx => by
    rwa [mem_ball, dist_zero_right, ← dist_eq_norm]
  have hhs : ∀ n : ℕ, ContDiffOn ℝ n
      (fun x => WithLp.toLp 2 fun κ => g κ (x - x₀) : Euclid m → Euclid k) (ball x₀ R) := fun n =>
    contDiffOn_piLp' 2 fun κ => (hg1 κ n).comp (contDiffOn_id.sub contDiffOn_const) hmaps
  have hΔh : ∀ x ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2
      (fun x => WithLp.toLp 2 fun κ => g κ (x - x₀) : Euclid m → Euclid k) x
      ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
    intro x hx
    have hxat := (hhs 2).contDiffAt (isOpen_ball.mem_nhds hx)
    refine PiLp.ext fun κ => ?_
    have h1 := (EuclideanSpace.proj κ).iteratedFDeriv_comp_left hxat (i := 2) le_rfl
    rw [show ⇑(EuclideanSpace.proj κ) ∘ (fun x => WithLp.toLp 2 fun κ => g κ (x - x₀) :
      Euclid m → Euclid k) = fun x => g κ (x - x₀) from rfl, iteratedFDeriv_comp_sub] at h1
    rw [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_zero, Pi.zero_apply]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (hg2 κ (x - x₀) (hmaps hx))
    rw [h1]
    rfl
  have hhae : ∀ᵐ x ∂μ, (fun x => WithLp.toLp 2 fun κ => g κ (x - x₀) : Euclid m → Euclid k) x =
      w x - ψ x := by
    filter_upwards [ae_all_iff.2 hg3] with x hx
    exact PiLp.ext hx
  generalize hhdef : (fun x => WithLp.toLp 2 fun κ => g κ (x - x₀) : Euclid m → Euclid k) = h
    at hhs hΔh hhae
  /- Step 9: `D(w - h) = z` a.e. on `B`.  For `φ ∈ C^∞_c(B)` and `Φ = φ eκ`,
  `∫_B ⟨Φ, ∂ⱼ(w - h)⟩ = -∫_B ⟨∂ⱼΦ, w - h⟩ = -∫_B ⟨∂ⱼΦ, ψ⟩ = ∫_B ⟨Φ, zⱼ⟩`. -/
  have hD : ContDiffOn ℝ 1 (w - h) (ball x₀ R) := (hw.mono hBB').sub (hhs 1)
  have hDψ : ∀ᵐ x ∂μ, (w - h) x = ψ x := by
    filter_upwards [hhae] with x hx
    rw [Pi.sub_apply, hx, sub_sub_cancel]
  have hgrad : ∀ j : Fin m, ∀ᵐ x ∂μ,
      fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ)) = z j x := by
    intro j
    have hDc : ContinuousOn (fun x => fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ)))
        (ball x₀ R) :=
      (hD.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).clm_apply continuousOn_const
    have hκ : ∀ κ : Fin k, ∀ᵐ x ∂μ, inner ℝ (EuclideanSpace.single κ (1 : ℝ))
        (fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ))) -
        inner ℝ (EuclideanSpace.single κ (1 : ℝ)) (z j x) = 0 := by
      intro κ
      refine (ae_restrict_iff' measurableSet_ball).2
        (isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (((ContinuousOn.inner (𝕜 := ℝ) continuousOn_const hDc).locallyIntegrableOn
          measurableSet_ball).sub (IntegrableOn.locallyIntegrableOn (hinner _ _
          (memLp_const (EuclideanSpace.single κ (1 : ℝ))) (Lp.memLp (z j)))))
        fun φ hφ hφc hφB => ?_)
      obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid m → Euclid k,
          Φ = fun y => φ y • EuclideanSpace.single κ (1 : ℝ) := ⟨_, rfl⟩
      have hΦC : ContDiff ℝ 1 Φ := hΦ ▸ (hφ.of_le (by simp)).smul contDiff_const
      have hΦc : HasCompactSupport Φ := hΦ ▸ hφc.smul_right
      have hΦB : tsupport Φ ⊆ ball x₀ R := hΦ ▸ (tsupport_smul_subset_left _ _).trans hφB
      obtain ⟨hMΦ, hMDΦ⟩ := hMζ Φ hΦC
      -- `∫_B ⟨Φ, zⱼ⟩ = -∫_B ⟨∂ⱼΦ, ψ⟩`, passing to the limit in `∫ ⟨Φ, ∂ⱼζₙ⟩ = -∫ ⟨∂ⱼΦ, ζₙ⟩`
      have hz' : ∫ x, inner ℝ (Φ x) (z j x) ∂μ =
          -∫ x, inner ℝ (fderiv ℝ Φ x (EuclideanSpace.single j (1 : ℝ))) (ψ x) ∂μ :=
        tendsto_nhds_unique (hlimz j Φ hMΦ) (((hlimψ _ (hMDΦ j)).neg).congr fun n => by
          rw [hIBPB univ (ζ n) Φ isOpen_univ (subset_univ _) (hζC n).contDiffOn hΦC hΦc hΦB j,
            neg_neg])
      -- `∫_B ⟨Φ, ∂ⱼ(w - h)⟩ = -∫_B ⟨∂ⱼΦ, w - h⟩ = -∫_B ⟨∂ⱼΦ, ψ⟩`
      have hD' := hIBPB (ball x₀ R) (w - h) Φ isOpen_ball subset_rfl hD hΦC hΦc hΦB j
      rw [integral_congr_ae (hDψ.mono fun x hx => by rw [hx])] at hD'
      have hI1 : Integrable (fun x => inner ℝ (Φ x)
          (fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ)))) μ :=
        (hint (ball x₀ R) _ _ hΦc hΦB (hΦC.continuous.continuousOn.inner hDc) fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_left]).integrableOn
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => hx (hφB h'), zero_smul]]
      rw [show (fun x => φ x • (inner ℝ (EuclideanSpace.single κ (1 : ℝ))
          (fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ))) -
          inner ℝ (EuclideanSpace.single κ (1 : ℝ)) (z j x))) = fun x => inner ℝ (Φ x)
          (fderiv ℝ (w - h) x (EuclideanSpace.single j (1 : ℝ))) - inner ℝ (Φ x) (z j x) by
        funext x
        rw [hΦ, smul_eq_mul, mul_sub, real_inner_smul_left, real_inner_smul_left]]
      rw [integral_sub hI1 (hinner _ _ hMΦ (Lp.memLp (z j)))]
      linarith only [hD', hz']
    filter_upwards [ae_all_iff.2 hκ] with x hx
    refine PiLp.ext fun κ => ?_
    have h1 := hx κ
    rwa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left, map_one, one_mul,
      one_mul, sub_eq_zero] at h1
  -- Step 10: the energy bound `∫_B |Dw - Dh|² = ‖z‖² ≤ ∫_B |F - c|²`
  have hEq : (fun x => ∑ j : Fin m,
      ‖(fderiv ℝ w x - fderiv ℝ h x) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) =ᵐ[μ]
      fun x => ∑ j : Fin m, ‖z j x‖ ^ 2 := by
    filter_upwards [ae_all_iff.2 hgrad, ae_restrict_mem measurableSet_ball] with x hx hxB
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hx j, fderiv_sub ((hw.differentiableOn one_ne_zero x (hBB' hxB)).differentiableAt
      (isOpen_ball.mem_nhds (hBB' hxB)))
      (((hhs 1).differentiableOn one_ne_zero x hxB).differentiableAt (isOpen_ball.mem_nhds hxB))]
  have hzint : Integrable (fun x => ∑ j : Fin m, ‖z j x‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => hsq _ (Lp.memLp (z j))
  have hznorm : ‖z‖ ^ 2 = ∫ x, ∑ j : Fin m, ‖z j x‖ ^ 2 ∂μ := by
    rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum _ fun j _ => hsq _ (Lp.memLp (z j))]
    exact Finset.sum_congr rfl fun j _ => hnorm (z j)
  refine ⟨h, hhs, hΔh, hzint.congr hEq.symm, fun c => ?_⟩
  rw [integral_congr_ae hEq, ← hznorm]
  exact hzle c
/-- Interior estimates for harmonic functions (Simon Ch. 5, 3.2–3.4, the standard estimates that
"follow directly from the mean-value property").  If `h` is smooth and harmonic on
`B = B̆_R(0) ⊂ ℝⁿ` with `∫_B ‖Dh‖² ≤ Rⁿ`, then with `ω = Lⁿ(B̆₁(0))`, `K₁ = 2ⁿ/√ω` and
`C_H = 4nK₁`: (a) `|h(0)| ≤ C_H √(R⁻ⁿ∫_B h²)`, (b) `‖Dh(0)‖ ≤ C_H`, and
(c) `|h(v) − h(0) − Dh(0)v| ≤ C_H‖v‖²/R` for `‖v‖ ≤ R/4`.  The directional derivatives `Dh(·)e`
are again harmonic, so the ball mean value property and Cauchy–Schwarz give (a), (b) on
`B̆_{R/2}(0)` and `‖Dh‖ ≤ K₁` on `B̄_{5R/8}(0)` (balls of radius `R/4`); comparing the means of
`Dh(·)v` over shifted balls gives `|D²h(x)(v, v)| ≤ 8nK₁‖v‖²/R` for `‖x‖ ≤ R/4`, and (c) follows
by second-order Taylor expansion. -/
theorem Submission.dorag_ha_interior_estimates : ∀ n : ℕ, 0 < n → ∃ CH : ℝ, 0 < CH ∧ ∀ (R : ℝ) (h : Euclid n → ℝ), 0 < R → (∀ m : ℕ, ContDiffOn ℝ m h (ball (0 : Euclid n) R)) → (∀ y ∈ ball (0 : Euclid n) R, ∑ i : Fin n, iteratedFDeriv ℝ 2 h y ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun y => ‖fderiv ℝ h y‖ ^ 2) (ball (0 : Euclid n) R) → ∫ y in ball (0 : Euclid n) R, ‖fderiv ℝ h y‖ ^ 2 ≤ R ^ n → IntegrableOn (fun y => h y ^ 2) (ball (0 : Euclid n) R) → |h 0| ≤ CH * Real.sqrt ((∫ y in ball (0 : Euclid n) R, h y ^ 2) / R ^ n) ∧ ‖fderiv ℝ h 0‖ ≤ CH ∧ ∀ v : Euclid n, ‖v‖ ≤ R / 4 → |h v - h 0 - fderiv ℝ h 0 v| ≤ CH * ‖v‖ ^ 2 / R := by
  intro n hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  -- `ω = Lⁿ(B̆₁(0)) ∈ (0, ∞)` and `Lⁿ(B̆_r(y)) = rⁿω`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, (volume (ball (0 : Euclid n) 1)).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  have hvol : ∀ (y : Euclid n) (r : ℝ), 0 < r → (volume (ball y r)).toReal = r ^ n * ω := by
    intro y r hr
    rw [Measure.addHaar_ball_of_pos volume y hr, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hω_def]
  -- `K₁ = 2ⁿ/√ω`, so that `K₁²ω = 4ⁿ`, and `C_H = 4nK₁ ≥ K₁`
  obtain ⟨K₁, hK₁_def⟩ : ∃ K₁ : ℝ, 2 ^ n / Real.sqrt ω = K₁ := ⟨_, rfl⟩
  have hK₁ : 0 < K₁ := hK₁_def ▸ div_pos (pow_pos two_pos n) (Real.sqrt_pos.2 hω)
  have hK₁sq : K₁ ^ 2 * ω = 4 ^ n := by
    rw [← hK₁_def, div_pow, Real.sq_sqrt hω.le, div_mul_cancel₀ _ hω.ne', ← pow_mul, mul_comm,
      pow_mul]
    norm_num
  have hle_K₁ : ∀ a : ℝ, 0 ≤ a → a ^ 2 * ω ≤ 4 ^ n → a ≤ K₁ := by
    intro a ha haK
    rw [← hK₁sq] at haK
    exact (pow_le_pow_iff_left₀ ha hK₁.le two_ne_zero).1 (le_of_mul_le_mul_right haK hω)
  have hCH : 0 < 4 * (n : ℝ) * K₁ := mul_pos (mul_pos four_pos hn') hK₁
  have hK₁CH : K₁ ≤ 4 * n * K₁ :=
    le_mul_of_one_le_left hK₁.le (by have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn; linarith)
  refine ⟨4 * n * K₁, hCH, ?_⟩
  intro R h hR hcd hlap hgradint hgrad hint
  have hB : IsOpen (ball (0 : Euclid n) R) := isOpen_ball
  have h2 : ContDiffOn ℝ 2 h (ball (0 : Euclid n) R) := by exact_mod_cast hcd 2
  have hDh : ContDiffOn ℝ 1 (fderiv ℝ h) (ball (0 : Euclid n) R) :=
    h2.fderiv_of_isOpen hB (by norm_num)
  -- `B̄_r(y) ⊆ B` as soon as `‖y‖ + r < R`
  have hsub : ∀ (y : Euclid n) (r : ℝ), ‖y‖ + r < R → closedBall y r ⊆ ball (0 : Euclid n) R :=
    fun y r hyr => closedBall_subset_ball' (by rw [dist_zero_right]; linarith)
  -- step 1: every `u_e = Dh(·)e` is smooth and harmonic on `B`
  have hA := fun e => Submission.dorag_ha_ie_fderiv_apply_harmonic n _ h e hB hcd hlap
  -- the mean value identities for `h` and for every `u_e` on balls `B̄_r(y) ⊆ B`
  have hmv : ∀ (y : Euclid n) (r : ℝ), 0 < r → closedBall y r ⊆ ball (0 : Euclid n) R →
      ∫ z in ball y r, h z = (volume (ball y r)).toReal * h y :=
    fun y r hr hyr => (Submission.dorag_ha_mean_value n _ h hn hB h2 hlap y r hr hyr).2
  have hmvD : ∀ (e y : Euclid n) (r : ℝ), 0 < r → closedBall y r ⊆ ball (0 : Euclid n) R →
      ∫ z in ball y r, fderiv ℝ h z e = (volume (ball y r)).toReal * fderiv ℝ h y e :=
    fun e y r hr hyr => (Submission.dorag_ha_mean_value n _ _ hn hB
      (by exact_mod_cast (hA e).1 2) (hA e).2 y r hr hyr).2
  -- step 2 (2b): `‖Dh(y)‖²ω ≤ cⁿ` whenever `B̄_{R/c}(y) ⊆ B`, since `∫_B ‖Dh‖² ≤ Rⁿ`
  have hgrad_le : ∀ (y : Euclid n) (c : ℝ), 0 < c →
      closedBall y (R / c) ⊆ ball (0 : Euclid n) R → ‖fderiv ℝ h y‖ ^ 2 * ω ≤ c ^ n := by
    intro y c hc hyc
    have hRc : 0 < R / c := div_pos hR hc
    have h1 := Submission.dorag_ha_ie_opNorm_sq_mul_volume_le_of_mean_value n (fderiv ℝ h) y
      (R / c) hRc (hDh.continuousOn.mono hyc) fun e => hmvD e y (R / c) hRc hyc
    have h2 : ∫ z in ball y (R / c), ‖fderiv ℝ h z‖ ^ 2 ≤ R ^ n :=
      (setIntegral_mono_set hgradint (Eventually.of_forall fun _ => sq_nonneg _)
        (ball_subset_closedBall.trans hyc).eventuallyLE).trans hgrad
    rw [hvol y _ hRc, div_pow] at h1
    have hRn : 0 < R ^ n := pow_pos hR n
    calc ‖fderiv ℝ h y‖ ^ 2 * ω
        = ‖fderiv ℝ h y‖ ^ 2 * (R ^ n / c ^ n * ω) * (c ^ n / R ^ n) := by field_simp
      _ ≤ R ^ n * (c ^ n / R ^ n) := by gcongr; exact h1.trans h2
      _ = c ^ n := by field_simp
  -- (a): the mean value bound (2a) on `B̆_{R/2}(0)`
  have ha : |h 0| ≤ 4 * n * K₁ * Real.sqrt ((∫ y in ball (0 : Euclid n) R, h y ^ 2) / R ^ n) := by
    have hR2 : 0 < R / 2 := half_pos hR
    have hsub0 := hsub 0 (R / 2) (by rw [norm_zero]; linarith)
    have h1 := Submission.dorag_ha_ie_sq_mul_volume_le_of_mean_value n h 0 (R / 2) hR2
      ((hcd 0).continuousOn.mono hsub0) (hmv 0 _ hR2 hsub0)
    have h2 : ∫ z in ball (0 : Euclid n) (R / 2), h z ^ 2 ≤ ∫ y in ball (0 : Euclid n) R, h y ^ 2 :=
      setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
        (ball_subset_closedBall.trans hsub0).eventuallyLE
    rw [hvol 0 _ hR2, div_pow] at h1
    obtain ⟨I, hI_def⟩ : ∃ I : ℝ, ∫ y in ball (0 : Euclid n) R, h y ^ 2 = I := ⟨_, rfl⟩
    rw [hI_def] at h2 ⊢
    have hRn : 0 < R ^ n := pow_pos hR n
    have hI : 0 ≤ I := le_trans (by positivity) (h1.trans h2)
    have hconst : 2 ^ n / ω ≤ (4 * n * K₁) ^ 2 := by
      rw [div_le_iff₀ hω]
      calc (2 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
        _ ≤ 16 * n ^ 2 * 4 ^ n := le_mul_of_one_le_left (by positivity) (by
            have : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
            nlinarith)
        _ = (4 * n * K₁) ^ 2 * ω := by rw [← hK₁sq]; ring
    have hsq : h 0 ^ 2 ≤ (4 * n * K₁) ^ 2 * (I / R ^ n) :=
      calc h 0 ^ 2 = h 0 ^ 2 * (R ^ n / 2 ^ n * ω) * (2 ^ n / ω / R ^ n) := by field_simp
        _ ≤ I * (2 ^ n / ω / R ^ n) := by gcongr; exact h1.trans h2
        _ = 2 ^ n / ω * (I / R ^ n) := by ring
        _ ≤ (4 * n * K₁) ^ 2 * (I / R ^ n) := mul_le_mul_of_nonneg_right hconst (by positivity)
    calc |h 0| ≤ Real.sqrt ((4 * n * K₁) ^ 2 * (I / R ^ n)) := Real.abs_le_sqrt hsq
      _ = 4 * n * K₁ * Real.sqrt (I / R ^ n) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hCH.le]
  -- (b): the mean value bound (2b) on `B̆_{R/2}(0)`
  have hb : ‖fderiv ℝ h 0‖ ≤ 4 * n * K₁ :=
    (hle_K₁ _ (norm_nonneg _) ((hgrad_le 0 2 two_pos (hsub 0 _ (by rw [norm_zero]; linarith))).trans
      (pow_le_pow_left₀ (by norm_num) (by norm_num) n))).trans hK₁CH
  -- step 4: `‖Dh‖ ≤ K₁` on `B̄_{5R/8}(0)`, by (2b) on balls of radius `R/4`
  have hstep4 : ∀ z : Euclid n, ‖z‖ ≤ 5 * R / 8 → ‖fderiv ℝ h z‖ ≤ K₁ := fun z hz =>
    hle_K₁ _ (norm_nonneg _) (hgrad_le z 4 four_pos (hsub z _ (by linarith)))
  -- step 5: `|D²h(x)(v, v)| ≤ 8nK₁‖v‖²/R` for `‖x‖ ≤ R/4`, by the shifted-ball comparison
  -- for the harmonic function `u_v = Dh(·)v`, bounded by `K₁‖v‖` on `B̄_{3R/8}(x)`
  have hstep5 : ∀ v x : Euclid n, ‖v‖ ≤ R / 4 → ‖x‖ ≤ R / 4 →
      |iteratedFDeriv ℝ 2 h x ![v, v]| ≤ 2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖ := by
    intro v x hv hx
    have hR4 : 0 < R / 4 := by positivity
    have hxB : x ∈ ball (0 : Euclid n) R := mem_ball_zero_iff.2 (by linarith)
    have hu := (hA v).1
    have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ h y v) x :=
      ((hu 1).differentiableOn (by norm_num)).differentiableAt (hB.mem_nhds hxB)
    have hD := Submission.dorag_ha_ie_norm_fderiv_le_of_mean_value n (fun y => fderiv ℝ h y v) x
      (R / 4) (K₁ * ‖v‖) hn hR4 hdiff ((hu 0).continuousOn.mono (hsub x _ (by linarith)))
      (fun z hz => by
        have hz' : ‖z‖ ≤ 5 * R / 8 := by linarith [norm_le_of_mem_closedBall hz]
        show |fderiv ℝ h z v| ≤ K₁ * ‖v‖
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ h z).le_opNorm v).trans
          (mul_le_mul_of_nonneg_right (hstep4 z hz') (norm_nonneg v)))
      (fun z hz => hmvD v z (R / 4) hR4
        (hsub z _ (by linarith [norm_le_of_mem_closedBall hz])))
    have hDhx : DifferentiableAt ℝ (fderiv ℝ h) x :=
      (hDh.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hxB)
    have hiter : iteratedFDeriv ℝ 2 h x ![v, v] = fderiv ℝ (fun y => fderiv ℝ h y v) x v := by
      rw [iteratedFDeriv_two_apply, fderiv_clm_apply hDhx (differentiableAt_const v)]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply]
    rw [hiter, ← Real.norm_eq_abs]
    exact ((fderiv ℝ _ x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg v))
  -- step 6 and (c): second-order Taylor expansion along `τ ↦ h(τv)`
  refine ⟨ha, hb, fun v hv => ?_⟩
  have hT := Submission.dorag_ha_ie_taylor_two_le n h R (2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖) v
    h2 (by linarith [norm_nonneg v]) fun τ hτ => hstep5 v (τ • v) hv (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
      exact (mul_le_of_le_one_left (norm_nonneg v) hτ.2).trans hv)
  calc |h v - h 0 - fderiv ℝ h 0 v| ≤ 2 * n * (K₁ * ‖v‖) / (R / 4) * ‖v‖ / 2 := hT
    _ = 4 * n * K₁ * ‖v‖ ^ 2 / R := by field_simp

/-- **Campanato and Morrey decay for harmonic maps** (Campanato's method, Giaquinta–Martinazzi,
*Regularity Theory for Elliptic Systems*, 2012, Ch. 5, from the interior estimates of Simon
Ch. 5, 3.2–3.4).  Let `h : ℝᵐ → ℝᵏ` be smooth and harmonic on `B_R(x₀)` with
`|Dh|² = Σⱼ ‖Dh eⱼ‖²` integrable there.  For `0 < r ≤ R`,
(i) `∫_{B_r(x₀)} |Dh − (Dh)_{x₀,r}|² ≤ C (r/R)^{m+2} ∫_{B_R(x₀)} |Dh − (Dh)_{x₀,R}|²` and
(ii) `∫_{B_r(x₀)} |Dh|² ≤ C (r/R)ᵐ ∫_{B_R(x₀)} |Dh|²`, with `C = 16^{m+2} + 144ω2ᵐmkC_H²`.
For `r > R/16` both follow from `B_r ⊆ B_R` and the minimality of the ball average.  For
`r ≤ R/16` and any `Λ` above the right-hand integral, `Submission.dorag_ha_interior_estimates`
for `v ↦ λ⁻¹(h − c)^κ(x + v)` on `B_{R/2}(0)`, `λ = √(Λ/(R/2)ᵐ)`, gives `|∂ⱼh^κ| ≤ C_Hλ`
(`c = 0`) and, by three Taylor expansions at `x` and `x₀` (`c = (Dh)_{x₀,R}`),
`|∂ⱼh^κ(x) − ∂ⱼh^κ(x₀)| ≤ 12C_Hλr/R` on `B_r(x₀)`. -/
theorem Submission.codim1_hcp_sr_harmonic_decay : ∀ (m k : ℕ), 1 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Euclid m) (R : ℝ) (h : Euclid m → Euclid k), 0 < R → (∀ n : ℕ, ContDiffOn ℝ n h (ball x₀ R)) → (∀ x ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2 h x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0) → IntegrableOn (fun x => ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) → ∀ r : ℝ, 0 < r → r ≤ R → (∫ x in ball x₀ r, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ r, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ C * (r / R) ^ (m + 2) * ∫ x in ball x₀ R, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ R, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ∧ ∫ x in ball x₀ r, ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ C * (r / R) ^ m * ∫ x in ball x₀ R, ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
  intro m k hm
  obtain ⟨CH, hCH, hIE⟩ := Submission.dorag_ha_interior_estimates m (by omega)
  -- `ω = Lᵐ(B₁(0))`, so `Lᵐ(B_ρ(y)) = ρᵐω`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, (volume (ball (0 : Euclid m) 1)).toReal = ω := ⟨_, rfl⟩
  have hω : 0 < ω := hω_def ▸ ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
    measure_ball_lt_top.ne
  have hvol : ∀ (y : Euclid m) (ρ : ℝ), 0 < ρ → volume.real (ball y ρ) = ρ ^ m * ω := by
    intro y ρ hρ
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume y hρ, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hω_def]
  -- the constant `C = 16^{m+2} + C₀` with `C₀ = 144 ω 2ᵐ m k C_H²`
  obtain ⟨C₀, hC₀_def⟩ : ∃ C₀ : ℝ, 144 * ω * 2 ^ m * ((m : ℝ) * k) * CH ^ 2 = C₀ := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := hC₀_def ▸ by positivity
  have h16 : (0 : ℝ) < 16 ^ (m + 2) := by positivity
  refine ⟨16 ^ (m + 2) + C₀, by linarith, ?_⟩
  intro x₀ R h hR hh hΔ hint r hr hrR
  -- `h` is `C¹` on the open ball `B = B_R(x₀)`
  have hB : IsOpen (ball x₀ R) := isOpen_ball
  have hh1 : ContDiffOn ℝ 1 h (ball x₀ R) := by exact_mod_cast hh 1
  have hDcont : ContinuousOn (fderiv ℝ h) (ball x₀ R) :=
    hh1.continuousOn_fderiv_of_isOpen hB le_rfl
  have hDh : ∀ y ∈ ball x₀ R, HasFDerivAt h (fderiv ℝ h y) y := fun y hy =>
    ((hh1.differentiableOn one_ne_zero).differentiableAt (hB.mem_nhds hy)).hasFDerivAt
  -- `Σⱼ ‖(Dh − c) eⱼ‖² ≤ 2 Σⱼ ‖Dh eⱼ‖² + 2 Σⱼ ‖c eⱼ‖²` is integrable on `B` for every `c`
  have hintc : ∀ c : Euclid m →L[ℝ] Euclid k, IntegrableOn (fun y => ∑ j : Fin m,
      ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) := by
    intro c
    have hg : IntegrableOn (fun y => 2 * ∑ j : Fin m,
        ‖fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 +
        ∑ j : Fin m, 2 * ‖c (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x₀ R) :=
      (hint.const_mul 2).add (integrableOn_const measure_ball_lt_top.ne)
    refine Integrable.mono' hg ?_ (ae_restrict_of_forall_mem measurableSet_ball fun y _ => ?_)
    · exact ContinuousOn.aestronglyMeasurable (continuousOn_finsetSum _ fun j _ =>
        ((hDcont.sub continuousOn_const).clm_apply continuousOn_const).norm.pow 2)
        measurableSet_ball
    · rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _), Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 := norm_sub_le (fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ)))
        (c (EuclideanSpace.single j (1 : ℝ)))
      rw [sub_apply]
      nlinarith [norm_nonneg (fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ)) -
        c (EuclideanSpace.single j (1 : ℝ))), norm_nonneg (fderiv ℝ h y
        (EuclideanSpace.single j (1 : ℝ))), norm_nonneg (c (EuclideanSpace.single j (1 : ℝ))),
        sq_nonneg (‖fderiv ℝ h y (EuclideanSpace.single j (1 : ℝ))‖ -
        ‖c (EuclideanSpace.single j (1 : ℝ))‖)]
  -- the ball average minimizes `A ↦ ∫_{B_ρ(x₀)} Σⱼ ‖(Dh − A) eⱼ‖²` (for `ρ < R`): the cross
  -- terms `∫⟨(a − A) eⱼ, (Dh − a) eⱼ⟩` vanish since `∫_{B_ρ(x₀)} (Dh − a) = 0`
  have hmin : ∀ ρ : ℝ, 0 < ρ → ρ < R → ∀ A : Euclid m →L[ℝ] Euclid k,
      ∫ x in ball x₀ ρ, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ ρ, fderiv ℝ h z)
        (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
      ∫ x in ball x₀ ρ, ∑ j : Fin m,
        ‖(fderiv ℝ h x - A) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    intro ρ hρ hρR A
    have hcont : ContinuousOn (fderiv ℝ h) (closedBall x₀ ρ) :=
      hDcont.mono (closedBall_subset_ball hρR)
    have hDint : IntegrableOn (fderiv ℝ h) (ball x₀ ρ) :=
      (hcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hzero : ∀ j : Fin m, ∫ x in ball x₀ ρ,
        inner ℝ (((⨍ z in ball x₀ ρ, fderiv ℝ h z) - A) (EuclideanSpace.single j (1 : ℝ)))
          ((fderiv ℝ h x - ⨍ z in ball x₀ ρ, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))) =
        0 := by
      intro j
      have hi : Integrable (fun x => fderiv ℝ h x - ⨍ z in ball x₀ ρ, fderiv ℝ h z)
          (volume.restrict (ball x₀ ρ)) := hDint.sub (integrableOn_const measure_ball_lt_top.ne)
      have h1 := (innerSL ℝ (((⨍ z in ball x₀ ρ, fderiv ℝ h z) - A)
        (EuclideanSpace.single j (1 : ℝ)))).integral_comp_comm
        (hi.apply_continuousLinearMap (EuclideanSpace.single j (1 : ℝ)))
      simp only [innerSL_apply_apply] at h1
      rw [h1, ← ContinuousLinearMap.integral_apply hi,
        setAverage_sub_setAverage measure_ball_lt_top.ne]
      simp
    obtain ⟨a, ha⟩ : ∃ a, ⨍ z in ball x₀ ρ, fderiv ℝ h z = a := ⟨_, rfl⟩
    rw [ha] at hzero ⊢
    have hexp : ∀ x, ∑ j : Fin m, ‖(fderiv ℝ h x - A) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 =
        (∑ j : Fin m, ‖(fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 +
        ∑ j : Fin m, 2 * inner ℝ ((a - A) (EuclideanSpace.single j (1 : ℝ)))
          ((fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ)))) +
        ∑ j : Fin m, ‖(a - A) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
      intro x
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (fderiv ℝ h x - A) (EuclideanSpace.single j (1 : ℝ)) =
          (fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ)) +
          (a - A) (EuclideanSpace.single j (1 : ℝ)) := by
        simp only [sub_apply]; abel
      rw [this, norm_add_sq_real, real_inner_comm]
    simp only [hexp]
    have hI1 : Integrable (fun x => ∑ j : Fin m,
        ‖(fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (volume.restrict (ball x₀ ρ)) :=
      ((continuousOn_finsetSum _ fun j _ =>
        ((hcont.sub continuousOn_const).clm_apply continuousOn_const).norm.pow
          2).integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hI2 : ∀ j ∈ (Finset.univ : Finset (Fin m)), Integrable (fun x => 2 * inner ℝ
        ((a - A) (EuclideanSpace.single j (1 : ℝ)))
        ((fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ)))) (volume.restrict (ball x₀ ρ)) :=
      fun j _ => ((continuousOn_const.mul (continuousOn_const.inner
        ((hcont.sub continuousOn_const).clm_apply continuousOn_const))).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hI12 : Integrable (fun x => ∑ j : Fin m,
        ‖(fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 +
        ∑ j : Fin m, 2 * inner ℝ ((a - A) (EuclideanSpace.single j (1 : ℝ)))
          ((fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ)))) (volume.restrict (ball x₀ ρ)) :=
      hI1.add (integrable_finsetSum _ hI2)
    rw [integral_add hI12 (integrableOn_const measure_ball_lt_top.ne),
      integral_add hI1 (integrable_finsetSum _ hI2), integral_finsetSum _ hI2, setIntegral_const]
    simp only [integral_const_mul, hzero, mul_zero, Finset.sum_const_zero, add_zero, smul_eq_mul]
    have : 0 ≤ volume.real (ball x₀ ρ) *
        ∑ j : Fin m, ‖(a - A) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by positivity
    linarith
  -- `‖L‖² ≤ Σⱼ (L eⱼ)²` (Cauchy–Schwarz) and `‖(e_κ^*) ∘ T‖² ≤ Σⱼ ‖T eⱼ‖²`
  have hopn : ∀ L : Euclid m →L[ℝ] ℝ,
      ‖L‖ ^ 2 ≤ ∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2 := by
    intro L
    have hS : 0 ≤ ∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2 := by positivity
    have hle : ‖L‖ ≤ Real.sqrt (∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2) := by
      refine L.opNorm_le_bound (Real.sqrt_nonneg _) fun u => ?_
      have hu : L u = ∑ j : Fin m, u j * L (EuclideanSpace.single j (1 : ℝ)) := by
        conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr u]
        simp [EuclideanSpace.basisFun_apply, map_sum, map_smul]
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => u j)
        (fun j => L (EuclideanSpace.single j (1 : ℝ)))
      calc ‖L u‖
          = Real.sqrt ((∑ j : Fin m, u j * L (EuclideanSpace.single j (1 : ℝ))) ^ 2) := by
            rw [hu, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
        _ ≤ Real.sqrt ((∑ j : Fin m, u j ^ 2) *
            ∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hcs
        _ = Real.sqrt (∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2) * ‖u‖ := by
            rw [Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_comm,
              ← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg u)]
    calc ‖L‖ ^ 2 ≤ Real.sqrt (∑ j : Fin m, L (EuclideanSpace.single j (1 : ℝ)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = _ := Real.sq_sqrt hS
  have hcomp : ∀ (T : Euclid m →L[ℝ] Euclid k) (κ : Fin k),
      ‖(EuclideanSpace.proj κ).comp T‖ ^ 2 ≤
        ∑ j : Fin m, ‖T (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
    intro T κ
    refine (hopn _).trans (Finset.sum_le_sum fun j _ => ?_)
    have h1 : ‖T (EuclideanSpace.single j (1 : ℝ)) κ‖ ≤ ‖T (EuclideanSpace.single j (1 : ℝ))‖ :=
      PiLp.norm_apply_le _ κ
    rw [Real.norm_eq_abs] at h1
    calc ((EuclideanSpace.proj κ).comp T) (EuclideanSpace.single j (1 : ℝ)) ^ 2
        = |T (EuclideanSpace.single j (1 : ℝ)) κ| ^ 2 := by rw [sq_abs]; rfl
      _ ≤ ‖T (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- interior estimates for the normalized components (Simon Ch. 5, 3.2–3.4): if
  -- `∫_B Σⱼ ‖(Dh − c) eⱼ‖² ≤ Λ`, `λ = √(Λ/(R/2)ᵐ)` and `x ∈ B_{R/2}(x₀)`, then
  -- `|((Dh(x) − c) eⱼ)^κ| ≤ C_H λ` and `|h^κ(x + v) − h^κ(x) − (Dh(x) v)^κ| ≤ C_H λ ‖v‖²/(R/2)`
  -- for `‖v‖ ≤ R/8`, by the accepted estimates for `v ↦ λ⁻¹ (h − c)^κ(x + v)` on `B_{R/2}(0)`
  have core : ∀ (c : Euclid m →L[ℝ] Euclid k) (Λ : ℝ), 0 < Λ →
      ∫ y in ball x₀ R, ∑ j : Fin m,
        ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Λ →
      ∀ (κ : Fin k) (x : Euclid m), x ∈ ball x₀ (R / 2) →
        (∀ j : Fin m, |(fderiv ℝ h x - c) (EuclideanSpace.single j (1 : ℝ)) κ| ≤
          CH * Real.sqrt (Λ / (R / 2) ^ m)) ∧
        ∀ v : Euclid m, ‖v‖ ≤ R / 8 → |h (x + v) κ - h x κ - fderiv ℝ h x v κ| ≤
          CH * Real.sqrt (Λ / (R / 2) ^ m) * ‖v‖ ^ 2 / (R / 2) := by
    intro c Λ hΛ hcΛ κ x hx
    obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, Real.sqrt (Λ / (R / 2) ^ m) = lam := ⟨_, rfl⟩
    rw [hlam_def]
    have hR2 : 0 < R / 2 := half_pos hR
    have hlam : 0 < lam := hlam_def ▸ Real.sqrt_pos.2 (by positivity)
    have hlam2 : lam ^ 2 = Λ / (R / 2) ^ m := hlam_def ▸ Real.sq_sqrt (by positivity)
    -- `G = λ⁻¹ (h − c)^κ` is smooth and harmonic on `B`
    obtain ⟨M, hM⟩ : ∃ M : Euclid k →L[ℝ] ℝ, lam⁻¹ • EuclideanSpace.proj κ = M := ⟨_, rfl⟩
    have hMv : ∀ w : Euclid k, M w = lam⁻¹ * w κ := fun w => by rw [← hM]; rfl
    obtain ⟨G, hG⟩ : ∃ G : Euclid m → ℝ, (fun y => M (h y - c y)) = G := ⟨_, rfl⟩
    have hGs : ∀ n : ℕ, ContDiffOn ℝ n G (ball x₀ R) := fun n => by
      rw [← hG]; exact M.contDiff.comp_contDiffOn ((hh n).sub c.contDiff.contDiffOn)
    have hGd : ∀ y ∈ ball x₀ R, HasFDerivAt G (M.comp (fderiv ℝ h y - c)) y := fun y hy => by
      rw [← hG]; exact M.hasFDerivAt.comp y ((hDh y hy).sub c.hasFDerivAt)
    have hGΔ : ∀ y ∈ ball x₀ R, ∑ i : Fin m, iteratedFDeriv ℝ 2 G y
        ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
      intro y hy
      have h2 : ContDiffAt ℝ 2 h y := (hh 2).contDiffAt (hB.mem_nhds hy)
      have h2c : ContDiffAt ℝ 2 (h - ⇑c) y := h2.sub c.contDiff.contDiffAt
      have hc2 : iteratedFDeriv ℝ 2 c y = 0 := by
        ext v
        rw [iteratedFDeriv_two_apply]
        have : fderiv ℝ (⇑c) = fun _ => c := funext fun _ => c.fderiv
        simp [this]
      have hG2 : iteratedFDeriv ℝ 2 G y =
          M.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 h y) := by
        rw [← hG, show (fun y => M (h y - c y)) = M ∘ (h - ⇑c) from rfl,
          M.iteratedFDeriv_comp_left h2c le_rfl,
          iteratedFDeriv_sub_apply h2 c.contDiff.contDiffAt, hc2, sub_zero]
      simp only [hG2, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
      rw [← map_sum, hΔ y hy, map_zero]
    -- the translate `F = G(x + ·)` is smooth on `U = {w | x + w ∈ B} ⊇ B̄_{R/2}(0)`
    have hxB : ∀ v ∈ closedBall (0 : Euclid m) (R / 2), x + v ∈ ball x₀ R := by
      intro v hv
      rw [mem_closedBall_zero_iff] at hv
      rw [mem_ball] at hx ⊢
      calc dist (x + v) x₀ ≤ dist (x + v) x + dist x x₀ := dist_triangle _ _ _
        _ = ‖v‖ + dist x x₀ := by rw [dist_self_add_left]
        _ < R := by linarith
    have hU : IsOpen ((fun w => x + w) ⁻¹' ball x₀ R) :=
      isOpen_ball.preimage (continuous_const.add continuous_id)
    have hclU : closedBall (0 : Euclid m) (R / 2) ⊆ (fun w => x + w) ⁻¹' ball x₀ R :=
      fun v hv => hxB v hv
    have hFsU : ∀ n : ℕ, ContDiffOn ℝ n (fun w => G (x + w)) ((fun w => x + w) ⁻¹' ball x₀ R) :=
      fun n => (hGs n).comp (contDiffOn_const.add contDiffOn_id) fun w hw => hw
    have hFs : ∀ n : ℕ, ContDiffOn ℝ n (fun w => G (x + w)) (ball (0 : Euclid m) (R / 2)) :=
      fun n => (hFsU n).mono (ball_subset_closedBall.trans hclU)
    have hF1 : ∀ v ∈ closedBall (0 : Euclid m) (R / 2),
        fderiv ℝ (fun w => G (x + w)) v = M.comp (fderiv ℝ h (x + v) - c) := fun v hv => by
      rw [fderiv_comp_add_left, (hGd _ (hxB v hv)).fderiv]
    have hFΔ : ∀ y ∈ ball (0 : Euclid m) (R / 2), ∑ i : Fin m,
        iteratedFDeriv ℝ 2 (fun w => G (x + w)) y
          ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] = 0 := by
      intro y hy
      simp only [iteratedFDeriv_comp_add_left]
      exact hGΔ _ (hxB y (ball_subset_closedBall hy))
    have hFsU1 : ContDiffOn ℝ 1 (fun w => G (x + w)) ((fun w => x + w) ⁻¹' ball x₀ R) := by
      exact_mod_cast hFsU 1
    have hDFcont :
        ContinuousOn (fderiv ℝ (fun w => G (x + w))) (closedBall (0 : Euclid m) (R / 2)) :=
      (hFsU1.continuousOn_fderiv_of_isOpen hU le_rfl).mono hclU
    have hDFint : IntegrableOn (fun v => ‖fderiv ℝ (fun w => G (x + w)) v‖ ^ 2)
        (ball (0 : Euclid m) (R / 2)) :=
      ((hDFcont.norm.pow 2).integrableOn_compact (isCompact_closedBall _ _)).mono_set
        ball_subset_closedBall
    have hF2int : IntegrableOn (fun v => G (x + v) ^ 2) (ball (0 : Euclid m) (R / 2)) :=
      ((((hFsU 0).continuousOn.mono hclU).pow 2).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    -- `‖DF(v)‖² ≤ λ⁻² Q(x + v)` with `Q = Σⱼ ‖(Dh − c) eⱼ‖²`, and `∫_{B_{R/2}(0)} Q(x + ·) ≤ Λ`
    have hDFle : ∀ v ∈ closedBall (0 : Euclid m) (R / 2),
        ‖fderiv ℝ (fun w => G (x + w)) v‖ ^ 2 ≤
          (lam ^ 2)⁻¹ * ∑ j : Fin m,
            ‖(fderiv ℝ h (x + v) - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
      intro v hv
      rw [hF1 v hv, ← hM, ContinuousLinearMap.smul_comp, norm_smul, mul_pow, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hlam), inv_pow]
      exact mul_le_mul_of_nonneg_left (hcomp _ κ) (by positivity)
    have hQcont : ContinuousOn (fun v => ∑ j : Fin m,
        ‖(fderiv ℝ h (x + v) - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (closedBall (0 : Euclid m) (R / 2)) := by
      have : ContinuousOn (fun v => fderiv ℝ h (x + v)) (closedBall (0 : Euclid m) (R / 2)) :=
        hDcont.comp (continuousOn_const.add continuousOn_id) fun v hv => hxB v hv
      exact continuousOn_finsetSum _ fun j _ =>
        ((this.sub continuousOn_const).clm_apply continuousOn_const).norm.pow 2
    have hQx : ∫ v in ball (0 : Euclid m) (R / 2), ∑ j : Fin m,
        ‖(fderiv ℝ h (x + v) - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 =
        ∫ y in ball x (R / 2), ∑ j : Fin m,
          ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
      have hpre : (fun v => x + v) ⁻¹' ball x (R / 2) = ball (0 : Euclid m) (R / 2) := by
        ext v
        simp
      rw [← hpre]
      exact (measurePreserving_add_left volume x).setIntegral_preimage_emb
        (measurableEmbedding_addLeft x) (fun y => ∑ j : Fin m,
          ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x (R / 2))
    have hQle : ∫ y in ball x (R / 2), ∑ j : Fin m,
        ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ Λ := by
      refine le_trans (setIntegral_mono_set (hintc c) ?_ ?_) hcΛ
      · exact Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      · refine (ball_subset_ball' ?_).eventuallyLE
        rw [mem_ball] at hx
        linarith
    have hDFbound : ∫ v in ball (0 : Euclid m) (R / 2), ‖fderiv ℝ (fun w => G (x + w)) v‖ ^ 2 ≤
        (R / 2) ^ m := by
      calc ∫ v in ball (0 : Euclid m) (R / 2), ‖fderiv ℝ (fun w => G (x + w)) v‖ ^ 2
          ≤ ∫ v in ball (0 : Euclid m) (R / 2), (lam ^ 2)⁻¹ * ∑ j : Fin m,
              ‖(fderiv ℝ h (x + v) - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
            setIntegral_mono_on hDFint
              ((((hQcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
                ball_subset_closedBall)).const_mul _) measurableSet_ball
              fun v hv => hDFle v (ball_subset_closedBall hv)
        _ = (lam ^ 2)⁻¹ * ∫ y in ball x (R / 2), ∑ j : Fin m,
              ‖(fderiv ℝ h y - c) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
            rw [integral_const_mul, hQx]
        _ ≤ (lam ^ 2)⁻¹ * Λ := mul_le_mul_of_nonneg_left hQle (by positivity)
        _ = (R / 2) ^ m := by
            rw [hlam2]
            field_simp
    obtain ⟨-, hb, hc⟩ := hIE (R / 2) (fun w => G (x + w)) hR2 hFs hFΔ hDFint hDFbound hF2int
    have hDF0 : fderiv ℝ (fun w => G (x + w)) 0 = M.comp (fderiv ℝ h x - c) := by
      rw [hF1 0 (mem_closedBall_self hR2.le), add_zero]
    rw [hDF0] at hb hc
    have hGv : ∀ w, G w = lam⁻¹ * (h w κ - c w κ) := fun w => by
      rw [← hG]
      simp only [hMv]
      rfl
    constructor
    · intro j
      have h1 := (M.comp (fderiv ℝ h x - c)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
      have hnorm : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
      rw [hnorm, mul_one, ContinuousLinearMap.comp_apply, hMv, Real.norm_eq_abs, abs_mul,
        abs_of_pos (inv_pos.2 hlam)] at h1
      have h2 := h1.trans hb
      rw [inv_mul_le_iff₀ hlam] at h2
      linarith
    · intro v hv
      have h1 := hc v (by linarith)
      rw [hGv, hGv, add_zero, ContinuousLinearMap.comp_apply, hMv] at h1
      have hkey : lam⁻¹ * (h (x + v) κ - c (x + v) κ) - lam⁻¹ * (h x κ - c x κ) -
          lam⁻¹ * ((fderiv ℝ h x - c) v κ) =
          lam⁻¹ * (h (x + v) κ - h x κ - fderiv ℝ h x v κ) := by
        simp only [map_add, sub_apply, PiLp.add_apply, PiLp.sub_apply]
        ring
      rw [hkey, abs_mul, abs_of_pos (inv_pos.2 hlam), inv_mul_le_iff₀ hlam] at h1
      calc |h (x + v) κ - h x κ - fderiv ℝ h x v κ| ≤ lam * (CH * ‖v‖ ^ 2 / (R / 2)) := h1
        _ = CH * lam * ‖v‖ ^ 2 / (R / 2) := by ring
  -- `a ≤ αΛ` for all `Λ > b` gives `a ≤ αb`
  have squeeze : ∀ a b α : ℝ, 0 < α → (∀ Λ, b < Λ → a ≤ α * Λ) → a ≤ α * b := by
    intro a b α hα H
    refine le_of_forall_pos_le_add fun ε hε => ?_
    calc a ≤ α * (b + ε / α) := H _ (by linarith [div_pos hε hα])
      _ = α * b + ε := by field_simp
  rcases le_or_gt r (R / 16) with hsmall | hlarge
  · -- small radii `r ≤ R/16`
    have hrR' : r < R := by linarith
    have hsub2 : ∀ x ∈ ball x₀ r, x ∈ ball x₀ (R / 2) := fun x hx =>
      ball_subset_ball (by linarith) hx
    have hx₀ : x₀ ∈ ball x₀ (R / 2) := mem_ball_self (by linarith)
    constructor
    · -- Campanato decay: `Dh` is `6C_Hλr/(R/2)`-close to `Dh(x₀)` on `B_r(x₀)`
      obtain ⟨a, ha⟩ : ∃ a, ⨍ z in ball x₀ R, fderiv ℝ h z = a := ⟨_, rfl⟩
      rw [ha]
      have hP : 0 ≤ ∫ x in ball x₀ R, ∑ j : Fin m,
          ‖(fderiv ℝ h x - a) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        setIntegral_nonneg measurableSet_ball fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      refine squeeze _ _ _ (by positivity) fun Λ hΛ => ?_
      have hΛ0 : 0 < Λ := hP.trans_lt hΛ
      have hc := core a Λ hΛ0 hΛ.le
      obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, Real.sqrt (Λ / (R / 2) ^ m) = lam := ⟨_, rfl⟩
      simp only [hlam_def] at hc
      have hlam2 : lam ^ 2 = Λ / (R / 2) ^ m := hlam_def ▸ Real.sq_sqrt (by positivity)
      have hlam : 0 ≤ lam := hlam_def ▸ Real.sqrt_nonneg _
      have hK : 0 ≤ CH * lam / (R / 2) := by positivity
      -- three Taylor expansions (centres `x`, `x₀`) give the Lipschitz bound
      have hpt : ∀ x ∈ ball x₀ r, ∀ j : Fin m, ∀ κ : Fin k,
          |(fderiv ℝ h x - fderiv ℝ h x₀) (EuclideanSpace.single j (1 : ℝ)) κ| ≤
            6 * (CH * lam / (R / 2)) * r := by
        intro x hx j κ
        obtain ⟨K, hK_def⟩ : ∃ K : ℝ, CH * lam / (R / 2) = K := ⟨_, rfl⟩
        have hK : 0 ≤ K := hK_def ▸ hK
        rw [hK_def]
        have hTay : ∀ y ∈ ball x₀ (R / 2), ∀ v : Euclid m, ‖v‖ ≤ R / 8 →
            |h (y + v) κ - h y κ - fderiv ℝ h y v κ| ≤ K * ‖v‖ ^ 2 := fun y hy v hv => by
          rw [← hK_def, div_mul_eq_mul_div]
          exact (hc κ y hy).2 v hv
        have hxr : ‖x - x₀‖ < r := by rwa [mem_ball, dist_eq_norm] at hx
        have hn1 : ‖r • EuclideanSpace.single j (1 : ℝ)‖ = r := by
          rw [norm_smul, Real.norm_of_nonneg hr.le]
          simp
        have hn2 : ‖x - x₀ + r • EuclideanSpace.single j (1 : ℝ)‖ ≤ 2 * r :=
          (norm_add_le _ _).trans (by rw [hn1]; linarith)
        have hT1 := hTay x (hsub2 x hx) (r • EuclideanSpace.single j (1 : ℝ))
          (by rw [hn1]; linarith)
        have hT2 := hTay x₀ hx₀ (x - x₀ + r • EuclideanSpace.single j (1 : ℝ)) (by linarith)
        have hT3 := hTay x₀ hx₀ (x - x₀) (by linarith)
        rw [show x₀ + (x - x₀ + r • EuclideanSpace.single j (1 : ℝ)) =
          x + r • EuclideanSpace.single j (1 : ℝ) by abel, map_add, map_smul, PiLp.add_apply,
          PiLp.smul_apply, smul_eq_mul] at hT2
        rw [show x₀ + (x - x₀) = x by abel] at hT3
        rw [hn1, map_smul, PiLp.smul_apply, smul_eq_mul] at hT1
        have hb2 : K * ‖x - x₀ + r • EuclideanSpace.single j (1 : ℝ)‖ ^ 2 ≤ K * (2 * r) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn2 2) hK
        have hb3 : K * ‖x - x₀‖ ^ 2 ≤ K * r ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hxr.le 2) hK
        rw [sub_apply, PiLp.sub_apply]
        have hmul : |r * (fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ)) κ -
            fderiv ℝ h x₀ (EuclideanSpace.single j (1 : ℝ)) κ)| ≤ r * (6 * K * r) := by
          rw [abs_le] at hT1 hT2 hT3 ⊢
          constructor <;> linarith [hT1.1, hT1.2, hT2.1, hT2.2, hT3.1, hT3.2]
        rw [abs_mul, abs_of_pos hr] at hmul
        exact le_of_mul_le_mul_left hmul hr
      have hsum : ∀ x ∈ ball x₀ r, ∑ j : Fin m,
          ‖(fderiv ℝ h x - fderiv ℝ h x₀) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
            m * k * (6 * (CH * lam / (R / 2)) * r) ^ 2 := by
        intro x hx
        calc ∑ j : Fin m, ‖(fderiv ℝ h x - fderiv ℝ h x₀) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            = ∑ j : Fin m, ∑ κ : Fin k,
                ((fderiv ℝ h x - fderiv ℝ h x₀) (EuclideanSpace.single j (1 : ℝ)) κ) ^ 2 := by
              simp only [EuclideanSpace.real_norm_sq_eq]
          _ ≤ ∑ j : Fin m, ∑ κ : Fin k, (6 * (CH * lam / (R / 2)) * r) ^ 2 :=
              Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun κ _ =>
                sq_le_sq' (abs_le.1 (hpt x hx j κ)).1 (abs_le.1 (hpt x hx j κ)).2
          _ = m * k * (6 * (CH * lam / (R / 2)) * r) ^ 2 := by simp; ring
      calc ∫ x in ball x₀ r, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ r, fderiv ℝ h z)
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ ∫ x in ball x₀ r, ∑ j : Fin m,
              ‖(fderiv ℝ h x - fderiv ℝ h x₀) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
            hmin r hr hrR' _
        _ ≤ ∫ x in ball x₀ r, ((m : ℝ) * k * (6 * (CH * lam / (R / 2)) * r) ^ 2) :=
            integral_mono_of_nonneg
              (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (integrableOn_const measure_ball_lt_top.ne)
              (ae_restrict_of_forall_mem measurableSet_ball hsum)
        _ = r ^ m * ω * ((m : ℝ) * k * (6 * (CH * lam / (R / 2)) * r) ^ 2) := by
            rw [setIntegral_const, hvol x₀ r hr, smul_eq_mul]
        _ = C₀ * (r / R) ^ (m + 2) * Λ := by
            rw [← hC₀_def]
            have hsq : (6 * (CH * lam / (R / 2)) * r) ^ 2 =
                144 * CH ^ 2 * lam ^ 2 * r ^ 2 / R ^ 2 := by
              field_simp
              ring
            rw [hsq, hlam2, div_pow, div_pow]
            field_simp
            ring
        _ ≤ (16 ^ (m + 2) + C₀) * (r / R) ^ (m + 2) * Λ := by
            gcongr
            linarith
    · -- Morrey decay: `|Dh|² ≤ m k C_H² λ²` on `B_r(x₀)`
      have hP : 0 ≤ ∫ x in ball x₀ R, ∑ j : Fin m,
          ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        setIntegral_nonneg measurableSet_ball fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      refine squeeze _ _ _ (by positivity) fun Λ hΛ => ?_
      have hΛ0 : 0 < Λ := hP.trans_lt hΛ
      have hc := core 0 Λ hΛ0 (by simpa only [sub_zero] using hΛ.le)
      obtain ⟨lam, hlam_def⟩ : ∃ lam : ℝ, Real.sqrt (Λ / (R / 2) ^ m) = lam := ⟨_, rfl⟩
      simp only [hlam_def, sub_zero] at hc
      have hlam2 : lam ^ 2 = Λ / (R / 2) ^ m := hlam_def ▸ Real.sq_sqrt (by positivity)
      have hsum : ∀ x ∈ ball x₀ r, ∑ j : Fin m,
          ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ m * k * (CH * lam) ^ 2 := by
        intro x hx
        calc ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            = ∑ j : Fin m, ∑ κ : Fin k,
                (fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ)) κ) ^ 2 := by
              simp only [EuclideanSpace.real_norm_sq_eq]
          _ ≤ ∑ j : Fin m, ∑ κ : Fin k, (CH * lam) ^ 2 :=
              Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun κ _ =>
                sq_le_sq' (abs_le.1 ((hc κ x (hsub2 x hx)).1 j)).1
                  (abs_le.1 ((hc κ x (hsub2 x hx)).1 j)).2
          _ = m * k * (CH * lam) ^ 2 := by simp; ring
      calc ∫ x in ball x₀ r, ∑ j : Fin m, ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
          ≤ ∫ x in ball x₀ r, ((m : ℝ) * k * (CH * lam) ^ 2) :=
            integral_mono_of_nonneg
              (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (integrableOn_const measure_ball_lt_top.ne)
              (ae_restrict_of_forall_mem measurableSet_ball hsum)
        _ = r ^ m * ω * ((m : ℝ) * k * (CH * lam) ^ 2) := by
            rw [setIntegral_const, hvol x₀ r hr, smul_eq_mul]
        _ = (ω * 2 ^ m * ((m : ℝ) * k) * CH ^ 2) * (r / R) ^ m * Λ := by
            rw [mul_pow, hlam2, div_pow, div_pow]
            field_simp
        _ ≤ (16 ^ (m + 2) + C₀) * (r / R) ^ m * Λ := by
            gcongr
            rw [← hC₀_def]
            have : 0 ≤ ω * 2 ^ m * ((m : ℝ) * k) * CH ^ 2 := by positivity
            linarith
  · -- large radii `R/16 < r ≤ R`: compare with `B_R(x₀)` directly
    have h16r : 1 ≤ 16 * (r / R) := by
      rw [mul_div_assoc', le_div_iff₀ hR]
      linarith
    have hpow : ∀ p : ℕ, 1 ≤ (16 : ℝ) ^ p * (r / R) ^ p := fun p => by
      rw [← mul_pow]
      exact one_le_pow₀ h16r
    constructor
    · have hP : 0 ≤ ∫ x in ball x₀ R, ∑ j : Fin m,
          ‖(fderiv ℝ h x - ⨍ z in ball x₀ R, fderiv ℝ h z) (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        setIntegral_nonneg measurableSet_ball fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hΦ : ∫ x in ball x₀ r, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ r, fderiv ℝ h z)
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
          ∫ x in ball x₀ R, ∑ j : Fin m, ‖(fderiv ℝ h x - ⨍ z in ball x₀ R, fderiv ℝ h z)
            (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
        rcases eq_or_lt_of_le hrR with rfl | hlt
        · exact le_rfl
        · exact (hmin r hr hlt _).trans (setIntegral_mono_set (hintc _)
            (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (ball_subset_ball hrR).eventuallyLE)
      calc _ ≤ _ := hΦ
        _ ≤ 16 ^ (m + 2) * (r / R) ^ (m + 2) * _ := le_mul_of_one_le_left hP (hpow _)
        _ ≤ (16 ^ (m + 2) + C₀) * (r / R) ^ (m + 2) * _ := by gcongr; linarith
    · have hP : 0 ≤ ∫ x in ball x₀ R, ∑ j : Fin m,
          ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
        setIntegral_nonneg measurableSet_ball fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc _ ≤ ∫ x in ball x₀ R, ∑ j : Fin m,
            ‖fderiv ℝ h x (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 :=
            setIntegral_mono_set hint
              (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
              (ball_subset_ball hrR).eventuallyLE
        _ ≤ 16 ^ m * (r / R) ^ m * _ := le_mul_of_one_le_left hP (hpow _)
        _ ≤ (16 ^ (m + 2) + C₀) * (r / R) ^ m * _ := by
            gcongr
            have : (16 : ℝ) ^ m ≤ 16 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
            linarith
/-- **Campanato's method** (Giaquinta 1983, Ch. III, Lemma 2.1; Giaquinta–Martinazzi 2012, §5.1.1,
§5.3).  (I) Iteration lemma: for `γ = (a + b)/2` and `τ ≤ 1/2` with `2Aτ^{a−γ} ≤ 1`, `ε₀ = τ^a`,
one step gives `φ(τρ') ≤ τ^γ φ(ρ') + Bρ'^b`; by induction `φ(τʲρ) ≤ τ^{jb}(φ(ρ) + D)` with
`D = Bρ^bτ^{−b}/(1 − τ^{γ−b})`, and `τ^{j+1}ρ < r ≤ τʲρ` interpolates between the scales.
(II) Campanato's Hölder criterion: integrating `2a‖g‖ ≤ ‖g‖² + a²` gives
`‖⨍_s f − c‖² |s| ≤ ∫_s ‖f − c‖²`, so averages over `B_r(y) ⊆ B_ρ(x)` with `ρ ≤ 2r` differ by at
most `(2ᵐ/ω)^{1/2} √K ρ^α` (`|B_r| = ω rᵐ`); telescoping over `ρ 2⁻ʲ` and continuity give
`‖f(x) − ⨍_{B_ρ(x)} f‖ ≤ C₁ √K ρ^α`; comparing `B_d(y) ⊆ B_{2d}(x)`, `d = ‖x − y‖`, concludes. -/
theorem Submission.codim1_hcp_sr_campanato_lemmas : (∀ (A a b : ℝ), 0 ≤ A → 0 < b → b < a → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ (φ : ℝ → ℝ) (R₀ ε B : ℝ), 0 ≤ ε → ε ≤ ε₀ → 0 ≤ B → (∀ r : ℝ, 0 < r → r ≤ R₀ → 0 ≤ φ r) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ φ ρ) → (∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ A * ((r / ρ) ^ a + ε) * φ ρ + B * ρ ^ b) → ∀ r ρ : ℝ, 0 < r → r ≤ ρ → ρ ≤ R₀ → φ r ≤ C * ((r / ρ) ^ b * φ ρ + B * r ^ b)) ∧ (∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α ≤ 1 → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (f : Euclid m → (Euclid m →L[ℝ] Euclid k)) (x₀ : Euclid m) (R ρ₁ K : ℝ), 0 < R → 0 < ρ₁ → 0 ≤ K → ContinuousOn f (closedBall x₀ (R + ρ₁)) → (∀ x ∈ ball x₀ R, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∫ z in ball x ρ, ‖f z - ⨍ z' in ball x ρ, f z'‖ ^ 2 ≤ K * ρ ^ ((m : ℝ) + 2 * α)) → ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ‖x - y‖ ≤ ρ₁ / 2 → ‖f x - f y‖ ≤ C₀ * Real.sqrt K * ‖x - y‖ ^ α) := by
  refine ⟨?_, ?_⟩
  · intro A a b hA hb hba
    set γ : ℝ := (a + b) / 2 with hγ_def
    have hag : 0 < a - γ := by rw [hγ_def]; linarith
    have hgb : 0 < γ - b := by rw [hγ_def]; linarith
    set τ : ℝ := min (1 / 2) (((2 * A + 1)⁻¹) ^ (1 / (a - γ)))
    have hτpos : 0 < τ := lt_min (by norm_num) (Real.rpow_pos_of_pos (by positivity) _)
    have hτlt1 : τ < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hτA : 2 * A * τ ^ (a - γ) ≤ 1 := by
      have h1 : τ ^ (a - γ) ≤ (2 * A + 1)⁻¹ := by
        calc τ ^ (a - γ) ≤ (((2 * A + 1)⁻¹) ^ (1 / (a - γ))) ^ (a - γ) :=
              Real.rpow_le_rpow hτpos.le (min_le_right _ _) hag.le
          _ = (2 * A + 1)⁻¹ := by
              rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hag.ne', Real.rpow_one]
      calc 2 * A * τ ^ (a - γ) ≤ 2 * A * (2 * A + 1)⁻¹ := by gcongr
        _ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one (by positivity)]
            linarith
    set t : ℝ := τ ^ b with ht_def
    set q : ℝ := τ ^ (γ - b) with hq_def
    have htpos : 0 < t := Real.rpow_pos_of_pos hτpos _
    have hqpos : 0 < q := Real.rpow_pos_of_pos hτpos _
    have hqlt1 : q < 1 := Real.rpow_lt_one hτpos.le hτlt1 hgb
    have hqt : q * t = τ ^ γ := by
      rw [hq_def, ht_def, ← Real.rpow_add hτpos, sub_add_cancel]
    have hAτ : ∀ ε : ℝ, ε ≤ τ ^ a → A * (τ ^ a + ε) ≤ q * t := by
      intro ε hε
      have hsplit : τ ^ a = τ ^ (a - γ) * τ ^ γ := by
        rw [← Real.rpow_add hτpos, sub_add_cancel]
      have hτγ : 0 < τ ^ γ := Real.rpow_pos_of_pos hτpos _
      calc A * (τ ^ a + ε) ≤ A * (τ ^ a + τ ^ a) := by gcongr
        _ = (2 * A * τ ^ (a - γ)) * τ ^ γ := by rw [hsplit]; ring
        _ ≤ 1 * τ ^ γ := by gcongr
        _ = q * t := by rw [one_mul, hqt]
    have hC : 0 < 1 / t + 1 / (t ^ 2 * (1 - q)) :=
      add_pos (one_div_pos.2 htpos) (one_div_pos.2 (mul_pos (pow_pos htpos 2) (by linarith)))
    refine ⟨τ ^ a, 1 / t + 1 / (t ^ 2 * (1 - q)), Real.rpow_pos_of_pos hτpos _, hC, ?_⟩
    intro φ R₀ ε B hε0 hεle hB hφnn hφmono hφit r ρ hr hrρ hρR
    have hρ : 0 < ρ := hr.trans_le hrρ
    -- one step of the iteration: `φ(τρ') ≤ τ^γ φ(ρ') + Bρ'^b`
    have step : ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ R₀ → φ (τ * ρ') ≤ q * t * φ ρ' + B * ρ' ^ b := by
      intro ρ' hρ' hρ'R
      have h := hφit (τ * ρ') ρ' (mul_pos hτpos hρ')
        (mul_le_of_le_one_left hρ'.le hτlt1.le) hρ'R
      rw [mul_div_cancel_right₀ τ hρ'.ne'] at h
      calc φ (τ * ρ') ≤ A * (τ ^ a + ε) * φ ρ' + B * ρ' ^ b := h
        _ ≤ q * t * φ ρ' + B * ρ' ^ b := by
            have := mul_le_mul_of_nonneg_right (hAτ ε hεle) (hφnn ρ' hρ' hρ'R)
            linarith
    set D : ℝ := B * ρ ^ b / (t * (1 - q)) with hD_def
    have h1q : 0 < 1 - q := by linarith
    have hD : q * D + B * ρ ^ b / t = D := by
      rw [hD_def]
      field_simp
      ring
    have hφρ : 0 ≤ φ ρ := hφnn ρ hρ hρR
    have hDnn : 0 ≤ D :=
      div_nonneg (mul_nonneg hB (Real.rpow_nonneg hρ.le _)) (mul_nonneg htpos.le h1q.le)
    have hτjR : ∀ j : ℕ, τ ^ j * ρ ≤ R₀ := fun j =>
      (mul_le_of_le_one_left hρ.le (pow_le_one₀ hτpos.le hτlt1.le)).trans hρR
    -- iteration: `φ(τ^j ρ) ≤ t^j (φ(ρ) + D)`
    have iter : ∀ j : ℕ, φ (τ ^ j * ρ) ≤ t ^ j * (φ ρ + D) := by
      intro j
      induction j with
      | zero => simp; linarith
      | succ j ih =>
        have hτj : 0 < τ ^ j * ρ := mul_pos (pow_pos hτpos j) hρ
        have h := step (τ ^ j * ρ) hτj (hτjR j)
        rw [show τ * (τ ^ j * ρ) = τ ^ (j + 1) * ρ by ring,
          Real.mul_rpow (pow_nonneg hτpos.le j) hρ.le, ← Real.rpow_pow_comm hτpos.le] at h
        calc φ (τ ^ (j + 1) * ρ) ≤ q * t * φ (τ ^ j * ρ) + B * (t ^ j * ρ ^ b) := h
          _ ≤ q * t * (t ^ j * (φ ρ + D)) + B * (t ^ j * ρ ^ b) := by
              gcongr
          _ = t ^ (j + 1) * (q * (φ ρ + D) + B * ρ ^ b / t) := by
              field_simp
              ring
          _ ≤ t ^ (j + 1) * (φ ρ + D) := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_pos htpos _).le
              have hqφ : q * φ ρ ≤ φ ρ := mul_le_of_le_one_left hφρ hqlt1.le
              linarith
    -- interpolation between consecutive scales
    obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hρ)
      ((div_le_one hρ).2 hrρ) hτpos hτlt1
    have hrj : r ≤ τ ^ j * ρ := (div_le_iff₀ hρ).1 hj2
    have h2 : t ^ (j + 1) ≤ (r / ρ) ^ b := by
      rw [ht_def, Real.rpow_pow_comm hτpos.le]
      exact Real.rpow_le_rpow (pow_nonneg hτpos.le _) hj1.le hb.le
    have h3 : t ^ j ≤ (r / ρ) ^ b / t := by
      rw [le_div_iff₀ htpos, ← pow_succ]
      exact h2
    have hrρb : (r / ρ) ^ b * ρ ^ b = r ^ b := by
      rw [← Real.mul_rpow (div_pos hr hρ).le hρ.le, div_mul_cancel₀ r hρ.ne']
    have h4 : 0 ≤ (r / ρ) ^ b * φ ρ := mul_nonneg (Real.rpow_nonneg (div_pos hr hρ).le _) hφρ
    have h5 : 0 ≤ B * r ^ b := mul_nonneg hB (Real.rpow_nonneg hr.le _)
    have h6 : 0 ≤ 1 / t := (one_div_pos.2 htpos).le
    have h7 : 0 ≤ 1 / (t ^ 2 * (1 - q)) := (one_div_pos.2 (mul_pos (pow_pos htpos 2) h1q)).le
    calc φ r ≤ φ (τ ^ j * ρ) := hφmono r (τ ^ j * ρ) hr hrj (hτjR j)
      _ ≤ t ^ j * (φ ρ + D) := iter j
      _ ≤ (r / ρ) ^ b / t * (φ ρ + D) := by gcongr
      _ = 1 / t * ((r / ρ) ^ b * φ ρ) + 1 / (t ^ 2 * (1 - q)) * (B * r ^ b) := by
          rw [hD_def, ← hrρb]
          field_simp
      _ ≤ (1 / t + 1 / (t ^ 2 * (1 - q))) * ((r / ρ) ^ b * φ ρ + B * r ^ b) := by
          linarith [mul_nonneg h6 h5, mul_nonneg h7 h4]
  · intro m k α hm hα _
    have : Nontrivial (Euclid m) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
    -- `|B_r(x)| = ω rᵐ`
    set ω : ℝ := (volume (ball (0 : Euclid m) 1)).toReal
    have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne'
      measure_ball_lt_top.ne
    have hvol : ∀ (x : Euclid m) (r : ℝ), 0 < r → volume.real (ball x r) = ω * r ^ m := by
      intro x r hr
      rw [measureReal_def, Measure.addHaar_ball volume x hr.le, finrank_euclideanSpace_fin,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_comm]
    set q : ℝ := (1 / 2 : ℝ) ^ α with hq_def
    have hq0 : 0 < q := Real.rpow_pos_of_pos one_half_pos _
    have hq1 : q < 1 := Real.rpow_lt_one one_half_pos.le one_half_lt_one hα
    set L : ℝ := Real.sqrt (2 ^ m / ω)
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hL2 : L ^ 2 = 2 ^ m / ω := Real.sq_sqrt (by positivity)
    set C₁ : ℝ := L / (1 - q)
    have hC₁ : 0 ≤ C₁ := div_nonneg hL (by linarith)
    have hLC : L = C₁ * (1 - q) := (div_mul_cancel₀ L (by linarith : (1 - q) ≠ 0)).symm
    refine ⟨(C₁ + L) * 2 ^ α + C₁ + 1, by positivity, ?_⟩
    intro f x₀ R ρ₁ K hR hρ₁ hK hf hcamp x hx y hy hxy
    -- integrability on the balls `B_ρ(x) ⊆ closedBall x₀ (R + ρ₁)`
    have hballsub : ∀ x ∈ ball x₀ R, ∀ ρ, ρ ≤ ρ₁ → ball x ρ ⊆ closedBall x₀ (R + ρ₁) := by
      intro x hx ρ hρ z hz
      rw [mem_closedBall]
      rw [mem_ball] at hx hz
      linarith [dist_triangle z x x₀]
    have hcpt : IsCompact (closedBall x₀ (R + ρ₁)) := isCompact_closedBall _ _
    have hfint : IntegrableOn f (closedBall x₀ (R + ρ₁)) := hf.integrableOn_compact hcpt
    have hf2int : ∀ c : Euclid m →L[ℝ] Euclid k,
        IntegrableOn (fun z => ‖f z - c‖ ^ 2) (closedBall x₀ (R + ρ₁)) := fun c =>
      ((hf.sub continuousOn_const).norm.pow 2).integrableOn_compact hcpt
    -- `|s| (⨍_s f - c) = ∫_s (f - c)`
    have avg_sub : ∀ (s : Set (Euclid m)) (c : Euclid m →L[ℝ] Euclid k), volume s ≠ 0 →
        volume s ≠ ⊤ → IntegrableOn f s →
        volume.real s • ((⨍ z in s, f z) - c) = ∫ z in s, (f z - c) := by
      intro s c h0 htop hfs
      have hV : volume.real s ≠ 0 := (ENNReal.toReal_pos h0 htop).ne'
      rw [integral_sub hfs (integrableOn_const htop enorm_ne_top), setIntegral_const, setAverage_eq,
        smul_sub, smul_inv_smul₀ hV]
    -- Cauchy–Schwarz in the form `‖⨍_s f - c‖² |s| ≤ ∫_s ‖f - c‖²`
    have key : ∀ (s : Set (Euclid m)) (c : Euclid m →L[ℝ] Euclid k) (M : ℝ), volume s ≠ 0 →
        volume s ≠ ⊤ → IntegrableOn f s → IntegrableOn (fun z => ‖f z - c‖ ^ 2) s →
        ∫ z in s, ‖f z - c‖ ^ 2 ≤ M → ‖(⨍ z in s, f z) - c‖ ^ 2 * volume.real s ≤ M := by
      intro s c M h0 htop hfs hf2 hM
      have hV : 0 < volume.real s := ENNReal.toReal_pos h0 htop
      set a := ‖(⨍ z in s, f z) - c‖ with ha_def
      have ha0 : 0 ≤ a := norm_nonneg _
      have h2 : a * volume.real s ≤ ∫ z in s, ‖f z - c‖ := by
        rw [ha_def, mul_comm, ← Real.norm_of_nonneg hV.le, ← norm_smul, avg_sub s c h0 htop hfs]
        exact norm_integral_le_integral_norm _
      have h3 : ∫ z in s, 2 * a * ‖f z - c‖ ≤ ∫ z in s, (‖f z - c‖ ^ 2 + a ^ 2) :=
        integral_mono ((hfs.sub (integrableOn_const htop enorm_ne_top)).norm.const_mul (2 * a))
          (hf2.add (integrableOn_const htop enorm_ne_top)) fun z =>
            show 2 * a * ‖f z - c‖ ≤ ‖f z - c‖ ^ 2 + a ^ 2 by linarith [sq_nonneg (‖f z - c‖ - a)]
      rw [integral_const_mul, integral_add hf2 (integrableOn_const htop enorm_ne_top),
        setIntegral_const, smul_eq_mul] at h3
      linarith [mul_le_mul_of_nonneg_left h2 ha0]
    -- comparison of averages over `B_r(y) ⊆ B_ρ(x)` with `ρ ≤ 2r`
    have cmp : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ → ∀ (y : Euclid m) (r : ℝ), 0 < r →
        ball y r ⊆ ball x ρ → ρ ≤ 2 * r →
        ‖(⨍ z in ball y r, f z) - ⨍ z in ball x ρ, f z‖ ≤ L * Real.sqrt K * ρ ^ α := by
      intro x hx ρ hρ hρρ₁ y r hr hsub h2r
      have hsub' : ball y r ⊆ closedBall x₀ (R + ρ₁) := hsub.trans (hballsub x hx ρ hρρ₁)
      have h := key (ball y r) (⨍ z in ball x ρ, f z) (K * ρ ^ ((m : ℝ) + 2 * α))
        (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne (hfint.mono_set hsub')
        ((hf2int _).mono_set hsub') <| by
          refine (setIntegral_mono_set ((hf2int _).mono_set (hballsub x hx ρ hρρ₁))
            (Eventually.of_forall fun z => sq_nonneg _) hsub.eventuallyLE).trans ?_
          exact hcamp x hx ρ hρ hρρ₁
      set N := ‖(⨍ z in ball y r, f z) - ⨍ z in ball x ρ, f z‖
      rw [hvol y r hr, Real.rpow_add hρ, Real.rpow_natCast, mul_comm 2 α, Real.rpow_mul hρ.le,
        Real.rpow_two] at h
      have hrm : ρ ^ m ≤ 2 ^ m * r ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ hρ.le h2r m
      have hrmpos : 0 < r ^ m := pow_pos hr m
      have hρα : 0 ≤ (ρ ^ α) ^ 2 := sq_nonneg _
      have h' : N ^ 2 * ω * r ^ m ≤ 2 ^ m * K * (ρ ^ α) ^ 2 * r ^ m := by
        calc N ^ 2 * ω * r ^ m = N ^ 2 * (ω * r ^ m) := by ring
          _ ≤ K * (ρ ^ m * (ρ ^ α) ^ 2) := h
          _ ≤ K * (2 ^ m * r ^ m * (ρ ^ α) ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrm hρα) hK
          _ = 2 ^ m * K * (ρ ^ α) ^ 2 * r ^ m := by ring
      have hN2 : N ^ 2 ≤ (L * Real.sqrt K * ρ ^ α) ^ 2 := by
        rw [mul_pow, mul_pow, hL2, Real.sq_sqrt hK, div_mul_eq_mul_div, div_mul_eq_mul_div,
          le_div_iff₀ hω]
        linarith [le_of_mul_le_mul_right h' hrmpos]
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hN2
    -- telescoping along the dyadic radii `ρ 2⁻ʲ`
    have tele : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ → ∀ j : ℕ,
        ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ ≤
          C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) := by
      intro x hx ρ hρ hρρ₁ j
      induction j with
      | zero => simp
      | succ j ih =>
        have hr : 0 < ρ * (1 / 2) ^ j := mul_pos hρ (pow_pos one_half_pos j)
        have hrρ : ρ * (1 / 2) ^ j ≤ ρ :=
          mul_le_of_le_one_right hρ.le (pow_le_one₀ one_half_pos.le one_half_lt_one.le)
        have hstep := cmp x hx (ρ * (1 / 2) ^ j) hr (hrρ.trans hρρ₁) x (ρ * (1 / 2) ^ j / 2)
          (half_pos hr) (ball_subset_ball (half_le_self hr.le)) (mul_div_cancel₀ _ two_ne_zero).ge
        rw [Real.mul_rpow hρ.le (pow_pos one_half_pos j).le, ← Real.rpow_pow_comm one_half_pos.le,
          ← hq_def] at hstep
        rw [show ρ * (1 / 2) ^ (j + 1) = ρ * (1 / 2) ^ j / 2 by rw [pow_succ]; ring]
        calc ‖(⨍ z in ball x (ρ * (1 / 2) ^ j / 2), f z) - ⨍ z in ball x ρ, f z‖
            ≤ ‖(⨍ z in ball x (ρ * (1 / 2) ^ j / 2), f z) - ⨍ z in ball x (ρ * (1 / 2) ^ j), f z‖
              + ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ L * Real.sqrt K * (ρ ^ α * q ^ j) + C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) :=
              add_le_add hstep ih
          _ = C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ (j + 1)) := by
              rw [hLC, pow_succ]
              ring
    -- `‖f(x) - ⨍_{B_ρ(x)} f‖ ≤ C₁ √K ρ^α`, letting the dyadic radii tend to `0`
    have hlim : ∀ x ∈ ball x₀ R, ∀ ρ, 0 < ρ → ρ ≤ ρ₁ →
        ‖f x - ⨍ z in ball x ρ, f z‖ ≤ C₁ * Real.sqrt K * ρ ^ α := by
      intro x hx ρ hρ hρρ₁
      have hcont : ContinuousAt f x := hf.continuousAt <| closedBall_mem_nhds_of_mem <| by
        rw [mem_ball] at hx ⊢
        linarith
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.1 hcont ε hε
      obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (div_pos hδ hρ) one_half_lt_one
      have hr : 0 < ρ * (1 / 2) ^ j := mul_pos hρ (pow_pos one_half_pos j)
      have hrδ : ρ * (1 / 2) ^ j < δ := by
        rw [lt_div_iff₀ hρ] at hj
        linarith
      have hrρ : ρ * (1 / 2) ^ j ≤ ρ :=
        mul_le_of_le_one_right hρ.le (pow_le_one₀ one_half_pos.le one_half_lt_one.le)
      have hV : 0 < volume.real (ball x (ρ * (1 / 2) ^ j)) :=
        ENNReal.toReal_pos (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne
      have hI := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := fun z => f z - f x)
        (C := ε) (s := ball x (ρ * (1 / 2) ^ j)) measure_ball_lt_top fun z hz => by
          rw [← dist_eq_norm]
          exact (hδε ((mem_ball.1 hz).trans hrδ)).le
      rw [← avg_sub _ (f x) (measure_ball_pos _ _ hr).ne' measure_ball_lt_top.ne
        (hfint.mono_set ((ball_subset_ball hrρ).trans (hballsub x hx ρ hρρ₁))), norm_smul,
        Real.norm_of_nonneg hV.le, mul_comm ε] at hI
      have h1 := le_of_mul_le_mul_left hI hV
      have h2 := tele x hx ρ hρ hρρ₁ j
      have hqj : 0 ≤ q ^ j := pow_nonneg hq0.le j
      have hC : 0 ≤ C₁ * Real.sqrt K * ρ ^ α := by positivity
      calc ‖f x - ⨍ z in ball x ρ, f z‖
          ≤ ‖f x - ⨍ z in ball x (ρ * (1 / 2) ^ j), f z‖
            + ‖(⨍ z in ball x (ρ * (1 / 2) ^ j), f z) - ⨍ z in ball x ρ, f z‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + C₁ * Real.sqrt K * ρ ^ α * (1 - q ^ j) := by
            rw [norm_sub_rev]
            exact add_le_add h1 h2
        _ ≤ C₁ * Real.sqrt K * ρ ^ α + ε := by linarith [mul_nonneg hC hqj]
    -- conclusion: compare `⨍_{B_d(y)} f` with `⨍_{B_{2d}(x)} f`, `d = ‖x - y‖`
    rcases (norm_nonneg (x - y)).eq_or_lt with hd | hd
    · rw [eq_comm, norm_eq_zero, sub_eq_zero] at hd
      subst hd
      simp only [sub_self, norm_zero]
      positivity
    · generalize hd_def : ‖x - y‖ = d at hxy hd ⊢
      have hd2 : 2 * d ≤ ρ₁ := by linarith
      have hsub : ball y d ⊆ ball x (2 * d) := by
        intro z hz
        rw [mem_ball] at hz ⊢
        have : dist y x = d := by rw [dist_eq_norm, norm_sub_rev, hd_def]
        linarith [dist_triangle z y x]
      have h2d : (2 * d) ^ α = 2 ^ α * d ^ α := Real.mul_rpow zero_le_two hd.le
      have e1 := hlim x hx (2 * d) (by linarith) hd2
      have e2 := cmp x hx (2 * d) (by linarith) hd2 y d hd hsub le_rfl
      have e3 := hlim y hy d hd (by linarith)
      rw [h2d] at e1 e2
      rw [norm_sub_rev] at e2 e3
      have hKd : 0 ≤ Real.sqrt K * d ^ α := by positivity
      calc ‖f x - f y‖
          ≤ ‖f x - ⨍ z in ball x (2 * d), f z‖ + ‖(⨍ z in ball x (2 * d), f z) - f y‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ‖f x - ⨍ z in ball x (2 * d), f z‖ + (‖(⨍ z in ball x (2 * d), f z) -
              ⨍ z in ball y d, f z‖ + ‖(⨍ z in ball y d, f z) - f y‖) :=
            add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub _ _ _)
        _ ≤ C₁ * Real.sqrt K * (2 ^ α * d ^ α) + (L * Real.sqrt K * (2 ^ α * d ^ α) +
              C₁ * Real.sqrt K * d ^ α) := add_le_add e1 (add_le_add e2 e3)
        _ ≤ ((C₁ + L) * 2 ^ α + C₁ + 1) * Real.sqrt K * d ^ α := by linarith [hKd]
set_option maxHeartbeats 1000000 in
/-- **Campanato's `C^{1,α}` estimate for `Δw = div F`** (the Schauder theory invoked in Simon's
proof of Ch. 5, 7.1; Giaquinta–Martinazzi 2012, §§5.1–5.4).  Harmonic replacement in `B_ρ(x)` and
harmonic decay give the comparison inequalities for `Φ(x,r) = ∫_{B_r(x)} |Dw - (Dw)_{x,r}|²` and
`Ψ(x,r) = ∫_{B_r(x)} |Dw|²` (Hilbert–Schmidt norms); a Caccioppoli estimate with the test map `η²w`
bounds `Ψ(x, R/8)`; the iteration lemma gives `Ψ ≲ r^{m-α}`, then `Φ ≲ r^{m+α}`, so `Dw` is
`α/2`-Hölder and bounded on `B_{3R/8}(x₀)`; a second Campanato pass gives `Φ ≲ r^{m+2α}`, and
Campanato's criterion yields the `α`-Hölder bound on `B_{R/4}(x₀)`.  As elaborated, (H_F) reads
`∫|F - c|² ≤ ε₁ ∫_{B_ρ(x)} (|Dw - (Dw)_{x,ρ}|² + Kρ^{2α} ∫_{B_ρ(x)} (|Dw|² + Kρ^{m+2α}))` (the
set-integral notation absorbs the trailing sums); for `ρ ≤ R/8` this still gives the comparison
inequality, with a constant depending on `K` and `R`. -/
theorem Submission.codim1_hcp_sr_c1alpha_estimate : ∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) → ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) → (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) → (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R → ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤ ε₁ * ∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2 + K * ρ ^ (2 * α) * ∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2 + K * ρ ^ ((m : ℝ) + 2 * α)) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := by
  have hrepl := Submission.codim1_hcp_sr_harmonic_replacement
  have hdecay := Submission.codim1_hcp_sr_harmonic_decay
  have hcamp := Submission.codim1_hcp_sr_campanato_lemmas
  intro m k α hm hα0 hα1
  obtain ⟨hcampI, hcampII⟩ := hcamp
  obtain ⟨Cd, hCd, hdec⟩ := hdecay m k hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have amgm : ∀ p q : ℝ, p * q ≤ p ^ 2 / 2 + q ^ 2 / 2 := fun p q => by
    have h := sq_nonneg (p - q)
    rw [sub_sq] at h
    linarith
  -- the squared Hilbert–Schmidt norm `|A|² = Σⱼ |A eⱼ|²`
  obtain ⟨hs, hs_def⟩ : ∃ hs : (Euclid m →L[ℝ] Euclid k) → ℝ, ∀ A,
      hs A = ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := ⟨_, fun _ => rfl⟩
  have hs_nonneg : ∀ A, 0 ≤ hs A := fun A => by rw [hs_def]; positivity
  have hs_cont : Continuous hs := by
    have : hs = fun A => ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := funext hs_def
    rw [this]; fun_prop
  have hs_le : ∀ A, hs A ≤ m * ‖A‖ ^ 2 := by
    intro A
    rw [hs_def]
    calc ∑ j : Fin m, ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ ∑ _j : Fin m, ‖A‖ ^ 2 := by
          gcongr with j
          calc ‖A (EuclideanSpace.single j (1 : ℝ))‖
              ≤ ‖A‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := A.le_opNorm _
            _ = ‖A‖ := by simp
      _ = m * ‖A‖ ^ 2 := by simp
  have hs_add : ∀ A B, hs (A + B) ≤ 2 * hs A + 2 * hs B := by
    intro A B
    simp only [hs_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    gcongr with j
    rw [add_apply]
    have h1 := norm_add_le (A (EuclideanSpace.single j (1 : ℝ))) (B (EuclideanSpace.single j (1 : ℝ)))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 := sq_nonneg (‖A (EuclideanSpace.single j (1 : ℝ))‖ - ‖B (EuclideanSpace.single j (1 : ℝ))‖)
    rw [add_sq] at h2
    rw [sub_sq] at h3
    linarith
  have hs_sub_comm : ∀ A B, hs (A - B) = hs (B - A) := by
    intro A B
    simp only [hs_def, sub_apply, norm_sub_rev]
  -- `|A|_op² ≤ c_N |A|²` (equivalence of norms on `L(ℝᵐ, ℝᵏ)`)
  obtain ⟨cN, hcN0, hN1⟩ : ∃ cN : ℝ, 0 ≤ cN ∧ ∀ A : Euclid m →L[ℝ] Euclid k, ‖A‖ ^ 2 ≤ cN * hs A := by
    let v := (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    refine ⟨(Fintype.card (Fin m) • ‖(v.equivFunL : Euclid m →L[ℝ] (Fin m → ℝ))‖) ^ 2,
      by positivity, fun A => ?_⟩
    have h1 : ∀ i, ‖A (v i)‖ ≤ Real.sqrt (hs A) := by
      intro i
      apply Real.le_sqrt_of_sq_le
      rw [hs_def]
      have hv : v i = EuclideanSpace.single i (1 : ℝ) := by
        simp [v, EuclideanSpace.basisFun_apply]
      rw [hv]
      exact Finset.single_le_sum (f := fun j => ‖A (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have h2 := v.opNorm_le (Real.sqrt_nonneg _) h1
    calc ‖A‖ ^ 2 ≤ (Fintype.card (Fin m) • ‖(v.equivFunL : Euclid m →L[ℝ] (Fin m → ℝ))‖
          * Real.sqrt (hs A)) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt (hs_nonneg A)]
  -- `|B_r(x)| = ω rᵐ`
  obtain ⟨ω, hω_def⟩ : ∃ ω : ℝ, ω = (volume (ball (0 : Euclid m) 1)).toReal := ⟨_, rfl⟩
  have hω_pos : 0 < ω := by
    rw [hω_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have hvol : ∀ (x : Euclid m) (r : ℝ), 0 < r → volume.real (ball x r) = ω * r ^ m := by
    intro x r hr
    rw [measureReal_def, Measure.addHaar_ball_of_pos volume x hr, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hω_def, mul_comm]
  have hvolpos : ∀ (x : Euclid m) (r : ℝ), 0 < r → 0 < volume.real (ball x r) := fun x r hr => by
    rw [hvol x r hr]; positivity
  -- the mean minimizes `c ↦ ∫_S |f - c|²`
  have hMP : ∀ (S : Set (Euclid m)) (f : Euclid m → (Euclid m →L[ℝ] Euclid k))
      (c : Euclid m →L[ℝ] Euclid k), MeasurableSet S → volume S ≠ ∞ → 0 < volume.real S →
      IntegrableOn f S → IntegrableOn (fun z => hs (f z)) S →
      ∫ z in S, hs (f z - ⨍ z' in S, f z') ≤ ∫ z in S, hs (f z - c) := by
    intro S f c hS hSfin hSpos hf hf2
    set a := ⨍ z' in S, f z' with ha
    set d := a - c with hd
    let Λ : (Euclid m →L[ℝ] Euclid k) →L[ℝ] ℝ := ∑ j : Fin m,
      (innerSL ℝ (d (EuclideanSpace.single j (1 : ℝ)))).comp
        (ContinuousLinearMap.apply ℝ (Euclid k) (EuclideanSpace.single j (1 : ℝ)))
    have hΛ : ∀ A, Λ A = ∑ j : Fin m,
        inner ℝ (d (EuclideanSpace.single j (1 : ℝ))) (A (EuclideanSpace.single j (1 : ℝ))) := by
      intro A
      simp [Λ, sum_apply, innerSL_apply_apply]
    have hpt : ∀ z, hs (f z - c) = hs (f z - a) + 2 * Λ (f z - a) + hs d := by
      intro z
      simp only [hs_def, hΛ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (f z - c) (EuclideanSpace.single j (1 : ℝ)) =
          (f z - a) (EuclideanSpace.single j (1 : ℝ)) + d (EuclideanSpace.single j (1 : ℝ)) := by
        simp only [hd, sub_apply]; abel
      rw [this, norm_add_sq_real, real_inner_comm]
    have hmeas : AEStronglyMeasurable (fun z => f z - a) (volume.restrict S) :=
      hf.aestronglyMeasurable.sub aestronglyMeasurable_const
    have hfa_int : IntegrableOn (fun z => f z - a) S := hf.sub (integrableOn_const hSfin)
    have hfa2 : IntegrableOn (fun z => hs (f z - a)) S := by
      refine Integrable.mono' ((hf2.const_mul 2).add (integrableOn_const hSfin (C := 2 * hs (-a))))
        (hs_cont.comp_aestronglyMeasurable hmeas) (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _), sub_eq_add_neg]
      exact hs_add _ _
    have hΛint : IntegrableOn (fun z => Λ (f z - a)) S := Λ.integrable_comp hfa_int
    have hΛ0 : ∫ z in S, Λ (f z - a) = 0 := by
      rw [Λ.integral_comp_comm hfa_int, integral_sub hf (integrableOn_const hSfin), setIntegral_const,
        ha, setAverage_eq, smul_inv_smul₀ hSpos.ne', sub_self, map_zero]
    calc ∫ z in S, hs (f z - a) ≤ (∫ z in S, hs (f z - a)) + 2 * (∫ z in S, Λ (f z - a))
          + volume.real S * hs d := by
          rw [hΛ0, mul_zero, add_zero]
          exact le_add_of_nonneg_right (mul_nonneg hSpos.le (hs_nonneg d))
      _ = ∫ z in S, hs (f z - c) := by
          have e1 : ∫ z in S, hs (f z - c) = ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a) + hs d) :=
            integral_congr_ae (ae_of_all _ fun z => hpt z)
          have e2 : ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a) + hs d) =
              (∫ z in S, (hs (f z - a) + 2 * Λ (f z - a))) + ∫ _z in S, hs d :=
            integral_add (hfa2.add (hΛint.const_mul 2)) (integrableOn_const hSfin)
          have e3 : ∫ z in S, (hs (f z - a) + 2 * Λ (f z - a)) =
              (∫ z in S, hs (f z - a)) + ∫ z in S, 2 * Λ (f z - a) :=
            integral_add hfa2 (hΛint.const_mul 2)
          rw [e1, e2, e3, integral_const_mul, setIntegral_const, smul_eq_mul]
  -- a fixed cutoff profile `η₀ ∈ C_c^∞(B₁(0))`, `η₀ = 1` on `B_{1/2}(0)`, `|Dη₀| ≤ M₀`
  obtain ⟨η₀, hη₀in, hη₀out⟩ : ∃ η₀ : ContDiffBump (0 : Euclid m), η₀.rIn = 1 / 2 ∧ η₀.rOut = 1 :=
    ⟨⟨1 / 2, 1, by norm_num, by norm_num⟩, rfl, rfl⟩
  obtain ⟨M₀, hM₀⟩ := ((η₀.contDiff (n := 1)).continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (η₀.hasCompactSupport.fderiv ℝ)
  have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans (hM₀ 0)
  -- the constants of the iteration lemmas
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = (4 * Cd + 2) * m * (cN + 1) := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hA₁e : A₁ = (4 * Cd + 2) * m * cN + (4 * Cd + 2) * m := by rw [hA₁]; ring
  have hA₁m : 0 ≤ (4 * Cd + 2) * (m : ℝ) * cN := by positivity
  have hA₁a : 4 * Cd ≤ A₁ := by
    have h1 : (4 * Cd + 2) * 1 ≤ (4 * Cd + 2) * m :=
      mul_le_mul_of_nonneg_left hmR (by positivity)
    linarith
  have hA₁b : (4 * Cd + 2) * m * cN ≤ A₁ := by
    have : 0 ≤ (4 * Cd + 2) * (m : ℝ) := by positivity
    linarith
  have hA₁c : (4 * Cd + 2) * m ≤ A₁ := by linarith
  obtain ⟨εa, ca, hεa, hca, hIa⟩ := hcampI A₁ m (m - α) hA₁0 (by linarith) (by linarith)
  obtain ⟨εb, cb, hεb, hcb, hIb⟩ := hcampI A₁ (m + 2) (m + α) hA₁0 (by linarith) (by linarith)
  obtain ⟨εc, cc, hεc, hcc, hIc⟩ := hcampI A₁ (m + 2) (m + 2 * α) hA₁0 (by linarith) (by linarith)
  obtain ⟨C₀', hC₀', hII'⟩ := hcampII m k (α / 2) hm (by linarith) (by linarith)
  obtain ⟨C₀'', hC₀'', hII''⟩ := hcampII m k α hm hα0 hα1.le
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ : ℝ,
      ε₁ = min (min 1 (εa / 2)) (min (min εb εc) (1 / (24 * m * (cN + 1)))) := ⟨_, rfl⟩
  have hε₁0 : 0 < ε₁ := by
    rw [hε₁]
    exact lt_min (lt_min one_pos (by linarith)) (lt_min (lt_min hεb hεc) (by positivity))
  have hε₁1 : ε₁ ≤ 1 := by rw [hε₁]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₁a : ε₁ ≤ εa / 2 := by rw [hε₁]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₁b : ε₁ ≤ εb := by
    rw [hε₁]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε₁c : ε₁ ≤ εc := by
    rw [hε₁]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε₁m : ε₁ ≤ 1 / (24 * m * (cN + 1)) := by
    rw [hε₁]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hε₁sq' : ε₁ ^ 2 ≤ ε₁ := by rw [sq]; exact mul_le_of_le_one_right hε₁0.le hε₁1
  have hε₁sq : 2 * ε₁ ^ 2 ≤ εa := by linarith
  have hε₁cacc : 6 * m * cN * ε₁ ^ 2 ≤ 1 / 4 := by
    have h1 : ε₁ * (24 * m * (cN + 1)) ≤ 1 := by
      rw [le_div_iff₀ (by positivity)] at hε₁m; linarith
    have h3 : 6 * m * cN * ε₁ ^ 2 ≤ 6 * m * cN * ε₁ :=
      mul_le_mul_of_nonneg_left hε₁sq' (by positivity)
    have h4 : 0 ≤ 6 * (m : ℝ) * ε₁ := by positivity
    have e : (6 * m * (cN + 1) * ε₁ : ℝ) = 6 * m * cN * ε₁ + 6 * m * ε₁ := by ring
    have e2 : (6 * m * (cN + 1) * ε₁ : ℝ) = (ε₁ * (24 * m * (cN + 1))) / 4 := by ring
    linarith
  refine ⟨ε₁, hε₁0, ?_⟩
  intro K R hK hR
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : ℝ, R₁ = R / 8 := ⟨_, rfl⟩
  have hR₁0 : 0 < R₁ := by rw [hR₁]; positivity
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ,
      K₁ = ω * K * R₁ ^ m * cN + ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α) := ⟨_, rfl⟩
  have hK₁0 : 0 ≤ K₁ := by rw [hK₁]; positivity
  obtain ⟨Ccacc, hCcacc⟩ : ∃ Ccacc : ℝ,
      Ccacc = 2 * (6 * m * K ^ 2 + 17 * m * (M₀ * (R / 4)⁻¹) ^ 2 * K ^ 2) * (ω * (R / 4) ^ m) :=
    ⟨_, rfl⟩
  obtain ⟨B₃, hB₃⟩ : ∃ B₃ : ℝ, B₃ = 2 * A₁ * K ^ 2 * ω * R₁ ^ α := ⟨_, rfl⟩
  have hB₃0 : 0 ≤ B₃ := by rw [hB₃]; positivity
  obtain ⟨C₃, hC₃⟩ : ∃ C₃ : ℝ, C₃ = ca * (Ccacc / R₁ ^ ((m : ℝ) - α) + B₃) := ⟨_, rfl⟩
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃, hCcacc]; positivity
  obtain ⟨B₅, hB₅⟩ : ∃ B₅ : ℝ, B₅ = A₁ * K₁ * (C₃ + R₁ ^ α) := ⟨_, rfl⟩
  have hB₅0 : 0 ≤ B₅ := by rw [hB₅]; positivity
  obtain ⟨C₅, hC₅⟩ : ∃ C₅ : ℝ,
      C₅ = cb * (C₃ * R₁ ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) + α) + B₅) := ⟨_, rfl⟩
  have hC₅0 : 0 ≤ C₅ := by rw [hC₅]; positivity
  obtain ⟨H, hH⟩ : ∃ H : ℝ, H = C₀' * Real.sqrt (cN * C₅) * (R / 16) ^ (α / 2) := ⟨_, rfl⟩
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  obtain ⟨C₆, hC₆⟩ : ∃ C₆ : ℝ,
      C₆ = 2 * H ^ 2 + 2 * cN * C₃ * (R / 16) ^ ((m : ℝ) - α) / (ω * (R / 16) ^ m) := ⟨_, rfl⟩
  have hC₆0 : 0 ≤ C₆ := by rw [hC₆]; positivity
  obtain ⟨B₈, hB₈⟩ : ∃ B₈ : ℝ, B₈ = A₁ * K₁ * (m * C₆ * ω + 1) := ⟨_, rfl⟩
  have hB₈0 : 0 ≤ B₈ := by rw [hB₈]; positivity
  obtain ⟨C₈, hC₈⟩ : ∃ C₈ : ℝ,
      C₈ = cc * (m * C₆ * ω * R₁ ^ m / R₁ ^ ((m : ℝ) + 2 * α) + B₈) := ⟨_, rfl⟩
  have hC₈0 : 0 ≤ C₈ := by rw [hC₈]; positivity
  refine ⟨max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α)),
    le_max_of_le_left (Real.sqrt_nonneg _), ?_⟩
  intro x₀ w F hw hF hwK hFK hHF hweak
  have hDw : ContinuousOn (fderiv ℝ w) (ball x₀ R) := hw.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Euclid m → ℝ → ℝ, ∀ x r,
      Ψ x r = ∫ z in ball x r, hs (fderiv ℝ w z) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Euclid m → ℝ → ℝ, ∀ x r,
      Φ x r = ∫ z in ball x r, hs (fderiv ℝ w z - ⨍ z' in ball x r, fderiv ℝ w z') :=
    ⟨_, fun _ _ => rfl⟩
  -- `|F|² ≤ 2ε₁² c_N |Dw|² + 2K²`
  have hF2 : ∀ z ∈ ball x₀ R, ‖F z‖ ^ 2 ≤ 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2 := by
    intro z hz
    have h1 : ‖F z‖ ^ 2 ≤ (ε₁ * ‖fderiv ℝ w z‖ + K) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hFK z hz) 2
    have h2 : ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 ≤ ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) :=
      mul_le_mul_of_nonneg_left (hN1 _) (sq_nonneg _)
    have h3 := amgm (ε₁ * ‖fderiv ℝ w z‖) K
    have h4 : (ε₁ * ‖fderiv ℝ w z‖ + K) ^ 2 =
        ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 + 2 * ((ε₁ * ‖fderiv ℝ w z‖) * K) + K ^ 2 := by ring
    have h5 : (ε₁ * ‖fderiv ℝ w z‖) ^ 2 = ε₁ ^ 2 * ‖fderiv ℝ w z‖ ^ 2 := by ring
    linarith
  -- integrability on balls `B_r(x)` with `B̄_r(x) ⊆ B_R(x₀)`
  have hgood : ∀ (x : Euclid m) (r : ℝ), closedBall x r ⊆ ball x₀ R →
      IntegrableOn (fderiv ℝ w) (ball x r) ∧
      (∀ c, IntegrableOn (fun z => hs (fderiv ℝ w z - c)) (ball x r)) ∧
      IntegrableOn (fun z => hs (fderiv ℝ w z)) (ball x r) := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    exact ⟨(hc.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall,
      fun c => ((hs_cont.comp_continuousOn (hc.sub continuousOn_const)).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall,
      ((hs_cont.comp_continuousOn hc).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall⟩
  have hΨ0 : ∀ x r, 0 ≤ Ψ x r := fun x r => by
    rw [hΨ]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
  have hΦ0 : ∀ x r, 0 ≤ Φ x r := fun x r => by
    rw [hΦ]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
  have hΦΨ : ∀ x r, 0 < r → closedBall x r ⊆ ball x₀ R → Φ x r ≤ Ψ x r := by
    intro x r hr hxr
    obtain ⟨h1, -, h3⟩ := hgood x r hxr
    rw [hΦ, hΨ]
    calc _ ≤ ∫ z in ball x r, hs (fderiv ℝ w z - 0) :=
          hMP _ _ 0 measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr) h1 h3
      _ = _ := by simp_rw [sub_zero]
  have hΨmono : ∀ x r ρ, r ≤ ρ → closedBall x ρ ⊆ ball x₀ R → Ψ x r ≤ Ψ x ρ := by
    intro x r ρ hrρ hxρ
    rw [hΨ, hΨ]
    exact setIntegral_mono_set (hgood x ρ hxρ).2.2 (ae_of_all _ fun z => hs_nonneg _)
      (ball_subset_ball hrρ).eventuallyLE
  have hΦmono : ∀ x r ρ, 0 < r → r ≤ ρ → closedBall x ρ ⊆ ball x₀ R → Φ x r ≤ Φ x ρ := by
    intro x r ρ hr hrρ hxρ
    have hxr : closedBall x r ⊆ ball x₀ R := (closedBall_subset_closedBall hrρ).trans hxρ
    obtain ⟨h1, -, h3⟩ := hgood x r hxr
    rw [hΦ, hΦ]
    calc _ ≤ ∫ z in ball x r, hs (fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z') :=
          hMP _ _ _ measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr) h1 h3
      _ ≤ _ := setIntegral_mono_set ((hgood x ρ hxρ).2.1 _) (ae_of_all _ fun z => hs_nonneg _)
          (ball_subset_ball hrρ).eventuallyLE
  have hΦop : ∀ x r, closedBall x r ⊆ ball x₀ R →
      ∫ z in ball x r, ‖fderiv ℝ w z - ⨍ z' in ball x r, fderiv ℝ w z'‖ ^ 2 ≤ cN * Φ x r := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    rw [hΦ, ← integral_const_mul]
    exact setIntegral_mono_on
      ((((hc.sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x r)).mono_set ball_subset_closedBall)
      (((hgood x r hxr).2.1 _).const_mul cN) measurableSet_ball (fun z _ => hN1 _)
  have hΨop : ∀ x r, closedBall x r ⊆ ball x₀ R →
      ∫ z in ball x r, ‖fderiv ℝ w z‖ ^ 2 ≤ cN * Ψ x r := by
    intro x r hxr
    have hc : ContinuousOn (fderiv ℝ w) (closedBall x r) := hDw.mono hxr
    rw [hΨ, ← integral_const_mul]
    exact setIntegral_mono_on
      (((hc.norm.pow 2).integrableOn_compact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall)
      ((hgood x r hxr).2.2.const_mul cN) measurableSet_ball (fun z _ => hN1 _)
  -- Caccioppoli: `Ψ(x, R/8) ≤ C_cacc` for `x ∈ B_{R/2}(x₀)`
  have hcacc : ∀ x ∈ ball x₀ (R / 2), Ψ x R₁ ≤ Ccacc := by
    intro x hx
    rw [hΨ, hR₁, hCcacc]
    obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = R / 4 := ⟨_, rfl⟩
    rw [← hρ_def]
    have hρ : 0 < ρ := by rw [hρ_def]; positivity
    have hxd : dist x x₀ < R / 2 := hx
    have hcl : closedBall x ρ ⊆ ball x₀ R := closedBall_subset_ball' (by rw [hρ_def]; linarith)
    have hbx : ball x ρ ⊆ ball x₀ R := ball_subset_closedBall.trans hcl
    -- the cutoff `η(y) = η₀((y - x)/ρ)`
    obtain ⟨η, hη_def⟩ : ∃ η : Euclid m → ℝ, η = fun y => η₀ (ρ⁻¹ • (y - x)) := ⟨_, rfl⟩
    have hη_cd : ContDiff ℝ 1 η := by
      rw [hη_def]
      exact (η₀.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).const_smul ρ⁻¹)
    have hη01 : ∀ y, 0 ≤ η y ∧ η y ≤ 1 := fun y => by rw [hη_def]; exact ⟨η₀.nonneg, η₀.le_one⟩
    have hη1 : ∀ y ∈ ball x (R / 8), η y = 1 := by
      intro y hy
      rw [hη_def]
      apply η₀.one_of_mem_closedBall
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le),
        hη₀in, inv_mul_le_iff₀ hρ, hρ_def]
      linarith
    have hη0 : ∀ y, y ∉ ball x ρ → η y = 0 := by
      intro y hy
      rw [hη_def]
      apply η₀.zero_of_le_dist
      rw [mem_ball, dist_eq_norm, not_lt] at hy
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le), hη₀out,
        le_inv_mul_iff₀ hρ]
      linarith
    have hDη : ∀ y, ‖fderiv ℝ η y‖ ≤ M₀ * ρ⁻¹ := by
      intro y
      have hA : HasFDerivAt (fun y : Euclid m => ρ⁻¹ • (y - x))
          (ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m)) y :=
        ((hasFDerivAt_id y).sub_const x).const_smul ρ⁻¹
      have hB : HasFDerivAt (η₀ : Euclid m → ℝ) (fderiv ℝ η₀ (ρ⁻¹ • (y - x))) (ρ⁻¹ • (y - x)) :=
        ((η₀.contDiff (n := 1)).differentiable (by norm_num) _).hasFDerivAt
      have hC := hB.comp y hA
      rw [hη_def]
      rw [show (fun y => η₀ (ρ⁻¹ • (y - x))) =
        (η₀ : Euclid m → ℝ) ∘ (fun y : Euclid m => ρ⁻¹ • (y - x)) from rfl, hC.fderiv]
      calc ‖(fderiv ℝ η₀ (ρ⁻¹ • (y - x))).comp (ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m))‖
          ≤ ‖fderiv ℝ η₀ (ρ⁻¹ • (y - x))‖ * ‖ρ⁻¹ • ContinuousLinearMap.id ℝ (Euclid m)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M₀ * ρ⁻¹ := by
            gcongr
            · exact hM₀ _
            · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hρ.le)]
              calc ρ⁻¹ * ‖ContinuousLinearMap.id ℝ (Euclid m)‖ ≤ ρ⁻¹ * 1 := by
                    gcongr; exact ContinuousLinearMap.norm_id_le
                _ = ρ⁻¹ := mul_one _
    -- the test map `ζ = η² w`
    obtain ⟨ζ, hζ_def⟩ : ∃ ζ : Euclid m → Euclid k, ζ = fun y => (η y * η y) • w y := ⟨_, rfl⟩
    have hζ0 : ∀ y, y ∉ ball x ρ → ζ y = 0 := fun y hy => by rw [hζ_def]; simp [hη0 y hy]
    have hζ_cd : ContDiff ℝ 1 ζ := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : y ∈ ball x₀ R
      · rw [hζ_def]
        exact ((hη_cd.contDiffAt).mul hη_cd.contDiffAt).smul (hw.contDiffAt (isOpen_ball.mem_nhds hy))
      · have hy' : y ∉ closedBall x ρ := fun h => hy (hcl h)
        have : ζ =ᶠ[𝓝 y] fun _ => 0 := by
          filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hy'] with z hz
          exact hζ0 z (fun h => hz (ball_subset_closedBall h))
        exact contDiffAt_const.congr_of_eventuallyEq this
    have hζ_supp : support ζ ⊆ closedBall x ρ := fun y hy => by
      by_contra h
      exact hy (hζ0 y (fun h' => h (ball_subset_closedBall h')))
    have hζ_cs : HasCompactSupport ζ :=
      HasCompactSupport.intro (isCompact_closedBall x ρ)
        (fun y hy => hζ0 y (fun h => hy (ball_subset_closedBall h)))
    have hζ_ts : tsupport ζ ⊆ ball x₀ R := (closure_minimal hζ_supp isClosed_closedBall).trans hcl
    have hζD : ∀ y ∈ ball x₀ R, ∀ v, fderiv ℝ ζ y v =
        (η y * η y) • fderiv ℝ w y v + (2 * η y * fderiv ℝ η y v) • w y := by
      intro y hy v
      have hηd : HasFDerivAt η (fderiv ℝ η y) y := (hη_cd.differentiable (by norm_num) y).hasFDerivAt
      have hwd : HasFDerivAt w (fderiv ℝ w y) y :=
        ((hw.differentiableOn (by norm_num)) y hy |>.differentiableAt
          (isOpen_ball.mem_nhds hy)).hasFDerivAt
      have hζd := (hηd.mul hηd).smul hwd
      rw [hζ_def, show (fun y => (η y * η y) • w y) = (η * η) • w from rfl, hζd.fderiv]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
        Pi.mul_apply]
      congr 1
      rw [← add_smul]
      congr 1
      ring
    -- the weak equation tested with `ζ`, localized to `B_ρ(x)`
    have hW := hweak ζ hζ_cd hζ_cs hζ_ts
    have hζD0 : ∀ y ∈ ball x₀ R, y ∉ ball x ρ → fderiv ℝ ζ y = 0 := by
      intro y hy hy'
      ext1 v
      rw [hζD y hy v, hη0 y hy']
      simp
    have eL : ∫ y in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
        (fun y hy => by simp [hζD0 y hy.1 hy.2])
    have eR : ∫ y in ball x₀ R, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
        (fun y hy => by simp [hζD0 y hy.1 hy.2])
    have hW' := eL.symm.trans (hW.trans eR)
    -- integrability on `B_ρ(x)`
    have hζc : Continuous (fderiv ℝ ζ) := hζ_cd.continuous_fderiv (by norm_num)
    have hDwc : ContinuousOn (fderiv ℝ w) (closedBall x ρ) := hDw.mono hcl
    have hFc : ContinuousOn F (closedBall x ρ) := hF.mono hcl
    have hLint : IntegrableOn (fun y => ∑ j : Fin m, inner ℝ
        (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        (continuousOn_finsetSum _ fun j _ => (hDwc.clm_apply continuousOn_const).inner
          (hζc.continuousOn.clm_apply continuousOn_const))).mono_set ball_subset_closedBall
    have hRint : IntegrableOn (fun y => ∑ j : Fin m, inner ℝ
        (F y (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        (continuousOn_finsetSum _ fun j _ => (hFc.clm_apply continuousOn_const).inner
          (hζc.continuousOn.clm_apply continuousOn_const))).mono_set ball_subset_closedBall
    have hPint : IntegrableOn (fun y => η y * η y * hs (fderiv ℝ w y)) (ball x ρ) :=
      (ContinuousOn.integrableOn_compact (isCompact_closedBall x ρ)
        ((hη_cd.continuous.continuousOn.mul hη_cd.continuous.continuousOn).mul
          (hs_cont.comp_continuousOn hDwc))).mono_set ball_subset_closedBall
    -- the pointwise estimate of the integrand of `∫ η² |Dw|² = ∫ (R - L + η² |Dw|²)`
    set G := M₀ * ρ⁻¹ with hG
    have hG0 : 0 ≤ G := by positivity
    have hpt : ∀ y ∈ ball x ρ,
        (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y) ≤
        η y * η y * hs (fderiv ℝ w y) / 2 + (6 * m * K ^ 2 + 17 * m * G ^ 2 * K ^ 2) := by
      intro y hy
      have hyR : y ∈ ball x₀ R := hbx hy
      obtain ⟨he0, he1⟩ := hη01 y
      have hwy : ‖w y‖ ≤ K := hwK y hyR
      have hee : 0 ≤ η y * η y := mul_nonneg he0 he0
      have hper : ∀ j : Fin m,
          inner ℝ (F y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
          - inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
          + η y * η y * ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
          η y * η y * (3 * ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
            + ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 / 4) + 17 * G ^ 2 * K ^ 2 := by
        intro j
        set f := F y (EuclideanSpace.single j (1 : ℝ))
        set a := fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))
        set t := fderiv ℝ η y (EuclideanSpace.single j (1 : ℝ))
        set e := η y
        have ht : |t| ≤ G := by
          calc |t| = ‖fderiv ℝ η y (EuclideanSpace.single j (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
            _ ≤ ‖fderiv ℝ η y‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖fderiv ℝ η y‖ := by simp
            _ ≤ G := hDη y
        rw [hζD y hyR, inner_add_right, inner_add_right, real_inner_smul_right, real_inner_smul_right,
          real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        have i1 : inner ℝ f a ≤ ‖f‖ * ‖a‖ := real_inner_le_norm f a
        have i2 : |inner ℝ f (w y)| ≤ ‖f‖ * K :=
          (abs_real_inner_le_norm f (w y)).trans (mul_le_mul_of_nonneg_left hwy (norm_nonneg _))
        have i3 : |inner ℝ a (w y)| ≤ ‖a‖ * K :=
          (abs_real_inner_le_norm a (w y)).trans (mul_le_mul_of_nonneg_left hwy (norm_nonneg _))
        have b1 : e * e * inner ℝ f a ≤ e * e * (2 * ‖f‖ ^ 2 + ‖a‖ ^ 2 / 8) := by
          apply mul_le_mul_of_nonneg_left _ hee
          calc inner ℝ f a ≤ ‖f‖ * ‖a‖ := i1
            _ = (2 * ‖f‖) * (‖a‖ / 2) := by ring
            _ ≤ (2 * ‖f‖) ^ 2 / 2 + (‖a‖ / 2) ^ 2 / 2 := amgm _ _
            _ = 2 * ‖f‖ ^ 2 + ‖a‖ ^ 2 / 8 := by ring
        have b2 : 2 * e * t * inner ℝ f (w y) ≤ e * e * ‖f‖ ^ 2 + G ^ 2 * K ^ 2 := by
          calc 2 * e * t * inner ℝ f (w y) ≤ |2 * e * t * inner ℝ f (w y)| := le_abs_self _
            _ = 2 * e * (|t| * |inner ℝ f (w y)|) := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_two]; ring
            _ ≤ 2 * e * (G * (‖f‖ * K)) := by gcongr
            _ = 2 * ((e * ‖f‖) * (G * K)) := by ring
            _ ≤ 2 * ((e * ‖f‖) ^ 2 / 2 + (G * K) ^ 2 / 2) := by gcongr; exact amgm _ _
            _ = e * e * ‖f‖ ^ 2 + G ^ 2 * K ^ 2 := by ring
        have b3 : -(2 * e * t * inner ℝ a (w y)) ≤ e * e * (‖a‖ ^ 2 / 8) + 16 * G ^ 2 * K ^ 2 := by
          calc -(2 * e * t * inner ℝ a (w y)) ≤ |2 * e * t * inner ℝ a (w y)| := neg_le_abs _
            _ = 2 * e * (|t| * |inner ℝ a (w y)|) := by
                rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he0, abs_two]; ring
            _ ≤ 2 * e * (G * (‖a‖ * K)) := by gcongr
            _ = 2 * ((e * ‖a‖ / 4) * (4 * G * K)) := by ring
            _ ≤ 2 * ((e * ‖a‖ / 4) ^ 2 / 2 + (4 * G * K) ^ 2 / 2) := by gcongr; exact amgm _ _
            _ = e * e * (‖a‖ ^ 2 / 16) + 16 * G ^ 2 * K ^ 2 := by ring
            _ ≤ e * e * (‖a‖ ^ 2 / 8) + 16 * G ^ 2 * K ^ 2 := by
                have : 0 ≤ e * e * ‖a‖ ^ 2 := by positivity
                linarith
        have e1 : e * e * ‖a‖ ^ 2 = e * e * ‖a‖ ^ 2 := rfl
        linarith [b1, b2, b3]
      -- `∑ |F e_j|² ≤ m |F|²` and `|F|² ≤ 2ε₁² c_N |Dw|²_HS + 2K²`
      have hFs : ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤ m * ‖F y‖ ^ 2 := by
        have := hs_le (F y); rwa [hs_def] at this
      have hFy : ‖F y‖ ≤ ε₁ * ‖fderiv ℝ w y‖ + K := hFK y hyR
      have hsy := hs_nonneg (fderiv ℝ w y)
      have hF2 : ‖F y‖ ^ 2 ≤ 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) + 2 * K ^ 2 := by
        have h1 : ‖F y‖ ^ 2 ≤ (ε₁ * ‖fderiv ℝ w y‖ + K) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hFy 2
        have h2 : ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 ≤ ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) :=
          mul_le_mul_of_nonneg_left (hN1 _) (sq_nonneg _)
        have h3 := amgm (ε₁ * ‖fderiv ℝ w y‖) K
        have h4 : (ε₁ * ‖fderiv ℝ w y‖ + K) ^ 2 =
            ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 + 2 * ((ε₁ * ‖fderiv ℝ w y‖) * K) + K ^ 2 := by ring
        have h5 : (ε₁ * ‖fderiv ℝ w y‖) ^ 2 = ε₁ ^ 2 * ‖fderiv ℝ w y‖ ^ 2 := by ring
        linarith
      have hee1 : η y * η y ≤ 1 := by
        calc η y * η y ≤ 1 * 1 := mul_le_mul he1 he1 he0 zero_le_one
          _ = 1 := one_mul 1
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hFsum : η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) ≤
          η y * η y * hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by
        have h3 : 3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
            6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) + 6 * m * K ^ 2 := by
          have := mul_le_mul_of_nonneg_left hF2 hm0
          have e : (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w y)) + 2 * K ^ 2) * 3 =
              6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) + 6 * m * K ^ 2 := by ring
          linarith [hFs]
        have h4 : 6 * m * cN * ε₁ ^ 2 * hs (fderiv ℝ w y) ≤ hs (fderiv ℝ w y) / 4 := by
          have := mul_le_mul_of_nonneg_right hε₁cacc hsy
          linarith
        have h5 : 0 ≤ 6 * m * K ^ 2 := by positivity
        have h6 : 3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 ≤
            hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by linarith
        calc η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
            ≤ η y * η y * (hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2) :=
              mul_le_mul_of_nonneg_left h6 hee
          _ = η y * η y * hs (fderiv ℝ w y) / 4 + η y * η y * (6 * m * K ^ 2) := by ring
          _ ≤ η y * η y * hs (fderiv ℝ w y) / 4 + 1 * (6 * m * K ^ 2) := by
              gcongr
          _ = η y * η y * hs (fderiv ℝ w y) / 4 + 6 * m * K ^ 2 := by ring
      calc (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
            (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)
          = ∑ j : Fin m, (inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
              - inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))
              + η y * η y * ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) := by
            rw [hs_def, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        _ ≤ ∑ j : Fin m, (η y * η y * (3 * ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
              + ‖fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 / 4) + 17 * G ^ 2 * K ^ 2) :=
            Finset.sum_le_sum fun j _ => hper j
        _ = η y * η y * (3 * ∑ j : Fin m, ‖F y (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
              + η y * η y * hs (fderiv ℝ w y) / 4 + m * (17 * G ^ 2 * K ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum,
              ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              hs_def]
            ring
        _ ≤ η y * η y * hs (fderiv ℝ w y) / 2 + (6 * m * K ^ 2 + 17 * m * G ^ 2 * K ^ 2) := by
            linarith [hFsum]
    -- integrate and absorb
    have hVρ : volume.real (ball x ρ) = ω * ρ ^ m := hvol x ρ hρ
    have hsub : ball x (R / 8) ⊆ ball x ρ := ball_subset_ball (by rw [hρ_def]; linarith)
    have hP0 : ∀ y, 0 ≤ η y * η y * hs (fderiv ℝ w y) := fun y =>
      mul_nonneg (mul_nonneg (hη01 y).1 (hη01 y).1) (hs_nonneg _)
    have hQint : IntegrableOn (fun y => (∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y))
        (ball x ρ) := (hRint.sub hLint).add hPint
    have hP_eq : ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) =
        ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)) := by
      have e1 : ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) + η y * η y * hs (fderiv ℝ w y)) =
        (∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))))) +
        ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) := integral_add (hRint.sub hLint) hPint
      have e2 : ∫ y in ball x ρ, ((∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        (∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))) =
        (∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (F y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) -
        ∫ y in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w y (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := integral_sub hRint hLint
      rw [e1, e2, hW']
      ring
    set c₁ := 6 * (m : ℝ) * K ^ 2 + 17 * m * G ^ 2 * K ^ 2 with hc₁
    have hbound : ∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) ≤
        ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) := by
      rw [hP_eq]
      exact setIntegral_mono_on hQint ((hPint.div_const 2).add (integrableOn_const measure_ball_lt_top.ne))
        measurableSet_ball hpt
    have hsplit : ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) =
        (∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y)) / 2 + volume.real (ball x ρ) * c₁ := by
      have e1 : ∫ y in ball x ρ, (η y * η y * hs (fderiv ℝ w y) / 2 + c₁) =
          (∫ y in ball x ρ, η y * η y * hs (fderiv ℝ w y) / 2) + ∫ _y in ball x ρ, c₁ :=
        integral_add (hPint.div_const 2) (integrableOn_const measure_ball_lt_top.ne)
      rw [e1, integral_div, setIntegral_const, smul_eq_mul]
    rw [hsplit, hVρ] at hbound
    calc ∫ z in ball x (R / 8), hs (fderiv ℝ w z)
        = ∫ z in ball x (R / 8), η z * η z * hs (fderiv ℝ w z) :=
          setIntegral_congr_fun measurableSet_ball (fun z hz => by simp [hη1 z hz])
      _ ≤ ∫ z in ball x ρ, η z * η z * hs (fderiv ℝ w z) :=
          setIntegral_mono_set hPint (ae_of_all _ hP0) hsub.eventuallyLE
      _ ≤ 2 * c₁ * (ω * ρ ^ m) := by linarith
  -- comparison with the harmonic replacement (Campanato's inequalities (C1'), (C2'))
  have hcomp : ∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → ρ ≤ R₁ → dist x x₀ + 2 * ρ < R →
      ∀ r, 0 < r → r ≤ ρ →
      Φ x r ≤ A₁ * ((r / ρ) ^ ((m : ℝ) + 2) + ε₁) * Φ x ρ
          + A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ∧
      Ψ x r ≤ A₁ * ((r / ρ) ^ (m : ℝ) + 2 * ε₁ ^ 2) * Ψ x ρ
          + 2 * A₁ * K ^ 2 * ω * ρ ^ (m : ℝ) := by
    intro x ρ hρ hρR₁ hxρ r hr hrρ
    have hball2 : ball x (2 * ρ) ⊆ ball x₀ R := ball_subset_ball' (by linarith)
    have hcl : closedBall x ρ ⊆ ball x₀ R := closedBall_subset_ball' (by linarith)
    have hbx : ball x ρ ⊆ ball x₀ R := ball_subset_closedBall.trans hcl
    have hsubr : ball x r ⊆ ball x ρ := ball_subset_ball hrρ
    -- the equation holds weakly in `B_ρ(x)`
    have hweak' : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ →
        tsupport ζ ⊆ ball x ρ →
        ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
        ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) := by
      intro ζ hζ hζc hζs
      have h := hweak ζ hζ hζc (hζs.trans hbx)
      have hzero : ∀ z, z ∉ ball x ρ → fderiv ℝ ζ z = 0 := fun z hz => by
        by_contra hne
        exact hz (hζs (support_fderiv_subset ℝ hne))
      have eL : ∫ z in ball x₀ R, ∑ j : Fin m,
            inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
          ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (fderiv ℝ w z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
          (fun z hz => by simp [hzero z hz.2])
      have eR : ∫ z in ball x₀ R, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) =
          ∫ z in ball x ρ, ∑ j : Fin m, inner ℝ (F z (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ z (EuclideanSpace.single j (1 : ℝ))) :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hbx
          (fun z hz => by simp [hzero z hz.2])
      rw [← eL, ← eR]
      exact h
    -- the harmonic replacement `h` of `w` in `B_ρ(x)`
    obtain ⟨h, hsm, hharm, hDint, hDle⟩ := hrepl m k hm x ρ (2 * ρ) w F hρ (by linarith)
      (hw.mono hball2) (hF.mono hball2) hweak'
    have hDint' : IntegrableOn (fun z => hs (fderiv ℝ w z - fderiv ℝ h z)) (ball x ρ) := by
      simpa only [hs_def] using hDint
    have hDle' : ∀ c, ∫ z in ball x ρ, hs (fderiv ℝ w z - fderiv ℝ h z) ≤
        ∫ z in ball x ρ, hs (F z - c) := by
      intro c; simpa only [hs_def] using hDle c
    obtain ⟨D, hD⟩ : ∃ D, D = ∫ z in ball x ρ, hs (fderiv ℝ w z - fderiv ℝ h z) := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by
      rw [hD]; exact setIntegral_nonneg measurableSet_ball fun z _ => hs_nonneg _
    have hDr : ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) ≤ D := by
      rw [hD]
      exact setIntegral_mono_set hDint' (ae_of_all _ fun z => hs_nonneg _) hsubr.eventuallyLE
    -- integrability in `B_ρ(x)`
    obtain ⟨hwint, hwint2c, hwint2⟩ := hgood x ρ hcl
    have hDh : ContinuousOn (fderiv ℝ h) (ball x ρ) :=
      (hsm 1).continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
    have hDhm : AEStronglyMeasurable (fderiv ℝ h) (volume.restrict (ball x ρ)) :=
      hDh.aestronglyMeasurable measurableSet_ball
    have hhint2 : IntegrableOn (fun z => hs (fderiv ℝ h z)) (ball x ρ) := by
      refine Integrable.mono' ((hwint2.const_mul 2).add (hDint'.const_mul 2))
        (hs_cont.comp_aestronglyMeasurable hDhm) (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _)]
      have := hs_add (fderiv ℝ w z) (fderiv ℝ h z - fderiv ℝ w z)
      rw [show fderiv ℝ w z + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z by abel,
        hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this
      exact this
    have hhint : IntegrableOn (fderiv ℝ h) (ball x ρ) := by
      refine Integrable.mono' ((integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).add
        (hhint2.const_mul cN)) hDhm (ae_of_all _ fun z => ?_)
      have h1 := hN1 (fderiv ℝ h z)
      have h2 := amgm ‖fderiv ℝ h z‖ 1
      have h3 : 0 ≤ cN * hs (fderiv ℝ h z) := mul_nonneg hcN0 (hs_nonneg _)
      show ‖fderiv ℝ h z‖ ≤ 1 + cN * hs (fderiv ℝ h z)
      linarith
    have hhint2c : ∀ c, IntegrableOn (fun z => hs (fderiv ℝ h z - c)) (ball x ρ) := fun c => by
      refine Integrable.mono' ((hhint2.const_mul 2).add
        (integrableOn_const measure_ball_lt_top.ne (C := 2 * hs (-c))))
        (hs_cont.comp_aestronglyMeasurable (hDhm.sub aestronglyMeasurable_const))
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_of_nonneg (hs_nonneg _), sub_eq_add_neg]
      exact hs_add _ _
    -- harmonic decay
    have hhint2' : IntegrableOn (fun z => ∑ j : Fin m,
        ‖fderiv ℝ h z (EuclideanSpace.single j (1 : ℝ))‖ ^ 2) (ball x ρ) := by
      simpa only [hs_def] using hhint2
    obtain ⟨hdec1, hdec2⟩ := hdec x ρ h hρ hsm hharm hhint2' r hr hrρ
    have hdec1' : ∫ z in ball x r, hs (fderiv ℝ h z - ⨍ z' in ball x r, fderiv ℝ h z') ≤
        Cd * (r / ρ) ^ (m + 2) *
          ∫ z in ball x ρ, hs (fderiv ℝ h z - ⨍ z' in ball x ρ, fderiv ℝ h z') := by
      simpa only [hs_def] using hdec1
    have hdec2' : ∫ z in ball x r, hs (fderiv ℝ h z) ≤
        Cd * (r / ρ) ^ m * ∫ z in ball x ρ, hs (fderiv ℝ h z) := by
      simpa only [hs_def] using hdec2
    have hq : 0 ≤ r / ρ := by positivity
    have hq1 : r / ρ ≤ 1 := (div_le_one hρ).mpr hrρ
    have hqa : (r / ρ) ^ (m + 2) ≤ 1 := pow_le_one₀ hq hq1
    have hqb : (r / ρ) ^ m ≤ 1 := pow_le_one₀ hq hq1
    have hΦρ0 := hΦ0 x ρ
    have hΨρ0 := hΨ0 x ρ
    -- (C1): `Φ(r) ≤ 4C_d (r/ρ)^{m+2} Φ(ρ) + (4C_d + 2) D`
    have hC1 : Φ x r ≤ 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ + (4 * Cd + 2) * D := by
      set ahr := ⨍ z' in ball x r, fderiv ℝ h z' with hahr
      set awρ := ⨍ z' in ball x ρ, fderiv ℝ w z' with hawρ
      have s1 : Φ x r ≤ ∫ z in ball x r, hs (fderiv ℝ w z - ahr) := by
        rw [hΦ]
        exact hMP _ _ _ measurableSet_ball measure_ball_lt_top.ne (hvolpos x r hr)
          (hwint.mono_set hsubr) (hwint2.mono_set hsubr)
      have s2 : ∫ z in ball x r, hs (fderiv ℝ w z - ahr) ≤
          2 * (∫ z in ball x r, hs (fderiv ℝ h z - ahr)) + 2 * D := by
        have i1 : ∫ z in ball x r, hs (fderiv ℝ w z - ahr) ≤
            ∫ z in ball x r, (2 * hs (fderiv ℝ h z - ahr)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on ((hwint2c ahr).mono_set hsubr)
            ((((hhint2c ahr).mono_set hsubr).const_mul 2).add ((hDint'.mono_set hsubr).const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ h z - ahr) (fderiv ℝ w z - fderiv ℝ h z)
              rwa [show fderiv ℝ h z - ahr + (fderiv ℝ w z - fderiv ℝ h z) = fderiv ℝ w z - ahr by
                abel] at this)
        have i2 : ∫ z in ball x r, (2 * hs (fderiv ℝ h z - ahr)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) =
            2 * (∫ z in ball x r, hs (fderiv ℝ h z - ahr))
              + 2 * ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) := by
          rw [integral_add (((hhint2c ahr).mono_set hsubr).const_mul 2)
            ((hDint'.mono_set hsubr).const_mul 2), integral_const_mul, integral_const_mul]
        linarith [hDr]
      have s3 : ∫ z in ball x ρ, hs (fderiv ℝ h z - ⨍ z' in ball x ρ, fderiv ℝ h z') ≤
          2 * Φ x ρ + 2 * D := by
        have i1 := hMP (ball x ρ) (fderiv ℝ h) awρ measurableSet_ball measure_ball_lt_top.ne
          (hvolpos x ρ hρ) hhint hhint2
        have i2 : ∫ z in ball x ρ, hs (fderiv ℝ h z - awρ) ≤
            ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z - awρ)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on (hhint2c awρ) (((hwint2c awρ).const_mul 2).add (hDint'.const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ w z - awρ) (fderiv ℝ h z - fderiv ℝ w z)
              rwa [show fderiv ℝ w z - awρ + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z - awρ by
                abel, hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this)
        have i3 : ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z - awρ)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) = 2 * Φ x ρ + 2 * D := by
          rw [integral_add ((hwint2c awρ).const_mul 2) (hDint'.const_mul 2), integral_const_mul,
            integral_const_mul, hΦ, hD]
        linarith
      have s4 : ∫ z in ball x r, hs (fderiv ℝ h z - ahr) ≤
          Cd * (r / ρ) ^ (m + 2) * (2 * Φ x ρ + 2 * D) :=
        hdec1'.trans (by gcongr)
      have s5 : Cd * (r / ρ) ^ (m + 2) * D ≤ Cd * D := by
        calc Cd * (r / ρ) ^ (m + 2) * D = (Cd * D) * (r / ρ) ^ (m + 2) := by ring
          _ ≤ (Cd * D) * 1 := mul_le_mul_of_nonneg_left hqa (by positivity)
          _ = Cd * D := mul_one _
      have e : Cd * (r / ρ) ^ (m + 2) * (2 * Φ x ρ + 2 * D) =
          2 * (Cd * (r / ρ) ^ (m + 2) * Φ x ρ) + 2 * (Cd * (r / ρ) ^ (m + 2) * D) := by ring
      have e2 : 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ = 4 * (Cd * (r / ρ) ^ (m + 2) * Φ x ρ) := by ring
      linarith
    -- (C2): `Ψ(r) ≤ 4C_d (r/ρ)^m Ψ(ρ) + (4C_d + 2) D`
    have hC2 : Ψ x r ≤ 4 * Cd * (r / ρ) ^ m * Ψ x ρ + (4 * Cd + 2) * D := by
      have s1 : Ψ x r ≤ 2 * (∫ z in ball x r, hs (fderiv ℝ h z)) + 2 * D := by
        have i1 : Ψ x r ≤ ∫ z in ball x r, (2 * hs (fderiv ℝ h z)
            + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) := by
          rw [hΨ]
          exact setIntegral_mono_on (hwint2.mono_set hsubr)
            (((hhint2.mono_set hsubr).const_mul 2).add ((hDint'.mono_set hsubr).const_mul 2))
            measurableSet_ball
            (fun z _ => by
              have := hs_add (fderiv ℝ h z) (fderiv ℝ w z - fderiv ℝ h z)
              rwa [show fderiv ℝ h z + (fderiv ℝ w z - fderiv ℝ h z) = fderiv ℝ w z by abel] at this)
        have i2 : ∫ z in ball x r, (2 * hs (fderiv ℝ h z)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) =
            2 * (∫ z in ball x r, hs (fderiv ℝ h z))
              + 2 * ∫ z in ball x r, hs (fderiv ℝ w z - fderiv ℝ h z) := by
          rw [integral_add ((hhint2.mono_set hsubr).const_mul 2)
            ((hDint'.mono_set hsubr).const_mul 2), integral_const_mul, integral_const_mul]
        linarith [hDr]
      have s2 : ∫ z in ball x ρ, hs (fderiv ℝ h z) ≤ 2 * Ψ x ρ + 2 * D := by
        have i1 : ∫ z in ball x ρ, hs (fderiv ℝ h z) ≤
            ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z) + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) :=
          setIntegral_mono_on hhint2 ((hwint2.const_mul 2).add (hDint'.const_mul 2))
            measurableSet_ball (fun z _ => by
              have := hs_add (fderiv ℝ w z) (fderiv ℝ h z - fderiv ℝ w z)
              rwa [show fderiv ℝ w z + (fderiv ℝ h z - fderiv ℝ w z) = fderiv ℝ h z by abel,
                hs_sub_comm (fderiv ℝ h z) (fderiv ℝ w z)] at this)
        have i2 : ∫ z in ball x ρ, (2 * hs (fderiv ℝ w z)
              + 2 * hs (fderiv ℝ w z - fderiv ℝ h z)) = 2 * Ψ x ρ + 2 * D := by
          rw [integral_add (hwint2.const_mul 2) (hDint'.const_mul 2), integral_const_mul,
            integral_const_mul, hΨ, hD]
        linarith
      have s3 : ∫ z in ball x r, hs (fderiv ℝ h z) ≤ Cd * (r / ρ) ^ m * (2 * Ψ x ρ + 2 * D) :=
        hdec2'.trans (by gcongr)
      have s5 : Cd * (r / ρ) ^ m * D ≤ Cd * D := by
        calc Cd * (r / ρ) ^ m * D = (Cd * D) * (r / ρ) ^ m := by ring
          _ ≤ (Cd * D) * 1 := mul_le_mul_of_nonneg_left hqb (by positivity)
          _ = Cd * D := mul_one _
      have e : Cd * (r / ρ) ^ m * (2 * Ψ x ρ + 2 * D) =
          2 * (Cd * (r / ρ) ^ m * Ψ x ρ) + 2 * (Cd * (r / ρ) ^ m * D) := by ring
      have e2 : 4 * Cd * (r / ρ) ^ m * Ψ x ρ = 4 * (Cd * (r / ρ) ^ m * Ψ x ρ) := by ring
      linarith
    -- `D ≤ ∫ |F - c|²_HS` for the constant `c` of (H_F), and for `c = 0`
    have hFint : ∀ c, IntegrableOn (fun z => hs (F z - c)) (ball x ρ) := fun c =>
      ((hs_cont.comp_continuousOn ((hF.mono hcl).sub continuousOn_const)).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hV := hvol x ρ hρ
    have hρm : ρ ^ m ≤ R₁ ^ m := pow_le_pow_left₀ hρ.le hρR₁ m
    have hρ2α : ρ ^ (2 * α) ≤ R₁ ^ (2 * α) := Real.rpow_le_rpow hρ.le hρR₁ (by positivity)
    obtain ⟨c, hc⟩ := hHF x ρ hρ hcl
    have hop1 : IntegrableOn (fun z => ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2)
        (ball x ρ) :=
      ((((hDw.mono hcl).sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hop2 : IntegrableOn (fun z => ‖fderiv ℝ w z‖ ^ 2) (ball x ρ) :=
      ((((hDw.mono hcl).norm.pow 2)).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hinner : ∫ z in ball x ρ, (‖fderiv ℝ w z‖ ^ 2 + K * ρ ^ ((m : ℝ) + 2 * α)) =
        (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)) := by
      rw [integral_add hop2 (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
        smul_eq_mul, hV]
    rw [hinner] at hc
    have houter : ∫ z in ball x ρ, (‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2
        + K * ρ ^ (2 * α) * ((∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2)
          + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) =
        (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2)
          + ω * ρ ^ m * (K * ρ ^ (2 * α) * ((∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2)
            + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) := by
      rw [integral_add hop1 (integrableOn_const measure_ball_lt_top.ne), setIntegral_const,
        smul_eq_mul, hV]
    rw [houter] at hc
    set Φop := ∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2 with hΦop_def
    set Ψop := ∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2 with hΨop_def
    have hΦop' : Φop ≤ cN * Φ x ρ := hΦop x ρ hcl
    have hΨop' : Ψop ≤ cN * Ψ x ρ := hΨop x ρ hcl
    have hΨop0 : 0 ≤ Ψop := setIntegral_nonneg measurableSet_ball (fun z _ => by positivity)
    have hFc : ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤
        ε₁ * cN * Φ x ρ + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) := by
      refine hc.trans ?_
      have t1 : ε₁ * Φop ≤ ε₁ * (cN * Φ x ρ) := mul_le_mul_of_nonneg_left hΦop' hε₁0.le
      have t2 : ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop)) ≤
          (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) := by
        have a1 : 0 ≤ K * ρ ^ (2 * α) := by positivity
        have a3 : 0 ≤ K * ρ ^ (2 * α) * Ψop := mul_nonneg a1 hΨop0
        have a4 : ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop) ≤
            ω * R₁ ^ m * (K * ρ ^ (2 * α) * (cN * Ψ x ρ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hρm hω_pos.le)
            (mul_le_mul_of_nonneg_left hΨop' a1) a3 (by positivity)
        have a5 : 0 ≤ ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop) := mul_nonneg (by positivity) a3
        calc ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop))
            ≤ 1 * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop)) := mul_le_mul_of_nonneg_right hε₁1 a5
          _ ≤ ω * R₁ ^ m * (K * ρ ^ (2 * α) * (cN * Ψ x ρ)) := by rw [one_mul]; exact a4
          _ = (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) := by ring
      have t3 : ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) ≤
          (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) := by
        have a0 : 0 ≤ ρ ^ ((m : ℝ) + 2 * α) := by positivity
        have a1 : ρ ^ m * ρ ^ m ≤ R₁ ^ m * R₁ ^ m := mul_le_mul hρm hρm (by positivity) (by positivity)
        have a2 : ρ ^ m * ρ ^ m * ρ ^ (2 * α) ≤ R₁ ^ m * R₁ ^ m * R₁ ^ (2 * α) :=
          mul_le_mul a1 hρ2α (by positivity) (by positivity)
        have a5 : 0 ≤ ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))) := by
          positivity
        calc ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α)))))
            ≤ 1 * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) :=
              mul_le_mul_of_nonneg_right hε₁1 a5
          _ = (ω ^ 2 * K ^ 2 * ρ ^ ((m : ℝ) + 2 * α)) * (ρ ^ m * ρ ^ m * ρ ^ (2 * α)) := by ring
          _ ≤ (ω ^ 2 * K ^ 2 * ρ ^ ((m : ℝ) + 2 * α)) * (R₁ ^ m * R₁ ^ m * R₁ ^ (2 * α)) :=
              mul_le_mul_of_nonneg_left a2 (by positivity)
          _ = (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) := by ring
      have t4 : (ω * K * R₁ ^ m * cN) * (ρ ^ (2 * α) * Ψ x ρ) ≤ K₁ * (ρ ^ (2 * α) * Ψ x ρ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hK₁]
        have : 0 ≤ ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α) := by positivity
        linarith
      have t5 : (ω ^ 2 * K ^ 2 * R₁ ^ (2 * m) * R₁ ^ (2 * α)) * ρ ^ ((m : ℝ) + 2 * α) ≤
          K₁ * ρ ^ ((m : ℝ) + 2 * α) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [hK₁]
        have : 0 ≤ ω * K * R₁ ^ m * cN := by positivity
        linarith
      have e : ε₁ * (Φop + ω * ρ ^ m * (K * ρ ^ (2 * α) * (Ψop
            + ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) =
          ε₁ * Φop + ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * Ψop))
            + ε₁ * (ω * ρ ^ m * (K * ρ ^ (2 * α) * (ω * ρ ^ m * (K * ρ ^ ((m : ℝ) + 2 * α))))) := by
        ring
      rw [e]
      have e2 : K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) =
          K₁ * (ρ ^ (2 * α) * Ψ x ρ) + K₁ * ρ ^ ((m : ℝ) + 2 * α) := by ring
      have e3 : ε₁ * (cN * Φ x ρ) = ε₁ * cN * Φ x ρ := by ring
      linarith
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hFc2 : IntegrableOn (fun z => ‖F z - c‖ ^ 2) (ball x ρ) :=
      ((((hF.mono hcl).sub continuousOn_const).norm.pow 2).integrableOn_compact
        (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hDc : D ≤ m * (ε₁ * cN * Φ x ρ + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by
      calc D ≤ ∫ z in ball x ρ, hs (F z - c) := by rw [hD]; exact hDle' c
        _ ≤ ∫ z in ball x ρ, (m : ℝ) * ‖F z - c‖ ^ 2 :=
            setIntegral_mono_on (hFint c) (hFc2.const_mul _) measurableSet_ball
              (fun z _ => hs_le _)
        _ = m * ∫ z in ball x ρ, ‖F z - c‖ ^ 2 := integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hFc hm0
    have hFb_int : IntegrableOn
        (fun z => (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2)) (ball x ρ) :=
      (((hwint2.const_mul cN).const_mul (2 * ε₁ ^ 2)).add
        (integrableOn_const measure_ball_lt_top.ne)).const_mul _
    have hDF : D ≤ m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m)) := by
      calc D ≤ ∫ z in ball x ρ, hs (F z - 0) := by rw [hD]; exact hDle' 0
        _ ≤ ∫ z in ball x ρ, (m : ℝ) * (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2) :=
            setIntegral_mono_on (hFint 0) hFb_int
              measurableSet_ball (fun z hz => by
                rw [sub_zero]
                exact (hs_le _).trans (mul_le_mul_of_nonneg_left (hF2 z (hbx hz)) hm0))
        _ = m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m)) := by
            have e1 : ∫ z in ball x ρ, (2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z)) + 2 * K ^ 2) =
                (∫ z in ball x ρ, 2 * ε₁ ^ 2 * (cN * hs (fderiv ℝ w z))) + ∫ _z in ball x ρ, 2 * K ^ 2 :=
              integral_add ((hwint2.const_mul cN).const_mul _)
                (integrableOn_const measure_ball_lt_top.ne)
            rw [integral_const_mul, e1, integral_const_mul, integral_const_mul, setIntegral_const,
              smul_eq_mul, hV, ← hΨ]
            ring
    -- conclusion
    have hqr : (r / ρ) ^ ((m : ℝ) + 2) = (r / ρ) ^ (m + 2) := by norm_cast
    have hqr' : (r / ρ) ^ (m : ℝ) = (r / ρ) ^ m := Real.rpow_natCast _ _
    have hρr : ρ ^ (m : ℝ) = ρ ^ m := Real.rpow_natCast _ _
    have hX0 : 0 ≤ ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α) := by positivity
    constructor
    · rw [hqr]
      have u1 : 4 * Cd * (r / ρ) ^ (m + 2) * Φ x ρ ≤ A₁ * (r / ρ) ^ (m + 2) * Φ x ρ := by
        gcongr
      have u2 : (4 * Cd + 2) * D ≤ (4 * Cd + 2) * (m * (ε₁ * cN * Φ x ρ
          + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)))) := by gcongr
      have u4 : ((4 * Cd + 2) * m * cN) * (ε₁ * Φ x ρ) ≤ A₁ * (ε₁ * Φ x ρ) := by gcongr
      have u5 : ((4 * Cd + 2) * m) * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) ≤
          A₁ * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by gcongr
      have e1 : (4 * Cd + 2) * (m * (ε₁ * cN * Φ x ρ
          + K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)))) =
          ((4 * Cd + 2) * m * cN) * (ε₁ * Φ x ρ)
            + ((4 * Cd + 2) * m) * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by ring
      have e2 : A₁ * ((r / ρ) ^ (m + 2) + ε₁) * Φ x ρ
          + A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) =
          A₁ * (r / ρ) ^ (m + 2) * Φ x ρ + A₁ * (ε₁ * Φ x ρ)
            + A₁ * (K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))) := by ring
      linarith
    · rw [hqr', hρr]
      have u1 : 4 * Cd * (r / ρ) ^ m * Ψ x ρ ≤ A₁ * (r / ρ) ^ m * Ψ x ρ := by gcongr
      have u2 : (4 * Cd + 2) * D ≤
          (4 * Cd + 2) * (m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m))) := by gcongr
      have u4 : ((4 * Cd + 2) * m * cN) * (2 * ε₁ ^ 2 * Ψ x ρ) ≤ A₁ * (2 * ε₁ ^ 2 * Ψ x ρ) := by
        gcongr
      have u5 : ((4 * Cd + 2) * m) * (2 * K ^ 2 * (ω * ρ ^ m)) ≤ A₁ * (2 * K ^ 2 * (ω * ρ ^ m)) := by
        gcongr
      have e1 : (4 * Cd + 2) * (m * (2 * ε₁ ^ 2 * cN * Ψ x ρ + 2 * K ^ 2 * (ω * ρ ^ m))) =
          ((4 * Cd + 2) * m * cN) * (2 * ε₁ ^ 2 * Ψ x ρ)
            + ((4 * Cd + 2) * m) * (2 * K ^ 2 * (ω * ρ ^ m)) := by ring
      have e2 : A₁ * ((r / ρ) ^ m + 2 * ε₁ ^ 2) * Ψ x ρ + 2 * A₁ * K ^ 2 * ω * ρ ^ m =
          A₁ * (r / ρ) ^ m * Ψ x ρ + A₁ * (2 * ε₁ ^ 2 * Ψ x ρ)
            + A₁ * (2 * K ^ 2 * (ω * ρ ^ m)) := by ring
      linarith
  -- Step 3 (Morrey decay): `Ψ(x, r) ≤ C₃ r^{m-α}` on `B_{R/2}(x₀)`, `r ≤ R₁`
  have hstep3 : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ R₁ → Ψ x r ≤ C₃ * r ^ ((m : ℝ) - α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 2 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have key := hIa (Ψ x) R₁ (2 * ε₁ ^ 2) B₃ (by positivity) hε₁sq hB₃0
      (fun s _ _ => hΨ0 x s)
      (fun s ρ _ hsρ hρR => hΨmono x s ρ hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).2
        have hsplit : ρ ^ (m : ℝ) = ρ ^ α * ρ ^ ((m : ℝ) - α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have hρα : ρ ^ α ≤ R₁ ^ α := Real.rpow_le_rpow hρ.le hρR hα0.le
        have : 2 * A₁ * K ^ 2 * ω * ρ ^ (m : ℝ) ≤ B₃ * ρ ^ ((m : ℝ) - α) := by
          rw [hsplit, hB₃]
          calc 2 * A₁ * K ^ 2 * ω * (ρ ^ α * ρ ^ ((m : ℝ) - α))
              = 2 * A₁ * K ^ 2 * ω * ρ ^ α * ρ ^ ((m : ℝ) - α) := by ring
            _ ≤ 2 * A₁ * K ^ 2 * ω * R₁ ^ α * ρ ^ ((m : ℝ) - α) := by gcongr
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hcx := hcacc x hx
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Ψ x r ≤ ca * (r ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) - α) * Ψ x R₁
          + B₃ * r ^ ((m : ℝ) - α)) := key
      _ ≤ ca * (r ^ ((m : ℝ) - α) / R₁ ^ ((m : ℝ) - α) * Ccacc + B₃ * r ^ ((m : ℝ) - α)) := by
          gcongr
      _ = C₃ * r ^ ((m : ℝ) - α) := by rw [hC₃]; ring
  -- Step 4 (first Campanato pass): `Φ(x, r) ≤ C₅ r^{m+α}` on `B_{R/2}(x₀)`, `r ≤ R₁`
  have hstep4 : ∀ x ∈ ball x₀ (R / 2), ∀ r, 0 < r → r ≤ R₁ → Φ x r ≤ C₅ * r ^ ((m : ℝ) + α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 2 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have key := hIb (Φ x) R₁ ε₁ B₅ hε₁0.le hε₁b hB₅0
      (fun s _ _ => hΦ0 x s)
      (fun s ρ hs hsρ hρR => hΦmono x s ρ hs hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).1
        have hΨρ := hstep3 x hx ρ hρ hρR
        have e1 : ρ ^ (2 * α) * ρ ^ ((m : ℝ) - α) = ρ ^ ((m : ℝ) + α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have e2 : ρ ^ ((m : ℝ) + 2 * α) = ρ ^ α * ρ ^ ((m : ℝ) + α) := by
          rw [← Real.rpow_add hρ]; ring_nf
        have hρα : ρ ^ α ≤ R₁ ^ α := Real.rpow_le_rpow hρ.le hρR hα0.le
        have : A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ≤
            B₅ * ρ ^ ((m : ℝ) + α) := by
          have h1 : ρ ^ (2 * α) * Ψ x ρ ≤ C₃ * ρ ^ ((m : ℝ) + α) := by
            calc ρ ^ (2 * α) * Ψ x ρ ≤ ρ ^ (2 * α) * (C₃ * ρ ^ ((m : ℝ) - α)) := by gcongr
              _ = C₃ * (ρ ^ (2 * α) * ρ ^ ((m : ℝ) - α)) := by ring
              _ = C₃ * ρ ^ ((m : ℝ) + α) := by rw [e1]
          have h2 : ρ ^ ((m : ℝ) + 2 * α) ≤ R₁ ^ α * ρ ^ ((m : ℝ) + α) := by
            rw [e2]; gcongr
          rw [hB₅]
          calc A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))
              ≤ A₁ * K₁ * (C₃ * ρ ^ ((m : ℝ) + α) + R₁ ^ α * ρ ^ ((m : ℝ) + α)) := by gcongr
            _ = A₁ * K₁ * (C₃ + R₁ ^ α) * ρ ^ ((m : ℝ) + α) := by ring
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hΦR₁ : Φ x R₁ ≤ C₃ * R₁ ^ ((m : ℝ) - α) :=
      (hΦΨ x R₁ hR₁0 (hgoodρ R₁ le_rfl)).trans (hstep3 x hx R₁ hR₁0 le_rfl)
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Φ x r ≤ cb * (r ^ ((m : ℝ) + α) / R₁ ^ ((m : ℝ) + α) * Φ x R₁
          + B₅ * r ^ ((m : ℝ) + α)) := key
      _ ≤ cb * (r ^ ((m : ℝ) + α) / R₁ ^ ((m : ℝ) + α) * (C₃ * R₁ ^ ((m : ℝ) - α))
          + B₅ * r ^ ((m : ℝ) + α)) := by gcongr
      _ = C₅ * r ^ ((m : ℝ) + α) := by rw [hC₅]; ring
  -- Step 5: `Dw` is `α/2`-Hölder on `B_{R/2}(x₀)` at scale `R₁/2`, and bounded on `B_{3R/8}(x₀)`
  have hhol1 : ∀ x ∈ ball x₀ (R / 2), ∀ y ∈ ball x₀ (R / 2), ‖x - y‖ ≤ R₁ / 2 →
      ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀' * Real.sqrt (cN * C₅) * ‖x - y‖ ^ (α / 2) :=
    hII' (fderiv ℝ w) x₀ (R / 2) R₁ (cN * C₅) (by positivity) hR₁0 (by positivity)
      (hDw.mono (closedBall_subset_ball (by rw [hR₁]; linarith)))
      (fun x hx ρ hρ hρR => by
        have hxd : dist x x₀ < R / 2 := hx
        have hxr : closedBall x ρ ⊆ ball x₀ R :=
          closedBall_subset_ball' (by rw [hR₁] at hρR; linarith)
        calc _ ≤ cN * Φ x ρ := hΦop x ρ hxr
          _ ≤ cN * (C₅ * ρ ^ ((m : ℝ) + α)) := by gcongr; exact hstep4 x hx ρ hρ hρR
          _ = cN * C₅ * ρ ^ ((m : ℝ) + 2 * (α / 2)) := by
              rw [show 2 * (α / 2) = α by ring]; ring)
  have hsup : ∀ x ∈ ball x₀ (3 * R / 8), ‖fderiv ℝ w x‖ ^ 2 ≤ C₆ := by
    intro x hx
    have hxd : dist x x₀ < 3 * R / 8 := hx
    have hx2 : x ∈ ball x₀ (R / 2) := by rw [mem_ball]; linarith
    have hr : 0 < R / 16 := by positivity
    have hrR₁ : R / 16 ≤ R₁ := by rw [hR₁]; linarith
    have hxr : closedBall x (R / 16) ⊆ ball x₀ R := closedBall_subset_ball' (by linarith)
    obtain ⟨-, -, h3⟩ := hgood x (R / 16) hxr
    have hpt : ∀ z ∈ ball x (R / 16),
        ‖fderiv ℝ w x‖ ^ 2 ≤ 2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z) := by
      intro z hz
      have hzd : dist z x < R / 16 := hz
      have hz2 : z ∈ ball x₀ (R / 2) := by
        rw [mem_ball]; linarith [dist_triangle z x x₀]
      have hxz' : ‖x - z‖ < R / 16 := by rw [← dist_eq_norm, dist_comm]; exact hzd
      have hxz : ‖x - z‖ ≤ R₁ / 2 := by rw [hR₁]; linarith
      have h1 := hhol1 x hx2 z hz2 hxz
      have h2 : ‖x - z‖ ^ (α / 2) ≤ (R / 16) ^ (α / 2) :=
        Real.rpow_le_rpow (norm_nonneg _) hxz'.le (by positivity)
      have h3' : ‖fderiv ℝ w x - fderiv ℝ w z‖ ≤ H := by
        rw [hH]
        calc _ ≤ C₀' * Real.sqrt (cN * C₅) * ‖x - z‖ ^ (α / 2) := h1
          _ ≤ C₀' * Real.sqrt (cN * C₅) * (R / 16) ^ (α / 2) := by gcongr
      have h4 : ‖fderiv ℝ w x‖ ≤ H + ‖fderiv ℝ w z‖ := by
        calc ‖fderiv ℝ w x‖ = ‖(fderiv ℝ w x - fderiv ℝ w z) + fderiv ℝ w z‖ := by
              rw [sub_add_cancel]
          _ ≤ ‖fderiv ℝ w x - fderiv ℝ w z‖ + ‖fderiv ℝ w z‖ := norm_add_le _ _
          _ ≤ H + ‖fderiv ℝ w z‖ := by linarith
      have h5 := hN1 (fderiv ℝ w z)
      have h6 : ‖fderiv ℝ w x‖ ^ 2 ≤ (H + ‖fderiv ℝ w z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h4 2
      have h7 := amgm H ‖fderiv ℝ w z‖
      have e : (H + ‖fderiv ℝ w z‖) ^ 2 = H ^ 2 + 2 * (H * ‖fderiv ℝ w z‖) + ‖fderiv ℝ w z‖ ^ 2 := by
        ring
      linarith
    have hint : ∫ _z in ball x (R / 16), ‖fderiv ℝ w x‖ ^ 2 ≤
        ∫ z in ball x (R / 16), (2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z)) :=
      setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne)
        ((integrableOn_const measure_ball_lt_top.ne).add (h3.const_mul (2 * cN)))
        measurableSet_ball hpt
    have e1 : ∫ z in ball x (R / 16), (2 * H ^ 2 + 2 * cN * hs (fderiv ℝ w z)) =
        (∫ _z in ball x (R / 16), 2 * H ^ 2) + ∫ z in ball x (R / 16), 2 * cN * hs (fderiv ℝ w z) :=
      integral_add (integrableOn_const measure_ball_lt_top.ne) (h3.const_mul (2 * cN))
    rw [e1, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul, integral_const_mul,
      ← hΨ, hvol x (R / 16) hr] at hint
    have hΨr := hstep3 x hx2 (R / 16) hr hrR₁
    have hVpos : 0 < ω * (R / 16) ^ m := by positivity
    have h1 : ω * (R / 16) ^ m * ‖fderiv ℝ w x‖ ^ 2 ≤
        ω * (R / 16) ^ m * (2 * H ^ 2) + 2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) := by
      have : 2 * cN * Ψ x (R / 16) ≤ 2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) := by gcongr
      linarith
    have h2 : ‖fderiv ℝ w x‖ ^ 2 - 2 * H ^ 2 ≤
        2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) / (ω * (R / 16) ^ m) := by
      rw [le_div_iff₀ hVpos]
      linarith
    have e : 2 * cN * C₃ * (R / 16) ^ ((m : ℝ) - α) / (ω * (R / 16) ^ m) =
        2 * cN * (C₃ * (R / 16) ^ ((m : ℝ) - α)) / (ω * (R / 16) ^ m) := by ring
    rw [hC₆]
    linarith
  -- Step 6 (second Campanato pass): `Φ(x, r) ≤ C₈ r^{m+2α}` on `B_{R/4}(x₀)`, `r ≤ R₁`
  have hstep6 : ∀ x ∈ ball x₀ (R / 4), ∀ r, 0 < r → r ≤ R₁ →
      Φ x r ≤ C₈ * r ^ ((m : ℝ) + 2 * α) := by
    intro x hx r hr hrR₁
    have hxd : dist x x₀ < R / 4 := hx
    have hgoodρ : ∀ ρ, ρ ≤ R₁ → closedBall x ρ ⊆ ball x₀ R := fun ρ hρ =>
      closedBall_subset_ball' (by rw [hR₁] at hρ; linarith)
    have hΨb : ∀ ρ, 0 < ρ → ρ ≤ R₁ → Ψ x ρ ≤ m * C₆ * ω * ρ ^ m := by
      intro ρ hρ hρR
      obtain ⟨-, -, h3⟩ := hgood x ρ (hgoodρ ρ hρR)
      rw [hΨ]
      calc ∫ z in ball x ρ, hs (fderiv ℝ w z) ≤ ∫ _z in ball x ρ, (m : ℝ) * C₆ :=
            setIntegral_mono_on h3 (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
              (fun z hz => by
                have hzd : dist z x < ρ := hz
                have hz3 : z ∈ ball x₀ (3 * R / 8) := by
                  rw [mem_ball]; rw [hR₁] at hρR; linarith [dist_triangle z x x₀]
                calc hs (fderiv ℝ w z) ≤ m * ‖fderiv ℝ w z‖ ^ 2 := hs_le _
                  _ ≤ m * C₆ := by gcongr; exact hsup z hz3)
        _ = m * C₆ * ω * ρ ^ m := by rw [setIntegral_const, smul_eq_mul, hvol x ρ hρ]; ring
    have key := hIc (Φ x) R₁ ε₁ B₈ hε₁0.le hε₁c hB₈0
      (fun s _ _ => hΦ0 x s)
      (fun s ρ hs hsρ hρR => hΦmono x s ρ hs hsρ (hgoodρ ρ hρR))
      (fun s ρ hs hsρ hρR => by
        have hρ : 0 < ρ := hs.trans_le hsρ
        have h := (hcomp x ρ hρ hρR (by rw [hR₁] at hρR; linarith) s hs hsρ).1
        have hΨρ := hΨb ρ hρ hρR
        have e1 : ρ ^ (2 * α) * ρ ^ m = ρ ^ ((m : ℝ) + 2 * α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hρ]; ring_nf
        have : A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α)) ≤
            B₈ * ρ ^ ((m : ℝ) + 2 * α) := by
          have h1 : ρ ^ (2 * α) * Ψ x ρ ≤ m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) := by
            calc ρ ^ (2 * α) * Ψ x ρ ≤ ρ ^ (2 * α) * (m * C₆ * ω * ρ ^ m) := by gcongr
              _ = m * C₆ * ω * (ρ ^ (2 * α) * ρ ^ m) := by ring
              _ = m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) := by rw [e1]
          rw [hB₈]
          calc A₁ * K₁ * (ρ ^ (2 * α) * Ψ x ρ + ρ ^ ((m : ℝ) + 2 * α))
              ≤ A₁ * K₁ * (m * C₆ * ω * ρ ^ ((m : ℝ) + 2 * α) + ρ ^ ((m : ℝ) + 2 * α)) := by
                gcongr
            _ = A₁ * K₁ * (m * C₆ * ω + 1) * ρ ^ ((m : ℝ) + 2 * α) := by ring
        linarith)
      r R₁ hr hrR₁ le_rfl
    have hΦR₁ : Φ x R₁ ≤ m * C₆ * ω * R₁ ^ m :=
      (hΦΨ x R₁ hR₁0 (hgoodρ R₁ le_rfl)).trans (hΨb R₁ hR₁0 le_rfl)
    rw [Real.div_rpow hr.le hR₁0.le] at key
    calc Φ x r ≤ cc * (r ^ ((m : ℝ) + 2 * α) / R₁ ^ ((m : ℝ) + 2 * α) * Φ x R₁
          + B₈ * r ^ ((m : ℝ) + 2 * α)) := key
      _ ≤ cc * (r ^ ((m : ℝ) + 2 * α) / R₁ ^ ((m : ℝ) + 2 * α) * (m * C₆ * ω * R₁ ^ m)
          + B₈ * r ^ ((m : ℝ) + 2 * α)) := by gcongr
      _ = C₈ * r ^ ((m : ℝ) + 2 * α) := by rw [hC₈]; ring
  -- Step 7: `Dw` is `α`-Hölder on `B_{R/4}(x₀)` at scale `R₁/2`
  have hhol2 : ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖x - y‖ ≤ R₁ / 2 →
      ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀'' * Real.sqrt (cN * C₈) * ‖x - y‖ ^ α :=
    hII'' (fderiv ℝ w) x₀ (R / 4) R₁ (cN * C₈) (by positivity) hR₁0 (by positivity)
      (hDw.mono (closedBall_subset_ball (by rw [hR₁]; linarith)))
      (fun x hx ρ hρ hρR => by
        have hxd : dist x x₀ < R / 4 := hx
        have hxr : closedBall x ρ ⊆ ball x₀ R :=
          closedBall_subset_ball' (by rw [hR₁] at hρR; linarith)
        calc _ ≤ cN * Φ x ρ := hΦop x ρ hxr
          _ ≤ cN * (C₈ * ρ ^ ((m : ℝ) + 2 * α)) := by gcongr; exact hstep6 x hx ρ hρ hρR
          _ = cN * C₈ * ρ ^ ((m : ℝ) + 2 * α) := by ring)
  -- conclusion
  have hbd : ∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ Real.sqrt C₆ := by
    intro x hx
    have hx' : x ∈ ball x₀ (3 * R / 8) := ball_subset_ball (by linarith) hx
    calc ‖fderiv ℝ w x‖ = Real.sqrt (‖fderiv ℝ w x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C₆ := Real.sqrt_le_sqrt (hsup x hx')
  refine ⟨fun x hx => (hbd x hx).trans (le_max_left _ _), fun x hx y hy => ?_⟩
  by_cases hxy : ‖x - y‖ ≤ R₁ / 2
  · calc ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C₀'' * Real.sqrt (cN * C₈) * ‖x - y‖ ^ α :=
          hhol2 x hx y hy hxy
      _ ≤ max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α))
          * ‖x - y‖ ^ α := by
          gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · rw [not_le] at hxy
    have h3 : 1 ≤ (16 / R) ^ α * ‖x - y‖ ^ α := by
      rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
      apply Real.one_le_rpow _ hα0.le
      rw [hR₁] at hxy
      rw [div_mul_eq_mul_div, le_div_iff₀ hR]
      linarith
    calc ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ ‖fderiv ℝ w x‖ + ‖fderiv ℝ w y‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt C₆ := by linarith [hbd x hx, hbd y hy]
      _ ≤ 2 * Real.sqrt C₆ * ((16 / R) ^ α * ‖x - y‖ ^ α) :=
          le_mul_of_one_le_right (by positivity) h3
      _ = 2 * Real.sqrt C₆ * (16 / R) ^ α * ‖x - y‖ ^ α := by ring
      _ ≤ max (Real.sqrt C₆) (max (C₀'' * Real.sqrt (cN * C₈)) (2 * Real.sqrt C₆ * (16 / R) ^ α))
          * ‖x - y‖ ^ α := by
          gcongr; exact (le_max_right _ _).trans (le_max_right _ _)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
