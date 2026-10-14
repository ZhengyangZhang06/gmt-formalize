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

/-- **The Euclidean coefficient norm is a continuous seminorm dominated by the operator norm**
(Simon Ch. 6, 1.15 and 2.4; used by the smooth approximation of test forms behind the mass of
`τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})`
for strictly increasing `I : Fin n → Fin P` and `c_I α = 0` otherwise.  Then
`covectorEuclideanNorm α = ‖v α‖` for the coefficient vector
`v α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)`, which is linear in `α`; this gives the
triangle inequality and homogeneity.  `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖` gives the bound with
`C = √(card (Fin n → Fin P))`, and then the norm is `C`-Lipschitz, hence continuous. -/
theorem Submission.rsd_mw_tfa_norm_props : ∀ (P n : ℕ), (∀ α α' : Covector (Euclid P) n, covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α') ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ C * ‖α‖) ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) := by
  intro P n
  classical
  -- Step 1: the coefficients `c_I α` and the coefficient vector `v α`, with `N α = ‖v α‖`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  let c : (Fin n → Fin P) → Covector (Euclid P) n → ℝ := fun I α =>
    if StrictMono I then α (fun i => e (I i)) else 0
  let v : Covector (Euclid P) n → EuclideanSpace ℝ (Fin n → Fin P) := fun α =>
    WithLp.toLp 2 (fun I => c I α)
  have hN : ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖v α‖ := by
    intro α
    rw [EuclideanSpace.norm_eq]
    unfold covectorEuclideanNorm
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hI : StrictMono I <;> simp [v, c, e, hI]
  -- Step 2: `v` is additive and `ℝ`-homogeneous
  have hadd : ∀ α α' : Covector (Euclid P) n, v (α + α') = v α + v α' := by
    intro α α'
    simp only [v, ← WithLp.toLp_add]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  have hsmul : ∀ (t : ℝ) (α : Covector (Euclid P) n), v (t • α) = t • v α := by
    intro t α
    simp only [v, ← WithLp.toLp_smul]
    congr 1
    funext I
    by_cases hI : StrictMono I <;> simp [c, hI]
  -- Step 3: (i), the triangle inequality in `EuclideanSpace ℝ (Fin n → Fin P)`
  have h1 : ∀ α α' : Covector (Euclid P) n,
      covectorEuclideanNorm (α + α') ≤ covectorEuclideanNorm α + covectorEuclideanNorm α' := by
    intro α α'
    rw [hN, hN, hN, hadd]
    exact norm_add_le _ _
  -- Step 4: (ii), homogeneity of the Euclidean norm
  have h2 : ∀ (t : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α := by
    intro t α
    rw [hN, hN, hsmul, norm_smul, Real.norm_eq_abs]
  -- Step 5: `|c_I α| ≤ ‖α‖ ∏ₖ ‖e_{I(k)}‖ = ‖α‖`
  have hc : ∀ (I : Fin n → Fin P) (α : Covector (Euclid P) n), |c I α| ≤ ‖α‖ := by
    intro I α
    by_cases hI : StrictMono I
    · simpa [c, e, hI, Real.norm_eq_abs] using α.le_opNorm (fun i => e (I i))
    · simp [c, hI]
  -- Step 6: (iii) with `C = √(card (Fin n → Fin P))`
  have h3 : ∀ α : Covector (Euclid P) n,
      covectorEuclideanNorm α ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
    intro α
    have hsum : ∑ I, ‖(v α).ofLp I‖ ^ 2 ≤ ∑ _I : Fin n → Fin P, ‖α‖ ^ 2 :=
      Finset.sum_le_sum fun I _ => by
        simpa [v, Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc I α) 2
    rw [hN, EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ I, ‖(v α).ofLp I‖ ^ 2) ≤ Real.sqrt (∑ _I : Fin n → Fin P, ‖α‖ ^ 2) :=
          Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (Fintype.card (Fin n → Fin P)) * ‖α‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  -- Step 7: (iv), `|N α - N α'| ≤ N (α - α') ≤ C ‖α - α'‖`, so `N` is Lipschitz
  have hlip : ∀ α α' : Covector (Euclid P) n, dist (covectorEuclideanNorm α)
      (covectorEuclideanNorm α') ≤ Real.sqrt (Fintype.card (Fin n → Fin P)) * dist α α' := by
    intro α α'
    have ha : covectorEuclideanNorm α ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α' := by
      simpa only [sub_add_cancel] using h1 (α - α') α'
    have hb : covectorEuclideanNorm α' ≤
        covectorEuclideanNorm (α - α') + covectorEuclideanNorm α := by
      have h := h1 (α' - α) α
      rwa [sub_add_cancel, ← neg_sub, covectorEuclideanNorm_neg] at h
    have hC := h3 (α - α')
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    constructor <;> linarith
  exact ⟨h1, h2, ⟨_, Real.sqrt_nonneg _, h3⟩,
    (LipschitzWith.of_dist_le_mul (K := ⟨_, Real.sqrt_nonneg _⟩) hlip).continuous⟩
/-- **Simon §6.1** (the test-form topology, the case `β = 0`): if `ωⱼ → 0` in `𝒟ⁿ(U)`, the
`ωⱼ` vanish outside one compact `C ⊆ U`, and `supₓ ‖ωⱼ(x)‖ → 0`.  The compact set is the one in
`TestFormOnConverges`; uniform convergence of the `0`-th iterated derivatives on `C` gives the
bound on `C`, and `ωⱼ = 0` off `C`. -/
theorem Submission.dpf_pfc_testFormOnConverges_zero_uniform : ∀ (P n : ℕ) (U : Set (Euclid P)) (ωs : ℕ → TestFormOn U n), TestFormOnConverges ωs 0 → ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ U ∧ (∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε := by
  intro P n U ωs h
  obtain ⟨C, hC, hCU, hsupp, -, hderiv⟩ := h
  have hzero : ∀ j x, x ∉ C → (ωs j : DifferentialForm (Euclid P) n) x = 0 := fun j x hx =>
    image_eq_zero_of_notMem_tsupport fun hx' => hx (hsupp j hx')
  refine ⟨C, hC, hCU, hzero, fun ε hε => ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hderiv 0) ε hε] with j hj x
  by_cases hx : x ∈ C
  · have hjx := hj x hx
    simp only [ZeroMemClass.coe_zero, iteratedFDeriv_zero, Pi.zero_apply, dist_zero_left,
      norm_iteratedFDeriv_zero] at hjx
    exact hjx.le
  · rw [hzero j x hx, norm_zero]
    exact hε.le

/-- **A linear functional on test forms dominated by the coefficient sup norm is a current**
(Simon Ch. 6, proof of 7.2, where the `M`-absolutely convergent series define currents; the
topology of `𝒟ⁿ(U)` is that of §6.1).  Suppose `|L ω| ≤ c A` whenever `|ω(x)| ≤ c` for all `x`.
Then `A ≥ 0` (take `ω = 0`).  If `ωⱼ → 0` in `𝒟ⁿ(U)`, then for large `j` and all `x`,
`|ωⱼ(x)| ≤ C ‖ωⱼ(x)‖ ≤ (C + 1) ε`, so `|L ωⱼ| ≤ (C + 1) ε A < η` for
`ε = η / (2 (C + 1) (A + 1))`.  Hence `L` is sequentially continuous, and `⟨L, ·⟩` is the
current. -/
theorem Submission.cmc_fc_sc_current_of_coeff_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (L : TestFormOn U n →ₗ[ℝ] ℝ) (A : ℝ), (∀ (ω : TestFormOn U n) (c : ℝ), 0 < c → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |L ω| ≤ c * A) → ∃ Y : GeometricCurrentOn U n, ∀ ω : TestFormOn U n, Y ω = L ω := by
  intro P n U L A hL
  -- Step 1: `A ≥ 0`, from the bound at `ω = 0`, `c = 1`
  have hA : 0 ≤ A := by simpa using hL 0 1 one_pos fun x => by simp
  -- Step 2: `|α| ≤ C ‖α‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P n).2.2.1
  -- Step 4: `Y = ⟨L, ·⟩`; its continuity is Step 3
  refine ⟨⟨L, fun ωs hωs => ?_⟩, fun ω => rfl⟩
  -- Step 3: eventually `supₓ ‖ωⱼ(x)‖ ≤ ε`, hence `|L ωⱼ| ≤ (C + 1) ε A < η`
  obtain ⟨K, -, -, -, hunif⟩ := Submission.dpf_pfc_testFormOnConverges_zero_uniform P n U ωs hωs
  rw [Metric.tendsto_atTop]
  intro η hη
  have hC1 : 0 < C + 1 := by linarith
  have hA1 : 0 < A + 1 := by linarith
  set ε : ℝ := η / (2 * (C + 1) * (A + 1)) with hε
  have hεpos : 0 < ε := div_pos hη (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif ε hεpos)
  refine ⟨N, fun j hj => ?_⟩
  have hbound : ∀ x, covectorEuclideanNorm ((ωs j : DifferentialForm (Euclid P) n) x) ≤
      (C + 1) * ε := fun x =>
    (hC _).trans <| (mul_le_mul_of_nonneg_left (hN j hj x) hC0).trans <| by nlinarith
  have hkey : (C + 1) * ε * (A + 1) = η / 2 := by
    rw [hε]
    field_simp
  rw [Real.dist_eq, sub_zero]
  calc |L (ωs j)| ≤ (C + 1) * ε * A := hL (ωs j) _ (by positivity) hbound
    _ ≤ (C + 1) * ε * (A + 1) := by nlinarith
    _ = η / 2 := hkey
    _ < η := by linarith

/-- **Test forms are Lipschitz in the Euclidean coefficient norm** (the constant `c` of the cone
inequality, Simon Ch. 6, 2.27/2.30 as used in 8.2(4)–(6)).  `ω` is `C^∞` with compact support, so
`Dω` is continuous with compact support and `‖Dω(z)‖ ≤ L₀` for some `L₀ ≥ 0`; the mean value
inequality on the convex set `ℝᴾ` gives `‖ω(x) - ω(y)‖ ≤ L₀ ‖x - y‖`.  With the bound
`covectorEuclideanNorm β ≤ C ‖β‖` of `Submission.rsd_mw_tfa_norm_props`, `c = C L₀` works. -/
theorem Submission.cbrld_cone_testForm_coeff_lipschitz : ∀ (P k : ℕ) (U : Set (Euclid P)) (ω : TestFormOn U k), ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : Euclid P, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y) ≤ c * dist x y := by
  intro P k U ω
  -- Step 1: the coefficient norm is dominated by the operator norm, `|β| ≤ C ‖β‖`
  obtain ⟨C, hC0, hC⟩ := (Submission.rsd_mw_tfa_norm_props P k).2.2.1
  -- Step 2: `ω` is smooth with compact support, so `Dω` is continuous with compact support
  have hsm : IsSmoothForm (ω : DifferentialForm (Euclid P) k) := ω.property.1.1
  have hcs : HasCompactSupport (ω : DifferentialForm (Euclid P) k) := ω.property.1.2
  have hcont : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) :=
    hsm.continuous_fderiv (by simp)
  have hcs' : HasCompactSupport (fderiv ℝ (ω : DifferentialForm (Euclid P) k)) := hcs.fderiv ℝ
  -- Step 3: `Dω` is bounded, `‖Dω(z)‖ ≤ L ≤ max L 0`
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ z, ‖fderiv ℝ (ω : DifferentialForm (Euclid P) k) z‖ ≤ L :=
    Continuous.bounded_above_of_compact_support
      (f := fderiv ℝ (ω : DifferentialForm (Euclid P) k)) hcont hcs'
  -- Step 4: the mean value inequality on the convex set `ℝᴾ`
  have hdiff : Differentiable ℝ (ω : DifferentialForm (Euclid P) k) :=
    hsm.differentiable (by simp)
  have hmv : ∀ x y : Euclid P, ‖(ω : DifferentialForm (Euclid P) k) x -
      (ω : DifferentialForm (Euclid P) k) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
    convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
      (fun z _ => (hL z).trans (le_max_left _ _)) (mem_univ y) (mem_univ x)
  -- Step 5: `c = C · max L 0`
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right _ _), fun x y => ?_⟩
  have h1 := hC ((ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y)
  have h2 := mul_le_mul_of_nonneg_left (hmv x y) hC0
  rw [dist_eq_norm]
  calc covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) k) x -
        (ω : DifferentialForm (Euclid P) k) y)
      ≤ C * ‖(ω : DifferentialForm (Euclid P) k) x - (ω : DifferentialForm (Euclid P) k) y‖ := h1
    _ ≤ C * (max L 0 * ‖x - y‖) := h2
    _ = C * max L 0 * ‖x - y‖ := by ring
/-- **Radial retraction onto the closed unit ball is nonexpansive towards the ball** (step 0(d)
of `regcomp_exists_smooth_unit_form_approx`).  If `‖y‖ ≤ 1`, then
`‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖`: for `‖x‖ ≤ 1` the retraction fixes `x`; for `s = ‖x‖ > 1`,
`‖x - y‖² - ‖s⁻¹ • x - y‖² = s² - 1 - 2(1 - s⁻¹)⟨x, y⟩ ≥ (s - 1)²` by Cauchy–Schwarz. -/
theorem Submission.regcomp_norm_radial_retraction_sub_le : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x y : E), ‖y‖ ≤ 1 → ‖(max 1 ‖x‖)⁻¹ • x - y‖ ≤ ‖x - y‖ := by
  intro E _ _ x y hy
  rcases le_or_gt ‖x‖ 1 with hx | hx
  · -- Step 1: if `‖x‖ ≤ 1`, the retraction fixes `x`.
    rw [max_eq_left hx, inv_one, one_smul]
  · -- Steps 2–5: `s = ‖x‖ > 1`; compare the squared distances.
    rw [max_eq_right hx.le]
    have hs : 0 < ‖x‖ := one_pos.trans hx
    -- Cauchy–Schwarz with `‖y‖ ≤ 1`: `⟨x, y⟩ ≤ s`; and `s⁻¹ < 1`, `s⁻¹ s = 1`.
    have hxy : inner ℝ x y ≤ ‖x‖ :=
      (real_inner_le_norm x y).trans (mul_le_of_le_one_right hs.le hy)
    have hinv : ‖x‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
    have hcancel : ‖x‖⁻¹ * ‖x‖ = 1 := inv_mul_cancel₀ hs.ne'
    -- `‖s⁻¹ • x - y‖² = 1 - 2s⁻¹⟨x, y⟩ + ‖y‖²`.
    have h2 : ‖‖x‖⁻¹ • x - y‖ ^ 2 = 1 - 2 * (‖x‖⁻¹ * inner ℝ x y) + ‖y‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_left, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hs), hcancel, one_pow]
    -- The difference of the squares is at least `(s - 1)² ≥ 0`.
    have key : ‖‖x‖⁻¹ • x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      rw [h2, norm_sub_sq_real]
      nlinarith [mul_nonneg (sub_nonneg.2 hinv.le) (sub_nonneg.2 hxy), sq_nonneg (‖x‖ - 1)]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 key

/-- **The Euclidean coefficient norm** `|α|_E = covectorEuclideanNorm α` on `Λⁿ(ℝᴾ)` (Simon
6.1.15) is a continuous seminorm dominated by the operator norm, and the radial retraction
`v ↦ (max 1 |v|_E)⁻¹ v` onto its unit ball does not increase the distance to points of that ball.

The coefficient map `Φ α = (ev_j α)_j ∈ ℓ²(Fin n → Fin P)`, with
`ev_j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j` and `0` otherwise, is continuous linear
with `‖Φ α‖ = |α|_E` (`EuclideanSpace.norm_eq`).  So (i)–(iii) are those of `‖·‖ ∘ Φ`, (iv) holds
with `c = 1 + ‖Φ‖`, and (v) is `regcomp_norm_radial_retraction_sub_le` for `x = Φ v`, `y = Φ b`. -/
theorem Submission.regcomp_covectorEuclideanNorm_seminorm_retract : ∀ (P n : ℕ), ∃ c : ℝ, 0 < c ∧ Continuous (fun α : Covector (Euclid P) n => covectorEuclideanNorm α) ∧ (∀ α β : Covector (Euclid P) n, covectorEuclideanNorm (α + β) ≤ covectorEuclideanNorm α + covectorEuclideanNorm β) ∧ (∀ (t : ℝ) (α : Covector (Euclid P) n), covectorEuclideanNorm (t • α) = |t| * covectorEuclideanNorm α) ∧ (∀ α : Covector (Euclid P) n, covectorEuclideanNorm α ≤ c * ‖α‖) ∧ ∀ v b : Covector (Euclid P) n, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm ((max 1 (covectorEuclideanNorm v))⁻¹ • v - b) ≤ covectorEuclideanNorm (v - b) := by
  intro P n
  classical
  -- `ev j α = α(e_{j 0}, …, e_{j (n-1)})` for increasing `j`, and `0` otherwise
  let ev : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun j =>
    if StrictMono j then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ
        (fun i ↦ EuclideanSpace.basisFun (Fin P) ℝ (j i))
    else 0
  -- the coefficient map `Φ : Λⁿ → ℓ²(Fin n → Fin P)`
  let Φ : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P) :=
    (EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi ev)
  have hΦ : ∀ α, ‖Φ α‖ = covectorEuclideanNorm α := by
    intro α
    rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : StrictMono j <;> simp [Φ, ev, hj]
  refine ⟨1 + ‖Φ‖, by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_norm.comp Φ.continuous).congr hΦ
  · intro α β
    simpa only [← hΦ, map_add] using norm_add_le (Φ α) (Φ β)
  · intro t α
    simp only [← hΦ, map_smul, norm_smul, Real.norm_eq_abs]
  · intro α
    rw [← hΦ]
    exact (Φ.le_opNorm α).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg α))
  · intro v b hb
    rw [← hΦ] at hb
    simp only [← hΦ, map_sub, map_smul]
    exact Submission.regcomp_norm_radial_retraction_sub_le (EuclideanSpace ℝ (Fin n → Fin P))
      (Φ v) (Φ b) hb
/-- **Evaluation of a finite-mass current is bounded by mass times the coefficient sup norm**
(Simon Ch. 6, 2.4: `M(X) = sup_{|ω| ≤ 1} X(ω)`, so `|X(ω)| ≤ sup |ω| · M(X)`; used for the
mass-absolutely convergent series in the proof of 7.2).  For `|s| = c⁻¹` the rescaled form
`s • ω` is admissible for `M(X) = M_U(X)`, as `|s • ω(x)| = c⁻¹ |ω(x)| ≤ 1` by homogeneity of
the coefficient norm; hence `s X(ω) = X(s • ω) ≤ M(X)`.  The choices `s = ±c⁻¹` give
`±X(ω) ≤ c M(X)`. -/
theorem Submission.cmc_fc_sc_abs_le_mul_mass : ∀ (P n : ℕ) (U : Set (Euclid P)) (X : GeometricCurrentOn U n) (ω : TestFormOn U n) (c : ℝ), 0 < c → X.mass ≠ ∞ → (∀ x, covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c) → |X ω| ≤ c * X.mass.toReal := by
  intro P n U X ω c hc hX hω
  -- Step 1: for `|s| = c⁻¹`, `s • ω` is admissible, so `s X(ω) = X(s • ω) ≤ M(X)`
  have hbound : ∀ s : ℝ, |s| = c⁻¹ → s * X ω ≤ X.mass.toReal := by
    intro s hs
    have hadm : s • ω ∈ massAdmissibleOn U n U := by
      refine ⟨(s • ω).property.2, fun x => ?_⟩
      have hx : ((s • ω : TestFormOn U n) : DifferentialForm (Euclid P) n) x =
          s • ((ω : DifferentialForm (Euclid P) n) x) := rfl
      rw [hx, (Submission.rsd_mw_tfa_norm_props P n).2.1, hs]
      calc c⁻¹ * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ c⁻¹ * c :=
            mul_le_mul_of_nonneg_left (hω x) (inv_nonneg.mpr hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    have hle : ENNReal.ofReal (X (s • ω)) ≤ X.mass := X.le_massOn hadm
    rw [ENNReal.ofReal_le_iff_le_toReal hX] at hle
    have hlin : X (s • ω) = s * X ω := by
      rw [map_smul, smul_eq_mul]
    rwa [hlin] at hle
  -- Step 2: `s = c⁻¹` and `s = -c⁻¹` give `X(ω) ≤ c M(X)` and `-X(ω) ≤ c M(X)`
  have hinv : |c⁻¹| = c⁻¹ := abs_of_pos (inv_pos.mpr hc)
  have hpos := mul_le_mul_of_nonneg_left (hbound c⁻¹ hinv) hc.le
  have hneg := mul_le_mul_of_nonneg_left (hbound (-c⁻¹) (by rw [abs_neg, hinv])) hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hpos
  rw [neg_mul, mul_neg, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hneg
  exact abs_le.mpr ⟨by linarith, hpos⟩
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
/-- **Support of a current vanishing away from a compact set** (Simon 6.2.11).  If `K ⊆ U` is
compact and `F ∈ 𝒟ₙ(U)` kills every `ω ∈ 𝒟ⁿ(U)` with `spt ω ∩ K = ∅`, then `spt F ⊆ K` and
`spt F` is compact.  For `y ∈ U \ K` choose `B_s(y) ⊆ U \ K`: the ball `W = B_{s/2}(y)` has compact
closure `⊆ B̄_{s/2}(y) ⊆ U \ K` and every form supported in `W` misses `K`, so `y ∈ Z(F)`.  Hence
`spt F = K \ Z(F)`, compact because the zero region `Z(F)` is open. -/
theorem Submission.rsd_cmr_support_subset_of_vanish : ∀ (P n : ℕ) (U K : Set (Euclid P)) (F : GeometricCurrentOn U n), IsOpen U → IsCompact K → K ⊆ U → (∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → F ω = 0) → F.support ⊆ K ∧ IsCompact F.support := by
  intro P n U K F hU hK hKU hvan
  -- Steps 1–2: no point of `U \ K` lies in `spt F = U \ Z(F)`, so `spt F ⊆ K`
  have hsub : F.support ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨s, hs, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff hK.isClosed) y ⟨hy.1, hyK⟩
    apply hy.2
    -- `W = B_{s/2}(y)` is one of the open sets whose union is `Z(F)`
    refine ⟨ball y (s / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self (by positivity)⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall y (s / 2)).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_{s/2}(y) ⊆ B_s(y) ⊆ U \ K ⊆ U`
      exact closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (by linarith)).trans (hball.trans sdiff_subset))
    · -- a form supported in `W ⊆ U \ K` misses `K`, so `F` kills it
      intro ω hω
      exact hvan ω (Set.disjoint_of_subset_left
        (hω.trans ((ball_subset_ball (by linarith)).trans hball)) disjoint_sdiff_left)
  -- Step 3: `spt F = K \ Z(F)` is compact, `Z(F)` being open
  refine ⟨hsub, ?_⟩
  have heq : F.support = K \ F.zeroRegion :=
    Set.ext fun x => ⟨fun hx => ⟨hsub hx, hx.2⟩, fun hx => ⟨hKU hx.1, hx.2⟩⟩
  rw [heq]
  exact hK.diff F.isOpen_zeroRegion

/-- **Slice and restriction forms along `x ↦ ι(t, x) = (t, x)`** (the forms entering the cylinder
`[[(0, 1)]] × X` of Simon Ch. 6, 2.18–2.21 and the homotopy formula 2.25, as used for the
Lipschitz push-forward in the deformation theorem).  With `J v = (0, v)` and `e₀ = (1, 0, …, 0)`,
the forms `η_t = (ω(·).curryLeft e₀)(ι(t, ·)) ∘ J`, `β_s = ω(ι(s, ·)) ∘ J` and
`γ_t = (Dω(ι(t, ·)) e₀) ∘ J` are affine pull-backs along the isometry `x ↦ single(0, t) + J x`,
which is proper, so they are test forms.  Every slice family satisfies `η_t(x) = S(ω(ι(t, x)))`
for the slice map `S α = (α.curryLeft e₀).compContinuousLinearMap J`; the covector bounds (L1),
(L2) and `‖J‖ ≤ 1` give `|S α| ≤ |α|`, which with `Submission.cbrld_cone_testForm_coeff_lipschitz`
yields the pointwise bound, the Lipschitz estimate in `t` and the support inclusion. -/
theorem Submission.dimred_mbl_dt_lpc_slice_forms : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)), (∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → (∀ (t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η t : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))))) ∧ (∀ (s t : ℝ) (x : Euclid N), covectorEuclideanNorm ((η s : DifferentialForm (Euclid N) k) x - (η t : DifferentialForm (Euclid N) k) x) ≤ c * |s - t|) ∧ ∀ t : ℝ, tsupport (η t : DifferentialForm (Euclid N) k) ⊆ {x : Euclid N | (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) ∈ tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1))}) ∧ ∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) k), (∃ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∃ γ : ℝ → TestFormOn (univ : Set (Euclid N)) k, ∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (γ t : DifferentialForm (Euclid N) k) x v = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ ∀ β : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∀ (s : ℝ) (x : Euclid N), covectorEuclideanNorm ((β s : DifferentialForm (Euclid N) k) x) ≤ covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := by
  rintro ⟨hL1, hL2⟩
  -- Step 1(a): the embedding `J v = (0, v)` is linear with `‖J v‖ = ‖v‖`
  have hJex : ∀ N : ℕ, ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧ ∀ v, ‖J v‖ = ‖v‖ := by
    intro N
    let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun v w => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c v => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    have hn : ∀ v, ‖Jl v‖ = ‖v‖ := by
      intro v
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_succ]
      simp [Jl]
    exact ⟨LinearMap.mkContinuous Jl 1 fun v => by rw [hn, one_mul], fun v => rfl, hn⟩
  -- Step 1(a)–(d): `‖J‖ ≤ 1`, `ι(t, x) = single(0, t) + J x`, each `x ↦ ι(t, x)` is an
  -- isometry, hence proper, and `dist (ι(s, x)) (ι(t, x)) = |s - t|`
  have hJprops : ∀ (N : ℕ) (J : Euclid N →L[ℝ] Euclid (N + 1)),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) → (∀ v, ‖J v‖ = ‖v‖) →
      ‖J‖ ≤ 1 ∧
      (∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
        EuclideanSpace.single 0 t + J x) ∧
      (∀ t : ℝ, IsProperMap fun x => EuclideanSpace.single (0 : Fin (N + 1)) t + J x) ∧
      ∀ (s t : ℝ) (x : Euclid N),
        dist (EuclideanSpace.single (0 : Fin (N + 1)) s + J x)
          (EuclideanSpace.single 0 t + J x) = |s - t| := by
    intro N J hJ hn
    refine ⟨J.opNorm_le_bound zero_le_one fun v => by rw [hn, one_mul], fun t x => ?_,
      fun t => ?_, fun s t x => ?_⟩
    · rw [hJ]
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · have hiso : Isometry fun x => EuclideanSpace.single (0 : Fin (N + 1)) t + J x :=
        Isometry.of_dist_eq fun x y => by
          rw [dist_add_left, dist_eq_norm, dist_eq_norm, ← map_sub, hn]
      exact hiso.isClosedEmbedding.isProperMap
    · rw [dist_add_right]
      simp [Real.dist_eq]
  refine ⟨fun N k ω => ?_, fun N k ω => ?_⟩
  · obtain ⟨J, hJ, hn⟩ := hJex N
    obtain ⟨hJ1, hι, hprop, hdist⟩ := hJprops N J hJ hn
    -- Step 2: the slice map `S α = (α.curryLeft e₀).compContinuousLinearMap J` is continuous
    -- linear, `S α v = α (e₀, J v)`, and `|S α| ≤ ‖J‖ ^ k |α.curryLeft e₀| ≤ |α|` by (L1), (L2)
    let Φ : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid (N + 1)) k :=
      (ContinuousLinearMap.apply ℝ (Covector (Euclid (N + 1)) k) (EuclideanSpace.single 0 1)).comp
        (ContinuousAlternatingMap.curryLeftLI (𝕜 := ℝ) (E := Euclid (N + 1)) (F := ℝ)
          (n := k)).toContinuousLinearMap
    let S : Covector (Euclid (N + 1)) (k + 1) →L[ℝ] Covector (Euclid N) k :=
      (ContinuousAlternatingMap.compContinuousLinearMapCLM J).comp Φ
    have hS : ∀ (α : Covector (Euclid (N + 1)) (k + 1)) (v : Fin k → Euclid N),
        S α v = α (Fin.cons (EuclideanSpace.single 0 1) fun i => J (v i)) := fun α v => rfl
    have hSb : ∀ α, covectorEuclideanNorm (S α) ≤ covectorEuclideanNorm α := by
      intro α
      have h1 := hL1 N (N + 1) k J (α.curryLeft (EuclideanSpace.single 0 1))
      have h2 := hL2 (N + 1) k (EuclideanSpace.single 0 1) α
      have he : ‖(EuclideanSpace.single (0 : Fin (N + 1)) (1 : ℝ))‖ = 1 := by simp
      have hJk : ‖J‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hJ1
      have h0 := covectorEuclideanNorm_nonneg (α.curryLeft (EuclideanSpace.single 0 1))
      rw [he, one_mul] at h2
      calc covectorEuclideanNorm (S α)
          = covectorEuclideanNorm
              ((α.curryLeft (EuclideanSpace.single 0 1)).compContinuousLinearMap J) := rfl
        _ ≤ ‖J‖ ^ k * covectorEuclideanNorm (α.curryLeft (EuclideanSpace.single 0 1)) := h1
        _ ≤ 1 * covectorEuclideanNorm (α.curryLeft (EuclideanSpace.single 0 1)) :=
            mul_le_mul_of_nonneg_right hJk h0
        _ ≤ covectorEuclideanNorm α := by rw [one_mul]; exact h2
    -- Step 3: (A1), `η_t` is the affine pull-back of `ω₁ = ω(·).curryLeft e₀` along
    -- `x ↦ ι(t, x)`
    have hω₁ : IsTestForm fun y => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) :=
      ⟨Φ.contDiff.comp ω.property.1.1, ω.property.1.2.comp_left (map_zero Φ)⟩
    refine ⟨⟨fun t => ⟨affinePullbackForm J (EuclideanSpace.single 0 t)
      (fun y => Φ ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y)),
      affinePullbackForm_isTestForm J _ (hprop t) hω₁, subset_univ _⟩,
      fun t x v => ?_⟩, ?_⟩
    · show S ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
        (EuclideanSpace.single 0 t + J x)) v = _
      rw [hS, ← hι t x]
      simp only [hJ]
    -- Step 5: the Lipschitz constant `c` of `ω`, fixed before the family `η`
    obtain ⟨c, hc0, hc⟩ :=
      Submission.cbrld_cone_testForm_coeff_lipschitz (N + 1) (k + 1) univ ω
    refine ⟨c, hc0, fun η hη => ?_⟩
    -- Step 4: every slice family is `η_t(x) = S(ω(ι(t, x)))`
    have hnf : ∀ t x, (η t : DifferentialForm (Euclid N) k) x =
        S ((ω : DifferentialForm (Euclid (N + 1)) (k + 1))
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))) := by
      intro t x
      ext v
      rw [hη t x v, hS]
      simp only [hJ]
    -- Step 5: (A2), (i) the pointwise bound, (ii) the Lipschitz estimate, (iii) the support
    refine ⟨fun t x => ?_, fun s t x => ?_, fun t => ?_⟩
    · rw [hnf]
      exact hSb _
    · rw [hnf, hnf, ← map_sub]
      calc _ ≤ _ := hSb _
        _ ≤ c * dist (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)) : Euclid (N + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) := hc _ _
        _ = c * |s - t| := by rw [hι, hι, hdist]
    · have hcont : Continuous fun x : Euclid N =>
          (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) := by
        simp only [hι]
        exact continuous_const.add J.continuous
      refine closure_minimal (fun x hx => ?_) ((isClosed_tsupport _).preimage hcont)
      by_contra hx'
      apply hx
      rw [hnf, image_eq_zero_of_notMem_tsupport hx', map_zero]
  · obtain ⟨J, hJ, hn⟩ := hJex N
    obtain ⟨hJ1, hι, hprop, -⟩ := hJprops N J hJ hn
    have hω : IsTestForm (ω : DifferentialForm (Euclid (N + 1)) k) := ω.property.1
    -- Step 6: (B1), `β_s` is the affine pull-back of `ω` along `x ↦ ι(s, x)`
    refine ⟨⟨fun s => ⟨affinePullbackForm J (EuclideanSpace.single 0 s)
      (ω : DifferentialForm (Euclid (N + 1)) k),
      affinePullbackForm_isTestForm J _ (hprop s) hω, subset_univ _⟩,
      fun s x v => ?_⟩, ?_, ?_⟩
    · show (ω : DifferentialForm (Euclid (N + 1)) k) (EuclideanSpace.single 0 s + J x)
        (fun i => J (v i)) = _
      rw [← hι s x]
      simp only [hJ]
    -- Step 6: (B2), `γ_t` is the affine pull-back of the test form `ω' = Dω(·) e₀`
    · have hω' : IsTestForm fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y
          (EuclideanSpace.single 0 1) :=
        ⟨(hω.1.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
            contDiff_const,
          (hω.2.fderiv ℝ).comp_left
            (g := fun L : Euclid (N + 1) →L[ℝ] Covector (Euclid (N + 1)) k =>
              L (EuclideanSpace.single 0 1)) rfl⟩
      refine ⟨fun t => ⟨affinePullbackForm J (EuclideanSpace.single 0 t)
        (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y
          (EuclideanSpace.single 0 1)),
        affinePullbackForm_isTestForm J _ (hprop t) hω', subset_univ _⟩, fun t x v => ?_⟩
      show fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (EuclideanSpace.single 0 t + J x)
        (EuclideanSpace.single 0 1) (fun i => J (v i)) = _
      rw [← hι t x]
      simp only [hJ]
    -- Step 7: (B3), `β_s(x) = ω(ι(s, x)).compContinuousLinearMap J`, so (L1) and `‖J‖ ≤ 1`
    -- give `|β_s(x)| ≤ |ω(ι(s, x))|`
    · intro β hβ s x
      have hnf : (β s : DifferentialForm (Euclid N) k) x =
          ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))).compContinuousLinearMap J := by
        ext v
        rw [hβ s x v, ContinuousAlternatingMap.compContinuousLinearMap_apply]
        simp only [Function.comp_def, hJ]
      rw [hnf]
      have hJk : ‖J‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hJ1
      calc _ ≤ ‖J‖ ^ k * covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) := hL1 _ _ _ _ _
        _ ≤ 1 * covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k)
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))) :=
          mul_le_mul_of_nonneg_right hJk (covectorEuclideanNorm_nonneg _)
        _ = _ := one_mul _
/-- **Exterior derivative along a slice.**  Write `ι(t, x) = (t, x)`, `e₀ = (1, 0, …, 0)` and
`J v = (0, v)`.  (a) If `η_t(x)(v) = ω(ι(t, x))(e₀, Jv)` for a test form `ω` of degree `k + 1`,
then `dω(ι(t, x))(e₀, Jv) = (Dω(ι(t, x))e₀)(Jv) − d(η_t)(x)(v)`.  (b) In degree `0`,
`dω(ι(t, x))(e₀) = (Dω(ι(t, x))e₀)()`. -/
theorem Submission.dimred_mbl_dt_lpc_slice_extDeriv : ((∀ (N k : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N), exteriorDerivative (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) - exteriorDerivative (η t : DifferentialForm (Euclid N) k) x v) ∧ ∀ (N : ℕ) (ω : TestFormOn (univ : Set (Euclid (N + 1))) 0) (t : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N), exteriorDerivative (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
  refine ⟨?_, ?_⟩
  -- (a)
  · intro N k ω η hη
    -- the continuous linear map `J v = (0, v)`, with `ι(t, x) = single 0 t + J x`
    obtain ⟨J, hJ, hι⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
        (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧
        ∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
          EuclideanSpace.single 0 t + J x := by
      let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
        { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
          map_add' := by
            intro a b
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp
          map_smul' := by
            intro c a
            ext i
            refine Fin.cases ?_ (fun j => ?_) i <;> simp }
      refine ⟨LinearMap.toContinuousLinearMap Jl, fun v => rfl, fun t x => ?_⟩
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Jl]
      · simp [Jl]
    intro t x v
    have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) :=
      ω.property.1.1.differentiable (by simp)
    have hηd : Differentiable ℝ (η t : DifferentialForm (Euclid N) k) :=
      (η t).property.1.1.differentiable (by simp)
    -- coordinate formula for `d`, split into the term `i = 0` and the terms `i = j + 1`
    rw [exteriorDerivative_apply (hωd _), exteriorDerivative_apply (hηd _), Fin.sum_univ_succ]
    -- chain rule through the affine slice map `x ↦ ι(t, x)`
    have hchain : ∀ (u : Fin k → Euclid N) (w : Euclid N),
        fderiv ℝ (fun x' => (η t : DifferentialForm (Euclid N) k) x' u) x w =
          fderiv ℝ (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (J w) := by
      intro u w
      have hfun : (fun x' => (η t : DifferentialForm (Euclid N) k) x' u) =
          (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            ∘ (fun x' => EuclideanSpace.single 0 t + J x') := by
        funext x'
        simp only [Function.comp_apply, ← hι]
        exact hη t x' u
      have hg : DifferentiableAt ℝ (fun y => (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (u i))))))
            (EuclideanSpace.single 0 t + J x) :=
        (hωd _).continuousAlternatingMap_apply_const _
      have hA : HasFDerivAt (fun x' : Euclid N => EuclideanSpace.single 0 t + J x') J x :=
        J.hasFDerivAt.const_add _
      rw [hfun, (hg.hasFDerivAt.comp x hA).fderiv, ← hι]
      rfl
    -- the term `i = 0` is `(Dω(ι(t, x))e₀)(Jv)`
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.removeNth_zero, Fin.tail_cons]
    rw [fderiv_continuousAlternatingMap_apply_const (hωd _)]
    simp only [ContinuousLinearMap.flipAlternating_apply_apply]
    -- the terms `i = j + 1` are minus the terms of `d(η_t)(x)(v)`
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hchain, hJ]
    have hrm : Fin.removeNth j.succ (Fin.cons (EuclideanSpace.single 0 1)
        (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))) :
          Fin (k + 1 + 1) → Euclid (N + 1)) =
        Fin.cons (EuclideanSpace.single 0 1)
          (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (Fin.removeNth j v i)))) :=
      Fin.cons_comp_succ_succAbove _ _ j
    rw [hrm, pow_succ]
    simp only [mul_neg, mul_one, neg_smul]
  -- (b): in degree `0` only the term `i = 0` occurs
  · intro N ω t x v
    have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) 0) :=
      ω.property.1.1.differentiable (by simp)
    rw [exteriorDerivative_apply (hωd _), Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero, Fin.removeNth_zero]
    rw [fderiv_continuousAlternatingMap_apply_const (hωd _)]
    simp only [ContinuousLinearMap.flipAlternating_apply_apply]
    congr 1

/-- **Fundamental theorem of calculus under a finite-mass current** (step 5 of
`dimred_mbl_dt_lp_cylinder`).  Let `X ∈ 𝒟ₖ(ℝᴺ)` have finite mass, `ω ∈ 𝒟ᵏ(ℝᴺ⁺¹)`, and let
`β_s(x) = ω(ι(s, x)) ∘ J`, `γ_t(x) = (Dω(ι(t, x)) e₀) ∘ J`, where `ι(t, x) = (t, x)` and
`J v = (0, v)`.  Then `∫₀¹ X(γ_t) dt = X(β₁) - X(β₀)`: (REP) gives `X(φ) = ∫ ξ(x)(φ(x)) dμ` with
`μ` finite and `ξ` bounded, Fubini swaps the integrals, and the fundamental theorem of calculus
applies to `t ↦ ξ(x)(β_t(x))` for each `x`. -/
theorem Submission.dimred_mbl_dt_lpc_ftc_current : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ → ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) k) (β γ : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (β s : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (γ t : DifferentialForm (Euclid N) k) x v = fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) → ∫ t in (0 : ℝ)..1, X (γ t) = X (β 1) - X (β 0) := by
  intro REP N k X hX ω β γ hβ hγ
  -- Step 1: (REP) with `U = univ` represents `X` by a finite measure `μ` and an orientation `ξ`.
  have hloc : ∀ W : Set (Euclid N), IsOpen W → CompactlyContained W univ → X.massOn W < ∞ :=
    fun W _ _ => lt_of_le_of_lt (X.massOn_mono (subset_univ W)) hX
  obtain ⟨μ, ξ, -, -, hμW, hξm, hξb, hrep, -⟩ := REP N k univ X isOpen_univ hloc
  have : IsFiniteMeasure μ := ⟨by rw [← hμW univ isOpen_univ]; exact hX⟩
  -- Step 2: `J v = (0, v)`, so `ι(t, x) = t e₀ + J x`; normal forms `β_s(x) = C_J(ω(ι(s, x)))`
  -- and `γ_t(x) = C_J(Dω(ι(t, x)) e₀)` with `C_J α = α ∘ J`.
  obtain ⟨J, hJ, hι⟩ : ∃ J : Euclid N →L[ℝ] Euclid (N + 1),
      (∀ v, J v = WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))) ∧
      ∀ (t : ℝ) (x : Euclid N), (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)) : Euclid (N + 1)) =
        t • EuclideanSpace.single 0 1 + J x := by
    let Jl : Euclid N →ₗ[ℝ] Euclid (N + 1) :=
      { toFun := fun v => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp v))
        map_add' := fun a b => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        map_smul' := fun c a => by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp }
    refine ⟨LinearMap.toContinuousLinearMap Jl, fun v => rfl, fun t x => ?_⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Jl]
  set e₀ : Euclid (N + 1) := EuclideanSpace.single 0 1
  let CJ : Covector (Euclid (N + 1)) k →L[ℝ] Covector (Euclid N) k :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM J
  have hCJ : ∀ a : Covector (Euclid (N + 1)) k, CJ a = a.compContinuousLinearMap J := fun a => rfl
  have hβc : ∀ s x, (β s : DifferentialForm (Euclid N) k) x =
      CJ ((ω : DifferentialForm (Euclid (N + 1)) k) (s • e₀ + J x)) := by
    intro s x
    ext v
    rw [hβ s x v, hCJ, hι s x]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hJ]
  have hγc : ∀ t x, (γ t : DifferentialForm (Euclid N) k) x =
      CJ (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (t • e₀ + J x) e₀) := by
    intro t x
    ext v
    rw [hγ t x v, hCJ, hι t x]
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def, hJ]
  -- Step 3: `ω` is `C¹` with compact support, so `ω` and `y ↦ Dω(y) e₀` are bounded.
  have hωC : ContDiff ℝ 1 (ω : DifferentialForm (Euclid (N + 1)) k) :=
    ω.property.1.1.of_le (by simp)
  have hωd : Differentiable ℝ (ω : DifferentialForm (Euclid (N + 1)) k) :=
    hωC.differentiable one_ne_zero
  have hDω : Continuous (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k)) :=
    hωC.continuous_fderiv one_ne_zero
  have hωcont : Continuous (ω : DifferentialForm (Euclid (N + 1)) k) := hωC.continuous
  have hωcs : HasCompactSupport (ω : DifferentialForm (Euclid (N + 1)) k) := ω.property.1.2
  have hDe : Continuous (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y e₀) :=
    hDω.clm_apply continuous_const
  have hDecs : HasCompactSupport
      (fun y => fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) y e₀) :=
    HasCompactSupport.comp_left
      (g := fun L : Euclid (N + 1) →L[ℝ] Covector (Euclid (N + 1)) k => L e₀)
      (hωcs.fderiv ℝ) (by simp)
  -- Step 4: `t ↦ ξ(x)(β_t(x))` has derivative `ξ(x)(γ_t(x))` (chain rule).
  have hderiv : ∀ (x : Euclid N) (t : ℝ),
      HasDerivAt (fun s => ξ x ((β s : DifferentialForm (Euclid N) k) x))
        (ξ x ((γ t : DifferentialForm (Euclid N) k) x)) t := by
    intro x t
    have h1 : HasDerivAt (fun s : ℝ => s • e₀ + J x) e₀ t := by
      simpa using ((hasDerivAt_id t).smul_const e₀).add_const (J x)
    have h2 : HasDerivAt (fun s => (ω : DifferentialForm (Euclid (N + 1)) k) (s • e₀ + J x))
        (fderiv ℝ (ω : DifferentialForm (Euclid (N + 1)) k) (t • e₀ + J x) e₀) t :=
      (hωd _).hasFDerivAt.comp_hasDerivAt t h1
    have h4 := (ξ x).hasFDerivAt.comp_hasDerivAt t (CJ.hasFDerivAt.comp_hasDerivAt t h2)
    simp only [hβc, hγc]
    exact h4
  -- Step 5: continuity, and uniform bounds via `|α| ≤ c ‖α‖` (coefficient-norm toolkit (iv)).
  have hγcont : Continuous
      (fun p : ℝ × Euclid N => (γ p.1 : DifferentialForm (Euclid N) k) p.2) := by
    simp only [hγc]
    exact CJ.continuous.comp ((hDω.comp ((continuous_fst.smul continuous_const).add
      (J.continuous.comp continuous_snd))).clm_apply continuous_const)
  have hβcont : ∀ s, Continuous (fun x => (β s : DifferentialForm (Euclid N) k) x) := by
    intro s
    simp only [hβc]
    exact CJ.continuous.comp (hωcont.comp (continuous_const.add J.continuous))
  obtain ⟨c, hc, -, -, -, hcle, -⟩ := Submission.regcomp_covectorEuclideanNorm_seminorm_retract N k
  obtain ⟨M₁, hM₁⟩ := hDe.bounded_above_of_compact_support hDecs
  obtain ⟨M₀, hM₀⟩ := hωcont.bounded_above_of_compact_support hωcs
  have hγb : ∀ t x, ‖ξ x ((γ t : DifferentialForm (Euclid N) k) x)‖ ≤ c * (‖CJ‖ * M₁) := by
    intro t x
    rw [Real.norm_eq_abs]
    refine (hξb x _).trans ((hcle _).trans (mul_le_mul_of_nonneg_left ?_ hc.le))
    rw [hγc]
    exact (CJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₁ _) (norm_nonneg _))
  have hβb : ∀ s x, ‖ξ x ((β s : DifferentialForm (Euclid N) k) x)‖ ≤ c * (‖CJ‖ * M₀) := by
    intro s x
    rw [Real.norm_eq_abs]
    refine (hξb x _).trans ((hcle _).trans (mul_le_mul_of_nonneg_left ?_ hc.le))
    rw [hβc]
    exact (CJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM₀ _) (norm_nonneg _))
  -- Step 6: measurability and integrability on `(0, 1] × ℝᴺ` and on `ℝᴺ`.
  have hev : Continuous
      (Function.uncurry fun (α : Covector (Euclid N) k) (L : MultiVector N k) => L α) :=
    continuous_snd.clm_apply continuous_fst
  have hβint : ∀ s, Integrable (fun x => ξ x ((β s : DifferentialForm (Euclid N) k) x)) μ := by
    intro s
    refine Integrable.of_bound ?_ (c * (‖CJ‖ * M₀)) (Eventually.of_forall fun x => hβb s x)
    exact hev.comp_aestronglyMeasurable₂ (hβcont s).aestronglyMeasurable hξm
  have hint : Integrable (Function.uncurry fun (t : ℝ) (x : Euclid N) =>
      ξ x ((γ t : DifferentialForm (Euclid N) k) x)) ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
    refine Integrable.of_bound ?_ (c * (‖CJ‖ * M₁)) (Eventually.of_forall fun p => hγb p.1 p.2)
    exact hev.comp_aestronglyMeasurable₂ hγcont.aestronglyMeasurable hξm.comp_snd
  -- Step 7: (REP), Fubini, the fundamental theorem of calculus for each `x`, and (REP) again.
  have hftc : ∀ x, ∫ t in (0 : ℝ)..1, ξ x ((γ t : DifferentialForm (Euclid N) k) x) =
      ξ x ((β 1 : DifferentialForm (Euclid N) k) x) -
        ξ x ((β 0 : DifferentialForm (Euclid N) k) x) := by
    intro x
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv x t) ?_
    exact ((ξ x).continuous.comp
      (hγcont.comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  calc ∫ t in (0 : ℝ)..1, X (γ t)
      = ∫ t in (0 : ℝ)..1, ∫ x, ξ x ((γ t : DifferentialForm (Euclid N) k) x) ∂μ := by
        congr 1
        funext t
        exact hrep (γ t)
    _ = ∫ x, (∫ t in (0 : ℝ)..1, ξ x ((γ t : DifferentialForm (Euclid N) k) x)) ∂μ := by
        simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
        exact integral_integral_swap hint
    _ = X (β 1) - X (β 0) := by
        simp_rw [hftc]
        rw [integral_sub (hβint 1) (hβint 0), ← hrep, ← hrep]
/-- **The cylinder `[[(0, 1)]] × X`** (Simon Ch. 6, 2.17–2.21, the product current of the
homotopy formula 2.25).  Write `ι(t, x) = (t, x)`, `Jv = ι(0, v)`, and call `η : ℝ → 𝒟ᵏ(ℝᴺ)` a
slice family of `ω ∈ 𝒟ᵏ⁺¹(ℝᴺ⁺¹)` if `η_t(x)(v) = ω(ι(t, x))(e₀, Jv₁, …, Jvₖ)`.  Every `ω` has
a slice family `η^ω`, which is unique, and `|η_s(x) − η_t(x)| ≤ c|s − t|` makes `t ↦ X(η_t)`
`c M(X)`-Lipschitz (`dimred_mbl_dt_lpc_slice_forms`).  So `L(ω) = ∫₀¹ X(η^ω_t) dt` is linear,
and `|η^ω_t(x)| ≤ |ω(ι(t, x))|` gives `|L(ω)| ≤ c M(X)` when `|ω| ≤ c`: `L` is a current `Y`
with `M(Y) ≤ M(X)` (cf. 2.20).  If `spt X` is compact and `spt ω` misses the compact set
`E = ι([0, 1] × spt X)`, each slice `η^ω_t`, `t ∈ [0, 1]`, misses `spt X`, so `Y(ω) = 0`; hence
`spt Y ⊆ E` is compact. -/
theorem Submission.dimred_mbl_dt_lpc_cylinder_current : ((∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β) → (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ → ∃ Y : GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), Y.mass ≤ X.mass ∧ (IsCompact X.support → IsCompact Y.support ∧ Y.support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (η : ℝ → TestFormOn (univ : Set (Euclid N)) k), (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) → Continuous (fun t => X (η t)) ∧ Y ω = ∫ t in (0 : ℝ)..1, X (η t) := by
  intro hCB hVO N k X hX
  classical
  have hS := (Submission.dimred_mbl_dt_lpc_slice_forms hCB).1 N k
  have hXm : X.mass ≠ ∞ := hX.ne
  -- Step 1: a slice family `η^ω` of every `ω`; every slice family of `ω` equals `η^ω`
  choose ηf hηf using fun ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) => (hS ω).1
  have huniq : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (η : ℝ → TestFormOn (univ : Set (Euclid N)) k),
      (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (η t : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      η = ηf ω := by
    intro ω η hη
    funext t
    apply Subtype.ext
    funext x
    ext v
    rw [hη, hηf]
  -- Step 2: `|X(η_s) − X(η_t)| ≤ c M(X) |s − t|`, so `t ↦ X(η_t)` is continuous
  have hcont : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
      (η : ℝ → TestFormOn (univ : Set (Euclid N)) k),
      (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (η t : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) →
      Continuous (fun t => X (η t)) := by
    intro ω η hη
    obtain ⟨c, hc0, hc⟩ := (hS ω).2
    obtain ⟨-, hlip, -⟩ := hc η hη
    have hM : 0 ≤ X.mass.toReal := ENNReal.toReal_nonneg
    have hL : ∀ s t, dist (X (η s)) (X (η t)) ≤ (c * X.mass.toReal) * dist s t := by
      intro s t
      rw [Real.dist_eq, Real.dist_eq]
      have hsub : X (η s) - X (η t) = X (η s - η t) := (map_sub X.toCurrent _ _).symm
      rw [hsub]
      -- (a)–(b): `|(η_s − η_t)(x)| ≤ c|s − t| + ε`, so `|X(η_s − η_t)| ≤ (c|s − t| + ε) M(X)`
      have hε : ∀ ε > 0, |X (η s - η t)| ≤ (c * |s - t| + ε) * X.mass.toReal := by
        intro ε hε
        apply Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (η s - η t) (c * |s - t| + ε)
          (by positivity) hXm
        intro x
        simp only [Submodule.coe_sub, Pi.sub_apply]
        linarith [hlip s t x]
      -- (c): let `ε ↓ 0`
      refine le_of_forall_pos_le_add (fun δ hδ => ?_)
      have h := hε (δ / (X.mass.toReal + 1)) (by positivity)
      have h2 : (δ / (X.mass.toReal + 1)) * X.mass.toReal ≤ δ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      nlinarith
    have hL' : LipschitzWith (Real.toNNReal (c * X.mass.toReal)) (fun t => X (η t)) := by
      refine LipschitzWith.of_dist_le_mul (fun s t => ?_)
      rw [Real.coe_toNNReal _ (by positivity)]
      exact hL s t
    exact hL'.continuous
  -- Step 3: `L(ω) = ∫₀¹ X(η^ω_t) dt` is linear: by Step 1, `η^{ω₁ + ω₂} = η^{ω₁} + η^{ω₂}` and
  -- `η^{aω} = a η^ω`, and the integrands are continuous by Step 2
  let L : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1) →ₗ[ℝ] ℝ :=
    { toFun := fun ω => ∫ t in (0 : ℝ)..1, X (ηf ω t)
      map_add' := by
        intro ω₁ ω₂
        have h : ηf (ω₁ + ω₂) = fun t => ηf ω₁ t + ηf ω₂ t := by
          refine (huniq (ω₁ + ω₂) (fun t => ηf ω₁ t + ηf ω₂ t) ?_).symm
          intro t x v
          simp only [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply]
          rw [hηf ω₁, hηf ω₂]
        simp only [h, map_add]
        exact intervalIntegral.integral_add ((hcont ω₁ _ (hηf ω₁)).intervalIntegrable 0 1)
          ((hcont ω₂ _ (hηf ω₂)).intervalIntegrable 0 1)
      map_smul' := by
        intro a ω
        have h : ηf (a • ω) = fun t => a • ηf ω t := by
          refine (huniq (a • ω) (fun t => a • ηf ω t) ?_).symm
          intro t x v
          simp only [Submodule.coe_smul, Pi.smul_apply, ContinuousAlternatingMap.smul_apply]
          rw [hηf ω]
        simp only [h, map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_const_mul a _ }
  have hLω : ∀ ω, L ω = ∫ t in (0 : ℝ)..1, X (ηf ω t) := fun ω => rfl
  -- Step 4: if `|ω| ≤ c`, then `|η^ω_t(x)| ≤ |ω(ι(t, x))| ≤ c`, so `|X(η^ω_t)| ≤ c M(X)` and
  -- `|L(ω)| ≤ c M(X)`
  have hbound : ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1)) (c : ℝ), 0 < c →
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) (k + 1)) y) ≤ c) →
      |L ω| ≤ c * X.mass.toReal := by
    intro ω c hc hω
    obtain ⟨c', -, hc'⟩ := (hS ω).2
    obtain ⟨hpt, -, -⟩ := hc' (ηf ω) (hηf ω)
    have h1 : ∀ t, ‖X (ηf ω t)‖ ≤ c * X.mass.toReal := fun t => by
      rw [Real.norm_eq_abs]
      exact Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (ηf ω t) c hc hXm
        (fun x => (hpt t x).trans (hω _))
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (fun t _ => h1 t)
    rw [hLω, ← Real.norm_eq_abs]
    simpa using h2
  -- Step 5: `L` is a current `Y`; with Steps 1–2 this is (c)
  obtain ⟨Y, hY⟩ := Submission.cmc_fc_sc_current_of_coeff_bound (N + 1) (k + 1) univ L
    X.mass.toReal (fun ω c hc hω => hbound ω c hc hω)
  refine ⟨Y, ?_, ?_, fun ω η hη => ⟨hcont ω η hη, ?_⟩⟩
  · -- Step 6, (a): an admissible `ω` has `|ω| ≤ 1`, so `Y(ω) = L(ω) ≤ M(X)`
    show Y.massOn univ ≤ X.mass
    unfold GeometricCurrentOn.massOn
    apply sSup_le
    rintro _ ⟨ω, hω, rfl⟩
    have h := hbound ω 1 one_pos hω.2
    show ENNReal.ofReal (Y ω) ≤ X.mass
    rw [hY ω]
    calc ENNReal.ofReal (L ω) ≤ ENNReal.ofReal (X.mass.toReal) :=
          ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (L ω)])
      _ = X.mass := ENNReal.ofReal_toReal hXm
  · -- Step 7, (b): `Y` vanishes on forms missing the compact set `E = ι([0, 1] × spt X)`
    intro hXc
    -- (a) `E` is the continuous image of the compact set `[0, 1] × spt X`
    have hE : {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} =
        (fun p : ℝ × Euclid N => (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) :
          Euclid (N + 1))) '' (Icc (0 : ℝ) 1 ×ˢ X.support) := by
      ext y
      simp only [mem_ofPred_eq, mem_image, mem_prod, Prod.exists]
      constructor
      · rintro ⟨t, ht, x, hx, rfl⟩
        exact ⟨t, x, ⟨ht, hx⟩, rfl⟩
      · rintro ⟨t, x, ⟨ht, hx⟩, rfl⟩
        exact ⟨t, ht, x, hx, rfl⟩
    have hιc : Continuous (fun p : ℝ × Euclid N =>
        (WithLp.toLp 2 (Fin.cons p.1 (WithLp.ofLp p.2)) : Euclid (N + 1))) := by
      refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using continuous_fst
      · simp only [Fin.cons_succ]
        exact (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd)
    have hEc : IsCompact {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
        y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} := by
      rw [hE]
      exact (isCompact_Icc.prod hXc).image hιc
    -- (b)–(d) if `spt ω ∩ E = ∅`, every slice `η^ω_t`, `t ∈ [0, 1]`, misses `spt X`, so
    -- `X(η^ω_t) = 0` and `Y(ω) = 0`
    have hvan : ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1),
        Disjoint (tsupport (ω : DifferentialForm (Euclid (N + 1)) (k + 1)))
          {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support,
            y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))} →
        Y ω = 0 := by
      intro ω hω
      rw [hY ω, hLω]
      obtain ⟨c, -, hc⟩ := (hS ω).2
      obtain ⟨-, -, hsup⟩ := hc (ηf ω) (hηf ω)
      have h0 : ∀ t ∈ uIcc (0 : ℝ) 1, X (ηf ω t) = 0 := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        apply hVO N k univ X (ηf ω t)
        rw [Set.disjoint_left]
        intro x hx hxX
        exact Set.disjoint_left.1 hω (hsup t hx) ⟨t, ht, x, hxX, rfl⟩
      rw [intervalIntegral.integral_congr h0]
      simp
    -- (e) hence `spt Y ⊆ E` and `spt Y` is compact
    obtain ⟨h1, h2⟩ := Submission.rsd_cmr_support_subset_of_vanish (N + 1) (k + 1) univ _ Y
      isOpen_univ hEc (subset_univ _) hvan
    exact ⟨h2, h1⟩
  · rw [hY ω, hLω, huniq ω η hη]
/-- **Basis independence of `Σ_j α(b ∘ j)²`** (Simon 6.1): for an `n`-covector `α` on `ℝᴾ` and
orthonormal bases `b`, `b'` of `ℝᴾ`, `Σ_{j : Fin n → Fin P} α(b_{j 0}, …, b_{j (n-1)})²` is the same
for `b` and `b'`.  Expand `bᵢ = Σₛ ⟨b'ₛ, bᵢ⟩ b'ₛ` in every slot (multilinearity), square and sum
over `j`; the `j`-sum factors over the slots, and `Σᵢ ⟨b'ₛ, bᵢ⟩⟨bᵢ, b'ₜ⟩ = ⟨b'ₛ, b'ₜ⟩ = δₛₜ`
(Parseval for `b`) kills every cross term. -/
theorem Submission.regcomp_covector_sq_sum_basis_invariant : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (b b' : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2 = ∑ j : Fin n → Fin P, (α (fun k => b' (j k))) ^ 2 := by
  intro P n α b b'
  classical
  -- `c i s = ⟨b'ₛ, bᵢ⟩`, the coordinates of `bᵢ` in `b'`
  set c : Fin P → Fin P → ℝ := fun i s => inner ℝ (b' s) (b i) with hc
  -- multilinearity: `α(b ∘ j) = Σ_a (Πₖ c(j k, a k)) α(b' ∘ a)`
  have hexp : ∀ j : Fin n → Fin P, α (fun k => b (j k)) =
      ∑ a : Fin n → Fin P, (∏ k, c (j k) (a k)) * α (fun k => b' (a k)) := by
    intro j
    have hb : (fun k => b (j k)) = fun k => ∑ s, c (j k) s • b' s :=
      funext fun k => (b'.sum_repr' (b (j k))).symm
    rw [hb, α.map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_eq_mul, ← α.map_smul_univ]
  -- Parseval for `b` and orthonormality of `b'`: `Σᵢ c(i, s) c(i, t) = δₛₜ`
  have hdelta : ∀ s t : Fin P, ∑ i, c i s * c i t = if s = t then 1 else 0 := by
    intro s t
    have h1 : ∑ i, c i s * c i t = inner ℝ (b' s) (b' t) := by
      rw [← b.sum_inner_mul_inner (b' s) (b' t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc]
      rw [real_inner_comm (b' t) (b i)]
    rw [h1]
    exact (orthonormal_iff_ite.mp b'.orthonormal) s t
  -- `Σ_j Πₖ c(j k, a k) c(j k, a' k) = Πₖ Σᵢ c(i, a k) c(i, a' k) = δ_{a a'}`
  have hT : ∀ a a' : Fin n → Fin P,
      ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) = if a = a' then 1 else 0 := by
    intro a a'
    rw [← Fintype.prod_sum (fun k i => c i (a k) * c i (a' k))]
    simp_rw [hdelta]
    split_ifs with h
    · subst h
      simp
    · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right hk)
  calc ∑ j : Fin n → Fin P, (α (fun k => b (j k))) ^ 2
      = ∑ j : Fin n → Fin P, ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hexp j, sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
    _ = ∑ a : Fin n → Fin P, ∑ a' : Fin n → Fin P,
          (α (fun k => b' (a k)) * α (fun k => b' (a' k))) *
            ∑ j : Fin n → Fin P, ∏ k, (c (j k) (a k) * c (j k) (a' k)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a' _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ a : Fin n → Fin P, (α (fun k => b' (a k))) ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [hT]
        rw [Finset.sum_eq_single a]
        · simp [sq]
        · intro a' _ hne
          simp [Ne.symm hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
/-- **Simon 6.1.2, 6.1.5** (the Euclidean coefficient norm in the standard basis `e`):
`Σ_{j : Fin n → Fin P} α(e_{j(0)}, …, e_{j(n−1)})² = n! |α|_E²`.  Tuples `j` with a repeated
index contribute `0` (alternation), and `(I, σ) ↦ I ∘ σ` is a bijection from the strictly
increasing `I` and the permutations `σ` of `Fin n` onto the injective `j`, with
`α(e_{I ∘ σ}) = sgn σ · α(e_I)`. -/
theorem Submission.regcomp_covector_sq_sum_basisFun : ∀ (P n : ℕ) (α : Covector (Euclid P) n), ∑ j : Fin n → Fin P, (α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α
  classical
  -- `|α|_E² = Σ_I [I strictly increasing] α(e_I)²`, so `n! |α|_E² = Σ_{(I, σ)} α(e_I)²` over
  -- strictly increasing `I` and `σ ∈ Perm(Fin n)`
  unfold covectorEuclideanNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun I _ => by positivity), ← Finset.sum_filter,
    Finset.mul_sum]
  have hcard : ∀ x : ℝ, (n.factorial : ℝ) * x = ∑ _σ : Equiv.Perm (Fin n), x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  simp only [hcard]
  rw [← Finset.sum_product']
  -- alternation: non-injective `j` contribute `0`
  have hzero : ∀ j : Fin n → Fin P, ¬ Injective j →
      α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (j k)) = 0 := fun j hj =>
    α.map_eq_zero_of_not_injective _
      fun h => hj (Injective.of_comp (f := ⇑(EuclideanSpace.basisFun (Fin P) ℝ)) h)
  rw [← Finset.sum_filter_of_ne (p := Injective) fun j _ hne => by
    by_contra hj
    exact hne (by rw [hzero j hj]; norm_num)]
  symm
  -- `(I, σ) ↦ I ∘ σ` is a bijection onto the injective `j`, and `α(e_{I ∘ σ}) = sgn σ · α(e_I)`
  refine Finset.sum_bij (fun p _ => fun k => p.1 (p.2 k)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
    exact hp.injective.comp p.2.injective
  · -- equal ranges force `I = I'`, and then `σ = σ'` by injectivity of `I`
    intro p hp q hq hpq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp hq
    have hrange : Set.range p.1 = Set.range q.1 := by
      rw [← EquivLike.range_comp p.1 p.2, ← EquivLike.range_comp q.1 q.2]
      exact congrArg Set.range hpq
    have hI : p.1 = q.1 := (StrictMono.range_inj_of_wellFoundedLT hp hq).mp hrange
    have hσ : p.2 = q.2 := by
      ext k
      have := congr_fun hpq k
      rw [hI] at this
      exact congrArg Fin.val (hq.injective this)
    exact Prod.ext hI hσ
  · -- `j ∘ Tuple.sort j` is monotone and injective, hence strictly increasing
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨(j ∘ Tuple.sort j, (Tuple.sort j)⁻¹), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
      exact (Tuple.monotone_sort j).strictMono_of_injective (hj.comp (Tuple.sort j).injective)
    · funext k
      simp
  · intro p _
    have hperm : α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 (p.2 k))) =
        Equiv.Perm.sign p.2 • α (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) :=
      α.toAlternatingMap.map_perm (fun k => EuclideanSpace.basisFun (Fin P) ℝ (p.1 k)) p.2
    dsimp only
    rw [hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p.2) with h | h <;> simp [h]

/-- **Simon 6.1.2, 6.1.5** in an arbitrary orthonormal basis (the coefficient norm behind
Remark 6.3.2(3)): for an `n`-covector `α` on `ℝᴾ` and an orthonormal basis `f` of `ℝᴾ`,
`Σ_{j : Fin n → Fin P} α(f_{j(0)}, …, f_{j(n−1)})² = n! |α|_E²`.  The sum is the same for every
orthonormal basis (`regcomp_covector_sq_sum_basis_invariant` with `b' = e`, the standard basis),
and for `e` it is `n! |α|_E²` (`regcomp_covector_sq_sum_basisFun`). -/
theorem Submission.regcomp_covector_sq_sum_orthonormalBasis : ∀ (P n : ℕ) (α : Covector (Euclid P) n) (f : OrthonormalBasis (Fin P) ℝ (Euclid P)), ∑ j : Fin n → Fin P, (α (fun k => f (j k))) ^ 2 = (n.factorial : ℝ) * covectorEuclideanNorm α ^ 2 := by
  intro P n α f
  rw [Submission.regcomp_covector_sq_sum_basis_invariant P n α f
    (EuclideanSpace.basisFun (Fin P) ℝ)]
  exact Submission.regcomp_covector_sq_sum_basisFun P n α

/-- **Simon 6.1.8** (the pull-back estimate behind the mass bound of Lemma 6.2.29): for a linear
map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`, the pull-back `A^#β = β(A ·, …, A ·)` satisfies
`|A^#β|_E ≤ ‖A‖ᵏ |β|_E`.  With the standard bases `e`, `e'` and `S_b(γ) = Σ_j γ(b ∘ j)²` over all
`j : Fin m → Fin P`, induction on the degree `m` gives `S_e(A^#γ) ≤ ‖A‖^{2m} S_{e'}(γ)`: split
`j = Fin.cons a j'`, use `ι_x(A^#γ) = A^#(ι_{Ax}γ)` (`ι_x = curryLeft x`) and the induction
hypothesis for `ι_{Ae_a}γ`, then the one-slot estimate
`Σ_a μ(Ae_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²` (Parseval for functionals) for
`μ(u) = (ι_u γ)(e' ∘ j')`.  Finally `S_e(A^#β) = k! |A^#β|_E²` and `S_{e'}(β) = k! |β|_E²`
(`regcomp_covector_sq_sum_orthonormalBasis`). -/
theorem Submission.dimred_mbl_dt_lp_cb_pullback_le : ∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β := by
  intro N N' k A β
  -- Parseval for functionals: `Σ_a μ(b_a)² = ‖g‖² = ‖μ‖²` for the Riesz vector `g` of `μ`
  have hpars : ∀ (M : ℕ) (b : OrthonormalBasis (Fin M) ℝ (Euclid M)) (μ : Euclid M →L[ℝ] ℝ),
      ∑ a, (μ (b a)) ^ 2 = ‖μ‖ ^ 2 := by
    intro M b μ
    obtain ⟨g, hg, hgn⟩ : ∃ g : Euclid M, (∀ x, μ x = inner ℝ g x) ∧ ‖g‖ = ‖μ‖ :=
      ⟨(InnerProductSpace.toDual ℝ (Euclid M)).symm μ,
        fun x => InnerProductSpace.toDual_symm_apply.symm,
        (InnerProductSpace.toDual ℝ (Euclid M)).symm.norm_map μ⟩
    rw [← hgn, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner g g]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hg, sq, real_inner_comm g (b a)]
  -- the standard orthonormal bases `e` of `ℝᴺ` and `e'` of `ℝᴺ'`
  have e : OrthonormalBasis (Fin N) ℝ (Euclid N) := EuclideanSpace.basisFun (Fin N) ℝ
  have e' : OrthonormalBasis (Fin N') ℝ (Euclid N') := EuclideanSpace.basisFun (Fin N') ℝ
  -- one-slot estimate: `Σ_a μ(Ae_a)² = ‖μ ∘ A‖² ≤ ‖A‖² ‖μ‖² = ‖A‖² Σ_b μ(e'_b)²`
  have hone : ∀ μ : Euclid N' →L[ℝ] ℝ,
      ∑ a, (μ (A (e a))) ^ 2 ≤ ‖A‖ ^ 2 * ∑ b, (μ (e' b)) ^ 2 := fun μ =>
    calc ∑ a, (μ (A (e a))) ^ 2 = ‖μ.comp A‖ ^ 2 := hpars N e (μ.comp A)
      _ ≤ (‖μ‖ * ‖A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (μ.opNorm_comp_le A) 2
      _ = ‖A‖ ^ 2 * ∑ b, (μ (e' b)) ^ 2 := by rw [hpars N' e' μ]; ring
  -- first-slot splitting `J = Fin.cons a j` of the index tuples
  have hcons : ∀ (M m : ℕ) (F : (Fin (m + 1) → Fin M) → ℝ),
      ∑ J : Fin (m + 1) → Fin M, F J = ∑ a : Fin M, ∑ j : Fin m → Fin M, F (Fin.cons a j) := by
    intro M m F
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin M) _ _ fun _ => rfl).symm
  -- `γ(b ∘ Fin.cons a j) = (ι_{b_a} γ)(b ∘ j)` for the interior product `ι_x = curryLeft x`
  have hcurry : ∀ (M m : ℕ) (γ : Covector (Euclid M) (m + 1)) (b : Fin M → Euclid M) (a : Fin M)
      (j : Fin m → Fin M),
      γ (fun i => b ((Fin.cons a j : Fin (m + 1) → Fin M) i)) =
        γ.curryLeft (b a) (fun i => b (j i)) := by
    intro M m γ b a j
    rw [ContinuousAlternatingMap.curryLeft_apply_apply]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp
  -- `S_e(A^#γ) ≤ ‖A‖^{2m} S_{e'}(γ)` for every `m`-covector `γ`, by induction on `m`
  have hHS : ∀ (m : ℕ) (γ : Covector (Euclid N') m),
      ∑ j : Fin m → Fin N, (γ.compContinuousLinearMap A (fun i => e (j i))) ^ 2 ≤
        (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N', (γ (fun i => e' (j i))) ^ 2 := by
    intro m
    induction m with
    | zero =>
      -- both sums consist of the single term `γ(∅)²`
      intro γ
      rw [pow_zero, one_mul, Fintype.sum_unique, Fintype.sum_unique,
        ContinuousAlternatingMap.compContinuousLinearMap_apply]
      exact le_of_eq (congrArg (· ^ 2) (congrArg γ (Subsingleton.elim _ _)))
    | succ m ih =>
      intro γ
      calc ∑ j : Fin (m + 1) → Fin N, (γ.compContinuousLinearMap A (fun i => e (j i))) ^ 2
          = ∑ a, ∑ j : Fin m → Fin N,
              ((γ.curryLeft (A (e a))).compContinuousLinearMap A (fun i => e (j i))) ^ 2 := by
            rw [hcons]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hcurry, ContinuousAlternatingMap.curryLeft_compContinuousLinearMap]
        _ ≤ ∑ a, (‖A‖ ^ 2) ^ m *
              ∑ j : Fin m → Fin N', (γ.curryLeft (A (e a)) (fun i => e' (j i))) ^ 2 :=
            Finset.sum_le_sum fun a _ => ih _
        _ = (‖A‖ ^ 2) ^ m *
              ∑ j : Fin m → Fin N', ∑ a, (γ.curryLeft (A (e a)) (fun i => e' (j i))) ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
        _ ≤ (‖A‖ ^ 2) ^ m * ∑ j : Fin m → Fin N',
              ‖A‖ ^ 2 * ∑ b, (γ.curryLeft (e' b) (fun i => e' (j i))) ^ 2 := by
            -- the one-slot estimate for `μ(u) = (ι_u γ)(e' ∘ j)`
            gcongr with j
            exact hone ((ContinuousAlternatingMap.apply ℝ (Euclid N') ℝ
              (fun i => e' (j i))).comp γ.curryLeft)
        _ = (‖A‖ ^ 2) ^ (m + 1) * ∑ j : Fin (m + 1) → Fin N', (γ (fun i => e' (j i))) ^ 2 := by
            rw [hcons, Finset.sum_comm, ← Finset.mul_sum, ← mul_assoc, ← pow_succ]
            congr 1
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
            rw [hcurry]
  -- `k! |A^#β|_E² = S_e(A^#β) ≤ ‖A‖^{2k} S_{e'}(β) = ‖A‖^{2k} k! |β|_E²`; cancel `k!`
  have h := hHS k β
  rw [Submission.regcomp_covector_sq_sum_orthonormalBasis N k _ e,
    Submission.regcomp_covector_sq_sum_orthonormalBasis N' k β e',
    mul_left_comm ((‖A‖ ^ 2) ^ k)] at h
  have hsq : covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2 ≤
      (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 :=
    calc covectorEuclideanNorm (β.compContinuousLinearMap A) ^ 2
        ≤ (‖A‖ ^ 2) ^ k * covectorEuclideanNorm β ^ 2 :=
          le_of_mul_le_mul_left h (by exact_mod_cast Nat.factorial_pos k)
      _ = (‖A‖ ^ k * covectorEuclideanNorm β) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _)
    (mul_nonneg (pow_nonneg (norm_nonneg A) k) (covectorEuclideanNorm_nonneg β)) two_ne_zero).mp hsq
/-- **Interior product bound for the Euclidean coefficient norm** (Simon 6.1): for `v ∈ ℝᴺ` and a
`(k+1)`-covector `β` on `ℝᴺ`, the interior product `ι_v β = β.curryLeft v`,
`ι_v β(w₁, …, w_k) = β(v, w₁, …, w_k)`, satisfies `|ι_v β|_E ≤ ‖v‖ |β|_E`.  By homogeneity it
suffices to treat `u = v / ‖v‖ = f_{i₀}` for an orthonormal basis `f` of `ℝᴺ`.  The position sums
`R_p = Σ_{J(p) = i₀} β(f ∘ J)²` all equal `R_0 = k! |ι_u β|_E²` (transpose `0 ↔ p`), and
`Σ_p R_p ≤ Σ_J β(f ∘ J)² = (k+1)! |β|_E²` because tuples with `i₀` in two slots vanish
(`regcomp_covector_sq_sum_orthonormalBasis` evaluates both sums). -/
theorem Submission.dimred_mbl_dt_lp_cb_curryLeft_le : ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  intro N k v β
  classical
  -- the case `v = 0`
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  -- homogeneity: `|c γ|_E = |c| |γ|_E`
  have hhom : ∀ (c : ℝ) (γ : Covector (Euclid N) k),
      covectorEuclideanNorm (c • γ) = |c| * covectorEuclideanNorm γ := by
    intro c γ
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg c), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, mul_pow]
    · rw [mul_zero]
  -- `N ≥ 1` as `ℝ⁰ = {0}`; an orthonormal basis `f` of `ℝᴺ` with `f i₀ = ‖v‖⁻¹ v`
  have hN : 0 < N := Nat.pos_of_ne_zero fun h => hv (by subst h; exact Subsingleton.elim v 0)
  set i₀ : Fin N := ⟨0, hN⟩
  obtain ⟨f, hf⟩ : ∃ f : OrthonormalBasis (Fin N) ℝ (Euclid N), f i₀ = ‖v‖⁻¹ • v := by
    have hon : Orthonormal ℝ (({i₀} : Set (Fin N)).domRestrict fun _ => ‖v‖⁻¹ • v) := by
      refine ⟨fun _ => ?_, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
      rw [Set.domRestrict_apply, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
    exact ⟨b, hb i₀ rfl⟩
  -- `|ι_v β|_E = ‖v‖ |ι_{f i₀} β|_E`, so it suffices to show `|ι_{f i₀} β|_E ≤ |β|_E`
  have hvu : β.curryLeft v = ‖v‖ • β.curryLeft (f i₀) := by
    rw [hf, map_smul, smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  rw [hvu, hhom, abs_of_pos hvpos]
  refine mul_le_mul_of_nonneg_left ?_ hvpos.le
  -- `g J = β(f ∘ J)²` and the position sums `R p = Σ_{J p = i₀} g J`
  set g : (Fin (k + 1) → Fin N) → ℝ := fun J => (β fun t => f (J t)) ^ 2 with hg
  set R : Fin (k + 1) → ℝ := fun p => ∑ J, if J p = i₀ then g J else 0 with hR
  -- `R 0 = Σ_j (ι_{f i₀} β)(f ∘ j)² = k! |ι_{f i₀} β|_E²` (reindex `J = Fin.cons a j`)
  have hR0 : R 0 = (k.factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 := by
    rw [← Submission.regcomp_covector_sq_sum_orthonormalBasis N k (β.curryLeft (f i₀)) f]
    simp only [hR]
    rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin N).sum_comp, Fintype.sum_prod_type,
      Finset.sum_eq_single i₀]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.consEquiv_apply, Fin.cons_zero, ↓reduceIte, hg]
      rw [ContinuousAlternatingMap.curryLeft_apply_apply]
      congr 2
      funext t
      refine Fin.cases ?_ (fun s => ?_) t <;> simp
    · intro a _ ha
      exact Finset.sum_eq_zero fun j _ => by simp [ha]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  -- `R p = R 0`: reindex `J ↦ J ∘ (0 p)`, and `β(f ∘ J ∘ (0 p)) = ±β(f ∘ J)`
  have hRp : ∀ p, R p = R 0 := by
    intro p
    simp only [hR]
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N))) _ _
      fun J => ?_
    have hJ : ∀ t, Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J t =
        J (Equiv.swap 0 p t) := fun t => by
      simp [Equiv.arrowCongr_apply]
    have hperm : β (fun t => f (J (Equiv.swap 0 p t))) =
        Equiv.Perm.sign (Equiv.swap 0 p) • β (fun t => f (J t)) :=
      β.toAlternatingMap.map_perm (fun t => f (J t)) (Equiv.swap 0 p)
    have hgJ : g (Equiv.arrowCongr (Equiv.swap 0 p) (Equiv.refl (Fin N)) J) = g J := by
      simp only [hg, hJ, hperm]
      rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (k + 1)) p)) with h | h <;>
        simp [h]
    rw [hgJ, hJ, Equiv.swap_apply_left]
  -- `Σ_p R p ≤ Σ_J g J`: a tuple `J` with `i₀` in two slots has `β(f ∘ J) = 0`
  have hsum : ∑ p, R p ≤ ∑ J, g J := by
    simp only [hR]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun J _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    by_cases h : (Finset.univ.filter fun p => J p = i₀).card ≤ 1
    · exact mul_le_of_le_one_left (sq_nonneg _) (by exact_mod_cast h)
    · obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (not_le.mp h)
      rw [Finset.mem_filter] at hp hq
      have h0 : β (fun t => f (J t)) = 0 :=
        β.map_eq_zero_of_eq _ (by rw [hp.2, hq.2]) hpq
      simp [hg, h0]
  -- `(k+1)! |ι_{f i₀} β|_E² = Σ_p R p ≤ Σ_J g J = (k+1)! |β|_E²`
  have key : ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2 ≤
      ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 :=
    calc ((k + 1).factorial : ℝ) * covectorEuclideanNorm (β.curryLeft (f i₀)) ^ 2
        = ∑ p, R p := by
          rw [Finset.sum_congr rfl fun p _ => hRp p, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, hR0, Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ∑ J, g J := hsum
      _ = ((k + 1).factorial : ℝ) * covectorEuclideanNorm β ^ 2 := by
          simp only [hg]
          exact Submission.regcomp_covector_sq_sum_orthonormalBasis N (k + 1) β f
  exact (pow_le_pow_iff_left₀ (covectorEuclideanNorm_nonneg _) (covectorEuclideanNorm_nonneg _)
    two_ne_zero).mp (le_of_mul_le_mul_left key (by exact_mod_cast Nat.factorial_pos _))

/-- **Covector bounds for the Lipschitz push-forward** (Simon 6.1, (L1)–(L2)): the pull-back
estimate `|A^#β|_E ≤ ‖A‖ᵏ |β|_E` for a linear map `A : ℝᴺ → ℝᴺ'` and a `k`-covector `β` on `ℝᴺ'`
(Simon 6.1.8, `dimred_mbl_dt_lp_cb_pullback_le`), and the interior product estimate
`|ι_v β|_E ≤ ‖v‖ |β|_E` for `v ∈ ℝᴺ` and a `(k+1)`-covector `β` on `ℝᴺ`
(`dimred_mbl_dt_lp_cb_curryLeft_le`). -/
theorem Submission.dimred_mbl_dt_lp_covector_bounds : (∀ (N N' k : ℕ) (A : Euclid N →L[ℝ] Euclid N') (β : Covector (Euclid N') k), covectorEuclideanNorm (β.compContinuousLinearMap A) ≤ ‖A‖ ^ k * covectorEuclideanNorm β) ∧ ∀ (N k : ℕ) (v : Euclid N) (β : Covector (Euclid N) (k + 1)), covectorEuclideanNorm (β.curryLeft v) ≤ ‖v‖ * covectorEuclideanNorm β := by
  exact ⟨Submission.dimred_mbl_dt_lp_cb_pullback_le, Submission.dimred_mbl_dt_lp_cb_curryLeft_le⟩
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

/-- **The cylinder operator `X ↦ [[(0, 1)]] × X`** (Simon Ch. 6, 2.17–2.22, in the `t`-integral
form of the homotopy formula 2.25; the product used for the Lipschitz push-forward in the
deformation theorem).  Write `ι(t, x) = (t, x)`, `e₀ = (1, 0, …, 0)` and `Jv = ι(0, v)`.  For
`M(X) < ∞`, `cyl(X)(ω) = ∫₀¹ X(η^ω_t) dt` with `η^ω_t(x)(v) = ω(ι(t, x))(e₀, Jv)` is a current
with `M(cyl X) ≤ M(X)` and, for compact `spt X`, compact support in `ι([0, 1] × spt X)`
(`Submission.dimred_mbl_dt_lpc_cylinder_current`); this gives (C3), and (C2) follows from
`M(X − Y) ≤ M(X) + M(Y)`.  The coordinate formula for `d` gives `η^{dω}_t = ∂_tβ^ω_t − d(η^ω_t)`
for `β^ω_s(x) = ω(ι(s, x)) ∘ J`, and Fubini with the fundamental theorem of calculus gives
`∫₀¹ X(∂_tβ^ω_t) dt = X(β^ω_1) − X(β^ω_0)`.  Hence (C4), (C5) and, for `|ω| ≤ 1`,
`∂cyl(X)(ω) ≤ 2M(X) + M(∂X)`, so `M(∂cyl X) < ∞`. -/
theorem Submission.dimred_mbl_dt_lp_cylinder : (∀ (P n : ℕ) (U : Set (Euclid P)) (S : GeometricCurrentOn U n) (ω : TestFormOn U n), Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) S.support → S ω = 0) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → T.massOn W < ∞) → ∃ (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), μ Uᶜ = 0 ∧ (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) ∧ (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) ∧ AEStronglyMeasurable ξ μ ∧ (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) ∧ (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) ∧ ((∀ W : Set (Euclid P), IsOpen W → CompactlyContained W U → boundaryMassOn T W < ∞) → ∀ E : Set (Euclid P), μHE[n] E = 0 → μ E = 0)) → ∃ cyl : ∀ (N k : ℕ), GeometricCurrentOn (univ : Set (Euclid N)) k → GeometricCurrentOn (univ : Set (Euclid (N + 1))) (k + 1), (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact (cyl N k X).support ∧ (cyl N k X).mass ≤ X.mass ∧ (cyl N k X).boundary.mass < ∞ ∧ (cyl N k X).support ⊆ {y : Euclid (N + 1) | ∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ X.support, y = WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))}) ∧ (∀ (N k : ℕ) (X Y : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → IsCompact Y.support → Y.mass < ∞ → boundaryMassOn Y univ < ∞ → cyl N k (X - Y) = cyl N k X - cyl N k Y) ∧ (∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), IsCompact X.support → X.mass < ∞ → boundaryMassOn X univ < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η : ℝ → TestFormOn (univ : Set (Euclid N)) k, (∀ (t : ℝ) (x : Euclid N) (v : Fin k → Euclid N), (η t : DifferentialForm (Euclid N) k) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x))) (Fin.cons (EuclideanSpace.single 0 1) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i)))))) ∧ cyl N k X ω = ∫ t in (0 : ℝ)..1, X (η t)) ∧ (∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), IsCompact X.support → X.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) 0, ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) 0, (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₀ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin 0 → Euclid N), (η₁ : DifferentialForm (Euclid N) 0) x v = (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N 0 X).boundary ω = X η₁ - X η₀) ∧ ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), IsCompact X.support → X.mass < ∞ → X.boundary.mass < ∞ → ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1), ∃ η₀ η₁ : TestFormOn (univ : Set (Euclid N)) (k + 1), (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₀ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (∀ (x : Euclid N) (v : Fin (k + 1) → Euclid N), (η₁ : DifferentialForm (Euclid N) (k + 1)) x v = (ω : DifferentialForm (Euclid (N + 1)) (k + 1)) (WithLp.toLp 2 (Fin.cons 1 (WithLp.ofLp x))) (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) ∧ (cyl N (k + 1) X).boundary ω = X η₁ - X η₀ - cyl N k X.boundary ω := by
  intro hVO hREP
  have hCB := Submission.dimred_mbl_dt_lp_covector_bounds
  classical
  -- Step 1: slice families `η^ω_t`, restriction families `β^ω_s` and their `t`-derivatives
  -- `∂_tβ^ω_t`, with `|β^ω_s(x)| ≤ |ω(ι(s, x))|` (0(e))
  have hS := Submission.dimred_mbl_dt_lpc_slice_forms hCB
  -- Steps 2 and 4: for `M(X) < ∞`, `cyl(X)(ω) = ∫₀¹ X(η^ω_t) dt` is a current with
  -- `M(cyl X) ≤ M(X)`; if `spt X` is compact, `spt cyl(X)` is a compact subset of
  -- `ι([0, 1] × spt X)`
  choose! cyl hmass hsupp hint using Submission.dimred_mbl_dt_lpc_cylinder_current hCB hVO
  -- 0(b): `|X(β^ω_s)| ≤ M(X)` when `|ω| ≤ 1`
  have hβbd : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) k), X.mass < ∞ →
      ∀ ω : TestFormOn (univ : Set (Euclid (N + 1))) k,
      (∀ y, covectorEuclideanNorm ((ω : DifferentialForm (Euclid (N + 1)) k) y) ≤ 1) →
      ∀ β : ℝ → TestFormOn (univ : Set (Euclid N)) k,
      (∀ (s : ℝ) (x : Euclid N) (v : Fin k → Euclid N),
        (β s : DifferentialForm (Euclid N) k) x v =
          (ω : DifferentialForm (Euclid (N + 1)) k) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      ∀ s, |X (β s)| ≤ X.mass.toReal := by
    intro N k X hX ω hω β hβ s
    have h := Submission.cmc_fc_sc_abs_le_mul_mass N k univ X (β s) 1 one_pos hX.ne
      fun x => ((hS.2 N k ω).2.2 β hβ s x).trans (hω _)
    rwa [one_mul] at h
  -- Step 5, degree `0`: `η^{dω}_t = ∂_tβ^ω_t`, so by Fubini and the fundamental theorem of
  -- calculus `∂cyl(X)(ω) = cyl(X)(dω) = ∫₀¹ X(∂_tβ^ω_t) dt = X(β^ω_1) − X(β^ω_0)`
  have hB₀ : ∀ (N : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) 0), X.mass < ∞ →
      ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) 0)
        (β : ℝ → TestFormOn (univ : Set (Euclid N)) 0),
      (∀ (s : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N),
        (β s : DifferentialForm (Euclid N) 0) x v =
          (ω : DifferentialForm (Euclid (N + 1)) 0) (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (cyl N 0 X).boundary ω = X (β 1) - X (β 0) := by
    intro N X hX ω β hβ
    obtain ⟨-, ⟨γ, hγ⟩, -⟩ := hS.2 N 0 ω
    have hγd : ∀ (t : ℝ) (x : Euclid N) (v : Fin 0 → Euclid N),
        (γ t : DifferentialForm (Euclid N) 0) x v =
          (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) 0 ω :
            DifferentialForm (Euclid (N + 1)) (0 + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
      intro t x v
      rw [hγ t x v]
      exact (Submission.dimred_mbl_dt_lpc_slice_extDeriv.2 N ω t x v).symm
    rw [GeometricCurrentOn.boundary_apply, (hint N 0 X hX _ γ hγd).2]
    exact Submission.dimred_mbl_dt_lpc_ftc_current hREP N 0 X hX ω β γ hβ hγ
  -- Step 5, degree `k + 1`: the coordinate formula for `d` gives
  -- `η^{dω}_t = ∂_tβ^ω_t − d(η^ω_t)` (*), and `X(dη^ω_t) = ∂X(η^ω_t)`, so
  -- `∂cyl(X)(ω) = ∫₀¹ X(∂_tβ^ω_t) dt − ∫₀¹ ∂X(η^ω_t) dt = X(β^ω_1) − X(β^ω_0) − cyl(∂X)(ω)`
  have hB : ∀ (N k : ℕ) (X : GeometricCurrentOn (univ : Set (Euclid N)) (k + 1)), X.mass < ∞ →
      X.boundary.mass < ∞ → ∀ (ω : TestFormOn (univ : Set (Euclid (N + 1))) (k + 1))
        (β : ℝ → TestFormOn (univ : Set (Euclid N)) (k + 1)),
      (∀ (s : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N),
        (β s : DifferentialForm (Euclid N) (k + 1)) x v =
          (ω : DifferentialForm (Euclid (N + 1)) (k + 1))
            (WithLp.toLp 2 (Fin.cons s (WithLp.ofLp x)))
            (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) →
      (cyl N (k + 1) X).boundary ω = X (β 1) - X (β 0) - cyl N k X.boundary ω := by
    intro N k X hX hbX ω β hβ
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    obtain ⟨-, ⟨γ, hγ⟩, -⟩ := hS.2 N (k + 1) ω
    have hηd : ∀ (t : ℝ) (x : Euclid N) (v : Fin (k + 1) → Euclid N),
        ((γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t) :
            TestFormOn (univ : Set (Euclid N)) (k + 1)) :
          DifferentialForm (Euclid N) (k + 1)) x v =
          (exteriorDerivativeTestOn (univ : Set (Euclid (N + 1))) (k + 1) ω :
            DifferentialForm (Euclid (N + 1)) (k + 1 + 1))
            (WithLp.toLp 2 (Fin.cons t (WithLp.ofLp x)))
            (Fin.cons (EuclideanSpace.single 0 1)
              (fun i => WithLp.toLp 2 (Fin.cons 0 (WithLp.ofLp (v i))))) := by
      intro t x v
      simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
      rw [hγ t x v]
      exact (Submission.dimred_mbl_dt_lpc_slice_extDeriv.1 N k ω η hη t x v).symm
    obtain ⟨hc₁, h₁⟩ := hint N (k + 1) X hX _ _ hηd
    obtain ⟨hc₂, h₂⟩ := hint N k X.boundary hbX ω η hη
    have hsplit : ∀ t, X (γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t)) =
        X (γ t) - X.boundary (η t) := fun t => map_sub X.toCurrent _ _
    -- `t ↦ X(∂_tβ^ω_t) = X(η^{dω}_t) + ∂X(η^ω_t)` is continuous
    have hc₃ : Continuous fun t => X (γ t) := by
      have h : (fun t => X (γ t)) = fun t =>
          X (γ t - exteriorDerivativeTestOn (univ : Set (Euclid N)) k (η t)) +
            X.boundary (η t) := by
        funext t
        rw [hsplit t, sub_add_cancel]
      rw [h]
      exact hc₁.add hc₂
    rw [GeometricCurrentOn.boundary_apply, h₁, h₂]
    simp_rw [hsplit]
    rw [intervalIntegral.integral_sub (hc₃.intervalIntegrable 0 1) (hc₂.intervalIntegrable 0 1),
      Submission.dimred_mbl_dt_lpc_ftc_current hREP N (k + 1) X hX ω β γ hβ hγ]
  refine ⟨cyl, fun N k X hXc hX hbX => ?_, fun N k X Y hXc hX hbX hYc hY hbY => ?_,
    fun N k X hXc hX hbX ω => ?_, fun N X hXc hX ω => ?_, fun N k X hXc hX hbX ω => ?_⟩
  · -- (C1): steps 2 and 4; step 6: `∂cyl(X)(ω) ≤ 2M(X) + M(∂X)` for admissible `ω`
    obtain ⟨hc, hs⟩ := hsupp N k X hX hXc
    refine ⟨hc, hmass N k X hX, ?_, hs⟩
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ω ∈ massAdmissibleOn (univ : Set (Euclid (N + 1))) k univ,
        (cyl N k X).boundary ω ≤ C := by
      rcases k with _ | k
      · refine ⟨2 * X.mass.toReal, fun ω hω => ?_⟩
        obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N 0 ω
        have h₁ := abs_le.mp (hβbd N 0 X hX ω hω.2 β hβ 1)
        have h₀ := abs_le.mp (hβbd N 0 X hX ω hω.2 β hβ 0)
        rw [hB₀ N X hX ω β hβ]
        linarith [h₁.2, h₀.1]
      · have hbX' : X.boundary.mass < ∞ := hbX
        refine ⟨2 * X.mass.toReal + X.boundary.mass.toReal, fun ω hω => ?_⟩
        obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N (k + 1) ω
        have h₁ := abs_le.mp (hβbd N (k + 1) X hX ω hω.2 β hβ 1)
        have h₀ := abs_le.mp (hβbd N (k + 1) X hX ω hω.2 β hβ 0)
        -- `|cyl(∂X)(ω)| ≤ M(cyl ∂X) ≤ M(∂X)`
        have hm := hmass N k X.boundary hbX'
        have h₂ := abs_le.mp (Submission.cmc_fc_sc_abs_le_mul_mass (N + 1) (k + 1) univ
          (cyl N k X.boundary) ω 1 one_pos (ne_top_of_le_ne_top hbX'.ne hm) hω.2)
        have h₃ := ENNReal.toReal_mono hbX'.ne hm
        rw [hB N k X hX hbX' ω β hβ]
        linarith [h₁.2, h₀.1, h₂.1]
    calc (cyl N k X).boundary.mass ≤ ENNReal.ofReal C := by
          unfold GeometricCurrentOn.mass GeometricCurrentOn.massOn
          refine sSup_le ?_
          rintro _ ⟨ω, hω, rfl⟩
          exact ENNReal.ofReal_le_ofReal (hC ω hω)
      _ < ∞ := ENNReal.ofReal_lt_top
  · -- (C2), step 3: `M(X − Y) ≤ M(X) + M(Y) < ∞`, and the `t`-integrals are linear
    have hXY : (X - Y).mass < ∞ := lt_of_le_of_lt
      (Submission.cmc_fc_cs_massOn_sub_le N k univ univ X Y) (ENNReal.add_lt_top.mpr ⟨hX, hY⟩)
    ext ω
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    obtain ⟨hcX, hX'⟩ := hint N k X hX ω η hη
    obtain ⟨hcY, hY'⟩ := hint N k Y hY ω η hη
    change cyl N k (X - Y) ω = cyl N k X ω - cyl N k Y ω
    rw [(hint N k (X - Y) hXY ω η hη).2, hX', hY',
      ← intervalIntegral.integral_sub (hcX.intervalIntegrable 0 1) (hcY.intervalIntegrable 0 1)]
    rfl
  · -- (C3), step 2
    obtain ⟨⟨η, hη⟩, -⟩ := hS.1 N k ω
    exact ⟨η, hη, (hint N k X hX ω η hη).2⟩
  · -- (C4), step 5 with `η_s = β^ω_s`
    obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N 0 ω
    exact ⟨β 0, β 1, hβ 0, hβ 1, hB₀ N X hX ω β hβ⟩
  · -- (C5), step 5 with `η_s = β^ω_s`
    obtain ⟨⟨β, hβ⟩, -⟩ := hS.2 N (k + 1) ω
    exact ⟨β 0, β 1, hβ 0, hβ 1, hB N k X hX hbX ω β hβ⟩

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
