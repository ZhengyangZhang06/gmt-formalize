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

set_option maxHeartbeats 4000000 in
/-- **Interior Schauder bootstrap** for `Δw = div(B[Dw] + g)` with `‖B‖ ≤ ε₁`
(Giaquinta–Martinazzi 2012, §5.4): if `B, g ∈ C^{l,α}_loc(Ω)` then `w ∈ C^{l+1,α}_loc(Ω)`.
Induction on `l`.  `l = 0`: on small balls `F = B[Dw] + g` satisfies the Campanato hypothesis of
`codim1_hcp_sr_c1alpha_estimate` (split `F - (B(z)[(Dw)_{z,ρ}] + g(z))` into three pieces).
`l = 1`: the difference quotients `w_t = t⁻¹(w(· + tv) - w)` solve `Δw_t = div(B[Dw_t] + g_t)`
(translation invariance of the weak equation) with data bounded and Hölder uniformly in `t, v`, so
`c1alpha_estimate` and `codim1_hcp_sr_difference_quotient` give `Dw ∈ C^{1,α}`.  `l ≥ 2`:
differentiating the translated equation at `t = 0` shows that `∂ₛw` solves
`Δ∂ₛw = div(B[D∂ₛw] + (∂ₛB)[Dw] + ∂ₛg)`; the induction hypothesis and
`codim1_hcp_sr_holder_algebra` give `Dw = Σₛ Λₛ(∂ₛw) ∈ C^{l,α}`. -/
theorem Submission.codim1_hcp_sr_linear_bootstrap : ∀ (m k : ℕ) (α : ℝ), 1 ≤ m → 0 < α → α < 1 → ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ (Ω : Set (Euclid m)) (l : ℕ) (w : Euclid m → Euclid k) (B : Euclid m → ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k))) (g : Euclid m → (Euclid m →L[ℝ] Euclid k)), IsOpen Ω → ContDiffOn ℝ 1 w Ω → (∀ x ∈ Ω, ‖B x‖ ≤ ε₁) → (ContDiffOn ℝ l B Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l B y - iteratedFDeriv ℝ l B z‖ ≤ C * ‖y - z‖ ^ α) → (ContDiffOn ℝ l g Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ l g y - iteratedFDeriv ℝ l g z‖ ≤ C * ‖y - z‖ ^ α) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ Ω → ∫ x in Ω, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in Ω, ∑ j : Fin m, inner ℝ ((B x (fderiv ℝ w x) + g x) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (ContDiffOn ℝ (l + 1) w Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ, ‖iteratedFDeriv ℝ (l + 1) w y - iteratedFDeriv ℝ (l + 1) w z‖ ≤ C * ‖y - z‖ ^ α) := by
  intro m k α hm hα hα1
  -- The prerequisites.  The Campanato hypothesis (H_F) of `codim1_hcp_sr_c1alpha_estimate` is used
  -- in the three-term form `ε₁ (∫ ‖Dw - (Dw)ₓ,ᵨ‖²) + Kρ^{2α} (∫ ‖Dw‖²) + Kρ^{m+2α}` of its statement.
  have hC1 : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ K R : ℝ, 0 ≤ K → 0 < R → ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Euclid m) (w : Euclid m → Euclid k) (F : Euclid m → (Euclid m →L[ℝ] Euclid k)), ContDiffOn ℝ 1 w (ball x₀ R) → ContinuousOn F (ball x₀ R) → (∀ x ∈ ball x₀ R, ‖w x‖ ≤ K) → (∀ x ∈ ball x₀ R, ‖F x‖ ≤ ε₁ * ‖fderiv ℝ w x‖ + K) → (∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R → ∃ c : Euclid m →L[ℝ] Euclid k, ∫ z in ball x ρ, ‖F z - c‖ ^ 2 ≤ ε₁ * (∫ z in ball x ρ, ‖fderiv ℝ w z - ⨍ z' in ball x ρ, fderiv ℝ w z'‖ ^ 2) + K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ w z‖ ^ 2) + K * ρ ^ ((m : ℝ) + 2 * α)) → (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x₀ R → ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (fderiv ℝ w x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) = ∫ x in ball x₀ R, ∑ j : Fin m, inner ℝ (F x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) → (∀ x ∈ ball x₀ (R / 4), ‖fderiv ℝ w x‖ ≤ C) ∧ ∀ x ∈ ball x₀ (R / 4), ∀ y ∈ ball x₀ (R / 4), ‖fderiv ℝ w x - fderiv ℝ w y‖ ≤ C * ‖x - y‖ ^ α := Submission.codim1_hcp_sr_c1alpha_estimate m k α hm hα hα1
  have hDQ := Submission.codim1_hcp_sr_difference_quotient m k α hm hα
  have hHA := Submission.codim1_hcp_sr_holder_algebra m α
  -- Jets of order `0` and `1` are isometric to the value and to the derivative.
  have hZ0 : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E) (y z : Euclid m),
      ‖iteratedFDeriv ℝ 0 f y - iteratedFDeriv ℝ 0 f z‖ = ‖f y - f z‖ := by
    intro E _ _ f y z
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map]
  have hZ1 : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E) (y z : Euclid m),
      ‖iteratedFDeriv ℝ 1 f y - iteratedFDeriv ℝ 1 f z‖ = ‖fderiv ℝ f y - fderiv ℝ f z‖ := by
    intro E _ _ f y z
    have h1 : ∀ x, iteratedFDeriv ℝ 1 f x =
        (continuousMultilinearCurryFin1 ℝ (Euclid m) E).symm (fderiv ℝ f x) := by
      intro x; ext v; simp [iteratedFDeriv_one_apply]
    rw [h1, h1, ← map_sub, LinearIsometryEquiv.norm_map]
  -- The weak formulation: integrands vanish off `tsupport ζ`, are integrable, and the equation
  -- can be translated, restricted to open subsets and differentiated in a translation parameter.
  have hVAN : ∀ (Ψ : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k) (y : Euclid m),
      y ∉ tsupport ζ →
      ∑ j : Fin m, inner ℝ (Ψ y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) = 0 := by
    intro Ψ ζ y hy
    simp [fderiv_of_notMem_tsupport ℝ hy]
  have hSI : ∀ (S : Set (Euclid m)) (Ψ : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k),
      tsupport ζ ⊆ S →
      ∫ x in S, ∑ j : Fin m, inner ℝ (Ψ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
      ∫ x, ∑ j : Fin m, inner ℝ (Ψ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) := by
    intro S Ψ ζ hS
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => hVAN Ψ ζ y fun h => hy (hS h)
  have hINT : ∀ (Ψ : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k),
      ContDiff ℝ 1 ζ → HasCompactSupport ζ → ContinuousOn Ψ (tsupport ζ) →
      Integrable (fun x => ∑ j : Fin m, inner ℝ (Ψ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) := by
    intro Ψ ζ hζ hζc hΨ
    have hdζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
    have hcont : ContinuousOn (fun x => ∑ j : Fin m, inner ℝ (Ψ x (EuclideanSpace.single j (1 : ℝ)))
        (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) (tsupport ζ) :=
      continuousOn_finsetSum _ fun j _ =>
        (hΨ.clm_apply continuousOn_const).inner (hdζ.continuousOn.clm_apply continuousOn_const)
    exact (hcont.integrableOn_compact hζc).integrable_of_forall_notMem_eq_zero fun y hy => hVAN Ψ ζ y hy
  have hTr : ∀ (O : Set (Euclid m)) (u : Euclid m → Euclid k) (Φ : Euclid m → (Euclid m →L[ℝ] Euclid k)),
      (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ O →
        ∫ x in O, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
        ∫ x in O, ∑ j : Fin m, inner ℝ (Φ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
      ∀ (ζ : Euclid m → Euclid k), ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ a : Euclid m, (∀ y ∈ tsupport ζ, y + a ∈ O) →
        ∫ x, ∑ j : Fin m, inner ℝ (fderiv ℝ u (x + a) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
        ∫ x, ∑ j : Fin m, inner ℝ (Φ (x + a) (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) := by
    intro O u Φ hweak ζ hζ hζc a ha
    have hζa1 : ContDiff ℝ 1 (fun y => ζ (y - a)) := hζ.comp (contDiff_id.sub contDiff_const)
    have hζac : HasCompactSupport (fun y => ζ (y - a)) := hζc.comp_homeomorph (Homeomorph.subRight a)
    have hζat : tsupport (fun y => ζ (y - a)) = (fun y => y - a) ⁻¹' tsupport ζ :=
      tsupport_comp_eq_preimage ζ (Homeomorph.subRight a)
    have hζaO : tsupport (fun y => ζ (y - a)) ⊆ O := by
      intro y hy
      rw [hζat] at hy
      simpa using ha _ hy
    have key : ∀ Ψ : Euclid m → (Euclid m →L[ℝ] Euclid k),
        ∫ x in O, ∑ j : Fin m, inner ℝ (Ψ x (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ (fun y => ζ (y - a)) x (EuclideanSpace.single j (1 : ℝ))) =
        ∫ x, ∑ j : Fin m, inner ℝ (Ψ (x + a) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) := by
      intro Ψ
      rw [hSI O Ψ _ hζaO]
      refine (integral_add_right_eq_self _ a).symm.trans ?_
      simp only [fderiv_comp_sub, add_sub_cancel_right]
    have h := hweak _ hζa1 hζac hζaO
    rw [key (fderiv ℝ u), key Φ] at h
    exact h
  have hDER : ∀ (U : Set (Euclid m)) (Φ : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k)
      (v : Euclid m), IsOpen U → ContDiffOn ℝ 1 Φ U → ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ U →
      HasDerivAt (fun t : ℝ => ∫ y, ∑ j : Fin m, inner ℝ (Φ (y + t • v) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
        (∫ y, ∑ j : Fin m, inner ℝ (fderiv ℝ Φ y v (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) 0 := by
    intro U Φ ζ v hU hΦ hζ hζc hζU
    obtain ⟨δ, hδ, hδU⟩ := hζc.isCompact.exists_cthickening_subset_open hU hζU
    have hK' : IsCompact (cthickening δ (tsupport ζ)) := hζc.isCompact.cthickening
    have hdΦc : ContinuousOn (fderiv ℝ Φ) U := hΦ.continuousOn_fderiv_of_isOpen hU le_rfl
    obtain ⟨MΦ, hMΦ⟩ := hK'.exists_bound_of_continuousOn (f := fderiv ℝ Φ) (hdΦc.mono hδU)
    have hdζ : Continuous (fderiv ℝ ζ) := hζ.continuous_fderiv one_ne_zero
    obtain ⟨Mζ, hMζ⟩ := hdζ.bounded_above_of_compact_support (hζc.fderiv ℝ)
    set r := δ / (‖v‖ + 1) with hr_def
    have hr : 0 < r := by positivity
    have hmem : ∀ y ∈ tsupport ζ, ∀ t ∈ ball (0 : ℝ) r, y + t • v ∈ cthickening δ (tsupport ζ) := by
      intro y hy t ht
      refine mem_cthickening_of_dist_le _ y δ _ hy ?_
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [mem_ball, dist_zero_right] at ht
      have h1 : r * (‖v‖ + 1) = δ := div_mul_cancel₀ δ (by positivity)
      nlinarith [norm_nonneg t, norm_nonneg v]
    have hΦd : ∀ x ∈ U, HasFDerivAt Φ (fderiv ℝ Φ x) x := fun x hx =>
      (((hΦ.differentiableOn one_ne_zero) x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
    have hline : ∀ (y : Euclid m) (t : ℝ), HasDerivAt (fun t : ℝ => y + t • v) v t := by
      intro y t
      simpa using ((hasDerivAt_id t).smul_const v).const_add y
    have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
      (F := fun t y => ∑ j : Fin m, inner ℝ (Φ (y + t • v) (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
      (F' := fun t y => ∑ j : Fin m, inner ℝ (fderiv ℝ Φ (y + t • v) v (EuclideanSpace.single j (1 : ℝ)))
          (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
      (bound := (tsupport ζ).indicator fun _ => (m : ℝ) * (MΦ * ‖v‖ * Mζ))
      (ball_mem_nhds (0 : ℝ) hr) ?meas ?int ?meas' ?bd ?bdint ?diff
    · simpa using key.2
    case meas =>
      refine Filter.eventually_of_mem (ball_mem_nhds (0 : ℝ) hr) fun t ht => ?_
      refine (hINT _ ζ hζ hζc ?_).aestronglyMeasurable
      exact hΦ.continuousOn.comp (continuousOn_id.add continuousOn_const)
        fun y hy => hδU (hmem y hy t ht)
    case int =>
      refine hINT _ ζ hζ hζc ?_
      exact hΦ.continuousOn.comp (continuousOn_id.add continuousOn_const)
        fun y hy => hδU (hmem y hy 0 (mem_ball_self hr))
    case meas' =>
      refine (hINT _ ζ hζ hζc ?_).aestronglyMeasurable
      exact (hdΦc.comp (continuousOn_id.add continuousOn_const)
        fun y hy => hδU (hmem y hy 0 (mem_ball_self hr))).clm_apply continuousOn_const
    case bd =>
      refine Filter.Eventually.of_forall fun y t ht => ?_
      by_cases hy : y ∈ tsupport ζ
      · rw [Set.indicator_of_mem hy]
        refine (norm_sum_le _ _).trans ?_
        have hj : ∀ j : Fin m, ‖inner ℝ (fderiv ℝ Φ (y + t • v) v (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))‖ ≤ MΦ * ‖v‖ * Mζ := by
          intro j
          have he : ‖EuclideanSpace.single j (1 : ℝ)‖ = 1 := by simp
          have hA : ‖fderiv ℝ Φ (y + t • v) v (EuclideanSpace.single j (1 : ℝ))‖ ≤ MΦ * ‖v‖ := by
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            rw [he, mul_one]
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            exact mul_le_mul_of_nonneg_right (hMΦ _ (hmem y hy t ht)) (norm_nonneg _)
          have hD : ‖fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))‖ ≤ Mζ := by
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            rw [he, mul_one]
            exact hMζ y
          exact (norm_inner_le_norm _ _).trans
            (mul_le_mul hA hD (norm_nonneg _) ((norm_nonneg _).trans hA))
        refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
        simp
      · rw [Set.indicator_of_notMem hy]
        simp [fderiv_of_notMem_tsupport ℝ hy]
    case bdint =>
      rw [integrable_indicator_iff (isClosed_tsupport ζ).measurableSet]
      exact integrableOn_const hζc.isCompact.measure_lt_top.ne
    case diff =>
      refine Filter.Eventually.of_forall fun y t ht => ?_
      by_cases hy : y ∈ tsupport ζ
      · have h1 : HasDerivAt (fun t : ℝ => Φ (y + t • v)) (fderiv ℝ Φ (y + t • v) v) t :=
          (hΦd _ (hδU (hmem y hy t ht))).comp_hasDerivAt t (hline y t)
        have h2 := HasDerivAt.sum (u := Finset.univ) (x := t)
          (A := fun j t => inner ℝ (Φ (y + t • v) (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
          (A' := fun j => inner ℝ (fderiv ℝ Φ (y + t • v) v (EuclideanSpace.single j (1 : ℝ)))
            (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) fun j _ => by
          have h3 := (h1.clm_apply (hasDerivAt_const t (EuclideanSpace.single j (1 : ℝ)))).inner ℝ
            (hasDerivAt_const t (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))))
          simpa using h3
        convert h2 using 1
        ext t'
        simp
      · simp only [fderiv_of_notMem_tsupport ℝ hy, zero_apply, inner_zero_right,
          Finset.sum_const_zero]
        exact hasDerivAt_const t (0 : ℝ)
  have hRES : ∀ (O O' : Set (Euclid m)) (u : Euclid m → Euclid k) (Φ : Euclid m → (Euclid m →L[ℝ] Euclid k)),
      O' ⊆ O →
      (∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ O →
        ∫ x in O, ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
        ∫ x in O, ∑ j : Fin m, inner ℝ (Φ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ)))) →
      ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ O' →
        ∫ x in O', ∑ j : Fin m, inner ℝ (fderiv ℝ u x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) =
        ∫ x in O', ∑ j : Fin m, inner ℝ (Φ x (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ x (EuclideanSpace.single j (1 : ℝ))) := by
    intro O O' u Φ hO' h ζ hζ hζc hζO'
    rw [hSI O' _ ζ hζO', hSI O' _ ζ hζO', ← hSI O _ ζ (hζO'.trans hO'),
      ← hSI O _ ζ (hζO'.trans hO')]
    exact h ζ hζ hζc (hζO'.trans hO')
  have hLIN : ∀ (Ψ Φ₁ Φ₂ : Euclid m → (Euclid m →L[ℝ] Euclid k)) (ζ : Euclid m → Euclid k) (c : ℝ),
      (∀ y ∈ tsupport ζ, Ψ y = c • (Φ₁ y - Φ₂ y)) → ∀ y : Euclid m,
      ∑ j : Fin m, inner ℝ (Ψ y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
        c * (∑ j : Fin m, inner ℝ (Φ₁ y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) -
          ∑ j : Fin m, inner ℝ (Φ₂ y (EuclideanSpace.single j (1 : ℝ))) (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) := by
    intro Ψ Φ₁ Φ₂ ζ c h y
    by_cases hy : y ∈ tsupport ζ
    · rw [h y hy, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_apply, sub_apply, inner_smul_left, inner_sub_left]
      simp
    · rw [hVAN _ ζ y hy, hVAN _ ζ y hy, hVAN _ ζ y hy]
      ring
  -- Mean value estimates for increments and for differences of increments.
  have hQB : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E) (c : Euclid m) (r M : ℝ),
      (∀ u ∈ ball c r, DifferentiableAt ℝ f u) → (∀ u ∈ ball c r, ‖fderiv ℝ f u‖ ≤ M) →
      ∀ y a : Euclid m, y ∈ ball c r → y + a ∈ ball c r → ‖f (y + a) - f y‖ ≤ M * ‖a‖ := by
    intro E _ _ f c r M hd hb y a hy hya
    have := (convex_ball c r).norm_image_sub_le_of_norm_fderiv_le hd hb hy hya
    simpa using this
  have hQH : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euclid m → E) (c : Euclid m) (r M : ℝ),
      (∀ u ∈ ball c r, DifferentiableAt ℝ f u) →
      (∀ u ∈ ball c r, ∀ u' ∈ ball c r, ‖fderiv ℝ f u - fderiv ℝ f u'‖ ≤ M * ‖u - u'‖ ^ α) →
      ∀ y z a : Euclid m, y ∈ ball c r → z ∈ ball c r → y + a ∈ ball c r → z + a ∈ ball c r →
        ‖(f (y + a) - f y) - (f (z + a) - f z)‖ ≤ M * ‖y - z‖ ^ α * ‖a‖ := by
    intro E _ _ f c r M hd hh y z a hy hz hya hza
    set S := ball c r ∩ ball (c - (z - y)) r with hS
    have hmemS : ∀ u, u ∈ S ↔ u ∈ ball c r ∧ u + (z - y) ∈ ball c r := by
      intro u
      simp only [hS, mem_inter_iff, mem_ball, dist_eq_norm]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> convert h2 using 2 <;> abel
    have hdψ : ∀ u ∈ S, HasFDerivAt (fun u => f u - f (u + (z - y)))
        (fderiv ℝ f u - fderiv ℝ f (u + (z - y))) u := by
      intro u hu
      rw [hmemS] at hu
      have h1 := (hd u hu.1).hasFDerivAt
      have h2 : HasFDerivAt (fun u => f (u + (z - y))) (fderiv ℝ f (u + (z - y))) u :=
        (hasFDerivAt_comp_add_right (z - y)).2 (hd _ hu.2).hasFDerivAt
      exact h1.sub h2
    have hbd : ∀ u ∈ S, ‖fderiv ℝ (fun u => f u - f (u + (z - y))) u‖ ≤ M * ‖y - z‖ ^ α := by
      intro u hu
      rw [(hdψ u hu).fderiv]
      have hu' := (hmemS u).1 hu
      have := hh u hu'.1 _ hu'.2
      have e : ‖u - (u + (z - y))‖ = ‖y - z‖ := by
        rw [show u - (u + (z - y)) = y - z by abel]
      rwa [e] at this
    have hyS : y ∈ S := (hmemS y).2 ⟨hy, by simpa using hz⟩
    have hyaS : y + a ∈ S := (hmemS _).2 ⟨hya, by convert hza using 1; abel⟩
    have hconv : Convex ℝ S := (convex_ball _ _).inter (convex_ball _ _)
    have := hconv.norm_image_sub_le_of_norm_fderiv_le (fun u hu => (hdψ u hu).differentiableAt) hbd hyS hyaS
    have e1 : (f (y + a) - f (y + a + (z - y))) - (f y - f (y + (z - y))) = (f (y + a) - f y) - (f (z + a) - f z) := by
      rw [show y + a + (z - y) = z + a by abel, show y + (z - y) = z by abel]; abel
    rw [e1, show y + a - y = a by abel] at this
    exact this
  -- Bounds and Hölder estimates for derivatives, for a general target space (no instances on
  -- `Euclid m →L[ℝ] ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k))` are synthesized).
  have hBND : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euclid m → F) (S K : Set (Euclid m)),
      IsOpen S → ContDiffOn ℝ 1 f S → IsCompact K → K ⊆ S → ∃ M : ℝ, ∀ y ∈ K, ‖fderiv ℝ f y‖ ≤ M := by
    intro F _ _ f S K hS hf hK hKS
    exact hK.exists_bound_of_continuousOn ((hf.continuousOn_fderiv_of_isOpen hS le_rfl).mono hKS)
  have hHD : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Euclid m → F)
      (S S' : Set (Euclid m)) (C K₁ : ℝ), S ⊆ S' → C ≤ K₁ →
      (∀ y ∈ S', ∀ z ∈ S', ‖iteratedFDeriv ℝ 0 (fun x => fderiv ℝ f x) y -
        iteratedFDeriv ℝ 0 (fun x => fderiv ℝ f x) z‖ ≤ C * ‖y - z‖ ^ α) →
      ∀ y ∈ S, ∀ z ∈ S, ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ K₁ * ‖y - z‖ ^ α := by
    intro F _ _ f S S' C K₁ hSS' hCK h y hy z hz
    have h1 := h y (hSS' hy) z (hSS' hz)
    rw [hZ0] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hCK (by positivity))
  -- `x ↦ f₁ x (f₂ x)` is `C^{l,α}` when `f₁, f₂` are (`holder_algebra (3)` with `β = id`).
  have hAPP :
      ∀ (Ω : Set (Euclid m)), IsOpen Ω → ∀ (l : ℕ) (E₂ E₃ : Type) [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
        [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] (f₁ : Euclid m → (E₂ →L[ℝ] E₃)) (f₂ : Euclid m → E₂),
        (ContDiffOn ℝ l f₁ Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ l f₁ y - iteratedFDeriv ℝ l f₁ z‖ ≤ C * ‖y - z‖ ^ α) →
        (ContDiffOn ℝ l f₂ Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
          ‖iteratedFDeriv ℝ l f₂ y - iteratedFDeriv ℝ l f₂ z‖ ≤ C * ‖y - z‖ ^ α) →
        (ContDiffOn ℝ l (fun x => f₁ x (f₂ x)) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ,
          ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
            ‖iteratedFDeriv ℝ l (fun x => f₁ x (f₂ x)) y - iteratedFDeriv ℝ l (fun x => f₁ x (f₂ x)) z‖ ≤
              C * ‖y - z‖ ^ α) := by
    intro Ω hΩ l E₂ E₃ _ _ _ _ f₁ f₂ h1 h2
    exact (hHA Ω hΩ hα hα1.le l).2.2.1 (E₂ →L[ℝ] E₃) E₂ E₃ (ContinuousLinearMap.id ℝ (E₂ →L[ℝ] E₃)) f₁ f₂ h1 h2
  -- `ε₁ ≤ εD` and `3 ε₁² ≤ εD`, `εD` the constant of `c1alpha_estimate`.
  obtain ⟨εD, hεD, hC1'⟩ := hC1
  obtain ⟨ε₁, hε₁, hε₁D, h3⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ εD ∧ 3 * ε₁ ^ 2 ≤ εD := by
    refine ⟨min (εD / 3) 1, lt_min (by positivity) one_pos, (min_le_left _ _).trans (by linarith), ?_⟩
    have h1 : min (εD / 3) 1 ≤ εD / 3 := min_le_left _ _
    have h2 : min (εD / 3) 1 ≤ 1 := min_le_right _ _
    have h0 : 0 < min (εD / 3) 1 := lt_min (by positivity) one_pos
    nlinarith
  -- Step 0: `F = B[Du] + G` satisfies (H_F) on small balls, with `c = B(x)[(Du)ₓ,ᵨ] + G(x)`.
  have hCamp : ∀ (B : Euclid m → ((Euclid m →L[ℝ] Euclid k) →L[ℝ] (Euclid m →L[ℝ] Euclid k)))
      (x₀ : Euclid m) (R : ℝ) (u : Euclid m → Euclid k) (G : Euclid m → (Euclid m →L[ℝ] Euclid k)) (CB CG K : ℝ),
        0 ≤ CB → 0 ≤ CG → 3 * CB ^ 2 ≤ K → 3 * CG ^ 2 * volume.real (ball (0 : Euclid m) 1) ≤ K →
        ContDiffOn ℝ 1 u (ball x₀ R) → (∀ y ∈ ball x₀ R, ‖B y‖ ≤ ε₁) →
        (∀ y ∈ ball x₀ R, ∀ z ∈ ball x₀ R, ‖B y - B z‖ ≤ CB * ‖y - z‖ ^ α) →
        (∀ y ∈ ball x₀ R, ∀ z ∈ ball x₀ R, ‖G y - G z‖ ≤ CG * ‖y - z‖ ^ α) →
        ∀ (x : Euclid m) (ρ : ℝ), 0 < ρ → closedBall x ρ ⊆ ball x₀ R → ∃ c : Euclid m →L[ℝ] Euclid k,
          ∫ z in ball x ρ, ‖B z (fderiv ℝ u z) + G z - c‖ ^ 2 ≤
            εD * (∫ z in ball x ρ, ‖fderiv ℝ u z - ⨍ z' in ball x ρ, fderiv ℝ u z'‖ ^ 2) +
            K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2) + K * ρ ^ ((m : ℝ) + 2 * α) := by
    intro B x₀ R u G CB CG K hCB hCG hK1 hK2 hu hBb hBh hGh x ρ hρ hxρ
    set avg := ⨍ z' in ball x ρ, fderiv ℝ u z' with havg
    refine ⟨B x avg + G x, ?_⟩
    have hxR : x ∈ ball x₀ R := hxρ (mem_closedBall_self hρ.le)
    have hball : ∀ z ∈ ball x ρ, z ∈ ball x₀ R := fun z hz => hxρ (ball_subset_closedBall hz)
    have hρα : ∀ z ∈ ball x ρ, ‖z - x‖ ^ α ≤ ρ ^ α := fun z hz =>
      Real.rpow_le_rpow (norm_nonneg _) (by rw [mem_ball, dist_eq_norm] at hz; exact hz.le) hα.le
    have hsq : (ρ ^ α) ^ 2 = ρ ^ (2 * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; norm_num [mul_comm]
    have hpt : ∀ z ∈ ball x ρ, ‖B z (fderiv ℝ u z) + G z - (B x avg + G x)‖ ^ 2 ≤
        3 * ε₁ ^ 2 * ‖fderiv ℝ u z - avg‖ ^ 2 + 3 * CB ^ 2 * ρ ^ (2 * α) * ‖fderiv ℝ u z‖ ^ 2 +
          3 * CG ^ 2 * ρ ^ (2 * α) := by
      intro z hz
      have hzR := hball z hz
      have e1 : B z (fderiv ℝ u z) + G z - (B x avg + G x) =
          (B z - B x) (fderiv ℝ u z) + B x (fderiv ℝ u z - avg) + (G z - G x) := by
        simp only [sub_apply, map_sub]; abel
      have n1 : ‖(B z - B x) (fderiv ℝ u z)‖ ≤ CB * ρ ^ α * ‖fderiv ℝ u z‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          ((hBh z hzR x hxR).trans (mul_le_mul_of_nonneg_left (hρα z hz) hCB)) (norm_nonneg _))
      have n2 : ‖B x (fderiv ℝ u z - avg)‖ ≤ ε₁ * ‖fderiv ℝ u z - avg‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hBb x hxR) (norm_nonneg _))
      have n3 : ‖G z - G x‖ ≤ CG * ρ ^ α :=
        (hGh z hzR x hxR).trans (mul_le_mul_of_nonneg_left (hρα z hz) hCG)
      have hsum : ‖B z (fderiv ℝ u z) + G z - (B x avg + G x)‖ ≤
          CB * ρ ^ α * ‖fderiv ℝ u z‖ + ε₁ * ‖fderiv ℝ u z - avg‖ + CG * ρ ^ α := by
        rw [e1]; exact norm_add₃_le.trans (by linarith)
      have hnn : 0 ≤ ‖B z (fderiv ℝ u z) + G z - (B x avg + G x)‖ := norm_nonneg _
      calc ‖B z (fderiv ℝ u z) + G z - (B x avg + G x)‖ ^ 2
          ≤ (CB * ρ ^ α * ‖fderiv ℝ u z‖ + ε₁ * ‖fderiv ℝ u z - avg‖ + CG * ρ ^ α) ^ 2 :=
            pow_le_pow_left₀ hnn hsum 2
        _ ≤ 3 * ((CB * ρ ^ α * ‖fderiv ℝ u z‖) ^ 2 + (ε₁ * ‖fderiv ℝ u z - avg‖) ^ 2 +
              (CG * ρ ^ α) ^ 2) := by
            nlinarith [sq_nonneg (CB * ρ ^ α * ‖fderiv ℝ u z‖ - ε₁ * ‖fderiv ℝ u z - avg‖),
              sq_nonneg (ε₁ * ‖fderiv ℝ u z - avg‖ - CG * ρ ^ α),
              sq_nonneg (CB * ρ ^ α * ‖fderiv ℝ u z‖ - CG * ρ ^ α)]
        _ = 3 * ε₁ ^ 2 * ‖fderiv ℝ u z - avg‖ ^ 2 + 3 * CB ^ 2 * ρ ^ (2 * α) * ‖fderiv ℝ u z‖ ^ 2 +
              3 * CG ^ 2 * ρ ^ (2 * α) := by
            rw [mul_pow, mul_pow, mul_pow, mul_pow, hsq]; ring
    have hUc : ContinuousOn (fderiv ℝ u) (closedBall x ρ) :=
      (hu.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).mono hxρ
    have hI1 : IntegrableOn (fun z => ‖fderiv ℝ u z - avg‖ ^ 2) (ball x ρ) :=
      (((hUc.sub continuousOn_const).norm.pow 2).integrableOn_compact (isCompact_closedBall x ρ)).mono_set
        ball_subset_closedBall
    have hI2 : IntegrableOn (fun z => ‖fderiv ℝ u z‖ ^ 2) (ball x ρ) :=
      ((hUc.norm.pow 2).integrableOn_compact (isCompact_closedBall x ρ)).mono_set ball_subset_closedBall
    have hI3 : IntegrableOn (fun _ : Euclid m => 3 * CG ^ 2 * ρ ^ (2 * α)) (ball x ρ) :=
      integrableOn_const measure_ball_lt_top.ne
    have hvol : volume.real (ball x ρ) = volume.real (ball (0 : Euclid m) 1) * ρ ^ m := by
      simp only [Measure.real]
      rw [Measure.addHaar_ball_of_pos volume x hρ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity)]
      ring
    have hJ1 : 0 ≤ ∫ z in ball x ρ, ‖fderiv ℝ u z - avg‖ ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun z _ => by positivity
    have hJ2 : 0 ≤ ∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2 :=
      setIntegral_nonneg measurableSet_ball fun z _ => by positivity
    have hρ2α : 0 ≤ ρ ^ (2 * α) := by positivity
    have hrpow : ρ ^ ((m : ℝ) + 2 * α) = ρ ^ m * ρ ^ (2 * α) := by
      rw [Real.rpow_add hρ, Real.rpow_natCast]
    have hω : 0 ≤ volume.real (ball (0 : Euclid m) 1) := measureReal_nonneg
    have i1 : Integrable (fun z => 3 * ε₁ ^ 2 * ‖fderiv ℝ u z - avg‖ ^ 2) (volume.restrict (ball x ρ)) :=
      hI1.const_mul _
    have i2 : Integrable (fun z => 3 * CB ^ 2 * ρ ^ (2 * α) * ‖fderiv ℝ u z‖ ^ 2)
        (volume.restrict (ball x ρ)) := hI2.const_mul _
    have i12 : Integrable (fun z => 3 * ε₁ ^ 2 * ‖fderiv ℝ u z - avg‖ ^ 2 +
        3 * CB ^ 2 * ρ ^ (2 * α) * ‖fderiv ℝ u z‖ ^ 2) (volume.restrict (ball x ρ)) := i1.add i2
    calc ∫ z in ball x ρ, ‖B z (fderiv ℝ u z) + G z - (B x avg + G x)‖ ^ 2
        ≤ ∫ z in ball x ρ, (3 * ε₁ ^ 2 * ‖fderiv ℝ u z - avg‖ ^ 2 +
            3 * CB ^ 2 * ρ ^ (2 * α) * ‖fderiv ℝ u z‖ ^ 2 + 3 * CG ^ 2 * ρ ^ (2 * α)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) (i12.add hI3) ?_
          exact (ae_restrict_iff' measurableSet_ball).mpr (Filter.Eventually.of_forall hpt)
      _ = 3 * ε₁ ^ 2 * (∫ z in ball x ρ, ‖fderiv ℝ u z - avg‖ ^ 2) +
            3 * CB ^ 2 * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2) +
            3 * CG ^ 2 * ρ ^ (2 * α) * volume.real (ball x ρ) := by
          rw [integral_add i12 hI3, integral_add i1 i2, integral_const_mul, integral_const_mul,
            setIntegral_const, smul_eq_mul]
          ring
      _ ≤ εD * (∫ z in ball x ρ, ‖fderiv ℝ u z - avg‖ ^ 2) +
            K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2) + K * ρ ^ ((m : ℝ) + 2 * α) := by
          rw [hvol, hrpow]
          have e1 : 3 * ε₁ ^ 2 * (∫ z in ball x ρ, ‖fderiv ℝ u z - avg‖ ^ 2) ≤
              εD * (∫ z in ball x ρ, ‖fderiv ℝ u z - avg‖ ^ 2) := mul_le_mul_of_nonneg_right h3 hJ1
          have e2 : 3 * CB ^ 2 * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2) ≤
              K * ρ ^ (2 * α) * (∫ z in ball x ρ, ‖fderiv ℝ u z‖ ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hρ2α) hJ2
          have e3 : 3 * CG ^ 2 * ρ ^ (2 * α) * (volume.real (ball (0 : Euclid m) 1) * ρ ^ m) ≤
              K * (ρ ^ m * ρ ^ (2 * α)) := by
            calc 3 * CG ^ 2 * ρ ^ (2 * α) * (volume.real (ball (0 : Euclid m) 1) * ρ ^ m)
                = (3 * CG ^ 2 * volume.real (ball (0 : Euclid m) 1)) * (ρ ^ m * ρ ^ (2 * α)) := by ring
              _ ≤ K * (ρ ^ m * ρ ^ (2 * α)) := mul_le_mul_of_nonneg_right hK2 (by positivity)
          linarith
  -- Induction on `l`, for all `w, B, g` at once.
  refine ⟨ε₁, hε₁, ?_⟩
  intro Ω l
  induction l with
  | zero =>
    -- l = 0: `c1alpha_estimate` on small balls
    intro w B g hΩ hw hBb hBreg hgreg hweak
    obtain ⟨hBc, hBh⟩ := hBreg
    obtain ⟨hgc, hgh⟩ := hgreg
    rw [Nat.cast_zero, contDiffOn_zero] at hBc hgc
    refine ⟨by simpa using hw, fun x hx => ?_⟩
    obtain ⟨ρB, hρB, hρBΩ, CB, hCB⟩ := hBh x hx
    obtain ⟨ρg, hρg, hρgΩ, Cg, hCg⟩ := hgh x hx
    obtain ⟨R, hR, hRB, hRg⟩ : ∃ R : ℝ, 0 < R ∧ R < ρB ∧ R < ρg :=
      ⟨min ρB ρg / 2, by positivity, by linarith [min_le_left ρB ρg, lt_min hρB hρg],
        by linarith [min_le_right ρB ρg, lt_min hρB hρg]⟩
    have hcl : closedBall x R ⊆ Ω := (closedBall_subset_ball hRB).trans hρBΩ
    have hbR : ball x R ⊆ Ω := ball_subset_closedBall.trans hcl
    have hDwc : ContinuousOn (fun y => fderiv ℝ w y) Ω := hw.continuousOn_fderiv_of_isOpen hΩ le_rfl
    obtain ⟨Mw, hMw⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn (f := w)
      (hw.continuousOn.mono hcl)
    obtain ⟨Mg, hMg⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn (f := g) (hgc.mono hcl)
    obtain ⟨K, hK1, hK2, hMwK, hMgK⟩ : ∃ K : ℝ, 3 * max CB 0 ^ 2 ≤ K ∧
        3 * max Cg 0 ^ 2 * volume.real (ball (0 : Euclid m) 1) ≤ K ∧ Mw ≤ K ∧ Mg ≤ K :=
      ⟨max (max Mw Mg) (max (3 * max CB 0 ^ 2) (3 * max Cg 0 ^ 2 * volume.real (ball (0 : Euclid m) 1))),
        le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _),
        le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _)⟩
    have hK0 : 0 ≤ K := le_trans (by positivity) hK1
    obtain ⟨C, hC0, hC⟩ := hC1' K R hK0 hR
    have hBhol : ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖B y - B z‖ ≤ max CB 0 * ‖y - z‖ ^ α := by
      intro y hy z hz
      have h := hCB y (ball_subset_ball hRB.le hy) z (ball_subset_ball hRB.le hz)
      rw [hZ0] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hghol : ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖g y - g z‖ ≤ max Cg 0 * ‖y - z‖ ^ α := by
      intro y hy z hz
      have h := hCg y (ball_subset_ball hRg.le hy) z (ball_subset_ball hRg.le hz)
      rw [hZ0] at h
      exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    obtain ⟨-, hhol⟩ := hC x w (fun z => B z (fderiv ℝ w z) + g z) (hw.mono hbR)
      (((hBc.mono hbR).clm_apply (hDwc.mono hbR)).add (hgc.mono hbR))
      (fun z hz => (hMw z (ball_subset_closedBall hz)).trans hMwK)
      (fun z hz => by
        have hzΩ := hbR hz
        calc ‖B z (fderiv ℝ w z) + g z‖ ≤ ‖B z (fderiv ℝ w z)‖ + ‖g z‖ := norm_add_le _ _
          _ ≤ ‖B z‖ * ‖fderiv ℝ w z‖ + ‖g z‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ εD * ‖fderiv ℝ w z‖ + K := by
            gcongr
            · exact (hBb z hzΩ).trans hε₁D
            · exact (hMg z (ball_subset_closedBall hz)).trans hMgK)
      (hCamp B x R w g (max CB 0) (max Cg 0) K (le_max_right _ _) (le_max_right _ _) hK1 hK2
        (hw.mono hbR) (fun y hy => hBb y (hbR hy)) hBhol hghol)
      (hRES Ω (ball x R) w (fun z => B z (fderiv ℝ w z) + g z) hbR hweak)
    refine ⟨R / 4, by positivity, (ball_subset_ball (by linarith)).trans hbR, C, fun y hy z hz => ?_⟩
    rw [zero_add, hZ1]
    exact hhol y hy z hz
  | succ n ih =>
    intro w B g hΩ hw hBb hBreg hgreg hweak
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- l = 1: difference quotients
      obtain ⟨-, -, -, -, H5, H6⟩ := hHA Ω hΩ hα hα1.le 0
      obtain ⟨-, -, -, -, -, H6'⟩ := hHA Ω hΩ hα hα1.le 1
      have hB1 : ContDiffOn ℝ 1 B Ω := by simpa using hBreg.1
      have hg1 : ContDiffOn ℝ 1 g Ω := by simpa using hgreg.1
      have hB0 := H5 _ B (by simpa using hB1)
      have hg0 := H5 _ g (by simpa using hg1)
      have hw1 := ih w B g hΩ hw hBb hB0 hg0 hweak
      have hDw0 := (H6 _ w hw).mp hw1
      have hDB0 := (H6 _ B hB1).mp ⟨by simpa using hB1, hBreg.2⟩
      have hDg0 := (H6 _ g hg1).mp ⟨by simpa using hg1, hgreg.2⟩
      have hBc : ContinuousOn B Ω := hB1.continuousOn
      have hgc : ContinuousOn g Ω := hg1.continuousOn
      have hDwc : ContinuousOn (fun y => fderiv ℝ w y) Ω := hw.continuousOn_fderiv_of_isOpen hΩ le_rfl
      have hFc : ContinuousOn (fun y => B y (fderiv ℝ w y) + g y) Ω := (hBc.clm_apply hDwc).add hgc
      have hwd : ∀ y ∈ Ω, DifferentiableAt ℝ w y := fun y hy =>
        (hw.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      have hBd : ∀ y ∈ Ω, DifferentiableAt ℝ B y := fun y hy =>
        (hB1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      have hgd : ∀ y ∈ Ω, DifferentiableAt ℝ g y := fun y hy =>
        (hg1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      have hLOC : ∀ x ∈ Ω, ∃ r : ℝ, 0 < r ∧ ball x r ⊆ Ω ∧
          ContDiffOn ℝ 1 (fun y => fderiv ℝ w y) (ball x r) ∧ ∃ C : ℝ, ∀ y ∈ ball x r, ∀ z ∈ ball x r,
            ‖fderiv ℝ (fun y => fderiv ℝ w y) y - fderiv ℝ (fun y => fderiv ℝ w y) z‖ ≤ C * ‖y - z‖ ^ α := by
        intro x hx
        obtain ⟨ρ1, hρ1, hρ1Ω, C1, hC1h⟩ := hB0.2 x hx
        obtain ⟨ρ2, hρ2, -, C2, hC2h⟩ := hDB0.2 x hx
        obtain ⟨ρ3, hρ3, -, C3, hC3h⟩ := hDg0.2 x hx
        obtain ⟨ρ4, hρ4, -, C4, hC4h⟩ := hDw0.2 x hx
        obtain ⟨R, hR, hR1, hR2, hR3, hR4⟩ : ∃ R : ℝ, 0 < R ∧ 2 * R < ρ1 ∧ 2 * R < ρ2 ∧ 2 * R < ρ3 ∧
            2 * R < ρ4 := by
          refine ⟨min (min ρ1 ρ2) (min ρ3 ρ4) / 4, by positivity, ?_, ?_, ?_, ?_⟩ <;>
            linarith [min_le_left (min ρ1 ρ2) (min ρ3 ρ4), min_le_right (min ρ1 ρ2) (min ρ3 ρ4),
              min_le_left ρ1 ρ2, min_le_right ρ1 ρ2, min_le_left ρ3 ρ4, min_le_right ρ3 ρ4,
              lt_min (lt_min hρ1 hρ2) (lt_min hρ3 hρ4)]
        have hcl : closedBall x (2 * R) ⊆ Ω := (closedBall_subset_ball hR1).trans hρ1Ω
        have hb2 : ball x (2 * R) ⊆ Ω := ball_subset_closedBall.trans hcl
        have hbR : ball x R ⊆ ball x (2 * R) := ball_subset_ball (by linarith)
        have hsub : ball x R ⊆ Ω := hbR.trans hb2
        have hb4 : ball x (R / 4) ⊆ ball x R := ball_subset_ball (by linarith)
        obtain ⟨M1, hM1⟩ := hBND _ B Ω (closedBall x (2 * R)) hΩ hB1 (isCompact_closedBall _ _) hcl
        obtain ⟨M2, hM2⟩ := hBND _ g Ω (closedBall x (2 * R)) hΩ hg1 (isCompact_closedBall _ _) hcl
        obtain ⟨M3, hM3⟩ := hBND _ w Ω (closedBall x (2 * R)) hΩ hw (isCompact_closedBall _ _) hcl
        obtain ⟨K₁, hK₁0, hKM1, hKM2, hKM3, hKC1, hKC2, hKC3, hKC4⟩ : ∃ K₁ : ℝ, 0 ≤ K₁ ∧ M1 ≤ K₁ ∧
            M2 ≤ K₁ ∧ M3 ≤ K₁ ∧ C1 ≤ K₁ ∧ C2 ≤ K₁ ∧ C3 ≤ K₁ ∧ C4 ≤ K₁ :=
          ⟨max 0 (max M1 (max M2 (max M3 (max C1 (max C2 (max C3 C4)))))), by simp, by simp, by simp,
            by simp, by simp, by simp, by simp, by simp⟩
        have hBh : ∀ y ∈ ball x (2 * R), ∀ z ∈ ball x (2 * R), ‖B y - B z‖ ≤ K₁ * ‖y - z‖ ^ α := by
          intro y hy z hz
          have h := hC1h y (ball_subset_ball hR1.le hy) z (ball_subset_ball hR1.le hz)
          rw [hZ0] at h
          exact h.trans (mul_le_mul_of_nonneg_right hKC1 (by positivity))
        have hDBh := hHD _ B (ball x (2 * R)) (ball x ρ2) C2 K₁ (ball_subset_ball hR2.le) hKC2 hC2h
        have hDgh := hHD _ g (ball x (2 * R)) (ball x ρ3) C3 K₁ (ball_subset_ball hR3.le) hKC3 hC3h
        have hDwh := hHD _ w (ball x (2 * R)) (ball x ρ4) C4 K₁ (ball_subset_ball hR4.le) hKC4 hC4h
        have hDBb := fun y (hy : y ∈ ball x (2 * R)) => (hM1 y (ball_subset_closedBall hy)).trans hKM1
        have hDgb := fun y (hy : y ∈ ball x (2 * R)) => (hM2 y (ball_subset_closedBall hy)).trans hKM2
        have hDwb := fun y (hy : y ∈ ball x (2 * R)) => (hM3 y (ball_subset_closedBall hy)).trans hKM3
        have hwd' : ∀ y ∈ ball x (2 * R), DifferentiableAt ℝ w y := fun y hy => hwd y (hb2 hy)
        have hBd' : ∀ y ∈ ball x (2 * R), DifferentiableAt ℝ B y := fun y hy => hBd y (hb2 hy)
        have hgd' : ∀ y ∈ ball x (2 * R), DifferentiableAt ℝ g y := fun y hy => hgd y (hb2 hy)
        obtain ⟨K, hK0, hKK₁, hKK₁', hK3, hK4⟩ : ∃ K : ℝ, 0 ≤ K ∧ K₁ ≤ K ∧ K₁ * K₁ + K₁ ≤ K ∧
            3 * K₁ ^ 2 ≤ K ∧ 3 * (2 * K₁ ^ 2 + K₁) ^ 2 * volume.real (ball (0 : Euclid m) 1) ≤ K :=
          ⟨max K₁ (max (K₁ * K₁ + K₁) (max (3 * K₁ ^ 2)
              (3 * (2 * K₁ ^ 2 + K₁) ^ 2 * volume.real (ball (0 : Euclid m) 1)))),
            hK₁0.trans (le_max_left _ _), le_max_left _ _, by simp, by simp, by simp⟩
        obtain ⟨C, hC0, hC⟩ := hC1' K R hK0 hR
        have hdq : ∀ v : Euclid m, ‖v‖ = 1 → ∀ t : ℝ, t ≠ 0 → |t| < R / 2 →
            (∀ y ∈ ball x (R / 4), ‖t⁻¹ • (fderiv ℝ w (y + t • v) - fderiv ℝ w y)‖ ≤ C) ∧
            ∀ y ∈ ball x (R / 4), ∀ z ∈ ball x (R / 4),
              ‖t⁻¹ • (fderiv ℝ w (y + t • v) - fderiv ℝ w y) -
                t⁻¹ • (fderiv ℝ w (z + t • v) - fderiv ℝ w z)‖ ≤ C * ‖y - z‖ ^ α := by
          intro v hv t ht0 ht
          have htv : ‖t • v‖ = |t| := by rw [norm_smul, hv, mul_one, Real.norm_eq_abs]
          have hta : 0 < |t| := abs_pos.mpr ht0
          have hta' : |t| ≠ 0 := hta.ne'
          have hshift : ∀ y ∈ ball x R, y + t • v ∈ ball x (2 * R) := by
            intro y hy
            rw [mem_ball] at hy ⊢
            calc dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
              _ < R / 2 + R := by
                rw [dist_eq_norm (y + t • v) y, add_sub_cancel_left, htv]; linarith
              _ ≤ 2 * R := by linarith
          have hmaps : MapsTo (fun y : Euclid m => y + t • v) (ball x R) Ω := fun y hy => hb2 (hshift y hy)
          have hshiftc : ContinuousOn (fun y : Euclid m => y + t • v) (ball x R) :=
            continuousOn_id.add continuousOn_const
          -- the difference quotients
          set wt : Euclid m → Euclid k := fun y => t⁻¹ • (w (y + t • v) - w y) with hwt_def
          set gt : Euclid m → (Euclid m →L[ℝ] Euclid k) := fun y =>
            t⁻¹ • (B (y + t • v) (fderiv ℝ w (y + t • v)) - B y (fderiv ℝ w (y + t • v))) +
              t⁻¹ • (g (y + t • v) - g y) with hgt_def
          have hDwt : ∀ y ∈ ball x R, fderiv ℝ wt y = t⁻¹ • (fderiv ℝ w (y + t • v) - fderiv ℝ w y) := by
            intro y hy
            have h1 : HasFDerivAt (fun y => w (y + t • v)) (fderiv ℝ w (y + t • v)) y :=
              (hasFDerivAt_comp_add_right (t • v)).2 (hwd' _ (hshift y hy)).hasFDerivAt
            exact ((h1.sub (hwd' y (hbR hy)).hasFDerivAt).const_smul t⁻¹).fderiv
          have hwt1 : ContDiffOn ℝ 1 wt (ball x R) := by
            have h1 : ContDiffOn ℝ 1 (fun y => w (y + t • v)) (ball x R) :=
              hw.comp (contDiffOn_id.add contDiffOn_const) hmaps
            exact (h1.sub (hw.mono hsub)).const_smul t⁻¹
          have hwtb : ∀ y ∈ ball x R, ‖wt y‖ ≤ K := by
            intro y hy
            have h := hQB _ w x (2 * R) K₁ hwd' hDwb y (t • v) (hbR hy) (hshift y hy)
            rw [htv] at h
            calc ‖wt y‖ = |t|⁻¹ * ‖w (y + t • v) - w y‖ := by
                  simp only [hwt_def, norm_smul, norm_inv, Real.norm_eq_abs]
              _ ≤ |t|⁻¹ * (K₁ * |t|) := by gcongr
              _ = K₁ := by field_simp
              _ ≤ K := hKK₁
          have hDB1 : ∀ y ∈ ball x R, ‖B (y + t • v) - B y‖ ≤ K₁ * |t| := by
            intro y hy
            have h := hQB _ B x (2 * R) K₁ hBd' hDBb y (t • v) (hbR hy) (hshift y hy)
            rwa [htv] at h
          have hDg1 : ∀ y ∈ ball x R, ‖g (y + t • v) - g y‖ ≤ K₁ * |t| := by
            intro y hy
            have h := hQB _ g x (2 * R) K₁ hgd' hDgb y (t • v) (hbR hy) (hshift y hy)
            rwa [htv] at h
          have hDB2 : ∀ y ∈ ball x R, ∀ z ∈ ball x R,
              ‖(B (y + t • v) - B y) - (B (z + t • v) - B z)‖ ≤ K₁ * ‖y - z‖ ^ α * |t| := by
            intro y hy z hz
            have h := hQH _ B x (2 * R) K₁ hBd' hDBh y z (t • v) (hbR hy) (hbR hz) (hshift y hy) (hshift z hz)
            rwa [htv] at h
          have hDg2 : ∀ y ∈ ball x R, ∀ z ∈ ball x R,
              ‖(g (y + t • v) - g y) - (g (z + t • v) - g z)‖ ≤ K₁ * ‖y - z‖ ^ α * |t| := by
            intro y hy z hz
            have h := hQH _ g x (2 * R) K₁ hgd' hDgh y z (t • v) (hbR hy) (hbR hz) (hshift y hy) (hshift z hz)
            rwa [htv] at h
          have hgtb : ∀ y ∈ ball x R, ‖gt y‖ ≤ K₁ * K₁ + K₁ := by
            intro y hy
            have e : gt y = t⁻¹ • ((B (y + t • v) - B y) (fderiv ℝ w (y + t • v))) +
                t⁻¹ • (g (y + t • v) - g y) := by
              simp only [hgt_def, sub_apply]
            have h1 : ‖(B (y + t • v) - B y) (fderiv ℝ w (y + t • v))‖ ≤ K₁ * |t| * K₁ :=
              (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul (hDB1 y hy) (hDwb _ (hshift y hy)) (norm_nonneg _) (by positivity))
            rw [e]
            calc _ ≤ ‖t⁻¹ • ((B (y + t • v) - B y) (fderiv ℝ w (y + t • v)))‖ +
                  ‖t⁻¹ • (g (y + t • v) - g y)‖ := norm_add_le _ _
              _ = |t|⁻¹ * ‖(B (y + t • v) - B y) (fderiv ℝ w (y + t • v))‖ +
                  |t|⁻¹ * ‖g (y + t • v) - g y‖ := by
                rw [norm_smul, norm_smul, norm_inv, Real.norm_eq_abs]
              _ ≤ |t|⁻¹ * (K₁ * |t| * K₁) + |t|⁻¹ * (K₁ * |t|) := by
                gcongr
                exact hDg1 y hy
              _ = K₁ * K₁ + K₁ := by field_simp
          have hgth : ∀ y ∈ ball x R, ∀ z ∈ ball x R, ‖gt y - gt z‖ ≤ (2 * K₁ ^ 2 + K₁) * ‖y - z‖ ^ α := by
            intro y hy z hz
            have e : gt y - gt z = t⁻¹ • (((B (y + t • v) - B y) - (B (z + t • v) - B z)) (fderiv ℝ w (y + t • v)) +
                (B (z + t • v) - B z) (fderiv ℝ w (y + t • v) - fderiv ℝ w (z + t • v)) +
                ((g (y + t • v) - g y) - (g (z + t • v) - g z))) := by
              simp only [hgt_def, sub_apply, map_sub]
              module
            have hyz : 0 ≤ ‖y - z‖ ^ α := by positivity
            have h1 : ‖((B (y + t • v) - B y) - (B (z + t • v) - B z)) (fderiv ℝ w (y + t • v))‖ ≤
                K₁ * ‖y - z‖ ^ α * |t| * K₁ :=
              (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hDB2 y hy z hz)
                (hDwb _ (hshift y hy)) (norm_nonneg _) (by positivity))
            have h2 : ‖(B (z + t • v) - B z) (fderiv ℝ w (y + t • v) - fderiv ℝ w (z + t • v))‖ ≤
                K₁ * |t| * (K₁ * ‖y - z‖ ^ α) := by
              refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hDB1 z hz) ?_ (norm_nonneg _)
                (by positivity))
              have := hDwh _ (hshift y hy) _ (hshift z hz)
              rwa [show y + t • v - (z + t • v) = y - z by abel] at this
            have h3 := hDg2 y hy z hz
            rw [e, norm_smul, norm_inv, Real.norm_eq_abs]
            calc |t|⁻¹ * ‖((B (y + t • v) - B y) - (B (z + t • v) - B z)) (fderiv ℝ w (y + t • v)) +
                  (B (z + t • v) - B z) (fderiv ℝ w (y + t • v) - fderiv ℝ w (z + t • v)) +
                  ((g (y + t • v) - g y) - (g (z + t • v) - g z))‖
                ≤ |t|⁻¹ * (K₁ * ‖y - z‖ ^ α * |t| * K₁ + K₁ * |t| * (K₁ * ‖y - z‖ ^ α) +
                    K₁ * ‖y - z‖ ^ α * |t|) := by
                  gcongr
                  exact norm_add₃_le.trans (by linarith)
              _ = (2 * K₁ ^ 2 + K₁) * ‖y - z‖ ^ α := by field_simp; ring
          have hgtc : ContinuousOn gt (ball x R) := by
            have hDws : ContinuousOn (fun y => fderiv ℝ w (y + t • v)) (ball x R) := hDwc.comp hshiftc hmaps
            exact ((((hBc.comp hshiftc hmaps).clm_apply hDws).sub ((hBc.mono hsub).clm_apply hDws)).const_smul
              t⁻¹).add (((hgc.comp hshiftc hmaps).sub (hgc.mono hsub)).const_smul t⁻¹)
          have hFtc : ContinuousOn (fun y => B y (fderiv ℝ wt y) + gt y) (ball x R) :=
            ((hBc.mono hsub).clm_apply (hwt1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl)).add hgtc
          have hFdef : ∀ y ∈ ball x R, B y (fderiv ℝ wt y) + gt y =
              t⁻¹ • ((B (y + t • v) (fderiv ℝ w (y + t • v)) + g (y + t • v)) - (B y (fderiv ℝ w y) + g y)) := by
            intro y hy
            rw [hDwt y hy]
            simp only [hgt_def, map_smul, map_sub]
            module
          have hweakt : ∀ ζ : Euclid m → Euclid k, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball x R →
              ∫ y in ball x R, ∑ j : Fin m, inner ℝ (fderiv ℝ wt y (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) =
              ∫ y in ball x R, ∑ j : Fin m, inner ℝ ((B y (fderiv ℝ wt y) + gt y) (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ))) := by
            intro ζ hζ hζc hζR
            rw [hSI (ball x R) (fun y => fderiv ℝ wt y) ζ hζR,
              hSI (ball x R) (fun y => B y (fderiv ℝ wt y) + gt y) ζ hζR]
            have l1 := hLIN (fun y => fderiv ℝ wt y) (fun y => fderiv ℝ w (y + t • v)) (fun y => fderiv ℝ w y)
              ζ t⁻¹ (fun y hy => hDwt y (hζR hy))
            have l2 := hLIN (fun y => B y (fderiv ℝ wt y) + gt y)
              (fun y => B (y + t • v) (fderiv ℝ w (y + t • v)) + g (y + t • v))
              (fun y => B y (fderiv ℝ w y) + g y) ζ t⁻¹ (fun y hy => hFdef y (hζR hy))
            have i1 := hINT (fun y => fderiv ℝ w (y + t • v)) ζ hζ hζc ((hDwc.comp hshiftc hmaps).mono hζR)
            have i2 := hINT (fun y => fderiv ℝ w y) ζ hζ hζc (hDwc.mono (hζR.trans hsub))
            have i3 := hINT (fun y => B (y + t • v) (fderiv ℝ w (y + t • v)) + g (y + t • v)) ζ hζ hζc
              ((hFc.comp hshiftc hmaps).mono hζR)
            have i4 := hINT (fun y => B y (fderiv ℝ w y) + g y) ζ hζ hζc (hFc.mono (hζR.trans hsub))
            have T1 := hTr Ω w (fun y => B y (fderiv ℝ w y) + g y) hweak ζ hζ hζc (t • v)
              (fun y hy => hmaps (hζR hy))
            have T0 := hTr Ω w (fun y => B y (fderiv ℝ w y) + g y) hweak ζ hζ hζc 0
              (fun y hy => by simpa using hsub (hζR hy))
            simp only [add_zero] at T0
            refine ((integral_congr_ae (Filter.Eventually.of_forall l1)).trans
              ((integral_const_mul _ _).trans ?_)).trans
              ((integral_congr_ae (Filter.Eventually.of_forall l2)).trans (integral_const_mul _ _)).symm
            exact congrArg (t⁻¹ * ·) ((integral_sub i1 i2).trans
              ((congrArg₂ (· - ·) T1 T0).trans (integral_sub i3 i4).symm))
          obtain ⟨hbd, hhol⟩ := hC x wt (fun y => B y (fderiv ℝ wt y) + gt y) hwt1 hFtc hwtb
            (fun y hy => by
              calc ‖B y (fderiv ℝ wt y) + gt y‖ ≤ ‖B y‖ * ‖fderiv ℝ wt y‖ + ‖gt y‖ :=
                    (norm_add_le _ _).trans (by gcongr; exact ContinuousLinearMap.le_opNorm _ _)
                _ ≤ εD * ‖fderiv ℝ wt y‖ + K := by
                  gcongr
                  · exact (hBb y (hsub hy)).trans hε₁D
                  · exact (hgtb y hy).trans hKK₁')
            (hCamp B x R wt gt K₁ (2 * K₁ ^ 2 + K₁) K hK₁0 (by nlinarith) hK3 hK4 hwt1
              (fun y hy => hBb y (hsub hy)) (fun y hy z hz => hBh y (hbR hy) z (hbR hz)) hgth)
            hweakt
          refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
          · have := hbd y hy
            rwa [hDwt y (hb4 hy)] at this
          · have := hhol y hy z hz
            rwa [hDwt y (hb4 hy), hDwt z (hb4 hz)] at this
        obtain ⟨hDD1, -, hDDh⟩ := hDQ (fun y => fderiv ℝ w y) x (R / 4) (R / 2) C (by positivity)
          (by positivity) (hDwc.mono (hb4.trans hsub)) hdq
        exact ⟨R / 4, by positivity, hb4.trans hsub, hDD1, C, hDDh⟩
      have hDw1 : ContDiffOn ℝ ↑(1 : ℕ) (fun y => fderiv ℝ w y) Ω ∧ ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧
          ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
            ‖iteratedFDeriv ℝ 1 (fun y => fderiv ℝ w y) y - iteratedFDeriv ℝ 1 (fun y => fderiv ℝ w y) z‖ ≤
              C * ‖y - z‖ ^ α := by
        constructor
        · rw [Nat.cast_one]
          refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
          obtain ⟨r, hr, -, hr1, -⟩ := hLOC x hx
          exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hr1.mono inter_subset_right⟩
        · intro x hx
          obtain ⟨r, hr, hrΩ, -, C, hC⟩ := hLOC x hx
          exact ⟨r, hr, hrΩ, C, fun y hy z hz => by rw [hZ1]; exact hC y hy z hz⟩
      exact (H6' _ w hw).mpr hDw1
    · -- l = n + 1 ≥ 2: differentiate the equation
      obtain ⟨H1n, H2n, -, -, H5n, H6n⟩ := hHA Ω hΩ hα hα1.le n
      obtain ⟨H1, H2, -, H4, -, H6⟩ := hHA Ω hΩ hα hα1.le (n + 1)
      have hBC : ContDiffOn ℝ (↑n + 1) B Ω := by rw [← Nat.cast_succ]; exact hBreg.1
      have hgC : ContDiffOn ℝ (↑n + 1) g Ω := by rw [← Nat.cast_succ]; exact hgreg.1
      have h1n : (1 : WithTop ℕ∞) ≤ ↑n + 1 := le_add_self
      have h2n : (2 : WithTop ℕ∞) ≤ ↑n + 1 := by
        have : (1 : WithTop ℕ∞) ≤ ↑n := by exact_mod_cast hn
        calc (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
          _ ≤ ↑n + 1 := by gcongr
      have hB1 : ContDiffOn ℝ 1 B Ω := hBC.of_le h1n
      have hg1 : ContDiffOn ℝ 1 g Ω := hgC.of_le h1n
      have hwn1 := ih w B g hΩ hw hBb (H5n _ B hBC) (H5n _ g hgC) hweak
      have hw2 : ContDiffOn ℝ 2 w Ω := hwn1.1.of_le h2n
      have hDwn := (H6n _ w hw).mp hwn1
      have hDBn := (H6n _ B hB1).mp ⟨hBC, hBreg.2⟩
      have hDgn := (H6n _ g hg1).mp ⟨hgC, hgreg.2⟩
      have hDw1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ w y) Ω := hw2.fderiv_of_isOpen hΩ (by norm_num)
      have hF1 : ContDiffOn ℝ 1 (fun y => B y (fderiv ℝ w y) + g y) Ω := (hB1.clm_apply hDw1).add hg1
      have hBd : ∀ y ∈ Ω, DifferentiableAt ℝ B y := fun y hy =>
        (hB1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      have hgd : ∀ y ∈ Ω, DifferentiableAt ℝ g y := fun y hy =>
        (hg1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      have hDwd : ∀ y ∈ Ω, DifferentiableAt ℝ (fun y => fderiv ℝ w y) y := fun y hy =>
        (hDw1.differentiableOn one_ne_zero y hy).differentiableAt (hΩ.mem_nhds hy)
      -- each partial derivative `∂ₛw` solves the differentiated equation; induction hypothesis
      have hvs : ∀ s : Fin m, ContDiffOn ℝ (↑n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) Ω ∧
          ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
            ‖iteratedFDeriv ℝ (n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) y -
              iteratedFDeriv ℝ (n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) z‖ ≤
                C * ‖y - z‖ ^ α := by
        intro s
        have hconst := H1n _ (EuclideanSpace.single s (1 : ℝ))
        have hBs := hAPP Ω hΩ n _ _ (fun y => fderiv ℝ B y) (fun _ => EuclideanSpace.single s (1 : ℝ)) hDBn
          hconst
        have hBsw := hAPP Ω hΩ n _ _ (fun y => fderiv ℝ B y (EuclideanSpace.single s (1 : ℝ)))
          (fun y => fderiv ℝ w y) hBs hDwn
        have hgs := hAPP Ω hΩ n _ _ (fun y => fderiv ℝ g y) (fun _ => EuclideanSpace.single s (1 : ℝ)) hDgn
          hconst
        refine ih (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) B
          (fun y => fderiv ℝ B y (EuclideanSpace.single s (1 : ℝ)) (fderiv ℝ w y) +
            fderiv ℝ g y (EuclideanSpace.single s (1 : ℝ)))
          hΩ (hDw1.clm_apply contDiffOn_const) hBb (H5n _ B hBC) (H2n _ _ _ hBsw hgs) ?_
        intro ζ hζ hζc hζΩ
        obtain ⟨δ, hδ, hδΩ⟩ := hζc.isCompact.exists_cthickening_subset_open hΩ hζΩ
        have hes : ‖EuclideanSpace.single s (1 : ℝ)‖ = 1 := by simp
        have d1 := hDER Ω (fun y => fderiv ℝ w y) ζ (EuclideanSpace.single s (1 : ℝ)) hΩ hDw1 hζ hζc hζΩ
        have d2 := hDER Ω (fun y => B y (fderiv ℝ w y) + g y) ζ (EuclideanSpace.single s (1 : ℝ)) hΩ hF1 hζ
          hζc hζΩ
        have heq : (fun t : ℝ => ∫ y, ∑ j : Fin m,
            inner ℝ (fderiv ℝ w (y + t • EuclideanSpace.single s (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)))
              (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) =ᶠ[𝓝 0]
            (fun t : ℝ => ∫ y, ∑ j : Fin m,
              inner ℝ ((B (y + t • EuclideanSpace.single s (1 : ℝ))
                (fderiv ℝ w (y + t • EuclideanSpace.single s (1 : ℝ))) +
                  g (y + t • EuclideanSpace.single s (1 : ℝ))) (EuclideanSpace.single j (1 : ℝ)))
                (fderiv ℝ ζ y (EuclideanSpace.single j (1 : ℝ)))) := by
          filter_upwards [ball_mem_nhds (0 : ℝ) hδ] with t ht
          refine hTr Ω w (fun y => B y (fderiv ℝ w y) + g y) hweak ζ hζ hζc _
            fun y hy => hδΩ (mem_cthickening_of_dist_le _ y δ _ hy ?_)
          rw [mem_ball, dist_zero_right] at ht
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hes, mul_one]
          exact ht.le
        have hD := d1.unique (d2.congr_of_eventuallyEq heq)
        have hsym : ∀ y ∈ Ω, fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) y =
            fderiv ℝ (fun y => fderiv ℝ w y) y (EuclideanSpace.single s (1 : ℝ)) := by
          intro y hy
          have hsymm : IsSymmSndFDerivAt ℝ w y :=
            (hw2.contDiffAt (hΩ.mem_nhds hy)).isSymmSndFDerivAt (by simp)
          rw [fderiv_clm_apply (hDwd y hy) (differentiableAt_const _)]
          refine ContinuousLinearMap.ext fun a => ?_
          simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
            ContinuousLinearMap.flip_apply]
          exact hsymm a _
        have hdF : ∀ y ∈ Ω, fderiv ℝ (fun y => B y (fderiv ℝ w y) + g y) y (EuclideanSpace.single s (1 : ℝ)) =
            B y (fderiv ℝ (fun y => fderiv ℝ w y) y (EuclideanSpace.single s (1 : ℝ))) +
              fderiv ℝ B y (EuclideanSpace.single s (1 : ℝ)) (fderiv ℝ w y) +
                fderiv ℝ g y (EuclideanSpace.single s (1 : ℝ)) := by
          intro y hy
          have h : HasFDerivAt (fun y => B y (fderiv ℝ w y) + g y) _ y :=
            ((hBd y hy).hasFDerivAt.clm_apply (hDwd y hy).hasFDerivAt).add (hgd y hy).hasFDerivAt
          rw [h.fderiv]
          simp
        rw [hSI Ω (fun y => fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) y) ζ hζΩ,
          hSI Ω (fun y => B y (fderiv ℝ (fun y => fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) y) +
            (fderiv ℝ B y (EuclideanSpace.single s (1 : ℝ)) (fderiv ℝ w y) +
              fderiv ℝ g y (EuclideanSpace.single s (1 : ℝ)))) ζ hζΩ]
        refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).trans
          (hD.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
        · try dsimp only
          by_cases hy : y ∈ tsupport ζ
          · rw [hsym y (hζΩ hy)]
          · simp [fderiv_of_notMem_tsupport ℝ hy]
        · try dsimp only
          by_cases hy : y ∈ tsupport ζ
          · rw [hsym y (hζΩ hy), hdF y (hζΩ hy), add_assoc]
          · simp [fderiv_of_notMem_tsupport ℝ hy]
      -- reassemble `Dw = ∑ₛ Λₛ (∂ₛw)`
      obtain ⟨Λ, hΛ⟩ : ∃ Λ : Fin m → (Euclid k →L[ℝ] (Euclid m →L[ℝ] Euclid k)),
          ∀ L : Euclid m →L[ℝ] Euclid k, L = ∑ s : Fin m, Λ s (L (EuclideanSpace.single s (1 : ℝ))) := by
        refine ⟨fun s => ContinuousLinearMap.smulRightL ℝ (Euclid m) (Euclid k)
          (innerSL ℝ (EuclideanSpace.single s (1 : ℝ))), fun L => ?_⟩
        refine ContinuousLinearMap.ext fun a => ?_
        have ha := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr' a
        simp only [EuclideanSpace.basisFun_apply] at ha
        rw [sum_apply]
        conv_lhs => rw [← ha]
        rw [map_sum L]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_smul]
        rfl
      have hsum : ∀ S : Finset (Fin m),
          ContDiffOn ℝ ↑(n + 1) (fun y => ∑ s ∈ S, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) Ω ∧
          ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
            ‖iteratedFDeriv ℝ (n + 1) (fun y => ∑ s ∈ S, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) y -
              iteratedFDeriv ℝ (n + 1)
                (fun y => ∑ s ∈ S, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) z‖ ≤
              C * ‖y - z‖ ^ α := by
        intro S
        induction S using Finset.induction_on with
        | empty =>
          have hfun : (fun y => ∑ s ∈ (∅ : Finset (Fin m)),
              Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) = fun _ => (0 : Euclid m →L[ℝ] Euclid k) :=
            funext fun y => Finset.sum_empty
          rw [hfun]
          exact H1 _ 0
        | insert a S ha ih' =>
          have hfun : (fun y => ∑ s ∈ insert a S, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) =
              fun y => Λ a (fderiv ℝ w y (EuclideanSpace.single a (1 : ℝ))) +
                ∑ s ∈ S, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ))) :=
            funext fun y => Finset.sum_insert ha
          rw [hfun]
          have hva : ContDiffOn ℝ ↑(n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single a (1 : ℝ))) Ω ∧
              ∀ x ∈ Ω, ∃ ρ : ℝ, 0 < ρ ∧ ball x ρ ⊆ Ω ∧ ∃ C : ℝ, ∀ y ∈ ball x ρ, ∀ z ∈ ball x ρ,
                ‖iteratedFDeriv ℝ (n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single a (1 : ℝ))) y -
                  iteratedFDeriv ℝ (n + 1) (fun y => fderiv ℝ w y (EuclideanSpace.single a (1 : ℝ))) z‖ ≤
                    C * ‖y - z‖ ^ α :=
            ⟨by rw [Nat.cast_succ]; exact (hvs a).1, (hvs a).2⟩
          exact H2 _ _ _ (H4 _ _ _ _ (Λ a).contDiff hva) ih'
      have hfun : (fun y => ∑ s : Fin m, Λ s (fderiv ℝ w y (EuclideanSpace.single s (1 : ℝ)))) =
          fun y => fderiv ℝ w y := funext fun y => (hΛ (fderiv ℝ w y)).symm
      have hDwH := hsum Finset.univ
      rw [hfun] at hDwH
      exact (H6 _ w hw).mpr hDwH

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
