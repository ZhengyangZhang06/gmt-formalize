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

/-- **Simon 7.3.1** (proof of (2), local retraction onto `N`, chart step): if `W` is open, `ψ` is
continuous and injective on `V`, `ψ(V) = W ∩ N` and `ψ` is proper over `W` (`V ∩ ψ⁻¹(K)` is
compact for compact `K ⊆ W`), then `N ∩ B_ρ(ψ(v₀)) ⊆ ψ(V₀)` for some `ρ > 0`, whenever `V₀ ⊆ V`
is open and `v₀ ∈ V₀`.  Otherwise there are `yᵢ = ψ(fᵢ) ∈ N` with `fᵢ ∈ V \ V₀` and
`yᵢ → ψ(v₀)`; the `fᵢ` lie in the compact set `V ∩ ψ⁻¹({ψ(v₀)} ∪ {yᵢ})`, so a subsequence
converges to some `a ∈ V \ V₀` with `ψ(a) = ψ(v₀)`, contradicting injectivity. -/
theorem Submission.dtc_bc_lr_chart_image_nhds : ∀ (P d : ℕ) (N W : Set (Euclid P)) (V V₀ : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v₀ : Euclid d), IsOpen W → ContinuousOn ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → IsOpen V₀ → V₀ ⊆ V → v₀ ∈ V₀ → ∃ ρ : ℝ, 0 < ρ ∧ N ∩ ball (ψ v₀) ρ ⊆ ψ '' V₀ := by
  intro P d N W V V₀ ψ v₀ hW hψc hψi hψV hprop hV₀ hV₀V hv₀
  -- Step 1: `x := ψ v₀ ∈ W` and `B_{r_W}(x) ⊆ W`
  have hv₀V : v₀ ∈ V := hV₀V hv₀
  have hxW : ψ v₀ ∈ W := (hψV ▸ mem_image_of_mem ψ hv₀V : ψ v₀ ∈ W ∩ N).1
  obtain ⟨rW, hrW, hballW⟩ := Metric.isOpen_iff.1 hW _ hxW
  -- Step 2: otherwise pick `yᵢ ∈ N ∩ B_{min(r_W, 1/(i+1))}(x) \ ψ(V₀)`, so `yᵢ ∈ W` and `yᵢ → x`
  by_contra hcon
  have hseq : ∀ i : ℕ, ∃ y, y ∈ N ∧ dist y (ψ v₀) < min rW (1 / ((i : ℝ) + 1)) ∧ y ∉ ψ '' V₀ := by
    intro i
    obtain ⟨y, ⟨hyN, hyb⟩, hy⟩ := not_subset.1 fun h =>
      hcon ⟨min rW (1 / ((i : ℝ) + 1)), lt_min hrW (by positivity), h⟩
    exact ⟨y, hyN, hyb, hy⟩
  choose y hyN hyd hyV₀ using hseq
  have hyW : ∀ i, y i ∈ W := fun i => hballW ((hyd i).trans_le (min_le_left _ _))
  have hylim : Tendsto y atTop (𝓝 (ψ v₀)) :=
    tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun i => dist_nonneg)
      (fun i => ((hyd i).trans_le (min_le_right _ _)).le) tendsto_one_div_add_atTop_nhds_zero_nat)
  -- Step 3: `yᵢ = ψ(fᵢ)` with `fᵢ ∈ V \ V₀`
  have hf : ∀ i, ∃ f, f ∈ V ∧ ψ f = y i := fun i => (hψV.symm ▸ ⟨hyW i, hyN i⟩ : y i ∈ ψ '' V)
  choose f hfV hfy using hf
  have hfV₀ : ∀ i, f i ∉ V₀ := fun i hi => hyV₀ i ⟨f i, hi, hfy i⟩
  -- Step 4: `K := {x} ∪ {yᵢ}` is a compact subset of `W`, so `V ∩ ψ⁻¹(K) ∋ fᵢ` is compact
  have hKW : insert (ψ v₀) (range y) ⊆ W := by
    rintro z (rfl | ⟨i, rfl⟩)
    exacts [hxW, hyW i]
  have hfK : ∀ i, f i ∈ V ∩ ψ ⁻¹' insert (ψ v₀) (range y) := fun i =>
    ⟨hfV i, Or.inr ⟨i, (hfy i).symm⟩⟩
  -- Step 5: a subsequence `f_{φ(i)} → a ∈ V`
  obtain ⟨a, ⟨haV, -⟩, φ, hφ, hfa⟩ :=
    (hprop _ hKW hylim.isCompact_insert_range).tendsto_subseq hfK
  -- Step 6: `a ∉ V₀`, as `V₀ᶜ` is closed
  have haV₀ : a ∉ V₀ :=
    hV₀.isClosed_compl.mem_of_tendsto hfa (Eventually.of_forall fun i => hfV₀ (φ i))
  -- Step 7: `ψ(a) = x` by continuity of `ψ` on `V` and uniqueness of limits
  have h₁ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ a)) :=
    (hψc a haV).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hfa, Eventually.of_forall fun i => hfV (φ i)⟩)
  have h₂ : Tendsto (ψ ∘ (f ∘ φ)) atTop (𝓝 (ψ v₀)) := by
    have hcomp : ψ ∘ (f ∘ φ) = y ∘ φ := funext fun i => hfy (φ i)
    rw [hcomp]
    exact hylim.comp hφ.tendsto_atTop
  -- Step 8: injectivity gives `a = v₀ ∈ V₀`, a contradiction
  exact haV₀ (hψi haV hv₀V (tendsto_nhds_unique h₁ h₂) ▸ hv₀)
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
/-- **Simon Ch. 2, §4, (4.3)**: if `ψ : V → W` is a local representation of `N` as in (4.1)
(`Cʳ`, `r ≥ 1`, 1:1 and proper, `ψ(V) = W ∩ N`, `Dψ` injective), then
`T_{ψ(v)}N = Dψ(v)(ℝᵈ)` for every `v ∈ V`.  `Dψ(v)(ℝᵈ) ⊆ T_{ψ(v)}N` because `ψ(V) ⊆ N`.
Conversely, properness and injectivity make `ψ⁻¹` continuous at `ψ(v)` on `ψ(V)`; with `Dψ(v)`
injective this gives, for each `ε > 0`, some `a` with `|y − ψ(v) − Dψ(v)a| ≤ ε|y − ψ(v)|` for all
`y ∈ N` near `ψ(v)`, so the difference quotients of a `C¹` curve in `N` through `ψ(v)` converge
into the closed subspace `Dψ(v)(ℝᵈ)`. -/
theorem Submission.chart_tangentSpace_eq_range_fderiv : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (v : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → (∀ z ∈ V, Injective (fderiv ℝ ψ z)) → v ∈ V → tangentSpace N (ψ v) = Set.range (fderiv ℝ ψ v) := by
  intro P d r N W V ψ v hr hV hW hψ hinj hψV hproper hDψ hv
  -- `ψ` is `C¹` on the open set `V`, hence differentiable at `v` with derivative `Dψ(v)`
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv : HasFDerivAt ψ (fderiv ℝ ψ v) v :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv)).hasFDerivAt
  -- `ψ(V) = W ∩ N` lies in `W` and in `N`
  have hVW : ψ '' V ⊆ W := hψV ▸ inter_subset_left
  have hVN : ψ '' V ⊆ N := hψV ▸ inter_subset_right
  -- `ψ⁻¹` is continuous at `ψ(v)` on `ψ(V)`
  have hinv := Submission.dsmc_chart_inverse_continuity P d V W ψ hψ.continuousOn hinj hVW
    hproper v hv
  refine Subset.antisymm ?_
    (Submission.dsmc_chart_range_subset_tangentSpace P r d N V ψ hr hV hψ hVN v hv)
  -- `T_{ψ(v)}N ⊆ Dψ(v)(ℝᵈ)`, from the secant estimate at `ψ(v)`
  exact Submission.dsmc_tangentSpace_subset_range_of_secant P d N (ψ v) (fderiv ℝ ψ v)
    (Submission.dsmc_chart_secant_estimate P d N V W ψ (fderiv ℝ ψ v) v hW hψV hv hψv
      (hDψ v hv) hinv)
/-- **Tangent space of a hypersurface in an `(m + 1)`-plane** (Simon Ch. 2, §4, (4.3), and
Appendix B, p. 231: `T_xM` and the unit normal `ν(x)` together span the ambient space).  Let
`M ⊆ A₀` be an embedded `C¹` `m`-submanifold, `dim A₀ = m + 1`, and let `ν(x) ∈ A₀` be a unit
vector orthogonal to `T_xM`.  Then `T_xM = A₀ ∩ ν(x)ᗮ`, and the orthogonal projection onto
`T_xM` is `w ↦ Π_{A₀}w − (ν(x)·w)ν(x)`.  A chart `ψ` with `ψ(v₀) = x` gives
`T_xM = Dψ(v₀)(ℝᵐ)`, of dimension `m`.  Difference quotients of curves in `M ⊆ A₀` lie in the
closed subspace `A₀`, so `T_xM ⊆ A₀ ∩ ν(x)ᗮ`, which has dimension `(m + 1) − 1 = m`; hence
equality.  Finally `u = Π_{A₀}w − (ν(x)·w)ν(x)` lies in `A₀ ∩ ν(x)ᗮ` and `w − u` is orthogonal
to it. -/
theorem Submission.codim1_hcp_sc_tangent_normal_complement : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → IsEmbeddedSubmanifold 1 m M → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, tangentSpace M x = {v : Euclid P | v ∈ A₀ ∧ inner ℝ (ν x) v = 0} ∧ ∀ w : Euclid P, (Submodule.span ℝ (tangentSpace M x)).starProjection w = A₀.starProjection w - inner ℝ (ν x) w • ν x := by
  intro P m A₀ M ν hdim hMA hM hν x hx
  obtain ⟨hνA, hν1, hνT⟩ := hν x hx
  -- Step 1: a chart `ψ` at `x = ψ(v₀)` gives `T_xM = Dψ(v₀)(ℝᵐ)`, a subspace of dimension `m`
  obtain ⟨V, W, ψ, hV, hW, hxW, hψ, hinj, hψV, hprop, hDψ⟩ := hM x hx
  obtain ⟨v₀, hv₀, hψv₀⟩ : x ∈ ψ '' V := hψV ▸ ⟨hxW, hx⟩
  set L : Submodule ℝ (Euclid P) :=
    LinearMap.range ((fderiv ℝ ψ v₀ : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) with hL
  have hT : tangentSpace M x = (L : Set (Euclid P)) := by
    rw [← hψv₀]
    exact Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W V ψ v₀ le_rfl hV hW hψ hinj
      hψV hprop hDψ hv₀
  have hLdim : Module.finrank ℝ L = m := by
    rw [hL, LinearMap.finrank_range_of_inj (hDψ v₀ hv₀), finrank_euclideanSpace_fin]
  -- Step 2: `T_xM ⊆ A₀`, as difference quotients of curves in `M ⊆ A₀` lie in the closed `A₀`
  have hTA : ∀ v ∈ tangentSpace M x, v ∈ A₀ := by
    rintro v ⟨γ, -, hγM, hγ0, hγv⟩
    refine A₀.closed_of_finiteDimensional.mem_of_tendsto hγv.tendsto_slope ?_
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1))] with t ht
    rw [slope_def_module]
    exact A₀.smul_mem _ (A₀.sub_mem (hMA (hγM ht)) (hγ0 ▸ hMA hx))
  -- Step 3: `T_xM ⊆ H = A₀ ∩ ν(x)ᗮ`
  set H : Submodule ℝ (Euclid P) := (ℝ ∙ ν x)ᗮ ⊓ A₀ with hH
  have hmemH : ∀ v, v ∈ H ↔ v ∈ A₀ ∧ inner ℝ (ν x) v = 0 := fun v => by
    rw [hH, Submodule.mem_inf, Submodule.mem_orthogonal_singleton_iff_inner_right, and_comm]
  have hLH : L ≤ H := fun v hv => by
    have hvT : v ∈ tangentSpace M x := hT ▸ hv
    exact (hmemH v).2 ⟨hTA v hvT, hνT v hvT⟩
  -- Step 4: `dim H = (m + 1) - 1 = m`, since `ν(x) ∈ A₀` is a unit vector
  have hν0 : ν x ≠ 0 := by
    rintro h
    rw [h, norm_zero] at hν1
    exact zero_ne_one hν1
  have hHdim : Module.finrank ℝ H = m := by
    have h : Module.finrank ℝ (ℝ ∙ ν x) + Module.finrank ℝ H = Module.finrank ℝ A₀ :=
      Submodule.finrank_add_inf_finrank_orthogonal
        ((Submodule.span_singleton_le_iff_mem (ν x) A₀).2 hνA)
    rw [finrank_span_singleton hν0, hdim] at h
    omega
  -- Step 5: `T_xM = H`
  have hLeq : L = H := Submodule.eq_of_le_of_finrank_eq hLH (hLdim.trans hHdim.symm)
  have hspan : Submodule.span ℝ (tangentSpace M x) = H := by
    rw [hT, Submodule.span_eq, hLeq]
  refine ⟨?_, fun w => ?_⟩
  · rw [hT, hLeq]
    ext v
    exact hmemH v
  -- Step 6: `u = Πw - ⟪ν(x), w⟫ν(x)` lies in `H` and `w - u ⊥ H`
  · have hPν : inner ℝ (ν x) (A₀.starProjection w) = inner ℝ (ν x) w := by
      rw [← Submodule.inner_starProjection_left_eq_right A₀,
        Submodule.starProjection_eq_self_iff.2 hνA]
    have hνν : inner ℝ (ν x) (ν x) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hν1, one_pow]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hspan, hmemH]
      refine ⟨A₀.sub_mem (A₀.starProjection_apply_mem w) (A₀.smul_mem _ hνA), ?_⟩
      rw [inner_sub_right, real_inner_smul_right, hPν, hνν, mul_one, sub_self]
    · intro h hh
      rw [hspan, hmemH] at hh
      have h1 : inner ℝ (w - A₀.starProjection w) h = 0 :=
        Submodule.starProjection_inner_eq_zero w h hh.1
      rw [sub_sub_eq_add_sub, add_sub_right_comm, inner_add_left, h1, real_inner_smul_left, hh.2,
        mul_zero, zero_add]
/-- **`Cʳ` inverse function theorem with a `Cʳ` inverse on a neighbourhood** (Simon Ch. 2, 4.4;
smooth charts of the hypercone plane: `φ` maps an open `V₀ ∋ z₀` `Cʳ`-diffeomorphically onto an
open `O`).  If `φ : ℝᵈ → ℝᵈ` is `Cʳ` (`r ≥ 1`) on an open `V ∋ z₀` and `Dφ(z₀)` is injective,
there are open sets `V₀`, `O` with `z₀ ∈ V₀ ⊆ V` such that `φ : V₀ → O` is a bijection whose
inverse `χ` is `Cʳ` on `O`.  `Dφ` is continuous on `V`, so `V' = {z ∈ V : Dφ(z) injective}` is
open; the strict-derivative inverse function theorem gives an open partial homeomorphism `Φ = φ`
with `z₀ ∈ Φ.source`; take `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀` and
`χ = Φ.symm`, which is `Cʳ` at every `a ∈ O` because `Dφ(χ a)` is invertible. -/
theorem Submission.codim1_hcp_sc_local_inverse_cr : ∀ (d r : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), 1 ≤ r → IsOpen V → z₀ ∈ V → ContDiffOn ℝ r φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (χ : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ r χ O ∧ MapsTo χ O V₀ ∧ (∀ a ∈ O, φ (χ a) = a) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ χ (φ z) = z := by
  intro d r φ V z₀ hr hV hz₀ hφ hinj
  -- `r ≥ 1` as an exponent in `WithTop ℕ∞`: `1 ≤ r` and `r ≠ 0`
  have hr1 : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hr0 : (r : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hr
  -- step 1: `φ` is `Cʳ` and differentiable at every point of `V`, and `Dφ` is continuous on `V`
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV hr1
  have hdiff : ∀ z ∈ V, HasFDerivAt φ (fderiv ℝ φ z) z := fun z hz =>
    ((hφ.contDiffAt (hV.mem_nhds hz)).differentiableAt hr0).hasFDerivAt
  -- step 2: an injective endomorphism of `ℝᵈ` is a continuous linear equivalence
  have equivOf : ∀ L : Euclid d →L[ℝ] Euclid d, Injective L →
      ∃ E : Euclid d ≃L[ℝ] Euclid d, (E : Euclid d →L[ℝ] Euclid d) = L := by
    intro L hL
    have hsurj : Surjective L := LinearMap.injective_iff_surjective.mp hL
    exact ⟨(LinearEquiv.ofBijective (L : Euclid d →ₗ[ℝ] Euclid d)
      ⟨hL, hsurj⟩).toContinuousLinearEquiv, by ext; rfl⟩
  -- step 3: `V' = {z ∈ V : Dφ(z) injective}` is open and contains `z₀`
  set V' := V ∩ (fderiv ℝ φ) ⁻¹' {L | Injective L}
  have hV' : IsOpen V' := hcont.isOpen_inter_preimage hV ContinuousLinearMap.isOpen_injective
  have hz₀' : z₀ ∈ V' := ⟨hz₀, hinj⟩
  -- step 4: the inverse function theorem at `z₀` gives `Φ = φ` with `z₀ ∈ Φ.source`
  obtain ⟨E₀, hE₀⟩ := equivOf _ hinj
  have hstrict : HasStrictFDerivAt φ (E₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hE₀]; exact (hφ.contDiffAt (hV.mem_nhds hz₀)).hasStrictFDerivAt hr0
  set Φ := hstrict.toOpenPartialHomeomorph φ
  have hΦcoe : ∀ z, Φ z = φ z := fun z => rfl
  -- step 5: `V₀ = Φ.source ∩ V'`, `O = Φ.target ∩ Φ.symm ⁻¹' V₀`, `χ = Φ.symm`; for `a ∈ O`,
  -- `χ a ∈ V₀` and `φ (χ a) = a`
  have hV₀ : IsOpen (Φ.source ∩ V') := Φ.open_source.inter hV'
  refine ⟨Φ.source ∩ V', Φ.target ∩ Φ.symm ⁻¹' (Φ.source ∩ V'), Φ.symm, hV₀,
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV₀,
    ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀'⟩, fun z hz => hz.2.1, ?_,
    fun a ha => ha.2, fun a ha => by rw [← hΦcoe]; exact Φ.right_inv ha.1, fun z hz => ?_⟩
  -- step 7: `χ` is `Cʳ` at every `a ∈ O`, since `Dφ(χ a)` is invertible and `φ` is `Cʳ` at `χ a`
  · intro a ha
    have hz : Φ.symm a ∈ V' := ha.2.2
    obtain ⟨E, hE⟩ := equivOf _ hz.2
    apply ContDiffAt.contDiffWithinAt
    apply Φ.contDiffAt_symm ha.1
    · rw [hE]; exact hdiff _ hz.1
    · exact hφ.contDiffAt (hV.mem_nhds hz.1)
  -- step 6: for `z ∈ V₀`, `φ z ∈ O` and `χ (φ z) = z`
  · have h1 : Φ.symm (Φ z) = z := Φ.left_inv hz.1
    rw [← hΦcoe]
    exact ⟨⟨Φ.map_source hz.1, by rw [Set.mem_preimage, h1]; exact hz⟩, h1⟩
/-- **A linear left inverse makes a map an injective immersion** (Simon Ch. 2, §4, (4.4), where
the graph map `G(x) = (x, u(x))` has the linear left inverse `(x, y) ↦ x`; step 4 of the `C^∞`
chart construction for the hypercone plane).  Let `D ⊆ ℝᵈ` be open, `g` differentiable on `D`,
and `π : ℝᴾ → ℝᵈ` continuous linear with `π(g(a) − c) = a` for `a ∈ D`.  Then `g` is injective
on `D`, since `a = π(g(a) − c) = π(g(b) − c) = b`.  For `a ∈ D` the map `b ↦ π(g(b) − c)` has
derivative `π ∘ Dg(a)` at `a` by the chain rule, and it agrees with the identity on the
neighbourhood `D` of `a`; uniqueness of the derivative gives `π ∘ Dg(a) = id`, so `π` is a left
inverse of `Dg(a)` and `Dg(a)` is injective. -/
theorem Submission.codim1_hcp_sc_left_inverse_immersion : ∀ (P d : ℕ) (D : Set (Euclid d)) (g : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), IsOpen D → DifferentiableOn ℝ g D → (∀ a ∈ D, π (g a - c) = a) → InjOn g D ∧ ∀ a ∈ D, π ∘L fderiv ℝ g a = ContinuousLinearMap.id ℝ (Euclid d) ∧ Injective (fderiv ℝ g a) := by
  intro P d D g π c hD hg hπ
  -- Steps 2–3: `π ∘ Dg(a) = id` for every `a ∈ D`
  have hid : ∀ a ∈ D, π ∘L fderiv ℝ g a = ContinuousLinearMap.id ℝ (Euclid d) := by
    intro a ha
    -- chain rule: `b ↦ π(g(b) − c)` has derivative `π ∘ Dg(a)` at `a`
    have h₁ : HasFDerivAt (fun b => π (g b - c)) (π ∘L fderiv ℝ g a) a :=
      π.hasFDerivAt.comp a ((hg.hasFDerivAt (hD.mem_nhds ha)).sub_const c)
    -- it equals the identity on the neighbourhood `D` of `a`, so it also has derivative `id`
    have h₂ : HasFDerivAt (fun b => π (g b - c)) (ContinuousLinearMap.id ℝ (Euclid d)) a :=
      (hasFDerivAt_id a).congr_of_eventuallyEq (eventually_of_mem (hD.mem_nhds ha) hπ)
    -- uniqueness of the Fréchet derivative
    exact h₁.unique h₂
  refine ⟨fun a ha b hb hab => ?_, fun a ha => ⟨hid a ha, ?_⟩⟩
  · -- Step 1: `a = π(g(a) − c) = π(g(b) − c) = b`
    rw [← hπ a ha, hab, hπ b hb]
  · -- Step 4: `π(Dg(a) u) = u`, so `π` is a left inverse of `Dg(a)`
    exact LeftInverse.injective fun u => DFunLike.congr_fun (hid a ha) u

/-- **Simon Ch. 2, §4, Remark 4.4** (local graphical representation, using (4.2)): let `ψ` be
`Cʳ` (`r ≥ 1`), 1:1 and proper on the open set `V` with `ψ(V) = W ∩ N`, and let `π` be
continuous linear with `π ∘ Dψ(v₀)` injective.  Then `φ = π(ψ − c)` has `Dφ(v₀) = π ∘ Dψ(v₀)`,
so the inverse function theorem gives a `Cʳ` inverse `χ : D → S` of `φ` with `v₀ ∈ S ⊆ V`, and
`g = ψ ∘ χ` is `Cʳ` on `D` with `π(g(a) − c) = a` and `g(D) = ψ(S)`.  As `ψ` is open onto its
image (4.2), `ψ(S) = O ∩ N` for the open set `O = W ∩ ⋃_{v ∈ S} B_{ρ_v}(ψ(v))`.  The left
inverse `π(· − c)` makes `g` and every `Dg(a)` injective, and for compact `K ⊆ O`,
`D ∩ g⁻¹(K) = π((N ∩ K) − c)`, where `N ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact. -/
theorem Submission.codim1_hcp_sc_graph_reparam : ∀ (P d r : ℕ) (N W : Set (Euclid P)) (V : Set (Euclid d)) (ψ : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P) (v₀ : Euclid d), 1 ≤ r → IsOpen V → IsOpen W → ContDiffOn ℝ r ψ V → InjOn ψ V → ψ '' V = W ∩ N → (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) → v₀ ∈ V → Injective (π ∘L fderiv ℝ ψ v₀) → ∃ (D : Set (Euclid d)) (O : Set (Euclid P)) (g : Euclid d → Euclid P), IsOpen D ∧ IsOpen O ∧ ψ v₀ ∈ O ∧ O ⊆ W ∧ ContDiffOn ℝ r g D ∧ InjOn g D ∧ g '' D = O ∩ N ∧ (∀ K ⊆ O, IsCompact K → IsCompact (D ∩ g ⁻¹' K)) ∧ (∀ a ∈ D, Injective (fderiv ℝ g a)) ∧ ∀ a ∈ D, π (g a - c) = a := by
  intro P d r N W V ψ π c v₀ hr hV hW hψ hinj hψV hprop hv₀ hπψ
  have hψc : ContinuousOn ψ V := hψ.continuousOn
  have hψVWN : ∀ v ∈ V, ψ v ∈ W ∩ N := fun v hv => hψV ▸ mem_image_of_mem ψ hv
  -- Step 1: `φ = π(ψ − c)` is `Cʳ` on `V`, and `Dφ(v₀) = π ∘ Dψ(v₀)` is injective
  have hψ1 : ContDiffOn ℝ 1 ψ V := hψ.of_le (by exact_mod_cast hr)
  have hψv₀ : HasFDerivAt ψ (fderiv ℝ ψ v₀) v₀ :=
    ((hψ1.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hv₀)).hasFDerivAt
  have hφ : ContDiffOn ℝ r (fun v => π (ψ v - c)) V :=
    π.contDiff.comp_contDiffOn (hψ.sub contDiffOn_const)
  have hDφ : fderiv ℝ (fun v => π (ψ v - c)) v₀ = π ∘L fderiv ℝ ψ v₀ :=
    (π.hasFDerivAt.comp v₀ (hψv₀.sub_const c)).fderiv
  -- Step 2: a `Cʳ` local inverse `χ : D → S` of `φ` with `v₀ ∈ S ⊆ V`; then `χ(D) = S`
  obtain ⟨S, D, χ, hS, hD, hv₀S, hSV, hχ, hχD, hφχ, hχφ⟩ :=
    Submission.codim1_hcp_sc_local_inverse_cr d r (fun v => π (ψ v - c)) V v₀ hr hV hv₀ hφ
      (hDφ ▸ hπψ)
  have hχS : χ '' D = S :=
    Subset.antisymm hχD.image_subset fun z hz => ⟨_, (hχφ z hz).1, (hχφ z hz).2⟩
  -- Step 3: `g = ψ ∘ χ` is `Cʳ` on `D`, `π(g(a) − c) = a` on `D`, and `g(D) = ψ(S)`
  have hg : ContDiffOn ℝ r (ψ ∘ χ) D := hψ.comp hχ (hχD.mono_right hSV)
  have hgπ : ∀ a ∈ D, π ((ψ ∘ χ) a - c) = a := hφχ
  have hgD : (ψ ∘ χ) '' D = ψ '' S := by rw [image_comp, hχS]
  -- Step 4: `ψ(S) = O ∩ N` for the open set `O = W ∩ ⋃_{v ∈ S} B(ψ(v), ρ_v)` (Simon 4.2)
  choose ρ hρ hρS using fun v (hv : v ∈ S) =>
    Submission.dtc_bc_lr_chart_image_nhds P d N W V S ψ v hW hψc hinj hψV hprop hS hSV hv
  set O : Set (Euclid P) := W ∩ ⋃ (v) (hv : v ∈ S), ball (ψ v) (ρ v hv)
  have hO : IsOpen O := hW.inter (isOpen_iUnion fun v => isOpen_iUnion fun hv => isOpen_ball)
  have hψO : ∀ v (hv : v ∈ S), ψ v ∈ O := fun v hv =>
    ⟨(hψVWN v (hSV hv)).1, mem_iUnion₂.2 ⟨v, hv, mem_ball_self (hρ v hv)⟩⟩
  have hSO : ψ '' S = O ∩ N := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨hψO v hv, (hψVWN v (hSV hv)).2⟩
    · rintro x ⟨⟨-, hx⟩, hxN⟩
      obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 hx
      exact hρS v hv ⟨hxN, hxv⟩
  -- Step 5: `g` and every `Dg(a)` are injective, as `π(· − c)` is a left inverse of `g`
  have hg1 : ContDiffOn ℝ 1 (ψ ∘ χ) D := hg.of_le (by exact_mod_cast hr)
  obtain ⟨hginj, hDg⟩ := Submission.codim1_hcp_sc_left_inverse_immersion P d D (ψ ∘ χ) π c hD
    (hg1.differentiableOn one_ne_zero) hgπ
  refine ⟨D, O, ψ ∘ χ, hD, hO, hψO v₀ hv₀S, inter_subset_left, hg, hginj, hgD.trans hSO,
    fun K hKO hK => ?_, fun a ha => (hDg a ha).2, hgπ⟩
  -- Step 6: `N ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have hKW : K ⊆ W := hKO.trans inter_subset_left
  have hNK : N ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨hxN, hxK⟩
      obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := hψV ▸ ⟨hKW hxK, hxN⟩
      exact ⟨v, ⟨hv, hxK⟩, rfl⟩
    · rintro _ ⟨v, ⟨hv, hvK⟩, rfl⟩
      exact ⟨(hψVWN v hv).2, hvK⟩
  have hNKc : IsCompact (N ∩ K) := by
    rw [hNK]
    exact (hprop K hKW hK).image_of_continuousOn (hψc.mono inter_subset_left)
  -- Step 7: `D ∩ g⁻¹(K) = p(N ∩ K)` with `p(x) = π(x − c)` continuous, so it is compact
  have hDK : D ∩ (ψ ∘ χ) ⁻¹' K = (fun x => π (x - c)) '' (N ∩ K) := by
    refine Subset.antisymm ?_ ?_
    · rintro a ⟨ha, haK⟩
      have haN : (ψ ∘ χ) a ∈ O ∩ N := hgD.trans hSO ▸ mem_image_of_mem (ψ ∘ χ) ha
      exact ⟨(ψ ∘ χ) a, ⟨haN.2, haK⟩, hgπ a ha⟩
    · rintro _ ⟨x, ⟨hxN, hxK⟩, rfl⟩
      obtain ⟨b, hb, rfl⟩ : x ∈ (ψ ∘ χ) '' D := hgD.trans hSO ▸ ⟨hKO hxK, hxN⟩
      show π ((ψ ∘ χ) b - c) ∈ D ∩ (ψ ∘ χ) ⁻¹' K
      rw [hgπ b hb]
      exact ⟨hb, hxK⟩
  rw [hDK]
  exact hNKc.image (π.continuous.comp (continuous_sub_right c))

/-- **Simon Ch. 2, §4, (4.1)–(4.4)**: a `C¹` local representation `G : D → W₀` of an embedded
`Cʳ` submanifold `M` (`r ≥ 1`; 1:1, proper, `G(D) = W₀ ∩ M`, `DG` injective) which is a graph
over the projection `π`, `π(G(a) − c) = a`, is `Cʳ` on `D`.  At `a₀ ∈ D`, `x₀ = G(a₀)`, take a
`Cʳ` chart `ψ'` of `M` with `ψ'(v₀) = x₀`.  By (4.3), `Dψ'(v₀)(ℝᵈ) = T_{x₀}M = DG(a₀)(ℝᵈ)`, and
`π ∘ DG(a₀) = id`, so `π ∘ Dψ'(v₀)` is injective.  Re-parametrizing `ψ'` over `π` gives a `Cʳ`
graph `g` on an open `U` with `g(U) = O ∩ M`, `x₀ ∈ O` and `π(g(a) − c) = a`; then `a₀ ∈ U`,
`g(a₀) = x₀`.  For `a` in the open set `U ∩ g⁻¹(W₀) ∋ a₀`, `g(a) ∈ W₀ ∩ M = G(D)`, and the
projection identity forces `G(a) = g(a)`, so `G` is `Cʳ` at `a₀`. -/
theorem Submission.codim1_hcp_sc_graph_contDiffOn : ∀ (P d r : ℕ) (M W₀ : Set (Euclid P)) (D : Set (Euclid d)) (G : Euclid d → Euclid P) (π : Euclid P →L[ℝ] Euclid d) (c : Euclid P), 1 ≤ r → IsEmbeddedSubmanifold r d M → IsOpen D → IsOpen W₀ → ContDiffOn ℝ 1 G D → InjOn G D → G '' D = W₀ ∩ M → (∀ K ⊆ W₀, IsCompact K → IsCompact (D ∩ G ⁻¹' K)) → (∀ a ∈ D, Injective (fderiv ℝ G a)) → (∀ a ∈ D, π (G a - c) = a) → ContDiffOn ℝ r G D := by
  intro P d r M W₀ D G π c hr hM hD hW₀ hG hGinj hGD hGproper hDG hπG a₀ ha₀
  -- it suffices that `G` is `Cʳ` at `a₀ ∈ D`; `x₀ = G(a₀) ∈ W₀ ∩ M`
  refine ContDiffAt.contDiffWithinAt ?_
  have hx₀ : G a₀ ∈ W₀ ∩ M := hGD ▸ mem_image_of_mem G ha₀
  -- a `Cʳ` chart `ψ'` of `M` at `x₀`, with `ψ'(v₀) = x₀`
  obtain ⟨V', W', ψ', hV', hW', hx₀W', hψ', hψ'inj, hψ'V', hψ'proper, hDψ'⟩ := hM (G a₀) hx₀.2
  obtain ⟨v₀, hv₀, hψv₀⟩ : G a₀ ∈ ψ' '' V' := hψ'V' ▸ ⟨hx₀W', hx₀.2⟩
  -- `Dψ'(v₀)(ℝᵈ) = T_{x₀}M = DG(a₀)(ℝᵈ)`, applying (4.3) to `ψ'` (`Cʳ`) and to `G` (`C¹`)
  have hrange : Set.range (fderiv ℝ ψ' v₀) = Set.range (fderiv ℝ G a₀) := by
    rw [← Submission.chart_tangentSpace_eq_range_fderiv P d r M W' V' ψ' v₀ hr hV' hW' hψ'
        hψ'inj hψ'V' hψ'proper hDψ' hv₀, hψv₀,
      Submission.chart_tangentSpace_eq_range_fderiv P d 1 M W₀ D G a₀ le_rfl hD hW₀
        (by exact_mod_cast hG) hGinj hGD hGproper hDG ha₀]
  -- `π ∘ DG(a₀) = id`
  have hπDG : ∀ w, π (fderiv ℝ G a₀ w) = w := fun w => by
    simpa using DFunLike.congr_fun ((Submission.codim1_hcp_sc_left_inverse_immersion P d D G π c
      hD hG.differentiableOn_one hπG).2 a₀ ha₀).1 w
  -- `π ∘ Dψ'(v₀)` is injective: if `π(Dψ'(v₀)u) = 0`, write `Dψ'(v₀)u = DG(a₀)w`; then
  -- `w = π(DG(a₀)w) = 0`, so `Dψ'(v₀)u = 0` and `u = 0`
  have hπDψ' : Injective (π ∘L fderiv ℝ ψ' v₀) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu => hDψ' v₀ hv₀ ?_
    obtain ⟨w, hw⟩ : fderiv ℝ ψ' v₀ u ∈ Set.range (fderiv ℝ G a₀) :=
      hrange ▸ Set.mem_range_self u
    have hw0 : w = 0 := by
      rw [← hπDG w, hw]
      simpa using hu
    rw [map_zero, ← hw, hw0, map_zero]
  -- re-parametrize `ψ'` as a `Cʳ` graph `g` over `π` on `U`, with `g(U) = O ∩ M` and `x₀ ∈ O`
  obtain ⟨U, O, g, hU, -, hx₀O, -, hg, -, hgU, -, -, hπg⟩ :=
    Submission.codim1_hcp_sc_graph_reparam P d r M W' V' ψ' π c v₀ hr hV' hW' hψ' hψ'inj hψ'V'
      hψ'proper hv₀ hπDψ'
  -- `x₀ = g(a₁)` with `a₁ ∈ U`, and `a₁ = π(g(a₁) − c) = π(G(a₀) − c) = a₀`
  rw [hψv₀] at hx₀O
  obtain ⟨a₁, ha₁, hga₁⟩ : G a₀ ∈ g '' U := hgU ▸ ⟨hx₀O, hx₀.2⟩
  have ha₁₀ : a₁ = a₀ := by rw [← hπg a₁ ha₁, hga₁, hπG a₀ ha₀]
  rw [ha₁₀] at ha₁ hga₁
  -- `G = g` on the open set `U ∩ g⁻¹(W₀) ∋ a₀`: there `g(a) ∈ W₀ ∩ M = G(D)`, say `g(a) = G(a')`,
  -- and `a' = π(G(a') − c) = π(g(a) − c) = a`
  have hGg : G =ᶠ[𝓝 a₀] g := by
    have hUg : IsOpen (U ∩ g ⁻¹' W₀) := hg.continuousOn.isOpen_inter_preimage hU hW₀
    have ha₀Ug : a₀ ∈ U ∩ g ⁻¹' W₀ := ⟨ha₁, show g a₀ ∈ W₀ from hga₁ ▸ hx₀.1⟩
    filter_upwards [hUg.mem_nhds ha₀Ug] with a ha
    obtain ⟨haU, haW₀⟩ := ha
    have hgaM : g a ∈ O ∩ M := hgU ▸ mem_image_of_mem g haU
    obtain ⟨a', ha', hGa'⟩ : g a ∈ G '' D := hGD ▸ ⟨haW₀, hgaM.2⟩
    have ha'a : a' = a := by rw [← hπG a' ha', hGa', hπg a haU]
    rw [← hGa', ha'a]
  -- `g` is `Cʳ` at `a₀` (`U` is open), and `G = g` near `a₀`
  exact (hg.contDiffAt (hU.mem_nhds ha₁)).congr_of_eventuallyEq hGg

/-- **`C^∞` charts** (Simon Ch. 2, §4, 4.1–4.4): if `M ⊆ ℝᴾ` is an embedded `Cʳ` `m`-dimensional
submanifold for every `r` (the charts may depend on `r`), then every `y ∈ M` has a `C^∞` local
representation.  Take a `C¹` chart `ψ₁` with `ψ₁(v_y) = y` and a continuous linear left inverse
`π` of the injective `Dψ₁(v_y)`.  Re-parametrizing `ψ₁` over `π` gives a `C¹` chart
`G : D → W₀ ∩ M` with `π(G(a) − y) = a`, and such a graph chart of the `C^{n+1}` submanifold `M`
is `C^{n+1}` on `D`.  So `G` is `Cⁿ` on `D` for every `n`, i.e. `C^∞`. -/
theorem Submission.codim1_hcp_smooth_charts : ∀ (P m : ℕ) (M : Set (Euclid P)), (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → ∀ y ∈ M, ∃ (V : Set (Euclid m)) (W : Set (Euclid P)) (ψ : Euclid m → Euclid P), IsOpen V ∧ IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ (⊤ : ℕ∞) ψ V ∧ InjOn ψ V ∧ ψ '' V = W ∩ M ∧ (∀ K ⊆ W, IsCompact K → IsCompact (V ∩ ψ ⁻¹' K)) ∧ ∀ z ∈ V, Injective (fderiv ℝ ψ z) := by
  intro P m M hM y hy
  -- Step 1: a `C¹` chart `(V₁, W₁, ψ₁)` at `y`, and `v_y ∈ V₁` with `ψ₁(v_y) = y`
  obtain ⟨V₁, W₁, ψ₁, hV₁, hW₁, hyW₁, hψ₁, hinj₁, hψ₁V, hprop₁, hD₁⟩ := hM 1 y hy
  obtain ⟨vy, hvy, hψvy⟩ : y ∈ ψ₁ '' V₁ := hψ₁V ▸ ⟨hyW₁, hy⟩
  -- Step 2: a continuous linear left inverse `π` of the injective `Dψ₁(v_y)`
  obtain ⟨π₀, hπ₀⟩ := (fderiv ℝ ψ₁ vy : Euclid m →ₗ[ℝ] Euclid P).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (hD₁ vy hvy))
  set π : Euclid P →L[ℝ] Euclid m := LinearMap.toContinuousLinearMap π₀
  have hπA : π ∘L fderiv ℝ ψ₁ vy = ContinuousLinearMap.id ℝ (Euclid m) :=
    ContinuousLinearMap.ext fun v => LinearMap.congr_fun hπ₀ v
  have hπ : Injective (π ∘L fderiv ℝ ψ₁ vy) := by
    rw [hπA]
    exact fun a b hab => hab
  -- Step 3: the `C¹` graph chart `G : D → W₀ ∩ M` over `π`, with `π(G(a) − y) = a`
  obtain ⟨D, W₀, G, hD, hW₀, hyW₀, -, hG, hGinj, hGD, hGprop, hDG, hπG⟩ :=
    Submission.codim1_hcp_sc_graph_reparam P m 1 M W₁ V₁ ψ₁ π y vy le_rfl hV₁ hW₁ hψ₁ hinj₁ hψ₁V
      hprop₁ hvy hπ
  -- Step 4: `G` is `C^{n+1}` on `D` for every `n` (`M` is `C^{n+1}`), hence `C^∞`
  have hG1 : ContDiffOn ℝ 1 G D := by exact_mod_cast hG
  have hGsmooth : ContDiffOn ℝ (⊤ : ℕ∞) G D := contDiffOn_infty.2 fun n =>
    (Submission.codim1_hcp_sc_graph_contDiffOn P m (n + 1) M W₀ D G π y (Nat.le_add_left 1 n)
      (hM (n + 1)) hD hW₀ hG1 hGinj hGD hGprop hDG hπG).of_le (by exact_mod_cast Nat.le_succ n)
  exact ⟨D, W₀, G, hD, hW₀, hψvy ▸ hyW₀, hGsmooth, hGinj, hGD, hGprop, hDG⟩
/-- Step 6 of the oriented graph chart (zero-scale limit plane, Simon 7.5.8): the inverse function
theorem with a `C¹` local inverse on an open target (as used in Simon Ch. 2, §4).  If `φ` is `C¹`
on an open `V ∋ z₀` and `Dφ(z₀)` is injective, then `Dφ(z₀)` is invertible, so
`V₁ = V ∩ {z : Dφ(z) invertible}` is an open neighbourhood of `z₀`.  The inverse function theorem
restricted to `V₁` gives `φ : V₀ → O` bijective with inverse `χ`, and `χ` is `C¹` at every
`a ∈ O` because `Dφ(χ(a))` is invertible. -/
theorem Submission.codim1_zsl_gc_local_inverse : ∀ (d : ℕ) (φ : Euclid d → Euclid d) (V : Set (Euclid d)) (z₀ : Euclid d), IsOpen V → z₀ ∈ V → ContDiffOn ℝ 1 φ V → Injective (fderiv ℝ φ z₀) → ∃ (V₀ O : Set (Euclid d)) (χ : Euclid d → Euclid d), IsOpen V₀ ∧ IsOpen O ∧ z₀ ∈ V₀ ∧ V₀ ⊆ V ∧ ContDiffOn ℝ 1 χ O ∧ MapsTo χ O V₀ ∧ (∀ a ∈ O, φ (χ a) = a) ∧ ∀ z ∈ V₀, φ z ∈ O ∧ χ (φ z) = z := by
  intro d φ V z₀ hV hz₀ hφ hinj
  -- `Dφ(z₀)` is invertible (injective endomorphism of a finite-dimensional space)
  let L₀ : Euclid d ≃L[ℝ] Euclid d :=
    (LinearEquiv.ofInjectiveEndo
      ((fderiv ℝ φ z₀ : Euclid d →L[ℝ] Euclid d) : Euclid d →ₗ[ℝ] Euclid d)
      hinj).toContinuousLinearEquiv
  have hL₀ : (L₀ : Euclid d →L[ℝ] Euclid d) = fderiv ℝ φ z₀ := by
    ext x; rfl
  have hcd : ∀ z ∈ V, ContDiffAt ℝ 1 φ z := fun z hz => hφ.contDiffAt (hV.mem_nhds hz)
  have hcont : ContinuousOn (fderiv ℝ φ) V := hφ.continuousOn_fderiv_of_isOpen hV le_rfl
  -- the open set `V₁` where `Dφ` is invertible
  let V₁ : Set (Euclid d) :=
    V ∩ fderiv ℝ φ ⁻¹' range ((↑) : (Euclid d ≃L[ℝ] Euclid d) → Euclid d →L[ℝ] Euclid d)
  have hV₁ : IsOpen V₁ := hcont.isOpen_inter_preimage hV ContinuousLinearEquiv.isOpen
  have hz₀V₁ : z₀ ∈ V₁ := ⟨hz₀, L₀, hL₀⟩
  have hstrict : HasStrictFDerivAt φ (L₀ : Euclid d →L[ℝ] Euclid d) z₀ := by
    rw [hL₀]
    exact (hcd z₀ hz₀).hasStrictFDerivAt one_ne_zero
  -- the inverse function theorem, restricted to `V₁`
  obtain ⟨e, he, hz₀e, hsrc⟩ : ∃ e : OpenPartialHomeomorph (Euclid d) (Euclid d),
      ⇑e = φ ∧ z₀ ∈ e.source ∧ e.source ⊆ V₁ :=
    ⟨(hstrict.toOpenPartialHomeomorph φ).restrOpen V₁ hV₁, rfl,
      ⟨hstrict.mem_toOpenPartialHomeomorph_source, hz₀V₁⟩, inter_subset_right⟩
  subst he
  refine ⟨e.source, e.target, e.symm, e.open_source, e.open_target, hz₀e,
    fun z hz => (hsrc hz).1, ?_, e.mapsTo_symm, fun a ha => e.right_inv ha,
    fun z hz => ⟨e.map_source hz, e.left_inv hz⟩⟩
  -- `χ = e.symm` is `C¹` at each `a ∈ O`, since `Dφ(χ(a))` is invertible
  intro a ha
  obtain ⟨hV', L, hL⟩ := hsrc (e.map_target ha)
  have hd : HasFDerivAt e (L : Euclid d →L[ℝ] Euclid d) (e.symm a) := by
    rw [hL]
    exact ((hcd _ hV').differentiableAt one_ne_zero).hasFDerivAt
  exact (e.contDiffAt_symm ha hd (hcd _ hV')).contDiffWithinAt
/-- An embedded `Cʳ` submanifold `M ⊆ ℝᴾ` (Simon Ch. 2, §4, (4.1)) is Borel, and it meets every
small closed ball about one of its points in a compact set.  For a chart `(V, W, ψ)` and a compact
`K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact because `ψ` is proper and continuous on `V`.  With `O`
the union of the chart domains `W`, `M = O ∩ closure M`: a point `p ∈ O ∩ closure M` lies in the
closure of the compact, hence closed, set `M ∩ closedBall p ε`.  So `M` is Borel. -/
theorem Submission.dimred_rpd_embedded_locally_closed : ∀ (P r d : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold r d M → MeasurableSet M ∧ ∀ y ∈ M, ∃ ε : ℝ, 0 < ε ∧ IsCompact (M ∩ closedBall y ε) := by
  intro P r d M hM
  -- step 1: for a chart `(V, W, ψ)` at `y` and compact `K ⊆ W`, `M ∩ K = ψ(V ∩ ψ⁻¹(K))` is compact
  have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
      ∀ K ⊆ W, IsCompact K → IsCompact (M ∩ K) := by
    intro y hy
    obtain ⟨V, W, ψ, -, hW, hyW, hψ, -, himg, hprop, -⟩ := hM y hy
    refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
    have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
      ext x
      constructor
      · rintro ⟨hxM, hxK⟩
        have hx : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
        obtain ⟨v, hv, rfl⟩ := hx
        exact ⟨v, ⟨hv, hxK⟩, rfl⟩
      · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
        have hv' : ψ v ∈ W ∩ M := by rw [← himg]; exact ⟨v, hv, rfl⟩
        exact ⟨hv'.2, hvK⟩
    rw [hEq]
    exact (hprop K hKW hK).image_of_continuousOn (hψ.continuousOn.mono inter_subset_left)
  refine ⟨?_, ?_⟩
  · -- steps 3-5: `O = ⋃_{y ∈ M} W_y` is open and `M = O ∩ closure M`, so `M` is Borel
    choose! Wf hWo hyW hcpt using key
    have hO : IsOpen (⋃ y ∈ M, Wf y) := isOpen_biUnion fun y hy => hWo y hy
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      apply Subset.antisymm
      · intro x hx
        exact ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩
      · -- `p ∈ O ∩ closure M` lies in the closure of the compact set `M ∩ closedBall p (r'/2)`
        rintro p ⟨hpO, hpcl⟩
        obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
        obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
        have hcb : closedBall p (r' / 2) ⊆ Wf y :=
          (closedBall_subset_ball (by linarith)).trans hball
        have hC := hcpt y hy (closedBall p (r' / 2)) hcb (isCompact_closedBall p (r' / 2))
        have h1 : p ∈ ball p (r' / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
        have h2 := isOpen_ball.inter_closure h1
        have hsub : ball p (r' / 2) ∩ M ⊆ M ∩ closedBall p (r' / 2) :=
          fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
        have h3 : p ∈ closure (M ∩ closedBall p (r' / 2)) := closure_mono hsub h2
        rw [hC.isClosed.closure_eq] at h3
        exact h3.1
    rw [hMeq]
    exact hO.measurableSet.inter isClosed_closure.measurableSet
  · -- step 2: a closed ball about `y` inside the chart domain `W` meets `M` in a compact set
    intro y hy
    obtain ⟨W, hW, hyW, hcpt⟩ := key y hy
    obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.1 hW y hyW
    exact ⟨r' / 2, by linarith,
      hcpt _ ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall y _)⟩
/-- **Graph chart of an embedded `C¹` submanifold** (Simon Ch. 2, §4, (4.4)).  Take a chart
`ψ : V → W₀` at `p = ψ(v₀)` and, in place of Simon's coordinate projection, `pr = ‖A‖⁻¹ A*`,
`A = Dψ(v₀)`, so `‖pr‖ ≤ 1` and `pr ∘ A` is injective.  The inverse function theorem for
`Φ = pr(ψ − p)` gives a `C¹` local inverse `χ` near `Φ(v₀) = 0`, and `G = ψ ∘ χ` satisfies
`pr(G(a) − p) = a`.  Continuity of `ψ⁻¹` at `p` and a small radius `r` give `M ∩ W = G(B_r(0))`
for `W = W₀ ∩ B_δ(p) ∩ {z : pr(z − p) ∈ B_r(0)}`; `DG` is bounded on `B̄_r(0)`, so `G` is
Lipschitz on `B_r(0)`.  Differentiating `pr(G(a) − p) = a` gives `pr ∘ DG(a) = id`, and `Dχ(a)`
is invertible, so `T_{G(a)}M = Dψ(χ(a))(ℝᵐ) = DG(a)(ℝᵐ)`. -/
theorem Submission.codim1_hcp_lsa_c1_graph_chart : ∀ (P m : ℕ) (M : Set (Euclid P)) (p : Euclid P), IsEmbeddedSubmanifold 1 m M → p ∈ M → ∃ (pr : Euclid P →L[ℝ] Euclid m) (G : Euclid m → Euclid P) (r : ℝ) (W : Set (Euclid P)) (Λ : NNReal), 0 < r ∧ IsOpen W ∧ p ∈ W ∧ ‖pr‖ ≤ 1 ∧ G 0 = p ∧ ContDiffOn ℝ 1 G (ball 0 r) ∧ LipschitzOnWith Λ G (ball 0 r) ∧ M ∩ W = G '' ball 0 r ∧ (∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a) ∧ (∀ a ∈ ball (0 : Euclid m) r, pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m)) ∧ ∀ a ∈ ball (0 : Euclid m) r, tangentSpace M (G a) = Set.range (fderiv ℝ G a) := by
  intro P m M p hM hp
  -- step 1: a chart `(V, W₀, ψ)` at `p = ψ(v₀)`
  obtain ⟨V, W₀, ψ, hVo, hW₀o, hpW₀, hψc, hψinj, hψV, hproper, hDψinj⟩ := hM p hp
  obtain ⟨v₀, hv₀, hψv₀⟩ : p ∈ ψ '' V := by rw [hψV]; exact ⟨hpW₀, hp⟩
  have hψd : ∀ v ∈ V, HasFDerivAt ψ (fderiv ℝ ψ v) v := fun v hv =>
    ((hψc.contDiffAt (hVo.mem_nhds hv)).differentiableAt one_ne_zero).hasFDerivAt
  -- step 2: the projection `pr = ‖A‖⁻¹ • A*`, `A = Dψ(v₀)`
  set A : Euclid m →L[ℝ] Euclid P := fderiv ℝ ψ v₀ with hA
  set pr : Euclid P →L[ℝ] Euclid m := ‖A‖⁻¹ • ContinuousLinearMap.adjoint A with hprdef
  have hpr : ‖pr‖ ≤ 1 := by
    rw [hprdef, norm_smul, LinearIsometryEquiv.norm_map, norm_inv, norm_norm]
    rcases eq_or_ne ‖A‖ 0 with h | h
    · rw [h]; simp
    · rw [inv_mul_cancel₀ h]
  have hprA : Injective (pr.comp A) := by
    refine (injective_iff_map_eq_zero (pr.comp A)).2 fun h hh => ?_
    have hh' : pr (A h) = 0 := hh
    rcases eq_or_ne ‖A‖ 0 with h0 | h0
    · have hA0 : A = 0 := norm_eq_zero.1 h0
      apply hDψinj v₀ hv₀
      rw [← hA, hA0, map_zero]; rfl
    · have h1 : ContinuousLinearMap.adjoint A (A h) = 0 := by
        have : ‖A‖⁻¹ • ContinuousLinearMap.adjoint A (A h) = 0 := hh'
        exact (smul_eq_zero.1 this).resolve_left (inv_ne_zero h0)
      have h2 : ‖A h‖ ^ 2 = 0 := by
        rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_left, h1,
          inner_zero_left]
      have h3 : A h = 0 := norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2)
      exact hDψinj v₀ hv₀ (by rw [← hA, h3, map_zero])
  -- step 3: the coordinate map `Φ = pr(ψ − p)` and its local inverse `χ`
  set Φ : Euclid m → Euclid m := fun v => pr (ψ v - p) with hΦ
  have hΦc : ContDiffOn ℝ 1 Φ V := pr.contDiff.comp_contDiffOn (hψc.sub contDiffOn_const)
  have hΦd : ∀ v ∈ V, HasFDerivAt Φ (pr.comp (fderiv ℝ ψ v)) v := fun v hv =>
    pr.hasFDerivAt.comp v ((hψd v hv).sub_const p)
  have hΦinj : Injective (fderiv ℝ Φ v₀) := by rw [(hΦd v₀ hv₀).fderiv]; exact hprA
  obtain ⟨V₀, O, χ, hV₀o, hOo, hv₀V₀, hV₀V, hχc, hχmaps, hΦχ, hχΦ⟩ :=
    Submission.codim1_zsl_gc_local_inverse m Φ V v₀ hVo hv₀ hΦc hΦinj
  -- step 4: the embedding margin `δ`
  obtain ⟨ε, hε, hεV₀⟩ := Metric.isOpen_iff.1 hV₀o v₀ hv₀V₀
  obtain ⟨δ, hδ, hδε⟩ := Submission.dsmc_chart_inverse_continuity P m V W₀ ψ hψc.continuousOn
    hψinj (by rw [hψV]; exact inter_subset_left) hproper v₀ hv₀ ε hε
  have hΦv₀ : Φ v₀ = 0 := by simp [hΦ, hψv₀]
  have h0O : (0 : Euclid m) ∈ O := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).1
  have hχ0 : χ 0 = v₀ := by rw [← hΦv₀]; exact (hχΦ v₀ hv₀V₀).2
  -- step 5: the graph map `G = ψ ∘ χ` and the radius `r`
  set G : Euclid m → Euclid P := fun a => ψ (χ a) with hGdef
  have hG0 : G 0 = p := by simp [hGdef, hχ0, hψv₀]
  have hGc : ContDiffOn ℝ 1 G O := hψc.comp hχc fun a ha => hV₀V (hχmaps ha)
  obtain ⟨r₁, hr₁, hr₁O⟩ := Metric.isOpen_iff.1 hOo 0 h0O
  have hGcont0 : ContinuousAt G 0 := hGc.continuousOn.continuousAt (hOo.mem_nhds h0O)
  obtain ⟨r₂, hr₂, hr₂δ⟩ := Metric.mem_nhds_iff.1
    (hGcont0.preimage_mem_nhds (by rw [hG0]; exact ball_mem_nhds p hδ))
  set r : ℝ := min (r₁ / 2) r₂ with hr
  have hrpos : 0 < r := lt_min (by positivity) hr₂
  have hcbO : closedBall (0 : Euclid m) r ⊆ O :=
    (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hr₁O
  have hbO : ball (0 : Euclid m) r ⊆ O := ball_subset_closedBall.trans hcbO
  have hbδ : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ ball p δ := fun a ha =>
    hr₂δ (ball_subset_ball (min_le_right _ _) ha)
  -- the Lipschitz bound on `B_r(0)`: `DG` is bounded on the compact set `B̄_r(0)`
  obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : Euclid m) r).exists_bound_of_continuousOn
    ((hGc.continuousOn_fderiv_of_isOpen hOo le_rfl).mono hcbO)
  have hGda : ∀ a ∈ O, HasFDerivAt G (fderiv ℝ G a) a := fun a ha =>
    ((hGc.contDiffAt (hOo.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
  have hGL : LipschitzOnWith (Real.toNNReal Cb) G (ball 0 r) := by
    refine (convex_ball (0 : Euclid m) r).lipschitzOnWith_of_nnnorm_fderiv_le
      (fun a ha => (hGda a (hbO ha)).differentiableAt) fun a ha => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hCb a (ball_subset_closedBall ha)).trans (Real.le_coe_toNNReal Cb)
  -- step 6: the chart domain `W`
  set W : Set (Euclid P) := W₀ ∩ ball p δ ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r with hW
  have hWo : IsOpen W := (hW₀o.inter isOpen_ball).inter (isOpen_ball.preimage (by fun_prop))
  have hpW : p ∈ W := ⟨⟨hpW₀, mem_ball_self hδ⟩, by simp [hrpos]⟩
  -- step 7: `pr(G(a) − p) = a`
  have hleft : ∀ a ∈ ball (0 : Euclid m) r, pr (G a - p) = a := fun a ha => hΦχ a (hbO ha)
  -- step 8: `M ∩ W = G(B_r(0))`
  have hMW : M ∩ W = G '' ball 0 r := by
    ext x
    constructor
    · rintro ⟨hxM, ⟨hxW₀, hxδ⟩, hxr⟩
      obtain ⟨v', hv', rfl⟩ : x ∈ ψ '' V := by rw [hψV]; exact ⟨hxW₀, hxM⟩
      have hv'ε : dist v' v₀ < ε := hδε v' hv' (by rw [hψv₀]; exact hxδ)
      have hv'V₀ : v' ∈ V₀ := hεV₀ hv'ε
      refine ⟨Φ v', hxr, ?_⟩
      show ψ (χ (Φ v')) = ψ v'
      rw [(hχΦ v' hv'V₀).2]
    · rintro ⟨a, ha, rfl⟩
      have hχV : χ a ∈ V := hV₀V (hχmaps (hbO ha))
      have hGa : G a ∈ W₀ ∩ M := by rw [← hψV]; exact mem_image_of_mem ψ hχV
      refine ⟨hGa.2, ⟨hGa.1, hbδ a ha⟩, ?_⟩
      show pr (G a - p) ∈ ball 0 r
      rw [hleft a ha]; exact ha
  -- step 9: `pr ∘ DG(a) = id`
  have hderiv : ∀ a ∈ ball (0 : Euclid m) r,
      pr ∘L fderiv ℝ G a = ContinuousLinearMap.id ℝ (Euclid m) := by
    intro a ha
    have h1 : HasFDerivAt (fun b => pr (G b - p)) (pr.comp (fderiv ℝ G a)) a :=
      pr.hasFDerivAt.comp a ((hGda a (hbO ha)).sub_const p)
    have h2 : (fun b => pr (G b - p)) =ᶠ[𝓝 a] fun b => b := by
      filter_upwards [isOpen_ball.mem_nhds ha] with b hb using hleft b hb
    rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
  -- step 10: `T_{G(a)}M = DG(a)(ℝᵐ)`
  have htan : ∀ a ∈ ball (0 : Euclid m) r,
      tangentSpace M (G a) = Set.range (fderiv ℝ G a) := by
    intro a ha
    have haO : a ∈ O := hbO ha
    have hχV : χ a ∈ V := hV₀V (hχmaps haO)
    have hχd : HasFDerivAt χ (fderiv ℝ χ a) a :=
      ((hχc.contDiffAt (hOo.mem_nhds haO)).differentiableAt one_ne_zero).hasFDerivAt
    have hGfd : fderiv ℝ G a = (fderiv ℝ ψ (χ a)).comp (fderiv ℝ χ a) :=
      ((hψd (χ a) hχV).comp a hχd).fderiv
    -- `Dχ(a)` is injective, hence surjective
    have hsurj : Surjective (fderiv ℝ χ a) := by
      have hid : (fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a) = ContinuousLinearMap.id ℝ (Euclid m) := by
        have h1 : HasFDerivAt (fun b => Φ (χ b)) ((fderiv ℝ Φ (χ a)).comp (fderiv ℝ χ a)) a :=
          (hΦd (χ a) hχV).differentiableAt.hasFDerivAt.comp a hχd
        have h2 : (fun b => Φ (χ b)) =ᶠ[𝓝 a] fun b => b := by
          filter_upwards [hOo.mem_nhds haO] with b hb using hΦχ b hb
        rw [← h1.fderiv, h2.fderiv_eq, fderiv_fun_id]
      have hinj : Injective (fderiv ℝ χ a) := by
        intro u v huv
        have := congrArg (fderiv ℝ Φ (χ a)) huv
        have hu := congrArg (fun L => L u) hid
        have hv := congrArg (fun L => L v) hid
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hu hv
        rw [← hu, ← hv]; exact this
      exact (LinearMap.injective_iff_surjective (f := ((fderiv ℝ χ a : Euclid m →L[ℝ] Euclid m) :
        Euclid m →ₗ[ℝ] Euclid m))).1 hinj
    rw [show G a = ψ (χ a) from rfl, Submission.chart_tangentSpace_eq_range_fderiv P m 1 M W₀ V ψ
      (χ a) le_rfl hVo hW₀o hψc hψinj hψV hproper hDψinj hχV, hGfd, ContinuousLinearMap.coe_comp,
      hsurj.range_comp]
  exact ⟨pr, G, r, W, Real.toNNReal Cb, hrpos, hWo, hpW, hpr, hG0, hGc.mono hbO, hGL, hMW, hleft,
    hderiv, htan⟩

/-- Derivatives within a set are unique on the span of its curve tangent vectors (Simon Ch. 2,
§4, p. 55; cf. (4.6)–(4.7)), for an arbitrary set `M ⊆ ℝᴾ`.  If `f` has derivative `f'` within
`M` at `x`, then so does `L = fderivWithin ℝ f M x`, and two derivatives within `M` agree on the
tangent cone of `M` at `x`.  Each `w = γ'(0) ∈ T_xM` lies in that cone: as `t → 0`, `t ≠ 0`,
`γ(t) − x → 0`, `x + (γ(t) − x) = γ(t) ∈ M` and `t⁻¹(γ(t) − x) → w`.  So `L = f'` on `T_xM`,
hence on its linear span. -/
theorem Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span : ∀ (P : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ) (f' : Euclid P →L[ℝ] ℝ) (x v : Euclid P), HasFDerivWithinAt f f' M x → v ∈ Submodule.span ℝ (tangentSpace M x) → fderivWithin ℝ f M x v = f' v := by
  intro P M f f' x v hf hv
  -- `L = fderivWithin ℝ f M x` and `f'` are both derivatives of `f` within `M` at `x`, so they
  -- agree on the tangent cone of `M` at `x`
  have huniq : EqOn (fderivWithin ℝ f M x) f' (tangentConeAt ℝ M x) :=
    hf.differentiableWithinAt.hasFDerivWithinAt.unique_on hf
  -- the velocity `w = γ'(0)` of a curve `γ` in `M` through `x` lies in the tangent cone:
  -- take `c(t) = t⁻¹` and `d(t) = γ(t) − x` as `t → 0`, `t ≠ 0`
  have hcone : tangentSpace M x ⊆ tangentConeAt ℝ M x := by
    rintro w ⟨γ, -, hγM, hγ0, hγw⟩
    refine mem_tangentConeAt_of_seq (𝓝[≠] (0 : ℝ)) (fun t => t⁻¹) (fun t => γ t - x) ?_ ?_ ?_
    · -- `γ(t) − x → 0`, since `γ` is continuous at `0` and `γ(0) = x`
      rw [tendsto_sub_nhds_zero_iff, ← hγ0]
      exact hγw.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · -- `x + (γ(t) − x) = γ(t) ∈ M` for `t ∈ (−1, 1)`
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) one_pos)]
        with t ht
      rw [add_sub_cancel]
      exact hγM ht
    · -- `t⁻¹(γ(t) − x) = t⁻¹(γ(0 + t) − γ(0)) → γ'(0) = w`
      simpa [hγ0] using hγw.tendsto_slope_zero
  -- `L = f'` on `T_xM`, hence on its linear span
  exact LinearMap.eqOn_span (f := (fderivWithin ℝ f M x : Euclid P →ₗ[ℝ] ℝ))
    (g := (f' : Euclid P →ₗ[ℝ] ℝ)) (fun w hw => huniq (hcone hw)) hv
/-- Hausdorff measure and lower integrals over Lipschitz images (Simon Ch. 2, Theorem 1.8(i)):
if `G : ℝᵐ → ℝᴾ` is `Λ`-Lipschitz on `D`, then `Hᵐ(G(N)) ≤ Λᵐ Lᵐ(N)` for every `N ⊆ D`, measurable
or not, and for Borel `D` and Borel `H ≥ 0`, `∫_{G(D)} H dHᵐ ≤ Λᵐ ∫_D H ∘ G dLᵐ`.  The first
bound is the `μH[m]` estimate for Lipschitz images scaled by the common normalizing constant of
`μHE[m]`, with `μHE[m] = Lᵐ` on `ℝᵐ`.  Applied to `N = G⁻¹(s) ∩ D` it gives
`Hᵐ⌞G(D) ≤ Λᵐ G₊(Lᵐ⌞D)` on Borel sets `s`; integrating `H` against this measure inequality and
changing variables gives the second bound.  Injectivity of `G` is not needed. -/
theorem Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le : ∀ (m P : ℕ) (G : Euclid m → Euclid P) (D : Set (Euclid m)) (Λ : NNReal), LipschitzOnWith Λ G D → (∀ N ⊆ D, μHE[m] (G '' N) ≤ (Λ : ℝ≥0∞) ^ m * volume N) ∧ (MeasurableSet D → ∀ H : Euclid P → ℝ≥0∞, Measurable H → ∫⁻ x in G '' D, H x ∂μHE[m] ≤ (Λ : ℝ≥0∞) ^ m * ∫⁻ a in D, H (G a)) := by
  intro m P G D Λ hG
  -- part (a): `μH[m](G(N)) ≤ Λᵐ μH[m](N)`, scaled by the normalizing constant of `μHE[m]`
  have hset : ∀ N ⊆ D, μHE[m] (G '' N) ≤ (Λ : ℝ≥0∞) ^ m * volume N := by
    intro N hN
    have h := (hG.mono hN).hausdorffMeasure_image_le (d := (m : ℝ)) (Nat.cast_nonneg m)
    rw [ENNReal.rpow_natCast] at h
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m,
      Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    calc _ ≤ _ := mul_le_mul_right h _
      _ = _ := by ring
  refine ⟨hset, fun hD H hH => ?_⟩
  -- part (b): the measure inequality `Hᵐ⌞G(D) ≤ Λᵐ G₊(Lᵐ⌞D)`, from (a) with `N = G⁻¹(s) ∩ D`
  have hGae : AEMeasurable G (volume.restrict D) := hG.continuousOn.aemeasurable hD
  have hle : μHE[m].restrict (G '' D) ≤ ((Λ : ℝ≥0∞) ^ m) • (volume.restrict D).map G := by
    refine Measure.le_iff.2 fun s hs => ?_
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.map_apply_of_aemeasurable hGae hs,
      Measure.restrict_apply' hD, smul_eq_mul]
    calc μHE[m] (s ∩ G '' D) ≤ μHE[m] (G '' (G ⁻¹' s ∩ D)) := by
          refine measure_mono ?_
          rintro _ ⟨hy, a, ha, rfl⟩
          exact ⟨a, ⟨hy, ha⟩, rfl⟩
      _ ≤ (Λ : ℝ≥0∞) ^ m * volume (G ⁻¹' s ∩ D) := hset _ inter_subset_right
  -- integrate `H` against the measure inequality and change variables along `G`
  calc ∫⁻ x in G '' D, H x ∂μHE[m] ≤ ∫⁻ x, H x ∂(((Λ : ℝ≥0∞) ^ m) • (volume.restrict D).map G) :=
        lintegral_mono' hle le_rfl
    _ = (Λ : ℝ≥0∞) ^ m * ∫⁻ a in D, H (G a) := by
        rw [lintegral_smul_measure, lintegral_map' hH.aemeasurable hGae, smul_eq_mul]
/-- The tangent projection `x ↦ P_x` of an embedded `C¹` submanifold `M ⊆ ℝᴾ`, `P_x` the
orthogonal projection onto `span T_xM`, is continuous on `M`.  Near `x₀ ∈ M` take a `C¹` graph
chart `G` on `B_r(0) ⊆ ℝᵐ`: `M ∩ W = G(B_r(0))`, `pr(G(a) − x₀) = a`, `pr ∘ DG(a) = id` and
`T_{G(a)}M = DG(a)(ℝᵐ)`.  `A = DG(a)` is injective, so the Gram operator `A*A` is invertible,
and `P_{G(a)} = A(A*A)⁻¹A*` by the orthogonality characterization of the projection.  This is
continuous in `a`, as `DG` is continuous, the adjoint is an isometry and inversion is continuous
at units; composing with `x ↦ pr(x − x₀)` gives continuity on the neighbourhood `M ∩ W` of `x₀`
in `M`. -/
theorem Submission.codim1_hcp_lsa_tangent_projection_continuousOn : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → ContinuousOn (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection) M := by
  intro P m M hM x₀ hx₀
  -- step 1: a `C¹` graph chart `G` on `B_r(0)` at `x₀`, with `M ∩ W = G(B_r(0))`
  obtain ⟨pr, G, r, W, -, -, hWo, hx₀W, -, -, hGc, -, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M x₀ hM hx₀
  -- step 2: `A(a) = DG(a)` is continuous on `B_r(0)`, and injective since `pr ∘ A(a) = id`
  set A : Euclid m → (Euclid m →L[ℝ] Euclid P) := fun a => fderiv ℝ G a
  have hAc : ContinuousOn A (ball 0 r) := hGc.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hAinj : ∀ a ∈ ball (0 : Euclid m) r, Injective (A a) := by
    intro a ha u v huv
    have h1 := congrArg (fun L => L u) (hderiv a ha)
    have h2 := congrArg (fun L => L v) (hderiv a ha)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2]
    exact congrArg pr huv
  -- step 3: the Gram operator `Γ(a) = A(a)* A(a)` is injective, hence a unit of `L(ℝᵐ)`
  set Γ : Euclid m → (Euclid m →L[ℝ] Euclid m) := fun a =>
    (ContinuousLinearMap.adjoint (A a)).comp (A a) with hΓ
  have hΓunit : ∀ a ∈ ball (0 : Euclid m) r, IsUnit (Γ a) := by
    intro a ha
    rw [ContinuousLinearMap.isUnit_iff_bijective]
    have hinj : Injective (Γ a) := by
      intro u v huv
      -- `⟨Γ(a) h, h⟩ = ‖A(a) h‖²` vanishes for `h = u - v`
      have h0 : Γ a (u - v) = 0 := by rw [map_sub, huv, sub_self]
      have h1 : inner ℝ (Γ a (u - v)) (u - v) = ‖A a (u - v)‖ ^ 2 := by
        simp only [hΓ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left]
        exact real_inner_self_eq_norm_sq _
      rw [h0, inner_zero_left] at h1
      have h2 : A a (u - v) = 0 := by
        have : ‖A a (u - v)‖ = 0 := by nlinarith [norm_nonneg (A a (u - v))]
        exact norm_eq_zero.1 this
      exact sub_eq_zero.1 (hAinj a ha (by rw [h2, map_zero]))
    exact ⟨hinj, (LinearMap.injective_iff_surjective
      (f := ((Γ a : Euclid m →L[ℝ] Euclid m) : Euclid m →ₗ[ℝ] Euclid m))).1 hinj⟩
  -- step 4: `P_{G(a)} = Q(a) = A(a) Γ(a)⁻¹ A(a)*`, by the orthogonality characterization
  set Q : Euclid m → (Euclid P →L[ℝ] Euclid P) := fun a =>
    (A a).comp ((Ring.inverse (Γ a)).comp (ContinuousLinearMap.adjoint (A a))) with hQ
  have hQeq : ∀ a ∈ ball (0 : Euclid m) r,
      (Submodule.span ℝ (tangentSpace M (G a))).starProjection = Q a := by
    intro a ha
    -- `T_{G(a)}M = A(a)(ℝᵐ)` is already a linear subspace
    have hspan : Submodule.span ℝ (tangentSpace M (G a)) =
        LinearMap.range ((A a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
      apply le_antisymm
      · rw [Submodule.span_le, htan a ha]
        rintro _ ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro _ ⟨y, rfl⟩
        apply Submodule.subset_span
        rw [htan a ha]
        exact ⟨y, rfl⟩
    have hinvr : Γ a * Ring.inverse (Γ a) = 1 := Ring.mul_inverse_cancel _ (hΓunit a ha)
    ext1 u
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
    · rw [hspan]
      exact ⟨_, rfl⟩
    · -- `⟨u − Q(a) u, A(a) h⟩ = ⟨A(a)* u − Γ(a) Γ(a)⁻¹ A(a)* u, h⟩ = 0`
      intro w hw
      rw [hspan] at hw
      obtain ⟨h, rfl⟩ := hw
      simp only [hQ, ContinuousLinearMap.coe_coe]
      rw [inner_sub_left, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.adjoint_inner_left]
      have : ContinuousLinearMap.adjoint (A a) ((A a).comp ((Ring.inverse (Γ a)).comp
          (ContinuousLinearMap.adjoint (A a))) u) = ContinuousLinearMap.adjoint (A a) u := by
        have h4 := congrArg
          (fun L : Euclid m →L[ℝ] Euclid m => L (ContinuousLinearMap.adjoint (A a) u)) hinvr
        simpa [hΓ, mul_apply_eq_comp] using h4
      rw [this, sub_self]
  -- step 5: `Q` is continuous on `B_r(0)`: the adjoint is a linear isometry, and inversion is
  -- continuous at every unit
  have hQc : ContinuousOn Q (ball 0 r) := by
    have hadj : ContinuousOn (fun a => ContinuousLinearMap.adjoint (A a)) (ball 0 r) :=
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Euclid m) (F := Euclid P)).continuous
        |>.comp_continuousOn hAc
    have hΓc : ContinuousOn Γ (ball 0 r) := hadj.clm_comp hAc
    have hinv : ContinuousOn (fun a => Ring.inverse (Γ a)) (ball 0 r) := by
      intro a ha
      obtain ⟨u, hu⟩ := hΓunit a ha
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp_continuousWithinAt (hΓc a ha)
    exact hAc.clm_comp (hinv.clm_comp hadj)
  -- step 6: on `M ∩ W`, `x = G(a)` with `a = pr(x − x₀) ∈ B_r(0)`, so `P_x = Q(pr(x − x₀))`
  have hPQ : ∀ x ∈ M ∩ W,
      (Submodule.span ℝ (tangentSpace M x)).starProjection = Q (pr (x - x₀)) := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]
    exact hQeq a ha
  have hcont : ContinuousOn (fun x => Q (pr (x - x₀))) (M ∩ W) := by
    refine hQc.comp (by fun_prop) fun x hx => ?_
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]
    exact ha
  -- step 7: `M ∩ W` is a neighbourhood of `x₀` in `M`
  exact (hcont.congr hPQ x₀ ⟨hx₀, hx₀W⟩).mono_of_mem_nhdsWithin
    (inter_mem_nhdsWithin M (hWo.mem_nhds hx₀W))

/-- **Mollifying a compactly supported Lipschitz function** (the smoothing step of the Lipschitz
approximation used for Simons' theorem, Simon B.2): if `g : ℝᵐ → ℝ` is `K`-Lipschitz and vanishes
off the compact set `S`, and `δ > 0`, then there are `C^∞` functions `gₖ`, vanishing off the closed
`δ`-neighbourhood of `S`, with `gₖ → g` uniformly and `Dgₖ → Dg` in `L²`.  Take `gₖ = ρₖ ⋆ g` for
normalized bumps `ρₖ ≥ 0` supported in `B_{εₖ}(0)`, `εₖ = δ / (k + 2)`, with
`ρₖ ≤ 2ᵐ / Lᵐ(B̄_{εₖ})`.  Then `|gₖ − g| ≤ K εₖ`, and `Dgₖ = ρₖ ⋆ Dg` by dominated convergence of
difference quotients (`g` is differentiable a.e. by Rademacher), so `Dgₖ → Dg` at every Lebesgue
point of `Dg` (Besicovitch differentiation).  As `|Dgₖ − Dg|² ≤ (2K)²` on the compact
`δ`-neighbourhood of `S` and `= 0` off it, dominated convergence gives the `L²` limit. -/
theorem Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support : ∀ (m : ℕ) (g : Euclid m → ℝ) (K : NNReal) (S : Set (Euclid m)) (δ : ℝ), LipschitzWith K g → IsCompact S → (∀ a, a ∉ S → g a = 0) → 0 < δ → ∃ gs : ℕ → Euclid m → ℝ, (∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k)) ∧ (∀ k a, a ∉ Metric.cthickening δ S → gs k a = 0) ∧ TendstoUniformly gs g atTop ∧ Tendsto (fun k => ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0) := by
  intro m g K S δ hg hS hg0 hδ
  classical
  -- the a.e. derivative `F = Dg`
  set F : Euclid m → (Euclid m →L[ℝ] ℝ) := fderiv ℝ g with hFdef
  have hFm : Measurable F := measurable_fderiv ℝ g
  have hFb : ∀ y, ‖F y‖ ≤ K := fun y => norm_fderiv_le_of_lipschitz ℝ hg
  have hF0 : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    have h : g =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hy] with z hz using hg0 z hz
    rw [hFdef, h.fderiv_eq]; simp
  have hFint : Integrable F := by
    refine Integrable.mono' (g := S.indicator fun _ => (K : ℝ)) ?_ hFm.aestronglyMeasurable ?_
    · exact (integrable_indicator_iff hS.isClosed.measurableSet).2
        (integrableOn_const hS.measure_lt_top.ne)
    · filter_upwards with y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]; exact hFb y
      · rw [indicator_of_notMem hy, hF0 y hy, norm_zero]
  -- radii
  set ε : ℕ → ℝ := fun k => δ / ((k : ℝ) + 2) with hεdef
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  have hεδ : ∀ k, ε k < δ := fun k => by
    simp only [hεdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := δ)).div_atTop
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [hεdef] using h
  -- normalized bumps
  let φ : ℕ → ContDiffBump (0 : Euclid m) := fun k =>
    ⟨ε k / 2, ε k, by linarith [hε k], by linarith [hε k]⟩
  set I : ℕ → ℝ := fun k => ∫ x, (φ k) x with hIdef
  have hφint : ∀ k, Integrable (fun x => (φ k) x) := fun k =>
    (φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport
  -- the volume of balls
  have hvol : ∀ (y : Euclid m) (s : ℝ), 0 ≤ s →
      volume.real (closedBall y s) = s ^ m * volume.real (ball (0 : Euclid m) 1) := by
    intro y s hs
    rw [measureReal_def, Measure.addHaar_closedBall volume y hs, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), measureReal_def]
  have hc : 0 < volume.real (ball (0 : Euclid m) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' measure_ball_lt_top.ne
  have hI : ∀ k, volume.real (closedBall (0 : Euclid m) (ε k / 2)) ≤ I k := by
    intro k
    have hle : (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) ≤
        fun x => (φ k) x := by
      intro x
      by_cases hx : x ∈ closedBall (0 : Euclid m) (ε k / 2)
      · rw [indicator_of_mem hx]; exact ((φ k).one_of_mem_closedBall hx).ge
      · rw [indicator_of_notMem hx]; exact (φ k).nonneg
    have hint1 : Integrable ((closedBall (0 : Euclid m) (ε k / 2)).indicator fun _ => (1 : ℝ)) :=
      (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const measure_closedBall_lt_top.ne)
    calc volume.real (closedBall (0 : Euclid m) (ε k / 2))
        = ∫ x, (closedBall (0 : Euclid m) (ε k / 2)).indicator (fun _ => (1 : ℝ)) x := by
          rw [integral_indicator measurableSet_closedBall]; simp
      _ ≤ I k := integral_mono hint1 (hφint k) hle
  have hIpos : ∀ k, 0 < I k := fun k =>
    lt_of_lt_of_le (by rw [hvol 0 _ (by linarith [hε k])]; exact mul_pos (pow_pos (by linarith [hε k]) _) hc)
      (hI k)
  set ρ : ℕ → Euclid m → ℝ := fun k x => (I k)⁻¹ * (φ k) x with hρdef
  have hρ0 : ∀ k x, 0 ≤ ρ k x := fun k x => mul_nonneg (inv_nonneg.2 (hIpos k).le) (φ k).nonneg
  have hρint1 : ∀ k, ∫ x, ρ k x = 1 := fun k => by
    have hIk : ∫ x, (φ k) x = I k := rfl
    simp only [hρdef]; rw [integral_const_mul, hIk, inv_mul_cancel₀ (hIpos k).ne']
  have hρsupp : ∀ k, Function.support (ρ k) ⊆ ball 0 (ε k) := fun k =>
    (Function.support_mul_subset_right _ _).trans (φ k).support_eq.subset
  have hρsmooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k) := fun k => contDiff_const.mul (φ k).contDiff
  have hρcs : ∀ k, HasCompactSupport (ρ k) := fun k => (φ k).hasCompactSupport.mul_left
  have hρcont : ∀ k, Continuous (ρ k) := fun k => continuous_const.mul (φ k).continuous
  have hρintg : ∀ k, Integrable (ρ k) := fun k => (hρcont k).integrable_of_hasCompactSupport (hρcs k)
  have hρle : ∀ k x (y : Euclid m), ρ k x ≤ 2 ^ m / volume.real (closedBall y (ε k)) := by
    intro k x y
    have h1 : ρ k x ≤ (I k)⁻¹ := by
      simp only [hρdef]
      calc (I k)⁻¹ * (φ k) x ≤ (I k)⁻¹ * 1 :=
            mul_le_mul_of_nonneg_left (φ k).le_one (inv_nonneg.2 (hIpos k).le)
        _ = (I k)⁻¹ := mul_one _
    have hpos2 : 0 < (ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1) :=
      mul_pos (pow_pos (by linarith [hε k]) _) hc
    have h2 : (I k)⁻¹ ≤ ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ := by
      rw [← hvol 0 _ (by linarith [hε k])]
      exact inv_anti₀ (by rw [hvol 0 _ (by linarith [hε k])]; exact hpos2) (hI k)
    have h3 : ((ε k / 2) ^ m * volume.real (ball (0 : Euclid m) 1))⁻¹ =
        2 ^ m / volume.real (closedBall y (ε k)) := by
      rw [hvol y _ (hε k).le, div_pow]
      field_simp
    linarith [h1, h2, h3.le, h3.ge]
  -- the approximants
  set gs : ℕ → Euclid m → ℝ := fun k => convolution (ρ k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume
    with hgsdef
  have hgs_apply : ∀ k a, gs k a = ∫ t, ρ k t * g (a - t) := by
    intro k a
    simp only [hgsdef, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hgs_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (gs k) := fun k =>
    (hρcs k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hρsmooth k)
      hg.continuous.locallyIntegrable
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hgs_supp : ∀ k a, a ∉ T → gs k a = 0 := by
    intro k a ha
    rw [hgs_apply]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : ρ k t = 0
    · simp [ht]
    · have htb : t ∈ ball (0 : Euclid m) (ε k) := hρsupp k ht
      rw [mem_ball_zero_iff] at htb
      have hS' : a - t ∉ S := by
        intro hmem
        exact ha (Metric.mem_cthickening_of_dist_le a (a - t) δ S hmem
          (by rw [dist_eq_norm, sub_sub_cancel]; linarith [hεδ k]))
      simp [hg0 _ hS']
  refine ⟨gs, hgs_smooth, hgs_supp, ?_, ?_⟩
  · -- uniform convergence
    rw [Metric.tendstoUniformly_iff]
    intro e he
    have hK : Tendsto (fun k => (K : ℝ) * ε k) atTop (𝓝 0) := by
      simpa using hεlim.const_mul (K : ℝ)
    filter_upwards [hK.eventually (gt_mem_nhds he)] with k hk a
    rw [dist_comm]
    refine lt_of_le_of_lt ?_ hk
    refine dist_convolution_le (by positivity) (hρsupp k) (hρ0 k) (hρint1 k)
      hg.continuous.aestronglyMeasurable fun x hx => ?_
    calc dist (g x) (g a) ≤ K * dist x a := hg.dist_le_mul x a
      _ ≤ K * ε k := by gcongr; exact (mem_ball.1 hx).le
  · -- the derivative of `gs k` is the mollification of `F`
    have hFae : ∀ a : Euclid m, ∀ᵐ t ∂(volume : Measure (Euclid m)), DifferentiableAt ℝ g (a - t) :=
      fun a => (Measure.measurePreserving_sub_left volume a).quasiMeasurePreserving.ae
        hg.ae_differentiableAt
    have hsl : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall
        fun n => ?_⟩
      simp only [mem_compl_iff, mem_singleton_iff]; positivity
    have hderiv : ∀ k a, fderiv ℝ (gs k) a = ∫ t, ρ k t • F (a - t) := by
      intro k a
      have hint : Integrable (fun t => ρ k t • F (a - t)) := by
        refine Integrable.mono' ((hρintg k).mul_const (K : ℝ)) ?_ (Eventually.of_forall fun t => ?_)
        · exact (hρcont k).aestronglyMeasurable.smul
            (hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        · rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
          exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
      ext v
      rw [ContinuousLinearMap.integral_apply hint]
      simp only [_root_.smul_apply, smul_eq_mul]
      set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hsdef
      have hspos : ∀ n, 0 < s n := fun n => by positivity
      -- difference quotients of `gs k` along `v`
      have hline : HasDerivAt (fun r : ℝ => gs k (a + r • v)) (fderiv ℝ (gs k) a v) 0 := by
        have h1 : HasDerivAt (fun r : ℝ => a + r • v) v 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add a
        have h2 : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) (a + (0 : ℝ) • v) := by
          rw [zero_smul, add_zero]
          exact ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
        exact h2.comp_hasDerivAt (0 : ℝ) h1
      have hq1 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (fderiv ℝ (gs k) a v)) := by
        have := (hasDerivAt_iff_tendsto_slope_zero.1 hline).comp hsl
        simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      have hgint : ∀ w : Euclid m, Integrable (fun t => ρ k t * g (w - t)) := fun w =>
        ((hρcont k).mul (hg.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((hρcs k).mul_right)
      have hrepr : ∀ n, (s n)⁻¹ * (gs k (a + s n • v) - gs k a) =
          ∫ t, ρ k t * ((s n)⁻¹ * (g (a - t + s n • v) - g (a - t))) := by
        intro n
        rw [hgs_apply, hgs_apply, ← integral_sub (hgint _) (hgint _), ← integral_const_mul]
        congr 1
        ext t
        rw [show a + s n • v - t = a - t + s n • v by abel]
        ring
      have hq2 : Tendsto (fun n => (s n)⁻¹ * (gs k (a + s n • v) - gs k a)) atTop
          (𝓝 (∫ t, ρ k t * F (a - t) v)) := by
        simp_rw [hrepr]
        refine tendsto_integral_of_dominated_convergence (fun t => ρ k t * (K * ‖v‖)) (fun n => ?_)
          ((hρintg k).mul_const _) (fun n => Eventually.of_forall fun t => ?_) ?_
        · exact ((hρcont k).mul (continuous_const.mul ((hg.continuous.comp
            ((continuous_const.sub continuous_id).add continuous_const)).sub
            (hg.continuous.comp (continuous_const.sub continuous_id))))).aestronglyMeasurable
        · rw [norm_mul, Real.norm_of_nonneg (hρ0 k t)]
          refine mul_le_mul_of_nonneg_left ?_ (hρ0 k t)
          have hL := hg.dist_le_mul (a - t + s n • v) (a - t)
          rw [dist_eq_norm, dist_eq_norm, add_sub_cancel_left, norm_smul,
            Real.norm_of_nonneg (hspos n).le] at hL
          rw [norm_mul, norm_inv, Real.norm_of_nonneg (hspos n).le, Real.norm_eq_abs]
          calc (s n)⁻¹ * |g (a - t + s n • v) - g (a - t)|
              ≤ (s n)⁻¹ * (K * (s n * ‖v‖)) := by gcongr; exact hL
            _ = K * ‖v‖ := by
                rw [show (s n)⁻¹ * (K * (s n * ‖v‖)) = (s n)⁻¹ * s n * (K * ‖v‖) by ring,
                  inv_mul_cancel₀ (hspos n).ne', one_mul]
        · filter_upwards [hFae a] with t ht
          refine Tendsto.const_mul _ ?_
          have hl : HasDerivAt (fun r : ℝ => g (a - t + r • v)) (F (a - t) v) 0 := by
            have h1 : HasDerivAt (fun r : ℝ => a - t + r • v) v 0 := by
              simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (a - t)
            have h2 : HasFDerivAt g (F (a - t)) (a - t + (0 : ℝ) • v) := by
              rw [zero_smul, add_zero]; exact ht.hasFDerivAt
            exact h2.comp_hasDerivAt (0 : ℝ) h1
          have := (hasDerivAt_iff_tendsto_slope_zero.1 hl).comp hsl
          simpa [Function.comp_def, smul_eq_mul, hsdef] using this
      exact tendsto_nhds_unique hq1 hq2
    -- bounds and support of the derivatives
    have hDgsb : ∀ k a, ‖fderiv ℝ (gs k) a‖ ≤ K := by
      intro k a
      rw [hderiv k a]
      calc ‖∫ t, ρ k t • F (a - t)‖ ≤ ∫ t, ρ k t * K := by
            refine norm_integral_le_of_norm_le ((hρintg k).mul_const _) (Eventually.of_forall fun t => ?_)
            rw [norm_smul, Real.norm_of_nonneg (hρ0 k t)]
            exact mul_le_mul_of_nonneg_left (hFb _) (hρ0 k t)
        _ = K := by rw [integral_mul_const, hρint1 k, one_mul]
    have hDgs0 : ∀ k a, a ∉ T → fderiv ℝ (gs k) a = 0 := by
      intro k a ha
      have h : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds ha] with b hb
        exact hgs_supp k b hb
      rw [h.fderiv_eq]; simp
    -- Lebesgue points: `D gs k → F` a.e.
    have hεlim' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hεlim, Eventually.of_forall hε⟩
    have hae : ∀ᵐ a ∂(volume : Measure (Euclid m)), Tendsto (fun k => fderiv ℝ (gs k) a) atTop (𝓝 (F a)) := by
      filter_upwards [(Besicovitch.vitaliFamily (volume : Measure (Euclid m))).ae_tendsto_average_norm_sub
        hFint.locallyIntegrable] with a ha
      have havg : Tendsto (fun k => ⨍ y in closedBall a (ε k), ‖F y - F a‖) atTop (𝓝 0) :=
        ha.comp ((Besicovitch.tendsto_filterAt volume a).comp hεlim')
      have hconv := tendsto_integral_smul_of_tendsto_average_norm_sub (μ := volume)
        (g := fun k y => ρ k (a - y)) (2 ^ m) havg
        (Eventually.of_forall fun k => hFint.integrableOn)
        (tendsto_const_nhds.congr' (Eventually.of_forall fun k => by
          simp only
          rw [integral_sub_left_eq_self (fun y => ρ k y) volume a, hρint1 k]))
        (Eventually.of_forall fun k y hy => by
          have h := hρsupp k hy
          rw [mem_ball_zero_iff] at h
          rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
          exact h.le)
        (Eventually.of_forall fun k y => by
          rw [abs_of_nonneg (hρ0 k _)]; exact hρle k _ a)
      refine hconv.congr' (Eventually.of_forall fun k => ?_)
      show _ = fderiv ℝ (gs k) a
      rw [hderiv k a]
      have := integral_sub_left_eq_self (fun t => ρ k t • F (a - t)) volume a
      simp only [sub_sub_cancel] at this
      exact this
    -- dominated convergence in `L²`
    have hTc : IsCompact T := hS.cthickening
    have hkey := tendsto_lintegral_of_dominated_convergence (μ := volume)
      (F := fun k a => ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2)) (f := fun _ => 0)
      (T.indicator fun _ => ENNReal.ofReal ((2 * K) ^ 2))
      (fun k => (((measurable_fderiv ℝ (gs k)).sub hFm).norm.pow_const 2).ennreal_ofReal)
      (fun k => Eventually.of_forall fun a => by
        by_cases ha : a ∈ T
        · rw [indicator_of_mem ha]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖fderiv ℝ (gs k) a - F a‖ ≤ 2 * K :=
            (norm_sub_le _ _).trans (by linarith [hDgsb k a, hFb a])
          exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        · have haS : a ∉ S := fun h => ha (Metric.self_subset_cthickening S h)
          rw [indicator_of_notMem ha]
          show ENNReal.ofReal (‖fderiv ℝ (gs k) a - F a‖ ^ 2) ≤ 0
          rw [hDgs0 k a ha, hF0 a haS, sub_zero, norm_zero]
          simp)
      (by
        rw [lintegral_indicator_const hTc.isClosed.measurableSet]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTc.measure_lt_top.ne)
      (by
        filter_upwards [hae] with a ha
        have h1 : Tendsto (fun k => ‖fderiv ℝ (gs k) a - F a‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 ha
        have h2 := ENNReal.tendsto_ofReal (h1.pow 2)
        simpa using h2)
    simpa using hkey

/-- **Rademacher's theorem on a `C¹` submanifold** (Simon Ch. 2, 1.4 and §4).  If `M ⊆ ℝᴾ` is an
embedded `C¹` `m`-dimensional submanifold and `ζ` is locally Lipschitz on `M`, then `ζ` is
differentiable within `M` at `Hᵐ`-a.e. point of `M`.  Near `p ∈ M`, a graph chart `G` over
`B_r(0) ⊆ ℝᵐ` with `pr(G(a) − p) = a` is shrunk to `B_{r₁}(0)` so that `ζ ∘ G` is Lipschitz there
and every `x ∈ M ∩ O` is `G(pr(x − p))`, for an open `O ∋ p`.  By Rademacher `ζ ∘ G` is
differentiable off an `Lᵐ`-null set `N`, and `G(N)` is `Hᵐ`-null because `G` is Lipschitz; off
`G(N)`, `ζ` agrees on `M ∩ O` with the differentiable function `(ζ ∘ G)(pr(· − p))`.  Countably
many such `O` cover `M`. -/
theorem Submission.codim1_hcp_lsa_rademacher_on_submanifold : ∀ (P m : ℕ) (M : Set (Euclid P)) (ζ : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M ζ → ∀ᵐ x ∂(μHE[m].restrict M), DifferentiableWithinAt ℝ ζ M x := by
  intro P m M ζ hM hζ
  -- step 1: `M` is Borel
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  -- step 2: near each `p ∈ M`, `ζ` is differentiable within `M` off an `Hᵐ`-null set
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∃ E : Set (Euclid P),
      μHE[m] E = 0 ∧ ∀ x ∈ M ∩ O, x ∉ E → DifferentiableWithinAt ℝ ζ M x := by
    intro p hp
    -- (a) a graph chart `G` of `M ∩ W` over `B_r(0)`, inverted by `z ↦ pr(z − p)`
    obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, -, hG0, hGc, hGL, hMW, hleft, -, -⟩ :=
      Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
    -- (b) `ζ` is `K`-Lipschitz on `t ⊇ M ∩ U`, with `U ∋ p` open
    obtain ⟨K, t, ht, hKt⟩ := hζ hp
    obtain ⟨U, hUo, hpU, hUt⟩ : ∃ U : Set (Euclid P), IsOpen U ∧ p ∈ U ∧ M ∩ U ⊆ t := by
      obtain ⟨U, hUo, hpU, hUt⟩ := mem_nhdsWithin.1 ht
      exact ⟨U, hUo, hpU, fun x hx => hUt ⟨hx.2, hx.1⟩⟩
    -- (c) shrink the chart so that `G(B_{r₁}(0)) ⊆ U`; `O = W ∩ {pr(z − p) ∈ B_{r₁}(0)}`
    obtain ⟨r₁, hr₁, hr₁r, hGU⟩ : ∃ r₁ : ℝ, 0 < r₁ ∧ r₁ ≤ r ∧ G '' ball 0 r₁ ⊆ U := by
      have hGcont : ContinuousAt G 0 :=
        hGc.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))
      have hpre : G ⁻¹' U ∈ 𝓝 (0 : Euclid m) :=
        hGcont.preimage_mem_nhds (hUo.mem_nhds (by rw [hG0]; exact hpU))
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hpre
      refine ⟨min ε r, lt_min hε hr, min_le_right _ _, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      exact hεU (ball_subset_ball (min_le_left _ _) ha)
    have hball : ball (0 : Euclid m) r₁ ⊆ ball 0 r := ball_subset_ball hr₁r
    let O : Set (Euclid P) := W ∩ (fun z => pr (z - p)) ⁻¹' ball 0 r₁
    have hOo : IsOpen O := hWo.inter (isOpen_ball.preimage (by fun_prop))
    have hpO : p ∈ O := ⟨hpW, by simp [hr₁]⟩
    -- (d) every `x ∈ M ∩ O` is `G(a)` with `a = pr(x − p) ∈ B_{r₁}(0)`
    have hMO : ∀ x ∈ M ∩ O, pr (x - p) ∈ ball (0 : Euclid m) r₁ ∧ G (pr (x - p)) = x := by
      intro x hx
      have hxW : x ∈ M ∩ W := ⟨hx.1, hx.2.1⟩
      rw [hMW] at hxW
      obtain ⟨a, ha, rfl⟩ := hxW
      have h2 : pr (G a - p) ∈ ball (0 : Euclid m) r₁ := hx.2.2
      rw [hleft a ha] at h2 ⊢
      exact ⟨h2, rfl⟩
    -- (e) `ζ ∘ G` is `KΛ`-Lipschitz on `B_{r₁}(0)`
    have hGM : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M := fun a ha =>
      ((hMW.symm ▸ mem_image_of_mem G ha : G a ∈ M ∩ W)).1
    have hgL : LipschitzOnWith (K * Λ) (ζ ∘ G) (ball 0 r₁) :=
      hKt.comp (hGL.mono hball) fun a ha => hUt ⟨hGM a (hball ha), hGU (mem_image_of_mem G ha)⟩
    -- (f) Rademacher: `ζ ∘ G` is differentiable off the `Lᵐ`-null set `N`
    let N : Set (Euclid m) := {a | a ∈ ball (0 : Euclid m) r₁ ∧ ¬ DifferentiableAt ℝ (ζ ∘ G) a}
    have hN : volume N = 0 := by
      have hrad := hgL.ae_differentiableWithinAt_of_mem (μ := volume)
      rw [ae_iff] at hrad
      refine measure_mono_null (fun a ha => ?_) hrad
      simp only [mem_ofPred_eq, not_imp]
      exact ⟨ha.1, fun hd => ha.2 (hd.differentiableAt (isOpen_ball.mem_nhds ha.1))⟩
    refine ⟨O, hOo, hpO, G '' N, ?_, ?_⟩
    · -- (g) `Hᵐ(G(N)) ≤ Λᵐ Lᵐ(N) = 0`
      have h := (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r₁) Λ
        (hGL.mono hball)).1 N (fun a ha => ha.1)
      rw [hN, mul_zero] at h
      exact le_antisymm h zero_le
    · -- (h) off `G(N)`, `ζ` agrees on `M ∩ O` with `(ζ ∘ G)(pr(· − p))`, differentiable at `x`
      intro x hx hxE
      obtain ⟨ha, hGa⟩ := hMO x hx
      have hdiffa : DifferentiableAt ℝ (ζ ∘ G) (pr (x - p)) := by
        by_contra hnd
        exact hxE ⟨pr (x - p), ⟨ha, hnd⟩, hGa⟩
      have hpr' : DifferentiableAt ℝ (fun z : Euclid P => pr (z - p)) x := by fun_prop
      have hf : DifferentiableAt ℝ ((ζ ∘ G) ∘ fun z : Euclid P => pr (z - p)) x :=
        hdiffa.comp x hpr'
      refine hf.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [inter_mem_nhdsWithin M (hOo.mem_nhds hx.2)] with y hy
        simp only [Function.comp_apply, (hMO y ⟨hy.1, hy.2⟩).2]
      · simp only [Function.comp_apply, hGa]
  -- step 3: countably many of the neighbourhoods `O p` cover `M` (second countability)
  choose! O hOo hpO E hE hdiff using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hnull : μHE[m] (⋃ p ∈ T, E p) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun p hp => hE p (hTM hp)
  -- step 4: every point of `M` where `ζ` is not differentiable within `M` lies in `⋃_{p ∈ T} E p`
  rw [ae_restrict_iff' hMmeas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxM, hxnd⟩ := hx
  have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hxM, hpO x hxM⟩
  rw [← hTU] at hxU
  obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
  refine mem_iUnion₂.2 ⟨p, hpT, ?_⟩
  by_contra hxE
  exact hxnd (hdiff p (hTM hpT) x ⟨hxM, hxO⟩ hxE)
/-- **Measurability of the tangential derivative of a Lipschitz function** (Simon Ch. 2, §4; used
in 7.5).  Let `M ⊆ ℝᴾ` be an embedded `C¹` `m`-dimensional submanifold, `ζ` locally Lipschitz on
`M`, and `P_x` the orthogonal projection onto `T_xM`.  Then `x ↦ d^M_xζ ∘ P_x` is `Hᵐ⌞M`-a.e.
strongly measurable.  On a graph chart `G : B_r(0) → M ∩ W` about `p` with `pr(G(a) − p) = a`,
`pr ∘ DG(a) = id` and `T_{G(a)}M = DG(a)(ℝᵐ)`, the map `Ψ(x) = D(ζ ∘ G)(pr(x − p)) ∘ pr ∘ P_x` is
a.e. strongly measurable (`D(ζ ∘ G)` is Borel and `x ↦ P_x` is continuous on `M`).  Where `ζ` is
differentiable within `M` (`Hᵐ`-a.e. on `M`, by Rademacher), the chain rule gives
`D(ζ ∘ G)(a) = d^M_xζ ∘ DG(a)` and `P_xv = DG(a)(pr P_xv)`, so `Ψ(x) = d^M_xζ ∘ P_x`.  Countably
many chart domains cover `M`. -/
theorem Submission.codim1_hcp_lsa_tangential_derivative_aesm : ∀ (P m : ℕ) (M : Set (Euclid P)) (ζ : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M ζ → AEStronglyMeasurable (fun x => (fderivWithin ℝ ζ M x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection) (μHE[m].restrict M) := by
  intro P m M ζ hM hζ
  -- step 1: `M` is Borel, `ζ` is differentiable within `M` a.e. on `M`, `x ↦ P_x` is continuous
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  have hdiff := Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M ζ hM hζ
  have hPc := Submission.codim1_hcp_lsa_tangent_projection_continuousOn P m M hM
  set F : Euclid P → (Euclid P →L[ℝ] ℝ) := fun x =>
    (fderivWithin ℝ ζ M x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection with hF
  -- step 2: `F` is a.e. strongly measurable on `M ∩ W` for a graph-chart domain `W ∋ p`
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧
      AEStronglyMeasurable F (μHE[m].restrict (M ∩ O)) := by
    intro p hp
    obtain ⟨pr, G, r, W, -, -, hWo, hpW, -, -, hGc, -, hMW, hleft, hderiv, htan⟩ :=
      Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
    refine ⟨W, hWo, hpW, ?_⟩
    have hMWm : MeasurableSet (M ∩ W) := hMmeas.inter hWo.measurableSet
    -- (b) the chart representative `Ψ(x) = D(ζ ∘ G)(pr(x − p)) ∘ pr ∘ P_x` is measurable
    set Ψ : Euclid P → (Euclid P →L[ℝ] ℝ) := fun x =>
      (fderiv ℝ (ζ ∘ G) (pr (x - p))).comp
        (pr.comp (Submodule.span ℝ (tangentSpace M x)).starProjection) with hΨ
    have hΨm : AEStronglyMeasurable Ψ (μHE[m].restrict (M ∩ W)) := by
      have h1 : Measurable (fun x : Euclid P => fderiv ℝ (ζ ∘ G) (pr (x - p))) :=
        (measurable_fderiv ℝ (ζ ∘ G)).comp (by fun_prop)
      have h2 : ContinuousOn (fun x => pr.comp (Submodule.span ℝ (tangentSpace M x)).starProjection)
          (M ∩ W) :=
        ((ContinuousLinearMap.compL ℝ (Euclid P) (Euclid P) (Euclid m) pr).continuous
          |>.comp_continuousOn hPc).mono inter_subset_left
      exact isBoundedBilinearMap_comp.continuous.comp_aestronglyMeasurable
        (h1.aestronglyMeasurable.prodMk (h2.aestronglyMeasurable hMWm))
    -- (c) `Ψ = F` at every `x ∈ M ∩ W` where `ζ` is differentiable within `M`
    refine hΨm.congr ?_
    have hdiff' : ∀ᵐ x ∂(μHE[m].restrict (M ∩ W)), DifferentiableWithinAt ℝ ζ M x :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hdiff
    filter_upwards [hdiff', ae_restrict_mem hMWm] with x hxd hxMW
    -- `x = G a` with `a = pr (x - p)`
    have hxMW' := hxMW
    rw [hMW] at hxMW'
    obtain ⟨a, ha, rfl⟩ := hxMW'
    simp only [hΨ, hF]
    rw [hleft a ha]
    -- chain rule: `D(ζ ∘ G)(a) = d^M_{G a}ζ ∘ DG(a)`
    have hGM : MapsTo G (ball 0 r) M :=
      fun b hb => (hMW.symm ▸ mem_image_of_mem G hb : G b ∈ M ∩ W).1
    have hGd : HasFDerivAt G (fderiv ℝ G a) a :=
      ((hGc.contDiffAt (isOpen_ball.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
    have hcomp : HasFDerivAt (ζ ∘ G) ((fderivWithin ℝ ζ M (G a)).comp (fderiv ℝ G a)) a :=
      (hxd.hasFDerivWithinAt.comp a hGd.hasFDerivWithinAt hGM).hasFDerivAt
        (isOpen_ball.mem_nhds ha)
    rw [hcomp.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    -- `P_x v ∈ T_{G a}M = DG(a)(ℝᵐ)`, so `P_x v = DG(a) h` and `pr (P_x v) = h`
    have hmem0 := Submodule.starProjection_apply_mem (Submodule.span ℝ (tangentSpace M (G a))) v
    have hle : Submodule.span ℝ (tangentSpace M (G a)) ≤
        LinearMap.range ((fderiv ℝ G a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
      rw [Submodule.span_le, htan a ha]
      rintro _ ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    have hmem : ∃ h, (fderiv ℝ G a) h =
        (Submodule.span ℝ (tangentSpace M (G a))).starProjection v :=
      LinearMap.mem_range.1 (hle hmem0)
    obtain ⟨h, hh⟩ := hmem
    rw [← hh]
    congr 1
    have := congrArg (fun L => L h) (hderiv a ha)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    rw [this]
  -- step 3: countably many chart domains `O p`, `p ∈ T`, cover `M`
  choose! O hOo hpO hO using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hcount : Countable T := hTc.to_subtype
  have hMU : M = ⋃ i : T, M ∩ O i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff]
    constructor
    · intro hx
      have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hx, hpO x hx⟩
      rw [← hTU] at hxU
      obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
      exact ⟨⟨p, hpT⟩, hx, hxO⟩
    · rintro ⟨i, hx, -⟩
      exact hx
  -- step 4: a.e. strong measurability passes to the countable union
  rw [hMU]
  exact aestronglyMeasurable_iUnion_iff.2 fun i => hO i.1 (hTM i.2)

/-- **Smooth approximation in one graph chart** (Simon Ch. 2, §4, 4.4–4.9; Lipschitz test
functions in App. B, proof of B.2, used for 7.5.8).  `W` is the domain of a `C¹` graph chart at `p`:
`M ∩ W = G(B_r(0))`, `pr(G(a) − p) = a`.  If `ζ` is locally Lipschitz on `M` and vanishes off a
compact `C ⊆ M ∩ W`, then `g = ζ ∘ G` on `B_r(0)` (`0` outside) is Lipschitz and vanishes off
`S = pr(C − p)`.  Mollify `g` to `gₖ`, supported in `T = cthickening δ S`, and put
`ζₖ = β · gₖ ∘ pr(· − p)` with `β` smooth, `= 1` near `C' = G(T)` and `tsupport β ⊆ W`.
`H^m`-a.e. on `M ∩ W` (Rademacher) the tangential error is `(Dgₖ(a) − Dg(a))(pr Pₓeⱼ)`,
`a = pr(x − p)`, whose squares sum to at most `‖Dgₖ(a) − Dg(a)‖²`; off `W` it vanishes.  The
Lipschitz area bound moves the error integral to `B_r(0)`, where it tends to `0`. -/
theorem Submission.codim1_hcp_lsa_local_chart_approx : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → ∀ p ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ p ∈ W ∧ ∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∩ W ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
  classical
  intro P m M hM p hp
  -- step 1: the graph chart at `p`; its domain `W` is the asserted neighbourhood
  obtain ⟨pr, G, r, W, Λ, hr, hWo, hpW, hpr, hG0, hGc, hGL, hMW, hleft, hderiv, htan⟩ :=
    Submission.codim1_hcp_lsa_c1_graph_chart P m M p hM hp
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  refine ⟨W, hWo, hpW, ?_⟩
  rintro ζ hζ ⟨C, hCc, hCMW, hζC⟩
  have hGMW : ∀ a ∈ ball (0 : Euclid m) r, G a ∈ M ∩ W := fun a ha => by
    rw [hMW]; exact mem_image_of_mem G ha
  have hrep : ∀ x ∈ M ∩ W, pr (x - p) ∈ ball (0 : Euclid m) r ∧ G (pr (x - p)) = x := by
    intro x hx
    rw [hMW] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hleft a ha]; exact ⟨ha, rfl⟩
  have hGcont : ContinuousOn G (ball 0 r) := hGc.continuousOn
  -- step 2: the compact parameter sets `S = pr(C − p) ⊆ T = cthickening δ S ⊆ B_r(0)`
  set S : Set (Euclid m) := (fun x => pr (x - p)) '' C with hS
  have hSc : IsCompact S := hCc.image (by fun_prop)
  have hSball : S ⊆ ball 0 r := by
    rintro _ ⟨x, hx, rfl⟩; exact (hrep x (hCMW hx)).1
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := hSc.exists_cthickening_subset_open isOpen_ball hSball
  set δ : ℝ := δ₀ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  set T : Set (Euclid m) := Metric.cthickening δ S with hT
  have hTc : IsCompact T := hSc.cthickening
  have hTball : T ⊆ ball 0 r := (Metric.cthickening_mono (by linarith) S).trans hδ₀sub
  have hST : S ⊆ T := Metric.self_subset_cthickening S
  -- step 3: the coordinate function `g = ζ ∘ G` on `B_r(0)`, `0` outside; `g = 0` off `S`
  set g : Euclid m → ℝ := fun a => if a ∈ ball (0 : Euclid m) r then ζ (G a) else 0 with hg
  have hg_ball : ∀ a ∈ ball (0 : Euclid m) r, g a = ζ (G a) := fun a ha => ite_eq_left ha
  have hg0 : ∀ a, a ∉ S → g a = 0 := by
    intro a ha
    by_cases hab : a ∈ ball (0 : Euclid m) r
    · rw [hg_ball a hab]
      refine hζC (G a) (hGMW a hab).1 fun hGC => ha ?_
      exact ⟨G a, hGC, hleft a hab⟩
    · exact ite_eq_right hab
  -- (b) `ζ ∘ G` is locally Lipschitz on the ball, hence Lipschitz and bounded on `T`
  have hζG : LocallyLipschitzOn (ball (0 : Euclid m) r) (ζ ∘ G) := by
    intro a ha
    obtain ⟨K, t, ht, hKt⟩ := hζ (hGMW a ha).1
    have ht' : t ∈ 𝓝[G '' ball 0 r] (G a) :=
      nhdsWithin_mono _ (fun y hy => by rw [← hMW] at hy; exact hy.1) ht
    refine ⟨K * Λ, G ⁻¹' t ∩ ball 0 r, ?_, ?_⟩
    · exact inter_mem ((hGcont a ha).preimage_mem_nhdsWithin' ht') self_mem_nhdsWithin
    · exact hKt.comp (hGL.mono inter_subset_right) fun b hb => hb.1
  obtain ⟨K₁, hK₁⟩ := (hζG.mono hTball).exists_lipschitzOnWith_of_compact hTc
  obtain ⟨B, hB⟩ := hTc.exists_bound_of_continuousOn (hK₁.continuousOn)
  -- (c) `g` is globally Lipschitz with constant `max(K₁, B/δ)`
  have hgLip : LipschitzWith (max K₁ (Real.toNNReal (B / δ))) g := by
    have hgT : ∀ a ∈ T, g a = ζ (G a) := fun a ha => hg_ball a (hTball ha)
    have hfar : ∀ a b, a ∈ S → b ∉ T →
        dist (g a) (g b) ≤ max K₁ (Real.toNNReal (B / δ)) * dist a b := by
      intro a b ha hb
      have hgb : g b = 0 := hg0 b fun h => hb (hST h)
      have hdist : δ < dist a b := by
        by_contra hle
        exact hb (Metric.mem_cthickening_of_dist_le b a δ S ha (by rw [dist_comm]; linarith))
      rw [hgb, dist_zero_right]
      have hBa : ‖g a‖ ≤ B := by rw [hgT a (hST ha)]; exact hB a (hST ha)
      have hB0 : 0 ≤ B := le_trans (norm_nonneg _) hBa
      calc ‖g a‖ ≤ B := hBa
        _ ≤ B / δ * dist a b := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
            exact mul_le_mul_of_nonneg_left hdist.le hB0
        _ ≤ (Real.toNNReal (B / δ) : ℝ) * dist a b :=
            mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg
        _ ≤ (max K₁ (Real.toNNReal (B / δ)) : ℝ) * dist a b := by
            gcongr; exact le_max_right _ _
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    by_cases ha : a ∈ T <;> by_cases hb : b ∈ T
    · rw [hgT a ha, hgT b hb]
      calc dist (ζ (G a)) (ζ (G b)) ≤ K₁ * dist a b := hK₁.dist_le_mul a ha b hb
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · by_cases haS : a ∈ S
      · exact hfar a b haS hb
      · rw [hg0 a haS, hg0 b fun h => hb (hST h), dist_self]; positivity
    · by_cases hbS : b ∈ S
      · rw [dist_comm, dist_comm a b]; exact hfar b a hbS ha
      · rw [hg0 a fun h => ha (hST h), hg0 b hbS, dist_self]; positivity
    · rw [hg0 a fun h => ha (hST h), hg0 b fun h => hb (hST h), dist_self]; positivity
  -- step 4: mollification
  obtain ⟨gs, hgs_smooth, hgs_supp, hgs_unif, hgs_L2⟩ :=
    Submission.codim1_hcp_lsa_mollify_lipschitz_compact_support m g _ S δ hgLip hSc hg0 hδpos
  -- step 5: the cutoff `β`, smooth, `= 1` near `K' = G(T)`, `tsupport β ⊆ W`
  set K' : Set (Euclid P) := G '' T with hK'
  have hK'c : IsCompact K' := hTc.image_of_continuousOn (hGcont.mono hTball)
  have hK'MW : K' ⊆ M ∩ W := by rintro _ ⟨a, ha, rfl⟩; exact hGMW a (hTball ha)
  obtain ⟨ε, hε, hεW⟩ := hK'c.exists_cthickening_subset_open hWo fun x hx => (hK'MW hx).2
  obtain ⟨β, hβs, hβr, hβsupp, hβ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (Metric.isOpen_thickening (δ := ε) (E := K'))
    (Metric.isClosed_cthickening (δ := ε / 2) (E := K'))
    (Metric.cthickening_subset_thickening' hε (by linarith) K')
  have htsβ : tsupport β ⊆ Metric.cthickening ε K' := by
    rw [tsupport, hβsupp]; exact Metric.closure_thickening_subset_cthickening ε K'
  have hβcs : HasCompactSupport β :=
    hK'c.cthickening.of_isClosed_subset (isClosed_tsupport β) htsβ
  have hβ0 : ∀ x, x ∉ W → x ∉ tsupport β := fun x hx h => hx (hεW (htsβ h))
  have hβone : ∀ x ∈ Metric.thickening (ε / 2) K', β x = 1 := fun x hx =>
    (hβ1 x).1 (Metric.thickening_subset_cthickening _ _ hx)
  have hK'thick : K' ⊆ Metric.thickening (ε / 2) K' :=
    Metric.self_subset_thickening (by positivity) K'
  have hprc : ContDiff ℝ (⊤ : ℕ∞) (fun z : Euclid P => pr (z - p)) := by fun_prop
  -- step 6: the approximants `ζₖ = β · gₖ ∘ pr(· − p)` and `C' = K'`
  refine ⟨K', fun k z => β z * gs k (pr (z - p)), hK'c, fun x hx => (hK'MW hx).1,
    fun k => ⟨hβs.mul ((hgs_smooth k).comp hprc), hβcs.mul_right⟩, ?_, ?_, ?_⟩
  · -- step 7: `ζₖ = 0` on `M \ K'`
    intro k x hxM hxK
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have haT : pr (x - p) ∉ T := fun h => hxK ⟨_, h, hGa⟩
      simp only [hgs_supp k _ haT, mul_zero]
    · simp only [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul]
  · -- step 8: uniform convergence on `M`, read off in chart coordinates
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    filter_upwards [Metric.tendstoUniformly_iff.1 hgs_unif ε' hε'] with k hk x hxM
    by_cases hxW : x ∈ W
    · obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
      have hζx : ζ x = g (pr (x - p)) := by rw [hg_ball _ ha, hGa]
      by_cases haT : pr (x - p) ∈ T
      · rw [hβone x (hK'thick ⟨_, haT, hGa⟩), one_mul, hζx]; exact hk _
      · rw [hgs_supp k _ haT, mul_zero, hζx, hg0 _ fun h => haT (hST h), dist_self]; exact hε'
    · rw [image_eq_zero_of_notMem_tsupport (hβ0 x hxW), zero_mul,
        hζC x hxM fun h => hxW (hCMW h).2, dist_self]
      exact hε'
  · -- steps 9–11: the tangential gradient error
    set w : Euclid P → Fin P → Euclid P := fun x j =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1) with hw
    -- step 9: `∑ⱼ λ(pr(Pₓeⱼ))² ≤ ‖λ‖²`, via the Riesz vector of `λ ∘ pr ∘ Pₓ`
    have halg : ∀ (l : Euclid m →L[ℝ] ℝ) (x : Euclid P),
        ∑ j : Fin P, (l (pr (w x j))) ^ 2 ≤ ‖l‖ ^ 2 := by
      intro l x
      set ℓ : Euclid P →L[ℝ] ℝ :=
        (l.comp pr).comp (Submodule.span ℝ (tangentSpace M x)).starProjection
      set u : Euclid P := (InnerProductSpace.toDual ℝ (Euclid P)).symm ℓ
      have hu : ∀ v, ℓ v = inner ℝ u v := fun v => (InnerProductSpace.toDual_symm_apply).symm
      have hcoord : ∀ j : Fin P, l (pr (w x j)) = u j := by
        intro j
        have := hu (EuclideanSpace.single j 1)
        rw [EuclideanSpace.inner_single_right] at this
        simpa [ℓ, w] using this
      have hnorm : ‖u‖ = ‖ℓ‖ := LinearIsometryEquiv.norm_map _ _
      have hℓ : ‖ℓ‖ ≤ ‖l‖ := by
        calc ‖ℓ‖ ≤ ‖l.comp pr‖ * ‖(Submodule.span ℝ (tangentSpace M x)).starProjection‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ (‖l‖ * ‖pr‖) * 1 := by
              gcongr
              · exact ContinuousLinearMap.opNorm_comp_le _ _
              · exact Submodule.starProjection_norm_le _
          _ ≤ ‖l‖ * 1 * 1 := by gcongr
          _ = ‖l‖ := by ring
      calc ∑ j : Fin P, (l (pr (w x j))) ^ 2 = ∑ j : Fin P, (u j) ^ 2 := by simp_rw [hcoord]
        _ = ‖u‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq u).symm
        _ ≤ ‖l‖ ^ 2 := by rw [hnorm]; gcongr
    -- the Borel chart majorant `Hₖ(z) = ‖Dgₖ(pr(z − p)) − Dg(pr(z − p))‖²`
    set H : ℕ → Euclid P → ℝ≥0∞ := fun k z =>
      ENNReal.ofReal (‖fderiv ℝ (gs k) (pr (z - p)) - fderiv ℝ g (pr (z - p))‖ ^ 2) with hH
    have hHm : ∀ k, Measurable (H k) := by
      intro k
      have h1 : Measurable fun z : Euclid P => fderiv ℝ (gs k) (pr (z - p)) :=
        (measurable_fderiv ℝ (gs k)).comp (by fun_prop)
      have h2 : Measurable fun z : Euclid P => fderiv ℝ g (pr (z - p)) :=
        (measurable_fderiv ℝ g).comp (by fun_prop)
      exact ((h1.sub h2).norm.pow_const 2).ennreal_ofReal
    have hζdiff := Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M ζ hM hζ
    -- step 10: the pointwise bound by `1_W · Hₖ`, `H^m`-a.e. on `M`
    have hpt : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
          fderivWithin ℝ ζ M x (w x j)) ^ 2) ≤ W.indicator (H k) x := by
      intro k
      filter_upwards [hζdiff, ae_restrict_mem hMmeas] with x hxd hxM
      by_cases hxW : x ∈ W
      · rw [indicator_of_mem hxW]
        obtain ⟨ha, hGa⟩ := hrep x ⟨hxM, hxW⟩
        set a := pr (x - p) with ha_def
        -- (i) `Dg(a) = d^M_xζ ∘ DG(a)`
        have hGd : HasFDerivAt G (fderiv ℝ G a) a :=
          ((hGc.contDiffAt (isOpen_ball.mem_nhds ha)).differentiableAt one_ne_zero).hasFDerivAt
        have hGM : MapsTo G (ball 0 r) M := fun b hb => (hGMW b hb).1
        have hcomp : HasFDerivAt (ζ ∘ G) ((fderivWithin ℝ ζ M x).comp (fderiv ℝ G a)) a := by
          have hxd' : HasFDerivWithinAt ζ (fderivWithin ℝ ζ M x) M (G a) := by
            rw [hGa]; exact hxd.hasFDerivWithinAt
          exact (hxd'.comp a hGd.hasFDerivWithinAt hGM).hasFDerivAt (isOpen_ball.mem_nhds ha)
        have hgeq : g =ᶠ[𝓝 a] ζ ∘ G := by
          filter_upwards [isOpen_ball.mem_nhds ha] with b hb
          exact hg_ball b hb
        have hDg : fderiv ℝ g a = (fderivWithin ℝ ζ M x).comp (fderiv ℝ G a) :=
          (hcomp.congr_of_eventuallyEq hgeq).fderiv
        -- (ii) `Dζₖ(x) = Dgₖ(a) ∘ pr`
        have hDζs : fderiv ℝ (fun z => β z * gs k (pr (z - p))) x =
            (fderiv ℝ (gs k) a).comp pr := by
          have hprd : HasFDerivAt (fun z : Euclid P => pr (z - p)) pr x := by
            have h := (pr.hasFDerivAt (x := x - p)).comp x ((hasFDerivAt_id x).sub_const p)
            rw [ContinuousLinearMap.comp_id] at h
            exact h
          by_cases haT : a ∈ T
          · have hxK : x ∈ Metric.thickening (ε / 2) K' := hK'thick ⟨a, haT, hGa⟩
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x]
                fun z => gs k (pr (z - p)) := by
              filter_upwards [Metric.isOpen_thickening.mem_nhds hxK] with z hz
              rw [hβone z hz, one_mul]
            rw [heq.fderiv_eq]
            have hgsd : HasFDerivAt (gs k) (fderiv ℝ (gs k) a) a :=
              ((hgs_smooth k).differentiable (by simp) a).hasFDerivAt
            exact (hgsd.comp x hprd).fderiv
          · have hnhds : (fun z : Euclid P => pr (z - p)) ⁻¹' Tᶜ ∈ 𝓝 x :=
              (Metric.isClosed_cthickening.isOpen_compl.preimage (by fun_prop)).mem_nhds haT
            have heq : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
              filter_upwards [hnhds] with z hz
              rw [hgs_supp k _ hz, mul_zero]
            have hga : gs k =ᶠ[𝓝 a] fun _ => (0 : ℝ) := by
              filter_upwards [Metric.isClosed_cthickening.isOpen_compl.mem_nhds haT] with b hb
              exact hgs_supp k b hb
            rw [heq.fderiv_eq, hga.fderiv_eq]
            simp
        -- (iii) `Pₓeⱼ = DG(a)(pr(Pₓeⱼ))`, since `T_xM = range DG(a)` and `pr ∘ DG(a) = id`
        have hwj : ∀ j, fderiv ℝ G a (pr (w x j)) = w x j := by
          intro j
          have hmem0 := Submodule.starProjection_apply_mem (Submodule.span ℝ (tangentSpace M x))
            (EuclideanSpace.single j (1 : ℝ))
          have hle : Submodule.span ℝ (tangentSpace M x) ≤ LinearMap.range
              ((fderiv ℝ G a : Euclid m →L[ℝ] Euclid P) : Euclid m →ₗ[ℝ] Euclid P) := by
            rw [Submodule.span_le, ← hGa, htan a ha]
            rintro _ ⟨y, rfl⟩
            exact ⟨y, rfl⟩
          obtain ⟨h, hh⟩ := LinearMap.mem_range.1 (hle hmem0)
          have hh' : fderiv ℝ G a h = w x j := hh
          rw [← hh']
          congr 1
          have := congrArg (fun T => T h) (hderiv a ha)
          simpa using this
        -- (iv) the error is `(Dgₖ(a) − Dg(a))(pr(Pₓeⱼ))`; apply step 9
        have herr : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = (fderiv ℝ (gs k) a - fderiv ℝ g a) (pr (w x j)) := by
          intro j
          rw [hDζs, hDg]
          simp only [ContinuousLinearMap.comp_apply, sub_apply, hwj j]
        simp_rw [herr]
        exact ENNReal.ofReal_le_ofReal (halg _ x)
      · rw [indicator_of_notMem hxW]
        -- off `W`: `ζₖ = 0` near `x`, and `ζ` has derivative `0` within `M` at `x`
        have hxC : x ∉ C := fun h => hxW (hCMW h).2
        have hz1 : (fun z => β z * gs k (pr (z - p))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 (hβ0 x hxW))] with z hz
          rw [hz, Pi.zero_apply, zero_mul]
        have hz2 : HasFDerivWithinAt ζ (0 : Euclid P →L[ℝ] ℝ) M x := by
          have h0 : HasFDerivWithinAt (fun _ : Euclid P => (0 : ℝ)) (0 : Euclid P →L[ℝ] ℝ) M x :=
            hasFDerivWithinAt_const 0 x M
          refine h0.congr_of_eventuallyEq ?_ (hζC x hxM hxC)
          filter_upwards [inter_mem_nhdsWithin M (hCc.isClosed.isOpen_compl.mem_nhds hxC)]
            with y hy
          exact hζC y hy.1 hy.2
        have hterm : ∀ j, fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j) = 0 := by
          intro j
          rw [hz1.fderiv_eq,
            Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span P M ζ 0 x (w x j) hz2
              (Submodule.starProjection_apply_mem _ _)]
          simp
        have hsum0 : ∑ j : Fin P, (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
            fderivWithin ℝ ζ M x (w x j)) ^ 2 = 0 := by
          simp only [hterm]; simp
        rw [hsum0, ENNReal.ofReal_zero]
    -- step 11: integrate, transfer to the chart ball, and pass to the limit
    have hint : ∀ k, ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (fun z => β z * gs k (pr (z - p))) x (w x j) -
          fderivWithin ℝ ζ M x (w x j)) ^ 2) ∂μHE[m] ≤ (Λ : ℝ≥0∞) ^ m *
            ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
      intro k
      have hWm : MeasurableSet W := hWo.measurableSet
      calc _ ≤ ∫⁻ x in M, W.indicator (H k) x ∂μHE[m] := lintegral_mono_ae (hpt k)
        _ = ∫⁻ x in G '' ball 0 r, H k x ∂μHE[m] := by
            rw [lintegral_indicator hWm, Measure.restrict_restrict hWm, inter_comm, hMW]
        _ ≤ (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r, H k (G a) :=
            (Submission.codim1_hcp_lsa_lipschitz_image_lintegral_le m P G (ball 0 r) Λ hGL).2
              measurableSet_ball (H k) (hHm k)
        _ = (Λ : ℝ≥0∞) ^ m * ∫⁻ a in ball (0 : Euclid m) r,
              ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2) := by
            congr 1
            refine setLIntegral_congr_fun measurableSet_ball fun a ha => ?_
            simp only [hH, hleft a ha]
        _ ≤ _ := mul_le_mul_right (setLIntegral_le_lintegral _ _) _
    have hlim : Tendsto (fun k => (Λ : ℝ≥0∞) ^ m *
        ∫⁻ a, ENNReal.ofReal (‖fderiv ℝ (gs k) a - fderiv ℝ g a‖ ^ 2)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (Λ : ℝ≥0∞) ^ m) hgs_L2
        (Or.inr (ENNReal.pow_ne_top ENNReal.coe_ne_top))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hint
/-- **Calculus of locally Lipschitz functions on a `C¹` submanifold** (Simon Ch. 2, 4.4–4.9).
Let `M ⊆ ℝᴾ` be an embedded `C¹` `m`-submanifold and `P_x` the orthogonal projection onto
`span T_xM`.  (i) For `ζ` locally Lipschitz on `M`, `x ↦ d^M_xζ(P_xe_j)` is a.e. strongly
measurable for `Hᵐ⌞M`: evaluate the a.e. strongly measurable operator `d^M_xζ ∘ P_x` at `e_j`.
(ii) If moreover `ζ = 0` on `M` off a compact `C ⊆ M`, cover `C` by finitely many open sets
`W_p ∩ B₁(p)`, `p ∈ C`, where `W_p` carries one-chart approximations, and split `ζ = Σᵢ χᵢζ` on
`M` by a smooth partition of unity `χᵢ` on `C` subordinate to this cover.  Each piece `χᵢζ` is
locally Lipschitz on `M` and vanishes on `M` off the compact `C ∩ spt χᵢ`, so it has approximants
`ζ_{i,k}`; put `ζ_k = Σᵢ ζ_{i,k}`.  At `Hᵐ`-a.e. `x ∈ M` every piece is differentiable within `M`,
so `d^M_xζ = Σᵢ d^M_x(χᵢζ)` on `span T_xM`, and Cauchy–Schwarz over the pieces bounds the
gradient error of `ζ_k` by `#pieces` times the sum of the (a.e. measurable) errors of the pieces,
each of which tends to `0`. -/
theorem Submission.codim1_hcp_lipschitz_smooth_approx : ∀ (P m : ℕ) (M : Set (Euclid P)), IsEmbeddedSubmanifold 1 m M → (∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
  intro P m M hM
  have hMmeas : MeasurableSet M := (Submission.dimred_rpd_embedded_locally_closed P 1 m M hM).1
  -- the tangent projections `P_x e_j` are a.e. strongly measurable on `M`
  have hPj : ∀ j : Fin P, AEStronglyMeasurable
      (fun x => (Submodule.span ℝ (tangentSpace M x)).starProjection
        (EuclideanSpace.single j (1 : ℝ))) (μHE[m].restrict M) := by
    intro j
    have hc := Submission.codim1_hcp_lsa_tangent_projection_continuousOn P m M hM
    exact ((ContinuousLinearMap.apply ℝ (Euclid P)
      (EuclideanSpace.single j (1 : ℝ))).continuous.comp_continuousOn hc).aestronglyMeasurable
        hMmeas
  -- part (i): evaluate the operator `d^M_xζ ∘ P_x` at `e_j`
  have part_i : ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P,
      AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)))
        (μHE[m].restrict M) := by
    intro ζ hζ j
    exact (ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.single j (1 : ℝ))).continuous.comp_aestronglyMeasurable
        (Submission.codim1_hcp_lsa_tangential_derivative_aesm P m M ζ hM hζ)
  refine ⟨part_i, ?_⟩
  -- part (ii)
  rintro ζ hζ ⟨C, hCc, hCM, hζC⟩
  -- open sets `W p ∋ p` carrying one-chart approximations
  choose! W hWo hpW hWapprox using Submission.codim1_hcp_lsa_local_chart_approx P m M hM
  -- a finite subcover of `C` by the sets `W p ∩ B₁(p)`, `p ∈ C`
  obtain ⟨t, htC, hCt⟩ := hCc.elim_nhds_subcover (fun p => W p ∩ ball p 1) fun p hp =>
    ((hWo p (hCM hp)).inter isOpen_ball).mem_nhds ⟨hpW p (hCM hp), mem_ball_self one_pos⟩
  let ι := {p // p ∈ t}
  let U : ι → Set (Euclid P) := fun i => W i.1 ∩ ball i.1 1
  have hUo : ∀ i, IsOpen (U i) := fun i => (hWo i.1 (hCM (htC i.1 i.2))).inter isOpen_ball
  have hCU : C ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (hCt hx)
    exact mem_iUnion.2 ⟨⟨p, hp⟩, hxp⟩
  -- a smooth partition of unity `χᵢ = f i` on `C` subordinate to the cover
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Euclid P)) hCc.isClosed U hUo hCU
  have hfsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) := fun i =>
    contMDiff_iff_contDiff.1 (f i).contMDiff
  have hfsum : ∀ x ∈ C, ∑ i, f i x = 1 := by
    intro x hx
    rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx
  -- the pieces `ζᵢ = χᵢ ζ`, with `ζ = Σᵢ ζᵢ` on `M`
  let ζi : ι → Euclid P → ℝ := fun i x => f i x * ζ x
  have hζeq : ∀ x ∈ M, ζ x = ∑ i, ζi i x := by
    intro x hx
    by_cases hxC : x ∈ C
    · simp only [ζi, ← Finset.sum_mul, hfsum x hxC, one_mul]
    · simp [ζi, hζC x hx hxC]
  -- each piece is locally Lipschitz on `M`: near `x`, `χᵢ` is Lipschitz with values in `[0, 1]`
  -- and `ζ` is Lipschitz and bounded by `|ζ x| + K`
  have hζiLip : ∀ i, LocallyLipschitzOn M (ζi i) := by
    intro i x hx
    obtain ⟨K, s, hs, hKs⟩ := hζ hx
    obtain ⟨L, u, hu, hLu⟩ := ((hfsmooth i).of_le (by exact_mod_cast le_top)).locallyLipschitz x
    have hxs : x ∈ s := mem_of_mem_nhdsWithin hx hs
    refine ⟨K + Real.toNNReal (|ζ x| + K) * L, s ∩ u ∩ closedBall x 1,
      inter_mem (inter_mem hs (mem_nhdsWithin_of_mem_nhds hu))
        (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x one_pos)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    have hζyz := hKs.dist_le_mul y hy.1.1 z hz.1.1
    have hfyz := hLu.dist_le_mul y hy.1.2 z hz.1.2
    have hζz : |ζ z| ≤ |ζ x| + K := by
      have h1 := hKs.dist_le_mul z hz.1.1 x hxs
      have h2 : dist z x ≤ 1 := hz.2
      rw [Real.dist_eq] at h1
      have h3 : |ζ z| ≤ |ζ x| + |ζ z - ζ x| := by
        have := abs_add_le (ζ x) (ζ z - ζ x); simpa using this
      nlinarith [abs_nonneg (ζ z - ζ x), NNReal.coe_nonneg K]
    have hfy : |f i y| ≤ 1 := by rw [abs_of_nonneg (f.nonneg i y)]; exact f.le_one i y
    rw [Real.dist_eq] at hζyz hfyz ⊢
    have hkey : f i y * ζ y - f i z * ζ z =
        f i y * (ζ y - ζ z) + ζ z * (f i y - f i z) := by ring
    simp only [ζi]
    rw [hkey]
    have hdist : 0 ≤ dist y z := dist_nonneg
    calc |f i y * (ζ y - ζ z) + ζ z * (f i y - f i z)|
        ≤ |f i y| * |ζ y - ζ z| + |ζ z| * |f i y - f i z| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
      _ ≤ 1 * (K * dist y z) + (|ζ x| + K) * (L * dist y z) := by gcongr
      _ = ((K + Real.toNNReal (|ζ x| + K) * L : NNReal) : ℝ) * dist y z := by
          rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; ring
  -- one-chart approximations of the pieces
  have happ : ∀ i : ι, ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧
      C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧
      (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs (ζi i) atTop M ∧
      Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection
          (EuclideanSpace.single j 1)) - fderivWithin ℝ (ζi i) M x
          ((Submodule.span ℝ (tangentSpace M x)).starProjection
            (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0) := by
    intro i
    refine hWapprox i.1 (hCM (htC i.1 i.2)) (ζi i) (hζiLip i)
      ⟨C ∩ tsupport (f i), hCc.inter_right (isClosed_tsupport _), ?_, ?_⟩
    · -- `C ∩ spt χᵢ ⊆ M ∩ W pᵢ`
      intro x hx
      exact ⟨hCM hx.1, (hf i hx.2).1⟩
    · -- `ζᵢ = 0` on `M` off `C ∩ spt χᵢ`
      intro x hxM hx
      by_cases hxC : x ∈ C
      · have hxt : x ∉ tsupport (f i) := fun h => hx ⟨hxC, h⟩
        simp [ζi, image_eq_zero_of_notMem_tsupport hxt]
      · simp [ζi, hζC x hxM hxC]
  choose C'i ζsi hC'c hC'M hζsi hζsi0 hζsiU hζsiL using happ
  -- `C' = ⋃ᵢ C'ᵢ` and `ζ_k = Σᵢ ζ_{i,k}`
  refine ⟨⋃ i, C'i i, fun k => ∑ i, ζsi i k, isCompact_iUnion hC'c, iUnion_subset hC'M,
    fun k => ⟨?_, HasCompactSupport.finset_sum fun i _ => (hζsi i k).2⟩, ?_, ?_, ?_⟩
  · -- smoothness
    show ContDiff ℝ _ (∑ i, ζsi i k)
    rw [Finset.sum_fn]
    exact ContDiff.sum fun i _ => (hζsi i k).1
  · -- `ζ_k = 0` on `M ∖ C'`
    intro k x hx hxC'
    show (∑ i, ζsi i k) x = 0
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hζsi0 i k x hx fun h => hxC' (mem_iUnion.2 ⟨i, h⟩)
  · -- uniform convergence on `M`
    have hsum : ∀ s : Finset ι, TendstoUniformlyOn (fun k x => ∑ i ∈ s, ζsi i k x)
        (fun x => ∑ i ∈ s, ζi i x) atTop M := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact Metric.tendstoUniformlyOn_iff.2 fun ε hε =>
          Eventually.of_forall fun k x _ => by simpa using hε
      | insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hζsiU a).add ih
    refine ((hsum Finset.univ).congr_right fun x hx => (hζeq x hx).symm).congr ?_
    exact Eventually.of_forall fun k x _ => by simp [Finset.sum_apply]
  · -- convergence of the tangential gradients
    set w : Euclid P → Fin P → Euclid P := fun x j =>
      (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)
    have hwmem : ∀ x j, w x j ∈ Submodule.span ℝ (tangentSpace M x) := fun x j =>
      Submodule.starProjection_apply_mem _ _
    -- `Hᵐ`-a.e. on `M` every piece is differentiable within `M`
    have hdiff : ∀ᵐ x ∂(μHE[m].restrict M),
        x ∈ M ∧ ∀ i, DifferentiableWithinAt ℝ (ζi i) M x := by
      have h1 : ∀ i, ∀ᵐ x ∂(μHE[m].restrict M), DifferentiableWithinAt ℝ (ζi i) M x :=
        fun i => Submission.codim1_hcp_lsa_rademacher_on_submanifold P m M (ζi i) hM (hζiLip i)
      filter_upwards [ae_restrict_mem hMmeas, Filter.eventually_all.2 h1] with x hx hx'
      exact ⟨hx, hx'⟩
    -- there `d^M_xζ = Σᵢ d^M_xζᵢ` on `span T_xM`, so the error of `ζ_k` is the sum of the errors
    -- of the pieces
    have hsplit : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ∀ j,
        fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j) =
          ∑ i, (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j)) := by
      intro k
      filter_upwards [hdiff] with x hx j
      obtain ⟨hxM, hxd⟩ := hx
      have hsum : HasFDerivWithinAt (∑ i, ζi i) (∑ i, fderivWithin ℝ (ζi i) M x) M x :=
        HasFDerivWithinAt.sum fun i _ => (hxd i).hasFDerivWithinAt
      have hζd : HasFDerivWithinAt ζ (∑ i, fderivWithin ℝ (ζi i) M x) M x :=
        hsum.congr (fun y hy => by rw [Finset.sum_apply]; exact hζeq y hy)
          (by rw [Finset.sum_apply]; exact hζeq x hxM)
      have hW := Submission.codim1_hcp_lsa_fderivWithin_eq_on_tangent_span P M ζ _ x (w x j)
        hζd (hwmem x j)
      have hD : fderiv ℝ (∑ i, ζsi i k) x = ∑ i, fderiv ℝ (ζsi i k) x :=
        fderiv_sum fun i _ => ((hζsi i k).1.differentiable (by simp)).differentiableAt
      rw [hW, hD, sum_apply, sum_apply, ← Finset.sum_sub_distrib]
    -- the errors of the pieces are a.e. measurable
    set n : ℕ := Fintype.card ι with hn
    let Fi : ι → ℕ → Euclid P → ℝ≥0∞ := fun i k x => ENNReal.ofReal (∑ j : Fin P,
      (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j)) ^ 2)
    have hFi_meas : ∀ i k, AEMeasurable (Fi i k) (μHE[m].restrict M) := by
      intro i k
      refine AEMeasurable.ennreal_ofReal ?_
      refine (Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_).aemeasurable
      have hcont : Continuous (fderiv ℝ (ζsi i k)) := (hζsi i k).1.continuous_fderiv (by simp)
      have h1 : AEStronglyMeasurable (fun x => fderiv ℝ (ζsi i k) x (w x j))
          (μHE[m].restrict M) :=
        isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
          (hcont.aestronglyMeasurable.prodMk (hPj j))
      exact (h1.sub (part_i (ζi i) (hζiLip i) j)).pow 2
    -- pointwise Cauchy–Schwarz over the pieces
    have hbound : ∀ k, ∀ᵐ x ∂(μHE[m].restrict M), ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2) ≤
          (n : ℝ≥0∞) * ∑ i, Fi i k x := by
      intro k
      filter_upwards [hsplit k] with x hx
      have hcs : ∀ j : Fin P,
          (∑ i, (fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j))) ^ 2 ≤
            (n : ℝ) * ∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j)) ^ 2 := by
        intro j
        have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
          (fun i => fderiv ℝ (ζsi i k) x (w x j) - fderivWithin ℝ (ζi i) M x (w x j))
        simpa [hn] using this
      calc ENNReal.ofReal (∑ j : Fin P,
            (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2)
          = ENNReal.ofReal (∑ j : Fin P, (∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j))) ^ 2) := by simp_rw [hx]
        _ ≤ ENNReal.ofReal (∑ j : Fin P, (n : ℝ) * ∑ i, (fderiv ℝ (ζsi i k) x (w x j) -
              fderivWithin ℝ (ζi i) M x (w x j)) ^ 2) :=
            ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j _ => hcs j)
        _ = (n : ℝ≥0∞) * ∑ i, Fi i k x := by
            rw [← Finset.mul_sum, Finset.sum_comm, ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    -- integrate, split the finite sum, and pass to the limit
    have hint : ∀ k, ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (∑ i, ζsi i k) x (w x j) - fderivWithin ℝ ζ M x (w x j)) ^ 2) ∂μHE[m] ≤
          (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m] := by
      intro k
      calc _ ≤ ∫⁻ x in M, (n : ℝ≥0∞) * ∑ i, Fi i k x ∂μHE[m] :=
            lintegral_mono_ae (hbound k)
        _ = (n : ℝ≥0∞) * ∫⁻ x in M, ∑ i, Fi i k x ∂μHE[m] :=
            lintegral_const_mul' _ _ (ENNReal.natCast_ne_top n)
        _ = (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m] := by
            rw [lintegral_finsetSum' _ fun i _ => hFi_meas i k]
    have hlim : Tendsto (fun k => (n : ℝ≥0∞) * ∑ i, ∫⁻ x in M, Fi i k x ∂μHE[m])
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (tendsto_finsetSum Finset.univ fun i _ => hζsiL i)
        (Or.inr (ENNReal.natCast_ne_top n))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le) hint

/-- Near-isometric local parametrizations of an embedded `C¹` submanifold `M` (charts as in
Simon Ch. 2, (4.1)): for `z ∈ M` and `ε > 0` there are `χ` with `χ(0) = z` and `δ, δ' > 0` such
that `χ` is `(1 ± ε)`-bi-Lipschitz on `B_δ(0)`, `χ(B_δ(0)) ⊆ M` and `M ∩ B_{δ'}(z) ⊆ χ(B_δ(0))`.
Take a chart `ψ` with `ψ(v₀) = z`, choose `L ∈ GL(ℝⁿ)` with `Dψ(v₀) ∘ L` a linear isometry (an
orthonormal basis of `Dψ(v₀)(ℝⁿ)`) and put `χ(w) = ψ(v₀ + Lw)`; strict differentiability of `χ`
at `0` gives the two-point bounds, and continuity of the chart inverse
(`Submission.dsmc_chart_inverse_continuity`) gives the covering of `M ∩ B_{δ'}(z)`. -/
theorem Submission.dimred_rpd_near_isometric_chart : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → ∀ ε : ℝ, 0 < ε → ∃ (χ : Euclid n → Euclid P) (δ δ' : ℝ), 0 < δ ∧ 0 < δ' ∧ χ 0 = z ∧ (∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ, (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖) ∧ χ '' ball 0 δ ⊆ M ∧ M ∩ ball z δ' ⊆ χ '' ball 0 δ := by
  intro P n M z hM hz ε hε
  obtain ⟨V, W, ψ, hV, hW, hzW, hψ, hinj, himg, hprop, hder⟩ := hM z hz
  obtain ⟨v₀, hv₀V, hψv₀⟩ : z ∈ ψ '' V := by rw [himg]; exact ⟨hzW, hz⟩
  set A : Euclid n →L[ℝ] Euclid P := fderiv ℝ ψ v₀
  have hA : Injective A := hder v₀ hv₀V
  have hstrict : HasStrictFDerivAt ψ A v₀ :=
    (hψ.contDiffAt (hV.mem_nhds hv₀V)).hasStrictFDerivAt one_ne_zero
  -- isometric normalization
  obtain ⟨L, hLJ⟩ : ∃ L : Euclid n ≃L[ℝ] Euclid n, ∀ w, ‖A (L w)‖ = ‖w‖ := by
    let Q := LinearMap.range (A : Euclid n →ₗ[ℝ] Euclid P)
    have hfin : Module.finrank ℝ Q = n := by
      rw [LinearMap.finrank_range_of_inj hA, finrank_euclideanSpace_fin]
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hfin)
    let A' : Euclid n ≃ₗ[ℝ] Q := LinearEquiv.ofInjective (A : Euclid n →ₗ[ℝ] Euclid P) hA
    let L₀ : Euclid n ≃ₗ[ℝ] Euclid n := b.repr.symm.toLinearEquiv.trans A'.symm
    refine ⟨L₀.toContinuousLinearEquiv, fun w => ?_⟩
    have h1 : A' (L₀ w) = b.repr.symm w := by simp [L₀]
    have h2 : A (L₀ w) = ((A' (L₀ w) : Q) : Euclid P) := rfl
    change ‖A (L₀ w)‖ = ‖w‖
    rw [h2, h1]
    exact b.repr.symm.norm_map w
  set χ : Euclid n → Euclid P := fun w => ψ (v₀ + L w)
  have hχ0 : χ 0 = z := by simp [χ, hψv₀]
  have hχstrict : HasStrictFDerivAt χ (A.comp (L : Euclid n →L[ℝ] Euclid n)) 0 := by
    have h1 : HasStrictFDerivAt (fun w : Euclid n => v₀ + L w) (L : Euclid n →L[ℝ] Euclid n) 0 :=
      (L.hasStrictFDerivAt).const_add v₀
    have h2 : HasStrictFDerivAt ψ A (v₀ + L 0) := by simpa using hstrict
    exact h2.comp (0 : Euclid n) h1
  -- two-point estimate
  have h1 := (hasStrictFDerivAt_iff_isLittleO.1 hχstrict).bound hε
  have h2 : ∀ᶠ w in 𝓝 (0 : Euclid n), v₀ + L w ∈ V := by
    have hc : Continuous (fun w : Euclid n => v₀ + L w) := continuous_const.add L.continuous
    have : (fun w : Euclid n => v₀ + L w) 0 ∈ V := by simpa using hv₀V
    exact hc.continuousAt.preimage_mem_nhds (hV.mem_nhds this)
  obtain ⟨δ₁, hδ₁, hball1⟩ := Metric.eventually_nhds_iff_ball.1 h1
  obtain ⟨δ₂, hδ₂, hball2⟩ := Metric.eventually_nhds_iff_ball.1 h2
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hδV : ∀ w ∈ ball (0 : Euclid n) δ, v₀ + L w ∈ V :=
    fun w hw => hball2 w (ball_subset_ball (min_le_right _ _) hw)
  have hbil : ∀ a ∈ ball (0 : Euclid n) δ, ∀ b ∈ ball (0 : Euclid n) δ,
      (1 - ε) * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ (1 + ε) * ‖a - b‖ := by
    intro a ha b hb
    have hab : (a, b) ∈ ball ((0 : Euclid n), (0 : Euclid n)) δ₁ := by
      rw [← ball_prod_same]
      exact ⟨ball_subset_ball (min_le_left _ _) ha, ball_subset_ball (min_le_left _ _) hb⟩
    have he := hball1 (a, b) hab
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at he
    have hn : ‖A (L (a - b))‖ = ‖a - b‖ := hLJ _
    have t1 := norm_sub_norm_le (χ a - χ b) (A (L (a - b)))
    have t2 := norm_sub_norm_le (A (L (a - b))) (χ a - χ b)
    rw [norm_sub_rev (A (L (a - b))) (χ a - χ b)] at t2
    constructor <;> linarith
  -- local surjectivity
  have hinvc := Submission.dsmc_chart_inverse_continuity P n V W ψ hψ.continuousOn hinj
    (by rw [himg]; exact inter_subset_left) hprop v₀ hv₀V
  set C : ℝ := ‖((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n)‖ with hCdef
  have hC : 0 ≤ C := norm_nonneg _
  obtain ⟨η, hη, hηprop⟩ := hinvc (δ / (C + 1)) (div_pos hδ (by linarith))
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.isOpen_iff.1 hW z hzW
  refine ⟨χ, δ, min η r₀, hδ, lt_min hη hr₀, hχ0, hbil, ?_, ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    have : ψ (v₀ + L w) ∈ W ∩ M := by rw [← himg]; exact ⟨_, hδV w hw, rfl⟩
    exact this.2
  · rintro x ⟨hxM, hxb⟩
    have hxW : x ∈ W := hr₀W (ball_subset_ball (min_le_right _ _) hxb)
    obtain ⟨v', hv'V, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hxW, hxM⟩
    have hd : dist (ψ v') (ψ v₀) < η := by
      rw [hψv₀]; exact lt_of_lt_of_le (mem_ball.1 hxb) (min_le_left _ _)
    have hv' := hηprop v' hv'V hd
    refine ⟨L.symm (v' - v₀), ?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      calc ‖L.symm (v' - v₀)‖ ≤ C * ‖v' - v₀‖ := by
            rw [hCdef]
            exact ContinuousLinearMap.le_opNorm
              ((L.symm : Euclid n ≃L[ℝ] Euclid n) : Euclid n →L[ℝ] Euclid n) (v' - v₀)
        _ ≤ C * (δ / (C + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← dist_eq_norm]; exact hv'.le
        _ < δ := by
            rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
            nlinarith
    · simp [χ]
/-- **Bi-Lipschitz images** (Simon Ch. 2, 1.8(i), applied to `χ` and to its inverse): if
`c₁|a − b| ≤ |χ(a) − χ(b)| ≤ c₂|a − b|` on `E ⊆ ℝⁿ`, then `c₁ⁿ Lⁿ(E) ≤ Hⁿ(χ(E)) ≤ c₂ⁿ Lⁿ(E)`.
`Hⁿ = μHE[n]` is `c · μH[n]` with one constant `c` on every metric space and equals `volume` on
`ℝⁿ`; `χ` is `c₂`-Lipschitz on `E`, and it is injective there with `c₁⁻¹`-Lipschitz inverse on
`χ(E)`. -/
theorem Submission.dimred_rpd_bilipschitz_image_measure : ∀ (P n : ℕ) (χ : Euclid n → Euclid P) (E : Set (Euclid n)) (c₁ c₂ : ℝ), 0 < c₁ → 0 ≤ c₂ → (∀ a ∈ E, ∀ b ∈ E, c₁ * ‖a - b‖ ≤ ‖χ a - χ b‖ ∧ ‖χ a - χ b‖ ≤ c₂ * ‖a - b‖) → ENNReal.ofReal (c₁ ^ n) * volume E ≤ μHE[n] (χ '' E) ∧ μHE[n] (χ '' E) ≤ ENNReal.ofReal (c₂ ^ n) * volume E := by
  intro P n χ E c₁ c₂ hc₁ hc₂ h
  -- `Lⁿ = Hⁿ` on `ℝⁿ`, and `Hⁿ = c · μH[n]` on every metric space
  have hvol : (volume : Measure (Euclid n)) = μHE[n] :=
    (EuclideanSpace.euclideanHausdorffMeasure_eq_volume n).symm
  have hscale : ∀ {X : Type} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (S : Set X),
      (μHE[n] : Measure X) S = (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) * μH[(n : ℝ)] S := by
    intro X _ _ _ S
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  constructor
  · -- lower bound: `χ` is injective on `E` and its inverse on `χ(E)` is `c₁⁻¹`-Lipschitz
    have hinj : InjOn χ E := by
      intro a ha b hb hab
      have := (h a ha b hb).1
      rw [hab, sub_self, norm_zero] at this
      have : ‖a - b‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (a - b)]) (norm_nonneg _)
      exact sub_eq_zero.1 (norm_eq_zero.1 this)
    set g := Function.invFunOn χ E
    have hleft : LeftInvOn g χ E := hinj.leftInvOn_invFunOn
    have hgL : LipschitzOnWith (Real.toNNReal c₁⁻¹) g (χ '' E) := by
      apply LipschitzOnWith.of_dist_le_mul
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [hleft ha, hleft hb, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le)]
      have := (h a ha b hb).1
      rw [inv_mul_eq_div, le_div_iff₀ hc₁]
      linarith
    have himg : g '' (χ '' E) = E := hleft.image_image
    have hle := hgL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [himg] at hle
    rw [hvol, hscale, hscale (χ '' E)]
    set c : ℝ≥0∞ := (Measure.addHaarScalarFactor
      (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞)
    have hK : ((Real.toNNReal c₁⁻¹ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₁ ^ n)⁻¹ := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal,
        Real.coe_toNNReal _ (inv_nonneg.2 hc₁.le), ← ENNReal.ofReal_pow (inv_nonneg.2 hc₁.le),
        inv_pow]
    rw [hK] at hle
    have hpos : ENNReal.ofReal (c₁ ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hc₁ n)).ne'
    have hinv : ENNReal.ofReal (c₁ ^ n)⁻¹ = (ENNReal.ofReal (c₁ ^ n))⁻¹ :=
      ENNReal.ofReal_inv_of_pos (pow_pos hc₁ n)
    rw [hinv] at hle
    calc ENNReal.ofReal (c₁ ^ n) * (c * μH[(n : ℝ)] E)
        ≤ ENNReal.ofReal (c₁ ^ n) * (c * ((ENNReal.ofReal (c₁ ^ n))⁻¹ * μH[(n : ℝ)] (χ '' E))) := by
          gcongr
      _ = c * μH[(n : ℝ)] (χ '' E) := by
          rw [← mul_assoc, mul_comm (ENNReal.ofReal (c₁ ^ n)) c, mul_assoc,
            ← mul_assoc (ENNReal.ofReal (c₁ ^ n)), ENNReal.mul_inv_cancel hpos ENNReal.ofReal_ne_top,
            one_mul]
  · -- upper bound: `χ` is `c₂`-Lipschitz on `E`
    have hL : LipschitzOnWith (Real.toNNReal c₂) χ E := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hc₂]
      exact (h a ha b hb).2
    have hle := hL.hausdorffMeasure_image_le (d := (n : ℝ)) (Nat.cast_nonneg n)
    rw [hvol, hscale, hscale E]
    have hK : ((Real.toNNReal c₂ : NNReal) : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (c₂ ^ n) := by
      rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hc₂,
        ← ENNReal.ofReal_pow hc₂]
    rw [hK] at hle
    calc _ ≤ (Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[n] : ℝ≥0∞) *
          (ENNReal.ofReal (c₂ ^ n) * μH[(n : ℝ)] E) := by gcongr
      _ = _ := by ring

/-- **Density one on an embedded `C¹` submanifold** (the fact `Θⁿ(Hⁿ⌞M, z) = 1` behind
`Θⁿ(μ_T, z) = |m|` for `T = m[[M]]` near `z ∈ reg T`, Simon 7.4.1):
`Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` as `s ↓ 0`.  For `ε ∈ (0, 1)`, a `(1 ± ε)`-bi-Lipschitz chart `χ`
with `χ(0) = z` gives `χ(B_{s/(1+ε)}(0)) ⊆ M ∩ B_s(z) ⊆ χ(B_{s/(1−ε)}(0))` for small `s > 0`.  With
the bi-Lipschitz measure bounds (Simon Ch. 2, 1.8(i)) and `Lⁿ(B_r(0)) = ωₙrⁿ` this gives
`((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`, and both bounds tend to `1`
as `ε → 0`. -/
theorem Submission.dimred_rpd_submanifold_density_one : ∀ (P n : ℕ) (M : Set (Euclid P)) (z : Euclid P), IsEmbeddedSubmanifold 1 n M → z ∈ M → Tendsto (fun s : ℝ => μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M z hM hz
  -- `ωₙ ∈ (0, ∞)`, and `Lⁿ(B_r(0)) = rⁿωₙ` for `r > 0`
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωT : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  have hvol : ∀ r : ℝ, 0 < r →
      volume (ball (0 : Euclid n) r) = ENNReal.ofReal (r ^ n) * unitBallVolume n := by
    intro r hr; rw [Measure.addHaar_ball_of_pos _ _ hr, finrank_euclideanSpace_fin]; rfl
  -- Step 1: for `ε ∈ (0, 1)`, `((1 − ε)/(1 + ε))ⁿ ≤ Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) ≤ ((1 + ε)/(1 − ε))ⁿ`
  -- for all small `s > 0`
  have hbounds : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) ≤
          μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ∧
        μHE[n] (M ∩ ball z s) / (unitBallVolume n * ENNReal.ofReal (s ^ n)) ≤
          ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) := by
    intro ε hε hε1
    -- the `(1 ± ε)`-bi-Lipschitz chart `χ : B_δ(0) → M` with `χ(0) = z`, onto `M` near `z`
    obtain ⟨χ, δ, δ', hδ, hδ', hχ0, hbil, hχM, hMχ⟩ :=
      Submission.dimred_rpd_near_isometric_chart P n M z hM hz ε hε
    have h1ε : 0 < 1 - ε := by linarith
    have h1ε' : 0 < 1 + ε := by linarith
    have hs₀ : 0 < min δ' ((1 - ε) * δ) := lt_min hδ' (mul_pos h1ε hδ)
    filter_upwards [Ioo_mem_nhdsGT hs₀] with s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hsδ' : s < δ' := lt_of_lt_of_le hs1 (min_le_left _ _)
    have hsδ : s < (1 - ε) * δ := lt_of_lt_of_le hs1 (min_le_right _ _)
    -- `0 < r₁ = s/(1 + ε) ≤ r₂ = s/(1 − ε) < δ`
    set r₁ := s / (1 + ε) with hr₁def
    set r₂ := s / (1 - ε) with hr₂def
    have hr₁ : 0 < r₁ := div_pos hs0 h1ε'
    have hr₂ : 0 < r₂ := div_pos hs0 h1ε
    have hr₂δ : r₂ < δ := by rw [hr₂def, div_lt_iff₀ h1ε]; linarith
    have hr₁r₂ : r₁ ≤ r₂ := div_le_div_of_nonneg_left hs0.le h1ε (by linarith)
    have hb₁ : ball (0 : Euclid n) r₁ ⊆ ball 0 δ := ball_subset_ball (by linarith)
    have hb₂ : ball (0 : Euclid n) r₂ ⊆ ball 0 δ := ball_subset_ball hr₂δ.le
    -- (a) `χ(B_{r₁}(0)) ⊆ M ∩ B_s(z)`: `|χ(w) − z| ≤ (1 + ε)|w| < (1 + ε)r₁ = s`
    have hinc₁ : χ '' ball 0 r₁ ⊆ M ∩ ball z s := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨hχM ⟨w, hb₁ hw, rfl⟩, ?_⟩
      rw [mem_ball, dist_eq_norm, ← hχ0]
      have h := (hbil w (hb₁ hw) 0 (mem_ball_self hδ)).2
      rw [sub_zero] at h
      rw [mem_ball, dist_zero_right] at hw
      calc ‖χ w - χ 0‖ ≤ (1 + ε) * ‖w‖ := h
        _ < (1 + ε) * r₁ := mul_lt_mul_of_pos_left hw h1ε'
        _ = s := by rw [hr₁def]; field_simp
    -- (b) `M ∩ B_s(z) ⊆ χ(B_{r₂}(0))`: `x = χ(w)` with `(1 − ε)|w| ≤ |x − z| < s`
    have hinc₂ : M ∩ ball z s ⊆ χ '' ball 0 r₂ := by
      rintro x ⟨hxM, hxs⟩
      obtain ⟨w, hw, rfl⟩ := hMχ ⟨hxM, ball_subset_ball hsδ'.le hxs⟩
      refine ⟨w, ?_, rfl⟩
      have h := (hbil w hw 0 (mem_ball_self hδ)).1
      rw [sub_zero] at h
      rw [mem_ball, dist_eq_norm, ← hχ0] at hxs
      rw [mem_ball, dist_zero_right, hr₂def, lt_div_iff₀ h1ε]
      nlinarith [norm_nonneg w]
    -- (c) the bi-Lipschitz measure bounds on `B_{r₁}(0), B_{r₂}(0) ⊆ B_δ(0)`
    have hlow := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₁) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₁ ha) b (hb₁ hb))).1
    have hupp := (Submission.dimred_rpd_bilipschitz_image_measure P n χ (ball 0 r₂) (1 - ε) (1 + ε)
      h1ε h1ε'.le (fun a ha b hb => hbil a (hb₂ ha) b (hb₂ hb))).2
    rw [hvol r₁ hr₁] at hlow
    rw [hvol r₂ hr₂] at hupp
    have hm1 := hlow.trans (measure_mono hinc₁)
    have hm2 := (measure_mono hinc₂).trans hupp
    -- divide by `ωₙsⁿ ∈ (0, ∞)`
    have hden0 : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ 0 :=
      mul_ne_zero hω0 (ENNReal.ofReal_pos.2 (pow_pos hs0 n)).ne'
    have hdenT : unitBallVolume n * ENNReal.ofReal (s ^ n) ≠ ∞ :=
      ENNReal.mul_ne_top hωT ENNReal.ofReal_ne_top
    constructor
    · rw [ENNReal.le_div_iff_mul_le (Or.inl hden0) (Or.inl hdenT)]
      have e : ((1 - ε) / (1 + ε)) ^ n * s ^ n = (1 - ε) ^ n * r₁ ^ n := by
        rw [hr₁def, div_pow, div_pow]; field_simp
      calc ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n) * (unitBallVolume n * ENNReal.ofReal (s ^ n))
          = ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n * s ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal ((1 - ε) ^ n * r₁ ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal ((1 - ε) ^ n) * (ENNReal.ofReal (r₁ ^ n) * unitBallVolume n) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ ≤ _ := hm1
    · rw [ENNReal.div_le_iff hden0 hdenT]
      have e : ((1 + ε) / (1 - ε)) ^ n * s ^ n = (1 + ε) ^ n * r₂ ^ n := by
        rw [hr₂def, div_pow, div_pow]; field_simp
      calc μHE[n] (M ∩ ball z s)
          ≤ ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal (r₂ ^ n) * unitBallVolume n) := hm2
        _ = ENNReal.ofReal ((1 + ε) ^ n * r₂ ^ n) * unitBallVolume n := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n * s ^ n) * unitBallVolume n := by rw [e]
        _ = ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n) *
              (unitBallVolume n * ENNReal.ofReal (s ^ n)) := by
            rw [ENNReal.ofReal_mul (by positivity)]; ring
  -- Step 2: both bounds tend to `1` as `ε → 0`, so `Hⁿ(M ∩ B_s(z)) / (ωₙsⁿ) → 1` (`tendsto_order`)
  have hg₁ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 - ε) / (1 + ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 - ε) / (1 + ε)) ^ n) (𝓝 0) (𝓝 (((1 - 0) / (1 + 0)) ^ n)) :=
      ((tendsto_const_nhds.sub tendsto_id).div (tendsto_const_nhds.add tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hg₂ : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ n)) (𝓝 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ n) (𝓝 0) (𝓝 (((1 + 0) / (1 - 0)) ^ n)) :=
      ((tendsto_const_nhds.add tendsto_id).div (tendsto_const_nhds.sub tendsto_id)
        (by norm_num)).pow n
    simpa using ENNReal.tendsto_ofReal h
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds one_pos)] with ε h1 h2
    exact ⟨h1, h2⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- `a < 1`: choose `ε ∈ (0, 1)` with `a < ((1 − ε)/(1 + ε))ⁿ`
    obtain ⟨ε, hεa, hε0, hε1⟩ :=
      (((hg₁.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds ha)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_lt_of_le hεa hs.1
  · -- `1 < b`: choose `ε ∈ (0, 1)` with `((1 + ε)/(1 − ε))ⁿ < b`
    obtain ⟨ε, hεb, hε0, hε1⟩ :=
      (((hg₂.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds hb)).and hsmall).exists
    filter_upwards [hbounds ε hε0 hε1] with s hs
    exact lt_of_le_of_lt hs.2 hεb

/-- **Tangential derivatives are well defined** (Simon Ch. 2, §4, p. 55; the tangential gradient
of the Simons cone step): for any set `M ⊆ ℝᴾ` and real normed space `E`, if `f : ℝᴾ → E` has
derivative `f'` within `M` at `x`, then `fderivWithin ℝ f M x` agrees with `f'` on the span of
`T_xM`.  `L = fderivWithin ℝ f M x` is itself a derivative of `f` within `M` at `x`, and two
derivatives within `M` agree on the tangent cone of `M` at `x`.  Each `w = γ'(0) ∈ T_xM` lies in
that cone: with `sₙ = 1/(n+2) ∈ (−1, 1)` and `dₙ = γ(sₙ) − x`, `dₙ → 0`, `x + dₙ = γ(sₙ) ∈ M` and
`(n+2) dₙ = sₙ⁻¹(γ(sₙ) − γ(0)) → w`.  So `L = f'` on `T_xM`, hence on its linear span. -/
theorem Submission.codim1_hcp_sc_fderivWithin_tangent_eq : ∀ (P : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M : Set (Euclid P)) (f : Euclid P → E) (f' : Euclid P →L[ℝ] E) (x : Euclid P), HasFDerivWithinAt f f' M x → ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderivWithin ℝ f M x v = f' v := by
  intro P E _ _ M f f' x hf v hv
  -- steps 2–3: `L = fderivWithin ℝ f M x` and `f'` are both derivatives of `f` within `M` at
  -- `x`, so they agree on the tangent cone of `M` at `x`
  have huniq : EqOn (fderivWithin ℝ f M x) f' (tangentConeAt ℝ M x) :=
    hf.differentiableWithinAt.hasFDerivWithinAt.unique_on hf
  -- step 1: the velocity `w = γ'(0)` of a curve `γ` in `M` through `x` lies in the tangent cone
  have hcone : tangentSpace M x ⊆ tangentConeAt ℝ M x := by
    rintro w ⟨γ, -, hγM, hγ0, hγw⟩
    -- `sₙ = 1/(n+2)` tends to `0` through nonzero values and lies in `(−1, 1)`
    have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop),
        Eventually.of_forall fun n => by simp only [mem_compl_singleton_iff]; positivity⟩
    have hsI : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ∈ Ioo (-1 : ℝ) 1 := fun n => by
      have hn : (0 : ℝ) ≤ n := n.cast_nonneg
      have hpos : 0 < 1 / ((n : ℝ) + 2) := by positivity
      refine ⟨by linarith, ?_⟩
      rw [div_lt_one (by positivity)]
      linarith
    -- `cₙ = n + 2` and `dₙ = γ(sₙ) − x`
    refine mem_tangentConeAt_of_seq atTop (fun n : ℕ => (n : ℝ) + 2)
      (fun n => γ (1 / ((n : ℝ) + 2)) - x) ?_ ?_ ?_
    · -- `dₙ → γ(0) − x = 0`, since `γ` is continuous at `0`
      rw [tendsto_sub_nhds_zero_iff, ← hγ0]
      exact hγw.continuousAt.tendsto.comp (hs.mono_right nhdsWithin_le_nhds)
    · -- `x + dₙ = γ(sₙ) ∈ M`, as `sₙ ∈ (−1, 1)`
      refine Eventually.of_forall fun n => ?_
      simp only [add_sub_cancel]
      exact hγM (hsI n)
    · -- `cₙ dₙ = sₙ⁻¹(γ(0 + sₙ) − γ(0)) → γ'(0) = w`
      refine (hγw.tendsto_slope_zero.comp hs).congr fun n => ?_
      simp [hγ0]
  -- step 4: `L = f'` on `T_xM`; the set where the linear maps `L` and `f'` agree is a subspace,
  -- so it contains the linear span of `T_xM`
  exact LinearMap.eqOn_span (f := (fderivWithin ℝ f M x : Euclid P →ₗ[ℝ] E))
    (g := (f' : Euclid P →ₗ[ℝ] E)) (fun w hw => huniq (hcone hw)) hv
/-- **The unit normal of a cone is homogeneous of degree `0`** (Simon, Appendix B, proof of
Lemma B.11, (1)–(2)).  Let `M ⊆ A₀` be an embedded `C¹` `m`-submanifold with `tM ⊆ M` for
`t > 0`, and `ν` a `C^∞` unit normal to `M` in `A₀`.  By
`Submission.codim1_hcp_sc_tangent_normal_complement`, `T_yM = {v ∈ A₀ : ν(y) · v = 0}` is a
linear subspace.  The curve `s ↦ eˢx` gives `x ∈ T_xM`, and scaling curves gives
`tT_xM ⊆ T_{tx}M`, hence `T_{tx}M = T_xM`.  So `ν(tx)` is a unit vector in
`A₀ ∩ (T_xM)^⊥ = ℝν(x)`, i.e. `ν(tx) = ±ν(x)`; `t ↦ ν(x) · ν(tx)` is continuous on `(0, ∞)`
and equals `1` at `t = 1`, so the intermediate value theorem gives `ν(tx) = ν(x)`.
Differentiating `ν(tγ(s)) = ν(γ(s))` at `s = 0` along curves `γ` in `M` gives
`tDν(tx)v = Dν(x)v`, and differentiating the constant map `t ↦ ν(tx)` at `t = 1` gives
`Dν(x)x = 0`. -/
theorem Submission.codim1_hcp_sc_cone_normal_homogeneous : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → IsEmbeddedSubmanifold 1 m M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, x ∈ tangentSpace M x ∧ fderiv ℝ ν x x = 0 ∧ ∀ t : ℝ, 0 < t → tangentSpace M (t • x) = tangentSpace M x ∧ ν (t • x) = ν x ∧ ∀ v ∈ tangentSpace M x, t • fderiv ℝ ν (t • x) v = fderiv ℝ ν x v := by
  intro P m A₀ M ν hdim hMA hM hcone hO hν x hx
  obtain ⟨O, hOo, hMO, hνO⟩ := hO
  -- Step 0: `ν` is differentiable at every point of `M ⊆ O`, and `T_yM = {v ∈ A₀ : ν(y) · v = 0}`
  have hνd : ∀ y ∈ M, HasFDerivAt ν (fderiv ℝ ν y) y := fun y hy =>
    ((hνO.contDiffAt (hOo.mem_nhds (hMO hy))).differentiableAt (by simp)).hasFDerivAt
  have hT : ∀ y ∈ M, tangentSpace M y = {v : Euclid P | v ∈ A₀ ∧ inner ℝ (ν y) v = 0} :=
    fun y hy =>
      (Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hdim hMA hM hν y hy).1
  -- in particular each `T_yM`, `y ∈ M`, is closed under scalar multiplication
  have hTsmul : ∀ y ∈ M, ∀ (c : ℝ) (v : Euclid P), v ∈ tangentSpace M y →
      c • v ∈ tangentSpace M y := by
    intro y hy c v hv
    rw [hT y hy] at hv ⊢
    exact ⟨A₀.smul_mem c hv.1, by rw [real_inner_smul_right, hv.2, mul_zero]⟩
  -- Step 1: `x ∈ T_xM`, via the curve `s ↦ eˢx` in `M`
  have hxT : x ∈ tangentSpace M x := by
    refine ⟨fun s => Real.exp s • x, (Real.contDiff_exp.smul contDiff_const).contDiffOn,
      fun s _ => hcone _ (Real.exp_pos s) x hx, by simp, ?_⟩
    simpa using (Real.hasDerivAt_exp 0).smul_const x
  -- Step 2: `t • T_yM ⊆ T_{ty}M` for `t > 0`: scale the curves
  have hscale : ∀ t : ℝ, 0 < t → ∀ y v : Euclid P, v ∈ tangentSpace M y →
      t • v ∈ tangentSpace M (t • y) := by
    rintro t ht y v ⟨γ, hγ, hγM, hγ0, hγv⟩
    exact ⟨fun s => t • γ s, hγ.const_smul t, fun s hs => hcone t ht _ (hγM hs),
      by simp [hγ0], hγv.const_smul t⟩
  -- Step 3: `T_{ty}M = T_yM` for `y ∈ M` and `t > 0`
  have hTeq : ∀ y ∈ M, ∀ t : ℝ, 0 < t → tangentSpace M (t • y) = tangentSpace M y := by
    intro y hy t ht
    ext w
    constructor
    · intro hw
      have h1 := hscale t⁻¹ (inv_pos.2 ht) (t • y) w hw
      rw [inv_smul_smul₀ ht.ne'] at h1
      have h2 := hTsmul y hy t _ h1
      rwa [smul_inv_smul₀ ht.ne'] at h2
    · intro hw
      have h1 := hscale t ht y _ (hTsmul y hy t⁻¹ w hw)
      rwa [smul_inv_smul₀ ht.ne'] at h1
  -- Step 4: `ν(ty) = λν(y)` with `λ = ν(y) · ν(ty) ∈ {1, −1}`
  have hpm : ∀ y ∈ M, ∀ t : ℝ, 0 < t →
      ν (t • y) = inner ℝ (ν y) (ν (t • y)) • ν y ∧
        (inner ℝ (ν y) (ν (t • y)) = 1 ∨ inner ℝ (ν y) (ν (t • y)) = -1) := by
    intro y hy t ht
    obtain ⟨hνyA, hνy1, -⟩ := hν y hy
    obtain ⟨hνtA, hνt1, hνtT⟩ := hν (t • y) (hcone t ht y hy)
    set lam : ℝ := inner ℝ (ν y) (ν (t • y)) with hlam
    have hyy : inner ℝ (ν y) (ν y) = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hνy1, one_pow]
    -- `h = ν(ty) − λν(y) ∈ A₀` is orthogonal to `ν(y)`, so `h ∈ T_yM = T_{ty}M`
    have hhT : ν (t • y) - lam • ν y ∈ tangentSpace M y := by
      rw [hT y hy]
      refine ⟨A₀.sub_mem hνtA (A₀.smul_mem lam hνyA), ?_⟩
      rw [inner_sub_right, real_inner_smul_right, hyy, mul_one, ← hlam, sub_self]
    have e1 : inner ℝ (ν (t • y)) (ν (t • y) - lam • ν y) = (0 : ℝ) :=
      hνtT _ (by rw [hTeq y hy t ht]; exact hhT)
    have e2 : inner ℝ (ν y) (ν (t • y) - lam • ν y) = (0 : ℝ) := by
      rw [hT y hy] at hhT
      exact hhT.2
    -- `|h|² = ν(ty) · h − λ ν(y) · h = 0`
    have hh0 : ν (t • y) - lam • ν y = 0 := by
      apply (inner_self_eq_zero (𝕜 := ℝ)).1
      rw [inner_sub_left, real_inner_smul_left, e1, e2, mul_zero, sub_zero]
    have hνt : ν (t • y) = lam • ν y := sub_eq_zero.1 hh0
    refine ⟨hνt, (abs_eq zero_le_one).1 ?_⟩
    -- `1 = |ν(ty)| = |λ| |ν(y)| = |λ|`
    have := congrArg norm hνt
    rw [norm_smul, hνt1, hνy1, mul_one, Real.norm_eq_abs] at this
    exact this.symm
  -- Step 5: `ν(ty) = ν(y)` for `y ∈ M` and `t > 0`: `g(s) = ν(y) · ν(sy)` is continuous on
  -- `(0, ∞)` with values in `{1, −1}` and `g(1) = 1`, so `g(t) = −1` contradicts the IVT
  have hhom : ∀ y ∈ M, ∀ t : ℝ, 0 < t → ν (t • y) = ν y := by
    intro y hy t ht
    have hg : ContinuousOn (fun s : ℝ => inner ℝ (ν y) (ν (s • y))) (Ioi 0) :=
      continuousOn_const.inner (hνO.continuousOn.comp
        (continuous_id.smul continuous_const).continuousOn fun s hs => hMO (hcone s hs y hy))
    obtain ⟨hνt, h1 | h1⟩ := hpm y hy t ht
    · rw [hνt, h1, one_smul]
    · exfalso
      have hg1 : inner ℝ (ν y) (ν ((1 : ℝ) • y)) = (1 : ℝ) := by
        rw [one_smul, real_inner_self_eq_norm_sq, (hν y hy).2.1, one_pow]
      obtain ⟨s, hs, hs0⟩ := isPreconnected_Ioi.intermediate_value (show t ∈ Ioi (0 : ℝ) from ht)
        (Set.mem_Ioi.2 one_pos) hg
        (show (0 : ℝ) ∈ Icc (inner ℝ (ν y) (ν (t • y))) (inner ℝ (ν y) (ν ((1 : ℝ) • y))) by
          rw [h1, hg1]
          constructor <;> norm_num)
      have hs0' : inner ℝ (ν y) (ν (s • y)) = (0 : ℝ) := hs0
      rcases (hpm y hy s hs).2 with h2 | h2 <;> linarith
  refine ⟨hxT, ?_, fun t ht => ⟨hTeq x hx t ht, hhom x hx t ht, ?_⟩⟩
  · -- Step 7: `Dν(x)x = 0`: `t ↦ ν(tx)` is constant near `t = 1`, with derivative `Dν(x)x` there
    have h1 : HasDerivAt (fun t : ℝ => ν (t • x)) (fderiv ℝ ν x x) 1 := by
      have hl : HasDerivAt (fun t : ℝ => t • x) x 1 := by
        simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
      exact (hνd x hx).comp_hasDerivAt_of_eq 1 hl (one_smul ℝ x).symm
    have h2 : HasDerivAt (fun t : ℝ => ν (t • x)) 0 1 := by
      refine (hasDerivAt_const (1 : ℝ) (ν x)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds one_pos] with t ht using hhom x hx t ht
    exact h1.unique h2
  · -- Step 6: `tDν(tx)v = Dν(x)v`: differentiate `ν(tγ(s)) = ν(γ(s))` at `s = 0`
    rintro v ⟨γ, -, hγM, hγ0, hγv⟩
    have h1 : HasDerivAt (fun s => ν (t • γ s)) (fderiv ℝ ν (t • x) (t • v)) 0 :=
      (hνd (t • x) (hcone t ht x hx)).comp_hasDerivAt_of_eq 0 (hγv.const_smul t) (by simp [hγ0])
    have h2 : HasDerivAt (fun s => ν (t • γ s)) (fderiv ℝ ν x v) 0 := by
      refine ((hνd x hx).comp_hasDerivAt_of_eq 0 hγv hγ0.symm).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with s hs using hhom (γ s) (hγM hs) t ht
    rw [← map_smul]
    exact h1.unique h2
/-- **Hausdorff measure on a cone** (Simon, Appendix B, proof of B.2: the finiteness that the
polar formula (5) provides, obtained here by dyadic scaling of `Hᵐ`).  Let `M ⊆ ℝᴾ` with `0 ∉ M`,
`M̄ ⊆ M ∪ {0}`, `tM ⊆ M` for `t > 0` and `Hᵐ(M ∩ K) < ∞` for compact `K`.  Then `tM = M`, so
`Hᵐ(M ∩ tS) = Hᵐ(t(M ∩ S)) = tᵐHᵐ(M ∩ S)`, and `M = M̄ \ {0}` is Borel.  (a) The sets
`M ∩ ∂B_{cₙ}(0)`, `cₙ = 1 + 1/(n+1) ∈ (1, 2]`, are disjoint subsets of `M ∩ B̄₂(0)` of measure
`cₙᵐHᵐ(M ∩ ∂B₁(0)) ≥ Hᵐ(M ∩ ∂B₁(0))`, so `Hᵐ(M ∩ ∂B₁(0)) = 0`; scale to radius `c`.  (b), (c) With
`B = Hᵐ(M ∩ B̄₁(0)) < ∞`, the shell `{x ∈ M : asᵏ ≤ |x| ≤ bsᵏ}` has measure `≤ (bsᵏ)ᵐB`, and
`|x|^γ ≤ (asᵏ)^γ` on it for `γ ≤ 0`, so the integral over a union of such shells is at most a
geometric series of ratio `s^γsᵐ`.  The shells `2⁻ᵏ⁻¹ ≤ |x| ≤ 2⁻ᵏ` cover `M ∩ B₁(0)` (ratio
`2^{-(m+α)} < 1` for `−m < α < 0`; for `α ≥ 0` use `|x|^α ≤ 1`), and `2ᵏ ≤ |x| ≤ 2ᵏ⁺¹` cover
`M \ B₁(0)` (ratio `2^{m+β} < 1`, as `β < −m ≤ 0`). -/
theorem Submission.codim1_hcp_sc_cone_annuli_measure : ∀ (P m : ℕ) (M : Set (Euclid P)), (0 : Euclid P) ∉ M → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ c : ℝ, 0 < c → μHE[m] (M ∩ sphere (0 : Euclid P) c) = 0) ∧ (∀ α : ℝ, -(m : ℝ) < α → ∫⁻ x in M ∩ ball (0 : Euclid P) 1, ENNReal.ofReal (‖x‖ ^ α) ∂μHE[m] ≠ ∞) ∧ (∀ β : ℝ, β < -(m : ℝ) → ∫⁻ x in M \ ball (0 : Euclid P) 1, ENNReal.ofReal (‖x‖ ^ β) ∂μHE[m] ≠ ∞) := by
  intro P m M h0 hcl hcone hfin
  open scoped Pointwise in
  -- Step 1: `tM = M`, hence `M ∩ tS = t(M ∩ S)`, for `t > 0`
  have hMt : ∀ t : ℝ, 0 < t → ∀ S : Set (Euclid P), M ∩ t • S = t • (M ∩ S) := by
    intro t ht S
    ext x
    simp only [mem_inter_iff, mem_smul_set_iff_inv_smul_mem₀ ht.ne']
    constructor
    · rintro ⟨hx, hS⟩
      exact ⟨hcone _ (inv_pos.2 ht) x hx, hS⟩
    · rintro ⟨hx, hS⟩
      refine ⟨?_, hS⟩
      simpa [smul_inv_smul₀ ht.ne'] using hcone t ht _ hx
  -- Step 2: `M = M̄ \ {0}` is Borel
  have hMeas : MeasurableSet M := by
    have hM : M = closure M \ {0} := by
      ext x
      constructor
      · intro hx
        refine ⟨subset_closure hx, ?_⟩
        rintro rfl
        exact h0 hx
      · rintro ⟨hx, hx0⟩
        rcases hcl hx with h | h
        · exact absurd h hx0
        · exact h
    rw [hM]
    exact isClosed_closure.measurableSet.diff (measurableSet_singleton 0)
  -- Step 3: `Hᵐ(tS) = tᵐHᵐ(S)` (`hausdorffMeasure_smul₀`), so `Hᵐ(M ∩ tS) = tᵐHᵐ(M ∩ S)`
  have hsc : ∀ t : ℝ, 0 < t → ∀ S : Set (Euclid P),
      μHE[m] (M ∩ t • S) = ENNReal.ofReal (t ^ m) * μHE[m] (M ∩ S) := by
    intro t ht S
    have hc : ((‖t‖₊ ^ (m : ℝ) : NNReal) : ℝ≥0∞) = ENNReal.ofReal (t ^ m) := by
      rw [NNReal.rpow_natCast, ENNReal.ofReal_pow ht.le, ENNReal.coe_pow, Real.nnnorm_of_nonneg ht.le,
        ENNReal.ofReal_eq_coe_nnreal ht.le]
    rw [hMt t ht S, Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, Measure.smul_apply,
      Measure.hausdorffMeasure_smul₀ (Nat.cast_nonneg m) ht.ne', smul_comm, ENNReal.smul_def,
      smul_eq_mul, hc]
  -- Step 4: `Hᵐ(M ∩ B̄ᵣ(0)) = rᵐB` with `B = Hᵐ(M ∩ B̄₁(0)) < ∞`
  set B := μHE[m] (M ∩ closedBall (0 : Euclid P) 1)
  have hBfin : B ≠ ∞ := hfin _ (isCompact_closedBall 0 1)
  have hball : ∀ r : ℝ, 0 < r →
      μHE[m] (M ∩ closedBall (0 : Euclid P) r) = ENNReal.ofReal (r ^ m) * B := by
    intro r hr
    have : closedBall (0 : Euclid P) r = r • closedBall (0 : Euclid P) 1 := by
      rw [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_one]
    rw [this, hsc r hr]
  -- Step 5: on the shell `{x ∈ M : asᵏ ≤ |x| ≤ bsᵏ}`, `|x|^γ ≤ (asᵏ)^γ` (`γ ≤ 0`) and the shell
  -- lies in `M ∩ B̄_{bsᵏ}(0)`; summing over `k` gives a geometric series of ratio `s^γsᵐ < 1`
  have hgeo : ∀ (γ a b s : ℝ) (Ω : Set (Euclid P)), γ ≤ 0 → 0 < a → 0 < b → 0 < s →
      s ^ γ * s ^ m < 1 → Ω ⊆ ⋃ k : ℕ, M ∩ {x | a * s ^ k ≤ ‖x‖ ∧ ‖x‖ ≤ b * s ^ k} →
      ∫⁻ x in Ω, ENNReal.ofReal (‖x‖ ^ γ) ∂μHE[m] ≠ ∞ := by
    intro γ a b s Ω hγ ha hb hs hρ hΩ
    have hterm : ∀ k : ℕ, ∫⁻ x in M ∩ {x | a * s ^ k ≤ ‖x‖ ∧ ‖x‖ ≤ b * s ^ k},
        ENNReal.ofReal (‖x‖ ^ γ) ∂μHE[m] ≤
          ENNReal.ofReal (a ^ γ * b ^ m) * B * ENNReal.ofReal (s ^ γ * s ^ m) ^ k := by
      intro k
      have hsk : 0 < s ^ k := pow_pos hs k
      calc ∫⁻ x in M ∩ {x | a * s ^ k ≤ ‖x‖ ∧ ‖x‖ ≤ b * s ^ k}, ENNReal.ofReal (‖x‖ ^ γ) ∂μHE[m]
          ≤ ∫⁻ x in M ∩ {x | a * s ^ k ≤ ‖x‖ ∧ ‖x‖ ≤ b * s ^ k},
              ENNReal.ofReal ((a * s ^ k) ^ γ) ∂μHE[m] := by
            apply setLIntegral_mono measurable_const
            rintro x ⟨-, hx1, -⟩
            exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (mul_pos ha hsk) hx1 hγ)
        _ = ENNReal.ofReal ((a * s ^ k) ^ γ) *
              μHE[m] (M ∩ {x | a * s ^ k ≤ ‖x‖ ∧ ‖x‖ ≤ b * s ^ k}) := setLIntegral_const _ _
        _ ≤ ENNReal.ofReal ((a * s ^ k) ^ γ) * μHE[m] (M ∩ closedBall 0 (b * s ^ k)) := by
            gcongr
            intro x hx
            exact mem_closedBall_zero_iff.2 hx.2
        _ = ENNReal.ofReal ((a * s ^ k) ^ γ) * (ENNReal.ofReal ((b * s ^ k) ^ m) * B) := by
            rw [hball _ (mul_pos hb hsk)]
        _ = ENNReal.ofReal (a ^ γ * b ^ m) * B * ENNReal.ofReal (s ^ γ * s ^ m) ^ k := by
            rw [← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
              ← ENNReal.ofReal_mul (by positivity), mul_right_comm,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 2
            rw [Real.mul_rpow ha.le hsk.le, ← Real.rpow_pow_comm hs.le]
            ring
    have hρ' : ENNReal.ofReal (s ^ γ * s ^ m) < 1 := ENNReal.ofReal_lt_one.2 hρ
    refine ne_top_of_le_ne_top ?_ ((lintegral_mono_set hΩ).trans
      ((lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hterm)))
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBfin)
      (ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ').ne')
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `Hᵐ(M ∩ ∂B_c(0)) = cᵐHᵐ(M ∩ ∂B₁(0))`, and `Hᵐ(M ∩ ∂B₁(0)) = 0`
    have hsph : ∀ c : ℝ, 0 < c → μHE[m] (M ∩ sphere (0 : Euclid P) c) =
        ENNReal.ofReal (c ^ m) * μHE[m] (M ∩ sphere (0 : Euclid P) 1) := by
      intro c hc
      have : sphere (0 : Euclid P) c = c • sphere (0 : Euclid P) 1 := by
        rw [smul_sphere' hc.ne', smul_zero, Real.norm_of_nonneg hc.le, mul_one]
      rw [this, hsc c hc]
    have h1 : μHE[m] (M ∩ sphere (0 : Euclid P) 1) = 0 := by
      by_contra hne
      -- the radii `cₙ = 1 + 1/(n+1) ∈ (1, 2]` are distinct
      set c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hc_def
      have hc1 : ∀ n, 1 ≤ c n := fun n => by
        have : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
        simp only [hc_def]; linarith
      have hc2 : ∀ n, c n ≤ 2 := fun n => by
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
        simp only [hc_def]; linarith
      have hcinj : Function.Injective c := by
        intro i j hij
        simp only [hc_def, add_right_inj, one_div, inv_inj, add_left_inj, Nat.cast_inj] at hij
        exact hij
      -- so the spheres `M ∩ ∂B_{cₙ}(0) ⊆ M ∩ B̄₂(0)` are disjoint Borel sets
      have hdisj : Pairwise (Disjoint on fun n => M ∩ sphere (0 : Euclid P) (c n)) := by
        intro i j hij
        rw [Function.onFun, Set.disjoint_left]
        rintro x ⟨-, hxi⟩ ⟨-, hxj⟩
        rw [mem_sphere_zero_iff_norm] at hxi hxj
        exact hij (hcinj (hxi.symm.trans hxj))
      have hmeas : ∀ n, MeasurableSet (M ∩ sphere (0 : Euclid P) (c n)) := fun n =>
        hMeas.inter isClosed_sphere.measurableSet
      have hsum : ∑' n, μHE[m] (M ∩ sphere (0 : Euclid P) (c n)) ≤
          μHE[m] (M ∩ closedBall (0 : Euclid P) 2) := by
        rw [← measure_iUnion hdisj hmeas]
        refine measure_mono (iUnion_subset fun n => ?_)
        exact inter_subset_inter_right _
          (sphere_subset_closedBall.trans (closedBall_subset_closedBall (hc2 n)))
      -- each has measure `cₙᵐHᵐ(M ∩ ∂B₁(0)) ≥ Hᵐ(M ∩ ∂B₁(0)) > 0`, so their sum is infinite
      have htop : ∑' n, μHE[m] (M ∩ sphere (0 : Euclid P) (c n)) = ∞ := by
        refine top_unique ?_
        rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) hne]
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [hsph (c n) (by linarith [hc1 n])]
        calc μHE[m] (M ∩ sphere (0 : Euclid P) 1) = 1 * μHE[m] (M ∩ sphere (0 : Euclid P) 1) :=
              (one_mul _).symm
          _ ≤ _ := by gcongr; exact ENNReal.one_le_ofReal.2 (one_le_pow₀ (hc1 n))
      exact hfin _ (isCompact_closedBall 0 2) (top_unique (htop ▸ hsum))
    intro c hc
    rw [hsph c hc, h1, mul_zero]
  · -- (b) for `α ≥ 0`, `|x|^α ≤ 1` on `B₁(0)`; for `−m < α < 0`, shells `2⁻ᵏ⁻¹ ≤ |x| ≤ 2⁻ᵏ`
    intro α hα
    rcases le_or_gt 0 α with hα0 | hα0
    · refine ne_top_of_le_ne_top (hfin _ (isCompact_closedBall (0 : Euclid P) 1)) ?_
      calc ∫⁻ x in M ∩ ball (0 : Euclid P) 1, ENNReal.ofReal (‖x‖ ^ α) ∂μHE[m]
          ≤ ∫⁻ x in M ∩ ball (0 : Euclid P) 1, 1 ∂μHE[m] := by
            apply setLIntegral_mono measurable_const
            rintro x ⟨-, hx⟩
            rw [mem_ball_zero_iff] at hx
            exact ENNReal.ofReal_le_one.2 (Real.rpow_le_one (norm_nonneg x) hx.le hα0)
        _ = μHE[m] (M ∩ ball (0 : Euclid P) 1) := by rw [setLIntegral_const, one_mul]
        _ ≤ μHE[m] (M ∩ closedBall (0 : Euclid P) 1) :=
            measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
    · refine hgeo α (1 / 2) 1 (1 / 2) _ hα0.le (by norm_num) one_pos (by norm_num) ?_ ?_
      · -- `2^{-α}2^{-m} = 2^{-(m+α)} < 1`
        rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
        exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
      · -- `0 < |x| < 1` as `0 ∉ M`, so `2⁻ᵏ⁻¹ < |x| ≤ 2⁻ᵏ` for some `k`
        rintro x ⟨hxM, hx⟩
        rw [mem_ball_zero_iff] at hx
        have hxpos : 0 < ‖x‖ := norm_pos_iff.2 (by rintro rfl; exact h0 hxM)
        obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hxpos hx.le
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        refine mem_iUnion.2 ⟨k, hxM, ?_, ?_⟩
        · rw [← pow_succ']; exact hk1.le
        · rw [one_mul]; exact hk2
  · -- (c) `β < −m ≤ 0`; shells `2ᵏ ≤ |x| ≤ 2ᵏ⁺¹`
    intro β hβ
    have hβ0 : β < 0 := by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    refine hgeo β 1 2 2 _ hβ0.le one_pos two_pos two_pos ?_ ?_
    · -- `2^β2^m = 2^{m+β} < 1`
      rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
      exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
    · -- `|x| ≥ 1`, so `2ᵏ ≤ |x| < 2ᵏ⁺¹` for some `k`
      rintro x ⟨hxM, hx⟩
      rw [mem_ball_zero_iff, not_lt] at hx
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx one_lt_two
      refine mem_iUnion.2 ⟨k, hxM, ?_, ?_⟩
      · rw [one_mul]; exact hk1
      · rw [← pow_succ']; exact hk2.le
/-- **Rademacher's theorem on an embedded `C¹` submanifold** (Simon Ch. 2, 4.8–4.9, via
Rademacher's theorem 1.4 in local coordinates).  If `M ⊆ ℝᴾ` is an embedded `C¹` `m`-dimensional
submanifold and `f` is locally Lipschitz on `M`, then `f` is differentiable within `M` at
`Hᵐ`-a.e. point of `M`.  The given charts `(V, W, ψ)` are used directly.  As `ψ` is proper and
injective, `M ∩ B_δ(ψ(b)) ⊆ ψ(V₀)` for every open `V₀ ∋ b`.  With `Q` a linear left inverse of
`Dψ(b)`, the inverse function theorem for `Q ∘ ψ` gives a local inverse `Θ`, differentiable at
`Q(ψ(b))`, so `f = (f ∘ ψ) ∘ Θ ∘ Q` on `M` near `ψ(b)`: if `f ∘ ψ` is differentiable at `b`, then
`f` is differentiable within `M` at `ψ(b)`.  On an open `B ∋ a` where `ψ` and `f ∘ ψ` are
Lipschitz, Rademacher's theorem makes `f ∘ ψ` differentiable off an `Lᵐ`-null set `N`, and
`Hᵐ(ψ(N)) ≤ Λᵐ Lᵐ(N) = 0`.  `M = O ∩ closure M` (`O` the union of the chart domains) is Borel,
and countably many of these neighbourhoods cover `M`. -/
theorem Submission.codim1_hcp_sc_rademacher_submanifold : ∀ (P m : ℕ) (M : Set (Euclid P)) (f : Euclid P → ℝ), IsEmbeddedSubmanifold 1 m M → LocallyLipschitzOn M f → ∀ᵐ x ∂(μHE[m].restrict M), DifferentiableWithinAt ℝ f M x := by
  intro P m M f hM hf
  -- step 1: `M` is Borel, as `M = O ∩ closure M` with `O` the union of the chart domains
  have hMmeas : MeasurableSet M := by
    have key : ∀ y ∈ M, ∃ W : Set (Euclid P), IsOpen W ∧ y ∈ W ∧
        ∀ K ⊆ W, IsCompact K → IsClosed (M ∩ K) := by
      intro y hy
      obtain ⟨V, W, ψ, -, hW, hyW, hψ, -, himg, hprop, -⟩ := hM y hy
      refine ⟨W, hW, hyW, fun K hKW hK => ?_⟩
      have hEq : M ∩ K = ψ '' (V ∩ ψ ⁻¹' K) := by
        ext x
        constructor
        · rintro ⟨hxM, hxK⟩
          obtain ⟨v, hv, rfl⟩ : x ∈ ψ '' V := by rw [himg]; exact ⟨hKW hxK, hxM⟩
          exact ⟨v, ⟨hv, hxK⟩, rfl⟩
        · rintro ⟨v, ⟨hv, hvK⟩, rfl⟩
          exact ⟨(himg ▸ mem_image_of_mem ψ hv : ψ v ∈ W ∩ M).2, hvK⟩
      rw [hEq]
      exact ((hprop K hKW hK).image_of_continuousOn
        (hψ.continuousOn.mono inter_subset_left)).isClosed
    choose! Wf hWo hyW hcl using key
    have hMeq : M = (⋃ y ∈ M, Wf y) ∩ closure M := by
      refine Subset.antisymm (fun x hx => ⟨mem_biUnion hx (hyW x hx), subset_closure hx⟩) ?_
      rintro p ⟨hpO, hpcl⟩
      obtain ⟨y, hy, hpW⟩ := mem_iUnion₂.1 hpO
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hWo y hy) p hpW
      have hC := hcl y hy (closedBall p (r / 2))
        ((closedBall_subset_ball (by linarith)).trans hball) (isCompact_closedBall p (r / 2))
      have h1 : p ∈ ball p (r / 2) ∩ closure M := ⟨mem_ball_self (by linarith), hpcl⟩
      have hsub : ball p (r / 2) ∩ M ⊆ M ∩ closedBall p (r / 2) :=
        fun x hx => ⟨hx.2, ball_subset_closedBall hx.1⟩
      have h3 : p ∈ closure (M ∩ closedBall p (r / 2)) :=
        closure_mono hsub (isOpen_ball.inter_closure h1)
      rw [hC.closure_eq] at h3
      exact h3.1
    rw [hMeq]
    exact (isOpen_biUnion fun y hy => hWo y hy).measurableSet.inter isClosed_closure.measurableSet
  -- step 2: near each `p ∈ M`, `f` is differentiable within `M` off an `Hᵐ`-null set
  have hloc : ∀ p ∈ M, ∃ O : Set (Euclid P), IsOpen O ∧ p ∈ O ∧ ∃ E : Set (Euclid P),
      μHE[m] E = 0 ∧ ∀ x ∈ M ∩ O, x ∉ E → DifferentiableWithinAt ℝ f M x := by
    intro p hp
    obtain ⟨V, W, ψ, hV, hW, hpW, hψ, hinj, himg, hprop, hDψ⟩ := hM p hp
    have hψ1 : ContDiffOn ℝ 1 ψ V := by exact_mod_cast hψ
    have hψM : ∀ c ∈ V, ψ c ∈ M := fun c hc => (himg ▸ mem_image_of_mem ψ hc : ψ c ∈ W ∩ M).2
    -- (a) `M ∩ B_δ(ψ(b)) ⊆ ψ(V₀)` for open `V₀ ∋ b`, as `ψ` is proper and injective
    have himgnhds : ∀ b ∈ V, ∀ V₀ : Set (Euclid m), IsOpen V₀ → V₀ ⊆ V → b ∈ V₀ →
        ∃ δ : ℝ, 0 < δ ∧ M ∩ ball (ψ b) δ ⊆ ψ '' V₀ := by
      intro b hb V₀ hV₀ hV₀V hbV₀
      have hbW : ψ b ∈ W := (himg ▸ mem_image_of_mem ψ hb : ψ b ∈ W ∩ M).1
      obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW _ hbW
      have hKW : closedBall (ψ b) (ε / 2) ⊆ W :=
        (closedBall_subset_ball (by linarith)).trans hεW
      -- `C = (V ∩ ψ⁻¹(K)) \ V₀` is compact, so its image is closed and misses `ψ(b)`
      have hCc : IsClosed (ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ b) (ε / 2)) \ V₀)) :=
        (((hprop _ hKW (isCompact_closedBall _ _)).diff hV₀).image_of_continuousOn
          (hψ1.continuousOn.mono fun c hc => hc.1.1)).isClosed
      have hbC : ψ b ∉ ψ '' ((V ∩ ψ ⁻¹' closedBall (ψ b) (ε / 2)) \ V₀) := by
        rintro ⟨c, ⟨⟨hcV, -⟩, hcV₀⟩, hc⟩
        exact hcV₀ (hinj hcV hb hc ▸ hbV₀)
      obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 hCc.isOpen_compl _ hbC
      refine ⟨min (ε / 2) δ, lt_min (by linarith) hδ, fun y hy => ?_⟩
      have hyK : y ∈ closedBall (ψ b) (ε / 2) :=
        ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hy.2)
      obtain ⟨c, hcV, rfl⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hKW hyK, hy.1⟩
      refine ⟨c, ?_, rfl⟩
      by_contra hcV₀
      exact hδC (ball_subset_ball (min_le_right _ _) hy.2) ⟨c, ⟨⟨hcV, hyK⟩, hcV₀⟩, rfl⟩
    -- (b) if `f ∘ ψ` is differentiable at `b`, then `f` is differentiable within `M` at `ψ(b)`
    have htransfer : ∀ b ∈ V, DifferentiableAt ℝ (f ∘ ψ) b →
        DifferentiableWithinAt ℝ f M (ψ b) := by
      intro b hb hdiff
      -- a continuous linear left inverse `Q` of the injective `Dψ(b)`
      obtain ⟨Q₀, hQ₀⟩ := LinearMap.exists_leftInverse_of_injective
        (fderiv ℝ ψ b : Euclid m →ₗ[ℝ] Euclid P) (LinearMap.ker_eq_bot.2 (hDψ b hb))
      let Q : Euclid P →L[ℝ] Euclid m := LinearMap.toContinuousLinearMap Q₀
      have hQ : ∀ v, Q (fderiv ℝ ψ b v) = v := fun v => LinearMap.congr_fun hQ₀ v
      -- `Φ = Q ∘ ψ` has strict derivative `id` at `b`
      have hψs : HasStrictFDerivAt ψ (fderiv ℝ ψ b) b :=
        (hψ1.contDiffAt (hV.mem_nhds hb)).hasStrictFDerivAt one_ne_zero
      have hΦ : HasStrictFDerivAt (Q ∘ ψ)
          ((ContinuousLinearEquiv.refl ℝ (Euclid m) : Euclid m ≃L[ℝ] Euclid m) :
            Euclid m →L[ℝ] Euclid m) b := by
        have hQψ : Q.comp (fderiv ℝ ψ b) =
            ((ContinuousLinearEquiv.refl ℝ (Euclid m) : Euclid m ≃L[ℝ] Euclid m) :
              Euclid m →L[ℝ] Euclid m) :=
          ContinuousLinearMap.ext fun v => hQ v
        rw [← hQψ]
        exact Q.hasStrictFDerivAt.comp b hψs
      -- the inverse function theorem: a local inverse `Θ` of `Φ`, differentiable at `Φ(b)`
      set Θ := hΦ.localInverse (Q ∘ ψ) _ b
      have hΘ := hΦ.to_localInverse
      have hleft : ∀ᶠ c in 𝓝 b, Θ ((Q ∘ ψ) c) = c := hΦ.eventually_left_inverse
      obtain ⟨V₁, hV₁sub, hV₁o, hbV₁⟩ := _root_.mem_nhds_iff.1 hleft
      obtain ⟨δ, hδ, hδsub⟩ :=
        himgnhds b hb (V₁ ∩ V) (hV₁o.inter hV) inter_subset_right ⟨hbV₁, hb⟩
      have hΘb : Θ (Q (ψ b)) = b := hleft.self_of_nhds
      -- `f = (f ∘ ψ) ∘ Θ ∘ Q` on `M ∩ B_δ(ψ(b))`, and the right side is differentiable at `ψ(b)`
      have hg : DifferentiableAt ℝ ((f ∘ ψ) ∘ Θ ∘ Q) (ψ b) := by
        have h1 : DifferentiableAt ℝ (f ∘ ψ) (Θ (Q (ψ b))) := by rw [hΘb]; exact hdiff
        exact h1.comp (ψ b) (hΘ.differentiableAt.comp (ψ b) Q.differentiableAt)
      refine hg.differentiableWithinAt.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [inter_mem_nhdsWithin M (ball_mem_nhds (ψ b) hδ)] with y hy
        obtain ⟨c, ⟨hc₁, -⟩, rfl⟩ := hδsub hy
        have hc : Θ (Q (ψ c)) = c := hV₁sub hc₁
        simp only [Function.comp_apply, hc]
      · simp only [Function.comp_apply, hΘb]
    -- (c) `ψ` and `f ∘ ψ` are Lipschitz on an open `B ∋ a`, where `ψ(a) = p`
    obtain ⟨a, haV, rfl⟩ : p ∈ ψ '' V := by rw [himg]; exact ⟨hpW, hp⟩
    obtain ⟨K, t, ht, hft⟩ := hf hp
    obtain ⟨U, hUo, haU, hUt⟩ := mem_nhdsWithin.1 ht
    have hψa : ContDiffAt ℝ 1 ψ a := hψ1.contDiffAt (hV.mem_nhds haV)
    obtain ⟨Λ, s, hs, hψs⟩ := hψa.exists_lipschitzOnWith
    obtain ⟨B, hBsub, hBo, haB⟩ := _root_.mem_nhds_iff.1 (inter_mem (inter_mem (hV.mem_nhds haV) hs)
      (hψa.continuousAt.preimage_mem_nhds (hUo.mem_nhds haU)))
    have hBV : B ⊆ V := fun c hc => (hBsub hc).1.1
    have hψB : LipschitzOnWith Λ ψ B := hψs.mono fun c hc => (hBsub hc).1.2
    have hfB : LipschitzOnWith (K * Λ) (f ∘ ψ) B :=
      hft.comp hψB fun c hc => hUt ⟨(hBsub hc).2, hψM c (hBV hc)⟩
    -- (d) Rademacher: `f ∘ ψ` is differentiable on `B` off the `Lᵐ`-null set `N`
    let N : Set (Euclid m) := {c | c ∈ B ∧ ¬ DifferentiableAt ℝ (f ∘ ψ) c}
    have hN : volume N = 0 := by
      have hrad := hfB.ae_differentiableWithinAt_of_mem (μ := volume)
      rw [ae_iff] at hrad
      refine measure_mono_null (fun c hc => ?_) hrad
      simp only [mem_ofPred_eq, not_imp]
      exact ⟨hc.1, fun hd => hc.2 (hd.differentiableAt (hBo.mem_nhds hc.1))⟩
    obtain ⟨δ, hδ, hδB⟩ := himgnhds a haV B hBo hBV haB
    refine ⟨ball (ψ a) δ, isOpen_ball, mem_ball_self hδ, ψ '' N, ?_, ?_⟩
    · -- (e) `Hᵐ(ψ(N)) ≤ Λᵐ Lᵐ(N) = 0`
      have h := (hψB.mono fun c (hc : c ∈ N) => hc.1).hausdorffMeasure_image_le
        (d := (m : ℝ)) (Nat.cast_nonneg m)
      rw [ENNReal.rpow_natCast] at h
      have h2 : μHE[m] (ψ '' N) ≤ (Λ : ℝ≥0∞) ^ m * volume N := by
        rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume m,
          Measure.euclideanHausdorffMeasure_def, Measure.euclideanHausdorffMeasure_def]
        simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
        calc _ ≤ _ := mul_le_mul_right h _
          _ = _ := by ring
      rw [hN, mul_zero] at h2
      exact le_antisymm h2 zero_le
    · -- (f) off `ψ(N)`, each `x ∈ M ∩ B_δ(ψ(a))` is `ψ(c)` with `f ∘ ψ` differentiable at `c`
      intro x hx hxE
      obtain ⟨c, hcB, rfl⟩ := hδB hx
      refine htransfer c (hBV hcB) ?_
      by_contra hnd
      exact hxE ⟨c, ⟨hcB, hnd⟩, rfl⟩
  -- step 3: countably many of the neighbourhoods `O p` cover `M` (second countability)
  choose! O hOo hpO E hE hdiff using hloc
  obtain ⟨T, hTM, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable M O hOo
  have hnull : μHE[m] (⋃ p ∈ T, E p) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun p hp => hE p (hTM hp)
  rw [ae_restrict_iff' hMmeas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [mem_ofPred_eq, not_imp] at hx
  obtain ⟨hxM, hxnd⟩ := hx
  have hxU : x ∈ ⋃ p ∈ M, O p := mem_iUnion₂.2 ⟨x, hxM, hpO x hxM⟩
  rw [← hTU] at hxU
  obtain ⟨p, hpT, hxO⟩ := mem_iUnion₂.1 hxU
  refine mem_iUnion₂.2 ⟨p, hpT, ?_⟩
  by_contra hxE
  exact hxnd (hdiff p (hTM hpT) x ⟨hxM, hxO⟩ hxE)
/-- **Weingarten map and Codazzi equations of a hypersurface** (Simon, Appendix B, B.4–B.5,
p. 231; cf. Ch. 2, 4.26).  Let `M ⊆ A₀` be an `m`-dimensional submanifold of the
`(m + 1)`-dimensional subspace `A₀`, `C^r` for every `r`, with unit normal `ν` in `A₀` that is
`C^∞` on an open `O ⊇ M`, and let `C(y) = Dν(y) ∘ P_y`.  For `x ∈ M` and `a, b, d ∈ T_xM`:
(i) `Dν(x)a ∈ T_xM`; (ii) `Dν(x)a · b = Dν(x)b · a` (B.4); (iii) `(D_aC)(b) · d = (D_bC)(a) · d`
(Codazzi, B.5); (iv) `(D_aC)(b) · d = (D_aC)(d) · b`.
(i): differentiate `ν(γ(t)) ∈ A₀` and `|ν(γ(t))|² = 1` along a curve `γ` with `γ'(0) = a`, and
use `T_xM = A₀ ∩ ν(x)^⊥` (`Submission.codim1_hcp_sc_tangent_normal_complement`).  (ii): in a
`C²` chart `ψ`, differentiate `ν(ψ(v)) · Dψ(v)e = 0` and use the symmetry of `D²ψ`.  On `M`,
`C = C̃ := Dν ∘ (Π − ν ⊗ ν)`, which is differentiable at `x`, so `D_aC = DC̃(x)a`
(`Submission.codim1_hcp_sc_fderivWithin_tangent_eq`) and
`(D_aC)(b) = D²ν(x)(a, b) − (Dν(x)a · b) Dν(x)ν(x)`; (iii) follows from the symmetry of
`D²ν(x)` and (ii).  (iv): by (i) and (ii), `C(y)u · w = C(y)w · u` for `y ∈ M`; differentiate
this identity along `M`. -/
theorem Submission.codim1_hcp_sc_weingarten_codazzi : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, ∀ a ∈ tangentSpace M x, ∀ b ∈ tangentSpace M x, fderiv ℝ ν x a ∈ tangentSpace M x ∧ inner ℝ (fderiv ℝ ν x a) b = inner ℝ (fderiv ℝ ν x b) a ∧ ∀ d ∈ tangentSpace M x, inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a b) d = inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x b a) d ∧ inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a b) d = inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a d) b := by
  intro P m A₀ M ν hA hMA hM hO hν x hx a ha b hb
  obtain ⟨O, hOo, hMO, hνO⟩ := hO
  -- Step 0: `T_y = {v ∈ A₀ : ν(y) · v = 0}` and `P_y w = Π w − (ν(y) · w) ν(y)` on `M`
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hA hMA (hM 1) hν
  -- `ν` is `C^∞` near every point of `M`
  have hνc : ∀ y ∈ M, ContDiffAt ℝ (⊤ : ℕ∞) ν y := fun y hy =>
    hνO.contDiffAt (hOo.mem_nhds (hMO hy))
  have hνd : ∀ y ∈ M, HasFDerivAt ν (fderiv ℝ ν y) y := fun y hy =>
    ((hνc y hy).differentiableAt (by simp)).hasFDerivAt
  -- `T_y` is a linear subspace, so `span T_y = T_y`
  have hspan : ∀ y ∈ M, ∀ v ∈ Submodule.span ℝ (tangentSpace M y), v ∈ tangentSpace M y := by
    intro y hy v hv
    rw [(hNC y hy).1] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem w hw => exact hw
    | zero => exact ⟨A₀.zero_mem, inner_zero_right _⟩
    | add u w _ _ hu hw =>
      exact ⟨A₀.add_mem hu.1 hw.1, by rw [inner_add_right, hu.2, hw.2, add_zero]⟩
    | smul c u _ hu => exact ⟨A₀.smul_mem c hu.1, by rw [inner_smul_right, hu.2, mul_zero]⟩
  -- Step 1 (i): `Dν(y) a ∈ T_y`, differentiating `ν(γ(t)) ∈ A₀` and `|ν(γ(t))|² = 1`
  have hi : ∀ y ∈ M, ∀ a ∈ tangentSpace M y, fderiv ℝ ν y a ∈ tangentSpace M y := by
    intro y hy a ha
    obtain ⟨γ, -, hγM, hγ0, hγa⟩ := ha
    have hc : HasDerivAt (ν ∘ γ) (fderiv ℝ ν y a) 0 :=
      (hνd y hy).comp_hasDerivAt_of_eq 0 hγa hγ0.symm
    have hI : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have h0I : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    rw [(hNC y hy).1]
    refine ⟨?_, ?_⟩
    · -- the difference quotients of `ν ∘ γ` lie in the closed subspace `A₀`
      refine A₀.closed_of_finiteDimensional.mem_of_tendsto hc.tendsto_slope ?_
      filter_upwards [nhdsWithin_le_nhds hI] with t ht
      rw [slope_def_module]
      exact A₀.smul_mem _ (A₀.sub_mem (hν _ (hγM ht)).1 (hν _ (hγM h0I)).1)
    · -- `|ν ∘ γ|² = 1` near `0`, so `2 ν(y) · Dν(y) a = 0`
      have hconst : (fun t => ‖(ν ∘ γ) t‖ ^ 2) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
        filter_upwards [hI] with t ht
        simp [(hν _ (hγM ht)).2.1]
      have h0 := hc.norm_sq.unique ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq hconst)
      simp only [Function.comp_apply, hγ0] at h0
      linarith
  -- Step 2 (ii): `Dν(y) a · b = Dν(y) b · a`, from a `C²` chart and the symmetry of `D²ψ`
  have hii : ∀ y ∈ M, ∀ a ∈ tangentSpace M y, ∀ b ∈ tangentSpace M y,
      inner ℝ (fderiv ℝ ν y a) b = inner ℝ (fderiv ℝ ν y b) a := by
    intro y hy a ha b hb
    obtain ⟨V, W, ψ, hV, hW, hyW, hψ, hinj, himg, hprop, hder⟩ := hM 2 y hy
    obtain ⟨v₀, hv₀, rfl⟩ : y ∈ ψ '' V := by rw [himg]; exact ⟨hyW, hy⟩
    have hT : ∀ v ∈ V, tangentSpace M (ψ v) = range (fderiv ℝ ψ v) := fun v hv =>
      Submission.chart_tangentSpace_eq_range_fderiv P m 2 M W V ψ v (by norm_num) hV hW hψ hinj
        himg hprop hder hv
    rw [hT v₀ hv₀] at ha hb
    obtain ⟨e₁, rfl⟩ := ha
    obtain ⟨e₂, rfl⟩ := hb
    have hψc := hψ.contDiffAt (hV.mem_nhds hv₀)
    have hψd : HasFDerivAt ψ (fderiv ℝ ψ v₀) v₀ := (hψc.differentiableAt (by simp)).hasFDerivAt
    have hDψd : HasFDerivAt (fderiv ℝ ψ) (fderiv ℝ (fderiv ℝ ψ) v₀) v₀ :=
      ((hψc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)).hasFDerivAt
    have hsymm : IsSymmSndFDerivAt ℝ ψ v₀ := hψc.isSymmSndFDerivAt (by simp)
    -- `v ↦ ν(ψ(v)) · Dψ(v) e` vanishes on `V`; its derivative in direction `e'` at `v₀`
    have key : ∀ e e' : Euclid m, inner ℝ (ν (ψ v₀)) (fderiv ℝ (fderiv ℝ ψ) v₀ e' e) +
        inner ℝ (fderiv ℝ ν (ψ v₀) (fderiv ℝ ψ v₀ e')) (fderiv ℝ ψ v₀ e) = 0 := by
      intro e e'
      have hzero : (fun v => inner ℝ ((ν ∘ ψ) v) (fderiv ℝ ψ v e)) =ᶠ[𝓝 v₀] fun _ => (0 : ℝ) := by
        filter_upwards [hV.mem_nhds hv₀] with v hv
        have hvM : ψ v ∈ M := (himg ▸ mem_image_of_mem ψ hv : ψ v ∈ W ∩ M).2
        exact (hν (ψ v) hvM).2.2 _ (by rw [hT v hv]; exact mem_range_self e)
      have hd := ((hνd (ψ v₀) hy).comp v₀ hψd).inner ℝ (hDψd.clm_apply (hasFDerivAt_const e v₀))
      have h0 := congrArg (fun L => L e')
        (hd.unique ((hasFDerivAt_const (0 : ℝ) v₀).congr_of_eventuallyEq hzero))
      simpa using h0
    have h1 := key e₂ e₁
    have h2 := key e₁ e₂
    rw [hsymm e₁ e₂] at h1
    linarith
  -- Step 3: `C = C̃` on `M`, where `C̃(y) = Dν(y) ∘ (Π − ν(y) ⊗ ν(y))` is differentiable at `x`
  set Ct : Euclid P → (Euclid P →L[ℝ] Euclid P) := fun y =>
    (fderiv ℝ ν y).comp (A₀.starProjection - (innerSL ℝ (ν y)).smulRight (ν y)) with hCt
  have hCeq : ∀ y ∈ M,
      (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection = Ct y := by
    intro y hy
    refine ContinuousLinearMap.ext fun w => ?_
    simp [hCt, (hNC y hy).2 w]
  have hν1 : ContDiffAt ℝ 1 ν x := (hνc x hx).of_le (by simp)
  have hDν1 : ContDiffAt ℝ 1 (fderiv ℝ ν) x := (hνc x hx).fderiv_right (by simp)
  have hD2 : HasFDerivAt (fderiv ℝ ν) (fderiv ℝ (fderiv ℝ ν) x) x :=
    (hDν1.differentiableAt (by simp)).hasFDerivAt
  have hCtd : HasFDerivAt Ct (fderiv ℝ Ct x) x := by
    have hCt1 : ContDiffAt ℝ 1 Ct x := hDν1.clm_comp (contDiffAt_const.sub
      ((((innerSL ℝ : Euclid P →L[ℝ] Euclid P →L[ℝ] ℝ).contDiff.contDiffAt).comp x hν1).smulRight
        hν1))
    exact (hCt1.differentiableAt (by simp)).hasFDerivAt
  -- `D_a C = DC̃(x) a` for `a ∈ T_x` (sibling `tangent_fderiv`)
  have hDC : ∀ a' ∈ tangentSpace M x, fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp
      (Submodule.span ℝ (tangentSpace M y)).starProjection) M x a' = fderiv ℝ Ct x a' :=
    fun a' ha' => Submission.codim1_hcp_sc_fderivWithin_tangent_eq P (Euclid P →L[ℝ] Euclid P) M _ _
      x (hCtd.hasFDerivWithinAt.congr hCeq (hCeq x hx)) a' (Submodule.subset_span ha')
  have hmemT : ∀ v ∈ tangentSpace M x, v ∈ A₀ ∧ inner ℝ (ν x) v = 0 := fun v hv => by
    rw [(hNC x hx).1] at hv
    exact hv
  -- `(D_a C)(b) = D²ν(x)(a, b) − (Dν(x) a · b) Dν(x) ν(x)` for `b ∈ A₀` with `ν(x) · b = 0`
  have hformula : ∀ a' b', b' ∈ A₀ → inner ℝ (ν x) b' = 0 → fderiv ℝ Ct x a' b' =
      fderiv ℝ (fderiv ℝ ν) x a' b' - inner ℝ (fderiv ℝ ν x a') b' • fderiv ℝ ν x (ν x) := by
    intro a' b' hbA hbν
    have hF : (fun y => Ct y b') =
        fun y => fderiv ℝ ν y b' - inner ℝ (ν y) b' • fderiv ℝ ν y (ν y) := by
      funext y
      simp [hCt, Submodule.starProjection_eq_self_iff.mpr hbA]
    have h1 := hCtd.clm_apply (hasFDerivAt_const b' x)
    rw [hF] at h1
    have h2 := (hD2.clm_apply (hasFDerivAt_const b' x)).sub
      (((hνd x hx).inner ℝ (hasFDerivAt_const b' x)).smul (hD2.clm_apply (hνd x hx)))
    have h3 := congrArg (fun L => L a') (h1.unique h2)
    simpa [hbν] using h3
  have hsymmν : IsSymmSndFDerivAt ℝ ν x := (hνc x hx).isSymmSndFDerivAt (by simp)
  refine ⟨hi x hx a ha, hii x hx a ha b hb, fun d hd => ⟨?_, ?_⟩⟩
  · -- Step 4 (iii), Codazzi: symmetry of `D²ν(x)` and (ii)
    rw [hDC a ha, hDC b hb, hformula a b (hmemT b hb).1 (hmemT b hb).2,
      hformula b a (hmemT a ha).1 (hmemT a ha).2, hsymmν a b, hii x hx a ha b hb]
  · -- Step 5 (iv): `C(y) u · w = C(y) w · u` on `M`; differentiate along `M`
    have hsymC : ∀ y ∈ M, ∀ u w : Euclid P, inner ℝ (Ct y u) w = inner ℝ (Ct y w) u := by
      intro y hy u w
      rw [← hCeq y hy]
      set K := Submodule.span ℝ (tangentSpace M y)
      have hPu : K.starProjection u ∈ tangentSpace M y :=
        hspan y hy _ (K.starProjection_apply_mem u)
      have hPw : K.starProjection w ∈ tangentSpace M y :=
        hspan y hy _ (K.starProjection_apply_mem w)
      have h1 : fderiv ℝ ν y (K.starProjection u) ∈ K := Submodule.subset_span (hi y hy _ hPu)
      have h2 : fderiv ℝ ν y (K.starProjection w) ∈ K := Submodule.subset_span (hi y hy _ hPw)
      simp only [ContinuousLinearMap.comp_apply]
      calc inner ℝ (fderiv ℝ ν y (K.starProjection u)) w
          = inner ℝ (K.starProjection (fderiv ℝ ν y (K.starProjection u))) w := by
            rw [Submodule.starProjection_eq_self_iff.mpr h1]
        _ = inner ℝ (fderiv ℝ ν y (K.starProjection u)) (K.starProjection w) :=
            K.inner_starProjection_left_eq_right _ _
        _ = inner ℝ (fderiv ℝ ν y (K.starProjection w)) (K.starProjection u) :=
            hii y hy _ hPu _ hPw
        _ = inner ℝ (K.starProjection (fderiv ℝ ν y (K.starProjection w))) u :=
            (K.inner_starProjection_left_eq_right _ _).symm
        _ = inner ℝ (fderiv ℝ ν y (K.starProjection w)) u := by
            rw [Submodule.starProjection_eq_self_iff.mpr h2]
    have hs0 : EqOn (fun y => inner ℝ (Ct y b) d - inner ℝ (Ct y d) b) (fun _ => (0 : ℝ)) M :=
      fun y hy => sub_eq_zero.mpr (hsymC y hy b d)
    have hsd : HasFDerivAt (fun y => inner ℝ (Ct y b) d - inner ℝ (Ct y d) b) _ x :=
      ((hCtd.clm_apply (hasFDerivAt_const b x)).inner ℝ (hasFDerivAt_const d x)).sub
        ((hCtd.clm_apply (hasFDerivAt_const d x)).inner ℝ (hasFDerivAt_const b x))
    have e1 := Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x
      ((hasFDerivWithinAt_const (0 : ℝ) x M).congr hs0 (hs0 hx)) a (Submodule.subset_span ha)
    have e2 := Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x
      hsd.hasFDerivWithinAt a (Submodule.subset_span ha)
    rw [e1] at e2
    rw [hDC a ha]
    exact sub_eq_zero.mp (by simpa using e2.symm)

/-- **Simon, Appendix B, B.8 (Simons' identity) for a minimal hypersurface of `A₀`**: for every
`x ∈ M`, `Δ_M |A|²(x) = 2 |∇A|²(x) − 2 (|A|²(x))²`, where `δⱼ g = D^M g (P eⱼ)`,
`Δ_M = Σⱼ δⱼ δⱼ`, `|A|² = Σᵢ |Dν(P eᵢ)|²` and `∇A` is the tangential derivative of
`C = Dν ∘ P`.

The proof is the frame-free form of B.4–B.9 (the elementary derivation of [Giu84, Ch. 10] that
Simon cites before B.4).  On the open `O ⊇ M` put `Q(z) w = Π w − ⟨ν(z), w⟩ ν(z)` (`Π` the
projection onto `A₀`), `C(z) = Dν(z) ∘ Q(z)` and `δ_b f(z) = Df(z) (Q(z) b)`.  By
`codim1_hcp_sc_tangent_normal_complement`, `Q(y) = P_y` on `M`, and by
`codim1_hcp_sc_fderivWithin_tangent_eq`, `fderivWithin` along `T_y M` is the derivative of any
ambient smooth extension; so every quantity of the statement is an ambient one.  Then:
* `δ`-derivatives only see values on `M`;
* `δ_a δ_b f − δ_b δ_a f = ⟨ν, a⟩ Df(C b) − ⟨ν, b⟩ Df(C a)` on `M`, by the symmetry of `D²f` and
  of the Weingarten map (B.4, `codim1_hcp_sc_weingarten_codazzi`).  For `f = ν` this is Codazzi
  (B.5); applied to `f = C` it replaces the Gauss and Ricci identities (B.6–B.7);
* contracting Codazzi and using `H = tr C = 0` on `M`: `Σⱼ δⱼ C eⱼ = −|A|² ν` on `M`;
* B.8–B.9: the product rule, the splitting `Σⱼ |δⱼ C|² = |∇A|² + 2 Σⱼ |C² eⱼ|²` and
  `Σᵢ ⟨C eᵢ, Σⱼ δⱼ δⱼ C eᵢ⟩ = −|A|⁴ − 2 Σⱼ |C² eⱼ|²` give `Δ_M |A|² = 2 |∇A|² − 2 |A|⁴`. -/
theorem Submission.codim1_hcp_sc_simons_identity : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → ∀ x ∈ M, (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) = 2 * (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P, (inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1)) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) - 2 * (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) ^ 2 := by
  intro P m A₀ M ν hdim hMA hM hO hν htr x hx
  refine Exists.elim hO fun O hO' => ?_
  have hOo : IsOpen O := hO'.1
  have hMO : M ⊆ O := hO'.2.1
  have hνO : ContDiffOn ℝ (⊤ : ℕ∞) ν O := hO'.2.2
  have hxO : x ∈ O := hMO hx
  have NC' := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hdim hMA (hM 1) hν
  have WC' := Submission.codim1_hcp_sc_weingarten_codazzi P m A₀ M ν hdim hMA hM
    ⟨O, hOo, hMO, hνO⟩ hν
  /- The standard basis `eⱼ` of `ℝᴾ`: Parseval's identity and its consequences. -/
  refine Exists.elim (⟨_, rfl⟩ : ∃ e : Fin P → Euclid P, e = fun i => EuclideanSpace.single i 1)
    fun e he => ?_
  have hpar : ∀ u v : Euclid P, ∑ i, inner ℝ u (e i) * inner ℝ v (e i) = inner ℝ u v := by
    intro u v
    have h := (EuclideanSpace.basisFun (Fin P) ℝ).sum_inner_mul_inner u v
    simp only [EuclideanSpace.basisFun_apply] at h
    rw [← h, he]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm v]
  have hexp : ∀ u : Euclid P, ∑ i, inner ℝ u (e i) • e i = u := by
    intro u
    have h := (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr' u
    simp only [EuclideanSpace.basisFun_apply] at h
    conv_rhs => rw [← h]
    rw [he]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
  have hsq : ∀ u : Euclid P, ∑ i, inner ℝ u (e i) ^ 2 = ‖u‖ ^ 2 := by
    intro u
    rw [← real_inner_self_eq_norm_sq, ← hpar]
    exact Finset.sum_congr rfl fun j _ => sq _
  have hinclm : ∀ (W : Euclid P →L[ℝ] Euclid P) (n v : Euclid P),
      ∑ i, inner ℝ n (e i) * inner ℝ (W (e i)) v = inner ℝ (W n) v := by
    intro W n v
    conv_rhs => rw [← hexp n]
    rw [map_sum, sum_inner]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, real_inner_smul_left]
  have hsmclm : ∀ (T : Euclid P →L[ℝ] Euclid P) (u : Euclid P),
      ∑ i, inner ℝ u (e i) • T (e i) = T u := by
    intro T u
    conv_rhs => rw [← hexp u]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (map_smul T _ _).symm
  /- Step B (linear algebra): `Σⱼ |L_j|²` splits into the tangential block and twice
  `Σⱼ |S² eⱼ|²`, given the normal parts of `L_j` in both slots. -/
  have hstepB : ∀ (n : Euclid P) (S R : Euclid P →L[ℝ] Euclid P)
      (L : Fin P → Euclid P →L[ℝ] Euclid P), ‖n‖ = 1 → R n = 0 →
      (∀ w, inner ℝ n (R w) = 0) → (∀ w, inner ℝ n (S w) = 0) →
      (∀ u v, inner ℝ (R u) v = inner ℝ u (R v)) → (∀ w, S (R w) = S w) →
      (∀ u v, inner ℝ (S u) v = inner ℝ u (S v)) →
      (∀ j b, L j b - L j (R b) = -(inner ℝ n b • S (S (e j)))) →
      (∀ j b, L j b - R (L j b) = -(inner ℝ (S (e j)) (S b) • n)) →
      ∑ j, ∑ i, ‖L j (e i)‖ ^ 2 =
        ∑ j, ∑ i, ∑ k, inner ℝ (L j (R (e i))) (R (e k)) ^ 2 + 2 * ∑ j, ‖S (S (e j))‖ ^ 2 := by
    intro n S R L hn hRn hnR hnS hRsymm hSR hSsymm hLin' hLout'
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hnn : inner ℝ n n = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    have hnw : inner ℝ n (S (S (e j))) = 0 := hnS _
    -- `L_j eᵢ = R L_j R eᵢ − ⟨n, eᵢ⟩ S² eⱼ − ⟨S² eⱼ, eᵢ⟩ n`
    have hdec : ∀ i, L j (e i) = R (L j (R (e i))) - inner ℝ n (e i) • S (S (e j)) -
        inner ℝ (S (S (e j))) (e i) • n := by
      intro i
      have h1 := hLin' j (e i)
      have h2 := hLout' j (R (e i))
      rw [hSR, ← hSsymm (S (e j)) (e i)] at h2
      calc L j (e i) = (L j (e i) - L j (R (e i))) + (L j (R (e i)) - R (L j (R (e i)))) +
            R (L j (R (e i))) := by abel
        _ = R (L j (R (e i))) - inner ℝ n (e i) • S (S (e j)) -
            inner ℝ (S (S (e j))) (e i) • n := by rw [h1, h2]; abel
    have hnorm : ∀ i, ‖L j (e i)‖ ^ 2 = ‖R (L j (R (e i)))‖ ^ 2 -
        2 * (inner ℝ n (e i) * inner ℝ (R (L j (R (e i)))) (S (S (e j)))) +
        inner ℝ n (e i) ^ 2 * ‖S (S (e j))‖ ^ 2 + inner ℝ (S (S (e j))) (e i) ^ 2 := by
      intro i
      have hnY : inner ℝ n (R (L j (R (e i)))) = 0 := hnR _
      have hYn : inner ℝ (R (L j (R (e i)))) n = 0 := by rw [real_inner_comm]; exact hnY
      have hwn : inner ℝ (S (S (e j))) n = 0 := by rw [real_inner_comm]; exact hnw
      rw [hdec i]
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right, hYn, hnY, hwn, hnw, hnn,
        real_inner_comm (R (L j (R (e i)))) (S (S (e j)))]
      ring
    simp_rw [hnorm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.sum_mul]
    have hA : ∑ i, ‖R (L j (R (e i)))‖ ^ 2 =
        ∑ i, ∑ k, inner ℝ (L j (R (e i))) (R (e k)) ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hsq]
      exact Finset.sum_congr rfl fun k _ => by rw [hRsymm]
    have hB : ∑ i, inner ℝ n (e i) * inner ℝ (R (L j (R (e i)))) (S (S (e j))) = 0 := by
      have := hinclm (R.comp ((L j).comp R)) n (S (S (e j)))
      simp only [ContinuousLinearMap.comp_apply, hRn, map_zero, inner_zero_left] at this
      exact this
    have hC1 : ∑ i, inner ℝ n (e i) ^ 2 = 1 := by
      rw [hsq, hn]; norm_num
    rw [hA, hB, hC1, hsq]
    ring
  /- Step C (algebra): `Σᵢ ⟨S eᵢ, Λ eᵢ⟩ = −|S|⁴ − 2 Σᵢ |S² eᵢ|²` for `Λ` of the form below. -/
  have hstepCalg : ∀ (n : Euclid P) (S : Euclid P →L[ℝ] Euclid P), S n = 0 →
      (∀ w, inner ℝ n (S w) = 0) → (∀ u v, inner ℝ (S u) v = inner ℝ u (S v)) →
      ∀ (Λ : Euclid P → Euclid P) (κ : Euclid P → ℝ) (V : Euclid P),
      (∀ b, Λ b = κ b • n - (∑ i, ‖S (e i)‖ ^ 2) • S b - (2 : ℝ) • S (S (S b)) -
        inner ℝ n b • V) →
      ∑ i, inner ℝ (S (e i)) (Λ (e i)) =
        -(∑ i, ‖S (e i)‖ ^ 2) ^ 2 - 2 * ∑ i, ‖S (S (e i))‖ ^ 2 := by
    intro n S hSn hnS hSsymm Λ κ V hΛ
    have h1 : ∀ i, inner ℝ (S (e i)) n = 0 := fun i => by rw [real_inner_comm]; exact hnS _
    have h2 : ∀ i, inner ℝ (S (e i)) (S (S (S (e i)))) = ‖S (S (e i))‖ ^ 2 := fun i => by
      rw [← hSsymm, real_inner_self_eq_norm_sq]
    have h3 : ∑ i, inner ℝ n (e i) * inner ℝ (S (e i)) V = 0 := by
      rw [hinclm, hSn, inner_zero_left]
    simp_rw [hΛ, inner_sub_right, real_inner_smul_right, h1, h2, real_inner_self_eq_norm_sq]
    simp only [mul_zero, zero_sub, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rw [h3, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  /- The ambient projection field `Q(z) w = Π w − ⟨ν(z), w⟩ ν(z)`. -/
  refine Exists.elim (⟨_, rfl⟩ : ∃ Q : Euclid P → Euclid P →L[ℝ] Euclid P,
      Q = fun z => A₀.starProjection - (innerSL ℝ (ν z)).smulRight (ν z)) fun Q hQdef => ?_
  have hQ : ∀ z w, Q z w = A₀.starProjection w - inner ℝ (ν z) w • ν z := fun z w => by
    rw [hQdef]; simp
  have hQsymm : ∀ z u v, inner ℝ (Q z u) v = inner ℝ u (Q z v) := by
    intro z u v
    rw [hQ, hQ, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      Submodule.inner_starProjection_left_eq_right, real_inner_comm (ν z) u]
    ring
  -- where `ν ∈ A₀` is a unit vector, `Q` is the orthogonal projection onto `A₀ ∩ ν^⊥`
  have hQfacts : ∀ y, ν y ∈ A₀ → ‖ν y‖ = 1 →
      (∀ w, inner ℝ (ν y) (Q y w) = 0) ∧ (∀ w, Q y w ∈ A₀) ∧ Q y (ν y) = 0 ∧
        (∀ v ∈ A₀, inner ℝ (ν y) v = 0 → Q y v = v) ∧ (∀ w, Q y (Q y w) = Q y w) := by
    intro y hA h1
    have hPν : A₀.starProjection (ν y) = ν y := (Submodule.starProjection_eq_self_iff).2 hA
    have hνν : inner ℝ (ν y) (ν y) = 1 := by rw [real_inner_self_eq_norm_sq, h1]; norm_num
    have h1' : ∀ w, inner ℝ (ν y) (Q y w) = 0 := by
      intro w
      rw [hQ, inner_sub_right, real_inner_smul_right, hνν,
        ← Submodule.inner_starProjection_left_eq_right, hPν]
      ring
    have h2 : ∀ w, Q y w ∈ A₀ := fun w => by
      rw [hQ]; exact A₀.sub_mem (A₀.starProjection_apply_mem w) (A₀.smul_mem _ hA)
    have h4 : ∀ v ∈ A₀, inner ℝ (ν y) v = 0 → Q y v = v := by
      intro v hv hνv
      rw [hQ, hνv, zero_smul, sub_zero]
      exact (Submodule.starProjection_eq_self_iff).2 hv
    refine ⟨h1', h2, ?_, h4, fun w => h4 _ (h2 w) (h1' w)⟩
    rw [hQ, hPν, hνν, one_smul, sub_self]
  /- Smoothness on `O`. -/
  have hdiff : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euclid P → F},
      ContDiffOn ℝ (⊤ : ℕ∞) f O → ∀ {y : Euclid P}, y ∈ O → DifferentiableAt ℝ f y := by
    intro F _ _ f hf y hy
    exact (hf.contDiffAt (hOo.mem_nhds hy)).differentiableAt (by simp)
  have hcdf : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euclid P → F},
      ContDiffOn ℝ (⊤ : ℕ∞) f O → ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) O := by
    intro F _ _ f hf
    exact hf.fderiv_of_isOpen hOo (by simp)
  have hQb : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Q z b) O := by
    intro b
    have h : (fun z => Q z b) = fun z => A₀.starProjection b - inner ℝ (ν z) b • ν z :=
      funext fun z => hQ z b
    rw [h]
    exact contDiffOn_const.sub ((hνO.inner ℝ contDiffOn_const).smul hνO)
  have hQs : ContDiffOn ℝ (⊤ : ℕ∞) Q O := by
    rw [hQdef]
    exact contDiffOn_const.sub (((innerSL ℝ).contDiff.comp_contDiffOn hνO).smulRight hνO)
  /- Derivative formulas. -/
  have hfis : ∀ {W : Euclid P → Euclid P} {y : Euclid P}, DifferentiableAt ℝ ν y →
      DifferentiableAt ℝ W y → ∀ c u : Euclid P,
      fderiv ℝ (fun z => inner ℝ (ν z) c • W z) y u =
        inner ℝ (fderiv ℝ ν y u) c • W y + inner ℝ (ν y) c • fderiv ℝ W y u := by
    intro W y hνy hW c u
    rw [fderiv_fun_smul (hνy.inner ℝ (differentiableAt_const c)) hW, add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, fderiv_inner_apply ℝ hνy (differentiableAt_const c),
      fderiv_const_apply, zero_apply, inner_zero_right, zero_add, add_comm]
  have hfQ : ∀ {y : Euclid P}, DifferentiableAt ℝ ν y → ∀ b u : Euclid P,
      fderiv ℝ (fun z => Q z b) y u =
        -(inner ℝ (fderiv ℝ ν y u) b • ν y + inner ℝ (ν y) b • fderiv ℝ ν y u) := by
    intro y hd b u
    have h : (fun z => Q z b) = fun z => A₀.starProjection b - inner ℝ (ν z) b • ν z :=
      funext fun z => hQ z b
    rw [h, fderiv_const_sub, neg_apply, hfis hd hd]
  have hfac : ∀ {L : Euclid P → Euclid P →L[ℝ] Euclid P} {y : Euclid P},
      DifferentiableAt ℝ L y → ∀ b u : Euclid P,
      fderiv ℝ (fun z => L z b) y u = fderiv ℝ L y u b := by
    intro L y hL b u
    rw [fderiv_clm_apply hL (differentiableAt_const b)]
    simp
  have hfic : ∀ {G : Euclid P → Euclid P} {y : Euclid P}, DifferentiableAt ℝ G y →
      ∀ d u : Euclid P,
      fderiv ℝ (fun z => inner ℝ (G z) d) y u = inner ℝ (fderiv ℝ G y u) d := by
    intro G y hG d u
    rw [fderiv_inner_apply ℝ hG (differentiableAt_const d)]
    simp
  have hfns : ∀ {G : Euclid P → Euclid P} {y : Euclid P}, DifferentiableAt ℝ G y →
      ∀ u : Euclid P, fderiv ℝ (fun z => ‖G z‖ ^ 2) y u = 2 * inner ℝ (G y) (fderiv ℝ G y u) := by
    intro G y hG u
    rw [hG.hasFDerivAt.norm_sq.fderiv]
    simp
  -- derivative of `z ↦ Df(z) (Q(z) c)`
  have hftan : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euclid P → F},
      ContDiffOn ℝ (⊤ : ℕ∞) f O → ∀ {y : Euclid P}, y ∈ O → ∀ c u : Euclid P,
      fderiv ℝ (fun z => fderiv ℝ f z (Q z c)) y u =
        fderiv ℝ (fderiv ℝ f) y u (Q y c) -
          (inner ℝ (fderiv ℝ ν y u) c • fderiv ℝ f y (ν y) +
            inner ℝ (ν y) c • fderiv ℝ f y (fderiv ℝ ν y u)) := by
    intro F _ _ f hf y hy c u
    have hfd : DifferentiableAt ℝ (fderiv ℝ f) y := hdiff (hcdf hf) hy
    have hQd : DifferentiableAt ℝ (fun z => Q z c) y := hdiff (hQb c) hy
    rw [fderiv_clm_apply hfd hQd]
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      hfQ (hdiff hνO hy), map_neg, map_add, map_smul]
    abel
  -- commutation formula `δ_a δ_b f − δ_b δ_a f = ⟨ν, a⟩ Df(C b) − ⟨ν, b⟩ Df(C a)` where the
  -- Weingarten map `Dν ∘ Q` is self-adjoint (B.4)
  have hcomm : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Euclid P → F},
      ContDiffOn ℝ (⊤ : ℕ∞) f O → ∀ {y : Euclid P}, y ∈ O →
      (∀ a b, inner ℝ (fderiv ℝ ν y (Q y a)) b = inner ℝ (fderiv ℝ ν y (Q y b)) a) →
      ∀ a b : Euclid P,
      fderiv ℝ (fun z => fderiv ℝ f z (Q z b)) y (Q y a) -
          fderiv ℝ (fun z => fderiv ℝ f z (Q z a)) y (Q y b) =
        inner ℝ (ν y) a • fderiv ℝ f y (fderiv ℝ ν y (Q y b)) -
          inner ℝ (ν y) b • fderiv ℝ f y (fderiv ℝ ν y (Q y a)) := by
    intro F _ _ f hf y hy hS a b
    have hsymm : IsSymmSndFDerivAt ℝ f y := (hf.contDiffAt (hOo.mem_nhds hy)).isSymmSndFDerivAt
      (by simp [minSmoothness_of_isRCLikeNormedField])
    rw [hftan hf hy, hftan hf hy, hsymm (Q y a) (Q y b), hS a b]
    module
  /- On `M`, `Q` is the projection onto `span T_y M`, and tangential derivatives only see
  values on `M`. -/
  have hPQ : ∀ y ∈ M, (Submodule.span ℝ (tangentSpace M y)).starProjection = Q y :=
    fun y hy => ContinuousLinearMap.ext fun w => by rw [hQ]; exact (NC' y hy).2 w
  have hQT : ∀ y ∈ M, ∀ w, Q y w ∈ tangentSpace M y := fun y hy w => by
    rw [(NC' y hy).1]
    exact ⟨(hQfacts y (hν y hy).1 (hν y hy).2.1).2.1 w,
      (hQfacts y (hν y hy).1 (hν y hy).2.1).1 w⟩
  have hQspan : ∀ y ∈ M, ∀ w, Q y w ∈ Submodule.span ℝ (tangentSpace M y) := fun y hy w =>
    Submodule.subset_span (hQT y hy w)
  have hloc : ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (φ : Euclid P → F),
      (∀ z ∈ M, φ z = 0) → ∀ y ∈ M, DifferentiableAt ℝ φ y → ∀ w, fderiv ℝ φ y (Q y w) = 0 := by
    intro F _ _ φ hφ y hy hd w
    have h0 : HasFDerivWithinAt φ (0 : Euclid P →L[ℝ] F) M y :=
      (hasFDerivWithinAt_const (0 : F) y M).congr (fun z hz => hφ z hz) (hφ y hy)
    have h1 := Submission.codim1_hcp_sc_fderivWithin_tangent_eq P F M φ 0 y h0 (Q y w)
      (hQspan y hy w)
    have h2 := Submission.codim1_hcp_sc_fderivWithin_tangent_eq P F M φ (fderiv ℝ φ y) y
      hd.hasFDerivAt.hasFDerivWithinAt (Q y w) (hQspan y hy w)
    rw [h1] at h2
    simpa using h2.symm
  have heqOn : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ ψ : Euclid P → F},
      (∀ z ∈ M, φ z = ψ z) → ∀ {y : Euclid P}, y ∈ M → DifferentiableAt ℝ φ y →
      DifferentiableAt ℝ ψ y → ∀ w, fderiv ℝ φ y (Q y w) = fderiv ℝ ψ y (Q y w) := by
    intro F _ _ φ ψ h y hy hφ hψ w
    have h0 := hloc F (fun z => φ z - ψ z) (fun z hz => sub_eq_zero.2 (h z hz)) y hy
      (hφ.sub hψ) w
    rw [fderiv_fun_sub hφ hψ, sub_apply, sub_eq_zero] at h0
    exact h0
  /- The Weingarten map `Dν ∘ Q` maps into `T_y M` and is self-adjoint (B.4). -/
  have hW : ∀ y ∈ M, ∀ a,
      fderiv ℝ ν y (Q y a) ∈ A₀ ∧ inner ℝ (ν y) (fderiv ℝ ν y (Q y a)) = 0 :=
    fun y hy a => by
      have h := (WC' y hy (Q y a) (hQT y hy a) (Q y a) (hQT y hy a)).1
      rw [(NC' y hy).1] at h
      exact h
  have hS : ∀ y ∈ M, ∀ a b,
      inner ℝ (fderiv ℝ ν y (Q y a)) b = inner ℝ (fderiv ℝ ν y (Q y b)) a := by
    intro y hy a b
    have hq4 := (hQfacts y (hν y hy).1 (hν y hy).2.1).2.2.2.1
    have hfix : ∀ c u,
        inner ℝ (fderiv ℝ ν y (Q y c)) u = inner ℝ (fderiv ℝ ν y (Q y c)) (Q y u) :=
      fun c u => by rw [← hQsymm, hq4 _ (hW y hy c).1 (hW y hy c).2]
    rw [hfix a b, hfix b a]
    exact (WC' y hy (Q y a) (hQT y hy a) (Q y b) (hQT y hy b)).2.1
  /- The Weingarten field `C = Dν ∘ Q`. -/
  refine Exists.elim (⟨_, rfl⟩ : ∃ C : Euclid P → Euclid P →L[ℝ] Euclid P,
      C = fun z => (fderiv ℝ ν z).comp (Q z)) fun C hCdef => ?_
  have hC : ∀ z b, C z b = fderiv ℝ ν z (Q z b) := fun z b => by rw [hCdef]; rfl
  have hCs : ContDiffOn ℝ (⊤ : ℕ∞) C O := by
    rw [hCdef]
    exact (hcdf hνO).clm_comp hQs
  -- minimality: `H = Σⱼ ⟨C eⱼ, eⱼ⟩ = tr(P ∘ Dν) = 0` on `M`
  have hH : ∀ y ∈ M, ∑ j, inner ℝ (C y (e j)) (e j) = 0 := by
    intro y hy
    have h := htr y hy
    rw [LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ)] at h
    rw [← h, he]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [EuclideanSpace.basisFun_apply, LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, hPQ y hy]
    rw [hC, real_inner_comm]
  -- pointwise facts on `M`: `C(y)` maps into `T_y M`, kills `(T_y M)^⊥`, is self-adjoint
  have hpt : ∀ y ∈ M, (∀ b, Q y (C y b) = C y b) ∧ (∀ b, C y (Q y b) = C y b) ∧
      C y (ν y) = 0 ∧ (∀ b, inner ℝ (ν y) (C y b) = 0) ∧
      (∀ b, fderiv ℝ ν y (C y b) = C y (C y b)) ∧
      (∀ u v, inner ℝ (C y u) v = inner ℝ u (C y v)) := by
    intro y hy
    have hq3 := (hQfacts y (hν y hy).1 (hν y hy).2.1).2.2.1
    have hq4 := (hQfacts y (hν y hy).1 (hν y hy).2.1).2.2.2.1
    have hq5 := (hQfacts y (hν y hy).1 (hν y hy).2.1).2.2.2.2
    have p1 : ∀ b, Q y (C y b) = C y b := fun b => by
      rw [hC]; exact hq4 _ (hW y hy b).1 (hW y hy b).2
    refine ⟨p1, fun b => by rw [hC, hC, hq5], by rw [hC, hq3, map_zero],
      fun b => by rw [hC]; exact (hW y hy b).2, fun b => by rw [hC y (C y b), p1],
      fun u v => by rw [hC, hC, hS y hy, real_inner_comm]⟩
  /- Codazzi (B.5): `DC(y)(Q a) b − DC(y)(Q b) a = ⟨ν, a⟩ Dν(Dν(Q b)) − ⟨ν, b⟩ Dν(Dν(Q a))`. -/
  have hcod : ∀ y ∈ M, ∀ a b, fderiv ℝ C y (Q y a) b - fderiv ℝ C y (Q y b) a =
      inner ℝ (ν y) a • fderiv ℝ ν y (fderiv ℝ ν y (Q y b)) -
        inner ℝ (ν y) b • fderiv ℝ ν y (fderiv ℝ ν y (Q y a)) := by
    intro y hy a b
    have hCd : DifferentiableAt ℝ C y := hdiff hCs (hMO hy)
    rw [← hfac hCd, ← hfac hCd]
    simp only [hC]
    exact hcomm hνO (hMO hy) (hS y hy) a b
  /- Contracted Codazzi with `H = 0`: on `M`, `Σⱼ DC(y)(Q eⱼ) eⱼ = −|A|²(y) ν(y)`. -/
  have hZ : ∀ y ∈ M, ∑ j, fderiv ℝ C y (Q y (e j)) (e j) = -(∑ i, ‖C y (e i)‖ ^ 2) • ν y := by
    intro y hy
    have hCd : DifferentiableAt ℝ C y := hdiff hCs (hMO hy)
    have p4 := (hpt y hy).2.2.2.1
    have p5 := (hpt y hy).2.2.2.2.1
    have p6 := (hpt y hy).2.2.2.2.2
    have hdi : ∀ c c', DifferentiableAt ℝ (fun z => inner ℝ (C z c) c') y := fun c c' =>
      (hCd.clm_apply (differentiableAt_const c)).inner ℝ (differentiableAt_const c')
    have hfi : ∀ c c' u,
        fderiv ℝ (fun z => inner ℝ (C z c) c') y u = inner ℝ (fderiv ℝ C y u c) c' :=
      fun c c' u => by rw [hfic (hCd.clm_apply (differentiableAt_const c)), hfac hCd]
    -- swap the two slots: `C` is self-adjoint on `M`
    have hswap : ∀ j d, inner ℝ (fderiv ℝ C y (Q y (e j)) (e j)) d =
        inner ℝ (fderiv ℝ C y (Q y (e j)) d) (e j) := by
      intro j d
      rw [← hfi, ← hfi]
      refine heqOn (fun z hz => ?_) hy (hdi _ _) (hdi _ _) (e j)
      rw [(hpt z hz).2.2.2.2.2, real_inner_comm]
    -- `H` vanishes on `M`, hence so do its tangential derivatives
    have hHd : ∀ d, ∑ j, inner ℝ (fderiv ℝ C y (Q y d) (e j)) (e j) = 0 := by
      intro d
      have h0 := hloc ℝ (fun z => ∑ j, inner ℝ (C z (e j)) (e j)) hH y hy
        (DifferentiableAt.fun_sum fun j _ => hdi _ _) d
      rw [fderiv_fun_sum fun j _ => hdi _ _, sum_apply] at h0
      simpa only [hfi] using h0
    refine ext_inner_right ℝ fun d => ?_
    rw [sum_inner, real_inner_smul_left]
    simp_rw [hswap]
    have hcod' : ∀ j, fderiv ℝ C y (Q y (e j)) d = fderiv ℝ C y (Q y d) (e j) +
        (inner ℝ (ν y) (e j) • fderiv ℝ ν y (fderiv ℝ ν y (Q y d)) -
          inner ℝ (ν y) d • fderiv ℝ ν y (fderiv ℝ ν y (Q y (e j)))) := fun j => by
      rw [← hcod y hy (e j) d]
      abel
    simp_rw [hcod', inner_add_left, inner_sub_left, real_inner_smul_left]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hHd d]
    have hNN : ∀ c, fderiv ℝ ν y (fderiv ℝ ν y (Q y c)) = C y (C y c) := fun c => by
      rw [← hC, p5]
    simp_rw [hNN]
    have h2 : ∑ j, inner ℝ (ν y) (e j) * inner ℝ (C y (C y d)) (e j) = 0 := by rw [hpar, p4]
    have h3 : ∑ j, inner ℝ (ν y) d * inner ℝ (C y (C y (e j))) (e j) =
        inner ℝ (ν y) d * ∑ i, ‖C y (e i)‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [p6, real_inner_self_eq_norm_sq]
    rw [h2, h3]
    ring
  /- From here on we work at the point `x`. -/
  have hCdx : DifferentiableAt ℝ C x := hdiff hCs hxO
  have hνdx : DifferentiableAt ℝ ν x := hdiff hνO hxO
  have hDs : ∀ c, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ C z (Q z c)) O := fun c =>
    (hcdf hCs).clm_apply (hQb c)
  have hDd : ∀ c, DifferentiableAt ℝ (fun z => fderiv ℝ C z (Q z c)) x := fun c =>
    hdiff (hDs c) hxO
  have hgs : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ∑ i, ‖C z (e i)‖ ^ 2) O :=
    ContDiffOn.sum fun i _ => (hCs.clm_apply contDiffOn_const).norm_sq ℝ
  have p1 := (hpt x hx).1
  have p2 := (hpt x hx).2.1
  have p3 := (hpt x hx).2.2.1
  have p4 := (hpt x hx).2.2.2.1
  have p5 := (hpt x hx).2.2.2.2.1
  have p6 := (hpt x hx).2.2.2.2.2
  have hq1 := (hQfacts x (hν x hx).1 (hν x hx).2.1).1
  have hq3 := (hQfacts x (hν x hx).1 (hν x hx).2.1).2.2.1
  -- `L = DC(x)(Q a)` satisfies `L b − L (Q b) = −⟨ν, b⟩ C² a`
  have hLin : ∀ a b, fderiv ℝ C x (Q x a) b - fderiv ℝ C x (Q x a) (Q x b) =
      -(inner ℝ (ν x) b • C x (C x a)) := by
    intro a b
    have hQd : DifferentiableAt ℝ (fun z => Q z b) x := hdiff (hQb b) hxO
    have hd1 : DifferentiableAt ℝ (fun z => C z b) x :=
      hCdx.clm_apply (differentiableAt_const b)
    have hd2 : DifferentiableAt ℝ (fun z => C z (Q z b)) x := hCdx.clm_apply hQd
    -- `C(z) b − C(z) (Q(z) b)` vanishes on `M`
    have h0 := hloc (Euclid P) (fun z => C z b - C z (Q z b))
      (fun z hz => by rw [(hpt z hz).2.1 b, sub_self]) x hx (hd1.sub hd2) a
    simp only [fderiv_fun_sub hd1 hd2, sub_apply, hfac hCdx, fderiv_clm_apply hCdx hQd,
      add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      hfQ hνdx, ← hC x a, map_neg, map_add, map_smul, p3, smul_zero, zero_add] at h0
    rw [sub_eq_zero] at h0
    rw [h0]
    abel
  -- `L = DC(x)(Q a)` satisfies `L b − Q (L b) = −⟨C a, C b⟩ ν`
  have hLout : ∀ a b, fderiv ℝ C x (Q x a) b - Q x (fderiv ℝ C x (Q x a) b) =
      -(inner ℝ (C x a) (C x b) • ν x) := by
    intro a b
    have hQd : DifferentiableAt ℝ Q x := hdiff hQs hxO
    have hd1 : DifferentiableAt ℝ (fun z => C z b) x :=
      hCdx.clm_apply (differentiableAt_const b)
    have hd2 : DifferentiableAt ℝ (fun z => Q z (C z b)) x := hQd.clm_apply hd1
    -- `C(z) b − Q(z) (C(z) b)` vanishes on `M`
    have h0 := hloc (Euclid P) (fun z => C z b - Q z (C z b))
      (fun z hz => by rw [(hpt z hz).1 b, sub_self]) x hx (hd1.sub hd2) a
    simp only [fderiv_fun_sub hd1 hd2, sub_apply, hfac hCdx, fderiv_clm_apply hQd hd1,
      add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, ← hfac hQd,
      hfQ hνdx, ← hC x a, p4, zero_smul, add_zero] at h0
    rw [sub_eq_zero] at h0
    exact sub_eq_iff_eq_add'.2 h0
  /- Step A (product rule): `Σⱼ δⱼ δⱼ |C|² = Σⱼ Σᵢ 2 (⟨C eᵢ, δⱼ δⱼ C eᵢ⟩ + |δⱼ C eᵢ|²)`. -/
  have hstepA : ∑ j, fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) y
        (Q y (e j))) x (Q x (e j)) =
      ∑ j, ∑ i, 2 * (inner ℝ (C x (e i))
        (fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) (e i)) +
        ‖fderiv ℝ C x (Q x (e j)) (e i)‖ ^ 2) := by
    have hCd : ∀ y ∈ O, DifferentiableAt ℝ C y := fun y hy => hdiff hCs hy
    have hCb : ∀ (b : Euclid P), ∀ y ∈ O, DifferentiableAt ℝ (fun z => C z b) y :=
      fun b y hy => (hCd y hy).clm_apply (differentiableAt_const b)
    refine Finset.sum_congr rfl fun j _ => ?_
    -- the first tangential derivative of `|C|²` near `x`
    have h1 : (fun y => fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) y (Q y (e j))) =ᶠ[𝓝 x]
        fun y => ∑ i, 2 * inner ℝ (C y (e i)) (fderiv ℝ C y (Q y (e j)) (e i)) := by
      filter_upwards [hOo.mem_nhds hxO] with y hy
      rw [fderiv_fun_sum fun i _ => ((hCb (e i) y hy).norm_sq ℝ), sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hfns (hCb (e i) y hy), hfac (hCd y hy)]
    rw [h1.fderiv_eq]
    have hd2 : ∀ i, DifferentiableAt ℝ (fun y => fderiv ℝ C y (Q y (e j)) (e i)) x :=
      fun i => (hDd (e j)).clm_apply (differentiableAt_const _)
    rw [fderiv_fun_sum fun i _ => ((hCb (e i) x hxO).inner ℝ (hd2 i)).const_mul 2, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [fderiv_const_mul ((hCb (e i) x hxO).inner ℝ (hd2 i)), smul_apply,
      fderiv_inner_apply ℝ (hCb (e i) x hxO) (hd2 i), hfac (hDd (e j)), hfac (hCd x hxO),
      real_inner_self_eq_norm_sq, smul_eq_mul]
  /- Step C (calculus): `Σⱼ δⱼ δⱼ C(x) b = κ(b) ν − |A|² C b − 2 C³ b − ⟨ν, b⟩ V`, by Codazzi
  on `M`, the commutation formula for `C` (in place of B.6–B.7) and
  `Σⱼ δⱼ C eⱼ = −|A|² ν`. -/
  have hstepC : ∃ (κ : Euclid P → ℝ) (V : Euclid P), ∀ b,
      ∑ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) b =
        κ b • ν x - (∑ i, ‖C x (e i)‖ ^ 2) • C x b - (2 : ℝ) • C x (C x (C x b)) -
          inner ℝ (ν x) b • V := by
    have hWs : ∀ c, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z c))) O := fun c =>
      (hcdf hνO).clm_apply ((hcdf hνO).clm_apply (hQb c))
    have hWd : ∀ c, DifferentiableAt ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z c))) x :=
      fun c => hdiff (hWs c) hxO
    have hDdb : ∀ c c', DifferentiableAt ℝ (fun z => fderiv ℝ C z (Q z c) c') x := fun c c' =>
      (hDd c).clm_apply (differentiableAt_const c')
    have hWdi : ∀ c c', DifferentiableAt ℝ
        (fun z => inner ℝ (ν z) c • fderiv ℝ ν z (fderiv ℝ ν z (Q z c'))) x := fun c c' =>
      (hνdx.inner ℝ (differentiableAt_const c)).smul (hWd c')
    refine ⟨fun b => -fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) x (Q x b),
      ∑ j, (fderiv ℝ C x (fderiv ℝ ν x (Q x (e j))) (e j) +
        fderiv ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z (e j)))) x (Q x (e j))),
      fun b => ?_⟩
    -- per-`j` expansion: Codazzi on `M`, then the commutation formula for `C`
    have hj : ∀ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) b =
        fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x b) (e j) +
          inner ℝ (ν x) (e j) • fderiv ℝ C x (fderiv ℝ ν x (Q x b)) (e j) -
          inner ℝ (ν x) b • fderiv ℝ C x (fderiv ℝ ν x (Q x (e j))) (e j) +
          ((inner ℝ (fderiv ℝ ν x (Q x (e j))) (e j) • fderiv ℝ ν x (fderiv ℝ ν x (Q x b)) +
              inner ℝ (ν x) (e j) • fderiv ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z b))) x
                (Q x (e j))) -
            (inner ℝ (fderiv ℝ ν x (Q x (e j))) b • fderiv ℝ ν x (fderiv ℝ ν x (Q x (e j))) +
              inner ℝ (ν x) b • fderiv ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z (e j)))) x
                (Q x (e j)))) := by
      intro j
      have heq := heqOn
        (φ := fun z => fderiv ℝ C z (Q z (e j)) b)
        (ψ := fun z => fderiv ℝ C z (Q z b) (e j) +
          (inner ℝ (ν z) (e j) • fderiv ℝ ν z (fderiv ℝ ν z (Q z b)) -
            inner ℝ (ν z) b • fderiv ℝ ν z (fderiv ℝ ν z (Q z (e j)))))
        (fun z hz => by
          rw [← hcod z hz (e j) b]
          abel)
        hx (hDdb (e j) b) ((hDdb b (e j)).fun_add ((hWdi (e j) b).fun_sub (hWdi b (e j)))) (e j)
      have hcm := congrArg (fun T => T (e j)) (hcomm hCs hxO (hS x hx) (e j) b)
      simp only [sub_apply, smul_apply] at hcm
      rw [sub_eq_iff_eq_add'] at hcm
      rw [← hfac (hDd (e j)) b (Q x (e j)), heq]
      simp only [fderiv_fun_add (hDdb b (e j)) ((hWdi (e j) b).fun_sub (hWdi b (e j))),
        add_apply, fderiv_fun_sub (hWdi (e j) b) (hWdi b (e j)), sub_apply, hfac (hDd b),
        hfis hνdx (hWd b), hfis hνdx (hWd (e j)), hcm]
      abel
    simp_rw [hj]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- (i) the contracted term, by `Σⱼ DC(Q eⱼ) eⱼ = −|A|² ν` on `M`
    have hZd : DifferentiableAt ℝ (fun z => ∑ j, fderiv ℝ C z (Q z (e j)) (e j)) x :=
      DifferentiableAt.fun_sum fun j _ => hDdb (e j) (e j)
    have hgd : DifferentiableAt ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) x := hdiff hgs hxO
    have hS1 : ∑ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x b) (e j) =
        -(fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) x (Q x b) • ν x) -
          (∑ i, ‖C x (e i)‖ ^ 2) • C x b := by
      have h1 : ∑ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x b) (e j) =
          fderiv ℝ (fun z => ∑ j, fderiv ℝ C z (Q z (e j)) (e j)) x (Q x b) := by
        rw [fderiv_fun_sum fun j _ => hDdb (e j) (e j), sum_apply]
        exact Finset.sum_congr rfl fun j _ => (hfac (hDd (e j)) _ _).symm
      simp only [h1, heqOn (ψ := fun z => -((∑ i, ‖C z (e i)‖ ^ 2) • ν z))
        (fun z hz => by rw [hZ z hz, neg_smul]) hx hZd (hgd.fun_smul hνdx).fun_neg b,
        fderiv_fun_neg, neg_apply, fderiv_fun_smul hgd hνdx, add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, ← hC x b]
      module
    -- (ii) `Σⱼ ⟨ν, eⱼ⟩ DC(C b) eⱼ = DC(C b) ν = −C³ b`
    have hS2 : ∑ j, inner ℝ (ν x) (e j) • fderiv ℝ C x (fderiv ℝ ν x (Q x b)) (e j) =
        -C x (C x (C x b)) := by
      rw [hsmclm, ← hC x b]
      have h := hLin (C x b) (ν x)
      simp only [p1, hq3, map_zero, sub_zero, real_inner_self_eq_norm_sq, (hν x hx).2.1, one_pow,
        one_smul] at h
      exact h
    -- (iii) the mean curvature term vanishes
    have hS4 : ∑ j, inner ℝ (fderiv ℝ ν x (Q x (e j))) (e j) •
        fderiv ℝ ν x (fderiv ℝ ν x (Q x b)) = 0 := by
      have h := hH x hx
      simp only [hC] at h
      rw [← Finset.sum_smul, h, zero_smul]
    -- (iv) `Σⱼ ⟨ν, eⱼ⟩ DW(Q eⱼ) = DW(Q ν) = 0`
    have hS5 : ∑ j, inner ℝ (ν x) (e j) •
        fderiv ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z b))) x (Q x (e j)) = 0 := by
      have := hsmclm
        ((fderiv ℝ (fun z => fderiv ℝ ν z (fderiv ℝ ν z (Q z b))) x).comp (Q x)) (ν x)
      simp only [ContinuousLinearMap.comp_apply, hq3, map_zero] at this
      exact this
    -- (v) `Σⱼ ⟨C eⱼ, b⟩ C² eⱼ = C³ b`
    have hS6 : ∑ j, inner ℝ (fderiv ℝ ν x (Q x (e j))) b •
        fderiv ℝ ν x (fderiv ℝ ν x (Q x (e j))) = C x (C x (C x b)) := by
      have := hsmclm ((C x).comp (C x)) (C x b)
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hC x (e j), p5, p6, real_inner_comm]
    simp only [hS1, hS2, hS4, hS5, hS6, ← Finset.smul_sum]
    module
  /- Simons' identity in ambient form (B.8 with `H = 0`). -/
  have hcore : ∑ j, fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) y (Q y (e j))) x
        (Q x (e j)) =
      2 * ∑ i, ∑ j, ∑ k, inner ℝ (fderiv ℝ C x (Q x (e k)) (Q x (e i))) (Q x (e j)) ^ 2 -
        2 * (∑ i, ‖C x (e i)‖ ^ 2) ^ 2 := by
    rw [hstepA]
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    obtain ⟨κ, V, hΛ⟩ := hstepC
    have hCalg := hstepCalg (ν x) (C x) p3 p4 p6
      (fun b => ∑ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) b) κ V hΛ
    have hBalg := hstepB (ν x) (C x) (Q x) (fun j => fderiv ℝ C x (Q x (e j))) (hν x hx).2.1
      hq3 hq1 p4 (hQsymm x) p2 p6 (fun j b => hLin (e j) b) (fun j b => hLout (e j) b)
    have hA' : ∑ j, ∑ i, inner ℝ (C x (e i))
          (fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) (e i)) =
        ∑ i, inner ℝ (C x (e i))
          (∑ j, fderiv ℝ (fun z => fderiv ℝ C z (Q z (e j))) x (Q x (e j)) (e i)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => (inner_sum _ _ _).symm
    have hN : ∑ i, ∑ j, ∑ k, inner ℝ (fderiv ℝ C x (Q x (e k)) (Q x (e i))) (Q x (e j)) ^ 2 =
        ∑ j, ∑ i, ∑ k, inner ℝ (fderiv ℝ C x (Q x (e j)) (Q x (e i))) (Q x (e k)) ^ 2 := by
      calc ∑ i, ∑ j, ∑ k, inner ℝ (fderiv ℝ C x (Q x (e k)) (Q x (e i))) (Q x (e j)) ^ 2 =
            ∑ i, ∑ k, ∑ j, inner ℝ (fderiv ℝ C x (Q x (e k)) (Q x (e i))) (Q x (e j)) ^ 2 :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    rw [hA', hCalg, hBalg, hN]
    ring
  /- Identify the frozen (within-`M`) quantities with the ambient ones. -/
  have hg : ∀ z ∈ M, (∑ i, ‖fderiv ℝ ν z
      ((Submodule.span ℝ (tangentSpace M z)).starProjection (e i))‖ ^ 2) =
      ∑ i, ‖C z (e i)‖ ^ 2 := fun z hz => by
    simp only [hPQ z hz, hC]
  have hinner : ∀ (j : Fin P), ∀ y ∈ M,
      fderivWithin ℝ (fun z => ∑ i, ‖fderiv ℝ ν z
        ((Submodule.span ℝ (tangentSpace M z)).starProjection (e i))‖ ^ 2) M
        y ((Submodule.span ℝ (tangentSpace M y)).starProjection (e j)) =
      fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) y (Q y (e j)) := by
    intro j y hy
    rw [hPQ y hy]
    exact Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ y
      ((hdiff hgs (hMO hy)).hasFDerivAt.hasFDerivWithinAt.congr hg (hg y hy)) _
      (hQspan y hy (e j))
  have hLHS : ∀ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ (fun z => ∑ i,
        ‖fderiv ℝ ν z ((Submodule.span ℝ (tangentSpace M z)).starProjection (e i))‖ ^ 2) M y
        ((Submodule.span ℝ (tangentSpace M y)).starProjection (e j))) M x (Q x (e j)) =
      fderiv ℝ (fun y => fderiv ℝ (fun z => ∑ i, ‖C z (e i)‖ ^ 2) y (Q y (e j))) x
        (Q x (e j)) := fun j =>
    Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x
      ((hdiff ((hcdf hgs).clm_apply (hQb (e j))) hxO).hasFDerivAt.hasFDerivWithinAt.congr
        (hinner j) (hinner j x hx)) _ (hQspan x hx (e j))
  have hRHS : ∀ k : Fin P, fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp
      (Submodule.span ℝ (tangentSpace M y)).starProjection) M x (Q x (e k)) =
      fderiv ℝ C x (Q x (e k)) := fun k =>
    Submission.codim1_hcp_sc_fderivWithin_tangent_eq P (Euclid P →L[ℝ] Euclid P) M _ _ x
      (hCdx.hasFDerivAt.hasFDerivWithinAt.congr (fun y hy => by rw [hPQ y hy, hCdef])
        (by rw [hPQ x hx, hCdef])) _ (hQspan x hx (e k))
  have he1 : ∀ i, (EuclideanSpace.single i 1 : Euclid P) = e i := fun i => by rw [he]
  simp only [he1, hPQ x hx]
  simp only [hLHS, hRHS, ← hC]
  exact hcore
/-- **Simon, Appendix B, Lemma B.11 (p. 232)**: for a cone `M ⊆ A₀ ≅ ℝ^{m+1}` (`0 ∉ M`, not
necessarily minimal) with smooth unit normal `ν`, at every `x ∈ M` with `|A|²(x) > 0`,
`2|A|⁴/|x|² + |∇|A|²|²/4 ≤ |A|²|∇A|²`, i.e. `D ≥ 2|x|⁻²|A|²` for the defect `D` of B.10.
`W = span T_xM` equals `T_xM` (`normal_complement`) and contains `x` (`cone_normal`); take an
orthonormal basis `τ` of `W` with radial last vector `x/|x|`.  On `M`, `C(y) = Dν(y) ∘ p_{T_yM}`
agrees with the smooth `C̃(y) = Dν(y) ∘ (p_{A₀} − ν(y) ⊗ ν(y))`, so `C` has a derivative `C'`
within `M` at `x`, and `D_M C(x) = C'` on `T_xM` (`tangent_fderiv`).  Instead of Simon's frame
constant along the ray, `C(tx) = t⁻¹C(x)` (`cone_normal`) and the curve `s ↦ (1 + s)x` give
`C'x = −C(x)`, which is Simon's (2); `Dν(x)x = 0` is his (1).  The chain rule gives
`D_M|A|²(x)τ = 2 Σᵢ ⟨C(x)eᵢ, (D_τ C)eᵢ⟩`.  With `h_ad = ⟨Dν(x)τₐ, τ_d⟩` and
`dh_cad = ⟨(D_{τ_c}C)τₐ, τ_d⟩`, the Hilbert–Schmidt identities give `|A|² = Σ h²`,
`|∇A|² = Σ dh²` and `|∇|A|²|² = 4 Σ_c (Σ_{a,d} h_ad dh_cad)²`.  By (1), (2) and the Codazzi
symmetries (`codazzi`), `h` vanishes in the radial row and column and
`dh_{c n d} = dh_{c d n} = −|x|⁻¹ h_cd`.  So for each `c` the radial entries of `dh_c` contribute
`2|x|⁻² Σ_d h_cd²` to `Σ dh_c²`, while Cauchy–Schwarz on the tangential block gives
`(Σ h dh_c)² ≤ |A|² Σ_{a,d<n} dh_cad²`; summing over `c` gives the estimate. -/
theorem Submission.codim1_hcp_sc_cone_simons_defect : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ∀ x ∈ M, 0 < (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) → 2 * (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) ^ 2 / ‖x‖ ^ 2 + (∑ k : Fin P, (fderivWithin ℝ (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1))) ^ 2) / 4 ≤ (∑ i : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))‖ ^ 2) * (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P, (inner ℝ (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single k 1)) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1))) ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) := by
  intro P m A₀ M ν hdim hMA h0 hM hcone hO hν x hx _
  -- the sibling facts: `normal_complement`, `cone_normal` and `codazzi` at `x`
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hdim hMA (hM 1) hν
  obtain ⟨hxT, hDx, hray⟩ :=
    Submission.codim1_hcp_sc_cone_normal_homogeneous P m A₀ M ν hdim hMA (hM 1) hcone hO hν x hx
  have hCZ := Submission.codim1_hcp_sc_weingarten_codazzi P m A₀ M ν hdim hMA hM hO hν x hx
  obtain ⟨O, hOopen, hMO, hνO⟩ := hO
  -- `span T_xM = T_xM`, since `T_xM = A₀ ∩ ν(x)^⊥` is a subspace
  have hWT : ∀ v ∈ Submodule.span ℝ (tangentSpace M x), v ∈ tangentSpace M x := by
    intro v hv
    have hT := (hNC x hx).1
    induction hv using Submodule.span_induction with
    | mem v hv => exact hv
    | zero => rw [hT]; exact ⟨A₀.zero_mem, inner_zero_right _⟩
    | add u w _ _ hu hw =>
      rw [hT] at hu hw ⊢
      exact ⟨A₀.add_mem hu.1 hw.1, by rw [inner_add_right, hu.2, hw.2, add_zero]⟩
    | smul c u _ hu =>
      rw [hT] at hu ⊢
      exact ⟨A₀.smul_mem c hu.1, by rw [inner_smul_right, hu.2, mul_zero]⟩
  -- an orthonormal basis `τ` of `span T_xM` whose last vector is `x/|x|`
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  have hρ : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hxW : x ∈ Submodule.span ℝ (tangentSpace M x) := Submodule.subset_span hxT
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℝ (Submodule.span ℝ (tangentSpace M x)) = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨x, hxW⟩, fun h => hx0 (congrArg Subtype.val h)⟩).ne'
  have hxhat : ‖(⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hxW⟩ :
      Submodule.span ℝ (tangentSpace M x))‖ = 1 := by
    show ‖‖x‖⁻¹ • x‖ = 1
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρ.ne']
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
    (ι := Fin (n + 1)) (by rw [hn, Fintype.card_fin])
    (v := fun _ => (⟨‖x‖⁻¹ • x, Submodule.smul_mem _ _ hxW⟩ :
      Submodule.span ℝ (tangentSpace M x))) (s := {Fin.last n})
    ⟨fun _ => hxhat, fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  have hlast : (b (Fin.last n) : Euclid P) = ‖x‖⁻¹ • x := by
    rw [hb _ (Set.mem_singleton _)]
  have hbT : ∀ a, (b a : Euclid P) ∈ tangentSpace M x := fun a => hWT _ (b a).2
  -- `C = C̃` on `M` with `C̃(y) = Dν(y) ∘ (p_{A₀} − ν(y) ⊗ ν(y))` smooth near `x`
  have hνx : ContDiffAt ℝ (⊤ : ℕ∞) ν x := hνO.contDiffAt (hOopen.mem_nhds (hMO hx))
  have hν1 : ContDiffAt ℝ 1 ν x := hνx.of_le (WithTop.coe_le_coe.2 le_top)
  have hDν1 : ContDiffAt ℝ 1 (fderiv ℝ ν) x := hνx.fderiv_right (WithTop.coe_le_coe.2 le_top)
  have hinner : ContDiffAt ℝ 1 (fun y => innerSL ℝ (ν y)) x :=
    ((innerSL ℝ : Euclid P →L[ℝ] Euclid P →L[ℝ] ℝ).contDiff.contDiffAt).comp x hν1
  have hCt : ContDiffAt ℝ 1 (fun y => (fderiv ℝ ν y).comp
      (A₀.starProjection - (innerSL ℝ (ν y)).smulRight (ν y))) x :=
    hDν1.clm_comp (contDiffAt_const.sub (hinner.smulRight hν1))
  have hCeq : ∀ y ∈ M, (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection =
      (fderiv ℝ ν y).comp (A₀.starProjection - (innerSL ℝ (ν y)).smulRight (ν y)) := by
    intro y hy
    ext1 w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, (hNC y hy).2 w,
      sub_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  obtain ⟨C', hC'⟩ : ∃ C', HasFDerivWithinAt
      (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) C' M x :=
    ⟨_, (hCt.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt.congr hCeq (hCeq x hx)⟩
  -- `D_M C(x) = C'` on `span T_xM` (`tangent_fderiv`)
  have hΦW : ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderivWithin ℝ
      (fun y => (fderiv ℝ ν y).comp (Submodule.span ℝ (tangentSpace M y)).starProjection) M x v =
        C' v := fun v hv =>
    Submission.codim1_hcp_sc_fderivWithin_tangent_eq P _ M _ C' x hC' v hv
  -- homogeneity `C(tx) = t⁻¹C(x)` for `t > 0`
  have hhom : ∀ t : ℝ, 0 < t → (fderiv ℝ ν (t • x)).comp
      (Submodule.span ℝ (tangentSpace M (t • x))).starProjection =
        t⁻¹ • (fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection := by
    intro t ht
    obtain ⟨hTt, -, hDt⟩ := hray t ht
    ext1 w
    rw [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hTt,
      ← hDt _ (hWT _ (Submodule.starProjection_apply_mem _ w)), smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul]
  -- the radial derivative `C'x = −C(x)`, along the curve `s ↦ (1 + s)x` in `M`
  have hrad : C' x =
      -((fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection) := by
    have hγ : HasDerivAt (fun s : ℝ => (1 + s) • x) x 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).smul_const x
    have hmaps : MapsTo (fun s : ℝ => (1 + s) • x) (Ioo (-1) 1) M :=
      fun s hs => hcone (1 + s) (by linarith [hs.1]) x hx
    have h1 := hC'.comp_hasDerivWithinAt_of_eq (0 : ℝ) hγ.hasDerivWithinAt hmaps (by simp)
    have h2 := h1.hasDerivAt (Ioo_mem_nhds (by norm_num) (by norm_num))
    have h3 : HasDerivAt (fun s : ℝ => (1 + s)⁻¹ •
        (fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection)
        (-((fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).const_add 1).inv (by simp)).smul_const
        ((fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection)
    refine h2.unique (h3.congr_of_eventuallyEq ?_)
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
      with s hs
    exact hhom (1 + s) (by linarith [hs.1])
  -- `D_M|A|²(x)τ = 2 Σᵢ ⟨C(x)eᵢ, (D_τ C)eᵢ⟩` for `τ ∈ T_xM` (chain rule, `tangent_fderiv`)
  have hSd : HasFDerivWithinAt (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z
      ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2)
      (∑ i : Fin P, 2 • (innerSL ℝ (fderiv ℝ ν x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1)))).comp
        ((ContinuousLinearMap.apply ℝ (Euclid P) (EuclideanSpace.single i (1 : ℝ))).comp C'))
      M x :=
    HasFDerivWithinAt.fun_sum fun i _ =>
      ((ContinuousLinearMap.apply ℝ (Euclid P)
        (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp_hasFDerivWithinAt x hC').norm_sq
  have hg : ∀ c, fderivWithin ℝ (fun z => ∑ i : Fin P, ‖fderiv ℝ ν z
      ((Submodule.span ℝ (tangentSpace M z)).starProjection (EuclideanSpace.single i 1))‖ ^ 2)
      M x (b c : Euclid P) = 2 * ∑ i : Fin P, inner ℝ (fderiv ℝ ν x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single i 1)))
        (fderivWithin ℝ (fun y => (fderiv ℝ ν y).comp
          (Submodule.span ℝ (tangentSpace M y)).starProjection) M x (b c : Euclid P)
          (EuclideanSpace.single i 1)) := by
    intro c
    rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hSd _ (b c).2,
      hΦW _ (b c).2, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply, nsmul_eq_mul, Nat.cast_ofNat]
  -- the algebra of B.11 in an orthonormal frame `τ` of `W` with radial last vector
  have frame : ∀ (W : Submodule ℝ (Euclid P)) (τ : OrthonormalBasis (Fin (n + 1)) ℝ W)
      (D : Euclid P →L[ℝ] Euclid P) (Φ : Euclid P →L[ℝ] Euclid P →L[ℝ] Euclid P)
      (g : Euclid P →L[ℝ] ℝ) (ρ : ℝ), (∀ a, D (τ a : Euclid P) ∈ W) →
      (∀ a c, inner ℝ (D (τ a : Euclid P)) (τ c : Euclid P) =
        inner ℝ (D (τ c : Euclid P)) (τ a : Euclid P)) →
      D (τ (Fin.last n) : Euclid P) = 0 →
      (∀ a c d, inner ℝ (Φ (τ a : Euclid P) (τ c : Euclid P)) (τ d : Euclid P) =
        inner ℝ (Φ (τ c : Euclid P) (τ a : Euclid P)) (τ d : Euclid P)) →
      (∀ a c d, inner ℝ (Φ (τ a : Euclid P) (τ c : Euclid P)) (τ d : Euclid P) =
        inner ℝ (Φ (τ a : Euclid P) (τ d : Euclid P)) (τ c : Euclid P)) →
      Φ (τ (Fin.last n) : Euclid P) = -(ρ⁻¹ • D.comp W.starProjection) →
      (∀ c, g (τ c : Euclid P) = 2 * ∑ i : Fin P,
        inner ℝ (D (W.starProjection (EuclideanSpace.single i 1)))
          (Φ (τ c : Euclid P) (EuclideanSpace.single i 1))) →
      2 * (∑ i : Fin P, ‖D (W.starProjection (EuclideanSpace.single i 1))‖ ^ 2) ^ 2 / ρ ^ 2 +
          (∑ k : Fin P, g (W.starProjection (EuclideanSpace.single k 1)) ^ 2) / 4 ≤
        (∑ i : Fin P, ‖D (W.starProjection (EuclideanSpace.single i 1))‖ ^ 2) *
          (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P,
            inner ℝ (Φ (W.starProjection (EuclideanSpace.single k 1))
              (W.starProjection (EuclideanSpace.single i 1)))
              (W.starProjection (EuclideanSpace.single j 1)) ^ 2) := by
    intro W τ D Φ g ρ hDW hDsym hDlast hΦsym₁ hΦsym₂ hΦlast hg
    -- `p_W v = Σₐ ⟨τₐ, v⟩ τₐ`
    have hproj : ∀ v : Euclid P,
        W.starProjection v = ∑ a, inner ℝ (τ a : Euclid P) v • (τ a : Euclid P) := by
      intro v
      rw [τ.starProjection_eq_sum_rankOne, sum_apply]
      simp only [InnerProductSpace.rankOne_apply]
    -- trace identity: `Σᵢ ⟨A(p_W eᵢ), B eᵢ⟩ = Σₐ ⟨A τₐ, B τₐ⟩`
    have htrace : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        (A B : Euclid P →L[ℝ] F),
        ∑ i : Fin P, inner ℝ (A (W.starProjection (EuclideanSpace.single i 1)))
            (B (EuclideanSpace.single i 1)) =
          ∑ a, inner ℝ (A (τ a : Euclid P)) (B (τ a : Euclid P)) := by
      intro F _ _ A B
      -- `τₐ = Σᵢ ⟨τₐ, eᵢ⟩ eᵢ` in the standard basis
      have he : ∀ a, ∑ i : Fin P, inner ℝ (τ a : Euclid P) (EuclideanSpace.single i 1) •
          EuclideanSpace.single i (1 : ℝ) = (τ a : Euclid P) := by
        intro a
        simpa [EuclideanSpace.basisFun_apply, real_inner_comm] using
          (EuclideanSpace.basisFun (Fin P) ℝ).sum_repr' (τ a : Euclid P)
      calc ∑ i : Fin P, inner ℝ (A (W.starProjection (EuclideanSpace.single i 1)))
              (B (EuclideanSpace.single i 1))
          = ∑ i : Fin P, ∑ a, inner ℝ (τ a : Euclid P) (EuclideanSpace.single i 1) *
              inner ℝ (A (τ a : Euclid P)) (B (EuclideanSpace.single i 1)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hproj, map_sum, sum_inner]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [map_smul, real_inner_smul_left]
        _ = ∑ a, ∑ i : Fin P, inner ℝ (τ a : Euclid P) (EuclideanSpace.single i 1) *
              inner ℝ (A (τ a : Euclid P)) (B (EuclideanSpace.single i 1)) := Finset.sum_comm
        _ = ∑ a, inner ℝ (A (τ a : Euclid P)) (B (∑ i : Fin P, inner ℝ (τ a : Euclid P)
              (EuclideanSpace.single i 1) • EuclideanSpace.single i (1 : ℝ))) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [map_sum, inner_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_smul, real_inner_smul_right]
        _ = ∑ a, inner ℝ (A (τ a : Euclid P)) (B (τ a : Euclid P)) := by simp_rw [he]
    -- Hilbert–Schmidt identities: `Σᵢ |L(p_W eᵢ)|² = Σₐ |L τₐ|²`, also for functionals
    have hhs : ∀ (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        (L : Euclid P →L[ℝ] F),
        ∑ i : Fin P, ‖L (W.starProjection (EuclideanSpace.single i 1))‖ ^ 2 =
          ∑ a, ‖L (τ a : Euclid P)‖ ^ 2 := by
      intro F _ _ L
      have h := htrace F L (L.comp W.starProjection)
      simp only [ContinuousLinearMap.comp_apply, Submodule.starProjection_mem_subspace_eq_self,
        real_inner_self_eq_norm_sq] at h
      exact h
    have hhs1 : ∀ ℓ : Euclid P →L[ℝ] ℝ,
        ∑ i : Fin P, ℓ (W.starProjection (EuclideanSpace.single i 1)) ^ 2 =
          ∑ a, ℓ (τ a : Euclid P) ^ 2 := by
      intro ℓ
      simpa only [Real.norm_eq_abs, sq_abs] using hhs ℝ ℓ
    have hhsf : ∀ (f : Euclid P → ℝ) (ℓ : Euclid P →L[ℝ] ℝ), (∀ u, f u = ℓ u) →
        ∑ i : Fin P, f (W.starProjection (EuclideanSpace.single i 1)) ^ 2 =
          ∑ a, f (τ a : Euclid P) ^ 2 := by
      intro f ℓ hf
      simpa only [hf] using hhs1 ℓ
    -- Parseval in `W`: `⟨u, w⟩ = Σₐ ⟨u, τₐ⟩⟨τₐ, w⟩` for `u ∈ W`
    have hpars : ∀ u ∈ W, ∀ w : Euclid P,
        inner ℝ u w = ∑ a, inner ℝ u (τ a : Euclid P) * inner ℝ (τ a : Euclid P) w := by
      intro u hu w
      calc inner ℝ u w = inner ℝ (W.starProjection u) w := by
            rw [Submodule.starProjection_eq_self_iff.2 hu]
        _ = inner ℝ u (W.starProjection w) := W.inner_starProjection_left_eq_right u w
        _ = _ := by
            rw [hproj, inner_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [real_inner_smul_right, mul_comm]
    -- the components `h_ad = ⟨Dτₐ, τ_d⟩` and `dh_cad = ⟨Φ(τ_c)τₐ, τ_d⟩`
    obtain ⟨H, hH⟩ : ∃ H : Fin (n + 1) → Fin (n + 1) → ℝ,
        ∀ a d, H a d = inner ℝ (D (τ a : Euclid P)) (τ d : Euclid P) := ⟨_, fun _ _ => rfl⟩
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ,
        ∀ c a d, Ψ c a d = inner ℝ (Φ (τ c : Euclid P) (τ a : Euclid P)) (τ d : Euclid P) :=
      ⟨_, fun _ _ _ => rfl⟩
    -- (a) `|A|² = Σ h²`
    have hS : ∑ i : Fin P, ‖D (W.starProjection (EuclideanSpace.single i 1))‖ ^ 2 =
        ∑ a, ∑ d, H a d ^ 2 := by
      rw [hhs (Euclid P) D]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← real_inner_self_eq_norm_sq, hpars _ (hDW a)]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [hH, real_inner_comm (D (τ a : Euclid P)) (τ d : Euclid P)]
      ring
    -- (b) `|∇A|² = Σ dh²`, one slot at a time
    have hG : (∑ i : Fin P, ∑ j : Fin P, ∑ k : Fin P,
        inner ℝ (Φ (W.starProjection (EuclideanSpace.single k 1))
          (W.starProjection (EuclideanSpace.single i 1)))
          (W.starProjection (EuclideanSpace.single j 1)) ^ 2) =
        ∑ c, ∑ a, ∑ d, Ψ c a d ^ 2 := by
      calc _ = ∑ i : Fin P, ∑ j : Fin P, ∑ c, inner ℝ (Φ (τ c : Euclid P)
              (W.starProjection (EuclideanSpace.single i 1)))
              (W.starProjection (EuclideanSpace.single j 1)) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            exact hhsf
              (fun u => inner ℝ (Φ u (W.starProjection (EuclideanSpace.single i 1)))
                (W.starProjection (EuclideanSpace.single j 1)))
              ((innerSL ℝ (W.starProjection (EuclideanSpace.single j 1))).comp
                ((ContinuousLinearMap.apply ℝ (Euclid P)
                  (W.starProjection (EuclideanSpace.single i 1))).comp Φ))
              (fun u => by
                rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
                  ContinuousLinearMap.apply_apply, innerSL_apply_apply, real_inner_comm])
        _ = ∑ i : Fin P, ∑ c, ∑ j : Fin P, inner ℝ (Φ (τ c : Euclid P)
              (W.starProjection (EuclideanSpace.single i 1)))
              (W.starProjection (EuclideanSpace.single j 1)) ^ 2 :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i : Fin P, ∑ c, ∑ d, inner ℝ (Φ (τ c : Euclid P)
              (W.starProjection (EuclideanSpace.single i 1))) (τ d : Euclid P) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
            exact hhsf
              (fun u => inner ℝ (Φ (τ c : Euclid P)
                (W.starProjection (EuclideanSpace.single i 1))) u)
              (innerSL ℝ (Φ (τ c : Euclid P) (W.starProjection (EuclideanSpace.single i 1))))
              (fun u => (innerSL_apply_apply _ _ _).symm)
        _ = ∑ c, ∑ i : Fin P, ∑ d, inner ℝ (Φ (τ c : Euclid P)
              (W.starProjection (EuclideanSpace.single i 1))) (τ d : Euclid P) ^ 2 :=
            Finset.sum_comm
        _ = ∑ c, ∑ d, ∑ i : Fin P, inner ℝ (Φ (τ c : Euclid P)
              (W.starProjection (EuclideanSpace.single i 1))) (τ d : Euclid P) ^ 2 :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
        _ = ∑ c, ∑ d, ∑ a,
              inner ℝ (Φ (τ c : Euclid P) (τ a : Euclid P)) (τ d : Euclid P) ^ 2 := by
            refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
            exact hhsf (fun u => inner ℝ (Φ (τ c : Euclid P) u) (τ d : Euclid P))
              ((innerSL ℝ (τ d : Euclid P)).comp (Φ (τ c : Euclid P)))
              (fun u => by
                rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, real_inner_comm])
        _ = ∑ c, ∑ a, ∑ d, Ψ c a d ^ 2 := by
            simp only [hΨ]
            exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    -- (c) `|∇|A|²|² = 4 Σ_c (Σ_{a,d} h_ad dh_cad)²`
    have hgrad : ∑ k : Fin P, g (W.starProjection (EuclideanSpace.single k 1)) ^ 2 =
        4 * ∑ c, (∑ a, ∑ d, H a d * Ψ c a d) ^ 2 := by
      rw [hhs1 g, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hc : ∑ a, inner ℝ (D (τ a : Euclid P)) (Φ (τ c : Euclid P) (τ a : Euclid P)) =
          ∑ a, ∑ d, H a d * Ψ c a d := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hpars _ (hDW a)]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hH, hΨ, real_inner_comm (Φ (τ c : Euclid P) (τ a : Euclid P)) (τ d : Euclid P)]
      rw [hg c, htrace (Euclid P) D (Φ (τ c : Euclid P)), hc]
      ring
    -- Simon's (1): `h` vanishes in the radial row and column
    have hH1 : ∀ a, H (Fin.last n) a = 0 := fun a => by rw [hH, hDlast, inner_zero_left]
    have hH2 : ∀ a, H a (Fin.last n) = 0 := fun a => by
      rw [hH, hDsym, hDlast, inner_zero_left]
    -- Simon's (2) with Codazzi: `dh_{c n d} = dh_{c d n} = −ρ⁻¹ h_cd`
    have hΨ1 : ∀ c d, Ψ c (Fin.last n) d = -(ρ⁻¹ * H c d) := by
      intro c d
      rw [hΨ, hH, hΦsym₁ c (Fin.last n) d, hΦlast, neg_apply, smul_apply,
        ContinuousLinearMap.comp_apply, Submodule.starProjection_mem_subspace_eq_self,
        inner_neg_left, real_inner_smul_left]
    have hΨ2 : ∀ c a, Ψ c a (Fin.last n) = -(ρ⁻¹ * H c a) := by
      intro c a
      rw [← hΨ1 c a, hΨ, hΨ, hΦsym₂ c a (Fin.last n)]
    -- `h` lives on the tangential block `Fin n × Fin n`
    have hR : ∀ c, ∑ d, H c d ^ 2 = ∑ j : Fin n, H c j.castSucc ^ 2 := fun c => by
      rw [Fin.sum_univ_castSucc, hH2, sq, mul_zero, add_zero]
    have hS' : ∑ a, ∑ d, H a d ^ 2 = ∑ i : Fin n, ∑ j : Fin n, H i.castSucc j.castSucc ^ 2 := by
      rw [Fin.sum_univ_castSucc, hR (Fin.last n)]
      simp only [hH1, hR, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, add_zero]
    -- for each `c`, the radial entries of `dh_c` contribute `2ρ⁻² Σ_d h_cd²` to `Σ dh_c²`,
    -- and Cauchy–Schwarz on the tangential block gives `(Σ h dh_c)² ≤ |A|² Σ_{tangential} dh_c²`
    have key : ∀ c, (∑ a, ∑ d, H a d * Ψ c a d) ^ 2 +
        2 * ρ⁻¹ ^ 2 * (∑ a, ∑ d, H a d ^ 2) * ∑ d, H c d ^ 2 ≤
          (∑ a, ∑ d, H a d ^ 2) * ∑ a, ∑ d, Ψ c a d ^ 2 := by
      intro c
      have hX : ∑ a, ∑ d, H a d * Ψ c a d =
          ∑ i : Fin n, ∑ j : Fin n, H i.castSucc j.castSucc * Ψ c i.castSucc j.castSucc := by
        simp only [Fin.sum_univ_castSucc, hH1, hH2, zero_mul, Finset.sum_const_zero, add_zero]
      have hT : ∑ a, ∑ d, Ψ c a d ^ 2 = ∑ i : Fin n, ∑ j : Fin n, Ψ c i.castSucc j.castSucc ^ 2 +
          2 * ρ⁻¹ ^ 2 * ∑ d, H c d ^ 2 := by
        rw [hR c]
        simp only [Fin.sum_univ_castSucc, hΨ1, hΨ2, hH2, Finset.sum_add_distrib]
        simp only [neg_sq, mul_pow, ← Finset.mul_sum, mul_zero, zero_pow two_ne_zero]
        ring
      have hCS : (∑ i : Fin n, ∑ j : Fin n, H i.castSucc j.castSucc *
          Ψ c i.castSucc j.castSucc) ^ 2 ≤
            (∑ i : Fin n, ∑ j : Fin n, H i.castSucc j.castSucc ^ 2) *
              ∑ i : Fin n, ∑ j : Fin n, Ψ c i.castSucc j.castSucc ^ 2 := by
        have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n × Fin n))
          (fun q => H q.1.castSucc q.2.castSucc) (fun q => Ψ c q.1.castSucc q.2.castSucc)
        simpa only [Fintype.sum_prod_type] using h
      rw [hX, hT, hS']
      nlinarith [hCS]
    -- sum over `c`, using `Σ_c Σ_d h_cd² = |A|²`
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun c _ => key c
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    rw [hS, hG, hgrad]
    have e : 2 * (∑ a, ∑ d, H a d ^ 2) ^ 2 / ρ ^ 2 =
        2 * ρ⁻¹ ^ 2 * (∑ a, ∑ d, H a d ^ 2) ^ 2 := by ring
    rw [e]
    nlinarith [hsum]
  exact frame _ b (fderiv ℝ ν x) _ _ ‖x‖
    (fun a => Submodule.subset_span (hCZ _ (hbT a) _ (hbT a)).1)
    (fun a c => (hCZ _ (hbT a) _ (hbT c)).2.1)
    (by rw [hlast, map_smul, hDx, smul_zero])
    (fun a c d => ((hCZ _ (hbT a) _ (hbT c)).2.2 _ (hbT d)).1)
    (fun a c d => ((hCZ _ (hbT a) _ (hbT c)).2.2 _ (hbT d)).2)
    (by rw [hlast, map_smul, hΦW x hxW, hrad, smul_neg]) hg
/-- **Simon, Appendix B, end of the proof of B.2** (the extension of (3) under (4), the cut-offs
`γ_ε`, and the choice (6); `chapter-B.txt` lines 250–282).  Let `M ⊆ A₀ ≅ ℝ^{m+1}`, `2 ≤ m ≤ 6`,
be a smooth embedded hypercone (`0 ∉ M`, `tM = M`, `M̄ ⊆ M ∪ {0}`, locally `Hᵐ`-finite) with unit
normal `ν`, density one at each of its points, and the Hardy-type inequality (3)
`2∫ψ²|A|²/|x|² ≤ ∫|A|²|∇^Mψ|²` for compactly supported locally Lipschitz `ψ`.  Then
`Dν(x)v = 0` for `x ∈ M`, `v ∈ T_xM`.

Proof.  `|A|² = Σⱼ|Dν(x)(P_xeⱼ)|²` is continuous on `M` (`P_x = Π_{A₀} − ν(x) ⊗ ν(x)`,
`Submission.codim1_hcp_sc_tangent_normal_complement`) and homogeneous of degree `−2`
(`Submission.codim1_hcp_sc_cone_normal_homogeneous`), so `|A|² ≤ c|x|⁻²`.  The profile is the
smooth variant `p(ρ) = ρᵃ/(1 + ρ^{a−b})`, `a = 1 + ε = 11/10`, `b = 2 − m/2 − ε`, of the printed
`ψ = r^{1+ε} r₁^{1−n/2−2ε}` (`ε = 1/10`): `p ≤ ρᵃ`, `p ≤ ρᵇ` and `(ρp')² ≤ (11/10)²p²`, since
`ρp'/p` lies between `b ≥ −11/10` and `a`.  Hence `F = |A|²p(|x|)²/|x|²` is `Hᵐ`-integrable on
`M` by the dyadic estimates of `Submission.codim1_hcp_sc_cone_annuli_measure` (replacing the polar
formula (5)).  For `κₙ = 1/(n+2)` let `gₙ` be the piecewise-linear cut-off (`0` below `κₙ/2`,
`1` on `[κₙ, 1/κₙ]`, `0` above `2/κₙ`, `|ρgₙ'| ≤ 2`).  The test function `ψₙ = p(|x|)gₙ(|x|)`
is locally Lipschitz on `M` and vanishes outside the compact `M ∩ {κₙ/2 ≤ |x| ≤ 2/κₙ}`; as
`x ∈ T_xM`, `Σⱼ(δⱼψₙ)² = (p'gₙ + pgₙ')²(|x|)` off the null spheres
(`Submission.codim1_hcp_sc_fderivWithin_tangent_eq`).  Applying (3) to `ψₙ` with
`(a + b)² ≤ (3/2)a² + 3b²` gives `(37/200)∫gₙ²F ≤ 3∫|A|²p²gₙ'²`, and dominated convergence
yields `(37/200)∫_M F ≤ 0`.  Hence `|A|² = 0` a.e. on `M`, so everywhere on `M` by continuity and
density one, and finally `Dν(x) = 0` on `T_xM`. -/
theorem Submission.codim1_hcp_sc_hardy_cone_flat : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ z ∈ M, Tendsto (fun s : ℝ => μHE[m] (M ∩ ball z s) / (unitBallVolume m * ENNReal.ofReal (s ^ m))) (𝓝[>] 0) (𝓝 1)) → (∀ ψ : Euclid P → ℝ, LocallyLipschitzOn M ψ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ψ x = 0) → 2 * (∫ x in M, ψ x ^ 2 * (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) / ‖x‖ ^ 2 ∂μHE[m]) ≤ ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * (∑ j : Fin P, (fderivWithin ℝ ψ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) → ∀ x ∈ M, ∀ v ∈ tangentSpace M x, fderiv ℝ ν x v = 0 := by
  intro P m A₀ M ν hm2 hm6
  -- Step 4: the profile `p(ρ) = ρᵃ/(1 + ρ^{a−b})`, `a = 11/10`, `b = 19/10 − m/2`
  obtain ⟨p, p', hpC, hp, hp0, hp', hpα, hpβ⟩ : ∃ p p' : ℝ → ℝ,
      (∀ ρ : ℝ, 0 < ρ → ContDiffAt ℝ 1 p ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → HasDerivAt p (p' ρ) ρ) ∧ (∀ ρ : ℝ, 0 < ρ → 0 < p ρ) ∧
      (∀ ρ : ℝ, 0 < ρ → (ρ * p' ρ) ^ 2 ≤ 121 / 100 * p ρ ^ 2) ∧
      (∀ ρ : ℝ, 0 < ρ → p ρ ^ 2 ≤ ρ ^ (-(9 / 5) : ℝ) * ρ ^ 4) ∧
      (∀ ρ : ℝ, 0 < ρ → p ρ ^ 2 ≤ ρ ^ (-(m : ℝ) - 1 / 5) * ρ ^ 4) := by
    have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hm6' : (m : ℝ) ≤ 6 := by exact_mod_cast hm6
    set a : ℝ := 11 / 10 with ha
    set b : ℝ := 19 / 10 - (m : ℝ) / 2 with hb
    set c : ℝ := a - b with hc
    have hc0 : 0 < c := by rw [hc, ha, hb]; linarith
    -- `(ρ^e)² = ρ^{2e−4} ρ⁴`
    have hsq : ∀ ρ : ℝ, 0 < ρ → ∀ e : ℝ, (ρ ^ e) ^ 2 = ρ ^ (2 * e - 4) * ρ ^ 4 := by
      intro ρ hρ e
      rw [← Real.rpow_two, ← Real.rpow_mul hρ.le, ← Real.rpow_natCast ρ 4, ← Real.rpow_add hρ]
      congr 1
      push_cast
      ring
    refine ⟨fun r => r ^ a / (1 + r ^ c),
      fun r => (a * r ^ (a - 1) * (1 + r ^ c) - r ^ a * (c * r ^ (c - 1))) / (1 + r ^ c) ^ 2,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ρ hρ
      exact (Real.contDiffAt_rpow_const_of_ne hρ.ne').div
        (contDiffAt_const.add (Real.contDiffAt_rpow_const_of_ne hρ.ne')) (by positivity)
    · intro ρ hρ
      have h1 := Real.hasDerivAt_rpow_const (p := a) (Or.inl hρ.ne')
      have h2 := (Real.hasDerivAt_rpow_const (p := c) (Or.inl hρ.ne')).const_add 1
      exact h1.div h2 (by positivity)
    · intro ρ hρ
      positivity
    · intro ρ hρ
      have hX : 0 < ρ ^ a := Real.rpow_pos_of_pos hρ a
      have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
      simp only
      rw [Real.rpow_sub_one hρ.ne', Real.rpow_sub_one hρ.ne']
      set X := ρ ^ a
      set t := ρ ^ c
      have key : ρ * ((a * (X / ρ) * (1 + t) - X * (c * (t / ρ))) / (1 + t) ^ 2) =
          X / (1 + t) * ((a + b * t) / (1 + t)) := by
        rw [hc]
        field_simp
        ring
      rw [key, mul_pow]
      have hq : ((a + b * t) / (1 + t)) ^ 2 ≤ 121 / 100 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have h1 : -(11 / 10) * (1 + t) ≤ a + b * t := by rw [ha, hb]; nlinarith
        have h2 : a + b * t ≤ 11 / 10 * (1 + t) := by rw [ha, hb]; nlinarith
        nlinarith
      have := sq_nonneg (X / (1 + t))
      nlinarith
    · intro ρ hρ
      have hX : 0 ≤ ρ ^ a := Real.rpow_nonneg hρ.le a
      have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
      have hle : ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ a := div_le_self hX (by linarith)
      calc (ρ ^ a / (1 + ρ ^ c)) ^ 2 ≤ (ρ ^ a) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
        _ = ρ ^ (-(9 / 5) : ℝ) * ρ ^ 4 := by rw [hsq ρ hρ a, ha]; norm_num
    · intro ρ hρ
      have hX : 0 ≤ ρ ^ a := Real.rpow_nonneg hρ.le a
      have ht : 0 < ρ ^ c := Real.rpow_pos_of_pos hρ c
      have hle : ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ b := by
        calc ρ ^ a / (1 + ρ ^ c) ≤ ρ ^ a / ρ ^ c := div_le_div_of_nonneg_left hX ht (by linarith)
          _ = ρ ^ b := by rw [← Real.rpow_sub hρ, hc]; ring_nf
      calc (ρ ^ a / (1 + ρ ^ c)) ^ 2 ≤ (ρ ^ b) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
        _ = ρ ^ (-(m : ℝ) - 1 / 5) * ρ ^ 4 := by rw [hsq ρ hρ b, hb]; ring_nf
  -- Step 6: the piecewise-linear cut-off `g_κ` and its derivative `g_κ'` off the break points
  have hcutoff : ∀ κ : ℝ, 0 < κ → κ < 1 → ∃ g g' : ℝ → ℝ, (∃ K, LipschitzWith K g) ∧
      (∀ ρ, 0 ≤ g ρ ∧ g ρ ≤ 1) ∧ (∀ ρ, ρ < κ / 2 ∨ 2 / κ < ρ → g ρ = 0) ∧
      (∀ ρ, ρ ≠ κ / 2 → ρ ≠ κ → ρ ≠ 1 / κ → ρ ≠ 2 / κ → HasDerivAt g (g' ρ) ρ) ∧
      Measurable g' ∧ (∀ ρ, 0 < ρ → (ρ * g' ρ) ^ 2 ≤ 4) ∧
      (∀ ρ, κ < ρ → ρ < 1 / κ → g ρ = 1 ∧ g' ρ = 0) := by
    intro κ hκ0 hκ1
    classical
    set g : ℝ → ℝ := fun ρ => max 0 (min 1 (min (2 * ρ / κ - 1) (2 - κ * ρ))) with hg
    set g' : ℝ → ℝ := fun ρ =>
      if ρ ∈ Ioo (κ / 2) κ then 2 / κ else if ρ ∈ Ioo (1 / κ) (2 / κ) then -κ else 0 with hg'
    -- the break points are ordered: `κ/2 < κ < 1/κ < 2/κ`
    have hb1 : κ / 2 < κ := by linarith
    have hb2 : κ < 1 / κ := by rw [lt_div_iff₀ hκ0]; nlinarith
    have hb3 : 1 / κ < 2 / κ := div_lt_div_of_pos_right one_lt_two hκ0
    -- `2ρ/κ − 1` and `2 − κρ` against the break points
    have hA0 : ∀ ρ, ρ ≤ κ / 2 → 2 * ρ / κ - 1 ≤ 0 := fun ρ hρ => by
      rw [sub_nonpos, div_le_one hκ0]; linarith
    have hA0' : ∀ ρ, κ / 2 ≤ ρ → 0 ≤ 2 * ρ / κ - 1 := fun ρ hρ => by
      rw [sub_nonneg, le_div_iff₀ hκ0]; linarith
    have hA1 : ∀ ρ, ρ ≤ κ → 2 * ρ / κ - 1 ≤ 1 := fun ρ hρ => by
      rw [sub_le_iff_le_add, div_le_iff₀ hκ0]; linarith
    have hA1' : ∀ ρ, κ ≤ ρ → 1 ≤ 2 * ρ / κ - 1 := fun ρ hρ => by
      rw [le_sub_iff_add_le, le_div_iff₀ hκ0]; linarith
    have hB1 : ∀ ρ, ρ ≤ 1 / κ → 1 ≤ 2 - κ * ρ := fun ρ hρ => by
      rw [le_div_iff₀ hκ0] at hρ; linarith
    have hB1' : ∀ ρ, 1 / κ ≤ ρ → 2 - κ * ρ ≤ 1 := fun ρ hρ => by
      rw [div_le_iff₀ hκ0] at hρ; linarith
    have hB0 : ∀ ρ, ρ ≤ 2 / κ → 0 ≤ 2 - κ * ρ := fun ρ hρ => by
      rw [le_div_iff₀ hκ0] at hρ; linarith
    have hB0' : ∀ ρ, 2 / κ ≤ ρ → 2 - κ * ρ ≤ 0 := fun ρ hρ => by
      rw [div_le_iff₀ hκ0] at hρ; linarith
    -- values of `g` on the five pieces
    have hv1 : ∀ ρ, ρ ≤ κ / 2 → g ρ = 0 := fun ρ hρ =>
      max_eq_left ((min_le_right _ _).trans ((min_le_left _ _).trans (hA0 ρ hρ)))
    have hv2 : ∀ ρ, κ / 2 ≤ ρ → ρ ≤ κ → g ρ = 2 * ρ / κ - 1 := fun ρ hρ hρ' => by
      have h1 := hA1 ρ hρ'
      have h2 := hB1 ρ (hρ'.trans hb2.le)
      simp only [hg, min_eq_left (h1.trans h2), min_eq_right h1, max_eq_right (hA0' ρ hρ)]
    have hv3 : ∀ ρ, κ ≤ ρ → ρ ≤ 1 / κ → g ρ = 1 := fun ρ hρ hρ' => by
      have h := le_min (hA1' ρ hρ) (hB1 ρ hρ')
      simp only [hg, min_eq_left h, max_eq_right zero_le_one]
    have hv4 : ∀ ρ, 1 / κ ≤ ρ → ρ ≤ 2 / κ → g ρ = 2 - κ * ρ := fun ρ hρ hρ' => by
      have h1 := hB1' ρ hρ
      have h2 := hA1' ρ (hb2.le.trans hρ)
      simp only [hg, min_eq_right (h1.trans h2), min_eq_right h1, max_eq_right (hB0 ρ hρ')]
    have hv5 : ∀ ρ, 2 / κ ≤ ρ → g ρ = 0 := fun ρ hρ =>
      max_eq_left ((min_le_right _ _).trans ((min_le_right _ _).trans (hB0' ρ hρ)))
    refine ⟨g, g', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Lipschitz: `max 0 (min 1 (min ℓ₁ ℓ₂))` with `ℓ₁, ℓ₂` affine
      have hl1 : LipschitzWith (Real.toNNReal (2 / κ)) (fun ρ : ℝ => 2 * ρ / κ - 1) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
          show 2 * x / κ - 1 - (2 * y / κ - 1) = 2 / κ * (x - y) by ring, abs_mul,
          abs_of_pos (by positivity)]
      have hl2 : LipschitzWith (Real.toNNReal κ) (fun ρ : ℝ => 2 - κ * ρ) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        rw [Real.coe_toNNReal _ hκ0.le, Real.dist_eq, Real.dist_eq,
          show 2 - κ * x - (2 - κ * y) = -κ * (x - y) by ring, abs_mul, abs_neg, abs_of_pos hκ0]
      exact ⟨_, ((hl1.min hl2).const_min 1).const_max 0⟩
    · intro ρ
      exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
    · rintro ρ (hρ | hρ)
      · exact hv1 ρ hρ.le
      · exact hv5 ρ hρ.le
    · intro ρ h1 h2 h3 h4
      rcases lt_or_gt_of_ne h1 with hρ1 | hρ1
      · -- `ρ < κ/2`: `g = 0` near `ρ`
        have hev : g =ᶠ[𝓝 ρ] fun _ => 0 :=
          Filter.eventually_of_mem (Iio_mem_nhds hρ1) fun t ht => hv1 t (le_of_lt ht)
        have hval : g' ρ = 0 := by
          simp only [hg', mem_Ioo]
          rw [ite_eq_right (by intro h; linarith [h.1]), ite_eq_right (by intro h; linarith [h.1])]
        rw [hval]
        exact (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq hev
      rcases lt_or_gt_of_ne h2 with hρ2 | hρ2
      · -- `κ/2 < ρ < κ`: `g(t) = 2t/κ − 1` near `ρ`
        have hev : g =ᶠ[𝓝 ρ] fun t => 2 * t / κ - 1 :=
          Filter.eventually_of_mem (Ioo_mem_nhds hρ1 hρ2) fun t ht => hv2 t ht.1.le ht.2.le
        have hval : g' ρ = 2 / κ := by
          simp only [hg', mem_Ioo]
          rw [ite_eq_left ⟨hρ1, hρ2⟩]
        rw [hval]
        have hd : HasDerivAt (fun t : ℝ => 2 * t / κ - 1) (2 * 1 / κ) ρ :=
          (((hasDerivAt_id ρ).const_mul 2).div_const κ).sub_const 1
        rw [mul_one] at hd
        exact hd.congr_of_eventuallyEq hev
      rcases lt_or_gt_of_ne h3 with hρ3 | hρ3
      · -- `κ < ρ < 1/κ`: `g = 1` near `ρ`
        have hev : g =ᶠ[𝓝 ρ] fun _ => 1 :=
          Filter.eventually_of_mem (Ioo_mem_nhds hρ2 hρ3) fun t ht => hv3 t ht.1.le ht.2.le
        have hval : g' ρ = 0 := by
          simp only [hg', mem_Ioo]
          rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.1])]
        rw [hval]
        exact (hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq hev
      rcases lt_or_gt_of_ne h4 with hρ4 | hρ4
      · -- `1/κ < ρ < 2/κ`: `g(t) = 2 − κt` near `ρ`
        have hev : g =ᶠ[𝓝 ρ] fun t => 2 - κ * t :=
          Filter.eventually_of_mem (Ioo_mem_nhds hρ3 hρ4) fun t ht => hv4 t ht.1.le ht.2.le
        have hval : g' ρ = -κ := by
          simp only [hg', mem_Ioo]
          rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_left ⟨hρ3, hρ4⟩]
        rw [hval]
        have hd : HasDerivAt (fun t : ℝ => 2 - κ * t) (-(κ * 1)) ρ :=
          ((hasDerivAt_id ρ).const_mul κ).const_sub 2
        rw [mul_one] at hd
        exact hd.congr_of_eventuallyEq hev
      · -- `ρ > 2/κ`: `g = 0` near `ρ`
        have hev : g =ᶠ[𝓝 ρ] fun _ => 0 :=
          Filter.eventually_of_mem (Ioi_mem_nhds hρ4) fun t ht => hv5 t (le_of_lt ht)
        have hval : g' ρ = 0 := by
          simp only [hg', mem_Ioo]
          rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.2])]
        rw [hval]
        exact (hasDerivAt_const ρ (0 : ℝ)).congr_of_eventuallyEq hev
    · exact Measurable.ite measurableSet_Ioo measurable_const
        (Measurable.ite measurableSet_Ioo measurable_const measurable_const)
    · intro ρ hρ
      simp only [hg', mem_Ioo]
      split_ifs with h h'
      · have : ρ * (2 / κ) ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ hκ0]; linarith [h.2]
        have h0 : 0 ≤ ρ * (2 / κ) := by positivity
        nlinarith
      · have : ρ * κ ≤ 2 := by
          have := h'.2; rw [lt_div_iff₀ hκ0] at this; linarith
        have h0 : 0 ≤ ρ * κ := by positivity
        nlinarith
      · norm_num
    · intro ρ hρ hρ'
      refine ⟨hv3 ρ hρ.le hρ'.le, ?_⟩
      simp only [hg', mem_Ioo]
      rw [ite_eq_right (by intro h; linarith [h.2]), ite_eq_right (by intro h; linarith [h.1])]
  intro hA₀ hMA₀ h0M hMsub hcl hcone hfin hνO hν hdens hH3
  -- the product of two bounded Lipschitz functions is Lipschitz
  have hlipmul : ∀ (f g : Euclid P → ℝ) (s : Set (Euclid P)) (Kf Kg : NNReal) (Bf Bg : ℝ),
      LipschitzOnWith Kf f s → LipschitzOnWith Kg g s → (∀ x ∈ s, |f x| ≤ Bf) →
      (∀ x ∈ s, |g x| ≤ Bg) →
      LipschitzOnWith (Real.toNNReal Bf * Kg + Real.toNNReal Bg * Kf) (fun x => f x * g x) s := by
    intro f g s Kf Kg Bf Bg hf hg hBf hBg
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf x hx)
    have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg y hy)
    have h1 := hf.dist_le_mul x hx y hy
    have h2 := hg.dist_le_mul x hx y hy
    rw [Real.dist_eq] at h1 h2 ⊢
    push_cast
    rw [Real.coe_toNNReal _ hBf0, Real.coe_toNNReal _ hBg0]
    have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [e]
    calc |f x * (g x - g y) + g y * (f x - f y)| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ Bf * (Kg * dist x y) + Bg * (Kf * dist x y) := by
          gcongr
          · exact hBf x hx
          · exact hBg y hy
      _ = (Bf * Kg + Bg * Kf) * dist x y := by ring
  -- Step 2: radial test functions, `Σⱼ (δⱼ(u ∘ |·|)(x))² = u'(|x|)²` for `x ∈ T_xM`
  have hradial : ∀ (x : Euclid P) (u : ℝ → ℝ) (d : ℝ), x ≠ 0 → x ∈ tangentSpace M x →
      HasDerivAt u d ‖x‖ → ∑ j : Fin P, (fderivWithin ℝ (fun y => u ‖y‖) M x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 =
        d ^ 2 := by
    intro x u d hx hxT hu
    have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
    -- derivative of the norm at `x ≠ 0`
    have hnorm : HasFDerivAt (fun y : Euclid P => ‖y‖) ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x)) x := by
      have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (by positivity)
      simp only [Real.sqrt_sq (norm_nonneg _)] at h1
      exact h1
    have hφ : HasFDerivWithinAt (fun y => u ‖y‖) (d • ((1 / (2 * ‖x‖)) • (2 • innerSL ℝ x))) M x :=
      (hu.comp_hasFDerivAt x hnorm).hasFDerivWithinAt
    have hPx : (Submodule.span ℝ (tangentSpace M x)).starProjection x = x :=
      Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span hxT)
    have key : ∀ j : Fin P, fderivWithin ℝ (fun y => u ‖y‖) M x
        ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) =
        d / ‖x‖ * x.ofLp j := by
      intro j
      rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hφ _
        (Submodule.starProjection_apply_mem _ _)]
      simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← Submodule.inner_starProjection_left_eq_right, hPx, EuclideanSpace.inner_single_right,
        one_mul, conj_trivial]
      field_simp
    simp_rw [key]
    have hs := EuclideanSpace.real_norm_sq_eq x
    calc ∑ j : Fin P, (d / ‖x‖ * x.ofLp j) ^ 2 = (d / ‖x‖) ^ 2 * ∑ j : Fin P, x.ofLp j ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ = (d / ‖x‖) ^ 2 * ‖x‖ ^ 2 := by rw [hs]
      _ = d ^ 2 := by field_simp
  -- Step 1(a): cone facts; `M = M̄ \ {0}` is Borel
  have hM1 : IsEmbeddedSubmanifold 1 m M := hMsub 1
  have hx0 : ∀ x ∈ M, x ≠ 0 := fun x hx h => h0M (h ▸ hx)
  have hxpos : ∀ x ∈ M, 0 < ‖x‖ := fun x hx => norm_pos_iff.2 (hx0 x hx)
  have hclM : ∀ x ∈ closure M, x ≠ 0 → x ∈ M := fun x hx hx' =>
    (Set.mem_insert_iff.1 (hcl hx)).resolve_left hx'
  have hMmeas : MeasurableSet M := by
    have hMeq : M = closure M \ {0} := by
      ext x
      exact ⟨fun hx => ⟨subset_closure hx, hx0 x hx⟩, fun hx => hclM x hx.1 hx.2⟩
    rw [hMeq]
    exact isClosed_closure.measurableSet.diff (measurableSet_singleton 0)
  -- the sibling results
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hA₀ hMA₀ hM1 hν
  have hCN :=
    Submission.codim1_hcp_sc_cone_normal_homogeneous P m A₀ M ν hA₀ hMA₀ hM1 hcone hνO hν
  obtain ⟨hsph, hint_in, hint_out⟩ :=
    Submission.codim1_hcp_sc_cone_annuli_measure P m M h0M hcl hcone hfin
  obtain ⟨O, hO, hMO, hνC⟩ := hνO
  -- Step 1(b): `T_x = A₀ ∩ ν(x)^⊥` is a linear subspace
  have hspan : ∀ x ∈ M, ∀ w ∈ Submodule.span ℝ (tangentSpace M x), w ∈ tangentSpace M x := by
    intro x hx w hw
    have hT := (hNC x hx).1
    have hle : Submodule.span ℝ (tangentSpace M x) ≤ A₀ ⊓ LinearMap.ker (innerₛₗ ℝ (ν x)) := by
      rw [hT, Submodule.span_le]
      rintro v ⟨hvA, hvν⟩
      exact ⟨hvA, hvν⟩
    have hw' := hle hw
    rw [hT]
    exact ⟨hw'.1, hw'.2⟩
  -- `|A|²`, nonnegative and continuous on `M` (`P_x = Π_{A₀} − ν(x) ⊗ ν(x)`)
  set A2 : Euclid P → ℝ := fun x => ∑ j : Fin P,
    ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection
      (EuclideanSpace.single j 1))‖ ^ 2 with hA2
  have hA2nn : ∀ x, 0 ≤ A2 x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hA2cont : ContinuousOn A2 M := by
    have hD : ContinuousOn (fderiv ℝ ν) O := hνC.continuousOn_fderiv_of_isOpen hO (by simp)
    have hνc : ContinuousOn ν O := hνC.continuousOn
    have hÃ : ContinuousOn (fun y => ∑ j : Fin P, ‖fderiv ℝ ν y (A₀.starProjection
        (EuclideanSpace.single j 1) - inner ℝ (ν y) (EuclideanSpace.single j 1) • ν y)‖ ^ 2) O := by
      refine continuousOn_finsetSum _ fun j _ => ?_
      have hinner : ContinuousOn
          (fun y => inner ℝ (ν y) (EuclideanSpace.single j (1 : ℝ) : Euclid P)) O :=
        hνc.inner continuousOn_const
      have hvec : ContinuousOn (fun y =>
          A₀.starProjection (EuclideanSpace.single j (1 : ℝ) : Euclid P) -
          inner ℝ (ν y) (EuclideanSpace.single j (1 : ℝ) : Euclid P) • ν y) O :=
        continuousOn_const.sub (hinner.smul hνc)
      exact ((hD.clm_apply hvec).norm).pow 2
    refine (hÃ.mono hMO).congr fun x hx => ?_
    simp only [hA2, (hNC x hx).2]
  -- Step 1(d): `|A|²(tx) = t⁻²|A|²(x)`
  have hhom : ∀ x ∈ M, ∀ t : ℝ, 0 < t → A2 (t • x) = (t ^ 2)⁻¹ * A2 x := by
    intro x hx t ht
    have htx : t • x ∈ M := hcone t ht x hx
    obtain ⟨-, hνt, hD⟩ := (hCN x hx).2.2 t ht
    simp only [hA2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hP : (Submodule.span ℝ (tangentSpace M (t • x))).starProjection
        (EuclideanSpace.single j 1) = (Submodule.span ℝ (tangentSpace M x)).starProjection
        (EuclideanSpace.single j 1) := by
      rw [(hNC _ htx).2, (hNC x hx).2, hνt]
    have hv := hspan x hx _ (Submodule.starProjection_apply_mem
      (Submodule.span ℝ (tangentSpace M x)) (EuclideanSpace.single j 1))
    have h := hD _ hv
    rw [hP, ← h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← mul_assoc,
      inv_mul_cancel₀ (pow_pos ht 2).ne', one_mul]
  -- Step 1(e): `|A|²(x) ≤ c|x|⁻²`, `c = max_{M ∩ S¹} |A|²`
  obtain ⟨cA, hcA0, hcA⟩ : ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ M, A2 x ≤ c / ‖x‖ ^ 2 := by
    have hSph : IsCompact (closure M ∩ sphere (0 : Euclid P) 1) :=
      (isCompact_sphere 0 1).inter_left isClosed_closure
    have hSphM : closure M ∩ sphere (0 : Euclid P) 1 ⊆ M := fun y hy =>
      hclM y hy.1 (by rintro rfl; simp at hy)
    obtain ⟨c, hc⟩ := hSph.exists_bound_of_continuousOn (hA2cont.mono hSphM)
    refine ⟨max c 0, le_max_right _ _, fun x hx => ?_⟩
    have hr := hxpos x hx
    have hyM : ‖x‖⁻¹ • x ∈ M := hcone _ (inv_pos.2 hr) x hx
    have hy1 : ‖x‖⁻¹ • x ∈ sphere (0 : Euclid P) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
    have hxy : ‖x‖ • (‖x‖⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hb := hc _ ⟨subset_closure hyM, hy1⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hA2nn _)] at hb
    calc A2 x = A2 (‖x‖ • (‖x‖⁻¹ • x)) := by rw [hxy]
      _ = (‖x‖ ^ 2)⁻¹ * A2 (‖x‖⁻¹ • x) := hhom _ hyM _ hr
      _ ≤ (‖x‖ ^ 2)⁻¹ * max c 0 := by gcongr; exact hb.trans (le_max_left _ _)
      _ = max c 0 / ‖x‖ ^ 2 := by rw [inv_mul_eq_div]
  -- Step 3: spheres are null
  have hae : ∀ c : ℝ, 0 < c → ∀ᵐ x ∂(μHE[m].restrict M), ‖x‖ ≠ c := by
    intro c hc
    rw [ae_restrict_iff' hMmeas]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hsph c hc)] with x hx hxM hxc
    exact hx ⟨hxM, mem_sphere_zero_iff_norm.2 hxc⟩
  -- Step 4: the profile `p`
  have hm2' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  -- Step 5: `F = |A|² p(r)²/r²` is integrable on `M`
  set F : Euclid P → ℝ := fun x => A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 with hF
  have hFnn : ∀ x, 0 ≤ F x := fun x =>
    div_nonneg (mul_nonneg (hA2nn x) (sq_nonneg _)) (sq_nonneg _)
  have hpc : ContinuousOn (fun x : Euclid P => p ‖x‖) M := fun x hx =>
    ((hp _ (hxpos x hx)).continuousAt.comp continuous_norm.continuousAt).continuousWithinAt
  have hFcont : ContinuousOn F M :=
    (hA2cont.mul (hpc.pow 2)).div (continuous_norm.continuousOn.pow 2)
      fun x hx => (pow_pos (hxpos x hx) 2).ne'
  have hFle : ∀ x ∈ M, ∀ e : ℝ, p ‖x‖ ^ 2 ≤ ‖x‖ ^ e * ‖x‖ ^ 4 → F x ≤ cA * ‖x‖ ^ e := by
    intro x hx e he
    have hr := hxpos x hx
    have hr2 : 0 < ‖x‖ ^ 2 := by positivity
    show A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 ≤ cA * ‖x‖ ^ e
    rw [div_le_iff₀ hr2]
    calc A2 x * p ‖x‖ ^ 2 ≤ (cA / ‖x‖ ^ 2) * (‖x‖ ^ e * ‖x‖ ^ 4) :=
          mul_le_mul (hcA x hx) he (sq_nonneg _) (by positivity)
      _ = cA * ‖x‖ ^ e * ‖x‖ ^ 2 := by field_simp
  have hFint : Integrable F (μHE[m].restrict M) := by
    refine ⟨hFcont.aestronglyMeasurable hMmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hFnn),
      ← lintegral_inter_add_sdiff _ M (measurableSet_ball (x := (0 : Euclid P)) (ε := 1))]
    refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
    · calc ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal (F x) ∂μHE[m]
          ≤ ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal cA * ENNReal.ofReal (‖x‖ ^ (-(9 / 5) : ℝ))
              ∂μHE[m] := by
            refine setLIntegral_mono' (hMmeas.inter measurableSet_ball) fun x hx => ?_
            rw [← ENNReal.ofReal_mul hcA0]
            exact ENNReal.ofReal_le_ofReal (hFle x hx.1 _ (hpα _ (hxpos x hx.1)))
        _ = ENNReal.ofReal cA * ∫⁻ x in M ∩ ball 0 1, ENNReal.ofReal (‖x‖ ^ (-(9 / 5) : ℝ))
              ∂μHE[m] := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.2 (hint_in _ (by linarith)))
    · calc ∫⁻ x in M \ ball 0 1, ENNReal.ofReal (F x) ∂μHE[m]
          ≤ ∫⁻ x in M \ ball 0 1, ENNReal.ofReal cA * ENNReal.ofReal (‖x‖ ^ (-(m : ℝ) - 1 / 5))
              ∂μHE[m] := by
            refine setLIntegral_mono' (hMmeas.diff measurableSet_ball) fun x hx => ?_
            rw [← ENNReal.ofReal_mul hcA0]
            exact ENNReal.ofReal_le_ofReal (hFle x hx.1 _ (hpβ _ (hxpos x hx.1)))
        _ = ENNReal.ofReal cA * ∫⁻ x in M \ ball 0 1, ENNReal.ofReal (‖x‖ ^ (-(m : ℝ) - 1 / 5))
              ∂μHE[m] := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lt_top_iff_ne_top.2 (hint_out _ (by linarith)))
  -- Step 6: the cut-offs `gₙ`, `κₙ = 1/(n+2)`
  have hκ0 : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 2) := fun n => by positivity
  have hκ1 : ∀ n : ℕ, 1 / ((n : ℝ) + 2) < 1 := fun n => by
    rw [div_lt_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  choose g g' hgL hg01 hgsupp hgd hg'meas hg'bd hg1 using
    fun n : ℕ => hcutoff (1 / ((n : ℝ) + 2)) (hκ0 n) (hκ1 n)
  have hXbd : ∀ n x, ‖g n ‖x‖ ^ 2 * F x‖ ≤ F x := by
    intro n x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hFnn x))]
    have h01 := hg01 n ‖x‖
    have h1 : g n ‖x‖ ^ 2 ≤ 1 := by nlinarith [h01.1, h01.2]
    calc g n ‖x‖ ^ 2 * F x ≤ 1 * F x := mul_le_mul_of_nonneg_right h1 (hFnn x)
      _ = F x := one_mul _
  have hYbd : ∀ n, ∀ x ∈ M, ‖A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2‖ ≤ 4 * F x := by
    intro n x hx
    have hr := hxpos x hx
    have hb := hg'bd n ‖x‖ hr
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (hA2nn x) (sq_nonneg _)) (sq_nonneg _))]
    have h4 : g' n ‖x‖ ^ 2 ≤ 4 / ‖x‖ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hb]
    calc A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ≤ A2 x * p ‖x‖ ^ 2 * (4 / ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (hA2nn x) (sq_nonneg _))
      _ = 4 * F x := by simp only [hF]; ring
  have hXint : ∀ n, Integrable (fun x => g n ‖x‖ ^ 2 * F x) (μHE[m].restrict M) := by
    intro n
    obtain ⟨K, hK⟩ := hgL n
    exact hFint.mono' ((((hK.continuous.comp continuous_norm).continuousOn.pow 2).mul
      hFcont).aestronglyMeasurable hMmeas) (ae_of_all _ (hXbd n))
  have hYint : ∀ n, Integrable (fun x => A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2) (μHE[m].restrict M) := by
    intro n
    refine (hFint.const_mul 4).mono' (((hA2cont.mul (hpc.pow 2)).aestronglyMeasurable
      hMmeas).mul (((hg'meas n).comp measurable_norm).pow_const 2).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' hMmeas]
    exact ae_of_all _ (hYbd n)
  -- Step 6(c)–(e): (3) for `ψₙ = p(r)gₙ(r)` gives `(37/200)∫gₙ²F ≤ 3∫|A|²p²gₙ'²`
  have hkey : ∀ n : ℕ, 37 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) ≤
      3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
    intro n
    set κ : ℝ := 1 / ((n : ℝ) + 2) with hκ
    have hκ' : 0 < κ := hκ0 n
    obtain ⟨K, hK⟩ := hgL n
    -- (a) `ψₙ` is locally Lipschitz on `M`
    have hφL : LocallyLipschitzOn M (fun y : Euclid P => p ‖y‖ * g n ‖y‖) := by
      intro x hx
      obtain ⟨K₁, t, ht, hK₁⟩ :=
        ((hpC ‖x‖ (hxpos x hx)).comp x (contDiffAt_norm ℝ (hx0 x hx))).exists_lipschitzOnWith
      have hxt : x ∈ t := mem_of_mem_nhds ht
      refine ⟨_, t ∩ ball x 1, mem_nhdsWithin_of_mem_nhds (inter_mem ht (ball_mem_nhds x one_pos)),
        hlipmul _ _ _ _ _ (|p ‖x‖| + K₁) 1 (hK₁.mono inter_subset_left)
          ((hK.comp lipschitzWith_one_norm).lipschitzOnWith) ?_ ?_⟩
      · intro y hy
        have h1 := hK₁.dist_le_mul y hy.1 x hxt
        have h2 : dist y x < 1 := hy.2
        rw [Real.dist_eq] at h1
        have h3 : (K₁ : ℝ) * dist y x ≤ K₁ := by
          calc (K₁ : ℝ) * dist y x ≤ K₁ * 1 := mul_le_mul_of_nonneg_left h2.le K₁.2
            _ = K₁ := mul_one _
        have h4 := abs_sub_abs_le_abs_sub (p ‖y‖) (p ‖x‖)
        simp only [Function.comp] at h1 ⊢
        linarith
      · intro y _
        have h01 := hg01 n ‖y‖
        rw [abs_of_nonneg h01.1]
        exact h01.2
    -- (b) `ψₙ` vanishes on `M` outside the compact `M̄ ∩ {κ/2 ≤ r ≤ 2/κ} ⊆ M`
    have hφsupp : ∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧
        ∀ x ∈ M, x ∉ C → p ‖x‖ * g n ‖x‖ = 0 := by
      refine ⟨closure M ∩ (closedBall 0 (2 / κ) \ ball 0 (κ / 2)),
        ((isCompact_closedBall 0 _).diff isOpen_ball).inter_left isClosed_closure, ?_, ?_⟩
      · rintro x ⟨hx, -, hx2⟩
        refine hclM x hx ?_
        rintro rfl
        exact hx2 (mem_ball_self (by positivity))
      · intro x hx hxC
        have hout : ‖x‖ < κ / 2 ∨ 2 / κ < ‖x‖ := by
          rcases lt_or_ge ‖x‖ (κ / 2) with h | h
          · exact Or.inl h
          rcases lt_or_ge (2 / κ) ‖x‖ with h' | h'
          · exact Or.inr h'
          exact absurd ⟨subset_closure hx, mem_closedBall_zero_iff.2 h', fun hb => by
            rw [mem_ball_zero_iff] at hb; linarith⟩ hxC
        rw [hgsupp n ‖x‖ hout, mul_zero]
    -- (c) apply (3)
    have h3 := hH3 (fun y : Euclid P => p ‖y‖ * g n ‖y‖) hφL hφsupp
    -- (d) the right side off the null spheres `r ∈ {κ/2, κ, 1/κ, 2/κ}`
    have hbound : ∫ x in M, A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ∂μHE[m] ≤
        ∫ x in M, (363 / 200 * (g n ‖x‖ ^ 2 * F x) + 3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2))
          ∂μHE[m] := by
      refine integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (hA2nn x) (sq_nonneg _))
        (((hXint n).const_mul _).add ((hYint n).const_mul _)) ?_
      rw [EventuallyLE, ae_restrict_iff' hMmeas]
      refine ae_of_all _ fun x hx => ?_
      have hr := hxpos x hx
      have hpp := hp' ‖x‖ hr
      have h1 : (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ≤
          3 / 2 * (p' ‖x‖ * g n ‖x‖) ^ 2 + 3 * (p ‖x‖ * g' n ‖x‖) ^ 2 := by
        nlinarith [sq_nonneg (p' ‖x‖ * g n ‖x‖ - 2 * (p ‖x‖ * g' n ‖x‖))]
      have h2 : p' ‖x‖ ^ 2 ≤ 121 / 100 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [hpp]
      have h2' : (p' ‖x‖ * g n ‖x‖) ^ 2 ≤ 121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) := by
        calc (p' ‖x‖ * g n ‖x‖) ^ 2 = g n ‖x‖ ^ 2 * p' ‖x‖ ^ 2 := by ring
          _ ≤ g n ‖x‖ ^ 2 * (121 / 100 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = 121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2)) := by ring
      calc A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2
          ≤ A2 x * (3 / 2 * (121 / 100 * (g n ‖x‖ ^ 2 * (p ‖x‖ ^ 2 / ‖x‖ ^ 2))) +
              3 * (p ‖x‖ * g' n ‖x‖) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (hA2nn x)
            linarith
        _ = 363 / 200 * (g n ‖x‖ ^ 2 * F x) + 3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2) := by
            simp only [hF]; ring
    have hsplit : ∫ x in M, (363 / 200 * (g n ‖x‖ ^ 2 * F x) +
          3 * (A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2)) ∂μHE[m] =
        363 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) +
          3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
      rw [integral_add ((hXint n).const_mul _) ((hYint n).const_mul _), integral_const_mul,
        integral_const_mul]
    have hineq : 2 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) ≤
        363 / 200 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) +
          3 * ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m] := by
      calc 2 * (∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m])
          = 2 * ∫ x in M, (p ‖x‖ * g n ‖x‖) ^ 2 * A2 x / ‖x‖ ^ 2 ∂μHE[m] := by
            congr 1
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            simp only [hF]
            ring
        _ ≤ ∫ x in M, A2 x * ∑ j : Fin P, (fderivWithin ℝ (fun y : Euclid P => p ‖y‖ * g n ‖y‖)
              M x ((Submodule.span ℝ (tangentSpace M x)).starProjection
                (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m] := h3
        _ = ∫ x in M, A2 x * (p' ‖x‖ * g n ‖x‖ + p ‖x‖ * g' n ‖x‖) ^ 2 ∂μHE[m] := by
            refine integral_congr_ae ?_
            filter_upwards [hae (κ / 2) (by positivity), hae κ hκ', hae (1 / κ) (by positivity),
              hae (2 / κ) (by positivity), self_mem_ae_restrict hMmeas] with x h1 h2 h3 h4 hxM
            have hrad := hradial x (fun r => p r * g n r) _
              (hx0 x hxM) (hCN x hxM).1 ((hp _ (hxpos x hxM)).mul (hgd n _ h1 h2 h3 h4))
            exact congrArg (fun s => A2 x * s) hrad
        _ ≤ _ := hbound
        _ = _ := hsplit
    linarith
  -- Step 7: `κₙ → 0`; for `x ∈ M`, eventually `gₙ(|x|) = 1` and `gₙ'(|x|) = 0`
  have hev : ∀ x ∈ M, ∀ᶠ n : ℕ in atTop, g n ‖x‖ = 1 ∧ g' n ‖x‖ = 0 := by
    intro x hx
    have hr := hxpos x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖x‖) ‖x‖)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hm1 := le_max_left (1 / ‖x‖) ‖x‖
    have hm2 := le_max_right (1 / ‖x‖) ‖x‖
    have h1 : 1 / ((n : ℝ) + 2) < ‖x‖ := by
      rw [div_lt_iff₀ (by positivity)]
      have h : 1 / ‖x‖ < n + 2 := by linarith
      rw [div_lt_iff₀ hr] at h
      linarith
    have h2 : ‖x‖ < 1 / (1 / ((n : ℝ) + 2)) := by
      rw [one_div_one_div]
      linarith
    exact hg1 n ‖x‖ h1 h2
  have hXlim : Tendsto (fun n => ∫ x in M, g n ‖x‖ ^ 2 * F x ∂μHE[m]) atTop
      (𝓝 (∫ x in M, F x ∂μHE[m])) := by
    refine tendsto_integral_of_dominated_convergence F (fun n => (hXint n).aestronglyMeasurable)
      hFint (fun n => ae_of_all _ (hXbd n)) ?_
    rw [ae_restrict_iff' hMmeas]
    refine ae_of_all _ fun x hx => tendsto_const_nhds.congr' ?_
    filter_upwards [hev x hx] with n hn
    rw [hn.1]
    ring
  have hYlim : Tendsto (fun n => ∫ x in M, A2 x * p ‖x‖ ^ 2 * g' n ‖x‖ ^ 2 ∂μHE[m]) atTop
      (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μHE[m].restrict M)
      (f := fun _ => (0 : ℝ)) (fun x => 4 * F x) (fun n => (hYint n).aestronglyMeasurable)
      (hFint.const_mul 4) (fun n => (ae_restrict_iff' hMmeas).2 (ae_of_all _ (hYbd n))) ?_
    · simpa using h
    rw [ae_restrict_iff' hMmeas]
    refine ae_of_all _ fun x hx => tendsto_const_nhds.congr' ?_
    filter_upwards [hev x hx] with n hn
    rw [hn.2]
    ring
  -- Step 8: `(37/200)∫_M F ≤ 0`, so `∫_M F = 0`
  have hJ0 : ∫ x in M, F x ∂μHE[m] = 0 := by
    have hlim := le_of_tendsto_of_tendsto' (hXlim.const_mul (37 / 200)) (hYlim.const_mul 3) hkey
    rw [mul_zero] at hlim
    have hJnn : 0 ≤ ∫ x in M, F x ∂μHE[m] := integral_nonneg hFnn
    linarith
  -- Step 9: `|A|² = 0` a.e. on `M`
  have hAE : ∀ᵐ x ∂μHE[m], x ∈ M → A2 x = 0 := by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hFnn) hFint).1 hJ0
    rw [EventuallyEq, ae_restrict_iff' hMmeas] at h
    filter_upwards [h] with x hx hxM
    have hFx : A2 x * p ‖x‖ ^ 2 / ‖x‖ ^ 2 = 0 := hx hxM
    have hr := hxpos x hxM
    have hpx := hp0 ‖x‖ hr
    rcases div_eq_zero_iff.1 hFx with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (pow_pos hpx 2).ne'
    · exact absurd h1 (pow_pos hr 2).ne'
  -- Step 10: `|A|² ≡ 0` on `M` (continuity and density one)
  have hA2zero : ∀ x ∈ M, A2 x = 0 := by
    intro x₀ hx₀
    by_contra hne
    have hpos : 0 < A2 x₀ := lt_of_le_of_ne (hA2nn x₀) (Ne.symm hne)
    obtain ⟨δ, hδ, hδA⟩ := Metric.continuousOn_iff.1 hA2cont x₀ hx₀ (A2 x₀) hpos
    have hev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        0 < μHE[m] (M ∩ ball x₀ s) / (unitBallVolume m * ENNReal.ofReal (s ^ m)) :=
      (hdens x₀ hx₀).eventually (lt_mem_nhds zero_lt_one)
    have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < δ :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)
    obtain ⟨s, hs1, hs2⟩ := (hev1.and hev2).exists
    have hnull : μHE[m] (M ∩ ball x₀ s) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.1 hAE)
      simp only [mem_ofPred_eq, not_imp]
      refine ⟨hy.1, ?_⟩
      have hd := hδA y hy.1 (lt_trans (mem_ball.1 hy.2) hs2)
      rw [Real.dist_eq] at hd
      have := (abs_lt.1 hd).1
      linarith
    rw [hnull, ENNReal.zero_div] at hs1
    exact lt_irrefl 0 hs1
  -- Step 11: `Dν(x)(P_xeⱼ) = 0` for all `j`, hence `Dν(x) = 0` on `T_x`
  intro x hx v hv
  have hA2x : A2 x = 0 := hA2zero x hx
  simp only [hA2] at hA2x
  have hj : ∀ j : Fin P, fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection
      (EuclideanSpace.single j 1)) = 0 := by
    intro j
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).1 hA2x j
      (Finset.mem_univ j)
    exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)
  have hcomp : (fderiv ℝ ν x).comp (Submodule.span ℝ (tangentSpace M x)).starProjection = 0 := by
    apply ContinuousLinearMap.coe_injective
    refine (EuclideanSpace.basisFun (Fin P) ℝ).toBasis.ext fun j => ?_
    simp [hj j]
  have hPv : (Submodule.span ℝ (tangentSpace M x)).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.2 (Submodule.subset_span hv)
  have h := congrArg (fun L : Euclid P →L[ℝ] Euclid P => L v) hcomp
  simp only [ContinuousLinearMap.comp_apply, hPv, zero_apply] at h
  exact h

/-- **Integration by parts on a stationary hypersurface** (parent proof (4c)).  Let `M ⊆ A₀`
(`dim A₀ = m + 1`, `0 ∉ M`) be stationary away from `0`, with smooth unit normal `ν ∈ A₀` and the
Lipschitz approximation property (HL), and let `F` be `C²` near `M` with `F = f` on `M`.  For `φ`
locally Lipschitz on `M` and vanishing on `M` off a compact subset of `M`, both integrands are
`Hᵐ⌞M`-integrable and `∫_M Σⱼ δⱼφ δⱼf = −∫_M φ Σⱼ δⱼ(δⱼf)`, where `δⱼg(x) = D^M g(x)(Pₓeⱼ)`.

By normal_complement `Pₓeⱼ = Πeⱼ − ⟨ν(x), eⱼ⟩ν(x)` on `M`, so (tangent_fderiv) `δⱼf` and
`δⱼ(δⱼf)` are restrictions of `Gⱼ = DF(Πeⱼ − ⟨ν, eⱼ⟩ν)` and `DGⱼ(Πeⱼ − ⟨ν, eⱼ⟩ν)`.  With the (HL)
approximants `χₖ → φ` and a cut-off `β` equal to `1` on the supports, `Xₖ = χₖβ Σⱼ Gⱼeⱼ` is an
admissible field and `tr(Pₓ ∘ DXₖ(x)) = Σⱼ δⱼχₖ δⱼf + χₖ Σⱼ δⱼ(δⱼf)` on `M`, whose integral
vanishes by stationarity.  Let `k → ∞`: Cauchy–Schwarz and Hölder turn the `L²` convergence
`δχₖ → δφ` into `L¹` convergence of the first term, and dominated convergence handles the second. -/
theorem Submission.codim1_hcp_sc_stationary_integration_by_parts : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → IsEmbeddedSubmanifold 1 m M → MeasurableSet M → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → (0 : Euclid P) ∉ tsupport X → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → ((∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0)) → ∀ (f F : Euclid P → ℝ) (O' : Set (Euclid P)), IsOpen O' → M ⊆ O' → ContDiffOn ℝ 2 F O' → (∀ y ∈ M, F y = f y) → ∀ φ : Euclid P → ℝ, LocallyLipschitzOn M φ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → φ x = 0) → Integrable (fun x => ∑ j : Fin P, fderivWithin ℝ φ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M) ∧ Integrable (fun x => φ x * ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M) ∧ ∫ x in M, (∑ j : Fin P, fderivWithin ℝ φ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ∂μHE[m] = -(∫ x in M, φ x * (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y ((Submodule.span ℝ (tangentSpace M y)).starProjection (EuclideanSpace.single j 1))) M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ∂μHE[m]) := by
  intro P m A₀ M ν hdim hMA hM0 hMsub hMmeas hMfin hstat hνO hν HL f F O' hO' hMO' hF hFf φ hφ hφC
  have hTan := Submission.codim1_hcp_sc_fderivWithin_tangent_eq
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hdim hMA hMsub hν
  obtain ⟨O, hO, hMO, hνs⟩ := hνO
  obtain ⟨HL1, HL2⟩ := HL
  obtain ⟨C, hC, hCM, hφ0⟩ := hφC
  -- `Pr x = Pₓ`, the orthogonal projection onto `span TₓM`
  obtain ⟨Pr, hPr⟩ : ∃ Pr : Euclid P → Euclid P →L[ℝ] Euclid P,
      ∀ x, Pr x = (Submodule.span ℝ (tangentSpace M x)).starProjection := ⟨_, fun _ => rfl⟩
  simp only [← hPr] at HL1 HL2 hstat ⊢
  have hPr_mem : ∀ x v, Pr x v ∈ Submodule.span ℝ (tangentSpace M x) := fun x v => by
    rw [hPr]; exact Submodule.starProjection_apply_mem _ v
  -- step 1 (smooth extensions): by normal_complement `Pₓeⱼ = p j x` on `M`, where
  -- `p j z = Πeⱼ − ⟨ν(z), eⱼ⟩ν(z)` is `C¹` on `U = (O ∩ O') \ {0} ⊇ M`; `Gⱼ(z) = DF(z)(p j z)` is
  -- `C¹` on `U`, and `δⱼf = Gⱼ`, `δⱼ(δⱼf) = DGⱼ(pⱼ)` on `M` (tangent_fderiv)
  set p : Fin P → Euclid P → Euclid P := fun j z =>
    A₀.starProjection (EuclideanSpace.single j 1) - inner ℝ (ν z) (EuclideanSpace.single j 1) • ν z
  have hPp : ∀ x ∈ M, ∀ j, Pr x (EuclideanSpace.single j 1) = p j x := fun x hx j => by
    rw [hPr]; exact (hNC x hx).2 _
  set U : Set (Euclid P) := (O ∩ O') \ {0}
  have hUo : IsOpen U := (hO.inter hO').sdiff isClosed_singleton
  have hMU : M ⊆ U := fun x hx =>
    ⟨⟨hMO hx, hMO' hx⟩, fun h0 => hM0 (by rwa [mem_singleton_iff.1 h0] at hx)⟩
  have hν1 : ContDiffOn ℝ 1 ν U :=
    (hνs.of_le (by exact_mod_cast le_top)).mono fun x hx => hx.1.1
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) U :=
    (hF.fderiv_of_isOpen hO' (by norm_num)).mono fun x hx => hx.1.2
  have hp1 : ∀ j, ContDiffOn ℝ 1 (p j) U := fun j =>
    contDiffOn_const.sub ((hν1.inner ℝ contDiffOn_const).smul hν1)
  set G : Fin P → Euclid P → ℝ := fun j z => fderiv ℝ F z (p j z)
  have hG1 : ∀ j, ContDiffOn ℝ 1 (G j) U := fun j => hDF.clm_apply (hp1 j)
  have hGd : ∀ j, ∀ x ∈ U, HasFDerivAt (G j) (fderiv ℝ (G j) x) x := fun j x hx =>
    (((hG1 j).differentiableOn one_ne_zero).differentiableAt (hUo.mem_nhds hx)).hasFDerivAt
  have hdf : ∀ j, ∀ x ∈ M, fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)) = G j x := by
    intro j x hx
    have hFx : HasFDerivAt F (fderiv ℝ F x) x :=
      ((hF.differentiableOn two_ne_zero).differentiableAt (hO'.mem_nhds (hMO' hx))).hasFDerivAt
    rw [hTan P ℝ M f _ x (hFx.hasFDerivWithinAt.congr' (fun y hy => (hFf y hy).symm) hx) _
      (hPr_mem x _), hPp x hx j]
  have hddf : ∀ j, ∀ x ∈ M, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
      (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1)) =
      fderiv ℝ (G j) x (p j x) := by
    intro j x hx
    rw [hTan P ℝ M _ _ x ((hGd j x (hMU hx)).hasFDerivWithinAt.congr' (fun y hy => hdf j y hy) hx)
      _ (hPr_mem x _), hPp x hx j]
  have hdf_cont : ∀ j, ContinuousOn
      (fun x => fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) M := fun j =>
    ((hG1 j).continuousOn.mono hMU).congr fun x hx => hdf j x hx
  have hlap_cont : ContinuousOn (fun x => ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
      (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1))) M :=
    continuousOn_finsetSum _ fun j _ =>
      ((((hG1 j).continuousOn_fderiv_of_isOpen hUo le_rfl).clm_apply
        (hp1 j).continuousOn).mono hMU).congr fun x hx => hddf j x hx
  -- step 2(b): if `g = 0` on `M \ K` (`K` closed), then `g` has tangential derivative `0` there
  have hvanish : ∀ (g : Euclid P → ℝ) (K : Set (Euclid P)), IsClosed K →
      (∀ y ∈ M, y ∉ K → g y = 0) → ∀ x ∈ M, x ∉ K →
      ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderivWithin ℝ g M x v = 0 := by
    intro g K hK hg x hx hxK v hv
    have h0 : HasFDerivWithinAt g (0 : Euclid P →L[ℝ] ℝ) M x := by
      refine (hasFDerivWithinAt_const (0 : ℝ) x M).congr_of_eventuallyEq ?_ (hg x hx hxK)
      filter_upwards [inter_mem_nhdsWithin M (hK.isOpen_compl.mem_nhds hxK)] with y hy
      exact hg y hy.1 hy.2
    simpa using hTan P ℝ M g 0 x h0 v hv
  have hvanish' : ∀ (g : Euclid P → ℝ) (K : Set (Euclid P)), IsClosed K →
      (∀ y ∈ M, y ∉ K → g y = 0) → ∀ x ∈ M, x ∉ K → DifferentiableAt ℝ g x →
      ∀ v ∈ Submodule.span ℝ (tangentSpace M x), fderiv ℝ g x v = 0 := by
    intro g K hK hg x hx hxK hd v hv
    rw [← hTan P ℝ M g _ x hd.hasFDerivAt.hasFDerivWithinAt v hv]
    exact hvanish g K hK hg x hx hxK v hv
  -- step 4: the (HL)(ii) approximants `χₖ` of `φ`, and the compact set `K = C ∪ C'' ⊆ M`
  obtain ⟨C'', χ, hC'', hC''M, hχs, hχ0, hχu, hχL2⟩ := HL2 φ hφ ⟨C, hC, hCM, hφ0⟩
  set K : Set (Euclid P) := C ∪ C''
  have hK : IsCompact K := hC.union hC''
  have hKM : K ⊆ M := union_subset hCM hC''M
  have hμK : (μHE[m].restrict M) K ≠ ∞ := by
    rw [Measure.restrict_apply hK.measurableSet, inter_comm]; exact hMfin K hK
  have hφK : ∀ x ∈ M, x ∉ K → φ x = 0 := fun x hx hxK => hφ0 x hx fun h => hxK (Or.inl h)
  have hχK : ∀ k, ∀ x ∈ M, x ∉ K → χ k x = 0 := fun k x hx hxK =>
    hχ0 k x hx fun h => hxK (Or.inr h)
  have hχ1 : ∀ k, ContDiff ℝ 1 (χ k) := fun k => (hχs k).1.of_le (by exact_mod_cast le_top)
  have hχd : ∀ k x, HasFDerivAt (χ k) (fderiv ℝ (χ k) x) x := fun k x =>
    ((hχ1 k).differentiable one_ne_zero x).hasFDerivAt
  have hdφK : ∀ j, ∀ x ∈ M, x ∉ K → fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1)) = 0 :=
    fun j x hx hxK => hvanish φ C hC.isClosed hφ0 x hx (fun h => hxK (Or.inl h)) _ (hPr_mem x _)
  have hdχK : ∀ k j, ∀ x ∈ M, x ∉ K → fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) = 0 :=
    fun k j x hx hxK => hvanish' (χ k) C'' hC''.isClosed (hχ0 k) x hx (fun h => hxK (Or.inr h))
      (hχd k x).differentiableAt _ (hPr_mem x _)
  have hdχ_cont : ∀ k j, ContinuousOn
      (fun x => fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1))) M := fun k j =>
    ((((hχ1 k).continuous_fderiv one_ne_zero).continuousOn.clm_apply (hp1 j).continuousOn).mono
      hMU).congr fun x hx => by simp only [hPp x hx j]
  -- step 3 (integrability): continuous on `M` and zero on `M \ K` implies integrable,
  -- since `Hᵐ(M ∩ K) < ∞`
  have hint : ∀ h : Euclid P → ℝ, ContinuousOn h M → (∀ x ∈ M, x ∉ K → h x = 0) →
      Integrable h (μHE[m].restrict M) := by
    intro h hc h0
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKM)
    refine Integrable.mono' (g := K.indicator fun _ => B)
      ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hμK))
      (hc.aestronglyMeasurable hMmeas) ?_
    filter_upwards [ae_restrict_mem hMmeas] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]; exact hB x hxK
    · rw [indicator_of_notMem hxK, h0 x hx hxK, norm_zero]
  have hIφB : Integrable (fun x => φ x * ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
      (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1)))
      (μHE[m].restrict M) :=
    hint _ (hφ.continuousOn.mul hlap_cont) fun x hx hxK => by rw [hφK x hx hxK, zero_mul]
  have hIA : ∀ k, Integrable (fun x => ∑ j : Fin P, fderiv ℝ (χ k) x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)))
      (μHE[m].restrict M) := fun k =>
    hint _ (continuousOn_finsetSum _ fun j _ => (hdχ_cont k j).mul (hdf_cont j))
      fun x hx hxK => Finset.sum_eq_zero fun j _ => by rw [hdχK k j x hx hxK, zero_mul]
  have hIB : ∀ k, Integrable (fun x => χ k x * ∑ j : Fin P, fderivWithin ℝ (fun y =>
      fderivWithin ℝ f M y (Pr y (EuclideanSpace.single j 1))) M x
      (Pr x (EuclideanSpace.single j 1))) (μHE[m].restrict M) := fun k =>
    hint _ ((hχ1 k).continuous.continuousOn.mul hlap_cont) fun x hx hxK => by
      rw [hχK k x hx hxK, zero_mul]
  -- step 5 (cut-off): `K ⊆ W₁` with `closure W₁ ⊆ U` compact, and a smooth `β : ℝᴾ → [0, 1]`
  -- with `support β = W₁` and `β = 1` exactly on `K`, so `Dβ = 0` on `K` (maxima of `β`)
  obtain ⟨W₁, hW₁o, hKW₁, hW₁U, hW₁c⟩ :=
    exists_open_between_and_isCompact_closure hK hUo (hKM.trans hMU)
  obtain ⟨β, hβs, hβr, hβsupp, hβ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW₁o hK.isClosed hKW₁
  have hβ1' : ContDiff ℝ 1 β := hβs.of_le (by exact_mod_cast le_top)
  have hβts : tsupport β = closure W₁ := by rw [tsupport, hβsupp]
  have hβU : tsupport β ⊆ U := hβts ▸ hW₁U
  have hβc : HasCompactSupport β := by rw [HasCompactSupport, hβts]; exact hW₁c
  have hβK : ∀ x ∈ K, β x = 1 := fun x hx => (hβ1 x).1 hx
  have hDβ : ∀ x ∈ K, fderiv ℝ β x = 0 := fun x hx =>
    IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun y => by
      rw [hβK x hx]; exact (hβr (mem_range_self y)).2)
  have hβd : ∀ x, HasFDerivAt β (fderiv ℝ β x) x := fun x =>
    (hβ1'.differentiable one_ne_zero x).hasFDerivAt
  -- `Xₖ = Σᵢ cₖᵢ eᵢ` with `cₖᵢ = 1_U χₖ β Gᵢ` is `C¹` with support in `tsupport β ⊆ U ∌ 0`
  set c : ℕ → Fin P → Euclid P → ℝ := fun k i => U.indicator fun z => χ k z * β z * G i z
    with hc_def
  set X : ℕ → Euclid P → Euclid P := fun k z =>
    ∑ i : Fin P, c k i z • EuclideanSpace.single i (1 : ℝ) with hX_def
  have hc_eq : ∀ k i, ∀ x ∈ U, c k i =ᶠ[𝓝 x] fun z => χ k z * β z * G i z := fun k i x hx => by
    filter_upwards [hUo.mem_nhds hx] with z hz
    simp only [hc_def, indicator_of_mem hz]
  have hc1 : ∀ k i, ContDiff ℝ 1 (c k i) := by
    intro k i
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ tsupport β
    · exact ((((hχ1 k).contDiffAt.mul hβ1'.contDiffAt).mul
        ((hG1 i).contDiffAt (hUo.mem_nhds (hβU hz)))).congr_of_eventuallyEq
        (hc_eq k i z (hβU hz)))
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hz] with w hw
      simp only [Pi.zero_apply] at hw
      simp [hc_def, hw]
  have hX1 : ∀ k, ContDiff ℝ 1 (X k) := fun k =>
    ContDiff.sum fun i _ => (hc1 k i).smul contDiff_const
  have hXsupp : ∀ k, support (X k) ⊆ tsupport β := by
    intro k z hz
    by_contra hzβ
    refine hz ?_
    have hβz : β z = 0 := image_eq_zero_of_notMem_tsupport hzβ
    classical
    simp [hX_def, hc_def, indicator_apply, hβz]
  have hXc : ∀ k, HasCompactSupport (X k) := fun k => hβc.mono' (hXsupp k)
  have hX0 : ∀ k, (0 : Euclid P) ∉ tsupport (X k) := fun k h0 =>
    (hβU (closure_minimal (hXsupp k) (isClosed_tsupport β) h0)).2 (mem_singleton _)
  -- step 6: for `x ∈ M`, `tr(Pₓ ∘ DXₖ(x)) = tr(DXₖ(x) ∘ Pₓ) = Σⱼ D(cₖⱼ)(x)(Pₓeⱼ)
  -- = Σⱼ δⱼχₖ δⱼf + χₖ Σⱼ δⱼ(δⱼf)` (product rule; `β = 1`, `Dβ = 0` on `K`, `χₖ = δχₖ = 0` off `K`)
  have htr : ∀ k, ∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Pr x).toLinearMap ∘ₗ
      (fderiv ℝ (X k) x).toLinearMap) =
      ∑ j : Fin P, fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) *
        fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)) +
      χ k x * ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
        (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1)) := by
    intro k x hx
    have hXd : fderiv ℝ (X k) x = ∑ i : Fin P,
        (fderiv ℝ (c k i) x).smulRight (EuclideanSpace.single i (1 : ℝ)) :=
      (HasFDerivAt.fun_sum fun i _ =>
        ((hc1 k i).differentiable one_ne_zero x).hasFDerivAt.smul_const _).fderiv
    rw [LinearMap.trace_comp_comm',
      LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin P) ℝ), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : inner ℝ ((EuclideanSpace.basisFun (Fin P) ℝ) j)
        (((fderiv ℝ (X k) x).toLinearMap ∘ₗ (Pr x).toLinearMap)
          ((EuclideanSpace.basisFun (Fin P) ℝ) j)) =
        fderiv ℝ (c k j) x (Pr x (EuclideanSpace.single j 1)) := by
      rw [EuclideanSpace.basisFun_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.coe_coe, hXd, EuclideanSpace.inner_single_left]
      simp [Pi.single_apply]
    have hprod : HasFDerivAt (fun z => χ k z * β z * G j z)
        ((χ k x * β x) • fderiv ℝ (G j) x +
          G j x • (χ k x • fderiv ℝ β x + β x • fderiv ℝ (χ k) x)) x :=
      ((hχd k x).fun_mul (hβd x)).fun_mul (hGd j x (hMU hx))
    rw [h1, (hc_eq k j x (hMU hx)).fderiv_eq, hprod.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [hdf j x hx, hddf j x hx, ← hPp x hx j]
    by_cases hxK : x ∈ K
    · rw [hβK x hxK, hDβ x hxK]
      simp only [zero_apply]
      ring
    · rw [hχK k x hx hxK, hdχK k j x hx hxK]
      ring
  -- step 7 (stationarity): `∫_M (Σⱼ δⱼχₖ δⱼf + χₖ Σⱼ δⱼ(δⱼf)) = 0`
  have hIk : ∀ k, ∫ x in M, (∑ j : Fin P, fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) *
      fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)) +
      χ k x * ∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
        (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1))) ∂μHE[m] = 0 :=
    fun k => (setIntegral_congr_fun hMmeas fun x hx => (htr k x hx).symm).trans
      (hstat (X k) (hX1 k) (hXc k) (hX0 k))
  -- step 8 (limit): `Σⱼ δⱼχₖ δⱼf → Σⱼ δⱼφ δⱼf` in `L¹`, since on `M`
  -- `|Σⱼ (δⱼχₖ − δⱼφ) δⱼf| ≤ (Σⱼ (δⱼχₖ − δⱼφ)²)^{1/2} · √B₂ · 1_K` (Cauchy–Schwarz in `j`; both
  -- sides vanish off `K`), then Hölder and (HL)(ii)
  have hCS : ∀ (a d : Fin P → ℝ) (B : ℝ), ∑ j, d j ^ 2 ≤ B →
      |∑ j, a j * d j| ≤ Real.sqrt (∑ j, a j ^ 2) * Real.sqrt B := by
    intro a d B hB
    refine (Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)).trans ?_
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hB (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hsq : ∀ a : Fin P → ℝ,
      ENNReal.ofReal (Real.sqrt (∑ j, a j ^ 2)) ^ (2 : ℝ) = ENNReal.ofReal (∑ j, a j ^ 2) :=
    fun a => by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) zero_le_two, Real.rpow_two,
        Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  obtain ⟨B₂, hB₂⟩ := hK.exists_bound_of_continuousOn
    ((continuousOn_finsetSum Finset.univ fun j _ => (hdf_cont j).pow 2).mono hKM)
  have hgm : AEMeasurable (K.indicator fun _ => ENNReal.ofReal (Real.sqrt B₂))
      (μHE[m].restrict M) := aemeasurable_const.indicator hK.measurableSet
  have hg2 : ∫⁻ x in M, (K.indicator (fun _ => ENNReal.ofReal (Real.sqrt B₂)) x) ^ (2 : ℝ)
      ∂μHE[m] ≠ ∞ := by
    have : (fun x => (K.indicator (fun _ => ENNReal.ofReal (Real.sqrt B₂)) x) ^ (2 : ℝ)) =
        K.indicator fun _ => ENNReal.ofReal (Real.sqrt B₂) ^ (2 : ℝ) := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · simp [hx, ENNReal.zero_rpow_of_pos two_pos]
    rw [this, lintegral_indicator_const hK.measurableSet]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg zero_le_two ENNReal.ofReal_ne_top) hμK
  have hAφm : AEStronglyMeasurable (fun x => ∑ j : Fin P, fderivWithin ℝ φ M x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)))
      (μHE[m].restrict M) :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (HL1 φ hφ j).mul ((hdf_cont j).aestronglyMeasurable hMmeas)
  have hEst : ∀ k, ∫⁻ x in M, ‖(∑ j : Fin P, fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) *
      fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) -
      ∑ j : Fin P, fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1)) *
      fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))‖ₑ ∂μHE[m] ≤
      (∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) -
        fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) ^ (1 / 2 : ℝ) *
      (∫⁻ x in M, (K.indicator (fun _ => ENNReal.ofReal (Real.sqrt B₂)) x) ^ (2 : ℝ) ∂μHE[m]) ^
        (1 / 2 : ℝ) := by
    intro k
    have hfm : AEMeasurable (fun x => ENNReal.ofReal (Real.sqrt (∑ j : Fin P,
        (fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) -
          fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1))) ^ 2))) (μHE[m].restrict M) :=
      (Finset.aemeasurable_fun_sum _ fun j _ =>
        ((((hdχ_cont k j).aestronglyMeasurable hMmeas).aemeasurable.sub
          (HL1 φ hφ j).aemeasurable).pow_const 2)).sqrt.ennreal_ofReal
    calc _ ≤ ∫⁻ x in M, ENNReal.ofReal (Real.sqrt (∑ j : Fin P,
            (fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) -
              fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1))) ^ 2)) *
            K.indicator (fun _ => ENNReal.ofReal (Real.sqrt B₂)) x ∂μHE[m] := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem hMmeas] with x hx
          rw [← Finset.sum_sub_distrib, Real.enorm_eq_ofReal_abs]
          simp_rw [← sub_mul]
          by_cases hxK : x ∈ K
          · rw [indicator_of_mem hxK, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hCS _ _ B₂ ((le_abs_self _).trans
              ((Real.norm_eq_abs _).symm.le.trans (hB₂ x hxK))))
          · rw [Finset.sum_eq_zero fun j _ => by
              rw [hdχK k j x hx hxK, hdφK j x hx hxK, sub_zero, zero_mul], abs_zero,
              ENNReal.ofReal_zero]
            exact zero_le
      _ ≤ _ := ENNReal.lintegral_mul_le_Lp_mul_Lq _ Real.HolderConjugate.two_two hfm hgm
      _ = _ := by simp only [hsq]
  have hL1 : Tendsto (fun k => ∫⁻ x in M, ‖(∑ j : Fin P, fderiv ℝ (χ k) x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) -
      ∑ j : Fin P, fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1)) *
      fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))‖ₑ ∂μHE[m]) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k => (∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
        (fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) -
          fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) ^ (1 / 2 : ℝ))
        atTop (𝓝 0) := by
      have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hχL2
      rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this
    have h1 := ENNReal.Tendsto.mul_const h0
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hg2))
    rw [zero_mul] at h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => zero_le) hEst
  -- first conjunct: `Σⱼ δⱼφ δⱼf = Aₖ − (Aₖ − Σⱼ δⱼφ δⱼf)`, `Aₖ = Σⱼ δⱼχₖ δⱼf`, where the last
  -- term has finite `L¹` norm for large `k`
  have hIφA : Integrable (fun x => ∑ j : Fin P, fderivWithin ℝ φ M x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)))
      (μHE[m].restrict M) := by
    obtain ⟨k, hk⟩ := (hL1.eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
    have hdiff : Integrable (fun x => (∑ j : Fin P, fderiv ℝ (χ k) x
        (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) -
        ∑ j : Fin P, fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1)) *
        fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) (μHE[m].restrict M) :=
      ⟨(hIA k).aestronglyMeasurable.sub hAφm, hasFiniteIntegral_iff_enorm.2 hk⟩
    refine ((hIA k).sub hdiff).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, sub_sub_cancel]
  have hTA : Tendsto (fun k => ∫ x in M, (∑ j : Fin P, fderiv ℝ (χ k) x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)))
      ∂μHE[m]) atTop (𝓝 (∫ x in M, (∑ j : Fin P, fderivWithin ℝ φ M x
      (Pr x (EuclideanSpace.single j 1)) * fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1)))
      ∂μHE[m])) :=
    tendsto_integral_of_L1 _ hAφm (Eventually.of_forall hIA) hL1
  -- `∫ χₖ Σⱼ δⱼ(δⱼf) → ∫ φ Σⱼ δⱼ(δⱼf)` by dominated convergence (`χₖ → φ` uniformly on `M`, and
  -- everything vanishes off `K`)
  obtain ⟨Φ, hΦ⟩ := hK.exists_bound_of_continuousOn (hφ.continuousOn.mono hKM)
  obtain ⟨L, hL⟩ := hK.exists_bound_of_continuousOn (hlap_cont.mono hKM)
  have hTB : Tendsto (fun k => ∫ x in M, χ k x * (∑ j : Fin P, fderivWithin ℝ (fun y =>
      fderivWithin ℝ f M y (Pr y (EuclideanSpace.single j 1))) M x
      (Pr x (EuclideanSpace.single j 1))) ∂μHE[m]) atTop (𝓝 (∫ x in M, φ x * (∑ j : Fin P,
      fderivWithin ℝ (fun y => fderivWithin ℝ f M y (Pr y (EuclideanSpace.single j 1))) M x
      (Pr x (EuclideanSpace.single j 1))) ∂μHE[m])) := by
    refine tendsto_integral_filter_of_dominated_convergence (K.indicator fun _ => (Φ + 1) * L)
      (Eventually.of_forall fun k => (hIB k).aestronglyMeasurable) ?_
      ((integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hμK)) ?_
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 hχu 1 one_pos] with k hk
      filter_upwards [ae_restrict_mem hMmeas] with x hx
      by_cases hxK : x ∈ K
      · rw [indicator_of_mem hxK, norm_mul]
        have hΦx := hΦ x hxK
        have hkx := hk x hx
        rw [Real.dist_eq] at hkx
        rw [Real.norm_eq_abs] at hΦx ⊢
        have h1 : |χ k x| ≤ Φ + 1 := by
          have := abs_sub_abs_le_abs_sub (χ k x) (φ x)
          rw [abs_sub_comm] at this
          linarith
        exact mul_le_mul h1 (hL x hxK) (norm_nonneg _) (by linarith [abs_nonneg (φ x)])
      · rw [indicator_of_notMem hxK, hχK k x hx hxK, zero_mul, norm_zero]
    · filter_upwards [ae_restrict_mem hMmeas] with x hx
      exact (hχu.tendsto_at hx).mul_const _
  -- conclusion: `∫ Aₖ = −∫ χₖ Σⱼ δⱼ(δⱼf)` for every `k`; pass to the limit
  have hEq : ∫ x in M, (∑ j : Fin P, fderivWithin ℝ φ M x (Pr x (EuclideanSpace.single j 1)) *
      fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) ∂μHE[m] =
      -(∫ x in M, φ x * (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
        (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1))) ∂μHE[m]) := by
    have h1 : ∀ k, ∫ x in M, (∑ j : Fin P, fderiv ℝ (χ k) x (Pr x (EuclideanSpace.single j 1)) *
        fderivWithin ℝ f M x (Pr x (EuclideanSpace.single j 1))) ∂μHE[m] =
        -(∫ x in M, χ k x * (∑ j : Fin P, fderivWithin ℝ (fun y => fderivWithin ℝ f M y
          (Pr y (EuclideanSpace.single j 1))) M x (Pr x (EuclideanSpace.single j 1))) ∂μHE[m]) := by
      intro k
      have h := hIk k
      rw [integral_add (hIA k) (hIB k)] at h
      linarith
    exact tendsto_nhds_unique hTA ((tendsto_congr h1).2 hTB.neg)
  exact ⟨hIφA, hIφB, hEq⟩

/-- **Simons' Hardy-type inequality on a stable minimal hypercone** (Simon, Appendix B, proof of
B.2, inequalities (1)–(3)).  `P_x` is the orthogonal projection onto `T_xM`, `δ_j g(x)` the
tangential derivative `fderivWithin ℝ g M x (P_x e_j)`, `|A|²(x) = Σ_j |Dν(x)(P_x e_j)|²` and
`|A| = √|A|²`.  For `ψ` locally Lipschitz on `M` and vanishing on `M` off a compact `C ⊆ M`:
* `M = closure M \ {0}` is Borel; on `M`, `P_x = Π_{A₀} − ν(x) ⊗ ν(x)` (normal complement), so
  `|A|²` agrees on `M` with the `C²` function `Σ_j |Dν(Π_{A₀}e_j − (ν·e_j)ν)|²` on `O`, and
  `|A|` is the `ℓ²` norm of a `C¹` map, hence locally Lipschitz on `M`;
* by Rademacher, `ψ` and `|A|` are differentiable within `M` at a.e. point; there
  `δ_j(|A|ψ) = |A|δ_jψ + ψδ_j|A|`, `δ_jψ² = 2ψδ_jψ`, `δ_j|A|² = 2|A|δ_j|A|`, and `δ_j|A| = 0` where
  `|A| = 0` (`|A| ≥ 0` is minimal along tangent curves);  the Simons identity and the cone defect
  give `½Δ_M|A|² + |A|⁴ ≥ 2|A|²/|x|² + Σ_j(δ_j|A|)²` (B.2 (1)), hence a.e.
  `2Σ_j(δ_j(|A|ψ))² ≤ 2|A|²Σ_j(δ_jψ)² + ψ²Δ_M|A|² + 2ψ²|A|⁴ − 4ψ²|A|²/|x|² + Σ_jδ_jψ²δ_j|A|²`;
* every term on the right is integrable (`Σ_j(δ_jψ)² ∈ L¹` by the smooth approximations (HL)),
  stability with `ζ = |A|ψ` gives `∫|A|⁴ψ² ≤ ∫Σ_j(δ_j(|A|ψ))²` (B.2 (2)), and integration by parts
  gives `∫Σ_jδ_jψ²δ_j|A|² = −∫ψ²Δ_M|A|²`; combining, `2∫ψ²|A|²/|x|² ≤ ∫|A|²Σ_j(δ_jψ)²`
  (B.2 (3)). -/
theorem Submission.codim1_hcp_sc_simons_hardy_inequality : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → (0 : Euclid P) ∉ tsupport X → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → (∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * ζ x ^ 2 ∂μHE[m] ≤ ∫ x in M, ∑ j : Fin P, (fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m]) → ((∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → ∀ j : Fin P, AEStronglyMeasurable (fun x => fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) (μHE[m].restrict M)) ∧ ∀ (ζ : Euclid P → ℝ), LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∃ (C' : Set (Euclid P)) (ζs : ℕ → Euclid P → ℝ), IsCompact C' ∧ C' ⊆ M ∧ (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ζs k) ∧ HasCompactSupport (ζs k)) ∧ (∀ k, ∀ x ∈ M, x ∉ C' → ζs k x = 0) ∧ TendstoUniformlyOn ζs ζ atTop M ∧ Tendsto (fun k => ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderiv ℝ (ζs k) x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)) - fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m]) atTop (𝓝 0)) → ∀ ψ : Euclid P → ℝ, LocallyLipschitzOn M ψ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ψ x = 0) → 2 * (∫ x in M, ψ x ^ 2 * (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) / ‖x‖ ^ 2 ∂μHE[m]) ≤ ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * (∑ j : Fin P, (fderivWithin ℝ ψ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2) ∂μHE[m] := by
  intro P m A₀ M ν hA₀ hMA h0 hM hcl hcone hfin hstat hνO hν hH hstab hHL ψ hψ hψC
  obtain ⟨O, hO, hMO, hνC⟩ := hνO
  obtain ⟨C, hCc, hCM, hψ0⟩ := hψC
  -- `Pe x j = P_x e_j` and `A2 = |A|²`
  set Pe : Euclid P → Fin P → Euclid P := fun x j =>
    (Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1)
  set A2 : Euclid P → ℝ := fun z => ∑ i : Fin P, ‖fderiv ℝ ν z (Pe z i)‖ ^ 2
  have hA2nn : ∀ y, 0 ≤ A2 y := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmem : ∀ x j, Pe x j ∈ Submodule.span ℝ (tangentSpace M x) := fun x j =>
    Submodule.starProjection_apply_mem _ _
  -- Step 0(a): `M = closure M \ {0}` is Borel, and `μ⌞M (C) < ∞`
  have hMmeas : MeasurableSet M := by
    have hMeq : M = closure M \ {0} := by
      ext x
      refine ⟨fun hx => ⟨subset_closure hx, fun hx0 => h0 ?_⟩, fun hx => ?_⟩
      · rwa [Set.mem_singleton_iff.mp hx0] at hx
      · rcases Set.mem_insert_iff.mp (hcl hx.1) with hx' | hx'
        · exact absurd (Set.mem_singleton_iff.mpr hx') hx.2
        · exact hx'
    rw [hMeq]
    exact isClosed_closure.measurableSet.diff (measurableSet_singleton 0)
  have hCmeas : MeasurableSet C := hCc.isClosed.measurableSet
  have hμMC : (μHE[m].restrict M) C ≠ ∞ := by
    rw [Measure.restrict_apply hCmeas, Set.inter_eq_left.mpr hCM]
    have h := hfin C hCc
    rwa [Set.inter_eq_right.mpr hCM] at h
  -- integrability on `M` of a.e.-strongly measurable functions bounded on `C`, zero on `M \ C`
  have hint : ∀ g : Euclid P → ℝ, AEStronglyMeasurable g (μHE[m].restrict M) →
      (∃ B, ∀ x ∈ C, ‖g x‖ ≤ B) → (∀ x ∈ M, x ∉ C → g x = 0) →
      Integrable g (μHE[m].restrict M) := by
    rintro g hg ⟨B, hB⟩ hg0
    refine ((integrableOn_const (C := B) hμMC).integrable_indicator hCmeas).mono' hg ?_
    filter_upwards [ae_restrict_mem hMmeas] with x hx
    by_cases hxC : x ∈ C
    · rw [Set.indicator_of_mem hxC]
      exact hB x hxC
    · simp [Set.indicator_of_notMem hxC, hg0 x hx hxC]
  have hintc : ∀ g : Euclid P → ℝ, ContinuousOn g M → (∀ x ∈ M, x ∉ C → g x = 0) →
      Integrable g (μHE[m].restrict M) := fun g hg hg0 =>
    hint g (hg.aestronglyMeasurable hMmeas) (hCc.exists_bound_of_continuousOn (hg.mono hCM)) hg0
  -- Step 0(c2): tangential derivatives of functions vanishing on `M \ C` vanish there
  have hzero : ∀ g : Euclid P → ℝ, (∀ x ∈ M, x ∉ C → g x = 0) →
      ∀ x ∈ M, x ∉ C → fderivWithin ℝ g M x = 0 := by
    intro g hg x hx hxC
    have hloc : g =ᶠ[𝓝[M] x] fun _ => (0 : ℝ) := by
      filter_upwards [inter_mem_nhdsWithin M (hCc.isClosed.isOpen_compl.mem_nhds hxC)] with y hy
      exact hg y hy.1 hy.2
    rw [hloc.fderivWithin_eq (hg x hx hxC), fderivWithin_const_apply]
  -- products of locally Lipschitz real functions are locally Lipschitz
  have hprod : ∀ f g : Euclid P → ℝ, LocallyLipschitzOn M f → LocallyLipschitzOn M g →
      LocallyLipschitzOn M (fun y => f y * g y) := by
    intro f g hf hg x hx
    obtain ⟨Kf, t, ht, hKf⟩ := hf hx
    obtain ⟨Kg, u, hu, hKg⟩ := hg hx
    have hbf : ∀ᶠ y in 𝓝[M] x, ‖f y‖ < ‖f x‖ + 1 :=
      Filter.Tendsto.eventually (hf.continuousOn x hx).norm (gt_mem_nhds (lt_add_one _))
    have hbg : ∀ᶠ y in 𝓝[M] x, ‖g y‖ < ‖g x‖ + 1 :=
      Filter.Tendsto.eventually (hg.continuousOn x hx).norm (gt_mem_nhds (lt_add_one _))
    refine ⟨Real.toNNReal ((‖g x‖ + 1) * Kf + (‖f x‖ + 1) * Kg),
      t ∩ u ∩ {y | ‖f y‖ < ‖f x‖ + 1 ∧ ‖g y‖ < ‖g x‖ + 1},
      inter_mem (inter_mem ht hu) (hbf.and hbg), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    obtain ⟨⟨hyt, hyu⟩, hyf, -⟩ := hy
    obtain ⟨⟨hzt, hzu⟩, -, hzg⟩ := hz
    have h1 := hKf.dist_le_mul y hyt z hzt
    have h2 := hKg.dist_le_mul y hyu z hzu
    rw [Real.dist_eq] at h1 h2 ⊢
    have e : f y * g y - f z * g z = g z * (f y - f z) + f y * (g y - g z) := by ring
    calc |f y * g y - f z * g z| = |g z * (f y - f z) + f y * (g y - g z)| := by rw [e]
      _ ≤ |g z| * |f y - f z| + |f y| * |g y - g z| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ (‖g x‖ + 1) * (Kf * dist y z) + (‖f x‖ + 1) * (Kg * dist y z) := by
          rw [← Real.norm_eq_abs (g z), ← Real.norm_eq_abs (f y)]
          exact add_le_add (mul_le_mul hzg.le h1 (abs_nonneg _) (by positivity))
            (mul_le_mul hyf.le h2 (abs_nonneg _) (by positivity))
      _ = _ := by
          rw [Real.coe_toNNReal _ (by positivity)]
          ring
  -- Step 0(b): on `M`, `P_y = Π_{A₀} − ν(y) ⊗ ν(y)`; the `C²` extension of `|A|²` to `O`
  have hNC := Submission.codim1_hcp_sc_tangent_normal_complement P m A₀ M ν hA₀ hMA (hM 1) hν
  have hPeq : ∀ y ∈ M, ∀ i : Fin P, Pe y i = A₀.starProjection (EuclideanSpace.single i 1) -
      inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y := fun y hy i => (hNC y hy).2 _
  have hνc : ContDiffOn ℝ 2 ν O := contDiffOn_infty.1 hνC 2
  have hDν : ContDiffOn ℝ 2 (fun y => fderiv ℝ ν y) O :=
    (contDiffOn_infty.1 hνC 3).fderiv_of_isOpen hO (by norm_num)
  have hV : ∀ i : Fin P, ContDiffOn ℝ 2 (fun y => fderiv ℝ ν y
      (A₀.starProjection (EuclideanSpace.single i 1) -
        inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y)) O := fun i =>
    hDν.clm_apply (contDiffOn_const.sub ((hνc.inner ℝ contDiffOn_const).smul hνc))
  have hF : ContDiffOn ℝ 2 (fun y => ∑ i : Fin P, ‖fderiv ℝ ν y
      (A₀.starProjection (EuclideanSpace.single i 1) -
        inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y)‖ ^ 2) O :=
    ContDiffOn.sum fun i _ => (hV i).norm_sq ℝ
  have hAeq : ∀ y ∈ M, A2 y = ∑ i : Fin P, ‖fderiv ℝ ν y
      (A₀.starProjection (EuclideanSpace.single i 1) -
        inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y)‖ ^ 2 := fun y hy =>
    Finset.sum_congr rfl fun i _ => by rw [hPeq y hy i]
  have hAcont : ContinuousOn A2 M := (hF.continuousOn.mono hMO).congr fun y hy => hAeq y hy
  -- `|A| = √|A|²` is the `ℓ²` norm of a `C¹` map on `O`, hence locally Lipschitz on `M`
  have hsLip : LocallyLipschitzOn M (fun y => Real.sqrt (A2 y)) := by
    intro x hx
    have hW : ContDiffOn ℝ 2 (fun y => WithLp.toLp 2 (fun i : Fin P => fderiv ℝ ν y
        (A₀.starProjection (EuclideanSpace.single i 1) -
          inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y))) O :=
      PiLp.contDiff_toLp.comp_contDiffOn (contDiffOn_pi.mpr hV)
    obtain ⟨K, t, ht, hK⟩ :=
      ((hW.contDiffAt (hO.mem_nhds (hMO hx))).of_le (by norm_num)).exists_lipschitzOnWith
    refine ⟨K, t ∩ M, inter_mem (nhdsWithin_le_nhds ht) self_mem_nhdsWithin, ?_⟩
    have hnorm : ∀ y ∈ M, Real.sqrt (A2 y) = ‖WithLp.toLp 2 (fun i : Fin P => fderiv ℝ ν y
        (A₀.starProjection (EuclideanSpace.single i 1) -
          inner ℝ (ν y) (EuclideanSpace.single i 1) • ν y))‖ := fun y hy => by
      rw [PiLp.norm_eq_of_L2, hAeq y hy]
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    show dist (Real.sqrt (A2 y)) (Real.sqrt (A2 z)) ≤ K * dist y z
    rw [hnorm y hy.2, hnorm z hz.2]
    exact (dist_norm_norm_le _ _).trans ((dist_eq_norm _ _).symm.le.trans
      (hK.dist_le_mul y hy.1 z hz.1))
  have hψc : ContinuousOn ψ M := hψ.continuousOn
  have hζLip : LocallyLipschitzOn M (fun y => Real.sqrt (A2 y) * ψ y) := hprod _ _ hsLip hψ
  have hφLip : LocallyLipschitzOn M (fun y => ψ y ^ 2) := by
    simpa only [sq] using hprod ψ ψ hψ hψ
  have hζ0 : ∀ x ∈ M, x ∉ C → Real.sqrt (A2 x) * ψ x = 0 := fun x hx hxC => by
    rw [hψ0 x hx hxC, mul_zero]
  have hφ0 : ∀ x ∈ M, x ∉ C → ψ x ^ 2 = 0 := fun x hx hxC => by
    rw [hψ0 x hx hxC]
    ring
  -- Step 3 (integrability): `Σ_j (δ_jψ)²` is integrable, by the smooth approximations (HL)
  have hSint : Integrable (fun x => ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2)
      (μHE[m].restrict M) := by
    obtain ⟨C', ζs, -, -, hζs, -, -, hlim⟩ := hHL.2 ψ hψ ⟨C, hCc, hCM, hψ0⟩
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
    obtain ⟨B, hB⟩ := ((hζs k).1.continuous_fderiv (by simp)).bounded_above_of_compact_support
      ((hζs k).2.fderiv ℝ)
    have hsupp : IsCompact (tsupport (ζs k)) := (hζs k).2
    refine ⟨Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hHL.1 ψ hψ j).pow 2,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
        Finset.sum_nonneg fun j _ => sq_nonneg _)).mpr ?_⟩
    have h2mul : ∀ X : ℝ, ENNReal.ofReal (2 * X) = 2 * ENNReal.ofReal X := fun X => by
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    have hpt : ∀ x, ENNReal.ofReal (∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) ≤
        (tsupport (ζs k)).indicator (fun _ => ENNReal.ofReal (2 * P * B ^ 2)) x +
          2 * ENNReal.ofReal (∑ j : Fin P,
            (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2) := by
      intro x
      have h1 : ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2 ≤
          2 * ∑ j : Fin P, (fderiv ℝ (ζs k) x (Pe x j)) ^ 2 + 2 * ∑ j : Fin P,
            (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ => by
          nlinarith [sq_nonneg (2 * fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j))]
      have h2 : ENNReal.ofReal (2 * ∑ j : Fin P, (fderiv ℝ (ζs k) x (Pe x j)) ^ 2) ≤
          (tsupport (ζs k)).indicator (fun _ => ENNReal.ofReal (2 * P * B ^ 2)) x := by
        by_cases hx : x ∈ tsupport (ζs k)
        · rw [Set.indicator_of_mem hx]
          refine ENNReal.ofReal_le_ofReal ?_
          have hb : ∀ j, (fderiv ℝ (ζs k) x (Pe x j)) ^ 2 ≤ B ^ 2 := fun j => by
            have hPj : ‖Pe x j‖ ≤ 1 :=
              (Submodule.norm_starProjection_apply_le _ _).trans (by simp)
            have hle : |fderiv ℝ (ζs k) x (Pe x j)| ≤ B := by
              rw [← Real.norm_eq_abs]
              exact ((fderiv ℝ (ζs k) x).le_opNorm _).trans
                ((mul_le_mul (hB x) hPj (norm_nonneg _) ((norm_nonneg _).trans (hB x))).trans
                  (mul_one B).le)
            exact sq_le_sq' (abs_le.mp hle).1 (abs_le.mp hle).2
          have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hb j
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
          linarith
        · rw [Set.indicator_of_notMem hx, fderiv_of_notMem_tsupport ℝ hx]
          simp
      calc ENNReal.ofReal (∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2)
          ≤ ENNReal.ofReal (2 * ∑ j : Fin P, (fderiv ℝ (ζs k) x (Pe x j)) ^ 2 + 2 * ∑ j : Fin P,
              (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2) :=
            ENNReal.ofReal_le_ofReal h1
        _ = ENNReal.ofReal (2 * ∑ j : Fin P, (fderiv ℝ (ζs k) x (Pe x j)) ^ 2) +
              2 * ENNReal.ofReal (∑ j : Fin P,
                (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), h2mul (∑ j : Fin P,
              (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2)]
        _ ≤ _ := add_le_add h2 le_rfl
    calc ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) ∂μHE[m]
        ≤ ∫⁻ x in M, ((tsupport (ζs k)).indicator (fun _ => ENNReal.ofReal (2 * P * B ^ 2)) x +
          2 * ENNReal.ofReal (∑ j : Fin P,
            (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2)) ∂μHE[m] :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * P * B ^ 2) * (μHE[m].restrict M) (tsupport (ζs k)) +
          2 * ∫⁻ x in M, ENNReal.ofReal (∑ j : Fin P,
            (fderiv ℝ (ζs k) x (Pe x j) - fderivWithin ℝ ψ M x (Pe x j)) ^ 2) ∂μHE[m] := by
          rw [lintegral_add_left (measurable_const.indicator (isClosed_tsupport _).measurableSet),
            lintegral_indicator_const (isClosed_tsupport _).measurableSet,
            lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
      _ < ∞ := by
          refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_,
            ENNReal.mul_lt_top ENNReal.ofNat_lt_top (hk.trans ENNReal.one_lt_top)⟩
          rw [Measure.restrict_apply (isClosed_tsupport _).measurableSet, Set.inter_comm]
          exact (hfin _ hsupp).lt_top
  -- the integrands of the final combination
  have hxne : ∀ x ∈ M, ‖x‖ ^ 2 ≠ 0 := fun x hx =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr fun h => h0 (h ▸ hx))
  have hIa : Integrable (fun x => A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2)
      (μHE[m].restrict M) := by
    obtain ⟨B, hB⟩ := hCc.exists_bound_of_continuousOn (hAcont.mono hCM)
    refine (hSint.const_mul B).mono' ((hAcont.aestronglyMeasurable hMmeas).mul hSint.1) ?_
    filter_upwards [ae_restrict_mem hMmeas] with x hx
    have hS0 : 0 ≤ ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    by_cases hxC : x ∈ C
    · rw [norm_mul, Real.norm_of_nonneg hS0]
      exact mul_le_mul_of_nonneg_right (hB x hxC) hS0
    · have hS : ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2 = 0 := by
        simp [hzero ψ hψ0 x hx hxC]
      simp [hS]
  have hIe : Integrable (fun x => ψ x ^ 2 * A2 x ^ 2) (μHE[m].restrict M) :=
    hintc _ ((hψc.pow 2).mul (hAcont.pow 2)) fun x hx hxC => by simp [hψ0 x hx hxC]
  have hIf : Integrable (fun x => ψ x ^ 2 * A2 x / ‖x‖ ^ 2) (μHE[m].restrict M) :=
    hintc _ (((hψc.pow 2).mul hAcont).div (continuous_norm.pow 2).continuousOn hxne)
      fun x hx hxC => by simp [hψ0 x hx hxC]
  -- Step 4: integration by parts (stationary_ibp) with `φ = ψ²`, `f = |A|²`
  obtain ⟨hibp1, hibp2, hibp3⟩ :=
    Submission.codim1_hcp_sc_stationary_integration_by_parts P m A₀ M ν hA₀ hMA h0 (hM 1) hMmeas
      hfin hstat ⟨O, hO, hMO, hνC⟩ hν hHL A2 _ O hO hMO hF (fun y hy => (hAeq y hy).symm)
      (fun y => ψ y ^ 2) hφLip ⟨C, hCc, hCM, hφ0⟩
  have hIb : Integrable (fun x => ∑ j : Fin P, fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j) *
      fderivWithin ℝ A2 M x (Pe x j)) (μHE[m].restrict M) := hibp1
  have hId : Integrable (fun x => ψ x ^ 2 * ∑ j : Fin P,
      fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j))
      (μHE[m].restrict M) := hibp2
  have hIbd : ∫ x in M, (∑ j : Fin P, fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j) *
      fderivWithin ℝ A2 M x (Pe x j)) ∂μHE[m] = -(∫ x in M, ψ x ^ 2 * (∑ j : Fin P,
      fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j)) ∂μHE[m]) := hibp3
  -- the pointwise algebra of steps 1–2 (`a = |A|`, `p = ψ`, `L = Δ_M|A|²`, `N = |∇A|²`)
  have alg : ∀ (a p A N L r2 : ℝ) (u v w z1 z2 : Fin P → ℝ), A = a ^ 2 → 0 < r2 →
      L = 2 * N - 2 * A ^ 2 → 0 ≤ N →
      (0 < A → 2 * A ^ 2 / r2 + (∑ k, w k ^ 2) / 4 ≤ A * N) → (A = 0 → ∀ k, v k = 0) →
      (∀ j, w j = 2 * a * v j) → (∀ j, z1 j = a * u j + p * v j) → (∀ j, z2 j = 2 * p * u j) →
      2 * ∑ j, z1 j ^ 2 ≤ 2 * (A * ∑ j, u j ^ 2) + p ^ 2 * L + 2 * (p ^ 2 * A ^ 2) -
        4 * (p ^ 2 * A / r2) + ∑ j, z2 j * w j := by
    intro a p A N L r2 u v w z1 z2 hAa hr2 hL hN hcd hv0 hw hz1 hz2
    subst hAa hL
    simp only [hw, hz1, hz2] at hcd ⊢
    -- the pointwise Simons inequality (1): `2|A|²/r² + Σ_k (δ_k|A|)² ≤ |∇A|²`
    have hI : 2 * a ^ 2 / r2 + ∑ k, v k ^ 2 ≤ N := by
      rcases (sq_nonneg a).lt_or_eq with hA | hA
      · refine le_of_mul_le_mul_left ?_ hA
        have e : (∑ k, (2 * a * v k) ^ 2) / 4 = a ^ 2 * ∑ k, v k ^ 2 := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun k _ => by ring
        calc a ^ 2 * (2 * a ^ 2 / r2 + ∑ k, v k ^ 2)
            = 2 * (a ^ 2) ^ 2 / r2 + (∑ k, (2 * a * v k) ^ 2) / 4 := by rw [e]; ring
          _ ≤ a ^ 2 * N := hcd hA
      · have hv := hv0 hA.symm
        simp only [hv, ← hA]
        simpa using hN
    have e1 : ∑ j, (a * u j + p * v j) ^ 2 =
        a ^ 2 * ∑ j, u j ^ 2 + 2 * a * p * ∑ j, u j * v j + p ^ 2 * ∑ j, v j ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j, 2 * p * u j * (2 * a * v j) = 4 * a * p * ∑ j, u j * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have key : 2 * (a ^ 2 * ∑ j, u j ^ 2) + p ^ 2 * (2 * N - 2 * (a ^ 2) ^ 2) +
        2 * (p ^ 2 * (a ^ 2) ^ 2) - 4 * (p ^ 2 * a ^ 2 / r2) + 4 * a * p * ∑ j, u j * v j -
        2 * (a ^ 2 * ∑ j, u j ^ 2 + 2 * a * p * ∑ j, u j * v j + p ^ 2 * ∑ j, v j ^ 2) =
        2 * p ^ 2 * (N - (2 * a ^ 2 / r2 + ∑ k, v k ^ 2)) := by ring
    rw [e1, e2]
    linarith [key, mul_nonneg (mul_nonneg zero_le_two (sq_nonneg p)) (sub_nonneg.mpr hI)]
  -- Steps 1–2: the a.e. pointwise inequality
  have hSI := Submission.codim1_hcp_sc_simons_identity P m A₀ M ν hA₀ hMA hM ⟨O, hO, hMO, hνC⟩ hν hH
  have hCD := Submission.codim1_hcp_sc_cone_simons_defect P m A₀ M ν hA₀ hMA h0 hM hcone
    ⟨O, hO, hMO, hνC⟩ hν
  have hmin : ∀ (g : Euclid P → ℝ) (g' : Euclid P →L[ℝ] ℝ) (x : Euclid P), (∀ y, 0 ≤ g y) →
      g x = 0 → HasFDerivWithinAt g g' M x →
      ∀ w ∈ Submodule.span ℝ (tangentSpace M x), g' w = 0 := by
    intro g g' x hg hgx hd w hw
    have hT : tangentSpace M x ⊆ (LinearMap.ker (g' : Euclid P →ₗ[ℝ] ℝ) : Set (Euclid P)) := by
      rintro τ ⟨γ, -, hγM, hγ0, hγd⟩
      have h1 : HasDerivWithinAt (g ∘ γ) (g' τ) (Set.Ioo (-1) 1) 0 :=
        HasFDerivWithinAt.comp_hasDerivWithinAt (0 : ℝ) (by rw [hγ0]; exact hd)
          hγd.hasDerivWithinAt hγM
      have h2 : HasDerivAt (g ∘ γ) (g' τ) 0 :=
        h1.hasDerivAt (Ioo_mem_nhds (by norm_num) (by norm_num))
      have h3 : IsLocalMin (g ∘ γ) 0 := Eventually.of_forall fun t => by
        show g (γ 0) ≤ g (γ t)
        rw [hγ0, hgx]
        exact hg _
      exact LinearMap.mem_ker.mpr (h3.hasDerivAt_eq_zero h2)
    exact LinearMap.mem_ker.mp ((Submodule.span_le.mpr hT) hw)
  have hrad_ψ := Submission.codim1_hcp_sc_rademacher_submanifold P m M ψ (hM 1) hψ
  have hrad_s := Submission.codim1_hcp_sc_rademacher_submanifold P m M
    (fun y => Real.sqrt (A2 y)) (hM 1) hsLip
  have hpt : ∀ᵐ x ∂(μHE[m].restrict M),
      2 * ∑ j : Fin P, (fderivWithin ℝ (fun y => Real.sqrt (A2 y) * ψ y) M x (Pe x j)) ^ 2 ≤
        2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) +
          ψ x ^ 2 * ∑ j : Fin P,
            fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j) +
          2 * (ψ x ^ 2 * A2 x ^ 2) - 4 * (ψ x ^ 2 * A2 x / ‖x‖ ^ 2) +
          ∑ j : Fin P, fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j) *
            fderivWithin ℝ A2 M x (Pe x j) := by
    filter_upwards [ae_restrict_mem hMmeas, hrad_ψ, hrad_s] with x hx hψd hsd
    have hψd' := hψd.hasFDerivWithinAt
    have hsd' := hsd.hasFDerivWithinAt
    -- Step 1(a)–(c): product rules within `M` and `tangent_fderiv`
    have hζd : ∀ j, fderivWithin ℝ (fun y => Real.sqrt (A2 y) * ψ y) M x (Pe x j) =
        Real.sqrt (A2 x) * fderivWithin ℝ ψ M x (Pe x j) +
          ψ x * fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x (Pe x j) := fun j => by
      have hd : HasFDerivWithinAt (fun y => Real.sqrt (A2 y) * ψ y)
          (Real.sqrt (A2 x) • fderivWithin ℝ ψ M x +
            ψ x • fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x) M x := hsd'.mul hψd'
      rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hd (Pe x j) (hmem x j)]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have hφd : ∀ j, fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j) =
        2 * ψ x * fderivWithin ℝ ψ M x (Pe x j) := fun j => by
      have hd : HasFDerivWithinAt (fun y => ψ y ^ 2)
          (ψ x • fderivWithin ℝ ψ M x + ψ x • fderivWithin ℝ ψ M x) M x :=
        (hψd'.mul hψd').congr (fun y _ => sq (ψ y)) (sq (ψ x))
      rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hd (Pe x j) (hmem x j)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    have hAd : ∀ j, fderivWithin ℝ A2 M x (Pe x j) =
        2 * Real.sqrt (A2 x) * fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x (Pe x j) :=
      fun j => by
        have hd : HasFDerivWithinAt A2
            (Real.sqrt (A2 x) • fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x +
              Real.sqrt (A2 x) • fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x) M x :=
          (hsd'.mul hsd').congr (fun y _ => (Real.mul_self_sqrt (hA2nn y)).symm)
            (Real.mul_self_sqrt (hA2nn x)).symm
        rw [Submission.codim1_hcp_sc_fderivWithin_tangent_eq P ℝ M _ _ x hd (Pe x j) (hmem x j)]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
    -- Step 1(d): `δ_j|A| = 0` where `|A|² = 0`
    have hv0 : A2 x = 0 → ∀ k, fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x (Pe x k) = 0 :=
      fun hA k => hmin (fun y => Real.sqrt (A2 y)) _ x (fun y => Real.sqrt_nonneg _)
        (by simp only [hA, Real.sqrt_zero]) hsd' (Pe x k) (hmem x k)
    have hr2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr fun h => h0 (h ▸ hx)) 2
    exact alg (Real.sqrt (A2 x)) (ψ x) (A2 x) _ _ (‖x‖ ^ 2)
      (fun j => fderivWithin ℝ ψ M x (Pe x j))
      (fun j => fderivWithin ℝ (fun y => Real.sqrt (A2 y)) M x (Pe x j))
      (fun j => fderivWithin ℝ A2 M x (Pe x j))
      (fun j => fderivWithin ℝ (fun y => Real.sqrt (A2 y) * ψ y) M x (Pe x j))
      (fun j => fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j))
      (Real.sq_sqrt (hA2nn x)).symm hr2 (hSI x hx)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)
      (hCD x hx) hv0 hAd hζd hφd
  -- Step 3: stability with `ζ = |A|ψ` (B.2 (2)), where `|A|²ζ² = ψ²|A|⁴`
  have hstabζ : ∫ x in M, ψ x ^ 2 * A2 x ^ 2 ∂μHE[m] ≤
      ∫ x in M, ∑ j : Fin P,
        (fderivWithin ℝ (fun y => Real.sqrt (A2 y) * ψ y) M x (Pe x j)) ^ 2 ∂μHE[m] := by
    have h := hstab _ hζLip ⟨C, hCc, hCM, hζ0⟩
    have e : ∫ x in M, ψ x ^ 2 * A2 x ^ 2 ∂μHE[m] =
        ∫ x in M, A2 x * (Real.sqrt (A2 x) * ψ x) ^ 2 ∂μHE[m] := by
      congr 1
      funext x
      rw [mul_pow, Real.sq_sqrt (hA2nn x)]
      ring
    rw [e]
    exact h
  -- Step 5: integrate the pointwise inequality and combine (B.2 (3))
  have i1 : Integrable (fun x => 2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2))
      (μHE[m].restrict M) := hIa.const_mul 2
  have i2 : Integrable (fun x => 2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) +
      ψ x ^ 2 * ∑ j : Fin P,
        fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j))
      (μHE[m].restrict M) := i1.add hId
  have i3 : Integrable (fun x => 2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) +
      ψ x ^ 2 * ∑ j : Fin P,
        fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j) +
      2 * (ψ x ^ 2 * A2 x ^ 2)) (μHE[m].restrict M) := i2.add (hIe.const_mul 2)
  have i4 : Integrable (fun x => 2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) +
      ψ x ^ 2 * ∑ j : Fin P,
        fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j) +
      2 * (ψ x ^ 2 * A2 x ^ 2) - 4 * (ψ x ^ 2 * A2 x / ‖x‖ ^ 2)) (μHE[m].restrict M) :=
    i3.sub (hIf.const_mul 4)
  have hmono : ∫ x in M, 2 * ∑ j : Fin P,
        (fderivWithin ℝ (fun y => Real.sqrt (A2 y) * ψ y) M x (Pe x j)) ^ 2 ∂μHE[m] ≤
      ∫ x in M, (2 * (A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2) +
          ψ x ^ 2 * ∑ j : Fin P,
            fderivWithin ℝ (fun y => fderivWithin ℝ A2 M y (Pe y j)) M x (Pe x j) +
          2 * (ψ x ^ 2 * A2 x ^ 2) - 4 * (ψ x ^ 2 * A2 x / ‖x‖ ^ 2) +
          ∑ j : Fin P, fderivWithin ℝ (fun y => ψ y ^ 2) M x (Pe x j) *
            fderivWithin ℝ A2 M x (Pe x j)) ∂μHE[m] :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg zero_le_two
      (Finset.sum_nonneg fun j _ => sq_nonneg _)) (i4.add hIb) hpt
  rw [integral_add i4 hIb, integral_sub i3 (hIf.const_mul 4), integral_add i2 (hIe.const_mul 2),
    integral_add i1 hId, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, hIbd] at hmono
  show 2 * (∫ x in M, ψ x ^ 2 * A2 x / ‖x‖ ^ 2 ∂μHE[m]) ≤
    ∫ x in M, A2 x * ∑ j : Fin P, (fderivWithin ℝ ψ M x (Pe x j)) ^ 2 ∂μHE[m]
  linarith
/-- **Simons' theorem for smooth stable minimal hypercones** (Simon, Appendix B, Theorem B.2 for
smooth cones, `2 ≤ m ≤ 6`).  Let `M ⊆ A₀`, `dim A₀ = m + 1`, be a smooth embedded `m`-dimensional
cone with `0 ∉ M` and `closure M ⊆ M ∪ {0}`, of locally finite `Hᵐ`-measure and stationary away
from `0`, with smooth unit normal `ν` in `A₀`, zero mean curvature `trace(Pₓ ∘ Dν(x)) = 0`, and
stable in the sense of B.1.  Then `Dν(x)v = 0` for `x ∈ M` and `v ∈ TₓM`: the second fundamental
form vanishes.  As in the printed proof of B.2, Simons' identity B.8 and Lemma B.11 give
(1) `½Δ_M|A|² + |A|⁴ ≥ 2|x|⁻²|A|² + |∇^M|A||²`; B.1 with `ζ = |A|ψ`, integration by parts on `M`
(smooth approximation of Lipschitz functions on `M`) and (1) give
(3) `2∫_M ψ²|A|²|x|⁻² ≤ ∫_M |A|²|∇^Mψ|²` for locally Lipschitz `ψ` vanishing off a compact subset
of `M`.  Cut-offs and `ψ = r^{1+ε} max(1, r)^{1−m/2−2ε}`, `ε = 1/10`, whose integrals are finite
by dyadic scaling of `Hᵐ` on the cone, give `|A| = 0` `Hᵐ`-a.e. on `M`, hence everywhere, since
`Hᵐ⌞M` has density one at every point of `M`. -/
theorem Submission.codim1_hcp_stable_minimal_cone_flat : ∀ (P m : ℕ) (A₀ : Submodule ℝ (Euclid P)) (M : Set (Euclid P)) (ν : Euclid P → Euclid P), 2 ≤ m → m ≤ 6 → Module.finrank ℝ A₀ = m + 1 → M ⊆ (A₀ : Set (Euclid P)) → (0 : Euclid P) ∉ M → (∀ r : ℕ, IsEmbeddedSubmanifold r m M) → closure M ⊆ insert 0 M → (∀ t : ℝ, 0 < t → ∀ x ∈ M, t • x ∈ M) → (∀ K : Set (Euclid P), IsCompact K → μHE[m] (M ∩ K) ≠ ∞) → (∀ X : Euclid P → Euclid P, ContDiff ℝ 1 X → HasCompactSupport X → (0 : Euclid P) ∉ tsupport X → ∫ x in M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ X x).toLinearMap) ∂μHE[m] = 0) → (∃ O : Set (Euclid P), IsOpen O ∧ M ⊆ O ∧ ContDiffOn ℝ (⊤ : ℕ∞) ν O) → (∀ x ∈ M, ν x ∈ A₀ ∧ ‖ν x‖ = 1 ∧ ∀ v ∈ tangentSpace M x, inner ℝ (ν x) v = 0) → (∀ x ∈ M, LinearMap.trace ℝ (Euclid P) ((Submodule.span ℝ (tangentSpace M x)).starProjection.toLinearMap ∘ₗ (fderiv ℝ ν x).toLinearMap) = 0) → (∀ ζ : Euclid P → ℝ, LocallyLipschitzOn M ζ → (∃ C : Set (Euclid P), IsCompact C ∧ C ⊆ M ∧ ∀ x ∈ M, x ∉ C → ζ x = 0) → ∫ x in M, (∑ j : Fin P, ‖fderiv ℝ ν x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))‖ ^ 2) * ζ x ^ 2 ∂μHE[m] ≤ ∫ x in M, ∑ j : Fin P, (fderivWithin ℝ ζ M x ((Submodule.span ℝ (tangentSpace M x)).starProjection (EuclideanSpace.single j 1))) ^ 2 ∂μHE[m]) → ∀ x ∈ M, ∀ v ∈ tangentSpace M x, fderiv ℝ ν x v = 0 := by
  intro P m A₀ M ν hm2 hm6 hdim hMA h0 hM hcl hcone hfin hstat hνO hν hH hstab
  -- smooth approximation of locally Lipschitz functions on the embedded `C¹` submanifold `M`
  have hL := Submission.codim1_hcp_lipschitz_smooth_approx P m M (hM 1)
  -- (3): Simons' inequality (1) (B.8, B.11), stability B.1 for `ζ = |A|ψ`, integration by parts
  have h3 := Submission.codim1_hcp_sc_simons_hardy_inequality P m A₀ M ν hdim hMA h0 hM hcl
    hcone hfin hstat hνO hν hH hstab hL
  -- (3) with cut-offs and `ψ = r^{1+ε} max(1, r)^{1−m/2−2ε}` gives `|A| = 0` a.e. on `M`, hence
  -- everywhere by density one of `Hᵐ⌞M`
  exact Submission.codim1_hcp_sc_hardy_cone_flat P m A₀ M ν hm2 hm6 hdim hMA h0 hM hcl hcone
    hfin hνO hν (fun z hz => Submission.dimred_rpd_submanifold_density_one P m M z (hM 1) hz) h3

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
