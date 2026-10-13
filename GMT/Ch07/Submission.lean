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

/-- **Mass upper bound from a representation by a unit-bounded multivector field** (Simon
6.2.5; step 10 of the representation `T = μ_T ∧ ξ⃗`).  Suppose `|⟨α, ξ(x)⟩| ≤ |α|_E` for all `x`
and all covectors `α` (`|·|_E` is `covectorEuclideanNorm`), and `T(ω) = ∫ ⟨ω(x), ξ(x)⟩ dμ(x)`
for every test form `ω`.  Then `M_W(T) ≤ μ(W)` for every set `W`.  Fix an admissible `ω`, i.e.
`tsupport ω ⊆ W` and `|ω|_E ≤ 1`, and let `K = tsupport ω` (closed, hence Borel) and
`f(x) = ⟨ω(x), ξ(x)⟩`.  Then `|f| ≤ |ω|_E ≤ 1` on `K` and `f = 0` off `K`, so
`T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ ∫⁻ 1_K dμ = μ(K) ≤ μ(W)`; the middle inequality holds whether
or not `f` is integrable.  Taking the supremum over admissible `ω` gives `M_W(T) ≤ μ(W)`. -/
theorem Submission.cmrc_massOn_le_of_repr : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n), (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → ∀ W : Set (Euclid P), T.massOn W ≤ μ W := by
  intro P n U T μ ξ hξ hT W
  -- Step 1: it suffices to bound `ofReal (T ω)` for each admissible `ω`
  refine sSup_le ?_
  rintro r ⟨ω, hω, rfl⟩
  set K : Set (Euclid P) := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  -- Step 2: `‖⟨ω(x), ξ(x)⟩‖ₑ ≤ 1_K(x)` for every `x`
  have hpt : ∀ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ≤ K.indicator 1 x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, Pi.one_apply, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((hξ x _).trans (hω.2 x))
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, map_zero, enorm_zero]
  -- Step 3: `T(ω) ≤ ‖∫ f dμ‖ₑ ≤ ∫⁻ ‖f‖ₑ dμ ≤ μ(K) ≤ μ(W)`
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) := by rw [hT ω]
    _ ≤ ‖∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x, ‖ξ x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, K.indicator 1 x ∂μ := lintegral_mono hpt
    _ = μ K := lintegral_indicator_one hKm
    _ ≤ μ W := measure_mono hω.1
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
/-- **A smooth cut-off in `V` that equals `1` off a set of small measure** (smooth cut-off step
of the approximation of the mass of `τ(M, θ, ξ)` by test forms).  `ν` is finite, so it is inner
regular by compact sets: there is a compact `K ⊆ V` with `ν(V \ K) < δ`.  Choose an open `V₀`
with `K ⊆ V₀` and `closure V₀` compact and contained in `V`.  The smooth Urysohn lemma gives a
`C^∞` function `χ` with values in `[0, 1]`, `support χ = V₀` and `χ = 1` exactly on `K`.  Then
`tsupport χ = closure V₀` is compact and contained in `V`, and
`ν{χ ≠ 1} = ν(Kᶜ) ≤ ν(Vᶜ) + ν(V \ K) = ν(V \ K) < δ`. -/
theorem Submission.rsd_mw_tfa_smooth_cutoff : ∀ (P : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → ∀ δ : ℝ, 0 < δ → ∃ χ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ν {x | χ x ≠ 1} < ENNReal.ofReal δ := by
  intro P ν V hν hV hVc δ hδ
  -- Step 1: a compact core `K ⊆ V` with `ν (V \ K) < δ`, by inner regularity of finite `ν`
  obtain ⟨K, hKV, hKc, hVK⟩ := hV.measurableSet.exists_isCompact_sdiff_lt (measure_ne_top ν V)
    (ENNReal.ofReal_pos.mpr hδ).ne'
  -- Step 2: an open `V₀ ⊇ K` whose closure is compact and contained in `V`
  obtain ⟨V₀, hV₀o, hKV₀, hV₀V, hV₀c⟩ := exists_open_between_and_isCompact_closure hKc hV hKV
  -- Step 3: smooth Urysohn: `χ` is `C^∞`, `[0, 1]`-valued, `support χ = V₀`, `χ = 1` exactly on `K`
  obtain ⟨χ, hχ, hχr, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hV₀o hKc.isClosed hKV₀
  -- Step 4: `tsupport χ = closure V₀`
  have hts : tsupport χ = closure V₀ := by rw [tsupport, hχs]
  refine ⟨χ, hχ, ?_, hts ▸ hV₀V, fun x => hχr (mem_range_self x), ?_⟩
  · rw [HasCompactSupport, hts]
    exact hV₀c
  -- Step 5: `{χ ≠ 1} = Kᶜ ⊆ Vᶜ ∪ (V \ K)` and `ν Vᶜ = 0`
  have hset : {x | χ x ≠ 1} = Kᶜ := by
    ext x
    exact (hχ1 x).not.symm
  calc ν {x | χ x ≠ 1} = ν Kᶜ := by rw [hset]
    _ ≤ ν (Vᶜ ∪ V \ K) := measure_mono fun x hx => by
        by_cases h : x ∈ V
        · exact Or.inr ⟨h, hx⟩
        · exact Or.inl h
    _ ≤ ν Vᶜ + ν (V \ K) := measure_union_le _ _
    _ = ν (V \ K) := by rw [hVc, zero_add]
    _ < ENNReal.ofReal δ := hVK

/-- **Radial retraction onto the unit ball of `N = covectorEuclideanNorm`** (step 4 of the
approximation of a unit covector field by admissible test forms, used for Simon Ch. 6,
Remark 3.2(3)).  `ρ(a) = max(1, N(a))⁻¹ a` is continuous, `ρ(0) = 0`, `N(ρ(a)) ≤ 1`, and
`N(ρ(a) − b) ≤ 2 N(a − b)` whenever `N(b) ≤ 1`: if `N(a) > 1` then
`N(a − ρ(a)) = N(a) − 1 ≤ N(a − b)`, and the triangle inequality gives the factor `2`. -/
theorem Submission.rsd_mw_tfa_retraction : ∀ (P n : ℕ), ∃ ρ : Covector (Euclid P) n → Covector (Euclid P) n, Continuous ρ ∧ ρ 0 = 0 ∧ (∀ a, covectorEuclideanNorm (ρ a) ≤ 1) ∧ ∀ a b, covectorEuclideanNorm b ≤ 1 → covectorEuclideanNorm (ρ a - b) ≤ 2 * covectorEuclideanNorm (a - b) := by
  intro P n
  obtain ⟨htri, hsmul, -, hcont⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- the rescaling factor `max 1 (N a) ≥ 1` never vanishes
  have hpos : ∀ a : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm a) :=
    fun a => one_pos.trans_le (le_max_left _ _)
  refine ⟨fun a => (max 1 (covectorEuclideanNorm a))⁻¹ • a,
    ((continuous_const.max hcont).inv₀ fun a => (hpos a).ne').smul continuous_id, by simp,
    fun a => ?_, fun a b hb => ?_⟩
  · -- `N (ρ a) = N a / max 1 (N a) ≤ 1`
    dsimp only
    rw [hsmul, abs_of_pos (inv_pos.mpr (hpos a)), inv_mul_le_iff₀ (hpos a), mul_one]
    exact le_max_right _ _
  dsimp only
  rcases le_or_gt (covectorEuclideanNorm a) 1 with ha | ha
  · -- `N a ≤ 1`: `ρ a = a`
    rw [max_eq_left ha, inv_one, one_smul]
    linarith [covectorEuclideanNorm_nonneg (a - b)]
  -- `r := N a > 1`: `ρ a = r⁻¹ a`
  set r := covectorEuclideanNorm a with hr
  rw [max_eq_right ha.le]
  -- `N (a - ρ a) = (1 - r⁻¹) r = r - 1`
  have h₁ : covectorEuclideanNorm (a - r⁻¹ • a) = r - 1 := by
    rw [show a - r⁻¹ • a = (1 - r⁻¹) • a by module, hsmul,
      abs_of_nonneg (sub_nonneg.mpr (inv_le_one_of_one_le₀ ha.le)), sub_mul, one_mul, ← hr,
      inv_mul_cancel₀ (one_pos.trans ha).ne']
  -- `r ≤ N (a - b) + N b ≤ N (a - b) + 1`
  have h₂ : r ≤ covectorEuclideanNorm (a - b) + 1 :=
    calc r = covectorEuclideanNorm (a - b + b) := by rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (a - b) + covectorEuclideanNorm b := htri _ _
      _ ≤ covectorEuclideanNorm (a - b) + 1 := by linarith
  calc covectorEuclideanNorm (r⁻¹ • a - b)
      = covectorEuclideanNorm (-(a - r⁻¹ • a) + (a - b)) := by congr 1; abel
    _ ≤ covectorEuclideanNorm (-(a - r⁻¹ • a)) + covectorEuclideanNorm (a - b) := htri _ _
    _ = r - 1 + covectorEuclideanNorm (a - b) := by rw [covectorEuclideanNorm_neg, h₁]
    _ ≤ 2 * covectorEuclideanNorm (a - b) := by linarith

/-- **`L¹(ν)` approximation of a unit covector field by continuous compactly supported unit
fields** (steps 3–4 of the `L¹(ν)` approximation of a unit covector field by admissible test
forms).  Let `ν` be a finite Borel measure on `ℝᴾ` and `β` a `ν`-integrable `n`-covector field
with `N(β) ≤ 1` `ν`-a.e., `N = covectorEuclideanNorm`.  Continuous compactly supported maps are
dense in `L¹(ν)` (`ν` is regular), so one of them, `g₀`, has `∫ ‖β − g₀‖ dν ≤ η`.  With `ρ` the
retraction onto `{N ≤ 1}`, `g = ρ ∘ g₀` is continuous, compactly supported (`ρ 0 = 0`), has
`N(g) ≤ 1`, and `N(g − β) ≤ 2 N(g₀ − β) ≤ 2C ‖β − g₀‖` a.e., so `∫ N(g − β) dν ≤ 2Cη < δ`. -/
theorem Submission.rsd_mw_tfa_continuous_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g x - β x)) ∂ν < ENNReal.ofReal δ := by
  intro P n ν β hν hβ hβ1 δ hδ
  -- Step 1: the constant `C` of `norm_props` (iii), the retraction `ρ`, and the tolerance `η`
  obtain ⟨-, -, ⟨C, hC0, hC⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  obtain ⟨ρ, hρc, hρ0, hρ1, hρ2⟩ := Submission.rsd_mw_tfa_retraction P n
  set η : ℝ := δ / (2 * (2 * C + 1)) with hη
  have hη0 : 0 < η := by positivity
  -- Step 2: continuous compactly supported maps are dense in `L¹(ν)` (`ν` is finite, hence
  -- regular).  The contract does not import `Integrable.exists_hasCompactSupport_lintegral_sub_le`,
  -- so this goes through `MemLp.induction_dense`: `c • 1_s` is approximated by `φ • c`, with `φ`
  -- a Urysohn function for compact `K ⊆ s ⊆ U` open, `ν (U \ K)` small.
  have hind : ∀ (c : Covector (Euclid P) n) ⦃s : Set (Euclid P)⦄, MeasurableSet s → ν s < ∞ →
      ∀ {ε : ℝ≥0∞}, ε ≠ 0 → ∃ g : Euclid P → Covector (Euclid P) n,
        eLpNorm (g - s.indicator fun _ => c) 1 ν ≤ ε ∧ (Continuous g ∧ HasCompactSupport g) := by
    intro c s hs hsν ε hε
    obtain ⟨t, ht0, htε⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (a := 2 * ‖c‖ₑ)
        (ENNReal.mul_ne_top ENNReal.ofNat_ne_top enorm_ne_top) hε
    have ht : (t : ℝ≥0∞) ≠ 0 := by exact_mod_cast ht0.ne'
    -- compact `K ⊆ s ⊆ U` open with `ν (s \ K) < t` and `ν (U \ s) < t`
    obtain ⟨K, hKs, hK, hsK⟩ := hs.exists_isCompact_sdiff_lt hsν.ne ht
    obtain ⟨U, hsU, hU, -, hUs⟩ := hs.exists_isOpen_sdiff_lt hsν.ne ht
    -- Urysohn: `φ = 1` on `K`, `φ = 0` off `U`, `0 ≤ φ ≤ 1`, compact support
    obtain ⟨φ, hφK, hφU, hφs, hφ01⟩ := exists_continuous_one_zero_of_isCompact hK hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hKs.trans hsU))
    have hgc : Continuous fun x => φ x • c := φ.continuous.smul continuous_const
    refine ⟨fun x => φ x • c, ?_, hgc, hφs.smul_right⟩
    -- pointwise `‖φ x • c - 1_s(x) c‖ₑ ≤ 1_{U \ K}(x) ‖c‖ₑ`
    have hle : ∀ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ≤
        (U \ K).indicator (fun _ => ‖c‖ₑ) x := by
      intro x
      rw [← ofReal_norm]
      by_cases hxK : x ∈ K
      · simp [hφK hxK, hKs hxK]
      by_cases hxU : x ∈ U
      · rw [indicator_of_mem (mem_sdiff_of_mem hxU hxK), ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        obtain ⟨h0, h1⟩ := hφ01 x
        by_cases hxs : x ∈ s
        · rw [Pi.sub_apply, indicator_of_mem hxs, show φ x • c - c = (φ x - 1) • c by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
          nlinarith [norm_nonneg c]
        · rw [Pi.sub_apply, indicator_of_notMem hxs, sub_zero, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg h0]
          nlinarith [norm_nonneg c]
      · simp [hφU hxU, show x ∉ s from fun h => hxU (hsU h), hxU]
    rw [eLpNorm_one_eq_lintegral_enorm
      (hgc.aestronglyMeasurable.sub (stronglyMeasurable_const.indicator hs).aestronglyMeasurable)]
    calc ∫⁻ x, ‖((fun x => φ x • c) - s.indicator fun _ => c) x‖ₑ ∂ν
        ≤ ∫⁻ x, (U \ K).indicator (fun _ => ‖c‖ₑ) x ∂ν := lintegral_mono hle
      _ = ‖c‖ₑ * ν (U \ K) := lintegral_indicator_const (hU.measurableSet.diff hK.measurableSet) _
      _ ≤ ‖c‖ₑ * (ν (U \ s) + ν (s \ K)) := by
          gcongr
          refine (measure_mono fun x hx => ?_).trans (measure_union_le (U \ s) (s \ K))
          by_cases hxs : x ∈ s
          · exact Or.inr ⟨hxs, hx.2⟩
          · exact Or.inl ⟨hx.1, hxs⟩
      _ ≤ ‖c‖ₑ * (t + t) := by gcongr
      _ = t * (2 * ‖c‖ₑ) := by ring
      _ ≤ ε := htε.le
  -- the density statement for `β`, with tolerance `η`
  obtain ⟨g₀, hg₀, hg₀c, hg₀s⟩ := (memLp_one_iff_integrable.2 hβ).induction_dense
    ENNReal.one_ne_top (fun g => Continuous g ∧ HasCompactSupport g) hind
    (fun f g hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩) (ENNReal.ofReal_pos.mpr hη0).ne'
  rw [eLpNorm_one_eq_lintegral_enorm (hβ.aestronglyMeasurable.sub hg₀c.aestronglyMeasurable)] at hg₀
  -- Step 3: `g := ρ ∘ g₀`
  refine ⟨ρ ∘ g₀, hρc.comp hg₀c, hg₀s.comp_left hρ0, fun x => hρ1 _, ?_⟩
  -- Step 4: pointwise a.e. estimate
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x))
      ≤ ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ := by
    filter_upwards [hβ1] with x hx
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc covectorEuclideanNorm ((ρ ∘ g₀) x - β x)
        ≤ 2 * covectorEuclideanNorm (g₀ x - β x) := hρ2 _ _ hx
      _ ≤ 2 * (C * ‖g₀ x - β x‖) := by gcongr; exact hC _
      _ = 2 * C * ‖β x - g₀ x‖ := by rw [norm_sub_rev]; ring
  -- Step 5: integration
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm ((ρ ∘ g₀) x - β x)) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal (2 * C) * ‖β x - g₀ x‖ₑ ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * C) * ∫⁻ x, ‖β x - g₀ x‖ₑ ∂ν :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * C) * ENNReal.ofReal η := by gcongr; exact hg₀
    _ = ENNReal.ofReal (2 * C * η) := (ENNReal.ofReal_mul (by positivity)).symm
    -- Step 6: arithmetic
    _ < ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_lt_ofReal_iff hδ, hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

/-- **Smooth uniform approximation keeping the unit bound** (smoothing step in the proof of
`M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is `covectorEuclideanNorm`).  Let
`η := δ/(2C + 1)`, where `|·|_E ≤ C‖·‖` (`Submission.rsd_mw_tfa_norm_props`).  A continuous
compactly supported covector field `g` with `|g|_E ≤ 1` is uniformly continuous, so
`‖g y − g x‖ < η` when `dist y x < r`.  Mollifying, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth
bump `φ ≥ 0` with `support φ = B_r(0)` is a `C^∞` field with `‖h' − g‖ ≤ η`; then
`|h' − g|_E ≤ Cη` and `|h'|_E ≤ 1 + Cη`.  The rescaled field `h = (1 + Cη)⁻¹h'` has `|h|_E ≤ 1`
and `|h − h'|_E = Cη(1 + Cη)⁻¹|h'|_E ≤ Cη`, hence `|h − g|_E ≤ 2Cη ≤ δ`. -/
theorem Submission.rsd_mw_tfa_smooth_uniform_approx : ∀ (P n : ℕ) (g : Euclid P → Covector (Euclid P) n), Continuous g → HasCompactSupport g → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → ∀ δ : ℝ, 0 < δ → ∃ h : Euclid P → Covector (Euclid P) n, ContDiff ℝ (⊤ : ℕ∞) h ∧ (∀ x, covectorEuclideanNorm (h x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (h x - g x) ≤ δ := by
  intro P n g hgc hgs hg1 δ hδ
  -- `N := covectorEuclideanNorm` is subadditive, absolutely homogeneous and `N ≤ C ‖·‖`
  obtain ⟨htri, hsmul, ⟨C, hC0, hCle⟩, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: the tolerance `η = δ / (2C + 1)`
  set η : ℝ := δ / (2 * C + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hCη : 0 ≤ C * η := mul_nonneg hC0 hη0.le
  -- Step 2: `g` is uniformly continuous: `‖g y - g x‖ < η` whenever `dist y x < r`
  obtain ⟨r, hr, hgr⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) η hη0
  -- Step 3: mollify, `h' = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ`, `support φ = B_r(0)`
  let φ : ContDiffBump (0 : Euclid P) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hr
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 r := hψφ.trans φ.support_eq.subset
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  obtain ⟨h', hh's, hh'g⟩ : ∃ h' : Euclid P → Covector (Euclid P) n,
      ContDiff ℝ (⊤ : ℕ∞) h' ∧ ∀ x, dist (h' x) (g x) ≤ η :=
    ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume,
      (φ.hasCompactSupport.mono hψφ).contDiff_convolution_left _ (φ.contDiff.div_const _)
        hgc.locallyIntegrable,
      fun x => dist_convolution_le hη0.le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgr (mem_ball.mp hy)).le⟩
  -- Step 4: `N(h' - g) ≤ Cη` and `N(h') ≤ 1 + Cη`
  have hdiff : ∀ x, covectorEuclideanNorm (h' x - g x) ≤ C * η := fun x =>
    (hCle _).trans (mul_le_mul_of_nonneg_left (by rw [← dist_eq_norm]; exact hh'g x) hC0)
  have hh'1 : ∀ x, covectorEuclideanNorm (h' x) ≤ 1 + C * η := fun x =>
    calc covectorEuclideanNorm (h' x) = covectorEuclideanNorm ((h' x - g x) + g x) := by
          rw [sub_add_cancel]
      _ ≤ covectorEuclideanNorm (h' x - g x) + covectorEuclideanNorm (g x) := htri _ _
      _ ≤ C * η + 1 := add_le_add (hdiff x) (hg1 x)
      _ = 1 + C * η := add_comm _ _
  -- Step 5: rescale by `s = (1 + Cη)⁻¹ ∈ (0, 1]`
  have hpos : 0 < 1 + C * η := by linarith
  have hne : 1 + C * η ≠ 0 := hpos.ne'
  set s : ℝ := (1 + C * η)⁻¹ with hs
  have hs0 : 0 < s := inv_pos.mpr hpos
  refine ⟨fun x => s • h' x, hh's.const_smul s, fun x => ?_, fun x => ?_⟩
  · show covectorEuclideanNorm (s • h' x) ≤ 1
    rw [hsmul, abs_of_pos hs0, hs, inv_mul_le_iff₀ hpos, mul_one]
    exact hh'1 x
  · show covectorEuclideanNorm (s • h' x - g x) ≤ δ
    -- Step 6: `N(s h' - h') = |s - 1| N(h') = Cη s N(h') ≤ Cη`
    have hsh : s • h' x - h' x = (s - 1) • h' x := by module
    have hs1 : |s - 1| = C * η * s := by
      have hle : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      rw [abs_of_nonpos (by linarith), hs]
      field_simp
      ring
    have h6 : covectorEuclideanNorm (s • h' x - h' x) ≤ C * η := by
      rw [hsh, hsmul, hs1]
      calc C * η * s * covectorEuclideanNorm (h' x) ≤ C * η * s * (1 + C * η) :=
            mul_le_mul_of_nonneg_left (hh'1 x) (mul_nonneg hCη hs0.le)
        _ = C * η := by rw [hs]; field_simp
    -- Step 7: `N(s h' - g) ≤ N(s h' - h') + N(h' - g) ≤ 2Cη ≤ δ`
    calc covectorEuclideanNorm (s • h' x - g x)
        = covectorEuclideanNorm ((s • h' x - h' x) + (h' x - g x)) := by
          rw [sub_add_sub_cancel]
      _ ≤ covectorEuclideanNorm (s • h' x - h' x) + covectorEuclideanNorm (h' x - g x) :=
          htri _ _
      _ ≤ C * η + C * η := add_le_add h6 (hdiff x)
      _ ≤ δ := by
          have h2 : 0 < 2 * C + 1 := by linarith
          have h2C : C * η + C * η = 2 * C * δ / (2 * C + 1) := by rw [hη]; ring
          rw [h2C, div_le_iff₀ h2]
          nlinarith

/-- **Test forms approximating a unit-bounded integrable covector field in `L¹(ν)`** (the
approximation behind `M_W(T) = ∫_{M ∩ W} θ dHⁿ`, Simon 6.3.2(3); `|·|_E` is
`covectorEuclideanNorm`).  Let `m = ν(ℝᴾ)` and `δ = ε/(4(m + 1))`.  The smooth cut-off `χ` of
`Submission.rsd_mw_tfa_smooth_cutoff` satisfies `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`.  The
continuous field `g₁` of `Submission.rsd_mw_tfa_continuous_approx` satisfies `|g₁|_E ≤ 1` and
`∫ |g₁ − β|_E dν < ε/4`.  Its smoothing `g₂` (`Submission.rsd_mw_tfa_smooth_uniform_approx`)
satisfies `|g₂|_E ≤ 1` and `|g₂ − g₁|_E ≤ δ`.  Then `ω = χ g₂` is a test form, `tsupport ω ⊆ V`
and `|ω|_E ≤ 1`.  For a.e. `x`, `|ω − β|_E ≤ δ + |g₁ − β|_E` where `χ = 1`, and
`|ω − β|_E ≤ 2` where `χ ≠ 1`.  Integrating,
`∫ |ω − β|_E dν ≤ δm + ∫ |g₁ − β|_E dν + 2ν{χ ≠ 1} < ε/4 + ε/4 + ε/4 < ε`. -/
theorem Submission.rsd_mw_exists_testForm_approx : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsFiniteMeasure ν → IsOpen V → ν Vᶜ = 0 → Integrable β ν → (∀ᵐ x ∂ν, covectorEuclideanNorm (β x) ≤ 1) → ∀ ε : ℝ, 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε := by
  intro P n ν V β hν hV hVc hβ hβ1 ε hε
  -- `N := covectorEuclideanNorm` is subadditive and absolutely homogeneous
  obtain ⟨htri, hsmul, -, -⟩ := Submission.rsd_mw_tfa_norm_props P n
  -- Step 1: a smooth cut-off `χ` with `tsupport χ ⊆ V` and `ν{χ ≠ 1} < ε/8`
  obtain ⟨χ, hχs, hχc, hχV, hχ01, hχν⟩ :=
    Submission.rsd_mw_tfa_smooth_cutoff P ν V hν hV hVc (ε / 8) (by positivity)
  -- Step 2: a continuous compactly supported `g₁` with `N(g₁) ≤ 1` and `∫ N(g₁ - β) dν < ε/4`
  obtain ⟨g₁, hg₁c, hg₁s, hg₁1, hg₁β⟩ :=
    Submission.rsd_mw_tfa_continuous_approx P n ν β hν hβ hβ1 (ε / 4) (by positivity)
  -- Step 3: a smooth `g₂` with `N(g₂) ≤ 1` and `N(g₂ - g₁) ≤ δ = ε/(4(m + 1))`, `m = ν(ℝᴾ)`
  set m : ℝ := (ν univ).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ : ℝ := ε / (4 * (m + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨g₂, hg₂s, hg₂1, hg₂g₁⟩ :=
    Submission.rsd_mw_tfa_smooth_uniform_approx P n g₁ hg₁c hg₁s hg₁1 δ hδ0
  -- Step 4: `ω = χ g₂` is a test form with `tsupport ω ⊆ V` and `N(ω) ≤ 1`
  have hω1 : ∀ x, covectorEuclideanNorm (χ x • g₂ x) ≤ 1 := fun x => by
    rw [hsmul, abs_of_nonneg (hχ01 x).1]
    exact (mul_le_of_le_one_left (covectorEuclideanNorm_nonneg _) (hχ01 x).2).trans (hg₂1 x)
  refine ⟨fun x => χ x • g₂ x, ⟨hχs.smul hg₂s, hχc.smul_right⟩,
    (tsupport_smul_subset_left χ g₂).trans hχV, hω1, ?_⟩
  -- Step 5: a.e., `N(ω - β) ≤ δ + N(g₁ - β)` where `χ = 1` and `N(ω - β) ≤ 2` on `S = {χ ≠ 1}`
  set S : Set (Euclid P) := {x | χ x ≠ 1}
  have hSm : MeasurableSet S := (isOpen_ne_fun hχs.continuous continuous_const).measurableSet
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ≤
      ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
        S.indicator (fun _ => (2 : ℝ≥0∞)) x := by
    filter_upwards [hβ1] with x hx
    by_cases h1 : χ x = 1
    · rw [indicator_of_notMem (not_not.mpr h1), add_zero,
        ← ENNReal.ofReal_add hδ0.le (covectorEuclideanNorm_nonneg _), h1, one_smul]
      refine ENNReal.ofReal_le_ofReal ?_
      calc covectorEuclideanNorm (g₂ x - β x)
          = covectorEuclideanNorm ((g₂ x - g₁ x) + (g₁ x - β x)) := by rw [sub_add_sub_cancel]
        _ ≤ covectorEuclideanNorm (g₂ x - g₁ x) + covectorEuclideanNorm (g₁ x - β x) :=
          htri _ _
        _ ≤ δ + covectorEuclideanNorm (g₁ x - β x) := by linarith [hg₂g₁ x]
    · rw [indicator_of_mem h1]
      refine le_add_left (le_of_le_of_eq (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_ofNat 2))
      calc covectorEuclideanNorm (χ x • g₂ x - β x)
          = covectorEuclideanNorm (χ x • g₂ x + -β x) := by rw [sub_eq_add_neg]
        _ ≤ covectorEuclideanNorm (χ x • g₂ x) + covectorEuclideanNorm (-β x) := htri _ _
        _ ≤ 2 := by rw [covectorEuclideanNorm_neg]; linarith [hω1 x]
  -- Step 6: integrate, `∫ N(ω - β) dν ≤ δm + ∫ N(g₁ - β) dν + 2ν(S) < 3ε/4`
  have hδm : ENNReal.ofReal δ * ν univ ≤ ENNReal.ofReal (ε / 4) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top ν univ), ← hm, ← ENNReal.ofReal_mul hδ0.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc δ * m ≤ δ * (m + 1) := by nlinarith
      _ = ε / 4 := by rw [hδ]; field_simp
  have hS2 : 2 * ν S < ENNReal.ofReal (ε / 4) := by
    calc 2 * ν S = ν S + ν S := two_mul _
      _ < ENNReal.ofReal (ε / 8) + ENNReal.ofReal (ε / 8) := ENNReal.add_lt_add hχν hχν
      _ = ENNReal.ofReal (ε / 4) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  calc ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (χ x • g₂ x - β x)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal δ + ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) +
          S.indicator (fun _ => (2 : ℝ≥0∞)) x) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal δ * ν univ +
          ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (g₁ x - β x)) ∂ν + 2 * ν S := by
        rw [lintegral_add_right _ (measurable_const.indicator hSm),
          lintegral_add_left measurable_const, lintegral_const, lintegral_indicator_const hSm]
    _ < ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4) :=
        ENNReal.add_lt_add (ENNReal.add_lt_add_of_le_of_lt
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν univ)) hδm hg₁β) hS2
    _ ≤ ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **A norming field bounds `μ(W')` by the mass `M_W(T)`** (the inequality `μ_T(W') ≤ M_W(T)`
behind Simon 6.2.8, `μ_T(W) = M_W(T)`, for the representation 6.2.7 `T(ω) = ∫ ⟨ω, ξ⟩ dμ`;
`|·|_E` is `covectorEuclideanNorm`).  Let `W' ⊂⊂ U` be open with `W' ⊆ W`.  Then `ν = μ⌞W'` is
finite, as `closure W'` is a compact subset of `U`, and the bounded field `β` is `ν`-integrable.
For `ε > 0`, `Submission.rsd_mw_exists_testForm_approx` gives a test form `ω` with
`tsupport ω ⊆ W'`, `|ω|_E ≤ 1` and `∫ |ω − β|_E dν < ε`, so `ω` is admissible for `M_W(T)`.
The function `f = ξ(ω)` vanishes off `W'`, so `T(ω) = ∫ f dν`; and `ν`-a.e.
`1 − f = ξ(β − ω) ≤ |ω − β|_E`, since `ξ(β) = 1` and `|ξ(α)| ≤ |α|_E`.  Hence
`μ(W') − T(ω) = ∫ (1 − f) dν < ε`, and `μ(W') ≤ M_W(T) + ε` for every `ε > 0`. -/
theorem Submission.cmrc_measure_le_massOn_of_norming : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β : Euclid P → Covector (Euclid P) n), (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K < ∞) → AEStronglyMeasurable ξ μ → (∀ (x : Euclid P) (α : Covector (Euclid P) n), |ξ x α| ≤ covectorEuclideanNorm α) → (∀ ω : TestFormOn U n, T ω = ∫ x, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μ) → AEStronglyMeasurable β μ → (∃ C : ℝ, ∀ x, ‖β x‖ ≤ C) → (∀ x, covectorEuclideanNorm (β x) ≤ 1) → (∀ᵐ x ∂μ, ξ x (β x) = 1) → ∀ W W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ T.massOn W := by
  intro P n U T μ ξ β hμK hξm hξ1 hT hβm hβC hβ1 hξβ W W' hW' hW'U hW'W
  -- `N := covectorEuclideanNorm`, `ν := μ⌞W'`
  -- Step 1: `ν` is finite (`closure W'` is a compact subset of `U`) and `ν(W'ᶜ) = 0`
  have hμW' : μ W' < ∞ := (measure_mono subset_closure).trans_lt (hμK _ hW'U.1 hW'U.2)
  have : IsFiniteMeasure (μ.restrict W') := isFiniteMeasure_restrict.2 hμW'.ne
  have hνc : μ.restrict W' W'ᶜ = 0 := by
    rw [Measure.restrict_apply hW'.measurableSet.compl, compl_inter_self, measure_empty]
  -- Step 2: `β` is bounded, hence `ν`-integrable
  obtain ⟨C, hC⟩ := hβC
  have hβi : Integrable β (μ.restrict W') :=
    Integrable.of_bound hβm.restrict C (Eventually.of_forall hC)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- Step 3: a test form `ω₀` with `tsupport ω₀ ⊆ W'`, `N(ω₀) ≤ 1` and `∫ N(ω₀ - β) dν < ε`
  obtain ⟨ω₀, hω₀, hω₀W', hω₀1, hω₀β⟩ := Submission.rsd_mw_exists_testForm_approx P n
    (μ.restrict W') W' β inferInstance hW' hνc hβi (Eventually.of_forall hβ1) ε
    (NNReal.coe_pos.2 hε)
  -- Step 4: `ω₀ ∈ 𝒟ⁿ(U)` is admissible for `M_W(T)`, so `T(ω₀) ≤ M_W(T)`
  let ω : TestFormOn U n := ⟨ω₀, hω₀, hω₀W'.trans (subset_closure.trans hW'U.2)⟩
  have hTω : ENNReal.ofReal (T ω) ≤ T.massOn W := T.le_massOn ⟨hω₀W'.trans hW'W, hω₀1⟩
  -- Step 5: `f = ξ(ω₀)` vanishes off `W'`, so `T(ω₀) = ∫ f dν`
  set f : Euclid P → ℝ := fun x => ξ x (ω₀ x) with hf
  have hTf : T ω = ∫ x, f x ∂(μ.restrict W') := by
    rw [hT ω, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
    simp [hf, image_eq_zero_of_notMem_tsupport fun h => hx (hω₀W' h)]
  -- Step 6: `|f| ≤ N(ω₀) ≤ 1`, so `f` is `ν`-integrable
  have hf1 : ∀ x, |f x| ≤ 1 := fun x => (hξ1 x (ω₀ x)).trans (hω₀1 x)
  have hfm : AEStronglyMeasurable f μ :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξm.prodMk hω₀.1.continuous.aestronglyMeasurable)
  have hfi : Integrable f (μ.restrict W') :=
    Integrable.of_bound hfm.restrict 1 (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hf1 x)
  -- Step 7: `ν`-a.e., `1 - f = ξ(β - ω₀) ≤ N(ω₀ - β)`, since `ξ(β) = 1` and `|ξ(α)| ≤ N(α)`
  have hle : ∀ᵐ x ∂(μ.restrict W'), 1 - f x ≤ covectorEuclideanNorm (ω₀ x - β x) := by
    filter_upwards [ae_restrict_of_ae hξβ] with x hx
    have h := abs_le.1 (hξ1 x (ω₀ x - β x))
    rw [map_sub, hx] at h
    linarith [h.1]
  -- Step 8: `μ(W') - T(ω₀) = ∫ (1 - f) dν ≤ ∫ N(ω₀ - β) dν < ε`
  have hint : ENNReal.ofReal (μ.real W' - T ω) < ENNReal.ofReal ε := by
    have h1 : ∫ x, (1 - f x) ∂(μ.restrict W') = μ.real W' - T ω := by
      rw [integral_sub (integrable_const 1) hfi, integral_const, hTf, smul_eq_mul, mul_one,
        measureReal_restrict_apply_univ]
    have hgi : Integrable (fun x => 1 - f x) (μ.restrict W') := (integrable_const 1).sub hfi
    rw [← h1, ofReal_integral_eq_lintegral_ofReal hgi
      (Eventually.of_forall fun x => sub_nonneg.2 (le_of_abs_le (hf1 x)))]
    exact (lintegral_mono_ae (hle.mono fun x hx => ENNReal.ofReal_le_ofReal hx)).trans_lt hω₀β
  -- Step 9: `μ(W') ≤ T(ω₀) + ε ≤ M_W(T) + ε`
  calc μ W' = ENNReal.ofReal (T ω + (μ.real W' - T ω)) := by
        rw [add_sub_cancel, ofReal_measureReal hμW'.ne]
    _ ≤ ENNReal.ofReal (T ω) + ENNReal.ofReal (μ.real W' - T ω) := ENNReal.ofReal_add_le
    _ ≤ T.massOn W + ε := add_le_add hTω (hint.le.trans_eq ENNReal.ofReal_coe_nnreal)
/-- Exhaustion by compactly contained open sets: if `U, W ⊆ ℝᴾ` are open, `μ(ℝᴾ \ U) = 0` and
`μ(W') ≤ m` for every open `W' ⊂⊂ U` with `W' ⊆ W`, then `μ(W) ≤ m`.  The open sets
`W'ⱼ = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` have closures inside the compact sets
`{y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} ⊆ W ∩ U`, increase with `j` and exhaust `W ∩ U`,
so `μ(W) = μ(W ∩ U) = supⱼ μ(W'ⱼ) ≤ m` by continuity from below. -/
theorem Submission.cmrc_measure_le_of_compactlyContained : ∀ (P : ℕ) (μ : Measure (Euclid P)) (U W : Set (Euclid P)) (m : ℝ≥0∞), IsOpen U → IsOpen W → μ Uᶜ = 0 → (∀ W' : Set (Euclid P), IsOpen W' → CompactlyContained W' U → W' ⊆ W → μ W' ≤ m) → μ W ≤ m := by
  intro P μ U W m hU hW hUc hm
  -- `V j = {y : ‖y‖ < j, (j + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}` exhausts the open set `W ∩ U`
  set V : ℕ → Set (Euclid P) :=
    fun j => {y | ‖y‖ < j ∧ ((j : ℝ≥0∞) + 1)⁻¹ < infEDist y (W ∩ U)ᶜ}
  have hd : Continuous fun y : Euclid P => infEDist y (W ∩ U)ᶜ := continuous_infEDist
  have hpos : ∀ j : ℕ, 0 < ((j : ℝ≥0∞) + 1)⁻¹ := fun j => ENNReal.inv_pos.2 (by simp)
  -- `closure (V j)` lies in `F j = {y : ‖y‖ ≤ j, (j + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ}`, a compact
  -- subset of `W ∩ U`
  have hF : ∀ j : ℕ, IsCompact (closure (V j)) ∧ closure (V j) ⊆ W ∩ U := by
    intro j
    have hVF : closure (V j) ⊆
        {y : Euclid P | ‖y‖ ≤ j ∧ ((j : ℝ≥0∞) + 1)⁻¹ ≤ infEDist y (W ∩ U)ᶜ} :=
      closure_minimal (fun y hy => ⟨hy.1.le, hy.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter (isClosed_le continuous_const hd))
    refine ⟨(isCompact_closedBall (0 : Euclid P) (j : ℝ)).of_isClosed_subset isClosed_closure
      fun y hy => ?_, fun y hy => ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      exact (hVF hy).1
    · by_contra hy'
      have h := (hVF hy).2
      rw [infEDist_zero_of_mem hy'] at h
      exact (hpos j).not_ge h
  have hVsub : ∀ j, V j ⊆ W ∩ U := fun j => subset_closure.trans (hF j).2
  have hVm : ∀ j, μ (V j) ≤ m := fun j =>
    hm (V j) ((isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const hd))
      ⟨(hF j).1, (hF j).2.trans inter_subset_right⟩ ((hVsub j).trans inter_subset_left)
  have hmono : Monotone V := by
    intro j k hjk y hy
    refine ⟨hy.1.trans_le (by exact_mod_cast hjk), lt_of_le_of_lt ?_ hy.2⟩
    gcongr
  have hUnion : ⋃ j, V j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset hVsub) fun y hy => ?_
    have hne : infEDist y (W ∩ U)ᶜ ≠ 0 := fun h0 =>
      ((mem_iff_infEDist_zero_of_closed (hW.inter hU).isClosed_compl).2 h0) hy
    obtain ⟨j₁, hj₁⟩ := ENNReal.exists_inv_nat_lt hne
    obtain ⟨j₂, hj₂⟩ := exists_nat_gt ‖y‖
    refine mem_iUnion.2 ⟨max j₁ j₂, hj₂.trans_le (by exact_mod_cast le_max_right j₁ j₂),
      lt_of_le_of_lt ?_ hj₁⟩
    gcongr
    norm_cast
    omega
  -- `μ W = μ (W ∩ U)` since `μ Uᶜ = 0`; continuity from below along the increasing `V j`
  calc μ W = μ (⋃ j, V j) := by rw [hUnion, measure_inter_conull hUc]
    _ = ⨆ j, μ (V j) := hmono.measure_iUnion
    _ ≤ m := iSup_le hVm

/-- **Mass of the current `Ξ(ω) = ∫ ⟨ω, ζ₀⟩ dν` with a constant multivector `ζ₀`** (Simon 6.2.5;
step 5(δ) of the integer-multiplicity criterion for cycles; `|·|_E` is `covectorEuclideanNorm`).
Suppose `ν` is finite on compact sets, `|⟨α, ζ₀⟩| ≤ s |α|_E` for every `α`, and `⟨β, ζ₀⟩ = s` for
some `β` with `|β|_E ≤ 1`.  Then `s ≥ 0`, because `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`.  Put `μ = s ν` and
`ξ ≡ s⁻¹ ζ₀`.  Then `|⟨α, ξ⟩| ≤ |α|_E` and `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ`; for `s = 0` both sides vanish,
since then `ζ₀ = 0`.  `Submission.cmrc_massOn_le_of_repr` gives `M_W(Ξ) ≤ μ(W) = s ν(W)`.  For
`s > 0` the constant field `β` norms `ξ`, as `⟨β, ξ⟩ = 1`.  So
`Submission.cmrc_measure_le_massOn_of_norming` gives `μ(W') ≤ M_W(Ξ)` for every open `W' ⊂⊂ ℝᴾ`
with `W' ⊆ W`, and `Submission.cmrc_measure_le_of_compactlyContained` gives `μ(W) ≤ M_W(Ξ)`. -/
theorem Submission.cbr_ci_const_vector_massOn : ∀ (P m : ℕ) (ν : Measure (Euclid P)) (ζ₀ : MultiVector P m) (s : ℝ) (Ξ : GeometricCurrentOn (univ : Set (Euclid P)) m), (∀ K : Set (Euclid P), IsCompact K → ν K < ∞) → (∀ α : Covector (Euclid P) m, |ζ₀ α| ≤ s * covectorEuclideanNorm α) → (∃ β : Covector (Euclid P) m, covectorEuclideanNorm β ≤ 1 ∧ ζ₀ β = s) → (∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω = ∫ x, ζ₀ ((ω : DifferentialForm (Euclid P) m) x) ∂ν) → ∀ W : Set (Euclid P), IsOpen W → Ξ.massOn W = ENNReal.ofReal s * ν W := by
  rintro P m ν ζ₀ s Ξ hνK hζ₀ ⟨β, hβ1, hζβ⟩ hΞ W hW
  -- Step 1: `s ≥ 0`, since `|s| = |⟨β, ζ₀⟩| ≤ s |β|_E`
  have hs : 0 ≤ s := by
    have h := hζ₀ β
    rw [hζβ] at h
    nlinarith [neg_le_abs s, covectorEuclideanNorm_nonneg β]
  -- Step 2: `ζ₀ = s (s⁻¹ ζ₀)`; for `s = 0` this says `ζ₀ = 0`, as `|⟨α, ζ₀⟩| ≤ 0`
  have hζs : ∀ α : Covector (Euclid P) m, s * (s⁻¹ * ζ₀ α) = ζ₀ α := by
    intro α
    rcases hs.eq_or_lt with h0 | hpos
    · have h := hζ₀ α
      rw [← h0, zero_mul, abs_nonpos_iff] at h
      rw [← h0, zero_mul, h]
    · rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  -- Step 3: the constant field `ξ ≡ s⁻¹ ζ₀` is unit-bounded, `|⟨α, ξ⟩| ≤ |α|_E`
  have hξ : ∀ (_ : Euclid P) (α : Covector (Euclid P) m),
      |(s⁻¹ • ζ₀) α| ≤ covectorEuclideanNorm α := by
    intro _ α
    rw [_root_.smul_apply, smul_eq_mul, abs_mul, abs_inv]
    rcases hs.eq_or_lt with h0 | hpos
    · rw [← h0, abs_zero, inv_zero, zero_mul]
      exact covectorEuclideanNorm_nonneg α
    · rw [abs_of_pos hpos, inv_mul_le_iff₀ hpos]
      exact hζ₀ α
  -- Step 4: `Ξ(ω) = ∫ ⟨ω, ξ⟩ dμ` for `μ = s ν`
  have hrep : ∀ ω : TestFormOn (univ : Set (Euclid P)) m, Ξ ω =
      ∫ x, (s⁻¹ • ζ₀) ((ω : DifferentialForm (Euclid P) m) x) ∂(ENNReal.ofReal s • ν) := by
    intro ω
    rw [hΞ ω, integral_smul_measure, ENNReal.toReal_ofReal hs, smul_eq_mul,
      ← integral_const_mul]
    simp only [_root_.smul_apply, smul_eq_mul, hζs]
  have hμW : (ENNReal.ofReal s • ν) W = ENNReal.ofReal s * ν W := by
    rw [Measure.smul_apply, smul_eq_mul]
  rw [← hμW]
  -- Step 5: upper bound `M_W(Ξ) ≤ μ(W)`
  refine le_antisymm (Submission.cmrc_massOn_le_of_repr P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) hξ hrep W) ?_
  -- Step 6: lower bound `μ(W) ≤ M_W(Ξ)`; trivial for `s = 0`, where `μ = 0`
  rcases hs.eq_or_lt with h0 | hpos
  · rw [← h0, ENNReal.ofReal_zero, zero_smul, Measure.coe_zero, Pi.zero_apply]
    exact zero_le
  -- for `s > 0`, `μ` is finite on compact sets and the constant covector `β` norms `ξ`:
  -- `⟨β, ξ⟩ = s⁻¹ ⟨β, ζ₀⟩ = 1`
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ univ → (ENNReal.ofReal s • ν) K < ∞ := by
    intro K hK _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hνK K hK)
  have hξβ : ∀ᵐ _ ∂(ENNReal.ofReal s • ν), (s⁻¹ • ζ₀) β = 1 := Eventually.of_forall fun _ => by
    rw [_root_.smul_apply, smul_eq_mul, hζβ, inv_mul_cancel₀ hpos.ne']
  -- `μ(W') ≤ M_W(Ξ)` for open `W' ⊂⊂ ℝᴾ` with `W' ⊆ W`; exhaust `W` by such `W'`
  refine Submission.cmrc_measure_le_of_compactlyContained P (ENNReal.ofReal s • ν) univ W
    (Ξ.massOn W) isOpen_univ hW (by rw [compl_univ, measure_empty]) fun W' hW' hW'U hW'W => ?_
  exact Submission.cmrc_measure_le_massOn_of_norming P m univ Ξ (ENNReal.ofReal s • ν)
    (fun _ => s⁻¹ • ζ₀) (fun _ => β) hμK aestronglyMeasurable_const hξ hrep
    aestronglyMeasurable_const ⟨‖β‖, fun _ => le_rfl⟩ (fun _ => hβ1) hξβ W W' hW' hW'U hW'W

/-- **Hausdorff measure of the affine plane through `a` spanned by an orthonormal frame `w`**
(Simon Ch. 1, 2.9, `Hᵐ = Lᵐ` on `ℝᵐ`, transported by an isometry; step 0 of the integer
multiplicity criterion for plane cycles).  Let `S = {y | y − a ∈ span w}`.  Orthonormality gives
`‖Σᵢ cᵢ wᵢ‖ = ‖c‖`, so `J(u) = a + Σᵢ uᵢ wᵢ` is an isometry of `Euclid m` onto `S`.  Hence
`J_*(Lᵐ) = J_*(Hᵐ) = Hᵐ⌞S`, and composing with the volume-preserving `toLp : ℝᵐ → Euclid m`
gives (i).  `S` is the preimage of the closed finite-dimensional subspace `span w` under
`y ↦ y − a`.  For compact `K`, `(Hᵐ⌞S)(K) = Lᵐ(J⁻¹K) < ∞`, as `J` is a closed embedding; and
`(Hᵐ⌞S)(B_r(a)) = Lᵐ(J⁻¹B_r(a)) > 0`, as `J⁻¹B_r(a)` is open and contains `0`. -/
theorem Submission.cbr_cipi_affine_plane_measure : ∀ (P m : ℕ) (w : Fin m → Euclid P) (a : Euclid P), Orthonormal ℝ w → Measure.map (fun z : Fin m → ℝ => a + ∑ i, z i • w i) volume = (μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ IsClosed {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} ∧ (∀ K : Set (Euclid P), IsCompact K → ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) K < ∞) ∧ ∀ r : ℝ, 0 < r → 0 < ((μHE[m] : Measure (Euclid P)).restrict {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)}) (ball a r) := by
  intro P m w a hw
  set S : Set (Euclid P) := {y : Euclid P | y - a ∈ Submodule.span ℝ (Set.range w)} with hS
  -- Step 1: `J(u) = a + Σᵢ uᵢ wᵢ` is an isometry, as `‖Σᵢ cᵢ wᵢ‖ = ‖c‖` by orthonormality
  set J : Euclid m → Euclid P := fun u => a + ∑ i, u i • w i
  have hnorm : ∀ c : Euclid m, ‖∑ i, c i • w i‖ = ‖c‖ := by
    intro c
    have h1 : ‖∑ i, c i • w i‖ ^ 2 = ‖c‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hw.inner_sum, EuclideanSpace.real_norm_sq_eq]
      simp [sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
  have hJ : Isometry J := by
    refine Isometry.of_dist_eq fun u u' => ?_
    rw [dist_eq_norm, dist_eq_norm, ← hnorm (u - u')]
    simp [J, sub_smul, Finset.sum_sub_distrib]
  -- Step 2: `range J = S`, as `y − a ∈ span w` iff `y − a = Σᵢ cᵢ wᵢ` for some `c`
  have hrange : range J = S := by
    ext y
    rw [hS, mem_range, mem_ofPred_eq, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨fun i => u i, by simp [J]⟩
    · rintro ⟨c, hc⟩
      exact ⟨WithLp.toLp 2 c, by simp [J, hc]⟩
  -- Step 3: `J_*(Lᵐ) = J_*(Hᵐ) = Hᵐ⌞S`
  have hJm : Measurable J := hJ.continuous.measurable
  have hmapJ : Measure.map J volume = (μHE[m] : Measure (Euclid P)).restrict S := by
    rw [← hrange, ← hJ.map_euclideanHausdorffMeasure,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  refine ⟨?_, ?_, ?_, ?_⟩
  -- Step 4: (i), as the parametrisation is `J ∘ toLp` and `toLp` preserves volume
  · have hcomp : (fun z : Fin m → ℝ => a + ∑ i, z i • w i) = J ∘ WithLp.toLp 2 := rfl
    rw [hcomp, ← Measure.map_map hJm (PiLp.volume_preserving_toLp (Fin m)).measurable,
      (PiLp.volume_preserving_toLp (Fin m)).map_eq, hmapJ]
  -- Step 5: (ii), `S` is the preimage of the closed subspace `span w` under `y ↦ y − a`
  · exact (Submodule.closed_of_finiteDimensional _).preimage (continuous_id.sub continuous_const)
  -- Step 6: (iii), `(Hᵐ⌞S)(K) = Lᵐ(J⁻¹K) < ∞`, `J` being a closed embedding
  · intro K hK
    rw [← hmapJ, Measure.map_apply hJm hK.isClosed.measurableSet]
    exact (hJ.isClosedEmbedding.isCompact_preimage hK).measure_lt_top
  -- Step 7: (iv), `(Hᵐ⌞S)(B_r(a)) = Lᵐ(J⁻¹B_r(a)) > 0`, an open set containing `0`
  · intro r hr
    rw [← hmapJ, Measure.map_apply hJm measurableSet_ball]
    exact (isOpen_ball.preimage hJ.continuous).measure_pos _ ⟨0, by simp [J, hr]⟩
/-- **Integrals of partial derivatives of a compactly supported `C¹` function over a coordinate
half-space** (the divergence theorem on a half-space by Fubini and the fundamental theorem of
calculus; used for the boundary of a half-plane current in the integer-multiplicity criterion for
cycles).  Let `g : ℝ^{d+1} → ℝ` be `C¹` with compact support, `H = {z | z₀ < t}` and
`∂ᵢg(z) = Dg(z)(eᵢ)`.  Since `tsupport g ⊆ B̄_R(0)`, on each coordinate line
`ℓ(s) = insertNth i s y = ℓ(0) + s eᵢ` the function `h = g ∘ ℓ` is `C¹` with compact support and
`h′(s) = ∂ᵢg(ℓ(s))`.  Fubini through the measure-preserving `z ↦ (zᵢ, removeNth i z)` gives
`∫_H ∂ᵢg = ∫_y ∫_s 1_H(ℓ(s)) h′(s) ds dy`.  For `i ≠ 0`, `ℓ(s)₀ = y₀` does not depend on `s`, so
each inner integral is `0` or `∫_ℝ h′ = 0`.  For `i = 0`, `ℓ(s) = (s, y)` and the inner integral
is `∫_{(−∞,t)} h′ = h(t) = g(t, y)`. -/
theorem Submission.cbr_cipi_halfspace_partial_integral : ∀ (d : ℕ) (g : (Fin (d + 1) → ℝ) → ℝ) (t : ℝ), ContDiff ℝ 1 g → HasCompactSupport g → (∀ i : Fin (d + 1), i ≠ 0 → ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single i 1) = 0) ∧ ∫ z in {z : Fin (d + 1) → ℝ | z 0 < t}, fderiv ℝ g z (Pi.single 0 1) = ∫ z' : Fin d → ℝ, g (Fin.cons t z') := by
  intro d g t hg hcs
  -- Step 1: `tsupport g ⊆ B̄_R(0)` (sup norm)
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  -- Steps 2–3: on the coordinate line `ℓ(s) = insertNth i s y = ℓ(0) + s eᵢ`, `h = g ∘ ℓ` is `C¹`
  -- with compact support and `h′(s) = ∂ᵢg(ℓ(s))`; the fundamental theorem of calculus gives
  -- `∫_ℝ h′ = 0` and `∫_{(−∞,t)} h′ = h(t)`
  have hline : ∀ (i : Fin (d + 1)) (y : Fin d → ℝ),
      (∫ s : ℝ, fderiv ℝ g (Fin.insertNth i s y) (Pi.single i 1) = 0) ∧
      ∫ s in Iio t, fderiv ℝ g (Fin.insertNth i s y) (Pi.single i 1) = g (Fin.insertNth i t y) := by
    intro i y
    have hℓ : ∀ s : ℝ, (Fin.insertNth i s y : Fin (d + 1) → ℝ) =
        Fin.insertNth i 0 y + s • Pi.single i 1 := by
      intro s
      funext j
      rcases eq_or_ne j i with rfl | hj
      · simp
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
        simp [hj]
    set h : ℝ → ℝ := fun s => g (Fin.insertNth i s y) with hh
    have hcomp : h = g ∘ fun s : ℝ =>
        (Fin.insertNth i 0 y : Fin (d + 1) → ℝ) + s • Pi.single i 1 := by
      funext s
      simp only [hh, Function.comp_apply, ← hℓ s]
    have hderiv : ∀ s, HasDerivAt h (fderiv ℝ g (Fin.insertNth i s y) (Pi.single i 1)) s := by
      intro s
      have h1 : HasDerivAt
          (fun s : ℝ => (Fin.insertNth i 0 y : Fin (d + 1) → ℝ) + s • Pi.single i 1)
          (Pi.single i 1) s := by
        simpa using ((hasDerivAt_id s).smul_const (Pi.single i (1 : ℝ) : Fin (d + 1) → ℝ)).const_add
          (Fin.insertNth i 0 y : Fin (d + 1) → ℝ)
      have h2 := (hg.differentiable one_ne_zero (Fin.insertNth i s y)).hasFDerivAt
      rw [hℓ s] at h2
      rw [hcomp, hℓ s]
      exact h2.comp_hasDerivAt s h1
    have hcont : ContDiff ℝ 1 h := by
      rw [hcomp]
      exact hg.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
    -- `|s| = |ℓ(s)ᵢ| ≤ ‖ℓ(s)‖`, so `h(s) = 0` for `|s| > R`
    have hsupp : HasCompactSupport h := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun s hs => ?_
      show g (Fin.insertNth i s y) = 0
      refine image_eq_zero_of_notMem_tsupport fun hmem => hs ?_
      have h3 := hR hmem
      simp only [mem_closedBall, dist_zero_right] at h3 ⊢
      calc ‖s‖ = ‖(Fin.insertNth i s y : Fin (d + 1) → ℝ) i‖ := by simp
        _ ≤ ‖(Fin.insertNth i s y : Fin (d + 1) → ℝ)‖ := norm_le_pi_norm _ i
        _ ≤ R := h3
    have hderiv_eq : deriv h = fun s => fderiv ℝ g (Fin.insertNth i s y) (Pi.single i 1) := by
      funext s
      exact (hderiv s).deriv
    refine ⟨integral_eq_zero_of_hasDerivAt_of_integrable hderiv ?_ ?_, ?_⟩
    · exact hderiv_eq ▸ (hcont.continuous_deriv le_rfl).integrable_of_hasCompactSupport hsupp.deriv
    · exact hcont.continuous.integrable_of_hasCompactSupport hsupp
    · rw [← integral_Iic_eq_integral_Iio, ← hderiv_eq]
      exact HasCompactSupport.integral_Iic_deriv_eq hcont hsupp t
  -- Step 4: Fubini through the measure-preserving `z ↦ (zᵢ, removeNth i z)`, whose inverse is
  -- `(s, y) ↦ insertNth i s y`
  have hfub : ∀ (i : Fin (d + 1)) (F : (Fin (d + 1) → ℝ) → ℝ), Integrable F →
      ∫ z, F z = ∫ y : Fin d → ℝ, ∫ s : ℝ, F (Fin.insertNth i s y) := by
    intro i F hF
    have hmp := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i).symm
    rw [← hmp.integral_comp' F,
      show (volume : Measure (ℝ × (Fin d → ℝ))) = volume.prod volume from rfl, integral_prod_symm]
    · simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  -- `1_H ∂ᵢg` is integrable: `∂ᵢg` is continuous with compact support and `H` is Borel
  have hH : MeasurableSet {z : Fin (d + 1) → ℝ | z 0 < t} :=
    measurableSet_lt (measurable_pi_apply 0) measurable_const
  have hint : ∀ i : Fin (d + 1), Integrable ({z : Fin (d + 1) → ℝ | z 0 < t}.indicator
      fun z => fderiv ℝ g z (Pi.single i 1)) := fun i =>
    (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hcs.fderiv_apply (𝕜 := ℝ) _)).indicator hH
  constructor
  -- Step 5: for `i ≠ 0`, `(insertNth i s y)₀ = y₀` does not depend on `s`, so each inner integral
  -- is `0` or `∫_ℝ h′ = 0`
  · intro i hi
    rw [← integral_indicator hH, hfub i _ (hint i)]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
    have hconst : ∀ s : ℝ, (Fin.insertNth i s y : Fin (d + 1) → ℝ) 0 =
        (Fin.insertNth i 0 y : Fin (d + 1) → ℝ) 0 := by
      intro s
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (x := (0 : Fin (d + 1))) (y := i) (Ne.symm hi)
      rw [← hk, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
    by_cases hy : (Fin.insertNth i 0 y : Fin (d + 1) → ℝ) 0 < t
    · simp only [Set.indicator, Set.mem_ofPred_eq, hconst, hy, ite_true]
      exact (hline i y).1
    · simp [Set.indicator, hconst, hy]
  -- Step 6: for `i = 0`, `insertNth 0 s y = Fin.cons s y`, so the inner integral is
  -- `∫_{(−∞,t)} h′ = h(t) = g(Fin.cons t y)`
  · rw [← integral_indicator hH, hfub 0 _ (hint 0)]
    congr 1
    funext y
    have h0 := (hline 0 y).2
    simp only [Fin.insertNth_zero'] at h0
    rw [← h0, ← integral_indicator measurableSet_Iio]
    congr 1
    funext s
    simp [Set.indicator, Fin.insertNth_zero']

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
