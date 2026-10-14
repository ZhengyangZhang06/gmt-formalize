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

/-- An approximate tangent plane forces unit `Hⁿ`-density on closed balls (Simon Ch. 3,
Remark 1.5(3), with Definition 1.4).  If `Hⁿ(M ∩ B̄_s(x)) < ∞` and `Q` is an approximate tangent
space of `M` at `x`, then `Hⁿ(M ∩ B̄_ρ(x)) / (ωₙρⁿ) → 1` as `ρ ↓ 0`.  Since
`Hⁿ(η_{x,r}(M) ∩ B̄_1(0)) = r⁻ⁿHⁿ(M ∩ B̄_r(x))` and `Hⁿ(Q ∩ B̄_t(0)) = ωₙtⁿ`, the radial cut-offs
`g_{1-ε,1} ≤ 1_{B̄_1(0)} ≤ g_{1,1+ε}` in `C_c` squeeze `r⁻ⁿHⁿ(M ∩ B̄_r(x))` between blow-up integrals
whose limits lie within `ωₙ(1 ∓ ε)ⁿ`. -/
theorem Submission.rsd_tendsto_closedBall_density_of_approxTangent : ∀ (P n : ℕ) (M : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)) (s : ℝ), 0 < s → μHE[n] (M ∩ closedBall x s) ≠ ∞ → HasApproximateTangentSpaceAt n M x Q → Tendsto (fun ρ : ℝ => μHE[n] (M ∩ closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
  intro P n M x Q s hs hfin hT
  obtain ⟨hQ, hconv⟩ := hT
  -- Step 1: `ωₙ ∈ (0, ∞)`
  set ω := unitBallVolume n with hωdef
  have hω0 : ω ≠ 0 := (measure_ball_pos volume (0 : Euclid n) one_pos).ne'
  have hωtop : ω ≠ ∞ := measure_ball_lt_top.ne
  set w := ω.toReal with hwdef
  have hw : 0 < w := ENNReal.toReal_pos hω0 hωtop
  -- Step 2: `Hⁿ(Q ∩ B̄_t(0)) = ωₙ tⁿ`, via a linear isometry `ℝⁿ ≅ Q`
  have hplane0 : ∀ t : ℝ, 0 ≤ t →
      μHE[n] ((Q : Set (Euclid P)) ∩ closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    let b : OrthonormalBasis (Fin n) ℝ Q := (stdOrthonormalBasis ℝ Q).reindex (finCongr hQ)
    let ι : Euclid n →ₗᵢ[ℝ] Euclid P := Q.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
    have himage : ι '' closedBall 0 t = (Q : Set (Euclid P)) ∩ closedBall 0 t := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨(b.repr.symm v).2, ?_⟩
        rw [mem_closedBall, dist_zero_right] at hv ⊢
        have : ‖((b.repr.symm v : Q) : Euclid P)‖ = ‖v‖ := b.repr.symm.norm_map v
        simpa [ι, this] using hv
      · rintro ⟨hyQ, hy⟩
        refine ⟨b.repr ⟨y, hyQ⟩, ?_, ?_⟩
        · rw [mem_closedBall, dist_zero_right] at hy ⊢
          simpa using hy
        · simp [ι]
    rw [← himage, ι.isometry.euclideanHausdorffMeasure_image,
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
      Measure.addHaar_closedBall _ _ ht, finrank_euclideanSpace_fin, hωdef, unitBallVolume, mul_comm]
  -- Step 3: scaling `Hⁿ(η_{x,r}(A)) = r⁻ⁿ Hⁿ(A)` and `η_{x,r}(M) ∩ B̄_t(0) = η_{x,r}(M ∩ B̄_{tr}(x))`
  have hscale : ∀ r : ℝ, 0 < r → ∀ A : Set (Euclid P),
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' A) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] A := by
    intro r hr A
    have h1 : Poincare.SimonGMT.Chapter03.blowUpMap x r '' A =
        (fun y => r⁻¹ • y) '' ((fun y => y - x) '' A) := by
      rw [image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) :=
      Isometry.of_dist_eq (fun a c => by simp [dist_eq_norm])
    rw [h1, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
      hiso.euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [abs_of_pos hr]
  have himg : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' M ∩ closedBall 0 t =
        Poincare.SimonGMT.Chapter03.blowUpMap x r '' (M ∩ closedBall x (t * r)) := by
    intro r hr t
    have key : ∀ z : Euclid P,
        ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ ≤ t ↔ dist z x ≤ t * r := by
      intro z
      simp only [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hr, dist_eq_norm]
      rw [inv_mul_le_iff₀ hr, mul_comm r t]
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      rw [mem_closedBall, dist_zero_right, key] at hy
      exact ⟨z, ⟨hz, hy⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzb⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_zero_right, key]
      exact hzb
  have hνball : ∀ r : ℝ, 0 < r → ∀ t : ℝ,
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) =
        ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] (M ∩ closedBall x (t * r)) := by
    intro r hr t
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, himg r hr t, hscale r hr]
  have hmfin : ∀ r : ℝ, r ≤ s → μHE[n] (M ∩ closedBall x r) ≠ ∞ := fun r hr =>
    ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_right _ (closedBall_subset_closedBall hr)))
  have hνfin : ∀ r : ℝ, 0 < r → ∀ t : ℝ, t * r ≤ s →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)) (closedBall 0 t) ≠ ∞ := by
    intro r hr t ht
    rw [hνball r hr t]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hmfin _ ht)
  -- Step 4: radial cut-off functions `g_{a,b}` in `C_c`
  have hbump : ∀ a b : ℝ, 0 < a → a < b →
      ∃ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Continuous f ∧ (0 ≤ ⇑f) ∧
        (closedBall (0 : Euclid P) a).indicator 1 ≤ ⇑f ∧ ⇑f ≤ (closedBall (0 : Euclid P) b).indicator 1 := by
    intro a b ha hab
    have hcont : Continuous (fun y : Euclid P => max 0 (min 1 ((b - ‖y‖) / (b - a)))) :=
      continuous_const.max (continuous_const.min ((continuous_const.sub continuous_norm).div_const _))
    have hzero : ∀ y : Euclid P, b ≤ ‖y‖ → max 0 (min 1 ((b - ‖y‖) / (b - a))) = 0 := by
      intro y hy
      have h1 : (b - ‖y‖) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      rw [max_eq_left ((min_le_right _ _).trans h1)]
    let f : CompactlySupportedContinuousMap (Euclid P) ℝ :=
      { toFun := fun y => max 0 (min 1 ((b - ‖y‖) / (b - a)))
        continuous_toFun := hcont
        hasCompactSupport' := by
          refine HasCompactSupport.intro (isCompact_closedBall (0 : Euclid P) b) ?_
          intro y hy
          rw [mem_closedBall, dist_zero_right, not_le] at hy
          exact hzero y hy.le }
    have hf : ∀ y, f y = max 0 (min 1 ((b - ‖y‖) / (b - a))) := fun y => rfl
    refine ⟨f, f.continuous, fun y => by rw [hf]; exact le_max_left _ _, ?_, ?_⟩
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) a
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        rw [mem_closedBall, dist_zero_right] at hy
        have : 1 ≤ (b - ‖y‖) / (b - a) := by
          rw [le_div_iff₀ (by linarith)]; linarith
        rw [min_eq_left this, max_eq_right zero_le_one]
      · rw [indicator_of_notMem hy, hf]; exact le_max_left _ _
    · intro y
      by_cases hy : y ∈ closedBall (0 : Euclid P) b
      · rw [indicator_of_mem hy, Pi.one_apply, hf]
        exact max_le zero_le_one (min_le_left _ _)
      · rw [indicator_of_notMem hy, hf, hzero]
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy.le
  -- Step 5: integrability of functions dominated by the indicator of a finite-measure closed ball
  have hindint : ∀ (ν : Measure (Euclid P)) (t : ℝ), ν (closedBall 0 t) ≠ ∞ →
      Integrable ((closedBall (0 : Euclid P) t).indicator (1 : Euclid P → ℝ)) ν := fun ν t h =>
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const h)
  have hdomint : ∀ (ν : Measure (Euclid P)) (f : Euclid P → ℝ) (t : ℝ), Continuous f →
      ν (closedBall 0 t) ≠ ∞ → 0 ≤ f → f ≤ (closedBall (0 : Euclid P) t).indicator 1 →
      Integrable f ν := by
    intro ν f t hf hfin' h0 hle
    refine (hindint ν t hfin').mono' hf.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 y)]
    exact hle y
  -- Step 6: the normalised mass `a(r) = r⁻ⁿ Hⁿ(M ∩ B̄_r(x))` and the plane-ball values
  set a : ℝ → ℝ := fun r => (r⁻¹) ^ n * (μHE[n] (M ∩ closedBall x r)).toReal with hadef
  have hareal : ∀ r : ℝ, 0 < r →
      (μHE[n].restrict (Poincare.SimonGMT.Chapter03.blowUpMap x r '' M)).real (closedBall 0 1) = a r := by
    intro r hr
    rw [measureReal_def, hνball r hr 1, one_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  have hplane : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) = ω * ENNReal.ofReal (t ^ n) := by
    intro t ht
    rw [Measure.restrict_apply measurableSet_closedBall, inter_comm, hplane0 t ht]
  have hplanefin : ∀ t : ℝ, 0 ≤ t → (μHE[n].restrict (Q : Set (Euclid P))) (closedBall 0 t) ≠ ∞ := by
    intro t ht
    rw [hplane t ht]
    exact ENNReal.mul_ne_top hωtop ENNReal.ofReal_ne_top
  have hplanereal : ∀ t : ℝ, 0 ≤ t →
      (μHE[n].restrict (Q : Set (Euclid P))).real (closedBall 0 t) = w * t ^ n := by
    intro t ht
    rw [measureReal_def, hplane t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  -- Step 7: `a r → ωₙ`
  have ha : Tendsto a (𝓝[>] 0) (𝓝 w) := by
    rw [tendsto_order]
    constructor
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 - ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 - ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (lt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump (1 - ε) 1 (by linarith [hε.2]) (by linarith [hε.1])
      -- `∫_Q f ≥ ωₙ (1-ε)ⁿ`
      have hQ1 : w * (1 - ε) ^ n ≤ ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] := by
        rw [← hplanereal (1 - ε) (by linarith [hε.2]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hplanefin _ (by linarith [hε.2])))
          (hdomint _ _ 1 hfc (hplanefin _ zero_le_one) hf0 hfle) hfge
      filter_upwards [(tendsto_order.1 (hconv f)).1 c (hcε.trans_le hQ1),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `∫_{η(M)} f ≤ a r`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have hle : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] ≤ a r := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ 1 hfc (hνfin r hr2.1 1 h1) hf0 hfle)
          (hindint _ _ (hνfin r hr2.1 1 h1)) hfle
      exact hr1.trans_le hle
    · intro c hc
      have hcont : Tendsto (fun ε : ℝ => w * (1 + ε) ^ n) (𝓝[>] 0) (𝓝 w) := by
        have : Continuous (fun ε : ℝ => w * (1 + ε) ^ n) := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨ε, hcε, hε⟩ :=
        ((hcont.eventually (gt_mem_nhds hc)).and (Ioo_mem_nhdsGT one_pos)).exists
      obtain ⟨f, hfc, hf0, hfge, hfle⟩ := hbump 1 (1 + ε) one_pos (by linarith [hε.1])
      -- `∫_Q f ≤ ωₙ (1+ε)ⁿ`
      have hQ2 : ∫ y in (Q : Set (Euclid P)), f y ∂μHE[n] ≤ w * (1 + ε) ^ n := by
        rw [← hplanereal (1 + ε) (by linarith [hε.1]), ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hdomint _ _ (1 + ε) hfc (hplanefin _ (by linarith [hε.1])) hf0 hfle)
          (hindint _ _ (hplanefin _ (by linarith [hε.1]))) hfle
      filter_upwards [(tendsto_order.1 (hconv f)).2 c (hQ2.trans_lt hcε),
        Ioc_mem_nhdsGT (half_pos hs)] with r hr1 hr2
      -- `a r ≤ ∫_{η(M)} f`
      have h1 : (1 : ℝ) * r ≤ s := by linarith [hr2.2]
      have h2 : (1 + ε) * r ≤ s := by nlinarith [hr2.1, hr2.2, hε.2]
      have hge : a r ≤ ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n] := by
        rw [← hareal r hr2.1, ← integral_indicator_one measurableSet_closedBall]
        exact integral_mono (hindint _ _ (hνfin r hr2.1 1 h1))
          (hdomint _ _ (1 + ε) hfc (hνfin r hr2.1 _ h2) hf0 hfle) hfge
      exact hge.trans_lt hr1
  -- Step 8: back to the `ℝ≥0∞` quotient
  have hconvert : ∀ ρ : ℝ, 0 < ρ → ρ ≤ s →
      μHE[n] (M ∩ closedBall x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) = ENNReal.ofReal (a ρ / w) := by
    intro ρ hρ hρs
    have hρn : 0 < ρ ^ n := pow_pos hρ n
    rw [← ENNReal.ofReal_toReal (hmfin ρ hρs), ← ENNReal.ofReal_toReal hωtop,
      ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ← ENNReal.ofReal_div_of_pos (mul_pos hw hρn)]
    congr 1
    simp only [hadef, inv_pow]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => ENNReal.ofReal (a ρ / w)) (𝓝[>] 0) (𝓝 1) := by
    have := ENNReal.tendsto_ofReal (ha.div_const w)
    rwa [div_self hw.ne', ENNReal.ofReal_one] at this
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT hs] with ρ hρ
  exact (hconvert ρ hρ.1 hρ.2).symm
/-- **Simon Ch. 1, 3.16–3.17 with 3.11(3)**, localized to an open `U`: if `μ` and
`ν = μ.withDensity θ` (`θ` Borel) are finite on compact subsets of `U`, then
`ν(B̄_ρ(x))/μ(B̄_ρ(x)) → θ(x)` as `ρ ↓ 0` for `μ`-a.e. `x ∈ U`.  Besicovitch differentiation
(`Besicovitch.ae_tendsto_rnDeriv`, `Measure.rnDeriv_withDensity`) is applied to `μ⌞Kⱼ` and
`ν⌞Kⱼ = (μ⌞Kⱼ).withDensity θ` for the compact exhaustion
`Kⱼ = B̄_{j+1}(0) ∩ {y : dist(y, z) ≥ 1/(j+1) for all z ∉ U}` of `U`; each `x ∈ U` has
`B_{1/(j+1)}(x) ⊆ Kⱼ` for some `j`, and there the localized ball ratios are the global ones. -/
theorem Submission.rsd_ae_tendsto_withDensity_div_closedBall : ∀ (P : ℕ) (U : Set (Euclid P)) (μ : Measure (Euclid P)) (θ : Euclid P → ℝ≥0∞), IsOpen U → Measurable θ → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞) → ∀ᵐ x ∂μ, x ∈ U → Tendsto (fun ρ : ℝ => μ.withDensity θ (closedBall x ρ) / μ (closedBall x ρ)) (𝓝[>] 0) (𝓝 (θ x)) := by
  intro P U μ θ hU hθ hμK hνK
  -- the compact exhaustion `K j`
  set K : ℕ → Set (Euclid P) := fun j =>
    closedBall 0 ((j : ℝ) + 1) ∩ {y | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} with hKdef
  have hKclosed' : ∀ j : ℕ, IsClosed {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} := by
    intro j
    have : {y : Euclid P | ∀ z ∉ U, 1 / ((j : ℝ) + 1) ≤ dist y z} =
        ⋂ z ∈ Uᶜ, {y | 1 / ((j : ℝ) + 1) ≤ dist y z} := by
      ext y; simp
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hKclosed : ∀ j, IsClosed (K j) := fun j => isClosed_closedBall.inter (hKclosed' j)
  have hKcpt : ∀ j, IsCompact (K j) := fun j =>
    (isCompact_closedBall (0 : Euclid P) _).inter_right (hKclosed' j)
  have hKU : ∀ j, K j ⊆ U := by
    intro j y hy
    by_contra hyU
    have h := hy.2 y hyU
    rw [dist_self] at h
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  have hcover : ∀ x ∈ U, ∃ j : ℕ, ball x (1 / ((j : ℝ) + 1)) ⊆ K j := by
    intro x hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨j, hj⟩ := exists_nat_gt (max (2 / δ) ‖x‖)
    have hj1 : 2 / δ < (j : ℝ) + 1 := by
      have := le_max_left (2 / δ) ‖x‖; linarith
    have hj2 : ‖x‖ < (j : ℝ) := lt_of_le_of_lt (le_max_right _ _) hj
    have hjpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hsmall : 2 / ((j : ℝ) + 1) < δ := by
      rw [div_lt_iff₀ hjpos]
      rw [div_lt_iff₀ hδ] at hj1
      linarith
    refine ⟨j, fun y hy => ⟨?_, ?_⟩⟩
    · rw [mem_closedBall, dist_zero_right]
      have h1 : ‖y‖ ≤ ‖x‖ + dist y x := by
        have := norm_le_norm_add_norm_sub' y x
        rw [dist_eq_norm]; linarith [norm_sub_rev y x]
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have h3 : 1 / ((j : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hjpos]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
      linarith
    · intro z hz
      have hxz : δ ≤ dist x z := by
        by_contra h
        exact hz (hball (by rw [mem_ball, dist_comm]; linarith))
      have h2 : dist y x < 1 / ((j : ℝ) + 1) := hy
      have htri := dist_triangle x y z
      have h4 : 2 / ((j : ℝ) + 1) = 2 * (1 / ((j : ℝ) + 1)) := by ring
      rw [dist_comm] at h2
      linarith
  -- Besicovitch on each `K j`
  have hj : ∀ j : ℕ, ∀ᵐ x ∂μ, x ∈ K j → Tendsto (fun ρ : ℝ =>
      ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
      (𝓝[>] 0) (𝓝 (θ x)) := by
    intro j
    have hKm : MeasurableSet (K j) := (hKclosed j).measurableSet
    have : IsFiniteMeasure (μ.restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hμK _ (hKcpt j) (hKU j)).lt_top⟩
    have : IsFiniteMeasure ((μ.withDensity θ).restrict (K j)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact (hνK _ (hKcpt j) (hKU j)).lt_top⟩
    have h1 := Besicovitch.ae_tendsto_rnDeriv ((μ.withDensity θ).restrict (K j)) (μ.restrict (K j))
    have h2 := Measure.rnDeriv_withDensity (μ.restrict (K j)) hθ
    rw [← restrict_withDensity hKm] at h2
    have h3 : ∀ᵐ x ∂(μ.restrict (K j)), Tendsto (fun ρ : ℝ =>
        ((μ.withDensity θ).restrict (K j)) (closedBall x ρ) / (μ.restrict (K j)) (closedBall x ρ))
        (𝓝[>] 0) (𝓝 (θ x)) := by
      filter_upwards [h1, h2] with x hx1 hx2
      rwa [hx2] at hx1
    exact (ae_restrict_iff' hKm).1 h3
  filter_upwards [ae_all_iff.2 hj] with x hx hxU
  obtain ⟨j, hjK⟩ := hcover x hxU
  have hr : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hxK : x ∈ K j := hjK (mem_ball_self hr)
  refine (hx j hxK).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hr] with ρ hρ
  have hsub : closedBall x ρ ⊆ K j := (closedBall_subset_ball hρ.2).trans hjK
  rw [Measure.restrict_apply measurableSet_closedBall, Measure.restrict_apply measurableSet_closedBall,
    inter_eq_left.2 hsub]
/-- **Simon Ch. 1, 3.1–3.2** (densities may be computed with closed or open balls; cf. 6.2.8 and
`HasMassDensity`): if `ν(B̄_ρ(x)) / (ωₙρⁿ) → θ ∈ [0, ∞]` as `ρ ↓ 0`, then also
`ν(B_ρ(x)) / (ωₙρⁿ) → θ`.  The upper bound follows from `B_ρ(x) ⊆ B̄_ρ(x)`.  For the lower
bound, given `a < θ` pick `t ∈ (0, 1)` with `a < tⁿθ`; then `B̄_{tρ}(x) ⊆ B_ρ(x)` and
`ωₙ(tρ)ⁿ = tⁿ ωₙρⁿ` give `ν(B_ρ(x)) / (ωₙρⁿ) ≥ tⁿ · ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) > a` for small
`ρ`. -/
theorem Submission.rsd_tendsto_ball_density_of_closedBall : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (x : Euclid P) (θ : ℝ≥0∞), Tendsto (fun ρ : ℝ => ν (closedBall x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) → Tendsto (fun ρ : ℝ => ν (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 θ) := by
  intro P n ν x θ hg
  set ω := unitBallVolume n
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- Step 2: choose `t ∈ (0, 1)` with `a < tⁿθ`, using `tⁿθ → θ` as `t ↑ 1`
    have hlim : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n) * θ) (𝓝[<] 1) (𝓝 (1 * θ)) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
      have : Tendsto (fun t : ℝ => ENNReal.ofReal (t ^ n)) (𝓝 1) (𝓝 (ENNReal.ofReal (1 ^ n))) :=
        (ENNReal.continuous_ofReal.comp (continuous_pow n)).tendsto 1
      simpa using this.mono_left nhdsWithin_le_nhds
    rw [one_mul] at hlim
    obtain ⟨t, hta, ht0, ht1⟩ : ∃ t : ℝ, a < ENNReal.ofReal (t ^ n) * θ ∧ 0 < t ∧ t < 1 := by
      have h1 := (tendsto_order.1 hlim).1 a ha
      have h2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨t, ht, ht'⟩ := (h1.and h2).exists
      exact ⟨t, ht, ht'.1, ht'.2⟩
    have hc0 : ENNReal.ofReal (t ^ n) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hctop : ENNReal.ofReal (t ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
    have ha' : a / ENNReal.ofReal (t ^ n) < θ := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop), mul_comm]
      exact hta
    -- Step 3: the rescaled closed-ball ratio `g(tρ)` still tends to `θ`
    have hmap : Tendsto (fun ρ : ℝ => t * ρ) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h0 : Tendsto (fun ρ : ℝ => t * ρ) (𝓝 0) (𝓝 0) := by
          simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul t
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ρ hρ
        exact mul_pos ht0 hρ
    have hev := (tendsto_order.1 (hg.comp hmap)).1 _ ha'
    filter_upwards [hev, self_mem_nhdsWithin] with ρ hρ hρpos
    simp only [Function.comp] at hρ
    have hρpos' : (0 : ℝ) < ρ := hρpos
    -- Step 4: `ν(B̄_{tρ}(x)) / (ωₙ(tρ)ⁿ) · tⁿ = ν(B̄_{tρ}(x)) / (ωₙρⁿ)`
    have hid : ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n)
        = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := by
      rw [mul_pow, ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (t ^ n)),
        ← mul_assoc, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inr hctop) (Or.inr hc0),
        mul_assoc, mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    -- Step 5: `a < tⁿ g(tρ) ≤ h(ρ)`, as `B̄_{tρ}(x) ⊆ B_ρ(x)`
    calc a = a / ENNReal.ofReal (t ^ n) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.div_mul_cancel hc0 hctop).symm
      _ < ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal ((t * ρ) ^ n)) * ENNReal.ofReal (t ^ n) :=
          (ENNReal.mul_lt_mul_iff_left hc0 hctop).2 hρ
      _ = ν (closedBall x (t * ρ)) / (ω * ENNReal.ofReal (ρ ^ n)) := hid
      _ ≤ ν (ball x ρ) / (ω * ENNReal.ofReal (ρ ^ n)) := by
          gcongr
          exact closedBall_subset_ball (by nlinarith)
  · -- Step 1: `h(ρ) ≤ g(ρ)`, as `B_ρ(x) ⊆ B̄_ρ(x)`
    filter_upwards [(tendsto_order.1 hg).2 b hb] with ρ hρ
    refine lt_of_le_of_lt ?_ hρ
    gcongr
    exact ball_subset_closedBall
/-- Local finiteness of an integer multiplicity representation `(M, θ, ξ)` in `U` (Simon Ch. 6,
Definition 3.1).  For compact `K ⊆ U`, `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞` by the local integrability
of `θ`, and `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞` since `θ ≥ 1` on `M`. -/
theorem Submission.rsd_imrep_compact_measure_ne_top : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ ∧ R.measure K ≠ ∞ := by
  intro P n U R K hK hKU
  have hint := R.locallyIntegrable_mult K hK hKU
  -- `μ_R(K) = ∫_K θ d(Hⁿ⌞M) = ∫_{M ∩ K} θ dHⁿ`, `K` being closed, hence Borel
  have hmeas : R.measure K = ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
  refine ⟨?_, by rw [hmeas]; exact hint⟩
  refine ne_top_of_le_ne_top hint ?_
  -- `Hⁿ(M ∩ K) = ∫_{M ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ`, as `1 ≤ θ` on `M`
  calc μHE[n] (R.carrier ∩ K) = ∫⁻ _ in R.carrier ∩ K, (1 : ℝ≥0∞) ∂μHE[n] := by
        rw [setLIntegral_one]
    _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
        refine setLIntegral_mono (measurable_from_nat.comp R.measurable_mult) ?_
        intro x hx
        exact_mod_cast R.mult_pos x hx.1
/-- A unit orientation has operator norm at most `1` (step 1(c) of the proof that the weight of
`T = τ(M, θ, ξ)` is at most its mass).  If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`,
then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖` for every `n`-covector `α`, so `‖ξ‖ ≤ 1`. -/
theorem Submission.rsd_mw_wlm_orient_opNorm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
  rintro P n Q ξ ⟨τ, hτ, -, hξ⟩
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun α => ?_
  -- `|α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`, as `‖τᵢ‖ = 1`
  have hbound : ‖α τ‖ ≤ ‖α‖ := by
    simpa [hτ.1] using α.le_opNorm τ
  rcases hξ with h | h
  · rw [h, one_mul]
    exact hbound
  · rw [h, norm_neg, one_mul]
    exact hbound
/-- An open `W ⊆ U` with `c < μ(W)`, `μ = θ Hⁿ⌞M`, contains an open `V` with `c < μ(V) < ∞`
(step 3 of the proof that the weight of `T = τ(M, θ, ξ)` is at most its mass).  Inner regularity
gives a compact `K ⊆ W` with `c < μ(K)`; an open `V ⊇ K` with compact `closure V ⊆ W` has
`μ(V) ≥ μ(K) > c` and `μ(V) ≤ μ(closure V) = ∫⁻_{M ∩ closure V} θ dHⁿ < ∞`. -/
theorem Submission.rsd_mw_wlm_exists_open_measure_between : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (W : Set (Euclid P)), IsOpen W → W ⊆ U → ∀ c : ℝ≥0∞, c < R.measure W → ∃ V : Set (Euclid P), IsOpen V ∧ V ⊆ W ∧ c < R.measure V ∧ R.measure V < ∞ := by
  intro P n U R W hW hWU c hc
  -- open sets are inner regular for closed sets, and closed sets for compact sets
  obtain ⟨K, hKW, hK, hcK⟩ := ((Measure.InnerRegularWRT.isCompact_isClosed R.measure).trans
    (Measure.InnerRegularWRT.of_pseudoMetrizableSpace R.measure)) hW c hc
  obtain ⟨V, hVo, hKV, hVW, hVc⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  refine ⟨V, hVo, subset_closure.trans hVW, hcK.trans_le (measure_mono hKV), ?_⟩
  -- `μ(closure V) = ∫⁻_{M ∩ closure V} θ dHⁿ`, finite as `closure V` is a compact subset of `U`
  have hcl : R.measure (closure V) ≠ ∞ := by
    unfold IMRep.measure
    rw [withDensity_apply _ isClosed_closure.measurableSet,
      Measure.restrict_restrict isClosed_closure.measurableSet, Set.inter_comm]
    exact R.locallyIntegrable_mult _ hVc (hVW.trans hWU)
  exact (measure_mono subset_closure).trans_lt hcl.lt_top
/-- A continuous linear image of an a.e. unit-bounded measurable `n`-vector field is integrable:
if `ν` is finite, `ξ` is `ν`-a.e. strongly measurable with `‖ξ x‖ ≤ 1` for `ν`-a.e. `x`, and
`J : MultiVector P n →L[ℝ] Covector (Euclid P) n`, then `x ↦ J (ξ x)` is `ν`-integrable.
Continuity of `J` at `0` gives `δ > 0` with `‖J w‖ < 1` whenever `‖w‖ < δ`; applied to
`(δ / 2) • w`, homogeneity gives `‖J w‖ ≤ 2 / δ` on the closed unit ball.  Hence `J ∘ ξ` is
a.e. strongly measurable and a.e. dominated by the constant `2 / δ`, which is `ν`-integrable as
`ν` is finite. -/
theorem Submission.rsd_mw_wlm_integrable_clm_comp : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (J : MultiVector P n →L[ℝ] Covector (Euclid P) n), IsFiniteMeasure ν → AEStronglyMeasurable ξ ν → (∀ᵐ x ∂ν, ‖ξ x‖ ≤ 1) → Integrable (fun x => J (ξ x)) ν := by
  intro P n ν ξ J hν hξ hξ1
  obtain ⟨δ, hδ, hJδ⟩ : ∃ δ > 0, ∀ w : MultiVector P n, ‖w‖ < δ → ‖J w‖ < 1 := by
    have hJc : @Continuous (MultiVector P n) (Covector (Euclid P) n)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace J := J.continuous
    obtain ⟨δ, hδ, h⟩ := Metric.continuous_iff.1 hJc 0 1 one_pos
    refine ⟨δ, hδ, fun w hw => ?_⟩
    have h' := h w (by convert hw using 1; exact dist_zero_right w)
    convert h' using 1
    rw [map_zero]
    exact (dist_zero_right _).symm
  have hbound : ∀ w : MultiVector P n, ‖w‖ ≤ 1 → ‖J w‖ ≤ 2 / δ := by
    intro w hw
    have h2 : ‖(δ / 2) • w‖ < δ := by
      calc ‖(δ / 2) • w‖ ≤ ‖δ / 2‖ * ‖w‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ δ / 2 * 1 := by
          rw [Real.norm_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left hw (by positivity)
        _ < δ := by linarith
    have := hJδ _ h2
    rw [map_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at this
    rw [le_div_iff₀ hδ]
    nlinarith
  refine Integrable.mono' (integrable_const (2 / δ)) (J.continuous.comp_aestronglyMeasurable hξ) ?_
  filter_upwards [hξ1] with x hx using hbound _ hx
/-- If `T = τ(M, θ, ξ)` and `spt ω ⊆ V`, then `T(ω) = ∫ ⟨ω, ξ⟩ d(μ⌞V)` with `μ = θ Hⁿ⌞M`
(step 7 of the proof that the weight of `T = τ(M, θ, ξ)` is at most its mass).  The integrand
vanishes off `spt ω ⊆ V`, so restricting `μ` to `V` changes nothing; writing the density `θ` as
a measurable `ℝ≥0`-valued function turns `∫ ⟨ω, ξ⟩ dμ` into `∫_M θ ⟨ω, ξ⟩ dHⁿ = T(ω)`. -/
theorem Submission.rsd_mw_wlm_eval_eq_integral_restrict : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ (V : Set (Euclid P)) (ω : TestFormOn U n), tsupport (ω : DifferentialForm (Euclid P) n) ⊆ V → T ω = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂(R.measure.restrict V) := by
  intro P n U T R hR V ω hωV
  rw [hR ω, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · -- `μ = (Hⁿ⌞M).withDensity θ` with `θ` read as a measurable `ℝ≥0`-valued density
    have hμ : R.measure = (μHE[n].restrict R.carrier).withDensity
        (fun x => ((R.mult x : NNReal) : ℝ≥0∞)) := by
      simp [IMRep.measure]
    have hmeas : Measurable fun x => (R.mult x : NNReal) :=
      measurable_from_nat.comp R.measurable_mult
    rw [hμ, integral_withDensity_eq_integral_smul hmeas]
    simp [IMRep.action, NNReal.smul_def]
  · -- off `V`, hence off `spt ω`, the form vanishes and so does `⟨ω, ξ⟩`
    intro x hx
    have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hx (hωV h)
    simp [h0]
/-- Integral lower bound for `⟨ω, ξ⟩` from an `L¹`-close dual field.  Write
`N = covectorEuclideanNorm`.  Let `ν` be finite, `ξ` `ν`-a.e. strongly measurable and `ω`
continuous with `N (ω x) ≤ 1`; suppose that, for `ν`-a.e. `x`, `|ξ x α| ≤ N α` for every `α` and
`ξ x (β x) = 1`.  If `∫⁻ N (ω − β) dν < ε`, then `ν(ℝᴾ) − ε < ∫ ξ(ω) dν`.
The function `h = ξ(ω)` is a.e. strongly measurable (continuous bilinear evaluation) and a.e.
bounded by `N ∘ ω ≤ 1`, hence integrable.  A.e., `h ≤ 1` and
`h = ξ(β) + ξ(ω − β) ≥ 1 − N (ω − β)`, so `0 ≤ 1 − h ≤ N (ω − β)`.  Therefore
`ofReal (∫ (1 − h) dν) = ∫⁻ ofReal (1 − h) dν ≤ ∫⁻ ofReal (N (ω − β)) dν < ofReal ε`, whence
`ν(ℝᴾ) − ∫ h dν = ∫ (1 − h) dν < ε`.  No measurability of `β` is needed: the comparison is made
only between lower integrals. -/
theorem Submission.rsd_mw_wlm_sub_lt_integral : ∀ (P n : ℕ) (ν : Measure (Euclid P)) (ξ : Euclid P → MultiVector P n) (β ω : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsFiniteMeasure ν → AEStronglyMeasurable ξ ν → Continuous ω → (∀ x, covectorEuclideanNorm (ω x) ≤ 1) → (∀ᵐ x ∂ν, (∀ α : Covector (Euclid P) n, |ξ x α| ≤ covectorEuclideanNorm α) ∧ ξ x (β x) = 1) → ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν < ENNReal.ofReal ε → (ν univ).toReal - ε < ∫ x, ξ x (ω x) ∂ν := by
  intro P n ν ξ β ω ε hν hξ hω hωN hG hlt
  have hhm : AEStronglyMeasurable (fun x => ξ x (ω x)) ν :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hξ.prodMk hω.aestronglyMeasurable)
  have hh_int : Integrable (fun x => ξ x (ω x)) ν := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hhm ?_
    filter_upwards [hG] with x hx
    rw [Real.norm_eq_abs]
    exact (hx.1 (ω x)).trans (hωN x)
  have hpt : ∀ᵐ x ∂ν, 0 ≤ 1 - ξ x (ω x) ∧
      1 - ξ x (ω x) ≤ covectorEuclideanNorm (ω x - β x) := by
    filter_upwards [hG] with x hx
    have hsplit : ξ x (ω x) = ξ x (β x) + ξ x (ω x - β x) := by
      rw [← map_add, add_sub_cancel]
    have h1 := (abs_le.1 ((hx.1 (ω x)).trans (hωN x))).2
    have h2 := (abs_le.1 (hx.1 (ω x - β x))).1
    constructor
    · linarith
    · rw [hsplit, hx.2]
      linarith
  have h1h_int : Integrable (fun x => 1 - ξ x (ω x)) ν := (integrable_const 1).sub hh_int
  have hint_eq : ∫ x, (1 - ξ x (ω x)) ∂ν = (ν univ).toReal - ∫ x, ξ x (ω x) ∂ν := by
    rw [integral_sub (integrable_const 1) hh_int, integral_const, smul_eq_mul, mul_one,
      measureReal_def]
  have hofreal : ENNReal.ofReal (∫ x, (1 - ξ x (ω x)) ∂ν) < ENNReal.ofReal ε := by
    rw [ofReal_integral_eq_lintegral_ofReal h1h_int (hpt.mono fun x hx => hx.1)]
    calc ∫⁻ x, ENNReal.ofReal (1 - ξ x (ω x)) ∂ν
        ≤ ∫⁻ x, ENNReal.ofReal (covectorEuclideanNorm (ω x - β x)) ∂ν :=
          lintegral_mono_ae (hpt.mono fun x hx => ENNReal.ofReal_le_ofReal hx.2)
      _ < ENNReal.ofReal ε := hlt
  have hlt' := (ENNReal.ofReal_lt_ofReal_iff'.1 hofreal).1
  linarith
/-- **Simon Ch. 6, Remark 2.6(a)–(b)** for the Euclidean coefficient norm: a unit orientation
`ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal) has `|ξ(α)| ≤ |α|`, and the single continuous linear map
`J(w) = Σ_I w(e^I) e^I` (`I` strictly increasing) has `|J(ξ)| = 1` and `ξ(J(ξ)) = 1`.  Here
`e^I(v) = det(⟨e_{I(k)}, vⱼ⟩)`, every covector expands as `α = Σ_I α(e_I) e^I`, and
`e^I(e_K) = δ_IK`.  Expanding `γ(v) = det(⟨τₖ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet identity
`Σ_I e^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.rsd_mw_unit_orientation_dual : ∀ (P n : ℕ), ∃ J : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (J ξ) = 1 ∧ ξ (J ξ) = 1 := by
  intro P n
  -- `D u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`, a continuous alternating map as an
  -- alternatization; `e^I = D (e ∘ I)` and `γ = D τ`
  let D : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hD : ∀ u v, D u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [D, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `D u v = D v u` (determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hDsymm : ∀ u v, D u v = D v u := by
    intro u v
    rw [hD, hD]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `D u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hD1 : ∀ u, Orthonormal ℝ u → D u u = 1 := by
    intro u hu
    rw [hD, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- step 2: `e^I(e_K) = δ_IK` for strictly increasing `I`, `K`; a nonzero term forces
  -- `K ∘ σ = I`, so `range I = range K` and `I = K`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I K : Fin n → Fin P, StrictMono I → StrictMono K →
      D (fun k => e (I k)) (fun k => e (K k)) = if I = K then 1 else 0 := by
    intro I K hI hK
    split_ifs with hIK
    · subst hIK
      exact hD1 _ (e.orthonormal.comp I hI.injective)
    · rw [hD]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIK
      have hKσ : K ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← StrictMono.range_inj_of_wellFoundedLT hI hK, ← hKσ, EquivLike.range_comp]
  -- step 1: `α = Σ_{I ∈ S} α(e_I) e^I`; both sides are alternating, so compare them on `e ∘ f`
  -- for injective `f`, and write `f = (f ∘ σ) ∘ σ⁻¹` with `f ∘ σ` strictly increasing
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • D (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hfσ : StrictMono (f ∘ σ) :=
      (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
    have hperm : ∀ β : Covector (Euclid P) n,
        β (fun k => e (f k)) = Equiv.Perm.sign σ⁻¹ • β (fun k => e ((f ∘ σ) k)) := by
      intro β
      have : (fun k => e (f k)) = (fun k => e ((f ∘ σ) k)) ∘ ⇑(σ⁻¹) := by
        funext k
        simp
      rw [this]
      exact β.toAlternatingMap.map_perm _ _
    rw [hperm α, hperm, ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (f ∘ σ)]
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hfσ hfσ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIf
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hfσ,
        ite_eq_right hIf, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfσ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- step 3 (Cauchy–Binet): `Σ_{I ∈ S} e^I(τ)² = 1` for orthonormal `τ`; evaluate the expansion
  -- of `γ = D τ` at `τ`, using `γ(τ) = 1` and `γ(e_I) = e^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (D τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hD1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hDsymm τ, sq]
  -- step 4: `J w = Σ_{I ∈ S} w(e^I) e^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (D fun k => e (I k))).smulRight
    (D fun k => e (I k)), ?_⟩
  have hJ : ∀ w : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (D fun k => e (I k))).smulRight (D fun k => e (I k))) w =
      ∑ I ∈ S, w (D fun k => e (I k)) • D fun k => e (I k) := by
    intro w
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.apply_apply]
  -- step 5: `ξ(α) = s α(τ)` with `s = ±1`
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  have hξ2 : ∀ α β : Covector (Euclid P) n, ξ α * ξ β = α τ * β τ := by
    intro α β
    rcases hξ with h | h
    · rw [h, h]
    · rw [h, h, neg_mul_neg]
  have hξabs : ∀ α : Covector (Euclid P) n, |ξ α| = |α τ| := by
    intro α
    rcases hξ with h | h
    · rw [h]
    · rw [h, abs_neg]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (i) `|ξ(α)| = |Σ_I α(e_I) e^I(τ)| ≤ |α| (Σ_I e^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * D (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, D (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (ii) `J(ξ)(e_K) = ξ(e^K)`, so `|J(ξ)|² = Σ_K ξ(e^K)² = Σ_K e^K(τ)² = 1`
    rw [hnorm, hJ]
    have : ∑ K ∈ S, (∑ I ∈ S, ξ (D fun k => e (I k)) • D fun k => e (I k))
        (fun k => e (K k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun K hK' => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single K]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hK').2
          (Finset.mem_filter.mp hK').2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIK
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hK').2, ite_eq_right hIK, smul_zero]
      · exact fun h => absurd hK' h
    rw [this, Real.sqrt_one]
  · -- (iii) `ξ(J(ξ)) = Σ_I ξ(e^I)² = Σ_I e^I(τ)² = 1`
    rw [hJ, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]

/-- **Simon Ch. 6, Remark 3.2(3), `≤` half** (with 2.5 and Remark 2.6(a)): `M_W(T) ≤ μ_T(W)` for
`T = τ(M, θ, ξ)` and every `W ⊆ ℝᴾ`.  Let `ω` be admissible: `spt ω ⊆ W`, `|ω| ≤ 1`.  At `Hⁿ`-a.e.
`x ∈ M`, `ξ(x)` is a unit simple `n`-vector, so `|⟨ω(x), ξ(x)⟩| ≤ |ω(x)| ≤ 1`; and `ω(x) = 0` off
`spt ω`.  Hence `T(ω) ≤ ∫_M θ|⟨ω, ξ⟩| dHⁿ ≤ ∫_{M ∩ spt ω} θ dHⁿ = μ_T(spt ω) ≤ μ_T(W)`.  Openness of
`U` and `W` and the local integrability of `θ` are not used. -/
theorem Submission.rsd_mw_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hT W
  obtain ⟨J, hJ⟩ := Submission.rsd_mw_unit_orientation_dual P n
  -- `|⟨α, ξ(x)⟩| ≤ |α|` at `Hⁿ`-a.e. `x ∈ M`, where `ξ(x)` is a unit simple `n`-vector
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hJ (R.orient x) Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  show ENNReal.ofReal (T ω) ≤ R.measure W
  set S := tsupport (ω : DifferentialForm (Euclid P) n)
  have hS : MeasurableSet S := (isClosed_tsupport _).measurableSet
  rw [hT ω, IMRep.action]
  calc _ ≤ ‖∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
          ∂μHE[n]‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (le_abs_self _)
    _ ≤ ∫⁻ x in R.carrier,
          ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ₑ ∂μHE[n] :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x in R.carrier, S.indicator (fun x => (R.mult x : ℝ≥0∞)) x ∂μHE[n] := by
        refine lintegral_mono_ae ?_
        filter_upwards [hξ] with x hx
        by_cases hxS : x ∈ S
        · -- `|θ⟨ω, ξ⟩| ≤ θ|ω| ≤ θ` on `spt ω`
          rw [indicator_of_mem hxS, enorm_mul, Real.enorm_natCast, Real.enorm_eq_ofReal_abs]
          exact mul_le_of_le_one_right zero_le
            (ENNReal.ofReal_le_one.2 ((hx _).trans (hω1 x)))
        · -- `ω = 0` off `spt ω`
          rw [indicator_of_notMem hxS, image_eq_zero_of_notMem_tsupport hxS, map_zero, mul_zero,
            enorm_zero]
    _ = R.measure S := by rw [lintegral_indicator hS, IMRep.measure, withDensity_apply _ hS]
    _ ≤ R.measure W := measure_mono hωW
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

/-- **Simon Ch. 6, Remark 3.2(3), `≥` half** (with 2.5 and Remark 2.6(a)–(b)): `μ_T(W) ≤ M_W(T)`
for `T = τ(M, θ, ξ)` and open `W ⊆ U`.  Given `c < μ_T(W)`, take an open `V ⊆ W` with
`c < μ_T(V) < ∞` and put `ν = μ_T⌞V`.  With `J` as in `Submission.rsd_mw_unit_orientation_dual`,
`β = J ∘ ξ` is `ν`-integrable, and `ν`-a.e. `|β| = 1`, `⟨β, ξ⟩ = 1` and `|⟨α, ξ⟩| ≤ |α|`.  A test
form `ω` with `spt ω ⊆ V`, `|ω| ≤ 1` and `∫ |ω − β| dν < ε = (μ_T(V) − c)/2` is admissible for
`M_W(T)`, and `T(ω) = ∫ ⟨ω, ξ⟩ dν > ν(ℝᴾ) − ε = (μ_T(V) + c)/2 > c`. -/
theorem Submission.rsd_mw_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), IsOpen W → W ⊆ U → R.measure W ≤ T.massOn W := by
  intro P n U T R hT W hW hWU
  obtain ⟨J, hJ⟩ := Submission.rsd_mw_unit_orientation_dual P n
  -- it suffices to show `c < M_W(T)` for every `c < μ_T(W)`
  refine le_of_forall_lt fun c hcW => ?_
  -- an open `V ⊆ W` with `c < μ_T(V) < ∞`
  obtain ⟨V, hV, hVW, hcV, hVfin⟩ :=
    Submission.rsd_mw_wlm_exists_open_measure_between P n U R W hW hWU c hcW
  -- `ν = μ_T⌞V` is finite, vanishes off `V`, and `ν ≪ μ_T ≪ Hⁿ⌞M`
  set ν := R.measure.restrict V with hν
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hVfin.ne
  have hνVc : ν Vᶜ = 0 := by
    rw [hν, Measure.restrict_apply' hV.measurableSet, compl_inter_self, measure_empty]
  have hμac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hνac : ν ≪ μHE[n].restrict R.carrier :=
    Measure.restrict_le_self.absolutelyContinuous.trans hμac
  -- `ν`-a.e. `ξ(x)` is a unit orientation
  have hG : ∀ᵐ x ∂ν, ∃ Q : Submodule ℝ (Euclid P), IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [hνac.ae_le R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact ⟨Q, hQ⟩
  have hξ : AEStronglyMeasurable R.orient ν := R.aestronglyMeasurable_orient.mono_ac hνac
  -- `β = J ∘ ξ` is `ν`-integrable, as `‖ξ‖ ≤ 1` `ν`-a.e., and `|β| ≤ 1` `ν`-a.e.
  have hβ : Integrable (fun x => J (R.orient x)) ν := by
    refine Submission.rsd_mw_wlm_integrable_clm_comp P n ν R.orient J hνfin hξ ?_
    filter_upwards [hG] with x hx
    obtain ⟨Q, hQ⟩ := hx
    exact Submission.rsd_mw_wlm_orient_opNorm_le_one P n Q (R.orient x) hQ
  have hβ1 : ∀ᵐ x ∂ν, covectorEuclideanNorm (J (R.orient x)) ≤ 1 := by
    filter_upwards [hG] with x hx
    obtain ⟨Q, hQ⟩ := hx
    exact (hJ _ Q hQ).2.1.le
  -- `c < ∞`, and `ε = (μ_T(V) − c)/2 > 0` in `ℝ`
  have hctop : c ≠ ∞ := ne_top_of_lt hcV
  have hcV' : c.toReal < (R.measure V).toReal := (ENNReal.toReal_lt_toReal hctop hVfin.ne).2 hcV
  set ε := ((R.measure V).toReal - c.toReal) / 2 with hε
  have hε0 : 0 < ε := by linarith
  -- a test form `ω` with `spt ω ⊆ V`, `|ω| ≤ 1` and `∫ |ω − β| dν < ε`
  obtain ⟨ω, hωt, hωV, hω1, hωβ⟩ := Submission.rsd_mw_exists_testForm_approx P n ν V
    (fun x => J (R.orient x)) hνfin hV hνVc hβ hβ1 ε hε0
  -- `ω` is admissible for `M_W(T)`
  let ω' : TestFormOn U n := ⟨ω, hωt, hωV.trans (hVW.trans hWU)⟩
  have hadm : ω' ∈ massAdmissibleOn U n W := ⟨hωV.trans hVW, hω1⟩
  -- `T(ω) = ∫ ⟨ω, ξ⟩ dν > ν(ℝᴾ) − ε`, where `ν(ℝᴾ) = μ_T(V)`
  have hTω : T ω' = ∫ x, R.orient x (ω x) ∂ν :=
    Submission.rsd_mw_wlm_eval_eq_integral_restrict P n U T R hT V ω' hωV
  have hest := Submission.rsd_mw_wlm_sub_lt_integral P n ν R.orient (fun x => J (R.orient x)) ω
    ε hνfin hξ (ContDiff.continuous hωt.1) hω1 (by
      filter_upwards [hG] with x hx
      obtain ⟨Q, hQ⟩ := hx
      exact ⟨(hJ _ Q hQ).1, (hJ _ Q hQ).2.2⟩) hωβ
  have hνuniv : ν univ = R.measure V := Measure.restrict_apply_univ V
  rw [hνuniv] at hest
  have hlt : c.toReal < T ω' := by
    rw [hTω]
    linarith
  -- `c = ofReal c.toReal < ofReal T(ω) ≤ M_W(T)`
  calc c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hctop).symm
    _ < ENNReal.ofReal (T ω') :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hlt
    _ ≤ T.massOn W := T.le_massOn hadm

/-- **Simon Ch. 6, Remark 3.2(3)** (with 2.7–2.8): for `T = τ(M, θ, ξ)` integer multiplicity,
`M_W(T) = μ_T(W) = ∫_{M ∩ W} θ dHⁿ` for every open `W ⊆ U`.  The bound `M_W(T) ≤ μ_T(W)` holds for
every `W` (`Submission.rsd_mw_massOn_le_measure`); the reverse bound tests `T` against smooth
admissible forms approximating the unit covector field dual to `ξ`
(`Submission.rsd_mw_measure_le_massOn`). -/
theorem Submission.rsd_massOn_eq_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W := by
  intro P n U T R _ hT W hW hWU
  exact le_antisymm (Submission.rsd_mw_massOn_le_measure P n U T R hT W)
    (Submission.rsd_mw_measure_le_massOn P n U T R hT W hW hWU)

/-- **Simon Ch. 4, p. 91** (Ch. 3, Remark 1.8(1)–(2) and Theorem 1.9): for an integer multiplicity
`T = τ(M, θ, ξ)` in open `U`, `Θⁿ(μ_T, x) = θ(x)` for `μ_T`-a.e. `x`.  Write `μ = Hⁿ⌞M`, so
`μ_T = θμ`, and let `x ∈ M` be a `μ`-generic point, with `B̄_s(x) ⊆ U`.
* `R.orients` gives an approximate tangent plane at `x`, so `μ(B̄_ρ(x))/(ωₙρⁿ) → 1`
  (`Submission.rsd_tendsto_closedBall_density_of_approxTangent`).  The required local finiteness
  of `μ` and `μ_T` is `Submission.rsd_imrep_compact_measure_ne_top`.
* Localized Besicovitch differentiation gives `μ_T(B̄_ρ(x))/μ(B̄_ρ(x)) → θ(x)`
  (`Submission.rsd_ae_tendsto_withDensity_div_closedBall`).
* For small `ρ`, `0 < μ(B̄_ρ(x)) < ∞`, so the product of the two ratios is
  `μ_T(B̄_ρ(x))/(ωₙρⁿ)`, which tends to `θ(x)`.
* Open balls give the same limit (`Submission.rsd_tendsto_ball_density_of_closedBall`), and
  `M_{B_ρ(x)}(T) = μ_T(B_ρ(x))` once `B_ρ(x) ⊆ U` (`Submission.rsd_massOn_eq_measure`).

Since `μ_T ≪ μ`, the `μ`-a.e. statement holds `μ_T`-a.e. -/
theorem Submission.rsd_ae_hasMassDensity_mult : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ᵐ x ∂R.measure, HasMassDensity T x (R.mult x) := by
  intro P n U T R hU hR
  -- `μ = Hⁿ⌞M` and `θ = R.mult`; by definition `μ_T = R.measure = θμ`
  set μ : Measure (Euclid P) := μHE[n].restrict R.carrier with hμ
  set θ : Euclid P → ℝ≥0∞ := fun x => (R.mult x : ℝ≥0∞)
  have hθm : Measurable θ := measurable_from_nat.comp R.measurable_mult
  have hμK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ K ≠ ∞ := fun K hK hKU => by
    rw [hμ, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
    exact (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1
  have hνK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μ.withDensity θ K ≠ ∞ :=
    fun K hK hKU => (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).2
  -- Besicovitch differentiation of `θμ` with respect to `μ`, at `μ`-a.e. `x ∈ U`
  have hbes := Submission.rsd_ae_tendsto_withDensity_div_closedBall P U μ θ hU hθm hμK hνK
  have key : ∀ᵐ x ∂μ, HasMassDensity T x (R.mult x) := by
    filter_upwards [ae_restrict_mem R.measurableSet_carrier, R.orients, hbes]
      with x hxM hQ hx
    obtain ⟨Q, hxQ, -⟩ := hQ
    have hxU : x ∈ U := R.carrier_subset hxM
    -- a closed ball `B̄_s(x) ⊆ U`; every `B̄_ρ(x)`, `ρ ≤ s`, is a compact subset of `U`
    obtain ⟨s, hs, hsU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hxU)
    have hsub : ∀ ρ : ℝ, ρ ≤ s → closedBall x ρ ⊆ U := fun ρ hρ =>
      (closedBall_subset_closedBall hρ).trans hsU
    -- `μ(B̄_ρ(x))/(ωₙρⁿ) → 1` (approximate tangent plane at `x`)
    have hden := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n R.carrier x Q s hs
      (Submission.rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x s) hsU).1 hxQ
    -- `μ_T(B̄_ρ(x))/(ωₙρⁿ) = [μ_T(B̄_ρ(x))/μ(B̄_ρ(x))] · [μ(B̄_ρ(x))/(ωₙρⁿ)] → θ(x) · 1`
    have hclosed : Tendsto (fun ρ : ℝ => R.measure (closedBall x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (θ x)) := by
      have hprod := ENNReal.Tendsto.mul (hx hxU) (Or.inr ENNReal.one_ne_top) hden
        (Or.inl one_ne_zero)
      rw [mul_one] at hprod
      refine hprod.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hs, hden.eventually_ne one_ne_zero] with ρ hρ hne
      -- `0 < μ(B̄_ρ(x)) < ∞` for small `ρ`
      have hfin : μHE[n] (R.carrier ∩ closedBall x ρ) ≠ ∞ :=
        (Submission.rsd_imrep_compact_measure_ne_top P n U R _ (isCompact_closedBall x ρ)
          (hsub ρ hρ.2.le)).1
      have hpos : μHE[n] (R.carrier ∩ closedBall x ρ) ≠ 0 := fun h0 =>
        hne (by rw [h0, ENNReal.zero_div])
      have hμρ : μ (closedBall x ρ) = μHE[n] (R.carrier ∩ closedBall x ρ) := by
        rw [hμ, Measure.restrict_apply' R.measurableSet_carrier, inter_comm]
      rw [hμρ]
      exact ENNReal.div_mul_div_cancel hpos hfin
    -- open balls, then `M_{B_ρ(x)}(T) = μ_T(B_ρ(x))` for `ρ < s`
    have hopen := Submission.rsd_tendsto_ball_density_of_closedBall P n R.measure x (θ x) hclosed
    refine ⟨Nat.cast_nonneg _, ?_⟩
    rw [ENNReal.ofReal_natCast]
    refine hopen.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hs] with ρ hρ
    rw [Submission.rsd_massOn_eq_measure P n U T R hU hR (ball x ρ) isOpen_ball
      (ball_subset_closedBall.trans (hsub ρ hρ.2.le))]
  -- `μ_T = θμ ≪ μ`
  exact (withDensity_absolutelyContinuous μ θ).ae_le key
/-- **Simon Ch. 1, Theorem 3.3** (comparison theorem, p. 14), with a non-sharp constant and
`Hⁿ = μHE[n]` on `ℝᴺ`: if `ν(B̄_t(x)) ≥ c tⁿ` for all small `t > 0` at every point `x` of a subset
`A` of an open set `O`, then `Hⁿ(A) ≤ C ν(O)` with `C = C(n, c) < ∞`.  At each scale `δ` the
5-times covering lemma (Simon 3.4) selects, among the balls `B̄_r(x) ⊆ O` with `x ∈ A`, `10r ≤ δ`
and `ν(B̄_r(x)) ≥ c rⁿ`, a disjoint, hence countable, subfamily whose 5-times enlargements cover
`A`.  This `δ`-cover costs `Σ (10rⱼ)ⁿ ≤ (10ⁿ/c) Σ ν(B̄_{rⱼ}(xⱼ)) ≤ (10ⁿ/c) ν(O)`, and `μHE[n]` is
a finite multiple of `μH[n]`. -/
theorem Submission.dorag_sn_hausdorff_le_mul_of_lower_density : ∀ (N n : ℕ) (c : ℝ), 0 < c → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ν : Measure (Euclid N)) (A O : Set (Euclid N)), IsOpen O → A ⊆ O → (∀ x ∈ A, ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ → ENNReal.ofReal (c * t ^ n) ≤ ν (closedBall x t)) → μHE[n] A ≤ C * ν O := by
  intro N n c hc
  -- `μHE[n] = k • μH[n]` with a finite factor `k`; take `C = k · 10ⁿ / c`
  set k : NNReal :=
    Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n))) μH[(n : ℝ)]
  refine ⟨(k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top, ?_⟩
  intro ν A O hO hAO hA
  have hdiam : ∀ (y : Euclid N) (ρ : ℝ), ediam (closedBall y ρ) ≤ ENNReal.ofReal (2 * ρ) := by
    intro y ρ
    apply ediam_le_of_forall_dist_le
    intro z hz w hw
    rw [mem_closedBall] at hz hw
    linarith [dist_triangle_right z w y]
  -- scale `δ = 1 / (m + 1)`: a countable disjoint family of admissible balls whose 5-times
  -- enlargements cover `A`, of total cost at most `(10ⁿ/c) ν(O)`
  have step : ∀ m : ℕ, ∃ u : Set (Euclid N × ℝ), u.Countable ∧
      (∀ p ∈ u, ediam (closedBall p.1 (5 * p.2)) ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1))) ∧
      A ⊆ ⋃ p : u, closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2) ∧
      ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) ≤
        ENNReal.ofReal (10 ^ n / c) * ν O := by
    intro m
    set δ : ℝ := 1 / ((m : ℝ) + 1)
    have hδpos : 0 < δ := by positivity
    -- the admissible balls, as (center, radius) pairs
    set T : Set (Euclid N × ℝ) := {p | p.1 ∈ A ∧ 0 < p.2 ∧ 10 * p.2 ≤ δ ∧
      closedBall p.1 p.2 ⊆ O ∧ ENNReal.ofReal (c * p.2 ^ n) ≤ ν (closedBall p.1 p.2)}
    obtain ⟨u, huT, hudisj, hucov⟩ :=
      Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun p => p.1)
        (fun p => p.2) δ (fun p hp => by linarith [hp.2.2.1, hp.2.1]) 5 (by norm_num)
    -- disjoint balls with nonempty interiors in the separable space `ℝᴺ`
    have hucount : u.Countable := by
      refine hudisj.countable_of_nonempty_interior fun p hp => ?_
      exact ⟨p.1, ball_subset_interior_closedBall (mem_ball_self (huT hp).2.1)⟩
    refine ⟨u, hucount, fun p hp => ?_, ?_, ?_⟩
    · obtain ⟨-, -, hpδ, -, -⟩ := huT hp
      refine (hdiam _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith
    · -- each `x ∈ A` is the center of a small admissible ball
      intro x hx
      obtain ⟨t₀, ht₀, hbound⟩ := hA x hx
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO x (hAO hx)
      set r : ℝ := min (t₀ / 2) (min (ε / 2) (δ / 10))
      have hrpos : 0 < r := by positivity
      have hr₁ := min_le_left (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₂ := min_le_right (t₀ / 2) (min (ε / 2) (δ / 10))
      have hr₃ := min_le_left (ε / 2) (δ / 10)
      have hr₄ := min_le_right (ε / 2) (δ / 10)
      have hmem : (x, r) ∈ T :=
        ⟨hx, hrpos, by linarith, (closedBall_subset_ball (by linarith)).trans hball,
          hbound r hrpos (by linarith)⟩
      obtain ⟨b, hbu, hsub⟩ := hucov (x, r) hmem
      exact mem_iUnion.2 ⟨⟨b, hbu⟩, hsub (mem_closedBall_self hrpos.le)⟩
    · calc ∑' p : u, ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
          ≤ ∑' p : u, ENNReal.ofReal (10 ^ n / c) *
              ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
            refine ENNReal.tsum_le_tsum fun p => ?_
            obtain ⟨-, hp0, -, -, hpν⟩ := huT p.2
            calc ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)
                ≤ ENNReal.ofReal (2 * (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ) :=
                  ENNReal.rpow_le_rpow (hdiam _ _) (Nat.cast_nonneg n)
              _ = ENNReal.ofReal (10 ^ n / c) * ENNReal.ofReal (c * (p : Euclid N × ℝ).2 ^ n) := by
                  rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow (by positivity),
                    ← ENNReal.ofReal_mul (by positivity)]
                  congr 1
                  field_simp
                  ring
              _ ≤ ENNReal.ofReal (10 ^ n / c) *
                    ν (closedBall (p : Euclid N × ℝ).1 (p : Euclid N × ℝ).2) := by
                  gcongr
        _ = ENNReal.ofReal (10 ^ n / c) * ν (⋃ p ∈ u, closedBall p.1 p.2) := by
            rw [ENNReal.tsum_mul_left,
              measure_biUnion hucount hudisj fun p _ => measurableSet_closedBall]
        _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
            gcongr
            exact iUnion₂_subset fun p hp => (huT hp).2.2.2.1
  choose u hucount hudiam hucov husum using step
  have : ∀ m, Countable (u m) := fun m => (hucount m).to_subtype
  -- covers of mesh `1 / (m + 1) → 0`
  have main : μH[(n : ℝ)] A ≤ ENNReal.ofReal (10 ^ n / c) * ν O := by
    calc μH[(n : ℝ)] A
        ≤ liminf (fun m => ∑' p : u m,
            ediam (closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2)) ^ (n : ℝ)) atTop := by
          refine Measure.hausdorffMeasure_le_liminf_tsum (ι := fun m => u m) (n : ℝ) A
            (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) + 1))) ?_
            (fun m p => closedBall (p : Euclid N × ℝ).1 (5 * (p : Euclid N × ℝ).2))
            (Eventually.of_forall fun m p => hudiam m p p.2) (Eventually.of_forall hucov)
          simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      _ ≤ ENNReal.ofReal (10 ^ n / c) * ν O :=
          liminf_le_of_frequently_le' (Frequently.of_forall husum)
  calc μHE[n] A = (k : ℝ≥0∞) * μH[(n : ℝ)] A := by
        rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def,
          smul_eq_mul]
    _ ≤ (k : ℝ≥0∞) * (ENNReal.ofReal (10 ^ n / c) * ν O) := by gcongr
    _ = (k : ℝ≥0∞) * ENNReal.ofReal (10 ^ n / c) * ν O := by rw [mul_assoc]
/-- **A null set at whose points the measure is locally finite has open neighbourhoods of
arbitrarily small measure** (localized outer regularity).  The balls `B(x, r(x))` of finite
measure, `x ∈ A`, have a countable subfamily `B(i, r(i))`, `i ∈ T ⊆ A`, still covering `A`
(Lindelöf).  With budgets `δᵢ > 0`, `∑ᵢ δᵢ < ε`, outer regularity of the finite measure
`μ ⌞ B(i, r(i))` at `A` gives an open `Uᵢ ⊇ A` with `μ (Uᵢ ∩ B(i, r(i))) < δᵢ`; take
`O = ⋃ᵢ Uᵢ ∩ B(i, r(i))`. -/
theorem Submission.dorag_sn_open_superset_measure_lt : ∀ (N : ℕ) (μ : Measure (Euclid N)) (A : Set (Euclid N)), μ A = 0 → (∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ μ (ball x r) ≠ ∞) → ∀ ε : ℝ≥0∞, 0 < ε → ∃ O : Set (Euclid N), IsOpen O ∧ A ⊆ O ∧ μ O < ε := by
  intro N μ A hA hloc ε hε
  choose! r hr hfin using hloc
  -- Lindelöf: countably many of the balls `B(x, r(x))`, `x ∈ A`, still cover `A`
  obtain ⟨T, hTA, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable A
    (fun x => ball x (r x)) fun x _ => isOpen_ball
  have : Countable T := hTc.to_subtype
  -- budgets `δᵢ > 0` with `∑ᵢ δᵢ < ε`
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' T
  -- outer regularity of the finite measure `μ ⌞ B(i, r(i))` at the null set `A`
  have hU : ∀ i : T, ∃ U : Set (Euclid N), A ⊆ U ∧ IsOpen U ∧
      μ (U ∩ ball (i : Euclid N) (r i)) < δ i := by
    intro i
    have : IsFiniteMeasure (μ.restrict (ball (i : Euclid N) (r i))) :=
      isFiniteMeasure_restrict.2 (hfin i (hTA i.2))
    obtain ⟨U, hAU, hUo, hUδ⟩ := A.exists_isOpen_lt_of_lt
      (μ := μ.restrict (ball (i : Euclid N) (r i))) (δ i)
      ((Measure.restrict_apply_le _ A).trans_lt (by rw [hA]; exact hδ i))
    exact ⟨U, hAU, hUo, by rwa [Measure.restrict_apply hUo.measurableSet] at hUδ⟩
  choose U hAU hUo hUδ using hU
  refine ⟨⋃ i : T, U i ∩ ball (i : Euclid N) (r i),
    isOpen_iUnion fun i => (hUo i).inter isOpen_ball, fun x hx => ?_, ?_⟩
  · obtain ⟨i, hiT, hxi⟩ :=
      mem_iUnion₂.1 (hTU.superset (mem_biUnion hx (mem_ball_self (hr x hx))))
    exact mem_iUnion.2 ⟨⟨i, hiT⟩, hAU _ hx, hxi⟩
  · calc μ (⋃ i : T, U i ∩ ball (i : Euclid N) (r i))
        ≤ ∑' i : T, μ (U i ∩ ball (i : Euclid N) (r i)) := measure_iUnion_le _
      _ ≤ ∑' i : T, δ i := ENNReal.tsum_le_tsum fun i => (hUδ i).le
      _ < ε := hδε

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
