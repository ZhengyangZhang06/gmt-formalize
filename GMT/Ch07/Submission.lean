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

/-- **Simon 7.3.3, proof of (1)** (p. 189): given (MB), the moving-centre form of 7.3.1(2), every
weak limit `η_{xᵢ,λᵢ#}T ⇀ S` in `ℝ^{n+k}` with centres `xᵢ → x ∈ U` and scales `λᵢ ↓ 0` is
minimizing in `ℝ^{n+k}` with `∂S = 0`.  (MB) gives a strictly increasing `φ` and `C`, minimizing
in `ℝ^{n+k}` with `∂C = 0`, with `η_{x_{φ(j)},λ_{φ(j)}#}T ⇀ C`.  For each `ω ∈ 𝒟ⁿ(ℝ^{n+k})` the
values along `φ` tend both to `S(ω)` and to `C(ω)`, so `S = C` by uniqueness of limits in `ℝ`. -/
theorem Submission.dimred_tr_bc_zero_limit_minimizing : (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → IsMinimizingIn S univ ∧ BoundaryVanishes S := by
  intro hMB n k ℓ hℓk U N T hn hU hN hNU hT hsptT hbdT x xs lams hlams S hx hxs hlams0 hS
  -- (MB) at the limit `x ∈ U` of the centres: along a subsequence `φ` the blow-ups converge
  -- weakly to some `C`, minimizing in `ℝ^{n+k}` with `∂C = 0`
  obtain ⟨φ, C, hφ, hC, -, hCmin, hCbd⟩ :=
    hMB n k ℓ hℓk U N T hn hU hN hNU hT hsptT hbdT x xs lams hlams hx hxs hlams0
  -- weak limits are unique: `φ(j) → ∞`, so along `φ` the values on `ω` tend to `S(ω)` and `C(ω)`
  have hSC : S = C := by
    ext ω
    exact tendsto_nhds_unique ((hS ω).comp hφ.tendsto_atTop) (hC ω)
  rw [hSC]
  exact ⟨hCmin, hCbd⟩
/-- **Blow-ups at a point off the support vanish** (Simon 6.2.11; class `𝒯` in the proof of 7.3.3).
Assume (BC)(ii): `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)`.  If `p ∈ U \ spt T`, then `p` lies in an open
`W` with `closure W ⊆ U` on which `T` vanishes; for `B_ε(p) ⊆ W`, `T` vanishes on `B_ε(p)`, so
`M_{B_ε(p)}(T) = 0`.  If `λⱼ → 0` and `spt ω ⊆ B_R(0)`, then `spt η_{p,λⱼ}^# ω ⊆ B_{λⱼR}(p)`,
which lies in `B_ε(p)` once `λⱼR < ε`; so `η_{p,λⱼ#}T(ω) = 0` for large `j`, and
`η_{p,λⱼ#}T ⇀ 0`. -/
theorem Submission.dimred_tr_bc_vanishing_blowup : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (p : Euclid P), p ∈ U → p ∉ T.support → ∃ ε : ℝ, 0 < ε ∧ ball p ε ⊆ U ∧ T.VanishesOn (ball p ε) ∧ T.massOn (ball p ε) = 0 ∧ ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun j => blowUp T p (lams j) (hlams j).ne') (0 : GeometricCurrentOn (univ : Set (Euclid P)) n) := by
  intro hBC P n U T p hpU hpT
  -- Step 1: `spt T = U \ zeroRegion T`, so `p` lies in an open `W` with `closure W ⊆ U` and
  -- `T.VanishesOn W`; choose `B_ε(p) ⊆ W`
  obtain ⟨W, ⟨hWo, -, hWU, hWv⟩, hpW⟩ : p ∈ T.zeroRegion := by
    by_contra h
    exact hpT ⟨hpU, h⟩
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hWo p hpW
  -- Step 2: `T` vanishes on `B_ε(p) ⊆ W`
  have hvan : T.VanishesOn (ball p ε) := fun ω hω => hWv ω (hω.trans hεW)
  refine ⟨ε, hε, hεW.trans (subset_closure.trans hWU), hvan, ?_, ?_⟩
  · -- Step 3: every admissible form gives `ofReal 0 = 0`, so `M_{B_ε(p)}(T) = 0`
    refine le_antisymm (sSup_le ?_) zero_le
    rintro r ⟨ω, hω, rfl⟩
    exact ((congrArg ENNReal.ofReal (hvan ω hω.1)).trans ENNReal.ofReal_zero).le
  · -- Step 4: `spt ω ⊆ B_R(0)` as `spt ω` is compact, and `λⱼR < ε` for large `j`
    intro lams hlams hlim ω
    obtain ⟨R, hR⟩ := ω.property.1.2.isCompact.isBounded.subset_ball (0 : Euclid P)
    have hev : ∀ᶠ j in atTop, lams j * R < ε := by
      have h := hlim.mul_const R
      rw [zero_mul] at h
      exact h.eventually_lt_const hε
    -- Step 8: it suffices that `η_{p,λⱼ#}T(ω) = 0 = 0(ω)` for all large `j`
    rw [GeometricCurrentOn.zero_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with j hj
    -- Step 5: by (BC)(ii), `η_{p,λⱼ#}T(ω) = T(η_{p,λⱼ}^# ω)`
    rw [(hBC P n U T p (lams j) (hlams j)).2.1]
    -- Step 6: `spt η_{p,λⱼ}^# ω ⊆ η_{p,λⱼ}⁻¹(B_R(0)) = B_{λⱼR}(p) ⊆ B_ε(p)`, as
    -- `‖η_{p,λⱼ}(v)‖ = λⱼ⁻¹‖v − p‖`
    have hsupp : tsupport (affinePullbackForm (dilationCLM P (lams j)) (-((lams j)⁻¹ • p))
        (ω : DifferentialForm (Euclid P) n)) ⊆ ball p ε := by
      intro v hv
      have hv' : -((lams j)⁻¹ • p) + (lams j)⁻¹ • v ∈ ball (0 : Euclid P) R :=
        hR (tsupport_affinePullbackForm_subset _ _ _ hv)
      rw [mem_ball_zero_iff, ← smul_neg, ← smul_add, neg_add_eq_sub, norm_smul, norm_inv,
        Real.norm_of_nonneg (hlams j).le, inv_mul_lt_iff₀ (hlams j)] at hv'
      rw [mem_ball, dist_eq_norm]
      exact hv'.trans hj
    -- Step 7: `currentEval T` of the pulled-back form is `0` in both cases of its definition
    rw [currentEval]
    split_ifs with h
    · exact (hvan ⟨_, h⟩ hsupp).symm
    · rfl
/-- **Rescaling blow-up limits in `ℝᴾ`** (proof of Simon 7.3.3(1), chapter-07.txt lines 444–472:
the class `𝒯` of weak limits of blow-ups `η_{xᵢ,λᵢ#}T` has `η_{y,λ#}𝒯 ⊆ 𝒯`, (10) there; here
the limits in `ℝᴾ`, the case `lim λᵢ = 0` of (8)–(9)).  Assume the blow-up calculus (BC): the
mass formula, `η_{x,λ#}T(ω) = T(η_{x,λ}^# ω)` and `η_{y,μ#}η_{x,λ#}T = η_{x+λy,λμ#}T`; and (BUI):
`η_{x,λ#}τ(M, θ, ξ)` has an integer multiplicity representation of weight `λ⁻ⁿ μ_R(η_{x,λ}⁻¹(·))`
on Borel sets.  If `η_{cᵢ,tᵢ#}T ⇀ S` in `ℝᴾ`, then for `y ∈ ℝᴾ` and `λ > 0`,
`η_{cᵢ+tᵢy,tᵢλ#}T = η_{y,λ#}η_{cᵢ,tᵢ#}T ⇀ S' = η_{y,λ#}S` in `ℝᴾ`, and a representation of `S`
of weight `μ` gives one of `S'` of weight `λ⁻ⁿ η_{y,λ#}μ`.  As `η_{y,λ}(ℝᴾ) = ℝᴾ`, `S'` is
`η_{y,λ#}S` with its domain restricted to `ℝᴾ`, and the representation of (BUI) moves along. -/
theorem Submission.dimred_tr_bc_zero_limit_rescale : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (cs : ℕ → Euclid P) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (lam : ℝ) (hlam : 0 < lam), ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S → ∃ S' : GeometricCurrentOn (univ : Set (Euclid P)) n, ConvergesWeakly (fun i => blowUp T (cs i + ts i • y) (ts i * lam) (mul_pos (hts i) hlam).ne') S' ∧ ∀ R : IMRep (univ : Set (Euclid P)) n, R.Represents S → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.Represents S' ∧ R'.measure = ENNReal.ofReal (lam⁻¹ ^ n) • R.measure.map (dilation y lam) := by
  intro hBC hBUI P n U T cs ts hts S y lam hlam hconv
  -- (1) `η = η_{y,λ}` maps `ℝᴾ` onto `ℝᴾ`: `η(y + λu) = u`
  have hsurj : (univ : Set (Euclid P)) ⊆ dilation y lam '' univ := by
    intro u _
    refine ⟨y + lam • u, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne']
  -- (3) `v ↦ −λ⁻¹y + λ⁻¹v` is a homeomorphism, hence proper
  have hproper : IsProperMap (fun v : Euclid P => -(lam⁻¹ • y) + dilationCLM P lam v) := by
    convert ((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
        (Homeomorph.addLeft (-(lam⁻¹ • y)))).isProperMap using 1
    funext v
    simp [dilationCLM]
  -- (2) `S' := η_#S`, restricted to the domain `ℝᴾ ⊆ η(ℝᴾ)`
  refine ⟨(blowUp S y lam hlam.ne').restrictDomain hsurj, ?_, ?_⟩
  · -- (4), (5) `η_{cᵢ+tᵢy,tᵢλ#}T(ω) = η_{cᵢ,tᵢ#}T(η^#ω) → S(η^#ω) = η_#S(ω) = S'(ω)`
    intro ω
    have hω' : IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y))
        (ω : DifferentialForm (Euclid P) n)) :=
      affinePullbackForm_isTestForm _ _ hproper ω.property.1
    let ω' : TestFormOn (univ : Set (Euclid P)) n :=
      ⟨affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • y)) (ω : DifferentialForm (Euclid P) n),
        hω', subset_univ _⟩
    have hseq : (fun i => currentEval (blowUp T (cs i + ts i • y) (ts i * lam)
        (mul_pos (hts i) hlam).ne') (ω : DifferentialForm (Euclid P) n)) =
        fun i => currentEval (blowUp T (cs i) (ts i) (hts i).ne')
          (ω' : DifferentialForm (Euclid P) n) := by
      funext i
      rw [← (hBC P n U T (cs i) (ts i) (hts i)).2.2 y lam hlam ω]
      exact (hBC P n _ (blowUp T (cs i) (ts i) (hts i).ne') y lam hlam).2.1 ω
    have hB : currentEval (blowUp S y lam hlam.ne') (ω : DifferentialForm (Euclid P) n) =
        (blowUp S y lam hlam.ne').restrictDomain hsurj ω := by
      unfold currentEval
      rw [dite_eq_left ⟨ω.property.1, ω.property.2.trans hsurj⟩]
      rfl
    have hS : currentEval S (ω' : DifferentialForm (Euclid P) n) = S ω' := by
      unfold currentEval
      rw [dite_eq_left ⟨hω', subset_univ _⟩]
    have hlim : S ω' = (blowUp S y lam hlam.ne').restrictDomain hsurj ω := by
      rw [← hB, ← hS]
      exact ((hBC P n univ S y lam hlam).2.1 ω).symm
    rw [hseq, ← hlim]
    exact hconv ω'
  · -- (6), (7) the representation of `η_#S` given by (BUI), moved to the domain `ℝᴾ`; its
    -- weight agrees with `λ⁻ⁿ η_#μ_R` on Borel sets
    intro R hR
    obtain ⟨R₁, hR₁, hR₁m⟩ := hBUI P n univ S y lam hlam R hR
    let R' : IMRep (univ : Set (Euclid P)) n :=
      { carrier := R₁.carrier
        mult := R₁.mult
        orient := R₁.orient
        measurableSet_carrier := R₁.measurableSet_carrier
        carrier_subset := subset_univ _
        rectifiable := R₁.rectifiable
        measurable_mult := R₁.measurable_mult
        mult_pos := R₁.mult_pos
        locallyIntegrable_mult := fun K hK _ =>
          R₁.locallyIntegrable_mult K hK ((subset_univ K).trans hsurj)
        aestronglyMeasurable_orient := R₁.aestronglyMeasurable_orient
        orients := R₁.orients }
    refine ⟨R', fun ω => hR₁ (testFormOnInclusion hsurj n ω), ?_⟩
    have hmeas : Measurable (dilation y lam) :=
      (continuous_const.add (dilationCLM P lam).continuous).measurable
    ext s hs
    rw [Measure.smul_apply, Measure.map_apply hmeas hs, smul_eq_mul]
    exact hR₁m s hs
/-- **The zero current is integer multiplicity, with zero weight** (Simon Ch. 6, 3.1: the zero
current is `τ(∅, θ, ξ)`).  The triple `R = (∅, 0, 0)` is an integer multiplicity representation in
`ℝᴾ`: each condition holds because `Hⁿ⌞∅ = 0` (rectifiability as `Hⁿ(∅) = 0`, local integrability
as `∫⁻ θ d0 = 0`, the a.e. conditions as `ae 0 = ⊥`).  Its action `∫_∅ θ⟨ω, ξ⟩ dHⁿ` is an
integral against `0`, so `R` represents the zero current, and its weight `θ Hⁿ⌞∅` is the zero
measure. -/
theorem Submission.dimred_tr_bc_ct_zero_imrep : ∀ (P n : ℕ), ∃ R : IMRep (univ : Set (Euclid P)) n, R.Represents (0 : GeometricCurrentOn (univ : Set (Euclid P)) n) ∧ R.measure = 0 := by
  intro P n
  -- Step 1: the triple `(∅, 0, 0)`; every field holds since `Hⁿ⌞∅ = 0`
  refine ⟨{ carrier := ∅
            mult := fun _ => 0
            orient := fun _ => 0
            measurableSet_carrier := MeasurableSet.empty
            carrier_subset := empty_subset _
            rectifiable :=
              Poincare.SimonGMT.Chapter03.countablyRectifiable_of_measure_zero measure_empty
            measurable_mult := measurable_const
            mult_pos := fun x hx => absurd hx (notMem_empty x)
            locallyIntegrable_mult := fun K _ _ => by
              rw [empty_inter, Measure.restrict_empty, lintegral_zero_measure]
              exact ENNReal.zero_ne_top
            aestronglyMeasurable_orient := aestronglyMeasurable_const
            orients := by
              rw [Measure.restrict_empty, ae_zero]
              exact eventually_bot }, fun ω => ?_, ?_⟩
  · -- Step 2: `0(ω) = 0` and `R.action ω = ∫ θ⟨ω, ξ⟩ d(Hⁿ⌞∅) = ∫ θ⟨ω, ξ⟩ d0 = 0`
    rw [GeometricCurrentOn.zero_apply]
    dsimp only [IMRep.action]
    rw [Measure.restrict_empty, integral_zero_measure]
  · -- Step 3: `R.measure = (Hⁿ⌞∅).withDensity θ = (0 : Measure).withDensity θ`, which agrees
    -- with `0` on every Borel set `s`: `∫⁻_s θ d0 = 0`
    dsimp only [IMRep.measure]
    rw [Measure.restrict_empty]
    ext s hs
    rw [withDensity_apply _ hs, Measure.restrict_zero, lintegral_zero_measure, Measure.coe_zero,
      Pi.zero_apply]
/-- **Uniform local mass bound near `B̄_r(z)`** (the mass hypothesis of the blow-up lemma at the
points `b ∈ B̄_r(z)`).  Let `r > 0`, `Λ ≥ 0`, let `ρ ↦ e^{Λρ}ρ⁻ⁿ M_{B_ρ(y)}(T)` be monotone on
`(0, R)` whenever `B̄_R(y) ⊆ B̄_{2r}(z)`, and let `M_{B_{2r}(z)}(T) < ∞`.  Then
`M_{B_ρ(x′)}(T) ≤ Γρⁿ` for all `b ∈ B̄_r(z)`, `x′ ∈ B_δ(b)` and `0 < ρ < δ`, with `δ = r/4` and
`Γ = e^{Λr/4}(r/4)⁻ⁿ M_{B_{2r}(z)}(T)`: since `|x′ − z| < 5r/4`, `B̄_{r/2}(x′) ⊆ B̄_{2r}(z)` and
`B_{r/4}(x′) ⊆ B_{2r}(z)`, so `ρ⁻ⁿ M_{B_ρ(x′)}(T) ≤ e^{Λρ}ρ⁻ⁿ M_{B_ρ(x′)}(T)
≤ e^{Λr/4}(r/4)⁻ⁿ M_{B_{r/4}(x′)}(T) ≤ Γ`. -/
theorem Submission.dimred_tr_bc_ct_uniform_mass_bound : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (z : Euclid P) (r Λ : ℝ), 0 < r → 0 ≤ Λ → (∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ closedBall z (2 * r) → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) → T.massOn (ball z (2 * r)) ≠ ∞ → ∃ δ Γ : ℝ, 0 < δ ∧ ∀ b ∈ closedBall z r, ∀ x' ∈ ball b δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n) := by
  intro P n U T z r Λ hr hΛ hmon hfin
  -- Step 1: `Γ′ = ofReal(e^{Λr/4}/(r/4)ⁿ) · M_{B_{2r}(z)}(T)` is finite; `δ = r/4`, `Γ = Γ′.toReal`
  have hΓ' : ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) *
      T.massOn (ball z (2 * r)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  refine ⟨r / 4, (ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) *
    T.massOn (ball z (2 * r))).toReal, by linarith, fun b hb x' hx' ρ hρ hρδ => ?_⟩
  -- Step 2: `|x′ − z| < 5r/4`, so (i) `B̄_{r/2}(x′) ⊆ B̄_{2r}(z)` and (ii) `B_{r/4}(x′) ⊆ B_{2r}(z)`
  have hxz : dist x' z < 5 * r / 4 := by
    linarith [dist_triangle x' b z, mem_ball.mp hx', mem_closedBall.mp hb]
  have hsub₁ : closedBall x' (r / 2) ⊆ closedBall z (2 * r) := fun w hw => by
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w x' z]
  have hsub₂ : ball x' (r / 4) ⊆ ball z (2 * r) := fun w hw => by
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w x' z]
  -- Step 3: by (i), monotonicity on `(0, r/2)` compares the radii `ρ ≤ r/4`
  have h₃ : ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball x' ρ) ≤
      ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) * T.massOn (ball x' (r / 4)) :=
    hmon x' (r / 2) hsub₁ ⟨hρ, by linarith⟩ ⟨by linarith, by linarith⟩ hρδ.le
  -- Step 4: by (ii), `M_{B_{r/4}(x′)}(T) ≤ M_{B_{2r}(z)}(T)`
  have h₄ := mul_le_mul_right (T.massOn_mono hsub₂)
    (ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n))
  -- Step 5: `e^{Λρ} ≥ 1` removes the exponential
  have hρn : 0 < ρ ^ n := pow_pos hρ n
  have h₅ : ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball x' ρ) ≤
      ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) * T.massOn (ball z (2 * r)) :=
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (Real.one_le_exp (mul_nonneg hΛ hρ.le)) hρn.le)) _).trans (h₃.trans h₄)
  -- Step 6: multiply by `ofReal(ρⁿ)`, using `ofReal(ρⁿ) · ofReal(1/ρⁿ) = 1` and `Γ′ = ofReal(Γ)`
  calc T.massOn (ball x' ρ)
      = ENNReal.ofReal (ρ ^ n) * (ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball x' ρ)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hρn.le, mul_one_div_cancel hρn.ne',
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal (ρ ^ n) * (ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) *
        T.massOn (ball z (2 * r))) := mul_le_mul_right h₅ _
    _ = ENNReal.ofReal ((ENNReal.ofReal (Real.exp (Λ * (r / 4)) / (r / 4) ^ n) *
        T.massOn (ball z (2 * r))).toReal * ρ ^ n) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hΓ']
        exact mul_comm _ _
/-- **Iterated blow-ups at a point of the open unit ball are again admissible blow-up limits**
(the class-membership step of Simon 7.3.3, proof of (1): `η_{y,s#}η_{x,λ#}T = η_{x+λy,λs#}T`).
Assume (IBL): if `η_{xᵢ,λᵢ#}T ⇀ S` with `xᵢ → x ∈ U`, `λᵢ ↓ 0` and `M_{B_ρ(x′)}(T) ≤ Γρⁿ` near `x`,
and `η_{y,sₖ#}S ⇀ C` with `sₖ ↓ 0`, then `η_{x_{φ(k)}+λ_{φ(k)}y, λ_{φ(k)}sₖ#}T ⇀ C` along some
`φ`.  If `η_{cᵢ,tᵢ#}T ⇀ S` with `dist(cᵢ, z) < r − tᵢ`, `tᵢ ↓ 0`, `cᵢ → b ∈ U`, and `‖y‖ < 1`,
`sₖ ↓ 0`, `η_{y,sₖ#}S ⇀ C`, then `C` is the weak limit of blow-ups `η_{c′ₖ,t′ₖ#}T` with
`dist(c′ₖ, z) < r − t′ₖ`, `t′ₖ ↓ 0`, `c′ₖ → b`: with `sₖ < 1 − ‖y‖` for `k ≥ k₀` and
`i(k) = φ(k + k₀)`, take `c′ₖ = c_{i(k)} + t_{i(k)}y` and `t′ₖ = t_{i(k)}s_{k+k₀}`; then
`dist(c′ₖ, z) < t_{i(k)}‖y‖ + r − t_{i(k)} = r − t_{i(k)}(1 − ‖y‖) < r − t′ₖ`. -/
theorem Submission.dimred_tr_bc_ct_zero_scale_iterate : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C) → ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (z : Euclid P) (r : ℝ) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (cs : ℕ → Euclid P) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → b ∈ U → (∀ i, dist (cs i) z < r - ts i) → Tendsto ts atTop (𝓝 0) → Tendsto cs atTop (𝓝 b) → ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball b δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ‖y‖ < 1 → Tendsto ss atTop (𝓝 0) → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ (cs' : ℕ → Euclid P) (ts' : ℕ → ℝ) (hts' : ∀ i, 0 < ts' i), (∀ i, dist (cs' i) z < r - ts' i) ∧ Tendsto ts' atTop (𝓝 0) ∧ Tendsto cs' atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs' i) (ts' i) (hts' i).ne') C := by
  intro hIBL P n U T z r S cs ts hts b y ss hss C hU hb hdist hts0 hcs hTS hmass hy hss0 hSC
  -- Step 1: (IBL) at `x := b` gives `φ` with `η_{c_{φ(k)}+t_{φ(k)}y, t_{φ(k)}sₖ#}T ⇀ C`
  obtain ⟨φ, hφ, hconv⟩ :=
    hIBL P n U T b cs ts hts S y ss hss C hU hb hcs hts0 hss0 hmass hTS hSC
  -- Step 2: `sₖ < 1 − ‖y‖` for all `k ≥ k₀`, as `sₖ → 0 < 1 − ‖y‖`
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hss0.eventually (gt_mem_nhds (sub_pos.mpr hy)))
  -- Step 5: `k ↦ k + k₀` and `i(k) = φ(k + k₀)` tend to `∞`
  have hshift : Tendsto (fun k => k + k₀) atTop atTop := tendsto_add_atTop_nat k₀
  have hidx : Tendsto (fun k => φ (k + k₀)) atTop atTop := hφ.tendsto_atTop.comp hshift
  -- Step 3: `c′ₖ = c_{i(k)} + t_{i(k)}y` and `t′ₖ = t_{i(k)}s_{k+k₀} > 0`
  refine ⟨fun k => cs (φ (k + k₀)) + ts (φ (k + k₀)) • y, fun k => ts (φ (k + k₀)) * ss (k + k₀),
    fun k => mul_pos (hts (φ (k + k₀))) (hss (k + k₀)), fun k => ?_, ?_, ?_, ?_⟩
  · -- Step 4: with `t = t_{i(k)}`, `dist(c′ₖ, z) ≤ t‖y‖ + dist(c_{i(k)}, z) < r − t(1 − ‖y‖)`,
    -- and `t′ₖ = t s_{k+k₀} < t(1 − ‖y‖)` as `k + k₀ ≥ k₀`
    show dist (cs (φ (k + k₀)) + ts (φ (k + k₀)) • y) z < r - ts (φ (k + k₀)) * ss (k + k₀)
    have ht := hts (φ (k + k₀))
    have h1 := dist_triangle (cs (φ (k + k₀)) + ts (φ (k + k₀)) • y) (cs (φ (k + k₀))) z
    have h2 : dist (cs (φ (k + k₀)) + ts (φ (k + k₀)) • y) (cs (φ (k + k₀))) =
        ts (φ (k + k₀)) * ‖y‖ := by
      rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg ht.le]
    have h3 : ts (φ (k + k₀)) * ss (k + k₀) < ts (φ (k + k₀)) * (1 - ‖y‖) :=
      mul_lt_mul_of_pos_left (hk₀ (k + k₀) (Nat.le_add_left k₀ k)) ht
    linarith [hdist (φ (k + k₀))]
  · -- Step 5: `t′ₖ → 0 · 0 = 0`
    have h := (hts0.comp hidx).mul (hss0.comp hshift)
    rw [mul_zero] at h
    exact h
  · -- Step 5: `c′ₖ → b + 0 • y = b`
    have h := (hcs.comp hidx).add ((hts0.comp hidx).smul_const y)
    rw [zero_smul, add_zero] at h
    exact h
  · -- Step 6: the tail along `k ↦ k + k₀` of the weakly convergent sequence of step 1 has the
    -- same limit; its terms are `η_{c′ₖ,t′ₖ#}T` (the nonvanishing proofs are irrelevant)
    intro ω
    exact (hconv ω).comp hshift
/-- **Rescaled IMRep weights along blow-ups converge** (preliminary P7 with
`MassMeasuresConverge`).  Assume (BUI): every IMRep `R` of `T` in `U` gives an IMRep `R'` of the
blow-up `η_{x,λ#}T` in `η_{x,λ}(U)` with `R'.measure(s) = λ⁻ⁿ R.measure(η_{x,λ}⁻¹(s))` for Borel
`s`.  Let `R` represent `A` in `V`, `R_C` represent `C` in `ℝᴾ`, `sⱼ > 0`, and let the mass measures
of the blow-ups `η_{a,sⱼ#}A` converge to those of `C`.  Then `∫ f d(sⱼ⁻ⁿ η_{a,sⱼ#}R.measure) →
∫ f dR_C.measure` for every continuous compactly supported `f`: the IMReps `Rⱼ` of the blow-ups
given by (BUI) have weights `Rⱼ.measure = sⱼ⁻ⁿ η_{a,sⱼ#}R.measure` (both sides agree on Borel sets,
`η_{a,sⱼ}` being continuous), and `MassMeasuresConverge` applies to `(Rⱼ)`, `R_C` and `f`. -/
theorem Submission.dimred_tr_bc_ct_weight_convergence : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (P n : ℕ) (V : Set (Euclid P)) (A : GeometricCurrentOn V n) (R : IMRep V n) (a : Euclid P) (ss : ℕ → ℝ) (hss : ∀ j, 0 < ss j) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (RC : IMRep (univ : Set (Euclid P)) n), R.Represents A → RC.Represents C → MassMeasuresConverge (fun j => blowUp A a (ss j) (hss j).ne') C → ∀ f : Euclid P → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((ss j)⁻¹ ^ n) • R.measure.map (dilation a (ss j)))) atTop (𝓝 (∫ x, f x ∂RC.measure)) := by
  intro hBUI P n V A R a ss hss C RC hRA hRC hconv f hf hfc
  -- Step 1: `η_{a,s}(v) = −s⁻¹a + s⁻¹v` is a constant plus a continuous linear map, hence
  -- continuous and Borel measurable
  have hmeas : ∀ s : ℝ, Measurable (dilation a s) := fun s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  -- Step 2: (BUI) gives, for every `j`, an IMRep `Rⱼ` of `η_{a,sⱼ#}A` in `η_{a,sⱼ}(V)` with
  -- `Rⱼ.measure(B) = sⱼ⁻ⁿ R.measure(η_{a,sⱼ}⁻¹(B))` for Borel `B`
  choose Rs hRs hRsμ using fun j => hBUI P n V A a (ss j) (hss j) R hRA
  -- Step 3: `Rⱼ.measure = sⱼ⁻ⁿ η_{a,sⱼ#}R.measure`, as both sides agree on Borel sets
  have hw : ∀ j, (Rs j).measure =
      ENNReal.ofReal ((ss j)⁻¹ ^ n) • R.measure.map (dilation a (ss j)) := by
    intro j
    ext B hB
    rw [hRsμ j B hB, Measure.smul_apply, Measure.map_apply (hmeas (ss j)) hB, smul_eq_mul]
  -- Steps 4–5: `MassMeasuresConverge` applied to `(Rⱼ)`, `R_C`, `f` and `tsupport f ⊆ ℝᴾ`
  exact (hconv Rs hRs RC hRC f hf hfc (subset_univ _)).congr fun j => by rw [hw j]
/-- **Simon Ch. 6, 1.2 and 1.5–1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` (`τ` orthonormal)
has `|ξ(α)| ≤ |α|` for the Euclidean coefficient norm, and `L(ζ) = Σ_I ζ(dx^I) dx^I` (`I` strictly
increasing) has `|L(ξ)| ≤ 1` and `ξ(L(ξ)) = 1`.  Every covector expands as `α = Σ_I α(e_I) dx^I`,
and `dx^I(e_J) = δ_IJ`.  Expanding `δ_τ(v) = det(⟨τᵢ, vⱼ⟩)` at `v = τ` gives the Cauchy–Binet
identity `Σ_I dx^I(τ)² = 1`; with Cauchy–Schwarz, `|α(τ)| ≤ |α|`. -/
theorem Submission.dor_ims_unitOrientation_dual : ∀ (P n : ℕ), ∃ L : MultiVector P n →L[ℝ] Covector (Euclid P) n, ∀ (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → (∀ α : Covector (Euclid P) n, |ξ α| ≤ covectorEuclideanNorm α) ∧ covectorEuclideanNorm (L ξ) ≤ 1 ∧ ξ (L ξ) = 1 := by
  intro P n
  -- `W u v = Σ_σ sgn σ ∏ₖ ⟨uₖ, v_{σ k}⟩ = det(⟨uₖ, vⱼ⟩)`; `dx^I = W (e ∘ I)` and `δ_τ = W τ`
  let W : (Fin n → Euclid P) → Covector (Euclid P) n := fun u =>
    ContinuousMultilinearMap.alternatization
      ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
        fun k => innerSL ℝ (u k))
  have hW : ∀ u v, W u v =
      ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ k, inner ℝ (u k) (v (σ k)) := by
    intro u v
    simp only [W, ContinuousMultilinearMap.alternatization_apply_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.mkPiAlgebra_apply, innerSL_apply_apply, Function.comp_apply]
  -- `W u v = W v u` (the determinant of the transpose): substitute `σ ↦ σ⁻¹` and `k ↦ σ k`
  have hWsymm : ∀ u v, W u v = W v u := by
    intro u v
    rw [hW, hW]
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun σ => ?_
    rw [Equiv.inv_apply, Equiv.Perm.sign_inv,
      ← Equiv.prod_comp σ (fun k => inner ℝ (v k) (u (σ⁻¹ k)))]
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply, real_inner_comm]
  -- `W u u = 1` for orthonormal `u`: only `σ = 1` contributes
  have hW1 : ∀ u, Orthonormal ℝ u → W u u = 1 := by
    intro u hu
    rw [hW, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [Equiv.Perm.sign_one, one_smul]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [Equiv.Perm.coe_one, id, real_inner_self_eq_norm_sq, hu.norm_eq_one, one_pow]
    · intro σ _ hσ
      obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra! h
        exact hσ (Equiv.ext h)
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (hu.inner_eq_zero hk.symm), smul_zero]
    · exact fun h => absurd (Finset.mem_univ _) h
  -- Kronecker property `dx^I(e_J) = δ_IJ` for strictly increasing `I`, `J`: a nonzero term
  -- forces `J ∘ σ = I`, so `range I = range J` and `I = J`
  let e := EuclideanSpace.basisFun (Fin P) ℝ
  have he : ∀ i j, inner ℝ (e i) (e j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp e.orthonormal
  have hK : ∀ I J : Fin n → Fin P, StrictMono I → StrictMono J →
      W (fun k => e (I k)) (fun k => e (J k)) = if I = J then 1 else 0 := by
    intro I J hI hJ
    split_ifs with hIJ
    · subst hIJ
      have hIo : Orthonormal ℝ (fun k => e (I k)) := e.orthonormal.comp I hI.injective
      exact hW1 _ hIo
    · rw [hW]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [Finset.prod_eq_zero_iff.mpr, smul_zero]
      by_contra! h
      apply hIJ
      have hJσ : J ∘ σ = I := funext fun k => by
        have := h k (Finset.mem_univ k)
        rw [he] at this
        split_ifs at this with hk
        · exact hk.symm
        · exact absurd rfl this
      rw [← (StrictMono.range_inj_of_wellFoundedLT hI hJ), ← hJσ, EquivLike.range_comp]
  -- expansion `α = Σ_{I ∈ S} α(e_I) dx^I`: both sides are alternating, so compare them on
  -- `e ∘ f`, `f` injective; writing `f = J ∘ σ⁻¹` with `J` strictly increasing (`J = f ∘ sort f`)
  -- reduces this to `e ∘ J`, where it is the Kronecker property
  let S : Finset (Fin n → Fin P) := Finset.univ.filter StrictMono
  have hE : ∀ α : Covector (Euclid P) n,
      α = ∑ I ∈ S, α (fun k => e (I k)) • W (fun k => e (I k)) := by
    intro α
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    refine e.toBasis.ext_alternating fun f hf => ?_
    simp only [OrthonormalBasis.coe_toBasis, ContinuousAlternatingMap.coe_toAlternatingMap]
    set σ := Tuple.sort f
    have hJ : StrictMono (f ∘ σ) :=
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
    · rw [ContinuousAlternatingMap.smul_apply, hK _ _ hJ hJ, ite_eq_left rfl, smul_eq_mul,
        mul_one]
    · intro I hI hIJ
      rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2 hJ,
        ite_eq_right hIJ, smul_zero]
    · exact fun h => absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hJ⟩) h
  -- `|β| = (Σ_{I ∈ S} β(e_I)²)^{1/2}`
  have hnorm : ∀ β : Covector (Euclid P) n,
      covectorEuclideanNorm β = Real.sqrt (∑ I ∈ S, β (fun k => e (I k)) ^ 2) := by
    intro β
    rw [covectorEuclideanNorm, Finset.sum_filter]
  -- Cauchy–Binet `Σ_{I ∈ S} dx^I(τ)² = 1` for orthonormal `τ`: evaluate the expansion of `δ_τ`
  -- at `τ`, using `δ_τ(τ) = 1` and `δ_τ(e_I) = dx^I(τ)`
  have hCB : ∀ τ : Fin n → Euclid P, Orthonormal ℝ τ →
      ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 = 1 := by
    intro τ hτ
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE (W τ))
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul, hW1 τ hτ] at h
    rw [h]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [hWsymm τ, sq]
  -- `L ζ = Σ_{I ∈ S} ζ(dx^I) dx^I`
  refine ⟨∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ (W fun k => e (I k))).smulRight
    (W fun k => e (I k)), ?_⟩
  rintro ξ Q ⟨τ, hτ, -, hξ⟩
  -- `ξ(α) = ±α(τ)` with a common sign
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
  have hL : ∀ ζ : MultiVector P n, (∑ I ∈ S, (ContinuousLinearMap.apply ℝ ℝ
      (W fun k => e (I k))).smulRight (W fun k => e (I k))) ζ =
      ∑ I ∈ S, ζ (W fun k => e (I k)) • W fun k => e (I k) := by
    intro ζ
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.apply_apply]
  have hCBτ := hCB τ hτ
  refine ⟨fun α => ?_, ?_, ?_⟩
  · -- (a) `|ξ(α)| = |Σ_I α(e_I) dx^I(τ)| ≤ |α| (Σ_I dx^I(τ)²)^{1/2} = |α|`
    rw [hξabs, hnorm]
    apply Real.abs_le_sqrt
    have h := congrArg (fun β : Covector (Euclid P) n => β τ) (hE α)
    simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [h]
    calc (∑ I ∈ S, α (fun k => e (I k)) * W (fun k => e (I k)) τ) ^ 2
        ≤ (∑ I ∈ S, α (fun k => e (I k)) ^ 2) * ∑ I ∈ S, W (fun k => e (I k)) τ ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = ∑ I ∈ S, α (fun k => e (I k)) ^ 2 := by rw [hCBτ, mul_one]
  · -- (b) `L(ξ)(e_J) = ξ(dx^J)`, so `|L(ξ)|² = Σ_J ξ(dx^J)² = Σ_J dx^J(τ)² = 1`
    rw [hnorm, hL]
    have : ∑ J ∈ S, (∑ I ∈ S, ξ (W fun k => e (I k)) • W fun k => e (I k))
        (fun k => e (J k)) ^ 2 = 1 := by
      rw [← hCBτ]
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single J]
      · rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hJ).2
          (Finset.mem_filter.mp hJ).2, ite_eq_left rfl, smul_eq_mul, mul_one, sq, sq, hξ2]
      · intro I hI hIJ
        rw [ContinuousAlternatingMap.smul_apply, hK _ _ (Finset.mem_filter.mp hI).2
          (Finset.mem_filter.mp hJ).2, ite_eq_right hIJ, smul_zero]
      · exact fun h => absurd hJ h
    rw [this, Real.sqrt_one]
  · -- (c) `ξ(L(ξ)) = Σ_I ξ(dx^I)² = Σ_I dx^I(τ)² = 1`
    rw [hL, map_sum, ← hCBτ]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [map_smul, smul_eq_mul, hξ2, sq]
/-- **Simon Ch. 6, 3.1 (‡), 3.2(3)**: for `R = (M, θ, ξ)` and `ω ∈ 𝒟ⁿ(U)`, the function
`x ↦ ⟨ω(x), ξ(x)⟩` is `μ_R`-integrable and `τ(M, θ, ξ)(ω) = ∫ ⟨ω, ξ⟩ dμ_R`, `μ_R = θ Hⁿ⌞M`.
`μ_R`-a.e. `ξ(x) = ±τ₁ ∧ ⋯ ∧ τₙ` with `τ` orthonormal, so `|⟨ω(x), ξ(x)⟩| ≤ ‖ω(x)‖`; this is
bounded and vanishes off the compact `spt ω ⊆ U`, which has finite `μ_R`-measure. -/
theorem Submission.dor_ims_action_eq_integral : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) R.measure ∧ R.action (ω : DifferentialForm (Euclid P) n) = ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure := by
  intro P n U R ω
  obtain ⟨⟨hsmooth, hcpt⟩, hU⟩ := ω.2
  set f : DifferentialForm (Euclid P) n := (ω : DifferentialForm (Euclid P) n)
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) := measurable_from_nat.comp R.measurable_mult
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  -- `x ↦ ξ(x)(ω(x))` is `μ_R`-a.e. strongly measurable
  have hmeas : AEStronglyMeasurable (fun x => R.orient x (f x)) R.measure :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
      (R.aestronglyMeasurable_orient.mono_ac hac) hsmooth.continuous.aestronglyMeasurable
  -- `|ξ(x)(ω(x))| ≤ C 1_K(x)`, `K = spt ω`
  obtain ⟨C, hC⟩ := hsmooth.continuous.bounded_above_of_compact_support hcpt
  have hKm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hbound : ∀ᵐ x ∂R.measure, ‖R.orient x (f x)‖ ≤ (tsupport f).indicator (fun _ => C) x := by
    filter_upwards [hac.ae_le R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    by_cases hxK : x ∈ tsupport f
    · rw [Set.indicator_of_mem hxK]
      have hτ1 : ‖f x τ‖ ≤ ‖f x‖ := by
        simpa [hτ.norm_eq_one] using (f x).le_opNorm τ
      rcases hξ with h | h
      · rw [h]
        exact hτ1.trans (hC x)
      · rw [h, norm_neg]
        exact hτ1.trans (hC x)
    · rw [Set.indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero, norm_zero]
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  have hKfin : R.measure (tsupport f) ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm,
      Set.inter_comm (tsupport f) R.carrier]
    exact R.locallyIntegrable_mult _ hcpt hU
  have hint : Integrable (fun x => R.orient x (f x)) R.measure :=
    ((integrable_indicator_iff hKm).2 (integrableOn_const hKfin)).mono' hmeas hbound
  refine ⟨hint, ?_⟩
  -- `∫ g d(θ Hⁿ⌞M) = ∫_M θ g dHⁿ`
  rw [IMRep.measure, integral_withDensity_eq_integral_toReal_smul hθ
    (ae_of_all _ fun x => ENNReal.natCast_lt_top _), IMRep.action]
  simp only [ENNReal.toReal_natCast, smul_eq_mul]

/-- **Simon Ch. 6, 3.2(3), upper bound**: if `T = τ(M, θ, ξ)` then `M_W(T) ≤ μ_T(W)` for every
`W`.  For admissible `ω`, `⟨ω, ξ⟩ ≤ |ω| ≤ 1` `μ_T`-a.e. (`|ξ(α)| ≤ |α|` for unit orientations)
and `⟨ω, ξ⟩ = 0` off `spt ω`, so `T(ω) = ∫ ⟨ω, ξ⟩ dμ_T ≤ μ_T(spt ω) ≤ μ_T(W)`. -/
theorem Submission.dor_ims_massOn_le_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), R.Represents T → ∀ W : Set (Euclid P), T.massOn W ≤ R.measure W := by
  intro P n U T R hR W
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `|ξ(x)(α)| ≤ |α|` for `μ_T`-a.e. `x`: `ξ(x)` is a unit orientation `Hⁿ⌞M`-a.e., and
  -- `μ_T = θ Hⁿ⌞M ≪ Hⁿ⌞M`
  have hdual : ∀ᵐ x ∂R.measure, ∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α := by
    have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (hL _ Q hQ).1
  apply sSup_le
  rintro r ⟨ω, ⟨hωW, hω1⟩, rfl⟩
  -- `K = spt ω` is a compact subset of `U`, so `μ_T(K) = ∫_{M ∩ K} θ dHⁿ < ∞`
  set K := tsupport (ω : DifferentialForm (Euclid P) n)
  have hKm : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hμK : R.measure K ≠ ∞ := by
    rw [IMRep.measure, withDensity_apply _ hKm, Measure.restrict_restrict hKm, inter_comm]
    exact R.locallyIntegrable_mult K ω.2.1.2.isCompact ω.2.2
  obtain ⟨hint, haction⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `⟨ω, ξ⟩ ≤ 1_K` `μ_T`-a.e.: `⟨ω(x), ξ(x)⟩ ≤ |ω(x)| ≤ 1` on `K` and `ω = 0` off `K`
  have hle : (fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x)) ≤ᵐ[R.measure]
      K.indicator fun _ => (1 : ℝ) := by
    filter_upwards [hdual] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK]
      exact (le_abs_self _).trans ((hx _).trans (hω1 x))
    · rw [indicator_of_notMem hxK, image_eq_zero_of_notMem_tsupport hxK, map_zero]
  calc ENNReal.ofReal (T ω)
      = ENNReal.ofReal (∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure) := by
        rw [hR ω, haction]
    _ ≤ ENNReal.ofReal (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂R.measure) :=
        ENNReal.ofReal_le_ofReal (integral_mono_ae hint
          ((integrableOn_const hμK).integrable_indicator hKm) hle)
    _ = R.measure K := by
        rw [integral_indicator_const _ hKm, smul_eq_mul, mul_one, measureReal_def,
          ENNReal.ofReal_toReal hμK]
    _ ≤ R.measure W := measure_mono hωW
/-- `Λⁿ(ℝᴾ)` is finite-dimensional: `α ↦ (α(e_{I(1)}, …, e_{I(n)}))_{I : Fin n → Fin P}` is a linear
map into the finite-dimensional space `(Fin n → Fin P) → ℝ`, injective because an alternating map
is determined by its values on tuples of basis vectors. -/
theorem Submission.dor_ims_lusin_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- `L α = (α(e ∘ I))_I`
  let L : Covector (Euclid P) n →ₗ[ℝ] (Fin n → Fin P) → ℝ :=
    { toFun := fun α I => α fun k => e (I k)
      map_add' := fun α β => rfl
      map_smul' := fun c α => rfl }
  refine FiniteDimensional.of_injective L fun α β h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact e.ext_alternating fun v _ => congrFun h v
/-- **Lusin's theorem**, compact form (Simon 1.17), for a measurable `g : ℝᴾ → Y` into a
second-countable `Y`.  If `μ(A) < ∞` and `ε ≠ 0`, there is a compact `K ⊆ A` with
`μ(A \ K) < ε` on which `g` is continuous.  `μ⌞A` is finite, hence inner regular on `ℝᴾ`.  For a
countable basis `(O_k)` of `Y` and weights `η_k > 0` with `∑ η_k < ε`, choose compact
`C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)` with defects `< η_k / 2`, and put
`K = ⋂ₖ (C_k ∪ D_k)`.  On `K`, `g x ∈ O_k ↔ x ∉ D_k`, so every `g⁻¹(O_k) ∩ K` is relatively
open. -/
theorem Submission.dor_ims_lusin_measurable_continuousOn : ∀ (P : ℕ) {Y : Type} [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] (μ : Measure (Euclid P)) (A : Set (Euclid P)) (g : Euclid P → Y) (ε : ℝ≥0∞), Measurable g → MeasurableSet A → μ A ≠ ∞ → ε ≠ 0 → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ε ∧ ContinuousOn g K := by
  intro P Y _ _ _ _ μ A g ε hg hA hμA hε
  -- `μ⌞A` is finite, hence regular on the σ-compact metric space `ℝᴾ`, so every measurable
  -- `B ⊆ A` contains a compact `C` with `μ (B \ C) = μ⌞A (B \ C)` arbitrarily small
  have : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hμA
  have approx : ∀ B, B ⊆ A → MeasurableSet B → ∀ η : ℝ≥0∞, η ≠ 0 →
      ∃ C ⊆ B, IsCompact C ∧ μ (B \ C) < η := by
    intro B hBA hB η hη
    obtain ⟨C, hCB, hC, hlt⟩ :=
      hB.exists_isCompact_sdiff_lt (μ := μ.restrict A) (measure_ne_top _ _) hη
    exact ⟨C, hCB, hC, by rwa [Measure.restrict_eq_self _ (sdiff_subset.trans hBA)] at hlt⟩
  -- a countable basis `(O_k)` of `Y`, and weights `η_k > 0` with `∑ η_k < ε`
  obtain ⟨O, hO⟩ := TopologicalSpace.exists_seq_basis Y
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_pos_sum_of_countable' hε ℕ
  have hS : ∀ k, MeasurableSet (g ⁻¹' O k) :=
    fun k => hg (hO.isOpen (mem_range_self k)).measurableSet
  -- compact `C_k ⊆ A ∩ g⁻¹(O_k)` and `D_k ⊆ A \ g⁻¹(O_k)`, each with defect `< η_k / 2`
  choose C hCA hC hCμ using fun k =>
    approx (A ∩ g ⁻¹' O k) inter_subset_left (hA.inter (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  choose D hDA hD hDμ using fun k =>
    approx (A \ g ⁻¹' O k) sdiff_subset (hA.diff (hS k)) (η k / 2)
      (ENNReal.half_pos (hη k).ne').ne'
  -- `E_k = C_k ∪ D_k` misses less than `η_k` of `A`
  have hE : ∀ k, μ (A \ (C k ∪ D k)) < η k := by
    intro k
    calc μ (A \ (C k ∪ D k))
        ≤ μ ((A ∩ g ⁻¹' O k) \ C k ∪ (A \ g ⁻¹' O k) \ D k) := by
          refine measure_mono fun x hx => ?_
          by_cases hxO : g x ∈ O k
          · exact Or.inl ⟨⟨hx.1, hxO⟩, fun hxC => hx.2 (Or.inl hxC)⟩
          · exact Or.inr ⟨⟨hx.1, hxO⟩, fun hxD => hx.2 (Or.inr hxD)⟩
      _ ≤ μ ((A ∩ g ⁻¹' O k) \ C k) + μ ((A \ g ⁻¹' O k) \ D k) := measure_union_le _ _
      _ < η k / 2 + η k / 2 := ENNReal.add_lt_add (hCμ k) (hDμ k)
      _ = η k := ENNReal.add_halves _
  -- `K = ⋂ₖ E_k` is closed inside the compact `E_0 ⊆ A`
  refine ⟨⋂ k, (C k ∪ D k), ?_, ?_, ?_, ?_⟩
  · exact ((hC 0).union (hD 0)).of_isClosed_subset
      (isClosed_iInter fun k => ((hC k).union (hD k)).isClosed) (iInter_subset _ 0)
  · exact (iInter_subset _ 0).trans
      (union_subset ((hCA 0).trans inter_subset_left) ((hDA 0).trans sdiff_subset))
  · calc μ (A \ ⋂ k, (C k ∪ D k)) = μ (⋃ k, A \ (C k ∪ D k)) := by rw [sdiff_iInter]
      _ ≤ ∑' k, μ (A \ (C k ∪ D k)) := measure_iUnion_le _
      _ ≤ ∑' k, η k := ENNReal.tsum_le_tsum fun k => (hE k).le
      _ < ε := hηε
  -- on `K`, `g x ∈ O_k ↔ x ∉ D_k`, so `g⁻¹(O_k) ∩ K = D_kᶜ ∩ K` is relatively open
  · rw [hO.continuousOn_iff]
    rintro _ ⟨k, rfl⟩
    refine ⟨(D k)ᶜ, (hD k).isClosed.isOpen_compl, ?_⟩
    ext x
    refine ⟨fun ⟨hxO, hxK⟩ => ⟨fun hxD => (hDA k hxD).2 hxO, hxK⟩, fun ⟨hxD, hxK⟩ => ⟨?_, hxK⟩⟩
    rcases mem_iInter.mp hxK k with hxC | hxD'
    · exact (hCA k hxC).2
    · exact absurd hxD' hxD

/-- **Lusin's theorem** (Simon 1.17) for a `μ`-a.e. strongly measurable covector field
`f : ℝᴾ → Λⁿ(ℝᴾ)`.  `Λⁿ(ℝᴾ)` is finite-dimensional, hence second countable; give it the Borel
σ-algebra.  `f` agrees with the Borel modification `f' = hf.mk f` off a measurable `μ`-null set
`Z`, and Lusin's theorem for `f'` on `A \ Z` gives a compact `K ⊆ A \ Z` with
`μ((A \ Z) \ K) < ε` on which `f = f'` is continuous.  As `μ(Z) = 0`,
`μ(A \ K) = μ((A \ K) \ Z) = μ((A \ Z) \ K)`. -/
theorem Submission.dor_ims_lusin_continuousOn : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)) (f : Euclid P → Covector (Euclid P) n) (ε : ℝ), MeasurableSet A → μ A ≠ ∞ → AEStronglyMeasurable f μ → 0 < ε → ∃ K : Set (Euclid P), IsCompact K ∧ K ⊆ A ∧ μ (A \ K) < ENNReal.ofReal ε ∧ ContinuousOn f K := by
  intro P n μ A f ε hA hμA hf hε
  -- `Λⁿ(ℝᴾ)` is finite-dimensional, hence proper and second countable
  have := Submission.dor_ims_lusin_covector_finiteDimensional P n
  borelize (Covector (Euclid P) n)
  -- `f = f'` off a measurable null set `Z`
  obtain ⟨Z, hfZ, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.mp hf.ae_eq_mk)
  obtain ⟨K, hK, hKA, hKμ, hfK⟩ := Submission.dor_ims_lusin_measurable_continuousOn P μ (A \ Z)
    (hf.mk f) (ENNReal.ofReal ε) hf.measurable_mk (hA.diff hZ)
    (ne_top_of_le_ne_top hμA (measure_mono sdiff_subset)) (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨K, hK, hKA.trans sdiff_subset, ?_, hfK.congr fun x hx => ?_⟩
  · rwa [← measure_sdiff_null hZ0, sdiff_right_comm]
  · by_contra hfx
    exact (hKA hx).2 (hfZ hfx)
/-- **The Euclidean coefficient norm is a pulled-back Euclidean norm** (Simon Ch. 6, 1.2 and 1.5;
used by the smooth unit approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard
basis of `ℝᴾ`, let `c_I α = α(e_{I(0)}, …, e_{I(n-1)})` for strictly increasing `I : Fin n → Fin P`
and `c_I = 0` otherwise.  Each `c_I` is a continuous linear functional, so
`A α = (c_I α)_I ∈ EuclideanSpace ℝ (Fin n → Fin P)` is continuous linear, and termwise
`‖A α‖ = √(∑_I c_I(α)²)` is the defining sum of `covectorEuclideanNorm α`. -/
theorem Submission.dor_ims_sua_coeff_norm_rep : ∀ (P n : ℕ), ∃ A : Covector (Euclid P) n →L[ℝ] EuclideanSpace ℝ (Fin n → Fin P), ∀ α : Covector (Euclid P) n, covectorEuclideanNorm α = ‖A α‖ := by
  intro P n
  -- Step 1: the coefficient functionals `c_I : α ↦ α(e_I)` for increasing `I`, else `0`
  let c : (Fin n → Fin P) → Covector (Euclid P) n →L[ℝ] ℝ := fun I =>
    if StrictMono I then
      ContinuousAlternatingMap.apply ℝ (Euclid P) ℝ fun i => EuclideanSpace.basisFun (Fin P) ℝ (I i)
    else 0
  -- Step 2: `A α = (c_I α)_I`, moved into `EuclideanSpace ℝ (Fin n → Fin P)`
  refine ⟨(EuclideanSpace.equiv (Fin n → Fin P) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi c), fun α => ?_⟩
  -- Step 3: `‖A α‖ = √(∑_I |c_I α|²)` and `|c_I α|² = [StrictMono I] α(e_I)²` termwise
  rw [EuclideanSpace.norm_eq, covectorEuclideanNorm]
  congr 1
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hI : StrictMono I <;> simp [c, hI]
/-- **`Λⁿ(ℝᴾ)` is finite-dimensional** (Simon Ch. 6, 1.2; used by Tietze in the smooth unit
approximation behind the mass of `τ(M, θ, ξ)`).  With `e` the standard basis of `ℝᴾ`, the map
`Φ α = (α(e_{v(0)}, …, e_{v(n-1)}))_{v : Fin n → Fin P}` is linear into the finite-dimensional
space `ℝ^(Fin n → Fin P)`, and injective: alternating maps agreeing on distinct basis vectors are
equal, and a continuous alternating map is determined by its underlying alternating map. -/
theorem Submission.dor_ims_sua_covector_finiteDimensional : ∀ (P n : ℕ), FiniteDimensional ℝ (Covector (Euclid P) n) := by
  intro P n
  -- Step 1: the standard basis `e` of `ℝᴾ`
  let e := (EuclideanSpace.basisFun (Fin P) ℝ).toBasis
  -- Step 2: `Φ α = (α(e ∘ v))_v`, linear since covector operations are pointwise
  let Φ : Covector (Euclid P) n →ₗ[ℝ] ((Fin n → Fin P) → ℝ) :=
    { toFun := fun α v => α fun i => e (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  -- Steps 3–4: `Φ` is injective into the finite-dimensional `(Fin n → Fin P) → ℝ`
  refine FiniteDimensional.of_injective Φ fun α α' h => ?_
  exact ContinuousAlternatingMap.toAlternatingMap_injective
    (e.ext_alternating fun v _ => congr_fun h v)
/-- **Continuous unit extension** (steps 0 and 2–5 of the smooth unit approximation behind the
mass of `τ(M, θ, ξ)`).  Let `K ⊆ V ⊆ ℝᴾ`, `K` compact, `V` open, and let `β : ℝᴾ → Λⁿ(ℝᴾ)` be
continuous on `K` with `|β| ≤ 1` there, `|·|` the Euclidean coefficient norm.  Then `β|_K`
extends to a continuous `g` with compact support in `V` and `|g| ≤ 1` everywhere.  Tietze is
proved in place for the complete normed space `Λⁿ(ℝᴾ)`: partitions of unity subordinate to
finite `δ`-nets of `K` give continuous `G_k` with `‖G_k - β‖ ≤ 2⁻ᵏ` on `K`, and
`B = G₀ + ∑ₖ D_k`, with `D_k` the difference `G_{k+1} - G_k` clamped to the ball of radius
`2 · 2⁻ᵏ`, is a uniformly convergent series of continuous maps equal to `β` on `K`.  Then retract
radially by `ρ(α) = max(1, |α|)⁻¹ α` and cut off by `χ = max(0, 1 − dist(·, K)/r)` with
`cthickening r K ⊆ V`; `g = χ · (ρ ∘ B)`. -/
theorem Submission.dor_ims_sua_continuous_unit_extension : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → ∃ g : Euclid P → Covector (Euclid P) n, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ V ∧ (∀ x, covectorEuclideanNorm (g x) ≤ 1) ∧ ∀ x ∈ K, g x = β x := by
  intro P n K V β hK hV hKV hβ hβ1
  -- Step 0: if `K = ∅`, take `g = 0`
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨0, continuous_zero, HasCompactSupport.zero, by simp, by simp, by simp⟩
  -- Step 1: `|α| = ‖A α‖`, so `|·|` is continuous and `|c • α| = |c| |α|`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hN1 : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    simpa only [hA] using A.continuous.norm
  have hN2 : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    rw [hA, hA, map_smul, norm_smul, Real.norm_eq_abs]
  -- Step 2: Tietze, a continuous `B` with `B = β` on `K`
  obtain ⟨B, hBc, hBK⟩ : ∃ B : Euclid P → Covector (Euclid P) n, Continuous B ∧
      ∀ x ∈ K, B x = β x := by
    -- (a) a partition of unity on a finite `δ`-net of `K` averages `β` to within `ε` on `K`
    have happrox : ∀ ε > 0, ∃ G : Euclid P → Covector (Euclid P) n, Continuous G ∧
        ∀ x ∈ K, ‖G x - β x‖ ≤ ε := by
      intro ε hε
      obtain ⟨δ, hδ, hβδ⟩ :=
        Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hβ) ε hε
      obtain ⟨t, htK, hKt⟩ :=
        hK.elim_nhds_subcover (fun a => ball a δ) fun a _ => ball_mem_nhds a hδ
      obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
        (fun a : t => ball (a : Euclid P) δ) (fun a => isOpen_ball) fun x hx => by
          obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hKt hx)
          exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩
      refine ⟨fun x => ∑ a : t, φ a x • β a,
        continuous_finsetSum _ fun a _ => (φ a).continuous.smul continuous_const, fun x hx => ?_⟩
      have h1 : ∑ a : t, φ a x = 1 := by
        rw [← finsum_eq_sum_of_fintype]
        exact φ.sum_eq_one hx
      calc ‖∑ a : t, φ a x • β a - β x‖ = ‖∑ a : t, φ a x • (β a - β x)‖ := by
            simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
        _ ≤ ∑ a : t, ‖φ a x • (β a - β x)‖ := norm_sum_le _ _
        _ ≤ ∑ a : t, φ a x * ε := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_smul, Real.norm_of_nonneg (φ.nonneg a x)]
            rcases eq_or_ne (φ a x) 0 with h | h
            · simp [h]
            · refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg a x)
              rw [← dist_eq_norm]
              exact (hβδ a (htK a a.2) x hx (mem_ball'.1 (hφ a (subset_tsupport _ h)))).le
        _ = ε := by rw [← Finset.sum_mul, h1, one_mul]
    choose G hGc hGK using fun k : ℕ => happrox ((1 / 2) ^ k) (by positivity)
    -- (b) clamp `G_{k+1} - G_k` to the ball of radius `2 · 2⁻ᵏ`; on `K` nothing changes
    have hc : ∀ k : ℕ, 0 < 2 * (1 / 2 : ℝ) ^ k := fun k => by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℕ → Euclid P → Covector (Euclid P) n, ∀ k x,
        D k x = (max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)))⁻¹ • (G (k + 1) x - G k x) :=
      ⟨_, fun _ _ => rfl⟩
    have hDc : ∀ k, Continuous (D k) := by
      intro k
      have hv : Continuous fun x => G (k + 1) x - G k x := (hGc (k + 1)).sub (hGc k)
      refine Continuous.congr ?_ fun x => (hD k x).symm
      exact ((continuous_const.max (hv.norm.div_const _)).inv₀ fun x =>
        (zero_lt_one.trans_le (le_max_left _ _)).ne').smul hv
    have hDb : ∀ k x, ‖D k x‖ ≤ 2 * (1 / 2) ^ k := by
      intro k x
      have hm : 0 < max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) :=
        zero_lt_one.trans_le (le_max_left _ _)
      rw [hD, norm_smul, norm_inv, Real.norm_of_nonneg hm.le, inv_mul_le_iff₀ hm]
      calc ‖G (k + 1) x - G k x‖
          = ‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k) * (2 * (1 / 2) ^ k) :=
            (div_mul_cancel₀ _ (hc k).ne').symm
        _ ≤ max 1 (‖G (k + 1) x - G k x‖ / (2 * (1 / 2) ^ k)) * (2 * (1 / 2) ^ k) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (hc k).le
    have hDK : ∀ k, ∀ x ∈ K, D k x = G (k + 1) x - G k x := by
      intro k x hx
      have h2 : ‖G (k + 1) x - G k x‖ ≤ 2 * (1 / 2) ^ k := by
        calc ‖G (k + 1) x - G k x‖ = ‖(G (k + 1) x - β x) - (G k x - β x)‖ := by
              rw [sub_sub_sub_cancel_right]
          _ ≤ ‖G (k + 1) x - β x‖ + ‖G k x - β x‖ := norm_sub_le _ _
          _ ≤ (1 / 2) ^ (k + 1) + (1 / 2) ^ k := add_le_add (hGK _ x hx) (hGK _ x hx)
          _ ≤ 2 * (1 / 2) ^ k := by
              rw [pow_succ]
              linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]
      rw [hD, max_eq_left ((div_le_one (hc k)).2 h2), inv_one, one_smul]
    -- (c) `B = G₀ + ∑ D_k` converges uniformly; on `K` the series telescopes to `β - G₀`
    refine ⟨fun x => G 0 x + ∑' k, D k x,
      (hGc 0).add (continuous_tsum hDc (summable_geometric_two.mul_left 2) hDb), fun x hx => ?_⟩
    have hs : Summable fun k => D k x :=
      Summable.of_norm_bounded (summable_geometric_two.mul_left 2) fun k => hDb k x
    have hTel : ∀ N, ∑ k ∈ Finset.range N, D k x = G N x - G 0 x := by
      intro N
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, ih, hDK N x hx]; abel
    have hG : Tendsto (fun N => G N x) atTop (𝓝 (β x)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun N => norm_nonneg _) (fun N => hGK N x hx)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hlim := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat
      ((hG.sub_const (G 0 x)).congr fun N => (hTel N).symm)
    show G 0 x + ∑' k, D k x = β x
    rw [hlim]
    abel
  -- Step 3: the radial retraction `ρ(α) = max(1, |α|)⁻¹ α` onto `{|α| ≤ 1}`
  let ρ : Covector (Euclid P) n → Covector (Euclid P) n :=
    fun α => (max 1 (covectorEuclideanNorm α))⁻¹ • α
  have hm : ∀ α : Covector (Euclid P) n, 0 < max 1 (covectorEuclideanNorm α) :=
    fun α => zero_lt_one.trans_le (le_max_left _ _)
  have hρ : Continuous ρ :=
    ((continuous_const.max hN1).inv₀ fun α => (hm α).ne').smul continuous_id
  have hρ1 : ∀ α, covectorEuclideanNorm (ρ α) ≤ 1 := by
    intro α
    rw [hN2, abs_of_pos (inv_pos.2 (hm α))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (hm α).le
  have hρid : ∀ α, covectorEuclideanNorm α ≤ 1 → ρ α = α := by
    intro α hα
    simp [ρ, max_eq_left hα]
  -- Step 4: the cut-off `χ = max(0, 1 − dist(·, K)/r)`, where `cthickening r K ⊆ V`
  obtain ⟨r, hr, hrV⟩ := hK.exists_cthickening_subset_open hV hKV
  let χ : Euclid P → ℝ := fun x => max 0 (1 - infDist x K / r)
  have hχ : Continuous χ :=
    continuous_const.max (continuous_const.sub ((continuous_infDist_pt K).div_const r))
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x =>
    max_le zero_le_one (sub_le_self _ (div_nonneg infDist_nonneg hr.le))
  have hχK : ∀ x ∈ K, χ x = 1 := by
    intro x hx
    simp [χ, infDist_zero_of_mem hx]
  have hχr : ∀ x, χ x ≠ 0 → x ∈ thickening r K := by
    intro x hx
    rw [mem_thickening_iff_infDist_lt hKne]
    by_contra h
    refine hx (max_eq_left ?_)
    rw [sub_nonpos, le_div_iff₀ hr, one_mul]
    exact not_lt.1 h
  -- Step 5: `g = χ · (ρ ∘ B)` has `tsupport g ⊆ cthickening r K ⊆ V`, compact
  have hsupp : support (fun x => χ x • ρ (B x)) ⊆ thickening r K := fun x hx =>
    hχr x fun h => hx (by simp [h])
  have htsupp : tsupport (fun x => χ x • ρ (B x)) ⊆ cthickening r K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening r K)
  refine ⟨fun x => χ x • ρ (B x), hχ.smul (hρ.comp hBc),
    hK.cthickening.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hrV,
    fun x => ?_, fun x hx => ?_⟩
  · -- `|g x| = χ x |ρ (B x)| ≤ χ x ≤ 1`
    rw [hN2, abs_of_nonneg (hχ0 x)]
    exact (mul_le_of_le_one_right (hχ0 x) (hρ1 _)).trans (hχ1 x)
  · -- on `K`: `χ = 1`, `B = β` and `|β| ≤ 1`, so `g = ρ ∘ β = β`
    simp only [hχK x hx, one_smul, hBK x hx, hρid _ (hβ1 x hx)]

/-- **Mollifying a unit covector field** (smooth unit approximation, step 6).  A continuous,
compactly supported `n`-covector field `g` with `tsupport g ⊆ V` (`V` open) and `|g| ≤ 1` for the
Euclidean coefficient norm `|·|` is uniformly `ε`-approximated in `|·|` by a test form `ω` with
`tsupport ω ⊆ V` and `|ω| ≤ 1`.

Write `|α| = ‖Aα‖` for a continuous linear coefficient map `A` (`dor_ims_sua_coeff_norm_rep`), so
`|α| ≤ ‖A‖‖α‖`.  Take `r > 0` with `cthickening r (tsupport g) ⊆ V`, and `s ≤ r` such that
`‖g y − g x‖ < ε/(‖A‖+1)` when `dist y x < s` (uniform continuity).  Let `ω = ψ ⋆ g`, where
`ψ = φ / ∫ φ` normalizes a smooth bump `φ ≥ 0` with `support φ = B_s(0)`.  Then `ω` is `C^∞` with
compact support and `tsupport ω ⊆ cthickening s (tsupport g) ⊆ V`; `Aω(x) = (ψ ⋆ (A ∘ g))(x)` is
an average of values of norm `|g| ≤ 1`; and `‖ω(x) − g(x)‖ ≤ ε/(‖A‖+1)`, whence
`|ω(x) − g(x)| ≤ ε`. -/
theorem Submission.dor_ims_sua_mollify_unit_field : ∀ (P n : ℕ) (V : Set (Euclid P)) (g : Euclid P → Covector (Euclid P) n) (ε : ℝ), IsOpen V → Continuous g → HasCompactSupport g → tsupport g ⊆ V → (∀ x, covectorEuclideanNorm (g x) ≤ 1) → 0 < ε → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x, covectorEuclideanNorm (ω x - g x) ≤ ε := by
  intro P n V g ε hV hgc hgs hgV hg1 hε
  -- (1) the coefficient map `A` with `|α| = ‖A α‖ ≤ ‖A‖ ‖α‖`
  obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
  have hC : 0 < ‖A‖ + 1 := by positivity
  -- (2) a support margin `r`
  obtain ⟨r, hr, hrV⟩ := hgs.isCompact.exists_cthickening_subset_open hV hgV
  -- (3) uniform continuity of `g`, and the radius `s = min s₀ r`
  obtain ⟨s₀, hs₀, hgs₀⟩ := Metric.uniformContinuous_iff.mp
    (hgs.uniformContinuous_of_continuous hgc) (ε / (‖A‖ + 1)) (div_pos hε hC)
  have hs : 0 < min s₀ r := lt_min hs₀ hr
  -- (4) a smooth bump `φ` with `support φ = B_s(0)`, and `ψ = φ / ∫ φ`: `ψ ≥ 0`, `∫ ψ = 1`
  let φ : ContDiffBump (0 : Euclid P) := ⟨min s₀ r / 2, min s₀ r, half_pos hs, half_lt_self hs⟩
  have hφ : 0 < ∫ y, φ y := by
    refine (integral_pos_iff_support_of_nonneg φ.nonneg'
      (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport)).mpr ?_
    rw [φ.support_eq]
    exact measure_ball_pos volume 0 hs
  let ψ : Euclid P → ℝ := fun y => φ y / ∫ y, φ y
  have hψφ : support ψ ⊆ support φ := fun y hy h => hy (by simp [ψ, h])
  have hψs : support ψ ⊆ ball 0 (min s₀ r) := hψφ.trans φ.support_eq.subset
  have hψc : HasCompactSupport ψ := φ.hasCompactSupport.mono hψφ
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => div_nonneg φ.nonneg hφ.le
  have hψ1 : ∫ y, ψ y = 1 := by rw [integral_div, div_self hφ.ne']
  -- (5) `ω = ψ ⋆ g`
  let ω : DifferentialForm (Euclid P) n :=
    convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume
  have hgi : LocallyIntegrable g volume := hgc.locallyIntegrable
  have hω : ConvolutionExists ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    hψc.convolutionExists_left _ (φ.continuous.div_const _) hgi
  refine ⟨ω, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- (6) smoothness
    exact hψc.contDiff_convolution_left _ (φ.contDiff.div_const _) hgi
  · exact hψc.convolution _ hgs
  · -- (7) `spt ω ⊆ cthickening s (tsupport g) ⊆ V`
    have hsupp : support ω ⊆ thickening (min s₀ r) (tsupport g) := by
      refine (support_convolution_subset _).trans ?_
      rintro _ ⟨t, ht, z, hz, rfl⟩
      have ht' : ‖t‖ < min s₀ r := mem_ball_zero_iff.mp (hψs ht)
      exact mem_thickening_iff.mpr ⟨z, subset_tsupport g hz, by
        rwa [dist_eq_norm, add_sub_cancel_right]⟩
    calc tsupport ω ⊆ closure (thickening (min s₀ r) (tsupport g)) := closure_mono hsupp
      _ ⊆ cthickening (min s₀ r) (tsupport g) := closure_thickening_subset_cthickening _ _
      _ ⊆ cthickening r (tsupport g) := cthickening_mono (min_le_right _ _) _
      _ ⊆ V := hrV
  · -- (8) `|ω x| = ‖(ψ ⋆ (A ∘ g)) x‖ ≤ 1`
    intro x
    have hAω : A (ω x) = convolution ψ (fun y => A (g y))
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      calc A (ω x) = ∫ t, A (ContinuousLinearMap.lsmul ℝ ℝ (ψ t) (g (x - t))) :=
            (A.integral_comp_comm (hω x).integrable).symm
        _ = _ := by simp only [convolution_def, ContinuousLinearMap.lsmul_apply, map_smul]
    rw [hA, hAω, ← dist_zero_right]
    exact dist_convolution_le zero_le_one hψs hψ0 hψ1
      (A.continuous.comp hgc).aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
  · -- (9) `‖ω x − g x‖ ≤ ε/(‖A‖+1)`, hence `|ω x − g x| ≤ ‖A‖ ε/(‖A‖+1) ≤ ε`
    intro x
    have hd : dist (ω x) (g x) ≤ ε / (‖A‖ + 1) :=
      dist_convolution_le (div_pos hε hC).le hψs hψ0 hψ1 hgc.aestronglyMeasurable fun y hy =>
        (hgs₀ ((mem_ball.mp hy).trans_le (min_le_left _ _))).le
    calc covectorEuclideanNorm (ω x - g x) = ‖A (ω x - g x)‖ := hA _
      _ ≤ ‖A‖ * dist (ω x) (g x) := by rw [dist_eq_norm]; exact A.le_opNorm _
      _ ≤ ‖A‖ * (ε / (‖A‖ + 1)) := by gcongr
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith [norm_nonneg A]

/-- **Smooth unit approximation** (Simon Ch. 6, 1.15 and 2.5; steps 4(c)–(d) of the mass formula
`M_W(T) = μ_T(W)` of Remark 3.2(3) for `T = τ(M, θ, ξ)`).  Extend `β|_K` to a continuous unit
field `g` with compact support in `V` and `g = β` on `K` (Tietze extension, radial retraction,
cut-off), then mollify: `ω = ψ ⋆ g` with `ψ = φ / ∫ φ` for a smooth bump `φ` supported in
`B_s(0)`, where `cthickening s (spt g) ⊆ V` and `s` is a modulus of uniform continuity of `𝒜 ∘ g`
for `δ`, `𝒜` being the coefficient map with `|α| = ‖𝒜 α‖`.  As `𝒜` commutes with the Bochner
integral, `𝒜 (ω x)` is a `ψ`-average of the values `𝒜 (g y)`, `|y - x| < s`; hence `|ω x| ≤ 1`
and `|ω x - g x| ≤ δ`, which is `|ω x - β x| ≤ δ` on `K`. -/
theorem Submission.dor_ims_smooth_unit_approx : ∀ (P n : ℕ) (K V : Set (Euclid P)) (β : Euclid P → Covector (Euclid P) n) (δ : ℝ), IsCompact K → IsOpen V → K ⊆ V → ContinuousOn β K → (∀ x ∈ K, covectorEuclideanNorm (β x) ≤ 1) → 0 < δ → ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧ tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧ ∀ x ∈ K, covectorEuclideanNorm (ω x - β x) ≤ δ := by
  intro P n K V β δ hK hV hKV hβ hβ1 hδ
  -- Steps 2–5: a continuous unit field `g`, compactly supported in `V`, with `g = β` on `K`
  obtain ⟨g, hg, hgc, hgV, hg1, hgK⟩ :=
    Submission.dor_ims_sua_continuous_unit_extension P n K V β hK hV hKV hβ hβ1
  -- Step 6: mollify `g` into a test form `ω` in `V` with `|ω| ≤ 1` and `|ω - g| ≤ δ` everywhere
  obtain ⟨ω, hω, hωV, hω1, hωg⟩ : ∃ ω : DifferentialForm (Euclid P) n, IsTestForm ω ∧
      tsupport ω ⊆ V ∧ (∀ x, covectorEuclideanNorm (ω x) ≤ 1) ∧
      ∀ x, covectorEuclideanNorm (ω x - g x) ≤ δ := by
    -- Step 1: the coefficient map `𝒜`, with `|α| = ‖𝒜 α‖`
    obtain ⟨A, hA⟩ := Submission.dor_ims_sua_coeff_norm_rep P n
    -- `cthickening r (spt g) ⊆ V`, as in step 4
    obtain ⟨r, hr, hrV⟩ := hgc.isCompact.exists_cthickening_subset_open hV hgV
    -- `𝒜 ∘ g` is continuous with compact support, so uniformly continuous; `s₀` is a modulus
    -- for `δ`
    have hAg : Continuous fun y => A (g y) := A.continuous.comp hg
    obtain ⟨s₀, hs₀, hs₀δ⟩ := Metric.uniformContinuous_iff.1
      ((hgc.comp_left (map_zero A)).uniformContinuous_of_continuous hAg) δ hδ
    -- the kernel: `ψ = φ / ∫ φ` for the bump `φ` with `support φ = B_s(0)`, `s = min r s₀`, is
    -- `C^∞` with compact support, `ψ ≥ 0`, `∫ ψ = 1` and `support ψ ⊆ B_s(0)`
    have hs : 0 < min r s₀ := lt_min hr hs₀
    obtain ⟨ψ, hψ, hψc, hψ0, hψ1, hψs⟩ : ∃ ψ : Euclid P → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
        HasCompactSupport ψ ∧ (∀ y, 0 ≤ ψ y) ∧ ∫ y, ψ y = 1 ∧
        support ψ ⊆ ball 0 (min r s₀) := by
      let φ : ContDiffBump (0 : Euclid P) := ⟨min r s₀ / 2, min r s₀, half_pos hs, half_lt_self hs⟩
      have hφ : 0 < ∫ y, φ y := by
        rw [integral_pos_iff_support_of_nonneg φ.nonneg'
          (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport), φ.support_eq]
        exact measure_ball_pos _ _ hs
      have hsupp : support (fun y => φ y / ∫ y, φ y) ⊆ support φ := fun y hy =>
        (div_ne_zero_iff.1 hy).1
      exact ⟨fun y => φ y / ∫ y, φ y, φ.contDiff.div_const _, φ.hasCompactSupport.mono hsupp,
        fun y => div_nonneg φ.nonneg hφ.le, by rw [integral_div, div_self hφ.ne'],
        hsupp.trans φ.support_eq.subset⟩
    -- `ω = ψ ⋆ g`, and (N4): `𝒜` commutes with the Bochner integral, so `𝒜 ∘ ω = ψ ⋆ (𝒜 ∘ g)`
    have hψg : ∀ x, ConvolutionExistsAt ψ g x (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
      hψc.convolutionExists_left _ hψ.continuous hg.locallyIntegrable
    have hAω : ∀ x, A (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x) =
        convolution ψ (fun y => A (g y)) (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
      intro x
      rw [convolution_def, convolution_def, ← A.integral_comp_comm (hψg x).integrable]
      simp only [ContinuousLinearMap.lsmul_apply, map_smul]
    refine ⟨convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    -- 6(i): `ω` is `C^∞` with compact support
    · exact hψc.contDiff_convolution_left _ hψ hg.locallyIntegrable
    · exact hψc.convolution _ hgc
    -- 6(ii): `support ω ⊆ B_s(0) + spt g = thickening s (spt g)`, so
    -- `spt ω ⊆ cthickening s (spt g) ⊆ cthickening r (spt g) ⊆ V`
    · have hsupp : support (convolution ψ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) ⊆
          thickening (min r s₀) (tsupport g) := by
        refine (support_convolution_subset _).trans ?_
        rw [← ball_add_zero]
        exact add_subset_add hψs (subset_tsupport g)
      exact (closure_minimal (hsupp.trans (thickening_subset_cthickening _ _))
        isClosed_cthickening).trans ((cthickening_mono (min_le_left r s₀) _).trans hrV)
    -- 6(iii): `|ω x| = ‖(ψ ⋆ 𝒜 ∘ g) x‖ ≤ 1`, since `‖𝒜 (g y)‖ = |g y| ≤ 1`
    · intro x
      rw [hA, hAω, ← dist_zero_right]
      exact dist_convolution_le zero_le_one hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y _ => by
        rw [dist_zero_right, ← hA]
        exact hg1 y
    -- 6(iv): `|ω x - g x| = ‖(ψ ⋆ 𝒜 ∘ g) x - 𝒜 (g x)‖ ≤ δ`, since `|y - x| < s ≤ s₀`
    · intro x
      rw [hA, map_sub, hAω, ← dist_eq_norm]
      exact dist_convolution_le hδ.le hψs hψ0 hψ1 hAg.aestronglyMeasurable fun y hy =>
        (hs₀δ ((mem_ball.1 hy).trans_le (min_le_right r s₀))).le
  -- Step 7: `g = β` on `K`
  refine ⟨ω, hω, hωV, hω1, fun x hx => ?_⟩
  rw [← hgK x hx]
  exact hωg x

/-- **Simon Ch. 6, 3.2(3)** (lower bound): if `T = τ(M, θ, ξ)` in the open set `U`, then
`μ_R(W) = ∫_{M ∩ W} θ dHⁿ ≤ M_W(T)` for every open `W`.  As `μ_R` lives on `M ⊆ U`, replace `W`
by `G = W ∩ U` and pick a compact `K ⊆ G` of nearly full measure.  With `L` from
`dor_ims_unitOrientation_dual`, `μ_R`-a.e. `|ξ(α)| ≤ |α|`, `|L ξ| ≤ 1` and `ξ(L ξ) = 1`; by
Lusin, `β = L ∘ ξ` is continuous on a compact `K' ⊆ K` with `μ_R(K \ K') < η`.  A thin open
thickening `V` of `K'` has `μ_R(V \ K') < η`, and a smooth admissible `ω` supported in `V` with
`|ω - β| ≤ δ` on `K'` has `T(ω) = ∫ ξ(ω) dμ_R ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`, close to
`μ_R(G)`. -/
theorem Submission.dor_ims_measure_le_massOn : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → ∀ W : Set (Euclid P), IsOpen W → R.measure W ≤ T.massOn W := by
  intro P n U T R hU hR W hW
  obtain ⟨L, hL⟩ := Submission.dor_ims_unitOrientation_dual P n
  -- `μ_R ≪ Hⁿ⌞M`, so `μ_R`-a.e. `x` is good: `|ξ(x)(α)| ≤ |α|`, `|L ξ(x)| ≤ 1`, `ξ(x)(L ξ(x)) = 1`
  have hac : R.measure ≪ μHE[n].restrict R.carrier := withDensity_absolutelyContinuous _ _
  have hgood : ∀ᵐ x ∂R.measure,
      (∀ α : Covector (Euclid P) n, |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 := by
    refine hac.ae_le ?_
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact hL _ Q hQ
  -- a measurable `μ_R`-null set `Z` containing every bad point
  obtain ⟨Z, hZ, hZm, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hβm : AEStronglyMeasurable (fun x => L (R.orient x)) R.measure :=
    L.continuous.comp_aestronglyMeasurable (R.aestronglyMeasurable_orient.mono_ac hac)
  -- `μ_R(K) < ∞` for compact `K ⊆ U`, and `μ_R(ℝᴾ \ U) = 0`, so `μ_R(W) = μ_R(W ∩ U)`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → R.measure K < ∞ := by
    intro K hK hKU
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hUc : R.measure Uᶜ = 0 := by
    refine hac ?_
    rw [Measure.restrict_apply hU.measurableSet.compl]
    exact measure_mono_null (fun x hx => absurd (R.carrier_subset hx.2) hx.1) measure_empty
  have hG : IsOpen (W ∩ U) := hW.inter hU
  have hWG : R.measure W = R.measure (W ∩ U) := by
    rw [← measure_inter_add_sdiff W hU.measurableSet,
      measure_mono_null (show W \ U ⊆ Uᶜ from fun x hx => hx.2) hUc, add_zero]
  -- it suffices to beat every `r < μ_R(W)`; fix `η > 0` with `r + 4η < μ_R(W ∩ U)`
  refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  obtain ⟨ε, hε0, hrε⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hr
  set η : ℝ := (ε : ℝ) / 4 with hη
  have hη0 : 0 < η := div_pos (NNReal.coe_pos.2 hε0) four_pos
  -- compact `K ⊆ W ∩ U` with `r + 4η < μ_R(K)`, from the exhaustion `Fⱼ ∩ B̄ⱼ(0)` of `W ∩ U`
  obtain ⟨F, hFc, hFG, hFU, hFm⟩ := hG.exists_iUnion_isClosed
  have hKm : Monotone fun j : ℕ => F j ∩ closedBall (0 : Euclid P) j := fun i j hij =>
    inter_subset_inter (hFm hij) (closedBall_subset_closedBall (Nat.cast_le.2 hij))
  have hKU : ⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j = W ∩ U := by
    refine Subset.antisymm (iUnion_subset fun j => inter_subset_left.trans (hFG j))
      fun x hx => ?_
    rw [← hFU] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.1 hx
    obtain ⟨k, hk⟩ := exists_nat_ge ‖x‖
    refine mem_iUnion.2 ⟨max i k, hFm (le_max_left i k) hi, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    exact hk.trans (Nat.cast_le.2 (le_max_right i k))
  have hlt : (r : ℝ≥0∞) + ε < R.measure (⋃ j : ℕ, F j ∩ closedBall (0 : Euclid P) j) := by
    rwa [hKU, ← hWG]
  obtain ⟨j, hj⟩ :=
    ((tendsto_order.1 (tendsto_measure_iUnion_atTop (μ := R.measure) hKm)).1 _ hlt).exists
  set K := F j ∩ closedBall (0 : Euclid P) j
  have hrK : (r : ℝ≥0∞) + ε < R.measure K := hj
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_left (hFc j)
  have hKG : K ⊆ W ∩ U := inter_subset_left.trans (hFG j)
  have hKfin : R.measure K < ∞ := hfin K hKc (hKG.trans inter_subset_right)
  -- Lusin: a compact `K' ⊆ K \ Z` with `μ_R(K \ K') < η` on which `β = L ∘ ξ` is continuous
  obtain ⟨K', hK'c, hK'K, hK'small, hβc⟩ := Submission.dor_ims_lusin_continuousOn P n
    R.measure (K \ Z) (fun x => L (R.orient x)) η (hKc.measurableSet.diff hZm)
    ((measure_mono sdiff_subset).trans_lt hKfin).ne hβm hη0
  have hgoodK' : ∀ x ∈ K', (∀ α : Covector (Euclid P) n,
      |R.orient x α| ≤ covectorEuclideanNorm α) ∧
        covectorEuclideanNorm (L (R.orient x)) ≤ 1 ∧ R.orient x (L (R.orient x)) = 1 :=
    fun x hx => by
      by_contra h
      exact (hK'K hx).2 (hZ h)
  have hK'G : K' ⊆ W ∩ U := hK'K.trans (sdiff_subset.trans hKG)
  have hK'm : MeasurableSet K' := hK'c.measurableSet
  have hK'fin : R.measure K' ≠ ∞ := ((measure_mono (hK'K.trans sdiff_subset)).trans_lt hKfin).ne
  have hKK' : R.measure (K \ K') < ENNReal.ofReal η := by
    calc R.measure (K \ K') ≤ R.measure ((K \ Z) \ K' ∪ Z) := measure_mono fun x hx => by
          by_cases hxZ : x ∈ Z
          · exact Or.inr hxZ
          · exact Or.inl ⟨⟨hx.1, hxZ⟩, hx.2⟩
      _ ≤ R.measure ((K \ Z) \ K') + R.measure Z := measure_union_le _ _
      _ < ENNReal.ofReal η := by rwa [hZ0, add_zero]
  -- a thin open thickening `V` of `K'`: `K' ⊆ V ⊆ W ∩ U` and `μ_R(V \ K') < η`
  obtain ⟨ρ, hρ0, hρG⟩ := hK'c.exists_cthickening_subset_open hG hK'G
  have hthick : R.measure (thickening ρ K') ≠ ∞ :=
    ((measure_mono (thickening_subset_cthickening_of_le (le_refl ρ) K')).trans_lt
      (hfin _ hK'c.cthickening (hρG.trans inter_subset_right))).ne
  obtain ⟨t, htV, ht⟩ := (((tendsto_order.1 (tendsto_measure_thickening_of_isClosed
    ⟨ρ, hρ0, hthick⟩ hK'c.isClosed)).2 _ (ENNReal.lt_add_right hK'fin
      (ENNReal.ofReal_pos.2 hη0).ne')).and (Ioo_mem_nhdsGT hρ0)).exists
  set V := thickening t K'
  have hK'V : K' ⊆ V := self_subset_thickening ht.1 K'
  have hVG : V ⊆ W ∩ U := (thickening_subset_cthickening_of_le ht.2.le K').trans hρG
  have hVK' : R.measure (V \ K') < ENNReal.ofReal η :=
    measure_sdiff_lt_of_lt_add hK'm.nullMeasurableSet hK'V hK'fin htV
  have hVK'fin : R.measure (V \ K') ≠ ∞ := (hVK'.trans ENNReal.ofReal_lt_top).ne
  have hVK'm : MeasurableSet (V \ K') := isOpen_thickening.measurableSet.diff hK'm
  -- a smooth admissible form `ω` supported in `V` with `|ω - β| ≤ δ` on `K'`
  set m : ℝ := R.measure.real K
  have hm0 : 0 ≤ m := measureReal_nonneg
  set δ : ℝ := η / (m + 1) with hδ
  have hδ0 : 0 < δ := div_pos hη0 (by linarith)
  obtain ⟨ω₀, hω₀t, hω₀V, hω₀1, hω₀β⟩ := Submission.dor_ims_smooth_unit_approx P n K' V
    (fun x => L (R.orient x)) δ hK'c isOpen_thickening hK'V hβc
    (fun x hx => (hgoodK' x hx).2.1) hδ0
  let ω : TestFormOn U n := ⟨ω₀, hω₀t, hω₀V.trans (hVG.trans inter_subset_right)⟩
  have hadm : ω ∈ massAdmissibleOn U n W := ⟨hω₀V.trans (hVG.trans inter_subset_left), hω₀1⟩
  obtain ⟨hfi, hfe⟩ := Submission.dor_ims_action_eq_integral P n U R ω
  -- `ξ(ω) ≥ (1 - δ) 1_{K'} - 1_{V \ K'}` a.e., hence `T(ω) ≥ (1 - δ) μ_R(K') - μ_R(V \ K')`
  have hi1 : Integrable (K'.indicator fun _ => 1 - δ) R.measure :=
    (integrableOn_const (C := 1 - δ) hK'fin).integrable_indicator hK'm
  have hi2 : Integrable ((V \ K').indicator fun _ => (1 : ℝ)) R.measure :=
    (integrableOn_const (C := (1 : ℝ)) hVK'fin).integrable_indicator hVK'm
  have hle : (fun x => K'.indicator (fun _ => 1 - δ) x -
      (V \ K').indicator (fun _ => (1 : ℝ)) x) ≤ᵐ[R.measure]
        fun x => R.orient x ((ω : DifferentialForm (Euclid P) n) x) := by
    filter_upwards [hgood] with x hx
    obtain ⟨hx1, -, hx3⟩ := hx
    change _ ≤ R.orient x (ω₀ x)
    by_cases hxK' : x ∈ K'
    · rw [indicator_of_mem hxK', indicator_of_notMem (fun h => h.2 hxK'), sub_zero]
      have h1 := hx1 (ω₀ x - L (R.orient x))
      have h2 : covectorEuclideanNorm (ω₀ x - L (R.orient x)) ≤ δ := hω₀β x hxK'
      rw [map_sub, hx3] at h1
      linarith [neg_abs_le (R.orient x (ω₀ x) - 1)]
    · rw [indicator_of_notMem hxK', zero_sub]
      by_cases hxV : x ∈ V
      · rw [indicator_of_mem (show x ∈ V \ K' from ⟨hxV, hxK'⟩)]
        linarith [neg_abs_le (R.orient x (ω₀ x)), hx1 (ω₀ x), hω₀1 x]
      · rw [indicator_of_notMem (fun h => hxV h.1), neg_zero,
          image_eq_zero_of_notMem_tsupport (fun h => hxV (hω₀V h)), map_zero]
  have hint : ∫ x, (K'.indicator (fun _ => 1 - δ) x - (V \ K').indicator (fun _ => (1 : ℝ)) x)
      ∂R.measure ≤ ∫ x, R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂R.measure :=
    integral_mono_ae (hi1.sub hi2) hfi hle
  rw [integral_sub hi1 hi2, integral_indicator_const _ hK'm, integral_indicator_const _ hVK'm,
    smul_eq_mul, smul_eq_mul, mul_one, ← hfe, ← hR ω] at hint
  -- arithmetic: `T(ω) > r`
  have hm1 : (r : ℝ) + ε < m := by
    have := ENNReal.toReal_strict_mono hKfin.ne hrK
    rwa [ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.coe_toReal] at this
  have hc : R.measure.real (K \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hKK'
  have hb : R.measure.real (V \ K') < η := ENNReal.toReal_lt_of_lt_ofReal hVK'
  have hsplit : R.measure.real (K ∩ K') + R.measure.real (K \ K') = m :=
    measureReal_inter_add_sdiff hK'm hKfin.ne
  rw [inter_eq_right.2 (hK'K.trans sdiff_subset)] at hsplit
  have hc0 : 0 ≤ R.measure.real (K \ K') := measureReal_nonneg
  have hδm : R.measure.real K' * δ < η := by
    have h1 : m * δ < η := by
      rw [hδ, ← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    have h2 : R.measure.real K' * δ ≤ m * δ :=
      mul_le_mul_of_nonneg_right (by linarith) hδ0.le
    linarith
  have hrT : (r : ℝ) < T ω := by linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal (T ω) := ENNReal.ofReal_le_ofReal hrT.le
    _ ≤ T.massOn W := T.le_massOn hadm
/-- **Support from a mass–measure identity** (Simon 6.2.11–6.2.12).  If `U` is open and
`M_W(T) = μ(W)` for every open `W`, then `spt T = U ∩ spt μ`.  First, `M_W(T) = 0` forces `T` to
vanish on `W`: if `spt ω ⊆ W` and `|ω| ≤ C`, both `±(max C 0 + 1)⁻¹ ω` are admissible for
`M_W(T)`, so `±T(ω) ≤ 0`.  A point of `spt T` with a `μ`-null neighbourhood then has a small ball
`W ⊂⊂ U` with `M_W(T) = μ(W) = 0`, so it lies in the zero region of `T`; and an open `W ∋ x` on
which `T` vanishes has `μ(W) = M_W(T) = 0`, so `x ∉ spt μ`. -/
theorem Submission.dor_ims_support_of_massOn_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (μ : Measure (Euclid P)), IsOpen U → (∀ W : Set (Euclid P), IsOpen W → T.massOn W = μ W) → T.support = U ∩ μ.support := by
  intro P n U T μ hU hmass
  -- Step 1: `|c α| = |c| |α|`, and `α ↦ |α|` is continuous
  have hhom : ∀ (c : ℝ) (α : Covector (Euclid P) n),
      covectorEuclideanNorm (c • α) = |c| * covectorEuclideanNorm α := by
    intro c α
    unfold covectorEuclideanNorm
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs <;> simp [mul_pow]
  have hcont : Continuous fun α : Covector (Euclid P) n => covectorEuclideanNorm α := by
    unfold covectorEuclideanNorm
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun I _ => ?_)
    split_ifs
    · exact (continuous_eval_const _).pow 2
    · exact continuous_const
  -- Step 2: if `M_W(T) = 0`, then `T` vanishes on `W`
  have hvan : ∀ W, T.massOn W = 0 → T.VanishesOn W := by
    intro W hW ω hω
    -- `x ↦ |ω(x)|` is continuous with compact support, hence bounded by some `C`
    obtain ⟨C, hC⟩ := (hcont.comp ω.property.1.1.continuous).bounded_above_of_compact_support
      (ω.property.1.2.comp_left (covectorEuclideanNorm_zero P n))
    set a : ℝ := (max C 0 + 1)⁻¹ with ha_def
    have ha : 0 < a := by positivity
    -- `s • ω` is admissible for `M_W(T)` whenever `|s| = a`
    have hadm : ∀ s : ℝ, |s| = a → s • ω ∈ massAdmissibleOn U n W := by
      intro s hs
      refine ⟨(tsupport_smul_subset_right (fun _ => s) _).trans hω, fun x => ?_⟩
      rw [Submodule.coe_smul, Pi.smul_apply, hhom, hs]
      have hx : covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x) ≤ max C 0 + 1 := by
        have := hC x
        rw [Function.comp_apply, Real.norm_of_nonneg (covectorEuclideanNorm_nonneg _)] at this
        linarith [le_max_left C 0]
      calc a * covectorEuclideanNorm ((ω : DifferentialForm (Euclid P) n) x)
          ≤ a * (max C 0 + 1) := by gcongr
        _ = 1 := inv_mul_cancel₀ (by positivity)
    -- `ofReal (±a T(ω)) ≤ M_W(T) = 0`, so `±a T(ω) ≤ 0`
    have h₁ := T.le_massOn (hadm a (abs_of_pos ha))
    have h₂ := T.le_massOn (hadm (-a) (by rw [abs_neg, abs_of_pos ha]))
    rw [hW, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, map_smul, smul_eq_mul] at h₁ h₂
    have h₃ : T ω ≤ 0 := by nlinarith
    have h₄ : 0 ≤ T ω := by nlinarith
    linarith
  ext x
  simp only [GeometricCurrentOn.support, Set.mem_sdiff, Set.mem_inter_iff]
  constructor
  · -- Step 3: `spt T ⊆ U ∩ spt μ`
    rintro ⟨hxU, hxZ⟩
    refine ⟨hxU, (Measure.mem_support_iff_forall x).2 fun N hN => ?_⟩
    by_contra hpos
    have hN0 : μ N = 0 := by simpa using hpos
    -- `W = B_r(x)` with `r = min(r₁, r₂)/2`, `B_{r₁}(x) ⊆ N` and `B_{r₂}(x) ⊆ U`
    obtain ⟨r₁, hr₁, hball₁⟩ := Metric.mem_nhds_iff.mp hN
    obtain ⟨r₂, hr₂, hball₂⟩ := Metric.isOpen_iff.mp hU x hxU
    have hr : 0 < min r₁ r₂ / 2 := by positivity
    have hrr₁ : min r₁ r₂ / 2 < r₁ := by linarith [min_le_left r₁ r₂]
    have hrr₂ : min r₁ r₂ / 2 < r₂ := by linarith [min_le_right r₁ r₂]
    apply hxZ
    refine ⟨ball x (min r₁ r₂ / 2), ⟨isOpen_ball, ?_, ?_, ?_⟩, mem_ball_self hr⟩
    · -- `closure W` is compact
      exact (isCompact_closedBall x _).of_isClosed_subset isClosed_closure
        closure_ball_subset_closedBall
    · -- `closure W ⊆ B̄_r(x) ⊆ B_{r₂}(x) ⊆ U`
      exact closure_ball_subset_closedBall.trans ((closedBall_subset_ball hrr₂).trans hball₂)
    · -- `M_W(T) = μ(W) ≤ μ(N) = 0`, so `T` vanishes on `W`
      apply hvan
      rw [hmass _ isOpen_ball]
      exact measure_mono_null ((ball_subset_ball hrr₁.le).trans hball₁) hN0
  · -- Step 4: `U ∩ spt μ ⊆ spt T`
    rintro ⟨hxU, hxμ⟩
    refine ⟨hxU, ?_⟩
    rintro ⟨W, ⟨hWo, -, -, hWv⟩, hxW⟩
    -- every admissible `ω` for `M_W(T)` has `T(ω) = 0`, so `μ(W) = M_W(T) = 0`
    have h0 : μ W = 0 := by
      rw [← hmass W hWo]
      refine le_antisymm (sSup_le ?_) zero_le
      rintro _ ⟨ω, hω, rfl⟩
      show ENNReal.ofReal (T ω) ≤ 0
      rw [hWv ω hω.1, ENNReal.ofReal_zero]
    exact ((Measure.mem_support_iff_forall x).1 hxμ W (hWo.mem_nhds hxW)).ne' h0
/-- **Change of variables for `Hⁿ` under the dilation `T(x) = cx`, `c > 0`**: formula (1.1) for the
scaling of the mass measure of a cone (proof of Simon 7.4.5, chapter-07.txt lines 697–699, "by
virtue of the fact that `C` is a cone").  For every `M ⊆ ℝᴾ`: (i) `T_#(Hⁿ⌞T⁻¹(M)) = c⁻ⁿ Hⁿ⌞M`;
(ii) `∫⁻_{T⁻¹(M)} g(cz) dHⁿ(z) = c⁻ⁿ ∫⁻_M g dHⁿ` for every `g : ℝᴾ → [0, ∞]`; (iii) the same for
the Bochner integral of every `g : ℝᴾ → ℝ`.  `T` is a homeomorphism, hence a measurable embedding,
and `T⁻¹(B) = c⁻¹B` with `Hⁿ(c⁻¹B) = c⁻ⁿ Hⁿ(B)` gives `T_#Hⁿ = c⁻ⁿ Hⁿ`; restriction and integrals
commute with the push-forward along `T`. -/
theorem Submission.euclid_hausdorff_dilation_change_of_variables : ∀ (P n : ℕ) (c : ℝ), 0 < c → ∀ M : Set (Euclid P), Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) = ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M ∧ (∀ g : Euclid P → ℝ≥0∞, ∫⁻ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = ENNReal.ofReal (c⁻¹ ^ n) * ∫⁻ y in M, g y ∂μHE[n]) ∧ ∀ g : Euclid P → ℝ, ∫ z in (fun x => c • x) ⁻¹' M, g (c • z) ∂μHE[n] = c⁻¹ ^ n * ∫ y in M, g y ∂μHE[n] := by
  intro P n c hc M
  -- Step 1: `T(x) = cx` is a homeomorphism, hence a measurable embedding.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc.ne').measurableEmbedding
  -- Step 2: `T_#Hⁿ = c⁻ⁿ Hⁿ`, since `Hⁿ(T⁻¹(B)) = Hⁿ(c⁻¹B) = ‖c⁻¹‖ⁿ Hⁿ(B)` for Borel `B`.
  have hmap : Measure.map (fun x : Euclid P => c • x) (μHE[n] : Measure (Euclid P)) =
      ENNReal.ofReal (c⁻¹ ^ n) • (μHE[n] : Measure (Euclid P)) := by
    ext B hB
    rw [Measure.map_apply hT.measurable hB, Set.preimage_smul₀ hc.ne',
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hc.ne'), Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hc]
  -- Step 3, (i): `T_#(Hⁿ⌞T⁻¹(M)) = (T_#Hⁿ)⌞M = c⁻ⁿ Hⁿ⌞M`.
  have h1 : Measure.map (fun x : Euclid P => c • x) (μHE[n].restrict ((fun x => c • x) ⁻¹' M)) =
      ENNReal.ofReal (c⁻¹ ^ n) • μHE[n].restrict M := by
    rw [← hT.restrict_map, hmap, Measure.restrict_smul]
  refine ⟨h1, fun g => ?_, fun g => ?_⟩
  -- Step 4, (ii): `∫⁻ g ∘ T dν = ∫⁻ g d(T_#ν)` for `ν = Hⁿ⌞T⁻¹(M)`, then (i).
  · have h := hT.lintegral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  -- Step 5, (iii): the same for Bochner integrals, with `(ofReal c⁻ⁿ).toReal = c⁻ⁿ`.
  · have h := hT.integral_map (μ := μHE[n].restrict ((fun x => c • x) ⁻¹' M)) g
    rw [h1, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h
    exact h.symm
/-- **Approximate tangent spaces under dilation** (Simon Ch. 3, 1.4).  For `c > 0` the blow-ups
of `c⁻¹M = {x : cx ∈ M}` at `z` are blow-ups of `M` at `cz`: `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)`, as
`(cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z)`.  Since `cr ↓ 0` as `r ↓ 0`, the limits defining `Q` as the
approximate tangent space of `M` at `cz` give the limits for `c⁻¹M` at `z`. -/
theorem Submission.approx_tangent_space_smul_preimage : ∀ (P n : ℕ) (M : Set (Euclid P)) (c : ℝ) (z : Euclid P) (Q : Submodule ℝ (Euclid P)), 0 < c → HasApproximateTangentSpaceAt n M (c • z) Q → HasApproximateTangentSpaceAt n ((fun x => c • x) ⁻¹' M) z Q := by
  intro P n M c z Q hc hT
  have hc0 : c ≠ 0 := hc.ne'
  -- `η_{cz,cr}(m) = (cr)⁻¹(m − cz) = r⁻¹(c⁻¹m − z) = η_{z,r}(c⁻¹m)`
  have hη : ∀ (r : ℝ) (m : Euclid P), Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) m =
      Poincare.SimonGMT.Chapter03.blowUpMap z r (c⁻¹ • m) := by
    intro r m
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, Poincare.SimonGMT.Chapter03.blowUpMap, mul_inv_rev,
      ← smul_smul, smul_sub c⁻¹, inv_smul_smul₀ hc0]
  -- `η_{z,r}(c⁻¹M) = η_{cz,cr}(M)` for every `r`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap z r '' ((fun x => c • x) ⁻¹' M) =
      Poincare.SimonGMT.Chapter03.blowUpMap (c • z) (c * r) '' M := by
    intro r
    ext y
    constructor
    · rintro ⟨m', hm', rfl⟩
      exact ⟨c • m', hm', by rw [hη, inv_smul_smul₀ hc0]⟩
    · rintro ⟨m, hm, rfl⟩
      refine ⟨c⁻¹ • m, ?_, (hη r m).symm⟩
      show c • c⁻¹ • m ∈ M
      rwa [smul_inv_smul₀ hc0]
  -- `r ↦ cr` tends to `0` within `(0, ∞)`: it is continuous, vanishes at `0` and is positive
  -- for `r > 0`
  have hφ : Tendsto (fun r : ℝ => c * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) := (continuous_const_mul c).tendsto 0
      rw [mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  -- the limit at `cz` along `cr ↓ 0` is the limit at `z` along `r ↓ 0`
  refine ⟨hT.1, fun f => ((hT.2 f).comp hφ).congr fun r => ?_⟩
  rw [Function.comp_apply, hset r]

/-- **Dilating an integer multiplicity triple** (Simon Ch. 6, 3.1 and 2.23).  For `c > 0` and
`T x = c • x`, the triple `(T⁻¹M, θ ∘ T, ξ ∘ T)` is again integer multiplicity in `ℝᴾ`.  By the
change of variables `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M`, null sets, local integrability and
`Hⁿ⌞M`-a.e. statements transfer through the measurable embedding `T`; the maps `c⁻¹ • Fⱼ`
parametrize `T⁻¹M`, and approximate tangent spaces are dilation invariant. -/
theorem Submission.imrep_univ_smul_rescale_exists : ∀ (P n : ℕ) (R : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → ∃ R' : IMRep (univ : Set (Euclid P)) n, R'.carrier = (fun x => c • x) ⁻¹' R.carrier ∧ (∀ x, R'.mult x = R.mult (c • x)) ∧ ∀ x, R'.orient x = R.orient (c • x) := by
  intro P n R c hc
  have hc0 : c ≠ 0 := hc.ne'
  -- `T x = c • x` is a homeomorphism of `ℝᴾ`, hence measurable and a measurable embedding
  have hT : Measurable (fun x : Euclid P => c • x) := measurable_const_smul c
  have hTemb : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    (Homeomorph.smulOfNeZero c hc0).measurableEmbedding
  -- (CV): `T_#(Hⁿ⌞T⁻¹S) = c⁻ⁿ Hⁿ⌞S` and the lower-integral change of variables, for every `S`
  have hCV := Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
  -- (∗) `T_#(Hⁿ⌞T⁻¹M) = c⁻ⁿ Hⁿ⌞M` for `M = R.carrier`
  have hstar := (hCV R.carrier).1
  refine ⟨{ carrier := (fun x : Euclid P => c • x) ⁻¹' R.carrier
            mult := fun x => R.mult (c • x)
            orient := fun x => R.orient (c • x)
            measurableSet_carrier := hT R.measurableSet_carrier
            carrier_subset := subset_univ _
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp hT
            mult_pos := fun x hx => R.mult_pos (c • x) hx
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, rfl, fun _ => rfl, fun _ => rfl⟩
  · -- rectifiability: `T⁻¹M ⊆ T⁻¹M₀ ∪ ⋃ⱼ range (c⁻¹ • Fⱼ)` with `Hⁿ(T⁻¹M₀) = 0`
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨(fun x : Euclid P => c • x) ⁻¹' M₀, ?_, fun j w => c⁻¹ • F j w, fun j => ?_, ?_⟩
    · -- evaluate `T_#(Hⁿ⌞T⁻¹M₀) = c⁻ⁿ Hⁿ⌞M₀` on `univ`
      have h := congrArg (fun μ : Measure (Euclid P) => μ univ) (hCV M₀).1
      simp only at h
      rwa [Measure.map_apply hT MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ,
        Measure.smul_apply, Measure.restrict_apply_univ, hM₀, smul_zero] at h
    · -- `c⁻¹ • Fⱼ` is `‖c⁻¹‖₊ Kⱼ`-Lipschitz
      obtain ⟨K, hK⟩ := hF j
      exact ⟨‖c⁻¹‖₊ * K, (lipschitzWith_smul c⁻¹).comp hK⟩
    · -- if `c • z = Fⱼ w` then `z = c⁻¹ • Fⱼ w`
      intro z hz
      rcases hcover hz with h0 | h1
      · exact Or.inl h0
      · obtain ⟨j, w, hw⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, w, by simp only [hw, inv_smul_smul₀ hc0]⟩)
  · -- local integrability: `T⁻¹M ∩ K = T⁻¹(M ∩ T(K))` with `T(K)` compact
    intro K hK _
    have hTK : IsCompact ((fun x : Euclid P => c • x) '' K) := hK.image (continuous_const_smul c)
    have hset : (fun x : Euclid P => c • x) ⁻¹' R.carrier ∩ K =
        (fun x : Euclid P => c • x) ⁻¹' (R.carrier ∩ (fun x : Euclid P => c • x) '' K) := by
      rw [preimage_inter, hTemb.injective.preimage_image]
    rw [hset, (hCV (R.carrier ∩ (fun x : Euclid P => c • x) '' K)).2.1 fun y => (R.mult y : ℝ≥0∞)]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (R.locallyIntegrable_mult _ hTK (subset_univ _))
  · -- `ξ` is a.e.-strongly measurable for `c⁻ⁿ Hⁿ⌞M = T_#(Hⁿ⌞T⁻¹M)`; compose with `T`
    have h := R.aestronglyMeasurable_orient.smul_measure (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar] at h
    exact h.comp_aemeasurable hT.aemeasurable
  · -- the orientation statement holds `T_#(Hⁿ⌞T⁻¹M)`-a.e., i.e. at `c • z` for a.e. `z ∈ T⁻¹M`;
    -- there `Q` is also the approximate tangent space of `T⁻¹M` at `z`
    have h := Measure.ae_smul_measure R.orients (ENNReal.ofReal (c⁻¹ ^ n))
    rw [← hstar, hTemb.ae_map_iff] at h
    filter_upwards [h] with z ⟨Q, hQ, hξ⟩
    exact ⟨Q, Submission.approx_tangent_space_smul_preimage P n R.carrier c z Q hc hQ, hξ⟩
/-- **A cone takes equal values on dilated test forms** (Simon 7.3.1(2), via 6.2.23).
If `C ∈ 𝒟ₙ(ℝᴾ)` is a cone, `λ > 0` and `ω ∈ 𝒟ⁿ(ℝᴾ)`, then `ω'(y) = λ⁻ⁿ ω(λ⁻¹y)` defines a test
form with `C(ω') = C(ω)`.  As `η_{0,λ}(ℝᴾ) = ℝᴾ`, the cone property `η_{0,λ#}C = C` reads
`C(η_{0,λ}^# ω) = C(ω)`, and by multilinearity
`η_{0,λ}^# ω (y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)`. -/
theorem Submission.cone_current_apply_dilation_pullback : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsConeCurrent C → ∀ lam : ℝ, 0 < lam → ∀ ω : TestFormOn (univ : Set (Euclid P)) n, ∃ ω' : TestFormOn (univ : Set (Euclid P)) n, (∀ y, (ω' : DifferentialForm (Euclid P) n) y = (lam⁻¹ ^ n) • (ω : DifferentialForm (Euclid P) n) (lam⁻¹ • y)) ∧ C ω' = C ω := by
  intro P n C hC lam hlam ω
  -- Step 1: the cone property `η_{0,λ#}C(ω) = C(ω)`.
  have hcone := hC lam hlam ω
  -- Step 2: `η_{0,λ}(ℝᴾ) = ℝᴾ`, so `currentEval` takes its test-form branch.
  have hV : dilation (0 : Euclid P) lam '' univ = univ := by
    refine eq_univ_of_forall fun x => ⟨lam • x, mem_univ _, ?_⟩
    simp [dilation, dilationCLM, smul_smul, mul_inv_cancel₀ hlam.ne']
  have h : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ dilation (0 : Euclid P) lam '' univ :=
    ⟨ω.property.1, by rw [hV]; exact subset_univ _⟩
  rw [currentEval, dite_eq_left h] at hcone
  -- Steps 3–4: unfolding `blowUp`, `η_{0,λ#}C(ω) = C(ω')` for the affine pullback `ω'` of `ω`,
  -- so `C(ω') = C(ω)`.
  refine ⟨_, fun y => ?_, hcone⟩
  -- Step 5: `ω'(y) = ω(λ⁻¹y) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(λ⁻¹y)` by multilinearity.
  ext v
  change (ω : DifferentialForm (Euclid P) n) (-(lam⁻¹ • (0 : Euclid P)) + dilationCLM P lam y)
      (fun i => dilationCLM P lam (v i)) = _
  simp only [dilationCLM, smul_zero, neg_zero, zero_add, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- **Action and weight of a dilated triple** (Simon 6.3.1 (‡) and Ch. 4, 1.1, under
`x ↦ cx`; used for the cone `C` of 7.3.1(2)).  If `c > 0` and `R' = (M', θ', ξ')` is
`R = (M, θ, ξ)` pulled back by `x ↦ cx`, i.e. `M' = {x : cx ∈ M}`, `θ'(x) = θ(cx)` and
`ξ'(x) = ξ(cx)`, then `τ(R')(ω) = τ(R)(ω_c)` with `ω_c(y) = c⁻ⁿ ω(c⁻¹y)` for every `n`-form `ω`,
and `μ_{R'}(A) = c⁻ⁿ μ_R(cA)` for every Borel `A`.  Both follow from the change of variables
`∫_{M'} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ`. -/
theorem Submission.imrep_smul_rescale_action_measure : ∀ (P n : ℕ) (R R' : IMRep (univ : Set (Euclid P)) n) (c : ℝ), 0 < c → R'.carrier = (fun x => c • x) ⁻¹' R.carrier → (∀ x, R'.mult x = R.mult (c • x)) → (∀ x, R'.orient x = R.orient (c • x)) → (∀ ω : DifferentialForm (Euclid P) n, R'.action ω = R.action (fun y => (c⁻¹ ^ n) • ω (c⁻¹ • y))) ∧ ∀ A : Set (Euclid P), MeasurableSet A → R'.measure A = ENNReal.ofReal (c⁻¹ ^ n) * R.measure ((fun x => c • x) '' A) := by
  intro P n R R' c hc hcar hmult horient
  -- `T x = cx` is a measurable embedding with `c⁻¹ (cz) = z`.
  have hT : MeasurableEmbedding (fun x : Euclid P => c • x) :=
    measurableEmbedding_const_smul₀ hc.ne'
  have hinv : ∀ z : Euclid P, c⁻¹ • c • z = z := fun z => by
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  refine ⟨fun ω => ?_, fun A hA => ?_⟩
  · -- Step 1: `R'.action ω = ∫_{T⁻¹M} g(cz) dHⁿ(z) = c⁻ⁿ ∫_M g dHⁿ` for
    -- `g(y) = θ(y) ξ(y)(ω(c⁻¹y))`.
    have hcv := (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      R.carrier).2.2 fun y => (R.mult y : ℝ) * R.orient y (ω (c⁻¹ • y))
    simp only [hinv] at hcv
    unfold IMRep.action
    rw [hcar]
    simp only [hmult, horient]
    -- Step 2: move `c⁻ⁿ` inside the integral and use the linearity of `ξ(y)`.
    rw [hcv, ← integral_const_mul]
    congr 1
    funext y
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    ring
  · -- Step 3: `R'.measure A = ∫⁻_{A ∩ M'} θ(c·) dHⁿ`, and `A ∩ M' = T⁻¹(cA ∩ M)`.
    have hTA : MeasurableSet ((fun x : Euclid P => c • x) '' A) := hT.measurableSet_image.2 hA
    have hset : A ∩ R'.carrier =
        (fun x : Euclid P => c • x) ⁻¹' ((fun x : Euclid P => c • x) '' A ∩ R.carrier) := by
      rw [preimage_inter, preimage_image_eq _ hT.injective, hcar]
    unfold IMRep.measure
    rw [withDensity_apply _ hA, withDensity_apply _ hTA, Measure.restrict_restrict hA,
      Measure.restrict_restrict hTA, hset]
    simp only [hmult]
    -- Step 4: the lower-integral change of variables on `cA ∩ M`.
    exact (Submission.euclid_hausdorff_dilation_change_of_variables P n c hc
      ((fun x : Euclid P => c • x) '' A ∩ R.carrier)).2.1 fun y => (R.mult y : ℝ≥0∞)
/-- A unit orientation has norm at most `1` (step 1(c) of the proof of Simon Ch. 6, 3.2(3)).
If `ξ α = ±α(τ₁, …, τₙ)` for an orthonormal family `τ`, then `|ξ α| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
for every `n`-covector `α`, so the operator norm of `ξ` is at most `1`. -/
theorem Submission.unit_orientation_norm_le_one : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ : MultiVector P n), IsUnitOrientationOf ξ Q → ‖ξ‖ ≤ 1 := by
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
/-- **Simon Ch. 6, 3.2(3)** (independence of `θHⁿ⌞M` from the representation, steps 1(b), 1(d)):
two unit orientations `ξ₁ = ±τ₁ ∧ ⋯ ∧ τₙ`, `ξ₂ = ±τ'₁ ∧ ⋯ ∧ τ'ₙ` of the same subspace `Q` take
absolute value `1` on a common `n`-covector.  Take the frame determinant
`δ(w) = det(⟨τᵢ, wⱼ⟩) = det_τ (π_Q w)`, continuous since `|δ(w)| ≤ ∏ ‖wⱼ‖` (Hadamard); then
`δ(τ) = 1` and `δ(τ') = det(⟨τᵢ, τ'ⱼ⟩) = ±1`, the change of orthonormal basis being orthogonal. -/
theorem Submission.unit_orientations_common_unit_covector : ∀ (P n : ℕ) (Q : Submodule ℝ (Euclid P)) (ξ₁ ξ₂ : MultiVector P n), IsUnitOrientationOf ξ₁ Q → IsUnitOrientationOf ξ₂ Q → ∃ α : Covector (Euclid P) n, |ξ₁ α| = 1 ∧ |ξ₂ α| = 1 := by
  rintro P n Q ξ₁ ξ₂ ⟨τ, hτ, hspan, hξ₁⟩ ⟨τ', hτ', hspan', hξ₂⟩
  -- an orthonormal frame spanning `Q` is an orthonormal basis of `Q`
  have frame : ∀ σ : Fin n → Euclid P, Orthonormal ℝ σ → Submodule.span ℝ (range σ) = Q →
      ∃ c : OrthonormalBasis (Fin n) ℝ Q, ∀ i, (c i : Euclid P) = σ i := by
    intro σ hσ hσspan
    have hmem : ∀ i, σ i ∈ Q := fun i => hσspan ▸ Submodule.subset_span (mem_range_self i)
    let w : Fin n → Q := fun i => ⟨σ i, hmem i⟩
    have hw : Orthonormal ℝ w := by
      rw [← Q.subtypeₗᵢ.orthonormal_comp_iff (v := w)]
      exact hσ
    have hwspan : ⊤ ≤ Submodule.span ℝ (range w) := by
      rintro ⟨y, hy⟩ -
      rw [← hσspan, Submodule.mem_span_range_iff_exists_fun] at hy
      obtain ⟨c, hc⟩ := hy
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, Subtype.ext (by simpa [w] using hc)⟩
    exact ⟨OrthonormalBasis.mk hw hwspan, fun i => by simp [w]⟩
  obtain ⟨b, hb⟩ := frame τ hτ hspan
  obtain ⟨b', hb'⟩ := frame τ' hτ' hspan'
  have : Fact (Module.finrank ℝ Q = n) := ⟨by simpa using Module.finrank_eq_card_basis b.toBasis⟩
  let o : Orientation ℝ Q (Fin n) := b.toBasis.orientation
  let π : Euclid P →L[ℝ] Q := Q.orthogonalProjectionOnto
  -- the frame determinant `δ(w) = det_b (π_Q w)`
  let A : Euclid P [⋀^Fin n]→ₗ[ℝ] ℝ := b.toBasis.det.compLinearMap π.toLinearMap
  have hA : ∀ w, ‖A w‖ ≤ 1 * ∏ i, ‖w i‖ := by
    intro w
    have h1 : |A w| = |o.volumeForm (fun i => π (w i))| :=
      (o.volumeForm_robust' b (fun i => π (w i))).symm
    rw [Real.norm_eq_abs, h1, one_mul]
    refine (o.abs_volumeForm_apply_le _).trans ?_
    gcongr with i
    exact Q.norm_orthogonalProjectionOnto_apply_le (w i)
  let δ : Covector (Euclid P) n := A.mkContinuous 1 hA
  have hπ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (i : Fin n), π (c i : Euclid P) = c i :=
    fun c i => Q.orthogonalProjectionOnto_mem_subspace_eq_self (c i)
  -- `|δ| = 1` on every orthonormal frame of `Q`
  have hδ : ∀ (c : OrthonormalBasis (Fin n) ℝ Q) (σ : Fin n → Euclid P),
      (∀ i, (c i : Euclid P) = σ i) → |δ σ| = 1 := by
    intro c σ hc
    have h2 : δ σ = b.toBasis.det (fun i => π (σ i)) := rfl
    have h3 : (fun i => π (σ i)) = c := by
      funext i
      rw [← hc i, hπ]
    rw [h2, h3, ← o.volumeForm_robust' b]
    exact o.abs_volumeForm_apply_of_orthonormal c
  refine ⟨δ, ?_, ?_⟩
  · rcases hξ₁ with h | h
    · rw [h]
      exact hδ b τ hb
    · rw [h, abs_neg]
      exact hδ b τ hb
  · rcases hξ₂ with h | h
    · rw [h]
      exact hδ b' τ' hb'
    · rw [h, abs_neg]
      exact hδ b' τ' hb'
/-- **Simon Ch. 3, 1.4** (used in Ch. 6, 3.2(3)): approximate tangent spaces only see a set up to
`Hⁿ`-null sets.  For `r ≠ 0` the blow-up `η_{x,r}(y) = r⁻¹(y - x)` is a translation followed by a
dilation, so it maps `Hⁿ`-null sets to `Hⁿ`-null sets.  As `η(A) \ η(B) ⊆ η(A \ B)` and
`η(B) \ η(A) ⊆ η(B \ A)`, the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, so their
integrals coincide for every `r > 0` and have the same limits as `r ↓ 0`. -/
theorem Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (Q : Submodule ℝ (Euclid P)), μHE[n] (A \ B) = 0 → μHE[n] (B \ A) = 0 → (HasApproximateTangentSpaceAt n A x Q ↔ HasApproximateTangentSpaceAt n B x Q) := by
  intro P n A B x Q hAB hBA
  -- `η_{x,r} = (r⁻¹ • ·) ∘ (· - x)` maps `Hⁿ`-null sets to `Hⁿ`-null sets when `r ≠ 0`
  have himg_null : ∀ r : ℝ, r ≠ 0 → ∀ S : Set (Euclid P), μHE[n] S = 0 →
      μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = 0 := by
    intro r hr S hS
    have himg : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
        (fun z => r⁻¹ • z) '' ((fun y => y - x) '' S) := by
      rw [Set.image_image]
      rfl
    have hiso : Isometry (fun y : Euclid P => y - x) := (IsometryEquiv.subRight x).isometry
    rw [himg, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr),
      hiso.euclideanHausdorffMeasure_image, hS, smul_zero]
  -- for `r ≠ 0` the blow-ups of `A` and `B` agree up to `Hⁿ`-null sets, hence so do the integrals
  have hint : ∀ r : ℝ, r ≠ 0 → ∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ,
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n] =
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] := by
    intro r hr f
    apply setIntegral_congr_set
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hAB)
    · exact measure_mono_null (Set.subset_image_sdiff _ _ _) (himg_null r hr _ hBA)
  -- the integrals agree on `(0, ∞) ∈ 𝓝[>] 0`, so they have the same limits as `r ↓ 0`
  constructor
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hint r (ne_of_gt hr) f
  · rintro ⟨hdim, hlim⟩
    refine ⟨hdim, fun f => (hlim f).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hint r (ne_of_gt hr) f).symm

/-- Two integer multiplicity representations of one current have `Hⁿ⌞(M₁ ∪ M₂)`-a.e. equal
vector densities `1_{M₁} θ₁ ξ₁ = 1_{M₂} θ₂ ξ₂` (step 2 of the proof of Simon Ch. 6, 3.2(3)).
With `Fₖ = 1_{Mₖ} θₖ ξₖ` and `ν = Hⁿ⌞(M₁ ∪ M₂)`, `‖Fₖ‖ ≤ 1_{Mₖ} θₖ` makes `F₁ − F₂` locally
`ν`-integrable on `U`; testing `T` on the forms `g α` (`g` smooth with compact support in `U`, `α`
an `n`-covector) gives `(∫ g (F₁ − F₂) dν) α = T(g α) − T(g α) = 0`, so the fundamental lemma of
the calculus of variations on the open set `U ⊇ M₁ ∪ M₂` gives `F₁ = F₂` `ν`-a.e. -/
theorem Submission.imrep_weighted_orient_indicator_ae_eq : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → ∀ᵐ x ∂(μHE[n].restrict (R₁.carrier ∪ R₂.carrier)), R₁.carrier.indicator (fun y => (R₁.mult y : ℝ) • R₁.orient y) x = R₂.carrier.indicator (fun y => (R₂.mult y : ℝ) • R₂.orient y) x := by
  intro P n U T R₁ R₂ hU h₁ h₂
  set ν := μHE[n].restrict (R₁.carrier ∪ R₂.carrier) with hν
  have hνle : ν ≤ μHE[n] := Measure.restrict_le_self
  let F : IMRep U n → Euclid P → MultiVector P n := fun R =>
    R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y)
  let θ : IMRep U n → Euclid P → ℝ := fun R => R.carrier.indicator (fun y => (R.mult y : ℝ))
  have hFmeas : ∀ R : IMRep U n, AEStronglyMeasurable (F R) μHE[n] := by
    intro R
    refine (aestronglyMeasurable_indicator_iff R.measurableSet_carrier).2 ?_
    have hm : AEStronglyMeasurable (fun y => (R.mult y : ℝ)) (μHE[n].restrict R.carrier) :=
      (measurable_from_nat.comp R.measurable_mult).aestronglyMeasurable
    exact hm.smul R.aestronglyMeasurable_orient
  have hθnn : ∀ R : IMRep U n, ∀ x, 0 ≤ θ R x := fun R x => by
    simp only [θ]; exact indicator_nonneg (fun y _ => Nat.cast_nonneg _) x
  -- `‖F R‖ ≤ θ R` a.e., as `‖ξ‖ ≤ 1` for a unit orientation `ξ`
  have hFbound : ∀ R : IMRep U n, ∀ᵐ x ∂μHE[n], ‖F R x‖ ≤ θ R x := by
    intro R
    have hor := R.orients
    rw [ae_restrict_iff' R.measurableSet_carrier] at hor
    filter_upwards [hor] with x hx
    by_cases hmem : x ∈ R.carrier
    · obtain ⟨Q, -, hQ⟩ := hx hmem
      have h1 := Submission.unit_orientation_norm_le_one P n Q _ hQ
      simp only [F, θ, indicator_of_mem hmem]
      calc ‖(R.mult x : ℝ) • R.orient x‖ ≤ ‖(R.mult x : ℝ)‖ * ‖R.orient x‖ :=
            ContinuousLinearMap.opNorm_smul_le _ _
        _ ≤ (R.mult x : ℝ) * 1 := by rw [Real.norm_natCast]; gcongr
        _ = R.mult x := mul_one _
    · simp only [F, θ, indicator_of_notMem hmem]
      exact ContinuousLinearMap.opNorm_zero.le
  -- `θ R` is integrable on compact subsets of `U`
  have hθint : ∀ R : IMRep U n, ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      IntegrableOn (θ R) K μHE[n] := by
    intro R K hK hKU
    refine ⟨((measurable_from_nat.comp R.measurable_mult).indicator
      R.measurableSet_carrier).aestronglyMeasurable, ?_⟩
    have hfin := R.locallyIntegrable_mult K hK hKU
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (hθnn R))]
    have : ∀ x, ENNReal.ofReal (θ R x) = R.carrier.indicator (fun y => (R.mult y : ℝ≥0∞)) x := by
      intro x
      by_cases hmem : x ∈ R.carrier
      · simp [θ, indicator_of_mem hmem]
      · simp [θ, indicator_of_notMem hmem]
    simp_rw [this]
    rw [lintegral_indicator R.measurableSet_carrier,
      Measure.restrict_restrict R.measurableSet_carrier]
    exact lt_top_iff_ne_top.2 hfin
  have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (F := MultiVector P n) (μ := ν)
    (f := fun x => F R₁ x - F R₂ x) ?hloc ?hmom
  · filter_upwards [key, ae_restrict_mem (R₁.measurableSet_carrier.union R₂.measurableSet_carrier)]
      with x hx hmem
    have hxU : x ∈ U := hmem.elim (fun h => R₁.carrier_subset h) (fun h => R₂.carrier_subset h)
    exact sub_eq_zero.1 (hx hxU)
  case hloc =>
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
    have hK : IsCompact (closedBall x (r / 2)) := isCompact_closedBall x (r / 2)
    have hKU : closedBall x (r / 2) ⊆ U :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    refine ⟨closedBall x (r / 2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)), ?_⟩
    refine Integrable.mono' (g := fun y => θ R₁ y + θ R₂ y) ?_ ?_ ?_
    · exact ((hθint R₁ _ hK hKU).add (hθint R₂ _ hK hKU)).mono_measure hνle
    · exact (((hFmeas R₁).sub (hFmeas R₂)).mono_measure hνle).restrict
    · filter_upwards [ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₁)),
        ae_restrict_of_ae (hνle.absolutelyContinuous (hFbound R₂))] with y hy1 hy2
      calc ‖F R₁ y - F R₂ y‖ ≤ ‖F R₁ y‖ + ‖F R₂ y‖ := norm_sub_le (F R₁ y) (F R₂ y)
        _ ≤ θ R₁ y + θ R₂ y := add_le_add hy1 hy2
  case hmom =>
    intro g hg hgc hgU
    have hK : IsCompact (tsupport g) := hgc
    obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    -- the test forms `g α`
    have hgα : ∀ α : Covector (Euclid P) n,
        (fun x => g x • α) ∈ testFormOnSubmodule (E := Euclid P) U n := by
      intro α
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact hg.smul contDiff_const
      · exact hgc.smul_right
      · exact (tsupport_smul_subset_left g (fun _ => α)).trans hgU
    have hθK : ∀ R : IMRep U n, Integrable ((tsupport g).indicator (θ R)) ν := fun R =>
      ((hθint R _ hK hgU).integrable_indicator (isClosed_tsupport g).measurableSet).mono_measure
        hνle
    -- `∫ g (F R) α dν = R.action (g α) = T (g α)`
    have hscal : ∀ R : IMRep U n, R.Represents T → R.carrier ⊆ R₁.carrier ∪ R₂.carrier →
        ∀ α : Covector (Euclid P) n,
          ∫ x, g x * F R x α ∂ν = T ⟨fun x => g x • α, hgα α⟩ := by
      intro R hR hsub α
      rw [hR ⟨fun x => g x • α, hgα α⟩]
      have hpt : ∀ x, g x * F R x α =
          R.carrier.indicator (fun y => (R.mult y : ℝ) * R.orient y (g y • α)) x := by
        intro x
        by_cases hmem : x ∈ R.carrier
        · simp only [F, indicator_of_mem hmem, smul_apply, smul_eq_mul, map_smul]
          ring
        · simp [F, indicator_of_notMem hmem]
      simp_rw [hpt]
      rw [integral_indicator R.measurableSet_carrier, hν,
        Measure.restrict_restrict R.measurableSet_carrier, inter_eq_left.2 hsub]
      rfl
    have hscalint : ∀ R : IMRep U n, ∀ α : Covector (Euclid P) n,
        Integrable (fun x => g x * F R x α) ν := by
      intro R α
      refine Integrable.mono' ((hθK R).const_mul (C * ‖α‖)) ?_ ?_
      · have hev : Continuous fun L : MultiVector P n => L α :=
          (ContinuousLinearMap.apply ℝ ℝ α).continuous
        exact (hg.continuous.aestronglyMeasurable.mul
          (hev.comp_aestronglyMeasurable (hFmeas R))).mono_measure hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R)] with x hx
        by_cases hx' : x ∈ tsupport g
        · rw [indicator_of_mem hx', norm_mul]
          have h1 : ‖F R x α‖ ≤ ‖F R x‖ * ‖α‖ := (F R x).le_opNorm α
          calc ‖g x‖ * ‖F R x α‖ ≤ C * (θ R x * ‖α‖) := by
                gcongr
                · exact hC x
                · exact h1.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            _ = C * ‖α‖ * θ R x := by ring
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_mul, norm_zero, indicator_of_notMem hx',
            mul_zero]
    refine ContinuousLinearMap.ext fun α => ?_
    rw [ContinuousLinearMap.integral_apply ?hint α]
    case hint =>
      refine Integrable.mono' ((hθK R₁).add (hθK R₂) |>.const_mul C) ?_ ?_
      · exact (hg.continuous.aestronglyMeasurable.smul ((hFmeas R₁).sub (hFmeas R₂))).mono_measure
          hνle
      · filter_upwards [hνle.absolutelyContinuous (hFbound R₁),
          hνle.absolutelyContinuous (hFbound R₂)] with x hx1 hx2
        by_cases hx' : x ∈ tsupport g
        · rw [Pi.add_apply, indicator_of_mem hx', indicator_of_mem hx']
          calc ‖g x • (F R₁ x - F R₂ x)‖ ≤ ‖g x‖ * ‖F R₁ x - F R₂ x‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ C * (θ R₁ x + θ R₂ x) := by
                gcongr
                · exact hC x
                · exact (norm_sub_le (F R₁ x) (F R₂ x)).trans (add_le_add hx1 hx2)
        · rw [image_eq_zero_of_notMem_tsupport hx', zero_smul, Pi.add_apply,
            indicator_of_notMem hx', indicator_of_notMem hx']
          simp
    have hsplit : ∀ x, (g x • (F R₁ x - F R₂ x)) α = g x * F R₁ x α - g x * F R₂ x α := by
      intro x
      simp only [smul_apply, sub_apply, smul_eq_mul, mul_sub]
    simp_rw [hsplit]
    rw [integral_sub (hscalint R₁ α) (hscalint R₂ α), hscal R₁ h₁ subset_union_left α,
      hscal R₂ h₂ subset_union_right α, sub_self]
    rfl

/-- **Simon Ch. 6, 3.2(3)** (chapter-06.txt lines 763–768): the weight `θHⁿ⌞M` of an integer
multiplicity current does not depend on the representation `T = τ(M, θ, ξ)`.  By the fundamental
lemma, `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂` `Hⁿ`-a.e. on `M₁ ∪ M₂`.  A unit orientation is nonzero, so
`Hⁿ(M₁ ∖ M₂) = Hⁿ(M₂ ∖ M₁) = 0`; then `M₁`, `M₂` have the same approximate tangent planes, and
evaluating at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂` a.e. on `M₁ ∩ M₂`. -/
theorem Submission.imrep_measure_eq_of_represents_same_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R₁ R₂ : IMRep U n), IsOpen U → R₁.Represents T → R₂.Represents T → R₁.measure = R₂.measure := by
  intro P n U T R₁ R₂ hU h₁ h₂
  -- (★) `1_{M₁}θ₁ξ₁ = 1_{M₂}θ₂ξ₂`, `Hⁿ`-a.e. on `M₁ ∪ M₂`
  have hstar := Submission.imrep_weighted_orient_indicator_ae_eq P n U T R₁ R₂ hU h₁ h₂
  -- `Hⁿ(M ∖ M') = 0`: for a.e. `x ∈ M ∖ M'`, (★) reads `θ(x)ξ(x) = 0`, but `θ(x) ≥ 1` and
  -- `|ξ(x)(α)| = 1` for some `α` (the common covector of `ξ(x)` with itself)
  have hnull : ∀ R R' : IMRep U n,
      (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∪ R'.carrier)),
        R.carrier.indicator (fun y => (R.mult y : ℝ) • R.orient y) x =
          R'.carrier.indicator (fun y => (R'.mult y : ℝ) • R'.orient y) x) →
      μHE[n] (R.carrier \ R'.carrier) = 0 := by
    intro R R' h
    have hmem : ∀ᵐ x ∂(μHE[n].restrict R.carrier), x ∈ R'.carrier := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left h, R.orients,
        ae_restrict_mem R.measurableSet_carrier] with x hx hxo hxM
      by_contra hxM'
      obtain ⟨Q, -, hQ⟩ := hxo
      obtain ⟨α, hα, -⟩ :=
        Submission.unit_orientations_common_unit_covector P n Q (R.orient x) (R.orient x) hQ hQ
      rw [indicator_of_mem hxM, indicator_of_notMem hxM'] at hx
      have hev := congrArg (fun L : MultiVector P n => |L α|) hx
      simp only [smul_apply, zero_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα, mul_one,
        abs_zero, Nat.cast_eq_zero] at hev
      exact (R.mult_pos x hxM).ne' hev
    rw [ae_restrict_iff' R.measurableSet_carrier, ae_iff] at hmem
    have hsub : R.carrier \ R'.carrier ⊆ {x | ¬(x ∈ R.carrier → x ∈ R'.carrier)} :=
      fun x hx h => hx.2 (h hx.1)
    exact measure_mono_null hsub hmem
  have h12 := hnull R₁ R₂ hstar
  have h21 := hnull R₂ R₁ (by
    rw [union_comm]
    filter_upwards [hstar] with x hx using hx.symm)
  -- hence `Hⁿ⌞M₁ = Hⁿ⌞M₂`
  have hrestr : μHE[n].restrict R₁.carrier = μHE[n].restrict R₂.carrier :=
    Measure.restrict_congr_set (ae_eq_set.2 ⟨h12, h21⟩)
  -- `θ₁ = θ₂` a.e. on `M₁`: the approximate tangent planes `Q₁` of `M₁` and `Q₂` of `M₂` agree,
  -- and (★) evaluated at a covector `α` with `|ξ₁(α)| = |ξ₂(α)| = 1` gives `θ₁ = θ₂`
  have hmult : ∀ᵐ x ∂(μHE[n].restrict R₁.carrier), (R₁.mult x : ℝ≥0∞) = R₂.mult x := by
    have hor₂ := R₂.orients
    have hmem₂ := ae_restrict_mem (μ := μHE[n]) R₂.measurableSet_carrier
    rw [← hrestr] at hor₂ hmem₂
    filter_upwards [ae_restrict_of_ae_restrict_of_subset subset_union_left hstar, R₁.orients, hor₂,
      ae_restrict_mem R₁.measurableSet_carrier, hmem₂] with x hx ho₁ ho₂ hx₁ hx₂
    obtain ⟨Q₁, hT₁, hQ₁⟩ := ho₁
    obtain ⟨Q₂, hT₂, hQ₂⟩ := ho₂
    have hQ : Q₁ = Q₂ :=
      ((Submission.hasApproximateTangentSpaceAt_iff_of_null_sdiff P n R₁.carrier R₂.carrier x Q₁
        h12 h21).1 hT₁).unique hT₂
    subst hQ
    obtain ⟨α, hα₁, hα₂⟩ :=
      Submission.unit_orientations_common_unit_covector P n Q₁ (R₁.orient x) (R₂.orient x) hQ₁ hQ₂
    rw [indicator_of_mem hx₁, indicator_of_mem hx₂] at hx
    have hev := congrArg (fun L : MultiVector P n => |L α|) hx
    simp only [smul_apply, smul_eq_mul, abs_mul, Nat.abs_cast, hα₁, hα₂, mul_one] at hev
    exact_mod_cast hev
  -- `θ₁Hⁿ⌞M₁ = θ₂Hⁿ⌞M₁ = θ₂Hⁿ⌞M₂`
  unfold IMRep.measure
  rw [withDensity_congr_ae hmult, hrestr]

/-- **Simon Ch. 6, 2.4–2.8 and 3.2(3)**: if `T = τ(M, θ, ξ)` in the open set `U` and
`μ_R = θHⁿ⌞M`, then (a) `M_W(T) = μ_R(W)` for every open `W ⊆ U`, (b) a point `x ∈ U` lies in
`spt T` iff every ball `B_ε(x)` has positive `μ_R`-measure, and (c) `μ_R` does not depend on the
representation.  (a) combines the upper and lower bounds `M_W(T) ≤ μ_R(W) ≤ M_W(T)`; by (a),
`spt T = U ∩ spt μ_R`, and the balls about `x` form a neighbourhood basis, which gives (b). -/
theorem Submission.dimred_im_mass_measure : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure := by
  intro P n U T R hU hR
  -- (a) `M_W(T) = μ_R(W)` for every open `W`, not only for `W ⊆ U`
  have hmass : ∀ W : Set (Euclid P), IsOpen W → T.massOn W = R.measure W := fun W hW =>
    le_antisymm (Submission.dor_ims_massOn_le_measure P n U T R hR W)
      (Submission.dor_ims_measure_le_massOn P n U T R hU hR W hW)
  refine ⟨fun W hW _ => hmass W hW, fun x hxU => ?_, fun R' hR' =>
    Submission.imrep_measure_eq_of_represents_same_current P n U T R' R hU hR' hR⟩
  -- (b) `spt T = U ∩ spt μ_R`, and `x ∈ spt μ_R` iff `μ_R(B_ε(x)) > 0` for every `ε > 0`
  rw [Submission.dor_ims_support_of_massOn_eq P n U T R.measure hU hmass, mem_inter_iff,
    and_iff_right hxU, Metric.nhds_basis_ball.mem_measureSupport]
  exact forall₂_congr fun ε _ => pos_iff_ne_zero
/-- **Test forms and the blow-up under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`** (Simon
Ch. 3, 1.4, chapter-03.txt line 85; push-forward 6.2.23, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337).  `η = η_{x,λ}` is an affine
homeomorphism of `ℝᴾ` with inverse `ι(z) = x + λz`, and `η⁻¹(η(U)) = U`.  (a) `ω ↦ ω ∘ η` maps
`𝒟ⁿ(η(U))` to `𝒟ⁿ(U)`; (b) `ω' ↦ ω' ∘ ι` maps `𝒟ⁿ(U)` to `𝒟ⁿ(η(U))`, and `(ω' ∘ ι) ∘ η = ω'`;
(c) if `ω' = ω ∘ η` then `η_{x,λ#}T(ω) = T(η^#ω) = λ⁻ⁿ T(ω')`, since by multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`. -/
theorem Submission.dtc_blowUp_testForm_corr : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ ω : TestFormOn (dilation x lam '' U) n, ∃ ω' : TestFormOn U n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ (∀ ω' : TestFormOn U n, ∃ ω : TestFormOn (dilation x lam '' U) n, ∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧ ∀ (T : GeometricCurrentOn U n) (ω : TestFormOn (dilation x lam '' U) n) (ω' : TestFormOn U n), (∀ y : Euclid P, (ω' : DifferentialForm (Euclid P) n) y = (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) → blowUp T x lam hlam.ne' ω = lam⁻¹ ^ n * T ω' := by
  intro P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- Step 1: `η = η_{x,λ}` (`y ↦ −λ⁻¹x + λ⁻¹y`) and `ι(z) = x + λz` are mutually inverse affine
  -- homeomorphisms, both `C^∞`.  (`∞` is `ℝ≥0∞`'s top under `open scoped ENNReal`.)
  let η : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hne)).trans
    (Homeomorph.addLeft (-(lam⁻¹ • x)))
  have hη : ⇑η = dilation x lam := by
    funext y
    simp [η, dilation, dilationCLM]
  let ι : Euclid P ≃ₜ Euclid P := (Homeomorph.smulOfNeZero lam hne).trans (Homeomorph.addLeft x)
  have hι : ⇑ι = fun z => x + lam • z := by
    funext z
    simp [ι]
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dilation x lam) :=
    contDiff_const.add (dilationCLM P lam).contDiff
  have hιsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Euclid P => x + lam • z) :=
    contDiff_const.add (contDiff_id.const_smul lam)
  refine ⟨?_, ?_, ?_⟩
  · -- (a) `ω' := ω ∘ η`: smooth, compactly supported (`η` a homeomorphism), and
    -- `tsupport ω' ⊆ η⁻¹(tsupport ω) ⊆ η⁻¹(η(U)) = U`.
    intro ω
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω.property
    refine ⟨⟨fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y), ?_⟩, fun y => rfl⟩
    change IsTestForm (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ∧
      tsupport (fun y => (ω : DifferentialForm (Euclid P) n) (dilation x lam y)) ⊆ U
    refine ⟨⟨hsmooth.comp hηsmooth, ?_⟩, ?_⟩
    · have h := hcompact.comp_homeomorph η
      rwa [hη] at h
    · refine (tsupport_comp_subset_preimage (ω : DifferentialForm (Euclid P) n)
        (hη ▸ η.continuous)).trans ((preimage_mono hsupp).trans ?_)
      rw [preimage_image_eq U (hη ▸ η.injective)]
  · -- (b) `ω := ω' ∘ ι`: a test form with `tsupport ω ⊆ ι⁻¹(U) ⊆ η(U)`, and `ω ∘ η = ω'`.
    intro ω'
    obtain ⟨⟨hsmooth, hcompact⟩, hsupp⟩ := ω'.property
    refine ⟨⟨fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z), ?_⟩, fun y => ?_⟩
    · change IsTestForm (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ∧
        tsupport (fun z => (ω' : DifferentialForm (Euclid P) n) (x + lam • z)) ⊆ dilation x lam '' U
      refine ⟨⟨hsmooth.comp hιsmooth, ?_⟩, ?_⟩
      · have h := hcompact.comp_homeomorph ι
        rwa [hι] at h
      · refine (tsupport_comp_subset_preimage (ω' : DifferentialForm (Euclid P) n)
          (hι ▸ ι.continuous)).trans fun z hz => ?_
        exact ⟨x + lam • z, hsupp hz, hηι z⟩
    · change (ω' : DifferentialForm (Euclid P) n) y =
        (ω' : DifferentialForm (Euclid P) n) (x + lam • dilation x lam y)
      rw [hιη]
  · -- (c) `η_{x,λ#}T(ω) = T(η^#ω)`, and `η^#ω = λ⁻ⁿ ω'` by multilinearity; `T` is linear.
    intro T ω ω' hω
    unfold blowUp
    rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
      show lam⁻¹ ^ n * T ω' = T (lam⁻¹ ^ n • ω') by rw [map_smul, smul_eq_mul]]
    congr 1
    apply Subtype.ext
    funext y
    ext v
    rw [testFormOnInclusion_coe, affinePullbackTestOn_coe]
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, show -(lam⁻¹ • x) + dilationCLM P lam y = dilation x lam y from rfl, ← hω y]
    simp
/-- **`Hⁿ` under the dilation `η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`**: the scaling behind (1) in the
proof of Simon 7.3.1 (chapter-07.txt lines 329–335).  (i) `Hⁿ(η_{x,λ}(s)) = λ⁻ⁿ Hⁿ(s)` for every
`s ⊆ ℝᴾ`: `η_{x,λ}(s)` is the translate by `−λ⁻¹x` of `λ⁻¹s`, `Hⁿ` is invariant under isometries
and `Hⁿ(r s) = |r|ⁿ Hⁿ(s)` for `r ≠ 0`.  (ii) `η_{x,λ#}Hⁿ = λⁿ Hⁿ`: `η_{x,λ}⁻¹(B) = η_{−λ⁻¹x,λ⁻¹}(B)`
for every Borel `B`, so (i) for the inverse dilation gives `Hⁿ(η_{x,λ}⁻¹(B)) = λⁿ Hⁿ(B)`. -/
theorem Submission.dtc_hausdorff_dilation : ∀ (P n : ℕ) (x : Euclid P) (lam : ℝ), 0 < lam → (∀ s : Set (Euclid P), μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s) ∧ Measure.map (dilation x lam) (μHE[n] : Measure (Euclid P)) = ENNReal.ofReal (lam ^ n) • (μHE[n] : Measure (Euclid P)) := by
  intro P n
  -- (i) for every centre and scale: `η_{x,λ}(s) = −λ⁻¹x + λ⁻¹s`; translation invariance and
  -- `Hⁿ(rs) = ‖r‖ⁿ Hⁿ(s)` with `r = λ⁻¹ > 0`.
  have himage : ∀ (x : Euclid P) (lam : ℝ), 0 < lam → ∀ s : Set (Euclid P),
      μHE[n] (dilation x lam '' s) = ENNReal.ofReal (lam⁻¹ ^ n) * μHE[n] s := by
    intro x lam hlam s
    have hs : dilation x lam '' s =
        (fun z => -(lam⁻¹ • x) + z) '' ((fun y => lam⁻¹ • y) '' s) := by
      rw [Set.image_image]
      rfl
    rw [hs, (isometry_add_left (-(lam⁻¹ • x))).euclideanHausdorffMeasure_image, Set.image_smul,
      Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hlam.ne') s, ENNReal.smul_def,
      smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
    congr 2
    simp [abs_of_pos hlam]
  intro x lam hlam
  refine ⟨himage x lam hlam, ?_⟩
  -- (ii): `η_{x,λ}` is continuous with inverse `η_{−λ⁻¹x,λ⁻¹}(z) = x + λz`, so
  -- `(η_{x,λ#}Hⁿ)(B) = Hⁿ(η_{−λ⁻¹x,λ⁻¹}(B)) = λⁿ Hⁿ(B)` by (i) for every Borel `B`.
  have hcont : Continuous (dilation x lam) := by
    unfold dilation
    fun_prop
  ext B hB
  have hpre : dilation x lam ⁻¹' B = dilation (-(lam⁻¹ • x)) lam⁻¹ '' B :=
    (congrFun (Set.image_eq_preimage_of_inverse
      (fun z => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])
      (fun y => by simp [dilation, dilationCLM, smul_add, smul_smul, hlam.ne'])) B).symm
  rw [Measure.map_apply hcont.measurable hB, hpre, himage _ _ (inv_pos.mpr hlam), inv_inv,
    Measure.smul_apply, smul_eq_mul]
/-- Approximate tangent spaces are invariant under the dilation `η = η_{x,λ}`, `λ > 0`
(Simon Ch. 3, 1.4).  As `η(w) − η(y) = λ⁻¹(w − y)`, the rescaled set `η_{η(y),r}(η(M))` is
`η_{y,λr}(M)`, and `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`; `dim Q = n` is unchanged. -/
theorem Submission.dtc_approxTangent_dilation : ∀ (P n : ℕ) (M : Set (Euclid P)) (x y : Euclid P) (lam : ℝ) (Q : Submodule ℝ (Euclid P)), 0 < lam → HasApproximateTangentSpaceAt n M y Q → HasApproximateTangentSpaceAt n (dilation x lam '' M) (dilation x lam y) Q := by
  intro P n M x y lam Q hlam hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `η_{η(y),r}(η(M)) = η_{y,λr}(M)`, since `η(w) − η(y) = λ⁻¹(w − y)`
  have hset : ∀ r : ℝ, Poincare.SimonGMT.Chapter03.blowUpMap (dilation x lam y) r ''
      (dilation x lam '' M) = Poincare.SimonGMT.Chapter03.blowUpMap y (lam * r) '' M := by
    intro r
    rw [image_image]
    congr 1
    funext w
    simp only [Poincare.SimonGMT.Chapter03.blowUpMap, dilation, dilationCLM,
      smul_apply, ContinuousLinearMap.id_apply, add_sub_add_left_eq_sub]
    rw [← smul_sub, smul_smul, mul_inv, mul_comm]
  simp_rw [hset]
  -- `r ↦ λr` maps `r ↓ 0` into `s ↓ 0`
  have hlim : Tendsto (fun r : ℝ => lam * r) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (tendsto_id.const_mul lam).mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hlam hr
  exact (hT.2 f).comp hlim

/-- **Simon Ch. 6, 3.3–3.9 for the similarity `η = η_{x,λ}`** (used in the proof of 7.3.1(2)):
if `R = (M, θ, ξ)` represents `T` in `U`, then `R' = (η(M), θ ∘ η⁻¹, ξ ∘ η⁻¹)` represents
`η_{x,λ#}T` in `η(U)` and `μ_{R'}(B) = λ⁻ⁿ μ_R(η⁻¹(B))` for Borel `B`.  The Jacobian of `η` is
the constant `λ⁻ⁿ`, so the area formula reduces to `Hⁿ⌞η(s) = λ⁻ⁿ η_#(Hⁿ⌞s)`
(`dtc_hausdorff_dilation`); `η(M)` is rectifiable as `η` is Lipschitz, `ξ ∘ η⁻¹` orients
`T_{η(y)}η(M) = T_yM` (`dtc_approxTangent_dilation`), and `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`
(`dtc_blowUp_testForm_corr`). -/
theorem Submission.dtc_blowUp_imrep : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s) := by
  intro P n U T x lam hlam R hR
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  obtain ⟨himage, hmap⟩ := Submission.dtc_hausdorff_dilation P n x lam hlam
  have htan : ∀ (y : Euclid P) (Q : Submodule ℝ (Euclid P)),
      HasApproximateTangentSpaceAt n R.carrier y Q →
        HasApproximateTangentSpaceAt n (dilation x lam '' R.carrier) (dilation x lam y) Q :=
    fun y Q => Submission.dtc_approxTangent_dilation P n R.carrier x y lam Q hlam
  -- `η = dilation x λ` is an affine homeomorphism with inverse `z ↦ x + λ • z`
  have hηc : (((Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x)))) : Euclid P → Euclid P) = dilation x lam := by
    funext y
    simp [dilation, dilationCLM]
  have hme : MeasurableEmbedding (dilation x lam) := by
    rw [← hηc]
    exact Homeomorph.measurableEmbedding _
  have hιη : ∀ y, x + lam • dilation x lam y = y := fun y => by
    simp [dilation, dilationCLM, smul_add, smul_smul, mul_inv_cancel₀ hlam.ne']
  have hc0 : 0 ≤ lam⁻¹ ^ n := by positivity
  set c : ℝ≥0∞ := ENNReal.ofReal (lam⁻¹ ^ n) with hc
  -- `Hⁿ⌞η(s) = c • η_#(Hⁿ⌞s)`, hence change of variables along `η`
  have hkey : ∀ s : Set (Euclid P),
      μHE[n].restrict (dilation x lam '' s) = c • (μHE[n].restrict s).map (dilation x lam) := by
    intro s
    have h1 : (μHE[n].restrict s).map (dilation x lam) =
        ENNReal.ofReal (lam ^ n) • μHE[n].restrict (dilation x lam '' s) := by
      rw [← hme.injective.preimage_image s, ← hme.restrict_map, hmap, Measure.restrict_smul,
        hme.injective.preimage_image]
    rw [h1, smul_smul, hc, ← ENNReal.ofReal_mul hc0, ← mul_pow, inv_mul_cancel₀ hlam.ne',
      one_pow, ENNReal.ofReal_one, one_smul]
  have hlint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ≥0∞),
      ∫⁻ z in dilation x lam '' s, g z ∂μHE[n] = c * ∫⁻ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, lintegral_smul_measure, hme.lintegral_map, smul_eq_mul]
  have hint : ∀ (s : Set (Euclid P)) (g : Euclid P → ℝ),
      ∫ z in dilation x lam '' s, g z ∂μHE[n] =
        lam⁻¹ ^ n * ∫ y in s, g (dilation x lam y) ∂μHE[n] := by
    intro s g
    rw [hkey s, integral_smul_measure, hme.integral_map, hc, ENNReal.toReal_ofReal hc0,
      smul_eq_mul]
  refine ⟨{ carrier := dilation x lam '' R.carrier
            mult := fun z => R.mult (x + lam • z)
            orient := fun z => R.orient (x + lam • z)
            measurableSet_carrier := hme.measurableSet_image.mpr R.measurableSet_carrier
            carrier_subset := image_mono R.carrier_subset
            rectifiable := ?_
            measurable_mult := R.measurable_mult.comp (by fun_prop)
            mult_pos := ?_
            locallyIntegrable_mult := ?_
            aestronglyMeasurable_orient := ?_
            orients := ?_ }, ?_, ?_⟩
  · -- `η(M) ⊆ η(M₀) ∪ ⋃ⱼ range (η ∘ Fⱼ)` with `Hⁿ(η(M₀)) = 0` and `η ∘ Fⱼ` Lipschitz
    obtain ⟨M₀, hM₀, F, hF, hcover⟩ := R.rectifiable
    refine ⟨dilation x lam '' M₀, by rw [himage, hM₀, mul_zero], fun j => dilation x lam ∘ F j,
      fun j => ?_, ?_⟩
    · obtain ⟨K, hK⟩ := hF j
      exact ⟨_, ((isometry_add_left (-(lam⁻¹ • x))).lipschitzWith.comp
        (dilationCLM P lam).lipschitzWith).comp hK⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases hcover hy with h0 | h1
      · exact Or.inl ⟨y, h0, rfl⟩
      · obtain ⟨j, v, rfl⟩ := mem_iUnion.mp h1
        exact Or.inr (mem_iUnion.mpr ⟨j, v, rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    show 0 < R.mult (x + lam • dilation x lam y)
    rw [hιη]
    exact R.mult_pos y hy
  · -- `η(M) ∩ K = η(M ∩ η⁻¹(K))`, and `η⁻¹(K)` is a compact subset of `U`
    intro K hK hKU
    rw [← image_inter_preimage, hlint]
    simp only [hιη]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (R.locallyIntegrable_mult _ ?_ ?_)
    · rw [← hηc]
      exact (Homeomorph.isCompact_preimage _).mpr hK
    · rw [← hme.injective.preimage_image U]
      exact preimage_mono hKU
  · rw [hkey]
    refine (hme.aestronglyMeasurable_map_iff.mpr ?_).smul_measure c
    simpa [Function.comp_def, hιη] using R.aestronglyMeasurable_orient
  · rw [hkey]
    refine Measure.ae_smul_measure (hme.ae_map_iff.mpr (R.orients.mono fun y hy => ?_)) c
    obtain ⟨Q, hQ, hξ⟩ := hy
    exact ⟨Q, htan y Q hQ, by simpa [hιη] using hξ⟩
  · -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η) = λ⁻ⁿ ∫_M θ ⟨ω ∘ η, ξ⟩ dHⁿ = ∫_{η(M)} θ' ⟨ω, ξ'⟩ dHⁿ`
    intro ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow T ω ω' hω', hR ω']
    simp only [IMRep.action]
    rw [hint]
    congr 1
    refine setIntegral_congr_fun R.measurableSet_carrier fun y _ => ?_
    simp [hιη, hω']
  · -- `μ_{R'}(B) = c ∫_{η⁻¹(B)} θ d(Hⁿ⌞M) = c μ_R(η⁻¹(B))`
    intro s hs
    simp only [IMRep.measure]
    rw [withDensity_apply _ hs, withDensity_apply _ (hme.measurable hs), hkey,
      Measure.restrict_smul, hme.restrict_map, lintegral_smul_measure, hme.lintegral_map]
    simp [hιη]

/-- **Mass scaling of blow-ups: `M_{η(W)}(η_{x,λ#}T) = λ⁻ⁿ M_W(T)`** for `λ > 0` and every
`W ⊆ ℝᴾ` (scaling identity (1) in the proof of Simon 7.3.1, chapter-07.txt lines 329–331; mass
`M_W` of 6.2.5 with the Euclidean coefficient norm).  By `Submission.dtc_blowUp_testForm_corr`,
`ω ↦ ω ∘ η` and `ω' ↦ ω' ∘ ι` (`ι(z) = x + λz`) exchange the admissible forms for
`M_{η(W)}(η_{x,λ#}T)` and `M_W(T)`, preserving the coefficient norm pointwise, and
`η_{x,λ#}T(ω) = λ⁻ⁿ T(ω ∘ η)`; multiplication by `λ⁻ⁿ ≥ 0` commutes with the suprema. -/
theorem Submission.dtc_blowUp_massOn_image : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (W : Set (Euclid P)), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W := by
  intro P n U T x lam hlam W
  obtain ⟨hA, hB, hC⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  have hc : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.mpr hlam.le) n
  -- `η = η_{x,λ}` and `ι(z) = x + λz` are continuous and mutually inverse; so `η` is injective.
  have hηι : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hιη : ∀ y, x + lam • dilation x lam y = y := by
    intro y
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  have hηinj : Injective (dilation x lam) := fun y y' h => by
    rw [← hιη y, ← hιη y', h]
  have hηcont : Continuous (dilation x lam) :=
    continuous_const.add (dilationCLM P lam).continuous
  have hιcont : Continuous (fun z : Euclid P => x + lam • z) :=
    continuous_const.add (continuous_const_smul lam)
  unfold GeometricCurrentOn.massOn
  apply le_antisymm
  · -- Upper bound: an admissible `ω` for `η_{x,λ#}T` on `η(W)` gives the admissible
    -- `ω' = ω ∘ η` for `T` on `W` (`tsupport ω' ⊆ η⁻¹(η(W)) = W`), and
    -- `η_{x,λ#}T(ω) = λ⁻ⁿ T(ω')`.
    refine sSup_le ?_
    rintro _ ⟨ω, ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω', hω'⟩ := hA ω
    dsimp only
    rw [hC T ω ω' hω', ENNReal.ofReal_mul hc]
    gcongr
    refine le_sSup ⟨ω', ⟨?_, fun y => ?_⟩, rfl⟩
    · have hcomp : (ω' : DifferentialForm (Euclid P) n) =
          (ω : DifferentialForm (Euclid P) n) ∘ dilation x lam := funext hω'
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hηcont).trans ((preimage_mono hωs).trans ?_)
      rw [preimage_image_eq W hηinj]
    · rw [hω' y]
      exact hωn _
  · -- Lower bound: an admissible `ω'` for `T` on `W` gives the admissible `ω = ω' ∘ ι` for
    -- `η_{x,λ#}T` on `η(W)` (`tsupport ω ⊆ ι⁻¹(W) ⊆ η(W)`), and `λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)`.
    rw [ENNReal.mul_sSup]
    refine iSup₂_le ?_
    rintro _ ⟨ω', ⟨hωs, hωn⟩, rfl⟩
    obtain ⟨ω, hω⟩ := hB ω'
    dsimp only
    rw [← ENNReal.ofReal_mul hc, ← hC T ω ω' hω]
    refine le_sSup ⟨ω, ⟨?_, fun z => ?_⟩, rfl⟩
    · have hcomp : (ω : DifferentialForm (Euclid P) n) =
          (ω' : DifferentialForm (Euclid P) n) ∘ fun z => x + lam • z := by
        funext z
        rw [Function.comp_apply, hω, hηι]
      rw [hcomp]
      refine (tsupport_comp_subset_preimage _ hιcont).trans fun z hz => ?_
      exact ⟨x + lam • z, hωs hz, hηι z⟩
    · have h := hωn (x + lam • z)
      rwa [hω, hηι] at h
/-- **`currentEval` of the blow-up `η_{x,λ#}T` is `currentEval T ∘ η^#`** (Simon 6.2.23 for the
dilation `η = η_{x,λ}(y) = λ⁻¹(y − x)`, `λ > 0`, chapter-06.txt lines 403–413; used for
`η_{x,λⱼ#}T ⇀ C` in the proof of 7.3.1, chapter-07.txt lines 329–337).  For every `n`-form `ω` on
`ℝᴾ`, `currentEval (η_{x,λ#}T) ω = currentEval T (η^#ω)`.  By multilinearity
`(η^#ω)(y) = ω(η(y)) ∘ (λ⁻¹ id) = λ⁻ⁿ ω(η(y))`.  If `ω ∈ 𝒟ⁿ(η(U))`, then `ω' = ω ∘ η ∈ 𝒟ⁿ(U)` and
`η^#ω = λ⁻ⁿ ω' ∈ 𝒟ⁿ(U)`, so both sides are `λ⁻ⁿ T(ω')` (`Submission.dtc_blowUp_testForm_corr`).
Otherwise `η^#ω ∉ 𝒟ⁿ(U)` and both sides are `0`: if `η^#ω ∈ 𝒟ⁿ(U)`, then `λⁿ η^#ω = ω ∘ η` gives
`ω₁ ∈ 𝒟ⁿ(η(U))` with `ω₁ ∘ η = ω ∘ η`, and `ω₁ = ω` since `η(x + λz) = z`. -/
theorem Submission.dimred_tr_bc_currentEval_blowUp : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) := by
  intro P n U T x lam hlam ω
  have hne : lam ≠ 0 := hlam.ne'
  obtain ⟨hA1, hA2, hA3⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  -- Step 1 (multilinearity): `(η^#ω)(p) = ω(η(p))(λ⁻¹ ·, …, λ⁻¹ ·) = λ⁻ⁿ ω(η(p))`.
  have hpull : ∀ p, affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω p =
      lam⁻¹ ^ n • ω (dilation x lam p) := by
    intro p
    ext v
    simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
    have hv : ⇑(dilationCLM P lam) ∘ v = fun i => lam⁻¹ • v i := by
      funext i
      simp [dilationCLM]
    rw [hv, ContinuousAlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    rfl
  -- Step 2: `η` is surjective, `η(x + λz) = z`.
  have hsurj : ∀ z, dilation x lam (x + lam • z) = z := by
    intro z
    simp [dilation, dilationCLM, smul_add, smul_smul, hne]
  unfold currentEval
  by_cases h : IsTestForm ω ∧ tsupport ω ⊆ dilation x lam '' U
  · -- Case 1: `ω ∈ 𝒟ⁿ(η(U))`.  With `ω' = ω ∘ η ∈ 𝒟ⁿ(U)` (part (a)), `η^#ω = λ⁻ⁿ ω'`, so
    -- `T(η^#ω) = λ⁻ⁿ T(ω') = η_{x,λ#}T(ω)` (part (c)).
    rw [dite_eq_left h]
    obtain ⟨ω', hω'⟩ := hA1 ⟨ω, h⟩
    have hν : affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω =
        ((lam⁻¹ ^ n • ω' : TestFormOn U n) : DifferentialForm (Euclid P) n) := by
      funext p
      rw [hpull p, Submodule.coe_smul, Pi.smul_apply, hω' p]
    have h' : IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ∧
        tsupport (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ⊆ U := by
      rw [hν]
      exact (lam⁻¹ ^ n • ω').property
    have hν' : (⟨affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω, h'⟩ : TestFormOn U n) =
        lam⁻¹ ^ n • ω' := Subtype.ext hν
    rw [dite_eq_left h', hA3 T ⟨ω, h⟩ ω' hω', hν', map_smul, smul_eq_mul]
  · -- Case 2: `ω ∉ 𝒟ⁿ(η(U))`.  If `η^#ω ∈ 𝒟ⁿ(U)`, then part (b) applied to `λⁿ η^#ω = ω ∘ η`
    -- gives `ω₁ ∈ 𝒟ⁿ(η(U))` with `ω₁ ∘ η = ω ∘ η`, hence `ω₁ = ω` by surjectivity of `η`.
    rw [dite_eq_right h]
    have h' : ¬(IsTestForm (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ∧
        tsupport (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω) ⊆ U) := by
      intro h'
      obtain ⟨ω₁, hω₁⟩ := hA2 (lam ^ n • (⟨_, h'⟩ : TestFormOn U n))
      have hω₁ω : (ω₁ : DifferentialForm (Euclid P) n) = ω := by
        funext z
        have hz := hω₁ (x + lam • z)
        rw [hsurj z, Submodule.coe_smul, Pi.smul_apply] at hz
        change lam ^ n • affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω (x + lam • z) =
          (ω₁ : DifferentialForm (Euclid P) n) z at hz
        rw [← hz, hpull, hsurj z, smul_smul, ← mul_pow, mul_inv_cancel₀ hne, one_pow, one_smul]
      exact h (hω₁ω ▸ ω₁.property)
    rw [dite_eq_right h']
/-- **Composition of dilation pull-backs** (the pull-back `f^#` of 6.2.23, chapter-06.txt lines
404–409; needed for the closure (10) of `𝒯` under `η_{x,λ#}`, Appendix A.1, in the proof of
7.3.3(1), chapter-07.txt line 472).  For `λ ≠ 0`, `η_{y,μ} ∘ η_{x,λ} = η_{x+λy,λμ}`, since
`μ⁻¹(λ⁻¹(p − x) − y) = (λμ)⁻¹(p − x − λy)`; hence, by contravariance of the affine pull-back,
`η_{x,λ}^#(η_{y,μ}^#ω) = η_{x+λy,λμ}^#ω`. -/
theorem Submission.dimred_tr_bc_dilation_pullback_comp : ∀ (P n : ℕ) (x y : Euclid P) (lam mu : ℝ), lam ≠ 0 → ∀ ω : DifferentialForm (Euclid P) n, affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) (affinePullbackForm (dilationCLM P mu) (-(mu⁻¹ • y)) ω) = affinePullbackForm (dilationCLM P (lam * mu)) (-((lam * mu)⁻¹ • (x + lam • y))) ω := by
  intro P n x y lam mu hlam ω
  -- `dilationCLM P a` is `v ↦ a⁻¹ • v`.
  have hd : ∀ (a : ℝ) (v : Euclid P), dilationCLM P a v = a⁻¹ • v := fun _ _ => rfl
  -- Linear parts: `μ⁻¹(λ⁻¹v) = (λμ)⁻¹v`.
  have hlin : ∀ v : Euclid P,
      dilationCLM P mu (dilationCLM P lam v) = dilationCLM P (lam * mu) v := by
    intro v
    rw [hd, hd, hd, smul_smul, mul_inv, mul_comm mu⁻¹ lam⁻¹]
  -- Base points: `−μ⁻¹y + μ⁻¹(−λ⁻¹x + λ⁻¹p) = −(λμ)⁻¹(x + λy) + (λμ)⁻¹p`, as `(λμ)⁻¹λ = μ⁻¹`.
  have hbase : ∀ p : Euclid P,
      -(mu⁻¹ • y) + dilationCLM P mu (-(lam⁻¹ • x) + dilationCLM P lam p) =
        -((lam * mu)⁻¹ • (x + lam • y)) + dilationCLM P (lam * mu) p := by
    intro p
    have hcoef : (lam * mu)⁻¹ * lam = mu⁻¹ := by
      rw [mul_inv, mul_comm lam⁻¹ mu⁻¹, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
    simp only [hd, smul_add, smul_neg, smul_smul, hcoef]
    rw [mul_inv, mul_comm mu⁻¹ lam⁻¹]
    abel
  -- At `p` and `(v₁, …, vₙ)` both sides are `ω(b + Lp)(Lv₁, …, Lvₙ)` with the same `b + Lp`
  -- and the same `L`.
  funext p
  ext v
  simp only [affinePullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hbase p]
  congr 1
  funext i
  exact hlin (v i)

/-- **Blow-up calculus for `η_{x,λ#}T`, `λ > 0`** (Simon 6.2.23 for the dilation
`η = η_{x,λ}(y) = λ⁻¹(y − x)`, chapter-06.txt lines 403–413; scaling identity (1) in the proof of
7.3.1, chapter-07.txt lines 329–331, and the closure (10) of `𝒯` under `η_{x,λ#}` in the proof of
7.3.3, chapter-07.txt line 472).  (i) `M_W(η_{x,λ#}T) = λ⁻ⁿ M_{η⁻¹(W)}(T)` for every `W ⊆ ℝᴾ`:
`η` is surjective (`η(x + λz) = z`), so `W = η(η⁻¹(W))` and this is the image form
`Submission.dtc_blowUp_massOn_image`.  (ii) `currentEval (η_{x,λ#}T) ω = currentEval T (η^#ω)`
(`Submission.dimred_tr_bc_currentEval_blowUp`).  (iii) Applying (ii) to `η_{y,μ#}` and then to
`η_{x,λ#}`, and composing the pull-backs, `η_{x,λ}^#(η_{y,μ}^#ω) = η_{x+λy,λμ}^#ω`
(`Submission.dimred_tr_bc_dilation_pullback_comp`), gives
`currentEval (η_{y,μ#}η_{x,λ#}T) ω = currentEval (η_{x+λy,λμ#}T) ω`. -/
theorem Submission.dimred_tr_blowup_calculus : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω := by
  intro P n U T x lam hlam
  have hne : lam ≠ 0 := hlam.ne'
  -- `η = η_{x,λ}` is surjective: `η(x + λz) = z`.
  have hsurj : Surjective (dilation x lam) := fun z =>
    ⟨x + lam • z, by simp [dilation, dilationCLM, smul_add, smul_smul, hne]⟩
  refine ⟨fun W => ?_, Submission.dimred_tr_bc_currentEval_blowUp P n U T x lam hlam, ?_⟩
  · -- (i) With `W' = η⁻¹(W)`, `η(W') = W`, so `M_W(η_{x,λ#}T) = M_{η(W')}(η_{x,λ#}T)`
    -- `= λ⁻ⁿ M_{W'}(T)`.
    have h := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W)
    rwa [image_preimage_eq W hsurj] at h
  · -- (iii) `currentEval (η_{y,μ#}η_{x,λ#}T) ω = currentEval (η_{x,λ#}T) (η_{y,μ}^#ω)`
    -- `= currentEval T (η_{x,λ}^#η_{y,μ}^#ω) = currentEval T (η_{x+λy,λμ}^#ω)`
    -- `= currentEval (η_{x+λy,λμ#}T) ω`.
    intro y mu hmu ω
    rw [Submission.dimred_tr_bc_currentEval_blowUp P n _ _ y mu hmu ω,
      Submission.dimred_tr_bc_currentEval_blowUp P n U T x lam hlam,
      Submission.dimred_tr_bc_dilation_pullback_comp P n x y lam mu hne,
      Submission.dimred_tr_bc_currentEval_blowUp P n U T (x + lam • y) (lam * mu)
        (mul_pos hlam hmu) ω]

/-- **Blow-ups commute with the current operations** (Simon 6.2.11, 6.2.23–6.2.24(1) for
`η = η_{x,λ}`, `λ > 0`): `η_#(S − T) = η_#S − η_#T`, `η_#` is injective,
`spt(η_#T) = η(spt T)` and `∂(η_#T) = η_#(∂T)`.

(i) Both sides evaluate `S − T` on the same pulled-back form.  (ii) Every `ω' ∈ 𝒟ⁿ(U)` is
`ω ∘ η` for some `ω ∈ 𝒟ⁿ(η(U))`, and `η_#Y(ω) = λ⁻ⁿ Y(ω')` (`dtc_blowUp_testForm_corr`).
(iii) `η` is an affine homeomorphism, and `η_#T` vanishes on `W₀ ⊂⊂ η(U)` iff `T` vanishes on
`η⁻¹(W₀) ⊂⊂ U`; so the zero regions correspond, and `spt(η_#T) = η(spt T)` as `η` is injective.
(iv) `d` commutes with affine pull-back (`GeometricCurrentOn.boundary_affinePushforward`). -/
theorem Submission.dtc_blowUp_algebra : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp (S - T) x lam hlam.ne' = blowUp S x lam hlam.ne' - blowUp T x lam hlam.ne') ∧ (∀ (n : ℕ) (S T : GeometricCurrentOn U n), blowUp S x lam hlam.ne' = blowUp T x lam hlam.ne' → S = T) ∧ (∀ (n : ℕ) (T : GeometricCurrentOn U n), (blowUp T x lam hlam.ne').support = dilation x lam '' T.support) ∧ ∀ (m : ℕ) (T : GeometricCurrentOn U (m + 1)), (blowUp T x lam hlam.ne').boundary = blowUp T.boundary x lam hlam.ne' := by
  intro P U x lam hlam
  have hc (n : ℕ) : lam⁻¹ ^ n ≠ 0 := pow_ne_zero n (inv_ne_zero hlam.ne')
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨fun n S T => GeometricCurrentOn.ext fun ω => rfl, fun n S T h => ?_, fun n T => ?_,
    fun m T => ?_⟩
  · -- (ii) `λ⁻ⁿ S(ω') = η_#S(ω) = η_#T(ω) = λ⁻ⁿ T(ω')`
    obtain ⟨-, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    refine GeometricCurrentOn.ext fun ω' => ?_
    obtain ⟨ω, hω⟩ := hb ω'
    have hS := hval S ω ω' hω
    rw [h, hval T ω ω' hω] at hS
    exact mul_left_cancel₀ (hc n) hS.symm
  · -- (iii) the zero regions correspond under `η`
    obtain ⟨ha, hb, hval⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
    have hzero : (blowUp T x lam hlam.ne').zeroRegion = dilation x lam '' T.zeroRegion := by
      ext z
      constructor
      · rintro ⟨W₀, ⟨hW₀o, hW₀c, hW₀U, hW₀v⟩, hz⟩
        rw [← he] at hW₀U
        have hW : closure (e ⁻¹' W₀) = e ⁻¹' closure W₀ := (e.preimage_closure W₀).symm
        refine ⟨e.symm z, ⟨e ⁻¹' W₀, ⟨hW₀o.preimage e.continuous, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
        · rw [hW]
          exact e.isCompact_preimage.2 hW₀c
        · rw [hW]
          exact (preimage_mono hW₀U).trans (e.preimage_image U).subset
        · intro ω' hω'
          obtain ⟨ω, hω⟩ := hb ω'
          have hsupp : tsupport (ω : DifferentialForm (Euclid P) n) ⊆ W₀ := by
            have hfun : (ω : DifferentialForm (Euclid P) n) =
                (ω' : DifferentialForm (Euclid P) n) ∘ e.symm := by
              funext y
              rw [Function.comp_apply, hω, ← congrFun he (e.symm y), e.apply_symm_apply]
            rw [hfun]
            refine (tsupport_comp_subset_preimage _ e.symm.continuous).trans fun y hy => ?_
            have hy' := hω' (mem_preimage.1 hy)
            rwa [mem_preimage, e.apply_symm_apply] at hy'
          have h0 := hW₀v ω hsupp
          rw [hval T ω ω' hω] at h0
          exact (mul_eq_zero.1 h0).resolve_left (hc n)
        · rwa [mem_preimage, e.apply_symm_apply]
        · rw [← he]
          exact e.apply_symm_apply z
      · rintro ⟨w, ⟨W, ⟨hWo, hWc, hWU, hWv⟩, hw⟩, rfl⟩
        have hW : closure (e '' W) = e '' closure W := (e.image_closure W).symm
        refine ⟨e '' W, ⟨e.isOpenMap W hWo, ?_, ?_, ?_⟩, ?_⟩
        · rw [hW]
          exact hWc.image e.continuous
        · rw [hW, ← he]
          exact image_mono hWU
        · intro ω hω
          obtain ⟨ω', hω'⟩ := ha ω
          have hsupp : tsupport (ω' : DifferentialForm (Euclid P) n) ⊆ W := by
            have hfun : (ω' : DifferentialForm (Euclid P) n) =
                (ω : DifferentialForm (Euclid P) n) ∘ e := by
              funext y
              rw [Function.comp_apply, hω', ← congrFun he y]
            rw [hfun, ← e.preimage_image W]
            exact (tsupport_comp_subset_preimage _ e.continuous).trans (preimage_mono hω)
          rw [hval T ω ω' hω', hWv ω' hsupp, mul_zero]
        · rw [← he]
          exact mem_image_of_mem e hw
    have hinj : Function.Injective (dilation x lam) := he ▸ e.injective
    simp only [GeometricCurrentOn.support]
    rw [hzero, image_sdiff hinj]
  · -- (iv) `d` commutes with the affine pull-back
    unfold blowUp
    rw [GeometricCurrentOn.boundary_affinePushforward]
    rfl
/-- **Every current in `η(U)` is a blow-up**, `η = η_{x,λ}`, `λ > 0` (Simon Ch. 6, 2.23 and 3.9
for `η⁻¹`; used for the minimality of `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt
lines 326–338): every `S' ∈ 𝒟ₙ(η(U))` is `η_{x,λ#}S''` for some `S'' ∈ 𝒟ₙ(U)`, integer
multiplicity whenever `S'` is.  `κ = η_{−λ⁻¹x,λ⁻¹}` inverts `η`, so `κ(η(U)) = U`, and `S''` is
`κ_#S'` restricted to `U`: `dtc_blowUp_testForm_corr` for `η` and for `κ` gives
`η_#S''(ω) = λ⁻ⁿ κ_#S'(ω ∘ η) = λ⁻ⁿ λⁿ S'(ω)`, and a representation of `κ_#S'` in
`κ(η(U)) = U` (`dtc_blowUp_imrep`) represents `S''`. -/
theorem Submission.dtc_blowUp_preimage : ∀ (P n : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (S' : GeometricCurrentOn (dilation x lam '' U) n), ∃ S'' : GeometricCurrentOn U n, blowUp S'' x lam hlam.ne' = S' ∧ (IsIntegerMultiplicity S' → IsIntegerMultiplicity S'') := by
  intro P n U x lam hlam S'
  have hlam' : 0 < lam⁻¹ := inv_pos.mpr hlam
  -- `κ = η_{−λ⁻¹x,λ⁻¹}`, `κ(z) = x + λz`, is a two-sided inverse of `η = η_{x,λ}`
  have hκη : ∀ y, dilation (-(lam⁻¹ • x)) lam⁻¹ (dilation x lam y) = y := fun y => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hηκ : ∀ z, dilation x lam (dilation (-(lam⁻¹ • x)) lam⁻¹ z) = z := fun z => by
    simp [dilation, dilationCLM, smul_smul, hlam.ne']
  have hdom : dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) = U := by
    rw [image_image]
    simp only [hκη, image_id']
  have hUV : U ⊆ dilation (-(lam⁻¹ • x)) lam⁻¹ '' (dilation x lam '' U) := hdom.superset
  obtain ⟨hpull, -, hblow⟩ := Submission.dtc_blowUp_testForm_corr P n U x lam hlam
  have hblow' := (Submission.dtc_blowUp_testForm_corr P n (dilation x lam '' U)
    (-(lam⁻¹ • x)) lam⁻¹ hlam').2.2
  -- `S'' := κ_#S'`, restricted from `κ(η(U)) = U` to `U`
  refine ⟨(blowUp S' (-(lam⁻¹ • x)) lam⁻¹ hlam'.ne').restrictDomain hUV, ?_, ?_⟩
  · -- `η_#S''(ω) = λ⁻ⁿ S''(ω ∘ η)` and `κ_#S'(ω ∘ η) = λⁿ S'(ω)`, as `ω ∘ η ∘ κ = ω`
    ext ω
    obtain ⟨ω', hω'⟩ := hpull ω
    rw [hblow _ ω ω' hω', GeometricCurrentOn.restrictDomain_apply,
      hblow' S' (testFormOnInclusion hUV n ω') ω fun z => by
        rw [testFormOnInclusion_coe, hω', hηκ],
      ← mul_assoc, ← mul_pow, inv_inv, inv_mul_cancel₀ hlam.ne', one_pow, one_mul]
  · -- a representation of `κ_#S'` in `κ(η(U)) = U` is one in `U`, and it represents `S''`
    rintro ⟨R₁, hR₁⟩
    obtain ⟨R₂, hR₂, -⟩ := Submission.dtc_blowUp_imrep P n (dilation x lam '' U) S'
      (-(lam⁻¹ • x)) lam⁻¹ hlam' R₁ hR₁
    exact ⟨{ R₂ with
        carrier_subset := R₂.carrier_subset.trans hdom.subset
        locallyIntegrable_mult := fun K hK hKU =>
          R₂.locallyIntegrable_mult K hK (hKU.trans hUV) },
      fun ω => hR₂ (testFormOnInclusion hUV n ω)⟩

/-- **Blow-ups preserve minimality** (Simon 7.1.1, chapter-07.txt lines 12–18, for `η = η_{x,λ}`,
`λ > 0`; used for `η_{x,λⱼ#}T` in the proof of 7.3.1, chapter-07.txt lines 329–337): if `T` is
minimizing in `A`, then `η_#T` is minimizing in `η(A)`.

`η_#T` is integer multiplicity (`dtc_blowUp_imrep`).  A competitor `S'` for `η_#T` on
`W' ⊂⊂ η(U)` is `η_#S''` with `S''` integer multiplicity (`dtc_blowUp_preimage`), and `S''` is a
competitor for `T` on `W = η⁻¹(W') ⊂⊂ U`: `∂S'' = ∂T` and
`spt(S'' − T) = η⁻¹(spt(S' − η_#T)) ⊆ A ∩ W` (`dtc_blowUp_algebra`).  So
`M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')` (`dtc_blowUp_massOn_image`). -/
theorem Submission.dtc_blowUp_isMinimizingIn : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A) := by
  intro P n U A T x lam hlam hT
  obtain ⟨⟨R, hR⟩, hmin⟩ := hT
  obtain ⟨hsub, hinj, hspt, hbdry⟩ := Submission.dtc_blowUp_algebra P U x lam hlam
  -- `η = η_{x,λ}` as a homeomorphism
  obtain ⟨e, he⟩ : ∃ e : Euclid P ≃ₜ Euclid P, ⇑e = dilation x lam :=
    ⟨(Homeomorph.smulOfNeZero lam⁻¹ (inv_ne_zero hlam.ne')).trans
      (Homeomorph.addLeft (-(lam⁻¹ • x))), by
        funext y
        simp [dilation, dilationCLM]⟩
  refine ⟨?_, fun W' S' hW'o hW'c hS'im hS'bd hS'c hS'A => ?_⟩
  · -- `η_#T` is integer multiplicity
    obtain ⟨R', hR', -⟩ := Submission.dtc_blowUp_imrep P n U T x lam hlam R hR
    exact ⟨R', hR'⟩
  -- `S' = η_#S''` with `S''` integer multiplicity
  obtain ⟨S'', rfl, hS''im⟩ := Submission.dtc_blowUp_preimage P n U x lam hlam S'
  -- `W = η⁻¹(W')` is open and `W ⊂⊂ U`, since `closure W = η⁻¹(closure W')` and `η⁻¹(η(U)) = U`
  have hWo : IsOpen (dilation x lam ⁻¹' W') := by
    rw [← he]
    exact hW'o.preimage e.continuous
  have hWc : CompactlyContained (dilation x lam ⁻¹' W') U := by
    obtain ⟨hc, hsub'⟩ := hW'c
    rw [← he] at hsub' ⊢
    refine ⟨?_, ?_⟩ <;> rw [← e.preimage_closure]
    · exact e.isCompact_preimage.2 hc
    · exact (preimage_mono hsub').trans (e.preimage_image U).subset
  -- `∂S'' = ∂T`: `η_#(∂S'') = ∂S' = ∂(η_#T) = η_#(∂T)` and `η_#` is injective
  have hbd : SameBoundary S'' T := by
    cases n with
    | zero => trivial
    | succ m =>
      show S''.boundary = T.boundary
      apply hinj
      rw [← hbdry, ← hbdry]
      exact hS'bd
  -- `spt(S' − η_#T) = η(spt(S'' − T))`, so `spt(S'' − T)` is compact and lies in `A ∩ W`
  have hspt' : (blowUp S'' x lam hlam.ne' - blowUp T x lam hlam.ne').support =
      dilation x lam '' (S'' - T).support := by
    rw [← hsub, hspt]
  rw [hspt', ← he] at hS'c hS'A
  have hc : IsCompact (S'' - T).support := e.isCompact_image.1 hS'c
  have hA : (S'' - T).support ⊆ A ∩ dilation x lam ⁻¹' W' := by
    intro y hy
    obtain ⟨⟨a, ha, hay⟩, hyW'⟩ := hS'A (mem_image_of_mem e hy)
    rw [← he]
    exact ⟨e.injective hay ▸ ha, hyW'⟩
  -- `M_{W'}(η_#T) = λ⁻ⁿ M_W(T) ≤ λ⁻ⁿ M_W(S'') = M_{W'}(S')`, as `η(W) = W'`
  have hle := hmin _ S'' hWo hWc (hS''im hS'im) hbd hc hA
  have hW' : dilation x lam '' (dilation x lam ⁻¹' W') = W' := by
    rw [← he]
    exact e.image_preimage W'
  have hmT := Submission.dtc_blowUp_massOn_image P n U T x lam hlam (dilation x lam ⁻¹' W')
  have hmS := Submission.dtc_blowUp_massOn_image P n U S'' x lam hlam (dilation x lam ⁻¹' W')
  rw [hW'] at hmT hmS
  rw [hmT, hmS]
  gcongr

/-- **Scaling of blow-ups** `η_{x,λ#}T`, `η = η_{x,λ}`, `λ > 0` (proof of Simon 7.3.1,
chapter-07.txt lines 326–338; push-forward 6.2.23 and 6.3.3–6.3.9): (1) the mass scaling
`M_{η(W)}(η_#T) = λ⁻ⁿ M_W(T)` of (1) there (`dtc_blowUp_massOn_image`); (2) a representation
`(M, θ, ξ)` of `T` pushes forward to one of `η_#T` with `μ_{η_#T}(B) = λ⁻ⁿ μ_T(η⁻¹(B))`
(`dtc_blowUp_imrep`); (3) `η_#T` is minimizing in `η(A)` if `T` is minimizing in `A`
(`dtc_blowUp_isMinimizingIn`).  The hypotheses `U` open and `n > 0` are not needed. -/
theorem Submission.dtc_blowUp_scaling : ∀ (P n : ℕ) (U A : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), IsOpen U → 0 < n → (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn (dilation x lam '' W) = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn W) ∧ (∀ R : IMRep U n, R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) ∧ (IsMinimizingIn T A → IsMinimizingIn (blowUp T x lam hlam.ne') (dilation x lam '' A)) := by
  intro P n U A T x lam hlam _ _
  exact ⟨Submission.dtc_blowUp_massOn_image P n U T x lam hlam,
    Submission.dtc_blowUp_imrep P n U T x lam hlam,
    Submission.dtc_blowUp_isMinimizingIn P n U A T x lam hlam⟩
/-- **The weight of a cone is homogeneous of degree `n`** (proof of Simon 7.4.5,
chapter-07.txt lines 697–699, "by virtue of the fact that `C` is a cone").  If the cone `C` is
represented by `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` and `λ > 0`, then `μ(λA) = λⁿ μ(A)` for
every Borel `A`.  The dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, and
`R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·)) = C(λ⁻ⁿ ω(λ⁻¹·)) = C(ω)` as `η_{0,λ#}C = C`, so `R_λ` represents `C`.
By the uniqueness of the weight (Simon Ch. 6, 3.2(3)), `μ(A) = μ_{R_λ}(A) = λ⁻ⁿ μ(λA)`. -/
theorem Submission.cone_current_imrep_measure_smul_image : ∀ (P n : ℕ) (C : GeometricCurrentOn (univ : Set (Euclid P)) n) (R : IMRep (univ : Set (Euclid P)) n), IsConeCurrent C → R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid P), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A := by
  intro P n C R hC hR lam hlam A hA
  -- Step 1: the dilated triple `R_λ = (λ⁻¹M, θ(λ·), ξ(λ·))` is integer multiplicity, with
  -- `R_λ(ω) = R(λ⁻ⁿ ω(λ⁻¹·))` for every form `ω` and `μ_{R_λ}(A) = λ⁻ⁿ μ(λA)` for Borel `A`
  obtain ⟨Rl, hcar, hmult, horient⟩ := Submission.imrep_univ_smul_rescale_exists P n R lam hlam
  obtain ⟨haction, hmeasure⟩ :=
    Submission.imrep_smul_rescale_action_measure P n R Rl lam hlam hcar hmult horient
  -- Step 2: `R_λ` represents `C`: `C(ω) = C(ω') = R(ω') = R_λ(ω)` for `ω' = λ⁻ⁿ ω(λ⁻¹·)`
  have hRl : Rl.Represents C := by
    intro ω
    obtain ⟨ω', hω', hCω'⟩ := Submission.cone_current_apply_dilation_pullback P n C hC lam hlam ω
    rw [← hCω', hR ω', haction]
    congr 1
    funext y
    exact hω' y
  -- Step 3: the weight does not depend on the representation, so `μ_{R_λ} = μ` and
  -- `μ(A) = λ⁻ⁿ μ(λA)`
  have hA' := hmeasure A hA
  rw [Submission.imrep_measure_eq_of_represents_same_current P n univ C Rl R isOpen_univ hRl hR]
    at hA'
  -- Step 4: multiply by `λⁿ`, using `λⁿ λ⁻ⁿ = 1`
  have hpow : ENNReal.ofReal (lam ^ n) * ENNReal.ofReal (lam⁻¹ ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hlam.le n), ← mul_pow, mul_inv_cancel₀ hlam.ne', one_pow,
      ENNReal.ofReal_one]
  rw [hA', ← mul_assoc, hpow, one_mul]
/-- **Blow-up domains eventually contain bounded sets** (Simon 7.3.3(2), proof: the domain
claims for `η_{x,σᵢ#}T`).  If `U` is open, `x ∈ U`, `λᵢ > 0` and `λᵢ → 0`, then every bounded `K`
lies in `η_{x,λᵢ}(U)` for all large `i`: with `B_δ(x) ⊆ U` and `K ⊆ B̄_r(0)`, eventually
`λᵢ(|r| + 1) < δ`, and then each `w ∈ K` is `η_{x,λᵢ}(x + λᵢw)` with `x + λᵢw ∈ B_δ(x)`. -/
theorem Submission.idtp_tpf_blowUp_domain_eventually : ∀ (P : ℕ) (U : Set (Euclid P)) (x : Euclid P) (lams : ℕ → ℝ), IsOpen U → x ∈ U → (∀ i, 0 < lams i) → Tendsto lams atTop (𝓝 0) → ∀ K : Set (Euclid P), Bornology.IsBounded K → ∀ᶠ i in atTop, K ⊆ dilation x (lams i) '' U := by
  intro P U x lams hU hx hpos hlim K hK
  -- `B_δ(x) ⊆ U` and `K ⊆ B̄_r(0)`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  -- `λᵢ(|r| + 1) → 0 < δ`, so `λᵢ(|r| + 1) < δ` for all large `i`
  have hlim' : Tendsto (fun i => lams i * (|r| + 1)) atTop (𝓝 0) := by
    simpa using hlim.mul_const (|r| + 1)
  filter_upwards [hlim'.eventually (gt_mem_nhds hδ)] with i hi w hw
  -- `y = x + λᵢw` lies in `B_δ(x) ⊆ U`, and `η_{x,λᵢ}(y) = w`
  refine ⟨x + lams i • w, hball ?_, ?_⟩
  · have hw : ‖w‖ ≤ |r| + 1 := by
      linarith [mem_closedBall_zero_iff.mp (hr hw), le_abs_self r]
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (hpos i).le]
    exact (mul_le_mul_of_nonneg_left hw (hpos i).le).trans_lt hi
  · simp only [dilation, dilationCLM, smul_apply, ContinuousLinearMap.id_apply, smul_add,
      smul_smul, inv_mul_cancel₀ (hpos i).ne', one_smul, neg_add_cancel_left]

/-- **Weak limits of blow-ups of a cycle are cycles** (`∂C = 0` for the blow-up limit `C` in the
proof of Simon 7.3.3(2), chapter-07.txt line 512 ff.; cf. the proof of 7.3.1, lines 335–336,
where `∂η_{x,λⱼ#}T = 0` in `B_{MR}(0)` for large `j`, and Ch. 6, 2.13 and 2.24(1)).  If
`∂T = 0` in `U`, `λᵢ > 0`, `λᵢ → 0` and `η_{x,λᵢ#}T ⇀ C` in `ℝᴾ`, then `∂C = 0`: for
`ω ∈ 𝒟ᵐ(ℝᴾ)`, the compact set `spt ω ⊇ spt dω` lies in `η_{x,λᵢ}(U)` for all large `i`
(`idtp_tpf_blowUp_domain_eventually`), and there
`η_{x,λᵢ#}T(dω) = ∂(η_{x,λᵢ#}T)(ω) = η_{x,λᵢ#}(∂T)(ω) = 0`; hence
`∂C(ω) = C(dω) = limᵢ η_{x,λᵢ#}T(dω) = 0`. -/
theorem Submission.idtp_tpf_blowUp_limit_boundaryVanishes : ∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → BoundaryVanishes T → Tendsto lams atTop (𝓝 0) → ConvergesWeakly (fun i => blowUp T x (lams i) (hlams i).ne') C → BoundaryVanishes C := by
  intro P n U T x lams hlams C hU hx hT hlim hconv
  cases n with
  | zero => trivial
  | succ m =>
    -- step 1: `∂T = 0`, and it suffices that `∂C(ω) = C(dω) = 0` for every `ω ∈ 𝒟ᵐ(ℝᴾ)`
    change T.boundary = 0 at hT
    change C.boundary = 0
    ext ω
    rw [GeometricCurrentOn.boundary_apply, GeometricCurrentOn.zero_apply]
    -- step 2: the compact set `spt ω` lies in `η_{x,λᵢ}(U)` for all large `i`
    have hev := Submission.idtp_tpf_blowUp_domain_eventually P U x lams hU hx hlams hlim
      (tsupport (ω : DifferentialForm (Euclid P) m)) ω.property.1.2.isCompact.isBounded
    -- steps 3–4: for such `i`, `η_{x,λᵢ#}T(dω) = ∂(η_{x,λᵢ#}T)(ω) = η_{x,λᵢ#}(∂T)(ω) = 0`
    have hzero : ∀ᶠ i in atTop, currentEval (blowUp T x (lams i) (hlams i).ne')
        (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) = 0 := by
      filter_upwards [hev] with i hi
      -- `∂` commutes with the affine push-forward `η_{x,λᵢ#}` (Simon 6.2.24(1)) ...
      have hB : (blowUp T x (lams i) (hlams i).ne').boundary =
          blowUp T.boundary x (lams i) (hlams i).ne' := by
        unfold blowUp
        rw [GeometricCurrentOn.boundary_affinePushforward]
        rfl
      -- ... and the blow-up of the zero current is zero
      have h0 : blowUp (0 : GeometricCurrentOn U m) x (lams i) (hlams i).ne' = 0 := by
        ext η
        unfold blowUp
        rw [GeometricCurrentOn.affinePushforward_apply, GeometricCurrentOn.restrictDomain_apply,
          GeometricCurrentOn.zero_apply, GeometricCurrentOn.zero_apply]
      -- `ω` is a test form in `η_{x,λᵢ}(U)`, and `currentEval` evaluates the blow-up on `dω`
      let ωi : TestFormOn (dilation x (lams i) '' U) m := ⟨ω, ω.property.1, hi⟩
      have hd : IsTestForm (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) ∧
          tsupport (exteriorDerivative (ω : DifferentialForm (Euclid P) m)) ⊆
            dilation x (lams i) '' U :=
        ⟨exteriorDerivative_isTestForm ω.property.1,
          (tsupport_exteriorDerivative_subset _).trans hi⟩
      rw [currentEval, dite_eq_left hd]
      change (blowUp T x (lams i) (hlams i).ne').boundary ωi = 0
      rw [hB, hT, h0, GeometricCurrentOn.zero_apply]
    -- step 5: `C(dω)` is the limit of a sequence that is eventually `0`
    exact tendsto_nhds_unique (hconv (exteriorDerivativeTestOn univ m ω))
      (tendsto_const_nhds.congr' (hzero.mono fun i hi => hi.symm))

/-- **The ambient space and the calculus of the dilations** `η_{a,s}(v) = s⁻¹(v − a)`, `s > 0`,
and of the rescaled measures `ν^{a,s} = s⁻ⁿ η_{a,s#}ν` (used tacitly by Simon in the proof of
7.3.3(1), cf. (10) there, chapter-07.txt line 472): (1) `ℝᴾ` is an embedded `C²` submanifold of
itself (Simon Ch. 2, (4.1), with `ψ = id`); (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`;
(3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`; (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`;
(5) `η_{a,s}(ℝᴾ) = ℝᴾ` and `η_{a,s}` is open; (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`;
(7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`; (8) `ν^{0,1} = ν` and `η_{0,1}(A) = A`;
(9) `s⁻ⁿ η_{a,s#}(ν⌞B) = ν^{a,s}⌞η_{a,s}(B)` for Borel `B`.  All of this follows from `η_{a,s}`
being the affine homeomorphism `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`. -/
theorem Submission.idtp_fons_cc_ambient_calculus : (∀ P : ℕ, IsEmbeddedSubmanifold 2 P (univ : Set (Euclid P))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (A : Set (Euclid P)), 0 < s → MeasurableSet A → (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)) A = ENNReal.ofReal (s⁻¹ ^ n) * ν (dilation a s ⁻¹' A)) ∧ (∀ (P : ℕ) (a w : Euclid P) (s ρ : ℝ), 0 < s → dilation a s ⁻¹' ball w ρ = ball (a + s • w) (s * ρ)) ∧ (∀ (P : ℕ) (a c : Euclid P) (s ρ : ℝ), 0 < s → dilation a s '' ball c ρ = ball (dilation a s c) (ρ / s)) ∧ (∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s → dilation a s '' univ = univ ∧ ∀ A : Set (Euclid P), IsOpen A → IsOpen (dilation a s '' A)) ∧ (∀ (P : ℕ) (a y : Euclid P) (s t : ℝ) (A : Set (Euclid P)), 0 < s → 0 < t → dilation y t '' (dilation a s '' A) = dilation (a + s • y) (s * t) '' A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t → ENNReal.ofReal (t⁻¹ ^ n) • (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).map (dilation y t) = ENNReal.ofReal ((s * t)⁻¹ ^ n) • ν.map (dilation (a + s • y) (s * t))) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)), ENNReal.ofReal ((1 : ℝ)⁻¹ ^ n) • ν.map (dilation 0 1) = ν ∧ ∀ A : Set (Euclid P), dilation (0 : Euclid P) 1 '' A = A) ∧ (∀ (P n : ℕ) (ν : Measure (Euclid P)) (a : Euclid P) (s : ℝ) (B : Set (Euclid P)), 0 < s → MeasurableSet B → ENNReal.ofReal (s⁻¹ ^ n) • (ν.restrict B).map (dilation a s) = (ENNReal.ofReal (s⁻¹ ^ n) • ν.map (dilation a s)).restrict (dilation a s '' B)) := by
  -- Step 0: `η_{a,s}(v) = s⁻¹(v − a)`; for `s > 0` it is the affine homeomorphism
  -- `v ↦ −s⁻¹a + s⁻¹v` with inverse `u ↦ a + su`, hence measurable, injective and open
  have hdil : ∀ (P : ℕ) (a : Euclid P) (s : ℝ) (v : Euclid P), dilation a s v = s⁻¹ • (v - a) := by
    intro P a s v
    show -(s⁻¹ • a) + s⁻¹ • v = s⁻¹ • (v - a)
    rw [smul_sub, neg_add_eq_sub]
  have hmeas : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), Measurable (dilation a s) := fun P a s =>
    (continuous_const.add (dilationCLM P s).continuous).measurable
  have hhomeo : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s →
      ∃ h : Euclid P ≃ₜ Euclid P, ⇑h = dilation a s := by
    intro P a s hs
    refine ⟨(Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs.ne')).trans
      (Homeomorph.addLeft (-(s⁻¹ • a))), ?_⟩
    funext v
    simp [dilation, dilationCLM]
  -- Step 6 (pointwise): `η_{y,t} ∘ η_{a,s} = η_{a+sy,st}`, as `(st)⁻¹ = t⁻¹s⁻¹`
  have hcomp : ∀ (P : ℕ) (a y : Euclid P) (s t : ℝ), 0 < s → 0 < t →
      dilation y t ∘ dilation a s = dilation (a + s • y) (s * t) := by
    intro P a y s t hs ht
    funext v
    rw [Function.comp_apply, hdil, hdil, hdil, mul_inv_rev, mul_smul, sub_add_eq_sub_sub,
      smul_sub s⁻¹ (v - a) (s • y), inv_smul_smul₀ hs.ne']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) `ℝᴾ` is a `C²` submanifold of itself: `V = W = ℝᴾ`, `ψ = id`
    intro P y _
    refine ⟨univ, univ, id, isOpen_univ, isOpen_univ, mem_univ y, contDiffOn_id, injOn_id univ,
      by simp, fun K _ hK => by simpa using hK, fun z _ => ?_⟩
    rw [fderiv_id, ContinuousLinearMap.coe_id']
    exact injective_id
  · -- (2) `ν^{a,s}(A) = s⁻ⁿ ν(η_{a,s}⁻¹(A))` for Borel `A`
    intro P n ν a s A _ hA
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply (hmeas P a s) hA]
  · -- (3) `η_{a,s}⁻¹(B_ρ(w)) = B_{sρ}(a + sw)`, as `η_{a,s}(v) − w = s⁻¹(v − (a + sw))`
    intro P a w s ρ hs
    ext v
    have hv : dilation a s v - w = s⁻¹ • (v - (a + s • w)) := by
      rw [hdil, sub_add_eq_sub_sub, smul_sub s⁻¹ (v - a) (s • w), inv_smul_smul₀ hs.ne']
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hv, norm_smul, norm_inv,
      Real.norm_of_nonneg hs.le, inv_mul_lt_iff₀ hs]
  · -- (4) `η_{a,s}(B_ρ(c)) = B_{ρ/s}(η_{a,s}(c))`: the image under `η_{a,s}` is the preimage
    -- under its inverse `u ↦ a + su`, and `a + su − c = s(u − η_{a,s}(c))`
    intro P a c s ρ hs
    rw [image_eq_preimage_of_inverse (f := dilation a s) (g := fun u => a + s • u)
      (fun v => show a + s • dilation a s v = v by rw [hdil, smul_inv_smul₀ hs.ne', add_sub_cancel])
      (fun u => show dilation a s (a + s • u) = u by
        rw [hdil, add_sub_cancel_left, inv_smul_smul₀ hs.ne'])]
    ext u
    have hu : a + s • u - c = s • (u - dilation a s c) := by
      rw [hdil, smul_sub, smul_inv_smul₀ hs.ne']
      abel
    rw [mem_preimage, mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, hu, norm_smul,
      Real.norm_of_nonneg hs.le, lt_div_iff₀ hs, mul_comm]
  · -- (5) `η_{a,s}` is a homeomorphism: surjective and open
    intro P a s hs
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    rw [← hh]
    exact ⟨image_univ_of_surjective h.surjective, fun A hA => h.isOpenMap A hA⟩
  · -- (6) `η_{y,t}(η_{a,s}(A)) = η_{a+sy,st}(A)`
    intro P a y s t A hs ht
    rw [← image_comp, hcomp P a y s t hs ht]
  · -- (7) `(ν^{a,s})^{y,t} = ν^{a+sy,st}`: `map_smul`, `map_map` and `t⁻ⁿs⁻ⁿ = (st)⁻ⁿ`
    intro P n ν a y s t hs ht
    rw [Measure.map_smul _ (hmeas P y t).aemeasurable, Measure.map_map (hmeas P y t) (hmeas P a s),
      hcomp P a y s t hs ht, smul_smul, ← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.2 ht.le) n),
      ← mul_pow, mul_inv_rev]
  · -- (8) `η_{0,1} = id`
    intro P n ν
    have h01 : dilation (0 : Euclid P) 1 = id := by
      funext v
      rw [hdil, inv_one, one_smul, sub_zero, id]
    refine ⟨?_, fun A => ?_⟩
    · rw [h01, Measure.map_id, inv_one, one_pow, ENNReal.ofReal_one, one_smul]
    · rw [h01, image_id]
  · -- (9) restriction commutes with the push-forward by the measurable embedding `η_{a,s}`,
    -- and `η_{a,s}⁻¹(η_{a,s}(B)) = B` by injectivity
    intro P n ν a s B hs _
    obtain ⟨h, hh⟩ := hhomeo P a s hs
    have hemb : MeasurableEmbedding (dilation a s) := hh ▸ h.measurableEmbedding
    rw [Measure.restrict_smul, hemb.restrict_map, hemb.injective.preimage_image]
/-- **The weight is the upper density times `Hⁿ`** (Simon Ch. 3, Remark 1.8(2) and Theorem 1.9).
Assume the density theorem: for every `R = (M, θ, ξ)` with weight `μ = θHⁿ⌞M` finite on compact
sets and `n ≥ 1`, `μ(B_ρ(x)) / (ωₙρⁿ) → 1_M(x)θ(x)` as `ρ ↓ 0` for `Hⁿ`-a.e. `x`.  Then
`μ = Hⁿ⌞L` for the upper density `L(x) = limsup_{ρ↓0} μ(B_ρ(x)) / (ωₙρⁿ)`, read through
`ofReal ∘ toReal`.  Where the ratio converges, `L(x)` is its limit `1_M(x)θ(x) < ∞`, so the two
densities agree `Hⁿ`-a.e., and `Hⁿ⌞(1_Mθ) = (Hⁿ⌞M)⌞θ = μ` as `M` is Borel. -/
theorem Submission.idtp_fons_cc_density_representation : (∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), 1 ≤ n → (∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞) → ∀ᵐ x ∂μHE[n], Tendsto (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator R.carrier (fun y => (R.mult y : ℝ≥0∞)) x))) → ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), 1 ≤ n → (∀ K : Set (Euclid P), IsCompact K → R.measure K ≠ ∞) → R.measure = (μHE[n] : Measure (Euclid P)).withDensity (fun x => ENNReal.ofReal ((limsup (fun ρ : ℝ => R.measure (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal)) := by
  intro hDEM P n U R hn hK
  -- Steps 1–2: wherever the density ratio converges, its limsup is the finite limit
  -- `1_M(x) θ(x)`, so `ofReal ∘ toReal` returns it unchanged
  have hae : (fun x => ENNReal.ofReal ((limsup (fun ρ : ℝ => R.measure (ball x ρ) /
      (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal)) =ᵐ[μHE[n]]
      R.carrier.indicator fun y => (R.mult y : ℝ≥0∞) := by
    filter_upwards [hDEM P n U R hn hK] with x hx
    rw [hx.limsup_eq, ENNReal.ofReal_toReal]
    by_cases hxM : x ∈ R.carrier
    · simp [Set.indicator_of_mem hxM]
    · simp [Set.indicator_of_notMem hxM]
  -- Steps 3–5: `Hⁿ.withDensity (1_M θ) = (Hⁿ⌞M).withDensity θ = μ_R`
  rw [withDensity_congr_ae hae, withDensity_indicator R.measurableSet_carrier]
  rfl
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
/-- Restricting an integer multiplicity triple `R = (C, θ, ξ)` to a Borel sub-carrier `C' ⊆ C`
with multiplicity `0 < θ' ≤ θ` on `C'`, keeping the orientation `ξ`, gives again a triple in `U`,
provided `Hⁿ`-a.e. point of `C'` inherits the approximate tangent spaces of `C` (Simon Ch. 6, 3.1).

Every field of `IMRep` for `(C', θ', ξ)` is inherited from `R`: `C' ⊆ C ⊆ U` is countably
rectifiable, `∫_{C' ∩ K} θ' dHⁿ ≤ ∫_{C' ∩ K} θ dHⁿ ≤ ∫_{C ∩ K} θ dHⁿ < ∞`, `Hⁿ⌞C' ≤ Hⁿ⌞C` carries
the measurability of `ξ`, and `R.orients` restricted to `C'` gives the orientation condition once
`T_x C = Q` is transferred to `T_x C' = Q`. -/
theorem Submission.regcomp_rim_sub_imrep : ∀ (P n : ℕ) (U C' : Set (Euclid P)) (R : IMRep U n) (θ' : Euclid P → ℕ), MeasurableSet C' → C' ⊆ R.carrier → Measurable θ' → (∀ x ∈ C', 0 < θ' x) → (∀ x ∈ C', θ' x ≤ R.mult x) → (∀ᵐ x ∂(μHE[n].restrict C'), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n R.carrier x Q → HasApproximateTangentSpaceAt n C' x Q) → ∃ R' : IMRep U n, R'.carrier = C' ∧ R'.mult = θ' ∧ R'.orient = R.orient := by
  intro P n U C' R θ' hC' hC'C hθ' hpos hle htan
  -- Step 6: `∫_{C' ∩ K} θ' ≤ ∫_{C' ∩ K} θ ≤ ∫_{C ∩ K} θ < ∞`
  have hint : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n] ≠ ∞ := by
    intro K hK hKU
    have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
      (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
    refine ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKU) ?_
    calc ∫⁻ x in C' ∩ K, (θ' x : ℝ≥0∞) ∂μHE[n]
        ≤ ∫⁻ x in C' ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono hθ fun x hx => by exact_mod_cast hle x hx.1
      _ ≤ ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          lintegral_mono_set (inter_subset_inter_left K hC'C)
  -- Step 7: `ξ` is a.e. strongly measurable for `Hⁿ⌞C' ≤ Hⁿ⌞C`
  have hmeas : AEStronglyMeasurable R.orient (μHE[n].restrict C') :=
    R.aestronglyMeasurable_orient.mono_measure (Measure.restrict_mono hC'C le_rfl)
  -- Step 8: restrict `R.orients` to `C'` and transfer the approximate tangent space
  have hor : ∀ᵐ x ∂(μHE[n].restrict C'), ∃ Q : Submodule ℝ (Euclid P),
      HasApproximateTangentSpaceAt n C' x Q ∧ IsUnitOrientationOf (R.orient x) Q := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hC'C R.orients, htan] with x hx hxt
    obtain ⟨Q, hQ, hξ⟩ := hx
    exact ⟨Q, hxt Q hQ, hξ⟩
  -- Step 9: assemble `R' = (C', θ', ξ)`
  exact ⟨IMRep.mk C' θ' R.orient hC' (hC'C.trans R.carrier_subset) (R.rectifiable.mono hC'C) hθ'
    hpos hint hmeas hor, rfl, rfl, rfl⟩
/-- **An integer multiplicity triple defines a current** (Simon 6.3.1 (‡)): for an `IMRep`
`R = (M, θ, ξ)` in `U`, `ω ↦ ∫_M θ⟨ω, ξ⟩ dHⁿ` is a current `T ∈ 𝒟ₙ(U)`, so `T = τ(M, θ, ξ)`.

Write `μ = Hⁿ⌞M`.  A unit orientation has `|ξ(x)(α)| = |α(τ₁, …, τₙ)| ≤ ‖α‖` (`τ` orthonormal),
the integrand is a.e. strongly measurable, and `1_K θ` is `μ`-integrable for compact `K ⊆ U`.
Hence for a test form `ω` the integrand is dominated by `sup|ω| · 1_{spt ω} θ`, so the functional
is defined and linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)` with supports in the compact `K`, then
`|T(ωⱼ)| ≤ sup_K |ωⱼ| · ∫_K θ dμ → 0`. -/
theorem Submission.dtc_imrep_current : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  set μ := μHE[n].restrict R.carrier with hμ
  -- (1) a unit orientation has norm at most one
  have hbound : ∀ᵐ x ∂μ, ∀ α : Covector (Euclid P) n, |R.orient x α| ≤ ‖α‖ := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, τ, hτ, -, hξ⟩ := hx
    intro α
    have hτn : ∀ i, ‖τ i‖ = 1 := fun i => hτ.1 i
    have hατ : |α τ| ≤ ‖α‖ := by
      have h := α.le_opNorm τ
      simp only [hτn, Finset.prod_const_one, mul_one, Real.norm_eq_abs] at h
      exact h
    rcases hξ with h | h
    · rw [h]; exact hατ
    · rw [h, abs_neg]; exact hατ
  have hθmeas : AEStronglyMeasurable (fun x => (R.mult x : ℝ)) μ :=
    ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp R.measurable_mult).aestronglyMeasurable
  -- (2) measurability of the integrand
  have hmeas : ∀ ω : DifferentialForm (Euclid P) n, Continuous ω →
      AEStronglyMeasurable (fun x => (R.mult x : ℝ) * R.orient x (ω x)) μ := by
    intro ω hω
    have h2 : AEStronglyMeasurable (fun x => R.orient x (ω x)) μ :=
      Continuous.comp_aestronglyMeasurable₂
        (g := fun (L : MultiVector P n) (α : Covector (Euclid P) n) => L α)
        (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Covector (Euclid P) n) (F := ℝ)).continuous
        R.aestronglyMeasurable_orient hω.aestronglyMeasurable
    exact hθmeas.mul h2
  -- (3) `θ` is integrable over compact subsets of `U`
  have hθK : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U →
      Integrable (K.indicator fun x => (R.mult x : ℝ)) μ := by
    intro K hK hKU
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    refine ⟨hθmeas.restrict, ?_⟩
    show ∫⁻ x, ‖(R.mult x : ℝ)‖ₑ ∂(μ.restrict K) < ∞
    rw [hμ, Measure.restrict_restrict hK.isClosed.measurableSet, inter_comm]
    simp only [Real.enorm_natCast]
    exact lt_top_iff_ne_top.mpr (R.locallyIntegrable_mult K hK hKU)
  -- (4) integrability of the integrand for test forms
  have hint : ∀ ω : TestFormOn U n,
      Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x))
        μ := by
    intro ω
    have hωc : Continuous (ω : DifferentialForm (Euclid P) n) := ω.property.1.1.continuous
    obtain ⟨C, hC⟩ := HasCompactSupport.exists_bound_of_continuous ω.property.1.2 hωc
    have hK : IsCompact (tsupport (ω : DifferentialForm (Euclid P) n)) := ω.property.1.2
    refine Integrable.mono' ((hθK _ hK ω.property.2).const_mul C) (hmeas _ hωc) ?_
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ω : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ω : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * C := by gcongr; exact hC x
        _ = C * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ω : DifferentialForm (Euclid P) n) x = 0 := image_eq_zero_of_notMem_tsupport hxK
      simp [h0, indicator_of_notMem hxK]
  -- (5) the linear functional `ω ↦ ∫_M θ ⟨ω, ξ⟩ dHⁿ`
  let L : TestFormOn U n →ₗ[ℝ] ℝ :=
    { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
      map_add' := by
        intro ω η
        simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
        exact integral_add (hint ω) (hint η)
      map_smul' := by
        intro c ω
        simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
          RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext x
        ring }
  refine ⟨⟨L, ?_⟩, fun ω => rfl⟩
  -- (6) sequential continuity
  intro ωs hconv
  obtain ⟨K, hK, hKU, hsupp, -, hderiv⟩ := hconv
  have h0 := hderiv 0
  rw [Metric.tendstoUniformlyOn_iff] at h0
  set CK := ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂μ with hCKdef
  have hCK : 0 ≤ CK := integral_nonneg fun x => indicator_nonneg (fun _ _ => Nat.cast_nonneg _) x
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / (CK + 1) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h0 (ε / (CK + 1)) hε')
  refine ⟨N, fun j hj => ?_⟩
  have hptw : ∀ x ∈ K, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ < ε / (CK + 1) := by
    intro x hx
    have h := hN j hj x hx
    rw [dist_comm, dist_eq_norm] at h
    simpa [norm_iteratedFDeriv_zero] using h
  rw [Real.dist_eq, sub_zero]
  have hle : |L (ωs j)| ≤ ∫ x, (ε / (CK + 1)) * K.indicator (fun x => (R.mult x : ℝ)) x ∂μ := by
    refine (Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le
      ((hθK K hK hKU).const_mul _) ?_)
    filter_upwards [hbound] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
      calc (R.mult x : ℝ) * |R.orient x ((ωs j : DifferentialForm (Euclid P) n) x)|
          ≤ (R.mult x : ℝ) * ‖(ωs j : DifferentialForm (Euclid P) n) x‖ := by
            gcongr; exact hx _
        _ ≤ (R.mult x : ℝ) * (ε / (CK + 1)) := by gcongr; exact (hptw x hxK).le
        _ = ε / (CK + 1) * (R.mult x : ℝ) := mul_comm _ _
    · have h0 : (ωs j : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxK (hsupp j h))
      simp [h0, indicator_of_notMem hxK]
  rw [integral_const_mul, ← hCKdef] at hle
  calc |L (ωs j)| ≤ ε / (CK + 1) * CK := hle
    _ < ε := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
/-- **Upper density theorem for `Hⁿ` off a Borel set of finite measure** (Simon Ch. 1, 3.3 and
3.6, with the crude covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `S ⊆ ℝᴾ` is Borel
with `Hⁿ(S) < ∞`, then for `Hⁿ`-a.e. `x ∉ S`, `Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  A failure
at `x` puts `x` in a threshold set `{x ∉ S : Hⁿ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}` with
`t = (k + 1)⁻¹`.  Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give
`t · μH[n](E) ≤ 6ⁿ Hⁿ(G)` whenever each `x ∈ E` has arbitrarily small `ρ` with
`t ρⁿ ≤ Hⁿ(G ∩ B̄_ρ(x))`.  Taking `G = S \ F` for a closed `F ⊆ S` with `Hⁿ(S \ F)` small (weak
regularity of the finite measure `Hⁿ⌞S`), which agrees with `S` near `x ∉ F`, every threshold set
is `μH[n]`-null, hence `Hⁿ`-null. -/
theorem Submission.regcomp_atl_upper_density_zero : ∀ (P n : ℕ) (S : Set (Euclid P)), MeasurableSet S → μHE[n] S ≠ ∞ → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n S hS hfin
  -- Step 2, Vitali selection (Simon 1.3.4): a countable disjoint subfamily whose
  -- 3-fold enlargements cover the centres.
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μHE[n] (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μHE[n] (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    -- packing estimate
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μHE[n] G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μHE[n] (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μHE[n] (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μHE[n] G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    -- diameter estimate
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μHE[n] G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μHE[n] G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μHE[n] G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μHE[n] G / t) := by gcongr
      _ = 6 ^ n * μHE[n] G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, each threshold set is null (Simon 1.3.6).
  have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
      μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
    intro t ht0 httop
    set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      t < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
    have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
      intro ε hε
      have : IsFiniteMeasure ((μHE[n] : Measure (Euclid P)).restrict S) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
      have : ((μHE[n] : Measure (Euclid P)).restrict S).WeaklyRegular :=
        Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
      have hpos : t * ε / 6 ^ n ≠ 0 := by
        apply ENNReal.div_ne_zero.2
        exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
      obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
        (μ := (μHE[n] : Measure (Euclid P)).restrict S)
        (by rw [Measure.restrict_apply hS, inter_self]; exact hfin) hpos
      have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
      have hμG : μHE[n] (S \ F) < t * ε / 6 ^ n := by
        rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
      have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
          t * ENNReal.ofReal ρ ^ n ≤ μHE[n] ((S \ F) ∩ closedBall x ρ) := by
        intro x hx δ hδ
        obtain ⟨hxS, hfreq⟩ := hx
        have hxF : x ∉ F := fun h => hxS (hFS h)
        obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
        have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
          Ioo_mem_nhdsGT (by positivity)
        obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
        refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
        have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
          pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
        have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
        have h1 : t * ENNReal.ofReal ρ ^ n < μHE[n] (S ∩ closedBall x ρ) :=
          (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
        have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
          ext y
          constructor
          · rintro ⟨hyS, hyB⟩
            refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
            rw [mem_ball]
            have := mem_closedBall.1 hyB
            have := hρ.2
            have := min_le_right δ (r₁ / 2)
            linarith
          · rintro ⟨⟨hyS, _⟩, hyB⟩
            exact ⟨hyS, hyB⟩
        rw [← h2]
        exact h1.le
      have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
      have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
      have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
      have hlt : t * μH[(n : ℝ)] N < t * ε := by
        calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μHE[n] (S \ F) := hcomp
          _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
          _ = t * ε := ENNReal.mul_div_cancel h6 h6'
      exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
    have hH : μH[(n : ℝ)] N = 0 := by
      by_contra h
      exact lt_irrefl _ (key _ h)
    rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
  -- Steps 1 and 4, every failure of convergence lies in a threshold set.
  rw [ae_iff]
  apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
    ((k : ℝ≥0∞) + 1)⁻¹ < μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
  · intro x hx
    simp only [mem_ofPred_eq, Classical.not_imp] at hx
    obtain ⟨hxS, hnt⟩ := hx
    rw [ENNReal.tendsto_nhds_zero] at hnt
    push Not at hnt
    obtain ⟨ε, hε, hfreq⟩ := hnt
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
    calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ < ε := hk
      _ < _ := hρ
  · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)
/-- **Upper density theorem** (Simon Ch. 1, 3.6 with Remark 3.7(2), via 3.3 with the crude
covering constant `6ⁿ`; chapter-01.txt lines 602–721).  If `μ` is finite on compact subsets of
`ℝᴾ` and `A ⊆ ℝᴾ` is Borel, then for `Hⁿ`-a.e. `x ∉ A`, `μ(A ∩ B_ρ(x)) / (ωₙ ρⁿ) → 0` as `ρ ↓ 0`.
Vitali's lemma (factor `2`, enlarged radius `3ρ`) and separability give `t · μH[n](E) ≤ 6ⁿ μ(G)`
whenever each `x ∈ E` has arbitrarily small `ρ` with `t ρⁿ ≤ μ(G ∩ B̄_ρ(x))`.  For Borel `S` with
`μ(S) < ∞`, taking `G = S \ F` for a closed `F ⊆ S` with `μ(S \ F)` small (weak regularity of
`μ⌞S`) makes every threshold set `{x ∉ S : μ(S ∩ B̄_ρ(x)) > t ρⁿ frequently as ρ ↓ 0}`
`μH[n]`-null, hence `Hⁿ`-null.  The general case applies this to `S = A ∩ B_j(0)`, which agrees
with `A` near `x` once `j > |x| + 1`. -/
theorem Submission.idtp_dema_upper_density_zero : ∀ (P n : ℕ) (μ : Measure (Euclid P)) (A : Set (Euclid P)), MeasurableSet A → (∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ A → Tendsto (fun ρ : ℝ => μ (A ∩ ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0) := by
  intro P n μ A hA hfin
  -- Step 1, Vitali selection (Simon 1.3.4).
  have vitali : ∀ (E : Set (Euclid P)) (p : Euclid P → ℝ → Prop) (δ : ℝ),
      (∀ x ∈ E, ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧ p x ρ) →
      ∃ u : Set (Euclid P × ℝ), u.Countable ∧ (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) := by
    intro E p δ hE
    obtain ⟨u, huT, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun a : Euclid P × ℝ => closedBall a.1 a.2)
      {a : Euclid P × ℝ | a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < δ ∧ p a.1 a.2} (fun a => a.2) 2 (by norm_num)
      (fun a ha => ha.2.1.le) δ (fun a ha => ha.2.2.1.le)
      (fun a ha => nonempty_closedBall.2 ha.2.1.le)
    refine ⟨u, ?_, fun a ha => huT ha, hdisj, ?_⟩
    · apply hdisj.countable_of_nonempty_interior
      intro a ha
      refine ⟨a.1, interior_mono ball_subset_closedBall ?_⟩
      rw [isOpen_ball.interior_eq]
      exact mem_ball_self (huT ha).2.1
    · intro x hx
      obtain ⟨ρ, hρ0, hρδ, hp⟩ := hE x hx
      obtain ⟨b, hbu, ⟨w, hw1, hw2⟩, hle⟩ := hcov (x, ρ) ⟨hx, hρ0, hρδ, hp⟩
      refine mem_iUnion₂.2 ⟨b, hbu, ?_⟩
      rw [mem_closedBall]
      have h1 : dist w x ≤ ρ := hw1
      have h2 : dist w b.1 ≤ b.2 := hw2
      have hle' : ρ ≤ 2 * b.2 := hle
      calc dist x b.1 ≤ dist x w + dist w b.1 := dist_triangle _ _ _
        _ ≤ ρ + b.2 := add_le_add (by rw [dist_comm]; exact h1) h2
        _ ≤ 3 * b.2 := by linarith
  -- Step 2, comparison (Simon 1.3.3 with the crude constant 6 ^ n).
  have comparison : ∀ (t : ℝ≥0∞) (E G : Set (Euclid P)), t ≠ 0 → t ≠ ∞ → MeasurableSet G →
      (∀ x ∈ E, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
        t * ENNReal.ofReal ρ ^ n ≤ μ (G ∩ closedBall x ρ)) →
      t * μH[(n : ℝ)] E ≤ 6 ^ n * μ G := by
    intro t E G ht0 httop hG hE
    have hfam : ∀ j : ℕ, ∃ u : Set (Euclid P × ℝ), u.Countable ∧
        (∀ a ∈ u, a.1 ∈ E ∧ 0 < a.2 ∧ a.2 < 1 / ((j : ℝ) + 1) ∧
          t * ENNReal.ofReal a.2 ^ n ≤ μ (G ∩ closedBall a.1 a.2)) ∧
        u.PairwiseDisjoint (fun a => closedBall a.1 a.2) ∧
        E ⊆ ⋃ a ∈ u, closedBall a.1 (3 * a.2) :=
      fun j => vitali E (fun c ρ => t * ENNReal.ofReal ρ ^ n ≤ μ (G ∩ closedBall c ρ))
        (1 / ((j : ℝ) + 1)) (fun x hx => hE x hx _ (by positivity))
    choose u hucount hu hdisj hcover using hfam
    have : ∀ j, Countable (u j) := fun j => (hucount j).to_subtype
    have hsum : ∀ j, t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n ≤ μ G := by
      intro j
      rw [← ENNReal.tsum_mul_left]
      calc ∑' a : u j, t * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n
          ≤ ∑' a : u j, μ (G ∩ closedBall (a : Euclid P × ℝ).1 (a : Euclid P × ℝ).2) :=
            ENNReal.tsum_le_tsum fun a => (hu j a a.2).2.2.2
        _ = μ (⋃ a ∈ u j, G ∩ closedBall a.1 a.2) :=
            (measure_biUnion (hucount j) ((hdisj j).mono fun a => inter_subset_right)
              fun a _ => hG.inter measurableSet_closedBall).symm
        _ ≤ μ G := measure_mono (iUnion₂_subset fun a _ => inter_subset_left)
    have hdiam : ∀ j (a : u j), ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
        ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) := by
      intro j a
      apply ediam_le_of_forall_dist_le
      intro y hy z hz
      rw [mem_closedBall] at hy hz
      calc dist y z ≤ dist y (a : Euclid P × ℝ).1 + dist z (a : Euclid P × ℝ).1 :=
            dist_triangle_right _ _ _
        _ ≤ 6 * (a : Euclid P × ℝ).2 := by linarith
    have hterm : ∀ j, t * ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μ G := by
      intro j
      calc t * ∑' a : u j, ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ)
          ≤ t * ∑' a : u j, 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
            gcongr with a
            rw [ENNReal.rpow_natCast]
            calc ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ n
                ≤ ENNReal.ofReal (6 * (a : Euclid P × ℝ).2) ^ n := by gcongr; exact hdiam j a
              _ = 6 ^ n * ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n := by
                rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 6 by norm_num), mul_pow]
                norm_num
        _ = 6 ^ n * (t * ∑' a : u j, ENNReal.ofReal (a : Euclid P × ℝ).2 ^ n) := by
            rw [ENNReal.tsum_mul_left]; ring
        _ ≤ 6 ^ n * μ G := by gcongr; exact hsum j
    have hH := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := Euclid P)
      (ι := fun j => (u j)) (n : ℝ) E (l := atTop)
      (fun j : ℕ => ENNReal.ofReal (6 * (1 / ((j : ℝ) + 1))))
      (by
        rw [← ENNReal.ofReal_zero]
        apply ENNReal.tendsto_ofReal
        have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using this.const_mul 6)
      (fun j a => closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2))
      (Eventually.of_forall fun j a => (hdiam j a).trans (ENNReal.ofReal_le_ofReal (by
        have := (hu j a a.2).2.2.1
        linarith)))
      (Eventually.of_forall fun j x hx => by
        obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hcover j hx)
        exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
    have hbound : ∀ j, ∑' a : u j,
        ediam (closedBall (a : Euclid P × ℝ).1 (3 * (a : Euclid P × ℝ).2)) ^ (n : ℝ) ≤
          6 ^ n * μ G / t := by
      intro j
      rw [ENNReal.le_div_iff_mul_le (Or.inl ht0) (Or.inl httop), mul_comm]
      exact hterm j
    have hlim : μH[(n : ℝ)] E ≤ 6 ^ n * μ G / t :=
      hH.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
    calc t * μH[(n : ℝ)] E ≤ t * (6 ^ n * μ G / t) := by gcongr
      _ = 6 ^ n * μ G := ENNReal.mul_div_cancel ht0 httop
  -- Step 3, the finite case (Simon 1.3.6).
  have finite_case : ∀ S : Set (Euclid P), MeasurableSet S → μ S ≠ ∞ →
      ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∉ S →
        Tendsto (fun ρ : ℝ => μ (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
    intro S hS hSfin
    have threshold : ∀ t : ℝ≥0∞, t ≠ 0 → t ≠ ∞ →
        μHE[n] {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
          t < μ (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} = 0 := by
      intro t ht0 httop
      set N := {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
        t < μ (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n} with hN
      have key : ∀ ε : ℝ≥0∞, ε ≠ 0 → μH[(n : ℝ)] N < ε := by
        intro ε hε
        have : IsFiniteMeasure (μ.restrict S) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact hSfin.lt_top⟩
        have : (μ.restrict S).WeaklyRegular :=
          Measure.WeaklyRegular.of_pseudoMetrizableSpace_of_isFiniteMeasure _
        have hpos : t * ε / 6 ^ n ≠ 0 := by
          apply ENNReal.div_ne_zero.2
          exact ⟨mul_ne_zero ht0 hε, ENNReal.pow_ne_top (by norm_num)⟩
        obtain ⟨F, hFS, hFc, hFlt⟩ := hS.exists_isClosed_sdiff_lt
          (μ := μ.restrict S)
          (by rw [Measure.restrict_apply hS, inter_self]; exact hSfin) hpos
        have hG : MeasurableSet (S \ F) := hS.diff hFc.measurableSet
        have hμG : μ (S \ F) < t * ε / 6 ^ n := by
          rwa [Measure.restrict_apply hG, inter_eq_left.2 sdiff_subset] at hFlt
        have hhyp : ∀ x ∈ N, ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ρ < δ ∧
            t * ENNReal.ofReal ρ ^ n ≤ μ ((S \ F) ∩ closedBall x ρ) := by
          intro x hx δ hδ
          obtain ⟨hxS, hfreq⟩ := hx
          have hxF : x ∉ F := fun h => hxS (hFS h)
          obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl x hxF
          have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (min δ (r₁ / 2)) :=
            Ioo_mem_nhdsGT (by positivity)
          obtain ⟨ρ, hρq, hρ⟩ := (hfreq.and_eventually hev).exists
          refine ⟨ρ, hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _), ?_⟩
          have hρpos : ENNReal.ofReal ρ ^ n ≠ 0 :=
            pow_ne_zero _ (ENNReal.ofReal_pos.2 hρ.1).ne'
          have hρtop : ENNReal.ofReal ρ ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
          have h1 : t * ENNReal.ofReal ρ ^ n < μ (S ∩ closedBall x ρ) :=
            (ENNReal.lt_div_iff_mul_lt (Or.inl hρpos) (Or.inl hρtop)).1 hρq
          have h2 : S ∩ closedBall x ρ = (S \ F) ∩ closedBall x ρ := by
            ext y
            constructor
            · rintro ⟨hyS, hyB⟩
              refine ⟨⟨hyS, fun hyF => hball ?_ hyF⟩, hyB⟩
              rw [mem_ball]
              have := mem_closedBall.1 hyB
              have := hρ.2
              have := min_le_right δ (r₁ / 2)
              linarith
            · rintro ⟨⟨hyS, _⟩, hyB⟩
              exact ⟨hyS, hyB⟩
          rw [← h2]
          exact h1.le
        have hcomp := comparison t N (S \ F) ht0 httop hG hhyp
        have h6 : (6 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
        have h6' : (6 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
        have hlt : t * μH[(n : ℝ)] N < t * ε := by
          calc t * μH[(n : ℝ)] N ≤ 6 ^ n * μ (S \ F) := hcomp
            _ < 6 ^ n * (t * ε / 6 ^ n) := ENNReal.mul_lt_mul_right h6 h6' hμG
            _ = t * ε := ENNReal.mul_div_cancel h6 h6'
        exact (ENNReal.mul_lt_mul_iff_right ht0 httop).1 hlt
      have hH : μH[(n : ℝ)] N = 0 := by
        by_contra h
        exact lt_irrefl _ (key _ h)
      rw [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, hH, smul_zero]
    rw [ae_iff]
    apply measure_mono_null (t := ⋃ k : ℕ, {x : Euclid P | x ∉ S ∧ ∃ᶠ ρ in 𝓝[>] (0 : ℝ),
      ((k : ℝ≥0∞) + 1)⁻¹ < μ (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n})
    · intro x hx
      simp only [mem_ofPred_eq, Classical.not_imp] at hx
      obtain ⟨hxS, hnt⟩ := hx
      rw [ENNReal.tendsto_nhds_zero] at hnt
      push Not at hnt
      obtain ⟨ε, hε, hfreq⟩ := hnt
      obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      refine mem_iUnion.2 ⟨k, hxS, hfreq.mono fun ρ hρ => ?_⟩
      calc ((k : ℝ≥0∞) + 1)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
        _ < ε := hk
        _ < _ := hρ
    · exact measure_iUnion_null fun k => threshold _ (by simp) (by simp)
  -- Step 4, localization (Simon 1.3.7(2)).
  have hloc : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ j : ℕ, x ∉ A ∩ ball 0 j →
      Tendsto (fun ρ : ℝ => μ ((A ∩ ball 0 j) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) :=
    ae_all_iff.2 fun j => finite_case _ (hA.inter measurableSet_ball)
      (ne_top_of_le_ne_top (hfin _ (isCompact_closedBall 0 j))
        (measure_mono (inter_subset_right.trans ball_subset_closedBall)))
  -- Step 0/5, normalization and open balls.
  have hω0 : unitBallVolume n ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hωtop : unitBallVolume n ≠ ∞ := measure_ball_lt_top.ne
  filter_upwards [hloc] with x hx hxA
  obtain ⟨j, hj⟩ := exists_nat_gt (‖x‖ + 1)
  have hcl := hx j (fun h => hxA h.1)
  have hlim : Tendsto (fun ρ : ℝ => (unitBallVolume n)⁻¹ *
      (μ ((A ∩ ball 0 j) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hcl (Or.inr (ENNReal.inv_ne_top.2 hω0))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  filter_upwards [hev] with ρ hρ
  have hsub : A ∩ ball x ρ ⊆ (A ∩ ball 0 j) ∩ closedBall x ρ := by
    rintro y ⟨hyA, hyB⟩
    refine ⟨⟨hyA, ?_⟩, ball_subset_closedBall hyB⟩
    rw [mem_ball, dist_zero_right]
    have h1 : dist y x < ρ := hyB
    have h2 : ‖y‖ ≤ ‖x‖ + dist y x := by
      have := norm_le_norm_add_norm_sub' y x
      rw [dist_eq_norm]; linarith [norm_sub_rev y x]
    linarith [hρ.2]
  have hle : μ (A ∩ ball x ρ) ≤ μ ((A ∩ ball 0 j) ∩ closedBall x ρ) := measure_mono hsub
  calc μ (A ∩ ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))
      = (unitBallVolume n)⁻¹ * (μ (A ∩ ball x ρ) / ENNReal.ofReal ρ ^ n) := by
        rw [ENNReal.ofReal_pow hρ.1.le, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop), mul_assoc]
    _ ≤ (unitBallVolume n)⁻¹ * (μ ((A ∩ ball 0 j) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) := by
        gcongr

/-- **Upper density theorem for `Hⁿ` off a Borel set of locally finite measure in `U`** (Simon
Ch. 1, Remark 3.7(2); chapter-01.txt lines 705–711).  If `U ⊆ ℝᴾ` is open and `S` is Borel with
`Hⁿ(S ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ U ∖ S`,
`Hⁿ(S ∩ B̄_ρ(x)) / ρⁿ → 0` as `ρ ↓ 0`.  Countably many balls `B_{r_y}(y)` with
`B̄_{r_y}(y) ⊆ U` cover `U` (Lindelöf); the finite-measure version applies to each piece
`S ∩ B_{r_y}(y)`, and near `x ∈ B_{r_y}(y)` the piece agrees with `S`. -/
theorem Submission.regcomp_atl_local_density_zero : ∀ (P n : ℕ) (U S : Set (Euclid P)), IsOpen U → MeasurableSet S → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (S ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ U → x ∉ S → Tendsto (fun ρ : ℝ => μHE[n] (S ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) := by
  intro P n U S hU hS hfin
  -- Step 1, a countable cover of `U` by balls `B(y, r y)` with `B̄(y, r y) ⊆ U`.
  have hr : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U := by
    intro x hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hball⟩
  choose! r hr0 hrU using hr
  obtain ⟨D, hDU, hDc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun y => ball y (r y)) (s := U)
    fun x hx => mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (hr0 x hx))
  -- Steps 2 and 3, the finite-measure theorem on each piece `S ∩ B(y, r y)`, simultaneously
  -- for the countably many `y ∈ D`.
  have hpiece : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ y ∈ D, x ∉ S ∩ ball y (r y) →
      Tendsto (fun ρ : ℝ => μHE[n] (S ∩ ball y (r y) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n)
        (𝓝[>] 0) (𝓝 0) := by
    rw [ae_ball_iff hDc]
    intro y hy
    apply Submission.regcomp_atl_upper_density_zero P n _ (hS.inter measurableSet_ball)
    exact ne_top_of_le_ne_top (hfin _ (isCompact_closedBall y (r y)) (hrU y (hDU hy)))
      (measure_mono (inter_subset_inter_right S ball_subset_closedBall))
  -- Step 4, localization: for small `ρ`, `B̄(x, ρ) ⊆ B(y, r y)`, so the piece agrees with `S`.
  filter_upwards [hpiece] with x hx hxU hxS
  obtain ⟨y, hyD, hxy⟩ := mem_iUnion₂.1 (hcov hxU)
  obtain ⟨ε, hε, hεy⟩ := Metric.isOpen_iff.1 isOpen_ball x hxy
  refine (hx y hyD fun h => hxS h.1).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with ρ hρ
  rw [inter_assoc, inter_eq_right.2 ((closedBall_subset_ball hρ.2).trans hεy)]
/-- Comparison of blow-up integrals (proof of Simon 3.1.6): for Borel `A ⊆ B`, `r > 0` and a
continuous `f` with `|f| ≤ C` vanishing off `B̄_R(0)`,
`|∫_{η_{x,r}(B)} f dHⁿ − ∫_{η_{x,r}(A)} f dHⁿ| ≤ C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0))`.  Since `η_{x,r}` is
injective, `η_{x,r}(B)` is the disjoint union of `η_{x,r}(A)` and `η_{x,r}(B \ A)`, both Borel
(`η_{x,r}(T)` is the preimage of `T` under `y ↦ x + ry`); the difference of the integrals is the
integral over `η_{x,r}(B \ A)`, which equals the integral over `η_{x,r}(B \ A) ∩ B̄_R(0)`. -/
theorem Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r R C : ℝ) (f : Euclid P → ℝ), Continuous f → MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ → (∀ y : Euclid P, ‖f y‖ ≤ C) → (∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0) → ‖(∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]‖ ≤ C * (μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R)).toReal := by
  intro P n A B x r R C f hf hA hB hAB hr hfin hC hzero
  -- Step 1: `η = η_{x,r}` is injective
  have hinj : Injective (Poincare.SimonGMT.Chapter03.blowUpMap x r : Euclid P → Euclid P) := by
    intro z w h
    have h' : z - x = w - x :=
      smul_right_injective (Euclid P) (inv_ne_zero hr.ne') h
    simpa using h'
  -- Step 2: `η(T) = g⁻¹(T)` for `g y = x + r • y`, so `η` maps Borel sets to Borel sets
  have himage : ∀ T : Set (Euclid P),
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' T = (fun y : Euclid P => x + r • y) ⁻¹' T := by
    intro T
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, mul_inv_cancel₀ hr.ne'] using hz
    · intro hy
      refine ⟨x + r • y, hy, ?_⟩
      simp [Poincare.SimonGMT.Chapter03.blowUpMap, smul_smul, inv_mul_cancel₀ hr.ne']
  have hmeas : ∀ T : Set (Euclid P), MeasurableSet T →
      MeasurableSet (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) := by
    intro T hT
    rw [himage T]
    exact (by fun_prop : Continuous fun y : Euclid P => x + r • y).measurable hT
  -- Step 3: `f` is integrable on `η(T)` for Borel `T ⊆ B`
  have hint : ∀ T : Set (Euclid P), MeasurableSet T → T ⊆ B →
      IntegrableOn f (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) μHE[n] := by
    intro T hT hTB
    have hfinT : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T ∩ closedBall 0 R) ≠ ∞ :=
      ne_top_of_le_ne_top hfin (measure_mono (inter_subset_inter_left _ (image_mono hTB)))
    exact (Measure.integrableOn_of_bounded hfinT hf.aestronglyMeasurable
      (Eventually.of_forall hC)).of_forall_sdiff_eq_zero (hmeas T hT)
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 4: `∫_{η(B)} f − ∫_{η(A)} f = ∫_{η(B∖A)} f`
  have hBA : MeasurableSet (B \ A) := hB.diff hA
  have hunion : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' B, f y ∂μHE[n] =
      (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' A, f y ∂μHE[n]) +
        ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] := by
    rw [← setIntegral_union ((disjoint_image_iff hinj).mpr disjoint_sdiff_right) (hmeas _ hBA)
      (hint A hA hAB) (hint _ hBA sdiff_subset), ← image_union, union_sdiff_cancel hAB]
  -- Step 5: localization to `B̄_R(0)`
  have hloc : ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A), f y ∂μHE[n] =
      ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R, f y ∂μHE[n] :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hmeas _ hBA) inter_subset_left
      fun y hy => hzero y fun h => hy.2 ⟨hy.1, h⟩
  -- Step 6: the estimate
  have hfinS : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' (B \ A) ∩ closedBall 0 R) < ∞ :=
    (measure_mono (inter_subset_inter_left _ (image_mono sdiff_subset))).trans_lt hfin.lt_top
  rw [hunion, add_sub_cancel_left, hloc, ← measureReal_def]
  exact norm_setIntegral_le_of_norm_le_const hfinS fun y _ => hC y
/-- Rescaling a vanishing `n`-density quotient (the final limit in the proof of Simon 3.1.6): if
`g(ρ)/ρⁿ → 0` as `ρ ↓ 0` and `R > 0`, then `r⁻ⁿ g(rR) → 0` as `r ↓ 0`.  The substitution
`ρ = rR` maps `𝓝[>] 0` to itself, multiplying by the finite constant `Rⁿ` keeps the limit `0`,
and `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)` for `r > 0`. -/
theorem Submission.regcomp_atl_pc_density_rescale_tendsto : ∀ (n : ℕ) (g : ℝ → ℝ≥0∞) (R : ℝ), 0 < R → Tendsto (fun ρ : ℝ => g ρ / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → Tendsto (fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R)) (𝓝[>] 0) (𝓝 0) := by
  intro n g R hR hg
  -- Step 1: `r ↦ r * R` maps `𝓝[>] 0` to `𝓝[>] 0`
  have hmap : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_mul_const R).tendsto' 0 0 (zero_mul R)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      exact mul_pos hr hR
  -- Step 2: `g (r * R) / ofReal (r * R) ^ n → 0`
  have hcomp : Tendsto (fun r : ℝ => g (r * R) / ENNReal.ofReal (r * R) ^ n) (𝓝[>] 0) (𝓝 0) :=
    hg.comp hmap
  -- Step 3: multiplication by the finite constant `ofReal R ^ n`
  have hbtop : ENNReal.ofReal R ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hconst : Tendsto
      (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hcomp (Or.inr hbtop)
    rwa [mul_zero] at h
  -- Step 4: for `r > 0`, `Rⁿ · g(rR)/(rR)ⁿ = r⁻ⁿ g(rR)`
  have heq : (fun r : ℝ => ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n))
      =ᶠ[𝓝[>] 0] fun r : ℝ => (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have ha0 : ENNReal.ofReal r ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hr).ne' n
    have hatop : ENNReal.ofReal r ^ n ≠ ∞ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
    have hb0 : ENNReal.ofReal R ^ n ≠ 0 := ENNReal.pow_ne_zero (ENNReal.ofReal_pos.mpr hR).ne' n
    calc ENNReal.ofReal R ^ n * (g (r * R) / ENNReal.ofReal (r * R) ^ n)
        = ENNReal.ofReal R ^ n *
            ((ENNReal.ofReal r ^ n)⁻¹ * (ENNReal.ofReal R ^ n)⁻¹ * g (r * R)) := by
          rw [ENNReal.ofReal_mul hr.le, mul_pow, ENNReal.div_eq_inv_mul,
            ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
      _ = ENNReal.ofReal R ^ n * (ENNReal.ofReal R ^ n)⁻¹ *
            ((ENNReal.ofReal r ^ n)⁻¹ * g (r * R)) := by ring
      _ = (ENNReal.ofReal r)⁻¹ ^ n * g (r * R) := by
          rw [ENNReal.mul_inv_cancel hb0 hbtop, one_mul, ENNReal.inv_pow]
  -- Step 5: the two functions agree eventually along `𝓝[>] 0`
  exact hconst.congr' heq
/-- Asymptotically equal blow-up integrals give equal approximate tangent spaces (Simon Ch. 3,
Definition 1.4; last step of the proof of 3.1.6).  With `η_r = η_{x,r}`, `I(r) = ∫_{η_r(M)} f dHⁿ`,
`I'(r) = ∫_{η_r(M')} f dHⁿ` and `I(r) − I'(r) → 0` as `r ↓ 0` for every `f ∈ C_c(ℝᴾ)`:
`I' = I − (I − I')` and `I = I' + (I − I')` have the same limit `∫_Q f dHⁿ` as `I`, resp. `I'`,
while the condition `dim Q = n` does not involve `M`, `M'`. -/
theorem Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P), (∀ f : CompactlySupportedContinuousMap (Euclid P) ℝ, Tendsto (fun r : ℝ => (∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M, f y ∂μHE[n]) - ∫ y in Poincare.SimonGMT.Chapter03.blowUpMap x r '' M', f y ∂μHE[n]) (𝓝[>] 0) (𝓝 0)) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n M x Q ↔ HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x hD Q
  constructor
  · -- (⇒) `I' = I − (I − I') → L − 0 = L`
    rintro ⟨hQ, hM⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM f).sub (hD f)
    rw [sub_zero] at h
    exact h.congr fun r => sub_sub_cancel _ _
  · -- (⇐) `I = I' + (I − I') → L + 0 = L`
    rintro ⟨hQ, hM'⟩
    refine ⟨hQ, fun f => ?_⟩
    have h := (hM' f).add (hD f)
    rw [add_zero] at h
    exact h.congr fun r => add_sub_cancel _ _
/-- Scaling of `Hⁿ` under the blow-up `η_{x,r}(z) = r⁻¹(z − x)`, `r > 0` (proof of Simon 3.1.6):
`Hⁿ(η_{x,r}(S) ∩ B̄_R(0)) = r⁻ⁿ Hⁿ(S ∩ B̄_{rR}(x))`.  Since `‖η_{x,r}(z)‖ = r⁻¹‖z − x‖`, the left
side is `Hⁿ(η_{x,r}(S ∩ B̄_{rR}(x)))`; `η_{x,r}` is the homothety of centre `x` and ratio `r⁻¹`
followed by the translation by `−x`, which preserves `Hⁿ`, while the homothety multiplies it by
`‖r⁻¹‖₊ⁿ = r⁻ⁿ`. -/
theorem Submission.regcomp_atl_blowUp_measure_scaling : ∀ (P n : ℕ) (x : Euclid P) (r R : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R) = (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] (S ∩ closedBall x (r * R)) := by
  intro P n x r R S hr
  -- `‖η(z)‖ = r⁻¹‖z − x‖`
  have hnorm : ∀ z : Euclid P,
      ‖Poincare.SimonGMT.Chapter03.blowUpMap x r z‖ = r⁻¹ * ‖z - x‖ := by
    intro z
    rw [Poincare.SimonGMT.Chapter03.blowUpMap, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)]
  -- Step 1: `η(S) ∩ B̄(0, R) = η(S ∩ B̄(x, rR))`
  have hset : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S ∩ closedBall 0 R =
      Poincare.SimonGMT.Chapter03.blowUpMap x r '' (S ∩ closedBall x (r * R)) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hy⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      rw [mem_closedBall_zero_iff, hnorm] at hy
      rw [mem_closedBall, dist_eq_norm]
      calc ‖z - x‖ = r * (r⁻¹ * ‖z - x‖) := by field_simp
        _ ≤ r * R := mul_le_mul_of_nonneg_left hy hr.le
    · rintro ⟨z, ⟨hz, hzx⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      rw [mem_closedBall, dist_eq_norm] at hzx
      rw [mem_closedBall_zero_iff, hnorm]
      calc r⁻¹ * ‖z - x‖ ≤ r⁻¹ * (r * R) := mul_le_mul_of_nonneg_left hzx (inv_pos.mpr hr).le
        _ = R := by field_simp
  -- Step 2: `η = τ ∘ h` with `h = homothety x r⁻¹` and `τ y = y + (-x)`
  have hcomp : Poincare.SimonGMT.Chapter03.blowUpMap x r =
      (fun y : Euclid P => y + -x) ∘ AffineMap.homothety x r⁻¹ := by
    funext z
    simp [Poincare.SimonGMT.Chapter03.blowUpMap, AffineMap.homothety_apply]
  -- Step 3: `μ(η(T)) = (ENNReal.ofReal r)⁻¹ ^ n * μ(T)`
  have hscale : ∀ T : Set (Euclid P), μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' T) =
      (ENNReal.ofReal r)⁻¹ ^ n * μHE[n] T := by
    intro T
    rw [hcomp, Set.image_comp, (isometry_add_right (-x)).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_homothety_image n x (inv_ne_zero hr.ne') T, ENNReal.smul_def,
      smul_eq_mul, ENNReal.coe_pow, nnnorm_inv, ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr hr.ne'),
      Real.nnnorm_of_nonneg hr.le, ← ENNReal.ofReal_eq_coe_nnreal hr.le]
  -- Step 4: conclusion
  rw [hset, hscale]

/-- Locality of approximate tangent spaces (Simon 3.1.5(2), from the proof of 3.1.6 "⇒"): if
`A ⊆ B` are Borel, `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞` and `Hⁿ((B \ A) ∩ B̄_ρ(x))/ρⁿ → 0` as `ρ ↓ 0`, then
`B` and `A` have the same approximate tangent spaces at `x`.  For `f ∈ C_c(ℝᴾ)` with `|f| ≤ C`
and `f = 0` off `B̄_R(0)`, and `0 < r < r₀/R`, the integrals of `f` over `η_{x,r}(B)` and
`η_{x,r}(A)` differ by at most `C Hⁿ(η_{x,r}(B \ A) ∩ B̄_R(0)) = C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))`,
which tends to `0` as `r ↓ 0`. -/
theorem Submission.regcomp_atl_tangent_iff_of_density_zero : ∀ (P n : ℕ) (A B : Set (Euclid P)) (x : Euclid P) (r₀ : ℝ), MeasurableSet A → MeasurableSet B → A ⊆ B → 0 < r₀ → μHE[n] (B ∩ closedBall x r₀) ≠ ∞ → Tendsto (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ) / ENNReal.ofReal ρ ^ n) (𝓝[>] 0) (𝓝 0) → ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n A B x r₀ hA hB hAB hr₀ hfin hdens
  refine Submission.regcomp_atl_pc_tangent_iff_of_integral_sub_tendsto P n B A x fun f => ?_
  -- `‖f‖ ≤ C` everywhere, and `f = 0` off `B̄_R(0)` with `R > 0`
  obtain ⟨C, hC⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  obtain ⟨R₁, hR₁⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : Euclid P)
  set R := max R₁ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right R₁ 1)
  have hf0 : ∀ y : Euclid P, y ∉ closedBall (0 : Euclid P) R → f y = 0 := by
    intro y hy
    by_contra hne
    exact hy (closedBall_subset_closedBall (le_max_left R₁ 1) (hR₁ (subset_tsupport f hne)))
  -- the bound `C r⁻ⁿ Hⁿ((B \ A) ∩ B̄_{rR}(x))` tends to `0` as `r ↓ 0`
  have hlim : Tendsto (fun r : ℝ => C * ((ENNReal.ofReal r)⁻¹ ^ n *
      μHE[n] ((B \ A) ∩ closedBall x (r * R))).toReal) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (Submission.regcomp_atl_pc_density_rescale_tendsto n
        (fun ρ : ℝ => μHE[n] ((B \ A) ∩ closedBall x ρ)) R hR hdens)
    rw [ENNReal.toReal_zero] at h
    have h' := h.const_mul C
    rw [mul_zero] at h'
    exact h'
  refine squeeze_zero_norm' ?_ hlim
  -- for `0 < r < r₀ / R` the fixed-scale comparison applies, and the scaling identity rewrites
  -- its bound
  filter_upwards [Ioo_mem_nhdsGT (div_pos hr₀ hR)] with r hr
  have hrR : r * R ≤ r₀ := ((lt_div_iff₀ hR).1 hr.2).le
  have hBfin : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' B ∩ closedBall 0 R) ≠ ∞ := by
    rw [Submission.regcomp_atl_blowUp_measure_scaling P n x r R B hr.1]
    exact ENNReal.mul_ne_top
      (ENNReal.pow_ne_top (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr.1).ne'))
      (ne_top_of_le_ne_top hfin
        (measure_mono (inter_subset_inter_right B (closedBall_subset_closedBall hrR))))
  have key := Submission.regcomp_atl_pc_blowUp_setIntegral_sub_le P n A B x r R C f
    (map_continuous f) hA hB hAB hr.1 hBfin hC hf0
  rwa [Submission.regcomp_atl_blowUp_measure_scaling P n x r R (B \ A) hr.1] at key

/-- **Locality of approximate tangent spaces** (Simon Ch. 3, Remark 1.5(2); proof of 3.1.6 "⇒",
chapter-03.txt lines 113–143).  If `U ⊆ ℝᴾ` is open and `A ⊆ B ⊆ U` are Borel with
`Hⁿ(B ∩ K) < ∞` for every compact `K ⊆ U`, then for `Hⁿ`-a.e. `x ∈ A`, `B` and `A` have the same
approximate tangent spaces at `x`.  `D = B \ A` is Borel with `Hⁿ(D ∩ K) < ∞` for compact `K ⊆ U`,
so by the upper density theorem `Hⁿ(D ∩ B̄_ρ(x))/ρⁿ → 0` as `ρ ↓ 0` for `Hⁿ`-a.e. `x ∈ U ∖ D`,
hence for `Hⁿ⌞A`-a.e. `x`.  At such `x ∈ A ⊆ U`, a closed ball `B̄_{r₀}(x) ⊆ U` is compact, so
`Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`, and the blow-ups of `B` and `A` at `x` have asymptotically equal
integrals. -/
theorem Submission.dor_lmb_approx_tangent_locality : ∀ (P n : ℕ) (U A B : Set (Euclid P)), IsOpen U → MeasurableSet A → MeasurableSet B → A ⊆ B → B ⊆ U → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (B ∩ K) ≠ ∞) → ∀ᵐ x ∂(μHE[n].restrict A), ∀ Q : Submodule ℝ (Euclid P), HasApproximateTangentSpaceAt n B x Q ↔ HasApproximateTangentSpaceAt n A x Q := by
  intro P n U A B hU hA hB hAB hBU hfin
  -- Steps 1–3: `D = B \ A` has finite measure on compact subsets of `U`, so its `n`-density
  -- vanishes at `Hⁿ`-a.e. point of `U ∖ D`
  have hdens := Submission.regcomp_atl_local_density_zero P n U (B \ A) hU (hB.diff hA)
    fun K hK hKU => ne_top_of_le_ne_top (hfin K hK hKU)
      (measure_mono (inter_subset_inter_left K sdiff_subset))
  -- Step 7: `Hⁿ⌞A`-a.e. `x` lies in `A`, hence in `U` and outside `D`
  filter_upwards [ae_restrict_of_ae hdens, ae_restrict_mem hA] with x hx hxA
  have hxU : x ∈ U := hBU (hAB hxA)
  -- Step 4: a closed ball `B̄_{r₀}(x) ⊆ U` is compact, so `Hⁿ(B ∩ B̄_{r₀}(x)) < ∞`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  have hsub : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  -- Steps 5–6: comparison of the blow-up integrals of `B` and `A` at `x`
  exact Submission.regcomp_atl_tangent_iff_of_density_zero P n A B x (ε / 2) hA hB hAB
    (half_pos hε) (hfin _ (isCompact_closedBall x (ε / 2)) hsub) (hx hxU fun h => h.2 hxA)

/-- **Restriction of an integer multiplicity current to a Borel set** (Simon Ch. 6, 4.5(2); e.g.
`Rⱼ⌞W_α` and `T⌞W_α` in the proof of 7.2.4): for a triple `R = (M, θ, ξ)` in `U` and Borel `A`,
`R' = (M ∩ A, θ, ξ)` is again a triple in `U`, it represents a current `S = τ(M, θ, ξ)⌞A` in
`𝒟ₙ(U)`, and `μ_{R'} = μ_R⌞A`.

As `θ ≥ 1` on `M`, `Hⁿ(M ∩ K) < ∞` for compact `K ⊆ U`.  So tangent locality for `M ∩ A ⊆ M`
gives `T_x(M ∩ A) = T_xM` for `Hⁿ`-a.e. `x ∈ M ∩ A`, and `ξ` still orients `M ∩ A`.  The triple
`R'` defines a current by Simon 6.3.1, and `(Hⁿ⌞(M ∩ A))θ = ((Hⁿ⌞M)θ)⌞A` because restriction to
the Borel set `A` commutes with taking densities. -/
theorem Submission.dor_lmb_imrep_restrict_current : ∀ (P n : ℕ) (U A : Set (Euclid P)) (R : IMRep U n), IsOpen U → MeasurableSet A → ∃ (S : GeometricCurrentOn U n) (R' : IMRep U n), R'.Represents S ∧ R'.carrier = R.carrier ∩ A ∧ R'.mult = R.mult ∧ R'.orient = R.orient ∧ R'.measure = R.measure.restrict A := by
  intro P n U A R hU hA
  -- Step 2(a): `Hⁿ(M ∩ K) < ∞` for compact `K ⊆ U`
  have hfin : ∀ K : Set (Euclid P), IsCompact K → K ⊆ U → μHE[n] (R.carrier ∩ K) ≠ ∞ :=
    fun K hK hKU => (Submission.rsd_imrep_compact_measure_ne_top P n U R K hK hKU).1
  -- Step 2(b): `M ∩ A` and `M` have the same approximate tangent spaces `Hⁿ`-a.e. on `M ∩ A`
  have hloc := Submission.dor_lmb_approx_tangent_locality P n U (R.carrier ∩ A) R.carrier hU
    (R.measurableSet_carrier.inter hA) R.measurableSet_carrier inter_subset_left
    R.carrier_subset hfin
  -- Steps 1 and 2(c): `R' = (M ∩ A, θ, ξ)` is a triple in `U`
  obtain ⟨R', hc, hm, ho⟩ := Submission.regcomp_rim_sub_imrep P n U (R.carrier ∩ A) R R.mult
    (R.measurableSet_carrier.inter hA) inter_subset_left R.measurable_mult
    (fun x hx => R.mult_pos x hx.1) (fun x _ => le_rfl) (hloc.mono fun x hx Q hQ => (hx Q).1 hQ)
  -- Step 3: `R'` represents a current `S`
  obtain ⟨S, hS⟩ := Submission.dtc_imrep_current P n U R'
  refine ⟨S, R', hS, hc, hm, ho, ?_⟩
  -- Step 4: `(Hⁿ⌞(M ∩ A))θ = ((Hⁿ⌞M)θ)⌞A`
  simp only [IMRep.measure, hc, hm]
  rw [restrict_withDensity hA, Measure.restrict_restrict hA, inter_comm]

/-- **The blow-up class `𝓜` is locally finite and is `Hⁿ` weighted by its upper density** (Simon
7.3.3, proof of (1), and Remark 3.4: the measures of `𝒯` are `θHⁿ`).  Assume the density theorem
(DEN) for weights `μ_R⌞W`, `W` open, and the blow-up of integer multiplicity representations (BUI).
Let `𝓜` consist of the rescalings `ν^{a,t} = t⁻ⁿ η_{a,t#}(μ_T⌞B_{2r}(z))` (`0 < t ≤ r`,
`|a − z| ≤ r − t`) and of the weights `μ_S` of the limits `S` of blow-ups of `T`.  Then every
`μ ∈ 𝓜` is finite on compact sets, and `μ = Hⁿ⌞(ofReal ∘ dens μ)` for the upper density
`dens μ x = limsup_{ρ↓0} μ(B_ρ(x)) / (ωₙρⁿ)`.  A weight `μ_R = θHⁿ⌞M` is finite on compact subsets
of its domain, as `θ` is locally integrable; and `ν^{a,t}(ℝ^{n+k}) = t⁻ⁿ μ_T(B_{2r}(z)) < ∞`.  By
(DEN) with `W = ℝ^{n+k}`, every locally finite weight is `Hⁿ` weighted by its upper density.  The
`μ_S` are weights, and `ν^{a,t}` is the weight of the blow-up `η_{a,t#}(T⌞B_{2r}(z))`. -/
theorem Submission.dimred_tr_bc_class_finite_density : (∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator (R.carrier ∩ W) (fun y => (R.mult y : ℝ≥0∞)) x))) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → ∀ dens : Measure (Euclid (n + k)) → Euclid (n + k) → ℝ, (∀ (μ : Measure (Euclid (n + k))) (x : Euclid (n + k)), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → (∀ μ ∈ 𝓜, ∀ K : Set (Euclid (n + k)), IsCompact K → μ K ≠ ∞) ∧ (∀ μ ∈ 𝓜, μ = (μHE[n] : Measure (Euclid (n + k))).withDensity (fun x => ENNReal.ofReal (dens μ x))) := by
  intro hDEN hBUI n k ℓ _ U N T hn hU _ _ _ _ _ z r RT 𝓜 _ hball _ h𝓜 dens hdens
  -- Step 1: a weight `μ_R` is finite on compact subsets `K` of the domain of `R`, as
  -- `μ_R(K) = ∫_{M ∩ K} θ dHⁿ`; in particular `μ_T(B_{2r}(z)) ≤ μ_T(B̄_{2r}(z)) < ∞`
  have hcpt : ∀ (V : Set (Euclid (n + k))) (R : IMRep V n) (K : Set (Euclid (n + k))),
      IsCompact K → K ⊆ V → R.measure K ≠ ∞ := by
    intro V R K hK hKV
    rw [IMRep.measure, withDensity_apply _ hK.measurableSet,
      Measure.restrict_restrict hK.measurableSet, inter_comm]
    exact R.locallyIntegrable_mult K hK hKV
  have hW : RT.measure (ball z (2 * r)) ≠ ∞ :=
    ne_top_of_le_ne_top (hcpt U RT _ (isCompact_closedBall z (2 * r)) hball)
      (measure_mono ball_subset_closedBall)
  -- Step 2: property (1); `ν^{a,t}(K) ≤ ν^{a,t}(ℝ^{n+k}) = t⁻ⁿ μ_T(B_{2r}(z))`, and `μ_S` is a
  -- weight in `ℝ^{n+k}`
  have h1 : ∀ μ ∈ 𝓜, ∀ K : Set (Euclid (n + k)), IsCompact K → μ K ≠ ∞ := by
    intro μ hμ K hK
    rcases (h𝓜 μ).1 hμ with ⟨a, t, ht, _, _, rfl⟩ | ⟨_, RS, _, _, _, _, _, _, _, _, _, rfl⟩
    · refine ne_top_of_le_ne_top ?_ (measure_mono (subset_univ K))
      rw [Submission.idtp_fons_cc_ambient_calculus.2.1 (n + k) n _ a t univ ht MeasurableSet.univ,
        preimage_univ, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW
    · exact hcpt univ RS K hK (subset_univ K)
  -- Steps 3–4: (DEN) with `W = ℝ^{n+k}` is the density hypothesis of the density
  -- representation, so a weight finite on compact sets is `Hⁿ⌞(ofReal ∘ dens μ_R)`
  have hrep : ∀ (V : Set (Euclid (n + k))) (R : IMRep V n),
      (∀ K : Set (Euclid (n + k)), IsCompact K → R.measure K ≠ ∞) →
      R.measure = (μHE[n] : Measure (Euclid (n + k))).withDensity
        (fun x => ENNReal.ofReal (dens R.measure x)) := by
    intro V R hfin
    simp only [hdens]
    refine Submission.idtp_fons_cc_density_representation (fun P m V' R' _ hfin' => ?_)
      (n + k) n V R hn hfin
    simpa only [inter_univ] using hDEN P m V' univ R' isOpen_univ fun K hK => by
      rw [inter_univ]
      exact hfin' K hK
  refine ⟨h1, fun μ hμ => ?_⟩
  rcases (h𝓜 μ).1 hμ with ⟨a, t, ht, _, _, hμa⟩ | ⟨_, RS, _, _, _, _, _, _, _, _, _, rfl⟩
  · -- Step 6: `ν^{a,t}` is the weight of the blow-up `η_{a,t#}(T⌞B_{2r}(z))`, by restriction of
    -- `RT` to `B_{2r}(z)` and (BUI)
    obtain ⟨SW, RW, hRW, _, _, _, hRWm⟩ := Submission.dor_lmb_imrep_restrict_current (n + k) n U
      (ball z (2 * r)) RT hU measurableSet_ball
    obtain ⟨R'', _, hR''⟩ := hBUI (n + k) n U SW a t ht RW hRW
    have heq : R''.measure = μ := by
      ext s hs
      rw [hR'' s hs, hμa, Submission.idtp_fons_cc_ambient_calculus.2.1 (n + k) n _ a t s ht hs,
        hRWm]
    rw [← heq]
    exact hrep _ R'' fun K hK => by
      rw [heq]
      exact h1 μ hμ K hK
  · -- Step 5: `μ_S` is a weight in `ℝ^{n+k}`
    exact hrep univ RS (h1 _ hμ)
/-- **Rescalings of the measure class `𝓜`** (Simon 7.3.3, proof of (1), (10):
`η_{x,λ#}𝒯 ⊆ 𝒯` for `0 < λ < 1`, `|x| < 1 − λ`, chapter-07.txt lines 444–472, "by definition one
readily checks"), conditional on the frozen types of `blowup_calculus` and `blowup_imrep`.  Here
`𝓜` consists of the positive-scale weights `ν^{a,t} = t⁻ⁿ η_{a,t#}ν` of `ν = μ_T⌞B_{2r}(z)`
(`0 < t ≤ r`, `|a − z| ≤ r − t`) and of the zero-scale weights `μ_S` of weak limits
`S = lim η_{cᵢ,tᵢ#}T` (`|cᵢ − z| < r − tᵢ`, `tᵢ → 0`, `cᵢ → b`).  For `0 < λ < 1` and
`|y| ≤ 1 − λ`, `λ⁻ⁿ η_{y,λ#}` maps `ν^{a,t}` to `ν^{a+ty,tλ}` (`idtp_fons_cc_ambient_calculus`
(7)) and `μ_S` to the weight of a weak limit of `η_{cᵢ+tᵢy,tᵢλ#}T`
(`dimred_tr_bc_zero_limit_rescale`); the new data are admissible by the triangle inequality
`|c + sy − z| ≤ |c − z| + s(1 − λ)` (`s ≥ 0`). -/
theorem Submission.dimred_tr_bc_class_rescale : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (lam : ℝ), 0 < lam → lam < 1 → ‖y‖ ≤ 1 - lam → ENNReal.ofReal (lam⁻¹ ^ n) • μ.map (dilation y lam) ∈ 𝓜) := by
  intro hBC hBUI n k ℓ _hℓ U N T _hn _hU _hN _hNcl _hmin _hspt _hbd z r RT 𝓜 _hr _hball _hRT h𝓜
    μ hμ y lam hlam0 hlam1 hy
  -- Step 1: the triangle inequality `|c + sy − z| ≤ |c − z| + s|y| ≤ |c − z| + s(1 − λ)`, `s ≥ 0`
  have htri : ∀ (c : Euclid (n + k)) (s : ℝ), 0 ≤ s →
      dist (c + s • y) z ≤ dist c z + s * (1 - lam) := by
    intro c s hs
    calc dist (c + s • y) z = ‖c - z + s • y‖ := by rw [dist_eq_norm, add_sub_right_comm]
      _ ≤ ‖c - z‖ + ‖s • y‖ := norm_add_le _ _
      _ = dist c z + s * ‖y‖ := by rw [dist_eq_norm, norm_smul, Real.norm_of_nonneg hs]
      _ ≤ dist c z + s * (1 - lam) := by gcongr
  rcases (h𝓜 μ).1 hμ with ⟨a, t, ht0, htr, hdist, rfl⟩ |
      ⟨S, RS, cs, ts, hts, b, hcs, hts0, hcsb, hconv, hRS, rfl⟩
  · -- Step 2 (positive scale): `(ν^{a,t})^{y,λ} = ν^{a+ty,tλ}` for `ν = μ_T⌞B_{2r}(z)`
    -- (`idtp_fons_cc_ambient_calculus` (7)), and `(a + ty, tλ)` is admissible: `0 < tλ < t ≤ r`
    -- and `|a + ty − z| ≤ (r − t) + t(1 − λ) = r − tλ`
    refine (h𝓜 _).2 (Or.inl ⟨a + t • y, t * lam, mul_pos ht0 hlam0,
      (mul_lt_of_lt_one_right ht0 hlam1).le.trans htr, ?_,
      Submission.idtp_fons_cc_ambient_calculus.2.2.2.2.2.2.1 (n + k) n _ a y t lam ht0 hlam0⟩)
    linarith [htri a t ht0.le]
  · -- Step 3 (zero scale): the rescaled weight `λ⁻ⁿ η_{y,λ#}μ_S` is the weight of a weak limit
    -- `S'` of `η_{cᵢ+tᵢy,tᵢλ#}T`
    obtain ⟨S', hconv', hrep⟩ := Submission.dimred_tr_bc_zero_limit_rescale hBC hBUI (n + k) n U T
      cs ts hts S y lam hlam0 hconv
    obtain ⟨RS', hRS', hmeas⟩ := hrep RS hRS
    -- Step 4: `(cᵢ + tᵢy, tᵢλ, b)` are zero-scale data for `S'`
    refine (h𝓜 _).2 (Or.inr ⟨S', RS', fun i => cs i + ts i • y, fun i => ts i * lam,
      fun i => mul_pos (hts i) hlam0, b, fun i => ?_, ?_, ?_, hconv', hRS', hmeas.symm⟩)
    · -- (a) `|cᵢ + tᵢy − z| ≤ |cᵢ − z| + tᵢ(1 − λ) < (r − tᵢ) + tᵢ(1 − λ) = r − tᵢλ`
      linarith [htri (cs i) (ts i) (hts i).le, hcs i]
    · -- (b) `tᵢλ → 0 · λ = 0`
      simpa using hts0.mul_const lam
    · -- (c) `cᵢ + tᵢy → b + 0 • y = b`
      simpa using hcsb.add (hts0.smul_const y)

/-- **Blow-up integrals of compactly supported functions** (the rescaled weights
`μ^{p,λ} = λ⁻ⁿ η_{p,λ#}μ` of the blow-ups `η_{p,λ#}T` of Simon 7.3.1(2), `η_{p,λ}(y) = λ⁻¹(y − p)`).
Let `λⱼ > 0`, `λⱼ → 0`, and let `f : ℝᴾ → ℝ` have compact support (neither continuity nor
integrability is needed).  (a) If `G` is open and `p ∈ G`, then `∫ f d(μ⌞G)^{p,λⱼ} = ∫ f dμ^{p,λⱼ}`
for all large `j`: `(μ⌞G)^{p,s} = μ^{p,s}⌞η_{p,s}(G)` as `η_{p,s}` is a measurable embedding, and
`η_{p,s}(G) ⊇ η_{p,s}(B_δ(p)) = B_{δ/s}(0) ⊇ spt f` once `λⱼ` is small.  (b) If `μ(B_ε(p)) = 0`,
then `∫ f dμ^{p,λⱼ} = 0` for all large `j`: `μ^{p,s}(B_{ε/s}(0)) = s⁻ⁿ μ(B_ε(p)) = 0` and
`spt f ⊆ B_{ε/λⱼ}(0)` once `λⱼ` is small, so `f = 0` `μ^{p,λⱼ}`-a.e. -/
theorem Submission.idtp_fons_cc_tm_blowup_integrals : (∀ (P n : ℕ) (μ : Measure (Euclid P)) (G : Set (Euclid P)) (p : Euclid P) (lams : ℕ → ℝ) (f : Euclid P → ℝ), IsOpen G → p ∈ G → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → HasCompactSupport f → ∀ᶠ j in atTop, ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • (μ.restrict G).map (dilation p (lams j))) = ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • μ.map (dilation p (lams j)))) ∧ ∀ (P n : ℕ) (μ : Measure (Euclid P)) (p : Euclid P) (ε : ℝ) (lams : ℕ → ℝ) (f : Euclid P → ℝ), 0 < ε → μ (ball p ε) = 0 → (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → HasCompactSupport f → ∀ᶠ j in atTop, ∫ x, f x ∂(ENNReal.ofReal ((lams j)⁻¹ ^ n) • μ.map (dilation p (lams j))) = 0 := by
  -- Step 1: `η_{a,s}(y) = s⁻¹(y − a)`; for `s > 0`, `η_{a,s}` is the homeomorphism
  -- `y ↦ −s⁻¹a + s⁻¹y`, hence a measurable embedding
  have hdil : ∀ (P : ℕ) (a : Euclid P) (s : ℝ) (y : Euclid P), dilation a s y = s⁻¹ • (y - a) := by
    intro P a s y
    show -(s⁻¹ • a) + s⁻¹ • y = s⁻¹ • (y - a)
    rw [smul_sub, neg_add_eq_sub]
  have hemb : ∀ (P : ℕ) (a : Euclid P) (s : ℝ), 0 < s → MeasurableEmbedding (dilation a s) := by
    intro P a s hs
    have hh : ⇑((Homeomorph.smulOfNeZero s⁻¹ (inv_ne_zero hs.ne')).trans
        (Homeomorph.addLeft (-(s⁻¹ • a)))) = dilation a s := by
      funext y
      simp [dilation, dilationCLM]
    exact hh ▸ Homeomorph.measurableEmbedding _
  -- Step 3: `tsupport f ⊆ B̄_M(0)` and `λⱼ(|M| + 1) → 0`, so for each `r > 0`, eventually
  -- `λⱼ‖x‖ ≤ λⱼ(|M| + 1) < r` on `tsupport f`, i.e. `tsupport f ⊆ B_{r/λⱼ}(0)`
  have hsupp : ∀ (P : ℕ) (f : Euclid P → ℝ) (lams : ℕ → ℝ) (r : ℝ), HasCompactSupport f →
      (∀ j, 0 < lams j) → Tendsto lams atTop (𝓝 0) → 0 < r →
      ∀ᶠ j in atTop, tsupport f ⊆ ball 0 (r / lams j) := by
    intro P f lams r hf hpos hlim hr
    obtain ⟨M, hM⟩ := hf.isCompact.isBounded.subset_closedBall 0
    have hlim' : Tendsto (fun j => lams j * (|M| + 1)) atTop (𝓝 0) := by
      simpa using hlim.mul_const (|M| + 1)
    filter_upwards [hlim'.eventually (gt_mem_nhds hr)] with j hj x hx
    have hx' : ‖x‖ ≤ |M| + 1 := by
      linarith [mem_closedBall_zero_iff.mp (hM hx), le_abs_self M]
    rw [mem_ball_zero_iff, lt_div_iff₀ (hpos j), mul_comm]
    exact (mul_le_mul_of_nonneg_left hx' (hpos j).le).trans_lt hj
  refine ⟨?_, ?_⟩
  · -- Step 4 (a): `B_δ(p) ⊆ G`, and eventually `tsupport f ⊆ B_{δ/λⱼ}(0)`
    intro P n μ G p lams f hG hp hpos hlim hf
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hG p hp
    filter_upwards [hsupp P f lams δ hf hpos hlim hδ] with j hj
    have hs := hpos j
    -- (i) `(μ⌞G)^{p,s} = μ^{p,s}⌞η_{p,s}(G)`, as `η_{p,s}⁻¹(η_{p,s}(G)) = G`
    rw [← (hemb P p (lams j) hs).injective.preimage_image G,
      ← (hemb P p (lams j) hs).restrict_map, ← Measure.restrict_smul]
    -- (ii)–(iii) `f` vanishes off `η_{p,s}(G)`: if `f(x) ≠ 0`, then `x ∈ B_{δ/s}(0)`, so
    -- `x = η_{p,s}(p + sx)` with `‖(p + sx) − p‖ = s‖x‖ < δ` (step 2), and `p + sx ∈ G`
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    by_contra hfx
    have hx' := hj (subset_tsupport f hfx)
    rw [mem_ball_zero_iff, lt_div_iff₀ hs, mul_comm] at hx'
    refine hx ⟨p + lams j • x, hball ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.le]
      exact hx'
    · rw [hdil, add_sub_cancel_left, inv_smul_smul₀ hs.ne']
  · -- Step 5 (b): eventually `tsupport f ⊆ B_{ε/λⱼ}(0)`
    intro P n μ p ε lams f hε hμ hpos hlim hf
    filter_upwards [hsupp P f lams ε hf hpos hlim hε] with j hj
    have hs := hpos j
    -- (i) `μ^{p,s}(B_{ε/s}(0)) = s⁻ⁿ μ(η_{p,s}⁻¹(B_{ε/s}(0))) = 0`, as
    -- `η_{p,s}⁻¹(B_{ε/s}(0)) ⊆ B_ε(p)`: `‖y − p‖ = s‖η_{p,s}(y)‖` (step 2)
    have hnull : (ENNReal.ofReal ((lams j)⁻¹ ^ n) • μ.map (dilation p (lams j)))
        (ball 0 (ε / lams j)) = 0 := by
      rw [Measure.smul_apply, (hemb P p (lams j) hs).map_apply]
      refine (congrArg _ (measure_mono_null (fun y hy => ?_) hμ)).trans (smul_zero _)
      have hy' : y - p = lams j • dilation p (lams j) y := by
        rw [hdil, smul_inv_smul₀ hs.ne']
      rw [mem_preimage, mem_ball_zero_iff, lt_div_iff₀ hs] at hy
      rw [mem_ball, dist_eq_norm, hy', norm_smul, Real.norm_of_nonneg hs.le, mul_comm]
      exact hy
    -- (ii) `{f ≠ 0} ⊆ tsupport f ⊆ B_{ε/s}(0)` is `μ^{p,s}`-null, so `∫ f dμ^{p,s} = 0`
    exact integral_eq_zero_of_ae (ae_iff.2 (measure_mono_null
      (fun x hx => hj (subset_tsupport f hx)) hnull))
/-- **Simon 7.3.3, proof of (1)** (pp. 189–191; A.2 of Appendix A for the class `𝒯`): tangent
measures of members of `𝓜` exist, lie in `𝓜` and are `n`-homogeneous.  Write `W = B_{2r}(z)` and
`m^{a,s} = s⁻ⁿ η_{a,s#}m`; `𝓜` consists of the `(μ_T⌞W)^{a,t}` (`0 < t ≤ r`, `dist(a, z) ≤ r − t`)
and of the weights of zero-scale limits `η_{cᵢ,tᵢ#}T ⇀ S` (`dist(cᵢ, z) < r − tᵢ`, `tᵢ → 0`,
`cᵢ → b`).  For `μ = (μ_T⌞W)^{a,t}`, `μ^{y,s} = (μ_T⌞W)^{p,ts}` with `p = a + ty` and
`dist(p, z) < r`: if `p ∈ spt T`, (TAN) at `p` gives a minimizing limit `C` of `η_{p,tλ_{φ(j)}#}T`
with homogeneous weight, a zero-scale member with constant centres `p`, and the weights of these
blow-ups agree with `μ^{y,λ_{φ(j)}}` near `spt f` and converge to `μ_C`; else the blow-ups at `p`
vanish and `ν = 0`.  For a zero-scale member `μ = μ_S`, `S` is minimizing in `ℝ^{n+k}`; if
`y ∈ spt S`, (TAN) for `S` at `y` gives `C`, a zero-scale limit of blow-ups of `T` by (IBL); else
`ν = 0`. -/
theorem Submission.dimred_tr_bc_class_tangent : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ x ∈ T.support, ∀ (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T x (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ ∀ R : IMRep (univ : Set (Euclid (n + k))) n, R.Represents C → ∀ lam : ℝ, 0 < lam → ∀ A : Set (Euclid (n + k)), MeasurableSet A → R.measure ((fun x => lam • x) '' A) = ENNReal.ofReal (lam ^ n) * R.measure A) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam), (∀ W : Set (Euclid P), (blowUp T x lam hlam.ne').massOn W = ENNReal.ofReal (lam⁻¹ ^ n) * T.massOn (dilation x lam ⁻¹' W)) ∧ (∀ ω : DifferentialForm (Euclid P) n, currentEval (blowUp T x lam hlam.ne') ω = currentEval T (affinePullbackForm (dilationCLM P lam) (-(lam⁻¹ • x)) ω)) ∧ ∀ (y : Euclid P) (mu : ℝ) (hmu : 0 < mu) (ω : DifferentialForm (Euclid P) n), currentEval (blowUp (blowUp T x lam hlam.ne') y mu hmu.ne') ω = currentEval (blowUp T (x + lam • y) (lam * mu) (mul_pos hlam hmu).ne') ω) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (lam : ℝ) (hlam : 0 < lam) (R : IMRep U n), R.Represents T → ∃ R' : IMRep (dilation x lam '' U) n, R'.Represents (blowUp T x lam hlam.ne') ∧ ∀ s : Set (Euclid P), MeasurableSet s → R'.measure s = ENNReal.ofReal (lam⁻¹ ^ n) * R.measure (dilation x lam ⁻¹' s)) → (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (x : Euclid P) (xs : ℕ → Euclid P) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i) (S : GeometricCurrentOn (univ : Set (Euclid P)) n) (y : Euclid P) (ss : ℕ → ℝ) (hss : ∀ k, 0 < ss k) (C : GeometricCurrentOn (univ : Set (Euclid P)) n), IsOpen U → x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → Tendsto ss atTop (𝓝 0) → (∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball x δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ → T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n)) → ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S → ConvergesWeakly (fun k => blowUp S y (ss k) (hss k).ne') C → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ConvergesWeakly (fun k => blowUp T (xs (φ k) + lams (φ k) • y) (lams (φ k) * ss k) (mul_pos (hlams (φ k)) (hss k)).ne') C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → (∀ μ ∈ 𝓜, ∀ y : Euclid (n + k), ‖y‖ < 1 → ∀ lams : ℕ → ℝ, (∀ j, 0 < lams j) → StrictAnti lams → Tendsto lams atTop (𝓝 0) → ∃ (sub : ℕ → ℕ) (ν : Measure (Euclid (n + k))), StrictMono sub ∧ ν ∈ 𝓜 ∧ (∀ lam : ℝ, 0 < lam → ∀ s : Set (Euclid (n + k)), MeasurableSet s → ν ((fun x => lam • x) '' s) = ENNReal.ofReal (lam ^ n) * ν s) ∧ ∀ f : Euclid (n + k) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun j => ∫ x, f x ∂(ENNReal.ofReal ((lams (sub j))⁻¹ ^ n) • μ.map (dilation y (lams (sub j))))) atTop (𝓝 (∫ x, f x ∂ν))) := by
  intro hIM hMON hMB hTAN hBC hBUI hIBL n k ℓ hℓk U N T hn hU hN hNU hT hsptT hbdT z r RT 𝓜 hr
    hzU hRT h𝓜 μ hμ y hy lams hlams _ hlim
  -- P1: `M_{B_{2r}(z)}(T) = μ_T(B_{2r}(z)) ≤ μ_T(B̄_{2r}(z)) < ∞` by (IM)(a) and the local
  -- integrability of the multiplicity of `RT` on the compact `B̄_{2r}(z) ⊆ U`
  have hWU : ball z (2 * r) ⊆ U := ball_subset_closedBall.trans hzU
  have hmassW : T.massOn (ball z (2 * r)) ≠ ∞ := by
    rw [(hIM (n + k) n U T RT hU hRT).1 _ isOpen_ball hWU]
    refine ne_top_of_le_ne_top ?_ (measure_mono ball_subset_closedBall)
    rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    exact RT.locallyIntegrable_mult _ (isCompact_closedBall z (2 * r)) hzU
  -- P8: (MON)(i) on `B̄_{2r}(z)` and uniform_mass_bound give `δ, Γ` with
  -- `M_{B_ρ(x')}(T) ≤ Γρⁿ` for `b ∈ B̄_r(z)`, `x' ∈ B_δ(b)`, `0 < ρ < δ` (the mass bound of (IBL))
  obtain ⟨Λ, hΛ, hmono⟩ := (hMON (n + k) n (n + ℓ) U N T hn (Nat.le_add_right n ℓ)
    (Nat.add_le_add_left hℓk n) hU hN hNU hT hsptT hbdT).1 _ (isCompact_closedBall z (2 * r)) hzU
  obtain ⟨δ, Γ, hδ, hbound⟩ :=
    Submission.dimred_tr_bc_ct_uniform_mass_bound (n + k) n U T z r Λ hr hΛ hmono hmassW
  -- P4: the empty IMRep `R0` represents `0` and has weight `0`, which is `n`-homogeneous
  obtain ⟨R0, hR0, hR0m⟩ := Submission.dimred_tr_bc_ct_zero_imrep (n + k) n
  have hhom0 : ∀ lam : ℝ, 0 < lam → ∀ s : Set (Euclid (n + k)), MeasurableSet s →
      (0 : Measure (Euclid (n + k))) ((fun x => lam • x) '' s) =
        ENNReal.ofReal (lam ^ n) * (0 : Measure (Euclid (n + k))) s := by
    simp
  -- constant centres: if `dist(p, z) < r`, `sⱼ → 0` and `η_{p,sⱼ#}T ⇀ C`, then the weight of every
  -- IMRep of `C` is a zero-scale member, with data `cᵢ = p`, `tᵢ = s_{i+i₀}`, `b = p`, where
  -- `sⱼ < r − dist(p, z)` for `j ≥ i₀` (P9: tails of weakly convergent sequences converge)
  have hconst : ∀ (p : Euclid (n + k)) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
      (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n)
      (RC : IMRep (univ : Set (Euclid (n + k))) n), dist p z < r → Tendsto s atTop (𝓝 0) →
      ConvergesWeakly (fun j => blowUp T p (s j) (hs j).ne') C → RC.Represents C →
      RC.measure ∈ 𝓜 := by
    intro p s hs C RC hp hs0 hC hRC
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hs0.eventually_lt_const (sub_pos.2 hp))
    refine (h𝓜 _).2 (Or.inr ⟨C, RC, fun _ => p, fun i => s (i + i₀), fun i => hs (i + i₀), p,
      fun i => ?_, hs0.comp (tendsto_add_atTop_nat i₀), tendsto_const_nhds,
      fun ω => (hC ω).comp (tendsto_add_atTop_nat i₀), hRC, rfl⟩)
    have hi := hi₀ (i + i₀) (Nat.le_add_left i₀ i)
    show dist p z < r - s (i + i₀)
    linarith
  rcases (h𝓜 μ).1 hμ with ⟨a, t, ht, -, hat, rfl⟩ |
    ⟨S, RS, cs, ts, hts, b, hcs, hts0, hcsb, hS, hRS, rfl⟩
  · -- Case (PS): `μ = (μ_T⌞W)^{a,t}`.  Put `p := a + t•y`; then `dist(p, z) < r` as `‖y‖ < 1`
    set p := a + t • y with hp
    have hpz : dist p z < r := by
      have hpa : dist p a = t * ‖y‖ := by
        rw [hp, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.le]
      linarith [dist_triangle p a z, mul_lt_of_lt_one_right ht hy]
    have hpW : p ∈ ball z (2 * r) := mem_ball.2 (by linarith)
    -- ambient_calculus (7): `μ^{y,s} = (μ_T⌞W)^{p,ts}`
    have hresc : ∀ s : ℝ, 0 < s →
        ENNReal.ofReal (s⁻¹ ^ n) • (ENNReal.ofReal (t⁻¹ ^ n) •
          (RT.measure.restrict (ball z (2 * r))).map (dilation a t)).map (dilation y s) =
        ENNReal.ofReal ((t * s)⁻¹ ^ n) •
          (RT.measure.restrict (ball z (2 * r))).map (dilation p (t * s)) := fun s hs =>
      Submission.idtp_fons_cc_ambient_calculus.2.2.2.2.2.2.1 (n + k) n _ a y t s ht hs
    have htl0 : Tendsto (fun j => t * lams j) atTop (𝓝 0) := by
      simpa using hlim.const_mul t
    by_cases hpT : p ∈ T.support
    · -- Case (PS-i): (TAN) at `p` with the scales `tλⱼ` gives a minimizing `C` with homogeneous
      -- weights; its weight is a zero-scale member with constant centres `p`
      obtain ⟨φ, C, hφ, hC, hCm, hCmin, hChom⟩ := hTAN n k ℓ hℓk U N T hn hU hN hNU hT hsptT
        hbdT p hpT (fun j => t * lams j) (fun j => mul_pos ht (hlams j)) htl0
      obtain ⟨RC, hRC⟩ := hCmin.1
      have hφ0 : Tendsto (fun j => t * lams (φ j)) atTop (𝓝 0) := htl0.comp hφ.tendsto_atTop
      refine ⟨φ, RC.measure, hφ, hconst p (fun j => t * lams (φ j))
        (fun j => mul_pos ht (hlams (φ j))) C RC hpz hφ0 hC hRC, hChom RC hRC, fun f hf hfs => ?_⟩
      -- the IMRep weights `μ_T^{p,tλ_{φ(j)}}` of the blow-ups converge vaguely to `μ_C`
      -- (weight_convergence), and agree with `μ^{y,λ_{φ(j)}} = (μ_T⌞W)^{p,tλ_{φ(j)}}` on `f`
      -- for large `j` (blowup_integrals (a), as `p ∈ W`)
      refine (Submission.dimred_tr_bc_ct_weight_convergence hBUI (n + k) n U T RT p
        (fun j => t * lams (φ j)) (fun j => mul_pos ht (hlams (φ j))) C RC hRT hRC hCm f hf
        hfs).congr' ?_
      filter_upwards [Submission.idtp_fons_cc_tm_blowup_integrals.1 (n + k) n RT.measure
        (ball z (2 * r)) p (fun j => t * lams (φ j)) f isOpen_ball hpW
        (fun j => mul_pos ht (hlams (φ j))) hφ0 hfs] with j hj
      rw [hresc _ (hlams (φ j))]
      exact hj.symm
    · -- Case (PS-ii): `p ∉ spt T`, so blow-ups at `p` vanish and `μ_T(B_ε(p)) = 0`; `ν := 0`
      obtain ⟨ε, hε, hεU, -, hεm, hvan⟩ :=
        Submission.dimred_tr_bc_vanishing_blowup hBC (n + k) n U T p (hWU hpW) hpT
      have hnull : RT.measure (ball p ε) = 0 := by
        rw [← (hIM (n + k) n U T RT hU hRT).1 _ isOpen_ball hεU, hεm]
      refine ⟨id, 0, strictMono_id, ?_, hhom0, fun f _ hfs => ?_⟩
      · rw [← hR0m]
        exact hconst p (fun j => t * lams j) (fun j => mul_pos ht (hlams j)) 0 R0 hpz htl0
          (hvan _ (fun j => mul_pos ht (hlams j)) htl0) hR0
      · -- `μ^{y,λⱼ} = (μ_T⌞W)^{p,tλⱼ}` and `(μ_T⌞W)(B_ε(p)) = 0`: blowup_integrals (b)
        rw [integral_zero_measure]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Submission.idtp_fons_cc_tm_blowup_integrals.2 (n + k) n
          (RT.measure.restrict (ball z (2 * r))) p ε (fun j => t * lams j) f hε
          (nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hnull.le))
          (fun j => mul_pos ht (hlams j)) htl0 hfs] with j hj
        rw [id, hresc _ (hlams j)]
        exact hj.symm
  · -- Case (ZS): `μ = μ_S` with zero-scale data `(cᵢ, tᵢ, b)`.  P6: `dist(b, z) ≤ r`, so `b ∈ U`,
    -- `S` is minimizing in `ℝ^{n+k}` with `∂S = 0` (zero_limit_minimizing), and (IBL)'s mass
    -- bound holds at `b` (P8)
    have hbz : b ∈ closedBall z r := by
      have hdist : Tendsto (fun i => dist (cs i) z) atTop (𝓝 (dist b z)) :=
        hcsb.dist tendsto_const_nhds
      exact mem_closedBall.2 (le_of_tendsto' hdist fun i => by linarith [hcs i, hts i])
    have hbU : b ∈ U := hzU (closedBall_subset_closedBall (by linarith) hbz)
    obtain ⟨hSmin, hSbd⟩ := Submission.dimred_tr_bc_zero_limit_minimizing hMB n k ℓ hℓk U N T hn
      hU hN hNU hT hsptT hbdT b cs ts hts S hbU hcsb hts0 hS
    have hmb : ∃ δ Γ : ℝ, 0 < δ ∧ ∀ x' ∈ ball b δ, ∀ ρ : ℝ, 0 < ρ → ρ < δ →
        T.massOn (ball x' ρ) ≤ ENNReal.ofReal (Γ * ρ ^ n) := ⟨δ, Γ, hδ, hbound b hbz⟩
    by_cases hyS : y ∈ S.support
    · -- Case (ZS-i): (TAN) for `S` at `y`, with `U = N = ℝ^{n+k}` (P5, ambient_calculus (1))
      obtain ⟨φ, C, hφ, hC, hCm, hCmin, hChom⟩ := hTAN n k k le_rfl univ univ S hn isOpen_univ
        (Submission.idtp_fons_cc_ambient_calculus.1 (n + k)) (by simp) (by rwa [inter_self])
        (by simp) hSbd y hyS lams hlams hlim
      obtain ⟨RC, hRC⟩ := hCmin.1
      -- (IBL) and a tail (zero_scale_iterate): `C` is a zero-scale limit of blow-ups of `T`, so
      -- `μ_C ∈ 𝓜`; the convergence is weight_convergence for `S`
      obtain ⟨cs', ts', hts', hcs', hts'0, hcs'b, hC'⟩ :=
        Submission.dimred_tr_bc_ct_zero_scale_iterate hIBL (n + k) n U T z r S cs ts hts b y
          (fun j => lams (φ j)) (fun j => hlams (φ j)) C hU hbU hcs hts0 hcsb hS hmb hy
          (hlim.comp hφ.tendsto_atTop) hC
      exact ⟨φ, RC.measure, hφ,
        (h𝓜 _).2 (Or.inr ⟨C, RC, cs', ts', hts', b, hcs', hts'0, hcs'b, hC', hRC, rfl⟩),
        hChom RC hRC, Submission.dimred_tr_bc_ct_weight_convergence hBUI (n + k) n univ S RS y
          (fun j => lams (φ j)) (fun j => hlams (φ j)) C RC hRS hRC hCm⟩
    · -- Case (ZS-ii): `y ∉ spt S`, so blow-ups of `S` at `y` vanish and `μ(B_ε(y)) = 0`; `ν := 0`
      obtain ⟨ε, hε, -, -, hεm, hvan⟩ :=
        Submission.dimred_tr_bc_vanishing_blowup hBC (n + k) n univ S y (mem_univ y) hyS
      have hnull : RS.measure (ball y ε) = 0 := by
        rw [← (hIM (n + k) n univ S RS isOpen_univ hRS).1 _ isOpen_ball (subset_univ _), hεm]
      obtain ⟨cs', ts', hts', hcs', hts'0, hcs'b, hC'⟩ :=
        Submission.dimred_tr_bc_ct_zero_scale_iterate hIBL (n + k) n U T z r S cs ts hts b y lams
          hlams 0 hU hbU hcs hts0 hcsb hS hmb hy hlim (hvan lams hlams hlim)
      refine ⟨id, 0, strictMono_id, ?_, hhom0, fun f _ hfs => ?_⟩
      · rw [← hR0m]
        exact (h𝓜 _).2 (Or.inr ⟨0, R0, cs', ts', hts', b, hcs', hts'0, hcs'b, hC', hR0, rfl⟩)
      · rw [integral_zero_measure]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Submission.idtp_fons_cc_tm_blowup_integrals.2 (n + k) n RS.measure y ε
          lams f hε hnull hlams hlim hfs] with j hj
        exact hj.symm
/-- **Simon 7.3.3, proof of (1)** (p. 189), monotonicity for the class `𝒯`: given (IM), (MON)
and (MB), one constant `Λ` makes `ρ ↦ e^{Λρ}ρ⁻ⁿμ(B_ρ(y))` nondecreasing on `(0, R)` for every
`μ ∈ 𝓜` and every `B̄_R(y) ⊆ B̄₂(0)`.  (MON)(i) on the compact `K = B̄_{2r}(z) ⊆ U` gives
`Λ_K ≥ 0`; take `Λ = rΛ_K`.  For a positive-scale member `μ = t⁻ⁿ η_{a,t#}(μ_T⌞B_{2r}(z))`,
`μ(B_ρ(y)) = t⁻ⁿ M_{B_{tρ}(a+ty)}(T)` with `B̄_{tR}(a + ty) ⊆ K`, so
`e^{Λρ}ρ⁻ⁿμ(B_ρ(y)) = e^{(r−t)Λ_Kρ} · e^{Λ_K tρ}(tρ)⁻ⁿ M_{B_{tρ}(a+ty)}(T)` is a product of
nondecreasing factors.  A zero-scale member is the measure of a weak limit `S` of blow-ups,
minimizing in `ℝ^{n+k}` with `∂S = 0` (zero_limit_minimizing), so (MON)(ii) and (IM) make
`ρ⁻ⁿμ(B_ρ(y))` nondecreasing, and `e^{Λρ}` is nondecreasing as `Λ ≥ 0`. -/
theorem Submission.dimred_tr_bc_class_monotone : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → ∃ Λ : ℝ, (∀ μ ∈ 𝓜, ∀ (y : Euclid (n + k)) (R : ℝ), closedBall y R ⊆ closedBall 0 2 → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * μ (ball y ρ)) (Ioo 0 R)) := by
  intro hIM hMON hMB n k ℓ hℓk U N T hn hU hN hNU hT hsptT hbdT z r RT 𝓜 hr hzU hRT h𝓜
  -- Step 1: (MON)(i) for `T` (with `d = n + ℓ`) on the compact `K = B̄_{2r}(z) ⊆ U` gives
  -- `Λ_K ≥ 0`; the common constant is `Λ = rΛ_K ≥ 0`
  obtain ⟨hMONi, -, -, -⟩ := hMON (n + k) n (n + ℓ) U N T hn (Nat.le_add_right n ℓ)
    (Nat.add_le_add_left hℓk n) hU hN hNU hT hsptT hbdT
  obtain ⟨ΛK, hΛK, hmonK⟩ := hMONi (closedBall z (2 * r)) (isCompact_closedBall z (2 * r)) hzU
  obtain ⟨hAC1, hAC2, hAC3, -⟩ := Submission.idtp_fons_cc_ambient_calculus
  refine ⟨r * ΛK, fun μ hμ y R hyR => ?_⟩
  rcases (h𝓜 μ).1 hμ with ⟨a, t, ht, htr, haz, hμeq⟩ |
    ⟨S, RS, cs, ts, hts, b, hcs, hts0, hcsb, hS, hRS, hμeq⟩
  · -- Step 4 (positive scale, `μ = t⁻ⁿ η_{a,t#}(μ_T⌞B_{2r}(z))`), with `c' := a + ty`:
    -- `η_{a,t}(v) = t⁻¹(v − a)`, so `dist(η_{a,t}(v), w) = t⁻¹ dist(v, a + tw)` and
    -- `dist(v, z) ≤ dist(a, z) + t‖η_{a,t}(v)‖`
    have hdil : ∀ v : Euclid (n + k), dilation a t v = t⁻¹ • (v - a) := fun v => by
      show -(t⁻¹ • a) + t⁻¹ • v = t⁻¹ • (v - a)
      rw [smul_sub, neg_add_eq_sub]
    have hdw : ∀ v w : Euclid (n + k), dist (dilation a t v) w = t⁻¹ * dist v (a + t • w) := by
      intro v w
      have hv : dilation a t v - w = t⁻¹ • (v - (a + t • w)) := by
        rw [hdil, sub_add_eq_sub_sub, smul_sub t⁻¹ (v - a) (t • w), inv_smul_smul₀ ht.ne']
      rw [dist_eq_norm, dist_eq_norm, hv, norm_smul, norm_inv, Real.norm_of_nonneg ht.le]
    have hvz : ∀ v : Euclid (n + k), dist v z ≤ dist a z + t * ‖dilation a t v‖ := by
      intro v
      have hv : v - z = (a - z) + t • dilation a t v := by
        rw [hdil, smul_inv_smul₀ ht.ne']
        abel
      calc dist v z = ‖(a - z) + t • dilation a t v‖ := by rw [dist_eq_norm, hv]
        _ ≤ ‖a - z‖ + ‖t • dilation a t v‖ := norm_add_le _ _
        _ = dist a z + t * ‖dilation a t v‖ := by
          rw [dist_eq_norm, norm_smul, Real.norm_of_nonneg ht.le]
    -- (a) `B̄_{tR}(c') ⊆ K`: `η_{a,t}` maps it into `B̄_R(y) ⊆ B̄₂(0)`, and
    -- `dist(v, z) ≤ (r − t) + 2t ≤ 2r`
    have hK : closedBall (a + t • y) (t * R) ⊆ closedBall z (2 * r) := by
      intro v hv
      have hw : dilation a t v ∈ closedBall (0 : Euclid (n + k)) 2 := by
        apply hyR
        rw [mem_closedBall, hdw, inv_mul_le_iff₀ ht]
        exact hv
      rw [mem_closedBall_zero_iff] at hw
      rw [mem_closedBall]
      linarith [hvz v, mul_le_mul_of_nonneg_left hw ht.le]
    have hκ : 0 ≤ (r - t) * ΛK := mul_nonneg (sub_nonneg.2 htr) hΛK
    have hg := hmonK (a + t • y) (t * R) hK
    intro ρ₁ hρ₁ ρ₂ hρ₂ hρ
    have hR : 0 < R := hρ₁.1.trans hρ₁.2
    -- `B_R(y) = int B̄_R(y) ⊆ int B̄₂(0) = B₂(0)`
    have hball2 : ball y R ⊆ ball (0 : Euclid (n + k)) 2 := by
      rw [← interior_closedBall y hR.ne', ← interior_closedBall (0 : Euclid (n + k)) two_ne_zero]
      exact interior_mono hyR
    -- `B_{tρ}(c') ⊆ B_{2r}(z)` for `ρ ≤ R`: here `‖η_{a,t}(v)‖ < 2`
    have hW : ∀ ρ, ρ ≤ R → ball (a + t • y) (t * ρ) ⊆ ball z (2 * r) := by
      intro ρ hρR v hv
      have hw : dilation a t v ∈ ball (0 : Euclid (n + k)) 2 := by
        apply hball2
        rw [mem_ball, hdw, inv_mul_lt_iff₀ ht]
        exact lt_of_lt_of_le hv (mul_le_mul_of_nonneg_left hρR ht.le)
      rw [mem_ball_zero_iff] at hw
      rw [mem_ball]
      linarith [hvz v, mul_lt_mul_of_pos_left hw ht]
    -- (b) `μ(B_ρ(y)) = t⁻ⁿ μ_T(B_{2r}(z) ∩ η_{a,t}⁻¹(B_ρ(y))) = t⁻ⁿ M_{B_{tρ}(c')}(T)`
    have hμball : ∀ ρ, ρ ≤ R →
        μ (ball y ρ) = ENNReal.ofReal (t⁻¹ ^ n) * T.massOn (ball (a + t • y) (t * ρ)) := by
      intro ρ hρR
      rw [hμeq, hAC2 (n + k) n _ a t _ ht measurableSet_ball, hAC3 (n + k) a y t ρ ht,
        Measure.restrict_apply measurableSet_ball, inter_eq_left.2 (hW ρ hρR),
        (hIM (n + k) n U T RT hU hRT).1 _ isOpen_ball
          ((hW ρ hρR).trans (ball_subset_closedBall.trans hzU))]
    -- (c), (d) `e^{rΛ_Kρ}ρ⁻ⁿ t⁻ⁿ = e^{(r−t)Λ_Kρ} · e^{Λ_K tρ}(tρ)⁻ⁿ`
    have key : ∀ ρ ∈ Ioo 0 R,
        ENNReal.ofReal (Real.exp (r * ΛK * ρ) / ρ ^ n) * μ (ball y ρ) =
          ENNReal.ofReal (Real.exp ((r - t) * ΛK * ρ)) *
            (ENNReal.ofReal (Real.exp (ΛK * (t * ρ)) / (t * ρ) ^ n) *
              T.massOn (ball (a + t • y) (t * ρ))) := by
      intro ρ hρ
      have hreal : Real.exp (r * ΛK * ρ) / ρ ^ n * t⁻¹ ^ n =
          Real.exp ((r - t) * ΛK * ρ) * (Real.exp (ΛK * (t * ρ)) / (t * ρ) ^ n) := by
        rw [show r * ΛK * ρ = (r - t) * ΛK * ρ + ΛK * (t * ρ) by ring, Real.exp_add, mul_pow,
          inv_pow]
        ring
      rw [hμball ρ hρ.2.le, ← mul_assoc,
        ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le (pow_nonneg hρ.1.le n)), hreal,
        ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    show ENNReal.ofReal (Real.exp (r * ΛK * ρ₁) / ρ₁ ^ n) * μ (ball y ρ₁) ≤
      ENNReal.ofReal (Real.exp (r * ΛK * ρ₂) / ρ₂ ^ n) * μ (ball y ρ₂)
    rw [key ρ₁ hρ₁, key ρ₂ hρ₂]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hρ hκ)))
      (hg ⟨mul_pos ht hρ₁.1, mul_lt_mul_of_pos_left hρ₁.2 ht⟩
        ⟨mul_pos ht hρ₂.1, mul_lt_mul_of_pos_left hρ₂.2 ht⟩ (mul_le_mul_of_nonneg_left hρ ht.le))
  · -- Step 5 (zero scale, `μ = μ_S`): `dist(b, z) ≤ r`, so `b ∈ U`
    have hbz : dist b z ≤ r := le_of_tendsto' (hcsb.dist tendsto_const_nhds) fun i =>
      ((hcs i).trans (sub_lt_self r (hts i))).le
    have hb : b ∈ U := hzU (mem_closedBall.2 (by linarith))
    -- `S` is minimizing in `ℝ^{n+k}` with `∂S = 0` (zero_limit_minimizing with (MB))
    obtain ⟨hSmin, hSbd⟩ := Submission.dimred_tr_bc_zero_limit_minimizing hMB n k ℓ hℓk U N T
      hn hU hN hNU hT hsptT hbdT b cs ts hts S hb hcsb hts0 hS
    -- (MON)(ii) for `S` in `U = N = ℝ^{n+k}` (`d = n + k`), and (IM) for `S`
    obtain ⟨-, hMONii, -, -⟩ := hMON (n + k) n (n + k) univ univ S hn (Nat.le_add_right n k)
      le_rfl isOpen_univ (hAC1 (n + k)) (by simp) (by rwa [inter_self])
      (by rw [inter_self]; exact subset_univ _) hSbd
    have hmono := hMONii rfl y R (subset_univ _)
    have hmass := (hIM (n + k) n univ S RS isOpen_univ hRS).1
    -- `e^{Λρ}ρ⁻ⁿμ(B_ρ(y)) = e^{Λρ} · ρ⁻ⁿ M_{B_ρ(y)}(S)`, and `e^{Λρ}` is nondecreasing
    intro ρ₁ hρ₁ ρ₂ hρ₂ hρ
    have key : ∀ ρ : ℝ, ENNReal.ofReal (Real.exp (r * ΛK * ρ) / ρ ^ n) * μ (ball y ρ) =
        ENNReal.ofReal (Real.exp (r * ΛK * ρ)) *
          (ENNReal.ofReal (1 / ρ ^ n) * S.massOn (ball y ρ)) := by
      intro ρ
      rw [hmass _ isOpen_ball (subset_univ _), ← hμeq, ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_one_div]
    show ENNReal.ofReal (Real.exp (r * ΛK * ρ₁) / ρ₁ ^ n) * μ (ball y ρ₁) ≤
      ENNReal.ofReal (Real.exp (r * ΛK * ρ₂) / ρ₂ ^ n) * μ (ball y ρ₂)
    rw [key ρ₁, key ρ₂]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hρ (mul_nonneg hr.le hΛK)))) (hmono hρ₁ hρ₂ hρ)
/-- **The anchor and the infinite-mass members of the blow-up class** (proof of Simon 7.3.3(1),
chapter-07.txt lines 443–465: `T` itself belongs to the class `𝒯` of weak limits of rescalings
`η_{xᵢ,λᵢ#}T`, and the members with `λᵢ → 0` minimize in all of `ℝ^{n+ℓ}`, (8) there).  Let
`μ_T` be the weight of `T`, `W = B_{2r}(z)` and `μ_{a,t} = t⁻ⁿ η_{a,t#}(μ_T⌞W)`; `𝓜` consists of
the `μ_{a,t}` with `0 < t ≤ r`, `|a − z| ≤ r − t`, and of the weights `μ_S` of the weak limits `S`
of `η_{cᵢ,tᵢ#}T` with `|cᵢ − z| < r − tᵢ`, `tᵢ → 0` and `cᵢ` convergent.  (i) The anchor `μ_{z,r}`
has `μ_{z,r}(B_ρ(w)) = r⁻ⁿ M_{B_{rρ}(z + rw)}(T)` for `0 < ρ < 1 − |w|`, so its density at
`w ∈ B₁(0)` is that of `T` at `z + rw`.  (ii) `μ_{a,t}(ℝ^{n+k}) = t⁻ⁿ μ_T(W) < ∞`, so a member of
infinite mass is some `μ_S`; then `S` is minimizing in `ℝ^{n+k}` with `∂S = 0`
(`dimred_tr_bc_zero_limit_minimizing`), and by the monotonicity formula `S` has a density at every
point, which is the `limsup` density of `μ_S` since `M_{B_ρ(y)}(S) = μ_S(B_ρ(y))`. -/
theorem Submission.dimred_tr_bc_class_anchor_infinite : (∀ (P n : ℕ) (U : Set (Euclid P)) (T : GeometricCurrentOn U n) (R : IMRep U n), IsOpen U → R.Represents T → (∀ W : Set (Euclid P), IsOpen W → W ⊆ U → T.massOn W = R.measure W) ∧ (∀ x ∈ U, (x ∈ T.support ↔ ∀ ε : ℝ, 0 < ε → R.measure (ball x ε) ≠ 0)) ∧ ∀ R' : IMRep U n, R'.Represents T → R'.measure = R.measure) → (∀ (P n d : ℕ) (U N : Set (Euclid P)) (T : GeometricCurrentOn U n), 1 ≤ n → n ≤ d → d ≤ P → IsOpen U → IsEmbeddedSubmanifold 2 d N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U → ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ (y : Euclid P) (R : ℝ), closedBall y R ⊆ K → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (Real.exp (Λ * ρ) / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (N = univ → ∀ (y : Euclid P) (R : ℝ), ball y R ⊆ U → MonotoneOn (fun ρ : ℝ => ENNReal.ofReal (1 / ρ ^ n) * T.massOn (ball y ρ)) (Ioo 0 R)) ∧ (∃ Θ : Euclid P → ℝ, (∀ y ∈ U, HasMassDensity T y (Θ y)) ∧ UpperSemicontinuousOn Θ U) ∧ ∀ y ∈ T.support, ∀ θ : ℝ, HasMassDensity T y θ → 1 ≤ θ) → (∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (x : Euclid (n + k)) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ j, 0 < lams j), x ∈ U → Tendsto xs atTop (𝓝 x) → Tendsto lams atTop (𝓝 0) → ∃ (φ : ℕ → ℕ) (C : GeometricCurrentOn (univ : Set (Euclid (n + k))) n), StrictMono φ ∧ ConvergesWeakly (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ MassMeasuresConverge (fun j => blowUp T (xs (φ j)) (lams (φ j)) (hlams (φ j)).ne') C ∧ IsMinimizingIn C univ ∧ BoundaryVanishes C) → ∀ (n k ℓ : ℕ), ℓ ≤ k → ∀ (U N : Set (Euclid (n + k))) (T : GeometricCurrentOn U n), 1 ≤ n → IsOpen U → IsEmbeddedSubmanifold 2 (n + ℓ) N → (closure N \ N) ∩ U = ∅ → IsMinimizingIn T (U ∩ N) → T.support ⊆ U ∩ N → BoundaryVanishes T → ∀ (z : Euclid (n + k)) (r : ℝ) (RT : IMRep U n) (𝓜 : Set (Measure (Euclid (n + k)))), 0 < r → closedBall z (2 * r) ⊆ U → RT.Represents T → (∀ μ : Measure (Euclid (n + k)), μ ∈ 𝓜 ↔ (∃ (a : Euclid (n + k)) (t : ℝ), 0 < t ∧ t ≤ r ∧ dist a z ≤ r - t ∧ μ = ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) ∨ ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (RS : IMRep (univ : Set (Euclid (n + k))) n) (cs : ℕ → Euclid (n + k)) (ts : ℕ → ℝ) (hts : ∀ i, 0 < ts i) (b : Euclid (n + k)), (∀ i, dist (cs i) z < r - ts i) ∧ Tendsto ts atTop (𝓝 0) ∧ Tendsto cs atTop (𝓝 b) ∧ ConvergesWeakly (fun i => blowUp T (cs i) (ts i) (hts i).ne') S ∧ RS.Represents S ∧ μ = RS.measure) → ∀ dens : Measure (Euclid (n + k)) → Euclid (n + k) → ℝ, (∀ (μ : Measure (Euclid (n + k))) (x : Euclid (n + k)), dens μ x = (limsup (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0)).toReal) → (∃ μ₀ ∈ 𝓜, ∀ w ∈ ball (0 : Euclid (n + k)) 1, ∀ θ : ℝ, HasMassDensity T (z + r • w) θ → dens μ₀ w = θ) ∧ ∀ ν ∈ 𝓜, ν univ = ∞ → ∃ (S : GeometricCurrentOn (univ : Set (Euclid (n + k))) n) (xs : ℕ → Euclid (n + k)) (lams : ℕ → ℝ) (hlams : ∀ i, 0 < lams i), (∀ i, xs i ∈ ball z r) ∧ Tendsto lams atTop (𝓝 0) ∧ ConvergesWeakly (fun i => blowUp T (xs i) (lams i) (hlams i).ne') S ∧ IsMinimizingIn S univ ∧ BoundaryVanishes S ∧ ∀ y, HasMassDensity S y (dens ν y) := by
  intro hIM hMON hMB n k ℓ hℓk U N T hn hU hN hNcl hTmin hTspt hTbd z r RT 𝓜 hr hzU hRT hM dens
    hdens
  obtain ⟨hAC1, hAC2, hAC3, -, -, -, -, -, -⟩ := Submission.idtp_fons_cc_ambient_calculus
  -- Step 0: if the density ratio of `μ` at `x` tends to `θ ≥ 0` as `ρ ↓ 0`, its `limsup` is `θ`
  have hdens_eq : ∀ (μ : Measure (Euclid (n + k))) (x : Euclid (n + k)) (θ : ℝ), 0 ≤ θ →
      Tendsto (fun ρ : ℝ => μ (ball x ρ) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n)))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal θ)) → dens μ x = θ := by
    intro μ x θ hθ hlim
    rw [hdens, hlim.limsup_eq, ENNReal.toReal_ofReal hθ]
  -- Step 1: `μ_T(W) ≤ μ_T(B̄_{2r}(z)) < ∞`, as the multiplicity is locally `Hⁿ`-integrable and
  -- `B̄_{2r}(z) ⊆ U`; so every positive-scale member has finite total mass `t⁻ⁿ μ_T(W)`
  have hWfin : RT.measure (ball z (2 * r)) ≠ ∞ := by
    have hK := RT.locallyIntegrable_mult (closedBall z (2 * r)) (isCompact_closedBall z (2 * r))
      hzU
    have hKeq : RT.measure (closedBall z (2 * r)) =
        ∫⁻ x in RT.carrier ∩ closedBall z (2 * r), (RT.mult x : ℝ≥0∞) ∂μHE[n] := by
      rw [IMRep.measure, withDensity_apply _ measurableSet_closedBall,
        Measure.restrict_restrict measurableSet_closedBall, inter_comm]
    rw [← hKeq] at hK
    exact ne_top_of_le_ne_top hK (measure_mono ball_subset_closedBall)
  have hPSfin : ∀ (a : Euclid (n + k)) (t : ℝ), 0 < t →
      (ENNReal.ofReal (t⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation a t)) univ
        ≠ ∞ := by
    intro a t ht
    rw [hAC2 (n + k) n _ a t univ ht MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWfin
  refine ⟨⟨ENNReal.ofReal (r⁻¹ ^ n) • (RT.measure.restrict (ball z (2 * r))).map (dilation z r),
    (hM _).2 (Or.inl ⟨z, r, hr, le_rfl, by simp, rfl⟩), ?_⟩, ?_⟩
  · -- Step 2: the anchor `μ₀ = μ_{z,r}` (`(a, t) = (z, r)`, admissible as `|z − z| = 0 = r − r`);
    -- by Step 0 it suffices that its density ratio at `w` tends to `θ`
    rintro w hw θ ⟨hθ, hθlim⟩
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    apply hdens_eq _ w θ hθ
    -- `ρ ↦ rρ` maps `𝓝[>] 0` to itself, so `M_{B_{rρ}(z+rw)}(T)/(ωₙ(rρ)ⁿ) → θ`
    have hscale : Tendsto (fun ρ : ℝ => r * ρ) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_const_mul r).tendsto' 0 0 (mul_zero r)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun ρ hρ => mul_pos hr hρ)
    refine (hθlim.comp hscale).congr' ?_
    -- for `0 < ρ < 1 − |w|`: `B_{rρ}(z + rw) ⊆ W ⊆ U` and
    -- `μ₀(B_ρ(w)) = r⁻ⁿ μ_T(B_{rρ}(z + rw)) = r⁻ⁿ M_{B_{rρ}(z+rw)}(T)`
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hw1)] with ρ hρ
    have hball : ball (z + r • w) (r * ρ) ⊆ ball z (2 * r) := by
      refine ball_subset_ball' ?_
      rw [dist_self_add_left, norm_smul, Real.norm_of_nonneg hr.le]
      nlinarith [hρ.2]
    have hmass : T.massOn (ball (z + r • w) (r * ρ)) = RT.measure (ball (z + r • w) (r * ρ)) :=
      (hIM (n + k) n U T RT hU hRT).1 _ isOpen_ball
        (hball.trans (ball_subset_closedBall.trans hzU))
    -- and `(rρ)ⁿ = rⁿρⁿ`, `r⁻ⁿ = (rⁿ)⁻¹` with `0 < rⁿ < ∞`
    have hc0 : ENNReal.ofReal (r ^ n) ≠ 0 := (ENNReal.ofReal_pos.2 (pow_pos hr n)).ne'
    have hcancel : ∀ m : ℝ≥0∞, ENNReal.ofReal (r ^ n) * ((ENNReal.ofReal (r ^ n))⁻¹ * m) = m :=
      fun m => by rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 ENNReal.ofReal_ne_top, one_mul]
    rw [Function.comp_apply, hAC2 (n + k) n _ z r _ hr measurableSet_ball,
      hAC3 (n + k) z w r ρ hr, Measure.restrict_apply measurableSet_ball, inter_eq_left.2 hball,
      ← hmass, mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le n), inv_pow,
      ENNReal.ofReal_inv_of_pos (pow_pos hr n),
      ← ENNReal.mul_div_mul_left (_ * T.massOn _) _ hc0 ENNReal.ofReal_ne_top, hcancel,
      mul_left_comm (unitBallVolume n)]
  · -- Step 3: a member `ν` of infinite total mass
    intro ν hν hνinf
    rcases (hM ν).1 hν with ⟨a, t, ht, -, -, rfl⟩ |
        ⟨S, RS, cs, ts, hts, b, hcs, hts0, hcsb, hconv, hRS, rfl⟩
    · -- by Step 1, `ν` is not a positive-scale member
      exact absurd hνinf (hPSfin a t ht)
    -- (a) the centres `cᵢ` lie in `B_r(z)`, as `|cᵢ − z| < r − tᵢ < r`
    have hcsr : ∀ i, dist (cs i) z < r := fun i => (hcs i).trans_le (sub_le_self r (hts i).le)
    -- (b) `|b − z| ≤ r`, so `b ∈ U` and `S` is minimizing in `ℝ^{n+k}` with `∂S = 0`
    have hbU : b ∈ U := by
      have hbz : dist b z ≤ r :=
        le_of_tendsto' (hcsb.dist tendsto_const_nhds) fun i => (hcsr i).le
      exact hzU (mem_closedBall.2 (by linarith))
    obtain ⟨hSmin, hSbd⟩ := Submission.dimred_tr_bc_zero_limit_minimizing hMB n k ℓ hℓk U N T hn hU
      hN hNcl hTmin hTspt hTbd b cs ts hts S hbU hcsb hts0 hconv
    -- (c) monotonicity in `U = N = ℝ^{n+k}` gives densities `Θ(y)` of `S` at every `y`
    obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := hMON (n + k) n (n + k) univ univ S hn (Nat.le_add_right n k)
      le_rfl isOpen_univ (hAC1 (n + k)) (by simp) (by rwa [inter_self])
      (by rw [inter_self]; exact subset_univ _) hSbd
    refine ⟨S, cs, ts, hts, fun i => mem_ball.2 (hcsr i), hts0, hconv, hSmin, hSbd, fun y => ?_⟩
    -- (d) `M_{B_ρ(y)}(S) = μ_S(B_ρ(y))`, so `dens μ_S y = Θ(y)`
    obtain ⟨hΘ0, hΘlim⟩ := hΘ y (mem_univ y)
    have hmassS := (hIM (n + k) n univ S RS isOpen_univ hRS).1
    rw [hdens_eq RS.measure y (Θ y) hΘ0
      (hΘlim.congr fun ρ => by rw [hmassS _ isOpen_ball (subset_univ _)])]
    exact hΘ y (mem_univ y)
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

/-- **Density of an integer multiplicity weight on its carrier** (Simon Ch. 3, Remarks 1.5(3) and
1.8, Theorem 1.9, for integer multiplicities).  If `W ⊆ ℝᴾ` is open and `μ_R(K ∩ W) < ∞` for
every compact `K`, then for `Hⁿ`-a.e. `x ∈ M ∩ W`, `μ_R(B_ρ(x) ∩ W) / (ωₙρⁿ) → θ(x)` as `ρ ↓ 0`.
Put `μ = μ_R⌞W` and `ν = Hⁿ⌞(M ∩ W) ≤ μ`.  The approximate tangent plane at `x` gives
`ν(B_ρ(x)) / (ωₙρⁿ) → 1`, and the upper density theorem for the levels
`A_k = (M ∩ W) ∩ {θ ≠ k}` gives `μ(A_k ∩ B_ρ(x)) = o(ρⁿ)` where `θ(x) = k`.  Then
`μ(B) ≤ k ν(B) + μ(A_k ∩ B)` and `k ν(B) ≤ μ(B) + k μ(A_k ∩ B)` squeeze the ratio to `k`. -/
theorem Submission.dimred_tr_ida_density_on_carrier : ∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ R.carrier ∩ W → Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (R.mult x : ℝ≥0∞)) := by
  intro P n V W R hW hfin
  have hWm : MeasurableSet W := hW.measurableSet
  set M := R.carrier with hM
  have hMm : MeasurableSet M := R.measurableSet_carrier
  set M' := M ∩ W with hM'
  have hM'm : MeasurableSet M' := hMm.inter hWm
  set μ : Measure (Euclid P) := R.measure.restrict W with hμ
  set ν : Measure (Euclid P) := (μHE[n] : Measure (Euclid P)).restrict M' with hν
  -- Step 1: `μ` is finite on compact sets, `μ(S) = ∫_{S ∩ M'} θ dHⁿ`, and `ν ≤ μ`
  have hμfin : ∀ K : Set (Euclid P), IsCompact K → μ K ≠ ∞ := by
    intro K hK
    rw [hμ, Measure.restrict_apply' hWm]
    exact hfin K hK
  have hmeas : ∀ S : Set (Euclid P), MeasurableSet S →
      μ S = ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
    intro S hS
    rw [hμ, Measure.restrict_apply hS]
    simp only [IMRep.measure]
    rw [withDensity_apply _ (hS.inter hWm), Measure.restrict_restrict (hS.inter hWm)]
    have hSet : S ∩ W ∩ M = S ∩ M' := by
      ext y
      simp only [hM', mem_inter_iff]
      tauto
    rw [hSet]
  have hνle : ∀ S : Set (Euclid P), MeasurableSet S → ν S ≤ μ S := by
    intro S hS
    rw [hmeas S hS, hν, Measure.restrict_apply hS]
    calc μHE[n] (S ∩ M') = ∫⁻ _y in S ∩ M', (1 : ℝ≥0∞) ∂μHE[n] := by simp
      _ ≤ ∫⁻ y in S ∩ M', (R.mult y : ℝ≥0∞) ∂μHE[n] := by
        apply setLIntegral_mono' (hS.inter hM'm)
        intro y hy
        have h := R.mult_pos y hy.2.1
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr h.ne'
  -- Step 2: the level sets `A k = M' ∖ {θ = k}`
  set A : ℕ → Set (Euclid P) := fun k => M' ∩ R.mult ⁻¹' ({k}ᶜ) with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    hM'm.inter (R.measurable_mult (measurableSet_singleton k).compl)
  -- Step 3: `μ(A k ∩ B_ρ(x)) = o(ρⁿ)` off `A k`, for all `k` at once
  have hUD : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), ∀ k : ℕ, x ∉ A k →
      Tendsto (fun ρ : ℝ => μ (A k ∩ ball x ρ) /
        (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 0) :=
    ae_all_iff.2 fun k => Submission.idtp_dema_upper_density_zero P n μ (A k) (hAm k) hμfin
  -- Step 4: approximate tangent planes `Hⁿ`-a.e. on `M`
  have htan : ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), x ∈ M →
      ∃ Q, HasApproximateTangentSpaceAt n M x Q := by
    have h := R.orients
    rw [ae_restrict_iff' hMm] at h
    filter_upwards [h] with x hx hxM
    obtain ⟨Q, hQ, -⟩ := hx hxM
    exact ⟨Q, hQ⟩
  filter_upwards [hUD, htan] with x hxUD hxtan hxMW
  obtain ⟨hxM, hxW⟩ := hxMW
  obtain ⟨Q, hQ⟩ := hxtan hxM
  -- Step 5: a closed ball `B̄_s(x) ⊆ W`, on which `ν` and `Hⁿ⌞M` agree
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.1 hW x hxW
  have hs : 0 < r / 2 := by positivity
  have hsW : closedBall x (r / 2) ⊆ W := (closedBall_subset_ball (by linarith)).trans hrW
  have hloc : ∀ ρ : ℝ, ρ ≤ r / 2 → closedBall x ρ ∩ M' = M ∩ closedBall x ρ := by
    intro ρ hρ
    ext y
    simp only [hM', mem_inter_iff]
    constructor
    · rintro ⟨hyB, hyM, -⟩
      exact ⟨hyM, hyB⟩
    · rintro ⟨hyM, hyB⟩
      exact ⟨hyB, hyM, hsW (closedBall_subset_closedBall hρ hyB)⟩
  -- Step 5: `ν(B_ρ(x)) / (ωₙρⁿ) → 1`
  have hfinball : μHE[n] (M ∩ closedBall x (r / 2)) ≠ ∞ := by
    have h1 := hνle (closedBall x (r / 2)) measurableSet_closedBall
    have h2 := hμfin (closedBall x (r / 2)) (isCompact_closedBall x (r / 2))
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc _ le_rfl] at h1
    exact ne_top_of_le_ne_top h2 h1
  have hTD := Submission.rsd_tendsto_closedBall_density_of_approxTangent P n M x Q (r / 2) hs
    hfinball hQ
  have hTD' : Tendsto (fun ρ : ℝ => ν (closedBall x ρ) /
      (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 1) := by
    refine hTD.congr' ?_
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 (r / 2) := Ioo_mem_nhdsGT hs
    filter_upwards [hev] with ρ hρ
    rw [hν, Measure.restrict_apply measurableSet_closedBall, hloc ρ hρ.2.le]
  have hb := Submission.rsd_tendsto_ball_density_of_closedBall P n ν x 1 hTD'
  -- Step 6: split `B = B_ρ(x)` along the level `T = {θ = k}`, `k = θ(x)`
  set k : ℕ := R.mult x with hk
  have hxA : x ∉ A k := fun h => h.2 (by simp [hk])
  have he := hxUD k hxA
  set T : Set (Euclid P) := R.mult ⁻¹' {k} with hT
  have hTm : MeasurableSet T := R.measurable_mult (measurableSet_singleton k)
  have hset : ∀ ρ : ℝ, (ball x ρ ∩ M') \ T = (A k ∩ ball x ρ) ∩ M' := by
    intro ρ
    ext y
    simp only [hA, hT, mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff,
      mem_singleton_iff]
    tauto
  have hsplit : ∀ ρ : ℝ, μ (ball x ρ) =
      (k : ℝ≥0∞) * μHE[n] ((ball x ρ ∩ M') ∩ T) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hmeas _ measurableSet_ball, hmeas _ ((hAm k).inter measurableSet_ball),
      ← lintegral_inter_add_sdiff (B := T) _ _ hTm]
    congr 1
    · rw [setLIntegral_congr_fun ((measurableSet_ball.inter hM'm).inter hTm)
        (g := fun _ => (k : ℝ≥0∞)) (fun y hy => by
          have : R.mult y = k := hy.2
          simp [this])]
      simp
    · rw [hset ρ]
  have hνsplit : ∀ ρ : ℝ, ν (ball x ρ) =
      μHE[n] ((ball x ρ ∩ M') ∩ T) + ν (A k ∩ ball x ρ) := by
    intro ρ
    rw [hν, Measure.restrict_apply measurableSet_ball,
      Measure.restrict_apply ((hAm k).inter measurableSet_ball),
      ← measure_inter_add_sdiff (ball x ρ ∩ M') hTm, hset ρ]
  have hup : ∀ ρ : ℝ, μ (ball x ρ) ≤
      (k : ℝ≥0∞) * ν (ball x ρ) + μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hsplit ρ]
    have h1 : μHE[n] ((ball x ρ ∩ M') ∩ T) ≤ ν (ball x ρ) := by
      rw [hν, Measure.restrict_apply measurableSet_ball]
      exact measure_mono inter_subset_left
    exact add_le_add (mul_le_mul_right h1 _) le_rfl
  have hlow : ∀ ρ : ℝ, (k : ℝ≥0∞) * ν (ball x ρ) ≤
      μ (ball x ρ) + (k : ℝ≥0∞) * μ (A k ∩ ball x ρ) := by
    intro ρ
    rw [hνsplit ρ, mul_add, hsplit ρ, add_assoc]
    have h2 := hνle (A k ∩ ball x ρ) ((hAm k).inter measurableSet_ball)
    exact add_le_add le_rfl ((mul_le_mul_right h2 _).trans le_add_self)
  -- Step 7: the quantity in the statement is `μ(B_ρ(x))`
  have htarget : ∀ ρ : ℝ, R.measure (ball x ρ ∩ W) = μ (ball x ρ) := by
    intro ρ
    rw [hμ, Measure.restrict_apply measurableSet_ball]
  simp_rw [htarget]
  -- Step 7: squeeze between `k b(ρ) - k e(ρ)` and `k b(ρ) + e(ρ)`, both tending to `k`
  set c : ℝ → ℝ≥0∞ := fun ρ => unitBallVolume n * ENNReal.ofReal (ρ ^ n) with hc
  have hk_top : (k : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top k
  have hupper : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) +
      μ (A k ∩ ball x ρ) / c ρ) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have := (ENNReal.Tendsto.const_mul hb (Or.inr hk_top)).add he
    simpa using this
  have hlower : Tendsto (fun ρ => (k : ℝ≥0∞) * (ν (ball x ρ) / c ρ) -
      (k : ℝ≥0∞) * (μ (A k ∩ ball x ρ) / c ρ)) (𝓝[>] 0) (𝓝 (k : ℝ≥0∞)) := by
    have h1 := ENNReal.Tendsto.const_mul hb (Or.inr hk_top)
    have h2 := ENNReal.Tendsto.const_mul he (Or.inr hk_top)
    have := ENNReal.Tendsto.sub h1 h2 (Or.inl (by simp))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hupper (fun ρ => ?_) (fun ρ => ?_)
  · simp only
    rw [tsub_le_iff_right, ← mul_div_assoc, ← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hlow ρ) _
  · simp only
    rw [← mul_div_assoc, ← ENNReal.add_div]
    exact ENNReal.div_le_div_right (hup ρ) _

/-- **Density of `μ_R` localized to an open set** (Simon Ch. 3, Remark 1.5(3), Remark 1.8 and
Theorem 1.9, with Ch. 1, Theorem 3.6 and Remark 3.7(2)).  Let `R = (M, θ, ξ)` be an integer
multiplicity triple and `W` open with `μ_R(K ∩ W) < ∞` for compact `K`.  Then for `Hⁿ`-a.e. `x`,
`μ_R(B_ρ(x) ∩ W) / (ωₙρⁿ) → 1_{M ∩ W}(x) θ(x)` as `ρ ↓ 0`.  At `Hⁿ`-a.e. `x ∈ M ∩ W` this is
`Submission.dimred_tr_ida_density_on_carrier`.  Since `μ_R = θHⁿ⌞M` lives on `M`,
`μ_R(B_ρ(x) ∩ W) = (μ_R⌞W)((M ∩ W) ∩ B_ρ(x))`; the upper density theorem
`Submission.idtp_dema_upper_density_zero` for `μ_R⌞W` (finite on compact sets) and the Borel set
`M ∩ W` makes this `o(ρⁿ)` at `Hⁿ`-a.e. `x ∉ M ∩ W`. -/
theorem Submission.dimred_tr_imrep_density_ae : ∀ (P n : ℕ) (V W : Set (Euclid P)) (R : IMRep V n), IsOpen W → (∀ K : Set (Euclid P), IsCompact K → R.measure (K ∩ W) ≠ ∞) → ∀ᵐ x ∂(μHE[n] : Measure (Euclid P)), Tendsto (fun ρ : ℝ => R.measure (ball x ρ ∩ W) / (unitBallVolume n * ENNReal.ofReal (ρ ^ n))) (𝓝[>] 0) (𝓝 (Set.indicator (R.carrier ∩ W) (fun y => (R.mult y : ℝ≥0∞)) x)) := by
  intro P n V W R hW hfin
  have hWm : MeasurableSet W := hW.measurableSet
  have hMW : MeasurableSet (R.carrier ∩ W) := R.measurableSet_carrier.inter hWm
  -- Step 1: `μ := μ_R⌞W` is finite on compact sets
  have hfin' : ∀ K : Set (Euclid P), IsCompact K → R.measure.restrict W K ≠ ∞ := by
    intro K hK
    rw [Measure.restrict_apply' hWm]
    exact hfin K hK
  -- Step 2 (off the carrier): upper density theorem for `μ` and the Borel set `M ∩ W`
  have hoff := Submission.idtp_dema_upper_density_zero P n (R.measure.restrict W)
    (R.carrier ∩ W) hMW hfin'
  -- Steps 3–4 (on the carrier): density `θ(x)` at `Hⁿ`-a.e. `x ∈ M ∩ W`
  have hon := Submission.dimred_tr_ida_density_on_carrier P n V W R hW hfin
  -- Step 5: outside both exceptional sets, distinguish `x ∈ M ∩ W` and `x ∉ M ∩ W`
  filter_upwards [hoff, hon] with x hxoff hxon
  by_cases hx : x ∈ R.carrier ∩ W
  · rw [Set.indicator_of_mem hx]
    exact hxon hx
  · rw [Set.indicator_of_notMem hx]
    -- `μ_R(B_ρ(x) ∩ W) = μ((M ∩ W) ∩ B_ρ(x))`: both are `∫_{B_ρ(x) ∩ W ∩ M} θ dHⁿ`
    have heq : ∀ ρ : ℝ, R.measure (ball x ρ ∩ W) =
        R.measure.restrict W ((R.carrier ∩ W) ∩ ball x ρ) := by
      intro ρ
      rw [Measure.restrict_apply' hWm]
      simp only [IMRep.measure]
      rw [withDensity_apply _ (measurableSet_ball.inter hWm),
        withDensity_apply _ ((hMW.inter measurableSet_ball).inter hWm),
        Measure.restrict_restrict (measurableSet_ball.inter hWm),
        Measure.restrict_restrict ((hMW.inter measurableSet_ball).inter hWm)]
      congr 2
      ext y
      simp only [mem_inter_iff]
      tauto
    simp_rw [heq]
    exact hxoff hx

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
