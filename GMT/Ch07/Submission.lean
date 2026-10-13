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

/-- **Rescaled Gauss–Green identity** (Simon Ch. 3, 4.3 (8), for a general field and centre).
Let `F ⊆ ℝ^{m+1}` be Borel and suppose `∫_F div φ = −∫ ⟨φ, ν⟩ dμ` for every `C¹` compactly
supported `φ` with `tsupport φ ⊆ D`.  If `r > 0` and `B̄_{rR}(y) ⊆ D`, then for every `C¹`
compactly supported `g` with `tsupport g ⊆ B_R(0)` the blow-up `F_{y,r} = {w : y + rw ∈ F}`
satisfies `∫_{F_{y,r}} div g = −(r^m)⁻¹ ∫ ⟨g(r⁻¹(z − y)), ν(z)⟩ dμ(z)`.  Apply the hypothesis to
`φ = g ∘ S`, `S z = r⁻¹(z − y)`: `div φ = r⁻¹ (div g) ∘ S` by the chain rule,
`tsupport φ ⊆ S⁻¹(tsupport g) ⊆ B̄_{rR}(y)`, and the substitution `z = y + rw` (Jacobian
`r^{m+1}`) gives `∫_F div φ = r^m ∫_{F_{y,r}} div g`. -/
theorem Submission.codim1_rdo_dg_bh_rescaled_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → ∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -(r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by
  intro m D F μ ν y r R hF hGG hr hball g hg hgc hgs
  have hr0 : r ≠ 0 := hr.ne'
  -- Step 1: the affine map `S z = r⁻¹(z − y)`, inverse to `w ↦ y + rw`.
  set S : Euclid (m + 1) → Euclid (m + 1) := fun z => r⁻¹ • (z - y) with hS_def
  have hS_cont : Continuous S := (continuous_id.sub continuous_const).const_smul r⁻¹
  have hS_deriv : ∀ z, HasFDerivAt S (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) z :=
    fun z => ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const y).const_smul r⁻¹
  -- Step 2: `φ = g ∘ S` is `C¹` and `div φ = r⁻¹ (div g) ∘ S`.
  have hφ : ContDiff ℝ 1 (fun z => g (S z)) :=
    hg.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  have hdiv : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => g (S z)) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
      r⁻¹ * LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ g (S z) : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) := by
    intro z
    have hgd : HasFDerivAt g (fderiv ℝ g (S z)) (S z) :=
      ((hg.differentiable one_ne_zero) (S z)).hasFDerivAt
    rw [show (fun z => g (S z)) = g ∘ S from rfl, (hgd.comp z (hS_deriv z)).fderiv]
    have : (fderiv ℝ g (S z)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Euclid (m + 1))) =
        r⁻¹ • fderiv ℝ g (S z) := by
      ext x; simp
    rw [this, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
  -- Step 3: `φ` has compact support and `tsupport φ ⊆ S⁻¹(tsupport g) ⊆ B̄_{rR}(y) ⊆ D`.
  let e : Euclid (m + 1) ≃ₜ Euclid (m + 1) :=
    (Homeomorph.subRight y).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr0))
  have he : ⇑e = S := by funext z; rfl
  have hφc : HasCompactSupport (fun z => g (S z)) := by
    have := hgc.comp_homeomorph e
    rwa [he] at this
  have hφs : tsupport (fun z => g (S z)) ⊆ D := by
    intro z hz
    have hmem := hgs (tsupport_comp_subset_preimage g hS_cont hz)
    rw [mem_ball_zero_iff, hS_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    apply hball
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  -- Step 4: the Gauss–Green hypothesis for `φ`.
  have hGGφ := hGG (fun z => g (S z)) hφ hφc hφs
  -- Step 5: the substitution `z = y + rw`: `∫_F div φ = r^m ∫_{F_{y,r}} div g`.
  set Tg : Euclid (m + 1) → ℝ := fun w => LinearMap.trace ℝ (Euclid (m + 1))
    (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1))
  have hpre : MeasurableSet ((fun w => y + r • w) ⁻¹' F) :=
    (measurable_const.add (measurable_id.const_smul r)) hF
  have hcv : ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => g (S z)) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
      r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w := by
    simp_rw [hdiv]
    rw [← integral_indicator hF, ← integral_indicator hpre]
    have h1 : ∫ z, F.indicator (fun z => r⁻¹ * Tg (S z)) z =
        ∫ u, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u) :=
      (integral_add_left_eq_self _ y).symm
    have h2 := Measure.integral_comp_smul (μ := volume)
      (fun u => F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u)) r
    rw [finrank_euclideanSpace_fin] at h2
    have h3 : ∫ u, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + u) =
        r ^ (m + 1) * ∫ x, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + r • x) := by
      rw [h2, smul_eq_mul, ← mul_assoc, abs_inv, abs_of_pos (pow_pos hr _),
        mul_inv_cancel₀ (pow_ne_zero _ hr0), one_mul]
    rw [h1, h3]
    have h4 : ∀ x, F.indicator (fun z => r⁻¹ * Tg (S z)) (y + r • x) =
        r⁻¹ * ((fun w => y + r • w) ⁻¹' F).indicator Tg x := by
      intro x
      by_cases hx : y + r • x ∈ F
      · have hx' : x ∈ (fun w => y + r • w) ⁻¹' F := hx
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
        simp [hS_def, smul_smul, inv_mul_cancel₀ hr0]
      · have hx' : x ∉ (fun w => y + r • w) ⁻¹' F := hx
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', mul_zero]
    simp_rw [h4]
    rw [integral_const_mul, ← mul_assoc, pow_succ, mul_assoc (r ^ m), mul_inv_cancel₀ hr0, mul_one]
  -- Step 6: divide by `r^m > 0`.
  rw [hcv] at hGGφ
  calc ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w
      = (r ^ m)⁻¹ * (r ^ m * ∫ w in (fun w => y + r • w) ⁻¹' F, Tg w) := by field_simp
    _ = -(r ^ m)⁻¹ * ∫ z, inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by rw [hGGφ]; ring

/-- **Directional rescaled Gauss–Green identity** (Simon Ch. 3, 4.3, (8), for an arbitrary
direction `w` in place of `eᵢ`).  Let `(μ, ν)` satisfy the Gauss–Green identity
`∫_F div φ dL^{m+1} = −∫ ⟨φ, ν⟩ dμ` for `φ ∈ C¹_c` with `spt φ ⊆ D`, and let `r > 0`,
`B̄_{rR}(y) ⊆ D`.  For `ζ ∈ C¹_c` with `spt ζ ⊆ B_R(0)` and `w ∈ ℝ^{m+1}`, the field `g = ζ w` is
`C¹` with `spt g ⊆ spt ζ ⊆ B_R(0)`, `div g = Dζ(·)(w)` (the trace of the rank-one map
`h ↦ Dζ(h) w` is `Dζ(w)`) and `⟨g, ν⟩ = ζ ⟨w, ν⟩`.  The rescaled Gauss–Green identity for `g`
thus reads `∫_{F_{y,r}} Dζ(w) dL^{m+1} = −r⁻ᵐ ∫ ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩ dμ(z)`, where
`F_{y,r} = {x : y + r x ∈ F}`. -/
theorem Submission.codim1_rdo_dg_bh_directional_gauss_green : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (r R : ℝ), MeasurableSet F → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < r → closedBall y (r * R) ⊆ D → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R → ∀ w : Euclid (m + 1), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w = -(r ^ m)⁻¹ * ∫ z, ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ := by
  intro m D F μ ν y r R hF hGG hr hball ζ hζ hζc hζs w
  -- Step 1: `g = ζ w` is `C¹` with compact support and `spt g ⊆ spt ζ ⊆ B_R(0)`
  have hg : ContDiff ℝ 1 (fun z => ζ z • w) := hζ.smul contDiff_const
  have hgc : HasCompactSupport (fun z => ζ z • w) := hζc.smul_right (f' := fun _ => w)
  have hgs : tsupport (fun z => ζ z • w) ⊆ ball (0 : Euclid (m + 1)) R :=
    (tsupport_smul_subset_left ζ (fun _ => w)).trans hζs
  -- Step 2: `div g = Dζ(·)(w)`, the trace of the rank-one map `h ↦ Dζ(h) w`
  have h1 : ∀ z, LinearMap.trace ℝ (Euclid (m + 1))
      (fderiv ℝ (fun z => ζ z • w) z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = fderiv ℝ ζ z w := by
    intro z
    rw [fderiv_smul_const ((hζ.differentiable one_ne_zero) z) w]
    have : ((fderiv ℝ ζ z).smulRight w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) =
        (fderiv ℝ ζ z : Euclid (m + 1) →ₗ[ℝ] ℝ).smulRight w := by
      ext x; simp
    rw [this, LinearMap.trace_smulRight]
    rfl
  -- Step 3: `⟨g(r⁻¹(z − y)), ν(z)⟩ = ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩`
  have h2 : ∀ z, inner ℝ (ζ (r⁻¹ • (z - y)) • w) (ν z) = ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) :=
    fun z => real_inner_smul_left _ _ _
  -- Step 4: the rescaled Gauss–Green identity for `g`, with both integrands rewritten
  have key := Submission.codim1_rdo_dg_bh_rescaled_gauss_green m D F μ ν y r R hF hGG hr hball
    (fun z => ζ z • w) hg hgc hgs
  simp_rw [h1, h2] at key
  exact key
/-- **Small normal defect** (Simon Ch. 3, proof of Theorem 4.3 (De Giorgi), printed (1)–(2),
chapter-03.txt lines 609–619).  Let `ν` be a measurable unit vector field and `v` a unit vector,
let `μ(B̄_ρ₀(y)) < ∞` for some `ρ₀ > 0`, and let the averages `A(ρ) = μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ`
tend to `v` as `ρ ↓ 0`.  Then for every `δ > 0` and all small `ρ > 0`,
`∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ δ μ(B̄_ρ(y))` and `∫_{B̄_ρ(y)} |⟨ν, w⟩| dμ ≤ δ |w| μ(B̄_ρ(y))` for
every `w ⊥ v`.  The first bound is `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ = μ(B̄_ρ(y)) (1 - ⟨A(ρ), v⟩)`; the
second integrates `|⟨ν, w⟩| ≤ |w| |ν - v| ≤ |w| (δ/2 + (1 - ⟨ν, v⟩)/δ)`, where
`|ν - v|² = 2 (1 - ⟨ν, v⟩)`. -/
theorem Submission.codim1_rdo_dg_bh_normal_defect_small : ∀ (m : ℕ) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), Measurable ν → (∀ z, ‖ν z‖ = 1) → ‖v‖ = 1 → (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞) → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∀ δ : ℝ, 0 < δ → ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∫ z in closedBall y ρ, (1 - inner ℝ (ν z) v) ∂μ ≤ δ * (μ (closedBall y ρ)).toReal ∧ ∀ w : Euclid (m + 1), inner ℝ w v = 0 → ∫ z in closedBall y ρ, |inner ℝ (ν z) w| ∂μ ≤ δ * ‖w‖ * (μ (closedBall y ρ)).toReal := by
  intro m μ ν y v hν hν1 hv ⟨ρ₀, hρ₀, hfin⟩ hA δ hδ
  -- `⟨A(ρ), v⟩ → ⟨v, v⟩ = 1`
  have hε : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 1) := by
    have hcont : Continuous (fun x : Euclid (m + 1) => inner ℝ x v) :=
      continuous_id.inner continuous_const
    have := (hcont.tendsto v).comp hA
    rwa [real_inner_self_eq_norm_sq, hv, one_pow] at this
  -- eventually `ρ < ρ₀` and `1 - ⟨A(ρ), v⟩ < η = min δ (δ² / 2)`
  set η := min δ (δ ^ 2 / 2) with hη_def
  have hη : 0 < η := lt_min hδ (by positivity)
  have hηδ : η ≤ δ := min_le_left _ _
  have hηδ2 : η ≤ δ ^ 2 / 2 := min_le_right _ _
  have hev1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 1 - η < inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v :=
    hε.eventually (lt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioo 0 ρ₀ := Ioo_mem_nhdsGT hρ₀
  filter_upwards [hev1, hev2] with ρ h1 h2
  -- `μ(B̄_ρ(y)) < ∞`, so the bounded measurable integrands are integrable
  set B := closedBall y ρ with hB
  have hfinρ : μ B ≠ ∞ :=
    ne_top_of_le_ne_top hfin (measure_mono (closedBall_subset_closedBall h2.2.le))
  have : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.mpr hfinρ
  set M := (μ B).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hνint : Integrable ν (μ.restrict B) :=
    Integrable.of_bound hν.aestronglyMeasurable 1 (Eventually.of_forall fun z => (hν1 z).le)
  have hνv_meas : Measurable (fun z => inner ℝ (ν z) v) :=
    (continuous_id.inner continuous_const).measurable.comp hν
  have hνv : Integrable (fun z => inner ℝ (ν z) v) (μ.restrict B) := by
    refine Integrable.of_bound hνv_meas.aestronglyMeasurable 1 (Eventually.of_forall fun z => ?_)
    calc ‖inner ℝ (ν z) v‖ = |inner ℝ (ν z) v| := Real.norm_eq_abs _
      _ ≤ ‖ν z‖ * ‖v‖ := abs_real_inner_le_norm _ _
      _ = 1 := by rw [hν1, hv, one_mul]
  have hdefint : Integrable (fun z => 1 - inner ℝ (ν z) v) (μ.restrict B) :=
    (integrable_const 1).sub hνv
  -- `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ = M (1 - ⟨A(ρ), v⟩) ≤ M η`
  have hdef : ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := by
    rcases eq_or_ne M 0 with hM0' | hMne
    · have hμB : μ B = 0 := by
        rcases (ENNReal.toReal_eq_zero_iff _).mp hM0' with h | h
        · exact h
        · exact absurd h hfinρ
      rw [Measure.restrict_eq_zero.mpr hμB, integral_zero_measure, hM0', zero_mul]
    · have hinner : ∫ z in B, inner ℝ (ν z) v ∂μ = inner ℝ (∫ z in B, ν z ∂μ) v := by
        simp_rw [real_inner_comm v]
        have := (innerSL ℝ v).integral_comp_comm hνint
        simpa using this
      rw [integral_sub (integrable_const 1) hνv, hinner, integral_const, smul_eq_mul, mul_one]
      simp only [Measure.real, Measure.restrict_apply_univ]
      have hA' : inner ℝ (∫ z in B, ν z ∂μ) v = M * inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v := by
        rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hMne, one_mul]
      rw [hA']
      have : 1 - inner ℝ (M⁻¹ • ∫ z in B, ν z ∂μ) v ≤ η := by linarith
      nlinarith
  refine ⟨?_, ?_⟩
  · calc ∫ z in B, (1 - inner ℝ (ν z) v) ∂μ ≤ M * η := hdef
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hηδ hM0
      _ = δ * M := mul_comm _ _
  · intro w hw
    -- pointwise `|⟨ν, w⟩| ≤ |w| |ν - v| ≤ |w| (δ/2 + (1 - ⟨ν, v⟩)/δ)` for `w ⊥ v`
    have hpt : ∀ z, |inner ℝ (ν z) w| ≤ ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) := by
      intro z
      have e1 : inner ℝ (ν z) w = inner ℝ (ν z - v) w := by
        rw [inner_sub_left, real_inner_comm w v, hw, sub_zero]
      have e2 : ‖ν z - v‖ ^ 2 = 2 - 2 * inner ℝ (ν z) v := by
        rw [norm_sub_sq_real, hν1, hv]; ring
      have e3 : ‖ν z - v‖ ≤ δ / 2 + (1 - inner ℝ (ν z) v) / δ := by
        have ht := sq_nonneg (‖ν z - v‖ - δ)
        have : (1 - inner ℝ (ν z) v) / δ = ‖ν z - v‖ ^ 2 / (2 * δ) := by
          rw [e2]; field_simp
        rw [this, div_add_div _ _ (two_ne_zero) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith
      rw [e1]
      calc |inner ℝ (ν z - v) w| ≤ ‖ν z - v‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ ≤ (δ / 2 + (1 - inner ℝ (ν z) v) / δ) * ‖w‖ :=
            mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
        _ = _ := mul_comm _ _
    have hint1 : Integrable (fun z => |inner ℝ (ν z) w|) (μ.restrict B) := by
      refine Integrable.of_bound
        ((continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp
          hν).aestronglyMeasurable ‖w‖
        (Eventually.of_forall fun z => ?_)
      rw [Real.norm_eq_abs, abs_abs]
      calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
        _ = ‖w‖ := by rw [hν1, one_mul]
    have hint2 : Integrable (fun z => ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ)) (μ.restrict B) :=
      ((integrable_const (δ / 2)).add (hdefint.div_const δ)).const_mul ‖w‖
    -- integrate, then use `∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ M η ≤ M δ² / 2`
    calc ∫ z in B, |inner ℝ (ν z) w| ∂μ
        ≤ ∫ z in B, ‖w‖ * (δ / 2 + (1 - inner ℝ (ν z) v) / δ) ∂μ :=
          integral_mono hint1 hint2 hpt
      _ = ‖w‖ * (δ / 2 * M + (∫ z in B, (1 - inner ℝ (ν z) v) ∂μ) / δ) := by
          rw [integral_const_mul, integral_add (integrable_const _) (hdefint.div_const δ),
            integral_const, integral_div, smul_eq_mul]
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
      _ ≤ ‖w‖ * (δ / 2 * M + M * η / δ) := by
          gcongr
      _ ≤ ‖w‖ * (δ / 2 * M + M * (δ ^ 2 / 2) / δ) := by
          gcongr
      _ = δ * ‖w‖ * M := by
          field_simp
          ring
/-- **Uniform perimeter bound for the blow-ups** (Simon Ch. 3, 4.3 (6)–(8): the bound that lets
the compactness theorem Ch. 2, 2.6 select an `L¹_loc`-convergent sequence of blow-ups).  Let
`∫_F div φ = -∫ ⟨φ, ν⟩ dμ` for `φ ∈ C¹_c` with `spt φ ⊆ D`, where `|ν| = 1`, and let
`B̄_{ρ₁}(y) ⊆ D` and `μ(B̄_ρ(y)) ≤ C₁ρᵐ` for `0 < ρ < ρ₁`.  If `rR < ρ₁`, `g ∈ C¹_c(B_R(0))` and
`|g| ≤ 1`, then `∫_{F_{y,r}} div g ≤ C₁Rᵐ`, where `F_{y,r} = {w : y + rw ∈ F}`.  As
`B̄_{rR}(y) ⊆ D`, the rescaled Gauss–Green identity gives `∫_{F_{y,r}} div g = -r⁻ᵐ ∫ h dμ` with
`h(z) = ⟨g(r⁻¹(z - y)), ν(z)⟩`; `|h| ≤ 1` and `h` vanishes off `K = B̄_{rR}(y)`, so
`|∫ h dμ| ≤ μ(K) ≤ C₁(rR)ᵐ` and `-r⁻ᵐ ∫ h dμ ≤ C₁Rᵐ`. -/
theorem Submission.codim1_rdo_dg_bh_perimeter_bound : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ R r : ℝ, 0 < R → 0 < r → r * R < ρ₁ → ∀ g : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 g → HasCompactSupport g → tsupport g ⊆ ball (0 : Euclid (m + 1)) R → (∀ z, ‖g z‖ ≤ 1) → ∫ w in (fun w => y + r • w) ⁻¹' F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ g w : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) ≤ C₁ * R ^ m := by
  intro m D F μ ν y ρ₁ C₁ hF hν hν1 hGG hρ₁ hC₁ hball hmass R r hR hr hrR g hg hgc hgs hg1
  -- Step 1: `B̄_{rR}(y) ⊆ B̄_{ρ₁}(y) ⊆ D`, so the rescaled Gauss–Green identity applies to `g`
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall hrR.le).trans hball
  rw [Submission.codim1_rdo_dg_bh_rescaled_gauss_green m D F μ ν y r R hF hGG hr hsub g hg hgc hgs]
  -- Step 2: `h(z) = ⟨g(r⁻¹(z - y)), ν(z)⟩` vanishes off `B̄_{rR}(y)`, as `spt g ⊆ B_R(0)`
  have hzero : ∀ z, z ∉ closedBall y (r * R) → inner ℝ (g (r⁻¹ • (z - y))) (ν z) = 0 := by
    intro z hz
    have hgz : g (r⁻¹ • (z - y)) = 0 := by
      by_contra hne
      apply hz
      have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hgs (subset_tsupport _ hne)
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_lt_iff₀ hr] at hmem
      rw [mem_closedBall, dist_eq_norm]
      exact hmem.le
    rw [hgz, inner_zero_left]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 3: `μ(B̄_{rR}(y)) ≤ C₁(rR)ᵐ < ∞` and `|h| ≤ |g| |ν| ≤ 1`, so `|∫ h dμ| ≤ C₁(rR)ᵐ`
  have hK : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) :=
    hmass _ (mul_pos hr hR) hrR
  have hbound : ‖∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ‖ ≤
      1 * μ.real (closedBall y (r * R)) := by
    refine norm_setIntegral_le_of_norm_le_const (hK.trans_lt ENNReal.ofReal_lt_top) fun z _ => ?_
    calc ‖inner ℝ (g (r⁻¹ • (z - y))) (ν z)‖ = |inner ℝ (g (r⁻¹ • (z - y))) (ν z)| :=
          Real.norm_eq_abs _
      _ ≤ ‖g (r⁻¹ • (z - y))‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [hν1, mul_one]; exact hg1 _
  have hμK : μ.real (closedBall y (r * R)) ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hK
  rw [Real.norm_eq_abs, one_mul] at hbound
  have hneg := (abs_le.mp hbound).1
  -- Step 4: `-r⁻ᵐ ∫ h dμ ≤ r⁻ᵐ C₁(rR)ᵐ = C₁Rᵐ`
  have hrm : 0 < r ^ m := pow_pos hr m
  calc -(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ
      = (r ^ m)⁻¹ * -∫ z in closedBall y (r * R), inner ℝ (g (r⁻¹ • (z - y))) (ν z) ∂μ := by
        ring
    _ ≤ (r ^ m)⁻¹ * (C₁ * (r * R) ^ m) :=
        mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hrm.le)
    _ = C₁ * R ^ m := by rw [mul_pow]; field_simp

/-- **Simon Ch. 3, proof of 4.3, (8)** ("so that `∫_{λ_k⁻¹E} Dᵢζ dL^{n+1} → 0` by (2) for
`i = 1, …, n`"): derivatives of `ζ ∈ C¹_c(ℝ^{m+1})` in directions `w ⊥ v` integrate to `0` over
the blow-ups `F_{y,r} = {x : y + rx ∈ F}` as `r ↓ 0`.  Take `R > 0` with `spt ζ ⊆ B_R(0)` and
`M = sup |ζ|`.  For small `r`, `ρ = rR < ρ₁`, so `B̄_ρ(y) ⊆ D` and the directional Gauss–Green
identity (`codim1_rdo_dg_bh_directional_gauss_green`) gives
`∫_{F_{y,r}} Dζ(w) = −r⁻ᵐ ∫ ζ(r⁻¹(z − y)) ⟨w, ν(z)⟩ dμ(z)`, whose integrand vanishes off `B̄_ρ(y)`
and is bounded by `M |⟨ν, w⟩|`.  The normal-defect estimate (2)
(`codim1_rdo_dg_bh_normal_defect_small`, applicable as `μ(B̄_{ρ₁/2}(y)) ≤ C₁(ρ₁/2)ᵐ < ∞`) gives
`∫_{B̄_ρ(y)} |⟨ν, w⟩| dμ ≤ δ|w| μ(B̄_ρ(y)) ≤ δ|w|C₁ρᵐ` for small `ρ`, hence
`|∫_{F_{y,r}} Dζ(w)| ≤ δM|w|C₁Rᵐ`, which is `< η` for `δ = η/(1 + M|w|C₁Rᵐ)`. -/
theorem Submission.codim1_rdo_dg_bh_tangential_vanish : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → ∀ w : Euclid (m + 1), inner ℝ w v = 0 → Tendsto (fun r : ℝ => ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z w) (𝓝[>] 0) (𝓝 0) := by
  intro m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA hρ₁ hC₁ hball hmass ζ hζ hζc w hw
  -- Step 1: `spt ζ ⊆ B_R(0)` with `R > 0`, and `|ζ| ≤ M`
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
  set R := max R₀ 1
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R :=
    hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ζ z‖ ≤ M := hζ.continuous.bounded_above_of_compact_support hζc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM' : ∀ z, |ζ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  -- Step 2: `μ(B̄_{ρ₁/2}(y)) < ∞`, and `r ↦ rR` maps `𝓝[>] 0` into `𝓝[>] 0`
  have hfin : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞ :=
    ⟨ρ₁ / 2, half_pos hρ₁, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass _ (half_pos hρ₁) (half_lt_self hρ₁))⟩
  have htend : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * R < ρ₁ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hρ₁)
  -- Step 3: given `η > 0`, apply (2) with `δ = η/(1 + K)`, `K = M|w|C₁Rᵐ`, at `ρ = rR`
  set K := M * ‖w‖ * C₁ * R ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ := η / (1 + K) with hδ_def
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hnd := htend.eventually
    (Submission.codim1_rdo_dg_bh_normal_defect_small m μ ν y v hν hν1 hv hfin hA δ hδ)
  filter_upwards [hnd, hsmall, self_mem_nhdsWithin] with r h1 h2 h3
  have hr : 0 < r := h3
  have hrR : 0 < r * R := mul_pos hr hRpos
  -- Step 4: `B̄_{rR}(y) ⊆ D` and `μ(B̄_{rR}(y)) ≤ C₁(rR)ᵐ < ∞`
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall h2.le).trans hball
  have hBfin : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) := hmass _ hrR h2
  have hBlt : μ (closedBall y (r * R)) < ∞ := hBfin.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (closedBall y (r * R))) :=
    isFiniteMeasure_restrict.mpr hBlt.ne
  have hμB : (μ (closedBall y (r * R))).toReal ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBfin
  -- Step 5: the directional Gauss–Green identity; its integrand vanishes off `B̄_{rR}(y)`
  have hζz : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hR (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [dist_zero_right, Submission.codim1_rdo_dg_bh_directional_gauss_green m D F μ ν y r R hF hGG hr
    hsub ζ hζ hζc hR w]
  have hzero : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) = 0 := by
    intro z hz
    rw [hζz z hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 6: `|∫ ζ(r⁻¹(z − y)) ⟨w, ν⟩ dμ| ≤ M ∫_{B̄_{rR}(y)} |⟨ν, w⟩| dμ ≤ Mδ|w|C₁(rR)ᵐ`
  have hνw : Measurable (fun z => |inner ℝ (ν z) w|) :=
    (continuous_abs.comp (continuous_id.inner continuous_const)).measurable.comp hν
  have hint : Integrable (fun z => M * |inner ℝ (ν z) w|) (μ.restrict (closedBall y (r * R))) := by
    refine (Integrable.of_bound hνw.aestronglyMeasurable ‖w‖
      (Eventually.of_forall fun z => ?_)).const_mul M
    rw [Real.norm_eq_abs, abs_abs]
    calc |inner ℝ (ν z) w| ≤ ‖ν z‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ = ‖w‖ := by rw [hν1, one_mul]
  have hb1 : ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ ≤
      ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ := by
    apply norm_integral_le_of_norm_le hint
    refine Eventually.of_forall fun z => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, real_inner_comm]
    exact mul_le_mul_of_nonneg_right (hM' _) (abs_nonneg _)
  have hb2 : ∫ z in closedBall y (r * R), M * |inner ℝ (ν z) w| ∂μ ≤
      M * (δ * ‖w‖ * (C₁ * (r * R) ^ m)) := by
    rw [integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hM0
    calc ∫ z in closedBall y (r * R), |inner ℝ (ν z) w| ∂μ
        ≤ δ * ‖w‖ * (μ (closedBall y (r * R))).toReal := h1.2 w hw
      _ ≤ δ * ‖w‖ * (C₁ * (r * R) ^ m) := by gcongr
  -- Step 7: `r⁻ᵐ · Mδ|w|C₁(rR)ᵐ = δK < η`
  have hnorm : ‖-(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ =
      (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖ := by
    rw [norm_mul, norm_neg, norm_inv, Real.norm_eq_abs (r ^ m), abs_of_pos hrm]
  rw [hnorm]
  calc (r ^ m)⁻¹ * ‖∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ w (ν z) ∂μ‖
      ≤ (r ^ m)⁻¹ * (M * (δ * ‖w‖ * (C₁ * (r * R) ^ m))) := by
        gcongr
        exact hb1.trans hb2
    _ = δ * K := by rw [hK, mul_pow]; field_simp
    _ < η := by
        rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Simon Ch. 3, 4.3, proof of (9): the normal derivatives of the blow-ups `F_{y,r}` are
asymptotically nonpositive.  Take `tsupport ζ ⊆ B_R(0)`, `M ≥ sup ζ` and `δ' = δ / (1 + M C₁ Rᵐ)`.
For small `r`, `directional_gauss_green` (with `w = v`, `ρ = rR`) and the pointwise bound
`-ζ⟨v, ν⟩ ≤ M (1 - ⟨ν, v⟩)` on `B̄_ρ(y)` give
`∫_{F_{y,r}} Dζ(v) ≤ r⁻ᵐ M ∫_{B̄_ρ(y)} (1 - ⟨ν, v⟩) dμ ≤ r⁻ᵐ M δ' μ(B̄_ρ(y)) ≤ M δ' C₁ Rᵐ ≤ δ`,
by `normal_defect_small` and `μ(B̄_ρ(y)) ≤ C₁ρᵐ`. -/
theorem Submission.codim1_rdo_dg_bh_normal_limsup : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)) (ρ₁ C₁ : ℝ), MeasurableSet F → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → 0 < ρ₁ → 0 ≤ C₁ → closedBall y ρ₁ ⊆ D → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C₁ * ρ ^ m)) → ∀ ζ : Euclid (m + 1) → ℝ, ContDiff ℝ 1 ζ → HasCompactSupport ζ → (∀ z, 0 ≤ ζ z) → ∀ δ : ℝ, 0 < δ → ∀ᶠ r in 𝓝[>] (0 : ℝ), ∫ z in (fun z => y + r • z) ⁻¹' F, fderiv ℝ ζ z v ≤ δ := by
  intro m D F μ ν y v ρ₁ C₁ hF hν hν1 hGG hv hA hρ₁ hC₁ hball hmass ζ hζ hζc hζ0 δ hδ
  -- Step 1: `tsupport ζ ⊆ B_R(0)` with `R ≥ 1`, `|ζ| ≤ M`, and `δ' = δ / (1 + M C₁ Rᵐ)`
  obtain ⟨R₀, hR₀⟩ := hζc.isCompact.isBounded.subset_ball (0 : Euclid (m + 1))
  set R := max R₀ 1 with hR_def
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hR : tsupport ζ ⊆ ball (0 : Euclid (m + 1)) R :=
    hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖ζ z‖ ≤ M := hζ.continuous.bounded_above_of_compact_support hζc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM' : ∀ z, |ζ z| ≤ M := fun z => by simpa [Real.norm_eq_abs] using hM z
  set K := M * C₁ * R ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  set δ' := δ / (1 + K) with hδ'_def
  have hδ' : 0 < δ' := div_pos hδ (by linarith)
  -- Step 2: the normal defect on `B̄_ρ(y)` is at most `δ' μ(B̄_ρ(y))` for small `ρ = rR`
  have hfin : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ μ (closedBall y ρ₀) ≠ ∞ :=
    ⟨ρ₁ / 2, half_pos hρ₁, ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass _ (half_pos hρ₁) (half_lt_self hρ₁))⟩
  have htend : Tendsto (fun r : ℝ => r * R) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun r : ℝ => r * R) (𝓝 0) (𝓝 (0 * R)) := tendsto_id.mul_const R
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hRpos
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r * R < ρ₁ :=
    (htend.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds hρ₁)
  have hnd := htend.eventually
    (Submission.codim1_rdo_dg_bh_normal_defect_small m μ ν y v hν hν1 hv hfin hA δ' hδ')
  filter_upwards [hnd, hsmall, self_mem_nhdsWithin] with r h1 h2 h3
  have hr : 0 < r := h3
  have hrR : 0 < r * R := mul_pos hr hRpos
  have hsub : closedBall y (r * R) ⊆ D := (closedBall_subset_closedBall h2.le).trans hball
  have hBfin : μ (closedBall y (r * R)) ≤ ENNReal.ofReal (C₁ * (r * R) ^ m) := hmass _ hrR h2
  have hBlt : μ (closedBall y (r * R)) < ∞ := hBfin.trans_lt ENNReal.ofReal_lt_top
  have : IsFiniteMeasure (μ.restrict (closedBall y (r * R))) :=
    isFiniteMeasure_restrict.mpr hBlt.ne
  have hμB : (μ (closedBall y (r * R))).toReal ≤ C₁ * (r * R) ^ m :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hBfin
  -- Step 3: the rescaled identity, with `s(z) = ζ(r⁻¹(z - y))` vanishing off `B̄_ρ(y)`
  have hζz : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) = 0 := by
    intro z hz
    by_contra hne
    apply hz
    have hmem : r⁻¹ • (z - y) ∈ ball (0 : Euclid (m + 1)) R := hR (subset_tsupport _ hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr] at hmem
    rw [mem_closedBall, dist_eq_norm]
    have := (inv_mul_lt_iff₀ hr).mp hmem
    linarith
  have hζmeas : Measurable (fun z : Euclid (m + 1) => ζ (r⁻¹ • (z - y))) :=
    (hζ.continuous.comp ((continuous_id.sub continuous_const).const_smul r⁻¹)).measurable
  have hrm : 0 < r ^ m := pow_pos hr m
  rw [Submission.codim1_rdo_dg_bh_directional_gauss_green m D F μ ν y r R hF hGG hr
    hsub ζ hζ hζc hR v]
  have hzero : ∀ z, z ∉ closedBall y (r * R) → ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) = 0 := by
    intro z hz
    rw [hζz z hz, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  -- Step 4: `-s⟨v, ν⟩ ≤ M (1 - ⟨ν, v⟩)`, both sides bounded on the finite ball
  have hνv : Measurable (fun z => inner ℝ (ν z) v) :=
    (continuous_id.inner continuous_const).measurable.comp hν
  have hνv' : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hν
  have hint_l : Integrable (fun z => ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z))
      (μ.restrict (closedBall y (r * R))) := by
    refine Integrable.of_bound (hζmeas.mul hνv').aestronglyMeasurable M
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have : |inner ℝ v (ν z)| ≤ 1 :=
      (abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul])
    calc |ζ (r⁻¹ • (z - y))| * |inner ℝ v (ν z)| ≤ M * 1 := by
          gcongr
          exact hM' _
      _ = M := mul_one M
  have hint_d : Integrable (fun z => 1 - inner ℝ (ν z) v) (μ.restrict (closedBall y (r * R))) := by
    refine (integrable_const 1).sub (Integrable.of_bound hνv.aestronglyMeasurable 1
      (Eventually.of_forall fun z => ?_))
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul])
  have hpt : ∀ z, -(ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z)) ≤ M * (1 - inner ℝ (ν z) v) := by
    intro z
    have hs0 := hζ0 (r⁻¹ • (z - y))
    have hsM : ζ (r⁻¹ • (z - y)) ≤ M := (le_abs_self _).trans (hM' _)
    have hin : inner ℝ (ν z) v ≤ 1 :=
      (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by rw [hν1, hv, one_mul]))
    rw [real_inner_comm]
    nlinarith
  -- Step 5: integrate and use `μ(B̄_ρ(y)) ≤ C₁ρᵐ`
  have hmain : -∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ ≤
      M * ∫ z in closedBall y (r * R), (1 - inner ℝ (ν z) v) ∂μ := by
    rw [← integral_neg, ← integral_const_mul]
    exact integral_mono hint_l.neg (hint_d.const_mul M) hpt
  have hdef : ∫ z in closedBall y (r * R), (1 - inner ℝ (ν z) v) ∂μ ≤ δ' * (C₁ * (r * R) ^ m) :=
    h1.1.trans (by gcongr)
  -- Step 6: `r⁻ᵐ M δ' C₁ (rR)ᵐ = δ' M C₁ Rᵐ ≤ δ`
  calc -(r ^ m)⁻¹ * ∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ
      = (r ^ m)⁻¹ * (-∫ z in closedBall y (r * R), ζ (r⁻¹ • (z - y)) * inner ℝ v (ν z) ∂μ) := by
        ring
    _ ≤ (r ^ m)⁻¹ * (M * (δ' * (C₁ * (r * R) ^ m))) := by
        gcongr
        exact hmain.trans (mul_le_mul_of_nonneg_left hdef hM0)
    _ = δ' * K := by rw [hK, mul_pow]; field_simp
    _ ≤ δ := by
        rw [hδ'_def, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
/-- **Scale invariance of the two-sided volume density bounds** (Simon Ch. 3, 4.3 (10)–(11)): if
`L(F ∩ B_ρ(y)) ≥ c₂ρ^{m+1}` and `L(B_ρ(y) \ F) ≥ c₂ρ^{m+1}` for `0 < ρ < ρ₂`, then the rescaled set
`F_{y,r} = {w : y + rw ∈ F}` satisfies the same bounds on `B_s(0)` whenever `rs < ρ₂`.  The map
`w ↦ y + rw` scales Lebesgue measure by `r^{m+1}` and pulls `B_{rs}(y)` back to `B_s(0)`. -/
theorem Submission.codim1_rdo_dg_bh_rescaled_volume_lower : ∀ (m : ℕ) (F : Set (Euclid (m + 1))) (y : Euclid (m + 1)) (c₂ ρ₂ : ℝ), MeasurableSet F → (∀ ρ : ℝ, 0 < ρ → ρ < ρ₂ → ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (F ∩ ball y ρ) ∧ ENNReal.ofReal (c₂ * ρ ^ (m + 1)) ≤ volume (ball y ρ \ F)) → ∀ s r : ℝ, 0 < s → 0 < r → r * s < ρ₂ → ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume ((fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s) ∧ ENNReal.ofReal (c₂ * s ^ (m + 1)) ≤ volume (ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F) := by
  intro m F y c₂ ρ₂ _ hvol s r hs hr hrs
  -- `L((y + r ·)⁻¹' S) = r^{-(m+1)} L(S)`: Haar scaling, then translation invariance
  have hscale : ∀ S : Set (Euclid (m + 1)), volume ((fun w => y + r • w) ⁻¹' S) =
      ENNReal.ofReal (|r ^ (m + 1)|⁻¹) * volume S := by
    intro S
    have : (fun w => y + r • w) ⁻¹' S = (r • ·) ⁻¹' ((fun u => y + u) ⁻¹' S) := rfl
    rw [this, Measure.addHaar_preimage_smul volume hr.ne', finrank_euclideanSpace_fin,
      measure_preimage_add, abs_inv]
  -- `|(y + rw) − y| = r|w|`, so `(y + r ·)⁻¹' B_{rs}(y) = B_s(0)`
  have hball : (fun w => y + r • w) ⁻¹' ball y (r * s) = ball (0 : Euclid (m + 1)) s := by
    ext w
    simp only [Set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_mul_iff_right₀ hr
  -- the hypothesis at `ρ = rs`, and both sets as preimages of the unscaled ones
  obtain ⟨h1, h2⟩ := hvol (r * s) (mul_pos hr hs) hrs
  have e1 : (fun w => y + r • w) ⁻¹' F ∩ ball (0 : Euclid (m + 1)) s =
      (fun w => y + r • w) ⁻¹' (F ∩ ball y (r * s)) := by rw [Set.preimage_inter, hball]
  have e2 : ball (0 : Euclid (m + 1)) s \ (fun w => y + r • w) ⁻¹' F =
      (fun w => y + r • w) ⁻¹' (ball y (r * s) \ F) := by rw [Set.preimage_sdiff, hball]
  -- `r^{-(m+1)} · c₂(rs)^{m+1} = c₂s^{m+1}` in `[0, ∞]` (both sides `0` if `c₂ ≤ 0`)
  have hfac : ENNReal.ofReal (c₂ * s ^ (m + 1)) =
      ENNReal.ofReal (|r ^ (m + 1)|⁻¹) * ENNReal.ofReal (c₂ * (r * s) ^ (m + 1)) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [abs_of_pos (pow_pos hr _), mul_pow]
    field_simp
  rw [e1, e2, hscale, hscale, hfac]
  exact ⟨by gcongr, by gcongr⟩
/-- **`L¹_loc` transfer** (the passage to the blow-up limit in Simon Ch. 3, 4.3 (7), and in the
volume bounds fixing `λ = 0` after (9)): if `L^{m+1}((F_k Δ F₀) ∩ B_R(0)) → 0` for every `R`,
then `∫_{F_k} f → ∫_{F₀} f` for continuous compactly supported `f`
(`|∫_{F_k} f − ∫_{F₀} f| ≤ sup |f| · L^{m+1}((F_k Δ F₀) ∩ B_R(0))` once `spt f ⊆ B_R(0)`), and
`L^{m+1}(F_k ∩ B_s(0))`, `L^{m+1}(B_s(0) \ F_k)` converge to the values for `F₀`, each differing
from its limit by at most `L^{m+1}((F_k Δ F₀) ∩ B_s(0))`. -/
theorem Submission.codim1_rdo_dg_bh_l1loc_transfer : ∀ (m : ℕ) (Fs : ℕ → Set (Euclid (m + 1))) (F₀ : Set (Euclid (m + 1))), (∀ k, MeasurableSet (Fs k)) → MeasurableSet F₀ → (∀ R : ℝ, Tendsto (fun k => volume (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R)) atTop (𝓝 0)) → (∀ f : Euclid (m + 1) → ℝ, Continuous f → HasCompactSupport f → Tendsto (fun k => ∫ z in Fs k, f z) atTop (𝓝 (∫ z in F₀, f z))) ∧ (∀ s : ℝ, Tendsto (fun k => volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)) atTop (𝓝 (volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)))) ∧ ∀ s : ℝ, Tendsto (fun k => volume (ball (0 : Euclid (m + 1)) s \ Fs k)) atTop (𝓝 (volume (ball (0 : Euclid (m + 1)) s \ F₀))) := by
  intro m Fs F₀ hFs hF₀ hconv
  -- `a k → b` in `[0, ∞]` once `b < ∞` and `a k ≤ b + e k`, `b ≤ a k + e k` with `e k → 0`
  have key : ∀ (a : ℕ → ℝ≥0∞) (b : ℝ≥0∞) (e : ℕ → ℝ≥0∞), b ≠ ∞ → Tendsto e atTop (𝓝 0) →
      (∀ k, a k ≤ b + e k) → (∀ k, b ≤ a k + e k) → Tendsto a atTop (𝓝 b) := by
    intro a b e hb he h1 h2
    rw [ENNReal.tendsto_nhds hb]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with k hk
    constructor
    · rw [tsub_le_iff_right]
      exact (h2 k).trans (by gcongr)
    · exact (h1 k).trans (by gcongr)
  refine ⟨?_, ?_, ?_⟩
  · intro f hf hfc
    obtain ⟨R, hR⟩ : ∃ R, tsupport f ⊆ ball (0 : Euclid (m + 1)) R :=
      hfc.isCompact.isBounded.subset_ball 0
    obtain ⟨M, hM⟩ : ∃ M, ∀ z, ‖f z‖ ≤ M := hf.bounded_above_of_compact_support hfc
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    have hM' : ∀ z, |f z| ≤ M := fun z => by rw [← Real.norm_eq_abs]; exact hM z
    have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
    set E : ℕ → Set (Euclid (m + 1)) := fun k => symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) R
    have hEm : ∀ k, MeasurableSet (E k) := fun k =>
      ((hFs k).symmDiff hF₀).inter measurableSet_ball
    have hEfin : ∀ k, volume (E k) ≠ ∞ := fun k =>
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    -- `|1_{F_k} f − 1_{F₀} f| ≤ M · 1_{E k}`, as `f = 0` off `B_R(0)`
    have hbound : ∀ k, ‖(∫ z in Fs k, f z) - ∫ z in F₀, f z‖ ≤ M * (volume (E k)).toReal := by
      intro k
      rw [← integral_indicator (hFs k), ← integral_indicator hF₀,
        ← integral_sub (hfi.indicator (hFs k)) (hfi.indicator hF₀)]
      have hgi : Integrable ((E k).indicator (fun _ => M)) :=
        (integrableOn_const (hEfin k)).integrable_indicator (hEm k)
      calc ‖∫ z, ((Fs k).indicator f z - F₀.indicator f z)‖
          ≤ ∫ z, (E k).indicator (fun _ => M) z := by
            refine norm_integral_le_of_norm_le hgi (Eventually.of_forall fun z => ?_)
            by_cases hz : z ∈ E k
            · rw [Set.indicator_of_mem hz]
              by_cases h1 : z ∈ Fs k <;> by_cases h2 : z ∈ F₀ <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2, hM0, hM' z]
            · rw [Set.indicator_of_notMem hz, norm_le_zero_iff, sub_eq_zero]
              by_cases hzR : z ∈ ball (0 : Euclid (m + 1)) R
              · -- `z ∉ F_k Δ F₀`, so `z ∈ F_k ↔ z ∈ F₀`
                have hzs : z ∉ symmDiff (Fs k) F₀ := fun h => hz ⟨h, hzR⟩
                rw [Set.mem_symmDiff, not_or, not_and_not_right, not_and_not_right] at hzs
                by_cases h1 : z ∈ Fs k
                · rw [Set.indicator_of_mem h1, Set.indicator_of_mem (hzs.1 h1)]
                · rw [Set.indicator_of_notMem h1,
                    Set.indicator_of_notMem fun h2 => h1 (hzs.2 h2)]
              · have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzR (hR h)
                rw [Set.indicator_apply_eq_zero.2 fun _ => hfz,
                  Set.indicator_apply_eq_zero.2 fun _ => hfz]
        _ = M * (volume (E k)).toReal := by
            rw [integral_indicator_const _ (hEm k), smul_eq_mul, mul_comm, measureReal_def]
    have hlim : Tendsto (fun k => M * (volume (E k)).toReal) atTop (𝓝 0) := by
      simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hconv R)).const_mul M
    rw [← tendsto_sub_nhds_zero_iff]
    exact squeeze_zero_norm hbound hlim
  · intro s
    have hb : volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.inter_subset_right)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (Fs k ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((F₀ ∩ ball (0 : Euclid (m + 1)) s) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ F₀
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (F₀ ∩ ball (0 : Euclid (m + 1)) s)
          ≤ volume ((Fs k ∩ ball (0 : Euclid (m + 1)) s) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ Fs k
            · exact Or.inl ⟨h, hz.2⟩
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨hz.1, h⟩), hz.2⟩
        _ ≤ _ := measure_union_le _ _
  · intro s
    have hb : volume (ball (0 : Euclid (m + 1)) s \ F₀) ≠ ∞ :=
      ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono Set.sdiff_subset)
    refine key _ _ _ hb (hconv s) (fun k => ?_) (fun k => ?_)
    · calc volume (ball (0 : Euclid (m + 1)) s \ Fs k)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ F₀) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ F₀
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inr ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
    · calc volume (ball (0 : Euclid (m + 1)) s \ F₀)
          ≤ volume ((ball (0 : Euclid (m + 1)) s \ Fs k) ∪
              (symmDiff (Fs k) F₀ ∩ ball (0 : Euclid (m + 1)) s)) := by
            refine measure_mono fun z hz => ?_
            by_cases h : z ∈ Fs k
            · exact Or.inr ⟨Set.mem_symmDiff.mpr (Or.inl ⟨h, hz.2⟩), hz.1⟩
            · exact Or.inl ⟨hz.1, h⟩
        _ ≤ _ := measure_union_le _ _
/-- **The blow-up half-space passes through the origin** (Simon Ch. 3, 4.3: "(10) and (11)
evidently tell us that `λ = 0` in (9)").  If `F₀` and its complement have positive measure in
every `B_s(0)`, and `F₀` is null, conull, or a.e. equal to `{⟨z, v⟩ > c}` with `|v| = 1`, then
`F₀ = {⟨z, v⟩ > 0}` a.e.  Since `|⟨z, v⟩| ≤ |z|`, `B_c(0)` misses `{⟨z, v⟩ > c}` if `c > 0`, and
`B_{−c}(0)` lies inside it if `c < 0`. -/
theorem Submission.codim1_rdo_dg_bh_offset_zero : ∀ (m : ℕ) (F₀ : Set (Euclid (m + 1))) (v : Euclid (m + 1)), ‖v‖ = 1 → (∀ s : ℝ, 0 < s → 0 < volume (F₀ ∩ ball (0 : Euclid (m + 1)) s) ∧ 0 < volume (ball (0 : Euclid (m + 1)) s \ F₀)) → (volume F₀ = 0 ∨ volume F₀ᶜ = 0 ∨ ∃ c : ℝ, volume (symmDiff F₀ {z | c < inner ℝ z v}) = 0) → volume (symmDiff F₀ {z | 0 < inner ℝ z v}) = 0 := by
  intro m F₀ v hv hpos htri
  rcases htri with h | h | ⟨c, hc⟩
  -- `L(F₀) = 0` would give `L(F₀ ∩ B_1(0)) = 0`
  · exact ((hpos 1 one_pos).1.ne' (measure_mono_null Set.inter_subset_left h)).elim
  -- `L(F₀ᶜ) = 0` would give `L(B_1(0) \ F₀) = 0`
  · exact ((hpos 1 one_pos).2.ne' (measure_mono_null (fun x hx => hx.2) h)).elim
  · rcases lt_trichotomy c 0 with hneg | rfl | hcpos
    -- `c < 0`: `⟨z, v⟩ ≥ −|z| > c` on `B_{−c}(0)`, so `B_{−c}(0) \ F₀ ⊆ F₀ Δ {⟨z, v⟩ > c}`
    · have hsub : ball (0 : Euclid (m + 1)) (-c) \ F₀ ⊆ symmDiff F₀ {z | c < inner ℝ z v} := by
        intro z hz
        refine Set.mem_symmDiff.mpr (Or.inr ⟨?_, hz.2⟩)
        have h1 : |inner ℝ z v| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
        have h2 := mem_ball_zero_iff.mp hz.1
        rw [hv, mul_one] at h1
        show c < inner ℝ z v
        linarith [neg_abs_le (inner ℝ z v)]
      exact ((hpos (-c) (neg_pos.mpr hneg)).2.ne' (measure_mono_null hsub hc)).elim
    · exact hc
    -- `c > 0`: `⟨z, v⟩ ≤ |z| < c` on `B_c(0)`, so `F₀ ∩ B_c(0) ⊆ F₀ Δ {⟨z, v⟩ > c}`
    · have hsub : F₀ ∩ ball (0 : Euclid (m + 1)) c ⊆ symmDiff F₀ {z | c < inner ℝ z v} := by
        intro z hz
        refine Set.mem_symmDiff.mpr (Or.inl ⟨hz.1, ?_⟩)
        have h1 : |inner ℝ z v| ≤ ‖z‖ * ‖v‖ := abs_real_inner_le_norm z v
        have h2 := mem_ball_zero_iff.mp hz.2
        rw [hv, mul_one] at h1
        show ¬ c < inner ℝ z v
        linarith [le_abs_self (inner ℝ z v)]
      exact ((hpos c hcpos).1.ne' (measure_mono_null hsub hc)).elim
/-- The `C¹` radial cut-off between `B̄_ρ(y)` and `B̄_{ρ+δ}(y)` (it replaces Simon's Lipschitz
cut-offs in Ch. 3, 4.3 (3)–(4)): `ζ = h ∘ a` with `a(z) = (|z - y| - ρ)/δ` and the clamped
smoothstep `h = p ∘ clamp_{[0,1]}`, `p(s) = 1 - 3s² + 2s³`.  As `p'(0) = p'(1) = 0`, `h` is `C¹`,
nonincreasing and `3/2`-Lipschitz, so `ζ` is `C¹`, `ζ = 1` on `B̄_ρ`, `tsupport ζ ⊆ B̄_{ρ+δ}`,
`‖Dζ‖ ≤ 3/(2δ)`, `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0, 1`), and
`{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = max {s ∈ [0, 1] | t ≤ h s} < 1`. -/
theorem Submission.codim1_rdo_dg_ce_radial_cutoff : ∀ (P : ℕ) (y : Euclid P) (ρ δ : ℝ), 0 < ρ → 0 < δ → ∃ ζ : Euclid P → ℝ, ContDiff ℝ 1 ζ ∧ HasCompactSupport ζ ∧ (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧ (∀ z ∈ closedBall y ρ, ζ z = 1) ∧ tsupport ζ ⊆ closedBall y (ρ + δ) ∧ (∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ)) ∧ (∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0) ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
  intro P y ρ δ hρ hδ
  -- Steps 1–3: the profile `h = p ∘ cl`, `p(s) = 1 - 3s² + 2s³`, `cl(s) = max 0 (min s 1)`
  have profile : ∃ h : ℝ → ℝ, ContDiff ℝ 1 h ∧ Antitone h ∧ (∀ s, 0 ≤ h s ∧ h s ≤ 1) ∧
      (∀ s, s ≤ 0 → h s = 1) ∧ (∀ s, 1 ≤ s → h s = 0) ∧ LipschitzWith (3 / 2 : NNReal) h := by
    set p : ℝ → ℝ := fun s => 1 - 3 * s ^ 2 + 2 * s ^ 3 with hp_def
    set cl : ℝ → ℝ := fun s => max 0 (min s 1) with hcl_def
    set h : ℝ → ℝ := fun s => p (cl s) with hh_def
    set q : ℝ → ℝ := fun s => -6 * cl s + 6 * cl s ^ 2 with hq_def
    have hp : ∀ s, HasDerivAt p (-6 * s + 6 * s ^ 2) s := by
      intro s
      have h1 := ((hasDerivAt_pow 2 s).const_mul 3).const_sub 1
      have h2 := (hasDerivAt_pow 3 s).const_mul 2
      convert h1.add h2 using 1
      push_cast
      ring
    have hcl0 : ∀ s, s ≤ 0 → cl s = 0 := fun s hs => by
      simp only [hcl_def]; exact max_eq_left (min_le_of_left_le hs)
    have hcl1 : ∀ s, 1 ≤ s → cl s = 1 := fun s hs => by
      simp only [hcl_def]; rw [min_eq_right hs]; exact max_eq_right zero_le_one
    have hclmid : ∀ s, 0 ≤ s → s ≤ 1 → cl s = s := fun s h0 h1 => by
      simp only [hcl_def]; rw [min_eq_left h1]; exact max_eq_right h0
    have hcl01 : ∀ s, 0 ≤ cl s ∧ cl s ≤ 1 := fun s =>
      ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
    -- Step 2: `h' = q = p' ∘ cl` everywhere; at `0` and `1` the one-sided derivatives agree
    have hderiv : ∀ s, HasDerivAt h (q s) s := by
      intro s
      rcases lt_trichotomy s 0 with hs | hs | hs
      · have heq : h =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
          filter_upwards [Iio_mem_nhds hs] with u hu
          simp only [hh_def, hcl0 u (le_of_lt hu), hp_def]; norm_num
        have hq0 : q s = 0 := by simp only [hq_def, hcl0 s hs.le]; norm_num
        rw [hq0]; exact (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq heq
      · subst hs
        have hq0 : q 0 = 0 := by simp only [hq_def, hcl0 0 le_rfl]; norm_num
        rw [hq0]
        have hL : HasDerivWithinAt h 0 (Iic 0) 0 := by
          refine (hasDerivWithinAt_const (0 : ℝ) (Iic 0) (1 : ℝ)).congr (fun u hu => ?_) ?_
          · simp only [hh_def, hcl0 u hu, hp_def]; norm_num
          · simp only [hh_def, hcl0 0 le_rfl, hp_def]; norm_num
        have hR : HasDerivWithinAt h 0 (Ici 0) 0 := by
          have := (hp 0).hasDerivWithinAt (s := Ici 0)
          simp only [mul_zero, zero_pow two_ne_zero, add_zero] at this
          refine this.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Ici (0 : ℝ))
                (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
            simp only [hh_def, hclmid u hu.1 (le_of_lt hu.2)]
          · simp only [hh_def, hclmid 0 le_rfl zero_le_one]
        have := hL.union hR
        rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
      · rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
        · have heq : h =ᶠ[𝓝 s] p := by
            filter_upwards [Ioo_mem_nhds hs hs1] with u hu
            simp only [hh_def, hclmid u hu.1.le hu.2.le]
          have hqs : q s = -6 * s + 6 * s ^ 2 := by simp only [hq_def, hclmid s hs.le hs1.le]
          rw [hqs]; exact (hp s).congr_of_eventuallyEq heq
        · subst hs1
          have hq0 : q 1 = 0 := by simp only [hq_def, hcl1 1 le_rfl]; norm_num
          rw [hq0]
          have hR : HasDerivWithinAt h 0 (Ici 1) 1 := by
            refine (hasDerivWithinAt_const (1 : ℝ) (Ici 1) (0 : ℝ)).congr (fun u hu => ?_) ?_
            · simp only [hh_def, hcl1 u hu, hp_def]; norm_num
            · simp only [hh_def, hcl1 1 le_rfl, hp_def]; norm_num
          have hL : HasDerivWithinAt h 0 (Iic 1) 1 := by
            have := (hp 1).hasDerivWithinAt (s := Iic 1)
            norm_num at this
            refine this.congr_of_eventuallyEq ?_ ?_
            · filter_upwards [inter_mem_nhdsWithin (Iic (1 : ℝ))
                  (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with u hu
              simp only [hh_def, hclmid u (le_of_lt hu.2) hu.1]
            · simp only [hh_def, hclmid 1 zero_le_one le_rfl]
          have := hL.union hR
          rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
        · have heq : h =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
            filter_upwards [Ioi_mem_nhds hs1] with u hu
            simp only [hh_def, hcl1 u (le_of_lt hu), hp_def]; norm_num
          have hq0 : q s = 0 := by simp only [hq_def, hcl1 s hs1.le]; norm_num
          rw [hq0]; exact (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq heq
    -- Step 3: `h ∈ C¹`, `-3/2 ≤ h' ≤ 0`, so `h` is antitone and `3/2`-Lipschitz; `0 ≤ h ≤ 1`
    have hdiff : Differentiable ℝ h := fun s => (hderiv s).differentiableAt
    have hderiv_eq : deriv h = q := funext fun s => (hderiv s).deriv
    have hclcont : Continuous cl := by
      simp only [hcl_def]; fun_prop
    have hqcont : Continuous q := by
      simp only [hq_def]; fun_prop
    have hC1 : ContDiff ℝ 1 h := contDiff_one_iff_deriv.2 ⟨hdiff, hderiv_eq ▸ hqcont⟩
    have hq_nonpos : ∀ s, q s ≤ 0 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s; simp only [hq_def]; nlinarith
    have hq_abs : ∀ s, |q s| ≤ 3 / 2 := by
      intro s; obtain ⟨h0, h1⟩ := hcl01 s
      rw [abs_of_nonpos (hq_nonpos s)]; simp only [hq_def]; nlinarith [sq_nonneg (cl s - 1 / 2)]
    have hanti : Antitone h := antitone_of_deriv_nonpos hdiff fun s => hderiv_eq ▸ hq_nonpos s
    refine ⟨h, hC1, hanti, ?_, ?_, ?_, ?_⟩
    · intro s; obtain ⟨h0, h1⟩ := hcl01 s
      simp only [hh_def, hp_def]
      have e1 : 1 - 3 * cl s ^ 2 + 2 * cl s ^ 3 = (1 - cl s) ^ 2 * (1 + 2 * cl s) := by ring
      constructor
      · rw [e1]; exact mul_nonneg (sq_nonneg _) (by linarith)
      · nlinarith [mul_nonneg (sq_nonneg (cl s)) (by linarith : (0 : ℝ) ≤ 3 - 2 * cl s)]
    · intro s hs; simp only [hh_def, hcl0 s hs, hp_def]; norm_num
    · intro s hs; simp only [hh_def, hcl1 s hs, hp_def]; norm_num
    · refine lipschitzWith_of_nnnorm_deriv_le hdiff fun s => ?_
      rw [hderiv_eq, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
      simpa using hq_abs s
  obtain ⟨h, hC1, hanti, h01, h0, h1, hlip⟩ := profile
  -- Step 4: `ζ = h ∘ a`, `a(z) = (|z - y| - ρ)/δ`; `ζ = 1` on `B̄_ρ` and `ζ = 0` off `B_{ρ+δ}`
  set a : Euclid P → ℝ := fun z => (‖z - y‖ - ρ) / δ with ha_def
  set ζ : Euclid P → ℝ := fun z => h (a z) with hζ_def
  have hζ1 : ∀ z ∈ closedBall y ρ, ζ z = 1 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    exact h0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hζ0 : ∀ z, ρ + δ ≤ ‖z - y‖ → ζ z = 0 := by
    intro z hz
    refine h1 _ ?_
    rw [ha_def, le_div_iff₀ hδ]; linarith
  have hsupp : support ζ ⊆ ball y (ρ + δ) := by
    intro z hz
    rw [mem_ball, dist_eq_norm]
    by_contra hcon
    exact hz (hζ0 z (not_lt.1 hcon))
  have htsupp : tsupport ζ ⊆ closedBall y (ρ + δ) :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  have hcomp : HasCompactSupport ζ :=
    HasCompactSupport.intro (isCompact_closedBall y (ρ + δ)) fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz (htsupp h'))
  -- Step 5: `ζ` is `C¹`: constant near points of `B_ρ`, a `C¹` composite where `z ≠ y`
  have hC1ζ : ContDiff ℝ 1 ζ := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : ‖z - y‖ < ρ
    · have heq : ζ =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
        have hmem : ball y ρ ∈ 𝓝 z :=
          isOpen_ball.mem_nhds (by rw [mem_ball, dist_eq_norm]; exact hz)
        filter_upwards [hmem] with u hu
        exact hζ1 u (ball_subset_closedBall hu)
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hzy : z - y ≠ 0 := by
        intro h0'; rw [h0', norm_zero] at hz; exact hz hρ
      have hn : ContDiffAt ℝ 1 (fun u : Euclid P => ‖u - y‖) z :=
        (contDiffAt_id.sub contDiffAt_const).norm ℝ hzy
      have ha' : ContDiffAt ℝ 1 a z := (hn.sub contDiffAt_const).div_const δ
      exact hC1.contDiffAt.comp z ha'
  -- Step 6: `ζ` is `3/(2δ)`-Lipschitz, hence `‖Dζ‖ ≤ 3/(2δ)`
  have hlipζ : LipschitzWith (Real.toNNReal (3 / (2 * δ))) ζ := by
    refine LipschitzWith.of_dist_le_mul fun z w => ?_
    have h1' := hlip.dist_le_mul (a z) (a w)
    have h2' : dist (a z) (a w) ≤ dist z w / δ := by
      rw [Real.dist_eq, ha_def]
      simp only
      rw [← sub_div, abs_div, abs_of_pos hδ, dist_eq_norm]
      gcongr
      calc |‖z - y‖ - ρ - (‖w - y‖ - ρ)| = |‖z - y‖ - ‖w - y‖| := by ring_nf
        _ ≤ ‖(z - y) - (w - y)‖ := abs_norm_sub_norm_le _ _
        _ = ‖z - w‖ := by abel_nf
    rw [Real.coe_toNNReal _ (by positivity)]
    calc dist (ζ z) (ζ w) ≤ (3 / 2 : NNReal) * dist (a z) (a w) := h1'
      _ ≤ (3 / 2 : ℝ) * (dist z w / δ) := by
          push_cast; gcongr
      _ = 3 / (2 * δ) * dist z w := by field_simp
  have hgrad : ∀ z, ‖fderiv ℝ ζ z‖ ≤ 3 / (2 * δ) := by
    intro z
    have := norm_fderiv_le_of_lipschitz ℝ hlipζ (x₀ := z)
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  -- Step 7: `Dζ = 0` off the open annulus (Fermat at the extrema `ζ = 0` and `ζ = 1`)
  have hζle : ∀ z, ζ z ≤ 1 := fun z => (h01 _).2
  have hζge : ∀ z, 0 ≤ ζ z := fun z => (h01 _).1
  have hzero : ∀ z, z ∉ ball y (ρ + δ) \ closedBall y ρ → fderiv ℝ ζ z = 0 := by
    intro z hz
    rw [Set.mem_sdiff, not_and_or, not_not] at hz
    rcases hz with hz | hz
    · rw [mem_ball, dist_eq_norm, not_lt] at hz
      have hmin : IsLocalMin ζ z := Eventually.of_forall fun u => by rw [hζ0 z hz]; exact hζge u
      exact hmin.fderiv_eq_zero
    · have hmax : IsLocalMax ζ z := Eventually.of_forall fun u => by rw [hζ1 z hz]; exact hζle u
      exact hmax.fderiv_eq_zero
  -- Step 8: `{t ≤ ζ} = B̄_{ρ+δ s_t}` with `s_t = sup M`, `M = {s ∈ [0, 1] | t ≤ h s}` compact
  have hlevel : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ r : ℝ, ρ ≤ r ∧ r < ρ + δ ∧ {z | t ≤ ζ z} = closedBall y r := by
    intro t ht0 ht1
    set M : Set ℝ := Icc 0 1 ∩ h ⁻¹' Ici t with hM
    have hMc : IsCompact M :=
      isCompact_Icc.inter_right (isClosed_Ici.preimage hC1.continuous)
    have hM0 : (0 : ℝ) ∈ M := ⟨⟨le_rfl, zero_le_one⟩, by simp [h0 0 le_rfl, ht1]⟩
    set st := sSup M with hst
    have hstM : st ∈ M := hMc.sSup_mem ⟨0, hM0⟩
    have hst0 : 0 ≤ st := hstM.1.1
    have hst1 : st < 1 := by
      rcases hstM.1.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; have := hstM.2; rw [heq, mem_preimage, mem_Ici, h1 1 le_rfl] at this; linarith
    have hiff : ∀ u : ℝ, t ≤ h u ↔ u ≤ st := by
      intro u
      constructor
      · intro hu
        by_contra hcon
        push Not at hcon
        rcases le_or_gt u 1 with hu1 | hu1
        · have huM : u ∈ M := ⟨⟨hst0.trans hcon.le, hu1⟩, hu⟩
          exact absurd (le_csSup hMc.bddAbove huM) (not_le.2 hcon)
        · rw [h1 u hu1.le] at hu; linarith
      · intro hu
        exact le_trans hstM.2 (hanti hu)
    refine ⟨ρ + δ * st, by nlinarith, by nlinarith, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq, mem_closedBall, dist_eq_norm, hζ_def]
    rw [hiff, ha_def, div_le_iff₀ hδ]
    constructor <;> intro hh <;> linarith
  exact ⟨ζ, hC1ζ, hcomp, fun z => h01 _, hζ1, htsupp, hgrad, hzero, hlevel⟩
/-- **Signed layer cake** (Simon Ch. 3, 4.3 (4)–(5), the limit procedure of the De Giorgi cut-off
estimates): let `0 ≤ ζ ≤ 1` vanish off `S`, `μ(S) < ∞`, `ζ = 1` on `B`, `|g| ≤ 1` and `c ≥ 0`.  If
`c μ({ζ ≥ t}) ≤ ∫_{ζ ≥ t} g dμ` for every `t ∈ (0, 1]`, then `c μ(B) ≤ ∫ ζ g dμ`.

Proof sketch:
* `ζ(x) g(x) = ∫_{(0,1]} H(x, t) dt` with `H(x, t) = 1{t ≤ ζ(x)} g(x)`; `H` is bounded and
  measurable on the finite product `μ⌞S ⊗ λ⌞(0, 1]`, so Fubini swaps the two integrals.
* For `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`, so `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`;
  integrating over `(0, 1]` concludes. -/
theorem Submission.codim1_rdo_dg_ce_signed_layer_cake : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (ζ g : X → ℝ) (S B : Set X) (c : ℝ), Measurable ζ → Measurable g → (∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) → (∀ x, |g x| ≤ 1) → MeasurableSet S → μ S ≠ ∞ → (∀ x, x ∉ S → ζ x = 0) → (∀ x ∈ B, ζ x = 1) → 0 ≤ c → (∀ t : ℝ, 0 < t → t ≤ 1 → c * (μ {x | t ≤ ζ x}).toReal ≤ ∫ x in {x | t ≤ ζ x}, g x ∂μ) → c * (μ B).toReal ≤ ∫ x, ζ x * g x ∂μ := by
  intro X _ μ ζ g S B c hζ hg hζ01 hg1 hS hSfin hζS hζB hc hlev
  -- the finite measures `μ⌞S` and `λ⌞(0, 1]`
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hSfin
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp)
  -- for `t ∈ (0, 1]`, `B ⊆ {ζ ≥ t} ⊆ S`
  have hLS : ∀ t : ℝ, 0 < t → {x | t ≤ ζ x} ⊆ S := fun t ht x hx => by
    by_contra hxS
    have hx' : t ≤ ζ x := hx
    rw [hζS x hxS] at hx'
    linarith
  have hBL : ∀ t : ℝ, t ≤ 1 → B ⊆ {x | t ≤ ζ x} := fun t ht x hx => by
    show t ≤ ζ x
    rw [hζB x hx]
    exact ht
  -- the layer-cake integrand `H(x, t) = 1{t ≤ ζ(x)} g(x)` is integrable on `μ⌞S ⊗ λ⌞(0, 1]`
  set H : X → ℝ → ℝ := fun x t => if t ≤ ζ x then g x else 0 with hH
  have hHmeas : Measurable (uncurry H) :=
    Measurable.ite (measurableSet_le measurable_snd (hζ.comp measurable_fst))
      (hg.comp measurable_fst) measurable_const
  have hHint : Integrable (uncurry H) ((μ.restrict S).prod ν) := by
    refine Integrable.of_bound hHmeas.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
    simp only [uncurry, hH]
    split_ifs
    · simpa [Real.norm_eq_abs] using hg1 p.1
    · simp
  -- inner integral in `t`: `∫_{(0,1]} H(x, t) dt = λ((0, ζ(x)]) g(x) = ζ(x) g(x)`
  have hinner : ∀ x, ∫ t, H x t ∂ν = ζ x * g x := by
    intro x
    have : (fun t => H x t) = (Iic (ζ x)).indicator (fun _ => g x) := by
      funext t; simp [hH, indicator_apply, mem_Iic]
    rw [this, integral_indicator_const _ measurableSet_Iic, smul_eq_mul, hν, Measure.real,
      Measure.restrict_apply measurableSet_Iic]
    have hset : Iic (ζ x) ∩ Ioc (0 : ℝ) 1 = Ioc 0 (ζ x) := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩; exact ⟨h1, h2, h1.trans (hζ01 x).2⟩
    rw [hset, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (hζ01 x).1]
  -- `ζ g` vanishes off `S`, so `∫ ζ g dμ = ∫∫ H dt dμ⌞S`
  have hleft : ∫ x, ζ x * g x ∂μ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := by
    simp_rw [hinner]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    simp [hζS x hx]
  -- for `t ∈ (0, 1]`: `∫ H(·, t) dμ⌞S = ∫_{ζ ≥ t} g dμ ≥ c μ({ζ ≥ t}) ≥ c μ(B)`
  have hlow : ∀ t ∈ Ioc (0 : ℝ) 1, c * (μ B).toReal ≤ ∫ x, H x t ∂(μ.restrict S) := by
    intro t ht
    have hLmeas : MeasurableSet {x | t ≤ ζ x} := measurableSet_le measurable_const hζ
    have : (fun x => H x t) = {x | t ≤ ζ x}.indicator g := by
      funext x; simp [hH, indicator_apply]
    rw [this, integral_indicator hLmeas, Measure.restrict_restrict hLmeas,
      inter_eq_left.2 (hLS t ht.1)]
    refine le_trans ?_ (hlev t ht.1 ht.2)
    have hLfin : μ {x | t ≤ ζ x} ≠ ∞ := ne_top_of_le_ne_top hSfin (measure_mono (hLS t ht.1))
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hLfin (measure_mono (hBL t ht.2))) hc
  have hint_t : Integrable (fun t => ∫ x, H x t ∂(μ.restrict S)) ν := hHint.integral_prod_right
  calc c * (μ B).toReal = ∫ t, c * (μ B).toReal ∂ν := by
        simp [hν, Measure.real]
    _ ≤ ∫ t, ∫ x, H x t ∂(μ.restrict S) ∂ν := by
        refine integral_mono_ae (integrable_const _) hint_t ?_
        rw [hν, EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact Eventually.of_forall hlow
    _ = ∫ x, ∫ t, H x t ∂ν ∂(μ.restrict S) := (integral_integral_swap hHint).symm
    _ = ∫ x, ζ x * g x ∂μ := hleft.symm
/-- The divergence theorem for compactly supported fields (step 6 of the cut-off estimates in the
De Giorgi argument, cf. Simon Ch. 3, 4.3): if `φ : ℝᴾ → ℝᴾ` is `C¹` with compact support, then
`div φ = trace Dφ = ∑ᵢ ∂ᵢφⁱ` is integrable and `∫ div φ dLᴾ = ∑ᵢ ∫ ∂ᵢφⁱ dLᴾ = 0`. -/
theorem Submission.codim1_rdo_dg_ce_integral_div_eq_zero : ∀ (P : ℕ) (φ : Euclid P → Euclid P), ContDiff ℝ 1 φ → HasCompactSupport φ → Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) ∧ ∫ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = 0 := by
  intro P φ hφ hφc
  set b := EuclideanSpace.basisFun (Fin P) ℝ with hb
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  -- the coordinate functions `φⁱ = ⟪bᵢ, φ⟫` are `C¹` with compact support
  set f : Fin P → Euclid P → ℝ := fun i w => innerSL ℝ (b i) (φ w) with hf
  have hfC : ∀ i, ContDiff ℝ 1 (f i) := fun i => (innerSL ℝ (b i)).contDiff.comp hφ
  have hfcs : ∀ i, HasCompactSupport (f i) := fun i => hφc.comp_left (map_zero _)
  have hfder : ∀ i z, fderiv ℝ (f i) z = (innerSL ℝ (b i)).comp (fderiv ℝ φ z) := by
    intro i z
    exact ((innerSL ℝ (b i)).hasFDerivAt.comp z (hdiff z).hasFDerivAt).fderiv
  -- `trace Dφ(z) = ∑ᵢ ⟪bᵢ, Dφ(z) bᵢ⟫ = ∑ᵢ ∂ᵢφⁱ(z)`
  have hcoord : ∀ z, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) =
      ∑ i, fderiv ℝ (f i) z (b i) := by
    intro z
    rw [LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfder]
    simp [innerSL_apply_apply]
  -- each `∂ᵢφⁱ` is continuous and vanishes off `tsupport φⁱ`, hence integrable
  have hint_i : ∀ i, Integrable (fun z => fderiv ℝ (f i) z (b i)) := by
    intro i
    apply Continuous.integrable_of_hasCompactSupport
    · exact ((hfC i).continuous_fderiv one_ne_zero).clm_apply continuous_const
    · refine (hfcs i).mono' ?_
      intro z hz
      refine support_fderiv_subset ℝ ?_
      intro h0
      exact hz (by simp [h0])
  -- `∫ ∂ᵢφⁱ = 0`: integrate by parts against the constant function `1`
  have hzero_i : ∀ i, ∫ z, fderiv ℝ (f i) z (b i) = 0 := by
    intro i
    obtain ⟨C, hC⟩ := (hfC i).lipschitzWith_of_hasCompactSupport (hfcs i) one_ne_zero
    have h1 := (LipschitzWith.const (1 : ℝ) : LipschitzWith 0 (fun _ : Euclid P => (1 : ℝ))).integral_lineDeriv_mul_eq
      (μ := (volume : Measure (Euclid P))) hC (hfcs i) (b i)
    have hl : ∀ x, lineDeriv ℝ (f i) x (-b i) = -fderiv ℝ (f i) x (b i) := by
      intro x
      rw [(((hfC i).differentiable one_ne_zero) x).lineDeriv_eq_fderiv, map_neg]
    have hc : ∀ x, lineDeriv ℝ (fun _ : Euclid P => (1 : ℝ)) x (b i) = 0 := by
      intro x
      simp [lineDeriv]
    simp only [hc, zero_mul, integral_zero, mul_one, hl, integral_neg] at h1
    linarith
  have hint : Integrable (fun z => LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P)) := by
    simp_rw [hcoord]
    exact integrable_finsetSum _ fun i _ => hint_i i
  refine ⟨hint, ?_⟩
  simp_rw [hcoord]
  rw [integral_finsetSum _ fun i _ => hint_i i]
  exact Finset.sum_eq_zero fun i _ => hzero_i i
/-- **Normal averages close to a unit vector** (quantitative form of Simon Ch. 3, 4.3 (1)).  Let
`μ(B̄_{ρ₀}(y)) < ∞`, `ν` be measurable with `|ν| ≤ 1`, `|v| = 1`, and
`A(ρ) := μ(B̄_ρ(y))⁻¹ ∫_{B̄_ρ(y)} ν dμ → v` as `ρ ↓ 0`.  Then for some `ρ₂ ∈ (0, ρ₀]`,
`∫_{B̄_r(y)} ⟨ν, v⟩ dμ ≥ ½ μ(B̄_r(y))` whenever `0 < r < ρ₂`.  Since `⟨A(r), v⟩ → |v|² = 1`, we have
`⟨A(r), v⟩ > ½` for `r ∈ (0, ε)`; take `ρ₂ = min ε ρ₀`.  For `0 < r < ρ₂`, `ν` is integrable on
`B̄_r(y)` (bounded, finite measure), so `∫⟨ν, v⟩ = ⟨∫ν, v⟩`.  Either `μ(B̄_r(y)) = 0` and both sides
vanish, or `∫ν = μ(B̄_r(y)) A(r)` and `∫⟨ν, v⟩ = μ(B̄_r(y)) ⟨A(r), v⟩ ≥ ½ μ(B̄_r(y))`. -/
theorem Submission.codim1_rdo_dg_ce_normal_average_lower : ∀ (P : ℕ) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₀ : ℝ), 0 < ρ₀ → μ (closedBall y ρ₀) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₂ : ℝ, 0 < ρ₂ ∧ ρ₂ ≤ ρ₀ ∧ ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ := by
  intro P μ ν y v ρ₀ hρ₀ hfin hν hν1 hv hT
  -- step 1: `⟨A(ρ), v⟩ → ⟨v, v⟩ = 1`, so `⟨A(ρ), v⟩ > ½` for `ρ ∈ (0, ε)`
  have hT' : Tendsto (fun ρ : ℝ => inner ℝ ((μ (closedBall y ρ)).toReal⁻¹ •
      ∫ z in closedBall y ρ, ν z ∂μ) v) (𝓝[>] 0) (𝓝 (inner ℝ v v)) :=
    hT.inner tendsto_const_nhds
  rw [real_inner_self_eq_norm_sq, hv, one_pow] at hT'
  obtain ⟨ε, hε, hεsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1
    (hT'.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  -- step 2: `ρ₂ = min ε ρ₀`; for `r < ρ₂`, `μ(B̄_r(y)) ≤ μ(B̄_{ρ₀}(y)) < ∞`
  refine ⟨min ε ρ₀, lt_min hε hρ₀, min_le_right _ _, fun r hr hr₂ => ?_⟩
  have hkey : (1 / 2 : ℝ) < inner ℝ ((μ (closedBall y r)).toReal⁻¹ •
      ∫ z in closedBall y r, ν z ∂μ) v :=
    hεsub ⟨hr, hr₂.trans_le (min_le_left _ _)⟩
  have hBfin : μ (closedBall y r) ≠ ∞ := ne_top_of_le_ne_top hfin
    (measure_mono (closedBall_subset_closedBall (hr₂.trans_le (min_le_right _ _)).le))
  -- step 3: `ν` is integrable on `B̄_r(y)`, and `∫⟨ν, v⟩ = ⟨∫ν, v⟩`
  have hint : IntegrableOn ν (closedBall y r) μ :=
    Measure.integrableOn_of_bounded hBfin hν.aestronglyMeasurable (Eventually.of_forall hν1)
  have hcomm : ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ =
      inner ℝ (∫ z in closedBall y r, ν z ∂μ) v := by
    simpa only [innerSL_apply_apply, real_inner_comm v] using
      (innerSL ℝ v).integral_comp_comm hint
  -- step 4: if `μ(B̄_r(y)) = 0`, both sides vanish
  by_cases hμ0 : μ (closedBall y r) = 0
  · rw [hμ0, ENNReal.toReal_zero, mul_zero, setIntegral_measure_zero _ hμ0]
  -- step 5: otherwise `∫ν = a A(r)` with `a = μ(B̄_r(y)) > 0`, so `∫⟨ν, v⟩ = a ⟨A(r), v⟩ ≥ a / 2`
  have hpos : 0 < (μ (closedBall y r)).toReal := ENNReal.toReal_pos hμ0 hBfin
  have hI : ∫ z in closedBall y r, ν z ∂μ = (μ (closedBall y r)).toReal •
      ((μ (closedBall y r)).toReal⁻¹ • ∫ z in closedBall y r, ν z ∂μ) := by
    rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [hcomm, hI, real_inner_smul_left]
  nlinarith

/-- Annular bound behind De Giorgi's cut-off estimates (Simon Ch. 3, 4.3 (3)–(6), in
finite-difference form, as used for 7.5.8).  Suppose `F` satisfies the Gauss–Green identity
`∫_F div φ dLᴾ = -∫ ⟨φ, ν⟩ dμ` for `C¹` fields `φ` with compact support in `D ⊇ B̄_{ρ₂}(y)`
(`|ν| ≤ 1`, `μ(B̄_{ρ₂}(y)) < ∞`), and `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂`
(`|v| ≤ 1`).  Then `δ μ(B̄_ρ(y)) ≤ 3 Lᴾ(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` whenever `ρ, δ > 0` and
`ρ + δ < ρ₂`.  Test the identity with `φ = ζ v`, `ζ` the radial cut-off
`Submission.codim1_rdo_dg_ce_radial_cutoff`: `div φ = Dζ v` vanishes off the annulus and is
bounded by `3/(2δ)`, while the signed layer-cake formula
`Submission.codim1_rdo_dg_ce_signed_layer_cake` over the superlevel balls `{ζ ≥ t} = B̄_r(y)`
gives `∫ ζ ⟨v, ν⟩ dμ ≥ ½ μ(B̄_ρ(y))`. -/
theorem Submission.codim1_rdo_dg_ce_annular_bound : ∀ (P : ℕ) (D F : Set (Euclid P)) (μ : Measure (Euclid P)) (ν : Euclid P → Euclid P) (y v : Euclid P) (ρ₂ : ℝ), MeasurableSet F → closedBall y ρ₂ ⊆ D → μ (closedBall y ρ₂) ≠ ∞ → Measurable ν → (∀ z, ‖ν z‖ ≤ 1) → ‖v‖ ≤ 1 → (∀ φ : Euclid P → Euclid P, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid P) (fderiv ℝ φ z : Euclid P →ₗ[ℝ] Euclid P) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → (∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤ ∫ z in closedBall y r, inner ℝ (ν z) v ∂μ) → ∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₂ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) := by
  intro P D F μ ν y v ρ₂ _hF hD hfin hν hν1 hv hGG h1' ρ δ hρ hδ hρδ
  set A := ball y (ρ + δ) \ closedBall y ρ
  -- Step 1: `μ(B̄_ρ) ≤ μ(B̄_{ρ+δ}) ≤ μ(B̄_{ρ₂}) < ∞` and `Lᴾ(F ∩ A) ≤ Lᴾ(B_{ρ+δ}) < ∞`.
  have hSsub : closedBall y (ρ + δ) ⊆ closedBall y ρ₂ := closedBall_subset_closedBall hρδ.le
  have hSfin : μ (closedBall y (ρ + δ)) ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hSsub)
  have hBfin : μ (closedBall y ρ) ≠ ∞ :=
    ne_top_of_le_ne_top hSfin (measure_mono (closedBall_subset_closedBall (by linarith)))
  have hAmeas : MeasurableSet A := measurableSet_ball.diff measurableSet_closedBall
  have hAfin : volume A ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono sdiff_subset)
  have hFAfin : volume (F ∩ A) ≠ ∞ := ne_top_of_le_ne_top hAfin (measure_mono inter_subset_right)
  -- Step 2: the radial cut-off `ζ`, `= 1` on `B̄_ρ`, supported in `B̄_{ρ+δ}`, `|Dζ| ≤ 3/(2δ)`.
  obtain ⟨ζ, hζC, hζc, hζ01, hζ1, hζsupp, hζgrad, hζzero, hζlevel⟩ :=
    Submission.codim1_rdo_dg_ce_radial_cutoff P y ρ δ hρ hδ
  -- Step 3: Gauss–Green for `φ = ζ v`, whose divergence is the trace `Dζ v` of the rank-one
  -- map `Dφ = Dζ ⊗ v`: `∫ ζ ⟨v, ν⟩ dμ = -∫_F Dζ v dLᴾ`.
  have hφD : tsupport (fun z => ζ z • v) ⊆ D :=
    (tsupport_smul_subset_left _ _).trans (hζsupp.trans (hSsub.trans hD))
  have htrace : ∀ z, LinearMap.trace ℝ (Euclid P)
      (fderiv ℝ (fun z => ζ z • v) z : Euclid P →ₗ[ℝ] Euclid P) = fderiv ℝ ζ z v := by
    intro z
    rw [fderiv_smul_const ((hζC.differentiable one_ne_zero) z) v]
    exact LinearMap.trace_smulRight _ _
  have hGGζ : ∫ z, ζ z * inner ℝ v (ν z) ∂μ = -∫ z in F, fderiv ℝ ζ z v := by
    have h := hGG (fun z => ζ z • v) (hζC.smul contDiff_const) hζc.smul_right hφD
    simp only [htrace, real_inner_smul_left] at h
    rw [h, neg_neg]
  -- Step 4: `|Dζ v| ≤ (3/(2δ)) 𝟙_A`, so `-∫_F Dζ v dLᴾ ≤ (3/(2δ)) Lᴾ(F ∩ A)`.
  have hpt : ∀ z, ‖fderiv ℝ ζ z v‖ ≤ A.indicator (fun _ => 3 / (2 * δ)) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      calc ‖fderiv ℝ ζ z v‖ ≤ ‖fderiv ℝ ζ z‖ * ‖v‖ := (fderiv ℝ ζ z).le_opNorm v
        _ ≤ 3 / (2 * δ) * 1 := mul_le_mul (hζgrad z) hv (norm_nonneg _) (by positivity)
        _ = 3 / (2 * δ) := mul_one _
    · rw [indicator_of_notMem hz, hζzero z hz]
      simp
  have hup : -∫ z in F, fderiv ℝ ζ z v ≤ 3 / (2 * δ) * (volume (F ∩ A)).toReal := by
    have hint : Integrable (A.indicator (fun _ => 3 / (2 * δ))) (volume.restrict F) :=
      ((integrableOn_const hAfin).integrable_indicator hAmeas).restrict
    have heq : ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z =
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      rw [integral_indicator_const _ hAmeas, smul_eq_mul, mul_comm]
      congr 1
      simp only [Measure.real, Measure.restrict_apply hAmeas, inter_comm]
    calc -∫ z in F, fderiv ℝ ζ z v ≤ ‖∫ z in F, fderiv ℝ ζ z v‖ := by
          rw [Real.norm_eq_abs]; exact neg_le_abs _
      _ ≤ ∫ z in F, A.indicator (fun _ => 3 / (2 * δ)) z :=
          norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
      _ = 3 / (2 * δ) * (volume (F ∩ A)).toReal := heq
  -- Step 5: the signed layer-cake formula with `g = ⟨v, ν⟩`, `S = B̄_{ρ+δ}`, `B = B̄_ρ`, `c = ½`;
  -- each `{ζ ≥ t} = B̄_r` has `0 < ρ ≤ r < ρ + δ < ρ₂`, where `(1′)` applies.
  have hg : Measurable (fun z => inner ℝ v (ν z)) :=
    (continuous_const.inner continuous_id).measurable.comp hν
  have hlow : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤ ∫ z, ζ z * inner ℝ v (ν z) ∂μ := by
    refine Submission.codim1_rdo_dg_ce_signed_layer_cake (Euclid P) μ ζ (fun z => inner ℝ v (ν z))
      (closedBall y (ρ + δ)) (closedBall y ρ) (1 / 2) hζC.continuous.measurable hg hζ01 ?_
      measurableSet_closedBall hSfin ?_ hζ1 (by norm_num) ?_
    · intro z
      calc |inner ℝ v (ν z)| ≤ ‖v‖ * ‖ν z‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := mul_le_mul hv (hν1 z) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · intro z hz
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hζsupp h))
    · intro t ht0 ht1
      obtain ⟨r, hr1, hr2, hrset⟩ := hζlevel t ht0 ht1
      rw [hrset]
      simpa only [real_inner_comm] using h1' r (by linarith) (by linarith)
  -- Step 6: `½ μ(B̄_ρ) ≤ (3/(2δ)) Lᴾ(F ∩ A)`; multiply by `2δ > 0`.
  have hreal : δ * (μ (closedBall y ρ)).toReal ≤ 3 * (volume (F ∩ A)).toReal := by
    have key : (1 / 2 : ℝ) * (μ (closedBall y ρ)).toReal ≤
        3 / (2 * δ) * (volume (F ∩ A)).toReal := by
      linarith
    have h3 : 3 / (2 * δ) * (volume (F ∩ A)).toReal * (2 * δ) = 3 * (volume (F ∩ A)).toReal := by
      field_simp
    nlinarith [key, hδ]
  -- Step 7: back to `[0, ∞]`, both measures being finite by step 1.
  calc ENNReal.ofReal δ * μ (closedBall y ρ)
      = ENNReal.ofReal (δ * (μ (closedBall y ρ)).toReal) := by
        rw [ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal hBfin]
    _ ≤ ENNReal.ofReal (3 * (volume (F ∩ A)).toReal) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal 3 * volume (F ∩ A) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hFAfin]

/-- **Cut-off estimates** of Simon Ch. 3, proof of Theorem 4.3, (1) and (3)–(6), in
finite-difference form, at a point `y` where the normal averages of the Gauss–Green measure `μ`
tend to a unit vector `v`.  `codim1_rdo_dg_ce_normal_average_lower` gives `0 < ρ₂ ≤ ρ₀`, with
`B̄_{ρ₀}(y) ⊆ D`, such that `½ μ(B̄_r(y)) ≤ ∫_{B̄_r(y)} ⟨ν, v⟩ dμ` for `0 < r < ρ₂` (printed (1)).
`codim1_rdo_dg_ce_annular_bound` (the cut-off and layer-cake argument of (3)–(5)) then gives
`δ μ(B̄_ρ(y)) ≤ 3 L(F ∩ (B_{ρ+δ}(y) \ B̄_ρ(y)))` for `ρ + δ < ρ₂`.  Since `∫ div φ = 0`
(`codim1_rdo_dg_ce_integral_div_eq_zero`), `Fᶜ` satisfies the Gauss–Green identity with `−ν`, and
`(−ν, −v)` satisfies the same lower bound, so the annular bound also holds for `Fᶜ`.  Taking
`δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}` gives `μ(B̄_ρ(y)) ≤ 3·2^{m+1} ω_{m+1} ρ^m`
(printed (6)).  Finally `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`. -/
theorem Submission.codim1_rdo_dg_cutoff_estimates : ∀ (m : ℕ) (D F : Set (Euclid (m + 1))) (μ : Measure (Euclid (m + 1))) (ν : Euclid (m + 1) → Euclid (m + 1)) (y v : Euclid (m + 1)), IsOpen D → MeasurableSet F → μ Dᶜ = 0 → (∀ K : Set (Euclid (m + 1)), IsCompact K → K ⊆ D → μ K ≠ ∞) → Measurable ν → (∀ z, ‖ν z‖ = 1) → (∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ D → ∫ z in F, LinearMap.trace ℝ (Euclid (m + 1)) (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (ν z) ∂μ) → y ∈ D → ‖v‖ = 1 → Tendsto (fun ρ : ℝ => (μ (closedBall y ρ)).toReal⁻¹ • ∫ z in closedBall y ρ, ν z ∂μ) (𝓝[>] 0) (𝓝 v) → ∃ ρ₁ C : ℝ, 0 < ρ₁ ∧ 0 ≤ C ∧ closedBall y ρ₁ ⊆ D ∧ (∀ ρ δ : ℝ, 0 < ρ → 0 < δ → ρ + δ < ρ₁ → ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume (F ∩ (ball y (ρ + δ) \ closedBall y ρ)) ∧ ENNReal.ofReal δ * μ (closedBall y ρ) ≤ ENNReal.ofReal C * volume ((ball y (ρ + δ) \ closedBall y ρ) \ F)) ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → μ (closedBall y ρ) ≤ ENNReal.ofReal (C * ρ ^ m) := by
  intro m D F μ ν y v hD hF hμD hμK hν hν1 hGG hy hv hT
  -- step 1: a radius `ρ₀` with `B̄_{ρ₀}(y) ⊆ D`, and `ρ₂ ≤ ρ₀` below which (1′) holds
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD y hy
  have hρ₀D : closedBall y (ε / 2) ⊆ D := (closedBall_subset_ball (half_lt_self hε)).trans hεD
  have hρ₀fin : μ (closedBall y (ε / 2)) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₀D
  obtain ⟨ρ₂, hρ₂pos, hρ₂le, h1'⟩ := Submission.codim1_rdo_dg_ce_normal_average_lower (m + 1) μ ν
    y v (ε / 2) (half_pos hε) hρ₀fin hν (fun z => (hν1 z).le) hv hT
  have hρ₂D : closedBall y ρ₂ ⊆ D := (closedBall_subset_closedBall hρ₂le).trans hρ₀D
  have hρ₂fin : μ (closedBall y ρ₂) ≠ ∞ := hμK _ (isCompact_closedBall y _) hρ₂D
  -- steps 2–5: the annular bound for `F`
  have hA1 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D F μ ν y v ρ₂ hF hρ₂D hρ₂fin hν
    (fun z => (hν1 z).le) hv.le hGG h1'
  -- step 6: `Fᶜ` satisfies (GG) with `−ν` because `∫ div φ = 0`, and (1′) holds for `(−ν, −v)`,
  -- so the annular bound also holds for `Fᶜ`
  have hGGc : ∀ φ : Euclid (m + 1) → Euclid (m + 1), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ D → ∫ z in Fᶜ, LinearMap.trace ℝ (Euclid (m + 1))
        (fderiv ℝ φ z : Euclid (m + 1) →ₗ[ℝ] Euclid (m + 1)) = -∫ z, inner ℝ (φ z) (-ν z) ∂μ := by
    intro φ hφ hφc hφD
    obtain ⟨hint, hzero⟩ := Submission.codim1_rdo_dg_ce_integral_div_eq_zero (m + 1) φ hφ hφc
    have hsplit := integral_add_compl hF hint
    rw [hzero, hGG φ hφ hφc hφD] at hsplit
    simp only [inner_neg_right, integral_neg, neg_neg]
    linarith
  have h1'c : ∀ r : ℝ, 0 < r → r < ρ₂ → (1 / 2 : ℝ) * (μ (closedBall y r)).toReal ≤
      ∫ z in closedBall y r, inner ℝ (-ν z) (-v) ∂μ := by
    intro r hr hr2
    simpa only [inner_neg_neg] using h1' r hr hr2
  have hA2 := Submission.codim1_rdo_dg_ce_annular_bound (m + 1) D Fᶜ μ (fun z => -ν z) y (-v) ρ₂
    hF.compl hρ₂D hρ₂fin hν.neg (fun z => by simpa using (hν1 z).le) (by simpa using hv.le) hGGc
    h1'c
  -- step 8: `ρ₁ = ρ₂/2` and `C = max(3, 3·2^{m+1} ω_{m+1})`, where `ω_{m+1} = L(B₁(0))`
  set ω : ℝ := (volume (ball (0 : Euclid (m + 1)) 1)).toReal with hω
  have hωeq : volume (ball (0 : Euclid (m + 1)) 1) = ENNReal.ofReal ω := by
    rw [hω, ENNReal.ofReal_toReal measure_ball_lt_top.ne]
  refine ⟨ρ₂ / 2, max 3 (3 * 2 ^ (m + 1) * ω), half_pos hρ₂pos, le_max_of_le_left (by norm_num),
    (closedBall_subset_closedBall (half_le_self hρ₂pos.le)).trans hρ₂D, ?_, ?_⟩
  -- the annular bounds of steps 5–6 hold below `ρ₁ < ρ₂`, and `3 ≤ C`
  · intro ρ δ hρ hδ hρδ
    have hlt : ρ + δ < ρ₂ := by linarith
    have hC : ENNReal.ofReal 3 ≤ ENNReal.ofReal (max 3 (3 * 2 ^ (m + 1) * ω)) :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    have hset : Fᶜ ∩ (ball y (ρ + δ) \ closedBall y ρ) = (ball y (ρ + δ) \ closedBall y ρ) \ F := by
      ext z; simp [and_comm]
    have h2 := hA2 ρ δ hρ hδ hlt
    rw [hset] at h2
    exact ⟨(hA1 ρ δ hρ hδ hlt).trans (mul_le_mul_left hC _), h2.trans (mul_le_mul_left hC _)⟩
  -- step 7: `δ = ρ` and `L(B_{2ρ}(y)) = (2ρ)^{m+1} ω_{m+1}`
  · intro ρ hρ hρ1
    have hvol : volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤
        ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
      calc volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) ≤ volume (ball y (ρ + ρ)) :=
            measure_mono (inter_subset_right.trans sdiff_subset)
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1)) * volume (ball (0 : Euclid (m + 1)) 1) := by
            rw [Measure.addHaar_ball _ _ (by linarith), finrank_euclideanSpace_fin]
        _ = ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := by
            rw [hωeq, ENNReal.ofReal_mul (by positivity)]
    have key : ENNReal.ofReal ρ * μ (closedBall y ρ) ≤
        ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
      calc ENNReal.ofReal ρ * μ (closedBall y ρ)
          ≤ ENNReal.ofReal 3 * volume (F ∩ (ball y (ρ + ρ) \ closedBall y ρ)) :=
            hA1 ρ ρ hρ hρ (by linarith)
        _ ≤ ENNReal.ofReal 3 * ENNReal.ofReal ((ρ + ρ) ^ (m + 1) * ω) := mul_le_mul_right hvol _
        _ = ENNReal.ofReal ρ * ENNReal.ofReal (3 * 2 ^ (m + 1) * ω * ρ ^ m) := by
            rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul hρ.le]
            congr 1
            ring
    have hρne : ENNReal.ofReal ρ ≠ 0 := by simpa using hρ
    refine ((ENNReal.mul_le_mul_iff_right hρne ENNReal.ofReal_ne_top).mp key).trans
      (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
