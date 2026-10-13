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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
