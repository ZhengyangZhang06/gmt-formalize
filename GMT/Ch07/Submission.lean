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

/-- **Simon 6.2.5** (mass of a restricted, positively scaled current; proof of 7.4.2, step 5).  If
`W ⊆ V ⊆ U`, `c ≥ 0`, and `T ∈ 𝒟ₙ(U)`, `T₀ ∈ 𝒟ₙ(V)` satisfy `T(ι ω) = c T₀(ω)` for every
`ω ∈ 𝒟ⁿ(V)` (`ι` = `testFormOnInclusion`), then `M_W(T) = c M_W(T₀)`.  A form admissible for
`M_W` has `spt ω ⊆ W ⊆ V`, so `ι` is a bijection from the admissible forms in `V` onto those in
`U`; the two value sets therefore agree after scaling by `c`, and `c` pulls out of the supremum
in `[0, ∞]`. -/
theorem Submission.rsd_cmr_massOn_eq_ofReal_mul : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n) (T₀ : GeometricCurrentOn V n) (c : ℝ), 0 ≤ c → (∀ ω : TestFormOn V n, T (testFormOnInclusion hVU n ω) = c * T₀ ω) → ∀ W : Set (Euclid P), W ⊆ V → T.massOn W = ENNReal.ofReal c * T₀.massOn W := by
  intro P n U V hVU T T₀ c hc hT W hWV
  -- the values `ofReal (T ω)` over admissible `ω ∈ 𝒟ⁿ(U)` are the scaled values of `T₀`
  have hvalues : (fun ω ↦ ENNReal.ofReal (T ω)) '' massAdmissibleOn U n W =
      (fun ω' ↦ ENNReal.ofReal c * ENNReal.ofReal (T₀ ω')) '' massAdmissibleOn V n W := by
    ext r
    constructor
    · -- an admissible `ω ∈ 𝒟ⁿ(U)` has `spt ω ⊆ W ⊆ V`, so it is an admissible `ω' ∈ 𝒟ⁿ(V)`
      rintro ⟨ω, hω, rfl⟩
      let ω' : TestFormOn V n := ⟨ω, ω.property.1, hω.1.trans hWV⟩
      have hincl : testFormOnInclusion hVU n ω' = ω := Subtype.ext rfl
      refine ⟨ω', hω, ?_⟩
      dsimp only
      rw [← ENNReal.ofReal_mul hc, ← hT ω', hincl]
    · -- an admissible `ω' ∈ 𝒟ⁿ(V)` is admissible in `U` after inclusion
      rintro ⟨ω', hω', rfl⟩
      refine ⟨testFormOnInclusion hVU n ω', hω', ?_⟩
      dsimp only
      rw [hT ω', ENNReal.ofReal_mul hc]
  -- `ofReal c` pulls out of the supremum in `[0, ∞]`
  unfold GeometricCurrentOn.massOn
  rw [hvalues, ENNReal.mul_sSup, sSup_image, iSup_image]
/-- **Simon 6.2.11** (`spt T`, chapter-06.txt lines 296–302) under `T = c T₀` in `V`: the support
step of the reduction to multiplicity one behind 7.4.2 (chapter-07.txt lines 608–610), as in the
proof of Ch. 5, 7.3 (chapter-05.txt lines 1388–1395).  If `V ⊆ U` is open, `c ≠ 0` and
`T(ι ω) = c T₀(ω)` for every `ω ∈ 𝒟ⁿ(V)`, then `spt T₀ = spt T ∩ V`: a zero set of `T₀` is a zero
set of `T`, because a form in `U` supported in it is `ι` of a form in `V`; and a zero set `W ∋ y`
of `T` with `y ∈ V` shrinks to `W ∩ B_{s/2}(y)`, `B_s(y) ⊆ V`, a zero set of `T₀` as `c ≠ 0`. -/
theorem Submission.rsd_cmr_support_eq_inter : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n) (T₀ : GeometricCurrentOn V n) (c : ℝ), IsOpen V → c ≠ 0 → (∀ ω : TestFormOn V n, T (testFormOnInclusion hVU n ω) = c * T₀ ω) → T₀.support = T.support ∩ V := by
  intro P n U V hVU T T₀ c hV hc hT
  -- Step 2: `Z(T₀) ⊆ Z(T)`; a form in `U` supported in `W ⊆ closure W ⊆ V` is `ι` of a form in `V`.
  have hZ₀ : T₀.zeroRegion ⊆ T.zeroRegion := by
    rintro y ⟨W, ⟨hWo, hWc, hWV, hW⟩, hyW⟩
    refine ⟨W, ⟨hWo, hWc, hWV.trans hVU, fun ω hω => ?_⟩, hyW⟩
    have hωV : (ω : DifferentialForm (Euclid P) n) ∈ testFormOnSubmodule V n :=
      ⟨ω.property.1, hω.trans (subset_closure.trans hWV)⟩
    calc T ω = T (testFormOnInclusion hVU n ⟨ω, hωV⟩) := rfl
      _ = c * T₀ ⟨ω, hωV⟩ := hT _
      _ = 0 := by rw [hW ⟨ω, hωV⟩ hω, mul_zero]
  -- Step 3: `Z(T) ∩ V ⊆ Z(T₀)`; shrink `W ∋ y` to `W ∩ B_{s/2}(y)`, `B_s(y) ⊆ V`, and cancel `c`.
  have hZ : T.zeroRegion ∩ V ⊆ T₀.zeroRegion := by
    rintro y ⟨⟨W, ⟨hWo, hWc, -, hW⟩, hyW⟩, hyV⟩
    obtain ⟨s, hs, hsV⟩ := Metric.isOpen_iff.1 hV y hyV
    refine ⟨W ∩ ball y (s / 2), ⟨hWo.inter isOpen_ball,
      hWc.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left),
      (closure_mono inter_subset_right).trans (closure_ball_subset_closedBall.trans
        ((closedBall_subset_ball (half_lt_self hs)).trans hsV)), fun ω hω => ?_⟩,
      hyW, mem_ball_self (half_pos hs)⟩
    have h0 : c * T₀ ω = 0 := (hT ω).symm.trans (hW _ (hω.trans inter_subset_left))
    exact (mul_eq_zero.1 h0).resolve_left hc
  -- Steps 1 and 4: `spt T₀ = V \ Z(T₀) = V \ Z(T) = (U \ Z(T)) ∩ V`.
  ext y
  constructor
  · rintro ⟨hyV, hy⟩
    exact ⟨⟨hVU hyV, fun h => hy (hZ ⟨h, hyV⟩)⟩, hyV⟩
  · rintro ⟨⟨-, hy⟩, hyV⟩
    exact ⟨hyV, fun h => hy (hZ₀ h)⟩
/-- **`Hⁿ` under the blow-up map `η_{x,r}(y) = r⁻¹(y − x)`, `r > 0`**: `Hⁿ(η_{x,r}(S)) = r⁻ⁿ Hⁿ(S)`
for every `S ⊆ ℝᴾ`, the scaling used in the proof of Simon Ch. 3, Theorem 1.6 "⇒".  `η_{x,r}` is
the translation `y ↦ y + (−x)`, an isometry, followed by the dilation `z ↦ r⁻¹z`, and
`Hⁿ(cT) = |c|ⁿ Hⁿ(T)` for `c ≠ 0`. -/
theorem Submission.rsd_cmr_ir_blowUp_image_measure : ∀ (P n : ℕ) (x : Euclid P) (r : ℝ) (S : Set (Euclid P)), 0 < r → μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' S) = ENNReal.ofReal (r⁻¹ ^ n) * μHE[n] S := by
  intro P n x r S hr
  -- `η_{x,r}(S) = r⁻¹ • (S + (−x))`: `η_{x,r}(y) = r⁻¹ • (y − x)` and `y − x = y + (−x)`.
  have hS : Poincare.SimonGMT.Chapter03.blowUpMap x r '' S =
      (fun z => r⁻¹ • z) '' ((fun y => y + -x) '' S) := by
    rw [Set.image_image]
    rfl
  -- `Hⁿ(r⁻¹ • T) = ‖r⁻¹‖₊ⁿ • Hⁿ(T)`, translation invariance, and `‖r⁻¹‖₊ⁿ = r⁻¹ ^ n` for `r > 0`.
  rw [hS, Set.image_smul, Measure.euclideanHausdorffMeasure_smul₀ n (inv_ne_zero hr.ne'),
    (isometry_add_right (-x)).euclideanHausdorffMeasure_image, ENNReal.smul_def, smul_eq_mul,
    ← ENNReal.ofReal_coe_nnreal]
  congr 2
  simp [abs_of_pos hr]

/-- Deleting from the Borel set `M` a set that is `Hⁿ`-null near `x` keeps the approximate
tangent space of `M` at `x` (Simon Ch. 3, 1.4): if `M' ⊆ M` and `Hⁿ((M ∖ M') ∩ B_δ(x)) = 0`, then
`TₓM = Q` gives `TₓM' = Q`.  Choose `R₀ > 0` with `spt f ⊆ B̄_{R₀}(0)`.  For
`0 < λ < δ/(R₀ + 1)`, a point `z = η_{x,λ}(y)` of `η_{x,λ}(M) ∖ η_{x,λ}(M')` with `f(z) ≠ 0` has
`y ∈ M ∖ M'` and `|y − x| = λ|z| ≤ λR₀ < δ`, so it lies in `η_{x,λ}((M ∖ M') ∩ B_δ(x))`, which is
`Hⁿ`-null by `rsd_cmr_ir_blowUp_image_measure`.  Hence `f = 0` a.e. on
`η_{x,λ}(M) ∖ η_{x,λ}(M')`, and the Borel set `η_{x,λ}(M)` and its subset `η_{x,λ}(M')` carry the
same integral of `f` for all small `λ` (as in the proof of 1.6 "⇒"). -/
theorem Submission.rsd_cmr_ir_approxTangent_of_local_null : ∀ (P n : ℕ) (M M' : Set (Euclid P)) (x : Euclid P) (δ : ℝ) (Q : Submodule ℝ (Euclid P)), MeasurableSet M → M' ⊆ M → 0 < δ → μHE[n] ((M \ M') ∩ ball x δ) = 0 → HasApproximateTangentSpaceAt n M x Q → HasApproximateTangentSpaceAt n M' x Q := by
  intro P n M M' x δ Q hM hM'M hδ hnull hT
  refine ⟨hT.1, fun f => ?_⟩
  -- `spt f ⊆ B̄_{R₀}(0)` with `R₀ > 0`
  obtain ⟨R₀, hR₀, hfR₀⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  have hR₀' : (0 : ℝ) < R₀ + 1 := by linarith
  refine (hT.2 f).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos hδ hR₀')] with r hr
  have hr0 : r ≠ 0 := hr.1.ne'
  -- `Z_λ = η_{x,λ}((M ∖ M') ∩ B_δ(x))` is `Hⁿ`-null
  have hZ : μHE[n] (Poincare.SimonGMT.Chapter03.blowUpMap x r '' ((M \ M') ∩ ball x δ)) = 0 := by
    rw [Submission.rsd_cmr_ir_blowUp_image_measure P n x r _ hr.1, hnull, mul_zero]
  -- `η_{x,λ}(y) = λ⁻¹ • (y − x)`
  have hη : Poincare.SimonGMT.Chapter03.blowUpMap x r = fun y => r⁻¹ • (y - x) := rfl
  rw [hη] at hZ ⊢
  -- `η_{x,λ}(M)` is Borel: it is the preimage of `M` under `z ↦ x + λ • z`
  have hmeas : MeasurableSet ((fun y => r⁻¹ • (y - x)) '' M) := by
    have himg : (fun y => r⁻¹ • (y - x)) '' M = (fun z => x + r • z) ⁻¹' M := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [smul_smul, mul_inv_cancel₀ hr0] using hy
      · intro hz
        exact ⟨x + r • z, hz, by simp [smul_smul, inv_mul_cancel₀ hr0]⟩
    rw [himg]
    exact hM.preimage (by fun_prop)
  -- `f` vanishes on `η_{x,λ}(M) ∖ η_{x,λ}(M')` off `Z_λ`, hence a.e. there
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hmeas.nullMeasurableSet
    (image_mono hM'M) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hZ] with z hzZ hz
  obtain ⟨⟨y, hyM, rfl⟩, hyM'⟩ := hz
  apply image_eq_zero_of_notMem_tsupport
  intro hyf
  apply hzZ
  refine ⟨y, ⟨⟨hyM, fun h => hyM' ⟨y, h, rfl⟩⟩, ?_⟩, rfl⟩
  -- `|y − x| = λ|η_{x,λ}(y)| ≤ λR₀ < λ(R₀ + 1) < δ`
  have h1 : ‖r⁻¹ • (y - x)‖ ≤ R₀ := mem_closedBall_zero_iff.mp (hfR₀ hyf)
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hr.1.le, inv_mul_le_iff₀ hr.1] at h1
  have h2 := (lt_div_iff₀ hR₀').mp hr.2
  rw [mem_ball, dist_eq_norm]
  linarith [hr.1]

/-- **Restricting an integer multiplicity triple to a locally full-measure subset.**  If
`R = (M, θ, ξ)` is an integer multiplicity triple in `U` and `A` is Borel, then `(M ∩ A, θ', ξ)` is
one in `U'` provided `M ∩ A ⊆ U'`, `θ'` is measurable, positive on `M ∩ A` and locally integrable
on `M ∩ A` in `U'`, and `Hⁿ`-a.e. `x ∈ M ∩ A` has a ball `B_δ(x)` with `Hⁿ((M \ A) ∩ B_δ(x)) = 0`.
This is used for `(M ∩ B, 1, ξ)`, `B` open, and for `(M_X ∩ K, θ_X, ξ_X)` in the constant
multiplicity reduction behind Simon 7.4.2 (via Ch. 5, Corollary 7.3).  All fields but the
orientation pass from `R` to the subset `M ∩ A ⊆ M`; at such `x`, `T_x(M ∩ A) = T_xM`
(Simon Ch. 3, Definition 1.4, chapter-03.txt lines 77–84) by
`Submission.rsd_cmr_ir_approxTangent_of_local_null`, since `M \ (M ∩ A) = M \ A`. -/
theorem Submission.rsd_cmr_imrep_restrict : ∀ (P n : ℕ) (U U' A : Set (Euclid P)) (R : IMRep U n) (θ : Euclid P → ℕ), MeasurableSet A → R.carrier ∩ A ⊆ U' → Measurable θ → (∀ x ∈ R.carrier ∩ A, 0 < θ x) → (∀ K : Set (Euclid P), IsCompact K → K ⊆ U' → ∫⁻ x in R.carrier ∩ A ∩ K, (θ x : ℝ≥0∞) ∂μHE[n] ≠ ∞) → (∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ A)), ∃ δ : ℝ, 0 < δ ∧ μHE[n] ((R.carrier \ A) ∩ ball x δ) = 0) → ∃ R' : IMRep U' n, R'.carrier = R.carrier ∩ A ∧ R'.mult = θ ∧ R'.orient = R.orient := by
  intro P n U U' A R θ hA hsub hθ hθpos hθint hlocal
  refine ⟨{ carrier := R.carrier ∩ A
            mult := θ
            orient := R.orient
            measurableSet_carrier := R.measurableSet_carrier.inter hA
            carrier_subset := hsub
            rectifiable := R.rectifiable.mono inter_subset_left
            measurable_mult := hθ
            mult_pos := hθpos
            locallyIntegrable_mult := hθint
            aestronglyMeasurable_orient :=
              R.aestronglyMeasurable_orient.mono_set inter_subset_left
            orients := ?_ }, rfl, rfl, rfl⟩
  -- `Hⁿ⌞(M ∩ A)`-a.e. `x` has `T_xM = Q` oriented by `ξ(x)` (from `Hⁿ⌞M`-a.e., `M ∩ A ⊆ M`) and
  -- a ball `B_δ(x)` on which `M \ (M ∩ A) = M \ A` is `Hⁿ`-null, so `T_x(M ∩ A) = Q`.
  filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left R.orients, hlocal]
    with x ⟨Q, hQ, hξ⟩ ⟨δ, hδ, hnull⟩
  refine ⟨Q, Submission.rsd_cmr_ir_approxTangent_of_local_null P n R.carrier (R.carrier ∩ A) x δ Q
    R.measurableSet_carrier inter_subset_left hδ ?_ hQ, hξ⟩
  rwa [Set.sdiff_self_inter]
/-- **Simon Ch. 6, 1.1 and 1.7**: a unit orientation `ξ = ±τ₁ ∧ ⋯ ∧ τₙ` of a plane (`τ`
orthonormal) is a nonzero `n`-vector of norm at most one.  `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
gives `‖ξ‖ ≤ 1`.  The covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩ = det(⟨τᵢ, wⱼ⟩)`, the
alternatization of `w ↦ ∏ᵢ ⟨τᵢ, wᵢ⟩`, has `δ(τ) = 1` by orthonormality, so `ξ(δ) = ±1 ≠ 0`. -/
theorem Submission.imsupp_unit_orientation_ne_zero_norm_le_one : ∀ (P n : ℕ) (ξ : MultiVector P n) (Q : Submodule ℝ (Euclid P)), IsUnitOrientationOf ξ Q → ξ ≠ 0 ∧ ‖ξ‖ ≤ 1 := by
  rintro P n ξ Q ⟨τ, hτ, -, hξ⟩
  -- `|ξ(α)| = |α(τ)|` for either sign
  have hnorm : ∀ α : Covector (Euclid P) n, ‖ξ α‖ = ‖α τ‖ := fun α => by
    rcases hξ with h | h
    · rw [h α]
    · rw [h α, norm_neg]
  refine ⟨fun h0 => ?_, ContinuousLinearMap.opNorm_le_bound ξ zero_le_one fun α => ?_⟩
  · -- the covector `δ(w) = Σ_σ sgn σ ∏ᵢ ⟨τᵢ, w_{σ(i)}⟩` has `δ(τ) = 1`: the term `σ = 1` is
    -- `∏ᵢ ‖τᵢ‖² = 1`, and for `σ ≠ 1` some factor `⟨τᵢ, τ_{σ(i)}⟩`, `σ(i) ≠ i`, vanishes
    obtain ⟨δ, hδ⟩ : ∃ δ : Covector (Euclid P) n, δ τ = 1 := by
      refine ⟨ContinuousMultilinearMap.alternatization
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
          fun i => innerSL ℝ (τ i)), ?_⟩
      rw [ContinuousMultilinearMap.alternatization_apply_apply,
        Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
      · rw [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, Function.comp_id,
          ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply]
        refine Finset.prod_eq_one fun i _ => ?_
        rw [innerSL_apply_apply, real_inner_self_eq_norm_sq, hτ.norm_eq_one, one_pow]
      · intro σ _ hσ
        obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
          by_contra! h
          exact hσ (Equiv.ext h)
        rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
          ContinuousMultilinearMap.mkPiAlgebra_apply,
          Finset.prod_eq_zero (Finset.mem_univ i) ?_, smul_zero]
        rw [innerSL_apply_apply, Function.comp_apply]
        exact hτ.inner_eq_zero hi.symm
      · exact fun h => absurd (Finset.mem_univ _) h
    -- `ξ = 0` would give `0 = ‖ξ(δ)‖ = ‖δ(τ)‖ = 1`
    have h := hnorm δ
    rw [h0, hδ, zero_apply, norm_zero, norm_one] at h
    exact zero_ne_one h
  · -- `|ξ(α)| = |α(τ)| ≤ ‖α‖ ∏ᵢ ‖τᵢ‖ = ‖α‖`
    rw [hnorm, one_mul]
    calc ‖α τ‖ ≤ ‖α‖ * ∏ i, ‖τ i‖ := ContinuousAlternatingMap.le_opNorm α τ
      _ = ‖α‖ := by rw [Finset.prod_eq_one fun i _ => hτ.norm_eq_one i, mul_one]

/-- **Simon Ch. 6, 3.1 (‡)**: the integrand `θ ⟨ω, ξ⟩` of `τ(M, θ, ξ)(ω)` is `Hⁿ⌞M`-integrable.
`ω` is continuous with compact support `K = spt ω ⊆ U`, so `‖ω‖ ≤ C` and `ω = 0` off `K`, and
`‖ξ‖ ≤ 1` `Hⁿ⌞M`-a.e.; hence `|θ ⟨ω, ξ⟩| ≤ C θ 1_K`, integrable as `∫_{M ∩ K} θ dHⁿ < ∞`. -/
theorem Submission.rsd_cmr_ic_action_integrable : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (ω : TestFormOn U n), Integrable (fun x => (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)) (μHE[n].restrict R.carrier) := by
  intro P n U R ω
  have hω : IsTestForm (ω : DifferentialForm (Euclid P) n) ∧
      tsupport (ω : DifferentialForm (Euclid P) n) ⊆ U := ω.2
  obtain ⟨⟨hsmooth, hcpt⟩, hsupp⟩ := hω
  have hcont : Continuous (ω : DifferentialForm (Euclid P) n) := ContDiff.continuous hsmooth
  -- `‖ω‖ ≤ C`, and `K = spt ω` is closed
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hcont
  have hKm : MeasurableSet (tsupport (ω : DifferentialForm (Euclid P) n)) :=
    (isClosed_tsupport _).measurableSet
  have hθ : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  -- `1_K θ` is `Hⁿ⌞M`-integrable: `∫_{M ∩ K} θ dHⁿ < ∞`
  have hh : Integrable ((tsupport (ω : DifferentialForm (Euclid P) n)).indicator
      fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, Measure.restrict_restrict hKm, inter_comm]
    refine ⟨hθ.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
    exact (R.locallyIntegrable_mult _ hcpt.isCompact hsupp).lt_top
  -- `θ ⟨ω, ξ⟩` is a.e. strongly measurable and dominated by `C θ 1_K`
  refine (hh.const_mul C).mono' (hθ.aestronglyMeasurable.mul
    (isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (R.aestronglyMeasurable_orient.prodMk hcont.aestronglyMeasurable))) ?_
  filter_upwards [R.orients] with x hx
  obtain ⟨Q, -, hQ⟩ := hx
  have hξ := (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  by_cases hK : x ∈ tsupport (ω : DifferentialForm (Euclid P) n)
  · rw [indicator_of_mem hK, norm_mul, Real.norm_natCast, mul_comm C]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖
        ≤ ‖R.orient x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (R.orient x).le_opNorm _
      _ ≤ 1 * C := mul_le_mul hξ (hC x) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · simp [indicator_of_notMem hK, image_eq_zero_of_notMem_tsupport hK]
/-- **Simon Ch. 6, 3.1 (‡)**: if `spt ω ⊆ K` for a compact `K ⊆ U` and `‖ω(x)‖ ≤ ε` for all `x`,
then `|τ(M, θ, ξ)(ω)| ≤ ε ∫_{M ∩ K} θ dHⁿ`.  `Hⁿ`-a.e. on `M`, `ξ(x)` is a unit orientation, so
`‖ξ(x)‖ ≤ 1` and `|θ(x) ⟨ω(x), ξ(x)⟩| ≤ ε θ(x) 1_K(x)`; the bound `θ 1_K` is `Hⁿ⌞M`-integrable
with integral `∫_{M ∩ K} θ dHⁿ < ∞`, `θ` being locally `Hⁿ`-integrable in `U`. -/
theorem Submission.rsd_cmr_ic_action_abs_le : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n) (K : Set (Euclid P)) (ω : TestFormOn U n) (ε : ℝ), IsCompact K → K ⊆ U → tsupport (ω : DifferentialForm (Euclid P) n) ⊆ K → (∀ x, ‖(ω : DifferentialForm (Euclid P) n) x‖ ≤ ε) → |R.action (ω : DifferentialForm (Euclid P) n)| ≤ ε * (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
  intro P n U R K ω ε hK hKU hsupp hbound
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hθm : Measurable fun x => (R.mult x : ℝ) := measurable_from_nat.comp R.measurable_mult
  have hθ0 : ∀ x, (0 : ℝ) ≤ R.mult x := fun x => Nat.cast_nonneg _
  -- `(Hⁿ⌞M)⌞K = Hⁿ⌞(M ∩ K)`, and `ofReal θ = θ` since `θ` is `ℕ`-valued
  have hrestr : (μHE[n].restrict R.carrier).restrict K = μHE[n].restrict (R.carrier ∩ K) := by
    rw [Measure.restrict_restrict hKm, inter_comm]
  have hlint : ∫⁻ x, ENNReal.ofReal (R.mult x : ℝ) ∂(μHE[n].restrict (R.carrier ∩ K)) =
      ∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n] := by
    simp_rw [ENNReal.ofReal_natCast]
  -- `θ 1_K` is `Hⁿ⌞M`-integrable with integral `∫_{M ∩ K} θ dHⁿ`
  have hint : Integrable (K.indicator fun x => (R.mult x : ℝ)) (μHE[n].restrict R.carrier) := by
    rw [integrable_indicator_iff hKm, IntegrableOn, hrestr]
    refine ⟨hθm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hθ0), hlint]
    exact (R.locallyIntegrable_mult K hK hKU).lt_top
  have hval : ∫ x, K.indicator (fun x => (R.mult x : ℝ)) x ∂(μHE[n].restrict R.carrier) =
      (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal := by
    rw [integral_indicator hKm, hrestr,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hθ0) hθm.aestronglyMeasurable, hlint]
  -- `‖ξ(x)‖ ≤ 1` for `Hⁿ`-a.e. `x ∈ M`, `ξ(x)` being a unit orientation there
  have hξ : ∀ᵐ x ∂(μHE[n].restrict R.carrier), ‖R.orient x‖ ≤ 1 := by
    filter_upwards [R.orients] with x hx
    obtain ⟨Q, -, hQ⟩ := hx
    exact (Submission.imsupp_unit_orientation_ne_zero_norm_le_one P n _ Q hQ).2
  -- `|θ ⟨ω, ξ⟩| ≤ θ ‖ξ‖ ‖ω‖ ≤ ε θ` on `K`, and `ω = 0` off `K ⊇ spt ω`
  have hpt : ∀ᵐ x ∂(μHE[n].restrict R.carrier),
      ‖(R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖ ≤
        ε * K.indicator (fun x => (R.mult x : ℝ)) x := by
    filter_upwards [hξ] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem hxK, norm_mul, Real.norm_of_nonneg (hθ0 x), mul_comm ε]
      refine mul_le_mul_of_nonneg_left ?_ (hθ0 x)
      calc ‖R.orient x ((ω : DifferentialForm (Euclid P) n) x)‖
          ≤ ‖R.orient x‖ * ‖(ω : DifferentialForm (Euclid P) n) x‖ := (R.orient x).le_opNorm _
        _ ≤ 1 * ε := mul_le_mul hx (hbound x) (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε
    · have hωx : (ω : DifferentialForm (Euclid P) n) x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hxK (hsupp h)
      rw [indicator_of_notMem hxK, hωx, map_zero, mul_zero, norm_zero, mul_zero]
  -- `|τ(M, θ, ξ)(ω)| ≤ ∫ ε θ 1_K d(Hⁿ⌞M) = ε ∫_{M ∩ K} θ dHⁿ`
  have h := norm_integral_le_of_norm_le (hint.const_mul ε) hpt
  rwa [integral_const_mul, hval, Real.norm_eq_abs] at h

/-- **Simon Ch. 6, 3.1 (‡)**: an integer multiplicity triple `(M, θ, ξ)` in `U` defines a current
`τ(M, θ, ξ) ∈ 𝒟ₙ(U)`, `τ(M, θ, ξ)(ω) = ∫_M ⟨ω(x), ξ(x)⟩ θ(x) dHⁿ(x)`.  The integrand is
`Hⁿ⌞M`-integrable, so `ω ↦ τ(M, θ, ξ)(ω)` is linear.  If `ωⱼ → 0` in `𝒟ⁿ(U)`, then
`spt ωⱼ ⊆ K` for one compact `K ⊆ U` and `ωⱼ → 0` uniformly on `K`; for `ε > 0` and `j` large,
`‖ωⱼ‖ ≤ δ = ε / (I + 1)`, `I = ∫_{M ∩ K} θ dHⁿ`, so `|τ(M, θ, ξ)(ωⱼ)| ≤ δ I < ε`. -/
theorem Submission.rsd_cmr_imrep_represents_exists : ∀ (P n : ℕ) (U : Set (Euclid P)) (R : IMRep U n), ∃ T : GeometricCurrentOn U n, R.Represents T := by
  intro P n U R
  refine ⟨{ toCurrent :=
              { toFun := fun ω => R.action (ω : DifferentialForm (Euclid P) n)
                map_add' := fun ω η => ?_
                map_smul' := fun c ω => ?_ }
            continuous' := fun ωs hωs => ?_ }, fun ω => rfl⟩
  · -- `θ ⟨ω + η, ξ⟩ = θ ⟨ω, ξ⟩ + θ ⟨η, ξ⟩`, both integrable
    simp only [IMRep.action, Submodule.coe_add, Pi.add_apply, map_add, mul_add]
    exact integral_add (Submission.rsd_cmr_ic_action_integrable P n U R ω)
      (Submission.rsd_cmr_ic_action_integrable P n U R η)
  · -- `θ ⟨c ω, ξ⟩ = c θ ⟨ω, ξ⟩`
    simp only [IMRep.action, Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul,
      RingHom.id_apply]
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  · -- `spt ωⱼ ⊆ K` for a compact `K ⊆ U`, and the `0`-th derivatives `ωⱼ → 0` uniformly on `K`
    obtain ⟨K, hK, hKU, hsupp, -, hconv⟩ := hωs
    change Tendsto (fun j => R.action (ωs j : DifferentialForm (Euclid P) n)) atTop (𝓝 0)
    set I := (∫⁻ x in R.carrier ∩ K, (R.mult x : ℝ≥0∞) ∂μHE[n]).toReal
    have hI : 0 ≤ I := ENNReal.toReal_nonneg
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : 0 < ε / (I + 1) := div_pos hε (by linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hconv 0) _ hδ)
    refine ⟨N, fun j hj => ?_⟩
    -- `‖ωⱼ(x)‖ ≤ δ` everywhere: on `K` by uniform convergence, off `K` since `ωⱼ = 0` there
    have hbound : ∀ x, ‖(ωs j : DifferentialForm (Euclid P) n) x‖ ≤ ε / (I + 1) := fun x => by
      by_cases hx : x ∈ K
      · have h := hN j hj x hx
        rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply,
          LinearIsometryEquiv.dist_map, Submodule.coe_zero, Pi.zero_apply, dist_zero_left] at h
        exact h.le
      · rw [image_eq_zero_of_notMem_tsupport fun h => hx (hsupp j h), norm_zero]
        exact hδ.le
    -- `|τ(M, θ, ξ)(ωⱼ)| ≤ δ I < ε`
    have h := Submission.rsd_cmr_ic_action_abs_le P n U R K (ωs j) _ hK hKU (hsupp j) hbound
    rw [Real.dist_eq, sub_zero]
    calc |R.action (ωs j : DifferentialForm (Euclid P) n)| ≤ ε / (I + 1) * I := h
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- **Constant multiplicity: the quotient current is integer multiplicity** (Simon Ch. 5, proof of
Corollary 7.3, chapter-05.txt lines 1389–1394, `Ṽ = v(M, N⁻¹θ)⌞B_ρ(ξ)`; a step of the constant
multiplicity reduction behind Simon 7.4.2).  Let `T = τ(M, θ, ξ)` in `U`, `V ⊆ U` open, `N₀ ≥ 1`
with `θ = N₀` `μ_T`-a.e. on `V`, and `T(ω) = N₀ T₀(ω)` for `ω ∈ 𝒟ⁿ(V)`.  Then `(M ∩ V, 1, ξ)`
represents `T₀`.  Since `μ_T = θHⁿ⌞M` with `θ ≥ 1` on `M`, `θ = N₀` `Hⁿ`-a.e. on `M ∩ V`.
`Submission.rsd_cmr_imrep_restrict` makes `(M ∩ V, 1, ξ)` a triple in `V` (`1 ≤ θ` gives local
integrability, and `V` is open).  As `ω = 0` off `V`,
`N₀ T₀(ω) = ∫_M θ⟨ω, ξ⟩ dHⁿ = ∫_{M ∩ V} N₀⟨ω, ξ⟩ dHⁿ`; cancel `N₀ ≠ 0`. -/
theorem Submission.rsd_cmr_isIntegerMultiplicity_of_const_mult : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n) (R : IMRep U n) (T₀ : GeometricCurrentOn V n) (N₀ : ℕ), IsOpen V → 0 < N₀ → R.Represents T → (∀ᵐ x ∂R.measure, x ∈ V → R.mult x = N₀) → (∀ ω : TestFormOn V n, T (testFormOnInclusion hVU n ω) = (N₀ : ℝ) * T₀ ω) → IsIntegerMultiplicity T₀ := by
  intro P n U V hVU T R T₀ N₀ hV hN₀ hRT hconst hT₀
  have hMV : MeasurableSet (R.carrier ∩ V) := R.measurableSet_carrier.inter hV.measurableSet
  have hθ : Measurable fun x => (R.mult x : ℝ≥0∞) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp R.measurable_mult
  -- Step 1: `θ = N₀` `Hⁿ`-a.e. on `M ∩ V`, as `μ_T = θHⁿ⌞M` and `θ ≠ 0` on `M`.
  have hae : ∀ᵐ x ∂(μHE[n].restrict (R.carrier ∩ V)), R.mult x = N₀ := by
    have h := (ae_withDensity_iff (μ := μHE[n].restrict R.carrier) hθ).1 hconst
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (inter_subset_left : R.carrier ∩ V ⊆ R.carrier) h, ae_restrict_mem hMV] with x hx hxMV
    exact hx (Nat.cast_ne_zero.2 (R.mult_pos x hxMV.1).ne') hxMV.2
  -- Step 2: `R₀ = (M ∩ V, 1, ξ)` is an integer multiplicity triple in `V`.
  obtain ⟨R₀, hcar, hmult, horient⟩ := Submission.rsd_cmr_imrep_restrict P n U V V R (fun _ => 1)
    hV.measurableSet inter_subset_right measurable_const (fun _ _ => Nat.one_pos)
    -- `∫_{M ∩ V ∩ K} 1 dHⁿ ≤ ∫_{M ∩ K} θ dHⁿ < ∞`, as `1 ≤ θ` on `M`.
    (fun K hK hKV => ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK (hKV.trans hVU))
      (le_trans (setLIntegral_mono hθ fun x hx => Nat.cast_le.2 (R.mult_pos x hx.1.1))
        (lintegral_mono_set (inter_subset_inter_left K inter_subset_left))))
    (by
      -- A ball `B_δ(x) ⊆ V` about `x ∈ M ∩ V` misses `M \ V`.
      filter_upwards [ae_restrict_mem hMV] with x hx
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV x hx.2
      exact ⟨δ, hδ, measure_mono_null (fun y hy => absurd (hball hy.2) hy.1.2) measure_empty⟩)
  -- Step 3: `N₀ T₀(ω) = N₀ R₀(ω)`, and `N₀ ≠ 0`.
  refine ⟨R₀, fun ω => mul_left_cancel₀ (Nat.cast_ne_zero.2 hN₀.ne' : (N₀ : ℝ) ≠ 0) ?_⟩
  -- `ω = 0` on `M \ V`, as `spt ω ⊆ V`.
  have hω : ∀ x ∈ R.carrier \ (R.carrier ∩ V), (ω : DifferentialForm (Euclid P) n) x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx.2 ⟨hx.1, ω.2.2 h⟩
  calc (N₀ : ℝ) * T₀ ω = T (testFormOnInclusion hVU n ω) := (hT₀ ω).symm
    _ = ∫ x in R.carrier, (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x)
          ∂μHE[n] := hRT _
    _ = ∫ x in R.carrier ∩ V,
          (R.mult x : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] :=
        setIntegral_eq_of_subset_of_forall_sdiff_eq_zero R.measurableSet_carrier
          inter_subset_left fun x hx => by simp only [hω x hx, map_zero, mul_zero]
    _ = ∫ x in R.carrier ∩ V,
          (N₀ : ℝ) * R.orient x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] :=
        integral_congr_ae (hae.mono fun x hx => by simp only [hx])
    _ = (N₀ : ℝ) * R₀.action ω := by
        rw [integral_const_mul]
        simp only [IMRep.action, hcar, hmult, horient, Nat.cast_one, one_mul]
/-- **Extension by zero** (Simon 6.2.16, 6.3.1; step 6(b)–(c) of the proof of 7.4.2).  Let
`B ⊆ U` with `B` open, `K ⊆ B` compact, and `X = τ(M, θ, ξ) ∈ 𝒟ₙ(B)` with `μ_X = θ Hⁿ⌞M`
vanishing near each point of `B \ K`.  By second countability `μ_X(B \ K) = 0`, so
`Hⁿ(M \ K) = 0` as `θ ≥ 1` on `M ⊆ B`.  Then `E = τ(M ∩ K, θ, ξ) ∈ 𝒟ₙ(U)` is integer
multiplicity, extends `X` (`M ∩ K = M` up to the `Hⁿ`-null set `M \ K`) and vanishes on forms
whose support misses `K`. -/
theorem Submission.rsd_cmr_zero_extension : ∀ (P n : ℕ) (U B K : Set (Euclid P)) (hBU : B ⊆ U) (X : GeometricCurrentOn B n) (R : IMRep B n), IsOpen B → IsCompact K → K ⊆ B → R.Represents X → (∀ y ∈ B, y ∉ K → ∃ ρ : ℝ, 0 < ρ ∧ R.measure (ball y ρ) = 0) → ∃ E : GeometricCurrentOn U n, IsIntegerMultiplicity E ∧ (∀ ω : TestFormOn B n, E (testFormOnInclusion hBU n ω) = X ω) ∧ ∀ ω : TestFormOn U n, Disjoint (tsupport (ω : DifferentialForm (Euclid P) n)) K → E ω = 0 := by
  intro P n U B K hBU X R hB hK hKB hX hloc
  -- `μ_X(B \ K) = 0`: each point of `B \ K` has a `μ_X`-null ball, and `ℝᴾ` is second countable.
  have hnull : R.measure (B \ K) = 0 :=
    measure_null_of_locally_null _ fun y hy => by
      obtain ⟨ρ, hρ, hball⟩ := hloc y hy.1 hy.2
      exact ⟨ball y ρ, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds y hρ), hball⟩
  -- `Hⁿ(M \ K) ≤ ∫_{M ∩ (B \ K)} θ dHⁿ = μ_X(B \ K) = 0`, since `θ ≥ 1` on `M ⊆ B`.
  have hBK : MeasurableSet (B \ K) := hB.measurableSet.diff hK.measurableSet
  have hMK : μHE[n] (R.carrier \ K) = 0 := by
    refine nonpos_iff_eq_zero.1 (le_of_le_of_eq ?_ hnull)
    calc μHE[n] (R.carrier \ K) ≤ μHE[n] ((B \ K) ∩ R.carrier) :=
          measure_mono fun x hx => ⟨⟨R.carrier_subset hx.1, hx.2⟩, hx.1⟩
      _ = ∫⁻ _ in (B \ K) ∩ R.carrier, 1 ∂μHE[n] := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in (B \ K) ∩ R.carrier, (R.mult x : ℝ≥0∞) ∂μHE[n] :=
          setLIntegral_mono' (hBK.inter R.measurableSet_carrier) fun x hx =>
            Nat.one_le_cast.2 (R.mult_pos x hx.2)
      _ = R.measure (B \ K) := by
          rw [IMRep.measure, withDensity_apply _ hBK, Measure.restrict_restrict hBK]
  -- `(M ∩ K, θ, ξ)` is a triple in `U`: `θ` is integrable on the compact `K ⊆ B`, and the
  -- discarded part `M \ K` is `Hⁿ`-null.
  obtain ⟨R', hR'c, hR'm, hR'o⟩ := Submission.rsd_cmr_imrep_restrict P n B U K R R.mult
    hK.measurableSet (fun x hx => hBU (hKB hx.2)) R.measurable_mult
    (fun x hx => R.mult_pos x hx.1)
    (fun _ _ _ => ne_top_of_le_ne_top (R.locallyIntegrable_mult K hK hKB)
      (lintegral_mono_set inter_subset_left))
    (Eventually.of_forall fun _ => ⟨1, one_pos, measure_mono_null inter_subset_left hMK⟩)
  -- `E = τ(M ∩ K, θ, ξ) ∈ 𝒟ₙ(U)`.
  obtain ⟨E, hE⟩ := Submission.rsd_cmr_imrep_represents_exists P n U R'
  refine ⟨E, ⟨R', hE⟩, fun ω => ?_, fun ω hω => ?_⟩
  · -- `E` extends `X`: `M ∩ K` and `M` differ by the `Hⁿ`-null set `M \ K`.
    rw [hE (testFormOnInclusion hBU n ω), hX ω]
    simp only [IMRep.action, testFormOnInclusion_coe]
    rw [hR'c, hR'm, hR'o]
    refine setIntegral_congr_set (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [Set.sdiff_eq_empty.2 inter_subset_left, measure_empty]
    · rwa [Set.sdiff_self_inter]
  · -- `E(ω) = 0` when `spt ω ∩ K = ∅`: `ω` vanishes on `M ∩ K ⊆ K`.
    rw [hE ω]
    simp only [IMRep.action]
    rw [hR'c]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
    rw [image_eq_zero_of_notMem_tsupport (Set.disjoint_right.1 hω hx.2), map_zero, mul_zero]
/-- Cut-off step of the reduction to multiplicity one behind **Simon 7.4.2** (chapter-07.txt
lines 608–610), as in the proof of Ch. 5, 7.3 (chapter-05.txt lines 1388–1395), where it gives
`∂S = ∂T` for the competitor `S = T + N₀E`.  If `B ⊆ U` is open, `K ⊆ B` is compact, and
`F ∈ 𝒟ₘ(U)` vanishes on every form whose support misses `K` and on `ι(𝒟ᵐ(B))`, then `F = 0`:
take a smooth `φ` with `tsupport φ ⊆ B` compact and `φ = 1` on an open `V ⊇ K`; then
`ω = ι(φω) + (1 − φ)ω`, and `(1 − φ)ω` vanishes on `V`, so its support misses `K`. -/
theorem Submission.rsd_cmr_eq_zero_of_vanish_off_compact : ∀ (P m : ℕ) (U B K : Set (Euclid P)) (hBU : B ⊆ U) (F : GeometricCurrentOn U m), IsOpen B → IsCompact K → K ⊆ B → (∀ ω : TestFormOn U m, Disjoint (tsupport (ω : DifferentialForm (Euclid P) m)) K → F ω = 0) → (∀ ψ : TestFormOn B m, F (testFormOnInclusion hBU m ψ) = 0) → ∀ ω : TestFormOn U m, F ω = 0 := by
  intro P m U B K hBU F hB hK hKB hoff hin ω
  -- Step 1: a smooth cutoff `φ`, `= 1` on `thickening (δ/2) K ⊇ K`, `tsupport φ ⊆ cthickening δ K ⊆ B`.
  obtain ⟨δ, hδ, hδB⟩ := hK.exists_cthickening_subset_open hB hKB
  obtain ⟨φ, hφ, -, hφs, hφt⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤)
    (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2) (E := K))
    (cthickening_subset_thickening' hδ (half_lt_self hδ) K)
  have htφ : tsupport φ ⊆ cthickening δ K := by
    rw [tsupport, hφs]
    exact closure_thickening_subset_cthickening δ K
  have hφ1 : ∀ x ∈ thickening (δ / 2) K, φ x = 1 :=
    fun x hx => (hφt x).1 (thickening_subset_cthickening _ _ hx)
  -- Step 2: `ψ = φ ω ∈ 𝒟ᵐ(B)`, so `F (ι ψ) = 0`.
  have hωs : ContDiff ℝ (⊤ : ℕ∞) (ω : DifferentialForm (Euclid P) m) := ω.property.1.1
  have hψt : tsupport (fun x => φ x • (ω : DifferentialForm (Euclid P) m) x) ⊆ tsupport φ :=
    tsupport_smul_subset_left _ _
  have hcφ : IsCompact (tsupport φ) :=
    hK.cthickening.of_isClosed_subset (isClosed_tsupport φ) htφ
  let ψ : TestFormOn B m := ⟨fun x => φ x • (ω : DifferentialForm (Euclid P) m) x,
    ⟨hφ.fun_smul hωs, hcφ.of_isClosed_subset (isClosed_tsupport _) hψt⟩, hψt.trans (htφ.trans hδB)⟩
  -- Step 3: `ω - ι ψ = (1 - φ) ω` vanishes on the open `thickening (δ/2) K ⊇ K`.
  have hdisj : Disjoint (tsupport ((ω - testFormOnInclusion hBU m ψ : TestFormOn U m) :
      DifferentialForm (Euclid P) m)) K := by
    refine Set.disjoint_right.2 fun x hx => notMem_tsupport_iff_eventuallyEq.2 ?_
    filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening (half_pos hδ) K hx)]
      with y hy
    simp [ψ, hφ1 y hy]
  -- Step 4: linearity, `F ω = F (ι ψ) + F (ω - ι ψ) = 0`.
  have h := hoff _ hdisj
  rw [map_sub F.toCurrent ω (testFormOnInclusion hBU m ψ), hin ψ, sub_zero] at h
  exact h
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
/-- **Simon 7.4.1** (`reg T`, chapter-07.txt lines 590–594) under `T = c T₀` in `V`: the
regularity transfer of the reduction to multiplicity one behind 7.4.2 (lines 605–610), as in the
proof of Ch. 5, 7.3 (chapter-05.txt lines 1388–1395).  If `V ⊆ U`, `c ∈ ℤ \ {0}`,
`T(ι ω) = c T₀(ω)` for every `ω ∈ 𝒟ⁿ(V)`, `y ∈ spt T` and `y ∈ reg T₀`, then `y ∈ reg T`: the
`ρ`, `M` and `ξ` with `T₀ = m[[M]]` in `B_ρ(y) ⊆ V` give `T = (c m)[[M]]` in `B_ρ(y)`, because a
form in `U` supported in `B_ρ(y)` is `ι` of a form in `V`. -/
theorem Submission.rsd_cmr_regularSet_transfer : ∀ (P n : ℕ) (U V : Set (Euclid P)) (hVU : V ⊆ U) (T : GeometricCurrentOn U n) (T₀ : GeometricCurrentOn V n) (c : ℤ) (y : Euclid P), c ≠ 0 → (∀ ω : TestFormOn V n, T (testFormOnInclusion hVU n ω) = (c : ℝ) * T₀ ω) → y ∈ T.support → y ∈ regularSet T₀ → y ∈ regularSet T := by
  intro P n U V hVU T T₀ c y hc hT hyT hy
  -- Step 1: `ρ, m, M, ξ` with `T₀ = m[[M]]` in `B_ρ(y) ⊆ V` (the clause `y ∈ spt T₀` is unused).
  obtain ⟨-, ρ, hρ, hball, m, M, ξ, hm, hyM, hM, hξ, hfin, hrep⟩ := hy
  -- Steps 2 and 4: the same `ρ, M, ξ`, multiplicity `c m ≠ 0`, and `B_ρ(y) ⊆ V ⊆ U`.
  refine ⟨hyT, ρ, hρ, hball.trans hVU, c * m, M, ξ, mul_ne_zero hc hm, hyM, hM, hξ, hfin, ?_⟩
  -- Step 3: `ω ∈ 𝒟ⁿ(U)` with `spt ω ⊆ B_ρ(y) ⊆ V` is `ι ω'` for `ω' ∈ 𝒟ⁿ(V)`, the same form.
  intro ω hω
  have hωV : (ω : DifferentialForm (Euclid P) n) ∈ testFormOnSubmodule V n :=
    ⟨ω.property.1, hω.trans hball⟩
  calc T ω = T (testFormOnInclusion hVU n ⟨ω, hωV⟩) := rfl
    _ = (c : ℝ) * T₀ ⟨ω, hωV⟩ := hT _
    _ = (c : ℝ) * (m * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n]) := by
      rw [hrep ⟨ω, hωV⟩ hω]
    _ = ((c * m : ℤ) : ℝ) * ∫ x in M, ξ x ((ω : DifferentialForm (Euclid P) n) x) ∂μHE[n] := by
      push_cast
      ring
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

/-- Chapter 7 of Simon's *Introduction to GMT*: the headline results above. -/
theorem main_theorem : MinimizingImpliesStationary ∧ ExistenceOfMinimizingFilling ∧ CompactnessOfMinimizingCurrents ∧ DensityAndTangentCones ∧ IntegerDensityAndTangentPlanes ∧ RegularSetDense ∧ DensityOneImpliesRegular ∧ SingularSetSmallWhereDensityBelowTwo ∧ HalfSpaceConeLiesInBoundary ∧ CodimensionOneRegularity ∧ RegularComponentsAreMinimizing := by sorry

end GMT.Ch07
